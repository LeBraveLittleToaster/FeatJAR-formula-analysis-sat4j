/*
 * Copyright (C) 2022 Sebastian Krieter
 *
 * This file is part of formula-analysis-sat4j.
 *
 * formula-analysis-sat4j is free software: you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3.0 of the License,
 * or (at your option) any later version.
 *
 * formula-analysis-sat4j is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with formula-analysis-sat4j. If not, see <https://www.gnu.org/licenses/>.
 *
 * See <https://github.com/FeatureIDE/FeatJAR-formula-analysis-sat4j> for further information.
 */
package de.featjar.transform;

import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.analysis.solver.RuntimeContradictionException;
import de.featjar.analysis.solver.SatSolver;
import de.featjar.clauses.CNF;
import de.featjar.clauses.ClauseLengthComparatorDsc;
import de.featjar.clauses.LiteralList;
import de.featjar.formula.structure.atomic.literal.VariableMap;
import de.featjar.util.job.InternalMonitor;
import de.featjar.util.job.MonitorableFunction;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import org.sat4j.specs.TimeoutException;

/**
 * Removes features from a model while retaining dependencies of all other
 * feature.
 *
 * @author Sebastian Krieter
 */
public class CNFSlicer implements MonitorableFunction<CNF, CNF> {

    protected static final Comparator<LiteralList> lengthComparator = new ClauseLengthComparatorDsc();

    protected CNF orgCNF;
    protected CNF cnfCopy;

    protected final List<DirtyClause> newDirtyClauseList = new ArrayList<>();
    protected final List<DirtyClause> newCleanClauseList = new ArrayList<>();
    protected final List<DirtyClause> dirtyClauseList = new ArrayList<>();
    protected final ArrayList<LiteralList> cleanClauseList = new ArrayList<>();
    protected final Set<DirtyClause> dirtyClauseSet = new HashSet<>();
    protected final Set<DirtyClause> cleanClauseSet = new HashSet<>();

    protected final LiteralList dirtyVariables;
    private int numberOfDirtyFeatures = 0;

    protected int[] helper;
    protected DirtyFeature[] map;
    protected MinimumClauseHeuristic heuristic;
    private Sat4JSolver newSolver;

    private boolean first = false;

    protected int globalMixedClauseCount = 0;

    protected int dirtyListPosIndex = 0;
    protected int dirtyListNegIndex = 0;
    protected int newDirtyListDelIndex = 0;

    public CNFSlicer(LiteralList dirtyVariables) {
        this.dirtyVariables = dirtyVariables;
    }

    public CNFSlicer(Collection<String> dirtyVariableNames, VariableMap variableMap) {
        dirtyVariables = LiteralList.getVariables(variableMap, dirtyVariableNames);
    }

    int cr = 0, cnr = 0, dr = 0, dnr = 0;

    @Override
    public CNF execute(CNF orgCNF, InternalMonitor monitor) throws TimeoutException {
        this.orgCNF = orgCNF;
        cnfCopy = new CNF(orgCNF.getVariableMap());

        map = new DirtyFeature[orgCNF.getVariableMap().getVariableCount() + 1];
        numberOfDirtyFeatures = 0;
        for (final int curFeature : dirtyVariables.getLiterals()) {
            map[curFeature] = new DirtyFeature(curFeature);
            numberOfDirtyFeatures++;
        }
        helper = new int[map.length];

        // Initialize lists and sets
        createClauseLists();

        if (!prepareHeuristics()) {
            return new CNF(orgCNF.getVariableMap(), orgCNF.getClauses());
        }

        monitor.setTotalWork(heuristic.size());
        monitor.checkCancel();

        while (heuristic.hasNext()) {
            final DirtyFeature nextFeature = heuristic.next();
            if (nextFeature == null) {
                break;
            }

            // Remove redundant dirty clauses
            firstRedundancyCheck(nextFeature);

            // Partition dirty list into clauses that contain the current variable and
            // clauses that don't
            partitionDirtyList(nextFeature);

            // Remove variable & create transitive clauses
            resolution(nextFeature);

            // Remove redundant clauses
            detectRedundancy(nextFeature);

            // Merge new dirty list into the old list
            updateLists();

            monitor.step();

            // If ALL dirty clauses exclusively consists of dirty features, they can just be
            // removed without applying resolution
            if (globalMixedClauseCount == 0) {
                break;
            }
        }

        addCleanClauses();

        release();
        final HashSet<String> names = new HashSet<>(orgCNF.getVariableMap().getVariableNames());
        for (final int literal : dirtyVariables.getLiterals()) {
            names.remove(
                    orgCNF.getVariableMap().getVariableName(Math.abs(literal)).get());
        }
        final VariableMap slicedVariableMap = new VariableMap(names);
        final List<LiteralList> slicedClauseList = cleanClauseList.stream()
                .map(clause ->
                        clause.adapt(orgCNF.getVariableMap(), slicedVariableMap).get())
                .collect(Collectors.toList());

        return new CNF(slicedVariableMap, slicedClauseList);
    }

    private void addNewClause(final DirtyClause curClause) {
        if (curClause != null) {
            if (curClause.computeRelevance(map)) {
                globalMixedClauseCount++;
            }
            if (curClause.getRelevance() == 0) {
                if (cleanClauseSet.add(curClause)) {
                    newCleanClauseList.add(curClause);
                } else {
                    deleteClause(curClause);
                }
            } else {
                if (dirtyClauseSet.add(curClause)) {
                    newDirtyClauseList.add(curClause);
                } else {
                    deleteClause(curClause);
                }
            }
        }
    }

    private void createClauseLists() {
        for (final LiteralList clause : orgCNF.getClauses()) {
            addNewClause(new DirtyClause(clause.getLiterals()));
        }

        cleanClauseList.ensureCapacity(cleanClauseList.size() + newCleanClauseList.size());
        for (final DirtyClause dirtyClause : newCleanClauseList) {
            cleanClauseList.add(new LiteralList(dirtyClause));
        }
        dirtyClauseList.addAll(newDirtyClauseList);
        newDirtyClauseList.clear();
        newCleanClauseList.clear();

        dirtyListPosIndex = dirtyClauseList.size();
        dirtyListNegIndex = dirtyClauseList.size();
    }

    protected final void deleteClause(final DirtyClause curClause) {
        if (curClause.delete(map)) {
            globalMixedClauseCount--;
        }
    }

    protected final void deleteOldDirtyClauses() {
        if (dirtyListPosIndex < dirtyClauseList.size()) {
            final List<DirtyClause> subList = dirtyClauseList.subList(dirtyListPosIndex, dirtyClauseList.size());
            dirtyClauseSet.removeAll(subList);
            for (final DirtyClause dirtyClause : subList) {
                deleteClause(dirtyClause);
            }
            subList.clear();
        }
    }

    protected final void deleteNewDirtyClauses() {
        if (newDirtyListDelIndex < newDirtyClauseList.size()) {
            final List<DirtyClause> subList =
                    newDirtyClauseList.subList(newDirtyListDelIndex, newDirtyClauseList.size());
            dirtyClauseSet.removeAll(subList);
            for (final DirtyClause dirtyClause : subList) {
                deleteClause(dirtyClause);
            }
        }
    }

    private void resolution(DirtyFeature nextFeature) {
        final int curFeatureID = nextFeature.getId();
        for (int i = dirtyListPosIndex; i < dirtyListNegIndex; i++) {
            final int[] posOrChildren = dirtyClauseList.get(i).getLiterals();
            for (int j = dirtyListNegIndex; j < dirtyClauseList.size(); j++) {
                final int[] negOrChildren = dirtyClauseList.get(j).getLiterals();
                final int[] newChildren = new int[posOrChildren.length + negOrChildren.length];

                System.arraycopy(posOrChildren, 0, newChildren, 0, posOrChildren.length);
                System.arraycopy(negOrChildren, 0, newChildren, posOrChildren.length, negOrChildren.length);

                addNewClause(DirtyClause.createClause(newChildren, curFeatureID, helper));
            }
        }
        newDirtyListDelIndex = newDirtyClauseList.size();
    }

    private void partitionDirtyList(DirtyFeature nextFeature) {
        final int curFeatureID = nextFeature.getId();
        for (int i = 0; i < dirtyListNegIndex; i++) {
            final LiteralList clause = dirtyClauseList.get(i);
            for (final int literal : clause.getLiterals()) {
                if (literal == -curFeatureID) {
                    Collections.swap(dirtyClauseList, i--, --dirtyListNegIndex);
                    break;
                }
            }
        }
        dirtyListPosIndex = dirtyListNegIndex;
        for (int i = 0; i < dirtyListPosIndex; i++) {
            final LiteralList clause = dirtyClauseList.get(i);
            for (final int literal : clause.getLiterals()) {
                if (literal == curFeatureID) {
                    Collections.swap(dirtyClauseList, i--, --dirtyListPosIndex);
                    break;
                }
            }
        }
    }

    private void updateLists() {
        // delete old & redundant dirty clauses
        deleteOldDirtyClauses();

        // delete new & redundant dirty clauses
        deleteNewDirtyClauses();

        dirtyClauseList.addAll(newDirtyClauseList.subList(0, newDirtyListDelIndex));
        newDirtyClauseList.clear();

        dirtyListPosIndex = dirtyClauseList.size();
        dirtyListNegIndex = dirtyClauseList.size();
        newDirtyListDelIndex = 0;
    }

    protected final boolean isRedundant(Sat4JSolver solver, LiteralList curClause) {
        switch (solver.hasSolution(curClause.negate())) {
            case FALSE:
                return true;
            case TIMEOUT:
            case TRUE:
                return false;
            default:
                assert false;
                return false;
        }
    }

    protected void detectRedundancy(DirtyFeature nextFeature) {
        if (nextFeature.getClauseCount() > 0) {
            addCleanClauses();

            final Sat4JSolver solver = new Sat4JSolver(cnfCopy);
            solver.getFormula().push(cleanClauseList);
            solver.getFormula().push(dirtyClauseList.subList(0, dirtyListPosIndex));

            Collections.sort(newDirtyClauseList.subList(0, newDirtyListDelIndex), lengthComparator);
            for (int i = newDirtyListDelIndex - 1; i >= 0; --i) {
                final DirtyClause curClause = newDirtyClauseList.get(i);
                if (isRedundant(solver, curClause)) {
                    dr++;
                    Collections.swap(newDirtyClauseList, i, --newDirtyListDelIndex);
                } else {
                    dnr++;
                    solver.getFormula().push(curClause);
                }
            }
        }
    }

    protected void addCleanClauses() {
        Collections.sort(newCleanClauseList, lengthComparator);

        for (int i = newCleanClauseList.size() - 1; i >= 0; --i) {
            final DirtyClause clause = newCleanClauseList.get(i);

            if (isRedundant(newSolver, clause)) {
                cr++;
                deleteClause(clause);
            } else {
                cnr++;
                newSolver.getFormula().push(clause);
                cleanClauseList.add(new LiteralList(clause));
            }
        }
        newCleanClauseList.clear();
    }

    protected void firstRedundancyCheck(DirtyFeature nextFeature) {
        if (first && (nextFeature.getClauseCount() > 0)) {
            first = false;
            Collections.sort(dirtyClauseList.subList(0, dirtyListPosIndex), lengthComparator);

            addCleanClauses();

            final Sat4JSolver solver = new Sat4JSolver(cnfCopy);
            solver.getFormula().push(cleanClauseList);

            // SAT Relevant
            for (int i = dirtyListPosIndex - 1; i >= 0; --i) {
                final DirtyClause mainClause = dirtyClauseList.get(i);
                if (isRedundant(solver, mainClause)) {
                    dr++;
                    Collections.swap(dirtyClauseList, i, --dirtyListPosIndex);
                } else {
                    dnr++;
                    solver.getFormula().push(mainClause);
                }
            }
            deleteOldDirtyClauses();

            dirtyListPosIndex = dirtyClauseList.size();
            dirtyListNegIndex = dirtyClauseList.size();
            cr = 0;
            cnr = 0;
            dr = 0;
            dnr = 0;
        }
    }

    protected boolean prepareHeuristics() {
        heuristic = new MinimumClauseHeuristic(map, numberOfDirtyFeatures);
        first = true;
        try {
            newSolver = new Sat4JSolver(cnfCopy);
            // newSolver.addClauses(cleanClauseList);
        } catch (final RuntimeContradictionException e) {
            return false;
        }
        return newSolver.hasSolution() == SatSolver.SatResult.TRUE;
    }

    protected void release() {
        newDirtyClauseList.clear();
        newCleanClauseList.clear();
        dirtyClauseSet.clear();
        cleanClauseSet.clear();
        dirtyClauseList.clear();

        if (newSolver != null) {
            newSolver.reset();
        }
    }
}
