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
package de.featjar.analysis.mig.solver;

import de.featjar.analysis.mig.solver.MIG.BuildStatus;
import de.featjar.analysis.mig.solver.Vertex.Status;
import de.featjar.analysis.sat4j.solver.SStrategy;
import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.analysis.solver.RuntimeContradictionException;
import de.featjar.clauses.CNF;
import de.featjar.clauses.Clauses;
import de.featjar.clauses.LiteralList;
import de.featjar.formula.structure.atomic.literal.VariableMap;
import de.featjar.util.job.InternalMonitor;
import java.util.Collection;
import java.util.HashSet;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

public class IncrementalMIGBuilder extends MIGBuilder {

    private enum Changes {
        UNCHANGED,
        ADDED,
        REMOVED,
        REPLACED
    }

    private final MIG oldMig;

    private boolean add = false;

    private Changes changes;
    private HashSet<LiteralList> addedClauses;
    private VariableMap variables;

    public IncrementalMIGBuilder(MIG oldMig) {
        this.oldMig = oldMig;
    }

    @Override
    public MIG execute(CNF cnf, InternalMonitor monitor) throws Exception {
        Objects.requireNonNull(cnf);
        Objects.requireNonNull(oldMig);

        collect(cnf);
        monitor.step();

        if (!satCheck(cnf)) {
            throw new RuntimeContradictionException("CNF is not satisfiable!");
        }
        monitor.step();
        core(cnf, monitor);
        monitor.step();

        cleanClauses();
        monitor.step();

        if (detectStrong) {
            checkOldStrong();

            if (add) {
                addClauses(cnf, false, monitor.subTask(10));

                bfsStrong(monitor.subTask(10));

                final LiteralList affectedVariables = new LiteralList(
                        addedClauses.stream() //
                                .map(c ->
                                        c.adapt(variables, cnf.getVariableMap()).get()) //
                                .flatMapToInt(c -> IntStream.of(c.getLiterals())) //
                                .map(Math::abs) //
                                .distinct() //
                                .toArray(), //
                        LiteralList.Order.NATURAL);
                bfsWeak(affectedVariables, monitor.subTask(1000));
            }
            mig.setStrongStatus(BuildStatus.Incremental);
        } else {
            mig.setStrongStatus(BuildStatus.None);
        }

        add(cnf, checkRedundancy, addedClauses);

        bfsStrong(monitor);
        monitor.step();

        finish();
        monitor.step();
        return mig;
    }

    public static double getChangeRatio(CNF cnf1, CNF cnf2) {
        final Set<String> allVariables = new HashSet<>(cnf2.getVariableMap().getVariableNames());
        allVariables.addAll(cnf1.getVariableMap().getVariableNames());
        final VariableMap variables = new VariableMap(allVariables);

        final HashSet<LiteralList> adaptedNewClauses = cnf1.getClauses().stream()
                .map(c -> c.adapt(cnf1.getVariableMap(), variables).get()) //
                .peek(c -> c.setOrder(LiteralList.Order.NATURAL))
                .collect(Collectors.toCollection(HashSet::new));

        final HashSet<LiteralList> adaptedOldClauses = cnf2.getClauses().stream() //
                .map(c -> c.adapt(cnf2.getVariableMap(), variables).get()) //
                .peek(c -> c.setOrder(LiteralList.Order.NATURAL)) //
                .collect(Collectors.toCollection(HashSet::new));

        final HashSet<LiteralList> addedClauses = adaptedNewClauses.stream() //
                .filter(c -> !adaptedOldClauses.contains(c)) //
                .collect(Collectors.toCollection(HashSet::new));
        final HashSet<LiteralList> removedClauses = adaptedOldClauses.stream() //
                .filter(c -> !adaptedNewClauses.contains(c)) //
                .collect(Collectors.toCollection(HashSet::new));

        final HashSet<LiteralList> allClauses = new HashSet<>(adaptedNewClauses);
        allClauses.addAll(adaptedOldClauses);
        return (addedClauses.size() + removedClauses.size()) / (double) allClauses.size();
    }

    private void collect(CNF cnf) {
        init(cnf);

        final CNF oldCnf = oldMig.getCnf();
        final Set<String> allVariables = new HashSet<>(oldCnf.getVariableMap().getVariableNames());
        allVariables.addAll(cnf.getVariableMap().getVariableNames());
        variables = new VariableMap(allVariables);

        final HashSet<LiteralList> adaptedNewClauses = cnf.getClauses().stream()
                .map(c -> c.adapt(cnf.getVariableMap(), variables).get()) //
                .peek(c -> c.setOrder(LiteralList.Order.NATURAL))
                .collect(Collectors.toCollection(HashSet::new));

        final HashSet<LiteralList> adaptedOldClauses = oldCnf.getClauses().stream() //
                .map(c -> c.adapt(oldCnf.getVariableMap(), variables).get()) //
                .peek(c -> c.setOrder(LiteralList.Order.NATURAL)) //
                .collect(Collectors.toCollection(HashSet::new));

        addedClauses = adaptedNewClauses.stream() //
                .filter(c -> !adaptedOldClauses.contains(c)) //
                .collect(Collectors.toCollection(HashSet::new));
        final HashSet<LiteralList> removedClauses = adaptedOldClauses.stream() //
                .filter(c -> !adaptedNewClauses.contains(c)) //
                .collect(Collectors.toCollection(HashSet::new));

        changes = addedClauses.isEmpty()
                ? removedClauses.isEmpty() ? Changes.UNCHANGED : Changes.REMOVED
                : removedClauses.isEmpty() ? Changes.ADDED : Changes.REPLACED;

        final HashSet<LiteralList> allClauses = new HashSet<>(adaptedNewClauses);
        allClauses.addAll(adaptedOldClauses);
        //		changeRatio = (addedClauses.size() + removedClauses.size()) / (double) allClauses.size();
    }

    private void core(CNF cnf, InternalMonitor monitor) {
        final int[] coreDead = oldMig.getVertices().stream() //
                .filter(Vertex::isCore) //
                .mapToInt(Vertex::getVar) //
                .map(l -> Clauses.adapt(l, oldMig.getCnf().getVariableMap(), cnf.getVariableMap())) //
                .filter(l -> l != 0) //
                .peek(l -> {
                    mig.getVertex(l).setStatus(Status.Core);
                    mig.getVertex(-l).setStatus(Status.Dead);
                })
                .toArray();
        switch (changes) {
            case ADDED:
                for (final int literal : coreDead) {
                    solver.getAssumptions().push(literal);
                    fixedFeatures[Math.abs(literal) - 1] = 0;
                }
                findCoreFeatures(monitor);
                break;
            case REMOVED:
                checkOldCoreLiterals(coreDead);
                break;
            case REPLACED:
                checkOldCoreLiterals(coreDead);
                for (final int literal : coreDead) {
                    fixedFeatures[Math.abs(literal) - 1] = 0;
                }
                findCoreFeatures(monitor);
                break;
            case UNCHANGED:
                break;
            default:
                throw new IllegalStateException(String.valueOf(changes));
        }
    }

    private long add(CNF cnf, boolean checkRedundancy, Collection<LiteralList> addedClauses) {
        Stream<LiteralList> cnfStream = cleanedClausesList.stream();
        if (checkRedundancy) {
            final Set<LiteralList> oldMigClauses = oldMig.getVertices().stream()
                    .flatMap(v -> v.getComplexClauses().stream())
                    .collect(Collectors.toCollection(HashSet::new));
            final HashSet<LiteralList> redundantClauses = oldMig.getCnf().getClauses().stream()
                    .map(c -> cleanClause(c, oldMig)) //
                    .filter(Objects::nonNull) //
                    .filter(c -> c.size() > 2) //
                    .filter(c -> !oldMigClauses.contains(c)) //
                    .map(c ->
                            c.adapt(oldMig.getCnf().getVariableMap(), variables).get()) //
                    .peek(c -> c.setOrder(LiteralList.Order.NATURAL)) //
                    .collect(Collectors.toCollection(HashSet::new));

            cnfStream = cnfStream //
                    .map(c -> c.adapt(cnf.getVariableMap(), variables).get()) //
                    .peek(c -> c.setOrder(LiteralList.Order.NATURAL));

            switch (changes) {
                case ADDED: {
                    if (add) {
                        final Sat4JSolver redundancySolver = new Sat4JSolver(new CNF(variables));
                        final int[] affectedVariables = addedClauses.stream()
                                .flatMapToInt(c -> IntStream.of(c.getLiterals()))
                                .map(Math::abs)
                                .distinct()
                                .toArray();
                        cnfStream = cnfStream
                                .sorted(lengthComparator)
                                .distinct()
                                .filter(c -> {
                                    if (c.size() < 3) {
                                        return true;
                                    }
                                    if (redundantClauses.contains(c)) {
                                        return false;
                                    }
                                    if (add && c.containsAnyVariable(affectedVariables)) {
                                        return !isRedundant(redundancySolver, c);
                                    }
                                    return true;
                                })
                                .peek(redundancySolver.getFormula()::push);
                    } else {
                        cnfStream = cnfStream
                                .sorted(lengthComparator)
                                .distinct()
                                .filter(c -> (c.size() < 3) || !redundantClauses.contains(c));
                    }
                    mig.setRedundancyStatus(BuildStatus.Incremental);
                    break;
                }
                case REMOVED: {
                    final Sat4JSolver redundancySolver = new Sat4JSolver(new CNF(variables));
                    cnfStream = cnfStream
                            .sorted(lengthComparator)
                            .distinct()
                            .filter(c -> {
                                if (c.size() < 3) {
                                    return true;
                                }
                                if (redundantClauses.contains(c)) {
                                    return !isRedundant(redundancySolver, c);
                                }
                                return true;
                            })
                            .peek(redundancySolver.getFormula()::push);
                    mig.setRedundancyStatus(mig.getRedundancyStatus());
                    break;
                }
                case REPLACED: {
                    if (add) {
                        final Sat4JSolver redundancySolver = new Sat4JSolver(new CNF(variables));
                        final int[] affectedVariables = addedClauses.stream()
                                .flatMapToInt(c -> IntStream.of(c.getLiterals()))
                                .map(Math::abs)
                                .distinct()
                                .toArray();
                        cnfStream = cnfStream
                                .sorted(lengthComparator)
                                .distinct()
                                .filter(c -> {
                                    if (c.size() < 3) {
                                        return true;
                                    }
                                    if (redundantClauses.contains(c)) {
                                        return !isRedundant(redundancySolver, c);
                                    } else {
                                        if (c.containsAnyVariable(affectedVariables)) {
                                            return !isRedundant(redundancySolver, c);
                                        }
                                        return true;
                                    }
                                })
                                .peek(redundancySolver.getFormula()::push);
                    } else {
                        final Sat4JSolver redundancySolver = new Sat4JSolver(new CNF(variables));
                        cnfStream = cnfStream
                                .sorted(lengthComparator)
                                .distinct()
                                .filter(c -> (c.size() < 3)
                                        || !redundantClauses.contains(c)
                                        || !isRedundant(redundancySolver, c))
                                .peek(redundancySolver.getFormula()::push);
                    }
                    mig.setRedundancyStatus(BuildStatus.Incremental);
                    break;
                }
                case UNCHANGED: {
                    cnfStream = cnfStream.distinct().filter(c -> (c.size() < 3) || !redundantClauses.contains(c));
                    mig.setRedundancyStatus(mig.getRedundancyStatus());
                    break;
                }
                default:
                    throw new IllegalStateException(String.valueOf(changes));
            }
            cnfStream = cnfStream
                    .map(c -> c.adapt(variables, cnf.getVariableMap()).get())
                    .peek(c -> c.setOrder(LiteralList.Order.NATURAL));
        } else {
            cnfStream = cnfStream.distinct();
            mig.setRedundancyStatus(BuildStatus.None);
        }
        return cnfStream.peek(mig::addClause).count();
    }

    protected void checkOldStrong() {
        switch (changes) {
            case REMOVED:
            case REPLACED:
                loop:
                for (final LiteralList strongEdge : oldMig.getDetectedStrong()) {
                    final LiteralList adaptClause = strongEdge
                            .adapt(
                                    oldMig.getCnf().getVariableMap(),
                                    mig.getCnf().getVariableMap())
                            .get();
                    if (adaptClause != null) {
                        final int[] literals = adaptClause.getLiterals();
                        final int l1 = -literals[0];
                        final int l2 = -literals[1];
                        for (final LiteralList solution : solver.getSolutionHistory()) {
                            if (solution.containsAllLiterals(l1, l2)) {
                                continue loop;
                            }
                        }
                        solver.getAssumptions().push(l1);
                        solver.getAssumptions().push(l2);
                        switch (solver.hasSolution()) {
                            case FALSE:
                                cleanedClausesList.add(adaptClause);
                                mig.getDetectedStrong().add(adaptClause);
                            case TIMEOUT:
                            case TRUE:
                                break;
                        }
                        solver.getAssumptions().pop();
                        solver.getAssumptions().pop();
                    }
                }
                break;
            case ADDED:
            case UNCHANGED:
                for (final LiteralList strongEdge : oldMig.getDetectedStrong()) {
                    final LiteralList adaptClause = strongEdge
                            .adapt(
                                    oldMig.getCnf().getVariableMap(),
                                    mig.getCnf().getVariableMap())
                            .get();
                    if (adaptClause != null) {
                        cleanedClausesList.add(adaptClause);
                        mig.getDetectedStrong().add(adaptClause);
                    }
                }
                break;
            default:
                throw new IllegalStateException(String.valueOf(changes));
        }
    }

    protected void checkOldCoreLiterals(int[] coreDead) {
        solver.setSelectionStrategy(SStrategy.inverse(fixedFeatures));
        for (final int literal : coreDead) {
            final int varX = fixedFeatures[Math.abs(literal) - 1];
            if (varX == 0) {
                mig.getVertex(-literal).setStatus(Status.Normal);
                mig.getVertex(literal).setStatus(Status.Normal);
            } else {
                solver.getAssumptions().push(-varX);
                switch (solver.hasSolution()) {
                    case FALSE:
                        solver.getAssumptions().replaceLast(varX);
                        mig.getVertex(varX).setStatus(Status.Core);
                        mig.getVertex(-varX).setStatus(Status.Dead);
                        break;
                    case TIMEOUT:
                        solver.getAssumptions().pop();
                        fixedFeatures[Math.abs(literal) - 1] = 0;
                        mig.getVertex(-varX).setStatus(Status.Normal);
                        mig.getVertex(varX).setStatus(Status.Normal);
                        break;
                    case TRUE:
                        solver.getAssumptions().pop();
                        mig.getVertex(-varX).setStatus(Status.Normal);
                        mig.getVertex(varX).setStatus(Status.Normal);
                        LiteralList.resetConflicts(fixedFeatures, solver.getInternalSolution());
                        solver.shuffleOrder(random);
                        break;
                }
            }
        }
    }

    public boolean isAdd() {
        return add;
    }

    public void setAdd(boolean add) {
        this.add = add;
    }
}
