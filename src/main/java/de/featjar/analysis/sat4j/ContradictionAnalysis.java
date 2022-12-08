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
package de.featjar.analysis.sat4j;

import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.analysis.solver.RuntimeContradictionException;
import de.featjar.analysis.solver.SatSolver;
import de.featjar.clauses.CNF;
import de.featjar.clauses.LiteralList;
import de.featjar.util.data.Identifier;
import de.featjar.util.job.InternalMonitor;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Finds contradicting clauses with respect to a given {@link CNF}. This
 * analysis works by iteratively adding each clause group (see
 * {@link AClauseAnalysis}) to the given {@link CNF}. If a clause group
 * contradicts the current formula, it is marked as a contradiction and removed
 * from the {@link CNF}. Otherwise it is kept as part of the {@link CNF} for the
 * remaining analysis. Clauses are added in the same order a they appear in the
 * given clauses list.<br>
 * For an independent analysis of every clause group use
 * {@link IndependentContradictionAnalysis}.
 *
 * @author Sebastian Krieter
 *
 * @see IndependentContradictionAnalysis
 */
public class ContradictionAnalysis extends AClauseAnalysis<List<LiteralList>> {

    public static final Identifier<List<LiteralList>> identifier = new Identifier<>();

    @Override
    public Identifier<List<LiteralList>> getIdentifier() {
        return identifier;
    }

    public ContradictionAnalysis() {
        super();
    }

    public ContradictionAnalysis(List<LiteralList> clauseList) {
        super();
        this.clauseList = clauseList;
    }

    @Override
    public List<LiteralList> analyze(Sat4JSolver solver, InternalMonitor monitor) throws Exception {
        if (clauseList == null) {
            clauseList = solver.getCnf().getClauses();
        }
        if (clauseGroupSize == null) {
            clauseGroupSize = new int[clauseList.size()];
            Arrays.fill(clauseGroupSize, 1);
        }
        monitor.setTotalWork(clauseList.size() + 1);

        final List<LiteralList> resultList = new ArrayList<>(clauseGroupSize.length);
        for (int i = 0; i < clauseList.size(); i++) {
            resultList.add(null);
        }
        monitor.step();

        int endIndex = 0;
        for (int i = 0; i < clauseGroupSize.length; i++) {
            final int startIndex = endIndex;
            endIndex += clauseGroupSize[i];
            final List<LiteralList> subList = clauseList.subList(startIndex, endIndex);

            try {
                solver.getFormula().push(subList);
            } catch (final RuntimeContradictionException e) {
                resultList.set(i, clauseList.get(startIndex));
                monitor.step();
                continue;
            }

            final SatSolver.SatResult hasSolution = solver.hasSolution();
            switch (hasSolution) {
                case FALSE:
                    resultList.set(i, clauseList.get(startIndex));
                    solver.getFormula().pop(subList.size());
                    break;
                case TIMEOUT:
                    reportTimeout();
                    break;
                case TRUE:
                    break;
                default:
                    throw new AssertionError(hasSolution);
            }

            monitor.step();
        }

        return resultList;
    }
}
