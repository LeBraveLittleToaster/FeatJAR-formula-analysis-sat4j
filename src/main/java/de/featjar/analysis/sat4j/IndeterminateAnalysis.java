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
import de.featjar.clauses.LiteralList;
import de.featjar.util.data.Identifier;
import de.featjar.util.job.InternalMonitor;
import java.util.Arrays;
import java.util.List;
import org.sat4j.core.VecInt;

/**
 * Finds indeterminate features.
 *
 * @author Sebastian Krieter
 */
public class IndeterminateAnalysis extends AVariableAnalysis<LiteralList> { // todo: variable-analysis does not work
    // reliably (false positives) (use old
    // analysis first?)

    public static final Identifier<LiteralList> identifier = new Identifier<>();

    @Override
    public Identifier<LiteralList> getIdentifier() {
        return identifier;
    }

    @Override
    public LiteralList analyze(Sat4JSolver solver, InternalMonitor monitor) throws Exception {
        if (variables == null) {
            variables = LiteralList.getVariables(solver.getVariables());
        }
        monitor.setTotalWork(variables.getLiterals().length);

        final VecInt resultList = new VecInt();
        variableLoop:
        for (final int variable : variables.getLiterals()) {
            final Sat4JSolver modSolver = new Sat4JSolver(solver.getVariables());
            final List<LiteralList> clauses = solver.getCnf().getClauses();
            for (final LiteralList clause : clauses) {
                final LiteralList newClause = clause.removeVariables(variable);
                if (newClause != null) {
                    try {
                        modSolver.getFormula().push(newClause);
                    } catch (final RuntimeContradictionException e) {
                        monitor.step();
                        continue variableLoop;
                    }
                } else {
                    monitor.step();
                    continue variableLoop;
                }
            }

            final SatSolver.SatResult hasSolution = modSolver.hasSolution();
            switch (hasSolution) {
                case FALSE:
                    break;
                case TIMEOUT:
                    reportTimeout();
                    break;
                case TRUE:
                    resultList.push(variable);
                    break;
                default:
                    throw new AssertionError(hasSolution);
            }
            monitor.step();
        }
        return new LiteralList(Arrays.copyOf(resultList.toArray(), resultList.size()));
    }
}
