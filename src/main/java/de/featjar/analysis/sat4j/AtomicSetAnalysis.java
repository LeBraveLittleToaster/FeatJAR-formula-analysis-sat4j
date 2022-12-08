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

import de.featjar.analysis.sat4j.solver.SStrategy;
import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.clauses.LiteralList;
import de.featjar.util.data.Identifier;
import de.featjar.util.job.InternalMonitor;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Finds atomic sets.
 *
 * @author Sebastian Krieter
 */
public class AtomicSetAnalysis extends Sat4JAnalysis<List<LiteralList>> { // todo: AVariableAnalysis

    public static final Identifier<List<LiteralList>> identifier = new Identifier<>();

    @Override
    public Identifier<List<LiteralList>> getIdentifier() {
        return identifier;
    }

    public AtomicSetAnalysis() {
        super();
    }

    @Override
    public List<LiteralList> analyze(Sat4JSolver solver, InternalMonitor monitor) throws Exception {
        final List<LiteralList> result = new ArrayList<>();
        //		if (variables == null) {
        //			variables = LiteralList.getVariables(solver.getVariables());
        //		}

        // for all variables not in this.variables, set done[...] to 2

        solver.setSelectionStrategy(SStrategy.positive());
        final int[] model1 = solver.findSolution().getLiterals();
        final List<LiteralList> solutions = solver.rememberSolutionHistory(1000);

        if (model1 != null) {
            // initial atomic set consists of core and dead features
            solver.setSelectionStrategy(SStrategy.negative());
            final int[] model2 = solver.findSolution().getLiterals();
            solver.setSelectionStrategy(SStrategy.positive());

            final byte[] done = new byte[model1.length];

            final int[] model1Copy = Arrays.copyOf(model1, model1.length);

            LiteralList.resetConflicts(model1Copy, model2);
            for (int i = 0; i < model1Copy.length; i++) {
                final int varX = model1Copy[i];
                if (varX != 0) {
                    solver.getAssumptions().push(-varX);
                    switch (solver.hasSolution()) {
                        case FALSE:
                            done[i] = 2;
                            solver.getAssumptions().replaceLast(varX);
                            break;
                        case TIMEOUT:
                            solver.getAssumptions().pop();
                            reportTimeout();
                            break;
                        case TRUE:
                            solver.getAssumptions().pop();
                            LiteralList.resetConflicts(model1Copy, solver.getInternalSolution());
                            solver.shuffleOrder(getRandom());
                            break;
                    }
                }
            }
            final int fixedSize = solver.getAssumptions().size();
            result.add(new LiteralList(solver.getAssumptions().asArray(0, fixedSize)));

            solver.setSelectionStrategy(SStrategy.random(getRandom()));

            for (int i = 0; i < model1.length; i++) {
                if (done[i] == 0) {
                    done[i] = 2;

                    int[] xModel0 = Arrays.copyOf(model1, model1.length);

                    final int mx0 = xModel0[i];
                    solver.getAssumptions().push(mx0);

                    inner:
                    for (int j = i + 1; j < xModel0.length; j++) {
                        final int my0 = xModel0[j];
                        if ((my0 != 0) && (done[j] == 0)) {
                            for (final LiteralList solution : solutions) {
                                final int mxI = solution.getLiterals()[i];
                                final int myI = solution.getLiterals()[j];
                                if ((mx0 == mxI) != (my0 == myI)) {
                                    continue inner;
                                }
                            }

                            solver.getAssumptions().push(-my0);

                            switch (solver.hasSolution()) {
                                case FALSE:
                                    done[j] = 1;
                                    break;
                                case TIMEOUT:
                                    reportTimeout();
                                    break;
                                case TRUE:
                                    LiteralList.resetConflicts(xModel0, solver.getInternalSolution());
                                    solver.shuffleOrder(getRandom());
                                    break;
                            }
                            solver.getAssumptions().pop();
                        }
                    }

                    solver.getAssumptions().pop();
                    solver.getAssumptions().push(-mx0);

                    switch (solver.hasSolution()) {
                        case FALSE:
                            break;
                        case TIMEOUT:
                            for (int j = i + 1; j < xModel0.length; j++) {
                                done[j] = 0;
                            }
                            reportTimeout();
                            break;
                        case TRUE:
                            xModel0 = solver.getInternalSolution();
                            break;
                    }

                    for (int j = i + 1; j < xModel0.length; j++) {
                        if (done[j] == 1) {
                            final int my0 = xModel0[j];
                            if (my0 != 0) {
                                solver.getAssumptions().push(-my0);

                                switch (solver.hasSolution()) {
                                    case FALSE:
                                        done[j] = 2;
                                        solver.getAssumptions().replaceLast(my0);
                                        break;
                                    case TIMEOUT:
                                        done[j] = 0;
                                        solver.getAssumptions().pop();
                                        reportTimeout();
                                        break;
                                    case TRUE:
                                        done[j] = 0;
                                        LiteralList.resetConflicts(xModel0, solver.getInternalSolution());
                                        solver.shuffleOrder(getRandom());
                                        solver.getAssumptions().pop();
                                        break;
                                }
                            } else {
                                done[j] = 0;
                            }
                        }
                    }

                    result.add(new LiteralList(solver.getAssumptions()
                            .asArray(fixedSize, solver.getAssumptions().size())));
                    solver.getAssumptions().clear(fixedSize);
                }
            }
        }
        return result;
    }
}
