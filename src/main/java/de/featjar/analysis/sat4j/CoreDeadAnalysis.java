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

import java.util.Arrays;

import org.sat4j.core.VecInt;
import org.sat4j.specs.IteratorInt;

import de.featjar.analysis.sat4j.solver.SStrategy;
import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.analysis.solver.RuntimeContradictionException;
import de.featjar.clauses.LiteralList;
import de.featjar.util.data.Identifier;
import de.featjar.util.job.InternalMonitor;

/**
 * Finds core and dead features.
 *
 * @author Sebastian Krieter
 */
public class CoreDeadAnalysis extends AVariableAnalysis<LiteralList> {

    public static final Identifier<LiteralList> identifier = new Identifier<>();

    private Sat4JSolver solver;

    @Override
    public Identifier<LiteralList> getIdentifier() {
        return identifier;
    }

    public CoreDeadAnalysis() {
        super();
    }

    public CoreDeadAnalysis(LiteralList variables) {
        super();
        this.variables = variables;
    }

    @Override
    public LiteralList analyze(Sat4JSolver solver, InternalMonitor monitor) throws Exception {
        this.solver = solver;
        return analyze1(monitor);
    }

    // currently unused (divide & conquer)
    public LiteralList analyze2(Sat4JSolver solver, InternalMonitor monitor) throws Exception {
        final int initialAssignmentLength = solver.getAssumptions().size();
        solver.setSelectionStrategy(SStrategy.positive());
        int[] model1 = solver.findSolution().getLiterals();

        if (model1 != null) {
            solver.setSelectionStrategy(SStrategy.negative());
            final int[] model2 = solver.findSolution().getLiterals();

            if (variables != null) {
                final int[] model3 = new int[model1.length];
                for (int i = 0; i < variables.getLiterals().length; i++) {
                    final int index = variables.getLiterals()[i] - 1;
                    if (index >= 0) {
                        model3[index] = model1[index];
                    }
                }
                model1 = model3;
            }

            for (int i = 0; i < initialAssignmentLength; i++) {
                model1[Math.abs(solver.getAssumptions().peek(i)) - 1] = 0;
            }

            LiteralList.resetConflicts(model1, model2);
            solver.setSelectionStrategy(SStrategy.inverse(model1));

            vars = new VecInt(model1.length);
            split(model1, 0, model1.length);
        }
        return new LiteralList(solver.getAssumptions()
                .asArray(initialAssignmentLength, solver.getAssumptions().size()));
    }

    VecInt vars;

    private void split(int[] model, int start, int end) {
        vars.clear();
        for (int j = start; j < end; j++) {
            final int var = model[j];
            if (var != 0) {
                vars.push(-var);
            }
        }
        switch (vars.size()) {
            case 0:
                return;
            case 1:
                test(model, 0);
                break;
            case 2:
                test(model, 0);
                test(model, 1);
                break;
            default:
                try {
                    solver.getFormula().push(new LiteralList(Arrays.copyOf(vars.toArray(), vars.size())));
                    switch (solver.hasSolution()) {
                        case FALSE:
                            foundVariables(model, vars);
                            break;
                        case TIMEOUT:
                            reportTimeout();
                            break;
                        case TRUE:
                            LiteralList.resetConflicts(model, solver.getInternalSolution());
                            solver.shuffleOrder(getRandom());

                            final int halfLength = (end - start) / 2;
                            if (halfLength > 0) {
                                split(model, start + halfLength, end);
                                split(model, start, start + halfLength);
                            }
                            break;
                    }
                    solver.getFormula().pop();
                } catch (final RuntimeContradictionException e) {
                    foundVariables(model, vars);
                }
                break;
        }
    }

    private void test(int[] model, int i) {
        final int var = vars.get(i);
        solver.getAssumptions().push(var);
        switch (solver.hasSolution()) {
            case FALSE:
                solver.getAssumptions().replaceLast(-var);
                model[Math.abs(var) - 1] = 0;
                break;
            case TIMEOUT:
                solver.getAssumptions().pop();
                reportTimeout();
                break;
            case TRUE:
                solver.getAssumptions().pop();
                LiteralList.resetConflicts(model, solver.getInternalSolution());
                solver.shuffleOrder(getRandom());
                break;
        }
    }

    private void foundVariables(int[] model, VecInt vars) {
        for (final IteratorInt iterator = vars.iterator(); iterator.hasNext(); ) {
            final int var = iterator.next();
            solver.getAssumptions().push(-var);
            model[Math.abs(var) - 1] = 0;
        }
    }

    public LiteralList analyze1(InternalMonitor monitor) throws Exception {
        final int initialAssignmentLength = solver.getAssumptions().size();
        solver.setSelectionStrategy(SStrategy.positive());
        int[] model1 = solver.findSolution().getLiterals();

		// TODO return null for contradiction
        if (model1 != null) {
            solver.setSelectionStrategy(SStrategy.inverse(model1));
            final int[] model2 = solver.findSolution().getLiterals();

            if (variables != null) {
                final int[] model3 = new int[model1.length];
                for (int i = 0; i < variables.getLiterals().length; i++) {
                    final int index = variables.getLiterals()[i] - 1;
                    if (index >= 0) {
                        model3[index] = model1[index];
                    }
                }
                model1 = model3;
            }

            for (int i = 0; i < initialAssignmentLength; i++) {
                model1[Math.abs(solver.getAssumptions().peek(i)) - 1] = 0;
            }

            LiteralList.resetConflicts(model1, model2);

            for (int i = 0; i < model1.length; i++) {
                final int varX = model1[i];
                if (varX != 0) {
                    solver.getAssumptions().push(-varX);
                    switch (solver.hasSolution()) {
                        case FALSE:
                            solver.getAssumptions().replaceLast(varX);
                            break;
                        case TIMEOUT:
                            solver.getAssumptions().pop();
                            reportTimeout();
                            break;
                        case TRUE:
                            solver.getAssumptions().pop();
                            LiteralList.resetConflicts(model1, solver.getInternalSolution());
                            solver.shuffleOrder(getRandom());
                            break;
                    }
                }
            }
        }

        return new LiteralList(solver.getAssumptions()
                .asArray(initialAssignmentLength, solver.getAssumptions().size()));
    }
}
