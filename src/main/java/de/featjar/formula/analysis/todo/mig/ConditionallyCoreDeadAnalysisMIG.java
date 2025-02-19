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
package de.featjar.formula.analysis.todo.mig;

import de.featjar.formula.analysis.todo.mig.solver.ModalImplicationGraph;
import de.featjar.formula.analysis.todo.mig.solver.SAT4JMIGSolver;
import de.featjar.formula.analysis.todo.mig.solver.Vertex;
import de.featjar.formula.analysis.todo.mig.solver.visitor.CollectingVisitor;
import de.featjar.formula.analysis.todo.mig.solver.visitor.Traverser;
import de.featjar.formula.analysis.sat4j.solver.ISelectionStrategy;
import de.featjar.base.computation.Progress;
import org.sat4j.core.VecInt;

/**
 * Finds core and dead features using a {@link ModalImplicationGraph model implication graph}.
 *
 * @author Sebastian Krieter
 */
public class ConditionallyCoreDeadAnalysisMIG extends Sat4JMIGAnalysis<SortedIntegerList> {
    protected int[] fixedVariables;
    protected int[] variableOrder;
    protected int newCount;

    public void setFixedFeatures(int[] fixedVariables, int newCount) {
        this.fixedVariables = fixedVariables;
        this.newCount = newCount;
    }

    public void setVariableOrder(int[] variableOrder) {
        this.variableOrder = variableOrder;
    }

    public void resetFixedFeatures() {
        fixedVariables = new int[0];
        newCount = 0;
    }

    public ConditionallyCoreDeadAnalysisMIG() {
        resetFixedFeatures();
    }

    @Override
    public SortedIntegerList analyze(SAT4JMIGSolver solver, Progress progress) throws Exception {
        monitor.setTotalSteps(solver.getVariableMap().getVariableCount() + 2);

        final Traverser traverser = solver.modalImplicationGraph.traverse();
        solver.getAssignment().ensureSize(fixedVariables.length + 1);
        final int[] knownValues = new int[solver.getVariableMap().getVariableCount()];

        for (final int fixedVar : fixedVariables) {
            final int var = Math.abs(fixedVar);
            knownValues[var - 1] = fixedVar;
            monitor.addStep();
        }

        // get core / dead variables
        for (final Vertex vertex : solver.modalImplicationGraph.getVertices()) {
            if (vertex.isCore()) {
                final int var = vertex.getVar();
                knownValues[Math.abs(var) - 1] = var;
                monitor.addStep();
            }
        }

        traverser.setModel(knownValues);
        final CollectingVisitor visitor = new CollectingVisitor();
        traverser.setVisitor(visitor);
        for (int i = 0; i < newCount; i++) {
            traverser.traverse(fixedVariables[i]);
        }
        final VecInt computedValues = visitor.getResult()[0];
        VecInt valuesToCompute = visitor.getResult()[1];

        monitor.setTotalSteps(valuesToCompute.size() + computedValues.size() + 3);

        for (int i = 0; i < computedValues.size(); i++) {
            final int computedVar = computedValues.get(i);
            final int var = Math.abs(computedVar);
            knownValues[var - 1] = computedVar;
            monitor.addStep();
        }

        if (variableOrder != null) {
            final VecInt sortedValuesToCalculate = new VecInt(valuesToCompute.size());
            for (int i = variableOrder.length - 1; i >= 0; i--) {
                final int var = variableOrder[i];
                if (valuesToCompute.contains(var)) {
                    sortedValuesToCalculate.push(var);
                }
                if (valuesToCompute.contains(-var)) {
                    sortedValuesToCalculate.push(-var);
                }
            }
            valuesToCompute = sortedValuesToCalculate;
        }

        for (final int var : knownValues) {
            if (var != 0) {
                solver.getAssignment().add(var);
            }
        }
        monitor.checkCancel();

        if (!valuesToCompute.isEmpty()) {
            solver.setSelectionStrategy(ISelectionStrategy.positive());
            final int[] unknownValues = solver.findSolution().getLiterals();
            monitor.addStep();

            if (unknownValues != null) {
                solver.setSelectionStrategy(ISelectionStrategy.negative());
                final int[] model2 = solver.findSolution().getLiterals();
                monitor.addStep();

                SortedIntegerList.resetConflicts(unknownValues, model2);
                solver.setSelectionStrategy(ISelectionStrategy.inverse(unknownValues));

                for (int k = 0; k < knownValues.length; k++) {
                    final int var = knownValues[k];
                    if ((var != 0) && (unknownValues[k] != 0)) {
                        unknownValues[k] = 0;
                    }
                }
                monitor.addStep();

                sat(solver, unknownValues, valuesToCompute, monitor, traverser);
            }
        }
        return new SortedIntegerList(
                solver.getAssignment().asArray(0, solver.getAssignment().size()));
    }

    private void sat(
            SAT4JMIGSolver solver,
            int[] unknownValues,
            VecInt valuesToCalculate,
            IMonitor monitor,
            Traverser traverser) {
        final CollectingVisitor visitor = new CollectingVisitor();
        traverser.setVisitor(visitor);

        while (!valuesToCalculate.isEmpty()) {
            final int varX = valuesToCalculate.last();
            valuesToCalculate.pop();
            final int i = Math.abs(varX) - 1;
            if (unknownValues[i] == varX) {
                solver.getAssignment().add(-varX);
                switch (solver.hasSolution()) {
                    case FALSE:
                        solver.getAssignment().replaceLast(varX);
                        unknownValues[i] = 0;
                        monitor.addStep();
                        traverser.traverseStrong(varX);
                        final VecInt newFoundValues = visitor.getResult()[0];
                        for (int j = 0; j < newFoundValues.size(); j++) {
                            final int var = newFoundValues.get(j);
                            solver.getAssignment().add(var);
                            unknownValues[Math.abs(var) - 1] = 0;
                            monitor.addStep();
                        }
                        break;
                    case TIMEOUT:
                        solver.getAssignment().remove();
                        unknownValues[Math.abs(varX) - 1] = 0;
                        monitor.addStep();
                        break;
                    case TRUE:
                        solver.getAssignment().remove();
                        SortedIntegerList.resetConflicts(unknownValues, solver.getInternalSolution());
                        solver.shuffleOrder(getRandom());
                        break;
                }
            }
        }
    }
}
