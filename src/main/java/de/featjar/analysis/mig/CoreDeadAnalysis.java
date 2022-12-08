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
package de.featjar.analysis.mig;

import de.featjar.analysis.mig.solver.MIG;
import de.featjar.analysis.mig.solver.Sat4JMIGSolver;
import de.featjar.analysis.mig.solver.Vertex;
import de.featjar.analysis.mig.solver.visitor.CollectingVisitor;
import de.featjar.analysis.mig.solver.visitor.Traverser;
import de.featjar.analysis.sat4j.solver.SStrategy;
import de.featjar.clauses.LiteralList;
import de.featjar.util.data.Identifier;
import de.featjar.util.job.InternalMonitor;
import java.util.stream.IntStream;
import org.sat4j.core.VecInt;

/**
 * Finds core and dead features using a {@link MIG model implication graph}.
 *
 * @author Sebastian Krieter
 */
public class CoreDeadAnalysis extends Sat4JMIGAnalysis<LiteralList> {

    public static final Identifier<LiteralList> identifier = new Identifier<>();

    protected int[] fixedVariables;
    protected int newCount;

    public void setFixedFeatures(int[] fixedVariables, int newCount) {
        this.fixedVariables = fixedVariables;
        this.newCount = newCount;
    }

    public void resetFixedFeatures() {
        fixedVariables = new int[0];
        newCount = 0;
    }

    @Override
    public Identifier<LiteralList> getIdentifier() {
        return identifier;
    }

    public CoreDeadAnalysis() {
        super();
        resetFixedFeatures();
    }

    @Override
    public LiteralList analyze(Sat4JMIGSolver solver, InternalMonitor monitor) throws Exception {
        monitor.setTotalWork(solver.getVariables().getVariableCount() + 2);

        final Traverser traverser = solver.mig.traverse();
        solver.getAssumptions().ensureSize(fixedVariables.length + 1);
        final int[] knownValues = new int[solver.getVariables().getVariableCount()];

        for (final int fixedVar : fixedVariables) {
            final int var = Math.abs(fixedVar);
            knownValues[var - 1] = fixedVar;
            monitor.step();
        }

        // get core / dead variables
        for (final Vertex vertex : solver.mig.getVertices()) {
            if (vertex.isCore()) {
                final int var = vertex.getVar();
                knownValues[Math.abs(var) - 1] = var;
                monitor.step();
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

        monitor.setTotalWork(valuesToCompute.size() + computedValues.size() + 3);

        for (int i = 0; i < computedValues.size(); i++) {
            final int computedVar = computedValues.get(i);
            final int var = Math.abs(computedVar);
            knownValues[var - 1] = computedVar;
            monitor.step();
        }

        for (final int var : knownValues) {
            if (var != 0) {
                solver.getAssumptions().push(var);
            }
        }
        monitor.checkCancel();

        if (!valuesToCompute.isEmpty()) {
            solver.setSelectionStrategy(SStrategy.positive());
            final int[] possibleValues = solver.findSolution().getLiterals();
            monitor.step();

            if (possibleValues != null) {
                solver.setSelectionStrategy(SStrategy.inverse(possibleValues));
                final int[] model2 = solver.findSolution().getLiterals();
                monitor.step();

                LiteralList.resetConflicts(possibleValues, model2);

                IntStream.range(0, knownValues.length).parallel().forEach(k -> {
                    final int var = knownValues[k];
                    if ((var != 0) && (possibleValues[k] != 0)) {
                        possibleValues[k] = 0;
                    }
                });
                monitor.step();

                sat(solver, possibleValues, valuesToCompute, monitor, traverser);
            }
        }
        return new LiteralList(
                solver.getAssumptions().asArray(0, solver.getAssumptions().size()));
    }

    private void sat(
            Sat4JMIGSolver solver,
            int[] possibleValues,
            VecInt valuesToCalculate,
            InternalMonitor monitor,
            Traverser traverser) {
        final CollectingVisitor visitor = new CollectingVisitor();
        traverser.setVisitor(visitor);

        while (!valuesToCalculate.isEmpty()) {
            final int varX = valuesToCalculate.last();
            valuesToCalculate.pop();
            final int i = Math.abs(varX) - 1;
            if (possibleValues[i] == varX) {
                solver.getAssumptions().push(-varX);
                switch (solver.hasSolution()) {
                    case FALSE:
                        solver.getAssumptions().replaceLast(varX);
                        possibleValues[i] = 0;
                        monitor.step();
                        traverser.traverseStrong(varX);
                        final VecInt newFoundValues = visitor.getResult()[0];
                        for (int j = 0; j < newFoundValues.size(); j++) {
                            final int var = newFoundValues.get(j);
                            solver.getAssumptions().push(var);
                            possibleValues[Math.abs(var) - 1] = 0;
                            monitor.step();
                        }
                        break;
                    case TIMEOUT:
                        solver.getAssumptions().pop();
                        possibleValues[Math.abs(varX) - 1] = 0;
                        monitor.step();
                        break;
                    case TRUE:
                        solver.getAssumptions().pop();
                        LiteralList.resetConflicts(possibleValues, solver.getInternalSolution());
                        solver.shuffleOrder(getRandom());
                        break;
                }
            }
        }
    }
}
