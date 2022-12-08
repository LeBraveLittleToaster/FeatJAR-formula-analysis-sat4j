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
import de.featjar.analysis.solver.SatSolver;
import de.featjar.clauses.LiteralList;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.util.data.Identifier;
import de.featjar.util.job.InternalMonitor;
import org.sat4j.core.VecInt;

/**
 * Generates configurations for a given propositional formula such that one-wise
 * feature coverage is achieved.
 *
 * @author Sebastian Krieter
 */
public class OneWiseConfigurationGenerator extends AbstractConfigurationGenerator {

    public static final Identifier<SolutionList> identifier = new Identifier<>();

    @Override
    public Identifier<SolutionList> getIdentifier() {
        return identifier;
    }

    public enum CoverStrategy {
        POSITIVE,
        NEGATIVE
    }

    private CoverStrategy coverStrategy = CoverStrategy.NEGATIVE;

    private int[] variables;

    private VecInt variablesToCover;

    private int initialAssignmentLength;

    public OneWiseConfigurationGenerator() {
        this(null);
    }

    public OneWiseConfigurationGenerator(int[] features) {
        super();
        setFeatures(features);
    }

    public int[] getFeatures() {
        return variables;
    }

    public void setFeatures(int[] features) {
        variables = features;
    }

    public CoverStrategy getCoverMode() {
        return coverStrategy;
    }

    public void setCoverMode(CoverStrategy coverStrategy) {
        this.coverStrategy = coverStrategy;
    }

    @Override
    protected void init(InternalMonitor monitor) {
        initialAssignmentLength = solver.getAssumptions().size();

        switch (coverStrategy) {
            case NEGATIVE:
                solver.setSelectionStrategy(SStrategy.negative());
                break;
            case POSITIVE:
                solver.setSelectionStrategy(SStrategy.positive());
                break;
            default:
                throw new RuntimeException("Unknown " + CoverStrategy.class.getName() + ": " + coverStrategy);
        }

        if (solver.hasSolution() == SatSolver.SatResult.TRUE) {
            variablesToCover = new VecInt();

            if (variables != null) {
                for (int i = 0; i < variables.length; i++) {
                    final int var = variables[i];
                    if (var > 0) {
                        variablesToCover.push(var);
                    }
                }
            }
        }
    }

    @Override
    public LiteralList get() {
        if ((variablesToCover != null) && !variablesToCover.isEmpty()) {
            boolean firstVar = true;
            int[] lastSolution = null;
            for (int i = variablesToCover.size() - 1; i >= 0; i--) {
                int var = variablesToCover.get(i);
                if (var == 0) {
                    continue;
                }

                switch (coverStrategy) {
                    case NEGATIVE:
                        var = -var;
                        break;
                    case POSITIVE:
                        break;
                    default:
                        throw new RuntimeException("Unknown " + CoverStrategy.class.getName() + ": " + coverStrategy);
                }

                solver.getAssumptions().pop(var);
                switch (solver.hasSolution()) {
                    case FALSE:
                        solver.getAssumptions().replaceLast(var);
                        if (firstVar) {
                            variablesToCover.set(i, 0);
                        }
                        break;
                    case TIMEOUT:
                        solver.getAssumptions().pop();
                        variablesToCover.set(i, 0);
                        break;
                    case TRUE:
                        lastSolution = solver.getInternalSolution();
                        switch (coverStrategy) {
                            case NEGATIVE:
                                for (int j = i; j < variablesToCover.size(); j++) {
                                    if (lastSolution[Math.abs(var) - 1] < 0) {
                                        variablesToCover.set(i, 0);
                                    }
                                }
                                break;
                            case POSITIVE:
                                for (int j = i; j < variablesToCover.size(); j++) {
                                    if (lastSolution[Math.abs(var) - 1] > 0) {
                                        variablesToCover.set(i, 0);
                                    }
                                }
                                break;
                            default:
                                throw new RuntimeException(
                                        "Unknown " + CoverStrategy.class.getName() + ": " + coverStrategy);
                        }
                        firstVar = false;
                        break;
                }
            }
            final LiteralList result =
                    lastSolution == null ? null : new LiteralList(lastSolution, LiteralList.Order.INDEX, false);
            solver.getAssumptions().clear(initialAssignmentLength);
            while (!variablesToCover.isEmpty()) {
                final int var = variablesToCover.last();
                if (var == 0) {
                    variablesToCover.pop();
                } else {
                    break;
                }
            }
            return result;
        }
        return null;
    }
}
