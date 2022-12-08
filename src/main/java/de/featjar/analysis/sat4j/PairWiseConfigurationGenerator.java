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

import de.featjar.analysis.mig.solver.MIG;
import de.featjar.analysis.mig.solver.MIGBuilder;
import de.featjar.analysis.mig.solver.RegularMIGBuilder;
import de.featjar.analysis.mig.solver.Vertex;
import de.featjar.analysis.sat4j.solver.AbstractSat4JSolver;
import de.featjar.analysis.sat4j.solver.SStrategy;
import de.featjar.analysis.solver.RuntimeContradictionException;
import de.featjar.clauses.LiteralList;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.util.data.Identifier;
import de.featjar.util.job.Executor;
import de.featjar.util.job.InternalMonitor;
import java.util.Arrays;
import java.util.Random;

/**
 * IncLing sampling algorithm. Generates configurations for a given
 * propositional formula such that two-wise feature coverage is achieved.
 *
 * @author Sebastian Krieter
 */
public class PairWiseConfigurationGenerator extends AbstractConfigurationGenerator {

    public static final Identifier<SolutionList> identifier = new Identifier<>();

    @Override
    public Identifier<SolutionList> getIdentifier() {
        return identifier;
    }

    private static class FeatureIndex implements Comparable<FeatureIndex> {

        private int coveredCombinations = 0, selected = 0;
        private final int index;
        private int priority = 0;

        public FeatureIndex(int index) {
            this.index = index;
        }

        @Override
        public int compareTo(FeatureIndex o) {
            final int result = coveredCombinations - o.coveredCombinations;
            return result != 0 ? result : priority - o.priority;
        }

        public int getIndex() {
            return index;
        }

        public int getSelected() {
            return selected;
        }

        public void setCoveredCombinations(int coveredCombinations) {
            this.coveredCombinations = coveredCombinations;
        }

        public void setSelected(int selected) {
            this.selected = selected;
        }

        public void setPriority(int priority) {
            this.priority = priority;
        }

        @Override
        public String toString() {
            return index + "[" + coveredCombinations + ", " + selected + "]";
        }
    }

    public static final boolean VERBOSE = false;

    private static final byte BIT_00 = 1 << 0;
    private static final byte BIT_01 = 1 << 1;
    private static final byte BIT_10 = 1 << 2;
    private static final byte BIT_11 = 1 << 3;

    private FeatureIndex[] featureIndexArray = new FeatureIndex[0];
    private byte[] combinations = new byte[0];
    private byte[] combinations2 = new byte[0];
    private byte[] core = new byte[0];

    private int mode;
    private int combinationCount;
    private int numVariables;
    private int numberOfFixedFeatures;

    private boolean[] featuresUsedOrg;
    private Random random = new Random(0);

    private void addCombinationsFromModel(int[] curModel) {
        for (int i = 0; i < combinations2.length; i++) {
            final int a = (i / numVariables);
            final int b = (i % numVariables);
            if (a == b) {
                continue;
            }

            final byte bit1;
            if (curModel[a] < 0) {
                if (curModel[b] < 0) {
                    bit1 = BIT_00;
                } else {
                    bit1 = BIT_01;
                }
            } else {
                if (curModel[b] < 0) {
                    bit1 = BIT_10;
                } else {
                    bit1 = BIT_11;
                }
            }
            combinations2[i] |= (bit1);
        }
    }

    private void addInvalidCombinations() {
        combinationCount = combinations2.length << 2;
        for (int i = 0; i < combinations.length; i++) {
            final int a = (i / numVariables);
            final int b = (i % numVariables);
            if (a == b) {
                combinationCount -= 4;
                combinations2[i] = 0x00;
                continue;
            }
            final byte coreA = core[a];
            final byte coreB = core[b];
            if (coreA != 0) {
                if (coreB != 0) {
                    if (coreA > 0) {
                        if (coreB > 0) {
                            combinations2[i] = (BIT_00 | BIT_01 | BIT_10);
                        } else {
                            combinations2[i] = (BIT_00 | BIT_01 | BIT_11);
                        }
                    } else {
                        if (coreB > 0) {
                            combinations2[i] = (BIT_00 | BIT_11 | BIT_10);
                        } else {
                            combinations2[i] = (BIT_10 | BIT_01 | BIT_11);
                        }
                    }
                } else {
                    if (coreA > 0) {
                        combinations2[i] = (BIT_00 | BIT_01);
                    } else {
                        combinations2[i] = (BIT_10 | BIT_11);
                    }
                }
            } else {
                if (coreB != 0) {
                    if (coreB > 0) {
                        combinations2[i] = (BIT_00 | BIT_10);
                    } else {
                        combinations2[i] = (BIT_01 | BIT_11);
                    }
                } else {
                    final byte b1 = (combinations[i]);

                    byte b2 = 0;

                    if ((b1 & BIT_00) != 0) {
                        b2 |= BIT_01;
                    } else if ((b1 & BIT_01) != 0) {
                        b2 |= BIT_00;
                    }
                    if ((b1 & BIT_10) != 0) {
                        b2 |= BIT_11;
                    } else if ((b1 & BIT_11) != 0) {
                        b2 |= BIT_10;
                    }
                    combinations2[i] = b2;
                }
            }
        }
    }

    private void addRelation(final int mx0, final int my0) {
        final int indexX = Math.abs(mx0) - 1;
        final int indexY = Math.abs(my0) - 1;
        final int combinationIndexXY = (indexX * numVariables) + indexY;
        final int combinationIndexYX = (indexY * numVariables) + indexX;

        if (mx0 > 0) {
            if (my0 > 0) {
                combinations[combinationIndexXY] |= BIT_11;
                combinations[combinationIndexYX] |= BIT_00;
            } else {
                combinations[combinationIndexXY] |= BIT_10;
                combinations[combinationIndexYX] |= BIT_10;
            }
        } else {
            if (my0 > 0) {
                combinations[combinationIndexXY] |= BIT_01;
                combinations[combinationIndexYX] |= BIT_01;
            } else {
                combinations[combinationIndexXY] |= BIT_00;
                combinations[combinationIndexYX] |= BIT_11;
            }
        }
    }

    private int count() {
        int partCount = 0;
        for (int i = 0; i < combinations2.length; i++) {
            final int c = (combinations2[i]);
            partCount += c & 1;
            partCount += (c >> 1) & 1;
            partCount += (c >> 2) & 1;
            partCount += (c >> 3) & 1;
        }
        return partCount;
    }

    private void fix(final boolean[] featuresUsed, int a, int b) {
        featuresUsed[a] = true;
        featuresUsed[b] = true;
    }

    private int[] getCombinationOrder(int selectedA, int selectedB, byte curCombo) {
        final int[] combinationOrder = new int[4];
        curCombo = (byte) ~curCombo;
        if (selectedA >= 0) {
            if (selectedB >= 0) {
                combinationOrder[0] = (curCombo & BIT_00);
                combinationOrder[1] = (curCombo & BIT_10);
                combinationOrder[2] = (curCombo & BIT_01);
                combinationOrder[3] = (curCombo & BIT_11);
            } else {
                combinationOrder[0] = (curCombo & BIT_01);
                combinationOrder[1] = (curCombo & BIT_11);
                combinationOrder[2] = (curCombo & BIT_00);
                combinationOrder[3] = (curCombo & BIT_10);
            }
        } else {
            if (selectedB >= 0) {
                combinationOrder[0] = (curCombo & BIT_10);
                combinationOrder[1] = (curCombo & BIT_00);
                combinationOrder[2] = (curCombo & BIT_11);
                combinationOrder[3] = (curCombo & BIT_01);
            } else {
                combinationOrder[0] = (curCombo & BIT_11);
                combinationOrder[1] = (curCombo & BIT_01);
                combinationOrder[2] = (curCombo & BIT_10);
                combinationOrder[3] = (curCombo & BIT_00);
            }
        }
        return combinationOrder;
    }

    private boolean handleNewConfig(LiteralList solution, final boolean[] featuresUsedOrg) {
        if (solution == null) {
            return true;
        }
        addCombinationsFromModel(solution.getLiterals());
        final int totalCount = count();

        for (int i = 0; i < featureIndexArray.length; i++) {
            final FeatureIndex featureIndex = featureIndexArray[i];
            final int a = featureIndex.getIndex();
            int selected = 0;
            int coveredCombinations = 0;
            for (int j = a * numVariables, end = j + numVariables; j < end; j++) {
                final byte c = (combinations2[j]);
                if ((c & BIT_00) != 0) {
                    selected--;
                    coveredCombinations++;
                }
                if ((c & BIT_01) != 0) {
                    selected--;
                    coveredCombinations++;
                }
                if ((c & BIT_10) != 0) {
                    selected++;
                    coveredCombinations++;
                }
                if ((c & BIT_11) != 0) {
                    selected++;
                    coveredCombinations++;
                }
            }
            featureIndex.setCoveredCombinations(coveredCombinations);
            featureIndex.setSelected(selected);
        }

        try {
            solver.getFormula().push(solution.negate());
        } catch (final RuntimeContradictionException e) {
            return true;
        }

        if (combinationCount <= totalCount) {
            return true;
        }
        return false;
    }

    private boolean testCombination(int[] varStatus, boolean[] featuresUsed, int sa, int sb) {
        final int a = Math.abs(sa) - 1;
        final int b = Math.abs(sb) - 1;

        final int sigA = (int) Math.signum(sa);
        final int sigB = (int) Math.signum(sb);

        if ((varStatus[0] != -sigA) && (varStatus[1] != -sigB)) {
            if ((varStatus[0] == sigA) && (varStatus[1] == sigB)) {
                fix(featuresUsed, a, b);
                return true;
            }

            if (varStatus[1] == 0) {
                solver.getAssumptions().push(sb);
                switch (solver.hasSolution()) {
                    case FALSE:
                        solver.getAssumptions().replaceLast(-sb);
                        varStatus[1] = -sigB;
                        featuresUsed[b] = true;
                        return false;
                    case TIMEOUT:
                        throw new RuntimeException();
                    case TRUE:
                        break;
                    default:
                        throw new RuntimeException();
                }
            }

            if (varStatus[0] == 0) {
                solver.getAssumptions().push(sa);
            }

            switch (solver.hasSolution()) {
                case FALSE:
                    if (varStatus[1] != 0) {
                        solver.getAssumptions().replaceLast(-sa);
                        varStatus[0] = -sigA;
                        featuresUsed[a] = true;
                        return true;
                    } else {
                        if (varStatus[0] == 0) {
                            solver.getAssumptions().pop();
                        }
                        solver.getAssumptions().pop();
                    }
                    break;
                case TIMEOUT:
                    throw new RuntimeException();
                case TRUE:
                    fix(featuresUsed, a, b);
                    return true;
                default:
                    throw new RuntimeException();
            }
        }
        return false;
    }

    @Override
    protected void init(InternalMonitor monitor) {
        numVariables = solver.getCnf().getVariableMap().getVariableCount();
        solver.rememberSolutionHistory(Math.min(numVariables, AbstractSat4JSolver.MAX_SOLUTION_BUFFER));

        final MIGBuilder migBuilder = new RegularMIGBuilder();
        migBuilder.setCheckRedundancy(true);
        migBuilder.setDetectStrong(true);
        final MIG mig = Executor.run(migBuilder, solver.getCnf()).get();

        combinations = new byte[numVariables * numVariables];
        combinations2 = new byte[numVariables * numVariables];
        core = new byte[numVariables];
        for (final Vertex vertex : mig.getVertices()) {
            if (vertex.isCore()) {
                core[Math.abs(vertex.getVar()) - 1] = (byte) (vertex.getVar() < 0 ? -1 : 1);
                solver.getAssumptions().push(vertex.getVar());
            } else {
                for (final Vertex strong : vertex.getStrongEdges()) {
                    if (strong.isNormal()) {
                        addRelation(vertex.getVar(), strong.getVar());
                    }
                }
            }
        }

        numberOfFixedFeatures = solver.getAssumptions().size();
        featuresUsedOrg = new boolean[numVariables];
        for (int i = 0; i < numberOfFixedFeatures; i++) {
            featuresUsedOrg[Math.abs(solver.getAssumptions().peek(i)) - 1] = true;
        }

        featureIndexArray = new FeatureIndex[numVariables - numberOfFixedFeatures];
        {
            int index = 0;
            for (int i = 0; i < numVariables; i++) {
                if (!featuresUsedOrg[i]) {
                    featureIndexArray[index++] = new FeatureIndex(i);
                }
            }
        }
        addInvalidCombinations();
    }

    @Override
    public LiteralList get() {
        switch (mode) {
            case 0: {
                return findFirstSolution(SStrategy.positive());
            }
            case 1: {
                return findFirstSolution(SStrategy.negative());
            }
            case 2: {
                solver.setSelectionStrategy(SStrategy.random(getRandom()));
                final int[] varStatus = new int[2];
                final boolean[] featuresUsed = Arrays.copyOf(featuresUsedOrg, featuresUsedOrg.length);

                int priority = 0;
                for (final FeatureIndex featureIndex : featureIndexArray) {
                    featureIndex.setPriority(priority++);
                }
                Arrays.sort(featureIndexArray);

                for (int x = 1, end = featureIndexArray.length; x < end; x++) {
                    final FeatureIndex featureIndexA = featureIndexArray[x];
                    final int a = featureIndexA.getIndex();
                    if (featuresUsed[a]) {
                        continue;
                    }
                    bLoop:
                    for (int y = 0; y < x; y++) {
                        final FeatureIndex featureIndexB = featureIndexArray[y];
                        final int b = featureIndexB.getIndex();
                        final int index = (a * numVariables) + b;
                        final byte curCombo = (combinations2[index]);
                        if ((curCombo == 15) || featuresUsed[b]) {
                            continue;
                        }

                        varStatus[0] = 0;
                        varStatus[1] = 0;

                        final int[] combinationOrder =
                                getCombinationOrder(featureIndexA.getSelected(), featureIndexB.getSelected(), curCombo);
                        comboLoop:
                        for (int i = 0; i < combinationOrder.length; i++) {
                            final boolean result;
                            switch (combinationOrder[i]) {
                                case BIT_00:
                                    result = testCombination(varStatus, featuresUsed, -(a + 1), -(b + 1));
                                    break;
                                case BIT_01:
                                    result = testCombination(varStatus, featuresUsed, -(a + 1), (b + 1));
                                    break;
                                case BIT_10:
                                    result = testCombination(varStatus, featuresUsed, (a + 1), -(b + 1));
                                    break;
                                case BIT_11:
                                    result = testCombination(varStatus, featuresUsed, (a + 1), (b + 1));
                                    break;
                                default:
                                    continue comboLoop;
                            }
                            if (result) {
                                break bLoop;
                            }
                        }
                    }
                }

                final LiteralList solution = solver.findSolution();
                if (handleNewConfig(solution, featuresUsedOrg)) {
                    mode = -1;
                } else {
                    solver.shuffleOrder(getRandom());
                }
                solver.getAssumptions().clear(numberOfFixedFeatures);
                return solution;
            }
            default:
                return null;
        }
    }

    private LiteralList findFirstSolution(final SStrategy strategy) {
        solver.setSelectionStrategy(strategy);
        final LiteralList allYesSolution = solver.findSolution();
        if (handleNewConfig(allYesSolution, featuresUsedOrg)) {
            mode = -1;
        } else {
            mode++;
        }
        return allYesSolution;
    }

    @Override
    public Random getRandom() {
        return random;
    }

    @Override
    public void setRandom(Random random) {
        this.random = random;
    }
}
