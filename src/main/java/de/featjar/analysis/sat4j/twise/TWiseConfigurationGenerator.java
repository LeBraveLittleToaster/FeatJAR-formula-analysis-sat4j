/*
 * Copyright (C) 2023 Sebastian Krieter
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
package de.featjar.analysis.sat4j.twise;

import de.featjar.analysis.mig.solver.MIG;
import de.featjar.analysis.sat4j.AbstractConfigurationGenerator;
import de.featjar.analysis.sat4j.solver.SStrategy;
import de.featjar.clauses.CNF;
import de.featjar.clauses.LiteralList;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.util.data.Identifier;
import de.featjar.util.job.InternalMonitor;
import de.featjar.util.logging.Logger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Random;

/**
 * YASA sampling algorithm. Generates configurations for a given propositional
 * formula such that t-wise feature coverage is achieved.
 *
 * @author Sebastian Krieter
 */
public class TWiseConfigurationGenerator extends AbstractConfigurationGenerator {

    public static final Identifier<SolutionList> identifier = new Identifier<>();

    @Override
    public Identifier<SolutionList> getIdentifier() {
        return identifier;
    }

    enum Deduce {
        DP,
        AC,
        NONE
    }

    enum Order {
        RANDOM,
        SORTED
    }

    enum Phase {
        MULTI,
        SINGLE
    }

    /**
     * Converts a set of single literals into a grouped expression list.
     *
     * @param literalSet the literal set
     * @return a grouped expression list (can be used as an input for the
     *         configuration generator).
     */
    public static List<List<List<LiteralList>>> convertLiterals(LiteralList literalSet) {
        return TWiseCombiner.convertGroupedLiterals(Arrays.asList(literalSet));
    }

    /**
     * Converts a grouped set of single literals into a grouped expression list.
     *
     * @param groupedLiterals the grouped literal sets
     * @return a grouped expression list (can be used as an input for the
     *         configuration generator).
     */
    public static List<List<List<LiteralList>>> convertGroupedLiterals(List<LiteralList> groupedLiterals) {
        return TWiseCombiner.convertGroupedLiterals(groupedLiterals);
    }

    /**
     * Converts an expression list into a grouped expression set with a single
     * group.
     *
     * @param expressions the expression list
     * @return a grouped expression list (can be used as an input for the
     *         configuration generator).
     */
    public static List<List<List<LiteralList>>> convertExpressions(List<List<LiteralList>> expressions) {
        return TWiseCombiner.convertExpressions(expressions);
    }

    public static boolean VERBOSE = false;

    public static final int DEFAULT_ITERATIONS = 5;
    public static final int DEFAULT_RANDOM_SAMPLE_SIZE = 100;
    public static final int DEFAULT_LOG_FREQUENCY = 60_000;

    // TODO Variation Point: Iterations of removing low-contributing Configurations
    private int iterations = DEFAULT_ITERATIONS;
    private int randomSampleSize = DEFAULT_RANDOM_SAMPLE_SIZE;
    private int logFrequency = DEFAULT_LOG_FREQUENCY;
    private boolean useMig = true;
    private MIG mig;
    private Deduce createConfigurationDeduce = Deduce.DP;
    private Deduce extendConfigurationDeduce = Deduce.NONE;

    protected TWiseConfigurationUtil util;
    protected TWiseCombiner combiner;
    protected Random random = new Random(0);

    protected int t;
    protected List<List<List<LiteralList>>> nodes;
    protected PresenceConditionManager presenceConditionManager;

    protected long numberOfCombinations, count, coveredCount, invalidCount;
    protected int phaseCount;

    private List<TWiseConfiguration> curResult = null;
    private ArrayList<TWiseConfiguration> bestResult = null;

    private int maxSampleSize = Integer.MAX_VALUE;

    public int getMaxSampleSize() {
        return maxSampleSize;
    }

    public void setMaxSampleSize(int maxSampleSize) {
        this.maxSampleSize = maxSampleSize;
    }

    public int getT() {
        return t;
    }

    public void setT(int t) {
        this.t = t;
    }

    public List<List<List<LiteralList>>> getNodes() {
        return nodes;
    }

    public void setNodes(List<List<List<LiteralList>>> nodes) {
        this.nodes = nodes;
    }

    @Override
    public Random getRandom() {
        return random;
    }

    @Override
    public void setRandom(Random random) {
        this.random = random;
    }

    @Override
    protected void init(InternalMonitor monitor) {
        final CNF cnf = solver.getCnf();
        solver.rememberSolutionHistory(10);
        solver.setSelectionStrategy(SStrategy.random(getRandom()));

        if (nodes == null) {
            nodes = convertLiterals(LiteralList.getLiterals(cnf));
        }
        if (cnf.getClauses().isEmpty()) {
            util = new TWiseConfigurationUtil(cnf, null);
        } else {
            util = new TWiseConfigurationUtil(cnf, solver);
        }
        util.setMaxSampleSize(maxSampleSize);
        util.setRandom(getRandom());
        util.setCreateConfigurationDeduce(createConfigurationDeduce);
        util.setExtendConfigurationDeduce(extendConfigurationDeduce);

        if (!cnf.getClauses().isEmpty()) {
            util.computeRandomSample(randomSampleSize);
            if (useMig) {
                if (mig != null) {
                    util.setMIG(mig);
                } else {
                    util.computeMIG(false, false);
                }
            }
        }

        // TODO Variation Point: Sorting Nodes
        presenceConditionManager = new PresenceConditionManager(
                util.getDeadCoreFeatures(), util.getCnf().getVariableMap().getVariableCount(), nodes);
        // TODO Variation Point: Building Combinations
        combiner = new TWiseCombiner(cnf.getVariableMap().getVariableCount());

        phaseCount = 0;

        for (int i = 0; i < iterations; i++) {
            trimConfigurations();
            buildCombinations(monitor);
        }
        Collections.reverse(bestResult);
    }

    @Override
    public LiteralList get() {
        return bestResult.isEmpty()
                ? null
                : bestResult.remove(bestResult.size() - 1).getCompleteSolution();
    }

    private void trimConfigurations() {
        if ((curResult != null) && !curResult.isEmpty()) {
            final CoverageStatistic statistic = new TWiseStatisticFastGenerator()
                    .getCoverage(curResult, presenceConditionManager.getGroupedPresenceConditions(), t);

            final double[] normConfigValues = statistic.getConfigScores();
            double mean = 0;
            for (final double d : normConfigValues) {
                mean += d;
            }
            mean /= normConfigValues.length;

            final double reference = mean;

            int index = 0;
            index = removeSolutions(normConfigValues, reference, index, util.getIncompleteSolutionList());
            index = removeSolutions(normConfigValues, reference, index, util.getCompleteSolutionList());
        }
    }

    private int removeSolutions(
            double[] values, final double reference, int index, List<TWiseConfiguration> solutionList) {
        for (final Iterator<TWiseConfiguration> iterator = solutionList.iterator(); iterator.hasNext(); ) {
            iterator.next();
            if (values[index++] < reference) {
                iterator.remove();
            }
        }
        return index;
    }

    private void buildCombinations(InternalMonitor monitor) {
        // TODO Variation Point: Cover Strategies
        final List<? extends ICoverStrategy> phaseList = Arrays.asList( //
                new CoverAll(util) //
                );

        // TODO Variation Point: Combination order
        final ICombinationSupplier<List<LiteralList>> it;
        presenceConditionManager.shuffleSort(getRandom());
        final List<List<List<LiteralList>>> groupedPresenceConditions =
                presenceConditionManager.getGroupedPresenceConditions();
        if (groupedPresenceConditions.size() == 1) {
            it = new SingleIterator(
                    t, util.getCnf().getVariableMap().getVariableCount(), groupedPresenceConditions.get(0));
        } else {
            it = new MergeIterator(t, util.getCnf().getVariableMap().getVariableCount(), groupedPresenceConditions);
        }
        numberOfCombinations = it.size();
        monitor.setTotalWork(numberOfCombinations);

        coveredCount = 0;
        invalidCount = 0;

        final List<List<LiteralList>> combinationListUncovered = new ArrayList<>();
        count = coveredCount;
        phaseCount++;
        ICoverStrategy phase = phaseList.get(0);
        while (true) {
            monitor.step();
            final List<LiteralList> combinedCondition = it.get();
            if (combinedCondition == null) {
                break;
            }
            if (combinedCondition.isEmpty()) {
                invalidCount++;
            } else {
                final ICoverStrategy.CombinationStatus covered = phase.cover(combinedCondition);
                switch (covered) {
                    case NOT_COVERED:
                        combinationListUncovered.add(combinedCondition);
                        break;
                    case COVERED:
                        coveredCount++;
                        combinedCondition.clear();
                        break;
                    case INVALID:
                        invalidCount++;
                        combinedCondition.clear();
                        break;
                    default:
                        combinedCondition.clear();
                        break;
                }
            }
            count++;
        }

        int coveredIndex = -1;
        for (int j = 1; j < phaseList.size(); j++) {
            phaseCount++;
            phase = phaseList.get(j);
            count = coveredCount + invalidCount;
            for (int i = coveredIndex + 1; i < combinationListUncovered.size(); i++) {
                final List<LiteralList> combination = combinationListUncovered.get(i);
                final ICoverStrategy.CombinationStatus covered = phase.cover(combination);
                switch (covered) {
                    case COVERED:
                        Collections.swap(combinationListUncovered, i, ++coveredIndex);
                        coveredCount++;
                        break;
                    case NOT_COVERED:
                        break;
                    case INVALID:
                        Collections.swap(combinationListUncovered, i, ++coveredIndex);
                        invalidCount++;
                        break;
                    default:
                        break;
                }
                count++;
            }
        }

        curResult = util.getResultList();
        if ((bestResult == null) || (bestResult.size() > curResult.size())) {
            bestResult = new ArrayList<>(curResult.size());
            curResult.stream().map(TWiseConfiguration::clone).forEach(bestResult::add);
        }
    }

    public boolean printStatus() {
        if (VERBOSE) {
            final long uncoveredCount = (numberOfCombinations - coveredCount) - invalidCount;
            final double phaseProgress =
                    ((int) Math.floor((1 - (((double) count) / numberOfCombinations)) * 1000)) / 10.0;
            final double coverProgress =
                    ((int) Math.floor(((((double) coveredCount) / numberOfCombinations)) * 1000)) / 10.0;
            final double uncoverProgress =
                    ((int) Math.floor(((((double) uncoveredCount) / numberOfCombinations)) * 1000)) / 10.0;
            final double invalidProgress =
                    ((int) Math.floor(((((double) invalidCount) / numberOfCombinations)) * 1000)) / 10.0;
            final StringBuilder sb = new StringBuilder();

            sb.append(phaseCount);
            sb.append(" - ");
            sb.append(phaseProgress);
            sb.append(" (");
            sb.append(count);

            sb.append(") -- Configurations: ");
            sb.append(util.getIncompleteSolutionList().size()
                    + util.getCompleteSolutionList().size());
            sb.append(" (");
            sb.append(util.getIncompleteSolutionList().size());
            sb.append(" | ");
            sb.append(util.getCompleteSolutionList().size());

            sb.append(") -- Covered: ");
            sb.append(coverProgress);
            sb.append(" (");
            sb.append(coveredCount);
            sb.append(")");

            sb.append(" -- Uncovered: ");
            sb.append(uncoverProgress);
            sb.append(" (");
            sb.append(uncoveredCount);
            sb.append(")");

            sb.append(" -- Invalid: ");
            sb.append(invalidProgress);
            sb.append(" (");
            sb.append(invalidCount);
            sb.append(")");
            Logger.logProgress(sb.toString());
        }
        return true;
    }

    public TWiseConfigurationUtil getUtil() {
        return util;
    }

    public int getIterations() {
        return iterations;
    }

    public void setIterations(int iterations) {
        this.iterations = iterations;
    }

    public int getRandomSampleSize() {
        return randomSampleSize;
    }

    public void setRandomSampleSize(int randomSampleSize) {
        this.randomSampleSize = randomSampleSize;
    }

    public boolean isUseMig() {
        return useMig;
    }

    public void setUseMig(boolean useMig) {
        this.useMig = useMig;
    }

    public void setMIG(MIG mig) {
        this.mig = mig;
    }

    public MIG getMig() {
        return mig;
    }

    public void setMig(MIG mig) {
        this.mig = mig;
    }

    public int getLogFrequency() {
        return logFrequency;
    }

    public void setLogFrequency(int logFrequency) {
        this.logFrequency = logFrequency;
    }

    public Deduce getCreateConfigurationDeduce() {
        return createConfigurationDeduce;
    }

    public void setCreateConfigurationDeduce(Deduce createConfigurationDeduce) {
        this.createConfigurationDeduce = createConfigurationDeduce;
    }

    public Deduce getExtendConfigurationDeduce() {
        return extendConfigurationDeduce;
    }

    public void setExtendConfigurationDeduce(Deduce extendConfigurationDeduce) {
        this.extendConfigurationDeduce = extendConfigurationDeduce;
    }
}
