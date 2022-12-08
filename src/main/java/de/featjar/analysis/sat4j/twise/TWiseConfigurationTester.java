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
package de.featjar.analysis.sat4j.twise;

import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.analysis.sat4j.twise.TWiseStatisticGenerator.ConfigurationScore;
import de.featjar.clauses.CNF;
import de.featjar.clauses.ClauseList;
import de.featjar.clauses.LiteralList;
import de.featjar.clauses.solutions.combinations.CombinationIterator;
import de.featjar.clauses.solutions.combinations.LexicographicIterator;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Tests whether a set of configurations achieves t-wise feature coverage.
 *
 * @author Sebastian Krieter
 */
public class TWiseConfigurationTester {

    private final TWiseConfigurationUtil util;

    private List<LiteralList> sample;
    private PresenceConditionManager presenceConditionManager;
    private int t;

    public TWiseConfigurationTester(CNF cnf) {
        if (!cnf.getClauses().isEmpty()) {
            util = new TWiseConfigurationUtil(cnf, new Sat4JSolver(cnf));
        } else {
            util = new TWiseConfigurationUtil(cnf, null);
        }

        getUtil().computeRandomSample(TWiseConfigurationGenerator.DEFAULT_RANDOM_SAMPLE_SIZE);
        if (!cnf.getClauses().isEmpty()) {
            getUtil().computeMIG(false, false);
        }
    }

    public void setNodes(List<List<ClauseList>> expressions) {
        presenceConditionManager = new PresenceConditionManager(getUtil(), expressions);
    }

    public void setNodes(PresenceConditionManager expressions) {
        presenceConditionManager = expressions;
    }

    public void setT(int t) {
        this.t = t;
    }

    public void setSample(List<LiteralList> sample) {
        this.sample = sample;
    }

    public List<LiteralList> getSample() {
        return sample;
    }

    /**
     * Creates statistic values about covered combinations.<br>
     * To get a percentage value of covered combinations use:<br>
     *
     * <pre>
     * {
     * 	&#64;code
     * 	CoverageStatistic coverage = getCoverage();
     * 	double covered = (double) coverage.getNumberOfCoveredConditions() / coverage.getNumberOfValidConditions();
     * }
     * </pre>
     *
     *
     * @return a statistic object containing multiple values:<br>
     *         <ul>
     *         <li>number of valid combinations
     *         <li>number of invalid combinations
     *         <li>number of covered combinations
     *         <li>number of uncovered combinations
     *         <li>value of each configuration
     *         </ul>
     */
    public CoverageStatistic getCoverage() {
        final List<CoverageStatistic> coveragePerSample = new TWiseStatisticGenerator(util)
                .getCoverage(
                        Arrays.asList(sample),
                        presenceConditionManager.getGroupedPresenceConditions(),
                        t,
                        ConfigurationScore.NONE,
                        true);
        return coveragePerSample.get(0);
    }

    public ValidityStatistic getValidity() {
        final List<ValidityStatistic> validityPerSample =
                new TWiseStatisticGenerator(util).getValidity(Arrays.asList(sample));
        return validityPerSample.get(0);
    }

    public boolean hasUncoveredConditions() {
        final List<ClauseList> uncoveredConditions = getUncoveredConditions(true);
        return !uncoveredConditions.isEmpty();
    }

    public ClauseList getFirstUncoveredCondition() {
        final List<ClauseList> uncoveredConditions = getUncoveredConditions(true);
        return uncoveredConditions.isEmpty() ? null : uncoveredConditions.get(0);
    }

    public List<ClauseList> getUncoveredConditions() {
        return getUncoveredConditions(false);
    }

    private List<ClauseList> getUncoveredConditions(boolean cancelAfterFirst) {
        final ArrayList<ClauseList> uncoveredConditions = new ArrayList<>();
        final TWiseCombiner combiner =
                new TWiseCombiner(getUtil().getCnf().getVariableMap().getVariableCount());
        ClauseList combinedCondition = new ClauseList();
        final PresenceCondition[] clauseListArray = new PresenceCondition[t];

        groupLoop:
        for (final List<PresenceCondition> expressions : presenceConditionManager.getGroupedPresenceConditions()) {
            for (final CombinationIterator iterator = new LexicographicIterator(t, expressions.size());
                    iterator.hasNext(); ) {
                final int[] next = iterator.next();
                if (next == null) {
                    break;
                }
                CombinationIterator.select(expressions, next, clauseListArray);

                combinedCondition.clear();
                combiner.combineConditions(clauseListArray, combinedCondition);
                if (!TWiseConfigurationUtil.isCovered(combinedCondition, sample)
                        && getUtil().isCombinationValid(combinedCondition)) {
                    uncoveredConditions.add(combinedCondition);
                    combinedCondition = new ClauseList();
                    if (cancelAfterFirst) {
                        break groupLoop;
                    }
                }
            }
        }
        return uncoveredConditions;
    }

    public boolean hasInvalidSolutions() {
        final List<LiteralList> invalidSolutions = getInvalidSolutions(true);
        return !invalidSolutions.isEmpty();
    }

    public LiteralList getFirstInvalidSolution() {
        final List<LiteralList> invalidSolutions = getInvalidSolutions(true);
        return invalidSolutions.isEmpty() ? null : invalidSolutions.get(0);
    }

    public List<LiteralList> getInvalidSolutions() {
        return getInvalidSolutions(false);
    }

    private List<LiteralList> getInvalidSolutions(boolean cancelAfterFirst) {
        final ArrayList<LiteralList> invalidSolutions = new ArrayList<>();
        configLoop:
        for (final LiteralList solution : sample) {
            for (final LiteralList clause : getUtil().getCnf().getClauses()) {
                if (!solution.hasDuplicates(clause)) {
                    invalidSolutions.add(solution);
                    if (cancelAfterFirst) {
                        break configLoop;
                    }
                }
            }
        }
        return invalidSolutions;
    }

    public TWiseConfigurationUtil getUtil() {
        return util;
    }
}
