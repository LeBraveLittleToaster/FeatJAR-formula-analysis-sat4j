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
package de.featjar.configuration.list;

import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.analysis.sat4j.twise.CoverageStatistic;
import de.featjar.analysis.sat4j.twise.PresenceConditionManager;
import de.featjar.analysis.sat4j.twise.TWiseConfigurationGenerator;
import de.featjar.analysis.sat4j.twise.TWiseConfigurationUtil;
import de.featjar.analysis.sat4j.twise.TWiseConfigurationUtil.InvalidClausesList;
import de.featjar.analysis.sat4j.twise.TWiseStatisticGenerator;
import de.featjar.clauses.CNF;
import de.featjar.clauses.Clauses;
import de.featjar.clauses.LiteralList;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.clauses.solutions.metrics.SampleMetric;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Tests whether a set of configurations achieves t-wise feature coverage.
 *
 * @author Sebastian Krieter
 */
public class TWiseCoverageMetrics {

    public final class TWiseCoverageMetric implements SampleMetric {
        private final int t;
        private boolean firstUse = true;

        public TWiseCoverageMetric(int t) {
            this.t = t;
        }

        @Override
        public double get(SolutionList sample) {
            return get(sample.getSolutions());
        }

        public double get(List<LiteralList> sample) {
            final TWiseStatisticGenerator tWiseStatisticGenerator = new TWiseStatisticGenerator(util);
            if (firstUse) {
                firstUse = false;
            } else {
                util.setInvalidClausesList(InvalidClausesList.Use);
            }

            final CoverageStatistic statistic = tWiseStatisticGenerator
                    .getCoverage(
                            Arrays.asList(sample), //
                            presenceConditionManager.getGroupedPresenceConditions(), //
                            t, //
                            TWiseStatisticGenerator.ConfigurationScore.NONE, //
                            true)
                    .get(0);

            final long numberOfValidConditions = statistic.getNumberOfValidConditions();
            final long numberOfCoveredConditions = statistic.getNumberOfCoveredConditions();
            if (numberOfValidConditions == 0) {
                return 1;
            } else {
                return (double) numberOfCoveredConditions / numberOfValidConditions;
            }
        }

        @Override
        public String getName() {
            return "T" + t + "_" + name + "_" + "Coverage";
        }
    }

    private TWiseConfigurationUtil util;
    private PresenceConditionManager presenceConditionManager;
    private String name;
    private CNF cnf;
    private List<List<List<LiteralList>>> expressions;

    public void setCNF(CNF cnf) {
        this.cnf = cnf;
    }

    public void setExpressions(List<List<List<LiteralList>>> expressions) {
        this.expressions = expressions;
    }

    public void init() {
        if (!cnf.getClauses().isEmpty()) {
            util = new TWiseConfigurationUtil(cnf, new Sat4JSolver(cnf));
        } else {
            util = new TWiseConfigurationUtil(cnf, null);
        }
        util.setInvalidClausesList(InvalidClausesList.Create);
        util.computeRandomSample(1000);
        if (!cnf.getClauses().isEmpty()) {
            util.computeMIG(false, false);
        }
        if (expressions == null) {
            expressions = TWiseConfigurationGenerator.convertLiterals(Clauses.getLiterals(cnf.getVariableMap()));
        }
        presenceConditionManager = new PresenceConditionManager(
                util.getDeadCoreFeatures(), util.getCnf().getVariableMap().getVariableCount(), expressions);
    }

    public TWiseCoverageMetric getTWiseCoverageMetric(int t) {
        return new TWiseCoverageMetric(t);
    }

    public static List<TWiseCoverageMetric> getTWiseCoverageMetrics(
            CNF cnf, List<List<List<LiteralList>>> expressions, String name, int... tValues) {
        final TWiseCoverageMetrics metrics = new TWiseCoverageMetrics();
        metrics.setName(name);
        metrics.setExpressions(expressions);
        metrics.setCNF(cnf);
        if (cnf != null) {
            metrics.init();
        }
        final List<TWiseCoverageMetric> coverageMetrics = new ArrayList<>(tValues.length);
        for (final int t : tValues) {
            coverageMetrics.add(metrics.getTWiseCoverageMetric(t));
        }
        return coverageMetrics;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }
}
