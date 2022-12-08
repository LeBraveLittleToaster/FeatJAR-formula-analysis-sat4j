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

import de.featjar.clauses.ClauseList;
import de.featjar.clauses.LiteralList;
import de.featjar.util.data.Pair;
import java.util.ArrayList;
import java.util.List;

/**
 * Calculates statistics regarding t-wise feature coverage of a set of
 * solutions.
 *
 * @author Sebastian Krieter
 */
public class TWiseStatisticGenerator {

    public enum ConfigurationScore {
        /**
         * No scoring.
         */
        NONE,
        /**
         * Number of conditions only covered by one configurations.
         */
        SIMPLE,
        /**
         * For each configuration: Sum of every conditions covered divided by number of
         * configurations that cover this condition.
         */
        COMPLETE
    }

    private final TWiseConfigurationUtil util;

    public TWiseStatisticGenerator(TWiseConfigurationUtil util) {
        this.util = util;
    }

    public List<CoverageStatistic> getCoverage(
            List<List<? extends LiteralList>> samples,
            List<List<PresenceCondition>> groupedPresenceConditions,
            int t,
            ConfigurationScore configurationScoreType,
            boolean identifyValidCombinations) {
        final int sampleListSize = samples.size();

        final TWiseCombiner combiner =
                new TWiseCombiner(util.getCnf().getVariableMap().getVariableCount());
        final ClauseList combinedCondition = new ClauseList();
        final PresenceCondition[] clauseListArray = new PresenceCondition[t];
        final ArrayList<ArrayList<List<Pair<Integer, LiteralList>>>> configurationSubLists =
                new ArrayList<>(sampleListSize);

        final List<CoverageStatistic> statisticList = new ArrayList<>(sampleListSize);
        for (final List<? extends LiteralList> sample : samples) {
            final CoverageStatistic statistic = new CoverageStatistic();
            if (configurationScoreType != ConfigurationScore.NONE) {
                statistic.initScores(sample.size());
            }
            statisticList.add(statistic);

            final ArrayList<List<Pair<Integer, LiteralList>>> configurationSubList = new ArrayList<>(t);
            configurationSubLists.add(configurationSubList);

            for (int i = 0; i <= t; i++) {
                configurationSubList.add(new ArrayList<Pair<Integer, LiteralList>>());
            }
            final List<Pair<Integer, LiteralList>> list = configurationSubList.get(0);
            int confIndex = 0;
            for (final LiteralList configuration : sample) {
                list.add(new Pair<>(confIndex++, configuration));
            }
        }

        for (List<PresenceCondition> expressions : groupedPresenceConditions) {
            if (expressions.size() < t) {
                if (expressions.size() == 0) {
                    continue;
                }
                final ArrayList<PresenceCondition> paddedExpressions = new ArrayList<>(t);
                paddedExpressions.addAll(expressions);
                for (int i = expressions.size(); i < t; i++) {
                    paddedExpressions.add(expressions.get(0));
                }
                expressions = paddedExpressions;
            }
            final int n = expressions.size();
            if (n == 0) {
                continue;
            }
            final int t2 = (n < t) ? n : t;
            final int[] c = new int[t2 + 1];
            c[0] = -1;
            for (int i = 1; i <= t2; i++) {
                c[i] = n - (t2 - i);
            }
            boolean first = true;

            combinationLoop:
            while (true) {
                int i = t2;
                for (; i > 0; i--) {
                    final int ci = ++c[i];
                    if (ci < ((n - t2) + i)) {
                        break;
                    }
                }

                if (i == 0) {
                    if (first) {
                        first = false;
                    } else {
                        break combinationLoop;
                    }
                }

                for (int j = i + 1; j <= t2; j++) {
                    c[j] = c[j - 1] + 1;
                }

                boolean valid = false;

                for (int sampleIndex = 0; sampleIndex < sampleListSize; sampleIndex++) {
                    final CoverageStatistic statistic = statisticList.get(sampleIndex);
                    final ArrayList<List<Pair<Integer, LiteralList>>> lists = configurationSubLists.get(sampleIndex);
                    final List<Pair<Integer, LiteralList>> curConfigurationList = lists.get(t2);

                    {
                        int j = i;
                        for (; j < t2; j++) {
                            if (j > 0) {
                                final List<Pair<Integer, LiteralList>> prevList = lists.get(j - 1);
                                final List<Pair<Integer, LiteralList>> curList = lists.get(j);
                                curList.clear();
                                final PresenceCondition presenceCondition = expressions.get(c[j]);
                                entryLoop:
                                for (final Pair<Integer, LiteralList> entry : prevList) {
                                    for (final LiteralList literals : presenceCondition) {
                                        if (entry.getValue().containsAll(literals)) {
                                            curList.add(entry);
                                            continue entryLoop;
                                        }
                                    }
                                }
                            }
                        }
                        final List<Pair<Integer, LiteralList>> prevList = lists.get(j - 1);
                        final List<Pair<Integer, LiteralList>> curList = lists.get(j);
                        curList.clear();
                        final PresenceCondition presenceCondition = expressions.get(c[j]);
                        entryLoop:
                        for (final Pair<Integer, LiteralList> entry : prevList) {
                            for (final LiteralList literals : presenceCondition) {
                                if (entry.getValue().containsAll(literals)) {
                                    curList.add(entry);
                                    if ((configurationScoreType != ConfigurationScore.COMPLETE)
                                            && (curList.size() > 1)) {
                                        break entryLoop;
                                    }
                                    continue entryLoop;
                                }
                            }
                        }
                    }

                    final int count = curConfigurationList.size();
                    if (count > 0) {
                        valid = true;
                        statistic.incNumberOfCoveredConditions();
                        switch (configurationScoreType) {
                            case NONE:
                                break;
                            case SIMPLE: {
                                final long value = count == 1 ? 1 : 0;
                                for (final Pair<Integer, LiteralList> entry : curConfigurationList) {
                                    statistic.addToScore(entry.getKey(), value);
                                }
                                break;
                            }
                            case COMPLETE: {
                                final double value = 1.0 / count;
                                for (final Pair<Integer, LiteralList> entry : curConfigurationList) {
                                    statistic.addToScore(entry.getKey(), value);
                                }
                                break;
                            }
                            default:
                                throw new IllegalStateException(configurationScoreType.toString());
                        }
                    }
                }

                if (identifyValidCombinations) {
                    for (int j = 1; j < c.length; j++) {
                        clauseListArray[j - 1] = expressions.get(c[j]);
                    }
                    combinedCondition.clear();
                    combiner.combineConditions(clauseListArray, combinedCondition);
                    valid = valid || util.isCombinationValid(combinedCondition);

                    if (valid) {
                        for (int sampleIndex = 0; sampleIndex < sampleListSize; sampleIndex++) {
                            final CoverageStatistic statistic = statisticList.get(sampleIndex);
                            statistic.incNumberOfValidConditions();
                            if (configurationSubLists.get(sampleIndex).get(t).size() == 0) {
                                statistic.incNumberOfUncoveredConditions();
                            }
                        }
                    } else {
                        for (final CoverageStatistic statistic : statisticList) {
                            statistic.incNumberOfInvalidConditions();
                        }
                    }
                } else {
                    for (int sampleIndex = 0; sampleIndex < sampleListSize; sampleIndex++) {
                        final CoverageStatistic statistic = statisticList.get(sampleIndex);
                        if (configurationSubLists.get(sampleIndex).get(t).size() == 0) {
                            statistic.incNumberOfUncoveredConditions();
                        }
                    }
                }
            }
        }

        if (configurationScoreType != ConfigurationScore.NONE) {
            for (int sampleIndex = 0; sampleIndex < sampleListSize; sampleIndex++) {
                final List<? extends LiteralList> sample = samples.get(sampleIndex);
                final CoverageStatistic statistic = statisticList.get(sampleIndex);
                int confIndex = 0;
                for (final LiteralList configuration : sample) {
                    int selectionCount = 0;
                    for (final int literal : configuration.getLiterals()) {
                        if (literal == 0) {
                            selectionCount++;
                        }
                    }
                    final double ratio = (double) selectionCount / configuration.size();
                    statistic.setScore(confIndex, statistic.getScore(confIndex) * (2 - Math.pow(ratio, t)));
                    confIndex++;
                }
            }
        }
        return statisticList;
    }

    public List<ValidityStatistic> getValidity(List<List<? extends LiteralList>> samples) {
        final List<ValidityStatistic> statisticList = new ArrayList<>(samples.size());
        for (final List<? extends LiteralList> sample : samples) {
            final ValidityStatistic statistic = new ValidityStatistic(sample.size());

            int configurationIndex = 0;
            configLoop:
            for (final LiteralList configuration : sample) {
                for (final LiteralList clause : util.getCnf().getClauses()) {
                    if (!configuration.hasDuplicates(clause)) {
                        statistic.setConfigValidity(configurationIndex++, false);
                        continue configLoop;
                    }
                }
                statistic.setConfigValidity(configurationIndex++, true);
            }
            statisticList.add(statistic);
        }
        return statisticList;
    }
}
