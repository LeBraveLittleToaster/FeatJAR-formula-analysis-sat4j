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
public class TWiseStatisticFastGenerator {

    public CoverageStatistic getCoverage(
            List<? extends LiteralList> sample, List<List<PresenceCondition>> groupedPresenceConditions, int t) {
        final CoverageStatistic statistic = new CoverageStatistic();
        statistic.initScores(sample.size());

        final ArrayList<List<Pair<Integer, LiteralList>>> lists = new ArrayList<>(t);
        {
            for (int i = 0; i < t; i++) {
                lists.add(new ArrayList<Pair<Integer, LiteralList>>(sample.size()));
            }
            final List<Pair<Integer, LiteralList>> list = lists.get(0);
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
            final int[] c = new int[t + 1];
            c[0] = -1;
            for (int i = 1; i <= t; i++) {
                c[i] = n - (t - i);
            }
            boolean first = true;

            combinationLoop:
            while (true) {
                int i = t;
                for (; i > 0; i--) {
                    final int ci = ++c[i];
                    if (ci < ((n - t) + i)) {
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

                for (int j = i + 1; j <= t; j++) {
                    c[j] = c[j - 1] + 1;
                }

                for (int j = i; j < t; j++) {
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

                Pair<Integer, LiteralList> curEntry = null;
                final PresenceCondition presenceCondition = expressions.get(c[t]);
                entryLoop:
                for (final Pair<Integer, LiteralList> entry : lists.get(t - 1)) {
                    for (final LiteralList literals : presenceCondition) {
                        if (entry.getValue().containsAll(literals)) {
                            if (curEntry == null) {
                                statistic.incNumberOfCoveredConditions();
                                curEntry = entry;
                                continue entryLoop;
                            } else {
                                continue combinationLoop;
                            }
                        }
                    }
                }

                if (curEntry != null) {
                    statistic.addToScore(curEntry.getKey(), 1);
                } else {
                    statistic.incNumberOfUncoveredConditions();
                }
            }
        }
        int confIndex = 0;
        for (final LiteralList configuration : sample) {
            int count = 0;
            for (final int literal : configuration.getLiterals()) {
                if (literal == 0) {
                    count++;
                }
            }
            final double d = (double) count / configuration.size();
            final double factor = (2 - (d * d));
            statistic.setScore(confIndex, statistic.getScore(confIndex) * factor);
            confIndex++;
        }
        return statistic;
    }
}
