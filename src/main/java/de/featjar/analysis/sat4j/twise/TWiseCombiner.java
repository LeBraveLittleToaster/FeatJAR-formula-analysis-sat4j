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

import de.featjar.clauses.LiteralList;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.TreeSet;
import org.sat4j.core.VecInt;

/**
 * Combines multiple presence conditions into one.
 *
 * @author Sebastian Krieter
 */
public class TWiseCombiner {

    /**
     * Converts a set of single literals into a grouped expression list.
     *
     * @param literalSet the literal set
     * @return a grouped expression list (can be used as an input for the
     *         configuration generator).
     */
    public static List<List<List<LiteralList>>> convertLiterals(LiteralList literalSet) {
        return convertGroupedLiterals(Arrays.asList(literalSet));
    }

    /**
     * Converts a grouped set of single literals into a grouped expression list.
     *
     * @param groupedLiterals the grouped literal sets
     * @return a grouped expression list (can be used as an input for the
     *         configuration generator).
     */
    public static List<List<List<LiteralList>>> convertGroupedLiterals(List<LiteralList> groupedLiterals) {
        final List<List<List<LiteralList>>> groupedExpressions = new ArrayList<>(groupedLiterals.size());
        for (final LiteralList literalSet : groupedLiterals) {
            final List<List<LiteralList>> arrayList = new ArrayList<>(literalSet.size());
            groupedExpressions.add(arrayList);
            for (final Integer literal : literalSet.getLiterals()) {
                final List<LiteralList> clauseList = new ArrayList<>(1);
                clauseList.add(new LiteralList(literal));
                arrayList.add(clauseList);
            }
        }
        return groupedExpressions;
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
        return Arrays.asList(expressions);
    }

    private final VecInt lits = new VecInt();
    private final int[] features;

    public TWiseCombiner(int numberOfVariables) {
        features = new int[numberOfVariables + 1];
    }

    public boolean combineConditions(List<LiteralList>[] conditionArray, List<LiteralList> combinedCondition) {
        return combineConditions(conditionArray, 0, combinedCondition);
    }

    private boolean combineConditions(List<LiteralList>[] conditionArray, int t, List<LiteralList> combinedCondition) {
        if (t == conditionArray.length) {
            final int[] combinedLiteralsArray = Arrays.copyOfRange(lits.toArray(), 0, lits.size());
            combinedCondition.add(new LiteralList(combinedLiteralsArray));
        } else {
            clauseLoop:
            for (final LiteralList clause : conditionArray[t]) {
                final int[] literals = clause.getLiterals();
                for (int i = 0; i < literals.length; i++) {
                    final int literal = literals[i];
                    final int var = Math.abs(literal);
                    final int x = features[var];
                    if ((x != 0) && ((literal ^ x) < 0)) {
                        for (i--; i >= 0; i--) {
                            final int undoLiteral = literals[i];
                            final int var2 = Math.abs(undoLiteral);
                            final int y = features[var2];
                            final int y2 = y - ((undoLiteral >>> 31) == 0 ? 1 : -1);
                            features[var2] = y2;
                            if (y2 == 0) {
                                lits.pop();
                            }
                        }
                        continue clauseLoop;
                    } else {
                        features[var] = x + ((literal >>> 31) == 0 ? 1 : -1);
                        if (x == 0) {
                            lits.push(literal);
                        }
                    }
                }
                if (!combineConditions(conditionArray, t + 1, combinedCondition)) {
                    return false;
                }
                for (int i = 0; i < literals.length; i++) {
                    final int literal = literals[i];
                    final int var = Math.abs(literal);
                    final int y = features[var];
                    final int y2 = y - ((literal >>> 31) == 0 ? 1 : -1);
                    features[var] = y2;
                    if (y2 == 0) {
                        lits.pop();
                    }
                }
            }
        }
        return true;
    }

    private boolean combineIteratively(List<LiteralList>[] conditionArray, List<LiteralList> combinedCondition) {
        final int[] clauseIndex = new int[conditionArray.length];
        clauseIndex[0] = -1;

        int i = 0;
        loop:
        while (i < clauseIndex.length) {
            for (i = 0; i < clauseIndex.length; i++) {
                final int cindex = clauseIndex[i];
                if (cindex == (conditionArray[i].size() - 1)) {
                    clauseIndex[i] = 0;
                } else {
                    clauseIndex[i] = cindex + 1;

                    final LiteralList literalSet = getCombinationLiterals(clauseIndex, conditionArray);
                    if (literalSet != null) {
                        combinedCondition.add(literalSet);
                        continue loop;
                    }
                }
            }
        }
        return true;
    }

    private LiteralList getCombinationLiterals(final int[] clauseIndex, final List<LiteralList>[] clauseListArray) {
        final TreeSet<Integer> newLiteralSet = new TreeSet<>();
        for (int j = 0; j < clauseIndex.length; j++) {
            for (final int literal : clauseListArray[j].get(clauseIndex[j]).getLiterals()) {
                if (newLiteralSet.contains(-literal)) {
                    return null;
                } else {
                    newLiteralSet.add(literal);
                }
            }
        }

        final int[] combinationLiterals = new int[newLiteralSet.size()];
        int j = 0;
        for (final Integer literal : newLiteralSet) {
            combinationLiterals[j++] = literal;
        }
        final LiteralList literalSet = new LiteralList(combinationLiterals);
        return literalSet;
    }

    private boolean combineConditions3(List<LiteralList>[] conditionArray, int t, List<LiteralList> combinedCondition) {
        if (t == conditionArray.length) {
            final int[] combinedLiteralsArray = Arrays.copyOfRange(lits.toArray(), 0, lits.size());
            combinedCondition.add(new LiteralList(combinedLiteralsArray));
        } else {
            clauseLoop:
            for (final LiteralList clause : conditionArray[t]) {
                final int[] literals = clause.getLiterals();
                for (int i = 0; i < literals.length; i++) {
                    final int literal = literals[i];
                    final int var = Math.abs(literal);
                    final int x = features[var];
                    if ((x != 0) && ((literal ^ x) < 0)) {
                        for (i--; i >= 0; i--) {
                            final int undoLiteral = literals[i];
                            final int var2 = Math.abs(undoLiteral);
                            final int y = features[var2];
                            final int y2 = y - ((undoLiteral >>> 31) == 0 ? 1 : -1);
                            features[var2] = y2;
                            if (y2 == 0) {
                                lits.pop();
                            }
                        }
                        continue clauseLoop;
                    } else {
                        features[var] = x + ((literal >>> 31) == 0 ? 1 : -1);
                        if (x == 0) {
                            lits.push(literal);
                        }
                    }
                }
                if (!combineConditions(conditionArray, t + 1, combinedCondition)) {
                    return false;
                }
                for (int i = 0; i < literals.length; i++) {
                    final int literal = literals[i];
                    final int var = Math.abs(literal);
                    final int y2 = features[var] - ((literal >>> 31) == 0 ? 1 : -1);
                    features[var] = y2;
                    if (y2 == 0) {
                        lits.pop();
                    }
                }
            }
        }
        return true;
    }

    private boolean combineConditions2(List<LiteralList>[] conditionArray, int t, List<LiteralList> combinedCondition) {
        if (t == conditionArray.length) {
            if (combinedCondition.size() >= 1) {
                return false;
            }
            final int[] combinedLiteralsArray = Arrays.copyOfRange(lits.toArray(), 0, lits.size());
            combinedCondition.add(new LiteralList(combinedLiteralsArray));
        } else {
            clauseLoop:
            for (final LiteralList clause : conditionArray[t]) {
                final int[] literals = clause.getLiterals();
                for (int i = 0; i < literals.length; i++) {
                    final int literal = literals[i];
                    final int var = Math.abs(literal);
                    final int x = features[var];
                    if ((x != 0) && ((literal ^ x) < 0)) {
                        for (i--; i >= 0; i--) {
                            final int undoLiteral = literals[i];
                            final int var2 = Math.abs(undoLiteral);
                            final int y = features[var2];
                            final int y2 = y - ((undoLiteral >>> 31) == 0 ? 1 : -1);
                            features[var2] = y2;
                            if (y2 == 0) {
                                lits.pop();
                            }
                        }
                        continue clauseLoop;
                    } else {
                        features[var] = x + ((literal >>> 31) == 0 ? 1 : -1);
                        if (x == 0) {
                            lits.push(literal);
                        }
                    }
                }
                if (!combineConditions(conditionArray, t + 1, combinedCondition)) {
                    return false;
                }
                for (int i = 0; i < literals.length; i++) {
                    final int literal = literals[i];
                    final int var = Math.abs(literal);
                    final int y2 = features[var] - ((literal >>> 31) == 0 ? 1 : -1);
                    features[var] = y2;
                    if (y2 == 0) {
                        lits.pop();
                    }
                }
            }
        }
        return true;
    }
}
