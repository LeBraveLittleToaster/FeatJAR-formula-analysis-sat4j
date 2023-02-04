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
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.stream.Collectors;

/**
 * Manages and manipulates a list of {@link PresenceCondition presence
 * conditions}.
 *
 * @author Sebastian Krieter
 */
public class PresenceConditionManager {

    private final List<List<List<LiteralList>>> dictionary = new ArrayList<>();
    private final List<List<List<LiteralList>>> groupedPresenceConditions = new ArrayList<>();

    public PresenceConditionManager(
            LiteralList core, int numberOfVariables, List<List<List<LiteralList>>> expressions) {
        final HashMap<List<LiteralList>, List<LiteralList>> presenceConditionSet = new HashMap<>();

        dictionary.add(null);
        for (int i = 0; i < numberOfVariables; i++) {
            dictionary.add(new ArrayList<>());
            dictionary.add(new ArrayList<>());
        }

        for (final List<List<LiteralList>> group : expressions) {
            final List<List<LiteralList>> newNodeList = new ArrayList<>();
            expressionLoop:
            for (final List<LiteralList> clauses : group) {
                final List<LiteralList> newClauses = new ArrayList<>();
                for (final LiteralList clause : clauses) {
                    // If clause can be satisfied
                    if ((clause.countConflicts(core) == 0)) {
                        // If clause is already satisfied
                        if (core.containsAll(clause)) {
                            continue expressionLoop;
                        } else {
                            newClauses.add(clause.clone());
                        }
                    }
                }
                if (!newClauses.isEmpty()) {
                    final List<LiteralList> pc = new ArrayList<>(newClauses);
                    List<LiteralList> mappedPc = presenceConditionSet.get(pc);
                    if (mappedPc == null) {
                        mappedPc = pc;
                        presenceConditionSet.put(mappedPc, mappedPc);

                        for (final LiteralList literalSet : mappedPc) {
                            for (final int literal : literalSet.getLiterals()) {
                                final int dictionaryIndex = literal < 0 ? numberOfVariables - literal : literal;
                                dictionary.get(dictionaryIndex).add(mappedPc);
                            }
                        }
                    }
                    Collections.sort(mappedPc, (o1, o2) -> o1.size() - o2.size());
                    newNodeList.add(mappedPc);
                }
            }
            groupedPresenceConditions.add(newNodeList);
        }
    }

    public void shuffle(Random random) {
        for (final List<List<LiteralList>> pcs : groupedPresenceConditions) {
            Collections.shuffle(pcs, random);
        }
    }

    public void shuffleSort(Random random) {
        for (final List<List<LiteralList>> list : groupedPresenceConditions) {
            final Map<Integer, List<List<LiteralList>>> groupedPCs =
                    list.stream().collect(Collectors.groupingBy(List::size));
            for (final List<List<LiteralList>> pcList : groupedPCs.values()) {
                Collections.shuffle(pcList, random);
            }
            final List<Entry<Integer, List<List<LiteralList>>>> shuffledPCs = new ArrayList<>(groupedPCs.entrySet());
            Collections.sort(shuffledPCs, (a, b) -> a.getKey() - b.getKey());
            list.clear();
            for (final Entry<Integer, List<List<LiteralList>>> entry : shuffledPCs) {
                list.addAll(entry.getValue());
            }
        }
    }

    public void sort() {
        for (final List<List<LiteralList>> list : groupedPresenceConditions) {
            Collections.sort(list, this::comparePresenceConditions);
        }
    }

    private int comparePresenceConditions(List<LiteralList> o1, List<LiteralList> o2) {
        final int clauseCountDiff = o1.size() - o2.size();
        if (clauseCountDiff != 0) {
            return clauseCountDiff;
        }
        int clauseLengthDiff = 0;
        for (int i = 0; i < o1.size(); i++) {
            clauseLengthDiff += o2.get(i).size() - o1.get(i).size();
        }
        return clauseLengthDiff;
    }

    public List<List<List<LiteralList>>> getDictionary() {
        return dictionary;
    }

    public List<List<List<LiteralList>>> getGroupedPresenceConditions() {
        return groupedPresenceConditions;
    }
}
