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
package de.featjar.formula.analysis.sat4j.todo.twise;

import de.featjar.formula.analysis.bool.ABooleanAssignmentList;

import java.util.ArrayList;
import java.util.Collections;
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

    private final List<List<PresenceCondition>> dictionary = new ArrayList<>();
    private final List<List<PresenceCondition>> groupedPresenceConditions = new ArrayList<>();

    public PresenceConditionManager(TWiseConfigurationUtil util, List<List<ABooleanAssignmentList>> expressions) {
        final SortedIntegerList coreDeadFeature = util.getDeadCoreFeatures();
        final int numberOfVariables = util.getCnf().getVariableMap().getVariableCount();

        final HashMap<PresenceCondition, PresenceCondition> presenceConditionSet = new HashMap<>();

        dictionary.add(null);
        for (int i = 0; i < numberOfVariables; i++) {
            dictionary.add(new ArrayList<PresenceCondition>());
            dictionary.add(new ArrayList<PresenceCondition>());
        }

        int groupIndex = 0;
        for (final List<ABooleanAssignmentList> group : expressions) {
            final List<PresenceCondition> newFormulaList = new ArrayList<>();
            expressionLoop:
            for (final ABooleanAssignmentList clauses : group) {
                final List<SortedIntegerList> newSortedIntegerLists = new ArrayList<>();
                for (final SortedIntegerList sortedIntegerList : clauses) {
                    // If clause can be satisfied
                    if ((sortedIntegerList.countConflicts(coreDeadFeature) == 0)) {
                        // If clause is already satisfied
                        if (coreDeadFeature.containsAll(sortedIntegerList)) {
                            continue expressionLoop;
                        } else {
                            newSortedIntegerLists.add(sortedIntegerList.clone());
                        }
                    }
                }
                if (!newSortedIntegerLists.isEmpty()) {
                    final PresenceCondition pc = new PresenceCondition(new ABooleanAssignmentList(newSortedIntegerLists));
                    PresenceCondition mappedPc = presenceConditionSet.get(pc);
                    if (mappedPc == null) {
                        mappedPc = pc;
                        presenceConditionSet.put(mappedPc, mappedPc);

                        for (final SortedIntegerList literalSet : mappedPc) {
                            for (final int literal : literalSet.getIntegers()) {
                                final int dictionaryIndex = literal < 0 ? numberOfVariables - literal : literal;
                                dictionary.get(dictionaryIndex).add(mappedPc);
                            }
                        }
                    }
                    mappedPc.addGroup(groupIndex);
                    Collections.sort(mappedPc, (o1, o2) -> o1.size() - o2.size());
                    newFormulaList.add(mappedPc);
                }
            }
            groupedPresenceConditions.add(newFormulaList);
            groupIndex++;
        }
    }

    public void shuffle(Random random) {
        for (final List<PresenceCondition> pcs : groupedPresenceConditions) {
            Collections.shuffle(pcs, random);
        }
    }

    public void shuffleSort(Random random) {
        for (final List<PresenceCondition> list : groupedPresenceConditions) {
            final Map<Integer, List<PresenceCondition>> groupedPCs =
                    list.stream().collect(Collectors.groupingBy(PresenceCondition::size));
            for (final List<PresenceCondition> pcList : groupedPCs.values()) {
                Collections.shuffle(pcList, random);
            }
            final List<Entry<Integer, List<PresenceCondition>>> shuffledPCs = new ArrayList<>(groupedPCs.entrySet());
            Collections.sort(shuffledPCs, (a, b) -> a.getKey() - b.getKey());
            list.clear();
            for (final Entry<Integer, List<PresenceCondition>> entry : shuffledPCs) {
                list.addAll(entry.getValue());
            }
        }
    }

    public void sort() {
        for (final List<PresenceCondition> list : groupedPresenceConditions) {
            Collections.sort(list, this::comparePresenceConditions);
        }
    }

    private int comparePresenceConditions(PresenceCondition o1, PresenceCondition o2) {
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

    public List<List<PresenceCondition>> getDictionary() {
        return dictionary;
    }

    public List<List<PresenceCondition>> getGroupedPresenceConditions() {
        return groupedPresenceConditions;
    }
}
