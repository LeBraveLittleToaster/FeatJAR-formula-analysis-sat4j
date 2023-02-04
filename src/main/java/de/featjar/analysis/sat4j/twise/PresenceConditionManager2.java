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
public class PresenceConditionManager2 {

    private final List<List<LiteralList>> presenceConditions = new ArrayList<>();

    public PresenceConditionManager2(
            LiteralList core, int numberOfVariables, List<List<LiteralList>> rawPresenceConditions) {
        expressionLoop:
        for (final List<LiteralList> clauses : rawPresenceConditions) {
            final List<LiteralList> newClauses = new ArrayList<>(clauses.size());
            for (final LiteralList clause : clauses) {
                // If clause can be satisfied
                if (!clause.hasConflicts(core)) {
                    // If clause is already satisfied
                    if (core.containsAll(clause)) {
                        continue expressionLoop;
                    } else {
                        newClauses.add(clause.clone());
                    }
                }
            }
            if (!newClauses.isEmpty()) {
                Collections.sort(newClauses, (o1, o2) -> o1.size() - o2.size());
                presenceConditions.add(newClauses);
            }
        }
    }

    public void shuffle(Random random) {
        Collections.shuffle(presenceConditions, random);
    }

    public void shuffleSort(Random random) {
        final Map<Integer, List<List<LiteralList>>> groupedPCs =
                presenceConditions.stream().collect(Collectors.groupingBy(List::size));
        for (final List<List<LiteralList>> pcList : groupedPCs.values()) {
            Collections.shuffle(pcList, random);
        }
        final List<Entry<Integer, List<List<LiteralList>>>> shuffledPCs = new ArrayList<>(groupedPCs.entrySet());
        Collections.sort(shuffledPCs, (a, b) -> a.getKey() - b.getKey());
        presenceConditions.clear();
        for (final Entry<Integer, List<List<LiteralList>>> entry : shuffledPCs) {
            presenceConditions.addAll(entry.getValue());
        }
    }

    public void sort() {
        Collections.sort(presenceConditions, this::comparePresenceConditions);
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

    public List<List<LiteralList>> getPresenceConditions() {
        return presenceConditions;
    }

    public int getPresenceConditionCount() {
        return presenceConditions.size();
    }
}
