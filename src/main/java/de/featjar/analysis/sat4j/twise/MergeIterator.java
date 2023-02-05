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
import java.util.List;

/**
 * Combines multiple {@link ICombinationSupplier supplies} of {@link ClauseList}
 * and returns results from each supplier by turns.
 *
 * @author Sebastian Krieter
 */
public class MergeIterator implements ICombinationSupplier<List<LiteralList>> {

    private final List<List<List<LiteralList>>> expressionSets;
    private final ICombinationSupplier<int[]>[] suppliers;
    private final long numberOfCombinations;

    private final List<List<LiteralList>> buffer = new ArrayList<>();
    private final TWiseCombiner combiner;
    private final List<LiteralList>[] nextCombination;

    private int bufferIndex = 0;
    private final int maxIteratorIndex;

    @SuppressWarnings("unchecked")
    public MergeIterator(int t, int n, List<List<List<LiteralList>>> expressionSets) {
        this.expressionSets = expressionSets;

        maxIteratorIndex = expressionSets.size() - 1;
        suppliers = new ICombinationSupplier[expressionSets.size()];
        combiner = new TWiseCombiner(n);
        nextCombination = new List[t];

        long sumNumberOfCombinations = 0;
        for (int i = 0; i <= maxIteratorIndex; i++) {
            final ICombinationSupplier<int[]> supplier =
                    new RandomPartitionSupplier(t, expressionSets.get(i).size());
            suppliers[i] = supplier;
            sumNumberOfCombinations += supplier.size();
        }
        numberOfCombinations = sumNumberOfCombinations;
    }

    @Override
    public List<LiteralList> get() {
        if (buffer.isEmpty()) {
            for (int i = 0; i <= maxIteratorIndex; i++) {
                final ICombinationSupplier<int[]> supplier = suppliers[i];
                if (supplier != null) {
                    final int[] js = supplier.get();
                    if (js != null) {
                        final List<List<LiteralList>> expressionSet = expressionSets.get(i);
                        for (int j = 0; j < js.length; j++) {
                            nextCombination[j] = expressionSet.get(js[j]);
                        }
                        final List<LiteralList> combinedCondition = new ArrayList<>();
                        combiner.combineConditions(nextCombination, combinedCondition);
                        buffer.add(combinedCondition);
                    } else {
                        suppliers[i] = null;
                    }
                }
            }
            if (buffer.isEmpty()) {
                return null;
            }
        }
        final List<LiteralList> remove = buffer.get(bufferIndex++);
        if (bufferIndex == buffer.size()) {
            buffer.clear();
            bufferIndex = 0;
        }
        return remove;
    }

    @Override
    public long size() {
        return numberOfCombinations;
    }
}
