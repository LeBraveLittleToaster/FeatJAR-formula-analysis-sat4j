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
 * Uses a {@link RandomPartitionSupplier} to construct a combined presence
 * condition for every combination.
 *
 * @author Sebastian Krieter
 */
public class SingleIterator implements ICombinationSupplier<List<LiteralList>> {

    private final List<List<LiteralList>> expressionSet;
    private final ICombinationSupplier<int[]> supplier;
    private final long numberOfCombinations;

    private final TWiseCombiner combiner;
    private final List<LiteralList>[] nextCombination;

    public SingleIterator(int t, int n, List<List<LiteralList>> expressionSet) {
        this.expressionSet = expressionSet;

        combiner = new TWiseCombiner(n);
        nextCombination = new List[t];

        supplier = new RandomPartitionSupplier(t, expressionSet.size());
        numberOfCombinations = supplier.size();
    }

    @Override
    public List<LiteralList> get() {
        final int[] js = supplier.get();
        if (js != null) {
            for (int j = 0; j < js.length; j++) {
                nextCombination[j] = expressionSet.get(js[j]);
            }
            final List<LiteralList> combinedCondition = new ArrayList<>();
            combiner.combineConditions(nextCombination, combinedCondition);
            return combinedCondition;
        } else {
            return null;
        }
    }

    @Override
    public long size() {
        return numberOfCombinations;
    }
}
