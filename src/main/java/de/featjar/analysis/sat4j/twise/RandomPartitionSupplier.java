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

import de.featjar.clauses.solutions.combinations.BinomialCalculator;
import java.util.Random;

/**
 * Presence condition combination supplier that uses the combinatorial number
 * system to enumerate all combinations and then alternately iterates over
 * certain randomized partitions of the combination space.
 *
 * @author Sebastian Krieter
 */
public class RandomPartitionSupplier implements ICombinationSupplier<int[]> {

    private final long numCombinations;
    private final BinomialCalculator binomialCalculator;

    private long counter = 0;

    private final int[][] dim;
    private final int[] pos;
    private final int radix;

    public RandomPartitionSupplier(int t, int n) {
        this(t, n, new Random(42));
    }

    public RandomPartitionSupplier(int t, int n, Random random) {
        binomialCalculator = new BinomialCalculator(t, n);
        numCombinations = binomialCalculator.binomial(n, t);

        final int numDim = 4 * t;
        radix = (int) Math.ceil(Math.pow(numCombinations, 1.0 / numDim));
        dim = new int[numDim][radix];
        pos = new int[numDim];

        for (int i = 0; i < dim.length; i++) {
            final int[] dimArray = dim[i];
            for (int j = 0; j < radix; j++) {
                dimArray[j] = j;
            }
        }

        for (int i = 0; i < dim.length; i++) {
            final int[] dimArray = dim[i];
            for (int j = dimArray.length - 1; j >= 0; j--) {
                final int index = random.nextInt(j + 1);
                final int a = dimArray[index];
                dimArray[index] = dimArray[j];
                dimArray[j] = a;
            }
        }
    }

    @Override
    public int[] get() {
        final long nextIndex = nextIndex();
        return nextIndex < 0 ? null : binomialCalculator.combination(nextIndex);
    }

    protected long nextIndex() {
        if (counter++ >= numCombinations) {
            return -1;
        }
        int result;
        do {
            result = 0;
            for (int i = 0; i < pos.length; i++) {
                result += Math.pow(radix, i) * dim[i][pos[i]];
            }
            for (int i = pos.length - 1; i >= 0; i--) {
                final int p = pos[i];
                if ((p + 1) < radix) {
                    pos[i] = p + 1;
                    break;
                } else {
                    pos[i] = 0;
                }
            }
        } while (result >= numCombinations);

        return result;
    }

    @Override
    public long size() {
        return numCombinations;
    }
}
