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
package de.featjar.analysis.sat4j.solver;

import de.featjar.analysis.mig.solver.MIGDistribution;
import java.util.Random;

public interface SStrategy {

    public enum Strategy {
        Original,
        Negative,
        Positive,
        Fixed,
        InverseFixed,
        FastRandom,
        UniformRandom,
        MIGRandom
    }

    Strategy strategy();

    public static final class OriginalStrategy implements SStrategy {
        @Override
        public Strategy strategy() {
            return Strategy.Original;
        }
    }

    public static final class NegativeStrategy implements SStrategy {
        @Override
        public Strategy strategy() {
            return Strategy.Negative;
        }
    }

    public static final class PositiveStrategy implements SStrategy {
        @Override
        public Strategy strategy() {
            return Strategy.Positive;
        }
    }

    public static final class FixedStrategy implements SStrategy {
        private final int[] model;

        public FixedStrategy(int[] model) {
            this.model = model;
        }

        @Override
        public Strategy strategy() {
            return Strategy.Fixed;
        }

        public int[] getModel() {
            return model;
        }
    }

    public static final class InverseFixedStrategy implements SStrategy {
        private final int[] model;

        public InverseFixedStrategy(int[] model) {
            this.model = model;
        }

        @Override
        public Strategy strategy() {
            return Strategy.InverseFixed;
        }

        public int[] getModel() {
            return model;
        }
    }

    public static final class FastRandomStrategy implements SStrategy {
        private final Random random;

        public FastRandomStrategy(Random random) {
            this.random = random;
        }

        @Override
        public Strategy strategy() {
            return Strategy.FastRandom;
        }

        public Random getRandom() {
            return random;
        }
    }

    public static final class UniformRandomStrategy implements SStrategy {
        private final LiteralDistribution dist;

        public UniformRandomStrategy(LiteralDistribution dist) {
            this.dist = dist;
        }

        @Override
        public Strategy strategy() {
            return Strategy.UniformRandom;
        }

        public LiteralDistribution getDist() {
            return dist;
        }
    }

    public static final class MIGRandomStrategy implements SStrategy {
        private final MIGDistribution dist;

        public MIGRandomStrategy(MIGDistribution dist) {
            this.dist = dist;
        }

        @Override
        public Strategy strategy() {
            return Strategy.MIGRandom;
        }

        public MIGDistribution getDist() {
            return dist;
        }
    }

    static OriginalStrategy original() {
        return new OriginalStrategy();
    }

    static NegativeStrategy negative() {
        return new NegativeStrategy();
    }

    static PositiveStrategy positive() {
        return new PositiveStrategy();
    }

    static FastRandomStrategy random(Random random) {
        return new FastRandomStrategy(random);
    }

    static FastRandomStrategy random() {
        return new FastRandomStrategy(new Random());
    }

    static FixedStrategy fixed(int[] model) {
        return new FixedStrategy(model);
    }

    static InverseFixedStrategy inverse(int[] model) {
        return new InverseFixedStrategy(model);
    }

    static UniformRandomStrategy uniform(LiteralDistribution dist) {
        return new UniformRandomStrategy(dist);
    }

    static MIGRandomStrategy mig(MIGDistribution dist) {
        return new MIGRandomStrategy(dist);
    }
}
