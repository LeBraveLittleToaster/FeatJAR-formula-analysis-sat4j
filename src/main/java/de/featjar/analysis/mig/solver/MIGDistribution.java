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
package de.featjar.analysis.mig.solver;

import de.featjar.analysis.sat4j.solver.LiteralDistribution;
import de.featjar.clauses.LiteralList;
import java.util.Arrays;

/**
 * Uses a sample of configurations to achieve a phase selection that corresponds
 * to a uniform distribution of configurations in the configuration space.
 *
 * @author Sebastian Krieter
 */
public class MIGDistribution extends LiteralDistribution {

    private final byte[] model;
    private final MIG mig;
    private int count;

    public MIGDistribution(MIG mig) {
        this.mig = mig;
        model = new byte[mig.size()];
        count = 0;
        for (final Vertex vertex : mig.getVertices()) {
            if (vertex.isNormal()) {
                count++;
            }
        }
        count /= 2;
    }

    @Override
    public void reset() {
        Arrays.fill(model, (byte) 0);
    }

    @Override
    public void unset(int var) {
        final int index = var - 1;
        final byte sign = model[index];
        if (sign != 0) {
            model[index] = 0;
        }
    }

    @Override
    public void set(int literal) {
        final int index = Math.abs(literal) - 1;
        if (model[index] == 0) {
            model[index] = (byte) (literal > 0 ? 1 : -1);
        }
    }

    @Override
    public int getRandomLiteral(int var) {
        int strongInPositive = 0;
        int strongInNegative = 0;
        int weakInPositive = 0;
        int weakInNegative = 0;

        //		count = 0;
        for (final Vertex vertex : mig.getVertices()) {
            if (vertex.isNormal() && (model[Math.abs(vertex.getVar()) - 1] == 0)) {
                //				if (vertex.getVar() > 0) {
                //					count++;
                //				}s
                for (final Vertex strong : vertex.getStrongEdges()) {
                    final int strongLiteral = strong.getVar();
                    if (Math.abs(strongLiteral) == var) {
                        if (strongLiteral > 0) {
                            strongInPositive++;
                        } else {
                            strongInNegative++;
                        }
                    }
                }
                for (final LiteralList weak : vertex.getComplexClauses()) {
                    for (final int l : weak.getLiterals()) {
                        if (Math.abs(l) == var) {
                            if (l > 0) {
                                weakInPositive += 1.0 / (weak.getLiterals().length - 1);
                            } else {
                                weakInNegative += 1.0 / (weak.getLiterals().length - 1);
                            }
                        }
                    }
                }
            }
        }
        double score = 1;
        score -= getScore(weakInNegative, strongInNegative, count);
        score += getScore(weakInPositive, strongInPositive, count);
        score *= 0.5;
        return random.nextDouble() < score ? var : -var;
    }

    private static double getScore(double strong, double weak, double total) {
        return Math.log((((strong + weak) / (total - 1)) + 1)) / Math.log(2);
    }
}
