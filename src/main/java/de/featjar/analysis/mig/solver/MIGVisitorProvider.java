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

import de.featjar.analysis.solver.RuntimeContradictionException;
import de.featjar.clauses.LiteralList;
import java.util.Arrays;
import java.util.List;

/**
 * Adjacency list implementation based on arrays. Intended to use for faster
 * traversion.
 *
 * @author Sebastian Krieter
 */
public class MIGVisitorProvider {

    private final int size;

    private final int[] core;

    private final int[][] strong;

    private final int[][] clauseIndices;
    private final int[] clauses;

    private final int[][] clauseCountIndices;
    private final int[] clauseCounts;

    public class Visitor {

        public final int[] tempClauseCounts;
        public final int[] model;
        public final int[] newLiterals;

        public int modelCount;

        public Visitor(int[] model) {
            this.model = model;
            for (int l : core) {
                model[Math.abs(l) - 1] = l;
            }
            newLiterals = new int[size - core.length];
            tempClauseCounts = Arrays.copyOf(clauseCounts, clauseCounts.length);
        }

        public Visitor() {
            this(new int[size]);
        }

        public void propagate(int... literals) throws RuntimeContradictionException {
            for (int l : literals) {
                processLiteral(l);
            }
        }

        public int[] extend(int... literals) throws RuntimeContradictionException {
            for (int l : literals) {
                processLiteral(l);
            }
            return Arrays.copyOf(newLiterals, modelCount);
        }

        public boolean isContradiction(int... literals) {
            try {
                propagate(literals);
                return false;
            } catch (RuntimeContradictionException e) {
                return true;
            }
        }

        public void reset() {
            for (int i = 0; i < modelCount; i++) {
                final int l = newLiterals[i];
                model[Math.abs(l) - 1] = 0;
                for (int clauseCountIndex : clauseCountIndices[getVertexIndex(l)]) {
                    tempClauseCounts[clauseCountIndex] = clauseCounts[clauseCountIndex];
                }
            }
            modelCount = 0;
        }

        public void reset(int keep) {
            for (int i = 0; i < modelCount; i++) {
                for (int clauseCountIndex : clauseCountIndices[getVertexIndex(newLiterals[i])]) {
                    tempClauseCounts[clauseCountIndex] = clauseCounts[clauseCountIndex];
                }
            }
            for (int i = keep; i < modelCount; i++) {
                model[Math.abs(newLiterals[i]) - 1] = 0;
            }
            modelCount = keep;
            for (int i = 0; i < modelCount; i++) {
                for (int j : clauseCountIndices[getVertexIndex(newLiterals[i])]) {
                    --tempClauseCounts[j];
                }
            }
        }

        private void processLiteral(int l) {
            final int varIndex = Math.abs(l) - 1;
            final int setL = model[varIndex];
            if (setL == 0) {
                model[varIndex] = l;
                newLiterals[modelCount++] = l;

                final int i = getVertexIndex(l);

                for (int strongL : strong[i]) {
                    final int varIndex1 = Math.abs(strongL) - 1;
                    final int setL1 = model[varIndex1];
                    if (setL1 == 0) {
                        model[varIndex1] = strongL;
                        newLiterals[modelCount++] = strongL;
                        processWeak(getVertexIndex(strongL));
                    } else if (setL1 != strongL) {
                        throw new RuntimeContradictionException();
                    }
                }

                processWeak(i);
            } else if (setL != l) {
                throw new RuntimeContradictionException();
            }
        }

        private void processWeak(final int i) {
            final int[] clauseCountIndexList = clauseCountIndices[i];
            weakLoop:
            for (int j = 0; j < clauseCountIndexList.length; j++) {
                final int clauseCountIndex = clauseCountIndexList[j];
                final int count = --tempClauseCounts[clauseCountIndex];
                if (count <= 1) {
                    if (count == 1) {
                        int clauseIndex = clauseIndices[i][j];
                        for (int end = clauseIndex + clauseCounts[clauseCountIndex], k = clauseIndex; k < end; k++) {
                            final int newL = clauses[k];
                            final int modelL = model[Math.abs(newL) - 1];
                            if (modelL == 0 || modelL == newL) {
                                processLiteral(newL);
                                continue weakLoop;
                            }
                        }
                    }
                    throw new RuntimeContradictionException();
                }
            }
        }
    }

    public static int getVertexIndex(int literal) {
        return literal < 0 ? (-literal - 1) << 1 : ((literal - 1) << 1) + 1;
    }

    public MIGVisitorProvider(MIG mig) {
        size = mig.size();

        strong = new int[2 * size][0];
        clauseIndices = new int[2 * size][0];
        clauseCountIndices = new int[2 * size][0];

        int coreSize = 0;
        int clausesSize = 0;
        int clauseCountsSize = 0;

        for (Vertex v : mig.getVertices()) {
            if (v.isNormal()) {
                int vertexIndex = getVertexIndex(v.getVar());

                List<Vertex> strongEdges = v.getStrongEdges();
                final int[] curStrong = new int[strongEdges.size()];
                for (int i = 0; i < curStrong.length; i++) {
                    curStrong[i] = strongEdges.get(i).getVar();
                }
                strong[vertexIndex] = curStrong;

                int weakCount = v.complexClauses.size();
                clauseIndices[vertexIndex] = new int[weakCount];
                clauseCountIndices[vertexIndex] = new int[weakCount];
            } else if (v.isCore()) {
                coreSize++;
            }
        }

        core = new int[coreSize];
        int coreI = 0;
        for (Vertex v : mig.getVertices()) {
            if (v.isCore()) {
                core[coreI++] = v.getVar();
            }
        }

        for (LiteralList clause : mig.getClauseList()) {
            if (clause.size() > 2) {
                clausesSize += clause.size();
                clauseCountsSize++;
            }
        }

        clauses = new int[clausesSize];
        clauseCounts = new int[clauseCountsSize];
        int clausesI = 0;
        int clauseCountI = 0;
        for (LiteralList clause : mig.getClauseList()) {
            if (clause.size() > 2) {
                int startClausesI = clausesI;
                int[] literals = clause.getLiterals();
                for (int i = 0; i < literals.length; i++) {
                    final int l = literals[i];
                    clauses[clausesI++] = l;
                    int vertexIndex = getVertexIndex(-l);
                    int[] clauseCountIndexList = clauseCountIndices[vertexIndex];
                    int k = 0;
                    for (; k < clauseCountIndexList.length; k++) {
                        if (clauseCountIndexList[k] == 0) {
                            clauseCountIndexList[k] = clauseCountI;
                            break;
                        }
                    }
                    try {
                        clauseIndices[vertexIndex][k] = startClausesI;
                    } catch (RuntimeException e) {
                        System.out.println(clause);
                        throw e;
                    }
                }
                clauseCounts[clauseCountI++] = clause.size();
            }
        }
    }

    public Visitor getVisitor() {
        return new Visitor();
    }

    public Visitor getVisitor(int[] model) {
        return new Visitor(model);
    }

    public int[] getCore() {
        return core;
    }

    public int size() {
        return size;
    }
}
