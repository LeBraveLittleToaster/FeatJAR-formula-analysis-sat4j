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
package de.featjar.formula.analysis.todo.mig.solver;

import java.util.Comparator;

/**
 * Compares the dependencies of the {@link SortedIntegerList literals} using a
 * {@link ModalImplicationGraph}.
 *
 * @author Sebastian Krieter
 */
public class MIGComparator implements Comparator<SortedIntegerList> {

    private static class VertexInfo {

        int weakOut, weakIn, strongOut, strongIn;

        @Override
        public String toString() {
            return "VertexInfo [weakOut=" + weakOut + ", weakIn=" + weakIn + ", strongOut=" + strongOut + ", strongIn="
                    + strongIn + "]";
        }
    }

    private final VertexInfo[] vertexInfos;

    public MIGComparator(ModalImplicationGraph modalImplicationGraph) {
        vertexInfos = new VertexInfo[modalImplicationGraph.getVertices().size()];
        for (final Vertex vertex : modalImplicationGraph.getVertices()) {
            vertexInfos[ModalImplicationGraph.getVertexIndex(vertex)] = new VertexInfo();
        }
        for (final Vertex vertex : modalImplicationGraph.getVertices()) {
            final VertexInfo vertexInfo = vertexInfos[ModalImplicationGraph.getVertexIndex(vertex)];
            vertexInfo.strongOut = vertex.getStrongEdges().size();
            vertexInfo.weakOut = vertex.getComplexClauses().size();
            for (final Vertex strongEdge : vertex.getStrongEdges()) {
                vertexInfos[ModalImplicationGraph.getVertexIndex(strongEdge)].strongIn++;
            }
            for (final SortedIntegerList sortedIntegerList : vertex.getComplexClauses()) {
                for (final int literal : sortedIntegerList.getIntegers()) {
                    if (literal != vertex.getVar()) {
                        vertexInfos[ModalImplicationGraph.getVertexIndex(literal)].weakIn++;
                    }
                }
            }
        }
    }

    @Override
    public int compare(SortedIntegerList o1, SortedIntegerList o2) {
        final double f1 = computeValue(o1);
        final double f2 = computeValue(o2);
        return (int) Math.signum(f1 - f2);
    }

    public String getValue(SortedIntegerList o1) {
        final VertexInfo vi1 = vertexInfos[ModalImplicationGraph.getVertexIndex(o1.getIntegers()[0])];
        final double f1 = computeValue(o1);
        return o1 + " | " + vi1 + " -> " + f1;
    }

    public double computeValue(SortedIntegerList... set) {
        int vIn = 0;
        int vOut = 0;
        for (final SortedIntegerList literalSet : set) {
            for (final int literal : literalSet.getIntegers()) {
                final VertexInfo info = vertexInfos[ModalImplicationGraph.getVertexIndex(literal)];
                vIn += (info.strongIn) + info.weakIn;
                vOut += (info.strongOut) + info.weakOut;
            }
        }
        return vIn - (vOut * vOut);
    }

    public int getOut(SortedIntegerList... set) {
        int vOut = 0;
        for (final SortedIntegerList literalSet : set) {
            for (final int literal : literalSet.getIntegers()) {
                final VertexInfo info = vertexInfos[ModalImplicationGraph.getVertexIndex(literal)];
                vOut += info.strongOut + info.weakOut;
            }
        }
        return vOut;
    }
}
