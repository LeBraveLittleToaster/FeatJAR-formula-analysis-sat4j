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
package de.featjar.analysis.mig.solver.visitor;

import de.featjar.analysis.mig.solver.MIG;
import de.featjar.analysis.mig.solver.Vertex;
import de.featjar.analysis.mig.solver.visitor.Visitor.VisitResult;
import de.featjar.clauses.LiteralList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import org.sat4j.core.VecInt;
import org.sat4j.specs.IteratorInt;

public class Traverser extends ATraverser {

    private static class CancelException extends Exception {
        private static final long serialVersionUID = 4872529212110156314L;
    }

    public Traverser(MIG mig) {
        super(mig);
    }

    @Override
    public void traverse(int... curLiterals) {
        try {
            traverseAll(curLiterals);
        } catch (final CancelException e) {
        }
    }

    private void traverseAll(int... curLiterals) throws CancelException {
        final HashMap<LiteralList, VecInt> openClauseMap = new HashMap<>();
        Arrays.fill(dfsMark, false);

        traverseStrong(openClauseMap, curLiterals);
        mainLoop:
        while (true) {
            for (final Iterator<Entry<LiteralList, VecInt>> openClauseIterator =
                            openClauseMap.entrySet().iterator();
                    openClauseIterator.hasNext(); ) {
                final VecInt openClause = openClauseIterator.next().getValue();
                if (openClause != null) {
                    for (final IteratorInt literalIterator = openClause.iterator(); literalIterator.hasNext(); ) {
                        final int literal = literalIterator.next();
                        if (currentConfiguration[getIndex(literal)] == 0) {
                            final int vertexIndex = MIG.getVertexIndex(literal);
                            if (!dfsMark[vertexIndex]) {
                                dfsMark[vertexIndex] = true;
                                boolean changed = false;
                                final VisitResult visitWeakResult = visitor.visitWeak(literal);
                                switch (visitWeakResult) {
                                    case Cancel:
                                        return;
                                    case Continue:
                                        changed |= addComplexClauses(openClauseMap, mig.getVertex(literal)) > 0;
                                        break;
                                    case Select:
                                        changed |= attemptStrongSelect(literal, openClauseMap);
                                        break;
                                    case Skip:
                                        break;
                                    default:
                                        throw new AssertionError(visitWeakResult);
                                }
                                changed |= processComplexClauses(openClauseMap);
                                if (changed) {
                                    continue mainLoop;
                                }
                            }
                        }
                    }
                }
            }
            break;
        }
    }

    @Override
    public void traverseStrong(int... curLiterals) {
        try {
            traverseStrong(new HashMap<>(), curLiterals);
        } catch (final CancelException e) {
        }
    }

    private void traverseStrong(final HashMap<LiteralList, VecInt> complexClauseMap, int... curLiterals)
            throws CancelException {
        boolean changed = false;
        for (final int curLiteral : curLiterals) {
            changed |= attemptStrongSelect(curLiteral, complexClauseMap);
        }
        if (changed) {
            processComplexClauses(complexClauseMap);
        }
    }

    private boolean processComplexClauses(final HashMap<LiteralList, VecInt> complexClauseMap) throws CancelException {
        boolean changedInLoop, changed = false;
        do {
            changedInLoop = false;
            final List<VecInt> unitClauses = new LinkedList<>();
            for (final Entry<LiteralList, VecInt> entry : complexClauseMap.entrySet()) {
                final VecInt v = entry.getValue();
                if (v != null) {
                    for (int j = v.size() - 1; j >= 0; j--) {
                        final int literal = v.get(j);
                        final int value = currentConfiguration[getIndex(literal)];
                        if (value != 0) {
                            if (value == literal) {
                                entry.setValue(null);
                            } else {
                                v.delete(j);
                            }
                            changed = true;
                        }
                    }

                    if (v.size() == 1) {
                        entry.setValue(null);
                        unitClauses.add(v);
                    }
                }
            }

            for (final VecInt v : unitClauses) {
                changedInLoop |= attemptStrongSelect(v.get(0), complexClauseMap);
            }
            changed |= changedInLoop;
        } while (changedInLoop);
        return changed;
    }

    private boolean attemptStrongSelect(final int curLiteral, final HashMap<LiteralList, VecInt> complexClauseMap)
            throws CancelException {
        final int modelIndex = getIndex(curLiteral);
        final int currentVariableSelection = currentConfiguration[modelIndex];
        if (currentVariableSelection == 0) {
            currentConfiguration[modelIndex] = curLiteral;
            VisitResult visitStrongResult = visitor.visitStrong(curLiteral);
            switch (visitStrongResult) {
                case Cancel:
                    throw new CancelException();
                case Skip:
                    return true;
                case Select:
                case Continue:
                    break;
                default:
                    throw new AssertionError(visitStrongResult);
            }

            final Vertex curVertex = mig.getVertex(curLiteral);
            addComplexClauses(complexClauseMap, curVertex);

            for (final Vertex strongVertex : curVertex.getStrongEdges()) {
                final int literal = strongVertex.getVar();
                final int strongVertexIndex = getIndex(literal);
                if (currentConfiguration[strongVertexIndex] == 0) {
                    currentConfiguration[strongVertexIndex] = literal;
                    visitStrongResult = visitor.visitStrong(literal);
                    switch (visitStrongResult) {
                        case Cancel:
                            throw new CancelException();
                        case Skip:
                            break;
                        case Select:
                        case Continue:
                            addComplexClauses(complexClauseMap, strongVertex);
                            break;
                        default:
                            throw new AssertionError(visitStrongResult);
                    }
                }
            }
            return true;
        } else if (currentVariableSelection != curLiteral) {
            // TODO

        }
        return false;
    }

    private int getIndex(final int literal) {
        return Math.abs(literal) - 1;
    }

    private int addComplexClauses(final HashMap<LiteralList, VecInt> complexClauseMap, final Vertex vertex) {
        int added = 0;
        final List<LiteralList> complexClauses = vertex.getComplexClauses();
        for (final LiteralList clause : complexClauses) {
            if (!complexClauseMap.containsKey(clause)) {
                complexClauseMap.put(clause, new VecInt(Arrays.copyOf(clause.getLiterals(), clause.size())));
                added++;
            }
        }
        return added;
    }
}
