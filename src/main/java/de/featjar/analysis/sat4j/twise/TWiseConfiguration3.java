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

import de.featjar.analysis.mig.solver.MIGVisitorProvider;
import de.featjar.analysis.mig.solver.MIGVisitorProvider.Visitor;
import de.featjar.clauses.LiteralList;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Iterator;

/**
 * Represent a solution within a covering array.
 *
 * @author Sebastian Krieter
 */
public class TWiseConfiguration3 extends LiteralList {

    private static final long serialVersionUID = -4775410644924706701L;

    final int numberOfVariableLiterals;
    final int id;

    Visitor visitor;

    ArrayDeque<LiteralList> solverSolutions;

    public TWiseConfiguration3(TWiseConfiguration3 config) {
        super(config);
        id = config.id;
        numberOfVariableLiterals = config.visitor.newLiterals.length;
        visitor = config.visitor.getVisitorProvider().new Visitor(config.visitor, literals);
        solverSolutions = config.solverSolutions != null ? new ArrayDeque<>(config.solverSolutions) : null;
    }

    public TWiseConfiguration3(
            int id, MIGVisitorProvider mig, ArrayDeque<LiteralList> randomSample, int... newliterals) {
        super(new int[mig.size()], Order.INDEX, false);
        this.id = id;
        visitor = mig.getVisitor(this.literals);
        numberOfVariableLiterals = visitor.newLiterals.length;
        solverSolutions = new ArrayDeque<>();
        visitor.propagate(newliterals);
    }

    public void updateSolutionList(ArrayDeque<LiteralList> solverSolutions) {
        solutionLoop:
        for (LiteralList solution : solverSolutions) {
            final int[] solverSolutionLiterals = solution.getLiterals();
            for (int j = 0; j < visitor.modelCount; j++) {
                int l = visitor.newLiterals[j];
                final int k = Math.abs(l) - 1;
                if (solverSolutionLiterals[k] != l) {
                    continue solutionLoop;
                }
            }
            this.solverSolutions.add(solution);
        }
    }

    public void updateSolutionList(int lastIndex) {
        if (isComplete()) {
            clear();
        } else {
            for (int i = lastIndex; i < visitor.modelCount; i++) {
                final int newLiteral = visitor.newLiterals[i];
                final int k = Math.abs(newLiteral) - 1;
                for (Iterator<LiteralList> it = solverSolutions.iterator(); it.hasNext(); ) {
                    final int[] solverSolutionLiterals = it.next().getLiterals();
                    if (solverSolutionLiterals[k] != newLiteral) {
                        it.remove();
                    }
                }
            }
        }
    }

    public int setLiteral(int... literals) {
        final int oldModelCount = visitor.modelCount;
        visitor.propagate(literals);
        return oldModelCount;
    }

    public void clear() {
        solverSolutions = null;
    }

    public boolean isComplete() {
        return visitor.modelCount == numberOfVariableLiterals;
    }

    public int countLiterals() {
        return visitor.modelCount;
    }

    @Override
    public int hashCode() {
        return Arrays.hashCode(literals);
    }
}
