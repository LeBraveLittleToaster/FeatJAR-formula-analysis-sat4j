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

import de.featjar.analysis.mig.solver.visitor.DefaultVisitor;
import de.featjar.analysis.mig.solver.visitor.Traverser;
import de.featjar.analysis.mig.solver.visitor.Visitor;
import de.featjar.analysis.sat4j.solver.SStrategy;
import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.analysis.solver.SatSolver;
import de.featjar.clauses.LiteralList;
import java.util.Arrays;
import org.sat4j.core.VecInt;

/**
 * Represent a solution within a covering array.
 *
 * @author Sebastian Krieter
 */
public class TWiseConfiguration extends LiteralList {

    private static final long serialVersionUID = -4775410644924706701L;

    public static final byte SELECTION_IMPOSSIBLE = 1;
    public static final byte SELECTION_SELECTED = 2;

    public static int SOLUTION_COUNT_THRESHOLD = 10;

    protected VecInt solutionLiterals;

    protected int countLiterals, rank = 0;

    protected final int numberOfVariableLiterals;
    protected final TWiseConfigurationUtil util;
    protected Traverser traverser;
    protected Visitor<?> visitor;

    protected VecInt solverSolutionIndex = new VecInt();

    private class DPVisitor extends DefaultVisitor {

        private int[] unknownValues = null;

        @Override
        public VisitResult visitStrong(int curLiteral) {
            addLiteral(curLiteral);
            if (unknownValues != null) {
                util.getSolver().getAssumptions().push(curLiteral);
                unknownValues[Math.abs(curLiteral) - 1] = 0;
            }
            return VisitResult.Continue;
        }

        @Override
        public final VisitResult visitWeak(final int curLiteral) {
            if (unknownValues == null) {
                final Sat4JSolver solver = util.getSolver();
                setUpSolver(solver);
                solver.setSelectionStrategy(SStrategy.original());
                switch (solver.hasSolution()) {
                    case FALSE:
                        return VisitResult.Cancel;
                    case TIMEOUT:
                        throw new RuntimeException();
                    case TRUE:
                        unknownValues = solver.getInternalSolution();
                        util.addSolverSolution(Arrays.copyOf(unknownValues, unknownValues.length));
                        solver.shuffleOrder(util.getRandom());
                        break;
                    default:
                        throw new RuntimeException();
                }
                if (unknownValues != null) {
                    solver.setSelectionStrategy(SStrategy.inverse(unknownValues));
                    solver.hasSolution();
                    final int[] model2 = solver.getInternalSolution();
                    util.addSolverSolution(Arrays.copyOf(model2, model2.length));

                    LiteralList.resetConflicts(unknownValues, model2);

                    final int[] literals = TWiseConfiguration.this.literals;
                    for (int k = 0; k < literals.length; k++) {
                        final int var = literals[k];
                        if ((var != 0) && (unknownValues[k] != 0)) {
                            unknownValues[k] = 0;
                        }
                    }
                } else {
                    throw new RuntimeException();
                }
            }
            return sat(unknownValues, curLiteral) ? VisitResult.Select : VisitResult.Continue;
        }

        private final boolean sat(final int[] unknownValues, final int curLiteral) {
            final int i = Math.abs(curLiteral) - 1;
            if (unknownValues[i] == curLiteral) {
                final Sat4JSolver solver = util.getSolver();
                solver.getAssumptions().push(-curLiteral);
                switch (solver.hasSolution()) {
                    case FALSE:
                        solver.getAssumptions().replaceLast(curLiteral);
                        unknownValues[i] = 0;
                        return true;
                    case TIMEOUT:
                        solver.getAssumptions().pop();
                        unknownValues[i] = 0;
                        break;
                    case TRUE:
                        solver.getAssumptions().pop();
                        final int[] solution2 = solver.getInternalSolution();
                        util.addSolverSolution(Arrays.copyOf(solution2, solution2.length));
                        LiteralList.resetConflicts(unknownValues, solution2);
                        solver.shuffleOrder(util.getRandom());
                        break;
                }
            }
            return false;
        }
    }

    public TWiseConfiguration(TWiseConfigurationUtil util) {
        super(new int[util.getCnf().getVariableMap().getVariableCount()], Order.INDEX, false);
        countLiterals = 0;
        this.util = util;
        if (util.hasSolver()) {
            for (final int var : util.getDeadCoreFeatures().getLiterals()) {
                literals[Math.abs(var) - 1] = var;
                countLiterals++;
            }
            numberOfVariableLiterals = literals.length - countLiterals;
            solutionLiterals = new VecInt(numberOfVariableLiterals);
            countLiterals = 0;
            if (util.hasMig()) {
                traverser = new Traverser(util.getMig());
                traverser.setModel(literals);
                visitor = new DefaultVisitor() {
                    @Override
                    public VisitResult visitStrong(int curLiteral) {
                        addLiteral(curLiteral);
                        return super.visitStrong(curLiteral);
                    }
                };
            } else {
                traverser = null;
                visitor = null;
            }
        } else {
            traverser = null;
            visitor = null;
            numberOfVariableLiterals = literals.length - countLiterals;
            solutionLiterals = new VecInt(numberOfVariableLiterals);
        }
    }

    public TWiseConfiguration(TWiseConfiguration other) {
        super(other);
        util = other.util;

        numberOfVariableLiterals = other.numberOfVariableLiterals;
        solverSolutionIndex = other.solverSolutionIndex;
        countLiterals = other.countLiterals;
        rank = other.rank;

        if (util.hasSolver()) {
            if (other.solutionLiterals != null) {
                solutionLiterals = new VecInt(numberOfVariableLiterals);
                other.solutionLiterals.copyTo(solutionLiterals);
            }
            if (util.hasMig()) {
                traverser = new Traverser(util.getMig());
                traverser.setModel(literals);

                visitor = new DefaultVisitor() {

                    @Override
                    public VisitResult visitStrong(int curLiteral) {
                        addLiteral(curLiteral);
                        return super.visitStrong(curLiteral);
                    }
                };
            } else {
                traverser = null;
                visitor = null;
            }
        } else {
            traverser = null;
            visitor = null;
        }
    }

    private void addLiteral(int curLiteral) {
        newLiteral(curLiteral);
    }

    private void newLiteral(int curLiteral) {
        countLiterals++;
        solutionLiterals.push(curLiteral);
        final int k = Math.abs(curLiteral) - 1;

        for (int i = 0; i < solverSolutionIndex.size(); i++) {
            if (util.getSolverSolution(solverSolutionIndex.get(i)).getLiterals()[k] == -curLiteral) {
                solverSolutionIndex.delete(i--);
            }
        }
    }

    public void setLiteral(int literal) {
        if (traverser != null) {
            traverser.setVisitor(visitor);
            traverser.traverseStrong(literals);
        } else {
            final int i = Math.abs(literal) - 1;
            if (literals[i] == 0) {
                literals[i] = literal;
                newLiteral(literal);
            }
        }
    }

    public void setLiteral(int... literals) {
        if (traverser != null) {
            traverser.setVisitor(visitor);
            traverser.traverseStrong(literals);
        } else {
            for (final int literal : literals) {
                final int i = Math.abs(literal) - 1;
                if (this.literals[i] == 0) {
                    this.literals[i] = literal;
                    newLiteral(literal);
                }
            }
        }
    }

    public void propagation() {
        final Sat4JSolver solver = util.getSolver();
        final int orgAssignmentSize;
        if (traverser != null) {
            final DPVisitor visitor = new DPVisitor();

            final int[] literals = Arrays.copyOf(solutionLiterals.toArray(), solutionLiterals.size());
            for (int i = 0, length = literals.length; i < length; i++) {
                this.literals[Math.abs(literals[i]) - 1] = 0;
            }
            solutionLiterals.clear();
            countLiterals = 0;

            orgAssignmentSize = solver.getAssumptions().size();
            traverser.setVisitor(visitor);
            traverser.traverse(literals);
        } else {
            orgAssignmentSize = setUpSolver(solver);

            solver.setSelectionStrategy(SStrategy.original());
            final int[] firstSolution = solver.findSolution().getLiterals();
            if (firstSolution != null) {
                util.addSolverSolution(Arrays.copyOf(firstSolution, firstSolution.length));
                solver.setSelectionStrategy(SStrategy.inverse(firstSolution));
                util.getSolver().hasSolution();
                final int[] secondSolution = util.getSolver().getInternalSolution();
                util.addSolverSolution(Arrays.copyOf(secondSolution, secondSolution.length));

                LiteralList.resetConflicts(firstSolution, secondSolution);
                for (final int literal : literals) {
                    if (literal != 0) {
                        firstSolution[Math.abs(literal) - 1] = 0;
                    }
                }

                for (int i = 0; i < firstSolution.length; i++) {
                    final int varX = firstSolution[i];
                    if (varX != 0) {
                        solver.getAssumptions().push(-varX);
                        switch (solver.hasSolution()) {
                            case FALSE:
                                solver.getAssumptions().replaceLast(varX);
                                setLiteral(varX);
                                break;
                            case TIMEOUT:
                                solver.getAssumptions().pop();
                                break;
                            case TRUE:
                                solver.getAssumptions().pop();
                                final int[] solution = solver.getInternalSolution();
                                util.addSolverSolution(Arrays.copyOf(solution, solution.length));
                                LiteralList.resetConflicts(firstSolution, solution);
                                solver.shuffleOrder(util.getRandom());
                                break;
                        }
                    }
                }
            }
        }
        solver.getAssumptions().clear(orgAssignmentSize);
        solver.setSelectionStrategy(SStrategy.random(util.getRandom()));
    }

    public void clear() {
        traverser = null;
        visitor = null;
        solutionLiterals = null;
        solverSolutionIndex = null;
    }

    public boolean isComplete() {
        return countLiterals == numberOfVariableLiterals;
    }

    public int countLiterals() {
        return countLiterals;
    }

    public void autoComplete() {
        if (!isComplete()) {
            if (util.hasSolver()) {
                if (solverSolutionIndex.isEmpty()) {
                    final Sat4JSolver solver = util.getSolver();
                    final int orgAssignmentSize = setUpSolver(solver);
                    try {
                        if (solver.hasSolution() == SatSolver.SatResult.TRUE) {
                            System.arraycopy(solver.getInternalSolution(), 0, literals, 0, literals.length);
                        }
                    } finally {
                        solver.getAssumptions().clear(orgAssignmentSize);
                    }
                } else {
                    System.arraycopy(
                            util.getSolverSolution(solverSolutionIndex.last()).getLiterals(),
                            0,
                            literals,
                            0,
                            literals.length);
                    solverSolutionIndex.clear();
                }
            } else {
                for (int i = 0; i < literals.length; i++) {
                    if (literals[i] == 0) {
                        literals[i] = -(i + 1);
                    }
                }
            }
            countLiterals = numberOfVariableLiterals;
        }
    }

    public LiteralList getCompleteSolution() {
        if (isComplete()) {
            return new LiteralList(this);
        } else {
            final int[] s;
            if (util.hasSolver()) {
                if (solverSolutionIndex.isEmpty()) {
                    final Sat4JSolver solver = util.getSolver();
                    final int orgAssignmentSize = setUpSolver(solver);
                    try {
                        final SatSolver.SatResult satResult = solver.hasSolution();
                        switch (satResult) {
                            case FALSE:
                                throw new RuntimeException("Solution Invalid!");
                            case TIMEOUT:
                                throw new RuntimeException("SatSolver Timeout!");
                            case TRUE:
                                s = solver.getInternalSolution();
                                break;
                            default:
                                throw new RuntimeException(satResult.toString());
                        }
                    } finally {
                        solver.getAssumptions().clear(orgAssignmentSize);
                    }
                } else {
                    s = util.getSolverSolution(solverSolutionIndex.last()).getLiterals();
                    if (s == null) {
                        throw new RuntimeException();
                    }
                }
            } else {
                s = Arrays.copyOf(literals, literals.length);
                for (int i = 0; i < s.length; i++) {
                    if (s[i] == 0) {
                        s[i] = -(i + 1);
                    }
                }
            }
            return (s == null) ? null : new LiteralList(Arrays.copyOf(s, s.length), Order.INDEX, false);
        }
    }

    public void generateRandomSolutions(int count) {
        final Sat4JSolver solver = util.getSolver();
        solver.setSelectionStrategy(SStrategy.random(util.getRandom()));
        final int orgAssignmentSize = setUpSolver(solver);
        try {
            for (int i = 0; i < count; i++) {
                solver.hasSolution();
                final int[] randomSolution = solver.getInternalSolution();
                util.addSolverSolution(Arrays.copyOf(randomSolution, randomSolution.length));
                solver.shuffleOrder(util.getRandom());
            }
        } finally {
            solver.getAssumptions().clear(orgAssignmentSize);
        }
    }

    public boolean isValid() {
        final Sat4JSolver solver = util.getSolver();
        final SStrategy selectionStrategy = solver.getSelectionStrategy();
        final int orgAssignmentSize = setUpSolver(solver);
        solver.setSelectionStrategy(SStrategy.original());
        try {
            return solver.hasSolution() == SatSolver.SatResult.TRUE;
        } finally {
            solver.getAssumptions().clear(orgAssignmentSize);
            solver.setSelectionStrategy(selectionStrategy);
        }
    }

    public int setUpSolver(final Sat4JSolver solver) {
        final int orgAssignmentSize = solver.getAssumptions().size();
        if (isComplete()) {
            for (int i = 0; i < literals.length; i++) {
                solver.getAssumptions().push(literals[i]);
            }
        } else {
            final int[] array = solutionLiterals.toArray();
            for (int i = 0, length = solutionLiterals.size(); i < length; i++) {
                solver.getAssumptions().push(array[i]);
            }
        }
        return orgAssignmentSize;
    }

    public void setRank(int rank) {
        this.rank = rank;
    }

    public void updateSolverSolutions() {
        if (util.hasSolver() && (solutionLiterals != null)) {
            solverSolutionIndex.clear();
            final int[] array = solutionLiterals.toArray();
            final LiteralList[] solverSolutions = util.getSolverSolutions();
            solutionLoop:
            for (int i = 0; i < solverSolutions.length; i++) {
                final LiteralList solverSolution = solverSolutions[i];
                if (solverSolution == null) {
                    break;
                }
                final int[] solverSolutionLiterals = solverSolution.getLiterals();
                for (int j = 0, length = solutionLiterals.size(); j < length; j++) {
                    final int k = Math.abs(array[j]) - 1;
                    if (solverSolutionLiterals[k] == -literals[k]) {
                        continue solutionLoop;
                    }
                }
                solverSolutionIndex.push(i);
            }
        }
    }

    public void updateSolverSolutions(int[] solverSolution, int index) {
        if (solverSolutionIndex != null) {
            for (int i = 0; i < solverSolutionIndex.size(); i++) {
                if (solverSolutionIndex.get(i) == index) {
                    solverSolutionIndex.delete(i);
                    break;
                }
            }
            final int[] array = solutionLiterals.toArray();
            for (int i = 0, length = solutionLiterals.size(); i < length; i++) {
                final int k = Math.abs(array[i]) - 1;
                if (solverSolution[k] == -literals[k]) {
                    return;
                }
            }
            solverSolutionIndex.push(index);
        }
    }

    public VecInt getSolverSolutionIndex() {
        return solverSolutionIndex;
    }

    @Override
    public int hashCode() {
        return Arrays.hashCode(literals);
    }

    @Override
    public TWiseConfiguration clone() {
        return new TWiseConfiguration(this);
    }
}
