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
package de.featjar.formula.analysis.todo.mig;

import de.featjar.formula.analysis.todo.mig.solver.ModalImplicationGraph;
import de.featjar.formula.analysis.todo.mig.solver.SAT4JMIGSolver;

import java.util.Random;

/**
 * Base class for analyses using a {@link SAT4JMIGSolver}.
 *
 * @param <T> the type of the analysis result.
 *
 * @author Sebastian Krieter
 */
public abstract class Sat4JMIGAnalysis<T> {

    protected boolean timeoutOccurred = false;
    private boolean throwTimeoutException = true;
    private int timeout = 1000;

    protected Random random = new Random(112358);

    public Sat4JMIGAnalysis() {
        solverInputComputation = MIGComputation.fromFormula();
    }

    @Override
    public Object getParameters() {
        return assumptions != null ? assumptions : super.getParameters();
    }

    public Random getRandom() {
        return random;
    }

    public void setRandom(Random random) {
        this.random = random;
    }

    public final T execute(IMonitor monitor) {
        return solver != null ? execute(solver, progress) : null;
    }

    @Override
    protected SAT4JMIGSolver createSolver(ModalImplicationGraph input) throws SolverContradictionException {
        return new SAT4JMIGSolver(input);
    }

    @Override
    protected void prepareSolver(SAT4JMIGSolver solver) {
        super.prepareSolver(solver);
        solver.setTimeout(timeout);
        timeoutOccurred = false;
    }

    protected final void reportTimeout() throws SolverTimeoutException {
        timeoutOccurred = true;
        if (throwTimeoutException) {
            throw new SolverTimeoutException();
        }
    }

    public final boolean isThrowTimeoutException() {
        return throwTimeoutException;
    }

    public final void setThrowTimeoutException(boolean throwTimeoutException) {
        this.throwTimeoutException = throwTimeoutException;
    }

    public final boolean isTimeoutOccurred() {
        return timeoutOccurred;
    }

    public int getTimeout() {
        return timeout;
    }

    public void setTimeout(int timeout) {
        this.timeout = timeout;
    }
}
