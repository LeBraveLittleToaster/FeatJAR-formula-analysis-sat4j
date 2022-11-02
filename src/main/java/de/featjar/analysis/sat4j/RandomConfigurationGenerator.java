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
package de.featjar.analysis.sat4j;

import de.featjar.analysis.sat4j.solver.SStrategy;
import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.analysis.solver.RuntimeContradictionException;
import de.featjar.clauses.LiteralList;
import de.featjar.util.job.InternalMonitor;
import java.util.Random;

/**
 * Finds random valid solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
public abstract class RandomConfigurationGenerator extends AbstractConfigurationGenerator {

    protected boolean satisfiable = true;

    public RandomConfigurationGenerator() {
        super();
        setRandom(new Random());
    }

    @Override
    protected void init(InternalMonitor monitor) {
        super.init(monitor);
        satisfiable = true;
    }    
    
    @Override
    protected void prepareSolver(Sat4JSolver solver) {
        super.prepareSolver(solver);
        solver.setSelectionStrategy(SStrategy.random());
    }

    @Override
    public LiteralList get() {
        reset();
        solver.shuffleOrder(random);
        final LiteralList solution = solver.findSolution();
        if (solution == null) {
            return null;
        }
        if (!allowDuplicates) {
            try {
                forbidSolution(solution.negate());
            } catch (final RuntimeContradictionException e) {
                satisfiable = false;
            }
        }
        return solution;
    }

    protected void forbidSolution(final LiteralList negate) {
        solver.getFormula().push(negate);
    }

    protected void reset() {}
}
