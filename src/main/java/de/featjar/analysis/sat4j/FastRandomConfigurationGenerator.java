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
package de.featjar.analysis.sat4j;

import de.featjar.analysis.sat4j.solver.SStrategy;
import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.util.data.Identifier;

/**
 * Generates random configurations for a given propositional formula.
 *
 * @author Sebastian Krieter
 */
public class FastRandomConfigurationGenerator extends RandomConfigurationGenerator {

    public static final Identifier<SolutionList> identifier = new Identifier<>();
    private SStrategy originalSelectionStrategy;

    @Override
    public Identifier<SolutionList> getIdentifier() {
        return identifier;
    }

    @Override
    protected void prepareSolver(Sat4JSolver solver) {
        super.prepareSolver(solver);
        originalSelectionStrategy = solver.getSelectionStrategy();
        solver.setSelectionStrategy(SStrategy.random(getRandom()));
    }

    @Override
    protected void resetSolver(Sat4JSolver solver) {
        super.resetSolver(solver);
        solver.setSelectionStrategy(originalSelectionStrategy);
    }
}
