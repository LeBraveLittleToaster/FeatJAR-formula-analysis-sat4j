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

import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.analysis.solver.SatSolver;
import de.featjar.clauses.CNF;
import de.featjar.util.data.Identifier;
import de.featjar.util.job.InternalMonitor;

/**
 * Determines whether a given {@link CNF} is satisfiable and returns the found
 * solution.
 *
 * @author Sebastian Krieter
 */
public class HasSolutionAnalysis extends Sat4JAnalysis<Boolean> {

    public static final Identifier<Boolean> identifier = new Identifier<>();

    @Override
    public Identifier<Boolean> getIdentifier() {
        return identifier;
    }

    @Override
    public Boolean analyze(Sat4JSolver solver, InternalMonitor monitor) throws Exception {
        final SatSolver.SatResult hasSolution = solver.hasSolution();
        switch (hasSolution) {
            case FALSE:
                return false;
            case TIMEOUT:
                reportTimeout();
                return false;
            case TRUE:
                return true;
            default:
                throw new AssertionError(hasSolution);
        }
    }
}
