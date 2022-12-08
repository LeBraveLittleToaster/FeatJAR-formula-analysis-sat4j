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
package de.featjar.analysis.sat4j.solver;

import de.featjar.analysis.solver.MusSolver;
import de.featjar.clauses.CNF;
import de.featjar.clauses.CNFProvider;
import de.featjar.formula.ModelRepresentation;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.xplain.Xplain;

/**
 * Implements a {@link MusSolver} using Sat4J.
 *
 * <br>
 * <br>
 * Sat4J only support the extraction of one minimal unsatisfiable subset, thus
 * {@link #getAllMinimalUnsatisfiableSubsets()} only returns one solution.
 *
 * <br>
 * <br>
 * Note: The usage of a solver to solve expression and to find minimal
 * unsatisfiable subset should be divided into two task because the native
 * solver for the MUS extractor are substantially slower in solving
 * satisfiability requests. If for solving the usage of the {@link Sat4JSolver}
 * is recommended.
 *
 * @author Joshua Sprey
 * @author Sebastian Krieter
 */
public class Sat4JMusSolver extends AbstractSat4JSolver<Xplain<ISolver>> implements MusSolver<IConstr> {

    public Sat4JMusSolver(ModelRepresentation modelRepresentation) {
        this(modelRepresentation.getCache().get(CNFProvider.fromFormula()).get());
    }

    public Sat4JMusSolver(CNF cnf) {
        super(cnf);
    }

    @Override
    protected Xplain<ISolver> createSolver() {
        return new Xplain<>(SolverFactory.newDefault());
    }

    @Override
    public List<IConstr> getMinimalUnsatisfiableSubset() throws IllegalStateException {
        if (hasSolution() == SatResult.TRUE) {
            throw new IllegalStateException("Problem is satisfiable");
        }
        try {
            return IntStream.of(solver.minimalExplanation()) //
                    .mapToObj(getFormula().getConstraints()::get) //
                    .collect(Collectors.toList());
        } catch (final TimeoutException e) {
            throw new IllegalStateException(e);
        }
    }

    @Override
    public List<List<IConstr>> getAllMinimalUnsatisfiableSubsets() throws IllegalStateException {
        return Collections.singletonList(getMinimalUnsatisfiableSubset());
    }
}
