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

import de.featjar.clauses.Clauses;
import de.featjar.clauses.LiteralList;
import de.featjar.clauses.solutions.analysis.SolutionUpdater;
import de.featjar.formula.ModelRepresentation;
import de.featjar.formula.structure.Formula;
import de.featjar.formula.structure.atomic.Assignment;
import de.featjar.formula.structure.atomic.literal.VariableMap;
import de.featjar.util.data.Pair;
import java.util.List;
import java.util.Optional;

public class ConfigurationCompletor implements SolutionUpdater {
    private final ConfigurationGenerator generator;
    private final ModelRepresentation model;

    public ConfigurationCompletor(ModelRepresentation model, ConfigurationGenerator generator) {
        this.generator = generator;
        this.model = model;
    }

    @Override
    public Optional<LiteralList> update(LiteralList partialSolution) {
        final de.featjar.analysis.mig.CoreDeadAnalysis analysis = new de.featjar.analysis.mig.CoreDeadAnalysis();
        analysis.setFixedFeatures(partialSolution.getLiterals(), partialSolution.size());
        // TODO return empty for contradicting partial configuration
        return Optional.of(partialSolution.addAll(model.get(analysis)));
    }

    @Override
    public Optional<LiteralList> complete(LiteralList partialSolution, LiteralList... excludeClauses) {
        if (partialSolution == null && excludeClauses.length == 0) {
            return Optional.ofNullable(generator.get());
        }
        final LiteralList result;
        final Assignment assumptions = generator.getAssumptions();
        final List<Pair<Integer, Object>> oldAssumptions = assumptions.getAll();

        if (partialSolution != null) {
            for (int literal : partialSolution.getLiterals()) {
                assumptions.set(Math.abs(literal), literal > 0);
            }
        }
        VariableMap variables = model.getVariables();
        List<Formula> assumedConstraints = generator.getAssumedConstraints();
        for (LiteralList clause : excludeClauses) {
            assumedConstraints.add(Clauses.toOrClause(clause.negate(), variables));
        }
        generator.updateAssumptions();

        result = generator.get();

        generator.resetAssumptions();
        assumptions.unsetAll();
        assumptions.setAll(oldAssumptions);
        assumedConstraints.clear();
        generator.updateAssumptions();
        return Optional.ofNullable(result);
    }
}
