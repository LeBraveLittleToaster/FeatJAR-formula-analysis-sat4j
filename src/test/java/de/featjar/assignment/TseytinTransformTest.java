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
package de.featjar.assignment;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import de.featjar.analysis.sat4j.AllConfigurationGenerator;
import de.featjar.formula.ModelRepresentation;
import de.featjar.formula.structure.Formula;
import de.featjar.formula.structure.Formulas;
import de.featjar.formula.structure.atomic.Assignment;
import de.featjar.formula.structure.atomic.literal.VariableMap;
import de.featjar.util.tree.Trees;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class TseytinTransformTest {

    @Test
    public void testImplies() {
        testTransform(FormulaCreator.getFormula01());
    }

    @Test
    public void testComplex() {
        testTransform(FormulaCreator.getFormula02());
    }

    private void testTransform(final Formula formulaOrg) {
        final Formula formulaClone = Trees.cloneTree(formulaOrg);
        final VariableMap map = formulaOrg.getVariableMap().orElseThrow();
        final VariableMap mapClone = map.clone();

        final ModelRepresentation rep = new ModelRepresentation(formulaOrg);
        // TODO Fix tseytin transformer
        //		CNF cnf = rep.get(CNFProvider.fromTseytinFormula());

        FormulaCreator.testAllAssignments(map, assignment -> {
            final Boolean orgEval =
                    (Boolean) Formulas.evaluate(formulaOrg, assignment).orElseThrow();
            final Boolean tseytinEval = evaluate(rep, assignment);
            Assertions.assertEquals(orgEval, tseytinEval, assignment.toString());
        });
        assertTrue(Trees.equals(formulaOrg, formulaClone));
        assertEquals(mapClone, map);
        assertEquals(mapClone, formulaOrg.getVariableMap().orElseThrow());
    }

    private Boolean evaluate(ModelRepresentation rep, final Assignment assignment) {
        final AllConfigurationGenerator analysis = new AllConfigurationGenerator();
        analysis.getAssumptions().setAll(assignment.getAll());
        analysis.setLimit(2);
        final int numSolutions =
                rep.getResult(analysis).orElseThrow().getSolutions().size();
        assertTrue(numSolutions < 2);
        return numSolutions == 1;
    }
}
