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
package de.featjar.assignment;

import de.featjar.analysis.mig.solver.MIGProvider;
import de.featjar.analysis.mig.solver.MIGVisitorProvider;
import de.featjar.analysis.mig.solver.MIGVisitorProvider.Visitor;
import de.featjar.formula.ModelRepresentation;
import de.featjar.util.extension.ExtensionLoader;
import de.featjar.util.logging.Logger;
import java.nio.file.Paths;
import java.util.Arrays;

public class MIGTest {

    public static void main(String[] args) {
        ExtensionLoader.load();

        String file = "src/test/resources/GPL/model.xml";
        MIGVisitorProvider mig = ModelRepresentation //
                .load(Paths.get(file)) //
                .map(m -> m.get(MIGProvider.fromFormula(false, false))) //
                .map(MIGVisitorProvider::new) //
                .orElse(Logger::logProblems);
        Visitor visitor = mig.getVisitor();

        int[] candidate, newCandidate;

        candidate = new int[] {5};
        newCandidate = visitor.extend(candidate);
        visitor.reset();
        System.out.println(Arrays.toString(candidate) + " -> " + Arrays.toString(newCandidate));

        candidate = new int[] {17, 33};
        newCandidate = visitor.extend(candidate);
        visitor.reset();
        System.out.println(Arrays.toString(candidate) + " -> " + Arrays.toString(newCandidate));

        candidate = new int[] {-5, -6, -16};
        newCandidate = visitor.extend(candidate);
        visitor.reset();
        System.out.println(Arrays.toString(candidate) + " -> " + Arrays.toString(newCandidate));
    }
}
