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

import de.featjar.analysis.sat4j.AtomicSetAnalysis;
import de.featjar.clauses.LiteralList;
import de.featjar.formula.ModelRepresentation;
import de.featjar.formula.io.KConfigReaderFormat;
import de.featjar.formula.structure.Formula;
import de.featjar.util.io.IO;
import de.featjar.util.io.format.FormatSupplier;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import org.junit.jupiter.api.Test;

public class CNFTransformTest {

    @Test
    public void testDistributiveBug() {
        final Path modelFile = Paths.get("src/test/resources/kconfigreader/distrib-bug.model");
        final Formula formula =
                IO.load(modelFile, FormatSupplier.of(new KConfigReaderFormat())).orElseThrow();

        final ModelRepresentation rep = new ModelRepresentation(formula);
        final List<LiteralList> atomicSets =
                rep.getResult(new AtomicSetAnalysis()).orElseThrow();
        assertEquals(5, atomicSets.size());
    }
}
