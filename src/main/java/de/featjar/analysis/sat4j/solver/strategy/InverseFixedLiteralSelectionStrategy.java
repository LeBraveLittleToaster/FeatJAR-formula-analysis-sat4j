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
package de.featjar.analysis.sat4j.solver.strategy;

import static org.sat4j.core.LiteralsUtils.negLit;
import static org.sat4j.core.LiteralsUtils.posLit;

public class InverseFixedLiteralSelectionStrategy extends FixedLiteralSelectionStrategy {

    public InverseFixedLiteralSelectionStrategy(int[] model) {
        super(model);
    }

    private static final long serialVersionUID = -1563968211094190882L;

    @Override
    protected void reset(int nlength) {
        for (int i = 1; i < nlength; i++) {
            phase[i] = model[i - 1] < 0 ? posLit(i) : negLit(i);
        }
    }
}
