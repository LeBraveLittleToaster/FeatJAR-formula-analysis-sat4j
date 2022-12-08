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
package de.featjar.analysis.mig.io;

import de.featjar.analysis.mig.solver.MIG;
import de.featjar.util.io.format.Format;

/**
 * Reads / Writes a MIG.
 *
 * @author Sebastian Krieter
 */
public class MIGFormat implements Format<MIG> {

    public static final String ID = "format.mig." + MIGFormat.class.getSimpleName();

    @Override
    public boolean supportsParse() {
        return true;
    }

    @Override
    public boolean supportsSerialize() {
        return true;
    }

    @Override
    public String getIdentifier() {
        return ID;
    }

    @Override
    public String getName() {
        return "ModalImplicationGraph";
    }

    @Override
    public String getFileExtension() {
        return "mig";
    }
}
