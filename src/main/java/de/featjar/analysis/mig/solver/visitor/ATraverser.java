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
package de.featjar.analysis.mig.solver.visitor;

import de.featjar.analysis.mig.solver.MIG;

abstract class ATraverser implements ITraverser {

    protected final boolean[] dfsMark;
    protected final MIG mig;

    protected Visitor<?> visitor = null;
    protected int[] currentConfiguration = null;

    public ATraverser(MIG mig) {
        this.mig = mig;
        dfsMark = new boolean[mig.getVertices().size()];
    }

    @Override
    public Visitor<?> getVisitor() {
        return visitor;
    }

    @Override
    public void setVisitor(Visitor<?> visitor) {
        this.visitor = visitor;
    }

    @Override
    public void setModel(int[] currentConfiguration) {
        this.currentConfiguration = currentConfiguration;
    }
}
