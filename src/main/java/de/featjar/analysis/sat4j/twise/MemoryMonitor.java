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
package de.featjar.analysis.sat4j.twise;

import de.featjar.util.job.UpdateFunction;

public final class MemoryMonitor implements UpdateFunction {

    public long maxUsedMemory = 0;
    public long maxAllocatedMemory = 0;

    @Override
    public boolean update() {
        final long allocatedMemory = Runtime.getRuntime().totalMemory();
        final long freeMemory = Runtime.getRuntime().freeMemory();
        final long usedMemory = allocatedMemory - freeMemory;
        if (allocatedMemory > maxAllocatedMemory) {
            maxAllocatedMemory = allocatedMemory;
        }
        if (usedMemory > maxUsedMemory) {
            maxUsedMemory = usedMemory;
        }
        return true;
    }
}
