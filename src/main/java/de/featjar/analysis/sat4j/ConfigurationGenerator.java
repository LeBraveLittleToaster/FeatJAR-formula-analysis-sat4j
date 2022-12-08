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

import de.featjar.analysis.Analysis;
import de.featjar.clauses.LiteralList;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.util.data.Cache;
import de.featjar.util.job.InternalMonitor;
import java.util.Spliterator;
import java.util.function.Supplier;
import java.util.stream.Stream;

/**
 * Interface for configuration generators. Can be used as a {@link Supplier} or
 * to get a {@link Stream} or a {@link SolutionList} of configurations.
 *
 * @author Sebastian Krieter
 */
public interface ConfigurationGenerator
        extends Analysis<SolutionList>, Supplier<LiteralList>, Spliterator<LiteralList> {

    void init(Cache rep, InternalMonitor monitor);

    int getLimit();

    void setLimit(int limit);

    boolean isAllowDuplicates();

    void setAllowDuplicates(boolean allowDuplicates);
}
