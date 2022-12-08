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

import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.clauses.LiteralList;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.util.data.Cache;
import de.featjar.util.job.InternalMonitor;
import java.util.ArrayList;
import java.util.Spliterator;
import java.util.function.Consumer;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

/**
 * Finds certain solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
public abstract class AbstractConfigurationGenerator extends Sat4JAnalysis<SolutionList>
        implements ConfigurationGenerator {

    private int maxSampleSize = Integer.MAX_VALUE;

    protected boolean allowDuplicates = false;

    @Override
    public int getLimit() {
        return maxSampleSize;
    }

    @Override
    public void setLimit(int limit) {
        maxSampleSize = limit;
    }

    @Override
    public boolean isAllowDuplicates() {
        return allowDuplicates;
    }

    @Override
    public void setAllowDuplicates(boolean allowDuplicates) {
        this.allowDuplicates = allowDuplicates;
    }

    @Override
    public int characteristics() {
        return NONNULL | IMMUTABLE;
    }

    @Override
    public long estimateSize() {
        return Long.MAX_VALUE;
    }

    @Override
    public boolean tryAdvance(Consumer<? super LiteralList> consumer) {
        final LiteralList literalList = get();
        if (literalList != null) {
            consumer.accept(literalList);
            return true;
        } else {
            return false;
        }
    }

    @Override
    public Spliterator<LiteralList> trySplit() {
        return null;
    }

    @Override
    public void init(Cache c, InternalMonitor monitor) {
        solver = createSolver(c.get(solverInputProvider).get());
        monitor.checkCancel();
        prepareSolver(solver);
        init(monitor);
    }

    protected void init(InternalMonitor monitor) {}

    @Override
    public final SolutionList analyze(Sat4JSolver solver, InternalMonitor monitor) throws Exception {
        init(monitor);
        monitor.setTotalWork(maxSampleSize);
        return new SolutionList(
                solver.getVariables(),
                StreamSupport.stream(this, false) //
                        .limit(maxSampleSize) //
                        .peek(c -> monitor.step()) //
                        .collect(Collectors.toCollection(ArrayList::new)));
    }
}
