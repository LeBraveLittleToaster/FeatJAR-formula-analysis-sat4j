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

import de.featjar.analysis.sat4j.solver.SStrategy;
import de.featjar.analysis.sat4j.solver.SampleDistribution;
import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.analysis.solver.SatSolver;
import de.featjar.clauses.LiteralList;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.util.data.Identifier;
import de.featjar.util.job.Executor;
import de.featjar.util.job.InternalMonitor;
import de.featjar.util.logging.Logger;
import java.util.List;

/**
 * Finds certain solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
public class SampleRandomConfigurationGenerator extends RandomConfigurationGenerator {

    public static final Identifier<SolutionList> identifier = new Identifier<>();

    @Override
    public Identifier<SolutionList> getIdentifier() {
        return identifier;
    }

    private int sampleSize = 100;
    private List<LiteralList> sample;
    private SampleDistribution dist;

    @Override
    protected void init(InternalMonitor monitor) {
        satisfiable = findCoreFeatures(solver);
        if (!satisfiable) {
            return;
        }

        final RandomConfigurationGenerator gen = new FastRandomConfigurationGenerator();
        gen.setAllowDuplicates(false);
        gen.setRandom(getRandom());
        gen.setLimit(sampleSize);
        sample = Executor.run(gen::execute, solver.getCnf())
                .map(SolutionList::getSolutions)
                .orElse(Logger::logProblems);
        if ((sample == null) || sample.isEmpty()) {
            satisfiable = false;
            return;
        }

        dist = new SampleDistribution(sample);
        dist.setRandom(getRandom());
        solver.setSelectionStrategy(SStrategy.uniform(dist));
    }

    @Override
    protected void reset() {
        dist.reset();
    }

    private boolean findCoreFeatures(Sat4JSolver solver) {
        final int[] fixedFeatures = solver.findSolution().getLiterals();
        if (fixedFeatures == null) {
            return false;
        }
        solver.setSelectionStrategy(SStrategy.inverse(fixedFeatures));

        // find core/dead features
        for (int i = 0; i < fixedFeatures.length; i++) {
            final int varX = fixedFeatures[i];
            if (varX != 0) {
                solver.getAssumptions().push(-varX);
                final SatSolver.SatResult hasSolution = solver.hasSolution();
                switch (hasSolution) {
                    case FALSE:
                        solver.getAssumptions().replaceLast(varX);
                        break;
                    case TIMEOUT:
                        solver.getAssumptions().pop();
                        break;
                    case TRUE:
                        solver.getAssumptions().pop();
                        LiteralList.resetConflicts(fixedFeatures, solver.getInternalSolution());
                        solver.shuffleOrder(getRandom());
                        break;
                }
            }
        }
        return true;
    }

    public int getSampleSize() {
        return sampleSize;
    }

    public void setSampleSize(int sampleSize) {
        this.sampleSize = sampleSize;
    }
}
