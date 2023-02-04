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

import de.featjar.analysis.mig.solver.MIG;
import de.featjar.analysis.mig.solver.MIGBuilder;
import de.featjar.analysis.mig.solver.MIGVisitorProvider;
import de.featjar.analysis.mig.solver.RegularMIGBuilder;
import de.featjar.analysis.sat4j.AbstractConfigurationGenerator;
import de.featjar.analysis.sat4j.solver.SStrategy;
import de.featjar.analysis.solver.RuntimeContradictionException;
import de.featjar.analysis.solver.RuntimeTimeoutException;
import de.featjar.analysis.solver.SatSolver;
import de.featjar.analysis.solver.SatSolver.SatResult;
import de.featjar.clauses.CNF;
import de.featjar.clauses.LiteralList;
import de.featjar.clauses.LiteralList.Order;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.clauses.solutions.combinations.ACombinationIterator;
import de.featjar.clauses.solutions.combinations.BinomialCalculator;
import de.featjar.clauses.solutions.combinations.LexicographicIterator;
import de.featjar.util.data.Identifier;
import de.featjar.util.job.Executor;
import de.featjar.util.job.InternalMonitor;
import de.featjar.util.logging.Logger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;
import java.util.function.Supplier;
import org.sat4j.core.VecInt;

/**
 * YASA sampling algorithm. Generates configurations for a given propositional
 * formula such that t-wise feature coverage is achieved.
 *
 * @author Sebastian Krieter
 */
public class YASA extends AbstractConfigurationGenerator {

    public static final Identifier<SolutionList> identifier = new Identifier<>();

    @Override
    public Identifier<SolutionList> getIdentifier() {
        return identifier;
    }

    /**
     * Converts a set of single literals into a grouped expression list.
     *
     * @param literalSet the literal set
     * @return a grouped expression list (can be used as an input for the
     *         configuration generator).
     */
    public static List<List<LiteralList>> convertLiterals(LiteralList literalSet) {
        final List<List<LiteralList>> arrayList = new ArrayList<>(literalSet.size());
        for (final Integer literal : literalSet.getLiterals()) {
            final List<LiteralList> clauseList = new ArrayList<>(1);
            clauseList.add(new LiteralList(literal));
            arrayList.add(clauseList);
        }
        return arrayList;
    }

    public static final int DEFAULT_ITERATIONS = 1;
    public static final int GLOBAL_SOLUTION_LIMIT = 100_000;

    // TODO Variation Point: Iterations of removing low-contributing Configurations
    private int iterations = DEFAULT_ITERATIONS;

    protected TWiseCombiner combiner;
    protected Random random = new Random(10);

    protected int t;

    // TODO simplify
    protected List<List<LiteralList>> nodes;
    protected PresenceConditionManager2 presenceConditionManager;

    // private List<TWiseConfiguration3> curResult = null;
    private List<LiteralList> bestResult = null;
    private ArrayDeque<LiteralList> randomSample;

    private int maxSampleSize = Integer.MAX_VALUE;

    private List<VecInt> indexedSolutions;
    private final List<TWiseConfiguration3> incompleteSolutionList = new LinkedList<>();
    private final List<TWiseConfiguration3> completeSolutionList = new ArrayList<>();
    private final ArrayList<TWiseConfiguration3> candidateConfiguration = new ArrayList<>();
    private TWiseConfiguration3 newConfiguration;
    private int curSolutionId;

    private MIGVisitorProvider mig;

    public int getT() {
        return t;
    }

    public void setT(int t) {
        this.t = t;
    }

    public void setNodes(List<List<LiteralList>> nodes) {
        this.nodes = nodes;
    }

    @Override
    public Random getRandom() {
        return random;
    }

    @Override
    public void setRandom(Random random) {
        this.random = random;
    }

    public int getIterations() {
        return iterations;
    }

    public void setIterations(int iterations) {
        this.iterations = iterations;
    }

    @Override
    protected void init(InternalMonitor monitor) {
        final CNF cnf = solver.getCnf();
        solver.rememberSolutionHistory(0);
        solver.setSelectionStrategy(SStrategy.random(getRandom()));

        if (nodes == null) {
            nodes = convertLiterals(LiteralList.getLiterals(cnf));
        }

        randomSample = new ArrayDeque<>(GLOBAL_SOLUTION_LIMIT);

        final MIGBuilder migBuilder = new RegularMIGBuilder();
        migBuilder.setCheckRedundancy(false);
        migBuilder.setDetectStrong(false);
        mig = new MIGVisitorProvider(Executor.run(migBuilder, solver.getCnf()).get());

        // TODO Variation Point: Sorting Nodes
        presenceConditionManager = new PresenceConditionManager2(
                new LiteralList(mig.getCore(), Order.NATURAL),
                cnf.getVariableMap().getVariableCount(),
                nodes);
        // TODO Variation Point: Building Combinations
        combiner = new TWiseCombiner(cnf.getVariableMap().getVariableCount());

        monitor.setTotalWork(iterations
                * new BinomialCalculator(
                                t,
                                presenceConditionManager.getPresenceConditions().size())
                        .binomial(
                                presenceConditionManager.getPresenceConditions().size(), t));
        monitor.setStatusReporter(new Supplier<>() {
            @Override
            public String get() {
                return incompleteSolutionList.size() + " + " + completeSolutionList.size();
            }
        });

        curSolutionId = 0;
        buildCombinations(monitor, 0);
        Logger.logDebug(incompleteSolutionList.size() + completeSolutionList.size() + " (" + bestResult.size() + ")");
        for (int i = 1; i < iterations; i++) {
            trimConfigurations();
            buildCombinations(monitor, i);
            Logger.logDebug(
                    incompleteSolutionList.size() + completeSolutionList.size() + " (" + bestResult.size() + ")");
        }
        Collections.reverse(bestResult);
    }

    @Override
    public LiteralList get() {
        return bestResult.isEmpty() ? null : bestResult.remove(bestResult.size() - 1);
    }

    private void trimConfigurations() {
        if (completeSolutionList.size() + incompleteSolutionList.size() > 0) {
            final ArrayList<TWiseConfiguration3> curResult =
                    new ArrayList<>(completeSolutionList.size() + incompleteSolutionList.size());
            curResult.addAll(incompleteSolutionList);
            curResult.addAll(completeSolutionList);
            final CoverageStatistic statistic = new TWiseStatisticFastGenerator()
                    .getCoverage2(curResult, presenceConditionManager.getPresenceConditions(), t);

            final double[] normConfigValues = statistic.getConfigScores();
            final double reference = Arrays.stream(normConfigValues).average().getAsDouble();

            int index = 0;
            index = removeSolutions(normConfigValues, reference, index, incompleteSolutionList);
            index = removeSolutions(normConfigValues, reference, index, completeSolutionList);
        }
    }

    private int removeSolutions(
            double[] values, final double reference, int index, List<TWiseConfiguration3> solutionList) {
        for (final Iterator<TWiseConfiguration3> iterator = solutionList.iterator(); iterator.hasNext(); ) {
            TWiseConfiguration3 solution = iterator.next();
            if (values[index++] < reference) {
                iterator.remove();
                for (int l : solution.getLiterals()) {
                    if (l != 0) {
                        VecInt vecInt = indexedSolutions.get(MIG.getVertexIndex(l));
                        int indexOf = vecInt.indexOf(solution.id);
                        if (indexOf > 0) {
                            vecInt.delete(indexOf);
                        }
                    }
                }
            }
        }
        return index;
    }

    private void buildCombinations(InternalMonitor monitor, int phase) {
        final int[] combinationLiterals = new int[t];
        final int[] literals = new int[presenceConditionManager.getPresenceConditionCount()];
        presenceConditionManager.shuffleSort(getRandom());
        // TODO Variation Point: Combination order
        List<List<LiteralList>> presenceConditions = presenceConditionManager.getPresenceConditions();
        final ACombinationIterator it;
        switch (phase) {
            case 0:
                //			it = new DiagonalIterator(t, presenceConditions.size());
                it = new LexicographicIterator(t, presenceConditions.size());
                break;
            case 1:
                it = new LexicographicIterator(t, presenceConditions.size());
                break;
            default:
                //			it = new RandomPartitionIterator(t, presenceConditions.size());
                it = new LexicographicIterator(t, presenceConditions.size());
                break;
        }

        for (int i1 = 0; i1 < literals.length; i1++) {
            literals[i1] = presenceConditions.get(i1).get(0).getLiterals()[0];
        }

        int initialCapacity = 2 * mig.size();
        indexedSolutions = new ArrayList<>(initialCapacity);
        for (int i2 = 0; i2 < initialCapacity; i2++) {
            indexedSolutions.add(new VecInt());
        }

        if (phase == 0) {
            for (int[] next = it.next(); next != null; next = it.next()) {
                monitor.step();
                for (int i = 0; i < next.length; i++) {
                    combinationLiterals[i] = literals[next[i]];
                }

                if (isCovered2(combinationLiterals)) {
                    continue;
                }
                if (isCombinationInvalidMIG(combinationLiterals)) {
                    continue;
                }
                if (firstCover(combinationLiterals)) {
                    continue;
                }
                if (!isCombinationValidSample(combinationLiterals) && isCombinationInvalidSAT(combinationLiterals)) {
                    continue;
                }
                if (coverSat(combinationLiterals)) {
                    continue;
                }
                newConfiguration(combinationLiterals);
            }
        } else {
            for (int[] next = it.next(); next != null; next = it.next()) {
                monitor.step();
                for (int i = 0; i < next.length; i++) {
                    combinationLiterals[i] = literals[next[i]];
                }

                if (!isCoveredBestResult(combinationLiterals)) {
                    continue;
                }
                if (isCovered2(combinationLiterals)) {
                    continue;
                }
                if (firstCover(combinationLiterals)) {
                    continue;
                }
                if (coverSat(combinationLiterals)) {
                    continue;
                }
                newConfiguration(combinationLiterals);
            }
        }

        if ((bestResult == null) || (bestResult.size() > incompleteSolutionList.size() + completeSolutionList.size())) {
            bestResult = new ArrayList<>(incompleteSolutionList.size() + completeSolutionList.size());
            incompleteSolutionList.stream().peek(this::autoComplete).forEach(bestResult::add);
            completeSolutionList.stream().peek(this::autoComplete).forEach(bestResult::add);
        }
    }

    private static boolean isCovered(int[] literals, Iterable<? extends LiteralList> solutionList) {
        for (final LiteralList configuration : solutionList) {
            if (configuration.containsAll(literals)) {
                return true;
            }
        }
        return false;
    }

    private boolean isCoveredBestResult(int[] literals) {
        for (final LiteralList configuration : bestResult) {
            if (configuration.containsAll(literals)) {
                return true;
            }
        }
        return false;
    }

    private boolean isCovered2(int[] literals) {
        final VecInt i0 = indexedSolutions.get(MIGVisitorProvider.getVertexIndex(literals[0]));
        final VecInt i1 = indexedSolutions.get(MIGVisitorProvider.getVertexIndex(literals[1]));
        int size0, size1;
        if ((size0 = i0.size()) == 0 || (size1 = i1.size()) == 0) {
            return false;
        }
        int it0 = 0;
        int it1 = 0;
        int id0 = -1;
        int id1 = -2;
        while (true) {
            while (id0 < id1) {
                if (it0 == size0) {
                    return false;
                }
                id0 = i0.get(it0++);
            }
            if (id0 == id1) {
                return true;
            }
            while (id0 > id1) {
                if (it1 == size1) {
                    return false;
                }
                id1 = i1.get(it1++);
            }
            if (id0 == id1) {
                return true;
            }
        }
    }

    private boolean isCovered3(int[] literals, int[] lIndex, int depth) {
        if (depth == literals.length - 1) {
            return true;
        }
        final VecInt i0 = indexedSolutions.get(MIGVisitorProvider.getVertexIndex(literals[depth]));
        final VecInt i1 = indexedSolutions.get(MIGVisitorProvider.getVertexIndex(literals[depth + 1]));
        int size0, size1;
        if ((size0 = i0.size()) == 0 || (size1 = i1.size()) == 0) {
            return false;
        }
        int it0 = lIndex[depth];
        int it1 = lIndex[depth + 1];
        int id0 = i0.get(it0++);
        int id1 = i1.get(it1++);
        while (true) {
            while (id0 > id1) {
                if (it1 == size1) {
                    return false;
                }
                id1 = i1.get(it1++);
            }
            if (id0 == id1) {
                lIndex[depth] = it0;
                lIndex[depth + 1] = it1;
                if (isCovered3(literals, lIndex, depth + 1)) {
                    return true;
                }
            }

            return false;
        }
    }

    private boolean isCovered(int[] literals) {
        return isCovered(literals, completeSolutionList) || isCovered(literals, incompleteSolutionList);
    }

    private boolean select(TWiseConfiguration3 solution, int[] literals) {
        final int lastIndex = solution.setLiteral(literals);
        for (int i = lastIndex; i < solution.visitor.modelCount; i++) {
            int vertexIndex = MIGVisitorProvider.getVertexIndex(solution.visitor.newLiterals[i]);
            VecInt indexList = indexedSolutions.get(vertexIndex);
            indexList.push(solution.id);
            Arrays.sort(indexList.toArray(), 0, indexList.size());
        }

        if (solution.isComplete()) {
            for (final Iterator<TWiseConfiguration3> iterator = incompleteSolutionList.iterator();
                    iterator.hasNext(); ) {
                if (iterator.next() == solution) {
                    iterator.remove();
                    completeSolutionList.add(solution);
                    break;
                }
            }
            return true;
        } else {
            solution.updateSolutionList(lastIndex);
            return false;
        }
    }

    private boolean firstCover(int[] literals) {
        candidateConfiguration.clear();
        configLoop:
        for (final TWiseConfiguration3 configuration : incompleteSolutionList) {
            final int[] literals2 = configuration.getLiterals();
            if (newConfiguration != null) {
                for (int i = 0; i < newConfiguration.visitor.modelCount; i++) {
                    final int l = newConfiguration.visitor.newLiterals[i];
                    if (literals2[Math.abs(l) - 1] == -l) {
                        continue configLoop;
                    }
                }
            } else {
                for (int i = 0; i < literals.length; i++) {
                    final int l = literals[i];
                    if (literals2[Math.abs(l) - 1] == -l) {
                        continue configLoop;
                    }
                }
            }
            if (isSelectionPossibleSol(configuration, literals)) {
                select(configuration, literals);
                //				if (!isValid(configuration)) {
                //					throw new RuntimeContradictionException(Arrays.toString(literals));
                //				}
                sortIncomplete();
                return true;
            }
            candidateConfiguration.add(configuration);
        }
        return false;
    }

    private void sortIncomplete() {
        Collections.sort(incompleteSolutionList, (a, b) -> b.countLiterals() - a.countLiterals());
    }

    private boolean isCombinationInvalidMIG(int[] literals) {
        if (newConfiguration != null) {
            newConfiguration.visitor.reset();
            try {
                newConfiguration.visitor.propagate(literals);
            } catch (RuntimeContradictionException e) {
                newConfiguration.visitor.reset();
                return true;
            }
        } else {
            try {
                newConfiguration = new TWiseConfiguration3(curSolutionId++, mig, randomSample, literals);
            } catch (RuntimeContradictionException e) {
                return true;
            }
        }
        return false;
    }

    private boolean isCombinationValidSample(int[] literals) {
        for (final LiteralList s : randomSample) {
            if (!s.hasConflicts(literals)) {
                return true;
            }
        }
        return false;
    }

    private boolean isCombinationInvalidSAT(int[] literals) {
        final int orgAssignmentLength = solver.getAssumptions().size();
        try {
            if (newConfiguration != null) {
                for (int i = 0; i < newConfiguration.visitor.modelCount; i++) {
                    solver.getAssumptions().push(newConfiguration.visitor.newLiterals[i]);
                }
            } else {
                for (int i = 0; i < literals.length; i++) {
                    solver.getAssumptions().push(literals[i]);
                }
            }
            final SatSolver.SatResult hasSolution = solver.hasSolution();
            switch (hasSolution) {
                case TRUE:
                    if (randomSample.size() == GLOBAL_SOLUTION_LIMIT) {
                        randomSample.removeFirst();
                    }
                    final int[] solution = solver.getInternalSolution();
                    final int[] copyOfSolution = Arrays.copyOf(solution, solution.length);
                    LiteralList e = new LiteralList(copyOfSolution, Order.INDEX, false);
                    for (TWiseConfiguration3 c : incompleteSolutionList) {
                        if (!c.hasConflicts(e)) {
                            c.solverSolutions.add(e);
                        }
                    }
                    randomSample.add(e);
                    solver.shuffleOrder(random);
                    return false;
                case FALSE:
                case TIMEOUT:
                    return true;
                default:
                    throw new IllegalStateException(String.valueOf(hasSolution));
            }
        } finally {
            solver.getAssumptions().clear(orgAssignmentLength);
        }
    }

    private boolean coverSat(int[] literals) {
        for (TWiseConfiguration3 configuration : candidateConfiguration) {
            if (trySelectSat(configuration, literals)) {
                sortIncomplete();
                //				if (!isValid(configuration)) {
                //					throw new RuntimeContradictionException(Arrays.toString(literals));
                //				}
                return true;
            }
        }
        return false;
    }

    private void newConfiguration(int[] literals) {
        if (newConfiguration == null) {
            newConfiguration = new TWiseConfiguration3(curSolutionId++, mig, randomSample, literals);
        }
        if (completeSolutionList.size() < maxSampleSize) {
            if (newConfiguration.isComplete()) {
                newConfiguration.clear();
                completeSolutionList.add(newConfiguration);
            } else {
                newConfiguration.updateSolutionList(randomSample);
                incompleteSolutionList.add(newConfiguration);
                sortIncomplete();
            }
            for (int i = 0; i < newConfiguration.visitor.modelCount; i++) {
                int vertexIndex = MIGVisitorProvider.getVertexIndex(newConfiguration.visitor.newLiterals[i]);
                VecInt indexList = indexedSolutions.get(vertexIndex);
                indexList.push(newConfiguration.id);
                Arrays.sort(indexList.toArray(), 0, indexList.size());
            }
        }
        newConfiguration = null;
    }

    public int getMaxSampleSize() {
        return maxSampleSize;
    }

    public void setMaxSampleSize(int maxSampleSize) {
        this.maxSampleSize = maxSampleSize;
    }

    public void setMIG(MIG mig) {
        this.mig = new MIGVisitorProvider(mig);
    }

    private LiteralList autoComplete(TWiseConfiguration3 configuration) {
        if (!configuration.isComplete()) {
            if (configuration.solverSolutions.size() > 0) {
                final int[] configuration2 =
                        configuration.solverSolutions.getFirst().getLiterals();
                return new LiteralList(Arrays.copyOf(configuration2, configuration2.length));
            }
            final int orgAssignmentSize = setUpSolver(configuration);
            try {
                SatResult hasSolution = solver.hasSolution();
                switch (hasSolution) {
                    case FALSE:
                        throw new RuntimeContradictionException();
                    case TIMEOUT:
                        throw new RuntimeTimeoutException();
                    case TRUE:
                        final int[] internalSolution = solver.getInternalSolution();
                        return new LiteralList(Arrays.copyOf(internalSolution, internalSolution.length));
                    default:
                        throw new IllegalStateException(String.valueOf(hasSolution));
                }
            } finally {
                solver.getAssumptions().clear(orgAssignmentSize);
            }
        } else {
            return new LiteralList(Arrays.copyOf(configuration.getLiterals(), configuration.getLiterals().length));
        }
    }

    public boolean isSelectionPossibleSol(TWiseConfiguration3 configuration, int[] literals) {
        for (LiteralList configuration2 : configuration.solverSolutions) {
            if (!configuration2.hasConflicts(literals)) {
                return true;
            }
        }
        return false;
    }

    public boolean trySelectSat(TWiseConfiguration3 configuration, final int[] literals) {
        final int oldModelCount = configuration.visitor.modelCount;
        try {
            configuration.visitor.propagate(literals);
        } catch (RuntimeException e) {
            configuration.visitor.reset(oldModelCount);
            return false;
        }

        final int orgAssignmentSize = setUpSolver(configuration);
        try {
            if (newConfiguration != null) {
                for (int i = 0; i < newConfiguration.visitor.modelCount; i++) {
                    int l = newConfiguration.visitor.newLiterals[i];
                    if (configuration.getLiterals()[Math.abs(l) - 1] == 0) {
                        solver.getAssumptions().push(l);
                    }
                }
            } else {
                for (int i = 0; i < literals.length; i++) {
                    int l = literals[i];
                    if (configuration.getLiterals()[Math.abs(l) - 1] == 0) {
                        solver.getAssumptions().push(l);
                    }
                }
            }
            SatResult hasSolution = solver.hasSolution();
            switch (hasSolution) {
                case FALSE:
                case TIMEOUT:
                    configuration.visitor.reset(oldModelCount);
                    return false;
                case TRUE:
                    if (randomSample.size() == GLOBAL_SOLUTION_LIMIT) {
                        randomSample.removeFirst();
                    }
                    final int[] solution = solver.getInternalSolution();
                    final int[] copyOfSolution = Arrays.copyOf(solution, solution.length);
                    LiteralList e = new LiteralList(copyOfSolution, Order.INDEX, false);
                    configuration.solverSolutions.add(e);
                    randomSample.add(e);
                    solver.shuffleOrder(random);
                    for (int i = oldModelCount; i < configuration.visitor.modelCount; i++) {
                        int vertexIndex = MIGVisitorProvider.getVertexIndex(configuration.visitor.newLiterals[i]);
                        VecInt indexList = indexedSolutions.get(vertexIndex);
                        indexList.push(configuration.id);
                        Arrays.sort(indexList.toArray(), 0, indexList.size());
                    }
                    configuration.updateSolutionList(oldModelCount);
                    return true;
                default:
                    throw new IllegalStateException(String.valueOf(hasSolution));
            }
        } finally {
            solver.getAssumptions().clear(orgAssignmentSize);
        }
    }

    public boolean isValid(TWiseConfiguration3 configuration) {
        final int orgAssignmentSize = setUpSolver(configuration);
        try {
            return solver.hasSolution() == SatSolver.SatResult.TRUE;
        } finally {
            solver.getAssumptions().clear(orgAssignmentSize);
        }
    }

    public int setUpSolver(TWiseConfiguration3 configuration) {
        final int orgAssignmentSize = solver.getAssumptions().size();
        for (int i = 0; i < configuration.visitor.modelCount; i++) {
            solver.getAssumptions().push(configuration.visitor.newLiterals[i]);
        }
        return orgAssignmentSize;
    }
}
