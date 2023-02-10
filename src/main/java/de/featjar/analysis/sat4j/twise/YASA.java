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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
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

    protected int t;

    protected List<List<LiteralList>> nodes;
    private List<TWiseConfiguration3> bestResult = null;
    private ArrayDeque<LiteralList> randomSample;

    private int maxSampleSize = Integer.MAX_VALUE;

    private List<VecInt> indexedSolutions;
    private List<VecInt> indexedBestSolutions;
    private List<TWiseConfiguration3> solutionList = new ArrayList<>();
    private final ArrayList<TWiseConfiguration3> candidateConfiguration = new ArrayList<>();
    private TWiseConfiguration3 newConfiguration;
    private int curSolutionId;

    private MIGVisitorProvider mig;
    private LiteralList core;
    private CNF cnf;

    private final List<List<LiteralList>> presenceConditions = new ArrayList<>();

    public void shuffleSort() {
        final Map<Integer, List<List<LiteralList>>> groupedPCs =
                presenceConditions.stream().collect(Collectors.groupingBy(List::size));
        for (final List<List<LiteralList>> pcList : groupedPCs.values()) {
            Collections.shuffle(pcList, random);
        }
        final List<Entry<Integer, List<List<LiteralList>>>> shuffledPCs = new ArrayList<>(groupedPCs.entrySet());
        Collections.sort(shuffledPCs, (a, b) -> a.getKey() - b.getKey());
        presenceConditions.clear();
        for (final Entry<Integer, List<List<LiteralList>>> entry : shuffledPCs) {
            presenceConditions.addAll(entry.getValue());
        }
    }

    public int getT() {
        return t;
    }

    public void setT(int t) {
        this.t = t;
    }

    public void setNodes(List<List<LiteralList>> nodes) {
        this.nodes = nodes;
    }

    public int getIterations() {
        return iterations;
    }

    public void setIterations(int iterations) {
        this.iterations = iterations;
    }

    @Override
    protected void init(InternalMonitor monitor) {
        cnf = solver.getCnf();
        solver.rememberSolutionHistory(0);
        solver.setSelectionStrategy(SStrategy.random(random));

        if (nodes == null) {
            nodes = convertLiterals(LiteralList.getLiterals(cnf));
        }

        randomSample = new ArrayDeque<>(GLOBAL_SOLUTION_LIMIT);

        final MIGBuilder migBuilder = new RegularMIGBuilder();
        migBuilder.setCheckRedundancy(false);
        migBuilder.setDetectStrong(false);
        mig = new MIGVisitorProvider(Executor.run(migBuilder, solver.getCnf()).get());

        // TODO Variation Point: Sorting Nodes
        core = new LiteralList(mig.getCore(), Order.INDEX);

        expressionLoop:
        for (final List<LiteralList> clauses : nodes) {
            final List<LiteralList> newClauses = new ArrayList<>(clauses.size());
            for (final LiteralList clause : clauses) {
                // If clause can be satisfied
                if (!clause.hasConflicts(core)) {
                    // If clause is already satisfied
                    if (core.containsAll(clause)) {
                        continue expressionLoop;
                    } else {
                        newClauses.add(clause.clone());
                    }
                }
            }
            if (!newClauses.isEmpty()) {
                Collections.sort(newClauses, (o1, o2) -> o1.size() - o2.size());
                presenceConditions.add(newClauses);
            }
        }

        monitor.setTotalWork(iterations
                * new BinomialCalculator(t, presenceConditions.size()).binomial(presenceConditions.size(), t));
        monitor.setStatusReporter(new Supplier<>() {
            @Override
            public String get() {
                return String.valueOf(solutionList.size());
            }
        });

        curSolutionId = 0;
        buildCombinations(monitor, 0);
        Logger.logDebug(solutionList.size() + " (" + bestResult.size() + ")");
        for (int i = 1; i < iterations; i++) {
            trimConfigurations();
            buildCombinations(monitor, i);
            Logger.logDebug(solutionList.size() + " (" + bestResult.size() + ")");
        }
        bestResult.forEach(this::autoComplete);
        Collections.reverse(bestResult);
    }

    @Override
    public LiteralList get() {
        return bestResult.isEmpty() ? null : bestResult.remove(bestResult.size() - 1);
    }

    private void trimConfigurations() {
        final int initialCapacity = 2 * mig.size();
        if (indexedBestSolutions == null) {
            indexedBestSolutions = new ArrayList<>(initialCapacity);
            for (int i = 0; i < initialCapacity; i++) {
                indexedBestSolutions.add(new VecInt());
            }
            for (TWiseConfiguration3 solution : bestResult) {
                addIndexBestSolutions(solution);
            }
            for (VecInt indexList : indexedBestSolutions) {
                Arrays.sort(indexList.toArray(), 0, indexList.size());
            }
        }

        solutionList = new ArrayList<>(solutionList.size());
        indexedSolutions = new ArrayList<>(initialCapacity);
        for (int i = 0; i < initialCapacity; i++) {
            indexedSolutions.add(new VecInt());
        }

        final double[] normConfigValues = getConfigScores(bestResult);
        final double reference =
                Arrays.stream(normConfigValues).filter(n -> n > 0).average().getAsDouble();

        int index = 0;
        for (TWiseConfiguration3 solution : bestResult) {
            if (normConfigValues[index++] >= reference) {
                addIndexSolutions(solution);
                solutionList.add(new TWiseConfiguration3(solution));
            }
        }

        for (VecInt indexList : indexedSolutions) {
            Arrays.sort(indexList.toArray(), 0, indexList.size());
        }
    }

    public double[] getConfigScores(List<TWiseConfiguration3> sample) {
        final int configLength = sample.size();
        final double[] configScore = new double[configLength];

        final int n = cnf.getVariableMap().getVariableCount();
        final int t2 = (n < t) ? n : t;
        final int n2 = n - t2;
        final int pow = (int) Math.pow(2, t2);

        boolean[][] masks = new boolean[pow][t2];
        for (int i = 0; i < masks.length; i++) {
            boolean[] p = masks[i];
            for (int j = 0; j < t2; j++) {
                p[j] = (i >> j & 1) == 0;
            }
        }

        int[] sampleIndex0 = IntStream.range(0, configLength).toArray();
        IntStream.range(0, pow) //
                .parallel() //
                .forEach(maskIndex -> {
                    boolean[] mask = new boolean[t2];
                    for (int j = 0; j < t2; j++) {
                        mask[j] = (maskIndex >> j & 1) == 0;
                    }

                    int[][] sampleIndex = new int[t2 + 1][];
                    sampleIndex[0] = sampleIndex0;
                    for (int i = 1; i < sampleIndex.length; i++) {
                        sampleIndex[i] = new int[configLength];
                    }

                    int[] literals = new int[t2];
                    int liSample = 0;

                    final int[] c = new int[t2];
                    for (int i = 0; i < t2; i++) {
                        c[i] = i;
                    }
                    int i = 0;

                    combinationLoop:
                    while (true) {

                        liSample = Math.min(liSample, i);

                        for (int k = 0; k < t2; k++) {
                            int literal = mask[k] ? (c[k] + 1) : -(c[k] + 1);
                            if (core.containsAnyVariable(literal)) {
                                i = k;
                                for (; i >= 0; i--) {
                                    final int ci = ++c[i];
                                    if (ci < (n2 + i)) {
                                        break;
                                    }
                                }
                                if (i == -1) {
                                    break combinationLoop;
                                }
                                for (int j = i + 1; j < t2; j++) {
                                    c[j] = c[j - 1] + 1;
                                }
                                continue combinationLoop;
                            }
                            literals[k] = literal;
                        }

                        final int t3 = t2 - 1;

                        {
                            extracted(literals, sampleIndex, c, t2, sample, liSample, configLength);
                            liSample = i;

                            final int[] sampleIndexK = sampleIndex[t2];

                            int count = 0;
                            for (int l = 0; l < sampleIndexK.length; l++) {
                                int j = sampleIndexK[l];
                                if (j < 0) {
                                    count = l;
                                    break;
                                }
                            }
                            //							final double s = 1.0 / count;
                            final double s = count == 1 ? 1 : 0;
                            for (int l = 0; l < count; l++) {
                                configScore[sampleIndexK[l]] += s;
                            }
                        }

                        i = t3;
                        for (; i >= 0; i--) {
                            final int ci = ++c[i];
                            if (ci < (n2 + i)) {
                                break;
                            }
                        }

                        if (i == -1) {
                            break;
                        }
                        for (int j = i + 1; j < t2; j++) {
                            c[j] = c[j - 1] + 1;
                        }
                    }
                });

        int confIndex = 0;
        for (final LiteralList configuration : sample) {
            int count = 0;
            for (final int literal : configuration.getLiterals()) {
                if (literal != 0) {
                    count++;
                }
            }
            final double d = ((double) count) / configuration.size();
            configScore[confIndex++] *= Math.pow((2 - d), 2);
        }

        return configScore;
    }

    private void extracted(
            int[] literals,
            int[][] sampleIndex,
            final int[] c,
            final int t3,
            List<TWiseConfiguration3> configurations,
            int ci,
            int configLength) {
        for (int k = ci; k < t3; k++) {
            final int index = c[k];
            final int literalValue = literals[k];
            int[] sampleIndex1 = sampleIndex[k];
            int[] sampleIndex2 = sampleIndex[k + 1];

            int sindex2 = 0;
            for (int sindex1 : sampleIndex1) {
                if (sindex1 == -1) {
                    break;
                }
                if (sindex1 >= configLength) {
                    break;
                }
                int[] config = configurations.get(sindex1).getLiterals();
                if (config[index] == literalValue) {
                    sampleIndex2[sindex2++] = sindex1;
                }
            }
            if (sindex2 < sampleIndex2.length) {
                sampleIndex2[sindex2] = -1;
            }
        }
    }

    private void buildCombinations(InternalMonitor monitor, int phase) {
        final int initialCapacity = 2 * mig.size();
        final int[] combinationLiterals = new int[t];
        final int[] literals = new int[presenceConditions.size()];
        shuffleSort();
        // TODO Variation Point: Combination order
        final ACombinationIterator it;
        switch (phase) {
            case 0:
                it = new LexicographicIterator(t, presenceConditions.size());
                break;
            case 1:
                it = new LexicographicIterator(t, presenceConditions.size());
                break;
            default:
                //			 it = new RandomPartitionIterator(t, presenceConditions.size());
                //			 it = new InverseLexicographicIterator(t, presenceConditions.size());
                it = new LexicographicIterator(t, presenceConditions.size());
                break;
        }

        for (int i1 = 0; i1 < literals.length; i1++) {
            literals[i1] = presenceConditions.get(i1).get(0).getLiterals()[0];
        }

        if (phase == 0) {
            indexedSolutions = new ArrayList<>(initialCapacity);
            for (int i2 = 0; i2 < initialCapacity; i2++) {
                indexedSolutions.add(new VecInt());
            }
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
            bestResult = solutionList;
        } else {
            for (int[] next = it.next(); next != null; next = it.next()) {
                monitor.step();
                for (int i = 0; i < next.length; i++) {
                    combinationLiterals[i] = literals[next[i]];
                }

                if (isCovered2(combinationLiterals)) {
                    continue;
                }
                if (!isCoveredBestResult2(combinationLiterals)) {
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
            if (bestResult.size() > solutionList.size()) {
                bestResult = solutionList;
            }
        }
    }

    private void addIndexBestSolutions(TWiseConfiguration3 solution) {
        final int[] literals = solution.getLiterals();
        for (int i = 0; i < literals.length; i++) {
            final int literal = literals[i];
            if (literal != 0) {
                final int vertexIndex = MIGVisitorProvider.getVertexIndex(literal);
                VecInt indexList = indexedBestSolutions.get(vertexIndex);
                indexList.push(solution.id);
            }
        }
    }

    private void addIndexSolutions(TWiseConfiguration3 solution) {
        final int[] literals = solution.getLiterals();
        for (int i = 0; i < literals.length; i++) {
            final int literal = literals[i];
            if (literal != 0) {
                final int vertexIndex = MIGVisitorProvider.getVertexIndex(literal);
                VecInt indexList = indexedSolutions.get(vertexIndex);
                indexList.push(solution.id);
            }
        }
    }

    private boolean isCoveredBestResult2(int[] literals) {
        final VecInt i0 = indexedBestSolutions.get(MIGVisitorProvider.getVertexIndex(literals[0]));
        final VecInt i1 = indexedBestSolutions.get(MIGVisitorProvider.getVertexIndex(literals[1]));
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

    private void select(TWiseConfiguration3 solution, int[] literals) {
        final int lastIndex = solution.setLiteral(literals);
        for (int i = lastIndex; i < solution.visitor.modelCount; i++) {
            int vertexIndex = MIGVisitorProvider.getVertexIndex(solution.visitor.newLiterals[i]);
            VecInt indexList = indexedSolutions.get(vertexIndex);
            indexList.push(solution.id);
            Arrays.sort(indexList.toArray(), 0, indexList.size());
        }
        solution.updateSolutionList(lastIndex);
    }

    private boolean firstCover(int[] literals) {
        candidateConfiguration.clear();
        configLoop:
        for (final TWiseConfiguration3 configuration : solutionList) {
            if (!configuration.isComplete()) {
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
                    sortIncomplete();
                    return true;
                }
                candidateConfiguration.add(configuration);
            }
        }
        return false;
    }

    private void sortIncomplete() {
        Collections.sort(solutionList, (a, b) -> b.countLiterals() - a.countLiterals());
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
                    for (TWiseConfiguration3 c : solutionList) {
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
                return true;
            }
        }
        return false;
    }

    private void newConfiguration(int[] literals) {
        if (newConfiguration == null) {
            newConfiguration = new TWiseConfiguration3(curSolutionId++, mig, randomSample, literals);
        }
        if (solutionList.size() < maxSampleSize) {
            newConfiguration.updateSolutionList(randomSample);
            solutionList.add(newConfiguration);
            sortIncomplete();
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

    private void autoComplete(TWiseConfiguration3 configuration) {
        if (!configuration.isComplete()) {
            if (configuration.solverSolutions.size() > 0) {
                final int[] configuration2 =
                        configuration.solverSolutions.getFirst().getLiterals();
                System.arraycopy(configuration2, 0, configuration.getLiterals(), 0, configuration.size());
                configuration.clear();
            } else {
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
                            System.arraycopy(internalSolution, 0, configuration.getLiterals(), 0, configuration.size());
                            configuration.clear();
                            break;
                        default:
                            throw new IllegalStateException(String.valueOf(hasSolution));
                    }
                } finally {
                    solver.getAssumptions().clear(orgAssignmentSize);
                }
            }
            //		} else {
            //			return new LiteralList(Arrays.copyOf(configuration.getLiterals(), configuration.getLiterals().length));
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
