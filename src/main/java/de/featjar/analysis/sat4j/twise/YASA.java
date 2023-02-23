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
import de.featjar.analysis.mig.solver.MIGVisitorProvider.Visitor;
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
import de.featjar.clauses.solutions.combinations.BinomialCalculator;
import de.featjar.clauses.solutions.combinations.CombinationIterator;
import de.featjar.clauses.solutions.combinations.LexicographicIterator;
import de.featjar.util.data.Identifier;
import de.featjar.util.data.IntList;
import de.featjar.util.job.Executor;
import de.featjar.util.job.InternalMonitor;
import de.featjar.util.logging.Logger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.LongStream;

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

    private class PartialConfiguration extends LiteralList {

        private static final long serialVersionUID = -1L;

        private final int id;

        private Visitor visitor;

        private ArrayDeque<LiteralList> solverSolutions;

        public PartialConfiguration(PartialConfiguration config) {
            super(config);
            id = config.id;
            visitor = config.visitor.getVisitorProvider().new Visitor(config.visitor, literals);
            solverSolutions = config.solverSolutions != null ? new ArrayDeque<>(config.solverSolutions) : null;
        }

        public PartialConfiguration(int id, MIGVisitorProvider mig, int... newliterals) {
            super(new int[mig.size()], Order.INDEX, false);
            this.id = id;
            visitor = mig.getVisitor(this.literals);
            solverSolutions = new ArrayDeque<>();
            visitor.propagate(newliterals);
        }

        public void updateSolutionList(ArrayDeque<LiteralList> solverSolutions) {
            solutionLoop:
            for (LiteralList solution : solverSolutions) {
                final int[] solverSolutionLiterals = solution.getLiterals();
                for (int j = 0; j < visitor.modelCount; j++) {
                    int l = visitor.newLiterals[j];
                    final int k = Math.abs(l) - 1;
                    if (solverSolutionLiterals[k] != l) {
                        continue solutionLoop;
                    }
                }
                this.solverSolutions.add(solution);
            }
        }

        public void updateSolutionList(int lastIndex) {
            if (!isComplete()) {
                for (int i = lastIndex; i < visitor.modelCount; i++) {
                    final int newLiteral = visitor.newLiterals[i];
                    final int k = Math.abs(newLiteral) - 1;
                    for (Iterator<LiteralList> it = solverSolutions.iterator(); it.hasNext(); ) {
                        final int[] solverSolutionLiterals = it.next().getLiterals();
                        if (solverSolutionLiterals[k] != newLiteral) {
                            it.remove();
                        }
                    }
                }
            }
        }

        public int setLiteral(int... literals) {
            final int oldModelCount = visitor.modelCount;
            visitor.propagate(literals);
            return oldModelCount;
        }

        public void clear() {
            solverSolutions = null;
        }

        public boolean isComplete() {
            return visitor.modelCount == numberOfVariableLiterals;
        }

        public int countLiterals() {
            return visitor.modelCount;
        }
    }

    public static final int DEFAULT_ITERATIONS = 1;
    public static final int DEFAULT_T = 2;
    public static final int GLOBAL_SOLUTION_LIMIT = 100_000;

    private List<List<LiteralList>> nodes;
    private ArrayDeque<LiteralList> randomSample;

    private int maxSampleSize = Integer.MAX_VALUE;
    private int iterations = DEFAULT_ITERATIONS;
    private int t = DEFAULT_T;

    private ArrayList<IntList> indexedSolutions;
    private ArrayList<IntList> indexedBestSolutions;
    private ArrayList<PartialConfiguration> solutionList;
    private ArrayList<PartialConfiguration> bestResult;
    private final ArrayDeque<PartialConfiguration> candidateConfiguration = new ArrayDeque<>();
    private IntList[] selectedIndexedSolutions;

    private PartialConfiguration newConfiguration;
    private int curSolutionId;
    private long maxCombinationIndex;
    private int numberOfVariableLiterals;

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

    public void setT(int t) {
        if (t < 1) {
            throw new IllegalArgumentException(String.valueOf(t));
        }
        this.t = t;
    }

    public void setNodes(List<List<LiteralList>> nodes) {
        this.nodes = nodes;
    }

    public void setIterations(int iterations) {
        this.iterations = iterations;
    }

    public void setMaxSampleSize(int maxSampleSize) {
        this.maxSampleSize = maxSampleSize;
    }

    public void setMIG(MIG mig) {
        this.mig = new MIGVisitorProvider(mig);
    }

    @Override
    protected void init(InternalMonitor monitor) {
        cnf = solver.getCnf();
        solver.rememberSolutionHistory(0);
        solver.setSelectionStrategy(SStrategy.random(random));
        curSolutionId = 0;
        selectedIndexedSolutions = new IntList[t];

        if (nodes == null) {
            nodes = convertLiterals(LiteralList.getLiterals(cnf));
        }
        randomSample = new ArrayDeque<>(GLOBAL_SOLUTION_LIMIT);

        final MIGBuilder migBuilder = new RegularMIGBuilder();
        migBuilder.setCheckRedundancy(false);
        migBuilder.setDetectStrong(false);
        mig = new MIGVisitorProvider(Executor.run(migBuilder, solver.getCnf()).get());
        core = new LiteralList(mig.getCore(), Order.INDEX);
        numberOfVariableLiterals = cnf.getVariableMap().getVariableCount() - core.countNonNull();

        expressionLoop:
        for (final List<LiteralList> clauses : nodes) {
            final List<LiteralList> newClauses = new ArrayList<>(clauses.size());
            for (final LiteralList clause : clauses) {
                // If clause can be satisfied
                if (!core.hasConflicts(clause)) {
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

        maxCombinationIndex = BinomialCalculator.computeBinomial(presenceConditions.size(), t);
        monitor.setTotalWork(iterations * maxCombinationIndex);
        monitor.setStatusReporter(new Supplier<>() {
            @Override
            public String get() {
                return String.valueOf(solutionList.size());
            }
        });

        solutionList = new ArrayList<>();
        buildCombinations(monitor, 0);
        Logger.logDebug(solutionList.size() + " (" + bestResult.size() + ")");
        for (int i = 1; i < iterations; i++) {
            trimConfigurations(i);
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

    private void trimConfigurations(int iteration) {
        final int indexSize = 2 * mig.size();
        if (indexedBestSolutions == null) {
            indexedBestSolutions = new ArrayList<>(indexSize);
            for (int i = 0; i < indexSize; i++) {
                indexedBestSolutions.add(new IntList());
            }
            for (PartialConfiguration solution : bestResult) {
                addIndexBestSolutions(solution);
            }
            for (IntList indexList : indexedBestSolutions) {
                indexList.sort();
            }
        }

        indexedSolutions = new ArrayList<>(indexSize);
        for (int i = 0; i < indexSize; i++) {
            indexedSolutions.add(new IntList());
        }

        final long[] normConfigValues = getConfigScores(solutionList);

        long[] normConfigValuesSorted = Arrays.copyOf(normConfigValues, normConfigValues.length);
        Arrays.sort(normConfigValuesSorted);
        final int meanSearch = Arrays.binarySearch(normConfigValuesSorted, (long)
                LongStream.of(normConfigValues).average().getAsDouble());
        final int meanIndex = meanSearch >= 0 ? meanSearch : -meanSearch - 1;
        final long reference = normConfigValuesSorted[
                (int) (normConfigValues.length
                        - ((normConfigValues.length - meanIndex) * ((double) iteration / iterations)))];

        ArrayList<PartialConfiguration> newSolutionList = new ArrayList<>(solutionList.size());
        int index = 0;
        for (PartialConfiguration solution : solutionList) {
            if (normConfigValues[index++] >= reference) {
                addIndexSolutions(solution);
                newSolutionList.add(new PartialConfiguration(solution));
            }
        }
        solutionList = newSolutionList;

        for (IntList indexList : indexedSolutions) {
            indexList.sort();
        }
    }

    private long[] getConfigScores(List<PartialConfiguration> sample) {
        final int configLength = sample.size();

        final int n = cnf.getVariableMap().getVariableCount();
        final int t2 = (n < t) ? n : t;
        final int n2 = n - t2;
        final int pow = (int) Math.pow(2, t2);

        final long[][] configScores = new long[pow][configLength];

        int[] sampleIndex0 = IntStream.range(0, configLength).toArray();
        IntStream.range(0, pow) //
                .parallel() //
                .forEach(maskIndex -> {
                    long[] configScore = configScores[maskIndex];
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

                        for (int k = liSample; k < t2; k++) {
                            final int index = c[k];
                            final int literalValue = literals[k];
                            int[] sampleIndex1 = sampleIndex[k];
                            int[] sampleIndex2 = sampleIndex[k + 1];

                            int sindex2 = 0;
                            for (int sindex1 : sampleIndex1) {
                                if (sindex1 == -1 || sindex1 >= configLength) {
                                    break;
                                }
                                int[] config = sample.get(sindex1).getLiterals();
                                if (config[index] == literalValue) {
                                    sampleIndex2[sindex2++] = sindex1;
                                }
                            }
                            if (sindex2 < sampleIndex2.length) {
                                sampleIndex2[sindex2] = -1;
                            }
                        }
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

                        final double s = count == 1 ? 1 : 0;
                        for (int l = 0; l < count; l++) {
                            configScore[sampleIndexK[l]] += s;
                        }

                        i = t2 - 1;
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
        final long[] configScore = configScores[0];
        for (int j = 1; j < pow; j++) {
            final long[] configScoreJ = configScores[j];
            for (int k = 1; k < configLength; k++) {
                configScore[k] += configScoreJ[k];
            }
        }
        for (final LiteralList configuration : sample) {
            int count = 0;
            for (final int literal : configuration.getLiterals()) {
                if (literal != 0) {
                    count++;
                }
            }
            double factor = Math.pow((2.0 - (((double) count) / configuration.size())), t);
            configScore[confIndex] = (long) Math.round(configScore[confIndex] * factor);
            confIndex++;
        }

        return configScore;
    }

    private void buildCombinations(InternalMonitor monitor, int phase) {
        // TODO Variation Point: Combination order
        shuffleSort();
        final CombinationIterator it = new LexicographicIterator(t, presenceConditions.size());

        final int[] literals = new int[presenceConditions.size()];
        for (int i1 = 0; i1 < literals.length; i1++) {
            literals[i1] = presenceConditions.get(i1).get(0).getLiterals()[0];
        }

        final int[] combinationLiterals = new int[t];

        if (phase == 0) {
            final int indexSize = 2 * mig.size();
            indexedSolutions = new ArrayList<>(indexSize);
            for (int i2 = 0; i2 < indexSize; i2++) {
                indexedSolutions.add(new IntList());
            }
            for (int[] next = it.next(); next != null; next = it.next()) {
                monitor.step();
                for (int i = 0; i < next.length; i++) {
                    combinationLiterals[i] = literals[next[i]];
                }

                if (isCovered(combinationLiterals, indexedSolutions)) {
                    continue;
                }
                if (isCombinationInvalidMIG(combinationLiterals)) {
                    continue;
                }

                if (isCombinationValidSample(combinationLiterals)) {
                    if (firstCover(combinationLiterals)) {
                        continue;
                    }
                } else {
                    if (isCombinationInvalidSAT(combinationLiterals)) {
                        continue;
                    }
                    addToCandidateList(combinationLiterals);
                }
                //				if (firstCover(combinationLiterals)) {
                //					continue;
                //				}
                //				if (!isCombinationValidSample(combinationLiterals) &&
                // isCombinationInvalidSAT(combinationLiterals)) {
                //					continue;
                //				}

                if (coverSat(combinationLiterals)) {
                    continue;
                }
                newConfiguration(combinationLiterals);
            }
            bestResult = solutionList;
        } else {
            long remainingCombinations = maxCombinationIndex;
            for (int[] next = it.next(); next != null; next = it.next()) {
                monitor.step();
                remainingCombinations--;
                for (int i = 0; i < next.length; i++) {
                    combinationLiterals[i] = literals[next[i]];
                }

                if (isCovered(combinationLiterals, indexedSolutions)) {
                    continue;
                }
                if (!isCovered(combinationLiterals, indexedBestSolutions)) {
                    continue;
                }
                if (firstCover(combinationLiterals)) {
                    continue;
                }
                if (coverSat(combinationLiterals)) {
                    continue;
                }
                if (solutionList.size() == bestResult.size()) {
                    monitor.step(remainingCombinations);
                    break;
                }
                newConfiguration(combinationLiterals);
            }
            if (bestResult.size() > solutionList.size()) {
                bestResult = solutionList;
            }
        }
    }

    private void addIndexBestSolutions(PartialConfiguration solution) {
        final int[] literals = solution.getLiterals();
        for (int i = 0; i < literals.length; i++) {
            final int literal = literals[i];
            if (literal != 0) {
                final int vertexIndex = MIGVisitorProvider.getVertexIndex(literal);
                IntList indexList = indexedBestSolutions.get(vertexIndex);
                indexList.add(solution.id);
            }
        }
    }

    private void addIndexSolutions(PartialConfiguration solution) {
        final int[] literals = solution.getLiterals();
        for (int i = 0; i < literals.length; i++) {
            final int literal = literals[i];
            if (literal != 0) {
                final int vertexIndex = MIGVisitorProvider.getVertexIndex(literal);
                IntList indexList = indexedSolutions.get(vertexIndex);
                indexList.add(solution.id);
            }
        }
    }

    private boolean isCovered(int[] literals, ArrayList<IntList> indexedSolutions) {
        if (t < 2) {
            return !indexedSolutions
                    .get(MIGVisitorProvider.getVertexIndex(literals[0]))
                    .isEmpty();
        }
        for (int i = 0; i < t; i++) {
            final IntList indexedSolution = indexedSolutions.get(MIGVisitorProvider.getVertexIndex(literals[i]));
            if (indexedSolution.size() == 0) {
                return false;
            }
            selectedIndexedSolutions[i] = indexedSolution;
        }
        Arrays.sort(selectedIndexedSolutions, (a, b) -> a.size() - b.size());
        final int[] ix = new int[t - 1];

        final IntList i0 = selectedIndexedSolutions[0];
        final int[] ia0 = i0.toArray();
        loop:
        for (int i = 0; i < i0.size(); i++) {
            int id0 = ia0[i];
            for (int j = 1; j < t; j++) {
                final IntList i1 = selectedIndexedSolutions[j];
                int binarySearch = Arrays.binarySearch(i1.toArray(), ix[j - 1], i1.size(), id0);
                if (binarySearch < 0) {
                    ix[j - 1] = -binarySearch - 1;
                    continue loop;
                } else {
                    ix[j - 1] = binarySearch;
                }
            }
            return true;
        }
        return false;
    }

    private void select(PartialConfiguration solution, int[] literals) {
        final int lastIndex = solution.setLiteral(literals);
        for (int i = lastIndex; i < solution.visitor.modelCount; i++) {
            IntList indexList =
                    indexedSolutions.get(MIGVisitorProvider.getVertexIndex(solution.visitor.newLiterals[i]));
            final int idIndex = Arrays.binarySearch(indexList.toArray(), 0, indexList.size(), solution.id);
            if (idIndex < 0) {
                indexList.add(solution.id, -(idIndex + 1));
            }
        }
        solution.updateSolutionList(lastIndex);
    }

    private boolean firstCover(int[] literals) {
        candidateConfiguration.clear();
        if (newConfiguration != null) {
            configLoop:
            for (final PartialConfiguration configuration : solutionList) {
                if (!configuration.isComplete()) {
                    final int[] literals2 = configuration.getLiterals();
                    for (int i = 0; i < newConfiguration.visitor.modelCount; i++) {
                        final int l = newConfiguration.visitor.newLiterals[i];
                        if (literals2[Math.abs(l) - 1] == -l) {
                            continue configLoop;
                        }
                    }
                    if (isSelectionPossibleSol(configuration, literals)) {
                        select(configuration, literals);
                        change(configuration);
                        return true;
                    }
                    candidateConfiguration.add(configuration);
                }
            }
        } else {
            configLoop:
            for (final PartialConfiguration configuration : solutionList) {
                if (!configuration.isComplete()) {
                    final int[] literals2 = configuration.getLiterals();
                    for (int i = 0; i < literals.length; i++) {
                        final int l = literals[i];
                        if (literals2[Math.abs(l) - 1] == -l) {
                            continue configLoop;
                        }
                    }
                    if (isSelectionPossibleSol(configuration, literals)) {
                        select(configuration, literals);
                        change(configuration);
                        return true;
                    }
                    candidateConfiguration.add(configuration);
                }
            }
        }
        return false;
    }

    private void addToCandidateList(int[] literals) {
        candidateConfiguration.clear();
        if (newConfiguration != null) {
            configLoop:
            for (final PartialConfiguration configuration : solutionList) {
                if (!configuration.isComplete()) {
                    final int[] literals2 = configuration.getLiterals();
                    for (int i = 0; i < newConfiguration.visitor.modelCount; i++) {
                        final int l = newConfiguration.visitor.newLiterals[i];
                        if (literals2[Math.abs(l) - 1] == -l) {
                            continue configLoop;
                        }
                    }
                    candidateConfiguration.add(configuration);
                }
            }
        } else {
            configLoop:
            for (final PartialConfiguration configuration : solutionList) {
                if (!configuration.isComplete()) {
                    final int[] literals2 = configuration.getLiterals();
                    for (int i = 0; i < literals.length; i++) {
                        final int l = literals[i];
                        if (literals2[Math.abs(l) - 1] == -l) {
                            continue configLoop;
                        }
                    }
                    candidateConfiguration.add(configuration);
                }
            }
        }
    }

    private void change(final PartialConfiguration configuration) {
        if (configuration.isComplete()) {
            configuration.clear();
        }
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
                newConfiguration = new PartialConfiguration(curSolutionId++, mig, literals);
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
                    final LiteralList e = addSolverSolution();

                    PartialConfiguration compatibleConfiguration = null;
                    for (PartialConfiguration c : candidateConfiguration) {
                        if (!c.hasConflicts(e)) {
                            c.solverSolutions.add(e);
                            if (compatibleConfiguration == null) {
                                compatibleConfiguration = c;
                            }
                        }
                    }
                    if (compatibleConfiguration != null) {
                        select(compatibleConfiguration, literals);
                        change(compatibleConfiguration);
                        return true;
                    }
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
        for (PartialConfiguration configuration : candidateConfiguration) {
            if (trySelectSat(configuration, literals)) {
                change(configuration);
                return true;
            }
        }
        return false;
    }

    private void newConfiguration(int[] literals) {
        if (solutionList.size() < maxSampleSize) {
            if (newConfiguration == null) {
                newConfiguration = new PartialConfiguration(curSolutionId++, mig, literals);
            }
            newConfiguration.updateSolutionList(randomSample);
            solutionList.add(newConfiguration);
            change(newConfiguration);
            for (int i = 0; i < newConfiguration.visitor.modelCount; i++) {
                IntList indexList = indexedSolutions.get(
                        MIGVisitorProvider.getVertexIndex(newConfiguration.visitor.newLiterals[i]));
                indexList.add(newConfiguration.id);
            }
        }
        newConfiguration = null;
    }

    private void autoComplete(PartialConfiguration configuration) {
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
        }
    }

    private boolean isSelectionPossibleSol(PartialConfiguration configuration, int[] literals) {
        for (LiteralList configuration2 : configuration.solverSolutions) {
            if (!configuration2.hasConflicts(literals)) {
                return true;
            }
        }
        return false;
    }

    private boolean trySelectSat(PartialConfiguration configuration, final int[] literals) {
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
                    final LiteralList e = addSolverSolution();
                    configuration.solverSolutions.add(e);
                    for (int i = oldModelCount; i < configuration.visitor.modelCount; i++) {
                        IntList indexList = indexedSolutions.get(
                                MIGVisitorProvider.getVertexIndex(configuration.visitor.newLiterals[i]));
                        final int idIndex =
                                Arrays.binarySearch(indexList.toArray(), 0, indexList.size(), configuration.id);
                        if (idIndex < 0) {
                            indexList.add(configuration.id, -(idIndex + 1));
                        }
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

    private LiteralList addSolverSolution() {
        if (randomSample.size() == GLOBAL_SOLUTION_LIMIT) {
            randomSample.removeFirst();
        }
        final int[] solution = solver.getInternalSolution();
        final LiteralList e = new LiteralList(Arrays.copyOf(solution, solution.length), Order.INDEX, false);
        randomSample.add(e);
        solver.shuffleOrder(random);
        return e;
    }

    private int setUpSolver(PartialConfiguration configuration) {
        final int orgAssignmentSize = solver.getAssumptions().size();
        for (int i = 0; i < configuration.visitor.modelCount; i++) {
            solver.getAssumptions().push(configuration.visitor.newLiterals[i]);
        }
        return orgAssignmentSize;
    }
}
