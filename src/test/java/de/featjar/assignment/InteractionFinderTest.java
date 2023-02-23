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
package de.featjar.assignment;

import de.featjar.analysis.mig.solver.MIG;
import de.featjar.analysis.mig.solver.MIGProvider;
import de.featjar.analysis.mig.solver.Vertex;
import de.featjar.analysis.sat4j.AtomicSetAnalysis;
import de.featjar.analysis.sat4j.ConfigurationCompletor;
import de.featjar.analysis.sat4j.FastRandomConfigurationGenerator;
import de.featjar.analysis.sat4j.RandomConfigurationGenerator;
import de.featjar.clauses.CNF;
import de.featjar.clauses.CNFProvider;
import de.featjar.clauses.Clauses;
import de.featjar.clauses.LiteralList;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.clauses.solutions.analysis.InteractionFinder;
import de.featjar.clauses.solutions.analysis.InteractionFinderAtLeastOne;
import de.featjar.clauses.solutions.analysis.InteractionFinderCombinationForward;
import de.featjar.formula.ModelRepresentation;
import de.featjar.formula.structure.AuxiliaryRoot;
import de.featjar.formula.structure.Formula;
import de.featjar.formula.structure.atomic.Atomic;
import de.featjar.formula.structure.atomic.literal.BooleanLiteral;
import de.featjar.formula.structure.atomic.literal.VariableMap;
import de.featjar.formula.structure.compound.Compound;
import de.featjar.formula.structure.compound.Or;
import de.featjar.formula.structure.transform.VariableMapSetter;
import de.featjar.util.extension.ExtensionLoader;
import de.featjar.util.io.csv.CSVWriter;
import de.featjar.util.job.NullMonitor;
import de.featjar.util.logging.Logger;
import de.featjar.util.tree.Trees;
import de.featjar.util.tree.visitor.TreeVisitor;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.function.Predicate;
import java.util.stream.Stream;

public class InteractionFinderTest {

    static {
        ExtensionLoader.load();
    }

    private static final Random randomSeed = new Random(314159);
    private static final int maxInteractionSize = 3;
    private static final int iterations = 100;
    private static final boolean computeAtomicSets = false;

    private static CSVWriter writer;

    private static class ConfigurationVerifier implements Predicate<LiteralList> {
        private final LiteralList interaction;

        public ConfigurationVerifier(LiteralList interaction) {
            this.interaction = interaction;
        }

        // HERE get true if configuration not contains failing interaction (if
        // configuration is valid)
        @Override
        public boolean test(LiteralList configuration) {
            return !configuration.containsAll(interaction);
        }
    }

    public static void main(String[] args) throws IOException {
        writer = new CSVWriter();
        writer.setOutputFile(Paths.get("daten.csv"));
        writer.setHeader(
                "model_name",
                "interaction_size",
                "iteration",
                "interaction",
                "success",
                "found_interactions_count",
                "merged_interactions_size",
                "updated_interactions_size",
                "found_interactions",
                "merged_interactions",
                "updated_interactions",
                "configuration_count",
                "time");

        InteractionFinderTest.printCompare();
    }

    private static class AtomicSetReplacer implements TreeVisitor<Void, Formula> {
        final VariableMap variables;
        final List<LiteralList> atomicSets;

        public AtomicSetReplacer(VariableMap variables, List<LiteralList> atomicSets) {
            this.variables = variables;
            this.atomicSets = atomicSets;
        }

        @Override
        public VisitorResult firstVisit(List<Formula> path) {
            final Formula node = TreeVisitor.getCurrentNode(path);
            if (node instanceof Atomic) {
                return VisitorResult.SkipChildren;
            } else if ((node instanceof AuxiliaryRoot) || (node instanceof Compound)) {
                return VisitorResult.Continue;
            } else {
                return VisitorResult.Fail;
            }
        }

        @Override
        public VisitorResult lastVisit(List<Formula> path) {
            final Formula node = TreeVisitor.getCurrentNode(path);
            node.mapChildren(c -> {
                if (c instanceof BooleanLiteral) {
                    BooleanLiteral l = (BooleanLiteral) c;
                    int index = l.getIndex();
                    for (LiteralList atomicSet : atomicSets) {
                        if (atomicSet.containsAnyLiteral(index)) {
                            int substitute = atomicSet.get(0);
                            if (index != substitute) {
                                if (l.isPositive()) {
                                    return variables.createLiteral(Math.abs(substitute), substitute > 0);
                                } else {
                                    return variables.createLiteral(Math.abs(substitute), substitute < 0);
                                }
                            }
                            break;
                        } else if (atomicSet.containsAnyLiteral(-index)) {
                            int substitute = atomicSet.get(0);
                            if (-index != substitute) {
                                if (l.isPositive()) {
                                    return variables.createLiteral(Math.abs(substitute), substitute < 0);
                                } else {
                                    return variables.createLiteral(Math.abs(substitute), substitute > 0);
                                }
                            }
                            break;
                        }
                    }
                }
                return null;
            });
            return VisitorResult.Continue;
        }
    }

    public static void printCompare() throws IOException {
        //		String[] results = new String[iterations];
        int failCount = 0;

        ArrayList<String> models = new ArrayList<>();
        models.add("src/test/resources/GPL/model.xml");
        models.add("src/test/resources/testFeatureModels/breakfast.xml");
        //		models.add("src/test/resources/testFeatureModels/busybox.xml");

        for (String modelName : models) {

            long startTimeLoadModel = System.nanoTime();
            //
            ModelRepresentation model = getModel(Paths.get(modelName)); // modeltest.xml
            //		ModelRepresentation model = getModel(Paths.get("src/test/resources/testFeatureModels/busybox.xml")); //
            // modeltest.xml
            //		ModelRepresentation model = getModel(100);

            VariableMap variables = model.getVariables();
            LiteralList coreDead;

            MIG mig = model.get(MIGProvider.fromFormula(false, false));
            if (computeAtomicSets) {
                final List<LiteralList> atomicSets = model.get(new AtomicSetAnalysis());
                coreDead = atomicSets.get(0);
                List<LiteralList> atomicSetsWithoutCore = atomicSets.subList(1, atomicSets.size());

                Formula formulaWithoutAtomicSets = Trees.cloneTree(model.getFormula());
                Trees.traverse(formulaWithoutAtomicSets, new AtomicSetReplacer(variables, atomicSetsWithoutCore));

                VariableMap variablesWithoutAtomicSets = variables.clone();
                for (LiteralList atomicSet : atomicSetsWithoutCore) {
                    for (int i = 1; i < atomicSet.getLiterals().length; i++) {
                        variablesWithoutAtomicSets.removeVariable(Math.abs(atomicSet.get(i)));
                    }
                }
                variablesWithoutAtomicSets.normalize();

                Trees.traverse(formulaWithoutAtomicSets, new VariableMapSetter(variablesWithoutAtomicSets));

                coreDead = Clauses.adapt(coreDead, variables, variablesWithoutAtomicSets)
                        .get();
                model = new ModelRepresentation(formulaWithoutAtomicSets);
                variables = variablesWithoutAtomicSets;
            } else {
                coreDead = new LiteralList(mig.getVertices().stream()
                        .filter(Vertex::isCore)
                        .mapToInt(Vertex::getVar)
                        .toArray());
            }

            for (int interactionSize = 2; interactionSize <= maxInteractionSize; interactionSize++) {
                long initialSampleSeed = randomSeed.nextLong();
                long randomSampleSeed = randomSeed.nextLong();

                List<Integer> configCounts = new ArrayList<>();

                for (int i = 14; i < iterations; i++) {

                    long startIterationTime = System.nanoTime();

                    Random sampleRandom = new Random(i + initialSampleSeed);

                    // HERE add failingConfig
                    final List<LiteralList> input = generateInput(model, interactionSize, coreDead, sampleRandom);
                    LiteralList failInteraction = input.get(0);
                    List<LiteralList> sample = input.subList(1, 3);

                    Random completorRandom = new Random(i + randomSampleSeed);

                    // HERE verifier contains failing interaction
                    ConfigurationVerifier verifier = new ConfigurationVerifier(failInteraction);

                    InteractionFinder finder =
                            new InteractionFinderAtLeastOne(sample, createCompletor(model, completorRandom), verifier);

                    finder = new InteractionFinderCombinationForward(finder);

                    finder.setCore(coreDead);

                    int numberOfFeats = variables.getVariableCount();

                    int t = maxInteractionSize;
                    List<LiteralList> foundInteraction = finder.find(t, numberOfFeats - coreDead.size());

                    int foundInteractionListLength = foundInteraction.size();
                    int configurationCount = finder.getConfigurationCount() - sample.size();

                    configCounts.add(configurationCount);

                    LiteralList merged = finder.merge(foundInteraction);
                    LiteralList updated = finder.update(merged);

                    System.out.println(i + " " + (updated.containsAll(failInteraction) ? "OK" : "FAIL") + " "
                            + verifier.interaction + " #Configs: " + configurationCount + " #Found: "
                            + foundInteractionListLength + ": " + merged + " -> " + updated);

                    long finishIterationTime = System.nanoTime();
                    long timeElapsedIteration = finishIterationTime - startIterationTime;
                    double elapsedTimeInSecondIteration = (timeElapsedIteration / 1_000_000) / 1_000.0;
                    if (!updated.containsAll(failInteraction)) failCount++;

                    writer.createNewLine();
                    writer.addValue(modelName);
                    writer.addValue(interactionSize);
                    writer.addValue(i + 1);
                    writer.addValue(str(verifier.interaction));
                    writer.addValue(updated.containsAll(failInteraction) ? "OK" : "FAIL");
                    writer.addValue(foundInteraction.size());
                    writer.addValue(updated.size());
                    writer.addValue(merged.size());
                    writer.addValue(str(foundInteraction));
                    writer.addValue(updated);
                    writer.addValue(merged);
                    writer.addValue(configurationCount);
                    //					writer.addValue(toStr(finder.getInteractionCounter()));
                    writer.addValue(elapsedTimeInSecondIteration);
                    writer.flush();
                }
                System.out.println("Fails: " + failCount);
                System.out.println("#Configs: "
                        + configCounts.stream()
                                .mapToInt(Integer::intValue)
                                .average()
                                .getAsDouble());

                long finishTime = System.nanoTime();
                long timeElapsed = finishTime - startTimeLoadModel;
                System.out.println("Time: " + timeElapsed);
                double elapsedTimeInSecond = (timeElapsed / 1_000_000) / 1_000.0;
                System.out.println(elapsedTimeInSecond + " seconds");
            }
        }
    }

    private static String str(LiteralList findTWise) {
        return Arrays.toString(findTWise.getLiterals());
    }

    private static String str(List<LiteralList> findTWise) {
        StringBuilder sb = new StringBuilder();
        findTWise.forEach(list -> sb.append(str(list)));
        return sb.toString();
    }

    private static String toStr(List<?> list) {
        StringBuilder sb = new StringBuilder();
        for (Object object : list) {
            sb.append(String.valueOf(object));
            sb.append(",");
        }
        return sb.toString();
    }

    private static ModelRepresentation getModel(int size) {
        final VariableMap variables = new VariableMap(size);
        BooleanLiteral l = variables.createLiteral(1);
        return new ModelRepresentation(new Or(l, l.flip()));
    }

    private static ModelRepresentation getModel(Path path) {
        return ModelRepresentation.load(path).orElse(Logger::logProblems);
    }

    public static ConfigurationCompletor createCompletor(ModelRepresentation rep, Random random) {
        RandomConfigurationGenerator randomGenerator = new FastRandomConfigurationGenerator();
        randomGenerator.setAllowDuplicates(true);
        randomGenerator.setRandom(random);
        randomGenerator.init(rep.getCache(), new NullMonitor());
        return new ConfigurationCompletor(rep, randomGenerator);
    }

    private static List<LiteralList> generateInput(
            ModelRepresentation rep, int interactionSize, LiteralList coreDead, Random random) {
        LiteralList solution1 = rep.getResult(getConfigGenerator(random))
                .map(SolutionList::getSolutions)
                .map(list -> list.get(0))
                .orElse(Logger::logProblems);
        if (solution1 != null) {
            LiteralList interaction = new LiteralList(Stream.generate(() -> (random.nextInt(solution1.size()) + 1)) //
                    .mapToInt(Integer::intValue) //
                    .filter(l -> !coreDead.containsAnyVariable(l))
                    .distinct() //
                    .limit(interactionSize) //
                    .map(l -> solution1.get(l - 1)) //
                    .toArray());

            CNF cnf = rep.get(CNFProvider.fromFormula());
            List<LiteralList> clauses = new ArrayList<>(cnf.getClauses());
            clauses.add(interaction.negate());
            LiteralList solution2 = getConfigGenerator(random)
                    .execute(new CNF(cnf.getVariableMap(), clauses), new NullMonitor())
                    .getSolutions()
                    .get(0);

            return Arrays.asList(interaction, solution1, solution2);
        }
        throw new RuntimeException();
    }

    private static RandomConfigurationGenerator getConfigGenerator(Random random) {
        RandomConfigurationGenerator generator;
        generator = new FastRandomConfigurationGenerator();
        generator.setAllowDuplicates(false);
        generator.setRandom(random);
        generator.setLimit(1);
        return generator;
    }
}
