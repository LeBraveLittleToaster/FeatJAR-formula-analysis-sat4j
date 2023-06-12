package de.featjar.assignment;

import de.featjar.analysis.sat4j.ContradictionAnalysis;
import de.featjar.analysis.sat4j.HasSolutionAnalysis;
import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.analysis.sat4j.twise.*;
import de.featjar.clauses.CNF;
import de.featjar.clauses.CNFProvider;
import de.featjar.clauses.Clauses;
import de.featjar.clauses.LiteralList;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.formula.ModelRepresentation;
import de.featjar.formula.structure.Formula;
import de.featjar.formula.structure.Formulas;
import de.featjar.formula.structure.atomic.Assignment;
import de.featjar.formula.structure.atomic.IndexAssignment;
import de.featjar.util.extension.ExtensionLoader;
import de.featjar.util.job.NullMonitor;
import de.featjar.util.logging.Logger;
import org.junit.jupiter.api.Test;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.StreamSupport;

public class EvolutionTest {

    private static boolean PRINT_CNFS = false;
    private static boolean PRINT_CONFIG_EXTENDED = true;

    @Test
    public void testTry() {
        ExtensionLoader.load();
        //ModelRepresentation repEvo0 = ModelRepresentation.load(Paths.get("C:/Users/gamef/Documents/GitHub/FeatJAR/formula-analysis-sat4j/src/test/resources/GPL/model.xml")).orElse(Logger::logProblems);

        ModelRepresentation repEvo0 = ModelRepresentation.load(Paths.get(
                        "C:/Users/gamef/Documents/GitHub/FeatJAR/FeatJAR/formula-analysis-sat4j/src/test/resources/MA_PS/m_simple_e0.xml"))
                .orElse(Logger::logProblems);
        ModelRepresentation repEvo1 = ModelRepresentation.load(Paths.get(
                        "C:/Users/gamef/Documents/GitHub/FeatJAR/FeatJAR/formula-analysis-sat4j/src/test/resources/MA_PS/m_simple_e1.xml"))
                .orElse(Logger::logProblems);

        /*ModelRepresentation repEvo0 = ModelRepresentation.load(Paths.get(
                        "C:/Users/gamef/Documents/GitHub/FeatJAR/FeatJAR/formula-analysis-sat4j/src/test/resources/MA_PS/model_evo0.xml"))
                .orElse(Logger::logProblems);
        ModelRepresentation repEvo1 = ModelRepresentation.load(Paths.get(
                        "C:/Users/gamef/Documents/GitHub/FeatJAR/FeatJAR/formula-analysis-sat4j/src/test/resources/MA_PS/model_evo1_simple.xml"))
                .orElse(Logger::logProblems);*/

        // Evolution Step 0
        CNF cnfEvo0 = repEvo0.get(CNFProvider.fromFormula());

        // Evolution Step 1
        CNF cnfEvo1 = repEvo1.get(CNFProvider.fromFormula());
        Formula formulaEvo = repEvo1.getFormula();

        if (PRINT_CNFS) {
            printCNF(cnfEvo0);
            printCNF(cnfEvo1);
        }

        SolutionList solutionList = generateValidTWiseConfigurations(repEvo0);
        var oldCoverage = calculateCoverage(cnfEvo0, solutionList);
        System.out.println("\nOLD COVERAGE (Should be 1.0) = " + oldCoverage + "\n");

        YASA yasa = new YASA();
        yasa.setSolver(new Sat4JSolver(cnfEvo1));
        var monitor = new NullMonitor();
        yasa.init2(monitor);

        solutionList.getSolutions().forEach(s -> {
            System.out.println("############# SOLUTION START ###############");
            var isValid = checkConfigurationOnNextEvolution(repEvo1, formulaEvo, s);
            var oldConfigurationWithZeros = IntStream.of(s.getLiterals()).toArray();
            var nextConfiguration = remapItemsByName(oldConfigurationWithZeros, cnfEvo0, cnfEvo1);
            if (PRINT_CONFIG_EXTENDED && !isValid) {
                System.out.println("OLD CONFIG");
                printConfigurationWithName(oldConfigurationWithZeros, cnfEvo0);
                System.out.println("NEXT CONFIG");
                printConfigurationWithName(nextConfiguration, cnfEvo1);
            }
            yasa.newConfiguration(nextConfiguration);
            System.out.println("############## SOLUTION END ################");
        });

        // New sample from partial configuration
        yasa.buildConfigurations(monitor);
        var newSample = StreamSupport.stream(yasa, false).collect(Collectors.toCollection(ArrayList::new));
        System.out.println("\nNEW SAMPLE");
        System.out.println(newSample);

        // Calculate coverage
        var newSolutions = new SolutionList(repEvo1.getVariables(), newSample);
        System.out.println("\nNEW COVERAGE = " + calculateCoverage(cnfEvo1, newSolutions) + " | Old Coverage = " + oldCoverage + "\n");
    }

    private static int[] remapItemsByName(int[] oldConfigurationWithZeros, CNF cnfOld, CNF cnfNext) {
        var nextAssignment = new ArrayList<Integer>();
        List<Integer> oldConfigAsList = IntStream.of(oldConfigurationWithZeros).boxed().collect(Collectors.toList());

        for (var nextIndex = 1; nextIndex <= cnfNext.getVariableMap().getVariableCount(); nextIndex++) {
            // get current var name
            var nextVarNameOpt = cnfNext.getVariableMap().getVariableName(nextIndex);
            if (nextVarNameOpt.isEmpty()) continue;

            // did feature exist in old CNF? if no, ignore
            var nextVarName = nextVarNameOpt.get();
            var oldVarIndexOpt = cnfOld.getVariableMap().getVariableIndex(nextVarName);
            if (oldVarIndexOpt.isEmpty()) continue; // didn´t exist, go on

            // did exist, do we consider it?
            var oldVarIndex = oldVarIndexOpt.get();
            // check if the old index appears in the oldConfig (if set to zero also not consider it)
            var oldValueOpt = oldConfigAsList.stream().filter(i -> Math.abs(i) == oldVarIndex).findFirst();
            if (oldValueOpt.isEmpty()) continue;

            // otherwise add the old value to the new assignment
            var oldValue = oldValueOpt.get();
            nextAssignment.add(oldValue > 0 ? nextIndex : -nextIndex);
        }
        return nextAssignment.stream().mapToInt(i -> i).toArray();
    }

    private static int getOldOrDefaultValue(int nextIndex, List<Integer> oldAssignment, CNF cnfOld, CNF cnfNext) {
        var defaultValue = 0;
        var nextVarName = cnfNext.getVariableMap().getVariableName(nextIndex + 1);
        if (nextVarName.isEmpty()) return defaultValue;
        var oldIndex = cnfOld.getVariableMap().getVariableIndex(nextVarName.get());
        if (oldIndex.isEmpty()) return defaultValue;
        for (int oldValue :
                oldAssignment) {
            if (oldValue == oldIndex.get() || oldValue == -oldIndex.get()) {
                return oldValue;
            }
        }
        return defaultValue;
    }

    private static boolean checkConfigurationOnNextEvolution(ModelRepresentation repEvo, Formula formula, LiteralList s) {
        List<LiteralList> assumptions = new ArrayList<>();
        ContradictionAnalysis contra = new ContradictionAnalysis();

        System.out.println(Arrays.toString(s.getLiterals()));
        IndexAssignment a = new IndexAssignment();
        for (int l : s.getLiterals()) {
            a.set(Math.abs(l), l > 0);
            assumptions.add(new LiteralList(l));
        }
        contra.setClauseList(assumptions);

        boolean isFormulaValid = (boolean) Formulas.evaluate(formula, a).orElse(false);
        System.out.println("Is configuration valid = " + isFormulaValid);

        if (isFormulaValid) return true;

        formula.getChildren().forEach(clause -> {
            boolean isValid = (boolean) Formulas.evaluate(clause, a).orElse(false);
            if (!isValid) {
                Formulas.getVariables(clause).forEach(variable -> {
                    s.getLiterals()[variable.getIndex() - 1] = 0;
                });
            }
        });

        HasSolutionAnalysis sat = new HasSolutionAnalysis();
        Assignment assumptions2 = contra.getAssumptions();
        for (int l : s.getLiterals()) {
            assumptions2.set(Math.abs(l), l > 0);
        }
        assumptions2 = sat.getAssumptions();
        for (int l : s.getLiterals()) {
            if (l != 0) {
                assumptions2.set(Math.abs(l), l > 0);
            }
        }
        Boolean canBeValid = repEvo.get(sat);
        System.out.println(s);
        System.out.println("Is CNF satisfiable? CanBeValid = " + canBeValid + "\n");
        return false;
    }

    private static double calculateCoverage(CNF cnf, SolutionList solutionList) {
        TWiseConfigurationUtil util = new TWiseConfigurationUtil(cnf, new Sat4JSolver(cnf));
        TWiseStatisticGenerator stat = new TWiseStatisticGenerator(util);

        PresenceConditionManager pcManager = new PresenceConditionManager(
                util.getDeadCoreFeatures(),
                solutionList.getVariableMap().getVariableCount(),
                TWiseConfigurationGenerator.convertLiterals(Clauses.getLiterals(cnf.getVariableMap())));
        var coverage = stat.getCoverage(List.of(solutionList.getSolutions()),
                pcManager.getGroupedPresenceConditions(), 2
                , TWiseStatisticGenerator.ConfigurationScore.NONE, true);
        return coverage.get(0).getCoverage();
    }

    private static SolutionList generateValidTWiseConfigurations(ModelRepresentation rep) {
        TWiseConfigurationGenerator twisegen = new TWiseConfigurationGenerator();
        twisegen.setT(2);
        return rep.get(twisegen);
    }

    private static void printCNF(CNF cnf) {
        System.out.println("++++++ CNF START +++++\n");
        AtomicInteger idx = new AtomicInteger(0);
        cnf.getClauses().forEach(clause -> {
            System.out.println("[" + idx.getAndIncrement() + "] " + clause);
            for (int literal : clause.getLiterals()) {
                System.out.println("\t" + cnf.getVariableMap().getVariableName(Math.abs(literal)).get());
            }
        });
        System.out.println("\n++++++ CNF END +++++");
    }

    private static void printConfigurationWithName(int[] assignment, CNF cnf) {
        var builder = new StringBuilder();
        builder.append("+++++++++CONFIGURATION++++++++++++++++++\n")
                .append("Config  => ").append(Arrays.toString(assignment)).append("\n")
                .append("Stats   => [size=").append(assignment.length).append("]\n")
                .append("Mapping => | ");
        for (int l : assignment) {
            builder.append(Math.abs(l))
                    .append(" = ")
                    .append(cnf.getVariableMap().getVariableName(Math.abs(l)).orElse("No name found"))
                    .append(" | ");
        }
        builder.append("\n");
        builder.append("+++++++++CONFIGURATION++++++++++++++++++\n");
        System.out.println(builder);
    }
}
