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
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.StreamSupport;

public class EvolutionTest {

    private static boolean PRINT_CNFS = true;

    @Test
    public void testTry() {
        ExtensionLoader.load();
        //ModelRepresentation rep = ModelRepresentation.load(Paths.get("C:/Users/gamef/Documents/GitHub/FeatJAR/formula-analysis-sat4j/src/test/resources/GPL/model.xml")).orElse(Logger::logProblems);
        ModelRepresentation rep = ModelRepresentation.load(Paths.get(
                        "C:/Users/gamef/Documents/GitHub/FeatJAR/FeatJAR/formula-analysis-sat4j/src/test/resources/MA_PS/m_simple_e0.xml"))
                .orElse(Logger::logProblems);
        ModelRepresentation repEvo = ModelRepresentation.load(Paths.get(
                        "C:/Users/gamef/Documents/GitHub/FeatJAR/FeatJAR/formula-analysis-sat4j/src/test/resources/MA_PS/m_simple_e1.xml"))
                .orElse(Logger::logProblems);

        // Evolution Step 0
        CNF cnf = rep.get(CNFProvider.fromFormula());

        // Evolution Step 1
        CNF cnfEvo = repEvo.get(CNFProvider.fromFormula());
        Formula formulaEvo = repEvo.getFormula();

        if(PRINT_CNFS) {
            printCNF(cnf);
            printCNF(cnfEvo);
        }

        SolutionList solutionList = generateValidTWiseConfigurations(rep);
        calculateCoverage(cnf, solutionList);

        YASA yasa = new YASA();
        yasa.setSolver(new Sat4JSolver(repEvo.get(CNFProvider.fromFormula())));
        var monitor = new NullMonitor();
        yasa.init2(monitor);

        solutionList.getSolutions().forEach(s -> {
            checkConfigurationOnNextEvolution(rep, repEvo, formulaEvo, s);
            yasa.newConfiguration(IntStream.of(s.getLiterals()).filter(i -> i != 0).toArray());
        });

        yasa.buildConfigurations(monitor);
        // New sample from partial configuration
        var newSample = StreamSupport.stream(yasa, false).collect(Collectors.toCollection(ArrayList::new));
        System.out.println("NEW SAMPLE");
        System.out.println(newSample);

        // Calculate coverage
        var newSolutions = new SolutionList(repEvo.getVariables(), newSample);
        calculateCoverage(repEvo.get(CNFProvider.fromFormula()), newSolutions);
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

    /**
     * Indexassignment remapping First, all
     *
     * @param oldAssignment  prior assignment that should be remapped
     * @param indexRemapping key is the new index position, the value is the old position
     * @param newItemsToAdd  key is the position where we should add the elements, value the value to
     *                       add
     * @return remapped assignment
     */
    private static IndexAssignment remapItems(IndexAssignment oldAssignment,
                                              Map<Integer, Integer> indexRemapping, Map<Integer, Object> newItemsToAdd) {

        var assignment = new IndexAssignment();
        //TODO: Check if mapping is valid, no duplicates, values present etc.
        indexRemapping.forEach(
                (newI, oldI) -> oldAssignment.get(oldI).ifPresent((value) -> assignment.set(newI, value)));
        newItemsToAdd.forEach(assignment::set);

        return assignment;
    }

    private static void checkConfigurationOnNextEvolution(ModelRepresentation rep,
                                                          ModelRepresentation repEvo, Formula formula, LiteralList s) {
        List<LiteralList> assumptions = new ArrayList<>();
        ContradictionAnalysis contra = new ContradictionAnalysis();

        System.out.println(Arrays.toString(s.getLiterals()));
        IndexAssignment a = new IndexAssignment();
        for (int l : s.getLiterals()) {
            a.set(Math.abs(l), l > 0);
            assumptions.add(new LiteralList(l));
        }
        contra.setClauseList(assumptions);

        boolean isFormulaValid = (boolean) Formulas.evaluate(formula, a)
                .orElse(false); //TODO: orElse false gleich richtig? Was bedeuetet no value present here?
        System.out.println("Is configuration valid = "
                + isFormulaValid); //evaluate => search for solution, each solution = one configuration
        if (isFormulaValid) return;

        formula.getChildren().forEach(clause -> {
            boolean isValid = (boolean) Formulas.evaluate(clause, a)
                    .orElse(false); //TODO: orElse false gleich richtig? Was bedeuetet no value present here?
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
        System.out.println("HasSolutionAnalysis = " + canBeValid + "\n");
    }

    private static void calculateCoverage(CNF cnf, SolutionList solutionList) {
        TWiseConfigurationUtil util = new TWiseConfigurationUtil(cnf, new Sat4JSolver(cnf));
        TWiseStatisticGenerator stat = new TWiseStatisticGenerator(util);

        PresenceConditionManager pcManager = new PresenceConditionManager(
                util.getDeadCoreFeatures(),
                solutionList.getVariableMap().getVariableCount(),
                TWiseConfigurationGenerator.convertLiterals(Clauses.getLiterals(cnf.getVariableMap())));
        var coverage = stat.getCoverage(List.of(solutionList.getSolutions()),
                pcManager.getGroupedPresenceConditions(), 2
                , TWiseStatisticGenerator.ConfigurationScore.NONE, true);
        System.out.println("NEW COVERAGE: " + coverage.get(0).getCoverage());
    }

    private static SolutionList generateValidTWiseConfigurations(ModelRepresentation rep) {
        TWiseConfigurationGenerator twisegen = new TWiseConfigurationGenerator();
        twisegen.setT(2);
        return rep.get(twisegen);
    }
}
