package de.featjar.assignment;

import de.featjar.analysis.sat4j.ContradictionAnalysis;
import de.featjar.analysis.sat4j.FastRandomConfigurationGenerator;
import de.featjar.analysis.sat4j.HasSolutionAnalysis;
import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.analysis.sat4j.twise.PresenceConditionManager;
import de.featjar.analysis.sat4j.twise.TWiseConfigurationGenerator;
import de.featjar.analysis.sat4j.twise.TWiseConfigurationUtil;
import de.featjar.analysis.sat4j.twise.TWiseStatisticGenerator;
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
import de.featjar.formula.structure.atomic.literal.BooleanLiteral;
import de.featjar.util.extension.ExtensionLoader;
import de.featjar.util.logging.Logger;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.concurrent.atomic.AtomicInteger;
import org.junit.jupiter.api.Test;

public class EvolutionTest {

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

    //System.out.println("EVO STAGE = 0");
    Formula formula = rep.getFormula();
    //System.out.println(Formulas.printTree(formula));
    CNF cnf = rep.get(CNFProvider.fromFormula());
    printCNF(cnf);

    //System.out.println("\n\nEVO STAGE = 1");
    Formula formulaEvo = repEvo.getFormula();
    CNF cnfEvo = repEvo.get(CNFProvider.fromFormula());
    printCNF(cnfEvo);
    //System.out.println(Formulas.printTree(formulaEvo));

    //System.out.println(cnf.getVariableMap().getVariableNames());

    SolutionList solutionList = generateValidConfigurations(rep);

    calculateCoverage(cnf, solutionList);

    solutionList.getSolutions().forEach(s -> {
            /*
            int randomVar = (int) (Math.random() * s.size());
            s.getLiterals()[randomVar] = randomVar + 1;
            */
      checkConfigurationOnNextEvolution(rep, repEvo, formulaEvo, s);
    });

    var genenrator = new TWiseStatisticGenerator(
        new TWiseConfigurationUtil(cnf, new Sat4JSolver(cnf)));
    // Find problematic clauses

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
      //var variableName = repEvo.getVariables().getBooleanVariable(Math.abs(l)).get();
      assumptions.add(new LiteralList(l));
    }
    contra.setClauseList(assumptions);
    //a.set(12, true);
    //a.set(13, true);

    boolean isValid = (boolean) Formulas.evaluate(formula, a)
        .orElse(false); //TODO: orElse false gleich richtig? Was bedeuetet no value present here?
    System.out.println("Is configuration valid = "
        + isValid); //evaluate => search for solution, each solution = one configuration
    //if (!isValid) {

    List<LiteralList> contradictions = repEvo.get(contra);
    contradictions.forEach(c -> {
      if (c != null) {
        System.out.println(Arrays.toString(c.getLiterals()));
                    /*
                    for (int l : c.getLiterals()) {
                        s.getLiterals()[Math.abs(l) - 1] = 0;
                    }
                    */
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
            System.out.println("HasSolutionAnalysis = " + canBeValid);

    //}
  }

  private static void calculateCoverage(CNF cnf, SolutionList solutionList) {
    TWiseConfigurationUtil util = new TWiseConfigurationUtil(cnf, new Sat4JSolver(cnf));
    TWiseStatisticGenerator stat = new TWiseStatisticGenerator(util);
/*
    PresenceConditionManager pcManager = new PresenceConditionManager(util, TWiseConfigurationGenerator.convertLiterals(Clauses.getLiterals(cnf.getVariableMap())));
    var coverage = stat.getCoverage(List.of(solutionList.getSolutions()),
        pcManager.getGroupedPresenceConditions(), 2
        , TWiseStatisticGenerator.ConfigurationScore.NONE, true);
    System.out.println(coverage.get(0).getCoverage());

 */
  }

  private static SolutionList generateValidConfigurations(ModelRepresentation rep) {
    TWiseConfigurationGenerator twisegen = new TWiseConfigurationGenerator();
    FastRandomConfigurationGenerator gen = new FastRandomConfigurationGenerator();
    gen.setRandom(new Random(1));
    gen.setLimit(10);
    gen.setAllowDuplicates(false);
    twisegen.setT(2);
    SolutionList solutionList = rep.get(twisegen);
    return solutionList;
  }
}
