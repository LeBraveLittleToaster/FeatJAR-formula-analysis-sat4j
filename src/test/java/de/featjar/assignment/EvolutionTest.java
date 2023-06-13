package de.featjar.assignment;

import de.featjar.analysis.sat4j.ContradictionAnalysis;
import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.analysis.sat4j.twise.PresenceConditionManager;
import de.featjar.analysis.sat4j.twise.TWiseConfigurationGenerator;
import de.featjar.analysis.sat4j.twise.TWiseConfigurationUtil;
import de.featjar.analysis.sat4j.twise.TWiseStatisticGenerator;
import de.featjar.analysis.sat4j.twise.YASA;
import de.featjar.assignment.DataLoader.Dataset;
import de.featjar.assignment.DataLoader.EvolutionSet;
import de.featjar.clauses.CNF;
import de.featjar.clauses.CNFProvider;
import de.featjar.clauses.Clauses;
import de.featjar.clauses.LiteralList;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.formula.structure.Formula;
import de.featjar.formula.structure.Formulas;
import de.featjar.formula.structure.atomic.IndexAssignment;
import de.featjar.util.extension.ExtensionLoader;
import de.featjar.util.job.NullMonitor;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicLong;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.StreamSupport;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

public class EvolutionTest {

  private static Dataset DATASET = Dataset.BERKELEY;
  private static String absolutPathPrefix = "C:\\Users\\gamef\\Documents\\GitHub\\FeatJAR\\formula-analysis-sat4j\\src\\test\\resources\\";
  private static boolean PRINT_CNFS = false;
  private static boolean PRINT_CONFIG_EXTENDED = false;
  private static boolean PRINT_SOLUTION_AND_CONFIGURATION = false;
  private static boolean PRINT_NEW_SAMPLE = false;


  private static EvolutionSet evoSet;
  private static CNF cnfEvo0;
  private static CNF cnfEvo1;
  private static SolutionList solutionList;
  private static double oldCoverage;
  private static Formula formulaEvo;
  private static YASA yasa;
  private static NullMonitor monitor;


  @BeforeAll
  public static void readModelRepresentations() {
    ExtensionLoader.load();

    evoSet = DataLoader.getEvolutionSet(DATASET, absolutPathPrefix);

    System.out.println("Retrieving CNFs...");
    // Evolution Step 0
    cnfEvo0 = evoSet.repEvo0.get(CNFProvider.fromFormula());

    // Evolution Step 1
    cnfEvo1 = evoSet.repEvo1.get(CNFProvider.fromFormula());
    formulaEvo = evoSet.repEvo1.getFormula();

    if (PRINT_CNFS) {
      EntityPrinter.printCNF(cnfEvo0);
      EntityPrinter.printCNF(cnfEvo1);
    }

    System.out.println("Generating valid sample for evo 0...");
    solutionList = EntityPrinter.generateValidTWiseConfigurations(evoSet.repEvo0);
    System.out.println("Calculating coverage...");
    oldCoverage = calculateCoverage(cnfEvo0, solutionList);
    System.out.println("\nOLD COVERAGE (Should be 1.0) = " + oldCoverage + "\n");

    System.out.println("Initializing Yasa...");
    yasa = new YASA();
    yasa.setSolver(new Sat4JSolver(cnfEvo1));
    monitor = new NullMonitor();
    yasa.init2(monitor);
  }

  @Test
  public void testGenerateSample() {
    AtomicLong timerTwise = new AtomicLong(System.nanoTime());
    EntityPrinter.generateValidTWiseConfigurations(evoSet.repEvo0);
    System.out.println("\n+++++++++++++++++++++++++\n");
    System.out.println(
        "Timer generate complete new Twise Sample = " + ((System.nanoTime() - timerTwise.get())
            / 1e6) + " ms");
    System.out.println("\n+++++++++++++++++++++++++\n");
  }

  @Test
  public void testRepairSample() {
    AtomicLong counterZeros = new AtomicLong();
    AtomicLong counterNonZeros = new AtomicLong();
    AtomicLong timerCounterCheckConfiguration = new AtomicLong();
    AtomicLong timerRemapping = new AtomicLong();
    AtomicLong timerNewConfiguration = new AtomicLong();
    AtomicLong timerBuildAndSample = new AtomicLong();

    System.out.println(
        "Starting solution analysis (solution count=" + solutionList.getSolutions().size()
            + ")...");

    AtomicLong timeStamp = new AtomicLong(System.nanoTime());
    solutionList.getSolutions().forEach(s -> {

      if (PRINT_SOLUTION_AND_CONFIGURATION) {
        System.out.println("############# SOLUTION START ###############");
      }

      // use configuration from Evo0 in Evo1
      timeStamp.set(System.nanoTime());
      var isValid = validateEvo0ConfigWithEvo1(formulaEvo, s);
      timerCounterCheckConfiguration.addAndGet(System.nanoTime() - timeStamp.get());

      // counting zeros for stats
      IntStream.of(s.getLiterals()).forEach(v -> {
        if (v == 0) {
          counterZeros.addAndGet(1);
        }
        {
          counterNonZeros.addAndGet(1);
        }
      });
      // remap configuration to fit next evolution step
      timeStamp.set(System.nanoTime());
      var oldConfigurationWithZeros = IntStream.of(s.getLiterals()).toArray();
      var nextConfiguration = remapItemsByName(oldConfigurationWithZeros, cnfEvo0, cnfEvo1);
      timerRemapping.addAndGet(System.nanoTime() - timeStamp.get());

      if (PRINT_CONFIG_EXTENDED && !isValid) {
        System.out.println("OLD CONFIG");
        EntityPrinter.printConfigurationWithName(oldConfigurationWithZeros, cnfEvo0);
        System.out.println("NEXT CONFIG");
        EntityPrinter.printConfigurationWithName(nextConfiguration, cnfEvo1);
      }

      // insert partial config into yasa
      timeStamp.set(System.nanoTime());
      yasa.newConfiguration(nextConfiguration);
      timerNewConfiguration.addAndGet(System.nanoTime() - timeStamp.get());

      if (PRINT_SOLUTION_AND_CONFIGURATION) {
        System.out.println("############## SOLUTION END ################");
      }
    });
    System.out.println("Done solution analysis...");

    System.out.println("Building new solutions...");
    timeStamp.set(System.nanoTime());
    // build sample from partial configurations
    yasa.buildConfigurations(monitor);
    var newSample = StreamSupport.stream(yasa, false)
        .collect(Collectors.toCollection(ArrayList::new));
    timerBuildAndSample.addAndGet(System.nanoTime() - timeStamp.get());

    if (PRINT_NEW_SAMPLE) {
      System.out.println("\nNEW SAMPLE");
      System.out.println(newSample);
    }

    var newSolutions = new SolutionList(evoSet.repEvo1.getVariables(), newSample);

    // Calculate coverage
    System.out.println(
        "\nNEW COVERAGE = " + calculateCoverage(cnfEvo1, newSolutions) + " | Old Coverage = "
            + oldCoverage + "\n");

    EntityPrinter.printStats(timerCounterCheckConfiguration, timerRemapping,
        timerNewConfiguration,
        timerBuildAndSample, counterZeros, counterNonZeros);
  }


  private static int[] remapItemsByName(int[] oldConfigurationWithZeros, CNF cnfOld, CNF cnfNext) {
    var nextAssignment = new ArrayList<Integer>();
    List<Integer> oldConfigAsList = IntStream.of(oldConfigurationWithZeros).boxed()
        .collect(Collectors.toList());

    for (var nextIndex = 1; nextIndex <= cnfNext.getVariableMap().getVariableCount(); nextIndex++) {
      // get current var name
      var nextVarNameOpt = cnfNext.getVariableMap().getVariableName(nextIndex);
      if (nextVarNameOpt.isEmpty()) {
        continue;
      }

      // did feature exist in old CNF? if no, ignore
      var nextVarName = nextVarNameOpt.get();
      var oldVarIndexOpt = cnfOld.getVariableMap().getVariableIndex(nextVarName);
      if (oldVarIndexOpt.isEmpty()) {
        continue; // didn´t exist, go on
      }

      // did exist, do we consider it?
      var oldVarIndex = oldVarIndexOpt.get();
      // check if the old index appears in the oldConfig (if set to zero also not consider it)
      var oldValueOpt = oldConfigAsList.stream().filter(i -> Math.abs(i) == oldVarIndex)
          .findFirst();
      if (oldValueOpt.isEmpty()) {
        continue;
      }

      // otherwise add the old value to the new assignment
      var oldValue = oldValueOpt.get();
      nextAssignment.add(oldValue > 0 ? nextIndex : -nextIndex);
    }
    return nextAssignment.stream().mapToInt(i -> i).toArray();
  }

  private static boolean validateEvo0ConfigWithEvo1(Formula formula, LiteralList s) {
    List<LiteralList> assumptions = new ArrayList<>();
    ContradictionAnalysis contra = new ContradictionAnalysis();

    if (PRINT_SOLUTION_AND_CONFIGURATION) {
      System.out.println(Arrays.toString(s.getLiterals()));
    }
    IndexAssignment a = new IndexAssignment();
    for (int l : s.getLiterals()) {
      a.set(Math.abs(l), l > 0);
      assumptions.add(new LiteralList(l));
    }
    contra.setClauseList(assumptions);

    boolean isFormulaValid = (boolean) Formulas.evaluate(formula, a).orElse(false);
    if (PRINT_SOLUTION_AND_CONFIGURATION) {

      System.out.println("Is configuration valid = " + isFormulaValid);
    }

    if (isFormulaValid) {
      return true;
    }

    formula.getChildren().forEach(clause -> {
      boolean isValid = (boolean) Formulas.evaluate(clause, a).orElse(false);
      if (!isValid) {
        Formulas.getVariables(clause).forEach(variable -> {
          s.getLiterals()[variable.getIndex() - 1] = 0;
        });
      }
    });

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
}
