package de.featjar.assignment;

import static de.featjar.assignment.TimerCollection.TimerType.BUILD_CONFIGURATIONS;
import static de.featjar.assignment.TimerCollection.TimerType.CHECK_CONFIGURATION;
import static de.featjar.assignment.TimerCollection.TimerType.NEW_CONFIGURATION;
import static de.featjar.assignment.TimerCollection.TimerType.NEXT_CONFIGURATION;
import static de.featjar.assignment.TimerCollection.TimerType.REMAPPING;

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
import java.util.Optional;
import java.util.concurrent.atomic.AtomicLong;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.StreamSupport;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

public class EvolutionTest {

  private static final Dataset DATASET = Dataset.BERKELEY;
  private static final String absolutPathPrefix = "C:\\Users\\gamef\\Documents\\GitHub\\FeatJAR\\FeatJAR\\formula-analysis-sat4j\\src\\test\\resources\\";
  private static final boolean PRINT_CNFS = false;
  private static final boolean PRINT_CONFIG_EXTENDED = false;
  private static final boolean PRINT_SOLUTION_AND_CONFIGURATION = false;
  private static final boolean PRINT_NEW_SAMPLE = false;


  private static EvolutionSet evoSet;
  private static CNF cnfEvo0;
  private static CNF cnfEvo1;
  private static SolutionList solutionList;
  private static double oldCoverage;
  private static Formula formulaEvo;
  private static YASA yasa;
  private static NullMonitor monitor;

  private static TimerCollection timers;


  @BeforeAll
  public static void readModelRepresentations() {
    timers = new TimerCollection();
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

    System.out.println(
        "Starting solution analysis (solution count=" + solutionList.getSolutions().size()
            + ")...");

    solutionList.getSolutions().forEach(s -> {

      if (PRINT_SOLUTION_AND_CONFIGURATION) {
        System.out.println("############# SOLUTION START ###############");
      }
      timers.startTimer(REMAPPING);
      var remappedConfig = remapItemsByName(IntStream.of(s.getLiterals()).toArray(), cnfEvo0, cnfEvo1);
      timers.stopAndAddTimer(REMAPPING);

      timers.startTimer(CHECK_CONFIGURATION);
      var isValid = validateEvo0ConfigWithEvo1(formulaEvo, remappedConfig);
      timers.stopAndAddTimer(CHECK_CONFIGURATION);

      if(isValid.isEmpty()) return;

      var nextConfigurationWithZeros = isValid.get();
      IntStream.of(nextConfigurationWithZeros).forEach(v -> {
        if (v == 0) {
          counterZeros.addAndGet(1);
        }
        {
          counterNonZeros.addAndGet(1);
        }
      });

      if (PRINT_CONFIG_EXTENDED) {

        System.out.println("OLD CONFIG");
        EntityPrinter.printConfigurationWithName(s.getLiterals(), cnfEvo0);
        System.out.println("NEXT CONFIG");
        EntityPrinter.printConfigurationWithName(nextConfigurationWithZeros, cnfEvo1);
      }


      // insert partial config into yasa

      timers.startTimer(NEXT_CONFIGURATION);
      var nextConfiguration = IntStream.of(isValid.get()).filter(i -> i != 0).toArray();
      yasa.newConfiguration(nextConfiguration);
      timers.stopAndAddTimer(NEXT_CONFIGURATION);


      if (PRINT_SOLUTION_AND_CONFIGURATION) {
        System.out.println("############## SOLUTION END ################");
      }
    });
    System.out.println("Done solution analysis...");

    System.out.println("Building new solutions...");
    timers.startTimer(BUILD_CONFIGURATIONS);
    // build sample from partial configurations
    yasa.buildConfigurations(monitor);
    var newSample = StreamSupport.stream(yasa, false)
        .collect(Collectors.toCollection(ArrayList::new));
    timers.stopAndAddTimer(BUILD_CONFIGURATIONS);


    if (PRINT_NEW_SAMPLE) {
      System.out.println("\nNEW SAMPLE");
      System.out.println(newSample);
    }


    timers.startTimer(NEW_CONFIGURATION);
    var newSolutions = new SolutionList(evoSet.repEvo1.getVariables(), newSample);
    var newValidSolutions = new SolutionList(evoSet.repEvo1.getVariables(), newSolutions.getValidSolutions(cnfEvo1)
            .collect(Collectors.toList()));

    // Calculate coverage
    System.out.println(
        "\nNEW COVERAGE = " + calculateCoverage(cnfEvo1, newValidSolutions) + " | Old Coverage = "
            + oldCoverage + "\n");
    timers.stopAndAddTimer(NEW_CONFIGURATION);

    EntityPrinter.printStats(cnfEvo0, cnfEvo1, counterZeros, counterNonZeros);
    EntityPrinter.printTimers(timers);
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

  private static Optional<int[]> validateEvo0ConfigWithEvo1(Formula formula, int[] s) {
    List<LiteralList> assumptions = new ArrayList<>();
    ContradictionAnalysis contra = new ContradictionAnalysis();

    if (PRINT_SOLUTION_AND_CONFIGURATION) {
      System.out.println(Arrays.toString(s));
    }
    IndexAssignment a = new IndexAssignment();
    for (int l : s) {
      a.set(Math.abs(l), l > 0);
      assumptions.add(new LiteralList(l));
    }
    contra.setClauseList(assumptions);

    boolean isFormulaValid = (boolean) Formulas.evaluate(formula, a).orElse(false);
    if (PRINT_SOLUTION_AND_CONFIGURATION) {

      System.out.println("Is configuration valid = " + isFormulaValid);
    }

    if (isFormulaValid) {
      return Optional.empty();
    }

    formula.getChildren().forEach(clause -> {
      boolean isValid = (boolean) Formulas.evaluate(clause, a).orElse(false);
      if (!isValid) {
        Formulas.getVariables(clause).forEach(variable -> {
          s[variable.getIndex() - 1] = 0;
        });
      }
    });

    return Optional.of(s);
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
