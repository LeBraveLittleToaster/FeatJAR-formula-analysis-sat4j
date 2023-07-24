package de.featjar.assignment.ma;

import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.analysis.sat4j.twise.*;
import de.featjar.repair.*;
import de.featjar.repair.DataLoader.Dataset2;
import de.featjar.clauses.CNF;
import de.featjar.clauses.CNFProvider;
import de.featjar.clauses.Clauses;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.formula.structure.Formula;
import de.featjar.util.extension.ExtensionLoader;
import de.featjar.util.job.NullMonitor;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.concurrent.atomic.AtomicLong;

public class EvolutionTest {

    private static final Dataset2 DATASET_2 = Dataset2.BUSYBOX;
    private static final String absolutPathPrefix = "./src/test/resources/";
    private static final boolean PRINT_CNFS = false;
    private static final boolean PRINT_CONFIG_EXTENDED = false;
    private static final boolean PRINT_SOLUTION_AND_CONFIGURATION = false;
    private static final boolean PRINT_NEW_SAMPLE = false;


    private static EvolutionSet evoSet;
    private static CNF cnfEvo0;
    private static CNF cnfEvo1;
    private static double oldCoverage;
    private static Formula formulaEvo;
    private static YASA yasa;
    private static NullMonitor monitor;

    private static TimerCollection timers;


    @BeforeAll
    public static void readModelRepresentations() {
        timers = new TimerCollection();
        ExtensionLoader.load();

        evoSet = DataLoader.getEvolutionSet(DATASET_2, absolutPathPrefix);
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

        System.out.println("Calculating coverage...");
        oldCoverage = RepairOperations.calculateCoverage(cnfEvo0, evoSet.repEvo0Sample);
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
        EntityPrinter.generateValidTWiseConfigurations(evoSet.repEvo1);
        System.out.println("\n+++++++++++++++++++++++++\n");
        System.out.println(
                "Timer generate complete new Twise Sample = " + ((System.nanoTime() - timerTwise.get())
                        / 1e9) + " s");
        System.out.println("\n+++++++++++++++++++++++++\n");
    }

    @Test
    public void testRepairSample() {
        AtomicLong counterZeros = new AtomicLong();
        AtomicLong counterNonZeros = new AtomicLong();
        AtomicLong faultyCount = new AtomicLong();
        System.out.println(
                "Starting solution analysis (solution count=" + evoSet.repEvo0Sample.getSolutions().size()
                        + ")...");


        evoSet.repEvo0Sample.getSolutions().forEach(s -> {

            if (PRINT_SOLUTION_AND_CONFIGURATION) {
                System.out.println("############# SOLUTION START ###############");
            }
            var remappedConfig = RepairOperations.remapOldIndexesViaNames(s, timers, cnfEvo0, cnfEvo1);

            var maybeNullifiedConfigOpt = RepairOperations.validateOldSampleAgainstEvo1(remappedConfig, timers, formulaEvo, evoSet.repEvo1, PRINT_SOLUTION_AND_CONFIGURATION);
            if(maybeNullifiedConfigOpt.isEmpty()) return;

            var maybeNullifiedConfig = maybeNullifiedConfigOpt.get();
            var nextConfigurationWithZeros = RepairOperations.countZerosInConfigurations(counterZeros, counterNonZeros, maybeNullifiedConfig);

            if (PRINT_CONFIG_EXTENDED) {
                System.out.println("OLD CONFIG");
                EntityPrinter.printConfigurationWithName(s.getLiterals(), cnfEvo0);
                System.out.println("NEXT CONFIG");
                EntityPrinter.printConfigurationWithName(nextConfigurationWithZeros, cnfEvo1);
            }

            var successful = RepairOperations.createNewConfigurationsWithYasa(maybeNullifiedConfig, timers, yasa);
            if (!successful) {
                faultyCount.addAndGet(1);
            }

            if (PRINT_SOLUTION_AND_CONFIGURATION) {
                System.out.println("############## SOLUTION END ################");
            }
        });
        System.out.println("Done solution analysis, faulty operations=" + faultyCount.get() + "...");

        System.out.println("Building new solutions...");

        var newSample = RepairOperations.buildNewSample(yasa, timers, monitor, PRINT_NEW_SAMPLE);
        
        var newValidOnlySolutions = RepairOperations.filterSolutionList(newSample, timers, evoSet.repEvo1, cnfEvo1);

        timers.startTimer(TimerCollection.TimerType.CALCULATE_COVERAGE);
        System.out.println(
                "\nNEW COVERAGE = " + RepairOperations.calculateCoverage(cnfEvo1, newValidOnlySolutions) + " | Old Coverage = "
                        + oldCoverage + "\n");
        timers.stopAndAddTimer(TimerCollection.TimerType.CALCULATE_COVERAGE);

        EntityPrinter.printStats(cnfEvo0, cnfEvo1, counterZeros, counterNonZeros, evoSet.repEvo0Sample, newValidOnlySolutions);
        EntityPrinter.printTimers(timers);
    }


}
