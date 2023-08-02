package de.featjar.assignment.ma;

import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.analysis.sat4j.twise.YASA;
import de.featjar.clauses.CNF;
import de.featjar.clauses.CNFProvider;
import de.featjar.formula.structure.Formula;
import de.featjar.repair.*;
import de.featjar.repair.DataLoader.Dataset2;
import de.featjar.util.extension.ExtensionLoader;
import de.featjar.util.job.NullMonitor;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicLong;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

public class EvolutionTest {

    private static final Dataset2 DATASET_2 = Dataset2.BUSYBOX_BEGIN;
    private static final List<DataLoader.DatasetN> DATASET_N = List.of(DataLoader.DatasetN.BUSYBOX_2018);
    private static final String absolutPathPrefix = "./src/test/resources/";
    private static final boolean PRINT_CNFS = false;
    private static final boolean PRINT_CONFIG_EXTENDED = false;
    private static final boolean PRINT_SOLUTION_AND_CONFIGURATION = false;
    private static final boolean PRINT_NEW_SAMPLE = false;
    private static final boolean THROW_OUT_FAILING_CONFIGS = false;


    private static EvolutionSet2 evoSet;
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

        //evoSet = DataLoader.getEvolutionSet(DATASET_2, absolutPathPrefix);
        var evoSetN = DataLoader.getEvolutionSetN(DATASET_N, 2, absolutPathPrefix);
        var sampleEvo0 = EntityPrinter.generateValidTWiseConfigurations(2, evoSetN.get().repEvos[0]);
        evoSet = new EvolutionSet2(evoSetN.get().repEvos[0],evoSetN.get().repEvos[1], sampleEvo0);
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
        oldCoverage = RepairOperations.calculateCoverage(cnfEvo0, evoSet.repEvo0Sample, 2);
        System.out.println("\nOLD COVERAGE (Should be 1.0) = " + oldCoverage + "\n");

        System.out.println("Initializing Yasa...");
        yasa = new YASA();
        yasa.setSolver(new Sat4JSolver(cnfEvo1));
        yasa.setT(2);
        monitor = new NullMonitor();
        yasa.init2(monitor);
        timers.stopAndAddTimer(TimerCollection.TimerType.CREATE_YASA);
    }

    @Test
    public void testGenerateSample() {

        AtomicLong timerTwiseYasa = new AtomicLong(System.nanoTime());
        var yasa = new YASA();
        yasa.setSolver(new Sat4JSolver(cnfEvo1));
        monitor = new NullMonitor();
        yasa.init2(monitor);
        yasa.setT(2);
        AtomicLong timerTwiseYasaBuild = new AtomicLong(System.nanoTime());
        yasa.buildConfigurations(monitor);
        long buildTime = System.nanoTime() - timerTwiseYasaBuild.get();
        var newSample = StreamSupport.stream(yasa, false)
                .collect(Collectors.toCollection(ArrayList::new));
        System.out.println(
                "BuildTime= " + ( buildTime / 1e9) + " s | YASATimer generate complete new Twise Sample [size=" + newSample.size() + "] = " + ((System.nanoTime() - timerTwiseYasa.get())
                        / 1e9) + " s");

        /*
        AtomicLong timerTwise = new AtomicLong(System.nanoTime());
        TWiseConfigurationGenerator twisegen = new TWiseConfigurationGenerator();
        twisegen.setT(2);
        twisegen.setIterations(1);
        twisegen.setRandom(new Random(1234));

        System.out.println(
                "NONYASATimer generate complete new Twise Sample [size=" + evoSet.repEvo1.get(twisegen).getSolutions().size() + "] = " + ((System.nanoTime() - timerTwise.get())
                        / 1e9) + " s");


        AtomicLong timerTwise = new AtomicLong(System.nanoTime());
        EntityPrinter.generateValidTWiseConfigurations(evoSet.repEvo1);
        System.out.println("\n+++++++++++++++++++++++++\n");
        System.out.println(
                "Timer generate complete new Twise Sample = " + ((System.nanoTime() - timerTwise.get())
                        / 1e9) + " s");
        System.out.println("\n+++++++++++++++++++++++++\n");

         */
    }

    @Test
    public void testRepairSample() {
        AtomicLong counterZeros = new AtomicLong();
        AtomicLong counterNonZeros = new AtomicLong();
        AtomicLong faultyCount = new AtomicLong();
        System.out.println(
                "Starting solution analysis (solution count=" + evoSet.repEvo0Sample.getSolutions().size()
                        + ")...");

        timers.startTimer(TimerCollection.TimerType.CREATE_YASA);
        System.out.println("Initializing Yasa...");
        yasa = new YASA();
        yasa.setSolver(new Sat4JSolver(cnfEvo1));
        monitor = new NullMonitor();
        yasa.init2(monitor);
        timers.stopAndAddTimer(TimerCollection.TimerType.CREATE_YASA);
        evoSet.repEvo0Sample.getSolutions().forEach(s -> {

            if (PRINT_SOLUTION_AND_CONFIGURATION) {
                System.out.println("############# SOLUTION START ###############");
            }
            var remappedConfig = RepairOperations.remapOldIndexesViaNames(s, timers, cnfEvo0, cnfEvo1);

            if (PRINT_CONFIG_EXTENDED) {
                System.out.println("OLD CONFIG");
                EntityPrinter.printConfigurationWithName(s.getLiterals(), cnfEvo0);
                System.out.println("NEXT CONFIG");
                EntityPrinter.printConfigurationWithName(remappedConfig, cnfEvo1);
            }

            var successful = RepairOperations.createNewConfigurationsWithYasa(remappedConfig, timers, yasa, evoSet.repEvo1, counterZeros, counterNonZeros, THROW_OUT_FAILING_CONFIGS);
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
                "\nNEW COVERAGE = " + RepairOperations.calculateCoverage(cnfEvo1, newValidOnlySolutions, 2) + " | Old Coverage = "
                        + oldCoverage + "\n");
        timers.stopAndAddTimer(TimerCollection.TimerType.CALCULATE_COVERAGE);

        EntityPrinter.printStats(cnfEvo0, cnfEvo1, counterZeros, counterNonZeros, evoSet.repEvo0Sample, newValidOnlySolutions);
        EntityPrinter.printTimers(timers);
    }


}
