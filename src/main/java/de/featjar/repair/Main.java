package de.featjar.repair;

import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.analysis.sat4j.twise.YASA;
import de.featjar.clauses.CNF;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.util.extension.ExtensionLoader;
import de.featjar.util.job.InternalMonitor;
import de.featjar.util.job.NullMonitor;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.atomic.AtomicLong;

public class Main {

    public static void main(String[] args) throws IOException {
        var main = new Main();
        main.run();
    }

    private static final DataLoader.Dataset2 DATASET_2 = DataLoader.Dataset2.BUSYBOX_BEGIN;
    private static final List<DataLoader.DatasetN> DATASET_N = List.of(
            DataLoader.DatasetN.BUSYBOX_2018, DataLoader.DatasetN.BUSYBOX_2019);
    private static final int T_WISE_T = 2;
    private static final String absolutPathPrefix = "./formula-analysis-sat4j/src/main/resources/";
    private static final String absolutFolderPrefix = "./formula-analysis-sat4j/src/main/resources/MA_PS/busybox-dayli/";
    private static final boolean PRINT_CNFS = false;
    private static final boolean PRINT_CONFIG_EXTENDED = false;
    private static final boolean PRINT_SOLUTION_AND_CONFIGURATION = false;
    private static final boolean PRINT_NEW_SAMPLE = false;
    private static final boolean THROW_OUT_FAILING_CONFIGS = false;

    public void run() throws IOException {
        ExtensionLoader.load();
        var timerList = new LinkedList<TimerCollection>();

        var evoSetNOpt = DataLoader.getEvolutionSetNInFolderWithSameName("clean.dimacs", 2, absolutFolderPrefix);
        if(evoSetNOpt.isEmpty()){
            System.out.println("Is empty");
            return;
        }

        //var evoSetNOpt = DataLoader.getEvolutionSetN(DATASET_N, 2, absolutPathPrefix);
        //if(evoSetNOpt.isEmpty()) throw new RuntimeException("failed to load evolutionset!");
        var evoSetN = evoSetNOpt.get();

        var curI = 0;
        SolutionList curSample = null;
        for(int i = 0; i + 1 < evoSetN.repEvos.length; i++){
            var timers = new TimerCollection();
            var monitor = new NullMonitor();



            var curEvoSetOpt = curSample == null ?
                    evoSetN.tryGetEvolutionSet2(curI, T_WISE_T, null, timers) :
                    evoSetN.tryGetEvolutionSet2(curI, T_WISE_T, curSample, timers);

            if(curEvoSetOpt.isEmpty()) {
                System.err.println("failed to get evoset2!");
                continue;
            }
            var evoSet2 = curEvoSetOpt.get();

            System.out.println("Generating test sample for time evaluation");
            timers.startTimer(TimerCollection.TimerType.CREATE_EVOLUTION_SAMPLE);
            var rslt = EntityPrinter.generateValidTWiseConfigurations(T_WISE_T, evoSet2.repEvo1);
            timers.stopAndAddTimer(TimerCollection.TimerType.CREATE_EVOLUTION_SAMPLE);
            System.out.println("New sample size = " + rslt.getSolutions().size());

            System.out.println("Calculating coverage...");
            var oldCoverage = RepairOperations.calculateCoverage(evoSet2.repEvo0CNF, evoSet2.repEvo0Sample, T_WISE_T);
            System.out.println("\nOLD COVERAGE (Should be 1.0) = " + oldCoverage + "\n");

            var yasa = createYasa(monitor, evoSet2.repEvo1CNF, T_WISE_T, timers);
            curSample = testRepairSample(evoSet2, yasa, monitor, oldCoverage, timers);
            curI++;
            timerList.add(timers);
        }
    }

    private static YASA createYasa(InternalMonitor monitor, CNF cnf, int t, TimerCollection timers){
        System.out.println("Initializing Yasa...");
        timers.startTimer(TimerCollection.TimerType.CREATE_YASA_INSTANCE);
        var yasa = new YASA();
        yasa.setSolver(new Sat4JSolver(cnf));
        yasa.setT(t);
        yasa.init2(monitor);
        timers.stopAndAddTimer(TimerCollection.TimerType.CREATE_YASA_INSTANCE);
        return yasa;
    }


    public SolutionList testRepairSample(EvolutionSet2 evoSet, YASA yasa, InternalMonitor monitor, double oldCoverage, TimerCollection timers) {
        AtomicLong counterZeros = new AtomicLong();
        AtomicLong counterNonZeros = new AtomicLong();
        AtomicLong faultyCount = new AtomicLong();
        System.out.println(
                "Starting solution analysis (solution count=" + evoSet.repEvo0Sample.getSolutions().size() + ")...");


        evoSet.repEvo0Sample.getSolutions().forEach(s -> {

            if (PRINT_SOLUTION_AND_CONFIGURATION) {
                System.out.println("############# SOLUTION START ###############");
            }
            var remappedConfig = RepairOperations.remapOldIndexesViaNames(s, timers, evoSet.repEvo0CNF, evoSet.repEvo1CNF);

            if (PRINT_CONFIG_EXTENDED) {
                System.out.println("OLD CONFIG");
                EntityPrinter.printConfigurationWithName(s.getLiterals(), evoSet.repEvo0CNF);
                System.out.println("NEXT CONFIG");
                EntityPrinter.printConfigurationWithName(remappedConfig, evoSet.repEvo1CNF);
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

        var newValidOnlySolutions = RepairOperations.filterSolutionList(newSample, timers, evoSet.repEvo1, evoSet.repEvo1CNF);

        timers.startTimer(TimerCollection.TimerType.CALCULATE_COVERAGE);
        System.out.println(
                "\nNEW COVERAGE = " + RepairOperations.calculateCoverage(evoSet.repEvo1CNF, newValidOnlySolutions, T_WISE_T) + " | Old Coverage = "
                        + oldCoverage + "\n");
        timers.stopAndAddTimer(TimerCollection.TimerType.CALCULATE_COVERAGE);

        EntityPrinter.printStats(evoSet.repEvo0CNF, evoSet.repEvo1CNF, counterZeros, counterNonZeros, evoSet.repEvo0Sample, newValidOnlySolutions);
        EntityPrinter.printTimers(timers);

        return newValidOnlySolutions;
    }


}
