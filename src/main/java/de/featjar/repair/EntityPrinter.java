package de.featjar.repair;

import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.analysis.sat4j.twise.TWiseConfigurationGenerator;
import de.featjar.analysis.sat4j.twise.YASA;
import de.featjar.clauses.CNFProvider;
import de.featjar.clauses.LiteralList;
import de.featjar.repair.TimerCollection.TimerType;
import de.featjar.clauses.CNF;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.formula.ModelRepresentation;
import de.featjar.util.job.NullMonitor;
import de.featjar.util.logging.Logger;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Random;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

public class EntityPrinter {

    public static SolutionList generateValidTWiseConfigurations(int t, ModelRepresentation rep) {
        var yasa = new YASA();
        yasa.setT(t);
        yasa.setSolver(new Sat4JSolver(rep.get(CNFProvider.fromFormula())));
        var monitor = new NullMonitor();
        yasa.init2(monitor);
        yasa.buildConfigurations(monitor);
        var newSample = StreamSupport.stream(yasa, false)
                .collect(Collectors.toCollection(ArrayList::new));
        return new SolutionList(rep.getVariables(), newSample);
    }

    public static void printCNF(CNF cnf) {
        Logger.logInfo("++++++ CNF START +++++\n");
        AtomicInteger idx = new AtomicInteger(0);
        cnf.getClauses().forEach(clause -> {
            Logger.logInfo("[" + idx.getAndIncrement() + "] " + clause);
            for (int literal : clause.getLiterals()) {
                Logger.logInfo("\t" + cnf.getVariableMap().getVariableName(Math.abs(literal)).get());
            }
        });
        Logger.logInfo("\n++++++ CNF END +++++");
    }

    public static void printConfigurationWithName(int[] assignment, CNF cnf) {
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
        Logger.logInfo(builder);
    }

    public static void printStats(CNF cnfEvo0, CNF cnfEvo1, AtomicLong counterZeros,
                                  AtomicLong counterNonZeros, SolutionList evo0Solutions, SolutionList evo1Solutions) {

        Logger.logInfo("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
        Logger.logInfo("Evolution Step 0:");
        Logger.logInfo("Sample size            = " + evo0Solutions.getSolutions().size());
        Logger.logInfo("Literals Count         = " + cnfEvo0.getVariableMap().getVariableCount());
        Logger.logInfo("Clauses Count          = " + cnfEvo0.getClauses().size());
        Logger.logInfo("\nEvolution Step 1:");
        Logger.logInfo("Sample size            = " + evo1Solutions.getSolutions().size());
        Logger.logInfo("Literals Count         = " + cnfEvo1.getVariableMap().getVariableCount());
        Logger.logInfo("Clauses Count          = " + cnfEvo1.getClauses().size());
        Logger.logInfo("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
        Logger.logInfo("Configuration literals stats:");
        Logger.logInfo("Found no mapping for = " + (((long) cnfEvo0.getVariableMap().getVariableCount() * evo0Solutions.getSolutions().size()) - (counterZeros.get() + counterNonZeros.get())));
        Logger.logInfo(
                "Total amount of literals = " + (counterZeros.get() + counterNonZeros.get()));
        Logger.logInfo(
                "Amount set to zero       = " + counterZeros.get() + " of " + (counterZeros.get()
                        + counterNonZeros.get()));
    }

    public static void printTimers(TimerCollection timerCollection) {
        var longestEnumCharCount = new AtomicInteger(0);
        Arrays.stream(TimerType.values()).forEach(timerType -> {
            if (timerType.toString().length() > longestEnumCharCount.get()) {
                longestEnumCharCount.set(timerType.toString().length());
            }
        });
        var builder = new StringBuilder();
        builder.append("+++++++++++++++++++++++++++++++++++++Total Time Timer Distribution++++++++++++++++++++++++++++++++++++\n");
        var indexTotalTime = new AtomicLong(1);
        timerCollection.getAllTimersOrdered().stream().filter(kv -> kv.x.addToTotalTime).forEach((entry) -> {
                    builder.append("[")
                            .append(indexTotalTime.get())
                            .append("] ")
                            .append(pad(entry.x.toString(), longestEnumCharCount.get() + 1, ' '))
                            .append(" = ")
                            .append(pad(entry.y / 1e6 + " ms ", 14, ' '))
                            .append(" | Desc = ")
                            .append(entry.x.description)
                            .append("\n");
                    indexTotalTime.incrementAndGet();
                }

        );
        builder.append("+++++++++++++++++++++++++++++++++++++++++++Additional Timers++++++++++++++++++++++++++++++++++++++++++\n");
        var indexAdditionalTimers = new AtomicLong(1);
        timerCollection.getAllTimersOrdered().stream().filter(kv -> !kv.x.addToTotalTime).forEach((entry) -> {
                    builder.append("[")
                            .append(indexAdditionalTimers.get())
                            .append("] ")
                            .append(pad(entry.x.toString(), longestEnumCharCount.get() + 1, ' '))
                            .append(" = ")
                            .append(pad(entry.y / 1e6 + " ms ", 14, ' '))
                            .append(" | Desc = ")
                            .append(entry.x.description)
                            .append("\n");
                    indexAdditionalTimers.incrementAndGet();
                }

        );

        double timeInSeconds = timerCollection.getAllTimersOrdered().stream()
                .filter(kv -> kv.x.addToTotalTime)
                .mapToLong(kv -> kv.y)
                .sum()
                / 1e9d;
        builder.append("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n")
                .append("Total time: ")
                .append(String.format("%.2f", timeInSeconds))
                .append(" s\n")
                .append("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n");
        Logger.logInfo(builder);
    }

    static String pad(String input, int toSize, char padChar) {
        if (input.length() >= toSize) {
            return input;
        }
        StringBuilder padded = new StringBuilder(input);
        while (padded.length() < toSize) {
            padded.append(padChar);
        }
        return padded.toString();
    }
}
