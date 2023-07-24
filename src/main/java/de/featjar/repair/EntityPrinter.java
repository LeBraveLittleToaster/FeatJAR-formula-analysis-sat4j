package de.featjar.repair;

import de.featjar.analysis.sat4j.twise.TWiseConfigurationGenerator;
import de.featjar.repair.TimerCollection.TimerType;
import de.featjar.clauses.CNF;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.formula.ModelRepresentation;

import java.util.Arrays;
import java.util.Random;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;

public class EntityPrinter {

    public static SolutionList generateValidTWiseConfigurations(ModelRepresentation rep) {
        TWiseConfigurationGenerator twisegen = new TWiseConfigurationGenerator();
        twisegen.setT(2);
        twisegen.setRandom(new Random(1234));
        return rep.get(twisegen);
    }

    public static void printCNF(CNF cnf) {
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
        System.out.println(builder);
    }

    public static void printStats(CNF cnfEvo0, CNF cnfEvo1, AtomicLong counterZeros,
                                  AtomicLong counterNonZeros, SolutionList evo0Solutions, SolutionList evo1Solutions) {

        System.out.println("++++++++++++++++++++++++++++++++++++++++++++++");
        System.out.println("Evolution Step 0:");
        System.out.println("Sample size            = " + evo0Solutions.getSolutions().size());
        System.out.println("Literals Count         = " + cnfEvo0.getVariableMap().getVariableCount());
        System.out.println("Clauses Count          = " + cnfEvo0.getClauses().size());
        System.out.println("\nEvolution Step 1:");
        System.out.println("Sample size            = " + evo1Solutions.getSolutions().size());
        System.out.println("Literals Count         = " + cnfEvo1.getVariableMap().getVariableCount());
        System.out.println("Clauses Count          = " + cnfEvo1.getClauses().size());
        System.out.println("++++++++++++++++++++++++++++++++++++++++++++++");
        System.out.println("Configuration literals stats:");
        System.out.println("Found no mapping for = " + (((long) cnfEvo0.getVariableMap().getVariableCount() * evo0Solutions.getSolutions().size()) - (counterZeros.get() + counterNonZeros.get())));
        System.out.println(
                "Total amount of literals = " + (counterZeros.get() + counterNonZeros.get()));
        System.out.println(
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
        builder.append("+++++++++Total Time Timer Distribution++++++++\n");
        var indexTotalTime = new AtomicLong(1);
        timerCollection.getAllTimersOrdered().stream().filter(kv -> kv.x.addToTotalTime).forEach((entry) -> {
                    builder.append("[")
                            .append(indexTotalTime.get())
                            .append("] ")
                            .append(pad(entry.x.toString(), longestEnumCharCount.get() + 1, ' '))
                            .append(" = ")
                            .append((entry.y / 1e6))
                            .append(" ms\n");
                    indexTotalTime.incrementAndGet();
                }

        );
        builder.append("+++++++++++++++Additional Timers++++++++++++++\n");
        var indexAdditionalTimers = new AtomicLong(1);
        timerCollection.getAllTimersOrdered().stream().filter(kv -> !kv.x.addToTotalTime).forEach((entry) -> {
                    builder.append("[")
                            .append(indexAdditionalTimers.get())
                            .append("] ")
                            .append(pad(entry.x.toString(), longestEnumCharCount.get() + 1, ' '))
                            .append(" = ")
                            .append((entry.y / 1e6))
                            .append(" ms\n");
                    indexAdditionalTimers.incrementAndGet();
                }

        );

        double timeInSeconds = timerCollection.getAllTimersOrdered().stream()
                .filter(kv -> kv.x.addToTotalTime)
                .mapToLong(kv -> kv.y)
                .sum()
                / 1e9d;
        builder.append("++++++++++++++++++++++++++++++++++++++++++++++\n")
                .append("Total time: ")
                .append(String.format("%.2f", timeInSeconds))
                .append(" s\n")
                .append("++++++++++++++++++++++++++++++++++++++++++++++\n");
        System.out.println(builder);
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
