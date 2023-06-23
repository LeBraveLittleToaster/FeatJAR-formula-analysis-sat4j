package de.featjar.assignment;

import de.featjar.analysis.sat4j.twise.TWiseConfigurationGenerator;
import de.featjar.assignment.TimerCollection.TimerType;
import de.featjar.clauses.CNF;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.formula.ModelRepresentation;
import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;

public class EntityPrinter {

  static SolutionList generateValidTWiseConfigurations(ModelRepresentation rep) {
    TWiseConfigurationGenerator twisegen = new TWiseConfigurationGenerator();
    twisegen.setT(2);
    return rep.get(twisegen);
  }

  static void printCNF(CNF cnf) {
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

  static void printConfigurationWithName(int[] assignment, CNF cnf) {
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

  static void printStats(CNF cnfEvo0, CNF cnfEvo1, AtomicLong counterZeros,
      AtomicLong counterNonZeros) {

    System.out.println("++++++++++++++++++++++++++++++++++++++++++++++");
    System.out.println("Evolution Step 0:");
    System.out.println("Literals Count         = " + cnfEvo0.getVariableMap().getVariableCount());
    System.out.println("Clauses Count          = " + cnfEvo0.getClauses().size());
    System.out.println("\nEvolution Step 1:");
    System.out.println("Literals Count         = " + cnfEvo1.getVariableMap().getVariableCount());
    System.out.println("Clauses Count          = " + cnfEvo1.getClauses().size());
    System.out.println("++++++++++++++++++++++++++++++++++++++++++++++");
    System.out.println("Configuration literals stats:");
    System.out.println(
        "Total amount of literals = " + (counterZeros.get() + counterNonZeros.get()));
    System.out.println(
        "Amount set to zero       = " + counterZeros.get() + " of " + (counterZeros.get()
            + counterNonZeros.get()));
  }

  static void printTimers(TimerCollection timerCollection) {
    var longestEnumCharCount = new AtomicInteger(0);
    Arrays.stream(TimerType.values()).forEach(timerType -> {
      if (timerType.toString().length() > longestEnumCharCount.get()) {
        longestEnumCharCount.set(timerType.toString().length());
      }
    });

    AtomicLong totalTime = new AtomicLong(0L);
    var builder = new StringBuilder();
    builder.append("++++++++++++++++++++++++++++++++++++++++++++++\n");
    timerCollection.getAllTimers().forEach((entry) -> {
          totalTime.addAndGet(entry.y);
          builder
              .append(pad(entry.x.toString(), longestEnumCharCount.get() + 1, ' '))
              .append(" = ")
              .append((entry.y / 1e6))
              .append(" ms\n");
        }
    );
    builder.append("++++++++++++++++++++++++++++++++++++++++++++++\n")
        .append("Total time: ")
        .append(totalTime.get() / 1e6)
        .append(" ms\n")
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
