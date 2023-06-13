package de.featjar.assignment;

import de.featjar.analysis.sat4j.twise.TWiseConfigurationGenerator;
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

  static void printStats(AtomicLong timerCounterCheckConfiguration,
      AtomicLong timerRemapping, AtomicLong timerNewConfiguration, AtomicLong timerBuildAndSample,
      AtomicLong counterZeros, AtomicLong counterNonZeros) {
    System.out.println("++++++++++++++++++++++++++++++++++++++++++++++");
    var totalTime =
        timerCounterCheckConfiguration.get() + timerRemapping.get() + timerNewConfiguration.get()
            + timerBuildAndSample.get();
    System.out.println("Timer total            = " + (totalTime / 1e6) + " ms\n");
    System.out.println(
        "Timer CheckConfig      = " + (timerCounterCheckConfiguration.get() / 1e6) + " ms");
    System.out.println("Timer Remappong        = " + (timerRemapping.get() / 1e6) + " ms");
    System.out.println("Timer New Config       = " + (timerNewConfiguration.get() / 1e6) + " ms");
    System.out.println("Timer Build and Sample = " + (timerBuildAndSample.get() / 1e6) + " ms");
    System.out.println();
    System.out.println("Configuration literals stats:");
    System.out.println("Total amount of literals = " + (counterZeros.get() + counterNonZeros.get()));
    System.out.println(
        "Amount set to zero       = " + counterZeros.get() + " of " + (counterZeros.get()
            + counterNonZeros.get()));
  }
}
