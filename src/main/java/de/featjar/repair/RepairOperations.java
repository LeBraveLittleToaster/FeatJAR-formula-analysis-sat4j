package de.featjar.repair;

import de.featjar.analysis.sat4j.HasSolutionAnalysis;
import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.analysis.sat4j.twise.*;
import de.featjar.analysis.solver.RuntimeContradictionException;
import de.featjar.clauses.CNF;
import de.featjar.clauses.Clauses;
import de.featjar.clauses.LiteralList;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.formula.ModelRepresentation;
import de.featjar.formula.structure.Formula;
import de.featjar.formula.structure.Formulas;
import de.featjar.formula.structure.atomic.Assignment;
import de.featjar.formula.structure.atomic.IndexAssignment;
import de.featjar.util.job.InternalMonitor;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicLong;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.StreamSupport;

public class RepairOperations {

    public static double calculateCoverage(CNF cnf, SolutionList solutionList, int t) {
        var util = new TWiseConfigurationUtil(cnf, new Sat4JSolver(cnf));
        var stat = new TWiseStatisticGenerator(util);

        var pcManager = new PresenceConditionManager(
                util.getDeadCoreFeatures(),
                solutionList.getVariableMap().getVariableCount(),
                TWiseConfigurationGenerator.convertLiterals(Clauses.getLiterals(cnf.getVariableMap())));
        var coverage = stat.getCoverage(List.of(solutionList.getSolutions()),
                pcManager.getGroupedPresenceConditions(), t
                , TWiseStatisticGenerator.ConfigurationScore.NONE, true);
        return coverage.get(0).getCoverage();
    }

    public static SolutionList filterSolutionList(ArrayList<LiteralList> newSample, TimerCollection timers, ModelRepresentation repEvo1, CNF cnfEvo1) {
        timers.startTimer(TimerCollection.TimerType.NEW_CONFIGURATION);
        var newSolutions = new SolutionList(repEvo1.getVariables(), newSample);
        var newValidSolutionList = new SolutionList(repEvo1.getVariables(), newSolutions.getValidSolutions(cnfEvo1)
                .collect(Collectors.toList()));
        timers.stopAndAddTimer(TimerCollection.TimerType.NEW_CONFIGURATION);
        return newValidSolutionList;
    }

    public static ArrayList<LiteralList> buildNewSample(YASA yasa, TimerCollection timers, InternalMonitor monitor, boolean printNewSample) {
        timers.startTimer(TimerCollection.TimerType.BUILD_CONFIGURATIONS);
        yasa.buildConfigurations(monitor);
        var newSample = StreamSupport.stream(yasa, false)
                .collect(Collectors.toCollection(ArrayList::new));
        timers.stopAndAddTimer(TimerCollection.TimerType.BUILD_CONFIGURATIONS);

        if (printNewSample) {
            System.out.println("\nNEW SAMPLE");
            System.out.println(newSample);
        }
        return newSample;
    }

    public static boolean createNewConfigurationsWithYasa(int[] remappedConfig, TimerCollection timers, YASA yasa, ModelRepresentation repEvo, AtomicLong counterZeros, AtomicLong counterNonZeros, boolean THROW_OUT_FAILING_CONFIGS) {
        timers.startTimer(TimerCollection.TimerType.REPAIR_AND_NEXT_CALL_CONFIGURATION);
        var nextConfiguration = IntStream.of(remappedConfig).filter(i -> i != 0).toArray();
        try {
            yasa.newConfiguration(nextConfiguration);
        } catch (RuntimeContradictionException e) {
            if (THROW_OUT_FAILING_CONFIGS) {
                return false;
            }
            var maybeNullifiedConfigOpt = RepairOperations.validateOldSampleAgainstEvo1(remappedConfig, timers, repEvo.getFormula(), repEvo, false);
            if (maybeNullifiedConfigOpt.isEmpty()) return false;
            var maybeNullifiedConfig = maybeNullifiedConfigOpt.get();
            RepairOperations.countZerosInConfigurations(counterZeros, counterNonZeros, maybeNullifiedConfig);
            try {
                yasa.newConfiguration(Arrays.stream(maybeNullifiedConfig).filter(i -> i != 0).toArray());
            } catch (RuntimeContradictionException e2Run) {
                return false;
            }
            return false;
        } finally {
            timers.stopAndAddTimer(TimerCollection.TimerType.REPAIR_AND_NEXT_CALL_CONFIGURATION);
        }
        return true;
    }

    public static int[] countZerosInConfigurations(AtomicLong counterZeros, AtomicLong counterNonZeros, int[] nextConfigurationWithZeros) {
        IntStream.of(nextConfigurationWithZeros).forEach(v -> {
            if (v == 0) {
                counterZeros.addAndGet(1);
            } else {
                counterNonZeros.addAndGet(1);
            }
        });
        return nextConfigurationWithZeros;
    }

    public static int[] remapOldIndexesViaNames(LiteralList s, TimerCollection timers, CNF cnfEvo0, CNF cnfEvo1) {
        timers.startTimer(TimerCollection.TimerType.REMAPPING);
        var remappedConfig = remapItemsByName(s, cnfEvo0, cnfEvo1);
        timers.stopAndAddTimer(TimerCollection.TimerType.REMAPPING);
        return remappedConfig;
    }

    public static Optional<int[]> validateOldSampleAgainstEvo1(int[] remappedConfig, TimerCollection timers, Formula formulaEvo, ModelRepresentation repEvo, boolean printSolutionAndConfiguration) {
        timers.startTimer(TimerCollection.TimerType.REPAIR_CONFIGURATION);
        var maybeNullifiedConfig = validateEvo0ConfigWithEvo1(formulaEvo, repEvo, remappedConfig, timers, printSolutionAndConfiguration);
        timers.stopAndAddTimer(TimerCollection.TimerType.REPAIR_CONFIGURATION);
        return maybeNullifiedConfig;
    }


    static int[] remapItemsByName(LiteralList oldConfigurationWithZeros, CNF cnfOld, CNF cnfNext) {
        var nextAssignment = new ArrayList<Integer>();
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
            int oldVarIndex = oldVarIndexOpt.get();
            // check if the old index appears in the oldConfig (if set to zero also not consider it)

            if(oldVarIndex > oldConfigurationWithZeros.getVariables().size()){
                continue;
            }

            // otherwise add the old value to the new assignment
            var oldValue = oldConfigurationWithZeros.get(oldVarIndex - 1);
            nextAssignment.add(oldValue > 0 ? nextIndex : -nextIndex);
        }
        return nextAssignment.stream().mapToInt(i -> i).toArray();
    }

    static Optional<int[]> validateEvo0ConfigWithEvo1(Formula formula, ModelRepresentation repEvo, int[] config, TimerCollection timers, boolean printSolutionAndConfiguration) {
        if (printSolutionAndConfiguration) {
            System.out.println(Arrays.toString(config));
        }
        IndexAssignment indexAssignment = new IndexAssignment();
        for (int l : config) {
            indexAssignment.set(Math.abs(l), l > 0);
        }

        Optional<Object> isFormulaValidOpt = Formulas.evaluate(formula, indexAssignment);
        if (printSolutionAndConfiguration) {
            System.out.println("Is configuration valid = " + isFormulaValidOpt);
        }
        if (isFormulaValidOpt.isEmpty()) {
            return useHasSolutionAnalysis(timers, indexAssignment, repEvo) ? Optional.of(nullifyErrors(formula, config, indexAssignment)) : Optional.empty();
        }
        boolean isFormulaValid = (boolean) isFormulaValidOpt.get();

        if (isFormulaValid) {
            return Optional.of(config);
        }

        return Optional.of(nullifyErrors(formula, config, indexAssignment));
    }

    private static boolean useHasSolutionAnalysis(TimerCollection timers, IndexAssignment indexAssignment, ModelRepresentation repEvo) {
        timers.startTimer(TimerCollection.TimerType.HAS_SOLUTION_ANALYSIS);
        HasSolutionAnalysis sat = new HasSolutionAnalysis();
        Assignment assumptions = sat.getAssumptions();
        indexAssignment.getAll().forEach(kv -> {
            assumptions.set(kv.getKey(), kv.getValue());
        });
        Boolean canBeValid = repEvo.get(sat);
        timers.stopAndAddTimer(TimerCollection.TimerType.HAS_SOLUTION_ANALYSIS);
        return canBeValid;
    }


    private static int[] nullifyErrors(Formula formula, int[] config, IndexAssignment indexAssignment) {
        formula.getChildren().forEach(clause -> {
            boolean isValid = (boolean) Formulas.evaluate(clause, indexAssignment).orElse(false);
            if (!isValid) {
                Formulas.getVariables(clause).forEach(variable -> {
                    var oldIndex = variable.getIndex() - 1;
                    if (oldIndex >= 0 && oldIndex < config.length) {
                        config[oldIndex] = 0;
                    }
                });
            }
        });
        return config;
    }
}
