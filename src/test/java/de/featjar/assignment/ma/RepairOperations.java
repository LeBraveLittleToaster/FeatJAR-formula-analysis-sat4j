package de.featjar.assignment.ma;

import de.featjar.analysis.sat4j.HasSolutionAnalysis;
import de.featjar.analysis.sat4j.twise.YASA;
import de.featjar.analysis.solver.RuntimeContradictionException;
import de.featjar.assignment.DataLoader;
import de.featjar.clauses.CNF;
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
    static SolutionList filterSolutionList(ArrayList<LiteralList> newSample, TimerCollection timers, DataLoader.EvolutionSet evoSet, CNF cnfEvo1) {
        timers.startTimer(TimerCollection.TimerType.NEW_CONFIGURATION);
        var newSolutions = new SolutionList(evoSet.repEvo1.getVariables(), newSample);
        var newValidSolutionList = new SolutionList(evoSet.repEvo1.getVariables(), newSolutions.getValidSolutions(cnfEvo1)
                .collect(Collectors.toList()));
        timers.stopAndAddTimer(TimerCollection.TimerType.NEW_CONFIGURATION);
        return newValidSolutionList;
    }

    static ArrayList<LiteralList> buildNewSample(YASA yasa, TimerCollection timers, InternalMonitor monitor, boolean printNewSample) {
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

    static boolean createNewConfigurationsWithYasa(int[] isValid, TimerCollection timers, YASA yasa) {
        timers.startTimer(TimerCollection.TimerType.NEXT_CONFIGURATION);
        var nextConfiguration = IntStream.of(isValid).filter(i -> i != 0).toArray();
        try {
            yasa.newConfiguration(nextConfiguration);
        }catch (RuntimeContradictionException e){
            return false;
        }finally{
            timers.stopAndAddTimer(TimerCollection.TimerType.NEXT_CONFIGURATION);
        }
        return true;
    }

    static int[] countZerosInConfigurations(AtomicLong counterZeros, AtomicLong counterNonZeros, int[] nextConfigurationWithZeros) {
        IntStream.of(nextConfigurationWithZeros).forEach(v -> {
            if (v == 0) {
                counterZeros.addAndGet(1);
            }else{
                counterNonZeros.addAndGet(1);
            }
        });
        return nextConfigurationWithZeros;
    }

    static int[] remapOldIndexesViaNames(LiteralList s, TimerCollection timers, CNF cnfEvo0, CNF cnfEvo1) {
        timers.startTimer(TimerCollection.TimerType.REMAPPING);
        var remappedConfig = remapItemsByName(IntStream.of(s.getLiterals()).toArray(), cnfEvo0, cnfEvo1);
        timers.stopAndAddTimer(TimerCollection.TimerType.REMAPPING);
        return remappedConfig;
    }

    static Optional<int[]> validateOldSampleAgainstEvo1(int[] remappedConfig, TimerCollection timers, Formula formulaEvo, ModelRepresentation repEvo, boolean printSolutionAndConfiguration) {
        timers.startTimer(TimerCollection.TimerType.CHECK_CONFIGURATION);
        var maybeNullifiedConfig = validateEvo0ConfigWithEvo1(formulaEvo, repEvo, remappedConfig, timers, printSolutionAndConfiguration);
        timers.stopAndAddTimer(TimerCollection.TimerType.CHECK_CONFIGURATION);
        return maybeNullifiedConfig;
    }


    static int[] remapItemsByName(int[] oldConfigurationWithZeros, CNF cnfOld, CNF cnfNext) {
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
        if(isFormulaValidOpt.isEmpty()) {
            return useHasSolutionAnalysis(timers,indexAssignment, repEvo) ? Optional.of(nullifyErrors(formula, config, indexAssignment)) : Optional.empty();
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
                    if(oldIndex >= 0 && oldIndex < config.length) {
                        config[oldIndex] =0;
                    }
                });
            }
        });
        return config;
    }
}
