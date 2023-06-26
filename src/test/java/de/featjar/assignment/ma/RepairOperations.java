package de.featjar.assignment.ma;

import de.featjar.analysis.sat4j.ContradictionAnalysis;
import de.featjar.analysis.sat4j.HasSolutionAnalysis;
import de.featjar.analysis.sat4j.twise.YASA;
import de.featjar.analysis.solver.RuntimeContradictionException;
import de.featjar.assignment.DataLoader;
import de.featjar.clauses.CNF;
import de.featjar.clauses.LiteralList;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.formula.structure.Formula;
import de.featjar.formula.structure.Formulas;
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
            }
            {
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

    static Optional<int[]> validateOldSampleAgainstEvo1(int[] remappedConfig, TimerCollection timers, Formula formulaEvo, boolean printSolutionAndConfiguration) {
        timers.startTimer(TimerCollection.TimerType.CHECK_CONFIGURATION);
        var isValid = validateEvo0ConfigWithEvo1(formulaEvo, remappedConfig, printSolutionAndConfiguration);
        timers.stopAndAddTimer(TimerCollection.TimerType.CHECK_CONFIGURATION);
        return isValid;
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

    static Optional<int[]> validateEvo0ConfigWithEvo1(Formula formula, int[] s, boolean printSolutionAndConfiguration) {
        List<LiteralList> assumptions = new ArrayList<>();
        ContradictionAnalysis contra = new ContradictionAnalysis();

        if (printSolutionAndConfiguration) {
            System.out.println(Arrays.toString(s));
        }
        IndexAssignment a = new IndexAssignment();
        for (int l : s) {
            a.set(Math.abs(l), l > 0);
            assumptions.add(new LiteralList(l));
        }
        contra.setClauseList(assumptions);

        boolean isFormulaValid = (boolean) Formulas.evaluate(formula, a).orElse(false);
        if (printSolutionAndConfiguration) {

            System.out.println("Is configuration valid = " + isFormulaValid);
        }

        if (isFormulaValid) {
            return Optional.empty();
        }

        formula.getChildren().forEach(clause -> {
            boolean isValid = (boolean) Formulas.evaluate(clause, a).orElse(false);
            if (!isValid) {
                Formulas.getVariables(clause).forEach(variable -> {
                    var oldIndex = variable.getIndex() - 1;
                    if(oldIndex >= 0 && oldIndex < s.length) {
                        s[oldIndex] =0;
                    }
                });
            }
        });

        return Optional.of(s);
    }
}
