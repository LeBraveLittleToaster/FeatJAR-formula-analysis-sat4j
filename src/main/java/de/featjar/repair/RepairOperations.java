package de.featjar.repair;

import de.featjar.analysis.sat4j.HasSolutionAnalysis;
import de.featjar.analysis.sat4j.solver.Sat4JSolver;
import de.featjar.analysis.sat4j.twise.*;
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
import de.featjar.util.logging.Logger;

import javax.print.attribute.standard.MediaSize;
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

    public static SolutionList filterSolutionList(List<LiteralList> newSample, TimerCollection timers, TimerCollection.TimerType timerType, ModelRepresentation repEvo1, CNF cnfEvo1) {
        timers.startTimer(timerType);
        var newSolutions = new SolutionList(repEvo1.getVariables(), newSample);
        var newValidSolutionList = new SolutionList(repEvo1.getVariables(), newSolutions.getValidSolutions(cnfEvo1)
                .collect(Collectors.toList()));
        timers.stopAndAddTimer(timerType);
        return newValidSolutionList;
    }

    public static ArrayList<LiteralList> buildNewSample(YASA yasa, TimerCollection timers, InternalMonitor monitor, boolean printNewSample) {
        timers.startTimer(TimerCollection.TimerType.BUILD_CONFIGURATIONS);
        yasa.buildConfigurations(monitor);
        var newSample = StreamSupport.stream(yasa, false)
                .collect(Collectors.toCollection(ArrayList::new));
        timers.stopAndAddTimer(TimerCollection.TimerType.BUILD_CONFIGURATIONS);

        if (printNewSample) {
            Logger.logInfo("\nNEW SAMPLE");
            Logger.logInfo(newSample);
        }
        return newSample;
    }

    public static boolean createNewConfigurationsWithYasa(int[] remappedConfig, TimerCollection timers, YASA yasa, ModelRepresentation repEvo, AtomicLong counterZeros, AtomicLong counterNonZeros, boolean THROW_OUT_FAILING_CONFIGS) {
        timers.startTimer(TimerCollection.TimerType.REPAIR_AND_NEXT_CALL_CONFIGURATION);
        var nextConfiguration = IntStream.of(remappedConfig).filter(i -> i != 0).toArray();

        var maybeNullifiedConfigOpt = RepairOperations.validateOldSampleAgainstEvo1(nextConfiguration, timers, repEvo.getFormula(), repEvo, THROW_OUT_FAILING_CONFIGS, false);
        if (maybeNullifiedConfigOpt.isEmpty()) {
            return false;
        } else {
            int[] configAsArr = maybeNullifiedConfigOpt.get().getAll().stream().mapToInt(p -> (boolean)p.getValue() ? p.getKey() : -p.getKey()).toArray();
            yasa.newConfiguration(configAsArr);
        }

        //RepairOperations.countZerosInConfigurations(counterZeros, counterNonZeros, maybeNullifiedConfig);

        timers.stopAndAddTimer(TimerCollection.TimerType.REPAIR_AND_NEXT_CALL_CONFIGURATION);

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

    public static Optional<IndexAssignment> validateOldSampleAgainstEvo1(int[] remappedConfig, TimerCollection timers, Formula formulaEvo, ModelRepresentation repEvo, boolean THROW_OUT_FAILING_CONFIGS, boolean printSolutionAndConfiguration) {
        timers.startTimer(TimerCollection.TimerType.REPAIR_CONFIGURATION);
        var maybeNullifiedConfig = validateEvo0ConfigWithEvo1(formulaEvo, repEvo, remappedConfig, timers, THROW_OUT_FAILING_CONFIGS, printSolutionAndConfiguration);
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

            if (oldVarIndex > oldConfigurationWithZeros.getVariables().size()) {
                continue;
            }

            // otherwise add the old value to the new assignment
            var oldValue = oldConfigurationWithZeros.get(oldVarIndex - 1);
            nextAssignment.add(oldValue > 0 ? nextIndex : -nextIndex);
        }
        return nextAssignment.stream().mapToInt(i -> i).toArray();
    }

    static Optional<IndexAssignment> validateEvo0ConfigWithEvo1(Formula formula, ModelRepresentation repEvo, int[] config, TimerCollection timers, boolean THROW_OUT_FAILING_CONFIGS, boolean printSolutionAndConfiguration) {
        var indexAssignment = buildIndexAssignment(config, false);
        Optional<Object> isFormulaValidOpt = Formulas.evaluate(formula, indexAssignment);

        if (isFormulaValidOpt.isEmpty()) {
            if (THROW_OUT_FAILING_CONFIGS) {
                return Optional.empty();
            }
            if (!useHasSolutionAnalysis(timers, indexAssignment, repEvo)) {
                return Optional.empty();
            }
        }else {
            var isFormulaValid = (boolean) isFormulaValidOpt.get();
            if (isFormulaValid) return Optional.of(indexAssignment);
        }

        var nullifiedIndex = buildIndexAssignment(nullifyErrors(formula, config, indexAssignment), true);
        if(useHasSolutionAnalysis(timers, nullifiedIndex, repEvo)){
            return Optional.of(nullifiedIndex);
        }
        return Optional.empty();
    }

    private static IndexAssignment buildIndexAssignment(int[] config, boolean filterZero) {
        IndexAssignment indexAssignment = new IndexAssignment();
        for (int l : config) {
            if(filterZero && l != 0) {
                indexAssignment.set(Math.abs(l), l > 0);
            }
        }
        return indexAssignment;
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
