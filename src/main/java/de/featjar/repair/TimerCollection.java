package de.featjar.repair;

import java.util.Comparator;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.stream.Collectors;

public class TimerCollection {

    public enum TimerType {
        // ++++++++++++++++++INCLUDED TIMERS++++++++++++++
        REMAPPING(1, true, "Remapping of values from before evo"),
        REDUCE_TO_VALID_ONLY(3, true, "Reduction to only valid configs"),
        REPAIR_AND_NEXT_CALL_CONFIGURATION(5, true, "Repairing process"),
        NEW_CONFIGURATION(6, true, "Inserting config into yasa"),
        BUILD_CONFIGURATIONS(7, true, "Yasa building call"),

        // ++++++++++++++++++EXCLUDED TIMERS++++++++++++++
        CREATE_EVOLUTION_SAMPLE(0, false, "For comparison reason"),
        CREATE_INITIAL_SAMPLE(1, false, "initial sample only relevant in first step"),
        CREATE_YASA_INSTANCE(2, false, "same for evolution and non evolution"),
        CALCULATE_COVERAGE(100, false, "only needed for eval"),
        HAS_SOLUTION_ANALYSIS(5, false, "Included in REPAIR_CONFIGURATION" ),
        REPAIR_CONFIGURATION(1000, false, "Included in REPAIR_AND_NEXT...");
        public final int printOrder;
        public final boolean addToTotalTime;

        public final String description;

        private TimerType(int printOrder, boolean addToTotalTime, String description) {
            this.printOrder = printOrder;
            this.addToTotalTime = addToTotalTime;
            this.description = description;
        }
    }

    private final ConcurrentMap<TimerType, TestTimer> timers;

    public TimerCollection() {
        this.timers = new ConcurrentHashMap<>();
    }

    public void startTimer(TimerType timerType) {
        timers.compute(timerType, (type, testTimer) -> {
            if (testTimer == null) {
                var tt = new TestTimer();
                tt.startTimer();
                return tt;
            }
            testTimer.startTimer();
            return testTimer;
        });
    }

    public Optional<Long> stopAndAddTimer(TimerType timerType) {
        var timerTime = timers.get(timerType);
        return timerTime == null ? Optional.empty() : Optional.of(timerTime.stopTimer());
    }

    public List<Tuple<TimerType, Long>> getAllTimersOrdered() {
        return timers.entrySet().stream()
                .sorted(Comparator.comparingInt(c -> c.getKey().printOrder))
                .map((entry) -> new Tuple<>(entry.getKey(), entry.getValue().getTime()))
                .collect(Collectors.toList());
    }
}

