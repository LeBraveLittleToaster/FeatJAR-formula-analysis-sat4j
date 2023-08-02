package de.featjar.repair;

import java.util.Comparator;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.stream.Collectors;

public class TimerCollection {

    public enum TimerType {

        REMAPPING(1, true),
        REDUCE_TO_VALID_ONLY(3, true),
        NEXT_CONFIGURATION(5, true),
        NEW_CONFIGURATION(6, true),
        BUILD_CONFIGURATIONS(7, true),
        CREATE_INITIAL_SAMPLE(1, false),
        CREATE_YASA(2, false),
        CALCULATE_COVERAGE(100, false),
        HAS_SOLUTION_ANALYSIS(5, false),
        CHECK_CONFIGURATION(1000, false),
        CREATE_EVOLUTION_SAMPLE(6, false); // included in NEXT_CONFIGURATION
        public final int printOrder;
        public final boolean addToTotalTime;

        private TimerType(int printOrder, boolean addToTotalTime) {
            this.printOrder = printOrder;
            this.addToTotalTime = addToTotalTime;
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

