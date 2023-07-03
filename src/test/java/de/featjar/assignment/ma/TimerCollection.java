package de.featjar.assignment.ma;

import de.featjar.assignment.Tuple;

import java.util.Comparator;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.stream.Collectors;

public class TimerCollection {

    public enum TimerType {
        CHECK_CONFIGURATION(1, true),
        REMAPPING(2, true),
        REDUCE_TO_VALID_ONLY(3, true),
        NEXT_CONFIGURATION(5, true),
        NEW_CONFIGURATION(6, true),
        BUILD_CONFIGURATIONS(7, true),
        CALCULATE_COVERAGE(8, true),
        HAS_SOLUTION_ANALYSIS(1, false);
        public final int printOrder;
        public final boolean addToTotalTime;

        private TimerType(int printOrder, boolean addToTotalTime) {
            this.printOrder = printOrder;this.addToTotalTime = addToTotalTime;
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

class TestTimer {

    private AtomicLong startTimeNano;
    private AtomicBoolean isRunning = new AtomicBoolean(false);

    private final AtomicLong accumulatedTimeNano = new AtomicLong(0);

    public void startTimer() {
        if (isRunning.get()) {
            System.out.println("Cannot start timer, already running!");
            return;
        }
        startTimeNano = new AtomicLong(System.nanoTime());
        isRunning.set(true);
    }

    public long stopTimer() {
        if (!isRunning.get()) {
            System.out.println("No timer running!");
        }
        isRunning.set(false);
        return accumulatedTimeNano.addAndGet(System.nanoTime() - startTimeNano.get());
    }

    public long getTime() {
        return accumulatedTimeNano.get();
    }
}

