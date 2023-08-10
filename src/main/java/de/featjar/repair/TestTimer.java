package de.featjar.repair;

import de.featjar.util.logging.Logger;

import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;

class TestTimer {

    private AtomicLong startTimeNano;
    private AtomicBoolean isRunning = new AtomicBoolean(false);

    private final AtomicLong accumulatedTimeNano = new AtomicLong(0);

    public void startTimer() {
        if (isRunning.get()) {
            Logger.logInfo("Cannot start timer, already running!");
            return;
        }
        startTimeNano = new AtomicLong(System.nanoTime());
        isRunning.set(true);
    }

    public long stopTimer() {
        if (!isRunning.get()) {
            Logger.logInfo("No timer running!");
        }
        isRunning.set(false);
        return accumulatedTimeNano.addAndGet(System.nanoTime() - startTimeNano.get());
    }

    public long getTime() {
        return accumulatedTimeNano.get();
    }
}


