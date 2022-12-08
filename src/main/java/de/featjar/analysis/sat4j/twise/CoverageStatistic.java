/*
 * Copyright (C) 2022 Sebastian Krieter
 *
 * This file is part of formula-analysis-sat4j.
 *
 * formula-analysis-sat4j is free software: you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3.0 of the License,
 * or (at your option) any later version.
 *
 * formula-analysis-sat4j is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with formula-analysis-sat4j. If not, see <https://www.gnu.org/licenses/>.
 *
 * See <https://github.com/FeatJAR/formula-analysis-sat4j> for further information.
 */
package de.featjar.analysis.sat4j.twise;

/**
 * Holds statistics regarding coverage of a configuration sample.
 *
 * @author Sebastian Krieter
 */
public class CoverageStatistic {

    protected long numberOfValidConditions;
    protected long numberOfInvalidConditions;
    protected long numberOfCoveredConditions;
    protected long numberOfUncoveredConditions;

    protected double[] configScores;

    protected void initScores(int sampleSize) {
        configScores = new double[sampleSize];
    }

    protected void setScore(int index, double score) {
        configScores[index] = score;
    }

    protected void addToScore(int index, double score) {
        configScores[index] += score;
    }

    protected double getScore(int index) {
        return configScores[index];
    }

    public double[] getConfigScores() {
        return configScores;
    }

    public void setNumberOfValidConditions(long numberOfValidConditions) {
        this.numberOfValidConditions = numberOfValidConditions;
    }

    public void setNumberOfInvalidConditions(long numberOfInvalidConditions) {
        this.numberOfInvalidConditions = numberOfInvalidConditions;
    }

    public void setNumberOfCoveredConditions(long numberOfCoveredConditions) {
        this.numberOfCoveredConditions = numberOfCoveredConditions;
    }

    public void setNumberOfUncoveredConditions(long numberOfUncoveredConditions) {
        this.numberOfUncoveredConditions = numberOfUncoveredConditions;
    }

    public void incNumberOfValidConditions() {
        numberOfValidConditions++;
    }

    public void incNumberOfInvalidConditions() {
        numberOfInvalidConditions++;
    }

    public void incNumberOfCoveredConditions() {
        numberOfCoveredConditions++;
    }

    public void incNumberOfUncoveredConditions() {
        numberOfUncoveredConditions++;
    }

    public long getNumberOfValidConditions() {
        return numberOfValidConditions;
    }

    public long getNumberOfInvalidConditions() {
        return numberOfInvalidConditions;
    }

    public long getNumberOfCoveredConditions() {
        return numberOfCoveredConditions;
    }

    public long getNumberOfUncoveredConditions() {
        return numberOfUncoveredConditions;
    }

    public double getCoverage() {
        if (numberOfValidConditions != 0) {
            return (double) numberOfCoveredConditions / (double) numberOfValidConditions;
        } else {
            if (numberOfInvalidConditions == 0) {
                return (double) numberOfCoveredConditions
                        / (double) (numberOfCoveredConditions + numberOfUncoveredConditions);
            } else {
                return 1.0;
            }
        }
    }
}
