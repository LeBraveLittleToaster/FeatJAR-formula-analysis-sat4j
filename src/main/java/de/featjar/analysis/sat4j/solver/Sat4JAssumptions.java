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
 * See <https://github.com/FeatureIDE/FeatJAR-formula-analysis-sat4j> for further information.
 */
package de.featjar.analysis.sat4j.solver;

import de.featjar.formula.structure.atomic.Assignment;
import de.featjar.formula.structure.atomic.literal.VariableMap;
import de.featjar.util.data.Pair;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import org.sat4j.core.VecInt;

/**
 * Assumptions for a {@link Sat4JSolver}.
 *
 * @author Sebastian Krieter
 */
public class Sat4JAssumptions implements Assignment {

    protected final VecInt assumptions;
    protected final VariableMap variables;

    public VecInt getAssumptions() {
        return assumptions;
    }

    public Sat4JAssumptions(VariableMap variables) {
        this.variables = variables;
        assumptions = new VecInt(variables.getVariableCount());
    }

    public void clear() {
        assumptions.clear();
    }

    public void clear(int newSize) {
        assumptions.shrinkTo(newSize);
    }

    public void ensureSize(int size) {
        assumptions.ensure(size);
    }

    public Integer pop() {
        final int topElement = assumptions.get(assumptions.size());
        assumptions.pop();
        return topElement;
    }

    public void pop(int count) {
        assumptions.shrinkTo(assumptions.size() - count);
    }

    public void push(int var) {
        assumptions.push(var);
    }

    public void pushAll(int[] vars) {
        assumptions.pushAll(new VecInt(vars));
    }

    public void replaceLast(int var) {
        assumptions.pop().unsafePush(var);
    }

    public void remove(int i) {
        assumptions.delete(i);
    }

    public void set(int index, int var) {
        assumptions.set(index, var);
    }

    public int size() {
        return assumptions.size();
    }

    public int[] asArray() {
        return Arrays.copyOf(assumptions.toArray(), assumptions.size());
    }

    public int[] asArray(int from) {
        return Arrays.copyOfRange(assumptions.toArray(), from, assumptions.size());
    }

    public int[] asArray(int from, int to) {
        return Arrays.copyOfRange(assumptions.toArray(), from, to);
    }

    public int peek() {
        return assumptions.get(assumptions.size() - 1);
    }

    public int peek(int i) {
        return assumptions.get(i);
    }

    @Override
    public void set(int variable, Object assignment) {
        if (assignment instanceof Boolean) {
            for (int i = 0; i < assumptions.size(); i++) {
                final int var = Math.abs(assumptions.unsafeGet(i));
                if (var == variable) {
                    assumptions.set(i, (Boolean) assignment ? var : -var);
                    return;
                }
            }
            assumptions.push((Boolean) assignment ? variable : -variable);
        } else if (assignment == null) {
            for (int i = 0; i < assumptions.size(); i++) {
                final int var = Math.abs(assumptions.unsafeGet(i));
                if (var == variable) {
                    assumptions.delete(i);
                    return;
                }
            }
        }
    }

    public void set(String name, Object assignment) {
        final int index = variables.getVariableIndex(name).orElse(-1);
        if (index > 0) {
            set(index, assignment);
        }
    }

    @Override
    public void unset(int index) {
        for (int i = 0; i < assumptions.size(); i++) {
            final int l = assumptions.unsafeGet(i);
            if (Math.abs(l) == index) {
                assumptions.delete(i);
                return;
            }
        }
    }

    @Override
    public void unsetAll() {
        assumptions.clear();
    }

    @Override
    public Optional<Object> get(int index) {
        for (int i = 0; i < assumptions.size(); i++) {
            final int l = assumptions.unsafeGet(i);
            if (Math.abs(l) == index) {
                return Optional.of(l);
            }
        }
        return Optional.empty();
    }

    public Optional<Object> get(String name) {
        final int index = variables.getVariableIndex(name).orElse(-1);
        return index > 0 ? get(index) : Optional.empty();
    }

    public VariableMap getVariables() {
        return variables;
    }

    @Override
    public List<Pair<Integer, Object>> getAll() {
        final List<Pair<Integer, Object>> map = new ArrayList<>();
        for (int i = 0; i < assumptions.size(); i++) {
            final int l = assumptions.unsafeGet(i);
            if (l != 0) {
                map.add(new Pair<>(Math.abs(l), l > 0));
            }
        }
        return map;
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        for (int i = 0; i < assumptions.size(); i++) {
            final int l = assumptions.get(i);
            sb.append(Math.abs(l));
            sb.append(": ");
            sb.append(l);
            sb.append("\n");
        }
        return sb.toString();
    }
}
