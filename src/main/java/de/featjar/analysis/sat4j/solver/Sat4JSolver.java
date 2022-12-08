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
package de.featjar.analysis.sat4j.solver;

import de.featjar.analysis.sat4j.solver.SStrategy.FixedStrategy;
import de.featjar.analysis.sat4j.solver.SStrategy.InverseFixedStrategy;
import de.featjar.analysis.sat4j.solver.SStrategy.MIGRandomStrategy;
import de.featjar.analysis.sat4j.solver.SStrategy.UniformRandomStrategy;
import de.featjar.analysis.sat4j.solver.strategy.FixedLiteralSelectionStrategy;
import de.featjar.analysis.sat4j.solver.strategy.FixedOrderHeap;
import de.featjar.analysis.sat4j.solver.strategy.FixedOrderHeap2;
import de.featjar.analysis.sat4j.solver.strategy.RandomSelectionStrategy;
import de.featjar.analysis.sat4j.solver.strategy.ReverseFixedLiteralSelectionStrategy;
import de.featjar.analysis.sat4j.solver.strategy.UniformRandomSelectionStrategy;
import de.featjar.clauses.CNF;
import de.featjar.clauses.LiteralList;
import de.featjar.formula.structure.atomic.literal.VariableMap;
import java.util.List;
import java.util.Random;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.minisat.core.IOrder;
import org.sat4j.minisat.core.Solver;
import org.sat4j.minisat.orders.NegativeLiteralSelectionStrategy;
import org.sat4j.minisat.orders.PositiveLiteralSelectionStrategy;
import org.sat4j.minisat.orders.RSATPhaseSelectionStrategy;
import org.sat4j.minisat.orders.VarOrderHeap;

/**
 * Sat solver using Sat4J.
 *
 * @author Sebastian Krieter
 */
public class Sat4JSolver extends AbstractSat4JSolver<Solver<?>> {

    protected final int[] order;
    protected SStrategy strategy;

    public Sat4JSolver(CNF cnf) {
        super(cnf);
        strategy = SStrategy.original();
        order = new int[cnf.getVariableMap().getVariableCount()];
        setOrderFix();
    }

    public Sat4JSolver(VariableMap variableMap) {
        super(variableMap);
        strategy = SStrategy.original();
        order = new int[variableMap.getVariableCount()];
        setOrderFix();
    }

    @Override
    protected Solver<?> createSolver() {
        return (Solver<?>) SolverFactory.newDefault();
    }

    @Override
    protected void initSolver(List<LiteralList> clauses) {
        super.initSolver(clauses);
        solver.getOrder().init();
    }

    public int[] getOrder() {
        return order;
    }

    public SStrategy getSelectionStrategy() {
        return strategy;
    }

    public void setOrder(int[] order) {
        assert order.length <= this.order.length;
        System.arraycopy(order, 0, this.order, 0, order.length);
    }

    public void setOrderFix() {
        for (int i = 0; i < order.length; i++) {
            order[i] = i + 1;
        }
    }

    public void shuffleOrder() {
        shuffleOrder(new Random());
    }

    public void shuffleOrder(Random rnd) {
        for (int i = order.length - 1; i >= 0; i--) {
            final int index = rnd.nextInt(i + 1);
            final int a = order[index];
            order[index] = order[i];
            order[i] = a;
        }
    }

    private void setSelectionStrategy(IOrder strategy) {
        solver.setOrder(strategy);
        solver.getOrder().init();
    }

    public void setSelectionStrategy(SStrategy strategy) {
        this.strategy = strategy;
        switch (strategy.strategy()) {
            case FastRandom:
                setSelectionStrategy(new FixedOrderHeap(new RandomSelectionStrategy(), order));
                break;
            case Fixed:
                setSelectionStrategy(
                        new FixedOrderHeap( //
                                new FixedLiteralSelectionStrategy(((FixedStrategy) strategy).getModel()), //
                                order));
                break;
            case InverseFixed:
                setSelectionStrategy(
                        new FixedOrderHeap( //
                                new ReverseFixedLiteralSelectionStrategy(((InverseFixedStrategy) strategy).getModel()), //
                                order));
                break;
            case MIGRandom:
                setSelectionStrategy(new FixedOrderHeap2(
                        new UniformRandomSelectionStrategy(((MIGRandomStrategy) strategy).getDist()), order));
                break;
            case Negative:
                setSelectionStrategy(new FixedOrderHeap(new NegativeLiteralSelectionStrategy(), order));
                break;
            case Original:
                setSelectionStrategy(new VarOrderHeap(new RSATPhaseSelectionStrategy()));
                break;
            case Positive:
                setSelectionStrategy(new FixedOrderHeap(new PositiveLiteralSelectionStrategy(), order));
                break;
            case UniformRandom:
                setSelectionStrategy(new FixedOrderHeap2(
                        new UniformRandomSelectionStrategy(((UniformRandomStrategy) strategy).getDist()), order));
                break;
            default:
                throw new IllegalStateException(String.valueOf(strategy.strategy()));
        }
    }
}
