package de.featjar.repair;

import de.featjar.clauses.LiteralList;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.formula.ModelRepresentation;

import java.util.Optional;

public class EvolutionSetN {
    public final ModelRepresentation[] repEvos;
    public final SolutionList evo0Sample;

    public EvolutionSetN(ModelRepresentation[] repEvos, SolutionList evo0Sample) {
        this.repEvos = repEvos;
        this.evo0Sample = evo0Sample;
    }

    public Optional<EvolutionSet2> tryGetEvolutionSet2(int i, int t, SolutionList oldSample) {
        return repEvos.length >= 2 && i >= 0 && i + 1 < repEvos.length ?
                Optional.of(oldSample != null ? EvolutionSet2.createWithoutSample(repEvos[i], repEvos[i + 1], oldSample) : EvolutionSet2.createWithSample(repEvos[i], repEvos[i + 1], t))
                : Optional.empty();
    }
}
