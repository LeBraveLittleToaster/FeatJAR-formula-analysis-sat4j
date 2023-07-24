package de.featjar.repair;

import de.featjar.clauses.solutions.SolutionList;
import de.featjar.formula.ModelRepresentation;

import java.util.List;

public class NEvolutionSet {
    public final ModelRepresentation[] repEvos;
    public final SolutionList evo0Sample;

    public NEvolutionSet(ModelRepresentation[] repEvos, SolutionList evo0Sample) {
        this.repEvos = repEvos;
        this.evo0Sample = evo0Sample;
    }
}
