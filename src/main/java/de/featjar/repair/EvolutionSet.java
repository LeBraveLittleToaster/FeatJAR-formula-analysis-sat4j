package de.featjar.repair;

import de.featjar.clauses.solutions.SolutionList;
import de.featjar.formula.ModelRepresentation;

public class EvolutionSet {

    public final ModelRepresentation repEvo0;
    public final ModelRepresentation repEvo1;
    public final SolutionList repEvo0Sample;

    public EvolutionSet(ModelRepresentation repEvo0, ModelRepresentation repEvo1, SolutionList repEvo0Sample) {
        this.repEvo0 = repEvo0;
        this.repEvo1 = repEvo1;
        this.repEvo0Sample = repEvo0Sample;
    }
}
