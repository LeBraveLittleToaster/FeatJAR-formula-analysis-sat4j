package de.featjar.repair;

import de.featjar.clauses.CNF;
import de.featjar.clauses.CNFProvider;
import de.featjar.clauses.LiteralList;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.formula.ModelRepresentation;
import de.featjar.formula.structure.Formula;

public class EvolutionSet2 {

    public final ModelRepresentation repEvo0;
    public final ModelRepresentation repEvo1;
    public final SolutionList repEvo0Sample;
    public final CNF repEvo0CNF;
    public final CNF repEvo1CNF;
    public final Formula repEvo0Formula;
    public final Formula repEvo1Formula;

    public EvolutionSet2(ModelRepresentation repEvo0, ModelRepresentation repEvo1, SolutionList repEvo0Sample) {
        this.repEvo0 = repEvo0;
        this.repEvo1 = repEvo1;
        this.repEvo0Sample = repEvo0Sample;
        this.repEvo0CNF = repEvo0.get(CNFProvider.fromFormula());
        this.repEvo1CNF = repEvo1.get(CNFProvider.fromFormula());
        this.repEvo0Formula = repEvo0.getFormula();
        this.repEvo1Formula = repEvo1.getFormula();
    }

    public static EvolutionSet2 createWithSample(ModelRepresentation repEvo0, ModelRepresentation repEvo1, int t){
        return new EvolutionSet2(repEvo0, repEvo1, EntityPrinter.generateValidTWiseConfigurations(t, repEvo0));
    }

    public static EvolutionSet2 createWithoutSample(ModelRepresentation repEvo0, ModelRepresentation repEvo1, SolutionList oldSample) {
        return new EvolutionSet2(repEvo0, repEvo1, oldSample);
    }
}
