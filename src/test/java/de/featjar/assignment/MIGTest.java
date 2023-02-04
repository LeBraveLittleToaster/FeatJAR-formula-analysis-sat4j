package de.featjar.assignment;

import de.featjar.analysis.mig.solver.MIGProvider;
import de.featjar.analysis.mig.solver.MIGVisitorProvider;
import de.featjar.analysis.mig.solver.MIGVisitorProvider.Visitor;
import de.featjar.formula.ModelRepresentation;
import de.featjar.util.extension.ExtensionLoader;
import de.featjar.util.logging.Logger;
import java.nio.file.Paths;
import java.util.Arrays;

public class MIGTest {

    public static void main(String[] args) {
        ExtensionLoader.load();

        String file = "src/test/resources/GPL/model.xml";
        MIGVisitorProvider mig = ModelRepresentation //
                .load(Paths.get(file)) //
                .map(m -> m.get(MIGProvider.fromFormula(false, false))) //
                .map(MIGVisitorProvider::new) //
                .orElse(Logger::logProblems);
        Visitor visitor = mig.getVisitor();

        int[] candidate, newCandidate;

        candidate = new int[] {5};
        newCandidate = visitor.extend(candidate);
        visitor.reset();
        System.out.println(Arrays.toString(candidate) + " -> " + Arrays.toString(newCandidate));

        candidate = new int[] {17, 33};
        newCandidate = visitor.extend(candidate);
        visitor.reset();
        System.out.println(Arrays.toString(candidate) + " -> " + Arrays.toString(newCandidate));

        candidate = new int[] {-5, -6, -16};
        newCandidate = visitor.extend(candidate);
        visitor.reset();
        System.out.println(Arrays.toString(candidate) + " -> " + Arrays.toString(newCandidate));
    }
}
