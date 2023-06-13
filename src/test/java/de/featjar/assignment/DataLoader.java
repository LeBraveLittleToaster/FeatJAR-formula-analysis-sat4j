package de.featjar.assignment;

import de.featjar.formula.ModelRepresentation;
import de.featjar.util.logging.Logger;
import java.nio.file.Paths;

public class DataLoader {

  public enum Dataset {
    BERKELEY("MA_PS\\berkeley_db_model_evo0.xml", "\\MA_PS\\berkeley_db_model_evo1.xml"),
    MODEL_MA("MA_PS\\model_ma_evo0.xml", "\\MA_PS\\model_ma_evo1.xml");
    public final String pathEvo0;
    public final String pathEvo1;

    private Dataset(String pathEvo0, String pathEvo1) {
      this.pathEvo0 = pathEvo0;
      this.pathEvo1 = pathEvo1;
    }
  }

  public static EvolutionSet getEvolutionSet(Dataset dataset, String absolutePrefix) {
    var pathEvo0 = absolutePrefix + dataset.pathEvo0;
    var pathEvo1 = absolutePrefix + dataset.pathEvo1;
    System.out.println("Loading Dataset Evolution Step 0 (path={" + pathEvo0 + "}...");
    var repEvo0 = ModelRepresentation
        .load(Paths.get(pathEvo0))
        .orElse(Logger::logProblems);
    System.out.println("Loading Dataset Evolution Step 1 (path={" + pathEvo1 + "}...");
    var repEvo1 = ModelRepresentation
        .load(Paths.get(pathEvo1))
        .orElse(Logger::logProblems);
    return new EvolutionSet(repEvo0, repEvo1);
  }

  public static class EvolutionSet {

    public final ModelRepresentation repEvo0;
    public final ModelRepresentation repEvo1;

    public EvolutionSet(ModelRepresentation repEvo0, ModelRepresentation repEvo1) {
      this.repEvo0 = repEvo0;
      this.repEvo1 = repEvo1;
    }
  }

}
