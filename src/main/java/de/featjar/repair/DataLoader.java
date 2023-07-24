package de.featjar.repair;

import de.featjar.formula.ModelRepresentation;
import de.featjar.util.logging.Logger;
import java.nio.file.Paths;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;

public class DataLoader {

  public enum Dataset2 {
    BERKELEY("MA_PS/berkeley_db_model_evo0.xml", "/MA_PS/berkeley_db_model_evo1.xml"),
    MODEL_MA("MA_PS/model_ma_evo0.xml", "/MA_PS/model_ma_evo1.xml"),

    BUSYBOX("MA_PS/busybox/busyboxEvo0.dimacs", "/MA_PS/busybox/busyboxEvo1.dimacs");
    public final String pathEvo0;
    public final String pathEvo1;

    private Dataset2(String pathEvo0, String pathEvo1) {
      this.pathEvo0 = pathEvo0;
      this.pathEvo1 = pathEvo1;
    }
  }
  public enum DatasetN {
    BERKELEY(List.of("MA_PS/berkeley_db_model_evo0.xml", "/MA_PS/berkeley_db_model_evo1.xml")),
    MODEL_MA(List.of("MA_PS/model_ma_evo0.xml", "/MA_PS/model_ma_evo1.xml")),

    BUSYBOX(List.of("MA_PS/busybox/busyboxEvo0.dimacs", "/MA_PS/busybox/busyboxEvo1.dimacs"));
    public final List<String> paths;

    private DatasetN(List<String> paths) {
      this.paths = paths;
    }
  }

  public static EvolutionSet getEvolutionSet(Dataset2 dataset2, String absolutePrefix) {
    var pathEvo0 = absolutePrefix + dataset2.pathEvo0;
    var pathEvo1 = absolutePrefix + dataset2.pathEvo1;
    System.out.println("Loading Dataset Evolution Step 0 (path={" + pathEvo0 + "}...");
    var repEvo0 = ModelRepresentation
        .load(Paths.get(pathEvo0))
        .orElse(Logger::logProblems);
    System.out.println("Loading Dataset Evolution Step 1 (path={" + pathEvo1 + "}...");
    var repEvo1 = ModelRepresentation
        .load(Paths.get(pathEvo1))
        .orElse(Logger::logProblems);
    System.out.println("Generating valid sample for evo 0...");
    var solutionList = EntityPrinter.generateValidTWiseConfigurations(repEvo0);
    return new EvolutionSet(repEvo0, repEvo1, solutionList);
  }

  public static NEvolutionSet getEvolutionSet(DatasetN datasetN, String absolutePrefix) {
    AtomicInteger i = new AtomicInteger();
    var models = datasetN.paths.stream().map(path -> {
      var fullPath = absolutePrefix + path;
      System.out.println("Loading Dataset Evolution Step "+i.getAndIncrement()+" (path={" + fullPath + "}...");
      return ModelRepresentation
              .load(Paths.get(fullPath))
              .orElse(Logger::logProblems);
    }).collect(Collectors.toList());

    System.out.println("Generating valid sample for evo 0...");
    var solutionList = EntityPrinter.generateValidTWiseConfigurations(models.get(0));
    return new NEvolutionSet(models.toArray(new ModelRepresentation[0]), solutionList);
  }



}
