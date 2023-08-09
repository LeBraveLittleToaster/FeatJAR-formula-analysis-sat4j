package de.featjar.repair;

import de.featjar.formula.ModelRepresentation;
import de.featjar.util.logging.Logger;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class DataLoader {

    public enum Dataset2 {
        BERKELEY("MA_PS/berkeley_db_model_evo0.xml", "/MA_PS/berkeley_db_model_evo1.xml"),
        MODEL_MA("MA_PS/model_ma_evo0.xml", "/MA_PS/model_ma_evo1.xml"),

        BUSYBOX("MA_PS/busybox/busyboxEvo0.dimacs", "/MA_PS/busybox/busyboxEvo1.dimacs"),
        BUSYBOX_BEGIN("MA_PS/busybox/2020/2020-08-13-clean.dimacs", "MA_PS/busybox/2020/2020-12-16-clean.dimacs");
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

        BUSYBOX_DEV(List.of("MA_PS/busybox/busyboxEvo0.dimacs", "/MA_PS/busybox/busyboxEvo1.dimacs")),

        BUSYBOX_2019(List.of("MA_PS/busybox/2019/2019-01-06-clean.dimacs", "MA_PS/busybox/2019/2019-04-30-clean.dimacs", "MA_PS/busybox/2019/2019-07-02-clean.dimacs", "MA_PS/busybox/2019/2019-10-14-clean.dimacs")),
        BUSYBOX_2018(List.of("MA_PS/busybox/2018/2018-04-06-clean.dimacs", "MA_PS/busybox/2018/2018-06-06-clean.dimacs", "MA_PS/busybox/2018/2018-11-18-clean.dimacs"));
        public final List<String> paths;

        private DatasetN(List<String> paths) {
            this.paths = paths;
        }
    }

    public static EvolutionSet2 getEvolutionSetN(Dataset2 dataset2, int t, String absolutePrefix) {
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
        var solutionList = EntityPrinter.generateValidTWiseConfigurations(t, repEvo0);
        return new EvolutionSet2(repEvo0, repEvo1, solutionList);
    }

    public static Optional<EvolutionSetN> getEvolutionSetN(List<DatasetN> datasetN, int t, String absolutePrefix) {
        return getEvolutionSetNFromPaths(
                datasetN.stream().map(dataN -> dataN.paths).flatMap(List::stream).map(path -> absolutePrefix + path), t);
    }

    public static Optional<EvolutionSetN> getEvolutionSetNInFolderWithSameName(String filename, int t, String pathToRootFolder) throws IOException {
        try (Stream<Path> walkStream = Files.walk(Paths.get(pathToRootFolder))) {
            var paths = walkStream.filter(p -> p.toFile().isFile())
                    .filter(p -> p.toFile().length() > 0)
                    .map(Path::toString)
                    .filter(string -> string.endsWith(filename));
            return getEvolutionSetNFromPaths(paths, t);
        }
    }

    private static Optional<EvolutionSetN> getEvolutionSetNFromPaths(Stream<String> paths, int t) {
        try {
            AtomicInteger i = new AtomicInteger();
            var models = paths.map(path -> {
                System.out.println("Loading Dataset Evolution Step " + i.getAndIncrement() + " (path={" + path + "}...");
                return ModelRepresentation
                        .load(Paths.get(path))
                        .orElse(problem -> System.out.println(problem));
            }).collect(Collectors.toList());

            if (models.stream().anyMatch(Objects::isNull)) {
                System.err.println("Not all models loaded!");
                return Optional.empty();
            }
            System.out.println("Generating valid sample for evo 0...");
            var solutionList = EntityPrinter.generateValidTWiseConfigurations(t, models.get(0));
            return Optional.of(new EvolutionSetN(models.toArray(new ModelRepresentation[0]), solutionList));
        } catch (Exception e) {
            e.printStackTrace();
            return Optional.empty();
        }
    }
}
