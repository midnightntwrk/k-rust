package org.kframework.kink.precfhook;

import static org.kframework.Collections.immutable;
import static org.kframework.Collections.stream;
import static org.kframework.definition.Constructors.Definition;
import static org.kframework.definition.Constructors.Module;
import static org.kframework.kore.KORE.KApply;
import static org.kframework.kore.KORE.KList;
import static org.kframework.kore.KORE.KToken;

import com.google.inject.Inject;
import com.google.inject.Injector;
import com.google.inject.Provider;
import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.LinkedHashMap;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;
import java.util.stream.Collectors;
import org.kframework.attributes.Att;
import org.kframework.compile.Backend;
import org.kframework.definition.Bubble;
import org.kframework.definition.Configuration;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.Sentence;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KToken;
import org.kframework.kore.Sort;
import org.kframework.kore.VisitK;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Main;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.inject.JCommanderModule.Usage;
import org.kframework.utils.inject.SimpleScope;
import org.kframework.utils.options.InnerParsingOptions;
import org.kframework.utils.options.OuterParsingOptions;

/** Task-owned executable oracle for OfficialConfigurationTransformHook-v0. */
public final class PreCfHookDriver {
  private static final String MODE_ENV = "R2_G_05_MODE";
  private static final String RECORD_ENV = "R2_G_05_RECORD";
  private static final String TARGET_MODULE = "P3-COUPLED";
  private static final String HOOK_ID = "OfficialConfigurationTransformHook-v0";
  private static final String ADAPTER_ID = "OfficialDefinitionAdapter-v1";
  private static final String BOUNDARY = "post-config-parse-pre-cell-check";

  private PreCfHookDriver() {}

  public static void main(String[] args) {
    Injector injector = Main.getInjector("-kompile");
    Main officialMain = injector.getInstance(Main.class);
    SimpleScope scope = officialMain.getRequestScope();
    int result = 1;
    try {
      scope.enter();
      Main.seedInjector(scope, "-kompile", args, new File("."), System.getenv(), System.nanoTime());
      KExceptionManager kem = injector.getInstance(KExceptionManager.class);
      kem.installForUncaughtExceptions();
      result = injector.getInstance(DriverFrontEnd.class).main();
    } finally {
      scope.exit();
    }
    System.exit(result);
  }

  public static final class DriverFrontEnd extends FrontEnd {
    private final KompileOptions options;
    private final OuterParsingOptions outerOptions;
    private final InnerParsingOptions innerOptions;
    private final Provider<Backend> backendProvider;
    private final Stopwatch stopwatch;
    private final KExceptionManager kem;
    private final BinaryLoader loader;
    private final Provider<FileUtil> files;

    @Inject
    public DriverFrontEnd(
        KompileOptions options,
        OuterParsingOptions outerOptions,
        InnerParsingOptions innerOptions,
        GlobalOptions globalOptions,
        @Usage String usage,
        Provider<Backend> backendProvider,
        Stopwatch stopwatch,
        KExceptionManager kem,
        BinaryLoader loader,
        JarInfo jarInfo,
        Provider<FileUtil> files) {
      super(kem, globalOptions, usage, jarInfo, files);
      this.options = options;
      this.outerOptions = outerOptions;
      this.innerOptions = innerOptions;
      this.backendProvider = backendProvider;
      this.stopwatch = stopwatch;
      this.kem = kem;
      this.loader = loader;
      this.files = files;
    }

    @Override
    protected int run() {
      FileUtil fileUtil = files.get();
      File definitionFile = outerOptions.mainDefinitionFile(fileUtil);
      if (!definitionFile.exists()) {
        throw KEMException.criticalError(
            "Definition file doesn't exist: " + definitionFile.getAbsolutePath());
      }
      String mode = requireEnvironment(MODE_ENV);
      Path recordPath = Path.of(requireEnvironment(RECORD_ENV)).toAbsolutePath().normalize();
      Trace trace = new Trace(mode, recordPath, canonical(definitionFile));
      try {
        Kompile kompile =
            new Kompile(
                options,
                outerOptions,
                innerOptions,
                globalOptions,
                fileUtil,
                kem,
                stopwatch,
                innerOptions.profileRules == null);
        Backend backend = backendProvider.get();
        Hook hook = new Hook(mode, trace);
        PostCfAdapter adapter = new PostCfAdapter(mode, trace);
        Function<Definition, Definition> postCfPipeline = adapter::apply;
        postCfPipeline = postCfPipeline.andThen(backend.steps());

        CompiledDefinition definition;
        if (mode.equals("default-identity")) {
          definition =
              kompile.run(
                  definitionFile,
                  options.mainModule(fileUtil),
                  options.syntaxModule(fileUtil),
                  postCfPipeline,
                  backend.excludedModuleTags());
          require(trace.hookInvocations == 0, "default entry unexpectedly invoked task hook");
        } else {
          definition =
              kompile.run(
                  definitionFile,
                  options.mainModule(fileUtil),
                  options.syntaxModule(fileUtil),
                  hook::apply,
                  postCfPipeline,
                  backend.excludedModuleTags());
          require(trace.hookInvocations == 1, "hook was not invoked exactly once");
        }
        require(trace.postCfAdapterInvocations == 1, "post-CF adapter was not invoked once");

        fileUtil.saveToKompiled("mainModule.txt", definition.executionModule().name());
        fileUtil.saveToKompiled("mainSyntaxModule.txt", definition.mainSyntaxModuleName());
        loader.saveOrDie(fileUtil.resolveKompiled("compiled.bin"), definition);
        fileUtil.saveToKompiled("backend.txt", options.backend);
        Backend.Holder holder = new Backend.Holder(definition);
        backend.accept(holder);
        loader.saveOrDie(fileUtil.resolveKompiled("timestamp"), "");
        trace.backendArtifactsConstructed = true;
        trace.status = "accepted";
        return 0;
      } catch (RuntimeException e) {
        trace.reject(e);
        throw e;
      } finally {
        trace.write();
      }
    }

    private static String requireEnvironment(String name) {
      String value = System.getenv(name);
      if (value == null || value.isBlank()) {
        throw KEMException.criticalError("Missing required environment variable " + name);
      }
      return value;
    }
  }

  private static final class Hook {
    private final String mode;
    private final Trace trace;
    private K expectedTargetBody;

    Hook(String mode, Trace trace) {
      this.mode = mode;
      this.trace = trace;
    }

    Definition apply(Definition input) {
      trace.hookInvocations++;
      trace.callbackBoundary = BOUNDARY;
      Snapshot before = Snapshot.capture(input, trace.primarySource);
      trace.preModuleCount = before.moduleCount;
      trace.preSentenceCount = before.sentenceCount;
      trace.preConfigurationCount = before.configurationCount;
      trace.prePrimarySourceCount = before.primarySourceCount;
      trace.preFingerprint = before.wholeSha;

      if (mode.equals("throw-sentinel")) {
        throw new SentinelException("r2-g-05-sentinel-transformer-exception");
      }
      Definition output =
          switch (mode) {
            case "explicit-identity" -> input;
            case "augment-a", "augment-b" -> augment(input, "observation");
            case "duplicate-k" -> augment(input, "k");
            case "unauthorized-nonconfig" -> mutateNonConfiguration(input);
            case "return-null" -> null;
            default -> throw validationError("unsupported hook mode: " + mode);
          };
      if (output == null) {
        trace.hookSameReference = false;
        return null;
      }

      trace.taskValidationInvoked = true;
      Snapshot after = Snapshot.capture(output, trace.primarySource);
      trace.postModuleCount = after.moduleCount;
      trace.postSentenceCount = after.sentenceCount;
      trace.postConfigurationCount = after.configurationCount;
      trace.postPrimarySourceCount = after.primarySourceCount;
      trace.postFingerprint = after.wholeSha;
      trace.hookSameReference = input == output;

      if (!before.graphSha.equals(after.graphSha)) {
        throw validationError("definition/module identity fields or imports changed");
      }
      if (!before.nonConfigurationSha.equals(after.nonConfigurationSha)) {
        throw validationError("unauthorized non-configuration sentence change");
      }
      if (before.configurationCount != after.configurationCount) {
        throw validationError("configuration cardinality changed");
      }
      if (mode.equals("explicit-identity")) {
        require(input == output, "explicit identity did not return the same Definition reference");
        require(before.wholeSha.equals(after.wholeSha), "explicit identity changed content");
      } else {
        require(!before.configurationSha.equals(after.configurationSha), "configuration body did not change");
        require(trace.targetConfigurations == 1, "expected exactly one target Configuration");
        trace.changedConfigurations = validateConfigurationDelta(input, output);
        require(trace.changedConfigurations == 1, "expected exactly one changed Configuration");
        require(trace.sideConditionsPreserved, "Configuration ensures/attributes were not preserved");
        require(expectedTargetBody != null, "expected target body was not captured");
        require(
            expectedTargetBody.equals(targetConfiguration(output).body()),
            "transformed target body was not the exact one-cell structural delta");
        trace.exactStructuralDelta = true;
      }
      trace.taskValidationAccepted = true;
      return output;
    }

    private Definition augment(Definition input, String addedCellName) {
      AtomicInteger targets = new AtomicInteger();
      AtomicInteger changes = new AtomicInteger();
      boolean[] sideConditions = {true};
      org.kframework.definition.DefinitionTransformer transformer =
          org.kframework.definition.DefinitionTransformer.from(
              module -> {
                if (!module.name().equals(TARGET_MODULE)) return module;
                java.util.Set<Sentence> updated =
                    stream(module.localSentences())
                        .map(
                            sentence -> {
                              if (!(sentence instanceof Configuration configuration)
                                  || !sameSource(configuration, trace.primarySource)) return sentence;
                              targets.incrementAndGet();
                              K newBody = addTypedCell(configuration.body(), addedCellName);
                              expectedTargetBody = newBody;
                              Configuration replacement =
                                  Configuration.apply(
                                      newBody, configuration.ensures(), configuration.att());
                              sideConditions[0] &=
                                  replacement.ensures() == configuration.ensures()
                                      && replacement.att().equals(configuration.att());
                              changes.incrementAndGet();
                              return replacement;
                            })
                        .collect(Collectors.toSet());
                return Module(module.name(), module.imports(), immutable(updated), module.att());
              },
              "R2-G-05 fixture-specific typed cell augmentation");
      Definition output = transformer.apply(input);
      trace.targetConfigurations = targets.get();
      trace.changedConfigurations = changes.get();
      trace.sideConditionsPreserved = sideConditions[0];
      return output;
    }

    private int validateConfigurationDelta(Definition before, Definition after) {
      Map<String, Configuration> beforeConfigurations = configurationMap(before);
      Map<String, Configuration> afterConfigurations = configurationMap(after);
      require(
          beforeConfigurations.keySet().equals(afterConfigurations.keySet()),
          "configuration identities changed");
      int changed = 0;
      for (String key : beforeConfigurations.keySet()) {
        Configuration left = beforeConfigurations.get(key);
        Configuration right = afterConfigurations.get(key);
        require(left.att().equals(right.att()), "configuration attributes changed at " + key);
        require(left.ensures().equals(right.ensures()), "configuration ensures changed at " + key);
        if (!left.body().equals(right.body())) changed++;
      }
      return changed;
    }

    private Map<String, Configuration> configurationMap(Definition definition) {
      Map<String, Configuration> result = new LinkedHashMap<>();
      stream(definition.modules())
          .sorted(Comparator.comparing(Module::name))
          .forEach(
              module ->
                  stream(module.localSentences())
                      .filter(Configuration.class::isInstance)
                      .map(Configuration.class::cast)
                      .sorted(Comparator.comparing(value -> value.location().map(Object::toString).orElse("")))
                      .forEach(
                          configuration -> {
                            String key =
                                module.name()
                                    + "|"
                                    + configuration.source().map(value -> value.source()).orElse("")
                                    + "|"
                                    + configuration.location().map(Object::toString).orElse("");
                            require(result.put(key, configuration) == null, "duplicate configuration identity " + key);
                          }));
      return result;
    }

    private Configuration targetConfiguration(Definition definition) {
      List<Configuration> targets =
          stream(definition.getModule(TARGET_MODULE).get().localSentences())
              .filter(Configuration.class::isInstance)
              .map(Configuration.class::cast)
              .filter(configuration -> sameSource(configuration, trace.primarySource))
              .toList();
      require(targets.size() == 1, "expected one target Configuration after transformation");
      return targets.get(0);
    }

    private K addTypedCell(K body, String addedCellName) {
      if (!(body instanceof KApply top) || !cellName(top).equals("T")) {
        throw validationError("P3 configuration did not have the expected typed <T> root");
      }
      KApply template = findCell(top, addedCellName.equals("k") ? "k" : "state");
      if (template == null) {
        throw validationError("could not find typed template cell");
      }
      K added = addedCellName.equals("k") ? template : cloneObservationCell(template);
      List<K> topItems = new ArrayList<>(top.klist().items());
      K originalChildren = topItems.get(2);
      topItems.set(2, KApply(org.kframework.builtin.KLabels.CELLS, originalChildren, added));
      return KApply(top.klabel(), KList(topItems), top.att());
    }

    private static KApply cloneObservationCell(KApply stateCell) {
      List<K> items = new ArrayList<>(stateCell.klist().items());
      KToken start = requireToken(items.get(0), "state start label");
      KToken end = requireToken(items.get(3), "state end label");
      KToken value = requireToken(items.get(2), "state body");
      items.set(0, KToken("observation", start.sort(), start.att()));
      items.set(2, KToken("0", value.sort(), value.att()));
      items.set(3, KToken("observation", end.sort(), end.att()));
      return KApply(stateCell.klabel(), KList(items), stateCell.att());
    }

    private static Definition mutateNonConfiguration(Definition input) {
      AtomicInteger changes = new AtomicInteger();
      org.kframework.definition.DefinitionTransformer transformer =
          org.kframework.definition.DefinitionTransformer.from(
              module -> {
                if (!module.name().equals(TARGET_MODULE)) return module;
                java.util.Set<Sentence> updated =
                    stream(module.localSentences())
                        .map(
                            sentence -> {
                              if (changes.get() == 0
                                  && sentence instanceof Bubble bubble
                                  && !bubble.sentenceType().equals("config")) {
                                changes.incrementAndGet();
                                return Bubble.apply(
                                    bubble.sentenceType(), bubble.contents() + " ", bubble.att());
                              }
                              return sentence;
                            })
                        .collect(Collectors.toSet());
                return Module(module.name(), module.imports(), immutable(updated), module.att());
              },
              "R2-G-05 unauthorized negative");
      Definition output = transformer.apply(input);
      require(changes.get() == 1, "unauthorized negative did not change exactly one Bubble");
      return output;
    }
  }

  private static final class PostCfAdapter {
    private final String mode;
    private final Trace trace;

    PostCfAdapter(String mode, Trace trace) {
      this.mode = mode;
      this.trace = trace;
    }

    Definition apply(Definition input) {
      trace.postCfAdapterInvocations++;
      trace.cfOutputConstructed = true;
      Snapshot snapshot = Snapshot.capture(input, trace.primarySource);
      trace.postCfModuleCount = snapshot.moduleCount;
      trace.postCfSentenceCount = snapshot.sentenceCount;
      trace.postCfPrimarySourceCount = snapshot.primarySourceCount;
      trace.postCfContainsConfiguration = snapshot.configurationCount > 0;
      require(!trace.postCfContainsConfiguration, "Configuration survived official CF generation");
      if (mode.startsWith("augment-")) {
        String official = input.toString();
        trace.officialObservationSentences =
            official.contains("ObservationCell")
                && official.contains("initObservationCell")
                && official.contains("observation");
        require(trace.officialObservationSentences, "official observation sentences missing post-CF");
        require(snapshot.primarySourceCount > 0, "existing sentence provenance disappeared post-CF");
      }
      trace.postCfSameReference = true;
      return input;
    }
  }

  private static final class Snapshot {
    final String wholeSha;
    final String graphSha;
    final String nonConfigurationSha;
    final String configurationSha;
    final int moduleCount;
    final int sentenceCount;
    final int configurationCount;
    final int primarySourceCount;

    private Snapshot(
        String wholeSha,
        String graphSha,
        String nonConfigurationSha,
        String configurationSha,
        int moduleCount,
        int sentenceCount,
        int configurationCount,
        int primarySourceCount) {
      this.wholeSha = wholeSha;
      this.graphSha = graphSha;
      this.nonConfigurationSha = nonConfigurationSha;
      this.configurationSha = configurationSha;
      this.moduleCount = moduleCount;
      this.sentenceCount = sentenceCount;
      this.configurationCount = configurationCount;
      this.primarySourceCount = primarySourceCount;
    }

    static Snapshot capture(Definition definition, String primarySource) {
      List<Module> modules =
          stream(definition.modules()).sorted(Comparator.comparing(Module::name)).toList();
      StringBuilder graph = new StringBuilder();
      StringBuilder nonConfigurations = new StringBuilder();
      StringBuilder configurations = new StringBuilder();
      int sentenceCount = 0;
      int configurationCount = 0;
      int primarySourceCount = 0;
      graph.append("definition|").append(definition.att()).append('|')
          .append(definition.mainModule().name()).append('\n');
      for (Module module : modules) {
        graph.append("module|").append(module.name()).append('|').append(module.att()).append('\n');
        stream(module.imports())
            .map(value -> value.module().name() + "|" + value.isPublic())
            .sorted()
            .forEach(value -> graph.append("import|").append(value).append('\n'));
        List<Sentence> sentences =
            stream(module.localSentences())
                .sorted(Comparator.comparing(value -> value.getClass().getName() + "|" + value))
                .toList();
        sentenceCount += sentences.size();
        for (Sentence sentence : sentences) {
          String value =
              module.name()
                  + "|"
                  + sentence.getClass().getName()
                  + "|"
                  + sentence
                  + "|"
                  + sentence.att()
                  + "\n";
          if (sentence instanceof Configuration) {
            configurationCount++;
            configurations.append(value);
          } else {
            nonConfigurations.append(value);
          }
          if (sameSource(sentence, primarySource)) primarySourceCount++;
        }
      }
      String graphSha = sha256(graph.toString());
      String nonConfigSha = sha256(nonConfigurations.toString());
      String configSha = sha256(configurations.toString());
      return new Snapshot(
          sha256(graphSha + nonConfigSha + configSha),
          graphSha,
          nonConfigSha,
          configSha,
          modules.size(),
          sentenceCount,
          configurationCount,
          primarySourceCount);
    }
  }

  private static final class Trace {
    final String mode;
    final Path recordPath;
    final String primarySource;
    final String kompileCodeSource;
    String status = "running";
    String rejectionBoundary = "";
    String error = "";
    String callbackBoundary = "";
    int hookInvocations;
    int postCfAdapterInvocations;
    boolean hookSameReference;
    boolean taskValidationInvoked;
    boolean taskValidationAccepted;
    boolean sideConditionsPreserved;
    boolean exactStructuralDelta;
    boolean postCfSameReference;
    boolean cfOutputConstructed;
    boolean backendArtifactsConstructed;
    boolean postCfContainsConfiguration;
    boolean officialObservationSentences;
    int targetConfigurations;
    int changedConfigurations;
    int preModuleCount;
    int preSentenceCount;
    int preConfigurationCount;
    int prePrimarySourceCount;
    int postModuleCount;
    int postSentenceCount;
    int postConfigurationCount;
    int postPrimarySourceCount;
    int postCfModuleCount;
    int postCfSentenceCount;
    int postCfPrimarySourceCount;
    String preFingerprint = "";
    String postFingerprint = "";

    Trace(String mode, Path recordPath, String primarySource) {
      this.mode = mode;
      this.recordPath = recordPath;
      this.primarySource = primarySource;
      this.kompileCodeSource =
          String.valueOf(Kompile.class.getProtectionDomain().getCodeSource().getLocation());
    }

    void reject(RuntimeException exception) {
      status = "rejected";
      error = exception.toString();
      if (mode.equals("unauthorized-nonconfig")) rejectionBoundary = "task-validation-pre-cell-check";
      else if (mode.equals("duplicate-k")) rejectionBoundary = "official-transformed-input-cell-check";
      else rejectionBoundary = BOUNDARY;
    }

    void write() {
      try {
        Files.createDirectories(recordPath.getParent());
        Files.writeString(recordPath, toJson(), StandardCharsets.UTF_8);
      } catch (IOException e) {
        throw KEMException.criticalError("Cannot write R2-G-05 trace " + recordPath, e);
      }
    }

    String toJson() {
      return "{\n"
          + field("schemaVersion", 1, true)
          + field("contract", HOOK_ID, true)
          + field("postCfAdapter", ADAPTER_ID, true)
          + field("mode", mode, true)
          + field("status", status, true)
          + field("callbackBoundary", callbackBoundary, true)
          + field("rejectionBoundary", rejectionBoundary, true)
          + field("error", error, true)
          + field("primarySource", primarySource, true)
          + field("kompileCodeSource", kompileCodeSource, true)
          + field("hookInvocations", hookInvocations, true)
          + field("hookSameReference", hookSameReference, true)
          + field("taskValidationInvoked", taskValidationInvoked, true)
          + field("taskValidationAccepted", taskValidationAccepted, true)
          + field("targetConfigurations", targetConfigurations, true)
          + field("changedConfigurations", changedConfigurations, true)
          + field("sideConditionsPreserved", sideConditionsPreserved, true)
          + field("exactStructuralDelta", exactStructuralDelta, true)
          + field("postCfAdapterInvocations", postCfAdapterInvocations, true)
          + field("postCfSameReference", postCfSameReference, true)
          + field("cfOutputConstructed", cfOutputConstructed, true)
          + field("backendArtifactsConstructed", backendArtifactsConstructed, true)
          + field("postCfContainsConfiguration", postCfContainsConfiguration, true)
          + field("officialObservationSentences", officialObservationSentences, true)
          + field("preModuleCount", preModuleCount, true)
          + field("preSentenceCount", preSentenceCount, true)
          + field("preConfigurationCount", preConfigurationCount, true)
          + field("prePrimarySourceCount", prePrimarySourceCount, true)
          + field("postModuleCount", postModuleCount, true)
          + field("postSentenceCount", postSentenceCount, true)
          + field("postConfigurationCount", postConfigurationCount, true)
          + field("postPrimarySourceCount", postPrimarySourceCount, true)
          + field("postCfModuleCount", postCfModuleCount, true)
          + field("postCfSentenceCount", postCfSentenceCount, true)
          + field("postCfPrimarySourceCount", postCfPrimarySourceCount, true)
          + field("preFingerprint", preFingerprint, true)
          + field("postFingerprint", postFingerprint, false)
          + "}\n";
    }
  }

  private static KApply findCell(K root, String name) {
    KApply[] found = {null};
    new VisitK() {
      @Override
      public void apply(KApply value) {
        if (found[0] == null && cellName(value).equals(name)) found[0] = value;
        super.apply(value);
      }
    }.apply(root);
    return found[0];
  }

  private static String cellName(KApply value) {
    if (!value.klabel().name().equals("#configCell") || value.klist().size() != 4) return "";
    K first = value.klist().items().get(0);
    return first instanceof KToken token ? token.s() : "";
  }

  private static KToken requireToken(K value, String description) {
    if (value instanceof KToken token) return token;
    throw validationError("expected typed KToken for " + description);
  }

  private static boolean sameSource(Sentence sentence, String expected) {
    if (sentence.source().isEmpty()) return false;
    String actual = sentence.source().get().source();
    if (actual.equals(expected)) return true;
    try {
      return Path.of(actual).toAbsolutePath().normalize().equals(Path.of(expected));
    } catch (RuntimeException ignored) {
      return false;
    }
  }

  private static String canonical(File file) {
    try {
      return file.getCanonicalPath();
    } catch (IOException e) {
      throw KEMException.criticalError("Cannot canonicalize definition path", e);
    }
  }

  private static void require(boolean condition, String message) {
    if (!condition) throw validationError(message);
  }

  private static ValidationException validationError(String message) {
    return new ValidationException(message);
  }

  private static String sha256(String value) {
    try {
      byte[] digest = MessageDigest.getInstance("SHA-256").digest(value.getBytes(StandardCharsets.UTF_8));
      StringBuilder result = new StringBuilder();
      for (byte item : digest) result.append(String.format(Locale.ROOT, "%02x", item));
      return result.toString();
    } catch (NoSuchAlgorithmException e) {
      throw new AssertionError(e);
    }
  }

  private static String field(String name, String value, boolean comma) {
    return "  \"" + name + "\": \"" + escape(value) + "\"" + (comma ? "," : "") + "\n";
  }

  private static String field(String name, int value, boolean comma) {
    return "  \"" + name + "\": " + value + (comma ? "," : "") + "\n";
  }

  private static String field(String name, boolean value, boolean comma) {
    return "  \"" + name + "\": " + value + (comma ? "," : "") + "\n";
  }

  private static String escape(String value) {
    return value.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n").replace("\r", "\\r");
  }

  private static final class ValidationException extends RuntimeException {
    ValidationException(String message) {
      super(message);
    }
  }

  private static final class SentinelException extends RuntimeException {
    SentinelException(String message) {
      super(message);
    }
  }
}
