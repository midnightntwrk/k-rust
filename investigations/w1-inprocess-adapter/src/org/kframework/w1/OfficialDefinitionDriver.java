package org.kframework.w1;

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
import java.util.Locale;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;
import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.compile.Backend;
import org.kframework.definition.Claim;
import org.kframework.definition.Context;
import org.kframework.definition.ContextAlias;
import org.kframework.definition.Definition;
import org.kframework.definition.DefinitionTransformer;
import org.kframework.definition.Import;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.TransformK;
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

import static org.kframework.Collections.stream;

/**
 * W1-D standalone driver over the pinned official K object graph.
 *
 * <p>The only pipeline difference from KompileFrontEnd is the adapter function composed before
 * Backend.steps(). The driver intentionally uses environment variables for its private controls so
 * the official JCommander option surface remains unchanged.
 */
public final class OfficialDefinitionDriver {
  private static final String MODE_ENV = "W1_ADAPTER_MODE";
  private static final String RECORD_ENV = "W1_ADAPTER_RECORD";

  private OfficialDefinitionDriver() {}

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
      Adapter adapter = new Adapter(mode, recordPath, definitionFile);
      Function<Definition, Definition> pipeline = adapter::apply;
      pipeline = pipeline.andThen(backend.steps());

      CompiledDefinition definition =
          kompile.run(
              definitionFile,
              options.mainModule(fileUtil),
              options.syntaxModule(fileUtil),
              pipeline,
              backend.excludedModuleTags());

      fileUtil.saveToKompiled("mainModule.txt", definition.executionModule().name());
      fileUtil.saveToKompiled("mainSyntaxModule.txt", definition.mainSyntaxModuleName());
      stopwatch.printIntermediate("Kompile to kore");
      loader.saveOrDie(fileUtil.resolveKompiled("compiled.bin"), definition);
      fileUtil.saveToKompiled("backend.txt", options.backend);
      stopwatch.printIntermediate("Save to disk");
      Backend.Holder holder = new Backend.Holder(definition);
      backend.accept(holder);
      stopwatch.printIntermediate("Backend");
      loader.saveOrDie(fileUtil.resolveKompiled("timestamp"), "");
      stopwatch.printTotal("Total");
      return 0;
    }

    private static String requireEnvironment(String name) {
      String value = System.getenv(name);
      if (value == null || value.isBlank()) {
        throw KEMException.criticalError("Missing required environment variable " + name);
      }
      return value;
    }
  }

  private static final class Adapter {
    private static final String ID = "OfficialDefinitionAdapter-v1-candidate";
    private static final String SEAM =
        "parseDefinitionAndResolveBubbles -> adapter -> KoreBackend.steps";

    private final String mode;
    private final Path recordPath;
    private final String primarySource;

    Adapter(String mode, Path recordPath, File definitionFile) {
      this.mode = mode;
      this.recordPath = recordPath;
      try {
        this.primarySource = definitionFile.getCanonicalPath();
      } catch (IOException e) {
        throw KEMException.criticalError("Cannot canonicalize definition path", e);
      }
    }

    Definition apply(Definition input) {
      Snapshot before = Snapshot.capture(input, primarySource);
      Definition output;
      int matchedTargets = 0;
      int replacements = 0;
      try {
        switch (mode) {
          case "identity" -> output = input;
          case "p3-start-to-bump" -> {
            Mutation mutation = mutateP3Start(input);
            output = mutation.definition;
            matchedTargets = mutation.matchedTargets;
            replacements = mutation.replacements;
          }
          case "malformed-null" -> output = null;
          default -> throw validationError("unsupported adapter mode: " + mode);
        }

        if (output == null) {
          throw validationError("transformation returned null Definition");
        }
        if (output.mainModule() == null || output.entryModules() == null) {
          throw validationError("transformation returned an incomplete Definition");
        }
        if (mode.equals("p3-start-to-bump") && (matchedTargets != 1 || replacements != 1)) {
          throw validationError(
              "expected one start-program rule and one RHS replacement, found "
                  + matchedTargets
                  + " and "
                  + replacements);
        }

        Snapshot after = Snapshot.capture(output, primarySource);
        if (mode.equals("identity") && !before.contentSha256.equals(after.contentSha256)) {
          throw validationError("identity transformation changed the content fingerprint");
        }
        if (mode.equals("p3-start-to-bump")) {
          validateMutation(before, after);
        }

        writeRecord(
            Record.accepted(
                mode,
                before,
                after,
                input == output,
                matchedTargets,
                replacements));
        return output;
      } catch (AdapterValidationException e) {
        writeRecord(Record.rejected(mode, before, e.getMessage()));
        throw KEMException.compilerError("W1 adapter validation failed: " + e.getMessage());
      } catch (RuntimeException e) {
        writeRecord(Record.rejected(mode, before, e.toString()));
        throw e;
      }
    }

    private static AdapterValidationException validationError(String message) {
      return new AdapterValidationException(message);
    }

    private static void validateMutation(Snapshot before, Snapshot after) {
      if (before.target == null || after.target == null) {
        throw validationError("start-program provenance missing before or after transformation");
      }
      if (!before.target.lineageSha256.equals(after.target.lineageSha256)) {
        throw validationError("start-program lineage changed");
      }
      if (!before.target.sentenceAttSha256.equals(after.target.sentenceAttSha256)) {
        throw validationError("start-program sentence attributes changed");
      }
      if (before.target.bodySha256.equals(after.target.bodySha256)) {
        throw validationError("start-program body fingerprint did not change");
      }
      if (!before.target.requiresSha256.equals(after.target.requiresSha256)
          || !before.target.ensuresSha256.equals(after.target.ensuresSha256)) {
        throw validationError("start-program side conditions changed");
      }
    }

    private Mutation mutateP3Start(Definition input) {
      AtomicInteger matchedTargets = new AtomicInteger();
      AtomicInteger replacements = new AtomicInteger();
      DefinitionTransformer transformer =
          DefinitionTransformer.fromSentenceTransformer(
              sentence -> {
                if (!(sentence instanceof Rule rule)
                    || !rule.label().orElse("").equals("start-program")) {
                  return sentence;
                }
                matchedTargets.incrementAndGet();
                K newBody =
                    new TransformK() {
                      @Override
                      public K apply(KApply original) {
                        K recursivelyTransformed = super.apply(original);
                        if (!(recursivelyTransformed instanceof KApply application)) {
                          return recursivelyTransformed;
                        }
                        List<K> items = application.klist().items();
                        if (application.klabel().name().equals("add")
                            && items.size() == 2
                            && isNullary(items.get(0), "read")
                            && isNullary(items.get(1), "bump")) {
                          replacements.incrementAndGet();
                          return items.get(1);
                        }
                        return application;
                      }
                    }.apply(rule.body());
                return Rule.apply(newBody, rule.requires(), rule.ensures(), rule.att());
              },
              "W1-D p3 start-program edit");
      Definition output = transformer.apply(input);
      return new Mutation(output, matchedTargets.get(), replacements.get());
    }

    private static boolean isNullary(K value, String label) {
      return value instanceof KApply application
          && application.klabel().name().equals(label)
          && application.klist().size() == 0;
    }

    private void writeRecord(Record record) {
      try {
        Path parent = recordPath.getParent();
        if (parent != null) {
          Files.createDirectories(parent);
        }
        Files.writeString(
            recordPath,
            record.toJson(ID, SEAM, primarySource),
            StandardCharsets.UTF_8);
      } catch (IOException e) {
        throw KEMException.criticalError("Cannot write W1 adapter record " + recordPath, e);
      }
    }
  }

  private static final class AdapterValidationException extends RuntimeException {
    AdapterValidationException(String message) {
      super(message);
    }
  }

  private record Mutation(Definition definition, int matchedTargets, int replacements) {}

  private static final class Snapshot {
    final String contentSha256;
    final String officialTextSha256;
    final String innerAttributesSha256;
    final String primarySourceProjectionSha256;
    final int moduleCount;
    final int localSentenceCount;
    final int kNodeCount;
    final int kNodesWithAttributes;
    final int innerProductionAttributeCount;
    final int primarySourceSentenceCount;
    final Target target;

    private Snapshot(
        String contentSha256,
        String officialTextSha256,
        String innerAttributesSha256,
        String primarySourceProjectionSha256,
        int moduleCount,
        int localSentenceCount,
        int kNodeCount,
        int kNodesWithAttributes,
        int innerProductionAttributeCount,
        int primarySourceSentenceCount,
        Target target) {
      this.contentSha256 = contentSha256;
      this.officialTextSha256 = officialTextSha256;
      this.innerAttributesSha256 = innerAttributesSha256;
      this.primarySourceProjectionSha256 = primarySourceProjectionSha256;
      this.moduleCount = moduleCount;
      this.localSentenceCount = localSentenceCount;
      this.kNodeCount = kNodeCount;
      this.kNodesWithAttributes = kNodesWithAttributes;
      this.innerProductionAttributeCount = innerProductionAttributeCount;
      this.primarySourceSentenceCount = primarySourceSentenceCount;
      this.target = target;
    }

    static Snapshot capture(Definition definition, String primarySource) {
      List<Module> modules = stream(definition.modules()).sorted(Comparator.comparing(Module::name)).toList();
      String officialText = definition.toString();
      StringBuilder attributes = new StringBuilder();
      attributes.append("definition-att|").append(definition.att()).append('\n');
      List<String> sourceProjection = new ArrayList<>();
      Counters counters = new Counters();
      Target target = null;

      for (Module module : modules) {
        attributes.append("module|").append(module.name()).append('|').append(module.att()).append('\n');
        stream(module.imports())
            .map(imp -> imp.module().name() + "|" + imp.isPublic())
            .sorted()
            .forEach(value -> attributes.append("import|").append(module.name()).append('|').append(value).append('\n'));

        List<Sentence> sentences =
            stream(module.localSentences())
                .sorted(
                    Comparator.comparing(
                        sentence ->
                            sentence.getClass().getName()
                                + "|"
                                + sentence
                                + "|"
                                + sentence.att()))
                .toList();
        counters.localSentences += sentences.size();
        for (int sentenceIndex = 0; sentenceIndex < sentences.size(); sentenceIndex++) {
          Sentence sentence = sentences.get(sentenceIndex);
          String prefix = module.name() + "/" + sentenceIndex + "/" + sentence.getClass().getSimpleName();
          attributes
              .append("sentence|")
              .append(prefix)
              .append('|')
              .append(sentence.att())
              .append('\n');
          appendSentenceTerms(sentence, prefix, attributes, counters);

          String source = sentence.source().map(Source::source).orElse(null);
          if (source != null && sameSource(source, primarySource)) {
            String projection =
                module.name()
                    + "|"
                    + sentence.getClass().getName()
                    + "|"
                    + sentence.label().orElse("")
                    + "|"
                    + source
                    + "|"
                    + sentence.location().map(Object::toString).orElse("")
                    + "|"
                    + sentenceDigest(sentence);
            sourceProjection.add(projection);
          }

          if (sentence instanceof Rule rule
              && rule.label().orElse("").equals("start-program")) {
            if (target != null) {
              throw Adapter.validationError("multiple start-program rules at the adapter seam");
            }
            target = Target.capture(module.name(), rule);
          }
        }
      }
      sourceProjection.sort(String::compareTo);
      String sourceProjectionText = String.join("\n", sourceProjection);
      String attributesText = attributes.toString();
      String contentProjection =
          "official-text\n"
              + officialText
              + "\ndefinition-and-inner-attributes\n"
              + attributesText;
      return new Snapshot(
          sha256(contentProjection),
          sha256(officialText),
          sha256(attributesText),
          sha256(sourceProjectionText),
          modules.size(),
          counters.localSentences,
          counters.kNodes,
          counters.kNodesWithAttributes,
          counters.productionAttributes,
          sourceProjection.size(),
          target);
    }

    private static boolean sameSource(String actual, String expected) {
      if (actual.equals(expected)) {
        return true;
      }
      try {
        return Path.of(actual).toAbsolutePath().normalize().equals(Path.of(expected));
      } catch (RuntimeException ignored) {
        return false;
      }
    }

    private static String sentenceDigest(Sentence sentence) {
      StringBuilder value = new StringBuilder();
      value.append(sentence.getClass().getName()).append('|').append(sentence).append('|').append(sentence.att());
      Counters ignored = new Counters();
      appendSentenceTerms(sentence, "source", value, ignored);
      return sha256(value.toString());
    }

    private static void appendSentenceTerms(
        Sentence sentence, String prefix, StringBuilder output, Counters counters) {
      if (sentence instanceof Rule rule) {
        appendK(rule.body(), prefix + "/body", output, counters);
        appendK(rule.requires(), prefix + "/requires", output, counters);
        appendK(rule.ensures(), prefix + "/ensures", output, counters);
      } else if (sentence instanceof Claim claim) {
        appendK(claim.body(), prefix + "/body", output, counters);
        appendK(claim.requires(), prefix + "/requires", output, counters);
        appendK(claim.ensures(), prefix + "/ensures", output, counters);
      } else if (sentence instanceof Context context) {
        appendK(context.body(), prefix + "/body", output, counters);
        appendK(context.requires(), prefix + "/requires", output, counters);
      } else if (sentence instanceof ContextAlias contextAlias) {
        appendK(contextAlias.body(), prefix + "/body", output, counters);
        appendK(contextAlias.requires(), prefix + "/requires", output, counters);
      }
    }

    private static void appendK(K value, String path, StringBuilder output, Counters counters) {
      counters.kNodes++;
      Att att = value.att();
      if (!att.equals(Att.empty())) {
        counters.kNodesWithAttributes++;
      }
      output
          .append("k|")
          .append(path)
          .append('|')
          .append(value.getClass().getName())
          .append('|')
          .append(att)
          .append('\n');
      if (att.contains(Att.PRODUCTION(), Production.class)) {
        Production production = att.get(Att.PRODUCTION(), Production.class);
        counters.productionAttributes++;
        output
            .append("inner-production|")
            .append(path)
            .append('|')
            .append(production)
            .append('|')
            .append(production.att())
            .append('\n');
      }

      if (value instanceof KApply application) {
        List<K> items = application.klist().items();
        for (int index = 0; index < items.size(); index++) {
          appendK(items.get(index), path + "/arg-" + index, output, counters);
        }
      } else if (value instanceof KRewrite rewrite) {
        appendK(rewrite.left(), path + "/left", output, counters);
        appendK(rewrite.right(), path + "/right", output, counters);
      } else if (value instanceof KSequence sequence) {
        List<K> items = sequence.items();
        for (int index = 0; index < items.size(); index++) {
          appendK(items.get(index), path + "/item-" + index, output, counters);
        }
      } else if (value instanceof KAs alias) {
        appendK(alias.pattern(), path + "/pattern", output, counters);
        appendK(alias.alias(), path + "/alias", output, counters);
      } else if (!(value instanceof KToken)
          && !(value instanceof KVariable)
          && !(value instanceof InjectedKLabel)) {
        throw Adapter.validationError("unsupported K node in fingerprint projection: " + value.getClass());
      }
    }
  }

  private static final class Counters {
    int localSentences;
    int kNodes;
    int kNodesWithAttributes;
    int productionAttributes;
  }

  private static final class Target {
    final String module;
    final String label;
    final String source;
    final Location location;
    final String uniqueId;
    final String lineageSha256;
    final String sentenceAttSha256;
    final String bodySha256;
    final String requiresSha256;
    final String ensuresSha256;

    private Target(
        String module,
        String label,
        String source,
        Location location,
        String uniqueId,
        String lineageSha256,
        String sentenceAttSha256,
        String bodySha256,
        String requiresSha256,
        String ensuresSha256) {
      this.module = module;
      this.label = label;
      this.source = source;
      this.location = location;
      this.uniqueId = uniqueId;
      this.lineageSha256 = lineageSha256;
      this.sentenceAttSha256 = sentenceAttSha256;
      this.bodySha256 = bodySha256;
      this.requiresSha256 = requiresSha256;
      this.ensuresSha256 = ensuresSha256;
    }

    static Target capture(String module, Rule rule) {
      String label = rule.label().orElse(null);
      String source = rule.source().map(Source::source).orElse(null);
      Location location = rule.location().orElse(null);
      String uniqueId = rule.att().getOptional(Att.UNIQUE_ID()).orElse(null);
      if (label == null || source == null || location == null) {
        throw Adapter.validationError("start-program lacks label/source/location provenance");
      }
      String lineage =
          module
              + "|"
              + rule.getClass().getName()
              + "|"
              + label
              + "|"
              + source
              + "|"
              + location;
      return new Target(
          module,
          label,
          source,
          location,
          uniqueId,
          sha256(lineage),
          sha256(rule.att().toString()),
          kDigest(rule.body()),
          kDigest(rule.requires()),
          kDigest(rule.ensures()));
    }

    private static String kDigest(K value) {
      StringBuilder projection = new StringBuilder();
      Snapshot.appendK(value, "root", projection, new Counters());
      return sha256(value.toString() + "\n" + projection);
    }
  }

  private static final class Record {
    final String mode;
    final String status;
    final Snapshot before;
    final Snapshot after;
    final Boolean sameDefinitionReference;
    final int matchedTargets;
    final int replacements;
    final String error;

    private Record(
        String mode,
        String status,
        Snapshot before,
        Snapshot after,
        Boolean sameDefinitionReference,
        int matchedTargets,
        int replacements,
        String error) {
      this.mode = mode;
      this.status = status;
      this.before = before;
      this.after = after;
      this.sameDefinitionReference = sameDefinitionReference;
      this.matchedTargets = matchedTargets;
      this.replacements = replacements;
      this.error = error;
    }

    static Record accepted(
        String mode,
        Snapshot before,
        Snapshot after,
        boolean sameDefinitionReference,
        int matchedTargets,
        int replacements) {
      return new Record(
          mode,
          "accepted",
          before,
          after,
          sameDefinitionReference,
          matchedTargets,
          replacements,
          null);
    }

    static Record rejected(String mode, Snapshot before, String error) {
      return new Record(mode, "rejected", before, null, null, 0, 0, error);
    }

    String toJson(String adapterId, String seam, String primarySource) {
      StringBuilder json = new StringBuilder();
      json.append("{\n");
      field(json, 1, "schemaVersion", "1", false);
      field(json, 1, "adapter", quote(adapterId), false);
      field(json, 1, "seam", quote(seam), false);
      field(json, 1, "mode", quote(mode), false);
      field(json, 1, "status", quote(status), false);
      field(json, 1, "validationBoundary", quote("post-transform-pre-backend"), false);
      field(json, 1, "primarySource", quote(primarySource), false);
      if (sameDefinitionReference != null) {
        field(json, 1, "sameDefinitionReference", sameDefinitionReference.toString(), false);
      }
      field(json, 1, "matchedTargets", Integer.toString(matchedTargets), false);
      field(json, 1, "replacements", Integer.toString(replacements), false);
      json.append("  \"before\": ");
      appendSnapshot(json, before, 1);
      json.append(",\n");
      if (after != null) {
        json.append("  \"after\": ");
        appendSnapshot(json, after, 1);
        json.append(",\n");
      }
      field(json, 1, "error", error == null ? "null" : quote(error), true);
      json.append("}\n");
      return json.toString();
    }

    private static void appendSnapshot(StringBuilder json, Snapshot snapshot, int indent) {
      json.append("{\n");
      field(json, indent + 1, "contentSha256", quote(snapshot.contentSha256), false);
      field(json, indent + 1, "officialTextSha256", quote(snapshot.officialTextSha256), false);
      field(json, indent + 1, "innerAttributesSha256", quote(snapshot.innerAttributesSha256), false);
      field(
          json,
          indent + 1,
          "primarySourceProjectionSha256",
          quote(snapshot.primarySourceProjectionSha256),
          false);
      field(json, indent + 1, "moduleCount", Integer.toString(snapshot.moduleCount), false);
      field(
          json,
          indent + 1,
          "localSentenceCount",
          Integer.toString(snapshot.localSentenceCount),
          false);
      field(json, indent + 1, "kNodeCount", Integer.toString(snapshot.kNodeCount), false);
      field(
          json,
          indent + 1,
          "kNodesWithAttributes",
          Integer.toString(snapshot.kNodesWithAttributes),
          false);
      field(
          json,
          indent + 1,
          "innerProductionAttributeCount",
          Integer.toString(snapshot.innerProductionAttributeCount),
          false);
      field(
          json,
          indent + 1,
          "primarySourceSentenceCount",
          Integer.toString(snapshot.primarySourceSentenceCount),
          false);
      indent(json, indent + 1).append("\"target\": ");
      if (snapshot.target == null) {
        json.append("null\n");
      } else {
        appendTarget(json, snapshot.target, indent + 1);
        json.append('\n');
      }
      indent(json, indent).append('}');
    }

    private static void appendTarget(StringBuilder json, Target target, int indent) {
      json.append("{\n");
      field(json, indent + 1, "module", quote(target.module), false);
      field(json, indent + 1, "label", quote(target.label), false);
      field(json, indent + 1, "source", quote(target.source), false);
      json
          .append("    ".repeat(indent + 1))
          .append("\"location\": [")
          .append(target.location.startLine())
          .append(", ")
          .append(target.location.startColumn())
          .append(", ")
          .append(target.location.endLine())
          .append(", ")
          .append(target.location.endColumn())
          .append("],\n");
      field(json, indent + 1, "uniqueId", target.uniqueId == null ? "null" : quote(target.uniqueId), false);
      field(json, indent + 1, "lineageSha256", quote(target.lineageSha256), false);
      field(json, indent + 1, "sentenceAttSha256", quote(target.sentenceAttSha256), false);
      field(json, indent + 1, "bodySha256", quote(target.bodySha256), false);
      field(json, indent + 1, "requiresSha256", quote(target.requiresSha256), false);
      field(json, indent + 1, "ensuresSha256", quote(target.ensuresSha256), true);
      indent(json, indent).append('}');
    }

    private static void field(
        StringBuilder json, int indent, String name, String value, boolean last) {
      indent(json, indent)
          .append(quote(name))
          .append(": ")
          .append(value)
          .append(last ? "\n" : ",\n");
    }

    private static StringBuilder indent(StringBuilder value, int count) {
      return value.append("  ".repeat(count));
    }
  }

  private static String sha256(String value) {
    try {
      byte[] digest = MessageDigest.getInstance("SHA-256").digest(value.getBytes(StandardCharsets.UTF_8));
      StringBuilder result = new StringBuilder();
      for (byte item : digest) {
        result.append(String.format(Locale.ROOT, "%02x", item & 0xff));
      }
      return result.toString();
    } catch (NoSuchAlgorithmException e) {
      throw new AssertionError(e);
    }
  }

  private static String quote(String value) {
    Objects.requireNonNull(value);
    StringBuilder result = new StringBuilder("\"");
    for (int index = 0; index < value.length(); index++) {
      char ch = value.charAt(index);
      switch (ch) {
        case '\"' -> result.append("\\\"");
        case '\\' -> result.append("\\\\");
        case '\b' -> result.append("\\b");
        case '\f' -> result.append("\\f");
        case '\n' -> result.append("\\n");
        case '\r' -> result.append("\\r");
        case '\t' -> result.append("\\t");
        default -> {
          if (ch < 0x20) {
            result.append(String.format(Locale.ROOT, "\\u%04x", (int) ch));
          } else {
            result.append(ch);
          }
        }
      }
    }
    return result.append('\"').toString();
  }
}
