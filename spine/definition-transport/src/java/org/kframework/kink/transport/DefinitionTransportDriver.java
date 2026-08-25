package org.kframework.kink.transport;

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
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
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
import org.kframework.kore.KORE;
import org.kframework.kore.Sort;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Main;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.RunProcess;
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
 * R2-G definition transport and input-relative patch driver over the pinned official K object graph.
 *
 * <p>The only pipeline difference from KompileFrontEnd is the adapter function composed before
 * Backend.steps(). The driver intentionally uses environment variables for its private controls so
 * the official JCommander option surface remains unchanged.
 */
public final class DefinitionTransportDriver {
  private static final String MODE_ENV = "KINK_TRANSPORT_MODE";
  private static final String RECORD_ENV = "KINK_TRANSPORT_RECORD";
  private static final String DEFINITION_ENV = "KINK_TRANSPORT_KOMPILED";

  private DefinitionTransportDriver() {}

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
    private static final String ID = "OfficialDefinitionAdapter-v1/R2-G-01";
    private static final String PATCH_ID = "OfficialDefinitionAdapter-v1/R2-G-02";
    private static final String TRANSACTION_ID = "OfficialDefinitionAdapter-v1/R2-G-03";
    private static final String TRANSPORT_SCHEMA = "KDefinitionTransport-v1";
    private static final String PATCH_SCHEMA = "KDefinitionPatch-v1";
    private static final String TRANSACTION_SCHEMA = "KDefinitionPatch-v2";
    private static final String PATCH_TRANSFORMATION = "p3-start-to-bump@1";
    private static final String TRANSACTION_TRANSFORMATION = "p3-start-and-add-values@1";
    private static final String SEAM =
        "parseDefinitionAndResolveBubbles -> adapter -> KoreBackend.steps";
    private static final String VALIDATION_BOUNDARY = "post-k-selection-pre-backend";
    private static final Pattern RESULT_PATTERN =
        Pattern.compile("dResult\\s*\\(\\s*\"([0-9a-f]{64})\"\\s*,\\s*(\\d+)\\s*,", Pattern.DOTALL);
    private static final Pattern SELECTION_PATTERN =
        Pattern.compile(
            "dSelection\\s*\\(\\s*\"([0-9a-f]{64})\"\\s*,\\s*\"([0-9a-f]{64})\"\\s*,\\s*\"([0-9a-f]{64})\"\\s*\\)",
            Pattern.DOTALL);

    private final String mode;
    private final Path recordPath;
    private final Path transportDefinition;
    private final String primarySource;

    Adapter(String mode, Path recordPath, File definitionFile) {
      this.mode = mode;
      this.recordPath = recordPath;
      this.transportDefinition =
          Path.of(DriverFrontEnd.requireEnvironment(DEFINITION_ENV)).toAbsolutePath().normalize();
      if (!Files.isRegularFile(this.transportDefinition.resolve("mainModule.txt"))) {
        throw validationError("invalid K transport definition: " + this.transportDefinition);
      }
      try {
        this.primarySource = definitionFile.getCanonicalPath();
      } catch (IOException e) {
        throw KEMException.criticalError("Cannot canonicalize definition path", e);
      }
    }

    Definition apply(Definition input) {
      if (mode.startsWith("transaction")) {
        return applyTransaction(input);
      }
      if (mode.startsWith("patch")) {
        return applyPatch(input);
      }
      return applyIdentity(input);
    }

    private Definition applyIdentity(Definition input) {
      Snapshot before = Snapshot.capture(input, primarySource);
      TransportResult transport = null;
      try {
        if (!List.of("identity", "stale-lineage", "stale-content", "duplicate-target")
            .contains(mode)) {
          throw validationError("unsupported transport mode: " + mode);
        }
        if (!mode.equals("identity") && before.target == null) {
          throw validationError(mode + " requires the P3 structural target");
        }
        String program = TransportProjection.encode(input, primarySource, before, mode);
        transport = invokeK(program, recordPath);
        if (!transport.definitionFingerprint.equals(before.contentSha256)) {
          throw validationError("K result returned a stale definition fingerprint");
        }
        int expectedSelections = before.target == null ? 0 : 1;
        if (transport.selectionCount != expectedSelections) {
          throw validationError(
              "expected "
                  + expectedSelections
                  + " K structural selections, found "
                  + transport.selectionCount);
        }
        if (transport.selections.size() != transport.selectionCount) {
          throw validationError("K result selection count disagrees with its payload");
        }
        if (before.target != null) {
          Selection selected = transport.selections.get(0);
          if (!selected.lineageSha256.equals(before.target.lineageSha256)) {
            throw validationError("K selection returned stale lineage");
          }
          if (!selected.contentSha256.equals(before.target.contentSha256)) {
            throw validationError("K selection returned stale content fingerprint");
          }
          if (!selected.bodySha256.equals(before.target.bodySha256)) {
            throw validationError("K selection returned stale body fingerprint");
          }
        }

        Definition output = input;
        Snapshot after = Snapshot.capture(output, primarySource);
        if (!after.contentSha256.equals(before.contentSha256)
            || !after.innerAttributesSha256.equals(before.innerAttributesSha256)
            || !after.primarySourceProjectionSha256.equals(
                before.primarySourceProjectionSha256)) {
          throw validationError("identity transport changed the official Definition");
        }

        writeRecord(
            Record.accepted(
                mode,
                before,
                after,
                output == input,
                transport.selectionCount,
                transport));
        return output;
      } catch (AdapterValidationException e) {
        writeRecord(Record.rejected(mode, before, e.getMessage(), transport));
        throw KEMException.compilerError("R2-G-01 transport validation failed: " + e.getMessage());
      } catch (RuntimeException e) {
        writeRecord(Record.rejected(mode, before, e.toString(), transport));
        throw e;
      }
    }

    private Definition applyPatch(Definition input) {
      Snapshot before = Snapshot.capture(input, primarySource);
      PatchResult patch = null;
      int applicationCount = 0;
      try {
        if (!List.of("patch", "patch-stale-content", "patch-unsupported-path")
            .contains(mode)) {
          throw validationError("unsupported patch mode: " + mode);
        }
        String program = TransportProjection.encodePatch(input, primarySource, before, mode);
        patch = invokePatchK(program, recordPath);
        validatePatchEnvelope(before, patch);

        LocatedRule located = locateRule(input, primarySource, patch);
        PatchEdit edit = patch.edits.get(0);
        validateSupportedPath(edit.targetPath);
        validateSupportedPath(edit.replacementPath);
        resolvePath(located.rule.body(), edit.targetPath);
        K replacement = resolvePath(located.rule.body(), edit.replacementPath);

        PatchApplication application =
            applySinglePatch(input, located.rule, edit.targetPath, replacement);
        Definition output = application.definition;
        applicationCount = application.applicationCount;
        Snapshot after = Snapshot.capture(output, primarySource);
        int changedLineageCount =
            changedSourceLineageCount(input, output, primarySource);
        validateAppliedPatch(before, after, input, output, applicationCount, changedLineageCount);

        writePatchRecord(
            PatchRecord.accepted(
                mode,
                before,
                after,
                input == output,
                patch,
                applicationCount,
                changedLineageCount));
        return output;
      } catch (AdapterValidationException e) {
        writePatchRecord(
            PatchRecord.rejected(mode, before, patch, applicationCount, e.getMessage()));
        throw KEMException.compilerError("R2-G-02 patch validation failed: " + e.getMessage());
      } catch (RuntimeException e) {
        writePatchRecord(
            PatchRecord.rejected(mode, before, patch, applicationCount, e.toString()));
        throw e;
      }
    }

    private Definition applyTransaction(Definition input) {
      Snapshot before = Snapshot.capture(input, primarySource);
      TransactionResult transaction = null;
      List<PreparedTransactionEdit> prepared = new ArrayList<>();
      List<TransactionEditOutcome> outcomes = List.of();
      int applicationCount = 0;
      int changedLineageCount = 0;
      boolean outputConstructed = false;
      try {
        if (!List.of(
                "transaction",
                "transaction-stale-first",
                "transaction-stale-second",
                "transaction-duplicate-target")
            .contains(mode)) {
          throw validationError("unsupported transaction mode: " + mode);
        }
        String program =
            TransportProjection.encodeTransaction(input, primarySource, before, mode);
        transaction = invokeTransactionK(program, recordPath);
        validateTransactionEnvelope(before, transaction);

        for (TransactionEdit edit : transaction.edits) {
          LocatedRule located =
              locateRule(
                  input,
                  primarySource,
                  edit.targetLineage,
                  edit.targetContent,
                  edit.targetBody,
                  "transaction");
          validateSupportedPath(edit.targetPath);
          validateSupportedPath(edit.replacementPath);
          resolvePath(located.rule.body(), edit.targetPath);
          K replacement = resolvePath(located.rule.body(), edit.replacementPath);
          prepared.add(
              new PreparedTransactionEdit(
                  edit, located, replacement, RuleState.capture(located.module, located.rule)));
        }

        PatchApplication application = applyTransactionEdits(input, prepared);
        Definition output = application.definition;
        outputConstructed = true;
        applicationCount = application.applicationCount;
        Snapshot after = Snapshot.capture(output, primarySource);
        changedLineageCount = changedSourceLineageCount(input, output, primarySource);
        outcomes =
            validateAppliedTransaction(
                before,
                after,
                input,
                output,
                primarySource,
                prepared,
                applicationCount,
                changedLineageCount);

        writeTransactionRecord(
            TransactionRecord.accepted(
                mode,
                before,
                after,
                input == output,
                transaction,
                prepared.size(),
                applicationCount,
                changedLineageCount,
                outputConstructed,
                outcomes));
        return output;
      } catch (AdapterValidationException e) {
        writeTransactionRecord(
            TransactionRecord.rejected(
                mode,
                before,
                transaction,
                prepared.size(),
                applicationCount,
                changedLineageCount,
                outputConstructed,
                outcomes,
                e.getMessage()));
        throw KEMException.compilerError(
            "R2-G-03 transaction validation failed: " + e.getMessage());
      } catch (RuntimeException e) {
        writeTransactionRecord(
            TransactionRecord.rejected(
                mode,
                before,
                transaction,
                prepared.size(),
                applicationCount,
                changedLineageCount,
                outputConstructed,
                outcomes,
                e.toString()));
        throw e;
      }
    }

    private static void validateTransactionEnvelope(
        Snapshot before, TransactionResult transaction) {
      if (!transaction.schema.equals(TRANSACTION_SCHEMA)) {
        throw validationError("unsupported transaction schema: " + transaction.schema);
      }
      if (!transaction.transformation.equals(TRANSACTION_TRANSFORMATION)) {
        throw validationError(
            "unsupported transaction transformation: " + transaction.transformation);
      }
      if (!transaction.definitionFingerprint.equals(before.contentSha256)) {
        throw validationError("transaction returned a stale definition fingerprint");
      }
      if (transaction.transactionCount != 1) {
        throw validationError(
            "expected transaction cardinality 1, found " + transaction.transactionCount);
      }
      if (transaction.editCount != 2 || transaction.edits.size() != 2) {
        throw validationError(
            "expected two transaction edits, found "
                + transaction.editCount
                + " declared and "
                + transaction.edits.size()
                + " encoded");
      }
      for (TransactionEdit edit : transaction.edits) {
        if (!edit.targetLineage.matches("[0-9a-f]{64}")
            || !edit.targetContent.matches("[0-9a-f]{64}")
            || !edit.targetBody.matches("[0-9a-f]{64}")) {
          throw validationError("transaction contains a malformed target fingerprint");
        }
      }
      String first = transaction.edits.get(0).canonical();
      String second = transaction.edits.get(1).canonical();
      if (first.compareTo(second) > 0) {
        throw validationError("transaction edits are not in canonical order");
      }
      Set<String> lineages = new HashSet<>();
      for (TransactionEdit edit : transaction.edits) {
        if (!lineages.add(edit.targetLineage)) {
          throw validationError("transaction contains duplicate target lineage");
        }
      }
    }

    private static void validatePatchEnvelope(Snapshot before, PatchResult patch) {
      if (!patch.schema.equals(PATCH_SCHEMA)) {
        throw validationError("unsupported patch schema: " + patch.schema);
      }
      if (!patch.transformation.equals(PATCH_TRANSFORMATION)) {
        throw validationError("unsupported patch transformation: " + patch.transformation);
      }
      if (!patch.definitionFingerprint.equals(before.contentSha256)) {
        throw validationError("patch returned a stale definition fingerprint");
      }
      if (patch.patchCount != 1) {
        throw validationError("expected patch cardinality 1, found " + patch.patchCount);
      }
      if (patch.editCount != 1 || patch.edits.size() != 1) {
        throw validationError(
            "expected one patch edit, found "
                + patch.editCount
                + " declared and "
                + patch.edits.size()
                + " encoded");
      }
      if (!patch.targetLineage.matches("[0-9a-f]{64}")
          || !patch.targetContent.matches("[0-9a-f]{64}")
          || !patch.targetBody.matches("[0-9a-f]{64}")) {
        throw validationError("patch contains a malformed target fingerprint");
      }
    }

    private static LocatedRule locateRule(
        Definition definition, String primarySource, PatchResult patch) {
      return locateRule(
          definition,
          primarySource,
          patch.targetLineage,
          patch.targetContent,
          patch.targetBody,
          "patch");
    }

    private static LocatedRule locateRule(
        Definition definition,
        String primarySource,
        String targetLineage,
        String targetContent,
        String targetBody,
        String owner) {
      LocatedRule located = locateRuleByLineage(definition, primarySource, targetLineage);
      if (!Snapshot.sentenceDigest(located.rule).equals(targetContent)) {
        throw validationError(owner + " returned stale target content fingerprint");
      }
      if (!Target.kDigest(located.rule.body()).equals(targetBody)) {
        throw validationError(owner + " returned stale target body fingerprint");
      }
      return located;
    }

    private static LocatedRule locateRuleByLineage(
        Definition definition, String primarySource, String targetLineage) {
      List<LocatedRule> lineageMatches = new ArrayList<>();
      for (Module module : stream(definition.modules()).toList()) {
        for (Sentence sentence : stream(module.localSentences()).toList()) {
          if (!(sentence instanceof Rule rule)
              || !rule.source()
                  .map(Source::source)
                  .map(source -> Snapshot.sameSource(source, primarySource))
                  .orElse(false)) {
            continue;
          }
          if (Target.lineage(module.name(), rule).equals(targetLineage)) {
            lineageMatches.add(new LocatedRule(module.name(), rule));
          }
        }
      }
      if (lineageMatches.size() != 1) {
        throw validationError(
            "expected one target lineage in the original definition, found "
                + lineageMatches.size());
      }
      LocatedRule located = lineageMatches.get(0);
      return located;
    }

    private static void validateSupportedPath(TermPath path) {
      if (path.steps.isEmpty()) {
        throw validationError("patch path must not be empty");
      }
      for (PathStep step : path.steps) {
        if (step instanceof ApplicationArgumentStep argument && argument.index < 0) {
          throw validationError("application argument index must be non-negative");
        }
        if (step instanceof SequenceItemStep sequence) {
          throw validationError("unsupported path step: dSequenceItem(" + sequence.index + ")");
        }
      }
    }

    private static K resolvePath(K root, TermPath path) {
      K current = root;
      for (PathStep step : path.steps) {
        if (step instanceof RewriteLeftStep) {
          if (!(current instanceof KRewrite rewrite)) {
            throw validationError("dRewriteLeft does not address a rewrite");
          }
          current = rewrite.left();
        } else if (step instanceof RewriteRightStep) {
          if (!(current instanceof KRewrite rewrite)) {
            throw validationError("dRewriteRight does not address a rewrite");
          }
          current = rewrite.right();
        } else if (step instanceof ApplicationArgumentStep argument) {
          if (!(current instanceof KApply application)) {
            throw validationError("dApplicationArgument does not address an application");
          }
          List<K> items = application.klist().items();
          if (argument.index < 0 || argument.index >= items.size()) {
            throw validationError(
                "application argument index "
                    + argument.index
                    + " is outside arity "
                    + items.size());
          }
          current = items.get(argument.index);
        } else {
          throw validationError("unsupported path step: " + step.canonical());
        }
      }
      return current;
    }

    private static PatchApplication applySinglePatch(
        Definition input, Rule originalRule, TermPath targetPath, K replacement) {
      AtomicInteger applications = new AtomicInteger();
      DefinitionTransformer transformer =
          DefinitionTransformer.fromSentenceTransformer(
              sentence -> {
                if (sentence != originalRule) {
                  return sentence;
                }
                K body = replaceAt(originalRule.body(), targetPath.steps, 0, replacement);
                applications.incrementAndGet();
                return Rule.apply(
                    body,
                    originalRule.requires(),
                    originalRule.ensures(),
                    originalRule.att());
              },
              "R2-G-02 canonical input-relative single-sentence patch");
      return new PatchApplication(transformer.apply(input), applications.get());
    }

    private static PatchApplication applyTransactionEdits(
        Definition input, List<PreparedTransactionEdit> prepared) {
      IdentityHashMap<Rule, PreparedTransactionEdit> byRule = new IdentityHashMap<>();
      for (PreparedTransactionEdit item : prepared) {
        if (byRule.put(item.located.rule, item) != null) {
          throw validationError("transaction contains duplicate original rule reference");
        }
      }
      AtomicInteger applications = new AtomicInteger();
      DefinitionTransformer transformer =
          DefinitionTransformer.fromSentenceTransformer(
              sentence -> {
                if (!(sentence instanceof Rule rule)) {
                  return sentence;
                }
                PreparedTransactionEdit item = byRule.get(rule);
                if (item == null) {
                  return sentence;
                }
                K body =
                    replaceAt(
                        rule.body(), item.edit.targetPath.steps, 0, item.replacement);
                applications.incrementAndGet();
                return Rule.apply(body, rule.requires(), rule.ensures(), rule.att());
              },
              "R2-G-03 canonical input-relative two-sentence transaction");
      return new PatchApplication(transformer.apply(input), applications.get());
    }

    private static K replaceAt(
        K current, List<PathStep> steps, int offset, K replacement) {
      if (offset == steps.size()) {
        return replacement;
      }
      PathStep step = steps.get(offset);
      if (step instanceof RewriteLeftStep) {
        if (!(current instanceof KRewrite rewrite)) {
          throw validationError("dRewriteLeft does not address a rewrite");
        }
        return KORE.KRewrite(
            replaceAt(rewrite.left(), steps, offset + 1, replacement),
            rewrite.right(),
            rewrite.att());
      }
      if (step instanceof RewriteRightStep) {
        if (!(current instanceof KRewrite rewrite)) {
          throw validationError("dRewriteRight does not address a rewrite");
        }
        return KORE.KRewrite(
            rewrite.left(),
            replaceAt(rewrite.right(), steps, offset + 1, replacement),
            rewrite.att());
      }
      if (step instanceof ApplicationArgumentStep argument) {
        if (!(current instanceof KApply application)) {
          throw validationError("dApplicationArgument does not address an application");
        }
        List<K> items = new ArrayList<>(application.klist().items());
        if (argument.index < 0 || argument.index >= items.size()) {
          throw validationError(
              "application argument index "
                  + argument.index
                  + " is outside arity "
                  + items.size());
        }
        items.set(
            argument.index,
            replaceAt(items.get(argument.index), steps, offset + 1, replacement));
        return KORE.KApply(
            application.klabel(), KORE.KList(items), application.att());
      }
      throw validationError("unsupported path step: " + step.canonical());
    }

    private static int changedSourceLineageCount(
        Definition before, Definition after, String primarySource) {
      Map<String, String> beforeContent = sourceContentByLineage(before, primarySource);
      Map<String, String> afterContent = sourceContentByLineage(after, primarySource);
      if (!beforeContent.keySet().equals(afterContent.keySet())) {
        throw validationError("patch changed the source-sentence lineage set");
      }
      int changed = 0;
      for (String lineage : beforeContent.keySet()) {
        if (!beforeContent.get(lineage).equals(afterContent.get(lineage))) {
          changed++;
        }
      }
      return changed;
    }

    private static Map<String, String> sourceContentByLineage(
        Definition definition, String primarySource) {
      Map<String, String> result = new TreeMap<>();
      for (Module module : stream(definition.modules()).toList()) {
        for (Sentence sentence : stream(module.localSentences()).toList()) {
          String source = sentence.source().map(Source::source).orElse(null);
          if (source == null || !Snapshot.sameSource(source, primarySource)) {
            continue;
          }
          String lineage =
              sha256(
                  module.name()
                      + "|"
                      + sentence.getClass().getName()
                      + "|"
                      + sentence.label().orElse("")
                      + "|"
                      + source
                      + "|"
                      + sentence.location().map(Object::toString).orElse(""));
          if (result.put(lineage, Snapshot.sentenceDigest(sentence)) != null) {
            throw validationError("duplicate source-sentence lineage: " + lineage);
          }
        }
      }
      return result;
    }

    private static void validateAppliedPatch(
        Snapshot before,
        Snapshot after,
        Definition input,
        Definition output,
        int applicationCount,
        int changedLineageCount) {
      if (applicationCount != 1) {
        throw validationError("expected one patch application, found " + applicationCount);
      }
      if (input == output) {
        throw validationError("patch returned the original Definition reference");
      }
      if (changedLineageCount != 1) {
        throw validationError(
            "expected one changed source-sentence lineage, found " + changedLineageCount);
      }
      if (before.moduleCount != after.moduleCount
          || before.localSentenceCount != after.localSentenceCount) {
        throw validationError("patch changed module or local-sentence cardinality");
      }
      if (before.target == null || after.target == null) {
        throw validationError("patch target provenance is missing after application");
      }
      if (!before.target.lineageSha256.equals(after.target.lineageSha256)) {
        throw validationError("patch target lineage changed");
      }
      if (!before.target.sentenceAttSha256.equals(after.target.sentenceAttSha256)) {
        throw validationError("patch target sentence attributes changed");
      }
      if (!before.target.requiresSha256.equals(after.target.requiresSha256)
          || !before.target.ensuresSha256.equals(after.target.ensuresSha256)) {
        throw validationError("patch target side conditions changed");
      }
      if (before.target.contentSha256.equals(after.target.contentSha256)
          || before.target.bodySha256.equals(after.target.bodySha256)
          || before.contentSha256.equals(after.contentSha256)) {
        throw validationError("patch did not change all required content fingerprints");
      }
    }

    private static List<TransactionEditOutcome> validateAppliedTransaction(
        Snapshot before,
        Snapshot after,
        Definition input,
        Definition output,
        String primarySource,
        List<PreparedTransactionEdit> prepared,
        int applicationCount,
        int changedLineageCount) {
      if (applicationCount != 2) {
        throw validationError(
            "expected two transaction applications, found " + applicationCount);
      }
      if (input == output) {
        throw validationError("transaction returned the original Definition reference");
      }
      if (changedLineageCount != 2) {
        throw validationError(
            "expected two changed source-sentence lineages, found " + changedLineageCount);
      }
      if (before.moduleCount != after.moduleCount
          || before.localSentenceCount != after.localSentenceCount) {
        throw validationError("transaction changed module or local-sentence cardinality");
      }
      if (before.contentSha256.equals(after.contentSha256)) {
        throw validationError("transaction did not change the definition fingerprint");
      }

      List<TransactionEditOutcome> outcomes = new ArrayList<>();
      for (PreparedTransactionEdit item : prepared) {
        LocatedRule afterRule =
            locateRuleByLineage(output, primarySource, item.edit.targetLineage);
        RuleState afterState = RuleState.capture(afterRule.module, afterRule.rule);
        RuleState beforeState = item.before;
        if (!beforeState.lineageSha256.equals(afterState.lineageSha256)) {
          throw validationError("transaction target lineage changed");
        }
        if (!beforeState.sentenceAttSha256.equals(afterState.sentenceAttSha256)) {
          throw validationError("transaction target sentence attributes changed");
        }
        if (!beforeState.requiresSha256.equals(afterState.requiresSha256)
            || !beforeState.ensuresSha256.equals(afterState.ensuresSha256)) {
          throw validationError("transaction target side conditions changed");
        }
        if (beforeState.contentSha256.equals(afterState.contentSha256)
            || beforeState.bodySha256.equals(afterState.bodySha256)) {
          throw validationError(
              "transaction did not change target content and body fingerprints");
        }
        outcomes.add(new TransactionEditOutcome(beforeState, afterState));
      }
      return List.copyOf(outcomes);
    }

    private static AdapterValidationException validationError(String message) {
      return new AdapterValidationException(message);
    }

    private TransportResult invokeK(String program, Path recordPath) {
      return parseResult(invokeKOutput(program, recordPath));
    }

    private PatchResult invokePatchK(String program, Path recordPath) {
      String output = invokeKOutput(program, recordPath);
      PatchResult parsed = PatchParser.parse(output);
      return parsed.withOutputSha256(sha256(output));
    }

    private TransactionResult invokeTransactionK(String program, Path recordPath) {
      String output = invokeKOutput(program, recordPath);
      TransactionResult parsed = TransactionParser.parse(output);
      return parsed.withOutputSha256(sha256(output));
    }

    private String invokeKOutput(String program, Path recordPath) {
      Path parent = recordPath.getParent();
      try {
        if (parent != null) {
          Files.createDirectories(parent);
        }
        Path programPath =
            Files.createTempFile(parent == null ? Path.of(".") : parent, "transport-", ".kink");
        try {
          Files.writeString(programPath, program, StandardCharsets.UTF_8);
          RunProcess.ProcessOutput process =
              RunProcess.execute(
                  Map.of("LC_ALL", "C", "LANG", "C", "TZ", "UTC"),
                  new ProcessBuilder(),
                  "krun",
                  programPath.toString(),
                  "--definition",
                  transportDefinition.toString(),
                  "--output",
                  "pretty");
          String stdout = new String(process.stdout(), StandardCharsets.UTF_8);
          String stderr = new String(process.stderr(), StandardCharsets.UTF_8);
          if (process.exitCode() != 0) {
            throw validationError(
                "K transport execution failed with exit "
                    + process.exitCode()
                    + ": "
                    + stderr.strip());
          }
          return stdout;
        } finally {
          Files.deleteIfExists(programPath);
        }
      } catch (IOException e) {
        throw KEMException.criticalError("Cannot execute K definition transport", e);
      }
    }

    private static TransportResult parseResult(String output) {
      Matcher result = RESULT_PATTERN.matcher(output);
      if (!result.find()) {
        throw validationError("cannot parse typed K transport result");
      }
      String definitionFingerprint = result.group(1);
      int selectionCount = Integer.parseInt(result.group(2));
      List<Selection> selections = new ArrayList<>();
      Matcher selection = SELECTION_PATTERN.matcher(output);
      while (selection.find()) {
        selections.add(new Selection(selection.group(1), selection.group(2), selection.group(3)));
      }
      String encodedSelections = "dSelectionNil";
      for (int index = selections.size() - 1; index >= 0; index--) {
        Selection item = selections.get(index);
        encodedSelections =
            "dSelectionCons(dSelection(\""
                + item.lineageSha256
                + "\",\""
                + item.contentSha256
                + "\",\""
                + item.bodySha256
                + "\"),"
                + encodedSelections
                + ")";
      }
      String expected =
          "<k>dResult(\""
              + definitionFingerprint
              + "\","
              + selectionCount
              + ","
              + encodedSelections
              + ")~>.K</k>";
      if (!output.replaceAll("\\s+", "").equals(expected)) {
        throw validationError("K transport returned unexpected residual structure");
      }
      return new TransportResult(
          definitionFingerprint, selectionCount, selections, sha256(output));
    }

    private void writeRecord(Record record) {
      try {
        Path parent = recordPath.getParent();
        if (parent != null) {
          Files.createDirectories(parent);
        }
        Files.writeString(
            recordPath,
            record.toJson(ID, SEAM, VALIDATION_BOUNDARY, primarySource),
            StandardCharsets.UTF_8);
      } catch (IOException e) {
        throw KEMException.criticalError("Cannot write R2-G-01 transport record " + recordPath, e);
      }
    }

    private void writePatchRecord(PatchRecord record) {
      try {
        Path parent = recordPath.getParent();
        if (parent != null) {
          Files.createDirectories(parent);
        }
        Files.writeString(
            recordPath,
            record.toJson(PATCH_ID, SEAM, primarySource),
            StandardCharsets.UTF_8);
      } catch (IOException e) {
        throw KEMException.criticalError("Cannot write R2-G-02 patch record " + recordPath, e);
      }
    }

    private void writeTransactionRecord(TransactionRecord record) {
      try {
        Path parent = recordPath.getParent();
        if (parent != null) {
          Files.createDirectories(parent);
        }
        Files.writeString(
            recordPath,
            record.toJson(TRANSACTION_ID, SEAM, primarySource),
            StandardCharsets.UTF_8);
      } catch (IOException e) {
        throw KEMException.criticalError(
            "Cannot write R2-G-03 transaction record " + recordPath, e);
      }
    }
  }

  private static final class AdapterValidationException extends RuntimeException {
    AdapterValidationException(String message) {
      super(message);
    }
  }

  private record Selection(String lineageSha256, String contentSha256, String bodySha256) {}

  private record TransportResult(
      String definitionFingerprint,
      int selectionCount,
      List<Selection> selections,
      String outputSha256) {}

  private interface PathStep {
    String canonical();
  }

  private record RewriteLeftStep() implements PathStep {
    @Override
    public String canonical() {
      return "dRewriteLeft";
    }
  }

  private record RewriteRightStep() implements PathStep {
    @Override
    public String canonical() {
      return "dRewriteRight";
    }
  }

  private record ApplicationArgumentStep(int index) implements PathStep {
    @Override
    public String canonical() {
      return "dApplicationArgument(" + index + ")";
    }
  }

  private record SequenceItemStep(int index) implements PathStep {
    @Override
    public String canonical() {
      return "dSequenceItem(" + index + ")";
    }
  }

  private record TermPath(List<PathStep> steps) {
    TermPath {
      steps = List.copyOf(steps);
    }

    String canonical() {
      String result = "dPathNil";
      for (int index = steps.size() - 1; index >= 0; index--) {
        result = "dPathCons(" + steps.get(index).canonical() + "," + result + ")";
      }
      return result;
    }
  }

  private record PatchEdit(TermPath targetPath, TermPath replacementPath) {
    String canonical() {
      return "dReplaceTermFromInput("
          + targetPath.canonical()
          + ","
          + replacementPath.canonical()
          + ")";
    }
  }

  private record PatchResult(
      String schema,
      String transformation,
      String definitionFingerprint,
      int patchCount,
      String targetLineage,
      String targetContent,
      String targetBody,
      int editCount,
      List<PatchEdit> edits,
      String outputSha256) {
    PatchResult {
      edits = List.copyOf(edits);
    }

    PatchResult withOutputSha256(String value) {
      return new PatchResult(
          schema,
          transformation,
          definitionFingerprint,
          patchCount,
          targetLineage,
          targetContent,
          targetBody,
          editCount,
          edits,
          value);
    }

    String canonical() {
      String encodedEdits = "dEditNil";
      for (int index = edits.size() - 1; index >= 0; index--) {
        encodedEdits = "dEditCons(" + edits.get(index).canonical() + "," + encodedEdits + ")";
      }
      return "dPatchResult("
          + quote(schema)
          + ","
          + quote(transformation)
          + ","
          + quote(definitionFingerprint)
          + ","
          + patchCount
          + ","
          + quote(targetLineage)
          + ","
          + quote(targetContent)
          + ","
          + quote(targetBody)
          + ","
          + editCount
          + ","
          + encodedEdits
          + ")";
    }

    String canonicalSha256() {
      return sha256(canonical());
    }
  }

  private record TransactionEdit(
      String targetLineage,
      String targetContent,
      String targetBody,
      TermPath targetPath,
      TermPath replacementPath) {
    String canonical() {
      return "dTransactionEdit("
          + quote(targetLineage)
          + ","
          + quote(targetContent)
          + ","
          + quote(targetBody)
          + ",dReplaceTermFromInput("
          + targetPath.canonical()
          + ","
          + replacementPath.canonical()
          + "))";
    }
  }

  private record TransactionResult(
      String schema,
      String transformation,
      String definitionFingerprint,
      int transactionCount,
      int editCount,
      List<TransactionEdit> edits,
      String outputSha256) {
    TransactionResult {
      edits = List.copyOf(edits);
    }

    TransactionResult withOutputSha256(String value) {
      return new TransactionResult(
          schema,
          transformation,
          definitionFingerprint,
          transactionCount,
          editCount,
          edits,
          value);
    }

    String canonical() {
      String encodedEdits = "dTransactionEditNil";
      for (int index = edits.size() - 1; index >= 0; index--) {
        encodedEdits =
            "dTransactionEditCons("
                + edits.get(index).canonical()
                + ","
                + encodedEdits
                + ")";
      }
      return "dTransactionResult("
          + quote(schema)
          + ","
          + quote(transformation)
          + ","
          + quote(definitionFingerprint)
          + ","
          + transactionCount
          + ","
          + editCount
          + ","
          + encodedEdits
          + ")";
    }

    String canonicalSha256() {
      return sha256(canonical());
    }
  }

  private record LocatedRule(String module, Rule rule) {}

  private record PatchApplication(Definition definition, int applicationCount) {}

  private record RuleState(
      String module,
      String lineageSha256,
      String contentSha256,
      String sentenceAttSha256,
      String bodySha256,
      String requiresSha256,
      String ensuresSha256) {
    static RuleState capture(String module, Rule rule) {
      return new RuleState(
          module,
          Target.lineage(module, rule),
          Snapshot.sentenceDigest(rule),
          sha256(rule.att().toString()),
          Target.kDigest(rule.body()),
          Target.kDigest(rule.requires()),
          Target.kDigest(rule.ensures()));
    }
  }

  private record PreparedTransactionEdit(
      TransactionEdit edit, LocatedRule located, K replacement, RuleState before) {}

  private record TransactionEditOutcome(RuleState before, RuleState after) {}

  private static final class PatchParser {
    private PatchParser() {}

    static PatchResult parse(String output) {
      TermReader reader = new TermReader(output);
      reader.expect("<k>");
      reader.expectIdentifier("dPatchResult");
      reader.expect('(');
      String schema = reader.readString();
      reader.expect(',');
      String transformation = reader.readString();
      reader.expect(',');
      String definitionFingerprint = reader.readString();
      reader.expect(',');
      int patchCount = reader.readInt();
      reader.expect(',');
      String targetLineage = reader.readString();
      reader.expect(',');
      String targetContent = reader.readString();
      reader.expect(',');
      String targetBody = reader.readString();
      reader.expect(',');
      int editCount = reader.readInt();
      reader.expect(',');
      List<PatchEdit> edits = readEdits(reader);
      reader.expect(')');
      reader.expect("~>");
      reader.expect(".K");
      reader.expect("</k>");
      reader.expectEnd();
      return new PatchResult(
          schema,
          transformation,
          definitionFingerprint,
          patchCount,
          targetLineage,
          targetContent,
          targetBody,
          editCount,
          edits,
          null);
    }

    private static List<PatchEdit> readEdits(TermReader reader) {
      String constructor = reader.readIdentifier();
      if (constructor.equals("dEditNil")) {
        return List.of();
      }
      if (!constructor.equals("dEditCons")) {
        throw Adapter.validationError("unexpected edit-list constructor: " + constructor);
      }
      reader.expect('(');
      PatchEdit first = readEdit(reader);
      reader.expect(',');
      List<PatchEdit> rest = readEdits(reader);
      reader.expect(')');
      List<PatchEdit> result = new ArrayList<>();
      result.add(first);
      result.addAll(rest);
      return result;
    }

    private static PatchEdit readEdit(TermReader reader) {
      reader.expectIdentifier("dReplaceTermFromInput");
      reader.expect('(');
      TermPath target = readPath(reader);
      reader.expect(',');
      TermPath replacement = readPath(reader);
      reader.expect(')');
      return new PatchEdit(target, replacement);
    }

    private static TermPath readPath(TermReader reader) {
      String constructor = reader.readIdentifier();
      if (constructor.equals("dPathNil")) {
        return new TermPath(List.of());
      }
      if (!constructor.equals("dPathCons")) {
        throw Adapter.validationError("unexpected path constructor: " + constructor);
      }
      reader.expect('(');
      PathStep first = readStep(reader);
      reader.expect(',');
      TermPath rest = readPath(reader);
      reader.expect(')');
      List<PathStep> result = new ArrayList<>();
      result.add(first);
      result.addAll(rest.steps);
      return new TermPath(result);
    }

    private static PathStep readStep(TermReader reader) {
      String constructor = reader.readIdentifier();
      return switch (constructor) {
        case "dRewriteLeft" -> new RewriteLeftStep();
        case "dRewriteRight" -> new RewriteRightStep();
        case "dApplicationArgument" -> {
          reader.expect('(');
          int index = reader.readInt();
          reader.expect(')');
          yield new ApplicationArgumentStep(index);
        }
        case "dSequenceItem" -> {
          reader.expect('(');
          int index = reader.readInt();
          reader.expect(')');
          yield new SequenceItemStep(index);
        }
        default -> throw Adapter.validationError("unknown path-step constructor: " + constructor);
      };
    }
  }

  private static final class TransactionParser {
    private TransactionParser() {}

    static TransactionResult parse(String output) {
      TermReader reader = new TermReader(output);
      reader.expect("<k>");
      reader.expectIdentifier("dTransactionResult");
      reader.expect('(');
      String schema = reader.readString();
      reader.expect(',');
      String transformation = reader.readString();
      reader.expect(',');
      String definitionFingerprint = reader.readString();
      reader.expect(',');
      int transactionCount = reader.readInt();
      reader.expect(',');
      int editCount = reader.readInt();
      reader.expect(',');
      List<TransactionEdit> edits = readEdits(reader);
      reader.expect(')');
      reader.expect("~>");
      reader.expect(".K");
      reader.expect("</k>");
      reader.expectEnd();
      return new TransactionResult(
          schema,
          transformation,
          definitionFingerprint,
          transactionCount,
          editCount,
          edits,
          null);
    }

    private static List<TransactionEdit> readEdits(TermReader reader) {
      String constructor = reader.readIdentifier();
      if (constructor.equals("dTransactionEditNil")) {
        return List.of();
      }
      if (!constructor.equals("dTransactionEditCons")) {
        throw Adapter.validationError(
            "unexpected transaction-edit-list constructor: " + constructor);
      }
      reader.expect('(');
      TransactionEdit first = readEdit(reader);
      reader.expect(',');
      List<TransactionEdit> rest = readEdits(reader);
      reader.expect(')');
      List<TransactionEdit> result = new ArrayList<>();
      result.add(first);
      result.addAll(rest);
      return result;
    }

    private static TransactionEdit readEdit(TermReader reader) {
      reader.expectIdentifier("dTransactionEdit");
      reader.expect('(');
      String lineage = reader.readString();
      reader.expect(',');
      String content = reader.readString();
      reader.expect(',');
      String body = reader.readString();
      reader.expect(',');
      reader.expectIdentifier("dReplaceTermFromInput");
      reader.expect('(');
      TermPath target = PatchParser.readPath(reader);
      reader.expect(',');
      TermPath replacement = PatchParser.readPath(reader);
      reader.expect(')');
      reader.expect(')');
      return new TransactionEdit(lineage, content, body, target, replacement);
    }
  }

  private static final class TermReader {
    private final String input;
    private int offset;

    TermReader(String input) {
      this.input = input;
    }

    void expect(String value) {
      skipWhitespace();
      if (!input.startsWith(value, offset)) {
        throw Adapter.validationError("expected '" + value + "' at patch-result offset " + offset);
      }
      offset += value.length();
    }

    void expect(char value) {
      skipWhitespace();
      if (offset >= input.length() || input.charAt(offset) != value) {
        throw Adapter.validationError("expected '" + value + "' at patch-result offset " + offset);
      }
      offset++;
    }

    void expectIdentifier(String value) {
      String actual = readIdentifier();
      if (!actual.equals(value)) {
        throw Adapter.validationError(
            "expected patch constructor " + value + ", found " + actual);
      }
    }

    String readIdentifier() {
      skipWhitespace();
      int start = offset;
      while (offset < input.length()) {
        char ch = input.charAt(offset);
        if (!Character.isLetterOrDigit(ch) && ch != '_' && ch != '#') {
          break;
        }
        offset++;
      }
      if (start == offset) {
        throw Adapter.validationError("expected patch constructor at offset " + offset);
      }
      return input.substring(start, offset);
    }

    int readInt() {
      skipWhitespace();
      int start = offset;
      if (offset < input.length() && input.charAt(offset) == '-') {
        offset++;
      }
      while (offset < input.length() && Character.isDigit(input.charAt(offset))) {
        offset++;
      }
      if (start == offset || (offset == start + 1 && input.charAt(start) == '-')) {
        throw Adapter.validationError("expected integer at patch-result offset " + start);
      }
      try {
        return Integer.parseInt(input.substring(start, offset));
      } catch (NumberFormatException e) {
        throw Adapter.validationError("patch integer is outside the supported range");
      }
    }

    String readString() {
      skipWhitespace();
      if (offset >= input.length() || input.charAt(offset) != '"') {
        throw Adapter.validationError("expected string at patch-result offset " + offset);
      }
      offset++;
      StringBuilder result = new StringBuilder();
      while (offset < input.length()) {
        char ch = input.charAt(offset++);
        if (ch == '"') {
          return result.toString();
        }
        if (ch != '\\') {
          result.append(ch);
          continue;
        }
        if (offset >= input.length()) {
          throw Adapter.validationError("unterminated escape in patch string");
        }
        char escaped = input.charAt(offset++);
        switch (escaped) {
          case '"' -> result.append('"');
          case '\\' -> result.append('\\');
          case 'b' -> result.append('\b');
          case 'f' -> result.append('\f');
          case 'n' -> result.append('\n');
          case 'r' -> result.append('\r');
          case 't' -> result.append('\t');
          case 'u' -> {
            if (offset + 4 > input.length()) {
              throw Adapter.validationError("short unicode escape in patch string");
            }
            try {
              result.append((char) Integer.parseInt(input.substring(offset, offset + 4), 16));
            } catch (NumberFormatException e) {
              throw Adapter.validationError("invalid unicode escape in patch string");
            }
            offset += 4;
          }
          default -> throw Adapter.validationError("invalid escape in patch string");
        }
      }
      throw Adapter.validationError("unterminated patch string");
    }

    void expectEnd() {
      skipWhitespace();
      if (offset != input.length()) {
        throw Adapter.validationError("unexpected residual K patch result at offset " + offset);
      }
    }

    private void skipWhitespace() {
      while (offset < input.length() && Character.isWhitespace(input.charAt(offset))) {
        offset++;
      }
    }
  }

  private static final class TransportProjection {
    private TransportProjection() {}

    static String encode(
        Definition definition, String primarySource, Snapshot snapshot, String mode) {
      return "selectDefinition("
          + encodeDefinition(definition, primarySource, snapshot, mode)
          + ")\n";
    }

    static String encodePatch(
        Definition definition, String primarySource, Snapshot snapshot, String mode) {
      return "proposeDefinitionPatch("
          + quote(mode)
          + ", "
          + encodeDefinition(definition, primarySource, snapshot, mode)
          + ")\n";
    }

    static String encodeTransaction(
        Definition definition, String primarySource, Snapshot snapshot, String mode) {
      return "proposeDefinitionTransaction("
          + quote(mode)
          + ", "
          + encodeDefinition(definition, primarySource, snapshot, mode)
          + ")\n";
    }

    private static String encodeDefinition(
        Definition definition, String primarySource, Snapshot snapshot, String mode) {
      List<Module> modules =
          stream(definition.modules()).sorted(Comparator.comparing(Module::name)).toList();
      List<String> encodedModules = new ArrayList<>();
      for (Module module : modules) {
        List<Rule> rules =
            stream(module.localSentences())
                .filter(Rule.class::isInstance)
                .map(Rule.class::cast)
                .filter(
                    rule ->
                        rule.source()
                            .map(Source::source)
                            .map(source -> Snapshot.sameSource(source, primarySource))
                            .orElse(false))
                .sorted(
                    Comparator.comparing(
                        rule -> rule.getClass().getName() + "|" + rule + "|" + rule.att()))
                .toList();
        if (rules.isEmpty()) {
          continue;
        }

        List<String> encodedRules = new ArrayList<>();
        for (int index = 0; index < rules.size(); index++) {
          Rule rule = rules.get(index);
          encodedRules.add(encodeRule(module.name(), index, rule, mode));
          if (mode.equals("duplicate-target")
              && rule.label().orElse("").equals("start-program")) {
            encodedRules.add(encodeRule(module.name(), index, rule, mode));
          }
        }

        List<String> imports =
            stream(module.imports())
                .map(
                    item ->
                        "dImport("
                            + quote(item.module().name())
                            + ", "
                            + item.isPublic()
                            + ")")
                .sorted()
                .toList();
        encodedModules.add(
            "dModule("
                + quote(module.name())
                + ", "
                + encodeList("dImportNil", "dImportCons", imports)
                + ", "
                + encodeList("dSentenceNil", "dSentenceCons", encodedRules)
                + ")");
      }

      return "dDefinition("
          + quote(Adapter.TRANSPORT_SCHEMA)
          + ", "
          + quote(snapshot.contentSha256)
          + ", "
          + encodeList("dModuleNil", "dModuleCons", encodedModules)
          + ")";
    }

    private static String encodeRule(String module, int occurrence, Rule rule, String mode) {
      String label = rule.label().orElse("");
      String source = rule.source().map(Source::source).orElse("");
      String location = rule.location().map(Object::toString).orElse("");
      String lineage = Target.lineage(module, rule);
      String content = Snapshot.sentenceDigest(rule);
      if (mode.equals("stale-lineage") && label.equals("start-program")) {
        lineage = "0".repeat(64);
      }
      if (mode.equals("stale-content") && label.equals("start-program")) {
        content = "0".repeat(64);
      }
      return "dRule(dIdentity("
          + quote(module)
          + ", "
          + occurrence
          + ", "
          + quote("Rule")
          + ", "
          + quote(label)
          + ", "
          + quote(source)
          + ", "
          + quote(location)
          + ", "
          + quote(lineage)
          + ", "
          + quote(content)
          + "), "
          + encodeTerm(rule.body())
          + ", "
          + encodeTerm(rule.requires())
          + ", "
          + encodeTerm(rule.ensures())
          + ", "
          + quote(rule.att().toString())
          + ", "
          + quote(sha256(rule.att().toString()))
          + ", "
          + quote(Target.kDigest(rule.body()))
          + ")";
    }

    private static String encodeTerm(K value) {
      String meta = encodeMeta(value);
      if (value instanceof KApply application) {
        List<String> arguments = application.klist().items().stream().map(TransportProjection::encodeTerm).toList();
        return "dApply("
            + quote(application.klabel().name())
            + ", "
            + encodeList("dTermNil", "dTermCons", arguments)
            + ", "
            + meta
            + ")";
      }
      if (value instanceof KToken token) {
        return "dToken(" + quote(token.sort().toString()) + ", " + quote(token.s()) + ", " + meta + ")";
      }
      if (value instanceof KVariable variable) {
        return "dVariable(" + quote(variable.name()) + ", " + meta + ")";
      }
      if (value instanceof KRewrite rewrite) {
        return "dRewrite("
            + encodeTerm(rewrite.left())
            + ", "
            + encodeTerm(rewrite.right())
            + ", "
            + meta
            + ")";
      }
      if (value instanceof KSequence sequence) {
        List<String> items = sequence.items().stream().map(TransportProjection::encodeTerm).toList();
        return "dSequence("
            + encodeList("dTermNil", "dTermCons", items)
            + ", "
            + meta
            + ")";
      }
      if (value instanceof KAs alias) {
        return "dAs("
            + encodeTerm(alias.pattern())
            + ", "
            + encodeTerm(alias.alias())
            + ", "
            + meta
            + ")";
      }
      if (value instanceof InjectedKLabel injected) {
        return "dInjectedLabel(" + quote(injected.klabel().name()) + ", " + meta + ")";
      }
      throw Adapter.validationError("unsupported K node in transport projection: " + value.getClass());
    }

    private static String encodeMeta(K value) {
      Att att = value.att();
      String sort = att.getOptional(Att.SORT(), Sort.class).map(Object::toString).orElse("");
      String production =
          att.getOptional(Att.PRODUCTION(), Production.class).map(Object::toString).orElse("");
      if (value instanceof KToken token) {
        sort = token.sort().toString();
      }
      return "dMeta("
          + quote(sort)
          + ", "
          + quote(production)
          + ", "
          + quote(sha256(att.toString()))
          + ")";
    }

    private static String encodeList(String empty, String cons, List<String> values) {
      String result = empty;
      for (int index = values.size() - 1; index >= 0; index--) {
        result = cons + "(" + values.get(index) + ", " + result + ")";
      }
      return result;
    }
  }

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
    final String contentSha256;
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
        String contentSha256,
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
      this.contentSha256 = contentSha256;
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
      return new Target(
          module,
          label,
          source,
          location,
          uniqueId,
          lineage(module, rule),
          Snapshot.sentenceDigest(rule),
          sha256(rule.att().toString()),
          kDigest(rule.body()),
          kDigest(rule.requires()),
          kDigest(rule.ensures()));
    }

    static String lineage(String module, Rule rule) {
      String value =
          module
              + "|"
              + rule.getClass().getName()
              + "|"
              + rule.label().orElse("")
              + "|"
              + rule.source().map(Source::source).orElse("")
              + "|"
              + rule.location().map(Object::toString).orElse("");
      return sha256(value);
    }

    static String kDigest(K value) {
      StringBuilder projection = new StringBuilder();
      Snapshot.appendK(value, "root", projection, new Counters());
      return sha256(value.toString() + "\n" + projection);
    }
  }

  private static final class TransactionRecord {
    final String mode;
    final String status;
    final Snapshot before;
    final Snapshot after;
    final Boolean sameDefinitionReference;
    final TransactionResult transaction;
    final int validatedEditCount;
    final int applicationCount;
    final int changedLineageCount;
    final boolean outputConstructed;
    final List<TransactionEditOutcome> outcomes;
    final String error;

    private TransactionRecord(
        String mode,
        String status,
        Snapshot before,
        Snapshot after,
        Boolean sameDefinitionReference,
        TransactionResult transaction,
        int validatedEditCount,
        int applicationCount,
        int changedLineageCount,
        boolean outputConstructed,
        List<TransactionEditOutcome> outcomes,
        String error) {
      this.mode = mode;
      this.status = status;
      this.before = before;
      this.after = after;
      this.sameDefinitionReference = sameDefinitionReference;
      this.transaction = transaction;
      this.validatedEditCount = validatedEditCount;
      this.applicationCount = applicationCount;
      this.changedLineageCount = changedLineageCount;
      this.outputConstructed = outputConstructed;
      this.outcomes = List.copyOf(outcomes);
      this.error = error;
    }

    static TransactionRecord accepted(
        String mode,
        Snapshot before,
        Snapshot after,
        boolean sameDefinitionReference,
        TransactionResult transaction,
        int validatedEditCount,
        int applicationCount,
        int changedLineageCount,
        boolean outputConstructed,
        List<TransactionEditOutcome> outcomes) {
      return new TransactionRecord(
          mode,
          "accepted",
          before,
          after,
          sameDefinitionReference,
          transaction,
          validatedEditCount,
          applicationCount,
          changedLineageCount,
          outputConstructed,
          outcomes,
          null);
    }

    static TransactionRecord rejected(
        String mode,
        Snapshot before,
        TransactionResult transaction,
        int validatedEditCount,
        int applicationCount,
        int changedLineageCount,
        boolean outputConstructed,
        List<TransactionEditOutcome> outcomes,
        String error) {
      return new TransactionRecord(
          mode,
          "rejected",
          before,
          null,
          null,
          transaction,
          validatedEditCount,
          applicationCount,
          changedLineageCount,
          outputConstructed,
          outcomes,
          error);
    }

    String toJson(String adapterId, String seam, String primarySource) {
      StringBuilder json = new StringBuilder();
      json.append("{\n");
      Record.field(json, 1, "schemaVersion", "1", false);
      Record.field(json, 1, "adapter", quote(adapterId), false);
      Record.field(json, 1, "seam", quote(seam), false);
      Record.field(json, 1, "mode", quote(mode), false);
      Record.field(json, 1, "status", quote(status), false);
      Record.field(
          json,
          1,
          "validationBoundary",
          quote("post-k-transaction-pre-apply"),
          false);
      Record.field(json, 1, "primarySource", quote(primarySource), false);
      if (sameDefinitionReference != null) {
        Record.field(
            json,
            1,
            "sameDefinitionReference",
            sameDefinitionReference.toString(),
            false);
      }
      Record.field(
          json,
          1,
          "transactionFingerprint",
          transaction == null ? "null" : quote(transaction.canonicalSha256()),
          false);
      Record.field(
          json,
          1,
          "transactionCardinality",
          Integer.toString(transaction == null ? 0 : transaction.transactionCount),
          false);
      Record.field(
          json,
          1,
          "editCount",
          Integer.toString(transaction == null ? 0 : transaction.editCount),
          false);
      Record.field(
          json, 1, "validatedEditCount", Integer.toString(validatedEditCount), false);
      Record.field(json, 1, "applicationCount", Integer.toString(applicationCount), false);
      Record.field(
          json, 1, "changedLineageCount", Integer.toString(changedLineageCount), false);
      Record.field(
          json, 1, "outputConstructed", Boolean.toString(outputConstructed), false);
      json.append("  \"before\": ");
      Record.appendSnapshot(json, before, 1);
      json.append(",\n");
      if (after != null) {
        json.append("  \"after\": ");
        Record.appendSnapshot(json, after, 1);
        json.append(",\n");
      }
      json.append("  \"transaction\": ");
      appendTransaction(json, transaction, 1);
      json.append(",\n");
      json.append("  \"editOutcomes\": ");
      appendOutcomes(json, outcomes, 1);
      json.append(",\n");
      Record.field(json, 1, "error", error == null ? "null" : quote(error), true);
      json.append("}\n");
      return json.toString();
    }

    private static void appendTransaction(
        StringBuilder json, TransactionResult transaction, int indent) {
      if (transaction == null) {
        json.append("null");
        return;
      }
      json.append("{\n");
      Record.field(json, indent + 1, "schema", quote(transaction.schema), false);
      Record.field(
          json,
          indent + 1,
          "transformation",
          quote(transaction.transformation),
          false);
      Record.field(
          json,
          indent + 1,
          "definitionFingerprint",
          quote(transaction.definitionFingerprint),
          false);
      Record.field(
          json,
          indent + 1,
          "transactionCount",
          Integer.toString(transaction.transactionCount),
          false);
      Record.field(
          json, indent + 1, "editCount", Integer.toString(transaction.editCount), false);
      Record.field(
          json,
          indent + 1,
          "canonicalSha256",
          quote(transaction.canonicalSha256()),
          false);
      Record.field(
          json, indent + 1, "outputSha256", quote(transaction.outputSha256), false);
      Record.indent(json, indent + 1).append("\"edits\": [");
      if (!transaction.edits.isEmpty()) {
        json.append('\n');
        for (int index = 0; index < transaction.edits.size(); index++) {
          TransactionEdit edit = transaction.edits.get(index);
          Record.indent(json, indent + 2).append("{\n");
          Record.field(json, indent + 3, "kind", quote("replaceTermFromInput"), false);
          Record.field(
              json, indent + 3, "canonical", quote(edit.canonical()), false);
          Record.field(
              json, indent + 3, "targetLineage", quote(edit.targetLineage), false);
          Record.field(
              json, indent + 3, "targetContent", quote(edit.targetContent), false);
          Record.field(
              json, indent + 3, "targetBody", quote(edit.targetBody), false);
          Record.field(
              json,
              indent + 3,
              "targetPathCanonical",
              quote(edit.targetPath.canonical()),
              false);
          Record.field(
              json,
              indent + 3,
              "replacementPathCanonical",
              quote(edit.replacementPath.canonical()),
              false);
          Record.indent(json, indent + 3).append("\"targetPath\": ");
          PatchRecord.appendPath(json, edit.targetPath, indent + 3);
          json.append(",\n");
          Record.indent(json, indent + 3).append("\"replacementPath\": ");
          PatchRecord.appendPath(json, edit.replacementPath, indent + 3);
          json.append('\n');
          Record.indent(json, indent + 2).append('}');
          json.append(index + 1 == transaction.edits.size() ? "\n" : ",\n");
        }
        Record.indent(json, indent + 1).append(']');
      } else {
        json.append(']');
      }
      json.append('\n');
      Record.indent(json, indent).append('}');
    }

    private static void appendOutcomes(
        StringBuilder json, List<TransactionEditOutcome> outcomes, int indent) {
      json.append('[');
      if (!outcomes.isEmpty()) {
        json.append('\n');
        for (int index = 0; index < outcomes.size(); index++) {
          TransactionEditOutcome outcome = outcomes.get(index);
          Record.indent(json, indent + 1).append("{\n");
          Record.indent(json, indent + 2).append("\"before\": ");
          appendRuleState(json, outcome.before, indent + 2);
          json.append(",\n");
          Record.indent(json, indent + 2).append("\"after\": ");
          appendRuleState(json, outcome.after, indent + 2);
          json.append('\n');
          Record.indent(json, indent + 1).append('}');
          json.append(index + 1 == outcomes.size() ? "\n" : ",\n");
        }
        Record.indent(json, indent).append(']');
      } else {
        json.append(']');
      }
    }

    private static void appendRuleState(StringBuilder json, RuleState state, int indent) {
      json.append("{\n");
      Record.field(json, indent + 1, "module", quote(state.module), false);
      Record.field(
          json, indent + 1, "lineageSha256", quote(state.lineageSha256), false);
      Record.field(
          json, indent + 1, "contentSha256", quote(state.contentSha256), false);
      Record.field(
          json,
          indent + 1,
          "sentenceAttSha256",
          quote(state.sentenceAttSha256),
          false);
      Record.field(json, indent + 1, "bodySha256", quote(state.bodySha256), false);
      Record.field(
          json, indent + 1, "requiresSha256", quote(state.requiresSha256), false);
      Record.field(
          json, indent + 1, "ensuresSha256", quote(state.ensuresSha256), true);
      Record.indent(json, indent).append('}');
    }
  }

  private static final class PatchRecord {
    final String mode;
    final String status;
    final Snapshot before;
    final Snapshot after;
    final Boolean sameDefinitionReference;
    final PatchResult patch;
    final int applicationCount;
    final int changedLineageCount;
    final String error;

    private PatchRecord(
        String mode,
        String status,
        Snapshot before,
        Snapshot after,
        Boolean sameDefinitionReference,
        PatchResult patch,
        int applicationCount,
        int changedLineageCount,
        String error) {
      this.mode = mode;
      this.status = status;
      this.before = before;
      this.after = after;
      this.sameDefinitionReference = sameDefinitionReference;
      this.patch = patch;
      this.applicationCount = applicationCount;
      this.changedLineageCount = changedLineageCount;
      this.error = error;
    }

    static PatchRecord accepted(
        String mode,
        Snapshot before,
        Snapshot after,
        boolean sameDefinitionReference,
        PatchResult patch,
        int applicationCount,
        int changedLineageCount) {
      return new PatchRecord(
          mode,
          "accepted",
          before,
          after,
          sameDefinitionReference,
          patch,
          applicationCount,
          changedLineageCount,
          null);
    }

    static PatchRecord rejected(
        String mode,
        Snapshot before,
        PatchResult patch,
        int applicationCount,
        String error) {
      return new PatchRecord(
          mode,
          "rejected",
          before,
          null,
          null,
          patch,
          applicationCount,
          0,
          error);
    }

    String toJson(String adapterId, String seam, String primarySource) {
      StringBuilder json = new StringBuilder();
      json.append("{\n");
      Record.field(json, 1, "schemaVersion", "1", false);
      Record.field(json, 1, "adapter", quote(adapterId), false);
      Record.field(json, 1, "seam", quote(seam), false);
      Record.field(json, 1, "mode", quote(mode), false);
      Record.field(json, 1, "status", quote(status), false);
      Record.field(
          json, 1, "validationBoundary", quote("post-k-patch-pre-apply"), false);
      Record.field(json, 1, "primarySource", quote(primarySource), false);
      if (sameDefinitionReference != null) {
        Record.field(
            json,
            1,
            "sameDefinitionReference",
            sameDefinitionReference.toString(),
            false);
      }
      Record.field(
          json,
          1,
          "patchFingerprint",
          patch == null ? "null" : quote(patch.canonicalSha256()),
          false);
      Record.field(
          json,
          1,
          "patchCardinality",
          Integer.toString(patch == null ? 0 : patch.patchCount),
          false);
      Record.field(
          json,
          1,
          "editCount",
          Integer.toString(patch == null ? 0 : patch.editCount),
          false);
      Record.field(json, 1, "applicationCount", Integer.toString(applicationCount), false);
      Record.field(
          json, 1, "changedLineageCount", Integer.toString(changedLineageCount), false);
      json.append("  \"before\": ");
      Record.appendSnapshot(json, before, 1);
      json.append(",\n");
      if (after != null) {
        json.append("  \"after\": ");
        Record.appendSnapshot(json, after, 1);
        json.append(",\n");
      }
      json.append("  \"patch\": ");
      appendPatch(json, patch, 1);
      json.append(",\n");
      Record.field(json, 1, "error", error == null ? "null" : quote(error), true);
      json.append("}\n");
      return json.toString();
    }

    private static void appendPatch(StringBuilder json, PatchResult patch, int indent) {
      if (patch == null) {
        json.append("null");
        return;
      }
      json.append("{\n");
      Record.field(json, indent + 1, "schema", quote(patch.schema), false);
      Record.field(
          json, indent + 1, "transformation", quote(patch.transformation), false);
      Record.field(
          json,
          indent + 1,
          "definitionFingerprint",
          quote(patch.definitionFingerprint),
          false);
      Record.field(
          json, indent + 1, "patchCount", Integer.toString(patch.patchCount), false);
      Record.field(
          json, indent + 1, "targetLineage", quote(patch.targetLineage), false);
      Record.field(
          json, indent + 1, "targetContent", quote(patch.targetContent), false);
      Record.field(json, indent + 1, "targetBody", quote(patch.targetBody), false);
      Record.field(
          json, indent + 1, "editCount", Integer.toString(patch.editCount), false);
      Record.field(
          json,
          indent + 1,
          "canonicalSha256",
          quote(patch.canonicalSha256()),
          false);
      Record.field(
          json, indent + 1, "outputSha256", quote(patch.outputSha256), false);
      Record.indent(json, indent + 1).append("\"edits\": [");
      if (!patch.edits.isEmpty()) {
        json.append('\n');
        for (int index = 0; index < patch.edits.size(); index++) {
          PatchEdit edit = patch.edits.get(index);
          Record.indent(json, indent + 2).append("{\n");
          Record.field(
              json,
              indent + 3,
              "kind",
              quote("replaceTermFromInput"),
              false);
          Record.field(
              json,
              indent + 3,
              "targetPathCanonical",
              quote(edit.targetPath.canonical()),
              false);
          Record.field(
              json,
              indent + 3,
              "replacementPathCanonical",
              quote(edit.replacementPath.canonical()),
              false);
          Record.indent(json, indent + 3).append("\"targetPath\": ");
          appendPath(json, edit.targetPath, indent + 3);
          json.append(",\n");
          Record.indent(json, indent + 3).append("\"replacementPath\": ");
          appendPath(json, edit.replacementPath, indent + 3);
          json.append('\n');
          Record.indent(json, indent + 2).append('}');
          json.append(index + 1 == patch.edits.size() ? "\n" : ",\n");
        }
        Record.indent(json, indent + 1).append(']');
      } else {
        json.append(']');
      }
      json.append('\n');
      Record.indent(json, indent).append('}');
    }

    private static void appendPath(StringBuilder json, TermPath path, int indent) {
      json.append('[');
      if (!path.steps.isEmpty()) {
        json.append('\n');
        for (int index = 0; index < path.steps.size(); index++) {
          PathStep step = path.steps.get(index);
          Record.indent(json, indent + 1).append("{\n");
          Record.field(
              json,
              indent + 2,
              "constructor",
              quote(step instanceof RewriteLeftStep
                  ? "dRewriteLeft"
                  : step instanceof RewriteRightStep
                      ? "dRewriteRight"
                      : step instanceof ApplicationArgumentStep
                          ? "dApplicationArgument"
                          : "dSequenceItem"),
              step instanceof RewriteLeftStep || step instanceof RewriteRightStep);
          if (step instanceof ApplicationArgumentStep argument) {
            Record.field(json, indent + 2, "index", Integer.toString(argument.index), true);
          } else if (step instanceof SequenceItemStep sequence) {
            Record.field(json, indent + 2, "index", Integer.toString(sequence.index), true);
          }
          Record.indent(json, indent + 1).append('}');
          json.append(index + 1 == path.steps.size() ? "\n" : ",\n");
        }
        Record.indent(json, indent).append(']');
      } else {
        json.append(']');
      }
    }
  }

  private static final class Record {
    final String mode;
    final String status;
    final Snapshot before;
    final Snapshot after;
    final Boolean sameDefinitionReference;
    final int selectionCount;
    final TransportResult transport;
    final String error;

    private Record(
        String mode,
        String status,
        Snapshot before,
        Snapshot after,
        Boolean sameDefinitionReference,
        int selectionCount,
        TransportResult transport,
        String error) {
      this.mode = mode;
      this.status = status;
      this.before = before;
      this.after = after;
      this.sameDefinitionReference = sameDefinitionReference;
      this.selectionCount = selectionCount;
      this.transport = transport;
      this.error = error;
    }

    static Record accepted(
        String mode,
        Snapshot before,
        Snapshot after,
        boolean sameDefinitionReference,
        int selectionCount,
        TransportResult transport) {
      return new Record(
          mode,
          "accepted",
          before,
          after,
          sameDefinitionReference,
          selectionCount,
          transport,
          null);
    }

    static Record rejected(
        String mode, Snapshot before, String error, TransportResult transport) {
      return new Record(
          mode,
          "rejected",
          before,
          null,
          null,
          transport == null ? 0 : transport.selectionCount,
          transport,
          error);
    }

    String toJson(
        String adapterId, String seam, String validationBoundary, String primarySource) {
      StringBuilder json = new StringBuilder();
      json.append("{\n");
      field(json, 1, "schemaVersion", "1", false);
      field(json, 1, "adapter", quote(adapterId), false);
      field(json, 1, "seam", quote(seam), false);
      field(json, 1, "mode", quote(mode), false);
      field(json, 1, "status", quote(status), false);
      field(json, 1, "validationBoundary", quote(validationBoundary), false);
      field(json, 1, "primarySource", quote(primarySource), false);
      if (sameDefinitionReference != null) {
        field(json, 1, "sameDefinitionReference", sameDefinitionReference.toString(), false);
      }
      field(json, 1, "selectionCount", Integer.toString(selectionCount), false);
      json.append("  \"before\": ");
      appendSnapshot(json, before, 1);
      json.append(",\n");
      if (after != null) {
        json.append("  \"after\": ");
        appendSnapshot(json, after, 1);
        json.append(",\n");
      }
      json.append("  \"transport\": ");
      appendTransport(json, transport, 1);
      json.append(",\n");
      field(json, 1, "error", error == null ? "null" : quote(error), true);
      json.append("}\n");
      return json.toString();
    }

    private static void appendTransport(
        StringBuilder json, TransportResult transport, int indent) {
      if (transport == null) {
        json.append("null");
        return;
      }
      json.append("{\n");
      field(
          json,
          indent + 1,
          "definitionFingerprint",
          quote(transport.definitionFingerprint),
          false);
      field(
          json,
          indent + 1,
          "selectionCount",
          Integer.toString(transport.selectionCount),
          false);
      field(json, indent + 1, "outputSha256", quote(transport.outputSha256), false);
      indent(json, indent + 1).append("\"selections\": [");
      if (!transport.selections.isEmpty()) {
        json.append('\n');
        for (int index = 0; index < transport.selections.size(); index++) {
          Selection selection = transport.selections.get(index);
          indent(json, indent + 2).append("{\n");
          field(
              json,
              indent + 3,
              "lineageSha256",
              quote(selection.lineageSha256),
              false);
          field(
              json,
              indent + 3,
              "contentSha256",
              quote(selection.contentSha256),
              false);
          field(
              json,
              indent + 3,
              "bodySha256",
              quote(selection.bodySha256),
              true);
          indent(json, indent + 2).append('}');
          json.append(index + 1 == transport.selections.size() ? "\n" : ",\n");
        }
        indent(json, indent + 1).append(']');
      } else {
        json.append(']');
      }
      json.append('\n');
      indent(json, indent).append('}');
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
      field(json, indent + 1, "contentSha256", quote(target.contentSha256), false);
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
