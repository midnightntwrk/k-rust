package org.kframework.kink.trace;

import static org.kframework.Collections.immutable;
import static org.kframework.Collections.stream;
import static org.kframework.definition.Constructors.Module;
import static org.kframework.definition.Constructors.Production;
import static org.kframework.kore.KORE.KApply;
import static org.kframework.kore.KORE.KList;
import static org.kframework.kore.KORE.KRewrite;
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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;
import org.kframework.attributes.Att;
import org.kframework.compile.Backend;
import org.kframework.definition.Configuration;
import org.kframework.definition.Definition;
import org.kframework.definition.DefinitionTransformer;
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
import org.kframework.kore.Sort;
import org.kframework.kore.VisitK;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Main;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.RunProcess;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.inject.JCommanderModule.Usage;
import org.kframework.utils.inject.SimpleScope;
import org.kframework.utils.options.InnerParsingOptions;
import org.kframework.utils.options.OuterParsingOptions;

/** Trusted-small post-CF host for KRuleAppliedAllowlist-v1. */
public final class RuleAppliedTraceDriver {
  private static final String MODE_ENV = "R3_G_05_MODE";
  private static final String RECORD_ENV = "R3_G_05_RECORD";
  private static final String TRACE_DEFINITION_ENV = "R3_G_05_TRACE_K_DEFINITION";
  private static final String CONFIGURATION_DEFINITION_ENV = "R3_G_05_CONFIGURATION_K_DEFINITION";
  private static final String PORTABLE_SOURCE_ENV = "R3_G_05_PORTABLE_SOURCE";
  private static final String TRACE_SCHEMA = "KRuleAppliedAllowlist-v1";
  private static final String TRACE_TRANSFORMATION = "exact-two-rule-applied-allowlist@1";
  private static final String POST_CF = "OfficialDefinitionAdapter-v1";

  private RuleAppliedTraceDriver() {}

  public static void main(String[] args) {
    if (args.length == 1 && args[0].equals("--parser-self-test")) {
      List<String> cases = TraceResultParser.selfTest();
      TraceConfigurationAugmentation.parserSelfTest();
      writeParserSelfTestRecord(cases);
      return;
    }
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

  private static void writeParserSelfTestRecord(List<String> cases) {
    String supplied = System.getenv("R3_G_05_PARSER_RECORD");
    if (supplied == null || supplied.isBlank()) {
      throw KEMException.criticalError("R3_G_05_PARSER_RECORD is required for parser self-test");
    }
    String encoded = cases.stream()
        .map(name -> "{\"backendInvocations\":0,\"name\":" + quoteJson(name)
            + ",\"outputDefinitionConstructed\":false,\"status\":\"pass\"}")
        .collect(Collectors.joining(","));
    Path path = Path.of(supplied);
    try {
      Files.createDirectories(path.getParent());
      Files.writeString(
          path,
          "{\"cases\":[" + encoded
              + "],\"schema\":\"R3-G-05-parser-canonicality-v1\"}\n",
          StandardCharsets.UTF_8);
    } catch (IOException error) {
      throw KEMException.criticalError("cannot write parser canonicality record", error);
    }
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
      String mode = required(MODE_ENV);
      Trace trace =
          new Trace(
              mode,
              Path.of(required(RECORD_ENV)).toAbsolutePath().normalize(),
              Path.of(required(TRACE_DEFINITION_ENV)).toAbsolutePath().normalize(),
              Path.of(required(CONFIGURATION_DEFINITION_ENV)).toAbsolutePath().normalize(),
              canonical(definitionFile),
              required(PORTABLE_SOURCE_ENV));
      try {
        require(definitionFile.isFile(), "definition file does not exist");
        require(Files.isRegularFile(trace.traceDefinition.resolve("mainModule.txt")), "invalid K trace definition");
        require(Files.isRegularFile(trace.configurationDefinition.resolve("mainModule.txt")), "invalid K configuration definition");
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
        Function<Definition, Definition> post = new TraceAdapter(trace)::apply;
        post = post.andThen(backend.steps());
        CompiledDefinition definition =
            kompile.run(
                definitionFile,
                options.mainModule(fileUtil),
                options.syntaxModule(fileUtil),
                trace.configuration,
                post,
                backend.excludedModuleTags());
        require(trace.configuration.metrics.hookInvocations == 1, "configuration hook invocation count was not one");
        require(trace.postCfInvocations == 1, "post-CF adapter invocation count was not one");
        fileUtil.saveToKompiled("mainModule.txt", definition.executionModule().name());
        fileUtil.saveToKompiled("mainSyntaxModule.txt", definition.mainSyntaxModuleName());
        loader.saveOrDie(fileUtil.resolveKompiled("compiled.bin"), definition);
        fileUtil.saveToKompiled("backend.txt", options.backend);
        backend.accept(new Backend.Holder(definition));
        loader.saveOrDie(fileUtil.resolveKompiled("timestamp"), "");
        trace.backendConstructed = true;
        trace.status = "accepted";
        return 0;
      } catch (RuntimeException e) {
        trace.status = "rejected";
        if (trace.error.isEmpty()) trace.error = e.toString();
        throw e;
      } finally {
        trace.write();
      }
    }
  }

  private static String productionStructure(Production production) {
    String label = production.klabel().isDefined()
        ? production.klabel().get().name() : "";
    return label + "|" + production.params() + "|" + production.sort()
        + "|" + production.items();
  }

  private static final class TraceAdapter {
    private static final Map<String, String> MALFORMED_EXISTING_FIELDS = Map.ofEntries(
        Map.entry("wrong-generated-cell-metadata", "generatedCell.metadata"),
        Map.entry("wrong-parent-production", "parent.production"),
        Map.entry("wrong-cell-production", "generatedCell.production"),
        Map.entry("wrong-left-marker-production", "leftMarker.production"),
        Map.entry("wrong-right-marker-production", "rightMarker.production"),
        Map.entry("wrong-left-marker-term", "leftMarker.term"),
        Map.entry("wrong-right-marker-term", "rightMarker.term"),
        Map.entry("wrong-append-production", "append.production"),
        Map.entry("wrong-singleton-production", "singleton.production"),
        Map.entry("wrong-event-production", "event.production"),
        Map.entry("wrong-origin-production", "origin.production"),
        Map.entry("wrong-rewrite-metadata", "rewrite.metadata"),
        Map.entry("wrong-variable-name", "variable.name"),
        Map.entry("wrong-variable-sort", "variable.sort"),
        Map.entry("wrong-variable-metadata", "variable.metadata"),
        Map.entry("wrong-token-sort", "payloadToken.sort"),
        Map.entry("wrong-token-metadata", "payloadToken.metadata"),
        Map.entry("wrong-payload-lineage", "payload.lineage"),
        Map.entry("wrong-payload-label", "payload.label"),
        Map.entry("wrong-payload-module", "payload.module"),
        Map.entry("wrong-payload-source", "payload.source"),
        Map.entry("wrong-payload-location", "payload.location"),
        Map.entry("partial-graph", "traceGraph.partial"),
        Map.entry("duplicate-graph", "traceGraph.duplicate"),
        Map.entry("extra-graph", "traceGraph.extra"));
    private final Trace trace;

    TraceAdapter(Trace trace) {
      this.trace = trace;
    }

    Definition apply(Definition input) {
      trace.postCfInvocations++;
      trace.cfConstructed = true;
      require(stream(input.modules()).flatMap(module -> stream(module.localSentences())).noneMatch(Configuration.class::isInstance), "Configuration survived CF");
      RuleDefinitionState before = RuleDefinitionState.capture(input, trace.primarySource);
      trace.ruleBeforeDefinition = before.fingerprint;
      try {
        if (trace.mode.equals("conflict-existing-first")) return conflictNegative(input, before, 0);
        if (trace.mode.equals("conflict-existing-second")) return conflictNegative(input, before, 1);
        if (trace.mode.equals("partial-existing-first")) return partialExistingNegative(input, before, 0);
        if (trace.mode.equals("partial-existing-second")) return partialExistingNegative(input, before, 1);
        if (isGenericMalformedExistingMode(trace.mode)) {
          return malformedExistingNegative(
              input, before, trace.mode.endsWith("-first") ? 0 : 1, trace.mode);
        }
        if (trace.mode.equals("false-apply-existing")) return falseApplyExistingNegative(input, before);
        if (trace.mode.equals("unsupported-shape")) return unsupportedShapeNegative(input, before);
        String kMode =
            switch (trace.mode) {
              case "positive-a", "positive-b", "missing-cell-metadata", "ambiguous-cell-metadata",
                  "missing-constructor-metadata", "ambiguous-constructor-metadata",
                  "missing-cell-metadata-first", "missing-cell-metadata-second",
                  "ambiguous-cell-metadata-first", "ambiguous-cell-metadata-second",
                  "missing-constructor-metadata-first", "missing-constructor-metadata-second",
                  "ambiguous-constructor-metadata-first", "ambiguous-constructor-metadata-second",
                  "forced-preparation-failure-first", "forced-preparation-failure-second" -> "apply";
              case "stale-first", "stale-second", "noncanonical-member-order",
                  "unsupported-path-first", "unsupported-path-second",
                  "unknown-constructor-first", "unknown-constructor-second",
                  "sort-invalid-first", "sort-invalid-second",
                  "freshness-invalid-first", "freshness-invalid-second",
                  "payload-invalid-first", "payload-invalid-second" -> trace.mode;
              case "false-already-present" -> "false-already-present";
              case "zero-target" -> "zero-target";
              case "one-target" -> "one-target";
              case "three-target" -> "three-target";
              case "duplicate-target" -> "duplicate-target";
              case "unknown-constructor" -> "unknown-constructor";
              case "sort-invalid" -> "sort-invalid";
              case "variable-collision" -> "variable-collision";
              default -> throw reject("result-envelope-validation", "unsupported trace mode");
            };
        TraceInvocation first = invokeTraceK(input, before, kMode, 1);
        TraceResult result = requireTraceResult(first, before);
        PairCall firstCall = executePairTransaction(input, before, result, 1);
        require(firstCall.status.equals("apply"), "first pair transaction did not apply");
        Definition output = firstCall.output;
        validateTraceApplied(input, output, before, result, firstCall.prepared);
        RuleDefinitionState after = RuleDefinitionState.capture(output, trace.primarySource);
        trace.ruleAfterDefinition = after.fingerprint;

        TraceInvocation second = invokeTraceK(output, after, "apply", 2);
        TraceResult already = requireTraceResult(second, after);
        require(already.status.equals("already-present"), "second trace pass did not report already-present");
        require(
            already.members.stream().map(TraceMember::lineage).toList()
                .equals(result.members.stream().map(TraceMember::lineage).toList()),
            "trace target order changed across passes");
        PairCall secondCall = executePairTransaction(output, after, already, 2);
        require(secondCall.status.equals("already-present"), "second pair transaction was not idempotent");
        capturePortableEvidence(input, output, before, after, result, already);
        trace.ruleSecondSameReference = secondCall.output == output;
        trace.ruleTransformedDefinitionReturned = firstCall.output == output;
        trace.postCfSameReference = secondCall.output == output;
        require(trace.ruleSecondSameReference, "already-present transaction changed Definition reference");
        return secondCall.output;
      } catch (ValidationException e) {
        if (trace.classification.isEmpty() && e.getMessage().contains(":")) {
          trace.classification = e.getMessage().substring(0, e.getMessage().indexOf(':'));
        }
        if (trace.error.isEmpty()) trace.error = e.getMessage();
        throw KEMException.compilerError("R3-G-05 rule trace failed: " + e.getMessage());
      }
    }

    private static boolean isGenericMalformedExistingMode(String mode) {
      return (mode.endsWith("-first") || mode.endsWith("-second"))
          && MALFORMED_EXISTING_FIELDS.containsKey(mutationBase(mode));
    }

    private static String mutationBase(String mode) {
      if (mode.endsWith("-first")) return mode.substring(0, mode.length() - "-first".length());
      if (mode.endsWith("-second")) return mode.substring(0, mode.length() - "-second".length());
      return mode;
    }

    private Definition malformedExistingNegative(
        Definition input, RuleDefinitionState before, int memberIndex, String defect) {
      TraceInvocation declaration = invokeTraceK(input, before, "apply", 1);
      TraceResult result = requireTraceResult(declaration, before);
      PreparedTrace prepared = prepareTrace(
          input, before, result.members.get(memberIndex), result.status, memberIndex);
      // Build the named task-local defect. The measured pair transaction never
      // sees an apply outcome and therefore performs zero edits/traversals.
      MalformedExistingConstruction construction = constructMalformedExistingInput(
          input, prepared, result.members.get(memberIndex), defect);
      Definition malformed = construction.definition;
      trace.ruleInputMutationCount = 1;
      RuleDefinitionState malformedState = RuleDefinitionState.capture(malformed, trace.primarySource);
      StructuredGraphDelta delta = construction.before.delta(construction.after);
      trace.mutationStructuralField = MALFORMED_EXISTING_FIELDS.get(mutationBase(defect));
      trace.mutationMemberIndex = memberIndex;
      boolean structural = trace.mutationStructuralField.startsWith("traceGraph.");
      require(
          structural
              ? construction.after.structure.equals(
                  trace.mutationStructuralField.substring("traceGraph.".length()))
              : delta.operation.equals("replace")
                  && delta.changedPaths.equals(List.of(trace.mutationStructuralField)),
          "actual structured mutation delta differs from its declared typed field/operation");
      trace.mutationProjectionSchema = ExistingGraphSnapshot.SCHEMA;
      trace.mutationStructuralOperation = delta.operation;
      trace.mutationChangedFieldPaths = String.join("|", delta.changedPaths);
      trace.mutationBeforeStructure = construction.before.structure;
      trace.mutationAfterStructure = construction.after.structure;
      trace.mutationBeforeProjectionFingerprintMap =
          construction.before.fieldFingerprintMap();
      trace.mutationAfterProjectionFingerprintMap =
          construction.after.fieldFingerprintMap();
      trace.mutationReferenceFragmentFingerprint =
          construction.before.referenceFragmentFingerprint;
      trace.mutationFieldBeforeFingerprint = sha256(delta.beforeValue);
      trace.mutationFieldAfterFingerprint = sha256(delta.afterValue);
      trace.mutationBeforeFingerprint = construction.before.graphFingerprint;
      trace.mutationAfterFingerprint = construction.after.graphFingerprint;
      trace.mutationFingerprint = sha256(delta.canonical());
      trace.mutationProductionMutatorBound = true;
      require(!trace.mutationFieldBeforeFingerprint.equals(trace.mutationFieldAfterFingerprint)
              && !trace.mutationBeforeFingerprint.equals(trace.mutationAfterFingerprint),
          "actual structured mutation did not change its field and graph fingerprints");
      TraceInvocation conflict = invokeTraceK(malformed, malformedState, "apply", 2);
      boolean kConflict = false;
      if (conflict.outcome instanceof TraceFailure failure) {
        if (!failure.reason.equals("conflicting-existing-state")) {
          throw reject("conflict", "K misclassified malformed existing graph: " + defect);
        }
        trace.mutationKConflictBeforePairTransaction = true;
        kConflict = true;
      }
      PreparedTrace malformedPrepared = new PreparedTrace(
          construction.located, prepared.parentPath, construction.malformedGraph,
          prepared.parentDescriptor, prepared.descriptor, prepared.target, prepared.markers,
          prepared.before, prepared.after, prepared.targetOperation);
      boolean hostRejected = false;
      try {
        validatePreparedAlreadyPresent(List.of(malformedPrepared));
      } catch (ValidationException hostRejection) {
        if (!hostRejection.getMessage().startsWith("host-existing-validation:")) {
          throw hostRejection;
        }
        hostRejected = true;
      }
      require(hostRejected,
          "malformed existing graph passed independent host validation: " + defect);
      trace.mutationHostIndependentRejection = true;
      require(kConflict,
          "K did not report conflict before the independent host rejection");
      throw reject("conflict", "K and host independently rejected malformed existing graph: " + defect);
    }

    private MalformedExistingConstruction constructMalformedExistingInput(
        Definition input, PreparedTrace prepared, TraceMember member, String defect) {
      Definition validDefinition = constructSingleMemberNegativeInput(
          input, prepared, prepared.before.term, prepared.after.term);
      LocatedRule validLocated = locateRule(
          validDefinition, trace.primarySource, member.lineage);
      require(validLocated != null,
          "constructed valid graph target could not be re-resolved");
      KApply validGraph = requireApplication(
          resolveOperationPath(validLocated.rule.body(), prepared.parentPath),
          "re-resolved valid existing graph");
      ExistingGraphSnapshot beforeSnapshot = ExistingGraphSnapshot.capture(
          validGraph, prepared, trace.primarySource);
      List<K> validChildren = validGraph.klist().items();
      KApply originalParent = requireApplication(validChildren.get(0), "original parent");
      KApply fragment = requireApplication(validChildren.get(1), "generated cell");
      List<K> fragmentChildren = fragment.klist().items();
      KApply left = requireApplication(fragmentChildren.get(0), "left marker");
      KRewrite rewrite = requireRewrite(fragmentChildren.get(1));
      KApply right = requireApplication(fragmentChildren.get(2), "right marker");
      K before = rewrite.left();
      K after = rewrite.right();
      Att fragmentAtt = fragment.att();
      Att parentAtt = validGraph.att();
      String mutation = mutationBase(defect);
      boolean duplicate = mutation.equals("duplicate-graph");
      boolean extra = mutation.equals("extra-graph");
      if (mutation.equals("wrong-generated-cell-metadata")) {
        fragmentAtt = replaceProductionMetadata(fragmentAtt);
      } else if (mutation.equals("wrong-parent-production")) {
        parentAtt = replaceProductionAuthority(parentAtt, prepared.descriptor.production);
      } else if (mutation.equals("wrong-cell-production")) {
        Production alternate = productionOf(originalParent, "original parent");
        fragmentAtt = replaceProductionAuthority(fragmentAtt, alternate);
      } else if (mutation.equals("wrong-left-marker-production")) {
        left = withProductionAuthority(left, prepared.descriptor.production);
      } else if (mutation.equals("wrong-right-marker-production")) {
        right = withProductionAuthority(right, prepared.descriptor.production);
      } else if (mutation.equals("wrong-left-marker-term")) {
        left = KApply(originalParent.klabel(), left.klist(), left.att());
      } else if (mutation.equals("wrong-right-marker-term")) {
        right = KApply(originalParent.klabel(), right.klist(), right.att());
      } else if (mutation.equals("wrong-append-production")) {
        after = replaceApplicationProduction(
            after, member.witness.append, productionAt(after, member.witness.singleton));
      } else if (mutation.equals("wrong-singleton-production")) {
        after = replaceApplicationProduction(
            after, member.witness.singleton, productionAt(after, member.witness.append));
      } else if (mutation.equals("wrong-event-production")) {
        after = replaceApplicationProduction(
            after, member.witness.event, productionAt(after, member.witness.origin));
      } else if (mutation.equals("wrong-origin-production")) {
        after = replaceApplicationProduction(
            after, member.witness.origin, productionAt(after, member.witness.event));
      } else if (mutation.equals("wrong-variable-name")) {
        KVariable variable = requireVariable(
            resolvePath(after, childPath(member.witness.append, 0)));
        after = replacePath(after, childPath(member.witness.append, 0),
            org.kframework.kore.KORE.KVariable(
                member.variable + "_WRONG", variable.att()));
      } else if (mutation.equals("wrong-variable-sort")) {
        K payload = resolvePath(after, member.witness.location);
        if (!(payload instanceof KToken token)) throw reject("fixture", "payload path is not a token");
        KVariable variable = requireVariable(
            resolvePath(after, childPath(member.witness.append, 0)));
        after = replacePath(after, childPath(member.witness.append, 0),
            org.kframework.kore.KORE.KVariable(
                member.variable, variable.att().add(Att.SORT(), Sort.class, token.sort())));
      } else if (mutation.equals("wrong-variable-metadata")) {
        KVariable variable = requireVariable(
            resolvePath(after, childPath(member.witness.append, 0)));
        after = replacePath(after, childPath(member.witness.append, 0),
            org.kframework.kore.KORE.KVariable(
                member.variable, wrongNonProductionMetadata(variable.att())));
      } else if (mutation.equals("wrong-token-sort")) {
        K payload = resolvePath(after, member.witness.location);
        if (!(payload instanceof KToken token)) throw reject("fixture", "payload path is not a token");
        after = replacePath(after, member.witness.location,
            KToken(token.s(), prepared.descriptor.bodySort, token.att()));
      } else if (mutation.equals("wrong-token-metadata")) {
        K payload = resolvePath(after, member.witness.location);
        if (!(payload instanceof KToken token)) throw reject("fixture", "payload path is not a token");
        after = replacePath(after, member.witness.location,
            KToken(token.s(), token.sort(), wrongNonProductionMetadata(token.att())));
      } else if (mutation.startsWith("wrong-payload-")) {
        TermPath payloadPath = switch (mutation) {
          case "wrong-payload-lineage" -> member.witness.lineage;
          case "wrong-payload-label" -> member.witness.label;
          case "wrong-payload-module" -> member.witness.module;
          case "wrong-payload-source" -> member.witness.source;
          case "wrong-payload-location" -> member.witness.location;
          default -> throw reject("fixture", "unknown payload mutation: " + mutation);
        };
        K payload = resolvePath(after, payloadPath);
        if (!(payload instanceof KToken token)) throw reject("fixture", "payload path is not a token");
        after = replacePath(after, payloadPath,
            KToken("wrong-" + mutation, token.sort(), token.att()));
      } else if (mutation.equals("partial-graph")) {
        KApply append = requireApplication(
            resolvePath(after, member.witness.append), "append term");
        after = replacePath(after, member.witness.append,
            KApply(append.klabel(), KList(append.klist().items().get(0)), append.att()));
      } else if (mutation.equals("wrong-rewrite-metadata")) {
        rewrite = KRewrite(before, after, wrongNonProductionMetadata(rewrite.att()));
      }
      if (!mutation.equals("wrong-rewrite-metadata")) {
        rewrite = KRewrite(before, after, rewrite.att());
      }
      KApply malformedFragment = KApply(
          prepared.descriptor.production.klabel().get(),
          KList(left, rewrite, right), fragmentAtt);
      List<K> children = new ArrayList<>();
      children.add(originalParent);
      children.add(malformedFragment);
      if (duplicate) children.add(malformedFragment);
      if (extra) {
        KApply append = requireApplication(
            resolvePath(prepared.after.term, member.witness.append), "append term");
        K partialAfter = replacePath(
            prepared.after.term, member.witness.append,
            KApply(append.klabel(), KList(append.klist().items().get(0)), append.att()));
        K extraFragment = KApply(
            fragment.klabel(),
            KList(prepared.markers.left, KRewrite(before, partialAfter), prepared.markers.right),
            fragment.att());
        children.add(extraFragment);
      }
      KApply malformedGraph = KApply(validGraph.klabel(), KList(children), parentAtt);
      K newBody = replaceOperationPath(
          validLocated.rule.body(), prepared.parentPath, malformedGraph);
      Rule replacement = Rule.apply(
          newBody, validLocated.rule.requires(), validLocated.rule.ensures(),
          validLocated.rule.att());
      Definition definition = replaceRule(
          validDefinition, validLocated, replacement,
          "R3-G-05 generic malformed-existing fixture");
      LocatedRule malformedLocated = locateRule(
          definition, trace.primarySource, member.lineage);
      require(malformedLocated != null,
          "constructed malformed graph target could not be re-resolved");
      K resolvedGraph = resolveOperationPath(
          malformedLocated.rule.body(), prepared.parentPath);
      KApply actualMalformedGraph = requireApplication(
          resolvedGraph, "re-resolved malformed graph");
      ExistingGraphSnapshot afterSnapshot = ExistingGraphSnapshot.capture(
          actualMalformedGraph, prepared, trace.primarySource);
      return new MalformedExistingConstruction(
          definition, malformedLocated, actualMalformedGraph, beforeSnapshot, afterSnapshot);
    }

    private static K replaceApplicationProduction(
        K root, TermPath path, Production alternate) {
      K value = resolvePath(root, path);
      if (!(value instanceof KApply application)) {
        throw reject("fixture", "production mutation path is not an application");
      }
      return replacePath(
          root, path, withProductionAuthority(application, alternate));
    }

    private static KApply withProductionAuthority(KApply application, Production alternate) {
      return KApply(
          application.klabel(), application.klist(),
          replaceProductionAuthority(application.att(), alternate));
    }

    private static Att replaceProductionAuthority(Att att, Production alternate) {
      Production original = att.getOptional(Att.PRODUCTION(), Production.class)
          .orElseThrow(() -> reject("fixture", "typed production metadata is absent"));
      Production replacement = Production(
          original.klabel(), original.params(), original.sort(), alternate.items(), original.att());
      require(!productionStructure(original).equals(productionStructure(replacement)),
          "narrow production mutation did not change production authority");
      require(original.sort().equals(replacement.sort())
              && original.att().equals(replacement.att()),
          "narrow production mutation changed sort or metadata");
      return att.add(Att.PRODUCTION(), Production.class, replacement);
    }

    private static Att replaceProductionMetadata(Att att) {
      Production original = att.getOptional(Att.PRODUCTION(), Production.class)
          .orElseThrow(() -> reject("fixture", "typed production metadata is absent"));
      Production replacement = Production(
          original.klabel(), original.params(), original.sort(), original.items(),
          wrongNonProductionMetadata(original.att()));
      require(productionStructure(original).equals(productionStructure(replacement))
              && original.sort().equals(replacement.sort()),
          "narrow metadata mutation changed production authority or sort");
      return att.add(Att.PRODUCTION(), Production.class, replacement);
    }

    private static Att wrongNonProductionMetadata(Att att) {
      return att.add(Att.unrecognizedKey("structuralMutation"), "wrong");
    }

    private static Production productionAt(K root, TermPath path) {
      return productionOf(requireApplication(resolvePath(root, path), "production path"),
          "production path");
    }

    private static Production productionOf(KApply application, String description) {
      return application.att().getOptional(Att.PRODUCTION(), Production.class)
          .orElseThrow(() -> reject("fixture", description + " production is absent"));
    }

    private static KApply requireApplication(K value, String description) {
      if (!(value instanceof KApply application)) {
        throw reject("fixture", description + " is not an application");
      }
      return application;
    }

    private static KRewrite requireRewrite(K value) {
      if (!(value instanceof KRewrite rewrite)) {
        throw reject("fixture", "generated cell middle child is not a rewrite");
      }
      return rewrite;
    }

    private static KVariable requireVariable(K value) {
      if (!(value instanceof KVariable variable)) {
        throw reject("fixture", "declared variable path is not a variable");
      }
      return variable;
    }

    private static TermPath childPath(TermPath parent, int child) {
      List<Integer> result = new ArrayList<>(parent.indices);
      result.add(child);
      return new TermPath(List.copyOf(result));
    }

    /** Execute one complete K-authored pair outcome against any supplied Definition. */
    private PairCall executePairTransaction(
        Definition input, RuleDefinitionState state, TraceResult result, int callIndex) {
      trace.pairTransactionInvocationCount++;
      int applicationsBefore = trace.ruleApplicationCount;
      int traversalsBefore = trace.ruleTransformerTraversalCount;
      int validationsBefore = trace.ruleValidatedOperationCount + trace.ruleAlreadyPresentValidatedCount;
      List<PreparedTrace> prepared = List.of();
      Definition returned;
      if (result.status.equals("apply")) {
        if (trace.mode.equals("forced-preparation-failure-first")) {
          throw reject("forced-preparation", "forced first operation preparation failure");
        }
        if (trace.mode.equals("forced-preparation-failure-second")) {
          prepareTrace(input, state, result.members.get(0), result.status, 0);
          throw reject("forced-preparation", "forced second operation preparation failure");
        }
        prepared = preparePair(input, state, result);
        trace.ruleValidatedOperationCount += 2;
        returned = applyTracePair(input, prepared);
        trace.ruleApplicationCount += 2;
      } else if (result.status.equals("already-present")) {
        prepared = preparePair(input, state, result);
        validatePreparedAlreadyPresent(prepared);
        trace.ruleAlreadyPresentValidatedCount += 2;
        returned = input;
      } else {
        throw reject("result-envelope-validation", "pair status is not homogeneous");
      }
      PairCall call = new PairCall(
          returned, result.status, List.copyOf(prepared),
          trace.ruleValidatedOperationCount + trace.ruleAlreadyPresentValidatedCount - validationsBefore,
          trace.ruleApplicationCount - applicationsBefore,
          trace.ruleTransformerTraversalCount - traversalsBefore,
          System.identityHashCode(input), System.identityHashCode(returned),
          returned == input, returned != input);
      trace.recordPairCall(callIndex, call);
      return call;
    }

    private void capturePortableEvidence(
        Definition input,
        Definition output,
        RuleDefinitionState rawBefore,
        RuleDefinitionState rawAfter,
        TraceResult rawPass1,
        TraceResult rawPass2) {
      RuleDefinitionState portableBefore =
          RuleDefinitionState.capture(input, trace.primarySource, trace.portableSource);
      RuleDefinitionState portableAfter =
          RuleDefinitionState.capture(output, trace.primarySource, trace.portableSource);
      require(
          TraceProjection.hasPortableRuleOrdering(
              input, trace.primarySource, trace.portableSource)
              && TraceProjection.hasPortableRuleOrdering(
                  output, trace.primarySource, trace.portableSource),
          "portable request rules were not ordered by portable identity");

      TraceResult portablePass1 = portableResult(
          rawPass1, rawBefore, portableBefore, trace.primarySource, trace.portableSource);
      TraceResult portablePass2 = portableResult(
          rawPass2, rawAfter, portableAfter, trace.primarySource, trace.portableSource);

      trace.portableRuleBeforeDefinition = portableBefore.fingerprint;
      trace.portableRuleAfterDefinition = portableAfter.fingerprint;
      Request portableRequest1 =
          TraceProjection.encode(
              input, portableBefore, trace.primarySource, trace.portableSource, "apply");
      Request portableRequest2 =
          TraceProjection.encode(
              output, portableAfter, trace.primarySource, trace.portableSource, "apply");
      require(
          !portableRequest1.program.contains(trace.primarySource)
              && !portableRequest2.program.contains(trace.primarySource),
          "portable request retained the raw source");
      for (String rawLineage : rawBefore.primaryRules.keySet()) {
        require(
            !portableRequest1.program.contains(rawLineage)
                && !portableRequest2.program.contains(rawLineage),
            "portable request retained a raw lineage");
      }
      trace.portableRuleRequestFingerprintPass1 = portableRequest1.fingerprint;
      trace.portableRuleRequestFingerprintPass2 = portableRequest2.fingerprint;
      trace.portableRuleOperationCanonicalPass1 = portablePass1.members.stream()
          .map(TraceMember::operationCanonical).collect(Collectors.joining("|"));
      trace.portableRuleOperationCanonicalPass2 = portablePass2.members.stream()
          .map(TraceMember::operationCanonical).collect(Collectors.joining("|"));
      trace.portableRuleResponseFingerprintPass1 =
          sha256(portablePass1.canonical());
      trace.portableRuleResponseFingerprintPass2 =
          sha256(portablePass2.canonical());
      trace.portableRuleResultCanonicalFingerprintPass1 =
          trace.portableRuleResponseFingerprintPass1;
      trace.portableRuleResultCanonicalFingerprintPass2 =
          trace.portableRuleResponseFingerprintPass2;
      trace.portableRuleTargetLineage = portablePass1.members.stream()
          .map(TraceMember::lineage).collect(Collectors.joining("|"));
      trace.portableRuleTargetModule = portablePass1.members.stream()
          .map(TraceMember::module).collect(Collectors.joining("|"));
      trace.portableRuleTargetLabel = portablePass1.members.stream()
          .map(TraceMember::label).collect(Collectors.joining("|"));
      trace.portableRuleTargetSource = portablePass1.members.stream()
          .map(TraceMember::source).collect(Collectors.joining("|"));
      trace.portableRuleTargetLocation = portablePass1.members.stream()
          .map(TraceMember::location).collect(Collectors.joining("|"));
      trace.portableRuleTargetRequires = portablePass1.members.stream()
          .map(TraceMember::requires).collect(Collectors.joining("|"));
      trace.portableRuleTargetEnsures = portablePass1.members.stream()
          .map(TraceMember::ensures).collect(Collectors.joining("|"));
      trace.portableRuleTargetAttributes = portablePass1.members.stream()
          .map(TraceMember::attributes).collect(Collectors.joining("|"));
      trace.portableRuleTargetContentBefore = portablePass1.members.stream()
          .map(TraceMember::content).collect(Collectors.joining("|"));
      trace.portableRuleTargetContentAfter = portablePass2.members.stream()
          .map(TraceMember::content).collect(Collectors.joining("|"));
      trace.portableRuleTargetBodyBefore = portablePass1.members.stream()
          .map(TraceMember::body).collect(Collectors.joining("|"));
      trace.portableRuleTargetBodyAfter = portablePass2.members.stream()
          .map(TraceMember::body).collect(Collectors.joining("|"));

      GeneratedCellDescriptor portableCell =
          portableBefore.descriptors.stream()
              .filter(
                  item ->
                      item.name.equals(trace.generatedCellName)
                          && item.label.equals(trace.generatedCellLabel))
              .findFirst()
              .orElseThrow(
                  () -> reject("portable-evidence", "portable cell projection disappeared"));
      trace.portableGeneratedCellProductionFingerprint = portableCell.productionFingerprint;
      trace.portableGeneratedCellMetadataFingerprint = portableCell.metadataFingerprint;
      trace.portableRuleOrderingValidated = true;
      trace.portableTermMetadataRederived = true;
      trace.portableEvidenceProjected = true;
    }

    private Definition conflictNegative(
        Definition input, RuleDefinitionState before, int memberIndex) {
      TraceInvocation declaration = invokeTraceK(input, before, "apply", 1);
      TraceResult result = requireTraceResult(declaration, before);
      PreparedTrace prepared = prepareTrace(
          input, before, result.members.get(memberIndex), result.status, memberIndex);
      Definition conflicting = constructSingleMemberNegativeInput(input, prepared, prepared.before.term, prepared.before.term);
      trace.ruleInputMutationCount = 1;
      RuleDefinitionState conflictState = RuleDefinitionState.capture(conflicting, trace.primarySource);
      TraceInvocation conflict = invokeTraceK(conflicting, conflictState, "apply", 2);
      if (!(conflict.outcome instanceof TraceFailure failure)
          || !failure.reason.equals("conflicting-existing-state")) {
        throw reject("conflict", "K did not reject conflicting generated cell update");
      }
      trace.ruleCandidateCountPass2 = failure.count;
      throw reject("conflict", "K rejected conflicting generated cell update");
    }

    private Definition partialExistingNegative(
        Definition input, RuleDefinitionState before, int memberIndex) {
      TraceInvocation declaration = invokeTraceK(input, before, "apply", 1);
      TraceResult result = requireTraceResult(declaration, before);
      PreparedTrace selected = prepareTrace(
          input, before, result.members.get(memberIndex), result.status, memberIndex);
      Definition partial = constructSingleMemberNegativeInput(
          input, selected, selected.before.term, selected.after.term);
      trace.ruleInputMutationCount = 1;
      RuleDefinitionState partialState = RuleDefinitionState.capture(partial, trace.primarySource);
      TraceInvocation mixed = invokeTraceK(partial, partialState, "apply", 2);
      if (!(mixed.outcome instanceof TraceFailure failure)
          || !failure.reason.equals("mixed-status")) {
        throw reject("partial-instrumentation", "K did not reject one-present/one-absent state");
      }
      trace.ruleCandidateCountPass2 = failure.count;
      throw reject("partial-instrumentation", "K rejected one-present/one-absent state");
    }

    private Definition falseApplyExistingNegative(Definition input, RuleDefinitionState before) {
      TraceResult declaration = requireTraceResult(invokeTraceK(input, before, "apply", 1), before);
      List<PreparedTrace> prepared = preparePair(input, before, declaration);
      Definition existing = applyTracePairFixture(input, prepared);
      trace.ruleInputMutationCount = 2;
      RuleDefinitionState existingState = RuleDefinitionState.capture(existing, trace.primarySource);
      TraceResult falseApply = requireTraceResult(
          invokeTraceK(existing, existingState, "false-apply", 2), existingState);
      preparePair(existing, existingState, falseApply);
      throw reject("false-status", "false apply status unexpectedly prepared");
    }

    private Definition unsupportedShapeNegative(
        Definition input, RuleDefinitionState before) {
      TraceInvocation declaration = invokeTraceK(input, before, "apply", 1);
      TraceResult result = requireTraceResult(declaration, before);
      TraceMember member = result.members.get(0);
      LocatedRule located = locateRule(input, trace.primarySource, member.lineage);
      if (located == null) throw reject("stale-precondition", "declared rule disappeared");
      K declaredParent;
      try {
        declaredParent = resolveOperationPath(located.rule.body(), member.parentPath);
      } catch (ValidationException e) {
        throw reject("path-operation", e.getMessage());
      }
      if (!(declaredParent instanceof KApply parent)
          || !parent.klabel().name().equals("#cells")) {
        throw reject("path-operation", "declared original parent was not a cell bag");
      }
      K unsupported =
          org.kframework.kore.KORE.KSequence(parent.klist().items(), parent.att());
      K newBody = replaceOperationPath(located.rule.body(), member.parentPath, unsupported);
      Definition mutated = replaceRuleBody(input, located, newBody, "R3-G-05 unsupported-shape input mutation");
      trace.ruleInputMutationCount = 1;
      RuleDefinitionState mutatedState = RuleDefinitionState.capture(mutated, trace.primarySource);
      TraceInvocation selected = invokeTraceK(mutated, mutatedState, "apply", 2);
      requireTraceResult(selected, mutatedState);
      throw reject("conservative-shape-rejection", "unsupported rule body unexpectedly prepared");
    }

    private TraceInvocation invokeTraceK(
        Definition definition, RuleDefinitionState state, String mode, int pass) {
      Request request = TraceProjection.encode(definition, state, trace.primarySource, mode);
      String output = runK(request.program, trace.traceDefinition, trace.recordPath);
      TraceOutcome outcome = TraceResultParser.parse(output);
      trace.currentTraceResult = outcome;
      String responseFingerprint = sha256(outcome.canonical());
      if (pass == 1) {
        trace.ruleRequestFingerprintPass1 = request.fingerprint;
        trace.ruleResponseFingerprintPass1 = responseFingerprint;
        trace.ruleKInvocationsPass1++;
        trace.ruleStatusPass1 = outcome.status();
        trace.ruleCandidateCountPass1 = outcome.count();
      } else {
        trace.ruleRequestFingerprintPass2 = request.fingerprint;
        trace.ruleResponseFingerprintPass2 = responseFingerprint;
        trace.ruleKInvocationsPass2++;
        trace.ruleStatusPass2 = outcome.status();
        trace.ruleCandidateCountPass2 = outcome.count();
      }
      return new TraceInvocation(request, outcome);
    }

    private TraceResult requireTraceResult(
      TraceInvocation invocation, RuleDefinitionState state) {
      if (invocation.outcome instanceof TraceFailure failure) {
        if (!failure.schema.equals(TRACE_SCHEMA)
            || failure.count < 0
            || (!failure.reason.equals("structural-target-cardinality")
                && !failure.reason.equals("conflicting-existing-state")
                && !failure.reason.equals("duplicate-target-lineage")
                && !failure.reason.equals("mixed-status"))) {
          throw reject("envelope", "invalid K trace failure envelope");
        }
        String classification =
            failure.reason.equals("structural-target-cardinality")
                ? "k-selection"
                : failure.reason.equals("conflicting-existing-state") ? "conflict" : failure.reason;
        throw reject(classification, "K trace selection failed: " + failure.reason + " count=" + failure.count);
      }
      TraceResult result = (TraceResult) invocation.outcome;
      if (!result.schema.equals(TRACE_SCHEMA)
          || !result.transformation.equals(TRACE_TRANSFORMATION)
          || result.candidateCount != 2
          || result.members.size() != 2
          || (!result.status.equals("apply") && !result.status.equals("already-present"))) {
        throw reject("envelope", "invalid K trace result envelope");
      }
      ResultIdentity identity = result.identity;
      if (!identity.schema.equals(result.schema)
          || !identity.transformation.equals(result.transformation)
          || !identity.definitionFingerprint.equals(result.definitionFingerprint)
          || identity.candidateCount != result.candidateCount
          || !identity.status.equals(result.status)
          || !identity.first.canonical().equals(result.members.get(0).canonical())
          || !identity.second.canonical().equals(result.members.get(1).canonical())) {
        throw reject("result-identity", "K-authored canonical result identity does not bind the pair");
      }
      if (!result.definitionFingerprint.equals(state.fingerprint)) {
        throw reject("stale-precondition", "stale post-CF definition fingerprint");
      }
      List<String> lineages = result.members.stream().map(TraceMember::lineage).toList();
      if (!lineages.equals(lineages.stream().sorted().toList())
          || lineages.get(0).equals(lineages.get(1))) {
        throw reject("canonical-order", "K member order was duplicate or noncanonical");
      }
      for (TraceMember member : result.members) {
        RuleState target = state.primaryRules.get(member.lineage);
        if (target == null
            || !target.content.equals(member.content)
            || !target.body.equals(member.body)
            || !target.requires.equals(member.requires)
            || !target.ensures.equals(member.ensures)
            || !target.attributes.equals(member.attributes)) {
          throw reject("stale-precondition", "stale trace target precondition");
        }
        if (!target.module.equals(member.module)
            || !target.label.equals(member.label)
            || !target.source.equals(member.source)
            || !target.location.equals(member.location)) {
          throw reject("stale-precondition", "stale trace target provenance");
        }
      }
      trace.ruleTargetLineage = String.join("|", lineages);
      trace.ruleTargetModule = result.members.stream().map(TraceMember::module).collect(Collectors.joining("|"));
      trace.ruleTargetLabel = result.members.stream().map(TraceMember::label).collect(Collectors.joining("|"));
      trace.ruleTargetSource = result.members.stream().map(TraceMember::source).collect(Collectors.joining("|"));
      trace.ruleTargetLocation = result.members.stream().map(TraceMember::location).collect(Collectors.joining("|"));
      trace.ruleTargetRequires = result.members.stream().map(TraceMember::requires).collect(Collectors.joining("|"));
      trace.ruleTargetEnsures = result.members.stream().map(TraceMember::ensures).collect(Collectors.joining("|"));
      trace.ruleTargetAttributes = result.members.stream().map(TraceMember::attributes).collect(Collectors.joining("|"));
      if (trace.ruleTargetContentBefore.isEmpty()) {
        trace.ruleTargetContentBefore = result.members.stream().map(TraceMember::content).collect(Collectors.joining("|"));
        trace.ruleTargetBodyBefore = result.members.stream().map(TraceMember::body).collect(Collectors.joining("|"));
        trace.ruleOperationCanonicalPass1 = result.members.stream().map(TraceMember::operationCanonical).collect(Collectors.joining("|"));
        trace.ruleResultCanonicalFingerprintPass1 = sha256(result.identity.canonical());
      } else {
        trace.ruleOperationCanonicalPass2 = result.members.stream().map(TraceMember::operationCanonical).collect(Collectors.joining("|"));
        trace.ruleResultCanonicalFingerprintPass2 = sha256(result.identity.canonical());
      }
      return result;
    }

    private PreparedTrace prepareTrace(
        Definition definition, RuleDefinitionState state, TraceMember result,
        String status, int memberIndex) {
      LocatedRule located = locateRule(definition, trace.primarySource, result.lineage);
      RuleState target = state.primaryRules.get(result.lineage);
      if (located == null || target == null) throw reject("stale-precondition", "trace target disappeared");
      if (result.parentPath.indices.isEmpty()) {
        throw reject("path-operation", "K-declared insertion path must be non-root");
      }
      K parent;
      try {
        parent = resolveOperationPath(located.rule.body(), result.parentPath);
      } catch (ValidationException e) {
        throw reject("path-operation", e.getMessage());
      }
      if (!(parent instanceof KApply parentApply)) {
        String classification = trace.mode.equals("unsupported-shape") ? "conservative-shape-rejection" : "path-operation";
        throw reject(classification, "declared insertion point is not an application");
      }
      ProductionDescriptor declaredParent = resolveProduction(result.authority.parentProduction, state, state.productions);
      if (!parentApply.klabel().equals(declaredParent.production.klabel().get())
          || parentApply.att().getOptional(Att.PRODUCTION(), Production.class)
              .filter(value -> value.equals(declaredParent.production)).isEmpty()) {
        throw reject("path-operation", "resolved parent does not equal the K-declared typed production");
      }
      List<GeneratedCellDescriptor> descriptors =
          state.descriptors.stream().filter(item -> item.matches(result.authority.generatedCell))
              .collect(Collectors.toCollection(ArrayList::new));
      if (affectsMember(trace.mode, "missing-cell-metadata", memberIndex)) {
        descriptors.clear();
        trace.ruleInputMutationCount++;
      } else if (affectsMember(trace.mode, "ambiguous-cell-metadata", memberIndex)
          && descriptors.size() == 1) {
        descriptors.add(descriptors.get(0));
        trace.ruleInputMutationCount++;
      }
      if (descriptors.size() != 1) {
        throw reject("generated-metadata", "declared generated cell metadata count was " + descriptors.size());
      }
      GeneratedCellDescriptor descriptor = descriptors.get(0);
      if (!result.name.equals(descriptor.name)
          || !result.variableSort.equals(result.authority.generatedCell.bodySort)) {
        throw reject("generated-metadata", "operation fields disagree with the complete cell descriptor");
      }
      ProductionDescriptor declaredCell = resolveProduction(
          result.authority.cellProduction, state, state.productions);
      if (declaredCell.production != descriptor.production) {
        throw reject("generated-metadata", "K-declared cell production does not equal generated metadata");
      }
      if (descriptor.production.arity() != 1 || descriptor.bodySort.toString().isBlank()) {
        throw reject("generated-metadata", "declared generated cell metadata is not a supported leaf");
      }
      SortDescriptor variableSort = resolveSort(result.variableSort, state);
      if (!descriptor.bodySortDescriptor.equals(variableSort)) {
        throw reject("term-sort", "declared trace variable sort differs from cell body sort");
      }
      if (!(result.beforeTerm instanceof VariableSpec beforeVariable)
          || !beforeVariable.name.equals(result.variable)
          || !beforeVariable.sort.equals(result.variableSort)) {
        throw reject("term-sort", "before term is not the declared trace variable");
      }
      validateExpectedGraphAuthority(result, state);
      java.util.Set<String> existingVariables = new java.util.HashSet<>();
      collectVariables(located.rule.body(), existingVariables);
      collectVariables(located.rule.requires(), existingVariables);
      collectVariables(located.rule.ensures(), existingVariables);
      if (status.equals("apply") && existingVariables.contains(result.variable)) {
        throw reject("fresh-variable", "declared trace variable collides with target rule");
      }
      List<ProductionDescriptor> productions = new ArrayList<>(state.productions);
      ProductionSpec rootProduction =
          result.afterTerm instanceof ApplySpec root ? root.production : null;
      if (affectsMember(trace.mode, "missing-constructor-metadata", memberIndex)
          && rootProduction != null) {
        productions.removeIf(item -> item.matches(rootProduction));
        trace.ruleInputMutationCount++;
      } else if (affectsMember(trace.mode, "ambiguous-constructor-metadata", memberIndex)
          && rootProduction != null) {
        productions.stream().filter(item -> item.matches(rootProduction)).findFirst().ifPresent(productions::add);
        trace.ruleInputMutationCount++;
      }
      BuiltTerm before = buildTerm(result.beforeTerm, state, productions);
      BuiltTerm after = buildTerm(result.afterTerm, state, productions);
      if (!before.sort.equals(descriptor.bodySortDescriptor)
          || !after.sort.equals(descriptor.bodySortDescriptor)) {
        throw reject("term-sort", "declared trace update does not have the cell body sort");
      }
      validateAppendAndPayload(result, target);
      int named = countNamedGeneratedUpdates(parentApply, descriptor);
      if (status.equals("apply") && named != 0) {
        throw reject("path-operation", "declared generated cell update already exists");
      }
      trace.generatedCellName = descriptor.name;
      trace.generatedCellLabel = descriptor.label;
      trace.generatedCellSort = descriptor.cellSort.toString();
      trace.generatedCellBodySort = descriptor.bodySort.toString();
      trace.generatedCellProductionFingerprint = descriptor.productionFingerprint;
      trace.generatedCellMetadataFingerprint = descriptor.metadataFingerprint;
      ProductionDescriptor leftMarkerProduction = resolveProduction(
          result.authority.leftMarkerProduction, state, state.productions);
      ProductionDescriptor rightMarkerProduction = resolveProduction(
          result.authority.rightMarkerProduction, state, state.productions);
      BuiltTerm leftMarker = buildTerm(result.authority.leftMarkerTerm, state, state.productions);
      BuiltTerm rightMarker = buildTerm(result.authority.rightMarkerTerm, state, state.productions);
      if (!(leftMarker.term instanceof KApply left) || !(rightMarker.term instanceof KApply right)
          || !left.klist().items().isEmpty() || !right.klist().items().isEmpty()
          || !left.klabel().equals(leftMarkerProduction.production.klabel().get())
          || !right.klabel().equals(rightMarkerProduction.production.klabel().get())) {
        throw reject("generated-metadata", "K-declared marker terms do not exactly resolve");
      }
      MarkerEnvelope markers = new MarkerEnvelope(left, right);
      return new PreparedTrace(
          located, result.parentPath, parentApply, declaredParent, descriptor, target, markers,
          before, after, result);
    }

    private static void validateExpectedGraphAuthority(
        TraceMember result, RuleDefinitionState state) {
      OperationAuthority authority = result.authority;
      require(
          authority.termMetadata.equals(TraceProjection.termMetadataAuthority(state)),
          "K-authored non-production metadata authority disagrees with the independent convention");
      require(
          authority.termMetadata.variableSort.equals(result.variableSort)
              && authority.termMetadata.variable.sort.equals(result.variableSort),
          "variable metadata authority is not bound to the operation sort");
      TermSpec append = resolveSpecPath(result.afterTerm, result.witness.append);
      TermSpec singleton = resolveSpecPath(result.afterTerm, result.witness.singleton);
      TermSpec event = resolveSpecPath(result.afterTerm, result.witness.event);
      TermSpec origin = resolveSpecPath(result.afterTerm, result.witness.origin);
      require(append instanceof ApplySpec application
              && application.production.equals(authority.appendProduction),
          "append production differs from exact operation authority");
      require(singleton instanceof ApplySpec application
              && application.production.equals(authority.singletonProduction),
          "singleton production differs from exact operation authority");
      require(event instanceof ApplySpec application
              && application.production.equals(authority.eventProduction),
          "event production differs from exact operation authority");
      require(origin instanceof ApplySpec application
              && application.production.equals(authority.originProduction),
          "origin production differs from exact operation authority");
      for (TermPath path : List.of(
          result.witness.lineage, result.witness.label, result.witness.module,
          result.witness.source, result.witness.location)) {
        TermSpec field = resolveSpecPath(result.afterTerm, path);
        require(field instanceof TokenSpec token
                && token.sort.equals(authority.termMetadata.tokenSort)
                && authority.termMetadata.token.sort.equals(token.sort),
            "payload token sort/metadata differs from exact operation authority");
      }
      for (ProductionSpec production : List.of(
          authority.appendProduction, authority.singletonProduction,
          authority.eventProduction, authority.originProduction)) {
        resolveProduction(production, state, state.productions);
      }
    }

    private List<PreparedTrace> preparePair(
        Definition definition, RuleDefinitionState state, TraceResult result) {
      List<PreparedTrace> prepared = new ArrayList<>();
      for (int index = 0; index < result.members.size(); index++) {
        prepared.add(prepareTrace(
            definition, state, result.members.get(index), result.status, index));
      }
      require(
          prepared.get(0).located.rule != prepared.get(1).located.rule,
          "duplicate or overlapping prepared targets");
      return List.copyOf(prepared);
    }

    private static boolean affectsMember(String mode, String base, int index) {
      return mode.equals(base)
          || mode.equals(base + (index == 0 ? "-first" : "-second"));
    }

    private void validateTraceAlreadyPresent(
        Definition definition, RuleDefinitionState state, TraceResult result) {
      List<PreparedTrace> prepared = preparePair(definition, state, result);
      validatePreparedAlreadyPresent(prepared);
      trace.ruleAlreadyPresentValidatedCount += 2;
    }

    private static void validatePreparedAlreadyPresent(List<PreparedTrace> prepared) {
      for (PreparedTrace item : prepared) {
        K resolved = resolveOperationPath(item.located.rule.body(), item.parentPath);
        hostRequire(resolved == item.parent,
            "existing graph was not re-resolved from the supplied Definition path");
        validateOperationRootHostAuthority(item);
        List<K> parentChildren = item.parent.klist().items();
        hostRequire(parentChildren.size() == 2 && parentChildren.get(0) instanceof KApply,
            "existing graph does not have exact original-parent/trace placement");
        KApply originalParent = (KApply) parentChildren.get(0);
        Att expectedParentAtt = exactParentAtt(item.parentDescriptor);
        hostRequire(originalParent.klabel().equals(
                item.parentDescriptor.production.klabel().get())
                && originalParent.att().toString().equals(expectedParentAtt.toString())
                && item.parent.klabel().equals(
                    item.parentDescriptor.production.klabel().get())
                && item.parent.att().toString().equals(expectedParentAtt.toString()),
            "both parent layers do not equal independently declared production authority");
        KApply expected = exactExistingParent(item, originalParent, expectedParentAtt);
        ExistingGraphSnapshot actualSnapshot = ExistingGraphSnapshot.capture(
            item.parent, item, item.target.source);
        ExistingGraphSnapshot expectedSnapshot = ExistingGraphSnapshot.capture(
            expected, item, item.target.source);
        hostRequire(actualSnapshot.structure.equals("exact")
                && actualSnapshot.graphFingerprint.equals(expectedSnapshot.graphFingerprint)
                && item.parent.equals(expected),
            "existing graph differs from independently constructed exact host authority");
        int named = countNamedGeneratedUpdates(item.parent, item.descriptor);
        int exact = countExactGeneratedUpdates(
            item.parent, item.descriptor, item.markers, item.before.term, item.after.term);
        if (named != 1 || exact != 1) {
          throw reject("host-existing-validation",
              "already-present claim failed independent host validation");
        }
      }
    }

    private static void validateOperationRootHostAuthority(PreparedTrace item) {
      MetaSpec root = item.targetOperation.authority.termMetadata.operationRoot;
      hostRequire(root.sort.name.equals("OperationRoot")
              && root.sort.fingerprint.equals(sha256("OperationRoot"))
              && root.productionFingerprint.equals(
                  sha256("R3-G-05-operation-root-production"))
              && root.metadataFingerprint.equals(
                  sha256("R3-G-05-operation-root-metadata")),
          "operation-root metadata differs from independent host authority");
      String encoded = Projection.encodeOperationRoot(
          item.located.rule.body(), item.target.source, item.target.source, Map.of());
      hostRequire(encoded.startsWith("cApply(\"#operationRoot\","),
          "operation-root child placement is not exact");
    }

    private static void hostRequire(boolean condition, String message) {
      if (!condition) throw reject("host-existing-validation", message);
    }

    private static Rule replacementFor(PreparedTrace prepared, K before, K after) {
      require(before.equals(prepared.before.term) && after.equals(prepared.after.term),
          "replacement terms differ from the prepared K-authored operation");
      K appended = exactExistingParent(prepared, prepared.parent);
      K newBody = replaceOperationPath(
          prepared.located.rule.body(), prepared.parentPath, appended);
      return Rule.apply(
          newBody, prepared.located.rule.requires(), prepared.located.rule.ensures(),
          prepared.located.rule.att());
    }

    private static KApply exactGeneratedFragment(PreparedTrace prepared) {
      Att fragmentAtt = Att.empty()
          .add(Att.PRODUCTION(), Production.class, prepared.descriptor.production)
          .add(Att.SORT(), Sort.class, prepared.descriptor.cellSort);
      return KApply(
          prepared.descriptor.production.klabel().get(),
          KList(
              prepared.markers.left,
              KRewrite(prepared.before.term, prepared.after.term),
              prepared.markers.right),
          fragmentAtt);
    }

    private static KApply exactExistingParent(
        PreparedTrace prepared, KApply originalParent) {
      return exactExistingParent(prepared, originalParent, originalParent.att());
    }

    private static KApply exactExistingParent(
        PreparedTrace prepared, KApply originalParent, Att parentAtt) {
      return KApply(
          originalParent.klabel(),
          KList(originalParent, exactGeneratedFragment(prepared)),
          parentAtt);
    }

    private static Att exactParentAtt(ProductionDescriptor descriptor) {
      return Att.empty()
          .add(Att.PRODUCTION(), Production.class, descriptor.production)
          .add(Att.SORT(), Sort.class, descriptor.production.sort());
    }

    private Definition applyTracePair(Definition input, List<PreparedTrace> prepared) {
      trace.ruleTransformerTraversalCount++;
      return transformPair(input, prepared);
    }

    /** Test-input construction is outside the measured pair transaction. */
    private Definition applyTracePairFixture(Definition input, List<PreparedTrace> prepared) {
      return transformPair(input, prepared);
    }

    private static Definition transformPair(Definition input, List<PreparedTrace> prepared) {
      Map<Rule, Rule> replacements = new java.util.IdentityHashMap<>();
      for (PreparedTrace item : prepared) {
        replacements.put(item.located.rule, replacementFor(item, item.before.term, item.after.term));
      }
      require(replacements.size() == 2, "atomic replacement set was not exactly two");
      DefinitionTransformer transformer = DefinitionTransformer.from(
          module -> {
            java.util.Set<Sentence> sentences = stream(module.localSentences())
                .map(sentence -> sentence instanceof Rule rule && replacements.containsKey(rule)
                    ? replacements.get(rule) : sentence)
                .collect(Collectors.toSet());
            return Module(module.name(), module.imports(), immutable(sentences), module.att());
          },
          "R3-G-05 atomic exact-two K-authored generated-cell rule updates");
      return transformer.apply(input);
    }

    private Definition constructSingleMemberNegativeInput(
        Definition input,
        PreparedTrace prepared,
        K before,
        K after) {
      Rule replacement = replacementFor(prepared, before, after);
      return replaceRule(
          input, prepared.located, replacement,
          "R3-G-05 test-only single-member input mutation");
    }

    private static void collectVariables(K root, java.util.Set<String> result) {
      new VisitK() {
        @Override public void apply(KVariable variable) { result.add(variable.name()); }
      }.apply(root);
    }

    private static void validateAppendAndPayload(TraceMember result, RuleState target) {
      TermSpec appendTerm = resolveSpecPath(result.afterTerm, result.witness.append);
      TermSpec singletonTerm = resolveSpecPath(result.afterTerm, result.witness.singleton);
      TermSpec eventTerm = resolveSpecPath(result.afterTerm, result.witness.event);
      TermSpec originTerm = resolveSpecPath(result.afterTerm, result.witness.origin);
      if (appendTerm != result.afterTerm
          || !(appendTerm instanceof ApplySpec append)
          || append.arguments.size() != 2
          || !append.arguments.get(0).canonical().equals(result.beforeTerm.canonical())
          || append.arguments.get(1) != singletonTerm) {
        throw reject("term-shape", "after term is not a binary append rooted at the before term");
      }
      if (!(singletonTerm instanceof ApplySpec singleton)
          || singleton.arguments.size() != 1
          || singleton.arguments.get(0) != eventTerm
          || !(eventTerm instanceof ApplySpec event)
          || event.arguments.size() != 1
          || event.arguments.get(0) != originTerm
          || !(originTerm instanceof ApplySpec origin)
          || origin.arguments.size() != 5) {
        throw reject("term-shape", "declared witness does not identify one singleton event/origin graph");
      }
      Map<TermPath, String> payload = new LinkedHashMap<>();
      payload.put(result.witness.lineage, target.lineage);
      payload.put(result.witness.label, target.label);
      payload.put(result.witness.module, target.module);
      payload.put(result.witness.source, target.source);
      payload.put(result.witness.location, target.location);
      if (payload.size() != 5) throw reject("payload-provenance", "payload witness paths are not unique");
      java.util.Set<String> declaredPaths =
          payload.keySet().stream().map(TermPath::canonical).collect(Collectors.toSet());
      java.util.Set<String> originChildren = new java.util.HashSet<>();
      for (int index = 0; index < 5; index++) {
        List<Integer> indices = new ArrayList<>(result.witness.origin.indices);
        indices.add(index);
        originChildren.add(new TermPath(List.copyOf(indices)).canonical());
      }
      if (!declaredPaths.equals(originChildren)) {
        throw reject("payload-provenance", "payload witnesses do not cover exactly the origin arguments");
      }
      for (var entry : payload.entrySet()) {
        TermSpec field = resolveSpecPath(result.afterTerm, entry.getKey());
        if (!(field instanceof TokenSpec token)
            || !token.value.equals(entry.getValue())
            || !StringUtil.unquoteKString(token.lexeme).equals(token.value)) {
          throw reject("payload-provenance", "event payload does not equal selected rule provenance");
        }
      }
      if (countVariables(result.afterTerm, result.variable) != 1) {
        throw reject("term-shape", "after term does not contain the fresh trace variable exactly once");
      }
    }

    private static TermSpec resolveSpecPath(TermSpec root, TermPath path) {
      TermSpec current = root;
      for (int index : path.indices) {
        if (!(current instanceof ApplySpec application)) {
          throw reject("term-shape", "typed-term path reached a non-application");
        }
        if (index < 0 || index >= application.arguments.size()) {
          throw reject("term-shape", "typed-term path index is out of bounds");
        }
        current = application.arguments.get(index);
      }
      return current;
    }

    private static int countVariables(TermSpec term, String name) {
      if (term instanceof VariableSpec variable) return variable.name.equals(name) ? 1 : 0;
      if (term instanceof ApplySpec application) {
        int count = 0; for (TermSpec child : application.arguments) count += countVariables(child, name); return count;
      }
      return 0;
    }

    private static SortDescriptor resolveSort(SortSpec spec, RuleDefinitionState state) {
      List<SortDescriptor> matches =
          state.sorts.stream().filter(item -> item.matches(spec)).collect(Collectors.toCollection(ArrayList::new));
      if (matches.size() != 1) throw reject("term-sort", "declared sort metadata count was " + matches.size());
      return matches.get(0);
    }

    private static BuiltTerm buildTerm(
        TermSpec spec, RuleDefinitionState state, List<ProductionDescriptor> productions) {
      if (spec instanceof VariableSpec variable) {
        require(!variable.name.isBlank(), "blank typed variable field");
        SortDescriptor sort = resolveSort(variable.sort, state);
        return new BuiltTerm(
            org.kframework.kore.KORE.KVariable(
                variable.name, Att.empty().add(Att.SORT(), Sort.class, sort.sort)),
            sort);
      }
      if (spec instanceof TokenSpec token) {
        SortDescriptor sort = resolveSort(token.sort, state);
        try {
          require(StringUtil.unquoteKString(token.lexeme).equals(token.value), "noncanonical semantic token lexeme");
        } catch (IllegalArgumentException e) {
          throw reject("term-token", "invalid semantic token lexeme");
        }
        return new BuiltTerm(KToken(token.value, sort.sort), sort);
      }
      ApplySpec application = (ApplySpec) spec;
      ProductionDescriptor descriptor = resolveProduction(
          application.production, state, productions);
      if (descriptor.argumentSorts.size() != application.arguments.size()) {
        throw reject("term-sort", "declared constructor arity mismatch");
      }
      List<K> children = new ArrayList<>();
      for (int index = 0; index < application.arguments.size(); index++) {
        BuiltTerm child = buildTerm(application.arguments.get(index), state, productions);
        if (!state.isSubsort(child.sort, descriptor.argumentSorts.get(index))) {
          throw reject(
              "term-sort",
              "declared constructor argument sort mismatch: "
                  + child.sort.name + " is not " + descriptor.argumentSorts.get(index).name
                  + " at " + descriptor.label + "[" + index + "]; relations="
                  + state.subsorts.stream()
                      .filter(item -> item.sub.name.equals(child.sort.name))
                      .map(item -> item.sub.name + "<" + item.sup.name)
                      .collect(Collectors.joining(",")));
        }
        children.add(child.term);
      }
      Att att = Att.empty().add(Att.PRODUCTION(), Production.class, descriptor.production)
          .add(Att.SORT(), Sort.class, descriptor.production.sort());
      return new BuiltTerm(KApply(descriptor.production.klabel().get(), KList(children), att), descriptor.resultSort);
    }

    private static ProductionDescriptor resolveProduction(
        ProductionSpec spec,
        RuleDefinitionState state,
        List<ProductionDescriptor> productions) {
      List<ProductionDescriptor> matches = productions.stream()
          .filter(item -> item.matches(spec))
          .collect(Collectors.toCollection(ArrayList::new));
      if (matches.size() != 1) {
        throw reject("constructor-metadata", "declared constructor metadata count was " + matches.size());
      }
      return matches.get(0);
    }

    private static Definition replaceRuleBody(
        Definition input, LocatedRule located, K newBody, String description) {
      Rule replacement =
          Rule.apply(newBody, located.rule.requires(), located.rule.ensures(), located.rule.att());
      return replaceRule(input, located, replacement, description);
    }

    private static Definition replaceRule(
        Definition input, LocatedRule located, Rule replacement, String description) {
      DefinitionTransformer transformer =
          DefinitionTransformer.from(
              module -> {
                if (!module.name().equals(located.module.name())) return module;
                java.util.Set<Sentence> sentences =
                    stream(module.localSentences())
                        .map(sentence -> sentence == located.rule ? replacement : sentence)
                        .collect(Collectors.toSet());
                return Module(module.name(), module.imports(), immutable(sentences), module.att());
              },
              description);
      return transformer.apply(input);
    }

    private void validateTraceApplied(
        Definition input,
        Definition output,
        RuleDefinitionState before,
        TraceResult result,
        List<PreparedTrace> prepared) {
      RuleDefinitionState after = RuleDefinitionState.capture(output, trace.primarySource);
      require(input != output, "rule trace returned original Definition reference");
      require(before.moduleCount == after.moduleCount, "rule trace changed module cardinality");
      require(before.sentenceCount == after.sentenceCount, "rule trace changed sentence cardinality");
      require(before.nonPrimaryFingerprint.equals(after.nonPrimaryFingerprint), "non-primary-source sentences changed");
      require(before.primaryRules.keySet().equals(after.primaryRules.keySet()), "primary-source rule lineage changed");
      require(!before.fingerprint.equals(after.fingerprint), "post-CF definition fingerprint did not change");
      List<RuleState> targetAfter = new ArrayList<>();
      for (int index = 0; index < prepared.size(); index++) {
        PreparedTrace item = prepared.get(index);
        TraceMember member = result.members.get(index);
        RuleState changed = after.primaryRules.get(member.lineage);
        require(changed != null, "instrumented rule lineage disappeared");
        require(!item.target.content.equals(changed.content), "instrumented rule content did not change");
        require(!item.target.body.equals(changed.body), "instrumented rule body did not change");
        require(item.target.requires.equals(changed.requires), "instrumented rule requires changed");
        require(item.target.ensures.equals(changed.ensures), "instrumented rule ensures changed");
        require(item.target.attributes.equals(changed.attributes), "instrumented rule attributes changed");
        LocatedRule locatedAfter = locateRule(output, trace.primarySource, member.lineage);
        require(
            locatedAfter != null && containsIdentity(locatedAfter.rule.body(), item.located.rule.body()),
            "original target body was not preserved as an immutable subtree");
        targetAfter.add(changed);
      }
      int changes = 0;
      for (String lineage : before.primaryRules.keySet()) {
        RuleState left = before.primaryRules.get(lineage);
        RuleState right = after.primaryRules.get(lineage);
        if (!left.content.equals(right.content)) changes++;
      }
      require(changes == 2, "changed primary-source rule count was not two");
      trace.ruleChangedRuleCount = changes;
      trace.ruleTargetContentAfter = targetAfter.stream()
          .map(RuleState::content).collect(Collectors.joining("|"));
      trace.ruleTargetBodyAfter = targetAfter.stream()
          .map(RuleState::body).collect(Collectors.joining("|"));
      trace.ruleIdentityPreserved = true;
      trace.ruleProvenancePreserved = true;
      trace.ruleAttributesPreserved = true;
      trace.ruleConditionsPreserved = true;
      trace.ruleOriginalNodesPreserved = true;
    }

    private static boolean containsIdentity(K root, K target) {
      if (root == target) return true;
      if (root instanceof KApply application) {
        for (K child : application.klist().items()) if (containsIdentity(child, target)) return true;
      } else if (root instanceof KRewrite rewrite) {
        return containsIdentity(rewrite.left(), target) || containsIdentity(rewrite.right(), target);
      } else if (root instanceof KSequence sequence) {
        for (K child : sequence.items()) if (containsIdentity(child, target)) return true;
      } else if (root instanceof KAs alias) {
        return containsIdentity(alias.pattern(), target) || containsIdentity(alias.alias(), target);
      }
      return false;
    }

    private static int countNamedGeneratedUpdates(K root, GeneratedCellDescriptor descriptor) {
      if (!(root instanceof KApply parent)) return 0;
      return (int) parent.klist().items().stream()
          .filter(KApply.class::isInstance)
          .map(KApply.class::cast)
          .filter(application -> application.klabel().name().equals(descriptor.label))
          .count();
    }

    private static int countExactGeneratedUpdates(
        K root, GeneratedCellDescriptor descriptor, MarkerEnvelope markers, K before, K after) {
      if (!(root instanceof KApply parent)) return 0;
      int count = 0;
      for (K child : parent.klist().items()) {
        if (child instanceof KApply application) {
          List<K> children = application.klist().items();
          Att expectedCellAtt = Att.empty()
              .add(Att.PRODUCTION(), Production.class, descriptor.production)
              .add(Att.SORT(), Sort.class, descriptor.cellSort);
          boolean exactProduction = application.klabel().equals(descriptor.production.klabel().get())
              && application.att().toString().equals(expectedCellAtt.toString());
          if (exactProduction && children.size() == 3
              && children.get(0).equals(markers.left)
              && children.get(2).equals(markers.right)
              && children.get(1) instanceof KRewrite rewrite
              && rewrite.left().equals(before) && rewrite.right().equals(after)
              && rewrite.att().equals(KRewrite(before, after).att())) {
            count++;
          }
        }
      }
      return count;
    }

    private static String applicationMetadata(KApply application) {
      Production production = productionOf(application, "structured projection");
      Att nodeMetadata = application.att()
          .remove(Att.PRODUCTION(), Production.class)
          .remove(Att.SORT(), Sort.class);
      return production.att().toString() + "|" + nodeMetadata.toString();
    }

    private static String nonProductionMetadata(K value) {
      return value.att()
          .remove(Att.PRODUCTION(), Production.class)
          .remove(Att.SORT(), Sort.class)
          .toString();
    }

    private static String termShape(KApply application) {
      return application.klabel().name() + "|" + application.klist().size();
    }

    private record MalformedExistingConstruction(
        Definition definition,
        LocatedRule located,
        KApply malformedGraph,
        ExistingGraphSnapshot before,
        ExistingGraphSnapshot after) {}

    private record StructuredGraphDelta(
        String operation,
        List<String> changedPaths,
        String beforeValue,
        String afterValue,
        String beforeGraphFingerprint,
        String afterGraphFingerprint) {
      String canonical() {
        return operation + "|" + String.join("|", changedPaths) + "|"
            + sha256(beforeValue) + "|"
            + sha256(afterValue) + "|" + beforeGraphFingerprint + "|"
            + afterGraphFingerprint;
      }
    }

    /** Projection of the actual production graph used by replacementFor and the negative mutator. */
    private record ExistingGraphSnapshot(
        String structure,
        Map<String, String> fields,
        String graphFingerprint,
        String structuralOperation,
        String structuralPath,
        String structuralValue,
        String referenceFragmentFingerprint,
        String removableValue) {
      static final String SCHEMA = "R3-G-05-existing-graph-projection-v1";

      static ExistingGraphSnapshot capture(
          KApply graph, PreparedTrace prepared, String representedSource) {
        String encoded = Projection.encodeTerm(
            graph, prepared.target.source, representedSource, Map.of());
        String graphFingerprint = sha256(encoded);
        List<K> outerChildren = graph.klist().items();
        String referenceFragment = outerChildren.size() >= 2
            ? sha256(Projection.encodeTerm(
                outerChildren.get(1), prepared.target.source, representedSource, Map.of()))
            : "";
        if (outerChildren.size() > 2) {
          boolean duplicate = outerChildren.stream().skip(2)
              .allMatch(item -> item.equals(outerChildren.get(1)));
          String inserted = Projection.encodeTerm(
              outerChildren.get(2), prepared.target.source, representedSource, Map.of());
          return new ExistingGraphSnapshot(
              duplicate ? "duplicate" : "extra", Map.of(), graphFingerprint,
              "insert", "parent.child[2]", inserted, referenceFragment, "");
        }
        if (outerChildren.size() != 2) {
          return new ExistingGraphSnapshot(
              "invalid", Map.of(), graphFingerprint, "", "", "", "", "");
        }
        Map<String, String> fields = new LinkedHashMap<>();
        String removable = "";
        try {
          KApply parent = requireApplication(outerChildren.get(0), "projected original parent");
          KApply cell = requireApplication(outerChildren.get(1), "projected generated cell");
          List<K> cellChildren = cell.klist().items();
          if (cellChildren.size() != 3) {
            return new ExistingGraphSnapshot(
                "invalid", Map.of(), graphFingerprint, "", "", "",
                referenceFragment, "");
          }
          KApply left = requireApplication(cellChildren.get(0), "projected left marker");
          KRewrite rewrite = requireRewrite(cellChildren.get(1));
          KApply right = requireApplication(cellChildren.get(2), "projected right marker");
          K after = rewrite.right();
          KApply append = requireApplication(
              resolvePath(after, prepared.targetOperation().witness.append), "projected append");
          String removalPath = "generatedCell.child[1].rewrite.after."
              + prepared.targetOperation().witness.append.canonical() + ".child[1]";
          if (append.klist().size() == 1) {
            return new ExistingGraphSnapshot(
                "partial", Map.of(), graphFingerprint, "remove", removalPath,
                "absent", referenceFragment, "");
          }
          if (append.klist().size() != 2) {
            return new ExistingGraphSnapshot(
                "invalid", Map.of(), graphFingerprint, "", "", "",
                referenceFragment, "");
          }
          removable = Projection.encodeTerm(
              append.klist().items().get(1), prepared.target.source,
              representedSource, Map.of());
          KApply singleton = requireApplication(
              resolvePath(after, prepared.targetOperation().witness.singleton), "projected singleton");
          KApply event = requireApplication(
              resolvePath(after, prepared.targetOperation().witness.event), "projected event");
          KApply origin = requireApplication(
              resolvePath(after, prepared.targetOperation().witness.origin), "projected origin");
          KVariable variable = requireVariable(resolvePath(
              after, childPath(prepared.targetOperation().witness.append, 0)));
          KToken token = requireToken(resolvePath(
              after, prepared.targetOperation().witness.location));
          fields.put("generatedCell.metadata", applicationMetadata(cell));
          fields.put("parent.production", productionStructure(productionOf(graph, "outer parent")));
          fields.put("generatedCell.production", productionStructure(productionOf(cell, "generated cell")));
          fields.put("leftMarker.production", productionStructure(productionOf(left, "left marker")));
          fields.put("rightMarker.production", productionStructure(productionOf(right, "right marker")));
          fields.put("leftMarker.term", termShape(left));
          fields.put("rightMarker.term", termShape(right));
          fields.put("append.production", productionStructure(productionOf(append, "append")));
          fields.put("singleton.production", productionStructure(productionOf(singleton, "singleton")));
          fields.put("event.production", productionStructure(productionOf(event, "event")));
          fields.put("origin.production", productionStructure(productionOf(origin, "origin")));
          fields.put("rewrite.metadata", nonProductionMetadata(rewrite));
          fields.put("variable.name", variable.name());
          fields.put("variable.sort", variable.att().getOptional(Att.SORT(), Sort.class)
              .map(Object::toString).orElse(""));
          fields.put("variable.metadata", nonProductionMetadata(variable));
          fields.put("payloadToken.sort", token.sort().toString());
          fields.put("payloadToken.metadata", nonProductionMetadata(token));
          fields.put("payload.lineage", tokenValue(after, prepared.targetOperation().witness.lineage));
          fields.put("payload.label", tokenValue(after, prepared.targetOperation().witness.label));
          fields.put("payload.module", tokenValue(after, prepared.targetOperation().witness.module));
          fields.put("payload.source", tokenValue(after, prepared.targetOperation().witness.source));
          fields.put("payload.location", tokenValue(after, prepared.targetOperation().witness.location));
          require(parent.klabel().equals(graph.klabel()),
              "projected parent layers have different term constructors");
        } catch (ValidationException malformed) {
          return new ExistingGraphSnapshot(
              "invalid", Map.of(), graphFingerprint, "", "", "",
              referenceFragment, "");
        }
        return new ExistingGraphSnapshot(
            "exact", java.util.Collections.unmodifiableMap(fields), graphFingerprint,
            "", "", "", referenceFragment, removable);
      }

      StructuredGraphDelta delta(ExistingGraphSnapshot after) {
        require(structure.equals("exact"), "valid before graph projection is not exact");
        if (!after.structure.equals("exact")) {
          String path = switch (after.structure) {
            case "partial", "duplicate", "extra" -> after.structuralPath;
            default -> throw reject("fixture", "unknown structured graph operation");
          };
          String beforeValue = after.structuralOperation.equals("remove")
              ? removableValue : "absent";
          String afterValue = after.structuralValue;
          require(!path.isBlank() && !beforeValue.isBlank() && !afterValue.isBlank(),
              "structured graph operation lacks an actual path/subtree delta");
          return new StructuredGraphDelta(
              after.structuralOperation, List.of(path), beforeValue, afterValue,
              graphFingerprint, after.graphFingerprint);
        }
        List<String> paths = fields.keySet().stream()
            .filter(path -> !fields.get(path).equals(after.fields.get(path)))
            .toList();
        require(paths.size() == 1, "primitive mutation did not change exactly one typed field");
        String path = paths.get(0);
        return new StructuredGraphDelta(
            "replace", paths, fields.get(path), after.fields.get(path),
            graphFingerprint, after.graphFingerprint);
      }

      String fieldFingerprintMap() {
        return fields.entrySet().stream()
            .map(item -> item.getKey() + ":" + sha256(item.getValue()))
            .collect(Collectors.joining(","));
      }

      private static String tokenValue(K root, TermPath path) {
        return requireToken(resolvePath(root, path)).s();
      }

      private static KToken requireToken(K value) {
        if (!(value instanceof KToken token)) {
          throw reject("fixture", "projected payload path is not a token");
        }
        return token;
      }
    }

  }

  private record PreparedTrace(
      LocatedRule located,
      TermPath parentPath,
      KApply parent,
      ProductionDescriptor parentDescriptor,
      GeneratedCellDescriptor descriptor,
      RuleState target,
      MarkerEnvelope markers,
      BuiltTerm before,
      BuiltTerm after,
      TraceMember targetOperation) {}

  private record PairCall(
      Definition output,
      String status,
      List<PreparedTrace> prepared,
      int validationCount,
      int applicationCount,
      int traversalCount,
      int inputIdentity,
      int outputIdentity,
      boolean sameReference,
      boolean outputDefinitionConstructed) {}

  private record BuiltTerm(K term, SortDescriptor sort) {}

  private record MarkerEnvelope(KApply left, KApply right) {}

  private record LocatedRule(Module module, Rule rule) {}

  private static LocatedRule locateRule(
      Definition definition, String primarySource, String lineage) {
    for (Module module : stream(definition.modules()).toList()) {
      for (Rule rule :
          stream(module.localSentences())
              .filter(Rule.class::isInstance)
              .map(Rule.class::cast)
              .toList()) {
        if (rule.source().map(value -> value.source()).orElse("").equals(primarySource)
            && RuleState.lineage(module.name(), rule).equals(lineage)) {
          return new LocatedRule(module, rule);
        }
      }
    }
    return null;
  }

  private static K resolvePath(K root, TermPath path) {
    K current = root;
    for (int index : path.indices) {
      if (!(current instanceof KApply application)) {
        throw new ValidationException("application-argument path reached non-application");
      }
      if (index < 0 || index >= application.klist().size()) {
        throw new ValidationException("application-argument path index out of bounds: " + index);
      }
      current = application.klist().items().get(index);
    }
    return current;
  }

  private static K resolveOperationPath(K ruleBody, TermPath path) {
    if (path.indices.isEmpty() || path.indices.get(0) != 0) {
      throw new ValidationException("operation path must enter the declared operation root at argument zero");
    }
    return resolvePath(ruleBody, new TermPath(List.copyOf(path.indices.subList(1, path.indices.size()))));
  }

  private static K replacePath(K root, TermPath path, K replacement) {
    if (path.indices.isEmpty()) return replacement;
    if (!(root instanceof KApply application)) throw new ValidationException("replace path reached non-application");
    int index = path.indices.get(0);
    if (index < 0 || index >= application.klist().size()) throw new ValidationException("replace path index out of bounds");
    List<K> items = new ArrayList<>(application.klist().items());
    items.set(index, replacePath(items.get(index), new TermPath(path.indices.subList(1, path.indices.size())), replacement));
    return KApply(application.klabel(), KList(items), application.att());
  }

  private static K replaceOperationPath(K ruleBody, TermPath path, K replacement) {
    if (path.indices.isEmpty() || path.indices.get(0) != 0) {
      throw new ValidationException("operation path must enter the declared operation root at argument zero");
    }
    return replacePath(
        ruleBody, new TermPath(List.copyOf(path.indices.subList(1, path.indices.size()))), replacement);
  }

  private record Request(String program, String fingerprint) {}

  private static final class Projection {
    private static String encodeTerm(K value) {
      return encodeTerm(value, "", "", Map.of());
    }

    private static String encodeTerm(
        K value,
        String primarySource,
        String representedSource,
        Map<String, String> lineageSubstitutions) {
      String meta =
          encodeMeta(value, primarySource, representedSource, lineageSubstitutions);
      if (value instanceof KApply application) {
        return "cApply(" + quote(application.klabel().name()) + ","
            + list(
                "cTermNil",
                "cTermCons",
                application.klist().items().stream()
                    .map(
                        item ->
                            encodeTerm(
                                item,
                                primarySource,
                                representedSource,
                                lineageSubstitutions))
                    .toList())
            + "," + meta + ")";
      }
      if (value instanceof KToken token) {
        String tokenValue =
            replaceIdentity(
                token.s(), primarySource, representedSource, lineageSubstitutions);
        return "cToken(" + quote(token.sort().toString()) + "," + quote(tokenValue) + "," + meta + ")";
      }
      if (value instanceof KVariable variable) return "cVariable(" + quote(variable.name()) + "," + meta + ")";
      if (value instanceof KRewrite rewrite) {
        return "cRewrite("
            + encodeTerm(rewrite.left(), primarySource, representedSource, lineageSubstitutions)
            + ","
            + encodeTerm(rewrite.right(), primarySource, representedSource, lineageSubstitutions)
            + "," + meta + ")";
      }
      if (value instanceof KSequence sequence) {
        return "cSequence("
            + list(
                "cTermNil",
                "cTermCons",
                sequence.items().stream()
                    .map(
                        item ->
                            encodeTerm(
                                item,
                                primarySource,
                                representedSource,
                                lineageSubstitutions))
                    .toList())
            + "," + meta + ")";
      }
      if (value instanceof KAs alias) {
        return "cAs("
            + encodeTerm(alias.pattern(), primarySource, representedSource, lineageSubstitutions)
            + ","
            + encodeTerm(alias.alias(), primarySource, representedSource, lineageSubstitutions)
            + "," + meta + ")";
      }
      if (value instanceof InjectedKLabel injected) return "cInjectedLabel(" + quote(injected.klabel().name()) + "," + meta + ")";
      throw reject("request-encoding", "unsupported typed K node: " + value.getClass());
    }

    private static String encodeOperationRoot(
        K value,
        String primarySource,
        String representedSource,
        Map<String, String> lineageSubstitutions) {
      return "cApply(" + quote("#operationRoot") + ",cTermCons("
          + encodeTerm(value, primarySource, representedSource, lineageSubstitutions)
          + ",cTermNil),cMeta(oSort(" + quote("OperationRoot") + ","
          + quote(sha256("OperationRoot")) + "),"
          + quote(sha256("R3-G-05-operation-root-production")) + ","
          + quote(sha256("R3-G-05-operation-root-metadata")) + "))";
    }

    private static String encodeMeta(
        K value,
        String primarySource,
        String representedSource,
        Map<String, String> lineageSubstitutions) {
      Att att = value.att();
      String sort = att.getOptional(Att.SORT(), Sort.class).map(Object::toString).orElse("");
      Production typedProduction =
          att.getOptional(Att.PRODUCTION(), Production.class).orElse(null);
      String production = typedProduction == null ? "" : productionStructure(typedProduction);
      if (value instanceof KToken token) sort = token.sort().toString();
      production =
          replaceIdentity(
              production, primarySource, representedSource, lineageSubstitutions);
      String attributes = typedProduction == null
          ? replaceIdentity(
              att.remove(Att.PRODUCTION(), Production.class)
                  .remove(Att.SORT(), Sort.class).toString(),
              primarySource, representedSource, lineageSubstitutions)
          : replaceIdentity(
              typedProduction.att().toString(),
              primarySource, representedSource, lineageSubstitutions);
      return "cMeta(oSort(" + quote(sort) + "," + quote(sha256(sort)) + "),"
          + quote(sha256(production)) + "," + quote(sha256(attributes)) + ")";
    }

    private static String list(String nil, String cons, List<String> values) {
      String result = nil;
      for (int index = values.size() - 1; index >= 0; index--) result = cons + "(" + values.get(index) + "," + result + ")";
      return result;
    }
  }

  private static final class TraceProjection {
    private static List<Rule> orderedRules(
        Module module, String primarySource, String representedSource) {
      return stream(module.localSentences())
          .filter(Rule.class::isInstance)
          .map(Rule.class::cast)
          .filter(
              rule ->
                  rule.source().map(value -> value.source()).orElse("")
                      .equals(primarySource))
          .sorted(
              Comparator.comparing(
                  rule -> RuleState.lineage(module.name(), rule, representedSource)))
          .toList();
    }

    static boolean hasPortableRuleOrdering(
        Definition definition, String primarySource, String representedSource) {
      for (Module module : stream(definition.modules()).toList()) {
        List<String> actual =
            orderedRules(module, primarySource, representedSource).stream()
                .map(rule -> RuleState.lineage(module.name(), rule, representedSource))
                .toList();
        if (!actual.equals(actual.stream().sorted().toList())) return false;
      }
      return true;
    }

    static Request encode(
        Definition definition,
        RuleDefinitionState state,
        String primarySource,
        String mode) {
      return encode(definition, state, primarySource, primarySource, mode);
    }

    static Request encode(
        Definition definition,
        RuleDefinitionState state,
        String primarySource,
        String representedSource,
        String mode) {
      Map<String, String> lineageSubstitutions =
          RuleDefinitionState.lineageSubstitutions(
              definition, primarySource, representedSource);
      List<String> modules = new ArrayList<>();
      for (Module module :
          stream(definition.modules()).sorted(Comparator.comparing(Module::name)).toList()) {
        List<Rule> rules = orderedRules(module, primarySource, representedSource);
        List<String> encoded = new ArrayList<>();
        for (Rule rule : rules) {
          RuleState item =
              RuleState.capture(
                  module.name(),
                  rule,
                  primarySource,
                  representedSource,
                  lineageSubstitutions);
          encoded.add(
              "oRule("
                  + quote(module.name()) + "," + quote("Rule") + ","
                  + quote(representedSource) + ","
                  + quote(rule.location().map(Object::toString).orElse("")) + ","
                  + quote(rule.label().orElse("")) + ","
                  + quote(item.lineage) + "," + quote(item.content) + ","
                  + quote(item.body) + "," + quote(item.requires) + ","
                  + quote(item.ensures) + "," + quote(item.attributes) + ","
                  + quote(StringUtil.enquoteKString(item.lineage)) + ","
                  + quote(StringUtil.enquoteKString(item.label)) + ","
                  + quote(StringUtil.enquoteKString(item.module)) + ","
                  + quote(StringUtil.enquoteKString(item.source)) + ","
                  + quote(StringUtil.enquoteKString(item.location)) + ","
                  + Projection.encodeOperationRoot(
                      rule.body(),
                      primarySource,
                      representedSource,
                      lineageSubstitutions)
                  + ")");
        }
        modules.add(
            "oModule("
                + quote(module.name()) + ","
                + Projection.list("oRuleNil", "oRuleCons", encoded) + ")");
      }
      List<String> descriptors =
          state.descriptors.stream()
              .map(
                  descriptor ->
                      "oGeneratedCell("
                          + quote(descriptor.module) + "," + quote(descriptor.name) + ","
                          + quote(descriptor.label) + ","
                          + sort(descriptor.cellSortDescriptor) + ","
                          + sort(descriptor.bodySortDescriptor) + ","
                          + quote(descriptor.productionFingerprint) + ","
                          + quote(descriptor.labelFingerprint) + ","
                          + quote(descriptor.metadataFingerprint) + ")")
              .toList();
      List<String> productions =
          state.productions.stream()
              .map(TraceProjection::production)
              .toList();
      List<String> sorts = state.sorts.stream().map(TraceProjection::sort).toList();
      List<String> subsorts =
          state.subsorts.stream()
              .map(item -> "oSubsort(" + sort(item.sub) + "," + sort(item.sup) + ","
                  + quote(item.fingerprint) + ")")
              .toList();
      String definitionTerm =
          "oDefinition("
              + quote(TRACE_SCHEMA) + "," + quote(state.fingerprint) + ","
              + Projection.list("oModuleNil", "oModuleCons", modules) + ","
              + Projection.list("oGeneratedCellNil", "oGeneratedCellCons", descriptors) + ","
              + Projection.list("oProductionNil", "oProductionCons", productions) + ","
              + Projection.list("oSortDescriptorNil", "oSortDescriptorCons", sorts) + ","
              + Projection.list("oSubsortNil", "oSubsortCons", subsorts) + ","
              + termMetadataAuthority(state).canonical() + ")";
      String program = "proposeRuleAppliedAllowlist(" + quote(mode) + "," + definitionTerm + ")\n";
      return new Request(program, sha256(definitionTerm));
    }

    private static String sort(SortDescriptor descriptor) {
      return "oSort(" + quote(descriptor.name) + "," + quote(descriptor.fingerprint) + ")";
    }

    private static String production(ProductionDescriptor descriptor) {
      return "oProduction("
          + quote(descriptor.module) + "," + quote(descriptor.label) + ","
          + sort(descriptor.resultSort) + ","
          + Projection.list(
              "oSortNil",
              "oSortCons",
              descriptor.argumentSorts.stream().map(TraceProjection::sort).toList()) + ","
          + quote(descriptor.productionFingerprint) + ","
          + quote(descriptor.labelFingerprint) + ","
          + quote(descriptor.metadataFingerprint) + ")";
    }

    private static TermMetadataAuthority termMetadataAuthority(RuleDefinitionState state) {
      SortDescriptor list = uniqueSort(state, "List");
      SortDescriptor string = uniqueSort(state, "String");
      SortSpec listSpec = new SortSpec(list.name, list.fingerprint);
      SortSpec stringSpec = new SortSpec(string.name, string.fingerprint);
      String emptyProduction = sha256("");
      String emptyMetadata = sha256(Att.empty().toString());
      return new TermMetadataAuthority(
          new MetaSpec(
              new SortSpec("OperationRoot", sha256("OperationRoot")),
              sha256("R3-G-05-operation-root-production"),
              sha256("R3-G-05-operation-root-metadata")),
          new MetaSpec(new SortSpec("", sha256("")), emptyProduction, emptyMetadata),
          listSpec,
          new MetaSpec(
              listSpec,
              emptyProduction,
              emptyMetadata),
          stringSpec,
          new MetaSpec(stringSpec, emptyProduction, emptyMetadata));
    }

    private static SortDescriptor uniqueSort(RuleDefinitionState state, String name) {
      List<SortDescriptor> matches =
          state.sorts.stream().filter(item -> item.name.equals(name)).toList();
      require(matches.size() == 1, "generic metadata sort was not unique: " + name);
      return matches.get(0);
    }
  }

  private sealed interface TraceOutcome
      permits TraceResult, TraceFailure {
    String canonical();
    String status();
    int count();
  }

  private record TraceMember(
      String lineage,
      String content,
      String body,
      String requires,
      String ensures,
      String attributes,
      String module,
      String label,
      String source,
      String location,
      TermPath parentPath,
      String name,
      String variable,
      SortSpec variableSort,
      TermSpec beforeTerm,
      TermSpec afterTerm,
      TraceWitness witness,
      OperationAuthority authority) {
    String operationCanonical() {
      return "appendGeneratedCellTerm("
          + parentPath.canonical() + "," + quote(name) + ","
          + quote(variable) + "," + variableSort.canonical() + ","
          + beforeTerm.canonical() + "," + afterTerm.canonical() + ","
          + witness.canonical() + "," + authority.canonical() + ")";
    }
    String canonical() {
      return "oAllowlistMember("
          + quote(lineage) + "," + quote(content) + ","
          + quote(body) + "," + quote(requires) + "," + quote(ensures) + ","
          + quote(attributes) + "," + quote(module) + "," + quote(label) + ","
          + quote(source) + "," + quote(location) + "," + operationCanonical() + ")";
    }
  }

  private record ResultIdentity(
      String schema,
      String transformation,
      String definitionFingerprint,
      int candidateCount,
      String status,
      TraceMember first,
      TraceMember second) {
    String canonical() {
      return "oResultIdentity(" + quote(schema) + "," + quote(transformation) + ","
          + quote(definitionFingerprint) + "," + candidateCount + "," + quote(status) + ","
          + first.canonical() + "," + second.canonical() + ")";
    }
  }

  private record TraceResult(
      String schema,
      String transformation,
      String definitionFingerprint,
      int candidateCount,
      String status,
      ResultIdentity identity,
      List<TraceMember> members) implements TraceOutcome {
    @Override public int count() { return candidateCount; }
    @Override public String canonical() {
      String encoded = "oAllowlistMemberNil";
      for (int index = members.size() - 1; index >= 0; index--) {
        encoded = "oAllowlistMemberCons(" + members.get(index).canonical() + "," + encoded + ")";
      }
      return "oAllowlistResult("
          + quote(schema) + "," + quote(transformation) + ","
          + quote(definitionFingerprint) + "," + candidateCount + ","
          + quote(status) + "," + identity.canonical() + "," + encoded + ")";
    }
  }

  private record SortSpec(String name, String fingerprint) {
    String canonical() {
      return "oSort(" + quote(name) + "," + quote(fingerprint) + ")";
    }
  }

  private record ProductionSpec(
      String module,
      String label,
      SortSpec resultSort,
      List<SortSpec> argumentSorts,
      String productionFingerprint,
      String labelFingerprint,
      String metadataFingerprint) {
    String canonical() {
      String arguments = "oSortNil";
      for (int index = argumentSorts.size() - 1; index >= 0; index--) {
        arguments = "oSortCons(" + argumentSorts.get(index).canonical() + "," + arguments + ")";
      }
      return "oProduction(" + quote(module) + "," + quote(label) + ","
          + resultSort.canonical() + "," + arguments + ","
          + quote(productionFingerprint) + "," + quote(labelFingerprint) + ","
          + quote(metadataFingerprint) + ")";
    }
  }

  private record GeneratedCellSpec(
      String module,
      String name,
      String label,
      SortSpec cellSort,
      SortSpec bodySort,
      String productionFingerprint,
      String labelFingerprint,
      String metadataFingerprint) {
    String canonical() {
      return "oGeneratedCell(" + quote(module) + "," + quote(name) + "," + quote(label) + ","
          + cellSort.canonical() + "," + bodySort.canonical() + ","
          + quote(productionFingerprint) + "," + quote(labelFingerprint) + ","
          + quote(metadataFingerprint) + ")";
    }
  }

  private record OperationAuthority(
      GeneratedCellSpec generatedCell,
      ProductionSpec parentProduction,
      ProductionSpec cellProduction,
      ProductionSpec leftMarkerProduction,
      ProductionSpec rightMarkerProduction,
      ProductionSpec appendProduction,
      ProductionSpec singletonProduction,
      ProductionSpec eventProduction,
      ProductionSpec originProduction,
      TermSpec leftMarkerTerm,
      TermSpec rightMarkerTerm,
      TermMetadataAuthority termMetadata) {
    String canonical() {
      return "oOperationAuthority(" + generatedCell.canonical() + ","
          + parentProduction.canonical() + "," + cellProduction.canonical() + ","
          + leftMarkerProduction.canonical() + "," + rightMarkerProduction.canonical() + ","
          + appendProduction.canonical() + "," + singletonProduction.canonical() + ","
          + eventProduction.canonical() + "," + originProduction.canonical() + ","
          + leftMarkerTerm.canonical() + "," + rightMarkerTerm.canonical() + ","
          + termMetadata.canonical() + ")";
    }
  }

  private record MetaSpec(
      SortSpec sort, String productionFingerprint, String metadataFingerprint) {
    String canonical() {
      return "cMeta(" + sort.canonical() + "," + quote(productionFingerprint) + ","
          + quote(metadataFingerprint) + ")";
    }
  }

  private record TermMetadataAuthority(
      MetaSpec operationRoot,
      MetaSpec rewrite,
      SortSpec variableSort,
      MetaSpec variable,
      SortSpec tokenSort,
      MetaSpec token) {
    String canonical() {
      return "oTermMetadataAuthority(" + operationRoot.canonical() + ","
          + rewrite.canonical() + "," + variableSort.canonical() + ","
          + variable.canonical() + "," + tokenSort.canonical() + ","
          + token.canonical() + ")";
    }
  }

  private sealed interface TermSpec permits ApplySpec, TokenSpec, VariableSpec {
    SortSpec sort();
    String canonical();
  }

  private record ApplySpec(
      ProductionSpec production,
      List<TermSpec> arguments) implements TermSpec {
    @Override public SortSpec sort() { return production.resultSort; }
    @Override public String canonical() {
      return "tApply(" + production.canonical() + "," + termList(arguments) + ")";
    }
  }

  private record TokenSpec(SortSpec sort, String value, String lexeme) implements TermSpec {
    @Override public String canonical() {
      return "tToken(" + sort.canonical() + "," + quote(value) + "," + quote(lexeme) + ")";
    }
  }

  private record VariableSpec(String name, SortSpec sort) implements TermSpec {
    @Override public String canonical() { return "tVariable(" + quote(name) + "," + sort.canonical() + ")"; }
  }

  private record TraceWitness(
      TermPath append,
      TermPath singleton,
      TermPath event,
      TermPath origin,
      TermPath lineage,
      TermPath label,
      TermPath module,
      TermPath source,
      TermPath location) {
    String canonical() {
      return "oAllowlistWitness(" + append.canonical() + "," + singleton.canonical() + ","
          + event.canonical() + "," + origin.canonical() + "," + lineage.canonical() + ","
          + label.canonical() + "," + module.canonical() + "," + source.canonical() + ","
          + location.canonical() + ")";
    }
  }

  private static String termList(List<TermSpec> values) {
    String result = "tTermNil";
    for (int index = values.size() - 1; index >= 0; index--) {
      result = "tTermCons(" + values.get(index).canonical() + "," + result + ")";
    }
    return result;
  }

  private record TraceFailure(String schema, String reason, int count)
      implements TraceOutcome {
    @Override public String status() { return "failure:" + reason; }
    @Override public String canonical() {
      return "oAllowlistFailure("
          + quote(schema) + "," + quote(reason) + "," + count + ")";
    }
  }

  private record TraceInvocation(Request request, TraceOutcome outcome) {}

  private static final class TraceResultParser {
    static List<String> selfTest() {
      List<String> cases = new ArrayList<>();
      SortSpec list = new SortSpec("ListSort", "list-sort-fingerprint");
      SortSpec string = new SortSpec("StringSort", "string-sort-fingerprint");
      ProductionSpec append =
          new ProductionSpec(
              "module", "append", list, List.of(list, list), "production", "label-fingerprint", "metadata");
      TermSpec before = new VariableSpec("TRACE_FRESH", list);
      TermSpec after =
          new ApplySpec(append, List.of(before, new TokenSpec(string, "payload", "\"payload\"")));
      TermPath root = new TermPath(List.of());
      GeneratedCellSpec cell = new GeneratedCellSpec(
          "module", "cell", "cell-label", list, list,
          "cell-production", "cell-label-fingerprint", "cell-metadata");
      MetaSpec emptyMeta = new MetaSpec(list, "empty-production", "empty-metadata");
      TermMetadataAuthority termMetadata = new TermMetadataAuthority(
          new MetaSpec(
              new SortSpec("OperationRoot", "operation-root-sort"),
              "root-production", "root-metadata"),
          emptyMeta, list, emptyMeta, string,
          new MetaSpec(string, "token-production", "token-metadata"));
      OperationAuthority authority = new OperationAuthority(
          cell, append, append, append, append, append, append, append, append,
          new ApplySpec(append, List.of()), new ApplySpec(append, List.of()), termMetadata);
      TraceMember first = new TraceMember(
          "lineage-a", "content-a", "body-a", "requires-a",
          "ensures-a", "attributes-a", "module", "label-a",
          "source", "location-a", new TermPath(List.of(0)),
          "cell", "TRACE_FRESH_A", list, before, after,
          new TraceWitness(root, root, root, root, root, root, root, root, root), authority);
      TraceMember second = new TraceMember(
          "lineage-b", "content-b", "body-b", "requires-b",
          "ensures-b", "attributes-b", "module", "label-b",
          "source", "location-b", new TermPath(List.of(0)),
          "cell", "TRACE_FRESH_B", list, before, after,
          new TraceWitness(root, root, root, root, root, root, root, root, root), authority);
      String canonical =
          "<k>"
              + new TraceResult(
                      TRACE_SCHEMA, TRACE_TRANSFORMATION, "definition", 2, "apply",
                      new ResultIdentity(
                          TRACE_SCHEMA, TRACE_TRANSFORMATION, "definition", 2, "apply",
                          first, second),
                      List.of(first, second))
                  .canonical()
              + "~>.K</k>";
      parse(canonical);
      cases.add("canonical-result-accepted");
      requireParserMutationRejection(
          canonical, canonical.replace(",2,\"apply\"", ",02,\"apply\""),
          "leading-zero-integer");
      cases.add("leading-zero-integer-rejected");
      requireParserMutationRejection(
          canonical,
          canonical.replace("cApplicationArgument(0)", "cApplicationArgument(-0)"),
          "negative-zero-path");
      cases.add("negative-zero-path-rejected");
      requireParserMutationRejection(
          canonical,
          canonical.replace(
              "\"KRuleAppliedAllowlist-v1\"", "\"\\u004bRuleAppliedAllowlist-v1\""),
          "unicode-escape");
      cases.add("unicode-escape-rejected");
      requireParserMutationRejection(
          canonical,
          canonical.replace(
              "oAllowlistMember(\"lineage-a\",\"content-a\"",
              "oAllowlistMember(\"lineage-a\"\"content-a\""),
          "missing-delimiter");
      cases.add("missing-delimiter-rejected");
      requireParserMutationRejection(canonical, canonical + canonical, "multiple-result");
      cases.add("multiple-result-rejected");
      requireParserMutationRejection(
          canonical, canonical.replace("~>.K", "~>residual~>.K"), "residual-result");
      cases.add("residual-result-rejected");
      requireParserMutationRejection(
          canonical,
          canonical.replace("oAllowlistResult", "oUnknownResult"),
          "unknown-result");
      cases.add("unknown-result-rejected");
      return List.copyOf(cases);
    }

    private static void requireParserMutationRejection(
        String canonical, String mutated, String name) {
      if (mutated.equals(canonical)) {
        throw new AssertionError(name + " parser mutation did not change canonical result");
      }
      try {
        parse(mutated);
      } catch (ValidationException expected) {
        return;
      }
      throw new AssertionError(name + " noncanonical or malformed trace result was accepted");
    }

    static TraceOutcome parse(String output) {
      Reader reader = new Reader(output);
      reader.expect("<k>");
      String constructor = reader.identifier();
      TraceOutcome result;
      if (constructor.equals("oAllowlistFailure")) {
        reader.expect('(');
        String schema = reader.string(); reader.expect(',');
        String reason = reader.string(); reader.expect(',');
        int count = reader.integer(); reader.expect(')');
        result = new TraceFailure(schema, reason, count);
      } else if (constructor.equals("oAllowlistResult")) {
        reader.expect('(');
        String schema = reader.string(); reader.expect(',');
        String transformation = reader.string(); reader.expect(',');
        String definition = reader.string(); reader.expect(',');
        int count = reader.integer(); reader.expect(',');
        String status = reader.string(); reader.expect(',');
        ResultIdentity identity = identity(reader); reader.expect(',');
        List<TraceMember> members = members(reader); reader.expect(')');
        result = new TraceResult(schema, transformation, definition, count, status, identity, members);
      } else {
        throw reject("envelope", "unexpected K trace result constructor: " + constructor);
      }
      reader.expect("~>"); reader.expect(".K"); reader.expect("</k>"); reader.end();
      return result;
    }

    private static List<TraceMember> members(Reader reader) {
      String constructor = reader.identifier();
      if (constructor.equals("oAllowlistMemberNil")) return List.of();
      if (!constructor.equals("oAllowlistMemberCons")) {
        throw reject("envelope", "unknown allowlist member-list constructor");
      }
      reader.expect('(');
      TraceMember head = member(reader); reader.expect(',');
      List<TraceMember> tail = members(reader); reader.expect(')');
      List<TraceMember> result = new ArrayList<>();
      result.add(head); result.addAll(tail); return List.copyOf(result);
    }

    private static TraceMember member(Reader reader) {
      reader.expectIdentifier("oAllowlistMember"); reader.expect('(');
      String lineage = reader.string(); reader.expect(',');
      String content = reader.string(); reader.expect(',');
      String body = reader.string(); reader.expect(',');
      String requires = reader.string(); reader.expect(',');
      String ensures = reader.string(); reader.expect(',');
      String attributes = reader.string(); reader.expect(',');
      String module = reader.string(); reader.expect(',');
      String label = reader.string(); reader.expect(',');
      String source = reader.string(); reader.expect(',');
      String location = reader.string(); reader.expect(',');
      reader.expectIdentifier("appendGeneratedCellTerm"); reader.expect('(');
        TermPath parent = PathParser.path(reader); reader.expect(',');
        String name = reader.string(); reader.expect(',');
        String variable = reader.string(); reader.expect(',');
        SortSpec variableSort = sort(reader); reader.expect(',');
        TermSpec before = term(reader); reader.expect(',');
        TermSpec after = term(reader); reader.expect(',');
      TraceWitness witness = witness(reader); reader.expect(',');
      OperationAuthority authority = authority(reader); reader.expect(')'); reader.expect(')');
      return new TraceMember(
          lineage, content, body, requires, ensures, attributes, module, label,
          source, location, parent, name, variable, variableSort, before, after,
          witness, authority);
    }

    private static ResultIdentity identity(Reader reader) {
      reader.expectIdentifier("oResultIdentity"); reader.expect('(');
      String schema = reader.string(); reader.expect(',');
      String transformation = reader.string(); reader.expect(',');
      String definition = reader.string(); reader.expect(',');
      int count = reader.integer(); reader.expect(',');
      String status = reader.string(); reader.expect(',');
      TraceMember first = member(reader); reader.expect(',');
      TraceMember second = member(reader); reader.expect(')');
      return new ResultIdentity(schema, transformation, definition, count, status, first, second);
    }

    private static OperationAuthority authority(Reader reader) {
      reader.expectIdentifier("oOperationAuthority"); reader.expect('(');
      GeneratedCellSpec cell = generatedCell(reader); reader.expect(',');
      ProductionSpec parent = production(reader); reader.expect(',');
      ProductionSpec cellProduction = production(reader); reader.expect(',');
      ProductionSpec leftProduction = production(reader); reader.expect(',');
      ProductionSpec rightProduction = production(reader); reader.expect(',');
      ProductionSpec appendProduction = production(reader); reader.expect(',');
      ProductionSpec singletonProduction = production(reader); reader.expect(',');
      ProductionSpec eventProduction = production(reader); reader.expect(',');
      ProductionSpec originProduction = production(reader); reader.expect(',');
      TermSpec left = term(reader); reader.expect(',');
      TermSpec right = term(reader); reader.expect(',');
      TermMetadataAuthority termMetadata = termMetadata(reader); reader.expect(')');
      return new OperationAuthority(
          cell, parent, cellProduction, leftProduction, rightProduction,
          appendProduction, singletonProduction, eventProduction, originProduction,
          left, right, termMetadata);
    }

    private static TermMetadataAuthority termMetadata(Reader reader) {
      reader.expectIdentifier("oTermMetadataAuthority"); reader.expect('(');
      MetaSpec root = meta(reader); reader.expect(',');
      MetaSpec rewrite = meta(reader); reader.expect(',');
      SortSpec variableSort = sort(reader); reader.expect(',');
      MetaSpec variable = meta(reader); reader.expect(',');
      SortSpec tokenSort = sort(reader); reader.expect(',');
      MetaSpec token = meta(reader); reader.expect(')');
      return new TermMetadataAuthority(
          root, rewrite, variableSort, variable, tokenSort, token);
    }

    private static MetaSpec meta(Reader reader) {
      reader.expectIdentifier("cMeta"); reader.expect('(');
      SortSpec sort = sort(reader); reader.expect(',');
      String production = reader.string(); reader.expect(',');
      String metadata = reader.string(); reader.expect(')');
      return new MetaSpec(sort, production, metadata);
    }

    private static GeneratedCellSpec generatedCell(Reader reader) {
      reader.expectIdentifier("oGeneratedCell"); reader.expect('(');
      String module = reader.string(); reader.expect(',');
      String name = reader.string(); reader.expect(',');
      String label = reader.string(); reader.expect(',');
      SortSpec cellSort = sort(reader); reader.expect(',');
      SortSpec bodySort = sort(reader); reader.expect(',');
      String production = reader.string(); reader.expect(',');
      String labelFingerprint = reader.string(); reader.expect(',');
      String metadata = reader.string(); reader.expect(')');
      return new GeneratedCellSpec(
          module, name, label, cellSort, bodySort, production, labelFingerprint, metadata);
    }

    private static TermSpec term(Reader reader) {
      String constructor = reader.identifier();
      reader.expect('(');
      if (constructor.equals("tVariable")) {
        String name = reader.string(); reader.expect(','); SortSpec sort = sort(reader); reader.expect(')');
        return new VariableSpec(name, sort);
      }
      if (constructor.equals("tToken")) {
        SortSpec sort = sort(reader); reader.expect(','); String value = reader.string(); reader.expect(',');
        String lexeme = reader.string(); reader.expect(')');
        return new TokenSpec(sort, value, lexeme);
      }
      if (constructor.equals("tApply")) {
        ProductionSpec production = production(reader); reader.expect(',');
        List<TermSpec> arguments = terms(reader); reader.expect(')');
        return new ApplySpec(production, arguments);
      }
      throw reject("envelope", "unknown typed term constructor: " + constructor);
    }

    private static List<TermSpec> terms(Reader reader) {
      String constructor = reader.identifier();
      if (constructor.equals("tTermNil")) return List.of();
      if (!constructor.equals("tTermCons")) throw reject("envelope", "unknown typed term list constructor");
      reader.expect('('); TermSpec head = term(reader); reader.expect(','); List<TermSpec> tail = terms(reader); reader.expect(')');
      List<TermSpec> result = new ArrayList<>(); result.add(head); result.addAll(tail); return List.copyOf(result);
    }

    private static SortSpec sort(Reader reader) {
      reader.expectIdentifier("oSort"); reader.expect('(');
      String name = reader.string(); reader.expect(','); String fingerprint = reader.string(); reader.expect(')');
      return new SortSpec(name, fingerprint);
    }

    private static ProductionSpec production(Reader reader) {
      reader.expectIdentifier("oProduction"); reader.expect('(');
      String module = reader.string(); reader.expect(','); String label = reader.string(); reader.expect(',');
      SortSpec result = sort(reader); reader.expect(','); List<SortSpec> arguments = sorts(reader); reader.expect(',');
      String production = reader.string(); reader.expect(','); String labelFingerprint = reader.string(); reader.expect(',');
      String metadata = reader.string(); reader.expect(')');
      return new ProductionSpec(module, label, result, arguments, production, labelFingerprint, metadata);
    }

    private static List<SortSpec> sorts(Reader reader) {
      String constructor = reader.identifier();
      if (constructor.equals("oSortNil")) return List.of();
      if (!constructor.equals("oSortCons")) throw reject("envelope", "unknown sort list constructor");
      reader.expect('('); SortSpec head = sort(reader); reader.expect(','); List<SortSpec> tail = sorts(reader); reader.expect(')');
      List<SortSpec> result = new ArrayList<>(); result.add(head); result.addAll(tail); return List.copyOf(result);
    }

    private static TraceWitness witness(Reader reader) {
      reader.expectIdentifier("oAllowlistWitness"); reader.expect('(');
      TermPath append = PathParser.path(reader); reader.expect(',');
      TermPath singleton = PathParser.path(reader); reader.expect(',');
      TermPath event = PathParser.path(reader); reader.expect(',');
      TermPath origin = PathParser.path(reader); reader.expect(',');
      TermPath lineage = PathParser.path(reader); reader.expect(',');
      TermPath label = PathParser.path(reader); reader.expect(',');
      TermPath module = PathParser.path(reader); reader.expect(',');
      TermPath source = PathParser.path(reader); reader.expect(',');
      TermPath location = PathParser.path(reader); reader.expect(')');
      return new TraceWitness(append, singleton, event, origin, lineage, label, module, source, location);
    }
  }

  private record TermPath(List<Integer> indices) {
    String canonical() {
      String result = "cPathNil";
      for (int index = indices.size() - 1; index >= 0; index--) result = "cPathCons(cApplicationArgument(" + indices.get(index) + ")," + result + ")";
      return result;
    }
  }

  private static final class PathParser {
    private static TermPath path(Reader reader) {
      String constructor = reader.identifier();
      if (constructor.equals("cPathNil")) return new TermPath(List.of());
      if (!constructor.equals("cPathCons")) throw reject("result-envelope-validation", "unexpected path constructor");
      reader.expect('('); reader.expectIdentifier("cApplicationArgument"); reader.expect('('); int index = reader.integer(); reader.expect(')'); reader.expect(','); TermPath rest = path(reader); reader.expect(')');
      List<Integer> result = new ArrayList<>(); result.add(index); result.addAll(rest.indices); return new TermPath(List.copyOf(result));
    }
  }

  private static final class Reader {
    final String input; int offset;
    Reader(String input) { this.input = input; }
    void skip() { while (offset < input.length() && Character.isWhitespace(input.charAt(offset))) offset++; }
    void expect(String value) { skip(); if (!input.startsWith(value, offset)) throw reject("result-envelope-validation", "expected " + value + " at " + offset); offset += value.length(); }
    void expect(char value) { skip(); if (offset >= input.length() || input.charAt(offset) != value) throw reject("result-envelope-validation", "expected " + value + " at " + offset); offset++; }
    void expectIdentifier(String value) { String actual = identifier(); if (!actual.equals(value)) throw reject("result-envelope-validation", "expected " + value + ", found " + actual); }
    String identifier() { skip(); int start = offset; while (offset < input.length() && (Character.isLetterOrDigit(input.charAt(offset)) || input.charAt(offset) == '_' || input.charAt(offset) == '#')) offset++; if (start == offset) throw reject("result-envelope-validation", "expected constructor at " + offset); return input.substring(start, offset); }
    int integer() {
      skip();
      int start = offset;
      if (offset < input.length() && input.charAt(offset) == '-') offset++;
      int digits = offset;
      while (offset < input.length() && Character.isDigit(input.charAt(offset))) offset++;
      if (digits == offset) throw reject("result-envelope-validation", "invalid integer");
      String encoded = input.substring(start, offset);
      try {
        int value = Integer.parseInt(encoded);
        if (!encoded.equals(Integer.toString(value))) {
          throw reject("result-envelope-validation", "noncanonical integer");
        }
        return value;
      } catch (NumberFormatException e) {
        throw reject("result-envelope-validation", "invalid integer");
      }
    }
    String string() {
      skip();
      int start = offset;
      if (offset >= input.length() || input.charAt(offset++) != '"') {
        throw reject("result-envelope-validation", "expected string");
      }
      StringBuilder out = new StringBuilder();
      while (offset < input.length()) {
        char ch = input.charAt(offset++);
        if (ch == '"') {
          String value = out.toString();
          if (!input.substring(start, offset).equals(quote(value))) {
            throw reject("result-envelope-validation", "noncanonical string");
          }
          return value;
        }
        if (ch != '\\') { out.append(ch); continue; }
        if (offset >= input.length()) throw reject("result-envelope-validation", "bad string escape");
        char escaped = input.charAt(offset++);
        switch (escaped) {
          case '"' -> out.append('"');
          case '\\' -> out.append('\\');
          case 'n' -> out.append('\n');
          case 'r' -> out.append('\r');
          case 't' -> out.append('\t');
          case 'b' -> out.append('\b');
          case 'f' -> out.append('\f');
          case 'u' -> {
            if (offset + 4 > input.length()) throw reject("result-envelope-validation", "bad string escape");
            try {
              out.append((char) Integer.parseInt(input.substring(offset, offset + 4), 16));
            } catch (NumberFormatException e) {
              throw reject("result-envelope-validation", "bad string escape");
            }
            offset += 4;
          }
          default -> throw reject("result-envelope-validation", "bad string escape");
        }
      }
      throw reject("result-envelope-validation", "unterminated string");
    }
    void end() { skip(); if (offset != input.length()) throw reject("result-envelope-validation", "residual K result"); }
  }

  private static final class RuleDefinitionState {
    final String fingerprint;
    final String nonPrimaryFingerprint;
    final int moduleCount;
    final int sentenceCount;
    final Map<String, RuleState> primaryRules;
    final List<GeneratedCellDescriptor> descriptors;
    final List<ProductionDescriptor> productions;
    final List<SortDescriptor> sorts;
    final List<SubsortDescriptor> subsorts;

    RuleDefinitionState(
        String fingerprint,
        String nonPrimaryFingerprint,
        int moduleCount,
        int sentenceCount,
        Map<String, RuleState> primaryRules,
        List<GeneratedCellDescriptor> descriptors,
        List<ProductionDescriptor> productions,
        List<SortDescriptor> sorts,
        List<SubsortDescriptor> subsorts) {
      this.fingerprint = fingerprint;
      this.nonPrimaryFingerprint = nonPrimaryFingerprint;
      this.moduleCount = moduleCount;
      this.sentenceCount = sentenceCount;
      this.primaryRules = primaryRules;
      this.descriptors = descriptors;
      this.productions = productions;
      this.sorts = sorts;
      this.subsorts = subsorts;
    }

    static RuleDefinitionState capture(Definition definition, String primarySource) {
      return capture(definition, primarySource, primarySource);
    }

    static RuleDefinitionState capture(
        Definition definition, String primarySource, String representedSource) {
      Map<String, String> lineageSubstitutions =
          lineageSubstitutions(definition, primarySource, representedSource);
      StringBuilder graph =
          new StringBuilder("definition|")
              .append(definition.att()).append('|')
              .append(definition.mainModule().name()).append('\n');
      StringBuilder nonPrimary = new StringBuilder();
      Map<String, RuleState> rules = new LinkedHashMap<>();
      List<GeneratedCellDescriptor> descriptors = new ArrayList<>();
      List<ProductionDescriptor> productions = new ArrayList<>();
      Map<String, SortDescriptor> sorts = new LinkedHashMap<>();
      Map<String, SubsortDescriptor> subsorts = new LinkedHashMap<>();
      int sentences = 0;
      List<Module> modules =
          stream(definition.modules()).sorted(Comparator.comparing(Module::name)).toList();
      for (Module module : modules) {
        graph.append("module|").append(module.name()).append('|').append(module.att()).append('\n');
        stream(module.imports())
            .map(value -> value.module().name() + "|" + value.isPublic())
            .sorted()
            .forEach(value -> graph.append("import|").append(value).append('\n'));
        List<Sentence> local =
            stream(module.localSentences())
                .sorted(Comparator.comparing(value -> value.getClass().getName() + "|" + value + "|" + value.att()))
                .toList();
        sentences += local.size();
        for (Sentence sentence : local) {
          if (sentence instanceof Rule rule
              && rule.source().map(value -> value.source()).orElse("").equals(primarySource)) {
            RuleState state =
                RuleState.capture(
                    module.name(),
                    rule,
                    primarySource,
                    representedSource,
                    lineageSubstitutions);
            if (rules.put(state.lineage, state) != null) {
              throw reject("request-encoding", "duplicate primary-source rule lineage");
            }
          } else {
            nonPrimary
                .append(module.name()).append('|')
                .append(sentence.getClass().getName()).append('|')
                .append(sentence).append('|').append(sentence.att()).append('\n');
          }
          if (sentence instanceof Production production) {
            SortDescriptor resultSort = SortDescriptor.capture(production.sort());
            sorts.putIfAbsent(resultSort.canonical(), resultSort);
            for (int index = 0; index < production.arity(); index++) {
              SortDescriptor argumentSort = SortDescriptor.capture(production.nonterminal(index).sort());
              sorts.putIfAbsent(argumentSort.canonical(), argumentSort);
            }
            if (production.att().contains(Att.CELL())
                && production.klabel().isDefined()
                && production.arity() == 1) {
              String name = production.att().getOptional(Att.CELL_NAME()).orElse("");
              if (!name.isBlank()) {
                descriptors.add(
                    GeneratedCellDescriptor.capture(
                        module.name(), name, production, primarySource, representedSource));
              }
            }
            if (production.klabel().isDefined()) {
              productions.add(
                  ProductionDescriptor.capture(
                      module.name(), production, primarySource, representedSource));
            }
            if (production.isSubsort() && production.arity() == 1) {
              SubsortDescriptor relation =
                  SubsortDescriptor.capture(
                      production.nonterminal(0).sort(), production.sort());
              subsorts.putIfAbsent(relation.canonical(), relation);
            }
          }
        }
      }
      for (Module module : modules) {
        org.kframework.POSet<Sort> semanticSubsorts = module.subsorts();
        for (Sort sub : semanticSubsorts.elements()) {
          SortDescriptor descriptor = SortDescriptor.capture(sub);
          sorts.putIfAbsent(descriptor.canonical(), descriptor);
          for (Sort sup : semanticSubsorts.elements()) {
            if (semanticSubsorts.directlyLessThan(sub, sup)) {
              SubsortDescriptor relation = SubsortDescriptor.capture(sub, sup);
              subsorts.putIfAbsent(relation.canonical(), relation);
            }
          }
        }
      }
      descriptors.sort(Comparator.comparing(GeneratedCellDescriptor::canonical));
      productions.sort(Comparator.comparing(ProductionDescriptor::canonical));
      List<SortDescriptor> canonicalSorts =
          sorts.values().stream().sorted(Comparator.comparing(SortDescriptor::canonical)).toList();
      List<SubsortDescriptor> canonicalSubsorts =
          subsorts.values().stream().sorted(Comparator.comparing(SubsortDescriptor::canonical)).toList();
      String nonHash =
          sha256(
              replaceIdentity(
                  nonPrimary.toString(),
                  primarySource,
                  representedSource,
                  lineageSubstitutions));
      String fingerprint =
          sha256(
              replaceIdentity(
                      graph.toString(),
                      primarySource,
                      representedSource,
                      lineageSubstitutions)
                  + "|" + nonHash + "|"
                  + rules.values().stream().map(value -> value.content).sorted().collect(Collectors.joining("|")));
      return new RuleDefinitionState(
          fingerprint,
          nonHash,
          modules.size(),
          sentences,
          Map.copyOf(rules),
          List.copyOf(descriptors),
          List.copyOf(productions),
          canonicalSorts,
          canonicalSubsorts);
    }

    static Map<String, String> lineageSubstitutions(
        Definition definition, String primarySource, String representedSource) {
      Map<String, String> substitutions = new LinkedHashMap<>();
      for (Module module : stream(definition.modules()).toList()) {
        for (Rule rule :
            stream(module.localSentences())
                .filter(Rule.class::isInstance)
                .map(Rule.class::cast)
                .filter(
                    item ->
                        item.source().map(value -> value.source()).orElse("")
                            .equals(primarySource))
                .toList()) {
          substitutions.put(
              RuleState.lineage(module.name(), rule),
              RuleState.lineage(module.name(), rule, representedSource));
        }
      }
      return Map.copyOf(substitutions);
    }

    boolean isSubsort(SortDescriptor actual, SortDescriptor expected) {
      if (actual.equals(expected)) return true;
      // KItem is the universal item carrier at this post-CF seam; explicit
      // injections are added by the unchanged official lowering that follows.
      if (expected.name.equals("KItem")) return true;
      java.util.Set<SortDescriptor> seen = new java.util.HashSet<>();
      List<SortDescriptor> frontier = new ArrayList<>(List.of(actual));
      while (!frontier.isEmpty()) {
        SortDescriptor current = frontier.remove(frontier.size() - 1);
        if (!seen.add(current)) continue;
        for (SubsortDescriptor relation : subsorts) {
          if (relation.sub.equals(current)) {
            if (relation.sup.equals(expected)) return true;
            frontier.add(relation.sup);
          }
        }
      }
      return false;
    }
  }

  private record RuleState(
      String module,
      String label,
      String source,
      String location,
      String lineage,
      String content,
      String body,
      String requires,
      String ensures,
      String attributes) {
    static RuleState capture(String module, Rule rule) {
      String source = rule.source().map(value -> value.source()).orElse("");
      return capture(
          module,
          rule,
          source,
          source,
          Map.of(lineage(module, rule), lineage(module, rule)));
    }

    static RuleState capture(
        String module,
        Rule rule,
        String primarySource,
        String representedSource,
        Map<String, String> lineageSubstitutions) {
      String label = rule.label().orElse("");
      String source = representedSource;
      String location = rule.location().map(Object::toString).orElse("");
      String lineage = lineage(module, rule, representedSource);
      String body =
          sha256(
              Projection.encodeTerm(
                  rule.body(),
                  primarySource,
                  representedSource,
                  lineageSubstitutions));
      String requires =
          sha256(
              Projection.encodeTerm(
                  rule.requires(),
                  primarySource,
                  representedSource,
                  lineageSubstitutions));
      String ensures =
          sha256(
              Projection.encodeTerm(
                  rule.ensures(),
                  primarySource,
                  representedSource,
                  lineageSubstitutions));
      String attributes =
          sha256(
              replaceIdentity(
                  rule.att().toString(),
                  primarySource,
                  representedSource,
                  lineageSubstitutions));
      String content = sha256(lineage + "|" + body + "|" + requires + "|" + ensures + "|" + attributes);
      return new RuleState(module, label, source, location, lineage, content, body, requires, ensures, attributes);
    }

    static String lineage(String module, Rule rule) {
      return lineage(
          module, rule, rule.source().map(value -> value.source()).orElse(""));
    }

    static String lineage(String module, Rule rule, String representedSource) {
      return sha256(
          module + "|Rule|"
              + representedSource + "|"
              + rule.location().map(Object::toString).orElse("") + "|"
              + rule.label().orElse(""));
    }
  }

  private record ProductionDescriptor(
      String module,
      String label,
      SortDescriptor resultSort,
      List<SortDescriptor> argumentSorts,
      String productionFingerprint,
      String labelFingerprint,
      String metadataFingerprint,
      Production production) {
    static ProductionDescriptor capture(String module, Production production) {
      return capture(module, production, "", "");
    }

    static ProductionDescriptor capture(
        String module,
        Production production,
        String primarySource,
        String representedSource) {
      List<SortDescriptor> arguments = new ArrayList<>();
      for (int index = 0; index < production.arity(); index++) {
        arguments.add(SortDescriptor.capture(production.nonterminal(index).sort()));
      }
      String label = production.klabel().get().name();
      return new ProductionDescriptor(
          module,
          label,
          SortDescriptor.capture(production.sort()),
          List.copyOf(arguments),
          sha256(
              replaceIdentity(
                  productionStructure(production),
                  primarySource,
                  representedSource,
                  Map.of())),
          sha256(label),
          sha256(
              replaceIdentity(
                  production.att().toString(),
                  primarySource,
                  representedSource,
                  Map.of())),
          production);
    }

    String canonical() {
      return module + "|" + label + "|" + resultSort.canonical() + "|"
          + argumentSorts.stream().map(SortDescriptor::canonical).collect(Collectors.joining(","))
          + "|" + productionFingerprint + "|"
          + labelFingerprint + "|" + metadataFingerprint;
    }

    boolean matches(ProductionSpec spec) {
      return module.equals(spec.module)
          && label.equals(spec.label)
          && resultSort.matches(spec.resultSort)
          && argumentSorts.size() == spec.argumentSorts.size()
          && java.util.stream.IntStream.range(0, argumentSorts.size())
              .allMatch(index -> argumentSorts.get(index).matches(spec.argumentSorts.get(index)))
          && productionFingerprint.equals(spec.productionFingerprint)
          && labelFingerprint.equals(spec.labelFingerprint)
          && metadataFingerprint.equals(spec.metadataFingerprint);
    }
  }

  private record SortDescriptor(String name, String fingerprint, Sort sort) {
    static SortDescriptor capture(Sort sort) {
      String name = sort.toString();
      return new SortDescriptor(name, sha256(name), sort);
    }

    String canonical() { return name + "|" + fingerprint; }
    boolean matches(SortSpec spec) {
      return name.equals(spec.name) && fingerprint.equals(spec.fingerprint);
    }
  }

  private record SubsortDescriptor(
      SortDescriptor sub, SortDescriptor sup, String fingerprint) {
    static SubsortDescriptor capture(Sort sub, Sort sup) {
      SortDescriptor subDescriptor = SortDescriptor.capture(sub);
      SortDescriptor supDescriptor = SortDescriptor.capture(sup);
      return new SubsortDescriptor(
          subDescriptor,
          supDescriptor,
          sha256(subDescriptor.canonical() + "|" + supDescriptor.canonical()));
    }

    String canonical() { return sub.canonical() + "|" + sup.canonical() + "|" + fingerprint; }
  }

  private record GeneratedCellDescriptor(
      String module,
      String name,
      String label,
      Sort cellSort,
      Sort bodySort,
      SortDescriptor cellSortDescriptor,
      SortDescriptor bodySortDescriptor,
      String productionFingerprint,
      String labelFingerprint,
      String metadataFingerprint,
      Production production) {
    static GeneratedCellDescriptor capture(String module, String name, Production production) {
      return capture(module, name, production, "", "");
    }

    static GeneratedCellDescriptor capture(
        String module,
        String name,
        Production production,
        String primarySource,
        String representedSource) {
      String label = production.klabel().get().name();
      Sort bodySort = production.nonterminal(0).sort();
      return new GeneratedCellDescriptor(
          module,
          name,
          label,
          production.sort(),
          bodySort,
          SortDescriptor.capture(production.sort()),
          SortDescriptor.capture(bodySort),
          sha256(
              replaceIdentity(
                  productionStructure(production),
                  primarySource,
                  representedSource,
                  Map.of())),
          sha256(label),
          sha256(
              replaceIdentity(
                  production.att().toString(),
                  primarySource,
                  representedSource,
                  Map.of())),
          production);
    }

    String canonical() {
      return module + "|" + name + "|" + label + "|" + cellSort + "|" + bodySort
          + "|" + productionFingerprint + "|" + labelFingerprint + "|" + metadataFingerprint;
    }

    boolean matches(GeneratedCellSpec spec) {
      return module.equals(spec.module)
          && name.equals(spec.name)
          && label.equals(spec.label)
          && cellSortDescriptor.matches(spec.cellSort)
          && bodySortDescriptor.matches(spec.bodySort)
          && productionFingerprint.equals(spec.productionFingerprint)
          && labelFingerprint.equals(spec.labelFingerprint)
          && metadataFingerprint.equals(spec.metadataFingerprint);
    }
  }

  private static final class Trace {
    final String mode;
    final Path recordPath;
    final Path traceDefinition;
    final Path configurationDefinition;
    final String primarySource;
    final String portableSource;
    final TraceConfigurationAugmentation configuration;
    String status = "running", classification = "", error = "";
    int postCfInvocations;
    boolean postCfSameReference, cfConstructed, backendConstructed;
    String ruleBeforeDefinition = "", ruleAfterDefinition = "";
    String ruleRequestFingerprintPass1 = "", ruleRequestFingerprintPass2 = "";
    String ruleResponseFingerprintPass1 = "", ruleResponseFingerprintPass2 = "";
    String ruleStatusPass1 = "", ruleStatusPass2 = "";
    String ruleTargetLineage = "", ruleTargetContentBefore = "", ruleTargetContentAfter = "";
    String ruleTargetBodyBefore = "", ruleTargetBodyAfter = "";
    String ruleTargetModule = "", ruleTargetLabel = "", ruleTargetSource = "", ruleTargetLocation = "";
    String ruleTargetRequires = "", ruleTargetEnsures = "", ruleTargetAttributes = "";
    String ruleOperationCanonicalPass1 = "", ruleOperationCanonicalPass2 = "";
    String ruleResultCanonicalFingerprintPass1 = "", ruleResultCanonicalFingerprintPass2 = "";
    String generatedCellName = "", generatedCellLabel = "", generatedCellSort = "";
    String generatedCellBodySort = "", generatedCellProductionFingerprint = "";
    String generatedCellMetadataFingerprint = "";
    String portableRuleBeforeDefinition = "", portableRuleAfterDefinition = "";
    String portableRuleRequestFingerprintPass1 = "", portableRuleRequestFingerprintPass2 = "";
    String portableRuleResponseFingerprintPass1 = "", portableRuleResponseFingerprintPass2 = "";
    String portableRuleTargetLineage = "", portableRuleTargetContentBefore = "";
    String portableRuleTargetContentAfter = "", portableRuleTargetBodyBefore = "";
    String portableRuleTargetBodyAfter = "", portableRuleTargetModule = "";
    String portableRuleTargetLabel = "", portableRuleTargetSource = "";
    String portableRuleTargetLocation = "", portableRuleTargetRequires = "";
    String portableRuleTargetEnsures = "", portableRuleTargetAttributes = "";
    String portableRuleOperationCanonicalPass1 = "", portableRuleOperationCanonicalPass2 = "";
    String portableRuleResultCanonicalFingerprintPass1 = "";
    String portableRuleResultCanonicalFingerprintPass2 = "";
    String portableGeneratedCellProductionFingerprint = "";
    String portableGeneratedCellMetadataFingerprint = "";
    int ruleKInvocationsPass1, ruleKInvocationsPass2;
    int ruleCandidateCountPass1, ruleCandidateCountPass2;
    int ruleValidatedOperationCount, ruleApplicationCount, ruleChangedRuleCount;
    int ruleTransformerTraversalCount;
    int ruleAlreadyPresentValidatedCount, ruleInputMutationCount;
    int pairTransactionInvocationCount;
    String mutationStructuralField = "", mutationBeforeFingerprint = "";
    String mutationAfterFingerprint = "", mutationFingerprint = "";
    String mutationProjectionSchema = "", mutationChangedFieldPaths = "";
    String mutationStructuralOperation = "";
    String mutationFieldBeforeFingerprint = "", mutationFieldAfterFingerprint = "";
    String mutationBeforeStructure = "", mutationAfterStructure = "";
    String mutationBeforeProjectionFingerprintMap = "";
    String mutationAfterProjectionFingerprintMap = "";
    String mutationReferenceFragmentFingerprint = "";
    int mutationMemberIndex = -1;
    boolean mutationKConflictBeforePairTransaction, mutationHostIndependentRejection;
    boolean mutationProductionMutatorBound;
    boolean ruleSecondSameReference, ruleTransformedDefinitionReturned;
    String pairCall1Status = "", pairCall2Status = "";
    int pairCall1ValidationCount, pairCall2ValidationCount;
    int pairCall1ApplicationCount, pairCall2ApplicationCount;
    int pairCall1TraversalCount, pairCall2TraversalCount;
    int pairCall1InputIdentity, pairCall2InputIdentity;
    int pairCall1OutputIdentity, pairCall2OutputIdentity;
    boolean pairCall1SameReference, pairCall2SameReference;
    boolean pairCall1OutputDefinitionConstructed, pairCall2OutputDefinitionConstructed;
    boolean ruleIdentityPreserved, ruleProvenancePreserved, ruleAttributesPreserved;
    boolean ruleConditionsPreserved, ruleOriginalNodesPreserved, portableEvidenceProjected;
    boolean portableRuleOrderingValidated, portableTermMetadataRederived;
    TraceOutcome currentTraceResult;

    Trace(
        String mode,
        Path recordPath,
        Path traceDefinition,
        Path configurationDefinition,
        String primarySource,
        String portableSource) {
      this.mode = mode;
      this.recordPath = recordPath;
      this.traceDefinition = traceDefinition;
      this.configurationDefinition = configurationDefinition;
      this.primarySource = primarySource;
      this.portableSource = portableSource;
      this.configuration =
          new TraceConfigurationAugmentation(
              mode, configurationDefinition, recordPath, primarySource, portableSource);
    }
    void recordPairCall(int index, PairCall call) {
      if (index == 1) {
        pairCall1Status = call.status;
        pairCall1ValidationCount = call.validationCount;
        pairCall1ApplicationCount = call.applicationCount;
        pairCall1TraversalCount = call.traversalCount;
        pairCall1InputIdentity = call.inputIdentity;
        pairCall1OutputIdentity = call.outputIdentity;
        pairCall1SameReference = call.sameReference;
        pairCall1OutputDefinitionConstructed = call.outputDefinitionConstructed;
      } else if (index == 2) {
        pairCall2Status = call.status;
        pairCall2ValidationCount = call.validationCount;
        pairCall2ApplicationCount = call.applicationCount;
        pairCall2TraversalCount = call.traversalCount;
        pairCall2InputIdentity = call.inputIdentity;
        pairCall2OutputIdentity = call.outputIdentity;
        pairCall2SameReference = call.sameReference;
        pairCall2OutputDefinitionConstructed = call.outputDefinitionConstructed;
      } else {
        throw new AssertionError("pair call index must be one or two");
      }
    }
    void write() {
      try { Files.createDirectories(recordPath.getParent()); Files.writeString(recordPath, json(), StandardCharsets.UTF_8); } catch (IOException e) { throw KEMException.criticalError("cannot write R3-G-05 record", e); }
    }
    String json() {
      Map<String,Object> fields = new LinkedHashMap<>();
      fields.put("schemaVersion", 1);
      fields.put("contract", TRACE_SCHEMA);
      fields.put("postCfAdapter", POST_CF);
      fields.put("mode", mode);
      fields.put("status", status);
      fields.put("classification", classification);
      fields.put("error", error);
      configuration.metrics.putJson(fields);
      fields.put("postCfAdapterInvocations", postCfInvocations);
      fields.put("postCfConstructed", cfConstructed);
      fields.put("ruleKInvocationsPass1", ruleKInvocationsPass1);
      fields.put("ruleKInvocationsPass2", ruleKInvocationsPass2);
      fields.put("ruleRequestFingerprintPass1", ruleRequestFingerprintPass1);
      fields.put("ruleResponseFingerprintPass1", ruleResponseFingerprintPass1);
      fields.put("ruleCandidateCountPass1", ruleCandidateCountPass1);
      fields.put("ruleStatusPass1", ruleStatusPass1);
      fields.put("ruleRequestFingerprintPass2", ruleRequestFingerprintPass2);
      fields.put("ruleResponseFingerprintPass2", ruleResponseFingerprintPass2);
      fields.put("ruleCandidateCountPass2", ruleCandidateCountPass2);
      fields.put("ruleStatusPass2", ruleStatusPass2);
      fields.put("ruleTargetLineage", ruleTargetLineage);
      fields.put("ruleTargetContentBefore", ruleTargetContentBefore);
      fields.put("ruleTargetContentAfter", ruleTargetContentAfter);
      fields.put("ruleTargetBodyBefore", ruleTargetBodyBefore);
      fields.put("ruleTargetBodyAfter", ruleTargetBodyAfter);
      fields.put("ruleTargetModule", ruleTargetModule);
      fields.put("ruleTargetLabel", ruleTargetLabel);
      fields.put("ruleTargetSource", ruleTargetSource);
      fields.put("ruleTargetLocation", ruleTargetLocation);
      fields.put("ruleTargetRequires", ruleTargetRequires);
      fields.put("ruleTargetEnsures", ruleTargetEnsures);
      fields.put("ruleTargetAttributes", ruleTargetAttributes);
      fields.put("ruleOperationCanonicalPass1", ruleOperationCanonicalPass1);
      fields.put("ruleOperationCanonicalPass2", ruleOperationCanonicalPass2);
      fields.put("ruleResultCanonicalFingerprintPass1", ruleResultCanonicalFingerprintPass1);
      fields.put("ruleResultCanonicalFingerprintPass2", ruleResultCanonicalFingerprintPass2);
      fields.put("ruleValidatedOperationCount", ruleValidatedOperationCount);
      fields.put("ruleApplicationCount", ruleApplicationCount);
      fields.put("ruleChangedRuleCount", ruleChangedRuleCount);
      fields.put("ruleTransformerTraversalCount", ruleTransformerTraversalCount);
      fields.put("ruleAlreadyPresentValidatedCount", ruleAlreadyPresentValidatedCount);
      fields.put("ruleInputMutationCount", ruleInputMutationCount);
      fields.put("pairTransactionInvocationCount", pairTransactionInvocationCount);
      fields.put("mutationStructuralField", mutationStructuralField);
      fields.put("mutationMemberIndex", mutationMemberIndex);
      fields.put("mutationProjectionSchema", mutationProjectionSchema);
      fields.put("mutationStructuralOperation", mutationStructuralOperation);
      fields.put("mutationChangedFieldPaths", mutationChangedFieldPaths);
      fields.put("mutationBeforeStructure", mutationBeforeStructure);
      fields.put("mutationAfterStructure", mutationAfterStructure);
      fields.put("mutationBeforeProjectionFingerprintMap",
          mutationBeforeProjectionFingerprintMap);
      fields.put("mutationAfterProjectionFingerprintMap",
          mutationAfterProjectionFingerprintMap);
      fields.put("mutationReferenceFragmentFingerprint",
          mutationReferenceFragmentFingerprint);
      fields.put("mutationFieldBeforeFingerprint", mutationFieldBeforeFingerprint);
      fields.put("mutationFieldAfterFingerprint", mutationFieldAfterFingerprint);
      fields.put("mutationBeforeFingerprint", mutationBeforeFingerprint);
      fields.put("mutationAfterFingerprint", mutationAfterFingerprint);
      fields.put("mutationFingerprint", mutationFingerprint);
      fields.put("mutationProductionMutatorBound", mutationProductionMutatorBound);
      fields.put("mutationKConflictBeforePairTransaction",
          mutationKConflictBeforePairTransaction);
      fields.put("mutationHostIndependentRejection",
          mutationHostIndependentRejection);
      fields.put("pairCall1Status", pairCall1Status);
      fields.put("pairCall1ValidationCount", pairCall1ValidationCount);
      fields.put("pairCall1ApplicationCount", pairCall1ApplicationCount);
      fields.put("pairCall1TransformerTraversalCount", pairCall1TraversalCount);
      fields.put("pairCall1InputIdentity", pairCall1InputIdentity);
      fields.put("pairCall1OutputIdentity", pairCall1OutputIdentity);
      fields.put("pairCall1SameReference", pairCall1SameReference);
      fields.put("pairCall1OutputDefinitionConstructed", pairCall1OutputDefinitionConstructed);
      fields.put("pairCall2Status", pairCall2Status);
      fields.put("pairCall2ValidationCount", pairCall2ValidationCount);
      fields.put("pairCall2ApplicationCount", pairCall2ApplicationCount);
      fields.put("pairCall2TransformerTraversalCount", pairCall2TraversalCount);
      fields.put("pairCall2InputIdentity", pairCall2InputIdentity);
      fields.put("pairCall2OutputIdentity", pairCall2OutputIdentity);
      fields.put("pairCall2SameReference", pairCall2SameReference);
      fields.put("pairCall2OutputDefinitionConstructed", pairCall2OutputDefinitionConstructed);
      fields.put("outputDefinitionConstructed",
          pairCall1OutputDefinitionConstructed || pairCall2OutputDefinitionConstructed);
      fields.put("ruleSecondSameReference", ruleSecondSameReference);
      fields.put("ruleIdentityPreserved", ruleIdentityPreserved);
      fields.put("ruleProvenancePreserved", ruleProvenancePreserved);
      fields.put("ruleAttributesPreserved", ruleAttributesPreserved);
      fields.put("ruleConditionsPreserved", ruleConditionsPreserved);
      fields.put("rule" + "OriginalNodesPreserved", ruleOriginalNodesPreserved);
      fields.put("ruleBeforeDefinition", ruleBeforeDefinition);
      fields.put("ruleAfterDefinition", ruleAfterDefinition);
      fields.put("ruleTransformedDefinitionReturned", ruleTransformedDefinitionReturned);
      fields.put("ruleSecondPassSameReference", postCfSameReference);
      fields.put("generatedCellName", generatedCellName);
      fields.put("generatedCellLabel", generatedCellLabel);
      fields.put("generatedCellSort", generatedCellSort);
      fields.put("generatedCellBodySort", generatedCellBodySort);
      fields.put("generatedCellProductionFingerprint", generatedCellProductionFingerprint);
      fields.put("generatedCellMetadataFingerprint", generatedCellMetadataFingerprint);
      fields.put("portableEvidenceProjected", portableEvidenceProjected);
      fields.put("portableRuleOrderingValidated", portableRuleOrderingValidated);
      fields.put("portableTermMetadataRederived", portableTermMetadataRederived);
      fields.put("portableSource", portableSource);
      fields.put("portableRuleRequestFingerprintPass1", portableRuleRequestFingerprintPass1);
      fields.put("portableRuleResponseFingerprintPass1", portableRuleResponseFingerprintPass1);
      fields.put("portableRuleRequestFingerprintPass2", portableRuleRequestFingerprintPass2);
      fields.put("portableRuleResponseFingerprintPass2", portableRuleResponseFingerprintPass2);
      fields.put("portableRuleTargetLineage", portableRuleTargetLineage);
      fields.put("portableRuleTargetContentBefore", portableRuleTargetContentBefore);
      fields.put("portableRuleTargetContentAfter", portableRuleTargetContentAfter);
      fields.put("portableRuleTargetBodyBefore", portableRuleTargetBodyBefore);
      fields.put("portableRuleTargetBodyAfter", portableRuleTargetBodyAfter);
      fields.put("portableRuleTargetModule", portableRuleTargetModule);
      fields.put("portableRuleTargetLabel", portableRuleTargetLabel);
      fields.put("portableRuleTargetSource", portableRuleTargetSource);
      fields.put("portableRuleTargetLocation", portableRuleTargetLocation);
      fields.put("portableRuleTargetRequires", portableRuleTargetRequires);
      fields.put("portableRuleTargetEnsures", portableRuleTargetEnsures);
      fields.put("portableRuleTargetAttributes", portableRuleTargetAttributes);
      fields.put("portableRuleOperationCanonicalPass1", portableRuleOperationCanonicalPass1);
      fields.put("portableRuleOperationCanonicalPass2", portableRuleOperationCanonicalPass2);
      fields.put("portableRuleResultCanonicalFingerprintPass1", portableRuleResultCanonicalFingerprintPass1);
      fields.put("portableRuleResultCanonicalFingerprintPass2", portableRuleResultCanonicalFingerprintPass2);
      fields.put("portableRuleBeforeDefinition", portableRuleBeforeDefinition);
      fields.put("portableRuleAfterDefinition", portableRuleAfterDefinition);
      fields.put("portableGeneratedCellProductionFingerprint", portableGeneratedCellProductionFingerprint);
      fields.put("portableGeneratedCellMetadataFingerprint", portableGeneratedCellMetadataFingerprint);
      fields.put("backendConstructed", backendConstructed);
      StringBuilder result = new StringBuilder("{\n"); int index=0; for (var item: fields.entrySet()) { result.append("  ").append(quoteJson(item.getKey())).append(": "); Object v=item.getValue(); if (v instanceof String s) result.append(quoteJson(s)); else result.append(v); result.append(++index == fields.size() ? "\n" : ",\n"); } return result.append("}\n").toString();
    }
  }

  private static String runK(String program, Path definition, Path recordPath) {
    try {
      Path parent = recordPath.getParent(); Files.createDirectories(parent); Path file = Files.createTempFile(parent, "trace-", ".kink");
      try { Files.writeString(file, program, StandardCharsets.UTF_8); RunProcess.ProcessOutput output = RunProcess.execute(Map.of("LC_ALL","C","LANG","C","TZ","UTC"), new ProcessBuilder(), "krun", file.toString(), "--definition", definition.toString(), "--output", "pretty"); String stderr = new String(output.stderr(), StandardCharsets.UTF_8); if (output.exitCode()!=0) throw reject("k-selection-failure", "K execution failed: " + stderr.strip()); return new String(output.stdout(), StandardCharsets.UTF_8); } finally { Files.deleteIfExists(file); }
    } catch (IOException e) { throw KEMException.criticalError("cannot invoke K augmentation", e); }
  }

  private static String required(String name) { String value=System.getenv(name); if (value==null || value.isBlank()) throw KEMException.criticalError("missing environment " + name); return value; }
  private static String canonical(File file) { try { return file.getCanonicalPath(); } catch (IOException e) { throw KEMException.criticalError("cannot canonicalize definition file", e); } }
  private static ValidationException reject(String classification, String message) { return new ValidationException(classification + ": " + message); }
  private static void require(boolean condition, String message) { if (!condition) throw new ValidationException(message); }
  private static String replaceIdentity(
      String value,
      String primarySource,
      String representedSource,
      Map<String, String> lineageSubstitutions) {
    Map<String, String> substitutions = new LinkedHashMap<>();
    for (var substitution : lineageSubstitutions.entrySet()) {
      if (!substitution.getKey().equals(substitution.getValue())) {
        substitutions.put(substitution.getKey(), substitution.getValue());
      }
    }
    if (!primarySource.equals(representedSource)) {
      require(
          !substitutions.containsKey(primarySource),
          "portable identity substitution domain was duplicated");
      substitutions.put(primarySource, representedSource);
    }
    if (substitutions.isEmpty()) return value;
    require(
        new java.util.HashSet<>(substitutions.values()).size() == substitutions.size(),
        "portable identity substitution range was duplicated");
    for (String range : substitutions.values()) {
      for (String domain : substitutions.keySet()) {
        require(
            !range.contains(domain),
            "portable identity substitution range contained a raw domain");
      }
    }
    List<String> domains =
        substitutions.keySet().stream()
            .sorted(
                Comparator.comparingInt(String::length)
                    .reversed()
                    .thenComparing(Function.identity()))
            .toList();
    StringBuilder result = new StringBuilder();
    int offset = 0;
    while (offset < value.length()) {
      int currentOffset = offset;
      List<String> matches =
          domains.stream()
              .filter(domain -> value.startsWith(domain, currentOffset))
              .toList();
      require(matches.size() <= 1, "portable identity substitution domains overlapped");
      if (matches.isEmpty()) {
        result.append(value.charAt(offset++));
      } else {
        String domain = matches.get(0);
        result.append(substitutions.get(domain));
        offset += domain.length();
      }
    }
    String projected = result.toString();
    for (String domain : domains) {
      require(
          !projected.contains(domain),
          "portable identity projection retained a raw domain");
    }
    return projected;
  }

  private static TraceResult portableResult(
      TraceResult rawResult,
      RuleDefinitionState raw,
      RuleDefinitionState portable,
      String primarySource,
      String representedSource) {
    List<TraceMember> members = rawResult.members.stream()
        .map(member -> portableMember(
            member, raw, portable, primarySource, representedSource))
        .toList();
    TraceResult result = new TraceResult(
        rawResult.schema, rawResult.transformation, portable.fingerprint,
        rawResult.candidateCount, rawResult.status,
        new ResultIdentity(
            rawResult.schema, rawResult.transformation, portable.fingerprint,
            rawResult.candidateCount, rawResult.status, members.get(0), members.get(1)),
        members);
    String canonical = result.canonical();
    require(!canonical.contains(primarySource), "portable result retained the raw source");
    for (String lineage : raw.primaryRules.keySet()) {
      require(!canonical.contains(lineage), "portable result retained a raw lineage");
    }
    return result;
  }

  private static TraceMember portableMember(
      TraceMember rawResult,
      RuleDefinitionState raw,
      RuleDefinitionState portable,
      String primarySource,
      String representedSource) {
    List<RuleState> targets =
        portable.primaryRules.values().stream()
            .filter(
                item ->
                    item.module.equals(rawResult.module)
                        && item.label.equals(rawResult.label)
                        && item.location.equals(rawResult.location))
            .toList();
    require(targets.size() == 1, "portable result target mapping was not unique");
    RuleState target = targets.get(0);
    return new TraceMember(
            target.lineage,
            target.content,
            target.body,
            target.requires,
            target.ensures,
            target.attributes,
            target.module,
            target.label,
            target.source,
            target.location,
            rawResult.parentPath,
            rawResult.name,
            rawResult.variable,
            portableSort(rawResult.variableSort, raw, portable),
            portableTerm(
                rawResult.beforeTerm, raw, portable, primarySource, representedSource),
            portableTerm(
                rawResult.afterTerm, raw, portable, primarySource, representedSource),
            rawResult.witness,
            portableAuthority(
                rawResult.authority, raw, portable, primarySource, representedSource));
  }

  private static OperationAuthority portableAuthority(
      OperationAuthority rawAuthority,
      RuleDefinitionState raw,
      RuleDefinitionState portable,
      String primarySource,
      String representedSource) {
    List<GeneratedCellDescriptor> cells = portable.descriptors.stream()
        .filter(item -> item.name.equals(rawAuthority.generatedCell.name)
            && item.label.equals(rawAuthority.generatedCell.label))
        .toList();
    require(cells.size() == 1, "portable generated-cell authority mapping was not unique");
    GeneratedCellDescriptor cell = cells.get(0);
    GeneratedCellSpec generated = new GeneratedCellSpec(
        cell.module, cell.name, cell.label,
        new SortSpec(cell.cellSortDescriptor.name, cell.cellSortDescriptor.fingerprint),
        new SortSpec(cell.bodySortDescriptor.name, cell.bodySortDescriptor.fingerprint),
        cell.productionFingerprint, cell.labelFingerprint, cell.metadataFingerprint);
    return new OperationAuthority(
        generated,
        portableProduction(rawAuthority.parentProduction, raw, portable),
        portableProduction(rawAuthority.cellProduction, raw, portable),
        portableProduction(rawAuthority.leftMarkerProduction, raw, portable),
        portableProduction(rawAuthority.rightMarkerProduction, raw, portable),
        portableProduction(rawAuthority.appendProduction, raw, portable),
        portableProduction(rawAuthority.singletonProduction, raw, portable),
        portableProduction(rawAuthority.eventProduction, raw, portable),
        portableProduction(rawAuthority.originProduction, raw, portable),
        portableTerm(rawAuthority.leftMarkerTerm, raw, portable, primarySource, representedSource),
        portableTerm(rawAuthority.rightMarkerTerm, raw, portable, primarySource, representedSource),
        TraceProjection.termMetadataAuthority(portable));
  }

  private static TermSpec portableTerm(
      TermSpec rawTerm,
      RuleDefinitionState raw,
      RuleDefinitionState portable,
      String primarySource,
      String representedSource) {
    if (rawTerm instanceof VariableSpec variable) {
      return new VariableSpec(variable.name, portableSort(variable.sort, raw, portable));
    }
    if (rawTerm instanceof TokenSpec token) {
      String value = token.value;
      if (value.equals(primarySource)) {
        value = representedSource;
      } else if (raw.primaryRules.containsKey(value)) {
        RuleState rawRule = raw.primaryRules.get(value);
        List<RuleState> matches =
            portable.primaryRules.values().stream()
                .filter(
                    item ->
                        item.module.equals(rawRule.module)
                            && item.label.equals(rawRule.label)
                            && item.location.equals(rawRule.location))
                .toList();
        require(matches.size() == 1, "portable token lineage mapping was not unique");
        value = matches.get(0).lineage;
      }
      String lexeme =
          value.equals(token.value) ? token.lexeme : StringUtil.enquoteKString(value);
      require(
          !value.contains(primarySource) && !lexeme.contains(primarySource),
          "portable token retained the raw source");
      return new TokenSpec(portableSort(token.sort, raw, portable), value, lexeme);
    }
    ApplySpec application = (ApplySpec) rawTerm;
    return new ApplySpec(
        portableProduction(application.production, raw, portable),
        application.arguments.stream()
            .map(
                item ->
                    portableTerm(
                        item, raw, portable, primarySource, representedSource))
            .toList());
  }

  private static SortSpec portableSort(
      SortSpec rawSort, RuleDefinitionState raw, RuleDefinitionState portable) {
    List<SortDescriptor> rawMatches =
        raw.sorts.stream().filter(item -> item.matches(rawSort)).toList();
    require(rawMatches.size() == 1, "portable sort source mapping was not unique");
    List<SortDescriptor> portableMatches =
        portable.sorts.stream()
            .filter(item -> item.name.equals(rawMatches.get(0).name))
            .toList();
    require(portableMatches.size() == 1, "portable sort target mapping was not unique");
    SortDescriptor descriptor = portableMatches.get(0);
    return new SortSpec(descriptor.name, descriptor.fingerprint);
  }

  private static ProductionSpec portableProduction(
      ProductionSpec rawSpec,
      RuleDefinitionState raw,
      RuleDefinitionState portable) {
    List<ProductionDescriptor> rawMatches =
        raw.productions.stream().filter(item -> item.matches(rawSpec)).toList();
    require(rawMatches.size() == 1, "portable production source mapping was not unique");
    List<ProductionDescriptor> portableMatches =
        portable.productions.stream()
            .filter(item -> item.production == rawMatches.get(0).production)
            .toList();
    require(portableMatches.size() == 1, "portable production target mapping was not unique");
    ProductionDescriptor descriptor = portableMatches.get(0);
    return new ProductionSpec(
        descriptor.module,
        descriptor.label,
        new SortSpec(descriptor.resultSort.name, descriptor.resultSort.fingerprint),
        descriptor.argumentSorts.stream()
            .map(item -> new SortSpec(item.name, item.fingerprint))
            .toList(),
        descriptor.productionFingerprint,
        descriptor.labelFingerprint,
        descriptor.metadataFingerprint);
  }
  private static String quote(String value) { return StringUtil.enquoteKString(value); }
  private static String quoteJson(String value) { return "\"" + value.replace("\\","\\\\").replace("\"","\\\"").replace("\n","\\n").replace("\r","\\r") + "\""; }
  private static String sha256(String value) { try { byte[] digest=MessageDigest.getInstance("SHA-256").digest(value.getBytes(StandardCharsets.UTF_8)); StringBuilder out=new StringBuilder(); for(byte item:digest) out.append(String.format(Locale.ROOT,"%02x",item)); return out.toString(); } catch(NoSuchAlgorithmException e){ throw new AssertionError(e); } }
  private static final class ValidationException extends RuntimeException { ValidationException(String message){super(message);} }
}
