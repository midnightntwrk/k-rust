package org.kframework.kink.trace;

import static org.kframework.Collections.immutable;
import static org.kframework.Collections.stream;
import static org.kframework.definition.Constructors.Module;
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

/** Trusted-small post-CF host for KRuleAppliedTrace-v1. */
public final class RuleAppliedTraceDriver {
  private static final String MODE_ENV = "R3_G_01_MODE";
  private static final String RECORD_ENV = "R3_G_01_RECORD";
  private static final String TRACE_DEFINITION_ENV = "R3_G_01_TRACE_K_DEFINITION";
  private static final String PORTABLE_SOURCE_ENV = "R3_G_01_PORTABLE_SOURCE";
  private static final String TRACE_SCHEMA = "KRuleAppliedTrace-v1";
  private static final String TRACE_TRANSFORMATION = "p3-trace-bump-rule-applied@1";
  private static final String POST_CF = "OfficialDefinitionAdapter-v1";

  private RuleAppliedTraceDriver() {}

  public static void main(String[] args) {
    if (args.length == 1 && args[0].equals("--parser-self-test")) {
      TraceResultParser.selfTest();
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
              canonical(definitionFile),
              required(PORTABLE_SOURCE_ENV));
      try {
        require(definitionFile.isFile(), "definition file does not exist");
        require(Files.isRegularFile(trace.traceDefinition.resolve("mainModule.txt")), "invalid K trace definition");
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
                Function.identity(),
                post,
                backend.excludedModuleTags());
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

  private static final class TraceAdapter {
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
        if (trace.mode.equals("conflict-existing")) return conflictNegative(input, before);
        if (trace.mode.equals("unsupported-shape")) return unsupportedShapeNegative(input, before);
        String kMode =
            switch (trace.mode) {
              case "positive-a", "positive-b", "missing-cell-metadata", "ambiguous-cell-metadata",
                  "missing-constructor-metadata", "ambiguous-constructor-metadata" -> "apply";
              case "stale-target-content" -> "stale-target-content";
              case "stale-target-provenance" -> "stale-target-provenance";
              case "zero-target" -> "zero-target";
              case "duplicate-target" -> "duplicate-target";
              case "unsupported-path" -> "unsupported-path";
              case "false-already-present" -> "false-already-present";
              case "unknown-constructor" -> "unknown-constructor";
              case "sort-invalid" -> "sort-invalid";
              case "variable-collision" -> "variable-collision";
              default -> throw reject("result-envelope-validation", "unsupported trace mode");
            };
        TraceInvocation first = invokeTraceK(input, before, kMode, 1);
        TraceResult result = requireTraceResult(first, before);
        if (!result.status.equals("apply")) {
          validateTraceAlreadyPresent(input, before, result);
          throw reject("result-envelope-validation", "first trace pass claimed already-present");
        }
        PreparedTrace prepared = prepareTrace(input, before, result);
        Definition output = applyTrace(input, prepared, prepared.before.term, prepared.after.term);
        trace.ruleApplicationCount = 1;
        trace.ruleValidatedOperationCount = 1;
        validateTraceApplied(input, output, before, result, prepared);
        RuleDefinitionState after = RuleDefinitionState.capture(output, trace.primarySource);
        trace.ruleAfterDefinition = after.fingerprint;

        TraceInvocation second = invokeTraceK(output, after, "apply", 2);
        TraceResult already = requireTraceResult(second, after);
        require(already.status.equals("already-present"), "second trace pass did not report already-present");
        require(already.lineage.equals(result.lineage), "trace target lineage changed across passes");
        validateTraceAlreadyPresent(output, after, already);
        capturePortableEvidence(input, output, before, after, result, already);
        trace.ruleSecondSameReference = true;
        trace.ruleTransformedDefinitionReturned = true;
        trace.postCfSameReference = true;
        return output;
      } catch (ValidationException e) {
        if (trace.classification.isEmpty() && e.getMessage().contains(":")) {
          trace.classification = e.getMessage().substring(0, e.getMessage().indexOf(':'));
        }
        if (trace.error.isEmpty()) trace.error = e.getMessage();
        throw KEMException.compilerError("R3-G-01 rule trace failed: " + e.getMessage());
      }
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
      List<RuleState> portableTargets =
          portableBefore.primaryRules.values().stream()
              .filter(
                  item ->
                      item.module.equals(rawPass1.module)
                          && item.label.equals(rawPass1.label)
                          && item.location.equals(rawPass1.location))
              .toList();
      require(portableTargets.size() == 1, "portable target projection was not unique");
      RuleState portableTarget = portableTargets.get(0);
      RuleState portableTargetAfter = portableAfter.primaryRules.get(portableTarget.lineage);
      require(portableTargetAfter != null, "portable target lineage changed across projections");
      RuleState rawTarget = rawBefore.primaryRules.get(rawPass1.lineage);
      require(rawTarget != null, "raw target disappeared before portable projection");
      require(
          !portableTarget.body.equals(rawTarget.body)
              && !portableTarget.requires.equals(rawTarget.requires)
              && !portableTarget.ensures.equals(rawTarget.ensures),
          "portable typed term metadata hashes were not independently rederived");
      require(
          TraceProjection.hasPortableRuleOrdering(
              input, trace.primarySource, trace.portableSource)
              && TraceProjection.hasPortableRuleOrdering(
                  output, trace.primarySource, trace.portableSource),
          "portable request rules were not ordered by portable identity");

      TraceResult portablePass1 =
          portableResult(
              rawPass1,
              rawBefore,
              portableBefore,
              trace.primarySource,
              trace.portableSource);
      TraceResult portablePass2 =
          portableResult(
              rawPass2,
              rawAfter,
              portableAfter,
              trace.primarySource,
              trace.portableSource);

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
      trace.portableRuleOperationCanonicalPass1 =
          portablePass1.operationCanonical();
      trace.portableRuleOperationCanonicalPass2 =
          portablePass2.operationCanonical();
      trace.portableRuleResponseFingerprintPass1 =
          sha256(portablePass1.canonical());
      trace.portableRuleResponseFingerprintPass2 =
          sha256(portablePass2.canonical());
      trace.portableRuleResultCanonicalFingerprintPass1 =
          trace.portableRuleResponseFingerprintPass1;
      trace.portableRuleResultCanonicalFingerprintPass2 =
          trace.portableRuleResponseFingerprintPass2;
      trace.portableRuleTargetLineage = portableTarget.lineage;
      trace.portableRuleTargetModule = portableTarget.module;
      trace.portableRuleTargetLabel = portableTarget.label;
      trace.portableRuleTargetSource = portableTarget.source;
      trace.portableRuleTargetLocation = portableTarget.location;
      trace.portableRuleTargetRequires = portableTarget.requires;
      trace.portableRuleTargetEnsures = portableTarget.ensures;
      trace.portableRuleTargetAttributes = portableTarget.attributes;
      trace.portableRuleTargetContentBefore = portableTarget.content;
      trace.portableRuleTargetContentAfter = portableTargetAfter.content;
      trace.portableRuleTargetBodyBefore = portableTarget.body;
      trace.portableRuleTargetBodyAfter = portableTargetAfter.body;

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

    private Definition conflictNegative(Definition input, RuleDefinitionState before) {
      TraceInvocation declaration = invokeTraceK(input, before, "apply", 1);
      TraceResult result = requireTraceResult(declaration, before);
      PreparedTrace prepared = prepareTrace(input, before, result);
      Definition conflicting = applyTrace(input, prepared, prepared.before.term, prepared.before.term);
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

    private Definition unsupportedShapeNegative(
        Definition input, RuleDefinitionState before) {
      TraceInvocation declaration = invokeTraceK(input, before, "apply", 1);
      TraceResult result = requireTraceResult(declaration, before);
      LocatedRule located = locateRule(input, trace.primarySource, result.lineage);
      if (located == null) throw reject("stale-precondition", "declared rule disappeared");
      K declaredParent;
      try {
        declaredParent = resolvePath(located.rule.body(), result.parentPath);
      } catch (ValidationException e) {
        throw reject("path-operation", e.getMessage());
      }
      if (!(declaredParent instanceof KApply parent)
          || !parent.klabel().name().equals("#cells")) {
        throw reject("path-operation", "declared original parent was not a cell bag");
      }
      K unsupported =
          org.kframework.kore.KORE.KSequence(parent.klist().items(), parent.att());
      K newBody = replacePath(located.rule.body(), result.parentPath, unsupported);
      Definition mutated = replaceRuleBody(input, located, newBody, "R3-G-01 unsupported-shape input mutation");
      trace.ruleInputMutationCount = 1;
      RuleDefinitionState mutatedState = RuleDefinitionState.capture(mutated, trace.primarySource);
      TraceInvocation selected = invokeTraceK(mutated, mutatedState, "apply", 2);
      TraceResult unsupportedResult = requireTraceResult(selected, mutatedState);
      prepareTrace(mutated, mutatedState, unsupportedResult);
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
                && !failure.reason.equals("conflicting-existing-state"))) {
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
          || result.candidateCount != 1
          || (!result.status.equals("apply") && !result.status.equals("already-present"))) {
        throw reject("envelope", "invalid K trace result envelope");
      }
      if (!result.definitionFingerprint.equals(state.fingerprint)) {
        throw reject("stale-precondition", "stale post-CF definition fingerprint");
      }
      RuleState target = state.primaryRules.get(result.lineage);
      if (target == null
          || !target.content.equals(result.content)
          || !target.body.equals(result.body)
          || !target.requires.equals(result.requires)
          || !target.ensures.equals(result.ensures)
          || !target.attributes.equals(result.attributes)) {
        throw reject("stale-precondition", "stale trace target precondition");
      }
      if (!target.module.equals(result.module)
          || !target.label.equals(result.label)
          || !target.source.equals(result.source)
          || !target.location.equals(result.location)) {
        throw reject("stale-precondition", "stale trace target provenance");
      }
      trace.ruleTargetLineage = result.lineage;
      trace.ruleTargetModule = result.module;
      trace.ruleTargetLabel = result.label;
      trace.ruleTargetSource = result.source;
      trace.ruleTargetLocation = result.location;
      trace.ruleTargetRequires = result.requires;
      trace.ruleTargetEnsures = result.ensures;
      trace.ruleTargetAttributes = result.attributes;
      if (trace.ruleTargetContentBefore.isEmpty()) {
        trace.ruleTargetContentBefore = result.content;
        trace.ruleTargetBodyBefore = result.body;
        trace.ruleOperationCanonicalPass1 = result.operationCanonical();
        trace.ruleResultCanonicalFingerprintPass1 = sha256(result.canonical());
      } else {
        trace.ruleOperationCanonicalPass2 = result.operationCanonical();
        trace.ruleResultCanonicalFingerprintPass2 = sha256(result.canonical());
      }
      return result;
    }

    private PreparedTrace prepareTrace(
        Definition definition, RuleDefinitionState state, TraceResult result) {
      LocatedRule located = locateRule(definition, trace.primarySource, result.lineage);
      RuleState target = state.primaryRules.get(result.lineage);
      if (located == null || target == null) throw reject("stale-precondition", "trace target disappeared");
      K parent;
      try {
        parent = resolvePath(located.rule.body(), result.parentPath);
      } catch (ValidationException e) {
        throw reject("path-operation", e.getMessage());
      }
      if (!(parent instanceof KApply parentApply)
          || !parentApply.klabel().name().equals("#cells")) {
        String classification = trace.mode.equals("unsupported-shape") ? "conservative-shape-rejection" : "path-operation";
        throw reject(classification, "declared insertion point is not an official cell bag");
      }
      List<GeneratedCellDescriptor> descriptors =
          state.descriptors.stream().filter(item -> item.name.equals(result.name)).collect(Collectors.toCollection(ArrayList::new));
      if (trace.mode.equals("missing-cell-metadata")) {
        descriptors.clear();
        trace.ruleInputMutationCount++;
      } else if (trace.mode.equals("ambiguous-cell-metadata") && descriptors.size() == 1) {
        descriptors.add(descriptors.get(0));
        trace.ruleInputMutationCount++;
      }
      if (descriptors.size() != 1) {
        throw reject("generated-metadata", "declared generated cell metadata count was " + descriptors.size());
      }
      GeneratedCellDescriptor descriptor = descriptors.get(0);
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
      java.util.Set<String> existingVariables = new java.util.HashSet<>();
      collectVariables(located.rule.body(), existingVariables);
      collectVariables(located.rule.requires(), existingVariables);
      collectVariables(located.rule.ensures(), existingVariables);
      if (result.status.equals("apply") && existingVariables.contains(result.variable)) {
        throw reject("fresh-variable", "declared trace variable collides with target rule");
      }
      List<ProductionDescriptor> productions = new ArrayList<>(state.productions);
      ProductionSpec rootProduction =
          result.afterTerm instanceof ApplySpec root ? root.production : null;
      if (trace.mode.equals("missing-constructor-metadata") && rootProduction != null) {
        productions.removeIf(item -> item.matches(rootProduction));
        trace.ruleInputMutationCount++;
      } else if (trace.mode.equals("ambiguous-constructor-metadata") && rootProduction != null) {
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
      int named = countGeneratedUpdates(parentApply, descriptor, null, null);
      if (result.status.equals("apply") && named != 0) {
        throw reject("path-operation", "declared generated cell update already exists");
      }
      trace.generatedCellName = descriptor.name;
      trace.generatedCellLabel = descriptor.label;
      trace.generatedCellSort = descriptor.cellSort.toString();
      trace.generatedCellBodySort = descriptor.bodySort.toString();
      trace.generatedCellProductionFingerprint = descriptor.productionFingerprint;
      trace.generatedCellMetadataFingerprint = descriptor.metadataFingerprint;
      MarkerEnvelope markers = resolveMarkerEnvelope(parentApply);
      return new PreparedTrace(located, parentApply, descriptor, target, markers, before, after);
    }

    private void validateTraceAlreadyPresent(
        Definition definition, RuleDefinitionState state, TraceResult result) {
      PreparedTrace prepared = prepareTrace(definition, state, result);
      int named = countGeneratedUpdates(prepared.parent, prepared.descriptor, null, null);
      int exact = countGeneratedUpdates(prepared.parent, prepared.descriptor, prepared.before.term, prepared.after.term);
      if (named != 1 || exact != 1) {
        throw reject("envelope", "already-present claim failed independent host validation");
      }
      trace.ruleAlreadyPresentValidatedCount = 1;
    }

    private Definition applyTrace(
        Definition input,
        PreparedTrace prepared,
        K before,
        K after) {
      Att fragmentAtt =
          Att.empty()
              .add(Att.PRODUCTION(), Production.class, prepared.descriptor.production)
              .add(Att.SORT(), Sort.class, prepared.descriptor.cellSort);
      K fragment =
          KApply(
              prepared.descriptor.production.klabel().get(),
              KList(prepared.markers.left, KRewrite(before, after), prepared.markers.right),
              fragmentAtt);
      K appended = KApply(prepared.parent.klabel(), KList(prepared.parent, fragment), prepared.parent.att());
      K newBody = replacePath(prepared.located.rule.body(), currentTraceParentPath(), appended);
      Rule replacement =
          Rule.apply(
              newBody,
              prepared.located.rule.requires(),
              prepared.located.rule.ensures(),
              prepared.located.rule.att());
      return replaceRule(input, prepared.located, replacement, "R3-G-01 generic K-authored generated-cell rule update");
    }

    private static void collectVariables(K root, java.util.Set<String> result) {
      new VisitK() {
        @Override public void apply(KVariable variable) { result.add(variable.name()); }
      }.apply(root);
    }

    private static void validateAppendAndPayload(TraceResult result, RuleState target) {
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
        return new BuiltTerm(KToken(token.lexeme, sort.sort), sort);
      }
      ApplySpec application = (ApplySpec) spec;
      List<ProductionDescriptor> matches = productions.stream()
          .filter(item -> item.matches(application.production))
          .collect(Collectors.toCollection(ArrayList::new));
      if (matches.size() != 1) throw reject("constructor-metadata", "declared constructor metadata count was " + matches.size());
      ProductionDescriptor descriptor = matches.get(0);
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

    private TermPath currentTraceParentPath() {
      return ((TraceResult) trace.currentTraceResult).parentPath;
    }

    private void validateTraceApplied(
        Definition input,
        Definition output,
        RuleDefinitionState before,
        TraceResult result,
        PreparedTrace prepared) {
      RuleDefinitionState after = RuleDefinitionState.capture(output, trace.primarySource);
      require(input != output, "rule trace returned original Definition reference");
      require(before.moduleCount == after.moduleCount, "rule trace changed module cardinality");
      require(before.sentenceCount == after.sentenceCount, "rule trace changed sentence cardinality");
      require(before.nonPrimaryFingerprint.equals(after.nonPrimaryFingerprint), "non-primary-source sentences changed");
      require(before.primaryRules.keySet().equals(after.primaryRules.keySet()), "primary-source rule lineage changed");
      require(!before.fingerprint.equals(after.fingerprint), "post-CF definition fingerprint did not change");
      RuleState targetAfter = after.primaryRules.get(result.lineage);
      require(targetAfter != null, "instrumented rule lineage disappeared");
      require(!prepared.target.content.equals(targetAfter.content), "instrumented rule content did not change");
      require(!prepared.target.body.equals(targetAfter.body), "instrumented rule body did not change");
      require(prepared.target.requires.equals(targetAfter.requires), "instrumented rule requires changed");
      require(prepared.target.ensures.equals(targetAfter.ensures), "instrumented rule ensures changed");
      require(prepared.target.attributes.equals(targetAfter.attributes), "instrumented rule attributes changed");
      int changes = 0;
      for (String lineage : before.primaryRules.keySet()) {
        RuleState left = before.primaryRules.get(lineage);
        RuleState right = after.primaryRules.get(lineage);
        if (!left.content.equals(right.content)) changes++;
      }
      require(changes == 1, "changed primary-source rule count was not one");
      LocatedRule locatedAfter = locateRule(output, trace.primarySource, result.lineage);
      require(locatedAfter != null && containsIdentity(locatedAfter.rule.body(), prepared.located.rule.body()), "original target body was not preserved as an immutable subtree");
      trace.ruleChangedRuleCount = changes;
      trace.ruleTargetContentAfter = targetAfter.content;
      trace.ruleTargetBodyAfter = targetAfter.body;
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

    private static int countGeneratedUpdates(
        K root, GeneratedCellDescriptor descriptor, K before, K after) {
      int[] count = {0};
      new VisitK() {
        @Override
        public void apply(KApply application) {
          if (application.klabel().name().equals(descriptor.label)
              && application.klist().size() == 3) {
            if (before == null && after == null) {
              count[0]++;
            } else if (application.klist().items().get(1) instanceof KRewrite rewrite
                && Projection.encodeTerm(rewrite.left()).equals(Projection.encodeTerm(before))
                && Projection.encodeTerm(rewrite.right()).equals(Projection.encodeTerm(after))) {
              count[0]++;
            }
          }
          super.apply(application);
        }
      }.apply(root);
      return count[0];
    }

    private static MarkerEnvelope resolveMarkerEnvelope(KApply parent) {
      List<MarkerEnvelope> candidates = new ArrayList<>();
      new VisitK() {
        @Override
        public void apply(KApply application) {
          List<K> items = application.klist().items();
          if (items.size() == 3
              && items.get(0) instanceof KApply left
              && items.get(2) instanceof KApply right
              && left.klist().size() == 0
              && right.klist().size() == 0
              && left.klabel().name().equals(right.klabel().name())) {
            candidates.add(new MarkerEnvelope(left, right));
          }
          super.apply(application);
        }
      }.apply(parent);
      if (candidates.isEmpty()) {
        throw reject("generated-metadata", "no reusable official leaf-cell marker envelope");
      }
      String canonical = candidates.get(0).left.klabel().name() + "|" + candidates.get(0).right.klabel().name();
      for (MarkerEnvelope candidate : candidates) {
        String other = candidate.left.klabel().name() + "|" + candidate.right.klabel().name();
        if (!canonical.equals(other)) {
          throw reject("generated-metadata", "ambiguous official leaf-cell marker envelopes");
        }
      }
      return candidates.get(0);
    }
  }

  private record PreparedTrace(
      LocatedRule located,
      KApply parent,
      GeneratedCellDescriptor descriptor,
      RuleState target,
      MarkerEnvelope markers,
      BuiltTerm before,
      BuiltTerm after) {}

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

  private static K replacePath(K root, TermPath path, K replacement) {
    if (path.indices.isEmpty()) return replacement;
    if (!(root instanceof KApply application)) throw new ValidationException("replace path reached non-application");
    int index = path.indices.get(0);
    if (index < 0 || index >= application.klist().size()) throw new ValidationException("replace path index out of bounds");
    List<K> items = new ArrayList<>(application.klist().items());
    items.set(index, replacePath(items.get(index), new TermPath(path.indices.subList(1, path.indices.size())), replacement));
    return KApply(application.klabel(), KList(items), application.att());
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

    private static String encodeMeta(
        K value,
        String primarySource,
        String representedSource,
        Map<String, String> lineageSubstitutions) {
      Att att = value.att();
      String sort = att.getOptional(Att.SORT(), Sort.class).map(Object::toString).orElse("");
      String production = att.getOptional(Att.PRODUCTION(), Production.class).map(Object::toString).orElse("");
      if (value instanceof KToken token) sort = token.sort().toString();
      production =
          replaceIdentity(
              production, primarySource, representedSource, lineageSubstitutions);
      String attributes =
          replaceIdentity(
              att.toString(), primarySource, representedSource, lineageSubstitutions);
      return "cMeta(" + quote(sort) + "," + quote(sha256(production)) + "," + quote(sha256(attributes)) + ")";
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
                  + Projection.encodeTerm(
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
              + Projection.list("oSubsortNil", "oSubsortCons", subsorts) + ")";
      String program = "proposeRuleAppliedTrace(" + quote(mode) + "," + definitionTerm + ")\n";
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
  }

  private sealed interface TraceOutcome
      permits TraceResult, TraceFailure {
    String canonical();
    String status();
    int count();
  }

  private record TraceResult(
      String schema,
      String transformation,
      String definitionFingerprint,
      int candidateCount,
      String status,
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
      TraceWitness witness) implements TraceOutcome {
    @Override public int count() { return candidateCount; }
    String operationCanonical() {
      return "appendGeneratedCellTerm("
          + parentPath.canonical() + "," + quote(name) + ","
          + quote(variable) + "," + variableSort.canonical() + ","
          + beforeTerm.canonical() + "," + afterTerm.canonical() + ","
          + witness.canonical() + ")";
    }
    @Override public String canonical() {
      return "oTraceResult("
          + quote(schema) + "," + quote(transformation) + ","
          + quote(definitionFingerprint) + "," + candidateCount + ","
          + quote(status) + "," + quote(lineage) + "," + quote(content) + ","
          + quote(body) + "," + quote(requires) + "," + quote(ensures) + ","
          + quote(attributes) + "," + quote(module) + "," + quote(label) + ","
          + quote(source) + "," + quote(location) + "," + operationCanonical() + ")";
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
      return "oTraceWitness(" + append.canonical() + "," + singleton.canonical() + ","
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
      return "oTraceFailure("
          + quote(schema) + "," + quote(reason) + "," + count + ")";
    }
  }

  private record TraceInvocation(Request request, TraceOutcome outcome) {}

  private static final class TraceResultParser {
    static void selfTest() {
      SortSpec list = new SortSpec("ListSort", "list-sort-fingerprint");
      SortSpec string = new SortSpec("StringSort", "string-sort-fingerprint");
      ProductionSpec append =
          new ProductionSpec(
              "module", "append", list, List.of(list, list), "production", "label-fingerprint", "metadata");
      TermSpec before = new VariableSpec("TRACE_FRESH", list);
      TermSpec after =
          new ApplySpec(append, List.of(before, new TokenSpec(string, "payload", "\"payload\"")));
      TermPath root = new TermPath(List.of());
      String canonical =
          "<k>"
              + new TraceResult(
                      TRACE_SCHEMA,
                      TRACE_TRANSFORMATION,
                      "definition",
                      1,
                      "apply",
                      "lineage",
                      "content",
                      "body",
                      "requires",
                      "ensures",
                      "attributes",
                      "module",
                      "label",
                      "source",
                      "location",
                      new TermPath(List.of(0)),
                      "cell",
                      "TRACE_FRESH",
                      list,
                      before,
                      after,
                      new TraceWitness(root, root, root, root, root, root, root, root, root))
                  .canonical()
              + "~>.K</k>";
      parse(canonical);
      requireParserRejection(canonical.replace(",1,\"apply\"", ",01,\"apply\""));
      requireParserRejection(canonical.replace("cApplicationArgument(0)", "cApplicationArgument(-0)"));
      requireParserRejection(canonical.replace("\"KRuleAppliedTrace-v1\"", "\"\\u004bRuleAppliedTrace-v1\""));
      requireParserRejection(canonical + canonical);
      requireParserRejection(canonical.replace("oTraceResult", "oUnknownResult"));
    }

    private static void requireParserRejection(String output) {
      try {
        parse(output);
      } catch (ValidationException expected) {
        return;
      }
      throw new AssertionError("noncanonical or malformed trace result was accepted");
    }

    static TraceOutcome parse(String output) {
      Reader reader = new Reader(output);
      reader.expect("<k>");
      String constructor = reader.identifier();
      TraceOutcome result;
      if (constructor.equals("oTraceFailure")) {
        reader.expect('(');
        String schema = reader.string(); reader.expect(',');
        String reason = reader.string(); reader.expect(',');
        int count = reader.integer(); reader.expect(')');
        result = new TraceFailure(schema, reason, count);
      } else if (constructor.equals("oTraceResult")) {
        reader.expect('(');
        String schema = reader.string(); reader.expect(',');
        String transformation = reader.string(); reader.expect(',');
        String definition = reader.string(); reader.expect(',');
        int count = reader.integer(); reader.expect(',');
        String status = reader.string(); reader.expect(',');
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
        TraceWitness witness = witness(reader); reader.expect(')'); reader.expect(')');
        result =
            new TraceResult(
                schema, transformation, definition, count, status, lineage, content,
                body, requires, ensures, attributes, module, label, source, location,
                parent, name, variable, variableSort, before, after, witness);
      } else {
        throw reject("envelope", "unexpected K trace result constructor: " + constructor);
      }
      reader.expect("~>"); reader.expect(".K"); reader.expect("</k>"); reader.end();
      return result;
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
      reader.expectIdentifier("oTraceWitness"); reader.expect('(');
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
                  module + "|" + production + "|" + production.att(),
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
                  module + "|" + production + "|" + production.att(),
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
  }

  private static final class Trace {
    final String mode;
    final Path recordPath;
    final Path traceDefinition;
    final String primarySource;
    final String portableSource;
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
    int ruleAlreadyPresentValidatedCount, ruleInputMutationCount;
    boolean ruleSecondSameReference, ruleTransformedDefinitionReturned;
    boolean ruleIdentityPreserved, ruleProvenancePreserved, ruleAttributesPreserved;
    boolean ruleConditionsPreserved, ruleOriginalNodesPreserved, portableEvidenceProjected;
    boolean portableRuleOrderingValidated, portableTermMetadataRederived;
    TraceOutcome currentTraceResult;

    Trace(
        String mode,
        Path recordPath,
        Path traceDefinition,
        String primarySource,
        String portableSource) {
      this.mode = mode;
      this.recordPath = recordPath;
      this.traceDefinition = traceDefinition;
      this.primarySource = primarySource;
      this.portableSource = portableSource;
    }
    void write() {
      try { Files.createDirectories(recordPath.getParent()); Files.writeString(recordPath, json(), StandardCharsets.UTF_8); } catch (IOException e) { throw KEMException.criticalError("cannot write R3-G-01 record", e); }
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
      fields.put("ruleAlreadyPresentValidatedCount", ruleAlreadyPresentValidatedCount);
      fields.put("ruleInputMutationCount", ruleInputMutationCount);
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
    TraceResult result =
        new TraceResult(
            rawResult.schema,
            rawResult.transformation,
            portable.fingerprint,
            rawResult.candidateCount,
            rawResult.status,
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
            rawResult.witness);
    String canonical = result.canonical();
    require(!canonical.contains(primarySource), "portable result retained the raw source");
    for (String lineage : raw.primaryRules.keySet()) {
      require(!canonical.contains(lineage), "portable result retained a raw lineage");
    }
    return result;
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
