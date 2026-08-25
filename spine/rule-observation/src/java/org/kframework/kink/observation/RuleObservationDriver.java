package org.kframework.kink.observation;

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

/** Composed trusted-small host for KConfigurationAugmentation-v1 and KRuleObservation-v1. */
public final class RuleObservationDriver {
  private static final String MODE_ENV = "R2_G_07_MODE";
  private static final String RECORD_ENV = "R2_G_07_RECORD";
  private static final String K_DEFINITION_ENV = "R2_G_07_CONFIGURATION_K_DEFINITION";
  private static final String OBSERVATION_DEFINITION_ENV = "R2_G_07_OBSERVATION_K_DEFINITION";
  private static final String SCHEMA = "KConfigurationAugmentation-v1";
  private static final String TRANSFORMATION = "p3-add-observation-cell@1";
  private static final String OBSERVATION_SCHEMA = "KRuleObservation-v1";
  private static final String OBSERVATION_TRANSFORMATION = "p3-observe-bump-state@1";
  private static final String HOOK = "OfficialConfigurationTransformHook-v0";
  private static final String POST_CF = "OfficialDefinitionAdapter-v1";

  private RuleObservationDriver() {}

  public static void main(String[] args) {
    if (args.length == 1 && args[0].equals("--parser-self-test")) {
      ObservationResultParser.selfTest();
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
              Path.of(required(K_DEFINITION_ENV)).toAbsolutePath().normalize(),
              Path.of(required(OBSERVATION_DEFINITION_ENV)).toAbsolutePath().normalize(),
              canonical(definitionFile));
      try {
        require(definitionFile.isFile(), "definition file does not exist");
        require(Files.isRegularFile(trace.kDefinition.resolve("mainModule.txt")), "invalid K augmentation definition");
        require(Files.isRegularFile(trace.observationDefinition.resolve("mainModule.txt")), "invalid K observation definition");
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
        AugmentationHook hook = new AugmentationHook(trace);
        Function<Definition, Definition> post = new ObservationAdapter(trace)::apply;
        post = post.andThen(backend.steps());
        CompiledDefinition definition =
            kompile.run(
                definitionFile,
                options.mainModule(fileUtil),
                options.syntaxModule(fileUtil),
                hook::apply,
                post,
                backend.excludedModuleTags());
        require(trace.hookInvocations == 1, "hook invocation count was not one");
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

  private static final class AugmentationHook {
    private final Trace trace;

    AugmentationHook(Trace trace) {
      this.trace = trace;
    }

    Definition apply(Definition input) {
      trace.hookInvocations++;
      DefinitionState before = DefinitionState.capture(input);
      trace.beforeDefinition = before.fingerprint;
      try {
        String kMode = "apply";
        Invocation first = invokeK(input, before, kMode, 1);
        Result result = requireResult(first, before);
        if (!result.status.equals("apply")) {
          validateAlreadyPresent(input, result);
          throw reject("result-envelope-validation", "first pass claimed already-present on unaugmented input");
        }
        Prepared prepared = prepare(input, before, result);
        Definition output = applyPrepared(input, prepared, result.value, true);
        trace.applicationCount = 1;
        trace.validatedOperationCount = 1;
        validateApplied(input, output, before, result, prepared);
        DefinitionState after = DefinitionState.capture(output);
        trace.afterDefinition = after.fingerprint;

        Invocation second = invokeK(output, after, "apply", 2);
        Result already = requireResult(second, after);
        require(already.status.equals("already-present"), "second K pass did not report already-present");
        require(already.lineage.equals(result.lineage), "target lineage changed across K passes");
        validateAlreadyPresent(output, already);
        trace.secondSameReference = true;
        trace.transformedDefinitionReturned = true;
        return output;
      } catch (ValidationException e) {
        if (trace.classification.isEmpty() && e.getMessage().contains(":")) {
          trace.classification = e.getMessage().substring(0, e.getMessage().indexOf(':'));
        }
        if (trace.error.isEmpty()) trace.error = e.getMessage();
        throw KEMException.compilerError("R2-G-06 configuration augmentation failed: " + e.getMessage());
      }
    }

    private Definition conflictNegative(Definition input, DefinitionState before) {
      Invocation declaration = invokeK(input, before, "apply", 1);
      Result result = requireResult(declaration, before);
      Prepared prepared = prepare(input, before, result);
      Definition conflicting = applyPrepared(input, prepared, result.value, false);
      trace.inputMutationCount = 1;
      DefinitionState conflictState = DefinitionState.capture(conflicting);
      Invocation conflict = invokeK(conflicting, conflictState, "apply", 2);
      if (!(conflict.outcome instanceof Failure failure)
          || !failure.reason.equals("conflicting-existing-state")) {
        throw reject("conflicting-existing-state", "K did not reject conflicting observation state");
      }
      trace.classification = "conflicting-existing-state";
      trace.candidateCountPass2 = failure.count;
      throw reject("conflicting-existing-state", "K rejected conflicting existing state");
    }

    private Invocation invokeK(
        Definition definition, DefinitionState state, String mode, int pass) {
      Request request = Projection.encode(definition, state, mode);
      String output = runK(request.program, trace.kDefinition, trace.recordPath);
      Outcome outcome = ResultParser.parse(output);
      trace.currentResult = outcome;
      String responseFingerprint = sha256(outcome.canonical());
      if (pass == 1) {
        trace.requestFingerprintPass1 = request.fingerprint;
        trace.responseFingerprintPass1 = responseFingerprint;
        trace.kInvocationsPass1++;
        trace.statusPass1 = outcome.status();
        trace.candidateCountPass1 = outcome.count();
      } else {
        trace.requestFingerprintPass2 = request.fingerprint;
        trace.responseFingerprintPass2 = responseFingerprint;
        trace.kInvocationsPass2++;
        trace.statusPass2 = outcome.status();
        trace.candidateCountPass2 = outcome.count();
      }
      return new Invocation(request, outcome);
    }

    private Result requireResult(Invocation invocation, DefinitionState state) {
      if (invocation.outcome instanceof Failure failure) {
        String classification =
            failure.reason.equals("structural-target-cardinality")
                ? "k-selection-failure"
                : failure.reason;
        throw reject(classification, "K selection failed: " + failure.reason + " count=" + failure.count);
      }
      Result result = (Result) invocation.outcome;
      if (!result.schema.equals(SCHEMA)
          || !result.transformation.equals(TRANSFORMATION)
          || result.candidateCount != 1
          || (!result.status.equals("apply") && !result.status.equals("already-present"))) {
        throw reject("result-envelope-validation", "invalid K result envelope");
      }
      if (!result.definitionFingerprint.equals(state.fingerprint)) {
        throw reject("stale-precondition", "stale whole-definition fingerprint");
      }
      ConfigurationState target = state.configurations.get(result.lineage);
      if (target == null) throw reject("stale-precondition", "stale target lineage");
      if (!target.content.equals(result.content)
          || !target.body.equals(result.body)
          || !target.ensures.equals(result.ensures)
          || !target.attributes.equals(result.attributes)) {
        throw reject("stale-precondition", "stale target fingerprint");
      }
      trace.targetLineage = result.lineage;
      if (trace.targetContentBefore.isEmpty()) {
        trace.targetContentBefore = result.content;
        trace.targetBodyBefore = result.body;
        trace.operationCanonicalPass1 = result.operationCanonical();
        trace.resultCanonicalFingerprintPass1 = sha256(result.canonical());
      } else {
        trace.operationCanonicalPass2 = result.operationCanonical();
        trace.resultCanonicalFingerprintPass2 = sha256(result.canonical());
      }
      trace.name = result.name;
      trace.value = result.value;
      return result;
    }

    private Prepared prepare(
        Definition definition, DefinitionState state, Result result) {
      ConfigurationState targetState = state.configurations.get(result.lineage);
      LocatedConfiguration located = locate(definition, result.lineage);
      require(targetState != null && located != null, "target disappeared before path validation");
      K parent;
      K template;
      try {
        parent = resolvePath(located.configuration.body(), result.parentPath);
        template = resolvePath(located.configuration.body(), result.templatePath);
      } catch (ValidationException e) {
        throw reject("path-operation-validation", e.getMessage());
      }
      if (!(parent instanceof KApply parentApply)
          || !parentApply.klabel().name().equals("#cells")) {
        throw reject("path-operation-validation", "declared parent is not an official cell bag");
      }
      if (!(template instanceof KApply templateApply)) {
        throw reject("path-operation-validation", "declared template is not an application");
      }
      validateLeafTemplate(templateApply);
      if (result.status.equals("apply") && countNamedCells(parent, result.name) != 0) {
        throw reject("path-operation-validation", "declared new cell name is already present");
      }
      return new Prepared(located, parentApply, templateApply, targetState);
    }

    private void validateAlreadyPresent(Definition definition, Result result) {
      Prepared prepared = prepareAlready(definition, result);
      int exact = countExactCells(prepared.parent, result.name, result.value);
      int named = countNamedCells(prepared.parent, result.name);
      if (named != 1 || exact != 1) {
        throw reject("result-envelope-validation", "already-present claim failed independent host validation");
      }
      trace.alreadyPresentValidatedCount = 1;
    }

    private Prepared prepareAlready(Definition definition, Result result) {
      LocatedConfiguration located = locate(definition, result.lineage);
      if (located == null) throw reject("stale-precondition", "already-present lineage is absent");
      K parent;
      K template;
      try {
        parent = resolvePath(located.configuration.body(), result.parentPath);
        template = resolvePath(located.configuration.body(), result.templatePath);
      } catch (ValidationException e) {
        throw reject("path-operation-validation", e.getMessage());
      }
      if (!(parent instanceof KApply parentApply)
          || !parentApply.klabel().name().equals("#cells")
          || !(template instanceof KApply templateApply)) {
        throw reject("path-operation-validation", "already-present paths do not resolve to required nodes");
      }
      validateLeafTemplate(templateApply);
      return new Prepared(located, parentApply, templateApply, null);
    }

    private Definition applyPrepared(
        Definition input, Prepared prepared, String value, boolean replaceValue) {
      KApply clone = cloneLeaf(prepared.template, trace.name, value, replaceValue);
      K appended = KApply(prepared.parent.klabel(), prepared.parent, clone);
      K newBody = replacePath(prepared.located.configuration.body(), traceResultParentPath(), appended);
      Configuration replacement =
          Configuration.apply(
              newBody,
              prepared.located.configuration.ensures(),
              prepared.located.configuration.att());
      DefinitionTransformer transformer =
          DefinitionTransformer.from(
              module -> {
                if (!module.name().equals(prepared.located.module.name())) return module;
                java.util.Set<Sentence> sentences =
                    stream(module.localSentences())
                        .map(sentence -> sentence == prepared.located.configuration ? replacement : sentence)
                        .collect(Collectors.toSet());
                return Module(module.name(), module.imports(), immutable(sentences), module.att());
              },
              "R2-G-06 generic K-authored configuration augmentation");
      return transformer.apply(input);
    }

    private TermPath traceResultParentPath() {
      Outcome outcome = trace.currentResult;
      if (!(outcome instanceof Result result)) throw reject("result-envelope-validation", "missing current result");
      return result.parentPath;
    }

    private void validateApplied(
        Definition input,
        Definition output,
        DefinitionState before,
        Result result,
        Prepared prepared) {
      DefinitionState after = DefinitionState.capture(output);
      require(input != output, "application returned original Definition reference");
      require(before.moduleCount == after.moduleCount, "module cardinality changed");
      require(before.sentenceCount == after.sentenceCount, "sentence cardinality changed");
      require(before.configurationCount == after.configurationCount, "configuration cardinality changed");
      require(before.nonConfiguration.equals(after.nonConfiguration), "non-configuration content changed");
      require(!before.fingerprint.equals(after.fingerprint), "definition fingerprint did not change");
      ConfigurationState targetAfter = after.configurations.get(result.lineage);
      require(targetAfter != null, "target lineage changed");
      require(!prepared.targetState.content.equals(targetAfter.content), "target content did not change");
      require(!prepared.targetState.body.equals(targetAfter.body), "target body did not change");
      require(prepared.targetState.ensures.equals(targetAfter.ensures), "target ensures changed");
      require(prepared.targetState.attributes.equals(targetAfter.attributes), "target attributes changed");
      int changes = 0;
      for (String lineage : before.configurations.keySet()) {
        ConfigurationState left = before.configurations.get(lineage);
        ConfigurationState right = after.configurations.get(lineage);
        require(right != null, "configuration lineage set changed");
        if (!left.content.equals(right.content)) changes++;
      }
      require(changes == 1, "changed configuration count was not one");
      trace.changedConfigurationCount = changes;
      trace.metadataPreserved = true;
      trace.conditionsPreserved = true;
      trace.provenancePreserved = true;
      trace.targetContentAfter = targetAfter.content;
      trace.targetBodyAfter = targetAfter.body;
    }

    private TermPath traceResultTemplatePath() {
      Outcome outcome = trace.currentResult;
      return ((Result) outcome).templatePath;
    }

    private static void validateLeafTemplate(KApply template) {
      List<K> items = template.klist().items();
      if (!template.klabel().name().equals("#configCell") || items.size() != 4) {
        throw reject("path-operation-validation", "template is not a four-argument #configCell");
      }
      if (!(items.get(0) instanceof KToken start)
          || !(items.get(3) instanceof KToken end)
          || !start.s().equals(end.s())
          || !(items.get(2) instanceof KToken)) {
        throw reject("path-operation-validation", "template is not a matching-name typed leaf cell");
      }
    }

    private static KApply cloneLeaf(
        KApply template, String name, String value, boolean replaceValue) {
      require(!name.isBlank(), "K emitted blank cell name");
      List<K> items = new ArrayList<>(template.klist().items());
      KToken start = (KToken) items.get(0);
      KToken end = (KToken) items.get(3);
      KToken body = (KToken) items.get(2);
      items.set(0, KToken(name, start.sort(), start.att()));
      if (replaceValue) items.set(2, KToken(value, body.sort(), body.att()));
      items.set(3, KToken(name, end.sort(), end.att()));
      return KApply(template.klabel(), KList(items), template.att());
    }
  }

  private static final class ObservationAdapter {
    private final Trace trace;

    ObservationAdapter(Trace trace) {
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
              case "positive-a", "positive-b", "missing-metadata", "ambiguous-metadata" -> "apply";
              case "stale-target-content" -> "stale-target-content";
              case "zero-target" -> "zero-target";
              case "duplicate-target" -> "duplicate-target";
              case "unsupported-path" -> "unsupported-path";
              case "false-already-present" -> "false-already-present";
              default -> throw reject("result-envelope-validation", "unsupported observation mode");
            };
        ObservationInvocation first = invokeObservationK(input, before, kMode, 1);
        ObservationResult result = requireObservationResult(first, before);
        if (!result.status.equals("apply")) {
          validateObservationAlreadyPresent(input, before, result);
          throw reject("result-envelope-validation", "first observation pass claimed already-present");
        }
        PreparedObservation prepared = prepareObservation(input, before, result);
        Definition output = applyObservation(input, prepared, result.beforeValue, result.afterValue);
        trace.ruleApplicationCount = 1;
        trace.ruleValidatedOperationCount = 1;
        validateObservationApplied(input, output, before, result, prepared);
        RuleDefinitionState after = RuleDefinitionState.capture(output, trace.primarySource);
        trace.ruleAfterDefinition = after.fingerprint;

        ObservationInvocation second = invokeObservationK(output, after, "apply", 2);
        ObservationResult already = requireObservationResult(second, after);
        require(already.status.equals("already-present"), "second observation pass did not report already-present");
        require(already.lineage.equals(result.lineage), "observation target lineage changed across passes");
        validateObservationAlreadyPresent(output, after, already);
        trace.ruleSecondSameReference = true;
        trace.ruleTransformedDefinitionReturned = true;
        trace.postCfSameReference = true;
        return output;
      } catch (ValidationException e) {
        if (trace.classification.isEmpty() && e.getMessage().contains(":")) {
          trace.classification = e.getMessage().substring(0, e.getMessage().indexOf(':'));
        }
        if (trace.error.isEmpty()) trace.error = e.getMessage();
        throw KEMException.compilerError("R2-G-07 rule observation failed: " + e.getMessage());
      }
    }

    private Definition conflictNegative(Definition input, RuleDefinitionState before) {
      ObservationInvocation declaration = invokeObservationK(input, before, "apply", 1);
      ObservationResult result = requireObservationResult(declaration, before);
      PreparedObservation prepared = prepareObservation(input, before, result);
      Definition conflicting = applyObservation(input, prepared, result.beforeValue, result.beforeValue);
      trace.ruleInputMutationCount = 1;
      RuleDefinitionState conflictState = RuleDefinitionState.capture(conflicting, trace.primarySource);
      ObservationInvocation conflict = invokeObservationK(conflicting, conflictState, "apply", 2);
      if (!(conflict.outcome instanceof ObservationFailure failure)
          || !failure.reason.equals("conflicting-existing-state")) {
        throw reject("conflict", "K did not reject conflicting generated cell update");
      }
      trace.ruleCandidateCountPass2 = failure.count;
      throw reject("conflict", "K rejected conflicting generated cell update");
    }

    private Definition unsupportedShapeNegative(
        Definition input, RuleDefinitionState before) {
      ObservationInvocation declaration = invokeObservationK(input, before, "apply", 1);
      ObservationResult result = requireObservationResult(declaration, before);
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
      Definition mutated = replaceRuleBody(input, located, newBody, "R2-G-07 unsupported-shape input mutation");
      trace.ruleInputMutationCount = 1;
      RuleDefinitionState mutatedState = RuleDefinitionState.capture(mutated, trace.primarySource);
      ObservationInvocation selected = invokeObservationK(mutated, mutatedState, "apply", 2);
      ObservationResult unsupportedResult = requireObservationResult(selected, mutatedState);
      prepareObservation(mutated, mutatedState, unsupportedResult);
      throw reject("conservative-shape-rejection", "unsupported rule body unexpectedly prepared");
    }

    private ObservationInvocation invokeObservationK(
        Definition definition, RuleDefinitionState state, String mode, int pass) {
      Request request = ObservationProjection.encode(definition, state, trace.primarySource, mode);
      String output = runK(request.program, trace.observationDefinition, trace.recordPath);
      ObservationOutcome outcome = ObservationResultParser.parse(output);
      trace.currentObservationResult = outcome;
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
      return new ObservationInvocation(request, outcome);
    }

    private ObservationResult requireObservationResult(
      ObservationInvocation invocation, RuleDefinitionState state) {
      if (invocation.outcome instanceof ObservationFailure failure) {
        if (!failure.schema.equals(OBSERVATION_SCHEMA)
            || failure.count < 0
            || (!failure.reason.equals("structural-target-cardinality")
                && !failure.reason.equals("conflicting-existing-state"))) {
          throw reject("envelope", "invalid K observation failure envelope");
        }
        String classification =
            failure.reason.equals("structural-target-cardinality")
                ? "k-selection"
                : failure.reason.equals("conflicting-existing-state") ? "conflict" : failure.reason;
        throw reject(classification, "K observation selection failed: " + failure.reason + " count=" + failure.count);
      }
      ObservationResult result = (ObservationResult) invocation.outcome;
      if (!result.schema.equals(OBSERVATION_SCHEMA)
          || !result.transformation.equals(OBSERVATION_TRANSFORMATION)
          || result.candidateCount != 1
          || (!result.status.equals("apply") && !result.status.equals("already-present"))) {
        throw reject("envelope", "invalid K observation result envelope");
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
        throw reject("stale-precondition", "stale observation target precondition");
      }
      trace.ruleTargetLineage = result.lineage;
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

    private PreparedObservation prepareObservation(
        Definition definition, RuleDefinitionState state, ObservationResult result) {
      LocatedRule located = locateRule(definition, trace.primarySource, result.lineage);
      RuleState target = state.primaryRules.get(result.lineage);
      if (located == null || target == null) throw reject("stale-precondition", "observation target disappeared");
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
      if (trace.mode.equals("missing-metadata")) {
        descriptors.clear();
        trace.ruleInputMutationCount++;
      } else if (trace.mode.equals("ambiguous-metadata") && descriptors.size() == 1) {
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
      return new PreparedObservation(located, parentApply, descriptor, target, markers);
    }

    private void validateObservationAlreadyPresent(
        Definition definition, RuleDefinitionState state, ObservationResult result) {
      PreparedObservation prepared = prepareObservation(definition, state, result);
      int named = countGeneratedUpdates(prepared.parent, prepared.descriptor, null, null);
      int exact = countGeneratedUpdates(prepared.parent, prepared.descriptor, result.beforeValue, result.afterValue);
      if (named != 1 || exact != 1) {
        throw reject("envelope", "already-present claim failed independent host validation");
      }
      trace.ruleAlreadyPresentValidatedCount = 1;
    }

    private Definition applyObservation(
        Definition input,
        PreparedObservation prepared,
        String beforeValue,
        String afterValue) {
      Att fragmentAtt =
          Att.empty()
              .add(Att.PRODUCTION(), Production.class, prepared.descriptor.production)
              .add(Att.SORT(), Sort.class, prepared.descriptor.cellSort);
      K before = KToken(beforeValue, prepared.descriptor.bodySort);
      K after = KToken(afterValue, prepared.descriptor.bodySort);
      K fragment =
          KApply(
              prepared.descriptor.production.klabel().get(),
              KList(prepared.markers.left, KRewrite(before, after), prepared.markers.right),
              fragmentAtt);
      K appended = KApply(prepared.parent.klabel(), KList(prepared.parent, fragment), prepared.parent.att());
      K newBody = replacePath(prepared.located.rule.body(), currentObservationParentPath(), appended);
      Rule replacement =
          Rule.apply(
              newBody,
              prepared.located.rule.requires(),
              prepared.located.rule.ensures(),
              prepared.located.rule.att());
      return replaceRule(input, prepared.located, replacement, "R2-G-07 generic K-authored generated-cell rule update");
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

    private TermPath currentObservationParentPath() {
      return ((ObservationResult) trace.currentObservationResult).parentPath;
    }

    private void validateObservationApplied(
        Definition input,
        Definition output,
        RuleDefinitionState before,
        ObservationResult result,
        PreparedObservation prepared) {
      RuleDefinitionState after = RuleDefinitionState.capture(output, trace.primarySource);
      require(input != output, "rule observation returned original Definition reference");
      require(before.moduleCount == after.moduleCount, "rule observation changed module cardinality");
      require(before.sentenceCount == after.sentenceCount, "rule observation changed sentence cardinality");
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
        K root, GeneratedCellDescriptor descriptor, String before, String after) {
      int[] count = {0};
      new VisitK() {
        @Override
        public void apply(KApply application) {
          if (application.klabel().name().equals(descriptor.label)
              && application.klist().size() == 3) {
            if (before == null && after == null) {
              count[0]++;
            } else if (application.klist().items().get(1) instanceof KRewrite rewrite
                && rewrite.left() instanceof KToken left
                && rewrite.right() instanceof KToken right
                && left.sort().equals(descriptor.bodySort)
                && right.sort().equals(descriptor.bodySort)
                && left.s().equals(before)
                && right.s().equals(after)) {
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

  private record PreparedObservation(
      LocatedRule located,
      KApply parent,
      GeneratedCellDescriptor descriptor,
      RuleState target,
      MarkerEnvelope markers) {}

  private record MarkerEnvelope(KApply left, KApply right) {}

  private record LocatedRule(Module module, Rule rule) {}

  private record Prepared(
      LocatedConfiguration located,
      KApply parent,
      KApply template,
      ConfigurationState targetState) {}

  private record LocatedConfiguration(Module module, Configuration configuration) {}

  private static LocatedConfiguration locate(Definition definition, String lineage) {
    for (Module module : stream(definition.modules()).toList()) {
      for (Configuration configuration :
          stream(module.localSentences())
              .filter(Configuration.class::isInstance)
              .map(Configuration.class::cast)
              .toList()) {
        if (ConfigurationState.lineage(module.name(), configuration).equals(lineage)) {
          return new LocatedConfiguration(module, configuration);
        }
      }
    }
    return null;
  }

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

  private static int countNamedCells(K root, String name) {
    int[] count = {0};
    new VisitK() {
      @Override
      public void apply(KApply value) {
        List<K> items = value.klist().items();
        if (value.klabel().name().equals("#configCell")
            && items.size() == 4
            && items.get(0) instanceof KToken token
            && token.s().equals(name)) count[0]++;
        super.apply(value);
      }
    }.apply(root);
    return count[0];
  }

  private static int countExactCells(K root, String name, String value) {
    int[] count = {0};
    new VisitK() {
      @Override
      public void apply(KApply application) {
        List<K> items = application.klist().items();
        if (application.klabel().name().equals("#configCell")
            && items.size() == 4
            && items.get(0) instanceof KToken start
            && items.get(2) instanceof KToken body
            && items.get(3) instanceof KToken end
            && start.s().equals(name)
            && end.s().equals(name)
            && body.s().equals(value)) count[0]++;
        super.apply(application);
      }
    }.apply(root);
    return count[0];
  }

  private record Request(String program, String fingerprint) {}

  private static final class Projection {
    static Request encode(Definition definition, DefinitionState state, String mode) {
      List<String> modules = new ArrayList<>();
      for (Module module : stream(definition.modules()).sorted(Comparator.comparing(Module::name)).toList()) {
        List<Configuration> configurations =
            stream(module.localSentences())
                .filter(Configuration.class::isInstance)
                .map(Configuration.class::cast)
                .sorted(Comparator.comparing(value -> ConfigurationState.lineage(module.name(), value)))
                .toList();
        List<String> encoded = new ArrayList<>();
        for (Configuration configuration : configurations) {
          ConfigurationState item = ConfigurationState.capture(module.name(), configuration);
          encoded.add(
              "cConfiguration("
                  + quote(module.name()) + "," + quote("Configuration") + ","
                  + quote(configuration.source().map(value -> value.source()).orElse("")) + ","
                  + quote(configuration.location().map(Object::toString).orElse("")) + ","
                  + quote(item.lineage) + "," + quote(item.content) + "," + quote(item.body) + ","
                  + quote(item.ensures) + "," + quote(item.attributes) + ","
                  + encodeTerm(configuration.body()) + ")");
        }
        modules.add("cModule(" + quote(module.name()) + "," + list("cConfigurationNil", "cConfigurationCons", encoded) + ")");
      }
      String definitionTerm =
          "cDefinition(" + quote(SCHEMA) + "," + quote(state.fingerprint) + ","
              + list("cModuleNil", "cModuleCons", modules) + ")";
      String program = "proposeConfigurationAugmentation(" + quote(mode) + "," + definitionTerm + ")\n";
      return new Request(program, sha256(definitionTerm));
    }

    private static String encodeTerm(K value) {
      String meta = encodeMeta(value);
      if (value instanceof KApply application) {
        return "cApply(" + quote(application.klabel().name()) + ","
            + list("cTermNil", "cTermCons", application.klist().items().stream().map(Projection::encodeTerm).toList())
            + "," + meta + ")";
      }
      if (value instanceof KToken token) return "cToken(" + quote(token.sort().toString()) + "," + quote(token.s()) + "," + meta + ")";
      if (value instanceof KVariable variable) return "cVariable(" + quote(variable.name()) + "," + meta + ")";
      if (value instanceof KRewrite rewrite) return "cRewrite(" + encodeTerm(rewrite.left()) + "," + encodeTerm(rewrite.right()) + "," + meta + ")";
      if (value instanceof KSequence sequence) return "cSequence(" + list("cTermNil", "cTermCons", sequence.items().stream().map(Projection::encodeTerm).toList()) + "," + meta + ")";
      if (value instanceof KAs alias) return "cAs(" + encodeTerm(alias.pattern()) + "," + encodeTerm(alias.alias()) + "," + meta + ")";
      if (value instanceof InjectedKLabel injected) return "cInjectedLabel(" + quote(injected.klabel().name()) + "," + meta + ")";
      throw reject("request-encoding", "unsupported typed K node: " + value.getClass());
    }

    private static String encodeMeta(K value) {
      Att att = value.att();
      String sort = att.getOptional(Att.SORT(), Sort.class).map(Object::toString).orElse("");
      String production = att.getOptional(Att.PRODUCTION(), Production.class).map(Object::toString).orElse("");
      if (value instanceof KToken token) sort = token.sort().toString();
      return "cMeta(" + quote(sort) + "," + quote(sha256(production)) + "," + quote(sha256(att.toString())) + ")";
    }

    private static String list(String nil, String cons, List<String> values) {
      String result = nil;
      for (int index = values.size() - 1; index >= 0; index--) result = cons + "(" + values.get(index) + "," + result + ")";
      return result;
    }
  }

  private static final class ObservationProjection {
    static Request encode(
        Definition definition,
        RuleDefinitionState state,
        String primarySource,
        String mode) {
      List<String> modules = new ArrayList<>();
      for (Module module :
          stream(definition.modules()).sorted(Comparator.comparing(Module::name)).toList()) {
        List<Rule> rules =
            stream(module.localSentences())
                .filter(Rule.class::isInstance)
                .map(Rule.class::cast)
                .filter(rule -> rule.source().map(value -> value.source()).orElse("").equals(primarySource))
                .sorted(Comparator.comparing(rule -> RuleState.lineage(module.name(), rule)))
                .toList();
        List<String> encoded = new ArrayList<>();
        for (Rule rule : rules) {
          RuleState item = RuleState.capture(module.name(), rule);
          encoded.add(
              "oRule("
                  + quote(module.name()) + "," + quote("Rule") + ","
                  + quote(rule.source().map(value -> value.source()).orElse("")) + ","
                  + quote(rule.location().map(Object::toString).orElse("")) + ","
                  + quote(rule.label().orElse("")) + ","
                  + quote(item.lineage) + "," + quote(item.content) + ","
                  + quote(item.body) + "," + quote(item.requires) + ","
                  + quote(item.ensures) + "," + quote(item.attributes) + ","
                  + Projection.encodeTerm(rule.body()) + ")");
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
                          + quote(descriptor.name) + "," + quote(descriptor.label) + ","
                          + quote(descriptor.cellSort.toString()) + ","
                          + quote(descriptor.bodySort.toString()) + ","
                          + quote(descriptor.productionFingerprint) + ","
                          + quote(descriptor.labelFingerprint) + ","
                          + quote(descriptor.metadataFingerprint) + ")")
              .toList();
      String definitionTerm =
          "oDefinition("
              + quote(OBSERVATION_SCHEMA) + "," + quote(state.fingerprint) + ","
              + Projection.list("oModuleNil", "oModuleCons", modules) + ","
              + Projection.list("oGeneratedCellNil", "oGeneratedCellCons", descriptors) + ")";
      String program = "proposeRuleObservation(" + quote(mode) + "," + definitionTerm + ")\n";
      return new Request(program, sha256(definitionTerm));
    }
  }

  private sealed interface ObservationOutcome
      permits ObservationResult, ObservationFailure {
    String canonical();
    String status();
    int count();
  }

  private record ObservationResult(
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
      TermPath parentPath,
      String name,
      String beforeValue,
      String afterValue) implements ObservationOutcome {
    @Override public int count() { return candidateCount; }
    String operationCanonical() {
      return "oAppendGeneratedCellUpdate("
          + parentPath.canonical() + "," + quote(name) + ","
          + quote(beforeValue) + "," + quote(afterValue) + ")";
    }
    @Override public String canonical() {
      return "oObservationResult("
          + quote(schema) + "," + quote(transformation) + ","
          + quote(definitionFingerprint) + "," + candidateCount + ","
          + quote(status) + "," + quote(lineage) + "," + quote(content) + ","
          + quote(body) + "," + quote(requires) + "," + quote(ensures) + ","
          + quote(attributes) + "," + operationCanonical() + ")";
    }
  }

  private record ObservationFailure(String schema, String reason, int count)
      implements ObservationOutcome {
    @Override public String status() { return "failure:" + reason; }
    @Override public String canonical() {
      return "oObservationFailure("
          + quote(schema) + "," + quote(reason) + "," + count + ")";
    }
  }

  private record ObservationInvocation(Request request, ObservationOutcome outcome) {}

  private static final class ObservationResultParser {
    static void selfTest() {
      String canonical =
          "<k>"
              + new ObservationResult(
                      OBSERVATION_SCHEMA,
                      OBSERVATION_TRANSFORMATION,
                      "definition",
                      1,
                      "apply",
                      "lineage",
                      "content",
                      "body",
                      "requires",
                      "ensures",
                      "attributes",
                      new TermPath(List.of(0)),
                      "cell",
                      "before",
                      "after")
                  .canonical()
              + "~>.K</k>";
      parse(canonical);
      requireParserRejection(canonical.replace(",1,\"apply\"", ",01,\"apply\""));
      requireParserRejection(canonical.replace("cApplicationArgument(0)", "cApplicationArgument(-0)"));
      requireParserRejection(canonical.replace("\"KRuleObservation-v1\"", "\"\\u004bRuleObservation-v1\""));
      requireParserRejection(canonical + canonical);
      requireParserRejection(canonical.replace("oObservationResult", "oUnknownResult"));
    }

    private static void requireParserRejection(String output) {
      try {
        parse(output);
      } catch (ValidationException expected) {
        return;
      }
      throw new AssertionError("noncanonical or malformed observation result was accepted");
    }

    static ObservationOutcome parse(String output) {
      Reader reader = new Reader(output);
      reader.expect("<k>");
      String constructor = reader.identifier();
      ObservationOutcome result;
      if (constructor.equals("oObservationFailure")) {
        reader.expect('(');
        String schema = reader.string(); reader.expect(',');
        String reason = reader.string(); reader.expect(',');
        int count = reader.integer(); reader.expect(')');
        result = new ObservationFailure(schema, reason, count);
      } else if (constructor.equals("oObservationResult")) {
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
        reader.expectIdentifier("oAppendGeneratedCellUpdate"); reader.expect('(');
        TermPath parent = ResultParser.path(reader); reader.expect(',');
        String name = reader.string(); reader.expect(',');
        String before = reader.string(); reader.expect(',');
        String after = reader.string(); reader.expect(')'); reader.expect(')');
        result =
            new ObservationResult(
                schema, transformation, definition, count, status, lineage, content,
                body, requires, ensures, attributes, parent, name, before, after);
      } else {
        throw reject("envelope", "unexpected K observation result constructor: " + constructor);
      }
      reader.expect("~>"); reader.expect(".K"); reader.expect("</k>"); reader.end();
      return result;
    }
  }

  private sealed interface Outcome permits Result, Failure {
    String canonical();
    String status();
    int count();
  }

  private record Result(
      String schema,
      String transformation,
      String definitionFingerprint,
      int candidateCount,
      String status,
      String lineage,
      String content,
      String body,
      String ensures,
      String attributes,
      TermPath parentPath,
      TermPath templatePath,
      String name,
      String value) implements Outcome {
    @Override public int count() { return candidateCount; }
    String operationCanonical() { return "cCloneLeafCellFromInput(" + parentPath.canonical() + "," + templatePath.canonical() + "," + quote(name) + "," + quote(value) + ")"; }
    @Override public String canonical() {
      return "cAugmentationResult(" + quote(schema) + "," + quote(transformation) + "," + quote(definitionFingerprint) + "," + candidateCount + "," + quote(status) + "," + quote(lineage) + "," + quote(content) + "," + quote(body) + "," + quote(ensures) + "," + quote(attributes) + "," + operationCanonical() + ")";
    }
  }

  private record Failure(String schema, String reason, int count) implements Outcome {
    @Override public String status() { return "failure:" + reason; }
    @Override public String canonical() { return "cAugmentationFailure(" + quote(schema) + "," + quote(reason) + "," + count + ")"; }
  }

  private record Invocation(Request request, Outcome outcome) {}

  private record TermPath(List<Integer> indices) {
    String canonical() {
      String result = "cPathNil";
      for (int index = indices.size() - 1; index >= 0; index--) result = "cPathCons(cApplicationArgument(" + indices.get(index) + ")," + result + ")";
      return result;
    }
  }

  private static final class ResultParser {
    static Outcome parse(String output) {
      Reader reader = new Reader(output);
      reader.expect("<k>");
      String constructor = reader.identifier();
      Outcome result;
      if (constructor.equals("cAugmentationFailure")) {
        reader.expect('('); String schema = reader.string(); reader.expect(','); String reason = reader.string(); reader.expect(','); int count = reader.integer(); reader.expect(')');
        result = new Failure(schema, reason, count);
      } else if (constructor.equals("cAugmentationResult")) {
        reader.expect('(');
        String schema = reader.string(); reader.expect(',');
        String transformation = reader.string(); reader.expect(',');
        String definition = reader.string(); reader.expect(',');
        int count = reader.integer(); reader.expect(',');
        String status = reader.string(); reader.expect(',');
        String lineage = reader.string(); reader.expect(',');
        String content = reader.string(); reader.expect(',');
        String body = reader.string(); reader.expect(',');
        String ensures = reader.string(); reader.expect(',');
        String attributes = reader.string(); reader.expect(',');
        reader.expectIdentifier("cCloneLeafCellFromInput"); reader.expect('(');
        TermPath parent = path(reader); reader.expect(','); TermPath template = path(reader); reader.expect(',');
        String name = reader.string(); reader.expect(','); String value = reader.string(); reader.expect(')'); reader.expect(')');
        result = new Result(schema, transformation, definition, count, status, lineage, content, body, ensures, attributes, parent, template, name, value);
      } else throw reject("result-envelope-validation", "unexpected K result constructor: " + constructor);
      reader.expect("~>"); reader.expect(".K"); reader.expect("</k>"); reader.end();
      return result;
    }

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

  private static final class DefinitionState {
    final String fingerprint;
    final String nonConfiguration;
    final int moduleCount;
    final int sentenceCount;
    final int configurationCount;
    final Map<String, ConfigurationState> configurations;
    DefinitionState(String fingerprint, String nonConfiguration, int moduleCount, int sentenceCount, int configurationCount, Map<String, ConfigurationState> configurations) {
      this.fingerprint = fingerprint; this.nonConfiguration = nonConfiguration; this.moduleCount = moduleCount; this.sentenceCount = sentenceCount; this.configurationCount = configurationCount; this.configurations = configurations;
    }
    static DefinitionState capture(Definition definition) {
      StringBuilder graph = new StringBuilder("definition|").append(definition.att()).append('|').append(definition.mainModule().name()).append('\n');
      StringBuilder non = new StringBuilder(); Map<String, ConfigurationState> configs = new LinkedHashMap<>(); int sentences = 0;
      List<Module> modules = stream(definition.modules()).sorted(Comparator.comparing(Module::name)).toList();
      for (Module module : modules) {
        graph.append("module|").append(module.name()).append('|').append(module.att()).append('\n');
        stream(module.imports()).map(value -> value.module().name() + "|" + value.isPublic()).sorted().forEach(value -> graph.append("import|").append(value).append('\n'));
        List<Sentence> local = stream(module.localSentences()).sorted(Comparator.comparing(value -> value.getClass().getName() + "|" + value + "|" + value.att())).toList(); sentences += local.size();
        for (Sentence sentence : local) {
          if (sentence instanceof Configuration configuration) { ConfigurationState state = ConfigurationState.capture(module.name(), configuration); if (configs.put(state.lineage, state) != null) throw reject("request-encoding", "duplicate configuration lineage"); }
          else non.append(module.name()).append('|').append(sentence.getClass().getName()).append('|').append(sentence).append('|').append(sentence.att()).append('\n');
        }
      }
      String nonHash = sha256(non.toString()); String fingerprint = sha256(graph + "|" + nonHash + "|" + configs.values().stream().map(value -> value.content).sorted().collect(Collectors.joining("|")));
      return new DefinitionState(fingerprint, nonHash, modules.size(), sentences, configs.size(), Map.copyOf(configs));
    }
  }

  private record ConfigurationState(String module, String lineage, String content, String body, String ensures, String attributes) {
    static ConfigurationState capture(String module, Configuration value) {
      String lineage = lineage(module, value); String body = sha256(Projection.encodeTerm(value.body())); String ensures = sha256(Projection.encodeTerm(value.ensures())); String attributes = sha256(value.att().toString()); String content = sha256(lineage + "|" + body + "|" + ensures + "|" + attributes); return new ConfigurationState(module, lineage, content, body, ensures, attributes);
    }
    static String lineage(String module, Configuration value) { return sha256(module + "|Configuration|" + value.source().map(item -> item.source()).orElse("") + "|" + value.location().map(Object::toString).orElse("")); }
  }

  private static final class RuleDefinitionState {
    final String fingerprint;
    final String nonPrimaryFingerprint;
    final int moduleCount;
    final int sentenceCount;
    final Map<String, RuleState> primaryRules;
    final List<GeneratedCellDescriptor> descriptors;

    RuleDefinitionState(
        String fingerprint,
        String nonPrimaryFingerprint,
        int moduleCount,
        int sentenceCount,
        Map<String, RuleState> primaryRules,
        List<GeneratedCellDescriptor> descriptors) {
      this.fingerprint = fingerprint;
      this.nonPrimaryFingerprint = nonPrimaryFingerprint;
      this.moduleCount = moduleCount;
      this.sentenceCount = sentenceCount;
      this.primaryRules = primaryRules;
      this.descriptors = descriptors;
    }

    static RuleDefinitionState capture(Definition definition, String primarySource) {
      StringBuilder graph =
          new StringBuilder("definition|")
              .append(definition.att()).append('|')
              .append(definition.mainModule().name()).append('\n');
      StringBuilder nonPrimary = new StringBuilder();
      Map<String, RuleState> rules = new LinkedHashMap<>();
      List<GeneratedCellDescriptor> descriptors = new ArrayList<>();
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
            RuleState state = RuleState.capture(module.name(), rule);
            if (rules.put(state.lineage, state) != null) {
              throw reject("request-encoding", "duplicate primary-source rule lineage");
            }
          } else {
            nonPrimary
                .append(module.name()).append('|')
                .append(sentence.getClass().getName()).append('|')
                .append(sentence).append('|').append(sentence.att()).append('\n');
          }
          if (sentence instanceof Production production
              && production.att().contains(Att.CELL())
              && production.klabel().isDefined()
              && production.arity() == 1) {
            String name = production.att().getOptional(Att.CELL_NAME()).orElse("");
            if (!name.isBlank()) descriptors.add(GeneratedCellDescriptor.capture(module.name(), name, production));
          }
        }
      }
      descriptors.sort(Comparator.comparing(GeneratedCellDescriptor::canonical));
      String nonHash = sha256(nonPrimary.toString());
      String fingerprint =
          sha256(
              graph + "|" + nonHash + "|"
                  + rules.values().stream().map(value -> value.content).sorted().collect(Collectors.joining("|")));
      return new RuleDefinitionState(
          fingerprint,
          nonHash,
          modules.size(),
          sentences,
          Map.copyOf(rules),
          List.copyOf(descriptors));
    }
  }

  private record RuleState(
      String module,
      String lineage,
      String content,
      String body,
      String requires,
      String ensures,
      String attributes) {
    static RuleState capture(String module, Rule rule) {
      String lineage = lineage(module, rule);
      String body = sha256(Projection.encodeTerm(rule.body()));
      String requires = sha256(Projection.encodeTerm(rule.requires()));
      String ensures = sha256(Projection.encodeTerm(rule.ensures()));
      String attributes = sha256(rule.att().toString());
      String content = sha256(lineage + "|" + body + "|" + requires + "|" + ensures + "|" + attributes);
      return new RuleState(module, lineage, content, body, requires, ensures, attributes);
    }

    static String lineage(String module, Rule rule) {
      return sha256(
          module + "|Rule|"
              + rule.source().map(value -> value.source()).orElse("") + "|"
              + rule.location().map(Object::toString).orElse("") + "|"
              + rule.label().orElse(""));
    }
  }

  private record GeneratedCellDescriptor(
      String module,
      String name,
      String label,
      Sort cellSort,
      Sort bodySort,
      String productionFingerprint,
      String labelFingerprint,
      String metadataFingerprint,
      Production production) {
    static GeneratedCellDescriptor capture(String module, String name, Production production) {
      String label = production.klabel().get().name();
      Sort bodySort = production.nonterminal(0).sort();
      return new GeneratedCellDescriptor(
          module,
          name,
          label,
          production.sort(),
          bodySort,
          sha256(module + "|" + production + "|" + production.att()),
          sha256(label),
          sha256(production.att().toString()),
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
    final Path kDefinition;
    final Path observationDefinition;
    final String primarySource;
    String status = "running", classification = "", error = "", beforeDefinition = "", afterDefinition = "", requestFingerprintPass1 = "", requestFingerprintPass2 = "", responseFingerprintPass1 = "", responseFingerprintPass2 = "", statusPass1 = "", statusPass2 = "", targetLineage = "", targetContentBefore = "", targetContentAfter = "", targetBodyBefore = "", targetBodyAfter = "", operationCanonicalPass1 = "", operationCanonicalPass2 = "", resultCanonicalFingerprintPass1 = "", resultCanonicalFingerprintPass2 = "", name = "", value = "";
    int hookInvocations, kInvocationsPass1, kInvocationsPass2, candidateCountPass1, candidateCountPass2, validatedOperationCount, applicationCount, changedConfigurationCount, alreadyPresentValidatedCount, inputMutationCount, postCfInvocations;
    boolean secondSameReference, metadataPreserved, conditionsPreserved, provenancePreserved, transformedDefinitionReturned, postCfSameReference, cfConstructed, backendConstructed;
    Outcome currentResult;
    String ruleBeforeDefinition = "", ruleAfterDefinition = "";
    String ruleRequestFingerprintPass1 = "", ruleRequestFingerprintPass2 = "";
    String ruleResponseFingerprintPass1 = "", ruleResponseFingerprintPass2 = "";
    String ruleStatusPass1 = "", ruleStatusPass2 = "";
    String ruleTargetLineage = "", ruleTargetContentBefore = "", ruleTargetContentAfter = "";
    String ruleTargetBodyBefore = "", ruleTargetBodyAfter = "";
    String ruleOperationCanonicalPass1 = "", ruleOperationCanonicalPass2 = "";
    String ruleResultCanonicalFingerprintPass1 = "", ruleResultCanonicalFingerprintPass2 = "";
    String generatedCellName = "", generatedCellLabel = "", generatedCellSort = "";
    String generatedCellBodySort = "", generatedCellProductionFingerprint = "";
    String generatedCellMetadataFingerprint = "";
    int ruleKInvocationsPass1, ruleKInvocationsPass2;
    int ruleCandidateCountPass1, ruleCandidateCountPass2;
    int ruleValidatedOperationCount, ruleApplicationCount, ruleChangedRuleCount;
    int ruleAlreadyPresentValidatedCount, ruleInputMutationCount;
    boolean ruleSecondSameReference, ruleTransformedDefinitionReturned;
    boolean ruleIdentityPreserved, ruleProvenancePreserved, ruleAttributesPreserved;
    boolean ruleConditionsPreserved, ruleOriginalNodesPreserved;
    ObservationOutcome currentObservationResult;

    Trace(
        String mode,
        Path recordPath,
        Path kDefinition,
        Path observationDefinition,
        String primarySource) {
      this.mode = mode;
      this.recordPath = recordPath;
      this.kDefinition = kDefinition;
      this.observationDefinition = observationDefinition;
      this.primarySource = primarySource;
    }
    void write() {
      try { Files.createDirectories(recordPath.getParent()); Files.writeString(recordPath, json(), StandardCharsets.UTF_8); } catch (IOException e) { throw KEMException.criticalError("cannot write R2-G-07 record", e); }
    }
    String json() {
      Map<String,Object> fields = new LinkedHashMap<>();
      fields.put("schemaVersion", 1);
      fields.put("configurationContract", SCHEMA);
      fields.put("ruleContract", OBSERVATION_SCHEMA);
      fields.put("hook", HOOK);
      fields.put("postCfAdapter", POST_CF);
      fields.put("mode", mode);
      fields.put("status", status);
      fields.put("classification", classification);
      fields.put("error", error);
      fields.put("configurationHookInvocations", hookInvocations);
      fields.put("configurationKInvocationsPass1", kInvocationsPass1);
      fields.put("configurationKInvocationsPass2", kInvocationsPass2);
      fields.put("configurationRequestFingerprintPass1", requestFingerprintPass1);
      fields.put("configurationResponseFingerprintPass1", responseFingerprintPass1);
      fields.put("configurationCandidateCountPass1", candidateCountPass1);
      fields.put("configurationStatusPass1", statusPass1);
      fields.put("configurationRequestFingerprintPass2", requestFingerprintPass2);
      fields.put("configurationResponseFingerprintPass2", responseFingerprintPass2);
      fields.put("configurationCandidateCountPass2", candidateCountPass2);
      fields.put("configurationStatusPass2", statusPass2);
      fields.put("configurationTargetLineage", targetLineage);
      fields.put("configurationTargetContentBefore", targetContentBefore);
      fields.put("configurationTargetContentAfter", targetContentAfter);
      fields.put("configurationTargetBodyBefore", targetBodyBefore);
      fields.put("configurationTargetBodyAfter", targetBodyAfter);
      fields.put("configurationOperationCanonicalPass1", operationCanonicalPass1);
      fields.put("configurationOperationCanonicalPass2", operationCanonicalPass2);
      fields.put("configurationResultCanonicalFingerprintPass1", resultCanonicalFingerprintPass1);
      fields.put("configurationResultCanonicalFingerprintPass2", resultCanonicalFingerprintPass2);
      fields.put("configurationValidatedOperationCount", validatedOperationCount);
      fields.put("configurationApplicationCount", applicationCount);
      fields.put("configurationChangedCount", changedConfigurationCount);
      fields.put("configurationAlreadyPresentValidatedCount", alreadyPresentValidatedCount);
      fields.put("configurationSecondSameReference", secondSameReference);
      fields.put("configurationMetadataPreserved", metadataPreserved);
      fields.put("configurationConditionsPreserved", conditionsPreserved);
      fields.put("configurationProvenancePreserved", provenancePreserved);
      fields.put("configurationBeforeDefinition", beforeDefinition);
      fields.put("configurationAfterDefinition", afterDefinition);
      fields.put("configurationTransformedDefinitionReturned", transformedDefinitionReturned);
      fields.put("postCfAdapterInvocations", postCfInvocations);
      fields.put("configurationCfConstructed", cfConstructed);
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
      fields.put("ruleOriginalNodesPreserved", ruleOriginalNodesPreserved);
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
      fields.put("backendConstructed", backendConstructed);
      StringBuilder result = new StringBuilder("{\n"); int index=0; for (var item: fields.entrySet()) { result.append("  ").append(quoteJson(item.getKey())).append(": "); Object v=item.getValue(); if (v instanceof String s) result.append(quoteJson(s)); else result.append(v); result.append(++index == fields.size() ? "\n" : ",\n"); } return result.append("}\n").toString();
    }
  }

  private static String runK(String program, Path definition, Path recordPath) {
    try {
      Path parent = recordPath.getParent(); Files.createDirectories(parent); Path file = Files.createTempFile(parent, "configuration-", ".kink");
      try { Files.writeString(file, program, StandardCharsets.UTF_8); RunProcess.ProcessOutput output = RunProcess.execute(Map.of("LC_ALL","C","LANG","C","TZ","UTC"), new ProcessBuilder(), "krun", file.toString(), "--definition", definition.toString(), "--output", "pretty"); String stderr = new String(output.stderr(), StandardCharsets.UTF_8); if (output.exitCode()!=0) throw reject("k-selection-failure", "K execution failed: " + stderr.strip()); return new String(output.stdout(), StandardCharsets.UTF_8); } finally { Files.deleteIfExists(file); }
    } catch (IOException e) { throw KEMException.criticalError("cannot invoke K augmentation", e); }
  }

  private static String required(String name) { String value=System.getenv(name); if (value==null || value.isBlank()) throw KEMException.criticalError("missing environment " + name); return value; }
  private static String canonical(File file) { try { return file.getCanonicalPath(); } catch (IOException e) { throw KEMException.criticalError("cannot canonicalize definition file", e); } }
  private static ValidationException reject(String classification, String message) { return new ValidationException(classification + ": " + message); }
  private static void require(boolean condition, String message) { if (!condition) throw new ValidationException(message); }
  private static String quote(String value) { return StringUtil.enquoteKString(value); }
  private static String quoteJson(String value) { return "\"" + value.replace("\\","\\\\").replace("\"","\\\"").replace("\n","\\n").replace("\r","\\r") + "\""; }
  private static String sha256(String value) { try { byte[] digest=MessageDigest.getInstance("SHA-256").digest(value.getBytes(StandardCharsets.UTF_8)); StringBuilder out=new StringBuilder(); for(byte item:digest) out.append(String.format(Locale.ROOT,"%02x",item)); return out.toString(); } catch(NoSuchAlgorithmException e){ throw new AssertionError(e); } }
  private static final class ValidationException extends RuntimeException { ValidationException(String message){super(message);} }
}
