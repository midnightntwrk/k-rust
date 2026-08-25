package org.kframework.kink.trace;

import static org.kframework.Collections.immutable;
import static org.kframework.Collections.stream;
import static org.kframework.definition.Constructors.Module;
import static org.kframework.kore.KORE.KApply;
import static org.kframework.kore.KORE.KList;
import static org.kframework.kore.KORE.KToken;

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
import org.kframework.definition.Configuration;
import org.kframework.definition.Definition;
import org.kframework.definition.DefinitionTransformer;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Sentence;
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
import org.kframework.utils.RunProcess;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;

/** Trusted-small pre-CF host for KTraceConfigurationAugmentation-v1. */
final class TraceConfigurationAugmentation implements Function<Definition, Definition> {
  static final String SCHEMA = "KTraceConfigurationAugmentation-v1";
  static final String TRANSFORMATION = "p3-add-empty-trace-cell@1";
  static final String HOOK = "OfficialConfigurationTransformHook-v0";

  private final String mode;
  private final Path kDefinition;
  private final Path recordPath;
  private final String primarySource;
  private final String portableSource;
  final Metrics metrics = new Metrics();
  private Outcome current;

  TraceConfigurationAugmentation(
      String mode,
      Path kDefinition,
      Path recordPath,
      String primarySource,
      String portableSource) {
    this.mode = mode;
    this.kDefinition = kDefinition;
    this.recordPath = recordPath;
    this.primarySource = primarySource;
    this.portableSource = portableSource;
  }

  static void parserSelfTest() {
    SortSpec sort = new SortSpec("UnitSort", "unit-sort-fingerprint");
    ProductionSpec production =
        new ProductionSpec(
            "module", "unit", sort, List.of(), "production", "label", "metadata");
    Result value =
        new Result(
            SCHEMA, TRANSFORMATION, "definition", 1, "apply", "lineage", "source",
            "location", "content", "body", "ensures", "attributes",
            new TermPath(List.of(2)), new TermPath(List.of(2, 1)), "cell",
            new ApplySpec(production, List.of()));
    String canonical = "<k>" + value.canonical() + "~>.K</k>";
    ResultParser.parse(canonical);
    rejectParser(canonical.replace(",1,\"apply\"", ",01,\"apply\""));
    rejectParser(canonical.replace("cApplicationArgument(2)", "cApplicationArgument(-0)"));
    rejectParser(canonical.replace("\"KTraceConfigurationAugmentation-v1\"", "\"\\u004bTraceConfigurationAugmentation-v1\""));
    rejectParser(canonical + canonical);
    rejectParser(canonical.replace("cTraceAugmentationResult", "cUnknownResult"));
    validateFailureEnvelope(new Failure(SCHEMA, "structural-target-cardinality", 0));
    validateFailureEnvelope(new Failure(SCHEMA, "initializer-descriptor-cardinality", 0));
    validateFailureEnvelope(new Failure(SCHEMA, "conflicting-existing-state", 1));
    rejectFailureEnvelope(new Failure("KTraceConfigurationAugmentation-v0",
        "structural-target-cardinality", 0));
    rejectFailureEnvelope(new Failure(SCHEMA, "unknown-reason", 0));
    rejectFailureEnvelope(new Failure(SCHEMA, "structural-target-cardinality", -1));
    rejectFailureEnvelope(new Failure(SCHEMA, "structural-target-cardinality", 1));
    rejectFailureEnvelope(new Failure(SCHEMA, "initializer-descriptor-cardinality", 1));
    rejectFailureEnvelope(new Failure(SCHEMA, "conflicting-existing-state", 0));
    exactCloneComparatorSelfTest();
    require(Projection.isCanonicalOrder(List.of("a", "b")), "canonical-order self-test rejected sorted values");
    require(!Projection.isCanonicalOrder(List.of("b", "a")), "canonical-order self-test accepted unsorted values");
  }

  private static void rejectFailureEnvelope(Failure failure) {
    try {
      validateFailureEnvelope(failure);
    } catch (ValidationException expected) {
      return;
    }
    throw new AssertionError("invalid configuration failure envelope was accepted");
  }

  private static void exactCloneComparatorSelfTest() {
    Sort cellName = org.kframework.kore.KORE.Sort("ComparatorCellName", List.of());
    Sort valueSort = org.kframework.kore.KORE.Sort("ComparatorValue", List.of());
    Att startAtt = Att.empty().add(Att.unrecognizedKey("comparator-start"), "one");
    Att endAtt = Att.empty().add(Att.unrecognizedKey("comparator-end"), "one");
    Att propertyAtt = Att.empty().add(Att.unrecognizedKey("comparator-property"), "one");
    Att shellAtt = Att.empty().add(Att.unrecognizedKey("comparator-shell"), "one");
    K property = KApply(org.kframework.kore.KORE.KLabel("comparatorProperty"), KList(), propertyAtt);
    K initializer = KApply(org.kframework.kore.KORE.KLabel("comparatorInitializer"), KList(),
        Att.empty().add(Att.SORT(), Sort.class, valueSort));
    KApply template = KApply(org.kframework.kore.KORE.KLabel("#configCell"),
        KList(KToken("comparatorOriginalName", cellName, startAtt), property,
            KToken("1", valueSort), KToken("comparatorOriginalName", cellName, endAtt)), shellAtt);
    KApply expected = cloneShell(template, "comparatorCloneName", initializer);
    require(sameCompleteTerm(
        expected, cloneShell(template, "comparatorCloneName", initializer), "", ""),
        "complete-clone comparator rejected an equal clone");

    List<K> items = new ArrayList<>(expected.klist().items());
    items.set(1, KApply(org.kframework.kore.KORE.KLabel("alteredProperty"), KList(), propertyAtt));
    require(!sameCompleteTerm(expected, KApply(expected.klabel(), KList(items), expected.att()), "", ""),
        "complete-clone comparator accepted altered properties");
    items = new ArrayList<>(expected.klist().items());
    items.set(0, KToken("comparatorCloneName", valueSort, startAtt));
    require(!sameCompleteTerm(expected, KApply(expected.klabel(), KList(items), expected.att()), "", ""),
        "complete-clone comparator accepted altered start-token sort");
    items = new ArrayList<>(expected.klist().items());
    items.set(3, KToken("comparatorCloneName", cellName,
        endAtt.add(Att.unrecognizedKey("comparator-end-extra"), "two")));
    require(!sameCompleteTerm(expected, KApply(expected.klabel(), KList(items), expected.att()), "", ""),
        "complete-clone comparator accepted altered end-token attributes");
    KApply alteredShell = KApply(expected.klabel(), expected.klist(),
        shellAtt.add(Att.unrecognizedKey("comparator-shell-extra"), "two"));
    require(!sameCompleteTerm(expected, alteredShell, "", ""),
        "complete-clone comparator accepted altered application metadata");
    items = new ArrayList<>(expected.klist().items());
    items.set(2, KApply(((KApply) initializer).klabel(), KList(),
        initializer.att().add(Att.unrecognizedKey("comparator-node-extra"), "two")));
    require(!sameCompleteTerm(expected, KApply(expected.klabel(), KList(items), expected.att()), "", ""),
        "complete-clone comparator accepted altered node metadata");
  }

  private static void rejectParser(String encoded) {
    try {
      ResultParser.parse(encoded);
    } catch (ValidationException expected) {
      return;
    }
    throw new AssertionError("noncanonical configuration result was accepted");
  }

  @Override
  public Definition apply(Definition input) {
    metrics.hookInvocations++;
    DefinitionState before = DefinitionState.capture(input, primarySource, primarySource);
    metrics.beforeDefinition = before.fingerprint;
    try {
      if (mode.equals("config-conflict-existing") || mode.equals("config-conflict-shape")) {
        return conflictNegative(input, before, mode.equals("config-conflict-shape"));
      }
      if (mode.equals("config-false-already-shape")) {
        return falseAlreadyShapeNegative(input, before);
      }
      String kMode = configurationMode();
      Invocation first = invoke(input, before, kMode, 1);
      Result result = requireResult(first, before);
      if (!result.status.equals("apply")) {
        validateAlreadyPresent(input, before, result);
        throw reject("envelope", "first pass claimed already-present on two-cell input");
      }
      Prepared prepared = prepare(input, before, result);
      Definition output = applyPrepared(input, prepared, prepared.initializer);
      metrics.applicationCount = 1;
      metrics.validatedOperationCount = 1;
      validateApplied(input, output, before, result, prepared);
      DefinitionState after = DefinitionState.capture(output, primarySource, primarySource);
      metrics.afterDefinition = after.fingerprint;

      Invocation second = invoke(output, after, "apply", 2);
      Result already = requireResult(second, after);
      require(already.status.equals("already-present"), "second configuration pass was not already-present");
      require(already.lineage.equals(result.lineage), "configuration lineage changed across passes");
      validateAlreadyPresent(output, after, already);
      capturePortableEvidence(input, output, before, after, result, already);
      metrics.secondSameReference = true;
      metrics.transformedDefinitionReturned = true;
      return output;
    } catch (ValidationException error) {
      if (metrics.classification.isEmpty() && error.getMessage().contains(":")) {
        metrics.classification = error.getMessage().substring(0, error.getMessage().indexOf(':'));
      }
      if (metrics.error.isEmpty()) metrics.error = error.getMessage();
      throw KEMException.compilerError("R3-G-02 configuration augmentation failed: " + error.getMessage());
    }
  }

  private String configurationMode() {
    if (!mode.startsWith("config-")) return "apply";
    return switch (mode) {
      case "config-stale-definition" -> "stale-definition";
      case "config-stale-target-content" -> "stale-target-content";
      case "config-stale-target-provenance" -> "stale-target-provenance";
      case "config-zero-target" -> "zero-target";
      case "config-duplicate-target" -> "duplicate-target";
      case "config-unsupported-parent-path" -> "unsupported-parent-path";
      case "config-out-of-bounds-template-path" -> "out-of-bounds-template-path";
      case "config-malformed-template" -> "malformed-template";
      case "config-non-leaf-template" -> "non-leaf-template";
      case "config-false-already-present" -> "false-already-present";
      case "config-failure-wrong-schema" -> "failure-wrong-schema";
      case "config-failure-unknown-reason" -> "failure-unknown-reason";
      case "config-failure-invalid-count" -> "failure-invalid-count";
      case "config-unknown-constructor" -> "unknown-constructor";
      case "config-non-nullary-initializer" -> "non-nullary-initializer";
      case "config-variable-initializer" -> "variable-initializer";
      case "config-sort-invalid-initializer" -> "sort-invalid-initializer";
      case "config-missing-production", "config-ambiguous-production",
          "config-missing-sort", "config-ambiguous-sort" -> "apply";
      default -> throw reject("envelope", "unsupported configuration mode");
    };
  }

  private Definition conflictNegative(
      Definition input, DefinitionState before, boolean alterShape) {
    Result declaration = requireResult(invoke(input, before, "apply", 1), before);
    Prepared prepared = prepare(input, before, declaration);
    KApply clone = alterShape
        ? alterCloneProperties(prepared.expectedClone)
        : cloneShell(prepared.template, declaration.name, prepared.template.klist().items().get(2));
    Definition conflicting = appendClone(input, prepared, clone, declaration);
    metrics.inputMutationCount = 1;
    DefinitionState state = DefinitionState.capture(conflicting, primarySource, primarySource);
    Invocation selected = invoke(conflicting, state, "apply", 2);
    if (!(selected.outcome instanceof Failure failure)) {
      throw reject("conflict", "K did not reject conflicting same-name cell");
    }
    requireValidFailure(failure);
    if (!failure.reason.equals("conflicting-existing-state") || failure.count != 1) {
      throw reject("conflict", "K conflict result was not exactly one same-name conflict");
    }
    throw reject("conflict", "K rejected conflicting same-name cell");
  }

  private Definition falseAlreadyShapeNegative(Definition input, DefinitionState before) {
    Result declaration = requireResult(invoke(input, before, "apply", 1), before);
    Prepared prepared = prepare(input, before, declaration);
    Definition altered = appendClone(
        input, prepared, alterCloneProperties(prepared.expectedClone), declaration);
    metrics.inputMutationCount = 1;
    DefinitionState state = DefinitionState.capture(altered, primarySource, primarySource);
    Result claimed = requireResult(invoke(altered, state, "false-already-shape", 2), state);
    require(claimed.status.equals("already-present"), "shape oracle did not claim already-present");
    validateAlreadyPresent(altered, state, claimed);
    throw reject("envelope", "altered shell unexpectedly passed complete-clone validation");
  }

  private Invocation invoke(Definition definition, DefinitionState state, String kMode, int pass) {
    Request request = Projection.encode(definition, state, primarySource, primarySource, kMode);
    String output = runK(request.program, kDefinition, recordPath);
    Outcome outcome = ResultParser.parse(output);
    current = outcome;
    String response = sha256(outcome.canonical());
    if (outcome instanceof Failure failure) {
      metrics.failureCanonical = failure.canonical();
      metrics.failureSchema = failure.schema;
      metrics.failureReason = failure.reason;
      metrics.failureCount = failure.count;
      metrics.failureObserved = true;
      recordInvocation(pass, request.fingerprint, response, "failure", failure.count);
      requireValidFailure(failure);
      if (pass == 1) metrics.statusPass1 = failure.status();
      else metrics.statusPass2 = failure.status();
      return new Invocation(request, outcome);
    }
    recordInvocation(pass, request.fingerprint, response, outcome.status(), outcome.count());
    return new Invocation(request, outcome);
  }

  private void recordInvocation(
      int pass, String requestFingerprint, String responseFingerprint, String status, int count) {
    if (pass == 1) {
      metrics.requestFingerprintPass1 = requestFingerprint;
      metrics.responseFingerprintPass1 = responseFingerprint;
      metrics.kInvocationsPass1++;
      metrics.statusPass1 = status;
      metrics.candidateCountPass1 = count;
    } else {
      metrics.requestFingerprintPass2 = requestFingerprint;
      metrics.responseFingerprintPass2 = responseFingerprint;
      metrics.kInvocationsPass2++;
      metrics.statusPass2 = status;
      metrics.candidateCountPass2 = count;
    }
  }

  private Result requireResult(Invocation invocation, DefinitionState state) {
    if (invocation.outcome instanceof Failure failure) {
      requireValidFailure(failure);
      String classification =
          failure.reason.equals("structural-target-cardinality")
              ? "k-selection"
              : failure.reason.equals("initializer-descriptor-cardinality")
                  ? "initializer-production-metadata"
                  : "conflict";
      throw reject(classification, "K selection failed: " + failure.reason + " count=" + failure.count);
    }
    Result result = (Result) invocation.outcome;
    if (!result.schema.equals(SCHEMA)
        || !result.transformation.equals(TRANSFORMATION)
        || result.candidateCount != 1
        || (!result.status.equals("apply") && !result.status.equals("already-present"))) {
      throw reject("envelope", "invalid configuration result envelope");
    }
    if (!result.definitionFingerprint.equals(state.fingerprint)) {
      throw reject("stale-precondition", "stale whole-definition fingerprint");
    }
    ConfigurationState target = state.configurations.get(result.lineage);
    if (target == null) throw reject("stale-precondition", "stale configuration lineage");
    if (!target.source.equals(result.source)
        || !target.location.equals(result.location)
        || !target.content.equals(result.content)
        || !target.body.equals(result.body)
        || !target.ensures.equals(result.ensures)
        || !target.attributes.equals(result.attributes)) {
      throw reject("stale-precondition", "stale configuration content or provenance");
    }
    if (!result.source.equals(primarySource) || !result.source.startsWith("/")) {
      throw reject("raw-provenance", "configuration source was not exact run-local absolute source");
    }
    metrics.targetLineage = result.lineage;
    metrics.targetSource = result.source;
    metrics.targetLocation = result.location;
    metrics.name = result.name;
    if (metrics.targetContentBefore.isEmpty()) {
      metrics.targetContentBefore = result.content;
      metrics.targetBodyBefore = result.body;
      metrics.operationCanonicalPass1 = result.operationCanonical();
      metrics.resultCanonicalFingerprintPass1 = sha256(result.canonical());
    } else {
      metrics.operationCanonicalPass2 = result.operationCanonical();
      metrics.resultCanonicalFingerprintPass2 = sha256(result.canonical());
    }
    return result;
  }

  private void requireValidFailure(Failure failure) {
    validateFailureEnvelope(failure);
    metrics.failureEnvelopeValidated = true;
  }

  private static void validateFailureEnvelope(Failure failure) {
    if (!failure.schema.equals(SCHEMA)) {
      throw reject("envelope", "invalid configuration failure schema");
    }
    if (!failure.reason.equals("structural-target-cardinality")
        && !failure.reason.equals("initializer-descriptor-cardinality")
        && !failure.reason.equals("conflicting-existing-state")) {
      throw reject("envelope", "unknown configuration failure reason");
    }
    if (failure.count < 0) {
      throw reject("envelope", "configuration failure count was negative");
    }
    if ((failure.reason.equals("structural-target-cardinality")
            || failure.reason.equals("initializer-descriptor-cardinality"))
        && failure.count == 1) {
      throw reject("envelope", "configuration cardinality failure count was one");
    }
    if (failure.reason.equals("conflicting-existing-state") && failure.count == 0) {
      throw reject("envelope", "configuration conflict failure count was zero");
    }
  }

  private Prepared prepare(Definition definition, DefinitionState state, Result result) {
    LocatedConfiguration located = locate(definition, primarySource, result.lineage);
    ConfigurationState target = state.configurations.get(result.lineage);
    require(located != null && target != null, "configuration disappeared before preparation");
    K parent;
    K template;
    try {
      parent = resolvePath(located.configuration.body(), result.parentPath);
      template = resolvePath(located.configuration.body(), result.templatePath);
    } catch (ValidationException error) {
      throw reject("path-operation", error.getMessage());
    }
    if (!(parent instanceof KApply parentApply)
        || !parentApply.klabel().name().equals("#cells")) {
      throw reject("path-operation", "declared parent was not an official cell bag");
    }
    if (!(template instanceof KApply templateApply)) {
      throw reject("path-operation", "declared shell template was not an application");
    }
    validateShell(templateApply);

    List<ProductionDescriptor> productions = new ArrayList<>(state.productions);
    List<SortDescriptor> sorts = new ArrayList<>(state.sorts);
    ProductionSpec declared = result.initializer instanceof ApplySpec application
        ? application.production : null;
    if (declared != null && mode.equals("config-missing-production")) {
      productions.removeIf(item -> item.matches(declared));
      metrics.inputMutationCount++;
    } else if (declared != null && mode.equals("config-ambiguous-production")) {
      productions.stream().filter(item -> item.matches(declared)).findFirst().ifPresent(productions::add);
      metrics.inputMutationCount++;
    }
    if (declared != null && mode.equals("config-missing-sort")) {
      sorts.removeIf(item -> item.matches(declared.resultSort));
      metrics.inputMutationCount++;
    } else if (declared != null && mode.equals("config-ambiguous-sort")) {
      sorts.stream().filter(item -> item.matches(declared.resultSort)).findFirst().ifPresent(sorts::add);
      metrics.inputMutationCount++;
    }
    K initializer = buildInitializer(result.initializer, productions, sorts);
    KApply expectedClone = cloneShell(templateApply, result.name, initializer);
    if (result.status.equals("apply") && countNamedCells(parentApply, result.name) != 0) {
      throw reject("path-operation", "declared same-name sibling already exists");
    }
    return new Prepared(located, parentApply, templateApply, target, initializer, expectedClone);
  }

  private static K buildInitializer(
      TermSpec spec,
      List<ProductionDescriptor> productions,
      List<SortDescriptor> sorts) {
    if (!(spec instanceof ApplySpec application)) {
      throw reject("initializer-term", "initializer was not an application");
    }
    if (!application.arguments.isEmpty()) {
      throw reject("initializer-term", "initializer was not nullary");
    }
    List<ProductionDescriptor> matches =
        productions.stream().filter(item -> item.matches(application.production)).toList();
    if (matches.size() != 1) {
      long sortOnlyMismatch = productions.stream()
          .filter(item -> item.matchesExceptResult(application.production)).count();
      if (matches.isEmpty() && sortOnlyMismatch == 1) {
        throw reject("initializer-sort", "initializer result sort did not match exact production");
      }
      throw reject("initializer-production-metadata", "initializer production count was " + matches.size());
    }
    ProductionDescriptor descriptor = matches.get(0);
    if (descriptor.production.arity() != 0 || !descriptor.argumentSorts.isEmpty()) {
      throw reject("initializer-term", "resolved initializer production was not nullary");
    }
    List<SortDescriptor> sortMatches =
        sorts.stream().filter(item -> item.matches(application.production.resultSort)).toList();
    if (sortMatches.size() != 1) {
      throw reject("initializer-sort-metadata", "initializer sort count was " + sortMatches.size());
    }
    if (!descriptor.resultSort.equals(sortMatches.get(0))) {
      throw reject("initializer-sort", "initializer production and declared sort differ");
    }
    Att att =
        Att.empty()
            .add(Att.PRODUCTION(), Production.class, descriptor.production)
            .add(Att.SORT(), Sort.class, descriptor.production.sort());
    return KApply(descriptor.production.klabel().get(), KList(), att);
  }

  private void validateAlreadyPresent(Definition definition, DefinitionState state, Result result) {
    Prepared prepared = prepare(definition, state, result);
    int named = countNamedCells(prepared.parent, result.name);
    int exact = countExactCells(
        prepared.parent, prepared.expectedClone, primarySource, primarySource);
    if (named != 1 || exact != 1) {
      throw reject("envelope", "already-present failed independent complete-clone validation");
    }
    metrics.alreadyPresentValidatedCount = 1;
  }

  private Definition applyPrepared(Definition input, Prepared prepared, K initializer) {
    KApply clone = cloneShell(prepared.template, ((Result) current).name, initializer);
    return appendClone(input, prepared, clone, (Result) current);
  }

  private Definition appendClone(
      Definition input, Prepared prepared, KApply clone, Result declaration) {
    K appended = KApply(prepared.parent.klabel(), KList(prepared.parent, clone), prepared.parent.att());
    K body = replacePath(prepared.located.configuration.body(), declaration.parentPath, appended);
    Configuration replacement =
        Configuration.apply(body, prepared.located.configuration.ensures(), prepared.located.configuration.att());
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
            "R3-G-02 generic K-authored typed configuration cell clone");
    return transformer.apply(input);
  }

  private void validateApplied(
      Definition input,
      Definition output,
      DefinitionState before,
      Result result,
      Prepared prepared) {
    DefinitionState after = DefinitionState.capture(output, primarySource, primarySource);
    require(input != output, "configuration application returned original Definition reference");
    require(before.moduleCount == after.moduleCount, "configuration changed module cardinality");
    require(before.sentenceCount == after.sentenceCount, "configuration changed sentence cardinality");
    require(before.configurationCount == after.configurationCount, "configuration changed configuration cardinality");
    require(before.nonConfiguration.equals(after.nonConfiguration), "configuration changed non-configuration content");
    require(!before.fingerprint.equals(after.fingerprint), "configuration definition fingerprint did not change");
    ConfigurationState targetAfter = after.configurations.get(result.lineage);
    require(targetAfter != null, "configuration target lineage changed");
    require(!prepared.target.content.equals(targetAfter.content), "configuration target content did not change");
    require(!prepared.target.body.equals(targetAfter.body), "configuration target body did not change");
    require(prepared.target.ensures.equals(targetAfter.ensures), "configuration ensures changed");
    require(prepared.target.attributes.equals(targetAfter.attributes), "configuration attributes changed");
    require(prepared.target.source.equals(targetAfter.source)
        && prepared.target.location.equals(targetAfter.location), "configuration provenance changed");
    int changes = 0;
    for (String lineage : before.configurations.keySet()) {
      ConfigurationState left = before.configurations.get(lineage);
      ConfigurationState right = after.configurations.get(lineage);
      require(right != null, "configuration lineage set changed");
      if (!left.content.equals(right.content)) changes++;
    }
    require(changes == 1, "changed configuration count was not one");
    LocatedConfiguration locatedAfter = locate(output, primarySource, result.lineage);
    require(locatedAfter != null
        && containsIdentity(locatedAfter.configuration.body(), prepared.parent)
        && containsIdentity(locatedAfter.configuration.body(), prepared.template),
        "original configuration nodes were not preserved by immutable rebuild");
    int exact = countExactCells(
        locatedAfter.configuration.body(), prepared.expectedClone, primarySource, primarySource);
    require(exact == 1, "complete expected clone was not installed exactly once");
    KApply installed = findExactCell(
        locatedAfter.configuration.body(), prepared.expectedClone, primarySource, primarySource);
    require(installed != null, "installed complete clone disappeared after application");
    metrics.expectedCloneFingerprint = completeTermFingerprint(
        prepared.expectedClone, primarySource, primarySource);
    metrics.installedCellFingerprint = completeTermFingerprint(
        installed, primarySource, primarySource);
    require(metrics.expectedCloneFingerprint.equals(metrics.installedCellFingerprint),
        "raw expected and installed clone fingerprints differed");
    metrics.changedConfigurationCount = changes;
    metrics.metadataPreserved = true;
    metrics.conditionsPreserved = true;
    metrics.provenancePreserved = true;
    metrics.originalNodesPreserved = true;
    metrics.targetContentAfter = targetAfter.content;
    metrics.targetBodyAfter = targetAfter.body;
    metrics.initializerCanonical = ((Result) current).initializer.canonical();
  }

  private void capturePortableEvidence(
      Definition input,
      Definition output,
      DefinitionState rawBefore,
      DefinitionState rawAfter,
      Result rawPass1,
      Result rawPass2) {
    DefinitionState portableBefore =
        DefinitionState.capture(input, primarySource, portableSource);
    DefinitionState portableAfter =
        DefinitionState.capture(output, primarySource, portableSource);
    List<ConfigurationState> candidates =
        portableBefore.configurations.values().stream()
            .filter(item -> item.module.equals(rawBefore.configurations.get(rawPass1.lineage).module)
                && item.location.equals(rawPass1.location))
            .toList();
    require(candidates.size() == 1, "portable configuration target mapping was not unique");
    ConfigurationState target = candidates.get(0);
    ConfigurationState targetAfter = portableAfter.configurations.get(target.lineage);
    require(targetAfter != null, "portable augmented configuration disappeared");
    Result portablePass1 = portableResult(rawPass1, rawBefore, portableBefore, target);
    Result portablePass2 = portableResult(rawPass2, rawAfter, portableAfter, targetAfter);
    Request request1 = Projection.encode(input, portableBefore, primarySource, portableSource, "apply");
    Request request2 = Projection.encode(output, portableAfter, primarySource, portableSource, "apply");
    require(!request1.program.contains(primarySource) && !request2.program.contains(primarySource),
        "portable configuration request retained raw source");
    require(!portablePass1.canonical().contains(primarySource)
        && !portablePass2.canonical().contains(primarySource),
        "portable configuration result retained raw source");
    metrics.portableBeforeDefinition = portableBefore.fingerprint;
    metrics.portableAfterDefinition = portableAfter.fingerprint;
    metrics.portableRequestFingerprintPass1 = request1.fingerprint;
    metrics.portableRequestFingerprintPass2 = request2.fingerprint;
    metrics.portableResponseFingerprintPass1 = sha256(portablePass1.canonical());
    metrics.portableResponseFingerprintPass2 = sha256(portablePass2.canonical());
    metrics.portableOperationCanonicalPass1 = portablePass1.operationCanonical();
    metrics.portableOperationCanonicalPass2 = portablePass2.operationCanonical();
    metrics.portableTargetLineage = target.lineage;
    metrics.portableTargetSource = target.source;
    metrics.portableTargetLocation = target.location;
    metrics.portableTargetContentBefore = target.content;
    metrics.portableTargetContentAfter = targetAfter.content;
    metrics.portableTargetBodyBefore = target.body;
    metrics.portableTargetBodyAfter = targetAfter.body;
    metrics.portableInitializerCanonical = portablePass1.initializer.canonical();
    LocatedConfiguration rawBeforeLocated = locate(input, primarySource, rawPass1.lineage);
    LocatedConfiguration rawAfterLocated = locate(output, primarySource, rawPass2.lineage);
    require(rawBeforeLocated != null && rawAfterLocated != null,
        "portable complete-clone configuration mapping disappeared");
    K rawTemplate = resolvePath(rawBeforeLocated.configuration.body(), rawPass1.templatePath);
    K rawParentAfter = resolvePath(rawAfterLocated.configuration.body(), rawPass2.parentPath);
    require(rawTemplate instanceof KApply && rawParentAfter instanceof KApply,
        "portable complete-clone paths were not applications");
    K portableInitializer = buildInitializer(rawPass1.initializer, rawBefore.productions, rawBefore.sorts);
    KApply portableExpected = cloneShell((KApply) rawTemplate, rawPass1.name, portableInitializer);
    KApply portableInstalled = findExactCell(
        rawParentAfter, portableExpected, primarySource, portableSource);
    require(portableInstalled != null, "portable installed complete clone was not unique");
    metrics.portableExpectedCloneFingerprint = completeTermFingerprint(
        portableExpected, primarySource, portableSource);
    metrics.portableInstalledCellFingerprint = completeTermFingerprint(
        portableInstalled, primarySource, portableSource);
    require(metrics.portableExpectedCloneFingerprint.equals(metrics.portableInstalledCellFingerprint),
        "portable expected and installed clone fingerprints differed");
    metrics.portableEvidenceProjected = true;
    metrics.portableOrderingValidated = Projection.hasPortableOrdering(input, primarySource, portableSource)
        && Projection.hasPortableOrdering(output, primarySource, portableSource);
    require(metrics.portableOrderingValidated, "portable configurations were not ordered by portable lineage");
  }

  private static Result portableResult(
      Result raw,
      DefinitionState rawState,
      DefinitionState portableState,
      ConfigurationState target) {
    return new Result(
        raw.schema,
        raw.transformation,
        portableState.fingerprint,
        raw.candidateCount,
        raw.status,
        target.lineage,
        target.source,
        target.location,
        target.content,
        target.body,
        target.ensures,
        target.attributes,
        raw.parentPath,
        raw.templatePath,
        raw.name,
        portableTerm(raw.initializer, rawState, portableState));
  }

  private static TermSpec portableTerm(
      TermSpec term, DefinitionState raw, DefinitionState portable) {
    if (term instanceof VariableSpec variable) {
      return new VariableSpec(variable.name, portableSort(variable.sort, raw, portable));
    }
    if (term instanceof TokenSpec token) {
      return new TokenSpec(portableSort(token.sort, raw, portable), token.value, token.lexeme);
    }
    ApplySpec application = (ApplySpec) term;
    return new ApplySpec(
        portableProduction(application.production, raw, portable),
        application.arguments.stream().map(item -> portableTerm(item, raw, portable)).toList());
  }

  private static SortSpec portableSort(SortSpec value, DefinitionState raw, DefinitionState portable) {
    List<SortDescriptor> rawMatches = raw.sorts.stream().filter(item -> item.matches(value)).toList();
    require(rawMatches.size() == 1, "portable sort source mapping was not unique");
    List<SortDescriptor> matches = portable.sorts.stream()
        .filter(item -> item.name.equals(rawMatches.get(0).name)).toList();
    require(matches.size() == 1, "portable sort target mapping was not unique");
    return matches.get(0).spec();
  }

  private static ProductionSpec portableProduction(
      ProductionSpec value, DefinitionState raw, DefinitionState portable) {
    List<ProductionDescriptor> rawMatches =
        raw.productions.stream().filter(item -> item.matches(value)).toList();
    require(rawMatches.size() == 1, "portable production source mapping was not unique");
    List<ProductionDescriptor> matches = portable.productions.stream()
        .filter(item -> item.production == rawMatches.get(0).production).toList();
    require(matches.size() == 1, "portable production target mapping was not unique");
    return matches.get(0).spec();
  }

  private static void validateShell(KApply shell) {
    List<K> items = shell.klist().items();
    if (!shell.klabel().name().equals("#configCell") || items.size() != 4) {
      throw reject("path-operation", "template was not a four-argument official cell shell");
    }
    if (!(items.get(0) instanceof KToken start)
        || !(items.get(3) instanceof KToken end)
        || !start.s().equals(end.s())
        || !start.sort().equals(end.sort())) {
      throw reject("path-operation", "template cell names were not matching typed tokens");
    }
    if (containsCellShell(items.get(2))) {
      throw reject("path-operation", "template was not a leaf-cell shell");
    }
  }

  private static boolean containsCellShell(K root) {
    boolean[] found = {false};
    new VisitK() {
      @Override public void apply(KApply application) {
        if (application.klabel().name().equals("#configCell")) found[0] = true;
        super.apply(application);
      }
    }.apply(root);
    return found[0];
  }

  private static KApply cloneShell(KApply template, String name, K initializer) {
    require(!name.isBlank(), "K declared a blank cell name");
    List<K> items = new ArrayList<>(template.klist().items());
    KToken start = (KToken) items.get(0);
    KToken end = (KToken) items.get(3);
    items.set(0, KToken(name, start.sort(), start.att()));
    items.set(2, initializer);
    items.set(3, KToken(name, end.sort(), end.att()));
    return KApply(template.klabel(), KList(items), template.att());
  }

  private static KApply alterCloneProperties(KApply clone) {
    List<K> items = new ArrayList<>(clone.klist().items());
    K property = items.get(1);
    items.set(1, org.kframework.kore.KORE.KSequence(List.of(property), property.att()));
    return KApply(clone.klabel(), KList(items), clone.att());
  }

  private record Prepared(
      LocatedConfiguration located,
      KApply parent,
      KApply template,
      ConfigurationState target,
      K initializer,
      KApply expectedClone) {}

  private record LocatedConfiguration(Module module, Configuration configuration) {}

  private static LocatedConfiguration locate(
      Definition definition, String source, String lineage) {
    for (Module module : stream(definition.modules()).toList()) {
      for (Configuration configuration : stream(module.localSentences())
          .filter(Configuration.class::isInstance).map(Configuration.class::cast).toList()) {
        if (configuration.source().map(item -> item.source()).orElse("").equals(source)
            && ConfigurationState.lineage(module.name(), configuration, source).equals(lineage)) {
          return new LocatedConfiguration(module, configuration);
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
    if (!(root instanceof KApply application)) {
      throw new ValidationException("replace path reached non-application");
    }
    int index = path.indices.get(0);
    if (index < 0 || index >= application.klist().size()) {
      throw new ValidationException("replace path index out of bounds");
    }
    List<K> items = new ArrayList<>(application.klist().items());
    items.set(index, replacePath(items.get(index),
        new TermPath(path.indices.subList(1, path.indices.size())), replacement));
    return KApply(application.klabel(), KList(items), application.att());
  }

  private static int countNamedCells(K root, String name) {
    int[] count = {0};
    new VisitK() {
      @Override public void apply(KApply application) {
        List<K> items = application.klist().items();
        if (application.klabel().name().equals("#configCell")
            && items.size() == 4
            && items.get(0) instanceof KToken token
            && token.s().equals(name)) count[0]++;
        super.apply(application);
      }
    }.apply(root);
    return count[0];
  }

  private static boolean sameCompleteTerm(
      K left, K right, String primarySource, String representedSource) {
    return Projection.encodeTerm(left, primarySource, representedSource)
        .equals(Projection.encodeTerm(right, primarySource, representedSource));
  }

  private static String completeTermFingerprint(
      K value, String primarySource, String representedSource) {
    return sha256(Projection.encodeTerm(value, primarySource, representedSource));
  }

  private static int countExactCells(
      K root, KApply expected, String primarySource, String representedSource) {
    int[] count = {0};
    new VisitK() {
      @Override public void apply(KApply application) {
        if (sameCompleteTerm(application, expected, primarySource, representedSource)) count[0]++;
        super.apply(application);
      }
    }.apply(root);
    return count[0];
  }

  private static KApply findExactCell(
      K root, KApply expected, String primarySource, String representedSource) {
    KApply[] found = {null};
    new VisitK() {
      @Override public void apply(KApply application) {
        if (sameCompleteTerm(application, expected, primarySource, representedSource)) {
          if (found[0] != null) throw reject("envelope", "multiple complete expected clones found");
          found[0] = application;
        }
        super.apply(application);
      }
    }.apply(root);
    return found[0];
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

  private record Request(String program, String fingerprint) {}

  private static final class Projection {
    private static List<Configuration> orderedConfigurations(
        Module module, String representedSource) {
      return stream(module.localSentences())
          .filter(Configuration.class::isInstance)
          .map(Configuration.class::cast)
          .sorted(Comparator.comparing(
              item -> ConfigurationState.lineage(module.name(), item, representedSource)))
          .toList();
    }

    static boolean isCanonicalOrder(List<String> values) {
      return values.equals(values.stream().sorted().toList());
    }

    static boolean hasPortableOrdering(
        Definition definition, String primarySource, String representedSource) {
      for (Module module : stream(definition.modules()).toList()) {
        List<String> lineages = orderedConfigurations(module, representedSource).stream()
            .map(item -> ConfigurationState.lineage(module.name(), item, representedSource))
            .toList();
        if (!isCanonicalOrder(lineages)) return false;
      }
      return true;
    }

    static Request encode(
        Definition definition,
        DefinitionState state,
        String primarySource,
        String representedSource,
        String mode) {
      List<String> modules = new ArrayList<>();
      for (Module module : stream(definition.modules()).sorted(Comparator.comparing(Module::name)).toList()) {
        List<Configuration> configurations = orderedConfigurations(module, representedSource);
        List<String> encoded = new ArrayList<>();
        for (Configuration configuration : configurations) {
          ConfigurationState item = ConfigurationState.capture(
              module.name(), configuration, primarySource, representedSource);
          encoded.add("cConfiguration("
              + quote(module.name()) + "," + quote("Configuration") + ","
              + quote(item.source) + "," + quote(item.location) + ","
              + quote(item.lineage) + "," + quote(item.content) + ","
              + quote(item.body) + "," + quote(item.ensures) + ","
              + quote(item.attributes) + ","
              + encodeTerm(configuration.body(), primarySource, representedSource) + ")");
        }
        modules.add("cModule(" + quote(module.name()) + ","
            + list("cConfigurationNil", "cConfigurationCons", encoded) + ")");
      }
      List<String> productions = state.productions.stream()
          .map(item -> production(item.spec())).toList();
      List<String> sorts = state.sorts.stream().map(item -> sort(item.spec())).toList();
      String definitionTerm = "cDefinition(" + quote(SCHEMA) + ","
          + quote(state.fingerprint) + ","
          + list("cModuleNil", "cModuleCons", modules) + ","
          + list("cProductionNil", "cProductionCons", productions) + ","
          + list("cSortNil", "cSortCons", sorts) + ")";
      return new Request(
          "proposeTraceConfigurationAugmentation(" + quote(mode) + "," + definitionTerm + ")\n",
          sha256(definitionTerm));
    }

    static String encodeTerm(K value, String primarySource, String representedSource) {
      String metadata = encodeMeta(value, primarySource, representedSource);
      if (value instanceof KApply application) {
        return "cApply(" + quote(application.klabel().name()) + ","
            + list("cTermNil", "cTermCons", application.klist().items().stream()
                .map(item -> encodeTerm(item, primarySource, representedSource)).toList())
            + "," + metadata + ")";
      }
      if (value instanceof KToken token) {
        return "cToken(" + quote(token.sort().toString()) + ","
            + quote(replaceSource(token.s(), primarySource, representedSource)) + ","
            + metadata + ")";
      }
      if (value instanceof KVariable variable) {
        return "cVariable(" + quote(variable.name()) + "," + metadata + ")";
      }
      if (value instanceof KRewrite rewrite) {
        return "cRewrite(" + encodeTerm(rewrite.left(), primarySource, representedSource) + ","
            + encodeTerm(rewrite.right(), primarySource, representedSource) + "," + metadata + ")";
      }
      if (value instanceof KSequence sequence) {
        return "cSequence(" + list("cTermNil", "cTermCons", sequence.items().stream()
            .map(item -> encodeTerm(item, primarySource, representedSource)).toList())
            + "," + metadata + ")";
      }
      if (value instanceof KAs alias) {
        return "cAs(" + encodeTerm(alias.pattern(), primarySource, representedSource) + ","
            + encodeTerm(alias.alias(), primarySource, representedSource) + "," + metadata + ")";
      }
      if (value instanceof InjectedKLabel injected) {
        return "cInjectedLabel(" + quote(injected.klabel().name()) + "," + metadata + ")";
      }
      throw reject("request-encoding", "unsupported typed configuration node: " + value.getClass());
    }

    private static String encodeMeta(K value, String primarySource, String representedSource) {
      Att att = value.att();
      String sort = att.getOptional(Att.SORT(), Sort.class).map(Object::toString).orElse("");
      String production = att.getOptional(Att.PRODUCTION(), Production.class).map(Object::toString).orElse("");
      if (value instanceof KToken token) sort = token.sort().toString();
      return "cMeta(" + quote(sort) + ","
          + quote(sha256(replaceSource(production, primarySource, representedSource))) + ","
          + quote(sha256(replaceSource(att.toString(), primarySource, representedSource))) + ")";
    }

    private static String production(ProductionSpec value) {
      return "cProduction(" + quote(value.module) + "," + quote(value.label) + ","
          + sort(value.resultSort) + ","
          + list("cSortNil", "cSortCons", value.argumentSorts.stream().map(Projection::sort).toList()) + ","
          + quote(value.productionFingerprint) + "," + quote(value.labelFingerprint) + ","
          + quote(value.metadataFingerprint) + ")";
    }

    private static String sort(SortSpec value) {
      return "cSort(" + quote(value.name) + "," + quote(value.fingerprint) + ")";
    }

    private static String list(String nil, String cons, List<String> values) {
      String result = nil;
      for (int index = values.size() - 1; index >= 0; index--) {
        result = cons + "(" + values.get(index) + "," + result + ")";
      }
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
      String source,
      String location,
      String content,
      String body,
      String ensures,
      String attributes,
      TermPath parentPath,
      TermPath templatePath,
      String name,
      TermSpec initializer) implements Outcome {
    @Override public int count() { return candidateCount; }
    String operationCanonical() {
      return "cloneLeafCellWithTypedContentFromInput(" + parentPath.canonical() + ","
          + templatePath.canonical() + "," + quote(name) + "," + initializer.canonical() + ")";
    }
    @Override public String canonical() {
      return "cTraceAugmentationResult(" + quote(schema) + "," + quote(transformation) + ","
          + quote(definitionFingerprint) + "," + candidateCount + "," + quote(status) + ","
          + quote(lineage) + "," + quote(source) + "," + quote(location) + ","
          + quote(content) + "," + quote(body) + "," + quote(ensures) + ","
          + quote(attributes) + "," + operationCanonical() + ")";
    }
  }

  private record Failure(String schema, String reason, int count) implements Outcome {
    @Override public String status() { return "failure:" + reason; }
    @Override public String canonical() {
      return "cTraceAugmentationFailure(" + quote(schema) + "," + quote(reason) + "," + count + ")";
    }
  }

  private record Invocation(Request request, Outcome outcome) {}

  private record TermPath(List<Integer> indices) {
    String canonical() {
      String result = "cPathNil";
      for (int index = indices.size() - 1; index >= 0; index--) {
        result = "cPathCons(cApplicationArgument(" + indices.get(index) + ")," + result + ")";
      }
      return result;
    }
  }

  private record SortSpec(String name, String fingerprint) {
    String canonical() { return "cSort(" + quote(name) + "," + quote(fingerprint) + ")"; }
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
      String arguments = "cSortNil";
      for (int index = argumentSorts.size() - 1; index >= 0; index--) {
        arguments = "cSortCons(" + argumentSorts.get(index).canonical() + "," + arguments + ")";
      }
      return "cProduction(" + quote(module) + "," + quote(label) + ","
          + resultSort.canonical() + "," + arguments + ","
          + quote(productionFingerprint) + "," + quote(labelFingerprint) + ","
          + quote(metadataFingerprint) + ")";
    }
  }

  private sealed interface TermSpec permits ApplySpec, TokenSpec, VariableSpec {
    String canonical();
  }

  private record ApplySpec(ProductionSpec production, List<TermSpec> arguments)
      implements TermSpec {
    @Override public String canonical() {
      String values = "tTermNil";
      for (int index = arguments.size() - 1; index >= 0; index--) {
        values = "tTermCons(" + arguments.get(index).canonical() + "," + values + ")";
      }
      return "tApply(" + production.canonical() + "," + values + ")";
    }
  }

  private record TokenSpec(SortSpec sort, String value, String lexeme) implements TermSpec {
    @Override public String canonical() {
      return "tToken(" + sort.canonical() + "," + quote(value) + "," + quote(lexeme) + ")";
    }
  }

  private record VariableSpec(String name, SortSpec sort) implements TermSpec {
    @Override public String canonical() {
      return "tVariable(" + quote(name) + "," + sort.canonical() + ")";
    }
  }

  private static final class ResultParser {
    static Outcome parse(String output) {
      Reader reader = new Reader(output);
      reader.expect("<k>");
      String constructor = reader.identifier();
      Outcome result;
      if (constructor.equals("cTraceAugmentationFailure")) {
        reader.expect('(');
        String schema = reader.string(); reader.expect(',');
        String reason = reader.string(); reader.expect(',');
        int count = reader.integer(); reader.expect(')');
        result = new Failure(schema, reason, count);
      } else if (constructor.equals("cTraceAugmentationResult")) {
        reader.expect('(');
        String schema = reader.string(); reader.expect(',');
        String transformation = reader.string(); reader.expect(',');
        String definition = reader.string(); reader.expect(',');
        int count = reader.integer(); reader.expect(',');
        String status = reader.string(); reader.expect(',');
        String lineage = reader.string(); reader.expect(',');
        String source = reader.string(); reader.expect(',');
        String location = reader.string(); reader.expect(',');
        String content = reader.string(); reader.expect(',');
        String body = reader.string(); reader.expect(',');
        String ensures = reader.string(); reader.expect(',');
        String attributes = reader.string(); reader.expect(',');
        reader.expectIdentifier("cloneLeafCellWithTypedContentFromInput"); reader.expect('(');
        TermPath parent = path(reader); reader.expect(',');
        TermPath template = path(reader); reader.expect(',');
        String name = reader.string(); reader.expect(',');
        TermSpec initializer = term(reader); reader.expect(')'); reader.expect(')');
        result = new Result(schema, transformation, definition, count, status, lineage,
            source, location, content, body, ensures, attributes, parent, template, name, initializer);
      } else {
        throw reject("envelope", "unexpected configuration result constructor: " + constructor);
      }
      reader.expect("~>"); reader.expect(".K"); reader.expect("</k>"); reader.end();
      return result;
    }

    private static TermPath path(Reader reader) {
      String constructor = reader.identifier();
      if (constructor.equals("cPathNil")) return new TermPath(List.of());
      if (!constructor.equals("cPathCons")) throw reject("envelope", "unexpected path constructor");
      reader.expect('('); reader.expectIdentifier("cApplicationArgument"); reader.expect('(');
      int index = reader.integer(); reader.expect(')'); reader.expect(',');
      TermPath rest = path(reader); reader.expect(')');
      List<Integer> values = new ArrayList<>(); values.add(index); values.addAll(rest.indices);
      return new TermPath(List.copyOf(values));
    }

    private static SortSpec sort(Reader reader) {
      reader.expectIdentifier("cSort"); reader.expect('(');
      String name = reader.string(); reader.expect(',');
      String fingerprint = reader.string(); reader.expect(')');
      return new SortSpec(name, fingerprint);
    }

    private static ProductionSpec production(Reader reader) {
      reader.expectIdentifier("cProduction"); reader.expect('(');
      String module = reader.string(); reader.expect(',');
      String label = reader.string(); reader.expect(',');
      SortSpec result = sort(reader); reader.expect(',');
      List<SortSpec> arguments = sorts(reader); reader.expect(',');
      String production = reader.string(); reader.expect(',');
      String labelFingerprint = reader.string(); reader.expect(',');
      String metadata = reader.string(); reader.expect(')');
      return new ProductionSpec(module, label, result, arguments,
          production, labelFingerprint, metadata);
    }

    private static List<SortSpec> sorts(Reader reader) {
      String constructor = reader.identifier();
      if (constructor.equals("cSortNil")) return List.of();
      if (!constructor.equals("cSortCons")) throw reject("envelope", "unexpected sort-list constructor");
      reader.expect('('); SortSpec first = sort(reader); reader.expect(',');
      List<SortSpec> rest = sorts(reader); reader.expect(')');
      List<SortSpec> result = new ArrayList<>(); result.add(first); result.addAll(rest);
      return List.copyOf(result);
    }

    private static TermSpec term(Reader reader) {
      String constructor = reader.identifier();
      if (constructor.equals("tApply")) {
        reader.expect('('); ProductionSpec production = production(reader); reader.expect(',');
        List<TermSpec> arguments = terms(reader); reader.expect(')');
        return new ApplySpec(production, arguments);
      }
      if (constructor.equals("tToken")) {
        reader.expect('('); SortSpec sort = sort(reader); reader.expect(',');
        String value = reader.string(); reader.expect(','); String lexeme = reader.string(); reader.expect(')');
        return new TokenSpec(sort, value, lexeme);
      }
      if (constructor.equals("tVariable")) {
        reader.expect('('); String name = reader.string(); reader.expect(',');
        SortSpec sort = sort(reader); reader.expect(')'); return new VariableSpec(name, sort);
      }
      throw reject("envelope", "unexpected typed initializer constructor");
    }

    private static List<TermSpec> terms(Reader reader) {
      String constructor = reader.identifier();
      if (constructor.equals("tTermNil")) return List.of();
      if (!constructor.equals("tTermCons")) throw reject("envelope", "unexpected term-list constructor");
      reader.expect('('); TermSpec first = term(reader); reader.expect(',');
      List<TermSpec> rest = terms(reader); reader.expect(')');
      List<TermSpec> result = new ArrayList<>(); result.add(first); result.addAll(rest);
      return List.copyOf(result);
    }
  }

  private static final class Reader {
    final String input;
    int offset;
    Reader(String input) { this.input = input; }
    void skip() { while (offset < input.length() && Character.isWhitespace(input.charAt(offset))) offset++; }
    void expect(String value) {
      skip();
      if (!input.startsWith(value, offset)) throw reject("envelope", "expected " + value + " at " + offset);
      offset += value.length();
    }
    void expect(char value) {
      skip();
      if (offset >= input.length() || input.charAt(offset) != value) {
        throw reject("envelope", "expected " + value + " at " + offset);
      }
      offset++;
    }
    void expectIdentifier(String value) {
      String actual = identifier();
      if (!actual.equals(value)) throw reject("envelope", "expected " + value + ", found " + actual);
    }
    String identifier() {
      skip(); int start = offset;
      while (offset < input.length()
          && (Character.isLetterOrDigit(input.charAt(offset))
              || input.charAt(offset) == '_' || input.charAt(offset) == '#')) offset++;
      if (start == offset) throw reject("envelope", "expected constructor at " + offset);
      return input.substring(start, offset);
    }
    int integer() {
      skip(); int start = offset;
      if (offset < input.length() && input.charAt(offset) == '-') offset++;
      int digits = offset;
      while (offset < input.length() && Character.isDigit(input.charAt(offset))) offset++;
      if (digits == offset) throw reject("envelope", "invalid integer");
      String encoded = input.substring(start, offset);
      try {
        int value = Integer.parseInt(encoded);
        if (!encoded.equals(Integer.toString(value))) throw reject("envelope", "noncanonical integer");
        return value;
      } catch (NumberFormatException error) {
        throw reject("envelope", "invalid integer");
      }
    }
    String string() {
      skip(); int start = offset;
      if (offset >= input.length() || input.charAt(offset++) != '"') {
        throw reject("envelope", "expected string");
      }
      StringBuilder out = new StringBuilder();
      while (offset < input.length()) {
        char ch = input.charAt(offset++);
        if (ch == '"') {
          String value = out.toString();
          if (!input.substring(start, offset).equals(quote(value))) {
            throw reject("envelope", "noncanonical string");
          }
          return value;
        }
        if (ch != '\\') { out.append(ch); continue; }
        if (offset >= input.length()) throw reject("envelope", "bad string escape");
        char escaped = input.charAt(offset++);
        switch (escaped) {
          case '"' -> out.append('"'); case '\\' -> out.append('\\');
          case 'n' -> out.append('\n'); case 'r' -> out.append('\r'); case 't' -> out.append('\t');
          case 'b' -> out.append('\b'); case 'f' -> out.append('\f');
          case 'u' -> {
            if (offset + 4 > input.length()) throw reject("envelope", "bad string escape");
            try { out.append((char) Integer.parseInt(input.substring(offset, offset + 4), 16)); }
            catch (NumberFormatException error) { throw reject("envelope", "bad string escape"); }
            offset += 4;
          }
          default -> throw reject("envelope", "bad string escape");
        }
      }
      throw reject("envelope", "unterminated string");
    }
    void end() { skip(); if (offset != input.length()) throw reject("envelope", "residual K result"); }
  }

  private static final class DefinitionState {
    final String fingerprint;
    final String nonConfiguration;
    final int moduleCount;
    final int sentenceCount;
    final int configurationCount;
    final Map<String, ConfigurationState> configurations;
    final List<ProductionDescriptor> productions;
    final List<SortDescriptor> sorts;

    DefinitionState(
        String fingerprint,
        String nonConfiguration,
        int moduleCount,
        int sentenceCount,
        Map<String, ConfigurationState> configurations,
        List<ProductionDescriptor> productions,
        List<SortDescriptor> sorts) {
      this.fingerprint = fingerprint;
      this.nonConfiguration = nonConfiguration;
      this.moduleCount = moduleCount;
      this.sentenceCount = sentenceCount;
      this.configurationCount = configurations.size();
      this.configurations = configurations;
      this.productions = productions;
      this.sorts = sorts;
    }

    static DefinitionState capture(
        Definition definition, String primarySource, String representedSource) {
      StringBuilder graph = new StringBuilder("definition|")
          .append(replaceSource(definition.att().toString(), primarySource, representedSource))
          .append('|').append(definition.mainModule().name()).append('\n');
      StringBuilder non = new StringBuilder();
      Map<String, ConfigurationState> configs = new LinkedHashMap<>();
      List<ProductionDescriptor> productions = new ArrayList<>();
      Map<String, SortDescriptor> sorts = new LinkedHashMap<>();
      int sentences = 0;
      List<Module> modules = stream(definition.modules()).sorted(Comparator.comparing(Module::name)).toList();
      for (Module module : modules) {
        graph.append("module|").append(module.name()).append('|')
            .append(replaceSource(module.att().toString(), primarySource, representedSource)).append('\n');
        stream(module.imports()).map(item -> item.module().name() + "|" + item.isPublic())
            .sorted().forEach(item -> graph.append("import|").append(item).append('\n'));
        List<Sentence> local = stream(module.localSentences())
            .sorted(Comparator.comparing(item -> item.getClass().getName() + "|"
                + replaceSource(item.toString(), primarySource, representedSource) + "|"
                + replaceSource(item.att().toString(), primarySource, representedSource)))
            .toList();
        sentences += local.size();
        for (Sentence sentence : local) {
          if (sentence instanceof Configuration configuration) {
            ConfigurationState state = ConfigurationState.capture(
                module.name(), configuration, primarySource, representedSource);
            if (configs.put(state.lineage, state) != null) {
              throw reject("request-encoding", "duplicate portable configuration lineage");
            }
          } else {
            non.append(module.name()).append('|').append(sentence.getClass().getName()).append('|')
                .append(replaceSource(sentence.toString(), primarySource, representedSource)).append('|')
                .append(replaceSource(sentence.att().toString(), primarySource, representedSource)).append('\n');
          }
          if (sentence instanceof Production production) {
            SortDescriptor result = SortDescriptor.capture(production.sort());
            sorts.putIfAbsent(result.canonical(), result);
            for (int index = 0; index < production.arity(); index++) {
              SortDescriptor argument = SortDescriptor.capture(production.nonterminal(index).sort());
              sorts.putIfAbsent(argument.canonical(), argument);
            }
            if (production.klabel().isDefined()) {
              productions.add(ProductionDescriptor.capture(
                  module.name(), production, primarySource, representedSource));
            }
          }
        }
      }
      productions.sort(Comparator.comparing(ProductionDescriptor::canonical));
      List<SortDescriptor> canonicalSorts = sorts.values().stream()
          .sorted(Comparator.comparing(SortDescriptor::canonical)).toList();
      String nonHash = sha256(non.toString());
      String fingerprint = sha256(graph + "|" + nonHash + "|"
          + configs.values().stream().map(item -> item.content).sorted().collect(Collectors.joining("|")));
      return new DefinitionState(fingerprint, nonHash, modules.size(), sentences,
          Map.copyOf(configs), List.copyOf(productions), canonicalSorts);
    }
  }

  private record ConfigurationState(
      String module,
      String source,
      String location,
      String lineage,
      String content,
      String body,
      String ensures,
      String attributes) {
    static ConfigurationState capture(
        String module,
        Configuration value,
        String primarySource,
        String representedSource) {
      String source = replaceSource(
          value.source().map(item -> item.source()).orElse(""), primarySource, representedSource);
      String location = value.location().map(Object::toString).orElse("");
      String lineage = lineage(module, value, representedSource);
      String body = sha256(Projection.encodeTerm(value.body(), primarySource, representedSource));
      String ensures = sha256(Projection.encodeTerm(value.ensures(), primarySource, representedSource));
      String attributes = sha256(replaceSource(value.att().toString(), primarySource, representedSource));
      String content = sha256(lineage + "|" + body + "|" + ensures + "|" + attributes);
      return new ConfigurationState(module, source, location, lineage, content, body, ensures, attributes);
    }
    static String lineage(String module, Configuration value, String representedSource) {
      return sha256(module + "|Configuration|" + representedSource + "|"
          + value.location().map(Object::toString).orElse(""));
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
    static ProductionDescriptor capture(
        String module, Production production, String primarySource, String representedSource) {
      List<SortDescriptor> arguments = new ArrayList<>();
      for (int index = 0; index < production.arity(); index++) {
        arguments.add(SortDescriptor.capture(production.nonterminal(index).sort()));
      }
      String label = production.klabel().get().name();
      Att initializerNodeAtt =
          Att.empty()
              .add(Att.PRODUCTION(), Production.class, production)
              .add(Att.SORT(), Sort.class, production.sort());
      return new ProductionDescriptor(
          module,
          label,
          SortDescriptor.capture(production.sort()),
          List.copyOf(arguments),
          sha256(replaceSource(module + "|" + production + "|" + production.att(), primarySource, representedSource)),
          sha256(replaceSource(production.toString(), primarySource, representedSource)),
          sha256(replaceSource(initializerNodeAtt.toString(), primarySource, representedSource)),
          production);
    }
    String canonical() {
      return module + "|" + label + "|" + resultSort.canonical() + "|"
          + argumentSorts.stream().map(SortDescriptor::canonical).collect(Collectors.joining(","))
          + "|" + productionFingerprint + "|" + labelFingerprint + "|" + metadataFingerprint;
    }
    ProductionSpec spec() {
      return new ProductionSpec(module, label, resultSort.spec(),
          argumentSorts.stream().map(SortDescriptor::spec).toList(),
          productionFingerprint, labelFingerprint, metadataFingerprint);
    }
    boolean matches(ProductionSpec value) {
      return module.equals(value.module)
          && label.equals(value.label)
          && resultSort.matches(value.resultSort)
          && argumentSorts.size() == value.argumentSorts.size()
          && java.util.stream.IntStream.range(0, argumentSorts.size())
              .allMatch(index -> argumentSorts.get(index).matches(value.argumentSorts.get(index)))
          && productionFingerprint.equals(value.productionFingerprint)
          && labelFingerprint.equals(value.labelFingerprint)
          && metadataFingerprint.equals(value.metadataFingerprint);
    }
    boolean matchesExceptResult(ProductionSpec value) {
      return module.equals(value.module)
          && label.equals(value.label)
          && argumentSorts.size() == value.argumentSorts.size()
          && java.util.stream.IntStream.range(0, argumentSorts.size())
              .allMatch(index -> argumentSorts.get(index).matches(value.argumentSorts.get(index)))
          && productionFingerprint.equals(value.productionFingerprint)
          && labelFingerprint.equals(value.labelFingerprint)
          && metadataFingerprint.equals(value.metadataFingerprint);
    }
  }

  private record SortDescriptor(String name, String fingerprint, Sort sort) {
    static SortDescriptor capture(Sort sort) {
      String name = sort.toString();
      return new SortDescriptor(name, sha256(name), sort);
    }
    String canonical() { return name + "|" + fingerprint; }
    SortSpec spec() { return new SortSpec(name, fingerprint); }
    boolean matches(SortSpec value) {
      return name.equals(value.name) && fingerprint.equals(value.fingerprint);
    }
  }

  static final class Metrics {
    String classification = "", error = "";
    String beforeDefinition = "", afterDefinition = "";
    String requestFingerprintPass1 = "", requestFingerprintPass2 = "";
    String responseFingerprintPass1 = "", responseFingerprintPass2 = "";
    String statusPass1 = "", statusPass2 = "";
    String targetLineage = "", targetSource = "", targetLocation = "";
    String targetContentBefore = "", targetContentAfter = "";
    String targetBodyBefore = "", targetBodyAfter = "";
    String operationCanonicalPass1 = "", operationCanonicalPass2 = "";
    String resultCanonicalFingerprintPass1 = "", resultCanonicalFingerprintPass2 = "";
    String name = "", initializerCanonical = "";
    String expectedCloneFingerprint = "", installedCellFingerprint = "";
    String failureCanonical = "", failureSchema = "", failureReason = "";
    String portableBeforeDefinition = "", portableAfterDefinition = "";
    String portableRequestFingerprintPass1 = "", portableRequestFingerprintPass2 = "";
    String portableResponseFingerprintPass1 = "", portableResponseFingerprintPass2 = "";
    String portableOperationCanonicalPass1 = "", portableOperationCanonicalPass2 = "";
    String portableTargetLineage = "", portableTargetSource = "", portableTargetLocation = "";
    String portableTargetContentBefore = "", portableTargetContentAfter = "";
    String portableTargetBodyBefore = "", portableTargetBodyAfter = "";
    String portableInitializerCanonical = "";
    String portableExpectedCloneFingerprint = "", portableInstalledCellFingerprint = "";
    int hookInvocations, kInvocationsPass1, kInvocationsPass2;
    int candidateCountPass1, candidateCountPass2;
    int validatedOperationCount, applicationCount, changedConfigurationCount;
    int alreadyPresentValidatedCount, inputMutationCount, failureCount;
    boolean secondSameReference, transformedDefinitionReturned;
    boolean metadataPreserved, conditionsPreserved, provenancePreserved, originalNodesPreserved;
    boolean portableEvidenceProjected, portableOrderingValidated;
    boolean failureObserved, failureEnvelopeValidated;

    void putJson(Map<String, Object> fields) {
      fields.put("configurationContract", SCHEMA);
      fields.put("configurationHook", HOOK);
      fields.put("configurationClassification", classification);
      fields.put("configurationError", error);
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
      fields.put("configurationTargetSource", targetSource);
      fields.put("configurationTargetLocation", targetLocation);
      fields.put("configurationTargetContentBefore", targetContentBefore);
      fields.put("configurationTargetContentAfter", targetContentAfter);
      fields.put("configurationTargetBodyBefore", targetBodyBefore);
      fields.put("configurationTargetBodyAfter", targetBodyAfter);
      fields.put("configurationOperationCanonicalPass1", operationCanonicalPass1);
      fields.put("configurationOperationCanonicalPass2", operationCanonicalPass2);
      fields.put("configurationResultCanonicalFingerprintPass1", resultCanonicalFingerprintPass1);
      fields.put("configurationResultCanonicalFingerprintPass2", resultCanonicalFingerprintPass2);
      fields.put("configurationCellName", name);
      fields.put("configurationInitializerCanonical", initializerCanonical);
      fields.put("configurationExpectedCloneFingerprint", expectedCloneFingerprint);
      fields.put("configurationInstalledCellFingerprint", installedCellFingerprint);
      fields.put("configurationFailureObserved", failureObserved);
      fields.put("configurationFailureCanonical", failureCanonical);
      fields.put("configurationFailureSchema", failureSchema);
      fields.put("configurationFailureReason", failureReason);
      fields.put("configurationFailureCount", failureCount);
      fields.put("configurationFailureEnvelopeValidated", failureEnvelopeValidated);
      fields.put("configurationValidatedOperationCount", validatedOperationCount);
      fields.put("configurationApplicationCount", applicationCount);
      fields.put("configurationChangedConfigurationCount", changedConfigurationCount);
      fields.put("configurationAlreadyPresentValidatedCount", alreadyPresentValidatedCount);
      fields.put("configurationInputMutationCount", inputMutationCount);
      fields.put("configurationSecondSameReference", secondSameReference);
      fields.put("configurationTransformedDefinitionReturned", transformedDefinitionReturned);
      fields.put("configurationMetadataPreserved", metadataPreserved);
      fields.put("configurationConditionsPreserved", conditionsPreserved);
      fields.put("configurationProvenancePreserved", provenancePreserved);
      fields.put("configurationOriginalNodesPreserved", originalNodesPreserved);
      fields.put("configurationBeforeDefinition", beforeDefinition);
      fields.put("configurationAfterDefinition", afterDefinition);
      fields.put("portableConfigurationEvidenceProjected", portableEvidenceProjected);
      fields.put("portableConfigurationOrderingValidated", portableOrderingValidated);
      fields.put("portableConfigurationBeforeDefinition", portableBeforeDefinition);
      fields.put("portableConfigurationAfterDefinition", portableAfterDefinition);
      fields.put("portableConfigurationRequestFingerprintPass1", portableRequestFingerprintPass1);
      fields.put("portableConfigurationResponseFingerprintPass1", portableResponseFingerprintPass1);
      fields.put("portableConfigurationRequestFingerprintPass2", portableRequestFingerprintPass2);
      fields.put("portableConfigurationResponseFingerprintPass2", portableResponseFingerprintPass2);
      fields.put("portableConfigurationOperationCanonicalPass1", portableOperationCanonicalPass1);
      fields.put("portableConfigurationOperationCanonicalPass2", portableOperationCanonicalPass2);
      fields.put("portableConfigurationTargetLineage", portableTargetLineage);
      fields.put("portableConfigurationTargetSource", portableTargetSource);
      fields.put("portableConfigurationTargetLocation", portableTargetLocation);
      fields.put("portableConfigurationTargetContentBefore", portableTargetContentBefore);
      fields.put("portableConfigurationTargetContentAfter", portableTargetContentAfter);
      fields.put("portableConfigurationTargetBodyBefore", portableTargetBodyBefore);
      fields.put("portableConfigurationTargetBodyAfter", portableTargetBodyAfter);
      fields.put("portableConfigurationInitializerCanonical", portableInitializerCanonical);
      fields.put("portableConfigurationExpectedCloneFingerprint", portableExpectedCloneFingerprint);
      fields.put("portableConfigurationInstalledCellFingerprint", portableInstalledCellFingerprint);
    }
  }

  private static String runK(String program, Path definition, Path recordPath) {
    try {
      Path parent = recordPath.getParent(); Files.createDirectories(parent);
      Path file = Files.createTempFile(parent, "configuration-", ".kink");
      try {
        Files.writeString(file, program, StandardCharsets.UTF_8);
        RunProcess.ProcessOutput output = RunProcess.execute(
            Map.of("LC_ALL", "C", "LANG", "C", "TZ", "UTC"), new ProcessBuilder(),
            "krun", file.toString(), "--definition", definition.toString(), "--output", "pretty");
        String stderr = new String(output.stderr(), StandardCharsets.UTF_8);
        if (output.exitCode() != 0) throw reject("k-selection", "K execution failed: " + stderr.strip());
        return new String(output.stdout(), StandardCharsets.UTF_8);
      } finally {
        Files.deleteIfExists(file);
      }
    } catch (IOException error) {
      throw KEMException.criticalError("cannot invoke configuration augmentation", error);
    }
  }

  private static String replaceSource(String value, String primarySource, String representedSource) {
    if (primarySource.equals(representedSource)) return value;
    require(!representedSource.contains(primarySource), "portable source contains raw source");
    String result = value.replace(primarySource, representedSource);
    require(!result.contains(primarySource), "portable projection retained raw source");
    return result;
  }

  private static ValidationException reject(String classification, String message) {
    return new ValidationException(classification + ": " + message);
  }
  private static void require(boolean condition, String message) {
    if (!condition) throw new ValidationException(message);
  }
  private static String quote(String value) { return StringUtil.enquoteKString(value); }
  private static String sha256(String value) {
    try {
      byte[] digest = MessageDigest.getInstance("SHA-256").digest(value.getBytes(StandardCharsets.UTF_8));
      StringBuilder out = new StringBuilder();
      for (byte item : digest) out.append(String.format(Locale.ROOT, "%02x", item));
      return out.toString();
    } catch (NoSuchAlgorithmException error) {
      throw new AssertionError(error);
    }
  }
  private static final class ValidationException extends RuntimeException {
    ValidationException(String message) { super(message); }
  }
}
