//! Collection without a command: the descriptors a definition's collector reports, and the K,
//! reference source or check verdict of any bundle of them, computed in memory by the stages
//! `emit-k`, `expand` and `check` run.
//!
//! A caller that judges many definitions from one collector run (the class tests, which collect
//! one package of many cases and judge each case from the descriptors of the base and that case)
//! collects once with [`collect_descriptors`] and then lowers each sub-bundle with
//! [`CollectedDefinition::emit_k`], and judges it with [`CollectedDefinition::check`]. Nothing
//! here reads or writes the result cache: every call builds and runs the collector.

use std::path::{Path, PathBuf};

use krs_compiler::{SentenceSource, SentenceSources, SourceMap};
use krs_ir::measure::Measurement;
use krs_ir::{DescriptorBundle, SentenceKind};
use krs_ir_levels::{DefinitionIr, DefinitionSentence};

use super::collector::{build_collector_measured, generate_collector, run_collector};
use super::{
    CommandError, CommandRequest, LoadVisit, PreparedDefinition, check_verdict,
    definition_warnings, emit_definition, expansion, plan_collector, prepare_bundle,
    prepare_bundle_with, validate_request,
};
use crate::metadata::cargo_metadata_in;
use crate::{CollectorPlan, DiagnosticEnvelope, DiagnosticReports, DiagnosticSources};

/// A definition's collected descriptors, the warnings the collector reported for them, and the
/// plan that collected them.
#[derive(Clone, Debug)]
pub struct CollectedDefinition {
    /// The descriptors, as every command decodes them before lowering.
    pub bundle: DescriptorBundle,
    warnings: Vec<DiagnosticEnvelope>,
    plan: CollectorPlan,
    profile: Option<krs_ir::RawKProfile>,
}

/// K emitted in memory, as `krs emit-k` writes it, with the table that names its rules.
#[derive(Clone, Debug)]
pub struct EmittedDefinition {
    /// `definition.k`.
    pub definition: String,
    /// `spec.k`, when the definition has claims.
    pub spec: Option<String>,
    /// The Definition IR the K is emitted from.
    pub ir: DefinitionIr,
    /// The warnings `krs emit-k` reports with it.
    pub warnings: DiagnosticReports,
    /// Every rule, equation, claim and other rule-like sentence of the emitted K, in emitted
    /// module order and, within a module, in Definition IR order ([`EmittedRule`]).
    pub rules: Vec<EmittedRule>,
    /// The source map of the emission, with the generated range of every node in
    /// `definition.k` and `spec.k`, as `krs emit-k` writes it to `sources.json`.
    pub source_map: SourceMap,
}

/// K emitted in memory as `krs emit-k` writes it ([`EmittedDefinition`]), with the lowering it is
/// emitted from kept in process: the baseline a re-derivation of its sentences reads
/// (`krs_compiler::Rederivation`).
#[derive(Debug)]
pub struct RetainedEmission {
    /// The emission.
    pub emitted: EmittedDefinition,
    /// The semantic lowering, with the modules before the derivation passes.
    pub retained: krs_compiler::RetainedLowering,
    /// The Definition IR lowering the K is emitted from.
    pub lowered: krs_compiler::LoweredDefinition,
}

/// One rule-like sentence of the emitted K (a rule, equation, simplification, alias, desugar,
/// context or claim), as every report of the krs front end names it.
///
/// `item` names the KRS item that wrote the sentence as a run's report and a stop name it
/// ([`krs_exec::item_spelling`], the one function that spells it), so a name a krs kink document
/// gives a rule is one `krs run --stop-before` reads as the same item. `source_item`, `package`,
/// `file` and `claim_helper` are those of the `// KRS` line the emission writes above the
/// sentence ([`krs_compiler::SentenceSources`], the one function that computes that line), so a
/// report and the K describe a sentence identically; they are `None` (and `claim_helper` false)
/// for a sentence the emission writes no such line for, which no Rust item names. `line` and
/// `column` position the start of the sentence's first authored range in the package's current
/// source, as `krs run --trace` positions a rule's step.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EmittedRule {
    /// The emitted K module that holds the sentence: its own module, or, for a claim of a
    /// module that is not a spec module, the generated `<MAIN>-SPEC` of `spec.k`.
    pub module: String,
    /// The label the emission writes (`nat--plus_zero`); labels are unique in the emitted K.
    pub label: String,
    /// The sentence's kind.
    pub kind: SentenceKind,
    /// The KRS item that wrote the sentence, spelled as a stop reads it: `crate::` and its Rust
    /// path for an item of the root package (`crate::plus_zero`), the crate name of the package
    /// that declares it and its path otherwise (`lang::step`); `None` where the sentence's origin
    /// names no authored item.
    pub item: Option<String>,
    /// The Rust item as the `// KRS` line spells it after the file: the item's own name, then
    /// `, branch <b>` and `, local function` where the line has them (`plus_zero`,
    /// `InterruptVector, branch 3`).
    pub source_item: Option<String>,
    /// The Cargo package of the authored file.
    pub package: Option<String>,
    /// The authored file, package-relative and slash-separated (`src/lib.rs`).
    pub file: Option<String>,
    /// The 1-based line of the start of the sentence's first authored range, when the
    /// package's source still has the revision the collector read.
    pub line: Option<u32>,
    /// The 1-based scalar column of that start.
    pub column: Option<u32>,
    /// Whether the `// KRS` line marks the sentence a claim helper (an equation of a function
    /// only claims apply).
    pub claim_helper: bool,
}

/// Collect `request`'s definition: Cargo metadata, the collector plan, and the collector's
/// build and run, the stages every command runs before lowering. `request.command`,
/// `request.no_reuse` and `request.message_format` play no part.
///
/// `target_directory` is Cargo's target directory for the package and its collector, in place of
/// the environment's, so that callers collecting several packages at once can give each its own.
///
/// # Errors
///
/// Fails as every command fails at those stages: a rustc error in the package or a collector
/// error is [`CommandError::Diagnostics`] when its range is known.
pub fn collect_descriptors(
    request: &CommandRequest,
    target_directory: Option<&Path>,
) -> Result<CollectedDefinition, CommandError> {
    plan_collection(
        request,
        target_directory,
        &mut Measurement::disabled(),
        &mut DiagnosticSources::default(),
    )?
    .collect(&mut Measurement::disabled())
}

/// A definition's collector, planned but not yet built: the first half of
/// [`collect_descriptors`], which reads Cargo metadata and plans the collector, and builds and
/// runs nothing.
pub(crate) struct PlannedCollection {
    metadata: crate::CargoMetadata,
    plan: CollectorPlan,
    target_directory: Option<PathBuf>,
    profile: Option<krs_ir::RawKProfile>,
}

/// Plan `request`'s collector as [`collect_descriptors`] does, recording the stages' timings in
/// `measurement`, and set `sources` to the selected packages' source roots, so that a failure
/// of the collector's build or run renders its diagnostics against the package's sources.
pub(crate) fn plan_collection(
    request: &CommandRequest,
    target_directory: Option<&Path>,
    measurement: &mut Measurement,
    sources: &mut DiagnosticSources,
) -> Result<PlannedCollection, CommandError> {
    validate_request(request)?;
    let metadata = measurement.timings.try_span("cargo.metadata.input", |_| {
        cargo_metadata_in(&request.manifest_path, target_directory)
    })?;
    let plan = plan_collector(
        request,
        &request.dependencies,
        &metadata,
        &mut measurement.timings,
    )?;
    *sources = DiagnosticSources::from_plan(&plan);
    Ok(PlannedCollection {
        metadata,
        plan,
        target_directory: target_directory.map(Path::to_path_buf),
        profile: request.profile,
    })
}

impl PlannedCollection {
    /// The directory of the selected root package's `Cargo.toml`.
    #[cfg(feature = "kink")]
    pub(crate) fn root_directory(&self) -> Option<PathBuf> {
        root_directory(&self.plan)
    }

    /// Build and run the planned collector and decode its descriptors, recording the stages'
    /// timings and counters in `measurement`.
    pub(crate) fn collect(
        self,
        measurement: &mut Measurement,
    ) -> Result<CollectedDefinition, CommandError> {
        let target_directory = self.target_directory.as_deref();
        let collector_directory = generate_collector(&self.metadata, &self.plan, measurement)?;
        let executable = build_collector_measured(
            &collector_directory,
            &self.plan,
            target_directory,
            measurement,
        )?;
        let collected = run_collector(&collector_directory, &executable, measurement)?;
        let bundle = measurement.timings.try_span("protocol.decode", |_| {
            DescriptorBundle::from_collector_protocol(&collected.stdout)
                .map_err(CommandError::DescriptorProtocol)
        })?;
        Ok(CollectedDefinition {
            bundle,
            warnings: collected.warnings,
            plan: self.plan,
            profile: self.profile,
        })
    }
}

/// The directory of `plan`'s root package's `Cargo.toml`.
fn root_directory(plan: &CollectorPlan) -> Option<PathBuf> {
    plan.facets()
        .iter()
        .find(|facet| facet.is_root)
        .and_then(|facet| facet.manifest_path.parent())
        .map(Path::to_path_buf)
}

impl CollectedDefinition {
    /// The directory of the selected root package's `Cargo.toml`.
    #[must_use]
    pub fn root_directory(&self) -> Option<PathBuf> {
        root_directory(&self.plan)
    }

    /// The collector's warnings about the sentences of `bundle`, this definition's or a subset of
    /// it: those located inside an authored node of a descriptor of `bundle` (a `cells!` entry
    /// lies inside its sentence's payload), or at a construct holding one (a readable entry's
    /// group record holds the nodes of its path, and none of its own), or naming one, and those
    /// about no sentence. A sentence's construct holds no other sentence's node, so a warning
    /// is kept with the sentence it was raised at, whatever subset `bundle` is.
    fn warnings_of(&self, bundle: &DescriptorBundle) -> Vec<DiagnosticEnvelope> {
        let ranges = bundle
            .descriptors()
            .iter()
            .flat_map(|descriptor| descriptor.provenance().origins())
            .filter_map(|node| node.origin.exact_authored_range())
            .collect::<Vec<_>>();
        self.warnings
            .iter()
            .filter(|warning| match (&warning.authored_range, &warning.item) {
                (Some(range), _) => ranges.iter().any(|node| {
                    let (node_bytes, warned) = (
                        node.start_byte..node.end_byte,
                        range.start_byte..range.end_byte,
                    );
                    let holds = |outer: &std::ops::Range<_>, inner: &std::ops::Range<_>| {
                        outer.start <= inner.start && inner.end <= outer.end
                    };
                    node.file == range.file
                        && (holds(&node_bytes, &warned) || holds(&warned, &node_bytes))
                }),
                (None, Some(item)) => bundle
                    .descriptors()
                    .iter()
                    .any(|descriptor| descriptor.id().to_string() == *item),
                (None, None) => true,
            })
            .cloned()
            .collect()
    }

    /// Lower `bundle` as every command does, after the collector's warnings about its sentences.
    fn prepare(
        &self,
        bundle: DescriptorBundle,
        measurement: &mut Measurement,
    ) -> Result<super::PreparedDefinition, CommandError> {
        let warnings = self.warnings_of(&bundle);
        let root = self.plan.root_package();
        prepare_bundle(bundle, warnings, root.as_ref(), self.profile, measurement)
    }

    /// Lower `bundle` and emit its K, as `krs emit-k` does without rendering or writing the
    /// artifacts. `bundle` is this definition's, or a subset of it.
    ///
    /// # Errors
    ///
    /// Fails as `krs emit-k` fails after collection, with the warnings of the stages that
    /// completed.
    pub fn emit_k(&self, bundle: DescriptorBundle) -> Result<EmittedDefinition, CommandError> {
        self.emit_k_measured(bundle, &mut Measurement::disabled())
    }

    /// [`Self::emit_k`] that records the stages' timings and counters in `measurement`.
    ///
    /// # Errors
    ///
    /// Fails as [`Self::emit_k`] fails.
    pub fn emit_k_measured(
        &self,
        bundle: DescriptorBundle,
        measurement: &mut Measurement,
    ) -> Result<EmittedDefinition, CommandError> {
        let prepared = self.prepare(bundle, measurement)?;
        self.emitted(&prepared, measurement)
    }

    /// [`Self::emit_k`], keeping the lowering the K is emitted from ([`RetainedEmission`]): the
    /// same stages, so the K is the K `krs emit-k` writes for `bundle`.
    ///
    /// # Errors
    ///
    /// Fails as [`Self::emit_k`] fails.
    pub fn emit_k_retained(
        &self,
        bundle: DescriptorBundle,
    ) -> Result<RetainedEmission, CommandError> {
        self.emit_k_retained_measured(bundle, &mut Measurement::disabled())
    }

    /// [`Self::emit_k_retained`] that records the stages' timings and counters in
    /// `measurement`.
    ///
    /// # Errors
    ///
    /// Fails as [`Self::emit_k`] fails.
    pub fn emit_k_retained_measured(
        &self,
        bundle: DescriptorBundle,
        measurement: &mut Measurement,
    ) -> Result<RetainedEmission, CommandError> {
        let warnings = self.warnings_of(&bundle);
        let root = self.plan.root_package();
        let (prepared, retained) =
            prepare_bundle_with(bundle, warnings, self.profile, measurement, |bundle| {
                krs_compiler::lower_descriptor_bundle_retained(bundle, root.as_ref())
                    .map(|retained| (retained.theory().clone(), retained))
                    .map_err(CommandError::DescriptorLowering)
            })?;
        let emitted = self.emitted(&prepared, measurement)?;
        Ok(RetainedEmission {
            emitted,
            retained,
            lowered: prepared.lowered,
        })
    }

    /// The emission of `prepared`, as `krs emit-k` emits it.
    fn emitted(
        &self,
        prepared: &PreparedDefinition,
        measurement: &mut Measurement,
    ) -> Result<EmittedDefinition, CommandError> {
        let warnings = definition_warnings(prepared);
        let emitted = emit_definition(prepared, measurement)
            .map_err(|error| error.warned(warnings.clone()))?;
        let ir = prepared.lowered.definition();
        let rules = measurement.timings.span("emit_k.rules", |_| {
            emitted_rules(
                ir,
                emitted.spec().and_then(|spec| spec.generated_module()),
                &DiagnosticSources::from_plan(&self.plan),
            )
        });
        Ok(EmittedDefinition {
            definition: emitted.source().to_owned(),
            spec: emitted.spec().map(|spec| spec.source().to_owned()),
            ir: ir.clone(),
            warnings,
            rules,
            source_map: emitted.source_map().clone(),
        })
    }

    /// Lower `bundle` and judge it as `krs check` without `--backend` does: `emit-k`'s emission,
    /// every native route's capability table and native compile, and on the `native-rust` route
    /// the definition load of the run commands. `bundle` is this definition's, or a subset of it.
    ///
    /// # Errors
    ///
    /// Fails exactly when `krs check` refuses the definition, with its refusal: the note naming
    /// the route or the command that refuses it, and the warnings of the stages that completed.
    pub fn check(&self, bundle: DescriptorBundle) -> Result<DiagnosticReports, CommandError> {
        self.check_visiting(bundle, None)
    }

    /// [`Self::check`], and where the check loads the definition the run commands load (on the
    /// `native-rust` route), `visit` made on it once loaded, on the check's worker: a program
    /// configured and run there runs as `krs run` runs it, on the compile the check judged.
    /// `visit` is made before the verdict is known; a caller reads what it saw only when the
    /// check passes.
    ///
    /// # Errors
    ///
    /// Fails as [`Self::check`] fails.
    pub fn check_visiting(
        &self,
        bundle: DescriptorBundle,
        visit: Option<LoadVisit<'_>>,
    ) -> Result<DiagnosticReports, CommandError> {
        let mut measurement = Measurement::disabled();
        let prepared = self.prepare(bundle, &mut measurement)?;
        check_verdict(&prepared, None, visit, &mut measurement)
            .map_err(|error| error.warned(definition_warnings(&prepared)))
    }

    /// The crate root `krs expand` prints for `bundle`, this definition's or a subset of it.
    ///
    /// # Errors
    ///
    /// Fails as `krs expand` fails after collection, and where the expansion changes a module
    /// file other than the crate root, which the crate root alone does not print.
    pub fn expand(&self, bundle: DescriptorBundle) -> Result<String, CommandError> {
        let mut measurement = Measurement::disabled();
        let prepared = self.prepare(bundle, &mut measurement)?;
        let warnings = definition_warnings(&prepared);
        let expanded = expansion(&prepared, &self.plan).map_err(|error| error.warned(warnings))?;
        match expanded.changed.as_slice() {
            [] => Ok(expanded.root.text),
            [file] if file.path == expanded.root.path => Ok(file.text.clone()),
            files => Err(CommandError::Usage(format!(
                "krs expand changes module files other than the crate root {} ({}), which its printed crate root does not hold",
                expanded.root.path,
                files
                    .iter()
                    .map(|file| file.path.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            ))),
        }
    }
}

/// The rule table of `definition`'s emission ([`EmittedRule`]): every rule-like sentence of
/// every module, a claim of a module that is not a spec module under `generated_spec` (the
/// generated `<MAIN>-SPEC` the emission moves it to), positioned in the source `sources`
/// reads by [`krs_exec::Origins`], as `krs run --trace` positions a step's rule, and its item
/// spelled by [`krs_exec::item_spelling`] with the crate names the definition records, as a
/// run's report spells it.
fn emitted_rules(
    definition: &DefinitionIr,
    generated_spec: Option<&str>,
    sources: &DiagnosticSources,
) -> Vec<EmittedRule> {
    let named = SentenceSources::new(definition);
    let text = sources.clone();
    let mut origins = krs_exec::Origins::new(Some(Box::new(move |file| text.source_text(file))));
    let mut rules = Vec::new();
    for module in definition.modules() {
        for sentence in module.sentences() {
            let DefinitionSentence::Rule(rule) = sentence else {
                continue;
            };
            let module_name = match generated_spec {
                Some(generated) if rule.kind() == SentenceKind::Claim && !module.is_spec() => {
                    generated.to_owned()
                }
                _ => module.id().as_str().to_owned(),
            };
            let source = named.source(sentence);
            let span = origins.span(sentence.origin());
            rules.push(EmittedRule {
                module: module_name,
                label: rule.label().emitted_name().to_owned(),
                kind: rule.kind(),
                item: krs_exec::item_spelling(definition, sentence.origin()),
                source_item: source.as_ref().map(SentenceSource::item_spelling),
                package: source.as_ref().map(|source| source.package().to_owned()),
                file: source.as_ref().map(|source| source.file().to_owned()),
                line: span.as_ref().and_then(|span| span.line),
                column: span.as_ref().and_then(|span| span.column),
                claim_helper: source.as_ref().is_some_and(SentenceSource::is_claim_helper),
            });
        }
    }
    rules
}
