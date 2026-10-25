//! Collection without a command: the descriptors a definition's collector reports, and the K or
//! reference source of any bundle of them, computed in memory by the stages `emit-k` and `expand`
//! run.
//!
//! A caller that judges many definitions from one collector run (the class tests, which collect
//! one package of many cases and judge each case from the descriptors of the base and that case)
//! collects once with [`collect_descriptors`] and then lowers each sub-bundle with
//! [`CollectedDefinition::emit_k`]. Nothing here reads or writes the result cache: every call
//! builds and runs the collector.

use std::path::Path;

use krs_compiler::{DEFINITION_ARTIFACT, SPEC_ARTIFACT};
use krs_ir::DescriptorBundle;
use krs_ir::measure::Measurement;
use krs_ir_levels::DefinitionIr;

use super::collector::{build_collector_measured, generate_collector, run_collector};
use super::{
    CommandError, CommandRequest, definition_warnings, expand, plan_collector, prepare_bundle,
    render_emitted, validate_request,
};
use crate::metadata::cargo_metadata_in;
use crate::{CollectorPlan, DiagnosticReports};

/// A definition's collected descriptors, and the plan that collected them.
#[derive(Clone, Debug)]
pub struct CollectedDefinition {
    /// The descriptors, as every command decodes them before lowering.
    pub bundle: DescriptorBundle,
    plan: CollectorPlan,
    profile: Option<krs_ir::RawKProfile>,
}

/// K emitted in memory, as `krs emit-k` writes it.
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
    validate_request(request)?;
    let mut measurement = Measurement::disabled();
    let metadata = cargo_metadata_in(&request.manifest_path, target_directory)?;
    let plan = plan_collector(request, &metadata, &mut measurement.timings)?;
    let collector_directory = generate_collector(&metadata, &plan, &mut measurement)?;
    let executable = build_collector_measured(
        &collector_directory,
        &plan,
        target_directory,
        &mut measurement,
    )?;
    let (stdout, _) = run_collector(&collector_directory, &executable, &mut measurement)?;
    let bundle = DescriptorBundle::from_collector_protocol(&stdout)
        .map_err(CommandError::DescriptorProtocol)?;
    Ok(CollectedDefinition {
        bundle,
        plan,
        profile: request.profile,
    })
}

impl CollectedDefinition {
    /// Lower `bundle` and emit its K, as `krs emit-k` does without writing the artifacts.
    /// `bundle` is this definition's, or a subset of it.
    ///
    /// # Errors
    ///
    /// Fails as `krs emit-k` fails after collection, with the warnings of the stages that
    /// completed.
    pub fn emit_k(&self, bundle: DescriptorBundle) -> Result<EmittedDefinition, CommandError> {
        let mut measurement = Measurement::disabled();
        let prepared = prepare_bundle(bundle, self.profile, &mut measurement)?;
        let warnings = definition_warnings(&prepared);
        let artifacts = render_emitted(&prepared, &mut measurement)
            .map_err(|error| error.warned(warnings.clone()))?;
        let text = |name: &str| {
            artifacts
                .iter()
                .find(|(artifact, _)| *artifact == name)
                .map(|(_, bytes)| String::from_utf8_lossy(bytes).into_owned())
        };
        Ok(EmittedDefinition {
            definition: text(DEFINITION_ARTIFACT).unwrap_or_default(),
            spec: text(SPEC_ARTIFACT),
            ir: prepared.lowered.definition().clone(),
            warnings,
        })
    }

    /// The reference source `krs expand` prints for `bundle`, this definition's or a subset of it.
    ///
    /// # Errors
    ///
    /// Fails as `krs expand` fails after collection.
    pub fn expand(&self, bundle: DescriptorBundle) -> Result<String, CommandError> {
        let mut measurement = Measurement::disabled();
        let prepared = prepare_bundle(bundle, self.profile, &mut measurement)?;
        let warnings = definition_warnings(&prepared);
        let outcome = expand(&prepared, &self.plan).map_err(|error| error.warned(warnings))?;
        Ok(String::from_utf8_lossy(outcome.stdout()).into_owned())
    }
}
