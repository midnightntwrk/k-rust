//! The raw K policy: the A4 amendment for quoted hooks and `raw_k!` (R9).
//!
//! A quoted hook (`hook = "NAMESPACE.name"`) and a `k::raw_k!` sentence are
//! unchecked K text, so a package admits them only with `allow-raw-k = true`
//! in `[package.metadata.krs]`. With the opt-in each use warns, and the strict
//! profile (`profile = "strict"` or `krs --profile strict`) turns the warnings
//! back into errors. Expansion has already checked each quoted hook against the
//! pinned hook registry; this pass runs after collection because only here are
//! the package metadata and the command line known.

use krs_diagnostic::{Diagnostic, Location, Severity, codes};
use krs_ir::{
    Descriptor, DescriptorBundle, DescriptorPayload, DescriptorProductionAttribute,
    GrammarDescriptor, ProvenanceKey, RawKProfile,
};

use super::error::DescriptorLoweringError;
use super::origin::semantic_origin;

/// The raw K findings of one bundle, in descriptor order.
#[derive(Clone, Debug, Default)]
pub struct RawKPolicy {
    /// Uses the package does not allow: no `allow-raw-k`, or the strict profile.
    pub errors: Vec<Diagnostic>,
    /// Allowed uses; each one is reported on every build.
    pub warnings: Vec<Diagnostic>,
}

/// Checks every quoted hook and `raw_k!` sentence of `bundle` against its
/// package's `allow-raw-k` and `profile` metadata. `profile` overrides every
/// package's profile (`krs --profile`).
///
/// # Errors
///
/// Returns a lowering error only when a descriptor lacks the parser origin of
/// its own provenance key.
pub fn raw_k_policy(
    bundle: &DescriptorBundle,
    profile: Option<RawKProfile>,
) -> Result<RawKPolicy, DescriptorLoweringError> {
    let mut policy = RawKPolicy::default();
    for descriptor in bundle.descriptors() {
        let DescriptorPayload::Grammar(grammar) = descriptor.payload() else {
            continue;
        };
        let uses = match grammar.as_ref() {
            GrammarDescriptor::RawSentence { key, kind, .. } => vec![RawUse {
                key,
                what: format!("`raw_k!` {}", kind.keyword()),
                allowed_code: codes::analysis::RAW_K,
                allowed: "unchecked K text, opaque to KRS; K parses it with this package's grammar"
                    .to_owned(),
            }],
            GrammarDescriptor::Production(production) => raw_hook_uses(&production.attributes),
            GrammarDescriptor::Tokens { productions } => productions
                .iter()
                .flat_map(|production| raw_hook_uses(&production.attributes))
                .collect(),
            GrammarDescriptor::Subsort { .. }
            | GrammarDescriptor::Precedence { .. }
            | GrammarDescriptor::Associativity { .. }
            | GrammarDescriptor::Lexical { .. }
            | GrammarDescriptor::Layout { .. } => Vec::new(),
        };
        if uses.is_empty() {
            continue;
        }
        let (allow_raw_k, package_profile) = bundle.raw_k(descriptor.id().package());
        let profile = profile.unwrap_or(package_profile);
        for raw in uses {
            let location = location(descriptor, raw.key)?;
            if !allow_raw_k {
                policy.errors.push(Diagnostic::error(
                    codes::policy::RAW_K_NOT_ALLOWED,
                    format!(
                        "{}: raw K is an escape from A4; add `allow-raw-k = true` to [package.metadata.krs] to allow it in this package",
                        raw.what
                    ),
                    location,
                ));
            } else if profile == RawKProfile::Strict {
                policy.errors.push(Diagnostic::error(
                    raw.allowed_code,
                    format!(
                        "{}: raw K is an error under the strict profile ({})",
                        raw.what, raw.allowed
                    ),
                    location,
                ));
            } else {
                let mut warning = Diagnostic::error(
                    raw.allowed_code,
                    format!("{}: {}", raw.what, raw.allowed),
                    location,
                );
                warning.severity = Severity::Warning;
                policy.warnings.push(warning);
            }
        }
    }
    Ok(policy)
}

struct RawUse<'a> {
    key: &'a ProvenanceKey,
    what: String,
    allowed_code: krs_diagnostic::Code,
    allowed: String,
}

fn location(
    descriptor: &Descriptor,
    key: &ProvenanceKey,
) -> Result<Location, DescriptorLoweringError> {
    Ok(semantic_origin(descriptor, key.clone(), "raw-k")?
        .origin()
        .exact_authored_range()
        .map_or(Location::None, Location::Source))
}

/// The quoted hooks among one production's attributes.
fn raw_hook_uses(attributes: &[DescriptorProductionAttribute]) -> Vec<RawUse<'_>> {
    attributes
        .iter()
        .filter_map(|attribute| match attribute {
            DescriptorProductionAttribute::RawHook {
                key,
                namespace,
                name,
            } => {
                let hook = format!("{namespace}.{name}");
                let capability = krs_ir::hook_registry::registered_hook(&hook)
                    .map_or("unknown", |registered| registered.capability.as_str());
                Some(RawUse {
                    key,
                    what: format!("quoted hook `{hook}`"),
                    allowed_code: codes::expand::RAW_HOOK,
                    allowed: format!("signature unchecked; native capability: {capability}"),
                })
            }
            _ => None,
        })
        .collect()
}
