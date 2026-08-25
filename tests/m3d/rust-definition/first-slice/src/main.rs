//! Executable vertical preflight for the first M3D function/equation slice.

use std::path::PathBuf;

use k::Term;
use k::builtin::{Int, int};
use krs_compiler::{
    PackageContext, collect_host_descriptors_with_builtins, emit_k, lower_descriptor_bundle,
    lower_semantic_theory,
};
use krs_ir::{DefinitionSentence, ProductionAttribute, SentenceKind};
use krs_k_rust::adapt_definition;

#[k::sort]
pub trait KItem {}

impl KItem for Int {}

#[k::configuration]
pub struct Machine {
    pub k: k::configuration::KCell<k::builtin::KSequence>,
}

#[allow(clippy::must_use_candidate, clippy::needless_pass_by_value)]
impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] program: Term<dyn KItem>) -> Self {
        Self {
            k: k::configuration::KCell::new(k::k![program]),
        }
    }
}

#[k::function(total, sort = Int, syntax = "#m3dSliceTotal({value})")]
pub struct M3dSliceTotal {
    pub value: Term<Int>,
}

#[k::function(partial, sort = Int, syntax = "#m3dSlicePositive({value})")]
pub struct M3dSlicePositive {
    pub value: Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#m3dSlicePriority({value})")]
pub struct M3dSlicePriority {
    pub value: Term<Int>,
}

#[k::equation]
fn m3d_slice_total(k::term![M3dSliceTotal(value)]: Term<Int>) -> Term<Int> {
    int::add(value, 1)
}

#[k::requires(int::le(0, value))]
#[k::equation]
fn m3d_slice_positive(k::term![M3dSlicePositive(value)]: Term<Int>) -> Term<Int> {
    value
}

#[k::priority(40)]
#[k::equation]
fn m3d_slice_priority_zero(k::term![M3dSlicePriority(0)]: Term<Int>) -> Term<Int> {
    111
}

#[k::priority(80)]
#[k::equation]
fn m3d_slice_priority_fallback(k::term![M3dSlicePriority(_)]: Term<Int>) -> Term<Int> {
    222
}

fn main() {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
    let context = PackageContext::new(
        "KRS-M3D-FIRST-SLICE",
        env!("CARGO_PKG_NAME"),
        env!("CARGO_PKG_VERSION"),
        "workspace",
        module_path!(),
        manifest,
    )
    .expect("fixture package context is valid");
    let mut descriptors = k::host_descriptors().collect::<Vec<_>>();
    let first = collect_host_descriptors_with_builtins(
        [context.clone()],
        descriptors.clone(),
        &k::builtin_registry(),
    )
    .expect("function and equation descriptors collect");
    descriptors.reverse();
    let reordered = collect_host_descriptors_with_builtins(
        [context],
        descriptors,
        &k::builtin_registry(),
    )
    .expect("reordered descriptors collect");
    assert_eq!(
        first.to_canonical_json().unwrap(),
        reordered.to_canonical_json().unwrap(),
        "descriptor JSON must not depend on registration order"
    );

    let semantic = lower_descriptor_bundle(&first).expect("descriptors lower to semantic IR");
    let lowered = lower_semantic_theory(&semantic).expect("semantic IR lowers to Definition IR");
    let functional_productions = lowered
        .definition()
        .modules()
        .iter()
        .flat_map(|module| module.sentences())
        .filter_map(|sentence| match sentence {
            DefinitionSentence::Production(production)
                if production.attributes().iter().any(
                    |attribute| matches!(attribute, ProductionAttribute::Function { .. }),
                ) => Some(production),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(functional_productions.len(), 3);
    let partial_productions = functional_productions
        .iter()
        .filter(|production| {
            !production
                .attributes()
                .iter()
                .any(|attribute| matches!(attribute, ProductionAttribute::Total { .. }))
        })
        .collect::<Vec<_>>();
    assert_eq!(partial_productions.len(), 1);
    assert!(lowered
        .definition()
        .modules()
        .iter()
        .flat_map(|module| module.sentences())
        .any(|sentence| matches!(sentence, DefinitionSentence::Rule(rule) if rule.kind() == SentenceKind::Equation)));
    let mut priorities = lowered
        .definition()
        .modules()
        .iter()
        .flat_map(|module| module.sentences())
        .filter_map(|sentence| match sentence {
            DefinitionSentence::Rule(rule) => rule.priority().map(|priority| priority.value()),
            _ => None,
        })
        .collect::<Vec<_>>();
    priorities.sort_unstable();
    assert_eq!(priorities, [40, 80]);

    let emitted = emit_k(&lowered).expect("Definition IR emits deterministic K source");
    assert!(emitted.source().contains("function, total"));
    assert!(emitted.source().contains("rule "));
    assert!(emitted.source().contains("priority(40)"));
    assert!(emitted.source().contains("priority(80)"));
    assert!(emitted.source().contains("requires "));
    let source_map = lowered.source_map().to_canonical_json().unwrap();
    assert!(source_map.contains("function_total"));
    assert!(source_map.contains("function_partial"));
    assert!(source_map.contains("rule_requires"));
    assert!(
        source_map.contains("equation_priority"),
        "priority provenance missing from source map: {source_map}"
    );
    assert!(
        lowered
            .symbol_map()
            .to_canonical_json()
            .unwrap()
            .contains(partial_productions[0].symbol().emitted_name())
    );
    adapt_definition(lowered.definition()).expect("native k-rust accepts the equation slice");
}
