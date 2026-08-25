//! Executable vertical preflight for the M3D static-alias slice.

use std::path::PathBuf;

use k::Term;
use k::builtin::Int;
use krs_compiler::{
    PackageContext, collect_host_descriptors_with_builtins, emit_k, lower_descriptor_bundle,
    lower_semantic_theory,
};
use krs_ir::{DefinitionSentence, ProductionAttribute, SentenceKind};
use krs_k_rust::adapt_definition;

#[k::sort]
pub trait Expr {}

#[k::subsort]
impl Expr for Int {}

#[k::configuration]
pub struct Machine {
    pub k: k::configuration::KCell<k::builtin::KSequence>,
}

#[allow(clippy::must_use_candidate, clippy::needless_pass_by_value)]
impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] program: Term<dyn Expr>) -> Self {
        Self {
            k: k::configuration::KCell::new(k::k![program]),
        }
    }
}

#[k::constructor(sort = Expr, syntax = "m3dZero")]
#[k::alias]
pub struct M3dZero;

#[k::alias]
fn m3d_zero_alias(k::term![M3dZero]: Term<dyn Expr>) -> Term<dyn Expr> {
    0
}

fn main() {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
    let context = PackageContext::new(
        "KRS-M3D-ALIAS-SLICE",
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
    .expect("alias production and clause descriptors collect");
    descriptors.reverse();
    let reordered = collect_host_descriptors_with_builtins(
        [context],
        descriptors,
        &k::builtin_registry(),
    )
    .expect("reordered alias descriptors collect");
    assert_eq!(
        first.to_canonical_json().unwrap(),
        reordered.to_canonical_json().unwrap(),
        "descriptor JSON must not depend on registration order"
    );

    let semantic = lower_descriptor_bundle(&first).expect("aliases lower to semantic IR");
    let lowered = lower_semantic_theory(&semantic).expect("aliases lower to Definition IR");
    let reordered_semantic =
        lower_descriptor_bundle(&reordered).expect("reordered aliases lower to semantic IR");
    let reordered_lowered = lower_semantic_theory(&reordered_semantic)
        .expect("reordered aliases lower to Definition IR");
    let alias_productions = lowered
        .definition()
        .modules()
        .iter()
        .flat_map(|module| module.sentences())
        .filter_map(|sentence| match sentence {
            DefinitionSentence::Production(production)
                if production
                    .attributes()
                    .iter()
                    .any(|attribute| matches!(attribute, ProductionAttribute::Alias { .. })) =>
            {
                Some(production)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(alias_productions.len(), 1);
    let alias_rules = lowered
        .definition()
        .modules()
        .iter()
        .flat_map(|module| module.sentences())
        .filter(|sentence| {
            matches!(sentence, DefinitionSentence::Rule(rule) if rule.kind() == SentenceKind::Alias)
        })
        .count();
    assert_eq!(alias_rules, 1);

    let emitted = emit_k(&lowered).expect("aliases emit deterministic K source");
    let reordered_emitted =
        emit_k(&reordered_lowered).expect("reordered aliases emit deterministic K source");
    assert_eq!(emitted, reordered_emitted);
    assert!(
        emitted.source().contains("m3dZero\" [symbol("),
        "{}",
        emitted.source()
    );
    assert!(emitted.source().contains(", alias]"));
    assert!(emitted.source().contains("rule m3dZero => 0"));
    assert!(!emitted.source().contains("rule m3dZero => 0 [alias"));
    let source_map = emitted.source_map().to_canonical_json().unwrap();
    assert!(source_map.contains("alias_production"));
    assert!(source_map.contains("alias_clause"));
    assert!(
        emitted
            .symbol_map()
            .to_canonical_json()
            .unwrap()
            .contains(alias_productions[0].symbol().emitted_name())
    );
    adapt_definition(lowered.definition()).expect("native k-rust accepts the alias slice");
}
