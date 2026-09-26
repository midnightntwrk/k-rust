//! Executable vertical preflight for the IMP static semantics simplification slice.

use std::path::PathBuf;

use k::Term;
use k::builtin::{Bool, bool, int};
use k_rust::definition::Sentence;
use krs_compiler::{
    PackageContext, SourceMapNodeKind, collect_host_descriptors_with_builtins, emit_k,
    lower_descriptor_bundle, lower_semantic_theory,
};
use krs_ir::{DefinitionSentence, ItemKind, SentenceKind};
use krs_k_rust::{CompileOptions, NativeNodeRole, adapt_definition, compile_definition};

#[k::sort]
pub trait KItem {}

impl KItem for Bool {}

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

#[k::simplification]
fn normalize_gt(k::term![int::gt(lhs, rhs)]: Term<Bool>) -> Term<Bool> {
    int::lt(rhs, lhs)
}

#[k::simplification]
fn normalize_ge(k::term![int::ge(lhs, rhs)]: Term<Bool>) -> Term<Bool> {
    int::le(rhs, lhs)
}

#[k::simplification]
fn normalize_not_lt(k::term![bool::not(int::lt(lhs, rhs))]: Term<Bool>) -> Term<Bool> {
    int::le(rhs, lhs)
}

#[k::simplification]
fn normalize_not_le(k::term![bool::not(int::le(lhs, rhs))]: Term<Bool>) -> Term<Bool> {
    int::lt(rhs, lhs)
}

fn main() {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
    let context = PackageContext::new(
        "KRS-IMP-STATIC-SIMPLIFICATION-SLICE",
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
    .expect("simplification descriptors collect");
    descriptors.reverse();
    let reordered =
        collect_host_descriptors_with_builtins([context], descriptors, &k::builtin_registry())
            .expect("reordered simplification descriptors collect");
    assert_eq!(first.to_canonical_json().unwrap(), reordered.to_canonical_json().unwrap());
    assert_eq!(
        first
            .descriptors
            .iter()
            .filter(|descriptor| descriptor.id.item_kind() == ItemKind::Simplification)
            .count(),
        4
    );

    let semantic = lower_descriptor_bundle(&first).expect("simplifications lower to semantic IR");
    let reordered_semantic =
        lower_descriptor_bundle(&reordered).expect("reordered simplifications lower");
    assert_eq!(semantic.to_canonical_json().unwrap(), reordered_semantic.to_canonical_json().unwrap());
    let lowered = lower_semantic_theory(&semantic).expect("simplifications lower to Definition IR");
    let reordered_lowered = lower_semantic_theory(&reordered_semantic).expect("reordered Definition lowering succeeds");
    assert_eq!(
        lowered.definition().to_canonical_json().unwrap(),
        reordered_lowered.definition().to_canonical_json().unwrap()
    );
    let rules = lowered
        .definition()
        .modules()
        .iter()
        .flat_map(|module| module.sentences())
        .filter_map(|sentence| match sentence {
            DefinitionSentence::Rule(rule) if rule.kind() == SentenceKind::Simplification => Some(rule),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(rules.len(), 4);
    assert!(rules.iter().all(|rule| rule.simplification().is_some()));
    assert!(rules.iter().all(|rule| rule.simplification().unwrap().priority().is_none()));

    let emitted = emit_k(&lowered).expect("simplifications emit deterministic K source");
    let reordered_emitted = emit_k(&reordered_lowered).expect("reordered simplifications emit");
    assert_eq!(emitted, reordered_emitted);
    assert_eq!(emitted.source().matches("simplification, label(").count(), 4);
    assert!(!emitted.source().contains("priority("));
    let source_nodes = lowered.source_map().entries();
    assert_eq!(source_nodes.iter().filter(|node| node.node_kind() == SourceMapNodeKind::Simplification).count(), 4);
    assert_eq!(source_nodes.iter().filter(|node| node.node_kind() == SourceMapNodeKind::SimplificationPriority).count(), 0);
    let source_json = emitted.source_map().to_canonical_json().unwrap();
    assert!(source_json.contains("simplification_marker"));

    let adapted = adapt_definition(lowered.definition()).expect("native adapter accepts simplifications");
    let main = adapted.definition().main_module().expect("native main module exists");
    let native_rules = main
        .local_sentences
        .iter()
        .filter(|sentence| matches!(sentence, Sentence::Rule { attributes, .. }
            if attributes.get("simplification").is_some()
                && attributes.get("priority").is_none()))
        .count();
    assert_eq!(native_rules, 4);
    assert_eq!(adapted.origins().iter().filter(|mapping| mapping.role == NativeNodeRole::Simplification).count(), 4);
    assert_eq!(adapted.origins().iter().filter(|mapping| mapping.role == NativeNodeRole::SimplificationPriority).count(), 0);

    let artifacts = compile_definition(lowered.definition(), CompileOptions::default())
        .expect("public native pipeline compiles the simplification slice");
    assert!(!artifacts.definition_kore.is_empty());
    for label in rules.iter().map(|rule| rule.label().emitted_name()) {
        let offset = artifacts
            .definition_kore
            .find(label)
            .unwrap_or_else(|| panic!("missing KRS-owned KORE sentence for {label}"));
        let start = artifacts.definition_kore[..offset]
            .rfind("axiom{")
            .expect("KRS label belongs to an axiom");
        let end = artifacts.definition_kore[offset..]
            .find("\n    ]")
            .map_or(artifacts.definition_kore.len(), |relative| offset + relative);
        let owned = &artifacts.definition_kore[start..end];
        assert!(owned.contains("simplification"), "{owned}");
    }
}
