//! Executable vertical fixture for the three pinned IMP reachability claims.

use std::path::PathBuf;

#[allow(unused_imports)]
use k::{Term, map};
use k::builtin::{Bool, Int, int};
use k_rust::definition::Sentence as NativeSentence;
use k_rust::kast::{Sort as NativeSort, Term as NativeTerm};
use krs_compiler::{
    PackageContext, collect_host_descriptors_with_builtins, emit_k, lower_descriptor_bundle,
    lower_semantic_theory,
};
use krs_ir::{ClaimModality, DefinitionSentence, DescriptorPayload, ItemKind, SentenceKind};
use krs_k_rust::{
    Backend, CompileOptions, NativeNodeRole, adapt_definition, compile_definition,
};

#[path = "imp_control_flow.rs"]
mod inherited;

pub use inherited::*;

#[k::claim(all_paths, label = "branching")]
#[k::exists(n: Int)]
#[k::ensures(k::or_bool![int::eq(n, 5), int::eq(n, 6)])]
fn branching(
    k::cells! {
        k: k::configuration::KCell(
            Sequence(
                Assign(k::id!("$n"), 7),
                IfThenElse(
                    k::anonymous!(Bool, "_B"),
                    Block(Assign(k::id!("$n"), 6)),
                    Block(Assign(k::id!("$n"), 5)),
                ),
            ),
            tail @ ..
        ),
        env: k::configuration::Cell(map![k::id!("$n") -> 0]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![k::id!("$n") -> n]),
        ..state
    }
}

#[k::claim(all_paths, label = "sum-loop")]
#[k::requires(int::le(0, n))]
fn sum_loop(
    s: Term<Int>,
    n: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(
            While(
                Lt(0, k::id!("$n")),
                Block(Sequence(
                    Assign(k::id!("$s"), Add(k::id!("$s"), k::id!("$n"))),
                    Assign(k::id!("$n"), Sub(k::id!("$n"), 1)),
                )),
            ),
            tail @ ..
        ),
        env: k::configuration::Cell(map![
            k::id!("$s") -> s,
            k::id!("$n") -> n,
        ]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![
            k::id!("$s") -> int::add(
                s,
                int::div(int::mul(n, int::add(n, 1)), 2),
            ),
            k::id!("$n") -> 0,
        ]),
        ..state
    }
}

#[k::claim(all_paths, label = "sum-spec", circularity)]
#[k::requires(int::ge(n, 0))]
fn sum_spec(
    n: Term<Int>,
    s: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(
            While(
                Not(Le(k::id!("$n"), 0)),
                Block(Sequence(
                    Assign(k::id!("$s"), Add(k::id!("$s"), k::id!("$n"))),
                    Assign(k::id!("$n"), Add(k::id!("$n"), int::sub(0, 1))),
                )),
            ),
            tail @ ..
        ),
        env: k::configuration::Cell(map![
            k::id!("$n") -> n,
            k::id!("$s") -> s,
        ]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![
            k::id!("$n") -> 0,
            k::id!("$s") -> int::add(
                s,
                int::div(int::mul(int::add(n, 1), n), 2),
            ),
        ]),
        ..state
    }
}

#[allow(clippy::too_many_lines)]
fn main() {
    let context = PackageContext::new(
        "KRS-IMP-STATIC-CLAIM-SLICE",
        env!("CARGO_PKG_NAME"),
        env!("CARGO_PKG_VERSION"),
        "workspace",
        module_path!(),
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml"),
    )
    .expect("valid package context");
    let mut descriptors = k::host_descriptors().collect::<Vec<_>>();
    let first = collect_host_descriptors_with_builtins(
        [context.clone()],
        descriptors.clone(),
        &k::builtin_registry(),
    )
    .expect("claims collect");
    descriptors.reverse();
    let reordered =
        collect_host_descriptors_with_builtins([context], descriptors, &k::builtin_registry())
            .expect("reordered claims collect");
    assert_eq!(
        first.to_canonical_json().unwrap(),
        reordered.to_canonical_json().unwrap(),
        "descriptor JSON must not depend on registration order"
    );

    let claims = first
        .descriptors
        .iter()
        .filter(|descriptor| descriptor.id.item_kind() == ItemKind::Claim)
        .collect::<Vec<_>>();
    assert_eq!(claims.len(), 3);
    for descriptor in &claims {
        let DescriptorPayload::ConfigurationRule(rule) = &descriptor.payload else {
            panic!("claim remains a configuration rewrite")
        };
        assert_eq!(rule.sentence_kind, SentenceKind::Claim);
        let claim = rule.claim.as_ref().expect("claim metadata is retained");
        assert_eq!(claim.modality, ClaimModality::AllPaths);
        let (label, universals, existentials, ensures, circularity, or_bool) =
            match descriptor.id.item_name() {
                "branching" => ("branching", 0, 1, true, false, 1),
                "sum_loop" => ("sum-loop", 2, 0, false, false, 0),
                "sum_spec" => ("sum-spec", 2, 0, false, true, 0),
                name => panic!("unexpected claim descriptor {name}"),
            };
        assert_eq!(
            rule.label.as_ref().map(|value| value.name.as_str()),
            Some(label)
        );
        assert_eq!(claim.universals.len(), universals);
        assert_eq!(claim.existentials.len(), existentials);
        assert_eq!(claim.ensures.is_some(), ensures);
        assert_eq!(claim.circularity_key.is_some(), circularity);
        assert_eq!(claim.or_bool_keys.len(), or_bool);
    }

    let semantic = lower_descriptor_bundle(&first).expect("claims lower to semantic IR");
    let reordered_semantic =
        lower_descriptor_bundle(&reordered).expect("reordered claims lower to semantic IR");
    assert_eq!(
        semantic.to_canonical_json().unwrap(),
        reordered_semantic.to_canonical_json().unwrap(),
        "semantic JSON must not depend on registration order"
    );
    let lowered = lower_semantic_theory(&semantic).expect("claims lower to Definition IR");
    let reordered_lowered =
        lower_semantic_theory(&reordered_semantic).expect("reordered claims lower to Definition IR");
    assert_eq!(
        lowered.definition().to_canonical_json().unwrap(),
        reordered_lowered.definition().to_canonical_json().unwrap(),
        "Definition JSON must not depend on registration order"
    );

    let definition_claims = lowered
        .definition()
        .modules()
        .iter()
        .flat_map(krs_ir::DefinitionModule::sentences)
        .filter_map(|sentence| match sentence {
            DefinitionSentence::Rule(rule) if rule.kind() == SentenceKind::Claim => Some(rule),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(definition_claims.len(), 3);
    assert!(definition_claims.iter().all(|rule| rule.claim().is_some()));
    for rule in &definition_claims {
        let claim = rule.claim().unwrap();
        let (universals, existentials, ensures, circularity) = match rule.label().emitted_name() {
            "branching" => (0, 1, true, false),
            "sum-loop" => (2, 0, false, false),
            "sum-spec" => (2, 0, false, true),
            label => panic!("unexpected Definition claim {label}"),
        };
        assert_eq!(claim.modality(), ClaimModality::AllPaths);
        assert_eq!(claim.universals().len(), universals);
        assert_eq!(claim.existentials().len(), existentials);
        assert_eq!(claim.ensures().is_some(), ensures);
        assert_eq!(claim.circularity_origin().is_some(), circularity);
    }

    let emitted = emit_k(&lowered).expect("claims emit deterministic K source");
    let reordered_emitted = emit_k(&reordered_lowered).expect("reordered claims emit K source");
    assert_eq!(emitted, reordered_emitted);
    for label in ["branching", "sum-loop", "sum-spec"] {
        assert!(
            emitted.source().contains(&format!("claim [{label}]:")),
            "missing claim label {label}:\n{}",
            emitted.source()
        );
    }
    assert!(emitted.source().contains("?N:Int"), "{}", emitted.source());
    assert!(emitted.source().contains("_B:Bool"), "{}", emitted.source());
    assert!(emitted.source().contains("ensures "), "{}", emitted.source());
    assert!(emitted.source().contains("orBool"), "{}", emitted.source());
    assert!(emitted.source().contains("circularity"), "{}", emitted.source());
    assert!(!emitted.source().contains("all-path"), "{}", emitted.source());
    assert!(emitted.source().contains("$n"), "{}", emitted.source());
    for rule in &definition_claims {
        let source_entry = emitted
            .source_map()
            .entries()
            .iter()
            .find(|entry| entry.key() == rule.origin().key())
            .expect("each claim sentence has a source-map entry");
        assert!(
            source_entry.generated().is_some(),
            "each rendered claim sentence has a generated range"
        );
    }
    let symbol_map_json = emitted.symbol_map().to_canonical_json().unwrap();
    for label in ["branching", "sum-loop", "sum-spec"] {
        assert!(
            symbol_map_json.contains(label),
            "claim label {label} is missing from the symbol sidecar"
        );
    }

    let adapted = adapt_definition(lowered.definition()).expect("claims adapt to native k-rust");
    let main = adapted
        .definition()
        .main_module()
        .expect("native main module");
    assert_eq!(
        main.local_sentences
            .iter()
            .filter(|sentence| matches!(sentence, NativeSentence::Claim { .. }))
            .count(),
        3
    );
    assert_eq!(
        main.local_sentences
            .iter()
            .filter(|sentence| matches!(sentence, NativeSentence::Rule { attributes, .. }
                if attributes.get_str("label").is_some_and(|label| ["branching", "sum-loop", "sum-spec"].contains(&label))))
            .count(),
        0,
        "claims must never adapt as native rules"
    );
    let truth = NativeTerm::Token {
        token: "true".into(),
        sort: NativeSort::new("Bool"),
    };
    for sentence in &main.local_sentences {
        let NativeSentence::Claim {
            ensures,
            attributes,
            ..
        } = sentence
        else {
            continue;
        };
        match attributes.get_str("label") {
            Some("branching") => assert_ne!(ensures, &truth),
            Some("sum-loop") => {
                assert_eq!(ensures, &truth);
                assert!(attributes.get("circularity").is_none());
            }
            Some("sum-spec") => {
                assert_eq!(ensures, &truth);
                assert_eq!(attributes.get_str("circularity"), Some(""));
            }
            label => panic!("unexpected native claim label {label:?}"),
        }
        assert!(attributes.get("one-path").is_none());
    }
    let native_claim_indices = main
        .local_sentences
        .iter()
        .enumerate()
        .filter_map(|(index, sentence)| {
            matches!(sentence, NativeSentence::Claim { .. }).then_some(index)
        })
        .collect::<Vec<_>>();
    for index in native_claim_indices {
        assert!(
            adapted.origins().iter().any(|mapping| {
                mapping.sentence_index == Some(index) && mapping.role == NativeNodeRole::Sentence
            }),
            "native claim sentence {index} has no origin mapping"
        );
    }

    let artifacts = compile_definition(
        lowered.definition(),
        CompileOptions {
            backend: Backend::Haskell,
            ..CompileOptions::default()
        },
    )
    .expect("public native Haskell-compatible pipeline compiles all three claims");
    assert!(!artifacts.definition_kore.is_empty());
    assert!(!artifacts.syntax_definition_kore.is_empty());
    for label in ["branching", "sum-loop", "sum-spec"] {
        assert!(
            artifacts.definition_kore.contains(label),
            "compiled KORE is missing exact claim label {label}"
        );
    }
}
