//! Executable vertical preflight for the M3D named-context strictness slice.

use std::path::PathBuf;

use k::Term;
use k_rust::{
    definition::Sentence,
    kompile::{resolve_contexts, resolve_strict},
};
use krs_compiler::{
    PackageContext, collect_host_descriptors_with_builtins, emit_k, lower_descriptor_bundle,
    lower_semantic_theory,
};
use krs_ir::{DefinitionSentence, OriginFrame, ProductionAttribute};
use krs_k_rust::{
    Backend, CompileOptions, NativeNodeRole, adapt_definition, compile_definition,
    prepare_definition,
};

#[path = "m3c.rs"]
mod inherited;

pub use inherited::*;

#[k::context_alias(name = m3d_eval, here = site)]
fn m3d_eval(
    k::cells! {
        k: k::configuration::KCell(site, tail @ ..),
        state @ ..
    }: Machine,
) {
}

#[k::constructor(sort = Expr, syntax = "m3dTwice({value})")]
#[k::seqstrict(using = m3d_eval, sequence = [value], result = KResult)]
pub struct M3dTwice {
    pub value: Term<dyn Expr>,
}

fn main() {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
    let context = PackageContext::new(
        "KRS-M3D-STATIC-SYNTAX",
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
    .expect("context alias and named seqstrict descriptors collect");
    descriptors.reverse();
    let reordered = collect_host_descriptors_with_builtins(
        [context],
        descriptors,
        &k::builtin_registry(),
    )
    .expect("reordered context descriptors collect");
    assert_eq!(
        first.to_canonical_json().unwrap(),
        reordered.to_canonical_json().unwrap(),
        "descriptor JSON must not depend on registration order"
    );

    let semantic = lower_descriptor_bundle(&first).expect("context slice lowers to semantic IR");
    let reordered_semantic =
        lower_descriptor_bundle(&reordered).expect("reordered context slice lowers to semantic IR");
    assert_eq!(
        semantic.to_canonical_json().unwrap(),
        reordered_semantic.to_canonical_json().unwrap(),
        "semantic JSON must not depend on registration order"
    );
    let lowered = lower_semantic_theory(&semantic).expect("context slice lowers to Definition IR");
    let reordered_lowered = lower_semantic_theory(&reordered_semantic)
        .expect("reordered context slice lowers to Definition IR");
    assert_eq!(
        lowered.definition().to_canonical_json().unwrap(),
        reordered_lowered.definition().to_canonical_json().unwrap(),
        "Definition JSON must not depend on registration order"
    );

    let context_aliases = lowered
        .definition()
        .modules()
        .iter()
        .flat_map(|module| module.sentences())
        .filter(|sentence| matches!(sentence, DefinitionSentence::ContextAlias(_)))
        .count();
    assert_eq!(context_aliases, 1);
    let named_seqstrict = lowered
        .definition()
        .modules()
        .iter()
        .flat_map(|module| module.sentences())
        .filter_map(|sentence| match sentence {
            DefinitionSentence::Production(production)
                if production.symbol().emitted_name() == "m3dTwice" => Some(production),
            _ => None,
        })
        .flat_map(|production| production.attributes())
        .filter(|attribute| {
            matches!(
                attribute,
                ProductionAttribute::Strictness { using: Some(_), .. }
            )
        })
        .count();
    assert_eq!(named_seqstrict, 1);

    let emitted = emit_k(&lowered).expect("context slice emits deterministic K source");
    let reordered_emitted =
        emit_k(&reordered_lowered).expect("reordered context slice emits deterministic K source");
    assert_eq!(emitted, reordered_emitted);
    let twice_line = emitted
        .source()
        .lines()
        .find(|line| line.contains("symbol(m3dTwice)"))
        .expect("emitted source contains m3dTwice");
    assert!(twice_line.contains("seqstrict"), "{twice_line}");
    assert!(twice_line.contains("context(m3d_eval)"), "{twice_line}");
    assert!(twice_line.contains("result(KResult)"), "{twice_line}");

    let adapted = adapt_definition(lowered.definition()).expect("context slice adapts natively");
    let main = adapted
        .definition()
        .main_module()
        .expect("adapted main module exists");
    assert_eq!(
        main.local_sentences
            .iter()
            .filter(|sentence| matches!(sentence, Sentence::ContextAlias { .. }))
            .count(),
        1
    );
    assert_eq!(
        main.local_sentences
            .iter()
            .filter(|sentence| matches!(sentence, Sentence::Context { .. }))
            .count(),
        0
    );
    assert_eq!(
        main.local_sentences
            .iter()
            .filter(|sentence| matches!(sentence, Sentence::Rule { attributes, .. }
                if attributes.get("heat").is_some() || attributes.get("cool").is_some()))
            .count(),
        0
    );
    let native_twice = main
        .local_sentences
        .iter()
        .find(|sentence| matches!(sentence, Sentence::Production { label: Some(label), .. }
            if label.name == "m3dTwice"))
        .expect("native m3dTwice production exists");
    assert_eq!(
        native_twice.attributes().get_str("seqstrict"),
        Some("m3d_eval")
    );

    assert_origin_roles(&adapted);

    let prepared = prepare_definition(adapted.definition().clone(), Backend::Llvm)
        .expect("KRS compatibility preparation accepts the context slice");
    let strict = resolve_strict(&prepared.definition)
        .expect("public strictness expansion accepts the named context alias");
    let prefix = "KRS-M3D-STATIC-SYNTAX.m3dTwice1";
    let selected_contexts = strict
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
        .filter(|sentence| matches!(sentence, Sentence::Context { attributes, .. }
            if attributes.get_str("label").is_some_and(|label| label.starts_with(prefix))))
        .count();
    assert_eq!(selected_contexts, 1);
    let resolved = resolve_contexts(&strict).expect("public context expansion succeeds");
    let (heat, cool) = resolved
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
        .filter_map(|sentence| match sentence {
            Sentence::Rule { attributes, .. }
                if attributes.get_str("label").is_some_and(|label| label.starts_with(prefix)) =>
            {
                Some((attributes.get("heat").is_some(), attributes.get("cool").is_some()))
            }
            _ => None,
        })
        .fold((0, 0), |(heat, cool), (is_heat, is_cool)| {
            (heat + usize::from(is_heat), cool + usize::from(is_cool))
        });
    assert_eq!((heat, cool), (1, 1));

    let artifacts = compile_definition(lowered.definition(), CompileOptions::default())
        .expect("permanent public native pipeline compiles the context slice");
    assert!(!artifacts.definition_kore.is_empty());
    assert!(!artifacts.syntax_definition_kore.is_empty());
}

fn assert_origin_roles(adapted: &krs_k_rust::AdaptedDefinition) {
    let count = |role: &NativeNodeRole| {
        adapted
            .origins()
            .iter()
            .filter(|mapping| {
                &mapping.role == role
                    && mapping.origin.origin().frames().iter().any(|frame| {
                        matches!(frame, OriginFrame::Ranged { range, .. }
                            if range.file.package_relative_path() == "src/main.rs")
                    })
            })
            .count()
    };
    assert_eq!(count(&NativeNodeRole::ContextAliasName), 1);
    assert_eq!(count(&NativeNodeRole::ContextAliasHere), 1);
    assert_eq!(count(&NativeNodeRole::ContextAliasCell(0)), 1);
    assert_eq!(count(&NativeNodeRole::ContextAliasFrame(0)), 1);
    assert_eq!(count(&NativeNodeRole::StrictnessContextAlias), 1);
    assert_eq!(count(&NativeNodeRole::StrictnessField(0)), 1);
    assert_eq!(count(&NativeNodeRole::StrictnessResult), 1);

    let source = include_str!("main.rs");
    for (role, expected) in [
        (NativeNodeRole::ContextAliasName, "m3d_eval"),
        (NativeNodeRole::ContextAliasHere, "site"),
        (NativeNodeRole::StrictnessContextAlias, "m3d_eval"),
        (NativeNodeRole::StrictnessField(0), "value"),
    ] {
        let mapping = adapted
            .origins()
            .iter()
            .find(|mapping| {
                mapping.role == role
                    && mapping.origin.origin().frames().iter().any(|frame| {
                        matches!(frame, OriginFrame::Ranged { range, .. }
                            if range.file.package_relative_path() == "src/main.rs")
                    })
            })
            .expect("required native role is mapped");
        let range = mapping
            .origin
            .origin()
            .frames()
            .iter()
            .find_map(|frame| match frame {
                OriginFrame::Ranged { range, .. }
                    if range.file.package_relative_path() == "src/main.rs" => Some(range),
                _ => None,
            })
            .expect("native role retains its authored fixture range");
        assert_eq!(
            &source[usize::try_from(range.start_byte).unwrap()
                ..usize::try_from(range.end_byte).unwrap()],
            expected
        );
    }
}
