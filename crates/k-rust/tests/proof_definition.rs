//! The definition a prover reads from a source compilation.
//!
//! `krust kprove` compiles a specification with `compile_loaded_definition_for_proof` and proves
//! against the KORE value it returns. That value must be the one `definition.kore` denotes for
//! the same compilation: parsing the text `compile_loaded_definition` prints gives an equal
//! definition, with the same diagnostics, and a compilation that fails, fails the same way.

use k_rust::{
    builtin::embedded,
    definition::CheckMode,
    kompile::{
        CompilationBackend, CompileOptions, compile_loaded_definition,
        compile_loaded_definition_for_proof,
    },
    kore::parser::parse_definition,
    outer::{LoadOptions, LoadedDefinition, ResolvedSource, load_with_options},
};

#[path = "support/proof_sources.rs"]
#[allow(dead_code)]
mod proof_sources;
use proof_sources::{
    ANYWHERE_OVERLOAD_REMAINDER, DEFPROBE, DEFPROBE_SPEC, LATER_BINDING_KEPT, LATER_BINDING_RULE,
    NEGATIVE_POWER, UNDEFINED_STEP,
};

fn load(source: &str, spec: &str, definition: &str) -> LoadedDefinition {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    load_with_options(
        ResolvedSource::new("spec.k", source),
        spec,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            configuration_module: Some(definition.to_owned()),
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap()
}

/// The options `kprove` compiles a source with.
fn proof_options(definition: &str) -> CompileOptions {
    CompileOptions {
        backend: CompilationBackend::Rust,
        default_claims_to_all_path: true,
        check_mode: CheckMode::Proof {
            definition_module: definition.to_owned(),
        },
        ..CompileOptions::default()
    }
}

#[test]
fn the_proof_definition_is_the_definition_kore_text_parsed() {
    let cases = [
        (
            ANYWHERE_OVERLOAD_REMAINDER.replace("$NEXT", "mark() ~>"),
            "OVL-SPEC",
            "OVL",
        ),
        (LATER_BINDING_KEPT.to_owned(), "LEMMAKEPT-SPEC", "LEMMAKEPT"),
        (
            LATER_BINDING_RULE.to_owned(),
            "RULESOLVED-SPEC",
            "RULESOLVED",
        ),
        (UNDEFINED_STEP.to_owned(), "UNDEF-SPEC", "UNDEF"),
        (NEGATIVE_POWER.to_owned(), "NEGPOW-SPEC", "NEGPOW"),
        (
            format!("{DEFPROBE}{DEFPROBE_SPEC}"),
            "DEFPROBE-SPEC",
            "DEFPROBE",
        ),
    ];
    for (source, spec, definition) in cases {
        let loaded = load(&source, spec, definition);
        let artifacts = compile_loaded_definition(&loaded, proof_options(definition)).unwrap();
        let proof = compile_loaded_definition_for_proof(&loaded, proof_options(definition))
            .unwrap_or_else(|error| panic!("{spec}: {error}"));
        assert_eq!(
            proof.definition,
            parse_definition(&artifacts.definition_kore).unwrap(),
            "{spec}"
        );
        assert_eq!(proof.diagnostics, artifacts.diagnostics, "{spec}");
    }
}

/// A specification module may hold only claims and simplification rules; both entry points
/// refuse a semantic rule there with the same error.
#[test]
fn a_refused_proof_compilation_fails_the_same_way() {
    let source = r#"
module PDEF
  imports INT
  syntax KItem ::= go(Int) | done(Int)
  rule go(N) => done(N)
endmodule

module PDEF-SPEC
  imports PDEF
  rule done(N) => go(N)
  claim go(1) => done(1)
endmodule
"#;
    let loaded = load(source, "PDEF-SPEC", "PDEF");
    let artifacts = compile_loaded_definition(&loaded, proof_options("PDEF")).unwrap_err();
    let proof = compile_loaded_definition_for_proof(&loaded, proof_options("PDEF")).unwrap_err();
    assert_eq!(proof, artifacts);
    assert!(!proof.diagnostics.is_empty(), "{proof}");
}
