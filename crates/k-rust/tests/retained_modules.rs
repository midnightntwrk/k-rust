//! The modules `load_for_compilation` retains outside the main module's import closure, and what
//! compilation does with their sentences.
//!
//! Compilation runs every stage on every retained module and emits only the sentences of the
//! main module's import closure. Cell concretization completes a rule of a module outside that
//! closure with that module's own configuration; when that configuration has no root cell, the
//! rule cannot be completed, and compilation refuses it with an error that names the rule, its
//! module and the main module.

use k_rust::builtin;
use k_rust::diagnostic::DiagnosticCode;
use k_rust::kompile::{
    CompilationBackend, CompileError, CompileOptions, compile_loaded_definition,
};
use k_rust::outer::{LoadOptions, LoadedDefinition, ResolvedSource, load_for_compilation};

/// Five modules: the main module `NR` with the configuration, the syntax module `NR-SYNTAX` that
/// `NR` does not import (its sentences are `{syntax}`), the shared `NR-COMMON`, the syntax-only
/// `NR-PURE` and `NR-RULES` with a rule, neither imported.
fn source(syntax: &str) -> String {
    format!(
        "module NR-COMMON
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)]
endmodule

module NR-SYNTAX
  imports NR-COMMON
  imports INT
  syntax Pgm ::= stop(Int) [symbol(stop)]
{syntax}
endmodule

module NR-PURE
  imports INT-SYNTAX
  syntax Q ::= q(Int)
endmodule

module NR-RULES
  imports INT
  syntax Q2 ::= q2(Int) [symbol(q2)]
  rule q2(0) => q2(1)
endmodule

module NR
  imports NR-COMMON
  imports INT
  configuration <k> $PGM:Pgm </k>
  rule [go]: go(X) => go(X +Int 1) requires X <Int 3
endmodule
"
    )
}

fn load(source: &str) -> LoadedDefinition {
    let mut resolver =
        |_: &str, required: &str| builtin::embedded(required).ok_or_else(|| required.to_owned());
    load_for_compilation(
        ResolvedSource::new("nr.k", source.to_owned()),
        "NR",
        Some("NR-SYNTAX"),
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![builtin::embedded("prelude.md").unwrap()],
            excluded_module_attributes: vec![
                CompilationBackend::Rust
                    .excluded_module_attribute()
                    .to_owned(),
            ],
            ..LoadOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("the definition should load: {error}"))
    .0
}

fn compile(source: &str) -> Result<String, CompileError> {
    compile_loaded_definition(&load(source), CompileOptions::default())
        .map(|artifacts| artifacts.definition_kore)
}

fn retained(loaded: &LoadedDefinition, name: &str) -> bool {
    loaded
        .definition()
        .modules
        .iter()
        .any(|module| module.name == name)
}

#[test]
fn load_for_compilation_retains_the_documented_roots() {
    let loaded = load(&source(""));
    let resolved = loaded.resolved();
    let main = resolved.main_module_id();
    let closure = resolved.transitive_imports(main);
    let outside = |name: &str| {
        let id = resolved
            .module_id(name)
            .unwrap_or_else(|| panic!("{name} is retained"));
        id != main && !closure.contains(&id)
    };
    // The syntax module is a root, and a module without a bubble that imports none with one is
    // retained; neither lies in the main module's closure.
    for name in ["NR-SYNTAX", "NR-PURE"] {
        assert!(retained(&loaded, name), "{name} should be retained");
        assert!(outside(name), "{name} lies outside NR's import closure");
    }
    // The well-known modules compilation reads are retained when present.
    for name in ["K-REFLECTION", "STDIN-STREAM", "STDOUT-STREAM"] {
        assert!(retained(&loaded, name), "{name} should be retained");
    }
    // A module with a rule that no root imports is dropped before inner parsing.
    assert!(!retained(&loaded, "NR-RULES"), "NR-RULES should be dropped");
    assert!(retained(&loaded, "NR") && retained(&loaded, "NR-COMMON"));
}

#[test]
fn a_rewrite_rule_outside_the_main_closure_is_refused_with_its_reason() {
    let error = compile(&source("  rule [s]: stop(0) => stop(1)"))
        .expect_err("a rewrite rule of NR-SYNTAX cannot be completed");
    assert_eq!(error.stage, "concretize cells", "{error}");
    let [diagnostic] = error.diagnostics.as_slice() else {
        panic!("one diagnostic expected: {:?}", error.diagnostics);
    };
    assert_eq!(diagnostic.code, DiagnosticCode::InvalidCellConcretization);
    assert_eq!(
        diagnostic.message,
        "rule NR-SYNTAX.s in module NR-SYNTAX lies outside the main module NR's import closure: \
         compilation completes its cells with module NR-SYNTAX's own configuration, which has no \
         root cell; import NR-SYNTAX from NR or move the rule"
    );
    assert_eq!(diagnostic.source.as_deref(), Some("nr.k"));
    assert_eq!(
        diagnostic
            .location
            .as_ref()
            .map(|location| location.start_line),
        Some(10)
    );
}

#[test]
fn an_unlabelled_rule_outside_the_main_closure_is_named_by_its_location() {
    let error = compile(&source("  rule stop(0) => stop(1)"))
        .expect_err("a rewrite rule of NR-SYNTAX cannot be completed");
    assert_eq!(error.stage, "concretize cells", "{error}");
    let [diagnostic] = error.diagnostics.as_slice() else {
        panic!("one diagnostic expected: {:?}", error.diagnostics);
    };
    assert_eq!(
        diagnostic.message,
        "rule at nr.k:10:3 in module NR-SYNTAX lies outside the main module NR's import closure: \
         compilation completes its cells with module NR-SYNTAX's own configuration, which has no \
         root cell; import NR-SYNTAX from NR or move the rule"
    );
}

#[test]
fn a_function_rule_of_an_unimported_syntax_module_is_not_emitted() {
    let kore = compile(&source(
        "  syntax Int ::= fs(Int) [function, symbol(fs)]\n  rule [s]: fs(X) => X",
    ))
    .unwrap_or_else(|error| panic!("the definition should compile: {error}"));
    assert!(
        kore.contains("label{}(\"NR.go\")"),
        "the main rule is emitted"
    );
    assert!(
        !kore.contains("NR-SYNTAX.s"),
        "the rule of NR-SYNTAX is not emitted"
    );
}

/// A rule of a module the main module imports is completed with the main module's configuration,
/// although its own module sees none, and is emitted.
#[test]
fn a_rewrite_rule_of_an_imported_module_is_completed_with_the_main_configuration() {
    let text = source("").replace(
        "  syntax Pgm ::= go(Int) [symbol(go)]\n",
        "  syntax Pgm ::= go(Int) [symbol(go)]\n  rule [c]: go(0) => go(1)\n",
    );
    let kore =
        compile(&text).unwrap_or_else(|error| panic!("the definition should compile: {error}"));
    assert!(
        kore.contains("label{}(\"NR-COMMON.c\")"),
        "the rule of NR-COMMON is emitted"
    );
}
