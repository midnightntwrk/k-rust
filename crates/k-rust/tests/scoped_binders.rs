//! Scoped binders in the frontend's definition check (BIND/A5).
//!
//! A quantifier `#Exists X . P` or `#Forall X . P` binds `X` in `P` and nowhere else
//! (`kast::binding`), so a right-hand-side variable spelled like a binder outside that binder's
//! body has no value when the rule applies, and the check refuses it, located at its rule.
//! A quantifier binds a variable, so a binder that is no variable (`#Exists f(X, X) . P`) is
//! malformed and refused at its rule too. Each case is compiled from source text in either
//! inference build.

use k_rust::{
    builtin::embedded,
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    outer::{LoadOptions, LoadedDefinition, ResolvedSource, load_with_options},
};

fn load(name: &str, source: &str) -> LoadedDefinition {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    load_with_options(
        ResolvedSource::new(format!("{name}.k"), source),
        name,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("{name} does not load: {error:?}"))
}

/// A module `P` over `go(Int)`, `done(Int)` and a constructor `f(Int, Int)` whose only rule is
/// `rule`, written on line 6.
fn probe(rule: &str) -> String {
    format!(
        "module P\n  imports INT\n  imports BOOL\n  syntax KItem ::= go(Int) | done(Int)\n  \
         syntax Pair ::= f(Int, Int)\n  {rule}\nendmodule\n"
    )
}

/// The error diagnostics of compiling `rule` (see [`probe`]), or `None` when it compiles.
fn refusals(rule: &str) -> Option<Vec<Diagnostic>> {
    let loaded = load("P", &probe(rule));
    match compile_loaded_definition(&loaded, CompileOptions::default()) {
        Ok(_) => None,
        Err(error) => Some(
            error
                .diagnostics
                .into_iter()
                .filter(|diagnostic| diagnostic.severity == Severity::Error)
                .collect(),
        ),
    }
}

/// Each error as `code@line: message`.
fn rendered(diagnostics: &[Diagnostic]) -> Vec<String> {
    diagnostics
        .iter()
        .map(|diagnostic| {
            format!(
                "{}@{}: {}",
                diagnostic.code.as_str(),
                diagnostic.location.map_or_else(
                    || "-".to_owned(),
                    |location| location.start_line.to_string()
                ),
                diagnostic.message
            )
        })
        .collect()
}

fn compile_result(rule: &str) -> Result<(), String> {
    let loaded = load("P", &probe(rule));
    compile_loaded_definition(&loaded, CompileOptions::default())
        .map(|_| ())
        .map_err(|error| {
            let errors = error
                .diagnostics
                .into_iter()
                .filter(|diagnostic| diagnostic.severity == Severity::Error)
                .collect::<Vec<_>>();
            if errors.is_empty() {
                format!("{}: {}", error.stage, error.message)
            } else {
                rendered(&errors).join("\n")
            }
        })
}

const UNBOUND_Y: &str = "UnboundVariable@6: Found variable Y on right hand side of rule, not bound on left hand side. Did you mean \"?Y\"?";

/// FU-34/D3: the `ensures` binder binds `Y` in its body only, so the right side's `Y` is unbound.
#[test]
fn an_ensures_binder_does_not_bind_a_right_side_variable_outside_it() {
    assert_eq!(
        compile_result(
            "rule [p]: <k> go(_) => done(Y) ... </k> ensures #Exists Y:Int . {Y #Equals 1}"
        ),
        Err(UNBOUND_Y.to_owned())
    );
}

/// The same right side without a binder is refused alike: the binder never changed the answer.
#[test]
fn a_right_side_variable_without_a_binder_is_refused() {
    assert_eq!(
        compile_result("rule [p]: <k> go(_) => done(Y) ... </k>"),
        Err(UNBOUND_Y.to_owned())
    );
}

/// A `requires` is matched on the Rust backend, so its variables bind in the whole rule; a
/// binder's variable there still binds in the binder's body only.
#[test]
fn a_requires_binder_does_not_bind_a_right_side_variable_outside_it() {
    assert_eq!(
        compile_result(
            "rule [p]: <k> go(_) => done(Y) ... </k> requires #Exists Y:Int . {Y #Equals 1}"
        ),
        Err(UNBOUND_Y.to_owned())
    );
}

/// An anonymous binder binds nothing and reads nothing (BIND/A3): it is no unbound use at a
/// built position, while an anonymous variable of its body is read there like any other.
#[test]
fn an_anonymous_binder_is_no_use_and_its_body_reads_its_anonymous_variables() {
    assert_eq!(
        compile_result(
            "rule [p]: <k> go(X) => done(X) ... </k> ensures #Exists _:Int . {X #Equals X}"
        ),
        Ok(())
    );
    assert_eq!(
        compile_result(
            "rule [p]: <k> go(X) => done(X) ... </k> ensures #Exists _:Int . {X #Equals _}"
        ),
        compile_result("rule [p]: <k> go(X) => done(X) ... </k> ensures {X #Equals _}")
    );
}

/// A binder binds its own body: a variable that occurs only there is bound.
#[test]
fn a_binder_binds_the_variable_in_its_body() {
    assert_eq!(
        compile_result(
            "rule [p]: <k> go(_) => done(0) ... </k> ensures #Exists Y:Int . {Y #Equals 1}"
        ),
        Ok(())
    );
    assert_eq!(
        compile_result(
            "rule [p]: <k> go(X) => done(X) ... </k> requires #Exists Y:Int . {Y #Equals X}"
        ),
        Ok(())
    );
}

/// A quantifier binds a variable, so a binder that is an application is malformed; it is
/// refused at its rule, in a `requires` and in an `ensures` alike.
#[test]
fn a_non_variable_binder_is_refused_at_its_rule() {
    for condition in ["requires", "ensures"] {
        let refused = refusals(&format!(
            "rule [p]: <k> go(X) => done(X) ... </k> {condition} #Exists f(Y, Y) . {{Y #Equals X}}"
        ))
        .unwrap_or_else(|| panic!("the {condition} binder f(Y, Y) compiles"));
        assert_eq!(
            rendered(&refused),
            [
                "InvalidBinder@6: The binder of #Exists must be a variable: a quantifier binds one variable in its body."
            ],
            "{condition}"
        );
        assert!(
            refused
                .iter()
                .all(|diagnostic| diagnostic.code != DiagnosticCode::UnboundVariable)
        );
    }
}
