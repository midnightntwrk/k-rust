//! The critical-pair check of function equations on the public path a client uses: compile K
//! source with the prelude, load it ([`Backend::select_definition`]), and read the load's verdict
//! ([`BackendDefinition::value_claims`]) or the check run again in every scope
//! ([`BackendDefinition::value_claims_in_scope`] with [`CheckScope::All`])
//! (`docs/compatibility.md`, "Value claims").
//!
//! A pair is `refuted` only when its two requires hold on no instance in any model. These tests
//! pin that on guards whose literals are spelled like Booleans but belong to another sort.

use k_rust::{
    backend::{Backend, BackendOptions},
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use k_rust_backend::{
    confluence::{CheckScope, UnjoinedPair, UnjoinedReason, ValueClaims},
    definition::BackendDefinition,
};

fn compile(source: &str, main: &str) -> String {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("pairs.k", source),
        main,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .unwrap();
    compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap()
        .definition_kore
}

/// The loaded definition of module `PAIRS` with `declarations` added.
///
/// Every definition here declares the anywhere head `nw`, so that it has a symbol whose claims a
/// pair can withdraw: the check classifies no pair of a definition without one, in either scope.
fn definition(declarations: &str) -> std::sync::Arc<BackendDefinition> {
    let source = format!(
        r#"module PAIRS
  imports INT
  imports BOOL
  imports STRING
  imports K-EQUAL
  syntax MyTok ::= r"[a-z][a-z0-9]*" [token]
  syntax Wrap ::= wr(MyTok) [symbol(wr)] | nw(Wrap) [symbol(nw)]
  rule nw(wr(T)) => wr(T) [anywhere]
  syntax Prog ::= go(MyTok) [symbol(go)] | val(Int) [symbol(val)]
{declarations}
  configuration <k> $PGM:Prog </k>
endmodule
"#
    );
    let kore = compile(&source, "PAIRS");
    let mut backend = Backend::new(&kore, "PAIRS", BackendOptions::default()).unwrap();
    backend.select_definition(None).unwrap()
}

/// The non-joined pairs of `claims` between the equations labelled `first` and `second` of
/// module `PAIRS`, in either order.
fn pairs_between<'a>(claims: &'a ValueClaims, first: &str, second: &str) -> Vec<&'a UnjoinedPair> {
    let label = |pair_rule: &k_rust_backend::rule::RewriteRule| {
        pair_rule.attributes.label.clone().unwrap_or_default()
    };
    let (first, second) = (format!("PAIRS.{first}"), format!("PAIRS.{second}"));
    claims
        .unjoined()
        .iter()
        .filter(|pair| {
            let labels = (label(&pair.first), label(&pair.second));
            labels == (first.clone(), second.clone()) || labels == (second.clone(), first.clone())
        })
        .collect()
}

/// `T =/=K #token("true", "MyTok")` beside `T =/=K #token("false", "MyTok")` holds at `T = abc`,
/// where the two equations give 1 and 2: the pair is not refuted, and the full check reports it
/// with its open conditions.
#[test]
fn a_token_spelled_true_or_false_is_not_a_boolean_literal() {
    let definition = definition(
        r#"  syntax Int ::= ht(MyTok) [function, symbol(ht)]
  rule [a]: ht(T) => 1 requires T =/=K #token("true", "MyTok")
  rule [b]: ht(T) => 2 requires T =/=K #token("false", "MyTok")"#,
    );
    let all = definition.value_claims_in_scope(CheckScope::All);
    let pairs = pairs_between(&all, "a", "b");
    assert_eq!(
        pairs
            .iter()
            .map(|pair| pair.reason.clone())
            .collect::<Vec<_>>(),
        [UnjoinedReason::ConditionOpen],
        "{:?}",
        all.unjoined()
    );
}

/// The same over `String`: `#Not({S #Equals "true"})` beside `#Not({S #Equals "false"})` holds at
/// `S = "abc"`.
#[test]
fn a_string_spelled_true_or_false_is_not_a_boolean_literal() {
    let definition = definition(
        r#"  syntax Int ::= hs(String) [function, symbol(hs)]
  rule [a]: hs(S) => 1 requires #Not({ S #Equals "true" })
  rule [b]: hs(S) => 2 requires #Not({ S #Equals "false" })"#,
    );
    let all = definition.value_claims_in_scope(CheckScope::All);
    let pairs = pairs_between(&all, "a", "b");
    assert_eq!(
        pairs
            .iter()
            .map(|pair| pair.reason.clone())
            .collect::<Vec<_>>(),
        [UnjoinedReason::ConditionOpen],
        "{:?}",
        all.unjoined()
    );
}

/// With the anywhere head `nw` in reach of `hg`'s second argument, the load itself classifies the
/// `hg` pair: guarded by the Boolean-like spellings it is reported and withdraws the claims of
/// `hg` and `nw`, exactly as with any other two spellings of the token sort.
#[test]
fn the_load_reports_a_pair_guarded_by_token_spellings_of_true_and_false() {
    for (first, second) in [("true", "false"), ("aaa", "bbb")] {
        let definition = definition(&format!(
            r#"  syntax Int ::= hg(MyTok, Wrap) [function, symbol(hg)]
  rule [c]: hg(T, _W) => 1 requires T =/=K #token("{first}", "MyTok")
  rule [d]: hg(T, _W) => 2 requires T =/=K #token("{second}", "MyTok")"#
        ));
        let load = definition.value_claims();
        let pairs = pairs_between(load, "c", "d");
        assert_eq!(
            pairs
                .iter()
                .map(|pair| pair.reason.clone())
                .collect::<Vec<_>>(),
            [UnjoinedReason::ConditionOpen],
            "{first}/{second}: {:?}",
            load.unjoined()
        );
        let tainted = load.tainted_symbols();
        for symbol in ["Lblhg", "Lblnw"] {
            assert!(
                tainted.iter().any(|name| name.as_ref() == symbol),
                "{first}/{second}: {symbol} is not tainted: {tainted:?}"
            );
        }
    }
}
