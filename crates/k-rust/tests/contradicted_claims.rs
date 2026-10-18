//! What a loaded rewrite rule says about its definedness, on the public path a client uses:
//! compile K source with the prelude, load it ([`Backend::select_definition`]), and read the rule's
//! attributes.
//!
//! `RuleAttributes::preserves_definedness` is the author's claim, as written: the rule is
//! declared `preserves-definedness`. `ComputedRuleAttributes::definedness_discharged` is what the
//! load showed: the rule is not declared so and its terms are defined wherever its left-hand side
//! and `requires` hold. A declared rule is not discharged, since the load proved nothing about it.

use k_rust::{
    backend::{Backend, BackendOptions},
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use k_rust_backend::{definition::BackendDefinition, rule::RewriteRule};

fn compile(source: &str, main: &str) -> String {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("claims.k", source),
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

/// `total` rewrites over constructors only; `declared` is written `preserves-definedness` and
/// applies the partial `pf` (a function without equations, so with no ceil equation); `partial`
/// applies `pf` without the attribute.
const CLAIMS: &str = r"
module CLAIMS
  imports INT
  syntax KItem ::= a() | b() | c() | d() | done(Int)
  syntax Int ::= pf(Int) [function]
  configuration <k> $PGM:KItem </k>
  rule [total]:    <k> a() => b() </k>
  rule [declared]: <k> c() => done(pf(1)) </k> [preserves-definedness]
  rule [partial]:  <k> d() => done(pf(2)) </k>
endmodule
";

fn definition() -> std::sync::Arc<BackendDefinition> {
    let kore = compile(CLAIMS, "CLAIMS");
    let mut backend = Backend::new(&kore, "CLAIMS", BackendOptions::default()).unwrap();
    backend.select_definition(None).unwrap()
}

/// The loaded rewrite rule labelled `CLAIMS.<label>`.
fn rule<'d>(definition: &'d BackendDefinition, label: &str) -> &'d RewriteRule {
    let label = format!("CLAIMS.{label}");
    let rules = definition
        .rewrite_theory()
        .values()
        .flat_map(|groups| groups.values())
        .flatten()
        .filter(|rule| rule.rule.attributes.label.as_deref() == Some(label.as_str()))
        .collect::<Vec<_>>();
    assert_eq!(rules.len(), 1, "{label}");
    &rules[0].rule
}

#[test]
fn a_discharged_rule_does_not_claim_preservation() {
    let definition = definition();
    let attributes = |label: &str| {
        let rule = rule(&definition, label);
        (
            rule.attributes.preserves_definedness,
            rule.computed_attributes.definedness_discharged,
        )
    };
    // Over constructors only: discharged trivially, and not declared.
    assert_eq!(attributes("total"), (false, true));
    // Declared: the author's claim, which the load does not discharge.
    assert_eq!(attributes("declared"), (true, false));
    // Over a partial symbol with no ceil equation: neither; the rule keeps its obligation.
    assert_eq!(attributes("partial"), (false, false));
    assert!(
        !rule(&definition, "partial")
            .computed_attributes
            .undefined_symbols
            .is_empty()
    );
    // The run-time obligation is cleared for the declared and the discharged rule alike.
    for label in ["total", "declared"] {
        assert!(
            rule(&definition, label)
                .computed_attributes
                .undefined_symbols
                .is_empty(),
            "{label}"
        );
    }
}
