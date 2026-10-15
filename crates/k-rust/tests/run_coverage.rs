//! Run coverage through the facade: an execute request that sets `collect_coverage` receives the
//! ids of the rules and equations the run applied, and of those whose condition it began to
//! decide for a matched instance, wherever the backend applied or decided them
//! (docs/compatibility.md, "Run coverage").
//!
//! Ids are resolved through `Backend::rule_catalog` as (label, id) pairs: equal sentences share
//! an id, so a map from id to label would keep only one of them.

use std::collections::BTreeSet;

use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, ExecutionResult, HaltReasonOutput,
        ObservedRequest, ResultModalityOutput, RunCoverageOutput,
    },
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::{codec, parser::parse_pattern},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

#[path = "support/shared.rs"]
mod shared;

const SOURCE: &str = r#"module COVER-SYNTAX
  imports INT-SYNTAX
  syntax Address ::= addr(Int) [symbol(addr)]
  syntax Op ::= load(Address, Int) [symbol(load)]
              | ens(Int) [symbol(ens)]
              | rhsp(Int) [symbol(rhsp)]
              | eqreq(Int) [symbol(eqreq)]
              | rej(Int) [symbol(rej)]
              | ow(Int) [symbol(ow)]
              | ru(Int) [symbol(ru)]
              | rv(Int) [symbol(rv)]
              | pr(Int) [symbol(pr)]
              | hk(Int) [symbol(hk)]
              | d1(Int) [symbol(d1)]
  syntax Prog ::= "halt" [symbol(halt)] | "fault" [symbol(fault)] | "nd" [symbol(nd)]
                | "mid1" [symbol(mid1)] | "mid2" [symbol(mid2)]
                | seq(Op, Prog) [symbol(seq)] | val(Int) [symbol(val)]
endmodule

module COVER
  imports COVER-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> $PGM:Prog </k>

  syntax Int ::= norm(Int) [function, total, symbol(norm)]
               | normE(Int) [function, total, symbol(normE)]
               | part(Int) [function, symbol(part)]
               | inner(Int) [function, total, symbol(inner)]
               | outer(Int) [function, total, symbol(outer)]
               | normR(Int) [function, total, symbol(normR)]
               | owf(Int) [function, total, symbol(owf)]
               | owg(Int) [function, total, symbol(owg)]
               | unused(Int) [function, total, symbol(unused)]
               | pu(Int) [function, symbol(pu)]
               | pv(Int) [function, symbol(pv)]
               | pd(Int) [function, symbol(pd)]

  rule [norm]:    norm(X) => X
  rule [normE]:   normE(X) => X
  rule [part]:    part(X) => X +Int 1 requires X >=Int 0
  rule [inner]:   inner(X) => X
  rule [outer]:   outer(X) => 1 requires inner(X) >=Int 0
  rule [outerow]: outer(_) => 0 [owise]
  rule [normR]:   normR(X) => X
  rule [owg]:     owg(X) => X
  rule [owf1]:    owf(X) => 1 requires owg(X) ==Int 0
  rule [owf2]:    owf(_) => 2 [owise]
  rule [unused]:  unused(X) => X
  rule [puCeil]:  #Ceil(pu(X)) => {(X >=Int 0) #Equals true} [simplification]
  rule [pvCeil]:  #Ceil(pv(_)) => #Top [simplification]
  rule [pdEq]:    pd(X) => X requires X >=Int 0

  rule [load]:    seq(load(addr(A), _), P) => P requires norm(A) ==Int A [preserves-definedness]
  rule [ens]:     seq(ens(A), P) => P ensures normE(A) ==Int A
  rule [rhsp]:    seq(rhsp(A), _) => val(part(A))
  rule [eqreq]:   seq(eqreq(A), _) => val(outer(A))
  rule [rejHigh]: seq(rej(A), _) => fault requires normR(A) <Int 0 [priority(40)]
  rule [rej]:     seq(rej(_), P) => P
  rule [ow]:      seq(ow(A), _) => val(owf(A))
  rule [ru]:      seq(ru(A), _) => val(pu(A))
  rule [rv]:      seq(rv(A), _) => val(pv(A))
  rule [prHigh]:  seq(pr(_), _) => halt [priority(40)]
  rule [prLow]:   seq(pr(_), _) => fault
  rule [hk]:      seq(hk(A), _) => val(A +Int 1)
  rule [d1]:      seq(d1(A), _) => val(#if A >=Int 0 #then A #else pd(A) #fi)
  rule [ndA]:     nd => mid1
  rule [ndB]:     nd => mid2
  rule [mid1]:    mid1 => halt
  rule [mid2]:    mid2 => halt
endmodule
"#;

/// The KORE of `SOURCE`, compiled once per process and inference mode for every test here.
fn definition_kore() -> std::sync::Arc<String> {
    static KORE: shared::Shared<String> = shared::Shared::new();
    KORE.get(compile)
}

fn compile() -> String {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("cover.k", SOURCE),
        "COVER",
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

/// A fresh backend over the shared definition, so no test observes another's backend state.
fn backend() -> Backend {
    Backend::new(&definition_kore(), "COVER", BackendOptions::default()).unwrap()
}

fn top(program: &str) -> String {
    format!(
        "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortProg{{}}, SortKItem{{}}}}({program}), dotk{{}}())), Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\")))"
    )
}

fn int(value: i64) -> String {
    format!("\\dv{{SortInt{{}}}}(\"{value}\")")
}

fn seq(op: &str, argument: i64) -> String {
    format!("Lblseq{{}}(Lbl{op}{{}}({}), Lblhalt{{}}())", int(argument))
}

fn request(program: &str, modality: ResultModalityOutput) -> ExecuteRequest {
    ExecuteRequest {
        result_modality: modality,
        collect_coverage: true,
        ..ExecuteRequest::new(parse_pattern(&top(program)).unwrap())
    }
}

/// The (label, id) pairs of the catalog's axioms that have a label.
fn catalog(backend: &Backend) -> Vec<(String, String)> {
    backend
        .rule_catalog(None)
        .unwrap()
        .into_iter()
        .filter_map(|rule| rule.label.map(|label| (label, rule.id)))
        .collect()
}

/// What `ids` names: the label, without its module, of each `COVER` sentence with an id in
/// `ids`, and every other id as `other:<id>`, so that an exact comparison also catches an id the
/// run should not have recorded.
fn labels(catalog: &[(String, String)], ids: &[String]) -> BTreeSet<String> {
    ids.iter()
        .flat_map(|id| {
            let cover = catalog
                .iter()
                .filter(|(label, other)| other == id && label.starts_with("COVER."))
                .map(|(label, _)| label.trim_start_matches("COVER.").to_owned())
                .collect::<Vec<_>>();
            if cover.is_empty() {
                vec![format!("other:{id}")]
            } else {
                cover
            }
        })
        .collect()
}

fn names(list: &[&str]) -> BTreeSet<String> {
    list.iter().map(|name| (*name).to_owned()).collect()
}

/// The `COVER` labels of a run's (applied, matched) sets.
fn covered(
    catalog: &[(String, String)],
    result: &ExecutionResult,
) -> (BTreeSet<String>, BTreeSet<String>) {
    let coverage = result
        .coverage
        .as_ref()
        .expect("the request asked for coverage");
    (
        labels(catalog, &coverage.applied),
        labels(catalog, &coverage.matched),
    )
}

fn run(backend: &mut Backend, program: &str, modality: ResultModalityOutput) -> ExecutionResult {
    backend.execute(request(program, modality)).unwrap()
}

/// (1) The requires-equation reproducer: the rule and the equation its `requires` used are
/// applied, and no equation the run never evaluated is in either set.
#[test]
fn an_equation_used_in_a_rule_requires_is_applied() {
    let mut backend = backend();
    let catalog = catalog(&backend);
    let program = format!(
        "Lblseq{{}}(Lblload{{}}(Lbladdr{{}}({}), {}), Lblhalt{{}}())",
        int(1),
        int(0)
    );
    let result = run(&mut backend, &program, ResultModalityOutput::PathSet);
    let (applied, matched) = covered(&catalog, &result);
    assert_eq!(applied, names(&["load", "norm"]));
    assert_eq!(matched, names(&["load", "norm"]));
}

/// A program `seq(op(argument), halt)`, the sentences applied, those matched only, and the
/// halt reason of its one leaf when the case pins it.
type Case<'a> = (
    &'a str,
    i64,
    &'a [&'a str],
    &'a [&'a str],
    Option<HaltReasonOutput>,
);

/// (2) Where the backend applied or decided each sentence: a rule's `ensures`, a partial
/// right-hand side, another equation's `requires`, a refuted higher-priority rule, a refuted
/// `owise` competitor, an unconditional ceil equation deciding definedness, a ceil equation
/// that discharged a rule at load, and an equation step deciding the definedness of an operand
/// `#if` does not evaluate.
#[test]
fn every_place_an_equation_is_used_is_covered() {
    let mut backend = backend();
    let catalog = catalog(&backend);
    let cases: [Case; 9] = [
        ("ens", 1, &["ens", "normE"], &[], None),
        ("rhsp", 1, &["rhsp", "part"], &[], None),
        ("eqreq", 1, &["eqreq", "outer", "inner"], &[], None),
        ("rej", 5, &["rej", "normR"], &["rejHigh"], None),
        ("ow", 5, &["ow", "owf2", "owg"], &["owf1"], None),
        (
            "ru",
            1,
            &["ru", "puCeil"],
            &[],
            Some(HaltReasonOutput::Stuck),
        ),
        (
            "ru",
            -1,
            &["ru", "puCeil"],
            &[],
            Some(HaltReasonOutput::Trivial),
        ),
        (
            "rv",
            -1,
            &["rv", "pvCeil"],
            &[],
            Some(HaltReasonOutput::Stuck),
        ),
        // `#if` does not evaluate `pd(5)`; one step of `pdEq` decides that it is defined.
        ("d1", 5, &["d1", "pdEq"], &[], Some(HaltReasonOutput::Stuck)),
    ];
    for (op, argument, applied_only, matched_only, reason) in cases {
        let result = run(
            &mut backend,
            &seq(op, argument),
            ResultModalityOutput::PathSet,
        );
        if let Some(reason) = reason {
            let reasons = result
                .leaves
                .iter()
                .map(|leaf| leaf.reason)
                .collect::<Vec<_>>();
            assert_eq!(reasons, vec![reason], "{op}({argument})");
        }
        let (applied, matched) = covered(&catalog, &result);
        let expected_matched = names(applied_only)
            .union(&names(matched_only))
            .cloned()
            .collect::<BTreeSet<_>>();
        assert_eq!(applied, names(applied_only), "{op}({argument}): applied");
        assert_eq!(matched, expected_matched, "{op}({argument}): matched");
    }
}

/// (3) Collecting changes no other field of the result.
#[test]
fn collecting_coverage_changes_nothing_else() {
    let mut backend = backend();
    for program in [seq("rhsp", 1), seq("ru", -1), "Lblnd{}()".to_owned()] {
        for modality in [
            ResultModalityOutput::PathSet,
            ResultModalityOutput::StateSet,
        ] {
            let mut with = run(&mut backend, &program, modality);
            let without = backend
                .execute(ExecuteRequest {
                    collect_coverage: false,
                    ..request(&program, modality)
                })
                .unwrap();
            assert!(without.coverage.is_none());
            assert!(with.coverage.take().is_some());
            assert_eq!(
                serde_json::to_value(&with).unwrap(),
                serde_json::to_value(&without).unwrap(),
                "{program} {modality:?}"
            );
        }
    }
}

/// (4) The sets cover the paths whose leaves a state-set result merges away, so both
/// modalities give the same sets; a lower-priority rule whose group the step never reaches is
/// in neither set (the documented limit).
#[test]
fn the_sets_are_those_of_the_explored_tree_under_either_modality() {
    let mut backend = backend();
    let catalog = catalog(&backend);
    let state_set = run(&mut backend, "Lblnd{}()", ResultModalityOutput::StateSet);
    let path_set = run(&mut backend, "Lblnd{}()", ResultModalityOutput::PathSet);
    assert_eq!(state_set.leaves.len(), 1);
    assert_eq!(path_set.leaves.len(), 2);
    assert_eq!(state_set.coverage, path_set.coverage);
    let every = names(&["ndA", "ndB", "mid1", "mid2"]);
    assert_eq!(covered(&catalog, &state_set), (every.clone(), every));

    let result = run(&mut backend, &seq("pr", 1), ResultModalityOutput::PathSet);
    let (applied, matched) = covered(&catalog, &result);
    assert_eq!(applied, names(&["prHigh"]));
    assert_eq!(matched, names(&["prHigh"]));
}

/// (5) The sets do not depend on observation, on earlier requests to the backend, or on a
/// module being built by the request that first names it.
#[test]
fn the_sets_do_not_depend_on_observation_or_request_history() {
    let program = seq("ru", -1);
    let mut first = backend();
    let expected = run(&mut first, &program, ResultModalityOutput::PathSet).coverage;
    assert!(expected.is_some());
    let again = run(&mut first, &program, ResultModalityOutput::PathSet).coverage;
    assert_eq!(again, expected, "the same request twice on one backend");
    let fresh = run(&mut backend(), &program, ResultModalityOutput::PathSet).coverage;
    assert_eq!(fresh, expected, "a fresh backend");
    for rules in [None, Some(Vec::new())] {
        let observed = first
            .execute_observed(ObservedRequest {
                request: request(&program, ResultModalityOutput::PathSet),
                rules: rules.clone(),
            })
            .unwrap()
            .coverage;
        assert_eq!(observed, expected, "execute_observed with rules {rules:?}");
    }

    // A backend whose default module is another one builds `COVER` on the first request that
    // names it, discharging its rules' definedness then; the run's sets are the same.
    let mut lazy = Backend::new(&definition_kore(), "K", BackendOptions::default()).unwrap();
    let in_module = || ExecuteRequest {
        module_name: Some("COVER".to_owned()),
        ..request(&program, ResultModalityOutput::PathSet)
    };
    let built = lazy.execute(in_module()).unwrap().coverage;
    let reused = lazy.execute(in_module()).unwrap().coverage;
    assert_eq!(built, expected, "the request that builds the module");
    assert_eq!(reused, expected, "a later request");
    let rv = seq("rv", -1);
    let mut lazy = Backend::new(&definition_kore(), "K", BackendOptions::default()).unwrap();
    let built = lazy
        .execute(ExecuteRequest {
            module_name: Some("COVER".to_owned()),
            ..request(&rv, ResultModalityOutput::PathSet)
        })
        .unwrap()
        .coverage;
    let eager = run(&mut backend(), &rv, ResultModalityOutput::PathSet).coverage;
    assert_eq!(
        built, eager,
        "a load-time discharge is the same whichever request built it"
    );
}

/// (6) The wire form: no `coverage` key unless asked for; `collectCoverage` is read from JSON,
/// and the result lists are sorted, also through the observed JSON entry point.
#[test]
fn the_wire_form_reports_coverage_only_when_asked() {
    let mut backend = backend();
    let state = codec::to_value(&parse_pattern(&top(&seq("ens", 1))).unwrap()).unwrap();
    let parse = |text: String| serde_json::from_str::<serde_json::Value>(&text).unwrap();

    let plain =
        serde_json::from_value::<ExecuteRequest>(serde_json::json!({ "state": state })).unwrap();
    assert!(!plain.collect_coverage);
    let output = parse(backend.execute_json(plain).unwrap());
    assert!(output.get("coverage").is_none(), "{output}");

    let asking = || {
        serde_json::from_value::<ExecuteRequest>(serde_json::json!({
            "state": state,
            "collectCoverage": true,
        }))
        .unwrap()
    };
    let output = parse(backend.execute_json(asking()).unwrap());
    let coverage = serde_json::from_value::<RunCoverageOutput>(output["coverage"].clone()).unwrap();
    assert!(!coverage.applied.is_empty());
    assert!(coverage.applied.is_sorted() && coverage.matched.is_sorted());
    let observed = parse(
        backend
            .execute_observed_json(ObservedRequest {
                request: asking(),
                rules: None,
            })
            .unwrap(),
    );
    assert_eq!(observed["coverage"], output["coverage"]);
}

/// (7) A builtin hook evaluated in a right-hand side is not a sentence and is never recorded.
#[test]
fn a_hook_is_never_recorded() {
    let mut backend = backend();
    let catalog = catalog(&backend);
    let result = run(&mut backend, &seq("hk", 1), ResultModalityOutput::PathSet);
    assert!(
        result.leaves[0]
            .trace
            .iter()
            .any(|entry| entry.unique_id.starts_with("builtin:")),
        "the hook is evaluated on the path"
    );
    let coverage = result.coverage.as_ref().unwrap();
    assert!(
        coverage
            .applied
            .iter()
            .chain(&coverage.matched)
            .all(|id| !id.starts_with("builtin:")),
        "{coverage:?}"
    );
    assert_eq!(covered(&catalog, &result).0, names(&["hk"]));
}
