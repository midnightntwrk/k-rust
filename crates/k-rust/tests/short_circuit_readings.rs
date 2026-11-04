//! A run lists every place where it used the strict definedness of an operand that a
//! short-circuiting reading skips and did not find it defined (`shortCircuitReadings`,
//! docs/compatibility.md, "Short-circuit readings"): the branch a decided `#if` does not select,
//! and the right operand of `andThenBool` and `andBool` after `false`, of `orElseBool` and
//! `orBool` after `true`, and of `impliesBool` after `false`. An entry names the operator, the
//! outcome (`undefined`: k-rust found the operand `\bottom`; `undecided`: k-rust kept its
//! definedness open), the operand's head and the rewrite rule whose work used it; it is a fact of
//! the run only, on no leaf. An operand that is defined, or one that no such reading skips,
//! lists nothing.
//!
//! Every run goes through the facade (`Backend::execute_kore`, `Backend::execute_observed_kore`,
//! the four searches) in both result modalities and both strategies, and the list is read from
//! the JSON a consumer reads.

use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, ExecutionStrategy, ObservedRequest,
        ResultModalityOutput, SearchPatternRequest, SearchRequest, SearchTypeArg,
    },
    builtin::embedded,
    kast::Sort,
    kompile::{
        CompilationBackend, CompileOptions, ConfigurationAssembler, ProgramGrammar,
        compile_loaded_definition,
    },
    kore::{ast::Pattern, parser::parse_pattern},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use serde_json::Value;

const STRATEGIES: [ExecutionStrategy; 2] = [ExecutionStrategy::All, ExecutionStrategy::Any];
const MODALITIES: [ResultModalityOutput; 2] = [
    ResultModalityOutput::PathSet,
    ResultModalityOutput::StateSet,
];

/// Each program passes the deciding operand and the divisor as arguments, so that the rules'
/// right-hand sides are symbolic at load and decided only by a run.
///
/// - `ite`, `at`, `oe`: a decided `#if`, `andThenBool` and `orElseBool` discards `1 /Int D`,
///   which builtin hooks show undefined at `D = 0`.
/// - `gc`: the discarded `1 /Int g(N)` needs more evaluation than the bounded steps that decide
///   a deferred atom (`g(N) => f(N)`), so its definedness stays open; `gs`: one equation step
///   (`f(0) = 1`) shows it defined.
/// - `sa`, `so`, `si`: `andBool`, `orBool` and `impliesBool` evaluate both operands, so a
///   decided left operand leaves an undefined right one making the application `\bottom`;
///   `sp`, `sq`, `s2`: the undefined operand is the left one, or both are.
/// - `tp`: `andThenBool` whose deciding left operand is undefined.
/// - `dp`: `dispatches`' shape, `Ime andThenBool interruptRequested(M)`, through two partial
///   functions and two map lookups whose keys are present, which takes two equation steps;
///   `dm`: the same with a key missing.
/// - `rc`: a discarded `cnt(N)`, a recursion through `down` that takes `2 N + 1` equation steps
///   to show defined.
/// - `w`: a rule whose candidate is undefined only through a discarded operand, with a defined
///   same-priority sibling; `eh`: an equation whose condition is undefined only through a
///   discarded operand, so that its `owise` sibling applies.
/// - `rp`: the prelude's `replace` on defined operands, and a condition
///   `notBool (B andBool f(N) >Int 0)` with both operands defined.
const READINGS: &str = r#"
module MAIN
  imports INT
  imports BOOL
  imports MAP
  imports STRING
  imports K-EQUAL
  syntax Pgm ::= "done" | val(Int) | bv(Bool) | sv(String)
               | ite(Bool, Int) | at(Bool, Int) | oe(Bool, Int)
               | gc(Bool, Int) | gs(Bool, Int)
               | sa(Bool, Int) | so(Bool, Int) | si(Bool, Int)
               | sp(Bool, Int) | sq(Bool, Int) | s2(Int)
               | tp(Bool, Int)
               | dp(Bool) | dm(Bool) | rc(Bool, Int)
               | w(Bool, Int) | eh(Bool, Int)
               | rp(String) | rn(Bool, Int)
  syntax Int ::= f(Int) [function]
               | g(Int) [function]
               | h(Bool, Int) [function]
               | requested(Int, Int) [function]
               | cnt(Int) [function]
               | down(Bool, Int) [function]
  syntax Bool ::= interruptRequested(Map) [function]
  configuration <k> $PGM:Pgm </k>
  rule f(N) => N +Int 1
  rule g(N) => f(N)
  rule requested(A, B) => A &Int B
  rule interruptRequested(M) => requested({M[65535]}:>Int, {M[65295]}:>Int) =/=Int 0
  rule cnt(N) => down(N <=Int 0, N)
  rule down(true, _) => 0
  rule down(false, N) => cnt(N -Int 1)
  rule [h1]: h(B, D) => 1 requires notBool (B andThenBool (1 /Int D >Int 0))
  rule [h2]: h(_, _) => 2 [owise]
  rule [ite]: ite(B, D) => val(#if B #then 1 #else 1 /Int D #fi)
  rule [at]: at(B, D) => bv(B andThenBool (1 /Int D >Int 0))
  rule [oe]: oe(B, D) => bv(B orElseBool (1 /Int D >Int 0))
  rule [gc]: gc(B, N) => val(#if B #then 1 #else 1 /Int g(N) #fi)
  rule [gs]: gs(B, N) => val(#if B #then 1 #else 1 /Int f(N) #fi)
  rule [sa]: sa(B, D) => bv(B andBool (1 /Int D >Int 0))
  rule [so]: so(B, D) => bv(B orBool (1 /Int D >Int 0))
  rule [si]: si(B, D) => bv(B impliesBool (1 /Int D >Int 0))
  rule [sp]: sp(B, D) => bv((1 /Int D >Int 0) andBool B)
  rule [sq]: sq(B, D) => bv((1 /Int D >Int 0) impliesBool B)
  rule [s2]: s2(D) => bv((1 /Int D >Int 0) andBool (1 /Int D >Int 0))
  rule [tp]: tp(B, D) => bv((1 /Int D >Int 0) andThenBool B)
  rule [dp]: dp(Ime) => bv(Ime andThenBool interruptRequested(65535 |-> 1 65295 |-> 1))
  rule [dm]: dm(Ime) => bv(Ime andThenBool interruptRequested(65535 |-> 1))
  rule [rc]: rc(B, N) => val(#if B #then 1 #else cnt(N) #fi)
  rule [w1]: w(B, D) => val(#if B #then 1 #else 1 /Int D #fi)
  rule [w2]: w(_, _) => done
  rule [eh]: eh(B, D) => val(h(B, D))
  rule [rp]: rp(S) => sv(replaceAll(S, "a", "b"))
  rule [rn]: rn(B, N) => done requires notBool (B andBool f(N) >Int 0)
endmodule
"#;

/// Compile `source` (main and syntax module `MAIN`) with the prelude, and assemble the initial
/// configuration whose `$PGM` is each of `programs` at sort `Pgm`.
fn compile(source: &str, programs: &[&str]) -> (String, Vec<Pattern>) {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("readings.k", source),
        "MAIN",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap();
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    let frontend = loaded.into_definition();
    let grammar = ProgramGrammar::new(&frontend).unwrap();
    let initials = programs
        .iter()
        .map(|program| {
            let mut assembler = ConfigurationAssembler::new(
                &grammar,
                "MAIN",
                "MAIN",
                &artifacts.configuration_variables,
            );
            assembler.program(&Sort::new("Pgm"), program).unwrap();
            assembler.finish().unwrap()
        })
        .collect();
    (artifacts.definition_kore, initials)
}

fn backend(kore: &str) -> Backend {
    Backend::new(kore, "MAIN", BackendOptions::default()).unwrap()
}

/// One entry as a consumer reads it: the operator, the outcome, the observing rule's label and
/// who observed it; `head` is checked apart.
type Entry = (Option<String>, String, Option<String>, String);

fn entry(operator: Option<&str>, outcome: &str, rule: Option<&str>) -> Entry {
    (
        operator.map(str::to_owned),
        outcome.to_owned(),
        rule.map(|rule| format!("MAIN.{rule}")),
        "run".to_owned(),
    )
}

/// The entries of a result's `shortCircuitReadings`, in order; every entry has an operand.
fn entries(result: &Value) -> Vec<Entry> {
    result["shortCircuitReadings"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|entry| {
            assert!(entry.get("operand").is_some(), "{entry:#}");
            (
                entry["operator"].as_str().map(str::to_owned),
                entry["outcome"].as_str().unwrap().to_owned(),
                entry["rewriteRuleLabel"].as_str().map(str::to_owned),
                entry["observedIn"].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

fn heads(result: &Value) -> Vec<Option<String>> {
    result["shortCircuitReadings"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|entry| entry["head"].as_str().map(str::to_owned))
        .collect()
}

/// The run of `initial` in every combination of strategy and modality, each through
/// `execute_kore` and `execute_observed_kore`, which list alike.
fn runs(kore: &str, initial: &Pattern) -> Vec<(String, Value)> {
    let mut runs = Vec::new();
    for strategy in STRATEGIES {
        for modality in MODALITIES {
            let request = || ExecuteRequest {
                result_modality: modality,
                strategy,
                ..ExecuteRequest::new(initial.clone())
            };
            let plain =
                serde_json::to_value(backend(kore).execute_kore(request()).unwrap()).unwrap();
            let observed = serde_json::to_value(
                backend(kore)
                    .execute_observed_kore(ObservedRequest {
                        request: request(),
                        rules: None,
                    })
                    .unwrap(),
            )
            .unwrap();
            assert_eq!(
                entries(&plain),
                entries(&observed),
                "observed and unobserved runs list alike"
            );
            runs.push((format!("{strategy:?} {modality:?}"), plain));
        }
    }
    runs
}

/// Every run of each program lists exactly its expected entries, and the definition's load lists
/// none.
fn assert_listed(cases: &[(&str, Vec<Entry>)]) {
    let programs = cases
        .iter()
        .map(|(program, _)| *program)
        .collect::<Vec<_>>();
    let (kore, initials) = compile(READINGS, &programs);
    for ((program, expected), initial) in cases.iter().zip(&initials) {
        for (name, result) in runs(&kore, initial) {
            assert_eq!(
                &entries(&result),
                expected,
                "{program} under {name}: {result:#}"
            );
        }
    }
}

fn leaf_states(result: &Value) -> Vec<String> {
    result["leaves"]
        .as_array()
        .unwrap()
        .iter()
        .map(|leaf| leaf["state"].to_string())
        .collect()
}

/// A decided `#if`, `andThenBool` or `orElseBool` whose discarded operand builtin hooks show
/// undefined: one `undefined` entry with the operator, the head of the undefined application and
/// the rule whose successor's normalization met it; the same rules on a defined operand list
/// nothing.
#[test]
fn a_discarded_operand_hooks_show_undefined_is_listed() {
    assert_listed(&[
        (
            "ite(true, 0)",
            vec![entry(Some("KEQUAL.ite"), "undefined", Some("ite"))],
        ),
        (
            "at(false, 0)",
            vec![entry(Some("BOOL.andThen"), "undefined", Some("at"))],
        ),
        (
            "oe(true, 0)",
            vec![entry(Some("BOOL.orElse"), "undefined", Some("oe"))],
        ),
        ("ite(true, 1)", vec![]),
        ("at(false, 1)", vec![]),
        ("oe(true, 1)", vec![]),
    ]);
    let (kore, initials) = compile(READINGS, &["ite(true, 0)"]);
    let (_, result) = &runs(&kore, &initials[0])[0];
    assert_eq!(
        heads(result),
        [Some("Lbl'UndsSlsh'Int'Unds'".to_owned())],
        "{result:#}"
    );
}

/// A discarded operand whose undefinedness needs more evaluation than the bounded steps that
/// decide a deferred atom is listed `undecided`, with no operator (a deferred atom does not know
/// its operator); one equation step that shows it defined lists nothing.
#[test]
fn an_operand_needing_more_evaluation_is_listed_undecided() {
    let (kore, initials) = compile(READINGS, &["gc(true, -1)", "gs(true, 0)"]);
    for (name, result) in runs(&kore, &initials[0]) {
        assert_undecided_under(&result, "gc", &name);
    }
    for (name, result) in runs(&kore, &initials[1]) {
        assert_eq!(entries(&result), [], "{name}: {result:#}");
    }
}

/// The entries of `result` are all `undecided` deferred-atom decisions (no operator), under
/// `rule` or outside every rule's scope, and at least one is under `rule`: the open atom is
/// carried by the successor, and the step's own remainder and the leaf's constraints, which no
/// one rule's work owns, decide it again.
fn assert_undecided_under(result: &Value, rule: &str, name: &str) {
    let listed = entries(result);
    assert!(
        listed.contains(&entry(None, "undecided", Some(rule))),
        "{name}: {result:#}"
    );
    assert!(
        listed
            .iter()
            .all(|listed| *listed == entry(None, "undecided", Some(rule))
                || *listed == entry(None, "undecided", None)),
        "{name}: {result:#}"
    );
}

/// A defined discarded operand lists nothing: a hook's value, one equation step, and a
/// selected operand of `dispatches`' shape. The list is no over-approximation that every run of
/// a definition with skippable operands meets.
#[test]
fn a_defined_discarded_operand_lists_nothing() {
    assert_listed(&[
        ("ite(true, 2)", vec![]),
        ("gs(true, 0)", vec![]),
        ("dp(true)", vec![]),
    ]);
}

/// The discarded `interruptRequested(M)` of `dispatches`' shape is defined (both keys are
/// present and both functions have a value there), and showing it takes two equation steps
/// (`interruptRequested`, then `requested`): an equation step states its instance's definedness
/// in the atom's place, and those atoms are decided in turn, so nothing is listed. With a key
/// missing, the chain finds `requested`'s argument undefined, and the reading is `undefined`,
/// under the rule and again where the step's remainder decides it.
#[test]
fn a_two_step_chain_through_partial_functions_is_decided() {
    assert_listed(&[("dp(false)", vec![])]);
    let (kore, initials) = compile(READINGS, &["dm(false)"]);
    for (name, result) in runs(&kore, &initials[0]) {
        let listed = entries(&result);
        assert!(
            listed.contains(&entry(None, "undefined", Some("dm"))),
            "{name}: {result:#}"
        );
        assert!(
            listed
                .iter()
                .all(|listed| *listed == entry(None, "undefined", Some("dm"))
                    || *listed == entry(None, "undefined", None)),
            "{name}: {result:#}"
        );
    }
}

/// The steps one deferred atom leads to share one budget: a recursion that shows the discarded
/// `cnt(N)` defined in a few steps lists nothing, and one deeper than the budget is given up and
/// listed `undecided`, although `cnt(200)` is `0`; the run ends either way.
#[test]
fn a_chain_beyond_the_step_budget_is_listed_undecided() {
    let (kore, initials) = compile(READINGS, &["rc(true, 3)", "rc(true, 200)"]);
    for (name, result) in runs(&kore, &initials[0]) {
        assert_eq!(entries(&result), [], "{name}: {result:#}");
    }
    for (name, result) in runs(&kore, &initials[1]) {
        assert_undecided_under(&result, "rc", &name);
    }
}

/// `andBool`, `orBool` and `impliesBool` evaluate both operands: where the left one decides the
/// value, an undefined right one is listed; where the left one does not decide, or is itself
/// undefined, both readings agree and nothing is listed. A reading that skips the left operand
/// is not one a short-circuiting backend takes, so an undefined left operand lists nothing.
#[test]
fn strict_connectives_list_the_operand_an_absorbing_one_makes_irrelevant() {
    assert_listed(&[
        (
            "sa(false, 0)",
            vec![entry(Some("BOOL.and"), "undefined", Some("sa"))],
        ),
        (
            "so(true, 0)",
            vec![entry(Some("BOOL.or"), "undefined", Some("so"))],
        ),
        (
            "si(false, 0)",
            vec![entry(Some("BOOL.implies"), "undefined", Some("si"))],
        ),
        ("sa(true, 0)", vec![]),
        ("so(false, 0)", vec![]),
        ("si(true, 0)", vec![]),
        ("sp(false, 0)", vec![]),
        ("sq(true, 0)", vec![]),
        ("s2(0)", vec![]),
        ("sa(false, 1)", vec![]),
    ]);
}

/// `andThenBool` evaluates its deciding left operand in every reading: an undefined one makes
/// the application `\bottom` in both, whatever the right operand, and lists nothing.
#[test]
fn an_undefined_deciding_operand_lists_nothing() {
    assert_listed(&[("tp(false, 0)", vec![]), ("tp(true, 0)", vec![])]);
}

/// Work on no leaf is listed: the candidate of `w1` that a discarded operand makes undefined,
/// beside its defined sibling `w2`, and `h1`'s condition that a discarded operand makes
/// undefined, so that the `owise` `h2` applies (a reading that skips the operand would apply
/// `h1`). Every leaf is that of the defined work, and carries no entry.
#[test]
fn work_on_no_leaf_is_listed() {
    let (kore, initials) = compile(READINGS, &["w(true, 0)", "eh(false, 0)"]);
    for (name, result) in runs(&kore, &initials[0]) {
        assert_eq!(
            entries(&result),
            [entry(Some("KEQUAL.ite"), "undefined", Some("w1"))],
            "{name}: {result:#}"
        );
        let states = leaf_states(&result);
        assert_eq!(states.len(), 1, "{name}: {result:#}");
        assert!(states[0].contains("Lbldone"), "{name}: {result:#}");
    }
    for (name, result) in runs(&kore, &initials[1]) {
        assert_eq!(
            entries(&result),
            [entry(Some("BOOL.andThen"), "undefined", Some("eh"))],
            "{name}: {result:#}"
        );
        let states = leaf_states(&result);
        assert_eq!(states.len(), 1, "{name}: {result:#}");
        assert!(states[0].contains(r#""value":"2""#), "{name}: {result:#}");
    }
    for (name, result) in runs(&kore, &initials[0])
        .into_iter()
        .chain(runs(&kore, &initials[1]))
    {
        for leaf in result["leaves"].as_array().unwrap() {
            assert!(
                !leaf.to_string().contains("shortCircuit"),
                "{name}: {leaf:#}"
            );
        }
    }
}

/// A ground run through the prelude's `replace`, whose condition is
/// `Count >Int 0 andBool findString(...) >=Int 0` with both operands defined, and a rule
/// condition `notBool (B andBool f(N) >Int 0)` with both operands defined, list nothing.
#[test]
fn a_defined_condition_through_the_prelude_lists_nothing() {
    assert_listed(&[
        ("rp(\"aXa\")", vec![]),
        ("rp(\"X\")", vec![]),
        ("rn(true, 0)", vec![]),
        ("rn(false, 0)", vec![]),
    ]);
}

/// The load of a definition whose right-hand sides hold symbolic discarded operands lists no
/// `undecided` entry of its own (it lists none at all here), so its runs' lists hold only what
/// they met.
#[test]
fn the_load_lists_no_undecided_reading() {
    let (kore, initials) = compile(READINGS, &["ite(true, 1)", "ite(true, 0)"]);
    for initial in &initials {
        for (name, result) in runs(&kore, initial) {
            assert!(
                entries(&result)
                    .iter()
                    .all(|(_, _, _, observed_in)| observed_in == "run"),
                "{name}: {result:#}"
            );
        }
    }
}

/// Every search response carries the list, from the same work an execution does.
#[test]
fn search_responses_list_readings() {
    let (kore, initials) = compile(READINGS, &["ite(true, 0)", "ite(true, 1)"]);
    let target = parse_pattern("VarResult:SortGeneratedTopCell{}").unwrap();
    for (initial, expected) in initials.iter().zip([
        vec![entry(Some("KEQUAL.ite"), "undefined", Some("ite"))],
        vec![],
    ]) {
        let search = SearchRequest {
            search_type: SearchTypeArg::All,
            ..SearchRequest::new(initial.clone())
        };
        let pattern = SearchPatternRequest {
            search_type: SearchTypeArg::All,
            ..SearchPatternRequest::new(initial.clone(), target.clone())
        };
        let mut backend = backend(&kore);
        for response in [
            serde_json::to_value(backend.search_kore(search.clone()).unwrap()).unwrap(),
            serde_json::to_value(backend.search_paths_kore(search).unwrap()).unwrap(),
            serde_json::to_value(backend.search_pattern_kore(pattern.clone()).unwrap()).unwrap(),
            serde_json::to_value(backend.search_pattern_paths_kore(pattern).unwrap()).unwrap(),
        ] {
            assert_eq!(entries(&response), expected, "{response:#}");
            if expected.is_empty() {
                assert!(
                    response.get("shortCircuitReadings").is_none(),
                    "{response:#}"
                );
            }
        }
    }
}

#[path = "support/pattern_results.rs"]
mod pattern_results;

/// The pattern result forms serialize as the `Value` forms on a run's short-circuit readings,
/// in each execution and search.
#[test]
fn readings_serialize_alike_as_patterns() {
    let (kore, initials) = compile(READINGS, &["ite(true, 0)"]);
    let [initial] = initials.as_slice() else {
        panic!("one program");
    };
    let fresh = || backend(&kore);
    let mut seen = pattern_results::executions_alike(fresh, &ExecuteRequest::new(initial.clone()));
    seen.extend(pattern_results::searches_alike(
        fresh,
        &SearchRequest {
            search_type: SearchTypeArg::All,
            ..SearchRequest::new(initial.clone())
        },
    ));
    seen.extend(pattern_results::pattern_searches_alike(
        fresh,
        &SearchPatternRequest {
            search_type: SearchTypeArg::All,
            ..SearchPatternRequest::new(
                initial.clone(),
                parse_pattern("VarResult:SortGeneratedTopCell{}").unwrap(),
            )
        },
    ));
    assert!(
        pattern_results::shows(&seen, "shortCircuitReadings"),
        "{seen:#?}"
    );
}
