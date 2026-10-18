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

/// Contradicted claims a run observes (docs/compatibility.md, "A contradicted total attribute is
/// named, not repaired"): an application of a symbol declared `total` that one of its own
/// equations reduces to bottom on defined arguments is a `contradicted-claim` path fact on every
/// leaf whose path's decisions rest on it, and the result lists every such record the run met
/// (`contradictedClaims`), including those of work that ended on no reported leaf. A record
/// changes no decision: every leaf, its reason and the result's order are those of a run
/// without the records.
///
/// Every run goes through the facade, under both strategies and both result modalities, and is
/// compared with `execute_observed`; the records are read from the JSON a consumer reads.
mod observed {
    use std::collections::BTreeSet;

    use k_rust::{
        backend::{
            Backend, BackendOptions, ExecuteRequest, ExecutionStrategy, ObservedRequest,
            ResultModalityOutput,
        },
        builtin::embedded,
        kast::Sort,
        kompile::{
            CompilationBackend, CompileOptions, ConfigurationAssembler, ProgramGrammar,
            compile_loaded_definition,
        },
        kore::{ast::Pattern, codec, printer::Printer},
        outer::{LoadOptions, ResolvedSource, load_with_options},
    };
    use serde_json::Value;

    pub(super) const STRATEGIES: [ExecutionStrategy; 2] =
        [ExecutionStrategy::All, ExecutionStrategy::Any];
    pub(super) const MODALITIES: [ResultModalityOutput; 2] = [
        ResultModalityOutput::PathSet,
        ResultModalityOutput::StateSet,
    ];

    /// `td` and `tc` are declared `total`; `td(0)` is `10 /Int 0`, bottom, and so is `tc(0)`,
    /// through the partial `tp`. Every rule that needs one of them on `0` observes the
    /// contradiction: in a `requires` (`r`, `ro`, `rc`, `mbx`), in an equation's `requires`
    /// (`fe1` through `e`), in a right-hand side (`sibtd`, `s3a`, `s3b`), or inside an attempt
    /// on an `Unspecified` application that is undone (`gu1` through `un`). `rp` and `rq` reach
    /// bottom through partial symbols only, which contradicts nothing.
    pub(super) const CLAIMS: &str = r#"
module MAIN
  imports INT
  imports BOOL
  imports STRING
  syntax Pgm ::= "done" | val(Int) | w(Int) | "mx"
               | r(Int) | ro(Int) | rp(Int) | rc(Int) | rq(Int) | e(Int)
               | sib(Int) | s3(Int) | m2(Int) | ma(Int) | mb(Int) | mj(Int) | un(String)
  syntax Int ::= td(Int) [function, total]
               | tp(Int) [function]
               | tc(Int) [function, total]
               | fe(Int) [function, total]
               | cntu(String, String) [function, total, hook(STRING.countAllOccurrences)]
               | gu(Int) [function, total]
  configuration <k> $PGM:Pgm </k>
  rule [tdeq]:  td(I) => 10 /Int (I +Int 0)
  rule [tpeq]:  tp(I) => 10 /Int (I +Int 0)
  rule [tceq]:  tc(I) => tp(I)
  rule [fe1]:   fe(I) => 1 requires td(I) >Int 0
  rule [fe2]:   fe(_) => 2 [owise]
  rule [r]:     r(I) => done requires td(I) >Int 0
  rule [ro]:    ro(I) => done requires td(I) >Int 0
  rule [roow]:  ro(_) => val(0) [owise]
  rule [rp]:    rp(I) => done requires tp(I) >Int 0
  rule [rc]:    rc(I) => done requires tc(I) >Int 0
  rule [rq]:    rq(I) => done requires 10 /Int I >Int 0
  rule [e]:     e(I) => val(fe(I))
  rule [sibtd]: sib(X) => val(td(X))
  rule [sibok]: sib(_) => done
  rule [s3a]:   s3(I) => val(td(I)) requires I ==Int 0
  rule [s3b]:   s3(I) => w(td(I)) requires I ==Int 0
  rule [m2a]:   m2(X) => ma(X)
  rule [m2b]:   m2(X) => mb(X)
  rule [ma]:    ma(X) => mj(X)
  rule [mbx]:   mb(X) => mx requires td(X) >Int 0
  rule [mbow]:  mb(X) => mj(X) [owise]
  rule [mj]:    mj(X) => val(X)
  rule [cntu]:  cntu(S, "") => gu(cntu(S, ""))
  rule [gu1]:   gu(X) => X requires td(0) >Int X
  rule [un]:    un(S) => val(cntu(S, ""))
endmodule
"#;

    /// The same definition with every `total` claim removed.
    pub(super) fn claim_free(source: &str) -> String {
        source.replace("[function, total", "[function")
    }

    /// Compile `source` (main and syntax module `MAIN`) with the prelude and assemble the
    /// initial configuration whose `$PGM` is `program` at sort `Pgm`.
    pub(super) fn compile(source: &str, program: &str) -> (String, Pattern) {
        compile_in(source, "MAIN", program)
    }

    /// [`compile`] with main and syntax module `main`.
    pub(super) fn compile_in(source: &str, main: &str, program: &str) -> (String, Pattern) {
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new("claims.k", source),
            main,
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
        let mut assembler =
            ConfigurationAssembler::new(&grammar, main, main, &artifacts.configuration_variables);
        assembler.program(&Sort::new("Pgm"), program).unwrap();
        (artifacts.definition_kore, assembler.finish().unwrap())
    }

    pub(super) fn backend(kore: &str) -> Backend {
        backend_in(kore, "MAIN")
    }

    /// [`backend`] for main module `main`.
    pub(super) fn backend_in(kore: &str, main: &str) -> Backend {
        Backend::new(kore, main, BackendOptions::default()).unwrap()
    }

    /// One record as a consumer reads it: the claim, the contradicted symbol's K label, the
    /// equation's label, the label of the rewrite rule whose attempt or successor observed it,
    /// and whether the contradicted application is ground.
    pub(super) type Record = (String, String, String, Option<String>, bool);

    /// The record of `symbol(_)`'s `total` claim, contradicted by `equation` and observed by
    /// `rule`, at a ground application.
    pub(super) fn record(symbol: &str, equation: &str, rule: Option<&str>) -> Record {
        (
            "total".to_owned(),
            format!("{symbol}(_)_MAIN_Int_Int"),
            format!("MAIN.{equation}"),
            rule.map(|rule| format!("MAIN.{rule}")),
            true,
        )
    }

    fn read_record(entry: &Value) -> Record {
        (
            entry["claim"].as_str().unwrap_or("?").to_owned(),
            entry["kLabel"].as_str().unwrap_or("?").to_owned(),
            entry["ruleLabel"].as_str().unwrap_or("?").to_owned(),
            entry["rewriteRuleLabel"].as_str().map(str::to_owned),
            entry["ground"].as_bool().unwrap_or(false),
        )
    }

    /// The records among a leaf's diagnostics.
    pub(super) fn records(leaf: &Value) -> BTreeSet<Record> {
        leaf["diagnostics"]
            .as_array()
            .into_iter()
            .flatten()
            .filter(|diagnostic| diagnostic["kind"] == "contradicted-claim")
            .map(read_record)
            .collect()
    }

    /// The result's list of every record the run observed, in order.
    pub(super) fn run_records(result: &Value) -> Vec<Record> {
        result["contradictedClaims"]
            .as_array()
            .into_iter()
            .flatten()
            .map(read_record)
            .collect()
    }

    pub(super) fn leaves(result: &Value) -> &Vec<Value> {
        result["leaves"].as_array().unwrap()
    }

    /// A leaf's state, printed.
    pub(super) fn printed(leaf: &Value) -> String {
        Printer::compact().print_pattern(&codec::from_value(&leaf["state"]).unwrap())
    }

    /// The one leaf whose printed state contains `needle`.
    pub(super) fn leaf_with<'a>(result: &'a Value, needle: &str) -> &'a Value {
        let found = leaves(result)
            .iter()
            .filter(|leaf| printed(leaf).contains(needle))
            .collect::<Vec<_>>();
        assert_eq!(found.len(), 1, "one leaf holds {needle}: {result:#}");
        found[0]
    }

    /// The result of `execute` as JSON, checked equal to `execute_observed`'s in each leaf's
    /// state, reason and records and in the result's list.
    pub(super) fn execute(
        kore: &str,
        initial: &Pattern,
        modality: ResultModalityOutput,
        strategy: ExecutionStrategy,
    ) -> Value {
        let request = || ExecuteRequest {
            result_modality: modality,
            strategy,
            ..ExecuteRequest::new(initial.clone())
        };
        let plain = backend(kore).execute(request()).unwrap();
        let observed = backend(kore)
            .execute_observed(ObservedRequest {
                request: request(),
                rules: None,
            })
            .unwrap();
        let plain = serde_json::to_value(&plain).unwrap();
        let observed = serde_json::to_value(&observed).unwrap();
        let essence = |result: &Value| {
            let leaves = leaves(result)
                .iter()
                .map(|leaf| (leaf["state"].clone(), leaf["reason"].clone(), records(leaf)))
                .collect::<Vec<_>>();
            (leaves, run_records(result))
        };
        assert_eq!(
            essence(&plain),
            essence(&observed),
            "observed and unobserved runs record alike"
        );
        plain
    }

    /// Every combination of strategy and modality, with its name.
    pub(super) fn each_run(
        kore: &str,
        initial: &Pattern,
    ) -> Vec<(String, ExecutionStrategy, ResultModalityOutput, Value)> {
        let mut runs = Vec::new();
        for strategy in STRATEGIES {
            for modality in MODALITIES {
                runs.push((
                    format!("{strategy:?} {modality:?}"),
                    strategy,
                    modality,
                    execute(kore, initial, modality, strategy),
                ));
            }
        }
        runs
    }

    /// Every leaf of `program` and the result's list carry exactly `expected`, in every
    /// combination, and the claim-free definition gives the same leaves with no record and no
    /// `contradictedClaims` key.
    pub(super) fn assert_recorded(program: &str, expected: &[Record]) {
        let (kore, initial) = compile(CLAIMS, program);
        let (free, free_initial) = compile(&claim_free(CLAIMS), program);
        for (name, strategy, modality, result) in each_run(&kore, &initial) {
            let context = format!("{program} under {name}: {result:#}");
            assert!(!leaves(&result).is_empty(), "{context}");
            for leaf in leaves(&result) {
                assert_eq!(
                    records(leaf),
                    expected.iter().cloned().collect::<BTreeSet<_>>(),
                    "{context}"
                );
            }
            assert_eq!(run_records(&result), expected, "{context}");
            let free = execute(&free, &free_initial, modality, strategy);
            assert!(
                leaves(&free).iter().all(|leaf| records(leaf).is_empty()),
                "claim-free {context}"
            );
            assert!(
                free.get("contradictedClaims").is_none(),
                "claim-free {free:#}"
            );
        }
    }
}

use std::collections::BTreeSet;

use observed::{
    CLAIMS as CONTRADICTIONS, assert_recorded, compile as compile_program, each_run, leaf_with,
    leaves, record, records, run_records,
};
use serde_json::Value;

/// A `requires` refuted through a contradicted `total` callee: the rule does not apply (an
/// undefined condition is not true), the state is stuck, and its leaf and the result name the
/// claim, the equation and the rule whose attempt observed it.
#[test]
fn a_requires_refuted_through_a_contradicted_total_names_the_claim_on_the_stuck_leaf() {
    assert_recorded("r(0)", &[record("td", "tdeq", Some("r"))]);
    // `r(1)` observes no bottom.
    assert_recorded("r(1)", &[]);
}

/// The `owise` rule applies because the first rule's `requires` was refuted through the
/// contradiction; the `val(0)` leaf rests on it.
#[test]
fn an_owise_rule_taken_after_a_refuted_requires_carries_the_record() {
    assert_recorded("ro(0)", &[record("td", "tdeq", Some("ro"))]);
}

/// `fe(0)` takes its `owise` equation because `fe1`'s `requires` is refuted through `td(0)`; the
/// `val(2)` leaf rests on it.
#[test]
fn an_equation_requires_refuted_through_a_contradiction_is_recorded() {
    assert_recorded("e(0)", &[record("td", "tdeq", Some("e"))]);
}

/// `tc(0)` reaches bottom through the partial `tp`: the contradicted claim is `tc`'s, not
/// `tp`'s. Bottom reached through partial symbols only (`rp`, `rq`) contradicts nothing.
#[test]
fn the_contradicted_callee_is_named_and_partial_symbols_contradict_nothing() {
    assert_recorded("rc(0)", &[record("tc", "tceq", Some("rc"))]);
    assert_recorded("rp(0)", &[]);
    assert_recorded("rq(0)", &[]);
}

/// `sibtd`'s successor `val(td(0))` is bottom and `sibok` covers every instance. Under
/// strategy all the candidate vanishes after the step and the `done` leaf does not rest on it:
/// the leaf is clean and the result lists the record. Under strategy any the sequential step
/// decides the candidate undefined before it takes `sibok`, so the `done` leaf rests on it.
#[test]
fn a_candidate_a_defined_sibling_covers_is_on_the_run_list_and_on_the_leaves_that_rest_on_it() {
    let (kore, initial) = compile_program(CONTRADICTIONS, "sib(0)");
    let expected = record("td", "tdeq", Some("sibtd"));
    for (name, strategy, _, result) in each_run(&kore, &initial) {
        let context = format!("{name}: {result:#}");
        let done = leaf_with(&result, "Lbldone");
        assert_eq!(leaves(&result).len(), 1, "{context}");
        let on_leaf = match strategy {
            k_rust::backend::ExecutionStrategy::All => BTreeSet::new(),
            _ => BTreeSet::from([expected.clone()]),
        };
        assert_eq!(records(done), on_leaf, "{context}");
        assert_eq!(
            run_records(&result),
            std::slice::from_ref(&expected),
            "{context}"
        );
    }
}

/// `s3a` and `s3b` both apply to `s3(0)` and both results are bottom. Each record names the rule
/// whose candidate observed it, so the two stay distinct. Under strategy any the sequential step
/// offers `s3a`'s instances to `s3b`, so the one `Trivial` leaf rests on both. Under strategy
/// all each candidate is its own undefined step, a `Trivial` leaf per rule, found when its
/// successor is normalized; its instances are those where the other candidate is not defined
/// either, which the other's normalization decides, so each leaf rests on both records. Without
/// the claims the step itself finds both results undefined: the halts are the same and nothing
/// is named.
#[test]
fn each_rule_whose_candidate_observed_a_contradiction_is_named() {
    let (kore, initial) = compile_program(CONTRADICTIONS, "s3(0)");
    let (free, free_initial) = compile_program(&observed::claim_free(CONTRADICTIONS), "s3(0)");
    let s3a = record("td", "tdeq", Some("s3a"));
    let s3b = record("td", "tdeq", Some("s3b"));
    for (name, strategy, modality, result) in each_run(&kore, &initial) {
        let context = format!("{name}: {result:#}");
        let trivial = leaves(&result)
            .iter()
            .map(|leaf| (leaf["ruleLabel"].clone(), records(leaf)))
            .collect::<Vec<_>>();
        match strategy {
            k_rust::backend::ExecutionStrategy::All => {
                assert_eq!(
                    trivial,
                    [
                        (
                            Value::from("MAIN.s3a"),
                            BTreeSet::from([s3a.clone(), s3b.clone()])
                        ),
                        (
                            Value::from("MAIN.s3b"),
                            BTreeSet::from([s3a.clone(), s3b.clone()])
                        ),
                    ],
                    "{context}"
                );
            }
            _ => assert_eq!(
                trivial,
                [(
                    Value::from("MAIN.s3b"),
                    BTreeSet::from([s3a.clone(), s3b.clone()])
                )],
                "{context}"
            ),
        }
        for leaf in leaves(&result) {
            assert_eq!(leaf["reason"], "trivial", "{context}");
            assert!(leaf.get("contradictedTotal").is_some(), "{context}");
        }
        assert_eq!(
            run_records(&result).into_iter().collect::<BTreeSet<_>>(),
            BTreeSet::from([s3a.clone(), s3b.clone()]),
            "{context}"
        );
        let free = observed::execute(&free, &free_initial, modality, strategy);
        assert!(
            leaves(&free)
                .iter()
                .all(|leaf| leaf["reason"] == "trivial" && records(leaf).is_empty()),
            "claim-free {name}: {free:#}"
        );
        assert!(free.get("contradictedClaims").is_none(), "{free:#}");
    }
}

/// Under strategy all `m2(0)` reaches `mj(0)` on two paths, and only the `mb` path's decision
/// rests on a contradiction (`mbx`'s refuted `requires`). Under path-set the `mb` path's leaf carries the
/// record and the `ma` path's does not; under state-set the two arrivals merge into one leaf
/// whatever their records, and the result lists the record.
#[test]
fn a_record_never_blocks_a_merge_and_an_absorbed_arrival_s_record_is_on_the_run_list() {
    let (kore, initial) = compile_program(CONTRADICTIONS, "m2(0)");
    let expected = record("td", "tdeq", Some("mbx"));
    // Strategy any takes `m2a` alone: one path, which meets no contradiction.
    for (name, strategy, modality, result) in each_run(&kore, &initial) {
        let context = format!("{name}: {result:#}");
        if matches!(strategy, k_rust::backend::ExecutionStrategy::Any) {
            assert_eq!(leaves(&result).len(), 1, "{context}");
            assert!(records(&leaves(&result)[0]).is_empty(), "{context}");
            assert!(result.get("contradictedClaims").is_none(), "{context}");
            continue;
        }
        match modality {
            k_rust::backend::ResultModalityOutput::PathSet => {
                assert_eq!(leaves(&result).len(), 2, "{context}");
                let marked = leaves(&result).iter().map(records).collect::<Vec<_>>();
                assert_eq!(
                    marked.iter().filter(|records| records.is_empty()).count(),
                    1,
                    "{context}"
                );
                assert!(
                    marked.contains(&BTreeSet::from([expected.clone()])),
                    "{context}"
                );
            }
            _ => assert_eq!(leaves(&result).len(), 1, "{context}"),
        }
        assert!(
            leaves(&result)
                .iter()
                .all(|leaf| leaf["reason"] == "stuck" && observed::printed(leaf).contains("Lblval")),
            "{context}"
        );
        assert_eq!(
            run_records(&result),
            std::slice::from_ref(&expected),
            "{context}"
        );
    }
}

/// `cntu(S, "")` is `Unspecified` (an empty needle), and its equation's evaluation needs the
/// same application again, so the attempt is undone and the application stays unevaluated. The
/// attempt evaluated `gu1`'s `requires` through `td(0)`: the contradiction it observed is
/// recorded although the attempt and its diagnostics are discarded. The successor's
/// normalization observes it as `un`'s work; the stuck leaf's own normalization, which is no
/// rule's work, evaluates the application again and observes it once more.
#[test]
fn a_contradiction_inside_an_undone_attempt_is_recorded() {
    assert_recorded(
        "un(\"a\")",
        &[record("td", "tdeq", Some("un")), record("td", "tdeq", None)],
    );
}

/// A symbolic run observes no contradiction: `td(X)` is trusted as total, and no record is
/// made (`r(X)` is decided by neither strategy without a solver).
#[test]
fn a_symbolic_run_observes_no_contradiction() {
    let (kore, ground) = compile_program(CONTRADICTIONS, "r(0)");
    let printed = k_rust::kore::printer::Printer::compact().print_pattern(&ground);
    let symbolic = printed.replacen("\\dv{SortInt{}}(\"0\")", "VarX:SortInt{}", 1);
    assert_ne!(symbolic, printed);
    let initial = k_rust::kore::parser::parse_pattern(&symbolic).unwrap();
    for (name, _, _, result) in each_run(&kore, &initial) {
        assert!(
            leaves(&result).iter().all(|leaf| records(leaf).is_empty()),
            "{name}: {result:#}"
        );
        assert!(
            result.get("contradictedClaims").is_none(),
            "{name}: {result:#}"
        );
    }
}

/// `a_refutation_that_observed_a_contradiction_is_not_reused_without_its_record`'s
/// definition.
const LOOP: &str = r#"
module MAIN
  imports INT
  syntax Pgm ::= loop(Int) | done(Int)
  syntax Int ::= td(Int) [function, total]
  configuration <k> $PGM:Pgm </k>
  rule [tdeq]: td(I) => 10 /Int (I +Int 0)
  rule [hit]: loop(N) => done(N) requires td(0) >Int N
  rule loop(N) => loop(N -Int 1) requires N >Int 0 [priority(60)]
  rule loop(0) => done(0) [priority(60)]
endmodule
"#;

/// The sequential step keeps one refutation memo for the run, shared by its initial patterns.
/// `hit`'s `requires` is refuted through `td(0)` on the first pattern; a memo that stored that
/// refutation would answer the second pattern's attempt without evaluating `td(0)`, and that
/// path's leaf would carry no record. A refutation that noted a record is not stored, so every
/// leaf carries it.
#[test]
fn a_refutation_that_observed_a_contradiction_is_not_reused_without_its_record() {
    use k_rust_backend::{
        evaluation::EvaluationMode,
        rewrite::{ExecutionMode, ExecutionOptions, execute_disjunction_with_solver_and_observer},
        search::ResultModality,
        smt::NoSolver,
    };
    let (kore, initial) = compile_program(LOOP, "loop(2)");
    let mut backend = observed::backend(&kore);
    let definition = backend.select_definition(None).unwrap();
    let pattern = definition
        .admit_unverified(&initial, &[])
        .internalize_pattern()
        .unwrap();
    let result = execute_disjunction_with_solver_and_observer(
        &definition,
        vec![pattern.clone(), pattern],
        ExecutionOptions {
            mode: ExecutionMode::Any,
            result_modality: ResultModality::PathSet,
            evaluation: EvaluationMode::Execution,
            ..ExecutionOptions::default()
        },
        &NoSolver,
        |_| {},
    );
    assert_eq!(result.leaves.len(), 2, "{result:#?}");
    let counts = result
        .leaves
        .iter()
        .map(|leaf| {
            format!("{:?}", leaf.diagnostics)
                .matches("ContradictedClaim {")
                .count()
        })
        .collect::<Vec<_>>();
    assert_eq!(counts, [1, 1], "{result:#?}");
}

/// What undone work never rolls back besides contradictions (docs/compatibility.md, "Backend
/// scope"): an allowance refusal of a `Bytes` hook and an unsupported hook that a run met are on
/// the result's run-level lists (`allowanceRefusals`, `unsupportedHooks`) even when the work that
/// met them was passed over or undone, so the diagnostic was dropped although the refusal
/// steered the run.
mod refusals {
    use super::observed::{STRATEGIES, compile, execute, leaf_with, leaves};
    use serde_json::Value;

    /// `f(N)`'s first equation pads to `N` bytes; at `2^40` the allowance refuses that on every
    /// host, the condition stays undecided, and the second equation gives `2`. `h(N)`'s first
    /// equation reads `countAllOccurrences("a", "")`, which the definition does not determine,
    /// and is passed over alike. `cnt(S, "")`'s equation needs the same application again, so its
    /// attempt, which met the refusal, is undone.
    pub(super) const REFUSALS: &str = r#"
module MAIN
  imports INT
  imports BYTES
  imports STRING
  imports BOOL
  syntax Pgm ::= run(Int) | runh(Int) | runc(String) | val(Int)
  syntax Int ::= f(Int) [function, total]
               | h(Int) [function, total]
               | cnt(String, String) [function, total, hook(STRING.countAllOccurrences)]
               | g(Int, Int) [function, total]
  configuration <k> $PGM:Pgm </k>
  rule f(N) => 1 requires lengthBytes(padRightBytes(.Bytes, N, 0)) >Int 0
  rule f(N) => 2 requires N >Int 0
  rule h(N) => 1 requires countAllOccurrences("a", "") >Int N
  rule h(N) => 2 requires N >Int 0
  rule cnt(S, "") => g(lengthBytes(padRightBytes(.Bytes, String2Int(S), 0)), cnt(S, ""))
  rule g(I, _) => 7 requires I >Int 0
  rule g(_, X) => X [owise]
  rule run(N) => val(f(N))
  rule runh(N) => val(h(N))
  rule runc(S) => val(cnt(S, ""))
endmodule
"#;

    /// `(hook, whether the reason names the allowance cap)` of each entry of `field`.
    fn entries(result: &Value, field: &str) -> Vec<(String, bool)> {
        result[field]
            .as_array()
            .into_iter()
            .flatten()
            .map(|entry| {
                (
                    entry["hook"].as_str().unwrap().to_owned(),
                    entry["reason"]
                        .as_str()
                        .unwrap()
                        .contains("longer than its cap"),
                )
            })
            .collect()
    }

    fn unsupported_diagnostics(leaf: &Value) -> Vec<String> {
        leaf["diagnostics"]
            .as_array()
            .into_iter()
            .flatten()
            .filter(|diagnostic| diagnostic["kind"] == "unsupported-hook-unevaluated")
            .map(|diagnostic| diagnostic["hook"].as_str().unwrap().to_owned())
            .collect()
    }

    fn runs(program: &str) -> Vec<(String, Value)> {
        let (kore, initial) = compile(REFUSALS, program);
        STRATEGIES
            .into_iter()
            .flat_map(|strategy| {
                super::observed::MODALITIES.map(|modality| {
                    (
                        format!("{program} {strategy:?} {modality:?}"),
                        execute(&kore, &initial, modality, strategy),
                    )
                })
            })
            .collect()
    }

    /// The refused padding left `f`'s first equation undecided and was passed over: the leaf has
    /// no diagnostic, and the result lists the refusal. Under an allowance that admits the
    /// padding the value would be `1`, so a result is reused across allowances only when its
    /// list is empty. `f(1)` needs no refusal and lists none.
    #[test]
    fn a_refusal_in_a_passed_over_equation_is_on_the_run_list() {
        for (name, result) in runs("run(1099511627776)") {
            let leaf = leaf_with(&result, "\"2\"");
            assert!(
                unsupported_diagnostics(leaf).is_empty(),
                "{name}: {result:#}"
            );
            assert_eq!(
                entries(&result, "allowanceRefusals"),
                [("BYTES.padRight".to_owned(), true)],
                "{name}: {result:#}"
            );
            assert!(
                result.get("unsupportedHooks").is_none(),
                "{name}: {result:#}"
            );
        }
        for (name, result) in runs("run(1)") {
            assert_eq!(leaves(&result).len(), 1, "{name}: {result:#}");
            assert!(leaf_with(&result, "\"1\"").is_object());
            assert!(
                result.get("allowanceRefusals").is_none(),
                "{name}: {result:#}"
            );
            assert!(
                result.get("unsupportedHooks").is_none(),
                "{name}: {result:#}"
            );
        }
    }

    /// An unsupported hook in a passed-over equation is on the run's list too.
    #[test]
    fn an_unsupported_hook_in_a_passed_over_equation_is_on_the_run_list() {
        for (name, result) in runs("runh(1)") {
            let leaf = leaf_with(&result, "\"2\"");
            assert!(
                unsupported_diagnostics(leaf).is_empty(),
                "{name}: {result:#}"
            );
            assert_eq!(
                entries(&result, "unsupportedHooks"),
                [("STRING.countAllOccurrences".to_owned(), false)],
                "{name}: {result:#}"
            );
            assert!(
                result.get("allowanceRefusals").is_none(),
                "{name}: {result:#}"
            );
        }
    }

    /// The searches list refusals and unsupported hooks as executions do, in each of the four
    /// responses, with the work that met them passed over alike.
    #[test]
    fn every_search_lists_the_refusals_and_the_unsupported_hooks() {
        use k_rust::{
            backend::{SearchPatternRequest, SearchRequest, SearchTypeArg},
            kore::parser::parse_pattern,
        };
        let target = parse_pattern("VarResult:SortGeneratedTopCell{}").unwrap();
        for (program, field, hook) in [
            ("run(1099511627776)", "allowanceRefusals", "BYTES.padRight"),
            ("runh(1)", "unsupportedHooks", "STRING.countAllOccurrences"),
        ] {
            let (kore, initial) = compile(REFUSALS, program);
            let search = SearchRequest {
                search_type: SearchTypeArg::All,
                ..SearchRequest::new(initial.clone())
            };
            let pattern = SearchPatternRequest {
                search_type: SearchTypeArg::All,
                ..SearchPatternRequest::new(initial, target.clone())
            };
            let mut backend = super::observed::backend(&kore);
            for response in [
                serde_json::to_value(backend.search(search.clone()).unwrap()).unwrap(),
                serde_json::to_value(backend.search_paths(search.clone()).unwrap()).unwrap(),
                serde_json::to_value(backend.search_pattern(pattern.clone()).unwrap()).unwrap(),
                serde_json::to_value(backend.search_pattern_paths(pattern).unwrap()).unwrap(),
            ] {
                let listed = entries(&response, field)
                    .into_iter()
                    .map(|(hook, _)| hook)
                    .collect::<Vec<_>>();
                assert_eq!(listed, [hook], "{program}: {response:#}");
                assert_eq!(
                    response[field][0]["observedIn"], "run",
                    "{program}: {response:#}"
                );
            }
        }
    }

    /// The refusal met inside `cnt`'s undone attempt is on the run's list; the leaf keeps only
    /// `cnt`'s own diagnostic, which is on the list too.
    #[test]
    fn a_refusal_inside_an_undone_attempt_is_on_the_run_list() {
        for (name, result) in runs("runc(\"1099511627776\")") {
            let leaf = leaf_with(&result, "Lblcnt");
            assert_eq!(
                unsupported_diagnostics(leaf),
                ["STRING.countAllOccurrences"],
                "{name}: {result:#}"
            );
            assert_eq!(
                entries(&result, "allowanceRefusals"),
                [("BYTES.padRight".to_owned(), true)],
                "{name}: {result:#}"
            );
            assert_eq!(
                entries(&result, "unsupportedHooks"),
                [("STRING.countAllOccurrences".to_owned(), false)],
                "{name}: {result:#}"
            );
        }
    }
}

/// Two `anywhere` equations of each equation head, `g` and `h` (a symbol a gate site can be
/// asked about), overlap; the load's critical-pair check classifies each overlap and simplifies
/// the first equation's condition: `td(0)` is bottom, a contradicted claim, and the padding is
/// refused by the memory allowance. `fe(0)` meets `td(0)` again when a run evaluates it.
const LOAD: &str = r#"
module MAIN
  imports INT
  imports BYTES
  syntax Pgm ::= go(Int) | val(Int)
  syntax Int ::= td(Int) [function, total]
               | fe(Int) [function, total]
  syntax Foo ::= g(Int) | h(Int) | "a" | "b"
  configuration <k> $PGM:Pgm </k>
  rule [tdeq]: td(I) => 10 /Int (I +Int 0)
  rule [fe1]:  fe(I) => 1 requires td(I) >Int 0
  rule [fe2]:  fe(_) => 2 [owise]
  rule [ga]:   g(_X) => a requires td(0) ==Int 1 [anywhere]
  rule [gb]:   g(_X) => b [anywhere]
  rule [ha]:   h(_X) => a requires lengthBytes(padRightBytes(.Bytes, 1099511627776, 0)) ==Int 1 [anywhere]
  rule [hb]:   h(_X) => b [anywhere]
  rule [go]:   go(I) => val(I)
endmodule
"#;

/// The load's verdicts decide every later use of the definition, so every run of it lists what
/// the load observed, the claim with no rule, beside its own records. They are facts about the
/// definition, the same for every leaf, so they are on the result's lists and on no leaf.
#[test]
fn what_the_load_observed_is_on_every_run_s_lists() {
    let (kore, initial) = compile_program(LOAD, "go(1)");
    for (name, _, _, result) in each_run(&kore, &initial) {
        let context = format!("{name}: {result:#}");
        assert!(
            leaves(&result).iter().all(|leaf| records(leaf).is_empty()),
            "{context}"
        );
        assert_eq!(
            run_records(&result),
            [record("td", "tdeq", None)],
            "{context}"
        );
        let refusals = result["allowanceRefusals"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|entry| entry["hook"].as_str().unwrap().to_owned())
            .collect::<Vec<_>>();
        assert_eq!(refusals, ["BYTES.padRight"], "{context}");
    }
}

/// `observedIn` of each entry of `field`, in order.
fn observed_in(result: &Value, field: &str) -> Vec<String> {
    result[field]
        .as_array()
        .into_iter()
        .flatten()
        .map(|entry| entry["observedIn"].as_str().unwrap_or("?").to_owned())
        .collect()
}

/// Every record says whether the definition's load or this run observed it (`observedIn`):
/// the load's records are `load`, and a leaf's records and the run's own are `run`. The load and
/// the run can observe one contradiction alike: `val(fe(0))`'s initial normalization, which is
/// no rule's work, meets the `td(0)` the load met, and the list holds both, so a client tells
/// what this run's inputs reached from what the definition carries.
#[test]
fn each_record_says_whether_the_load_or_the_run_observed_it() {
    let (kore, initial) = compile_program(LOAD, "go(1)");
    for (name, _, _, result) in each_run(&kore, &initial) {
        let context = format!("{name}: {result:#}");
        assert_eq!(
            observed_in(&result, "contradictedClaims"),
            ["load"],
            "{context}"
        );
        assert_eq!(
            observed_in(&result, "allowanceRefusals"),
            ["load"],
            "{context}"
        );
    }
    let (kore, initial) = compile_program(LOAD, "val(fe(0))");
    for (name, _, _, result) in each_run(&kore, &initial) {
        let context = format!("{name}: {result:#}");
        assert_eq!(
            run_records(&result),
            [record("td", "tdeq", None), record("td", "tdeq", None)],
            "{context}"
        );
        assert_eq!(
            observed_in(&result, "contradictedClaims"),
            ["load", "run"],
            "{context}"
        );
    }
    let (kore, initial) = compile_program(CONTRADICTIONS, "r(0)");
    for (name, _, _, result) in each_run(&kore, &initial) {
        let context = format!("{name}: {result:#}");
        assert_eq!(
            observed_in(&result, "contradictedClaims"),
            ["run"],
            "{context}"
        );
        for leaf in leaves(&result) {
            let tags = leaf["diagnostics"]
                .as_array()
                .unwrap()
                .iter()
                .filter(|diagnostic| diagnostic["kind"] == "contradicted-claim")
                .map(|diagnostic| diagnostic["observedIn"].clone())
                .collect::<Vec<_>>();
            assert_eq!(tags, [Value::from("run")], "{context}");
        }
    }
}

/// Every leaf of a run that sets `stopAtBranch`, `maxWork` or `maxBreadth`, and under
/// `state-set` a leaf whose halt another halt may stand for (`depth-bound` here), carries every
/// record the run observed, as it carries every mark: `sib(0)`'s `done` leaf, which rests on no
/// contradiction in the plain run, carries `sibtd`'s record in each. Under `path-set`,
/// `maxDepth` adds nothing. This pins the shared rule of `crate::path_facts` for records.
#[test]
fn a_bound_or_a_stop_rule_puts_every_record_of_the_run_on_every_leaf() {
    use k_rust::backend::{ExecuteRequest, ExecutionStrategy, ResultModalityOutput};
    let (kore, initial) = compile_program(CONTRADICTIONS, "sib(0)");
    let expected = BTreeSet::from([record("td", "tdeq", Some("sibtd"))]);
    let run = |modality, adjust: &dyn Fn(&mut ExecuteRequest)| {
        let mut request = ExecuteRequest {
            result_modality: modality,
            strategy: ExecutionStrategy::All,
            ..ExecuteRequest::new(initial.clone())
        };
        adjust(&mut request);
        let result = observed::backend(&kore).execute(request).unwrap();
        serde_json::to_value(&result).unwrap()
    };
    for modality in observed::MODALITIES {
        let plain = run(modality, &|_| {});
        assert!(
            records(leaf_with(&plain, "Lbldone")).is_empty(),
            "{plain:#}"
        );
        type Adjustment<'a> = (&'a str, &'a dyn Fn(&mut ExecuteRequest));
        let adjustments: [Adjustment; 3] = [
            ("stopAtBranch", &|request| request.stop_at_branch = true),
            ("maxWork 100", &|request| request.max_work = Some(100)),
            ("maxBreadth 10", &|request| request.max_breadth = Some(10)),
        ];
        for (name, adjust) in adjustments {
            let result = run(modality, adjust);
            let context = format!("{modality:?} {name}: {result:#}");
            assert_eq!(leaves(&result).len(), 1, "{context}");
            assert_eq!(records(&leaves(&result)[0]), expected, "{context}");
        }
        let result = run(modality, &|request| request.max_depth = Some(1));
        let context = format!("{modality:?} maxDepth 1: {result:#}");
        let done = leaf_with(&result, "Lbldone");
        assert_eq!(done["reason"], "depth-bound", "{context}");
        match modality {
            ResultModalityOutput::StateSet => assert_eq!(records(done), expected, "{context}"),
            _ => assert!(records(done).is_empty(), "{context}"),
        }
    }
}

/// The searches report the run-level records as executions do (`contradictedClaims`,
/// `allowanceRefusals`, `unsupportedHooks`, absent when empty), each of the four responses: what
/// the load observed, and what the search observed, including work on no reported state (under
/// `sib(0)` the `sibtd` successor vanishes, and every state is clean).
#[test]
fn every_search_response_lists_the_records() {
    use k_rust::{
        backend::{SearchPatternRequest, SearchRequest, SearchTypeArg},
        kore::parser::parse_pattern,
    };
    let target = parse_pattern("VarResult:SortGeneratedTopCell{}").unwrap();
    let responses = |source: &str, program: &str| {
        let (kore, initial) = compile_program(source, program);
        let search = SearchRequest {
            search_type: SearchTypeArg::All,
            ..SearchRequest::new(initial.clone())
        };
        let pattern = SearchPatternRequest {
            search_type: SearchTypeArg::All,
            ..SearchPatternRequest::new(initial, target.clone())
        };
        let mut backend = observed::backend(&kore);
        [
            serde_json::to_value(backend.search(search.clone()).unwrap()).unwrap(),
            serde_json::to_value(backend.search_paths(search).unwrap()).unwrap(),
            serde_json::to_value(backend.search_pattern(pattern.clone()).unwrap()).unwrap(),
            serde_json::to_value(backend.search_pattern_paths(pattern).unwrap()).unwrap(),
        ]
    };
    for response in responses(CONTRADICTIONS, "sib(0)") {
        assert_eq!(
            run_records(&response),
            [record("td", "tdeq", Some("sibtd"))],
            "{response:#}"
        );
        assert_eq!(
            observed_in(&response, "contradictedClaims"),
            ["run"],
            "{response:#}"
        );
        assert!(response.get("allowanceRefusals").is_none(), "{response:#}");
        assert!(response.get("unsupportedHooks").is_none(), "{response:#}");
    }
    for response in responses(LOAD, "go(1)") {
        assert_eq!(
            run_records(&response),
            [record("td", "tdeq", None)],
            "{response:#}"
        );
        assert_eq!(
            observed_in(&response, "contradictedClaims"),
            ["load"],
            "{response:#}"
        );
        assert_eq!(
            response["allowanceRefusals"][0]["hook"], "BYTES.padRight",
            "{response:#}"
        );
    }
    for response in responses(CONTRADICTIONS, "r(1)") {
        assert!(response.get("contradictedClaims").is_none(), "{response:#}");
    }
}

/// A search successor's normalization is the work of the rule that produced it, as in an
/// execution: `e(0)`'s successor `val(fe(0))` meets `td(0)` when the search normalizes it, and
/// the record names `e`, in every search and in the execution alike.
#[test]
fn a_search_successor_s_normalization_names_its_rule() {
    use k_rust::backend::{SearchRequest, SearchTypeArg};
    let (kore, initial) = compile_program(CONTRADICTIONS, "e(0)");
    let expected = BTreeSet::from([record("td", "tdeq", Some("e"))]);
    for search_type in [SearchTypeArg::Final, SearchTypeArg::All] {
        let search = SearchRequest {
            search_type,
            ..SearchRequest::new(initial.clone())
        };
        let mut backend = observed::backend(&kore);
        let graph = serde_json::to_value(backend.search(search.clone()).unwrap()).unwrap();
        let paths = serde_json::to_value(backend.search_paths(search).unwrap()).unwrap();
        for (states, response) in [("states", &graph), ("witnesses", &paths)] {
            let val = response[states]
                .as_array()
                .unwrap()
                .iter()
                .filter(|state| observed::printed(state).contains("Lblval"))
                .collect::<Vec<_>>();
            assert_eq!(val.len(), 1, "{search_type:?}: {response:#}");
            assert_eq!(records(val[0]), expected, "{search_type:?}: {response:#}");
        }
    }
}

/// `the_warning_says_what_a_record_shows`'s definition: a non-ground record.
const NON_GROUND: &str = r#"
module MAIN
  imports INT
  syntax Pgm ::= "done" | rz(Int)
  syntax Int ::= tz(Int) [function, total]
  configuration <k> $PGM:Pgm </k>
  rule [tzeq]: tz(_) => 10 /Int 0
  rule [rz]:   rz(I) => done requires tz(I) >Int 0
endmodule
"#;

/// `krun`'s warning says what a record shows. A ground record is a refutation of the claim at
/// that input, so the definition is inconsistent there; a non-ground one (`rz(X)`, through
/// `tz(_) => 10 /Int 0`) holds at each instance of a state that may have none, so it is worded as
/// contradicted only. A record of the load says so.
#[test]
fn the_warning_says_what_a_record_shows() {
    use k_rust::backend::execution::contradicted_claim_message;
    use k_rust_backend::{rewrite::execute_with_solver, smt::NoSolver};
    let messages = |source: &str, program: &str, symbolic: bool| {
        let (kore, ground) = compile_program(source, program);
        let initial = if symbolic {
            let printed = k_rust::kore::printer::Printer::compact().print_pattern(&ground);
            let symbolic = printed.replacen("\\dv{SortInt{}}(\"0\")", "VarX:SortInt{}", 1);
            assert_ne!(symbolic, printed);
            k_rust::kore::parser::parse_pattern(&symbolic).unwrap()
        } else {
            ground
        };
        let mut backend = observed::backend(&kore);
        let definition = backend.select_definition(None).unwrap();
        let pattern = definition
            .admit_unverified(&initial, &[])
            .internalize_pattern()
            .unwrap();
        let result = execute_with_solver(&definition, pattern, Default::default(), &NoSolver);
        result
            .contradicted_claims
            .iter()
            .map(contradicted_claim_message)
            .collect::<Vec<_>>()
    };
    let [ground] = <[String; 1]>::try_from(messages(CONTRADICTIONS, "r(0)", false)).unwrap();
    assert!(
        ground.contains("is contradicted on this input")
            && ground.contains("so the definition is inconsistent here")
            && ground.ends_with("(observed by rule MAIN.r)"),
        "{ground}"
    );
    let [symbolic] = <[String; 1]>::try_from(messages(NON_GROUND, "rz(0)", true)).unwrap();
    assert!(
        symbolic.contains("is contradicted")
            && !symbolic.contains("on this input")
            && !symbolic.contains("inconsistent")
            && symbolic.contains("not ground")
            && symbolic.ends_with("(observed by rule MAIN.rz)"),
        "{symbolic}"
    );
    let [load] = <[String; 1]>::try_from(messages(LOAD, "go(1)", false)).unwrap();
    assert!(
        load.ends_with("(observed when the definition was loaded)"),
        "{load}"
    );
}

/// Contradicted `preserves-definedness` attributes (docs/compatibility.md, "A contradicted
/// `preserves-definedness` attribute is named, not repaired"): a rule declared so claims that its
/// result term is defined wherever its left-hand side and `requires` hold. The step applies, and
/// when the normalization of the result term it built finds a subterm undefined, the claim is
/// refuted at that instance: a `contradicted-claim` record with `claim: preserves-definedness`
/// naming the rule, its result term and the undefined subterm, on every leaf whose path rests on
/// it and on the result's list. An undefined `ensures` or a refuted carried condition is not
/// covered by the claim, and a rule that is not declared so (discharged or not) claims nothing.
mod preservation {
    use std::collections::BTreeSet;

    use k_rust::backend::{ExecutionStrategy, ResultModalityOutput};
    use serde_json::Value;

    use super::observed::{
        Record, backend, compile, each_run, leaf_with, leaves, record, records, run_records,
    };

    pub(super) const PRESERVATION: &str = r#"
module MAIN
  imports INT
  syntax Pgm ::= "done" | val(Int) | pd(Int) | npd(Int) | pdt(Int) | pdp(Int) | pdens(Int)
               | pdsib(Int) | two(Int) | ja(Int) | jb(Int) | join(Int) | tdiv(Int)
  syntax Int ::= td(Int) [function, total]
               | tp(Int) [function]
  configuration <k> $PGM:Pgm </k>
  rule [tdeq]:   td(I) => 10 /Int (I +Int 0)
  rule [tpeq]:   tp(I) => 10 /Int (I +Int 0)
  rule [pd]:     pd(X) => val(X /Int 0) [preserves-definedness]
  rule [npd]:    npd(X) => val(X /Int 0)
  rule [pdt]:    pdt(X) => val(td(X)) [preserves-definedness]
  rule [pdp]:    pdp(X) => val(tp(X)) [preserves-definedness]
  rule [pdens]:  pdens(X) => done ensures X >Int 0 [preserves-definedness]
  rule [pdsiba]: pdsib(X) => val(X /Int 0) [preserves-definedness]
  rule [pdsibb]: pdsib(_) => done
  rule [twoa]:   two(X) => ja(X)
  rule [twob]:   two(X) => jb(X)
  rule [ja]:     ja(X) => join(X)
  rule [jb]:     jb(X) => join(X)
  rule [join]:   join(X) => val(X /Int 0) [preserves-definedness]
  rule [tdiv]:   tdiv(I) => val(td(I))
endmodule
"#;

    /// The definition with no claim at all: no `total` and no `preserves-definedness`.
    fn claim_free(source: &str) -> String {
        super::observed::claim_free(source).replace(" [preserves-definedness]", "")
    }

    /// The record of `rule`'s `preserves-definedness` claim, observed by the rule's own step, at
    /// a ground instance.
    pub(super) fn preservation(rule: &str) -> Record {
        (
            "preserves-definedness".to_owned(),
            "?".to_owned(),
            format!("MAIN.{rule}"),
            Some(format!("MAIN.{rule}")),
            true,
        )
    }

    /// The printed `undefined` subterm of each preserves-definedness record of `result`'s list.
    fn undefined_subterms(result: &Value) -> Vec<String> {
        result["contradictedClaims"]
            .as_array()
            .into_iter()
            .flatten()
            .filter(|entry| entry["claim"] == "preserves-definedness")
            .map(|entry| {
                k_rust::kore::printer::Printer::compact()
                    .print_pattern(&k_rust::kore::codec::from_value(&entry["undefined"]).unwrap())
            })
            .collect()
    }

    /// Every leaf of `program` and the result's list carry exactly `expected`, in every
    /// combination, and the claim-free definition gives the same leaves' reasons with no record.
    fn assert_recorded(program: &str, expected: &[Record]) {
        let (kore, initial) = compile(PRESERVATION, program);
        let (free, free_initial) = compile(&claim_free(PRESERVATION), program);
        for (name, strategy, modality, result) in each_run(&kore, &initial) {
            let context = format!("{program} under {name}: {result:#}");
            assert!(!leaves(&result).is_empty(), "{context}");
            for leaf in leaves(&result) {
                assert_eq!(
                    records(leaf),
                    expected.iter().cloned().collect::<BTreeSet<_>>(),
                    "{context}"
                );
            }
            assert_eq!(run_records(&result), expected, "{context}");
            let free = super::observed::execute(&free, &free_initial, modality, strategy);
            let reasons = |result: &Value| {
                leaves(result)
                    .iter()
                    .map(|leaf| leaf["reason"].clone())
                    .collect::<Vec<_>>()
            };
            assert_eq!(reasons(&free), reasons(&result), "claim-free {context}");
            assert!(
                free.get("contradictedClaims").is_none(),
                "claim-free {free:#}"
            );
        }
    }

    /// `pd(0)` steps to `val(0 /Int 0)`: the attribute is trusted, so the step applies, and the
    /// result term's normalization finds `0 /Int 0` undefined. The `trivial` leaf and the list
    /// name the rule, as they would without the attribute only by the halt.
    #[test]
    fn a_result_found_undefined_refutes_the_rule_s_preserves_definedness() {
        assert_recorded("pd(0)", &[preservation("pd")]);
        let (kore, initial) = compile(PRESERVATION, "pd(0)");
        for (name, _, _, result) in each_run(&kore, &initial) {
            assert_eq!(
                undefined_subterms(&result),
                ["Lbl'UndsSlsh'Int'Unds'{}(\\dv{SortInt{}}(\"0\"), \\dv{SortInt{}}(\"0\"))"],
                "{name}: {result:#}"
            );
            for leaf in leaves(&result) {
                assert_eq!(leaf["reason"], "trivial", "{name}: {result:#}");
            }
        }
        // Through a partial callee the result is undefined alike.
        assert_recorded("pdp(0)", &[preservation("pdp")]);
    }

    /// No claim, no record: `npd` is not declared, so its step carries the obligation and finds
    /// the result undefined itself; `pdens`'s undefined `ensures` is no part of its result term;
    /// `tdiv`'s result is undefined only through a contradicted `total` callee, whose record is
    /// the one named.
    #[test]
    fn a_rule_that_claims_nothing_about_the_undefinedness_is_not_named() {
        assert_recorded("npd(0)", &[]);
        assert_recorded("pdens(0)", &[]);
        assert_recorded("tdiv(0)", &[record("td", "tdeq", Some("tdiv"))]);
    }

    /// `pdt(0)` steps to `val(td(0))`, and `td(0)` is bottom through `td`'s own equation, which
    /// contradicts `td`'s `total` claim; the result is undefined, which contradicts `pdt`'s claim
    /// too. Both are named, the callee's first.
    #[test]
    fn a_step_through_a_contradicted_total_callee_names_both_claims() {
        assert_recorded(
            "pdt(0)",
            &[record("td", "tdeq", Some("pdt")), preservation("pdt")],
        );
    }

    /// `pdsiba`'s result is undefined and `pdsibb` covers every instance. Under strategy all the
    /// candidate vanishes after the step: the `done` leaf is clean and the result lists the
    /// record. Under strategy any the sequential step decides the candidate undefined before it
    /// takes `pdsibb`, so the `done` leaf rests on it.
    #[test]
    fn a_candidate_a_defined_sibling_covers_is_on_the_list_and_on_the_leaves_that_rest_on_it() {
        let (kore, initial) = compile(PRESERVATION, "pdsib(0)");
        let expected = preservation("pdsiba");
        for (name, strategy, _, result) in each_run(&kore, &initial) {
            let context = format!("{name}: {result:#}");
            assert_eq!(leaves(&result).len(), 1, "{context}");
            let on_leaf = match strategy {
                ExecutionStrategy::All => BTreeSet::new(),
                _ => BTreeSet::from([expected.clone()]),
            };
            assert_eq!(records(leaf_with(&result, "Lbldone")), on_leaf, "{context}");
            assert_eq!(
                run_records(&result),
                std::slice::from_ref(&expected),
                "{context}"
            );
        }
    }

    /// `two(0)` reaches `join(0)` on two paths, and `join`'s result is undefined: the state-set
    /// result has one `trivial` leaf, the path-set result one per path, and each carries the
    /// record (strategy any takes `twoa` alone).
    #[test]
    fn converging_paths_each_rest_on_the_contradiction() {
        let (kore, initial) = compile(PRESERVATION, "two(0)");
        let expected = BTreeSet::from([preservation("join")]);
        for (name, strategy, modality, result) in each_run(&kore, &initial) {
            let context = format!("{name}: {result:#}");
            let count = match (strategy, modality) {
                (ExecutionStrategy::All, ResultModalityOutput::PathSet) => 2,
                _ => 1,
            };
            assert_eq!(leaves(&result).len(), count, "{context}");
            for leaf in leaves(&result) {
                assert_eq!(leaf["reason"], "trivial", "{context}");
                assert_eq!(records(leaf), expected, "{context}");
            }
            assert_eq!(run_records(&result), [preservation("join")], "{context}");
        }
    }

    /// A search names the contradiction as an execution does: every search response lists it.
    #[test]
    fn every_search_lists_a_contradicted_preserves_definedness() {
        use k_rust::backend::{SearchRequest, SearchTypeArg};
        let (kore, initial) = compile(PRESERVATION, "pd(0)");
        for search_type in [SearchTypeArg::Final, SearchTypeArg::All] {
            let search = SearchRequest {
                search_type,
                ..SearchRequest::new(initial.clone())
            };
            let mut backend = backend(&kore);
            for response in [
                serde_json::to_value(backend.search(search.clone()).unwrap()).unwrap(),
                serde_json::to_value(backend.search_paths(search).unwrap()).unwrap(),
            ] {
                assert_eq!(
                    run_records(&response),
                    [preservation("pd")],
                    "{search_type:?}: {response:#}"
                );
            }
        }
    }

    /// `krun`'s warning names the rule and its undefined result.
    #[test]
    fn the_warning_names_the_rule_and_the_undefined_result() {
        use k_rust::backend::execution::contradicted_claim_message;
        use k_rust_backend::{rewrite::execute_with_solver, smt::NoSolver};
        let (kore, initial) = compile(PRESERVATION, "pd(0)");
        let mut backend = backend(&kore);
        let definition = backend.select_definition(None).unwrap();
        let pattern = definition
            .admit_unverified(&initial, &[])
            .internalize_pattern()
            .unwrap();
        let result = execute_with_solver(&definition, pattern, Default::default(), &NoSolver);
        let messages = result
            .contradicted_claims
            .iter()
            .map(contradicted_claim_message)
            .collect::<Vec<_>>();
        let [message] = <[String; 1]>::try_from(messages).unwrap();
        assert!(
            message
                .starts_with("the `preserves-definedness` attribute of rule MAIN.pd at claims.k:")
                && message.contains("is contradicted on this input: its result ")
                && message.contains("is undefined at Lbl'UndsSlsh'Int'Unds'{}")
                && message.contains("so the definition is inconsistent here")
                && message.ends_with("(observed by rule MAIN.pd)"),
            "{message}"
        );
    }

    /// The shapes of the fix round: a disjunctive right-hand side, a result that reaches
    /// `\bottom` through an equation whose right-hand side is `#Bottom` (`bot` is partial, `tb`
    /// and `tb2` are declared `total`), and two rules whose `requires` no instance satisfies.
    pub(super) const ROUTES: &str = r#"
module MAIN
  imports INT
  imports BOOL
  imports STRING
  syntax Pgm ::= "done" | val(Int) | pdo(Int) | pdoo(Int) | bt(Int) | bts(Int)
               | tbt(Int) | tbn(Int) | pa(Int) | pb(Int)
  syntax Int ::= bot(Int) [function]
               | tb(Int) [function, total]
               | tb2(Int) [function, total]
  configuration <k> $PGM:Pgm </k>
  rule [pdo]:    pdo(X) => (val(X /Int 0) #Or done) [preserves-definedness]
  rule [pdoo]:   pdoo(X) => (val(X /Int 0) #Or val((X /Int 0) +Int 1)) [preserves-definedness]
  rule [boteq]:  bot(I) => #Bottom requires I ==Int 0
  rule [boteq2]: bot(I) => I requires I =/=Int 0
  rule [btr]:    bt(X) => val(bot(X)) [preserves-definedness]
  rule [btsa]:   bts(X) => val(bot(X)) [preserves-definedness]
  rule [btsb]:   bts(_) => done
  rule [tbeq]:   tb(I) => #Bottom requires I ==Int 0
  rule [tbeq2]:  tb(I) => I requires I =/=Int 0
  rule [tbt]:    tbt(X) => val(tb(X))
  rule [tb2eq]:  tb2(I) => bot(I) +Int 1
  rule [tbn]:    tbn(X) => val(tb2(X))
  rule [pa]:     pa(X) => val(1 /Int 0) requires 2 ^Int X ==Int 3 [preserves-definedness]
  rule [pb]:     pb(X) => val(1 /Int 0) requires lengthString(Int2String(X)) ==Int 0 [preserves-definedness]
endmodule
"#;

    /// Each run of `program` over [`ROUTES`] and over its claim-free variant, by name.
    fn route_runs(program: &str) -> Vec<(String, ExecutionStrategy, Value, Value)> {
        let (kore, initial) = compile(ROUTES, program);
        let (free, free_initial) = compile(&claim_free(ROUTES), program);
        each_run(&kore, &initial)
            .into_iter()
            .map(|(name, strategy, modality, result)| {
                let free = super::observed::execute(&free, &free_initial, modality, strategy);
                (format!("{program} under {name}"), strategy, result, free)
            })
            .collect()
    }

    /// The leaves' reasons, in order.
    fn reasons(result: &Value) -> Vec<Value> {
        leaves(result)
            .iter()
            .map(|leaf| leaf["reason"].clone())
            .collect()
    }

    /// The claim-free run records nothing.
    fn assert_claim_free_records_nothing(name: &str, free: &Value) {
        assert!(
            leaves(free).iter().all(|leaf| records(leaf).is_empty()),
            "claim-free {name}: {free:#}"
        );
        assert!(
            free.get("contradictedClaims").is_none(),
            "claim-free {name}: {free:#}"
        );
    }

    /// The printed `undefined` term of every record of `result`'s list.
    fn undefined_terms(result: &Value) -> Vec<String> {
        result["contradictedClaims"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|entry| {
                k_rust::kore::printer::Printer::compact()
                    .print_pattern(&k_rust::kore::codec::from_value(&entry["undefined"]).unwrap())
            })
            .collect()
    }

    /// The definedness of a disjunction is the disjunction of its alternatives' definedness:
    /// `pdo(0)`'s result `val(0 /Int 0) #Or done` is defined, since `done` is, so the claim holds
    /// and nothing is named, as without the attribute. `pdoo(0)`'s alternatives are both
    /// undefined, so the claim is refuted at the instance, and the one record names the first
    /// alternative; each alternative is an undefined step, with or without the attribute.
    #[test]
    fn a_disjunctive_result_is_undefined_only_when_every_alternative_is() {
        for (name, _, result, free) in route_runs("pdo(0)") {
            assert!(!leaves(&result).is_empty(), "{name}: {result:#}");
            for leaf in leaves(&result) {
                assert_eq!(records(leaf), BTreeSet::new(), "{name}: {result:#}");
            }
            assert!(
                result.get("contradictedClaims").is_none(),
                "{name}: {result:#}"
            );
            assert_eq!(reasons(&free), reasons(&result), "claim-free {name}");
            assert_claim_free_records_nothing(&name, &free);
        }
        for (name, _, result, free) in route_runs("pdoo(0)") {
            let expected = preservation("pdoo");
            assert!(!leaves(&result).is_empty(), "{name}: {result:#}");
            for leaf in leaves(&result) {
                assert_eq!(
                    records(leaf),
                    BTreeSet::from([expected.clone()]),
                    "{name}: {result:#}"
                );
            }
            assert_eq!(run_records(&result), [expected], "{name}: {result:#}");
            assert_eq!(
                undefined_terms(&result),
                ["Lbl'UndsSlsh'Int'Unds'{}(\\dv{SortInt{}}(\"0\"), \\dv{SortInt{}}(\"0\"))"],
                "{name}: {result:#}"
            );
            for run in [&result, &free] {
                assert!(
                    reasons(run).iter().all(|reason| reason == "trivial"),
                    "{name}: {run:#}"
                );
            }
            assert_claim_free_records_nothing(&name, &free);
        }
    }

    /// `bt(0)`'s result `val(bot(0))` reaches `\bottom` through `bot`'s `#Bottom` equation, with
    /// no undefined builtin application: the declared rule's step is taken (its result is
    /// trusted), its successor is a vacuous state, and the record names the rule with
    /// `undefined` at `bot(0)`. Without the attribute the step decides the result itself and
    /// the leaf is the undefined step's `trivial` one.
    #[test]
    fn a_result_found_bottom_through_an_equation_refutes_the_claim() {
        for (name, _, result, free) in route_runs("bt(0)") {
            let expected = preservation("btr");
            assert!(!leaves(&result).is_empty(), "{name}: {result:#}");
            for leaf in leaves(&result) {
                assert_eq!(leaf["reason"], "vacuous", "{name}: {result:#}");
                assert_eq!(
                    records(leaf),
                    BTreeSet::from([expected.clone()]),
                    "{name}: {result:#}"
                );
            }
            assert_eq!(run_records(&result), [expected], "{name}: {result:#}");
            assert_eq!(
                undefined_terms(&result),
                ["Lblbot'LParUndsRParUnds'MAIN'Unds'Int'Unds'Int{}(\\dv{SortInt{}}(\"0\"))"],
                "{name}: {result:#}"
            );
            for leaf in leaves(&free) {
                assert_eq!(leaf["reason"], "trivial", "claim-free {name}: {free:#}");
            }
            assert_claim_free_records_nothing(&name, &free);
        }
    }

    /// `bts(0)` under strategy any: `btsa`'s successor is a vacuous state the sequential step
    /// keeps, so the run ends on a vacuous leaf that exists only because of the false claim, and
    /// the leaf and the list name it. Without the attribute `btsa`'s step is undefined and
    /// `btsb` covers it: `done`, nothing named. Under strategy all the `done` leaf is reached
    /// either way, and the record is on the list.
    #[test]
    fn a_vacuous_leaf_resting_on_a_false_claim_names_it() {
        for (name, strategy, result, free) in route_runs("bts(0)") {
            let expected = preservation("btsa");
            assert_eq!(
                run_records(&result),
                std::slice::from_ref(&expected),
                "{name}: {result:#}"
            );
            assert!(
                leaves(&result)
                    .iter()
                    .any(|leaf| records(leaf) == BTreeSet::from([expected.clone()])),
                "{name}: {result:#}"
            );
            if matches!(strategy, ExecutionStrategy::Any) {
                let [leaf] = leaves(&result).as_slice() else {
                    panic!("{name}: {result:#}");
                };
                assert_eq!(leaf["reason"], "vacuous", "{name}: {result:#}");
                assert!(
                    leaves(&free)
                        .iter()
                        .all(|leaf| super::observed::printed(leaf).contains("Lbldone")),
                    "claim-free {name}: {free:#}"
                );
            }
            assert_claim_free_records_nothing(&name, &free);
        }
    }

    /// A `total` symbol whose own equation's right-hand side is `#Bottom` on a defined argument
    /// contradicts its claim as an equation whose result reaches an undefined builtin does:
    /// `tbt(0)` names `tb` and `tbeq`, at `tb(0)`. `tbn(0)` reaches `\bottom` inside `tb2`'s
    /// result, through the partial `bot`: `tb2` and `tb2eq` are named, at `bot(0)`. The trusted
    /// claim discharges the rule's obligation, so its successor is a vacuous state; without the
    /// claim the step decides its result itself and the leaf is the undefined step's `trivial`
    /// one.
    #[test]
    fn a_total_symbol_whose_result_is_found_bottom_through_an_equation_is_named() {
        for (program, symbol, equation, rule, undefined) in [
            (
                "tbt(0)",
                "tb",
                "tbeq",
                "tbt",
                "Lbltb'LParUndsRParUnds'MAIN'Unds'Int'Unds'Int{}(\\dv{SortInt{}}(\"0\"))",
            ),
            (
                "tbn(0)",
                "tb2",
                "tb2eq",
                "tbn",
                "Lblbot'LParUndsRParUnds'MAIN'Unds'Int'Unds'Int{}(\\dv{SortInt{}}(\"0\"))",
            ),
        ] {
            for (name, _, result, free) in route_runs(program) {
                let expected = record(symbol, equation, Some(rule));
                assert!(!leaves(&result).is_empty(), "{name}: {result:#}");
                for leaf in leaves(&result) {
                    assert_eq!(
                        records(leaf),
                        BTreeSet::from([expected.clone()]),
                        "{name}: {result:#}"
                    );
                }
                assert_eq!(run_records(&result), [expected], "{name}: {result:#}");
                assert_eq!(undefined_terms(&result), [undefined], "{name}: {result:#}");
                for (run, reason) in [(&result, "vacuous"), (&free, "trivial")] {
                    assert!(
                        reasons(run).iter().all(|found| found == reason),
                        "{name}: {run:#}"
                    );
                }
                assert_claim_free_records_nothing(&name, &free);
            }
        }
    }

    /// A ground result term found undefined refutes the claim only where the step's premises
    /// hold. `pa` and `pb` have `requires` no integer satisfies, so their claims hold vacuously;
    /// from the symbolic `pa(X)` and `pb(X)` a solver that cannot decide the `requires` lets the
    /// step carry it, and its successor's undefined `val(1 /Int 0)` is named non-ground: it
    /// refutes nothing. Without a solver the `requires` is undecided and the step is not taken.
    #[test]
    fn a_result_under_a_carried_requires_refutes_nothing() {
        for (program, rule) in [("pa(0)", "pa"), ("pb(0)", "pb")] {
            let symbolic = |source: &str| {
                let (kore, ground) = compile(source, program);
                let printed = k_rust::kore::printer::Printer::compact().print_pattern(&ground);
                let symbolic = printed.replacen("\\dv{SortInt{}}(\"0\")", "VarX:SortInt{}", 1);
                assert_ne!(symbolic, printed);
                (
                    kore,
                    k_rust::kore::parser::parse_pattern(&symbolic).unwrap(),
                )
            };
            let (kore, initial) = symbolic(ROUTES);
            let (free, free_initial) = symbolic(&claim_free(ROUTES));
            for (name, strategy, modality, result) in each_run(&kore, &initial) {
                let context = format!("{program} symbolic under {name}: {result:#}");
                let listed = run_records(&result);
                if cfg!(feature = "z3-inference") {
                    assert!(!listed.is_empty(), "{context}");
                }
                for record in listed {
                    assert_eq!(
                        record,
                        (
                            "preserves-definedness".to_owned(),
                            "?".to_owned(),
                            format!("MAIN.{rule}"),
                            Some(format!("MAIN.{rule}")),
                            false,
                        ),
                        "{context}"
                    );
                }
                let free = super::observed::execute(&free, &free_initial, modality, strategy);
                assert_claim_free_records_nothing(&name, &free);
            }
        }
    }

    /// The console route: with a console, a ground unconstrained step simplifies its right-hand
    /// side within the step (`apply_rhs_alternative`), and an undefined result ends the step
    /// there. `pd(0)`'s `trivial` leaf and the list carry the record under either strategy;
    /// `pdsib(0)` under strategy any reaches `done` through `pdsibb` after finding `pdsiba`'s
    /// result undefined, so its leaf rests on the record. Without the attribute, nothing.
    #[test]
    fn the_console_route_names_a_contradicted_preserves_definedness() {
        use k_rust_backend::{
            definition::BackendDefinition,
            diagnostic::BackendDiagnostic,
            rewrite::{ExecutionMode, ExecutionOptions, execute_with_io_state},
            transition::ExecutionIoState,
        };
        let run = |source: &str, program: &str, mode: ExecutionMode| {
            let (kore, initial) = compile(source, program);
            let syntax = k_rust::kore::parser::parse_definition(&kore).unwrap();
            let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
            let initial = definition
                .admit_unverified(&initial, &[])
                .internalize_pattern()
                .unwrap();
            execute_with_io_state(
                &definition,
                initial,
                ExecutionOptions {
                    mode,
                    ..ExecutionOptions::default()
                },
                ExecutionIoState::new(Vec::new()),
            )
        };
        let labels = |diagnostics: &[BackendDiagnostic]| {
            diagnostics
                .iter()
                .filter_map(|diagnostic| match diagnostic {
                    BackendDiagnostic::ContradictedClaim(claim) => claim
                        .preservation()
                        .map(|preservation| (preservation.label.clone(), claim.ground)),
                    _ => None,
                })
                .collect::<Vec<_>>()
        };
        for (program, rule, modes) in [
            (
                "pd(0)",
                "MAIN.pd",
                &[ExecutionMode::All, ExecutionMode::Any][..],
            ),
            ("pdsib(0)", "MAIN.pdsiba", &[ExecutionMode::Any][..]),
        ] {
            for &mode in modes {
                let context = format!("{program} under {mode:?}");
                let result = run(PRESERVATION, program, mode);
                let expected = vec![(Some(rule.to_owned()), true)];
                let listed = result
                    .contradicted_claims
                    .iter()
                    .filter_map(|claim| {
                        claim
                            .preservation()
                            .map(|preservation| (preservation.label.clone(), claim.ground))
                    })
                    .collect::<Vec<_>>();
                assert_eq!(listed, expected, "{context}: {result:#?}");
                let [leaf] = result.leaves.as_slice() else {
                    panic!("{context}: {result:#?}");
                };
                assert_eq!(labels(&leaf.diagnostics), expected, "{context}: {leaf:#?}");
                let free = run(&claim_free(PRESERVATION), program, mode);
                assert!(free.contradicted_claims.is_empty(), "claim-free {context}");
                assert!(
                    free.leaves
                        .iter()
                        .all(|leaf| labels(&leaf.diagnostics).is_empty()),
                    "claim-free {context}"
                );
            }
        }
    }
}

/// What a record rests on, and the shapes the second fix round adds: a record is ground only
/// when nothing but `\top` was assumed to refute the claim, for a `total` claim (`tb3`, whose
/// `ensures` the path condition refutes, and `td2`, whose builtin result the path condition
/// makes undefined) as for a `preserves-definedness` one; a declared `#Bottom` right-hand side
/// (`pdb`) refutes the claim; deciding a disjunctive right-hand side emits nothing (`pdy`); and a
/// lineage whose result is `\bottom` is reused as any other (`un3`, through the `Unspecified`
/// `cntw(S, "")`, whose equation's result is the `#Bottom` of the partial `bot`).
mod premises {
    use std::collections::BTreeSet;

    use k_rust::kore::{ast::Pattern, parser::parse_pattern, printer::Printer};
    use serde_json::Value;

    use super::observed::{Record, compile, each_run, leaf_with, leaves, records, run_records};

    pub(super) const PREMISES: &str = r#"
module MAIN
  imports INT
  imports BOOL
  imports STRING
  syntax Pgm ::= "done" | val(Int) | w(Int) | mid(Int) | mid2(Int) | pdq(Int)
               | pdb(Int) | npdb(Int) | pdy(Int) | npdy(Int) | pdz(Int) | un3(String)
  syntax Int ::= q(Int) [function, total]
               | tb3(Int) [function, total]
               | td2(Int) [function, total]
               | grow(Int) [function]
               | bot(Int) [function]
               | pair(Int, Int) [function]
               | cntw(String, String) [function, total, hook(STRING.countAllOccurrences)]
               | cntx(String, String) [function, total, hook(STRING.countAllOccurrences)]
  configuration <k> $PGM:Pgm </k>
  rule [tb3eq]: tb3(I) => 1 ensures q(I) ==Int 1
  rule [td2eq]: td2(I) => 10 /Int q(I)
  rule [m]:     mid(X) => val(tb3(X))
  rule [m2]:    mid2(X) => val(td2(X))
  rule [pdq]:   pdq(X) => val(10 /Int q(X)) [preserves-definedness]
  rule [pdb]:   pdb(_) => #Bottom [preserves-definedness]
  rule [npdb]:  npdb(_) => #Bottom
  rule grow(I) => grow(I +Int 1) [simplification]
  rule [pdy]:   pdy(X) => (w(grow(X)) #Or done) [preserves-definedness]
  rule [npdy]:  npdy(X) => (w(grow(X)) #Or done)
  rule [pdz]:   pdz(X) => (done #Or w(grow(X))) [preserves-definedness]
  rule [boteq]: bot(I) => #Bottom requires I ==Int 0
  rule [boteq2]: bot(I) => I requires I =/=Int 0
  rule [cntw]:  cntw(_, "") => bot(0)
  rule [cntx]:  cntx(S, "") => pair(cntw(S, ""), cntw(S, ""))
  rule [un3]:   un3(S) => val(cntx(S, ""))
endmodule
"#;

    /// The definition with no claim at all.
    pub(super) fn claim_free(source: &str) -> String {
        super::checks_off::strip(source)
    }

    /// `program`'s initial configuration conjoined with `q(0) ==Int value`.
    pub(super) fn constrained(source: &str, program: &str, value: i64) -> (String, Pattern) {
        let (kore, ground) = compile(source, program);
        (kore, with_q(&ground, value))
    }

    /// `pattern` conjoined with `q(0) ==Int value`.
    pub(super) fn with_q(pattern: &Pattern, value: i64) -> Pattern {
        let printed = Printer::compact().print_pattern(pattern);
        let text = format!(
            "\\and{{SortGeneratedTopCell{{}}}}({printed}, \\equals{{SortInt{{}}, SortGeneratedTopCell{{}}}}(Lblq'LParUndsRParUnds'MAIN'Unds'Int'Unds'Int{{}}(\\dv{{SortInt{{}}}}(\"0\")), \\dv{{SortInt{{}}}}(\"{value}\")))"
        );
        parse_pattern(&text).unwrap()
    }

    fn total(symbol: &str, equation: &str, rule: &str, ground: bool) -> Record {
        (
            "total".to_owned(),
            format!("{symbol}(_)_MAIN_Int_Int"),
            format!("MAIN.{equation}"),
            Some(format!("MAIN.{rule}")),
            ground,
        )
    }

    /// Every run of `initial` over `kore` lists exactly `expected`.
    fn assert_listed(kore: &str, initial: &Pattern, expected: &[Record], context: &str) {
        for (name, _, _, result) in each_run(kore, initial) {
            assert_eq!(
                run_records(&result),
                expected,
                "{context} under {name}: {result:#}"
            );
        }
    }

    /// `mid(0)` under `q(0) ==Int 2`: `tb3(0)`'s `ensures q(0) ==Int 1` is refuted only by the
    /// path condition, and `q(0) = 1`, `tb3(0) = 1` is a model of the definition with the claim,
    /// so the record is not ground; under `q(0) ==Int 1` the `ensures` holds and nothing is
    /// named. `mid2(0)` under `q(0) ==Int 0` reaches `10 /Int 0` only through the path
    /// condition, the builtin route: not ground; under `q(0) ==Int 1` it is `10`. The same
    /// premise test makes `pdq(0)`'s preservation record under `q(0) ==Int 0` non-ground.
    #[test]
    fn a_claim_refuted_through_an_assumption_is_not_ground() {
        let free = claim_free(PREMISES);
        for (program, value, expected) in [
            ("mid(0)", 2, vec![total("tb3", "tb3eq", "m", false)]),
            ("mid(0)", 1, vec![]),
            ("mid2(0)", 0, vec![total("td2", "td2eq", "m2", false)]),
            ("mid2(0)", 1, vec![]),
            (
                "pdq(0)",
                0,
                vec![(
                    "preserves-definedness".to_owned(),
                    "?".to_owned(),
                    "MAIN.pdq".to_owned(),
                    Some("MAIN.pdq".to_owned()),
                    false,
                )],
            ),
        ] {
            let context = format!("{program} under q(0) ==Int {value}");
            let (kore, initial) = constrained(PREMISES, program, value);
            assert_listed(&kore, &initial, &expected, &context);
            let (kore, initial) = constrained(&free, program, value);
            assert_listed(&kore, &initial, &[], &format!("claim-free {context}"));
        }
    }

    /// A declared rule whose right-hand side is `#Bottom` claims a result defined that is defined
    /// nowhere: `pdb(0)`'s step applies, its `trivial` leaf and the list name the rule, ground.
    /// The undeclared `npdb(0)` has the same leaf and names nothing.
    #[test]
    fn a_declared_bottom_right_hand_side_refutes_the_claim() {
        let expected = (
            "preserves-definedness".to_owned(),
            "?".to_owned(),
            "MAIN.pdb".to_owned(),
            Some("MAIN.pdb".to_owned()),
            true,
        );
        let (kore, initial) = compile(PREMISES, "pdb(0)");
        let (undeclared, undeclared_initial) = compile(PREMISES, "npdb(0)");
        let reasons = |result: &Value| {
            leaves(result)
                .iter()
                .map(|leaf| leaf["reason"].clone())
                .collect::<Vec<_>>()
        };
        let plain = each_run(&undeclared, &undeclared_initial);
        for ((name, _, _, result), (_, _, _, npdb)) in
            each_run(&kore, &initial).into_iter().zip(plain)
        {
            let context = format!("pdb(0) under {name}: {result:#}");
            assert!(!leaves(&result).is_empty(), "{context}");
            for leaf in leaves(&result) {
                assert_eq!(
                    records(leaf),
                    BTreeSet::from([expected.clone()]),
                    "{context}"
                );
            }
            assert_eq!(
                run_records(&result),
                std::slice::from_ref(&expected),
                "{context}"
            );
            assert_eq!(reasons(&result), reasons(&npdb), "{context}");
            assert!(
                run_records(&npdb).is_empty(),
                "npdb(0) under {name}: {npdb:#}"
            );
        }
    }

    /// Deciding whether every alternative of `pdy`'s disjunctive result is `\bottom` normalizes
    /// `w(grow(0))`, whose simplification exhausts its budget; that normalization decides
    /// nothing in the run, so its diagnostics reach no leaf: the `done` leaf is clean, as it is
    /// for `pdz(0)`, whose `done` alternative comes first.
    #[test]
    fn deciding_a_disjunctive_result_emits_nothing() {
        for program in ["pdy(0)", "pdz(0)"] {
            let (kore, initial) = compile(PREMISES, program);
            for (name, _, _, result) in each_run(&kore, &initial) {
                let done = leaf_with(&result, "Lbldone");
                assert!(
                    done["diagnostics"]
                        .as_array()
                        .is_none_or(|diagnostics| diagnostics.is_empty()),
                    "{program} under {name}: {result:#}"
                );
                assert!(run_records(&result).is_empty(), "{program} under {name}");
            }
        }
    }

    /// `cntx("a", "")`'s value holds `cntw("a", "")` twice, and the first evaluation of it,
    /// whose result is `\bottom` through the partial `bot`, serves the second, as for a lineage
    /// whose result is defined: the claim-free run attempts fewer equations with the reuse of
    /// `Unspecified` evaluations than without it, and gives the same result.
    #[test]
    fn a_lineage_whose_result_is_bottom_is_reused() {
        use k_rust::backend::{ExecuteRequest, ExecutionStrategy};
        use k_rust_backend::simplify::without_unspecified_reuse;
        use k_rust_kore::measure::{Counter, snapshot};
        let (kore, initial) = compile(&claim_free(PREMISES), "un3(\"a\")");
        let run = || {
            let before = snapshot();
            let result = super::observed::backend(&kore)
                .execute(ExecuteRequest {
                    strategy: ExecutionStrategy::All,
                    ..ExecuteRequest::new(initial.clone())
                })
                .unwrap();
            let attempts = snapshot()
                .delta(&before)
                .get(Counter::SimplifyEquationAttempts);
            (serde_json::to_value(&result).unwrap(), attempts)
        };
        let (reused, with_reuse) = run();
        let (fresh, without_reuse) = without_unspecified_reuse(run);
        assert_eq!(reused, fresh);
        assert!(
            with_reuse < without_reuse,
            "equation attempts: {with_reuse} with reuse, {without_reuse} without"
        );
    }
}

/// What a ground record rests on (docs/compatibility.md, "A contradicted `total` attribute is
/// named, not repaired"): a record is ground only when the work that found `\bottom` depended on
/// nothing that may differ between models of the definition, which every such dependence
/// states as a path fact (an implementation-chosen value, among others), and assumed nothing but
/// `\top`. For a `total` claim that work is the evaluation from the application on (the
/// equation's selection, its conditions and its result); for a `preserves-definedness` claim it
/// is the step's attempt (its match and `requires`) and the normalization of its result. Each
/// case runs next to its mirror, whose chosen value leads away from `\bottom`.
mod derivations {
    use std::collections::BTreeSet;

    use super::observed::{Record, compile, each_run, leaves, records, run_records};

    pub(super) const CHOSEN: &str = r#"
module MAIN
  imports INT
  imports BOOL
  imports STRING
  imports MAP
  imports LIST
  imports K-EQUAL
  syntax Pgm ::= "done" | val(Int) | ka(Int) | kb(Int) | ca(Int) | cb(Int) | pka(Int) | pkb(Int)
               | kr(Int) | ks(Int) | pkr(Int) | pks(Int) | karg(Int)
  syntax Int ::= tka(Int) [function, total]
               | tkb(Int) [function, total]
               | tca(Int) [function, total]
               | tcb(Int) [function, total]
               | tkr(Int) [function, total]
               | tks(Int) [function, total]
               | td(Int) [function, total]
  configuration <k> $PGM:Pgm </k>
  rule [tkaeq]: tka(I) => 10 /Int (#if keys_list(1 |-> I 2 |-> I) ==K ListItem(1) ListItem(2) #then 0 #else 1 #fi)
  rule [tkbeq]: tkb(I) => 10 /Int (#if keys_list(1 |-> I 2 |-> I) ==K ListItem(2) ListItem(1) #then 0 #else 1 #fi)
  rule [tcaeq]: tca(I) => 10 /Int (#if Base2String(10, 16) ==String "a" #then I #else 1 #fi)
  rule [tcbeq]: tcb(I) => 10 /Int (#if Base2String(10, 16) ==String "A" #then I #else 1 #fi)
  rule [tkreq]: tkr(I) => 10 /Int I requires keys_list(1 |-> I 2 |-> I) ==K ListItem(1) ListItem(2)
  rule [tkseq]: tks(I) => 10 /Int I requires keys_list(1 |-> I 2 |-> I) ==K ListItem(2) ListItem(1)
  rule [tdeq]:  td(I) => 10 /Int I
  rule [ka]: ka(X) => val(tka(X))
  rule [kb]: kb(X) => val(tkb(X))
  rule [ca]: ca(X) => val(tca(X))
  rule [cb]: cb(X) => val(tcb(X))
  rule [kr]: kr(X) => val(tkr(X))
  rule [ks]: ks(X) => val(tks(X))
  rule [pka]: pka(X) => val(10 /Int (#if keys_list(1 |-> X 2 |-> X) ==K ListItem(1) ListItem(2) #then 0 #else 1 #fi)) [preserves-definedness]
  rule [pkb]: pkb(X) => val(10 /Int (#if keys_list(1 |-> X 2 |-> X) ==K ListItem(2) ListItem(1) #then 0 #else 1 #fi)) [preserves-definedness]
  rule [pkr]: pkr(X) => val(10 /Int X) requires keys_list(1 |-> X 2 |-> X) ==K ListItem(1) ListItem(2) [preserves-definedness]
  rule [pks]: pks(X) => val(10 /Int X) requires keys_list(1 |-> X 2 |-> X) ==K ListItem(2) ListItem(1) [preserves-definedness]
  rule [karg]: karg(X) => val(td(#if keys_list(1 |-> X 2 |-> X) ==K ListItem(1) ListItem(2) #then 0 #else 1 #fi))
endmodule
"#;

    fn total(symbol: &str, equation: &str, rule: &str, ground: bool) -> Record {
        (
            "total".to_owned(),
            format!("{symbol}(_)_MAIN_Int_Int"),
            format!("MAIN.{equation}"),
            Some(format!("MAIN.{rule}")),
            ground,
        )
    }

    fn preservation(rule: &str, ground: bool) -> Record {
        (
            "preserves-definedness".to_owned(),
            "?".to_owned(),
            format!("MAIN.{rule}"),
            Some(format!("MAIN.{rule}")),
            ground,
        )
    }

    /// Every leaf and the list of every run of `program` carry exactly `expected`, and the
    /// claim-free definition names nothing.
    fn assert_recorded(program: &str, expected: &[Record]) {
        let (kore, initial) = compile(CHOSEN, program);
        let (free, free_initial) = compile(&super::premises::claim_free(CHOSEN), program);
        for (name, _, _, result) in each_run(&kore, &initial) {
            let context = format!("{program} under {name}: {result:#}");
            assert!(!leaves(&result).is_empty(), "{context}");
            for leaf in leaves(&result) {
                assert_eq!(
                    records(leaf),
                    expected.iter().cloned().collect::<BTreeSet<_>>(),
                    "{context}"
                );
            }
            assert_eq!(run_records(&result), expected, "{context}");
        }
        for (name, _, _, result) in each_run(&free, &free_initial) {
            assert!(
                run_records(&result).is_empty(),
                "claim-free {program} under {name}: {result:#}"
            );
        }
    }

    /// `tka(0)`'s result is `\bottom` only because `keys_list` listed `1` first, a value the
    /// definition leaves open: in a model that lists `2` first, `tka(0)` is `10`, as the mirror
    /// `kb(0)` shows, so the record refutes nothing and is not ground.
    #[test]
    fn a_total_bottom_that_rests_on_a_chosen_order_is_not_ground() {
        assert_recorded("ka(0)", &[total("tka", "tkaeq", "ka", false)]);
        assert_recorded("kb(0)", &[]);
    }

    /// The same for `Base2String`'s letter case (`ca(0)`, mirror `cb(0)`).
    #[test]
    fn a_total_bottom_that_rests_on_a_chosen_letter_case_is_not_ground() {
        assert_recorded("ca(0)", &[total("tca", "tcaeq", "ca", false)]);
        assert_recorded("cb(0)", &[]);
    }

    /// The same for a `preserves-definedness` result term (`pka(0)`, mirror `pkb(0)`).
    #[test]
    fn a_result_bottom_that_rests_on_a_chosen_value_is_not_ground() {
        assert_recorded("pka(0)", &[preservation("pka", false)]);
        assert_recorded("pkb(0)", &[]);
    }

    /// A chosen value that decided a premise of the work is a dependence too: `tkr`'s equation
    /// applies to `tkr(0)` because its `requires` read `keys_list`'s order. Its mirror does not
    /// apply (`tks(0)` stays unevaluated) and names nothing.
    #[test]
    fn an_equation_requires_decided_by_a_chosen_value_is_a_dependence() {
        assert_recorded("kr(0)", &[total("tkr", "tkreq", "kr", false)]);
        assert_recorded("ks(0)", &[]);
    }

    /// `pkr`'s step applies to `pkr(0)` because its `requires` read `keys_list`'s order; the
    /// mirror `pks(0)` is stuck and names nothing.
    #[test]
    fn a_rule_requires_decided_by_a_chosen_value_is_a_dependence() {
        assert_recorded("pkr(0)", &[preservation("pkr", false)]);
        assert_recorded("pks(0)", &[]);
    }

    /// A chosen value that only built the contradicted application is no part of the work that
    /// found `\bottom`: `karg(0)`'s configuration holds `td(0)` because `keys_list` listed `1`
    /// first, and `td(0)` is `\bottom` through `td`'s own equation in every model. The record is
    /// ground; the leaf's chosen-value mark says that the path is one model's.
    #[test]
    fn a_chosen_value_that_only_built_the_application_leaves_the_record_ground() {
        assert_recorded("karg(0)", &[total("td", "tdeq", "karg", true)]);
    }

    pub(super) const REUSE: &str = r#"
module MAIN
  imports INT
  imports BOOL
  imports STRING
  syntax Pgm ::= "done" | val(Int) | un7(String) | un8(String)
  syntax Int ::= tt(String) [function, total]
               | tt2(String) [function, total]
               | bot(Int) [function]
               | pair(Int, Int) [function]
               | cnt2(String, String) [function, hook(STRING.countAllOccurrences)]
               | cntz(String, String) [function, hook(STRING.countAllOccurrences)]
               | cnty(String, String) [function, hook(STRING.countAllOccurrences)]
  configuration <k> $PGM:Pgm </k>
  rule [boteq]: bot(I) => #Bottom requires I ==Int 0
  rule [boteq2]: bot(I) => I requires I =/=Int 0
  rule [cnt2eq]: cnt2(_, "") => bot(0)
  rule [tteq]: tt(S) => cnt2(S, "")
  rule [tt2eq]: tt2(S) => cnt2(S, "")
  rule [cntzeq]: cntz(S, "") => pair(tt(S), tt2(S))
  rule [cntyeq]: cnty(S, "") => pair(cnt2(S, ""), tt2(S))
  rule [un7]: un7(S) => val(cntz(S, ""))
  rule [un8]: un8(S) => val(cnty(S, ""))
endmodule
"#;

    /// The `Unspecified` application `cnt2("a", "")` is `\bottom` through the partial `bot`, and
    /// its first evaluation serves the second. Its result reaches `\bottom` under `tt`'s
    /// equation and again under `tt2`'s, so both `total` claims are contradicted, with the reuse
    /// of `Unspecified` evaluations as without it: in `un7`, the first evaluation ran under
    /// `tt`'s step, which named it, and the served value does not carry that naming to `tt2`'s
    /// step; in `un8`, the first ran outside every `total` step. Reuse still serves the value
    /// (fewer equation attempts).
    #[test]
    fn a_reused_bottom_names_every_total_step_it_is_served_under() {
        use k_rust::backend::ExecuteRequest;
        use k_rust_backend::simplify::without_unspecified_reuse;
        use k_rust_kore::measure::{Counter, snapshot};
        let record = |symbol: &str, equation: &str, rule: &str| {
            (
                "total".to_owned(),
                format!("{symbol}(_)_MAIN_Int_String"),
                format!("MAIN.{equation}"),
                Some(format!("MAIN.{rule}")),
                true,
            )
        };
        for (program, rule) in [("un7(\"a\")", "un7"), ("un8(\"a\")", "un8")] {
            // `un7` evaluates `tt` first; `un8` has no `tt`.
            let expected = if rule == "un7" {
                vec![record("tt", "tteq", rule), record("tt2", "tt2eq", rule)]
            } else {
                vec![record("tt2", "tt2eq", rule)]
            };
            let (kore, initial) = compile(REUSE, program);
            for strategy in super::observed::STRATEGIES {
                let run = || {
                    let before = snapshot();
                    let result = super::observed::backend(&kore)
                        .execute(ExecuteRequest {
                            strategy,
                            ..ExecuteRequest::new(initial.clone())
                        })
                        .unwrap();
                    let attempts = snapshot()
                        .delta(&before)
                        .get(Counter::SimplifyEquationAttempts);
                    (serde_json::to_value(&result).unwrap(), attempts)
                };
                let (reused, with_reuse) = run();
                let (fresh, without_reuse) = without_unspecified_reuse(run);
                let context = format!("{program} under {strategy:?}");
                assert_eq!(
                    run_records(&reused),
                    expected,
                    "{context} with reuse: {reused:#}"
                );
                assert_eq!(
                    run_records(&fresh),
                    expected,
                    "{context} without reuse: {fresh:#}"
                );
                assert_eq!(reused, fresh, "{context}");
                assert!(
                    with_reuse < without_reuse,
                    "{context}: equation attempts {with_reuse} with reuse, {without_reuse} without"
                );
            }
        }
    }
}

/// The claim checks observe and decide nothing (docs/compatibility.md, "A contradicted `total`
/// attribute is named, not repaired"): every run is the same with the checks on and with them
/// off (`k_rust_backend::path_facts::without_claim_checks`, which notes no record and does none
/// of the work done only to find one), apart from the records. The oracle runs every definition
/// of this file, each probe definition of the reviews of the change that added the records, the
/// claim-free variant of each (no `total`, no `preserves-definedness`), and the light IMP corpus,
/// under both strategies and both result modalities, by every route: executed (plain, stopping
/// at a branch, collecting coverage, with a breadth bound, assuming the state defined), executed
/// observed, searched (graph final and all, paths) and, for ground inputs, executed with a
/// console; and per input, simplified, implied by itself and asked for a model. Claims are
/// proved by the same pairs ([`the_proof_route`]). Every output must be equal once the records
/// (`contradicted-claim` diagnostics and `contradictedClaims`) are taken out: leaves, their
/// states, reasons, order, other diagnostics, halts, `work` and the run-level lists. A
/// claim-free definition must also count the same work: every `measure` counter is equal. A
/// claim-carrying definition may count more where a claim is checked (the counters that differ
/// are printed); a proof counts the same in every case.
///
/// The fixtures and probes run with no work, depth, breadth or result bound: a bound that is set
/// puts every path fact the run noted so far on every leaf (docs/compatibility.md, "`maxWork`"),
/// which would hide which leaf carries which fact. The IMP corpus alone runs bounded
/// ([`Tier::Bounded`]).
///
/// A later finding of the same kind becomes an input here.
mod checks_off {
    use k_rust::{
        backend::{
            ExecuteRequest, ExecutionStrategy, ObservedRequest, ResultModalityOutput,
            SearchRequest, SearchTypeArg,
        },
        kore::{ast::Pattern, parser::parse_pattern, printer::Printer},
    };
    use k_rust_backend::path_facts::without_claim_checks;
    use k_rust_kore::measure::{self, Snapshot};
    use serde_json::Value;

    use super::observed::{MODALITIES, STRATEGIES, backend_in, compile_in};

    /// The definition with every claim attribute removed.
    pub(super) fn strip(source: &str) -> String {
        source
            .replace("[function, total", "[function")
            .replace(" [preserves-definedness]", "")
    }

    /// Whether `source` writes a claim attribute.
    fn claims(source: &str) -> bool {
        source.contains("total") || source.contains("preserves-definedness")
    }

    /// One input of a definition.
    #[derive(Clone, Copy)]
    enum Input {
        /// A program, at sort `Pgm`.
        Ground(&'static str),
        /// A program whose `777`s become the variable `X`.
        Symbolic(&'static str),
        /// A program conjoined with `q(0) ==Int value`.
        Constrained(&'static str, i64),
    }

    impl Input {
        fn pattern(self, source: &str, main: &str) -> (String, Pattern) {
            match self {
                Input::Ground(program) => compile_in(source, main, program),
                Input::Symbolic(program) => {
                    let (kore, ground) = compile_in(source, main, program);
                    let printed = Printer::compact().print_pattern(&ground);
                    let symbolic = printed.replace("\\dv{SortInt{}}(\"777\")", "VarX:SortInt{}");
                    assert_ne!(symbolic, printed, "{program}");
                    (kore, parse_pattern(&symbolic).unwrap())
                }
                Input::Constrained(program, value) => {
                    let (kore, ground) = compile_in(source, main, program);
                    (kore, super::premises::with_q(&ground, value))
                }
            }
        }

        fn name(self) -> String {
            match self {
                Input::Ground(program) => program.to_owned(),
                Input::Symbolic(program) => format!("{program} with X for 777"),
                Input::Constrained(program, value) => format!("{program} /\\ q(0) ==Int {value}"),
            }
        }
    }

    /// Everything a run gives, with the records taken out: each response's JSON, the console
    /// run's result printed, and the counters of the whole run (the definition's load included).
    struct Outputs {
        responses: Vec<Value>,
        counters: Snapshot,
    }

    /// `value` without its records: every `contradicted-claim` diagnostic and every
    /// `contradictedClaims` list, a `diagnostics` list left empty removed as an absent one is.
    fn without_records(value: &mut Value) {
        match value {
            Value::Object(object) => {
                object.remove("contradictedClaims");
                if let Some(Value::Array(diagnostics)) = object.get_mut("diagnostics") {
                    diagnostics.retain(|diagnostic| diagnostic["kind"] != "contradicted-claim");
                    if diagnostics.is_empty() {
                        object.remove("diagnostics");
                    }
                }
                for value in object.values_mut() {
                    without_records(value);
                }
            }
            Value::Array(values) => values.iter_mut().for_each(without_records),
            _ => {}
        }
    }

    /// The console run's result without its records, printed.
    fn console_without_records(mut result: k_rust_backend::rewrite::ExecutionResult) -> Value {
        use k_rust_backend::diagnostic::BackendDiagnostic;
        result.contradicted_claims.clear();
        for leaf in &mut result.leaves {
            leaf.diagnostics.retain(|diagnostic| {
                !matches!(diagnostic, BackendDiagnostic::ContradictedClaim(_))
            });
        }
        Value::String(format!("{result:#?}"))
    }

    /// How a definition's inputs are run. IMP's `strict` and `seqstrict` attributes admit every
    /// evaluation order, so under strategy `all` an unbounded run enumerates every interleaving:
    /// the path-set execution, the observed execution's per-leaf traces and the path search of
    /// the three-line `sum` program alone took one process to 39 GB. Bounded, a bound that fires
    /// fires alike with the checks on and off, so the comparison holds; it only puts every fact
    /// of the run on every leaf, alike on both sides.
    #[derive(Clone, Copy)]
    enum Tier {
        /// No work, depth, breadth or result bound: every fixture and probe.
        Unbounded,
        /// The IMP corpus.
        Bounded,
    }

    const MAX_WORK: u64 = 400;
    const MAX_DEPTH: u64 = 400;
    const MAX_BREADTH: usize = 16;
    const MAX_SIMPLIFICATION_ITERATIONS: usize = 100;

    /// A response as JSON, an error as its message.
    fn json<T: serde::Serialize>(response: Result<T, k_rust::backend::BackendError>) -> Value {
        match response {
            Ok(response) => serde_json::to_value(&response).unwrap(),
            Err(error) => Value::String(format!("error: {}", error.message())),
        }
    }

    /// Run `work` on a thread of its own, with the claim checks on or off, and count it.
    fn counted<T: Send + 'static>(
        checks: bool,
        work: impl FnOnce() -> T + Send + 'static,
    ) -> (T, Snapshot) {
        std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn(move || {
                let work = move || {
                    let before = measure::snapshot();
                    let result = work();
                    (result, measure::snapshot().delta(&before))
                };
                if checks {
                    work()
                } else {
                    without_claim_checks(work)
                }
            })
            .unwrap()
            .join()
            .unwrap()
    }

    /// Run `initial` over `kore` by every execution and search route, under one strategy and
    /// modality, with the claim checks on or off.
    #[allow(clippy::too_many_arguments)]
    fn run(
        kore: &str,
        main: &str,
        initial: &Pattern,
        strategy: ExecutionStrategy,
        modality: ResultModalityOutput,
        console: bool,
        tier: Tier,
        checks: bool,
    ) -> Outputs {
        let (kore, main, initial) = (kore.to_owned(), main.to_owned(), initial.clone());
        let bounded = matches!(tier, Tier::Bounded);
        let (mut responses, counters) = counted(checks, move || {
            let request = || {
                let request = ExecuteRequest {
                    result_modality: modality,
                    strategy,
                    ..ExecuteRequest::new(initial.clone())
                };
                if bounded {
                    ExecuteRequest {
                        max_work: Some(MAX_WORK),
                        max_depth: Some(MAX_DEPTH),
                        max_simplification_iterations: MAX_SIMPLIFICATION_ITERATIONS,
                        ..request
                    }
                } else {
                    request
                }
            };
            let search = |search_type| {
                let request = SearchRequest {
                    search_type,
                    ..SearchRequest::new(initial.clone())
                };
                if bounded {
                    SearchRequest {
                        max_depth: Some(MAX_DEPTH),
                        max_breadth: Some(MAX_BREADTH),
                        max_results: Some(MAX_BREADTH),
                        max_simplification_iterations: MAX_SIMPLIFICATION_ITERATIONS,
                        ..request
                    }
                } else {
                    request
                }
            };
            let mut backend = backend_in(&kore, &main);
            let mut responses = vec![
                json(backend.execute(request())),
                json(backend.execute(ExecuteRequest {
                    stop_at_branch: true,
                    ..request()
                })),
                json(backend.execute(ExecuteRequest {
                    collect_coverage: true,
                    ..request()
                })),
                json(backend.execute(ExecuteRequest {
                    max_breadth: Some(1),
                    ..request()
                })),
                json(backend.execute(ExecuteRequest {
                    assume_state_defined: true,
                    ..request()
                })),
                json(backend.execute_observed(ObservedRequest {
                    request: request(),
                    rules: None,
                })),
                json(backend.search(search(SearchTypeArg::Final))),
                json(backend.search(search(SearchTypeArg::All))),
                json(backend.search_paths(search(SearchTypeArg::Final))),
            ];
            if console {
                use k_rust_backend::{
                    rewrite::{ExecutionMode, ExecutionOptions, execute_with_io_state},
                    transition::ExecutionIoState,
                };
                let definition = backend.select_definition(None).unwrap();
                let pattern = definition
                    .admit_unverified(&initial, &[])
                    .internalize_pattern()
                    .unwrap();
                let mode = match strategy {
                    ExecutionStrategy::All => ExecutionMode::All,
                    _ => ExecutionMode::Any,
                };
                let options = if bounded {
                    ExecutionOptions {
                        mode,
                        max_work: Some(MAX_WORK),
                        max_depth: MAX_DEPTH,
                        max_simplification_iterations: MAX_SIMPLIFICATION_ITERATIONS,
                        ..ExecutionOptions::default()
                    }
                } else {
                    ExecutionOptions {
                        mode,
                        ..ExecutionOptions::default()
                    }
                };
                responses.push(console_without_records(execute_with_io_state(
                    &definition,
                    pattern,
                    options,
                    ExecutionIoState::new(Vec::new()),
                )));
            }
            responses
        });
        responses.iter_mut().for_each(without_records);
        Outputs {
            responses,
            counters,
        }
    }

    /// Simplify `initial`, ask whether it implies itself and ask for a model of it, with the
    /// claim checks on or off: the routes that do not depend on a strategy.
    fn requests(kore: &str, main: &str, initial: &Pattern, checks: bool) -> Outputs {
        use k_rust::backend::{ImplicationRequest, PatternRequest};
        let (kore, main, initial) = (kore.to_owned(), main.to_owned(), initial.clone());
        let (mut responses, counters) = counted(checks, move || {
            let mut backend = backend_in(&kore, &main);
            vec![
                json(backend.simplify(PatternRequest::new(initial.clone()))),
                json(backend.implies(ImplicationRequest::new(initial.clone(), initial.clone()))),
                json(backend.get_model(PatternRequest::new(initial.clone()))),
            ]
        });
        responses.iter_mut().for_each(without_records);
        Outputs {
            responses,
            counters,
        }
    }

    /// The counters that differ between `on` and `off`, by name.
    fn differing(on: &Snapshot, off: &Snapshot) -> Vec<(&'static str, u64, u64)> {
        on.iter()
            .zip(off.iter())
            .filter(|((_, on), (_, off))| on != off)
            .map(|((name, on), (_, off))| (name, on, off))
            .collect()
    }

    /// The oracle over `source` (main module `main`) and its claim-free variant, each input
    /// under both strategies and both modalities, unbounded.
    fn assert_inert(case: &str, source: &str, main: &str, inputs: &[Input]) {
        assert_inert_in(Tier::Unbounded, case, source, main, inputs);
    }

    /// The equality and the counters of one pair of runs.
    fn assert_pair(context: &str, on: &Outputs, off: &Outputs, claim_free: bool) {
        assert_eq!(on.responses.len(), off.responses.len(), "{context}");
        for (on, off) in on.responses.iter().zip(&off.responses) {
            assert_eq!(on, off, "{context}: checks on, then off");
        }
        let counters = differing(&on.counters, &off.counters);
        if claim_free {
            assert!(
                counters.is_empty(),
                "{context}: counters (name, on, off) {counters:?}"
            );
        } else if !counters.is_empty() {
            eprintln!("counter growth, {context}: (name, on, off) {counters:?}");
        }
    }

    /// [`assert_inert`] in `tier`.
    fn assert_inert_in(tier: Tier, case: &str, source: &str, main: &str, inputs: &[Input]) {
        let stripped = strip(source);
        assert!(
            !claims(&stripped),
            "{case}: the stripped variant claims nothing"
        );
        let variants = if claims(source) {
            vec![
                (case.to_owned(), source.to_owned()),
                (format!("{case} claim-free"), stripped),
            ]
        } else {
            vec![(format!("{case} (claim-free)"), source.to_owned())]
        };
        for (variant, source) in variants {
            let claim_free = !claims(&source);
            let mut warmed = false;
            for &input in inputs {
                let (kore, initial) = input.pattern(&source, main);
                let console = matches!(input, Input::Ground(_));
                for strategy in STRATEGIES {
                    for modality in MODALITIES {
                        let context = format!(
                            "{variant}: {} under {strategy:?} {modality:?}",
                            input.name()
                        );
                        let run_once = |checks| {
                            run(
                                &kore, main, &initial, strategy, modality, console, tier, checks,
                            )
                        };
                        if !warmed {
                            run_once(true);
                            warmed = true;
                        }
                        let on = run_once(true);
                        let off = run_once(false);
                        assert_pair(&context, &on, &off, claim_free);
                    }
                }
                let context = format!("{variant}: {} by request", input.name());
                let on = requests(&kore, main, &initial, true);
                let off = requests(&kore, main, &initial, false);
                assert_pair(&context, &on, &off, claim_free);
            }
        }
    }

    use Input::{Constrained, Ground, Symbolic};

    #[test]
    fn the_total_fixtures() {
        assert_inert(
            "CLAIMS",
            super::observed::CLAIMS,
            "MAIN",
            &[
                Ground("r(0)"),
                Ground("r(1)"),
                Ground("ro(0)"),
                Ground("e(0)"),
                Ground("rc(0)"),
                Ground("rp(0)"),
                Ground("rq(0)"),
                Ground("sib(0)"),
                Ground("s3(0)"),
                Ground("m2(0)"),
                Ground("un(\"a\")"),
                Symbolic("r(777)"),
                Symbolic("sib(777)"),
            ],
        );
    }

    #[test]
    fn the_load_loop_and_non_ground_fixtures() {
        assert_inert("LOOP", super::LOOP, "MAIN", &[Ground("loop(2)")]);
        assert_inert(
            "LOAD",
            super::LOAD,
            "MAIN",
            &[Ground("go(1)"), Ground("val(fe(0))")],
        );
        assert_inert(
            "NON_GROUND",
            super::NON_GROUND,
            "MAIN",
            &[Ground("rz(0)"), Symbolic("rz(777)")],
        );
    }

    #[test]
    fn the_refusal_fixtures() {
        assert_inert(
            "REFUSALS",
            super::refusals::REFUSALS,
            "MAIN",
            &[
                Ground("run(1)"),
                Ground("run(1099511627776)"),
                Ground("runh(1)"),
                Ground("runc(\"1099511627776\")"),
            ],
        );
    }

    #[test]
    fn the_preservation_fixtures() {
        assert_inert(
            "PRESERVATION",
            super::preservation::PRESERVATION,
            "MAIN",
            &[
                Ground("pd(0)"),
                Ground("npd(0)"),
                Ground("pdt(0)"),
                Ground("pdp(0)"),
                Ground("pdens(0)"),
                Ground("pdsib(0)"),
                Ground("two(0)"),
                Ground("tdiv(0)"),
                Symbolic("pd(777)"),
            ],
        );
        assert_inert(
            "ROUTES",
            super::preservation::ROUTES,
            "MAIN",
            &[
                Ground("pdo(0)"),
                Ground("pdoo(0)"),
                Ground("bt(0)"),
                Ground("bts(0)"),
                Ground("tbt(0)"),
                Ground("tbn(0)"),
                Symbolic("pa(777)"),
                Symbolic("pb(777)"),
            ],
        );
    }

    #[test]
    fn the_premise_fixtures() {
        assert_inert(
            "PREMISES",
            super::premises::PREMISES,
            "MAIN",
            &[
                Constrained("mid(0)", 0),
                Constrained("mid(0)", 1),
                Constrained("mid(0)", 2),
                Constrained("mid2(0)", 0),
                Constrained("mid2(0)", 1),
                Constrained("mid2(0)", 2),
                Constrained("pdq(0)", 0),
                Constrained("pdq(0)", 1),
                Constrained("pdq(0)", 2),
                Ground("pdb(0)"),
                Ground("npdb(0)"),
                Ground("pdy(0)"),
                Ground("npdy(0)"),
                Ground("pdz(0)"),
                Ground("un3(\"a\")"),
            ],
        );
    }

    // The probe definitions of code-reviews/KINK-18-3.toml (p1 to p7).

    const P1: &str = r#"
module MAIN
  imports INT
  syntax Pgm ::= "done" | val(Int) | c(Int, Int) | cr(Int, Int) | bt(Int) | own(Int)
  syntax Int ::= bot(Int) [function]
               | tp(Int) [function]
  configuration <k> $PGM:Pgm </k>
  rule [boteq]: bot(I) => #Bottom requires I ==Int 0
  rule [boteq2]: bot(I) => I requires I =/=Int 0
  rule [tpeq]: tp(I) => 10 /Int I
  rule [cz]: c(0, Y) => val(Y) [preserves-definedness]
  rule [crr]: cr(X, Y) => val(Y) requires X ==Int 0 [preserves-definedness]
  rule [btr]: bt(X) => val(bot(X)) [preserves-definedness]
  rule [ownr]: own(X) => val(X) ensures #Ceil(10 /Int X) [preserves-definedness]
endmodule
"#;

    const P2: &str = r#"
module MAIN
  imports INT
  syntax Pgm ::= "done" | val(Int) | bt(Int) | nbt(Int) | tbt(Int)
  syntax Int ::= bot(Int) [function]
               | tb(Int) [function, total]
  configuration <k> $PGM:Pgm </k>
  rule [boteq]: bot(I) => #Bottom requires I ==Int 0
  rule [boteq2]: bot(I) => I requires I =/=Int 0
  rule [tbeq]: tb(I) => #Bottom requires I ==Int 0
  rule [tbeq2]: tb(I) => I requires I =/=Int 0
  rule [btr]: bt(X) => val(bot(X)) [preserves-definedness]
  rule [nbtr]: nbt(X) => val(bot(X))
  rule [tbtr]: tbt(X) => val(tb(X))
endmodule
"#;

    const P3: &str = r#"
module MAIN
  imports INT
  syntax Pgm ::= "done" | val(Int) | pd(Int) | npd(Int) | pdt(Int)
  syntax Int ::= td(Int) [function, total]
  configuration <k> $PGM:Pgm </k>
  rule [tdeq]: td(I) => 10 /Int (I +Int 0)
  rule [pd]: pd(X) => val(X /Int 0) [preserves-definedness]
  rule [npd]: npd(X) => val(X /Int 0)
  rule [pdt]: pdt(X) => val(td(X))
endmodule
"#;

    const P4: &str = r#"
module MAIN
  imports INT
  imports BOOL
  syntax Pgm ::= "done" | val(Int) | pdr(Int) | pds(Int)
  syntax Int ::= q(Int) [function, total]
  configuration <k> $PGM:Pgm </k>
  rule [pdr]: pdr(X) => val(1 /Int 0) requires X *Int X <Int 0 [preserves-definedness]
  rule [pds]: pds(X) => val(1 /Int 0) requires (q(X) ==Int 1) andBool (q(X) ==Int 2) [preserves-definedness]
endmodule
"#;

    const P5: &str = r#"
module MAIN
  imports INT
  imports BOOL
  imports STRING
  syntax Pgm ::= "done" | val(Int) | pa(Int) | pb(Int) | pc(Int) | na(Int)
  configuration <k> $PGM:Pgm </k>
  rule [pa]: pa(X) => val(1 /Int 0) requires 2 ^Int X ==Int 3 [preserves-definedness]
  rule [pb]: pb(X) => val(1 /Int 0) requires lengthString(Int2String(X)) ==Int 0 [preserves-definedness]
  rule [pc]: pc(X) => val(1 /Int 0) requires X *Int X *Int X ==Int 2 [preserves-definedness]
  rule [na]: na(X) => val(1 /Int 0) requires lengthString(Int2String(X)) ==Int 0
endmodule
"#;

    const P6: &str = r#"
module MAIN
  imports INT
  imports BOOL
  syntax Pgm ::= "done" | val(Int) | bts(Int) | nbts(Int) | pds(Int)
  syntax Int ::= bot(Int) [function]
  configuration <k> $PGM:Pgm </k>
  rule [boteq]: bot(I) => #Bottom requires I ==Int 0
  rule [boteq2]: bot(I) => I requires I =/=Int 0
  rule [btsa]: bts(X) => val(bot(X)) [preserves-definedness]
  rule [btsb]: bts(_) => done
  rule [nbtsa]: nbts(X) => val(bot(X))
  rule [nbtsb]: nbts(_) => done
  rule [pdsa]: pds(X) => val(X /Int 0) [preserves-definedness]
  rule [pdsb]: pds(_) => done
endmodule
"#;

    const P7: &str = r#"
module MAIN
  imports INT
  imports BOOL
  syntax Pgm ::= "done" | val(Int) | pdo(Int) | npdo(Int)
  configuration <k> $PGM:Pgm </k>
  rule [pdo]: pdo(X) => (val(X /Int 0) #Or done) [preserves-definedness]
  rule [npdo]: npdo(X) => (val(X /Int 0) #Or done)
endmodule
"#;

    #[test]
    fn the_first_review_s_probes() {
        assert_inert(
            "p1",
            P1,
            "MAIN",
            &[
                Ground("c(7, 8)"),
                Ground("c(0, 8)"),
                Ground("bt(0)"),
                Ground("own(0)"),
                Ground("own(1)"),
                Symbolic("c(777, 10 /Int 777)"),
                Symbolic("cr(777, 10 /Int 777)"),
            ],
        );
        assert_inert(
            "p2",
            P2,
            "MAIN",
            &[Ground("bt(0)"), Ground("nbt(0)"), Ground("tbt(0)")],
        );
        assert_inert(
            "p3",
            P3,
            "MAIN",
            &[Ground("pd(0)"), Ground("npd(0)"), Ground("pdt(0)")],
        );
        assert_inert(
            "p4",
            P4,
            "MAIN",
            &[Ground("pdr(7)"), Symbolic("pdr(777)"), Symbolic("pds(777)")],
        );
        assert_inert(
            "p5",
            P5,
            "MAIN",
            &[
                Ground("pa(7)"),
                Symbolic("pa(777)"),
                Symbolic("pb(777)"),
                Symbolic("pc(777)"),
                Symbolic("na(777)"),
            ],
        );
        assert_inert(
            "p6",
            P6,
            "MAIN",
            &[Ground("bts(0)"), Ground("nbts(0)"), Ground("pds(0)")],
        );
        assert_inert("p7", P7, "MAIN", &[Ground("pdo(0)"), Ground("npdo(0)")]);
    }

    // The probe definitions of code-reviews/KINK-18-3-fix1.toml (q1 to q7; q2 is PREMISES's
    // `mid`, `mid2` and `pdq`).

    const Q1: &str = r#"
module MAIN
  imports INT
  imports BOOL
  syntax Pgm ::= "done" | val(Int) | w(Int)
               | pd3(Int) | npd3(Int) | pd3b(Int) | pdn(Int) | npdn(Int)
               | pdi(Int) | npdi(Int) | pdm(Int) | npdm(Int)
               | pdb(Int) | npdb(Int) | pdc(Int) | npdc(Int) | pdc2(Int)
  syntax Pgm ::= mac(Int) [macro]
  rule mac(X) => (val(X /Int 0) #Or done)
  configuration <k> $PGM:Pgm </k> <aux> 0 </aux>
  rule [pd3]:  pd3(X) => (val(X /Int 0) #Or val(X /Int 0 +Int 1) #Or done) [preserves-definedness]
  rule [npd3]: npd3(X) => (val(X /Int 0) #Or val(X /Int 0 +Int 1) #Or done)
  rule [pd3b]: pd3b(X) => (val(X /Int 0) #Or (val(X /Int 0 +Int 1) #Or val(X /Int 0 +Int 2))) [preserves-definedness]
  rule [pdn]:  pdn(X) => (val(X /Int 0) #Or (done #Or val(X /Int 0 +Int 2))) [preserves-definedness]
  rule [npdn]: npdn(X) => (val(X /Int 0) #Or (done #Or val(X /Int 0 +Int 2)))
  rule [pdi]:  pdi(X) => val((X /Int 0) #Or 1) [preserves-definedness]
  rule [npdi]: npdi(X) => val((X /Int 0) #Or 1)
  rule [pdm]:  pdm(X) => mac(X) [preserves-definedness]
  rule [npdm]: npdm(X) => mac(X)
  rule [pdb]:  pdb(_) => #Bottom [preserves-definedness]
  rule [npdb]: npdb(_) => #Bottom
  rule [pdc]:  <k> pdc(X) => (val(X /Int 0) #Or done) </k> <aux> _ => 1 </aux> [preserves-definedness]
  rule [npdc]: <k> npdc(X) => (val(X /Int 0) #Or done) </k> <aux> _ => 1 </aux>
  rule [pdc2]: <k> pdc2(X) => (val(X /Int 0) #Or val(X /Int 0 +Int 1)) </k> <aux> _ => 1 </aux> [preserves-definedness]
endmodule
"#;

    const Q3: &str = r#"
module MAIN
  imports INT
  imports BOOL
  syntax Pgm ::= "done" | val(Int) | w(Int)
               | pdw(Int) | npdw(Int) | pdw2(Int) | npdw2(Int)
  syntax Bool ::= g(Int) [function, total]
  syntax Int ::= f(Int) [function]
  configuration <k> $PGM:Pgm </k>
  rule f(I) => 1 requires g(I)
  rule [pdw]:   pdw(X) => (w(f(X)) #Or val(X /Int 0)) [preserves-definedness]
  rule [npdw]:  npdw(X) => (w(f(X)) #Or val(X /Int 0))
  rule [pdw2]:  pdw2(X) => (val(X /Int 0) #Or w(f(X))) [preserves-definedness]
  rule [npdw2]: npdw2(X) => (val(X /Int 0) #Or w(f(X)))
endmodule
"#;

    const Q4: &str = r#"
module MAIN
  imports INT
  imports BOOL
  syntax Pgm ::= "done" | val(Int) | pdoc(Int) | pdod(Int)
  configuration <k> $PGM:Pgm </k>
  rule [pdoc]: pdoc(X) => (val(1 /Int X) #Or val(2 /Int X)) [preserves-definedness]
  rule [pdod]: pdod(X) => (val(1 /Int X) #Or done) [preserves-definedness]
endmodule
"#;

    const Q5: &str = r#"
module MAIN
  imports INT
  imports BOOL
  syntax Pgm ::= "done" | val(Int) | w(Int)
               | pdg(Int) | npdg(Int) | pdg2(Int) | npdg2(Int) | pdg3(Int) | npdg3(Int)
               | pdx(Int) | npdx(Int)
  syntax Int ::= grow(Int) [function]
  configuration <k> $PGM:Pgm </k>
  rule grow(I) => grow(I +Int 1) [simplification]
  rule [pdg]:   pdg(X) => (w(grow(X)) #Or val(X /Int 0)) [preserves-definedness]
  rule [npdg]:  npdg(X) => (w(grow(X)) #Or val(X /Int 0))
  rule [pdg2]:  pdg2(X) => (val(X /Int 0) #Or w(grow(X))) [preserves-definedness]
  rule [npdg2]: npdg2(X) => (val(X /Int 0) #Or w(grow(X)))
  rule [pdg3]:  pdg3(X) => (val(X /Int 0) #Or val(1 /Int 0) #Or w(grow(X))) [preserves-definedness]
  rule [npdg3]: npdg3(X) => (val(X /Int 0) #Or val(1 /Int 0) #Or w(grow(X)))
  rule [pdx]:   pdx(X) => (w(grow(X)) #Or val(X /Int 0)) [preserves-definedness]
  rule [pdxo]:  pdx(_) => done
  rule [npdx]:  npdx(X) => (w(grow(X)) #Or val(X /Int 0))
  rule [npdxo]: npdx(_) => done
endmodule
"#;

    const Q6: &str = r#"
module MAIN
  imports INT
  imports BOOL
  syntax Pgm ::= "done" | val(Int) | "k0" | "k1" | "start"
  syntax Int ::= tb(Int) [function, total]
               | td(Int) [function, total]
  configuration <k> $PGM:Pgm </k>
  rule [tbeq]:  tb(I) => #Bottom requires I ==Int 0
  rule [tbeq2]: tb(I) => I requires I =/=Int 0
  rule [tdeq]:  td(I) => 10 /Int I
  rule [k0]: k0 => val(tb(0))
  rule [k1]: k1 => val(td(0))
  rule [st]: start => done
endmodule
"#;

    const Q7: &str = r#"
module MAIN
  imports INT
  imports BOOL
  imports STRING
  syntax Pgm ::= "done" | val(Int) | un(String) | un2(String)
  syntax Int ::= tb(Int) [function, total]
               | cntu(String, String) [function, total, hook(STRING.countAllOccurrences)]
               | cntv(String, String) [function, total, hook(STRING.countAllOccurrences)]
               | gu(Int) [function, total]
               | gv(Int) [function, total]
  configuration <k> $PGM:Pgm </k>
  rule [tbeq]:  tb(I) => #Bottom requires I ==Int 0
  rule [tbeq2]: tb(I) => I requires I =/=Int 0
  rule [cntu]:  cntu(S, "") => gu(cntu(S, ""))
  rule [gu1]:   gu(X) => X requires tb(0) >Int X
  rule [un]:    un(S) => val(cntu(S, ""))
  rule [cntv]:  cntv(S, "") => gv(cntv(S, ""))
  rule [gv1]:   gv(X) => X +Int tb(0)
  rule [un2]:   un2(S) => val(cntv(S, ""))
endmodule
"#;

    #[test]
    fn the_second_review_s_probes() {
        assert_inert(
            "q1",
            Q1,
            "MAIN",
            &[
                Ground("pd3(0)"),
                Ground("npd3(0)"),
                Ground("pd3b(0)"),
                Ground("pdn(0)"),
                Ground("npdn(0)"),
                Ground("pdi(0)"),
                Ground("npdi(0)"),
                Ground("pdm(0)"),
                Ground("npdm(0)"),
                Ground("pdb(0)"),
                Ground("npdb(0)"),
                Ground("pdc(0)"),
                Ground("npdc(0)"),
                Ground("pdc2(0)"),
            ],
        );
        assert_inert(
            "q3",
            Q3,
            "MAIN",
            &[
                Ground("pdw(0)"),
                Ground("npdw(0)"),
                Ground("pdw2(0)"),
                Ground("npdw2(0)"),
            ],
        );
        assert_inert(
            "q4",
            Q4,
            "MAIN",
            &[
                Ground("pdoc(0)"),
                Ground("pdod(0)"),
                Symbolic("pdoc(777)"),
                Symbolic("pdod(777)"),
            ],
        );
        assert_inert(
            "q5",
            Q5,
            "MAIN",
            &[
                Ground("pdg(0)"),
                Ground("npdg(0)"),
                Ground("pdg2(0)"),
                Ground("npdg2(0)"),
                Ground("pdg3(0)"),
                Ground("npdg3(0)"),
                Ground("pdx(0)"),
                Ground("npdx(0)"),
            ],
        );
        assert_inert(
            "q6",
            Q6,
            "MAIN",
            &[Ground("k0"), Ground("k1"), Ground("start")],
        );
        assert_inert(
            "q7",
            Q7,
            "MAIN",
            &[Ground("un(\"a\")"), Ground("un2(\"a\")")],
        );
    }

    // The probe definitions of code-reviews/KINK-18-3-fix2.toml: the chosen values and the
    // reuse are `derivations`'s; the `#Bottom` right-hand sides follow.

    const BOTTOMS: &str = r#"
module MAIN
  imports INT
  imports BOOL
  syntax Pgm ::= "done" | val(Int) | w(Int) | pdbn(Int) | pdbq(Int) | pdbr(Int) | go(Int) | pdo(Int)
               | pds(Int) | pdc(Int)
  syntax Int ::= q(Int) [function, total]
               | f(Int) [function, total]
  configuration <k> $PGM:Pgm </k>
  rule [feq]: f(X) => X +Int 1
  rule [pdbn]: pdbn(X) => #Bottom requires X ==Int 1 [preserves-definedness]
  rule [pdbq]: pdbq(X) => #Bottom requires q(X) ==Int 0 [preserves-definedness]
  rule [pdbr]: pdbr(X) => #Bottom requires X ==Int 0 [preserves-definedness]
  rule [pdbrb]: pdbr(_) => done
  rule [go]: go(X) => (w(f(X)) #Or done) [preserves-definedness]
  rule [w]: w(Y) => val(Y)
  rule [pdo]: pdo(X) => (val(X /Int 0) #Or val(f(X))) [preserves-definedness]
  rule [pdsa]: pds(X) => val(X /Int 0) [preserves-definedness]
  rule [pdsb]: pds(_) => done
  rule [pdc]: pdc(X) => val(10 /Int X) requires X <Int 1 [preserves-definedness]
  rule [pdc2]: pdc(X) => done requires X >=Int 1
endmodule
"#;

    #[test]
    fn the_third_review_s_probes() {
        assert_inert(
            "chosen",
            super::derivations::CHOSEN,
            "MAIN",
            &[
                Ground("ka(0)"),
                Ground("kb(0)"),
                Ground("ca(0)"),
                Ground("cb(0)"),
                Ground("pka(0)"),
                Ground("pkb(0)"),
                Ground("kr(0)"),
                Ground("ks(0)"),
                Ground("pkr(0)"),
                Ground("pks(0)"),
                Ground("karg(0)"),
            ],
        );
        assert_inert(
            "reuse",
            super::derivations::REUSE,
            "MAIN",
            &[Ground("un7(\"a\")"), Ground("un8(\"a\")")],
        );
        assert_inert(
            "bottoms",
            BOTTOMS,
            "MAIN",
            &[
                Ground("pdbn(0)"),
                Ground("pdbq(0)"),
                Ground("pdbr(0)"),
                Ground("go(0)"),
                Ground("pdo(0)"),
                Ground("pds(0)"),
                Ground("pdc(0)"),
                Symbolic("go(777)"),
                Symbolic("pdo(777)"),
                Symbolic("pdbr(777)"),
                Symbolic("pdc(777)"),
                Symbolic("pds(777)"),
                Constrained("pdbq(0)", 0),
                Constrained("pdbq(0)", 1),
            ],
        );
    }

    /// Claims of the fixtures' shapes, with their contradictions on the proof's path.
    const PROOF: &str = r#"
module MAIN
  imports INT
  imports BOOL
  imports MAP
  imports LIST
  imports K-EQUAL
  syntax Pgm ::= "done" | val(Int) | pd(Int) | pdt(Int) | tbt(Int) | pdb(Int) | pdo(Int) | bt(Int)
               | ka(Int)
  syntax Int ::= td(Int) [function, total]
               | tb(Int) [function, total]
               | bot(Int) [function]
               | tka(Int) [function, total]
  configuration <k> $PGM:Pgm </k>
  rule [tdeq]: td(I) => 10 /Int I
  rule [tbeq]: tb(I) => #Bottom requires I ==Int 0
  rule [tbeq2]: tb(I) => I requires I =/=Int 0
  rule [boteq]: bot(I) => #Bottom requires I ==Int 0
  rule [boteq2]: bot(I) => I requires I =/=Int 0
  rule [tkaeq]: tka(I) => 10 /Int (#if keys_list(1 |-> I 2 |-> I) ==K ListItem(1) ListItem(2) #then 0 #else 1 #fi)
  rule [pd]: pd(X) => val(X /Int 0) [preserves-definedness]
  rule [pdt]: pdt(X) => val(td(X)) [preserves-definedness]
  rule [tbt]: tbt(X) => val(tb(X))
  rule [pdb]: pdb(_) => #Bottom [preserves-definedness]
  rule [pdo]: pdo(X) => (val(X /Int 0) #Or done) [preserves-definedness]
  rule [bt]: bt(X) => val(bot(X)) [preserves-definedness]
  rule [ka]: ka(X) => val(tka(X))
  rule val(_) => done
endmodule

module MAIN-SPEC
  imports MAIN
  claim [c-pd]: <k> pd(0) => done </k>
  claim [c-pdt]: <k> pdt(0) => done </k>
  claim [c-tbt]: <k> tbt(0) => done </k>
  claim [c-pdb]: <k> pdb(0) => done </k>
  claim [c-pdo]: <k> pdo(0) => done </k>
  claim [c-bt]: <k> bt(0) => done </k>
  claim [c-ka]: <k> ka(0) => done </k>
  claim [c-pdx]: <k> pd(X) => done </k>
  claim [c-tbx]: <k> tbt(X) => done </k>
endmodule
"#;

    /// The compiled KORE of the spec module `spec` of `source`, its definition module `main`.
    fn compile_spec(source: &str, spec: &str, main: &str) -> String {
        use k_rust::{
            builtin::embedded,
            definition::CheckMode,
            kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
            outer::{LoadOptions, ResolvedSource, load_with_options},
        };
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new("spec.k", source),
            spec,
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![embedded("prelude.md").unwrap()],
                configuration_module: Some(main.to_owned()),
                ..CompilationBackend::Rust.load_options()
            },
        )
        .unwrap();
        compile_loaded_definition(
            &loaded,
            CompileOptions {
                backend: CompilationBackend::Rust,
                default_claims_to_all_path: true,
                check_mode: CheckMode::Proof {
                    definition_module: main.to_owned(),
                },
                ..CompileOptions::default()
            },
        )
        .unwrap()
        .definition_kore
    }

    /// The proof route: each claim proved with the checks on and off, with and without
    /// `allowVacuous`, of the definition and of its claim-free variant. A proof notes no record
    /// (`docs/compatibility.md`), so it does none of the work done only to find one: the
    /// responses and every counter are equal, claims or none.
    #[test]
    fn the_proof_route() {
        use k_rust::backend::ProveRequest;
        for source in [PROOF.to_owned(), strip(PROOF)] {
            let kore = compile_spec(&source, "MAIN-SPEC", "MAIN");
            for claim in [
                "c-pd", "c-pdt", "c-tbt", "c-pdb", "c-pdo", "c-bt", "c-ka", "c-pdx", "c-tbx",
            ] {
                for allow_vacuous in [false, true] {
                    let run = |checks| {
                        let kore = kore.clone();
                        let (response, counters) = counted(checks, move || {
                            let mut backend = backend_in(&kore, "MAIN-SPEC");
                            json(backend.prove(ProveRequest {
                                claim: Some(format!("MAIN-SPEC.{claim}")),
                                allow_vacuous,
                                ..ProveRequest::default()
                            }))
                        });
                        Outputs {
                            responses: vec![response],
                            counters,
                        }
                    };
                    let context = format!(
                        "{claim} (allowVacuous {allow_vacuous}, claims {})",
                        claims(&source)
                    );
                    let on = run(true);
                    let off = run(false);
                    assert_pair(&context, &on, &off, true);
                }
            }
        }
    }

    /// IMP of the K tutorial, which writes no claim attribute: the light corpus.
    const IMP: &str = include_str!("fixtures/kink/imp-lesson-4.k");

    #[test]
    fn the_light_imp_corpus() {
        assert_inert_in(
            Tier::Bounded,
            "IMP",
            IMP,
            "IMP",
            &[
                Ground(
                    "int n, sum; n = 3; sum = 0; while (!(n <= 0)) { sum = sum + n; n = n + -1; }",
                ),
                Ground(
                    "int i, m, n, q, r, s, t, x, y, z; m = 4; n = 2; \
                     while (n <= m) { i = 2; q = n/i; t = 1; \
                     while (i<=q && 1<=t) { x = i; y = q; z = 0; \
                     while (!(x <= 0)) { q = x/2; r = q + q + 1; if (r <= x) { z = z + y; } else {} \
                     x = q; y = y + y; } \
                     if (n <= z) { t = 0; } else { i = i + 1; q = n/i; } } \
                     if (1 <= t) { s = s + 1; } else {} n = n + 1; }",
                ),
                Ground("int a; a = 1 / 0;"),
                Ground("int a, b, c; a = 2 + 3; b = 7 / 2; c = -4;"),
                Ground(
                    "int a, b; if (1 <= 2 && 2 <= 1) { a = 1; } else { a = 2; } \
                     if (2 <= 1 && 1 <= 2) { b = 1; } else { b = 2; }",
                ),
            ],
        );
    }
}
