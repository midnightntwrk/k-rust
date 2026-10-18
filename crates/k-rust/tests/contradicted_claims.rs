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
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new("claims.k", source),
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
        let mut assembler = ConfigurationAssembler::new(
            &grammar,
            "MAIN",
            "MAIN",
            &artifacts.configuration_variables,
        );
        assembler.program(&Sort::new("Pgm"), program).unwrap();
        (artifacts.definition_kore, assembler.finish().unwrap())
    }

    pub(super) fn backend(kore: &str) -> Backend {
        Backend::new(kore, "MAIN", BackendOptions::default()).unwrap()
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
    const REFUSALS: &str = r#"
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

/// `krun`'s warning says what a record shows. A ground record is a refutation of the claim at
/// that input, so the definition is inconsistent there; a non-ground one (`rz(X)`, through
/// `tz(_) => 10 /Int 0`) holds at each instance of a state that may have none, so it is worded as
/// contradicted only. A record of the load says so.
#[test]
fn the_warning_says_what_a_record_shows() {
    use k_rust::backend::execution::contradicted_claim_message;
    use k_rust_backend::{rewrite::execute_with_solver, smt::NoSolver};
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
