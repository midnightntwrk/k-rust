//! Symbolic execution covers its initial state, including the instances a step leaves without a
//! defined successor.
//!
//! An instance on which a rule applies (it matches and its `requires` holds) but whose result
//! is undefined (a false `ensures`, an undefined right-hand side) is not stuck, since the rule
//! blocks the lower priorities, and it is not on any successor's path. It is an undefined step,
//! reported as a `Trivial` leaf over the pre-step configuration, under the condition where no
//! applied candidate of the step's priority group has a defined result. The ground run of such
//! an instance ends `Trivial` too, so every symbolic leaf agrees with the ground runs of its
//! instances.

use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, ExecutionLeaf, ExecutionResult, ExecutionStrategy,
        HaltReasonOutput, ObservedRequest, PatternRequest, ResultModalityOutput,
    },
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::{codec, parser::parse_pattern, printer::Printer},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

const SOURCE: &str = r#"module UNDEF-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Prog ::= "halt" [symbol(halt)]
                | "done" [symbol(done)]
                | "fresh" [symbol(fresh)]
                | apart(Int, Int) [symbol(apart)]
                | stop(Int) [symbol(stop)]
                | val(Int) [symbol(val)]
                | pick(Int) [symbol(pick)]
                | over(Int) [symbol(over)]
                | half(Int) [symbol(half)]
                | guarded(Int, Int) [symbol(guarded)]
                | uselem(Int) [symbol(uselem)]
                | keep(Int) [symbol(keep)]
                | hz(Int) [symbol(hz)]
                | cmp(Int, Int) [symbol(cmp)]
                | cut(Int) [symbol(cut)]
                | sel(Int) [symbol(sel)]
                | low(Int) [symbol(low)]
  syntax Int ::= g(Int) [function, total, symbol(g)]
               | f(Int) [function, total, symbol(f)]
endmodule

module UNDEF
  imports UNDEF-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>

  rule [apart]:   <k> apart(A, B) => halt </k> ensures A =/=Int B
  rule [stop]:    <k> stop(I) => halt </k> ensures I <Int 0
  rule [fresh]:   <k> fresh => val(?X:Int) </k> ensures ?X >Int 0
  rule [pickpos]: <k> pick(I) => halt </k> requires I >Int 0 ensures false
  rule [pickneg]: <k> pick(I) => done </k> requires I <=Int 0
  rule [overbot]: <k> over(_) => halt </k> ensures false
  rule [overok]:  <k> over(_) => done </k>
  rule [half]:    <k> half(I) => val(10 /Int I) </k>
  rule [guarded]: <k> guarded(I1, I2) => val(I1 /Int I2) </k> requires I2 =/=Int 0
  rule [flem]:    f(X) => g(X) ensures g(X) >Int 0 [simplification]
  rule [uselem]:  <k> uselem(I) => val(f(I) /Int 2) </k>
  rule [keep]:    <k> keep(V) => val(V /Int 1) </k>
  rule [hz]:      <k> hz(I) => val(10 /Int I) </k> ensures I ==Int 0
  rule [cmpbot]:  <k> cmp(I, J) => halt </k> requires I >Int 0 andBool J >Int 0 ensures false
  rule [cmpok]:   <k> cmp(I, J) => done </k> requires I >Int 0 andBool J >Int 0
  rule [cutbot]:  <k> cut(_) => halt </k> ensures false
  rule [cutok]:   <k> cut(_) => done </k>
  rule [selpos]:  <k> sel(I) => halt </k> ensures I >Int 0
  rule [selany]:  <k> sel(_) => done </k>
  rule [lowpos]:  <k> low(I) => halt </k> ensures I >Int 0
  rule [lowow]:   <k> low(_) => done </k> [owise]
endmodule
"#;

const X: &str = "X:SortInt{}";
const Y: &str = "Y:SortInt{}";

fn backend() -> Backend {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("undef.k", SOURCE),
        "UNDEF",
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
    let compiled = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    Backend::new(
        &compiled.definition_kore,
        "UNDEF",
        BackendOptions::default(),
    )
    .unwrap()
}

fn top(program: &str) -> String {
    format!(
        "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortProg{{}}, SortKItem{{}}}}({program}), dotk{{}}())), Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\")))"
    )
}

fn int(value: i64) -> String {
    format!("\\dv{{SortInt{{}}}}(\"{value}\")")
}

fn request(program: &str) -> ExecuteRequest {
    ExecuteRequest {
        state: codec::to_value(&parse_pattern(&top(program)).unwrap()).unwrap(),
        result_modality: ResultModalityOutput::PathSet,
        ..ExecuteRequest::default()
    }
}

fn execute(backend: &mut Backend, program: &str) -> ExecutionResult {
    backend.execute(request(program)).unwrap()
}

fn text(leaf: &ExecutionLeaf) -> String {
    Printer::compact().print_pattern(&codec::from_value(&leaf.state).unwrap())
}

fn summary(result: &ExecutionResult) -> Vec<(HaltReasonOutput, u64, String)> {
    result
        .leaves
        .iter()
        .map(|leaf| (leaf.reason, leaf.depth, text(leaf)))
        .collect()
}

fn reasons(result: &ExecutionResult) -> Vec<HaltReasonOutput> {
    result.leaves.iter().map(|leaf| leaf.reason).collect()
}

fn trivial_leaves(result: &ExecutionResult) -> Vec<&ExecutionLeaf> {
    result
        .leaves
        .iter()
        .filter(|leaf| leaf.reason == HaltReasonOutput::Trivial)
        .collect()
}

/// The solver's verdict on a leaf's state (`sat`, `unsat` or `unknown`), with Z3 only.
fn satisfiable(backend: &mut Backend, leaf: &ExecutionLeaf) -> Option<String> {
    backend.capabilities().smt.then(|| {
        backend
            .get_model(PatternRequest {
                state: leaf.state.clone(),
                module_name: None,
                schema_version: k_rust::backend::BACKEND_SCHEMA_VERSION,
            })
            .unwrap()
            .satisfiable
    })
}

/// A leaf whose state is the pre-step configuration `program`, under a constraint.
fn is_pre_step(leaf: &ExecutionLeaf, program_head: &str) -> bool {
    text(leaf).contains(program_head)
}

#[test]
fn a_carried_ensures_leaves_its_violating_instances_a_trivial_leaf() {
    let mut backend = backend();
    let program = format!("Lblapart{{}}({X}, {Y})");
    let result = execute(&mut backend, &program);
    let mut found = reasons(&result);
    found.sort_by_key(|reason| format!("{reason:?}"));
    assert_eq!(
        found,
        [HaltReasonOutput::Stuck, HaltReasonOutput::Trivial],
        "{:#?}",
        summary(&result)
    );
    let stuck = result
        .leaves
        .iter()
        .find(|leaf| leaf.reason == HaltReasonOutput::Stuck)
        .unwrap();
    assert!(
        text(stuck).contains("Lblhalt{}()"),
        "{:#?}",
        summary(&result)
    );
    let [trivial] = trivial_leaves(&result)[..] else {
        panic!("one Trivial leaf: {:#?}", summary(&result));
    };
    // The undefined instances are the pre-step state under the negated `ensures`, `X = Y`.
    assert!(is_pre_step(trivial, "Lblapart{}(X:SortInt{}, Y:SortInt{})"));
    assert!(
        text(trivial)
            .ends_with(", \\equals{SortInt{}, SortGeneratedTopCell{}}(X:SortInt{}, Y:SortInt{}))"),
        "{:#?}",
        summary(&result)
    );
    if let Some(verdict) = satisfiable(&mut backend, trivial) {
        assert_eq!(verdict, "sat", "X = Y is an undefined instance");
    }
    // The leaf reports the step before its successors' leaves.
    assert_eq!(result.leaves[0].reason, HaltReasonOutput::Trivial);

    // Its instance agrees: the ground run of `apart(0, 0)` ends `Trivial`.
    let ground = execute(
        &mut backend,
        &format!("Lblapart{{}}({}, {})", int(0), int(0)),
    );
    assert_eq!(
        reasons(&ground),
        [HaltReasonOutput::Trivial],
        "{:#?}",
        summary(&ground)
    );
}

#[test]
fn observation_does_not_change_the_leaves_and_rolls_back_the_undefined_part() {
    let mut backend = backend();
    let program = format!("Lblapart{{}}({X}, {Y})");
    let plain = execute(&mut backend, &program);
    let observed = backend
        .execute_observed(ObservedRequest {
            request: request(&program),
            rules: None,
        })
        .unwrap();
    assert_eq!(
        summary(&plain),
        summary(&observed),
        "observation must not change the leaves"
    );
    let trivial = trivial_leaves(&observed);
    assert!(
        trivial.iter().all(|leaf| leaf.branch.is_empty()),
        "the undefined step commits no transition: {:#?}",
        summary(&observed)
    );
    assert!(
        !observed.discarded.is_empty(),
        "the undefined part of the application is rolled back"
    );
}

#[test]
fn a_symbolic_ensures_on_one_variable_splits_stuck_and_trivial() {
    let mut backend = backend();
    let result = execute(&mut backend, &format!("Lblstop{{}}({X})"));
    let mut found = reasons(&result);
    found.sort_by_key(|reason| format!("{reason:?}"));
    assert_eq!(
        found,
        [HaltReasonOutput::Stuck, HaltReasonOutput::Trivial],
        "{:#?}",
        summary(&result)
    );
    let [trivial] = trivial_leaves(&result)[..] else {
        panic!("one Trivial leaf: {:#?}", summary(&result));
    };
    assert!(is_pre_step(trivial, "Lblstop{}(X:SortInt{})"));
    if let Some(verdict) = satisfiable(&mut backend, trivial) {
        assert_eq!(verdict, "sat", "X >=Int 0 is an undefined instance");
    }
    let ground = execute(&mut backend, &format!("Lblstop{{}}({})", int(1)));
    assert_eq!(
        reasons(&ground),
        [HaltReasonOutput::Trivial],
        "{:#?}",
        summary(&ground)
    );
}

#[test]
fn an_ensures_on_a_fresh_variable_quantifies_it() {
    let mut backend = backend();
    let result = execute(&mut backend, "Lblfresh{}()");
    // The step is defined for every instance: some `?X >Int 0` exists. Any Trivial leaf must
    // quantify `?X`, so that its constraint has no instance.
    for trivial in trivial_leaves(&result) {
        let text = text(trivial);
        assert!(
            text.contains("\\not{") && text.contains("\\exists{"),
            "the fresh variable must be existentially quantified under the negation: {text}"
        );
        if let Some(verdict) = satisfiable(&mut backend, trivial) {
            assert_eq!(verdict, "unsat", "no instance is undefined: {text}");
        }
    }
    assert!(
        result
            .leaves
            .iter()
            .any(|leaf| leaf.reason == HaltReasonOutput::Stuck && text(leaf).contains("Lblval{}")),
        "{:#?}",
        summary(&result)
    );
}

#[test]
fn a_refuted_ensures_beside_a_disjoint_sibling_is_a_trivial_leaf() {
    let mut backend = backend();
    let result = execute(&mut backend, &format!("Lblpick{{}}({X})"));
    if !backend.capabilities().smt {
        // Without a solver, the symbolic `requires` is undecided.
        assert_eq!(
            reasons(&result),
            [HaltReasonOutput::Indeterminate],
            "{:#?}",
            summary(&result)
        );
    } else {
        let [trivial] = trivial_leaves(&result)[..] else {
            panic!("one Trivial leaf: {:#?}", summary(&result));
        };
        assert!(is_pre_step(trivial, "Lblpick{}(X:SortInt{})"));
        assert_eq!(satisfiable(&mut backend, trivial).as_deref(), Some("sat"));
        assert!(
            result
                .leaves
                .iter()
                .any(|leaf| leaf.reason == HaltReasonOutput::Stuck
                    && text(leaf).contains("Lbldone{}()")),
            "{:#?}",
            summary(&result)
        );
    }
    let ground = execute(&mut backend, &format!("Lblpick{{}}({})", int(1)));
    assert_eq!(
        reasons(&ground),
        [HaltReasonOutput::Trivial],
        "{:#?}",
        summary(&ground)
    );
    let ground = execute(&mut backend, &format!("Lblpick{{}}({})", int(0)));
    assert_eq!(
        reasons(&ground),
        [HaltReasonOutput::Stuck],
        "{:#?}",
        summary(&ground)
    );
}

#[test]
fn a_defined_sibling_covering_the_refuted_rule_leaves_no_trivial_leaf() {
    let mut backend = backend();
    for program in [
        format!("Lblover{{}}({X})"),
        format!("Lblover{{}}({})", int(3)),
    ] {
        let result = execute(&mut backend, &program);
        assert_eq!(
            reasons(&result),
            [HaltReasonOutput::Stuck],
            "{program}: {:#?}",
            summary(&result)
        );
        assert!(text(&result.leaves[0]).contains("Lbldone{}()"));
    }
}

#[test]
fn a_carried_right_hand_side_obligation_leaves_a_trivial_leaf() {
    let mut backend = backend();
    let result = execute(&mut backend, &format!("Lblhalf{{}}({X})"));
    let [trivial] = trivial_leaves(&result)[..] else {
        panic!("one Trivial leaf: {:#?}", summary(&result));
    };
    assert!(is_pre_step(trivial, "Lblhalf{}(X:SortInt{})"));
    if let Some(verdict) = satisfiable(&mut backend, trivial) {
        assert_eq!(verdict, "sat", "X = 0 is an undefined instance");
    }
    let ground = execute(&mut backend, &format!("Lblhalf{{}}({})", int(0)));
    assert_eq!(
        reasons(&ground),
        [HaltReasonOutput::Trivial],
        "{:#?}",
        summary(&ground)
    );
}

#[test]
fn a_discharged_right_hand_side_obligation_leaves_no_trivial_leaf() {
    let mut backend = backend();
    if !backend.capabilities().smt {
        return;
    }
    let result = execute(&mut backend, &format!("Lblguarded{{}}({X}, {Y})"));
    assert!(
        trivial_leaves(&result).is_empty(),
        "the requires discharges I2 =/=Int 0: {:#?}",
        summary(&result)
    );
    assert!(
        result
            .leaves
            .iter()
            .any(|leaf| text(leaf).contains("Lblval{}")),
        "{:#?}",
        summary(&result)
    );
}

/// A `[simplification]` lemma's `ensures` is an axiom of the definition, trusted wherever the
/// lemma applies: evaluating `f(I)` in the right-hand side to `g(I)` with the open `ensures
/// g(I) >Int 0` does not make the step undefined where that fails. The successor keeps it.
#[test]
fn a_simplification_lemmas_ensures_is_trusted_not_an_undefined_step() {
    let mut backend = backend();
    let result = execute(&mut backend, &format!("Lbluselem{{}}({X})"));
    assert_eq!(
        reasons(&result),
        [HaltReasonOutput::Stuck],
        "{:#?}",
        summary(&result)
    );
    assert!(
        text(&result.leaves[0]).contains("Lbl'Unds-GT-'Int'Unds'{}(Lblg{}(X:SortInt{})"),
        "the successor keeps the lemma's fact: {:#?}",
        summary(&result)
    );
}

/// With `assume_state_defined`, the initial state's partial subterm `10 /Int X` is defined, so
/// the right-hand side's obligation on it leaves no undefined instance.
#[test]
fn an_assumed_initial_definedness_leaves_no_undefined_step() {
    let mut backend = backend();
    let mut assumed = request(&format!(
        "Lblkeep{{}}(Lbl'UndsSlsh'Int'Unds'{{}}({}, {X}))",
        int(10)
    ));
    assumed.assume_state_defined = true;
    let result = backend.execute(assumed).unwrap();
    assert_eq!(
        reasons(&result),
        [HaltReasonOutput::Stuck],
        "{:#?}",
        summary(&result)
    );
}

/// Stopping at branches, a step whose one candidate carries its condition is no branch point:
/// it goes on as the step did before the undefined part was reported, and the candidate's
/// `\bottom` successor (`I = 0` makes `10 /Int I` undefined) is `Vacuous` one step later, never
/// a `Stuck` pre-step state. The `Trivial` leaf of the undefined part comes first.
#[test]
fn stopping_at_branches_a_carried_step_goes_on_as_one_successor() {
    let mut backend = backend();
    let mut stopped = request(&format!("Lblhz{{}}({X})"));
    stopped.stop_at_branch = true;
    let result = backend.execute(stopped).unwrap();
    assert_eq!(
        result
            .leaves
            .iter()
            .map(|leaf| (leaf.reason, leaf.depth))
            .collect::<Vec<_>>(),
        [
            (HaltReasonOutput::Trivial, 0),
            (HaltReasonOutput::Vacuous, 1)
        ],
        "{:#?}",
        summary(&result)
    );
}

/// An overlapping pair with a compound applicability: `cmpok` takes every instance `cmpbot`
/// rewrites to bottom, `not (X > 0 /\ Y > 0)` beside both conjuncts folds to `\bottom`, and
/// no undefined step is reported.
#[test]
fn a_defined_sibling_with_a_compound_applicability_leaves_no_trivial_leaf() {
    let mut backend = backend();
    let result = execute(&mut backend, &format!("Lblcmp{{}}({X}, {Y})"));
    assert!(
        trivial_leaves(&result).is_empty(),
        "{:#?}",
        summary(&result)
    );
    if backend.capabilities().smt {
        assert!(
            result
                .leaves
                .iter()
                .any(|leaf| text(leaf).contains("Lbldone{}()")),
            "{:#?}",
            summary(&result)
        );
    }
}

/// Exploring all paths, a step with one applied candidate beside a refuted sibling has one
/// successor, as a `Finished` step does, so the stop rules apply to it alike: `cutok` as a
/// cut point stops at the pre-step state, and as a terminal rule stops at its successor.
#[test]
fn stop_rules_apply_to_a_one_candidate_step_beside_a_refuted_sibling() {
    let mut backend = backend();
    for program in [
        format!("Lblcut{{}}({X})"),
        format!("Lblcut{{}}({})", int(3)),
    ] {
        let mut cut = request(&program);
        cut.cut_point_rules = vec!["UNDEF.cutok".into()];
        let result = backend.execute(cut).unwrap();
        assert_eq!(
            result
                .leaves
                .iter()
                .map(|leaf| (leaf.reason, leaf.depth))
                .collect::<Vec<_>>(),
            [(HaltReasonOutput::CutPoint, 0)],
            "{program}: {:#?}",
            summary(&result)
        );
        let mut terminal = request(&program);
        terminal.terminal_rules = vec!["UNDEF.cutok".into()];
        let result = backend.execute(terminal).unwrap();
        assert_eq!(
            result
                .leaves
                .iter()
                .map(|leaf| (leaf.reason, leaf.depth))
                .collect::<Vec<_>>(),
            [(HaltReasonOutput::Terminal, 1)],
            "{program}: {:#?}",
            summary(&result)
        );
    }
}

/// Strategy `any` offers the instances where a rule applies but its result is undefined to the
/// later rules of the same priority. `selpos` is tried first; `selany` takes its instances
/// `not (X > 0)`, so neither strategy reports a `Trivial` leaf, and both reach `halt` and `done`.
/// A ground instance agrees: `sel(0)` reaches `done` under `any`.
#[test]
fn under_strategy_any_a_later_rule_of_the_priority_takes_the_undefined_instances() {
    let mut backend = backend();
    let program = format!("Lblsel{{}}({X})");
    let all = execute(&mut backend, &program);
    assert!(trivial_leaves(&all).is_empty(), "{:#?}", summary(&all));
    let mut any = request(&program);
    any.strategy = ExecutionStrategy::Any;
    let any = backend.execute(any).unwrap();
    assert!(trivial_leaves(&any).is_empty(), "{:#?}", summary(&any));
    for result in [&all, &any] {
        let mut ends = result
            .leaves
            .iter()
            .map(|leaf| {
                (
                    leaf.reason,
                    text(leaf).contains("Lblhalt{}()"),
                    text(leaf).contains("Lbldone{}()"),
                )
            })
            .collect::<Vec<_>>();
        ends.sort_by_key(|end| format!("{end:?}"));
        assert_eq!(
            ends,
            [
                (HaltReasonOutput::Stuck, false, true),
                (HaltReasonOutput::Stuck, true, false),
            ],
            "{:#?}",
            summary(result)
        );
    }

    let mut ground = request(&format!("Lblsel{{}}({})", int(0)));
    ground.strategy = ExecutionStrategy::Any;
    let ground = backend.execute(ground).unwrap();
    assert_eq!(
        reasons(&ground),
        [HaltReasonOutput::Stuck],
        "{:#?}",
        summary(&ground)
    );
    assert!(
        text(&ground.leaves[0]).contains("Lbldone{}()"),
        "{:#?}",
        summary(&ground)
    );
}

/// An instance where a rule applies but its result is undefined blocks the lower priorities
/// under both strategies: `low(X)` under `not (X > 0)` is an undefined step, never `lowow`'s
/// `done`.
#[test]
fn an_undefined_instance_is_not_offered_to_a_lower_priority() {
    let mut backend = backend();
    for strategy in [ExecutionStrategy::All, ExecutionStrategy::Any] {
        let mut symbolic = request(&format!("Lbllow{{}}({X})"));
        symbolic.strategy = strategy;
        let result = backend.execute(symbolic).unwrap();
        let mut found = reasons(&result);
        found.sort_by_key(|reason| format!("{reason:?}"));
        assert_eq!(
            found,
            [HaltReasonOutput::Stuck, HaltReasonOutput::Trivial],
            "{strategy:?}: {:#?}",
            summary(&result)
        );
        assert!(
            result
                .leaves
                .iter()
                .all(|leaf| !text(leaf).contains("Lbldone{}()")),
            "{strategy:?}: {:#?}",
            summary(&result)
        );

        let mut ground = request(&format!("Lbllow{{}}({})", int(0)));
        ground.strategy = strategy;
        let ground = backend.execute(ground).unwrap();
        assert_eq!(
            reasons(&ground),
            [HaltReasonOutput::Trivial],
            "{strategy:?}: {:#?}",
            summary(&ground)
        );
    }
}
