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

use k_rust_kore::measure::{self, Counter};

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

#[path = "support/shared.rs"]
mod shared;
#[path = "support/undefined_successor.rs"]
mod undefined_successor;

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
                | tdiv(Int) [symbol(tdiv)]
                | tdarg(Int) [symbol(tdarg)]
                | pdup(Int) [symbol(pdup)]
                | mapv(Map) [symbol(mapv)]
                | sib(Int) [symbol(sib)]
                | sibr(Int) [symbol(sibr)]
                | bis(Int) [symbol(bis)]
                | s3(Int) [symbol(s3)]
                | w(Int) [symbol(w)]
                | rem(Int, Int) [symbol(rem)]
                | rem2(Int, Int) [symbol(rem2)]
                | cnt(Int, Int) [symbol(cnt)]
  syntax Int ::= g(Int) [function, total, symbol(g)]
               | f(Int) [function, total, symbol(f)]
               | td(Int) [function, total, symbol(td)]
               | f2(Int) [function, total, symbol(f2)]
               | fib(Int) [function, total, symbol(fib)]
  syntax Map ::= dup(Int) [function, total, symbol(dup)]
endmodule

module UNDEF
  imports UNDEF-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports MAP
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
  rule [tdeq]:    td(I) => 10 /Int I
  rule [tdiv]:    <k> tdiv(I) => val(td(I)) </k>
  rule [tdarg]:   <k> tdarg(I) => val(td(10 /Int I)) </k>
  rule [dupeq]:   dup(I) => (I |-> 1) (I |-> 2)
  rule [pdup]:    <k> pdup(I) => mapv(dup(I)) </k>
  rule [sibtd]:   <k> sib(_) => val(td(0)) </k>
  rule [sibok]:   <k> sib(_) => done </k>
  rule [sibrtd]:  <k> sibr(_) => val(td(0)) </k>
  rule [sibrok]:  <k> sibr(I) => done </k> requires I >Int 0
  rule [bisok]:   <k> bis(_) => done </k>
  rule [bistd]:   <k> bis(_) => val(td(0)) </k>
  rule [s3a]:     <k> s3(I) => val(td(I)) </k> requires I ==Int 0
  rule [s3b]:     <k> s3(I) => w(td(I)) </k> requires I ==Int 0
  rule [f2pos]:   f2(I) => 1 requires I >Int 0
  rule [f2neg]:   f2(I) => 2 requires I <=Int 0
  rule [remhi]:   <k> rem(X, _) => done </k> requires X >Int 0 [priority(10)]
  rule [remlo]:   <k> rem(_, J) => val(td(J -Int 2)) </k> [priority(50)]
  rule [rem2hi]:  <k> rem2(X, _) => done </k> requires X >Int 0 [priority(10)]
  rule [rem2lo]:  <k> rem2(_, J) => val(10 /Int (J -Int 2)) </k> [priority(50)]
  rule [fibbase]: fib(N) => N requires N <Int 2
  rule [fibrec]:  fib(N) => fib(N -Int 1) +Int fib(N -Int 2) requires N >=Int 2
  rule [cntstep]: <k> cnt(N, A) => cnt(N -Int 1, A +Int fib(8)) </k> requires N >Int 0
  rule [cntdone]: <k> cnt(N, A) => val(A) </k> requires N <=Int 0
endmodule
"#;

const X: &str = "X:SortInt{}";
const Y: &str = "Y:SortInt{}";

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
    compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap()
        .definition_kore
}

/// A fresh backend over the shared definition, so no test observes another's backend state.
fn backend() -> Backend {
    Backend::new(&definition_kore(), "UNDEF", BackendOptions::default()).unwrap()
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
        result_modality: ResultModalityOutput::PathSet,
        ..ExecuteRequest::new(parse_pattern(&top(program)).unwrap())
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

fn assert_trivial_rule(backend: &Backend, leaf: &ExecutionLeaf, label: &str) {
    let compiled_label = format!("UNDEF.{label}");
    let catalog = backend.rule_catalog(None).unwrap();
    let rule = catalog
        .iter()
        .find(|rule| rule.label.as_deref() == Some(compiled_label.as_str()))
        .unwrap();
    assert_eq!(leaf.rule_id.as_deref(), Some(rule.id.as_str()));
    assert_eq!(leaf.rule_label.as_deref(), Some(compiled_label.as_str()));
    assert_eq!(leaf.detail, None);
    let wire = serde_json::to_value(leaf).unwrap();
    assert_eq!(wire["ruleId"], rule.id);
    assert_eq!(wire["ruleLabel"], compiled_label);
    let decoded: ExecutionLeaf = serde_json::from_value(wire.clone()).unwrap();
    assert_eq!(serde_json::to_value(decoded).unwrap(), wire);
}

/// The solver's verdict on a leaf's state (`sat`, `unsat` or `unknown`), with Z3 only.
fn satisfiable(backend: &mut Backend, leaf: &ExecutionLeaf) -> Option<String> {
    backend.capabilities().smt.then(|| {
        backend
            .get_model(PatternRequest::new(codec::from_value(&leaf.state).unwrap()))
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
    assert_trivial_rule(&backend, trivial, "apart");
    assert!(stuck.rule_id.is_none() && stuck.rule_label.is_none());
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
    assert_trivial_rule(&backend, &ground.leaves[0], "apart");
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
        assert_trivial_rule(&backend, trivial, "pickpos");
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
    assert_trivial_rule(&backend, &ground.leaves[0], "pickpos");
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
/// it goes on as the step did before the undefined part was reported. The candidate's successor
/// (`I = 0` makes `10 /Int I` undefined) normalizes to `\bottom`, so it is no successor, never a
/// `Stuck` pre-step state nor a `Vacuous` state one step later: every instance of `hz(X)` is on
/// the undefined step's `Trivial` leaf, the one leaf.
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
        [(HaltReasonOutput::Trivial, 0)],
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
        // The undefined step is `lowpos`'s under either strategy, and the leaf names it.
        let [trivial] = trivial_leaves(&result)[..] else {
            panic!("{strategy:?}: one Trivial leaf: {:#?}", summary(&result));
        };
        assert_trivial_rule(&backend, trivial, "lowpos");

        let mut ground = request(&format!("Lbllow{{}}({})", int(0)));
        ground.strategy = strategy;
        let ground = backend.execute(ground).unwrap();
        assert_eq!(
            reasons(&ground),
            [HaltReasonOutput::Trivial],
            "{strategy:?}: {:#?}",
            summary(&ground)
        );
        assert_trivial_rule(&backend, &ground.leaves[0], "lowpos");
    }
}

/// `td` is declared `total`, but its equation divides by its argument, so `td(0)` is bottom: the
/// definition contradicts the attribute there. The ground run ends in an undefined step, as it
/// does without the attribute, and the leaf names the symbol, the equation, the application and
/// the undefined term in `contradictedTotal`. The symbolic run observes no bottom (the attribute
/// is trusted, so `td(X)` is defined) and reports nothing: the diagnostic changes no leaf.
#[test]
fn a_ground_undefined_step_through_a_total_function_names_the_contradicted_attribute() {
    let mut backend = backend();
    let ground = execute(&mut backend, &format!("Lbltdiv{{}}({})", int(0)));
    assert_eq!(
        reasons(&ground),
        [HaltReasonOutput::Trivial],
        "{:#?}",
        summary(&ground)
    );
    assert_trivial_rule(&backend, &ground.leaves[0], "tdiv");
    // The step is undefined on the configuration it was taken from: the leaf is that
    // configuration, before the step, not the empty successor.
    assert_eq!(
        (ground.leaves[0].depth, text(&ground.leaves[0])),
        (0, top(&format!("Lbltdiv{{}}({})", int(0)))),
        "{:#?}",
        summary(&ground)
    );
    let contradicted = ground.leaves[0]
        .contradicted_total
        .as_ref()
        .expect("the leaf names the contradicted attribute");
    let catalog = backend.rule_catalog(None).unwrap();
    let equation = catalog
        .iter()
        .find(|rule| rule.label.as_deref() == Some("UNDEF.tdeq"))
        .unwrap();
    assert_eq!(contradicted.symbol, "Lbltd");
    assert_eq!(contradicted.k_label.as_deref(), Some("td"));
    assert_eq!(contradicted.rule_id, equation.id);
    assert_eq!(contradicted.rule_label.as_deref(), Some("UNDEF.tdeq"));
    assert_eq!(contradicted.origin.as_ref(), equation.origins.first());
    let kore = |value: &serde_json::Value| {
        Printer::compact().print_pattern(&codec::from_value(value).unwrap())
    };
    assert_eq!(
        kore(&contradicted.application),
        format!("Lbltd{{}}({})", int(0))
    );
    assert_eq!(
        kore(&contradicted.undefined),
        format!("Lbl'UndsSlsh'Int'Unds'{{}}({}, {})", int(10), int(0))
    );
    let wire = serde_json::to_value(&ground.leaves[0]).unwrap();
    assert_eq!(wire["contradictedTotal"]["ruleLabel"], "UNDEF.tdeq");
    assert_eq!(wire["contradictedTotal"]["kLabel"], "td");
    // The halt's cause is also the leaf's path fact, naming the step's rule, and the run's.
    assert_eq!(
        contradicted_claims(&wire),
        [(
            "td".to_owned(),
            "UNDEF.tdeq".to_owned(),
            Some("UNDEF.tdiv".to_owned()),
            true
        )],
        "{wire:#}"
    );
    let run = serde_json::to_value(&ground).unwrap();
    assert_eq!(
        run["contradictedClaims"].as_array().map(Vec::len),
        Some(1),
        "{run:#}"
    );
    let decoded: ExecutionLeaf = serde_json::from_value(wire.clone()).unwrap();
    assert_eq!(serde_json::to_value(decoded).unwrap(), wire);

    let symbolic = execute(&mut backend, &format!("Lbltdiv{{}}({X})"));
    assert!(
        symbolic
            .leaves
            .iter()
            .all(|leaf| leaf.reason != HaltReasonOutput::Trivial
                && leaf.contradicted_total.is_none()),
        "{:#?}",
        summary(&symbolic)
    );
    assert!(
        symbolic
            .leaves
            .iter()
            .all(|leaf| contradicted_claims(&serde_json::to_value(leaf).unwrap()).is_empty())
            && serde_json::to_value(&symbolic).unwrap()["contradictedClaims"].is_null(),
        "{:#?}",
        summary(&symbolic)
    );
    // An argument that is bottom before the equation fires is not the equation's doing: the
    // step is undefined, and no attribute is named.
    let argument = execute(&mut backend, &format!("Lbltdarg{{}}({})", int(0)));
    assert_eq!(
        reasons(&argument),
        [HaltReasonOutput::Trivial],
        "{:#?}",
        summary(&argument)
    );
    assert!(argument.leaves[0].contradicted_total.is_none());
    assert!(
        contradicted_claims(&serde_json::to_value(&argument.leaves[0]).unwrap()).is_empty()
            && serde_json::to_value(&argument).unwrap()["contradictedClaims"].is_null()
    );
}

/// The `contradicted-claim` path facts among a leaf's diagnostics (wire form): the symbol's K
/// label, the equation's label, the rewrite rule's label and whether the application is ground.
fn contradicted_claims(leaf: &serde_json::Value) -> Vec<(String, String, Option<String>, bool)> {
    leaf["diagnostics"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|diagnostic| diagnostic["kind"] == "contradicted-claim")
        .map(|diagnostic| {
            (
                diagnostic["kLabel"].as_str().unwrap_or("?").to_owned(),
                diagnostic["ruleLabel"].as_str().unwrap_or("?").to_owned(),
                diagnostic["rewriteRuleLabel"].as_str().map(str::to_owned),
                diagnostic["ground"].as_bool().unwrap_or(false),
            )
        })
        .collect()
}

/// `dup(1)` is declared `total`, but its equation builds `(1 |-> 1) (1 |-> 2)`, a map with a
/// repeated key, which is bottom. The step `pdup(1) => mapv(dup(1))` is therefore undefined on
/// `pdup(1)`, a defined configuration: its leaf is `pdup(1)` itself at depth 0, as for an
/// undefined right-hand side the step detects, and it names the contradicted attribute.
#[test]
fn a_repeated_key_built_by_a_total_function_is_a_trivial_step_of_the_pre_step_configuration() {
    let mut backend = backend();
    for strategy in [ExecutionStrategy::All, ExecutionStrategy::Any] {
        let mut ground = request(&format!("Lblpdup{{}}({})", int(1)));
        ground.strategy = strategy;
        let ground = backend.execute(ground).unwrap();
        assert_eq!(
            reasons(&ground),
            [HaltReasonOutput::Trivial],
            "{strategy:?}: {:#?}",
            summary(&ground)
        );
        assert_trivial_rule(&backend, &ground.leaves[0], "pdup");
        assert_eq!(
            (ground.leaves[0].depth, text(&ground.leaves[0])),
            (0, top(&format!("Lblpdup{{}}({})", int(1)))),
            "{strategy:?}: {:#?}",
            summary(&ground)
        );
        assert!(
            ground.leaves[0].contradicted_total.is_some(),
            "{strategy:?}: {:#?}",
            summary(&ground)
        );
        let wire = serde_json::to_value(&ground.leaves[0]).unwrap();
        assert_eq!(
            contradicted_claims(&wire),
            [(
                "dup".to_owned(),
                "UNDEF.dupeq".to_owned(),
                Some("UNDEF.pdup".to_owned()),
                true
            )],
            "{strategy:?}: {wire:#}"
        );
    }
}

/// Two rules of one priority apply to `sib(I)`: `sibtd`'s result `val(td(0))` is bottom (a
/// contradicted `total`), found only when its successor is normalized, and `sibok` gives
/// `done`. Every instance has a defined successor, so there is no undefined step and no
/// `Trivial` leaf. When `sibok` applies only where `I >Int 0` (`sibr`), the instances where it
/// does not are an undefined step of `sibr(I)`, and only those.
#[test]
fn an_undefined_successor_found_after_the_step_is_trivial_only_where_no_sibling_is_defined() {
    let mut backend = backend();
    for program in [
        format!("Lblsib{{}}({X})"),
        format!("Lblsib{{}}({})", int(0)),
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
    let ground = execute(&mut backend, &format!("Lblsibr{{}}({})", int(1)));
    assert_eq!(
        reasons(&ground),
        [HaltReasonOutput::Stuck],
        "{:#?}",
        summary(&ground)
    );
    let ground = execute(&mut backend, &format!("Lblsibr{{}}({})", int(0)));
    assert_eq!(
        summary(&ground),
        [(
            HaltReasonOutput::Trivial,
            0,
            top(&format!("Lblsibr{{}}({})", int(0)))
        )],
    );
    assert_trivial_rule(&backend, &ground.leaves[0], "sibrtd");
    if !backend.capabilities().smt {
        return;
    }
    let symbolic = execute(&mut backend, &format!("Lblsibr{{}}({X})"));
    let [trivial] = trivial_leaves(&symbolic)[..] else {
        panic!("one Trivial leaf: {:#?}", summary(&symbolic));
    };
    assert_eq!(trivial.depth, 0, "{:#?}", summary(&symbolic));
    assert!(is_pre_step(trivial, "Lblsibr{}(X:SortInt{})"));
    // Its instances are those where `sibrok` does not apply.
    let excluded = format!(
        "\\equals{{SortBool{{}}, SortGeneratedTopCell{{}}}}(\\dv{{SortBool{{}}}}(\"true\"), Lbl'Unds-GT-'Int'Unds'{{}}({X}, {}))",
        int(0)
    );
    assert!(
        text(trivial).contains(&format!("\\not{{SortGeneratedTopCell{{}}}}({excluded})")),
        "{:#?}",
        summary(&symbolic)
    );
    assert!(
        symbolic.leaves.iter().any(
            |leaf| leaf.reason == HaltReasonOutput::Stuck && text(leaf).contains("Lbldone{}()")
        ),
        "{:#?}",
        summary(&symbolic)
    );
}

fn request_with(program: &str, configure: impl FnOnce(&mut ExecuteRequest)) -> ExecuteRequest {
    let mut request = request(program);
    configure(&mut request);
    request
}

/// The leaves of `request`, with their observations, after checking that observing the run
/// changes no leaf's state, depth, reason, rule or trace.
fn execute_both(backend: &mut Backend, request: ExecuteRequest) -> ExecutionResult {
    let plain = backend.execute(request.clone()).unwrap();
    let observed = backend
        .execute_observed(ObservedRequest {
            request,
            rules: None,
        })
        .unwrap();
    let key = |result: &ExecutionResult| {
        result
            .leaves
            .iter()
            .map(|leaf| {
                (
                    leaf.reason,
                    leaf.depth,
                    text(leaf),
                    leaf.rule_label.clone(),
                    leaf.trace.clone(),
                )
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(
        key(&plain),
        key(&observed),
        "observation must not change the leaves"
    );
    observed
}

/// Under strategy `any` the step commits to the first rule of a priority that gives an instance
/// a defined result, so it decides there whether a candidate's result is undefined, also when
/// only the successor's normalization shows it (a contradicted `total`). `sibtd` is tried before
/// `sibok` on `sib(0)`, `bisok` before `bistd` on `bis(0)`: in either order `done` is reached and
/// no undefined step is reported. On `sibr(I)` the instances where `sibrok` does not apply are
/// the undefined step, and only those.
#[test]
fn under_strategy_any_a_candidate_undefined_after_the_step_leaves_its_instances_to_later_rules() {
    let mut backend = backend();
    let any = |request: &mut ExecuteRequest| request.strategy = ExecutionStrategy::Any;
    for program in [
        format!("Lblsib{{}}({})", int(0)),
        format!("Lblbis{{}}({})", int(0)),
        format!("Lblsib{{}}({X})"),
        format!("Lblsibr{{}}({})", int(1)),
    ] {
        let result = execute_both(&mut backend, request_with(&program, any));
        assert_eq!(
            summary(&result)
                .into_iter()
                .map(|(reason, depth, state)| (reason, depth, state.contains("Lbldone{}()")))
                .collect::<Vec<_>>(),
            [(HaltReasonOutput::Stuck, 1, true)],
            "{program}: {:#?}",
            summary(&result)
        );
    }
    let ground = execute_both(
        &mut backend,
        request_with(&format!("Lblsibr{{}}({})", int(0)), any),
    );
    assert_eq!(
        summary(&ground),
        [(
            HaltReasonOutput::Trivial,
            0,
            top(&format!("Lblsibr{{}}({})", int(0)))
        )],
    );
    assert_trivial_rule(&backend, &ground.leaves[0], "sibrtd");
    assert!(ground.leaves[0].contradicted_total.is_some());
    if !backend.capabilities().smt {
        return;
    }
    let symbolic = execute_both(
        &mut backend,
        request_with(&format!("Lblsibr{{}}({X})"), any),
    );
    assert_sibr_symbolic(&backend, &symbolic);
}

/// The symbolic `sibr(X)` run: one `Trivial` leaf of `sibrtd` over `sibr(X)` at depth 0 under
/// `not (X >Int 0)`, the instances where `sibrok` does not apply, and `done` beside it.
fn assert_sibr_symbolic(backend: &Backend, result: &ExecutionResult) {
    let [trivial] = trivial_leaves(result)[..] else {
        panic!("one Trivial leaf: {:#?}", summary(result));
    };
    assert_eq!(trivial.depth, 0, "{:#?}", summary(result));
    assert!(is_pre_step(trivial, "Lblsibr{}(X:SortInt{})"));
    assert_trivial_rule(backend, trivial, "sibrtd");
    let excluded = format!(
        "\\equals{{SortBool{{}}, SortGeneratedTopCell{{}}}}(\\dv{{SortBool{{}}}}(\"true\"), Lbl'Unds-GT-'Int'Unds'{{}}({X}, {}))",
        int(0)
    );
    assert!(
        text(trivial).contains(&format!("\\not{{SortGeneratedTopCell{{}}}}({excluded})")),
        "{:#?}",
        summary(result)
    );
    assert!(
        result.leaves.iter().any(
            |leaf| leaf.reason == HaltReasonOutput::Stuck && text(leaf).contains("Lbldone{}()")
        ),
        "{:#?}",
        summary(result)
    );
}

/// Without a solver the step on `sibr(X)` cannot decide `sibrok`'s condition, so the run ends
/// `Indeterminate` at the pre-step state and claims no undefined step; with Z3 it is the
/// undefined step of the instances `not (X >Int 0)`. Observing the run changes no leaf.
#[test]
fn a_symbolic_post_step_undefined_candidate_beside_a_conditional_sibling() {
    let mut backend = backend();
    let result = execute_both(&mut backend, request(&format!("Lblsibr{{}}({X})")));
    if backend.capabilities().smt {
        assert_sibr_symbolic(&backend, &result);
    } else {
        assert_eq!(
            reasons(&result),
            [HaltReasonOutput::Indeterminate],
            "{:#?}",
            summary(&result)
        );
        assert_eq!(result.leaves[0].depth, 0);
    }
}

/// Stopping at branches, the candidates of a step are normalized in the step. One normalized to
/// `\bottom` with an undefined result is an undefined step of the pre-step state where no defined
/// candidate applies, not a dropped candidate: `sibr(X)` reports the instances `not (X >Int 0)`,
/// and `s3(0)`, whose two candidates are both undefined, ends in the one `Trivial` leaf of its
/// undefined step at depth 0, naming the first candidate and resting on both, rather than
/// `Stuck`. Without its undefined sibling the defined candidate is the state's
/// unique successor, so the stop rules apply to it: `sib(0)` stops at the cut point `sibok`
/// before the step, or at the terminal rule `sibok` after it. Under strategy `any` the step
/// itself drops `sibtd` there, with or without stopping at branches.
#[test]
fn stopping_at_branches_reports_a_candidate_undefined_after_the_step() {
    let mut backend = backend();
    let stop = |request: &mut ExecuteRequest| request.stop_at_branch = true;
    let both = execute_both(
        &mut backend,
        request_with(&format!("Lbls3{{}}({})", int(0)), stop),
    );
    assert_eq!(
        reasons(&both),
        [HaltReasonOutput::Trivial],
        "{:#?}",
        summary(&both)
    );
    assert!(both.leaves.iter().all(|leaf| leaf.depth == 0
        && text(leaf) == top(&format!("Lbls3{{}}({})", int(0)))
        && leaf.contradicted_total.is_some()
        && leaf.branch.is_empty()));
    assert_trivial_rule(&backend, &both.leaves[0], "s3a");
    assert_eq!(both.discarded.len(), 2, "both transitions are rolled back");

    for strategy in [ExecutionStrategy::All, ExecutionStrategy::Any] {
        let mut cut = request(&format!("Lblsib{{}}({})", int(0)));
        cut.stop_at_branch = true;
        cut.strategy = strategy;
        cut.cut_point_rules = vec!["UNDEF.sibok".into()];
        let result = execute_both(&mut backend, cut);
        assert_eq!(
            summary(&result),
            [(
                HaltReasonOutput::CutPoint,
                0,
                top(&format!("Lblsib{{}}({})", int(0)))
            )],
            "{strategy:?}"
        );
        let mut terminal = request(&format!("Lblsib{{}}({})", int(0)));
        terminal.stop_at_branch = true;
        terminal.strategy = strategy;
        terminal.terminal_rules = vec!["UNDEF.sibok".into()];
        let result = execute_both(&mut backend, terminal);
        assert_eq!(
            reasons(&result),
            [HaltReasonOutput::Terminal],
            "{strategy:?}: {:#?}",
            summary(&result)
        );
        assert_eq!(result.leaves[0].depth, 1);
    }
    // Under `any` the step drops `sibtd`, so the stop rules apply exploring all paths too.
    let mut cut = request(&format!("Lblsib{{}}({})", int(0)));
    cut.strategy = ExecutionStrategy::Any;
    cut.cut_point_rules = vec!["UNDEF.sibok".into()];
    assert_eq!(
        reasons(&backend.execute(cut).unwrap()),
        [HaltReasonOutput::CutPoint]
    );

    if !backend.capabilities().smt {
        return;
    }
    let symbolic = execute_both(
        &mut backend,
        request_with(&format!("Lblsibr{{}}({X})"), stop),
    );
    assert_sibr_symbolic(&backend, &symbolic);
}

/// Two candidates of one step, `s3a` and `s3b`, are both undefined only after the step, where
/// `I ==Int 0`. The step has one undefined step, of `s3(X)` under `X = 0`, under either strategy
/// and whether or not the run stops at branches, and the other instances are the stuck
/// remainder: no instance is lost. Exploring all paths, the first of its successors to be
/// expanded reports it, naming the first candidate, and the other reports none. Strategy `any`'s
/// step finds `s3a` undefined and offers its instances to `s3b`, the priority's last rule,
/// whose successor's normalization then reports the undefined step, naming `s3b`.
#[test]
fn two_candidates_undefined_after_the_step_are_one_undefined_step() {
    let mut backend = backend();
    for (strategy, leaves, rule) in [
        (ExecutionStrategy::All, 1, "s3a"),
        (ExecutionStrategy::Any, 1, "s3b"),
    ] {
        let ground = execute_both(
            &mut backend,
            request_with(&format!("Lbls3{{}}({})", int(0)), |request| {
                request.strategy = strategy;
            }),
        );
        assert_eq!(
            summary(&ground),
            vec![
                (
                    HaltReasonOutput::Trivial,
                    0,
                    top(&format!("Lbls3{{}}({})", int(0)))
                );
                leaves
            ],
            "{strategy:?}"
        );
        assert_trivial_rule(&backend, &ground.leaves[0], rule);
    }
    if !backend.capabilities().smt {
        return;
    }
    for (strategy, stop_at_branch, leaves) in [
        (ExecutionStrategy::All, false, 1),
        (ExecutionStrategy::All, true, 1),
        (ExecutionStrategy::Any, false, 1),
    ] {
        let result = execute_both(
            &mut backend,
            request_with(&format!("Lbls3{{}}({X})"), |request| {
                request.strategy = strategy;
                request.stop_at_branch = stop_at_branch;
            }),
        );
        let context = format!("{strategy:?} {stop_at_branch}: {:#?}", summary(&result));
        let trivial = trivial_leaves(&result);
        assert_eq!(trivial.len(), leaves, "{context}");
        let zero = format!(
            "\\equals{{SortInt{{}}, SortGeneratedTopCell{{}}}}({X}, {})",
            int(0)
        );
        for leaf in trivial {
            assert_eq!(leaf.depth, 0, "{context}");
            assert!(is_pre_step(leaf, "Lbls3{}(X:SortInt{})"), "{context}");
            assert!(text(leaf).ends_with(&format!("{zero})")), "{context}");
        }
        let stuck = result
            .leaves
            .iter()
            .filter(|leaf| leaf.reason == HaltReasonOutput::Stuck)
            .collect::<Vec<_>>();
        assert_eq!(stuck.len(), 1, "{context}");
        assert!(
            text(stuck[0]).contains(&format!("\\not{{SortGeneratedTopCell{{}}}}({zero})")),
            "{context}"
        );
    }
}

/// A lower-priority candidate is applied to the higher priority's remainder after its
/// simplification (`f2(X)` is `2` where `not (X >Int 0)`). When that candidate's result is
/// undefined, the leaf's path goes through that simplification, whether the undefinedness is
/// found after the step (`remlo`, through the contradicted `total` `td`) or by the step itself
/// (`rem2lo`, a partial division): the two leaves have the same state, trace and observations.
#[test]
fn an_undefined_step_on_a_simplified_remainder_traces_the_simplification() {
    let mut backend = backend();
    if !backend.capabilities().smt {
        return;
    }
    let trivial_of = |backend: &mut Backend, program: &str| {
        let result = execute_both(backend, request(program));
        let [trivial] = trivial_leaves(&result)[..] else {
            panic!("one Trivial leaf: {:#?}", summary(&result));
        };
        trivial.clone()
    };
    let after = trivial_of(&mut backend, &format!("Lblrem{{}}({X}, Lblf2{{}}({X}))"));
    let within = trivial_of(&mut backend, &format!("Lblrem2{{}}({X}, Lblf2{{}}({X}))"));
    assert_trivial_rule(&backend, &after, "remlo");
    assert_trivial_rule(&backend, &within, "rem2lo");
    assert_eq!(after.depth, 0);
    assert!(is_pre_step(&after, &format!("Lblrem{{}}({X}, {})", int(2))));
    assert_eq!(text(&after).replace("Lblrem{}", "Lblrem2{}"), text(&within));
    assert!(
        !after.trace.is_empty(),
        "the remainder's simplification is traced"
    );
    assert_eq!(after.trace, within.trace);
    assert_eq!(after.observations.len(), within.observations.len());
    assert!(!after.observations.is_empty());
}

/// Strategy `any` decides whether a candidate's result is undefined by normalizing its successor
/// within the step when a later rule of the priority could take its instances, as `cntdone` could
/// for `cntstep`; the successor then takes that normalization instead of repeating it. So a
/// concrete run whose cost is the successor's evaluation (`fib(8)` at each of ten steps) applies
/// as many equations under `any` as under `all`, which does no such check.
#[test]
fn strategy_any_normalizes_each_committed_successor_once() {
    let mut backend = backend();
    let mut equations = |strategy| {
        let before = measure::snapshot();
        let result = backend
            .execute(request_with(
                &format!("Lblcnt{{}}({}, {})", int(10), int(0)),
                |request| request.strategy = strategy,
            ))
            .unwrap();
        let attempts = measure::snapshot()
            .delta(&before)
            .get(Counter::SimplifyEquationAttempts);
        assert_eq!(
            summary(&result),
            [(
                HaltReasonOutput::Stuck,
                11,
                top(&format!("Lblval{{}}({})", int(210)))
            )],
            "{strategy:?}"
        );
        attempts
    };
    let all = equations(ExecutionStrategy::All);
    let any = equations(ExecutionStrategy::Any);
    assert!(all > 0, "the run evaluates `fib`");
    assert_eq!(any, all, "equation attempts under any and all");
}

/// The reading of a `\bottom` successor on every execution route (design/undefined-successor.md
/// §3, reading R): a candidate whose successor normalizes to `\bottom` denotes no state, so it is
/// no successor, however the `\bottom` is found. Its instances that no defined candidate of its
/// priority takes are the undefined step's `Trivial` leaf over the pre-step configuration; where
/// a defined candidate takes them, there is no leaf. Lower priorities stay blocked, and strategy
/// `any` follows a defined successor.
///
/// Each program of [`matrix_source`] pairs one way a candidate's result is `\bottom` (a route of
/// [`ROUTES`]) with one shape of the step around it ([`SHAPES`]); every program is run under both
/// strategies and both result modalities, plainly, stopping at branches and with the `\bottom`
/// rule as a cut point and as a terminal rule, with and without the console, and searched in every
/// search mode. Every row must read R.
mod matrix {
    use super::*;
    use k_rust::backend::{SearchRequest, SearchTypeArg};
    use k_rust_backend::{
        definition::BackendDefinition,
        rewrite::{
            ExecutionBranchMode, ExecutionMode, ExecutionOptions, HaltReason, execute_with_io_state,
        },
        rule::Predicate,
        search::ResultModality,
        transition::ExecutionIoState,
    };
    use undefined_successor::{Shape, matrix_source, programs};

    fn matrix_kore() -> std::sync::Arc<String> {
        static KORE: shared::Shared<String> = shared::Shared::new();
        KORE.get(|| {
            let source = matrix_source();
            let mut resolver = |_: &str, required: &str| {
                embedded(required).ok_or_else(|| format!("unexpected require {required}"))
            };
            let loaded = load_with_options(
                ResolvedSource::new("fu42.k", &source),
                "FU42",
                &mut resolver,
                &LoadOptions {
                    implicit_sources: vec![embedded("prelude.md").unwrap()],
                    ..CompilationBackend::Rust.load_options()
                },
            )
            .unwrap();
            compile_loaded_definition(&loaded, CompileOptions::default())
                .unwrap()
                .definition_kore
        })
    }

    /// How a run is stopped.
    #[derive(Clone, Copy, Debug)]
    enum Stops {
        Plain,
        StopAtBranch,
        /// The program's rule `<p><letter>` is a cut point; stopping at branches or not.
        CutPoint(char, bool),
        /// The program's rule `<p><letter>` is a terminal rule; stopping at branches or not.
        Terminal(char, bool),
    }

    impl Stops {
        /// The rule a stop rule names, if any.
        fn rule(self) -> Option<char> {
            match self {
                Stops::CutPoint(letter, _) | Stops::Terminal(letter, _) => Some(letter),
                Stops::Plain | Stops::StopAtBranch => None,
            }
        }
    }

    /// The stop options of the matrices: a cut point or a terminal rule on each of the
    /// program's rules (the `\bottom` rule `<p>a`, and `<p>b`: the defined sibling, the
    /// lower-priority rule or the second `\bottom` rule), with and without stopping at branches.
    const STOPS: [Stops; 10] = [
        Stops::Plain,
        Stops::StopAtBranch,
        Stops::CutPoint('a', false),
        Stops::CutPoint('a', true),
        Stops::CutPoint('b', false),
        Stops::CutPoint('b', true),
        Stops::Terminal('a', false),
        Stops::Terminal('a', true),
        Stops::Terminal('b', false),
        Stops::Terminal('b', true),
    ];

    /// Which configuration a leaf is.
    #[derive(Clone, Debug, PartialEq)]
    enum State {
        /// The program's own configuration, before any step.
        Pre,
        Done,
        /// A configuration with no instance, `\bottom`.
        Bottom,
        Other(String),
    }

    /// A leaf: its reason, depth, configuration and rule label (that of a `Trivial` leaf, and on
    /// the console route that of a `Vacuous` one).
    type Row = (String, u64, State, Option<String>);

    /// What reading R gives for `program` of `shape` under `strategy`, whatever the result
    /// modality, the stop rules on the `\bottom` rule, stopping at branches or the console.
    ///
    /// The undefined step has one `Trivial` leaf, standing for every instance on which a
    /// candidate applies and every candidate that applies is undefined. Under strategy all the
    /// two-`\bottom` shape's leaf names the first candidate; under strategy any it may name
    /// either (`<p>?`), the one the sequential step kept.
    ///
    /// A cut-point or terminal rule on the covering rule `<p>b` stops the run at the step's one
    /// successor: before it (`cut-point`, the pre-step configuration) or after it (`terminal`).
    /// A stop rule on a `\bottom` rule or on a blocked lower-priority rule selects no successor.
    fn expected(
        program: &str,
        shape: Shape,
        strategy: ExecutionStrategy,
        stops: Stops,
    ) -> Vec<Row> {
        let trivial = |rule: &str| {
            (
                "trivial".to_owned(),
                0,
                State::Pre,
                Some(format!("FU42.{program}{rule}")),
            )
        };
        match (shape, strategy) {
            (Shape::Covering, _) => match stops {
                Stops::CutPoint('b', _) => vec![("cut-point".to_owned(), 0, State::Pre, None)],
                Stops::Terminal('b', _) => vec![("terminal".to_owned(), 1, State::Done, None)],
                _ => vec![("stuck".to_owned(), 1, State::Done, None)],
            },
            (Shape::Lower | Shape::Alone, _) => vec![trivial("a")],
            (Shape::Two, ExecutionStrategy::All) => vec![trivial("a")],
            (Shape::Two, _) => vec![trivial("?")],
        }
    }

    fn initial(program: &str) -> String {
        top(&format!("Lbl{program}{{}}({})", int(0)))
    }

    /// `program`'s configuration under the constraint `N ==Int 0 /\ N =/=Int 0`, which has no
    /// model and which the initial normalization does not refute before the first step.
    fn empty_initial(program: &str) -> String {
        let condition = |operator: &str| {
            format!(
                r#"\equals{{SortBool{{}}, SortGeneratedTopCell{{}}}}({operator}{{}}(N:SortInt{{}}, \dv{{SortInt{{}}}}("0")), \dv{{SortBool{{}}}}("true"))"#
            )
        };
        format!(
            r#"\and{{SortGeneratedTopCell{{}}}}({}, \and{{SortGeneratedTopCell{{}}}}({}, {}))"#,
            initial(program),
            condition("Lbl'UndsEqlsEqls'Int'Unds'"),
            condition("Lbl'UndsEqlsSlshEqls'Int'Unds'"),
        )
    }

    fn classify(program: &str, text: &str) -> State {
        if text == initial(program) {
            State::Pre
        } else if text == top("Lbldone{}()") {
            State::Done
        } else if text == "\\bottom{SortGeneratedTopCell{}}()" {
            State::Bottom
        } else {
            State::Other(text.to_owned())
        }
    }

    /// The leaves of `program`, from the configuration `start`, through the facade (no console).
    fn facade_rows(
        program: &str,
        start: &str,
        strategy: ExecutionStrategy,
        modality: ResultModalityOutput,
        stops: Stops,
    ) -> Vec<Row> {
        let mut backend = Backend::new(&matrix_kore(), "FU42", BackendOptions::default()).unwrap();
        let rule = |letter: char| format!("FU42.{program}{letter}");
        let mut request = ExecuteRequest {
            result_modality: modality,
            strategy,
            max_depth: Some(10),
            ..ExecuteRequest::new(parse_pattern(start).unwrap())
        };
        match stops {
            Stops::Plain => {}
            Stops::StopAtBranch => request.stop_at_branch = true,
            Stops::CutPoint(letter, stop) => {
                request.cut_point_rules = vec![rule(letter)];
                request.stop_at_branch = stop;
            }
            Stops::Terminal(letter, stop) => {
                request.terminal_rules = vec![rule(letter)];
                request.stop_at_branch = stop;
            }
        }
        let result = backend.execute(request).unwrap();
        result
            .leaves
            .iter()
            .map(|leaf| {
                let reason = serde_json::to_value(leaf.reason).unwrap();
                (
                    reason.as_str().unwrap().to_owned(),
                    leaf.depth,
                    classify(program, &text(leaf)),
                    match leaf.reason {
                        HaltReasonOutput::Trivial => leaf.rule_label.clone(),
                        _ => None,
                    },
                )
            })
            .collect()
    }

    /// The leaves of `program`, from the configuration `start`, through the console route
    /// (`krun --io on`).
    fn console_rows(
        program: &str,
        start: &str,
        strategy: ExecutionStrategy,
        modality: ResultModalityOutput,
        stops: Stops,
    ) -> Vec<Row> {
        let syntax = k_rust::kore::parser::parse_definition(&matrix_kore()).unwrap();
        let definition = BackendDefinition::internalize(&syntax, "FU42").unwrap();
        let internal = |text: &str| {
            definition
                .admit_unverified(&parse_pattern(text).unwrap(), &[])
                .internalize_pattern()
                .unwrap()
        };
        let pre = internal(&initial(program));
        let done = internal(&top("Lbldone{}()"));
        let rule = |letter: char| format!("FU42.{program}{letter}");
        let mut options = ExecutionOptions {
            max_depth: 10,
            mode: match strategy {
                ExecutionStrategy::All => ExecutionMode::All,
                _ => ExecutionMode::Any,
            },
            result_modality: match modality {
                ResultModalityOutput::PathSet => ResultModality::PathSet,
                _ => ResultModality::StateSet,
            },
            ..ExecutionOptions::default()
        };
        match stops {
            Stops::Plain => {}
            Stops::StopAtBranch => options.branch_mode = ExecutionBranchMode::StopAtBranch,
            Stops::CutPoint(letter, stop) => {
                options.cut_point_rules.insert(rule(letter));
                if stop {
                    options.branch_mode = ExecutionBranchMode::StopAtBranch;
                }
            }
            Stops::Terminal(letter, stop) => {
                options.terminal_rules.insert(rule(letter));
                if stop {
                    options.branch_mode = ExecutionBranchMode::StopAtBranch;
                }
            }
        }
        let result = execute_with_io_state(
            &definition,
            internal(start),
            options,
            ExecutionIoState::new(Vec::new()),
        );
        result
            .leaves
            .iter()
            .map(|leaf| {
                let state = if leaf.pattern == pre {
                    State::Pre
                } else if leaf.pattern == done {
                    State::Done
                } else if leaf.pattern.constraints == [Predicate::False] {
                    State::Bottom
                } else {
                    State::Other(format!("{:?}", leaf.pattern))
                };
                let (reason, label) = match &leaf.halt_reason {
                    HaltReason::Stuck => ("stuck".to_owned(), None),
                    HaltReason::Trivial { label, .. } => ("trivial".to_owned(), label.clone()),
                    HaltReason::Vacuous { label, .. } => ("vacuous".to_owned(), label.clone()),
                    HaltReason::CutPointRule { .. } => ("cut-point".to_owned(), None),
                    HaltReason::TerminalRule { .. } => ("terminal".to_owned(), None),
                    HaltReason::Branch { .. } => ("branch".to_owned(), None),
                    other => (format!("{other:?}"), None),
                };
                (reason, leaf.depth, state, label)
            })
            .collect()
    }

    /// Whether `found` reads R: the expected rows, where an expected label `<p>?` accepts the
    /// label of either rule of the program.
    fn reads_r(program: &str, expected: &[Row], found: &[Row]) -> bool {
        expected.len() == found.len()
            && expected.iter().zip(found).all(|(expected, found)| {
                let (reason, depth, state, label) = expected;
                (reason, depth, state) == (&found.0, &found.1, &found.2)
                    && match label.as_deref().and_then(|label| label.strip_suffix('?')) {
                        None => label == &found.3,
                        Some(_) => [format!("FU42.{program}a"), format!("FU42.{program}b")]
                            .iter()
                            .any(|rule| found.3.as_deref() == Some(rule.as_str())),
                    }
            })
    }

    /// Every execution row of the matrix reads R; the rows that do not are listed. The state-set
    /// results with and without the console are the same.
    #[test]
    fn every_execution_route_reads_a_bottom_successor_as_no_successor() {
        let mut wrong = Vec::new();
        let mut rows = 0;
        for (program, route, shape) in programs() {
            for strategy in [ExecutionStrategy::Any, ExecutionStrategy::All] {
                for modality in [
                    ResultModalityOutput::PathSet,
                    ResultModalityOutput::StateSet,
                ] {
                    for stops in STOPS {
                        if stops.rule() == Some('b') && shape == Shape::Alone {
                            continue;
                        }
                        let expected = expected(&program, shape, strategy, stops);
                        let mut both = Vec::new();
                        for console in [false, true] {
                            rows += 1;
                            let start = initial(&program);
                            let found = if console {
                                console_rows(&program, &start, strategy, modality, stops)
                            } else {
                                facade_rows(&program, &start, strategy, modality, stops)
                            };
                            if !reads_r(&program, &expected, &found) {
                                wrong.push(format!(
                                    "{program} ({}, {shape:?}) {strategy:?} {modality:?} {stops:?} io {}: {found:?}, expected {expected:?}",
                                    route.name,
                                    if console { "on" } else { "off" },
                                ));
                            }
                            both.push(found);
                        }
                        // With and without the console the results agree; where R leaves the
                        // named rule open (`<p>?`), on all but the rule.
                        let open = expected
                            .iter()
                            .any(|row| row.3.as_deref().is_some_and(|label| label.ends_with('?')));
                        let strip = |rows: &Vec<Row>| {
                            rows.iter()
                                .map(|row| {
                                    (
                                        row.0.clone(),
                                        row.1,
                                        row.2.clone(),
                                        (!open).then(|| row.3.clone()),
                                    )
                                })
                                .collect::<Vec<_>>()
                        };
                        if strip(&both[0]) != strip(&both[1]) {
                            wrong.push(format!(
                                "{program} ({}, {shape:?}) {strategy:?} {modality:?} {stops:?}: io off {:?} and on {:?} differ",
                                route.name, both[0], both[1]
                            ));
                        }
                    }
                }
            }
        }
        // The alone shape has no rule `<p>b` to stop at.
        assert_eq!(rows, (7 * 4 * 10 - 7 * 4) * 2 * 2 * 2);
        assert!(
            wrong.is_empty(),
            "{} wrong of {rows} rows:\n{}",
            wrong.len(),
            wrong.join("\n")
        );
    }

    /// A configuration that has no instance, which only its step exposes, is one `Vacuous` leaf
    /// at the step's successor depth that names no rule, on every route and shape, under both
    /// strategies and modalities, with any stop rule on any of its rules, stopping at branches or
    /// not, with the console or not: never a `Trivial` leaf (no instance has an undefined step),
    /// never one per candidate, and never an empty result.
    #[test]
    fn a_configuration_with_no_instance_is_one_vacuous_leaf_on_every_route() {
        let mut wrong = Vec::new();
        let mut rows = 0;
        let expected = vec![("vacuous".to_owned(), 1, State::Bottom, None)];
        for (program, route, shape) in programs() {
            let start = empty_initial(&program);
            for strategy in [ExecutionStrategy::Any, ExecutionStrategy::All] {
                for modality in [
                    ResultModalityOutput::PathSet,
                    ResultModalityOutput::StateSet,
                ] {
                    for stops in STOPS {
                        if stops.rule() == Some('b') && shape == Shape::Alone {
                            continue;
                        }
                        for console in [false, true] {
                            rows += 1;
                            let found = if console {
                                console_rows(&program, &start, strategy, modality, stops)
                            } else {
                                facade_rows(&program, &start, strategy, modality, stops)
                            };
                            if found != expected {
                                wrong.push(format!(
                                    "{program} ({}, {shape:?}) {strategy:?} {modality:?} {stops:?} io {}: {found:?}",
                                    route.name,
                                    if console { "on" } else { "off" },
                                ));
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(rows, (7 * 4 * 10 - 7 * 4) * 2 * 2 * 2);
        assert!(
            wrong.is_empty(),
            "{} wrong of {rows} rows:\n{}",
            wrong.len(),
            wrong.join("\n")
        );
    }

    /// The review's shapes beyond the route matrix, with symbolic inputs: a candidate's
    /// successor `\bottom` beside a sibling that covers only some instances, a constrained
    /// `\bottom` rule above a lower-priority rule, definedness only a solver decides, nested
    /// `total` calls, a `\bottom` in another cell, and the shapes the step itself decides (a rule
    /// `ensures` refuted by the path condition, an infeasible `requires`); a stop rule on the
    /// defined sibling of a constrained `\bottom` rule, of the same priority (`qc`) or a lower one
    /// (`pl`); and a branch beside an undefined step (`br`), whose `Branch` leaf, stopping at
    /// branches, stands for the instances the step does not leave undefined.
    const SHAPES_SOURCE: &str = r#"
module P
  imports INT
  imports BOOL
  syntax Pgm ::= "done" | "done2" | val(Int) | w(Int)
               | es(Int) | esb(Int) | ep(Int) | rq(Int) | rp(Int)
               | pc(Int) | pd(Int) | pl(Int) | nf(Int) | oc(Int) | ud(Int) | eb(Int) | ec(Int)
               | qc(Int) | br(Int)
  syntax Int ::= tb(Int) [function, total]
               | f1(Int) [function, total]
               | f2(Int) [function, total]
  configuration <k> $PGM:Pgm </k> <c> 0 </c>
  rule [tbeq]:   tb(I) => #Bottom requires I ==Int 0
  rule [tbeq2]:  tb(I) => I requires I =/=Int 0
  rule [f1eq]:   f1(I) => f2(I) +Int 1
  rule [f2eq]:   f2(I) => #Bottom requires I ==Int 0
  rule [f2eq2]:  f2(I) => I requires I =/=Int 0
  rule [esa]: es(X) => done2 ensures X >Int 0
  rule [esba]: esb(X) => done2 ensures X >Int 0
  rule [esbb]: esb(_) => done
  rule [epa]: ep(X) => done2 ensures X >Int 0
  rule [epb]: ep(_) => done [priority(60)]
  rule [rqa]: rq(X) => done2 requires X >Int 0
  rule [rpa]: rp(X) => done2 requires X >Int 0
  rule [rpb]: rp(_) => done [priority(60)]
  rule [pca]: pc(_) => val(tb(0))
  rule [pcb]: pc(X) => done requires X >Int 5
  rule [pda]: pd(_) => val(tb(0))
  rule [pdb]: pd(X) => done requires X >Int 5
  rule [pla]: pl(X) => val(tb(0)) requires X >Int 0
  rule [plb]: pl(_) => done [priority(60)]
  rule [nfa]: nf(X) => val(f1(X))
  rule [nfb]: nf(_) => done
  rule [oca]: <k> oc(_) => done </k> <c> _ => tb(0) </c>
  rule [ocb]: <k> oc(_) => done2 </k>
  rule [uda]: ud(X) => val(tb(X))
  rule [udb]: ud(X) => done requires X >Int 5
  rule [eba]: eb(X) => val(tb(X))
  rule [eca]: ec(X) => done2 ensures X >Int 0
  rule [qca]: qc(X) => val(tb(0)) requires X >Int 0
  rule [qcb]: qc(X) => done requires X <=Int 0
  rule [bra]: br(X) => val(tb(0)) requires X >Int 3
  rule [brb]: br(X) => done requires X <=Int 0
  rule [brc]: br(X) => done2 requires X >Int 0 andBool X <=Int 5
endmodule
"#;

    /// The KORE of [`SHAPES_SOURCE`] and the configuration of `program` with each `777` read
    /// as the variable `N`, conjoined with `constraints` (`(operator, bound)`: `N op bound`).
    fn shape_initial(program: &str, constraints: &[(&str, i64)]) -> (String, String) {
        use k_rust::{
            kast::Sort,
            kompile::{ConfigurationAssembler, ProgramGrammar},
        };
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new("shapes.k", SHAPES_SOURCE),
            "P",
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
            ConfigurationAssembler::new(&grammar, "P", "P", &artifacts.configuration_variables);
        assembler.program(&Sort::new("Pgm"), program).unwrap();
        let ground = Printer::compact().print_pattern(&assembler.finish().unwrap());
        let mut start = ground.replace("\\dv{SortInt{}}(\"777\")", "N:SortInt{}");
        for (operator, bound) in constraints {
            start = format!(
                r#"\and{{SortGeneratedTopCell{{}}}}({start}, \equals{{SortBool{{}}, SortGeneratedTopCell{{}}}}({operator}{{}}(N:SortInt{{}}, {}), \dv{{SortBool{{}}}}("true")))"#,
                int(*bound)
            );
        }
        (artifacts.definition_kore, start)
    }

    /// Stopping plainly, at branches, and at a cut point or terminal rule on the rule `<p>b`
    /// with and without stopping at branches.
    fn sibling_stops() -> Vec<Stops> {
        vec![
            Stops::Plain,
            Stops::StopAtBranch,
            Stops::CutPoint('b', false),
            Stops::CutPoint('b', true),
            Stops::Terminal('b', false),
            Stops::Terminal('b', true),
        ]
    }

    /// The leaf of an instance whose one successor is `done` by the rule `<p>b`, under `stops`.
    fn stopped_or_done(stops: Stops) -> (&'static str, u64, &'static str, Option<&'static str>) {
        match stops {
            Stops::CutPoint(..) => ("cut-point", 0, "pre", None),
            Stops::Terminal(..) => ("terminal", 1, "done", None),
            _ => ("stuck", 1, "done", None),
        }
    }

    const GT: &str = "Lbl'Unds-GT-'Int'Unds'";
    const LT: &str = "Lbl'Unds-LT-'Int'Unds'";
    const LE: &str = "Lbl'Unds-LT-Eqls'Int'Unds'";
    const GE: &str = "Lbl'Unds-GT-Eqls'Int'Unds'";

    /// What a leaf of a shape is: `Pre` (the program's configuration), `Done`, `Done2`.
    fn shape_state(program: &str, text: &str) -> &'static str {
        let head = program.split('(').next().unwrap();
        if text.contains("Lbldone2'Unds'P'Unds'Pgm{}()") {
            "done2"
        } else if text.contains("Lbldone'Unds'P'Unds'Pgm{}()") {
            "done"
        } else if text.contains(&format!("Lbl{head}'LParUnds")) {
            "pre"
        } else {
            "other"
        }
    }

    /// The leaves partition the instances under R: for each sample value of `N` that the
    /// initial constraint admits, exactly one leaf's constraint holds, and it is the expected
    /// leaf (reason, depth, configuration, and the rule a `Trivial` leaf names). A ground
    /// program has the one sample `None`.
    #[test]
    fn the_leaves_of_symbolic_shapes_partition_their_instances() {
        type Expect =
            fn(Option<i64>, Stops) -> (&'static str, u64, &'static str, Option<&'static str>);
        let stuck_done: Expect = |_, _| ("stuck", 1, "done", None);
        /// A program, its constraints on `N`, the sample values, the stop options and the
        /// expected leaf of a sample.
        type Case = (
            &'static str,
            Vec<(&'static str, i64)>,
            Vec<i64>,
            Vec<Stops>,
            Expect,
        );
        let cases: Vec<Case> = vec![
            (
                "pc(777)",
                vec![],
                vec![-1, 0, 5, 6, 10],
                vec![Stops::Plain, Stops::StopAtBranch],
                |v, _| {
                    if v.unwrap() > 5 {
                        ("stuck", 1, "done", None)
                    } else {
                        ("trivial", 0, "pre", Some("P.pca"))
                    }
                },
            ),
            (
                "pd(777)",
                vec![(GT, 10)],
                vec![11, 20],
                vec![Stops::Plain, Stops::StopAtBranch],
                stuck_done,
            ),
            (
                "pl(777)",
                vec![],
                vec![-1, 0, 1, 5],
                sibling_stops(),
                |v, stops| {
                    if v.unwrap() > 0 {
                        ("trivial", 0, "pre", Some("P.pla"))
                    } else {
                        stopped_or_done(stops)
                    }
                },
            ),
            (
                "qc(777)",
                vec![],
                vec![-1, 0, 1, 5],
                sibling_stops(),
                |v, stops| {
                    if v.unwrap() > 0 {
                        ("trivial", 0, "pre", Some("P.qca"))
                    } else {
                        stopped_or_done(stops)
                    }
                },
            ),
            (
                "br(777)",
                vec![],
                vec![-1, 0, 2, 4, 5, 6, 10],
                vec![Stops::Plain, Stops::StopAtBranch],
                |v, stops| match (v.unwrap(), stops) {
                    (v, _) if v > 5 => ("trivial", 0, "pre", Some("P.bra")),
                    (_, Stops::StopAtBranch) => ("branch", 0, "pre", None),
                    (v, _) if v <= 0 => ("stuck", 1, "done", None),
                    _ => ("stuck", 1, "done2", None),
                },
            ),
            (
                "eb(777)",
                vec![(LE, 0), (GE, 0)],
                vec![0],
                vec![Stops::Plain, Stops::StopAtBranch],
                |_, _| ("trivial", 0, "pre", Some("P.eba")),
            ),
            (
                "ud(777)",
                vec![(LE, 0), (GE, 0)],
                vec![0],
                vec![Stops::Plain, Stops::StopAtBranch],
                |_, _| ("trivial", 0, "pre", Some("P.uda")),
            ),
            (
                "nf(0)",
                vec![],
                vec![],
                vec![Stops::Plain, Stops::StopAtBranch],
                stuck_done,
            ),
            (
                "oc(0)",
                vec![],
                vec![],
                vec![Stops::Plain, Stops::StopAtBranch],
                |_, _| ("stuck", 1, "done2", None),
            ),
            (
                "es(777)",
                vec![(LT, 0)],
                vec![-3, -1],
                vec![Stops::Plain, Stops::StopAtBranch],
                |_, _| ("trivial", 0, "pre", Some("P.esa")),
            ),
            (
                "esb(777)",
                vec![(LT, 0)],
                vec![-3, -1],
                vec![Stops::Plain, Stops::StopAtBranch],
                stuck_done,
            ),
            (
                "ep(777)",
                vec![(LT, 0)],
                vec![-3, -1],
                vec![Stops::Plain, Stops::StopAtBranch],
                |_, _| ("trivial", 0, "pre", Some("P.epa")),
            ),
            (
                "rq(777)",
                vec![(LT, 0)],
                vec![-3, -1],
                vec![Stops::Plain, Stops::StopAtBranch],
                |_, _| ("stuck", 0, "pre", None),
            ),
            (
                "rp(777)",
                vec![(LT, 0)],
                vec![-3, -1],
                vec![Stops::Plain, Stops::StopAtBranch],
                stuck_done,
            ),
            (
                "ec(777)",
                vec![],
                vec![-1, 0, 1, 5],
                vec![Stops::Plain, Stops::StopAtBranch],
                |v, _| {
                    if v.unwrap() > 0 {
                        ("stuck", 1, "done2", None)
                    } else {
                        ("trivial", 0, "pre", Some("P.eca"))
                    }
                },
            ),
        ];
        let mut wrong = Vec::new();
        for (program, constraints, samples, stops_list, expect) in cases {
            let (kore, start) = shape_initial(program, &constraints);
            let mut backend = Backend::new(&kore, "P", BackendOptions::default()).unwrap();
            if !backend.capabilities().smt {
                // Without a solver the symbolic conditions are undecided.
                return;
            }
            let samples = if samples.is_empty() {
                vec![None]
            } else {
                samples.into_iter().map(Some).collect()
            };
            for strategy in [ExecutionStrategy::Any, ExecutionStrategy::All] {
                for modality in [
                    ResultModalityOutput::PathSet,
                    ResultModalityOutput::StateSet,
                ] {
                    for &stops in &stops_list {
                        let mut request = ExecuteRequest {
                            result_modality: modality,
                            strategy,
                            max_depth: Some(10),
                            ..ExecuteRequest::new(parse_pattern(&start).unwrap())
                        };
                        let rule = |letter: char| {
                            format!("P.{}{letter}", program.split('(').next().unwrap())
                        };
                        match stops {
                            Stops::Plain => {}
                            Stops::StopAtBranch => request.stop_at_branch = true,
                            Stops::CutPoint(letter, stop) => {
                                request.stop_at_branch = stop;
                                request.cut_point_rules = vec![rule(letter)];
                            }
                            Stops::Terminal(letter, stop) => {
                                request.stop_at_branch = stop;
                                request.terminal_rules = vec![rule(letter)];
                            }
                        }
                        let result = backend.execute(request).unwrap();
                        let context = format!("{program} {strategy:?} {modality:?} {stops:?}");
                        for &sample in &samples {
                            let mut holding = Vec::new();
                            for leaf in &result.leaves {
                                let printed = text(leaf);
                                // A ground program's leaves have no constraint to decide.
                                let Some(value) = sample else {
                                    holding.push(leaf);
                                    continue;
                                };
                                let instance = printed.replace("N:SortInt{}", &int(value));
                                let verdict = backend
                                    .get_model(PatternRequest::new(
                                        parse_pattern(&instance).unwrap(),
                                    ))
                                    .unwrap()
                                    .satisfiable;
                                match verdict.as_str() {
                                    "unsat" => {}
                                    "sat" => holding.push(leaf),
                                    other => wrong.push(format!(
                                        "{context} N = {sample:?}: {other} for {printed}"
                                    )),
                                }
                            }
                            let found = holding
                                .iter()
                                .map(|leaf| {
                                    let reason = serde_json::to_value(leaf.reason).unwrap();
                                    (
                                        reason.as_str().unwrap().to_owned(),
                                        leaf.depth,
                                        shape_state(program, &text(leaf)),
                                        match leaf.reason {
                                            HaltReasonOutput::Trivial => leaf.rule_label.clone(),
                                            _ => None,
                                        },
                                    )
                                })
                                .collect::<Vec<_>>();
                            let (reason, depth, state, label) = expect(sample, stops);
                            let expected =
                                vec![(reason.to_owned(), depth, state, label.map(str::to_owned))];
                            if found != expected {
                                wrong.push(format!(
                                    "{context} N = {sample:?}: {found:?}, expected {expected:?}"
                                ));
                            }
                        }
                    }
                }
            }
        }
        assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    }

    /// A search reads a `\bottom` successor as no state, and an undefined step as no result:
    /// from each program the states found, by depth and configuration, in each search mode.
    #[test]
    fn every_search_mode_reads_a_bottom_successor_as_no_state() {
        let mut wrong = Vec::new();
        for (program, route, shape) in programs() {
            let mut backend =
                Backend::new(&matrix_kore(), "FU42", BackendOptions::default()).unwrap();
            let request = |search_type| SearchRequest {
                search_type,
                max_depth: Some(10),
                ..SearchRequest::new(parse_pattern(&initial(&program)).unwrap())
            };
            let states = |value: serde_json::Value, field: &str| {
                let mut states = value[field]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|state| {
                        let printed = Printer::compact()
                            .print_pattern(&codec::from_value(&state["state"]).unwrap());
                        (
                            state["depth"].as_u64().unwrap(),
                            classify(&program, &printed),
                        )
                    })
                    .collect::<Vec<_>>();
                states.sort_by_key(|state| format!("{state:?}"));
                assert!(
                    value["incomplete"].as_array().unwrap().is_empty(),
                    "{program}: {value:#}"
                );
                states
            };
            let covering = shape == Shape::Covering;
            for (mode, search_type, expected) in [
                (
                    "final",
                    SearchTypeArg::Final,
                    if covering {
                        vec![(1, State::Done)]
                    } else {
                        vec![]
                    },
                ),
                (
                    "all",
                    SearchTypeArg::All,
                    if covering {
                        vec![(0, State::Pre), (1, State::Done)]
                    } else {
                        vec![(0, State::Pre)]
                    },
                ),
                (
                    "one step",
                    SearchTypeArg::OneStep,
                    if covering {
                        vec![(1, State::Done)]
                    } else {
                        vec![]
                    },
                ),
                (
                    "one or more steps",
                    SearchTypeArg::OneOrMoreSteps,
                    if covering {
                        vec![(1, State::Done)]
                    } else {
                        vec![]
                    },
                ),
            ] {
                let found = states(
                    serde_json::to_value(backend.search(request(search_type)).unwrap()).unwrap(),
                    "states",
                );
                if found != expected {
                    wrong.push(format!(
                        "{program} ({}, {shape:?}) search {mode}: {found:?}, expected {expected:?}",
                        route.name
                    ));
                }
            }
            let found = states(
                serde_json::to_value(backend.search_paths(request(SearchTypeArg::Final)).unwrap())
                    .unwrap(),
                "witnesses",
            );
            let expected = if covering {
                vec![(1, State::Done)]
            } else {
                vec![]
            };
            if found != expected {
                wrong.push(format!(
                    "{program} ({}, {shape:?}) path search: {found:?}, expected {expected:?}",
                    route.name
                ));
            }
        }
        assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    }
}
