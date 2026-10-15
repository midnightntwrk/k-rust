//! A symbolic step keeps the definedness of the partial terms a builtin hook consumed.
//!
//! Every hook is strict: `f(t1, .., tn)` is `\bottom` wherever some `ti` is, so a hook that
//! evaluates `f(t1, .., tn)` to `v` without inspecting a symbolic `ti` (`t ==Int t`,
//! `true orBool b`, `true orElseBool b`, `#if true #then a #else b #fi`) must return
//! `\ceil(t1) /\ .. /\ \ceil(tn) /\ v`. With `10 /Int X` as such an argument, every leaf a rule
//! reaches from a symbolic `X` must imply `X =/=Int 0`, which is what ground execution on `0`
//! shows: the rule does not apply (Stuck) or its successor is empty (Trivial).
//!
//! A rule or equation condition holds on an instance only where its terms are defined, so the
//! same holds for a condition that no hook shortcuts but a solver decides (`10 /Int A <=Int
//! 10 /Int A`, which a solver that gives `/Int` a value at `0` finds valid) and for a condition
//! the predicate simplifier splits into a disjunction (`a orBool b` into `a \/ b`).

use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, ExecutionLeaf, HaltReasonOutput,
        ResultModalityOutput,
    },
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::{codec, parser::parse_pattern, printer::Printer},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

#[path = "support/shared.rs"]
mod shared;

const SOURCE: &str = r#"module DEFPROBE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Op ::= half(Int)   [symbol(half)]
              | orb(Int)    [symbol(orb)]
              | orelse(Int) [symbol(orelse)]
              | andthen(Int) [symbol(andthen)]
              | keq(Int)    [symbol(keq)]
              | ifte(Int)   [symbol(ifte)]
              | rhseq(Int)  [symbol(rhseq)]
              | ens(Int)    [symbol(ens)]
              | rhsdiv(Int) [symbol(rhsdiv)]
              | nopb(Bool)  [symbol(nopb)]
              | lt(Int)     [symbol(lt)]
              | orx(Int)    [symbol(orx)]
              | andx(Int)   [symbol(andx)]
              | enslt(Int)  [symbol(enslt)]
              | divok(Int)  [symbol(divok)]
              | eqf(Int)    [symbol(eqf)]
              | eqfk(Int)   [symbol(eqfk)]
              | gnd(Int)    [symbol(gnd)]
              | val(Int)    [symbol(val)]
              | flag(Bool)  [symbol(flag)]
  syntax Prog ::= "halt" [symbol(halt)]
                | seq(Op, Prog) [symbol(seq)]
  syntax Int ::= f(Int) [function, symbol(f)]
endmodule

module DEFPROBE
  imports DEFPROBE-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> .K </k>

  rule [half]:    seq(half(A), P) => P requires 10 /Int A ==Int 10 /Int A
  rule [orb]:     seq(orb(A), P) => P requires true orBool (10 /Int A >Int 0)
  rule [orelse]:  seq(orelse(A), P) => P requires true orElseBool (10 /Int A >Int 0)
  rule [andthen]: seq(andthen(A), P) => P requires notBool (false andThenBool (10 /Int A >Int 0))
  rule [keq]:     seq(keq(A), P) => P requires 10 /Int A ==K 10 /Int A
  rule [ifte]:    seq(ifte(A), P) => seq(val(#if true #then 1 #else 10 /Int A #fi), P)
  rule [rhseq]:   seq(rhseq(A), P) => seq(flag(10 /Int A ==Int 10 /Int A), P)
  rule [ens]:     seq(ens(A), P) => P ensures 10 /Int A ==Int 10 /Int A
  rule [rhsdiv]:  seq(rhsdiv(A), P) => seq(val(10 /Int A), P)
  rule [nopb]:    seq(nopb(_), P) => P
  rule [lt]:      seq(lt(A), P) => P requires 10 /Int A <=Int 10 /Int A
  rule [orx]:     seq(orx(A), P) => P requires A >Int -1 orBool 10 /Int A >Int 0
  rule [andx]:    seq(andx(A), P) => P requires notBool (A <=Int -1 andBool 10 /Int A <=Int 0)
  rule [enslt]:   seq(enslt(A), P) => P ensures 10 /Int A <=Int 10 /Int A
  rule [divok]:   seq(divok(A), P) => seq(val(10 /Int A), P) requires A =/=Int 0
  rule [eqf]:     seq(eqf(A), P) => seq(val(f(A)), P)
  rule [eqfk]:    seq(eqfk(A), P) => seq(val(f(A)), P) requires A =/=Int 0
  rule [gnd]:     seq(gnd(_), P) => P requires f(0) <=Int f(0)
  rule f(X) => 1 requires 10 /Int X <=Int 10 /Int X [simplification]
endmodule
"#;

const X: &str = "X:SortInt{}";
const ZERO: &str = "\\dv{SortInt{}}(\"0\")";
/// `X =/=Int 0` as the leaf predicate states it.
const X_NONZERO: &str = "\\not{SortGeneratedTopCell{}}(\\equals{SortInt{}, SortGeneratedTopCell{}}(X:SortInt{}, \\dv{SortInt{}}(\"0\")))";
/// `X ==Int 0` as the leaf predicate states it (a substring of `X_NONZERO`).
const X_ZERO: &str =
    "\\equals{SortInt{}, SortGeneratedTopCell{}}(X:SortInt{}, \\dv{SortInt{}}(\"0\"))";

/// Operations whose rule relies on the definedness of `10 /Int A` only through a hook that
/// returns without inspecting it.
const HOOK_SHORTCUTS: [&str; 8] = [
    "half", "orb", "orelse", "andthen", "keq", "ifte", "rhseq", "ens",
];
/// Operations whose rule excludes `A = 0` through its `requires`, so `A = 0` is Stuck.
const REQUIRES: [&str; 5] = ["half", "orb", "orelse", "andthen", "keq"];

/// A fresh backend over the KORE of `SOURCE`, which is compiled once per process and inference
/// mode; no test observes another's backend state.
fn backend() -> Backend {
    static KORE: shared::Shared<String> = shared::Shared::new();
    backend_over(&KORE.get(|| compile(SOURCE)))
}

fn backend_over(definition_kore: &str) -> Backend {
    Backend::new(definition_kore, "DEFPROBE", BackendOptions::default()).unwrap()
}

fn compile(source: &str) -> String {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("defprobe.k", source),
        "DEFPROBE",
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

fn top(program: &str) -> String {
    format!(
        "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortProg{{}}, SortKItem{{}}}}({program}), dotk{{}}())), Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\")))"
    )
}

fn seq(op: &str) -> String {
    format!("Lblseq{{}}({op}, Lblhalt{{}}())")
}

fn div(argument: &str) -> String {
    format!("Lbl'UndsSlsh'Int'Unds'{{}}(\\dv{{SortInt{{}}}}(\"10\"), {argument})")
}

struct Leaf {
    depth: u64,
    reason: HaltReasonOutput,
    text: String,
}

impl std::fmt::Debug for Leaf {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "depth {} {:?}: {}",
            self.depth, self.reason, self.text
        )
    }
}

fn leaf(leaf: ExecutionLeaf) -> Leaf {
    let pattern = codec::from_value(&leaf.state).unwrap();
    Leaf {
        depth: leaf.depth,
        reason: leaf.reason,
        text: Printer::compact().print_pattern(&pattern),
    }
}

fn execute(backend: &mut Backend, program: &str, assume_state_defined: bool) -> Vec<Leaf> {
    let state = parse_pattern(&top(program)).unwrap();
    backend
        .execute(ExecuteRequest {
            assume_state_defined,
            result_modality: ResultModalityOutput::PathSet,
            max_depth: Some(4),
            ..ExecuteRequest::new(state)
        })
        .unwrap()
        .leaves
        .into_iter()
        .map(leaf)
        .collect()
}

fn op(name: &str, argument: &str) -> String {
    seq(&format!("Lbl{name}{{}}({argument})"))
}

/// Why `leaves` fail the contract, if they do: every leaf past the rule's step implies
/// `X =/=Int 0`, and the rule either steps or halts Indeterminate.
fn nonzero_violation(case: &str, leaves: &[Leaf]) -> Option<String> {
    let dropped = leaves
        .iter()
        .any(|leaf| leaf.depth > 0 && !leaf.text.contains(X_NONZERO));
    let stepped_or_indeterminate = leaves.iter().any(|leaf| leaf.depth > 0)
        || leaves
            .iter()
            .all(|leaf| leaf.reason == HaltReasonOutput::Indeterminate);
    (dropped || !stepped_or_indeterminate).then(|| {
        format!(
            "{case}: {}: {leaves:#?}",
            if dropped {
                "a leaf past the step drops X =/=Int 0"
            } else {
                "neither a step nor an Indeterminate halt"
            }
        )
    })
}

fn assert_no_violation(violations: &[String]) {
    assert!(violations.is_empty(), "{}", violations.join("\n"));
}

#[test]
fn hook_shortcuts_keep_the_definedness_of_a_symbolic_argument() {
    let mut backend = backend();
    let mut violations = Vec::new();
    for name in HOOK_SHORTCUTS {
        for assume in [false, true] {
            let leaves = execute(&mut backend, &op(name, X), assume);
            violations.extend(nonzero_violation(
                &format!("{name}(X) assume={assume}"),
                &leaves,
            ));
        }
    }
    assert_no_violation(&violations);
}

#[test]
fn a_hook_shortcut_in_the_initial_state_keeps_its_argument_definedness() {
    let mut backend = backend();
    let program = seq(&format!(
        "Lblnopb{{}}(Lbl'UndsEqlsEqls'Int'Unds'{{}}({}, {}))",
        div(X),
        div(X)
    ));
    let leaves = execute(&mut backend, &program, false);
    assert_no_violation(&Vec::from_iter(nonzero_violation(
        "nopb(10/X ==Int 10/X)",
        &leaves,
    )));
}

#[test]
fn a_plain_partial_right_hand_side_keeps_its_obligation() {
    let mut backend = backend();
    let mut violations = Vec::new();
    for assume in [false, true] {
        let leaves = execute(&mut backend, &op("rhsdiv", X), assume);
        violations.extend(nonzero_violation(
            &format!("rhsdiv(X) assume={assume}"),
            &leaves,
        ));
    }
    assert_no_violation(&violations);
}

#[test]
fn a_solver_splits_a_requires_hook_shortcut_like_the_ground_run() {
    let mut backend = backend();
    if !backend.capabilities().smt {
        return;
    }
    let mut violations = Vec::new();
    for name in REQUIRES {
        let leaves = execute(&mut backend, &op(name, X), false);
        let stuck_at_zero = leaves.iter().any(|leaf| {
            leaf.depth == 0
                && leaf.reason == HaltReasonOutput::Stuck
                && leaf.text.contains(X_ZERO)
                && !leaf.text.contains(X_NONZERO)
        });
        let stepped = leaves
            .iter()
            .any(|leaf| leaf.depth == 1 && leaf.text.contains(X_NONZERO));
        if !stuck_at_zero || !stepped {
            violations.push(format!(
                "{name}(X): expected a Stuck leaf under X = 0 and a step under X =/=Int 0: \
                 {leaves:#?}"
            ));
        }
    }
    assert_no_violation(&violations);
}

/// Operations whose condition relies on the definedness of `10 /Int A` without a hook
/// shortcut: a solver decides it, or the simplifier splits it into a disjunction.
const CONDITIONS: [&str; 4] = ["lt", "orx", "andx", "enslt"];
/// Of those, the ones whose `requires` excludes `A = 0`.
const CONDITION_REQUIRES: [&str; 3] = ["lt", "orx", "andx"];

#[test]
fn a_condition_keeps_the_definedness_of_its_terms() {
    let mut backend = backend();
    let mut violations = Vec::new();
    for name in CONDITIONS {
        for assume in [false, true] {
            let leaves = execute(&mut backend, &op(name, X), assume);
            violations.extend(nonzero_violation(
                &format!("{name}(X) assume={assume}"),
                &leaves,
            ));
        }
    }
    assert_no_violation(&violations);
}

#[test]
fn a_solver_splits_a_partial_requires_like_the_ground_run() {
    let mut backend = backend();
    if !backend.capabilities().smt {
        return;
    }
    let mut violations = Vec::new();
    for name in CONDITION_REQUIRES {
        let leaves = execute(&mut backend, &op(name, X), false);
        // The remainder negates an applicability whose first conjunct is `X =/=Int 0`, so
        // `X = 0` satisfies it.
        let remainder = format!(
            "\\not{{SortGeneratedTopCell{{}}}}(\\and{{SortGeneratedTopCell{{}}}}({X_NONZERO}, "
        );
        let stuck_at_zero = leaves.iter().any(|leaf| {
            leaf.depth == 0
                && leaf.reason == HaltReasonOutput::Stuck
                && leaf.text.contains(&remainder)
        });
        let stepped = leaves
            .iter()
            .any(|leaf| leaf.depth == 1 && leaf.text.contains(X_NONZERO));
        if !stuck_at_zero || !stepped {
            violations.push(format!(
                "{name}(X): expected a Stuck remainder admitting X = 0 and a step under \
                 X =/=Int 0: {leaves:#?}"
            ));
        }
    }
    assert_no_violation(&violations);
}

#[test]
fn a_ceil_free_requires_yields_the_same_leaves() {
    let mut backend = backend();
    let leaves = execute(&mut backend, &op("divok", X), false);
    if backend.capabilities().smt {
        // `X =/=Int 0` is the requires itself: the step carries it once and nothing else, and
        // the remainder is `X = 0`.
        assert!(
            matches!(leaves.as_slice(), [stuck, step]
                if stuck.depth == 0 && stuck.reason == HaltReasonOutput::Stuck
                    && step.depth == 1 && step.text.matches(X_NONZERO).count() == 1)
                || matches!(leaves.as_slice(), [step, stuck]
                if stuck.depth == 0 && stuck.reason == HaltReasonOutput::Stuck
                    && step.depth == 1 && step.text.matches(X_NONZERO).count() == 1),
            "divok(X): expected a step under X =/=Int 0 and a Stuck remainder: {leaves:#?}"
        );
    } else {
        // No solver decides `X =/=Int 0`.
        assert!(
            matches!(leaves.as_slice(), [leaf] if leaf.depth == 0
                && leaf.reason == HaltReasonOutput::Indeterminate),
            "divok(X): expected an Indeterminate requires: {leaves:#?}"
        );
    }
    let ground = execute(&mut backend, &op("divok", "\\dv{SortInt{}}(\"5\")"), false);
    assert!(
        matches!(ground.as_slice(), [leaf] if leaf.depth == 1
            && leaf.text.contains("Lblval{}(\\dv{SortInt{}}(\"2\"))")),
        "divok(5): expected one step to val(2): {ground:#?}"
    );
}

/// `f(X) => 1 requires 10 /Int X <=Int 10 /Int X` holds only on `X =/=Int 0`, so it rewrites
/// `f(X)` where that is known and leaves `f(X)` alone otherwise.
#[test]
fn an_equation_requires_keeps_the_definedness_of_its_terms() {
    let mut backend = backend();
    let one = "Lblval{}(\\dv{SortInt{}}(\"1\"))";
    let unevaluated = "Lblval{}(Lblf{}(X:SortInt{}))";
    for assume in [false, true] {
        let leaves = execute(&mut backend, &op("eqf", X), assume);
        assert!(
            leaves
                .iter()
                .any(|leaf| leaf.depth == 1 && leaf.text.contains(unevaluated))
                && !leaves.iter().any(|leaf| leaf.text.contains(one)),
            "eqf(X) assume={assume}: f(X) must stay unevaluated: {leaves:#?}"
        );
        // The rule's own `requires A =/=Int 0` needs a solver to be decided.
        if backend.capabilities().smt {
            let leaves = execute(&mut backend, &op("eqfk", X), assume);
            assert!(
                leaves
                    .iter()
                    .any(|leaf| leaf.depth == 1 && leaf.text.contains(one))
                    && !leaves.iter().any(|leaf| leaf.text.contains(unevaluated)),
                "eqfk(X) assume={assume}: f(X) must become 1 under X =/=Int 0: {leaves:#?}"
            );
        }
    }
}

/// `f(0)` is left unevaluated (its only equation needs `10 /Int 0` defined), so the ground
/// `requires f(0) <=Int f(0)` is undecided by evaluation and must reach any solver with
/// `\ceil(f(0))`: no step may happen without it.
#[test]
fn a_ground_condition_over_an_unevaluated_partial_term_keeps_its_obligation() {
    let mut backend = backend();
    for assume in [false, true] {
        let leaves = execute(&mut backend, &op("gnd", X), assume);
        assert!(
            leaves
                .iter()
                .all(|leaf| leaf.depth == 0 || leaf.text.contains("\\ceil")),
            "gnd(X) assume={assume}: a step dropped \\ceil(f(0)): {leaves:#?}"
        );
    }
}

#[test]
fn ground_zero_is_stuck_or_trivial() {
    let mut backend = backend();
    for name in HOOK_SHORTCUTS.into_iter().chain(CONDITIONS) {
        let leaves = execute(&mut backend, &op(name, ZERO), false);
        let expected = if REQUIRES.contains(&name) || CONDITION_REQUIRES.contains(&name) {
            HaltReasonOutput::Stuck
        } else {
            HaltReasonOutput::Trivial
        };
        assert!(
            matches!(leaves.as_slice(), [leaf] if leaf.depth == 0 && leaf.reason == expected),
            "{name}(0): expected one {expected:?} leaf at depth 0: {leaves:#?}"
        );
    }
}

/// A `#let` binds its argument through a generated lambda whose only equation equates the
/// application with the body, so a condition or right-hand side over `#let Y = A #in 10 /Int Y`
/// is defined exactly where `10 /Int A` is: its leaves must keep `X =/=Int 0` as the plain
/// operations `lt` and `rhsdiv` do. The instances `X = 0` do not step: `letlt(0)` is Stuck (the
/// `requires` is undefined, so the rule does not apply) and `letrhs(0)` is an undefined step
/// (Trivial), as is the symbolic `letrhs(X)` under `X = 0`.
///
/// Both builds' rule grammars parse `#let`, so these operations are compiled with and without
/// Z3 inference; only the solver-dependent test needs Z3.
mod generated_lambda {
    use super::*;

    const LET_RULES: &str = r#"  syntax Op ::= letlt(Int)  [symbol(letlt)]
              | letrhs(Int) [symbol(letrhs)]
  rule [letlt]:   seq(letlt(A), P) => P requires (#let Y = A #in 10 /Int Y) <=Int (#let Y = A #in 10 /Int Y)
  rule [letrhs]:  seq(letrhs(A), P) => seq(val(#let Y = A #in 10 /Int Y), P)
endmodule
"#;

    /// As the outer `backend`, over `SOURCE` extended by `LET_RULES`.
    fn backend() -> Backend {
        static KORE: shared::Shared<String> = shared::Shared::new();
        backend_over(&KORE.get(|| {
            let source = SOURCE
                .trim_end()
                .strip_suffix("endmodule")
                .expect("the probe source ends with its main module");
            compile(&format!("{source}{LET_RULES}"))
        }))
    }

    #[test]
    fn a_let_bound_partial_body_keeps_its_definedness() {
        let mut backend = backend();
        let mut violations = Vec::new();
        for name in ["letlt", "letrhs"] {
            for assume in [false, true] {
                let leaves = execute(&mut backend, &op(name, X), assume);
                violations.extend(nonzero_violation(
                    &format!("{name}(X) assume={assume}"),
                    &leaves,
                ));
            }
        }
        assert_no_violation(&violations);
    }

    #[test]
    fn a_solver_splits_a_let_bound_partial_requires_like_the_ground_run() {
        let mut backend = backend();
        if !backend.capabilities().smt {
            return;
        }
        let leaves = execute(&mut backend, &op("letlt", X), false);
        let remainder = format!(
            "\\not{{SortGeneratedTopCell{{}}}}(\\and{{SortGeneratedTopCell{{}}}}({X_NONZERO}, "
        );
        assert!(
            leaves.iter().any(|leaf| leaf.depth == 0
                && leaf.reason == HaltReasonOutput::Stuck
                && leaf.text.contains(&remainder))
                && leaves
                    .iter()
                    .any(|leaf| leaf.depth == 1 && leaf.text.contains(X_NONZERO)),
            "letlt(X): expected a Stuck remainder admitting X = 0 and a step under X =/=Int 0: \
             {leaves:#?}"
        );
        let ground = execute(&mut backend, &op("letlt", ZERO), false);
        assert!(
            matches!(ground.as_slice(), [leaf] if leaf.depth == 0
                && leaf.reason == HaltReasonOutput::Stuck),
            "letlt(0): expected one Stuck leaf at depth 0: {ground:#?}"
        );
    }
}

/// A request's own constraints are read with the definedness of each atom stated where the atom
/// stands, an equivalence (`Admitted`), so k-rust decides nothing on the instances where a term
/// of the constraint is undefined as a solver that reads `/Int` as a total operation would.
///
/// In `pos(X, Y) /\ \not(X /Int Y >Int 5) /\ \not(X /Int Y <=Int 5)` each atom `\equals(true, b)`
/// is `\bottom` where `Y = 0`, so its negation holds there: the pattern denotes the `Y = 0`
/// instances of `pos(X, Y)`, on which the rule's `requires` is undefined, so they are stuck.
/// `\equals(X /Int Y, X /Int Y +Int 1)` holds exactly where both sides are undefined (`Y = 0`).
mod request_constraints {
    use k_rust::{
        backend::{
            Backend, BackendError, ExecuteRequest, HaltReasonOutput, ImplicationRequest,
            PatternRequest, ResultModalityOutput, SearchRequest,
        },
        kore::{ast::Pattern as KorePattern, codec, parser::parse_pattern, printer::Printer},
    };
    use k_rust_backend::{
        externalize, smt::Satisfiability, stop::StopCause, substitution::Substitution,
    };

    use super::shared;

    /// The probe definition of the request (`UNSATDEF`), named as `super::compile` expects.
    const SOURCE: &str = r#"module DEFPROBE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Res ::= yes(Int) [symbol(yes)]
               | done() [symbol(done)]
               | pos(Int, Int) [symbol(pos)]
               | pos3(Int, Int, Int) [symbol(pos3)]
               | ens(Int, Int) [symbol(ens)]
               | rhs(Int, Int) [symbol(rhs)]
               | sti(Int) [symbol(sti)]
               | a() [symbol(a)] | b() [symbol(b)] | c() [symbol(c)]
endmodule

module DEFPROBE
  imports DEFPROBE-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> .K </k>

  rule [pos]: pos(X, Y) => yes(X /Int Y) requires X /Int Y >Int 0
  rule [pos3]: pos3(X, Y, _Z) => yes(X /Int Y) requires X /Int Y >Int 0
  rule [ens]: ens(X, Y) => done() ensures X /Int Y >Int 0
  rule [rhs]: rhs(X, Y) => yes(X /Int Y)
  rule [sti-a]: sti(I) => a() requires I >Int 5
  rule [sti-b]: sti(I) => b() requires I <=Int 5
  rule [sti-c]: sti(_) => c() [owise]
endmodule
"#;

    const SORT: &str = "SortGeneratedTopCell{}";
    const X: &str = "X:SortInt{}";
    const Y: &str = "Y:SortInt{}";

    fn backend() -> Backend {
        static KORE: shared::Shared<String> = shared::Shared::new();
        super::backend_over(&KORE.get(|| super::compile(SOURCE)))
    }

    fn top(program: &str) -> String {
        format!(
            "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortRes{{}}, SortKItem{{}}}}({program}), dotk{{}}())), Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\")))"
        )
    }

    fn and(left: &str, right: &str) -> String {
        format!("\\and{{{SORT}}}({left}, {right})")
    }

    fn not(predicate: &str) -> String {
        format!("\\not{{{SORT}}}({predicate})")
    }

    fn holds(term: &str) -> String {
        format!("\\equals{{SortBool{{}}, {SORT}}}(\\dv{{SortBool{{}}}}(\"true\"), {term})")
    }

    fn int(value: i64) -> String {
        format!("\\dv{{SortInt{{}}}}(\"{value}\")")
    }

    fn quotient() -> String {
        format!("Lbl'UndsSlsh'Int'Unds'{{}}({X}, {Y})")
    }

    fn greater(left: &str, right: &str) -> String {
        format!("Lbl'Unds-GT-'Int'Unds'{{}}({left}, {right})")
    }

    fn at_most(left: &str, right: &str) -> String {
        format!("Lbl'Unds-LT-Eqls'Int'Unds'{{}}({left}, {right})")
    }

    fn pos() -> String {
        top(&format!("Lblpos{{}}({X}, {Y})"))
    }

    /// `\not(X /Int Y >Int 5) /\ \not(X /Int Y <=Int 5)`, which holds exactly where `Y = 0`.
    fn negated_atoms() -> String {
        and(
            &not(&holds(&greater(&quotient(), &int(5)))),
            &not(&holds(&at_most(&quotient(), &int(5)))),
        )
    }

    /// `\equals(X /Int Y, X /Int Y +Int 1)`, which holds exactly where `Y = 0`.
    fn undefined_equality() -> String {
        format!(
            "\\equals{{SortInt{{}}, {SORT}}}({}, Lbl'UndsPlus'Int'Unds'{{}}({}, {}))",
            quotient(),
            quotient(),
            int(1)
        )
    }

    /// The caller pattern: `pos(X, Y)` under [`negated_atoms`].
    fn caller_pattern() -> String {
        and(&pos(), &negated_atoms())
    }

    fn parse(text: &str) -> KorePattern {
        parse_pattern(text).unwrap()
    }

    fn print(pattern: &KorePattern) -> String {
        Printer::compact().print_pattern(pattern)
    }

    #[derive(Debug)]
    #[allow(
        dead_code,
        reason = "the payload is read through Debug in a failure message"
    )]
    enum ProbeError {
        Backend(BackendError),
        Stop(StopCause),
    }

    impl From<BackendError> for ProbeError {
        fn from(error: BackendError) -> Self {
            Self::Backend(error)
        }
    }

    impl From<StopCause> for ProbeError {
        fn from(cause: StopCause) -> Self {
            Self::Stop(cause)
        }
    }

    /// The solver's answer on the constraints of `pattern` as a client reads them back:
    /// admitted, internalized, and given to `is_sat`.
    fn satisfiability(backend: &mut Backend, pattern: &KorePattern) -> String {
        backend
            .with_solver(None, |definition, solver| -> Result<String, ProbeError> {
                let internal = definition
                    .admit_unverified(pattern, &[])
                    .internalize_pattern()
                    .map_err(|error| BackendError(error.to_string()))?;
                if internal.constraints.is_empty() {
                    return Ok("no constraints".into());
                }
                Ok(
                    match solver.is_sat(&internal.constraints, &Substitution::new()) {
                        Ok(Ok(Satisfiability::Sat)) => "sat".into(),
                        Ok(Ok(Satisfiability::Unsat)) => "unsat".into(),
                        Ok(Ok(Satisfiability::Unknown(reason))) => format!("unknown {reason}"),
                        Ok(Err(error)) => format!("error {error:?}"),
                        Err(stop) => {
                            stop.forgo_refinement();
                            "stopped".into()
                        }
                    },
                )
            })
            .unwrap()
    }

    struct Leaf {
        depth: u64,
        reason: HaltReasonOutput,
        state: KorePattern,
    }

    impl std::fmt::Debug for Leaf {
        fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(
                formatter,
                "depth {} {:?}: {}",
                self.depth,
                self.reason,
                print(&self.state)
            )
        }
    }

    fn execute(backend: &mut Backend, pattern: &str, assume_state_defined: bool) -> Vec<Leaf> {
        backend
            .execute(ExecuteRequest {
                assume_state_defined,
                result_modality: ResultModalityOutput::PathSet,
                max_depth: Some(4),
                ..ExecuteRequest::new(parse(pattern))
            })
            .unwrap()
            .leaves
            .into_iter()
            .map(|leaf| Leaf {
                depth: leaf.depth,
                reason: leaf.reason,
                state: codec::from_value(&leaf.state).unwrap(),
            })
            .collect()
    }

    fn implies_bottom(backend: &mut Backend, antecedent: &str) -> String {
        backend
            .implies(ImplicationRequest::new(
                parse(antecedent),
                parse(&format!("\\bottom{{{SORT}}}()")),
            ))
            .unwrap()
            .status
    }

    /// `pattern` executed with both `assume_state_defined` values is one Stuck leaf at depth 0
    /// whose constraints the solver finds satisfiable.
    fn assert_one_stuck_initial_leaf(backend: &mut Backend, case: &str, pattern: &str) {
        for assume in [false, true] {
            let leaves = execute(backend, pattern, assume);
            let [leaf] = leaves.as_slice() else {
                panic!("{case} assume={assume}: expected one leaf: {leaves:#?}");
            };
            assert!(
                leaf.depth == 0 && leaf.reason == HaltReasonOutput::Stuck,
                "{case} assume={assume}: expected a Stuck leaf at depth 0: {leaves:#?}"
            );
            let answer = satisfiability(backend, &leaf.state);
            assert_eq!(answer, "sat", "{case} assume={assume}: {leaves:#?}");
        }
    }

    #[test]
    fn a_negated_partial_atom_in_the_request_keeps_its_undefined_instances() {
        let mut backend = backend();
        if !backend.capabilities().smt {
            return;
        }
        assert_one_stuck_initial_leaf(&mut backend, "caller pattern", &caller_pattern());
    }

    #[test]
    fn the_same_request_searched_returns_its_stuck_state() {
        let mut backend = backend();
        if !backend.capabilities().smt {
            return;
        }
        let response = backend
            .search(SearchRequest::new(parse(&caller_pattern())))
            .unwrap();
        assert!(
            response.states.len() == 1 && response.incomplete.is_empty(),
            "expected one final state and no incomplete entry: {response:#?}"
        );
        let state: KorePattern = codec::from_value(&response.states[0].state).unwrap();
        assert!(
            response.states[0].depth == 0 && print(&state).contains("Lblpos{}"),
            "expected the stuck pos(X, Y): {}",
            print(&state)
        );
    }

    #[test]
    fn an_implication_from_a_negated_partial_atom_is_not_vacuously_valid() {
        let mut backend = backend();
        if !backend.capabilities().smt {
            return;
        }
        let status = implies_bottom(&mut backend, &caller_pattern());
        assert_ne!(status, "valid", "pos(X, Y) has instances where Y = 0");
        // Control: `yes(X /Int Y)` is undefined exactly where the constraints hold.
        let control = and(
            &top(&format!("Lblyes{{}}({})", quotient())),
            &negated_atoms(),
        );
        assert_eq!(implies_bottom(&mut backend, &control), "valid");
    }

    #[test]
    fn simplify_keeps_a_request_with_a_negated_partial_atom() {
        let mut backend = backend();
        if !backend.capabilities().smt {
            return;
        }
        let simplified = backend
            .simplify(PatternRequest::new(parse(&caller_pattern())))
            .unwrap();
        let simplified: KorePattern = codec::from_value(&simplified).unwrap();
        assert!(
            !matches!(simplified, KorePattern::Bottom { .. }),
            "the pattern has instances where Y = 0: {}",
            print(&simplified)
        );
    }

    #[test]
    fn get_model_of_a_negated_partial_atom_is_unknown() {
        let mut backend = backend();
        if !backend.capabilities().smt {
            return;
        }
        for (case, pattern) in [
            ("pattern", caller_pattern()),
            ("predicate", negated_atoms()),
        ] {
            let model = backend
                .get_model(PatternRequest::new(parse(&pattern)))
                .unwrap();
            assert_eq!(model.satisfiable, "unknown", "{case}: {model:?}");
        }
    }

    #[test]
    fn a_request_equality_of_two_undefined_terms_holds_where_both_are_undefined() {
        let mut backend = backend();
        if !backend.capabilities().smt {
            return;
        }
        let pattern = and(&pos(), &undefined_equality());
        assert_one_stuck_initial_leaf(&mut backend, "pos(X, Y) /\\ X/Y = X/Y + 1", &pattern);
        let status = implies_bottom(&mut backend, &pattern);
        assert_ne!(status, "valid", "pos(X, Y) has instances where Y = 0");
    }

    /// The one request route that internalizes outside `Admitted`: the argument of a `\not`
    /// consequent. `pos(X, Y)` and `pos(X, Y) /\ X/Y = X/Y + 1` share the instances `Y = 0`, so
    /// `pos(X, Y) -> \not(pos(X, Y) /\ X/Y = X/Y + 1)` is not valid.
    #[test]
    fn a_negated_consequent_with_a_request_equality_is_not_vacuously_valid() {
        let mut backend = backend();
        if !backend.capabilities().smt {
            return;
        }
        let consequent = not(&and(&pos(), &undefined_equality()));
        let result = backend
            .implies(ImplicationRequest::new(parse(&pos()), parse(&consequent)))
            .unwrap();
        assert_ne!(result.status, "valid", "{result:?}");
    }

    #[test]
    fn a_positive_partial_atom_in_the_request_leaves_no_empty_remainder() {
        let mut backend = backend();
        if !backend.capabilities().smt {
            return;
        }
        let pattern = and(&pos(), &holds(&greater(&quotient(), &int(0))));
        for assume in [false, true] {
            let leaves = execute(&mut backend, &pattern, assume);
            assert!(
                matches!(leaves.as_slice(), [leaf] if leaf.depth == 1
                    && print(&leaf.state).contains("Lblyes{}")),
                "assume={assume}: expected the one step to yes(X /Int Y): {leaves:#?}"
            );
        }
    }

    /// Admitting a leaf a run printed gives internal constraints that admitting their printed
    /// form again leaves unchanged: the definedness-explicit form is a fixed point.
    #[test]
    fn a_printed_leaf_admits_back_to_its_own_constraints() {
        let mut backend = backend();
        let mut programs = ["pos", "ens", "rhs"]
            .map(|name| top(&format!("Lbl{name}{{}}({X}, {Y})")))
            .to_vec();
        programs.push(top(&format!("Lblsti{{}}({})", quotient())));
        programs.push(caller_pattern());
        programs.push(and(&pos(), &undefined_equality()));
        programs.push(and(&pos(), &holds(&greater(&quotient(), &int(0)))));
        let mut checked = 0;
        for program in &programs {
            for assume in [false, true] {
                for leaf in execute(&mut backend, program, assume) {
                    // An empty leaf has no term to admit.
                    if matches!(leaf.state, KorePattern::Bottom { .. }) {
                        continue;
                    }
                    let (first, second) = backend
                        .with_solver(None, |definition, _| -> Result<_, ProbeError> {
                            let admit = |pattern: &KorePattern| {
                                definition
                                    .admit_unverified(pattern, &[])
                                    .internalize_pattern()
                                    .map_err(|error| BackendError(error.to_string()))
                            };
                            let first = admit(&leaf.state)?;
                            let second = admit(&externalize::constrained_pattern(&first))?;
                            Ok((
                                format!("{:?}", first.constraints),
                                format!("{:?}", second.constraints),
                            ))
                        })
                        .unwrap();
                    assert_eq!(first, second, "{leaf:?}");
                    checked += 1;
                }
            }
        }
        assert!(checked >= programs.len(), "{checked}");
    }

    const Z: &str = "Z:SortInt{}";
    const W: &str = "W:SortInt{}";

    fn equals(left: &str, right: &str) -> String {
        format!("\\equals{{SortInt{{}}, {SORT}}}({left}, {right})")
    }

    fn times_zero(term: &str) -> String {
        format!("Lbl'UndsStar'Int'Unds'{{}}({term}, {})", int(0))
    }

    fn pos3() -> String {
        top(&format!("Lblpos3{{}}({X}, {Y}, {Z})"))
    }

    /// `\not(X /Int Z *Int 0 = X /Int Y *Int 0)` beside `\not(Z = 0)`, which shows its left side
    /// defined: where `Z` is 1 and `Y` is 0 the left side is 0 and the right side undefined, so
    /// the equality is false and its negation holds.
    fn one_side_shown() -> String {
        and(
            &not(&equals(Z, &int(0))),
            &not(&equals(
                &times_zero(&format!("Lbl'UndsSlsh'Int'Unds'{{}}({X}, {Z})")),
                &times_zero(&quotient()),
            )),
        )
    }

    /// An equality of which only one side is shown defined by the conjuncts beside it is stated
    /// in its faithful form, so `pos3(X, Y, Z)` under [`one_side_shown`] keeps its stuck
    /// instances where `Z` is 1 and `Y` is 0 on every route: alone, under a disjunction, and as
    /// the argument of a `\not` consequent.
    #[test]
    fn an_equality_with_one_side_shown_defined_keeps_its_undefined_instances() {
        let mut backend = backend();
        if !backend.capabilities().smt {
            return;
        }
        let pattern = and(&pos3(), &one_side_shown());
        assert_ne!(implies_bottom(&mut backend, &pattern), "valid");
        assert_one_stuck_initial_leaf(&mut backend, "pos3 under one side shown", &pattern);
        let simplified: KorePattern = codec::from_value(
            &backend
                .simplify(PatternRequest::new(parse(&pattern)))
                .unwrap(),
        )
        .unwrap();
        assert!(
            !matches!(simplified, KorePattern::Bottom { .. }),
            "{}",
            print(&simplified)
        );
        let model = backend
            .get_model(PatternRequest::new(parse(&pattern)))
            .unwrap();
        assert_eq!(model.satisfiable, "unknown", "{model:?}");
        // Under a disjunction: the instances where `Z` is 1 and `Y` is 0 lie outside `Y = 5`.
        let five = equals(Y, &int(5));
        let disjunction = and(
            &pos3(),
            &format!("\\or{{{SORT}}}({five}, {})", one_side_shown()),
        );
        let result = backend
            .implies(ImplicationRequest::new(
                parse(&disjunction),
                parse(&and(&pos3(), &five)),
            ))
            .unwrap();
        assert_ne!(result.status, "valid", "{result:?}");
        // As the argument of a `\not` consequent: `pos3(X, 0, 1)` lies inside it.
        let instance = and(&and(&pos3(), &equals(Y, &int(0))), &equals(Z, &int(1)));
        let result = backend
            .implies(ImplicationRequest::new(
                parse(&instance),
                parse(&not(&pattern)),
            ))
            .unwrap();
        assert_ne!(result.status, "valid", "{result:?}");
    }

    /// `X /Int D ==Int 3` is undefined exactly where `D` is 0, so
    /// `\not(true = X /Int D ==Int 3) /\ \not(false = X /Int D ==Int 3)` holds exactly there.
    fn undefined_only(divisor: &str) -> String {
        let atom = format!(
            "Lbl'UndsEqlsEqls'Int'Unds'{{}}(Lbl'UndsSlsh'Int'Unds'{{}}({X}, {divisor}), {})",
            int(3)
        );
        and(
            &not(&holds(&atom)),
            &not(&format!(
                "\\equals{{SortBool{{}}, {SORT}}}(\\dv{{SortBool{{}}}}(\"false\"), {atom})"
            )),
        )
    }

    /// Requests with instances, each of which a solver that read `/Int` as a total operation
    /// found empty: a quantifier over the partial term, a guard beside a binder that shadows its
    /// variable, implications whose premises are undefined atoms, and an equality over two
    /// different partial terms.
    #[test]
    fn requests_over_quantifiers_implications_and_two_partial_terms_are_not_vacuously_valid() {
        let mut backend = backend();
        if !backend.capabilities().smt {
            return;
        }
        let premise = |atom: &str| format!("\\implies{{{SORT}}}({atom}, {})", equals(Y, &int(1)));
        let quotient_is_three =
            format!("Lbl'UndsEqlsEqls'Int'Unds'{{}}({}, {})", quotient(), int(3));
        let cases = [
            (
                "a guard beside a binder that shadows it",
                and(
                    &and(&pos(), &not(&equals(W, &int(0)))),
                    &format!("\\exists{{{SORT}}}({W}, {})", undefined_only(W)),
                ),
            ),
            (
                "a universal over the partial term",
                and(
                    &pos(),
                    &format!("\\forall{{{SORT}}}({W}, {})", not(&equals(W, &quotient()))),
                ),
            ),
            (
                "implications with undefined premises",
                and(
                    &and(
                        &and(&pos(), &premise(&holds(&quotient_is_three))),
                        &premise(&format!(
                            "\\equals{{SortBool{{}}, {SORT}}}(\\dv{{SortBool{{}}}}(\"false\"), {quotient_is_three})"
                        )),
                    ),
                    &equals(Y, &int(0)),
                ),
            ),
            (
                "an equality over two different partial terms",
                and(
                    &pos3(),
                    &not(&equals(
                        &times_zero(&format!("Lbl'UndsSlsh'Int'Unds'{{}}({X}, {Z})")),
                        &times_zero(&quotient()),
                    )),
                ),
            ),
        ];
        let wrong = cases
            .iter()
            .filter_map(|(case, antecedent)| {
                let status = implies_bottom(&mut backend, antecedent);
                (status == "valid").then(|| format!("{case}: {status}"))
            })
            .collect::<Vec<_>>();
        assert!(wrong.is_empty(), "{wrong:#?}");
    }

    /// A term-level `\and` denotes the intersection of its operands, `\bottom` where they differ,
    /// so an atom over one has a definedness that its operands' does not state (`Z /\ W` of two
    /// variables is empty unless `Z = W`). A request with such an atom is refused rather than
    /// decided.
    #[test]
    fn a_request_atom_over_a_term_conjunction_is_refused() {
        let mut backend = backend();
        let intersection = format!(
            "Lbl'UndsPlus'Int'Unds'{{}}(\\and{{SortInt{{}}}}({Z}, {W}), {})",
            int(0)
        );
        let pattern = and(&pos3(), &not(&equals(&intersection, &int(0))));
        let result = backend.implies(ImplicationRequest::new(
            parse(&pattern),
            parse(&format!("\\bottom{{{SORT}}}()")),
        ));
        assert!(
            result
                .as_ref()
                .is_err_and(|error| error.0.contains("term-level")),
            "{result:?}"
        );
    }

    /// An `\equals` whose operands are not both terms would be read as the `\iff` of its
    /// operands taken as predicates, with a term read as `t = true`. That is not what
    /// `\equals(B1 /\ B2, false)` (the intersection of two Boolean values, `\bottom` where they
    /// differ) or `\equals(B, \top)` (false, since `Bool` has two elements) mean, so in both
    /// builds such a request is refused, by `execute`, `simplify` and `implies` alike.
    #[test]
    fn a_request_that_equates_a_term_read_as_a_predicate_is_refused() {
        let mut backend = backend();
        let boolean =
            |left: &str, right: &str| format!("\\equals{{SortBool{{}}, {SORT}}}({left}, {right})");
        let (b1, b2) = ("B1:SortBool{}", "B2:SortBool{}");
        let (yes, no) = ("\\dv{SortBool{}}(\"true\")", "\\dv{SortBool{}}(\"false\")");
        let cases = [
            (
                "an intersection equated to false",
                and(
                    &and(&and(&pos(), &boolean(b1, yes)), &boolean(b2, no)),
                    &not(&boolean(&format!("\\and{{SortBool{{}}}}({b1}, {b2})"), no)),
                ),
            ),
            (
                "a variable equated to top",
                and(&pos(), &boolean(b1, "\\top{SortBool{}}()")),
            ),
        ];
        let refused = |result: Result<String, BackendError>| {
            result.is_err_and(|error| error.0.contains("cannot be read faithfully"))
        };
        for (case, pattern) in cases {
            let implies = backend
                .implies(ImplicationRequest::new(
                    parse(&pattern),
                    parse(&format!("\\bottom{{{SORT}}}()")),
                ))
                .map(|result| result.status);
            let execute = backend
                .execute(ExecuteRequest::new(parse(&pattern)))
                .map(|result| format!("{} leaves", result.leaves.len()));
            let simplify = backend
                .simplify(PatternRequest::new(parse(&pattern)))
                .map(|result| result.to_string());
            for (route, result) in [
                ("implies", implies),
                ("execute", execute),
                ("simplify", simplify),
            ] {
                let shown = format!("{result:?}");
                assert!(refused(result), "{case}, {route}: {shown}");
            }
        }
    }

    /// An alias applied in a request is read as its body. With `both(X, Y) := X /\ Y` and
    /// `eqfalse(X, Y) := \equals(X /\ Y, false)` added to the definition, a request whose alias
    /// unfolds to an `\equals` that reads a term as a predicate is refused by `simplify` and
    /// `get_model`, the routes that accept aliases, as the unfolded request is.
    #[test]
    fn a_request_whose_alias_unfolds_to_a_term_read_as_a_predicate_is_refused() {
        static KORE: shared::Shared<String> = shared::Shared::new();
        let kore = KORE.get(|| {
            let aliases = r#"
  alias both{}(SortBool{}, SortBool{}) : SortBool{} where both{}(X:SortBool{}, Y:SortBool{}) := \and{SortBool{}}(X:SortBool{}, Y:SortBool{}) []
  alias eqfalse{R}(SortBool{}, SortBool{}) : R where eqfalse{R}(X:SortBool{}, Y:SortBool{}) := \equals{SortBool{}, R}(\and{SortBool{}}(X:SortBool{}, Y:SortBool{}), \dv{SortBool{}}("false")) []
"#;
            let kore = super::compile(SOURCE);
            let header = "module DEFPROBE\n";
            let at = kore.find(header).expect("the main module") + header.len();
            format!("{}{aliases}{}", &kore[..at], &kore[at..])
        });
        let mut backend = super::backend_over(&kore);
        let boolean =
            |left: &str, right: &str| format!("\\equals{{SortBool{{}}, {SORT}}}({left}, {right})");
        let (b1, b2) = ("B1:SortBool{}", "B2:SortBool{}");
        let (yes, no) = ("\\dv{SortBool{}}(\"true\")", "\\dv{SortBool{}}(\"false\")");
        let facts = and(&and(&pos(), &boolean(b1, yes)), &boolean(b2, no));
        for (case, constraint) in [
            (
                "an alias for the intersection",
                not(&boolean(&format!("both{{}}({b1}, {b2})"), no)),
            ),
            (
                "an alias for the equality",
                not(&format!("eqfalse{{{SORT}}}({b1}, {b2})")),
            ),
        ] {
            let pattern = and(&facts, &constraint);
            let simplify = backend
                .simplify(PatternRequest::new(parse(&pattern)))
                .map(|result| result.to_string());
            let mut routes = vec![("simplify", simplify)];
            // Without a solver `get_model` answers no request.
            if backend.capabilities().smt {
                let model = backend
                    .get_model(PatternRequest::new(parse(&pattern)))
                    .map(|result| format!("{result:?}"));
                routes.push(("get_model", model));
            }
            for (route, result) in routes {
                let shown = format!("{result:?}");
                assert!(
                    result.is_err_and(|error| error.0.contains("cannot be read faithfully")),
                    "{case}, {route}: {shown}"
                );
            }
        }
    }
}
