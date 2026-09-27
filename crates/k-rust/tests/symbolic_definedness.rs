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

fn backend() -> Backend {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("defprobe.k", SOURCE),
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
    let compiled = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    Backend::new(
        &compiled.definition_kore,
        "DEFPROBE",
        BackendOptions::default(),
    )
    .unwrap()
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
    let state = codec::to_value(&parse_pattern(&top(program)).unwrap()).unwrap();
    backend
        .execute(ExecuteRequest {
            state,
            assume_state_defined,
            result_modality: ResultModalityOutput::PathSet,
            max_depth: Some(4),
            ..ExecuteRequest::default()
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
