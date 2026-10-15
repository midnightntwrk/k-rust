//! The load-time critical-pair check (`k_rust_backend::confluence`) simplifies each condition of
//! an overlap within a budget of stop polls, so its verdict is a function of the definition: a
//! condition decided within the budget is decided on every thread and under any load, and one
//! that is not is stopped at the same poll every time.
//!
//! The fixture is an overlap of two `anywhere` equations of the equation head `g`, whose
//! condition calls a terminating function `slow` that recurses `big` times:
//!
//! ```k
//! syntax Int ::= slow(Int) [function]
//! rule slow(0) => 0
//! rule slow(N) => slow(N -Int 1) requires N >Int 0
//! syntax Foo ::= g(Int) | "a" | "b"
//! rule g(_X) => a requires slow(BIG) ==Int 1 [anywhere]
//! rule g(_X) => b [anywhere]
//! ```
//!
//! The overlap must be at a symbol a gate site can be asked about (here an equation head):
//! the load classifies only those pairs (`CheckScope::Gate`), so two overlapping equations of an
//! ordinary function would give no condition to simplify and the tests would hold vacuously.
//! Decided, the condition is `0 ==Int 1`, which refutes the overlap of `g`'s equations (the
//! overlap of `slow`'s two equations reaches no gate symbol and is not classified). Stopped, it
//! decides nothing, so `g`'s pair does not join (`a` against `b`) and the check withdraws the
//! claims of `g` and of `slow`, which its condition calls.

use std::{
    path::Path,
    sync::{Arc, Barrier},
};

use k_rust_backend::{
    confluence::{CheckCounts, CheckScope, ConditionMemo, ValueClaims},
    definition::BackendDefinition,
    nesting::with_simplification_stack_budget,
    stop::CancellationToken,
};
use k_rust_kore::kore::{ast as kore, parser::parse_definition};

const PRELUDE: &str = r#"
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    hooked-symbol subInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.sub"), smt-hook{}("-")]
    hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
    hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
    sort SortFoo{} []
    symbol slow{}(SortInt{}) : SortInt{} [function{}()]
    symbol g{}(SortInt{}) : SortFoo{} [anywhere{}()]
    symbol a{}() : SortFoo{} [constructor{}(), functional{}(), injective{}()]
    symbol b{}() : SortFoo{} [constructor{}(), functional{}(), injective{}()]
"#;

/// A condition the check decides in a handful of polls.
const SMALL: u64 = 100;

/// A condition whose simplification takes far more polls than the check's budget (14 polls per
/// step of `slow`): `slow` would recurse for longer than any load may take.
const HUGE: u64 = 1_000_000_000_000;

/// A condition well within the budget (560,000 polls) that the former one-second wall-clock
/// deadline decided on one thread and stopped on some of 32 concurrent ones: at the parent of
/// this change, in the `dev` profile the tests build (opt-level 1 with debug assertions), it took
/// 0.4 s alone on a 32-CPU workstation, and 32 concurrent loads gave other verdicts than one.
const NEAR_THE_FORMER_DEADLINE: u64 = 40_000;

/// The equation `head(X0, ..., Xn) = right requires requires`, each `Xi` bound to
/// `patterns[i]` of sort `sorts[i]`, with the axiom attributes `attributes`.
fn equation(
    head: &str,
    sorts: &[&str],
    result: &str,
    patterns: &[&str],
    right: &str,
    requires: &str,
    attributes: &str,
) -> String {
    let memberships = sorts.iter().zip(patterns).enumerate().rev().fold(
        r"\top{R}()".to_owned(),
        |rest, (index, (sort, pattern))| {
            format!(r"\and{{R}}(\in{{{sort}, R}}(X{index}:{sort}, {pattern}), {rest})")
        },
    );
    let parameters = sorts
        .iter()
        .enumerate()
        .map(|(index, sort)| format!("X{index}:{sort}"))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        r"axiom{{R}} \implies{{R}}(\and{{R}}({requires}, {memberships}), \equals{{{result}, R}}({head}{{}}({parameters}), \and{{{result}}}({right}, \top{{{result}}}()))) [{attributes}]"
    )
}

fn int(value: u64) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

/// `left` holds as a `requires`: `\equals(left, true)`.
fn holds(left: &str) -> String {
    format!(r#"\equals{{SortBool{{}}, R}}({left}, \dv{{SortBool{{}}}}("true"))"#)
}

/// The fixture's KORE with `slow(big)` in the condition of `g`'s first equation.
fn fixture(big: u64) -> kore::Definition {
    let axioms = [
        equation(
            "slow",
            &["SortInt{}"],
            "SortInt{}",
            &[&int(0)],
            &int(0),
            r"\top{R}()",
            "",
        ),
        equation(
            "slow",
            &["SortInt{}"],
            "SortInt{}",
            &["VarN:SortInt{}"],
            &format!("slow{{}}(subInt{{}}(VarN:SortInt{{}}, {}))", int(1)),
            &holds(&format!("gtInt{{}}(VarN:SortInt{{}}, {})", int(0))),
            "",
        ),
        equation(
            "g",
            &["SortInt{}"],
            "SortFoo{}",
            &["VarX:SortInt{}"],
            "a{}()",
            &holds(&format!("eqInt{{}}(slow{{}}({}), {})", int(big), int(1))),
            "anywhere{}()",
        ),
        equation(
            "g",
            &["SortInt{}"],
            "SortFoo{}",
            &["VarX:SortInt{}"],
            "b{}()",
            r"\top{R}()",
            "anywhere{}()",
        ),
    ];
    let source = format!(
        "[] module MAIN {PRELUDE} {} endmodule []",
        axioms.join("\n")
    );
    parse_definition(&source).expect("the fixture parses")
}

/// What a load's check said: its counts and the symbols whose claims it withdrew.
#[derive(Debug, Eq, PartialEq)]
struct Verdict {
    counts: CheckCounts,
    tainted_symbols: Vec<String>,
}

impl Verdict {
    fn of(claims: &ValueClaims) -> Self {
        Self {
            counts: claims.counts(),
            tainted_symbols: claims
                .tainted_symbols()
                .iter()
                .map(ToString::to_string)
                .collect(),
        }
    }
}

fn load(syntax: &kore::Definition) -> Verdict {
    let definition =
        BackendDefinition::internalize(syntax, "MAIN").expect("the fixture internalizes");
    let verdict = Verdict::of(definition.value_claims());
    // The overlap of `g`'s equations is classified, so the check simplified its condition.
    assert!(
        verdict.counts.simplifier_calls >= 1,
        "the check simplified no condition: {verdict:?}"
    );
    verdict
}

#[test]
fn a_condition_within_the_budget_is_decided() {
    let verdict = load(&fixture(SMALL));
    let counts = verdict.counts;
    assert_eq!(counts.refuted, 1, "{verdict:?}");
    assert_eq!(counts.unjoined, 0, "{verdict:?}");
    assert_eq!(counts.condition_budget_stops, 0, "{verdict:?}");
    assert_eq!(counts.condition_stack_stops, 0, "{verdict:?}");
    assert!(verdict.tainted_symbols.is_empty(), "{verdict:?}");
}

#[test]
fn a_condition_over_the_budget_stops_deterministically() {
    let verdict = load(&fixture(HUGE));
    let counts = verdict.counts;
    assert!(counts.condition_budget_stops >= 1, "{verdict:?}");
    assert_eq!(counts.condition_stack_stops, 0, "{verdict:?}");
    assert_eq!(counts.refuted, 0, "{verdict:?}");
    assert_eq!(counts.unjoined, 1, "{verdict:?}");
    assert_eq!(verdict.tainted_symbols.len(), 2, "{verdict:?}");
    // The stop is at the same poll every time, so a second load says the same.
    assert_eq!(load(&fixture(HUGE)), verdict);
}

/// The verdicts of `syntax` loaded on `threads` threads at once, one per thread.
fn concurrent_loads(syntax: &kore::Definition, threads: usize) -> Vec<Verdict> {
    let start = Arc::new(Barrier::new(threads));
    std::thread::scope(|scope| {
        let loads = (0..threads)
            .map(|_| {
                let start = Arc::clone(&start);
                scope.spawn(move || {
                    start.wait();
                    load(syntax)
                })
            })
            .collect::<Vec<_>>();
        loads
            .into_iter()
            .map(|load| load.join().expect("a load does not panic"))
            .collect()
    })
}

/// Concurrent loads give the verdict of one load alone, for a condition decided within the
/// budget and one the former wall-clock deadline decided only on an idle thread (32 loads each),
/// and for one over the budget (4 loads: each spends a whole budget, and a budget stop does not
/// depend on the clock, so more threads would add cost and no case).
#[test]
fn the_verdict_does_not_depend_on_concurrency() {
    for (big, threads) in [(SMALL, 32), (NEAR_THE_FORMER_DEADLINE, 32), (HUGE, 4)] {
        let syntax = fixture(big);
        let alone = load(&syntax);
        for (thread, verdict) in concurrent_loads(&syntax, threads).into_iter().enumerate() {
            assert_eq!(
                verdict, alone,
                "slow({big}): thread {thread} of {threads} against one load alone"
            );
        }
        if big == NEAR_THE_FORMER_DEADLINE {
            assert_eq!(alone.counts.condition_budget_stops, 0, "{alone:?}");
            assert_eq!(alone.counts.refuted, 1, "{alone:?}");
        }
    }
}

/// The compiled definitions under `tests/fixtures` record no stop of the check. The definitions
/// of this crate's confluence unit tests are checked by their own helpers, and the conformance
/// corpus by the value-contract gate (`scripts/value-contract-corpus.sh`), which expects both
/// counters to be zero.
#[test]
fn the_corpus_definitions_record_no_stops() {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let mut paths = std::fs::read_dir(&fixtures)
        .expect("the fixtures directory is readable")
        .map(|entry| entry.expect("a fixture entry is readable").path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "kore")
        })
        .collect::<Vec<_>>();
    paths.sort();
    assert!(!paths.is_empty(), "no fixture under {}", fixtures.display());
    for path in paths {
        let text = std::fs::read_to_string(&path).expect("the fixture is readable");
        let syntax =
            parse_definition(&text).unwrap_or_else(|error| panic!("{}: {error:?}", path.display()));
        let main = syntax
            .modules
            .last()
            .expect("a definition has a module")
            .name
            .clone();
        let definition = BackendDefinition::internalize(&syntax, &main)
            .unwrap_or_else(|error| panic!("{}: {error:?}", path.display()));
        let counts = definition.value_claims().counts();
        assert_eq!(
            (counts.condition_budget_stops, counts.condition_stack_stops),
            (0, 0),
            "{}: {counts:?}",
            path.display()
        );
    }
}

/// Declarations of the fixtures below: `hk`, a hooked function whose hook this backend does not
/// implement, so that it is evaluated by its equations; `deep`, an ordinary function; the
/// equation heads `g` and `h`.
const HOOK_PRELUDE: &str = r#"
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    hooked-symbol subInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.sub"), smt-hook{}("-")]
    hooked-symbol addInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
    hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
    hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
    hooked-symbol hk{}(SortInt{}) : SortInt{} [function{}(), hook{}("MYHOOK.hk")]
    symbol deep{}(SortInt{}) : SortInt{} [function{}()]
    sort SortFoo{} []
    symbol g{}(SortInt{}) : SortFoo{} [anywhere{}()]
    symbol h{}(SortInt{}) : SortFoo{} [anywhere{}()]
    symbol k{}(SortInt{}) : SortFoo{} [constructor{}(), functional{}(), injective{}()]
    symbol a{}() : SortFoo{} [constructor{}(), functional{}(), injective{}()]
    symbol b{}() : SortFoo{} [constructor{}(), functional{}(), injective{}()]
"#;

/// The equations of a function `head` that recurses `N` levels deep, not in tail position:
/// `head(0) = 0`, `head(N) = head(N -Int 1) +Int 1 requires N >Int 0`.
fn deep_recursion(head: &str) -> [String; 2] {
    [
        equation(
            head,
            &["SortInt{}"],
            "SortInt{}",
            &[&int(0)],
            &int(0),
            r"\top{R}()",
            "",
        ),
        equation(
            head,
            &["SortInt{}"],
            "SortInt{}",
            &["VarN:SortInt{}"],
            &format!(
                "addInt{{}}({head}{{}}(subInt{{}}(VarN:SortInt{{}}, {})), {})",
                int(1),
                int(1)
            ),
            &holds(&format!("gtInt{{}}(VarN:SortInt{{}}, {})", int(0))),
            "",
        ),
    ]
}

/// The two `anywhere` equations `g(_) = k(hk(n))` and `g(_) = k(n)`, whose overlap joins exactly
/// when the join evaluates `hk(n)` to `n`.
fn hook_overlap(n: u64) -> [String; 2] {
    [
        equation(
            "g",
            &["SortInt{}"],
            "SortFoo{}",
            &["VarX:SortInt{}"],
            &format!("k{{}}(hk{{}}({}))", int(n)),
            r"\top{R}()",
            "anywhere{}()",
        ),
        equation(
            "g",
            &["SortInt{}"],
            "SortFoo{}",
            &["VarX:SortInt{}"],
            &format!("k{{}}({})", int(n)),
            r"\top{R}()",
            "anywhere{}()",
        ),
    ]
}

/// The overlap `head(_) = a requires deep(n) ==Int 1` against `head(_) = b`.
fn deep_condition(head: &str, n: u64) -> [String; 2] {
    [
        equation(
            head,
            &["SortInt{}"],
            "SortFoo{}",
            &["VarX:SortInt{}"],
            "a{}()",
            &holds(&format!("eqInt{{}}(deep{{}}({}), {})", int(n), int(1))),
            "anywhere{}()",
        ),
        equation(
            head,
            &["SortInt{}"],
            "SortFoo{}",
            &["VarX:SortInt{}"],
            "b{}()",
            r"\top{R}()",
            "anywhere{}()",
        ),
    ]
}

fn hook_module(axioms: &[String]) -> kore::Definition {
    let source = format!(
        "[] module MAIN {HOOK_PRELUDE} {} endmodule []",
        axioms.join("\n")
    );
    parse_definition(&source).expect("the fixture parses")
}

/// `syntax` internalized on an 8 MiB thread that the simplifier may not extend with stack
/// segments, so that a recursion deeper than that thread's stack stops for lack of stack.
fn internalize_on_a_bounded_stack(syntax: kore::Definition) -> BackendDefinition {
    std::thread::Builder::new()
        .stack_size(8 << 20)
        .spawn(move || {
            with_simplification_stack_budget(0, || {
                BackendDefinition::internalize(&syntax, "MAIN").expect("the fixture internalizes")
            })
        })
        .expect("the loading thread starts")
        .join()
        .expect("the load does not panic")
}

/// The join evaluates `hk(100000)` by `hk`'s equations, recursing 100,000 levels: on a thread
/// whose stack holds fewer, the evaluation stops for lack of stack. The stop is counted, and the
/// overlap is not joined through it.
#[test]
fn a_hook_evaluation_of_the_join_that_runs_out_of_stack_is_counted() {
    let axioms = [deep_recursion("hk"), hook_overlap(100_000)].concat();
    let definition = internalize_on_a_bounded_stack(hook_module(&axioms));
    let verdict = Verdict::of(definition.value_claims());
    assert!(verdict.counts.condition_stack_stops >= 1, "{verdict:?}");
    assert_eq!(verdict.counts.joined, 0, "{verdict:?}");
    assert_eq!(verdict.counts.unjoined, 1, "{verdict:?}");
    assert!(
        verdict.tainted_symbols.iter().any(|symbol| symbol == "g"),
        "{verdict:?}"
    );
}

/// The join evaluates `hk(1)` by `hk(N) = hk(N +Int 1)`, which does not end: the budget stops
/// it, so the load ends, and the stop is counted.
#[test]
fn a_hook_evaluation_of_the_join_that_does_not_end_is_stopped_by_the_budget() {
    let mut axioms = vec![equation(
        "hk",
        &["SortInt{}"],
        "SortInt{}",
        &["VarN:SortInt{}"],
        &format!("hk{{}}(addInt{{}}(VarN:SortInt{{}}, {}))", int(1)),
        r"\top{R}()",
        "",
    )];
    axioms.extend(hook_overlap(1));
    let definition =
        BackendDefinition::internalize(&hook_module(&axioms), "MAIN").expect("the fixture loads");
    let verdict = Verdict::of(definition.value_claims());
    assert!(verdict.counts.condition_budget_stops >= 1, "{verdict:?}");
    assert_eq!(verdict.counts.condition_stack_stops, 0, "{verdict:?}");
    assert_eq!(verdict.counts.unjoined, 1, "{verdict:?}");
}

/// Two equation heads whose overlaps have the same condition, which stops for lack of stack: the
/// memo of condition simplifications answers the second from the first, and counts the first's
/// stop again, so the counts with the memo and without it agree.
#[test]
fn the_stop_counts_do_not_depend_on_the_memo() {
    let axioms = [
        deep_recursion("deep"),
        deep_condition("g", 100_000),
        deep_condition("h", 100_000),
    ]
    .concat();
    let definition = internalize_on_a_bounded_stack(hook_module(&axioms));
    let with_memo = definition.value_claims().counts();
    assert!(with_memo.condition_memo_hits >= 1, "{with_memo:?}");
    assert!(with_memo.condition_stack_stops >= 2, "{with_memo:?}");
    let without_memo = std::thread::Builder::new()
        .stack_size(8 << 20)
        .spawn(move || {
            with_simplification_stack_budget(0, || {
                definition
                    .value_claims_checked(CheckScope::Gate, ConditionMemo::Off)
                    .counts()
            })
        })
        .expect("the checking thread starts")
        .join()
        .expect("the check does not panic");
    assert_eq!(
        with_memo.without_memo_work(),
        without_memo.without_memo_work()
    );
}

/// Declarations beside [`HOOK_PRELUDE`] for the fixtures of the load's discharge and of the
/// definedness of conditions: `p`, a partial function with a ceil equation, and a rewrite rule's
/// sort.
const PARTIAL: &str = r#"
    symbol p{}(SortInt{}) : SortInt{} [function{}()]
    symbol q{}(SortInt{}) : SortInt{} [function{}()]
    sort SortS{} []
    symbol state{}() : SortS{} [constructor{}(), functional{}(), injective{}()]
    symbol done{}(SortInt{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
"#;

fn partial_module(axioms: &[String]) -> kore::Definition {
    let source = format!(
        "[] module MAIN {HOOK_PRELUDE} {PARTIAL} {} endmodule []",
        axioms.join("\n")
    );
    parse_definition(&source).expect("the fixture parses")
}

/// The ceil equation `\ceil(p(X)) = (hk(n) == n)`: `p` is defined where `hk(n)` evaluates to `n`.
fn ceil_of_p(n: u64) -> String {
    format!(
        r"axiom{{R}} \implies{{R}}(\top{{R}}(), \equals{{R, R}}(\ceil{{SortInt{{}}, R}}(p{{}}(X:SortInt{{}})), \equals{{SortInt{{}}, R}}(hk{{}}({}), {}))) []",
        int(n),
        int(n)
    )
}

/// The rewrite rule `state => done(p(0))`, whose right-hand side is defined where `p(0)` is.
const ADVANCE: &str = r#"axiom{} \rewrites{SortS{}}(\and{SortS{}}(state{}(), \top{SortS{}}()), done{}(p{}(\dv{SortInt{}}("0")))) [label{}("advance")]"#;

/// Whether the load discharged the definedness of every rewrite rule.
fn rules_discharged(definition: &BackendDefinition) -> Vec<bool> {
    definition
        .rewrite_theory()
        .values()
        .flat_map(|groups| groups.values())
        .flatten()
        .map(|rule| rule.rule.attributes.preserves_definedness)
        .collect()
}

/// The load discharges `state => done(p(0))` by simplifying the ceil equation's instance
/// `hk(n) == n`. With `n` small it is discharged; with `n` deep, on a thread whose stack holds
/// fewer levels, the simplification stops for lack of stack: the stop is counted and the rule
/// stays undischarged.
#[test]
fn a_discharge_that_runs_out_of_stack_is_counted_and_leaves_the_rule_undischarged() {
    let fixture = |n: u64| {
        let mut axioms = deep_recursion("hk").to_vec();
        axioms.push(ceil_of_p(n));
        axioms.push(ADVANCE.to_owned());
        partial_module(&axioms)
    };
    let small = BackendDefinition::internalize(&fixture(100), "MAIN").expect("the fixture loads");
    assert_eq!(rules_discharged(&small), [true]);
    assert_eq!(small.discharge_counts(), Default::default());
    let deep = internalize_on_a_bounded_stack(fixture(100_000));
    assert_eq!(rules_discharged(&deep), [false]);
    assert!(
        deep.discharge_counts().stack_stops >= 1,
        "{:?}",
        deep.discharge_counts()
    );
    assert_eq!(deep.discharge_counts().budget_stops, 0);
}

/// The ceil equation's instance `hk(1) == 1` under `hk(N) = hk(N +Int 1)` does not end: the
/// budget stops it, so the load ends, the stop is counted and the rule stays undischarged.
#[test]
fn a_discharge_that_does_not_end_is_stopped_by_the_budget() {
    let axioms = [
        equation(
            "hk",
            &["SortInt{}"],
            "SortInt{}",
            &["VarN:SortInt{}"],
            &format!("hk{{}}(addInt{{}}(VarN:SortInt{{}}, {}))", int(1)),
            r"\top{R}()",
            "",
        ),
        ceil_of_p(1),
        ADVANCE.to_owned(),
    ];
    let definition = BackendDefinition::internalize(&partial_module(&axioms), "MAIN")
        .expect("the fixture loads");
    assert_eq!(rules_discharged(&definition), [false]);
    assert!(
        definition.discharge_counts().budget_stops >= 1,
        "{:?}",
        definition.discharge_counts()
    );
    assert_eq!(definition.discharge_counts().stack_stops, 0);
}

/// The overlap `g(_) = a requires p(0) ==Int 1` against `g(_) = b`, with `p(X) = 0`: its condition
/// is refuted once its definedness, the ceil equation's instance `hk(n) == n`, is stated. With
/// `n` deep, on a thread whose stack holds fewer levels, stating that definedness stops for lack
/// of stack: the check counts the stop and the overlap is not refuted through it.
#[test]
fn a_condition_whose_definedness_runs_out_of_stack_is_counted() {
    let fixture = |n: u64| {
        let mut axioms = deep_recursion("hk").to_vec();
        axioms.push(ceil_of_p(n));
        axioms.push(equation(
            "p",
            &["SortInt{}"],
            "SortInt{}",
            &["VarX:SortInt{}"],
            &int(0),
            r"\top{R}()",
            "",
        ));
        axioms.push(equation(
            "g",
            &["SortInt{}"],
            "SortFoo{}",
            &["VarX:SortInt{}"],
            "a{}()",
            &holds(&format!("eqInt{{}}(p{{}}({}), {})", int(0), int(1))),
            "anywhere{}()",
        ));
        axioms.push(equation(
            "g",
            &["SortInt{}"],
            "SortFoo{}",
            &["VarX:SortInt{}"],
            "b{}()",
            r"\top{R}()",
            "anywhere{}()",
        ));
        partial_module(&axioms)
    };
    let small = BackendDefinition::internalize(&fixture(100), "MAIN").expect("the fixture loads");
    let small = Verdict::of(small.value_claims());
    assert_eq!(small.counts.refuted, 1, "{small:?}");
    assert_eq!(small.counts.condition_stack_stops, 0, "{small:?}");
    let deep = internalize_on_a_bounded_stack(fixture(100_000));
    let deep = Verdict::of(deep.value_claims());
    assert!(deep.counts.condition_stack_stops >= 1, "{deep:?}");
    assert_eq!(deep.counts.refuted, 0, "{deep:?}");
}

/// A load inside the scope of a cancelled request token discharges the rule as any other load:
/// the discharge is cached with the definition, so the request that loads it does not reach it.
#[test]
fn a_load_in_a_cancelled_scope_discharges_as_any_other() {
    let mut axioms = deep_recursion("hk").to_vec();
    axioms.push(ceil_of_p(100));
    axioms.push(ADVANCE.to_owned());
    let syntax = partial_module(&axioms);
    let token = CancellationToken::new();
    token.cancel();
    let definition = token
        .scope(|| BackendDefinition::internalize(&syntax, "MAIN"))
        .expect("the fixture loads");
    assert_eq!(rules_discharged(&definition), [true]);
}

/// The overlap `g(_) = k(q(1))` against `g(_) = k(2)`, with `q(X) = 2 requires p(0) ==Int 0` and
/// `p(X) = 0`: the join applies `q`'s equation once it has stated the definedness of its
/// `requires`, the ceil equation's instance `hk(n) == n`. With `n` deep, on a thread whose stack
/// holds fewer levels, stating it stops for lack of stack: the check counts the stop and the join
/// refuses the step, so the pair is not joined through it.
#[test]
fn a_join_step_whose_definedness_runs_out_of_stack_is_counted_and_refused() {
    let fixture = |n: u64| {
        let mut axioms = deep_recursion("hk").to_vec();
        axioms.push(ceil_of_p(n));
        axioms.push(equation(
            "p",
            &["SortInt{}"],
            "SortInt{}",
            &["VarX:SortInt{}"],
            &int(0),
            r"\top{R}()",
            "",
        ));
        axioms.push(equation(
            "q",
            &["SortInt{}"],
            "SortInt{}",
            &["VarX:SortInt{}"],
            &int(2),
            &holds(&format!("eqInt{{}}(p{{}}({}), {})", int(0), int(0))),
            "",
        ));
        for right in [
            format!("k{{}}(q{{}}({}))", int(1)),
            format!("k{{}}({})", int(2)),
        ] {
            axioms.push(equation(
                "g",
                &["SortInt{}"],
                "SortFoo{}",
                &["VarX:SortInt{}"],
                &right,
                r"\top{R}()",
                "anywhere{}()",
            ));
        }
        partial_module(&axioms)
    };
    let small = BackendDefinition::internalize(&fixture(100), "MAIN").expect("the fixture loads");
    let small = Verdict::of(small.value_claims());
    assert_eq!(small.counts.joined, 1, "{small:?}");
    assert_eq!(small.counts.condition_stack_stops, 0, "{small:?}");
    let deep = internalize_on_a_bounded_stack(fixture(100_000));
    let deep = Verdict::of(deep.value_claims());
    assert!(deep.counts.condition_stack_stops >= 1, "{deep:?}");
    assert_eq!(deep.counts.joined, 0, "{deep:?}");
    assert_eq!(deep.counts.unjoined, 1, "{deep:?}");
}
