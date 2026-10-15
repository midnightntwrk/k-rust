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
    confluence::{CheckCounts, ValueClaims},
    definition::BackendDefinition,
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

/// 32 concurrent loads give the verdict of one load alone, for a condition decided within the
/// budget, one over it, and one the former wall-clock deadline decided only on an idle thread.
#[test]
fn the_verdict_does_not_depend_on_concurrency() {
    for big in [SMALL, HUGE, NEAR_THE_FORMER_DEADLINE] {
        let syntax = fixture(big);
        let alone = load(&syntax);
        for (thread, verdict) in concurrent_loads(&syntax, 32).into_iter().enumerate() {
            assert_eq!(
                verdict, alone,
                "slow({big}): thread {thread} of 32 against one load alone"
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
/// corpus by the value-contract gate (`scripts/value-contract-corpus.sh`), whose counts include
/// these.
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
