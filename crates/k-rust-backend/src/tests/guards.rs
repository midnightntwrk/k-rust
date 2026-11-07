//! Guard outcomes (`crate::coverage::guards`): a run that names axioms reports, per node of
//! each one's written `requires`, the outcomes it took where it was reached, the guard outcomes
//! of the entries, and their valuation combinations.
//!
//! The axioms carry labels and no `UNIQUE_ID`, so each one's id is its label. Every run here
//! ends by itself well inside its budget; none depends on a clock.

use std::collections::BTreeSet;

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    coverage::{
        AxiomGuard, Connective, GuardCollection, GuardOutcome, GuardShape, NodeOutcome,
        OperandCause, Refutation, Truth,
    },
    definition::BackendDefinition,
    rewrite::{ExecutionOptions, ExecutionResult, Pattern, execute},
};

const TRUE: &str = r#"\dv{SortBool{}}("true")"#;

fn int(value: i64) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

/// A function equation `head(X) = rhs requires condition` over one `Int` argument; `condition`
/// is a whole predicate.
fn equation(label: &str, head: &str, rhs: &str, condition: &str, attrs: &str) -> String {
    format!(
        r#"
            axiom{{R}} \implies{{R}}(
                \and{{R}}({condition}, \and{{R}}(\in{{SortInt{{}}, R}}(X0:SortInt{{}}, X:SortInt{{}}), \top{{R}}())),
                \equals{{SortInt{{}}, R}}({head}{{}}(X0:SortInt{{}}), \and{{SortInt{{}}}}({rhs}, \top{{SortInt{{}}}}()))
            ) [label{{}}("{label}"){attrs}]"#
    )
}

/// `\equals(b, true)` of a Boolean term, over the sort `R` of an equation.
fn holds_r(b: &str) -> String {
    format!(r"\equals{{SortBool{{}}, R}}({b}, {TRUE})")
}

/// A rewrite rule `lhs => rhs requires b` of sort `SortS`; no condition when `b` is empty.
fn rule(label: &str, lhs: &str, rhs: &str, b: &str, attrs: &str) -> String {
    let requires = if b.is_empty() {
        r"\top{SortS{}}()".to_owned()
    } else {
        format!(r"\equals{{SortBool{{}}, SortS{{}}}}({b}, {TRUE})")
    };
    format!(
        r#"
            axiom{{}} \rewrites{{SortS{{}}}}(
                \and{{SortS{{}}}}({lhs}, {requires}),
                \and{{SortS{{}}}}({rhs}, \top{{SortS{{}}}}())
            ) [label{{}}("{label}"){attrs}]"#,
    )
}

const A: &str = "A:SortInt{}";
const B: &str = "B:SortInt{}";
const X: &str = "X:SortInt{}";

fn definition() -> BackendDefinition {
    let zero = int(0);
    let one = int(1);
    let ten = int(10);
    let axioms = [
        // `A == 0 andThen B == 0`, and the same with `andBool`; a fallback below each.
        rule(
            "andThen",
            &format!("st{{}}({A}, {B})"),
            "halt{}()",
            &format!("andThenBool{{}}(eqInt{{}}({A}, {zero}), eqInt{{}}({B}, {zero}))"),
            r#", priority{}("40")"#,
        ),
        rule(
            "andThenOther",
            &format!("st{{}}({A}, {B})"),
            "fault{}()",
            "",
            r#", priority{}("50")"#,
        ),
        rule(
            "andStrict",
            &format!("sa{{}}({A}, {B})"),
            "halt{}()",
            &format!("andBool{{}}(eqInt{{}}({A}, {zero}), eqInt{{}}({B}, {zero}))"),
            r#", priority{}("40")"#,
        ),
        rule(
            "andStrictOther",
            &format!("sa{{}}({A}, {B})"),
            "fault{}()",
            "",
            r#", priority{}("50")"#,
        ),
        // `1 / A == 1`: undefined at `A = 0`.
        rule(
            "division",
            &format!("su{{}}({A})"),
            "halt{}()",
            &format!("eqInt{{}}(divInt{{}}({one}, {A}), {one})"),
            r#", priority{}("40")"#,
        ),
        rule(
            "divisionOther",
            &format!("su{{}}({A})"),
            "fault{}()",
            "",
            r#", priority{}("50")"#,
        ),
        // Nested equation decisions: deciding `f`'s condition applies `g`, whose condition is
        // decided inside.
        rule(
            "useF2",
            &format!("rf2{{}}({A})"),
            &format!("pair{{}}(f{{}}({A}), f{{}}({}))", int(20)),
            "",
            "",
        ),
        rule(
            "useF",
            &format!("rf{{}}({A})"),
            &format!("val{{}}(f{{}}({A}))"),
            "",
            "",
        ),
        equation(
            "fPos",
            "f",
            &one,
            &holds_r(&format!("geInt{{}}(g{{}}({X}), {zero})")),
            "",
        ),
        equation("fOther", "f", &zero, r"\top{R}()", r#", owise{}()"#),
        equation(
            "gSmall",
            "g",
            X,
            &holds_r(&format!("ltInt{{}}({X}, {ten})")),
            "",
        ),
        equation("gLarge", "g", &zero, r"\top{R}()", r#", owise{}()"#),
        // An equation guarded by a competitor antecedent and its own condition, as a compiled
        // `owise` equation is.
        rule(
            "useH",
            &format!("rh{{}}({A})"),
            &format!("val{{}}(h{{}}({A}))"),
            "",
            "",
        ),
        equation(
            "hGuarded",
            "h",
            &one,
            &format!(
                r"\and{{R}}(\not{{R}}({}), {})",
                holds_r(&format!("eqInt{{}}({X}, {zero})")),
                holds_r(&format!("geInt{{}}({X}, {zero})"))
            ),
            "",
        ),
        equation("hOther", "h", &zero, r"\top{R}()", r#", owise{}()"#),
    ];
    let source = format!(
        r#"[]
        module MAIN
            hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
            hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
            sort SortS{{}} []
            hooked-symbol geInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.ge"), smt-hook{{}}(">=")]
            hooked-symbol ltInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.lt"), smt-hook{{}}("<")]
            hooked-symbol eqInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.eq"), smt-hook{{}}("=")]
            hooked-symbol divInt{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
                [function{{}}(), hook{{}}("INT.tdiv"), smt-hook{{}}("div")]
            hooked-symbol andBool{{}}(SortBool{{}}, SortBool{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("BOOL.and"), smt-hook{{}}("and")]
            hooked-symbol andThenBool{{}}(SortBool{{}}, SortBool{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("BOOL.andThen"), smt-hook{{}}("and")]
            symbol st{{}}(SortInt{{}}, SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol sa{{}}(SortInt{{}}, SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol su{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol rf{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol rh{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol rf2{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol pair{{}}(SortInt{{}}, SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol val{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol halt{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
            symbol fault{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
            symbol f{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
            symbol g{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
            symbol h{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
            {axioms}
        endmodule []"#,
        axioms = axioms.join("\n"),
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

fn ground(definition: &BackendDefinition, source: &str) -> Pattern {
    Pattern {
        term: definition
            .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
            .expect("term should internalize"),
        constraints: Vec::new(),
    }
}

/// A run with coverage, guards collected for `axioms`.
fn guarded(axioms: &[&str]) -> ExecutionOptions {
    ExecutionOptions {
        collect_coverage: true,
        collect_guards: Some(GuardCollection::new(axioms.iter().copied())),
        max_depth: 20,
        ..ExecutionOptions::default()
    }
}

/// Run `initial` collecting the guards of `axioms`, check that collecting changed nothing else in
/// the result, and return the guards.
fn guards_of(definition: &BackendDefinition, initial: Pattern, axioms: &[&str]) -> Vec<AxiomGuard> {
    let mut with = execute(definition, initial.clone(), guarded(axioms));
    let without = execute(
        definition,
        initial,
        ExecutionOptions {
            collect_guards: None,
            ..guarded(axioms)
        },
    );
    let guards = with
        .coverage
        .as_mut()
        .and_then(|coverage| coverage.guards.take())
        .expect("the run collected guards");
    assert_eq!(
        without.coverage.as_ref().map(|coverage| &coverage.guards),
        Some(&None)
    );
    assert_results_equal(&with, &without);
    guards
}

fn assert_results_equal(with: &ExecutionResult, without: &ExecutionResult) {
    assert_eq!(with, without, "collecting guards changed the result");
}

fn guard<'a>(guards: &'a [AxiomGuard], axiom: &str) -> &'a AxiomGuard {
    guards
        .iter()
        .find(|guard| guard.axiom == axiom)
        .unwrap_or_else(|| panic!("no guard of {axiom}: {guards:?}"))
}

/// The reached outcomes of the node at `path`.
fn reached(guard: &AxiomGuard, path: &[u32]) -> BTreeSet<NodeOutcome> {
    guard
        .nodes
        .iter()
        .find(|node| node.path == path)
        .unwrap_or_else(|| panic!("no node {path:?}: {guard:?}"))
        .reached
        .clone()
}

fn set<T: Ord + Clone>(items: &[T]) -> BTreeSet<T> {
    items.iter().cloned().collect()
}

/// For `A andThenBool B`: an entry where A is false gives A `false` and B nothing; A true and B
/// false gives B `false`; both true gives the guard `held`. The skeleton is the written
/// condition: `\equals(_, true)`, the connective, two atoms.
#[test]
fn short_circuit_classes_of_and_then() {
    let definition = definition();
    let st = |a: i64, b: i64| ground(&definition, &format!("st{{}}({}, {})", int(a), int(b)));
    let first_false = guards_of(&definition, st(1, 5), &["andThen"]);
    let first_false = guard(&first_false, "andThen");
    let shapes = first_false
        .nodes
        .iter()
        .map(|node| (node.path.clone(), node.shape.clone()))
        .collect::<Vec<_>>();
    assert!(matches!(shapes[0], (ref path, GuardShape::Equals(true)) if path == &[0]));
    assert!(
        matches!(shapes[1], (ref path, GuardShape::Connective(Connective::AndThenBool)) if path == &[0, 0])
    );
    assert!(matches!(shapes[2], (ref path, GuardShape::Term(_)) if path == &[0, 0, 0]));
    assert!(matches!(shapes[3], (ref path, GuardShape::Term(_)) if path == &[0, 0, 1]));
    assert_eq!(reached(first_false, &[0, 0, 0]), set(&[NodeOutcome::False]));
    assert_eq!(reached(first_false, &[0, 0, 1]), set(&[]));
    assert_eq!(
        first_false.outcomes,
        set(&[GuardOutcome::Refuted(Refutation::False)])
    );
    assert_eq!(first_false.combinations.len(), 1);
    assert_eq!(
        first_false.combinations[0].atoms,
        [Truth::False, Truth::False]
    );

    let second_false = guards_of(&definition, st(0, 5), &["andThen"]);
    let second_false = guard(&second_false, "andThen");
    assert_eq!(reached(second_false, &[0, 0, 0]), set(&[NodeOutcome::True]));
    assert_eq!(
        reached(second_false, &[0, 0, 1]),
        set(&[NodeOutcome::False])
    );

    let both = guards_of(&definition, st(0, 0), &["andThen"]);
    let both = guard(&both, "andThen");
    assert_eq!(both.outcomes, set(&[GuardOutcome::Held]));
    assert_eq!(reached(both, &[0]), set(&[NodeOutcome::True]));
}

/// `andBool` reads as `andThenBool` does: the same classes, by written order.
#[test]
fn and_bool_reports_as_and_then_bool() {
    let definition = definition();
    let sa = |a: i64, b: i64| ground(&definition, &format!("sa{{}}({}, {})", int(a), int(b)));
    for ((a, b), first, second) in [
        ((1, 5), set(&[NodeOutcome::False]), set(&[])),
        (
            (0, 5),
            set(&[NodeOutcome::True]),
            set(&[NodeOutcome::False]),
        ),
        ((0, 0), set(&[NodeOutcome::True]), set(&[NodeOutcome::True])),
    ] {
        let guards = guards_of(&definition, sa(a, b), &["andStrict"]);
        let strict = guard(&guards, "andStrict");
        assert_eq!(reached(strict, &[0, 0, 0]), first, "{a} {b}");
        assert_eq!(reached(strict, &[0, 0, 1]), second, "{a} {b}");
    }
}

/// An undefined operand (`1 / 0`) makes its atom `undefined`, and the refutation is classed
/// undefined.
#[test]
fn an_undefined_operand_is_reported_undefined() {
    let definition = definition();
    let guards = guards_of(
        &definition,
        ground(&definition, &format!("su{{}}({})", int(0))),
        &["division"],
    );
    let division = guard(&guards, "division");
    assert_eq!(reached(division, &[0, 0]), set(&[NodeOutcome::Undefined]));
    assert_eq!(reached(division, &[0]), set(&[NodeOutcome::False]));
    assert_eq!(
        division.outcomes,
        set(&[GuardOutcome::Refuted(Refutation::Undefined)])
    );
}

/// On a symbolic state the atom the evaluation does not decide is `undecided: symbolic`, and the
/// operand after it is not reached; the attempt, without a solver, is undecided.
#[test]
fn a_symbolic_instance_is_undecided_symbolic() {
    let definition = definition();
    let mut initial = ground(&definition, &format!("st{{}}({}, {})", int(0), int(0)));
    let program = ground(&definition, "st{}(Z:SortInt{}, Z:SortInt{})");
    initial.term = program.term;
    let guards = guards_of(&definition, initial, &["andThen"]);
    let and_then = guard(&guards, "andThen");
    assert_eq!(
        reached(and_then, &[0, 0, 0]),
        set(&[NodeOutcome::Undecided(OperandCause::Symbolic)])
    );
    assert_eq!(reached(and_then, &[0, 0, 1]), set(&[]));
    assert!(
        and_then
            .outcomes
            .iter()
            .all(|outcome| matches!(outcome, GuardOutcome::Undecided(_))),
        "{:?}",
        and_then.outcomes
    );
}

/// Nested equation decisions each get their own verdict: deciding `fPos`'s condition at
/// `g(20)` applies `gLarge` after refuting `gSmall` inside, and `fPos` then holds.
#[test]
fn nested_equation_decisions_get_their_own_verdicts() {
    let definition = definition();
    for (argument, g_outcomes) in [
        (5, set(&[GuardOutcome::Held])),
        (20, set(&[GuardOutcome::Refuted(Refutation::False)])),
    ] {
        let guards = guards_of(
            &definition,
            ground(&definition, &format!("rf{{}}({})", int(argument))),
            &["fPos", "gSmall"],
        );
        assert_eq!(
            guard(&guards, "fPos").outcomes,
            set(&[GuardOutcome::Held]),
            "{argument}"
        );
        assert_eq!(guard(&guards, "gSmall").outcomes, g_outcomes, "{argument}");
        let small = guard(&guards, "gSmall");
        let expected = if argument == 5 {
            NodeOutcome::True
        } else {
            NodeOutcome::False
        };
        assert_eq!(reached(small, &[0, 0]), set(&[expected]), "{argument}");
    }
}

/// A competitor antecedent `\not(..)` before the equation's own condition is a node of the
/// written `requires` like any other: a conjunct, reached first, and the own condition is reached
/// only where it is true.
#[test]
fn a_competitor_antecedent_is_a_conjunct() {
    let definition = definition();
    let at = |argument: i64| {
        let guards = guards_of(
            &definition,
            ground(&definition, &format!("rh{{}}({})", int(argument))),
            &["hGuarded"],
        );
        guard(&guards, "hGuarded").clone()
    };
    let zero = at(0);
    let not_paths = zero
        .nodes
        .iter()
        .filter(|node| matches!(node.shape, GuardShape::Connective(Connective::Not)))
        .map(|node| node.path.clone())
        .collect::<Vec<_>>();
    assert_eq!(not_paths.len(), 1, "{zero:?}");
    let not_path = &not_paths[0];
    assert_eq!(reached(&zero, not_path), set(&[NodeOutcome::False]));
    let own = zero
        .nodes
        .iter()
        .find(|node| {
            node.path.len() == not_path.len()
                && node.path != *not_path
                && matches!(node.shape, GuardShape::Equals(true))
        })
        .expect("the own condition is a sibling conjunct")
        .path
        .clone();
    assert_eq!(reached(&zero, &own), set(&[]));
    let five = at(5);
    assert_eq!(reached(&five, not_path), set(&[NodeOutcome::True]));
    assert_eq!(reached(&five, &own), set(&[NodeOutcome::True]));
    assert_eq!(five.outcomes, set(&[GuardOutcome::Held]));
}

/// The valuation combinations are bounded by the least ones in their order, whatever the
/// entries' order, and say when one was left out: `rf2(5)` decides `gSmall` at 5 (held) and at
/// 20 (refuted), and a limit of one keeps the first in the order of combinations.
#[test]
fn combinations_keep_the_least_within_the_limit() {
    let definition = definition();
    let initial = ground(&definition, &format!("rf2{{}}({})", int(5)));
    let all = guards_of(&definition, initial.clone(), &["gSmall"]);
    let all = guard(&all, "gSmall");
    assert_eq!(all.combinations.len(), 2, "{all:?}");
    assert!(!all.combinations_truncated);
    let mut options = guarded(&["gSmall"]);
    options.collect_guards.as_mut().unwrap().combination_limit = 1;
    let result = execute(&definition, initial, options);
    let guards = result.coverage.unwrap().guards.unwrap();
    let limited = guard(&guards, "gSmall");
    assert!(limited.combinations_truncated);
    assert_eq!(limited.combinations, all.combinations[..1]);
    assert_eq!(limited.combinations[0].atoms, [Truth::True]);
    assert_eq!(limited.combinations[0].outcome, GuardOutcome::Held);
}

/// The bounded cache that recognizes repeated entries changes no outcome: a cache of one key,
/// which the second distinct entry clears, and a size cap under which no key is cached (so each
/// entry is evaluated whenever it is made) report what the default bounds report. `rf2(5)`
/// decides `gSmall` at 5 and at 20, and `fPos` at both.
#[test]
fn the_bounded_cache_changes_no_outcome() {
    let definition = definition();
    let initial = ground(&definition, &format!("rf2{{}}({})", int(5)));
    let axioms = ["gSmall", "fPos"];
    let expected = guards_of(&definition, initial.clone(), &axioms);
    assert_eq!(
        guard(&expected, "gSmall").outcomes,
        set(&[GuardOutcome::Held, GuardOutcome::Refuted(Refutation::False)])
    );
    for (cache_keys, max_value_size) in [(1, 64), (4_096, 0)] {
        let mut options = guarded(&axioms);
        let collection = options.collect_guards.as_mut().unwrap();
        collection.cache_keys = cache_keys;
        collection.max_value_size = max_value_size;
        let result = execute(&definition, initial.clone(), options);
        let guards = result.coverage.unwrap().guards.unwrap();
        assert_eq!(guards, expected, "{cache_keys} keys, size {max_value_size}");
    }
}
