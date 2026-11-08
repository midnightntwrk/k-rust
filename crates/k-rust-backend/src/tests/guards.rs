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
        AttemptCause, AxiomGuard, Connective, GuardCollection, GuardOutcome, GuardShape,
        NodeOutcome, OperandCause, Refutation, Truth,
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

/// The skeleton of an axiom's condition is the one a run that enters it reports, every node
/// unreached; an axiom no run entered has one too, and an axiom with no condition has none.
#[test]
fn a_skeleton_is_the_nodes_a_run_reports() {
    let definition = definition();
    let named = ["andThen", "fPos", "useF"];
    let skeletons = crate::coverage::skeletons(
        &definition,
        &named.iter().map(|name| (*name).to_owned()).collect(),
    );
    let names = skeletons
        .iter()
        .map(|guard| guard.axiom.as_str())
        .collect::<Vec<_>>();
    assert!(
        names.contains(&"andThen") && names.contains(&"fPos"),
        "{names:?}"
    );
    assert!(!names.contains(&"useF"), "{names:?}");
    for skeleton in &skeletons {
        assert!(skeleton.outcomes.is_empty() && skeleton.combinations.is_empty());
        assert!(skeleton.nodes.iter().all(|node| node.reached.is_empty()));
    }
    let st = ground(&definition, &format!("st{{}}({}, {})", int(1), int(5)));
    let ran = guards_of(&definition, st, &["andThen"]);
    let ran = guard(&ran, "andThen");
    let skeleton = guard(&skeletons, "andThen");
    let shape = |guard: &AxiomGuard| {
        guard
            .nodes
            .iter()
            .map(|node| (node.path.clone(), node.shape.clone()))
            .collect::<Vec<_>>()
    };
    assert_eq!(shape(skeleton), shape(ran));
}

/// `\equals(b, true)` of the conjunction of `conjuncts` by `andBool`, nested to the left as a
/// chain of `&&` is, over the sort `R` of an equation.
fn all_r(conjuncts: &[String]) -> String {
    let mut conjunction = conjuncts[0].clone();
    for conjunct in &conjuncts[1..] {
        conjunction = format!("andBool{{}}({conjunction}, {conjunct})");
    }
    holds_r(&conjunction)
}

fn eq_x(value: i64) -> String {
    format!("eqInt{{}}({X}, {})", int(value))
}

fn not(b: &str) -> String {
    format!("notBool{{}}({b})")
}

/// A definition whose function groups have several equations whose guards are disjoint, each
/// group declared in written order or, with `reversed`, in the reverse order:
/// - `iv`, the equations an `if`/`else if`/`else` chain lowers to: branch `i` is guarded by the
///   negations of the earlier conditions and its own, the `else` by every negation;
/// - `w`, two hand-written complementary equations, `A <Int 32768` and `A >=Int 32768`;
/// - `u`, an equation applying at 0 and two whose guards are open there: one reads a function
///   with no equation (`k`), one divides by the argument;
/// - `o`, an equation, an `owise` one and one of a lower priority, each with a guard;
/// - `n`, an equation applying at 0 and one whose guard applies the helper `hl`, which nothing
///   else applies;
/// - `p`, `p(0) = 0` and an equation whose guard, at 0, recurses on `p(-1)` forever.
///
/// Each `cF(A)` rewrites to `val(F(A))`, and `two(A, B)` to `pair(iv(A), iv(B))`.
fn untried_definition(reversed: bool) -> BackendDefinition {
    let group = |mut equations: Vec<String>| {
        if reversed {
            equations.reverse();
        }
        equations
    };
    let chain = group(vec![
        equation("iv1", "iv", &int(10), &all_r(&[eq_x(1)]), ""),
        equation("iv2", "iv", &int(20), &all_r(&[not(&eq_x(1)), eq_x(2)]), ""),
        equation(
            "iv3",
            "iv",
            &int(30),
            &all_r(&[not(&eq_x(1)), not(&eq_x(2)), eq_x(3)]),
            "",
        ),
        equation(
            "iv4",
            "iv",
            &int(0),
            &all_r(&[not(&eq_x(1)), not(&eq_x(2)), not(&eq_x(3))]),
            "",
        ),
    ]);
    let bound = int(32768);
    let complementary = group(vec![
        equation(
            "wLow",
            "w",
            &int(1),
            &holds_r(&format!("ltInt{{}}({X}, {bound})")),
            "",
        ),
        equation(
            "wHigh",
            "w",
            &int(2),
            &holds_r(&format!("geInt{{}}({X}, {bound})")),
            "",
        ),
    ]);
    let others = [
        equation("uZero", "u", &int(0), &holds_r(&eq_x(0)), ""),
        equation(
            "uOpen",
            "u",
            &int(1),
            &holds_r(&format!("eqInt{{}}(k{{}}({X}), {})", int(1))),
            "",
        ),
        equation(
            "uDivides",
            "u",
            &int(2),
            &holds_r(&format!(
                "eqInt{{}}(divInt{{}}({}, {X}), {})",
                int(1),
                int(1)
            )),
            "",
        ),
        equation(
            "oHigh",
            "o",
            &int(1),
            &holds_r(&format!("geInt{{}}({X}, {})", int(0))),
            "",
        ),
        equation(
            "oOwise",
            "o",
            &int(2),
            &holds_r(&format!("ltInt{{}}({X}, {})", int(100))),
            r#", owise{}()"#,
        ),
        equation(
            "oLower",
            "o",
            &int(3),
            &holds_r(&format!("ltInt{{}}({X}, {})", int(100))),
            r#", priority{}("60")"#,
        ),
        equation("nZero", "n", &int(0), &holds_r(&eq_x(0)), ""),
        equation(
            "nHelped",
            "n",
            &int(1),
            &holds_r(&format!("eqInt{{}}(hl{{}}({X}), {})", int(7))),
            "",
        ),
        equation(
            "hlEq",
            "hl",
            X,
            &holds_r(&format!("geInt{{}}({X}, {})", int(0))),
            "",
        ),
        equation("pZero", "p", &int(0), &holds_r(&eq_x(0)), ""),
        equation(
            "pDown",
            "p",
            &int(1),
            &holds_r(&format!(
                "andThenBool{{}}({}, geInt{{}}(p{{}}(subInt{{}}({X}, {})), {}))",
                not(&eq_x(0)),
                int(1),
                int(0)
            )),
            "",
        ),
    ];
    let calls = ["iv", "w", "u", "o", "n", "p"]
        .iter()
        .map(|function| {
            rule(
                &format!("call{function}"),
                &format!("c{function}{{}}({A})"),
                &format!("val{{}}({function}{{}}({A}))"),
                "",
                "",
            )
        })
        .chain([rule(
            "callTwo",
            &format!("two{{}}({A}, {B})"),
            &format!("pair{{}}(iv{{}}({A}), iv{{}}({B}))"),
            "",
            "",
        )])
        .collect::<Vec<_>>();
    let constructors = ["iv", "w", "u", "o", "n", "p"]
        .iter()
        .map(|function| {
            format!(
                "symbol c{function}{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]\n"
            )
        })
        .collect::<String>();
    let functions = ["iv", "w", "u", "o", "n", "hl", "p"]
        .iter()
        .map(|function| {
            format!(
                "symbol {function}{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]\n"
            )
        })
        .collect::<String>();
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
            hooked-symbol subInt{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.sub"), smt-hook{{}}("-")]
            hooked-symbol divInt{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
                [function{{}}(), hook{{}}("INT.tdiv"), smt-hook{{}}("div")]
            hooked-symbol andBool{{}}(SortBool{{}}, SortBool{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("BOOL.and"), smt-hook{{}}("and")]
            hooked-symbol andThenBool{{}}(SortBool{{}}, SortBool{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("BOOL.andThen"), smt-hook{{}}("and")]
            hooked-symbol notBool{{}}(SortBool{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("BOOL.not"), smt-hook{{}}("not")]
            symbol k{{}}(SortInt{{}}) : SortInt{{}} [function{{}}()]
            symbol two{{}}(SortInt{{}}, SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol pair{{}}(SortInt{{}}, SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol val{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            {constructors}
            {functions}
            {axioms}
        endmodule []"#,
        axioms = chain
            .iter()
            .chain(&complementary)
            .chain(&others)
            .chain(&calls)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n"),
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

const CHAIN: [&str; 4] = ["iv1", "iv2", "iv3", "iv4"];

/// `cF(argument)` of the untried fixture.
fn call(definition: &BackendDefinition, function: &str, argument: i64) -> Pattern {
    ground(definition, &format!("c{function}{{}}({})", int(argument)))
}

/// The `matched` set of a run of `initial` collecting the guards of `axioms`.
fn matched_of(
    definition: &BackendDefinition,
    initial: Pattern,
    axioms: &[&str],
) -> BTreeSet<String> {
    execute(definition, initial, guarded(axioms))
        .coverage
        .expect("the run collected coverage")
        .matched
}

/// An application taking the first branch of an `if` chain records the restated conditions of
/// the later branches, which the scan does not try: each later branch reads its restated `!c1`
/// false, with `c1` true below it, and is refuted.
#[test]
fn the_later_branches_of_a_chain_record_their_restated_conditions() {
    let definition = untried_definition(false);
    let initial = call(&definition, "iv", 1);
    let matched = matched_of(&definition, initial.clone(), &CHAIN);
    assert!(
        matched.contains("iv1") && !matched.contains("iv2"),
        "{matched:?}"
    );
    let guards = guards_of(&definition, initial, &CHAIN);
    assert_eq!(guard(&guards, "iv1").outcomes, set(&[GuardOutcome::Held]));
    // `notBool(c1) andBool c2`: the negation is the conjunction's first operand.
    let second = guard(&guards, "iv2");
    assert_eq!(reached(second, &[0, 0, 0]), set(&[NodeOutcome::False]));
    assert_eq!(reached(second, &[0, 0, 0, 0]), set(&[NodeOutcome::True]));
    assert_eq!(reached(second, &[0, 0, 1]), set(&[]));
    assert_eq!(
        second.outcomes,
        set(&[GuardOutcome::Refuted(Refutation::False)])
    );
    // `(notBool(c1) andBool notBool(c2)) andBool ..`: the first negation is the innermost
    // conjunction's first operand.
    for later in ["iv3", "iv4"] {
        let later = guard(&guards, later);
        assert_eq!(reached(later, &[0, 0, 0, 0]), set(&[NodeOutcome::False]));
        assert_eq!(reached(later, &[0, 0, 0, 0, 0]), set(&[NodeOutcome::True]));
        assert_eq!(reached(later, &[0, 0, 0, 1]), set(&[]));
        assert_eq!(
            later.outcomes,
            set(&[GuardOutcome::Refuted(Refutation::False)])
        );
    }
}

/// The guard outcomes of a group do not depend on the order in which its equations are
/// declared, which is the order the scan tries them in (the `matched` sets differ): the
/// equations of an `if` chain, and two hand-written complementary equations, report the same
/// outcomes declared either way, at every argument. Of the complementary pair, the one tried
/// second is seen refuted where the first applies.
#[test]
fn guard_outcomes_do_not_depend_on_the_declaration_order_in_a_group() {
    let forward = untried_definition(false);
    let reverse = untried_definition(true);
    let complementary = ["wLow", "wHigh"];
    assert_ne!(
        matched_of(&forward, call(&forward, "iv", 1), &CHAIN),
        matched_of(&reverse, call(&reverse, "iv", 1), &CHAIN),
        "the two orders try the chain's equations differently"
    );
    for argument in 0..=4 {
        let ran = guards_of(&forward, call(&forward, "iv", argument), &CHAIN);
        assert_eq!(ran.len(), CHAIN.len(), "{argument}: {ran:?}");
        assert_eq!(
            ran,
            guards_of(&reverse, call(&reverse, "iv", argument), &CHAIN),
            "{argument}"
        );
    }
    for argument in [5, 40_000] {
        let ran = guards_of(&forward, call(&forward, "w", argument), &complementary);
        assert_eq!(
            ran,
            guards_of(&reverse, call(&reverse, "w", argument), &complementary),
            "{argument}"
        );
        let (held, refuted) = if argument == 5 {
            ("wLow", "wHigh")
        } else {
            ("wHigh", "wLow")
        };
        assert_eq!(guard(&ran, held).outcomes, set(&[GuardOutcome::Held]));
        assert_eq!(
            guard(&ran, refuted).outcomes,
            set(&[GuardOutcome::Refuted(Refutation::False)])
        );
        assert_eq!(
            reached(guard(&ran, refuted), &[0, 0]),
            set(&[NodeOutcome::False])
        );
    }
}

/// An untried guard the solver-free evaluation leaves open is `undecided: untried`, its open
/// atom `undecided: unevaluated` (`k` has no equation); one undefined at the arguments (`1 / 0`)
/// is refuted, the refutation classed undefined.
#[test]
fn an_open_untried_guard_is_undecided_untried_and_an_undefined_one_refuted() {
    let definition = untried_definition(false);
    let axioms = ["uZero", "uOpen", "uDivides"];
    let guards = guards_of(&definition, call(&definition, "u", 0), &axioms);
    assert_eq!(guard(&guards, "uZero").outcomes, set(&[GuardOutcome::Held]));
    let open = guard(&guards, "uOpen");
    assert_eq!(
        open.outcomes,
        set(&[GuardOutcome::Undecided(AttemptCause::Untried)])
    );
    assert_eq!(
        reached(open, &[0, 0]),
        set(&[NodeOutcome::Undecided(OperandCause::Unevaluated)])
    );
    let divides = guard(&guards, "uDivides");
    assert_eq!(
        divides.outcomes,
        set(&[GuardOutcome::Refuted(Refutation::Undefined)])
    );
    assert_eq!(reached(divides, &[0, 0]), set(&[NodeOutcome::Undefined]));
    assert_eq!(reached(divides, &[0]), set(&[NodeOutcome::False]));
}

/// The equations of a group below the one that applied, an `owise` one and one of a lower
/// priority, state nothing where it applies and get no entry; where it does not apply they are
/// tried, and reported as before.
#[test]
fn a_lower_group_gets_no_untried_entry() {
    let definition = untried_definition(false);
    let axioms = ["oHigh", "oOwise", "oLower"];
    let guards = guards_of(&definition, call(&definition, "o", 5), &axioms);
    let names = guards
        .iter()
        .map(|guard| guard.axiom.as_str())
        .collect::<Vec<_>>();
    assert_eq!(names, ["oHigh"]);
    let below = guards_of(&definition, call(&definition, "o", -5), &axioms);
    assert_eq!(
        guard(&below, "oHigh").outcomes,
        set(&[GuardOutcome::Refuted(Refutation::False)])
    );
    let names = below
        .iter()
        .map(|guard| guard.axiom.as_str())
        .collect::<Vec<_>>();
    assert_eq!(names, ["oHigh", "oLower"]);
    assert_eq!(guard(&below, "oLower").outcomes, set(&[GuardOutcome::Held]));
}

/// A function applied inside an untried guard's evaluation is applied by the record, not by the
/// run: `hl`, applied only by `nHelped`'s guard, is in no coverage set and has no entry, while
/// `nHelped` itself is reported.
#[test]
fn applications_inside_an_untried_evaluation_are_not_recorded() {
    let definition = untried_definition(false);
    let axioms = ["nZero", "nHelped", "hlEq"];
    let initial = call(&definition, "n", 0);
    let result = execute(&definition, initial.clone(), guarded(&axioms));
    let coverage = result.coverage.expect("the run collected coverage");
    assert!(!coverage.matched.contains("hlEq"), "{:?}", coverage.matched);
    assert!(!coverage.applied.contains("hlEq"), "{:?}", coverage.applied);
    assert!(
        !coverage.matched.contains("nHelped"),
        "{:?}",
        coverage.matched
    );
    let guards = guards_of(&definition, initial, &axioms);
    let names = guards
        .iter()
        .map(|guard| guard.axiom.as_str())
        .collect::<Vec<_>>();
    assert_eq!(names, ["nHelped", "nZero"]);
    assert_eq!(
        guard(&guards, "nHelped").outcomes,
        set(&[GuardOutcome::Refuted(Refutation::False)])
    );
}

/// An untried guard whose evaluation recurses forever where an earlier equation applies stops at
/// the entry's budget of polls: the operand it decided reads `false`, the conjunct `undecided:
/// stopped`, the guard `undecided: untried`, and the run ends as it does without guards.
#[test]
fn a_diverging_untried_guard_stops_at_its_budget() {
    let definition = untried_definition(false);
    let axioms = ["pZero", "pDown"];
    let mut options = guarded(&axioms);
    options.collect_guards.as_mut().unwrap().record_polls = 2_000;
    let initial = call(&definition, "p", 0);
    let result = execute(&definition, initial.clone(), options.clone());
    let without = execute(
        &definition,
        initial,
        ExecutionOptions {
            collect_guards: None,
            ..options
        },
    );
    let mut coverage = result.coverage.clone().expect("the run collected coverage");
    let guards = coverage.guards.take().expect("the run collected guards");
    assert_eq!(Some(coverage), without.coverage);
    assert_eq!(result.leaves, without.leaves);
    let down = guard(&guards, "pDown");
    assert_eq!(
        down.outcomes,
        set(&[GuardOutcome::Undecided(AttemptCause::Untried)])
    );
    assert_eq!(
        reached(down, &[0]),
        set(&[NodeOutcome::Undecided(OperandCause::Stopped)])
    );
    assert_eq!(reached(down, &[0, 0, 0]), set(&[NodeOutcome::False]));
    assert_eq!(reached(down, &[0, 0, 1]), set(&[]));
}

/// The cache of applications whose untried entries were made changes no outcome: a run that
/// evaluates `iv(1)` twice and `iv(4)` reports the same guards with a cache of one key, which
/// each new application clears, and with a size cap under which nothing is cached.
#[test]
fn the_application_cache_changes_no_outcome() {
    let definition = untried_definition(false);
    let initial = ground(&definition, &format!("two{{}}({}, {})", int(1), int(4)));
    let expected = guards_of(&definition, initial.clone(), &CHAIN);
    assert_eq!(
        guard(&expected, "iv4").outcomes,
        set(&[GuardOutcome::Held, GuardOutcome::Refuted(Refutation::False)])
    );
    let repeated = ground(&definition, &format!("two{{}}({}, {})", int(1), int(1)));
    assert_eq!(
        guards_of(&definition, repeated, &CHAIN),
        guards_of(&definition, call(&definition, "iv", 1), &CHAIN)
    );
    for (cache_keys, max_value_size) in [(1, 64), (4_096, 0)] {
        let mut options = guarded(&CHAIN);
        let collection = options.collect_guards.as_mut().unwrap();
        collection.cache_keys = cache_keys;
        collection.max_value_size = max_value_size;
        let result = execute(&definition, initial.clone(), options);
        let guards = result.coverage.unwrap().guards.unwrap();
        assert_eq!(guards, expected, "{cache_keys} keys, size {max_value_size}");
    }
}

/// `\and` of two predicates over the sort `R` of an equation: a `requires` of two conjuncts.
fn both_r(left: &str, right: &str) -> String {
    format!(r"\and{{R}}({left}, {right})")
}

/// A function equation `head(X0) = rhs requires condition` whose argument is bound by
/// `binding`, of argument sort `argument` and result sort `result`, as [`equation`] is.
fn equation_over(
    label: &str,
    head: &str,
    (argument, binding): (&str, &str),
    result: &str,
    rhs: &str,
    condition: &str,
) -> String {
    format!(
        r#"
            axiom{{R}} \implies{{R}}(
                \and{{R}}({condition}, \and{{R}}(\in{{{argument}, R}}(X0:{argument}, {binding}), \top{{R}}())),
                \equals{{{result}, R}}({head}{{}}(X0:{argument}), \and{{{result}}}({rhs}, \top{{{result}}}()))
            ) [label{{}}("{label}")]"#
    )
}

const MINT: &str = "SortMInt{Sort8{}}";

/// A definition whose function groups exercise what the scan does not decide, each group
/// declared in written order or, with `reversed`, in the reverse order:
/// - `s`, one group: `sSet`, which a `symbolic` attribute sets aside on a ground argument, and
///   `sApp`, which applies at 0;
/// - `t`, the same pair above a lower group (`tLow`), so that the scan decides `tSet`'s guard;
///   its guard reads `k`, which has no equation, so a tried entry and an untried one differ;
/// - `mp`, one equation over a map pattern, `mp(K |-> V M) = 1 requires V ==Int 5 orBool V ==Int
///   7`, which matches `1 |-> 5 2 |-> 7` in two ways, both applying;
/// - `m`, `mZero` applying at 0 beside two equations of two conjuncts each, the first open
///   (`k`) and the second false (`mMixed`) or false for an undefined operand (`mUndef`);
/// - `om`, of `MInt{8}` values: `omZero` at 0, and `omNarrow` and `omWide` at positive
///   arguments, whose results are a literal its width holds and one it cannot hold
///   (`crate::literal`).
///
/// Each `cF(A)` rewrites to `val(F(A))` (`valm` for `om`), and `cmp(M)` to `val(mp(M))`.
fn undecided_definition(reversed: bool) -> BackendDefinition {
    let group = |mut equations: Vec<String>| {
        if reversed {
            equations.reverse();
        }
        equations
    };
    let open = holds_r(&format!("eqInt{{}}(k{{}}({X}), {})", int(1)));
    let int_sort = ("SortInt{}", X);
    let groups = [
        group(vec![
            equation(
                "sSet",
                "s",
                &int(5),
                &holds_r(&format!("geInt{{}}({X}, {})", int(0))),
                ", symbolic{}()",
            ),
            equation("sApp", "s", &int(1), &holds_r(&eq_x(0)), ""),
        ]),
        group(vec![
            equation("tSet", "t", &int(5), &open, ", symbolic{}()"),
            equation("tApp", "t", &int(1), &holds_r(&eq_x(0)), ""),
        ]),
        vec![equation(
            "tLow",
            "t",
            &int(2),
            &holds_r(&format!("geInt{{}}({X}, {})", int(0))),
            r#", priority{}("60")"#,
        )],
        vec![equation_over(
            "mpEq",
            "mp",
            (
                "SortC{}",
                "cConcat{}(cItem{}(K:SortInt{}, V:SortInt{}), M:SortC{})",
            ),
            "SortInt{}",
            &int(1),
            &holds_r(&format!(
                "orBool{{}}(eqInt{{}}(V:SortInt{{}}, {}), eqInt{{}}(V:SortInt{{}}, {}))",
                int(5),
                int(7)
            )),
        )],
        group(vec![
            equation("mZero", "m", &int(0), &holds_r(&eq_x(0)), ""),
            equation(
                "mMixed",
                "m",
                &int(1),
                &both_r(&open, &holds_r(&eq_x(5))),
                "",
            ),
            equation(
                "mUndef",
                "m",
                &int(2),
                &both_r(
                    &open,
                    &holds_r(&format!(
                        "eqInt{{}}(divInt{{}}({}, {X}), {})",
                        int(1),
                        int(1)
                    )),
                ),
                "",
            ),
        ]),
        group(vec![
            equation_over(
                "omZero",
                "om",
                int_sort,
                MINT,
                &format!(r#"\dv{{{MINT}}}("-128p8")"#),
                &holds_r(&eq_x(0)),
            ),
            equation_over(
                "omNarrow",
                "om",
                int_sort,
                MINT,
                &format!(r#"\dv{{{MINT}}}("5p8")"#),
                &holds_r(&format!("geInt{{}}({X}, {})", int(1))),
            ),
            equation_over(
                "omWide",
                "om",
                int_sort,
                MINT,
                &format!(r#"\dv{{{MINT}}}("256p8")"#),
                &holds_r(&format!("geInt{{}}({X}, {})", int(1))),
            ),
        ]),
    ];
    let mut calls = ["s", "t", "m"]
        .iter()
        .map(|function| {
            rule(
                &format!("call{function}"),
                &format!("c{function}{{}}({A})"),
                &format!("val{{}}({function}{{}}({A}))"),
                "",
                "",
            )
        })
        .collect::<Vec<_>>();
    calls.push(rule(
        "callom",
        &format!("com{{}}({A})"),
        &format!("valm{{}}(om{{}}({A}))"),
        "",
        "",
    ));
    calls.push(rule(
        "callmp",
        "cmp{}(M:SortC{})",
        "val{}(mp{}(M:SortC{}))",
        "",
        "",
    ));
    let source = format!(
        r#"[]
        module MAIN
            hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
            hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
            hooked-sort SortMInt{{S}} [hook{{}}("MINT.MInt"), hasDomainValues{{}}()]
            sort Sort8{{}} []
            hooked-sort SortC{{}} [hook{{}}("MAP.Map"), unit{{}}(cUnit{{}}()), element{{}}(cItem{{}}()), concat{{}}(cConcat{{}}())]
            hooked-symbol cUnit{{}}() : SortC{{}} [function{{}}(), total{{}}(), hook{{}}("MAP.unit")]
            hooked-symbol cItem{{}}(SortInt{{}}, SortInt{{}}) : SortC{{}} [function{{}}(), total{{}}(), hook{{}}("MAP.element")]
            hooked-symbol cConcat{{}}(SortC{{}}, SortC{{}}) : SortC{{}}
                [function{{}}(), hook{{}}("MAP.concat"), assoc{{}}(), comm{{}}(), unit{{}}(cUnit{{}}())]
            sort SortS{{}} []
            hooked-symbol geInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.ge"), smt-hook{{}}(">=")]
            hooked-symbol eqInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.eq"), smt-hook{{}}("=")]
            hooked-symbol divInt{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
                [function{{}}(), hook{{}}("INT.tdiv"), smt-hook{{}}("div")]
            hooked-symbol orBool{{}}(SortBool{{}}, SortBool{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("BOOL.or"), smt-hook{{}}("or")]
            symbol k{{}}(SortInt{{}}) : SortInt{{}} [function{{}}()]
            symbol s{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
            symbol t{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
            symbol m{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
            symbol mp{{}}(SortC{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
            symbol om{{}}(SortInt{{}}) : {MINT} [function{{}}(), total{{}}()]
            symbol val{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol valm{{}}({MINT}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol cs{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol ct{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol cm{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol com{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol cmp{{}}(SortC{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            {axioms}
        endmodule []"#,
        axioms = groups
            .iter()
            .flatten()
            .chain(&calls)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n"),
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

/// The axioms of [`undecided_definition`] with a `requires`.
const UNDECIDED: [&str; 12] = [
    "sSet", "sApp", "tSet", "tApp", "tLow", "mpEq", "mZero", "mMixed", "mUndef", "omZero",
    "omNarrow", "omWide",
];

/// The names of the axioms `guards` reports.
fn names(guards: &[AxiomGuard]) -> Vec<&str> {
    guards.iter().map(|guard| guard.axiom.as_str()).collect()
}

/// A set-aside instance the scan reads as unused without deciding it, in a group no lower group
/// follows, gets an untried entry whether it is declared before or after the equation that
/// applies: `sSet`'s guard holds at 0 either way.
#[test]
fn an_undecided_set_aside_instance_gets_an_entry_before_the_applied_equation_too() {
    for reversed in [false, true] {
        let definition = undecided_definition(reversed);
        let guards = guards_of(&definition, call(&definition, "s", 0), &["sSet", "sApp"]);
        assert_eq!(names(&guards), ["sApp", "sSet"], "reversed: {reversed}");
        assert_eq!(guard(&guards, "sApp").outcomes, set(&[GuardOutcome::Held]));
        assert_eq!(
            guard(&guards, "sSet").outcomes,
            set(&[GuardOutcome::Held]),
            "reversed: {reversed}"
        );
    }
}

/// A set-aside instance the scan decides, in a group a lower group follows, keeps the entry its
/// attempt made and gets no untried one beside it: declared before the equation that applies,
/// `tSet` reports its attempt's verdict alone, never `undecided-untried`; declared after it, it
/// is not tried and reports `undecided-untried` alone.
#[test]
fn a_decided_set_aside_instance_gets_no_second_entry() {
    let tried = guards_of(
        &undecided_definition(false),
        call(&undecided_definition(false), "t", 0),
        &["tSet"],
    );
    let tried = &guard(&tried, "tSet").outcomes;
    assert_eq!(tried.len(), 1, "{tried:?}");
    assert!(
        !tried.contains(&GuardOutcome::Undecided(AttemptCause::Untried)),
        "{tried:?}"
    );
    let definition = undecided_definition(true);
    let untried = guards_of(&definition, call(&definition, "t", 0), &["tSet"]);
    assert_eq!(
        guard(&untried, "tSet").outcomes,
        set(&[GuardOutcome::Undecided(AttemptCause::Untried)])
    );
}

/// An equation whose map pattern matches the subject in two ways, both applying, reports both
/// instances, whichever the matcher reaches first: the one the scan applies, and the other,
/// untried. `V ==Int 5` is seen true (`V = 5`) and false (`V = 7`), and `V ==Int 7` true where
/// it is reached.
#[test]
fn every_instance_of_the_applied_equation_has_an_entry() {
    let definition = undecided_definition(false);
    let initial = ground(
        &definition,
        &format!(
            "cmp{{}}(cConcat{{}}(cItem{{}}({}, {}), cItem{{}}({}, {})))",
            int(1),
            int(5),
            int(2),
            int(7)
        ),
    );
    let guards = guards_of(&definition, initial, &["mpEq"]);
    let equation = guard(&guards, "mpEq");
    assert_eq!(equation.outcomes, set(&[GuardOutcome::Held]));
    assert_eq!(
        reached(equation, &[0, 0, 0]),
        set(&[NodeOutcome::True, NodeOutcome::False])
    );
    assert_eq!(reached(equation, &[0, 0, 1]), set(&[NodeOutcome::True]));
    assert_eq!(equation.combinations.len(), 2, "{equation:?}");
}

/// An equation holding a literal whose element the definition leaves open gets no untried
/// entry: after `omZero` applies at 0, `omNarrow`, whose literal is determined, is refuted
/// there, and `omWide`, the same equation but for its literal, has none.
#[test]
fn an_equation_holding_an_open_literal_gets_no_untried_entry() {
    let definition = undecided_definition(false);
    let axioms = ["omZero", "omNarrow", "omWide"];
    let guards = guards_of(&definition, call(&definition, "om", 0), &axioms);
    assert_eq!(names(&guards), ["omNarrow", "omZero"]);
    assert_eq!(
        guard(&guards, "omNarrow").outcomes,
        set(&[GuardOutcome::Refuted(Refutation::False)])
    );
}

/// Collecting the guards of every axiom, with the untried entries it makes, changes nothing
/// else in the run: every call of both untried fixtures, in both declaration orders, gives the
/// same leaves, halts, work and coverage as without guards (`guards_of` compares the whole
/// result), the diverging `pDown` included under a small budget of polls.
#[test]
fn collecting_untried_guards_changes_nothing_else_in_the_run() {
    let untried_axioms = [
        "iv1", "iv2", "iv3", "iv4", "wLow", "wHigh", "uZero", "uOpen", "uDivides", "oHigh",
        "oOwise", "oLower", "nZero", "nHelped", "hlEq", "pZero", "pDown",
    ];
    for reversed in [false, true] {
        let definition = untried_definition(reversed);
        for function in ["iv", "w", "u", "o", "n", "p"] {
            // `p(A)` recurses to `p(A - 1)` in the run itself, with or without guards: forever
            // at a negative argument, and `A` levels deep otherwise.
            for argument in [-5, 0, 1, 2, 3, 4, 40_000]
                .into_iter()
                .filter(|argument| function != "p" || (0..=4).contains(argument))
            {
                let initial = call(&definition, function, argument);
                let mut options = guarded(&untried_axioms);
                options.collect_guards.as_mut().unwrap().record_polls = 2_000;
                let mut with = execute(&definition, initial.clone(), options.clone());
                let without = execute(
                    &definition,
                    initial,
                    ExecutionOptions {
                        collect_guards: None,
                        ..options
                    },
                );
                with.coverage
                    .as_mut()
                    .and_then(|coverage| coverage.guards.take())
                    .expect("the run collected guards");
                assert_results_equal(&with, &without);
            }
        }
        let definition = undecided_definition(reversed);
        for function in ["s", "t", "m", "om"] {
            for argument in [-1, 0, 1, 5] {
                guards_of(
                    &definition,
                    call(&definition, function, argument),
                    &UNDECIDED,
                );
            }
        }
    }
}
