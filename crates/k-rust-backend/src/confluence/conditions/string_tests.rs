//! The equality classes and the literal substitution (module documentation, "equality
//! classes") against brute force over strings: random conjunctions of `STRING.eq` and
//! `STRING.ne` atoms, `==K` between one-element `K` sequences of injected strings (which the
//! reader itself does not peel to the strings yet: `sequence_item`), ML equalities and length
//! comparisons, over two string variables, judged on every
//! assignment of short strings by the backend's own ground evaluation. A conjunction the reader
//! refutes (by its literals, classes or bounds, or after substituting a class's literal and
//! simplifying again, as `Context::conditions` does) must have no satisfying assignment, and every
//! value the classes give a term must be the term's value wherever the conjunction holds.

use std::collections::BTreeSet;

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use super::{contradictory, literal_values, refuted_by_literals};
use crate::{
    definition::BackendDefinition,
    rule::Predicate,
    simplify::{SimplificationOptions, simplify, simplify_predicate_with_solver},
    smt::NoSolver,
    substitution::{Substitution, substitute},
    term::{Term, TermKind},
};

const FUN_PRELUDE: &str = include_str!("../../../tests/fixtures/fun-prelude-hooked-equations.kore");

fn prelude() -> BackendDefinition {
    let syntax = parse_definition(FUN_PRELUDE).expect("the fixture parses");
    BackendDefinition::internalize(&syntax, "FUN-UNTYPED").expect("the fixture internalizes")
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).expect("the term parses"), &[])
        .unwrap_or_else(|error| panic!("{source}: {error}"))
}

/// The KORE name of the prelude's symbol carrying `hook` with `arity` arguments.
fn hooked(definition: &BackendDefinition, hook: &str, arity: usize) -> String {
    definition
        .symbols()
        .values()
        .find(|symbol| {
            symbol.attributes.hook.as_deref() == Some(hook) && symbol.argument_sorts.len() == arity
        })
        .unwrap_or_else(|| panic!("no symbol hooked {hook}"))
        .name
        .to_string()
}

const VALUES: [&str; 7] = ["", "a", "b", "aa", "ab", "ba", "bb"];
const LITERALS: [&str; 4] = ["", "a", "b", "ab"];
const NAMES: [&str; 2] = ["S", "T"];

struct Symbols {
    eq: String,
    ne: String,
    concat: String,
    length: String,
    kequal: String,
    int_eq: String,
}

fn string(value: &str) -> String {
    format!(r#"\dv{{SortString{{}}}}("{value}")"#)
}

/// A string term of the generated conjunctions: a variable, a literal, or a variable followed by
/// a literal or by the other variable.
fn string_term(symbols: &Symbols, next: &mut dyn FnMut(usize) -> usize) -> String {
    let variable = |index: usize| format!("{}:SortString{{}}", NAMES[index]);
    match next(5) {
        0 => string(LITERALS[next(LITERALS.len())]),
        1 => format!(
            "{}{{}}({}, {})",
            symbols.concat,
            variable(next(2)),
            string(LITERALS[1 + next(LITERALS.len() - 1)])
        ),
        2 => format!("{}{{}}({}, {})", symbols.concat, variable(0), variable(1)),
        _ => variable(next(2)),
    }
}

/// `term` as a one-element `K` sequence.
fn sequence(term: &str) -> String {
    format!("kseq{{}}(inj{{SortString{{}}, SortKItem{{}}}}({term}), dotk{{}}())")
}

/// A generated conjunct.
fn conjunct(
    definition: &BackendDefinition,
    symbols: &Symbols,
    next: &mut dyn FnMut(usize) -> usize,
) -> Predicate {
    let polarity = next(3) != 0;
    let truth = |value: bool| term(definition, &format!(r#"\dv{{SortBool{{}}}}("{value}")"#));
    let (left, right) = (string_term(symbols, next), string_term(symbols, next));
    match next(6) {
        0 => Predicate::Equals(
            term(definition, &format!("{}{{}}({left}, {right})", symbols.ne)),
            truth(polarity),
        ),
        1 => Predicate::Equals(
            term(
                definition,
                &format!(
                    "{}{{}}({}, {})",
                    symbols.kequal,
                    sequence(&left),
                    sequence(&right)
                ),
            ),
            truth(polarity),
        ),
        2 => Predicate::Equals(
            term(definition, &format!("{}:SortString{{}}", NAMES[next(2)])),
            term(definition, &right),
        ),
        3 => Predicate::Equals(
            term(
                definition,
                &format!(
                    r#"{}{{}}({}{{}}({left}), \dv{{SortInt{{}}}}("{}"))"#,
                    symbols.int_eq,
                    symbols.length,
                    next(3)
                ),
            ),
            truth(polarity),
        ),
        _ => Predicate::Equals(
            term(definition, &format!("{}{{}}({left}, {right})", symbols.eq)),
            truth(polarity),
        ),
    }
}

fn assignment(definition: &BackendDefinition, values: [&str; 2]) -> Substitution {
    NAMES
        .iter()
        .zip(values)
        .map(|(name, value)| {
            let TermKind::Variable(variable) = term(definition, &format!("{name}:SortString{{}}"))
                .kind()
                .clone()
            else {
                unreachable!("a variable")
            };
            (variable, term(definition, &string(value)))
        })
        .collect()
}

/// A generated conjunct (an `\\equals`) under `valuation`.
fn instance(conjunct: &Predicate, valuation: &Substitution) -> Predicate {
    let Predicate::Equals(left, right) = conjunct else {
        unreachable!("the generated conjuncts are equalities")
    };
    Predicate::Equals(substitute(left, valuation), substitute(right, valuation))
}

fn decide(definition: &BackendDefinition, predicate: &Predicate) -> Option<bool> {
    match simplify_predicate_with_solver(
        definition,
        predicate,
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    ) {
        Ok(Ok(Predicate::True)) => Some(true),
        Ok(Ok(Predicate::False)) => Some(false),
        _ => None,
    }
}

fn value(definition: &BackendDefinition, term: &Term) -> Option<Term> {
    match simplify(definition, term, SimplificationOptions::default()) {
        Ok(Ok(result)) if result.constraints().is_empty() => Some(result.term),
        _ => None,
    }
}

/// The reader's verdict on `conjuncts` as `Context::conditions` reaches it: the conjunction
/// simplified, then read by `contradictory` and by the literal substitution; and whether only
/// the substitution refutes it.
fn refuted(definition: &BackendDefinition, conjuncts: &[Predicate]) -> (bool, bool) {
    let mut simplify = |predicate: Predicate| match simplify_predicate_with_solver(
        definition,
        &predicate,
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    ) {
        Ok(Ok(simplified)) => Some(simplified),
        _ => None,
    };
    let Some(simplified) = simplify(Predicate::And(conjuncts.to_vec().into())) else {
        return (false, false);
    };
    let mut flat = BTreeSet::new();
    super::super::flatten(simplified, &mut flat);
    let flat = flat.into_iter().collect::<Vec<_>>();
    if flat.contains(&Predicate::False) || contradictory(definition, &flat) {
        return (true, false);
    }
    let substituted = refuted_by_literals(
        definition,
        &super::memberships(definition),
        &flat,
        &mut simplify,
    );
    (substituted, substituted)
}

/// The failures of `cases` random conjunctions of two to four conjuncts.
pub(crate) fn random_string_conjunctions_agree_with_brute_force(cases: usize) -> Vec<String> {
    let definition = prelude();
    let symbols = Symbols {
        eq: hooked(&definition, "STRING.eq", 2),
        ne: hooked(&definition, "STRING.ne", 2),
        concat: hooked(&definition, "STRING.concat", 2),
        length: hooked(&definition, "STRING.length", 1),
        kequal: hooked(&definition, "KEQUAL.eq", 2),
        int_eq: hooked(&definition, "INT.eq", 2),
    };
    let mut state = 0x57a1_c0d1_u64;
    let mut next = |bound: usize| {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        usize::try_from((state >> 33) % u64::try_from(bound).unwrap()).unwrap()
    };
    let assignments = VALUES
        .iter()
        .flat_map(|s| VALUES.iter().map(move |t| [*s, *t]))
        .map(|values| assignment(&definition, values))
        .collect::<Vec<_>>();
    let mut failures = Vec::new();
    // (refuted, unsatisfiable, with a literal class, refuted only after the substitution): the
    // run reaches each verdict.
    let mut tally = (0, 0, 0, 0);
    for _ in 0..cases {
        let count = 2 + next(3);
        let conjuncts = (0..count)
            .map(|_| conjunct(&definition, &symbols, &mut next))
            .collect::<Vec<_>>();
        let satisfying = assignments
            .iter()
            .filter(|valuation| {
                conjuncts.iter().all(|conjunct| {
                    decide(&definition, &instance(conjunct, valuation)) == Some(true)
                })
            })
            .collect::<Vec<_>>();
        let (verdict, by_substitution) = refuted(&definition, &conjuncts);
        tally.0 += usize::from(verdict);
        tally.3 += usize::from(by_substitution);
        tally.1 += usize::from(satisfying.is_empty());
        tally.2 += usize::from(!literal_values(&definition, &conjuncts).is_empty());
        if verdict && !satisfying.is_empty() {
            failures.push(format!(
                "{conjuncts:?} is refuted but {:?} satisfies it",
                satisfying[0]
            ));
            continue;
        }
        for (member, literal) in literal_values(&definition, &conjuncts) {
            for valuation in &satisfying {
                if value(&definition, &substitute(&member, valuation)) != Some(literal.clone()) {
                    failures.push(format!(
                        "{conjuncts:?}: {member:?} is given {literal:?}, which it is not at {valuation:?}"
                    ));
                }
            }
        }
    }
    if tally.0 == 0 || tally.1 == 0 || tally.2 == 0 || tally.3 == 0 || tally.1 == cases {
        failures.push(format!("the run does not reach every verdict: {tally:?}"));
    }
    if std::env::var_os("KRUST_CONDITIONS_TALLY").is_some() {
        eprintln!("string conjunctions: {tally:?} of {cases}");
    }
    failures
}

#[test]
fn random_string_conjunctions_agree_with_brute_force_by_default() {
    let failures = random_string_conjunctions_agree_with_brute_force(400);
    assert!(failures.is_empty(), "{failures:#?}");
}

/// V7: giving a class's members another class's literal makes the substituted conjunction false
/// where the original holds, which the string property test sees.
#[test]
fn a_misplaced_class_literal_is_caught_by_the_string_property_test() {
    let switches = crate::confluence::switches::Switches {
        misplace_class_literal: true,
        ..Default::default()
    };
    let failures = crate::confluence::switches::with(switches, || {
        random_string_conjunctions_agree_with_brute_force(400)
    });
    assert!(!failures.is_empty());
}

/// V7: merging the operands of a negative string equality into one class is caught by the string
/// property test too.
#[test]
fn a_misread_string_class_is_caught_by_the_string_property_test() {
    let switches = crate::confluence::switches::Switches {
        misread_literal_classes: true,
        ..Default::default()
    };
    let failures = crate::confluence::switches::with(switches, || {
        random_string_conjunctions_agree_with_brute_force(400)
    });
    assert!(!failures.is_empty());
}

/// `S +String T ==String "ab"` beside `lengthString(S +String T) ==Int 1`: the simplifier keeps
/// both, and only putting the class's literal inside the second (`lengthString("ab")`) and
/// simplifying again refutes them. The member `lengthString(S +String T)` has its own class (with
/// `1`); replacing it whole would lose that.
#[test]
fn a_class_literal_put_inside_another_member_refutes() {
    let definition = prelude();
    let eq = hooked(&definition, "STRING.eq", 2);
    let concat = hooked(&definition, "STRING.concat", 2);
    let length = hooked(&definition, "STRING.length", 1);
    let int_eq = hooked(&definition, "INT.eq", 2);
    let joined = format!("{concat}{{}}(S:SortString{{}}, T:SortString{{}})");
    let truth = term(&definition, r#"\dv{SortBool{}}("true")"#);
    let conjuncts = vec![
        Predicate::Equals(
            term(
                &definition,
                &format!("{eq}{{}}({joined}, {})", string("ab")),
            ),
            truth.clone(),
        ),
        Predicate::Equals(
            term(
                &definition,
                &format!(r#"{int_eq}{{}}({length}{{}}({joined}), \dv{{SortInt{{}}}}("1"))"#),
            ),
            truth,
        ),
    ];
    assert_eq!(refuted(&definition, &conjuncts), (true, true));
}
