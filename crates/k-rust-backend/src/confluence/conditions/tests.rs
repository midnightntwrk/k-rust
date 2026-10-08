//! The condition reader against the meaning of its atoms: a unit test per comparison identity and
//! per atom true wherever defined, and a property test that compares `contradictory` and
//! `equalities` with brute force over integer assignments (the design's "Revision after review 1",
//! R1.7).

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use super::{contradictory, equalities};
use crate::{
    definition::BackendDefinition,
    rule::Predicate,
    substitution::substitute,
    term::{Term, TermKind},
};

const DEFINITION: &str = r#"
[] module MAIN
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    hooked-symbol ltInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.lt")]
    hooked-symbol leInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.le")]
    hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.gt")]
    hooked-symbol geInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.ge")]
    hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.eq")]
    hooked-symbol neInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.ne")]
    hooked-symbol notBool{}(SortBool{}) : SortBool{} [function{}(), total{}(), hook{}("BOOL.not")]
    hooked-sort SortMap{}
        [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
    hooked-symbol mapUnit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
    hooked-symbol mapItem{}(SortInt{}, SortInt{}) : SortMap{} [function{}(), total{}(), hook{}("MAP.element")]
    hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{} [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
    hooked-symbol inKeys{}(SortInt{}, SortMap{}) : SortBool{} [function{}(), total{}(), hook{}("MAP.in_keys")]
endmodule []
"#;

fn definition() -> BackendDefinition {
    let syntax = parse_definition(DEFINITION).expect("the definition parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).expect("the term parses"), &[])
        .expect("the term internalizes")
}

const OPERATORS: [&str; 6] = ["ltInt", "leInt", "gtInt", "geInt", "eqInt", "neInt"];

fn holds(operator: &str, left: i64, right: i64) -> bool {
    match operator {
        "ltInt" => left < right,
        "leInt" => left <= right,
        "gtInt" => left > right,
        "geInt" => left >= right,
        "eqInt" => left == right,
        "neInt" => left != right,
        _ => unreachable!("an operator of OPERATORS"),
    }
}

/// An operand: one of the variables `X`, `Y`, `Z`, or a literal.
#[derive(Clone, Copy, Debug)]
enum Operand {
    Variable(usize),
    Literal(i64),
}

const NAMES: [&str; 3] = ["X", "Y", "Z"];

impl Operand {
    fn kore(self) -> String {
        match self {
            Self::Variable(index) => format!("{}:SortInt{{}}", NAMES[index]),
            Self::Literal(value) => format!(r#"\dv{{SortInt{{}}}}("{value}")"#),
        }
    }

    fn value(self, assignment: [i64; 3]) -> i64 {
        match self {
            Self::Variable(index) => assignment[index],
            Self::Literal(value) => value,
        }
    }
}

/// A conjunct: `operator(left, right)` required `polarity`, written under `negations` `notBool`s;
/// or the equality `\equals(X, operand)`.
#[derive(Clone, Debug)]
enum Conjunct {
    Literal {
        operator: &'static str,
        left: Operand,
        right: Operand,
        negations: usize,
        polarity: bool,
    },
    Equality(usize, Operand),
}

impl Conjunct {
    fn predicate(&self, definition: &BackendDefinition) -> Predicate {
        match self {
            Self::Literal {
                operator,
                left,
                right,
                negations,
                polarity,
            } => {
                let mut text = format!("{operator}{{}}({}, {})", left.kore(), right.kore());
                for _ in 0..*negations {
                    text = format!("notBool{{}}({text})");
                }
                let boolean = term(definition, &format!(r#"\dv{{SortBool{{}}}}("{polarity}")"#));
                Predicate::Equals(term(definition, &text), boolean)
            }
            Self::Equality(variable, operand) => Predicate::Equals(
                term(definition, &Operand::Variable(*variable).kore()),
                term(definition, &operand.kore()),
            ),
        }
    }

    fn satisfied(&self, assignment: [i64; 3]) -> bool {
        match self {
            Self::Literal {
                operator,
                left,
                right,
                negations,
                polarity,
            } => {
                let value = holds(operator, left.value(assignment), right.value(assignment));
                (value != (negations % 2 == 1)) == *polarity
            }
            Self::Equality(variable, operand) => assignment[*variable] == operand.value(assignment),
        }
    }
}

fn assignments() -> impl Iterator<Item = [i64; 3]> {
    (-3..=3).flat_map(|x| (-3..=3).flat_map(move |y| (-3..=3).map(move |z| [x, y, z])))
}

/// Checks one conjunction against brute force: `contradictory` only when no assignment in
/// `[-3, 3]^3` satisfies it, and each equality `equalities` returns holds in every assignment
/// that does. Returns the failure.
fn check(definition: &BackendDefinition, conjuncts: &[Conjunct]) -> Option<String> {
    let predicates = conjuncts
        .iter()
        .map(|conjunct| conjunct.predicate(definition))
        .collect::<Vec<_>>();
    let satisfying = assignments()
        .filter(|assignment| {
            conjuncts
                .iter()
                .all(|conjunct| conjunct.satisfied(*assignment))
        })
        .collect::<Vec<_>>();
    if contradictory(&predicates) {
        if let Some(witness) = satisfying.first() {
            return Some(format!(
                "{conjuncts:?} is called contradictory but {witness:?} satisfies it"
            ));
        }
        return None;
    }
    let substitution = equalities(&predicates);
    for assignment in &satisfying {
        for (variable, value) in &substitution {
            let index = NAMES
                .iter()
                .position(|name| variable.name.as_ref() == *name)
                .expect("a variable of the conjunction");
            let evaluated = ground_value(&substitute(
                value,
                &assignment_substitution(definition, *assignment),
            ));
            if evaluated != Some(assignment[index]) {
                return Some(format!(
                    "{conjuncts:?}: the equality {} = {value:?} fails at {assignment:?}",
                    variable.name
                ));
            }
        }
    }
    None
}

fn assignment_substitution(
    definition: &BackendDefinition,
    assignment: [i64; 3],
) -> crate::substitution::Substitution {
    NAMES
        .iter()
        .enumerate()
        .map(|(index, name)| {
            let TermKind::Variable(variable) = term(definition, &format!("{name}:SortInt{{}}"))
                .kind()
                .clone()
            else {
                unreachable!("a variable")
            };
            (
                variable,
                term(definition, &Operand::Literal(assignment[index]).kore()),
            )
        })
        .collect()
}

fn ground_value(term: &Term) -> Option<i64> {
    match term.kind() {
        TermKind::DomainValue { value, .. } => {
            std::str::from_utf8(value.as_bytes()).ok()?.parse().ok()
        }
        _ => None,
    }
}

fn literal(operator: &'static str, left: Operand, right: Operand, polarity: bool) -> Conjunct {
    Conjunct::Literal {
        operator,
        left,
        right,
        negations: 0,
        polarity,
    }
}

const X: Operand = Operand::Variable(0);
const Y: Operand = Operand::Variable(1);

#[test]
fn each_comparison_identity_refutes_exactly_its_complement() {
    let definition = definition();
    // `a <op> b` beside the complementary comparison is contradictory; beside a compatible one
    // it is not.
    let complements = [
        ("ltInt", "geInt", false),
        ("leInt", "gtInt", false),
        ("gtInt", "leInt", false),
        ("geInt", "ltInt", false),
        ("eqInt", "neInt", false),
        ("leInt", "ltInt", true),
        ("geInt", "gtInt", true),
        ("leInt", "geInt", true),
    ];
    for (first, second, compatible) in complements {
        let conjuncts = [literal(first, X, Y, true), literal(second, X, Y, true)];
        let predicates = conjuncts
            .iter()
            .map(|conjunct| conjunct.predicate(&definition))
            .collect::<Vec<_>>();
        assert_eq!(
            contradictory(&predicates),
            !compatible,
            "{first} beside {second}"
        );
        assert_eq!(check(&definition, &conjuncts), None);
    }
    // The reversed argument order of `>` and `>=`: `X > Y` is `Y < X`, so it refutes `Y >= X`.
    let conjuncts = [literal("gtInt", X, Y, true), literal("geInt", Y, X, true)];
    let predicates = conjuncts
        .iter()
        .map(|conjunct| conjunct.predicate(&definition))
        .collect::<Vec<_>>();
    assert!(contradictory(&predicates));
}

#[test]
fn atoms_true_wherever_defined_refute_their_negation_only() {
    let definition = definition();
    let required = |text: &str, polarity: bool| {
        Predicate::Equals(
            term(&definition, text),
            term(
                &definition,
                &format!(r#"\dv{{SortBool{{}}}}("{polarity}")"#),
            ),
        )
    };
    let key_in_its_map =
        "inKeys{}(X:SortInt{}, mapConcat{}(mapItem{}(X:SortInt{}, Y:SortInt{}), M:SortMap{}))";
    assert!(contradictory(&[required(key_in_its_map, false)]));
    assert!(!contradictory(&[required(key_in_its_map, true)]));
    let other_key =
        "inKeys{}(Y:SortInt{}, mapConcat{}(mapItem{}(X:SortInt{}, Y:SortInt{}), M:SortMap{}))";
    assert!(!contradictory(&[required(other_key, false)]));
    // `A == A` holds wherever defined; `A < A` fails wherever defined.
    assert!(contradictory(&[required(
        "eqInt{}(X:SortInt{}, X:SortInt{})",
        false
    )]));
    assert!(contradictory(&[required(
        "ltInt{}(X:SortInt{}, X:SortInt{})",
        true
    )]));
    assert!(!contradictory(&[required(
        "leInt{}(X:SortInt{}, X:SortInt{})",
        true
    )]));
}

#[test]
fn equalities_hold_on_every_satisfying_assignment() {
    let definition = definition();
    let conjuncts = [
        Conjunct::Equality(0, Y),
        Conjunct::Equality(1, Operand::Literal(2)),
    ];
    assert_eq!(check(&definition, &conjuncts), None);
    let predicates = conjuncts
        .iter()
        .map(|conjunct| conjunct.predicate(&definition))
        .collect::<Vec<_>>();
    assert_eq!(equalities(&predicates).len(), 2);
}

/// Random conjunctions of two to four conjuncts over `X`, `Y`, `Z` and the literals `-1` to `1`,
/// against brute force. With the default count the run takes well under a second.
pub(crate) fn random_conjunctions_agree_with_brute_force(cases: usize) -> Vec<String> {
    let definition = definition();
    let mut state = 0x5eed_c0d1_u64;
    let mut next = |bound: usize| {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        usize::try_from((state >> 33) % u64::try_from(bound).unwrap()).unwrap()
    };
    let mut failures = Vec::new();
    for _ in 0..cases {
        let operand = |next: &mut dyn FnMut(usize) -> usize| {
            if next(4) == 0 {
                Operand::Literal(i64::try_from(next(3)).unwrap() - 1)
            } else {
                Operand::Variable(next(3))
            }
        };
        let count = 2 + next(3);
        let conjuncts = (0..count)
            .map(|_| {
                if next(6) == 0 {
                    Conjunct::Equality(next(3), operand(&mut next))
                } else {
                    Conjunct::Literal {
                        operator: OPERATORS[next(OPERATORS.len())],
                        left: operand(&mut next),
                        right: operand(&mut next),
                        negations: next(3),
                        polarity: next(2) == 0,
                    }
                }
            })
            .collect::<Vec<_>>();
        if let Some(failure) = check(&definition, &conjuncts) {
            failures.push(failure);
        }
    }
    failures
}

#[test]
fn random_conjunctions_agree_with_brute_force_by_default() {
    let failures = random_conjunctions_agree_with_brute_force(2_000);
    assert!(failures.is_empty(), "{failures:#?}");
}

/// V7: reading `a <=Int b` with the wrong orientation refutes satisfiable conjunctions, which the
/// property test sees.
#[test]
fn a_misread_comparison_is_caught_by_the_property_test() {
    let switches = crate::confluence::switches::Switches {
        misread_int_le: true,
        ..Default::default()
    };
    let failures = crate::confluence::switches::with(switches, || {
        random_conjunctions_agree_with_brute_force(2_000)
    });
    assert!(!failures.is_empty());
}
