//! `proptest` invariants of the kept algorithms (CQ-10 commit 9): syntactic matching (row B2),
//! first-order unification (row B5), and substitution extraction (row B6), over generated
//! constructor terms of two sorts with one injection and variables of each sort.

use std::collections::BTreeSet;

use k_rust_backend::{
    definition::BackendDefinition,
    matching::{MatchMode, MatchResult, match_terms_in_definition},
    rule::Predicate,
    substitution::{Substitution, extract_substitution, substitute},
    term::{Name, Term, Variable},
    unification::{UnificationResult, unify_term_pairs},
};
use k_rust_kore::kore::parser::parse_definition;
use proptest::prelude::*;

use crate::support::internal_term;

/// Two sorts, `SortT` a subsort of `SortS`; constructors of arity one and two on `SortS`, of
/// arity one on `SortT`, and three nullary ones on each (the leaves).
fn definition() -> BackendDefinition {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortS{} []
                sort SortT{} []
                symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
                symbol c1{}(SortS{}) : SortS{} [constructor{}()]
                symbol c2{}(SortS{}, SortS{}) : SortS{} [constructor{}()]
                symbol d1{}(SortT{}) : SortT{} [constructor{}()]
                symbol s0{}() : SortS{} [constructor{}()]
                symbol s1{}() : SortS{} [constructor{}()]
                symbol s2{}() : SortS{} [constructor{}()]
                symbol t0{}() : SortT{} [constructor{}()]
                symbol t1{}() : SortT{} [constructor{}()]
                symbol t2{}() : SortT{} [constructor{}()]
            endmodule []"#,
    )
    .expect("property definition should parse");
    let mut definition = BackendDefinition::internalize(&syntax, "MAIN")
        .expect("property definition should internalize");
    definition.sort_graph.insert("SortS", [Name::from("SortT")]);
    definition
}

/// A generated term, rendered to KORE text and internalized through the definition so that
/// injections and sorts are built the way the frontend builds them.
#[derive(Clone, Debug)]
enum Generated {
    VarS(u8),
    VarT(u8),
    /// The nullary constructors `s0`..`s2` and `t0`..`t2`.
    DvS(u8),
    DvT(u8),
    C1(Box<Generated>),
    C2(Box<Generated>, Box<Generated>),
    D1(Box<Generated>),
    /// `inj{SortT{}, SortS{}}` around a `SortT` term.
    Inj(Box<Generated>),
}

impl Generated {
    fn render(&self) -> String {
        match self {
            Self::VarS(index) => format!("X{index}:SortS{{}}"),
            Self::VarT(index) => format!("Y{index}:SortT{{}}"),
            Self::DvS(value) => format!("s{value}{{}}()"),
            Self::DvT(value) => format!("t{value}{{}}()"),
            Self::C1(inner) => format!("c1{{}}({})", inner.render()),
            Self::C2(left, right) => format!("c2{{}}({}, {})", left.render(), right.render()),
            Self::D1(inner) => format!("d1{{}}({})", inner.render()),
            Self::Inj(inner) => format!("inj{{SortT{{}}, SortS{{}}}}({})", inner.render()),
        }
    }
}

fn term_t(with_variables: bool) -> impl Strategy<Value = Generated> {
    let leaf = if with_variables {
        prop_oneof![
            (0u8..2).prop_map(Generated::VarT),
            (0u8..3).prop_map(Generated::DvT),
        ]
        .boxed()
    } else {
        (0u8..3).prop_map(Generated::DvT).boxed()
    };
    leaf.prop_recursive(3, 8, 2, |inner| {
        inner.prop_map(|inner| Generated::D1(Box::new(inner)))
    })
}

fn term_s(with_variables: bool) -> impl Strategy<Value = Generated> {
    let leaf = if with_variables {
        prop_oneof![
            (0u8..3).prop_map(Generated::VarS),
            (0u8..3).prop_map(Generated::DvS),
            term_t(true).prop_map(|inner| Generated::Inj(Box::new(inner))),
        ]
        .boxed()
    } else {
        prop_oneof![
            (0u8..3).prop_map(Generated::DvS),
            term_t(false).prop_map(|inner| Generated::Inj(Box::new(inner))),
        ]
        .boxed()
    };
    leaf.prop_recursive(4, 16, 2, |inner| {
        prop_oneof![
            inner
                .clone()
                .prop_map(|inner| Generated::C1(Box::new(inner))),
            (inner.clone(), inner)
                .prop_map(|(left, right)| Generated::C2(Box::new(left), Box::new(right))),
        ]
    })
}

fn variables_of(term: &Term) -> BTreeSet<Variable> {
    term.attributes().variables.iter().cloned().collect()
}

fn idempotent(substitution: &Substitution) -> bool {
    substitution
        .values()
        .all(|value| substitute(value, substitution) == *value)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Row B2: a successful `Rewrite`-mode match of a constructor pattern against an instance
    /// of it returns a substitution whose application to the pattern is the subject.
    #[test]
    fn matching_substitution_applied_to_the_pattern_is_the_subject(
        pattern in term_s(true),
        ground_s in prop::collection::vec(term_s(false), 3),
        ground_t in prop::collection::vec(term_t(false), 2),
    ) {
        let definition = definition();
        let pattern = internal_term(&definition, &pattern.render());
        let instance = variables_of(&pattern)
            .into_iter()
            .map(|variable| {
                let name = variable.name.as_ref();
                let index = name[1..].parse::<usize>().expect("generated variable index");
                let value = if name.starts_with('X') {
                    &ground_s[index]
                } else {
                    &ground_t[index]
                };
                (variable, internal_term(&definition, &value.render()))
            })
            .collect::<Substitution>();
        let subject = substitute(&pattern, &instance);
        prop_assert!(subject.attributes().variables.is_empty());
        match match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &subject) {
            MatchResult::Success(found) => {
                prop_assert_eq!(substitute(&pattern, &found), subject);
            }
            other => prop_assert!(false, "constructor instance did not match: {other:?}"),
        }
    }

    /// Row B5: a `Unified` result is a unifier (both sides agree under it) and the substitution
    /// is idempotent, so composing it again changes nothing.
    #[test]
    fn unifier_is_idempotent_and_identifies_both_sides(
        left in term_s(true),
        right in term_s(true),
    ) {
        let definition = definition();
        let left = internal_term(&definition, &left.render());
        let right = internal_term(&definition, &right.render());
        if let UnificationResult::Unified(unified) =
            unify_term_pairs(&definition, Substitution::new(), [(left.clone(), right.clone())])
        {
            prop_assert!(unified.constraints.is_empty(), "{:?}", unified.constraints);
            prop_assert!(idempotent(&unified.substitution));
            prop_assert_eq!(
                substitute(&left, &unified.substitution),
                substitute(&right, &unified.substitution)
            );
        }
    }

    /// Row B6: extraction returns an idempotent (hence acyclic) substitution; every input
    /// equality is either exactly one binding, saturated under the whole substitution, or
    /// returned untouched among the remaining predicates (the cycle-breaking equality of each
    /// cycle stays there in its input form). An equality whose right-hand side mentions its
    /// own variable (`X = X`, `X = c1(X)`) is never a binding, as the reference backend drops
    /// `X = X` as trivial and rejects `X = c1(X)` by occurs check; such an equality may still
    /// saturate to the chosen value, so it is not a source of that binding.
    #[test]
    fn extracted_substitution_is_idempotent_and_accounts_for_every_equality(
        equalities in prop::collection::vec((0u8..3, term_s(true)), 1..5),
    ) {
        let definition = definition();
        let constraints = equalities
            .iter()
            .map(|(index, value)| {
                Predicate::Equals(
                    internal_term(&definition, &Generated::VarS(*index).render()),
                    internal_term(&definition, &value.render()),
                )
            })
            .collect::<Vec<_>>();
        let (found, remaining) = extract_substitution(&constraints, &definition.sort_graph);
        prop_assert!(idempotent(&found), "{:?}", found);
        for (variable, value) in &found {
            prop_assert!(
                !value.attributes().variables.contains(variable),
                "{:?} occurs in its own binding {:?}", variable, value
            );
            let sources = constraints
                .iter()
                .filter(|constraint| match constraint {
                    Predicate::Equals(left, right) => {
                        left == &Term::variable(variable.clone())
                            && !right.attributes().variables.contains(variable)
                            && substitute(right, &found) == *value
                    }
                    _ => false,
                })
                .count();
            prop_assert_eq!(sources, 1, "{:?} = {:?} has {} sources", variable, value, sources);
        }
        for predicate in &remaining {
            prop_assert!(constraints.contains(predicate), "{:?} is not an input", predicate);
        }
        prop_assert_eq!(found.len() + remaining.len(), constraints.len());
    }
}
