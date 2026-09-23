//! The order-constraint model of `lean/KRust/SubsortEncoding.lean` against the Rust, through the
//! Lean model conformance harness (`lean_conformance::check`):
//! - `new` against the formula `Encoding::less_than_eq` builds;
//! - `old` against the formula `OrderRelation::full_disjunction` builds.
//!
//! `new_equiv` proves `old R a b` and `new R a b` equivalent in every model of a free datatype,
//! for every relation `R` and every pair of sides. It says something about the Rust only if
//! `less_than_eq` and `full_disjunction` build those two formulas; these tests check that on
//! generated relations and sides, as the `ground_side_encoding_is_equivalent` test does, but by
//! comparing the formulas themselves rather than asking Z3 whether they are equivalent. That
//! test checks the Rust against the conclusion of the theorem, and so also checks Z3 against the
//! hypothesis `hI`; these check the Rust against the model the theorem is about, without Z3.
//!
//! The model's ground values are `G = Nat`: a cached ground sort value (a value of
//! `closed_values`) is its index in `ground_values`, so two ground values are equal in the model
//! exactly when they are the same AST. The model's `other n` is the `n`th of four expressions that
//! are not cached ground values: two variables, a constructor applied to a variable, and an
//! accessor applied to a cached value (a closed term that is not a cached constructor term).
//!
//! The Rust answer is the Z3 formula read back as a disjunction of conjunctions of equalities
//! (`Dnf`): `true` is `[[]]`, `false` is `[]`, an `or` is one conjunction per argument, an `and`
//! is one equality per argument, and a lone `and` or equality is a one-conjunction disjunction.
//! Each side of an equality is read back by AST identity against the generated sides. Any other
//! shape is answered by its text, which no model answer equals.

use lean_conformance::check;
use proptest::prelude::*;
use serde_json::{Value, json};
use z3::DeclKind;
use z3::ast::{Ast, Bool, Datatype};

use super::super::{
    Encoding, EncodingBase, Grammar, OrderRelation, PackedTerm, Sort, SortHead, TermSorts,
    collect_packed_term_sorts,
};
use super::cached_encoding_fixture;

/// `cached_encoding_fixture(sort_count)`: the grammar, the term and the top sort.
type Fixture = (Grammar, std::rc::Rc<PackedTerm>, Sort);

/// Coverage is asserted only for runs of at least this many cases.
const COVERAGE_CASES: usize = 1024;

/// The number of generated expressions that are not cached ground values.
const OTHER_SIDES: usize = 4;

/// One side of an order constraint: a cached ground value (by index, reduced modulo the number
/// of cached values) or one of the `OTHER_SIDES` other expressions (reduced modulo that number).
#[derive(Clone, Copy, Debug)]
struct Side {
    ground: bool,
    index: usize,
}

/// One generated order constraint: the grammar size of `cached_encoding_fixture`, the semantic
/// and the syntactic relation as index pairs into the cached ground values, which relation the
/// constraint reads, and its two sides.
#[derive(Clone, Debug)]
struct Case {
    sort_count: usize,
    semantic: Vec<(usize, usize)>,
    syntactic: Vec<(usize, usize)>,
    use_syntactic: bool,
    lesser: Side,
    greater: Side,
}

fn side() -> impl Strategy<Value = Side> {
    (any::<bool>(), 0usize..16).prop_map(|(ground, index)| Side { ground, index })
}

fn case() -> impl Strategy<Value = Case> {
    let pairs = || proptest::collection::vec((0usize..16, 0usize..16), 0..12);
    (2usize..5, pairs(), pairs(), any::<bool>(), side(), side()).prop_map(
        |(sort_count, semantic, syntactic, use_syntactic, lesser, greater)| Case {
            sort_count,
            semantic,
            syntactic,
            use_syntactic,
            lesser,
            greater,
        },
    )
}

/// The encoding of `cached_encoding_fixture(case.sort_count)` with both relations replaced by the
/// generated ones, as `ground_side_encoding_is_equivalent` builds it, and the generated sides:
/// the cached ground values in `ground_values` order, then the `OTHER_SIDES` other expressions.
struct Realized<'a> {
    encoding: Encoding<'a>,
    sides: Vec<Datatype>,
    ground: usize,
}

/// The encoding base of `fixture`, as `EncodingBase::build` makes it, its term sorts, and its
/// cached ground values in `ground_values` order.
fn fixture_base((grammar, term, top_sort): &Fixture) -> (EncodingBase, TermSorts, Vec<Datatype>) {
    let mut term_sorts = TermSorts::default();
    collect_packed_term_sorts(term, &mut term_sorts.heads, &mut term_sorts.ground);
    let base = EncodingBase::build(grammar, top_sort, &term_sorts).unwrap();
    let ground_values = base
        .ground_values
        .borrow()
        .values()
        .cloned()
        .collect::<Vec<_>>();
    (base, term_sorts, ground_values)
}

impl Case {
    fn relation(&self) -> &[(usize, usize)] {
        if self.use_syntactic {
            &self.syntactic
        } else {
            &self.semantic
        }
    }

    /// The position of `side` in `Realized::sides`.
    fn position(&self, side: Side, ground: usize) -> usize {
        if side.ground {
            ground_index(side.index, ground)
        } else {
            ground + side.index % OTHER_SIDES
        }
    }

    fn realize<'a>(&self, fixture: &'a Fixture) -> Realized<'a> {
        let (grammar, _, top_sort) = fixture;
        let (mut base, term_sorts, ground_values) = fixture_base(fixture);
        let ground = ground_values.len();
        let relation = |pairs: &[(usize, usize)]| {
            OrderRelation::new(
                pairs
                    .iter()
                    .map(|&(left, right)| {
                        (
                            ground_values[ground_index(left, ground)].clone(),
                            ground_values[ground_index(right, ground)].clone(),
                        )
                    })
                    .collect(),
            )
        };
        base.semantic_relation = relation(&self.semantic);
        base.syntactic_relation = relation(&self.syntactic);
        let mut encoding =
            Encoding::new_with_term_sorts(grammar, top_sort, false, &term_sorts).unwrap();
        encoding.base = std::rc::Rc::new(base);

        let sort = &encoding.datatype.sort;
        let box_variant =
            &encoding.datatype.variants[encoding.head_indexes[&SortHead::from(top_sort)]];
        let boxed = encoding
            .sort_value(top_sort, &std::collections::BTreeMap::new())
            .unwrap();
        let x = Datatype::new_const("x", sort);
        let others = [
            x.clone(),
            Datatype::new_const("y", sort),
            box_variant.constructor.apply(&[&x]).as_datatype().unwrap(),
            box_variant.accessors[0]
                .apply(&[&boxed])
                .as_datatype()
                .unwrap(),
        ];
        let sides = ground_values.into_iter().chain(others).collect();
        Realized {
            encoding,
            sides,
            ground,
        }
    }

    /// The model's input: `{"relation": [[l, r], …], "lesser": side, "greater": side}`.
    fn input(&self) -> Value {
        let ground = ground_count(self.sort_count);
        let side = |side: Side| side_json(self.position(side, ground), ground);
        json!({
            "relation": self
                .relation()
                .iter()
                .map(|&(left, right)| {
                    json!([ground_index(left, ground), ground_index(right, ground)])
                })
                .collect::<Vec<_>>(),
            "lesser": side(self.lesser),
            "greater": side(self.greater),
        })
    }

    /// The formula `build` makes from the realized relation and sides, read back as a `Dnf`.
    fn answer(&self, build: impl Fn(&Encoding<'_>, &Datatype, &Datatype, bool) -> Bool) -> Value {
        let fixture = cached_encoding_fixture(self.sort_count);
        let realized = self.realize(&fixture);
        let lesser = &realized.sides[self.position(self.lesser, realized.ground)];
        let greater = &realized.sides[self.position(self.greater, realized.ground)];
        let formula = build(&realized.encoding, lesser, greater, self.use_syntactic);
        dnf_json(&formula, &realized)
    }
}

/// The number of cached ground values of `cached_encoding_fixture(sort_count)`.
fn ground_count(sort_count: usize) -> usize {
    thread_local! {
        static COUNTS: std::cell::RefCell<std::collections::BTreeMap<usize, usize>> =
            const { std::cell::RefCell::new(std::collections::BTreeMap::new()) };
    }
    COUNTS.with(|counts| {
        *counts
            .borrow_mut()
            .entry(sort_count)
            .or_insert_with(|| fixture_base(&cached_encoding_fixture(sort_count)).2.len())
    })
}

/// A generated ground index reduced to one of the `ground` cached ground values.
fn ground_index(index: usize, ground: usize) -> usize {
    index % ground
}

/// The model's `Tm Nat` for the side at `position` of `Realized::sides`.
fn side_json(position: usize, ground: usize) -> Value {
    if position < ground {
        json!({ "val": position })
    } else {
        json!({ "other": position - ground })
    }
}

/// An equality `lhs = rhs` as `[lhs, rhs]`, each side read back by AST identity.
fn equality_json(equality: &Bool, realized: &Realized<'_>) -> Option<Value> {
    if equality.decl().kind() != DeclKind::Eq {
        return None;
    }
    let sides = equality
        .children()
        .iter()
        .map(|child| {
            let child = child.as_datatype()?;
            let position = realized.sides.iter().position(|side| *side == child)?;
            Some(side_json(position, realized.ground))
        })
        .collect::<Option<Vec<_>>>()?;
    (sides.len() == 2).then_some(Value::Array(sides))
}

/// A conjunction: the equalities of an `and`, or one equality.
fn conjunction_json(conjunction: &Bool, realized: &Realized<'_>) -> Option<Value> {
    if conjunction.decl().kind() == DeclKind::And {
        conjunction
            .children()
            .iter()
            .map(|child| equality_json(&child.as_bool()?, realized))
            .collect::<Option<Vec<_>>>()
            .map(Value::Array)
    } else {
        Some(json!([equality_json(conjunction, realized)?]))
    }
}

/// The formula as the model's `Dnf Nat`, or its text when it is not of that shape.
fn dnf_json(formula: &Bool, realized: &Realized<'_>) -> Value {
    let dnf = match formula.decl().kind() {
        DeclKind::True => Some(json!([[]])),
        DeclKind::False => Some(json!([])),
        DeclKind::Or => formula
            .children()
            .iter()
            .map(|child| conjunction_json(&child.as_bool()?, realized))
            .collect::<Option<Vec<_>>>()
            .map(Value::Array),
        _ => conjunction_json(formula, realized).map(|conjunction| json!([conjunction])),
    };
    dnf.unwrap_or_else(|| Value::String(formula.to_string()))
}

#[test]
fn less_than_eq_agrees_with_new() {
    let Some(answers) = check("lessThanEq", case(), Case::input, |case| {
        case.answer(|encoding, lesser, greater, syntactic| {
            encoding.less_than_eq(lesser, greater, syntactic).unwrap()
        })
    }) else {
        return;
    };
    // Both sides ground is the only case that gives a constant: `[[]]` or `[]`.
    let constant = |value: &serde_json::Value| *value == json!([[]]) || *value == json!([]);
    let constants = answers.iter().filter(|answer| constant(answer)).count();
    let taken = answers
        .iter()
        .filter(|answer| **answer == json!([[]]))
        .count();
    eprintln!(
        "lean bridge: lessThanEq gave a constant in {constants} of {} cases, true in {taken}",
        answers.len()
    );
    if answers.len() >= COVERAGE_CASES {
        assert!(
            taken > 0 && taken < constants && constants < answers.len(),
            "the generator should reach both constants and formulas with a variable side"
        );
    }
}

#[test]
fn full_disjunction_agrees_with_old() {
    let Some(answers) = check("fullDisjunction", case(), Case::input, |case| {
        case.answer(|encoding, lesser, greater, syntactic| {
            let relation = if syntactic {
                &encoding.syntactic_relation
            } else {
                &encoding.semantic_relation
            };
            relation.full_disjunction(lesser, greater)
        })
    }) else {
        return;
    };
    let lengths = answers
        .iter()
        .map(|answer| answer.as_array().map_or(0, Vec::len))
        .collect::<std::collections::BTreeSet<_>>();
    eprintln!(
        "lean bridge: fullDisjunction gave {} distinct disjunct counts in {} cases",
        lengths.len(),
        answers.len()
    );
    if answers.len() >= COVERAGE_CASES {
        assert!(
            lengths.contains(&1) && lengths.len() > 2,
            "the generator should reach empty and larger relations"
        );
    }
}
