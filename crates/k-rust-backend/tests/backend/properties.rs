//! `proptest` invariants of the backend algorithms: syntactic matching
//! (backend.matching.syntactic), first-order unification (backend.unification.syntactic), and
//! substitution extraction (backend.substitution.extract), over generated constructor terms of
//! two sorts with one injection and variables of each sort.

use std::collections::BTreeSet;

use k_rust_backend::{
    definition::BackendDefinition,
    matching::{MatchMode, MatchResult, match_terms_in_definition},
    rule::Predicate,
    substitution::{Substitution, extract_substitution, substitute},
    term::{Term, Variable},
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
                axiom{R} \exists{R}(Value:SortS{},
                    \equals{SortS{}, R}(Value:SortS{}, inj{SortT{}, SortS{}}(From:SortT{})))
                    [subsort{SortT{}, SortS{}}()]
            endmodule []"#,
    )
    .expect("property definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("property definition should internalize")
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

    /// backend.matching.syntactic: a successful `Rewrite`-mode match of a constructor pattern
    /// against an instance of it returns a substitution whose application to the pattern is the
    /// subject.
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

    /// backend.unification.syntactic: a `Unified` result is a unifier (both sides agree under
    /// it) and the substitution is idempotent, so composing it again changes nothing.
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

    /// backend.substitution.extract: extraction returns an idempotent (hence acyclic)
    /// substitution; every input equality is either exactly one binding, saturated under the
    /// whole substitution, or
    /// returned untouched among the remaining predicates (the cycle-breaking equality of each
    /// cycle stays there in its input form). An equality whose right-hand side mentions its
    /// own variable (`X = X`, `X = c1(X)`) is never a binding: `X = X` holds trivially and
    /// determines nothing, and an idempotent substitution cannot bind `X` to a term containing
    /// `X`; such an equality may still saturate to the chosen value, so it is not a source of
    /// that binding.
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
        let (found, remaining) = extract_substitution(&constraints, definition.sort_graph());
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

/// What an edge of a generated rule graph does.
#[derive(Clone, Debug)]
enum EdgeKind {
    /// `n{from} => n{to}`.
    Plain,
    /// `n{from} => seq(log(text), write(1, "x"), n{to})`, which `n{to}` follows: one of two
    /// texts, so converging paths log alike or not.
    Effect(bool),
    /// `n{from} => n{to}` under a condition no solver decides, which leaves a remainder.
    Guarded,
    /// `n{from} => node(\bottom)`, an undefined step.
    Undefined,
}

/// A generated rule graph over the nodes `n0`..`n6` and its run's options.
#[derive(Clone, Debug)]
struct GraphCase {
    /// Each edge with its kind and whether its rule is terminal (`Some(true)`) or a cut point
    /// (`Some(false)`).
    edges: Vec<(u8, u8, EdgeKind, Option<bool>)>,
    max_depth: u64,
    max_breadth: Option<usize>,
    any: bool,
    retain_trace: bool,
}

fn graph_case() -> impl Strategy<Value = GraphCase> {
    let edge_kind = prop_oneof![
        6 => Just(EdgeKind::Plain),
        2 => any::<bool>().prop_map(EdgeKind::Effect),
        1 => Just(EdgeKind::Guarded),
        1 => Just(EdgeKind::Undefined),
    ];
    let mark = prop_oneof![
        12 => Just(None),
        1 => Just(Some(true)),
        1 => Just(Some(false)),
    ];
    let breadth = prop_oneof![13 => Just(None), 7 => (1usize..8).prop_map(Some)];
    // Nodes are layered (`n0`; `n1`, `n2`; `n3`, `n4`; `n5`, `n6`) and most edges go one layer
    // down, so that paths of one length often meet; the others go anywhere, cycles included.
    // Each node has up to three edges, `n0` and the second layer at least one.
    let layer = |node: u8| node.div_ceil(2);
    let target = (0u8..2, 0u8..7, proptest::bool::weighted(0.8));
    let out_edges = |least| {
        proptest::collection::vec((target.clone(), edge_kind.clone(), mark.clone()), least..4)
    };
    (
        (
            out_edges(1),
            proptest::collection::vec(out_edges(1), 2),
            proptest::collection::vec(out_edges(0), 4),
        )
            .prop_map(move |(first, second, rest)| {
                std::iter::once(first)
                    .chain(second)
                    .chain(rest)
                    .zip(0u8..)
                    .flat_map(|(edges, from)| {
                        edges
                            .into_iter()
                            .map(move |((pick, anywhere, down), kind, mark)| {
                                let to = if down && layer(from) < 3 {
                                    2 * layer(from) + 1 + pick
                                } else {
                                    anywhere
                                };
                                (from, to, kind, mark)
                            })
                    })
                    .collect::<Vec<_>>()
            }),
        2u64..10,
        breadth,
        proptest::bool::weighted(0.2),
        any::<bool>(),
    )
        .prop_map(
            |(edges, max_depth, max_breadth, any, retain_trace)| GraphCase {
                edges,
                max_depth,
                max_breadth,
                any,
                retain_trace,
            },
        )
}

/// A merged state-set execution over a generated rule graph, bounded so that cycles end, is the
/// deduplicated path-set execution with the same coverage
/// (`exploration_merge::assert_merged_state_set_agrees`), where the path-set run stays within
/// its breadth bound; every third case also runs observed, and returns the unobserved run's
/// leaves. A fixed seed makes the cases the same on every run, and at least a quarter of them
/// must merge, so the property is not met by runs that never merge.
#[test]
fn a_merged_state_set_execution_of_a_rule_graph_is_its_deduplicated_path_set() {
    use std::cell::Cell;

    use k_rust_backend::{
        rewrite::{ExecutionMode, ExecutionOptions, HaltReason, execute, execute_observed},
        search::ResultModality,
        transition::ObservationOptions,
    };
    use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};

    use crate::exploration_merge::{
        assert_merged_state_set_agrees, edge, graph_definition, guarded_edge, logging, node,
        pattern, reaches_breadth_bound, seq_edge,
    };

    const CASES: u32 = 256;
    let (cases, merging, beyond_breadth) = (Cell::new(0), Cell::new(0), Cell::new(0));
    let mut runner = TestRunner::new_with_rng(
        Config {
            cases: CASES,
            failure_persistence: None,
            ..Config::default()
        },
        TestRng::deterministic_rng(RngAlgorithm::ChaCha),
    );
    let outcome = runner.run(&graph_case(), |case| {
        let mut rules = (0..7)
            .map(|index| {
                let name = format!("n{index}");
                seq_edge(&format!("s{index}"), &name, &node(&name))
            })
            .collect::<String>();
        let (mut terminal_rules, mut cut_point_rules) = (Vec::new(), Vec::new());
        for (index, (from, to, kind, mark)) in case.edges.iter().enumerate() {
            let (label, from, to) = (format!("e{index}"), format!("n{from}"), format!("n{to}"));
            rules += &match kind {
                EdgeKind::Plain => edge(&label, &from, &node(&to)),
                EdgeKind::Effect(left) => edge(
                    &label,
                    &from,
                    &logging(if *left { "a" } else { "b" }, "x", &to),
                ),
                EdgeKind::Guarded => guarded_edge(&label, &from, &node(&to)),
                EdgeKind::Undefined => edge(&label, &from, r#"node{}(\bottom{SortString{}}())"#),
            };
            match mark {
                Some(true) => terminal_rules.push(label),
                Some(false) => cut_point_rules.push(label),
                None => {}
            }
        }
        let definition = graph_definition(&rules);
        let initial = pattern(&definition, &node("n0"));
        let options = ExecutionOptions {
            max_depth: case.max_depth,
            max_breadth: case.max_breadth,
            mode: if case.any {
                ExecutionMode::Any
            } else {
                ExecutionMode::All
            },
            terminal_rules: terminal_rules.into_iter().collect(),
            cut_point_rules: cut_point_rules.into_iter().collect(),
            retain_trace: case.retain_trace,
            ..ExecutionOptions::default()
        };
        let (state_set, path_set) =
            assert_merged_state_set_agrees(&definition, &initial, &options, &format!("{case:?}"));
        cases.set(cases.get() + 1);
        merging.set(merging.get() + usize::from(state_set.merged > 0));
        beyond_breadth
            .set(beyond_breadth.get() + usize::from(reaches_breadth_bound(&path_set.result)));
        if cases.get() % 3 == 0 {
            let options = ExecutionOptions {
                result_modality: ResultModality::StateSet,
                ..options
            };
            let mut observed = execute_observed(
                &definition,
                initial.clone(),
                options.clone(),
                &ObservationOptions::all(),
            );
            observed.discarded.clear();
            // An observed run adds its observations to each leaf, and to each candidate of a
            // `Branch` or `CutPointRule` halt.
            for leaf in &mut observed.leaves {
                leaf.branch.clear();
                leaf.observations.clear();
                if let HaltReason::Branch {
                    branches: candidates,
                    ..
                }
                | HaltReason::CutPointRule {
                    next_states: candidates,
                    ..
                } = &mut leaf.halt_reason
                {
                    for candidate in candidates {
                        candidate.observations.clear();
                    }
                }
            }
            assert_eq!(observed, execute(&definition, initial, options), "{case:?}");
        }
        Ok(())
    });
    if let Err(failure) = outcome {
        panic!("{failure}");
    }
    eprintln!(
        "rule graphs: {} cases, {} merging, {} beyond the path-set breadth bound",
        cases.get(),
        merging.get(),
        beyond_breadth.get()
    );
    assert!(
        4 * merging.get() >= cases.get(),
        "{} of {} cases merge",
        merging.get(),
        cases.get()
    );
}
