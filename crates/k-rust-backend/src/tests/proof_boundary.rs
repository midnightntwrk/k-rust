//! Boundary contracts of `crate::proof::prove_claim`: the leaf a state gets when its own
//! simplification fails, when the implication check shows it empty, and when the step that
//! produced it or the destination check could not be decided.
//!
//! The undecided answers come from a scripted solver: an SMT solver may answer `Unknown` for
//! one query and decide another (Z3 under a timeout does), and these contracts are about what
//! the proof makes of such answers, not about which query a real solver decides.

use std::collections::BTreeSet;

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    claim::{ClaimAttributes, ReachabilityClaim, ReachabilityMode},
    definition::BackendDefinition,
    proof::{
        ProofIndeterminateReason, ProofLeaf, ProofLeafOutcome, ProofOptions, ProofResult,
        ProofStatus, prove_claim,
    },
    rewrite::{IndeterminateReason, Pattern, TraceKind},
    rule::Predicate,
    simplify::SimplificationError,
    smt::{NoSolver, Satisfiability, SmtError, SmtSolver, Validity},
    stop::Stoppable,
    substitution::Substitution,
    term::{Term, TermKind, Variable},
};

/// Constructors `a`, `b`, `c`, `done`, `start(_)`, `wrap(_)`; total functions `f` and `g`
/// without equations; `unsupported(\dv)`, an application of a hooked function whose hook the
/// backend does not implement and which has no equations, declared `impure` so that it is the
/// unsupported-hook error where the simplifier reaches it (a pure `total` one is left for the run
/// to refuse where it uses the value); and the rewrite rules `rules`.
fn definition(rules: &str) -> BackendDefinition {
    let source = format!(
        r#"[]
            module MAIN
                sort SortS{{}} []
                sort SortV{{}} [hasDomainValues{{}}()]
                symbol a{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol b{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol c{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol done{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol start{{}}(SortS{{}}) : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol wrap{{}}(SortS{{}}) : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol f{{}}(SortS{{}}) : SortS{{}} [function{{}}(), total{{}}()]
                symbol g{{}}(SortS{{}}) : SortS{{}} [function{{}}(), total{{}}()]
                hooked-symbol unsupported{{}}(SortV{{}}) : SortS{{}}
                    [function{{}}(), total{{}}(), impure{{}}(), hook{{}}("TEST.unimplemented")]
                {rules}
            endmodule []"#
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

/// The rewrite rule `left => right` with label `label` and, when given, priority `priority`.
fn rule(label: &str, left: &str, right: &str, priority: Option<u32>) -> String {
    let priority = priority.map_or_else(String::new, |priority| {
        format!(r#", priority{{}}("{priority}")"#)
    });
    format!(
        r#"
                axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}({left}, \top{{SortS{{}}}}()),
                    \and{{SortS{{}}}}({right}, \top{{SortS{{}}}}())
                ) [label{{}}("{label}"){priority}]"#
    )
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
        .expect("term should internalize")
}

fn pattern(definition: &BackendDefinition, source: &str, constraints: Vec<Predicate>) -> Pattern {
    Pattern {
        term: term(definition, source),
        constraints,
    }
}

/// The all-path claim `lhs => \or(rhs)`, with the variables `existentials` of `rhs` quantified.
fn claim(lhs: Pattern, rhs: Vec<Pattern>, existentials: &[Variable]) -> ReachabilityClaim {
    ReachabilityClaim {
        lhs,
        rhs,
        existentials: existentials.iter().cloned().collect::<BTreeSet<_>>(),
        mode: ReachabilityMode::AllPath,
        attributes: ClaimAttributes {
            label: Some("boundary".into()),
            unique_id: "boundary".into(),
            trusted: false,
            source: None,
            location: None,
            sentence: 0,
        },
        unstated: None,
    }
}

fn prove(
    definition: &BackendDefinition,
    claim: &ReachabilityClaim,
    options: ProofOptions,
    solver: &dyn SmtSolver,
) -> ProofResult {
    prove_claim(definition, claim, &[], options, solver).expect("the proof should run")
}

fn head(term: &Term) -> String {
    match term.kind() {
        TermKind::Application { symbol, .. } => symbol.name.to_string(),
        other => panic!("expected an application, found {other:?}"),
    }
}

/// The leaves whose outcome satisfies `outcome`.
fn leaves_where(
    result: &ProofResult,
    outcome: impl Fn(&ProofLeafOutcome) -> bool,
) -> Vec<&ProofLeaf> {
    result
        .leaves
        .iter()
        .filter(|leaf| outcome(&leaf.outcome))
        .collect()
}

fn mentions_symbol(predicates: &[Predicate], name: &str) -> bool {
    let mut found = false;
    for predicate in predicates {
        predicate.visit_terms(&mut |term| {
            term.visit_symbols(&mut |symbol| found |= symbol.name.as_ref() == name);
        });
    }
    found
}

/// A solver whose satisfiability answer is `Unknown` for a query that mentions the symbol
/// `undecided_symbol` and `Sat` otherwise, and whose validity answer is always `validity`.
struct ScriptedSolver {
    undecided_symbol: &'static str,
    validity: Validity,
}

impl SmtSolver for ScriptedSolver {
    fn is_sat(
        &self,
        predicates: &[Predicate],
        _substitution: &Substitution,
    ) -> Stoppable<Result<Satisfiability, SmtError>> {
        Ok(Ok(if mentions_symbol(predicates, self.undecided_symbol) {
            Satisfiability::Unknown("scripted".into())
        } else {
            Satisfiability::Sat
        }))
    }

    fn check_predicates(
        &self,
        _known: &[Predicate],
        _substitution: &Substitution,
        _checked: &[Predicate],
    ) -> Stoppable<Result<Validity, SmtError>> {
        Ok(Ok(self.validity.clone()))
    }
}

fn is_unsupported_hook(outcome: &ProofLeafOutcome) -> bool {
    matches!(
        outcome,
        ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Simplification(
            SimplificationError::UnsupportedHook { hook, .. }
        )) if hook == "TEST.unimplemented"
    )
}

/// A state whose simplification fails, in its term or in its constraints, cannot be decided:
/// it is an `Indeterminate` leaf carrying the failure, and the claim is `Indeterminate`, neither
/// proven nor failed.
#[test]
fn a_state_whose_simplification_fails_is_an_indeterminate_leaf() {
    let definition = definition("");
    let unsupported = r#"unsupported{}(\dv{SortV{}}("1"))"#;
    let in_constraints = |definition: &BackendDefinition, source: &str| {
        pattern(
            definition,
            source,
            vec![Predicate::Equals(
                term(definition, unsupported),
                term(definition, "b{}()"),
            )],
        )
    };
    let cases = [
        (
            "term",
            pattern(&definition, &format!("wrap{{}}({unsupported})"), Vec::new()),
        ),
        ("constraints", in_constraints(&definition, "wrap{}(a{}())")),
    ];
    for (place, lhs) in cases {
        let claim = claim(lhs, vec![pattern(&definition, "done{}()", Vec::new())], &[]);
        let result = prove(&definition, &claim, ProofOptions::default(), &NoSolver);
        let [leaf] = result.leaves.as_slice() else {
            panic!("{place}: expected one leaf, found {result:#?}");
        };
        assert!(is_unsupported_hook(&leaf.outcome), "{place}: {leaf:#?}");
        assert_eq!(leaf.depth, 0, "{place}");
        assert_eq!(result.status, ProofStatus::Indeterminate, "{place}");
        assert_eq!(result.stopped, None, "{place}");
    }
}

/// A rule whose `requires` cannot be simplified leaves the step that tries it undecided: the
/// state is an `Indeterminate` leaf carrying the failure, and it has no successor.
#[test]
fn a_step_whose_rule_condition_fails_to_simplify_is_an_indeterminate_leaf() {
    let condition = r#"\equals{SortS{}, SortS{}}(unsupported{}(\dv{SortV{}}("1")), a{}())"#;
    let definition = definition(&format!(
        r#"
                axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}(start{{}}(X:SortS{{}}), {condition}),
                    \and{{SortS{{}}}}(done{{}}(), \top{{SortS{{}}}}())
                ) [label{{}}("guarded")]"#
    ));
    let claim = claim(
        pattern(&definition, "start{}(a{}())", Vec::new()),
        vec![pattern(&definition, "done{}()", Vec::new())],
        &[],
    );
    let result = prove(&definition, &claim, ProofOptions::default(), &NoSolver);
    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one leaf, found {result:#?}");
    };
    assert!(is_unsupported_hook(&leaf.outcome), "{leaf:#?}");
    assert_eq!(leaf.depth, 0);
    assert_eq!(head(&leaf.pattern.term), "start");
    assert_eq!(result.status, ProofStatus::Indeterminate);
}

/// When the destination check finds a state empty, the state has no instance. At the claim's
/// initial state the claim holds vacuously, so the leaf is proven. After a step the state is a
/// successor that denotes no state, so it is no successor: the configuration the step was taken
/// from has instances, the step applies to them and gives them no successor, so they are the
/// step's undefined step, a `Trivial` leaf over `start(X)` one step below, which fails the claim
/// unless vacuous proofs are allowed. Here the state's own constraints are satisfiable, and the
/// validity check of the destination's condition, which adds the facts the state's term
/// implies, finds them inconsistent.
#[test]
fn a_state_the_destination_check_shows_empty_is_vacuous_after_a_step_only() {
    let definition = definition(&rule(
        "start-wrap",
        "start{}(X:SortS{})",
        "wrap{}(X:SortS{})",
        None,
    ));
    let y = Variable::new("Y", crate::term::Sort::simple("SortS"));
    let destination = pattern(
        &definition,
        "wrap{}(Y:SortS{})",
        vec![Predicate::Equals(
            term(&definition, "f{}(Y:SortS{})"),
            term(&definition, "a{}()"),
        )],
    );
    let solver = ScriptedSolver {
        undecided_symbol: "none",
        validity: Validity::InconsistentGroundTruth,
    };
    let vacuous_proof = |leaf: &ProofLeafOutcome| {
        matches!(
            leaf,
            ProofLeafOutcome::Proven(condition) if condition.predicates == [Predicate::False]
        )
    };
    let cases = [
        (
            "initial",
            "wrap{}(X:SortS{})",
            false,
            0,
            ProofStatus::Proven,
        ),
        (
            "after a step",
            "start{}(X:SortS{})",
            false,
            1,
            ProofStatus::Failed,
        ),
        (
            "allowed",
            "start{}(X:SortS{})",
            true,
            1,
            ProofStatus::Proven,
        ),
    ];
    for (case, lhs, allow_vacuous, depth, status) in cases {
        let claim = claim(
            pattern(&definition, lhs, Vec::new()),
            vec![destination.clone()],
            std::slice::from_ref(&y),
        );
        let options = ProofOptions {
            allow_vacuous,
            ..ProofOptions::default()
        };
        let result = prove(&definition, &claim, options, &solver);
        let [leaf] = result.leaves.as_slice() else {
            panic!("{case}: expected one leaf, found {result:#?}");
        };
        assert_eq!(leaf.depth, depth, "{case}");
        let expected_head = if depth == 0 { "wrap" } else { "start" };
        assert_eq!(head(&leaf.pattern.term), expected_head, "{case}");
        if status == ProofStatus::Proven {
            assert!(vacuous_proof(&leaf.outcome), "{case}: {leaf:#?}");
        } else {
            assert_eq!(leaf.outcome, ProofLeafOutcome::Trivial, "{case}");
        }
        assert_eq!(result.status, status, "{case}");
    }
}

/// The remainder of a step whose lower-priority rule could not be decided on it is a state
/// whose successors are unknown: the proof does not step it again, and it is an `Indeterminate`
/// leaf carrying the lower rule's reason, at the depth of the state it remains of.
#[test]
fn a_remainder_left_undecided_by_a_lower_priority_rule_is_an_indeterminate_leaf() {
    let rules = [
        rule("wrap-a", "wrap{}(a{}())", "b{}()", Some(10)),
        rule("wrap-g", "wrap{}(g{}(Z:SortS{}))", "c{}()", Some(50)),
    ]
    .concat();
    let definition = definition(&rules);
    let claim = claim(
        pattern(&definition, "wrap{}(X:SortS{})", Vec::new()),
        vec![pattern(&definition, "b{}()", Vec::new())],
        &[],
    );
    // Narrowing `X` to `g(Z)` asks whether `X = g(Z)` is satisfiable: undecided.
    let solver = ScriptedSolver {
        undecided_symbol: "g",
        validity: Validity::Contingent,
    };
    let result = prove(&definition, &claim, ProofOptions::default(), &solver);
    // The branch `wrap-a` took reaches `b()`, a proven leaf at depth 1, deeper than the
    // remainder's leaf at depth 0, which is the horizon: it is not reported.
    assert!(
        leaves_where(&result, |outcome| matches!(
            outcome,
            ProofLeafOutcome::Proven(_)
        ))
        .is_empty(),
        "{result:#?}"
    );
    let indeterminate = leaves_where(&result, |outcome| {
        matches!(
            outcome,
            ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Rewrite(
                IndeterminateReason::Smt { rule_id, .. }
            )) if rule_id.contains("wrap-g")
        )
    });
    let [remainder] = indeterminate.as_slice() else {
        panic!("expected one indeterminate remainder leaf, found {result:#?}");
    };
    assert_eq!(remainder.depth, 0);
    assert_eq!(head(&remainder.pattern.term), "wrap");
    assert_eq!(
        remainder.trace.last().map(|entry| entry.kind),
        Some(TraceKind::Remainder)
    );
    assert_eq!(result.leaves.len(), 1, "{result:#?}");
    assert_eq!(result.status, ProofStatus::Indeterminate);
}

/// Refutes an obligation that applies `f` on a state whose constraints hold no negation, and
/// leaves it undecided on a state whose constraints hold one; every other validity question is
/// undecided. Incomplete, as a solver that more assumptions make time out is, but consistent:
/// an obligation it refutes on a state it never decides otherwise on a part of that state.
struct UndecidedUnderNegationSolver;

impl SmtSolver for UndecidedUnderNegationSolver {
    fn is_sat(
        &self,
        _predicates: &[Predicate],
        _substitution: &Substitution,
    ) -> Stoppable<Result<Satisfiability, SmtError>> {
        Ok(Ok(Satisfiability::Sat))
    }

    fn check_predicates(
        &self,
        known: &[Predicate],
        _substitution: &Substitution,
        checked: &[Predicate],
    ) -> Stoppable<Result<Validity, SmtError>> {
        let negated = known
            .iter()
            .any(|predicate| matches!(predicate, Predicate::Not(_)));
        Ok(Ok(if mentions_symbol(checked, "f") && !negated {
            Validity::Refuted
        } else {
            Validity::Unknown("scripted".into())
        }))
    }
}

/// The remainder of a step to which no lower rule applies has no successor; when the
/// destination check cannot decide whether it lies in the destination, it is neither proven nor
/// stuck: it is an `Indeterminate` leaf for the implication. The check on the state the step
/// took is decided (refuted), so the search steps it; one undecided there would end the branch
/// before the step (`an_undecided_destination_ends_the_branch_before_its_step`).
#[test]
fn an_undecided_destination_on_a_remainder_is_an_indeterminate_leaf() {
    let definition = definition(&rule("wrap-a", "wrap{}(a{}())", "b{}()", None));
    let y = Variable::new("Y", crate::term::Sort::simple("SortS"));
    let claim = claim(
        pattern(&definition, "wrap{}(X:SortS{})", Vec::new()),
        vec![
            pattern(&definition, "b{}()", Vec::new()),
            pattern(
                &definition,
                "wrap{}(Y:SortS{})",
                vec![Predicate::Equals(
                    term(&definition, "f{}(Y:SortS{})"),
                    term(&definition, "a{}()"),
                )],
            ),
        ],
        std::slice::from_ref(&y),
    );
    // The remainder is `wrap(X)` with `X` not `a`, a negated constraint.
    let result = prove(
        &definition,
        &claim,
        ProofOptions::default(),
        &UndecidedUnderNegationSolver,
    );
    let indeterminate = leaves_where(&result, |outcome| {
        outcome == &ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Implication)
    });
    let [remainder] = indeterminate.as_slice() else {
        panic!("expected one indeterminate remainder leaf, found {result:#?}");
    };
    assert_eq!(remainder.depth, 0);
    assert_eq!(head(&remainder.pattern.term), "wrap");
    assert_eq!(
        remainder.trace.last().map(|entry| entry.kind),
        Some(TraceKind::Remainder)
    );
    assert_eq!(result.status, ProofStatus::Indeterminate, "{result:#?}");
}

/// A state whose destination check is undecided ends its branch there, before its step: with
/// the obligation `f(X) = a` undecided on `wrap(X)` itself, the rule `wrap(a) => b()` is never
/// tried, and the one leaf is `wrap(X)`, indeterminate for the implication, with no remainder.
#[test]
fn an_undecided_destination_ends_the_branch_before_its_step() {
    let definition = definition(&rule("wrap-a", "wrap{}(a{}())", "b{}()", None));
    let y = Variable::new("Y", crate::term::Sort::simple("SortS"));
    let claim = claim(
        pattern(&definition, "wrap{}(X:SortS{})", Vec::new()),
        vec![
            pattern(&definition, "b{}()", Vec::new()),
            pattern(
                &definition,
                "wrap{}(Y:SortS{})",
                vec![Predicate::Equals(
                    term(&definition, "f{}(Y:SortS{})"),
                    term(&definition, "a{}()"),
                )],
            ),
        ],
        std::slice::from_ref(&y),
    );
    let solver = ScriptedSolver {
        undecided_symbol: "f",
        validity: Validity::Unknown("scripted".into()),
    };
    let result = prove(&definition, &claim, ProofOptions::default(), &solver);
    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one leaf, found {result:#?}");
    };
    assert_eq!(
        leaf.outcome,
        ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Implication),
        "{result:#?}"
    );
    assert_eq!(leaf.depth, 0);
    assert_eq!(head(&leaf.pattern.term), "wrap");
    assert!(
        leaf.trace
            .iter()
            .all(|entry| entry.kind != TraceKind::Remainder),
        "{result:#?}"
    );
    assert_eq!(result.status, ProofStatus::Indeterminate, "{result:#?}");
}

/// Leaves every validity question about `f` undecided and finds every other one contingent;
/// every satisfiability question is satisfiable.
struct UndecidedOnF;

impl SmtSolver for UndecidedOnF {
    fn is_sat(
        &self,
        _predicates: &[Predicate],
        _substitution: &Substitution,
    ) -> Stoppable<Result<Satisfiability, SmtError>> {
        Ok(Ok(Satisfiability::Sat))
    }

    fn check_predicates(
        &self,
        _known: &[Predicate],
        _substitution: &Substitution,
        checked: &[Predicate],
    ) -> Stoppable<Result<Validity, SmtError>> {
        Ok(Ok(if mentions_symbol(checked, "f") {
            Validity::Unknown("scripted".into())
        } else {
            Validity::Contingent
        }))
    }
}

/// `start(X)` steps to `wrap(X)` and, where `X` is not `a`, to `r(X)`. The destination check on
/// `wrap(X)` is undecided, an `Indeterminate` leaf; `r(X)` has no successor, and its constraint
/// `¬(X = a)` has no exact translation, so it is a `Failed` leaf that certifies nothing. Under
/// either order of the two rules, so of the two successors, the claim is `Failed`, the strongest
/// of its leaves at depth 1, the horizon, and reports the same leaves: stopping the search at
/// its first leaf that is not proven would give the status of whichever successor comes first.
#[test]
fn a_claim_with_an_indeterminate_and_a_failed_leaf_is_failed_under_either_rule_order() {
    let to_wrap = rule("to-wrap", "start{}(X:SortS{})", "wrap{}(X:SortS{})", None);
    let to_r = r#"
                symbol r{}(SortS{}) : SortS{} [constructor{}(), functional{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        start{}(X:SortS{}),
                        \not{SortS{}}(\equals{SortS{}, SortS{}}(X:SortS{}, a{}()))
                    ),
                    \and{SortS{}}(r{}(X:SortS{}), \top{SortS{}}())
                ) [label{}("to-r")]"#;
    let y = Variable::new("Y", crate::term::Sort::simple("SortS"));
    let solver = UndecidedOnF;
    let reports = [format!("{to_wrap}{to_r}"), format!("{to_r}{to_wrap}")].map(|rules| {
        let definition = definition(&rules);
        let claim = claim(
            pattern(&definition, "start{}(X:SortS{})", Vec::new()),
            vec![
                pattern(&definition, "done{}()", Vec::new()),
                pattern(
                    &definition,
                    "wrap{}(Y:SortS{})",
                    vec![Predicate::Equals(
                        term(&definition, "f{}(Y:SortS{})"),
                        term(&definition, "a{}()"),
                    )],
                ),
            ],
            std::slice::from_ref(&y),
        );
        let report = |max_counterexamples| {
            let result = prove(
                &definition,
                &claim,
                ProofOptions {
                    max_counterexamples,
                    ..ProofOptions::default()
                },
                &solver,
            );
            assert_eq!(result.explored_states, 3, "{rules}: {result:#?}");
            assert_eq!(result.unexplored_states, 0, "{rules}: {result:#?}");
            (
                result.status,
                result
                    .leaves
                    .iter()
                    .map(|leaf| (leaf.outcome.clone(), leaf.depth, head(&leaf.pattern.term)))
                    .collect::<Vec<_>>(),
            )
        };
        (report(1), report(2))
    });
    let failed = (ProofLeafOutcome::Stuck, 1, "r".to_owned());
    let indeterminate = (
        ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Implication),
        1,
        "wrap".to_owned(),
    );
    for (one, two) in &reports {
        assert_eq!(*one, (ProofStatus::Failed, vec![failed.clone()]));
        assert_eq!(
            *two,
            (
                ProofStatus::Failed,
                vec![failed.clone(), indeterminate.clone()]
            )
        );
    }
    assert_eq!(reports[0], reports[1]);
}
