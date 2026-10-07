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
        },
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
/// initial state the claim holds vacuously, so the leaf is proven; after a step the emptiness
/// comes from the path's own conditions, so the leaf is `Vacuous` and fails the claim, unless
/// vacuous proofs are allowed. Here the state's own constraints are satisfiable, and the
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
        assert_eq!(head(&leaf.pattern.term), "wrap", "{case}");
        if status == ProofStatus::Proven {
            assert!(vacuous_proof(&leaf.outcome), "{case}: {leaf:#?}");
        } else {
            assert_eq!(leaf.outcome, ProofLeafOutcome::Vacuous, "{case}");
        }
        assert_eq!(result.status, status, "{case}");
    }
}

/// The remainder of a step whose lower-priority rule could not be decided on it is a state
/// whose successors are unknown: the proof does not step it again, and it is an `Indeterminate`
/// leaf carrying the lower rule's reason, at the depth of the state it remains of. The branch
/// the higher-priority rule took is explored as usual.
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
    let proven = leaves_where(&result, |outcome| {
        matches!(outcome, ProofLeafOutcome::Proven(_))
    });
    assert_eq!(
        proven
            .iter()
            .map(|leaf| (head(&leaf.pattern.term), leaf.depth))
            .collect::<Vec<_>>(),
        [("b".to_owned(), 1)],
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
    assert_eq!(result.leaves.len(), 2, "{result:#?}");
    assert_eq!(result.status, ProofStatus::Indeterminate);
}

/// The remainder of a step to which no lower rule applies has no successor; when the
/// destination check cannot decide whether it lies in the destination, it is neither proven nor
/// stuck: it is an `Indeterminate` leaf for the implication.
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
    let solver = ScriptedSolver {
        undecided_symbol: "f",
        validity: Validity::Unknown("scripted".into()),
    };
    let result = prove(&definition, &claim, ProofOptions::default(), &solver);
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
