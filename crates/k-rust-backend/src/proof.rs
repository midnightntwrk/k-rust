//! Breadth-first reachability proof execution.

use std::{
    collections::{BTreeSet, VecDeque},
    error::Error,
    fmt,
};

use crate::{
    claim::{ReachabilityClaim, ReachabilityMode},
    definition::BackendDefinition,
    implication::{
        ImplicationCondition, ImplicationError, ImplicationStatus,
        check_disjunctive_implication_with_existentials,
    },
    matching::{MatchMode, MatchResult, match_terms},
    rewrite::{
        IndeterminateReason, Pattern, RewriteResult, TraceEntry, TraceKind, Truth,
        predicates_truth, rewrite_step_with_solver, substitute_predicates,
    },
    simplify::{
        SimplificationError, SimplificationOptions, simplify_predicates_with_solver,
        simplify_with_solver,
    },
    smt::{SmtError, SmtSolver, Validity},
    substitution::{Substitution, substitute},
    term::{Term, Variable},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProofOptions {
    pub max_depth: u64,
    pub min_depth: u64,
    pub max_simplification_iterations: usize,
    pub allow_vacuous: bool,
    pub search_order: ProofSearchOrder,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ProofSearchOrder {
    #[default]
    BreadthFirst,
    DepthFirst,
}

impl Default for ProofOptions {
    fn default() -> Self {
        Self {
            max_depth: 1_000,
            min_depth: 0,
            max_simplification_iterations: 100,
            allow_vacuous: false,
            search_order: ProofSearchOrder::BreadthFirst,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProofStatus {
    Proven,
    Disproved,
    Indeterminate,
    DepthBound,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofIndeterminateReason {
    Implication,
    Rewrite(IndeterminateReason),
    Simplification(SimplificationError),
    Claim {
        claim_id: String,
        reason: ClaimIndeterminateReason,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ClaimIndeterminateReason {
    Match {
        substitution: Substitution,
        remainder: Vec<(Term, Term)>,
    },
    Requires(Vec<crate::rule::Predicate>),
    Smt(SmtError),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofLeafOutcome {
    Proven(ImplicationCondition),
    Trusted,
    Stuck,
    Trivial,
    Vacuous,
    DepthBound,
    Indeterminate(ProofIndeterminateReason),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofLeaf {
    pub pattern: Pattern,
    pub depth: u64,
    pub trace: Vec<TraceEntry>,
    pub outcome: ProofLeafOutcome,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofResult {
    pub status: ProofStatus,
    pub leaves: Vec<ProofLeaf>,
    pub explored_states: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofError {
    Implication(ImplicationError),
}

impl fmt::Display for ProofError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl Error for ProofError {}

pub fn prove_claim(
    definition: &BackendDefinition,
    claim: &ReachabilityClaim,
    options: ProofOptions,
    solver: &dyn SmtSolver,
) -> Result<ProofResult, ProofError> {
    if claim.attributes.trusted {
        return Ok(ProofResult {
            status: ProofStatus::Proven,
            leaves: vec![ProofLeaf {
                pattern: claim.lhs.clone(),
                depth: 0,
                trace: Vec::new(),
                outcome: ProofLeafOutcome::Trusted,
            }],
            explored_states: 0,
        });
    }

    let mut pending = VecDeque::from([ProofState {
        pattern: claim.lhs.clone(),
        depth: 0,
        trace: Vec::new(),
    }]);
    let mut leaves = Vec::new();
    let mut fresh_counter = 0;
    let mut explored_states = 0;
    while let Some(mut state) = match options.search_order {
        ProofSearchOrder::BreadthFirst => pending.pop_front(),
        ProofSearchOrder::DepthFirst => pending.pop_back(),
    } {
        explored_states += 1;
        let simplified = match simplify_with_solver(
            definition,
            &state.pattern.term,
            &state.pattern.constraints,
            SimplificationOptions {
                max_iterations: options.max_simplification_iterations,
            },
            solver,
        ) {
            Ok(simplified) => simplified,
            Err(error) => {
                leaves.push(state.leaf(ProofLeafOutcome::Indeterminate(
                    ProofIndeterminateReason::Simplification(error),
                )));
                continue;
            }
        };
        state.pattern.term = simplified.term;
        extend_unique(&mut state.pattern.constraints, simplified.constraints);
        state.trace.extend(
            simplified
                .applied_rules
                .into_iter()
                .map(|unique_id| TraceEntry {
                    depth: state.depth,
                    kind: TraceKind::Simplification,
                    label: None,
                    unique_id,
                }),
        );

        if predicates_truth(&state.pattern.constraints) == Truth::False {
            let outcome = if options.allow_vacuous {
                ProofLeafOutcome::Proven(ImplicationCondition {
                    predicates: vec![crate::rule::Predicate::False],
                    substitution: Default::default(),
                })
            } else {
                ProofLeafOutcome::Vacuous
            };
            let proven = matches!(outcome, ProofLeafOutcome::Proven(_));
            leaves.push(state.leaf(outcome));
            if proven && claim.mode == ReachabilityMode::OnePath {
                return Ok(finish(claim.mode, leaves, explored_states));
            }
            continue;
        }

        let mut implication_indeterminate = false;
        if state.depth >= options.min_depth {
            let implication = check_disjunctive_implication_with_existentials(
                definition,
                &state.pattern,
                &claim.rhs,
                &claim.existentials,
                SimplificationOptions {
                    max_iterations: options.max_simplification_iterations,
                },
                solver,
            )
            .map_err(ProofError::Implication)?;
            match implication.status {
                ImplicationStatus::Valid => {
                    let condition = implication
                        .condition
                        .expect("a valid implication always has a condition");
                    leaves.push(state.leaf(ProofLeafOutcome::Proven(condition)));
                    if claim.mode == ReachabilityMode::OnePath {
                        return Ok(finish(claim.mode, leaves, explored_states));
                    }
                    continue;
                }
                ImplicationStatus::Invalid => {}
                ImplicationStatus::Indeterminate => implication_indeterminate = true,
            }
        }

        if state.depth >= options.max_depth {
            leaves.push(state.leaf(ProofLeafOutcome::DepthBound));
            continue;
        }

        if state.depth > 0 {
            let mut claim_transition = None;
            for candidate in &definition.reachability_claims {
                if candidate.mode != claim.mode {
                    continue;
                }
                match apply_claim(
                    definition,
                    candidate,
                    &state.pattern,
                    options,
                    solver,
                    &mut fresh_counter,
                ) {
                    ClaimApplication::NotApplicable => {}
                    transition => {
                        claim_transition = Some((candidate, transition));
                        break;
                    }
                }
            }
            if let Some((candidate, transition)) = claim_transition {
                match transition {
                    ClaimApplication::Applied(patterns) => {
                        pending.extend(patterns.into_iter().map(|pattern| {
                            state.clone().claimed(
                                pattern,
                                candidate.attributes.label.clone(),
                                candidate.attributes.unique_id.clone(),
                            )
                        }));
                    }
                    ClaimApplication::Indeterminate(reason) => {
                        leaves.push(state.leaf(ProofLeafOutcome::Indeterminate(
                            ProofIndeterminateReason::Claim {
                                claim_id: candidate.attributes.unique_id.clone(),
                                reason,
                            },
                        )));
                    }
                    ClaimApplication::NotApplicable => unreachable!(),
                }
                continue;
            }
        }

        match rewrite_step_with_solver(definition, &state.pattern, &mut fresh_counter, solver) {
            RewriteResult::Finished(applied) => {
                pending.push_back(state.rewritten(applied));
            }
            RewriteResult::Branch { branches, .. } => {
                pending.extend(
                    branches
                        .into_iter()
                        .map(|applied| state.clone().rewritten(applied)),
                );
            }
            RewriteResult::Stuck(_) => {
                let outcome = if implication_indeterminate {
                    ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Implication)
                } else {
                    ProofLeafOutcome::Stuck
                };
                leaves.push(state.leaf(outcome));
            }
            RewriteResult::Trivial(_) => leaves.push(state.leaf(ProofLeafOutcome::Trivial)),
            RewriteResult::Indeterminate { reason, .. } => {
                leaves.push(state.leaf(ProofLeafOutcome::Indeterminate(
                    ProofIndeterminateReason::Rewrite(reason),
                )));
            }
        }
    }

    Ok(finish(claim.mode, leaves, explored_states))
}

#[derive(Clone)]
struct ProofState {
    pattern: Pattern,
    depth: u64,
    trace: Vec<TraceEntry>,
}

impl ProofState {
    fn leaf(self, outcome: ProofLeafOutcome) -> ProofLeaf {
        ProofLeaf {
            pattern: self.pattern,
            depth: self.depth,
            trace: self.trace,
            outcome,
        }
    }

    fn rewritten(mut self, applied: crate::rewrite::AppliedRule) -> Self {
        self.depth += 1;
        self.trace.push(TraceEntry {
            depth: self.depth,
            kind: TraceKind::Rewrite,
            label: applied.label,
            unique_id: applied.unique_id,
        });
        self.pattern = applied.pattern;
        self
    }

    fn claimed(mut self, pattern: Pattern, label: Option<String>, unique_id: String) -> Self {
        self.depth += 1;
        self.trace.push(TraceEntry {
            depth: self.depth,
            kind: TraceKind::Claim,
            label,
            unique_id,
        });
        self.pattern = pattern;
        self
    }
}

enum ClaimApplication {
    NotApplicable,
    Applied(Vec<Pattern>),
    Indeterminate(ClaimIndeterminateReason),
}

fn apply_claim(
    definition: &BackendDefinition,
    claim: &ReachabilityClaim,
    subject: &Pattern,
    options: ProofOptions,
    solver: &dyn SmtSolver,
    fresh_counter: &mut u64,
) -> ClaimApplication {
    let claim = freshen_claim(claim, subject, fresh_counter);
    let substitution = match match_terms(
        MatchMode::Rewrite,
        &definition.sort_graph,
        &claim.lhs.term,
        &subject.term,
    ) {
        MatchResult::Success(substitution) => substitution,
        MatchResult::Failed(_) => return ClaimApplication::NotApplicable,
        MatchResult::Indeterminate {
            substitution,
            remainder,
        } => {
            return ClaimApplication::Indeterminate(ClaimIndeterminateReason::Match {
                substitution,
                remainder,
            });
        }
    };
    let requires = substitute_predicates(&claim.lhs.constraints, &substitution);
    let requires = match simplify_predicates_with_solver(
        definition,
        &requires,
        &subject.constraints,
        SimplificationOptions {
            max_iterations: options.max_simplification_iterations,
        },
        solver,
    ) {
        Ok(requires) => requires,
        Err(_) => {
            return ClaimApplication::Indeterminate(ClaimIndeterminateReason::Requires(requires));
        }
    };
    match predicates_truth(&requires) {
        Truth::True => {}
        Truth::False => return ClaimApplication::NotApplicable,
        Truth::Unknown => {
            match solver.check_predicates(&subject.constraints, &Substitution::new(), &requires) {
                Ok(Validity::Valid) => {}
                Ok(Validity::Invalid | Validity::InconsistentGroundTruth) => {
                    return ClaimApplication::NotApplicable;
                }
                Ok(Validity::Indeterminate | Validity::Unknown(_)) => {
                    return ClaimApplication::Indeterminate(ClaimIndeterminateReason::Requires(
                        requires,
                    ));
                }
                Err(error) => {
                    return ClaimApplication::Indeterminate(ClaimIndeterminateReason::Smt(error));
                }
            }
        }
    }

    ClaimApplication::Applied(
        claim
            .rhs
            .iter()
            .map(|rhs| {
                let mut constraints = subject.constraints.clone();
                extend_unique(
                    &mut constraints,
                    substitute_predicates(&rhs.constraints, &substitution),
                );
                Pattern {
                    term: substitute(&rhs.term, &substitution),
                    constraints,
                }
            })
            .collect(),
    )
}

fn freshen_claim(
    claim: &ReachabilityClaim,
    subject: &Pattern,
    fresh_counter: &mut u64,
) -> ReachabilityClaim {
    let mut names = subject
        .term
        .attributes()
        .variables
        .iter()
        .map(|variable| variable.name.clone())
        .collect::<BTreeSet<_>>();
    for predicate in &subject.constraints {
        names.extend(
            predicate
                .free_variables()
                .into_iter()
                .map(|variable| variable.name),
        );
    }
    let variables = claim
        .lhs
        .term
        .attributes()
        .variables
        .iter()
        .cloned()
        .chain(
            claim
                .lhs
                .constraints
                .iter()
                .flat_map(crate::rule::Predicate::free_variables),
        )
        .chain(claim.rhs.iter().flat_map(|rhs| {
            rhs.term.attributes().variables.iter().cloned().chain(
                rhs.constraints
                    .iter()
                    .flat_map(crate::rule::Predicate::free_variables),
            )
        }))
        .chain(claim.existentials.iter().cloned())
        .collect::<BTreeSet<_>>();
    let mut renaming = Substitution::new();
    for variable in variables {
        let name = loop {
            let name = format!("{}!claim{}", variable.name, *fresh_counter);
            *fresh_counter += 1;
            if names.insert(name.as_str().into()) {
                break name;
            }
        };
        renaming.insert(
            variable.clone(),
            Term::variable(Variable::new(name, variable.sort)),
        );
    }
    let rename_pattern = |pattern: &Pattern| Pattern {
        term: substitute(&pattern.term, &renaming),
        constraints: substitute_predicates(&pattern.constraints, &renaming),
    };
    ReachabilityClaim {
        lhs: rename_pattern(&claim.lhs),
        rhs: claim.rhs.iter().map(rename_pattern).collect(),
        existentials: claim
            .existentials
            .iter()
            .map(|variable| {
                let renamed = renaming
                    .get(variable)
                    .expect("every claim variable is refreshed");
                let crate::term::TermKind::Variable(variable) = renamed.kind() else {
                    unreachable!("claim variables are renamed to variables")
                };
                variable.clone()
            })
            .collect(),
        mode: claim.mode,
        attributes: claim.attributes.clone(),
    }
}

fn finish(mode: ReachabilityMode, leaves: Vec<ProofLeaf>, explored_states: u64) -> ProofResult {
    let any_proven = leaves.iter().any(is_proven);
    let any_disproved = leaves.iter().any(|leaf| {
        matches!(
            leaf.outcome,
            ProofLeafOutcome::Stuck | ProofLeafOutcome::Trivial | ProofLeafOutcome::Vacuous
        )
    });
    let any_indeterminate = leaves
        .iter()
        .any(|leaf| matches!(leaf.outcome, ProofLeafOutcome::Indeterminate(_)));
    let any_depth_bound = leaves
        .iter()
        .any(|leaf| matches!(leaf.outcome, ProofLeafOutcome::DepthBound));
    let status = match mode {
        ReachabilityMode::OnePath if any_proven => ProofStatus::Proven,
        ReachabilityMode::AllPath if any_disproved => ProofStatus::Disproved,
        _ if any_indeterminate => ProofStatus::Indeterminate,
        _ if any_depth_bound => ProofStatus::DepthBound,
        ReachabilityMode::AllPath if leaves.iter().all(is_proven) => ProofStatus::Proven,
        ReachabilityMode::OnePath => ProofStatus::Disproved,
        ReachabilityMode::AllPath => ProofStatus::Indeterminate,
    };
    ProofResult {
        status,
        leaves,
        explored_states,
    }
}

fn is_proven(leaf: &ProofLeaf) -> bool {
    matches!(
        leaf.outcome,
        ProofLeafOutcome::Proven(_) | ProofLeafOutcome::Trusted
    )
}

fn extend_unique(left: &mut Vec<crate::rule::Predicate>, right: Vec<crate::rule::Predicate>) {
    for predicate in right {
        if !left.contains(&predicate) {
            left.push(predicate);
        }
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::parse_definition;

    use super::*;
    use crate::smt::NoSolver;

    fn definition(rules: &str, claims: &str) -> BackendDefinition {
        let source = format!(
            r#"[]
            module MAIN
                sort SortS{{}} []
                symbol a{{}}() : SortS{{}} [constructor{{}}()]
                symbol b{{}}() : SortS{{}} [constructor{{}}()]
                symbol c{{}}() : SortS{{}} [constructor{{}}()]
                {rules}
                {claims}
            endmodule []"#
        );
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    #[cfg(feature = "z3")]
    #[test]
    fn proves_a_destination_covered_by_complementary_branches() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                claim{} \implies{SortInt{}}(
                    \and{SortInt{}}(X:SortInt{}, \top{SortInt{}}()),
                    weakExistsFinally{SortInt{}}(
                        \or{SortInt{}}(
                            \and{SortInt{}}(
                                X:SortInt{},
                                \equals{SortInt{}, SortInt{}}(
                                    X:SortInt{},
                                    \dv{SortInt{}}("0")
                                )
                            ),
                            \and{SortInt{}}(
                                X:SortInt{},
                                \not{SortInt{}}(
                                    \equals{SortInt{}, SortInt{}}(
                                        X:SortInt{},
                                        \dv{SortInt{}}("0")
                                    )
                                )
                            )
                        )
                    )
                ) [label{}("complementary")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");

        let result = prove_claim(
            &definition,
            &definition.reachability_claims[0],
            ProofOptions::default(),
            &solver,
        )
        .expect("claim should execute");

        assert_eq!(result.status, ProofStatus::Proven);
        assert_eq!(result.explored_states, 1);
        assert!(matches!(
            result.leaves.as_slice(),
            [ProofLeaf {
                outcome: ProofLeafOutcome::Proven(_),
                ..
            }]
        ));
    }

    const A_TO_B: &str = r#"
        axiom{} \rewrites{SortS{}}(
            \and{SortS{}}(a{}(), \top{SortS{}}()),
            \and{SortS{}}(b{}(), \top{SortS{}}())
        ) [label{}("a-to-b")]
    "#;

    const A_TO_B_AND_C: &str = r#"
        axiom{} \rewrites{SortS{}}(
            \and{SortS{}}(a{}(), \top{SortS{}}()),
            \and{SortS{}}(b{}(), \top{SortS{}}())
        ) [label{}("a-to-b")]
        axiom{} \rewrites{SortS{}}(
            \and{SortS{}}(a{}(), \top{SortS{}}()),
            \and{SortS{}}(c{}(), \top{SortS{}}())
        ) [label{}("a-to-c")]
    "#;

    const A_TO_A: &str = r#"
        axiom{} \rewrites{SortS{}}(
            \and{SortS{}}(a{}(), \top{SortS{}}()),
            \and{SortS{}}(a{}(), \top{SortS{}}())
        ) [label{}("a-loop")]
    "#;

    fn modal_claim(mode: ReachabilityMode, left: &str, right: &str, trusted: bool) -> String {
        let modality = match mode {
            ReachabilityMode::OnePath => "weakExistsFinally",
            ReachabilityMode::AllPath => "weakAlwaysFinally",
        };
        let trusted = if trusted {
            "trusted{}()"
        } else {
            "label{}(\"claim\")"
        };
        format!(
            r#"claim{{}} \implies{{SortS{{}}}}(
                \and{{SortS{{}}}}(\top{{SortS{{}}}}(), {left}{{}}()),
                {modality}{{SortS{{}}}}(
                    \and{{SortS{{}}}}({right}{{}}(), \top{{SortS{{}}}}())
                )
            ) [{trusted}]"#
        )
    }

    #[test]
    fn proves_direct_and_rewritten_reachability() {
        let claims = [
            modal_claim(ReachabilityMode::OnePath, "a", "a", false),
            modal_claim(ReachabilityMode::OnePath, "a", "b", false),
        ]
        .join("\n");
        let definition = definition(A_TO_B, &claims);

        let direct = prove_claim(
            &definition,
            &definition.reachability_claims[0],
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();
        let rewritten = prove_claim(
            &definition,
            &definition.reachability_claims[1],
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(direct.status, ProofStatus::Proven);
        assert_eq!(direct.leaves[0].depth, 0);
        assert_eq!(rewritten.status, ProofStatus::Proven);
        assert_eq!(rewritten.leaves[0].depth, 1);
    }

    #[test]
    fn reports_stuck_and_depth_bounded_claims_separately() {
        let claims = modal_claim(ReachabilityMode::AllPath, "a", "b", false);
        let stuck_definition = definition("", &claims);
        let bounded_definition = definition(A_TO_B, &claims);

        let stuck = prove_claim(
            &stuck_definition,
            &stuck_definition.reachability_claims[0],
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();
        let bounded = prove_claim(
            &bounded_definition,
            &bounded_definition.reachability_claims[0],
            ProofOptions {
                max_depth: 0,
                ..ProofOptions::default()
            },
            &NoSolver,
        )
        .unwrap();

        assert_eq!(stuck.status, ProofStatus::Disproved);
        assert_eq!(bounded.status, ProofStatus::DepthBound);
    }

    #[test]
    fn accepts_trusted_claims_without_exploration() {
        let claims = modal_claim(ReachabilityMode::AllPath, "a", "b", true);
        let definition = definition("", &claims);

        let result = prove_claim(
            &definition,
            &definition.reachability_claims[0],
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(result.status, ProofStatus::Proven);
        assert_eq!(result.explored_states, 0);
        assert!(matches!(
            result.leaves[0].outcome,
            ProofLeafOutcome::Trusted
        ));
    }

    #[test]
    fn distinguishes_existential_and_universal_rewrite_paths() {
        let claims = [
            modal_claim(ReachabilityMode::OnePath, "a", "b", false),
            modal_claim(ReachabilityMode::AllPath, "a", "b", false),
        ]
        .join("\n");
        let definition = definition(A_TO_B_AND_C, &claims);

        let one_path = prove_claim(
            &definition,
            &definition.reachability_claims[0],
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();
        let all_path = prove_claim(
            &definition,
            &definition.reachability_claims[1],
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(one_path.status, ProofStatus::Proven);
        assert_eq!(all_path.status, ProofStatus::Disproved);
        assert_eq!(all_path.leaves.len(), 2);
    }

    #[test]
    fn supports_breadth_first_and_depth_first_proof_search() {
        let claims = modal_claim(ReachabilityMode::OnePath, "a", "c", false);
        let definition = definition(A_TO_B_AND_C, &claims);
        let claim = &definition.reachability_claims[0];

        let breadth_first = prove_claim(
            &definition,
            claim,
            ProofOptions {
                search_order: ProofSearchOrder::BreadthFirst,
                ..ProofOptions::default()
            },
            &NoSolver,
        )
        .unwrap();
        let depth_first = prove_claim(
            &definition,
            claim,
            ProofOptions {
                search_order: ProofSearchOrder::DepthFirst,
                ..ProofOptions::default()
            },
            &NoSolver,
        )
        .unwrap();

        assert_eq!(breadth_first.status, ProofStatus::Proven);
        assert_eq!(depth_first.status, ProofStatus::Proven);
        assert_eq!(breadth_first.explored_states, 3);
        assert_eq!(depth_first.explored_states, 2);
    }

    #[test]
    fn applies_guarded_claim_circularities_only_after_a_semantic_step() {
        let claims = modal_claim(ReachabilityMode::OnePath, "a", "b", false);
        let definition = definition(A_TO_A, &claims);

        let result = prove_claim(
            &definition,
            &definition.reachability_claims[0],
            ProofOptions {
                max_depth: 3,
                ..ProofOptions::default()
            },
            &NoSolver,
        )
        .unwrap();

        assert_eq!(result.status, ProofStatus::Proven);
        assert_eq!(result.leaves[0].depth, 2);
        assert_eq!(
            result.leaves[0]
                .trace
                .iter()
                .map(|entry| entry.kind)
                .collect::<Vec<_>>(),
            vec![TraceKind::Rewrite, TraceKind::Claim]
        );
    }
}
