//! Fixture helpers shared by more than one module of the `backend` target.

use std::{cell::RefCell, collections::VecDeque};

use k_rust_backend::{
    cancellation::CancellationToken,
    definition::BackendDefinition,
    rule::Predicate,
    smt::{Satisfiability, SmtError, SmtSolver, Validity},
    substitution::Substitution,
    term::Term,
};
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

/// One ordered query made to [`ScriptedSolver`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ScriptedQuery {
    IsSat {
        predicates: Vec<Predicate>,
        substitution: Substitution,
    },
    CheckPredicates {
        known: Vec<Predicate>,
        substitution: Substitution,
        checked: Vec<Predicate>,
    },
}

/// An ordered SMT test double whose answers and complete query transcript are explicit fixtures.
#[derive(Debug)]
pub struct ScriptedSolver {
    pub answers: RefCell<VecDeque<Result<Satisfiability, SmtError>>>,
    pub validity: RefCell<VecDeque<Result<Validity, SmtError>>>,
    pub transcript: RefCell<Vec<ScriptedQuery>>,
    /// Zero-based query index and token to cancel after recording that query.
    pub cancel_at: Option<(usize, CancellationToken)>,
}

impl ScriptedSolver {
    pub fn new(
        answers: impl IntoIterator<Item = Result<Satisfiability, SmtError>>,
        validity: impl IntoIterator<Item = Result<Validity, SmtError>>,
    ) -> Self {
        Self {
            answers: RefCell::new(answers.into_iter().collect()),
            validity: RefCell::new(validity.into_iter().collect()),
            transcript: RefCell::default(),
            cancel_at: None,
        }
    }

    pub fn cancelling_at(mut self, query_index: usize, token: CancellationToken) -> Self {
        self.cancel_at = Some((query_index, token));
        self
    }

    fn record(&self, query: ScriptedQuery) {
        let mut transcript = self.transcript.borrow_mut();
        let query_index = transcript.len();
        transcript.push(query);
        if let Some((cancel_at, token)) = &self.cancel_at
            && query_index == *cancel_at
        {
            token.cancel();
        }
    }
}

impl SmtSolver for ScriptedSolver {
    fn is_sat(
        &self,
        predicates: &[Predicate],
        substitution: &Substitution,
    ) -> Result<Satisfiability, SmtError> {
        self.record(ScriptedQuery::IsSat {
            predicates: predicates.to_vec(),
            substitution: substitution.clone(),
        });
        self.answers.borrow_mut().pop_front().unwrap_or_else(|| {
            panic!(
                "ScriptedSolver exhausted satisfiability answers after transcript {:#?}",
                self.transcript.borrow()
            )
        })
    }

    fn check_predicates(
        &self,
        known: &[Predicate],
        substitution: &Substitution,
        checked: &[Predicate],
    ) -> Result<Validity, SmtError> {
        self.record(ScriptedQuery::CheckPredicates {
            known: known.to_vec(),
            substitution: substitution.clone(),
            checked: checked.to_vec(),
        });
        self.validity.borrow_mut().pop_front().unwrap_or_else(|| {
            panic!(
                "ScriptedSolver exhausted validity answers after transcript {:#?}",
                self.transcript.borrow()
            )
        })
    }
}

/// A single-constructor cell sort collected in a hooked set, with rewrite rules that add either
/// a distinct, unresolved cell value or an exact duplicate.
pub fn ground_cell_set_definition() -> BackendDefinition {
    let syntax = parse_definition(include_str!("../fixtures/ground-cell-set.kore"))
        .expect("ground cell set fixture should parse");
    BackendDefinition::internalize(&syntax, "GROUND-CELL-SET")
        .expect("ground cell set fixture should internalize")
}

/// A strict-list overload and `isKResult` equation pair used to distinguish concrete lowering
/// from symbolic sort membership.
pub fn ground_overload_definition() -> BackendDefinition {
    let syntax = parse_definition(include_str!("../fixtures/ground-overload.kore"))
        .expect("ground overload fixture should parse");
    BackendDefinition::internalize(&syntax, "GROUND-OVERLOAD")
        .expect("ground overload fixture should internalize")
}

/// Parse a KORE pattern and internalize it as a term of `definition`.
pub fn internal_term(definition: &BackendDefinition, source: &str) -> Term {
    let syntax = parse_pattern(source).expect("term should parse");
    definition
        .internalize_term(&syntax, &[])
        .expect("term should internalize")
}
