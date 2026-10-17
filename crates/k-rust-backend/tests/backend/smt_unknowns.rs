//! The undecided solver answers an execution counts (`ExecutionResult::smt_unknowns`): one per
//! `Unknown` the solver delivered to a decision of the run, none for a decided answer.

use std::cell::Cell;

use k_rust_backend::{
    definition::BackendDefinition,
    rewrite::{ExecutionOptions, Pattern, execute_with_solver},
    rule::Predicate,
    smt::{Satisfiability, SmtError, SmtSolver, Validity},
    stop::Stoppable,
    substitution::Substitution,
};
use k_rust_kore::kore::parser::parse_definition;

use crate::support::internal_term;

/// `state(X)` steps to `pos()` where `X > 0` and to `neg()` where `X < 0`: from a symbolic `X`
/// each rule's condition goes to the solver.
fn definition() -> BackendDefinition {
    let rule = |label: &str, hook: &str, right: &str| {
        format!(
            r#"
            axiom{{}} \rewrites{{SortS{{}}}}(
                \and{{SortS{{}}}}(
                    state{{}}(X:SortInt{{}}),
                    \equals{{SortBool{{}}, SortS{{}}}}(
                        {hook}{{}}(X:SortInt{{}}, \dv{{SortInt{{}}}}("0")),
                        \dv{{SortBool{{}}}}("true")
                    )
                ),
                \and{{SortS{{}}}}({right}{{}}(), \top{{SortS{{}}}}())
            ) [label{{}}("{label}")]"#
        )
    };
    let source = format!(
        r#"[]
        module MAIN
            hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
            hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
            sort SortS{{}} []
            hooked-symbol gtInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.gt"), smt-hook{{}}(">")]
            hooked-symbol ltInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.lt"), smt-hook{{}}("<")]
            symbol state{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol pos{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
            symbol neg{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
            {positive}
            {negative}
        endmodule []"#,
        positive = rule("positive", "gtInt", "pos"),
        negative = rule("negative", "ltInt", "neg"),
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

/// A solver that gives every satisfiability and validity query one fixed answer and counts the
/// undecided answers it gave.
struct Fixed {
    satisfiability: Satisfiability,
    validity: Validity,
    undecided: Cell<usize>,
}

impl Fixed {
    fn new(satisfiability: Satisfiability, validity: Validity) -> Self {
        Self {
            satisfiability,
            validity,
            undecided: Cell::new(0),
        }
    }
}

impl SmtSolver for Fixed {
    fn is_sat(
        &self,
        _predicates: &[Predicate],
        _substitution: &Substitution,
    ) -> Stoppable<Result<Satisfiability, SmtError>> {
        if matches!(self.satisfiability, Satisfiability::Unknown(_)) {
            self.undecided.set(self.undecided.get() + 1);
        }
        Ok(Ok(self.satisfiability.clone()))
    }

    fn check_predicates(
        &self,
        _known: &[Predicate],
        _substitution: &Substitution,
        _checked: &[Predicate],
    ) -> Stoppable<Result<Validity, SmtError>> {
        if matches!(self.validity, Validity::Unknown(_)) {
            self.undecided.set(self.undecided.get() + 1);
        }
        Ok(Ok(self.validity.clone()))
    }
}

fn run(solver: &Fixed) -> usize {
    let definition = definition();
    let initial = Pattern {
        term: internal_term(&definition, "state{}(X:SortInt{})"),
        constraints: Vec::new(),
    };
    let result = execute_with_solver(
        &definition,
        initial,
        ExecutionOptions {
            max_depth: 2,
            ..ExecutionOptions::default()
        },
        solver,
    );
    result.smt_unknowns
}

/// A solver that leaves every query undecided gives a positive count, exactly the undecided
/// answers it delivered; one that decides every query, satisfiable or not, gives zero.
#[test]
fn an_execution_counts_each_undecided_solver_answer_it_received() {
    let unknown = Fixed::new(
        Satisfiability::Unknown("timeout".into()),
        Validity::Unknown("timeout".into()),
    );
    let count = run(&unknown);
    assert!(count > 0);
    assert_eq!(count, unknown.undecided.get());

    for decided in [
        Fixed::new(Satisfiability::Sat, Validity::Contingent),
        Fixed::new(Satisfiability::Unsat, Validity::Refuted),
        Fixed::new(Satisfiability::Sat, Validity::Valid),
    ] {
        assert_eq!(run(&decided), 0);
        assert_eq!(decided.undecided.get(), 0);
    }
}
