//! The destination of one implication check, in the form the match against it assumes.
//!
//! The match compares both sides of the implication in the definition's normal form under the
//! antecedent's constraints: a destination term with an unevaluated function application leaves
//! an obligation the definition's equations could have discharged. The fields are private to
//! this module, so no other code, including the rest of `implication`, can build a
//! [`Destination`] except through [`Destination::prepare`] (E0451); the match and the discharge
//! take a `&Destination`, so every destination they compare against, on the single- and the
//! multi-destination path alike, has been simplified.

use std::collections::BTreeSet;

use crate::{
    definition::BackendDefinition,
    rewrite::Pattern,
    simplify::SimplificationOptions,
    smt::SmtSolver,
    stop::{Layered, Stoppable},
    term::Variable,
};

use super::{ImplicationError, freshen_existentials, rename_as_freshened, simplify_consequent};

/// One consequent of a check: the pattern the check simplifies and matches (`checked`), and the
/// pattern its caller wrote (`written`), which denote the same set on every valuation. They are
/// the same pattern ([`Consequent::as_written`]) except for a proof's destination, whose ground
/// subterms the proof has simplified once (`proof::prepare_destinations`); the written form then
/// decides what the check does where the prepared one would decide otherwise (whether the
/// destination is kept unsimplified, and what a failed simplification keeps), so that each check
/// takes the steps it would take on the written form.
#[derive(Clone, Copy)]
pub(crate) struct Consequent<'a> {
    pub(crate) checked: &'a Pattern,
    pub(crate) written: &'a Pattern,
}

impl<'a> Consequent<'a> {
    /// A consequent checked as written.
    pub(crate) fn as_written(pattern: &'a Pattern) -> Self {
        Self {
            checked: pattern,
            written: pattern,
        }
    }
}

/// The destination of one implication check in the form the match against it assumes: its
/// existentials freshened apart from the antecedent, then simplified with the definition's
/// equations under the antecedent's constraints. A term that already carries the evaluated mark
/// is kept, and a simplification failure keeps the term as written (`simplify_consequent`); the
/// type records that simplification was attempted.
pub(super) struct Destination {
    pattern: Pattern,
    existentials: BTreeSet<Variable>,
}

impl Destination {
    /// Freshen `consequent`'s `existentials` apart from `antecedent` (`freshen_existentials`),
    /// then simplify its checked form under the antecedent's constraints (`simplify_consequent`).
    ///
    /// Inside a proof the simplification is looked up in, and recorded to, the proof's record of
    /// normal forms (`simplify::normal_forms`), by the checked form's node as the caller holds
    /// it, the renaming the freshening chose, and the antecedent's constraints. The renaming
    /// depends on the antecedent's variables, its term's included, so it is in the key itself:
    /// two states with equal constraints may freshen differently.
    ///
    /// A stop is returned on the outer layer: it belongs to the operation that runs the check
    /// and says nothing about the destination.
    pub(super) fn prepare(
        definition: &BackendDefinition,
        antecedent: &Pattern,
        consequent: Consequent<'_>,
        existentials: &BTreeSet<Variable>,
        options: SimplificationOptions,
        solver: &dyn SmtSolver,
    ) -> Stoppable<Result<Self, ImplicationError>> {
        // The renaming is chosen for the written form, as a check of it alone chooses it, and the
        // prepared form, which has the same variables, is renamed alike.
        let (written, existentials, renaming) =
            freshen_existentials(antecedent, consequent.written, existentials);
        let checked = if std::ptr::eq(consequent.checked, consequent.written) {
            written.clone()
        } else {
            rename_as_freshened(consequent.checked, &renaming)
        };
        simplify_consequent(
            definition,
            antecedent,
            checked,
            written,
            &consequent.checked.term,
            &renaming,
            options,
            solver,
        )
        .map(|pattern| Self {
            pattern,
            existentials,
        })
        .layered()
    }

    /// The prepared destination pattern.
    pub(super) fn pattern(&self) -> &Pattern {
        &self.pattern
    }

    /// The destination's existentials, freshened apart from the antecedent.
    pub(super) fn existentials(&self) -> &BTreeSet<Variable> {
        &self.existentials
    }
}

/// The destination's simplification is served from the proof's record of normal forms
/// (`simplify::normal_forms`) under equal constraints, and only there.
#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use k_rust_kore::{
        kore::parser::{parse_definition, parse_pattern},
        measure::{self, Counter},
    };

    use super::*;
    use crate::{
        rule::Predicate,
        simplify::{self, normal_forms},
        smt::{Satisfiability, SmtError, Validity},
        substitution::Substitution,
        term::Term,
    };

    /// `f(X) = X` only under `X >Int 0`, which the solver decides; `g(X) = X` only under
    /// `missing(X)`, a partial hook without an evaluator, which a simplification leaves
    /// unevaluated and reports as an unsupported hook (a warning diagnostic).
    fn definition() -> BackendDefinition {
        let equation = |symbol: &str, requires: &str| {
            format!(
                r#"axiom{{R}} \implies{{R}}(
                    \and{{R}}(
                        \equals{{SortBool{{}}, R}}({requires}, \dv{{SortBool{{}}}}("true")),
                        \and{{R}}(\in{{SortInt{{}}, R}}(X0:SortInt{{}}, Z:SortInt{{}}), \top{{R}}())
                    ),
                    \equals{{SortInt{{}}, R}}(
                        {symbol}{{}}(X0:SortInt{{}}),
                        \and{{SortInt{{}}}}(Z:SortInt{{}}, \top{{SortInt{{}}}}())
                    )
                ) [label{{}}("{symbol}-guarded")]"#
            )
        };
        let source = format!(
            r#"[]
            module MAIN
                hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
                hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
                symbol f{{}}(SortInt{{}}) : SortInt{{}} [function{{}}()]
                symbol g{{}}(SortInt{{}}) : SortInt{{}} [function{{}}()]
                hooked-symbol gtInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                    [function{{}}(), total{{}}(), hook{{}}("INT.gt"), smt-hook{{}}(">")]
                hooked-symbol missing{{}}(SortInt{{}}) : SortBool{{}}
                    [function{{}}(), hook{{}}("TEST.missing")]
                {}
                {}
            endmodule []"#,
            equation("f", r#"gtInt{}(X0:SortInt{}, \dv{SortInt{}}("0"))"#),
            equation("g", "missing{}(X0:SortInt{})"),
        );
        let syntax = parse_definition(&source).expect("the definition parses");
        BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
    }

    fn term(definition: &BackendDefinition, source: &str) -> Term {
        definition
            .internalize_term(&parse_pattern(source).expect("the term parses"), &[])
            .expect("the term internalizes")
    }

    /// Every validity check is `Valid`, so `f`'s condition is decided satisfied; counted.
    #[derive(Default)]
    struct Valid {
        checks: Cell<usize>,
    }

    impl SmtSolver for Valid {
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
            _checked: &[Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            self.checks.set(self.checks.get() + 1);
            Ok(Ok(Validity::Valid))
        }
    }

    /// The state `X` under `X >Int bound` for each bound, in order.
    fn antecedent(definition: &BackendDefinition, bounds: &[&str]) -> Pattern {
        Pattern {
            term: term(definition, "X:SortInt{}"),
            constraints: bounds
                .iter()
                .map(|bound| {
                    Predicate::Term(term(
                        definition,
                        &format!(r#"gtInt{{}}(X:SortInt{{}}, \dv{{SortInt{{}}}}("{bound}"))"#),
                    ))
                })
                .collect(),
        }
    }

    /// What one preparation did: the prepared pattern, and the counters' moves.
    struct Prepared {
        pattern: Pattern,
        attempts: u64,
        recorded: u64,
        served: u64,
        refused_diagnostic: u64,
    }

    fn prepare(
        definition: &BackendDefinition,
        antecedent: &Pattern,
        consequent: &Pattern,
        existentials: &BTreeSet<Variable>,
        solver: &dyn SmtSolver,
    ) -> Prepared {
        let before = measure::snapshot();
        let destination = Destination::prepare(
            definition,
            antecedent,
            Consequent::as_written(consequent),
            existentials,
            SimplificationOptions::default(),
            solver,
        )
        .map_err(crate::stop::Stop::into_cause)
        .expect("no stop is armed")
        .unwrap_or_else(|error| panic!("the destination is prepared: {error}"));
        let delta = measure::snapshot().delta(&before);
        Prepared {
            pattern: destination.pattern().clone(),
            attempts: delta.get(Counter::SimplifyEquationAttempts),
            recorded: delta.get(Counter::SimplifyNormalFormsRecorded),
            served: delta.get(Counter::SimplifyNormalFormsServed),
            refused_diagnostic: delta.get(Counter::SimplifyNormalFormsRefusedDiagnostic),
        }
    }

    /// GAP K17: inside a proof's scope, with the condition memo off, a destination checked
    /// again under equal constraints is served the simplification the first check recorded:
    /// `f(Y)` (`Y` an existential, freshened alike at each check) decides `f`'s condition once.
    /// Under stronger constraints it is simplified again, since a stronger path condition may
    /// decide more, and recorded under its own key. The served pattern is the one the first
    /// check prepared, and the served simplification equals a new one (`check-normal-forms`,
    /// which every test build runs; its own work is not counted).
    #[test]
    fn a_destination_checked_again_under_equal_constraints_decides_its_conditions_once() {
        let definition = definition();
        let solver = Valid::default();
        let consequent = Pattern {
            term: term(&definition, "f{}(Y:SortInt{})"),
            constraints: Vec::new(),
        };
        let existentials = BTreeSet::from([Variable {
            kind: crate::term::VariableKind::Element,
            sort: consequent.term.sort(),
            name: "Y".into(),
        }]);
        simplify::without_condition_memo(|| {
            let memo = simplify::condition_memo_scope(&solver);
            let _record = normal_forms::scope();
            let prepare = |bounds: &[&str]| {
                prepare(
                    &definition,
                    &antecedent(&definition, bounds),
                    &consequent,
                    &existentials,
                    memo.solver(),
                )
            };
            let first = prepare(&["0"]);
            assert!(first.attempts > 0 && solver.checks.get() > 0);
            assert_eq!((first.recorded, first.served), (1, 0));
            // `f` was applied: the prepared term is the freshened existential.
            assert_ne!(first.pattern.term, consequent.term);
            let again = prepare(&["0"]);
            assert_eq!(again.attempts, 0);
            assert_eq!((again.recorded, again.served), (0, 1));
            assert_eq!(again.pattern, first.pattern);
            let stronger = prepare(&["0", "1"]);
            assert!(stronger.attempts > 0);
            assert_eq!((stronger.recorded, stronger.served), (1, 0));
        });
    }

    /// Outside a proof's scope nothing is recorded or served: each check simplifies its
    /// destination, as an implication check outside a proof always does.
    #[test]
    fn a_destination_outside_a_proof_is_simplified_at_each_check() {
        let definition = definition();
        let solver = Valid::default();
        let consequent = Pattern {
            term: term(&definition, "f{}(X:SortInt{})"),
            constraints: Vec::new(),
        };
        simplify::without_condition_memo(|| {
            for _ in 0..2 {
                let prepared = prepare(
                    &definition,
                    &antecedent(&definition, &["0"]),
                    &consequent,
                    &BTreeSet::new(),
                    &solver,
                );
                assert!(prepared.attempts > 0);
                assert_eq!((prepared.recorded, prepared.served), (0, 0));
            }
        });
    }

    /// GAP K17: a simplification that emits a diagnostic is never recorded, so never served,
    /// whether or not a collector is open to receive it: `g(3)`'s condition reads `missing(3)`,
    /// a hook without an evaluator, reported as an unsupported hook at each check (the scripted
    /// solver then decides the condition, so the warning is the only reason not to record).
    #[test]
    fn a_destination_whose_simplification_warns_is_never_served() {
        let definition = definition();
        let solver = Valid::default();
        let consequent = Pattern {
            term: term(&definition, r#"g{}(\dv{SortInt{}}("3"))"#),
            constraints: Vec::new(),
        };
        let memo = simplify::condition_memo_scope(&solver);
        let _record = normal_forms::scope();
        for collecting in [false, true, false] {
            let prepare = || {
                prepare(
                    &definition,
                    &antecedent(&definition, &["0"]),
                    &consequent,
                    &BTreeSet::new(),
                    memo.solver(),
                )
            };
            let prepared = if collecting {
                let (prepared, diagnostics) = crate::diagnostic::collect(prepare);
                assert!(!diagnostics.is_empty());
                prepared
            } else {
                prepare()
            };
            assert_eq!(
                (
                    prepared.recorded,
                    prepared.served,
                    prepared.refused_diagnostic
                ),
                (0, 0, 1)
            );
        }
    }
}
