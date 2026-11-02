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

    /// Every satisfiability check is `Sat` and every validity check is `validity`; the validity
    /// checks are counted.
    struct Answering {
        validity: Validity,
        checks: Cell<usize>,
    }

    impl Answering {
        fn new(validity: Validity) -> Self {
            Self {
                validity,
                checks: Cell::new(0),
            }
        }

        /// `f`'s and `g`'s conditions are decided satisfied.
        fn valid() -> Self {
            Self::new(Validity::Valid)
        }
    }

    impl SmtSolver for Answering {
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
            Ok(Ok(self.validity.clone()))
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

    /// The consequent `source`, with no constraint.
    fn consequent(definition: &BackendDefinition, source: &str) -> Pattern {
        Pattern {
            term: term(definition, source),
            constraints: Vec::new(),
        }
    }

    /// The existential `Y:SortInt{}`.
    fn existential_y(definition: &BackendDefinition) -> BTreeSet<Variable> {
        BTreeSet::from([Variable {
            kind: crate::term::VariableKind::Element,
            sort: term(definition, "Y:SortInt{}").sort(),
            name: "Y".into(),
        }])
    }

    /// Run `action` as a proof runs its checks: inside a renaming-apart scope, the condition
    /// memo's scope and the record's, with the solver the memo counts undecided answers on.
    fn in_a_proof<T>(solver: &dyn SmtSolver, action: impl FnOnce(&dyn SmtSolver) -> T) -> T {
        let _apart = crate::rule::ApartScope::enter();
        let memo = simplify::condition_memo_scope(solver);
        let _record = normal_forms::scope();
        action(memo.solver())
    }

    /// What one preparation did: the prepared pattern, the counters' moves, and the equation
    /// conditions and attempts it left undecided.
    struct Prepared {
        pattern: Pattern,
        attempts: u64,
        recorded: u64,
        served: u64,
        refused_diagnostic: u64,
        undecided: u64,
        delta: measure::Snapshot,
    }

    fn prepare(
        definition: &BackendDefinition,
        antecedent: &Pattern,
        consequent: &Pattern,
        existentials: &BTreeSet<Variable>,
        solver: &dyn SmtSolver,
    ) -> Prepared {
        let before = measure::snapshot();
        let undecided = simplify::undecided_count();
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
        let undecided = simplify::undecided_count() - undecided;
        let delta = measure::snapshot().delta(&before);
        Prepared {
            pattern: destination.pattern().clone(),
            attempts: delta.get(Counter::SimplifyEquationAttempts),
            recorded: delta.get(Counter::SimplifyNormalFormsRecorded),
            served: delta.get(Counter::SimplifyNormalFormsServed),
            refused_diagnostic: delta.get(Counter::SimplifyNormalFormsRefusedDiagnostic),
            undecided,
            delta,
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
        let solver = Answering::valid();
        let consequent = consequent(&definition, "f{}(Y:SortInt{})");
        let existentials = existential_y(&definition);
        simplify::without_condition_memo(|| {
            in_a_proof(&solver, |counted| {
                let prepare = |bounds: &[&str]| {
                    prepare(
                        &definition,
                        &antecedent(&definition, bounds),
                        &consequent,
                        &existentials,
                        counted,
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
        });
    }

    /// Outside a proof's scope nothing is recorded or served: each check simplifies its
    /// destination, as an implication check outside a proof always does.
    #[test]
    fn a_destination_outside_a_proof_is_simplified_at_each_check() {
        let definition = definition();
        let solver = Answering::valid();
        let consequent = consequent(&definition, "f{}(X:SortInt{})");
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

    /// GAP K17: a simplification that emits a diagnostic is recorded only where no collector is
    /// open, where its diagnostic reaches no one, and is served only where none is open either:
    /// `g(3)`'s condition reads `missing(3)`, a hook without an evaluator, reported as an
    /// unsupported hook at each simplification (the scripted solver then decides the condition).
    /// Under a collector the check simplifies again, the collector receives the warning, and
    /// nothing is recorded.
    #[test]
    fn a_destination_whose_simplification_warns_is_served_only_where_no_collector_is_open() {
        let definition = definition();
        let solver = Answering::valid();
        let consequent = consequent(&definition, r#"g{}(\dv{SortInt{}}("3"))"#);
        in_a_proof(&solver, |counted| {
            let prepare = || {
                prepare(
                    &definition,
                    &antecedent(&definition, &["0"]),
                    &consequent,
                    &BTreeSet::new(),
                    counted,
                )
            };
            let counts = |prepared: &Prepared| {
                (
                    prepared.recorded,
                    prepared.served,
                    prepared.refused_diagnostic,
                )
            };
            assert_eq!(counts(&prepare()), (1, 0, 0));
            assert_eq!(counts(&prepare()), (0, 1, 0));
            let (collected, diagnostics) = crate::diagnostic::collect(prepare);
            assert!(!diagnostics.is_empty());
            assert_eq!(counts(&collected), (0, 0, 1));
            assert_eq!(counts(&prepare()), (0, 1, 0));
        });
    }

    /// GAP K17 review, finding 1: a simplification whose condition warns and is refuted, made
    /// with no collector open, is not served under a collector. With the condition memo on, the
    /// first check decides `g(3)`'s condition (warning, refuted) and is recorded; the second is
    /// served. Under a collector the record is not served, the memo decides the condition again
    /// (its verdict, reached with no collector open, holds no warning to replay), and the warning
    /// is emitted, so nothing is recorded (the refuted attempt's caller drops it, so the
    /// collector ends empty). Before, the first check was refused, the second recorded a
    /// simplification whose memo-served verdict replayed nothing, and the third was served it
    /// and failed the check of a served simplification.
    #[test]
    fn a_refuted_destination_recorded_with_no_collector_open_is_not_served_under_one() {
        let definition = definition();
        let solver = Answering::new(Validity::Refuted);
        let consequent = consequent(&definition, r#"g{}(\dv{SortInt{}}("3"))"#);
        in_a_proof(&solver, |counted| {
            let prepare = || {
                prepare(
                    &definition,
                    &antecedent(&definition, &["0"]),
                    &consequent,
                    &BTreeSet::new(),
                    counted,
                )
            };
            let first = prepare();
            assert_eq!((first.recorded, first.served), (1, 0));
            // Refuted: `g(3)` is left as it is.
            assert_eq!(first.pattern.term, consequent.term);
            let again = prepare();
            assert_eq!((again.recorded, again.served), (0, 1));
            let (collected, _) = crate::diagnostic::collect(prepare);
            assert_eq!(
                (
                    collected.recorded,
                    collected.served,
                    collected.refused_diagnostic
                ),
                (0, 0, 1)
            );
            assert_eq!(collected.pattern, first.pattern);
        });
    }

    /// GAP K17 relaxation (i): a destination whose equation's `requires` stays undecided on
    /// decided answers (the solver finds it and its negation satisfiable, as on `#bufStrict`) is
    /// recorded, with no collector open, and served under equal constraints: the condition is
    /// decided once, and the serve counts as many undecided decisions and gives the pattern a
    /// new simplification gives.
    #[test]
    fn a_destination_left_undecided_on_decided_answers_is_served_with_its_undecided_count() {
        let definition = definition();
        let solver = Answering::new(Validity::Contingent);
        let consequent = consequent(&definition, "f{}(Y:SortInt{})");
        let existentials = existential_y(&definition);
        simplify::without_condition_memo(|| {
            let check = || {
                in_a_proof(&solver, |counted| {
                    let prepare = || {
                        prepare(
                            &definition,
                            &antecedent(&definition, &["0"]),
                            &consequent,
                            &existentials,
                            counted,
                        )
                    };
                    (prepare(), prepare())
                })
            };
            let (first, again) = check();
            assert!(first.undecided > 0 && first.attempts > 0);
            assert_eq!((first.recorded, first.served), (1, 0));
            // Undecided: `f` was not applied.
            assert!(matches!(
                first.pattern.term.kind(),
                crate::term::TermKind::Application { .. }
            ));
            let checks = solver.checks.get();
            assert_eq!((again.recorded, again.served, again.attempts), (0, 1, 0));
            assert_eq!(again.undecided, first.undecided);
            assert_eq!(again.pattern, first.pattern);
            let (fresh, fresh_again) = normal_forms::without_normal_forms(check);
            assert!(solver.checks.get() > checks);
            for fresh in [fresh, fresh_again] {
                assert_eq!((fresh.recorded, fresh.served), (0, 0));
                assert_eq!(fresh.undecided, first.undecided);
                assert_eq!(fresh.pattern, first.pattern);
            }
        });
    }

    /// GAP K17 review, finding 3: a serve moves the renaming-apart counter on as far as the
    /// simplification it reuses did, so the names minted after it are those minted after a new
    /// simplification. `f(Z)` shares `Z` with `f`'s equation, which is renamed apart before it is
    /// applied; its result `Z` holds no minted name, so it is recorded and served.
    #[test]
    fn a_served_destination_moves_the_renaming_apart_counter_as_a_new_one_does() {
        let definition = definition();
        let solver = Answering::valid();
        // `Eq#Z` is the name the equation's `Z` has once internalized.
        let consequent = {
            let written = consequent(&definition, "f{}(Z:SortInt{})");
            let z = |name: &str| Variable {
                kind: crate::term::VariableKind::Element,
                sort: written.term.sort(),
                name: name.into(),
            };
            let renaming = Substitution::from([(z("Z"), Term::variable(z("Eq#Z")))]);
            super::super::rename_as_freshened(&written, &renaming)
        };
        let run = || {
            in_a_proof(&solver, |counted| {
                let prepare = || {
                    prepare(
                        &definition,
                        &antecedent(&definition, &["0"]),
                        &consequent,
                        &BTreeSet::new(),
                        counted,
                    )
                };
                let first = prepare();
                let minted = crate::rule::apart_counter();
                let again = prepare();
                (
                    (first.recorded, again.served),
                    minted,
                    crate::rule::apart_counter(),
                    again.pattern,
                )
            })
        };
        let (served, minted, counter, pattern) = run();
        assert_eq!(served, (1, 1));
        assert!(minted > 0, "f's equation is renamed apart from f(Z)");
        assert!(matches!(
            pattern.term.kind(),
            crate::term::TermKind::Variable(variable) if &*variable.name == "Eq#Z"
        ));
        let (fresh, fresh_minted, fresh_counter, fresh_pattern) =
            normal_forms::without_normal_forms(run);
        assert_eq!(fresh, (0, 0));
        assert_eq!((minted, counter), (fresh_minted, fresh_counter));
        assert_eq!(counter, 2 * minted);
        assert_eq!(pattern, fresh_pattern);
    }

    /// GAP K17 review, finding 3: a simplification recorded with no path-fact record open is not
    /// served where one is, since "noted no fact" says nothing where nothing was open to note
    /// one; the check inside simplifies again and records under a record, which is then served
    /// there.
    #[test]
    fn a_destination_recorded_with_no_fact_record_open_is_not_served_inside_one() {
        let definition = definition();
        let solver = Answering::valid();
        let consequent = consequent(&definition, "f{}(Y:SortInt{})");
        let existentials = existential_y(&definition);
        in_a_proof(&solver, |counted| {
            let prepare = || {
                prepare(
                    &definition,
                    &antecedent(&definition, &["0"]),
                    &consequent,
                    &existentials,
                    counted,
                )
            };
            let first = prepare();
            assert_eq!((first.recorded, first.served), (1, 0));
            let (inside, _) = crate::path_facts::run(prepare);
            assert_eq!((inside.recorded, inside.served), (1, 0));
            let (again, _) = crate::path_facts::run(prepare);
            assert_eq!((again.recorded, again.served), (0, 1));
            assert_eq!(again.pattern, first.pattern);
        });
    }

    /// GAP K17 review, finding 3: work isolated from the run (`coverage::isolated`) is neither
    /// served from the record nor records into it, since what it emits and notes goes nowhere.
    /// With the condition memo off, the solver's checks show whether a preparation simplified.
    #[test]
    fn isolated_work_neither_is_served_nor_records() {
        let definition = definition();
        let solver = Answering::valid();
        let consequent = consequent(&definition, "f{}(Y:SortInt{})");
        let existentials = existential_y(&definition);
        simplify::without_condition_memo(|| {
            in_a_proof(&solver, |counted| {
                let prepare = |bounds: &[&str]| {
                    prepare(
                        &definition,
                        &antecedent(&definition, bounds),
                        &consequent,
                        &existentials,
                        counted,
                    )
                };
                let isolated = |bounds: &[&str]| {
                    let checks = solver.checks.get();
                    let (prepared, _) = crate::coverage::isolated(1 << 20, || prepare(bounds));
                    (prepared.pattern, solver.checks.get() > checks)
                };
                let first = prepare(&["0"]);
                assert_eq!(first.recorded, 1);
                let (pattern, simplified) = isolated(&["0"]);
                assert!(simplified, "recorded outside, simplified again inside");
                assert_eq!(pattern, first.pattern);
                let (_, simplified) = isolated(&["0", "1"]);
                assert!(simplified);
                let after = prepare(&["0", "1"]);
                assert_eq!(
                    (after.recorded, after.served),
                    (1, 0),
                    "nothing was recorded inside"
                );
            });
        });
    }

    /// GAP K17 review, finding 3: inside a run with a console, an open coverage collection, or
    /// an open lineage's records of `Unspecified` evaluations, the thread holds something the
    /// key does not, and each check is refused before the lookup, counted by its reason, and
    /// simplifies. The reason is counted once per check at each site: for the destination, and
    /// for its term `f(Y')`, a non-ground subterm the term simplifier routes through the record
    /// too (K17 part b), which is refused for the same reason and counted at the subterm site.
    #[test]
    fn a_destination_is_neither_recorded_nor_served_inside_what_its_key_does_not_hold() {
        let definition = definition();
        let solver = Answering::valid();
        let consequent = consequent(&definition, "f{}(Y:SortInt{})");
        let existentials = existential_y(&definition);
        in_a_proof(&solver, |counted| {
            let prepare = || {
                prepare(
                    &definition,
                    &antecedent(&definition, &["0"]),
                    &consequent,
                    &existentials,
                    counted,
                )
            };
            let refused = |(reason, subterm): (Counter, Counter), inside: &dyn Fn() -> Prepared| {
                for _ in 0..2 {
                    let prepared = inside();
                    assert_eq!(
                        (
                            prepared.recorded,
                            prepared.served,
                            prepared
                                .delta
                                .get(Counter::SimplifyNormalFormsSubtermRecorded),
                            prepared
                                .delta
                                .get(Counter::SimplifyNormalFormsSubtermServed),
                            prepared.delta.get(reason),
                            prepared.delta.get(subterm)
                        ),
                        (0, 0, 0, 0, 1, 1),
                        "{reason:?}"
                    );
                    assert!(prepared.attempts > 0);
                }
            };
            refused(
                (
                    Counter::SimplifyNormalFormsRefusedConsole,
                    Counter::SimplifyNormalFormsSubtermRefusedConsole,
                ),
                &|| {
                    let _console = crate::evaluation::EvaluationScope::enter_run(
                        crate::evaluation::EvaluationMode::Proof,
                        true,
                    );
                    prepare()
                },
            );
            refused(
                (
                    Counter::SimplifyNormalFormsRefusedCoverage,
                    Counter::SimplifyNormalFormsSubtermRefusedCoverage,
                ),
                &|| crate::coverage::collect(prepare).0,
            );
            refused(
                (
                    Counter::SimplifyNormalFormsRefusedUnspecified,
                    Counter::SimplifyNormalFormsSubtermRefusedUnspecified,
                ),
                &|| simplify::with_unspecified_values_open(prepare),
            );
        });
    }
}
