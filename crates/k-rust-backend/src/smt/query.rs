//! A query posed to the solver, with the exactness its translation recorded.

#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::BTreeMap;

use super::{Exactness, SExpr, TranslationState};
use crate::term::Term;

/// A query posed to the solver. The fields are private to this module, so the solver reads the
/// constants that stand for the query's variables only through [`Self::model_mappings`], which
/// withholds them when a model of the query need not be a K valuation.
pub(crate) struct TranslatedQuery {
    base: String,
    checked: SExpr,
    mappings: BTreeMap<Term, String>,
    exactness: Exactness,
    foreign_text: bool,
}

impl TranslatedQuery {
    /// Takes the finished translation, so the query's exactness and mappings are read from the
    /// state that recorded them; no caller states an exactness.
    pub(super) fn new(base: String, checked: SExpr, translation: TranslationState) -> Self {
        Self {
            base,
            checked,
            exactness: translation.exactness(),
            foreign_text: translation.foreign_text,
            mappings: translation.mappings,
        }
    }

    /// The script that declares the query's constants and asserts its known facts.
    pub(crate) fn base(&self) -> &str {
        &self.base
    }

    /// The conjunction of the checked predicates.
    pub(crate) fn checked(&self) -> &SExpr {
        &self.checked
    }

    pub(crate) fn exactness(&self) -> Exactness {
        self.exactness
    }

    /// Whether the translation copied text it did not write itself into the query
    /// (`TranslationState::write_foreign_text`).
    pub(crate) fn foreign_text(&self) -> bool {
        self.foreign_text
    }

    /// The constants that stand for the query's variables, only when a model of the query is a
    /// K valuation: when the translation is exact.
    pub(crate) fn model_mappings(&self) -> Option<&BTreeMap<Term, String>> {
        match self.exactness() {
            Exactness::Exact => Some(&self.mappings),
            Exactness::Approximate => None,
        }
    }
}

#[cfg(test)]
#[allow(clippy::wildcard_enum_match_arm)]
mod tests {
    use std::sync::Arc;

    use super::super::SmtPrelude;
    use super::*;
    use crate::{
        rule::Predicate,
        substitution::Substitution,
        term::{FunctionType, Sort, Symbol, SymbolAttributes, SymbolType, Variable},
    };

    fn prelude() -> SmtPrelude {
        SmtPrelude {
            declarations: Vec::new(),
            smtlib_names: std::collections::BTreeSet::new(),
            user_script: false,
            congruence: None,
            source: None,
        }
    }

    fn int() -> Sort {
        Sort::simple("SortInt")
    }

    fn integer(value: &str) -> Term {
        Term::raw_domain_value(int(), value)
    }

    fn variable(name: &str, sort: Sort) -> Term {
        Term::variable(Variable::new(name, sort))
    }

    fn opaque(argument: Term) -> Term {
        Term::application(
            Arc::new(Symbol {
                name: "opaque".into(),
                sort_variables: Vec::new(),
                argument_sorts: vec![int()],
                result_sort: int(),
                attributes: {
                    let mut attributes =
                        SymbolAttributes::constructor().with_declared_function(true);
                    attributes.symbol_type = SymbolType::Function(FunctionType::Total);
                    attributes
                },
            }),
            Vec::new(),
            vec![argument],
        )
    }

    fn query(known: &[Predicate]) -> TranslatedQuery {
        prelude()
            .query(known, &Substitution::new(), &[], false)
            .unwrap()
            .expect("the query should translate")
    }

    #[test]
    fn an_int_query_with_a_free_int_variable_has_model_mappings() {
        let x = variable("X", int());
        let query = query(&[Predicate::Equals(x.clone(), integer("1"))]);

        assert_eq!(query.exactness(), Exactness::Exact);
        let mappings = query
            .model_mappings()
            .expect("an exact query has model mappings");
        assert_eq!(mappings.get(&x), Some(&"SMT-1".to_owned()));
    }

    #[test]
    fn a_query_with_an_abstracted_term_has_no_model_mappings() {
        let x = variable("X", int());
        let query = query(&[Predicate::Equals(opaque(x), integer("1"))]);

        assert_eq!(query.exactness(), Exactness::Approximate);
        assert_eq!(query.model_mappings(), None);
    }

    #[test]
    fn a_query_with_a_free_variable_of_an_uninterpreted_sort_has_no_model_mappings() {
        let n = variable("N", Sort::simple("SortNat"));
        let x = variable("X", int());
        let query = query(&[
            Predicate::Equals(n.clone(), n),
            Predicate::Equals(x, integer("1")),
        ]);

        assert_eq!(query.exactness(), Exactness::Approximate);
        assert_eq!(query.model_mappings(), None);
    }

    #[test]
    fn a_query_whose_filter_drops_a_known_conjunct_is_approximate() {
        let x = variable("X", int());
        let y = variable("Y", int());
        let checked = [Predicate::Equals(x.clone(), integer("1"))];
        let unrelated = [Predicate::Equals(y, integer("2"))];

        let filtered = prelude()
            .query(&unrelated, &Substitution::new(), &checked, true)
            .unwrap()
            .expect("the query should translate");
        assert_eq!(filtered.exactness(), Exactness::Approximate);
        assert!(!filtered.base().contains("(assert"));

        let related = [Predicate::Equals(x, integer("2"))];
        let kept = prelude()
            .query(&related, &Substitution::new(), &checked, true)
            .unwrap()
            .expect("the query should translate");
        assert_eq!(kept.exactness(), Exactness::Exact);
        assert_eq!(kept.checked().to_string(), "(and (= SMT-1 1))");
    }

    fn congruence_definition() -> crate::definition::BackendDefinition {
        let syntax = k_rust_kore::kore::parser::parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol f{}(SortInt{}) : SortInt{} [function{}(), total{}()]
                symbol g{}(SortInt{}) : SortInt{} [function{}(), total{}()]
                symbol h{}(SortInt{}) : SortInt{} [function{}(), total{}()]
                symbol pair{}(SortInt{}, SortInt{}) : SortInt{} [function{}(), total{}()]
                symbol partial{}(SortInt{}) : SortInt{} [function{}()]
                symbol restricted{}(SortInt{}) : SortInt{} [function{}()]
                symbol nonzero{}(SortInt{}) : SortInt{} [function{}()]
                symbol onDefined{}(SortInt{}) : SortInt{} [function{}()]
                symbol domainEffect{}(SortInt{}) : SortInt{} [function{}()]
                symbol booleanPartial{}(SortInt{}) : SortBool{} [function{}()]
                symbol effectFlag{}(SortInt{}) : SortBool{} [function{}(),total{}(),impure{}()]
                symbol effect{}(SortInt{}) : SortInt{} [function{}(), total{}(), impure{}()]
                symbol wrapped{}(SortInt{}) : SortInt{} [function{}(), total{}()]
                symbol poly{S}(S) : S [function{}(), total{}()]
                symbol named{}(SortInt{}) : SortInt{} [function{}(), total{}(), smtlib{}("NAMED")]
                hooked-symbol plus{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
                hooked-symbol ne{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.ne"), smt-hook{}("distinct")]
                axiom{R} \implies{R}(\top{R}(), \equals{R,R}(
                    \ceil{SortInt{},R}(restricted{}(\dv{SortInt{}}("0"))), \bottom{R}())) []
                axiom{R} \implies{R}(\top{R}(), \equals{R,R}(
                    \ceil{SortInt{},R}(onDefined{}(X:SortInt{})), \top{R}())) []
                axiom{R} \implies{R}(\top{R}(), \equals{R,R}(
                    \ceil{SortInt{},R}(domainEffect{}(X:SortInt{})),
                    \and{R}(\equals{SortBool{},R}(effectFlag{}(X:SortInt{}),
                        \dv{SortBool{}}("true")),\top{R}()))) []
                axiom{R} \implies{R}(\top{R}(), \equals{R,R}(
                    \ceil{SortInt{},R}(nonzero{}(X:SortInt{})),
                    \and{R}(\equals{SortBool{},R}(
                        ne{}(X:SortInt{},\dv{SortInt{}}("0")),\dv{SortBool{}}("true")),\top{R}()))) []
                axiom{R} \implies{R}(\top{R}(), \equals{SortInt{}, R}(
                    wrapped{}(X:SortInt{}), \and{SortInt{}}(effect{}(X:SortInt{}), \top{SortInt{}}()))) [simplification{}(), label{}("effect-wrapper")]
            endmodule []"#,
        )
        .unwrap();
        crate::definition::BackendDefinition::internalize(&syntax, "MAIN").unwrap()
    }

    fn parsed_term(definition: &crate::definition::BackendDefinition, source: &str) -> Term {
        definition
            .internalize_term(
                &k_rust_kore::kore::parser::parse_pattern(source).unwrap(),
                &[],
            )
            .unwrap()
    }

    #[test]
    fn automatic_congruence_retains_ground_head_dependencies_and_withholds_models() {
        let definition = congruence_definition();
        let x = Variable::new("X", int());
        let known = [Predicate::Forall(
            x,
            Arc::new(Predicate::Equals(
                parsed_term(&definition, "f{}(X:SortInt{})"),
                integer("0"),
            )),
        )];
        let checked = [Predicate::Equals(
            parsed_term(&definition, r#"f{}(\dv{SortInt{}}("7"))"#),
            integer("0"),
        )];
        let query = SmtPrelude::from_definition(&definition)
            .unwrap()
            .query(&known, &Substitution::new(), &checked, true)
            .unwrap()
            .unwrap();
        assert!(
            query.base().contains("(assert"),
            "the quantified fact was filtered out"
        );
        assert_eq!(query.exactness(), Exactness::Approximate);
        assert!(query.model_mappings().is_none());
        let solver = super::super::Z3Solver::new(&definition).unwrap();
        use super::super::{SmtSolver, Validity};
        assert_eq!(
            solver.check_predicates(&known, &Substitution::new(), &checked),
            Ok(Ok(Validity::Valid))
        );
    }

    #[test]
    fn congruence_does_not_assert_injectivity_or_an_effectful_function_rank() {
        use super::super::{Satisfiability, SmtSolver};
        let definition = congruence_definition();
        let solver = super::super::Z3Solver::new(&definition).unwrap();
        let f0 = parsed_term(&definition, r#"f{}(\dv{SortInt{}}("0"))"#);
        let f1 = parsed_term(&definition, r#"f{}(\dv{SortInt{}}("1"))"#);
        let equal = Predicate::Equals(f0, f1);
        assert_eq!(
            solver.is_sat(std::slice::from_ref(&equal), &Substitution::new()),
            Ok(Ok(Satisfiability::Sat))
        );
        assert_eq!(
            solver.is_sat(&[Predicate::Not(Arc::new(equal))], &Substitution::new()),
            Ok(Ok(Satisfiability::Sat))
        );
        let prelude = SmtPrelude::from_definition(&definition).unwrap();
        for head in ["effect", "wrapped", "domainEffect"] {
            let predicates = [Predicate::Equals(
                parsed_term(&definition, &format!("{head}{{}}(X:SortInt{{}})")),
                integer("0"),
            )];
            let query = prelude
                .query(&predicates, &Substitution::new(), &[], false)
                .unwrap()
                .unwrap();
            assert!(!query.base().contains("(declare-fun SMT-"), "{head}");
            assert!(query.model_mappings().is_none());
        }
    }

    #[test]
    fn partial_values_and_domains_share_argument_congruence_without_asserting_totality() {
        use super::super::{SmtSolver, Validity};
        let definition = congruence_definition();
        let solver = super::super::Z3Solver::new(&definition).unwrap();
        let left = parsed_term(
            &definition,
            r#"partial{}(plus{}(X:SortInt{}, \dv{SortInt{}}("1")))"#,
        );
        let right = parsed_term(
            &definition,
            r#"partial{}(plus{}(\dv{SortInt{}}("1"), X:SortInt{}))"#,
        );
        let known = [Predicate::Ceil(left.clone())];
        let checked = [
            Predicate::Ceil(right.clone()),
            Predicate::Equals(left.clone(), right.clone()),
        ];
        assert_eq!(
            solver.check_predicates(&known, &Substitution::new(), &checked),
            Ok(Ok(Validity::Valid))
        );
        assert_eq!(
            solver.check_predicates(
                &[Predicate::Not(Arc::new(Predicate::Ceil(left)))],
                &Substitution::new(),
                &[Predicate::Not(Arc::new(Predicate::Ceil(right.clone())))],
            ),
            Ok(Ok(Validity::Valid))
        );
        assert_eq!(
            solver.check_predicates(&[], &Substitution::new(), &[Predicate::Ceil(right)]),
            Ok(Ok(Validity::Contingent))
        );
        let query = SmtPrelude::from_definition(&definition)
            .unwrap()
            .query(&known, &Substitution::new(), &checked, true)
            .unwrap()
            .unwrap();
        assert_eq!(query.exactness(), Exactness::Approximate);
        assert!(query.model_mappings().is_none());
    }

    #[test]
    fn partial_domains_keep_discarded_arguments_and_undefined_values_unrelated() {
        use super::super::{SmtSolver, Validity};
        let definition = congruence_definition();
        let solver = super::super::Z3Solver::new(&definition).unwrap();
        let left = parsed_term(&definition, r#"partial{}(\dv{SortInt{}}("0"))"#);
        let right = parsed_term(&definition, r#"partial{}(\dv{SortInt{}}("1"))"#);
        let outer = parsed_term(&definition, r#"g{}(partial{}(\dv{SortInt{}}("0")))"#);
        let known = [
            Predicate::Not(Arc::new(Predicate::Ceil(left.clone()))),
            Predicate::Not(Arc::new(Predicate::Ceil(right.clone()))),
        ];
        assert_eq!(
            solver.check_predicates(
                &known,
                &Substitution::new(),
                &[Predicate::Not(Arc::new(Predicate::Ceil(outer)))],
            ),
            Ok(Ok(Validity::Valid))
        );
        // An equality atom must retain its domains: two undefined applications do not
        // supply either a defined common result or equality of their totalized values.
        assert_eq!(
            solver.check_predicates(
                &known,
                &Substitution::new(),
                &[
                    Predicate::Ceil(left.clone()),
                    Predicate::Ceil(right.clone()),
                    Predicate::Equals(left, right),
                ],
            ),
            Ok(Ok(Validity::Refuted))
        );
    }

    #[test]
    fn decided_source_domains_remain_congruent_with_unresolved_instances() {
        use super::super::{SmtSolver, Validity};
        let definition = congruence_definition();
        let solver = super::super::Z3Solver::new(&definition).unwrap();
        let zero = parsed_term(&definition, r#"restricted{}(\dv{SortInt{}}("0"))"#);
        let symbolic = parsed_term(&definition, "restricted{}(X:SortInt{})");
        let known = [
            Predicate::Equals(parsed_term(&definition, "X:SortInt{}"), integer("0")),
            Predicate::Not(Arc::new(Predicate::Ceil(zero))),
        ];
        assert_eq!(
            solver.check_predicates(
                &known,
                &Substitution::new(),
                &[Predicate::Not(Arc::new(Predicate::Ceil(symbolic)))],
            ),
            Ok(Ok(Validity::Valid))
        );
    }

    #[test]
    fn source_domain_facts_and_lets_stay_under_their_own_quantifiers() {
        use super::super::{Satisfiability, SmtSolver, Validity};
        let definition = congruence_definition();
        let solver = super::super::Z3Solver::new(&definition).unwrap();
        let x = Variable::new("X", int());
        let partial = parsed_term(&definition, "nonzero{}(X:SortInt{})");
        let some_defined = Predicate::Exists(x.clone(), Arc::new(Predicate::Ceil(partial.clone())));
        let some_undefined = Predicate::Exists(
            x.clone(),
            Arc::new(Predicate::Not(Arc::new(Predicate::Ceil(partial)))),
        );
        assert_eq!(
            solver.check_predicates(&[], &Substitution::new(), &[some_defined, some_undefined]),
            Ok(Ok(Validity::Valid))
        );
        let undefined_zero = Predicate::Not(Arc::new(Predicate::Ceil(parsed_term(
            &definition,
            r#"nonzero{}(\dv{SortInt{}}("0"))"#,
        ))));
        let bound = Predicate::Forall(
            x,
            Arc::new(Predicate::Iff(
                Arc::new(Predicate::Ceil(parsed_term(
                    &definition,
                    "nonzero{}(X:SortInt{})",
                ))),
                Arc::new(Predicate::Term(parsed_term(
                    &definition,
                    r#"ne{}(X:SortInt{},\dv{SortInt{}}("0"))"#,
                ))),
            )),
        );
        assert_eq!(
            solver.is_sat(&[bound, undefined_zero], &Substitution::new()),
            Ok(Ok(Satisfiability::Sat))
        );
    }

    #[test]
    fn shared_partial_domain_dags_have_bounded_construction_and_text() {
        let definition = congruence_definition();
        let prelude = SmtPrelude::from_definition(&definition).unwrap();
        let size = |depth| {
            let mut value = parsed_term(&definition, "X:SortInt{}");
            for _ in 0..depth {
                let partial =
                    Term::application(definition.symbols()["partial"].clone(), vec![], vec![value]);
                value = Term::application(
                    definition.symbols()["pair"].clone(),
                    vec![],
                    vec![partial.clone(), partial],
                );
            }
            let query = prelude
                .query(&[], &Substitution::new(), &[Predicate::Ceil(value)], false)
                .unwrap()
                .unwrap();
            assert_eq!(query.exactness(), Exactness::Approximate);
            query.base().len() + query.checked().to_string().len()
        };
        let small = size(16);
        let large = size(32);
        assert!(large < 250_000, "shared domain DAG emitted {large} bytes");
        assert!(large < small * 6, "domain DAG growth {small} -> {large}");
    }

    #[test]
    fn source_head_facts_are_guarded_by_the_original_argument_domains() {
        use super::super::{Satisfiability, SmtSolver};
        let definition = congruence_definition();
        let solver = super::super::Z3Solver::new(&definition).unwrap();
        let known = [
            Predicate::Forall(
                Variable::new("X", int()),
                Arc::new(Predicate::Ceil(parsed_term(
                    &definition,
                    "onDefined{}(X:SortInt{})",
                ))),
            ),
            Predicate::Not(Arc::new(Predicate::Ceil(parsed_term(
                &definition,
                r#"partial{}(\dv{SortInt{}}("0"))"#,
            )))),
            Predicate::Not(Arc::new(Predicate::Ceil(parsed_term(
                &definition,
                r#"onDefined{}(partial{}(\dv{SortInt{}}("0")))"#,
            )))),
        ];
        // The source head exists on every Int, but a strict application to an undefined
        // argument is still undefined. Its totalized argument must not constrain the head.
        assert_eq!(
            solver.is_sat(&known, &Substitution::new()),
            Ok(Ok(Satisfiability::Sat))
        );
    }

    #[test]
    fn a_domain_equation_effect_keeps_value_and_domain_readings_opaque() {
        use super::super::{SmtSolver, Validity};
        let definition = congruence_definition();
        assert!(
            definition
                .console_effect_symbols()
                .unwrap()
                .contains("domainEffect")
        );
        let left = parsed_term(
            &definition,
            r#"domainEffect{}(plus{}(X:SortInt{},\dv{SortInt{}}("1")))"#,
        );
        let right = parsed_term(
            &definition,
            r#"domainEffect{}(plus{}(\dv{SortInt{}}("1"),X:SortInt{}))"#,
        );
        let solver = super::super::Z3Solver::new(&definition).unwrap();
        assert_eq!(
            solver.check_predicates(
                &[Predicate::Ceil(left)],
                &Substitution::new(),
                &[Predicate::Ceil(right)],
            ),
            Ok(Ok(Validity::Contingent)),
        );
    }

    #[test]
    fn a_false_boolean_value_is_distinct_from_an_undefined_boolean() {
        use super::super::{Satisfiability, SmtSolver};
        let definition = congruence_definition();
        let term = parsed_term(&definition, r#"booleanPartial{}(\dv{SortInt{}}("0"))"#);
        let predicates = [
            Predicate::Ceil(term.clone()),
            Predicate::Not(Arc::new(Predicate::Term(term))),
        ];
        let solver = super::super::Z3Solver::new(&definition).unwrap();
        assert_eq!(
            solver.is_sat(&predicates, &Substitution::new()),
            Ok(Ok(Satisfiability::Sat))
        );
    }

    #[test]
    fn eliminating_a_domain_keeps_uninterpreted_free_carriers_approximate() {
        let syntax = k_rust_kore::kore::parser::parse_definition(
            "[] module MAIN sort SortS{} [] endmodule []",
        )
        .unwrap();
        let definition =
            crate::definition::BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let term = parsed_term(&definition, "X:SortS{}");
        let query = SmtPrelude::from_definition(&definition)
            .unwrap()
            .query(&[], &Substitution::new(), &[Predicate::Ceil(term)], false)
            .unwrap()
            .unwrap();
        assert_eq!(query.exactness(), Exactness::Approximate);
        assert!(query.model_mappings().is_none());
    }

    #[test]
    fn congruence_signatures_distinguish_closed_instantiations_and_preserve_explicit_mappings() {
        let definition = congruence_definition();
        let known = [
            Predicate::Equals(
                parsed_term(&definition, "poly{SortInt{}}(X:SortInt{})"),
                integer("0"),
            ),
            Predicate::Equals(
                parsed_term(&definition, "poly{SortBool{}}(B:SortBool{})"),
                Term::bool(true),
            ),
            Predicate::Equals(
                parsed_term(&definition, "named{}(X:SortInt{})"),
                integer("0"),
            ),
        ];
        let query = SmtPrelude::from_definition(&definition)
            .unwrap()
            .query(&known, &Substitution::new(), &[], false)
            .unwrap()
            .unwrap();
        assert_eq!(query.base().matches("(declare-fun SMT-").count(), 2);
        assert!(query.base().contains("(Int) Int)"));
        assert!(query.base().contains("(Bool) Bool)"));
        assert!(query.base().contains("(NAMED "));
        use super::super::{Satisfiability, SmtSolver};
        assert_eq!(
            super::super::Z3Solver::new(&definition)
                .unwrap()
                .is_sat(&known, &Substitution::new()),
            Ok(Ok(Satisfiability::Sat))
        );
    }

    #[test]
    fn congruence_lets_stay_inside_alpha_renamed_and_shadowed_binders() {
        use super::super::{SmtSolver, Validity};
        let definition = congruence_definition();
        let x = Variable::new("X", int());
        let y = Variable::new("Y", int());
        let known = [Predicate::Forall(
            x.clone(),
            Arc::new(Predicate::Equals(
                parsed_term(&definition, "f{}(X:SortInt{})"),
                Term::variable(x.clone()),
            )),
        )];
        let body = Predicate::Equals(
            parsed_term(
                &definition,
                r#"f{}(plus{}(Y:SortInt{}, \dv{SortInt{}}("0")))"#,
            ),
            Term::variable(y.clone()),
        );
        let checked = [Predicate::Exists(
            x.clone(),
            Arc::new(Predicate::Forall(
                y,
                Arc::new(Predicate::Exists(x, Arc::new(body))),
            )),
        )];
        assert_eq!(
            super::super::Z3Solver::new(&definition)
                .unwrap()
                .check_predicates(&known, &Substitution::new(), &checked),
            Ok(Ok(Validity::Valid))
        );
    }

    #[test]
    fn shared_opaque_term_dags_have_bounded_emission_and_valid_let_scopes() {
        use super::super::{Satisfiability, SmtSolver};
        let definition = congruence_definition();
        let prelude = SmtPrelude::from_definition(&definition).unwrap();
        let f = |name: &str, args: Vec<Term>| {
            Term::application(definition.symbols()[name].clone(), vec![], args)
        };
        let mut sizes = Vec::new();
        for depth in [4, 8, 16, 32] {
            let mut term = variable("X", int());
            for _ in 0..depth {
                term = f("pair", vec![f("g", vec![term.clone()]), f("h", vec![term])]);
            }
            let predicates = [Predicate::Not(Arc::new(Predicate::Equals(
                term.clone(),
                term,
            )))];
            let query = prelude
                .query(&predicates, &Substitution::new(), &[], false)
                .unwrap()
                .unwrap();
            let bytes = query.base().len();
            if let Some(previous) = sizes.last() {
                assert!(
                    bytes < previous * 3,
                    "doubling DAG depth expanded {previous} bytes to {bytes}"
                );
            }
            sizes.push(bytes);
            assert_eq!(
                super::super::Z3Solver::new(&definition)
                    .unwrap()
                    .is_sat(&predicates, &Substitution::new()),
                Ok(Ok(Satisfiability::Unsat))
            );
        }
    }

    #[test]
    fn default_translation_and_scalar_queries_keep_their_prior_contracts() {
        let definition = congruence_definition();
        let opaque = parsed_term(&definition, "f{}(X:SortInt{})");
        let mut legacy = TranslationState::new();
        legacy.translate_term(&opaque).unwrap();
        assert!(legacy.opaque_functions.is_empty());
        assert!(legacy.mappings.contains_key(&opaque));
        let known = [Predicate::Equals(
            parsed_term(
                &definition,
                r#"plus{}(plus{}(X:SortInt{},\dv{SortInt{}}("1")),\dv{SortInt{}}("2"))"#,
            ),
            integer("7"),
        )];
        let query = SmtPrelude::from_definition(&definition)
            .unwrap()
            .query(&known, &Substitution::new(), &[], false)
            .unwrap()
            .unwrap();
        assert_eq!(query.exactness(), Exactness::Exact);
        assert!(query.model_mappings().is_some());
        assert!(!query.base().contains("(let "), "{}", query.base());
    }
}
