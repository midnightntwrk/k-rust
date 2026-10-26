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
            .expect("the query should translate");
        assert_eq!(filtered.exactness(), Exactness::Approximate);
        assert!(!filtered.base().contains("(assert"));

        let related = [Predicate::Equals(x, integer("2"))];
        let kept = prelude()
            .query(&related, &Substitution::new(), &checked, true)
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
                symbol effect{}(SortInt{}) : SortInt{} [function{}(), total{}(), impure{}()]
                symbol wrapped{}(SortInt{}) : SortInt{} [function{}(), total{}()]
                symbol poly{S}(S) : S [function{}(), total{}()]
                symbol named{}(SortInt{}) : SortInt{} [function{}(), total{}(), smtlib{}("NAMED")]
                hooked-symbol plus{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
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
    fn congruence_does_not_assert_injectivity_or_a_partial_or_effectful_function_rank() {
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
        for head in ["partial", "effect", "wrapped"] {
            let predicates = [Predicate::Equals(
                parsed_term(&definition, &format!("{head}{{}}(X:SortInt{{}})")),
                integer("0"),
            )];
            let query = prelude
                .query(&predicates, &Substitution::new(), &[], false)
                .unwrap();
            assert!(!query.base().contains("(declare-fun SMT-"), "{head}");
            assert!(query.model_mappings().is_none());
        }
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
            .unwrap();
        assert_eq!(query.exactness(), Exactness::Exact);
        assert!(query.model_mappings().is_some());
        assert!(!query.base().contains("(let "), "{}", query.base());
    }
}
