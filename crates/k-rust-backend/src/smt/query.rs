//! A query posed to the solver, with the exactness its translation recorded.

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
}

impl TranslatedQuery {
    /// Takes the finished translation, so the query's exactness and mappings are read from the
    /// state that recorded them; no caller states an exactness.
    pub(super) fn new(base: String, checked: SExpr, translation: TranslationState) -> Self {
        Self {
            base,
            checked,
            exactness: translation.exactness(),
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
        }
    }

    fn int() -> Sort {
        Sort::simple("SortInt")
    }

    fn integer(value: &str) -> Term {
        Term::domain_value(int(), value)
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
}
