//! Product reconstruction from complete source no-junk and actual field equations.
//! A field name, a total declaration, or a constructor alone supplies no inverse.

use std::{collections::BTreeMap, sync::Arc};

use crate::{
    definition::{BackendDefinition, ConstructorHead},
    rule::{RewriteRule, RuleRhs, TermIndex},
    term::{HeadRole, Name, Sort, Sorts, Symbol, Term, TermKind, VariableKind},
};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Key(Name, Sorts);

#[derive(Clone, Debug)]
struct Field {
    head: Arc<Symbol>,
    sorts: Sorts,
    input: Sort,
    output: Sort,
    column: usize,
}

impl Field {
    fn input_of<'a>(&self, term: &'a Term) -> Option<&'a Term> {
        let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = term.kind()
        else {
            return None;
        };
        let [input] = arguments.as_slice() else {
            return None;
        };
        (symbol == &self.head
            && sort_arguments == &self.sorts
            && input.sort() == self.input
            && term.sort() == self.output)
            .then_some(input)
    }
}

#[derive(Clone, Debug)]
struct Product {
    head: Arc<Symbol>,
    sorts: Sorts,
    sort: Sort,
    arguments: Vec<Sort>,
    fields: Vec<Vec<Arc<Field>>>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Products {
    constructors: BTreeMap<Key, Product>,
    by_sort: BTreeMap<Sort, Key>,
    fields: BTreeMap<Key, Arc<Field>>,
}

impl BackendDefinition {
    pub(crate) fn products(&self) -> Option<&Products> {
        if let Some(products) = self.product_observations.get() {
            return Some(products);
        }
        self.console_effect_symbols()?;
        self.equation_selection_complete()?;
        Some(self.product_observations.get_or_init(|| Products::of(self)))
    }
}

impl Products {
    fn of(definition: &BackendDefinition) -> Self {
        let Some(effects) = definition.console_effect_symbols() else {
            return Self::default();
        };
        if definition.classified_axioms().len() > 16_384
            || definition.symbols().len() > 16_384
            || [
                definition.function_theory(),
                definition.simplification_theory(),
                definition.ceil_theory(),
            ]
            .into_iter()
            .any(|t| t.contains_key(&TermIndex::Variable) || t.contains_key(&TermIndex::And))
        {
            return Self::default();
        }
        let mut products = Self::default();
        for (sort, head) in definition.sole_constructor_heads() {
            let ConstructorHead::Symbol {
                name,
                sort_arguments,
            } = head
            else {
                continue;
            };
            let Some(symbol) = definition.symbols().get(name) else {
                continue;
            };
            if symbol.attributes.head_role() != HeadRole::FreeConstructor
                || symbol.attributes.binder
                || symbol.attributes.hook.is_some()
                || symbol.attributes.smt.is_some()
                || effects.contains(name.as_ref())
                || sort_arguments.len() != symbol.sort_variables.len()
                || sort_arguments.iter().any(Sort::has_variable)
                || symbol.argument_sorts.len() > 128
            {
                continue;
            }
            let index = TermIndex::Symbol(name.clone());
            if [
                definition.function_theory(),
                definition.simplification_theory(),
                definition.ceil_theory(),
            ]
            .into_iter()
            .any(|t| {
                t.get(&index)
                    .is_some_and(|g| g.values().any(|r| !r.is_empty()))
            }) {
                continue;
            }
            let bindings = symbol
                .sort_variables
                .iter()
                .cloned()
                .zip(sort_arguments.iter().copied())
                .collect();
            let arguments = symbol
                .argument_sorts
                .iter()
                .map(|s| crate::definition::substitute_sort(s, &bindings))
                .collect::<Vec<_>>();
            if crate::definition::substitute_sort(&symbol.result_sort, &bindings) != sort
                || arguments.iter().any(|s| s.has_variable() || *s == sort)
            {
                continue;
            }
            let key = Key(name.clone(), *sort_arguments);
            products.by_sort.insert(sort, key.clone());
            products.constructors.insert(
                key,
                Product {
                    head: symbol.clone(),
                    sorts: *sort_arguments,
                    sort,
                    fields: vec![Vec::new(); arguments.len()],
                    arguments,
                },
            );
        }
        let mut remaining = 16_384usize;
        for theory in [
            definition.function_theory(),
            definition.simplification_theory(),
        ] {
            for groups in theory.values() {
                for rows in groups.values() {
                    if rows.len() > remaining {
                        return Self::default();
                    }
                    remaining -= rows.len();
                    for row in rows {
                        let Some((key, column, field)) = products.field(definition, row, &effects)
                        else {
                            continue;
                        };
                        products
                            .fields
                            .insert(Key(field.head.name.clone(), field.sorts), field.clone());
                        products
                            .constructors
                            .get_mut(&key)
                            .expect("checked constructor")
                            .fields[column]
                            .push(field);
                    }
                }
            }
        }
        products
    }

    fn field(
        &self,
        definition: &BackendDefinition,
        row: &Arc<RewriteRule>,
        effects: &std::collections::BTreeSet<String>,
    ) -> Option<(Key, usize, Arc<Field>)> {
        if !super::plain(row) || !row.requires.is_empty() || row.attributes.priority != 50 {
            return None;
        }
        let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = row.lhs.kind()
        else {
            return None;
        };
        let [input] = arguments.as_slice() else {
            return None;
        };
        if !matches!(
            symbol.attributes.head_role(),
            HeadRole::Function { declared: true, .. }
        ) || symbol.attributes.hook.is_some()
            || symbol.attributes.smt.is_some()
            || symbol.attributes.binder
            || symbol.attributes.macro_or_alias
            || effects.contains(symbol.name.as_ref())
            || sort_arguments.iter().any(Sort::has_variable)
        {
            return None;
        }
        let TermKind::Application {
            symbol: constructor,
            sort_arguments: sorts,
            arguments: fields,
        } = input.kind()
        else {
            return None;
        };
        let key = Key(constructor.name.clone(), *sorts);
        let product = self.constructors.get(&key)?;
        if constructor != &product.head
            || input.sort() != product.sort
            || fields.len() != product.arguments.len()
            || !fields
                .iter()
                .map(Term::sort)
                .eq(product.arguments.iter().copied())
        {
            return None;
        }
        let mut variables = std::collections::BTreeSet::new();
        for field in fields {
            let TermKind::Variable(variable) = field.kind() else {
                return None;
            };
            if variable.kind != VariableKind::Element || !variables.insert(variable) {
                return None;
            }
        }
        let RuleRhs::Term(result) = &row.rhs else {
            return None;
        };
        let column = fields.iter().position(|field| field == result)?;
        let index = TermIndex::Symbol(symbol.name.clone());
        let mut offered = 0usize;
        for (domain, theory) in [
            (false, definition.function_theory()),
            (false, definition.simplification_theory()),
            (true, definition.ceil_theory()),
        ] {
            if let Some(groups) = theory.get(&index) {
                for rows in groups.values() {
                    if rows.len() > 128usize.saturating_sub(offered) {
                        return None;
                    }
                    offered += rows.len();
                    for other in rows {
                        let TermKind::Application {
                            sort_arguments: actual,
                            ..
                        } = other.lhs.kind()
                        else {
                            return None;
                        };
                        if actual.iter().any(Sort::has_variable) {
                            return None;
                        }
                        if actual != sort_arguments {
                            continue;
                        }
                        if domain || !Arc::ptr_eq(other, row) {
                            return None;
                        }
                    }
                }
            }
        }
        Some((
            key,
            column,
            Arc::new(Field {
                head: symbol.clone(),
                sorts: *sort_arguments,
                input: product.sort,
                output: result.sort(),
                column,
            }),
        ))
    }

    pub(crate) fn reconstruction(&self, term: &Term) -> Option<Term> {
        let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = term.kind()
        else {
            return None;
        };
        let product = self
            .constructors
            .get(&Key(symbol.name.clone(), *sort_arguments))?;
        if symbol != &product.head
            || sort_arguments != &product.sorts
            || term.sort() != product.sort
            || arguments.len() != product.arguments.len()
            || arguments.is_empty()
        {
            return None;
        }
        let mut base: Option<&Term> = None;
        for (argument, fields) in arguments.iter().zip(&product.fields) {
            let input = fields.iter().find_map(|field| field.input_of(argument))?;
            if base.is_some_and(|base| base != input) {
                return None;
            }
            base = Some(input);
        }
        base.cloned()
    }

    pub(crate) fn field_is_defined(&self, term: &Term) -> bool {
        let TermKind::Application {
            symbol,
            sort_arguments,
            ..
        } = term.kind()
        else {
            return false;
        };
        self.fields
            .get(&Key(symbol.name.clone(), *sort_arguments))
            .is_some_and(|field| field.input_of(term).is_some())
    }

    /// One deterministic source witness, to be used as a demand on the original value's
    /// domain. It does not unfold the original value or assume that it is defined.
    pub(crate) fn canonical(&self, term: &Term) -> Option<Term> {
        let product = self.constructors.get(self.by_sort.get(&term.sort())?)?;
        if product.fields.is_empty() {
            return None;
        }
        let arguments = product
            .fields
            .iter()
            .map(|fields| {
                let field = fields.first()?;
                Some(Term::application(
                    field.head.clone(),
                    field.sorts,
                    vec![term.clone()],
                ))
            })
            .collect::<Option<Vec<_>>>()?;
        Some(Term::application(
            product.head.clone(),
            product.sorts,
            arguments,
        ))
    }

    pub(crate) fn field_value(&self, term: &Term) -> Option<Term> {
        let TermKind::Application {
            symbol,
            sort_arguments,
            ..
        } = term.kind()
        else {
            return None;
        };
        let field = self
            .fields
            .get(&Key(symbol.name.clone(), *sort_arguments))?;
        let input = field.input_of(term)?;
        let product = self.constructors.get(self.by_sort.get(&input.sort())?)?;
        if let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = input.kind()
            && symbol == &product.head
            && sort_arguments == &product.sorts
            && arguments.len() == product.arguments.len()
            && arguments
                .iter()
                .map(Term::sort)
                .eq(product.arguments.iter().copied())
        {
            return Some(arguments[field.column].clone());
        }
        // Distinct checked observers of the same field agree on every defined product.
        let canonical = product.fields[field.column].first()?;
        if canonical.head == field.head && canonical.sorts == field.sorts {
            return None;
        }
        Some(Term::application(
            canonical.head.clone(),
            canonical.sorts,
            vec![input.clone()],
        ))
    }
}

/// Complete no-junk and the admitted field equation cover every defined input value.
/// The canonical definedness caller retains the input's strict domain.
///
/// `\top` beyond the input's own domain is the weakest condition, so it never refutes a defined instance.
/// The reconstruction fact `\ceil(p) -> p = c(f1(p), .., fn(p))` that the SMT reading adds
/// holds of every defined `p` by the same no-junk argument (kink27 R2-DOMAIN-ROUTES).
pub(crate) fn field_domain(
    definition: &BackendDefinition,
    term: &Term,
) -> Option<Vec<crate::rule::Predicate>> {
    definition.products()?.field_is_defined(term).then(Vec::new)
}

#[cfg(test)]
mod tests {
    use super::*;
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    const NO_JUNK: &str = r#"axiom{} \or{SortPair{}}(
      \exists{SortPair{}}(A:SortInt{},\exists{SortPair{}}(B:SortInt{},pair{}(A:SortInt{},B:SortInt{}))),
      \bottom{SortPair{}}()) [constructor{}()]"#;

    const BASE: &str = r#"[] module MAIN
      hooked-sort SortInt{} [hook{}("INT.Int"),hasDomainValues{}()]
      sort SortPair{} []
      symbol pair{}(SortInt{},SortInt{}) : SortPair{} [constructor{}()]
      symbol first{}(SortPair{}) : SortInt{} [function{}()]
      symbol second{}(SortPair{}) : SortInt{} [function{}()]
      symbol context{}(SortPair{}) : SortInt{} [function{}()]
      axiom{R} \implies{R}(\top{R}(),\equals{SortInt{},R}(first{}(pair{}(A:SortInt{},B:SortInt{})),\and{SortInt{}}(A:SortInt{},\top{SortInt{}}()))) [simplification{}()]
      axiom{R} \implies{R}(\top{R}(),\equals{SortInt{},R}(second{}(pair{}(A:SortInt{},B:SortInt{})),\and{SortInt{}}(B:SortInt{},\top{SortInt{}}()))) [simplification{}()]
    endmodule []"#;

    fn source() -> String {
        BASE.replace("endmodule", &format!("{NO_JUNK} endmodule"))
    }

    fn load(source: &str) -> BackendDefinition {
        BackendDefinition::internalize(&parse_definition(source).unwrap(), "MAIN").unwrap()
    }

    fn term(definition: &BackendDefinition, text: &str) -> Term {
        definition
            .internalize_term(&parse_pattern(text).unwrap(), &[])
            .unwrap()
    }

    #[test]
    fn complete_no_junk_and_actual_fields_justify_reconstruction_and_partial_field_domains() {
        let definition = load(&source());
        let rebuilt = term(
            &definition,
            "pair{}(first{}(P:SortPair{}),second{}(P:SortPair{}))",
        );
        let original = term(&definition, "P:SortPair{}");
        assert_eq!(
            definition.products().unwrap().reconstruction(&rebuilt),
            Some(original.clone())
        );
        assert_eq!(
            field_domain(&definition, &term(&definition, "first{}(P:SortPair{})")),
            Some(vec![])
        );
        let plan = crate::observation::reading::Builder::new(&definition)
            .of(&rebuilt)
            .unwrap()
            .unwrap();
        assert_eq!(
            plan.as_ref(),
            &crate::observation::reading::Reading::Leaf(original.clone())
        );
        #[cfg(feature = "z3")]
        {
            use crate::smt::{SmtSolver, Validity, Z3Solver};
            let solver = Z3Solver::new(&definition).unwrap();
            let checked = [
                crate::rule::Predicate::Equals(original, rebuilt),
                crate::rule::Predicate::Ceil(term(&definition, "first{}(P:SortPair{})")),
            ];
            assert_eq!(
                solver
                    .check_predicates(&[], &crate::substitution::Substitution::new(), &checked)
                    .unwrap()
                    .unwrap(),
                Validity::Valid
            );
        }
    }

    #[test]
    fn forward_fields_do_not_supply_no_junk_or_missing_columns() {
        for text in [
            BASE.to_owned(),
            source().replace(
                r#"\and{SortInt{}}(B:SortInt{},\top{SortInt{}}())"#,
                r#"\and{SortInt{}}(A:SortInt{},\top{SortInt{}}())"#,
            ),
            source().replace(
                "endmodule",
                "symbol other{}() : SortPair{} [constructor{}()] endmodule",
            ),
        ] {
            let definition = load(&text);
            let rebuilt = term(
                &definition,
                "pair{}(first{}(P:SortPair{}),second{}(P:SortPair{}))",
            );
            assert!(
                definition
                    .products()
                    .unwrap()
                    .reconstruction(&rebuilt)
                    .is_none()
            );
            #[cfg(feature = "z3")]
            {
                use crate::smt::{SmtSolver, Validity, Z3Solver};
                let checked = [crate::rule::Predicate::Equals(
                    term(&definition, "P:SortPair{}"),
                    rebuilt,
                )];
                assert_ne!(
                    Z3Solver::new(&definition)
                        .unwrap()
                        .check_predicates(&[], &crate::substitution::Substitution::new(), &checked)
                        .unwrap()
                        .unwrap(),
                    Validity::Valid
                );
            }
        }
    }

    #[test]
    fn offered_domain_overrides_and_effects_decline_the_field_contract() {
        let domain = source().replace("endmodule",r#"axiom{R} \implies{R}(\top{R}(),\equals{R,R}(\ceil{SortInt{},R}(first{}(P:SortPair{})),\bottom{R}())) [] endmodule"#);
        let impure = source().replace(
            "first{}(SortPair{}) : SortInt{} [function{}()]",
            "first{}(SortPair{}) : SortInt{} [function{}(),impure{}()]",
        );
        for text in [domain, impure] {
            let definition = load(&text);
            assert!(
                field_domain(&definition, &term(&definition, "first{}(P:SortPair{})")).is_none()
            );
            assert!(
                definition
                    .products()
                    .unwrap()
                    .reconstruction(&term(
                        &definition,
                        "pair{}(first{}(P:SortPair{}),second{}(P:SortPair{}))"
                    ))
                    .is_none()
            );
        }
    }

    #[cfg(feature = "z3")]
    #[test]
    fn product_field_equalities_compose_through_an_opaque_partial_context() {
        use crate::{
            rule::Predicate,
            smt::{SmtSolver, Validity, Z3Solver},
            substitution::Substitution,
        };
        let definition = load(&source());
        let known = [
            Predicate::Equals(
                term(&definition, "first{}(P:SortPair{})"),
                term(&definition, "first{}(Q:SortPair{})"),
            ),
            Predicate::Equals(
                term(&definition, "second{}(P:SortPair{})"),
                term(&definition, "second{}(Q:SortPair{})"),
            ),
        ];
        let checked = [Predicate::Equals(
            term(&definition, "context{}(P:SortPair{})"),
            term(&definition, "context{}(Q:SortPair{})"),
        )];
        assert_eq!(
            Z3Solver::new(&definition)
                .unwrap()
                .check_predicates(&known, &Substitution::new(), &checked)
                .unwrap()
                .unwrap(),
            Validity::Valid
        );
        let single_scope = Predicate::And(
            vec![
                Predicate::Ceil(term(&definition, "first{}(P:SortPair{})")),
                Predicate::Implies(
                    Arc::new(Predicate::And(known.to_vec().into())),
                    Arc::new(checked[0].clone()),
                ),
            ]
            .into(),
        );
        assert_eq!(
            Z3Solver::new(&definition)
                .unwrap()
                .check_predicates(&[], &Substitution::new(), &[single_scope])
                .unwrap()
                .unwrap(),
            Validity::Valid
        );
        let concrete_alias = [Predicate::Equals(
            term(&definition, "P:SortPair{}"),
            term(
                &definition,
                r#"pair{}(\dv{SortInt{}}("1"),\dv{SortInt{}}("2"))"#,
            ),
        )];
        let concrete_read = [Predicate::Equals(
            term(&definition, "first{}(P:SortPair{})"),
            Term::int(1),
        )];
        assert_eq!(
            Z3Solver::new(&definition)
                .unwrap()
                .check_predicates(&concrete_alias, &Substitution::new(), &concrete_read)
                .unwrap()
                .unwrap(),
            Validity::Valid
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn static_scalar_cases_share_value_domains_and_keep_exact_only_model_queries() {
        use crate::{
            model::ModelQuery,
            rule::Predicate,
            smt::{ModelResult, Satisfiability, SmtSolver, Validity, Z3Solver},
            substitution::Substitution,
            term::Variable,
        };
        let text = source().replace("endmodule",r#"
          sort SortTag{} []
          symbol tag0{}() : SortTag{} [constructor{}()]
          symbol tag1{}() : SortTag{} [constructor{}()]
          symbol partial{}(SortInt{}) : SortInt{} [function{}()]
          hooked-symbol add{}(SortInt{},SortInt{}) : SortInt{} [function{}(),total{}(),hook{}("INT.add"),smt-hook{}("+")]
          symbol helper{}(SortTag{},SortInt{}) : SortInt{} [function{}()]
          axiom{R} \implies{R}(\top{R}(),\equals{SortInt{},R}(helper{}(tag0{}(),X:SortInt{}),\and{SortInt{}}(add{}(X:SortInt{},\dv{SortInt{}}("1")),\top{SortInt{}}()))) [simplification{}()]
          axiom{R} \implies{R}(\top{R}(),\equals{SortInt{},R}(helper{}(tag1{}(),X:SortInt{}),\and{SortInt{}}(X:SortInt{},\top{SortInt{}}()))) [simplification{}()]
        endmodule"#);
        let definition = load(&text);
        let solver = Z3Solver::new(&definition).unwrap();
        let alias = Predicate::Equals(
            term(&definition, "T:SortTag{}"),
            term(&definition, "tag0{}()"),
        );
        let opaque = term(&definition, "helper{}(T:SortTag{},X:SortInt{})");
        let specialized = term(&definition, "helper{}(tag0{}(),X:SortInt{})");
        assert_eq!(
            solver
                .check_predicates(
                    std::slice::from_ref(&alias),
                    &Substitution::new(),
                    &[
                        Predicate::Equals(opaque.clone(), specialized),
                        Predicate::Ceil(opaque)
                    ]
                )
                .unwrap()
                .unwrap(),
            Validity::Valid
        );
        let partial = term(&definition, "partial{}(X:SortInt{})");
        let undefined_call = term(&definition, "helper{}(tag0{}(),partial{}(X:SortInt{}))");
        let z = Variable::new("Z", Sort::simple("SortInt"));
        let known = [
            alias,
            Predicate::Not(Arc::new(Predicate::Ceil(partial))),
            Predicate::Not(Arc::new(Predicate::Ceil(undefined_call))),
            Predicate::Forall(
                z,
                Arc::new(Predicate::Ceil(term(
                    &definition,
                    "helper{}(T:SortTag{},Z:SortInt{})",
                ))),
            ),
        ];
        assert_eq!(
            solver
                .is_sat(&known, &Substitution::new())
                .unwrap()
                .unwrap(),
            Satisfiability::Sat
        );
        let r = Variable::new("R", Sort::simple("SortInt"));
        let exact = [Predicate::Equals(
            Term::variable(r.clone()),
            term(&definition, r#"helper{}(tag0{}(),\dv{SortInt{}}("4"))"#),
        )];
        let substitution = Substitution::new();
        let model = solver
            .get_model(&ModelQuery::for_solver_tests(&exact, &substitution))
            .unwrap()
            .unwrap();
        assert!(
            matches!(model,ModelResult::Sat(ref values) if values.get(&r) == Some(&Term::int(5))),
            "{model:?}"
        );
    }
}
