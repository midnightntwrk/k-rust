//! ```toml algorithm
//! id = "backend.observation.selectors"
//! name = "source-checked selector catalog and local image test"
//! sites = ["Selectors::of", "Selectors::checked", "selector_domain"]
//! variable = "A = classified source axioms; C = ceil rows; I = candidate inverse rows at their root index; E = embedding nodes; M = image-match work"
//! counters = []
//! no_counter = "The definition-local catalog has no dedicated counter; the ordinary matcher retains its measurements."
//! span = "none"
//! invariant = "Each retained selector has the exact source image-domain, forward and conditional inverse equations; source names or markers supply none of these facts."
//!
//! [[cost]]
//! mode = "one immutable definition, then one local instance"
//! bound = "O(C * (I + E) + A) catalog work plus structural comparisons; catalog discovery declines above 16384 source axioms or 128 inverse candidates for a selector. A cached rank lookup costs O(log C), then one ordinary image match costs M. This bounds catalog work, not solver work."
//! ```
//!
//! Source-checked local observation contracts.
//!
//! A selector name or its forward equation supplies no inverse law. A selector view is
//! available only when this immutable definition contains the complete exact image-domain,
//! forward and guarded reconstruction equations, at compatible pure ranks. The existing
//! definedness and equation machinery continues to evaluate those ordinary source axioms.

pub(crate) mod maps;
pub(crate) mod reading;

use std::{collections::BTreeMap, sync::Arc};

use crate::{
    definition::BackendDefinition,
    rule::{Predicate, RewriteRule, RuleRhs, TermIndex},
    substitution::{Substitution, substitute},
    term::{FunctionType, Name, Sort, Symbol, SymbolType, Term, TermKind, Variable},
};

#[derive(Clone, Debug, Default)]
pub(crate) struct Selectors {
    by_name: BTreeMap<Name, Selector>,
    by_rank: BTreeMap<(Sort, Sort), Option<Name>>,
}

#[derive(Clone, Debug)]
pub(crate) struct Selector {
    head: Arc<Symbol>,
    value: Variable,
    embedding: Term,
}

impl Selector {
    /// Read only the checked forward equation on an actual embedding instance.
    pub(crate) fn value_in(&self, definition: &BackendDefinition, input: &Term) -> Option<Term> {
        let mut value = self.value.clone();
        while input.attributes().variables.contains(&value) {
            value.name = format!("{}'", value.name).into();
        }
        let pattern = self.embed(Term::variable(value.clone()));
        match crate::matching::match_terms_in_definition(
            crate::matching::MatchMode::Implies,
            definition,
            &pattern,
            input,
        ) {
            crate::matching::MatchResult::Success(bindings) => bindings.get(&value).cloned(),
            _ => None,
        }
    }

    /// The source embedding, not an assumed direct coercion to K.
    pub(crate) fn embed(&self, value: Term) -> Term {
        let substitution = Substitution::from([(self.value.clone(), value)]);
        substitute(&self.embedding, &substitution)
    }

    pub(crate) fn project(&self, input: Term) -> Option<Term> {
        (input.sort() == self.head.argument_sorts[0])
            .then(|| Term::application(self.head.clone(), vec![], vec![input]))
    }
}

/// Decide an exact image-domain instance without querying a solver or evaluating a body.
/// Undefined child obligations remain the caller's strict-argument obligations.
pub(crate) fn selector_domain(definition: &BackendDefinition, term: &Term) -> Option<bool> {
    let TermKind::Application { arguments, .. } = term.kind() else {
        return None;
    };
    let [input] = arguments.as_slice() else {
        return None;
    };
    let selector = definition.selector(&input.sort(), &term.sort())?;
    if selector.project(input.clone()).as_ref() != Some(term) {
        return None;
    }
    let mut witness = selector.value.clone();
    while input.attributes().variables.contains(&witness) {
        witness.name = format!("{}'", witness.name).into();
    }
    let image = selector.embed(Term::variable(witness));
    match crate::matching::match_terms_in_definition(
        crate::matching::MatchMode::Implies,
        definition,
        &image,
        input,
    ) {
        crate::matching::MatchResult::Success(_) => Some(true),
        crate::matching::MatchResult::Failed(_) => Some(false),
        crate::matching::MatchResult::Indeterminate { .. }
        | crate::matching::MatchResult::Undecided(_) => None,
    }
}

impl BackendDefinition {
    fn selectors(&self) -> Option<&Selectors> {
        if let Some(selectors) = self.selector_contracts.get() {
            return Some(selectors);
        }
        self.console_effect_symbols()?;
        Some(self.selector_contracts.get_or_init(|| Selectors::of(self)))
    }

    /// Only complete, definition-local source contracts may justify typed observations.
    pub(crate) fn selector(&self, input: &Sort, value: &Sort) -> Option<&Selector> {
        // Early load analyses run before effects are indexed. Do not memoize that temporary
        // absence as a permanent contract decision.
        let selectors = self.selectors()?;
        let name = selectors.by_rank.get(&(*input, *value))?.as_ref()?;
        selectors.by_name.get(name)
    }
}

impl Selectors {
    fn of(definition: &BackendDefinition) -> Self {
        let Some(effects) = definition.console_effect_symbols() else {
            return Self::default();
        };
        if definition.equation_selection_complete().is_none()
            || definition.classified_axioms().len() > 16_384
        {
            return Self::default();
        }
        let mut selectors = BTreeMap::new();
        for groups in definition.ceil_theory().values() {
            for rule in groups.values().flatten() {
                if let Some(selector) = Self::checked(definition, rule, &effects) {
                    selectors.insert(selector.head.name.clone(), selector);
                }
            }
        }
        let mut by_rank = BTreeMap::new();
        for selector in selectors.values() {
            let rank = (selector.head.argument_sorts[0], selector.head.result_sort);
            by_rank
                .entry(rank)
                .and_modify(|name| *name = None)
                .or_insert_with(|| Some(selector.head.name.clone()));
        }
        Self {
            by_name: selectors,
            by_rank,
        }
    }

    fn checked(
        definition: &BackendDefinition,
        domain_rule: &RewriteRule,
        effects: &std::collections::BTreeSet<String>,
    ) -> Option<Selector> {
        if !plain(domain_rule) || !domain_rule.requires.is_empty() {
            return None;
        }
        let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = domain_rule.lhs.kind()
        else {
            return None;
        };
        let [input] = arguments.as_slice() else {
            return None;
        };
        let TermKind::Variable(input_variable) = input.kind() else {
            return None;
        };
        if !sort_arguments.is_empty()
            || !symbol.sort_variables.is_empty()
            || symbol.attributes.symbol_type != SymbolType::Function(FunctionType::Partial)
            || symbol.attributes.binder
            || symbol.attributes.macro_or_alias
            || symbol.attributes.smt.is_some()
            || symbol.attributes.hook.is_some()
            || effects.contains(symbol.name.as_ref())
            || symbol.argument_sorts.as_slice() != [input.sort()]
            || symbol.result_sort.has_variable()
        {
            return None;
        }
        let RuleRhs::Predicates(predicates) = &domain_rule.rhs else {
            return None;
        };
        let [Predicate::Exists(value, image)] = predicates.as_slice() else {
            return None;
        };
        let Predicate::Equals(image_input, embedding) = image.as_ref() else {
            return None;
        };
        if input != image_input
            || value == input_variable
            || value.sort != symbol.result_sort
            || !embedding_shape(definition, embedding, value)
            || embedding.sort() != input.sort()
        {
            return None;
        }
        let candidate = Selector {
            head: symbol.clone(),
            value: value.clone(),
            embedding: embedding.clone(),
        };
        let projected = candidate.project(input.clone())?;
        let inverse_left = candidate.embed(projected.clone());
        let expected_domain = Predicate::Ceil(projected);
        let inverses = definition
            .simplification_theory()
            .get(&crate::rule::term_index(&inverse_left))?;
        if inverses.values().map(Vec::len).sum::<usize>() > 128 {
            return None;
        }
        let inverse = inverses.values().flatten().find(|rule| {
            let RuleRhs::Term(result) = &rule.rhs else {
                return false;
            };
            let TermKind::Variable(found) = result.kind() else {
                return false;
            };
            if found.sort != input.sort() || !plain(rule) {
                return false;
            }
            let renaming = Substitution::from([(found.clone(), input.clone())]);
            substitute(&rule.lhs, &renaming) == inverse_left
                && rule.requires.len() == 1
                && rule.requires.iter().all(|condition| {
                    matches!(condition, Predicate::Ceil(call)
                            if Predicate::Ceil(substitute(call, &renaming)) == expected_domain)
                })
        });
        let inverse = inverse?;
        // Source variable names may differ between axioms. Compare by a checked renaming,
        // rather than requiring that the compiler happened to use identical spellings.
        let index = TermIndex::Symbol(symbol.name.clone());
        let forwards = definition.function_theory().get(&index)?;
        let mut offered = forwards.values().flatten();
        let forward = offered.next()?;
        if offered.next().is_some() || !plain(forward) || !forward.requires.is_empty() {
            return None;
        }
        let RuleRhs::Term(result) = &forward.rhs else {
            return None;
        };
        let TermKind::Variable(result_variable) = result.kind() else {
            return None;
        };
        let expected_embedding = substitute(
            embedding,
            &Substitution::from([(value.clone(), result.clone())]),
        );
        let expected_left = candidate.project(expected_embedding)?;
        if result_variable.sort != value.sort || forward.lhs != expected_left {
            return None;
        }
        // Additional ceil or direct simplification rows can alter the supported contract;
        // decline this specialized reading rather than selecting a convenient source subset.
        if definition
            .ceil_theory()
            .get(&index)?
            .values()
            .flatten()
            .count()
            != 1
            || definition
                .simplification_theory()
                .get(&index)
                .is_some_and(|groups| {
                    groups
                        .values()
                        .flatten()
                        .any(|rule| !Arc::ptr_eq(rule, inverse))
                })
            || [
                definition.function_theory(),
                definition.ceil_theory(),
                definition.simplification_theory(),
            ]
            .into_iter()
            .any(|theory| {
                theory.contains_key(&TermIndex::Variable) || theory.contains_key(&TermIndex::And)
            })
        {
            return None;
        }
        Some(candidate)
    }
}

fn plain(rule: &RewriteRule) -> bool {
    rule.attributes.executable
        && rule.attributes.concreteness == crate::rule::Concreteness::Unconstrained
        && rule.ensures.is_empty()
        && rule.existentials.is_empty()
}

/// Exactly an injection/K-singleton spine with one occurrence of the observed value.
/// Every rank and subsort edge comes from the loaded source declaration.
fn embedding_shape(definition: &BackendDefinition, term: &Term, value: &Variable) -> bool {
    match term.kind() {
        TermKind::Variable(found) => found == value,
        TermKind::Injection {
            source,
            target,
            term: inner,
        } => {
            inner.sort() == *source
                && definition.sort_graph().check_subsort(source, target) == Ok(true)
                && embedding_shape(definition, inner, value)
        }
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } => {
            use k_rust_kore::names::WellKnownSymbol;
            let [inner, end] = arguments.as_slice() else {
                return false;
            };
            let TermKind::Application {
                symbol: end_symbol,
                sort_arguments: end_sorts,
                arguments: empty,
            } = end.kind()
            else {
                return false;
            };
            symbol.name.as_ref() == WellKnownSymbol::KSeq.as_str()
                && end_symbol.name.as_ref() == WellKnownSymbol::DotK.as_str()
                && sort_arguments.is_empty()
                && end_sorts.is_empty()
                && empty.is_empty()
                && symbol.argument_sorts.as_slice() == [inner.sort(), end.sort()]
                && symbol.result_sort == term.sort()
                && end.sort() == term.sort()
                && symbol.attributes.head_role() == crate::term::HeadRole::FreeConstructor
                && end_symbol.attributes.head_role() == crate::term::HeadRole::FreeConstructor
                && embedding_shape(definition, inner, value)
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{definedness::ceil_term, term::Sort};

    const SOURCE: &str = r#"[] module MAIN
      sort SortS{} []
      sort SortC{} []
      symbol inj{From,To}(From) : To [sortInjection{}()]
      symbol other{}() : SortC{} [constructor{}()]
      symbol partial{}() : SortS{} [function{}()]
      symbol p{}(SortC{}) : SortS{} [function{}()]
      axiom{R} \exists{SortC{}}(X:SortC{},\equals{SortC{},SortC{}}(X:SortC{},inj{SortS{},SortC{}}(Y:SortS{}))) [subsort{SortS{},SortC{}}()]
      axiom{R} \implies{R}(
        \and{R}(\top{R}(),\and{R}(\in{SortC{},R}(X:SortC{},inj{SortS{},SortC{}}(Y:SortS{})),\top{R}())),
        \equals{SortS{},R}(p{}(X:SortC{}),\and{SortS{}}(Y:SortS{},\top{SortS{}}()))) [label{}("forward")]
      axiom{R} \implies{R}(\top{R}(),\equals{R,R}(
        \ceil{SortS{},R}(p{}(X:SortC{})),
        \exists{R}(Y:SortS{},\equals{SortC{},R}(X:SortC{},inj{SortS{},SortC{}}(Y:SortS{}))))) [label{}("domain")]
      axiom{R} \implies{R}(\ceil{SortS{},R}(p{}(X:SortC{})),
        \equals{SortC{},R}(inj{SortS{},SortC{}}(p{}(X:SortC{})),\and{SortC{}}(X:SortC{},\top{SortC{}}()))) [simplification{}(),label{}("inverse")]
    endmodule []"#;

    fn load(source: &str) -> BackendDefinition {
        let syntax = k_rust_kore::kore::parser::parse_definition(source).unwrap();
        BackendDefinition::internalize(&syntax, "MAIN").unwrap()
    }

    fn term(definition: &BackendDefinition, text: &str) -> Term {
        definition
            .internalize_term(
                &k_rust_kore::kore::parser::parse_pattern(text).unwrap(),
                &[],
            )
            .unwrap()
    }

    #[test]
    #[ignore = "set SELECTOR_AUDIT_KORE and SELECTOR_AUDIT_MODULE to actual compiler output"]
    fn actual_compiler_selector_contracts_are_recognized() {
        let path = std::env::var("SELECTOR_AUDIT_KORE").unwrap();
        let module = std::env::var("SELECTOR_AUDIT_MODULE").unwrap();
        let source = std::fs::read_to_string(path).unwrap();
        let syntax = k_rust_kore::kore::parser::parse_definition(&source).unwrap();
        let definition = BackendDefinition::internalize(&syntax, &module).unwrap();
        for output in ["SortInt", "SortBool", "SortKItem", "SortK"] {
            assert!(
                definition
                    .selector(&Sort::simple("SortK"), &Sort::simple(output))
                    .is_some(),
                "missing {output}"
            );
        }
    }

    #[test]
    fn complete_source_contract_supplies_exact_domain_and_actual_embedding() {
        let definition = load(SOURCE);
        let selector = definition
            .selector(&Sort::simple("SortC"), &Sort::simple("SortS"))
            .expect("complete contract");
        let input = term(&definition, "X:SortC{}");
        let projection = selector.project(input.clone()).unwrap();
        assert_eq!(
            selector.embed(projection),
            term(&definition, "inj{SortS{},SortC{}}(p{}(X:SortC{}))")
        );
        assert_eq!(
            selector_domain(
                &definition,
                &term(&definition, "p{}(inj{SortS{},SortC{}}(Y:SortS{}))")
            ),
            Some(true)
        );
        assert_eq!(
            selector_domain(&definition, &term(&definition, "p{}(other{}())")),
            Some(false)
        );
        assert_eq!(
            selector_domain(&definition, &term(&definition, "p{}(X:SortC{})")),
            None
        );
        // The exact image at a strict embedding does not erase the embedded operand domain.
        let partial = term(&definition, "partial{}()");
        let strict = term(&definition, "p{}(inj{SortS{},SortC{}}(partial{}()))");
        assert!(
            ceil_term(&definition, &strict)
                .unwrap()
                .contains(&Predicate::Ceil(partial))
        );
    }

    #[test]
    fn singleton_embeddings_and_independent_axiom_binders_are_checked() {
        let wrapped = r#"[] module MAIN
          sort SortS{} [] sort SortItem{} [] sort SortC{} []
          symbol inj{From,To}(From) : To [sortInjection{}()]
          symbol kseq{}(SortItem{},SortC{}) : SortC{} [constructor{}()]
          symbol dotk{}() : SortC{} [constructor{}()]
          symbol p{}(SortC{}) : SortS{} [function{}()]
          axiom{R} \exists{SortItem{}}(X:SortItem{},\equals{SortItem{},SortItem{}}(X:SortItem{},inj{SortS{},SortItem{}}(Y:SortS{}))) [subsort{SortS{},SortItem{}}()]
          axiom{R} \implies{R}(\and{R}(\top{R}(),\and{R}(\in{SortC{},R}(X:SortC{},kseq{}(inj{SortS{},SortItem{}}(Y:SortS{}),dotk{}())),\top{R}())),
            \equals{SortS{},R}(p{}(X:SortC{}),\and{SortS{}}(Y:SortS{},\top{SortS{}}()))) []
          axiom{R} \implies{R}(\top{R}(),\equals{R,R}(\ceil{SortS{},R}(p{}(X:SortC{})),
            \exists{R}(Y:SortS{},\equals{SortC{},R}(X:SortC{},kseq{}(inj{SortS{},SortItem{}}(Y:SortS{}),dotk{}()))))) []
          axiom{R} \implies{R}(\ceil{SortS{},R}(p{}(Z:SortC{})),
            \equals{SortC{},R}(kseq{}(inj{SortS{},SortItem{}}(p{}(Z:SortC{})),dotk{}()),\and{SortC{}}(Z:SortC{},\top{SortC{}}()))) [simplification{}()]
        endmodule []"#;
        let definition = load(wrapped);
        assert!(
            definition
                .selector(&Sort::simple("SortC"), &Sort::simple("SortS"))
                .is_some(),
            "{wrapped}"
        );
        let (prefix, inverse) = SOURCE.rsplit_once("      axiom{R}").unwrap();
        let renamed = format!(
            "{prefix}      axiom{{R}}{}",
            inverse.replace("X:SortC{}", "Z:SortC{}")
        );
        let definition = load(&renamed);
        assert!(
            definition
                .selector(&Sort::simple("SortC"), &Sort::simple("SortS"))
                .is_some()
        );
    }

    #[test]
    fn missing_or_changed_source_cannot_reuse_a_baseline_contract() {
        let baseline = load(SOURCE);
        assert!(
            baseline
                .selector(&Sort::simple("SortC"), &Sort::simple("SortS"))
                .is_some()
        );
        let syntax = k_rust_kore::kore::parser::parse_definition(SOURCE).unwrap();
        for label in ["forward", "domain", "inverse"] {
            let mut changed = syntax.clone();
            changed.modules[0].sentences.retain(|sentence| !matches!(sentence,
                k_rust_kore::kore::ast::Sentence::Axiom { attributes, .. }
                    if attributes.string(k_rust_kore::names::KoreAttribute::Label).unwrap() == Some(label)));
            let definition = BackendDefinition::internalize(&changed, "MAIN").unwrap();
            assert!(
                definition
                    .selector(&Sort::simple("SortC"), &Sort::simple("SortS"))
                    .is_none(),
                "missing {label}"
            );
        }
        let changed = SOURCE.replace(
            "\\and{SortC{}}(X:SortC{},\\top{SortC{}}())",
            "\\and{SortC{}}(other{}(),\\top{SortC{}}())",
        );
        let definition = load(&changed);
        assert!(
            definition
                .selector(&Sort::simple("SortC"), &Sort::simple("SortS"))
                .is_none()
        );
        for changed in [
            SOURCE.replace("\\and{SortS{}}(Y:SortS{},", "\\and{SortS{}}(partial{}(),"),
            SOURCE.replace(
                "p{}(SortC{}) : SortS{} [function{}()]",
                "p{}(SortC{}) : SortS{} [function{}(),impure{}()]",
            ),
            SOURCE.replace(
                "\\equals{SortC{},R}(X:SortC{},inj",
                "\\equals{SortC{},R}(other{}(),inj",
            ),
        ] {
            let definition = load(&changed);
            assert!(
                definition
                    .selector(&Sort::simple("SortC"), &Sort::simple("SortS"))
                    .is_none()
            );
        }
        // The original immutable definition retains its own checked contract.
        assert!(
            baseline
                .selector(&Sort::simple("SortC"), &Sort::simple("SortS"))
                .is_some()
        );
    }
}
