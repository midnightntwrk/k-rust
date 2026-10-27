//! Source-owned map operations and request-owned finite views.
//!
//! Views describe a value on the original map's domain; they do not replace that domain.
//! In particular an explicit entry/rest concatenation can be viewed as overwrite only while
//! retaining its original disjointness and every strict operand. Unknown aliases stay guards.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use crate::{
    builtin::{CollectionOperand, read_collection_item, stored_at},
    definition::BackendDefinition,
    rule::{ClassifiedAxiom, Predicate, TermIndex},
    stop::{self, Stoppable},
    term::{CollectionMetadata, HeadRole, MapDefinition, Sort, Symbol, Term, TermKind},
};

type ChangedRanks = BTreeMap<crate::term::Name, Vec<Option<Vec<Sort>>>>;

#[derive(Clone, Debug)]
pub(crate) struct Operations {
    pub collection: Arc<MapDefinition>,
    symbols: Vec<Arc<Symbol>>,
    changed_ranks: ChangedRanks,
}

impl Operations {
    fn of(definition: &BackendDefinition, sort: Sort) -> Option<Self> {
        if definition.classified_axioms().len() > 16_384 || definition.symbols().len() > 16_384 {
            return None;
        }
        let effects = definition.console_effect_symbols()?;
        definition.equation_selection_complete()?;
        // Offered root-variable rows can affect a hooked instance without naming its head.
        // This small source catalog does not prove their inapplicability or compatibility.
        if [
            definition.function_theory(),
            definition.simplification_theory(),
            definition.ceil_theory(),
        ]
        .into_iter()
        .any(|theory| {
            theory
                .get(&TermIndex::Variable)
                .is_some_and(|groups| groups.values().any(|rows| !rows.is_empty()))
                || theory.contains_key(&TermIndex::And)
        }) {
            return None;
        }
        definition.value_claims().admit_at(
            definition,
            &TermIndex::Map,
            crate::confluence::GateSite::Collection,
        )?;
        let collection = definition.symbols().values().find_map(|symbol| {
            let CollectionMetadata::Map(map) = symbol.attributes.collection.as_ref()? else {
                return None;
            };
            (sort == Sort::simple(map.map_sort.clone())).then(|| map.clone())
        })?;
        let role_names = [
            &collection.symbols.unit,
            &collection.symbols.element,
            &collection.symbols.concat,
        ]
        .into_iter()
        .map(|name| name.as_ref())
        .collect::<BTreeSet<&str>>();
        for name in &role_names {
            let symbol = definition.symbols().get(*name)?;
            if effects.contains(*name)
                || symbol.attributes.binder
                || symbol.attributes.macro_or_alias
                || symbol.attributes.smt.is_some()
            {
                return None;
            }
        }
        let mut changed_heads = BTreeSet::new();
        let mut changed_ranks = ChangedRanks::new();
        let mut role_domains = false;
        for axiom in definition.classified_axioms() {
            let (lhs, domain) = match axiom {
                ClassifiedAxiom::Function { lhs, .. }
                | ClassifiedAxiom::Simplification { lhs, .. } => (lhs, false),
                ClassifiedAxiom::Ceil { lhs, .. } => (lhs, true),
                ClassifiedAxiom::Rewrite { .. } => continue,
            };
            if let k_rust_kore::kore::ast::Pattern::Application { symbol, .. } = lhs {
                if role_names.contains(symbol.name.as_str()) {
                    if !domain {
                        return None;
                    }
                    role_domains = true;
                }
                changed_heads.insert(symbol.name.as_str());
                changed_ranks
                    .entry(symbol.name.as_str().into())
                    .or_default()
                    .push(
                        symbol
                            .sort_parameters
                            .iter()
                            .map(|s| closed_sort(s, 0))
                            .collect(),
                    );
            }
        }
        let symbols = definition
            .symbols()
            .values()
            .filter(|symbol| {
                (symbol.sort_variables.is_empty()
                    || symbol.attributes.hook.as_deref() == Some("KEQUAL.ite"))
                    && matches!(
                        symbol.attributes.head_role(),
                        HeadRole::Function { declared: true, .. }
                    )
                    && !symbol.attributes.binder
                    && (symbol.attributes.hook.as_deref() != Some("MAP.lookup")
                        || symbol.attributes.symbol_type
                            == crate::term::SymbolType::Function(
                                crate::term::FunctionType::Partial,
                            ))
                    && !symbol.attributes.macro_or_alias
                    && (symbol.attributes.smt.is_none()
                        || (symbol.attributes.hook.as_deref() == Some("KEQUAL.ite")
                            && symbol.attributes.smt
                                == Some(crate::smt::SmtType::Hook(crate::smt::SExpr::atom("ite")))))
                    && !effects.contains(symbol.name.as_ref())
                    && (!changed_heads.contains(symbol.name.as_ref())
                        || symbol.attributes.hook.as_deref() == Some("KEQUAL.ite"))
                    && matches!(
                        symbol.attributes.hook.as_deref(),
                        Some(
                            "MAP.lookup"
                                | "MAP.update"
                                | "MAP.remove"
                                | "MAP.in_keys"
                                | "KEQUAL.ite"
                        )
                    )
            })
            .cloned()
            .collect();
        let operations = Self {
            collection,
            symbols,
            changed_ranks,
        };
        if role_domains && !operations.canonical_role_domains(definition) {
            return None;
        }
        Some(operations)
    }

    pub fn sort(&self) -> Sort {
        Sort::simple(self.collection.map_sort.clone())
    }

    /// The compiler emits a concat(entry(K,V),R) ceil row stating absence and the
    /// strict value's domain. Recognize its actual source meaning under defined operands;
    /// an altered domain, restriction or extra unsupported role row declines this view.
    fn canonical_role_domains(&self, definition: &BackendDefinition) -> bool {
        let mut offered = Vec::new();
        let indexes = std::iter::once(TermIndex::Map).chain(
            [
                &self.collection.symbols.unit,
                &self.collection.symbols.element,
                &self.collection.symbols.concat,
            ]
            .into_iter()
            .map(|name| TermIndex::Symbol(name.clone())),
        );
        for index in indexes {
            if let Some(groups) = definition.ceil_theory().get(&index) {
                for rows in groups.values() {
                    if rows.len() > 128 - offered.len() {
                        return false;
                    }
                    offered.extend(rows.iter());
                }
            }
        }
        let mut found = false;
        for row in offered {
            if row.lhs.sort() != self.sort() {
                continue;
            }
            found = true;
            if !super::plain(row) || !row.requires.is_empty() || row.attributes.priority != 50 {
                return false;
            }
            let TermKind::Map {
                definition: map,
                entries,
                rest: Some(rest),
            } = row.lhs.kind()
            else {
                return false;
            };
            if map != &self.collection || entries.len() != 1 {
                return false;
            }
            let (key, value) = entries.iter().next().expect("one entry");
            if [key, value, rest]
                .iter()
                .any(|t| !matches!(t.kind(), TermKind::Variable(_)))
                || key == value
                || key == rest
                || value == rest
            {
                return false;
            }
            let is_member = |term: &Term| {
                let TermKind::Application {
                    symbol, arguments, ..
                } = term.kind()
                else {
                    return false;
                };
                definition.domain_kind(&Sort::builtin(k_rust_kore::names::BuiltinSort::Bool))
                    == Some(crate::term::DomainKind::Bool)
                    && self.admits(term, "MAP.in_keys")
                    && symbol.attributes.symbol_type
                        == crate::term::SymbolType::Function(crate::term::FunctionType::Total)
                    && term
                        .sort()
                        .is_builtin(k_rust_kore::names::BuiltinSort::Bool)
                    && arguments.as_slice() == [key.clone(), rest.clone()]
            };
            let crate::rule::RuleRhs::Predicates(predicates) = &row.rhs else {
                return false;
            };
            if predicates.len() > 256 {
                return false;
            }
            let mut pending = predicates.iter().collect::<Vec<_>>();
            let mut remaining = 256usize;
            let mut absence = false;
            while let Some(predicate) = pending.pop() {
                if remaining == 0 {
                    return false;
                }
                remaining -= 1;
                match predicate {
                    Predicate::True => {}
                    Predicate::And(parts) if parts.len() <= remaining => {
                        pending.extend(parts.iter())
                    }
                    Predicate::Ceil(term) | Predicate::Defined(term)
                        if term == key || term == value || term == rest || is_member(term) => {}
                    Predicate::Equals(a, b)
                        if (is_member(a) && crate::builtin::read_bool(b) == Some(false))
                            || (is_member(b) && crate::builtin::read_bool(a) == Some(false)) =>
                    {
                        absence = true;
                    }
                    Predicate::Not(p) if matches!(p.as_ref(),Predicate::Term(t) if is_member(t)) => {
                        absence = true;
                    }
                    _ => return false,
                }
            }
            if !absence {
                return false;
            }
        }
        found
    }

    pub(crate) fn admits(&self, term: &Term, hook: &str) -> bool {
        let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = term.kind()
        else {
            return false;
        };
        let substitution = symbol
            .sort_variables
            .iter()
            .cloned()
            .zip(sort_arguments.iter().copied())
            .collect();
        sort_arguments.len() == symbol.sort_variables.len()
            && !sort_arguments.iter().any(Sort::has_variable)
            && symbol.attributes.hook.as_deref() == Some(hook)
            && self.symbols.contains(symbol)
            && !self.changed_ranks.get(&symbol.name).is_some_and(|ranks| {
                ranks.iter().any(|rank| {
                    rank.as_ref()
                        .is_none_or(|rank| rank.as_slice() == sort_arguments.as_slice())
                })
            })
            && symbol
                .argument_sorts
                .iter()
                .map(|sort| crate::definition::substitute_sort(sort, &substitution))
                .eq(arguments.iter().map(Term::sort))
    }

    /// Retain the observation's actual source head and key rank at an opaque view leaf.
    pub(super) fn on_base(&self, source: &Term, map: Term) -> Option<Term> {
        let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = source.kind()
        else {
            return None;
        };
        let hook = symbol.attributes.hook.as_deref()?;
        let position = match hook {
            "MAP.lookup" => 0,
            "MAP.in_keys" => 1,
            _ => return None,
        };
        if !self.admits(source, hook) || map.sort() != self.sort() {
            return None;
        }
        let mut arguments = arguments.clone();
        arguments[position] = map;
        Some(Term::application(
            symbol.clone(),
            *sort_arguments,
            arguments,
        ))
    }

    pub fn remove(&self, definition: &BackendDefinition, map: Term, key: &Term) -> Option<Term> {
        self.symbols.iter().find_map(|symbol| {
            let [map_sort, key_sort] = symbol.argument_sorts.as_slice() else {
                return None;
            };
            if symbol.attributes.hook.as_deref() != Some("MAP.remove")
                || *map_sort != self.sort()
                || symbol.result_sort != *map_sort
                || map.sort() != *map_sort
                || symbol.attributes.result_collection.as_ref()
                    != Some(&CollectionMetadata::Map(self.collection.clone()))
            {
                return None;
            }
            let key = read_at(definition, key, key_sort)?;
            Some(Term::application(
                symbol.clone(),
                vec![],
                vec![map.clone(), key],
            ))
        })
    }

    pub fn member(&self, definition: &BackendDefinition, map: Term, key: &Term) -> Option<Term> {
        if definition.domain_kind(&Sort::builtin(k_rust_kore::names::BuiltinSort::Bool))
            != Some(crate::term::DomainKind::Bool)
        {
            return None;
        }
        self.symbols.iter().find_map(|symbol| {
            let [key_sort, map_sort] = symbol.argument_sorts.as_slice() else {
                return None;
            };
            if symbol.attributes.hook.as_deref() != Some("MAP.in_keys")
                || *map_sort != self.sort()
                || !symbol
                    .result_sort
                    .is_builtin(k_rust_kore::names::BuiltinSort::Bool)
                || map.sort() != *map_sort
            {
                return None;
            }
            let key = read_at(definition, key, key_sort)?;
            Some(Term::application(
                symbol.clone(),
                vec![],
                vec![key, map.clone()],
            ))
        })
    }

    pub fn lookup(&self, definition: &BackendDefinition, map: Term, key: &Term) -> Option<Term> {
        self.symbols.iter().find_map(|symbol| {
            let [map_sort, key_sort] = symbol.argument_sorts.as_slice() else {
                return None;
            };
            if symbol.attributes.hook.as_deref() != Some("MAP.lookup")
                || *map_sort != self.sort()
                || map.sort() != *map_sort
                || symbol.result_sort != self.collection.value_sort
            {
                return None;
            }
            let key = read_at(definition, key, key_sort)?;
            Some(Term::application(
                symbol.clone(),
                vec![],
                vec![map.clone(), key],
            ))
        })
    }
}

fn closed_sort(sort: &k_rust_kore::kore::ast::Sort, depth: usize) -> Option<Sort> {
    if depth >= 128 {
        return None;
    }
    match sort {
        k_rust_kore::kore::ast::Sort::Variable(_) => None,
        k_rust_kore::kore::ast::Sort::Application { name, arguments } => Some(Sort::application(
            name.as_str(),
            arguments
                .iter()
                .map(|s| closed_sort(s, depth + 1))
                .collect::<Option<Vec<_>>>()?,
        )),
    }
}

impl BackendDefinition {
    pub(crate) fn map_operations(&self, sort: &Sort) -> Option<&Operations> {
        self.value_claims().admit_at(
            self,
            &TermIndex::Map,
            crate::confluence::GateSite::Collection,
        )?;
        if let Some(operations) = self.map_observations.get() {
            return operations.get(sort);
        }
        // During load, effects and value claims are not ready. Do not cache that absence.
        self.console_effect_symbols()?;
        self.equation_selection_complete()?;
        self.map_observations
            .get_or_init(|| {
                self.symbols()
                    .values()
                    .filter_map(|symbol| {
                        let CollectionMetadata::Map(map) = symbol.attributes.collection.as_ref()?
                        else {
                            return None;
                        };
                        let sort = Sort::simple(map.map_sort.clone());
                        Some(sort)
                    })
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .filter_map(|sort| Some((sort, Operations::of(self, sort)?)))
                    .collect()
            })
            .get(sort)
    }
}

/// Canonical head domain of an actual source lookup. Strict child domains are retained by
/// the existing definedness walk. Offered source ceil/value rows disable this contract.
pub(crate) fn lookup_domain(definition: &BackendDefinition, term: &Term) -> Option<Vec<Predicate>> {
    let TermKind::Application { arguments, .. } = term.kind() else {
        return None;
    };
    let [map, key] = arguments.as_slice() else {
        return None;
    };
    let operations = definition.map_operations(&map.sort())?;
    if !operations.admits(term, "MAP.lookup") || term.sort() != operations.collection.value_sort {
        return None;
    }
    let key = read_at(definition, key, &operations.collection.key_sort)?;
    Some(vec![Predicate::Term(operations.member(
        definition,
        map.clone(),
        &key,
    )?)])
}

pub(super) fn read_at(definition: &BackendDefinition, value: &Term, sort: &Sort) -> Option<Term> {
    match read_collection_item(Some(definition.sort_graph()), value, sort) {
        CollectionOperand::Element(value) => Some(value.into_owned()),
        CollectionOperand::Wider { .. } | CollectionOperand::Unrelated => None,
    }
}

#[derive(Clone, Debug)]
pub(crate) enum View {
    Base(Term),
    Put {
        base: Arc<View>,
        key: Term,
        value: Term,
    },
    Remove {
        base: Arc<View>,
        key: Term,
    },
    If {
        test: Term,
        yes: Arc<View>,
        no: Arc<View>,
    },
}

/// One observation request's source-term DAG. No caller facts or SMT names are retained.
pub(crate) struct Views<'a> {
    definition: &'a BackendDefinition,
    operations: &'a Operations,
    memo: BTreeMap<Term, Arc<View>>,
    remaining: usize,
}

impl<'a> Views<'a> {
    pub fn new(definition: &'a BackendDefinition, operations: &'a Operations) -> Self {
        Self {
            definition,
            operations,
            memo: BTreeMap::new(),
            remaining: 16_384,
        }
    }

    /// The observation builder has already checked the whole operand DAG for purity.
    pub(super) fn of_pure(&mut self, term: &Term) -> Stoppable<Option<Arc<View>>> {
        if let Some(view) = self.memo.get(term) {
            return Ok(Some(view.clone()));
        }
        self.node(term, 0)
    }

    fn node(&mut self, term: &Term, depth: usize) -> Stoppable<Option<Arc<View>>> {
        stop::check()?;
        if term.sort() != self.operations.sort() {
            return Ok(None);
        }
        if let Some(view) = self.memo.get(term) {
            return Ok(Some(view.clone()));
        }
        if self.remaining == 0 || depth >= 128 {
            return Ok(None);
        }
        self.remaining -= 1;
        let view = match term.kind() {
            TermKind::Map {
                definition,
                entries,
                rest,
            } if definition == &self.operations.collection => {
                if entries.len() > self.remaining {
                    return Ok(None);
                }
                self.remaining -= entries.len();
                let mut view = if let Some(rest) = rest {
                    let Some(rest) = self.node(rest, depth + 1)? else {
                        return Ok(None);
                    };
                    rest
                } else {
                    Arc::new(View::Base(Term::map(definition.clone(), vec![], None)))
                };
                for (key, value) in entries {
                    view = Arc::new(View::Put {
                        base: view,
                        key: key.clone(),
                        value: value.clone(),
                    });
                }
                view
            }
            TermKind::Application {
                symbol, arguments, ..
            } if self
                .operations
                .symbols
                .iter()
                .any(|declared| declared == symbol)
                && matches!(
                    symbol.attributes.hook.as_deref(),
                    Some("MAP.update" | "MAP.remove")
                )
                && symbol.attributes.result_collection.as_ref()
                    == Some(&CollectionMetadata::Map(self.operations.collection.clone())) =>
            {
                let (base, key, value) = match arguments.as_slice() {
                    [base, key, value]
                        if symbol.attributes.hook.as_deref() == Some("MAP.update") =>
                    {
                        (base, key, Some(value))
                    }
                    [base, key] if symbol.attributes.hook.as_deref() == Some("MAP.remove") => {
                        (base, key, None)
                    }
                    _ => return Ok(None),
                };
                let Some(base) = self.node(base, depth + 1)? else {
                    return Ok(None);
                };
                if let Some(value) = value {
                    let Some(key) = stored_at(
                        Some(self.definition.sort_graph()),
                        key,
                        &self.operations.collection.key_sort,
                    ) else {
                        return Ok(None);
                    };
                    let Some(value) = stored_at(
                        Some(self.definition.sort_graph()),
                        value,
                        &self.operations.collection.value_sort,
                    ) else {
                        return Ok(None);
                    };
                    Arc::new(View::Put { base, key, value })
                } else {
                    let Some(key) =
                        read_at(self.definition, key, &self.operations.collection.key_sort)
                    else {
                        return Ok(None);
                    };
                    Arc::new(View::Remove { base, key })
                }
            }
            TermKind::Application {
                symbol, arguments, ..
            } if self.operations.admits(term, "KEQUAL.ite") => {
                let [test, yes, no] = arguments.as_slice() else {
                    return Ok(None);
                };
                if !test
                    .sort()
                    .is_builtin(k_rust_kore::names::BuiltinSort::Bool)
                    || self.definition.domain_kind(&test.sort())
                        != Some(crate::term::DomainKind::Bool)
                    || yes.sort() != term.sort()
                    || no.sort() != term.sort()
                {
                    return Ok(None);
                }
                let Some(yes) = self.node(yes, depth + 1)? else {
                    return Ok(None);
                };
                let Some(no) = self.node(no, depth + 1)? else {
                    return Ok(None);
                };
                Arc::new(View::If {
                    test: test.clone(),
                    yes,
                    no,
                })
            }
            _ => Arc::new(View::Base(term.clone())),
        };
        self.memo.insert(term.clone(), view.clone());
        Ok(Some(view))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore = "set MAP_AUDIT_KORE and MAP_AUDIT_MODULE to actual compiler output"]
    fn actual_compiler_map_roles_are_admitted() {
        let source = std::fs::read_to_string(std::env::var("MAP_AUDIT_KORE").unwrap()).unwrap();
        let syntax = k_rust_kore::kore::parser::parse_definition(&source).unwrap();
        let definition =
            BackendDefinition::internalize(&syntax, &std::env::var("MAP_AUDIT_MODULE").unwrap())
                .unwrap();
        let sort = Sort::simple("SortMap");
        assert!(definition.map_operations(&sort).is_some());
    }
}
