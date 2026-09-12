//! Validation and internalization of textual KORE definitions.

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt,
    sync::Arc,
};

use k_rust_kore::kore::ast as kore;

use crate::{
    alias::{AliasDefinition, collect as collect_aliases, expand as expand_aliases},
    claim::{ClaimError, ReachabilityClaim, internalize_reachability_claim},
    matching::SortGraph,
    rewrite::Pattern,
    rule::{
        AxiomError, ClassifiedAxiom, InternalizedRule, PredicateTheory, RuleKind, RulePatternError,
        Theory, classify_axiom, insert_theory, internalize_axiom,
        internalize_model_predicate as internalize_rule_model_predicate,
        internalize_predicate as internalize_rule_predicate, internalize_rule_pattern,
    },
    smt::{SExpr, SmtType},
    term::{
        CollectionMetadata, CollectionSymbols, FunctionType, ListDefinition, MapDefinition, Name,
        Sort, Symbol, SymbolAttributes, SymbolType, Term, TermKind, Variable,
    },
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SortInfo {
    pub parameters: Vec<Name>,
    pub hook: Option<Name>,
    pub has_domain_values: bool,
    collection: Option<CollectionSort>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum CollectionSort {
    Map(CollectionSymbols),
    List(CollectionSymbols),
    Set(CollectionSymbols),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SubsortValidation {
    Check,
    Ignore,
}

/// Transitive strict ordering between overloaded KORE symbols.
///
/// A relation `(greater, lesser)` records that `greater` overloads `lesser`. Symbols which share
/// a strict upper bound may be unified by lifting both applications to a common overload.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct OverloadGraph {
    greater_than: BTreeMap<Name, BTreeSet<Name>>,
    members: BTreeSet<Name>,
}

impl OverloadGraph {
    fn from_relations(
        relations: impl IntoIterator<Item = (Name, Name)>,
    ) -> Result<Self, DefinitionError> {
        let mut pairs = relations.into_iter().collect::<BTreeSet<_>>();
        loop {
            let inferred = pairs
                .iter()
                .flat_map(|(greater, middle)| {
                    pairs
                        .iter()
                        .filter(move |(candidate, _)| candidate == middle)
                        .map(move |(_, lesser)| (greater.clone(), lesser.clone()))
                })
                .collect::<Vec<_>>();
            let previous = pairs.len();
            pairs.extend(inferred);
            if pairs.len() == previous {
                break;
            }
        }
        if let Some((symbol, _)) = pairs.iter().find(|(greater, lesser)| greater == lesser) {
            return Err(DefinitionError::MalformedAttribute(format!(
                "symbol-overload relation contains a cycle through {symbol}"
            )));
        }
        let mut graph = Self::default();
        for (greater, lesser) in pairs {
            graph.members.insert(greater.clone());
            graph.members.insert(lesser.clone());
            graph
                .greater_than
                .entry(greater)
                .or_default()
                .insert(lesser);
        }
        Ok(graph)
    }

    pub fn is_overloaded(&self, symbol: &Name) -> bool {
        self.members.contains(symbol)
    }

    pub fn is_overloading(&self, greater: &Name, lesser: &Name) -> bool {
        self.greater_than
            .get(greater)
            .is_some_and(|lessers| lessers.contains(lesser))
    }

    pub fn common_overloads(&self, left: &Name, right: &Name) -> BTreeSet<Name> {
        self.greater_than
            .iter()
            .filter(|(_, lessers)| lessers.contains(left) && lessers.contains(right))
            .map(|(greater, _)| greater.clone())
            .collect()
    }

    pub fn overloaded_by(&self, greater: &Name) -> BTreeSet<Name> {
        self.greater_than.get(greater).cloned().unwrap_or_default()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PendingAxiom {
    pub module: Name,
    pub parameters: Vec<Name>,
    pub pattern: kore::Pattern,
    pub attributes: kore::Attributes,
}

#[derive(Clone, Debug)]
pub struct BackendDefinition {
    pub main_module: Name,
    pub modules: BTreeSet<Name>,
    pub sorts: BTreeMap<Name, SortInfo>,
    pub symbols: BTreeMap<Name, Arc<Symbol>>,
    aliases: BTreeMap<String, AliasDefinition>,
    pub sort_graph: SortGraph,
    pub overloads: OverloadGraph,
    pub axioms: Vec<PendingAxiom>,
    pub classified_axioms: Vec<ClassifiedAxiom>,
    pub claims: Vec<PendingAxiom>,
    pub reachability_claims: Vec<ReachabilityClaim>,
    pub rewrite_theory: Theory,
    pub function_theory: Theory,
    pub simplification_theory: Theory,
    pub predicate_simplification_theory: PredicateTheory,
    pub ceil_theory: Theory,
    finite_sort_constructors: BTreeMap<Sort, BTreeSet<ConstructorHead>>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum ConstructorHead {
    Symbol {
        name: Name,
        sort_arguments: Vec<Sort>,
    },
    Injection {
        source: Sort,
        target: Sort,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DefinitionError {
    NoSuchModule(String),
    ImportCycle(Vec<String>),
    DuplicateModule(String),
    DuplicateSort(String),
    DuplicateSymbol(String),
    DuplicateAlias(String),
    DuplicateRewriteOrderId(String),
    MissingRewriteOrderIds(Vec<String>),
    DuplicateName {
        name: String,
        first_module: String,
        second_module: String,
    },
    DuplicateParameter(String),
    UnknownSort(String),
    UnknownSymbol(String),
    WrongSortArity {
        sort: String,
        expected: usize,
        actual: usize,
    },
    WrongSortArgumentCount {
        symbol: String,
        expected: usize,
        actual: usize,
    },
    WrongSymbolArity {
        symbol: String,
        expected: usize,
        actual: usize,
    },
    WrongAliasSortArgumentCount {
        alias: String,
        expected: usize,
        actual: usize,
    },
    WrongAliasArity {
        alias: String,
        expected: usize,
        actual: usize,
    },
    IncorrectArgumentSort {
        symbol: String,
        index: usize,
        expected: Sort,
        actual: Sort,
    },
    NotSubsort {
        source: Sort,
        target: Sort,
    },
    InvalidSymbolType(String),
    InvalidSortParameter,
    MalformedAttribute(String),
    MalformedCollection(String),
    MalformedAlias(String),
    AliasCycle(Vec<String>),
    MacroOrAliasInImplication(String),
    PredicateInTermPosition {
        count: usize,
    },
    SortWithoutDomainValues {
        sort: Sort,
    },
    InvalidDomainValue {
        sort: Sort,
        value: String,
    },
    ExpectedTerm(&'static str),
    EmptyAssociativeApplication(String),
    Axiom(AxiomError),
    RulePattern(RulePatternError),
    Claim(ClaimError),
    Verification(crate::verify::VerificationError),
}

impl fmt::Display for DefinitionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoSuchModule(module) => write!(formatter, "Module {module} not found."),
            Self::ImportCycle(modules) => {
                write!(formatter, "Import cycle: {}", modules.join(" -> "))
            }
            Self::DuplicateModule(module) => write!(formatter, "Duplicate module '{module}'"),
            Self::DuplicateSort(sort) => write!(formatter, "Duplicate sort '{sort}'"),
            Self::DuplicateSymbol(symbol) => write!(formatter, "Duplicate symbol '{symbol}'"),
            Self::DuplicateAlias(alias) => write!(formatter, "Duplicate alias '{alias}'"),
            Self::DuplicateRewriteOrderId(unique_id) => {
                write!(formatter, "Duplicate rewrite-order UNIQUE_ID '{unique_id}'")
            }
            Self::MissingRewriteOrderIds(unique_ids) => write!(
                formatter,
                "Rewrite order is missing executable UNIQUE_ID{}: {}",
                if unique_ids.len() == 1 { "" } else { "s" },
                unique_ids.join(", ")
            ),
            Self::DuplicateName { name, .. } => write!(formatter, "Duplicated name: {name}."),
            Self::DuplicateParameter(parameter) => {
                write!(formatter, "Duplicate sort parameter '{parameter}'")
            }
            Self::UnknownSort(sort) => write!(formatter, "Unknown sort '{sort}'"),
            Self::UnknownSymbol(symbol) => write!(formatter, "Unknown symbol '{symbol}'"),
            Self::WrongSortArity {
                sort,
                expected,
                actual,
            } => write!(
                formatter,
                "Sort '{sort}' expected {expected} parameters but got {actual}"
            ),
            Self::WrongSortArgumentCount {
                symbol,
                expected,
                actual,
            } => write!(
                formatter,
                "Symbol '{symbol}' expected {expected} sort arguments but got {actual}"
            ),
            Self::WrongSymbolArity {
                symbol,
                expected,
                actual,
            } => write!(
                formatter,
                "Symbol '{symbol}' expected {expected} arguments but got {actual}"
            ),
            Self::WrongAliasSortArgumentCount {
                alias,
                expected,
                actual,
            } => write!(
                formatter,
                "Alias '{alias}' expected {expected} sort arguments but got {actual}"
            ),
            Self::WrongAliasArity {
                alias,
                expected,
                actual,
            } => write!(
                formatter,
                "Alias '{alias}' expected {expected} arguments but got {actual}"
            ),
            Self::IncorrectArgumentSort {
                symbol,
                index,
                expected,
                actual,
            } => write!(
                formatter,
                "Argument {index} of symbol '{symbol}' expected sort {} but got {}",
                display_sort(expected),
                display_sort(actual)
            ),
            Self::NotSubsort { source, target } => write!(
                formatter,
                "{} is not a subsort of {}",
                display_sort(source),
                display_sort(target)
            ),
            Self::InvalidSymbolType(symbol) => {
                write!(formatter, "Invalid type for symbol '{symbol}'")
            }
            Self::InvalidSortParameter => write!(formatter, "Invalid sort parameter"),
            Self::MalformedAttribute(attribute) => {
                write!(formatter, "Malformed attribute: {attribute}")
            }
            Self::MalformedCollection(error) => {
                write!(formatter, "Malformed collection: {error}")
            }
            Self::MalformedAlias(error) => write!(formatter, "Malformed alias: {error}"),
            Self::AliasCycle(aliases) => {
                write!(formatter, "Alias cycle: {}", aliases.join(" -> "))
            }
            Self::MacroOrAliasInImplication(symbol) => {
                write!(
                    formatter,
                    "A symbol cannot be an alias or a macro: '{symbol}'"
                )
            }
            Self::PredicateInTermPosition { count } => write!(
                formatter,
                "predicate in term position ({count} floated conjuncts) where a term is required"
            ),
            Self::SortWithoutDomainValues { sort } => write!(
                formatter,
                "Sort {} used with a domain value must have the hasDomainValues attribute.",
                display_sort(sort)
            ),
            Self::InvalidDomainValue { sort, value } => {
                write!(
                    formatter,
                    "Invalid domain value {value:?} for sort {}",
                    display_sort(sort)
                )
            }
            Self::ExpectedTerm(pattern) => {
                write!(
                    formatter,
                    "Pattern not supported where a term is required: {pattern}"
                )
            }
            Self::EmptyAssociativeApplication(symbol) => {
                write!(formatter, "Associative symbol '{symbol}' has no arguments")
            }
            Self::Axiom(error) => write!(formatter, "Invalid axiom: {error:?}"),
            Self::RulePattern(error) => write!(formatter, "Invalid rule pattern: {error:?}"),
            Self::Claim(error) => write!(formatter, "Invalid claim: {error:?}"),
            Self::Verification(error) => write!(formatter, "{error}"),
        }
    }
}

fn display_sort(sort: &Sort) -> String {
    match sort {
        Sort::Variable(name) => name.to_string(),
        Sort::Application { name, arguments } => {
            let arguments = arguments.iter().map(display_sort).collect::<Vec<_>>();
            format!("{name}{{{}}}", arguments.join(", "))
        }
    }
}

impl Error for DefinitionError {}

impl BackendDefinition {
    pub fn internalize(
        definition: &kore::Definition,
        main_module: &str,
    ) -> Result<Self, DefinitionError> {
        Self::internalize_canonical(definition, main_module)
    }

    /// Internalizes a definition and orders semantic rewrites by their stable identifiers.
    ///
    /// This is the source-compiled execution boundary: the frontend supplies the order from its
    /// transformed definition before KORE emission structurally sorts the rules. Function,
    /// simplification, predicate, and definedness theories retain canonical KORE order. Every
    /// executable rewrite must have exactly one entry; extra frontend entries are accepted.
    pub fn internalize_for_source_execution<T: AsRef<str>>(
        definition: &kore::Definition,
        main_module: &str,
        rewrite_order: &[T],
    ) -> Result<Self, DefinitionError> {
        let mut result = Self::internalize(definition, main_module)?;
        let mut ranks = BTreeMap::new();
        for (rank, unique_id) in rewrite_order.iter().enumerate() {
            let unique_id = unique_id.as_ref();
            if ranks.insert(unique_id, rank).is_some() {
                return Err(DefinitionError::DuplicateRewriteOrderId(
                    unique_id.to_owned(),
                ));
            }
        }
        let missing = result
            .rewrite_theory
            .values()
            .flat_map(BTreeMap::values)
            .flatten()
            .filter(|rule| !ranks.contains_key(rule.attributes.unique_id.as_str()))
            .map(|rule| rule.attributes.unique_id.clone())
            .collect::<BTreeSet<_>>();
        if !missing.is_empty() {
            return Err(DefinitionError::MissingRewriteOrderIds(
                missing.into_iter().collect(),
            ));
        }
        for priority_groups in result.rewrite_theory.values_mut() {
            for rules in priority_groups.values_mut() {
                rules.sort_by_key(|rule| {
                    ranks
                        .get(rule.attributes.unique_id.as_str())
                        .copied()
                        .expect("all executable rewrites were checked above")
                });
            }
        }
        Ok(result)
    }

    fn internalize_canonical(
        definition: &kore::Definition,
        main_module: &str,
    ) -> Result<Self, DefinitionError> {
        let mut module_map = BTreeMap::new();
        for module in &definition.modules {
            if module_map.insert(module.name.as_str(), module).is_some() {
                return Err(DefinitionError::DuplicateModule(module.name.clone()));
            }
        }

        let mut visiting = Vec::new();
        let mut visited = BTreeSet::new();
        let mut ordered = Vec::new();
        visit_module(
            main_module,
            &module_map,
            &mut visiting,
            &mut visited,
            &mut ordered,
        )?;

        let aliases = collect_aliases(&ordered)?;

        let mut sorts = BTreeMap::new();
        for module in &ordered {
            for sentence in &module.sentences {
                let kore::Sentence::SortDeclaration {
                    name,
                    parameters,
                    attributes,
                    ..
                } = sentence
                else {
                    continue;
                };
                reject_duplicates(parameters)?;
                let collection = collection_sort(attributes)?;
                let info = SortInfo {
                    parameters: parameters.iter().cloned().map(Into::into).collect(),
                    hook: attribute_string(attributes, "hook")?.map(Into::into),
                    has_domain_values: has_attribute(attributes, "hasDomainValues"),
                    collection,
                };
                if sorts.insert(Name::from(name.as_str()), info).is_some() {
                    return Err(DefinitionError::DuplicateSort(name.clone()));
                }
            }
        }
        validate_alias_declarations(&ordered, &sorts)?;

        let mut symbols = BTreeMap::new();
        for module in &ordered {
            for sentence in &module.sentences {
                let kore::Sentence::SymbolDeclaration {
                    symbol,
                    argument_sorts,
                    result_sort,
                    attributes,
                    ..
                } = sentence
                else {
                    continue;
                };
                let sort_variables = symbol
                    .sort_parameters
                    .iter()
                    .map(|sort| match sort {
                        kore::Sort::Variable(name) => Ok(Name::from(name.as_str())),
                        kore::Sort::Application { .. } => {
                            Err(DefinitionError::InvalidSortParameter)
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                reject_name_duplicates(&sort_variables)?;
                let known = sort_variables.iter().cloned().collect();
                let argument_sorts = argument_sorts
                    .iter()
                    .map(|sort| internalize_sort(sort, &sorts, &known))
                    .collect::<Result<Vec<_>, _>>()?;
                let result_sort = internalize_sort(result_sort, &sorts, &known)?;
                let attributes = symbol_attributes(attributes)?;
                validate_binder_attribute(&attributes, &argument_sorts, &sorts)?;
                let internal = Arc::new(Symbol {
                    name: symbol.name.as_str().into(),
                    sort_variables,
                    argument_sorts,
                    result_sort,
                    attributes,
                });
                if symbols
                    .insert(Name::from(symbol.name.as_str()), internal)
                    .is_some()
                {
                    return Err(DefinitionError::DuplicateSymbol(symbol.name.clone()));
                }
            }
        }

        attach_collection_metadata(&sorts, &mut symbols)?;
        crate::verify::verify_definition(
            &ordered,
            &definition.modules,
            &sorts,
            &symbols,
            &aliases,
        )?;

        let mut axioms = Vec::new();
        let mut claims = Vec::new();
        let mut subsorts = Vec::new();
        let mut overloads = Vec::new();
        let rule_orders = ordered
            .iter()
            .map(|module| (module.name.as_str(), sorted_rule_sentence_indices(module)))
            .collect::<BTreeMap<_, _>>();
        let import_orders = ordered
            .iter()
            .map(|module| (module.name.as_str(), sorted_import_sentence_indices(module)))
            .collect::<BTreeMap<_, _>>();
        let mut axiom_modules = Vec::new();
        visit_modules_preorder(main_module, &module_map, &import_orders, &mut axiom_modules)?;
        for module in axiom_modules {
            for &index in &rule_orders[module.name.as_str()] {
                let sentence = &module.sentences[index];
                let (target, parameters, pattern, attributes, expand) = match sentence {
                    kore::Sentence::Axiom {
                        parameters,
                        pattern,
                        attributes,
                    } => (&mut axioms, parameters, pattern, attributes, true),
                    kore::Sentence::Claim {
                        parameters,
                        pattern,
                        attributes,
                    } => (&mut claims, parameters, pattern, attributes, false),
                    _ => continue,
                };
                reject_duplicates(parameters)?;
                if let Some((sub, sup)) = subsort_attribute(pattern, attributes, &sorts)? {
                    subsorts.push((sub, sup));
                }
                if let Some(overload) = overload_attribute(attributes)? {
                    overloads.push(overload);
                }
                target.push(PendingAxiom {
                    module: module.name.as_str().into(),
                    parameters: parameters.iter().cloned().map(Into::into).collect(),
                    pattern: if expand {
                        expand_aliases(pattern, &aliases)?
                    } else {
                        (**pattern).clone()
                    },
                    attributes: attributes.clone(),
                });
            }
        }

        let classified_axioms = axioms
            .iter()
            .filter_map(|axiom| {
                classify_axiom(
                    axiom.module.clone(),
                    axiom.parameters.clone(),
                    &axiom.pattern,
                    &axiom.attributes,
                )
                .transpose()
            })
            .collect::<Result<Vec<_>, _>>()
            .map_err(DefinitionError::Axiom)?;
        let sort_graph = build_sort_graph(sorts.keys().cloned(), subsorts);
        for (greater, lesser) in &overloads {
            if !symbols.contains_key(greater) {
                return Err(DefinitionError::UnknownSymbol(greater.to_string()));
            }
            if !symbols.contains_key(lesser) {
                return Err(DefinitionError::UnknownSymbol(lesser.to_string()));
            }
        }
        let overloads = OverloadGraph::from_relations(overloads)?;
        let mut result = Self {
            main_module: main_module.into(),
            modules: ordered
                .iter()
                .map(|module| Name::from(module.name.as_str()))
                .collect(),
            sorts,
            symbols,
            aliases,
            sort_graph,
            overloads,
            axioms,
            classified_axioms,
            claims,
            reachability_claims: Vec::new(),
            rewrite_theory: Theory::new(),
            function_theory: Theory::new(),
            simplification_theory: Theory::new(),
            predicate_simplification_theory: PredicateTheory::new(),
            ceil_theory: Theory::new(),
            finite_sort_constructors: BTreeMap::new(),
        };
        let rules = result
            .classified_axioms
            .iter()
            .filter(|axiom| match axiom {
                ClassifiedAxiom::Rewrite { attributes, .. }
                | ClassifiedAxiom::Function { attributes, .. }
                | ClassifiedAxiom::Simplification { attributes, .. }
                | ClassifiedAxiom::Ceil { attributes, .. } => attributes.executable,
            })
            .map(|axiom| internalize_axiom(&result, axiom))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten();
        for rule in rules {
            match rule {
                InternalizedRule::Term(kind, rule) => {
                    let theory = match kind {
                        RuleKind::Rewrite => &mut result.rewrite_theory,
                        RuleKind::Function => &mut result.function_theory,
                        RuleKind::Simplification => &mut result.simplification_theory,
                        RuleKind::Ceil => &mut result.ceil_theory,
                    };
                    insert_theory(theory, rule);
                }
                InternalizedRule::Predicate(rule) => {
                    result
                        .predicate_simplification_theory
                        .entry(rule.attributes.priority)
                        .or_default()
                        .push(Arc::new(rule));
                }
            }
        }
        result.reachability_claims = result
            .claims
            .iter()
            .map(|claim| internalize_reachability_claim(&result, claim))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect();
        result.finite_sort_constructors = collect_finite_sort_constructors(&result);
        crate::definedness::discharge_rewrite_definedness(&mut result);
        Ok(result)
    }

    pub(crate) fn finite_constructor_heads(
        &self,
        sort: &Sort,
    ) -> Option<&BTreeSet<ConstructorHead>> {
        self.finite_sort_constructors.get(sort)
    }

    pub fn internalize_term(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
    ) -> Result<Term, DefinitionError> {
        self.internalize_term_with_validation(pattern, sort_variables, SubsortValidation::Check)
    }

    /// Internalize KORE emitted by the paired frontend without rechecking sort injections.
    ///
    /// The frontend can use trusted injection bridges, such as embedding a parsed `SortK` program
    /// in the initializer's `SortKItem` map. Untrusted KORE and RPC inputs should use
    /// [`Self::internalize_term`] so malformed injections are rejected at the boundary.
    pub fn internalize_frontend_term(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
    ) -> Result<Term, DefinitionError> {
        self.internalize_term_with_validation(pattern, sort_variables, SubsortValidation::Ignore)
    }

    pub(crate) fn internalize_term_with_validation(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
        subsort_validation: SubsortValidation,
    ) -> Result<Term, DefinitionError> {
        let mut floated = Vec::new();
        let term = self.internalize_term_collecting(
            pattern,
            sort_variables,
            subsort_validation,
            &mut floated,
        )?;
        if !floated.is_empty() {
            return Err(DefinitionError::PredicateInTermPosition {
                count: floated.len(),
            });
        }
        Ok(term)
    }

    pub(crate) fn internalize_term_collecting(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
        subsort_validation: SubsortValidation,
        floated: &mut Vec<crate::rule::Predicate>,
    ) -> Result<Term, DefinitionError> {
        let known = sort_variables.iter().cloned().collect::<BTreeSet<_>>();
        let pattern = expand_aliases(pattern, &self.aliases)?;
        self.internalize_term_with(&pattern, &known, subsort_validation, floated)
    }

    /// Internalize a constrained KORE pattern into its term and predicate components.
    pub fn internalize_pattern(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
    ) -> Result<Pattern, DefinitionError> {
        let pattern = expand_aliases(pattern, &self.aliases)?;
        let (term, constraints) =
            internalize_rule_pattern(self, &pattern, sort_variables, SubsortValidation::Check)?;
        Ok(Pattern { term, constraints })
    }

    /// Verify a standalone KORE pattern before internalizing a file boundary.
    pub fn verify_standalone_pattern(
        &self,
        pattern: &kore::Pattern,
    ) -> Result<(), DefinitionError> {
        crate::verify::verify_standalone(
            &self.main_module,
            pattern,
            &self.sorts,
            &self.symbols,
            &self.aliases,
        )
        .map_err(DefinitionError::Verification)
    }

    /// Internalize an arbitrary KORE pattern as an ML predicate and retain its result sort.
    pub fn internalize_predicate(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
    ) -> Result<(crate::rule::Predicate, Sort), DefinitionError> {
        let pattern = expand_aliases(pattern, &self.aliases)?;
        let known = sort_variables.iter().cloned().collect::<BTreeSet<_>>();
        let result_sort =
            self.internalize_pattern_result_sort(&pattern, &known, SubsortValidation::Check)?;
        let predicate =
            internalize_rule_predicate(self, &pattern, sort_variables, SubsortValidation::Check)?;
        Ok((predicate, result_sort))
    }

    /// Extract the predicate portion used by the backend get-model operation.
    pub fn internalize_model_predicate(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
    ) -> Result<Option<(crate::rule::Predicate, Sort)>, DefinitionError> {
        let pattern = expand_aliases(pattern, &self.aliases)?;
        let known = sort_variables.iter().cloned().collect::<BTreeSet<_>>();
        let result_sort =
            self.internalize_pattern_result_sort(&pattern, &known, SubsortValidation::Check)?;
        Ok(internalize_rule_model_predicate(
            self,
            &pattern,
            sort_variables,
            SubsortValidation::Check,
        )?
        .map(|predicate| (predicate, result_sort)))
    }

    /// Internalize one side of an implication, peeling its leading existential binders.
    pub fn internalize_implication_pattern(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
    ) -> Result<(Pattern, BTreeSet<Variable>), DefinitionError> {
        self.validate_implication_pattern(pattern)?;
        let pattern = expand_aliases(pattern, &self.aliases)?;
        let mut body = &pattern;
        let mut existentials = BTreeSet::new();
        while let kore::Pattern::Exists {
            variable,
            body: next,
            ..
        } = body
        {
            existentials.insert(self.internalize_variable(variable, sort_variables)?);
            body = next;
        }
        let (term, constraints) =
            internalize_rule_pattern(self, body, sort_variables, SubsortValidation::Check)?;
        Ok((Pattern { term, constraints }, existentials))
    }

    /// Reject syntax that the implication RPC boundary does not permit.
    pub fn validate_implication_pattern(
        &self,
        pattern: &kore::Pattern,
    ) -> Result<(), DefinitionError> {
        if let Some(name) = self.macro_or_alias_in_pattern(pattern) {
            Err(DefinitionError::MacroOrAliasInImplication(name))
        } else {
            Ok(())
        }
    }

    fn macro_or_alias_in_pattern(&self, pattern: &kore::Pattern) -> Option<String> {
        let mut pending = vec![pattern];
        while let Some(pattern) = pending.pop() {
            match pattern {
                kore::Pattern::Application { symbol, arguments }
                | kore::Pattern::AssociativeApplication {
                    symbol, arguments, ..
                } => {
                    if self.aliases.contains_key(&symbol.name)
                        || self
                            .symbols
                            .get(symbol.name.as_str())
                            .is_some_and(|symbol| symbol.attributes.macro_or_alias)
                    {
                        return Some(symbol.name.clone());
                    }
                    pending.extend(arguments.iter().rev());
                }
                kore::Pattern::And { arguments, .. } | kore::Pattern::Or { arguments, .. } => {
                    pending.extend(arguments.iter().rev());
                }
                kore::Pattern::Not { argument, .. }
                | kore::Pattern::Next { argument, .. }
                | kore::Pattern::Ceil { argument, .. }
                | kore::Pattern::Floor { argument, .. } => pending.push(argument),
                kore::Pattern::Implies { left, right, .. }
                | kore::Pattern::Iff { left, right, .. }
                | kore::Pattern::Rewrites { left, right, .. }
                | kore::Pattern::Equals { left, right, .. }
                | kore::Pattern::In { left, right, .. } => {
                    pending.push(right);
                    pending.push(left);
                }
                kore::Pattern::Exists { body, .. }
                | kore::Pattern::Forall { body, .. }
                | kore::Pattern::Mu { body, .. }
                | kore::Pattern::Nu { body, .. } => pending.push(body),
                kore::Pattern::String(_)
                | kore::Pattern::Variable(_)
                | kore::Pattern::Top { .. }
                | kore::Pattern::Bottom { .. }
                | kore::Pattern::DomainValue { .. } => {}
            }
        }
        None
    }

    /// Internalize the alternatives of a top-level KORE disjunction.
    pub fn internalize_disjunction(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
    ) -> Result<Vec<Pattern>, DefinitionError> {
        let pattern = expand_aliases(pattern, &self.aliases)?;
        crate::rule::term_disjuncts(&pattern)
            .into_iter()
            .map(|alternative| {
                let (term, constraints) = internalize_rule_pattern(
                    self,
                    &alternative,
                    sort_variables,
                    SubsortValidation::Check,
                )?;
                Ok(Pattern { term, constraints })
            })
            .collect()
    }

    pub(crate) fn internalize_syntax_sort(
        &self,
        sort: &kore::Sort,
        sort_variables: &[Name],
    ) -> Result<Sort, DefinitionError> {
        let known = sort_variables.iter().cloned().collect::<BTreeSet<_>>();
        internalize_sort(sort, &self.sorts, &known)
    }

    pub(crate) fn internalize_variable(
        &self,
        variable: &kore::Variable,
        sort_variables: &[Name],
    ) -> Result<Variable, DefinitionError> {
        let sort = self.internalize_syntax_sort(&variable.sort, sort_variables)?;
        Ok(match variable.kind {
            kore::VariableKind::Element => Variable::new(variable.name.as_str(), sort),
            kore::VariableKind::Set => Variable::set(variable.name.as_str(), sort),
        })
    }

    fn internalize_term_with(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &BTreeSet<Name>,
        subsort_validation: SubsortValidation,
        floated: &mut Vec<crate::rule::Predicate>,
    ) -> Result<Term, DefinitionError> {
        match pattern {
            kore::Pattern::String(value) => Ok(Term::domain_value(
                Sort::simple("SortString"),
                value.as_str(),
            )),
            kore::Pattern::Variable(variable) => {
                let sort = internalize_sort(&variable.sort, &self.sorts, sort_variables)?;
                let variable = match variable.kind {
                    kore::VariableKind::Element => Variable::new(variable.name.as_str(), sort),
                    kore::VariableKind::Set => Variable::set(variable.name.as_str(), sort),
                };
                Ok(Term::variable(variable))
            }
            kore::Pattern::Application { symbol, arguments } => {
                self.validate_application_shape(symbol, arguments.len())?;
                let arguments = arguments
                    .iter()
                    .map(|argument| {
                        self.internalize_term_with(
                            argument,
                            sort_variables,
                            subsort_validation,
                            floated,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                self.internalize_application(symbol, arguments, sort_variables, subsort_validation)
            }
            kore::Pattern::DomainValue { sort, value } => {
                let sort = internalize_sort(sort, &self.sorts, sort_variables)?;
                self.validate_domain_value(&sort, value)?;
                Ok(Term::domain_value(sort, value.as_str()))
            }
            kore::Pattern::And { arguments, .. } => {
                let (terms, predicates): (Vec<_>, Vec<_>) = arguments
                    .iter()
                    .partition(|argument| crate::rule::contains_term_component(argument));
                let sort_variables = sort_variables.iter().cloned().collect::<Vec<_>>();
                for predicate in predicates {
                    floated.push(internalize_rule_predicate(
                        self,
                        predicate,
                        &sort_variables,
                        subsort_validation,
                    )?);
                }
                let known = sort_variables.iter().cloned().collect::<BTreeSet<_>>();
                let mut arguments = terms
                    .into_iter()
                    .map(|argument| {
                        self.internalize_term_with(argument, &known, subsort_validation, floated)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let Some(mut result) = arguments.pop() else {
                    return Err(DefinitionError::ExpectedTerm("top"));
                };
                while let Some(left) = arguments.pop() {
                    result = Term::and(left, result);
                }
                Ok(result)
            }
            kore::Pattern::AssociativeApplication {
                associativity,
                symbol,
                arguments,
            } => {
                let arguments = arguments
                    .iter()
                    .map(|argument| {
                        self.internalize_term_with(
                            argument,
                            sort_variables,
                            subsort_validation,
                            floated,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let mut iter: Box<dyn Iterator<Item = Term>> = match associativity {
                    kore::Associativity::Left => Box::new(arguments.into_iter()),
                    kore::Associativity::Right => Box::new(arguments.into_iter().rev()),
                };
                let Some(mut result) = iter.next() else {
                    return Err(DefinitionError::EmptyAssociativeApplication(
                        symbol.name.clone(),
                    ));
                };
                for argument in iter {
                    let pair = match associativity {
                        kore::Associativity::Left => vec![result, argument],
                        kore::Associativity::Right => vec![argument, result],
                    };
                    result = self.internalize_application(
                        symbol,
                        pair,
                        sort_variables,
                        subsort_validation,
                    )?;
                }
                Ok(result)
            }
            kore::Pattern::Top { .. } => Err(DefinitionError::ExpectedTerm("top")),
            kore::Pattern::Bottom { .. } => Err(DefinitionError::ExpectedTerm("bottom")),
            kore::Pattern::Or { .. } => Err(DefinitionError::ExpectedTerm("or")),
            kore::Pattern::Not { .. } => Err(DefinitionError::ExpectedTerm("not")),
            kore::Pattern::Next { .. } => Err(DefinitionError::ExpectedTerm("next")),
            kore::Pattern::Implies { .. } => Err(DefinitionError::ExpectedTerm("implies")),
            kore::Pattern::Iff { .. } => Err(DefinitionError::ExpectedTerm("iff")),
            kore::Pattern::Rewrites { .. } => Err(DefinitionError::ExpectedTerm("rewrites")),
            kore::Pattern::Exists { .. } => Err(DefinitionError::ExpectedTerm("exists")),
            kore::Pattern::Forall { .. } => Err(DefinitionError::ExpectedTerm("forall")),
            kore::Pattern::Mu { .. } => Err(DefinitionError::ExpectedTerm("mu")),
            kore::Pattern::Nu { .. } => Err(DefinitionError::ExpectedTerm("nu")),
            kore::Pattern::Ceil { .. } => Err(DefinitionError::ExpectedTerm("ceil")),
            kore::Pattern::Floor { .. } => Err(DefinitionError::ExpectedTerm("floor")),
            kore::Pattern::Equals { .. } => Err(DefinitionError::ExpectedTerm("equals")),
            kore::Pattern::In { .. } => Err(DefinitionError::ExpectedTerm("in")),
        }
    }

    fn validate_domain_value(&self, sort: &Sort, value: &str) -> Result<(), DefinitionError> {
        let Sort::Application { name, .. } = sort else {
            return Err(DefinitionError::SortWithoutDomainValues { sort: sort.clone() });
        };
        let Some(info) = self.sorts.get(name) else {
            return Err(DefinitionError::UnknownSort(name.to_string()));
        };
        if !info.has_domain_values {
            return Err(DefinitionError::SortWithoutDomainValues { sort: sort.clone() });
        }
        if info.hook.as_deref() == Some("BOOL.Bool") && !matches!(value, "true" | "false") {
            return Err(DefinitionError::InvalidDomainValue {
                sort: sort.clone(),
                value: value.into(),
            });
        }
        if info.hook.as_deref() == Some("INT.Int") && !is_decimal_integer(value) {
            return Err(DefinitionError::InvalidDomainValue {
                sort: sort.clone(),
                value: value.into(),
            });
        }
        Ok(())
    }

    fn validate_application_shape(
        &self,
        syntax: &kore::Symbol,
        argument_count: usize,
    ) -> Result<(), DefinitionError> {
        let symbol = self
            .symbols
            .get(syntax.name.as_str())
            .ok_or_else(|| DefinitionError::UnknownSymbol(syntax.name.clone()))?;
        if syntax.sort_parameters.len() != symbol.sort_variables.len() {
            return Err(DefinitionError::WrongSortArgumentCount {
                symbol: syntax.name.clone(),
                expected: symbol.sort_variables.len(),
                actual: syntax.sort_parameters.len(),
            });
        }
        if argument_count != symbol.argument_sorts.len() {
            return Err(DefinitionError::WrongSymbolArity {
                symbol: syntax.name.clone(),
                expected: symbol.argument_sorts.len(),
                actual: argument_count,
            });
        }
        Ok(())
    }

    fn internalize_pattern_result_sort(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &BTreeSet<Name>,
        subsort_validation: SubsortValidation,
    ) -> Result<Sort, DefinitionError> {
        let syntax_sort = match pattern {
            kore::Pattern::Variable(variable) => Some(&variable.sort),
            kore::Pattern::Top { sort }
            | kore::Pattern::Bottom { sort }
            | kore::Pattern::Not { sort, .. }
            | kore::Pattern::Next { sort, .. }
            | kore::Pattern::And { sort, .. }
            | kore::Pattern::Or { sort, .. }
            | kore::Pattern::Rewrites { sort, .. }
            | kore::Pattern::Implies { sort, .. }
            | kore::Pattern::Iff { sort, .. }
            | kore::Pattern::Exists { sort, .. }
            | kore::Pattern::Forall { sort, .. } => Some(sort),
            kore::Pattern::Ceil { result_sort, .. }
            | kore::Pattern::Floor { result_sort, .. }
            | kore::Pattern::Equals { result_sort, .. }
            | kore::Pattern::In { result_sort, .. } => Some(result_sort),
            kore::Pattern::Mu { variable, .. } | kore::Pattern::Nu { variable, .. } => {
                Some(&variable.sort)
            }
            kore::Pattern::DomainValue { sort, .. } => Some(sort),
            kore::Pattern::String(_) => return Ok(Sort::simple("SortString")),
            kore::Pattern::Application { .. } | kore::Pattern::AssociativeApplication { .. } => {
                None
            }
        };
        match syntax_sort {
            Some(sort) => internalize_sort(sort, &self.sorts, sort_variables),
            None => Ok(self
                .internalize_term_with_validation(
                    pattern,
                    &sort_variables.iter().cloned().collect::<Vec<_>>(),
                    subsort_validation,
                )?
                .sort()),
        }
    }

    fn internalize_application(
        &self,
        syntax: &kore::Symbol,
        arguments: Vec<Term>,
        sort_variables: &BTreeSet<Name>,
        subsort_validation: SubsortValidation,
    ) -> Result<Term, DefinitionError> {
        let symbol = self
            .symbols
            .get(syntax.name.as_str())
            .ok_or_else(|| DefinitionError::UnknownSymbol(syntax.name.clone()))?
            .clone();
        if syntax.sort_parameters.len() != symbol.sort_variables.len() {
            return Err(DefinitionError::WrongSortArgumentCount {
                symbol: syntax.name.clone(),
                expected: symbol.sort_variables.len(),
                actual: syntax.sort_parameters.len(),
            });
        }
        if arguments.len() != symbol.argument_sorts.len() {
            return Err(DefinitionError::WrongSymbolArity {
                symbol: syntax.name.clone(),
                expected: symbol.argument_sorts.len(),
                actual: arguments.len(),
            });
        }
        let sort_arguments = syntax
            .sort_parameters
            .iter()
            .map(|sort| internalize_sort(sort, &self.sorts, sort_variables))
            .collect::<Result<Vec<_>, _>>()?;
        let substitution = symbol
            .sort_variables
            .iter()
            .cloned()
            .zip(sort_arguments.iter().cloned())
            .collect::<BTreeMap<_, _>>();
        if subsort_validation == SubsortValidation::Check
            && syntax.name == "inj"
            && let [source, target] = sort_arguments.as_slice()
            && !self
                .sort_graph
                .check_subsort(source, target)
                .unwrap_or(false)
        {
            return Err(DefinitionError::NotSubsort {
                source: source.clone(),
                target: target.clone(),
            });
        }
        // Booster's injection branch records the declared source sort directly and does not run
        // the ordinary symbol-argument sort check. Preserve that boundary behavior as well as its
        // precedence over validation performed by an enclosing application.
        if syntax.name != "inj" {
            for (index, (expected, argument)) in symbol
                .argument_sorts
                .iter()
                .map(|sort| substitute_sort(sort, &substitution))
                .zip(&arguments)
                .enumerate()
            {
                let actual = argument.sort();
                if expected != actual {
                    return Err(DefinitionError::IncorrectArgumentSort {
                        symbol: syntax.name.clone(),
                        index,
                        expected,
                        actual,
                    });
                }
            }
        }
        Ok(Term::application(symbol, sort_arguments, arguments))
    }
}

fn is_decimal_integer(value: &str) -> bool {
    let digits = value.strip_prefix(['+', '-']).unwrap_or(value).as_bytes();
    !digits.is_empty() && digits.iter().all(u8::is_ascii_digit)
}

fn collect_finite_sort_constructors(
    definition: &BackendDefinition,
) -> BTreeMap<Sort, BTreeSet<ConstructorHead>> {
    let mut domains = BTreeMap::new();
    for axiom in &definition.axioms {
        if !has_attribute(&axiom.attributes, "constructor") {
            continue;
        }
        let mut alternatives = Vec::new();
        flatten_or(&axiom.pattern, &mut alternatives);
        if alternatives.len() < 2 {
            continue;
        }
        let mut domain_sort = None;
        let mut constructors = BTreeSet::new();
        let mut has_bottom = false;
        let mut valid = true;
        for alternative in alternatives {
            match alternative {
                kore::Pattern::Bottom { sort } => {
                    let Ok(sort) = definition.internalize_syntax_sort(sort, &axiom.parameters)
                    else {
                        valid = false;
                        break;
                    };
                    has_bottom = true;
                    if domain_sort.get_or_insert_with(|| sort.clone()) != &sort {
                        valid = false;
                        break;
                    }
                }
                alternative => {
                    let mut constructor = alternative;
                    let mut binders = BTreeSet::new();
                    while let kore::Pattern::Exists { variable, body, .. } = constructor {
                        let Ok(sort) =
                            definition.internalize_syntax_sort(&variable.sort, &axiom.parameters)
                        else {
                            valid = false;
                            break;
                        };
                        binders.insert(match variable.kind {
                            kore::VariableKind::Element => {
                                Variable::new(variable.name.as_str(), sort)
                            }
                            kore::VariableKind::Set => Variable::set(variable.name.as_str(), sort),
                        });
                        constructor = body;
                    }
                    if !valid {
                        break;
                    }
                    let Ok(term) = definition.internalize_term_with_validation(
                        constructor,
                        &axiom.parameters,
                        SubsortValidation::Ignore,
                    ) else {
                        valid = false;
                        break;
                    };
                    let Some(head) = constructor_head(&term) else {
                        valid = false;
                        break;
                    };
                    if !term.attributes().variables.is_subset(&binders) {
                        valid = false;
                        break;
                    }
                    let sort = term.sort();
                    if domain_sort.get_or_insert_with(|| sort.clone()) != &sort {
                        valid = false;
                        break;
                    }
                    constructors.insert(head);
                }
            }
        }
        if valid && has_bottom && !constructors.is_empty() {
            domains.insert(
                domain_sort.expect("a nonempty domain has a sort"),
                constructors,
            );
        }
    }
    domains
}

pub(crate) fn constructor_head(term: &Term) -> Option<ConstructorHead> {
    match term.kind() {
        TermKind::Application {
            symbol,
            sort_arguments,
            ..
        } if symbol.attributes.symbol_type == SymbolType::Constructor => {
            Some(ConstructorHead::Symbol {
                name: symbol.name.clone(),
                sort_arguments: sort_arguments.clone(),
            })
        }
        TermKind::Injection { source, target, .. } => Some(ConstructorHead::Injection {
            source: source.clone(),
            target: target.clone(),
        }),
        _ => None,
    }
}

fn flatten_or<'a>(pattern: &'a kore::Pattern, output: &mut Vec<&'a kore::Pattern>) {
    if let kore::Pattern::Or { arguments, .. } = pattern {
        for argument in arguments {
            flatten_or(argument, output);
        }
    } else {
        output.push(pattern);
    }
}

fn validate_alias_declarations(
    modules: &[&kore::Module],
    sorts: &BTreeMap<Name, SortInfo>,
) -> Result<(), DefinitionError> {
    for module in modules {
        for sentence in &module.sentences {
            let kore::Sentence::AliasDeclaration {
                alias,
                argument_sorts,
                result_sort,
                ..
            } = sentence
            else {
                continue;
            };
            let known = alias
                .sort_parameters
                .iter()
                .map(|sort| match sort {
                    kore::Sort::Variable(name) => Ok(Name::from(name.as_str())),
                    kore::Sort::Application { .. } => Err(DefinitionError::InvalidSortParameter),
                })
                .collect::<Result<BTreeSet<_>, _>>()?;
            for sort in argument_sorts.iter().chain([result_sort]) {
                internalize_sort(sort, sorts, &known)?;
            }
        }
    }
    Ok(())
}

fn visit_module<'a>(
    name: &str,
    modules: &BTreeMap<&str, &'a kore::Module>,
    visiting: &mut Vec<String>,
    visited: &mut BTreeSet<String>,
    ordered: &mut Vec<&'a kore::Module>,
) -> Result<(), DefinitionError> {
    if visited.contains(name) {
        return Ok(());
    }
    if let Some(start) = visiting.iter().position(|module| module == name) {
        let mut cycle = visiting[start..].to_vec();
        cycle.push(name.to_owned());
        return Err(DefinitionError::ImportCycle(cycle));
    }
    let module = modules
        .get(name)
        .copied()
        .ok_or_else(|| DefinitionError::NoSuchModule(name.to_owned()))?;
    visiting.push(name.to_owned());
    for sentence in &module.sentences {
        if let kore::Sentence::Import { module, .. } = sentence {
            visit_module(module, modules, visiting, visited, ordered)?;
        }
    }
    visiting.pop();
    visited.insert(name.to_owned());
    ordered.push(module);
    Ok(())
}

fn visit_modules_preorder<'a>(
    name: &str,
    modules: &BTreeMap<&str, &'a kore::Module>,
    import_orders: &BTreeMap<&str, Vec<usize>>,
    ordered: &mut Vec<&'a kore::Module>,
) -> Result<(), DefinitionError> {
    let module = modules
        .get(name)
        .copied()
        .ok_or_else(|| DefinitionError::NoSuchModule(name.to_owned()))?;
    ordered.push(module);
    for &index in &import_orders[name] {
        let kore::Sentence::Import { module: import, .. } = &module.sentences[index] else {
            unreachable!("cached import order contains only import sentences")
        };
        visit_modules_preorder(import, modules, import_orders, ordered)?;
    }
    Ok(())
}

fn sorted_import_sentence_indices(module: &kore::Module) -> Vec<usize> {
    let mut imports = module
        .sentences
        .iter()
        .enumerate()
        .filter_map(|(index, sentence)| match sentence {
            kore::Sentence::Import { module, attributes } => Some((
                index,
                module,
                attributes
                    .0
                    .iter()
                    .map(k_rust_kore::kore::normalize::for_kast)
                    .collect::<Vec<_>>(),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    imports.sort_by(
        |(_, left_module, left_attributes), (_, right_module, right_attributes)| {
            left_module.cmp(right_module).then_with(|| {
                compare_normalized_haskell_pattern_slices(left_attributes, right_attributes)
            })
        },
    );
    imports
        .into_iter()
        .rev()
        .map(|(index, _, _)| index)
        .collect()
}

fn sorted_rule_sentence_indices(module: &kore::Module) -> Vec<usize> {
    let mut rules = module
        .sentences
        .iter()
        .enumerate()
        .filter(|(_, sentence)| {
            matches!(
                sentence,
                kore::Sentence::Axiom { .. } | kore::Sentence::Claim { .. }
            )
        })
        .map(|(index, sentence)| (index, PreparedRuleSentence::new(sentence)))
        .collect::<Vec<_>>();
    rules.sort_by(|(_, left), (_, right)| left.compare(right));
    rules.into_iter().rev().map(|(index, _)| index).collect()
}

#[cfg(test)]
fn compare_rule_sentences(left: &kore::Sentence, right: &kore::Sentence) -> std::cmp::Ordering {
    PreparedRuleSentence::new(left).compare(&PreparedRuleSentence::new(right))
}

struct PreparedRuleSentence<'a> {
    kind: u8,
    parameters: &'a [String],
    pattern: kore::Pattern,
    attributes: Vec<kore::Pattern>,
}

impl<'a> PreparedRuleSentence<'a> {
    fn new(sentence: &'a kore::Sentence) -> Self {
        match sentence {
            kore::Sentence::Axiom {
                parameters,
                pattern,
                attributes,
            } => Self {
                kind: 0,
                parameters,
                pattern: k_rust_kore::kore::normalize::for_kast(pattern),
                attributes: attributes
                    .0
                    .iter()
                    .map(k_rust_kore::kore::normalize::for_kast)
                    .collect(),
            },
            kore::Sentence::Claim {
                parameters,
                pattern,
                attributes,
            } => Self {
                kind: 1,
                parameters,
                pattern: k_rust_kore::kore::normalize::for_kast(pattern),
                attributes: attributes
                    .0
                    .iter()
                    .map(k_rust_kore::kore::normalize::for_kast)
                    .collect(),
            },
            _ => unreachable!("only axioms and claims are sorted as rule sentences"),
        }
    }

    fn compare(&self, other: &Self) -> std::cmp::Ordering {
        self.kind
            .cmp(&other.kind)
            .then_with(|| self.parameters.cmp(other.parameters))
            .then_with(|| compare_normalized_haskell_patterns(&self.pattern, &other.pattern))
            .then_with(|| {
                compare_normalized_haskell_pattern_slices(&self.attributes, &other.attributes)
            })
    }
}

/// Compares parsed patterns as the pinned Haskell `PatternF` derived `Ord` instance does.
///
/// `k-rust-kore`'s public `Pattern::cmp` intentionally follows the Scala backend's ordering,
/// which has a different constructor order and compares domain values alphanumerically.
#[cfg(test)]
fn compare_haskell_patterns(left: &kore::Pattern, right: &kore::Pattern) -> std::cmp::Ordering {
    let left = k_rust_kore::kore::normalize::for_kast(left);
    let right = k_rust_kore::kore::normalize::for_kast(right);
    compare_normalized_haskell_patterns(&left, &right)
}

fn compare_normalized_haskell_patterns(
    left: &kore::Pattern,
    right: &kore::Pattern,
) -> std::cmp::Ordering {
    use kore::Pattern;
    use std::cmp::Ordering;

    fn rank(pattern: &Pattern) -> u8 {
        match pattern {
            Pattern::And { .. } => 0,
            Pattern::Application { .. } => 1,
            Pattern::Bottom { .. } => 2,
            Pattern::Ceil { .. } => 3,
            Pattern::DomainValue { .. } => 4,
            Pattern::Equals { .. } => 5,
            Pattern::Exists { .. } => 6,
            Pattern::Floor { .. } => 7,
            Pattern::Forall { .. } => 8,
            Pattern::Iff { .. } => 9,
            Pattern::Implies { .. } => 10,
            Pattern::In { .. } => 11,
            Pattern::Mu { .. } => 12,
            Pattern::Next { .. } => 13,
            Pattern::Not { .. } => 14,
            Pattern::Nu { .. } => 15,
            Pattern::Or { .. } => 16,
            Pattern::Rewrites { .. } => 17,
            Pattern::Top { .. } => 18,
            Pattern::String(_) => 20,
            Pattern::Variable(_) => 21,
            Pattern::AssociativeApplication { .. } => {
                unreachable!("associative applications were normalized above")
            }
        }
    }

    fn variable_name(name: &str) -> (&str, Option<&str>) {
        let suffix_start = name
            .char_indices()
            .rev()
            .find_map(|(index, character)| {
                (!character.is_ascii_digit()).then_some(index + character.len_utf8())
            })
            .unwrap_or(0);
        let suffix = &name[suffix_start..];
        if suffix.is_empty() {
            return (name, None);
        }
        let nonzero = suffix.find(|character| character != '0');
        match nonzero {
            None => (&name[..name.len() - 1], Some("0")),
            Some(index) => (&name[..suffix_start + index], Some(&suffix[index..])),
        }
    }

    fn compare_variable_names(left: &str, right: &str) -> Ordering {
        let (left_base, left_counter) = variable_name(left);
        let (right_base, right_counter) = variable_name(right);
        left_base
            .cmp(right_base)
            .then_with(|| match (left_counter, right_counter) {
                (None, None) => Ordering::Equal,
                (None, Some(_)) => Ordering::Less,
                (Some(_), None) => Ordering::Greater,
                (Some(left), Some(right)) => {
                    left.len().cmp(&right.len()).then_with(|| left.cmp(right))
                }
            })
    }

    fn compare_variables(left: &kore::Variable, right: &kore::Variable) -> Ordering {
        left.kind
            .cmp(&right.kind)
            .then_with(|| compare_variable_names(&left.name, &right.name))
            .then_with(|| left.sort.cmp(&right.sort))
    }

    fn scalars(left: &Pattern, right: &Pattern) -> Ordering {
        match (left, right) {
            (Pattern::And { sort: left, .. }, Pattern::And { sort: right, .. })
            | (Pattern::Or { sort: left, .. }, Pattern::Or { sort: right, .. })
            | (Pattern::Bottom { sort: left }, Pattern::Bottom { sort: right })
            | (Pattern::Top { sort: left }, Pattern::Top { sort: right }) => left.cmp(right),
            (
                Pattern::Application { symbol: left, .. },
                Pattern::Application { symbol: right, .. },
            ) => left.cmp(right),
            (
                Pattern::Ceil {
                    operand_sort: left_operand,
                    result_sort: left_result,
                    ..
                },
                Pattern::Ceil {
                    operand_sort: right_operand,
                    result_sort: right_result,
                    ..
                },
            )
            | (
                Pattern::Floor {
                    operand_sort: left_operand,
                    result_sort: left_result,
                    ..
                },
                Pattern::Floor {
                    operand_sort: right_operand,
                    result_sort: right_result,
                    ..
                },
            )
            | (
                Pattern::Equals {
                    operand_sort: left_operand,
                    result_sort: left_result,
                    ..
                },
                Pattern::Equals {
                    operand_sort: right_operand,
                    result_sort: right_result,
                    ..
                },
            )
            | (
                Pattern::In {
                    operand_sort: left_operand,
                    result_sort: left_result,
                    ..
                },
                Pattern::In {
                    operand_sort: right_operand,
                    result_sort: right_result,
                    ..
                },
            ) => left_operand
                .cmp(right_operand)
                .then_with(|| left_result.cmp(right_result)),
            (
                Pattern::DomainValue {
                    sort: left_sort,
                    value: left_value,
                },
                Pattern::DomainValue {
                    sort: right_sort,
                    value: right_value,
                },
            ) => left_sort
                .cmp(right_sort)
                .then_with(|| left_value.cmp(right_value)),
            (
                Pattern::Exists {
                    sort: left_sort,
                    variable: left_variable,
                    ..
                },
                Pattern::Exists {
                    sort: right_sort,
                    variable: right_variable,
                    ..
                },
            )
            | (
                Pattern::Forall {
                    sort: left_sort,
                    variable: left_variable,
                    ..
                },
                Pattern::Forall {
                    sort: right_sort,
                    variable: right_variable,
                    ..
                },
            ) => left_sort
                .cmp(right_sort)
                .then_with(|| compare_variables(left_variable, right_variable)),
            (Pattern::Iff { sort: left, .. }, Pattern::Iff { sort: right, .. })
            | (Pattern::Implies { sort: left, .. }, Pattern::Implies { sort: right, .. })
            | (Pattern::Next { sort: left, .. }, Pattern::Next { sort: right, .. })
            | (Pattern::Not { sort: left, .. }, Pattern::Not { sort: right, .. })
            | (Pattern::Rewrites { sort: left, .. }, Pattern::Rewrites { sort: right, .. }) => {
                left.cmp(right)
            }
            (
                Pattern::Mu { variable: left, .. },
                Pattern::Mu {
                    variable: right, ..
                },
            )
            | (
                Pattern::Nu { variable: left, .. },
                Pattern::Nu {
                    variable: right, ..
                },
            ) => compare_variables(left, right),
            (Pattern::String(left), Pattern::String(right)) => left.cmp(right),
            (Pattern::Variable(left), Pattern::Variable(right)) => compare_variables(left, right),
            _ => Ordering::Equal,
        }
    }

    enum Step<'a> {
        Compare(&'a Pattern, &'a Pattern),
        PrefixLength(Ordering),
    }

    let mut work = vec![Step::Compare(left, right)];
    while let Some(step) = work.pop() {
        let Step::Compare(left, right) = step else {
            let Step::PrefixLength(ordering) = step else {
                unreachable!()
            };
            if !ordering.is_eq() {
                return ordering;
            }
            continue;
        };
        let ordering = rank(left)
            .cmp(&rank(right))
            .then_with(|| scalars(left, right));
        if !ordering.is_eq() {
            return ordering;
        }
        match (left, right) {
            (
                Pattern::Application {
                    arguments: left, ..
                }
                | Pattern::And {
                    arguments: left, ..
                }
                | Pattern::Or {
                    arguments: left, ..
                },
                Pattern::Application {
                    arguments: right, ..
                }
                | Pattern::And {
                    arguments: right, ..
                }
                | Pattern::Or {
                    arguments: right, ..
                },
            ) => {
                let common = left.len().min(right.len());
                work.push(Step::PrefixLength(left.len().cmp(&right.len())));
                for index in (0..common).rev() {
                    work.push(Step::Compare(&left[index], &right[index]));
                }
            }
            (
                Pattern::Not { argument: left, .. }
                | Pattern::Next { argument: left, .. }
                | Pattern::Ceil { argument: left, .. }
                | Pattern::Floor { argument: left, .. },
                Pattern::Not {
                    argument: right, ..
                }
                | Pattern::Next {
                    argument: right, ..
                }
                | Pattern::Ceil {
                    argument: right, ..
                }
                | Pattern::Floor {
                    argument: right, ..
                },
            ) => work.push(Step::Compare(left, right)),
            (
                Pattern::Implies {
                    left: left_a,
                    right: left_b,
                    ..
                }
                | Pattern::Iff {
                    left: left_a,
                    right: left_b,
                    ..
                }
                | Pattern::Rewrites {
                    left: left_a,
                    right: left_b,
                    ..
                }
                | Pattern::Equals {
                    left: left_a,
                    right: left_b,
                    ..
                }
                | Pattern::In {
                    left: left_a,
                    right: left_b,
                    ..
                },
                Pattern::Implies {
                    left: right_a,
                    right: right_b,
                    ..
                }
                | Pattern::Iff {
                    left: right_a,
                    right: right_b,
                    ..
                }
                | Pattern::Rewrites {
                    left: right_a,
                    right: right_b,
                    ..
                }
                | Pattern::Equals {
                    left: right_a,
                    right: right_b,
                    ..
                }
                | Pattern::In {
                    left: right_a,
                    right: right_b,
                    ..
                },
            ) => {
                work.push(Step::Compare(left_b, right_b));
                work.push(Step::Compare(left_a, right_a));
            }
            (
                Pattern::Exists { body: left, .. }
                | Pattern::Forall { body: left, .. }
                | Pattern::Mu { body: left, .. }
                | Pattern::Nu { body: left, .. },
                Pattern::Exists { body: right, .. }
                | Pattern::Forall { body: right, .. }
                | Pattern::Mu { body: right, .. }
                | Pattern::Nu { body: right, .. },
            ) => work.push(Step::Compare(left, right)),
            (Pattern::AssociativeApplication { .. }, _)
            | (_, Pattern::AssociativeApplication { .. }) => {
                unreachable!("associative applications were normalized above")
            }
            _ => {}
        }
    }
    Ordering::Equal
}

fn compare_normalized_haskell_pattern_slices(
    left: &[kore::Pattern],
    right: &[kore::Pattern],
) -> std::cmp::Ordering {
    for (left, right) in left.iter().zip(right) {
        let ordering = compare_normalized_haskell_patterns(left, right);
        if !ordering.is_eq() {
            return ordering;
        }
    }
    left.len().cmp(&right.len())
}

pub(crate) fn internalize_sort(
    sort: &kore::Sort,
    sorts: &BTreeMap<Name, SortInfo>,
    variables: &BTreeSet<Name>,
) -> Result<Sort, DefinitionError> {
    match sort {
        kore::Sort::Variable(name) if variables.contains(name.as_str()) => {
            Ok(Sort::Variable(name.as_str().into()))
        }
        kore::Sort::Variable(name) => Err(DefinitionError::UnknownSort(name.clone())),
        kore::Sort::Application { name, arguments } => {
            let info = sorts
                .get(name.as_str())
                .ok_or_else(|| DefinitionError::UnknownSort(name.clone()))?;
            if arguments.len() != info.parameters.len() {
                return Err(DefinitionError::WrongSortArity {
                    sort: name.clone(),
                    expected: info.parameters.len(),
                    actual: arguments.len(),
                });
            }
            Ok(Sort::application(
                name.as_str(),
                arguments
                    .iter()
                    .map(|sort| internalize_sort(sort, sorts, variables))
                    .collect::<Result<Vec<_>, _>>()?,
            ))
        }
    }
}

pub(crate) fn substitute_sort(sort: &Sort, substitution: &BTreeMap<Name, Sort>) -> Sort {
    match sort {
        Sort::Variable(name) => substitution
            .get(name)
            .cloned()
            .unwrap_or_else(|| sort.clone()),
        Sort::Application { name, arguments } => Sort::application(
            name.clone(),
            arguments
                .iter()
                .map(|argument| substitute_sort(argument, substitution))
                .collect(),
        ),
    }
}

fn symbol_attributes(attributes: &kore::Attributes) -> Result<SymbolAttributes, DefinitionError> {
    let constructor =
        has_attribute(attributes, "constructor") || has_attribute(attributes, "sortInjection");
    let total = has_attribute(attributes, "total") || has_attribute(attributes, "functional");
    let function = has_attribute(attributes, "function");
    let symbol_type = if constructor {
        SymbolType::Constructor
    } else if total {
        SymbolType::Function(FunctionType::Total)
    } else if function {
        SymbolType::Function(FunctionType::Partial)
    } else {
        return Err(DefinitionError::InvalidSymbolType(format!(
            "attributes {attributes:?}"
        )));
    };
    if has_attribute(attributes, "sortInjection")
        && (has_attribute(attributes, "assoc") || has_attribute(attributes, "idem"))
    {
        return Err(DefinitionError::MalformedAttribute(
            "sort injections cannot be associative or idempotent".into(),
        ));
    }
    let smt_hook = attribute_string(attributes, "smt-hook")?;
    let smtlib = attribute_string(attributes, "smtlib")?;
    let smt = if let Some(hook) = smt_hook {
        Some(SmtType::Hook(SExpr::parse(&hook).map_err(|error| {
            DefinitionError::MalformedAttribute(format!("invalid smt-hook {hook:?}: {error}"))
        })?))
    } else {
        smtlib.map(SmtType::Lib)
    };
    Ok(SymbolAttributes {
        symbol_type,
        binder: has_attribute(attributes, "binder"),
        injective: has_attribute(attributes, "injective"),
        associative: has_attribute(attributes, "assoc"),
        idempotent: has_attribute(attributes, "idem"),
        macro_or_alias: has_attribute(attributes, "macro")
            || has_attribute(attributes, "alias'Kywd'"),
        has_evaluators: !has_attribute(attributes, "no-evaluators"),
        smt,
        hook: attribute_string(attributes, "hook")?.map(Into::into),
        collection: None,
    })
}

fn validate_binder_attribute(
    attributes: &SymbolAttributes,
    argument_sorts: &[Sort],
    sorts: &BTreeMap<Name, SortInfo>,
) -> Result<(), DefinitionError> {
    if !attributes.binder {
        return Ok(());
    }
    if argument_sorts.len() < 2 {
        return Err(DefinitionError::MalformedAttribute(
            "Binder productions must have at least two nonterminals.".into(),
        ));
    }
    let Sort::Application { name, .. } = &argument_sorts[0] else {
        return Err(DefinitionError::MalformedAttribute(
            "First child of binder must have a sort with the 'KVAR.KVar' hook attribute.".into(),
        ));
    };
    if sorts.get(name).and_then(|info| info.hook.as_deref()) != Some("KVAR.KVar") {
        return Err(DefinitionError::MalformedAttribute(
            "First child of binder must have a sort with the 'KVAR.KVar' hook attribute.".into(),
        ));
    }
    Ok(())
}

fn collection_sort(
    attributes: &kore::Attributes,
) -> Result<Option<CollectionSort>, DefinitionError> {
    let element = attribute_symbol(attributes, "element")?;
    let concat = attribute_symbol(attributes, "concat")?;
    let unit = attribute_symbol(attributes, "unit")?;
    let hook = attribute_string(attributes, "hook")?;
    match (element, concat, unit, hook.as_deref()) {
        (None, None, None, _) => Ok(None),
        (Some(element), Some(concat), Some(unit), Some(hook)) => {
            let symbols = CollectionSymbols {
                unit: unit.into(),
                element: element.into(),
                concat: concat.into(),
            };
            match hook {
                "MAP.Map" => Ok(Some(CollectionSort::Map(symbols))),
                "LIST.List" => Ok(Some(CollectionSort::List(symbols))),
                "SET.Set" => Ok(Some(CollectionSort::Set(symbols))),
                _ => Ok(None),
            }
        }
        _ => Err(DefinitionError::MalformedCollection(
            "collection sorts require unit, element, concat, and a collection hook".into(),
        )),
    }
}

fn attach_collection_metadata(
    sorts: &BTreeMap<Name, SortInfo>,
    symbols: &mut BTreeMap<Name, Arc<Symbol>>,
) -> Result<(), DefinitionError> {
    let mut metadata = BTreeMap::new();
    for (sort_name, info) in sorts {
        let Some(collection) = &info.collection else {
            continue;
        };
        let (names, collection) = match collection {
            CollectionSort::Map(names) => {
                let element = symbols.get(&names.element).ok_or_else(|| {
                    DefinitionError::MalformedCollection(format!(
                        "missing map element symbol {}",
                        names.element
                    ))
                })?;
                let [
                    Sort::Application {
                        name: key_sort,
                        arguments: key_arguments,
                    },
                    Sort::Application {
                        name: value_sort,
                        arguments: value_arguments,
                    },
                ] = element.argument_sorts.as_slice()
                else {
                    return Err(DefinitionError::MalformedCollection(format!(
                        "map element symbol {} must take key and value sorts",
                        names.element
                    )));
                };
                if !key_arguments.is_empty() || !value_arguments.is_empty() {
                    return Err(DefinitionError::MalformedCollection(
                        "parametric map element sorts are unsupported by the reference backend"
                            .into(),
                    ));
                }
                let definition = Arc::new(MapDefinition {
                    symbols: names.clone(),
                    key_sort: key_sort.clone(),
                    value_sort: value_sort.clone(),
                    map_sort: sort_name.clone(),
                });
                (names, CollectionMetadata::Map(definition))
            }
            CollectionSort::List(names) | CollectionSort::Set(names) => {
                let element = symbols.get(&names.element).ok_or_else(|| {
                    DefinitionError::MalformedCollection(format!(
                        "missing collection element symbol {}",
                        names.element
                    ))
                })?;
                let [
                    Sort::Application {
                        name: element_sort,
                        arguments,
                    },
                ] = element.argument_sorts.as_slice()
                else {
                    return Err(DefinitionError::MalformedCollection(format!(
                        "collection element symbol {} must take one sort",
                        names.element
                    )));
                };
                if !arguments.is_empty() {
                    return Err(DefinitionError::MalformedCollection(
                        "parametric collection element sorts are unsupported by the reference backend"
                            .into(),
                    ));
                }
                let definition = Arc::new(ListDefinition {
                    symbols: names.clone(),
                    element_sort: element_sort.clone(),
                    list_sort: sort_name.clone(),
                });
                let collection = match collection {
                    CollectionSort::List(_) => CollectionMetadata::List(definition),
                    CollectionSort::Set(_) => CollectionMetadata::Set(definition),
                    CollectionSort::Map(_) => unreachable!(),
                };
                (names, collection)
            }
        };
        for name in [&names.unit, &names.element, &names.concat] {
            if metadata.insert(name.clone(), collection.clone()).is_some() {
                return Err(DefinitionError::MalformedCollection(format!(
                    "symbol {name} belongs to multiple collections"
                )));
            }
        }
    }
    for (name, collection) in metadata {
        let symbol = symbols.get_mut(&name).ok_or_else(|| {
            DefinitionError::MalformedCollection(format!("missing collection symbol {name}"))
        })?;
        Arc::make_mut(symbol).attributes.collection = Some(collection);
    }
    Ok(())
}

fn build_sort_graph(names: impl IntoIterator<Item = Name>, pairs: Vec<(Name, Name)>) -> SortGraph {
    let names = names.into_iter().collect::<Vec<_>>();
    let mut closure = names
        .iter()
        .cloned()
        .map(|name| (name.clone(), BTreeSet::from([name])))
        .collect::<BTreeMap<_, _>>();
    for (sub, sup) in pairs {
        closure.entry(sup).or_default().insert(sub);
    }
    loop {
        let previous = closure.clone();
        for subsorts in closure.values_mut() {
            let descendants = subsorts
                .iter()
                .filter_map(|sort| previous.get(sort))
                .flatten()
                .cloned()
                .collect::<Vec<_>>();
            subsorts.extend(descendants);
        }
        if closure == previous {
            break;
        }
    }
    let mut graph = SortGraph::default();
    for name in names {
        graph.insert(name.clone(), closure.remove(&name).unwrap_or_default());
    }
    graph
}

fn subsort_attribute(
    pattern: &kore::Pattern,
    attributes: &kore::Attributes,
    sorts: &BTreeMap<Name, SortInfo>,
) -> Result<Option<(Name, Name)>, DefinitionError> {
    let Some(attribute_pattern) = attribute(attributes, "subsort") else {
        return Ok(None);
    };
    let kore::Pattern::Application { symbol, arguments } = attribute_pattern else {
        unreachable!()
    };
    if !arguments.is_empty() || symbol.sort_parameters.len() != 2 {
        return Err(DefinitionError::MalformedAttribute(
            "subsort must have two sort parameters and no arguments".into(),
        ));
    }
    let known = BTreeSet::new();
    let sub = internalize_sort(&symbol.sort_parameters[0], sorts, &known)?;
    let sup = internalize_sort(&symbol.sort_parameters[1], sorts, &known)?;
    let kore::Pattern::Exists { variable, body, .. } = pattern else {
        return Err(DefinitionError::MalformedAttribute(
            "subsort attribute must annotate the generated existential axiom".into(),
        ));
    };
    let kore::Pattern::Equals { left, right, .. } = body.as_ref() else {
        return Err(DefinitionError::MalformedAttribute(
            "subsort existential must contain an equality".into(),
        ));
    };
    let kore::Pattern::Variable(left_variable) = left.as_ref() else {
        return Err(DefinitionError::MalformedAttribute(
            "subsort equality must bind its existential variable".into(),
        ));
    };
    let kore::Pattern::Application {
        symbol: injection,
        arguments,
    } = right.as_ref()
    else {
        return Err(DefinitionError::MalformedAttribute(
            "subsort equality must contain an injection".into(),
        ));
    };
    if left_variable != variable
        || injection.name != "inj"
        || injection.sort_parameters.as_slice()
            != [
                symbol.sort_parameters[0].clone(),
                symbol.sort_parameters[1].clone(),
            ]
        || !matches!(arguments.as_slice(), [kore::Pattern::Variable(inner)] if inner.sort == symbol.sort_parameters[0])
        || variable.sort != symbol.sort_parameters[1]
    {
        return Err(DefinitionError::MalformedAttribute(
            "subsort axiom does not agree with its sub- and supersort parameters".into(),
        ));
    }
    match (sub, sup) {
        (
            Sort::Application {
                name: sub,
                arguments: _,
            },
            Sort::Application {
                name: sup,
                arguments: _,
            },
        ) => Ok(Some((sub, sup))),
        _ => Err(DefinitionError::MalformedAttribute(
            "subsort arguments must be concrete sorts".into(),
        )),
    }
}

fn attribute<'a>(attributes: &'a kore::Attributes, name: &str) -> Option<&'a kore::Pattern> {
    attributes.0.iter().find(|pattern| {
        matches!(pattern, kore::Pattern::Application { symbol, .. } if symbol.name == name)
    })
}

fn has_attribute(attributes: &kore::Attributes, name: &str) -> bool {
    attribute(attributes, name).is_some()
}

fn attribute_string(
    attributes: &kore::Attributes,
    name: &str,
) -> Result<Option<String>, DefinitionError> {
    let Some(pattern) = attribute(attributes, name) else {
        return Ok(None);
    };
    let kore::Pattern::Application { arguments, .. } = pattern else {
        unreachable!()
    };
    match arguments.as_slice() {
        [kore::Pattern::String(value)] => Ok(Some(value.clone())),
        _ => Err(DefinitionError::MalformedAttribute(format!(
            "{name} must contain one string"
        ))),
    }
}

fn attribute_symbol(
    attributes: &kore::Attributes,
    name: &str,
) -> Result<Option<String>, DefinitionError> {
    let Some(pattern) = attribute(attributes, name) else {
        return Ok(None);
    };
    let kore::Pattern::Application { arguments, .. } = pattern else {
        unreachable!()
    };
    match arguments.as_slice() {
        [kore::Pattern::Application { symbol, arguments }] if arguments.is_empty() => {
            Ok(Some(symbol.name.clone()))
        }
        _ => Err(DefinitionError::MalformedAttribute(format!(
            "{name} must contain one nullary symbol"
        ))),
    }
}

fn overload_attribute(
    attributes: &kore::Attributes,
) -> Result<Option<(Name, Name)>, DefinitionError> {
    let Some(pattern) =
        attribute(attributes, "symbol-overload").or_else(|| attribute(attributes, "overload"))
    else {
        return Ok(None);
    };
    let kore::Pattern::Application { arguments, .. } = pattern else {
        unreachable!()
    };
    let [
        kore::Pattern::Application {
            symbol: greater,
            arguments: greater_arguments,
        },
        kore::Pattern::Application {
            symbol: lesser,
            arguments: lesser_arguments,
        },
    ] = arguments.as_slice()
    else {
        return Err(DefinitionError::MalformedAttribute(
            "symbol-overload must contain two nullary symbols".into(),
        ));
    };
    if !greater_arguments.is_empty() || !lesser_arguments.is_empty() {
        return Err(DefinitionError::MalformedAttribute(
            "symbol-overload must contain two nullary symbols".into(),
        ));
    }
    Ok(Some((
        greater.name.as_str().into(),
        lesser.name.as_str().into(),
    )))
}

fn reject_duplicates(parameters: &[String]) -> Result<(), DefinitionError> {
    let mut seen = BTreeSet::new();
    for parameter in parameters {
        if !seen.insert(parameter) {
            return Err(DefinitionError::DuplicateParameter(parameter.clone()));
        }
    }
    Ok(())
}

fn reject_name_duplicates(parameters: &[Name]) -> Result<(), DefinitionError> {
    let mut seen = BTreeSet::new();
    for parameter in parameters {
        if !seen.insert(parameter) {
            return Err(DefinitionError::DuplicateParameter(parameter.to_string()));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use indoc::indoc;
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};
    use std::cmp::Ordering;

    use crate::term::TermKind;

    use super::*;

    #[test]
    fn retains_valid_binder_attribute() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                hooked-sort SortKVar{} [hook{}("KVAR.KVar"), hasDomainValues{}()]
                sort SortExp{} []
                symbol lambda{}(SortKVar{}, SortExp{}) : SortExp{}
                    [constructor{}(), binder{}()]
                symbol apply{}(SortExp{}, SortExp{}) : SortExp{} [constructor{}()]
            endmodule []
        "#})
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");

        assert!(definition.symbols["lambda"].attributes.binder);
        assert!(!definition.symbols["apply"].attributes.binder);
    }

    #[test]
    fn retains_three_argument_binder_attribute() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                hooked-sort SortKVar{} [hook{}("KVAR.KVar"), hasDomainValues{}()]
                sort SortExp{} []
                symbol letWithAnnotation{}(SortKVar{}, SortExp{}, SortExp{}) : SortExp{}
                    [constructor{}(), binder{}()]
            endmodule []
        "#})
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");

        assert!(definition.symbols["letWithAnnotation"].attributes.binder);
    }

    #[test]
    fn rejects_unary_binder_attribute() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                hooked-sort SortKVar{} [hook{}("KVAR.KVar"), hasDomainValues{}()]
                sort SortExp{} []
                symbol malformed{}(SortKVar{}) : SortExp{} [constructor{}(), binder{}()]
            endmodule []
        "#})
        .expect("definition should parse");

        assert!(matches!(
            BackendDefinition::internalize(&syntax, "MAIN"),
            Err(DefinitionError::MalformedAttribute(message))
                if message == "Binder productions must have at least two nonterminals."
        ));
    }

    #[test]
    fn rejects_binder_attribute_without_kvar_hook() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortExp{} []
                symbol malformed{}(SortExp{}, SortExp{}) : SortExp{}
                    [constructor{}(), binder{}()]
            endmodule []
        "#})
        .expect("definition should parse");

        assert!(matches!(
            BackendDefinition::internalize(&syntax, "MAIN"),
            Err(DefinitionError::MalformedAttribute(message))
                if message == "First child of binder must have a sort with the 'KVAR.KVar' hook attribute."
        ));
    }

    #[test]
    fn rejects_binder_attribute_with_first_sort_variable() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortExp{} []
                symbol malformed{S}(S, SortExp{}) : SortExp{} [constructor{}(), binder{}()]
            endmodule []
        "#})
        .expect("definition should parse");

        assert!(matches!(
            BackendDefinition::internalize(&syntax, "MAIN"),
            Err(DefinitionError::MalformedAttribute(message))
                if message == "First child of binder must have a sort with the 'KVAR.KVar' hook attribute."
        ));
    }

    fn assert_haskell_pattern_order(left: &str, right: &str, expected: Ordering) {
        let left = parse_pattern(left).expect("left pattern should parse");
        let right = parse_pattern(right).expect("right pattern should parse");
        assert_eq!(
            compare_haskell_patterns(&left, &right),
            expected,
            "unexpected Haskell order for {left} and {right}"
        );
        assert_eq!(
            compare_haskell_patterns(&right, &left),
            expected.reverse(),
            "unexpected reverse Haskell order for {right} and {left}"
        );
    }

    #[test]
    fn haskell_pattern_order_variable_counters() {
        for (left, right) in [
            ("X2:SortS{}", "X10:SortS{}"),
            ("X1:SortS{}", "X01:SortS{}"),
            ("@X2:SortS{}", "@X10:SortS{}"),
            ("@X1:SortS{}", "@X01:SortS{}"),
            ("X:SortS{}", "X0:SortS{}"),
            ("X0:SortS{}", "X00:SortS{}"),
            ("@X:SortS{}", "@X0:SortS{}"),
            ("@X0:SortS{}", "@X00:SortS{}"),
            ("X12:SortS{}", "X0012:SortS{}"),
            ("@X12:SortS{}", "@X0012:SortS{}"),
            (
                "X184467440737095516160:SortS{}",
                "X184467440737095516161:SortS{}",
            ),
            (
                "@X184467440737095516160:SortS{}",
                "@X184467440737095516161:SortS{}",
            ),
        ] {
            assert_haskell_pattern_order(left, right, Ordering::Less);
        }

        // Sort-variable identifiers and string literals retain lexical ordering.
        assert_haskell_pattern_order(r"\top{X10}()", r"\top{X2}()", Ordering::Less);
        assert_haskell_pattern_order(r#""X10""#, r#""X2""#, Ordering::Less);
    }

    #[test]
    fn haskell_pattern_order_empty_and_unary_connectives() {
        for (left, right) in [
            (r"\and{SortS{}}()", r"\top{SortS{}}()"),
            (r"\or{SortS{}}()", r"\bottom{SortS{}}()"),
            (r"\and{SortS{}}(a{}())", "a{}()"),
            (r"\or{SortS{}}(a{}())", "a{}()"),
        ] {
            assert_haskell_pattern_order(left, right, Ordering::Equal);
        }
    }

    #[test]
    fn haskell_pattern_order_normalized_pattern_attribute_tiebreak() {
        let empty_and = r#"
            axiom{} \rewrites{SortS{}}(a{}(), a{}())
                [ordering{}(\and{SortS{}}()), label{}("z-empty-and")]
        "#;
        let explicit_top = r#"
            axiom{} \rewrites{SortS{}}(a{}(), a{}())
                [ordering{}(\top{SortS{}}()), label{}("a-top")]
        "#;

        for rules in [
            format!("{empty_and}{explicit_top}"),
            format!("{explicit_top}{empty_and}"),
        ] {
            let source = format!(
                r#"[]
                module MAIN
                    sort SortS{{}} []
                    symbol a{{}}() : SortS{{}} [constructor{{}}()]
                    symbol ordering{{}}(SortS{{}}) : SortS{{}} []
                    symbol label{{}}(SortS{{}}) : SortS{{}} []
                    {rules}
                endmodule []"#
            );
            let syntax = parse_definition(&source).expect("definition should parse");
            let axioms = syntax.modules[0]
                .sentences
                .iter()
                .filter(|sentence| matches!(sentence, kore::Sentence::Axiom { .. }))
                .collect::<Vec<_>>();
            let (empty_and, explicit_top) = if rules.starts_with(empty_and) {
                (axioms[0], axioms[1])
            } else {
                (axioms[1], axioms[0])
            };
            assert_eq!(
                compare_rule_sentences(empty_and, explicit_top),
                Ordering::Greater
            );
        }
    }

    #[test]
    fn haskell_pattern_order_all_represented_constructors_and_fields() {
        let constructors = [
            r"\and{SortS{}}(a{}(), b{}())",
            "a{}()",
            r"\bottom{SortS{}}()",
            r"\ceil{SortS{}, SortS{}}(a{}())",
            r#"\dv{SortS{}}("a")"#,
            r"\equals{SortS{}, SortS{}}(a{}(), b{}())",
            r"\exists{SortS{}}(X:SortS{}, a{}())",
            r"\floor{SortS{}, SortS{}}(a{}())",
            r"\forall{SortS{}}(X:SortS{}, a{}())",
            r"\iff{SortS{}}(a{}(), b{}())",
            r"\implies{SortS{}}(a{}(), b{}())",
            r"\in{SortS{}, SortS{}}(a{}(), b{}())",
            r"\mu{}(@X:SortS{}, a{}())",
            r"\next{SortS{}}(a{}())",
            r"\not{SortS{}}(a{}())",
            r"\nu{}(@X:SortS{}, a{}())",
            r"\or{SortS{}}(a{}(), b{}())",
            r"\rewrites{SortS{}}(a{}(), b{}())",
            r"\top{SortS{}}()",
            r#""a""#,
            "X:SortS{}",
        ];
        for pair in constructors.windows(2) {
            assert_haskell_pattern_order(pair[0], pair[1], Ordering::Less);
        }

        let scalar_and_child_cases = [
            (r"\and{S}(a{}(), b{}())", r"\and{T}(a{}(), b{}())"),
            ("a{}()", "b{}()"),
            (r"\bottom{S}()", r"\bottom{T}()"),
            (r"\ceil{S, S}(a{}())", r"\ceil{T, S}(a{}())"),
            (r"\ceil{S, S}(a{}())", r"\ceil{S, T}(a{}())"),
            (r#"\dv{S}("a")"#, r#"\dv{T}("a")"#),
            (r#"\dv{S}("a")"#, r#"\dv{S}("b")"#),
            (
                r"\equals{S, S}(a{}(), b{}())",
                r"\equals{T, S}(a{}(), b{}())",
            ),
            (r"\exists{S}(X:S, a{}())", r"\exists{T}(X:S, a{}())"),
            (r"\exists{S}(X:S, a{}())", r"\exists{S}(Y:S, a{}())"),
            (r"\floor{S, S}(a{}())", r"\floor{T, S}(a{}())"),
            (r"\forall{S}(X:S, a{}())", r"\forall{T}(X:S, a{}())"),
            (r"\iff{S}(a{}(), b{}())", r"\iff{T}(a{}(), b{}())"),
            (r"\implies{S}(a{}(), b{}())", r"\implies{T}(a{}(), b{}())"),
            (r"\in{S, S}(a{}(), b{}())", r"\in{T, S}(a{}(), b{}())"),
            (r"\mu{}(@X:S, a{}())", r"\mu{}(@Y:S, a{}())"),
            (r"\next{S}(a{}())", r"\next{T}(a{}())"),
            (r"\not{S}(a{}())", r"\not{T}(a{}())"),
            (r"\nu{}(@X:S, a{}())", r"\nu{}(@Y:S, a{}())"),
            (r"\or{S}(a{}(), b{}())", r"\or{T}(a{}(), b{}())"),
            (r"\rewrites{S}(a{}(), b{}())", r"\rewrites{T}(a{}(), b{}())"),
            (r"\top{S}()", r"\top{T}()"),
            (r#""a""#, r#""b""#),
            ("X2:S", "X10:S"),
            ("a{}()", "a{}(a{}())"),
            (r"\and{S}(a{}(), a{}())", r"\and{S}(a{}(), b{}())"),
            (r"\and{S}(a{}(), b{}())", r"\and{S}(a{}(), b{}(), a{}())"),
            (r"\not{S}(a{}())", r"\not{S}(b{}())"),
            (r"\implies{S}(a{}(), a{}())", r"\implies{S}(a{}(), b{}())"),
        ];
        for (left, right) in scalar_and_child_cases {
            assert_haskell_pattern_order(left, right, Ordering::Less);
        }

        assert_haskell_pattern_order(
            r"\left-assoc{}(f{}(a{}(), b{}(), c{}()))",
            "f{}(f{}(a{}(), b{}()), c{}())",
            Ordering::Equal,
        );
        assert_haskell_pattern_order(
            r"\right-assoc{}(f{}(a{}(), b{}(), c{}()))",
            "f{}(a{}(), f{}(b{}(), c{}()))",
            Ordering::Equal,
        );
    }

    fn classified_rule_labels(definition: &BackendDefinition) -> Vec<&str> {
        definition
            .classified_axioms
            .iter()
            .filter_map(|axiom| match axiom {
                ClassifiedAxiom::Rewrite { attributes, .. }
                | ClassifiedAxiom::Function { attributes, .. }
                | ClassifiedAxiom::Simplification { attributes, .. }
                | ClassifiedAxiom::Ceil { attributes, .. } => attributes.label.as_deref(),
            })
            .collect()
    }

    #[test]
    fn indexes_main_module_before_imports_in_reverse_canonical_import_order() {
        let syntax = parse_definition(indoc! {r#"
            []
            module BASE
                sort SortS{} []
                symbol base{}() : SortS{} [constructor{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(base{}(), \top{SortS{}}()),
                    base{}()
                ) [label{}("base")]
            endmodule []
            module A
                import BASE []
                symbol a{}() : SortS{} [constructor{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(a{}(), \top{SortS{}}()),
                    a{}()
                ) [label{}("a")]
            endmodule []
            module B
                import BASE []
                symbol b{}() : SortS{} [constructor{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(b{}(), \top{SortS{}}()),
                    b{}()
                ) [label{}("b")]
            endmodule []
            module MAIN
                import A []
                import B []
                symbol main{}() : SortS{} [constructor{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(main{}(), \top{SortS{}}()),
                    main{}()
                ) [label{}("main")]
            endmodule []
        "#})
        .expect("definition should parse");

        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");

        assert_eq!(
            classified_rule_labels(&definition),
            ["main", "b", "base", "a", "base"]
        );
    }

    #[test]
    fn indexes_axioms_in_reverse_canonical_order_independent_of_source_order() {
        let heat = r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(injectiveFunction{}(X:SortV{})),
                    \top{SortS{}}()
                ),
                heatResult{}()
            ) [label{}("heat")]
        "#;
        let lookup = r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(\dv{SortV{}}("value")),
                    \top{SortS{}}()
                ),
                lookupResult{}()
            ) [label{}("lookup")]
        "#;

        for rules in [format!("{heat}{lookup}"), format!("{lookup}{heat}")] {
            let source = format!(
                r#"[]
                module MAIN
                    sort SortV{{}} [hasDomainValues{{}}()]
                    sort SortS{{}} []
                    symbol wrap{{}}(SortV{{}}) : SortS{{}} [constructor{{}}()]
                    symbol injectiveFunction{{}}(SortV{{}}) : SortV{{}}
                        [function{{}}(), total{{}}(), injective{{}}()]
                    symbol heatResult{{}}() : SortS{{}} [constructor{{}}()]
                    symbol lookupResult{{}}() : SortS{{}} [constructor{{}}()]
                    {rules}
                endmodule []"#
            );
            let syntax = parse_definition(&source).expect("definition should parse");
            let definition = BackendDefinition::internalize(&syntax, "MAIN")
                .expect("definition should internalize");

            assert_eq!(classified_rule_labels(&definition), ["lookup", "heat"]);
        }
    }

    fn source_execution_order_definition() -> kore::Definition {
        parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortS{} []
                symbol a{}() : SortS{} [constructor{}()]
                symbol b{}() : SortS{} [constructor{}()]
                symbol c{}() : SortS{} [constructor{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(a{}(), \top{SortS{}}()),
                    b{}()
                ) [UNIQUE'Unds'ID{}("first")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(a{}(), \top{SortS{}}()),
                    c{}()
                ) [UNIQUE'Unds'ID{}("second")]
            endmodule []
        "#})
        .expect("source-execution definition should parse")
    }

    #[test]
    fn source_execution_rejects_missing_and_duplicate_rewrite_order_ids() {
        let syntax = source_execution_order_definition();
        assert_eq!(
            BackendDefinition::internalize_for_source_execution(&syntax, "MAIN", &["first"])
                .unwrap_err(),
            DefinitionError::MissingRewriteOrderIds(vec!["second".into()])
        );
        assert_eq!(
            BackendDefinition::internalize_for_source_execution(
                &syntax,
                "MAIN",
                &["first", "first", "second"],
            )
            .unwrap_err(),
            DefinitionError::DuplicateRewriteOrderId("first".into())
        );
    }

    #[test]
    fn source_execution_accepts_frontend_order_entries_not_emitted_as_rewrites() {
        BackendDefinition::internalize_for_source_execution(
            &source_execution_order_definition(),
            "MAIN",
            &["first", "equation-or-macro", "second"],
        )
        .expect("extra frontend ranks do not make rewrite precedence ambiguous");
    }

    fn reference_definition_fixture(name: &str) -> kore::Definition {
        let source = match name {
            "undef" => include_str!("../../k-rust/tests/fixtures/reference/definition/undef.kore"),
            "arity" => include_str!("../../k-rust/tests/fixtures/reference/definition/arity.kore"),
            "boolbad" => {
                include_str!("../../k-rust/tests/fixtures/reference/definition/boolbad.kore")
            }
            "varsort" => {
                include_str!("../../k-rust/tests/fixtures/reference/definition/varsort.kore")
            }
            "claimrhs" => {
                include_str!("../../k-rust/tests/fixtures/reference/definition/claimrhs.kore")
            }
            "unbound" => {
                include_str!("../../k-rust/tests/fixtures/reference/definition/unbound.kore")
            }
            "selfsub" => {
                include_str!("../../k-rust/tests/fixtures/reference/definition/selfsub.kore")
            }
            "dupsym" => {
                include_str!("../../k-rust/tests/fixtures/reference/definition/dupsym.kore")
            }
            "ok" => include_str!("../../k-rust/tests/fixtures/reference/definition/ok.kore"),
            _ => panic!("unknown definition fixture {name}"),
        };
        parse_definition(source).expect("reference definition fixture should parse")
    }

    fn reference_pattern_fixture(name: &str) -> kore::Pattern {
        let source = match name {
            "dv" => include_str!("../../k-rust/tests/fixtures/reference/definition/dv.kore"),
            "pat" => include_str!("../../k-rust/tests/fixtures/reference/definition/pat.kore"),
            "var" => include_str!("../../k-rust/tests/fixtures/reference/definition/var.kore"),
            _ => panic!("unknown pattern fixture {name}"),
        };
        parse_pattern(source).expect("reference pattern fixture should parse")
    }

    #[test]
    fn reference_rejects_undeclared_symbols_in_ignored_axioms() {
        let error = BackendDefinition::internalize(&reference_definition_fixture("undef"), "M")
            .expect_err("ignored axioms must be verified");
        assert!(
            format!("{error}").contains("Head 'g' not defined."),
            "{error}"
        );
    }

    #[test]
    fn reference_rejects_arity_errors_in_ignored_axioms() {
        let error = BackendDefinition::internalize(&reference_definition_fixture("arity"), "M")
            .expect_err("ignored axioms must have their application arity verified");
        assert!(
            format!("{error}").contains("Expected 1 operands, but got 0."),
            "{error}"
        );
    }

    #[test]
    fn reference_rejects_domain_values_on_unmarked_sorts() {
        let definition = BackendDefinition::internalize(&reference_definition_fixture("ok"), "M")
            .expect("control definition should internalize");
        let error = definition
            .internalize_term(&reference_pattern_fixture("dv"), &[])
            .expect_err("domain values require hasDomainValues");
        assert!(format!("{error}").contains("hasDomainValues"), "{error}");
    }

    #[test]
    fn reference_rejects_non_boolean_bool_literals() {
        let error = BackendDefinition::internalize(&reference_definition_fixture("boolbad"), "M")
            .expect_err("Bool literals must be true or false");
        assert!(format!("{error}").contains("BOOL.Bool"), "{error}");
    }

    #[test]
    fn rejects_non_decimal_int_literals() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortToken{} [hasDomainValues{}()]
            endmodule []
        "#})
        .expect("domain-value definition should parse");
        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("domain-value definition should internalize");

        for value in ["3.0", "three"] {
            let pattern = parse_pattern(&format!(r#"\dv{{SortInt{{}}}}("{value}")"#))
                .expect("malformed Int domain value should parse as KORE");
            assert!(matches!(
                definition.internalize_term(&pattern, &[]),
                Err(DefinitionError::InvalidDomainValue { sort, value: actual })
                    if sort == Sort::simple("SortInt") && actual == value
            ));
        }

        let token = parse_pattern(r#"\dv{SortToken{}}("value")"#)
            .expect("unhooked domain value should parse");
        definition
            .internalize_term(&token, &[])
            .expect("an unhooked hasDomainValues sort stays accepted");
    }

    #[test]
    fn reference_rejects_inconsistent_free_variable_sorts() {
        let error = BackendDefinition::internalize(&reference_definition_fixture("varsort"), "M")
            .expect_err("one free variable name must have one sort");
        assert!(
            format!("{error}").contains("Inconsistent free variable usage"),
            "{error}"
        );
    }

    #[test]
    fn reference_rejects_claims_with_free_rhs_variables() {
        let error = BackendDefinition::internalize(&reference_definition_fixture("claimrhs"), "M")
            .expect_err("claim RHS variables must be bound on the LHS or existential");
        assert!(
            format!("{error}").contains("universally-quantified variables"),
            "{error}"
        );
    }

    #[test]
    fn reference_accepts_free_rhs_variables_in_axioms() {
        BackendDefinition::internalize(&reference_definition_fixture("unbound"), "M")
            .expect("Kore permits free variables appearing only on an axiom RHS");
    }

    #[test]
    fn reference_accepts_reflexive_subsort_axioms() {
        BackendDefinition::internalize(&reference_definition_fixture("selfsub"), "M")
            .expect("reflexive subsorts must be accepted, as in Kore");
    }

    #[test]
    fn reference_reports_duplicate_names_across_modules() {
        let error = BackendDefinition::internalize(&reference_definition_fixture("dupsym"), "N")
            .expect_err("duplicate names in an import closure must be rejected");
        assert!(format!("{error}").contains("c"), "{error}");
    }

    #[test]
    fn reference_accepts_free_standalone_variables() {
        let definition = BackendDefinition::internalize(&reference_definition_fixture("ok"), "M")
            .expect("control definition should internalize");
        definition
            .internalize_pattern(&reference_pattern_fixture("var"), &[])
            .expect("Kore permits free variables in standalone patterns");
    }

    fn predicate_floating_definition() -> BackendDefinition {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortToken{} [hasDomainValues{}()]
                sort SortK{} []
                symbol item{}(SortToken{}) : SortK{} [constructor{}()]
                symbol cell{}(SortK{}) : SortK{} [constructor{}()]
            endmodule []
        "#})
        .expect("predicate-floating definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("predicate-floating definition should internalize")
    }

    fn nested_predicate_pattern() -> kore::Pattern {
        parse_pattern(indoc! {r#"
            cell{}(
                \and{SortK{}}(
                    item{}(\dv{SortToken{}}("2")),
                    \equals{SortToken{}, SortK{}}(
                        \dv{SortToken{}}("3"),
                        X:SortToken{}
                    )
                )
            )
        "#})
        .expect("nested predicate pattern should parse")
    }

    #[test]
    fn floats_predicates_under_constructors_into_rule_constraints() {
        let definition = predicate_floating_definition();
        let pattern = definition
            .internalize_pattern(&nested_predicate_pattern(), &[])
            .expect("nested predicates should float to the pattern condition");

        assert_eq!(pattern.constraints.len(), 1);
        let TermKind::Application {
            symbol, arguments, ..
        } = pattern.term.kind()
        else {
            panic!("expected outer cell application: {:?}", pattern.term);
        };
        assert_eq!(symbol.name.as_ref(), "cell");
        assert_eq!(arguments.len(), 1);
        assert!(matches!(
            arguments[0].kind(),
            TermKind::Application { symbol, .. } if symbol.name.as_ref() == "item"
        ));
    }

    #[test]
    fn rejects_floated_predicates_at_pure_term_entry_points() {
        let error = predicate_floating_definition()
            .internalize_term(&nested_predicate_pattern(), &[])
            .expect_err("a pure term boundary must not discard floated predicates");

        assert_eq!(
            format!("{error}"),
            "predicate in term position (1 floated conjuncts) where a term is required"
        );
    }

    #[test]
    fn keeps_term_conjunctions_as_and_terms() {
        let definition = predicate_floating_definition();
        let syntax = parse_pattern(indoc! {r#"
            \and{SortToken{}}(
                \dv{SortToken{}}("2"),
                \dv{SortToken{}}("3")
            )
        "#})
        .expect("term conjunction should parse");

        let term = definition
            .internalize_term(&syntax, &[])
            .expect("two term components stay a term conjunction");
        assert!(matches!(term.kind(), TermKind::And(..)));
    }

    fn disjunction_definition(sentences: &str) -> Result<BackendDefinition, DefinitionError> {
        let source = format!(
            r#"[]
            module MAIN
                sort SortS{{}} []
                symbol a{{}}() : SortS{{}} [constructor{{}}()]
                symbol b{{}}() : SortS{{}} [constructor{{}}()]
                symbol c{{}}() : SortS{{}} [constructor{{}}()]
                symbol box{{}}(SortS{{}}) : SortS{{}} [constructor{{}}()]
                alias weakAlwaysFinally{{S}}(S) : S
                    where weakAlwaysFinally{{S}}(@X:S) := @X:S []
                {sentences}
            endmodule []"#
        );
        BackendDefinition::internalize(
            &parse_definition(&source).expect("disjunction definition should parse"),
            "MAIN",
        )
    }

    #[test]
    fn splits_lhs_disjunctions_into_one_rule_per_disjunct() {
        let definition = disjunction_definition(
            r#"axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    box{}(\or{SortS{}}(a{}(), b{}())),
                    \top{SortS{}}()
                ),
                c{}()
            ) [label{}("split-lhs")]"#,
        )
        .expect("term disjunctions on rewrite LHSs should split");

        let rules = definition
            .rewrite_theory
            .values()
            .flat_map(BTreeMap::values)
            .flatten()
            .collect::<Vec<_>>();
        assert_eq!(rules.len(), 2);
        assert!(
            rules
                .iter()
                .all(|rule| rule.attributes.unique_id == "split-lhs")
        );
    }

    #[test]
    fn internalizes_rhs_disjunctions_without_splitting_the_source_rule() {
        let definition = disjunction_definition(
            r#"axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(c{}(), \top{SortS{}}()),
                \or{SortS{}}(a{}(), b{}())
            ) [label{}("split-rhs")]"#,
        )
        .expect("term disjunctions on rewrite RHSs should internalize");

        let rule_count = definition
            .rewrite_theory
            .values()
            .flat_map(BTreeMap::values)
            .map(Vec::len)
            .sum::<usize>();
        assert_eq!(rule_count, 1);
    }

    #[test]
    fn splits_claim_lhs_disjunctions_into_several_claims() {
        let definition = disjunction_definition(
            r#"claim{} \implies{SortS{}}(
                \or{SortS{}}(a{}(), b{}()),
                weakAlwaysFinally{SortS{}}(c{}())
            ) [label{}("split-claim"), all-path{}()]"#,
        )
        .expect("term disjunctions on claim LHSs should split");

        assert_eq!(definition.reachability_claims.len(), 2);
        assert!(
            definition
                .reachability_claims
                .iter()
                .all(|claim| claim.attributes.unique_id == "split-claim")
        );
    }

    #[test]
    fn nested_initial_disjunctions_expand_but_single_pattern_entry_rejects_them() {
        let definition = disjunction_definition("").expect("control definition should load");
        let syntax = parse_pattern(r#"box{}(\or{SortS{}}(a{}(), b{}()))"#)
            .expect("nested initial disjunction should parse");

        let alternatives = definition
            .internalize_disjunction(&syntax, &[])
            .expect("nested initial disjunction should distribute");
        assert_eq!(alternatives.len(), 2);

        let error = definition
            .internalize_pattern(&syntax, &[])
            .expect_err("a single-pattern boundary must reject a term disjunction");
        assert!(
            format!("{error:?}").contains("TermDisjunction"),
            "{error:?}"
        );
    }

    fn definition() -> BackendDefinition {
        let syntax = parse_definition(indoc! {r#"
            []
            module BASE
                sort SortKey{} []
                sort SortValue{} []
                sort SortBox{S} []
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(dot{}()), element{}(item{}()), concat{}(concat{}())]
                hooked-symbol dot{}() : SortMap{} [function{}(), functional{}(), hook{}("MAP.unit")]
                hooked-symbol item{}(SortKey{}, SortValue{}) : SortMap{}
                    [function{}(), functional{}(), hook{}("MAP.element")]
                hooked-symbol concat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), assoc{}(), hook{}("MAP.concat")]
                symbol value{}() : SortValue{} [constructor{}()]
                symbol wrap{}(SortValue{}) : SortValue{} [constructor{}()]
                symbol injectiveFunction{}(SortValue{}) : SortValue{}
                    [function{}(), total{}(), injective{}()]
                symbol box{S}(S) : SortBox{S} [constructor{}()]
                symbol inj{From, To}(From) : To [sortInjection{}()]
                axiom{R}
                    \exists{R}(
                        Val:SortValue{},
                        \equals{SortValue{}, R}(
                            Val:SortValue{},
                            inj{SortKey{}, SortValue{}}(From:SortKey{})
                        )
                    )
                    [subsort{SortKey{}, SortValue{}}()]
            endmodule []
            module MAIN
                import BASE []
                symbol key{}() : SortKey{} [constructor{}()]
                axiom{}
                    \rewrites{SortValue{}}(
                        \and{SortValue{}}(
                            wrap{}(X:SortValue{}),
                            \equals{SortValue{}, SortValue{}}(X:SortValue{}, value{}())
                        ),
                        \exists{SortValue{}}(
                            Y:SortValue{},
                            \and{SortValue{}}(
                                wrap{}(Y:SortValue{}),
                                \equals{SortValue{}, SortValue{}}(Y:SortValue{}, X:SortValue{})
                            )
                        )
                    )
                    [label{}("kept-for-rule-internalization")]
            endmodule []
        "#})
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn overload_definition() -> BackendDefinition {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortS{} []
                symbol A{}() : SortS{} [constructor{}()]
                symbol B{}() : SortS{} [constructor{}()]
                symbol C{}() : SortS{} [constructor{}()]
                symbol D{}() : SortS{} [constructor{}()]
                symbol E{}() : SortS{} [constructor{}()]
                axiom{} \equals{SortS{}, SortS{}}(D{}(), B{}())
                    [symbol-overload{}(D{}(), B{}())]
                axiom{} \equals{SortS{}, SortS{}}(D{}(), C{}())
                    [symbol-overload{}(D{}(), C{}())]
                axiom{} \equals{SortS{}, SortS{}}(B{}(), A{}())
                    [symbol-overload{}(B{}(), A{}())]
                axiom{} \equals{SortS{}, SortS{}}(C{}(), A{}())
                    [symbol-overload{}(C{}(), A{}())]
            endmodule []
        "#})
        .expect("overload definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("overload definition should internalize")
    }

    #[test]
    fn model_predicates_require_an_atomic_ml_condition() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let term_only =
            parse_pattern(r"\and{SortBool{}}(\not{SortBool{}}(X:SortBool{}), X:SortBool{})")
                .unwrap();
        let predicate = parse_pattern(
            r"\equals{SortBool{}, SortBool{}}(\not{SortBool{}}(X:SortBool{}), X:SortBool{})",
        )
        .unwrap();

        assert_eq!(
            definition.internalize_model_predicate(&term_only, &[]),
            Ok(None)
        );
        assert!(matches!(
            definition.internalize_model_predicate(&predicate, &[]),
            Ok(Some((crate::rule::Predicate::Iff(..), _)))
        ));
    }

    #[test]
    fn resolves_transitive_module_scope_and_subsorts() {
        let definition = definition();
        assert_eq!(
            definition.modules,
            BTreeSet::from([Name::from("BASE"), Name::from("MAIN")])
        );
        assert!(definition.sorts.contains_key("SortBox"));
        assert!(definition.symbols.contains_key("key"));
        assert_eq!(definition.axioms.len(), 2);
        assert_eq!(definition.classified_axioms.len(), 1);
        let priorities = definition
            .rewrite_theory
            .get(&crate::rule::TermIndex::Symbol("wrap".into()))
            .expect("rewrite should be indexed by its head symbol");
        let rule = &priorities[&50][0];
        assert_eq!(rule.requires.len(), 1);
        assert_eq!(rule.ensures.len(), 1);
        assert!(
            rule.lhs
                .attributes()
                .variables
                .iter()
                .any(|variable| variable.name.as_ref() == "Rule#X")
        );
        assert_eq!(
            rule.existentials
                .iter()
                .map(|variable| variable.name.as_ref())
                .collect::<Vec<_>>(),
            vec!["Ex#Y"]
        );
        assert_eq!(
            definition
                .sort_graph
                .check_subsort(&Sort::simple("SortKey"), &Sort::simple("SortValue")),
            Ok(true)
        );
    }

    #[test]
    fn validates_and_instantiates_parametric_symbol_sorts() {
        let definition = definition();
        let pattern = parse_pattern("box{SortValue{}}(value{}())").expect("pattern should parse");
        let term = definition
            .internalize_term(&pattern, &[])
            .expect("term should internalize");
        assert_eq!(
            term.sort(),
            Sort::application("SortBox", vec![Sort::simple("SortValue")])
        );
    }

    #[test]
    fn preserves_injective_symbol_metadata() {
        let definition = definition();

        assert!(definition.symbols["injectiveFunction"].attributes.injective);
        assert!(!definition.symbols["wrap"].attributes.injective);
    }

    #[test]
    fn internalizes_the_transitive_symbol_overload_graph() {
        let definition = overload_definition();
        let a = Name::from("A");
        let b = Name::from("B");
        let c = Name::from("C");
        let d = Name::from("D");
        let e = Name::from("E");

        assert!(definition.overloads.is_overloaded(&a));
        assert!(definition.overloads.is_overloaded(&d));
        assert!(!definition.overloads.is_overloaded(&e));
        assert!(definition.overloads.is_overloading(&d, &a));
        assert!(!definition.overloads.is_overloading(&a, &d));
        assert_eq!(
            definition.overloads.common_overloads(&a, &a),
            BTreeSet::from([b, c, d.clone()])
        );
        assert_eq!(
            definition
                .overloads
                .common_overloads(&Name::from("B"), &Name::from("C")),
            BTreeSet::from([d])
        );
    }

    #[test]
    fn rejects_cyclic_symbol_overloads() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortS{} []
                symbol A{}() : SortS{} [constructor{}()]
                symbol B{}() : SortS{} [constructor{}()]
                axiom{} \equals{SortS{}, SortS{}}(A{}(), B{}())
                    [symbol-overload{}(A{}(), B{}())]
                axiom{} \equals{SortS{}, SortS{}}(B{}(), A{}())
                    [symbol-overload{}(B{}(), A{}())]
            endmodule []
        "#})
        .expect("cyclic overload definition should parse");

        assert!(matches!(
            BackendDefinition::internalize(&syntax, "MAIN"),
            Err(DefinitionError::MalformedAttribute(message))
                if message.contains("cycle")
        ));
    }

    #[test]
    fn canonicalizes_collection_symbol_applications() {
        let definition = definition();
        let pattern = parse_pattern("concat{}(item{}(key{}(), value{}()), REST:SortMap{})")
            .expect("pattern should parse");
        let term = definition
            .internalize_term(&pattern, &[])
            .expect("term should internalize");

        let TermKind::Map {
            definition,
            entries,
            rest,
        } = term.kind()
        else {
            panic!("expected internal map, found {term:?}");
        };
        assert_eq!(definition.map_sort.as_ref(), "SortMap");
        assert_eq!(entries.len(), 1);
        assert!(matches!(
            rest.as_ref().map(Term::kind),
            Some(TermKind::Variable(Variable { name, .. })) if name.as_ref() == "REST"
        ));
    }

    #[test]
    fn rejects_import_cycles_with_the_cycle_path() {
        let syntax = parse_definition(indoc! {"
            []
            module A
                import B []
            endmodule []
            module B
                import A []
            endmodule []
        "})
        .expect("definition should parse");

        assert_eq!(
            BackendDefinition::internalize(&syntax, "A").unwrap_err(),
            DefinitionError::ImportCycle(vec!["A".into(), "B".into(), "A".into()])
        );
    }

    #[test]
    fn rejects_term_sort_mismatches() {
        let definition = definition();
        let pattern = parse_pattern("box{SortKey{}}(value{}())").expect("pattern should parse");

        assert!(matches!(
            definition.internalize_term(&pattern, &[]),
            Err(DefinitionError::IncorrectArgumentSort {
                symbol,
                index: 0,
                expected,
                actual,
            }) if symbol == "box"
                && expected == Sort::simple("SortKey")
                && actual == Sort::simple("SortValue")
        ));
    }

    #[test]
    fn validates_application_shape_before_internalizing_children() {
        let definition = definition();
        let pattern = parse_pattern("box{SortKey{}}(box{SortKey{}}(value{}()), value{}())")
            .expect("pattern should parse");

        assert_eq!(
            definition.internalize_term(&pattern, &[]).unwrap_err(),
            DefinitionError::WrongSymbolArity {
                symbol: "box".into(),
                expected: 1,
                actual: 2,
            }
        );
    }

    #[test]
    fn rejects_injections_between_unrelated_sorts() {
        let definition = definition();
        let pattern =
            parse_pattern("inj{SortValue{}, SortKey{}}(key{}())").expect("pattern should parse");

        assert_eq!(
            definition.internalize_term(&pattern, &[]).unwrap_err(),
            DefinitionError::NotSubsort {
                source: Sort::simple("SortValue"),
                target: Sort::simple("SortKey"),
            }
        );
        definition
            .internalize_frontend_term(&pattern, &[])
            .expect("frontend-validated terms may use trusted injection bridges");
    }

    #[test]
    fn definition_rules_do_not_recheck_sort_injections() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortA{} []
                sort SortB{} []
                symbol inj{From, To}(From) : To [sortInjection{}()]
                axiom{}
                    \rewrites{SortB{}}(
                        \and{SortB{}}(
                            inj{SortA{}, SortB{}}(X:SortA{}),
                            \top{SortB{}}()
                        ),
                        inj{SortA{}, SortB{}}(X:SortA{})
                    ) []
            endmodule []
        "#})
        .expect("definition should parse");

        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("definition rules should trust frontend-validated injections");
    }

    #[test]
    fn expands_parametric_aliases_without_treating_them_as_symbols() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortValue{} []
                symbol value{}() : SortValue{} [constructor{}()]
                alias identity{S}(S) : S
                    where identity{S}(X:S) := X:S []
            endmodule []
        "#})
        .expect("definition should parse");

        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("alias definition should internalize");
        assert!(!definition.symbols.contains_key("identity"));
        let application = parse_pattern("identity{SortValue{}}(value{}())")
            .expect("alias application should parse");
        assert_eq!(
            definition.internalize_term(&application, &[]).unwrap(),
            definition
                .internalize_term(&parse_pattern("value{}()").unwrap(), &[])
                .unwrap()
        );
    }

    #[test]
    fn expands_aliases_before_classifying_rewrite_axioms() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortValue{} []
                sort SortState{} []
                symbol value{}() : SortValue{} [constructor{}()]
                symbol state{}(SortValue{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
                alias stateAlias{}(SortValue{}) : SortState{}
                    where stateAlias{}(X:SortValue{}) := state{}(X:SortValue{}) []
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        stateAlias{}(value{}()),
                        \top{SortState{}}()
                    ),
                    done{}()
                ) [label{}("aliased-rewrite")]
            endmodule []
        "#})
        .expect("aliased rewrite definition should parse");

        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("aliased rewrite should internalize");
        let rules = definition
            .rewrite_theory
            .values()
            .flat_map(|groups| groups.values())
            .flatten()
            .collect::<Vec<_>>();
        let [rule] = rules.as_slice() else {
            panic!("expected one expanded rewrite rule, found {rules:?}");
        };
        assert_eq!(
            rule.lhs,
            definition
                .internalize_term(&parse_pattern("state{}(value{}())").unwrap(), &[])
                .unwrap()
        );
    }

    #[test]
    fn rejects_recursive_alias_expansion_with_the_cycle() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortValue{} []
                symbol value{}() : SortValue{} [constructor{}()]
                alias loop{}(SortValue{}) : SortValue{}
                    where loop{}(X:SortValue{}) := loop{}(X:SortValue{}) []
            endmodule []
        "#})
        .expect("recursive alias definition should parse");
        assert_eq!(
            BackendDefinition::internalize(&syntax, "MAIN").unwrap_err(),
            DefinitionError::AliasCycle(vec!["loop".into(), "loop".into()])
        );
    }

    #[test]
    fn implication_patterns_reject_aliases_and_macros() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortValue{} []
                symbol value{}() : SortValue{} [constructor{}()]
                symbol macroValue{}() : SortValue{} [constructor{}(), macro{}()]
                alias identity{}(SortValue{}) : SortValue{}
                    where identity{}(X:SortValue{}) := X:SortValue{} []
            endmodule []
        "#})
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");

        for (source, expected) in [
            (
                "identity{}(value{}())",
                DefinitionError::MacroOrAliasInImplication("identity".into()),
            ),
            (
                "macroValue{}()",
                DefinitionError::MacroOrAliasInImplication("macroValue".into()),
            ),
        ] {
            let pattern = parse_pattern(source).expect("pattern should parse");
            assert_eq!(
                definition
                    .internalize_implication_pattern(&pattern, &[])
                    .unwrap_err(),
                expected
            );
        }

        let pattern = parse_pattern(r#"\and{SortValue{}}(macroValue{}(), identity{}(value{}()))"#)
            .expect("pattern should parse");
        assert_eq!(
            definition.validate_implication_pattern(&pattern),
            Err(DefinitionError::MacroOrAliasInImplication(
                "macroValue".into()
            ))
        );
    }

    #[test]
    fn builds_function_simplification_and_ceil_theories() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortValue{} []
                symbol value{}() : SortValue{} [constructor{}()]
                symbol wrap{}(SortValue{}) : SortValue{} [constructor{}()]
                symbol f{}(SortValue{}) : SortValue{} [function{}()]
                axiom{R}
                    \implies{R}(
                        \and{R}(
                            \top{R}(),
                            \and{R}(
                                \in{SortValue{}, R}(X0:SortValue{}, wrap{}(X:SortValue{})),
                                \top{R}()
                            )
                        ),
                        \equals{SortValue{}, R}(
                            f{}(X0:SortValue{}),
                            \and{SortValue{}}(value{}(), \top{SortValue{}}())
                        )
                    )
                    [label{}("evaluate-f")]
                axiom{R}
                    \implies{R}(
                        \top{R}(),
                        \equals{SortValue{}, R}(
                            f{}(X:SortValue{}),
                            \and{SortValue{}}(X:SortValue{}, \top{SortValue{}}())
                        )
                    )
                    [label{}("simplify-f"), simplification{}()]
                axiom{R}
                    \implies{R}(
                        \top{R}(),
                        \equals{R, R}(
                            \ceil{SortValue{}, R}(f{}(X:SortValue{})),
                            \top{R}()
                        )
                    )
                    [label{}("ceil-f")]
            endmodule []
        "#})
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let index = crate::rule::TermIndex::Symbol("f".into());

        let function = &definition.function_theory[&index][&50][0];
        assert!(
            function
                .lhs
                .attributes()
                .variables
                .iter()
                .any(|variable| variable.name.as_ref() == "Eq#X")
        );
        assert!(definition.simplification_theory.contains_key(&index));
        let ceil = &definition.ceil_theory[&index][&50][0];
        assert!(matches!(
            ceil.rhs,
            crate::rule::RuleRhs::Predicates(ref predicates) if predicates.is_empty()
        ));
    }

    #[test]
    fn source_execution_order_changes_only_the_rewrite_theory() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortValue{} []
                symbol value{}() : SortValue{} [constructor{}()]
                symbol other{}() : SortValue{} [constructor{}()]
                symbol wrap{}(SortValue{}) : SortValue{} [constructor{}()]
                symbol f{}(SortValue{}) : SortValue{} [function{}()]
                axiom{} \rewrites{SortValue{}}(
                    \and{SortValue{}}(value{}(), \top{SortValue{}}()),
                    other{}()
                ) [UNIQUE'Unds'ID{}("rewrite-value")]
                axiom{} \rewrites{SortValue{}}(
                    \and{SortValue{}}(value{}(), \top{SortValue{}}()),
                    wrap{}(other{}())
                ) [UNIQUE'Unds'ID{}("rewrite-wrap")]
                axiom{R}
                    \implies{R}(
                        \and{R}(
                            \top{R}(),
                            \and{R}(
                                \in{SortValue{}, R}(X0:SortValue{}, wrap{}(X:SortValue{})),
                                \top{R}()
                            )
                        ),
                        \equals{SortValue{}, R}(
                            f{}(X0:SortValue{}),
                            \and{SortValue{}}(value{}(), \top{SortValue{}}())
                        )
                    )
                    [label{}("evaluate-f"), UNIQUE'Unds'ID{}("function")]
                axiom{R}
                    \implies{R}(
                        \top{R}(),
                        \equals{SortValue{}, R}(
                            f{}(X:SortValue{}),
                            \and{SortValue{}}(X:SortValue{}, \top{SortValue{}}())
                        )
                    )
                    [label{}("simplify-f"), UNIQUE'Unds'ID{}("simplification"), simplification{}()]
                axiom{R}
                    \implies{R}(
                        \top{R}(),
                        \equals{R, R}(
                            \ceil{SortValue{}, R}(f{}(X:SortValue{})),
                            \top{R}()
                        )
                    )
                    [label{}("ceil-f"), UNIQUE'Unds'ID{}("ceil")]
            endmodule []
        "#})
        .expect("mixed-theory definition should parse");
        let canonical = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("mixed-theory definition should internalize");
        let canonical_order = canonical
            .rewrite_theory
            .values()
            .flat_map(BTreeMap::values)
            .flatten()
            .map(|rule| rule.attributes.unique_id.clone())
            .collect::<Vec<_>>();
        assert_eq!(canonical_order.len(), 2);
        let requested = canonical_order.iter().rev().cloned().collect::<Vec<_>>();

        let ordered =
            BackendDefinition::internalize_for_source_execution(&syntax, "MAIN", &requested)
                .expect("explicit rewrite order should internalize");
        let ordered_rewrites = ordered
            .rewrite_theory
            .values()
            .flat_map(BTreeMap::values)
            .flatten()
            .map(|rule| rule.attributes.unique_id.clone())
            .collect::<Vec<_>>();

        assert_eq!(ordered_rewrites, requested);
        assert_eq!(ordered.function_theory, canonical.function_theory);
        assert_eq!(
            ordered.simplification_theory,
            canonical.simplification_theory
        );
        assert_eq!(
            ordered.predicate_simplification_theory,
            canonical.predicate_simplification_theory
        );
        assert_eq!(ordered.ceil_theory, canonical.ceil_theory);
        assert_eq!(ordered.claims, canonical.claims);
        assert_eq!(ordered.classified_axioms, canonical.classified_axioms);
    }

    #[test]
    fn internalizes_smt_hooks_and_smtlib_symbol_names() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                symbol absolute{}(SortInt{}) : SortInt{}
                    [function{}(), total{}(), smt-hook{}("(ite (< #1 0) (- 0 #1) #1)")]
                symbol opaque{}(SortInt{}) : SortInt{}
                    [function{}(), total{}(), smtlib{}("opaque_int")]
                symbol hookWins{}(SortInt{}) : SortInt{}
                    [function{}(), total{}(), smt-hook{}("+"), smtlib{}("ignored")]
            endmodule []
        "#})
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");

        assert_eq!(
            definition.symbols["absolute"].attributes.smt,
            Some(SmtType::Hook(
                SExpr::parse("(ite (< #1 0) (- 0 #1) #1)").unwrap()
            ))
        );
        assert_eq!(
            definition.symbols["opaque"].attributes.smt,
            Some(SmtType::Lib("opaque_int".into()))
        );
        assert_eq!(
            definition.symbols["hookWins"].attributes.smt,
            Some(SmtType::Hook(SExpr::atom("+")))
        );
    }
}
