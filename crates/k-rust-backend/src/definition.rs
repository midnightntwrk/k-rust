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
    collection: Option<CollectionSort>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum CollectionSort {
    Map(CollectionSymbols),
    List(CollectionSymbols),
    Set(CollectionSymbols),
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
    InvalidSymbolType(String),
    InvalidSortParameter,
    MalformedAttribute(String),
    MalformedCollection(String),
    MalformedAlias(String),
    AliasCycle(Vec<String>),
    MacroOrAliasInImplication(String),
    ExpectedTerm(&'static str),
    EmptyAssociativeApplication(String),
    Axiom(AxiomError),
    RulePattern(RulePatternError),
    Claim(ClaimError),
}

impl fmt::Display for DefinitionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl Error for DefinitionError {}

impl BackendDefinition {
    pub fn internalize(
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

        let mut axioms = Vec::new();
        let mut claims = Vec::new();
        let mut subsorts = Vec::new();
        let mut overloads = Vec::new();
        for module in &ordered {
            for sentence in &module.sentences {
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
            .collect::<Result<Vec<_>, _>>()?;
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
            .filter_map(Result::transpose)
            .collect::<Result<Vec<_>, _>>()?;
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
        let known = sort_variables.iter().cloned().collect::<BTreeSet<_>>();
        let pattern = expand_aliases(pattern, &self.aliases)?;
        self.internalize_term_with(&pattern, &known)
    }

    /// Internalize a constrained KORE pattern into its term and predicate components.
    pub fn internalize_pattern(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
    ) -> Result<Pattern, DefinitionError> {
        let pattern = expand_aliases(pattern, &self.aliases)?;
        let (term, constraints) = internalize_rule_pattern(self, &pattern, sort_variables)?;
        Ok(Pattern { term, constraints })
    }

    /// Internalize an arbitrary KORE pattern as an ML predicate and retain its result sort.
    pub fn internalize_predicate(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
    ) -> Result<(crate::rule::Predicate, Sort), DefinitionError> {
        let pattern = expand_aliases(pattern, &self.aliases)?;
        let known = sort_variables.iter().cloned().collect::<BTreeSet<_>>();
        let result_sort = self.internalize_pattern_result_sort(&pattern, &known)?;
        let predicate = internalize_rule_predicate(self, &pattern, sort_variables)?;
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
        let result_sort = self.internalize_pattern_result_sort(&pattern, &known)?;
        Ok(
            internalize_rule_model_predicate(self, &pattern, sort_variables)?
                .map(|predicate| (predicate, result_sort)),
        )
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
        let (term, constraints) = internalize_rule_pattern(self, body, sort_variables)?;
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
                    pending.extend(arguments);
                }
                kore::Pattern::And { arguments, .. } | kore::Pattern::Or { arguments, .. } => {
                    pending.extend(arguments);
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
                    pending.push(left);
                    pending.push(right);
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
        let mut alternatives = Vec::new();
        flatten_or(&pattern, &mut alternatives);
        alternatives
            .into_iter()
            .filter(|alternative| !matches!(alternative, kore::Pattern::Bottom { .. }))
            .map(|alternative| {
                let (term, constraints) =
                    internalize_rule_pattern(self, alternative, sort_variables)?;
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
                let arguments = arguments
                    .iter()
                    .map(|argument| self.internalize_term_with(argument, sort_variables))
                    .collect::<Result<Vec<_>, _>>()?;
                self.internalize_application(symbol, arguments, sort_variables)
            }
            kore::Pattern::DomainValue { sort, value } => Ok(Term::domain_value(
                internalize_sort(sort, &self.sorts, sort_variables)?,
                value.as_str(),
            )),
            kore::Pattern::And { arguments, .. } => {
                let mut arguments = arguments
                    .iter()
                    .map(|argument| self.internalize_term_with(argument, sort_variables))
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
                    .map(|argument| self.internalize_term_with(argument, sort_variables))
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
                    result = self.internalize_application(symbol, pair, sort_variables)?;
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

    fn internalize_pattern_result_sort(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &BTreeSet<Name>,
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
            None => Ok(self.internalize_term_with(pattern, sort_variables)?.sort()),
        }
    }

    fn internalize_application(
        &self,
        syntax: &kore::Symbol,
        arguments: Vec<Term>,
        sort_variables: &BTreeSet<Name>,
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
        Ok(Term::application(symbol, sort_arguments, arguments))
    }
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
                    let Ok(term) = definition.internalize_term(constructor, &axiom.parameters)
                    else {
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

fn internalize_sort(
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

fn substitute_sort(sort: &Sort, substitution: &BTreeMap<Name, Sort>) -> Sort {
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

    use crate::term::TermKind;

    use super::*;

    fn definition() -> BackendDefinition {
        let syntax = parse_definition(indoc! {r#"
            []
            module BASE
                sort SortKey{} []
                sort SortValue{} []
                sort SortBox{S} []
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(dot{}()), element{}(item{}()), concat{}(concat{}())]
                symbol dot{}() : SortMap{} [function{}(), functional{}(), hook{}("MAP.unit")]
                symbol item{}(SortKey{}, SortValue{}) : SortMap{}
                    [function{}(), functional{}(), hook{}("MAP.element")]
                symbol concat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), assoc{}(), hook{}("MAP.concat")]
                symbol value{}() : SortValue{} [constructor{}()]
                symbol wrap{}(SortValue{}) : SortValue{} [constructor{}()]
                symbol injectiveFunction{}(SortValue{}) : SortValue{}
                    [function{}(), total{}(), injective{}()]
                symbol box{S}(S) : SortBox{S} [constructor{}()]
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
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
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
    fn internalizes_smt_hooks_and_smtlib_symbol_names() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
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
