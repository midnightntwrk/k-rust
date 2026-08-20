//! Validation and internalization of textual KORE definitions.

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt,
    sync::Arc,
};

use k_rust_kore::kore::ast as kore;

use crate::{
    matching::SortGraph,
    rule::{
        AxiomError, ClassifiedAxiom, RuleKind, RulePatternError, Theory, classify_axiom,
        insert_theory, internalize_axiom,
    },
    term::{
        CollectionMetadata, CollectionSymbols, FunctionType, ListDefinition, MapDefinition, Name,
        Sort, Symbol, SymbolAttributes, SymbolType, Term, Variable,
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
    pub sort_graph: SortGraph,
    pub axioms: Vec<PendingAxiom>,
    pub classified_axioms: Vec<ClassifiedAxiom>,
    pub claims: Vec<PendingAxiom>,
    pub rewrite_theory: Theory,
    pub function_theory: Theory,
    pub simplification_theory: Theory,
    pub ceil_theory: Theory,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DefinitionError {
    NoSuchModule(String),
    ImportCycle(Vec<String>),
    DuplicateModule(String),
    DuplicateSort(String),
    DuplicateSymbol(String),
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
    ExpectedTerm(&'static str),
    EmptyAssociativeApplication(String),
    Axiom(AxiomError),
    RulePattern(RulePatternError),
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
        for module in &ordered {
            for sentence in &module.sentences {
                let (target, parameters, pattern, attributes) = match sentence {
                    kore::Sentence::Axiom {
                        parameters,
                        pattern,
                        attributes,
                    } => (&mut axioms, parameters, pattern, attributes),
                    kore::Sentence::Claim {
                        parameters,
                        pattern,
                        attributes,
                    } => (&mut claims, parameters, pattern, attributes),
                    _ => continue,
                };
                reject_duplicates(parameters)?;
                if let Some((sub, sup)) = subsort_attribute(pattern, attributes, &sorts)? {
                    subsorts.push((sub, sup));
                }
                target.push(PendingAxiom {
                    module: module.name.as_str().into(),
                    parameters: parameters.iter().cloned().map(Into::into).collect(),
                    pattern: (**pattern).clone(),
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
        let mut result = Self {
            main_module: main_module.into(),
            modules: ordered
                .iter()
                .map(|module| Name::from(module.name.as_str()))
                .collect(),
            sorts,
            symbols,
            sort_graph,
            axioms,
            classified_axioms,
            claims,
            rewrite_theory: Theory::new(),
            function_theory: Theory::new(),
            simplification_theory: Theory::new(),
            ceil_theory: Theory::new(),
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
        for (kind, rule) in rules {
            let theory = match kind {
                RuleKind::Rewrite => &mut result.rewrite_theory,
                RuleKind::Function => &mut result.function_theory,
                RuleKind::Simplification => &mut result.simplification_theory,
                RuleKind::Ceil => &mut result.ceil_theory,
            };
            insert_theory(theory, rule);
        }
        Ok(result)
    }

    pub fn internalize_term(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
    ) -> Result<Term, DefinitionError> {
        let known = sort_variables.iter().cloned().collect::<BTreeSet<_>>();
        self.internalize_term_with(pattern, &known)
    }

    pub(crate) fn internalize_syntax_sort(
        &self,
        sort: &kore::Sort,
        sort_variables: &[Name],
    ) -> Result<Sort, DefinitionError> {
        let known = sort_variables.iter().cloned().collect::<BTreeSet<_>>();
        internalize_sort(sort, &self.sorts, &known)
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
            kore::Pattern::Variable(variable) => Ok(Term::variable(Variable::new(
                variable.name.as_str(),
                internalize_sort(&variable.sort, &self.sorts, sort_variables)?,
            ))),
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
    Ok(SymbolAttributes {
        symbol_type,
        associative: has_attribute(attributes, "assoc"),
        idempotent: has_attribute(attributes, "idem"),
        macro_or_alias: has_attribute(attributes, "macro")
            || has_attribute(attributes, "alias'Kywd'"),
        has_evaluators: !has_attribute(attributes, "no-evaluators"),
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
    fn ignores_claim_only_alias_declarations_like_the_reference_backend() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortValue{} []
                alias identity{}(SortValue{}) : SortValue{}
                    where identity{}(X:SortValue{}) := X:SortValue{} []
            endmodule []
        "#})
        .expect("definition should parse");

        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("claim-only aliases should not prevent executable definition loading");
        assert!(!definition.symbols.contains_key("identity"));
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
}
