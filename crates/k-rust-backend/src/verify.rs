//! Syntactic verification of KORE sentences before backend classification.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    sync::Arc,
};

use k_rust_kore::kore::ast as kore;

use crate::{
    alias::AliasDefinition,
    definition::{DefinitionError, SortInfo, internalize_sort, substitute_sort},
    term::{Name, Sort, Symbol, SymbolType},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerificationError {
    pub module: String,
    pub sentence: SentenceContext,
    pub context: Vec<String>,
    pub message: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SentenceContext {
    Axiom { index: usize },
    Claim { index: usize },
    Sort(String),
    Symbol(String),
    Alias(String),
    Standalone,
}

impl fmt::Display for VerificationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.module.is_empty() {
            write!(formatter, "module '{}': ", self.module)?;
        }
        match &self.sentence {
            SentenceContext::Axiom { .. } => write!(formatter, "axiom declaration")?,
            SentenceContext::Claim { .. } => write!(formatter, "claim declaration")?,
            SentenceContext::Sort(name) => write!(formatter, "sort declaration '{name}'")?,
            SentenceContext::Symbol(name) => write!(formatter, "symbol declaration '{name}'")?,
            SentenceContext::Alias(name) => write!(formatter, "alias declaration '{name}'")?,
            SentenceContext::Standalone => {}
        }
        for context in &self.context {
            if !matches!(self.sentence, SentenceContext::Standalone) || !self.context.is_empty() {
                write!(formatter, ": {context}")?;
            }
        }
        if matches!(self.sentence, SentenceContext::Standalone) && self.context.is_empty() {
            write!(formatter, "{}", self.message)
        } else {
            write!(formatter, ": {}", self.message)
        }
    }
}

struct VerifyContext<'a> {
    module: &'a str,
    sentence: SentenceContext,
    sorts: &'a BTreeMap<Name, SortInfo>,
    symbols: &'a BTreeMap<Name, Arc<Symbol>>,
    aliases: &'a BTreeMap<String, AliasDefinition>,
    sort_variables: BTreeSet<Name>,
    free: BTreeMap<(kore::VariableKind, String), Sort>,
    bound: Vec<((kore::VariableKind, String), Sort)>,
    context: Vec<String>,
}

impl<'a> VerifyContext<'a> {
    fn new(
        module: &'a str,
        sentence: SentenceContext,
        sorts: &'a BTreeMap<Name, SortInfo>,
        symbols: &'a BTreeMap<Name, Arc<Symbol>>,
        aliases: &'a BTreeMap<String, AliasDefinition>,
        sort_variables: impl IntoIterator<Item = Name>,
    ) -> Self {
        Self {
            module,
            sentence,
            sorts,
            symbols,
            aliases,
            sort_variables: sort_variables.into_iter().collect(),
            free: BTreeMap::new(),
            bound: Vec::new(),
            context: Vec::new(),
        }
    }

    fn error(&self, message: impl Into<String>) -> VerificationError {
        VerificationError {
            module: self.module.into(),
            sentence: self.sentence.clone(),
            context: self.context.clone(),
            message: message.into(),
        }
    }

    fn with_context<T>(
        &mut self,
        name: impl Into<String>,
        action: impl FnOnce(&mut Self) -> Result<T, VerificationError>,
    ) -> Result<T, VerificationError> {
        self.context.push(name.into());
        let result = action(self);
        self.context.pop();
        result
    }

    fn sort(&self, sort: &kore::Sort) -> Result<Sort, VerificationError> {
        if let kore::Sort::Variable(name) = sort
            && !self.sort_variables.contains(name.as_str())
        {
            return Err(self.error(format!("Sort variable {name} not declared.")));
        }
        internalize_sort(sort, self.sorts, &self.sort_variables).map_err(|error| {
            let message = match error {
                DefinitionError::UnknownSort(name) => format!("Sort '{name}' not defined."),
                DefinitionError::WrongSortArity {
                    expected, actual, ..
                } => format!("Expected {expected} sort arguments, but got {actual}."),
                _ => format!("{error}"),
            };
            self.error(message)
        })
    }

    fn expect_sort(&self, expected: &Sort, actual: Sort) -> Result<(), VerificationError> {
        if expected == &actual {
            Ok(())
        } else {
            Err(self.error(format!(
                "Expecting sort {} but got {}.",
                render_sort(expected),
                render_sort(&actual)
            )))
        }
    }

    fn pattern(&mut self, pattern: &kore::Pattern) -> Result<Sort, VerificationError> {
        use kore::Pattern;
        match pattern {
            Pattern::String(_) => Ok(Sort::simple("SortString")),
            Pattern::Variable(variable) => {
                let sort = self.sort(&variable.sort)?;
                let key = (variable.kind, variable.name.clone());
                if let Some((_, bound_sort)) = self.bound.iter().rev().find(|(found, _)| found == &key)
                {
                    if bound_sort != &sort {
                        return Err(self.error("The declared sort is different."));
                    }
                } else if let Some(previous) = self.free.get(&key) {
                    if previous != &sort {
                        return Err(self.error(format!(
                            "Inconsistent free variable usage: {}:{} and {}:{}.",
                            variable.name,
                            render_sort(previous),
                            variable.name,
                            render_sort(&sort)
                        )));
                    }
                } else {
                    self.free.insert(key, sort.clone());
                }
                Ok(sort)
            }
            Pattern::Application { symbol, arguments }
            | Pattern::AssociativeApplication {
                symbol, arguments, ..
            } => self.with_context(format!("symbol or alias '{}'", symbol.name), |ctx| {
                let sort_arguments = symbol
                    .sort_parameters
                    .iter()
                    .map(|sort| ctx.sort(sort))
                    .collect::<Result<Vec<_>, _>>()?;
                let (parameters, expected_arguments, result) =
                    if let Some(declaration) = ctx.symbols.get(symbol.name.as_str()) {
                        (
                            declaration.sort_variables.clone(),
                            declaration.argument_sorts.clone(),
                            declaration.result_sort.clone(),
                        )
                    } else if let Some(alias) = ctx.aliases.get(&symbol.name) {
                        let parameters = alias
                            .sort_parameters
                            .iter()
                            .map(|name| Name::from(name.as_str()))
                            .collect::<Vec<_>>();
                        let known = alias
                            .sort_parameters
                            .iter()
                            .cloned()
                            .map(Name::from)
                            .collect::<BTreeSet<_>>();
                        (
                            parameters,
                            alias
                                .argument_sorts
                                .iter()
                                .map(|sort| internalize_sort(sort, ctx.sorts, &known))
                                .collect::<Result<Vec<_>, _>>()
                                .map_err(|error| ctx.error(format!("{error}")))?,
                            internalize_sort(&alias.result_sort, ctx.sorts, &known)
                                .map_err(|error| ctx.error(format!("{error}")))?,
                        )
                    } else {
                        return Err(ctx.error(format!("Head '{}' not defined.", symbol.name)));
                    };
                if parameters.len() != sort_arguments.len() {
                    return Err(ctx.error(format!(
                        "Expected {} sort parameters, but got {}.",
                        parameters.len(),
                        sort_arguments.len()
                    )));
                }
                if expected_arguments.len() != arguments.len() {
                    return Err(ctx.error(format!(
                        "Expected {} operands, but got {}.",
                        expected_arguments.len(),
                        arguments.len()
                    )));
                }
                let substitution = parameters
                    .into_iter()
                    .zip(sort_arguments)
                    .collect::<BTreeMap<_, _>>();
                for (argument, expected) in arguments.iter().zip(expected_arguments) {
                    let actual = ctx.pattern(argument)?;
                    ctx.expect_sort(&substitute_sort(&expected, &substitution), actual)?;
                }
                Ok(substitute_sort(&result, &substitution))
            }),
            Pattern::Top { sort } | Pattern::Bottom { sort } => self.sort(sort),
            Pattern::And { sort, arguments } | Pattern::Or { sort, arguments } => {
                let operator = if matches!(pattern, Pattern::And { .. }) {
                    "\\and"
                } else {
                    "\\or"
                };
                self.with_context(operator, |ctx| {
                    if arguments.len() < 2 {
                        return Err(ctx.error(format!(
                            "Cannot internalize {} with less than two children",
                            if operator == "\\and" { "And" } else { "Or" }
                        )));
                    }
                    let expected = ctx.sort(sort)?;
                    for argument in arguments {
                        let actual = ctx.pattern(argument)?;
                        ctx.expect_sort(&expected, actual)?;
                    }
                    Ok(expected)
                })
            }
            Pattern::Not { sort, argument } | Pattern::Next { sort, argument } => {
                let operator = if matches!(pattern, Pattern::Not { .. }) {
                    "\\not"
                } else {
                    "\\next"
                };
                self.with_context(operator, |ctx| {
                    let expected = ctx.sort(sort)?;
                    let actual = ctx.pattern(argument)?;
                    ctx.expect_sort(&expected, actual)?;
                    Ok(expected)
                })
            }
            Pattern::Implies { sort, left, right }
            | Pattern::Iff { sort, left, right }
            | Pattern::Rewrites { sort, left, right } => {
                let operator = match pattern {
                    Pattern::Implies { .. } => "\\implies",
                    Pattern::Iff { .. } => "\\iff",
                    Pattern::Rewrites { .. } => "\\rewrites",
                    _ => unreachable!(),
                };
                self.with_context(operator, |ctx| {
                    let expected = ctx.sort(sort)?;
                    let left = ctx.pattern(left)?;
                    ctx.expect_sort(&expected, left)?;
                    let right = ctx.pattern(right)?;
                    ctx.expect_sort(&expected, right)?;
                    Ok(expected)
                })
            }
            Pattern::Exists {
                sort,
                variable,
                body,
            }
            | Pattern::Forall {
                sort,
                variable,
                body,
            } => {
                let operator = if matches!(pattern, Pattern::Exists { .. }) {
                    "\\exists"
                } else {
                    "\\forall"
                };
                self.with_context(operator, |ctx| {
                    let result = ctx.sort(sort)?;
                    let variable_sort = ctx.sort(&variable.sort)?;
                    ctx.bound.push(((variable.kind, variable.name.clone()), variable_sort));
                    let body_sort = ctx.pattern(body)?;
                    ctx.bound.pop();
                    ctx.expect_sort(&result, body_sort)?;
                    Ok(result)
                })
            }
            Pattern::Mu { variable, body } | Pattern::Nu { variable, body } => {
                let result = self.sort(&variable.sort)?;
                self.bound.push(((variable.kind, variable.name.clone()), result.clone()));
                let body_sort = self.pattern(body)?;
                self.bound.pop();
                self.expect_sort(&result, body_sort)?;
                Ok(result)
            }
            Pattern::Ceil {
                operand_sort,
                result_sort,
                argument,
            }
            | Pattern::Floor {
                operand_sort,
                result_sort,
                argument,
            } => {
                let operator = if matches!(pattern, Pattern::Ceil { .. }) {
                    "\\ceil"
                } else {
                    "\\floor"
                };
                self.with_context(operator, |ctx| {
                    let operand = ctx.sort(operand_sort)?;
                    let result = ctx.sort(result_sort)?;
                    let actual = ctx.pattern(argument)?;
                    ctx.expect_sort(&operand, actual)?;
                    Ok(result)
                })
            }
            Pattern::Equals {
                operand_sort,
                result_sort,
                left,
                right,
            }
            | Pattern::In {
                operand_sort,
                result_sort,
                left,
                right,
            } => {
                let operator = if matches!(pattern, Pattern::Equals { .. }) {
                    "\\equals"
                } else {
                    "\\in"
                };
                self.with_context(operator, |ctx| {
                    let operand = ctx.sort(operand_sort)?;
                    let result = ctx.sort(result_sort)?;
                    let left = ctx.pattern(left)?;
                    ctx.expect_sort(&operand, left)?;
                    let right = ctx.pattern(right)?;
                    ctx.expect_sort(&operand, right)?;
                    Ok(result)
                })
            }
            Pattern::DomainValue { sort, value } => self.with_context("\\dv", |ctx| {
                let sort = ctx.sort(sort)?;
                let Sort::Application { name, .. } = &sort else {
                    return Err(ctx.error(
                        "Sorts used with domain value must have the hasDomainValues attribute.",
                    ));
                };
                let info = &ctx.sorts[name];
                if !info.has_domain_values {
                    return Err(ctx.error(
                        "Sorts used with domain value must have the hasDomainValues attribute.",
                    ));
                }
                if info.hook.as_deref() == Some("BOOL.Bool")
                    && !matches!(value.as_str(), "true" | "false")
                {
                    return Err(ctx.error(format!(
                        "Verifying builtin sort 'BOOL.Bool': While parsing domain value: expecting \"false\" or \"true\", found {value:?}"
                    )));
                }
                Ok(sort)
            }),
        }
    }
}

pub(crate) fn verify_definition(
    ordered: &[&kore::Module],
    all_modules: &[kore::Module],
    sorts: &BTreeMap<Name, SortInfo>,
    symbols: &BTreeMap<Name, Arc<Symbol>>,
    aliases: &BTreeMap<String, AliasDefinition>,
) -> Result<(), DefinitionError> {
    verify_unique_names(all_modules)?;
    for module in ordered {
        let mut axiom_index = 0;
        let mut claim_index = 0;
        for sentence in &module.sentences {
            verify_attributes(module, sentence, sorts, symbols, aliases)?;
            verify_declaration(module, sentence, sorts, symbols, aliases)?;
            match sentence {
                kore::Sentence::AliasDeclaration {
                    alias,
                    left,
                    right,
                    result_sort,
                    ..
                } => {
                    let variables = match left.as_ref() {
                        kore::Pattern::Application { arguments, .. } => arguments
                            .iter()
                            .filter_map(|argument| match argument {
                                kore::Pattern::Variable(variable) => Some(variable.clone()),
                                _ => None,
                            })
                            .collect::<Vec<_>>(),
                        _ => Vec::new(),
                    };
                    let parameters = alias.sort_parameters.iter().filter_map(|sort| match sort {
                        kore::Sort::Variable(name) => Some(Name::from(name.as_str())),
                        _ => None,
                    });
                    let mut ctx = VerifyContext::new(
                        &module.name,
                        SentenceContext::Alias(alias.name.clone()),
                        sorts,
                        symbols,
                        aliases,
                        parameters,
                    );
                    for variable in variables {
                        let sort = ctx
                            .sort(&variable.sort)
                            .map_err(DefinitionError::Verification)?;
                        ctx.bound.push(((variable.kind, variable.name), sort));
                    }
                    let actual = ctx.pattern(right).map_err(DefinitionError::Verification)?;
                    let expected = ctx
                        .sort(result_sort)
                        .map_err(DefinitionError::Verification)?;
                    ctx.expect_sort(&expected, actual)
                        .map_err(DefinitionError::Verification)?;
                    if let Some((_, name)) = ctx.free.keys().next() {
                        return Err(DefinitionError::Verification(
                            ctx.error(format!("Unquantified variable: {name}")),
                        ));
                    }
                }
                kore::Sentence::Axiom {
                    parameters,
                    pattern,
                    attributes,
                } => {
                    let mut ctx = VerifyContext::new(
                        &module.name,
                        SentenceContext::Axiom { index: axiom_index },
                        sorts,
                        symbols,
                        aliases,
                        parameters.iter().map(|name| Name::from(name.as_str())),
                    );
                    ctx.pattern(pattern)
                        .map_err(DefinitionError::Verification)?;
                    verify_subsort_super(attributes, sorts, &ctx)?;
                    verify_function_head(pattern, attributes, symbols, &ctx)?;
                    axiom_index += 1;
                }
                kore::Sentence::Claim {
                    parameters,
                    pattern,
                    ..
                } => {
                    let mut ctx = VerifyContext::new(
                        &module.name,
                        SentenceContext::Claim { index: claim_index },
                        sorts,
                        symbols,
                        aliases,
                        parameters.iter().map(|name| Name::from(name.as_str())),
                    );
                    ctx.pattern(pattern)
                        .map_err(DefinitionError::Verification)?;
                    verify_claim_variables(pattern, &ctx)?;
                    claim_index += 1;
                }
                kore::Sentence::SortDeclaration { .. } => {}
                kore::Sentence::SymbolDeclaration { .. } => {}
                kore::Sentence::Import { .. } => {}
            }
        }
    }
    Ok(())
}

fn verify_declaration(
    module: &kore::Module,
    sentence: &kore::Sentence,
    sorts: &BTreeMap<Name, SortInfo>,
    symbols: &BTreeMap<Name, Arc<Symbol>>,
    aliases: &BTreeMap<String, AliasDefinition>,
) -> Result<(), DefinitionError> {
    match sentence {
        kore::Sentence::SortDeclaration {
            hooked,
            name,
            attributes,
            ..
        } => {
            let ctx = VerifyContext::new(
                &module.name,
                SentenceContext::Sort(name.clone()),
                sorts,
                symbols,
                aliases,
                Vec::new(),
            );
            verify_hook_attribute(*hooked, attributes, &ctx)
        }
        kore::Sentence::SymbolDeclaration {
            hooked,
            symbol,
            result_sort,
            attributes,
            ..
        } => {
            let ctx = VerifyContext::new(
                &module.name,
                SentenceContext::Symbol(symbol.name.clone()),
                sorts,
                symbols,
                aliases,
                symbol.sort_parameters.iter().filter_map(|sort| match sort {
                    kore::Sort::Variable(name) => Some(Name::from(name.as_str())),
                    _ => None,
                }),
            );
            verify_hook_attribute(*hooked, attributes, &ctx)?;
            if has_attribute(attributes, "constructor") {
                let result = ctx
                    .sort(result_sort)
                    .map_err(DefinitionError::Verification)?;
                match result {
                    Sort::Variable(_) => Err(DefinitionError::Verification(
                        ctx.error("Constructor result sort must not be a sort variable."),
                    )),
                    Sort::Application { name, .. }
                        if sorts
                            .get(&name)
                            .is_some_and(|info| info.hook.is_some() || info.has_domain_values) =>
                    {
                        Err(DefinitionError::Verification(ctx.error(
                            "Constructor result sort must not be hooked or have domain values.",
                        )))
                    }
                    Sort::Application { .. } => Ok(()),
                }
            } else {
                Ok(())
            }
        }
        _ => Ok(()),
    }
}

fn verify_hook_attribute(
    hooked: bool,
    attributes: &kore::Attributes,
    ctx: &VerifyContext<'_>,
) -> Result<(), DefinitionError> {
    match (hooked, has_attribute(attributes, "hook")) {
        (true, false) => Err(DefinitionError::Verification(
            ctx.error("Missing hook attribute."),
        )),
        (false, true) => Err(DefinitionError::Verification(
            ctx.error("Unexpected 'hook' attribute."),
        )),
        _ => Ok(()),
    }
}

pub(crate) fn verify_standalone(
    module: &str,
    pattern: &kore::Pattern,
    sorts: &BTreeMap<Name, SortInfo>,
    symbols: &BTreeMap<Name, Arc<Symbol>>,
    aliases: &BTreeMap<String, AliasDefinition>,
) -> Result<(), VerificationError> {
    let mut ctx = VerifyContext::new(
        module,
        SentenceContext::Standalone,
        sorts,
        symbols,
        aliases,
        Vec::new(),
    );
    ctx.pattern(pattern)?;
    Ok(())
}

fn verify_unique_names(modules: &[kore::Module]) -> Result<(), DefinitionError> {
    let mut names = BTreeMap::<String, String>::new();
    for module in modules {
        for sentence in &module.sentences {
            let name = match sentence {
                kore::Sentence::SortDeclaration { name, .. } => Some(name),
                kore::Sentence::SymbolDeclaration { symbol, .. }
                | kore::Sentence::AliasDeclaration { alias: symbol, .. } => Some(&symbol.name),
                _ => None,
            };
            if let Some(name) = name
                && let Some(first_module) = names.insert(name.clone(), module.name.clone())
            {
                return Err(DefinitionError::DuplicateName {
                    name: name.clone(),
                    first_module,
                    second_module: module.name.clone(),
                });
            }
        }
    }
    Ok(())
}

fn verify_attributes(
    module: &kore::Module,
    sentence: &kore::Sentence,
    sorts: &BTreeMap<Name, SortInfo>,
    symbols: &BTreeMap<Name, Arc<Symbol>>,
    aliases: &BTreeMap<String, AliasDefinition>,
) -> Result<(), DefinitionError> {
    let (attributes, context) = match sentence {
        kore::Sentence::Import { attributes, module } => {
            (attributes, SentenceContext::Symbol(module.clone()))
        }
        kore::Sentence::SortDeclaration {
            attributes, name, ..
        } => (attributes, SentenceContext::Sort(name.clone())),
        kore::Sentence::SymbolDeclaration {
            attributes, symbol, ..
        } => (attributes, SentenceContext::Symbol(symbol.name.clone())),
        kore::Sentence::AliasDeclaration {
            attributes, alias, ..
        } => (attributes, SentenceContext::Alias(alias.name.clone())),
        kore::Sentence::Axiom { attributes, .. } => {
            (attributes, SentenceContext::Axiom { index: 0 })
        }
        kore::Sentence::Claim { attributes, .. } => {
            (attributes, SentenceContext::Claim { index: 0 })
        }
    };
    if attributes
        .0
        .iter()
        .all(|attribute| matches!(attribute, kore::Pattern::Application { .. }))
    {
        Ok(())
    } else {
        let ctx = VerifyContext::new(&module.name, context, sorts, symbols, aliases, Vec::new());
        Err(DefinitionError::Verification(
            ctx.error("Non-application attributes are not supported"),
        ))
    }
}

fn verify_subsort_super(
    attributes: &kore::Attributes,
    sorts: &BTreeMap<Name, SortInfo>,
    ctx: &VerifyContext<'_>,
) -> Result<(), DefinitionError> {
    let Some(kore::Pattern::Application { symbol, .. }) = attribute(attributes, "subsort") else {
        return Ok(());
    };
    let Some(kore::Sort::Application { name, .. }) = symbol.sort_parameters.get(1) else {
        return Ok(());
    };
    if sorts
        .get(name.as_str())
        .is_some_and(|info| info.has_domain_values)
    {
        Err(DefinitionError::Verification(
            ctx.error("Hooked sorts may not have subsorts."),
        ))
    } else {
        Ok(())
    }
}

fn verify_function_head(
    pattern: &kore::Pattern,
    attributes: &kore::Attributes,
    symbols: &BTreeMap<Name, Arc<Symbol>>,
    ctx: &VerifyContext<'_>,
) -> Result<(), DefinitionError> {
    if [
        "simplification",
        "assoc",
        "comm",
        "unit",
        "idem",
        "symbol-overload",
        "overload",
    ]
    .iter()
    .any(|name| has_attribute(attributes, name))
    {
        return Ok(());
    }
    let kore::Pattern::Implies { right, .. } = pattern else {
        return Ok(());
    };
    let kore::Pattern::Equals { left, .. } = right.as_ref() else {
        return Ok(());
    };
    let kore::Pattern::Application { symbol, arguments } = left.as_ref() else {
        return Ok(());
    };
    if !arguments
        .iter()
        .all(|argument| matches!(argument, kore::Pattern::Variable(_)))
    {
        return Err(DefinitionError::Verification(
            ctx.error("Found invalid subterm in argument of function equation:"),
        ));
    }
    if symbols
        .get(symbol.name.as_str())
        .is_some_and(|symbol| symbol.attributes.symbol_type == SymbolType::Constructor)
    {
        return Err(DefinitionError::Verification(
            ctx.error("Expected function symbol, but found constructor symbol:"),
        ));
    }
    Ok(())
}

fn verify_claim_variables(
    pattern: &kore::Pattern,
    ctx: &VerifyContext<'_>,
) -> Result<(), DefinitionError> {
    let kore::Pattern::Implies { left, right, .. } = pattern else {
        return Ok(());
    };
    let kore::Pattern::Application { symbol, .. } = right.as_ref() else {
        return Ok(());
    };
    if !matches!(
        symbol.name.as_str(),
        "weakExistsFinally" | "weakAlwaysFinally"
    ) {
        return Ok(());
    }
    let lhs = free_variables(left, &mut Vec::new());
    let rhs = free_variables(right, &mut Vec::new());
    if rhs.difference(&lhs).next().is_some() {
        Err(DefinitionError::Verification(ctx.error(
            "Found claim with universally-quantified variables appearing only on the right-hand side",
        )))
    } else {
        Ok(())
    }
}

fn free_variables(
    pattern: &kore::Pattern,
    bound: &mut Vec<(kore::VariableKind, String)>,
) -> BTreeSet<(kore::VariableKind, String)> {
    use kore::Pattern;
    match pattern {
        Pattern::Variable(variable) => {
            let key = (variable.kind, variable.name.clone());
            if bound.contains(&key) {
                BTreeSet::new()
            } else {
                BTreeSet::from([key])
            }
        }
        Pattern::Application { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. } => arguments
            .iter()
            .flat_map(|argument| free_variables(argument, bound))
            .collect(),
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => free_variables(argument, bound),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            let mut result = free_variables(left, bound);
            result.extend(free_variables(right, bound));
            result
        }
        Pattern::Exists { variable, body, .. }
        | Pattern::Forall { variable, body, .. }
        | Pattern::Mu { variable, body }
        | Pattern::Nu { variable, body } => {
            bound.push((variable.kind, variable.name.clone()));
            let result = free_variables(body, bound);
            bound.pop();
            result
        }
        Pattern::String(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => BTreeSet::new(),
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

fn render_sort(sort: &Sort) -> String {
    match sort {
        Sort::Variable(name) => name.to_string(),
        Sort::Application { name, arguments } => format!(
            "{}{{{}}}",
            name,
            arguments
                .iter()
                .map(render_sort)
                .collect::<Vec<_>>()
                .join(",")
        ),
    }
}
