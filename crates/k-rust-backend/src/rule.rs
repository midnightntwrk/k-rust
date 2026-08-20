//! Recognition of the axiom shapes emitted by the K frontend.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use k_rust_kore::kore::ast as kore;

use crate::{
    definition::{BackendDefinition, DefinitionError},
    substitution::{Substitution, substitute},
    term::{Name, Term, TermKind, Variable},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Predicate {
    True,
    False,
    Term(Term),
    Equals(Term, Term),
    Ceil(Term),
    Floor(Term),
    In(Term, Term),
    Not(Box<Predicate>),
    And(Vec<Predicate>),
    Or(Vec<Predicate>),
    Implies(Box<Predicate>, Box<Predicate>),
    Iff(Box<Predicate>, Box<Predicate>),
    Exists(Variable, Box<Predicate>),
    Forall(Variable, Box<Predicate>),
}

impl Predicate {
    pub fn free_variables(&self) -> BTreeSet<Variable> {
        match self {
            Self::True | Self::False => BTreeSet::new(),
            Self::Term(term) | Self::Ceil(term) | Self::Floor(term) => {
                term.attributes().variables.clone()
            }
            Self::Equals(left, right) | Self::In(left, right) => {
                let mut variables = left.attributes().variables.clone();
                variables.extend(right.attributes().variables.iter().cloned());
                variables
            }
            Self::Not(inner) => inner.free_variables(),
            Self::And(inner) | Self::Or(inner) => inner
                .iter()
                .flat_map(Self::free_variables)
                .collect::<BTreeSet<_>>(),
            Self::Implies(left, right) | Self::Iff(left, right) => {
                let mut variables = left.free_variables();
                variables.extend(right.free_variables());
                variables
            }
            Self::Exists(variable, inner) | Self::Forall(variable, inner) => {
                let mut variables = inner.free_variables();
                variables.remove(variable);
                variables
            }
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ComputedRuleAttributes {
    pub contains_ac_symbols: bool,
    pub undefined_symbols: BTreeSet<Name>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RewriteRule {
    pub lhs: Term,
    pub rhs: RuleRhs,
    pub requires: Vec<Predicate>,
    pub ensures: Vec<Predicate>,
    pub attributes: RuleAttributes,
    pub computed_attributes: ComputedRuleAttributes,
    pub existentials: BTreeSet<Variable>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RuleRhs {
    Term(Term),
    Predicates(Vec<Predicate>),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum TermIndex {
    Symbol(Name),
    Injection,
    Map,
    List,
    Set,
    DomainValue,
    Variable,
    And,
}

pub type Theory = BTreeMap<TermIndex, BTreeMap<u8, Vec<Arc<RewriteRule>>>>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuleKind {
    Rewrite,
    Function,
    Simplification,
    Ceil,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RulePatternError {
    MissingTerm,
    UnsupportedPredicate(&'static str),
    BinderSortMismatch(Variable),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConstraintKind {
    Concrete,
    Symbolic,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Concreteness {
    Unconstrained,
    All(ConstraintKind),
    Some(BTreeMap<(Name, Name), ConstraintKind>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuleAttributes {
    pub priority: u8,
    pub label: Option<String>,
    pub unique_id: String,
    pub simplification: bool,
    pub preserves_definedness: bool,
    pub concreteness: Concreteness,
    pub smt_lemma: bool,
    pub executable: bool,
    pub source: Option<String>,
    pub location: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArgumentBinder {
    pub variable: kore::Variable,
    pub pattern: kore::Pattern,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ClassifiedAxiom {
    Rewrite {
        module: Name,
        sort_parameters: Vec<Name>,
        lhs: kore::Pattern,
        rhs: kore::Pattern,
        existentials: Vec<kore::Variable>,
        attributes: RuleAttributes,
    },
    Function {
        module: Name,
        sort_parameters: Vec<Name>,
        requires: kore::Pattern,
        binders: Vec<ArgumentBinder>,
        lhs: kore::Pattern,
        rhs: kore::Pattern,
        attributes: RuleAttributes,
    },
    Simplification {
        module: Name,
        sort_parameters: Vec<Name>,
        requires: kore::Pattern,
        lhs: kore::Pattern,
        rhs: kore::Pattern,
        attributes: RuleAttributes,
    },
    Ceil {
        module: Name,
        sort_parameters: Vec<Name>,
        lhs: kore::Pattern,
        rhs: kore::Pattern,
        attributes: RuleAttributes,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AxiomError {
    MalformedRewrite,
    UnsupportedAliasRewrite(String),
    MalformedEquation,
    MalformedArgumentBinder,
    Unexpected,
    ConflictingPriorities(Vec<&'static str>),
    InvalidPriority(String),
    InvalidConcreteness(String),
    ConcretenessOverlap(String),
    MalformedAttribute(String),
}

pub fn classify_axiom(
    module: Name,
    sort_parameters: Vec<Name>,
    pattern: &kore::Pattern,
    syntax_attributes: &kore::Attributes,
) -> Result<Option<ClassifiedAxiom>, AxiomError> {
    let attributes = RuleAttributes::parse(syntax_attributes)?;
    match pattern {
        kore::Pattern::Rewrites { left, right, .. } => {
            if !matches!(left.as_ref(), kore::Pattern::And { .. }) {
                if let kore::Pattern::Application { symbol, .. } = left.as_ref() {
                    return Err(AxiomError::UnsupportedAliasRewrite(symbol.name.clone()));
                }
                return Err(AxiomError::MalformedRewrite);
            }
            let (rhs, existentials) = extract_existentials((**right).clone());
            Ok(Some(ClassifiedAxiom::Rewrite {
                module,
                sort_parameters,
                lhs: (**left).clone(),
                rhs,
                existentials,
                attributes,
            }))
        }
        kore::Pattern::Implies { left, right, .. } => {
            let kore::Pattern::Equals {
                left: equation_left,
                right: equation_right,
                ..
            } = right.as_ref()
            else {
                return if is_ignored_constructor_axiom(pattern, syntax_attributes) {
                    Ok(None)
                } else {
                    Err(AxiomError::Unexpected)
                };
            };
            if let kore::Pattern::Ceil { argument, .. } = equation_left.as_ref() {
                return Ok(Some(ClassifiedAxiom::Ceil {
                    module,
                    sort_parameters,
                    lhs: (**argument).clone(),
                    rhs: (**equation_right).clone(),
                    attributes,
                }));
            }
            if !matches!(equation_right.as_ref(), kore::Pattern::And { .. }) {
                return Err(AxiomError::MalformedEquation);
            }
            if attributes.simplification {
                return match equation_left.as_ref() {
                    kore::Pattern::Application { .. } => {
                        Ok(Some(ClassifiedAxiom::Simplification {
                            module,
                            sort_parameters,
                            requires: (**left).clone(),
                            lhs: (**equation_left).clone(),
                            rhs: (**equation_right).clone(),
                            attributes,
                        }))
                    }
                    _ => Ok(None),
                };
            }
            let kore::Pattern::Application { arguments, .. } = equation_left.as_ref() else {
                return Err(AxiomError::MalformedEquation);
            };
            if !arguments
                .iter()
                .all(|argument| matches!(argument, kore::Pattern::Variable(_)))
            {
                return Err(AxiomError::MalformedEquation);
            }
            let (requires, binders) = function_conditions(left, arguments.is_empty())?;
            Ok(Some(ClassifiedAxiom::Function {
                module,
                sort_parameters,
                requires,
                binders,
                lhs: (**equation_left).clone(),
                rhs: (**equation_right).clone(),
                attributes,
            }))
        }
        kore::Pattern::Exists { variable, body, .. }
            if matches!(body.as_ref(), kore::Pattern::Equals { left, .. }
                if matches!(left.as_ref(), kore::Pattern::Variable(found) if found == variable))
                && (has_attribute(syntax_attributes, "functional")
                    || has_attribute(syntax_attributes, "total")) =>
        {
            Ok(None)
        }
        kore::Pattern::Exists { .. } if has_attribute(syntax_attributes, "subsort") => Ok(None),
        kore::Pattern::Or { .. } | kore::Pattern::Bottom { .. }
            if has_attribute(syntax_attributes, "constructor") =>
        {
            Ok(None)
        }
        kore::Pattern::Not { .. } if has_attribute(syntax_attributes, "constructor") => Ok(None),
        kore::Pattern::Equals { left, right, .. }
            if [
                "assoc",
                "comm",
                "idem",
                "unit",
                "symbol-overload",
                "overload",
            ]
            .iter()
            .any(|name| has_attribute(syntax_attributes, name))
                || (has_attribute(syntax_attributes, "simplification")
                    && is_injection(left)
                    && is_injection(right)) =>
        {
            Ok(None)
        }
        _ => Err(AxiomError::Unexpected),
    }
}

pub fn internalize_axiom(
    definition: &BackendDefinition,
    axiom: &ClassifiedAxiom,
) -> Result<(RuleKind, RewriteRule), DefinitionError> {
    match axiom {
        ClassifiedAxiom::Rewrite {
            sort_parameters,
            lhs,
            rhs,
            existentials,
            attributes,
            ..
        } => {
            let (lhs, requires) = internalize_rule_pattern(definition, lhs, sort_parameters)?;
            let (rhs, ensures) = internalize_rule_pattern(definition, rhs, sort_parameters)?;
            let lhs = rename_term(&lhs, |variable| prefixed(variable, "Rule#"));
            let requires = rename_predicates(&requires, |variable| prefixed(variable, "Rule#"));
            let existential_variables = existentials
                .iter()
                .map(|variable| {
                    Ok(Variable::new(
                        variable.name.as_str(),
                        definition.internalize_syntax_sort(&variable.sort, sort_parameters)?,
                    ))
                })
                .collect::<Result<BTreeSet<_>, DefinitionError>>()?;
            let rhs_renaming = |variable: &Variable| {
                if existential_variables.contains(variable) {
                    prefixed(variable, "Ex#")
                } else {
                    prefixed(variable, "Rule#")
                }
            };
            let rhs = rename_term(&rhs, rhs_renaming);
            let ensures = rename_predicates(&ensures, rhs_renaming);
            let existentials = existential_variables
                .iter()
                .map(|variable| prefixed(variable, "Ex#"))
                .collect();
            Ok((
                RuleKind::Rewrite,
                make_rule(
                    lhs,
                    rhs,
                    requires,
                    ensures,
                    attributes.clone(),
                    existentials,
                ),
            ))
        }
        ClassifiedAxiom::Simplification {
            sort_parameters,
            requires,
            lhs,
            rhs,
            attributes,
            ..
        } => {
            let lhs = definition.internalize_term(lhs, sort_parameters)?;
            let requires = internalize_predicates(definition, requires, sort_parameters)?;
            let (rhs, ensures) = internalize_rule_pattern(definition, rhs, sort_parameters)?;
            let rename = |variable: &Variable| prefixed(variable, "Eq#");
            Ok((
                RuleKind::Simplification,
                make_rule(
                    rename_term(&lhs, rename),
                    rename_term(&rhs, rename),
                    rename_predicates(&requires, rename),
                    rename_predicates(&ensures, rename),
                    attributes.clone(),
                    BTreeSet::new(),
                ),
            ))
        }
        ClassifiedAxiom::Function {
            sort_parameters,
            requires,
            binders,
            lhs,
            rhs,
            attributes,
            ..
        } => {
            let mut lhs = definition.internalize_term(lhs, sort_parameters)?;
            let mut bindings = Substitution::new();
            for binder in binders {
                let variable = Variable::new(
                    binder.variable.name.as_str(),
                    definition.internalize_syntax_sort(&binder.variable.sort, sort_parameters)?,
                );
                let pattern = definition.internalize_term(&binder.pattern, sort_parameters)?;
                if variable.sort != pattern.sort() {
                    return Err(DefinitionError::RulePattern(
                        RulePatternError::BinderSortMismatch(variable),
                    ));
                }
                bindings.insert(variable, pattern);
            }
            lhs = substitute(&lhs, &bindings);
            let requires = internalize_predicates(definition, requires, sort_parameters)?;
            let (rhs, ensures) = internalize_rule_pattern(definition, rhs, sort_parameters)?;
            let rename = |variable: &Variable| prefixed(variable, "Eq#");
            Ok((
                RuleKind::Function,
                make_rule(
                    rename_term(&lhs, rename),
                    rename_term(&rhs, rename),
                    rename_predicates(&requires, rename),
                    rename_predicates(&ensures, rename),
                    attributes.clone(),
                    BTreeSet::new(),
                ),
            ))
        }
        ClassifiedAxiom::Ceil {
            sort_parameters,
            lhs,
            rhs,
            attributes,
            ..
        } => {
            let lhs = definition.internalize_term(lhs, sort_parameters)?;
            let rhs = internalize_predicates(definition, rhs, sort_parameters)?;
            let rename = |variable: &Variable| prefixed(variable, "Eq#");
            let lhs = rename_term(&lhs, rename);
            let rhs = rename_predicates(&rhs, rename);
            let computed_attributes = computed_attributes([&lhs]);
            Ok((
                RuleKind::Ceil,
                RewriteRule {
                    lhs,
                    rhs: RuleRhs::Predicates(rhs),
                    requires: Vec::new(),
                    ensures: Vec::new(),
                    attributes: attributes.clone(),
                    computed_attributes,
                    existentials: BTreeSet::new(),
                },
            ))
        }
    }
}

pub fn insert_theory(theory: &mut Theory, rule: RewriteRule) {
    theory
        .entry(term_index(&rule.lhs))
        .or_default()
        .entry(rule.attributes.priority)
        .or_default()
        .push(Arc::new(rule));
}

pub fn term_index(term: &Term) -> TermIndex {
    match term.kind() {
        TermKind::Application { symbol, .. } => TermIndex::Symbol(symbol.name.clone()),
        TermKind::Injection { .. } => TermIndex::Injection,
        TermKind::Map { .. } => TermIndex::Map,
        TermKind::List { .. } => TermIndex::List,
        TermKind::Set { .. } => TermIndex::Set,
        TermKind::DomainValue { .. } => TermIndex::DomainValue,
        TermKind::Variable(_) => TermIndex::Variable,
        TermKind::And(..) => TermIndex::And,
    }
}

pub(crate) fn internalize_rule_pattern(
    definition: &BackendDefinition,
    pattern: &kore::Pattern,
    sort_parameters: &[Name],
) -> Result<(Term, Vec<Predicate>), DefinitionError> {
    let mut components = Vec::new();
    flatten_and(pattern, &mut components);
    let mut terms = Vec::new();
    let mut predicates = Vec::new();
    for component in components {
        if is_term_pattern(component) {
            terms.push(definition.internalize_term(component, sort_parameters)?);
        } else {
            predicates.extend(internalize_predicates(
                definition,
                component,
                sort_parameters,
            )?);
        }
    }
    let mut terms = terms.into_iter();
    let Some(mut term) = terms.next() else {
        return Err(DefinitionError::RulePattern(RulePatternError::MissingTerm));
    };
    for other in terms {
        term = Term::and(term, other);
    }
    Ok((term, predicates))
}

fn internalize_predicates(
    definition: &BackendDefinition,
    pattern: &kore::Pattern,
    sort_parameters: &[Name],
) -> Result<Vec<Predicate>, DefinitionError> {
    match pattern {
        kore::Pattern::Top { .. } => Ok(Vec::new()),
        kore::Pattern::Bottom { .. } => Ok(vec![Predicate::False]),
        kore::Pattern::And { arguments, .. } => arguments
            .iter()
            .map(|argument| internalize_predicates(definition, argument, sort_parameters))
            .collect::<Result<Vec<_>, _>>()
            .map(|predicates| predicates.into_iter().flatten().collect()),
        kore::Pattern::Or { arguments, .. } => Ok(vec![Predicate::Or(
            arguments
                .iter()
                .map(|argument| internalize_one_predicate(definition, argument, sort_parameters))
                .collect::<Result<Vec<_>, _>>()?,
        )]),
        _ => Ok(vec![internalize_one_predicate(
            definition,
            pattern,
            sort_parameters,
        )?]),
    }
}

fn internalize_one_predicate(
    definition: &BackendDefinition,
    pattern: &kore::Pattern,
    sort_parameters: &[Name],
) -> Result<Predicate, DefinitionError> {
    let term = |pattern: &kore::Pattern| definition.internalize_term(pattern, sort_parameters);
    let predicate =
        |pattern: &kore::Pattern| internalize_one_predicate(definition, pattern, sort_parameters);
    match pattern {
        kore::Pattern::Top { .. } => Ok(Predicate::True),
        kore::Pattern::Bottom { .. } => Ok(Predicate::False),
        kore::Pattern::Equals { left, right, .. } => {
            Ok(Predicate::Equals(term(left)?, term(right)?))
        }
        kore::Pattern::Ceil { argument, .. } => Ok(Predicate::Ceil(term(argument)?)),
        kore::Pattern::Floor { argument, .. } => Ok(Predicate::Floor(term(argument)?)),
        kore::Pattern::In { left, right, .. } => Ok(Predicate::In(term(left)?, term(right)?)),
        kore::Pattern::Not { argument, .. } => Ok(Predicate::Not(Box::new(predicate(argument)?))),
        kore::Pattern::And { arguments, .. } => Ok(Predicate::And(
            arguments
                .iter()
                .map(predicate)
                .collect::<Result<Vec<_>, _>>()?,
        )),
        kore::Pattern::Or { arguments, .. } => Ok(Predicate::Or(
            arguments
                .iter()
                .map(predicate)
                .collect::<Result<Vec<_>, _>>()?,
        )),
        kore::Pattern::Implies { left, right, .. } => Ok(Predicate::Implies(
            Box::new(predicate(left)?),
            Box::new(predicate(right)?),
        )),
        kore::Pattern::Iff { left, right, .. } => Ok(Predicate::Iff(
            Box::new(predicate(left)?),
            Box::new(predicate(right)?),
        )),
        kore::Pattern::Exists { variable, body, .. } => Ok(Predicate::Exists(
            Variable::new(
                variable.name.as_str(),
                definition.internalize_syntax_sort(&variable.sort, sort_parameters)?,
            ),
            Box::new(predicate(body)?),
        )),
        kore::Pattern::Forall { variable, body, .. } => Ok(Predicate::Forall(
            Variable::new(
                variable.name.as_str(),
                definition.internalize_syntax_sort(&variable.sort, sort_parameters)?,
            ),
            Box::new(predicate(body)?),
        )),
        pattern if is_term_pattern(pattern) => Ok(Predicate::Term(term(pattern)?)),
        kore::Pattern::Next { .. } => Err(DefinitionError::RulePattern(
            RulePatternError::UnsupportedPredicate("next"),
        )),
        kore::Pattern::Rewrites { .. } => Err(DefinitionError::RulePattern(
            RulePatternError::UnsupportedPredicate("rewrites"),
        )),
        kore::Pattern::Mu { .. } => Err(DefinitionError::RulePattern(
            RulePatternError::UnsupportedPredicate("mu"),
        )),
        kore::Pattern::Nu { .. } => Err(DefinitionError::RulePattern(
            RulePatternError::UnsupportedPredicate("nu"),
        )),
        kore::Pattern::AssociativeApplication { .. } => unreachable!(),
        kore::Pattern::String(_)
        | kore::Pattern::Variable(_)
        | kore::Pattern::Application { .. }
        | kore::Pattern::DomainValue { .. } => unreachable!(),
    }
}

fn flatten_and<'a>(pattern: &'a kore::Pattern, output: &mut Vec<&'a kore::Pattern>) {
    if let kore::Pattern::And { arguments, .. } = pattern {
        for argument in arguments {
            flatten_and(argument, output);
        }
    } else {
        output.push(pattern);
    }
}

fn is_term_pattern(pattern: &kore::Pattern) -> bool {
    matches!(
        pattern,
        kore::Pattern::String(_)
            | kore::Pattern::Variable(_)
            | kore::Pattern::Application { .. }
            | kore::Pattern::DomainValue { .. }
            | kore::Pattern::AssociativeApplication { .. }
    )
}

fn make_rule(
    lhs: Term,
    rhs: Term,
    requires: Vec<Predicate>,
    ensures: Vec<Predicate>,
    attributes: RuleAttributes,
    existentials: BTreeSet<Variable>,
) -> RewriteRule {
    let mut computed_attributes = computed_attributes([&lhs, &rhs]);
    if attributes.preserves_definedness {
        computed_attributes.undefined_symbols.clear();
    }
    RewriteRule {
        lhs,
        rhs: RuleRhs::Term(rhs),
        requires,
        ensures,
        attributes,
        computed_attributes,
        existentials,
    }
}

fn computed_attributes<'a>(terms: impl IntoIterator<Item = &'a Term>) -> ComputedRuleAttributes {
    let mut result = ComputedRuleAttributes::default();
    for term in terms {
        visit_symbols(term, &mut |symbol| {
            result.contains_ac_symbols |=
                symbol.attributes.associative || symbol.attributes.idempotent;
            if symbol.attributes.symbol_type
                == crate::term::SymbolType::Function(crate::term::FunctionType::Partial)
            {
                result.undefined_symbols.insert(symbol.name.clone());
            }
        });
        visit_partial_collections(term, &mut |name| {
            result.undefined_symbols.insert(name.clone());
        });
    }
    result
}

fn visit_partial_collections(term: &Term, visitor: &mut impl FnMut(&Name)) {
    match term.kind() {
        TermKind::Application { arguments, .. } => {
            for argument in arguments {
                visit_partial_collections(argument, visitor);
            }
        }
        TermKind::And(left, right) => {
            visit_partial_collections(left, visitor);
            visit_partial_collections(right, visitor);
        }
        TermKind::Injection { term, .. } => visit_partial_collections(term, visitor),
        TermKind::Map {
            definition,
            entries,
            rest,
        } => {
            visitor(&definition.symbols.concat);
            for (key, value) in entries {
                visit_partial_collections(key, visitor);
                visit_partial_collections(value, visitor);
            }
            if let Some(rest) = rest {
                visit_partial_collections(rest, visitor);
            }
        }
        TermKind::List { heads, rest, .. } => {
            for head in heads {
                visit_partial_collections(head, visitor);
            }
            if let Some((middle, tails)) = rest {
                visit_partial_collections(middle, visitor);
                for tail in tails {
                    visit_partial_collections(tail, visitor);
                }
            }
        }
        TermKind::Set {
            definition,
            elements,
            rest,
        } => {
            visitor(&definition.symbols.concat);
            for element in elements {
                visit_partial_collections(element, visitor);
            }
            if let Some(rest) = rest {
                visit_partial_collections(rest, visitor);
            }
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
    }
}

fn visit_symbols(term: &Term, visitor: &mut impl FnMut(&crate::term::Symbol)) {
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => {
            visitor(symbol);
            for argument in arguments {
                visit_symbols(argument, visitor);
            }
        }
        TermKind::And(left, right) => {
            visit_symbols(left, visitor);
            visit_symbols(right, visitor);
        }
        TermKind::Injection { term, .. } => visit_symbols(term, visitor),
        TermKind::Map { entries, rest, .. } => {
            for (key, value) in entries {
                visit_symbols(key, visitor);
                visit_symbols(value, visitor);
            }
            if let Some(rest) = rest {
                visit_symbols(rest, visitor);
            }
        }
        TermKind::List { heads, rest, .. } => {
            for head in heads {
                visit_symbols(head, visitor);
            }
            if let Some((middle, tails)) = rest {
                visit_symbols(middle, visitor);
                for tail in tails {
                    visit_symbols(tail, visitor);
                }
            }
        }
        TermKind::Set { elements, rest, .. } => {
            for element in elements {
                visit_symbols(element, visitor);
            }
            if let Some(rest) = rest {
                visit_symbols(rest, visitor);
            }
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
    }
}

fn prefixed(variable: &Variable, prefix: &str) -> Variable {
    Variable::new(format!("{prefix}{}", variable.name), variable.sort.clone())
}

fn rename_term(term: &Term, rename: impl Fn(&Variable) -> Variable) -> Term {
    let substitution = term
        .attributes()
        .variables
        .iter()
        .cloned()
        .map(|variable| {
            let renamed = Term::variable(rename(&variable));
            (variable, renamed)
        })
        .collect::<Substitution>();
    substitute(term, &substitution)
}

fn rename_predicates(
    predicates: &[Predicate],
    rename: impl Copy + Fn(&Variable) -> Variable,
) -> Vec<Predicate> {
    predicates
        .iter()
        .map(|predicate| rename_predicate(predicate, rename))
        .collect()
}

fn rename_predicate(
    predicate: &Predicate,
    rename: impl Copy + Fn(&Variable) -> Variable,
) -> Predicate {
    match predicate {
        Predicate::True => Predicate::True,
        Predicate::False => Predicate::False,
        Predicate::Term(term) => Predicate::Term(rename_term(term, rename)),
        Predicate::Equals(left, right) => {
            Predicate::Equals(rename_term(left, rename), rename_term(right, rename))
        }
        Predicate::Ceil(term) => Predicate::Ceil(rename_term(term, rename)),
        Predicate::Floor(term) => Predicate::Floor(rename_term(term, rename)),
        Predicate::In(left, right) => {
            Predicate::In(rename_term(left, rename), rename_term(right, rename))
        }
        Predicate::Not(inner) => Predicate::Not(Box::new(rename_predicate(inner, rename))),
        Predicate::And(inner) => Predicate::And(rename_predicates(inner, rename)),
        Predicate::Or(inner) => Predicate::Or(rename_predicates(inner, rename)),
        Predicate::Implies(left, right) => Predicate::Implies(
            Box::new(rename_predicate(left, rename)),
            Box::new(rename_predicate(right, rename)),
        ),
        Predicate::Iff(left, right) => Predicate::Iff(
            Box::new(rename_predicate(left, rename)),
            Box::new(rename_predicate(right, rename)),
        ),
        Predicate::Exists(variable, inner) => {
            Predicate::Exists(rename(variable), Box::new(rename_predicate(inner, rename)))
        }
        Predicate::Forall(variable, inner) => {
            Predicate::Forall(rename(variable), Box::new(rename_predicate(inner, rename)))
        }
    }
}

impl RuleAttributes {
    pub fn parse(attributes: &kore::Attributes) -> Result<Self, AxiomError> {
        let priority = attribute_string(attributes, "priority")?;
        let simplification_priority = attribute_string_or_empty(attributes, "simplification")?;
        let owise = has_attribute(attributes, "owise");
        let present = [
            priority.as_ref().map(|_| "priority"),
            simplification_priority.as_ref().map(|_| "simplification"),
            owise.then_some("owise"),
        ]
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
        if present.len() > 1 {
            return Err(AxiomError::ConflictingPriorities(present));
        }
        let priority = if owise {
            u8::MAX
        } else {
            priority
                .or(simplification_priority)
                .map(|value| {
                    if value.is_empty() {
                        Ok(50)
                    } else {
                        value
                            .parse::<u8>()
                            .map_err(|_| AxiomError::InvalidPriority(value))
                    }
                })
                .transpose()?
                .unwrap_or(50)
        };
        let label = attribute_string(attributes, "label")?;
        let unique_id = attribute_string(attributes, "UNIQUE'Unds'ID")?
            .or_else(|| label.clone())
            .unwrap_or_else(|| "UNKNOWN".into());
        Ok(Self {
            priority,
            label,
            unique_id,
            simplification: has_attribute(attributes, "simplification"),
            preserves_definedness: has_attribute(attributes, "preserves-definedness"),
            concreteness: parse_concreteness(attributes)?,
            smt_lemma: has_attribute(attributes, "smt-lemma"),
            executable: !has_attribute(attributes, "non-executable"),
            source: attribute_string(
                attributes,
                "org'Stop'kframework'Stop'attributes'Stop'Source",
            )?,
            location: attribute_string(
                attributes,
                "org'Stop'kframework'Stop'attributes'Stop'Location",
            )?,
        })
    }
}

fn function_conditions(
    condition: &kore::Pattern,
    nullary: bool,
) -> Result<(kore::Pattern, Vec<ArgumentBinder>), AxiomError> {
    let kore::Pattern::And { arguments, .. } = condition else {
        return Err(AxiomError::MalformedEquation);
    };
    let [first, second] = arguments.as_slice() else {
        return Err(AxiomError::MalformedEquation);
    };
    if nullary && matches!(second, kore::Pattern::Top { .. }) {
        return Ok((first.clone(), Vec::new()));
    }
    if let kore::Pattern::And { arguments, .. } = second
        && arguments
            .first()
            .is_some_and(|pattern| matches!(pattern, kore::Pattern::In { .. }))
    {
        return Ok((first.clone(), extract_binders(second)?));
    }
    if let kore::Pattern::And { arguments, .. } = second
        && let [requires, binders] = arguments.as_slice()
    {
        return Ok((requires.clone(), extract_binders(binders)?));
    }
    Err(AxiomError::MalformedEquation)
}

fn extract_binders(pattern: &kore::Pattern) -> Result<Vec<ArgumentBinder>, AxiomError> {
    match pattern {
        kore::Pattern::Top { .. } => Ok(Vec::new()),
        kore::Pattern::In { left, right, .. } => {
            let kore::Pattern::Variable(variable) = left.as_ref() else {
                return Err(AxiomError::MalformedArgumentBinder);
            };
            Ok(vec![ArgumentBinder {
                variable: variable.clone(),
                pattern: (**right).clone(),
            }])
        }
        kore::Pattern::And { arguments, .. } => {
            let [first, rest] = arguments.as_slice() else {
                return Err(AxiomError::MalformedArgumentBinder);
            };
            let kore::Pattern::In { left, right, .. } = first else {
                return Err(AxiomError::MalformedArgumentBinder);
            };
            let kore::Pattern::Variable(variable) = left.as_ref() else {
                return Err(AxiomError::MalformedArgumentBinder);
            };
            let mut result = vec![ArgumentBinder {
                variable: variable.clone(),
                pattern: (**right).clone(),
            }];
            result.extend(extract_binders(rest)?);
            Ok(result)
        }
        _ => Err(AxiomError::MalformedArgumentBinder),
    }
}

fn extract_existentials(mut pattern: kore::Pattern) -> (kore::Pattern, Vec<kore::Variable>) {
    let mut variables = Vec::new();
    while let kore::Pattern::Exists { variable, body, .. } = pattern {
        variables.push(variable);
        pattern = *body;
    }
    (pattern, variables)
}

fn parse_concreteness(attributes: &kore::Attributes) -> Result<Concreteness, AxiomError> {
    let concrete = attribute_constrained_variables(attributes, "concrete")?;
    let symbolic = attribute_constrained_variables(attributes, "symbolic")?;
    match (concrete, symbolic) {
        (None, None) => Ok(Concreteness::Unconstrained),
        (Some(concrete), Some(_)) if concrete.is_empty() => {
            Err(AxiomError::ConcretenessOverlap("all concrete".into()))
        }
        (Some(_), Some(symbolic)) if symbolic.is_empty() => {
            Err(AxiomError::ConcretenessOverlap("all symbolic".into()))
        }
        (Some(concrete), None) if concrete.is_empty() => {
            Ok(Concreteness::All(ConstraintKind::Concrete))
        }
        (None, Some(symbolic)) if symbolic.is_empty() => {
            Ok(Concreteness::All(ConstraintKind::Symbolic))
        }
        (concrete, symbolic) => {
            let concrete = concrete.unwrap_or_default();
            let symbolic = symbolic.unwrap_or_default();
            let concrete = parse_constrained_variables(concrete, ConstraintKind::Concrete)?;
            let symbolic = parse_constrained_variables(symbolic, ConstraintKind::Symbolic)?;
            let overlap = concrete
                .keys()
                .collect::<BTreeSet<_>>()
                .intersection(&symbolic.keys().collect())
                .next()
                .cloned();
            if let Some((name, sort)) = overlap {
                return Err(AxiomError::ConcretenessOverlap(format!("{name}:{sort}")));
            }
            Ok(Concreteness::Some(
                concrete.into_iter().chain(symbolic).collect(),
            ))
        }
    }
}

fn attribute_constrained_variables(
    attributes: &kore::Attributes,
    name: &str,
) -> Result<Option<Vec<String>>, AxiomError> {
    let Some(arguments) = attribute_application(attributes, name) else {
        return Ok(None);
    };
    arguments
        .iter()
        .map(|argument| match argument {
            kore::Pattern::Variable(variable) => {
                let kore::Sort::Application {
                    name: sort,
                    arguments,
                } = &variable.sort
                else {
                    return Err(AxiomError::MalformedAttribute(name.into()));
                };
                if !arguments.is_empty() {
                    return Err(AxiomError::MalformedAttribute(name.into()));
                }
                Ok(format!("{}:{sort}", variable.name))
            }
            // Older generated definitions encoded the same pair as a string.
            kore::Pattern::String(value) => Ok(value.clone()),
            _ => Err(AxiomError::MalformedAttribute(name.into())),
        })
        .collect::<Result<Vec<_>, _>>()
        .map(Some)
}

fn parse_constrained_variables(
    variables: Vec<String>,
    kind: ConstraintKind,
) -> Result<BTreeMap<(Name, Name), ConstraintKind>, AxiomError> {
    variables
        .into_iter()
        .map(|variable| {
            let Some((name, sort)) = variable.split_once(':') else {
                return Err(AxiomError::InvalidConcreteness(variable));
            };
            Ok(((Name::from(name), Name::from(sort)), kind))
        })
        .collect()
}

fn is_ignored_constructor_axiom(pattern: &kore::Pattern, attributes: &kore::Attributes) -> bool {
    has_attribute(attributes, "constructor") && matches!(pattern, kore::Pattern::Implies { .. })
}

fn is_injection(pattern: &kore::Pattern) -> bool {
    matches!(pattern, kore::Pattern::Application { symbol, .. } if symbol.name == "inj")
}

fn has_attribute(attributes: &kore::Attributes, name: &str) -> bool {
    attribute_application(attributes, name).is_some()
}

fn attribute_application<'a>(
    attributes: &'a kore::Attributes,
    name: &str,
) -> Option<&'a Vec<kore::Pattern>> {
    attributes.0.iter().find_map(|attribute| match attribute {
        kore::Pattern::Application { symbol, arguments } if symbol.name == name => Some(arguments),
        _ => None,
    })
}

fn attribute_string(
    attributes: &kore::Attributes,
    name: &str,
) -> Result<Option<String>, AxiomError> {
    let Some(arguments) = attribute_application(attributes, name) else {
        return Ok(None);
    };
    match arguments.as_slice() {
        [kore::Pattern::String(value)] => Ok(Some(value.clone())),
        _ => Err(AxiomError::MalformedAttribute(name.into())),
    }
}

fn attribute_string_or_empty(
    attributes: &kore::Attributes,
    name: &str,
) -> Result<Option<String>, AxiomError> {
    let Some(arguments) = attribute_application(attributes, name) else {
        return Ok(None);
    };
    match arguments.as_slice() {
        [] => Ok(Some(String::new())),
        [kore::Pattern::String(value)] => Ok(Some(value.clone())),
        _ => Err(AxiomError::MalformedAttribute(name.into())),
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::parse_sentence;

    use super::*;

    fn classify(source: &str) -> Result<Option<ClassifiedAxiom>, AxiomError> {
        let sentence = parse_sentence(source).expect("axiom should parse");
        let kore::Sentence::Axiom {
            parameters,
            pattern,
            attributes,
        } = sentence
        else {
            panic!("expected axiom");
        };
        classify_axiom(
            "MAIN".into(),
            parameters.into_iter().map(Into::into).collect(),
            &pattern,
            &attributes,
        )
    }

    #[test]
    fn classifies_rewrites_and_extracts_rhs_existentials() {
        let classified = classify(
            r#"axiom{} \rewrites{S{}}(
                \and{S{}}(lhs{}(X:S{}), \top{S{}}()),
                \exists{S{}}(Y:S{}, rhs{}(Y:S{}))
            ) [label{}("step"), priority{}("42")]"#,
        )
        .expect("axiom should classify")
        .expect("axiom should be executable");

        let ClassifiedAxiom::Rewrite {
            existentials,
            attributes,
            ..
        } = classified
        else {
            panic!("expected rewrite");
        };
        assert_eq!(existentials.len(), 1);
        assert_eq!(existentials[0].name, "Y");
        assert_eq!(attributes.priority, 42);
        assert_eq!(attributes.label.as_deref(), Some("step"));
        assert_eq!(attributes.unique_id, "step");
    }

    #[test]
    fn classifies_function_argument_binders() {
        let classified = classify(
            r#"axiom{R} \implies{R}(
                \and{R}(
                    \top{R}(),
                    \and{R}(
                        \in{S{}, R}(X:S{}, arg{}()),
                        \top{R}()
                    )
                ),
                \equals{S{}, R}(
                    f{}(X:S{}),
                    \and{S{}}(result{}(), \top{S{}}())
                )
            ) [concrete{}(X:S{})]"#,
        )
        .expect("axiom should classify")
        .expect("axiom should be executable");

        let ClassifiedAxiom::Function {
            binders,
            attributes,
            ..
        } = classified
        else {
            panic!("expected function equation");
        };
        assert_eq!(binders.len(), 1);
        assert_eq!(binders[0].variable.name, "X");
        assert_eq!(
            attributes.concreteness,
            Concreteness::Some(BTreeMap::from([(
                (Name::from("X"), Name::from("S")),
                ConstraintKind::Concrete,
            )]))
        );
    }

    #[test]
    fn classifies_simplifications_with_the_reference_default_priority() {
        let classified = classify(
            r#"axiom{R} \implies{R}(
                \top{R}(),
                \equals{S{}, R}(f{}(X:S{}), \and{S{}}(X:S{}, \top{S{}}()))
            ) [simplification{}()]"#,
        )
        .expect("axiom should classify")
        .expect("axiom should be executable");

        let ClassifiedAxiom::Simplification { attributes, .. } = classified else {
            panic!("expected simplification");
        };
        assert!(attributes.simplification);
        assert_eq!(attributes.priority, 50);
    }

    #[test]
    fn ignores_generated_constructor_axioms() {
        assert_eq!(
            classify(r#"axiom{} \or{S{}}(constructor{}(), \bottom{S{}}()) [constructor{}()]"#),
            Ok(None)
        );
    }

    #[test]
    fn rejects_conflicting_priority_attributes() {
        assert_eq!(
            classify(
                r#"axiom{} \rewrites{S{}}(
                    \and{S{}}(lhs{}(), \top{S{}}()), rhs{}()
                ) [priority{}("10"), owise{}()]"#
            ),
            Err(AxiomError::ConflictingPriorities(vec!["priority", "owise"]))
        );
    }
}
