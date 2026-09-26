//! ```toml algorithm
//! id = "backend.rule.select"
//! name = "single-symbol rule selection"
//! sites = ["applicable_groups", "applicable_rewrite_groups", "term_index", "rule_index", "subject_index", "fetch_k_cell", "first_with_k_cell", "find_k_cells"]
//! variable = "k = index keys; c = candidate rules returned for one step; r = rules stored under the subject's key and the Variable key; d = depth of the subject's one <k> cell; a = children of a node on the path to it"
//! counters = []
//! span = "per call"
//! no_counter = "rule selection has no dedicated counter; RewriteRuleAttempts is bumped by apply_rule_with_match for each candidate the caller tries"
//! lean = ["KRust.TermAttributes.rule_index_same"]
//!
//! [[cost]]
//! mode = "one subject"
//! bound = "O(log k) index lookups plus O(r) covers checks plus O(c) candidate clones"
//!
//! [[cost]]
//! mode = "subject_index"
//! bound = "O(1) unless the subject's stored k_cells count is 1, then O(d x a) to fetch the cell"
//! ```
//!
//! Axiom-shape classification and rule indexes. Every theory uses the top-symbol `TermIndex`;
//! rewrite rules additionally filter by the head of their `<k>` cell. Candidate count is the old
//! exact-symbol then variable-symbol sequence filtered by `rule.index.covers(subject_index)`, so
//! priority and declaration order remain unchanged. Selection costs O(log k) index lookups plus
//! one `covers` check per rule stored under the subject's key and the `Variable` key;
//! `Counter::RewriteRuleAttempts` is bumped by the caller per candidate tried.
//!
//! The index uses `Anything` for absent or malformed `<k>` cells, variables, overloaded heads,
//! associative or idempotent heads, and subject-side functions. It strips injections and meets
//! conjunctions. These conservative cases correspond to the matcher's overload, AC, variable,
//! injection, and symbolic-function paths; a later matcher extension must keep this list sound.

use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use k_rust_kore::kore::ast::{self as kore, KoreString};
use k_rust_kore::kore::walk;
use k_rust_kore::measure::{self, Algorithm};
use k_rust_kore::names::{KoreAttribute, MalformedAttribute, WellKnownSymbol};

use crate::{
    definition::{BackendDefinition, DefinitionError, SubsortValidation},
    substitution::{Substitution, substitute},
    term::{Name, SymbolType, Term, TermKind, Variable, names::VariableProvenance},
};

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
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
    /// Visit every term carried by this predicate, including nested logical predicates.
    pub fn visit_terms(&self, visitor: &mut impl FnMut(&Term)) {
        match self {
            Self::True | Self::False => {}
            Self::Term(term) | Self::Ceil(term) | Self::Floor(term) => visitor(term),
            Self::Equals(left, right) | Self::In(left, right) => {
                visitor(left);
                visitor(right);
            }
            Self::Not(inner) | Self::Exists(_, inner) | Self::Forall(_, inner) => {
                inner.visit_terms(visitor);
            }
            Self::And(inner) | Self::Or(inner) => {
                for predicate in inner {
                    predicate.visit_terms(visitor);
                }
            }
            Self::Implies(left, right) | Self::Iff(left, right) => {
                left.visit_terms(visitor);
                right.visit_terms(visitor);
            }
        }
    }

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
    /// Every variable of the rule, free or bound by a quantifier of a condition.
    pub variables: BTreeSet<Variable>,
    /// The free variables of the right-hand side, requires and ensures that the left-hand side
    /// does not bind and that are not existentials.
    pub unbound_variables: BTreeSet<Variable>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RewriteRule {
    pub lhs: Term,
    pub lhs_alternative: Option<usize>,
    pub rhs: RuleRhs,
    pub requires: Vec<Predicate>,
    pub ensures: Vec<Predicate>,
    pub attributes: RuleAttributes,
    pub computed_attributes: ComputedRuleAttributes,
    pub existentials: BTreeSet<Variable>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PredicateRewriteRule {
    pub lhs: Predicate,
    pub rhs: Vec<Predicate>,
    pub requires: Vec<Predicate>,
    pub attributes: RuleAttributes,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RhsAlternative {
    pub term: Term,
    pub ensures: Vec<Predicate>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RuleRhs {
    Term(Term),
    Disjunction(Vec<RhsAlternative>),
    Top,
    Bottom,
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

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CellIndex {
    None,
    Anything,
    Constructor(Name),
    Function(Name),
    Value(KoreString),
    Map,
    List,
    Set,
}

impl CellIndex {
    pub fn covers(&self, subject: &Self) -> bool {
        !matches!(self, Self::None)
            && (matches!(self, Self::Anything)
                || matches!(subject, Self::Anything)
                || self == subject)
    }

    pub fn meet(self, other: Self) -> Self {
        match (self, other) {
            (Self::None, _) | (_, Self::None) => Self::None,
            (Self::Anything, other) | (other, Self::Anything) => other,
            (left, right) if left == right => left,
            _ => Self::None,
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RuleIndex(Vec<CellIndex>);

impl RuleIndex {
    pub fn covers(&self, subject: &Self) -> bool {
        self.0.len() == subject.0.len()
            && self
                .0
                .iter()
                .zip(&subject.0)
                .all(|(rule, subject)| rule.covers(subject))
    }

    pub fn cells(&self) -> &[CellIndex] {
        &self.0
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IndexedRewriteRule {
    pub rule: Arc<RewriteRule>,
    pub index: RuleIndex,
}

impl std::ops::Deref for IndexedRewriteRule {
    type Target = RewriteRule;

    fn deref(&self) -> &Self::Target {
        &self.rule
    }
}

pub type Theory = BTreeMap<TermIndex, BTreeMap<u8, Vec<Arc<RewriteRule>>>>;
pub type RewriteTheory = BTreeMap<TermIndex, BTreeMap<u8, Vec<IndexedRewriteRule>>>;
pub type PredicateTheory = BTreeMap<u8, Vec<Arc<PredicateRewriteRule>>>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuleKind {
    Rewrite,
    Function,
    Simplification,
    Ceil,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum InternalizedRule {
    Term(RuleKind, RewriteRule),
    Predicate(PredicateRewriteRule),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RulePatternError {
    MissingTerm,
    TermDisjunction,
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
    /// Every written axiom sentence this rule was internalized from, in declaration order.
    ///
    /// Parsing one sentence yields one origin. Internalization collapses axioms that are equal
    /// up to their origins and a renaming of variables into one rule
    /// (`collapse_equal_axioms`); the collapsed rule lists each collapsed sentence once, the
    /// first being the representative whose variable names the rule keeps. The list is never
    /// empty, and no other field of these attributes is provenance.
    pub origins: Vec<RuleOrigin>,
}

/// The written position of one axiom sentence: its KORE `Source` and `Location` attributes,
/// each absent when the sentence does not carry it.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RuleOrigin {
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
        requires: kore::Pattern,
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

impl From<MalformedAttribute> for AxiomError {
    /// The payload is the attribute's KORE name, as the backend has always reported it.
    fn from(malformed: MalformedAttribute) -> Self {
        Self::MalformedAttribute(malformed.attribute.as_str().into())
    }
}

/// ```toml algorithm-site
/// id = "backend.definition.internalize"
/// role = "part"
/// sites = ["classify_axiom"]
/// ```
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
                    requires: (**left).clone(),
                    lhs: (**argument).clone(),
                    rhs: (**equation_right).clone(),
                    attributes,
                }));
            }
            if !matches!(equation_right.as_ref(), kore::Pattern::And { .. }) {
                return Err(AxiomError::MalformedEquation);
            }
            if attributes.simplification {
                return Ok(Some(ClassifiedAxiom::Simplification {
                    module,
                    sort_parameters,
                    requires: (**left).clone(),
                    lhs: (**equation_left).clone(),
                    rhs: (**equation_right).clone(),
                    attributes,
                }));
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
                && (syntax_attributes.has(KoreAttribute::Functional)
                    || syntax_attributes.has(KoreAttribute::Total)) =>
        {
            Ok(None)
        }
        kore::Pattern::Exists { .. } if syntax_attributes.has(KoreAttribute::Subsort) => Ok(None),
        kore::Pattern::Or { .. } | kore::Pattern::Bottom { .. }
            if syntax_attributes.has(KoreAttribute::Constructor) =>
        {
            Ok(None)
        }
        kore::Pattern::Not { .. } if syntax_attributes.has(KoreAttribute::Constructor) => Ok(None),
        kore::Pattern::Equals {
            result_sort,
            left,
            right,
            ..
        } if syntax_attributes.has(KoreAttribute::SymbolOverload)
            || syntax_attributes.has(KoreAttribute::Overload) =>
        {
            if !matches!(left.as_ref(), kore::Pattern::Application { .. }) {
                return Err(AxiomError::MalformedEquation);
            }
            Ok(Some(ClassifiedAxiom::Function {
                module,
                sort_parameters,
                requires: kore::Pattern::Top {
                    sort: result_sort.clone(),
                },
                binders: Vec::new(),
                lhs: (**left).clone(),
                rhs: (**right).clone(),
                attributes,
            }))
        }
        kore::Pattern::Equals { left, right, .. }
            if [
                KoreAttribute::Assoc,
                KoreAttribute::Comm,
                KoreAttribute::Idem,
                KoreAttribute::Unit,
            ]
            .into_iter()
            .any(|attribute| syntax_attributes.has(attribute))
                || (syntax_attributes.has(KoreAttribute::Simplification)
                    && is_injection(left)
                    && is_injection(right)) =>
        {
            Ok(None)
        }
        _ => Err(AxiomError::Unexpected),
    }
}

impl ClassifiedAxiom {
    pub fn attributes(&self) -> &RuleAttributes {
        match self {
            Self::Rewrite { attributes, .. }
            | Self::Function { attributes, .. }
            | Self::Simplification { attributes, .. }
            | Self::Ceil { attributes, .. } => attributes,
        }
    }

    fn attributes_mut(&mut self) -> &mut RuleAttributes {
        match self {
            Self::Rewrite { attributes, .. }
            | Self::Function { attributes, .. }
            | Self::Simplification { attributes, .. }
            | Self::Ceil { attributes, .. } => attributes,
        }
    }
}

/// Identity of one KORE axiom sentence: the module that declares it and its index among that
/// module's sentences. A sentence reached through two import paths has one key.
pub(crate) type SentenceKey = (Name, usize);

/// ```toml algorithm-site
/// id = "backend.definition.internalize"
/// role = "part"
/// sites = ["collapse_equal_axioms"]
/// ```
///
/// Collapses classified axioms that denote one rule into one axiom that lists every origin.
///
/// Two axioms denote one rule when they are equal after erasing their origins and renaming
/// variables: the same variant with the same sort parameters, every other attribute equal
/// (priority, label, `UNIQUE_ID`, simplification, preserves-definedness, concreteness,
/// smt-lemma, executability), and patterns that coincide under one bijection between variable
/// names applied to the whole axiom at once. The one bijection covers the left-hand side, the
/// right-hand side with its ensures, the requires, function argument binders, existentials and
/// the variables that `concrete`/`symbolic` name, so a variable shared between the left-hand
/// side and a side condition or a concreteness constraint is renamed identically in each, and
/// binders keep the variables they capture because the renaming is injective. A `concrete` or
/// `symbolic` entry that names no variable of the patterns constrains nothing and is dropped
/// before the comparison (`VariableRenaming::concreteness`). Sorts, sort
/// parameters, symbols and domain values are compared literally. Under such a renaming the
/// two axioms have the same instances: the same matches, substitutions, side conditions,
/// results and applicability constraints, so no execution fact tells an application of one
/// from an application of the other, and storing both only makes one rule apply twice. The
/// declaring module is not compared because no later stage reads it.
///
/// The first axiom of a class in declaration order is kept with its variable names, and the
/// origins of the others are appended to its origin list in declaration order. A sentence
/// visited again through another import path adds no origin. Axioms that share a `UNIQUE_ID`
/// but differ in anything compared above stay separate rules. Each axiom is hashed once by its
/// `UNIQUE_ID` and a shape that ignores variable names (`axiom_shape`), and comparisons, each
/// one traversal of the smaller axiom, run only between axioms with one hash key, so a
/// definition without `UNIQUE_ID`s does not compare every pair of its axioms.
pub(crate) fn collapse_equal_axioms(
    axioms: impl IntoIterator<Item = (ClassifiedAxiom, SentenceKey)>,
) -> Vec<ClassifiedAxiom> {
    let mut collapsed = Vec::<ClassifiedAxiom>::new();
    let mut sentences = Vec::<Vec<SentenceKey>>::new();
    let mut classes = BTreeMap::<(String, u64), Vec<usize>>::new();
    for (mut axiom, sentence) in axioms {
        let candidates = classes
            .entry((axiom.attributes().unique_id.clone(), axiom_shape(&axiom)))
            .or_default();
        match candidates
            .iter()
            .copied()
            .find(|&class| equal_axioms(&collapsed[class], &axiom))
        {
            Some(class) => {
                if !sentences[class].contains(&sentence) {
                    sentences[class].push(sentence);
                    let origins = std::mem::take(&mut axiom.attributes_mut().origins);
                    collapsed[class].attributes_mut().origins.extend(origins);
                }
            }
            None => {
                candidates.push(collapsed.len());
                sentences.push(vec![sentence]);
                collapsed.push(axiom);
            }
        }
    }
    collapsed
}

fn equal_axioms(left: &ClassifiedAxiom, right: &ClassifiedAxiom) -> bool {
    use ClassifiedAxiom::{Ceil, Function, Rewrite, Simplification};
    let mut renaming = VariableRenaming::default();
    let patterns = match (left, right) {
        (
            Rewrite {
                module: _,
                sort_parameters: left_parameters,
                lhs: left_lhs,
                rhs: left_rhs,
                existentials: left_existentials,
                attributes: _,
            },
            Rewrite {
                module: _,
                sort_parameters: right_parameters,
                lhs: right_lhs,
                rhs: right_rhs,
                existentials: right_existentials,
                attributes: _,
            },
        ) => {
            left_parameters == right_parameters
                && left_existentials.len() == right_existentials.len()
                && left_existentials
                    .iter()
                    .zip(right_existentials)
                    .all(|(left, right)| renaming.variable(left, right))
                && renaming.pattern(left_lhs, right_lhs)
                && renaming.pattern(left_rhs, right_rhs)
        }
        (
            Function {
                module: _,
                sort_parameters: left_parameters,
                requires: left_requires,
                binders: left_binders,
                lhs: left_lhs,
                rhs: left_rhs,
                attributes: _,
            },
            Function {
                module: _,
                sort_parameters: right_parameters,
                requires: right_requires,
                binders: right_binders,
                lhs: right_lhs,
                rhs: right_rhs,
                attributes: _,
            },
        ) => {
            left_parameters == right_parameters
                && left_binders.len() == right_binders.len()
                && left_binders.iter().zip(right_binders).all(|(left, right)| {
                    renaming.variable(&left.variable, &right.variable)
                        && renaming.pattern(&left.pattern, &right.pattern)
                })
                && renaming.pattern(left_requires, right_requires)
                && renaming.pattern(left_lhs, right_lhs)
                && renaming.pattern(left_rhs, right_rhs)
        }
        (
            Simplification {
                module: _,
                sort_parameters: left_parameters,
                requires: left_requires,
                lhs: left_lhs,
                rhs: left_rhs,
                attributes: _,
            },
            Simplification {
                module: _,
                sort_parameters: right_parameters,
                requires: right_requires,
                lhs: right_lhs,
                rhs: right_rhs,
                attributes: _,
            },
        )
        | (
            Ceil {
                module: _,
                sort_parameters: left_parameters,
                requires: left_requires,
                lhs: left_lhs,
                rhs: left_rhs,
                attributes: _,
            },
            Ceil {
                module: _,
                sort_parameters: right_parameters,
                requires: right_requires,
                lhs: right_lhs,
                rhs: right_rhs,
                attributes: _,
            },
        ) => {
            left_parameters == right_parameters
                && renaming.pattern(left_requires, right_requires)
                && renaming.pattern(left_lhs, right_lhs)
                && renaming.pattern(left_rhs, right_rhs)
        }
        _ => false,
    };
    patterns && renaming.attributes(left.attributes(), right.attributes())
}

/// One bijection between the variable names of two axioms, grown while they are compared.
///
/// It is keyed by name alone, and kinds and sorts are compared at every occurrence, so it is a
/// bijection both between names and between `(name, sort)` variables.
#[derive(Default)]
struct VariableRenaming<'a> {
    forward: BTreeMap<&'a str, &'a str>,
    backward: BTreeMap<&'a str, &'a str>,
}

impl<'a> VariableRenaming<'a> {
    fn variable(&mut self, left: &'a kore::Variable, right: &'a kore::Variable) -> bool {
        left.kind == right.kind && left.sort == right.sort && self.name(&left.name, &right.name)
    }

    fn name(&mut self, left: &'a str, right: &'a str) -> bool {
        match (self.forward.get(left), self.backward.get(right)) {
            (None, None) => {
                self.forward.insert(left, right);
                self.backward.insert(right, left);
                true
            }
            (Some(&image), Some(&preimage)) => image == right && preimage == left,
            _ => false,
        }
    }

    fn pattern(&mut self, left: &'a kore::Pattern, right: &'a kore::Pattern) -> bool {
        let mut work = vec![(left, right)];
        // Invariant: every popped pair had equal node scalars under the renaming and equal
        // child counts, and `work` holds the child pairs still to compare; each pair of nodes
        // is pushed once, so the loop ends after at most min(|left|, |right|) pops.
        while let Some((left, right)) = work.pop() {
            if !self.node(left, right) {
                return false;
            }
            let (left, right) = (walk::children(left), walk::children(right));
            if left.len() != right.len() {
                return false;
            }
            work.extend(left.into_iter().zip(right));
        }
        true
    }

    fn node(&mut self, left: &'a kore::Pattern, right: &'a kore::Pattern) -> bool {
        use kore::Pattern as P;
        match (left, right) {
            (P::String(left), P::String(right)) => left == right,
            (P::Variable(left), P::Variable(right)) => self.variable(left, right),
            (P::Application { symbol: left, .. }, P::Application { symbol: right, .. }) => {
                left == right
            }
            (P::Top { sort: left }, P::Top { sort: right })
            | (P::Bottom { sort: left }, P::Bottom { sort: right })
            | (P::And { sort: left, .. }, P::And { sort: right, .. })
            | (P::Or { sort: left, .. }, P::Or { sort: right, .. })
            | (P::Not { sort: left, .. }, P::Not { sort: right, .. })
            | (P::Next { sort: left, .. }, P::Next { sort: right, .. })
            | (P::Implies { sort: left, .. }, P::Implies { sort: right, .. })
            | (P::Iff { sort: left, .. }, P::Iff { sort: right, .. })
            | (P::Rewrites { sort: left, .. }, P::Rewrites { sort: right, .. }) => left == right,
            (
                P::Exists {
                    sort: left_sort,
                    variable: left,
                    ..
                },
                P::Exists {
                    sort: right_sort,
                    variable: right,
                    ..
                },
            )
            | (
                P::Forall {
                    sort: left_sort,
                    variable: left,
                    ..
                },
                P::Forall {
                    sort: right_sort,
                    variable: right,
                    ..
                },
            ) => left_sort == right_sort && self.variable(left, right),
            (
                P::Mu { variable: left, .. },
                P::Mu {
                    variable: right, ..
                },
            )
            | (
                P::Nu { variable: left, .. },
                P::Nu {
                    variable: right, ..
                },
            ) => self.variable(left, right),
            (
                P::Ceil {
                    operand_sort: left_operand,
                    result_sort: left_result,
                    ..
                },
                P::Ceil {
                    operand_sort: right_operand,
                    result_sort: right_result,
                    ..
                },
            )
            | (
                P::Floor {
                    operand_sort: left_operand,
                    result_sort: left_result,
                    ..
                },
                P::Floor {
                    operand_sort: right_operand,
                    result_sort: right_result,
                    ..
                },
            )
            | (
                P::Equals {
                    operand_sort: left_operand,
                    result_sort: left_result,
                    ..
                },
                P::Equals {
                    operand_sort: right_operand,
                    result_sort: right_result,
                    ..
                },
            )
            | (
                P::In {
                    operand_sort: left_operand,
                    result_sort: left_result,
                    ..
                },
                P::In {
                    operand_sort: right_operand,
                    result_sort: right_result,
                    ..
                },
            ) => left_operand == right_operand && left_result == right_result,
            (
                P::DomainValue {
                    sort: left_sort,
                    value: left,
                },
                P::DomainValue {
                    sort: right_sort,
                    value: right,
                },
            ) => left_sort == right_sort && left == right,
            (
                P::AssociativeApplication {
                    associativity: left_associativity,
                    symbol: left,
                    ..
                },
                P::AssociativeApplication {
                    associativity: right_associativity,
                    symbol: right,
                    ..
                },
            ) => left_associativity == right_associativity && left == right,
            _ => false,
        }
    }

    /// Every attribute except the origins, with concreteness constraints read through the
    /// renaming because they name variables.
    fn attributes(&self, left: &RuleAttributes, right: &RuleAttributes) -> bool {
        let RuleAttributes {
            priority,
            label,
            unique_id,
            simplification,
            preserves_definedness,
            concreteness,
            smt_lemma,
            executable,
            origins: _,
        } = left;
        *priority == right.priority
            && *label == right.label
            && *unique_id == right.unique_id
            && *simplification == right.simplification
            && *preserves_definedness == right.preserves_definedness
            && *smt_lemma == right.smt_lemma
            && *executable == right.executable
            && self.concreteness(concreteness, &right.concreteness)
    }

    /// Concreteness constraints compared after dropping the vacuous ones.
    ///
    /// Application reads a `concrete`/`symbolic` entry only for a left-hand-side variable with
    /// the entry's name and sort (`check_concreteness`), and every internalized rule variable is
    /// a variable of the axiom's patterns under a provenance marker. An entry naming no pattern
    /// variable therefore constrains nothing, and a set of such entries is the same as no
    /// constraint. The live entries name pattern variables, which the renaming already relates.
    fn concreteness(&self, left: &Concreteness, right: &Concreteness) -> bool {
        match (left, right) {
            (Concreteness::All(left), Concreteness::All(right)) => left == right,
            (Concreteness::All(_), _) | (_, Concreteness::All(_)) => false,
            (left, right) => {
                let left = live_constraints(left, &self.forward);
                let right = live_constraints(right, &self.backward);
                left.len() == right.len()
                    && left.iter().all(|((name, sort), kind)| {
                        right.get(&(Name::from(self.forward[name.as_ref()]), sort.clone()))
                            == Some(kind)
                    })
            }
        }
    }
}

/// The entries of `concreteness` that name a variable of the axiom's patterns, whose names are
/// the keys of `pattern_names`.
fn live_constraints<'c>(
    concreteness: &'c Concreteness,
    pattern_names: &BTreeMap<&str, &str>,
) -> BTreeMap<&'c (Name, Name), &'c ConstraintKind> {
    match concreteness {
        Concreteness::Some(constrained) => constrained
            .iter()
            .filter(|((name, _), _)| pattern_names.contains_key(name.as_ref()))
            .collect(),
        Concreteness::Unconstrained | Concreteness::All(_) => BTreeMap::new(),
    }
}

/// A hash of what [`equal_axioms`] compares literally: the variant, and for every pattern node
/// its variant, symbol, domain value and child count, with variables reduced to their kind.
/// Equal axioms have equal shapes, so only axioms with one shape are compared.
fn axiom_shape(axiom: &ClassifiedAxiom) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    std::mem::discriminant(axiom).hash(&mut hasher);
    let mut patterns = Vec::new();
    match axiom {
        ClassifiedAxiom::Rewrite {
            lhs,
            rhs,
            existentials,
            ..
        } => {
            existentials.len().hash(&mut hasher);
            patterns.extend([lhs, rhs]);
        }
        ClassifiedAxiom::Function {
            requires,
            binders,
            lhs,
            rhs,
            ..
        } => {
            binders.len().hash(&mut hasher);
            patterns.extend(binders.iter().map(|binder| &binder.pattern));
            patterns.extend([requires, lhs, rhs]);
        }
        ClassifiedAxiom::Simplification {
            requires, lhs, rhs, ..
        }
        | ClassifiedAxiom::Ceil {
            requires, lhs, rhs, ..
        } => patterns.extend([requires, lhs, rhs]),
    }
    for pattern in patterns {
        walk::for_each_post_order(pattern, |node| {
            std::mem::discriminant(node).hash(&mut hasher);
            walk::children(node).len().hash(&mut hasher);
            match node {
                kore::Pattern::String(value) | kore::Pattern::DomainValue { value, .. } => {
                    value.hash(&mut hasher);
                }
                kore::Pattern::Variable(variable) => {
                    matches!(variable.kind, kore::VariableKind::Set).hash(&mut hasher);
                }
                kore::Pattern::Application { symbol, .. }
                | kore::Pattern::AssociativeApplication { symbol, .. } => {
                    symbol.name.hash(&mut hasher);
                }
                _ => {}
            }
        });
    }
    hasher.finish()
}

/// ```toml algorithm-site
/// id = "backend.definition.internalize"
/// role = "part"
/// sites = ["internalize_axiom"]
/// ```
pub fn internalize_axiom(
    definition: &BackendDefinition,
    axiom: &ClassifiedAxiom,
) -> Result<Vec<InternalizedRule>, DefinitionError> {
    let subsort_validation = SubsortValidation::Ignore;
    match axiom {
        ClassifiedAxiom::Rewrite {
            sort_parameters,
            lhs,
            rhs,
            existentials,
            attributes,
            ..
        } => {
            let (rhs, ensures) =
                internalize_term_rhs(definition, rhs, sort_parameters, subsort_validation)?;
            if matches!(rhs, RuleRhs::Top) {
                return Err(DefinitionError::RulePattern(RulePatternError::MissingTerm));
            }
            let existential_variables = existentials
                .iter()
                .map(|variable| definition.internalize_variable(variable, sort_parameters))
                .collect::<Result<BTreeSet<_>, DefinitionError>>()?;
            let rhs_renaming = |variable: &Variable| {
                if existential_variables.contains(variable) {
                    variable.with_provenance(VariableProvenance::Existential)
                } else {
                    variable.with_provenance(VariableProvenance::Rule)
                }
            };
            let rhs = rename_rhs(rhs, rhs_renaming);
            let ensures = rename_predicates(&ensures, rhs_renaming);
            let existentials = existential_variables
                .iter()
                .map(|variable| variable.with_provenance(VariableProvenance::Existential))
                .collect::<BTreeSet<_>>();
            let lhs_alternatives = term_disjuncts(lhs);
            let split = lhs_alternatives.len() > 1;
            lhs_alternatives
                .into_iter()
                .enumerate()
                .map(|(index, lhs)| {
                    let (lhs, requires) = internalize_rule_pattern(
                        definition,
                        &lhs,
                        sort_parameters,
                        subsort_validation,
                    )?;
                    Ok(InternalizedRule::Term(
                        RuleKind::Rewrite,
                        make_rule(
                            rename_term(&lhs, |variable| {
                                variable.with_provenance(VariableProvenance::Rule)
                            }),
                            rhs.clone(),
                            rename_predicates(&requires, |variable| {
                                variable.with_provenance(VariableProvenance::Rule)
                            }),
                            ensures.clone(),
                            attributes.clone(),
                            existentials.clone(),
                            split.then_some(index),
                        ),
                    ))
                })
                .collect()
        }
        ClassifiedAxiom::Simplification {
            sort_parameters,
            requires,
            lhs,
            rhs,
            attributes,
            ..
        } => {
            if !is_term_pattern(lhs) {
                let lhs =
                    internalize_predicate(definition, lhs, sort_parameters, subsort_validation)?;
                let requires = internalize_predicates(
                    definition,
                    requires,
                    sort_parameters,
                    subsort_validation,
                )?;
                let rhs =
                    internalize_predicates(definition, rhs, sort_parameters, subsort_validation)?;
                let rename =
                    |variable: &Variable| variable.with_provenance(VariableProvenance::Equation);
                let mut lhs = rename_predicates(&[lhs], rename);
                return Ok(vec![InternalizedRule::Predicate(PredicateRewriteRule {
                    lhs: lhs.pop().expect("one predicate was internalized"),
                    rhs: rename_predicates(&rhs, rename),
                    requires: rename_predicates(&requires, rename),
                    attributes: attributes.clone(),
                })]);
            }
            if contains_term_or(lhs) {
                return Err(DefinitionError::RulePattern(
                    RulePatternError::TermDisjunction,
                ));
            }
            let lhs = definition.internalize_term_with_validation(
                lhs,
                sort_parameters,
                subsort_validation,
            )?;
            let requires =
                internalize_predicates(definition, requires, sort_parameters, subsort_validation)?;
            let (rhs, ensures) =
                internalize_term_rhs(definition, rhs, sort_parameters, subsort_validation)?;
            let rename =
                |variable: &Variable| variable.with_provenance(VariableProvenance::Equation);
            Ok(vec![InternalizedRule::Term(
                RuleKind::Simplification,
                make_rule(
                    rename_term(&lhs, rename),
                    rename_rhs(rhs, rename),
                    rename_predicates(&requires, rename),
                    rename_predicates(&ensures, rename),
                    attributes.clone(),
                    BTreeSet::new(),
                    None,
                ),
            )])
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
            if contains_term_or(lhs) {
                return Err(DefinitionError::RulePattern(
                    RulePatternError::TermDisjunction,
                ));
            }
            let lhs = definition.internalize_term_with_validation(
                lhs,
                sort_parameters,
                subsort_validation,
            )?;
            let mut binding_alternatives = vec![Substitution::new()];
            for binder in binders {
                let variable =
                    definition.internalize_variable(&binder.variable, sort_parameters)?;
                let alternatives = binder_term_alternatives(&binder.pattern)
                    .into_iter()
                    .map(|pattern| {
                        definition.internalize_term_with_validation(
                            pattern,
                            sort_parameters,
                            subsort_validation,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                for alternative in &alternatives {
                    if variable.sort != alternative.sort() {
                        return Err(DefinitionError::RulePattern(
                            RulePatternError::BinderSortMismatch(variable),
                        ));
                    }
                }
                binding_alternatives = binding_alternatives
                    .into_iter()
                    .flat_map(|bindings| {
                        alternatives.iter().cloned().map({
                            let variable = variable.clone();
                            move |alternative| {
                                let mut bindings = bindings.clone();
                                bindings.insert(variable.clone(), alternative);
                                bindings
                            }
                        })
                    })
                    .collect();
            }
            let requires =
                internalize_predicates(definition, requires, sort_parameters, subsort_validation)?;
            let (rhs, ensures) =
                internalize_term_rhs(definition, rhs, sort_parameters, subsort_validation)?;
            let rename =
                |variable: &Variable| variable.with_provenance(VariableProvenance::Equation);
            let rhs = rename_rhs(rhs, rename);
            let requires = rename_predicates(&requires, rename);
            let ensures = rename_predicates(&ensures, rename);
            Ok(binding_alternatives
                .into_iter()
                .map(|bindings| {
                    InternalizedRule::Term(
                        RuleKind::Function,
                        make_rule(
                            rename_term(&substitute(&lhs, &bindings), rename),
                            rhs.clone(),
                            requires.clone(),
                            ensures.clone(),
                            attributes.clone(),
                            BTreeSet::new(),
                            None,
                        ),
                    )
                })
                .collect())
        }
        ClassifiedAxiom::Ceil {
            sort_parameters,
            requires,
            lhs,
            rhs,
            attributes,
            ..
        } => {
            let lhs = definition.internalize_term_with_validation(
                lhs,
                sort_parameters,
                subsort_validation,
            )?;
            let requires =
                internalize_predicates(definition, requires, sort_parameters, subsort_validation)?;
            let rhs = internalize_predicates(definition, rhs, sort_parameters, subsort_validation)?;
            let rename =
                |variable: &Variable| variable.with_provenance(VariableProvenance::Equation);
            let lhs = rename_term(&lhs, rename);
            let requires = rename_predicates(&requires, rename);
            let rhs = rename_predicates(&rhs, rename);
            let mut computed_attributes = computed_attributes([&lhs]);
            let rhs = RuleRhs::Predicates(rhs);
            (
                computed_attributes.variables,
                computed_attributes.unbound_variables,
            ) = rule_variable_sets(&lhs, &rhs, &requires, &[], &BTreeSet::new());
            Ok(vec![InternalizedRule::Term(
                RuleKind::Ceil,
                RewriteRule {
                    lhs,
                    lhs_alternative: None,
                    rhs,
                    requires,
                    ensures: Vec::new(),
                    attributes: attributes.clone(),
                    computed_attributes,
                    existentials: BTreeSet::new(),
                },
            )])
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

pub fn insert_rewrite_theory(theory: &mut RewriteTheory, rule: RewriteRule, index: RuleIndex) {
    let priority = rule.attributes.priority;
    theory
        .entry(term_index(&rule.lhs))
        .or_default()
        .entry(priority)
        .or_default()
        .push(IndexedRewriteRule {
            rule: Arc::new(rule),
            index,
        });
}

pub fn rule_index(definition: &BackendDefinition, term: &Term) -> RuleIndex {
    // The index keys on the one `<k>` cell not nested in a `<k>` cell, and on nothing when there
    // are none or several. The stored count, saturated at 2, says which case holds, and the cell
    // is fetched only when it is 1: the same cell as the first that `find_k_cells` collects
    // (`rule_index_same` of lean/KRust/TermAttributes.lean).
    let cell = match term.attributes().k_cells() {
        1 => fetch_k_cell(term),
        _ => None,
    };
    RuleIndex(vec![
        cell.and_then(k_cell_head)
            .map_or(CellIndex::Anything, |head| cell_index(definition, head)),
    ])
}

pub fn subject_index(definition: &BackendDefinition, term: &Term) -> RuleIndex {
    let mut index = rule_index(definition, term);
    for cell in &mut index.0 {
        if matches!(cell, CellIndex::Function(_)) {
            *cell = CellIndex::Anything;
        }
    }
    index
}

/// The first `<k>` cell of `term` not nested in a `<k>` cell, in the order of `find_k_cells`, or
/// `None` when there is none: descends only into the first child whose stored `k_cells` count is
/// not zero (`fetchK` of lean/KRust/TermAttributes.lean).
pub(crate) fn fetch_k_cell(term: &Term) -> Option<&Term> {
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => {
            if symbol.is(WellKnownSymbol::KCell) {
                return Some(term);
            }
            first_with_k_cell(arguments.iter())
        }
        TermKind::And(left, right) => first_with_k_cell([left, right].into_iter()),
        TermKind::Injection { term, .. } => fetch_k_cell(term),
        TermKind::Map { entries, rest, .. } => first_with_k_cell(
            entries
                .iter()
                .flat_map(|(key, value)| [key, value])
                .chain(rest.iter()),
        ),
        TermKind::List { heads, rest, .. } => first_with_k_cell(
            heads.iter().chain(
                rest.iter()
                    .flat_map(|(middle, tails)| std::iter::once(middle).chain(tails)),
            ),
        ),
        TermKind::Set { elements, rest, .. } => {
            first_with_k_cell(elements.iter().chain(rest.iter()))
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => None,
    }
}

/// `fetch_k_cell` of the first child whose stored `k_cells` count is not zero.
fn first_with_k_cell<'a>(mut children: impl Iterator<Item = &'a Term>) -> Option<&'a Term> {
    children
        .find(|child| child.attributes().k_cells() > 0)
        .and_then(fetch_k_cell)
}

/// Every `<k>` cell not nested in a `<k>` cell, stopping after two: the walk that `rule_index`
/// ran before the stored count replaced it (`findK` of lean/KRust/TermAttributes.lean), kept as
/// the reference its replacement is tested against.
#[cfg(test)]
pub(crate) fn find_k_cells<'a>(term: &'a Term, cells: &mut Vec<&'a Term>) {
    if cells.len() > 1 {
        return;
    }
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => {
            if symbol.is(WellKnownSymbol::KCell) {
                cells.push(term);
                return;
            }
            for argument in arguments {
                find_k_cells(argument, cells);
            }
        }
        TermKind::And(left, right) => {
            find_k_cells(left, cells);
            find_k_cells(right, cells);
        }
        TermKind::Injection { term, .. } => find_k_cells(term, cells),
        TermKind::Map { entries, rest, .. } => {
            for (key, value) in entries {
                find_k_cells(key, cells);
                find_k_cells(value, cells);
            }
            if let Some(rest) = rest {
                find_k_cells(rest, cells);
            }
        }
        TermKind::List { heads, rest, .. } => {
            for head in heads {
                find_k_cells(head, cells);
            }
            if let Some((middle, tails)) = rest {
                find_k_cells(middle, cells);
                for tail in tails {
                    find_k_cells(tail, cells);
                }
            }
        }
        TermKind::Set { elements, rest, .. } => {
            for element in elements {
                find_k_cells(element, cells);
            }
            if let Some(rest) = rest {
                find_k_cells(rest, cells);
            }
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
    }
}

fn k_cell_head(cell: &Term) -> Option<&Term> {
    let TermKind::Application {
        arguments: cell_arguments,
        ..
    } = cell.kind()
    else {
        return None;
    };
    let [contents] = cell_arguments.as_slice() else {
        return None;
    };
    match contents.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } if symbol.is(WellKnownSymbol::KSeq) => {
            let [head, _tail] = arguments.as_slice() else {
                return None;
            };
            Some(head)
        }
        TermKind::Application {
            symbol, arguments, ..
        } if symbol.is(WellKnownSymbol::DotK) && arguments.is_empty() => Some(contents),
        _ => None,
    }
}

fn cell_index(definition: &BackendDefinition, term: &Term) -> CellIndex {
    match term.kind() {
        TermKind::Injection { term, .. } => cell_index(definition, term),
        TermKind::And(left, right) => {
            cell_index(definition, left).meet(cell_index(definition, right))
        }
        TermKind::Variable(_) => CellIndex::Anything,
        TermKind::Application { symbol, .. }
            if definition.overloads.is_overloaded(&symbol.name)
                || symbol.attributes.associative
                || symbol.attributes.idempotent =>
        {
            CellIndex::Anything
        }
        TermKind::Application { symbol, .. } => match symbol.attributes.symbol_type {
            SymbolType::Constructor => CellIndex::Constructor(symbol.name.clone()),
            SymbolType::Function(_) => CellIndex::Function(symbol.name.clone()),
        },
        TermKind::DomainValue { value, .. } => CellIndex::Value(value.clone()),
        TermKind::Map { .. } => CellIndex::Map,
        TermKind::List { .. } => CellIndex::List,
        TermKind::Set { .. } => CellIndex::Set,
    }
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
        // K's `#as` aliases are emitted as a conjunction between the real pattern and a
        // variable which binds the entire matched subject. Index the rule by the structural
        // conjunct so it remains discoverable for an ordinary subject term.
        TermKind::And(left, right) if matches!(left.kind(), TermKind::Variable(_)) => {
            term_index(right)
        }
        TermKind::And(left, right) if matches!(right.kind(), TermKind::Variable(_)) => {
            term_index(left)
        }
        TermKind::And(..) => TermIndex::And,
    }
}

/// The rules a subject with `index` may match, per priority and in trial order: the rules under `index`, then the rules under `TermIndex::Variable`, each group in declaration order.
/// `Variable` subjects see only the variable-indexed rules.
/// One `Arc` clone is made per candidate; `Counter::RewriteRuleAttempts` counts what the caller does with them (backend.rule.select).
pub(crate) fn applicable_groups(
    theory: &Theory,
    index: &TermIndex,
) -> BTreeMap<u8, Vec<Arc<RewriteRule>>> {
    let _span = measure::algorithm_span(Algorithm::BackendRuleSelect);
    let mut groups = BTreeMap::new();
    let covered = if index == &TermIndex::Variable {
        vec![index]
    } else {
        vec![index, &TermIndex::Variable]
    };
    for covered in covered {
        if let Some(found) = theory.get(covered) {
            for (priority, rules) in found {
                groups
                    .entry(*priority)
                    .or_insert_with(Vec::new)
                    .extend(rules.iter().cloned());
            }
        }
    }
    groups
}

pub fn applicable_rewrite_groups(
    theory: &RewriteTheory,
    index: &TermIndex,
    subject: &RuleIndex,
) -> BTreeMap<u8, Vec<Arc<RewriteRule>>> {
    let _span = measure::algorithm_span(Algorithm::BackendRuleSelect);
    let mut groups = BTreeMap::new();
    let covered = if index == &TermIndex::Variable {
        vec![index]
    } else {
        vec![index, &TermIndex::Variable]
    };
    for covered in covered {
        if let Some(found) = theory.get(covered) {
            for (priority, rules) in found {
                groups.entry(*priority).or_insert_with(Vec::new).extend(
                    rules
                        .iter()
                        .filter(|stored| stored.index.covers(subject))
                        .map(|stored| stored.rule.clone()),
                );
            }
        }
    }
    groups
}

pub(crate) fn internalize_rule_pattern(
    definition: &BackendDefinition,
    pattern: &kore::Pattern,
    sort_parameters: &[Name],
    subsort_validation: SubsortValidation,
) -> Result<(Term, Vec<Predicate>), DefinitionError> {
    if contains_term_or(pattern) {
        return Err(DefinitionError::RulePattern(
            RulePatternError::TermDisjunction,
        ));
    }
    let mut components = Vec::new();
    flatten_and(pattern, &mut components);
    let mut terms = Vec::new();
    let mut predicates = Vec::new();
    for component in components {
        if is_term_pattern(component) {
            terms.push(definition.internalize_term_collecting(
                component,
                sort_parameters,
                subsort_validation,
                &mut predicates,
            )?);
        } else {
            predicates.extend(internalize_predicates(
                definition,
                component,
                sort_parameters,
                subsort_validation,
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

fn internalize_term_rhs(
    definition: &BackendDefinition,
    pattern: &kore::Pattern,
    sort_parameters: &[Name],
    subsort_validation: SubsortValidation,
) -> Result<(RuleRhs, Vec<Predicate>), DefinitionError> {
    if contains_strict_bottom(pattern) {
        return Ok((RuleRhs::Bottom, Vec::new()));
    }
    let mut components = Vec::new();
    flatten_and(pattern, &mut components);
    if !components.is_empty()
        && components
            .iter()
            .all(|component| matches!(component, kore::Pattern::Top { .. }))
    {
        return Ok((RuleRhs::Top, Vec::new()));
    }
    let alternatives = term_disjuncts(pattern);
    match alternatives.as_slice() {
        [] => Ok((RuleRhs::Bottom, Vec::new())),
        [single] => {
            let (term, predicates) =
                internalize_rule_pattern(definition, single, sort_parameters, subsort_validation)?;
            Ok((RuleRhs::Term(term), predicates))
        }
        many => Ok((
            RuleRhs::Disjunction(
                many.iter()
                    .map(|alternative| {
                        let (term, ensures) = internalize_rule_pattern(
                            definition,
                            alternative,
                            sort_parameters,
                            subsort_validation,
                        )?;
                        Ok(RhsAlternative { term, ensures })
                    })
                    .collect::<Result<Vec<_>, DefinitionError>>()?,
            ),
            Vec::new(),
        )),
    }
}

fn contains_strict_bottom(pattern: &kore::Pattern) -> bool {
    match pattern {
        kore::Pattern::Bottom { .. } => true,
        kore::Pattern::And { arguments, .. }
        | kore::Pattern::Application { arguments, .. }
        | kore::Pattern::AssociativeApplication { arguments, .. } => {
            arguments.iter().any(contains_strict_bottom)
        }
        _ => false,
    }
}

fn internalize_predicates(
    definition: &BackendDefinition,
    pattern: &kore::Pattern,
    sort_parameters: &[Name],
    subsort_validation: SubsortValidation,
) -> Result<Vec<Predicate>, DefinitionError> {
    match pattern {
        kore::Pattern::Top { .. } => Ok(Vec::new()),
        kore::Pattern::Bottom { .. } => Ok(vec![Predicate::False]),
        kore::Pattern::And { arguments, .. } => arguments
            .iter()
            .map(|argument| {
                internalize_predicates(definition, argument, sort_parameters, subsort_validation)
            })
            .collect::<Result<Vec<_>, _>>()
            .map(|predicates| predicates.into_iter().flatten().collect()),
        kore::Pattern::Or { arguments, .. } => Ok(vec![Predicate::Or(
            arguments
                .iter()
                .map(|argument| {
                    internalize_predicate(definition, argument, sort_parameters, subsort_validation)
                })
                .collect::<Result<Vec<_>, _>>()?,
        )]),
        _ => Ok(vec![internalize_predicate(
            definition,
            pattern,
            sort_parameters,
            subsort_validation,
        )?]),
    }
}

pub(crate) fn internalize_predicate(
    definition: &BackendDefinition,
    pattern: &kore::Pattern,
    sort_parameters: &[Name],
    subsort_validation: SubsortValidation,
) -> Result<Predicate, DefinitionError> {
    let term = |pattern: &kore::Pattern| {
        definition.internalize_term_with_validation(pattern, sort_parameters, subsort_validation)
    };
    let predicate = |pattern: &kore::Pattern| {
        internalize_predicate(definition, pattern, sort_parameters, subsort_validation)
    };
    match pattern {
        kore::Pattern::Top { .. } => Ok(Predicate::True),
        kore::Pattern::Bottom { .. } => Ok(Predicate::False),
        kore::Pattern::Equals { left, right, .. }
            if is_term_pattern(left) && is_term_pattern(right) =>
        {
            Ok(Predicate::Equals(term(left)?, term(right)?))
        }
        kore::Pattern::Equals { left, right, .. } => Ok(Predicate::Iff(
            Box::new(predicate(left)?),
            Box::new(predicate(right)?),
        )),
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
            definition.internalize_variable(variable, sort_parameters)?,
            Box::new(predicate(body)?),
        )),
        kore::Pattern::Forall { variable, body, .. } => Ok(Predicate::Forall(
            definition.internalize_variable(variable, sort_parameters)?,
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

pub(crate) fn internalize_model_predicate(
    definition: &BackendDefinition,
    pattern: &kore::Pattern,
    sort_parameters: &[Name],
    subsort_validation: SubsortValidation,
) -> Result<Option<Predicate>, DefinitionError> {
    let recurse = |pattern: &kore::Pattern| {
        internalize_model_predicate(definition, pattern, sort_parameters, subsort_validation)
    };
    Ok(match pattern {
        kore::Pattern::Equals { .. }
        | kore::Pattern::Ceil { .. }
        | kore::Pattern::Floor { .. }
        | kore::Pattern::In { .. } => Some(internalize_predicate(
            definition,
            pattern,
            sort_parameters,
            subsort_validation,
        )?),
        kore::Pattern::And { arguments, .. } => {
            let predicates = arguments
                .iter()
                .map(recurse)
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .flatten()
                .collect::<Vec<_>>();
            (!predicates.is_empty()).then_some(Predicate::And(predicates))
        }
        kore::Pattern::Or { arguments, .. } => {
            let predicates = arguments
                .iter()
                .map(recurse)
                .collect::<Result<Option<Vec<_>>, _>>()?;
            predicates.map(Predicate::Or)
        }
        kore::Pattern::Not { argument, .. } => {
            recurse(argument)?.map(|inner| Predicate::Not(Box::new(inner)))
        }
        kore::Pattern::Implies { left, right, .. } => match (recurse(left)?, recurse(right)?) {
            (Some(left), Some(right)) => Some(Predicate::Implies(Box::new(left), Box::new(right))),
            _ => None,
        },
        kore::Pattern::Iff { left, right, .. } => match (recurse(left)?, recurse(right)?) {
            (Some(left), Some(right)) => Some(Predicate::Iff(Box::new(left), Box::new(right))),
            _ => None,
        },
        kore::Pattern::Exists { variable, body, .. } => recurse(body)?
            .map(|inner| {
                definition
                    .internalize_variable(variable, sort_parameters)
                    .map(|variable| Predicate::Exists(variable, Box::new(inner)))
            })
            .transpose()?,
        kore::Pattern::Forall { variable, body, .. } => recurse(body)?
            .map(|inner| {
                definition
                    .internalize_variable(variable, sort_parameters)
                    .map(|variable| Predicate::Forall(variable, Box::new(inner)))
            })
            .transpose()?,
        _ => None,
    })
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

pub(crate) fn contains_term_component(pattern: &kore::Pattern) -> bool {
    match pattern {
        kore::Pattern::String(_)
        | kore::Pattern::Variable(_)
        | kore::Pattern::Application { .. }
        | kore::Pattern::DomainValue { .. }
        | kore::Pattern::AssociativeApplication { .. } => true,
        kore::Pattern::And { arguments, .. } => arguments.iter().any(contains_term_component),
        kore::Pattern::Exists { body, .. } | kore::Pattern::Forall { body, .. } => {
            contains_term_component(body)
        }
        kore::Pattern::Top { .. }
        | kore::Pattern::Bottom { .. }
        | kore::Pattern::Or { .. }
        | kore::Pattern::Not { .. }
        | kore::Pattern::Next { .. }
        | kore::Pattern::Implies { .. }
        | kore::Pattern::Iff { .. }
        | kore::Pattern::Rewrites { .. }
        | kore::Pattern::Mu { .. }
        | kore::Pattern::Nu { .. }
        | kore::Pattern::Ceil { .. }
        | kore::Pattern::Floor { .. }
        | kore::Pattern::Equals { .. }
        | kore::Pattern::In { .. } => false,
    }
}

fn contains_term_or(pattern: &kore::Pattern) -> bool {
    match pattern {
        kore::Pattern::Or { arguments, .. } => arguments.iter().any(contains_term_component),
        kore::Pattern::And { arguments, .. } => arguments.iter().any(contains_term_or),
        kore::Pattern::Application { arguments, .. }
        | kore::Pattern::AssociativeApplication { arguments, .. } => arguments
            .iter()
            .any(|argument| contains_term_or_in_context(argument, true)),
        _ => false,
    }
}

fn contains_term_or_in_context(pattern: &kore::Pattern, inside_term: bool) -> bool {
    match pattern {
        kore::Pattern::Or { arguments, .. } => {
            inside_term || arguments.iter().any(contains_term_component)
        }
        kore::Pattern::And { arguments, .. } => arguments
            .iter()
            .any(|argument| contains_term_or_in_context(argument, inside_term)),
        kore::Pattern::Application { arguments, .. }
        | kore::Pattern::AssociativeApplication { arguments, .. } => arguments
            .iter()
            .any(|argument| contains_term_or_in_context(argument, true)),
        _ => false,
    }
}

pub(crate) fn distribute_term_or(pattern: &kore::Pattern) -> Vec<kore::Pattern> {
    distribute_term_or_with_context(pattern, false)
}

fn distribute_term_or_with_context(
    pattern: &kore::Pattern,
    inside_term: bool,
) -> Vec<kore::Pattern> {
    match pattern {
        kore::Pattern::Or { arguments, .. }
            if inside_term || arguments.iter().any(contains_term_component) =>
        {
            arguments
                .iter()
                .flat_map(|argument| distribute_term_or_with_context(argument, true))
                .collect()
        }
        kore::Pattern::And { sort, arguments } => distribute_arguments(arguments, inside_term)
            .into_iter()
            .map(|arguments| kore::Pattern::And {
                sort: sort.clone(),
                arguments,
            })
            .collect(),
        kore::Pattern::Application { symbol, arguments } => distribute_arguments(arguments, true)
            .into_iter()
            .map(|arguments| kore::Pattern::Application {
                symbol: symbol.clone(),
                arguments,
            })
            .collect(),
        kore::Pattern::AssociativeApplication {
            associativity,
            symbol,
            arguments,
        } => distribute_arguments(arguments, true)
            .into_iter()
            .map(|arguments| kore::Pattern::AssociativeApplication {
                associativity: *associativity,
                symbol: symbol.clone(),
                arguments,
            })
            .collect(),
        _ => vec![pattern.clone()],
    }
}

fn distribute_arguments(arguments: &[kore::Pattern], inside_term: bool) -> Vec<Vec<kore::Pattern>> {
    let mut combinations = vec![Vec::new()];
    for argument in arguments {
        let alternatives = distribute_term_or_with_context(argument, inside_term);
        combinations = combinations
            .into_iter()
            .flat_map(|prefix| {
                alternatives.iter().cloned().map(move |alternative| {
                    let mut combined = prefix.clone();
                    combined.push(alternative);
                    combined
                })
            })
            .collect();
    }
    combinations
}

pub(crate) fn term_disjuncts(pattern: &kore::Pattern) -> Vec<kore::Pattern> {
    distribute_term_or(pattern)
        .into_iter()
        .filter(|alternative| !matches!(alternative, kore::Pattern::Bottom { .. }))
        .collect()
}

fn make_rule(
    lhs: Term,
    rhs: RuleRhs,
    requires: Vec<Predicate>,
    ensures: Vec<Predicate>,
    attributes: RuleAttributes,
    existentials: BTreeSet<Variable>,
    lhs_alternative: Option<usize>,
) -> RewriteRule {
    let mut terms = vec![&lhs];
    match &rhs {
        RuleRhs::Term(rhs) => terms.push(rhs),
        RuleRhs::Disjunction(alternatives) => {
            terms.extend(alternatives.iter().map(|alternative| &alternative.term));
        }
        RuleRhs::Top | RuleRhs::Bottom | RuleRhs::Predicates(_) => {}
    }
    let mut computed_attributes = computed_attributes(terms);
    if attributes.preserves_definedness {
        computed_attributes.undefined_symbols.clear();
    }
    (
        computed_attributes.variables,
        computed_attributes.unbound_variables,
    ) = rule_variable_sets(&lhs, &rhs, &requires, &ensures, &existentials);
    RewriteRule {
        lhs,
        lhs_alternative,
        rhs,
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
        term.visit_symbols(&mut |symbol| {
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

fn rename_rhs(rhs: RuleRhs, rename: impl Copy + Fn(&Variable) -> Variable) -> RuleRhs {
    match rhs {
        RuleRhs::Term(term) => RuleRhs::Term(rename_term(&term, rename)),
        RuleRhs::Disjunction(alternatives) => RuleRhs::Disjunction(
            alternatives
                .into_iter()
                .map(|alternative| RhsAlternative {
                    term: rename_term(&alternative.term, rename),
                    ensures: rename_predicates(&alternative.ensures, rename),
                })
                .collect(),
        ),
        RuleRhs::Top => RuleRhs::Top,
        RuleRhs::Bottom => RuleRhs::Bottom,
        RuleRhs::Predicates(_) => unreachable!("term rules cannot have predicate RHSs"),
    }
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

/// A rule whose variables that its scope also mentions were renamed to fresh names, with the
/// renaming it applied (original rule variable to fresh variable).
pub(crate) type RenamedApart<R> = (R, BTreeMap<Variable, Variable>);

thread_local! {
    /// The open `ApartScope`s on this thread and the next `{name}!apart{counter}` counter.
    static APART: Cell<(usize, u64)> = const { Cell::new((0, 0)) };
}

/// One request's allocation scope for `{name}!apart{counter}` names.
///
/// The backend's entry points (an execution, a rewrite step, a simplification, a proof) open a
/// scope. Opening the outermost scope on a thread restarts the counter at 0; nested scopes keep
/// it. Within one outermost scope every name is minted from a counter that only grows, so no
/// two renamings, nested or siblings, share a name, and identical requests mint identical names
/// whatever ran before them. A renamed name that outlives its application is part of the state
/// later scopes are applied to, and every renaming avoids every name of its scope, so a later
/// scope that restarts the counter cannot reuse it either. Outside any scope the counter keeps
/// growing from its last value.
pub(crate) struct ApartScope(());

impl ApartScope {
    pub(crate) fn enter() -> Self {
        APART.with(|state| {
            let (depth, next) = state.get();
            state.set((depth + 1, if depth == 0 { 0 } else { next }));
        });
        Self(())
    }
}

impl Drop for ApartScope {
    fn drop(&mut self) {
        APART.with(|state| {
            let (depth, next) = state.get();
            state.set((depth.saturating_sub(1), next));
        });
    }
}

fn next_apart_counter() -> u64 {
    APART.with(|state| {
        let (depth, next) = state.get();
        state.set((depth, next + 1));
        next
    })
}

/// `rule` with every variable that its scope also mentions renamed to a fresh name, or `None`
/// when no rule variable can meet a scope variable.
///
/// A rule's variables are bound by the rule, so renaming them injectively gives the same rule.
/// The scope of one application is the subject term (`subject`, its variables) and the path
/// conditions it is applied under (`constraints`). Two meetings would identify a rule variable
/// with a scope variable of the same name and sort:
/// - any rule variable, free or bound, against a subject variable: the matcher composes its
///   bindings into the subject terms it binds, and a binding's value, which mentions subject
///   variables, is substituted under the rule's quantifiers and next to its other variables;
/// - a free rule variable that the left-hand side does not bind (`unbound_variables`: a
///   variable only of the requires, the right-hand side or the ensures) against a variable of
///   the path conditions, under which the instantiated conditions are then decided.
///
/// Every rule variable that the scope mentions is renamed, at every occurrence: left-hand side,
/// right-hand side with its ensures, requires, quantifier binders, existentials, and
/// `concrete`/`symbolic` constraints. The fresh name is `{name}!apart{counter}`: the `apart`
/// marker is spelled by no other name source (KORE identifiers contain no `!`, and the other
/// backend-minted names use `!{counter}`, `!claim` and `!exists`), the counter is the request's
/// (`ApartScope`), and the name is still checked against every rule variable and every scope
/// variable. So a fresh name captures nothing in scope and is not reused by another renaming of
/// the same request, including a nested one while a condition of this rule is evaluated.
///
/// ```toml algorithm-site
/// id = "backend.fresh.variables"
/// role = "part"
/// sites = ["rename_apart"]
/// ```
pub(crate) fn rename_apart(
    rule: &RewriteRule,
    subject: &BTreeSet<Variable>,
    constraints: &[Predicate],
) -> Option<RenamedApart<RewriteRule>> {
    let computed = &rule.computed_attributes;
    let term_clash = !computed.variables.is_disjoint(subject);
    if !term_clash && computed.unbound_variables.is_empty() {
        return None;
    }
    let constraint_variables = free_variables_of(constraints);
    if !term_clash
        && computed
            .unbound_variables
            .is_disjoint(&constraint_variables)
    {
        return None;
    }
    let mut scope = constraint_variables;
    scope.extend(subject.iter().cloned());
    let renaming = fresh_renaming(&computed.variables, &scope);
    let rename = |variable: &Variable| {
        renaming
            .get(variable)
            .cloned()
            .unwrap_or_else(|| variable.clone())
    };
    let rhs = match &rule.rhs {
        RuleRhs::Predicates(predicates) => {
            RuleRhs::Predicates(rename_predicates(predicates, rename))
        }
        rhs => rename_rhs(rhs.clone(), rename),
    };
    let rename_set = |variables: &BTreeSet<Variable>| variables.iter().map(rename).collect();
    let renamed = RewriteRule {
        lhs: rename_term(&rule.lhs, rename),
        lhs_alternative: rule.lhs_alternative,
        rhs,
        requires: rename_predicates(&rule.requires, rename),
        ensures: rename_predicates(&rule.ensures, rename),
        attributes: rename_concreteness(&rule.attributes, &renaming),
        computed_attributes: ComputedRuleAttributes {
            contains_ac_symbols: computed.contains_ac_symbols,
            undefined_symbols: computed.undefined_symbols.clone(),
            variables: rename_set(&computed.variables),
            unbound_variables: rename_set(&computed.unbound_variables),
        },
        existentials: rename_set(&rule.existentials),
    };
    Some((renamed, renaming))
}

/// [`rename_apart`] for a predicate equation. Its left-hand side is a predicate that is matched
/// under quantifiers, so the subject's bound variables are in scope too: a rule variable must
/// not meet any variable of `subject`, free or bound.
pub(crate) fn rename_predicate_rule_apart(
    rule: &PredicateRewriteRule,
    subject: &Predicate,
    constraints: &[Predicate],
) -> Option<RenamedApart<PredicateRewriteRule>> {
    let mut variables = BTreeSet::new();
    collect_all_variables(std::slice::from_ref(&rule.lhs), &mut variables);
    collect_all_variables(&rule.rhs, &mut variables);
    collect_all_variables(&rule.requires, &mut variables);
    let mut scope = BTreeSet::new();
    collect_all_variables(std::slice::from_ref(subject), &mut scope);
    let term_clash = !variables.is_disjoint(&scope);
    let bound = rule.lhs.free_variables();
    let unbound = free_variables_of(&rule.rhs)
        .into_iter()
        .chain(free_variables_of(&rule.requires))
        .filter(|variable| !bound.contains(variable))
        .collect::<BTreeSet<_>>();
    if !term_clash && unbound.is_empty() {
        return None;
    }
    let constraint_variables = free_variables_of(constraints);
    if !term_clash && unbound.is_disjoint(&constraint_variables) {
        return None;
    }
    scope.extend(constraint_variables);
    let renaming = fresh_renaming(&variables, &scope);
    let rename = |variable: &Variable| {
        renaming
            .get(variable)
            .cloned()
            .unwrap_or_else(|| variable.clone())
    };
    let renamed = PredicateRewriteRule {
        lhs: rename_predicate(&rule.lhs, rename),
        rhs: rename_predicates(&rule.rhs, rename),
        requires: rename_predicates(&rule.requires, rename),
        attributes: rename_concreteness(&rule.attributes, &renaming),
    };
    Some((renamed, renaming))
}

fn free_variables_of(predicates: &[Predicate]) -> BTreeSet<Variable> {
    predicates
        .iter()
        .flat_map(Predicate::free_variables)
        .collect()
}

/// Each variable of `rule_variables` that `scope` also has, mapped to a variable of the same
/// kind and sort named `{name}!apart{counter}`, a name no variable of either has.
fn fresh_renaming(
    rule_variables: &BTreeSet<Variable>,
    scope: &BTreeSet<Variable>,
) -> BTreeMap<Variable, Variable> {
    let mut avoid = rule_variables
        .iter()
        .chain(scope)
        .map(|variable| variable.name.clone())
        .collect::<BTreeSet<_>>();
    rule_variables
        .intersection(scope)
        .map(|variable| {
            // Invariant: the counter only grows, so at most |avoid| + 1 names are tried.
            let name = loop {
                let counter = next_apart_counter();
                let name = crate::term::names::with_fresh_marker(
                    &variable.name,
                    crate::term::names::FreshMarker::Apart,
                    counter,
                );
                if avoid.insert(name.as_str().into()) {
                    break name;
                }
            };
            (variable.clone(), variable.with_name(name))
        })
        .collect()
}

/// Every variable a rule mentions, free or bound, and those of its free variables that its
/// left-hand side does not bind and that are not existentials: the sets `rename_apart` tests.
pub(crate) fn rule_variable_sets(
    lhs: &Term,
    rhs: &RuleRhs,
    requires: &[Predicate],
    ensures: &[Predicate],
    existentials: &BTreeSet<Variable>,
) -> (BTreeSet<Variable>, BTreeSet<Variable>) {
    let mut free = BTreeSet::new();
    let mut all = BTreeSet::new();
    match rhs {
        RuleRhs::Term(term) => free.extend(term.attributes().variables.iter().cloned()),
        RuleRhs::Disjunction(alternatives) => {
            for alternative in alternatives {
                free.extend(alternative.term.attributes().variables.iter().cloned());
                free.extend(free_variables_of(&alternative.ensures));
                collect_all_variables(&alternative.ensures, &mut all);
            }
        }
        RuleRhs::Predicates(predicates) => {
            free.extend(free_variables_of(predicates));
            collect_all_variables(predicates, &mut all);
        }
        RuleRhs::Top | RuleRhs::Bottom => {}
    }
    free.extend(free_variables_of(requires));
    free.extend(free_variables_of(ensures));
    collect_all_variables(requires, &mut all);
    collect_all_variables(ensures, &mut all);
    all.extend(free.iter().cloned());
    all.extend(lhs.attributes().variables.iter().cloned());
    all.extend(existentials.iter().cloned());
    let bound = &lhs.attributes().variables;
    let unbound = free
        .into_iter()
        .filter(|variable| !bound.contains(variable) && !existentials.contains(variable))
        .collect();
    (all, unbound)
}

/// Every variable of `predicates`, free or bound by a quantifier.
pub(crate) fn collect_all_variables(predicates: &[Predicate], variables: &mut BTreeSet<Variable>) {
    for predicate in predicates {
        predicate.visit_terms(&mut |term| {
            variables.extend(term.attributes().variables.iter().cloned());
        });
        collect_binders(predicate, variables);
    }
}

fn collect_binders(predicate: &Predicate, variables: &mut BTreeSet<Variable>) {
    match predicate {
        Predicate::Exists(variable, inner) | Predicate::Forall(variable, inner) => {
            variables.insert(variable.clone());
            collect_binders(inner, variables);
        }
        Predicate::Not(inner) => collect_binders(inner, variables),
        Predicate::And(inner) | Predicate::Or(inner) => {
            for predicate in inner {
                collect_binders(predicate, variables);
            }
        }
        Predicate::Implies(left, right) | Predicate::Iff(left, right) => {
            collect_binders(left, variables);
            collect_binders(right, variables);
        }
        Predicate::True
        | Predicate::False
        | Predicate::Term(_)
        | Predicate::Equals(..)
        | Predicate::Ceil(_)
        | Predicate::Floor(_)
        | Predicate::In(..) => {}
    }
}

/// `attributes` with each `concrete`/`symbolic` constraint that names a renamed variable naming
/// its new name. A constraint names a rule variable by its name without the `Rule#`/`Eq#`
/// marker and by its sort name, as `check_concreteness` reads it.
fn rename_concreteness(
    attributes: &RuleAttributes,
    renaming: &BTreeMap<Variable, Variable>,
) -> RuleAttributes {
    let mut attributes = attributes.clone();
    let Concreteness::Some(constrained) = &mut attributes.concreteness else {
        return attributes;
    };
    let unmarked = |variable: &Variable| {
        crate::term::names::split_marker(
            &variable.name,
            &[VariableProvenance::Rule, VariableProvenance::Equation],
        )
        .1
        .to_owned()
    };
    let mut renamed = BTreeMap::new();
    for (variable, fresh) in renaming {
        let crate::term::Sort::Application { name: sort, .. } = &variable.sort else {
            continue;
        };
        let key = (Name::from(unmarked(variable)), sort.clone());
        if let Some(kind) = constrained.remove(&key) {
            renamed.insert((Name::from(unmarked(fresh)), sort.clone()), kind);
        }
    }
    constrained.extend(renamed);
    attributes
}

impl RuleAttributes {
    pub fn parse(attributes: &kore::Attributes) -> Result<Self, AxiomError> {
        let priority = attributes
            .string(KoreAttribute::Priority)?
            .map(str::to_owned);
        let simplification_priority = attributes
            .string_or_empty(KoreAttribute::Simplification)?
            .map(str::to_owned);
        let owise = attributes.has(KoreAttribute::Owise);
        let present = [
            priority.as_ref().map(|_| KoreAttribute::Priority.as_str()),
            simplification_priority
                .as_ref()
                .map(|_| KoreAttribute::Simplification.as_str()),
            owise.then_some(KoreAttribute::Owise.as_str()),
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
        let label = attributes.string(KoreAttribute::Label)?.map(str::to_owned);
        let unique_id = attributes
            .string(KoreAttribute::UniqueId)?
            .map(str::to_owned)
            .or_else(|| label.clone())
            .unwrap_or_else(|| "UNKNOWN".into());
        Ok(Self {
            priority,
            label,
            unique_id,
            simplification: attributes.has(KoreAttribute::Simplification),
            preserves_definedness: attributes.has(KoreAttribute::PreservesDefinedness),
            concreteness: parse_concreteness(attributes)?,
            smt_lemma: attributes.has(KoreAttribute::SmtLemma),
            executable: !attributes.has(KoreAttribute::NonExecutable),
            origins: vec![RuleOrigin {
                source: attributes.string(KoreAttribute::Source)?.map(str::to_owned),
                location: attributes
                    .string(KoreAttribute::Location)?
                    .map(str::to_owned),
            }],
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

fn binder_term_alternatives(pattern: &kore::Pattern) -> Vec<&kore::Pattern> {
    let kore::Pattern::Or { arguments, .. } = pattern else {
        return vec![pattern];
    };
    if arguments.is_empty() {
        return vec![pattern];
    }
    arguments
        .iter()
        .flat_map(binder_term_alternatives)
        .collect()
}

fn extract_existentials(mut pattern: kore::Pattern) -> (kore::Pattern, Vec<kore::Variable>) {
    let mut variables = Vec::new();
    while let kore::Pattern::Exists { variable, body, .. } = &mut pattern {
        variables.push(variable.clone());
        pattern = std::mem::replace(body.as_mut(), kore::Pattern::String(String::new().into()));
    }
    (pattern, variables)
}

fn parse_concreteness(attributes: &kore::Attributes) -> Result<Concreteness, AxiomError> {
    let concrete = attribute_constrained_variables(attributes, KoreAttribute::Concrete)?;
    let symbolic = attribute_constrained_variables(attributes, KoreAttribute::Symbolic)?;
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
    attribute: KoreAttribute,
) -> Result<Option<Vec<String>>, AxiomError> {
    let Some(arguments) = attributes.arguments(attribute) else {
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
                    return Err(AxiomError::MalformedAttribute(attribute.as_str().into()));
                };
                if !arguments.is_empty() {
                    return Err(AxiomError::MalformedAttribute(attribute.as_str().into()));
                }
                Ok(format!("{}:{sort}", variable.name))
            }
            // Older generated definitions encoded the same pair as a string.
            kore::Pattern::String(value) => value
                .as_utf8()
                .map(str::to_owned)
                .map_err(|_| AxiomError::MalformedAttribute(attribute.as_str().into())),
            _ => Err(AxiomError::MalformedAttribute(attribute.as_str().into())),
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
    attributes.has(KoreAttribute::Constructor) && matches!(pattern, kore::Pattern::Implies { .. })
}

fn is_injection(pattern: &kore::Pattern) -> bool {
    matches!(pattern, kore::Pattern::Application { symbol, .. } if symbol.is(WellKnownSymbol::Inj))
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_sentence};

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

    fn top_rhs_definition(axiom: &str) -> Result<BackendDefinition, DefinitionError> {
        let source = format!(
            r#"[]
            module MAIN
                sort SortS{{}} []
                symbol f{{}}(SortS{{}}) : SortS{{}} [function{{}}()]
                symbol a{{}}() : SortS{{}} [constructor{{}}()]
                {axiom}
            endmodule []"#
        );
        BackendDefinition::internalize(
            &parse_definition(&source).expect("definition should parse"),
            "MAIN",
        )
    }

    fn function_binder_definition() -> BackendDefinition {
        BackendDefinition::internalize(
            &parse_definition(
                r#"[]
                module MAIN
                    sort SortS{} []
                    sort SortT{} []
                    symbol unary{}(SortS{}) : SortS{} [function{}()]
                    symbol binary{}(SortS{}, SortS{}) : SortS{} [function{}()]
                    symbol wrap{}(SortS{}) : SortS{} [constructor{}()]
                    symbol a{}() : SortS{} [constructor{}()]
                    symbol b{}() : SortS{} [constructor{}()]
                    symbol c{}() : SortS{} [constructor{}()]
                    symbol d{}() : SortS{} [constructor{}()]
                    symbol e{}() : SortS{} [constructor{}()]
                    symbol other{}() : SortT{} [constructor{}()]
                    symbol result{}() : SortS{} [constructor{}()]
                endmodule []"#,
            )
            .expect("definition should parse"),
            "MAIN",
        )
        .expect("definition should internalize")
    }

    fn internalize_function(source: &str) -> Result<Vec<InternalizedRule>, DefinitionError> {
        let classified = classify(source)
            .expect("axiom should classify")
            .expect("axiom should be executable");
        internalize_axiom(&function_binder_definition(), &classified)
    }

    fn function_lhs_argument_names(rules: &[InternalizedRule]) -> Vec<Vec<String>> {
        rules
            .iter()
            .map(|rule| {
                let InternalizedRule::Term(RuleKind::Function, rule) = rule else {
                    panic!("expected function rule");
                };
                let TermKind::Application { arguments, .. } = rule.lhs.kind() else {
                    panic!("expected function application lhs");
                };
                arguments
                    .iter()
                    .map(|argument| {
                        let TermKind::Application { symbol, .. } = argument.kind() else {
                            panic!("expected constructor application argument");
                        };
                        symbol.name.to_string()
                    })
                    .collect()
            })
            .collect()
    }

    #[test]
    fn internalizes_top_right_hand_sides_of_simplifications() {
        let definition = top_rhs_definition(
            r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(\top{SortS{}}(), \top{SortS{}}())
                )
            ) [label{}("erase-f"), simplification{}()]
            "#,
        )
        .expect("a simplification equation may have a top RHS");
        let rule = definition
            .simplification_theory
            .values()
            .flat_map(|groups| groups.values())
            .flatten()
            .next()
            .expect("simplification rule should be indexed");

        assert!(matches!(rule.rhs, RuleRhs::Top));
    }

    #[test]
    fn top_right_hand_sides_are_rejected_on_rewrite_axioms() {
        let error = top_rhs_definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(a{}(), \top{SortS{}}()),
                \and{SortS{}}(\top{SortS{}}(), \top{SortS{}}())
            ) [label{}("invalid-top-rewrite")]
            "#,
        )
        .expect_err("an executable rewrite still requires a term RHS");

        assert_eq!(
            error,
            DefinitionError::RulePattern(RulePatternError::MissingTerm)
        );
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
    fn rewrite_axioms_keep_their_concreteness_attribute() {
        let classified = classify(
            r#"axiom{} \rewrites{S{}}(
                \and{S{}}(lhs{}(X:S{}), \top{S{}}()), rhs{}()
            ) [symbolic{}()]"#,
        )
        .expect("axiom should classify")
        .expect("axiom should be executable");

        let ClassifiedAxiom::Rewrite { attributes, .. } = classified else {
            panic!("expected rewrite");
        };
        assert_eq!(
            attributes.concreteness,
            Concreteness::All(ConstraintKind::Symbolic)
        );
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
    fn expands_a_disjunctive_function_argument_binder() {
        let rules = internalize_function(
            r#"axiom{R} \implies{R}(
                \and{R}(
                    \equals{SortS{}, R}(a{}(), a{}()),
                    \and{R}(
                        \in{SortS{}, R}(
                            X:SortS{},
                            \or{SortS{}}(a{}(), b{}())
                        ),
                        \top{R}()
                    )
                ),
                \equals{SortS{}, R}(
                    unary{}(X:SortS{}),
                    \and{SortS{}}(
                        result{}(),
                        \ceil{SortS{}, SortS{}}(a{}())
                    )
                )
            ) [
                label{}("disjunctive-binder"),
                priority{}("17"),
                org'Stop'kframework'Stop'attributes'Stop'Source{}("Source(fixture.k)"),
                org'Stop'kframework'Stop'attributes'Stop'Location{}("Location(3,1,7,2)")
            ]"#,
        )
        .expect("each binder disjunct should produce a function rule");

        assert_eq!(
            function_lhs_argument_names(&rules),
            vec![vec![String::from("a")], vec![String::from("b")]]
        );
        let first = match &rules[0] {
            InternalizedRule::Term(_, rule) => rule,
            InternalizedRule::Predicate(_) => unreachable!(),
        };
        let second = match &rules[1] {
            InternalizedRule::Term(_, rule) => rule,
            InternalizedRule::Predicate(_) => unreachable!(),
        };
        assert_eq!(first.rhs, second.rhs);
        assert_eq!(first.requires, second.requires);
        assert_eq!(first.ensures, second.ensures);
        assert_eq!(first.requires.len(), 1);
        assert_eq!(first.ensures.len(), 1);
        assert_eq!(first.attributes, second.attributes);
        assert_eq!(first.attributes.priority, 17);
        assert_eq!(first.attributes.unique_id, "disjunctive-binder");
        assert_eq!(
            first.attributes.origins,
            [RuleOrigin {
                source: Some("Source(fixture.k)".into()),
                location: Some("Location(3,1,7,2)".into()),
            }]
        );
    }

    #[test]
    fn expands_nested_disjuncts_across_independent_function_binders() {
        let rules = internalize_function(
            r#"axiom{R} \implies{R}(
                \and{R}(
                    \top{R}(),
                    \and{R}(
                        \in{SortS{}, R}(
                            X:SortS{},
                            \or{SortS{}}(a{}(), \or{SortS{}}(b{}(), c{}()))
                        ),
                        \and{R}(
                            \in{SortS{}, R}(
                                Y:SortS{},
                                \or{SortS{}}(d{}(), e{}())
                            ),
                            \top{R}()
                        )
                    )
                ),
                \equals{SortS{}, R}(
                    binary{}(X:SortS{}, Y:SortS{}),
                    \and{SortS{}}(result{}(), \top{SortS{}}())
                )
            ) [label{}("binder-product")]"#,
        )
        .expect("nested binder disjuncts should form a Cartesian product");

        assert_eq!(
            function_lhs_argument_names(&rules),
            vec![
                vec![String::from("a"), String::from("d")],
                vec![String::from("a"), String::from("e")],
                vec![String::from("b"), String::from("d")],
                vec![String::from("b"), String::from("e")],
                vec![String::from("c"), String::from("d")],
                vec![String::from("c"), String::from("e")],
            ]
        );
    }

    #[test]
    fn rejects_a_wrong_sort_in_a_disjunctive_function_binder() {
        let error = internalize_function(
            r#"axiom{R} \implies{R}(
                \and{R}(
                    \top{R}(),
                    \and{R}(
                        \in{SortS{}, R}(
                            X:SortS{},
                            \or{SortS{}}(a{}(), other{}())
                        ),
                        \top{R}()
                    )
                ),
                \equals{SortS{}, R}(
                    unary{}(X:SortS{}),
                    \and{SortS{}}(result{}(), \top{SortS{}}())
                )
            ) [label{}("wrong-sort-disjunct")]"#,
        )
        .expect_err("every disjunct must match the binder variable sort");

        assert!(matches!(
            error,
            DefinitionError::RulePattern(RulePatternError::BinderSortMismatch(variable))
                if variable.name.as_ref() == "X"
        ));
    }

    #[test]
    fn rejects_disjunction_nested_below_a_binder_term_head() {
        let error = internalize_function(
            r#"axiom{R} \implies{R}(
                \and{R}(
                    \top{R}(),
                    \and{R}(
                        \in{SortS{}, R}(
                            X:SortS{},
                            wrap{}(\or{SortS{}}(a{}(), b{}()))
                        ),
                        \top{R}()
                    )
                ),
                \equals{SortS{}, R}(
                    unary{}(X:SortS{}),
                    \and{SortS{}}(result{}(), \top{SortS{}}())
                )
            ) [label{}("nested-term-or")]"#,
        )
        .expect_err("only a binder's top-level disjunction is admissible");

        assert_eq!(error, DefinitionError::ExpectedTerm("or"));
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

    fn collapse(sources: &[(&str, usize)]) -> Vec<ClassifiedAxiom> {
        collapse_equal_axioms(sources.iter().map(|&(source, sentence)| {
            let axiom = classify(source)
                .expect("axiom should classify")
                .expect("axiom should be a rule");
            (axiom, (Name::from("MAIN"), sentence))
        }))
    }

    fn origin_locations(axiom: &ClassifiedAxiom) -> Vec<&str> {
        axiom
            .attributes()
            .origins
            .iter()
            .map(|origin| {
                origin
                    .location
                    .as_deref()
                    .expect("fixture origins have a location")
            })
            .collect()
    }

    /// `pair(L0, L1) /\ C = a() => R`, with the side condition inside the left-hand side.
    fn guarded_rewrite(left: [&str; 2], condition: &str, result: &str, attributes: &str) -> String {
        let [first, second] = left;
        format!(
            r#"axiom{{}} \rewrites{{SortS{{}}}}(
                \and{{SortS{{}}}}(
                    pair{{}}({first}:SortS{{}}, {second}:SortS{{}}),
                    \equals{{SortS{{}}, SortS{{}}}}({condition}:SortS{{}}, a{{}}())
                ),
                \and{{SortS{{}}}}({result}:SortS{{}}, \top{{SortS{{}}}}())
            ) [UNIQUE'Unds'ID{{}}("shared"), {attributes}]"#
        )
    }

    fn location(line: usize) -> String {
        format!(
            r#"org'Stop'kframework'Stop'attributes'Stop'Location{{}}("Location({line},1,{line},9)")"#
        )
    }

    #[test]
    fn equal_axioms_collapse_under_one_renaming_of_the_whole_axiom() {
        let first = guarded_rewrite(["X", "Y"], "X", "Y", &location(1));
        let alpha = guarded_rewrite(["Y", "X"], "Y", "X", &location(2));
        // Equal to `first` if the left-hand side and the side condition were renamed separately.
        let other_guard = guarded_rewrite(["X", "Y"], "Y", "Y", &location(3));
        // `Z` would have to be the image of both `X` and `Y`.
        let merged_variables = guarded_rewrite(["Z", "Z"], "Z", "Z", &location(4));
        let relabelled = guarded_rewrite(
            ["X", "Y"],
            "X",
            "Y",
            &format!(r#"label{{}}("other"), {}"#, location(5)),
        );
        let alpha_again = guarded_rewrite(["A", "B"], "A", "B", &location(6));

        let collapsed = collapse(&[
            (&first, 0),
            (&alpha, 1),
            (&other_guard, 2),
            (&merged_variables, 3),
            (&relabelled, 4),
            (&alpha_again, 5),
        ]);

        assert_eq!(
            collapsed.iter().map(origin_locations).collect::<Vec<_>>(),
            [
                vec![
                    "Location(1,1,1,9)",
                    "Location(2,1,2,9)",
                    "Location(6,1,6,9)"
                ],
                vec!["Location(3,1,3,9)"],
                vec!["Location(4,1,4,9)"],
                vec!["Location(5,1,5,9)"],
            ]
        );
        assert!(
            collapsed
                .iter()
                .all(|axiom| axiom.attributes().unique_id == "shared")
        );
        // The first occurrence is the representative and keeps its variable names.
        let classified_first = classify(&first).unwrap().unwrap();
        let ClassifiedAxiom::Rewrite { lhs, .. } = &collapsed[0] else {
            panic!("expected a rewrite");
        };
        let ClassifiedAxiom::Rewrite { lhs: expected, .. } = &classified_first else {
            panic!("expected a rewrite");
        };
        assert_eq!(lhs, expected);
    }

    #[test]
    fn a_sentence_reached_twice_is_one_origin() {
        let rule = guarded_rewrite(["X", "Y"], "X", "Y", &location(1));
        let copy = guarded_rewrite(["X", "Y"], "X", "Y", &location(2));

        let collapsed = collapse(&[(&rule, 0), (&copy, 1), (&rule, 0)]);

        let [axiom] = collapsed.as_slice() else {
            panic!("expected one rule: {collapsed:?}");
        };
        assert_eq!(
            origin_locations(axiom),
            ["Location(1,1,1,9)", "Location(2,1,2,9)"]
        );
    }

    /// `unary(Arg) = Result` for `Arg` in `Result`, with `concrete(Constrained)`.
    fn concrete_equation(argument: &str, result: &str, constrained: &str, line: usize) -> String {
        format!(
            r#"axiom{{R}} \implies{{R}}(
                \and{{R}}(
                    \top{{R}}(),
                    \and{{R}}(\in{{SortS{{}}, R}}({argument}:SortS{{}}, {result}:SortS{{}}), \top{{R}}())
                ),
                \equals{{SortS{{}}, R}}(
                    unary{{}}({argument}:SortS{{}}),
                    \and{{SortS{{}}}}({result}:SortS{{}}, \top{{SortS{{}}}}())
                )
            ) [UNIQUE'Unds'ID{{}}("equation"), concrete{{}}({constrained}:SortS{{}}), {}]"#,
            location(line)
        )
    }

    #[test]
    fn concreteness_constraints_are_compared_through_the_renaming() {
        let first = concrete_equation("X0", "VarA", "VarA", 1);
        let alpha = concrete_equation("Y0", "VarB", "VarB", 2);
        let constrains_the_argument = concrete_equation("Y0", "VarB", "Y0", 3);
        let constrains_no_variable = concrete_equation("X0", "VarA", "VarB", 4);

        let collapsed = collapse(&[
            (&first, 0),
            (&alpha, 1),
            (&constrains_the_argument, 2),
            (&constrains_no_variable, 3),
        ]);

        assert!(matches!(collapsed[0], ClassifiedAxiom::Function { .. }));
        assert_eq!(
            collapsed.iter().map(origin_locations).collect::<Vec<_>>(),
            [
                vec!["Location(1,1,1,9)", "Location(2,1,2,9)"],
                vec!["Location(3,1,3,9)"],
                vec!["Location(4,1,4,9)"],
            ]
        );
    }

    #[test]
    fn concreteness_entries_naming_no_pattern_variable_are_vacuous() {
        let constrained_u = guarded_rewrite(
            ["X", "Y"],
            "X",
            "Y",
            &format!("concrete{{}}(U:SortS{{}}), {}", location(1)),
        );
        let constrained_v = guarded_rewrite(
            ["X", "Y"],
            "X",
            "Y",
            &format!("concrete{{}}(V:SortS{{}}), {}", location(2)),
        );
        let unconstrained = guarded_rewrite(["X", "Y"], "X", "Y", &location(3));
        // `X` is a pattern variable, so this constraint is live and keeps the rule apart.
        let constrained_x = guarded_rewrite(
            ["X", "Y"],
            "X",
            "Y",
            &format!("concrete{{}}(X:SortS{{}}), {}", location(4)),
        );

        let collapsed = collapse(&[
            (&constrained_u, 0),
            (&constrained_v, 1),
            (&unconstrained, 2),
            (&constrained_x, 3),
        ]);

        assert_eq!(
            collapsed.iter().map(origin_locations).collect::<Vec<_>>(),
            [
                vec![
                    "Location(1,1,1,9)",
                    "Location(2,1,2,9)",
                    "Location(3,1,3,9)"
                ],
                vec!["Location(4,1,4,9)"],
            ]
        );
    }

    #[test]
    fn axioms_without_unique_ids_collapse_by_content_within_one_shape() {
        let rewrite = |left: [&str; 2], condition: &str, result: &str, line: usize| {
            guarded_rewrite(left, condition, result, &location(line))
                .replace(r#"UNIQUE'Unds'ID{}("shared"), "#, "")
        };
        let first = rewrite(["X", "Y"], "X", "Y", 1);
        let alpha = rewrite(["A", "B"], "A", "B", 2);
        let other = rewrite(["X", "Y"], "Y", "X", 3);
        let shape = |source: &str| axiom_shape(&classify(source).unwrap().unwrap());
        assert_eq!(shape(&first), shape(&alpha));
        assert_eq!(
            classify(&first).unwrap().unwrap().attributes().unique_id,
            "UNKNOWN"
        );

        let collapsed = collapse(&[(&first, 0), (&other, 1), (&alpha, 2)]);

        assert_eq!(
            collapsed.iter().map(origin_locations).collect::<Vec<_>>(),
            [
                vec!["Location(1,1,1,9)", "Location(2,1,2,9)"],
                vec!["Location(3,1,3,9)"],
            ]
        );
    }

    #[test]
    fn renaming_apart_picks_names_that_neither_side_uses() {
        let classified = classify(
            r#"axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    binary{}(X:SortS{}, Z:SortS{}),
                    \and{SortS{}}(X:SortS{}, \top{SortS{}}())
                )
            ) [simplification{}(), concrete{}(X:SortS{})]"#,
        )
        .expect("axiom should classify")
        .expect("axiom should be a rule");
        let [InternalizedRule::Term(_, rule)] =
            &internalize_axiom(&function_binder_definition(), &classified).unwrap()[..]
        else {
            panic!("expected one term rule");
        };
        let sort = crate::term::Sort::simple("SortS");
        let x = Variable::new("Eq#X", sort.clone());
        let z = Variable::new("Eq#Z", sort.clone());
        assert!(rule.lhs.attributes().variables.contains(&x));
        let subject = BTreeSet::from([x.clone(), Variable::new("Eq#X!0", sort.clone())]);

        let (renamed, renaming) =
            rename_apart(rule, &subject, &[]).expect("the rule shares Eq#X with the subject");

        let [(original, fresh)] = renaming.iter().collect::<Vec<_>>()[..] else {
            panic!("only the shared variable is renamed: {renaming:?}");
        };
        assert_eq!(original, &x);
        assert_eq!((fresh.kind, &fresh.sort), (x.kind, &x.sort));
        let (base, counter) = fresh
            .name
            .split_once("!apart")
            .expect("the fresh name carries the apart marker");
        assert_eq!(base, "Eq#X");
        assert!(counter.bytes().all(|byte| byte.is_ascii_digit()));
        assert_eq!(
            renamed.lhs.attributes().variables,
            BTreeSet::from([fresh.clone(), z.clone()])
        );
        assert_eq!(renamed.rhs, RuleRhs::Term(Term::variable(fresh.clone())));
        assert_eq!(
            renamed.attributes.concreteness,
            Concreteness::Some(BTreeMap::from([(
                (Name::from(&fresh.name["Eq#".len()..]), Name::from("SortS")),
                ConstraintKind::Concrete
            )]))
        );
        assert_eq!(
            renamed.computed_attributes.variables,
            BTreeSet::from([fresh.clone(), z])
        );
        assert!(rename_apart(&renamed, &subject, &[]).is_none());

        // A second renaming, as a nested evaluation would make, mints a different name.
        let (_, again) = rename_apart(rule, &subject, &[]).expect("still shared");
        assert_ne!(again[&x], *fresh);
    }

    #[test]
    fn a_requires_only_variable_is_renamed_apart_from_the_path_condition() {
        let classified = classify(
            r#"axiom{R} \implies{R}(
                \equals{SortBool{}, R}(g{}(Y:SortS{}), \dv{SortBool{}}("true")),
                \equals{SortS{}, R}(
                    unary{}(X:SortS{}),
                    \and{SortS{}}(a{}(), \top{SortS{}}())
                )
            ) [simplification{}()]"#,
        )
        .expect("axiom should classify")
        .expect("axiom should be a rule");
        let definition = BackendDefinition::internalize(
            &parse_definition(
                r#"[]
                module MAIN
                    sort SortS{} []
                    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                    symbol unary{}(SortS{}) : SortS{} [function{}()]
                    symbol g{}(SortS{}) : SortBool{} [function{}()]
                    symbol a{}() : SortS{} [constructor{}()]
                endmodule []"#,
            )
            .unwrap(),
            "MAIN",
        )
        .unwrap();
        let [InternalizedRule::Term(_, rule)] =
            &internalize_axiom(&definition, &classified).unwrap()[..]
        else {
            panic!("expected one term rule");
        };
        let sort = crate::term::Sort::simple("SortS");
        let y = Variable::new("Eq#Y", sort.clone());
        assert_eq!(
            rule.computed_attributes.unbound_variables,
            BTreeSet::from([y.clone()])
        );
        let subject = BTreeSet::new();
        assert!(rename_apart(rule, &subject, &[]).is_none());
        let path = [Predicate::Equals(
            Term::variable(y.clone()),
            Term::variable(y.clone()),
        )];

        let (renamed, renaming) =
            rename_apart(rule, &subject, &path).expect("the path mentions the rule's Eq#Y");

        assert_eq!(renaming.keys().collect::<Vec<_>>(), [&y]);
        assert!(!renamed.requires[0].free_variables().contains(&y));
    }
}
