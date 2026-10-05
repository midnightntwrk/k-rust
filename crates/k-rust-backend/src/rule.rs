//! ```toml algorithm
//! id = "backend.rule.select"
//! name = "single-symbol rule selection"
//! sites = ["applicable_groups", "applicable_rewrite_groups", "term_index", "rule_index", "subject_index", "fetch_k_cell", "first_with_k_cell", "find_k_cells"]
//! variable = "k = index keys; c = candidate rules returned for one step; r = rules stored under the subject's key and the Variable key for rigid subjects, or all rules for a non-rigid subject; d = depth of the subject's one <k> cell; a = children of a node on the path to it"
//! counters = []
//! span = "per call"
//! no_counter = "rule selection has no dedicated counter; RewriteRuleAttempts is bumped by apply_rule_with_match for each candidate the caller tries"
//! lean = ["KRust.TermAttributes.rule_index_same"]
//!
//! [[cost]]
//! mode = "rigid subject"
//! bound = "O(log k) index lookups plus O(r) covers checks plus O(c) candidate clones"
//!
//! [[cost]]
//! mode = "non-rigid subject"
//! bound = "O(k log k) index lookups plus O(r) covers checks plus O(c) candidate clones"
//!
//! [[cost]]
//! mode = "subject_index"
//! bound = "O(1) unless the subject's stored k_cells count is 1, then O(d x a) to fetch the cell"
//! ```
//!
//! Axiom-shape classification and rule indexes. Every theory uses the top-symbol `TermIndex`;
//! rewrite rules additionally filter by the head of their `<k>` cell and by the item after it
//! (the frozen context a cooling rule waits for). A subject's keys are a `SubjectKey`, built
//! only by `subject_index` from `term::head::classify_value`; a rule's cell keys are built by
//! `rule_index` from `term::head::classify_pattern` with the left-hand side read as written.
//! Candidate count is the exact-symbol then variable-symbol sequence for a subject whose root is
//! fixed, or every term-index bucket for any other subject (`SubjectKey::buckets`), filtered by
//! `rule.index.covers(subject)`. Selection costs O(log k) index lookups plus one `covers` check
//! per rule in the selected buckets; `Counter::RewriteRuleAttempts` is bumped by the caller per
//! candidate tried.
//!
//! The index uses `Anything` for absent or malformed `<k>` cells, variables, functions, macro
//! and alias applications, uninterpreted heads, subject-side `anywhere` heads that
//! are not overloaded or whose root is not fixed, and `anywhere` heads in the item after the
//! head. A fixed overloaded head is `Overloaded`, which covers only `Overloaded`, `Anywhere` and
//! `Anything`; on the subject side an overloaded `anywhere` head is fixed only with evidence
//! that it is a normal form on every instance (the simplifier's certificate or
//! `BackendDefinition::instance_normal`), since an equation may give an instance of any other
//! application another head. A rule's non-overloaded `anywhere` head is `Anywhere`. It strips
//! injections and meets conjunctions (`CellIndex::meet`); `None`, two distinct rigid
//! conjuncts, covers only `Anything`. These
//! conservative cases correspond to the matcher's overload, AC, variable, injection, and
//! symbolic-function paths; a later matcher extension must keep this list sound.
//!
//! A subject's keys hold for the term they were computed from, and only for it: the matcher
//! refutes a dropped candidate against that term. An `anywhere` head keyed `Overloaded`, a
//! function keyed `Anything`, or the `<k>` cell itself can change when the term is simplified,
//! so a caller that applies rules to a simplified term (the remainder of a step) selects them
//! again for it.

use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use k_rust_kore::kore::ast::{self as kore, KoreString};
use k_rust_kore::kore::walk;
use k_rust_kore::measure::{self, Algorithm};
use k_rust_kore::names::{
    DEFAULT_RULE_PRIORITY, KoreAttribute, MalformedAttribute, OWISE_RULE_PRIORITY, WellKnownSymbol,
    rule_priority,
};

use crate::{
    condition::Condition,
    definition::{BackendDefinition, DefinitionError, UnlicensedInjectionSite},
    substitution::{Substitution, substitute},
    term::{
        AlgebraicAxioms, HeadRole, Name, Sort, Term, TermKind, Variable,
        head::{
            CertifiedOrScanned, FixedRoot, Head, PatternReading, Shape, classify_pattern,
            classify_value,
        },
        names::{VariableProvenance, split_marker},
    },
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
    /// For an equation (function, simplification or ceil), the free variables of its
    /// right-hand side and `ensures` that its left-hand side does not bind, in the definition's
    /// spelling ([`equation_unbound_result_variables`]); empty for a rewrite rule. An instance
    /// of such an equation is not used (`ConditionIndeterminacy::UnboundResultVariables`).
    pub unbound_result_variables: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RewriteRule {
    pub lhs: Term,
    pub lhs_alternative: Option<usize>,
    pub rhs: RuleRhs,
    pub requires: Condition,
    pub ensures: Condition,
    pub attributes: RuleAttributes,
    pub computed_attributes: ComputedRuleAttributes,
    pub existentials: BTreeSet<Variable>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PredicateRewriteRule {
    pub lhs: Predicate,
    pub rhs: Vec<Predicate>,
    pub requires: Condition,
    pub attributes: RuleAttributes,
    /// The free variables of `rhs` that `lhs` does not bind, in the definition's spelling, as
    /// [`ComputedRuleAttributes::unbound_result_variables`] states them for a term equation.
    pub unbound_result_variables: Vec<String>,
    /// The variable sets `rename_predicate_rule_apart` tests, computed once from the three
    /// parts above by [`PredicateRewriteRule::new`].
    pub variables: PredicateRuleVariables,
}

/// Every variable a predicate equation mentions, free or bound, and those free variables of
/// its right-hand side and requires that its left-hand side does not bind.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PredicateRuleVariables {
    pub all: BTreeSet<Variable>,
    pub unbound: BTreeSet<Variable>,
}

impl PredicateRewriteRule {
    pub fn new(
        lhs: Predicate,
        rhs: Vec<Predicate>,
        requires: Condition,
        attributes: RuleAttributes,
    ) -> Self {
        let mut all = BTreeSet::new();
        collect_all_variables(std::slice::from_ref(&lhs), &mut all);
        collect_all_variables(&rhs, &mut all);
        collect_all_variables(requires.iter(), &mut all);
        let bound = lhs.free_variables();
        let unbound_result = free_variables_of(&rhs)
            .into_iter()
            .filter(|variable| !bound.contains(variable))
            .collect::<BTreeSet<_>>();
        let unbound_result_variables = definition_spellings(&unbound_result);
        let mut unbound = unbound_result;
        unbound.extend(
            free_variables_of(requires.iter())
                .into_iter()
                .filter(|variable| !bound.contains(variable)),
        );
        Self {
            lhs,
            rhs,
            requires,
            attributes,
            unbound_result_variables,
            variables: PredicateRuleVariables { all, unbound },
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RhsAlternative {
    pub term: Term,
    pub ensures: Condition,
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
    /// A conjunction of two distinct rigid heads (`meet`): it matches no rigid head, and only a
    /// wildcard (a variable or a function, keyed `Anything`) on the other side leaves the
    /// matcher undecided.
    None,
    Anything,
    Constructor(Name),
    /// A head in some `symbol-overload` relation that the rewrite matcher treats as rigid in
    /// the term the key is computed from: a constructor, or a production with `anywhere`
    /// equations that is not a declared function (on the subject side, in an instance-normal
    /// application only). Overload resolution may lift it to another
    /// production of its relation. An `anywhere` head is rigid only in that term: simplifying
    /// the term (a remainder under a stronger path condition) may rewrite it to any
    /// constructor, so a key computed from one term must not select rules for its simplified
    /// successor (`fold_lower_priority_groups` selects again).
    Overloaded,
    /// A production with `anywhere` equations that is not a declared function and is in no
    /// `symbol-overload` relation. The rewrite matcher reads it as written, fixed
    /// (`matching::matcher_root_policy`), and refutes it against a different rigid head, except
    /// against another non-constructor
    /// head under injections from unrelated sorts that may overlap, which it defers; so it
    /// covers `Overloaded` too. Only a rule's key uses it: a subject's `anywhere` head, which
    /// its equations may still rewrite, is `Anything` (`subject_index`). A function that is
    /// evaluated rather than matched is `Anything` on both sides.
    Anywhere(Name),
    Value(KoreString),
    Map,
    List,
    Set,
}

impl CellIndex {
    pub fn covers(&self, subject: &Self) -> bool {
        matches!(self, Self::Anything)
            || matches!(subject, Self::Anything)
            || (self == subject && !matches!(self, Self::None))
            || matches!(
                (self, subject),
                (Self::Overloaded, Self::Anywhere(_)) | (Self::Anywhere(_), Self::Overloaded)
            )
    }

    /// The key of a conjunction `left /\ right`. The matcher matches each conjunct against the
    /// same term, so the conjunction is refuted where either conjunct is, and the key must still
    /// cover every term that both conjuncts' keys cover. A function conjunct is `Anything` and
    /// leaves the other key; two distinct `Overloaded`/`Anywhere` keys both cover `Overloaded`;
    /// any other two distinct keys share only `Anything`, which `None` covers.
    pub fn meet(self, other: Self) -> Self {
        match (self, other) {
            (Self::None, _) | (_, Self::None) => Self::None,
            (Self::Anything, other) | (other, Self::Anything) => other,
            (left, right) if left == right => left,
            (Self::Overloaded | Self::Anywhere(_), Self::Overloaded | Self::Anywhere(_)) => {
                Self::Overloaded
            }
            _ => Self::None,
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RuleIndex(Vec<CellIndex>);

impl RuleIndex {
    /// Whether a rule with these keys may match the subject `subject` was computed from: every
    /// cell key covers the subject's.
    pub fn covers(&self, subject: &SubjectKey) -> bool {
        let subject = subject.cells();
        self.0.len() == subject.len()
            && self
                .0
                .iter()
                .zip(subject)
                .all(|(rule, subject)| rule.covers(subject))
    }

    pub fn cells(&self) -> &[CellIndex] {
        &self.0
    }
}

/// The keys rewrite selection uses for one subject, built only by [`subject_index`]: whether the
/// subject's root is fixed, with its term index, and the cell keys of its `<k>` cell. Two subjects
/// with equal keys are offered the same candidates, so a caller that reselects rules only when the
/// keys change (the rewrite loop's remainder) compares this whole key, root fixedness included.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SubjectKey {
    top: TopKey,
    cells: RuleIndex,
}

/// The subject's term index, and whether its root is the root of every value the subject
/// denotes (`term::head::classify_value`).
#[derive(Clone, Debug, Eq, PartialEq)]
enum TopKey {
    /// The root is fixed: a rule stored under another root's bucket has a left-hand side whose
    /// root differs from the subject's, which the rewrite matcher refutes.
    Fixed(TermIndex),
    /// The root may be the root of another value (a variable, a conjunction, a function
    /// application, an equation head without evidence): every bucket is offered, the own bucket
    /// first.
    Open(TermIndex),
}

impl SubjectKey {
    /// The cell keys: the head of the subject's one `<k>` cell and the item after it.
    pub fn cells(&self) -> &[CellIndex] {
        self.cells.cells()
    }

    /// The term-index buckets this key offers, in trial order: the own bucket, then `Variable`,
    /// then, for an open root only, every other bucket of `theory` in `TermIndex` order. The
    /// single definition of which buckets a subject may match.
    #[deny(clippy::wildcard_enum_match_arm)]
    fn buckets<'r>(&'r self, theory: &'r RewriteTheory) -> impl Iterator<Item = &'r TermIndex> {
        const VARIABLE: &TermIndex = &TermIndex::Variable;
        let (own, open) = match &self.top {
            TopKey::Fixed(own) => (own, false),
            TopKey::Open(own) => (own, true),
        };
        let variable = (own != VARIABLE).then_some(VARIABLE);
        let others = open
            .then(|| {
                theory
                    .keys()
                    .filter(move |key| *key != own && *key != VARIABLE)
            })
            .into_iter()
            .flatten();
        std::iter::once(own).chain(variable).chain(others)
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
    /// Constraints keyed by the variable's name without its provenance marker and its full sort.
    Some(BTreeMap<(Name, Sort), ConstraintKind>),
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

/// Records the application roots of equations whose algebraic tags deny structural freeness.
/// Both loading and classification use this predicate so dropping an equation preserves its facts.
pub(crate) fn algebraic_axiom_roots(
    pattern: &kore::Pattern,
    attributes: &kore::Attributes,
) -> Option<Result<(AlgebraicAxioms, Vec<Name>), AxiomError>> {
    let kore::Pattern::Equals { left, right, .. } = pattern else {
        return None;
    };
    // Overload equations are executable, even when they carry an algebraic tag. Preserve
    // their classification priority and record facts only for equations we actually drop.
    if attributes.has(KoreAttribute::SymbolOverload) || attributes.has(KoreAttribute::Overload) {
        return None;
    }
    let mut facts = AlgebraicAxioms::default();
    for (attribute, fact) in [
        (KoreAttribute::Assoc, AlgebraicAxioms::assoc()),
        (KoreAttribute::Comm, AlgebraicAxioms::comm()),
        (KoreAttribute::Idem, AlgebraicAxioms::idem()),
        (KoreAttribute::Unit, AlgebraicAxioms::unit()),
    ] {
        if attributes.has(attribute) {
            facts = facts.union(fact);
        }
    }
    if facts.is_empty() {
        return None;
    }
    let roots = [left.as_ref(), right.as_ref()]
        .into_iter()
        .filter_map(|side| match side {
            kore::Pattern::Application { symbol, .. } => Some(Name::from(symbol.name.as_str())),
            _ => None,
        })
        .collect::<Vec<_>>();
    Some(if roots.is_empty() {
        Err(AxiomError::MalformedEquation)
    } else {
        Ok((facts, roots))
    })
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
    if let Some(facts) = algebraic_axiom_roots(pattern, syntax_attributes) {
        return facts.map(|_| None);
    }
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
                if matches!(left.as_ref(), kore::Pattern::Variable(found) if found == variable.as_ref()))
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
            if syntax_attributes.has(KoreAttribute::Simplification)
                && is_injection(left)
                && is_injection(right) =>
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
pub type SentenceKey = (Name, usize);

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
/// declaring module is not compared because it locates the sentence and does not affect its
/// instances.
///
/// The first axiom of a class in declaration order is kept with its variable names and sentence
/// key for load diagnostics, and the origins of the others are appended to its origin list in
/// declaration order. A sentence visited again through another import path adds no origin.
/// Axioms that share a `UNIQUE_ID` but differ in anything compared above stay separate rules.
/// Each axiom is hashed once by its `UNIQUE_ID` and a shape that ignores variable names
/// (`axiom_shape`), and comparisons, each one traversal of the smaller axiom, run only between
/// axioms with one hash key, so a definition without `UNIQUE_ID`s does not compare every pair
/// of its axioms.
pub(crate) fn collapse_equal_axioms(
    axioms: impl IntoIterator<Item = (ClassifiedAxiom, SentenceKey)>,
) -> Vec<(ClassifiedAxiom, SentenceKey)> {
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
        .into_iter()
        .zip(sentences.into_iter().map(|sentences| {
            sentences
                .into_iter()
                .next()
                .expect("each class records its first sentence")
        }))
        .collect()
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
) -> BTreeMap<&'c (Name, Sort), &'c ConstraintKind> {
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

/// Load only alternatives that can match licensed values.
/// A matched unlicensed injection denotes no value under I-INJ; dropping its alternative
/// preserves matching on licensed values and prevents unification from binding junk.
///
/// ```toml algorithm-site
/// id = "backend.definition.internalize"
/// role = "part"
/// sites = ["internalize_axiom"]
/// ```
pub fn internalize_axiom(
    definition: &BackendDefinition,
    axiom: &ClassifiedAxiom,
    sentence: &SentenceKey,
) -> Result<Vec<InternalizedRule>, DefinitionError> {
    let injection_role = UnlicensedInjectionSite::InAxiom;
    let internalize = || match axiom {
        ClassifiedAxiom::Rewrite {
            sort_parameters,
            lhs,
            rhs,
            existentials,
            attributes,
            ..
        } => {
            let lhs_alternatives = term_disjuncts(lhs);
            let split = lhs_alternatives.len() > 1;
            let mut live = Vec::new();
            for (index, lhs) in lhs_alternatives.into_iter().enumerate() {
                if let Some((lhs, requires)) =
                    live_matched(internalize_rule_pattern_with_position(
                        definition,
                        &lhs,
                        sort_parameters,
                        injection_role,
                        Some((attributes, sentence)),
                    ))?
                {
                    live.push((index, lhs, requires));
                }
            }
            if live.is_empty() {
                return Ok(vec![]);
            }
            let (rhs, ensures) =
                internalize_term_rhs(definition, rhs, sort_parameters, injection_role)?;
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
            live.into_iter()
                .map(|(index, lhs, requires)| {
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
                let Some(lhs) = live_matched(internalize_predicate(
                    definition,
                    lhs,
                    sort_parameters,
                    UnlicensedInjectionSite::InAxiomMatched,
                ))?
                else {
                    return Ok(vec![]);
                };
                let requires =
                    internalize_predicates(definition, requires, sort_parameters, injection_role)?;
                let rhs = internalize_predicates(definition, rhs, sort_parameters, injection_role)?;
                let rename =
                    |variable: &Variable| variable.with_provenance(VariableProvenance::Equation);
                let mut lhs = rename_predicates(&[lhs], rename);
                return Ok(vec![InternalizedRule::Predicate(
                    PredicateRewriteRule::new(
                        lhs.pop().expect("one predicate was internalized"),
                        rename_predicates(&rhs, rename),
                        Condition::new(rename_predicates(&requires, rename)),
                        attributes.clone(),
                    ),
                )]);
            }
            if contains_term_or(lhs) {
                return Err(DefinitionError::RulePattern(
                    RulePatternError::TermDisjunction,
                ));
            }
            let Some(lhs) = live_matched(definition.internalize_term_with_validation(
                lhs,
                sort_parameters,
                injection_role,
            ))?
            else {
                return Ok(vec![]);
            };
            let requires =
                internalize_predicates(definition, requires, sort_parameters, injection_role)?;
            let (rhs, ensures) =
                internalize_term_rhs(definition, rhs, sort_parameters, injection_role)?;
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
            let Some(lhs) = live_matched(definition.internalize_term_with_validation(
                lhs,
                sort_parameters,
                injection_role,
            ))?
            else {
                return Ok(vec![]);
            };
            let mut binding_alternatives = vec![Substitution::new()];
            for binder in binders {
                let variable =
                    definition.internalize_variable(&binder.variable, sort_parameters)?;
                let alternatives = binder_term_alternatives(&binder.pattern)
                    .into_iter()
                    .filter_map(|pattern| {
                        live_matched(definition.internalize_term_with_validation(
                            pattern,
                            sort_parameters,
                            injection_role,
                        ))
                        .transpose()
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                if alternatives.is_empty() {
                    return Ok(vec![]);
                }
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
                internalize_predicates(definition, requires, sort_parameters, injection_role)?;
            let (rhs, ensures) =
                internalize_term_rhs(definition, rhs, sort_parameters, injection_role)?;
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
            let Some(lhs) = live_matched(definition.internalize_term_with_validation(
                lhs,
                sort_parameters,
                injection_role,
            ))?
            else {
                return Ok(vec![]);
            };
            let requires =
                internalize_predicates(definition, requires, sort_parameters, injection_role)?;
            let rhs = internalize_predicates(definition, rhs, sort_parameters, injection_role)?;
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
            let requires = Condition::new(requires);
            Ok(vec![InternalizedRule::Term(
                RuleKind::Ceil,
                RewriteRule {
                    lhs,
                    lhs_alternative: None,
                    rhs,
                    requires,
                    ensures: Condition::default(),
                    attributes: attributes.clone(),
                    computed_attributes,
                    existentials: BTreeSet::new(),
                },
            )])
        }
    };
    let mut rules = internalize()
        .map_err(|error| written_injection_error(error, axiom.attributes(), sentence))?;
    for rule in &mut rules {
        if let InternalizedRule::Term(
            RuleKind::Function | RuleKind::Simplification | RuleKind::Ceil,
            rule,
        ) = rule
        {
            rule.computed_attributes.unbound_result_variables =
                equation_unbound_result_variables(rule);
        }
    }
    Ok(rules)
}

/// The free variables of a term equation's right-hand side and `ensures` that its left-hand
/// side does not bind, in the definition's spelling.
///
/// An equation `l = r requires R ensures E` is an axiom closed over all its variables. A
/// variable `Y` of `r` or `E` that `l` does not bind is not fixed by matching `l`: the axiom
/// states `l = r` for every value of `Y` that satisfies `R` (and `E`). Such an equation is
/// consistent and meaningful when `R` determines `Y` (`f(X) = Y requires Y = X + 1` is
/// `f(X) = X + 1`), but the evaluator has no witness for `Y`; the instance `r` with the
/// equation's own `Y` left free would name no value of the request. The definition is loaded,
/// and an instance of such an equation is not used: once its `requires` is not refuted, the
/// attempt is indeterminate (`ConditionIndeterminacy::UnboundResultVariables`). A variable only
/// of the `requires` never reaches a result and is not listed: the `requires` is decided with
/// it free, so it holds only if it holds for every value of the variable, and it is refuted
/// only if it holds for none.
fn equation_unbound_result_variables(rule: &RewriteRule) -> Vec<String> {
    let mut free = free_variables_of(rule.ensures.iter());
    match &rule.rhs {
        RuleRhs::Term(term) => free.extend(term.attributes().variables.iter().cloned()),
        RuleRhs::Disjunction(alternatives) => {
            for alternative in alternatives {
                free.extend(alternative.term.attributes().variables.iter().cloned());
                free.extend(free_variables_of(alternative.ensures.iter()));
            }
        }
        RuleRhs::Predicates(predicates) => free.extend(free_variables_of(predicates)),
        RuleRhs::Top | RuleRhs::Bottom => {}
    }
    let bound = &rule.lhs.attributes().variables;
    free.retain(|variable| !bound.contains(variable));
    definition_spellings(&free)
}

/// The names of equation variables as the definition spells them, without the backend's
/// equation marker.
fn definition_spellings(variables: &BTreeSet<Variable>) -> Vec<String> {
    variables
        .iter()
        .map(|variable| {
            split_marker(&variable.name, &[VariableProvenance::Equation])
                .1
                .into_owned()
        })
        .collect()
}

/// How an error names an axiom: its `UNIQUE_ID`, else its label, else its source location,
/// else its position among the module's sentences.
fn axiom_identity(attributes: &RuleAttributes, sentence: &SentenceKey) -> String {
    // The index counts all module sentences, including sorts, symbols and imports.
    let fallback = || {
        format!(
            "module {}, sentence index {} (zero-based)",
            sentence.0, sentence.1
        )
    };
    if attributes.unique_id != "UNKNOWN" {
        attributes.unique_id.clone()
    } else if let Some(label) = &attributes.label {
        // An explicit UNIQUE_ID of "UNKNOWN" overrides the parser's label fallback.
        label.clone()
    } else {
        attributes.origins.first().map_or_else(fallback, |origin| {
            match (&origin.source, &origin.location) {
                (Some(source), Some(location)) => format!("source {source}, location {location}"),
                (Some(source), None) => format!("source {source}"),
                (None, Some(location)) => format!("location {location}"),
                (None, None) => fallback(),
            }
        })
    }
}

pub(crate) fn written_injection_error(
    error: DefinitionError,
    attributes: &RuleAttributes,
    sentence: &SentenceKey,
) -> DefinitionError {
    let DefinitionError::NotSubsort { source, target } = error else {
        return error;
    };
    let axiom = axiom_identity(attributes, sentence);
    DefinitionError::UnlicensedInjection {
        source,
        target,
        axiom,
        sentence: Box::new(sentence.clone()),
    }
}

/// A matched pattern containing an unlicensed injection has no licensed instances.
fn live_matched<T>(result: Result<T, DefinitionError>) -> Result<Option<T>, DefinitionError> {
    match result {
        Ok(value) => Ok(Some(value)),
        Err(DefinitionError::NotSubsort { .. }) => Ok(None),
        Err(error) => Err(error),
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
    index_of(definition, term, KeySide::Rule)
}

/// The side of the matcher a key is computed for: a rule's left-hand side, matched as written,
/// or a subject, whose `anywhere` applications denote the values of their normal forms.
#[derive(Clone, Copy, Eq, PartialEq)]
enum KeySide {
    Rule,
    Subject,
}

fn index_of(definition: &BackendDefinition, term: &Term, side: KeySide) -> RuleIndex {
    // The index keys on the one `<k>` cell not nested in a `<k>` cell, and on nothing when there
    // are none or several. The stored count, saturated at 2, says which case holds, and the cell
    // is fetched only when it is 1: the same cell as the first that `find_k_cells` collects
    // (`rule_index_same` of lean/KRust/TermAttributes.lean).
    let cell = match term.attributes().k_cells() {
        1 => fetch_k_cell(term),
        _ => None,
    };
    // The second key is the item after the head, when the cell is `kseq(head, kseq(next, _))`:
    // `kseq` is a constructor, so a pattern and a subject that both have that shape match only
    // if their next items match. The key rejects only a pair of distinct rigid items (a
    // constructor, a domain value, a collection), which the matcher refutes; a function
    // application or an `anywhere` head on either side is a wildcard.
    // Any other tail (`.K`, a variable, a function) keys nothing.
    let head = cell
        .and_then(k_cell_head)
        .map_or(CellIndex::Anything, |head| {
            cell_index(definition, head, side)
        });
    let next = match cell
        .and_then(k_cell_next)
        .map(|next| cell_index(definition, next, side))
    {
        None | Some(CellIndex::Anywhere(_)) => CellIndex::Anything,
        Some(next) => next,
    };
    RuleIndex(vec![head, next])
}

/// The keys of a subject. The top key is fixed exactly when `classify_value`, with the
/// simplifier's certificate and then the instance-normal scan as evidence, fixes the subject's
/// root, or the root is a macro or alias application, which the rewrite matcher compares by its
/// root. The cell keys differ from [`rule_index`] only at equation heads (`anywhere` productions
/// that are not declared functions): such a head is `Overloaded` when it is overloaded and its
/// root is fixed as a value, the case in which the matcher refutes it against a rigid head outside
/// its overload relation, and `Anything` otherwise. An application whose root is not fixed may
/// denote a value with any head an equation of its production produces, so it keys nothing.
pub fn subject_index(definition: &BackendDefinition, term: &Term) -> SubjectKey {
    let index = term_index(term);
    let top = match classify_value(term, &mut CertifiedOrScanned(definition)) {
        Head::Fixed(_) | Head::Residual => TopKey::Fixed(index),
        Head::Open(_) => TopKey::Open(index),
    };
    SubjectKey {
        top,
        cells: index_of(definition, term, KeySide::Subject),
    }
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

/// The item after the head of a `<k>` cell whose contents are `kseq(head, kseq(next, _))`.
fn k_cell_next(cell: &Term) -> Option<&Term> {
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
    let tail = match contents.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } if symbol.is(WellKnownSymbol::KSeq) => match arguments.as_slice() {
            [_head, tail] => tail,
            _ => return None,
        },
        _ => return None,
    };
    match tail.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } if symbol.is(WellKnownSymbol::KSeq) => match arguments.as_slice() {
            [next, _rest] => Some(next),
            _ => None,
        },
        _ => None,
    }
}

#[deny(clippy::wildcard_enum_match_arm)]
fn cell_index(definition: &BackendDefinition, term: &Term, side: KeySide) -> CellIndex {
    match term.kind() {
        TermKind::Injection { term, .. } => cell_index(definition, term, side),
        TermKind::And(left, right) => {
            cell_index(definition, left, side).meet(cell_index(definition, right, side))
        }
        TermKind::Variable(_) => CellIndex::Anything,
        TermKind::Application { symbol, .. }
            if symbol.attributes.head_role() == HeadRole::Uninterpreted =>
        {
            CellIndex::Anything
        }
        TermKind::Application { symbol, .. } => {
            let overloaded = definition.overloads().is_overloaded(&symbol.name);
            let head = match side {
                KeySide::Rule => classify_pattern(PatternReading::AsWritten, term),
                // A subject's equation head outside every overload relation keys nothing,
                // whatever its evidence: only a rule's key uses `Anywhere`. Its evidence is
                // therefore not asked for, which would run the instance-normal scan once per
                // rewrite step.
                KeySide::Subject
                    if !overloaded
                        && term.shape() == Shape::Application(HeadRole::EquationHead) =>
                {
                    return CellIndex::Anything;
                }
                KeySide::Subject => classify_value(term, &mut CertifiedOrScanned(definition)),
            };
            match head {
                // An overloaded head meets another overloaded head through a common overload,
                // and a declared function through evaluation. A fixed one is still refuted
                // against a rigid head outside every overload relation: overload resolution
                // needs both heads in one (`Matcher::resolve_overloads`), and the matcher then
                // fails the two distinct roots.
                Head::Fixed(_) if overloaded => CellIndex::Overloaded,
                Head::Fixed(fixed) => match fixed.root() {
                    FixedRoot::FreeConstructor => CellIndex::Constructor(symbol.name.clone()),
                    // Reached on the rule side only: a subject's non-overloaded equation head
                    // returned above.
                    FixedRoot::EquationHead(_) => CellIndex::Anywhere(symbol.name.clone()),
                    // Not the root of an application; `Anything` drops nothing.
                    FixedRoot::DomainValue | FixedRoot::Injection | FixedRoot::Collection(_) => {
                        CellIndex::Anything
                    }
                },
                // The rewrite matcher evaluates or defers a function application, and an
                // equation head without evidence may denote a value with another head; neither
                // is refuted by its root. A macro or alias application denotes a value the
                // definition does not describe, so it selects no rules by its head.
                Head::Open(_) | Head::Residual => CellIndex::Anything,
            }
        }
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

/// Rewrite candidates in priority order: the rules stored under the buckets `subject` offers
/// (`SubjectKey::buckets`: a subject whose root is fixed sees its own bucket and `Variable`, any
/// other subject every bucket), in bucket order within a priority, each filtered by the cell keys.
///
/// The function receives the subject's keys and no term, so whether the subject's root is fixed
/// is read only from the key [`subject_index`] built; handing it the term and a rule-side index
/// does not compile:
///
/// ```compile_fail
/// use k_rust_backend::{
///     definition::BackendDefinition,
///     rule::{applicable_rewrite_groups, rule_index},
///     term::Term,
/// };
/// fn select(definition: &BackendDefinition, term: &Term) -> usize {
///     applicable_rewrite_groups(definition, term, &rule_index(definition, term)).len()
/// }
/// ```
///
/// ```
/// use k_rust_backend::{
///     definition::BackendDefinition,
///     rule::{applicable_rewrite_groups, subject_index},
///     term::Term,
/// };
/// fn select(definition: &BackendDefinition, term: &Term) -> usize {
///     applicable_rewrite_groups(definition, &subject_index(definition, term)).len()
/// }
/// ```
///
/// A rule's index is not a subject's key either:
///
/// ```compile_fail
/// use k_rust_backend::{
///     definition::BackendDefinition,
///     rule::{applicable_rewrite_groups, rule_index},
///     term::Term,
/// };
/// fn select(definition: &BackendDefinition, term: &Term) -> usize {
///     applicable_rewrite_groups(definition, &rule_index(definition, term)).len()
/// }
/// ```
#[deny(clippy::wildcard_enum_match_arm)]
pub fn applicable_rewrite_groups(
    definition: &BackendDefinition,
    subject: &SubjectKey,
) -> BTreeMap<u8, Vec<Arc<RewriteRule>>> {
    let _span = measure::algorithm_span(Algorithm::BackendRuleSelect);
    let theory = definition.rewrite_theory();
    let mut groups = BTreeMap::new();
    for covered in subject.buckets(theory) {
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
    injection_role: UnlicensedInjectionSite,
) -> Result<(Term, Vec<Predicate>), DefinitionError> {
    internalize_rule_pattern_with_position(
        definition,
        pattern,
        sort_parameters,
        injection_role,
        None,
    )
}

fn internalize_rule_pattern_with_position(
    definition: &BackendDefinition,
    pattern: &kore::Pattern,
    sort_parameters: &[Name],
    injection_role: UnlicensedInjectionSite,
    defer_written_conditions_for: Option<(&RuleAttributes, &SentenceKey)>,
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
    let mut deferred_predicates = Vec::new();
    for component in components {
        if is_term_pattern(component) {
            terms.push(definition.internalize_term_collecting(
                component,
                sort_parameters,
                injection_role,
                &mut predicates,
                defer_written_conditions_for.map(|_| &mut deferred_predicates),
            )?);
        } else if defer_written_conditions_for.is_some() {
            deferred_predicates.push(component.clone());
        } else {
            predicates.extend(internalize_predicates(
                definition,
                component,
                sort_parameters,
                injection_role,
            )?);
        }
    }
    // A dead matched term is discarded before any written condition is internalized.
    for predicate in deferred_predicates {
        predicates.extend(
            internalize_predicates(definition, &predicate, sort_parameters, injection_role)
                .map_err(|error| {
                    let (attributes, sentence) =
                        defer_written_conditions_for.expect("written conditions were deferred");
                    written_injection_error(error, attributes, sentence)
                })?,
        );
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
    injection_role: UnlicensedInjectionSite,
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
                internalize_rule_pattern(definition, single, sort_parameters, injection_role)?;
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
                            injection_role,
                        )?;
                        Ok(RhsAlternative {
                            term,
                            ensures: Condition::new(ensures),
                        })
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
    injection_role: UnlicensedInjectionSite,
) -> Result<Vec<Predicate>, DefinitionError> {
    match pattern {
        kore::Pattern::Top { .. } => Ok(Vec::new()),
        kore::Pattern::Bottom { .. } => Ok(vec![Predicate::False]),
        kore::Pattern::And { arguments, .. } => arguments
            .iter()
            .map(|argument| {
                internalize_predicates(definition, argument, sort_parameters, injection_role)
            })
            .collect::<Result<Vec<_>, _>>()
            .map(|predicates| predicates.into_iter().flatten().collect()),
        kore::Pattern::Or { arguments, .. } => Ok(vec![Predicate::Or(
            arguments
                .iter()
                .map(|argument| {
                    internalize_predicate(definition, argument, sort_parameters, injection_role)
                })
                .collect::<Result<Vec<_>, _>>()?,
        )]),
        _ => Ok(vec![internalize_predicate(
            definition,
            pattern,
            sort_parameters,
            injection_role,
        )?]),
    }
}

pub(crate) fn internalize_predicate(
    definition: &BackendDefinition,
    pattern: &kore::Pattern,
    sort_parameters: &[Name],
    injection_role: UnlicensedInjectionSite,
) -> Result<Predicate, DefinitionError> {
    let term = |pattern: &kore::Pattern| {
        definition.internalize_term_with_validation(pattern, sort_parameters, injection_role)
    };
    let predicate = |pattern: &kore::Pattern| {
        internalize_predicate(definition, pattern, sort_parameters, injection_role)
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
        kore::Pattern::In { left, right, .. } => {
            let left = term(left)?;
            match term(right) {
                Err(DefinitionError::NotSubsort { .. })
                    if injection_role == UnlicensedInjectionSite::InAxiom =>
                {
                    Ok(Predicate::False)
                }
                right => Ok(Predicate::In(left, right?)),
            }
        }
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
    injection_role: UnlicensedInjectionSite,
) -> Result<Option<Predicate>, DefinitionError> {
    let recurse = |pattern: &kore::Pattern| {
        internalize_model_predicate(definition, pattern, sort_parameters, injection_role)
    };
    Ok(match pattern {
        kore::Pattern::Equals { .. }
        | kore::Pattern::Ceil { .. }
        | kore::Pattern::Floor { .. }
        | kore::Pattern::In { .. } => Some(internalize_predicate(
            definition,
            pattern,
            sort_parameters,
            injection_role,
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

/// Every choice of one alternative per argument, as argument lists, the first argument's choice
/// varying slowest.
///
/// The choices form a product: for `n` arguments and `C` choices the lists hold `C * n`
/// patterns, and each list is built once from its chosen alternatives, so building them costs
/// that much and no more. When every argument has a single alternative, as in a wide pattern
/// with no disjunction below it, the one list is built by moving the alternatives.
fn distribute_arguments(arguments: &[kore::Pattern], inside_term: bool) -> Vec<Vec<kore::Pattern>> {
    let mut alternatives = arguments
        .iter()
        .map(|argument| distribute_term_or_with_context(argument, inside_term))
        .collect::<Vec<_>>();
    if alternatives.iter().any(Vec::is_empty) {
        return Vec::new();
    }
    if alternatives.iter().all(|choices| choices.len() == 1) {
        return vec![
            alternatives
                .iter_mut()
                .map(|choices| choices.pop().expect("each argument has one alternative"))
                .collect(),
        ];
    }
    let mut combinations = Vec::new();
    // Invariant: `choice[i] < alternatives[i].len()` for every argument `i`, and the list of
    // every choice that precedes `choice`, in the order where the last argument varies fastest,
    // has been pushed once. Each pass pushes the list of `choice` and advances it to its
    // successor, so the loop returns after one pass per choice.
    let mut choice = vec![0_usize; alternatives.len()];
    loop {
        combinations.push(
            choice
                .iter()
                .zip(&alternatives)
                .map(|(&index, choices)| choices[index].clone())
                .collect(),
        );
        let mut position = choice.len();
        loop {
            let Some(previous) = position.checked_sub(1) else {
                return combinations;
            };
            position = previous;
            choice[position] += 1;
            if choice[position] < alternatives[position].len() {
                break;
            }
            choice[position] = 0;
        }
    }
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
        requires: Condition::new(requires),
        ensures: Condition::new(ensures),
        attributes,
        computed_attributes,
        existentials,
    }
}

fn computed_attributes<'a>(terms: impl IntoIterator<Item = &'a Term>) -> ComputedRuleAttributes {
    let mut result = ComputedRuleAttributes::default();
    for term in terms {
        term.visit_symbols(&mut |symbol| {
            result.contains_ac_symbols |= !symbol.attributes.algebraic_axioms().is_empty();
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
                    ensures: alternative.ensures.rename(rename),
                })
                .collect(),
        ),
        RuleRhs::Top => RuleRhs::Top,
        RuleRhs::Bottom => RuleRhs::Bottom,
        RuleRhs::Predicates(_) => unreachable!("term rules cannot have predicate RHSs"),
    }
}

pub(crate) fn rename_predicates(
    predicates: &[Predicate],
    rename: impl Copy + Fn(&Variable) -> Variable,
) -> Vec<Predicate> {
    predicates
        .iter()
        .map(|predicate| rename_predicate(predicate, rename))
        .collect()
}

#[deny(
    clippy::wildcard_enum_match_arm,
    clippy::match_wildcard_for_single_variants
)]
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
/// sites = ["rename_apart", "fresh_renaming"]
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
        requires: rule.requires.rename(rename),
        ensures: rule.ensures.rename(rename),
        attributes: rename_concreteness(&rule.attributes, &renaming),
        computed_attributes: ComputedRuleAttributes {
            contains_ac_symbols: computed.contains_ac_symbols,
            undefined_symbols: computed.undefined_symbols.clone(),
            variables: rename_set(&computed.variables),
            unbound_variables: rename_set(&computed.unbound_variables),
            unbound_result_variables: computed.unbound_result_variables.clone(),
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
    let PredicateRuleVariables {
        all: variables,
        unbound,
    } = &rule.variables;
    // The subject is walked for a clash without collecting its variables; its scope is
    // collected only when a renaming is needed.
    let term_clash = mentions_any(subject, variables);
    if !term_clash && unbound.is_empty() {
        return None;
    }
    let constraint_variables = free_variables_of(constraints);
    if !term_clash && unbound.is_disjoint(&constraint_variables) {
        return None;
    }
    let mut scope = BTreeSet::new();
    collect_all_variables(std::slice::from_ref(subject), &mut scope);
    scope.extend(constraint_variables);
    let renaming = fresh_renaming(variables, &scope);
    let rename = |variable: &Variable| {
        renaming
            .get(variable)
            .cloned()
            .unwrap_or_else(|| variable.clone())
    };
    let rename_set = |variables: &BTreeSet<Variable>| variables.iter().map(rename).collect();
    let renamed = PredicateRewriteRule {
        lhs: rename_predicate(&rule.lhs, rename),
        rhs: rename_predicates(&rule.rhs, rename),
        requires: rule.requires.rename(rename),
        attributes: rename_concreteness(&rule.attributes, &renaming),
        unbound_result_variables: rule.unbound_result_variables.clone(),
        variables: PredicateRuleVariables {
            all: rename_set(variables),
            unbound: rename_set(unbound),
        },
    };
    Some((renamed, renaming))
}

/// Whether `predicate` mentions one of `variables`, free or bound: whether the set
/// `collect_all_variables` builds for it meets `variables`.
fn mentions_any(predicate: &Predicate, variables: &BTreeSet<Variable>) -> bool {
    match predicate {
        Predicate::True | Predicate::False => false,
        Predicate::Term(term) | Predicate::Ceil(term) | Predicate::Floor(term) => {
            !term.attributes().variables.is_disjoint(variables)
        }
        Predicate::Equals(left, right) | Predicate::In(left, right) => {
            !left.attributes().variables.is_disjoint(variables)
                || !right.attributes().variables.is_disjoint(variables)
        }
        Predicate::Not(inner) => mentions_any(inner, variables),
        Predicate::And(inner) | Predicate::Or(inner) => inner
            .iter()
            .any(|predicate| mentions_any(predicate, variables)),
        Predicate::Implies(left, right) | Predicate::Iff(left, right) => {
            mentions_any(left, variables) || mentions_any(right, variables)
        }
        Predicate::Exists(variable, inner) | Predicate::Forall(variable, inner) => {
            variables.contains(variable) || mentions_any(inner, variables)
        }
    }
}

/// Whether `variable` occurs free in `predicate`, without collecting its free variables.
pub(crate) fn mentions_free(predicate: &Predicate, variable: &Variable) -> bool {
    match predicate {
        Predicate::True | Predicate::False => false,
        Predicate::Term(term) | Predicate::Ceil(term) | Predicate::Floor(term) => {
            term.attributes().variables.contains(variable)
        }
        Predicate::Equals(left, right) | Predicate::In(left, right) => {
            left.attributes().variables.contains(variable)
                || right.attributes().variables.contains(variable)
        }
        Predicate::Not(inner) => mentions_free(inner, variable),
        Predicate::And(inner) | Predicate::Or(inner) => inner
            .iter()
            .any(|predicate| mentions_free(predicate, variable)),
        Predicate::Implies(left, right) | Predicate::Iff(left, right) => {
            mentions_free(left, variable) || mentions_free(right, variable)
        }
        Predicate::Exists(bound, inner) | Predicate::Forall(bound, inner) => {
            bound != variable && mentions_free(inner, variable)
        }
    }
}

fn free_variables_of<'a>(
    predicates: impl IntoIterator<Item = &'a Predicate>,
) -> BTreeSet<Variable> {
    predicates
        .into_iter()
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
                free.extend(free_variables_of(alternative.ensures.iter()));
                collect_all_variables(alternative.ensures.iter(), &mut all);
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
pub(crate) fn collect_all_variables<'a>(
    predicates: impl IntoIterator<Item = &'a Predicate>,
    variables: &mut BTreeSet<Variable>,
) {
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
/// marker and by its full sort, as `check_concreteness` reads it.
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
        .into_owned()
    };
    let mut renamed = BTreeMap::new();
    for (variable, fresh) in renaming {
        let key = (Name::from(unmarked(variable)), variable.sort.clone());
        if let Some(kind) = constrained.remove(&key) {
            renamed.insert((Name::from(unmarked(fresh)), fresh.sort.clone()), kind);
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
            OWISE_RULE_PRIORITY
        } else {
            priority
                .or(simplification_priority)
                .map(|value| rule_priority(&value).ok_or(AxiomError::InvalidPriority(value)))
                .transpose()?
                .unwrap_or(DEFAULT_RULE_PRIORITY)
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
        variables.push(variable.as_ref().clone());
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
            let concrete = parse_constrained_variables(concrete, ConstraintKind::Concrete);
            let symbolic = parse_constrained_variables(symbolic, ConstraintKind::Symbolic);
            let overlap = concrete
                .keys()
                .collect::<BTreeSet<_>>()
                .intersection(&symbolic.keys().collect())
                .next()
                .cloned();
            if let Some((name, sort)) = overlap {
                return Err(AxiomError::ConcretenessOverlap(format!(
                    "{name}:{}",
                    crate::externalize::sort(sort)
                )));
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
) -> Result<Option<Vec<(Name, Sort)>>, AxiomError> {
    let Some(arguments) = attributes.arguments(attribute) else {
        return Ok(None);
    };
    arguments
        .iter()
        .map(|argument| match argument {
            kore::Pattern::Variable(variable) => Ok((
                Name::from(variable.name.as_str()),
                attribute_sort(&variable.sort)
                    .ok_or_else(|| AxiomError::MalformedAttribute(attribute.as_str().into()))?,
            )),
            // Older generated definitions encoded the same pair as a string.
            kore::Pattern::String(value) => {
                let text = value
                    .as_utf8()
                    .map_err(|_| AxiomError::MalformedAttribute(attribute.as_str().into()))?;
                let invalid = || AxiomError::InvalidConcreteness(text.to_owned());
                let (name, sort) = text.split_once(':').ok_or_else(invalid)?;
                let sort = if sort.contains('{') {
                    let kore::Pattern::Top { ref sort } =
                        k_rust_kore::kore::parser::parse_pattern(&format!("\\top{{{sort}}}()"))
                            .map_err(|_| invalid())?
                    else {
                        return Err(invalid());
                    };
                    attribute_sort(sort).ok_or_else(invalid)?
                } else {
                    Sort::simple(sort)
                };
                Ok((Name::from(name), sort))
            }
            _ => Err(AxiomError::MalformedAttribute(attribute.as_str().into())),
        })
        .collect::<Result<Vec<_>, _>>()
        .map(Some)
}

fn attribute_sort(sort: &kore::Sort) -> Option<Sort> {
    match sort {
        kore::Sort::Application { name, arguments } => Some(Sort::application(
            name.as_str(),
            arguments
                .iter()
                .map(attribute_sort)
                .collect::<Option<_>>()?,
        )),
        kore::Sort::Variable(_) => None,
    }
}

fn parse_constrained_variables(
    variables: Vec<(Name, Sort)>,
    kind: ConstraintKind,
) -> BTreeMap<(Name, Sort), ConstraintKind> {
    variables
        .into_iter()
        .map(|variable| (variable, kind))
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

    #[test]
    fn overload_classification_precedes_algebraic_tags() {
        for overload in ["overload", "symbol-overload"] {
            let source = format!(
                r"axiom{{R}} \equals{{SortS{{}}, R}}(g{{}}(X:SortS{{}}), h{{}}(X:SortS{{}})) [{overload}{{}}(), idem{{}}()]"
            );
            let kore::Sentence::Axiom {
                pattern,
                attributes,
                ..
            } = parse_sentence(&source).expect("overload axiom should parse")
            else {
                panic!("expected axiom");
            };
            assert_eq!(algebraic_axiom_roots(&pattern, &attributes), None);
            assert!(matches!(
                classify(&source),
                Ok(Some(ClassifiedAxiom::Function { .. }))
            ));
        }
    }

    #[test]
    fn algebraic_classification_uses_the_recorded_roots_and_tags() {
        for (sides, expected_roots) in [
            (
                "g{}(X:SortS{}), h{}(X:SortS{})",
                vec![Name::from("g"), Name::from("h")],
            ),
            ("g{}(X:SortS{}), X:SortS{}", vec![Name::from("g")]),
            ("X:SortS{}, h{}(X:SortS{})", vec![Name::from("h")]),
        ] {
            for (tag, expected_fact) in [
                ("assoc", AlgebraicAxioms::assoc()),
                ("comm", AlgebraicAxioms::comm()),
                ("idem", AlgebraicAxioms::idem()),
                ("unit", AlgebraicAxioms::unit()),
            ] {
                let source = format!(r"axiom{{R}} \equals{{SortS{{}}, R}}({sides}) [{tag}{{}}()]");
                let sentence = parse_sentence(&source).expect("algebraic axiom should parse");
                let kore::Sentence::Axiom {
                    pattern,
                    attributes,
                    ..
                } = sentence
                else {
                    panic!("expected axiom");
                };
                assert_eq!(
                    algebraic_axiom_roots(&pattern, &attributes),
                    Some(Ok((expected_fact, expected_roots.clone())))
                );
                assert!(
                    classify(&source)
                        .expect("tagged equation should classify")
                        .is_none()
                );
            }
        }
        assert!(matches!(
            classify(r"axiom{R} \equals{SortS{}, R}(X:SortS{}, Y:SortS{}) [comm{}()]"),
            Err(AxiomError::MalformedEquation)
        ));
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
        internalize_axiom(
            &function_binder_definition(),
            &classified,
            &("MAIN".into(), 0),
        )
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
    fn nested_written_conditions_internalize_like_top_level_requires() {
        let definition = function_binder_definition();
        for condition in [
            r"\top{SortS{}}()",
            r"\and{SortS{}}(\top{SortS{}}(), \equals{SortS{},SortS{}}(a{}(), b{}()))",
        ] {
            let internalize = |lhs: &str| {
                let axiom = classify(&format!(
                    r"axiom{{}} \rewrites{{SortS{{}}}}({lhs}, result{{}}()) []",
                ))
                .unwrap()
                .unwrap();
                internalize_axiom(&definition, &axiom, &("MAIN".into(), 0)).unwrap()
            };
            let nested = internalize(&format!(
                r"\and{{SortS{{}}}}(wrap{{}}(\and{{SortS{{}}}}(a{{}}(), {condition})), \top{{SortS{{}}}}())",
            ));
            let top_level = internalize(&format!(
                r"\and{{SortS{{}}}}(wrap{{}}(a{{}}()), {condition})",
            ));
            assert_eq!(nested, top_level);
        }
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
            .simplification_theory()
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
                (Name::from("X"), Sort::simple("S")),
                ConstraintKind::Concrete,
            )]))
        );
    }

    #[test]
    fn classifies_concreteness_constraints_with_full_sorts() {
        let classified = classify_parametric_concreteness("concrete{}(X:SortM{SortA{}})")
            .expect("a closed parametric constraint should classify");
        let ClassifiedAxiom::Simplification { attributes, .. } = classified else {
            panic!("expected simplification equation");
        };
        assert_eq!(
            attributes.concreteness,
            Concreteness::Some(BTreeMap::from([(
                (
                    Name::from("X"),
                    Sort::application("SortM", vec![Sort::simple("SortA")]),
                ),
                ConstraintKind::Concrete,
            )]))
        );
    }

    fn classify_parametric_concreteness(attribute: &str) -> Result<ClassifiedAxiom, AxiomError> {
        let source = format!(
            r#"[]
            module MAIN
                sort SortM{{W}} []
                sort SortA{{}} []
                sort SortS{{}} []
                symbol f{{}}(SortM{{SortA{{}}}}) : SortS{{}} [function{{}}()]
                symbol a{{}}() : SortS{{}} [constructor{{}}()]
                axiom{{R, S}} \implies{{R}}(
                    \top{{R}}(),
                    \equals{{SortS{{}}, R}}(
                        f{{}}(X:SortM{{SortA{{}}}}),
                        \and{{SortS{{}}}}(a{{}}(), \top{{SortS{{}}}}())
                    )
                ) [simplification{{}}(), {attribute}]
            endmodule []"#
        );
        let definition = parse_definition(&source).expect("definition should parse");
        let kore::Sentence::Axiom {
            parameters,
            pattern,
            attributes,
        } = definition.modules[0].sentences.last().unwrap()
        else {
            panic!("expected axiom");
        };
        classify_axiom(
            "MAIN".into(),
            parameters.iter().cloned().map(Into::into).collect(),
            pattern,
            attributes,
        )
        .map(|classified| classified.expect("axiom should be executable"))
    }

    #[test]
    fn legacy_concreteness_strings_keep_full_sorts() {
        for (attribute, sort) in [
            (
                r#"concrete{}("X:SortM{SortA{}}")"#,
                Sort::application("SortM", vec![Sort::simple("SortA")]),
            ),
            (r#"concrete{}("X:SortS")"#, Sort::simple("SortS")),
        ] {
            let ClassifiedAxiom::Simplification { attributes, .. } =
                classify_parametric_concreteness(attribute).expect("legacy entry should classify")
            else {
                panic!("expected simplification equation");
            };
            assert_eq!(
                attributes.concreteness,
                Concreteness::Some(BTreeMap::from([(
                    (Name::from("X"), sort),
                    ConstraintKind::Concrete,
                )]))
            );
        }
    }

    #[test]
    fn concreteness_constraints_reject_sort_variables() {
        assert_eq!(
            classify_parametric_concreteness("symbolic{}(X:SortM{S})").unwrap_err(),
            AxiomError::MalformedAttribute("symbolic".into())
        );
    }

    #[test]
    fn malformed_legacy_concreteness_strings_are_rejected() {
        for text in ["X", "X:SortM{SortA{}", "X:SortM{S}"] {
            assert_eq!(
                classify_parametric_concreteness(&format!(r#"concrete{{}}("{text}")"#))
                    .unwrap_err(),
                AxiomError::InvalidConcreteness(text.into())
            );
        }
    }

    #[test]
    fn concreteness_overlap_reports_the_full_sort() {
        assert_eq!(
            classify_parametric_concreteness(
                "concrete{}(X:SortM{SortA{}}), symbolic{}(X:SortM{SortA{}})"
            )
            .unwrap_err(),
            AxiomError::ConcretenessOverlap("X:SortM{SortA{}}".into())
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

    /// An `owise` rule ranks after every explicit priority, so no explicit priority names its
    /// rank: a rule ranked beside the `owise` rules would be their alternative.
    #[test]
    fn owise_ranks_after_every_explicit_priority() {
        let rank = |attributes: &str| {
            let source = format!(
                r#"axiom{{}} \rewrites{{S{{}}}}(
                    \and{{S{{}}}}(lhs{{}}(), \top{{S{{}}}}()), rhs{{}}()
                ) [{attributes}]"#
            );
            match classify(&source) {
                Ok(Some(ClassifiedAxiom::Rewrite { attributes, .. })) => Ok(attributes.priority),
                Ok(other) => panic!("expected a rewrite rule: {other:?}"),
                Err(error) => Err(error),
            }
        };
        assert_eq!(rank("owise{}()"), Ok(OWISE_RULE_PRIORITY));
        assert_eq!(rank(r#"priority{}("254")"#), Ok(254));
        assert_eq!(
            rank(r#"priority{}("255")"#),
            Err(AxiomError::InvalidPriority("255".into()))
        );
    }

    fn collapse(sources: &[(&str, usize)]) -> Vec<ClassifiedAxiom> {
        collapse_equal_axioms(sources.iter().map(|&(source, sentence)| {
            let axiom = classify(source)
                .expect("axiom should classify")
                .expect("axiom should be a rule");
            (axiom, (Name::from("MAIN"), sentence))
        }))
        .into_iter()
        .map(|(axiom, _)| axiom)
        .collect()
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
        let [InternalizedRule::Term(_, rule)] = &internalize_axiom(
            &function_binder_definition(),
            &classified,
            &("MAIN".into(), 0),
        )
        .unwrap()[..] else {
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
                (
                    Name::from(&fresh.name["Eq#".len()..]),
                    Sort::simple("SortS")
                ),
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
            &internalize_axiom(&definition, &classified, &("MAIN".into(), 0)).unwrap()[..]
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
        assert!(
            !renamed
                .requires
                .iter()
                .next()
                .expect("one requires")
                .free_variables()
                .contains(&y)
        );
    }

    #[test]
    fn predicate_rule_cached_variables_preserve_renaming() {
        let sort = crate::term::Sort::simple("SortS");
        let x = Variable::new("Eq#X", sort.clone());
        let y = Variable::new("Eq#Y", sort.clone());
        let z = Variable::new("Eq#Z", sort.clone());
        let lhs = Predicate::Equals(Term::variable(x.clone()), Term::variable(x.clone()));
        let rhs = vec![Predicate::Exists(
            z.clone(),
            Box::new(Predicate::Equals(
                Term::variable(y.clone()),
                Term::variable(z.clone()),
            )),
        )];
        let rule = PredicateRewriteRule::new(
            lhs,
            rhs,
            Condition::default(),
            RuleAttributes {
                priority: 50,
                label: None,
                unique_id: "predicate-apart".into(),
                simplification: true,
                preserves_definedness: false,
                concreteness: Concreteness::Unconstrained,
                smt_lemma: false,
                executable: true,
                origins: vec![],
            },
        );
        assert_eq!(
            rule.variables.all,
            BTreeSet::from([x.clone(), y.clone(), z.clone()])
        );
        assert_eq!(rule.variables.unbound, BTreeSet::from([y.clone()]));
        assert!(rename_predicate_rule_apart(&rule, &Predicate::True, &[]).is_none());

        let subject = Predicate::Forall(z.clone(), Box::new(Predicate::True));
        let (renamed, renaming) = rename_predicate_rule_apart(&rule, &subject, &[])
            .expect("a subject binder is in scope");
        assert_eq!(renaming.keys().collect::<Vec<_>>(), [&z]);
        let recomputed = PredicateRewriteRule::new(
            renamed.lhs.clone(),
            renamed.rhs.clone(),
            renamed.requires.clone(),
            renamed.attributes.clone(),
        );
        assert_eq!(renamed.variables, recomputed.variables);
        assert!(rename_predicate_rule_apart(&renamed, &subject, &[]).is_none());

        let path = [Predicate::Equals(
            Term::variable(y.clone()),
            Term::variable(y.clone()),
        )];
        let (_, renaming) = rename_predicate_rule_apart(&rule, &Predicate::True, &path)
            .expect("the path mentions an unbound rule variable");
        assert_eq!(renaming.keys().collect::<Vec<_>>(), [&y]);
        let subject = Predicate::Equals(Term::variable(x.clone()), Term::variable(x.clone()));
        let (_, renaming) = rename_predicate_rule_apart(&rule, &subject, &[])
            .expect("the subject mentions the left-hand side variable");
        assert_eq!(renaming.keys().collect::<Vec<_>>(), [&x]);
    }

    /// Rule selection by `SubjectKey`. `wrap` is an equation head whose equation `wrap(s(z)) =
    /// wrap(z)` rewrites `wrap(s(z))` but reaches no instance of `wrap(s(s(z)))`; `app` is an
    /// equation head overloading the constructor `appv`, whose overload equation rewrites
    /// `app(inj(v), inj(v))`; `f` is a function. Rewrite rules are stored under the buckets
    /// `top`, `other`, `wrap`, `w0` and `Variable`.
    fn selection_definition() -> BackendDefinition {
        let rewrite = |sort: &str, label: &str, lhs: &str, rhs: &str| {
            format!(
                r#"axiom{{}} \rewrites{{{sort}{{}}}}(
                    \and{{{sort}{{}}}}({lhs}, \top{{{sort}{{}}}}()),
                    {rhs}
                  ) [label{{}}("{label}"), priority{{}}("50")]
                "#
            )
        };
        let top =
            |head: &str| format!("top{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}({head}, R:SortK{{}})))");
        let source = r#"[]
            module MAIN
              sort SortK{} []
              sort SortKItem{} []
              sort SortKCell{} []
              sort SortGeneratedTopCell{} []
              sort SortExp{} []
              sort SortVal{} []
              sort SortNat{} []
              sort SortW{} []
              symbol inj{From, To}(From) : To [sortInjection{}()]
              symbol kseq{}(SortKItem{}, SortK{}) : SortK{} [constructor{}(), total{}()]
              symbol dotk{}() : SortK{} [constructor{}(), total{}()]
              symbol Lbl'-LT-'k'-GT-'{}(SortK{}) : SortKCell{} [constructor{}(), total{}()]
              symbol top{}(SortKCell{}) : SortGeneratedTopCell{} [constructor{}(), total{}()]
              symbol other{}(SortKCell{}) : SortGeneratedTopCell{} [constructor{}(), total{}()]
              symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
              symbol s{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
              symbol f{}(SortNat{}) : SortGeneratedTopCell{} [function{}(), total{}()]
              symbol wrap{}(SortNat{}) : SortW{} [anywhere{}(), functional{}(), injective{}()]
              symbol w0{}() : SortW{} [constructor{}(), functional{}(), injective{}()]
              symbol v{}() : SortVal{} [constructor{}(), total{}()]
              symbol appv{}(SortVal{}, SortVal{}) : SortVal{} [constructor{}(), total{}()]
              symbol app{}(SortExp{}, SortExp{}) : SortExp{}
                [anywhere{}(), functional{}(), injective{}(), no-evaluators{}()]
              symbol plus{}(SortExp{}, SortExp{}) : SortExp{} [constructor{}(), total{}()]
              axiom{R} \exists{R}(
                  Value:SortExp{},
                  \equals{SortExp{}, R}(Value:SortExp{}, inj{SortVal{}, SortExp{}}(From:SortVal{}))
              ) [subsort{SortVal{}, SortExp{}}()]
              axiom{R} \exists{R}(
                  Value:SortKItem{},
                  \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortExp{}, SortKItem{}}(From:SortExp{}))
              ) [subsort{SortExp{}, SortKItem{}}()]
              axiom{R} \exists{R}(
                  Value:SortKItem{},
                  \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortVal{}, SortKItem{}}(From:SortVal{}))
              ) [subsort{SortVal{}, SortKItem{}}()]
              axiom{} \equals{SortExp{}, SortExp{}}(
                  app{}(inj{SortVal{}, SortExp{}}(V1:SortVal{}), inj{SortVal{}, SortExp{}}(V2:SortVal{})),
                  inj{SortVal{}, SortExp{}}(appv{}(V1:SortVal{}, V2:SortVal{}))
              ) [symbol-overload{}(app{}(), appv{}())]
              axiom{R} \implies{R}(
                  \and{R}(
                      \top{R}(),
                      \and{R}(\in{SortNat{}, R}(X0:SortNat{}, s{}(z{}())), \top{R}())
                  ),
                  \equals{SortW{}, R}(
                      wrap{}(X0:SortNat{}),
                      \and{SortW{}}(wrap{}(z{}()), \top{SortW{}}())
                  )
              ) [label{}("collapse"), anywhere{}()]
            "#
        .to_owned()
            + &rewrite(
                "SortGeneratedTopCell",
                "app",
                &top("inj{SortExp{}, SortKItem{}}(app{}(X:SortExp{}, Y:SortExp{}))"),
                "top{}(Lbl'-LT-'k'-GT-'{}(R:SortK{}))",
            )
            + &rewrite(
                "SortGeneratedTopCell",
                "plus",
                &top("inj{SortExp{}, SortKItem{}}(plus{}(X:SortExp{}, Y:SortExp{}))"),
                "top{}(Lbl'-LT-'k'-GT-'{}(R:SortK{}))",
            )
            + &rewrite(
                "SortGeneratedTopCell",
                "other",
                "other{}(Lbl'-LT-'k'-GT-'{}(R:SortK{}))",
                "top{}(Lbl'-LT-'k'-GT-'{}(R:SortK{}))",
            )
            + &rewrite(
                "SortGeneratedTopCell",
                "any-top",
                "T:SortGeneratedTopCell{}",
                "T:SortGeneratedTopCell{}",
            )
            + &rewrite("SortW", "wrap-z", "wrap{}(z{}())", "w0{}()")
            + &rewrite("SortW", "w0", "w0{}()", "wrap{}(z{}())")
            + "endmodule []";
        BackendDefinition::internalize(
            &parse_definition(&source).expect("definition should parse"),
            "MAIN",
        )
        .expect("definition should internalize")
    }

    fn selection_term(definition: &BackendDefinition, source: &str) -> Term {
        definition
            .internalize_term(
                &k_rust_kore::kore::parser::parse_pattern(source).expect("term should parse"),
                &[],
            )
            .expect("term should internalize")
    }

    fn offered_buckets<'r>(key: &'r SubjectKey, theory: &'r RewriteTheory) -> Vec<&'r TermIndex> {
        key.buckets(theory).collect()
    }

    fn candidate_labels(definition: &BackendDefinition, key: &SubjectKey) -> Vec<String> {
        applicable_rewrite_groups(definition, key)
            .into_values()
            .flatten()
            .map(|rule| rule.attributes.unique_id.clone())
            .collect()
    }

    /// Acceptance (c83f65a7): a variable and a function application may denote a value with any
    /// root, so their top keys are open and they are offered every bucket of the theory, their
    /// own first and `Variable` next.
    #[test]
    fn a_variable_or_function_subject_is_open_and_offered_every_bucket() {
        let definition = selection_definition();
        let theory = definition.rewrite_theory();
        let every: BTreeSet<&TermIndex> = theory.keys().collect();
        assert!(
            every.len() >= 5,
            "the theory has several buckets: {every:?}"
        );
        let all_rules: usize = theory
            .values()
            .flat_map(BTreeMap::values)
            .map(Vec::len)
            .sum();

        let variable = selection_term(&definition, "X:SortK{}");
        let key = subject_index(&definition, &variable);
        assert_eq!(key.top, TopKey::Open(TermIndex::Variable));
        let buckets = offered_buckets(&key, theory);
        assert_eq!(buckets[0], &TermIndex::Variable);
        assert_eq!(buckets.len(), every.len());
        assert_eq!(buckets.iter().copied().collect::<BTreeSet<_>>(), every);
        assert_eq!(candidate_labels(&definition, &key).len(), all_rules);

        let function = selection_term(&definition, "f{}(z{}())");
        let key = subject_index(&definition, &function);
        let own = TermIndex::Symbol(Name::from("f"));
        assert!(!every.contains(&own), "no rule is stored under `f`");
        assert_eq!(key.top, TopKey::Open(own.clone()));
        let buckets = offered_buckets(&key, theory);
        assert_eq!(buckets[..2], [&own, &TermIndex::Variable]);
        assert_eq!(buckets.len(), every.len() + 1);
        assert!(every.iter().all(|bucket| buckets.contains(bucket)));
        assert_eq!(candidate_labels(&definition, &key).len(), all_rules);

        // Control: a free-constructor root is fixed and offered its own bucket and `Variable`.
        let fixed = selection_term(
            &definition,
            "other{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortVal{}, SortKItem{}}(v{}()), dotk{}())))",
        );
        let key = subject_index(&definition, &fixed);
        let own = TermIndex::Symbol(Name::from("other"));
        assert_eq!(key.top, TopKey::Fixed(own.clone()));
        assert_eq!(offered_buckets(&key, theory), [&own, &TermIndex::Variable]);
        assert_eq!(candidate_labels(&definition, &key), ["other", "any-top"]);
    }

    /// Acceptance (d0e0762e): an overloaded equation-head `<k>` head that is neither certified by
    /// the simplifier nor instance-normal may denote a value with another head, so its cell key
    /// is `Anything`; the same head with no equation reaching any instance keys `Overloaded`.
    #[test]
    fn an_uncertified_redex_of_an_overloaded_equation_head_keys_anything() {
        let definition = selection_definition();
        let in_k = |head: &str| {
            selection_term(
                &definition,
                &format!(
                    "top{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortExp{{}}, SortKItem{{}}}}({head}), dotk{{}}())))"
                ),
            )
        };
        let redex = "app{}(inj{SortVal{}, SortExp{}}(v{}()), inj{SortVal{}, SortExp{}}(v{}()))";
        let app = selection_term(&definition, redex);
        assert!(definition.overloads().is_overloaded(&Name::from("app")));
        assert!(!app.attributes().evaluated, "uncertified");
        assert!(
            definition.instance_normal(&app).is_none(),
            "not instance-normal"
        );
        assert_eq!(
            subject_index(&definition, &in_k(redex)).cells(),
            &[CellIndex::Anything, CellIndex::Anything]
        );
        assert_eq!(
            candidate_labels(&definition, &subject_index(&definition, &in_k(redex))),
            ["app", "plus", "any-top"]
        );

        let normal = "app{}(plus{}(inj{SortVal{}, SortExp{}}(v{}()), inj{SortVal{}, SortExp{}}(v{}())), inj{SortVal{}, SortExp{}}(v{}()))";
        assert!(
            definition
                .instance_normal(&selection_term(&definition, normal))
                .is_some()
        );
        assert_eq!(
            subject_index(&definition, &in_k(normal)).cells(),
            &[CellIndex::Overloaded, CellIndex::Anything]
        );
        assert_eq!(
            candidate_labels(&definition, &subject_index(&definition, &in_k(normal))),
            ["app", "any-top"]
        );
    }

    /// Acceptance (finding 0.7): `wrap(s(z))`, which an equation rewrites, and `wrap(s(s(z)))`,
    /// which no equation reaches, have one term index and equal cell keys, but only the second
    /// root is fixed. Their keys differ, so the rewrite loop, which reselects rules only when a
    /// remainder's key changes, does not hand one the groups selected for the other.
    #[test]
    fn subject_keys_differ_in_top_rigidity_alone() {
        let definition = selection_definition();
        let open = selection_term(&definition, "wrap{}(s{}(z{}()))");
        let fixed = selection_term(&definition, "wrap{}(s{}(s{}(z{}())))");
        let open_key = subject_index(&definition, &open);
        let fixed_key = subject_index(&definition, &fixed);
        let wrap = TermIndex::Symbol(Name::from("wrap"));
        assert_eq!(term_index(&open), term_index(&fixed));
        assert_eq!(open_key.cells(), fixed_key.cells());
        assert_eq!(open_key.top, TopKey::Open(wrap.clone()));
        assert_eq!(fixed_key.top, TopKey::Fixed(wrap));
        assert_ne!(open_key, fixed_key);
        // The two keys select different candidates: only the open root may denote `w0()`.
        assert_eq!(
            candidate_labels(&definition, &fixed_key),
            ["wrap-z", "any-top"]
        );
        assert!(candidate_labels(&definition, &open_key).contains(&"w0".to_owned()));
    }

    /// A wide pattern is distributed in time proportional to the patterns it distributes into:
    /// a conjunction of a disjunction of two constants and 20,000 further constants becomes two
    /// conjunctions of 20,001 constants each. Copying each growing prefix of the argument list
    /// once per argument took 400 million copies of a constant here, which is about a minute in
    /// a debug build; building each list once takes 40,000 copies. The patterns are flat and
    /// take a few MB.
    #[test]
    fn wide_disjunctions_are_distributed_in_linear_time() {
        let sort = || kore::Sort::Application {
            name: "SortS".into(),
            arguments: Vec::new(),
        };
        let constant = |name: &str| kore::Pattern::Application {
            symbol: kore::Symbol {
                name: name.into(),
                sort_parameters: Vec::new(),
            },
            arguments: Vec::new(),
        };
        let width = 20_000;
        let mut arguments = vec![kore::Pattern::Or {
            sort: sort(),
            arguments: vec![constant("b"), constant("c")],
        }];
        arguments.extend(std::iter::repeat_with(|| constant("a")).take(width));
        let pattern = kore::Pattern::And {
            sort: sort(),
            arguments,
        };

        let disjuncts = term_disjuncts(&pattern);

        let heads = disjuncts
            .iter()
            .map(|disjunct| {
                let kore::Pattern::And { arguments, .. } = disjunct else {
                    panic!("each disjunct is a conjunction");
                };
                assert_eq!(arguments.len(), width + 1);
                assert!(
                    arguments[1..]
                        .iter()
                        .all(|argument| *argument == constant("a"))
                );
                arguments[0].clone()
            })
            .collect::<Vec<_>>();
        assert_eq!(heads, [constant("b"), constant("c")]);
    }

    /// Distribution chooses one alternative per argument, the first argument's choice varying
    /// slowest, and an argument with no alternative leaves no choice.
    #[test]
    fn distribution_enumerates_every_choice_in_order() {
        let pattern = k_rust_kore::kore::parser::parse_pattern(
            r"p{}(\or{SortS{}}(a{}(), b{}()), c{}(), \or{SortS{}}(d{}(), e{}(), f{}()))",
        )
        .unwrap();
        let printed = distribute_term_or(&pattern)
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        assert_eq!(
            printed,
            [
                "p{}(a{}(), c{}(), d{}())",
                "p{}(a{}(), c{}(), e{}())",
                "p{}(a{}(), c{}(), f{}())",
                "p{}(b{}(), c{}(), d{}())",
                "p{}(b{}(), c{}(), e{}())",
                "p{}(b{}(), c{}(), f{}())",
            ]
        );
        let empty =
            k_rust_kore::kore::parser::parse_pattern(r"p{}(a{}(), \or{SortS{}}())").unwrap();
        assert!(distribute_term_or(&empty).is_empty());
    }
}

#[cfg(test)]
mod unbound_equation_tests {
    use k_rust_kore::kore::parser::parse_definition;

    use super::*;

    fn load(axiom: &str) -> BackendDefinition {
        let source = format!(
            r#"[]
            module MAIN
                sort SortS{{}} []
                symbol a{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol c{{}}(SortS{{}}) : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol f{{}}(SortS{{}}) : SortS{{}} [function{{}}()]
                symbol p{{}}(SortS{{}}) : SortS{{}} [function{{}}()]
                {axiom}
            endmodule []"#
        );
        BackendDefinition::internalize(&parse_definition(&source).unwrap(), "MAIN")
            .expect("an equation with a variable its left-hand side does not bind is loaded")
    }

    /// The unbound result variables recorded on the one equation of `axiom`.
    fn unbound_result(axiom: &str) -> Vec<String> {
        let definition = load(axiom);
        let term_rules = [
            definition.function_theory(),
            definition.simplification_theory(),
            definition.ceil_theory(),
        ]
        .into_iter()
        .flat_map(|theory| theory.values())
        .flat_map(|groups| groups.values())
        .flatten()
        .map(|rule| rule.computed_attributes.unbound_result_variables.clone());
        let predicate_rules = definition
            .predicate_simplification_theory()
            .values()
            .flatten()
            .map(|rule| rule.unbound_result_variables.clone());
        let recorded = term_rules.chain(predicate_rules).collect::<Vec<_>>();
        let [recorded] = &recorded[..] else {
            panic!("expected one equation: {recorded:?}");
        };
        recorded.clone()
    }

    /// An equation states `l = r` for every value of each of its variables that satisfies its
    /// `requires`. A variable of its right-hand side or `ensures` that `l` does not bind is
    /// recorded, whatever kind of equation it is, and the definition is loaded: the equation can
    /// be consistent and meaningful (`f(X) = Y requires Y = c(X)` is `f(X) = c(X)`), and only
    /// its instances are not used.
    #[test]
    fn an_equation_with_a_variable_its_left_hand_side_does_not_bind_is_loaded_and_recorded() {
        // A function equation, its right-hand side.
        assert_eq!(
            unbound_result(
                r#"axiom{R} \implies{R}(
                    \and{R}(\top{R}(), \and{R}(\in{SortS{}, R}(K0:SortS{}, X:SortS{}), \top{R}())),
                    \equals{SortS{}, R}(
                        f{}(K0:SortS{}), \and{SortS{}}(c{}(Y:SortS{}), \top{SortS{}}())))
                    [label{}("eq")]"#
            ),
            ["Y"]
        );
        // A function equation whose right-hand-side variable its `requires` determines.
        assert_eq!(
            unbound_result(
                r#"axiom{R} \implies{R}(
                    \and{R}(
                        \equals{SortS{}, R}(Y:SortS{}, c{}(X:SortS{})),
                        \and{R}(\in{SortS{}, R}(K0:SortS{}, X:SortS{}), \top{R}())),
                    \equals{SortS{}, R}(
                        f{}(K0:SortS{}), \and{SortS{}}(Y:SortS{}, \top{SortS{}}())))
                    [label{}("eq")]"#
            ),
            ["Y"]
        );
        // A simplification, its `ensures`.
        assert_eq!(
            unbound_result(
                r#"axiom{R} \implies{R}(\top{R}(), \equals{SortS{}, R}(
                    f{}(X:SortS{}), \and{SortS{}}(X:SortS{},
                        \equals{SortS{}, SortS{}}(X:SortS{}, Y:SortS{}))))
                    [label{}("eq"), simplification{}()]"#
            ),
            ["Y"]
        );
        // A predicate simplification.
        assert_eq!(
            unbound_result(
                r#"axiom{R, Q} \implies{R}(\top{R}(), \equals{Q, R}(
                    \equals{SortS{}, Q}(p{}(X:SortS{}), a{}()),
                    \and{Q}(\equals{SortS{}, Q}(X:SortS{}, Y:SortS{}), \top{Q}())))
                    [label{}("eq"), simplification{}()]"#
            ),
            ["Y"]
        );
    }

    /// A variable only of the `requires` never reaches the result, so nothing is recorded; a
    /// rewrite rule is not an equation, and mints its unbound variables per application.
    #[test]
    fn requires_only_variables_and_rewrite_rules_record_nothing() {
        assert_eq!(
            unbound_result(
                r#"axiom{R} \implies{R}(
                    \and{R}(
                        \equals{SortS{}, R}(p{}(Y:SortS{}), a{}()),
                        \and{R}(\in{SortS{}, R}(K0:SortS{}, X:SortS{}), \top{R}())),
                    \equals{SortS{}, R}(
                        f{}(K0:SortS{}), \and{SortS{}}(X:SortS{}, \top{SortS{}}())))
                    [label{}("eq")]"#,
            ),
            Vec::<String>::new()
        );
        let definition = load(
            r#"axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(a{}(), \top{SortS{}}()), \and{SortS{}}(c{}(Y:SortS{}), \top{SortS{}}()))
                [label{}("eq")]"#,
        );
        let rules = definition
            .rewrite_theory()
            .values()
            .flat_map(|groups| groups.values())
            .flatten()
            .collect::<Vec<_>>();
        assert_eq!(rules.len(), 1);
        assert!(
            rules[0]
                .computed_attributes
                .unbound_result_variables
                .is_empty()
        );
    }
}
