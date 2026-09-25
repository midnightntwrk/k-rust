//! ```toml algorithm
//! id = "kompile.sort_injections.insert"
//! name = "sort inference and explicit injection insertion"
//! sites = ["SortInjector::inject_sentence", "SortInjector::term_sort_with_arity", "add_sort_injections_to_definition"]
//! variable = "N = term nodes; P = production candidates; S = subsort queries"
//! counters = ["KompileInjectionsInserted"]
//!
//! [[cost]]
//! mode = "one sentence"
//! bound = "O(N x (P + S))"
//! ```
//!
//! Sort injection computes expected sorts, least upper bounds, and explicit KORE injections, with strict rebase-in and lossy localization-out metadata policies.
//! Work is O(term nodes times production and subsort queries); `KompileInjectionsInserted` measures its variable work, and the shared pass scaffolding counts resolutions and copied sentences.
//!
//! Production-aware insertion of explicit KORE subsort injections.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use k_rust_kore::measure::{self, Counter};
use serde_json::json;

use crate::definition::{
    AttributeKey, Definition, DefinitionViews, LabelHead, ModuleId, PartialOrder,
    ProductionCatalog, ResolveError, ResolvedDefinition, Sentence, SortCatalog, SortHead,
};
use crate::kast::{FrontendSort, InternalLabel, Label, Sort, Term};
use crate::names::{BuiltinSort, WellKnownSymbol};
use crate::provenance::GeneratingPass;

use super::passes::{injectable, placeable};

mod typing;
use super::view::View;
pub use typing::{
    BranchTyping, PositionTyping, SentenceTyper, SentenceTyping, SentenceTypingError,
    sentence_typing,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SortInjectionError {
    Definition(ResolveError),
    MissingModule(String),
    CircularSubsort(Vec<Sort>),
    MissingSort(&'static str),
    UnknownLabel(String),
    AmbiguousLabel {
        label: String,
        productions: usize,
    },
    InvalidResolvedProduction {
        label: String,
        production: String,
        message: String,
    },
    InvalidImportedMetadata {
        module: String,
        message: String,
    },
    Sentence {
        module: String,
        sentence: usize,
        source: Option<String>,
        line: Option<u32>,
        error: Box<SortInjectionError>,
    },
    InvalidArity {
        label: String,
        expected: usize,
        actual: usize,
    },
    InvalidSortPredicate {
        label: String,
    },
    MissingParameters {
        label: String,
        expected: usize,
        actual: usize,
    },
    IncompatibleSorts {
        sorts: Vec<Sort>,
        expected: Option<Sort>,
    },
    /// A term whose sort is not below the sort its position requires, so the only injection that
    /// could place it there, `inj{found, required}`, is not an embedding of the subsort order.
    IllSortedTerm(Box<SortMismatch>),
    /// A semantic cast whose target (`required`) is neither at or above the operand's sort
    /// (`found`) nor strictly below it, so the cast is neither an upcast (an injection) nor a
    /// downcast (a projection).
    IncomparableCast(Box<SortMismatch>),
    /// A parametric production whose arguments fit several incomparable least instantiations,
    /// so no instantiation fits them most tightly.
    AmbiguousInstance(Box<AmbiguousInstance>),
}

/// A parametric production's arguments with several incomparable least instantiations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AmbiguousInstance {
    /// The declared argument sorts involved, with their sort parameters.
    pub declared: Vec<Sort>,
    /// The sorts of the corresponding arguments.
    pub arguments: Vec<Sort>,
    /// Declared argument sorts under representative minimal instantiations. When independent
    /// parameter groups are ambiguous, these vary one group while fixing the others.
    pub candidates: Vec<Vec<Sort>>,
}

/// A term and the two sorts a sort check found unrelated.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SortMismatch {
    /// The term, rendered and truncated for a diagnostic.
    pub term: String,
    /// The sort the term has.
    pub found: Sort,
    /// The sort its position or cast requires.
    pub required: Sort,
}

impl fmt::Display for SortInjectionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Definition(error) => error.fmt(formatter),
            Self::MissingModule(module) => {
                write!(formatter, "sort-injection module {module:?} was not found")
            }
            Self::CircularSubsort(path) => write!(
                formatter,
                "cannot add sort injections with circular subsorts: {}",
                path.iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" > ")
            ),
            Self::MissingSort(construct) => {
                write!(formatter, "cannot recover the sort of {construct}")
            }
            Self::UnknownLabel(label) => {
                write!(formatter, "cannot find a production for KLabel {label:?}")
            }
            Self::AmbiguousLabel { label, productions } => write!(
                formatter,
                "KLabel {label:?} has {productions} productions and no resolved production identity"
            ),
            Self::InvalidResolvedProduction {
                label,
                production,
                message,
            } => write!(
                formatter,
                "resolved production #{production} for KLabel {label:?} is invalid: {message}"
            ),
            Self::InvalidImportedMetadata { module, message } => write!(
                formatter,
                "cannot rebase production metadata from module {module:?}: {message}"
            ),
            Self::Sentence {
                module,
                sentence,
                source,
                line,
                error,
            } => {
                if let Some(source) = source {
                    write!(formatter, "{source}")?;
                    if let Some(line) = line {
                        write!(formatter, ":{line}")?;
                    }
                    write!(formatter, ": ")?;
                } else {
                    write!(formatter, "sentence {sentence} of module {module:?}: ")?;
                }
                error.fmt(formatter)
            }
            Self::InvalidArity {
                label,
                expected,
                actual,
            } => write!(
                formatter,
                "KLabel {label:?} expects {expected} arguments but received {actual}"
            ),
            Self::InvalidSortPredicate { label } => write!(
                formatter,
                "Invalid sort predicate {label} that depends directly or indirectly on the current configuration. Is it possible to replace the sort predicate with a regular function?"
            ),
            Self::MissingParameters {
                label,
                expected,
                actual,
            } => write!(
                formatter,
                "KLabel {label:?} expects {expected} sort parameters but carries {actual}"
            ),
            Self::IncompatibleSorts { sorts, expected } => {
                write!(
                    formatter,
                    "cannot compute a unique least upper bound for {}",
                    sorts
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", ")
                )?;
                if let Some(expected) = expected {
                    write!(formatter, " below expected sort {expected}")?;
                }
                Ok(())
            }
            Self::IllSortedTerm(mismatch) => write!(
                formatter,
                "term {} has sort {}, which is not a subsort of the sort {} its position requires",
                mismatch.term, mismatch.found, mismatch.required
            ),
            Self::IncomparableCast(mismatch) => write!(
                formatter,
                "semantic cast of {} to sort {} is not comparable with its sort {}: it is neither an upcast nor a downcast",
                mismatch.term, mismatch.required, mismatch.found
            ),
            Self::AmbiguousInstance(ambiguity) => {
                let list = |sorts: &[Sort]| {
                    sorts
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", ")
                };
                write!(
                    formatter,
                    "arguments of sorts ({}) fit ({}) at several incomparable least instantiations: {}",
                    list(&ambiguity.arguments),
                    list(&ambiguity.declared),
                    ambiguity
                        .candidates
                        .iter()
                        .map(|candidate| format!("({})", list(candidate)))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
    }
}

impl std::error::Error for SortInjectionError {}

/// Adds explicit `inj{From,To}` applications using one resolved module's syntax.
///
/// Public terms may contain variables without sort annotations. A positional expected sort types
/// such a variable during injection; without an expected sort, it defaults to `K`. Application
/// sort metadata produced by semantic-cast resolution requests a runtime projection only when the
/// metadata sort is a strict subsort of the selected production's natural result sort.
#[derive(Clone, Debug)]
pub struct SortInjector<'view, 'definition> {
    productions: View<'view, ProductionCatalog<'definition>>,
    sorts: View<'view, SortCatalog<'definition>>,
    subsorts: View<'view, PartialOrder<Sort>>,
    next_sort_parameter: Cell<usize>,
    used_sort_parameters: RefCell<BTreeSet<String>>,
}

impl<'definition> SortInjector<'definition, 'definition> {
    pub fn new(
        definition: &'definition ResolvedDefinition,
        module: &str,
    ) -> Result<Self, SortInjectionError> {
        let module = definition
            .module_id(module)
            .ok_or_else(|| SortInjectionError::MissingModule(module.to_owned()))?;
        let subsorts = definition
            .subsorts(module)
            .map_err(|cycle| SortInjectionError::CircularSubsort(cycle.path))?;
        Ok(Self {
            productions: View::Shared(definition.production_catalog(module)),
            sorts: View::Owned(definition.sort_catalog(module)),
            subsorts: View::Owned(subsorts),
            next_sort_parameter: Cell::new(0),
            used_sort_parameters: RefCell::new(BTreeSet::new()),
        })
    }
}

impl<'view, 'definition> SortInjector<'view, 'definition> {
    pub(crate) fn with_views(
        views: &'view DefinitionViews<'definition>,
        module: ModuleId,
    ) -> Result<Self, SortInjectionError> {
        let subsorts = views
            .subsorts(module)
            .map_err(|cycle| SortInjectionError::CircularSubsort(cycle.path.clone()))?;
        Ok(Self {
            productions: View::Borrowed(views.production_catalog(module)),
            sorts: View::Borrowed(views.sort_catalog(module)),
            subsorts: View::Borrowed(subsorts),
            next_sort_parameter: Cell::new(0),
            used_sort_parameters: RefCell::new(BTreeSet::new()),
        })
    }

    /// Add injections to a standalone term in the supplied top-level sort.
    pub fn inject(&self, term: &Term, expected: &Sort) -> Result<Term, SortInjectionError> {
        self.inject_with_position(term, expected, false)
    }

    /// Infer a standalone term's top sort and add every injection below it.
    pub fn inject_at_top(&self, term: &Term) -> Result<Term, SortInjectionError> {
        let top = self.term_sort(term, None)?;
        self.inject_with_position(term, &top, false)
    }

    pub(crate) fn is_user_list_sort(&self, sort: &Sort) -> bool {
        self.sorts.list_sorts().contains(sort)
    }

    /// Match Java's sentence boundary: rule/claim conditions are always `Bool`.
    pub fn inject_sentence(&self, sentence: &Sentence) -> Result<Sentence, SortInjectionError> {
        self.next_sort_parameter.set(0);
        self.used_sort_parameters.borrow_mut().clear();
        match sentence {
            Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            } => {
                let body = self.inject_rule_body(body)?;
                let requires = self.inject(requires, &Sort::builtin(BuiltinSort::Bool))?;
                let ensures = self.inject(ensures, &Sort::builtin(BuiltinSort::Bool))?;
                Ok(Sentence::Rule {
                    body,
                    requires,
                    ensures,
                    attributes: self.sentence_attributes(attributes),
                })
            }
            Sentence::Claim {
                body,
                requires,
                ensures,
                attributes,
            } => {
                let body = self.inject_rule_body(body)?;
                let requires = self.inject(requires, &Sort::builtin(BuiltinSort::Bool))?;
                let ensures = self.inject(ensures, &Sort::builtin(BuiltinSort::Bool))?;
                Ok(Sentence::Claim {
                    body,
                    requires,
                    ensures,
                    attributes: self.sentence_attributes(attributes),
                })
            }
            _ => Ok(sentence.clone()),
        }
    }

    fn inject_rule_body(&self, body: &Term) -> Result<Term, SortInjectionError> {
        let body = if has_rewrite(body) {
            Term::Rewrite {
                left: Box::new(rewrite_projection(body, false)),
                right: Box::new(rewrite_projection(body, true)),
            }
        } else {
            body.clone()
        };
        let top = self.fresh_sort_parameter();
        let actual = self.term_sort(&body, Some(&top))?;
        self.inject_with_position(&body, &actual, false)
    }

    fn sentence_attributes(
        &self,
        attributes: &crate::definition::Attributes,
    ) -> crate::definition::Attributes {
        let mut attributes = attributes.clone();
        let parameters = self.used_sort_parameters.borrow();
        if !parameters.is_empty() {
            attributes.set(
                AttributeKey::SortParams,
                json!({
                    "node": "KSort",
                    "name": "",
                    "params": parameters.iter().map(|name| json!({
                        "node": "KSort",
                        "name": name,
                        "params": [],
                    })).collect::<Vec<_>>(),
                }),
            );
        }
        attributes
    }

    fn fresh_sort_parameter(&self) -> Sort {
        let index = self.next_sort_parameter.get();
        self.next_sort_parameter.set(index + 1);
        Sort::with_parameters(
            FrontendSort::SortParam.as_str(),
            vec![Sort::new(format!("Q{index}"))],
        )
    }

    /// Infer a term's sort in an optional positional context.
    ///
    /// An unsorted variable uses `expected` when supplied and defaults to `K` otherwise.
    pub fn term_sort(
        &self,
        term: &Term,
        expected: Option<&Sort>,
    ) -> Result<Sort, SortInjectionError> {
        self.term_sort_with_arity(term, expected, false)
    }

    /// Infer a sort before cell terms have been normalized to their generated productions.
    ///
    /// Java's sort-only inference visits the declared nonterminal prefix and ignores trailing
    /// syntax children. GuardOrPatterns runs while authored cells still carry their dots and
    /// aggregate child, so this narrow entry point retains that behavior. Missing declared
    /// children and every other inference error remain errors.
    pub(crate) fn term_sort_before_shape_normalization(
        &self,
        term: &Term,
        expected: Option<&Sort>,
    ) -> Result<Sort, SortInjectionError> {
        self.term_sort_with_arity(term, expected, true)
    }

    fn term_sort_with_arity(
        &self,
        term: &Term,
        expected: Option<&Sort>,
        allow_trailing_arguments: bool,
    ) -> Result<Sort, SortInjectionError> {
        Ok(self
            .sort_and_downcast(term, expected, allow_trailing_arguments)?
            .0)
    }

    /// Infer a term's sort together with the downcast target the injector projects it to.
    ///
    /// A semantic cast on an application or token whose target is at or above the selected
    /// production's result sort records the intended overload/context, not a replacement for that
    /// result sort: `{P}:K` where `P:KItem` must still materialize the KItem-to-K sequence wrapper,
    /// and an exact-sort cast needs nothing. A target strictly below the result sort is a
    /// downcast: the injector replaces the term by `project:<target>(term)`, whose declared result
    /// sort is `target`, so `target` is the sort of the term the sentence contains and the second
    /// component is `Some(target)`. Every enclosing inference must see that sort.
    ///
    /// A cast `t:S` claims that `t` denotes an element of `S`. When `S` is neither at or above the
    /// sort of `t` nor strictly below it, no injection or projection realizes that claim, so the
    /// cast is rejected as [`SortInjectionError::IncomparableCast`]. The rule applies to every
    /// operand with a sort of its own (applications, tokens, K sequences, injected labels, sorted
    /// variables); a cast on a rewrite or `as` pattern instead fixes the sort its sides are
    /// injected at, and a sortless variable takes the cast's sort.
    fn sort_and_downcast(
        &self,
        term: &Term,
        expected: Option<&Sort>,
        allow_trailing_arguments: bool,
    ) -> Result<(Sort, Option<Sort>), SortInjectionError> {
        let cast = term.metadata().and_then(|metadata| metadata.sort.as_ref());
        match (term.unannotated(), cast) {
            // A cast on a rewrite or an `as` pattern is the sort its sides are placed at: each
            // side is injected at `sort`, which checks it against the cast.
            (Term::Rewrite { .. } | Term::As { .. }, Some(sort)) => {
                return Ok((sort.clone(), None));
            }
            // A variable without its own sort has the cast's sort; there is no operand sort to
            // compare it with.
            (Term::Variable { sort: None, .. }, Some(sort)) => return Ok((sort.clone(), None)),
            _ => {}
        }
        let natural = self.natural_sort(term, expected, allow_trailing_arguments)?;
        match cast {
            Some(target) if *target != natural && self.subsorts.less_than_eq(target, &natural) => {
                Ok((target.clone(), Some(target.clone())))
            }
            Some(target) if !self.below(&natural, target) && !self.below(target, &natural) => Err(
                SortInjectionError::IncomparableCast(Box::new(SortMismatch {
                    term: render_term(term),
                    found: natural,
                    required: target.clone(),
                })),
            ),
            _ => Ok((natural, None)),
        }
    }

    /// Whether compilation can place a term of sort `actual` at a position of sort `expected`
    /// ([`placeable`]): by one injection along the subsort axioms, including every non-parser sort
    /// below `KItem`, or through the one-element `K` sequence of a `KItem`.
    ///
    /// The injector also serves callers that never ran the `add KItem subsorts` stage, so the
    /// relation states the implicit `KItem` subsorts itself.
    ///
    /// A sort that mentions a sort variable (`#SortParam`) stands for every instance of it: a
    /// sentence's sort parameters are universally quantified, so the relation must hold for every
    /// instantiation. The order has no parametric subsort declarations (a production with sort
    /// parameters declares no subsort), so that holds only reflexively (the same sort, variables
    /// included), or through `KItem` when the sort's head is not a parser sort; the relation
    /// therefore applies unchanged to such sorts.
    fn below(&self, actual: &Sort, expected: &Sort) -> bool {
        placeable(actual, expected, &self.subsorts)
    }

    /// Whether a single `inj{actual, expected}` is justified ([`injectable`]).
    fn injects(&self, actual: &Sort, expected: &Sort) -> bool {
        injectable(actual, expected, &self.subsorts)
    }

    /// Reject a term of sort `actual` at a position of sort `expected` unless one injection places it.
    fn check_injects(
        &self,
        term: &Term,
        actual: &Sort,
        expected: &Sort,
    ) -> Result<(), SortInjectionError> {
        if self.injects(actual, expected) {
            Ok(())
        } else {
            Err(SortInjectionError::IllSortedTerm(Box::new(SortMismatch {
                term: render_term(term),
                found: actual.clone(),
                required: expected.clone(),
            })))
        }
    }

    // Invariant: each recursive call (through `term_sort_with_arity` and `sort_and_downcast`, which call `natural_sort` once on the same term) descends into a direct subterm of `term` (a rewrite side, an `as` pattern or alias, or one argument of a sort-transparent application), so the depth of `term` bounds the recursion.
    fn natural_sort(
        &self,
        term: &Term,
        expected: Option<&Sort>,
        allow_trailing_arguments: bool,
    ) -> Result<Sort, SortInjectionError> {
        match term.unannotated() {
            Term::InjectedLabel(_) => Ok(Sort::builtin(BuiltinSort::KItem)),
            Term::Rewrite { left, right } => {
                let left = self.term_sort_with_arity(left, expected, allow_trailing_arguments)?;
                let right = self.term_sort_with_arity(right, expected, allow_trailing_arguments)?;
                self.least_upper_bound(&[left, right], expected)
            }
            Term::As { pattern, alias } => {
                let pattern =
                    self.term_sort_with_arity(pattern, expected, allow_trailing_arguments)?;
                let alias = self.term_sort_with_arity(alias, expected, allow_trailing_arguments)?;
                self.least_upper_bound(&[pattern, alias], expected)
            }
            Term::Variable { sort, .. } => Ok(sort
                .clone()
                .or_else(|| expected.cloned())
                .unwrap_or_else(|| Sort::builtin(BuiltinSort::K))),
            Term::Sequence(_) => Ok(Sort::builtin(BuiltinSort::K)),
            Term::Token { sort, .. } => Ok(sort.clone()),
            Term::Apply { label, arguments } => {
                if label.is(WellKnownSymbol::Inj) {
                    return label.parameters.get(1).cloned().ok_or_else(|| {
                        SortInjectionError::MissingParameters {
                            label: label.name.clone(),
                            expected: 2,
                            actual: label.parameters.len(),
                        }
                    });
                }
                if let Some(sort) = label.semantic_cast_sort() {
                    return Ok(sort);
                }
                if label.is(InternalLabel::OuterCast) {
                    let [argument] = arguments.as_slice() else {
                        return Err(SortInjectionError::InvalidArity {
                            label: label.name.clone(),
                            expected: 1,
                            actual: arguments.len(),
                        });
                    };
                    return self.term_sort_with_arity(argument, expected, allow_trailing_arguments);
                }
                if InternalLabel::of(&label.name)
                    .is_some_and(|internal| InternalLabel::MATCHING_LOGIC.contains(&internal))
                    && self.has_production(term, label)
                {
                    return Ok(self
                        .signature(term, label, arguments, expected, allow_trailing_arguments)?
                        .result);
                }
                match InternalLabel::of(&label.name) {
                    Some(
                        InternalLabel::Top
                        | InternalLabel::Bottom
                        | InternalLabel::And
                        | InternalLabel::Or
                        | InternalLabel::Not
                        | InternalLabel::Implies
                        | InternalLabel::AG
                        | InternalLabel::WeakExistsFinally
                        | InternalLabel::WeakAlwaysFinally,
                    ) => {
                        return label.parameters.first().cloned().ok_or_else(|| {
                            SortInjectionError::MissingParameters {
                                label: label.name.clone(),
                                expected: 1,
                                actual: label.parameters.len(),
                            }
                        });
                    }
                    Some(InternalLabel::Ceil | InternalLabel::Floor | InternalLabel::Equals) => {
                        return label.parameters.get(1).cloned().ok_or_else(|| {
                            SortInjectionError::MissingParameters {
                                label: label.name.clone(),
                                expected: 2,
                                actual: label.parameters.len(),
                            }
                        });
                    }
                    Some(InternalLabel::Exists | InternalLabel::Forall) => {
                        return label.parameters.last().cloned().ok_or_else(|| {
                            SortInjectionError::MissingParameters {
                                label: label.name.clone(),
                                expected: 1,
                                actual: 0,
                            }
                        });
                    }
                    Some(InternalLabel::Fun2) if arguments.len() >= 2 => {
                        return self.term_sort_with_arity(
                            &arguments[0],
                            expected,
                            allow_trailing_arguments,
                        );
                    }
                    Some(InternalLabel::Fun3) if arguments.len() >= 3 => {
                        return self.term_sort_with_arity(
                            &arguments[1],
                            expected,
                            allow_trailing_arguments,
                        );
                    }
                    Some(InternalLabel::Let) if arguments.len() >= 3 => {
                        return self.term_sort_with_arity(
                            &arguments[2],
                            expected,
                            allow_trailing_arguments,
                        );
                    }
                    Some(InternalLabel::KEqualsK | InternalLabel::KNotEqualsK) => {
                        return Ok(Sort::builtin(BuiltinSort::Bool));
                    }
                    _ => {}
                }
                let signature =
                    self.signature(term, label, arguments, expected, allow_trailing_arguments)?;
                Ok(signature.result)
            }
            Term::Annotated { .. } => unreachable!(),
        }
    }

    // Invariant: each call either retries once on the `semantic_projection` of `term`, whose argument carries no cast sort and so cannot project again, or recurses through `visit_children` into the direct subterms of `term`; the depth of `term` bounds the calls.
    fn inject_with_position(
        &self,
        term: &Term,
        expected: &Sort,
        is_lhs: bool,
    ) -> Result<Term, SortInjectionError> {
        let (actual, downcast) = self.sort_and_downcast(term, Some(expected), false)?;
        if let Some(target) = downcast {
            let projected = semantic_projection(term, &target);
            return self.inject_with_position(&projected, expected, is_lhs);
        }
        if actual == *expected {
            return self.visit_children(term, &actual, is_lhs);
        }

        let visited = self.visit_children(term, &actual, is_lhs)?;
        if expected.name == BuiltinSort::K.k_name() {
            if actual.name == BuiltinSort::KItem.k_name() {
                return Ok(Term::Sequence(vec![visited]));
            }
            self.check_injects(term, &actual, &Sort::builtin(BuiltinSort::KItem))?;
            return Ok(Term::Sequence(vec![injection(
                actual,
                Sort::builtin(BuiltinSort::KItem),
                visited,
            )]));
        }
        if let Some(wrapped) =
            self.collection_wrapper(term, &actual, expected, visited.clone(), is_lhs)?
        {
            return Ok(wrapped);
        }
        if let Some(wrapped) = self.user_list_wrapper(&actual, expected, visited.clone()) {
            return Ok(wrapped);
        }
        if self.injects(&actual, expected) {
            return Ok(injection(actual, expected.clone(), visited));
        }
        // A position above `K`: the term is a `K` as a one-element sequence, and that `K` is
        // injected into the position.
        let k = Sort::builtin(BuiltinSort::K);
        let k_item = Sort::builtin(BuiltinSort::KItem);
        if self.injects(&k, expected) && self.injects(&actual, &k_item) {
            let item = if actual == k_item {
                visited
            } else {
                injection(actual, k_item, visited)
            };
            return Ok(injection(k, expected.clone(), Term::Sequence(vec![item])));
        }
        Err(SortInjectionError::IllSortedTerm(Box::new(SortMismatch {
            term: render_term(term),
            found: actual,
            required: expected.clone(),
        })))
    }

    fn user_list_wrapper(&self, actual: &Sort, expected: &Sort, visited: Term) -> Option<Term> {
        if !self.is_user_list_sort(expected) || self.is_user_list_sort(actual) {
            return None;
        }
        let mut recursive = self
            .productions
            .productions_for_sort(&SortHead::from(expected))
            .iter()
            .filter_map(|id| match self.productions.production(*id) {
                Sentence::Production {
                    label: Some(label),
                    parameters,
                    sort,
                    items,
                    attributes,
                } if parameters.is_empty()
                    && sort == expected
                    && attributes.has(AttributeKey::UserList) =>
                {
                    let arguments = items
                        .iter()
                        .filter_map(|item| match item {
                            crate::definition::ProductionItem::NonTerminal { sort, .. } => {
                                Some(sort)
                            }
                            crate::definition::ProductionItem::Terminal(_)
                            | crate::definition::ProductionItem::RegexTerminal { .. } => None,
                        })
                        .collect::<Vec<_>>();
                    match arguments.as_slice() {
                        [child, list]
                            if *list == expected
                                && (actual == *child
                                    || self.subsorts.less_than_eq(actual, child)) =>
                        {
                            Some((label.clone(), false))
                        }
                        [list, child]
                            if *list == expected
                                && (actual == *child
                                    || self.subsorts.less_than_eq(actual, child)) =>
                        {
                            Some((label.clone(), true))
                        }
                        _ => None,
                    }
                }
                _ => None,
            });
        let (recursive_label, list_first) = recursive.next()?;
        if recursive.next().is_some() {
            return None;
        }

        let mut terminators = self
            .productions
            .productions_for_sort(&SortHead::from(expected))
            .iter()
            .filter_map(|id| match self.productions.production(*id) {
                Sentence::Production {
                    label: Some(label),
                    parameters,
                    sort,
                    items,
                    attributes,
                } if parameters.is_empty()
                    && sort == expected
                    && attributes.has(AttributeKey::UserList)
                    && !items.iter().any(|item| {
                        matches!(item, crate::definition::ProductionItem::NonTerminal { .. })
                    }) =>
                {
                    Some(label.clone())
                }
                _ => None,
            });
        let terminator = terminators.next()?;
        if terminators.next().is_some() {
            return None;
        }
        let terminator = Term::Apply {
            label: terminator,
            arguments: Vec::new(),
        };
        let arguments = if list_first {
            vec![terminator, visited]
        } else {
            vec![visited, terminator]
        };
        Some(Term::Apply {
            label: recursive_label,
            arguments,
        })
    }

    fn collection_wrapper(
        &self,
        term: &Term,
        actual: &Sort,
        expected: &Sort,
        visited: Term,
        is_lhs: bool,
    ) -> Result<Option<Term>, SortInjectionError> {
        let hook = self
            .sorts
            .attributes_for(&SortHead::from(expected))
            .and_then(|attributes| attributes.string(AttributeKey::Hook));
        if !matches!(hook, Some("MAP.Map" | "SET.Set" | "LIST.List")) {
            return Ok(None);
        }
        let Term::Apply { label, arguments } = term.unannotated() else {
            return Ok(None);
        };
        // Invariant: no production before `production` in catalog order carries both `wrapElement` and `element` with a wrapped label of sort `actual`, since the first one that does returns; each candidate scans the productions of its wrapped label once.
        for (_, production) in self.productions.productions() {
            let Sentence::Production { attributes, .. } = production else {
                unreachable!()
            };
            let (Some(wrapped_label), Some(element_label)) = (
                attributes.string(AttributeKey::WrapElement),
                attributes.string(AttributeKey::Element),
            ) else {
                continue;
            };
            let wraps_actual = self
                .productions
                .productions_for(&LabelHead::new(wrapped_label))
                .iter()
                .any(|id| {
                    matches!(
                        self.productions.production(*id),
                        Sentence::Production { sort, .. } if sort == actual
                    )
                });
            if !wraps_actual {
                continue;
            }
            let is_map = attributes.has(AttributeKey::Comm)
                && !attributes.has(AttributeKey::Idem)
                && !attributes.has(AttributeKey::Bag);
            if !is_map {
                return Ok(Some(Term::apply(element_label, vec![visited])));
            }

            let element_ids = self
                .productions
                .productions_for(&LabelHead::new(element_label));
            let Some(element_id) = element_ids.first() else {
                return Err(SortInjectionError::UnknownLabel(element_label.into()));
            };
            let Sentence::Production { items, .. } = self.productions.production(*element_id)
            else {
                unreachable!()
            };
            let key_sort = items.iter().find_map(|item| match item {
                crate::definition::ProductionItem::NonTerminal { sort, .. } => Some(sort),
                _ => None,
            });
            let Some(key_sort) = key_sort else {
                return Err(SortInjectionError::InvalidArity {
                    label: element_label.into(),
                    expected: 2,
                    actual: 0,
                });
            };
            let key = if label.name == wrapped_label {
                arguments
                    .first()
                    .cloned()
                    .ok_or_else(|| SortInjectionError::InvalidArity {
                        label: label.name.clone(),
                        expected: 1,
                        actual: 0,
                    })?
            } else {
                Term::apply(format!("{}Key", expected.name), vec![visited.clone()])
            };
            let key = self.inject_with_position(&key, key_sort, is_lhs)?;
            return Ok(Some(Term::apply(element_label, vec![key, visited])));
        }
        Ok(None)
    }

    fn visit_children(
        &self,
        term: &Term,
        actual: &Sort,
        is_lhs: bool,
    ) -> Result<Term, SortInjectionError> {
        if actual.name == FrontendSort::SortParam.as_str()
            && let Some(parameter) = actual.parameters.first()
        {
            self.used_sort_parameters
                .borrow_mut()
                .insert(parameter.name.clone());
        }
        let rebuilt = match term.unannotated() {
            Term::Apply { label, .. } if label.is(WellKnownSymbol::Inj) => return Ok(term.clone()),
            Term::Apply { label, arguments }
                if label.semantic_cast_sort().is_some() || label.is(InternalLabel::OuterCast) =>
            {
                let [argument] = arguments.as_slice() else {
                    return Err(SortInjectionError::InvalidArity {
                        label: label.name.clone(),
                        expected: 1,
                        actual: arguments.len(),
                    });
                };
                Term::Apply {
                    label: label.clone(),
                    arguments: vec![self.inject_with_position(argument, actual, is_lhs)?],
                }
            }
            Term::Apply { label, arguments } => {
                let signature = self.signature(term, label, arguments, Some(actual), false)?;
                let arguments = arguments
                    .iter()
                    .zip(signature.arguments.iter())
                    .map(|(argument, expected)| {
                        self.inject_with_position(argument, expected, is_lhs)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Term::Apply {
                    label: signature.label,
                    arguments,
                }
            }
            Term::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.inject_with_position(left, actual, true)?),
                right: Box::new(self.inject_with_position(right, actual, false)?),
            },
            // The alias names the value the pattern matches, at the as-pattern's sort. A sortless
            // alias variable takes that sort; an alias with a sort of its own is placed at that
            // sort like the pattern, so it is injected when below it and rejected otherwise.
            Term::As { pattern, alias } => Term::As {
                pattern: Box::new(self.inject_with_position(pattern, actual, is_lhs)?),
                alias: Box::new(match alias.unannotated() {
                    Term::Variable { sort: Some(_), .. } => {
                        self.inject_with_position(alias, actual, is_lhs)?
                    }
                    _ => with_variable_sort(alias, actual),
                }),
            },
            Term::Sequence(items) => {
                let items = items
                    .iter()
                    .map(|item| {
                        let context = if is_lhs {
                            Sort::builtin(BuiltinSort::KItem)
                        } else {
                            Sort::builtin(BuiltinSort::K)
                        };
                        let item_sort = self.term_sort(item, Some(&context))?;
                        let expected = if item_sort.name == BuiltinSort::K.k_name() {
                            Sort::builtin(BuiltinSort::K)
                        } else {
                            Sort::builtin(BuiltinSort::KItem)
                        };
                        self.inject_with_position(item, &expected, is_lhs)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Term::sequence(items)
            }
            Term::InjectedLabel(label) => Term::InjectedLabel(label.clone()),
            Term::Variable { name, .. } => Term::Variable {
                name: name.clone(),
                sort: Some(actual.clone()),
            },
            Term::Token { token, sort } => Term::Token {
                token: token.clone(),
                sort: sort.clone(),
            },
            Term::Annotated { .. } => unreachable!(),
        };
        Ok(copy_metadata(term, rebuilt))
    }

    fn signature(
        &self,
        term: &Term,
        label: &Label,
        arguments: &[Term],
        expected: Option<&Sort>,
        allow_trailing_arguments: bool,
    ) -> Result<InstantiatedSignature, SortInjectionError> {
        let expected = term
            .metadata()
            .and_then(|metadata| metadata.sort.as_ref())
            .or(expected);
        let production = self.production(term, label)?;
        let Sentence::Production {
            parameters,
            sort,
            items,
            ..
        } = production
        else {
            unreachable!()
        };
        let argument_sorts = items
            .iter()
            .filter_map(|item| match item {
                crate::definition::ProductionItem::NonTerminal { sort, .. } => Some(sort),
                _ => None,
            })
            .collect::<Vec<_>>();
        if argument_sorts.len() != arguments.len()
            && (!allow_trailing_arguments || arguments.len() < argument_sorts.len())
        {
            if label.name.strip_prefix("is").is_some_and(|sort| {
                self.sorts
                    .defined_heads()
                    .contains(&SortHead::nullary(sort))
            }) {
                return Err(SortInjectionError::InvalidSortPredicate {
                    label: label.name.clone(),
                });
            }
            return Err(SortInjectionError::InvalidArity {
                label: label.name.clone(),
                expected: argument_sorts.len(),
                actual: arguments.len(),
            });
        }
        let substitution = if parameters.is_empty() {
            BTreeMap::new()
        } else {
            let expected = expected
                .cloned()
                .unwrap_or_else(|| self.fresh_sort_parameter());
            let fresh = parameters
                .iter()
                .map(|parameter| {
                    if parameter == sort {
                        expected.clone()
                    } else {
                        self.fresh_sort_parameter()
                    }
                })
                .collect::<Vec<_>>();
            let fresh_substitution = parameters
                .iter()
                .cloned()
                .zip(fresh.iter().cloned())
                .collect::<BTreeMap<_, _>>();
            let actual_sorts = arguments
                .iter()
                .zip(
                    argument_sorts
                        .iter()
                        .map(|sort| substitute_sort(sort, &fresh_substitution)),
                )
                .map(|(argument, fresh_expected)| {
                    self.term_sort_with_arity(
                        argument,
                        Some(&fresh_expected),
                        allow_trailing_arguments,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            self.solve_parameters(
                parameters,
                &argument_sorts,
                &actual_sorts,
                sort,
                &expected,
                &fresh_substitution,
            )?
        };
        let instantiated_parameters = parameters
            .iter()
            .map(|parameter| substitute_sort(parameter, &substitution))
            .collect::<Vec<_>>();
        Ok(InstantiatedSignature {
            label: Label::with_parameters(&label.name, instantiated_parameters),
            arguments: argument_sorts
                .into_iter()
                .map(|sort| substitute_sort(sort, &substitution))
                .collect(),
            result: substitute_sort(sort, &substitution),
        })
    }

    /// Instantiate a parametric production's sort parameters from its arguments and position.
    ///
    /// The unknowns are all of `parameters`. The constraints are: every argument whose sort is
    /// concrete is at or below its declared sort instantiated (`actual <= declared[σ]`), and,
    /// when the position is concrete and the result sort mentions a parameter, the instantiated
    /// result is at or below the position. An argument whose sort still contains a sort
    /// variable of the enclosing sentence constrains nothing here; injecting it decides.
    ///
    /// Candidate values of a parameter `p`:
    /// - where `p` is a whole argument sort, the minimal upper bounds of those arguments' sorts
    ///   (every value satisfying these lower bounds lies above one of them, and a larger one
    ///   satisfies no further upper-bound constraint), also taken below the position when `p` is
    ///   the result sort;
    /// - where an argument sort contains `p`, the values that match it against the argument's
    ///   sort and the declared sorts above it; where the result contains `p`, those that match it
    ///   against the position and the declared sorts below it;
    /// - a parameter that occurs in no argument keeps its existing rule: the values matching the
    ///   result against the position and the sorts below it, joined by their least upper bound,
    ///   or the position itself for a result that is the parameter.
    ///
    /// A parameter without candidates keeps its uninstantiated fallback (a sort variable of an
    /// argument, or the fresh parameter), and injecting the arguments then decides. The exact
    /// assignment (each argument's sort as its declared sort) is tried first and accepted when it
    /// satisfies every constraint. Otherwise the least satisfying assignment in the pointwise
    /// order on the instantiated argument sorts is chosen; when none satisfies the position
    /// constraint, the least assignment satisfying the argument constraints is chosen, so a
    /// position the injector fills through a wrapper or a projection is decided there. Several
    /// incomparable minimal assignments are [`SortInjectionError::AmbiguousInstance`].
    // Invariant: each connected group visits its candidate product once. Independent groups add
    // their costs rather than multiplying them, and only current minima are retained.
    fn solve_parameters(
        &self,
        parameters: &[Sort],
        declared: &[&Sort],
        actual: &[Sort],
        result: &Sort,
        position: &Sort,
        fallback: &BTreeMap<Sort, Sort>,
    ) -> Result<BTreeMap<Sort, Sort>, SortInjectionError> {
        let concrete = |sort: &Sort| !mentions_sort_parameter(sort);
        let mentions_parameter = |sort: &Sort| {
            parameters
                .iter()
                .any(|parameter| contains_sort(sort, parameter))
        };
        let constrained = declared
            .iter()
            .zip(actual)
            .filter(|(declared, actual)| mentions_parameter(declared) && concrete(actual))
            .map(|(declared, actual)| (*declared, actual))
            .collect::<Vec<_>>();
        let position_constrains = concrete(position) && mentions_parameter(result);
        let fits_arguments = |assignment: &BTreeMap<Sort, Sort>| {
            constrained.iter().all(|(declared, actual)| {
                self.below(actual, &substitute_sort(declared, assignment))
            })
        };
        let fits_position = |assignment: &BTreeMap<Sort, Sort>| {
            !position_constrains || self.below(&substitute_sort(result, assignment), position)
        };

        // An argument that is already an instance fixes every parameter in its declared sort.
        // Check this before gathering possible super-sort instances.
        let mut exact = BTreeMap::new();
        if constrained
            .iter()
            .all(|(declared, actual)| bind_parameters(parameters, declared, actual, &mut exact))
            && exact.len() == parameters.len()
            && fits_arguments(&exact)
            && fits_position(&exact)
        {
            return Ok(exact);
        }

        let mut candidates = parameters
            .iter()
            .map(|parameter| (parameter.clone(), BTreeSet::<Sort>::new()))
            .collect::<BTreeMap<_, _>>();
        let mut pending = BTreeMap::<Sort, Sort>::new();
        let candidate = |candidates: &mut BTreeMap<Sort, BTreeSet<Sort>>,
                         binding: BTreeMap<Sort, Sort>| {
            for (parameter, value) in binding {
                if let Some(values) = candidates.get_mut(&parameter) {
                    values.insert(value);
                }
            }
        };
        for parameter in parameters {
            if !declared
                .iter()
                .any(|declared| contains_sort(declared, parameter))
            {
                if parameter == result {
                    candidates
                        .get_mut(parameter)
                        .expect("every parameter has a candidate set")
                        .insert(position.clone());
                } else if contains_sort(result, parameter) {
                    let mut matches = BTreeMap::new();
                    self.match_sort_below(parameters, result, position, &mut matches);
                    if let Some(values) = matches.remove(parameter) {
                        let fallback = fallback.get(parameter).expect("fresh parameter");
                        let value = self.parametric_lub(&values, fallback)?;
                        candidates
                            .get_mut(parameter)
                            .expect("every parameter has a candidate set")
                            .insert(value);
                    }
                }
                continue;
            }
            let lower = declared
                .iter()
                .zip(actual)
                .filter(|(declared, _)| **declared == parameter)
                .map(|(_, actual)| actual.clone())
                .collect::<Vec<_>>();
            let lower_concrete = lower
                .iter()
                .filter(|sort| concrete(sort))
                .cloned()
                .collect::<Vec<_>>();
            if lower_concrete.is_empty() {
                if let Some(first) = lower.first() {
                    pending.insert(parameter.clone(), first.clone());
                }
                continue;
            }
            let values = candidates
                .get_mut(parameter)
                .expect("every parameter has a candidate set");
            values.extend(self.minimal_upper_bounds(&lower_concrete, None));
            if parameter == result && concrete(position) {
                values.extend(self.minimal_upper_bounds(&lower_concrete, Some(position)));
            }
        }
        for (declared, actual) in declared.iter().zip(actual) {
            if !mentions_parameter(declared) || parameters.contains(*declared) {
                continue;
            }
            if !concrete(actual) {
                let mut binding = BTreeMap::new();
                if bind_parameters(parameters, declared, actual, &mut binding) {
                    for (parameter, value) in binding {
                        pending.entry(parameter).or_insert(value);
                    }
                }
                continue;
            }
            let above = std::iter::once(actual).chain(
                self.sorts
                    .sorted_all_sorts()
                    .filter(|candidate| self.subsorts.less_than_eq(actual, candidate)),
            );
            for sort in above {
                let mut binding = BTreeMap::new();
                if bind_parameters(parameters, declared, sort, &mut binding) {
                    candidate(&mut candidates, binding);
                }
            }
        }
        if position_constrains && !parameters.contains(result) {
            let below = std::iter::once(position).chain(
                self.sorts
                    .sorted_all_sorts()
                    .filter(|candidate| self.subsorts.less_than_eq(candidate, position)),
            );
            for sort in below {
                let mut binding = BTreeMap::new();
                if bind_parameters(parameters, result, sort, &mut binding) {
                    binding.retain(|parameter, _| {
                        declared
                            .iter()
                            .any(|declared| contains_sort(declared, parameter))
                    });
                    candidate(&mut candidates, binding);
                }
            }
        }
        let domains = parameters
            .iter()
            .map(|parameter| {
                let values = &candidates[parameter];
                if values.is_empty() {
                    let value = pending
                        .get(parameter)
                        .or_else(|| fallback.get(parameter))
                        .expect("fresh parameter")
                        .clone();
                    (parameter.clone(), vec![value])
                } else {
                    (parameter.clone(), values.iter().cloned().collect())
                }
            })
            .collect::<Vec<_>>();

        // A parameter absent from concrete arguments can still have one inferred candidate.
        // Keep the exact preference when those candidates complete a partial exact binding.
        let mut completed_exact = BTreeMap::new();
        if constrained.iter().all(|(declared, actual)| {
            bind_parameters(parameters, declared, actual, &mut completed_exact)
        }) {
            for (parameter, values) in &domains {
                if !completed_exact.contains_key(parameter)
                    && let [value] = values.as_slice()
                {
                    completed_exact.insert(parameter.clone(), value.clone());
                }
            }
            if completed_exact.len() == parameters.len()
                && fits_arguments(&completed_exact)
                && fits_position(&completed_exact)
            {
                return Ok(completed_exact);
            }
        }

        // A constraint joins all parameters that occur in its declared sort. A concrete result
        // position joins the parameters of the result sort in the same way.
        fn root(parents: &mut [usize], index: usize) -> usize {
            if parents[index] != index {
                let parent = parents[index];
                parents[index] = root(parents, parent);
            }
            parents[index]
        }
        let mut parents = (0..parameters.len()).collect::<Vec<_>>();
        for sort in declared
            .iter()
            .copied()
            .chain(position_constrains.then_some(result))
        {
            let touched = parameters
                .iter()
                .enumerate()
                .filter_map(|(index, parameter)| contains_sort(sort, parameter).then_some(index))
                .collect::<Vec<_>>();
            if let Some((&first, rest)) = touched.split_first() {
                for &index in rest {
                    let first_root = root(&mut parents, first);
                    let index_root = root(&mut parents, index);
                    parents[index_root] = first_root;
                }
            }
        }
        let mut groups = BTreeMap::<usize, Vec<usize>>::new();
        for index in 0..parameters.len() {
            groups
                .entry(root(&mut parents, index))
                .or_default()
                .push(index);
        }
        let mut groups = groups.into_values().collect::<Vec<_>>();
        groups.sort_by_key(|group| group[0]);

        fn visit_assignments(
            domains: &[(Sort, Vec<Sort>)],
            assignment: &mut BTreeMap<Sort, Sort>,
            visit: &mut impl FnMut(&BTreeMap<Sort, Sort>),
        ) {
            if let Some(((parameter, values), rest)) = domains.split_first() {
                for value in values {
                    assignment.insert(parameter.clone(), value.clone());
                    visit_assignments(rest, assignment, visit);
                }
                assignment.remove(parameter);
            } else {
                visit(assignment);
            }
        }

        let mut chosen = BTreeMap::new();
        let mut group_minima = Vec::new();
        for group in groups {
            let group_domains = group
                .iter()
                .map(|&index| domains[index].clone())
                .collect::<Vec<_>>();
            let group_constraints = constrained
                .iter()
                .filter(|(declared, _)| {
                    group
                        .iter()
                        .any(|&index| contains_sort(declared, &parameters[index]))
                })
                .copied()
                .collect::<Vec<_>>();
            let group_has_position = position_constrains
                && group
                    .iter()
                    .any(|&index| contains_sort(result, &parameters[index]));
            let at_most = |left: &[Sort], right: &[Sort]| {
                left.iter()
                    .zip(right)
                    .all(|(left, right)| self.below(left, right))
            };
            let mut fitting = Vec::<(BTreeMap<Sort, Sort>, Vec<Sort>)>::new();
            let mut preferred = Vec::<(BTreeMap<Sort, Sort>, Vec<Sort>)>::new();
            visit_assignments(&group_domains, &mut BTreeMap::new(), &mut |assignment| {
                if !group_constraints.iter().all(|(declared, actual)| {
                    self.below(actual, &substitute_sort(declared, assignment))
                }) {
                    return;
                }
                let sorts = group_constraints
                    .iter()
                    .map(|(declared, _)| substitute_sort(declared, assignment))
                    .collect::<Vec<_>>();
                let retain_minimum = |minima: &mut Vec<(BTreeMap<Sort, Sort>, Vec<Sort>)>| {
                    if minima.iter().any(|(_, other)| at_most(other, &sorts)) {
                        return;
                    }
                    minima.retain(|(_, other)| !at_most(&sorts, other));
                    minima.push((assignment.clone(), sorts.clone()));
                };
                retain_minimum(&mut fitting);
                if !group_has_position || fits_position(assignment) {
                    retain_minimum(&mut preferred);
                }
            });
            let minima = if preferred.is_empty() {
                fitting
            } else {
                preferred
            };
            let Some((first, _)) = minima.first() else {
                // Nothing fits: keep the fallback for every parameter; injection rejects it.
                return Ok(domains
                    .into_iter()
                    .map(|(parameter, values)| (parameter, values[0].clone()))
                    .collect());
            };
            chosen.extend(first.clone());
            group_minima.push(minima);
        }
        if let Some(minima) = group_minima.iter().find(|minima| minima.len() > 1) {
            let candidates = minima
                .iter()
                .map(|(assignment, _)| {
                    let mut witness = chosen.clone();
                    witness.extend(assignment.clone());
                    constrained
                        .iter()
                        .map(|(declared, _)| substitute_sort(declared, &witness))
                        .collect()
                })
                .collect();
            Err(SortInjectionError::AmbiguousInstance(Box::new(
                AmbiguousInstance {
                    declared: constrained
                        .iter()
                        .map(|(declared, _)| (*declared).clone())
                        .collect(),
                    arguments: constrained
                        .iter()
                        .map(|(_, actual)| (*actual).clone())
                        .collect(),
                    candidates,
                },
            )))
        } else {
            Ok(chosen)
        }
    }

    fn has_production(&self, term: &Term, label: &Label) -> bool {
        term.metadata()
            .and_then(|metadata| metadata.production)
            .is_some()
            || !self
                .productions
                .productions_for(&LabelHead::from(label))
                .is_empty()
    }

    fn parametric_lub(&self, sorts: &[Sort], fallback: &Sort) -> Result<Sort, SortInjectionError> {
        let concrete = sorts
            .iter()
            .filter(|sort| sort.name != FrontendSort::SortParam.as_str())
            .cloned()
            .collect::<Vec<_>>();
        if concrete.is_empty() {
            return Ok(sorts.first().cloned().unwrap_or_else(|| fallback.clone()));
        }
        self.least_upper_bound(
            &concrete,
            (fallback.name != FrontendSort::SortParam.as_str()).then_some(fallback),
        )
    }

    /// Collect the bindings under which the parametric result sort `declared` is instantiated to
    /// `known` or a declared sort below it: the candidates for a parameter that occurs only in
    /// the result, which must fit its position of sort `known`.
    // Invariant: each `match_sort_below` to `match_sort_below_parameters` to `match_sort_below` round descends one level into `declared.parameters`, so the depth of `declared` bounds the recursion; `matches` accumulates, per formal parameter, every sort bound so far.
    fn match_sort_below(
        &self,
        formal_parameters: &[Sort],
        declared: &Sort,
        known: &Sort,
        matches: &mut BTreeMap<Sort, Vec<Sort>>,
    ) {
        if formal_parameters.contains(declared) {
            matches
                .entry(declared.clone())
                .or_default()
                .push(known.clone());
            return;
        }
        self.match_sort_below_parameters(formal_parameters, declared, known, matches);
        // Invariant: `matches` includes the bindings from `known` and from every declared sort strictly below `known` before `candidate` in `sorts.sorted_all_sorts()`; each candidate is visited once.
        for candidate in self.sorts.sorted_all_sorts() {
            if candidate != known && self.subsorts.less_than_eq(candidate, known) {
                self.match_sort_below_parameters(formal_parameters, declared, candidate, matches);
            }
        }
    }

    fn match_sort_below_parameters(
        &self,
        formal_parameters: &[Sort],
        declared: &Sort,
        known: &Sort,
        matches: &mut BTreeMap<Sort, Vec<Sort>>,
    ) {
        if same_head(declared, known) {
            for (declared, known) in declared.parameters.iter().zip(&known.parameters) {
                self.match_sort_below(formal_parameters, declared, known, matches);
            }
        }
    }

    fn production(&self, term: &Term, label: &Label) -> Result<&Sentence, SortInjectionError> {
        let mut invalid_resolved = None;
        if let Some(resolved) = term.metadata().and_then(|metadata| metadata.production) {
            if let Some(production_id) = self.productions.lookup(&resolved) {
                let production = self.productions.production(production_id);
                let Sentence::Production {
                    label: production_label,
                    ..
                } = production
                else {
                    unreachable!()
                };
                if production_label
                    .as_ref()
                    .is_some_and(|production_label| production_label.name == label.name)
                {
                    return Ok(production);
                }
                invalid_resolved = Some(SortInjectionError::InvalidResolvedProduction {
                    label: label.name.clone(),
                    production: resolved.to_hex(),
                    message: "the production belongs to a different KLabel".into(),
                });
            } else {
                invalid_resolved = Some(SortInjectionError::InvalidResolvedProduction {
                    label: label.name.clone(),
                    production: resolved.to_hex(),
                    message: "the active production catalog does not contain this identity".into(),
                });
            }
        }
        let ids = self.productions.productions_for(&LabelHead::from(label));
        if ids.len() > 1
            && let Some(sort) = term.metadata().and_then(|metadata| metadata.sort.as_ref())
        {
            let matching = ids
                .iter()
                .filter(|id| {
                    matches!(
                        self.productions.production(**id),
                        Sentence::Production { sort: result, .. } if result == sort
                    )
                })
                .collect::<Vec<_>>();
            if let [id] = matching.as_slice() {
                return Ok(self.productions.production(**id));
            }
        }
        match ids {
            [] => Err(invalid_resolved
                .unwrap_or_else(|| SortInjectionError::UnknownLabel(label.name.clone()))),
            [id] => Ok(self.productions.production(*id)),
            ids => Err(
                invalid_resolved.unwrap_or_else(|| SortInjectionError::AmbiguousLabel {
                    label: label.name.clone(),
                    productions: ids.len(),
                }),
            ),
        }
    }

    pub(crate) fn least_upper_bound(
        &self,
        sorts: &[Sort],
        expected: Option<&Sort>,
    ) -> Result<Sort, SortInjectionError> {
        let mut entries = sorts
            .iter()
            .filter(|sort| sort.name != FrontendSort::SortParam.as_str())
            .cloned()
            .collect::<Vec<_>>();
        if entries.is_empty() {
            return sorts
                .first()
                .cloned()
                .or_else(|| expected.cloned())
                .ok_or_else(|| SortInjectionError::IncompatibleSorts {
                    sorts: Vec::new(),
                    expected: expected.cloned(),
                });
        }
        entries.sort();
        entries.dedup();
        let minima = self.minimal_upper_bounds(&entries, expected);
        if minima.len() == 1 {
            Ok(minima.into_iter().next().expect("one minimum"))
        } else {
            Err(SortInjectionError::IncompatibleSorts {
                sorts: entries,
                expected: expected.cloned(),
            })
        }
    }

    /// The minimal upper bounds of the concrete `sorts` below `K` and above `KBott`, restricted to
    /// sorts at or below `expected` when it is a concrete nullary sort.
    fn minimal_upper_bounds(&self, sorts: &[Sort], expected: Option<&Sort>) -> BTreeSet<Sort> {
        let mut entries = sorts
            .iter()
            .filter(|sort| sort.name != FrontendSort::SortParam.as_str())
            .cloned()
            .collect::<Vec<_>>();
        entries.sort();
        entries.dedup();
        let non_parametric = entries
            .iter()
            .filter(|sort| {
                sort.parameters.is_empty()
                    || sort
                        .parameters
                        .iter()
                        .all(|parameter| self.sorts.all_sorts().contains(parameter))
            })
            .cloned()
            .collect::<Vec<_>>();
        let mut bounds = self.subsorts.upper_bounds(&non_parametric);
        if let [sort] = non_parametric.as_slice() {
            // A relation-free sort is absent from PartialOrder's element set, while Java's
            // upperBounds includes every supplied element itself.
            bounds.insert(sort.clone());
        }
        let k_bottom = Sort::frontend(FrontendSort::KBott);
        let k = Sort::builtin(BuiltinSort::K);
        bounds.retain(|bound| {
            !self.subsorts.less_than_eq(bound, &k_bottom) && !self.subsorts.greater_than(bound, &k)
        });
        if let Some(expected) = expected
            && expected.name != FrontendSort::SortParam.as_str()
            && expected.parameters.is_empty()
        {
            bounds.retain(|bound| self.subsorts.less_than_eq(bound, expected));
        }
        let parametric = entries
            .iter()
            .filter(|sort| !sort.parameters.is_empty())
            .collect::<Vec<_>>();
        // Invariant: a `bound` is kept only when every sort of `parametric` has an instantiation below it; the check costs O(|bounds| * the instantiations of the sorts in `parametric`).
        bounds.retain(|bound| {
            parametric.iter().all(|sort| {
                self.sorts
                    .instantiations()
                    .get(&SortHead::from(*sort))
                    .into_iter()
                    .flatten()
                    .any(|instance| self.subsorts.less_than_eq(instance, bound))
            })
        });
        self.subsorts.minimal(&bounds)
    }
}

#[derive(Clone, Debug)]
struct InstantiatedSignature {
    label: Label,
    arguments: Vec<Sort>,
    result: Sort,
}

pub fn add_sort_injections(
    definition: &Definition,
    module: &str,
    term: &Term,
) -> Result<Term, SortInjectionError> {
    let resolved =
        ResolvedDefinition::resolve(definition).map_err(SortInjectionError::Definition)?;
    add_sort_injections_from_resolved(&resolved, module, term)
}

/// Materialize sort injections across the compiled main module and its imports.
pub fn add_sort_injections_to_definition(
    definition: &Definition,
) -> Result<Definition, SortInjectionError> {
    super::pipeline::run_standalone(
        definition,
        add_sort_injections_to_definition_pass,
        Some(GeneratingPass::AddSortInjections),
    )
}

pub(crate) fn add_sort_injections_to_definition_pass(
    input: &super::pipeline::PassInput<'_>,
    _: &mut super::pipeline::PipelineState,
) -> Result<Definition, SortInjectionError> {
    let resolved = input
        .resolved_raw()
        .map_err(|error| SortInjectionError::Definition(error.clone()))?;
    let target = resolved.main_module_id();
    let target_modules = resolved
        .transitive_imports(target)
        .into_iter()
        .chain(std::iter::once(target))
        .collect::<BTreeSet<_>>();
    let views = resolved.views();
    let target_injector = SortInjector::with_views(&views, target)?;
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        if !target_modules.contains(&module_id) {
            continue;
        }
        for (sentence_index, sentence) in module.local_sentences.iter_mut().enumerate() {
            let injected = target_injector.inject_sentence(sentence).map_err(|error| {
                SortInjectionError::Sentence {
                    module: module.name.clone(),
                    sentence: sentence_index,
                    source: sentence.attributes().source().map(str::to_owned),
                    line: sentence
                        .attributes()
                        .location()
                        .map(|location| location.start_line),
                    error: Box::new(error),
                }
            })?;
            *crate::definition::sentence_mut(sentence) = injected;
        }
    }
    Ok(output)
}

pub fn add_sort_injections_from_resolved(
    definition: &ResolvedDefinition,
    module: &str,
    term: &Term,
) -> Result<Term, SortInjectionError> {
    SortInjector::new(definition, module)?.inject_at_top(term)
}

/// Whether `sort` is or contains a sort variable of a sentence or production.
fn mentions_sort_parameter(sort: &Sort) -> bool {
    sort.name == FrontendSort::SortParam.as_str()
        || sort.parameters.iter().any(mentions_sort_parameter)
}

/// Extend `binding` so that `declared`, with the sort parameters in `parameters` substituted, is
/// `concrete`; a parameter occurring twice must be bound to one sort. Returns whether it matched.
fn bind_parameters(
    parameters: &[Sort],
    declared: &Sort,
    concrete: &Sort,
    binding: &mut BTreeMap<Sort, Sort>,
) -> bool {
    if parameters.contains(declared) {
        return match binding.get(declared) {
            Some(bound) => bound == concrete,
            None => {
                binding.insert(declared.clone(), concrete.clone());
                true
            }
        };
    }
    same_head(declared, concrete)
        && declared
            .parameters
            .iter()
            .zip(&concrete.parameters)
            .all(|(declared, concrete)| bind_parameters(parameters, declared, concrete, binding))
}

/// Whether two sorts have the same head name and parameter count.
fn same_head(left: &Sort, right: &Sort) -> bool {
    left.name == right.name && left.parameters.len() == right.parameters.len()
}

/// A bounded rendering of a term for a sort diagnostic.
fn render_term(term: &Term) -> String {
    const LIMIT: usize = 200;
    let rendered = term.to_string();
    match rendered.char_indices().nth(LIMIT) {
        Some((end, _)) => format!("{}...", &rendered[..end]),
        None => rendered,
    }
}

fn injection(from: Sort, to: Sort, term: Term) -> Term {
    measure::bump(Counter::KompileInjectionsInserted);
    Term::Apply {
        label: Label::with_parameters(WellKnownSymbol::Inj.as_str(), vec![from, to]),
        arguments: vec![term],
    }
}

fn copy_metadata(source: &Term, term: Term) -> Term {
    if let Some(metadata) = source.metadata() {
        term.with_metadata(metadata.clone())
    } else {
        term
    }
}

fn substitute_sort(sort: &Sort, substitution: &BTreeMap<Sort, Sort>) -> Sort {
    substitution.get(sort).cloned().unwrap_or_else(|| {
        Sort::with_parameters(
            &sort.name,
            sort.parameters
                .iter()
                .map(|parameter| substitute_sort(parameter, substitution))
                .collect(),
        )
    })
}

fn contains_sort(sort: &Sort, needle: &Sort) -> bool {
    sort == needle
        || sort
            .parameters
            .iter()
            .any(|parameter| contains_sort(parameter, needle))
}

fn has_rewrite(term: &Term) -> bool {
    let mut found = false;
    term.visit_preorder(&mut |term| {
        found |= matches!(term, Term::Rewrite { .. });
    });
    found
}

// Invariant: each call projects one node of `term` and recurses only into its direct subterms, so the finite `term` bounds the calls; `right` selects the side kept at every rewrite.
pub(crate) fn rewrite_projection(term: &Term, right: bool) -> Term {
    match term.unannotated() {
        Term::Rewrite {
            left,
            right: rewrite_right,
        } => {
            if right {
                rewrite_projection(rewrite_right, true)
            } else {
                left.as_ref().clone()
            }
        }
        Term::Apply { label, arguments } => {
            let projected = Term::Apply {
                label: label.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| rewrite_projection(argument, right))
                    .collect(),
            };
            copy_metadata(term, compact_injections(projected))
        }
        Term::Sequence(items) => copy_metadata(
            term,
            Term::sequence(items.iter().map(|item| rewrite_projection(item, right))),
        ),
        Term::As { pattern, alias } => {
            if right {
                alias.as_ref().clone()
            } else {
                copy_metadata(
                    term,
                    Term::As {
                        pattern: Box::new(rewrite_projection(pattern, false)),
                        alias: alias.clone(),
                    },
                )
            }
        }
        _ => term.clone(),
    }
}

fn compact_injections(term: Term) -> Term {
    let Term::Apply { label, arguments } = term.unannotated() else {
        return term;
    };
    let [outer_from, outer_to] = label.parameters.as_slice() else {
        return term;
    };
    let [argument] = arguments.as_slice() else {
        return term;
    };
    let Term::Apply {
        label: inner_label,
        arguments: inner_arguments,
    } = argument.unannotated()
    else {
        return term;
    };
    let [inner_from, inner_to] = inner_label.parameters.as_slice() else {
        return term;
    };
    if !label.is(WellKnownSymbol::Inj)
        || !inner_label.is(WellKnownSymbol::Inj)
        || inner_to != outer_from
    {
        return term;
    }
    Term::Apply {
        label: Label::with_parameters(
            WellKnownSymbol::Inj.as_str(),
            vec![inner_from.clone(), outer_to.clone()],
        ),
        arguments: inner_arguments.clone(),
    }
}

fn with_variable_sort(term: &Term, sort: &Sort) -> Term {
    match term.unannotated() {
        Term::Variable { name, .. } => copy_metadata(
            term,
            Term::Variable {
                name: name.clone(),
                sort: Some(sort.clone()),
            },
        ),
        _ => term.clone(),
    }
}

/// Wrap a downcast term in the runtime projection generated for its cast target.
///
/// The argument keeps its metadata except the cast sort, so it sorts as its production's natural
/// result sort and is not projected again.
fn semantic_projection(term: &Term, target: &Sort) -> Term {
    let mut argument = term.clone().into_unannotated();
    if let Some(metadata) = term.metadata() {
        let mut metadata = metadata.clone();
        metadata.sort = None;
        argument = argument.with_metadata(metadata);
    }
    Term::Apply {
        label: Label::projection(target),
        arguments: vec![argument],
    }
}
