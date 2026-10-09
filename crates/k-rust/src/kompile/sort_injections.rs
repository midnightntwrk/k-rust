//! ```toml algorithm
//! id = "kompile.sort_injections.insert"
//! name = "sort inference and explicit injection insertion"
//! sites = ["SortInjector::inject_sentence", "SortInjector::term_sort_with_arity", "SortInjector::sort_and_downcast", "SortInjector::solve_parameters", "add_sort_injections_to_definition"]
//! variable = "N = term nodes; P = production candidates; S = cost of the subsort queries of one node outside an instance search, each costing B; B = cost of one subsort query: closure lookups, O(log s), except a parser sort placed at KItem or above, which scans its supersorts, O(s log s), and an injection into a sort above K, which searches the declared subsort edges, O(s x e); s = declared sorts; e = declared subsort edges; a = arguments of one parametric application; c = candidate values of one sort parameter, at most O(s); g = sort parameters in one connected group of that application (parameters that share a declared argument or result sort); m = incomparable minimal assignments retained for a group, at most c^g"
//! counters = ["KompileInjectionsInserted"]
//!
//! [[cost]]
//! mode = "one sentence, excluding the instance search of each parametric application"
//! bound = "O(N x (P + S))"
//!
//! [[cost]]
//! mode = "instance search of one parametric application (SortInjector::solve_parameters)"
//! bound = "O(a x s x B + sum over groups of c^g x a x (m + 1) x B)"
//! ```
//!
//! Sort injection computes expected sorts, least upper bounds, and explicit KORE injections, with strict rebase-in and lossy localization-out metadata policies.
//! Work is O(term nodes times production and subsort queries), each node's natural sort being inferred once per expected sort within one injection (`NaturalSorts`), plus, for each application of a parametric production, an instance search: the candidate values of each sort parameter are gathered by scanning the declared sorts per argument, and every assignment in the product of the candidate sets of each connected group of parameters is checked against the group's constraints, keeping the pointwise-least ones; the search is exponential in the size of a connected group, not in the number of parameters.
//! `KompileInjectionsInserted` measures its variable work, and the shared pass scaffolding counts resolutions and copied sentences.
//!
//! Production-aware insertion of explicit KORE subsort injections.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use k_rust_kore::measure::{self, Counter};

use crate::definition::checks::{LabelParameterError, SentenceLabelParameterError};
use crate::definition::configuration::cell_map_key_label;
use crate::definition::production_kind::{NoJunk, ProductionKind, ResultSorts};
use crate::definition::{
    AttributeKey, Definition, DefinitionViews, LabelHead, ModuleId, PartialOrder,
    ProductionCatalog, ResolveError, ResolvedDefinition, Sentence, SortCatalog, SortHead,
};
use crate::kast::{FrontendSort, InternalLabel, Label, Sort, Term};
use crate::names::{BuiltinSort, WellKnownSymbol};
use crate::provenance::GeneratingPass;

use super::passes::{ExpandedProgram, Injectable, Placement, PlacementKind, placeable};

mod typing;
use super::view::View;
pub use typing::{
    BranchTyping, PathMap, PathTrie, PositionTyping, SentenceTyper, SentenceTyping,
    SentenceTypingError, sentence_typing,
};

mod sentence_variables {
    use super::*;
    use crate::definition::ProductionItem;

    /// The sort variables an injected sentence quantifies over.
    /// Each is a whole sort argument of a matching-logic connective: the sort of a predicate,
    /// which is the whole carrier or empty at every sort alike, so it chooses nothing and the
    /// sentence binds it. Only `SortInjector::sentence_sort_variables` exposes a nonempty set.
    #[derive(Clone, Debug, Default, Eq, PartialEq)]
    pub struct SentenceSortVariables {
        names: BTreeSet<String>,
    }

    impl SentenceSortVariables {
        pub fn names(&self) -> impl Iterator<Item = &str> {
            self.names.iter().map(String::as_str)
        }

        pub fn is_empty(&self) -> bool {
            self.names.is_empty()
        }

        pub(crate) fn contains(&self, name: &str) -> bool {
            self.names.contains(name)
        }

        pub(crate) fn union(&self, other: &Self) -> Self {
            Self {
                names: self.names.union(&other.names).cloned().collect(),
            }
        }
    }

    struct Offender {
        term: String,
        variable: Sort,
        cause: UndeterminedCause,
    }

    impl SortInjector<'_, '_> {
        pub(crate) fn sentence_sort_variables<'t>(
            &self,
            terms: impl IntoIterator<Item = &'t Term>,
        ) -> Result<SentenceSortVariables, SortInjectionError> {
            self.classify(terms).map_err(|offender| {
                SortInjectionError::UndeterminedInstance(Box::new(UndeterminedInstance {
                    term: offender.term,
                    variable: offender.variable,
                    site: UndeterminedSite::Sentence(offender.cause),
                }))
            })
        }

        fn classify<'t>(
            &self,
            terms: impl IntoIterator<Item = &'t Term>,
        ) -> Result<SentenceSortVariables, Box<Offender>> {
            let mut variables = SentenceSortVariables::default();
            let mut injection = None;
            let mut leaf = None;
            for term in terms {
                self.classify_sentence_sort_variables(
                    term,
                    &mut variables,
                    &mut injection,
                    &mut leaf,
                )?;
            }
            if let Some(offender) = injection.or(leaf) {
                Err(Box::new(offender))
            } else {
                Ok(variables)
            }
        }

        /// Require an injected ground term to contain no sort variable, even at a
        /// predicate sort: a ground value binds no sort variable.
        pub(crate) fn require_ground(
            &self,
            term: &Term,
            input: GroundInput,
        ) -> Result<(), SortInjectionError> {
            let variables = self.classify([term]).map_err(|offender| {
                SortInjectionError::UndeterminedInstance(Box::new(UndeterminedInstance {
                    term: offender.term,
                    variable: offender.variable,
                    site: UndeterminedSite::Ground {
                        input,
                        cause: GroundCause::Instance(offender.cause),
                    },
                }))
            })?;
            if variables.is_empty() {
                return Ok(());
            }
            // Classification has rejected every occurrence except whole predicate sorts.
            // Report the first remaining occurrence on the connective that carries it.
            let mut offender = None;
            term.visit_preorder(&mut |term| {
                if offender.is_none()
                    && let Term::Apply { label, .. } = term
                    && let Some(variable) = label
                        .parameters
                        .iter()
                        .find(|sort| sort.is_rigid_variable())
                {
                    offender = Some(UndeterminedInstance {
                        term: render_term(term),
                        variable: variable.clone(),
                        site: UndeterminedSite::Ground {
                            input,
                            cause: GroundCause::PredicateSort {
                                label: label.name.clone(),
                            },
                        },
                    });
                }
            });
            Err(SortInjectionError::UndeterminedInstance(Box::new(
                offender.expect("a nonempty sentence binder has a predicate-sort occurrence"),
            )))
        }

        // Invariant: each recursive call descends into a direct subterm, so term depth bounds recursion. The walk returns the first non-injection label offender in pre-order, retaining the first injection and leaf only as fallbacks.
        #[deny(clippy::wildcard_enum_match_arm)]
        fn classify_sentence_sort_variables(
            &self,
            term: &Term,
            variables: &mut SentenceSortVariables,
            injection: &mut Option<Offender>,
            leaf: &mut Option<Offender>,
        ) -> Result<(), Box<Offender>> {
            crate::stack::guarded(|| self.classify_level(term, variables, injection, leaf))
        }

        /// One level of [`Self::classify_sentence_sort_variables`], which runs it with stack
        /// for one more level.
        #[deny(clippy::wildcard_enum_match_arm)]
        fn classify_level(
            &self,
            term: &Term,
            variables: &mut SentenceSortVariables,
            injection: &mut Option<Offender>,
            leaf: &mut Option<Offender>,
        ) -> Result<(), Box<Offender>> {
            match term.unannotated() {
                Term::Apply { label, .. } | Term::InjectedLabel(label) => {
                    for (index, parameter) in label.parameters.iter().enumerate() {
                        let Some(variable) = first_sort_variable(parameter) else {
                            continue;
                        };
                        if matches!(term.unannotated(), Term::Apply { .. })
                            && InternalLabel::MATCHING_LOGIC
                                .iter()
                                .any(|builtin| label.is(*builtin))
                            && parameter.is_rigid_variable()
                            && let [name] = parameter.parameters.as_slice()
                            && name.parameters.is_empty()
                        {
                            variables.names.insert(name.name.clone());
                            continue;
                        }
                        let (formal, phantom) = match self.production(term, label).ok() {
                            Some(Sentence::Production {
                                parameters,
                                sort,
                                items,
                                ..
                            }) => {
                                let formal = parameters.get(index);
                                let phantom = formal.is_some_and(|formal| {
                                    !contains_sort(sort, formal)
                                        && !items.iter().any(|item| {
                                            matches!(item,
                                            ProductionItem::NonTerminal { sort, .. }
                                                if contains_sort(sort, formal))
                                        })
                                });
                                (formal.cloned(), phantom)
                            }
                            Some(
                                Sentence::SyntaxSort { .. }
                                | Sentence::SortSynonym { .. }
                                | Sentence::SyntaxLexical { .. }
                                | Sentence::SyntaxAssociativity { .. }
                                | Sentence::SyntaxPriority { .. }
                                | Sentence::ContextAlias { .. }
                                | Sentence::Context { .. }
                                | Sentence::Configuration { .. }
                                | Sentence::Bubble { .. }
                                | Sentence::Rule { .. }
                                | Sentence::Claim { .. },
                            )
                            | None => (None, false),
                        };
                        let cause = match (formal, phantom) {
                            (Some(parameter), true) => UndeterminedCause::Phantom {
                                label: label.name.clone(),
                                parameter,
                            },
                            (Some(parameter), false) => UndeterminedCause::Open {
                                label: label.name.clone(),
                                parameter,
                            },
                            (None, true | false) => UndeterminedCause::Unattributed {
                                label: Some(label.name.clone()),
                            },
                        };
                        let offender = Offender {
                            term: render_term(term),
                            variable: variable.clone(),
                            cause,
                        };
                        if label.is(WellKnownSymbol::Inj) {
                            injection.get_or_insert(offender);
                        } else {
                            return Err(Box::new(offender));
                        }
                    }
                    if let Term::Apply { arguments, .. } = term.unannotated() {
                        for argument in arguments {
                            self.classify_sentence_sort_variables(
                                argument, variables, injection, leaf,
                            )?;
                        }
                    }
                }
                Term::Variable {
                    sort: Some(sort), ..
                }
                | Term::Token { sort, .. } => {
                    if let Some(variable) = first_sort_variable(sort) {
                        leaf.get_or_insert_with(|| Offender {
                            term: render_term(term),
                            variable: variable.clone(),
                            cause: UndeterminedCause::Unattributed { label: None },
                        });
                    }
                }
                Term::Rewrite { left, right } => {
                    self.classify_sentence_sort_variables(left, variables, injection, leaf)?;
                    self.classify_sentence_sort_variables(right, variables, injection, leaf)?;
                }
                Term::As { pattern, alias } => {
                    self.classify_sentence_sort_variables(pattern, variables, injection, leaf)?;
                    self.classify_sentence_sort_variables(alias, variables, injection, leaf)?;
                }
                Term::Sequence(items) => {
                    for item in items {
                        self.classify_sentence_sort_variables(item, variables, injection, leaf)?;
                    }
                }
                Term::Annotated { term, .. } => {
                    self.classify_sentence_sort_variables(term, variables, injection, leaf)?;
                }
                Term::Variable { sort: None, .. } => {}
            }
            Ok(())
        }
    }

    // Invariant: each recursive call descends into a direct sort parameter, so sort depth bounds recursion.
    fn first_sort_variable(sort: &Sort) -> Option<&Sort> {
        if sort.is_rigid_variable() {
            Some(sort)
        } else {
            sort.parameters.iter().find_map(first_sort_variable)
        }
    }
}

pub use sentence_variables::SentenceSortVariables;

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
        origin: Option<crate::provenance::GeneratingPass>,
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
    /// A semantic cast whose target (`required`) is strictly below the operand's sort (`found`),
    /// so it is a downcast, and whose target has no sort projection: no K term has that sort, so
    /// no projection can read the operand as one.
    DowncastWithoutProjection(Box<SortMismatch>),
    /// A parametric production whose arguments fit several incomparable least instantiations,
    /// so no instantiation fits them most tightly.
    AmbiguousInstance(Box<AmbiguousInstance>),
    /// An application instance or term sort that no argument, position or cast determined.
    UndeterminedInstance(Box<UndeterminedInstance>),
    /// A value-building schema instance at a sort whose hook or domain values fix its values.
    InstanceAtFixedSort(Box<InstanceAtFixedSort>),
    /// A label of a loaded rule-like sentence that carries sort parameters. Sort injection
    /// instantiates every parametric label from its arguments and position, so a written
    /// instance would be re-solved rather than placed; it is rejected instead.
    LabelParameters {
        label: String,
        parameters: Vec<Sort>,
    },
}

impl SortInjectionError {
    /// The public shape of a label rejected by
    /// [`reject_label_parameters`](crate::definition::checks::reject_label_parameters).
    pub(crate) fn label_parameters(error: LabelParameterError) -> Self {
        Self::LabelParameters {
            label: error.label,
            parameters: error.parameters,
        }
    }

    /// The public shape of a sentence rejected by
    /// [`reject_label_parameters_in_definition`](
    ///     crate::definition::checks::reject_label_parameters_in_definition).
    pub(crate) fn sentence_label_parameters(error: SentenceLabelParameterError) -> Self {
        Self::Sentence {
            module: error.module,
            sentence: error.sentence,
            source: error.source,
            line: error.location.map(|location| location.start_line),
            origin: error.origin,
            error: Box::new(Self::label_parameters(*error.error)),
        }
    }
}

/// A parametric production's arguments with several incomparable least instantiations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AmbiguousInstance {
    /// The declared argument sorts involved, with their sort parameters.
    pub declared: Vec<Sort>,
    /// The sorts of the corresponding arguments.
    pub arguments: Vec<Sort>,
    /// The declared result sort and the position's sort, when the ambiguous parameters include
    /// one that occurs in no argument: the instantiated result is then ordered as well, and it is
    /// the last sort of each candidate.
    pub position: Option<(Sort, Sort)>,
    /// Declared argument sorts under representative minimal instantiations. When independent
    /// parameter groups are ambiguous, these vary one group while fixing the others.
    pub candidates: Vec<Vec<Sort>>,
}

/// A value-building schema application that adds its own root to a sort with fixed values.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InstanceAtFixedSort {
    /// The offending application, rendered for the diagnostic.
    pub term: String,
    /// The label whose result sort is its own sort parameter.
    pub label: String,
    /// The fixed sort of the instance.
    pub sort: Sort,
}

/// A sort variable left where it must not stay, with where it was found and why nothing fixed it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UndeterminedInstance {
    /// The offending application or leaf, rendered for the diagnostic.
    pub term: String,
    /// The sort variable sort injection left in it.
    pub variable: Sort,
    pub site: UndeterminedSite,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UndeterminedSite {
    /// A rule, claim, equation or macro: its binder may quantify only a predicate's sort.
    Sentence(UndeterminedCause),
    /// A value without a binder, read by `input`'s grammar.
    Ground {
        input: GroundInput,
        cause: GroundCause,
    },
}

/// What parsed a ground value, which decides whether its text can hold a sort cast.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GroundInput {
    /// A program or configuration value: the definition's syntax, which has no sort casts.
    Value,
    /// A search pattern: rule content, which has sort casts.
    SearchPattern,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GroundCause {
    /// An application instance or leaf sort that classification found undetermined.
    Instance(UndeterminedCause),
    /// A matching-logic connective's sort: a sentence would bind it, a ground value cannot.
    PredicateSort { label: String },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UndeterminedCause {
    /// `parameter` occurs in neither the argument sorts nor the result sort of `label`'s
    /// production: no application determines it and no cast fixes it.
    Phantom { label: String, parameter: Sort },
    /// `parameter` occurs in the production's sorts, and neither the arguments nor the
    /// position fixed it.
    Open { label: String, parameter: Sort },
    /// An `inj`, a label whose production is unknown, or a variable's or token's sort.
    Unattributed { label: Option<String> },
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
    #[deny(clippy::wildcard_enum_match_arm)]
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
                origin,
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
                if let Some(origin) = origin {
                    write!(formatter, "(origin: {}) ", origin.as_str())?;
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
            Self::LabelParameters { label, parameters } => write!(
                formatter,
                "KLabel {label:?} carries the sort parameters {{{}}}; label sort parameters are inferred from the arguments and the position: remove them, or use a cast to fix an instance",
                parameters
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
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
            Self::DowncastWithoutProjection(mismatch) => write!(
                formatter,
                "semantic cast of {} to sort {} is a downcast from {}, and {} has no sort projection",
                mismatch.term, mismatch.required, mismatch.found, mismatch.required
            ),
            Self::InstanceAtFixedSort(instance) => write!(
                formatter,
                "the instance of `{label}` in `{term}` is at sort {sort}, whose values its hook or its domain values fix; the result sort of `{label}` is its own sort parameter, so its applications are values with their own root at the instance sort, and none is a value of {sort}",
                label = instance.label,
                term = instance.term,
                sort = instance.sort,
            ),
            Self::UndeterminedInstance(instance) => {
                let (input, cause) = match &instance.site {
                    UndeterminedSite::Sentence(cause) => (None, cause),
                    UndeterminedSite::Ground {
                        input,
                        cause: GroundCause::Instance(cause),
                    } => (Some(*input), cause),
                    UndeterminedSite::Ground {
                        input,
                        cause: GroundCause::PredicateSort { label },
                    } => {
                        write!(
                            formatter,
                            "the sort of `{label}` in `{}` is not determined; a ground value binds no sort variable, so even a predicate's sort must be determined",
                            instance.term
                        )?;
                        return match input {
                            GroundInput::Value => Ok(()),
                            GroundInput::SearchPattern => {
                                write!(formatter, ", so add a sort cast that fixes it")
                            }
                        };
                    }
                };
                match cause {
                    UndeterminedCause::Phantom { label, parameter }
                    | UndeterminedCause::Open { label, parameter } => write!(
                        formatter,
                        "the instance of `{label}` in `{}` is not determined: its sort parameter {parameter} ",
                        instance.term
                    )?,
                    UndeterminedCause::Unattributed { label: Some(label) } => write!(
                        formatter,
                        "the instance of `{label}` in `{}` is not determined: ",
                        instance.term
                    )?,
                    UndeterminedCause::Unattributed { label: None } => write!(
                        formatter,
                        "term `{}` has an undetermined sort: ",
                        instance.term
                    )?,
                }
                match (input, cause) {
                    (
                        None | Some(GroundInput::Value | GroundInput::SearchPattern),
                        UndeterminedCause::Phantom { label, parameter },
                    ) => write!(
                        formatter,
                        "occurs in neither its argument sorts nor its result sort, so no application of `{label}` determines it and no sort cast can fix it; `{label}` can be used in no rule, claim, program, configuration value or search pattern unless its declaration drops {parameter} or uses it in an argument or the result sort"
                    ),
                    (None, UndeterminedCause::Open { .. }) => write!(
                        formatter,
                        "is fixed neither by its arguments nor by its position, so sort injection left the sentence sort variable {} in it, and only the sort of a predicate may stay a sort variable; add a sort cast that fixes it",
                        instance.variable
                    ),
                    (None, UndeterminedCause::Unattributed { .. }) => write!(
                        formatter,
                        "it contains the sentence sort variable {}, and only the sort of a predicate may stay a sort variable; add a sort cast that fixes it",
                        instance.variable
                    ),
                    (Some(GroundInput::Value), UndeterminedCause::Open { .. }) => write!(
                        formatter,
                        "is fixed neither by its arguments nor by the sort the value is read at; a program or configuration value binds no sort variable and its syntax has no sort casts, so every instance must follow from its arguments and the sort it is read at"
                    ),
                    (Some(GroundInput::Value), UndeterminedCause::Unattributed { .. }) => write!(
                        formatter,
                        "it contains the sort variable {}; a program or configuration value binds no sort variable and its syntax has no sort casts, so every instance must follow from its arguments and the sort it is read at",
                        instance.variable
                    ),
                    (Some(GroundInput::SearchPattern), UndeterminedCause::Open { .. }) => write!(
                        formatter,
                        "is fixed neither by its arguments nor by its position; a search pattern binds no sort variable, so add a sort cast that fixes it"
                    ),
                    (Some(GroundInput::SearchPattern), UndeterminedCause::Unattributed { .. }) => {
                        write!(
                            formatter,
                            "it contains the sort variable {}; a search pattern binds no sort variable, so add a sort cast that fixes it",
                            instance.variable
                        )
                    }
                }
            }
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
                    "arguments of sorts ({}) fit ({}){} at several incomparable least instantiations: {}",
                    list(&ambiguity.arguments),
                    list(&ambiguity.declared),
                    ambiguity
                        .position
                        .as_ref()
                        .map(|(result, position)| format!(
                            " and the position {position} fits the result {result}"
                        ))
                        .unwrap_or_default(),
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
    /// The natural sorts inferred in the current memoized call ([`Self::memoized`]).
    natural_sorts: RefCell<NaturalSorts>,
}

/// The natural sorts the injector inferred during one call, by node.
///
/// The natural sort of a node under an expected sort is a function of the node and that sort,
/// the injector's views being immutable, unless its inference draws a fresh sort parameter. A
/// parametric production's sort depends on its arguments' sorts, so inferring it walks the
/// node's whole subtree, and injection infers the sort of every node again, from the top and
/// from each level down: a chain of a parametric production was injected in time quadratic in
/// its depth. Recording each nontrivial inference makes it once per node and expected sort.
///
/// A node is identified by its address, which is sound only while the nodes recorded live and
/// stay in place: the memo is active only inside [`SortInjector::memoized`], whose callers
/// borrow the terms they pass for the whole call, it is cleared when the outermost such call
/// ends, and it is suspended ([`SortInjector::unmemoized`]) while a term built during the call
/// is inferred, since such a term may be dropped and its address reused before the call ends.
#[derive(Clone, Debug, Default)]
struct NaturalSorts {
    /// The memoized calls in progress; the memo is active while this is positive.
    depth: usize,
    /// The suspensions in progress; the memo is used only while this is zero.
    suspended: usize,
    /// The natural sort of each recorded node, by its address, expected sort and arity mode.
    sorts: BTreeMap<(usize, Option<Sort>, bool), Sort>,
    /// The natural sorts inferred so far, to tell an inference that walked a subtree.
    inferences: usize,
}

/// An inference that made at most this many inferences below its node is not recorded: it
/// costs about what a lookup does, and recording every node would only fill the memo.
const RECORDED_INFERENCES: usize = 4;

/// Leaves a memoized call or a suspension when dropped, also on unwinding.
struct NaturalSortsScope<'a> {
    natural_sorts: &'a RefCell<NaturalSorts>,
    suspension: bool,
}

impl Drop for NaturalSortsScope<'_> {
    fn drop(&mut self) {
        let mut natural_sorts = self.natural_sorts.borrow_mut();
        if self.suspension {
            natural_sorts.suspended -= 1;
        } else {
            natural_sorts.depth -= 1;
            if natural_sorts.depth == 0 {
                natural_sorts.sorts.clear();
            }
        }
    }
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
            natural_sorts: RefCell::default(),
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
            natural_sorts: RefCell::default(),
        })
    }

    /// Run `work` with the natural-sort memo active ([`NaturalSorts`]). Every term `work`
    /// infers sorts of must stay alive and in place until `work` returns, except terms it
    /// builds itself, which it infers inside [`Self::unmemoized`].
    pub(crate) fn memoized<T>(&self, work: impl FnOnce() -> T) -> T {
        self.natural_sorts.borrow_mut().depth += 1;
        let _scope = NaturalSortsScope {
            natural_sorts: &self.natural_sorts,
            suspension: false,
        };
        work()
    }

    /// Run `work` with the natural-sort memo suspended, for a term built during a memoized
    /// call, which may not live until it ends.
    pub(crate) fn unmemoized<T>(&self, work: impl FnOnce() -> T) -> T {
        self.natural_sorts.borrow_mut().suspended += 1;
        let _scope = NaturalSortsScope {
            natural_sorts: &self.natural_sorts,
            suspension: true,
        };
        work()
    }

    /// Add injections to a standalone term in the supplied top-level sort.
    pub fn inject(&self, term: &Term, expected: &Sort) -> Result<Term, SortInjectionError> {
        self.memoized(|| self.inject_with_position(term, expected, false))
    }

    /// Infer a standalone term's top sort and add every injection below it.
    pub fn inject_at_top(&self, term: &Term) -> Result<Term, SortInjectionError> {
        self.memoized(|| {
            let top = self.term_sort(term, None)?;
            self.inject_with_position(term, &top, false)
        })
    }

    /// Instantiate an expanded value at its carried position and reject any remaining sentence variable.
    /// The position decides only parameters nothing else fixes: `solve_parameters` accepts
    /// the instance fixed by the arguments whenever it fits the position.
    pub(crate) fn inject_ground(
        &self,
        value: &ExpandedProgram,
    ) -> Result<(Term, Sort), SortInjectionError> {
        let term = value.term();
        let position = value.position();
        let (injected, sort) = self.memoized(|| {
            let sort = self.term_sort(term, Some(position))?;
            Ok::<_, SortInjectionError>((self.inject_with_position(term, &sort, false)?, sort))
        })?;
        self.require_ground(&injected, GroundInput::Value)?;
        Ok((injected, sort))
    }

    pub(crate) fn is_user_list_sort(&self, sort: &Sort) -> bool {
        self.sorts.list_sorts().contains(sort)
    }

    /// Restart the fresh sort parameter counter at zero, as for a new sentence.
    pub(crate) fn reset_sort_parameters(&self) {
        self.next_sort_parameter.set(0);
    }

    /// Add sort injections to a sentence; rule and claim conditions have sort `Bool`.
    pub fn inject_sentence(&self, sentence: &Sentence) -> Result<Sentence, SortInjectionError> {
        self.inject_sentence_bound(sentence)
            .map(|(sentence, _)| sentence)
    }

    /// Inject and classify the predicate sort variables the sentence must bind.
    #[deny(clippy::wildcard_enum_match_arm)]
    pub(crate) fn inject_sentence_bound(
        &self,
        sentence: &Sentence,
    ) -> Result<(Sentence, SentenceSortVariables), SortInjectionError> {
        self.reset_sort_parameters();
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
                let variables = self.sentence_sort_variables([&body, &requires, &ensures])?;
                Ok((
                    Sentence::Rule {
                        body,
                        requires,
                        ensures,
                        attributes: attributes.clone(),
                    },
                    variables,
                ))
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
                let variables = self.sentence_sort_variables([&body, &requires, &ensures])?;
                Ok((
                    Sentence::Claim {
                        body,
                        requires,
                        ensures,
                        attributes: attributes.clone(),
                    },
                    variables,
                ))
            }
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => Ok((sentence.clone(), SentenceSortVariables::default())),
        }
    }

    fn inject_rule_body(&self, body: &Term) -> Result<Term, SortInjectionError> {
        let body = if has_rewrite(body) {
            Term::Rewrite {
                left: Box::new(rewrite_projection(body, false, &self.subsorts)),
                right: Box::new(rewrite_projection(body, true, &self.subsorts)),
            }
        } else {
            body.clone()
        };
        let top = self.fresh_sort_parameter();
        self.memoized(|| {
            let actual = self.term_sort(&body, Some(&top))?;
            self.inject_with_position(&body, &actual, false)
        })
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
    /// An authored cell still carries its dots and aggregate child beyond the nonterminals its
    /// production declares. They are cell notation, not arguments, and a term's sort is its
    /// production's result, so this entry point infers from the declared nonterminal prefix
    /// and ignores trailing syntax children. GuardOrPatterns runs at that stage. Missing
    /// declared children and every other inference error remain errors.
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

    /// Infer a term's sort together with the projection the injector applies to it for a downcast.
    ///
    /// A semantic cast on an application or token whose target is at or above the selected
    /// production's result sort records the intended overload/context, not a replacement for that
    /// result sort: `{P}:K` where `P:KItem` must still materialize the KItem-to-K sequence wrapper,
    /// and an exact-sort cast needs nothing. A target strictly below the result sort is a
    /// downcast: the injector replaces the term by `project:<target>(term)`, whose declared result
    /// sort is `target`, so `target` is the sort of the term the sentence contains and the second
    /// component is `Some` of that projection's label. Every enclosing inference must see that
    /// sort. A downcast to a sort without a sort projection is rejected as
    /// [`SortInjectionError::DowncastWithoutProjection`]: no K term has that sort, so no
    /// projection reads the operand as one.
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
    ) -> Result<(Sort, Option<Label>), SortInjectionError> {
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
                match Label::projection(target) {
                    Some(projection) => Ok((target.clone(), Some(projection))),
                    None => Err(SortInjectionError::DowncastWithoutProjection(Box::new(
                        SortMismatch {
                            term: render_term(term),
                            found: natural,
                            required: target.clone(),
                        },
                    ))),
                }
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
    /// While constructing an instance, this relation admits a sort such as
    /// `MInt{#SortParam{Q}}` below `KItem`. A sentence retaining that sort outside a whole
    /// predicate-sort argument is rejected after injection, so the emitted theory never
    /// needs a subsort axiom for it.
    fn below(&self, actual: &Sort, expected: &Sort) -> bool {
        placeable(actual, expected, &self.subsorts)
    }

    /// The witness for a single `inj{actual, expected}` under the module's order
    /// ([`Injectable::between`]); `None` when the sorts are equal or no injection is justified.
    fn witness(&self, actual: &Sort, expected: &Sort) -> Option<Injectable> {
        Injectable::between(actual, expected, &self.subsorts)
    }

    fn apply_placement(&self, plan: Placement, term: Term) -> Term {
        let count = match plan.kind() {
            PlacementKind::Identity => 0,
            PlacementKind::Injection(_) => 1,
            PlacementKind::SingletonK { item } => usize::from(item.is_some()),
            PlacementKind::SingletonKInjection { item, .. } => 1 + usize::from(item.is_some()),
        };
        for _ in 0..count {
            measure::bump(Counter::KompileInjectionsInserted);
        }
        plan.apply(term)
    }

    /// Select an outer placement without retyping the supplied value's children.
    pub(crate) fn placement(&self, actual: &Sort, expected: &Sort) -> Option<Placement> {
        Placement::between(actual, expected, &self.subsorts)
    }

    pub(crate) fn injection_witness(&self, actual: &Sort, expected: &Sort) -> Option<Injectable> {
        self.witness(actual, expected)
    }

    fn retained_injection(
        &self,
        term: &Term,
        label: &Label,
        arguments: &[Term],
    ) -> Result<Injectable, SortInjectionError> {
        let [source, target] = label.parameters.as_slice() else {
            return Err(SortInjectionError::MissingParameters {
                label: label.name.clone(),
                expected: 2,
                actual: label.parameters.len(),
            });
        };
        let [operand] = arguments else {
            return Err(SortInjectionError::InvalidArity {
                label: label.name.clone(),
                expected: 1,
                actual: arguments.len(),
            });
        };
        let actual = self.term_sort(operand, Some(source))?;
        if actual != *source {
            return Err(SortInjectionError::IllSortedTerm(Box::new(SortMismatch {
                term: render_term(operand),
                found: actual,
                required: source.clone(),
            })));
        }
        self.required_witness(term, source, target)
    }

    /// The witness for placing `term` of sort `actual` at a position of sort `expected` by one
    /// injection, or the rejection of the term there.
    fn required_witness(
        &self,
        term: &Term,
        actual: &Sort,
        expected: &Sort,
    ) -> Result<Injectable, SortInjectionError> {
        self.witness(actual, expected).ok_or_else(|| {
            SortInjectionError::IllSortedTerm(Box::new(SortMismatch {
                term: render_term(term),
                found: actual.clone(),
                required: expected.clone(),
            }))
        })
    }

    // Invariant: each recursive call (through `term_sort_with_arity` and `sort_and_downcast`, which call `natural_sort` once on the same term) descends into a direct subterm of `term` (a rewrite side, an `as` pattern or alias, or one argument of a sort-transparent application), so the depth of `term` bounds the recursion.
    fn natural_sort(
        &self,
        term: &Term,
        expected: Option<&Sort>,
        allow_trailing_arguments: bool,
    ) -> Result<Sort, SortInjectionError> {
        let key = {
            let mut natural_sorts = self.natural_sorts.borrow_mut();
            natural_sorts.inferences += 1;
            (natural_sorts.depth > 0 && natural_sorts.suspended == 0).then(|| {
                (
                    std::ptr::from_ref(term) as usize,
                    expected.cloned(),
                    allow_trailing_arguments,
                )
            })
        };
        if let Some(key) = &key
            && let Some(sort) = self.natural_sorts.borrow().sorts.get(key)
        {
            return Ok(sort.clone());
        }
        let (inferences, parameters) = (
            self.natural_sorts.borrow().inferences,
            self.next_sort_parameter.get(),
        );
        let sort = crate::stack::guarded(|| {
            self.natural_sort_level(term, expected, allow_trailing_arguments)
        })?;
        let mut natural_sorts = self.natural_sorts.borrow_mut();
        if let Some(key) = key
            && natural_sorts.inferences - inferences > RECORDED_INFERENCES
            && self.next_sort_parameter.get() == parameters
        {
            natural_sorts.sorts.insert(key, sort.clone());
        }
        Ok(sort)
    }

    /// One level of [`Self::natural_sort`], which runs it with stack for one more level.
    fn natural_sort_level(
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
                    return Ok(self
                        .retained_injection(term, label, arguments)?
                        .target()
                        .clone());
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
        crate::stack::guarded(|| self.inject_level(term, expected, is_lhs))
    }

    /// One level of [`Self::inject_with_position`], which runs it with stack for one more level.
    fn inject_level(
        &self,
        term: &Term,
        expected: &Sort,
        is_lhs: bool,
    ) -> Result<Term, SortInjectionError> {
        let (actual, downcast) = self.sort_and_downcast(term, Some(expected), false)?;
        if let Some(projection) = downcast {
            let projected = semantic_projection(term, projection);
            return self.unmemoized(|| self.inject_with_position(&projected, expected, is_lhs));
        }
        if actual == *expected {
            return self.visit_children(term, &actual, is_lhs);
        }

        let visited = self.visit_children(term, &actual, is_lhs)?;
        if expected.is_builtin(BuiltinSort::K) {
            return self
                .placement(&actual, expected)
                .map(|plan| self.apply_placement(plan, visited))
                .ok_or_else(|| {
                    SortInjectionError::IllSortedTerm(Box::new(SortMismatch {
                        term: render_term(term),
                        found: actual,
                        required: expected.clone(),
                    }))
                });
        }
        // Each wrapper gives `visited` back when it does not apply, so the subterm is moved
        // rather than copied at every level of a nesting.
        let visited = match self.collection_wrapper(term, &actual, expected, visited, is_lhs)? {
            Ok(wrapped) => return Ok(wrapped),
            Err(visited) => visited,
        };
        let visited = match self.user_list_wrapper(&actual, expected, visited) {
            Ok(wrapped) => return Ok(wrapped),
            Err(visited) => visited,
        };
        if let Some(plan) = self.placement(&actual, expected) {
            return Ok(self.apply_placement(plan, visited));
        }
        Err(SortInjectionError::IllSortedTerm(Box::new(SortMismatch {
            term: render_term(term),
            found: actual,
            required: expected.clone(),
        })))
    }

    /// `visited` wrapped as the one element of a user list of sort `expected`, or `visited` back
    /// when no such wrapping applies.
    fn user_list_wrapper(
        &self,
        actual: &Sort,
        expected: &Sort,
        visited: Term,
    ) -> Result<Term, Term> {
        if !self.is_user_list_sort(expected) || self.is_user_list_sort(actual) {
            return Err(visited);
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
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Context { .. }
                | Sentence::Rule { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => None,
            });
        let Some((recursive_label, list_first)) = recursive.next() else {
            return Err(visited);
        };
        if recursive.next().is_some() {
            return Err(visited);
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
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Context { .. }
                | Sentence::Rule { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => None,
            });
        let Some(terminator) = terminators.next() else {
            return Err(visited);
        };
        if terminators.next().is_some() {
            return Err(visited);
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
        Ok(Term::Apply {
            label: recursive_label,
            arguments,
        })
    }

    /// `visited` wrapped as an element of the collection sort `expected`, or `visited` back when
    /// no element production wraps its sort.
    fn collection_wrapper(
        &self,
        term: &Term,
        actual: &Sort,
        expected: &Sort,
        visited: Term,
        is_lhs: bool,
    ) -> Result<Result<Term, Term>, SortInjectionError> {
        let hook = self
            .sorts
            .attributes_for(&SortHead::from(expected))
            .and_then(|attributes| attributes.string(AttributeKey::Hook));
        if !matches!(hook, Some("MAP.Map" | "SET.Set" | "LIST.List")) {
            return Ok(Err(visited));
        }
        let Term::Apply { label, arguments } = term.unannotated() else {
            return Ok(Err(visited));
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
                return Ok(Ok(Term::apply(element_label, vec![visited])));
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
            #[expect(
                clippy::wildcard_enum_match_arm,
                reason = "ProductionItem is not a sentence kind; only the listed variants are special here"
            )]
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
                Term::apply(cell_map_key_label(expected), vec![visited.clone()])
            };
            let key = self.unmemoized(|| self.inject_with_position(&key, key_sort, is_lhs))?;
            return Ok(Ok(Term::apply(element_label, vec![key, visited])));
        }
        Ok(Err(visited))
    }

    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is not a sentence kind; only the listed variants are special here"
    )]
    fn visit_children(
        &self,
        term: &Term,
        actual: &Sort,
        is_lhs: bool,
    ) -> Result<Term, SortInjectionError> {
        let rebuilt = match term.unannotated() {
            Term::Apply { label, arguments } if label.is(WellKnownSymbol::Inj) => {
                let witness = self.retained_injection(term, label, arguments)?;
                let operand = self.inject_with_position(&arguments[0], witness.source(), is_lhs)?;
                witness.apply(operand)
            }
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
                self.admit_instance(term, &signature)?;
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

    fn admit_instance(
        &self,
        term: &Term,
        signature: &InstantiatedSignature,
    ) -> Result<(), SortInjectionError> {
        if signature.builds_every_sort
            && !mentions_sort_parameter(&signature.result)
            && self
                .sorts
                .has_fixed_values(&SortHead::from(&signature.result))
        {
            return Err(SortInjectionError::InstanceAtFixedSort(Box::new(
                InstanceAtFixedSort {
                    term: render_term(term),
                    label: signature.label.name.clone(),
                    sort: signature.result.clone(),
                },
            )));
        }
        Ok(())
    }

    #[deny(clippy::wildcard_enum_match_arm)]
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
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "ProductionItem is not a sentence kind; only the listed variants are special here"
        )]
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
            // `isS` is a generated sort predicate only for a sort whose role has one.
            if label.name.strip_prefix("is").is_some_and(|sort| {
                Sort::new(sort).role().has_sort_predicate()
                    && self
                        .sorts
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
        let builds_every_sort = if parameters.is_empty() {
            false
        } else {
            match (
                ResultSorts::of(production),
                ProductionKind::of(production).no_junk(),
            ) {
                (ResultSorts::Every, NoJunk::Generator) => true,
                (ResultSorts::Head(_), NoJunk::Generator)
                | (
                    ResultSorts::Every | ResultSorts::Head(_),
                    NoJunk::DomainValues | NoJunk::Absent,
                ) => false,
            }
        };
        Ok(InstantiatedSignature {
            label: Label::with_parameters(&label.name, instantiated_parameters),
            arguments: argument_sorts
                .into_iter()
                .map(|sort| substitute_sort(sort, &substitution))
                .collect(),
            result: substitute_sort(sort, &substitution),
            builds_every_sort,
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
    /// - a parameter that occurs in no argument: the position itself when the result is the
    ///   parameter, otherwise every value under which the whole result is the position or a
    ///   declared sort below it, so every declared instance whose result fits the position.
    ///
    /// A parameter without candidates keeps its uninstantiated fallback (a sort variable of an
    /// argument, or the fresh parameter), and injecting the arguments then decides. The exact
    /// assignment (each argument's sort as its declared sort) is tried first and accepted when it
    /// satisfies every constraint. Otherwise the least satisfying assignment in the pointwise
    /// order on the instantiated argument sorts is chosen, extended by the instantiated result
    /// sort when a parameter occurs in no argument (nothing else orders it); when none satisfies the position
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
                    // Every instance whose result fits the position is a candidate: the whole
                    // result is matched against the position and each declared sort below it,
                    // so a value is kept only when its instantiated result is one of those
                    // sorts. The search orders them by their instantiated result, since no
                    // argument does.
                    let below = std::iter::once(position).chain(
                        self.sorts
                            .sorted_all_sorts()
                            .filter(|candidate| self.subsorts.less_than_eq(candidate, position)),
                    );
                    let values = below
                        .filter_map(|sort| {
                            let mut binding = BTreeMap::new();
                            bind_parameters(parameters, result, sort, &mut binding)
                                .then(|| binding.remove(parameter))
                                .flatten()
                        })
                        // The declared result itself, written with the formal parameters, is
                        // no instance.
                        .filter(|value| concrete(value) && !mentions_parameter(value))
                        .collect::<Vec<_>>();
                    candidates
                        .get_mut(parameter)
                        .expect("every parameter has a candidate set")
                        .extend(values);
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
            // A parameter that occurs in no argument is ordered by nothing but the result it
            // instantiates, so the group's order then includes the instantiated result.
            let group_orders_result = group_has_position
                && group.iter().any(|&index| {
                    !declared
                        .iter()
                        .any(|declared| contains_sort(declared, &parameters[index]))
                });
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
                    .chain(group_orders_result.then(|| substitute_sort(result, assignment)))
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
            group_minima.push((minima, group_orders_result));
        }
        if let Some((minima, orders_result)) =
            group_minima.iter().find(|(minima, _)| minima.len() > 1)
        {
            let candidates = minima
                .iter()
                .map(|(assignment, _)| {
                    let mut witness = chosen.clone();
                    witness.extend(assignment.clone());
                    constrained
                        .iter()
                        .map(|(declared, _)| substitute_sort(declared, &witness))
                        .chain(orders_result.then(|| substitute_sort(result, &witness)))
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
                    position: orders_result.then(|| (result.clone(), position.clone())),
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
            .filter(|sort| !sort.is_rigid_variable())
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
            .filter(|sort| !sort.is_rigid_variable())
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
            // A single sort is an upper bound of itself, but a relation-free sort is absent from
            // PartialOrder's element set, so `upper_bounds` omits it.
            bounds.insert(sort.clone());
        }
        let k_bottom = Sort::frontend(FrontendSort::KBott);
        let k = Sort::builtin(BuiltinSort::K);
        bounds.retain(|bound| {
            !self.subsorts.less_than_eq(bound, &k_bottom) && !self.subsorts.greater_than(bound, &k)
        });
        if let Some(expected) = expected
            && !expected.is_rigid_variable()
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
    builds_every_sort: bool,
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
                    origin: sentence
                        .attributes()
                        .origin_record()
                        .map(|record| record.pass),
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
    sort.is_rigid_variable() || sort.parameters.iter().any(mentions_sort_parameter)
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

/// The side of every rewrite in `term` that `right` selects, with each nested pair of injections
/// that the projection exposes composed into one when `subsorts`, the module's semantic order,
/// justifies the composed pair.
// Invariant: each call projects one node of `term` and recurses only into its direct subterms, so the finite `term` bounds the calls; `right` selects the side kept at every rewrite.
pub(crate) fn rewrite_projection(term: &Term, right: bool, subsorts: &PartialOrder<Sort>) -> Term {
    crate::stack::guarded(|| rewrite_projection_level(term, right, subsorts))
}

/// One level of [`rewrite_projection`], which runs it with stack for one more level.
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is not a sentence kind; only the listed variants are special here"
)]
fn rewrite_projection_level(term: &Term, right: bool, subsorts: &PartialOrder<Sort>) -> Term {
    match term.unannotated() {
        Term::Rewrite {
            left,
            right: rewrite_right,
        } => {
            if right {
                rewrite_projection(rewrite_right, true, subsorts)
            } else {
                left.as_ref().clone()
            }
        }
        Term::Apply { label, arguments } => {
            let projected = Term::Apply {
                label: label.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| rewrite_projection(argument, right, subsorts))
                    .collect(),
            };
            copy_metadata(term, compact_injections(projected, subsorts))
        }
        Term::Sequence(items) => copy_metadata(
            term,
            Term::sequence(
                items
                    .iter()
                    .map(|item| rewrite_projection(item, right, subsorts)),
            ),
        ),
        Term::As { pattern, alias } => {
            if right {
                alias.as_ref().clone()
            } else {
                copy_metadata(
                    term,
                    Term::As {
                        pattern: Box::new(rewrite_projection(pattern, false, subsorts)),
                        alias: alias.clone(),
                    },
                )
            }
        }
        _ => term.clone(),
    }
}

/// `inj{B, C}(inj{A, B}(t))` as `inj{A, C}(t)` when `A < C` along the subsort axioms of
/// `subsorts`; any other term, including a nested pair whose composition is not justified, is
/// returned unchanged.
fn compact_injections(term: Term, subsorts: &PartialOrder<Sort>) -> Term {
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
    let Some(composed) = Injectable::between(inner_from, outer_to, subsorts) else {
        return term;
    };
    let [inner_argument] = inner_arguments.as_slice() else {
        return term;
    };
    composed.apply(inner_argument.clone())
}

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is not a sentence kind; only the listed variants are special here"
)]
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

/// Wrap a downcast term in `projection`, the runtime projection generated for its cast target.
///
/// The argument keeps its metadata except the cast sort, so it sorts as its production's natural
/// result sort and is not projected again.
fn semantic_projection(term: &Term, projection: Label) -> Term {
    let mut argument = term.clone().into_unannotated();
    if let Some(metadata) = term.metadata() {
        let mut metadata = metadata.clone();
        metadata.sort = None;
        argument = argument.with_metadata(metadata);
    }
    Term::Apply {
        label: projection,
        arguments: vec![argument],
    }
}

#[cfg(test)]
mod tests {
    use super::{
        GroundCause, GroundInput, SortInjectionError, SortInjector, UndeterminedCause,
        UndeterminedSite, rewrite_projection,
    };
    use crate::definition::{PartialOrder, ResolvedDefinition, Sentence, production_identity};
    use crate::kast::{Label, Sort, Term, TermMetadata, parser::parse_term};

    /// Injecting a chain of a parametric production infers each node's sort once: the sort of
    /// `wrap(t)` under `syntax {S} S ::= wrap(S)` is the sort of `t`, so inferring it walks the
    /// whole chain below, and injection once repeated that walk at every level and then once
    /// more for each child, inferring O(depth²) sorts (12 s at 4,000 levels in a release build).
    /// A chain of 2,000 levels now makes at most 2.5 times the inferences of one of 1,000, and
    /// after the call the memo is empty.
    #[test]
    fn a_parametric_chain_is_injected_with_one_inference_per_node() {
        let parsed = crate::outer::parse(
            "chain.k",
            "module MAIN\n syntax Nat ::= \"z\" [symbol(z)]\n syntax {S} S ::= wrap(S) [symbol(wrap)]\nendmodule\n",
        )
        .unwrap();
        let definition = crate::outer::lower(&parsed, "MAIN").unwrap();
        let resolved = ResolvedDefinition::resolve(&definition).unwrap();
        let injector = SortInjector::new(&resolved, "MAIN").unwrap();
        let inferences = |depth: usize| {
            let chain = (0..depth).fold(Term::apply("z", Vec::new()), |term, _| {
                Term::apply("wrap", vec![term])
            });
            let before = injector.natural_sorts.borrow().inferences;
            let injected = injector.inject_at_top(&chain).unwrap();
            let Term::Apply { label, .. } = injected.unannotated() else {
                panic!("the chain stays an application")
            };
            assert_eq!(label.parameters, [Sort::new("Nat")]);
            assert!(injector.natural_sorts.borrow().sorts.is_empty());
            injector.natural_sorts.borrow().inferences - before
        };
        let (small, large) = (inferences(1_000), inferences(2_000));
        assert!(
            large <= small * 5 / 2,
            "{small} inferences at 1,000 levels, {large} at 2,000"
        );
    }

    #[test]
    fn sentence_sort_variables_classifies_only_whole_predicate_sorts() {
        let parsed = crate::outer::parse(
            "sentence-sorts.k",
            "module MAIN\n syntax {S} MInt{S} ::= zero() [symbol(zero)]\n syntax {T} Foo ::= zero() [symbol(zero)]\n endmodule\n",
        )
        .unwrap();
        let definition = crate::outer::lower(&parsed, "MAIN").unwrap();
        let resolved = ResolvedDefinition::resolve(&definition).unwrap();
        let injector = SortInjector::new(&resolved, "MAIN").unwrap();
        let q = Sort::with_parameters("#SortParam", vec![Sort::new("Q0")]);
        let mint_q = Sort::with_parameters("MInt", vec![q.clone()]);
        let equals = |parameters| Term::Apply {
            label: Label::with_parameters("#Equals", parameters),
            arguments: vec![Term::variable("X"), Term::variable("Y")],
        };
        let predicate = equals(vec![Sort::new("Bool"), q.clone()]);
        let variables = injector.sentence_sort_variables([&predicate]).unwrap();
        assert_eq!(variables.names().collect::<Vec<_>>(), ["Q0"]);
        assert!(!variables.is_empty());

        let error = injector
            .require_ground(&predicate, GroundInput::Value)
            .unwrap_err();
        let message = error.to_string();
        assert!(
            message.contains("a ground value binds no sort variable"),
            "{message}"
        );
        assert!(
            message.contains("even a predicate's sort must be determined"),
            "{message}"
        );
        assert!(
            !message.contains("only the sort of a predicate may stay"),
            "{message}"
        );
        let SortInjectionError::UndeterminedInstance(instance) = error else {
            panic!("{error:?}")
        };
        assert_eq!(
            instance.site,
            UndeterminedSite::Ground {
                input: GroundInput::Value,
                cause: GroundCause::PredicateSort {
                    label: "#Equals".into()
                },
            }
        );
        assert_eq!(instance.variable, q);
        assert!(!message.contains("add a sort cast"), "{message}");
        let pattern_error = injector
            .require_ground(&predicate, GroundInput::SearchPattern)
            .unwrap_err();
        assert!(
            pattern_error
                .to_string()
                .contains("add a sort cast that fixes it")
        );
        let SortInjectionError::UndeterminedInstance(pattern_instance) = pattern_error else {
            panic!("{pattern_error:?}")
        };
        assert_eq!(
            pattern_instance.site,
            UndeterminedSite::Ground {
                input: GroundInput::SearchPattern,
                cause: GroundCause::PredicateSort {
                    label: "#Equals".into()
                },
            }
        );
        assert!(
            injector
                .require_ground(
                    &equals(vec![Sort::new("Bool"), Sort::new("Int")]),
                    GroundInput::Value
                )
                .is_ok()
        );

        let nested = equals(vec![mint_q.clone(), Sort::new("Bool")]);
        let variable = Term::Variable {
            name: "X".into(),
            sort: Some(q.clone()),
        };
        let token = Term::Token {
            token: "0".into(),
            sort: mint_q.clone(),
        };
        let injected_label = Term::InjectedLabel(Label::with_parameters("zero", vec![q.clone()]));
        let malformed = equals(vec![Sort::with_parameters(
            "#SortParam",
            vec![Sort::with_parameters("Q0", vec![Sort::new("Int")])],
        )]);
        for offender in [&nested, &variable, &token, &injected_label, &malformed] {
            assert!(
                matches!(
                    injector.sentence_sort_variables([offender]),
                    Err(SortInjectionError::UndeterminedInstance(_))
                ),
                "{offender}"
            );
        }

        let production = definition
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find(|sentence| {
                matches!(&***sentence, Sentence::Production { parameters, .. }
                if parameters == &[Sort::new("S")])
            })
            .unwrap();
        let zero = Term::Apply {
            label: Label::with_parameters("zero", vec![q.clone()]),
            arguments: Vec::new(),
        }
        .with_metadata(TermMetadata {
            production: production_identity(production),
            ..TermMetadata::default()
        });
        let injection = Term::Apply {
            label: Label::with_parameters("inj", vec![mint_q.clone(), Sort::new("KItem")]),
            arguments: vec![zero],
        };
        let error = injector
            .sentence_sort_variables([&variable, &injection])
            .unwrap_err();
        let SortInjectionError::UndeterminedInstance(instance) = error else {
            panic!("{error:?}")
        };
        assert_eq!(
            instance.site,
            UndeterminedSite::Sentence(UndeterminedCause::Open {
                label: "zero".into(),
                parameter: Sort::new("S"),
            })
        );
        assert_eq!(instance.variable, q);
    }

    fn order(edges: &[(&str, &str)]) -> PartialOrder<Sort> {
        PartialOrder::new(
            edges
                .iter()
                .map(|(lesser, greater)| (Sort::new(*lesser), Sort::new(*greater))),
        )
        .expect("the test order is acyclic")
    }

    fn projected(term: &str, subsorts: &PartialOrder<Sort>) -> String {
        let term = parse_term(term).expect("the test term parses");
        rewrite_projection(&term, false, subsorts).to_string()
    }

    /// Two nested injections along subsort axioms compose into one, which the composed pair's
    /// own axiom chain justifies.
    #[test]
    fn projection_composes_a_nested_pair_along_subsort_axioms() {
        let subsorts = order(&[("A", "B"), ("B", "C")]);
        assert_eq!(projected("inj{B,C}(inj{A,B}(X))", &subsorts), "inj{A,C}(X)");
    }

    /// Composition must not turn a nested pair into an injection no axiom chain justifies:
    /// `Int < KItem < K < KList` has no subsort axiom into `K`, so `inj{Int,KList}` would embed
    /// nothing; the nested pair is left as it is.
    #[test]
    fn projection_keeps_a_nested_pair_whose_composition_is_not_an_injection() {
        let subsorts = order(&[("Int", "KItem"), ("KItem", "K"), ("K", "KList")]);
        assert_eq!(
            projected("inj{K,KList}(inj{Int,K}(X))", &subsorts),
            "inj{K,KList}(inj{Int,K}(X))"
        );
    }
}

/// The stage on the definition the pipeline gives it ([`crate::kompile::stage_harness`]).
#[cfg(test)]
mod stage_tests {
    use crate::kompile::stage_harness::{labelled, render, run_to_stage};

    /// In KORE an argument has exactly the sort its symbol declares; a K term of a strict
    /// subsort stands there through the injection `inj{Sub, Super}`. So the stage wraps every
    /// argument whose sort is strictly below the declared sort in one injection between those
    /// two sorts, and leaves an argument of the declared sort alone: `V:Val` under `pair(Exp,
    /// Exp)` becomes `inj{Val,Exp}(V)`, `E:Exp` stays, and the `Exp` term in the `<k>` cell,
    /// whose content is a `KItem`, is injected into `KItem`. (The stage also states the rule as
    /// one rewrite of the whole configuration, as a KORE rewrite axiom has it; the definition has
    /// no `Int`, so its configuration has no fresh counter cell.)
    #[test]
    fn a_subsort_argument_is_injected_into_the_declared_sort_and_only_then() {
        let run = run_to_stage(
            r#"
module MAIN
  syntax K
  syntax Val ::= "v" [symbol(v)]
  syntax Exp ::= Val | pair(Exp, Exp) [symbol(pair)]
  configuration <k> v </k>
  rule <k> pair(V:Val, E) => pair(E, V) </k> [label(swap)]
endmodule
"#,
            "add sort injections",
        );
        let before = labelled(&run.input, "MAIN", "swap");
        let after = labelled(run.output(), "MAIN", "swap");
        assert_eq!(
            render(before[0]),
            r#"rule `<generatedTop>`(`<k>`(pair(V,E)=>pair(E,V))) requires #token("true","Bool") ensures #token("true","Bool")"#
        );
        assert_eq!(
            render(after[0]),
            r#"rule `<generatedTop>`(`<k>`(inj{Exp,KItem}(pair(inj{Val,Exp}(V),E))))=>`<generatedTop>`(`<k>`(inj{Exp,KItem}(pair(E,inj{Val,Exp}(V))))) requires #token("true","Bool") ensures #token("true","Bool")"#
        );
    }

    /// `isS(X)` holds exactly when `X` is a term of sort `S`: a sort predicate is decided by its
    /// argument's sort. A rule that makes it read the configuration (here through a function
    /// that matches a cell) would make sort membership change as the program runs, which no
    /// sort predicate can state, so the definition is rejected naming the predicate.
    #[test]
    fn a_sort_predicate_that_reads_the_configuration_is_rejected() {
        let run = run_to_stage(
            r#"
module BOOL
endmodule
module MAIN
  syntax K
  syntax Bool ::= "true" [token] | both(Bool, Bool) [function, symbol(both)]
  syntax Int ::= r"[0-9]+" [token]
  syntax Exp
  rule isExp(I) => both(isInt(I), configFunction())
  configuration <k> .K </k> <state> .K </state>
  syntax Bool ::= configFunction() [function, symbol(configFunction)]
  rule [[ configFunction() => true ]]
       <state> .K </state>
endmodule
"#,
            "add sort injections",
        );
        let error = run.error();
        assert_eq!(error.stage, "add sort injections");
        assert!(
            error.message.starts_with("definition.k:9: ")
                && error.message.ends_with(
                    "Invalid sort predicate isExp that depends directly or indirectly on the current configuration. Is it possible to replace the sort predicate with a regular function?"
                ),
            "{}",
            error.message
        );
    }
}
