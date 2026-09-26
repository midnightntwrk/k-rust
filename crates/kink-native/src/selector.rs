//! Rule selectors that choose which baseline rules an observation manifest observes.
//!
//! A selector is evaluated once, over the written rules of the [`Baseline`], and yields
//! [`ObservedRule`]s by source position. Each compiled side resolves those positions to its
//! own rule identities ([`crate::NativeValidator::observation_manifest`]).
//!
//! Selection is atomic: any failure publishes no rule. A selection must match exactly its
//! expected number of rules, and at least one; no rule may be selected twice.

use std::{collections::BTreeSet, fmt};

use k_rust::{
    backend::{Backend, BackendOptions, CompiledRuleKind},
    definition::{AttributeKey, Sentence},
    kast::Sort,
    provenance::InputSpace,
};
use kink_patch::{Baseline, CandidateFailure, SentenceRef, SiteSelector, derive_sites};
use serde_json::Value;

use crate::observation::DomainEventSpec;
use crate::{NativeValidator, ObservedRule, ValidatedDefinition};

/// Which written rules of the baseline one selection observes.
#[derive(Clone, Debug, PartialEq)]
pub enum RuleSelector {
    /// The rule with this module-qualified label.
    Label(String),
    /// Every rule whose attribute `key` has exactly `value`, as the loader writes it.
    Attribute { key: String, value: Value },
    /// Every rule with a term at `path` (a kink-patch term path) of exactly `sort`.
    ///
    /// Without a `label`, labelled and unlabelled rules both match; without a `head`, any
    /// term of the sort matches, including a rewrite or a variable.
    Structural {
        label: Option<String>,
        path: Vec<u32>,
        sort: Sort,
        head: Option<String>,
    },
    /// Every written rule that k-rust executes as a rewrite rule, as classified by the
    /// compiled baseline's `rewrite_theory`. Function equations, simplification and anywhere
    /// rules are left out; an explicit selection of one fails closed.
    AllTransitions,
}

/// Written baseline rules present in k-rust's executable rewrite theory.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RewriteRules(BTreeSet<SentenceRef>);

/// Why a compiled baseline cannot be classified without guessing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ClassificationFailure {
    MutantBaseline,
    Internalize(String),
    AmbiguousRule(SentenceRef),
    /// A rewrite identity cannot be assigned to a written rule or a known builtin.
    UnmappedRewriteIdentity(String),
}

impl fmt::Display for ClassificationFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MutantBaseline => {
                formatter.write_str("rewrite classification requires a compiled baseline")
            }
            Self::Internalize(error) => {
                write!(formatter, "could not internalize compiled KORE: {error}")
            }
            Self::AmbiguousRule(rule) => {
                write!(formatter, "{rule:?} has ambiguous compiled identities")
            }
            Self::UnmappedRewriteIdentity(id) => {
                write!(
                    formatter,
                    "rewrite identity {id} has no authored source position"
                )
            }
        }
    }
}

impl std::error::Error for ClassificationFailure {}

impl RewriteRules {
    /// Classifies authored rules by k-rust's compiled rewrite theory for `module`.
    ///
    /// # Errors
    ///
    /// Refuses a mutant, failed KORE parse or internalization, an ambiguous position,
    /// or a rewrite identity without a known authored or builtin position.
    pub fn classify(
        validator: &NativeValidator,
        baseline: &ValidatedDefinition,
        module: &str,
    ) -> Result<Self, ClassificationFailure> {
        if baseline.origins().is_some() {
            return Err(ClassificationFailure::MutantBaseline);
        }
        let backend = Backend::new(
            &baseline.artifacts().definition_kore,
            module,
            BackendOptions::default(),
        )
        .map_err(|error| ClassificationFailure::Internalize(error.to_string()))?;
        let catalog = backend
            .rule_catalog(Some(module))
            .map_err(|error| ClassificationFailure::Internalize(error.to_string()))?;
        let authored = validator
            .baseline()
            .authored_sentences()
            .filter(|(_, sentence)| matches!(sentence, Sentence::Rule { .. }))
            .map(|(at, _)| at)
            .collect::<BTreeSet<_>>();
        let mut selected = BTreeSet::new();
        for entry in catalog
            .into_iter()
            .filter(|entry| entry.kind == CompiledRuleKind::Rewrite && entry.executable)
        {
            let authors = baseline
                .artifacts()
                .sentence_provenance
                .get(&entry.id)
                .into_iter()
                .flat_map(|provenance| &provenance.input_addresses)
                .filter(|address| address.input == InputSpace::Compile)
                .map(|address| SentenceRef::new(&address.module, address.index))
                .filter(|at| authored.contains(at))
                .collect::<BTreeSet<_>>();
            if entry.shared_identity {
                if let Some(first) = authors.into_iter().next() {
                    return Err(ClassificationFailure::AmbiguousRule(first));
                }
                continue;
            }
            if authors.is_empty() {
                let known_builtin = !entry.origins.is_empty()
                    && entry.origins.iter().all(|origin| {
                        origin.source.as_ref().is_some_and(|source| {
                            baseline
                                .compile_options()
                                .builtin_source_prefixes
                                .iter()
                                .any(|prefix| source.starts_with(prefix))
                        })
                    });
                if !known_builtin {
                    return Err(ClassificationFailure::UnmappedRewriteIdentity(entry.id));
                }
            }
            selected.extend(authors);
        }
        Ok(Self(selected))
    }
}

/// One selector with the number of rules it must match and what each matched rule emits.
#[derive(Clone, Debug, PartialEq)]
pub struct RuleSelection {
    pub selector: RuleSelector,
    pub expected_cardinality: usize,
    pub emit_rule_applied: bool,
    pub domain_events: Vec<DomainEventSpec>,
}

/// Why a list of selections publishes no rule. `selection` is the index of the failing
/// selection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SelectionFailure {
    /// `AllTransitions` needs the compiled baseline's rewrite classification.
    Unclassified { selection: usize },
    /// The selection matched `actual` rules, not `expected`, or matched none.
    CardinalityMismatch {
        selection: usize,
        expected: usize,
        actual: usize,
    },
    /// A rule is matched by this selection and an earlier one.
    DuplicateRule { selection: usize, rule: SentenceRef },
    /// Some position's sort could not be decided, so whether the rule matches is unknown.
    UndecidedSort { selection: usize },
    /// A structural selector names an invalid site.
    Structural {
        selection: usize,
        failure: CandidateFailure,
    },
}

impl fmt::Display for SelectionFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unclassified { selection } => write!(
                formatter,
                "selection {selection} has no rewrite classification"
            ),
            Self::CardinalityMismatch {
                selection,
                expected,
                actual,
            } => write!(
                formatter,
                "selection {selection} matched {actual} rules, expected {expected}"
            ),
            Self::DuplicateRule { selection, rule } => write!(
                formatter,
                "selection {selection} matched {rule:?}, which an earlier selection matched"
            ),
            Self::UndecidedSort { selection } => {
                write!(
                    formatter,
                    "selection {selection} met a position of unknown sort"
                )
            }
            Self::Structural { selection, failure } => {
                write!(
                    formatter,
                    "selection {selection} has an invalid structural site: {failure}"
                )
            }
        }
    }
}

impl std::error::Error for SelectionFailure {}

/// Resolves `selections` over `baseline`: the matched rules of each selection in definition
/// order, selections in the order given, each with its selection's emissions. `AllTransitions`
/// requires `rewrite_rules` from that compiled baseline; other selectors ignore it.
///
/// # Errors
///
/// Returns the first failing selection's [`SelectionFailure`]; no rule is published then.
pub fn select_rules(
    baseline: &Baseline,
    rewrite_rules: Option<&RewriteRules>,
    selections: &[RuleSelection],
) -> Result<Vec<ObservedRule>, SelectionFailure> {
    let mut seen = BTreeSet::new();
    let mut rules = Vec::new();
    for (index, selection) in selections.iter().enumerate() {
        if matches!(selection.selector, RuleSelector::AllTransitions) && rewrite_rules.is_none() {
            return Err(SelectionFailure::Unclassified { selection: index });
        }
        let matched = matched_rules(baseline, rewrite_rules, &selection.selector)
            .map_err(|failure| SelectionFailure::Structural {
                selection: index,
                failure,
            })?
            .ok_or(SelectionFailure::UndecidedSort { selection: index })?;
        if matched.len() != selection.expected_cardinality || matched.is_empty() {
            return Err(SelectionFailure::CardinalityMismatch {
                selection: index,
                expected: selection.expected_cardinality,
                actual: matched.len(),
            });
        }
        for at in matched {
            if !seen.insert(at.clone()) {
                return Err(SelectionFailure::DuplicateRule {
                    selection: index,
                    rule: at,
                });
            }
            rules.push(ObservedRule {
                rule: at,
                emit_rule_applied: selection.emit_rule_applied,
                domain_events: selection.domain_events.clone(),
            });
        }
    }
    Ok(rules)
}

/// The written rules `selector` matches, in definition order; `None` when
/// a structural selector met a position of undecided sort.
fn matched_rules(
    baseline: &Baseline,
    rewrite_rules: Option<&RewriteRules>,
    selector: &RuleSelector,
) -> Result<Option<Vec<SentenceRef>>, CandidateFailure> {
    let structural = match selector {
        RuleSelector::Structural {
            label,
            path,
            sort,
            head,
        } => {
            let clauses = label
                .iter()
                .map(|label| SiteSelector::RuleLabel(label.clone()))
                .chain([
                    SiteSelector::Path(path.clone()),
                    SiteSelector::Sort(sort.clone()),
                ])
                .chain(head.iter().map(|label| SiteSelector::Head {
                    label: label.clone(),
                }))
                .collect::<Vec<_>>();
            let discovery = derive_sites(baseline, "observation", &clauses)?;
            if !discovery.exhaustive() {
                return Ok(None);
            }
            Some(
                discovery
                    .tuples()
                    .iter()
                    .flat_map(|tuple| &tuple.sites)
                    .map(|site| site.at.sentence.clone())
                    .collect::<BTreeSet<_>>(),
            )
        }
        _ => None,
    };
    Ok(Some(
        baseline
            .authored_sentences()
            .filter(|(at, sentence)| {
                matches!(sentence, Sentence::Rule { .. })
                    && match selector {
                        RuleSelector::Label(label) => {
                            sentence.attributes().string(AttributeKey::Label)
                                == Some(label.as_str())
                        }
                        RuleSelector::Attribute { key, value } => {
                            sentence.attributes().get(key) == Some(value)
                        }
                        RuleSelector::Structural { .. } => structural
                            .as_ref()
                            .is_some_and(|matched| matched.contains(at)),
                        RuleSelector::AllTransitions => {
                            rewrite_rules.is_some_and(|rules| rules.0.contains(at))
                        }
                    }
            })
            .map(|(at, _)| at)
            .collect(),
    ))
}
