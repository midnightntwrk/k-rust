//! Rule selectors that choose which baseline rules an observation manifest observes.
//!
//! A selector is evaluated once, over the written rules of the [`Baseline`], and yields
//! [`ObservedRule`]s by label. Each compiled side then resolves those labels to its own rule
//! identities ([`crate::NativeValidator::observation_manifest`]), so a mutant never changes
//! which rules are observed; the label is immutable under patches for that reason.
//!
//! Selection is atomic: any failure publishes no rule. A selection must match exactly its
//! expected number of rules, and at least one; no rule may be selected twice.

use std::{collections::BTreeSet, fmt};

use k_rust::{
    definition::{AttributeKey, Sentence},
    kast::Sort,
};
use kink_patch::{Baseline, SentenceRef, SiteSelector, derive_sites};
use serde_json::Value;

use crate::ObservedRule;
use crate::observation::DomainEventSpec;

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
    /// Every written rule. Function equations are rules too, and are included.
    AllTransitions,
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
    /// The selection matched `actual` rules, not `expected`, or matched none.
    CardinalityMismatch {
        selection: usize,
        expected: usize,
        actual: usize,
    },
    /// A matched rule has no label, so no compiled side can resolve it.
    UnlabelledRule { selection: usize, rule: SentenceRef },
    /// A rule is matched by this selection and an earlier one.
    DuplicateRule { selection: usize, rule: SentenceRef },
    /// Some position's sort could not be decided, so whether the rule matches is unknown.
    UndecidedSort { selection: usize },
}

impl fmt::Display for SelectionFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CardinalityMismatch {
                selection,
                expected,
                actual,
            } => write!(
                formatter,
                "selection {selection} matched {actual} rules, expected {expected}"
            ),
            Self::UnlabelledRule { selection, rule } => {
                write!(
                    formatter,
                    "selection {selection} matched unlabelled {rule:?}"
                )
            }
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
        }
    }
}

impl std::error::Error for SelectionFailure {}

/// Resolves `selections` over `baseline`: the matched rules of each selection in definition
/// order, selections in the order given, each with its selection's emissions.
///
/// # Errors
///
/// Returns the first failing selection's [`SelectionFailure`]; no rule is published then.
pub fn select_rules(
    baseline: &Baseline,
    selections: &[RuleSelection],
) -> Result<Vec<ObservedRule>, SelectionFailure> {
    let mut seen = BTreeSet::new();
    let mut rules = Vec::new();
    for (index, selection) in selections.iter().enumerate() {
        let matched = matched_rules(baseline, &selection.selector)
            .ok_or(SelectionFailure::UndecidedSort { selection: index })?;
        if matched.len() != selection.expected_cardinality || matched.is_empty() {
            return Err(SelectionFailure::CardinalityMismatch {
                selection: index,
                expected: selection.expected_cardinality,
                actual: matched.len(),
            });
        }
        for (at, label) in matched {
            let Some(label) = label else {
                return Err(SelectionFailure::UnlabelledRule {
                    selection: index,
                    rule: at,
                });
            };
            if !seen.insert(at.clone()) {
                return Err(SelectionFailure::DuplicateRule {
                    selection: index,
                    rule: at,
                });
            }
            rules.push(ObservedRule {
                label,
                emit_rule_applied: selection.emit_rule_applied,
                domain_events: selection.domain_events.clone(),
            });
        }
    }
    Ok(rules)
}

/// The written rules `selector` matches, in definition order, with their labels; `None` when
/// a structural selector met a position of undecided sort.
fn matched_rules(
    baseline: &Baseline,
    selector: &RuleSelector,
) -> Option<Vec<(SentenceRef, Option<String>)>> {
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
            let discovery = derive_sites(baseline, "observation", &clauses)
                .expect("a selector without Bind clauses is valid");
            if !discovery.exhaustive() {
                return None;
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
    Some(
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
                        RuleSelector::AllTransitions => true,
                    }
            })
            .map(|(at, sentence)| {
                let label = sentence
                    .attributes()
                    .string(AttributeKey::Label)
                    .map(str::to_owned);
                (at, label)
            })
            .collect(),
    )
}
