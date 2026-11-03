//! The compiled definition's rules and equations, by the backend's identity (`UNIQUE_ID`).
//!
//! k-rust names a rule or an equation by its `UNIQUE_ID` in run coverage and in traces, and a
//! run's stop rules are named by label ([`crate::StopRules`]). This catalog is what krs-exec
//! reads both from: each identity's label and kind, as the backend loaded them
//! (`Backend::rule_catalog`).

use std::collections::BTreeMap;

use k_rust::backend::{Backend, CompiledRuleKind};

use crate::{ExecError, report::RuleKind};

/// One identity of the catalog.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CatalogRule {
    /// The rule's label, as the backend names it (`SM83.boundary-fetch`, `nat--plus_zero`).
    pub(crate) label: Option<String>,
    /// What kind of sentence it is.
    pub(crate) kind: RuleKind,
}

/// The rules and equations of the definition a run executes, by `UNIQUE_ID`.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Rules {
    by_id: BTreeMap<String, CatalogRule>,
}

impl Rules {
    /// The catalog of the definition `backend` runs.
    pub(crate) fn new(backend: &Backend) -> Result<Self, ExecError> {
        let mut by_id = BTreeMap::new();
        for rule in backend.rule_catalog(None)? {
            // Equal written axioms share one identity (`shared_identity`); they are one rule.
            by_id.entry(rule.id).or_insert(CatalogRule {
                label: rule.label,
                kind: match rule.kind {
                    CompiledRuleKind::Rewrite => RuleKind::Rule,
                    CompiledRuleKind::FunctionEquation => RuleKind::Equation,
                    CompiledRuleKind::Simplification => RuleKind::Simplification,
                    CompiledRuleKind::Definedness => RuleKind::Definedness,
                },
            });
        }
        Ok(Self { by_id })
    }

    #[cfg(test)]
    pub(crate) fn from_entries(entries: impl IntoIterator<Item = (String, CatalogRule)>) -> Self {
        Self {
            by_id: entries.into_iter().collect(),
        }
    }

    /// The identity `id`, when the catalog holds it.
    pub(crate) fn get(&self, id: &str) -> Option<&CatalogRule> {
        self.by_id.get(id)
    }

    /// The rewrite rules `requested` names, by label: exactly, or by a unique `.`-suffix as
    /// `krs prove --claim` accepts a claim label (`boundary-fetch` for `SM83.boundary-fetch`).
    ///
    /// The name is resolved among the labels of every sentence, whatever its kind, and the
    /// sentences it names must then be rewrite rules: only a rewrite rule takes a step, so a
    /// name that selects an equation, a simplification or a definedness equation is refused,
    /// never read as a suffix of some rewrite rule's label instead. An exact label wins over
    /// every suffix. A label several rewrite rules carry selects each of them; a suffix that two
    /// labels end with is ambiguous.
    pub(crate) fn resolve_rewrite(&self, requested: &str) -> Result<Vec<String>, ExecError> {
        let labelled = || {
            self.by_id
                .iter()
                .filter_map(|(id, rule)| Some((id, rule, rule.label.as_deref()?)))
        };
        let mut named = labelled()
            .filter(|(.., label)| *label == requested)
            .map(|(id, rule, _)| (id, rule))
            .collect::<Vec<_>>();
        if named.is_empty() {
            let suffix = format!(".{requested}");
            let mut labels = BTreeMap::<&str, Vec<(&String, &CatalogRule)>>::new();
            for (id, rule, label) in labelled().filter(|(.., label)| label.ends_with(&suffix)) {
                labels.entry(label).or_default().push((id, rule));
            }
            named = match labels.len() {
                0 => {
                    return Err(ExecError::UnknownRule {
                        requested: requested.to_owned(),
                        sentence: None,
                        suggestion: self.suggestion(requested),
                    });
                }
                1 => labels.into_values().next().unwrap_or_default(),
                _ => {
                    return Err(ExecError::AmbiguousRule {
                        requested: requested.to_owned(),
                        matches: labels.into_keys().map(str::to_owned).collect(),
                    });
                }
            };
        }
        if let Some((_, other)) = named.iter().find(|(_, rule)| rule.kind != RuleKind::Rule) {
            return Err(ExecError::UnknownRule {
                requested: requested.to_owned(),
                sentence: Some((other.label.clone().unwrap_or_default(), other.kind)),
                suggestion: None,
            });
        }
        Ok(named.into_iter().map(|(id, _)| id.clone()).collect())
    }

    /// A did-you-mean for a rule label written as a Rust identifier (`boundary_fetch` for
    /// `boundary-fetch`) or in another case.
    fn suggestion(&self, requested: &str) -> Option<String> {
        let kebab = requested.replace('_', "-").to_ascii_lowercase();
        let mut labels = self
            .by_id
            .values()
            .filter(|rule| rule.kind == RuleKind::Rule)
            .filter_map(|rule| rule.label.as_deref())
            .filter(|label| {
                let local = label.rsplit_once('.').map_or(*label, |(_, local)| local);
                local.to_ascii_lowercase() == kebab || label.to_ascii_lowercase() == kebab
            })
            .collect::<Vec<_>>();
        labels.sort_unstable();
        labels.dedup();
        match labels.as_slice() {
            [label] => Some((*label).to_owned()),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{CatalogRule, Rules};
    use crate::{ExecError, report::RuleKind};

    fn rules() -> Rules {
        let rule = |id: &str, label: Option<&str>, kind| {
            (
                id.to_owned(),
                CatalogRule {
                    label: label.map(str::to_owned),
                    kind,
                },
            )
        };
        Rules::from_entries([
            rule("r1", Some("SM83.boundary-fetch"), RuleKind::Rule),
            rule("r2", Some("SM83.boundary-halted"), RuleKind::Rule),
            rule("r3", Some("SM83.step"), RuleKind::Rule),
            rule("r4", Some("OTHER.step"), RuleKind::Rule),
            rule("r5", Some("SM83.shared"), RuleKind::Rule),
            rule("r6", Some("SM83.shared"), RuleKind::Rule),
            rule("e1", Some("SM83.plus-zero"), RuleKind::Equation),
            rule("e2", None, RuleKind::Equation),
            rule("e3", Some("fetch"), RuleKind::Equation),
            rule("r7", Some("SM83.fetch"), RuleKind::Rule),
            rule("s1", Some("SM83.lemma"), RuleKind::Simplification),
            rule("r8", Some("OTHER.lemma"), RuleKind::Rule),
        ])
    }

    #[test]
    fn stop_rules_resolve_by_exact_label_or_unique_suffix() {
        let rules = rules();
        assert_eq!(
            rules.resolve_rewrite("SM83.boundary-fetch").unwrap(),
            ["r1"]
        );
        assert_eq!(rules.resolve_rewrite("boundary-halted").unwrap(), ["r2"]);
        assert_eq!(rules.resolve_rewrite("OTHER.step").unwrap(), ["r4"]);
        // One label on two axioms selects both.
        assert_eq!(rules.resolve_rewrite("shared").unwrap(), ["r5", "r6"]);
    }

    #[test]
    fn stop_rules_refuse_ambiguous_unknown_and_equation_names() {
        let rules = rules();
        let ambiguous = rules.resolve_rewrite("step").unwrap_err();
        assert!(
            matches!(&ambiguous, ExecError::AmbiguousRule { matches, .. } if matches == &["OTHER.step", "SM83.step"]),
            "{ambiguous:?}"
        );
        assert_eq!(
            ambiguous.to_string(),
            "rule label `step` is ambiguous; matches `OTHER.step`, `SM83.step`"
        );
        let spelled = rules.resolve_rewrite("boundary_fetch").unwrap_err();
        assert_eq!(
            spelled.to_string(),
            "no rewrite rule has label `boundary_fetch`; did you mean `SM83.boundary-fetch`?"
        );
        let equation = rules.resolve_rewrite("plus-zero").unwrap_err();
        assert_eq!(
            equation.to_string(),
            "no rewrite rule has label `plus-zero`: `SM83.plus-zero` is a function equation, which a run applies without taking a step, so no step can stop at it"
        );
        assert!(matches!(
            rules.resolve_rewrite("missing").unwrap_err(),
            ExecError::UnknownRule {
                suggestion: None,
                sentence: None,
                ..
            }
        ));
    }

    /// An exact label names its own sentence, never a rewrite rule whose label ends with it.
    #[test]
    fn an_exact_label_wins_and_is_refused_when_it_names_no_rewrite_rule() {
        let rules = rules();
        let exact = rules.resolve_rewrite("fetch").unwrap_err();
        assert!(
            matches!(
                &exact,
                ExecError::UnknownRule { sentence: Some((label, RuleKind::Equation)), .. }
                    if label == "fetch"
            ),
            "{exact:?}"
        );
        assert_eq!(rules.resolve_rewrite("SM83.fetch").unwrap(), ["r7"]);
        // A suffix that a simplification's label and a rewrite rule's label end with is
        // ambiguous, and the refusal of a simplification says what it is.
        assert!(matches!(
            rules.resolve_rewrite("lemma").unwrap_err(),
            ExecError::AmbiguousRule { .. }
        ));
        assert_eq!(
            rules.resolve_rewrite("SM83.lemma").unwrap_err().to_string(),
            "no rewrite rule has label `SM83.lemma`: `SM83.lemma` is a simplification, which a run applies without taking a step, so no step can stop at it"
        );
    }
}
