//! Coverage chooses test order only; it does not supply an oracle outcome.

use std::collections::BTreeSet;

use k_rust::{
    kore::{
        ast::{Attributes, Definition, Pattern, Sentence},
        parser::parse_definition,
    },
    names::KoreAttribute,
};
use kink_native::{ValidatedDefinition, coverage::TestCoverage};
use serde_json::{Value, json};

/// The campaign's test scheduling policy.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum SelectionPolicy {
    #[default]
    None,
    Prioritize(Sel),
}

/// Coverage key and domain are fixed in this version.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Sel {
    pub coupled: Coupled,
}

/// Whether coverage of any edited site or every edited site comes first.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Coupled {
    #[default]
    Union,
    AllSites,
}

impl SelectionPolicy {
    /// The exact manifest declaration; replay rebuilds scheduling from this input.
    #[must_use]
    pub fn value(self) -> Value {
        match self {
            Self::None => json!("none"),
            Self::Prioritize(selection) => json!({"prioritize": {
                "key": "compiled-rule-ids",
                "coupled": match selection.coupled {
                    Coupled::Union => "union",
                    Coupled::AllSites => "all-sites",
                },
                "coverage": kink_native::coverage::COVERAGE_DOMAIN,
            }}),
        }
    }
}

/// A compiled-side diff, computed for the actual side a test runs on.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompiledEdit {
    pub removed_rule_ids: BTreeSet<String>,
    pub global: bool,
}

impl CompiledEdit {
    /// Compares the baseline with a patched or claim-withdrawn side.
    ///
    /// Only removed and added rewrite axioms may differ. Unparseable KORE, removed
    /// equations, and additions without any removed identity select every test.
    #[must_use]
    pub fn between(baseline: &ValidatedDefinition, side: &ValidatedDefinition) -> Self {
        let left = baseline.artifacts();
        let right = side.artifacts();
        let baseline_ids = left
            .sentence_provenance
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>();
        let side_ids = right
            .sentence_provenance
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>();
        let removed_rule_ids = baseline_ids
            .difference(&side_ids)
            .cloned()
            .collect::<BTreeSet<_>>();
        let added = side_ids
            .difference(&baseline_ids)
            .cloned()
            .collect::<BTreeSet<_>>();
        let unchanged_order = left
            .execution_rewrite_order
            .iter()
            .filter(|id| !removed_rule_ids.contains(*id))
            .eq(right
                .execution_rewrite_order
                .iter()
                .filter(|id| !added.contains(*id)));
        let global = baseline.compile_options() != side.compile_options()
            || left.configuration_variables != right.configuration_variables
            || left.syntax_definition_kore != right.syntax_definition_kore
            || left.macros_kore != right.macros_kore
            || !unchanged_order
            || (removed_rule_ids.is_empty() && !added.is_empty())
            || !only_changed_rewrites(
                &left.definition_kore,
                &right.definition_kore,
                &removed_rule_ids,
                &added,
            );
        Self {
            removed_rule_ids,
            global,
        }
    }
}

/// The regenerated per-mutant schedule. Prioritize has no deselected tests.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MutantSelection {
    pub policy: SelectionPolicy,
    pub order: Vec<String>,
    pub deselected: Vec<String>,
    pub global: bool,
    pub removed_rule_ids: BTreeSet<String>,
}

impl MutantSelection {
    /// The exact report value, with no policy duplicate.
    #[must_use]
    pub fn value(&self) -> Value {
        if self.policy == SelectionPolicy::None {
            return Value::Null;
        }
        json!({
            "order": self.order,
            "deselected": self.deselected,
            "global": self.global,
            "removed_rule_ids": self.removed_rule_ids,
        })
    }
}

/// Whether one test comes first. `site_groups` contains the baseline identities
/// authored by each edited site, intersected with this actual side's removed ids.
/// The caller handles the campaign-wide empty-selection fallback.
#[must_use]
pub fn coverage_selected(
    coverage: &TestCoverage,
    edit: &CompiledEdit,
    coupled: Coupled,
    site_groups: &[BTreeSet<String>],
) -> bool {
    if !coverage.complete || edit.global {
        return true;
    }
    match coupled {
        Coupled::Union => !coverage.rule_ids.is_disjoint(&edit.removed_rule_ids),
        Coupled::AllSites => {
            !site_groups.is_empty()
                && site_groups
                    .iter()
                    .all(|ids| !coverage.rule_ids.is_disjoint(ids))
        }
    }
}

fn only_changed_rewrites(
    left: &str,
    right: &str,
    removed: &BTreeSet<String>,
    added: &BTreeSet<String>,
) -> bool {
    let (Ok(mut left), Ok(mut right)) = (parse_definition(left), parse_definition(right)) else {
        return false;
    };
    strip_changed_rewrites(&mut left, removed)
        && strip_changed_rewrites(&mut right, added)
        && left == right
}

fn rule_identity(attributes: &Attributes) -> Option<&str> {
    attributes.0.iter().find_map(|attribute| match attribute {
        Pattern::Application { symbol, arguments }
            if symbol.name == KoreAttribute::UniqueId.as_str() =>
        {
            let [Pattern::String(id)] = arguments.as_slice() else {
                return None;
            };
            id.as_utf8().ok()
        }
        _ => None,
    })
}

fn strip_changed_rewrites(definition: &mut Definition, changed: &BTreeSet<String>) -> bool {
    let mut seen = BTreeSet::new();
    let mut only_rewrites = true;
    for module in &mut definition.modules {
        module.sentences.retain(|sentence| {
            let (attributes, rewrite) = match sentence {
                Sentence::Axiom {
                    pattern,
                    attributes,
                    ..
                } => (
                    attributes,
                    matches!(pattern.as_ref(), Pattern::Rewrites { .. }),
                ),
                Sentence::Claim { attributes, .. } => (attributes, false),
                _ => return true,
            };
            let Some(id) = rule_identity(attributes).filter(|id| changed.contains(*id)) else {
                return true;
            };
            seen.insert(id.to_owned());
            only_rewrites &= rewrite;
            !rewrite
        });
    }
    only_rewrites && seen == *changed
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kore(body: &str) -> String {
        format!("[]\nmodule M\n{body}\nendmodule []")
    }

    #[test]
    fn changed_axioms_must_be_rewrites_and_all_other_kore_is_retained() {
        let left = kore(r#"axiom{} \rewrites{S{}}(a{}(), b{}()) [UNIQUE'Unds'ID{}("old")]"#);
        let right = kore(r#"axiom{} \rewrites{S{}}(a{}(), c{}()) [UNIQUE'Unds'ID{}("new")]"#);
        let removed = BTreeSet::from(["old".to_owned()]);
        let added = BTreeSet::from(["new".to_owned()]);
        assert!(only_changed_rewrites(&left, &right, &removed, &added));
        let equation = kore(r#"axiom{} \equals{S{},S{}}(a{}(), b{}()) [UNIQUE'Unds'ID{}("old")]"#);
        assert!(!only_changed_rewrites(&equation, &right, &removed, &added));
        let declaration = right.replace("module M", "module M\nsymbol z{}(): S{} []");
        assert!(!only_changed_rewrites(
            &left,
            &declaration,
            &removed,
            &added
        ));
        assert!(!only_changed_rewrites(
            "malformed",
            &right,
            &removed,
            &added
        ));
    }
}
