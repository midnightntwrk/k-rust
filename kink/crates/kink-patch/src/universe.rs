//! Declared rule universes and deterministic, explicitly listed exclusions.

use crate::typing::CompilationTyping;
use crate::{Baseline, SentenceRef, Sha256Digest, canonical_json, payload_digest};
use k_rust::definition::{AttributeKey, Sentence};
use k_rust::kast::Term;
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

/// The predicates defining a v1 rule universe.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Universe {
    /// V1 discovery requires an authored-rule declaration.
    pub authored: bool,
    /// Whether the resolution reads each included rule's typing, to record the rules no typing
    /// view types ([`ResolvedUniverse::unsorted`]). A typing error excludes no rule (packet
    /// L2-2-fix-1): typing only gives site sorts.
    pub typed: bool,
    pub exclude_attributes: Vec<String>,
    pub exclude_macro_rules: bool,
}

impl Universe {
    #[must_use]
    pub fn v1() -> Self {
        Self {
            authored: true,
            typed: true,
            exclude_attributes: vec!["simplification".to_owned(), "smt-lemma".to_owned()],
            exclude_macro_rules: true,
        }
    }
}

/// The first applicable reason a rule is outside the declared universe.
///
/// No reason is a typing error. Until L2-2-fix-1 a rule its typing view did not type was
/// excluded as `Untyped`; it is now included (on a baseline that compiles, a typing error is no
/// evidence against the rule), and a rule no view types is recorded in
/// [`ResolvedUniverse::unsorted`] instead.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExclusionReason {
    Attribute(String),
    MacroRule,
}

impl ExclusionReason {
    fn text(&self) -> String {
        match self {
            Self::Attribute(key) => format!("attribute:{key}"),
            Self::MacroRule => "macro-rule".to_owned(),
        }
    }
}

/// A resolved declaration, with both partitions in sentence order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedUniverse {
    declaration: Universe,
    included: Vec<SentenceRef>,
    excluded: Vec<(SentenceRef, ExclusionReason)>,
    unsorted: Vec<SentenceRef>,
    typing_refused: Vec<(SentenceRef, String)>,
}

impl ResolvedUniverse {
    #[must_use]
    pub fn included(&self) -> &[SentenceRef] {
        &self.included
    }

    #[must_use]
    pub fn excluded(&self) -> &[(SentenceRef, ExclusionReason)] {
        &self.excluded
    }

    /// The included rules that no typing view types (neither compilation's view nor the
    /// declaring module's own), in sentence order: their sites have no sort, so a sort-selected
    /// discovery skips them and is not exhaustive. Empty unless the declaration is `typed`. It
    /// is derived from the baseline, like every other part, and is not in [`Self::value`].
    #[must_use]
    pub fn unsorted(&self) -> &[SentenceRef] {
        &self.unsorted
    }

    /// The unsorted rules whose typing segment was refused, each with the refusal, in sentence
    /// order: a rule too deep for the largest stack segment kink maps (kink's limit) or one whose
    /// segment the system would not map (the host's, which another host may grant). Such a rule
    /// is in [`Self::unsorted`] like any rule no view types, and this names why (re-pin L1-4,
    /// review L1-3-tail-1 D3: it was silent). Not in [`Self::value`].
    #[must_use]
    pub fn typing_refusals(&self) -> &[(SentenceRef, String)] {
        &self.typing_refused
    }

    fn excluded_value(&self) -> Value {
        Value::Array(
            self.excluded
                .iter()
                .map(|(at, reason)| {
                    json!({"module": at.module, "index": at.index, "reason": reason.text()})
                })
                .collect(),
        )
    }

    #[must_use]
    pub fn excluded_digest(&self) -> Sha256Digest {
        payload_digest(
            "kink/universe-excluded/v1",
            canonical_json(&self.excluded_value()).as_bytes(),
        )
    }

    #[must_use]
    pub fn value(&self) -> Value {
        json!({
            "kinds": ["rule"],
            "authored": self.declaration.authored,
            "typed": self.declaration.typed,
            "exclude_attributes": self.declaration.exclude_attributes,
            "exclude_macro_rules": self.declaration.exclude_macro_rules,
            "excluded": self.excluded_value(),
            "excluded_sha256": self.excluded_digest().to_string(),
        })
    }

    pub(crate) fn matches_baseline(&self, baseline: &Baseline) -> bool {
        self.declaration.authored && *self == resolve_universe(baseline, &self.declaration)
    }
}

/// Resolves the declaration. No typing error excludes a rule: a mutant is valid when it
/// compiles, and k-rust's typing view refuses rules compilation accepts (packet L2-2-fix-1; the
/// crate docs give the counterexample). Typing only places site sorts: compilation's view (one
/// `SentenceTyper::for_compilation` of the baseline, `typing_in` the declaring module), else the
/// declaring module's own view, as before L2-2. A rule that neither types (a `CellCompletion`
/// shape, or the lubmain shape) is included and recorded in [`ResolvedUniverse::unsorted`].
#[must_use]
pub fn resolve_universe(baseline: &Baseline, universe: &Universe) -> ResolvedUniverse {
    let mut typing = universe
        .typed
        .then(|| CompilationTyping::new(baseline.loaded().resolved()));
    let mut macro_heads = BTreeMap::new();
    let mut included = Vec::new();
    let mut excluded = Vec::new();
    let mut unsorted = Vec::new();
    let mut typing_refused = Vec::new();
    for (at, sentence) in baseline.authored_sentences() {
        let Sentence::Rule {
            body, attributes, ..
        } = sentence
        else {
            continue;
        };
        let reason = if let Some(key) = universe
            .exclude_attributes
            .iter()
            .find(|key| attributes.get(key).is_some())
        {
            Some(ExclusionReason::Attribute(key.clone()))
        } else if universe.exclude_macro_rules && {
            let heads = macro_heads
                .entry(at.module.clone())
                .or_insert_with(|| macro_labels(baseline, &at.module));
            let left = match body.unannotated() {
                Term::Rewrite { left, .. } => left,
                body => body,
            };
            head(left).is_some_and(|head| heads.contains(head))
        } {
            Some(ExclusionReason::MacroRule)
        } else {
            None
        };
        if let Some(reason) = reason {
            excluded.push((at, reason));
        } else {
            match typing
                .as_mut()
                .map(|typing| typing.site_typing(sentence, &at.module))
            {
                Some(Ok(None)) => unsorted.push(at.clone()),
                Some(Err(refusal)) => {
                    unsorted.push(at.clone());
                    typing_refused.push((at.clone(), refusal.to_string()));
                }
                Some(Ok(Some(_))) | None => {}
            }
            included.push(at);
        }
    }
    included.sort();
    excluded.sort_by(|left, right| left.0.cmp(&right.0));
    unsorted.sort();
    typing_refused.sort();
    ResolvedUniverse {
        declaration: universe.clone(),
        included,
        excluded,
        unsorted,
        typing_refused,
    }
}

fn macro_labels(baseline: &Baseline, module: &str) -> BTreeSet<String> {
    let resolved = baseline.loaded().resolved();
    let Some(module) = resolved.module_id(module) else {
        return BTreeSet::new();
    };
    resolved
        .signature_sentences(module)
        .into_iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } if attributes.has_any(&AttributeKey::MACRO_LIKE) => Some(label.name.clone()),
            _ => None,
        })
        .collect()
}

fn head(term: &Term) -> Option<&str> {
    match term.unannotated() {
        Term::As { pattern, .. } => head(pattern),
        Term::Apply { label, arguments } if label.semantic_cast_sort().is_some() => {
            head(arguments.first()?)
        }
        Term::Apply { label, .. } => Some(&label.name),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Discovery, SiteSelector, derive_sites_in, typing::SITE_TYPING_PER_LEVEL};
    use k_rust::{
        builtin,
        kast::Sort,
        kompile::CompilationBackend,
        outer::{LoadOptions, ResolvedSource},
    };

    const GUARDED: &str = r#"module GUARDED
  imports INT
  imports BOOL
  syntax KItem ::= go(Int) | done(Int)
  rule [positive]: go(N) => done(N) requires N >Int 0
  rule [other]: go(N) => done(0 -Int N) requires N <=Int 0
endmodule
"#;

    fn guarded() -> Baseline {
        let mut resolver = |_: &str, name: &str| {
            builtin::embedded(name).ok_or_else(|| format!("{name} is not embedded"))
        };
        Baseline::load(
            ResolvedSource::new("guarded.k", GUARDED),
            "GUARDED",
            None,
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![
                    builtin::embedded("kast.md").expect("kast.md is embedded"),
                    builtin::embedded("prelude.md").expect("prelude.md is embedded"),
                ],
                excluded_module_attributes: vec![
                    CompilationBackend::Rust
                        .excluded_module_attribute()
                        .to_owned(),
                ],
                ..LoadOptions::default()
            },
        )
        .expect("inline fixture loads")
    }

    /// Re-pin L1-4 (review L1-3-tail-1 D3): a baseline rule whose typing segment is refused is
    /// unsorted, as before, and the universe and a sort-selected discovery now name the refusal
    /// (here kink's limit, forced by a per-level bound past the largest segment kink maps; a
    /// segment the system will not map is the host's and is named the same way). With the bound
    /// as built, neither names anything and every rule is sorted.
    #[test]
    fn a_refused_typing_segment_is_named_in_the_universe_and_the_discovery() {
        let baseline = guarded();
        let selector = [
            SiteSelector::Path(vec![1]),
            SiteSelector::Sort(Sort::new("Bool")),
        ];
        let universe = resolve_universe(&baseline, &Universe::v1());
        assert_eq!(universe.included().len(), 2);
        assert_eq!(universe.unsorted(), &[]);
        assert_eq!(universe.typing_refusals(), &[]);
        let discovery = derive_sites_in(&baseline, &universe, &selector).expect("sites");
        assert!(discovery.exhaustive());
        assert_eq!(discovery.tuples().len(), 2);
        assert_eq!(discovery.typing_refusals(), &[]);

        SITE_TYPING_PER_LEVEL.with(|bound| bound.set(usize::MAX / 1024));
        let refused = resolve_universe(&baseline, &Universe::v1());
        let discovery = derive_sites_in(&baseline, &refused, &selector).expect("sites");
        SITE_TYPING_PER_LEVEL.with(|bound| bound.set(crate::stack::TYPING_STACK_PER_LEVEL));
        assert_eq!(refused.included(), universe.included());
        assert_eq!(refused.unsorted(), universe.included());
        assert_eq!(
            refused
                .typing_refusals()
                .iter()
                .map(|(at, _)| at.clone())
                .collect::<Vec<_>>(),
            universe.included()
        );
        for (_, refusal) in refused.typing_refusals() {
            assert!(
                refusal.contains("more than the")
                    && refusal.contains("largest stack segment kink maps"),
                "{refusal}"
            );
        }
        assert!(!discovery.exhaustive());
        assert!(discovery.tuples().is_empty());
        assert_eq!(discovery.typing_refusals(), refused.typing_refusals());
        // A union keeps the cause.
        let united = discovery
            .union(&Discovery::empty(&baseline, false, false))
            .expect("same shape");
        assert_eq!(united.typing_refusals(), refused.typing_refusals());
        assert!(!united.exhaustive());
    }
}
