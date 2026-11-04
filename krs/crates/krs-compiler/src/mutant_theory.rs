//! The theory check of a K mutation of a definition KRS emitted: KRS's own rule-level admission
//! checks run on the mutant's pre-derivation theory.
//!
//! A mutation that the judge and the re-derivation accept stands for one Rust source `P'`: the
//! specification `P` with each edited sentence's authored syntax changed and everything else
//! kept, including the keys that emit nothing (a `nondet = NAME` group). The re-derivation gives
//! each edited sentence's pre-derivation form `A'`, which is what `P'` lowers that sentence to;
//! every other sentence of `P'` lowers as in `P`. So the modules the admission checks take when
//! KRS lowers `P'` are the baseline's with each edited sentence replaced by its `A'` and each
//! deleted sentence removed, in the baseline's order, and running KRS's checks on them gives
//! KRS's verdict on `P'`, its first refusal included.
//!
//! The checks are KRS's, run unchanged ([`crate::semantic::admit_sentences`]): the per-sentence
//! checks lowering makes before resolution (a fresh binder's generator, a heat or cool rule's
//! hole), then the rule-level tail (smtlib symbols, equation restrictions, or-pattern positions,
//! list patterns, smt lemmas, result sorts, the static rewriting, proof visibility, spec lemmas
//! and identifiers, the overlap of transitions and their nondet groups, `priority-after-owise`,
//! the overlap of equations and of match arms). Overlap is never restated over K: a second
//! implementation would drift from KRS's in both directions, and nothing would show where.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

use krs_diagnostic::ToDiagnostic;
use krs_ir::{DescriptorIndex, SentenceKind, SourceMapKey, SourceRange, StableItemId};
use krs_ir_levels::{SemanticModule, SemanticRule};

use crate::semantic::{DescriptorLoweringError, RetainedLowering};

/// The sentence key of a pre-derivation rule: the key a re-derivation's [`crate::Site`] and the
/// theory check name it by.
#[must_use]
pub fn rule_sentence_key(rule: &SemanticRule) -> &SourceMapKey {
    crate::rederivation::sentence_key(rule)
}

/// What a mutation changes in the pre-derivation theory, by sentence key
/// ([`rule_sentence_key`]).
#[derive(Clone, Debug, Default)]
pub struct TheoryChanges {
    /// Each edited sentence's pre-derivation form `A'`, as the re-derivation built it.
    pub replaced: BTreeMap<SourceMapKey, SemanticRule>,
    /// The sentences the mutation deletes.
    pub deleted: BTreeSet<SourceMapKey>,
}

impl TheoryChanges {
    /// Whether the changes change nothing.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.replaced.is_empty() && self.deleted.is_empty()
    }
}

/// KRS's refusal of the source a mutation stands for.
#[derive(Debug)]
pub struct TheoryRefusal {
    /// The registered diagnostic code (`krs::analysis::overlapping-rule-heads`, ...).
    pub code: &'static str,
    /// The diagnostic's message, as `krs check` prints it after the code.
    pub message: String,
    /// The items the error names, in its order: the first and second of an overlap, the rule
    /// and the `owise` sentence of `priority-after-owise`, the rule of a nondet-group or
    /// or-pattern error, else its subject.
    pub items: Vec<StableItemId>,
    /// The sentences of the checked theory those items lower to, by sentence key, in the
    /// items' order and, for one item, in theory order.
    pub sentences: Vec<SourceMapKey>,
    /// The error's range (a head, a priority, an arm), when it has one.
    pub range: Option<SourceRange>,
    /// The error itself.
    pub error: Box<DescriptorLoweringError>,
}

/// Why a mutation's theory is not checked.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum TheoryCheckError {
    /// A changed sentence is not a rule of the checked modules.
    UnknownSentence(SourceMapKey),
    /// A changed sentence is an alias or desugar clause: the static rewriting reads it, and the
    /// re-derivation's `A'` is the form after that rewriting, not the clause the checks take.
    StaticClause(SourceMapKey),
    /// A replaced sentence names a framework item while the baseline lowered no framework
    /// module: the source would keep a module the mutant lacks.
    FrameworkUse(SourceMapKey),
    /// KRS's refusal carries a code its registry does not hold.
    UnregisteredCode(String),
}

impl fmt::Display for TheoryCheckError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownSentence(key) => {
                write!(formatter, "{key} is no rule sentence of the checked theory")
            }
            Self::StaticClause(key) => write!(
                formatter,
                "{key} is an alias or desugar clause, which the static rewriting reads; an edit \
                 of one is not checked"
            ),
            Self::FrameworkUse(key) => write!(
                formatter,
                "{key} names a framework item, and the specification lowers no framework module"
            ),
            Self::UnregisteredCode(code) => {
                write!(formatter, "KRS's refusal has the unregistered code {code}")
            }
        }
    }
}

impl Error for TheoryCheckError {}

/// The theory check over one baseline lowering.
pub struct MutantTheory<'a> {
    retained: &'a RetainedLowering,
    declarations: DescriptorIndex<'a>,
    /// Each rule of the checked modules, by sentence key, with its module and place.
    places: BTreeMap<SourceMapKey, (usize, usize)>,
    /// Whether the checked modules hold a framework module.
    framework: bool,
}

impl<'a> MutantTheory<'a> {
    /// The check over `retained`, which must be a lowering that kept what it computes
    /// ([`crate::lower_descriptor_bundle_retained`]).
    #[must_use]
    pub fn new(retained: &'a RetainedLowering) -> Self {
        let places = retained
            .admitted()
            .iter()
            .enumerate()
            .flat_map(|(module, semantic)| {
                semantic
                    .rules()
                    .iter()
                    .enumerate()
                    .map(move |(place, rule)| (rule_sentence_key(rule).clone(), (module, place)))
            })
            .collect();
        Self {
            retained,
            declarations: DescriptorIndex::from_descriptors(retained.descriptors().iter()),
            places,
            framework: retained
                .admitted()
                .iter()
                .any(|module| crate::partition::is_framework_module(module.id())),
        }
    }

    /// KRS's verdict on the source that `changes` of the baseline stand for: `Ok(())` when KRS
    /// admits its rules, else KRS's first refusal.
    ///
    /// # Errors
    ///
    /// [`TheoryCheckError`] when the changes are not checked here.
    pub fn check(
        &self,
        changes: &TheoryChanges,
    ) -> Result<Result<(), TheoryRefusal>, TheoryCheckError> {
        let admitted = self.retained.admitted();
        let mut by_module = BTreeMap::<usize, BTreeMap<usize, Option<&SemanticRule>>>::new();
        let edits = changes
            .replaced
            .iter()
            .map(|(key, rule)| (key, Some(rule)))
            .chain(changes.deleted.iter().map(|key| (key, None)));
        for (key, replacement) in edits {
            let &(module, place) = self
                .places
                .get(key)
                .ok_or_else(|| TheoryCheckError::UnknownSentence(key.clone()))?;
            let baseline = &admitted[module].rules()[place];
            if matches!(baseline.kind(), SentenceKind::Alias | SentenceKind::Desugar) {
                return Err(TheoryCheckError::StaticClause(key.clone()));
            }
            if let Some(rule) = replacement
                && !self.framework
                && serde_json::to_value(rule)
                    .is_ok_and(|value| crate::semantic::names_framework_item(&value))
            {
                return Err(TheoryCheckError::FrameworkUse(key.clone()));
            }
            // A deletion and a replacement of one sentence: the deletion wins, as a deleted
            // sentence has no form.
            let entry = by_module.entry(module).or_default();
            match replacement {
                None => {
                    entry.insert(place, None);
                }
                Some(rule) => {
                    entry.entry(place).or_insert(Some(rule));
                }
            }
        }
        let modules = admitted
            .iter()
            .enumerate()
            .map(|(index, module)| match by_module.get(&index) {
                None => module.clone(),
                Some(places) => {
                    let rules = module
                        .rules()
                        .iter()
                        .enumerate()
                        .filter_map(|(place, rule)| match places.get(&place) {
                            None => Some(rule.clone()),
                            Some(replacement) => replacement.cloned(),
                        })
                        .collect();
                    module.clone().with_rules(rules)
                }
            })
            .collect::<Vec<SemanticModule>>();
        match crate::semantic::admit_sentences(
            modules,
            &self.declarations,
            self.retained.sort_parents(),
        ) {
            Ok(_) => Ok(Ok(())),
            Err(error) => self.refusal(error, changes).map(Err),
        }
    }

    /// KRS's refusal `error` of the theory `changes` of the baseline give, with the sentences it
    /// names. The checked theory is the baseline's rules in their order, each replaced or
    /// removed as `changes` says, so its sentences are read from the baseline and `changes`
    /// rather than from a copy kept for a refusal.
    fn refusal(
        &self,
        error: DescriptorLoweringError,
        changes: &TheoryChanges,
    ) -> Result<TheoryRefusal, TheoryCheckError> {
        let diagnostic = error.to_diagnostic();
        let code = krs_diagnostic::codes::static_spelling(diagnostic.code.as_str())
            .ok_or_else(|| TheoryCheckError::UnregisteredCode(diagnostic.code.to_string()))?;
        let items = named_items(&error);
        let checked = self
            .retained
            .admitted()
            .iter()
            .flat_map(SemanticModule::rules)
            .filter_map(|rule| {
                let key = rule_sentence_key(rule);
                if changes.deleted.contains(key) {
                    return None;
                }
                Some((key, changes.replaced.get(key).unwrap_or(rule)))
            })
            .collect::<Vec<_>>();
        let sentences = items
            .iter()
            .flat_map(|item| {
                checked
                    .iter()
                    .filter(move |(_, rule)| rule.id() == item)
                    .map(|(key, _)| (*key).clone())
            })
            .collect();
        Ok(TheoryRefusal {
            code,
            message: diagnostic.message,
            items,
            sentences,
            range: error.range().cloned(),
            error: Box::new(error),
        })
    }
}

/// The items `error` names, in its order ([`TheoryRefusal::items`]).
fn named_items(error: &DescriptorLoweringError) -> Vec<StableItemId> {
    match error {
        DescriptorLoweringError::OverlappingRules { first, second, .. }
        | DescriptorLoweringError::OverlappingEquations { first, second, .. }
        | DescriptorLoweringError::OverlappingMatchArms { first, second, .. } => {
            vec![first.as_ref().clone(), second.as_ref().clone()]
        }
        DescriptorLoweringError::PriorityAfterOwise { rule, owise, .. } => {
            vec![rule.as_ref().clone(), owise.as_ref().clone()]
        }
        other => other.subject_item().cloned().into_iter().collect(),
    }
}
