//! Atomic application of a [`Patch`] to a [`Baseline`].

use crate::failure::{PatchFailure, PatchFailureKind};
use crate::{Baseline, Edit, InsertPosition, Patch, Region, SentenceRef, Target, path_in};
use k_rust::definition::{AttributeKey, Definition, ResolvedDefinition, Sentence, sentence_mut};
use k_rust::kast::Term;
use k_rust::kompile::SentenceTyper;
use k_rust::outer::{LoadError, LoadedDefinition};
use std::collections::{BTreeMap, BTreeSet};
use std::mem::discriminant;
use std::sync::Arc;

/// Keys no edit may write: the rule label, kompile identities and source positions.
const PROTECTED_KEYS: [AttributeKey; 11] = [
    AttributeKey::Label,
    AttributeKey::UniqueId,
    AttributeKey::Origin,
    AttributeKey::Location,
    AttributeKey::Source,
    AttributeKey::SourceId,
    AttributeKey::SentenceStartOffset,
    AttributeKey::SentenceEndOffset,
    AttributeKey::ContentStartLine,
    AttributeKey::ContentStartColumn,
    AttributeKey::ContentStartOffset,
];

/// A patched definition. It exists only when every edit applied.
#[derive(Clone, Debug)]
pub struct Mutant {
    definition: Definition,
    origins: BTreeMap<SentenceRef, SentenceOrigin>,
}

/// Where an output sentence came from.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SentenceOrigin {
    Baseline(SentenceRef),
    /// The index of the inserting edit in [`Patch::edits`].
    Inserted {
        edit: usize,
    },
}

impl Mutant {
    #[must_use]
    pub const fn definition(&self) -> &Definition {
        &self.definition
    }

    /// Where the output sentence `output` came from.
    #[must_use]
    pub fn origin(&self, output: &SentenceRef) -> Option<&SentenceOrigin> {
        self.origins.get(output)
    }

    /// Every output sentence of every module with its origin.
    #[must_use]
    pub const fn origins(&self) -> &BTreeMap<SentenceRef, SentenceOrigin> {
        &self.origins
    }

    /// Relinks the mutant for `compile_loaded_definition`.
    ///
    /// A loaded definition cannot be fed back through `load_structured`, so
    /// the mutant reuses the baseline's files, source table and load
    /// diagnostics with its own definition
    /// (`LoadedDefinition::with_definition`), which resolves it again and
    /// checks the loaded stage.
    ///
    /// # Errors
    ///
    /// Returns k-rust's loaded-stage rejection of the mutant definition.
    pub fn to_loaded(&self, baseline: &Baseline) -> Result<LoadedDefinition, LoadError> {
        baseline.loaded().with_definition(self.definition.clone())
    }
}

/// Applies every edit of `patch` or none.
///
/// Pins are checked first, in sentence order. Every edit is checked against the immutable baseline, then edits are
/// checked against each other. The patched rule sentences are typed after
/// all edits are assembled, and no output is published unless every check passes.
///
/// # Errors
///
/// Returns the first pin failure, then the first failure in canonical edit order. A failure carries only
/// its class and a diagnostic.
pub fn apply(baseline: &Baseline, patch: &Patch) -> Result<Mutant, PatchFailure> {
    if patch.is_pinned() {
        for (at, pin) in patch.pins() {
            let current = baseline.fingerprint(at)?;
            if current != *pin {
                return Err(stale(format!(
                    "{at:?} has fingerprint {current}, not {pin}"
                )));
            }
        }
    }
    for edit in patch.edits() {
        preflight(baseline, edit)?;
    }
    check_targets(patch.edits())?;

    let mut definition = baseline.definition().clone();
    for edit in patch.edits() {
        write_in_place(&mut definition, edit)?;
    }
    let origins = rebuild_modules(&mut definition, patch.edits())?;
    let resolved = ResolvedDefinition::resolve(&definition)
        .map_err(|error| ill_formed(format!("the patched definition does not resolve: {error}")))?;
    check_edited_sentences(&definition, &resolved, &origins, patch.edits())?;
    Ok(Mutant {
        definition,
        origins,
    })
}

fn preflight(baseline: &Baseline, edit: &Edit) -> Result<(), PatchFailure> {
    match edit {
        Edit::ReplaceTerm {
            at,
            expected,
            replacement,
        } => {
            let sentence = existing(baseline, &at.sentence)?;
            let current = path_in(sentence, &at.path.0).ok_or_else(|| {
                PatchFailure::new(
                    PatchFailureKind::MalformedPath,
                    format!("{:?} does not resolve in {:?}", at.path.0, at.sentence),
                )
            })?;
            if current != expected {
                return Err(stale(format!("{at:?} holds {current}, not {expected}")));
            }
            if replacement == current {
                return Err(no_change(format!("{at:?} already holds {current}")));
            }
            Ok(())
        }
        Edit::ReplaceSentence { at, replacement } => {
            let current = existing(baseline, at)?;
            if replacement == current {
                return Err(no_change(format!("{at:?} is unchanged")));
            }
            if discriminant(replacement) != discriminant(current) {
                return Err(ill_formed(format!("{at:?} changes sentence kind")));
            }
            rule_like(replacement)?;
            for key in PROTECTED_KEYS {
                if replacement.attributes().value(key) != current.attributes().value(key) {
                    return Err(ill_formed(format!(
                        "{at:?} changes attribute {}",
                        key.as_str()
                    )));
                }
            }
            Ok(())
        }
        Edit::DeleteSentence { at } => existing(baseline, at).map(|_| ()),
        Edit::InsertSentence {
            position, sentence, ..
        } => {
            match position {
                InsertPosition::Before(anchor) | InsertPosition::After(anchor) => {
                    existing(baseline, anchor)?;
                }
                InsertPosition::ModuleStart(module) | InsertPosition::ModuleEnd(module) => {
                    if !baseline
                        .definition()
                        .modules
                        .iter()
                        .any(|candidate| &candidate.name == module)
                    {
                        return Err(stale(format!("module {module} does not exist")));
                    }
                }
            }
            rule_like(sentence)?;
            if let Some(key) = PROTECTED_KEYS
                .into_iter()
                .find(|key| sentence.attributes().has(*key))
            {
                return Err(ill_formed(format!(
                    "an inserted sentence carries {}",
                    key.as_str()
                )));
            }
            Ok(())
        }
        Edit::AddAttribute { at, key, .. } => {
            let current = existing(baseline, at)?;
            protected(key)?;
            match current.attributes().get(key) {
                Some(value) => Err(stale(format!("{at:?} already has {key} = {value}"))),
                None => Ok(()),
            }
        }
        Edit::RemoveAttribute { at, key, expected } => {
            let current = existing(baseline, at)?;
            protected(key)?;
            expect_attribute(current, at, key, expected).map(|_| ())
        }
        Edit::ReplaceAttribute {
            at,
            key,
            expected,
            replacement,
        } => {
            let current = existing(baseline, at)?;
            protected(key)?;
            if expect_attribute(current, at, key, expected)? == replacement {
                Err(no_change(format!(
                    "{at:?} already has {key} = {replacement}"
                )))
            } else {
                Ok(())
            }
        }
    }
}

/// Check the edited rule-like sentences with the same typer compilation uses.
/// A module typer is reused for every changed sentence in that module.
fn check_edited_sentences(
    definition: &Definition,
    resolved: &ResolvedDefinition,
    origins: &BTreeMap<SentenceRef, SentenceOrigin>,
    edits: &[Edit],
) -> Result<(), PatchFailure> {
    let changed = edits
        .iter()
        .filter_map(|edit| match edit {
            Edit::ReplaceTerm { at, .. } => Some(&at.sentence),
            Edit::ReplaceSentence { at, .. } => Some(at),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let mut typers = BTreeMap::new();
    for (at, origin) in origins {
        let edited = match origin {
            SentenceOrigin::Baseline(original) => changed.contains(original),
            SentenceOrigin::Inserted { .. } => true,
        };
        if !edited {
            continue;
        }
        let sentence = definition
            .modules
            .iter()
            .find(|module| module.name == at.module)
            .and_then(|module| module.local_sentences.get(at.index as usize))
            .ok_or_else(|| ill_formed(format!("{at:?} does not resolve after patching")))?;
        if !matches!(
            sentence.as_ref(),
            Sentence::Rule { .. } | Sentence::Claim { .. }
        ) {
            continue;
        }
        let typer = typers.entry(at.module.as_str()).or_insert_with(|| {
            SentenceTyper::new(resolved, &at.module).map_err(|error| ill_formed(error.to_string()))
        });
        typer
            .as_ref()
            .map_err(Clone::clone)?
            .typing(sentence)
            .map_err(|error| ill_formed(error.to_string()))?;
    }
    Ok(())
}

fn existing<'a>(baseline: &'a Baseline, at: &SentenceRef) -> Result<&'a Sentence, PatchFailure> {
    baseline
        .sentence(at)
        .ok_or_else(|| stale(format!("{at:?} does not exist")))
}

fn expect_attribute<'a>(
    sentence: &'a Sentence,
    at: &SentenceRef,
    key: &str,
    expected: &serde_json::Value,
) -> Result<&'a serde_json::Value, PatchFailure> {
    match sentence.attributes().get(key) {
        None => Err(stale(format!("{at:?} has no attribute {key}"))),
        Some(value) if value != expected => {
            Err(stale(format!("{at:?} has {key} = {value}, not {expected}")))
        }
        Some(value) => Ok(value),
    }
}

fn protected(key: &str) -> Result<(), PatchFailure> {
    if PROTECTED_KEYS
        .iter()
        .any(|protected| protected.as_str() == key)
    {
        Err(ill_formed(format!("attribute {key} cannot be edited")))
    } else {
        Ok(())
    }
}

fn rule_like(sentence: &Sentence) -> Result<(), PatchFailure> {
    match sentence {
        Sentence::Rule { .. }
        | Sentence::Claim { .. }
        | Sentence::Context { .. }
        | Sentence::ContextAlias { .. } => Ok(()),
        _ => Err(ill_formed(
            "only rules, claims and contexts can be replaced or inserted",
        )),
    }
}

/// Rejects two edits of one target, then edits whose regions nest: a term
/// path and its prefix, a whole-sentence edit and any other edit of that
/// sentence, and an insertion anchored at a deleted or replaced sentence.
fn check_targets(edits: &[Edit]) -> Result<(), PatchFailure> {
    let targets = edits.iter().map(Edit::target).collect::<Vec<_>>();
    for (index, left) in targets.iter().enumerate() {
        if let Some(right) = targets[index + 1..].iter().find(|right| *right == left) {
            return Err(PatchFailure::new(
                PatchFailureKind::DuplicateTarget,
                format!("two edits target {right:?}"),
            ));
        }
    }
    let whole = targets
        .iter()
        .filter_map(|target| match target {
            Target::Existing(at, Region::Sentence) => Some(*at),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    for (index, left) in targets.iter().enumerate() {
        for right in &targets[index + 1..] {
            let overlapping = match (left, right) {
                (Target::Existing(left_at, left), Target::Existing(right_at, right))
                    if left_at == right_at =>
                {
                    match (left, right) {
                        (Region::Sentence, _) | (_, Region::Sentence) => true,
                        (Region::Term(left), Region::Term(right)) => {
                            left.starts_with(right) || right.starts_with(left)
                        }
                        _ => false,
                    }
                }
                _ => false,
            };
            if overlapping {
                return Err(overlap(format!("{left:?} overlaps {right:?}")));
            }
        }
        if let Target::Slot(InsertPosition::Before(anchor) | InsertPosition::After(anchor), _) =
            left
            && whole.contains(anchor)
        {
            return Err(overlap(format!(
                "{left:?} is anchored at a deleted or replaced sentence"
            )));
        }
    }
    Ok(())
}

/// Applies term, attribute and sentence replacements in baseline coordinates.
fn write_in_place(definition: &mut Definition, edit: &Edit) -> Result<(), PatchFailure> {
    let at = match edit {
        Edit::ReplaceTerm { at, .. } => &at.sentence,
        Edit::ReplaceSentence { at, .. }
        | Edit::AddAttribute { at, .. }
        | Edit::RemoveAttribute { at, .. }
        | Edit::ReplaceAttribute { at, .. } => at,
        Edit::DeleteSentence { .. } | Edit::InsertSentence { .. } => return Ok(()),
    };
    let slot = definition
        .modules
        .iter_mut()
        .find(|module| module.name == at.module)
        .and_then(|module| {
            module
                .local_sentences
                .get_mut(usize::try_from(at.index).ok()?)
        })
        .ok_or_else(|| stale(format!("{at:?} does not exist")))?;
    match edit {
        Edit::ReplaceTerm {
            at, replacement, ..
        } => {
            let term = term_mut(sentence_mut(slot), &at.path.0).ok_or_else(|| {
                PatchFailure::new(
                    PatchFailureKind::MalformedPath,
                    format!("{at:?} does not resolve"),
                )
            })?;
            *term = replacement.clone();
        }
        Edit::ReplaceSentence { replacement, .. } => *slot = Arc::new(replacement.clone()),
        Edit::AddAttribute { key, value, .. } => {
            sentence_mut(slot)
                .attributes_mut()
                .insert(key.clone(), value.clone());
        }
        Edit::RemoveAttribute { key, .. } => {
            sentence_mut(slot).attributes_mut().remove(key);
        }
        Edit::ReplaceAttribute {
            key, replacement, ..
        } => {
            sentence_mut(slot)
                .attributes_mut()
                .insert(key.clone(), replacement.clone());
        }
        Edit::DeleteSentence { .. } | Edit::InsertSentence { .. } => {}
    }
    Ok(())
}

fn term_mut<'a>(sentence: &'a mut Sentence, path: &[u32]) -> Option<&'a mut Term> {
    let (field, steps) = path.split_first()?;
    let mut term = match (sentence, field) {
        (
            Sentence::Rule { body, .. }
            | Sentence::Claim { body, .. }
            | Sentence::Context { body, .. }
            | Sentence::ContextAlias { body, .. }
            | Sentence::Configuration { body, .. },
            0,
        ) => body,
        (
            Sentence::Rule { requires, .. }
            | Sentence::Claim { requires, .. }
            | Sentence::Context { requires, .. }
            | Sentence::ContextAlias { requires, .. },
            1,
        ) => requires,
        (Sentence::Configuration { ensures, .. }, 1)
        | (Sentence::Rule { ensures, .. } | Sentence::Claim { ensures, .. }, 2) => ensures,
        _ => return None,
    };
    for step in steps {
        let step = usize::try_from(*step).ok()?;
        term = match unannotated_mut(term) {
            Term::Rewrite { left, right } => match step {
                0 => left,
                1 => right,
                _ => return None,
            },
            Term::As { pattern, alias } => match step {
                0 => pattern,
                1 => alias,
                _ => return None,
            },
            Term::Apply { arguments, .. } | Term::Sequence(arguments) => arguments.get_mut(step)?,
            _ => return None,
        };
    }
    Some(term)
}

/// The mutable twin of `Term::unannotated`.
fn unannotated_mut(mut term: &mut Term) -> &mut Term {
    while let Term::Annotated { term: inner, .. } = term {
        term = inner;
    }
    term
}

/// Deletes and inserts sentences, rebuilding each touched module once from
/// the baseline order, and records every output sentence's origin.
fn rebuild_modules(
    definition: &mut Definition,
    edits: &[Edit],
) -> Result<BTreeMap<SentenceRef, SentenceOrigin>, PatchFailure> {
    let mut deleted = BTreeSet::new();
    let mut inserted = BTreeMap::<&InsertPosition, Vec<(usize, &Sentence)>>::new();
    for (index, edit) in edits.iter().enumerate() {
        match edit {
            Edit::DeleteSentence { at } => {
                deleted.insert(at);
            }
            // Edits are canonical, so each slot's list is in ordinal order.
            Edit::InsertSentence {
                position, sentence, ..
            } => inserted
                .entry(position)
                .or_default()
                .push((index, sentence)),
            _ => {}
        }
    }
    let mut origins = BTreeMap::new();
    for module in &mut definition.modules {
        let name = module.name.clone();
        let baseline = std::mem::take(&mut module.local_sentences);
        let mut output = Vec::with_capacity(baseline.len());
        let place = |output: &mut Vec<_>, position: &InsertPosition| {
            for (edit, sentence) in inserted.get(position).into_iter().flatten() {
                output.push((
                    Arc::new((*sentence).clone()),
                    SentenceOrigin::Inserted { edit: *edit },
                ));
            }
        };
        place(&mut output, &InsertPosition::ModuleStart(name.clone()));
        for (index, sentence) in baseline.into_iter().enumerate() {
            let at = SentenceRef::new(name.clone(), output_index(index)?);
            place(&mut output, &InsertPosition::Before(at.clone()));
            let after = InsertPosition::After(at.clone());
            if !deleted.contains(&at) {
                output.push((sentence, SentenceOrigin::Baseline(at)));
            }
            place(&mut output, &after);
        }
        place(&mut output, &InsertPosition::ModuleEnd(name.clone()));
        for (index, (sentence, origin)) in output.into_iter().enumerate() {
            module.local_sentences.push(sentence);
            origins.insert(SentenceRef::new(name.clone(), output_index(index)?), origin);
        }
    }
    Ok(origins)
}

fn output_index(index: usize) -> Result<u32, PatchFailure> {
    u32::try_from(index).map_err(|_| ill_formed("a module has more than u32::MAX sentences"))
}

fn stale(detail: impl Into<String>) -> PatchFailure {
    PatchFailure::new(PatchFailureKind::StalePrecondition, detail)
}

fn no_change(detail: impl Into<String>) -> PatchFailure {
    PatchFailure::new(PatchFailureKind::NoChange, detail)
}

fn overlap(detail: impl Into<String>) -> PatchFailure {
    PatchFailure::new(PatchFailureKind::OverlappingEdit, detail)
}

fn ill_formed(detail: impl Into<String>) -> PatchFailure {
    PatchFailure::new(PatchFailureKind::LocallyIllFormed, detail)
}
