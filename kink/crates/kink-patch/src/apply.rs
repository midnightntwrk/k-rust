//! Atomic application of a [`Patch`] to a [`Baseline`].
//!
//! [`apply`] checks that each edit applies and resolves, not that some K text parses to the
//! edited sentence: a structural edit (an operator's `ReplaceHead` or `Wrap`, a catalogue
//! operator, a `Patch` built from terms) is held only to compilation afterwards, so it can build
//! a mutant no K text yields (decisions log 2026-10-18, STRUCT-SORT parked; `trust.md`, "What a
//! kill trusts"). kink-flow's text edits are parsed by K's parser before they become a patch.

use crate::failure::{PatchFailure, PatchFailureKind};
use crate::stack::{TYPING_STACK_PER_LEVEL, sentence_depth, with_stack};
use crate::typing::CompilationTyping;
use crate::{
    Baseline, Edit, InsertPosition, Patch, Region, SentenceRef, Target, path_in, sentence_at,
};
use k_rust::definition::{
    AttributeKey, Definition, ResolvedDefinition, Sentence, production_identity, sentence_mut,
};
use k_rust::inner::ProgramParser;
use k_rust::kast::{ProductionIdentity, Term, TermParts};
use k_rust::kompile::initial_configuration::ProgramGrammar;
use k_rust::outer::{LoadError, LoadedDefinition};
use std::collections::{BTreeMap, BTreeSet};
use std::mem::discriminant;
use std::sync::Arc;

/// The version of the rule by which [`apply`] admits a patch before compilation: a mutant's
/// admission depends on it, so kink's semantics identity names it (kink-campaign `identity`).
/// Bump it whenever apply, or the typing it records, starts or stops refusing a patch.
/// v1 (re-pin L2-2-fix-1, L2-2 review 2 minor 1): no typing error refuses a patch; apply refuses
/// only an edit that does not apply or resolve, records the edited rules' typing errors in
/// compilation's view as [`Mutant::typing_diagnostics`], and compilation decides whether the
/// mutant is valid. Builds before packet CACHE-ID name no version: 1ee9955 refused a typing
/// error in the module's own view, and 977dc0c (L2-2) a Sort or semantic-cast error in
/// compilation's view.
/// v2 (PJ-34, U34a): a production, a lexical declaration, a priority declaration or an
/// associativity declaration may be replaced (by one of its own variant) or inserted, where only
/// rules, claims and contexts could before; every other check is unchanged. Extended before
/// release (PJ-34, U34c): a production replaced in place has another content identity, and every
/// term built with the baseline's production is pointed at its replacement, where it named a
/// production the mutant does not declare (which compilation, under debug assertions, refused by
/// a panic); no patch is admitted or refused otherwise. Extended again before release (PJ-34,
/// FX2): the retarget is per module, a term pointed at a replacement only in a module that no
/// longer sees the replaced production and sees exactly one replacement, where it was pointed at
/// the replacement in every module (a module that still saw an equivalent copy of the replaced
/// production elsewhere was given an identity it cannot see); no patch is admitted or refused
/// otherwise.
pub const PATCH_ADMISSION_VERSION: &str = "kink-patch/patch-admission/v2";

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
    typing_diagnostics: Vec<TypingDiagnostic>,
}

/// A typing error of an edited or inserted rule or claim in compilation's typing view (one
/// `SentenceTyper::for_compilation` of the patched definition, `typing_in` the sentence's
/// module). A diagnostic only: it refuses nothing, and compilation decides whether the mutant is
/// valid (packet L2-2-fix-1; the view refuses shapes compilation accepts, see the crate docs).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypingDiagnostic {
    /// The output sentence, in the mutant's coordinates.
    pub at: SentenceRef,
    /// Where it came from: the edited baseline sentence, or the inserting edit.
    pub origin: SentenceOrigin,
    /// The typer's message.
    pub message: String,
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

    /// The typing errors of the edited and inserted rules and claims in compilation's view, in
    /// sentence order; empty when each of them types there or lies outside the main module's
    /// import closure. Diagnostics only: compilation decides.
    #[must_use]
    pub fn typing_diagnostics(&self) -> &[TypingDiagnostic] {
        &self.typing_diagnostics
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

    /// Every application in the mutant's sentences whose production identity the production
    /// catalog of its module does not hold, as `label in module`, in module and sentence order:
    /// the check k-rust's compilation makes of every stage's output under debug assertions
    /// (`assert_no_dangling_application_identities`), made before compilation. A deleted
    /// production that a rule still applies leaves one; so does a retarget that found no single
    /// replacement ([`apply`]). Empty for a mutant whose terms all name productions their module
    /// sees, and for one that does not resolve (compilation then refuses it).
    #[must_use]
    pub fn dangling_applications(&self) -> Vec<String> {
        let Ok(resolved) = ResolvedDefinition::resolve(&self.definition) else {
            return Vec::new();
        };
        let mut dangling = Vec::new();
        for (module_id, module) in resolved.modules() {
            let catalog = resolved.production_catalog(module_id);
            for sentence in &module.local_sentences {
                for (_, term) in sentence.terms() {
                    unseen_applications(
                        term,
                        &|identity| catalog.lookup(identity).is_some(),
                        &mut |label| {
                            dangling.push(format!("{label} in {}", module.name));
                        },
                    );
                }
            }
        }
        dangling
    }

    /// Whether k-rust builds the program parser of `syntax_module` from the mutant's definition:
    /// the parser a program text (`$PGM`) is read with. It is built as initial-configuration
    /// assembly builds it (k-rust `ProgramGrammar::new` of the loaded definition, then
    /// `ProgramParser::from_resolved` of its resolution at the syntax module; kink-corpus
    /// `InputGrammar::prepare` and `ConfigurationAssembler::program_file`), so a refusal here is
    /// the definition's fault that kink-corpus reports as `InputError::Grammar` for a program,
    /// never a program that does not parse. The syntax module is the caller's: a [`Baseline`]
    /// does not keep it.
    ///
    /// # Errors
    ///
    /// [`PatchFailureKind::NoProgramParser`] with k-rust's reason.
    pub fn program_parser(&self, syntax_module: &str) -> Result<(), PatchFailure> {
        let no_parser =
            |detail: String| PatchFailure::new(PatchFailureKind::NoProgramParser, detail);
        let grammar =
            ProgramGrammar::new(&self.definition).map_err(|error| no_parser(error.to_string()))?;
        ProgramParser::from_resolved(grammar.resolved(), syntax_module)
            .map(|_| ())
            .map_err(|error| no_parser(error.to_string()))
    }
}

/// Applies every edit of `patch` or none.
///
/// Pins are checked first, in sentence order. Every edit is checked against the immutable baseline, then edits are
/// checked against each other. No output is published unless every check passes. No check is a
/// typing check: the edited rules and claims are typed in compilation's view after all edits are
/// assembled, and a typing error is only recorded ([`Mutant::typing_diagnostics`]); compilation
/// decides whether the mutant is valid.
///
/// A replaced or inserted sentence is a rule, a claim, a context, or one of the sentences that
/// define a grammar's text: a production (a token definition among them), a lexical
/// declaration, or a priority or associativity declaration (PJ-34). Sort and sort-synonym
/// declarations, configurations and bubbles are refused. A grammar edit is held, as every edit
/// is, only to applying and resolving here and to compilation afterwards; whether the mutant's
/// grammar still gives a program parser is [`Mutant::program_parser`]'s question.
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
    let replaced = replaced_productions(baseline, patch, &definition, &origins);
    retarget_productions(&mut definition, &replaced)?;
    let resolved = ResolvedDefinition::resolve(&definition)
        .map_err(|error| ill_formed(format!("the patched definition does not resolve: {error}")))?;
    let typing_diagnostics = typing_diagnostics(&definition, &resolved, &origins, patch.edits())?;
    Ok(Mutant {
        definition,
        origins,
        typing_diagnostics,
    })
}

/// The content identity (k-rust `production_identity`) of each baseline production the patch
/// changed in place, mapped to its outputs': a replaced production (a grammar edit that keeps its
/// label and changes a literal, a regex or an attribute) has another identity, and every term
/// built with it names the old one in its metadata. Two equivalent productions of two modules
/// share an identity, so one identity may have several replacements. Only the sentences the
/// patch writes are read, so a patch that edits rules only hashes no production and gives an
/// empty map.
fn replaced_productions(
    baseline: &Baseline,
    patch: &Patch,
    definition: &Definition,
    origins: &BTreeMap<SentenceRef, SentenceOrigin>,
) -> BTreeMap<ProductionIdentity, BTreeSet<ProductionIdentity>> {
    let edited = patch
        .written_sentences()
        .into_iter()
        .filter_map(|at| {
            let before = baseline.sentence(&at)?;
            matches!(before, Sentence::Production { .. })
                .then(|| production_identity(before))
                .flatten()
                .map(|identity| (at, identity))
        })
        .collect::<BTreeMap<_, _>>();
    let mut replaced = BTreeMap::new();
    if edited.is_empty() {
        return replaced;
    }
    for (output, origin) in origins {
        let SentenceOrigin::Baseline(source) = origin else {
            continue;
        };
        if let Some(old) = edited.get(source)
            && let Some(after) = sentence_at(definition, &output.module, output.index)
            && let Some(new) = production_identity(after)
            && new != *old
        {
            replaced
                .entry(*old)
                .or_insert_with(BTreeSet::new)
                .insert(new);
        }
    }
    replaced
}

/// Points every term of `definition` that was built with a replaced production at its
/// replacement (`replaced`, [`replaced_productions`]). A grammar edit changes which text parses
/// to which term and keeps the rules' terms: a rule's application of a replaced production is
/// an application of the same constructor (same label, sort and arguments), and its metadata
/// must name a production the mutant declares where the term is, or compilation finds no
/// production for it (a dangling production identity).
///
/// The retarget is per module, against the module's production catalog in the patched
/// definition: a term of module M naming a replaced identity is pointed at a replacement only
/// where M no longer sees the replaced identity (an equivalent copy of it in another module M
/// imports still names the same production) and sees exactly one of its replacements. Otherwise
/// the term is left as it is, and a term left naming a production M does not see is a dangling
/// application ([`Mutant::dangling_applications`]), which compilation refuses. Only sentences
/// that name a replaced identity are rewritten.
fn retarget_productions(
    definition: &mut Definition,
    replaced: &BTreeMap<ProductionIdentity, BTreeSet<ProductionIdentity>>,
) -> Result<(), PatchFailure> {
    if replaced.is_empty() {
        return Ok(());
    }
    let resolved = ResolvedDefinition::resolve(definition)
        .map_err(|error| ill_formed(format!("the patched definition does not resolve: {error}")))?;
    // Per module, the replacement each replaced identity its terms name is pointed at.
    let mut targets = BTreeMap::<String, BTreeMap<ProductionIdentity, ProductionIdentity>>::new();
    for (module_id, module) in resolved.modules() {
        let catalog = resolved.production_catalog(module_id);
        let seen = |identity: &ProductionIdentity| catalog.lookup(identity).is_some();
        let module_targets = replaced
            .iter()
            .filter(|(old, _)| !seen(old))
            .filter_map(|(old, news)| {
                let mut visible = news.iter().filter(|new| seen(new));
                match (visible.next(), visible.next()) {
                    (Some(new), None) => Some((*old, *new)),
                    _ => None,
                }
            })
            .collect::<BTreeMap<_, _>>();
        if !module_targets.is_empty() {
            targets.insert(module.name.clone(), module_targets);
        }
    }
    for module in &mut definition.modules {
        let Some(module_targets) = targets.get(&module.name) else {
            continue;
        };
        for sentence in &mut module.local_sentences {
            if !sentence
                .terms()
                .any(|(_, term)| names_any(term, module_targets))
            {
                continue;
            }
            for (_, term) in sentence_mut(sentence).terms_mut() {
                let taken = std::mem::replace(term, Term::Sequence(Vec::new()));
                *term = retarget_term(taken, module_targets);
            }
        }
    }
    Ok(())
}

/// Whether `term` or a subterm carries a production identity of `replaced` in its metadata.
fn names_any(term: &Term, replaced: &BTreeMap<ProductionIdentity, ProductionIdentity>) -> bool {
    if term
        .metadata()
        .and_then(|metadata| metadata.production)
        .is_some_and(|identity| replaced.contains_key(&identity))
    {
        return true;
    }
    match term.unannotated() {
        Term::Rewrite { left, right } => names_any(left, replaced) || names_any(right, replaced),
        Term::As { pattern, alias } => names_any(pattern, replaced) || names_any(alias, replaced),
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => items.iter().any(|item| names_any(item, replaced)),
        _ => false,
    }
}

/// Calls `found` with the label of each application in `term` whose production identity `seen`
/// does not hold (k-rust's dangling-identity check, `Mutant::dangling_applications`).
// Invariant: every recursive call consumes one child of the finite term tree.
fn unseen_applications(
    term: &Term,
    seen: &dyn Fn(&ProductionIdentity) -> bool,
    found: &mut dyn FnMut(&str),
) {
    if let (Some(metadata), Term::Apply { label, .. }) = (term.metadata(), term.unannotated())
        && let Some(identity) = metadata.production
        && !seen(&identity)
    {
        found(&label.name);
    }
    match term.unannotated() {
        Term::Rewrite { left, right } => {
            unseen_applications(left, seen, found);
            unseen_applications(right, seen, found);
        }
        Term::As { pattern, alias } => {
            unseen_applications(pattern, seen, found);
            unseen_applications(alias, seen, found);
        }
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => {
            for item in items {
                unseen_applications(item, seen, found);
            }
        }
        _ => {}
    }
}

// Invariant: every recursive call consumes one child of the finite term tree.
fn retarget_term(term: Term, replaced: &BTreeMap<ProductionIdentity, ProductionIdentity>) -> Term {
    let mut metadata = term.metadata().cloned().unwrap_or_default();
    if let Some(identity) = metadata.production
        && let Some(replacement) = replaced.get(&identity)
    {
        metadata.production = Some(*replacement);
    }
    let rebuilt = match term.into_unannotated().into_parts() {
        TermParts::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(retarget_term(*left, replaced)),
            right: Box::new(retarget_term(*right, replaced)),
        },
        TermParts::As { pattern, alias } => Term::As {
            pattern: Box::new(retarget_term(*pattern, replaced)),
            alias: Box::new(retarget_term(*alias, replaced)),
        },
        TermParts::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| retarget_term(item, replaced))
                .collect(),
        ),
        TermParts::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments
                .into_iter()
                .map(|argument| retarget_term(argument, replaced))
                .collect(),
        },
        leaf => Term::from(leaf),
    };
    rebuilt.with_metadata(metadata)
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
            editable(replacement)?;
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
            editable(sentence)?;
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

/// The typing diagnostics of the edited and inserted rules and claims (decision 4; findings
/// C-02, C-03; packet L2-2-fix-1): each is typed in compilation's view, one
/// `SentenceTyper::for_compilation` of the patched definition with `typing_in` its declaring
/// module, and any error is recorded, never a refusal. A mutant is valid when it compiles. k-rust
/// documents a typing error as an error compilation stops at, but the view refuses shapes
/// compilation accepts: `CellCompletion`, its stated exception, and a least upper bound a second
/// common supersort in the main module makes non-unique (`Sort`; review L2-2-review-1, probes
/// lubbase and lubmain). Before L2-2 every error of the declaring module's view refused the
/// patch, and at L2-2 a `Sort` or `SemanticCasts` error of compilation's view did.
///
/// The typing recurses once per level of the rule's terms, with no stack guard in k-rust (about
/// 2 KiB per level, 4 KiB through parametric productions; `stack::TYPING_STACK_PER_LEVEL`), so it
/// runs on a stack sized from the rule's deepest term (`stack`, re-pin L1-3-fix-2, L1-3-tail): on
/// the calling thread, it aborted the process near 230,000 levels on kink's
/// 256 MiB thread and near 1,500 on a worker's default stack (reviews L1-3-1 D1, L1-3-2 D1).
/// The typing a rule gets is therefore a function of the rule, not of the thread. A rule too
/// deep for the largest segment kink maps (over about a million levels), or one whose segment
/// the system refuses, is not typed, and the diagnostic says so; that refuses nothing, as no
/// typing error does, so [`PATCH_ADMISSION_VERSION`] is unchanged (before, such a rule aborted).
fn typing_diagnostics(
    definition: &Definition,
    resolved: &ResolvedDefinition,
    origins: &BTreeMap<SentenceRef, SentenceOrigin>,
    edits: &[Edit],
) -> Result<Vec<TypingDiagnostic>, PatchFailure> {
    let changed = edits
        .iter()
        .filter_map(|edit| match edit {
            Edit::ReplaceTerm { at, .. } => Some(&at.sentence),
            Edit::ReplaceSentence { at, .. } => Some(at),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let mut typing = None;
    let mut diagnostics = Vec::new();
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
        let typing: &CompilationTyping<'_> =
            typing.get_or_insert_with(|| CompilationTyping::new(resolved));
        let typed = with_stack(sentence_depth(sentence), TYPING_STACK_PER_LEVEL, || {
            typing.error(sentence, &at.module)
        });
        let message = match typed {
            Ok(None) => continue,
            Ok(Some(error)) => error.to_string(),
            Err(refusal) => format!("not typed: {refusal}"),
        };
        diagnostics.push(TypingDiagnostic {
            at: at.clone(),
            origin: origin.clone(),
            message,
        });
    }
    Ok(diagnostics)
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

/// The sentences an edit may replace or insert: rules, claims and contexts, and the sentences
/// that say which text parses to which term (productions, lexical, priority and associativity
/// declarations). A sort or sort-synonym declaration, a configuration and a bubble are refused.
fn editable(sentence: &Sentence) -> Result<(), PatchFailure> {
    match sentence {
        Sentence::Rule { .. }
        | Sentence::Claim { .. }
        | Sentence::Context { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::SyntaxAssociativity { .. } => Ok(()),
        _ => Err(ill_formed(
            "only rules, claims, contexts, productions and lexical, priority and associativity \
             declarations can be replaced or inserted",
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
