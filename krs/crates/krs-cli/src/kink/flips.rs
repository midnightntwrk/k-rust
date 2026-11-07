//! Condition flips: the mutations derived from the definition, one per minimal closed set of
//! sentences in which negating one condition atom (or toggling one bit of a `k::bits!` encoding)
//! keeps the sentences apart ([`krs_compiler::guard_families`]).
//!
//! A flip asks whether the corpus notices that a condition's two outcomes are swapped where the
//! definition tests it. Every flip is computed from the definition on every command, so it has
//! no list file and no misunderstanding: the rule that generates it is its justification.
//!
//! Each flip is spelled as a K patch of `definition.k` in the mutation format a list uses, one
//! `rule = <label>` edit per flipped sentence, and judged by the front end's checks
//! ([`super::checks`]) through the judge cache shared with `check` and `run`, as an authored
//! mutation is: KRS's admission, not the generator's propositional argument, decides whether a
//! flipped definition is one a Rust source writes.
//!
//! The spelling edits the nodes that render each occurrence of the atom:
//!
//! - a Boolean atom `T` becomes `notBool (T)`, except where the occurrence is the operand of a
//!   rendered negation, which then becomes the operand itself (Rust's `!c` becomes `c`); each is
//!   a Rust spelling of the negated condition;
//! - a bit `k` of an encoding toggles the constant of every node that fixes it: a template's
//!   fixed run `bitRangeInt(x, i, n) ==Int c` becomes `c ⊕ 2^(k−i)`, and a literal pattern or a
//!   hole `x =/=Int v` becomes `v ⊕ 2^k`, so that the encodings of the flipped arms are permuted
//!   by `x ↦ x ⊕ 2^k`.
//!
//! An edit's `find` is the smallest emitted node that holds every edited occurrence of its
//! sentence and occurs once in the sentence's text, so that it addresses one place; the whole
//! sentence is the last resort. A flip the spelling cannot write (an occurrence the emission does
//! not render, a constant that is not one) is refused with the reason `not-judged`, as a judge's
//! refusal is: either is a disagreement between the generator and KRS's admission, which a
//! definition's tests pin to zero.

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use kink_corpus::LoadedSource;
use kink_flow::{EditAction, EditSpec, FlowManifest, InvalidMutation, Mutation};
use krs_compiler::{
    AtomKind, FamilySentence, FlipOperator, GuardAtom, GuardFamily, guard_families,
};
use krs_ir::SourceMapKey;
use krs_ir_levels::{SemanticModule, SemanticRule, SemanticTerm, SemanticTermKind};
use serde_json::{Value, json};

use super::checks::{Baseline, KrsChecks, NOT_JUDGED};
use crate::EmittedRule;

/// The condition flips of a definition: every flip obligation of its guard families, each
/// spelled as a K patch and judged, and the flips the families do not generate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DerivedFlips {
    /// The number of guard families: the families of sentences with a guard or a `k::bits!`
    /// argument.
    pub families: usize,
    /// Every flip obligation, in generation order (family, then atom, then component).
    pub flips: Vec<DerivedFlip>,
    /// The flips not generated, with their reasons, in family order.
    pub not_generated: Vec<FlipNotGenerated>,
}

/// One flip obligation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DerivedFlip {
    /// The flip's presentation identity (`flip--boundary_halted+boundary_wake--Requested`),
    /// unique in the definition and stable while the definition's families are.
    pub id: String,
    /// `flip` (a Boolean atom negated) or `bitflip` (a bit of an encoding toggled).
    pub operator: &'static str,
    /// The flipped atom.
    pub atom: FlipAtom,
    /// Whether the flip edits every sentence that mentions the atom.
    pub whole: bool,
    /// The flipped sentences, in family order.
    pub sentences: Vec<FlipSentence>,
    /// The edits of `definition.k`, one per flipped sentence: the K patch.
    pub edits: Vec<EditSpec>,
    /// Whether the front end admits the flipped definition.
    pub status: FlipStatus,
}

/// The atom a flip changes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FlipAtom {
    /// A Boolean atom of the guards, by the head of its first occurrence.
    Boolean {
        /// The first declared production the atom applies, else its builtin operation.
        head: String,
    },
    /// Bit `bit` of argument `column` (zero-based) of the family's function.
    Bit {
        /// The argument.
        column: usize,
        /// The bit, the least significant being 0.
        bit: u32,
    },
}

/// A flipped sentence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FlipSentence {
    /// The emitted label.
    pub label: String,
    /// The emitted K module that holds the sentence.
    pub module: String,
    /// The KRS item that wrote the sentence, as a stop names it.
    pub item: Option<String>,
    /// The authored file, package-relative.
    pub file: Option<String>,
    /// The line of the sentence's first authored range.
    pub line: Option<u32>,
    /// The bytes of `definition.k` that render each occurrence of the atom in the sentence.
    pub occurrences: Vec<Range<usize>>,
}

/// Whether the front end admits a flipped definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FlipStatus {
    /// Admitted: the K patch resolves to this patch digest and KRS admits the Rust source it
    /// stands for.
    Admitted {
        /// The patch digest (kink-flow's mutation identity).
        digest: String,
    },
    /// Refused, with the first refusal: kink-flow's resolution or the front end's checks.
    Refused {
        /// The refusal's reason.
        reason: String,
        /// What the refusal says to do next.
        next: Option<String>,
        /// What the refusal is about.
        detail: String,
    },
}

/// A flip, or a family's flips, the families do not generate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FlipNotGenerated {
    /// Why ([`krs_compiler::NotGeneratedReason::as_str`]).
    pub reason: &'static str,
    /// The atom concerned, when there is one.
    pub atom: Option<FlipAtom>,
    /// The labels of the sentences concerned.
    pub sentences: Vec<String>,
    /// The labels of the pair the reason names, when there is one.
    pub pair: Option<[String; 2]>,
    /// What the reason is about.
    pub detail: String,
}

impl DerivedFlips {
    /// Why the definition has no flip, or `None` when it has one.
    #[must_use]
    pub fn none_reason(&self) -> Option<String> {
        if !self.flips.is_empty() {
            return None;
        }
        Some(if self.families == 0 {
            "no sentence of the definition has a guard or a k::bits! argument, so no sentences \
             are kept apart by a condition a flip could negate"
                .to_owned()
        } else {
            format!(
                "the definition's {} guard famil{} generate no flip ({} not generated)",
                self.families,
                if self.families == 1 { "y" } else { "ies" },
                self.not_generated.len()
            )
        })
    }

    /// The flips as one JSON value, a function of the definition and the build alone.
    #[must_use]
    pub fn value(&self) -> Value {
        json!({
            "families": self.families,
            "flips": self.flips.iter().map(DerivedFlip::value).collect::<Vec<_>>(),
            "not_generated": self.not_generated.iter().map(FlipNotGenerated::value).collect::<Vec<_>>(),
            "none": self.none_reason(),
        })
    }
}

impl DerivedFlip {
    /// The flip as a list's mutation, with no misunderstanding: the generator's rule is its
    /// justification.
    #[must_use]
    pub fn mutation(&self) -> Mutation {
        Mutation {
            id: self.id.clone(),
            misunderstanding: String::new(),
            edits: self.edits.clone(),
        }
    }

    fn value(&self) -> Value {
        let status = match &self.status {
            FlipStatus::Admitted { digest } => json!({"status": "admitted", "digest": digest}),
            FlipStatus::Refused {
                reason,
                next,
                detail,
            } => json!({"status": "refused", "reason": reason, "next": next, "detail": detail}),
        };
        json!({
            "id": self.id,
            "operator": self.operator,
            "atom": self.atom.value(),
            "whole": self.whole,
            "sentences": self.sentences.iter().map(|sentence| json!({
                "label": sentence.label,
                "module": sentence.module,
                "item": sentence.item,
                "file": sentence.file,
                "line": sentence.line,
                "occurrences": sentence.occurrences.iter().map(|range| [range.start, range.end]).collect::<Vec<_>>(),
            })).collect::<Vec<_>>(),
            "edits": self.edits.iter().map(edit_value).collect::<Vec<_>>(),
            "judged": status,
        })
    }
}

impl FlipAtom {
    fn of(kind: &AtomKind) -> Self {
        match kind {
            AtomKind::Boolean { head } => Self::Boolean { head: head.clone() },
            AtomKind::Bit { column, bit } => Self::Bit {
                column: *column,
                bit: *bit,
            },
        }
    }

    fn value(&self) -> Value {
        match self {
            Self::Boolean { head } => json!({"kind": "boolean", "head": head}),
            Self::Bit { column, bit } => json!({"kind": "bit", "column": column, "bit": bit}),
        }
    }
}

impl FlipNotGenerated {
    fn value(&self) -> Value {
        json!({
            "reason": self.reason,
            "atom": self.atom.as_ref().map(FlipAtom::value),
            "sentences": self.sentences,
            "pair": self.pair,
            "detail": self.detail,
        })
    }
}

fn edit_value(edit: &EditSpec) -> Value {
    match &edit.action {
        EditAction::Replace { find, replace } => {
            json!({"rule": edit.rule, "find": find, "replace": replace})
        }
        EditAction::Delete => json!({"rule": edit.rule, "delete": true}),
    }
}

/// The flips of `baseline`'s definition, each judged by `checks` after kink-flow resolves its
/// patch against the corpus `manifest` bound to `definition.k`, whose specification is `loaded`.
pub(crate) fn derive(
    baseline: &Baseline<'_>,
    checks: &KrsChecks<'_>,
    manifest: &FlowManifest,
    loaded: &LoadedSource,
) -> DerivedFlips {
    let modules = baseline.retained.pre_derivation();
    let families = guard_families(modules);
    let speller = Speller::new(baseline, checks, manifest, loaded);
    let mut derived = DerivedFlips {
        families: families.len(),
        flips: Vec::new(),
        not_generated: Vec::new(),
    };
    for family in &families {
        let labels = family
            .sentences
            .iter()
            .map(|sentence| speller.label(sentence))
            .collect::<Vec<_>>();
        for flip in &family.obligations {
            let atom = &family.atoms[flip.atom];
            let mut flipped = DerivedFlip {
                id: flip.id.clone(),
                operator: flip.operator.as_str(),
                atom: FlipAtom::of(&atom.kind),
                whole: flip.whole,
                sentences: Vec::new(),
                edits: Vec::new(),
                status: FlipStatus::Admitted {
                    digest: String::new(),
                },
            };
            let outcome = flip.sentences.iter().try_for_each(|sentence| {
                let (sentence, edit) =
                    speller.sentence(modules, family, atom, *sentence, flip.operator)?;
                flipped.sentences.push(sentence);
                flipped.edits.push(edit);
                Ok::<_, String>(())
            });
            flipped.status = match outcome {
                Err(detail) => FlipStatus::Refused {
                    reason: NOT_JUDGED.to_owned(),
                    next: None,
                    detail,
                },
                Ok(()) => judge(&flipped.mutation(), checks, manifest, loaded),
            };
            derived.flips.push(flipped);
        }
        for not in &family.not_generated {
            derived.not_generated.push(FlipNotGenerated {
                reason: not.reason.as_str(),
                atom: not.atom.map(|atom| FlipAtom::of(&family.atoms[atom].kind)),
                sentences: not
                    .sentences
                    .iter()
                    .map(|sentence| labels[*sentence].clone())
                    .collect(),
                pair: not
                    .pair
                    .map(|[left, right]| [labels[left].clone(), labels[right].clone()]),
                detail: not.detail.clone(),
            });
        }
    }
    derived
}

/// Resolve `mutation` and judge it as `run` judges a list's mutation.
fn judge(
    mutation: &Mutation,
    checks: &KrsChecks<'_>,
    manifest: &FlowManifest,
    loaded: &LoadedSource,
) -> FlipStatus {
    let refused = |refusal: InvalidMutation| FlipStatus::Refused {
        reason: refusal.reason.as_str().to_owned(),
        next: Some(refusal.reason.next_step().to_owned()),
        detail: refusal.detail,
    };
    match kink_flow::resolve(manifest, loaded, mutation) {
        Err(refusal) => refused(refusal),
        Ok(resolved) => match checks.refusal(&resolved) {
            Some(refusal) => refused(refusal),
            None => FlipStatus::Admitted {
                digest: resolved.digest.to_string(),
            },
        },
    }
}

/// What spelling a flip reads: the emitted sentences and nodes, and each Definition IR node of a
/// semantic node.
struct Speller<'a> {
    checks: &'a KrsChecks<'a>,
    definition: &'a str,
    /// The Definition IR nodes of each semantic node.
    definition_keys: BTreeMap<&'a SourceMapKey, Vec<&'a SourceMapKey>>,
    /// The K text of each rule of the specification kink-flow loaded, by its stored label: the
    /// text in which an edit's `find` must occur once.
    texts: Vec<(String, String)>,
}

impl<'a> Speller<'a> {
    fn new(
        baseline: &Baseline<'a>,
        checks: &'a KrsChecks<'a>,
        manifest: &FlowManifest,
        loaded: &LoadedSource,
    ) -> Self {
        let mut definition_keys = BTreeMap::<_, Vec<_>>::new();
        for (definition, semantic) in baseline.lowered.semantic_keys() {
            definition_keys
                .entry(semantic)
                .or_default()
                .push(definition);
        }
        let texts = kink_flow::mutation::rule_texts(manifest, loaded)
            .into_iter()
            .filter_map(|rule| Some((rule.label?, rule.text?)))
            .collect();
        Self {
            checks,
            definition: &baseline.emitted.definition,
            definition_keys,
            texts,
        }
    }

    /// The emitted sentence of the family sentence `sentence`: its bytes and its rule.
    fn emitted(&self, sentence: &FamilySentence) -> Option<(Range<usize>, &'a EmittedRule)> {
        self.definition_keys
            .get(&sentence.key)?
            .iter()
            .find_map(|key| self.checks.sentence(key))
    }

    fn label(&self, sentence: &FamilySentence) -> String {
        self.emitted(sentence).map_or_else(
            || sentence.rule.item_name().to_owned(),
            |(_, rule)| rule.label.clone(),
        )
    }

    /// The flipped sentence `index` of `family` and its edit, or why the flip cannot be spelled.
    fn sentence(
        &self,
        modules: &[SemanticModule],
        family: &GuardFamily,
        atom: &GuardAtom,
        index: usize,
        operator: FlipOperator,
    ) -> Result<(FlipSentence, EditSpec), String> {
        let sentence = &family.sentences[index];
        let (range, rule) = self.emitted(sentence).ok_or_else(|| {
            format!(
                "the sentence `{}` is not rendered in definition.k",
                sentence.rule.item_name()
            )
        })?;
        let rendered = |key: &SourceMapKey| -> Vec<Range<usize>> {
            let mut ranges = self
                .definition_keys
                .get(key)
                .into_iter()
                .flatten()
                .filter_map(|key| self.checks.node(key))
                .map(|(node, _)| node)
                .filter(|node| range.start <= node.start && node.end <= range.end)
                .collect::<Vec<_>>();
            ranges.sort_by_key(|node| (node.start, node.end));
            ranges.dedup();
            ranges
        };
        let mut edits = Vec::new();
        let mut occurrences = Vec::new();
        for occurrence in atom
            .occurrences
            .iter()
            .filter(|occurrence| occurrence.sentence == index)
        {
            let nodes = rendered(&occurrence.key);
            if nodes.is_empty() {
                return Err(format!(
                    "an occurrence of the atom in `{}` is not rendered in definition.k",
                    rule.label
                ));
            }
            match (operator, &atom.kind) {
                (FlipOperator::Flip, _) => {
                    for node in nodes {
                        edits.push(self.negation(&range, &node));
                        occurrences.push(node);
                    }
                }
                (FlipOperator::BitFlip, AtomKind::Bit { bit, .. }) => {
                    let term = semantic_rule(modules, sentence)
                        .and_then(|rule| find_term(rule, &occurrence.key))
                        .ok_or_else(|| {
                            format!("an occurrence of the bit in `{}` is not found", rule.label)
                        })?;
                    let (token, value) = toggled(term, *bit).ok_or_else(|| {
                        format!(
                            "`{}` in `{}` holds no constant a bit flip can toggle",
                            self.text(&nodes[0]),
                            rule.label
                        )
                    })?;
                    let token_nodes = rendered(token.origin().key());
                    let [token_node] = token_nodes.as_slice() else {
                        return Err(format!(
                            "the constant `{}` in `{}` is not rendered once in definition.k",
                            self.text(&nodes[0]),
                            rule.label
                        ));
                    };
                    edits.push((token_node.clone(), value.to_string()));
                    occurrences.extend(nodes);
                }
                (FlipOperator::BitFlip, AtomKind::Boolean { .. }) => {
                    return Err("a bit flip of a Boolean atom".to_owned());
                }
            }
        }
        edits.sort_by_key(|(edited, _)| (edited.start, edited.end));
        edits.dedup();
        occurrences.sort_by_key(|node| (node.start, node.end));
        occurrences.dedup();
        let edit = self.edit(&range, rule, &edits)?;
        Ok((
            FlipSentence {
                label: rule.label.clone(),
                module: rule.module.clone(),
                item: rule.item.clone(),
                file: rule.file.clone(),
                line: rule.line,
                occurrences,
            },
            edit,
        ))
    }

    fn text(&self, range: &Range<usize>) -> &'a str {
        self.definition.get(range.clone()).unwrap_or_default()
    }

    /// The edit that negates the occurrence `node` of the sentence `sentence`: the operand of a
    /// rendered negation in place of the negation, else `notBool (T)` in place of `T`.
    fn negation(&self, sentence: &Range<usize>, node: &Range<usize>) -> (Range<usize>, String) {
        let operand = self.text(node);
        if let Some(parent) = self.checks.parent(sentence, node) {
            let text = self.text(&parent);
            let before = &text[..node.start - parent.start];
            let after = &text[node.end - parent.start..];
            let bare = |text: &str| {
                text.chars()
                    .all(|c| c.is_whitespace() || c == '(' || c == ')')
            };
            if before
                .trim()
                .trim_start_matches('(')
                .trim()
                .strip_prefix("notBool")
                .is_some_and(bare)
                && bare(after)
            {
                return (parent, operand.to_owned());
            }
        }
        (node.clone(), format!("(notBool ({operand}))"))
    }

    /// The edit of the sentence `sentence` (`rule`) that makes `edits`: `find` the smallest
    /// emitted node holding every edited range that occurs once in the sentence's text.
    fn edit(
        &self,
        sentence: &Range<usize>,
        rule: &EmittedRule,
        edits: &[(Range<usize>, String)],
    ) -> Result<EditSpec, String> {
        let (Some(start), Some(end)) = (
            edits.iter().map(|(range, _)| range.start).min(),
            edits.iter().map(|(range, _)| range.end).max(),
        ) else {
            return Err(format!("no occurrence of the atom in `{}`", rule.label));
        };
        if edits.windows(2).any(|pair| pair[0].0.end > pair[1].0.start) {
            return Err(format!("two edited nodes of `{}` overlap", rule.label));
        }
        let text = self
            .texts
            .iter()
            .find(|(label, _)| {
                kink_flow::label_match(label, &rule.module, &rule.label)
                    == Some(kink_flow::mutation::LabelMatch::Exact)
            })
            .map(|(_, text)| text.as_str())
            .ok_or_else(|| format!("kink-flow reads no rule labelled `{}`", rule.label))?;
        let unique = |range: &Range<usize>| text.matches(self.text(range)).count() == 1;
        let find = self
            .checks
            .enclosing(sentence, &(start..end))
            .into_iter()
            .chain([sentence.clone()])
            .find(unique)
            .ok_or_else(|| {
                format!(
                    "no node of `{}` holding the edited occurrences occurs once in its text",
                    rule.label
                )
            })?;
        let mut replace = String::new();
        let mut at = find.start;
        for (range, replacement) in edits {
            replace.push_str(self.text(&(at..range.start)));
            replace.push_str(replacement);
            at = range.end;
        }
        replace.push_str(self.text(&(at..find.end)));
        Ok(EditSpec {
            file: None,
            rule: Some(rule.label.clone()),
            line: None,
            action: EditAction::Replace {
                find: self.text(&find).to_owned(),
                replace,
            },
        })
    }
}

/// The pre-derivation rule of the family sentence `sentence`.
fn semantic_rule<'m>(
    modules: &'m [SemanticModule],
    sentence: &FamilySentence,
) -> Option<&'m SemanticRule> {
    modules
        .iter()
        .flat_map(SemanticModule::rules)
        .find(|rule| *rule.id() == sentence.rule)
}

/// The term of `rule` whose source-map key is `key`.
fn find_term<'m>(rule: &'m SemanticRule, key: &SourceMapKey) -> Option<&'m SemanticTerm> {
    let mut stack = rule
        .requires()
        .map(|condition| condition.terms())
        .unwrap_or_default();
    if let Some(body) = rule.body() {
        stack.extend([body.from(), body.to()]);
    }
    let mut seen = BTreeSet::new();
    while let Some(term) = stack.pop() {
        if term.origin().key() == key {
            return Some(term);
        }
        if seen.insert(std::ptr::from_ref(term)) {
            stack.extend(term.children());
        }
    }
    None
}

/// The integer value of a token.
fn int_value(term: &SemanticTerm) -> Option<i128> {
    match term.kind() {
        SemanticTermKind::Token { value } => value.parse().ok(),
        _ => None,
    }
}

/// The token of the constant a bit flip of `bit` toggles in `term`, and its toggled value: the
/// literal itself; the `c` of a fixed run `bitRange(x, i, n) == c`, toggled at `bit − i`; the
/// literal of a hole `x =/= v`.
fn toggled(term: &SemanticTerm, bit: u32) -> Option<(&SemanticTerm, i128)> {
    let flip = |value: i128, at: u32| Some(value ^ 1_i128.checked_shl(at)?);
    if let Some(value) = int_value(term) {
        return Some((term, flip(value, bit)?));
    }
    let SemanticTermKind::Application { arguments, .. } = term.kind() else {
        return None;
    };
    let tokens = arguments
        .iter()
        .filter(|argument| int_value(argument).is_some())
        .collect::<Vec<_>>();
    let [token] = tokens.as_slice() else {
        return None;
    };
    let value = int_value(token)?;
    let run = arguments.iter().find_map(|argument| match argument.kind() {
        SemanticTermKind::Application { arguments, .. } => match arguments.as_slice() {
            [_, offset, length] => Some((int_value(offset)?, int_value(length)?)),
            _ => None,
        },
        _ => None,
    });
    match run {
        Some((offset, length)) => {
            let at = i128::from(bit).checked_sub(offset)?;
            if at < 0 || at >= length {
                return None;
            }
            Some((token, flip(value, u32::try_from(at).ok()?)?))
        }
        None => Some((token, flip(value, bit)?)),
    }
}
