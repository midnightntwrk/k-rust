//! Generated grammar sets (PJ-34, U34h): a `[[mutation]]` with `grammar = "default"` names the
//! default grammar operator set (kink-patch `GrammarForm::DEFAULT`: widening and token-level
//! narrowing) instead of writing edits, and expands, once the specification is admitted, into one
//! mutation per generated grammar patch ([`expand`]).
//!
//! Each row is the patch kink-patch generates at one site (`generate_grammar`, admitted when its
//! mutant gives a program parser for the syntax module), resolved as a grammar mutation with that
//! patch ([`ResolvedMutation`], one `rules` entry of kind `grammar`), so `run`'s search judges it
//! as it judges a written grammar mutation (`crate::reparse`), and `check --mutations` shows it.
//! No text edit writes it: its `before` is the site sentence's text in its file's K view, and its
//! `after` describes what the patch writes there, the edited or inserted sentence rendered as K
//! ([`render`]; k-rust prints no production), so it is a description, not a declaration's text.
//!
//! The sites are the authored grammar sentences of the modules the syntax module imports
//! (transitively, every import, and itself): a program's text is parsed with the grammar the
//! syntax module sees, so a sentence outside them changes no case's parse, and its survivor would
//! be a target no case can meet. The expansion is a function of the admitted baseline, the
//! syntax module and the entry: forms in `GrammarForm::DEFAULT` order, sites in kink-patch's site
//! order, variants in kink-patch's order, the same rows with the same ids on every run.
//!
//! A row's id is `<set>/<form>/<module>/<site>/<variant>`, a function of the form and of the
//! site's own content, never of a sentence index:
//!
//! - site: a labelled production's label; a lexical declaration's `lexical-<Name>`; an unlabelled
//!   token production's `<Sort>-token-<the first 8 hex digits of the SHA-256 of its regex>`; two
//!   sites with one key in one module (two tokens of one sort with one regex) take `#2`, `#3` in
//!   module order;
//! - variant: `merge-alternative`'s target sort, `drop-anchor`'s `start` or `end`, else
//!   kink-patch's variant path joined by `.` (a terminal's item index, a regex node's preorder
//!   index and the choice made there), each a function of the site's own sentence.
//!
//! So an edit of the definition elsewhere (a rule, a production, a module, a sentence before the
//! site) keeps every row's id; an edit of the site itself may give its id to another mutant, whose
//! recorded killer the lock keeps only while it still kills. A row's outcome records are keyed by
//! its patch's mutation identity, as every mutation's are, and its lock row by its id.
//! [`GRAMMAR_SET_VERSION`] names the expansion: the forms, the site selection and the id scheme.
//!
//! A flow whose definition is KRS (`FlowManifest::definition`) gets no row: its front end judges
//! written production edits only, a generated row has no text edit for it to judge, and it would
//! run unjudged. The set is one refused row
//! (`grammar-set-not-judged`), as is a set one of whose ids another mutation has
//! (`grammar-set-id-collision`).

use crate::{
    manifest::FlowManifest,
    mutation::{
        EditedKind, EditedRule, GrammarSet, InvalidMutation, InvalidReason, Mutation, MutationList,
        ResolvedMutation, View, sentence_span,
    },
};
use k_rust::definition::{AttributeKey, ProductionItem, Sentence};
use kink_corpus::LoadedSource;
use kink_patch::{
    Baseline, CandidateDisposition, Edit, GrammarEffect, GrammarForm, GrammarSelector, Patch,
    SentenceRef, TermRef, generate_grammar, sha256,
};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

/// The expansion of a generated grammar set: the forms it takes (kink-patch
/// `GrammarForm::DEFAULT`), the sites it selects (the syntax module's import closure) and the
/// rows' id scheme (module documentation). It keys no record: a row's outcome records are keyed
/// by its patch's identity and its lock row by its id, so a change of the expansion changes which
/// rows exist.
pub const GRAMMAR_SET_VERSION: &str = "kink-flow/grammar-set/v1";

/// One row a set expands into: a mutation of the list as `run` and `check` read it.
#[derive(Clone, Debug)]
pub struct GeneratedRow {
    /// The row's mutation: its id, its note, no edit and no expectation.
    pub mutation: Mutation,
    /// Its resolution: the generated patch, or why the set gives no row ([`InvalidReason`]).
    pub resolution: Result<ResolvedMutation, InvalidMutation>,
    /// The row's `generated` member: `{set, grammar, version, form, effect, site, variant}` (the
    /// last four absent on a set's refused row).
    pub generated: Value,
}

/// What one set expands into.
#[derive(Clone, Debug)]
pub struct Expansion {
    /// The set's id.
    pub id: String,
    /// Its rows, in expansion order; one refused row with the set's id where it gives none.
    pub rows: Vec<GeneratedRow>,
    /// The set's entry in `check`'s `grammar_sets`: `{id, grammar, version, modules, forms:
    /// [{form, effect, rows, rejected: [{site, variant, reason}]}], refusal}`.
    pub summary: Value,
}

/// Every set of `list` expanded over the admitted `loaded` (module documentation), in list
/// order; empty for a list with no set.
#[must_use]
pub fn expand_all(
    manifest: &FlowManifest,
    loaded: &LoadedSource,
    list: &MutationList,
) -> Vec<Expansion> {
    let mut taken = list
        .mutations
        .iter()
        .map(|mutation| mutation.id.clone())
        .chain(list.grammar_sets.iter().map(|set| set.id.clone()))
        .collect::<BTreeSet<_>>();
    list.grammar_sets
        .iter()
        .map(|set| {
            let mut expansion = expand(manifest, loaded, set);
            // An id another mutation of the list has, or that another row of the set has
            // (none arise from distinct sites and variants).
            let mut own = BTreeSet::new();
            let collisions = expansion
                .rows
                .iter()
                .filter(|row| row.resolution.is_ok())
                .map(|row| row.mutation.id.clone())
                .filter(|id| taken.contains(id) || !own.insert(id.clone()))
                .collect::<Vec<_>>();
            if collisions.is_empty() {
                taken.extend(expansion.rows.iter().map(|row| row.mutation.id.clone()));
            } else {
                let refusal = InvalidMutation {
                    edit: None,
                    reason: InvalidReason::GrammarSetIdCollision,
                    detail: format!(
                        "the set's rows {collisions:?} have the id of another mutation of the list \
                         or of another row of the set"
                    ),
                };
                expansion.summary["refusal"] = refusal_value(&refusal);
                // The set gives no generated row, so its summary lists none.
                expansion.summary["forms"] = json!([]);
                expansion.rows = vec![refused_row(set, refusal)];
            }
            expansion
        })
        .collect()
}

/// The expansion of `set` over the admitted `loaded` (module documentation).
#[must_use]
pub fn expand(manifest: &FlowManifest, loaded: &LoadedSource, set: &GrammarSet) -> Expansion {
    let mut summary = json!({
        "id": set.id,
        "grammar": set.set.as_str(),
        "version": GRAMMAR_SET_VERSION,
        "modules": [],
        "forms": [],
        "refusal": null,
    });
    let refused = |mut summary: Value, refusal: InvalidMutation| {
        summary["refusal"] = refusal_value(&refusal);
        Expansion {
            id: set.id.clone(),
            rows: vec![refused_row(set, refusal)],
            summary,
        }
    };
    if let Some(definition) = &manifest.definition {
        let refusal = InvalidMutation {
            edit: None,
            reason: InvalidReason::GrammarSetNotJudged,
            detail: format!(
                "the flow's definition is {definition}, whose productions its front end emits \
                 from Rust items and judges by the text edits of a mutation: a generated grammar \
                 mutant of it has none, and would run unjudged"
            ),
        };
        return refused(summary, refusal);
    }
    let baseline = &loaded.baseline;
    let syntax_module = loaded.syntax_module();
    let modules = import_closure(baseline, syntax_module);
    summary["modules"] = json!(modules);
    let sites = site_keys(baseline);
    let mut views = BTreeMap::<String, Result<View, (InvalidReason, String)>>::new();
    let mut rows = Vec::new();
    let mut forms = Vec::new();
    for form in GrammarForm::DEFAULT {
        let (generated, rejected) =
            match form_candidates(baseline, form, &modules, syntax_module, &sites) {
                Ok(candidates) => candidates,
                Err(refusal) => return refused(summary, refusal),
            };
        let mut ids = Vec::new();
        for (at, patch) in generated {
            let row = generated_row(manifest, loaded, set, form, &sites, &mut views, &at, patch);
            ids.push(row.mutation.id.clone());
            rows.push(row);
        }
        forms.push(json!({
            "form": form.name(),
            "effect": effect_name(form.effect()),
            "rows": ids,
            "rejected": rejected,
        }));
    }
    summary["forms"] = json!(forms);
    Expansion {
        id: set.id.clone(),
        rows,
        summary,
    }
}

/// The candidates of `form` at the sites of `modules`, each module generated apart and merged
/// back into kink-patch's site order: each distinct admitted patch at its first origin, and each
/// origin kink-patch rejected (`{site, variant, reason}`), which is no mutant.
#[allow(clippy::type_complexity)]
fn form_candidates(
    baseline: &Baseline,
    form: GrammarForm,
    modules: &[String],
    syntax_module: &str,
    sites: &BTreeMap<SentenceRef, String>,
) -> Result<(Vec<(TermRef, Patch)>, Vec<Value>), InvalidMutation> {
    let mut generated = Vec::new();
    let mut rejected = Vec::new();
    for module in modules {
        let generation = generate_grammar(
            baseline,
            form,
            &[GrammarSelector::Module(module.clone())],
            syntax_module,
            usize::MAX,
        )
        .map_err(|failure| InvalidMutation {
            edit: None,
            reason: InvalidReason::PatchRejected,
            detail: format!("generating {} in {module}: {failure}", form.name()),
        })?;
        for (origin, disposition) in generation
            .selected_origins()
            .iter()
            .zip(generation.dispositions())
        {
            let at = &origin.site_tuple[0];
            match disposition {
                CandidateDisposition::Mutant(index) => {
                    let candidate = &generation.candidates()[*index];
                    // A patch several origins give is one row, at its first origin.
                    if candidate.origins[0] == *origin {
                        generated.push((at.clone(), candidate.patch.clone()));
                    }
                }
                CandidateDisposition::Rejected(failure) => rejected.push((
                    at.clone(),
                    json!({
                        "site": sites.get(&at.sentence),
                        "variant": path_text(at),
                        "reason": failure.to_string(),
                    }),
                )),
            }
        }
    }
    generated.sort_by(|left, right| left.0.cmp(&right.0));
    rejected.sort_by(|left, right| left.0.cmp(&right.0));
    Ok((
        generated,
        rejected.into_iter().map(|(_, value)| value).collect(),
    ))
}

/// The list `run` and `check` judge: `list`'s written mutations, then every row of `expansions`
/// in order, with no set left.
#[must_use]
pub fn expanded_list(list: &MutationList, expansions: &[Expansion]) -> MutationList {
    MutationList {
        mutations: list
            .mutations
            .iter()
            .cloned()
            .chain(
                expansions
                    .iter()
                    .flat_map(|expansion| expansion.rows.iter().map(|row| row.mutation.clone())),
            )
            .collect(),
        grammar_sets: Vec::new(),
    }
}

/// `only` with the ids of every row a named set expands into added after the set's id, so that
/// `--only SET` selects the set's rows and the lock compares them. The set's id is kept: a set
/// that expands into no row then still leaves `--only` naming something, so the run selects
/// nothing rather than every mutation.
#[must_use]
pub fn selected_ids(only: &[String], expansions: &[Expansion]) -> Vec<String> {
    let mut ids = Vec::new();
    for id in only {
        ids.push(id.clone());
        if let Some(expansion) = expansions.iter().find(|expansion| expansion.id == *id) {
            ids.extend(
                expansion
                    .rows
                    .iter()
                    .map(|row| row.mutation.id.clone())
                    .filter(|row| row != id),
            );
        }
    }
    ids
}

fn refusal_value(refusal: &InvalidMutation) -> Value {
    json!({
        "reason": refusal.reason.as_str(),
        "detail": refusal.detail,
        "next": refusal.reason.next_step(),
    })
}

fn refused_row(set: &GrammarSet, refusal: InvalidMutation) -> GeneratedRow {
    GeneratedRow {
        mutation: Mutation {
            id: set.id.clone(),
            misunderstanding: set.misunderstanding.clone().unwrap_or_default(),
            expect: None,
            edits: Vec::new(),
        },
        resolution: Err(refusal),
        generated: json!({
            "set": set.id,
            "grammar": set.set.as_str(),
            "version": GRAMMAR_SET_VERSION,
        }),
    }
}

#[allow(clippy::too_many_arguments)]
fn generated_row(
    manifest: &FlowManifest,
    loaded: &LoadedSource,
    set: &GrammarSet,
    form: GrammarForm,
    sites: &BTreeMap<SentenceRef, String>,
    views: &mut BTreeMap<String, Result<View, (InvalidReason, String)>>,
    at: &TermRef,
    patch: Patch,
) -> GeneratedRow {
    let site = sites
        .get(&at.sentence)
        .cloned()
        .unwrap_or_else(|| format!("sentence-{}", at.sentence.index));
    let variant = variant_text(form, at, &patch);
    let id = format!(
        "{}/{}/{}/{site}/{variant}",
        set.id,
        form.name(),
        at.sentence.module
    );
    let sentence = loaded
        .baseline
        .sentence(&at.sentence)
        .expect("a generated site is a sentence of the baseline");
    let description = describe(form, sentence, &at.path.0, &patch);
    let mutation = Mutation {
        id: id.clone(),
        misunderstanding: match &set.misunderstanding {
            Some(note) => format!("{note}: {description}"),
            None => description,
        },
        expect: None,
        edits: Vec::new(),
    };
    let generated = json!({
        "set": set.id,
        "grammar": set.set.as_str(),
        "version": GRAMMAR_SET_VERSION,
        "form": form.name(),
        "effect": effect_name(form.effect()),
        "site": site,
        "variant": variant,
    });
    let resolution =
        site_rule(manifest, loaded, views, &at.sentence, sentence, &patch).and_then(|rule| {
            let digest = patch.digest().map_err(|e| InvalidMutation {
                edit: None,
                reason: InvalidReason::PatchRejected,
                detail: format!("the generated patch does not encode: {e}"),
            })?;
            Ok(ResolvedMutation::generated(id, patch, digest, rule))
        });
    GeneratedRow {
        mutation,
        resolution,
        generated,
    }
}

/// The `rules` entry of a generated row: the site's address, file, lines and text, and a
/// description of what the patch writes there as its `after`.
fn site_rule(
    manifest: &FlowManifest,
    loaded: &LoadedSource,
    views: &mut BTreeMap<String, Result<View, (InvalidReason, String)>>,
    at: &SentenceRef,
    sentence: &Sentence,
    patch: &Patch,
) -> Result<EditedRule, InvalidMutation> {
    let refused = |reason, detail: String| InvalidMutation {
        edit: None,
        reason,
        detail,
    };
    let attributes = sentence.attributes();
    let (Some(file), Some(location)) = (
        attributes
            .source()
            .filter(|source| loaded.files.iter().any(|f| f.name == *source)),
        attributes.location(),
    ) else {
        return Err(refused(
            InvalidReason::NoUsableSpan,
            format!(
                "the generated site {}#{} has no source file or location",
                at.module, at.index
            ),
        ));
    };
    let view = views.entry(file.to_owned()).or_insert_with(|| {
        View::read(
            &manifest.directory,
            loaded,
            &manifest.spec.md_selector,
            file,
        )
    });
    let view = view
        .as_ref()
        .map_err(|(reason, detail)| refused(*reason, detail.clone()))?;
    let span = sentence_span(sentence, &view.text).ok_or_else(|| {
        refused(
            InvalidReason::NoUsableSpan,
            format!(
                "the generated site at {file}:{} has no span",
                location.start_line
            ),
        )
    })?;
    let before = view.text[span].to_owned();
    let after = patch
        .edits()
        .iter()
        .map(|edit| match edit {
            Edit::ReplaceSentence { replacement, .. } => render(replacement),
            Edit::InsertSentence { sentence, .. } => format!("{before}\n{}", render(sentence)),
            other => format!("{other:?}"),
        })
        .collect::<Vec<_>>()
        .join("\n");
    Ok(EditedRule {
        at: at.clone(),
        kind: EditedKind::Grammar,
        edits: Vec::new(),
        file: file.to_owned(),
        label: production_label(sentence).map(str::to_owned),
        start_line: location.start_line,
        end_line: location.end_line,
        before,
        after: Some(after),
    })
}

/// The modules whose grammar sentences the program parser of `syntax_module` reads: it and every
/// module it imports, transitively, publicly or not (an over-approximation), in the definition's
/// module order.
fn import_closure(baseline: &Baseline, syntax_module: &str) -> Vec<String> {
    let modules = &baseline.definition().modules;
    let mut closure = BTreeSet::from([syntax_module.to_owned()]);
    let mut pending = vec![syntax_module.to_owned()];
    while let Some(name) = pending.pop() {
        if let Some(module) = modules.iter().find(|module| module.name == name) {
            for import in &module.imports {
                if closure.insert(import.name.clone()) {
                    pending.push(import.name.clone());
                }
            }
        }
    }
    modules
        .iter()
        .filter(|module| closure.contains(&module.name))
        .map(|module| module.name.clone())
        .collect()
}

/// The site key of every authored sentence of `baseline` that has one (module documentation),
/// a repeated key in a module taking `#2`, `#3` in module order.
fn site_keys(baseline: &Baseline) -> BTreeMap<SentenceRef, String> {
    let mut keys = BTreeMap::new();
    let mut seen = BTreeMap::<(String, String), usize>::new();
    for (at, sentence) in baseline.authored_sentences() {
        let Some(key) = site_key(sentence) else {
            continue;
        };
        let count = seen.entry((at.module.clone(), key.clone())).or_default();
        *count += 1;
        let key = if *count == 1 {
            key
        } else {
            format!("{key}#{count}")
        };
        keys.insert(at, key);
    }
    keys
}

fn site_key(sentence: &Sentence) -> Option<String> {
    match sentence {
        Sentence::Production {
            label: Some(label), ..
        } => Some(label.name.clone()),
        Sentence::Production { sort, items, .. } => match items.as_slice() {
            [ProductionItem::RegexTerminal { regex }] => Some(format!(
                "{sort}-token-{}",
                &sha256(regex.as_bytes()).to_string()[..8]
            )),
            _ => None,
        },
        Sentence::SyntaxLexical { name, .. } => Some(format!("lexical-{name}")),
        _ => None,
    }
}

fn path_text(at: &TermRef) -> String {
    if at.path.0.is_empty() {
        "whole".to_owned()
    } else {
        at.path
            .0
            .iter()
            .map(u32::to_string)
            .collect::<Vec<_>>()
            .join(".")
    }
}

/// A row's variant (module documentation): what tells it apart from the other variants of its
/// form at its site, from the site's own content.
fn variant_text(form: GrammarForm, at: &TermRef, patch: &Patch) -> String {
    match form {
        GrammarForm::MergeAlternative => inserted(patch)
            .and_then(|sentence| match sentence {
                Sentence::Production { sort, .. } => Some(sort.to_string()),
                _ => None,
            })
            .unwrap_or_else(|| path_text(at)),
        GrammarForm::DropAnchor => match at.path.0.as_slice() {
            [0] => "start".to_owned(),
            [1] => "end".to_owned(),
            _ => path_text(at),
        },
        _ => path_text(at),
    }
}

fn inserted(patch: &Patch) -> Option<&Sentence> {
    patch.edits().iter().find_map(|edit| match edit {
        Edit::InsertSentence { sentence, .. } => Some(sentence),
        _ => None,
    })
}

fn replaced(patch: &Patch) -> Option<&Sentence> {
    patch.edits().iter().find_map(|edit| match edit {
        Edit::ReplaceSentence { replacement, .. } => Some(replacement),
        _ => None,
    })
}

const fn effect_name(effect: GrammarEffect) -> &'static str {
    match effect {
        GrammarEffect::Widening => "widening",
        GrammarEffect::TokenNarrowing => "token-narrowing",
        GrammarEffect::ProductionNarrowing => "production-narrowing",
        GrammarEffect::LiteralMove => "literal-move",
        GrammarEffect::Disambiguation => "disambiguation",
    }
}

fn production_label(sentence: &Sentence) -> Option<&str> {
    match sentence {
        Sentence::Production {
            label: Some(label), ..
        } => Some(label.name.as_str()),
        _ => None,
    }
}

/// The site's regex: a token production's or a lexical declaration's.
fn regex_of(sentence: &Sentence) -> Option<&str> {
    match sentence {
        Sentence::Production { items, .. } => match items.as_slice() {
            [ProductionItem::RegexTerminal { regex }] => Some(regex),
            _ => None,
        },
        Sentence::SyntaxLexical { regex, .. } => Some(regex),
        _ => None,
    }
}

/// The misunderstanding a row writes: what its form does at its site.
fn describe(form: GrammarForm, site: &Sentence, variant: &[u32], patch: &Patch) -> String {
    let name = production_label(site).map_or_else(
        || match site {
            Sentence::SyntaxLexical { name, .. } => format!("the lexical {name}"),
            Sentence::Production { sort, .. } => format!("the token of {sort}"),
            _ => "the declaration".to_owned(),
        },
        |label| format!("production `{label}`"),
    );
    let fresh = inserted(patch)
        .and_then(production_label)
        .unwrap_or("?")
        .to_owned();
    match form {
        GrammarForm::AlternativeWithoutTerminal => {
            // The variant's path is the dropped terminal's item index (kink-patch).
            let dropped = match (site, variant.first()) {
                (Sentence::Production { items, .. }, Some(&index)) => {
                    match usize::try_from(index)
                        .ok()
                        .and_then(|index| items.get(index))
                    {
                        Some(ProductionItem::Terminal(text)) => format!("{text:?}"),
                        _ => "a literal".to_owned(),
                    }
                }
                _ => "a literal".to_owned(),
            };
            format!(
                "the text of {name} without its literal {dropped} also parses, to a new \
                 constructor `{fresh}`"
            )
        }
        GrammarForm::MergeAlternative => {
            let sort = match inserted(patch) {
                Some(Sentence::Production { sort, .. }) => sort.to_string(),
                _ => "another sort".to_owned(),
            };
            format!(
                "the text of {name} also parses where {sort} is expected, to a new constructor \
                 `{fresh}`"
            )
        }
        GrammarForm::LoosenRegex | GrammarForm::NarrowRegex | GrammarForm::DropAnchor => {
            let how = match form {
                GrammarForm::LoosenRegex => "loosened at one node",
                GrammarForm::NarrowRegex => "narrowed at one node",
                _ => "stripped of a line anchor",
            };
            format!(
                "the regex of {name} is {how}: r\"{}\" becomes r\"{}\"",
                regex_of(site).unwrap_or_default(),
                replaced(patch).and_then(regex_of).unwrap_or_default()
            )
        }
        _ => format!("{} at {name}", form.name()),
    }
}

/// `sentence` rendered as K, to describe what a generated patch writes: a production's sort,
/// items and the attributes that tell it apart (`symbol`, `token`, `prefer`, `avoid`), a lexical
/// declaration's name and regex. It is a description: k-rust prints no production, and the text
/// is never read back.
#[must_use]
pub fn render(sentence: &Sentence) -> String {
    match sentence {
        Sentence::Production {
            label,
            sort,
            items,
            attributes,
            ..
        } => {
            let items = items
                .iter()
                .map(|item| match item {
                    ProductionItem::Terminal(text) => format!("{text:?}"),
                    ProductionItem::NonTerminal { sort, name: None } => sort.to_string(),
                    ProductionItem::NonTerminal {
                        sort,
                        name: Some(name),
                    } => format!("{name}: {sort}"),
                    ProductionItem::RegexTerminal { regex } => format!("r\"{regex}\""),
                })
                .collect::<Vec<_>>()
                .join(" ");
            let mut tags = Vec::new();
            if let Some(label) = label {
                tags.push(format!("symbol({})", label.name));
            }
            for (key, tag) in [
                (AttributeKey::Token, "token"),
                (AttributeKey::Prefer, "prefer"),
                (AttributeKey::Avoid, "avoid"),
            ] {
                if attributes.has(key) {
                    tags.push(tag.to_owned());
                }
            }
            if tags.is_empty() {
                format!("syntax {sort} ::= {items}")
            } else {
                format!("syntax {sort} ::= {items} [{}]", tags.join(", "))
            }
        }
        Sentence::SyntaxLexical { name, regex, .. } => {
            format!("syntax lexical {name} = r\"{regex}\"")
        }
        other => format!("{other:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expansion(id: &str, rows: &[&str]) -> Expansion {
        Expansion {
            id: id.to_owned(),
            rows: rows
                .iter()
                .map(|row| GeneratedRow {
                    mutation: Mutation {
                        id: (*row).to_owned(),
                        misunderstanding: String::new(),
                        expect: None,
                        edits: Vec::new(),
                    },
                    resolution: Err(InvalidMutation {
                        edit: None,
                        reason: InvalidReason::PatchRejected,
                        detail: String::new(),
                    }),
                    generated: Value::Null,
                })
                .collect(),
            summary: Value::Null,
        }
    }

    /// `--only SET` names the set's rows, and a set that expands into none still names
    /// something, so the run selects nothing rather than every mutation.
    #[test]
    fn only_a_set_selects_its_rows_and_an_empty_set_selects_nothing() {
        let sets = [expansion("g", &["g/a", "g/b"]), expansion("empty", &[])];
        let only = |ids: &[&str]| {
            selected_ids(
                &ids.iter().map(|id| (*id).to_owned()).collect::<Vec<_>>(),
                &sets,
            )
        };
        assert_eq!(only(&["g"]), ["g", "g/a", "g/b"]);
        assert_eq!(only(&["empty"]), ["empty"]);
        assert_eq!(only(&["x", "g/a"]), ["x", "g/a"]);
        assert_eq!(only(&[]), Vec::<String>::new());
    }
}
