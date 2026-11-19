//! Grammar mutation sites and forms (PJ-34): the sentences that say which text parses to which
//! term, as mutation sites, and the edits generated at them.
//!
//! A grammar is what a K definition's syntax sentences say about text: its productions (a token
//! definition among them, a production with `token` whose one item is a regex terminal), its
//! lexical declarations (`syntax lexical Name = r"..."`, the named regex fragments a token regex
//! refers to as `{Name}`), and its priority and associativity declarations (`>` between the
//! groups of a `syntax` block, `syntax priority`, `[left]`, `syntax left`), which the parser reads
//! as separate sentences (k-rust `compute_priorities`, `compute_associativities`), never from a
//! production's attributes. A follow restriction (a token that a given text may not follow or
//! precede) has no place in k-rust's definitions (`docs/compatibility.md`, "Token precede and
//! follow restrictions"; `ProductionItem::RegexTerminal` holds only its regex), so no form edits
//! one; `tests/grammar.rs` pins that passage, and fails when k-rust gains one.
//!
//! Every form is an ordinary [`Edit`] of one authored grammar sentence, the site, so a grammar
//! mutant is applied, pinned, encoded and has its claims withdrawn as any mutant is. A site's
//! [`TermRef`] names the sentence and a path that is not a term path: it names the variant of the
//! form at that sentence (the item a terminal form edits, the regex node and the choice a regex
//! form makes, the group boundary a priority form moves, the associativity a form sets). It
//! identifies the origin within one baseline and form; [`crate::Baseline::term`] does not
//! resolve it.
//!
//! [`generate_grammar`] enumerates every variant of a form at every authored grammar sentence its
//! selector admits, so a generation it gives within its cap is complete. Each candidate is
//! admitted by [`crate::Mutant::program_parser`]: a generated grammar mutant gives a program parser
//! for the syntax module, or its origin is rejected with k-rust's reason
//! ([`crate::PatchFailureKind::NoProgramParser`]). Whether a mutant accepts more programs or fewer
//! is a fact of each program that tells it apart, never of the form: a form's name says how it
//! edits, not what it does to the language.

use crate::{
    Baseline, CandidateFailure, CandidateGeneration, Edit, InsertPosition, Patch, PatchOrigin,
    Selection, SentenceRef, TermRef,
};
use k_rust::definition::{
    Associativity, AttributeKey, Attributes, ProductionItem, Regex, RegexBody, Sentence,
    parse_regex,
};
use k_rust::kast::{Label, Sort};
use std::collections::{BTreeMap, BTreeSet};

/// How a grammar form edits its site.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum GrammarForm {
    /// A production's terminal (a literal) is removed: the symbol keeps its label, sort,
    /// nonterminals and attributes, and its text loses that literal. Not generated where the
    /// production has a `format`, which names items by position, or where the production would
    /// be left with no item or with one nonterminal alone.
    DropTerminal,
    /// A production's terminal is replaced by another literal: each terminal text of another
    /// authored grammar production of the same sort, in text order.
    ChangeTerminal,
    /// An alternative is added: a copy of the production with one terminal removed, inserted
    /// after it under a fresh label, so that the text without that literal also parses (to a
    /// new constructor).
    AlternativeWithoutTerminal,
    /// Alternatives are merged: a copy of the production is inserted at another sort that an
    /// authored grammar production of its module has, under a fresh label, so that the
    /// production's text also parses where that sort is expected.
    MergeAlternative,
    /// The production is deleted.
    DeleteProduction,
    /// A token or lexical regex is loosened at one node: a node made optional, `R+` to `R*`,
    /// a lower bound to 0, an upper bound dropped, a character or class to any character. No
    /// variant makes a regex that did not match the empty text match it.
    LoosenRegex,
    /// A token or lexical regex is narrowed at one node: `R*` to `R+`, `R?` to `R`, a union to
    /// one side, an unbounded repeat to its lower bound, a class member dropped.
    NarrowRegex,
    /// A token regex's line anchor (`^` or `$`) is dropped: the token no longer has to start or
    /// end a line.
    DropAnchor,
    /// Two adjacent groups of a priority declaration become one (one `>` is dropped).
    MergePriorityGroups,
    /// Two adjacent groups of a priority declaration are swapped.
    SwapPriorityGroups,
    /// An associativity declaration declares each other associativity (`left`, `right`,
    /// `non-assoc`).
    ChangeAssociativity,
    /// A priority or associativity declaration is deleted.
    DeleteRelation,
}

impl GrammarForm {
    /// Every form, in declaration order.
    pub const ALL: [Self; 12] = [
        Self::DropTerminal,
        Self::ChangeTerminal,
        Self::AlternativeWithoutTerminal,
        Self::MergeAlternative,
        Self::DeleteProduction,
        Self::LoosenRegex,
        Self::NarrowRegex,
        Self::DropAnchor,
        Self::MergePriorityGroups,
        Self::SwapPriorityGroups,
        Self::ChangeAssociativity,
        Self::DeleteRelation,
    ];

    /// The form's name, the operator name of its candidates.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::DropTerminal => "drop-terminal",
            Self::ChangeTerminal => "change-terminal",
            Self::AlternativeWithoutTerminal => "alternative-without-terminal",
            Self::MergeAlternative => "merge-alternative",
            Self::DeleteProduction => "delete-production",
            Self::LoosenRegex => "loosen-regex",
            Self::NarrowRegex => "narrow-regex",
            Self::DropAnchor => "drop-anchor",
            Self::MergePriorityGroups => "merge-priority-groups",
            Self::SwapPriorityGroups => "swap-priority-groups",
            Self::ChangeAssociativity => "change-associativity",
            Self::DeleteRelation => "delete-relation",
        }
    }
}

/// One conjunctive clause restricting the grammar sentences a form is generated at. A clause
/// that does not apply to a sentence's kind excludes it (a `Sort` clause excludes every
/// priority, associativity and lexical declaration).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GrammarSelector {
    /// The sentence is declared in this module.
    Module(String),
    /// The production's result sort is this sort.
    Sort(Sort),
    /// The production has this label, or the priority or associativity declaration names it.
    Label(String),
}

/// Every variant of `form` at every authored grammar sentence `selector` admits, as
/// (origin site, patch) pairs in site order.
///
/// # Panics
///
/// Never: every form builds at least one edit per variant.
#[must_use]
pub fn grammar_variants(
    baseline: &Baseline,
    form: GrammarForm,
    selector: &[GrammarSelector],
) -> Vec<(TermRef, Patch)> {
    let labels = production_labels(baseline);
    let mut variants = Vec::new();
    for (at, sentence) in baseline.authored_sentences() {
        if !selector.iter().all(|clause| admits(clause, &at, sentence)) {
            continue;
        }
        for (path, edits) in edits_at(baseline, &labels, form, &at, sentence) {
            let patch = Patch::new(edits).expect("a form builds at least one edit");
            variants.push((TermRef::new(at.clone(), path), patch));
        }
    }
    variants.sort_by(|left, right| left.0.cmp(&right.0));
    variants
}

/// Generates `form` over `baseline` (see the module documentation): at most `cap` origins, in
/// site order, each folded and applied, and admitted only when its mutant gives a program parser
/// for `syntax_module`. The generation is complete when no origin was cut by the cap.
///
/// # Errors
///
/// Those of [`Selection::fold_admitting`]: every edit targets its origin's sentence, so none.
///
/// # Panics
///
/// Never: each origin's patch is the one enumerated for it.
pub fn generate_grammar<'b>(
    baseline: &'b Baseline,
    form: GrammarForm,
    selector: &[GrammarSelector],
    syntax_module: &str,
    cap: usize,
) -> Result<CandidateGeneration<'b>, CandidateFailure> {
    let mut variants = grammar_variants(baseline, form, selector);
    let complete = variants.len() <= cap;
    variants.truncate(cap);
    let patches = variants
        .iter()
        .map(|(at, patch)| (at.clone(), patch.clone()))
        .collect::<BTreeMap<_, _>>();
    let origins = variants
        .into_iter()
        .map(|(at, _)| PatchOrigin {
            site_tuple: vec![at],
            discovery_tuples: Vec::new(),
        })
        .collect();
    Selection::enumerated(baseline, origins, complete).fold_admitting(
        form.name(),
        |origin| patches[&origin.site_tuple[0]].clone(),
        |mutant| mutant.program_parser(syntax_module),
    )
}

/// The generation of one supplied grammar patch (a mutation a user wrote, which kink-flow
/// resolved into `patch`): one origin, admitted as [`generate_grammar`] admits a generated one,
/// when its mutant gives a program parser for `syntax_module`. The origin's sites are the
/// sentences the patch replaces or deletes and, for an insertion at a module's start or end, the
/// first sentence of that module; their paths are empty, since no form's variant names them.
/// Complete: the generation is the one patch it was given.
///
/// # Errors
///
/// Those of [`Selection::fold_admitting`]: every edit targets a site of the origin, so none.
pub fn supplied_grammar<'b>(
    baseline: &'b Baseline,
    operator: &str,
    patch: &Patch,
    syntax_module: &str,
) -> Result<CandidateGeneration<'b>, CandidateFailure> {
    let mut sites = patch.written_sentences();
    for edit in patch.edits() {
        if let Edit::InsertSentence {
            position: InsertPosition::ModuleStart(module) | InsertPosition::ModuleEnd(module),
            ..
        } = edit
            && !sites.iter().any(|at| at.module == *module)
        {
            sites.push(SentenceRef {
                module: module.clone(),
                index: 0,
            });
        }
    }
    let origin = PatchOrigin {
        site_tuple: sites
            .into_iter()
            .map(|at| TermRef::new(at, Vec::new()))
            .collect(),
        discovery_tuples: Vec::new(),
    };
    Selection::enumerated(baseline, vec![origin], true).fold_admitting(
        operator,
        |_| patch.clone(),
        |mutant| mutant.program_parser(syntax_module),
    )
}

fn admits(clause: &GrammarSelector, at: &SentenceRef, sentence: &Sentence) -> bool {
    match (clause, sentence) {
        (GrammarSelector::Module(module), _) => at.module == *module,
        (GrammarSelector::Sort(wanted), Sentence::Production { sort, .. }) => sort == wanted,
        (GrammarSelector::Label(wanted), Sentence::Production { label, .. }) => {
            label.as_ref().is_some_and(|label| label.name == *wanted)
        }
        (GrammarSelector::Label(wanted), Sentence::SyntaxPriority { priorities, .. }) => {
            priorities.iter().flatten().any(|tag| tag == wanted)
        }
        (GrammarSelector::Label(wanted), Sentence::SyntaxAssociativity { tags, .. }) => {
            tags.contains(wanted)
        }
        _ => false,
    }
}

/// Attributes that leave a production out of the production forms: configuration expansion's
/// cell productions, user lists, brackets and tokens (a token is a regex form's site).
const NOT_A_PRODUCTION_SITE: [AttributeKey; 10] = [
    AttributeKey::Cell,
    AttributeKey::CellName,
    AttributeKey::CellFragment,
    AttributeKey::CellOptAbsent,
    AttributeKey::CellSort,
    AttributeKey::CellCollection,
    AttributeKey::Initializer,
    AttributeKey::UserList,
    AttributeKey::Bracket,
    AttributeKey::Token,
];

/// The attributes an inserted copy keeps: those that only choose among parses. Every other
/// attribute says something of the symbol (its claims, hook, overload family, unit, function or
/// macro kind) or names it (`symbol`, `klabel`) or its items by position (`format`), and a fresh
/// constructor of the site's signature has none of them.
const COPIED_ATTRIBUTES: [AttributeKey; 2] = [AttributeKey::Prefer, AttributeKey::Avoid];

/// A production that the production forms edit: labelled, not a cell, list, bracket or token.
pub(crate) fn production_site(sentence: &Sentence) -> bool {
    matches!(sentence, Sentence::Production { label: Some(_), attributes, .. }
        if !attributes.has_any(&NOT_A_PRODUCTION_SITE))
}

fn production_labels(baseline: &Baseline) -> BTreeSet<String> {
    baseline
        .definition()
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
        .filter_map(|sentence| match sentence.as_ref() {
            Sentence::Production {
                label: Some(label), ..
            } => Some(label.name.clone()),
            _ => None,
        })
        .collect()
}

/// A label no production of the baseline has: `base`, then `base-2`, `base-3`, and so on (the
/// baseline has finitely many labels, so one is free).
fn fresh_label(labels: &BTreeSet<String>, base: &str) -> String {
    let mut candidate = base.to_owned();
    let mut n = 1;
    while labels.contains(&candidate) {
        n += 1;
        candidate = format!("{base}-{n}");
    }
    candidate
}

fn edits_at(
    baseline: &Baseline,
    labels: &BTreeSet<String>,
    form: GrammarForm,
    at: &SentenceRef,
    sentence: &Sentence,
) -> Vec<(Vec<u32>, Vec<Edit>)> {
    let replace = |replacement: Sentence| {
        vec![Edit::ReplaceSentence {
            at: at.clone(),
            replacement,
        }]
    };
    match (form, sentence) {
        (
            GrammarForm::DropTerminal
            | GrammarForm::ChangeTerminal
            | GrammarForm::AlternativeWithoutTerminal
            | GrammarForm::MergeAlternative
            | GrammarForm::DeleteProduction,
            _,
        ) if !production_site(sentence) => Vec::new(),
        (GrammarForm::DropTerminal, Sentence::Production { attributes, .. })
            if attributes.has(AttributeKey::Format) =>
        {
            Vec::new()
        }
        (GrammarForm::DropTerminal, Sentence::Production { items, .. }) => terminals_dropped(items)
            .into_iter()
            .map(|(index, items)| (vec![index], replace(with_items(sentence, items))))
            .collect(),
        (GrammarForm::ChangeTerminal, Sentence::Production { sort, items, .. }) => {
            let texts = sort_terminals(baseline, at, sort);
            let mut variants = Vec::new();
            for (index, item) in items.iter().enumerate() {
                let ProductionItem::Terminal(text) = item else {
                    continue;
                };
                let others = texts.iter().filter(|other| *other != text);
                for (choice, other) in others.enumerate() {
                    let mut changed = items.clone();
                    changed[index] = ProductionItem::Terminal(other.clone());
                    variants.push((
                        vec![index_u32(index), index_u32(choice)],
                        replace(with_items(sentence, changed)),
                    ));
                }
            }
            variants
        }
        (
            GrammarForm::AlternativeWithoutTerminal,
            Sentence::Production {
                label: Some(label),
                items,
                ..
            },
        ) => terminals_dropped(items)
            .into_iter()
            .map(|(index, items)| {
                let name = fresh_label(labels, &format!("{}-kink-without-{index}", label.name));
                let copy = copy_of(sentence, name, None, items);
                (vec![index], insert_after(at, copy))
            })
            .collect(),
        (
            GrammarForm::MergeAlternative,
            Sentence::Production {
                label: Some(label),
                parameters,
                sort,
                items,
                ..
            },
        ) if parameters.is_empty() => module_sorts(baseline, &at.module)
            .into_iter()
            .filter(|other| other != sort)
            .enumerate()
            .map(|(choice, other)| {
                let name = fresh_label(labels, &format!("{}-kink-at-{}", label.name, other.name));
                let copy = copy_of(sentence, name, Some(other), items.clone());
                (vec![index_u32(choice)], insert_after(at, copy))
            })
            .collect(),
        (GrammarForm::DeleteProduction, _) => {
            vec![(Vec::new(), vec![Edit::DeleteSentence { at: at.clone() }])]
        }
        (GrammarForm::LoosenRegex | GrammarForm::NarrowRegex | GrammarForm::DropAnchor, _) => {
            let Some(regex) = token_regex(sentence) else {
                return Vec::new();
            };
            regex_variants(form, &regex)
                .into_iter()
                .map(|(path, edited)| (path, replace(with_regex(sentence, &edited))))
                .collect()
        }
        (
            GrammarForm::MergePriorityGroups
            | GrammarForm::SwapPriorityGroups
            | GrammarForm::ChangeAssociativity
            | GrammarForm::DeleteRelation,
            _,
        ) => relation_edits(form, at, sentence),
        _ => Vec::new(),
    }
}

/// The variants of a priority or associativity form at `sentence`.
fn relation_edits(
    form: GrammarForm,
    at: &SentenceRef,
    sentence: &Sentence,
) -> Vec<(Vec<u32>, Vec<Edit>)> {
    let replace = |replacement: Sentence| {
        vec![Edit::ReplaceSentence {
            at: at.clone(),
            replacement,
        }]
    };
    match (form, sentence) {
        (GrammarForm::MergePriorityGroups, Sentence::SyntaxPriority { priorities, .. }) => (0
            ..priorities.len().saturating_sub(1))
            .map(|index| {
                let mut merged = priorities.clone();
                let next = merged.remove(index + 1);
                merged[index].extend(next);
                (
                    vec![index_u32(index)],
                    replace(with_priorities(sentence, merged)),
                )
            })
            .collect(),
        (GrammarForm::SwapPriorityGroups, Sentence::SyntaxPriority { priorities, .. }) => (0
            ..priorities.len().saturating_sub(1))
            .map(|index| {
                let mut swapped = priorities.clone();
                swapped.swap(index, index + 1);
                (
                    vec![index_u32(index)],
                    replace(with_priorities(sentence, swapped)),
                )
            })
            .collect(),
        (
            GrammarForm::ChangeAssociativity,
            Sentence::SyntaxAssociativity {
                associativity,
                tags,
                attributes,
            },
        ) => [
            Associativity::Left,
            Associativity::Right,
            Associativity::NonAssoc,
        ]
        .into_iter()
        .enumerate()
        .filter(|(_, other)| other != associativity)
        .map(|(index, other)| {
            (
                vec![index_u32(index)],
                replace(Sentence::SyntaxAssociativity {
                    associativity: other,
                    tags: tags.clone(),
                    attributes: attributes.clone(),
                }),
            )
        })
        .collect(),
        (
            GrammarForm::DeleteRelation,
            Sentence::SyntaxPriority { .. } | Sentence::SyntaxAssociativity { .. },
        ) => vec![(Vec::new(), vec![Edit::DeleteSentence { at: at.clone() }])],
        _ => Vec::new(),
    }
}

fn index_u32(index: usize) -> u32 {
    u32::try_from(index).expect("an item index fits u32")
}

fn insert_after(at: &SentenceRef, sentence: Sentence) -> Vec<Edit> {
    vec![Edit::InsertSentence {
        position: InsertPosition::After(at.clone()),
        ordinal: 0,
        sentence,
    }]
}

/// Each terminal's index with the items left when it is removed, where some item is left and
/// they are not one nonterminal alone (a subsort's shape).
fn terminals_dropped(items: &[ProductionItem]) -> Vec<(u32, Vec<ProductionItem>)> {
    items
        .iter()
        .enumerate()
        .filter(|(_, item)| matches!(item, ProductionItem::Terminal(_)))
        .filter_map(|(index, _)| {
            let mut left = items.to_vec();
            left.remove(index);
            let lone_nonterminal = matches!(left.as_slice(), [ProductionItem::NonTerminal { .. }]);
            (!left.is_empty() && !lone_nonterminal).then(|| (index_u32(index), left))
        })
        .collect()
}

/// The distinct terminal texts of the authored production sites of `sort` other than `at`.
fn sort_terminals(baseline: &Baseline, at: &SentenceRef, sort: &Sort) -> BTreeSet<String> {
    baseline
        .authored_sentences()
        .filter(|(other, sentence)| other != at && production_site(sentence))
        .filter_map(|(_, sentence)| match sentence {
            Sentence::Production {
                sort: other, items, ..
            } if other == sort => Some(items),
            _ => None,
        })
        .flatten()
        .filter_map(|item| match item {
            ProductionItem::Terminal(text) => Some(text.clone()),
            _ => None,
        })
        .collect()
}

/// The result sorts of the authored production sites of `module`.
fn module_sorts(baseline: &Baseline, module: &str) -> BTreeSet<Sort> {
    baseline
        .authored_sentences()
        .filter(|(at, sentence)| at.module == module && production_site(sentence))
        .filter_map(|(_, sentence)| match sentence {
            Sentence::Production {
                sort, parameters, ..
            } if parameters.is_empty() => Some(sort.clone()),
            _ => None,
        })
        .collect()
}

fn with_items(sentence: &Sentence, items: Vec<ProductionItem>) -> Sentence {
    let mut sentence = sentence.clone();
    if let Sentence::Production { items: slot, .. } = &mut sentence {
        *slot = items;
    }
    sentence
}

fn with_priorities(sentence: &Sentence, priorities: Vec<Vec<String>>) -> Sentence {
    let mut sentence = sentence.clone();
    if let Sentence::SyntaxPriority {
        priorities: slot, ..
    } = &mut sentence
    {
        *slot = priorities;
    }
    sentence
}

/// A fresh constructor with `production`'s items replaced by `items`, at `sort` or the
/// production's own sort, keeping only [`COPIED_ATTRIBUTES`].
fn copy_of(
    production: &Sentence,
    name: String,
    sort: Option<Sort>,
    items: Vec<ProductionItem>,
) -> Sentence {
    let Sentence::Production {
        label: Some(label),
        parameters,
        sort: own,
        attributes,
        ..
    } = production
    else {
        unreachable!("a production site is a labelled production");
    };
    let mut copied = Attributes::default();
    for key in COPIED_ATTRIBUTES {
        if let Some(value) = attributes.value(key) {
            copied.set(key, value.clone());
        }
    }
    Sentence::Production {
        label: Some(Label::with_parameters(name, label.parameters.clone())),
        parameters: parameters.clone(),
        sort: sort.unwrap_or_else(|| own.clone()),
        items,
        attributes: copied,
    }
}

/// A token definition: a production with `token` whose one item is a regex terminal.
pub(crate) fn regex_token(sentence: &Sentence) -> bool {
    matches!(sentence, Sentence::Production { items, attributes, .. }
        if attributes.has(AttributeKey::Token)
            && matches!(items.as_slice(), [ProductionItem::RegexTerminal { .. }]))
}

/// The regex of a token definition (a production with `token` whose one item is a regex
/// terminal) or of a lexical declaration.
fn token_regex(sentence: &Sentence) -> Option<Regex> {
    let text = match sentence {
        Sentence::Production {
            items, attributes, ..
        } if attributes.has(AttributeKey::Token) => match items.as_slice() {
            [ProductionItem::RegexTerminal { regex }] => regex,
            _ => return None,
        },
        Sentence::SyntaxLexical { regex, .. } => regex,
        _ => return None,
    };
    parse_regex(text).ok()
}

fn with_regex(sentence: &Sentence, regex: &Regex) -> Sentence {
    let text = regex.to_canonical_string();
    let mut sentence = sentence.clone();
    match &mut sentence {
        Sentence::Production { items, .. } => {
            items[0] = ProductionItem::RegexTerminal { regex: text };
        }
        Sentence::SyntaxLexical { regex, .. } => *regex = text,
        _ => unreachable!("a token regex belongs to a token production or a lexical"),
    }
    sentence
}

/// The variants of a regex form: (path, edited regex). A loosening or narrowing path is the
/// node's preorder index and the choice at it; a dropped anchor's is `[0]` for `^`, `[1]` for
/// `$`.
fn regex_variants(form: GrammarForm, regex: &Regex) -> Vec<(Vec<u32>, Regex)> {
    if form == GrammarForm::DropAnchor {
        let mut variants = Vec::new();
        if regex.start_line {
            variants.push((
                vec![0],
                Regex {
                    start_line: false,
                    ..regex.clone()
                },
            ));
        }
        if regex.end_line {
            variants.push((
                vec![1],
                Regex {
                    end_line: false,
                    ..regex.clone()
                },
            ));
        }
        return variants;
    }
    let mut nodes = Vec::new();
    regex
        .body
        .visit_preorder(&mut |node| nodes.push(node.clone()));
    // The nodes directly under `?` or `*`: making one optional changes no language.
    let mut optional = BTreeSet::new();
    let mut next = 0;
    regex.body.visit_preorder(&mut |node| {
        next += 1;
        if matches!(node, RegexBody::ZeroOrOne(_) | RegexBody::ZeroOrMore(_)) {
            optional.insert(next);
        }
    });
    let nullable_before = nullable(&regex.body);
    let mut variants = Vec::new();
    for (index, node) in nodes.iter().enumerate() {
        let choices = if form == GrammarForm::LoosenRegex {
            loosenings(node, optional.contains(&index))
        } else {
            narrowings(node)
        };
        for (choice, replacement) in choices.into_iter().enumerate() {
            let body = replaced(&regex.body, index, &replacement);
            if form == GrammarForm::LoosenRegex && !nullable_before && nullable(&body) {
                continue;
            }
            variants.push((
                vec![index_u32(index), index_u32(choice)],
                Regex {
                    body,
                    ..regex.clone()
                },
            ));
        }
    }
    variants
}

fn boxed(body: &RegexBody) -> Box<RegexBody> {
    Box::new(body.clone())
}

/// The bodies that match every text `node` matches, and more. A node already optional, or
/// directly under `?` or `*` (`under_optional`), is not made optional again.
fn loosenings(node: &RegexBody, under_optional: bool) -> Vec<RegexBody> {
    let mut choices = Vec::new();
    if !under_optional && !matches!(node, RegexBody::ZeroOrOne(_) | RegexBody::ZeroOrMore(_)) {
        choices.push(RegexBody::ZeroOrOne(boxed(node)));
    }
    match node {
        RegexBody::OneOrMore(body) => choices.push(RegexBody::ZeroOrMore(body.clone())),
        RegexBody::Exactly { body, count } if *count > 0 => choices.push(RegexBody::Range {
            body: body.clone(),
            at_least: 0,
            at_most: *count,
        }),
        RegexBody::AtLeast { body, count } if *count > 0 => {
            choices.push(RegexBody::ZeroOrMore(body.clone()));
        }
        RegexBody::Range {
            body,
            at_least,
            at_most,
        } => {
            if *at_least > 0 {
                choices.push(RegexBody::Range {
                    body: body.clone(),
                    at_least: 0,
                    at_most: *at_most,
                });
            }
            choices.push(RegexBody::AtLeast {
                body: body.clone(),
                count: *at_least,
            });
        }
        RegexBody::Char(_) | RegexBody::CharClass { .. } => choices.push(RegexBody::AnyChar),
        _ => {}
    }
    choices
}

/// The bodies that match only texts `node` matches, and fewer.
fn narrowings(node: &RegexBody) -> Vec<RegexBody> {
    match node {
        RegexBody::ZeroOrMore(body) => vec![RegexBody::OneOrMore(body.clone())],
        RegexBody::ZeroOrOne(body) => vec![(**body).clone()],
        RegexBody::Union { left, right } => vec![(**left).clone(), (**right).clone()],
        RegexBody::AtLeast { body, count } => vec![RegexBody::Exactly {
            body: body.clone(),
            count: *count,
        }],
        RegexBody::Range { body, at_least, .. } => vec![RegexBody::Exactly {
            body: body.clone(),
            count: *at_least,
        }],
        RegexBody::CharClass {
            negated: false,
            members,
        } if members.len() > 1 => (0..members.len())
            .map(|dropped| RegexBody::CharClass {
                negated: false,
                members: members
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| *index != dropped)
                    .map(|(_, member)| member.clone())
                    .collect(),
            })
            .collect(),
        _ => Vec::new(),
    }
}

/// `body` with its node at preorder index `target` replaced by `replacement`.
fn replaced(body: &RegexBody, target: usize, replacement: &RegexBody) -> RegexBody {
    fn walk(
        body: &RegexBody,
        next: &mut usize,
        target: usize,
        replacement: &RegexBody,
    ) -> RegexBody {
        let index = *next;
        *next += 1;
        if index == target {
            return replacement.clone();
        }
        let mut child = |inner: &RegexBody| Box::new(walk(inner, next, target, replacement));
        match body {
            RegexBody::Union { left, right } => {
                let left = child(left);
                let right = child(right);
                RegexBody::Union { left, right }
            }
            RegexBody::Concat(members) => RegexBody::Concat(
                members
                    .iter()
                    .map(|member| walk(member, next, target, replacement))
                    .collect(),
            ),
            RegexBody::ZeroOrMore(inner) => RegexBody::ZeroOrMore(child(inner)),
            RegexBody::ZeroOrOne(inner) => RegexBody::ZeroOrOne(child(inner)),
            RegexBody::OneOrMore(inner) => RegexBody::OneOrMore(child(inner)),
            RegexBody::Exactly { body, count } => RegexBody::Exactly {
                body: child(body),
                count: *count,
            },
            RegexBody::AtLeast { body, count } => RegexBody::AtLeast {
                body: child(body),
                count: *count,
            },
            RegexBody::Range {
                body,
                at_least,
                at_most,
            } => RegexBody::Range {
                body: child(body),
                at_least: *at_least,
                at_most: *at_most,
            },
            leaf @ (RegexBody::Char(_)
            | RegexBody::AnyChar
            | RegexBody::Named(_)
            | RegexBody::CharClass { .. }) => leaf.clone(),
        }
    }
    walk(body, &mut 0, target, replacement)
}

/// Whether `body` matches the empty text. A `{Name}` reference counts as not matching it, so a
/// loosening through one is judged by the rest of the regex.
fn nullable(body: &RegexBody) -> bool {
    match body {
        RegexBody::Char(_)
        | RegexBody::AnyChar
        | RegexBody::Named(_)
        | RegexBody::CharClass { .. } => false,
        RegexBody::Union { left, right } => nullable(left) || nullable(right),
        RegexBody::Concat(members) => members.iter().all(nullable),
        RegexBody::ZeroOrMore(_) | RegexBody::ZeroOrOne(_) => true,
        RegexBody::OneOrMore(inner) => nullable(inner),
        RegexBody::Exactly { body, count } | RegexBody::AtLeast { body, count } => {
            *count == 0 || nullable(body)
        }
        RegexBody::Range { body, at_least, .. } => *at_least == 0 || nullable(body),
    }
}
