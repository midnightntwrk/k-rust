//! ```toml algorithm
//! id = "kompile.contexts.resolve"
//! name = "lowering of evaluation contexts"
//! sites = ["resolve_contexts", "resolve_contexts_pass", "prepare_context", "freezer_labels"]
//! variable = "N = context and term nodes; C = generated rules and productions; P = visible productions; V = visible sentences; s = compared sentence size"
//! counters = []
//! no_counter = "context lowering has no dedicated counter"
//!
//! [[cost]]
//! mode = "one definition"
//! bound = "O(N + V + P log P + C^2 x s)"
//! ```
//!
//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Lower evaluation contexts into heat/cool rules and freezer productions.
#![deny(clippy::wildcard_enum_match_arm)]

use super::number_sentences::unique_id_text;
use crate::provenance::extend_unique_sentences as extend_unique;
use std::{collections::BTreeMap, collections::BTreeSet, fmt, sync::Arc};

use serde_json::Value;

use crate::definition::AttributeKey;
use crate::definition::production_kind::ProductionKind;
use crate::kast::binding::quantifier;
use crate::names::BuiltinSort;
use crate::{
    definition::{Attributes, Definition, LabelHead, ProductionCatalog, ProductionItem, Sentence},
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{GeneratedLabel, InternalLabel, Label, Sort, Term, TermParts},
    provenance::{GeneratingPass, seed_generated_sentence_origin, sentence_origin_links},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolveContextsError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for ResolveContextsError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "context resolution produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for ResolveContextsError {}

/// Materialize contexts as freezer productions and paired heat and cool rules.
///
/// The contexts visible from the main module are materialized there. Imported modules remain
/// unchanged: the main module sees every one of these contexts and holds what is generated for
/// them.
pub fn resolve_contexts(definition: &Definition) -> Result<Definition, ResolveContextsError> {
    super::super::pipeline::run_standalone(
        definition,
        resolve_contexts_pass,
        Some(GeneratingPass::ResolveContexts),
    )
}

pub(crate) fn resolve_contexts_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveContextsError> {
    let resolved = input.resolved_raw().map_err(|error| ResolveContextsError {
        diagnostics: vec![plain_error(error.to_string())],
    })?;
    let views = resolved.views();
    let main_id = resolved.main_module_id();
    let productions = views.production_catalog(main_id);
    let contexts = resolved
        .sentences(main_id)
        .into_iter()
        .filter(|sentence| matches!(sentence, Sentence::Context { .. }))
        .collect::<Vec<_>>();
    if contexts.is_empty() {
        return Ok(input.definition.clone());
    }
    let macro_labels = resolved.rule_catalog(main_id).all_macro_labels(productions);

    let mut labels = productions
        .productions()
        .filter_map(|(_, sentence)| match sentence {
            Sentence::Production {
                label: Some(label), ..
            } => Some(label.clone()),
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Rule { .. }
            | Sentence::Claim { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => None,
        })
        .collect::<BTreeSet<_>>();
    let sentence_labels = resolved
        .sentences(main_id)
        .into_iter()
        .filter_map(|sentence| {
            sentence
                .attributes()
                .string(AttributeKey::Label)
                .map(|label| (label.to_owned(), sentence.attributes().clone()))
        })
        .collect::<BTreeMap<_, _>>();
    let mut prepared = Vec::new();
    let mut diagnostics = Vec::new();
    // Invariant: `prepared` holds the lowering of every context of `contexts` before `context` that has one, in order, and `diagnostics` the errors of the others; each iteration consumes one context.
    for context in contexts {
        match prepare_context(context, productions, &macro_labels, &sentence_labels) {
            Ok(context) => prepared.push(context),
            Err(mut errors) => diagnostics.append(&mut errors),
        }
    }
    let freezer_labels = freezer_labels(&prepared, &mut labels);
    let mut generated = Vec::new();
    // Invariant: `generated` holds, without duplicates, the sentences of every prepared context before `context`, each around the freezer `freezer_labels` gives it; each iteration consumes one context.
    for (context, freezer_label) in prepared.into_iter().zip(freezer_labels) {
        extend_unique(&mut generated, context.lower(freezer_label, productions));
    }
    if !diagnostics.is_empty() {
        diagnostics.sort();
        diagnostics.dedup();
        return Err(ResolveContextsError { diagnostics });
    }

    let mut output = input.definition.clone();
    let main = output.main_module.clone();
    let main = output
        .modules
        .iter_mut()
        .find(|module| module.name == main)
        .expect("definition contains its main module");
    main.local_sentences
        .retain(|sentence| !matches!(&**sentence, Sentence::Context { .. }));
    if !generated.is_empty() {
        extend_unique(
            &mut generated,
            [Sentence::SyntaxSort {
                parameters: Vec::new(),
                sort: Sort::builtin(BuiltinSort::K),
                attributes: Attributes::default(),
            }],
        );
        main.local_sentences
            .extend(generated.into_iter().map(Arc::new));
    }
    Ok(output)
}

/// A context checked and taken apart, ready to lower around the freezer it is given.
struct PreparedContext {
    /// The context's term with its rewrite in place, where the heating and cooling rewrites go.
    body: Term,
    requires: Term,
    /// The term the context rewrites: matched by heating, rebuilt by cooling.
    cooled: Term,
    /// What heating puts at the front of the computation.
    heated: Term,
    /// The freezer's arguments.
    variables: Vec<Term>,
    /// The part of the freezer's name the context's own content gives it.
    hint: String,
    /// The context's content, which orders the contexts that share a hint.
    content: String,
    attributes: Attributes,
    heat_attributes: Attributes,
    cool_attributes: Attributes,
    origins: Vec<crate::provenance::ProvenanceLink>,
}

fn prepare_context(
    context: &Sentence,
    productions: &ProductionCatalog<'_>,
    macro_labels: &BTreeSet<LabelHead>,
    sentence_labels: &BTreeMap<String, Attributes>,
) -> Result<PreparedContext, Vec<Diagnostic>> {
    let Sentence::Context {
        body,
        requires,
        attributes,
    } = context
    else {
        unreachable!()
    };
    validate_context(body, attributes)?;
    // The matched root retains its selected production until the admissibility check; stripping
    // metadata first would lose that identity when several productions share a label.
    let left = rewrite_left(body);
    let body = strip_metadata(body);
    let requires = strip_metadata(requires);
    let has_main_cell = contains_main_cell(&body, productions);
    let mut scan = HeatScan {
        productions,
        has_main_cell,
        in_main_cell: false,
        heated: None,
        hole: None,
        variables: Vec::new(),
        seen: BTreeSet::new(),
        bound: Vec::new(),
        current_hole_position: 0,
        final_hole_position: 0,
    };
    scan.visit(&body);
    let heated = scan
        .heated
        .or(scan.hole)
        .expect("validated contexts contain a hole");
    let variables = scan.variables;
    let cooled = find_cooled(&left, productions).unwrap_or(left);
    if let Term::Apply { label, .. } = cooled.unannotated()
        && label.generated().is_none()
        && InternalLabel::of(&label.name).is_none()
    {
        let head = LabelHead::from(label);
        let production = cooled
            .metadata()
            .and_then(|metadata| metadata.production)
            .and_then(|identity| productions.lookup(&identity))
            .map(|id| productions.production(id))
            .filter(|production| {
                matches!(production, Sentence::Production { label: Some(candidate), .. } if candidate.name == label.name)
            })
            .or_else(|| {
                let candidates = productions.productions_for(&head);
                (candidates.len() == 1).then(|| productions.production(candidates[0]))
            });
        if let Some(production) = production {
            let kind = ProductionKind::of(production);
            let reason = if !kind.rewrite_steps_meet_applications() {
                Some(match kind {
                    ProductionKind::Function { .. } => {
                        "its applications are evaluated by its equations"
                    }
                    ProductionKind::MacroProduction => {
                        "its applications are expanded before rewriting"
                    }
                    ProductionKind::Bracket(_) => {
                        "every parser erases a bracket, so no term applies it"
                    }
                    ProductionKind::Token { .. } => "a token production's terms are domain values",
                    ProductionKind::Builtin => {
                        "it is a matching-logic connective or the K sequence, which the prelude declares"
                    }
                    ProductionKind::Subsort | ProductionKind::Unlabelled => {
                        "its production declares no symbol"
                    }
                    ProductionKind::Base | ProductionKind::Algebraic => {
                        unreachable!("rewrite steps meet these applications")
                    }
                })
            } else if macro_labels.contains(&head) {
                Some("its label is macro-like and its applications are expanded before rewriting")
            } else {
                None
            };
            if let Some(reason) = reason {
                return Err(vec![error_at(
                    format!(
                        "Cannot compile a context rooted at {label}: {reason}; a context lowers to heating and cooling rewrite rules that match its term, and no rewrite step meets an application of {label}"
                    ),
                    attributes,
                )]);
            }
        }
    }
    let cooled = strip_metadata(&cooled);
    let hint = freezer_hint(&cooled, scan.final_hole_position, attributes);
    let content = context_content(&body, &requires, attributes);

    let heat_attributes = rule_attributes(attributes, AttributeKey::Heat, "-heat");
    let cool_attributes = rule_attributes(attributes, AttributeKey::Cool, "-cool");
    for rule_attributes in [&heat_attributes, &cool_attributes] {
        if let Some(label) = rule_attributes.string(AttributeKey::Label)
            && let Some(conflict) = sentence_labels.get(label)
        {
            return Err(vec![error_at(
                format!(
                    "The generated label for a context rule conflicts with a user-defined label {label}. Please consider renaming."
                ),
                conflict,
            )]);
        }
    }

    Ok(PreparedContext {
        body,
        requires,
        cooled,
        heated,
        variables,
        hint,
        content,
        attributes: attributes.clone(),
        heat_attributes,
        cool_attributes,
        origins: sentence_origin_links(context),
    })
}

impl PreparedContext {
    /// The freezer production and the heating and cooling rules around it.
    fn lower(self, freezer_label: Label, productions: &ProductionCatalog<'_>) -> Vec<Sentence> {
        let Self {
            body,
            requires,
            cooled,
            heated,
            variables,
            attributes,
            heat_attributes,
            cool_attributes,
            origins,
            ..
        } = self;
        let mut freezer_items = vec![
            ProductionItem::Terminal(freezer_label.name.clone()),
            ProductionItem::Terminal("(".into()),
        ];
        for index in 0..variables.len() {
            if index > 0 {
                freezer_items.push(ProductionItem::Terminal(",".into()));
            }
            freezer_items.push(ProductionItem::NonTerminal {
                sort: Sort::builtin(BuiltinSort::K),
                name: None,
            });
        }
        freezer_items.push(ProductionItem::Terminal(")".into()));
        let freezer = Sentence::Production {
            label: Some(freezer_label.clone()),
            parameters: Vec::new(),
            sort: Sort::builtin(BuiltinSort::KItem),
            items: freezer_items,
            attributes: Attributes::default(),
        };
        let frozen = Term::Apply {
            label: freezer_label,
            arguments: variables,
        };
        let heated_and_frozen = Term::sequence([heated, frozen]);
        let heat_rewrite = Term::Rewrite {
            left: Box::new(cooled.clone()),
            right: Box::new(heated_and_frozen.clone()),
        };
        let cool_rewrite = Term::Rewrite {
            left: Box::new(heated_and_frozen),
            right: Box::new(cooled),
        };
        let mut generated = vec![
            freezer,
            Sentence::Rule {
                body: insert(body.clone(), heat_rewrite, productions).0,
                requires,
                ensures: bool_token(true),
                attributes: heat_attributes,
            },
            Sentence::Rule {
                body: insert(body, cool_rewrite, productions).0,
                requires: bool_token(true),
                ensures: bool_token(true),
                attributes: cool_attributes,
            },
        ];
        // The freezer, heating, and cooling sentences all derive from this context alone.
        for sentence in &mut generated {
            sentence.attributes_mut().union_input_addresses(&attributes);
            seed_generated_sentence_origin(
                sentence,
                GeneratingPass::ResolveContexts,
                origins.clone(),
            );
        }
        generated
    }
}

struct HeatScan<'a, 'definition> {
    productions: &'a ProductionCatalog<'definition>,
    has_main_cell: bool,
    in_main_cell: bool,
    heated: Option<Term>,
    hole: Option<Term>,
    /// The context's variables other than `HOLE`, each once, in the order of their first
    /// occurrence: the freezer's arguments. A freezer's argument positions are internal to the
    /// heating and cooling pair, so any order consistent between the two denotes the same rules;
    /// first occurrence is the one that reads no name, so an alpha-variant of the context lowers
    /// to an alpha-variant of the pair. For a context strictness generates this is the order of
    /// the production's arguments (`K2` before `K10`).
    variables: Vec<Term>,
    /// The names in `variables`.
    seen: BTreeSet<String>,
    /// The names the quantifiers around the visited term bind. A bound variable belongs to its
    /// quantifier, which the freezer holds whole when it holds the term around it, so it is no
    /// variable of the context: freezing it would put its name free beside its binder.
    bound: Vec<String>,
    current_hole_position: usize,
    final_hole_position: usize,
}

impl HeatScan<'_, '_> {
    // Invariant: `self.variables` holds the distinct non-`HOLE` variables visited so far in preorder that no enclosing quantifier binds (`self.bound`), by first occurrence (`self.seen` their names), and `self.current_hole_position` counts their occurrences, where `self.in_main_cell || !self.has_main_cell` holds, and `self.hole` the last `HOLE` found there; each call recurses into the immediate subterms of `term`.
    fn visit(&mut self, term: &Term) {
        match term.unannotated() {
            Term::Rewrite { left, right } => {
                self.heated = Some((**right).clone());
                self.visit(left);
                self.visit(right);
            }
            Term::As { pattern, alias } => {
                self.visit(pattern);
                self.visit(alias);
            }
            Term::Sequence(items) => {
                for item in items {
                    self.visit(item);
                }
            }
            Term::Apply { label, arguments } => {
                let main_cell = is_main_cell(label, self.productions);
                if main_cell {
                    self.in_main_cell = true;
                }
                let scope = self.bound.len();
                if let Some(quantifier) = quantifier(term) {
                    self.bound
                        .extend(quantifier.bound().into_iter().map(str::to_owned));
                }
                for argument in arguments {
                    self.visit(argument);
                }
                self.bound.truncate(scope);
                if main_cell {
                    self.in_main_cell = false;
                }
            }
            Term::Variable { name, .. } => {
                if self.in_main_cell || !self.has_main_cell {
                    if name == "HOLE" {
                        self.hole = Some(term.clone());
                        self.final_hole_position = self.current_hole_position;
                    } else {
                        if !self.bound.contains(name) && self.seen.insert(name.clone()) {
                            self.variables.push(term.clone());
                        }
                        self.current_hole_position += 1;
                    }
                }
            }
            Term::InjectedLabel(_) | Term::Token { .. } => {}
            Term::Annotated { .. } => unreachable!(),
        }
    }
}

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
fn validate_context(body: &Term, attributes: &Attributes) -> Result<(), Vec<Diagnostic>> {
    let mut holes = BTreeSet::new();
    let mut rewrites = Vec::new();
    // Invariant: `holes` holds every `HOLE` variable and `rewrites` every distinct rewrite among the subterms of `body` visited so far in preorder; the finite `body` bounds the visit, and `rewrites.contains` scans one entry per distinct rewrite.
    body.visit_preorder(&mut |term| match term.unannotated() {
        Term::Variable { name, .. } if name == "HOLE" => {
            holes.insert(term.clone());
        }
        Term::Rewrite { .. } if !rewrites.contains(&term.clone()) => rewrites.push(term.clone()),
        _ => {}
    });
    if holes.is_empty() {
        return Err(vec![error_at(
            "Contexts must have at least one HOLE.",
            attributes,
        )]);
    }
    if rewrites.len() > 1 {
        return Err(vec![error_at(
            "Cannot compile a context with multiple rewrites.",
            attributes,
        )]);
    }
    for rewrite in rewrites {
        let Term::Rewrite { left, right } = rewrite.unannotated() else {
            unreachable!()
        };
        if !is_hole(left) {
            return Err(vec![error_at(
                "Only the HOLE can be rewritten in a context definition",
                attributes,
            )]);
        }
        // Heating puts the rewritten term in front of the computation, and cooling matches that
        // term, once evaluated, to plug its HOLE back into the context: a rewritten term without
        // HOLE leaves the cooled context's HOLE bound by nothing.
        let mut rewritten_hole = false;
        right.visit_preorder(&mut |term| {
            rewritten_hole |= matches!(term, Term::Variable { name, .. } if name == "HOLE");
        });
        if !rewritten_hole {
            return Err(vec![error_at(
                "The HOLE of a context must be rewritten to a term containing HOLE: cooling matches that term to plug its HOLE back into the context.",
                attributes,
            )]);
        }
    }
    Ok(())
}

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
fn is_hole(term: &Term) -> bool {
    match term.unannotated() {
        Term::Variable { name, .. } => name == "HOLE",
        Term::Apply { label, arguments }
            if matches!(label.generated(), Some(GeneratedLabel::SemanticCast { .. }))
                && arguments.len() == 1 =>
        {
            matches!(
                arguments[0].unannotated(),
                Term::Variable { name, .. } if name == "HOLE"
            )
        }
        _ => false,
    }
}

fn contains_main_cell(term: &Term, productions: &ProductionCatalog<'_>) -> bool {
    let mut found = false;
    term.visit_preorder(&mut |term| {
        if let Term::Apply { label, .. } = term.unannotated()
            && is_main_cell(label, productions)
        {
            found = true;
        }
    });
    found
}

fn is_main_cell(label: &Label, productions: &ProductionCatalog<'_>) -> bool {
    productions
        .attributes_for(&LabelHead::from(label))
        .is_some_and(|attributes| attributes.has(AttributeKey::Maincell))
}

fn find_cooled(term: &Term, productions: &ProductionCatalog<'_>) -> Option<Term> {
    // Invariant: `cooled` holds the second argument of the last main-cell application visited so far in preorder; each call recurses into the immediate subterms of `term`, so the finite `term` bounds the visit.
    fn visit(term: &Term, productions: &ProductionCatalog<'_>, cooled: &mut Option<Term>) {
        match term.unannotated() {
            Term::Apply { label, arguments } => {
                if is_main_cell(label, productions)
                    && let Some(body) = arguments.get(1)
                {
                    *cooled = Some(body.clone());
                }
                for argument in arguments {
                    visit(argument, productions, cooled);
                }
            }
            Term::Rewrite { left, right }
            | Term::As {
                pattern: left,
                alias: right,
            } => {
                visit(left, productions, cooled);
                visit(right, productions, cooled);
            }
            Term::Sequence(items) => {
                for item in items {
                    visit(item, productions, cooled);
                }
            }
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
            Term::Annotated { .. } => unreachable!(),
        }
    }
    let mut cooled = None;
    visit(term, productions, &mut cooled);
    cooled
}

/// The part of a context's freezer name its own content gives it: the head of the term the
/// context rewrites (for a K sequence, of the item holding the hole, or of its first item when no
/// item holds it), or else the context's label, followed by the position of the hole among the
/// context's variables. It reads nothing but the context, so no other context changes it.
fn freezer_hint(cooled: &Term, hole_position: usize, attributes: &Attributes) -> String {
    let name = content_head(cooled)
        .or_else(|| attributes.string(AttributeKey::Label))
        .unwrap_or_default();
    format!("{name}{hole_position}")
}

/// The label heading `term`: an application's label, the head of the term inside a sort cast,
/// and, for a K sequence, the head of the item holding the hole (of the first item when no item
/// holds it). A variable has no head, whatever sort a cast gives it, and neither has a token, an
/// empty sequence or a term without a label: each gives `None`. A cast only states the sort of
/// the term it holds, so the term names the context, not the cast.
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
fn content_head(term: &Term) -> Option<&str> {
    match term.unannotated() {
        Term::Apply { label, arguments }
            if matches!(label.generated(), Some(GeneratedLabel::SemanticCast { .. })) =>
        {
            arguments.first().and_then(content_head)
        }
        Term::Apply { label, .. } => Some(&label.name),
        Term::Sequence(items) => items
            .iter()
            .find(|item| holds_hole(item))
            .or_else(|| items.first())
            .and_then(content_head),
        _ => None,
    }
}

fn holds_hole(term: &Term) -> bool {
    let mut found = false;
    term.visit_preorder(&mut |term| {
        found |= matches!(term, Term::Variable { name, .. } if name == "HOLE");
    });
    found
}

/// The text of a context that two contexts differ in exactly when they denote different
/// contexts: its term and condition with variables numbered by first occurrence, the way a
/// rule's identifier text writes them, and its attributes other than where it was read.
fn context_content(body: &Term, requires: &Term, attributes: &Attributes) -> String {
    let mut written = Attributes::default();
    for (key, value) in attributes.wire_entries() {
        let provenance = AttributeKey::from_name(key)
            .is_some_and(|key| key.is_provenance_only() || key.is_source_position());
        if !provenance {
            written.insert(key, value.clone());
        }
    }
    let rule = Sentence::Rule {
        body: body.clone(),
        requires: requires.clone(),
        ensures: bool_token(true),
        attributes: Attributes::default(),
    };
    unique_id_text(&rule, &written)
}

/// The freezer label of each prepared context, in order.
///
/// A freezer is a symbol of the definition, and its name and the identifiers of the heating and
/// cooling rules that mention it should change only when the context changes. A context whose
/// hint no other context shares is named by the hint alone. Contexts sharing a hint are ordered by
/// their content (declaration order only between contexts written alike) and numbered in that
/// order, so adding or removing a context renames only contexts of the same hint. A name some
/// production already has (in `labels`) is skipped.
fn freezer_labels(prepared: &[PreparedContext], labels: &mut BTreeSet<Label>) -> Vec<Label> {
    let mut by_hint = BTreeMap::<&str, Vec<usize>>::new();
    for (index, context) in prepared.iter().enumerate() {
        by_hint.entry(&context.hint).or_default().push(index);
    }
    let mut named = vec![None; prepared.len()];
    // Invariant: `named` holds the label of every context whose hint precedes `hint`, and `labels` those labels besides the productions' own; each iteration names one hint's contexts.
    for (hint, mut indices) in by_hint {
        indices.sort_by(|left, right| {
            prepared[*left]
                .content
                .cmp(&prepared[*right].content)
                .then(left.cmp(right))
        });
        for index in indices {
            named[index] = Some(unique_freezer_label(labels, hint));
        }
    }
    named
        .into_iter()
        .map(|label| label.expect("every context has a hint"))
        .collect()
}

fn unique_freezer_label(labels: &mut BTreeSet<Label>, hint: &str) -> Label {
    let mut attempt = 0usize;
    // Invariant: every freezer label for `hint` with a suffix tried so far is already in `labels`, and `attempt` counts those attempts; each iteration tries a new suffix, so the finite `labels` bounds the loop to `labels.len() + 1` iterations.
    loop {
        let suffix = if attempt == 0 {
            String::new()
        } else {
            (attempt + 1).to_string()
        };
        let label = Label::freezer(hint, &suffix);
        if labels.insert(label.clone()) {
            return label;
        }
        attempt += 1;
    }
}

fn rule_attributes(source: &Attributes, marker: AttributeKey, suffix: &str) -> Attributes {
    let mut attributes = source.clone();
    attributes.mark(marker);
    if let Some(label) = source.string(AttributeKey::Label) {
        attributes.set(
            AttributeKey::Label,
            Value::String(format!("{label}{suffix}")),
        );
    }
    attributes
}

fn insert(term: Term, rewrite: Term, productions: &ProductionCatalog<'_>) -> (Term, bool) {
    let (inserted, found) = insert_inner(term, &rewrite, productions);
    if found {
        (inserted, true)
    } else {
        (rewrite, false)
    }
}

// Invariant: each call stops at a main-cell application or recurses into the immediate subterms of `term`; the returned flag is true exactly when a three-argument main cell below `term` had its middle argument replaced by `rewrite`.
fn insert_inner(term: Term, rewrite: &Term, productions: &ProductionCatalog<'_>) -> (Term, bool) {
    match term.into_parts() {
        TermParts::Annotated { term, metadata } => {
            let (term, found) = insert_inner(*term, rewrite, productions);
            (term.with_metadata(metadata), found)
        }
        TermParts::Apply { label, arguments } if is_main_cell(&label, productions) => {
            if let [left, _, right] = arguments.as_slice() {
                (
                    Term::Apply {
                        label,
                        arguments: vec![left.clone(), rewrite.clone(), right.clone()],
                    },
                    true,
                )
            } else {
                (Term::Apply { label, arguments }, false)
            }
        }
        TermParts::Rewrite { left, right } => {
            let (left, left_found) = insert_inner(*left, rewrite, productions);
            let (right, right_found) = insert_inner(*right, rewrite, productions);
            (
                Term::Rewrite {
                    left: Box::new(left),
                    right: Box::new(right),
                },
                left_found || right_found,
            )
        }
        TermParts::As { pattern, alias } => {
            let (pattern, pattern_found) = insert_inner(*pattern, rewrite, productions);
            let (alias, alias_found) = insert_inner(*alias, rewrite, productions);
            (
                Term::As {
                    pattern: Box::new(pattern),
                    alias: Box::new(alias),
                },
                pattern_found || alias_found,
            )
        }
        TermParts::Sequence(items) => {
            let mut found = false;
            let items = items
                .into_iter()
                .map(|item| {
                    let (item, item_found) = insert_inner(item, rewrite, productions);
                    found |= item_found;
                    item
                })
                .collect();
            (Term::Sequence(items), found)
        }
        TermParts::Apply { label, arguments } => {
            let mut found = false;
            let arguments = arguments
                .into_iter()
                .map(|argument| {
                    let (argument, argument_found) = insert_inner(argument, rewrite, productions);
                    found |= argument_found;
                    argument
                })
                .collect();
            (Term::Apply { label, arguments }, found)
        }
        leaf @ (TermParts::InjectedLabel(_)
        | TermParts::Variable { .. }
        | TermParts::Token { .. }) => (Term::from(leaf), false),
    }
}

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
fn rewrite_left(term: &Term) -> Term {
    match term {
        Term::Annotated { term, metadata } => match term.unannotated() {
            Term::Rewrite { left, .. } => rewrite_left(left),
            _ => rewrite_left(term).with_metadata(metadata.clone()),
        },
        Term::Rewrite { left, .. } => rewrite_left(left),
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments.iter().map(rewrite_left).collect(),
        },
        Term::Sequence(items) => Term::Sequence(items.iter().map(rewrite_left).collect()),
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(rewrite_left(pattern)),
            alias: alias.clone(),
        },
        term => term.clone(),
    }
}

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
fn strip_metadata(term: &Term) -> Term {
    match term.unannotated() {
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(strip_metadata(left)),
            right: Box::new(strip_metadata(right)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(strip_metadata(pattern)),
            alias: Box::new(strip_metadata(alias)),
        },
        Term::Sequence(items) => Term::Sequence(items.iter().map(strip_metadata).collect()),
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments.iter().map(strip_metadata).collect(),
        },
        term => term.clone(),
    }
}

fn bool_token(value: bool) -> Term {
    Term::Token {
        token: value.to_string(),
        sort: Sort::builtin(BuiltinSort::Bool),
    }
}

fn error_at(message: impl Into<String>, attributes: &Attributes) -> Diagnostic {
    Diagnostic::error_at(DiagnosticCode::InvalidContext, message, attributes)
}

fn plain_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        severity: Severity::Error,
        code: DiagnosticCode::InvalidContext,
        message: message.into(),
        source: None,
        location: None,
        input_addresses: Vec::new(),
    }
}

/// The stage on the definition the pipeline gives it ([`crate::kompile::stage_harness`]).
#[cfg(test)]
mod stage_tests {
    use crate::{
        definition::{ProductionItem, Sentence},
        diagnostic::DiagnosticCode,
        kompile::stage_harness::{labelled, module, render, run_to_stage, sentence_changes},
    };

    /// A context `C[HOLE] requires R` says: when `C[HOLE]` is the next computation and `R`
    /// holds, evaluate `HOLE` first. Lowering states this as two rules around a freezer, a
    /// constructor that holds the rest of `C`: heating `C[HOLE] => HOLE ~> freezer(rest)` under
    /// `R`, and cooling `HOLE ~> freezer(rest) => C[HOLE]`, which plugs the value back in place.
    /// Cooling has no condition of its own (the heat/cool stage adds the result tests), and the
    /// freezer keeps exactly the variables of `C` other than `HOLE`, so cooling rebuilds `C`.
    ///
    /// The contexts the pipeline hands this stage include those strictness generated, so every
    /// one of them, and the user's context, must come out as such a pair.
    #[test]
    fn every_context_lowers_to_a_heating_and_a_cooling_rule_around_a_freezer() {
        let run = run_to_stage(
            r#"
module BOOL
  syntax Bool ::= Bool "andBool" Bool [function, total, symbol(_andBool_), hook(BOOL.and)]
                | "notBool" Bool [function, total, symbol(notBool_), hook(BOOL.not)]
endmodule
module MAIN
  syntax K
  syntax KResult
  syntax Val ::= "v" [symbol(v)]
  syntax KResult ::= Val
  syntax Exp ::= Val
               | plus(Exp, Exp) [strict, symbol(plus)]
               | seq(Exp, Exp) [seqstrict, symbol(seq)]
               | wrap(Exp) [symbol(wrap)]
  context wrap(HOLE:Exp)
  configuration <k> v </k>
endmodule
"#,
            "resolve contexts",
        );
        let (added, removed) = sentence_changes(&run.input, run.output());
        let contexts = removed
            .iter()
            .map(|(_, sentence)| {
                let Sentence::Context { body, requires, .. } = sentence else {
                    panic!(
                        "the stage removed a sentence that is not a context: {}",
                        render(sentence)
                    )
                };
                (body.to_string(), requires.to_string())
            })
            .collect::<Vec<_>>();
        // Two contexts of `plus`, two of `seq`, and `wrap`.
        assert_eq!(contexts.len(), 5, "{contexts:?}");
        assert_eq!(
            run.input
                .modules
                .iter()
                .flat_map(|module| &module.local_sentences)
                .filter(|sentence| matches!(&***sentence, Sentence::Context { .. }))
                .count(),
            5,
            "the stage lowers every context it receives"
        );

        let rules = |attribute: &str| {
            added
                .iter()
                .filter_map(|(_, sentence)| {
                    let Sentence::Rule {
                        body,
                        requires,
                        ensures,
                        attributes,
                    } = sentence
                    else {
                        return None;
                    };
                    attributes
                        .get(attribute)
                        .is_some()
                        .then(|| (body.to_string(), requires.to_string(), ensures.to_string()))
                })
                .collect::<Vec<_>>()
        };
        let (heating, cooling) = (rules("heat"), rules("cool"));
        let freezers = added
            .iter()
            .filter_map(|(_, sentence)| {
                let Sentence::Production {
                    label: Some(label),
                    items,
                    ..
                } = sentence
                else {
                    return None;
                };
                label.name.starts_with("#freezer").then(|| {
                    (
                        label.name.clone(),
                        items
                            .iter()
                            .filter(|item| matches!(item, ProductionItem::NonTerminal { .. }))
                            .count(),
                    )
                })
            })
            .collect::<Vec<_>>();
        assert_eq!(heating.len(), contexts.len(), "{heating:#?}");
        assert_eq!(cooling.len(), contexts.len(), "{cooling:#?}");
        assert_eq!(freezers.len(), contexts.len(), "{freezers:?}");
        assert_eq!(
            added.len(),
            3 * contexts.len(),
            "the stage adds only the rules and freezers: {:#?}",
            added
                .iter()
                .map(|(_, sentence)| render(sentence))
                .collect::<Vec<_>>()
        );

        let truth = r#"#token("true","Bool")"#;
        for (context, condition) in &contexts {
            let (_, frozen, _) = heating
                .iter()
                .find_map(|(body, requires, ensures)| {
                    let frozen = body
                        .strip_prefix(&format!("{context}=>``HOLE~>"))?
                        .strip_suffix("``")?;
                    (requires == condition && ensures == truth).then_some((
                        body,
                        frozen,
                        (requires, ensures),
                    ))
                })
                .unwrap_or_else(|| {
                    panic!("no heating rule of {context} under {condition}: {heating:#?}")
                });
            assert!(
                cooling.contains(&(
                    format!("``HOLE~>{frozen}``=>{context}"),
                    truth.to_owned(),
                    truth.to_owned()
                )),
                "no cooling rule plugging {frozen} back into {context}: {cooling:#?}"
            );
            // The freezer holds the variables of the context other than HOLE: here every
            // context variable is `K<n>`, one per other argument.
            let held = context.matches("(K").count();
            let label = frozen.trim_start_matches('`').split('`').next().unwrap();
            assert!(
                freezers.contains(&(label.to_owned(), held)),
                "{label} should take {held} arguments: {freezers:?}"
            );
        }
    }

    /// The freezer's arguments are the context's variables other than `HOLE` in the order of
    /// their first occurrence, never in the order of their names: a renaming of the context then
    /// renames the heating and cooling rules and permutes nothing. `f(HOLE, Y, X)` freezes
    /// `(Y, X)`, and a context strictness generates freezes the production's other arguments in
    /// their order, so `K2` comes before `K10`.
    #[test]
    fn freezer_arguments_follow_first_occurrence_not_spelling() {
        let run = run_to_stage(
            r#"
module BOOL
  syntax Bool ::= Bool "andBool" Bool [function, total, symbol(_andBool_), hook(BOOL.and)]
                | "notBool" Bool [function, total, symbol(notBool_), hook(BOOL.not)]
endmodule
module MAIN
  syntax K
  syntax KResult
  syntax Val ::= "v" [symbol(v)]
  syntax KResult ::= Val
  syntax Exp ::= Val
               | f(Exp, Exp, Exp) [symbol(f)]
               | big(Exp, Exp, Exp, Exp, Exp, Exp, Exp, Exp, Exp, Exp, Exp, Exp) [strict(1), symbol(big)]
  context f(HOLE, Y, X)
  configuration <k> v </k>
endmodule
"#,
            "resolve contexts",
        );
        let (added, _) = sentence_changes(&run.input, run.output());
        let frozen = added
            .iter()
            .filter_map(|(_, sentence)| {
                let Sentence::Rule {
                    body, attributes, ..
                } = sentence
                else {
                    return None;
                };
                attributes.get("heat").is_some().then(|| {
                    let body = body.to_string();
                    let frozen = body
                        .split_once("=>``HOLE~>")
                        .and_then(|(_, frozen)| frozen.strip_suffix("``"))
                        .map(str::to_owned);
                    frozen.unwrap_or_else(|| panic!("a heating rule without a freezer: {body}"))
                })
            })
            .collect::<Vec<_>>();
        let arguments = |frozen: &str| {
            let (_, arguments) = frozen.split_once('(').expect("the freezer is applied");
            arguments
                .trim_end_matches(')')
                .split(',')
                .map(|argument| argument.split(':').next().unwrap().to_owned())
                .collect::<Vec<_>>()
        };
        let mut found = frozen
            .iter()
            .map(|frozen| arguments(frozen))
            .collect::<Vec<_>>();
        found.sort();
        let mut expected = vec![
            vec!["Y".to_owned(), "X".to_owned()],
            (1..12).map(|index| format!("K{index}")).collect(),
        ];
        expected.sort();
        assert_eq!(found, expected, "{frozen:#?}");
    }

    /// The freezer the heating rule labelled `label`-heat uses, and the `UNIQUE_ID`s of the
    /// heating and cooling rules of `label`, after the stage that numbers sentences.
    fn freezer_and_ids(source: &str, label: &str) -> (String, String, String) {
        let run = run_to_stage(source, "number sentences");
        let rule = |suffix: &str| {
            let [rule] = labelled(run.output(), "MAIN", &format!("MAIN.{label}{suffix}"))[..]
            else {
                panic!("one rule labelled {label}{suffix}")
            };
            rule
        };
        let (heat, cool) = (rule("-heat"), rule("-cool"));
        let id = |rule: &Sentence| {
            rule.attributes()
                .get_str("UNIQUE_ID")
                .expect("numbered")
                .to_owned()
        };
        let Sentence::Rule { body, .. } = heat else {
            panic!("{}", render(heat))
        };
        let body = body.to_string();
        let start = body.find("#freezer").expect("heating freezes");
        let freezer = body[start..]
            .split(['(', '`'])
            .next()
            .expect("a label")
            .to_owned();
        (freezer, id(heat), id(cool))
    }

    /// A freezer is a symbol of the definition generated for one context, so its name, and the
    /// identifiers of the heating and cooling rules that mention it, depend on that context
    /// alone. `hop`'s context rewrites a K sequence, whose first item names it; adding an unrelated
    /// context before it, one more K sequence and one application, renames nothing of `hop`'s.
    #[test]
    fn adding_a_context_leaves_another_contexts_freezer_and_rule_identifiers() {
        let alone = r#"
module BOOL
  syntax Bool ::= Bool "andBool" Bool [function, total, symbol(_andBool_), hook(BOOL.and)]
                | "notBool" Bool [function, total, symbol(notBool_), hook(BOOL.not)]
endmodule
module MAIN
  syntax K
  syntax KResult
  syntax Val ::= "v" [symbol(v)]
  syntax KResult ::= Val
  syntax Exp ::= Val
               | hop(Exp) [symbol(hop)]
               | jump(Exp) [symbol(jump)]
               | wrap(Exp) [symbol(wrap)]
  context [hop]: <k> hop(HOLE:Exp) ~> R:K </k>
  configuration <k> v </k>
endmodule
"#;
        let hop = "  context [hop]:";
        let beside = alone.replace(
            hop,
            &format!(
                "  context [jump]: <k> jump(HOLE:Exp) ~> R:K </k>\n  context wrap(HOLE:Exp)\n{hop}"
            ),
        );
        let before = freezer_and_ids(alone, "hop");
        assert_eq!(before.0, "#freezerhop0_", "{before:?}");
        assert_eq!(freezer_and_ids(&beside, "hop"), before);
        assert_eq!(freezer_and_ids(&beside, "jump").0, "#freezerjump0_");
    }

    /// The heating and cooling rules of module `MAIN` after the stage that numbers sentences,
    /// each as its body (which names its freezer) and its `UNIQUE_ID`.
    fn heat_and_cool_rules(source: &str) -> std::collections::BTreeSet<(String, String)> {
        let run = run_to_stage(source, "number sentences");
        module(run.output(), "MAIN")
            .local_sentences
            .iter()
            .filter_map(|sentence| {
                let Sentence::Rule {
                    body, attributes, ..
                } = &**sentence
                else {
                    return None;
                };
                (attributes.get("heat").is_some() || attributes.get("cool").is_some()).then(|| {
                    let id = attributes
                        .get_str("UNIQUE_ID")
                        .expect("numbered")
                        .to_owned();
                    (body.to_string(), id)
                })
            })
            .collect()
    }

    /// A sort-annotated variable is parsed as a sort cast of the variable, and a variable has no
    /// head whatever its sort, so a K sequence led by one is named by the item holding the hole,
    /// and a context whose hole item is the hole itself by its label. Adding unrelated contexts
    /// led by a variable of the same sort, labelled and not, renames none of the other contexts'
    /// freezers and moves none of their heating or cooling rules' identifiers.
    #[test]
    fn a_context_led_by_a_sorted_variable_is_named_by_its_hole_item_or_label() {
        let alone = r#"
module BOOL
  syntax Bool ::= Bool "andBool" Bool [function, total, symbol(_andBool_), hook(BOOL.and)]
                | "notBool" Bool [function, total, symbol(notBool_), hook(BOOL.not)]
endmodule
module MAIN
  syntax K
  syntax KResult
  syntax Val ::= "v" [symbol(v)]
  syntax KResult ::= Val
  syntax Exp ::= Val
               | hop(Exp) [symbol(hop)]
               | jump(Exp) [symbol(jump)]
               | wrap(Exp) [symbol(wrap)]
  context [mine]: <k> V:Val ~> hop(HOLE:Exp) ~> R:K </k>
  context <k> V:Val ~> hop(HOLE:Exp) </k>
  context [lead]: <k> HOLE:Exp ~> R:K </k>
  configuration <k> v </k>
endmodule
"#;
        let mine = "  context [mine]:";
        let beside = alone.replace(
            mine,
            &format!(
                "  context [other]: <k> W:Val ~> jump(HOLE:Exp) </k>\n  context <k> W:Val ~> wrap(HOLE:Exp) ~> R:K </k>\n  context [also]: <k> HOLE:Exp ~> W:Val </k>\n{mine}"
            ),
        );
        let names = |source: &str| ["mine", "lead"].map(|label| freezer_and_ids(source, label).0);
        let named = names(alone);
        assert!(named[0].starts_with("#freezerhop1_"), "{named:?}");
        assert_eq!(named[1], "#freezerMAIN.lead0_", "{named:?}");
        assert_eq!(names(&beside), named);
        assert_eq!(freezer_and_ids(&beside, "other").0, "#freezerjump1_");
        let (rules_alone, rules_beside) =
            (heat_and_cool_rules(alone), heat_and_cool_rules(&beside));
        assert_eq!(rules_alone.len(), 6, "{rules_alone:#?}");
        let moved = rules_alone.difference(&rules_beside).collect::<Vec<_>>();
        assert!(moved.is_empty(), "{moved:#?}");
    }

    /// Contexts whose content gives the same hint are numbered in the order of their content, not
    /// of their declarations: writing them in the other order names each one alike.
    #[test]
    fn contexts_sharing_a_hint_are_numbered_by_content() {
        let written = r#"
module BOOL
  syntax Bool ::= Bool "andBool" Bool [function, total, symbol(_andBool_), hook(BOOL.and)]
                | "notBool" Bool [function, total, symbol(notBool_), hook(BOOL.not)]
endmodule
module MAIN
  syntax K
  syntax KResult
  syntax Val ::= "v" [symbol(v)]
  syntax KResult ::= Val
  syntax Exp ::= Val
               | pair(Exp, Exp) [symbol(pair)]
  context [first]: pair(HOLE:Exp, E:Exp)
  context [second]: pair(HOLE:Exp, E:Exp)
  configuration <k> v </k>
endmodule
"#;
        let swapped = written
            .replace("[first]", "[placeholder]")
            .replace("[second]", "[first]")
            .replace("[placeholder]", "[second]");
        let names = |source: &str| ["first", "second"].map(|label| freezer_and_ids(source, label));
        let names_written = names(written);
        assert_eq!(names_written[0].0, "#freezerpair0_", "{names_written:?}");
        assert_eq!(names_written[1].0, "#freezerpair0_2", "{names_written:?}");
        assert_eq!(names(&swapped), names_written);
    }

    /// Cooling matches the term the context rewrites HOLE to and plugs HOLE back in; a term
    /// without HOLE leaves nothing to plug, so the context is rejected where it is written.
    #[test]
    fn a_context_rewriting_hole_away_is_rejected_at_the_context() {
        let run = run_to_stage(
            r#"
module BOOL
endmodule
module MAIN
  syntax K
  syntax KResult ::= Op
  syntax Op ::= "a" [symbol(a)] | "b" [symbol(b)] | wrap(Op) [symbol(wrap)]
  context wrap(HOLE => a)
endmodule
"#,
            "resolve contexts",
        );
        let error = run.error();
        assert_eq!(error.stage, "resolve contexts");
        let [diagnostic] = error.diagnostics.as_slice() else {
            panic!("{error:?}")
        };
        assert_eq!(diagnostic.code, DiagnosticCode::InvalidContext);
        assert!(
            diagnostic
                .message
                .starts_with("The HOLE of a context must be rewritten to a term containing HOLE"),
            "{}",
            diagnostic.message
        );
        let location = diagnostic.location.expect("the diagnostic is located");
        assert_eq!((location.start_line, location.start_column), (8, 3));
    }
}
