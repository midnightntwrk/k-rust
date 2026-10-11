//! ```toml algorithm
//! id = "kompile.contexts.resolve"
//! name = "lowering of evaluation contexts"
//! sites = ["resolve_contexts", "resolve_contexts_pass", "resolve_context"]
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

use crate::provenance::extend_unique_sentences as extend_unique;
use std::{collections::BTreeMap, collections::BTreeSet, fmt, sync::Arc};

use serde_json::Value;

use crate::definition::AttributeKey;
use crate::definition::production_kind::ProductionKind;
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
    let mut generated = Vec::new();
    let mut diagnostics = Vec::new();
    // Invariant: `generated` holds, without duplicates, the sentences resolved from every context of `contexts` before `context`, `labels` every freezer label taken so far, and `diagnostics` their errors; each iteration consumes one context.
    for context in contexts {
        match resolve_context(
            context,
            productions,
            &macro_labels,
            &sentence_labels,
            &mut labels,
        ) {
            Ok(sentences) => extend_unique(&mut generated, sentences),
            Err(mut errors) => diagnostics.append(&mut errors),
        }
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

fn resolve_context(
    context: &Sentence,
    productions: &ProductionCatalog<'_>,
    macro_labels: &BTreeSet<LabelHead>,
    sentence_labels: &BTreeMap<String, Attributes>,
    labels: &mut BTreeSet<Label>,
) -> Result<Vec<Sentence>, Vec<Diagnostic>> {
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
        variables: BTreeMap::new(),
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
    let hint = freezer_hint(&cooled, scan.final_hole_position);
    let freezer_label = unique_freezer_label(labels, &hint);

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
        arguments: variables.into_values().collect(),
    };

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

    let heated_and_frozen = Term::sequence([heated.clone(), frozen]);
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
            requires: requires.clone(),
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
    let origins = sentence_origin_links(context);
    // The freezer, heating, and cooling sentences all derive from this context alone.
    for sentence in &mut generated {
        sentence.attributes_mut().union_input_addresses(attributes);
        seed_generated_sentence_origin(sentence, GeneratingPass::ResolveContexts, origins.clone());
    }
    Ok(generated)
}

struct HeatScan<'a, 'definition> {
    productions: &'a ProductionCatalog<'definition>,
    has_main_cell: bool,
    in_main_cell: bool,
    heated: Option<Term>,
    hole: Option<Term>,
    variables: BTreeMap<String, Term>,
    current_hole_position: usize,
    final_hole_position: usize,
}

impl HeatScan<'_, '_> {
    // Invariant: `self.variables` and `self.current_hole_position` record the non-`HOLE` variables visited so far in preorder where `self.in_main_cell || !self.has_main_cell` holds, and `self.hole` the last `HOLE` found there; each call recurses into the immediate subterms of `term`.
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
                for argument in arguments {
                    self.visit(argument);
                }
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
                        self.variables.insert(name.clone(), term.clone());
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

fn freezer_hint(cooled: &Term, hole_position: usize) -> String {
    let Term::Apply { label, arguments } = cooled.unannotated() else {
        return String::new();
    };
    let is_k_cast = label.generated()
        == Some(GeneratedLabel::SemanticCast {
            sort_text: BuiltinSort::K.k_name(),
        });
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is syntax; only the listed variants are special here"
    )]
    let name = if is_k_cast {
        arguments
            .first()
            .and_then(|argument| match argument.unannotated() {
                Term::Apply { label, .. } => Some(label.name.as_str()),
                _ => None,
            })
            .unwrap_or(&label.name)
    } else {
        &label.name
    };
    format!("{name}{hole_position}")
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
        kompile::stage_harness::{render, run_to_stage, sentence_changes},
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
                    let frozen = body.strip_prefix(&format!("{context}=>HOLE~>"))?;
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
                    format!("HOLE~>{frozen}=>{context}"),
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
