//! ```toml algorithm
//! id = "parser.bubble.rules"
//! name = "parsing and reconstruction of rule bubbles"
//! sites = ["resolve_rule_bubbles", "resolve_rule_bubbles_with_resolved", "parse_rule_content"]
//! variable = "b = rule bubbles; g = grammar construction work; p = parse work"
//! counters = ["KompileRuleBubblesParsed", "ParserGrammarBuilds", "ParserParseAttempts"]
//! consumes = [
//!   { type = "k_rust::definition::Definition", role = "expanded configurations" },
//! ]
//! produces = [{ type = "k_rust::definition::Definition", role = "parsed rule bubbles" }]
//! constrains = [
//!   { id = "definition.catalog.production", site = "resolve_rule_bubbles_with_resolved", via = "the per-module ProductionCatalog that rule_grammar reads from ResolvedDefinition::production_catalog" },
//! ]
//! span = "per call"
//!
//! [[cost]]
//! mode = "one definition"
//! bound = "O(g + sum over b of p)"
//! ```
//!
//! Per-module rule-bubble parsing with K implicit rule syntax.
//!
//! One grammar is built per bubble-bearing module and each bubble is parsed through the Earley
//! pipeline. `Counter::KompileRuleBubblesParsed` counts bubbles; `parse_rule_content` deliberately
//! rebuilds its standalone grammar. Total cost is grammar construction plus bubble parse work.

#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::BTreeSet;
use std::fmt;

use k_rust_kore::measure::{self, Algorithm, Counter};
use web_time::Instant;

use crate::definition::AttributeKey;
use crate::definition::relations::SubsortDeclaration;
use crate::definition::totality::TotalityWitness;
use crate::definition::{
    Attributes, Definition, Location, ModuleId, ProductionItem, ResolveError, ResolvedDefinition,
    Sentence, SortSynonyms,
};
use crate::kast::sort_role::KernelSort;
use crate::kast::{FrontendSort, InternalLabel, Label, Sort, Term, TermParts};
use crate::names::BuiltinSort;
use crate::timings::PhaseTimings;

use super::config::{
    BuiltinTokenGrammar, add_bottom_subsort, add_casts, add_implicit_ml_syntax, add_k_syntax,
    add_kitem_subsort, add_sort_bracket, add_subsort, add_synonym_casts, implicit_kseq_bracket,
    nonterminal, reject_kernel_position_contradiction, truth,
};
use super::location::{locate_ambiguity_places, span_location};
use super::parser::{
    Grammar, ParseError, TokenPrecedenceDeclaration, named_projection_productions,
};
use super::sort_universe::{
    CastTarget, GrammarSort, RULE_BRACKET_SEED_ORDER, RULE_CAST_SEED_ORDER, RULE_GRAMMAR,
    SortUniverse, rule_kernel_seeds, rule_member_productions,
};
#[cfg(not(feature = "z3-inference"))]
use super::sort_universe::{RULE_SCAFFOLD_SEED_ORDER, ScaffoldPosition};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RuleError {
    Definition(ResolveError),
    MissingModule {
        module: String,
    },
    Parse(Box<RuleParseError>),
    InconsistentTokenPrecedence {
        token: String,
        declarations: Vec<TokenPrecedenceDeclaration>,
    },
    IllegalEnsures {
        module: String,
        sentence_type: String,
        source: Option<String>,
        location: Option<Location>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuleParseError {
    pub module: String,
    pub sentence_type: String,
    pub source: Option<String>,
    pub location: Option<Location>,
    pub error: ParseError,
}

impl fmt::Display for RuleError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Definition(error) => error.fmt(formatter),
            Self::MissingModule { module } => {
                write!(formatter, "rule syntax module {module:?} was not found")
            }
            Self::Parse(error) => {
                match (&error.source, error.location) {
                    (Some(source), Some(location)) => write!(
                        formatter,
                        "{source}:{}:{}: ",
                        location.start_line, location.start_column
                    )?,
                    (Some(source), None) => write!(formatter, "{source}: ")?,
                    _ => {}
                }
                write!(
                    formatter,
                    "could not parse {} in module {:?}: {}",
                    error.sentence_type, error.module, error.error
                )
            }
            Self::InconsistentTokenPrecedence {
                token,
                declarations,
            } => ParseError::InconsistentTokenPrecedence {
                token: token.clone(),
                declarations: declarations.clone(),
            }
            .fmt(formatter),
            Self::IllegalEnsures {
                module,
                sentence_type,
                ..
            } => write!(
                formatter,
                "{sentence_type} in module {module:?} cannot contain an ensures clause"
            ),
        }
    }
}

impl std::error::Error for RuleError {}

/// Parse one complete rule-content string with a resolved module's rule grammar.
///
/// The returned rule retains the caller-supplied attributes, including source and
/// content offsets used by parser metadata and diagnostics.
pub fn parse_rule_content(
    definition: &ResolvedDefinition,
    module: &str,
    contents: &str,
    attributes: Attributes,
) -> Result<Sentence, RuleError> {
    let module_id = definition
        .module_id(module)
        .ok_or_else(|| RuleError::MissingModule {
            module: module.to_owned(),
        })?;
    let grammar = module_rule_grammar(definition, module_id, "rule", &attributes)?;
    parse_rule_like_sentence(&grammar, module, "rule", contents, attributes)
}

/// Replace local rule, claim, context, and context-alias bubbles with KAST sentences.
///
/// This is the syntax-only first slice of non-configuration bubble resolution.
/// Priority and associativity filter the concrete parse forest;
/// inputs that remain genuinely ambiguous are reported explicitly.
pub fn resolve_rule_bubbles(definition: &Definition) -> Result<Definition, RuleError> {
    let resolved = ResolvedDefinition::resolve(definition).map_err(RuleError::Definition)?;
    resolve_rule_bubbles_with_resolved(definition, &resolved, None)
        .map(|(transformed, _)| transformed)
}

/// Resolve rule bubbles using a graph already built for the same module structure.
pub(crate) fn resolve_rule_bubbles_with_resolved(
    definition: &Definition,
    resolved: &ResolvedDefinition,
    timings: Option<&mut PhaseTimings>,
) -> Result<(Definition, ResolvedDefinition), RuleError> {
    let _span = measure::algorithm_span(Algorithm::ParserBubbleRules);
    let mut grammar_seconds = 0.0;
    let mut parse_seconds = 0.0;
    let mut transformed = definition.clone();
    let main = resolved.main_module_id();

    for module in &mut transformed.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("every flat module was added to the resolved definition");
        // The main module's grammar is the syntax of the compiled definition, so it is built
        // and checked (token precedences, priorities, subsorts) even when the main module
        // has no bubble of its own; another module's grammar exists only to parse its bubbles.
        if module_id != main
            && !module
                .local_sentences
                .iter()
                .any(|sentence| is_rule_bubble(sentence))
        {
            continue;
        }
        let grammar_started = timings.as_ref().map(|_| Instant::now());
        let grammar = module_rule_grammar(
            resolved,
            module_id,
            "rule-like sentence",
            &module.attributes,
        );
        if let Some(started) = grammar_started {
            grammar_seconds += started.elapsed().as_secs_f64();
        }
        let grammar = grammar?;

        for sentence in &mut module.local_sentences {
            let Sentence::Bubble {
                sentence_type,
                contents,
                attributes,
            } = &**sentence
            else {
                continue;
            };
            if !is_rule_sentence_type(sentence_type) {
                continue;
            }
            measure::bump(Counter::KompileRuleBubblesParsed);
            let parse_started = timings.as_ref().map(|_| Instant::now());
            let parsed = parse_rule_like_sentence(
                &grammar,
                &module.name,
                sentence_type,
                contents,
                attributes.clone(),
            );
            if let Some(started) = parse_started {
                parse_seconds += started.elapsed().as_secs_f64();
            }
            *crate::definition::sentence_mut(sentence) = parsed?;
        }
    }

    if let Some(timings) = timings {
        timings.phases.push(crate::timings::PhaseTiming {
            name: crate::kompile::pipeline::load_phase::RESOLVE_RULE_BUBBLES_GRAMMARS,
            seconds: grammar_seconds,
            depth: 1,
        });
        timings.phases.push(crate::timings::PhaseTiming {
            name: crate::kompile::pipeline::load_phase::RESOLVE_RULE_BUBBLES_PARSE,
            seconds: parse_seconds,
            depth: 1,
        });
    }

    let resolved = resolved
        .update(definition, &transformed)
        .map_err(RuleError::Definition)?;
    Ok((transformed, resolved))
}

/// The grammar that parses the rule-like sentences of `module`.
///
/// A sentence denotes in the syntax its own module sees, so the grammar, its scanner included,
/// is built from that module's view alone. A terminal or token declared only in a module that
/// `module` does not import is no lexeme of this grammar: lexing it would split or swallow the
/// characters that spell `module`'s own tokens, so the meaning of a module's rules would depend
/// on which definition imports it.
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "ParseError is not a sentence kind; only the listed variants are special here"
)]
fn module_rule_grammar(
    definition: &ResolvedDefinition,
    module: ModuleId,
    sentence_type: &str,
    attributes: &Attributes,
) -> Result<Grammar, RuleError> {
    rule_grammar(definition, module).map_err(|error| match error {
        ParseError::InconsistentTokenPrecedence {
            token,
            declarations,
        } => RuleError::InconsistentTokenPrecedence {
            token,
            declarations,
        },
        error => RuleError::Parse(Box::new(RuleParseError {
            module: definition.module(module).name.clone(),
            sentence_type: sentence_type.to_owned(),
            source: attributes.source().map(str::to_owned),
            location: attributes.location(),
            error,
        })),
    })
}

fn parse_rule_like_sentence(
    grammar: &Grammar,
    module: &str,
    sentence_type: &str,
    contents: &str,
    attributes: Attributes,
) -> Result<Sentence, RuleError> {
    let is_anywhere = attributes.has_any(&[
        AttributeKey::Anywhere,
        AttributeKey::Simplification,
        AttributeKey::Macro,
        AttributeKey::MacroRec,
        AttributeKey::Alias,
        AttributeKey::AliasRec,
    ]);
    let parsed = if let Some(source) = attributes.source_id() {
        grammar.parse_with_context(
            &Sort::new("#RuleContent"),
            contents,
            is_anywhere,
            source,
            content_start_offset(&attributes),
        )
    } else {
        grammar.parse_with_context_without_provenance(
            &Sort::new("#RuleContent"),
            contents,
            is_anywhere,
        )
    }
    .map_err(|error| bubble_error(module, sentence_type, &attributes, Some(contents), error))?;
    up_sentence(module, sentence_type, parsed, attributes)
}

fn content_start_offset(attributes: &Attributes) -> usize {
    attributes
        .value(AttributeKey::ContentStartOffset)
        .and_then(serde_json::Value::as_u64)
        .and_then(|offset| usize::try_from(offset).ok())
        .unwrap_or(0)
}

fn is_rule_bubble(sentence: &Sentence) -> bool {
    matches!(
        sentence,
        Sentence::Bubble { sentence_type, .. } if is_rule_sentence_type(sentence_type)
    )
}

fn is_rule_sentence_type(sentence_type: &str) -> bool {
    matches!(sentence_type, "rule" | "claim" | "context" | "alias")
}

fn bubble_error(
    module: &str,
    sentence_type: &str,
    attributes: &Attributes,
    contents: Option<&str>,
    mut error: ParseError,
) -> RuleError {
    if let Some(contents) = contents {
        locate_ambiguity_places(&mut error, attributes, contents);
    }
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "ParseError is not a sentence kind; only the listed variants are special here"
    )]
    let span = match &error {
        ParseError::NoParse {
            span: Some(span), ..
        }
        | ParseError::Ambiguous {
            span: Some(span), ..
        }
        | ParseError::ProjectionCastWithoutProjection {
            span: Some(span), ..
        } => Some(*span),
        ParseError::CyclicDerivation(cycle) => cycle.span,
        _ => None,
    };
    let location = span
        .zip(contents)
        .and_then(|(span, contents)| span_location(attributes, contents, span))
        .or_else(|| attributes.location());
    RuleError::Parse(Box::new(RuleParseError {
        module: module.to_owned(),
        sentence_type: sentence_type.to_owned(),
        source: attributes.source().map(str::to_owned),
        location,
        error,
    }))
}

/// Clear every label's sort parameters in a term the inner parser produced for a rule-like
/// sentence or a configuration.
///
/// K source text cannot write a label parameter: a KLabel is a token, and a cast is the only
/// sort annotation. A parameter on a parsed label is therefore the parser's own choice of
/// instance, either derivable from the arguments and the position or, for an unconstrained
/// parameter, arbitrary. Sort injection solves every parametric label from its arguments and
/// position, so the loaded sentence carries no parameter: a loaded rule-like term has a
/// parameter only where a later compiler pass generates one.
///
/// Readings that differ only in their instance stay distinct during disambiguation; the
/// parameters are dropped only here, after one reading has been chosen.
pub(super) fn erase_label_parameters(term: Term) -> Term {
    crate::stack::guarded(|| match term.into_parts() {
        TermParts::Annotated { term, metadata } => Term::Annotated {
            term: Box::new(erase_label_parameters(*term)),
            metadata,
        },
        TermParts::Apply {
            mut label,
            arguments,
        } => {
            label.parameters.clear();
            Term::Apply {
                label,
                arguments: arguments.into_iter().map(erase_label_parameters).collect(),
            }
        }
        TermParts::InjectedLabel(mut label) => {
            label.parameters.clear();
            Term::InjectedLabel(label)
        }
        TermParts::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(erase_label_parameters(*left)),
            right: Box::new(erase_label_parameters(*right)),
        },
        TermParts::As { pattern, alias } => Term::As {
            pattern: Box::new(erase_label_parameters(*pattern)),
            alias: Box::new(erase_label_parameters(*alias)),
        },
        TermParts::Sequence(items) => {
            Term::Sequence(items.into_iter().map(erase_label_parameters).collect())
        }
        term @ (TermParts::Variable { .. } | TermParts::Token { .. }) => Term::from(term),
    })
}

fn up_sentence(
    module: &str,
    sentence_type: &str,
    parsed: Term,
    attributes: Attributes,
) -> Result<Sentence, RuleError> {
    let TermParts::Apply { label, arguments } = erase_label_parameters(parsed)
        .into_unannotated()
        .into_parts()
    else {
        return Err(bubble_error(
            module,
            sentence_type,
            &attributes,
            None,
            ParseError::InvalidParseShape {
                expected: "#RuleContent".into(),
            },
        ));
    };
    let (body, requires, ensures) = match (InternalLabel::of(&label.name), arguments.as_slice()) {
        (Some(InternalLabel::RuleNoConditions), [body]) => (body.clone(), truth(), truth()),
        (Some(InternalLabel::RuleRequires), [body, requires]) => {
            (body.clone(), requires.clone(), truth())
        }
        (Some(InternalLabel::RuleEnsures), [body, ensures]) => {
            (body.clone(), truth(), ensures.clone())
        }
        (Some(InternalLabel::RuleRequiresEnsures), [body, requires, ensures]) => {
            (body.clone(), requires.clone(), ensures.clone())
        }
        _ => {
            return Err(bubble_error(
                module,
                sentence_type,
                &attributes,
                None,
                ParseError::InvalidParseShape {
                    expected: "rule content".into(),
                },
            ));
        }
    };

    match sentence_type {
        "rule" => Ok(Sentence::Rule {
            body,
            requires,
            ensures,
            attributes,
        }),
        "claim" => Ok(Sentence::Claim {
            body,
            requires,
            ensures,
            attributes,
        }),
        "context" | "alias" => {
            if label.is(InternalLabel::RuleEnsures) || label.is(InternalLabel::RuleRequiresEnsures)
            {
                return Err(RuleError::IllegalEnsures {
                    module: module.to_owned(),
                    sentence_type: sentence_type.to_owned(),
                    source: attributes.source().map(str::to_owned),
                    location: attributes.location(),
                });
            }
            if sentence_type == "context" {
                Ok(Sentence::Context {
                    body,
                    requires,
                    attributes,
                })
            } else {
                Ok(Sentence::ContextAlias {
                    body,
                    requires,
                    attributes,
                })
            }
        }
        _ => unreachable!("callers filter sentence types"),
    }
}

/// The sentences the rule grammar of `module` is built from: the module's signature plus
/// ML-SYNTAX, plus, when the signature holds a configuration's cells, the RULE-CELLS cell
/// productions that no visible cell production already provides.
#[cfg(test)]
fn rule_grammar_view(resolved: &ResolvedDefinition, module: ModuleId) -> Vec<&Sentence> {
    rule_grammar_view_and_signature(resolved, module).0
}

/// [`rule_grammar_view`] and the number of its leading sentences that are the module's
/// signature, the syntax a program of the module writes.
fn rule_grammar_view_and_signature(
    resolved: &ResolvedDefinition,
    module: ModuleId,
) -> (Vec<&Sentence>, usize) {
    let mut visible = resolved.signature_sentences(module);
    let signature = visible.len();
    add_implicit_ml_syntax(resolved, &mut visible);
    inject_rule_cell_sentences(resolved, &mut visible);
    (visible, signature)
}

/// Sentences added to the rule view independently of the module's imports.
/// Configuration grammars use the same ML-SYNTAX augmentation as the rule view.
pub(crate) fn grammar_injected_sentences(
    resolved: &ResolvedDefinition,
    module: ModuleId,
) -> Vec<&Sentence> {
    let mut signature = resolved.signature_sentences(module);
    let signature_end = signature.len();
    add_implicit_ml_syntax(resolved, &mut signature);
    inject_rule_cell_sentences(resolved, &mut signature);
    signature.split_off(signature_end)
}

fn inject_rule_cell_sentences<'a>(
    resolved: &'a ResolvedDefinition,
    visible: &mut Vec<&'a Sentence>,
) {
    // RULE-CELLS supplies parse-only cells, notably generatedCounter for claims
    // about fresh constants. The compiler generates their real productions later, as cells of
    // the compiled configuration, beside the cells the definition's configurations declare. A
    // view has them exactly when it has a cell of the configuration (a `cell` production): a module
    // that sees no configuration names no cell of it, the added ones included, and the content
    // sorts of the added cells come with the configuration, not into every module.
    // Import only these declarations into the grammar, preserving the source module.
    let sees_configuration = visible.iter().any(|sentence| {
        matches!(sentence, Sentence::Production { attributes, .. } if attributes.has(AttributeKey::Cell))
    });
    if !sees_configuration {
        return;
    }
    if let Some(rule_cells) = resolved.module_id("RULE-CELLS") {
        for sentence in resolved
            .module(rule_cells)
            .local_sentences
            .iter()
            .map(std::sync::Arc::as_ref)
        {
            let Sentence::Production {
                label,
                sort,
                attributes,
                ..
            } = sentence
            else {
                continue;
            };
            if !attributes.has(AttributeKey::Cell) {
                continue;
            }
            if !visible.iter().any(|existing| matches!(existing,
                Sentence::Production { label: existing_label, sort: existing_sort, attributes, .. }
                if existing_label == label && existing_sort == sort && attributes.has(AttributeKey::Cell)
            )) {
                visible.push(sentence);
            }
        }
    }
}

fn rule_grammar(resolved: &ResolvedDefinition, module: ModuleId) -> Result<Grammar, ParseError> {
    let (visible, signature) = rule_grammar_view_and_signature(resolved, module);
    reject_kernel_position_contradiction(&visible)?;
    // Start sorts and #token sort strings denote in the module's full view. SortUniverse
    // still restricts generated casts to aliases declared in this grammar's own view.
    let synonyms = if resolved.declares_sort_synonyms() {
        SortSynonyms::of_module(resolved, module)
    } else {
        SortSynonyms::default()
    };
    // Built after the RULE-CELLS injection, so the injected cells' body sorts are members.
    let universe = SortUniverse::new(&visible, &synonyms);
    let has_generated_top_sort = visible.iter().any(|sentence| {
        matches!(
            SubsortDeclaration::of(sentence),
            Some(SubsortDeclaration::KernelTop)
        )
    });
    let has_generated_bottom_sort = visible.iter().any(|sentence| {
        matches!(
            SubsortDeclaration::of(sentence),
            Some(SubsortDeclaration::KernelBottom)
        )
    });
    let explicit_top_sorts = visible
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: None,
                parameters,
                sort,
                items,
                ..
            } if parameters.is_empty() && sort.name == BuiltinSort::KItem.k_name() => {
                match items.as_slice() {
                    [ProductionItem::NonTerminal { sort: child, .. }] => Some(child.clone()),
                    _ => None,
                }
            }
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
    let is_cell = |sentence: &&Sentence| {
        matches!(
            sentence,
            Sentence::Production { attributes, .. } if attributes.has(AttributeKey::Cell)
        )
    };
    let mut parsing_sentences = visible
        .iter()
        .filter(|sentence| !is_cell(sentence))
        .map(|sentence| (*sentence).clone())
        .collect::<Vec<_>>();
    // The parsing sentences keep the view's order, so the signature's come first; everything
    // after them is syntax the rule grammar adds to the module's.
    let program_syntax = visible[..signature]
        .iter()
        .filter(|sentence| !is_cell(sentence))
        .count();
    let has_production_labeled = |name: &str| {
        visible.iter().any(|sentence| {
            matches!(sentence, Sentence::Production { label: Some(label), .. } if label.name == name)
        })
    };
    parsing_sentences.extend(
        universe
            .members()
            .filter(|member| rule_member_productions(member.role()).predicate)
            .filter(|member| !has_production_labeled(&Label::sort_predicate(member.sort()).name))
            .map(|member| sort_predicate_production(&member)),
    );
    parsing_sentences.extend(
        universe
            .members()
            .filter(|member| rule_member_productions(member.role()).projection)
            .filter_map(|member| Label::projection(member.sort()).map(|label| (member, label)))
            .filter(|(_, label)| !has_production_labeled(&label.name))
            .map(|(member, label)| sort_projection_production(&member, label)),
    );
    parsing_sentences.extend(named_projection_productions(visible.iter().copied()));
    if !parsing_sentences
        .iter()
        .any(|sentence| matches!(sentence, Sentence::SyntaxSort { sort, .. } if sort.name == FrontendSort::Bag.as_str()))
    {
        parsing_sentences.push(Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: Sort::new("Bag"),
            attributes: Attributes::default(),
        });
    }
    #[cfg(feature = "z3-inference")]
    add_rewrite_rule_sentences(&mut parsing_sentences);
    add_k_rule_sentences(&mut parsing_sentences);
    let source_catalog = resolved.production_catalog(module);
    // The reference rule grammar imports DEFAULT-LAYOUT explicitly, independently
    // of the layout used to parse programs in the language being compiled.
    let mut grammar = Grammar::from_rule_sentences(
        parsing_sentences.iter(),
        program_syntax,
        &source_catalog,
        synonyms.denotations().clone(),
    )?;
    // Multiplicity-cell collection concatenations have no separator, so retaining every
    // binary association expands a short sequence into a Catalan-sized parse forest. Their
    // generated productions are explicitly associative; choosing one association here is
    // therefore lossless and keeps the rule grammar bounded without affecting user syntax.
    for sentence in &parsing_sentences {
        let Sentence::Production {
            label: Some(label),
            attributes,
            ..
        } = sentence
        else {
            continue;
        };
        if attributes.has(AttributeKey::CellCollection) && attributes.has(AttributeKey::Assoc) {
            grammar.add_left_associative(label.name.clone());
        }
    }
    let bracket_sorts = visible
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                sort, attributes, ..
            } if attributes.has(AttributeKey::Bracket) => Some(sort.clone()),
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
    let klabel_terminals = visible
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label),
                items,
                ..
            } if items.iter().any(
                |item| matches!(item, ProductionItem::Terminal(value) if value == &label.name),
            ) =>
            {
                Some(label.name.clone())
            }
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
    add_k_syntax(&mut grammar, BuiltinTokenGrammar::Rule)?;
    // `~>` (KSEQ) belongs to the rule grammar of every definition without a module declaring it;
    // its bracket keeps the priority contract of the brackets the seed adds.
    let default_bracket = implicit_kseq_bracket(resolved);
    add_rule_k_syntax(
        &mut grammar,
        &universe,
        &bracket_sorts,
        &klabel_terminals,
        default_bracket,
    )?;
    add_rule_cells(&mut grammar, &visible, &universe)?;
    #[cfg(not(feature = "z3-inference"))]
    for kernel in RULE_SCAFFOLD_SEED_ORDER {
        if rule_kernel_seeds(kernel).rule_scaffold == Some(ScaffoldPosition::AfterRuleCells) {
            add_rule_sort(&mut grammar, GrammarSort::kernel(kernel).sort())?;
        }
    }
    // The sorts that have a `#Rule` scaffolding sort; every argument position of one of them
    // admits a rewrite or `#as` pattern of that sort.
    #[cfg(not(feature = "z3-inference"))]
    let mut rule_sorts = RULE_SCAFFOLD_SEED_ORDER
        .into_iter()
        .filter(|kernel| rule_kernel_seeds(*kernel).rule_scaffold.is_some())
        .map(|kernel| {
            let sort = kernel.sort();
            let rule = rule_sort(&sort);
            (sort, rule)
        })
        .collect::<std::collections::BTreeMap<_, _>>();

    for member in universe.members() {
        let productions = rule_member_productions(member.role());
        #[cfg(not(feature = "z3-inference"))]
        if productions.rule_scaffold {
            add_rule_sort(&mut grammar, member.sort())?;
            rule_sorts.insert(member.sort().clone(), rule_sort(member.sort()));
        }
        if productions.kitem_subsort
            && !has_generated_top_sort
            && !explicit_top_sorts.contains(member.sort())
        {
            add_kitem_subsort(&mut grammar, &member)?;
        }
        if productions.bottom_subsort && !has_generated_bottom_sort {
            add_bottom_subsort(&mut grammar, &member, FrontendSort::KBott.as_str())?;
        }
        if productions.casts {
            add_casts(&mut grammar, &CastTarget::member(&member))?;
        }
    }
    add_synonym_casts(&mut grammar, &universe, &RULE_GRAMMAR)?;
    #[cfg(not(feature = "z3-inference"))]
    {
        let scaffolding = rule_sorts
            .iter()
            .flat_map(|(sort, rule)| [rule.clone(), rewrite_side_sort(sort)])
            .collect::<BTreeSet<_>>();
        grammar.admit_rewrites_in_argument_positions(&rule_sorts, &scaffolding);
    }

    // The generated productions are complete; check their sorts against their roles and the
    // acyclicity of the semantic subsort relation (G0-G3).
    #[cfg(debug_assertions)]
    grammar.assert_generated_sort_roles(&universe);
    grammar.read_token_text_as_program_text();
    Ok(grammar)
}

fn sort_predicate_production(sort: &GrammarSort) -> Sentence {
    let label = Label::sort_predicate(sort.sort());
    let mut attributes = Attributes::default();
    attributes.mark(AttributeKey::Function);
    attributes.declare_total(TotalityWitness::covering_predicate());
    attributes.mark(AttributeKey::GeneratedRuleSyntax);
    Sentence::Production {
        label: Some(label.clone()),
        parameters: Vec::new(),
        sort: Sort::new("Bool"),
        items: vec![
            ProductionItem::Terminal(label.name),
            ProductionItem::Terminal("(".into()),
            ProductionItem::NonTerminal {
                sort: Sort::new("K"),
                name: None,
            },
            ProductionItem::Terminal(")".into()),
        ],
        attributes,
    }
}

fn sort_projection_production(sort: &GrammarSort, label: Label) -> Sentence {
    let mut attributes = Attributes::default();
    attributes.mark(AttributeKey::Function);
    attributes.mark(AttributeKey::Projection);
    attributes.mark(AttributeKey::GeneratedRuleSyntax);
    Sentence::Production {
        label: Some(label.clone()),
        parameters: Vec::new(),
        sort: sort.sort().clone(),
        items: vec![
            ProductionItem::Terminal(label.name),
            ProductionItem::Terminal("(".into()),
            ProductionItem::NonTerminal {
                sort: Sort::new("K"),
                name: None,
            },
            ProductionItem::Terminal(")".into()),
        ],
        attributes,
    }
}

fn add_rule_k_syntax(
    grammar: &mut Grammar,
    universe: &SortUniverse,
    bracket_sorts: &BTreeSet<Sort>,
    klabel_terminals: &BTreeSet<String>,
    default_bracket: Option<&Attributes>,
) -> Result<(), ParseError> {
    add_subsort(grammar, "KBott", "#KVariable")?;
    add_subsort(grammar, "KBott", "KConfigVar")?;
    add_subsort(grammar, "KItem", "KBott")?;
    // Literal terminals always beat regex lexemes in the global scanner. Retain this generated
    // bridge so labels whose spelling is also a terminal remain usable in prefix applications
    // and explicit `#klabel(...)` terms.
    for label in klabel_terminals {
        grammar.add(
            Sort::new("KLabel"),
            vec![ProductionItem::Terminal(label.clone())],
            None,
            true,
            false,
        )?;
    }
    grammar.add(
        Sort::new("KList"),
        vec![nonterminal("K")],
        None,
        false,
        true,
    )?;
    grammar.add(
        Sort::new("KList"),
        vec![ProductionItem::Terminal(".KList".into())],
        Some(Label::new("#EmptyKList")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("KList"),
        vec![
            nonterminal("KList"),
            ProductionItem::Terminal(",".into()),
            nonterminal("KList"),
        ],
        Some(Label::new("#KList")),
        false,
        false,
    )?;
    grammar.add_left_associative("#KList");
    grammar.add(
        Sort::new("KBott"),
        vec![
            ProductionItem::Terminal("#token".into()),
            ProductionItem::Terminal("(".into()),
            nonterminal("KString"),
            ProductionItem::Terminal(",".into()),
            nonterminal("KString"),
            ProductionItem::Terminal(")".into()),
        ],
        Some(Label::new("#KToken")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("KBott"),
        vec![
            ProductionItem::Terminal("#klabel".into()),
            ProductionItem::Terminal("(".into()),
            nonterminal("KLabel"),
            ProductionItem::Terminal(")".into()),
        ],
        Some(Label::new("#WrappedKLabel")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("KBott"),
        vec![
            nonterminal("KLabel"),
            ProductionItem::Terminal("(".into()),
            nonterminal("KList"),
            ProductionItem::Terminal(")".into()),
        ],
        Some(Label::new("#KApply")),
        false,
        false,
    )?;
    for kernel in RULE_BRACKET_SEED_ORDER {
        if rule_kernel_seeds(kernel).bracket {
            add_sort_bracket(grammar, &GrammarSort::kernel(kernel), default_bracket)?;
        }
    }
    for kernel in RULE_CAST_SEED_ORDER {
        if rule_kernel_seeds(kernel).casts {
            add_casts(grammar, &CastTarget::kernel(kernel))?;
        }
    }
    #[cfg(not(feature = "z3-inference"))]
    for kernel in RULE_SCAFFOLD_SEED_ORDER {
        if rule_kernel_seeds(kernel).rule_scaffold == Some(ScaffoldPosition::BeforeRuleBody) {
            add_rule_sort(grammar, GrammarSort::kernel(kernel).sort())?;
        }
    }
    let rule_body_sort = rule_sort(&KernelSort::K.sort());
    // The fixed kernel syntax derives `#RuleBody` from `K` (`add_k_syntax`); the portable
    // build's rule body is its `K` scaffolding, which needs a production of its own.
    #[cfg(not(feature = "z3-inference"))]
    grammar.add(
        Sort::new("#RuleBody"),
        vec![ProductionItem::NonTerminal {
            sort: rule_body_sort.clone(),
            name: None,
        }],
        None,
        false,
        true,
    )?;
    for member in universe.members() {
        if rule_member_productions(member.role()).bracket && !bracket_sorts.contains(member.sort())
        {
            add_sort_bracket(grammar, &member, default_bracket)?;
        }
    }
    grammar.add(
        Sort::new("#RuleBody"),
        vec![
            // Keep the delimiters as four scanner tokens. A `]]` token would shadow two adjacent
            // lookup closers in inputs such as `{M[PATH[0]]}:>MerkleTree`.
            ProductionItem::Terminal("[".into()),
            ProductionItem::Terminal("[".into()),
            ProductionItem::NonTerminal {
                sort: rule_body_sort,
                name: None,
            },
            ProductionItem::Terminal("]".into()),
            ProductionItem::Terminal("]".into()),
            nonterminal("Bag"),
        ],
        Some(Label::new("#withConfig")),
        false,
        false,
    )
}

#[cfg(not(feature = "z3-inference"))]
fn add_rule_sort(grammar: &mut Grammar, sort: &Sort) -> Result<(), ParseError> {
    // A pattern of sort `S` in a rule is a term of sort `S`, an `#as` pattern `P #as V`, or a
    // rewrite `L => R` whose sides are each a term or an `#as` pattern of sort `S`:
    //   #Rule:S        ::= S | S "#as" S | S "=>" S   (operands of `=>` recognized as the side)
    //   #RewriteSide:S ::= S | S "#as" S
    // `P #as V` is the conjunction of `P` and `V` at one position: it matches the terms that
    // match both and binds `V` to the matched term. Both conjuncts occupy that position, so the
    // alias is an operand of `sort` like the pattern: a bare variable there is bounded by `sort`,
    // and a sort-annotated variable (`V:Int`) can stand there. An `#as` pattern is a pattern of
    // sort `S` like any other, so it can also stand where a rewrite side stands.
    // The operands of `=>` stay declared `S`, so inference bounds a plain side by `S` and an
    // `#as` side by its own operands. A rewrite is not a side, so `A => B => C` and a rewrite as
    // an operand of `#as` need parentheses, where the scope rules apply. `#Rule:S` and
    // `#RewriteSide:S` each derive an `#as` directly, so an `#as` has one derivation wherever
    // it stands: at a `#Rule:S` position outside a rewrite, or as a side inside one.
    let result = rule_sort(sort);
    let side = rewrite_side_sort(sort);
    let child = ProductionItem::NonTerminal {
        sort: sort.clone(),
        name: None,
    };
    let alias = vec![
        child.clone(),
        ProductionItem::Terminal("#as".into()),
        child.clone(),
    ];
    for scaffolding in [&side, &result] {
        grammar.add(scaffolding.clone(), vec![child.clone()], None, false, true)?;
        grammar.add(
            scaffolding.clone(),
            alias.clone(),
            Some(Label::new("#KAs")),
            false,
            false,
        )?;
    }
    grammar.add_with_recognized_operands(
        result,
        vec![child.clone(), ProductionItem::Terminal("=>".into()), child],
        Some(Label::new("#KRewrite")),
        sort,
        &side,
    )
}

// The scaffolding sorts of a sort `S` are named `#Rule:S` and `#RewriteSide:S`. A sort name,
// a user's or the frontend's, has no `:`, so neither family names a sort of the grammar, and the
// two prefixes differ, so they do not name each other's sorts either. Without the separator,
// `#Rule` followed by a user sort `Body` or `Content` would be the frontend's `#RuleBody` or
// `#RuleContent`, and every rule body would also read as a rewrite at that user sort.
#[cfg(not(feature = "z3-inference"))]
fn rule_sort(sort: &Sort) -> Sort {
    Sort::new(format!("#Rule:{}", sort.name))
}

#[cfg(not(feature = "z3-inference"))]
fn rewrite_side_sort(sort: &Sort) -> Sort {
    Sort::new(format!("#RewriteSide:{}", sort.name))
}

#[cfg(feature = "z3-inference")]
fn rule_sort(sort: &Sort) -> Sort {
    sort.clone()
}

/// Labels of the productions among `sentences`; a builtin rule production is added only when
/// no visible production already carries its label.
fn production_labels(sentences: &[Sentence]) -> BTreeSet<String> {
    sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label), ..
            } => Some(label.name.clone()),
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
        .collect()
}

fn generated_rule_attributes() -> Attributes {
    let mut attributes = Attributes::default();
    attributes.set(AttributeKey::GeneratedRuleSyntax, serde_json::Value::Null);
    attributes
}

/// The parametric rewrite and `#as` productions of the rule grammar (`kast.md`, modules
/// `KREWRITE` and `K`). The portable rule grammar derives rewrites and `#as` patterns from the
/// `#Rule` scaffolding sorts instead (`add_rule_sort`), so these are the Z3 build's alone.
#[cfg(feature = "z3-inference")]
fn add_rewrite_rule_sentences(sentences: &mut Vec<Sentence>) {
    let labels = production_labels(sentences);
    let parameter = Sort::new("Sort");
    let generated_attributes = generated_rule_attributes();
    let binary = |label: &str, operator: &str| Sentence::Production {
        label: Some(Label::with_parameters(label, vec![parameter.clone()])),
        parameters: vec![parameter.clone()],
        sort: parameter.clone(),
        items: vec![
            ProductionItem::NonTerminal {
                sort: parameter.clone(),
                name: None,
            },
            ProductionItem::Terminal(operator.into()),
            ProductionItem::NonTerminal {
                sort: parameter.clone(),
                name: None,
            },
        ],
        attributes: generated_attributes.clone(),
    };
    if !labels.contains(InternalLabel::KRewrite.as_str()) {
        sentences.push(binary("#KRewrite", "=>"));
    }
    if !labels.contains(InternalLabel::KAs.as_str()) {
        sentences.push(binary("#KAs", "#as"));
    }
    if !sentences.iter().any(|sentence| {
        matches!(sentence, Sentence::SyntaxAssociativity { tags, .. } if tags.iter().any(|tag| tag == InternalLabel::KRewrite.as_str()))
    }) {
        sentences.push(Sentence::SyntaxAssociativity {
            associativity: crate::definition::Associativity::NonAssoc,
            tags: vec!["#KRewrite".into()],
            attributes: Attributes::default(),
        });
    }
}

/// The rule-only term syntax of module `K` (`kast.md`) other than rewrites and `#as`: the local
/// functions `#fun2`, `#fun3` and `#let`, and the pattern tests `:=K` and `:/=K`.
///
/// Every rule grammar has them, whatever the inference engine: they are terms of the rule
/// language, not a way of writing rewrites, so the portable scaffolding does not replace them.
/// `#fun3` and `#let` are parametric in a result sort `Sort1` and an argument sort `Sort2` that
/// occurs only in argument positions (the bound pattern and the bound value). Such a parameter
/// only bounds those subterms from above, and `K` bounds every sort, so it never removes a
/// typing: the maximal variable typing of a rule is the one at `Sort2 = K`, and the loaded term
/// carries no label parameter (`erase_label_parameters`). The value either engine gives the
/// parameter is therefore not observable in the rule it loads.
fn add_k_rule_sentences(sentences: &mut Vec<Sentence>) {
    let labels = production_labels(sentences);
    let has_label = |name: &str| labels.contains(name);
    let parameter = Sort::new("Sort");
    let generated_attributes = generated_rule_attributes();
    if !has_label(InternalLabel::Fun2.as_str()) {
        let mut attributes = generated_attributes.clone();
        attributes.mark(AttributeKey::Prefer);
        sentences.push(Sentence::Production {
            label: Some(Label::with_parameters("#fun2", vec![parameter.clone()])),
            parameters: vec![parameter.clone()],
            sort: parameter.clone(),
            items: vec![
                ProductionItem::Terminal("#fun".into()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: parameter.clone(),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: parameter.clone(),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
            ],
            attributes,
        });
    }
    let result_parameter = Sort::new("Sort1");
    let argument_parameter = Sort::new("Sort2");
    if !has_label(InternalLabel::Fun3.as_str()) {
        sentences.push(Sentence::Production {
            label: Some(Label::with_parameters(
                "#fun3",
                vec![result_parameter.clone(), argument_parameter.clone()],
            )),
            parameters: vec![result_parameter.clone(), argument_parameter.clone()],
            sort: result_parameter.clone(),
            items: vec![
                ProductionItem::Terminal("#fun".into()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: argument_parameter.clone(),
                    name: None,
                },
                ProductionItem::Terminal("=>".into()),
                ProductionItem::NonTerminal {
                    sort: result_parameter.clone(),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: argument_parameter.clone(),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
            ],
            attributes: generated_attributes.clone(),
        });
    }
    if !has_label(InternalLabel::Let.as_str()) {
        sentences.push(Sentence::Production {
            label: Some(Label::with_parameters(
                "#let",
                vec![result_parameter.clone(), argument_parameter.clone()],
            )),
            parameters: vec![result_parameter.clone(), argument_parameter.clone()],
            sort: result_parameter,
            items: vec![
                ProductionItem::Terminal("#let".into()),
                ProductionItem::NonTerminal {
                    sort: argument_parameter.clone(),
                    name: None,
                },
                ProductionItem::Terminal("=".into()),
                ProductionItem::NonTerminal {
                    sort: argument_parameter,
                    name: None,
                },
                ProductionItem::Terminal("#in".into()),
                ProductionItem::NonTerminal {
                    sort: Sort::new("Sort1"),
                    name: None,
                },
            ],
            attributes: generated_attributes.clone(),
        });
    }
    for (label, terminal) in [
        (InternalLabel::KEqualsK, ":=K"),
        (InternalLabel::KNotEqualsK, ":/=K"),
    ] {
        let label = label.as_str();
        if has_label(label) {
            continue;
        }
        let mut attributes = generated_attributes.clone();
        attributes.mark(AttributeKey::Function);
        attributes.declare_total(TotalityWitness::k_equality());
        sentences.push(Sentence::Production {
            label: Some(Label::new(label)),
            parameters: Vec::new(),
            sort: Sort::new("Bool"),
            items: vec![
                ProductionItem::NonTerminal {
                    sort: Sort::new("K"),
                    name: None,
                },
                ProductionItem::Terminal(terminal.into()),
                ProductionItem::NonTerminal {
                    sort: Sort::new("K"),
                    name: None,
                },
            ],
            attributes,
        });
    }
}

fn add_rule_cells(
    grammar: &mut Grammar,
    sentences: &[&Sentence],
    universe: &SortUniverse,
) -> Result<(), ParseError> {
    grammar.add(
        Sort::new("#OptionalDots"),
        vec![ProductionItem::Terminal("...".into())],
        Some(Label::new("#dots")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("#OptionalDots"),
        Vec::new(),
        Some(Label::new("#noDots")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("Bag"),
        vec![nonterminal("Bag"), nonterminal("Bag")],
        Some(Label::new("#cells")),
        false,
        false,
    )?;
    grammar.add_left_associative("#cells");
    grammar.add(
        Sort::new("Bag"),
        vec![nonterminal("Cell")],
        None,
        false,
        true,
    )?;

    let cell_sorts = sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                sort, attributes, ..
            } if attributes.has(AttributeKey::Cell) => Some(sort.clone()),
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
    let collection_sorts = sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::SyntaxSort {
                sort, attributes, ..
            } if attributes.has(AttributeKey::CellCollection) => Some(sort.clone()),
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

    for sentence in sentences {
        match sentence {
            Sentence::Production {
                label,
                sort,
                items,
                attributes,
                ..
            } if attributes.has(AttributeKey::Cell) => {
                // The load rejects a `cell` production of another shape than an opening item,
                // the contents and a closing item (`check_cell_attributes`).
                let (Some(label), [first, middle @ .., last]) = (label.clone(), items.as_slice())
                else {
                    continue;
                };
                let (first, last) = (first.clone(), last.clone());
                // The body of a cell is a pattern of one sort: the sort of a single body that is
                // neither a cell nor a cell collection, which is an unbound operand of this
                // visible production and so a universe member, else `Bag`, the sort of the cells.
                let body = match middle {
                    [ProductionItem::NonTerminal { sort, .. }]
                        if !cell_sorts.contains(sort) && !collection_sorts.contains(sort) =>
                    {
                        universe.member(sort).ok_or(sort)
                    }
                    _ => Ok(GrammarSort::kernel(KernelSort::Bag)),
                };
                // A parametric body sort whose instance declaration this view does not see is not
                // a member; its body keeps the declared sort and the scaffolding spelled from it.
                let body_sort = match &body {
                    Ok(member) => member.sort(),
                    Err(declared) => *declared,
                };
                let cell_items = |recognized: Sort| {
                    vec![
                        first,
                        nonterminal("#OptionalDots"),
                        ProductionItem::NonTerminal {
                            sort: recognized,
                            name: None,
                        },
                        nonterminal("#OptionalDots"),
                        last,
                    ]
                };
                // Infer a whole-cell anonymous variable at the cell's declared sort, while
                // recognizing the rule scaffolding needed for rewrites in that cell.
                #[cfg(not(feature = "z3-inference"))]
                grammar.add_with_recognized_operands(
                    sort.clone(),
                    cell_items(body_sort.clone()),
                    Some(label),
                    body_sort,
                    &rule_sort(body_sort),
                )?;
                #[cfg(feature = "z3-inference")]
                grammar.add(
                    sort.clone(),
                    cell_items(rule_sort(body_sort)),
                    Some(label),
                    false,
                    false,
                )?;
                grammar.add(
                    Sort::new("Cell"),
                    vec![ProductionItem::NonTerminal {
                        sort: sort.clone(),
                        name: None,
                    }],
                    None,
                    false,
                    true,
                )?;
            }
            Sentence::Production {
                sort, attributes, ..
            } if attributes.has(AttributeKey::CellFragment) => {
                grammar.add(
                    Sort::new("Cell"),
                    vec![ProductionItem::NonTerminal {
                        sort: sort.clone(),
                        name: None,
                    }],
                    None,
                    false,
                    true,
                )?;
            }
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
            | Sentence::Bubble { .. } => {}
        }
    }
    Ok(())
}

#[cfg(test)]
#[allow(clippy::wildcard_enum_match_arm)]
mod tests {
    use super::*;
    use crate::definition::SortCatalog;

    fn try_load_with_prelude(
        source: &str,
    ) -> Result<crate::outer::LoadedDefinition, crate::outer::LoadError> {
        let prelude = crate::builtin::embedded("prelude.md").expect("embedded prelude");
        let mut resolver = |_: &str, required: &str| {
            crate::builtin::embedded(required)
                .ok_or_else(|| format!("unexpected require {required}"))
        };
        crate::outer::load_with_options(
            crate::outer::ResolvedSource::new("main.k", source.to_owned()),
            "MAIN",
            &mut resolver,
            &crate::outer::LoadOptions {
                implicit_sources: vec![prelude],
                ..crate::outer::LoadOptions::default()
            },
        )
    }

    fn load_with_prelude(source: &str) -> crate::outer::LoadedDefinition {
        try_load_with_prelude(source).unwrap_or_else(|error| panic!("MAIN loads: {error}"))
    }

    /// The universe of the rule grammar of `module`, with the declared sorts of the same view.
    fn rule_grammar_universe(
        resolved: &ResolvedDefinition,
        module: &str,
    ) -> (SortUniverse, BTreeSet<Sort>) {
        let module = resolved.module_id(module).expect("the module is resolved");
        let visible = rule_grammar_view(resolved, module);
        let declared = SortCatalog::from_visible(visible.iter().copied())
            .all_sorts()
            .clone();
        (
            SortUniverse::new(&visible, &SortSynonyms::of(visible.iter().copied())),
            declared,
        )
    }

    /// 86a21b90: the parameters `Sort`, `Sort1` and `Sort2` of the ML productions are bound by
    /// each production alone and are not sorts of the module, while a declared sort that shares a
    /// parameter's spelling is.
    #[test]
    fn the_universe_excludes_the_sort_parameters_of_the_ml_productions() {
        let loaded = load_with_prelude(
            r#"
module MAIN
  imports ML-SYNTAX
  syntax Sort2 ::= "s2"
endmodule
"#,
        );
        let resolved = loaded.resolved();
        let module = resolved.module_id("MAIN").expect("MAIN is resolved");
        let mut visible = resolved.signature_sentences(module);
        add_implicit_ml_syntax(resolved, &mut visible);
        assert!(
            visible.iter().any(|sentence| matches!(sentence,
                Sentence::Production { parameters, sort, .. }
                    if sort.name == "Sort1" || parameters.iter().any(|parameter| parameter.name == "Sort1"))),
            "the ML productions binding Sort1 are visible"
        );

        let universe = SortUniverse::new(&visible, &SortSynonyms::of(visible.iter().copied()));

        // The heads of every member, whatever its arity: no member is a parameter.
        let names = universe
            .members()
            .map(|member| member.sort().name.clone())
            .collect::<BTreeSet<_>>();
        assert!(!names.contains("Sort"), "{names:?}");
        assert!(!names.contains("Sort1"), "{names:?}");
        assert!(
            names.contains("Sort2"),
            "the declared sort Sort2 shares a parameter's spelling and stays: {names:?}"
        );
        assert!(universe.member(&Sort::new("Sort")).is_none(), "{names:?}");
        assert!(universe.member(&Sort::new("Sort1")).is_none(), "{names:?}");
        assert!(universe.member(&Sort::new("Sort2")).is_some(), "{names:?}");
    }

    /// A numeral names a width, so both a production of it and an operand position of it are
    /// rejected before the rule bubble is parsed. A declaration alone gives it no terms.
    #[test]
    fn a_numeral_with_terms_or_positions_is_rejected_at_load() {
        for (declaration, expected_places) in [
            (
                r#"syntax 8 ::= "eight""#,
                vec!["the sort of a production.", "an operand of a production."],
            ),
            ("syntax 8", vec!["an operand of a production."]),
        ] {
            let error = try_load_with_prelude(&format!(
                r#"
module MAIN
  {declaration}
  syntax Foo ::= bar(8) | "done"
  rule bar(_X) => done
endmodule
"#
            ))
            .expect_err("a numeral cannot have terms or operand positions");
            let crate::outer::LoadError::SourceDiagnostics(mut diagnostics) = error else {
                panic!("{declaration}: {error}");
            };
            diagnostics
                .sort_by_key(|diagnostic| diagnostic.location.map(|location| location.start_line));
            assert_eq!(diagnostics.len(), expected_places.len(), "{diagnostics:#?}");
            for (diagnostic, place) in diagnostics.iter().zip(expected_places) {
                assert_eq!(
                    diagnostic.code,
                    crate::diagnostic::DiagnosticCode::InvalidNumeralSort,
                    "{diagnostics:#?}"
                );
                assert!(diagnostic.message.ends_with(place), "{diagnostic:#?}");
            }
        }
    }

    /// F10: a rule grammar whose view holds a cell also sees the RULE-CELLS cell
    /// `<generatedCounter> Int </generatedCounter>`, so `Int` is a sort of that grammar although
    /// the view declares no `Int`. A configuration's module imports MAP, which declares `Int`, so
    /// the view here holds a written `cell` production instead.
    #[test]
    fn the_universe_of_a_view_with_the_injected_counter_cell_contains_int() {
        let loaded = load_with_prelude(
            "module CELLS\n  syntax Foo ::= \"foo\"\n  syntax FooCell ::= \"<foo>\" Foo \"</foo>\" [cell, symbol(<foo>)]\nendmodule\n\nmodule MAIN\n  imports CELLS\nendmodule\n",
        );

        let (universe, declared) = rule_grammar_universe(loaded.resolved(), "CELLS");

        let int = Sort::new("Int");
        assert!(!declared.contains(&int), "CELLS's view declares no Int");
        assert_eq!(
            universe.member(&int).map(|member| member.role()),
            Some(crate::kast::SortRole::Defined)
        );
    }

    /// A module whose view holds no configuration cell sees none of the cells compilation adds to
    /// the configuration: BOOL-COMMON's rule grammar has no `<generatedCounter>`, and so no `Int`.
    #[test]
    fn a_view_without_a_configuration_has_no_compiler_added_cell() {
        let loaded = load_with_prelude("module MAIN\nendmodule\n");
        let resolved = loaded.resolved();
        let module = resolved
            .module_id("BOOL-COMMON")
            .expect("the module is resolved");

        assert!(
            !rule_grammar_view(resolved, module)
                .iter()
                .any(|sentence| matches!(
                    sentence,
                    Sentence::Production { attributes, .. } if attributes.has(AttributeKey::Cell)
                ))
        );
        let (universe, _) = rule_grammar_universe(resolved, "BOOL-COMMON");
        assert!(universe.member(&Sort::new("Int")).is_none());
    }

    /// F10: `updateArray(Array, Int, List)` is a public ARRAY-SYNTAX production whose module
    /// imports LIST privately, so a module that sees it without LIST still has positions of sort
    /// `List`, and `List` is a sort of its rule grammar. (The main module is not that module: it
    /// imports the default configuration, which sees LIST.)
    #[test]
    fn the_universe_of_a_view_without_list_contains_the_list_operand_of_array_syntax() {
        let loaded = load_with_prelude(
            r#"
module ARRAY-USER
  imports ARRAY-SYNTAX
endmodule

module MAIN
  imports ARRAY-USER
endmodule
"#,
        );

        let (universe, declared) = rule_grammar_universe(loaded.resolved(), "ARRAY-USER");

        let list = Sort::new("List");
        assert!(
            !declared.contains(&list),
            "ARRAY-USER's view declares no List"
        );
        assert!(universe.member(&list).is_some());
        assert!(universe.member(&Sort::new("Array")).is_some());
    }

    /// A flat `~>` sequence written directly against a rule's rewrite completes sequences
    /// starting after its first item (each `~>` can begin one), and a completion can find a
    /// caller waiting for it for every item before it. What a completion gives a caller depends
    /// on the caller's production and dot only, so it is decided once per group of callers
    /// sharing them: the most decisions one completion makes is bounded by the grammar and does
    /// not grow with the sequence, where deciding for every caller made it grow with the
    /// sequence's length.
    #[test]
    fn a_sequence_against_a_rewrite_decides_each_group_of_callers_once() {
        let [at_30, at_60] = [30, 60].map(|length| {
            let sequence = (0..length)
                .map(|number| format!("foo({})", number % 10))
                .collect::<Vec<_>>()
                .join(" ~> ");
            let source = format!(
                "module MAIN\n  imports INT\n  syntax KItem ::= foo(Int) [symbol(foo)]\n  \
                 configuration <k> $PGM:K </k>\n  rule <k> {sequence} => .K </k>\nendmodule\n"
            );
            crate::inner::parser::take_most_caller_group_decisions();
            drop(load_with_prelude(&source));
            crate::inner::parser::take_most_caller_group_decisions()
        });
        println!("the most decisions one completion made: {at_30} with 30 items, {at_60} with 60");
        // Every completion with a caller decides for it, so a zero is a counter that is no
        // longer fed, which would make the comparison below vacuous.
        assert!(at_30 > 0, "no completion decided for its callers");
        assert_eq!(
            at_30, at_60,
            "the most decisions one completion made: {at_30} with 30 items, {at_60} with 60"
        );
    }

    /// The structural preference chooses before inference, so where it keeps only ill-sorted
    /// readings sorts decide among every reading (`Grammar::infer_without_structural_preference`).
    /// Whatever the outcome, a parse is never a term the per-position choice among well-sorted
    /// readings would not keep, and a rejection other than an ambiguity means no reading is well
    /// sorted. Checked against that choice computed on trees (`Grammar::exact_structural_choice`)
    /// for every sequence of up to three items over a user `=>` building a `Foo` that the
    /// rewrite also reads, where `f` and `h` take a `Foo` and `g` a sort the user's `=>` takes
    /// but the rewrite at `f` cannot.
    #[test]
    fn a_rule_body_parse_is_one_the_choice_among_well_sorted_readings_keeps() {
        // The sides of the user's `=>` are of a sort unrelated to `Foo`, or above it, so that a
        // reading through it can have a greater typing than the rewrite's.
        let unrelated = r#"
  syntax Bar ::= "bar" [symbol(bar)]
  syntax Foo ::= Bar "=>" Bar [symbol(arrowfoo)]
  syntax KItem ::= f(Foo) [symbol(f)] | g(Bar) [symbol(g)] | h(Foo) [symbol(h)]"#;
        let above = r#"
  syntax Qux ::= "qux" [symbol(qux)]
  syntax Baz ::= Foo | Qux
  syntax Foo ::= Baz "=>" Baz [symbol(arrowfoo)]
  syntax KItem ::= f(Foo) [symbol(f)] | g(Qux) [symbol(g)] | h(Foo) [symbol(h)]"#;
        let items = [
            "f(X => Y)",
            "f(Y => X)",
            "f(Z => W)",
            "g(X)",
            "g(Y)",
            "g(W)",
            "h(X)",
            "h(Y)",
            "X => Y",
        ];
        let mut longest: Vec<String> = items.iter().map(|item| (*item).to_owned()).collect();
        let mut bodies = longest.clone();
        for _ in 1..3 {
            longest = longest
                .iter()
                .flat_map(|body| items.iter().map(move |item| format!("{body} ~> {item}")))
                .collect();
            bodies.extend(longest.iter().cloned());
        }
        let start = Sort::new("#RuleContent");
        for syntax in [unrelated, above] {
            let loaded = load_with_prelude(&format!("module MAIN{syntax}\nendmodule\n"));
            let grammar = module_rule_grammar_of(loaded.resolved(), "MAIN");
            let (mut accepted, mut decided, mut ambiguous, mut kept_one, mut rejected) =
                (0, 0, 0, 0, 0);
            for body in &bodies {
                let exact = grammar.exact_structural_choice(&start, body);
                match grammar.parse(&start, body) {
                    Ok(term) => {
                        accepted += 1;
                        decided += usize::from(exact.kept.len() < exact.well_sorted);
                        assert!(
                            exact.kept.iter().any(|kept| kept.identical(&term)),
                            "{syntax}\n{body}: parsed {term}, kept {:?}",
                            exact
                                .kept
                                .iter()
                                .map(ToString::to_string)
                                .collect::<Vec<_>>()
                        );
                    }
                    Err(ParseError::Ambiguous { .. }) => {
                        ambiguous += 1;
                        kept_one += usize::from(exact.kept.len() == 1);
                    }
                    Err(error) => {
                        rejected += 1;
                        assert_eq!(exact.well_sorted, 0, "{syntax}\n{body}: {error}");
                    }
                }
            }
            println!(
                "{} bodies: {accepted} parsed ({decided} where the choice drops a well-sorted \
                 term), {ambiguous} ambiguous ({kept_one} where it keeps one term), \
                 {rejected} rejected",
                bodies.len()
            );
            assert!(decided > 0 && kept_one > 0 && rejected > 0);
        }
    }

    /// When sorts decide among every reading, a part of a structural choice is decided and
    /// joined with another on its inferred forest, never on its trees. In
    /// `f(A => B1 + ... + Bn) ~> h(C => D) ~> k(D)` no preferred reading is well sorted, since
    /// the rewrite at `h` needs `D` both a `Gee` and a `Hoo`. Read as a rewrite at `f`, the sum is
    /// the one left-nested `Foo` sum, whose variables are `Foo`s; read as the user's `=>`, it is a
    /// `Bar` sum of any nesting, `+` on `Bar` having no associativity, whose variables are `Bar`s
    /// below `Foo`. So inference over every reading keeps the rewrite, and the two parts at `f`
    /// are well sorted: the parse is reported ambiguous between them. Inference over the arm's
    /// part keeps a tree per nesting of the sum, all of one typing: 58,786 at twelve operands.
    /// At six (42 trees) the forest's lowering is checked against its trees' (`InferredLowering`); at twelve
    /// the parse unpacks fewer nodes than the part has trees, so it built none of them: what it
    /// unpacks is the test build's check of the one tree inference over every reading keeps.
    #[cfg(feature = "z3-inference")]
    #[test]
    fn a_part_of_a_structural_choice_is_decided_and_joined_on_its_forest() {
        let loaded = load_with_prelude(
            r#"module MAIN
  syntax Bar ::= Bar "+" Bar [symbol(plusBar)]
  syntax Foo ::= Bar | Foo "+" Foo [left, symbol(plusFoo)] > Bar "=>" Bar [symbol(arrowfoo)]
  syntax Hoo ::= "hoo" [symbol(hoo)]
  syntax Gee ::= Hoo "=>" Hoo [symbol(arrowgee)]
  syntax KItem ::= f(Foo) [symbol(f)] | h(Gee) [symbol(h)] | k(Hoo) [symbol(k)]
  syntax K
endmodule
"#,
        );
        let grammar = module_rule_grammar_of(loaded.resolved(), "MAIN");
        for (operands, nestings) in [(6, 42), (12, 58_786)] {
            let sum = (1..=operands)
                .map(|operand| format!("B{operand}"))
                .collect::<Vec<_>>()
                .join(" + ");
            let body = format!("f(A => {sum}) ~> h(C => D) ~> k(D)");
            let before = measure::snapshot().get(Counter::ParserUnpackedNodes);

            let parsed = grammar.parse(&Sort::new("#RuleContent"), &body);

            let unpacked = measure::snapshot().get(Counter::ParserUnpackedNodes) - before;
            let Err(ParseError::Ambiguous { alternatives, .. }) = &parsed else {
                panic!("{body}: {parsed:?}");
            };
            let terms = alternatives
                .iter()
                .map(|alternative| alternative.term.as_str())
                .collect::<Vec<_>>();
            assert_eq!(terms.len(), 2, "{body}: {terms:?}");
            assert!(
                terms[0].starts_with("#SemanticCastToFoo(A)=>plusFoo(")
                    && terms[1].starts_with("arrowfoo(#SemanticCastToBar(A),plusBar("),
                "{body}: {terms:?}"
            );
            if operands == 12 {
                assert!(unpacked < nestings, "{body}: {unpacked} nodes unpacked");
            }
        }
    }

    /// The rule grammar of `module`, as a rule of that module is parsed with it.
    fn module_rule_grammar_of(resolved: &ResolvedDefinition, module: &str) -> Grammar {
        let module = resolved.module_id(module).expect("the module is resolved");
        rule_grammar(resolved, module).expect("the rule grammar builds")
    }

    #[test]
    fn a_declared_numeral_receives_no_rule_grammar_production() {
        let source = |rule: &str| {
            format!(
                r#"module MAIN
  imports BOOL
  syntax 8
  syntax W = 8
  syntax Foo ::= g(K) | "done"
  {rule}
endmodule
"#
            )
        };
        let loaded = load_with_prelude(&source(""));
        let grammar = module_rule_grammar_of(loaded.resolved(), "MAIN");
        let numeral_absent = grammar.sort_id(&Sort::new("8")).is_none();
        let kitem_subsort = grammar.has_equivalent_production(
            &Sort::new("KItem"),
            &[ProductionItem::NonTerminal {
                sort: Sort::new("8"),
                name: None,
            }],
            false,
        );
        let terminals_absent = [":8", "::8", ":W", "::W"]
            .into_iter()
            .all(|terminal| !grammar.has_production_with_terminal(terminal));
        let mut outcomes = Vec::new();
        for cast in ["8", "W"] {
            let rule = format!("rule g(X:{cast}) => done");
            let error = try_load_with_prelude(&source(&rule))
                .err()
                .map(|error| error.to_string());
            outcomes.push((rule, error));
        }
        // Every production's result and nonterminal sorts are interned, so an absent sort id
        // rules out every production position at the numeral, including casts and brackets.
        assert!(
            numeral_absent
                && !kitem_subsort
                && terminals_absent
                && outcomes.iter().all(|(_, error)| error
                    .as_ref()
                    .is_some_and(|error| error.contains("could not parse rule"))),
            "numeral absent: {numeral_absent}; KItem ::= 8: {kitem_subsort}; cast terminals absent: {terminals_absent}; rule outcomes: {outcomes:?}"
        );
    }

    /// Whether `grammar` has the sort helper production `result ::= label "(" K ")"`.
    fn has_sort_helper(grammar: &Grammar, label: &str, result: &str) -> bool {
        grammar.has_equivalent_production(
            &Sort::new(result),
            &[
                ProductionItem::Terminal(label.into()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: Sort::new("K"),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
            ],
            false,
        )
    }

    /// A module that sees the kernel syntax of KSEQ, whose sorts include `KItem`, `KConfigVar`,
    /// `KLabel`, `KList` and `KString`.
    const KSEQ_IMPORTING_MAIN: &str = "module MAIN\n  imports KSEQ\n  imports BOOL\nendmodule\n";

    /// F3: compilation declares `project:KItem` and `project:K`, and the predicates of `K`,
    /// `KItem` and `KConfigVar`, so the rule grammar offers them.
    #[test]
    fn the_rule_grammar_offers_the_kernel_helpers_compilation_declares() {
        let loaded = load_with_prelude(KSEQ_IMPORTING_MAIN);
        let grammar = module_rule_grammar_of(loaded.resolved(), "MAIN");

        for (label, result) in [
            ("project:KItem", "KItem"),
            ("project:K", "K"),
            ("project:Bool", "Bool"),
            ("isKItem", "Bool"),
            ("isK", "Bool"),
            ("isKConfigVar", "Bool"),
            ("isBool", "Bool"),
        ] {
            assert!(has_sort_helper(&grammar, label, result), "{label}");
        }
    }

    /// F3: compilation declares no projection or predicate of `KList`, `KLabel` or `KString`,
    /// which are sorts of the term syntax rather than of K terms, and no projection of
    /// `KConfigVar`, so the rule grammar offers none, although the three are sorts of the module.
    #[test]
    fn the_rule_grammar_offers_no_klist_helper() {
        let loaded = load_with_prelude(KSEQ_IMPORTING_MAIN);
        let (universe, _) = rule_grammar_universe(loaded.resolved(), "MAIN");
        for sort in ["KList", "KLabel", "KString", "KConfigVar"] {
            assert!(
                universe.member(&Sort::new(sort)).is_some(),
                "{sort} is a sort of MAIN's rule grammar"
            );
        }
        let grammar = module_rule_grammar_of(loaded.resolved(), "MAIN");

        for (label, result) in [
            ("project:KList", "KList"),
            ("project:KLabel", "KLabel"),
            ("project:KString", "KString"),
            ("project:KConfigVar", "KConfigVar"),
            ("isKList", "Bool"),
            ("isKLabel", "Bool"),
            ("isKString", "Bool"),
        ] {
            assert!(!has_sort_helper(&grammar, label, result), "{label}");
        }
    }

    /// F3 through the loader: a rule mentioning `project:KItem(_)` parses, and one mentioning
    /// `project:KList(_)` is rejected while parsing, where it could not be compiled.
    #[test]
    fn a_rule_parses_project_kitem_and_rejects_project_klist() {
        let loaded = load_with_prelude(
            r#"
module MAIN
  imports KSEQ
  syntax KItem ::= h(K) [function]
  rule h(X) => project:KItem(X)
endmodule
"#,
        );
        let main = loaded
            .definition()
            .modules
            .iter()
            .find(|module| module.name == "MAIN")
            .expect("MAIN is a module");
        assert!(
            main.local_sentences
                .iter()
                .any(|sentence| matches!(&**sentence,
                Sentence::Rule { body, .. } if body.to_string().contains("`project:KItem`"))),
            "the rule mentions project:KItem"
        );

        let error = match try_load_with_prelude(
            r#"
module MAIN
  imports KSEQ
  syntax Foo ::= h(KList) [function] | g(K) [function]
  rule g(X) => h(project:KList(X))
endmodule
"#,
        ) {
            Ok(_) => panic!("a rule mentioning project:KList loads"),
            Err(error) => error.to_string(),
        };
        assert!(error.contains("could not parse rule"), "{error}");
    }

    /// KAST declares `KList ::= K` and BASIC-K `K ::= KItem`; a label, an argument sequence and a
    /// token spelling are not K items, so the rule grammar of a view without a generated top sort
    /// adds no `KItem ::= KList` (nor the `KLabel` and `KString` subsorts), and no cycle
    /// `KItem < K < KList < KItem` keeps the view's rules from parsing.
    #[test]
    fn a_rule_of_a_view_that_sees_kast_parses() {
        let source = r#"
module MAIN
  imports BASIC-K
  imports KAST
  syntax Exp ::= "a" | "b" | f(Exp) [function]
  rule f(X) => X
endmodule
"#;
        if let Err(error) = try_load_with_prelude(source) {
            panic!("a rule of a view that sees KAST loads: {error}");
        }
    }

    /// The configuration grammar of a view that sees KAST through KSEQ adds no `KItem ::= KList`
    /// either, so its configuration parses.
    #[test]
    fn a_configuration_of_a_view_that_sees_kast_parses() {
        let source = r#"
module MAIN
  imports KSEQ
  syntax Exp ::= "a" | "b"
  configuration <k> $PGM:K </k>
endmodule
"#;
        if let Err(error) = try_load_with_prelude(source) {
            panic!("a configuration of a view that sees KAST loads: {error}");
        }
    }

    /// A view that imports KAST and declares nothing else loads in a debug build: the sort-role
    /// checker reads the rule grammars it builds, and their semantic relations are acyclic (G0).
    /// A user sort is a sort of K items, so `syntax Exp ::= KItem` closes `Exp < KItem < Exp`
    /// with the kernel position the rule grammar gives `Exp`. Built without the load, which would
    /// report the declaration first, the rule grammar rejects the view with that cycle before it
    /// generates any production, so its sort-role check never meets a cyclic relation.
    #[test]
    fn a_view_contradicting_a_kernel_position_has_no_rule_grammar() {
        let source = "module MAIN\n  syntax KItem\n  syntax Exp ::= \"a\"\n  syntax Exp ::= KItem\nendmodule\n";
        let parsed = crate::outer::parse("main.k", source).expect("MAIN parses");
        let definition = crate::outer::lower(&parsed, "MAIN").expect("MAIN lowers");
        let resolved = ResolvedDefinition::resolve(&definition).expect("MAIN resolves");
        let main = resolved.main_module_id();
        match rule_grammar(&resolved, main) {
            Err(ParseError::CircularSubsorts { path }) => {
                assert!(path.contains(&Sort::new("Exp")), "{path:?}");
                assert!(path.contains(&KernelSort::KItem.sort()), "{path:?}");
            }
            Err(error) => panic!("expected the kernel-position cycle, got {error}"),
            Ok(_) => panic!("the rule grammar of a contradicting view was built"),
        }
    }

    #[test]
    fn a_view_that_only_imports_kast_loads() {
        if let Err(error) = try_load_with_prelude("module MAIN\n  imports KAST\nendmodule\n") {
            panic!("a view that only imports KAST loads: {error}");
        }
    }

    /// The projection cast `{T}:>S` lowers to `project:S`, which compilation declares exactly for
    /// the sorts with a sort projection, so the rule grammar offers it for those sorts and their
    /// synonyms only. A width declaration gives a numeral no terms and no projection.
    #[test]
    fn the_rule_grammar_offers_the_projection_cast_only_for_a_sort_with_a_projection() {
        let loaded = load_with_prelude(
            r#"
module MAIN
  imports BOOL
  syntax 8
  syntax Foo ::= "done" | g(K) [function] | h(K)
  syntax Bg = Bag
  syntax Wad = Foo
endmodule
"#,
        );
        let grammar = module_rule_grammar_of(loaded.resolved(), "MAIN");

        for terminal in [":>Foo", ":>Wad", ":>K", ":>KItem", ":>Bool"] {
            assert!(
                grammar.has_production_with_terminal(terminal),
                "the rule grammar offers {terminal}"
            );
        }
        for terminal in [":>8", ":>Bag", ":>Cell", ":>KLabel", ":>KList", ":>Bg"] {
            assert!(
                !grammar.has_production_with_terminal(terminal),
                "the rule grammar offers {terminal}"
            );
        }

        let loaded = load_with_prelude(KSEQ_IMPORTING_MAIN);
        let grammar = module_rule_grammar_of(loaded.resolved(), "MAIN");
        assert!(!grammar.has_production_with_terminal(":>KString"));
    }

    /// A numeral position is rejected at load; a projection cast to `Bag` is rejected at the
    /// cast because no K term can be projected into Bag. A defined sort has a projection.
    #[test]
    fn a_rule_with_a_projection_cast_to_a_sort_without_a_projection_does_not_parse() {
        let numeral_source = r#"
module MAIN
  imports BOOL
  syntax 8 ::= "eight"
  syntax Foo ::= foo(8) | "done" | g(K) [function]
  rule g(X) => foo({X}:>8)
endmodule
"#;
        let error = try_load_with_prelude(numeral_source)
            .expect_err("a numeral cannot have terms or operand positions");
        let crate::outer::LoadError::SourceDiagnostics(diagnostics) = error else {
            panic!("{error}");
        };
        assert_eq!(diagnostics.len(), 2);
        for diagnostic in diagnostics {
            assert_eq!(
                diagnostic.code,
                crate::diagnostic::DiagnosticCode::InvalidNumeralSort
            );
            assert_eq!(diagnostic.severity, crate::diagnostic::Severity::Error);
        }

        let source = |rule: &str| {
            format!(
                r#"
module MAIN
  imports BOOL
  syntax Foo ::= "done" | g(K) [function] | h(K)
  {rule}
endmodule
"#
            )
        };
        let rejected = "rule g(X) => h({X}:>Bag)";
        let error = try_load_with_prelude(&source(rejected)).expect_err("Bag has no projection");
        assert!(
            error.to_string().contains("could not parse rule"),
            "{rejected}: {error}"
        );
        let accepted = "rule g(X) => h({X}:>Foo)";
        if let Err(error) = try_load_with_prelude(&source(accepted)) {
            panic!("`{accepted}` loads: {error}");
        }
    }

    /// A definition's own production labelled `#OuterCast` reads its operand through the
    /// projection into its result sort. A scaffolding sort has no such projection, so its use
    /// is a parse error at the use; with a defined result it lowers to `project:Foo`.
    #[test]
    fn a_definitions_own_projection_cast_to_a_sort_without_a_projection_does_not_parse() {
        let source = |result: &str, rule: &str| {
            format!(
                r#"
module MAIN
  imports BOOL
  syntax #Foo ::= "foo"
  syntax {result} ::= "{{" K "}}" "asFoo" [symbol(#OuterCast)]
  syntax Foo ::= foo(#Foo) | g(K) [function]
  {rule}
endmodule
"#
            )
        };
        let rejected = source("#Foo", "rule g(X) => foo({X} asFoo)");
        match try_load_with_prelude(&rejected) {
            Ok(_) => panic!("`rule g(X) => foo({{X}} asFoo)` loads"),
            Err(error) => {
                let error = error.to_string();
                assert!(
                    error.starts_with("main.k:7:")
                        && error.contains("could not parse rule")
                        && error.contains(
                            "projection cast to sort #Foo, which has no sort projection because no K term has sort #Foo"
                        ),
                    "{error}"
                );
            }
        }

        let accepted = load_with_prelude(&source("Foo", "rule g(X) => {X} asFoo"));
        let mut projects = false;
        for module in &accepted.definition().modules {
            for sentence in &module.local_sentences {
                if let Sentence::Rule { body, .. } = &**sentence {
                    body.visit_preorder(&mut |term| {
                        projects |= matches!(term, Term::Apply { label, .. } if label.name == "project:Foo");
                    });
                }
            }
        }
        assert!(projects, "the rule body mentions project:Foo");
    }

    /// A numeral's terms and positions are rejected before configuration parsing; a projection
    /// cast into a defined sort still loads because compilation declares its projection.
    #[test]
    fn a_configuration_with_a_projection_cast_to_a_numeral_is_rejected_at_load() {
        let rejected = r#"
module MAIN
  imports BOOL
  syntax 8 ::= "eight"
  syntax Foo ::= foo(8) | "done"
  configuration <k> foo({eight}:>8) </k>
endmodule
"#;
        let error = try_load_with_prelude(rejected)
            .expect_err("a numeral cannot have terms or operand positions");
        let crate::outer::LoadError::SourceDiagnostics(diagnostics) = error else {
            panic!("{error}");
        };
        assert_eq!(diagnostics.len(), 2);
        for diagnostic in diagnostics {
            assert_eq!(
                diagnostic.code,
                crate::diagnostic::DiagnosticCode::InvalidNumeralSort
            );
            assert_eq!(diagnostic.severity, crate::diagnostic::Severity::Error);
        }

        let accepted = r#"
module MAIN
  imports BOOL
  syntax Foo ::= "done"
  configuration <k> {done}:>Foo </k>
endmodule
"#;
        if let Err(error) = try_load_with_prelude(accepted) {
            panic!("`{{done}}:>Foo` loads: {error}");
        }
    }

    /// A rule grammar declares each production once. A second copy of a production would parse
    /// every text it derives twice, as an ambiguity whose readings are the same term, and a pass
    /// that reads a node's sort before such readings are merged sees an ambiguity where there is
    /// one term: list completion read the side `L:Bag` of a rewrite at a cell body that way, as
    /// `K`, which a `Bag` position does not hold. The definition writes cells, so the grammar
    /// holds the casts of `Bag` and `Cell` and every cell's productions.
    #[test]
    fn a_rule_grammar_has_no_two_equal_productions() {
        let loaded = load_with_prelude(
            r#"
module MAIN
  imports INT
  configuration <T> <k> $PGM:K </k> <rs> <r multiplicity="*" type="List"> <rid> 0 </rid> </r> </rs> </T>
endmodule
"#,
        );
        let grammar = module_rule_grammar_of(loaded.resolved(), "MAIN");
        assert_eq!(grammar.first_repeated_production(), None);
        let bag = Sort::new("Bag");
        assert_eq!(
            grammar.equivalent_production_count(
                &bag,
                &[
                    ProductionItem::NonTerminal {
                        sort: bag.clone(),
                        name: None,
                    },
                    ProductionItem::Terminal(":Bag".into()),
                ],
                false,
            ),
            1,
            "the semantic cast to Bag"
        );
    }
}
