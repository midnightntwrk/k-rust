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

use std::collections::BTreeSet;
use std::fmt;

use k_rust_kore::measure::{self, Algorithm, Counter};
use web_time::Instant;

use crate::definition::AttributeKey;
use crate::definition::totality::TotalityWitness;
use crate::definition::{
    Attributes, Definition, Location, ModuleId, ProductionItem, ResolveError, ResolvedDefinition,
    Sentence,
};
use crate::kast::sort_role::KernelSort;
use crate::kast::{FrontendSort, InternalLabel, Label, Sort, Term};
use crate::names::BuiltinSort;
use crate::timings::PhaseTimings;

use super::config::{
    BuiltinTokenGrammar, add_bottom_subsort, add_casts, add_implicit_ml_syntax, add_k_syntax,
    add_kitem_subsort, add_sort_bracket, add_subsort, add_synonym_casts, implicit_kseq_bracket,
    nonterminal, truth,
};
use super::location::span_location;
use super::parser::{
    Grammar, ParseError, Scanner, TokenPrecedenceDeclaration, named_projection_productions,
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
    let main = definition.main_module_id();
    let global = global_rule_grammar(definition)?;
    let reachable = definition
        .transitive_imports(main)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let grammar = module_rule_grammar(
        definition,
        module_id,
        &global,
        &reachable,
        "rule",
        &attributes,
    )?;
    parse_rule_like_sentence(&grammar, module, "rule", contents, attributes)
}

/// Replace local rule, claim, context, and context-alias bubbles with KAST sentences.
///
/// This is the syntax-only first slice of Java's non-configuration bubble
/// resolution. Priority and associativity filter the concrete parse forest;
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
    let global_started = timings.as_ref().map(|_| Instant::now());
    let global = global_rule_grammar(resolved);
    if let Some(started) = global_started {
        grammar_seconds += started.elapsed().as_secs_f64();
    }
    let global = global?;
    let reachable = resolved
        .transitive_imports(main)
        .into_iter()
        .collect::<BTreeSet<_>>();

    for module in &mut transformed.modules {
        if !module
            .local_sentences
            .iter()
            .any(|sentence| is_rule_bubble(sentence))
        {
            continue;
        }
        let module_id = resolved
            .module_id(&module.name)
            .expect("every flat module was added to the resolved definition");
        let grammar_started = timings.as_ref().map(|_| Instant::now());
        let grammar = module_rule_grammar(
            resolved,
            module_id,
            &global,
            &reachable,
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

fn global_rule_grammar(definition: &ResolvedDefinition) -> Result<Grammar, RuleError> {
    let main = definition.main_module_id();
    rule_grammar(definition, main, RuleGrammarScope::GlobalScanner).map_err(|error| match error {
        ParseError::InconsistentTokenPrecedence {
            token,
            declarations,
        } => RuleError::InconsistentTokenPrecedence {
            token,
            declarations,
        },
        error => RuleError::Parse(Box::new(RuleParseError {
            module: definition.main_module().name.clone(),
            sentence_type: "rule grammar".into(),
            source: definition
                .main_module()
                .attributes
                .source()
                .map(str::to_owned),
            location: definition.main_module().attributes.location(),
            error,
        })),
    })
}

fn module_rule_grammar(
    definition: &ResolvedDefinition,
    module: ModuleId,
    global: &Grammar,
    reachable: &BTreeSet<ModuleId>,
    sentence_type: &str,
    attributes: &Attributes,
) -> Result<Grammar, RuleError> {
    rule_grammar(
        definition,
        module,
        RuleGrammarScope::Module {
            scanner_seed: reachable.contains(&module).then_some(global.scanner()),
        },
    )
    .map_err(|error| {
        RuleError::Parse(Box::new(RuleParseError {
            module: definition.module(module).name.clone(),
            sentence_type: sentence_type.to_owned(),
            source: attributes.source().map(str::to_owned),
            location: attributes.location(),
            error,
        }))
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
    error: ParseError,
) -> RuleError {
    let span = match &error {
        ParseError::NoParse {
            span: Some(span), ..
        }
        | ParseError::Ambiguous {
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
    match term {
        Term::Annotated { term, metadata } => Term::Annotated {
            term: Box::new(erase_label_parameters(*term)),
            metadata,
        },
        Term::Apply {
            mut label,
            arguments,
        } => {
            label.parameters.clear();
            Term::Apply {
                label,
                arguments: arguments.into_iter().map(erase_label_parameters).collect(),
            }
        }
        Term::InjectedLabel(mut label) => {
            label.parameters.clear();
            Term::InjectedLabel(label)
        }
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(erase_label_parameters(*left)),
            right: Box::new(erase_label_parameters(*right)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(erase_label_parameters(*pattern)),
            alias: Box::new(erase_label_parameters(*alias)),
        },
        Term::Sequence(items) => {
            Term::Sequence(items.into_iter().map(erase_label_parameters).collect())
        }
        term @ (Term::Variable { .. } | Term::Token { .. }) => term,
    }
}

fn up_sentence(
    module: &str,
    sentence_type: &str,
    parsed: Term,
    attributes: Attributes,
) -> Result<Sentence, RuleError> {
    let Term::Apply { label, arguments } = erase_label_parameters(parsed).into_unannotated() else {
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

#[derive(Clone, Copy)]
enum RuleGrammarScope<'a> {
    GlobalScanner,
    Module { scanner_seed: Option<&'a Scanner> },
}

/// The sentences the rule grammar of `module` is built from: the module's sentences (all of them
/// for the global scanner, the signature plus ML-SYNTAX for a module grammar), plus the RULE-CELLS
/// cell productions that no visible cell production already provides.
fn rule_grammar_view<'a>(
    resolved: &'a ResolvedDefinition,
    module: ModuleId,
    scope: RuleGrammarScope<'_>,
) -> Vec<&'a Sentence> {
    let mut visible = match scope {
        RuleGrammarScope::GlobalScanner => resolved.sentences(module),
        RuleGrammarScope::Module { .. } => {
            let mut visible = resolved.signature_sentences(module);
            add_implicit_ml_syntax(resolved, &mut visible);
            visible
        }
    };
    // RULE-CELLS supplies parse-only cells, notably generatedCounter for claims
    // about fresh constants. The compiler generates their real productions later.
    // Import only these declarations into the grammar, preserving the source module.
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
    visible
}

fn rule_grammar(
    resolved: &ResolvedDefinition,
    module: ModuleId,
    scope: RuleGrammarScope<'_>,
) -> Result<Grammar, ParseError> {
    let visible = rule_grammar_view(resolved, module, scope);
    let scanner_seed = match scope {
        RuleGrammarScope::GlobalScanner => None,
        RuleGrammarScope::Module { scanner_seed } => scanner_seed,
    };
    // Built after the RULE-CELLS injection, so the injected cells' body sorts are members.
    let universe = SortUniverse::new(&visible);
    let has_generated_top_sort = visible.iter().any(|sentence| {
        matches!(
            sentence,
            Sentence::Production {
                label: None,
                parameters,
                sort,
                items,
                ..
            } if sort.name == BuiltinSort::KItem.k_name()
                && matches!(items.as_slice(), [ProductionItem::NonTerminal { sort: child, .. }]
                    if parameters.contains(child))
        )
    });
    let has_generated_bottom_sort = visible.iter().any(|sentence| {
        matches!(
            sentence,
            Sentence::Production {
                label: None,
                parameters,
                sort,
                items,
                ..
            } if parameters.contains(sort)
                && matches!(items.as_slice(), [ProductionItem::NonTerminal { sort: child, .. }]
                    if child.name == FrontendSort::KBott.as_str())
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
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let mut parsing_sentences = visible
        .iter()
        .filter(|sentence| {
            !matches!(
                sentence,
                Sentence::Production { attributes, .. } if attributes.has(AttributeKey::Cell)
            )
        })
        .map(|sentence| (*sentence).clone())
        .collect::<Vec<_>>();
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
            .filter(|member| !has_production_labeled(&Label::projection(member.sort()).name))
            .map(|member| sort_projection_production(&member)),
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
    let mut grammar =
        Grammar::from_rule_sentences(parsing_sentences.iter(), &source_catalog, scanner_seed)?;
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
            _ => None,
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
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    add_k_syntax(&mut grammar, BuiltinTokenGrammar::Rule)?;
    // KSEQ is implicit in the reference rule grammar. Preserve its bracket's
    // priority contract when adding the concrete brackets supplied by our seed.
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

fn sort_projection_production(sort: &GrammarSort) -> Sentence {
    let label = Label::projection(sort.sort());
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
    add_subsort(grammar, "KBott", Sort::new("#KVariable"))?;
    add_subsort(grammar, "KBott", Sort::new("KConfigVar"))?;
    add_subsort(grammar, "KItem", Sort::new("KBott"))?;
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
    //   #Rule<S>        ::= S | S "#as" S | S "=>" S   (operands of `=>` recognized as the side)
    //   #RewriteSide<S> ::= S | S "#as" S
    // `P #as V` is the conjunction of `P` and `V` at one position: it matches the terms that
    // match both and binds `V` to the matched term. Both conjuncts occupy that position, so the
    // alias is an operand of `sort` like the pattern: a bare variable there is bounded by `sort`,
    // and a sort-annotated variable (`V:Int`) can stand there. An `#as` pattern is a pattern of
    // sort `S` like any other, so it can also stand where a rewrite side stands.
    // The operands of `=>` stay declared `S`, so inference bounds a plain side by `S` and an
    // `#as` side by its own operands. A rewrite is not a side, so `A => B => C` and a rewrite as
    // an operand of `#as` need parentheses, where the scope rules apply. `#Rule<S>` and
    // `#RewriteSide<S>` each derive an `#as` directly, so an `#as` has one derivation wherever
    // it stands: at a `#Rule<S>` position outside a rewrite, or as a side inside one.
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

#[cfg(not(feature = "z3-inference"))]
fn rule_sort(sort: &Sort) -> Sort {
    Sort::new(format!("#Rule{}", sort.name))
}

// The prefix differs from `#Rule`, so no user sort name makes the two families collide.
#[cfg(not(feature = "z3-inference"))]
fn rewrite_side_sort(sort: &Sort) -> Sort {
    Sort::new(format!("#RewriteSide{}", sort.name))
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
            _ => None,
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
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let collection_sorts = sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::SyntaxSort {
                sort, attributes, ..
            } if attributes.has(AttributeKey::CellCollection) => Some(sort.clone()),
            _ => None,
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
                let (Some(label), Some(first), Some(last)) =
                    (label.clone(), items.first().cloned(), items.last().cloned())
                else {
                    continue;
                };
                let middle = &items[1..items.len().saturating_sub(1)];
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
            _ => {}
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::definition::SortCatalog;

    fn load_with_prelude(source: &str) -> crate::outer::LoadedDefinition {
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
        .expect("MAIN loads")
    }

    /// The universe of the rule grammar of `module`, with the declared sorts of the same view.
    fn rule_grammar_universe(
        resolved: &ResolvedDefinition,
        module: &str,
    ) -> (SortUniverse, BTreeSet<Sort>) {
        let module = resolved.module_id(module).expect("the module is resolved");
        let visible = rule_grammar_view(
            resolved,
            module,
            RuleGrammarScope::Module { scanner_seed: None },
        );
        let declared = SortCatalog::from_visible(visible.iter().copied())
            .all_sorts()
            .clone();
        (SortUniverse::new(&visible), declared)
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
        let resolved = &loaded.resolved;
        let module = resolved.module_id("MAIN").expect("MAIN is resolved");
        let mut visible = resolved.signature_sentences(module);
        add_implicit_ml_syntax(resolved, &mut visible);
        assert!(
            visible.iter().any(|sentence| matches!(sentence,
                Sentence::Production { parameters, sort, .. }
                    if sort.name == "Sort1" || parameters.iter().any(|parameter| parameter.name == "Sort1"))),
            "the ML productions binding Sort1 are visible"
        );

        let universe = SortUniverse::new(&visible);

        let names = universe
            .members()
            .map(|member| member.sort().name.clone())
            .collect::<BTreeSet<_>>();
        assert!(universe.member(&Sort::new("Sort")).is_none(), "{names:?}");
        assert!(universe.member(&Sort::new("Sort1")).is_none(), "{names:?}");
        assert!(
            universe.member(&Sort::new("Sort2")).is_some(),
            "the declared sort Sort2 shares a parameter's spelling and stays: {names:?}"
        );
    }

    /// F10: every rule grammar sees the RULE-CELLS cell `<generatedCounter> Int
    /// </generatedCounter>`, so `Int` is a sort of the rule grammar of BOOL-COMMON, whose visible
    /// sentences declare no `Int`.
    #[test]
    fn the_universe_of_a_view_with_the_injected_counter_cell_contains_int() {
        let loaded = load_with_prelude("module MAIN\nendmodule\n");

        let (universe, declared) = rule_grammar_universe(&loaded.resolved, "BOOL-COMMON");

        let int = Sort::new("Int");
        assert!(
            !declared.contains(&int),
            "BOOL-COMMON's view declares no Int"
        );
        assert_eq!(
            universe.member(&int).map(|member| member.role()),
            Some(crate::kast::SortRole::Defined)
        );
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

        let (universe, declared) = rule_grammar_universe(&loaded.resolved, "ARRAY-USER");

        let list = Sort::new("List");
        assert!(
            !declared.contains(&list),
            "ARRAY-USER's view declares no List"
        );
        assert!(universe.member(&list).is_some());
        assert!(universe.member(&Sort::new("Array")).is_some());
    }
}
