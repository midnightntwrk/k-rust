//! ```toml algorithm
//! id = "parser.bubble.configurations"
//! name = "parsing and reconstruction of configuration bubbles"
//! sites = ["resolve_configuration_bubbles"]
//! variable = "b = configuration bubbles; g = grammar construction work summed over modules with configuration bubbles; p = parse work; r = ResolvedDefinition::resolve work; D = definition size"
//! counters = ["ParserGrammarBuilds", "ParserParseAttempts"]
//! consumes = [
//!   { type = "k_rust::definition::Definition", role = "lowered source" },
//! ]
//! produces = [{ type = "k_rust::definition::Definition", role = "parsed configuration bubbles" }]
//!
//! [[cost]]
//! mode = "one definition"
//! bound = "O(r + D + g + sum over b of p)"
//! ```
//!
//! Per-module configuration-bubble parsing with K implicit configuration syntax.
//!
//! One grammar is built for each module with configurations, then each bubble runs the Earley
//! pipeline. Cost is O(grammar construction + bubble parse work); rule bubbles use
//! `Counter::KompileRuleBubblesParsed`, while configuration work is visible in parse counters.

#![deny(clippy::wildcard_enum_match_arm)]

use std::fmt;

use crate::definition::AttributeKey;
use crate::definition::{
    Attributes, Definition, EquivalenceAccumulator, LabelHead, LabelResultSort, Location, ModuleId,
    ProductionItem, ResolveError, ResolvedDefinition, Sentence, SortSynonyms,
    kernel_position_cycle, push_if_inequivalent,
};
use crate::kast::sort_role::KernelSort;
use crate::kast::{FrontendSort, InternalLabel, Label, Sort, Term, TermParts, TermSpan};

use super::location::{locate_ambiguity_places, span_location};
use super::parser::{Grammar, ParseError};
use super::sort_universe::configuration::{
    CONFIGURATION_BRACKET_SEED_ORDER, CONFIGURATION_GRAMMAR, configuration_kernel_seeds,
    configuration_member_productions,
};
use super::sort_universe::{CastTarget, GrammarPlan, GrammarSort, SortUniverse};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConfigError {
    Definition(ResolveError),
    Parse {
        module: String,
        source: Option<String>,
        location: Option<Location>,
        error: Box<ParseError>,
    },
    IllegalRequires {
        module: String,
        source: Option<String>,
        location: Option<Location>,
    },
    /// The configuration's text writes a configuration variable that its parse does not read
    /// as one.
    UnreadVariable(Box<UnreadConfigurationVariable>),
}

/// A configuration variable written in a configuration's text and read there as part of
/// another token, so the compiled configuration holds that text and reads no value of the
/// variable.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnreadConfigurationVariable {
    pub module: String,
    pub source: Option<String>,
    /// Where the variable is written.
    pub location: Option<Location>,
    /// The variable as written, `$` included.
    pub variable: String,
    /// The name of the innermost cell around the variable, if the parse places it in one.
    pub cell: Option<String>,
    /// The sort of the token the parse reads the variable's text in, if it reads it in one.
    pub sort: Option<Sort>,
}

impl fmt::Display for ConfigError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Definition(error) => error.fmt(formatter),
            Self::Parse { module, error, .. } => {
                write!(
                    formatter,
                    "could not parse configuration in module {module:?}: {error}"
                )
            }
            Self::IllegalRequires { module, .. } => write!(
                formatter,
                "configuration in module {module:?} cannot contain a requires clause"
            ),
            Self::UnreadVariable(unread) => {
                let UnreadConfigurationVariable {
                    module,
                    variable,
                    cell,
                    sort,
                    ..
                } = &**unread;
                write!(
                    formatter,
                    "configuration in module {module:?} writes the configuration variable `{variable}`"
                )?;
                if let Some(cell) = cell {
                    write!(formatter, " in cell <{cell}>")?;
                }
                match sort {
                    Some(sort) => write!(
                        formatter,
                        " but parses it as text of a token of sort {sort}"
                    )?,
                    None => write!(
                        formatter,
                        " but does not parse it as a configuration variable"
                    )?,
                }
                write!(
                    formatter,
                    ", so the initial configuration would not read `{variable}` there"
                )
            }
        }
    }
}

impl std::error::Error for ConfigError {}

/// Replace local `config` bubbles with structured configuration sentences.
///
/// This is the parsing half of configuration resolution.
/// Generating cell productions and initializer rules remains a subsequent
/// compilation pass.
pub fn resolve_configuration_bubbles(definition: &Definition) -> Result<Definition, ConfigError> {
    if !definition
        .modules
        .iter()
        .flat_map(|module| module.local_sentences.iter())
        .any(|sentence| is_configuration_bubble(sentence))
    {
        return Ok(definition.clone());
    }
    let resolved = ResolvedDefinition::resolve(definition).map_err(ConfigError::Definition)?;
    let mut transformed = definition.clone();

    for module in &mut transformed.modules {
        if !module
            .local_sentences
            .iter()
            .any(|sentence| is_configuration_bubble(sentence))
        {
            continue;
        }
        let module_id = resolved
            .module_id(&module.name)
            .expect("every flat module was added to the resolved definition");
        let grammar =
            configuration_grammar(&resolved, module_id).map_err(|error| ConfigError::Parse {
                module: module.name.clone(),
                source: module.attributes.source().map(str::to_owned),
                location: module.attributes.location(),
                error: Box::new(error),
            })?;

        for sentence in &mut module.local_sentences {
            let Sentence::Bubble {
                sentence_type,
                contents,
                attributes,
            } = &**sentence
            else {
                continue;
            };
            if sentence_type != "config" {
                continue;
            }
            let parsed = if let Some(source) = attributes.source_id() {
                grammar.parse_with_provenance(
                    &Sort::new("#RuleContent"),
                    contents,
                    source,
                    content_start_offset(attributes),
                )
            } else {
                grammar.parse(&Sort::new("#RuleContent"), contents)
            }
            .map_err(|error| bubble_error(&module.name, attributes, Some(contents), error))?;
            reject_unread_configuration_variables(
                &module.name,
                attributes,
                contents,
                &grammar,
                &parsed,
            )?;
            *crate::definition::sentence_mut(sentence) = up_configuration(
                &module.name,
                parsed,
                attributes.clone(),
                &resolved,
                module_id,
            )?;
        }
    }

    Ok(transformed)
}

/// Reject a configuration whose text writes a configuration variable that its parse does not
/// read as one.
///
/// Configuration expansion turns each configuration-variable token of a parsed configuration
/// into a read of that variable's initial value, so a configuration reads the variables its
/// text writes exactly through those tokens. A `$X` of the text (a token of the scanner's
/// stream that the `KConfigVar` lexeme scans) that no such token spans was built into a token of
/// another sort, whose value is the text it spans (a token production over a phrase): the
/// compiled configuration would hold the text `$X` and read no value of `X`, so the value
/// given for `$X` would be discarded. Each written occurrence is checked, so a variable read in
/// one cell does not cover its text taken as a token in another.
fn reject_unread_configuration_variables(
    module: &str,
    attributes: &Attributes,
    contents: &str,
    grammar: &Grammar,
    parsed: &Term,
) -> Result<(), ConfigError> {
    // A token of `parsed` that carries a span, with the name of its innermost enclosing cell.
    // Only a token can hold a written `$X`: any other leaf is built from a lexeme of its own.
    struct Leaf<'a> {
        span: TermSpan,
        sort: &'a Sort,
        cell: Option<&'a str>,
    }

    fn span_of(mut term: &Term) -> Option<TermSpan> {
        while let Term::Annotated {
            term: inner,
            metadata,
        } = term
        {
            if metadata.span.is_some() {
                return metadata.span;
            }
            term = inner;
        }
        None
    }

    let config_var = KernelSort::KConfigVar.name();
    let written = grammar.scanned_tokens_of(&Sort::new(config_var), contents);
    if written.is_empty() {
        return Ok(());
    }
    // A parse with provenance places byte zero of `contents` at the content offset; one
    // without places it at zero.
    let base_offset = if attributes.source_id().is_some() {
        content_start_offset(attributes)
    } else {
        0
    };
    let mut leaves = Vec::new();
    let mut pending = vec![(parsed, None)];
    // Invariant: `leaves` holds the spanned tokens among the nodes visited so far, and each entry
    // of `pending` is an unvisited node with its innermost enclosing cell; each iteration visits
    // one node and pushes its children.
    while let Some((term, cell)) = pending.pop() {
        let span = span_of(term);
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "Term is not a sentence kind; only the listed variants are special here"
        )]
        match term.unannotated() {
            Term::Token { sort, .. } => {
                if let Some(span) = span {
                    leaves.push(Leaf { span, sort, cell });
                }
            }
            Term::Apply { label, arguments } if label.is(InternalLabel::ConfigCell) => {
                let name = arguments
                    .first()
                    .and_then(|start| match start.unannotated() {
                        Term::Token { token, sort } if sort.is_frontend(FrontendSort::CellName) => {
                            Some(token.as_str())
                        }
                        _ => None,
                    });
                pending.extend(
                    term.children()
                        .into_iter()
                        .map(|child| (child, name.or(cell))),
                );
            }
            _ => pending.extend(term.children().into_iter().map(|child| (child, cell))),
        }
    }
    // The tokens of a parse span disjoint pieces of the text, so the only one that can cover a
    // written variable is the last to start at or before it.
    leaves.sort_by_key(|leaf| leaf.span.start);
    for (start, end) in written {
        let (start_offset, end_offset) = (base_offset + start, base_offset + end);
        let covering = leaves
            .partition_point(|leaf| leaf.span.start <= start_offset)
            .checked_sub(1)
            .map(|index| &leaves[index])
            .filter(|leaf| end_offset <= leaf.span.end);
        if covering.is_some_and(|leaf| {
            leaf.sort.name == config_var
                && (leaf.span.start, leaf.span.end) == (start_offset, end_offset)
        }) {
            continue;
        }
        let location = attributes.source_id().and_then(|source| {
            super::location::span_location(
                attributes,
                contents,
                TermSpan {
                    source,
                    start: content_start_offset(attributes) + start,
                    end: content_start_offset(attributes) + end,
                },
            )
        });
        return Err(ConfigError::UnreadVariable(Box::new(
            UnreadConfigurationVariable {
                module: module.to_owned(),
                source: attributes.source().map(str::to_owned),
                location: location.or_else(|| attributes.location()),
                variable: contents[start..end].to_owned(),
                cell: covering.and_then(|leaf| leaf.cell).map(str::to_owned),
                sort: covering.map(|leaf| leaf.sort.clone()),
            },
        )));
    }
    Ok(())
}

fn content_start_offset(attributes: &Attributes) -> usize {
    attributes
        .value(AttributeKey::ContentStartOffset)
        .and_then(serde_json::Value::as_u64)
        .and_then(|offset| usize::try_from(offset).ok())
        .unwrap_or(0)
}

fn is_configuration_bubble(sentence: &Sentence) -> bool {
    matches!(
        sentence,
        Sentence::Bubble { sentence_type, .. } if sentence_type == "config"
    )
}

fn bubble_error(
    module: &str,
    attributes: &Attributes,
    contents: Option<&str>,
    mut error: ParseError,
) -> ConfigError {
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
    let location = match span {
        Some(span) => contents
            .and_then(|contents| span_location(attributes, contents, span))
            .or_else(|| attributes.location()),
        None => attributes.location(),
    };
    ConfigError::Parse {
        module: module.to_owned(),
        source: attributes.source().map(str::to_owned),
        location,
        error: Box::new(error),
    }
}

fn up_configuration(
    module: &str,
    parsed: Term,
    attributes: Attributes,
    resolved: &ResolvedDefinition,
    module_id: ModuleId,
) -> Result<Sentence, ConfigError> {
    // Only cell-content leaves determine generated cell sorts; nested applications do not.
    // A production whose result mentions its parameters has at least one parameter, so only an
    // application carrying an instance can have a schematic result; the module's production
    // catalog is read (and, on first use, built) only for such a leaf.
    fn keep_content_instance(
        term: Term,
        resolved: &ResolvedDefinition,
        module_id: ModuleId,
    ) -> Term {
        crate::stack::guarded(|| {
            // #configCell arguments are [start, properties, contents, end].
            const CONFIG_CELL_CONTENTS_INDEX: usize = 2;
            if let Term::Apply { label, .. } = term.unannotated()
                && !label.is(InternalLabel::ConfigCell)
                && !label.is(InternalLabel::Cells)
                && !label.is(InternalLabel::ExternalCell)
                && label.semantic_cast_sort().is_none()
            {
                if label.parameters.is_empty() {
                    return term;
                }
                if let Some(result @ LabelResultSort::Schematic { .. }) = resolved
                    .production_catalog(module_id)
                    .result_sort_of(&LabelHead::from(label))
                    && let Some(sort) = result.of_application(&label.parameters)
                {
                    return Term::Apply {
                        label: Label::semantic_cast(&sort),
                        arguments: vec![term],
                    };
                }
                return term;
            }
            match term.into_parts() {
                TermParts::Annotated { term, metadata } => Term::Annotated {
                    term: Box::new(keep_content_instance(*term, resolved, module_id)),
                    metadata,
                },
                TermParts::Apply {
                    label,
                    mut arguments,
                } => {
                    if label.is(InternalLabel::ConfigCell) {
                        arguments = arguments
                            .into_iter()
                            .enumerate()
                            .map(|(index, term)| {
                                if index == CONFIG_CELL_CONTENTS_INDEX {
                                    keep_content_instance(term, resolved, module_id)
                                } else {
                                    term
                                }
                            })
                            .collect();
                    } else if label.is(InternalLabel::Cells) {
                        arguments = arguments
                            .into_iter()
                            .map(|term| keep_content_instance(term, resolved, module_id))
                            .collect();
                    }
                    Term::Apply { label, arguments }
                }
                parts @ (TermParts::InjectedLabel(_)
                | TermParts::Rewrite { .. }
                | TermParts::As { .. }
                | TermParts::Variable { .. }
                | TermParts::Sequence(_)
                | TermParts::Token { .. }) => Term::from(parts),
            }
        })
    }

    let TermParts::Apply { label, arguments } = parsed.into_unannotated().into_parts() else {
        return Err(bubble_error(
            module,
            &attributes,
            None,
            ParseError::InvalidParseShape {
                expected: "#RuleContent".into(),
            },
        ));
    };
    match (InternalLabel::of(&label.name), arguments.as_slice()) {
        (Some(InternalLabel::RuleNoConditions), [body]) => Ok(Sentence::Configuration {
            body: super::rules::erase_label_parameters(keep_content_instance(
                body.clone(),
                resolved,
                module_id,
            )),
            ensures: truth(),
            attributes,
        }),
        (Some(InternalLabel::RuleEnsures), [body, ensures]) => Ok(Sentence::Configuration {
            body: super::rules::erase_label_parameters(keep_content_instance(
                body.clone(),
                resolved,
                module_id,
            )),
            ensures: super::rules::erase_label_parameters(ensures.clone()),
            attributes,
        }),
        (Some(InternalLabel::RuleRequires | InternalLabel::RuleRequiresEnsures), _) => {
            Err(ConfigError::IllegalRequires {
                module: module.to_owned(),
                source: attributes.source().map(str::to_owned),
                location: attributes.location(),
            })
        }
        _ => Err(bubble_error(
            module,
            &attributes,
            None,
            ParseError::InvalidParseShape {
                expected: "configuration body".into(),
            },
        )),
    }
}

fn configuration_grammar(
    resolved: &ResolvedDefinition,
    module: ModuleId,
) -> Result<Grammar, ParseError> {
    let mut visible = resolved.signature_sentences(module);
    let signature = visible.len();
    add_implicit_ml_syntax(resolved, &mut visible);
    reject_kernel_position_contradiction(&visible)?;
    // Start sorts and #token sort strings denote in the module's full view. SortUniverse
    // still restricts generated casts to aliases declared in this grammar's own view.
    let synonyms = if resolved.declares_sort_synonyms() {
        SortSynonyms::of_module(resolved, module)
    } else {
        SortSynonyms::default()
    };
    // The reference configuration grammar imports DEFAULT-LAYOUT explicitly,
    // even when the language declares a program-specific `#Layout` sort.
    let mut grammar = Grammar::from_configuration_view(
        visible.iter().copied(),
        signature,
        synonyms.denotations().clone(),
    )?;
    // The sorts the per-sort productions range over: the rule grammar's universe over this
    // grammar's visible sentences. A visible production gives each of its operand sorts a
    // position whether or not that sort's declaration is visible here (a private import hides
    // it), and a configuration variable standing at that position needs the sort's variable
    // subsorts, so an operand sort is a member even when no visible sentence declares it.
    let universe = SortUniverse::new(&visible, &synonyms);

    add_config_cells(&mut grammar)?;
    grammar.add_matching_terminal_tokens(Sort::new("#CellName"), is_cell_name)?;
    add_k_syntax(&mut grammar, BuiltinTokenGrammar::Configuration)?;
    // K's configuration grammar imports the KAST seed, whose #KToken production is the only
    // source form that can intentionally construct a token without passing its value through
    // configuration-variable inference first. Keep this parser-only KBott bridge local to the
    // configuration grammar; lower_term converts the selected #KToken application to Term::Token.
    add_subsort(&mut grammar, "KBott", "KConfigVar")?;
    add_subsort(&mut grammar, "KItem", "KBott")?;
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

    // Every member whose row has a bracket, then the kernel seeds (`K`, `KItem`, `Bag`) whether
    // or not the module declares them; `add_bracket` skips a bracket the grammar already has.
    let default_bracket = implicit_kseq_bracket(resolved);
    for member in universe.members() {
        if configuration_member_productions(member.role()).bracket {
            add_sort_bracket(&mut grammar, &member, default_bracket)?;
        }
    }
    for kernel in CONFIGURATION_BRACKET_SEED_ORDER {
        if configuration_kernel_seeds(kernel).bracket {
            add_sort_bracket(&mut grammar, &GrammarSort::kernel(kernel), default_bracket)?;
        }
    }

    for member in universe.members() {
        let productions = configuration_member_productions(member.role());
        if productions.kitem_subsort {
            add_kitem_subsort(&mut grammar, &member)?;
        }
        if productions.variable_subsorts {
            add_bottom_subsort(&mut grammar, &member, KernelSort::KConfigVar.name())?;
            add_bottom_subsort(&mut grammar, &member, FrontendSort::KVariable.as_str())?;
        }
        if productions.casts {
            add_casts(&mut grammar, &CastTarget::member(&member))?;
        }
    }
    add_synonym_casts(&mut grammar, &universe, &CONFIGURATION_GRAMMAR)?;

    // The generated productions are complete; check their sorts against their roles and the
    // acyclicity of the semantic subsort relation (G0-G3).
    #[cfg(debug_assertions)]
    grammar.assert_generated_sort_roles(&universe);
    grammar.read_token_text_as_program_text();
    Ok(grammar)
}

/// Reject the definition sentences `visible` a grammar is about to be built from when their
/// declared subsorts contradict the positions `K` fixes for its kernel sorts.
///
/// The rule and configuration grammars add, for every member sort, the kernel subsorts its role
/// grants (`S < KItem`, `KBott < S` and the variable sorts below `S`). A declared subsort that
/// places a sort of K items at or above `KItem` or `K`, or a sort a variable stands at at or below
/// `KBott`, closes a cycle with those pairs, and a grammar with a cyclic subsort relation has no
/// order to infer sorts against. The error is the grammar's circular subsort error with the cycle
/// of declared and kernel pairs. The load reports the same contradiction as a diagnostic on the
/// declaration before it builds any grammar; this check makes every builder establish it, whatever
/// path reaches it. It reads only the sentences the builder already holds, so it adds no counted
/// work.
pub(super) fn reject_kernel_position_contradiction(
    visible: &[&Sentence],
) -> Result<(), ParseError> {
    match kernel_position_cycle(visible) {
        Some(cycle) => Err(ParseError::CircularSubsorts { path: cycle.path }),
        None => Ok(()),
    }
}

pub(super) fn implicit_kseq_bracket(resolved: &ResolvedDefinition) -> Option<&Attributes> {
    let kseq = resolved.module_id("KSEQ")?;
    resolved
        .module(kseq)
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence.as_ref() {
            Sentence::Production { attributes, .. } if attributes.has(AttributeKey::Bracket) => {
                Some(attributes)
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
}

/// The reference rule and configuration grammar seed imports `K`, whose
/// `KSEQ-SYMBOLIC` import contributes `ML-SYNTAX` independently of the user
/// module signature. The hand-built seed models the rest of that syntax.
pub(super) fn add_implicit_ml_syntax<'a>(
    resolved: &'a ResolvedDefinition,
    visible: &mut Vec<&'a Sentence>,
) {
    let Some(module) = resolved.module_id("ML-SYNTAX") else {
        return;
    };
    let mut unique = EquivalenceAccumulator::from_sentences(visible.iter().copied());
    let accepted = resolved
        .signature_sentences(module)
        .into_iter()
        .filter(|sentence| push_if_inequivalent(&mut unique, sentence))
        .collect::<Vec<_>>();
    visible.extend(accepted);
}

fn is_cell_name(value: &str) -> bool {
    let mut characters = value.chars();
    characters
        .next()
        .is_some_and(|character| character.is_ascii_alphabetic())
        && characters.all(|character| character.is_ascii_alphanumeric() || character == '-')
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum BuiltinTokenGrammar {
    Rule,
    Configuration,
}

const BUILTIN_LEXEMES: [(&str, &str, &str); 7] = [
    ("#LowerId", r"[a-z][a-zA-Z0-9]*", "2"),
    ("#UpperId", r"[A-Z][a-zA-Z0-9]*", "2"),
    (
        "KString",
        r#"[\"](([^\"\n\r\\])|([\\][nrtf\"\\])|([\\][x][0-9a-fA-F]{2})|([\\][u][0-9a-fA-F]{4})|([\\][U][0-9a-fA-F]{8}))*[\"]"#,
        "0",
    ),
    ("KLabel", r"`(\\`|\\\\|[^`\\\n\r])+`", "0"),
    ("KLabel", r"[#a-z][a-zA-Z0-9]*", "1"),
    (
        "#KVariable",
        r"(\!|\?|@)?([A-Z][A-Za-z0-9'_]*|_|_[A-Z][A-Za-z0-9'_]*)",
        "1",
    ),
    ("KConfigVar", r"(\$)([A-Z][A-Za-z0-9'_]*)", "0"),
];

/// Lexemes and token subsorts imported from `kast.md` by every rule grammar.
pub(super) fn add_builtin_tokens(
    grammar: &mut Grammar,
    which: BuiltinTokenGrammar,
) -> Result<(), ParseError> {
    for (sort, regex, precedence) in BUILTIN_LEXEMES {
        grammar.add_token_with_precedence(
            Sort::new(sort),
            ProductionItem::regex(regex),
            precedence,
        )?;
    }
    grammar.add_token_subsort("KLabel", "#LowerId")?;
    grammar.add_token_subsort("#KVariable", "#UpperId")?;
    if which == BuiltinTokenGrammar::Configuration {
        grammar.add_token_with_precedence(
            Sort::new("#CellName"),
            ProductionItem::regex(r"[a-zA-Z][a-zA-Z0-9\-]*"),
            "1",
        )?;
        grammar.add_token_subsort("#CellName", "#LowerId")?;
        grammar.add_token_subsort("#CellName", "#UpperId")?;
    }
    Ok(())
}

pub(super) fn add_k_syntax(
    grammar: &mut Grammar,
    which: BuiltinTokenGrammar,
) -> Result<(), ParseError> {
    add_builtin_tokens(grammar, which)?;
    add_subsort(grammar, "K", "KItem")?;
    add_subsort(grammar, "KItem", "Bag")?;
    add_subsort(grammar, "KItem", "Bool")?;
    add_subsort(grammar, "KItem", "KConfigVar")?;
    add_subsort(grammar, "KItem", "#KVariable")?;
    add_subsort(grammar, "#RuleBody", "K")?;

    grammar.add(
        Sort::new("K"),
        vec![ProductionItem::Terminal(".K".into())],
        Some(Label::new("#EmptyK")),
        false,
        false,
    )?;
    // KSEQ retains `.` as a deprecated spelling of the empty K sequence. K's
    // KSEQ declares it `unparseAvoid`, a spelling for parsing only, so both
    // spellings lower to the same KAST node and printers continue to emit the
    // canonical `.K` form.
    grammar.add(
        Sort::new("K"),
        vec![ProductionItem::Terminal(".".into())],
        Some(Label::new("#EmptyK")),
        false,
        false,
    )?;
    // Configuration initializers and rule bodies share the same concrete K-sequence syntax.
    // Keep it here so rule grammar construction does not install a duplicate production.
    grammar.add(
        Sort::new("K"),
        vec![
            nonterminal("K"),
            ProductionItem::Terminal("~>".into()),
            nonterminal("K"),
        ],
        Some(Label::new("#KSequence")),
        false,
        false,
    )?;
    // KSEQ declares left associativity; adding the opposite edge would make
    // a visible KSEQ declaration prohibit both associations.
    grammar.add_left_associative("#KSequence");
    grammar.add(
        Sort::new("Bag"),
        vec![ProductionItem::Terminal(".Bag".into())],
        Some(Label::new("#cells")),
        false,
        false,
    )?;
    add_casts(grammar, &CastTarget::kernel(KernelSort::Bag))?;
    add_casts(grammar, &CastTarget::kernel(KernelSort::K))?;
    add_casts(grammar, &CastTarget::kernel(KernelSort::KItem))?;
    add_casts(grammar, &CastTarget::kernel(KernelSort::KLabel))?;
    add_casts(grammar, &CastTarget::kernel(KernelSort::KList))?;
    for value in ["true", "false"] {
        grammar.add(
            Sort::new("Bool"),
            vec![ProductionItem::Terminal(value.into())],
            None,
            true,
            false,
        )?;
    }
    add_subsort(grammar, "Bool", "#KVariable")?;
    add_subsort(grammar, "Bool", "KConfigVar")?;
    add_casts(grammar, &CastTarget::kernel(KernelSort::Bool))?;
    grammar.add(
        Sort::new("#RuleContent"),
        vec![nonterminal("#RuleBody")],
        Some(Label::new("#ruleNoConditions")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("#RuleContent"),
        vec![
            nonterminal("#RuleBody"),
            ProductionItem::Terminal("requires".into()),
            nonterminal("Bool"),
        ],
        Some(Label::new("#ruleRequires")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("#RuleContent"),
        vec![
            nonterminal("#RuleBody"),
            ProductionItem::Terminal("ensures".into()),
            nonterminal("Bool"),
        ],
        Some(Label::new("#ruleEnsures")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("#RuleContent"),
        vec![
            nonterminal("#RuleBody"),
            ProductionItem::Terminal("requires".into()),
            nonterminal("Bool"),
            ProductionItem::Terminal("ensures".into()),
            nonterminal("Bool"),
        ],
        Some(Label::new("#ruleRequiresEnsures")),
        false,
        false,
    )
}

fn add_config_cells(grammar: &mut Grammar) -> Result<(), ParseError> {
    grammar.add(
        Sort::new("#CellProperty"),
        vec![
            nonterminal("#CellName"),
            ProductionItem::Terminal("=".into()),
            nonterminal("KString"),
        ],
        Some(Label::new("#cellProperty")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("#CellProperties"),
        vec![nonterminal("#CellProperty"), nonterminal("#CellProperties")],
        Some(Label::new("#cellPropertyList")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("#CellProperties"),
        Vec::new(),
        Some(Label::new("#cellPropertyListTerminator")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("Cell"),
        vec![
            ProductionItem::Terminal("<".into()),
            nonterminal("#CellName"),
            nonterminal("#CellProperties"),
            ProductionItem::Terminal(">".into()),
            nonterminal("K"),
            ProductionItem::Terminal("</".into()),
            nonterminal("#CellName"),
            ProductionItem::Terminal(">".into()),
        ],
        Some(Label::new("#configCell")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("Cell"),
        vec![
            ProductionItem::Terminal("<".into()),
            nonterminal("#CellName"),
            ProductionItem::Terminal("/>".into()),
        ],
        Some(Label::new("#externalCell")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("Bag"),
        vec![nonterminal("Cell"), nonterminal("Bag")],
        Some(Label::new("#cells")),
        false,
        false,
    )?;
    add_subsort(grammar, "Bag", "Cell")
}

/// `result ::= child` between two sorts of the fixed kernel syntax. The per-sort subsorts of a
/// grammar's members go through [`add_kitem_subsort`] and [`add_bottom_subsort`], which take a
/// [`GrammarSort`].
pub(super) fn add_subsort(
    grammar: &mut Grammar,
    result: &'static str,
    child: &'static str,
) -> Result<(), ParseError> {
    add_unary_subsort(grammar, Sort::new(result), Sort::new(child))
}

fn add_unary_subsort(grammar: &mut Grammar, result: Sort, child: Sort) -> Result<(), ParseError> {
    grammar.add(
        result,
        vec![ProductionItem::NonTerminal {
            sort: child,
            name: None,
        }],
        None,
        false,
        true,
    )
}

/// `KItem ::= S`: every term of the sort `S` is a `KItem`.
pub(super) fn add_kitem_subsort(
    grammar: &mut Grammar,
    sort: &GrammarSort,
) -> Result<(), ParseError> {
    add_unary_subsort(grammar, KernelSort::KItem.sort(), sort.sort().clone())
}

/// `S ::= child` for a kernel bottom `child` (`KBott`, `KConfigVar`, `#KVariable`), through which
/// a variable or a configuration variable stands at the sort. The result is the whole sort,
/// parameters included.
pub(super) fn add_bottom_subsort(
    grammar: &mut Grammar,
    sort: &GrammarSort,
    child: &'static str,
) -> Result<(), ParseError> {
    add_unary_subsort(grammar, sort.sort().clone(), Sort::new(child))
}

/// `S ::= "(" S ")"`, carrying the priority contract of `default`, the implicit K-sequence
/// bracket, when the grammar has one.
pub(super) fn add_sort_bracket(
    grammar: &mut Grammar,
    sort: &GrammarSort,
    default: Option<&Attributes>,
) -> Result<(), ParseError> {
    grammar.add_bracket(
        sort.sort().clone(),
        vec![
            ProductionItem::Terminal("(".into()),
            ProductionItem::NonTerminal {
                sort: sort.sort().clone(),
                name: None,
            },
            ProductionItem::Terminal(")".into()),
        ],
        default,
    )
}

/// The casts of every synonym of `universe`, when the grammar's `plan` has them.
pub(super) fn add_synonym_casts(
    grammar: &mut Grammar,
    universe: &SortUniverse,
    plan: &GrammarPlan,
) -> Result<(), ParseError> {
    if plan.synonym_casts {
        for target in universe.synonym_casts() {
            add_casts(grammar, &target)?;
        }
    }
    Ok(())
}

/// The syntactic casts and the semantic cast of `target`, and the projection cast when its label
/// sort has a sort projection: `S ::= L "::S"`, `S ::= "{" L "}" "::S"`, `L ::= L ":S"` and
/// `L ::= "{" K "}" ":>S"`, with `S` its cast and `L` its label. The projection cast lowers to
/// `project:L`, so it is added only when [`CastTarget::projection_operand`] gives its operand
/// sort, which is exactly when compilation declares `project:L`.
pub(super) fn add_casts(grammar: &mut Grammar, target: &CastTarget) -> Result<(), ParseError> {
    let cast_sort = target.cast();
    let label_sort = target.label();
    grammar.add(
        cast_sort.clone(),
        vec![
            ProductionItem::NonTerminal {
                sort: label_sort.clone(),
                name: None,
            },
            ProductionItem::Terminal(format!("::{cast_sort}")),
        ],
        Some(Label::new("#SyntacticCast")),
        false,
        false,
    )?;
    grammar.add(
        cast_sort.clone(),
        vec![
            ProductionItem::Terminal("{".into()),
            ProductionItem::NonTerminal {
                sort: label_sort.clone(),
                name: None,
            },
            ProductionItem::Terminal("}".into()),
            ProductionItem::Terminal(format!("::{cast_sort}")),
        ],
        Some(Label::new("#SyntacticCastBraced")),
        false,
        false,
    )?;
    let semantic_cast_items = vec![
        ProductionItem::NonTerminal {
            sort: label_sort.clone(),
            name: None,
        },
        ProductionItem::Terminal(format!(":{cast_sort}")),
    ];
    if *label_sort == Sort::new("K") && *cast_sort == Sort::new("K") {
        grammar.add_with_source_text(
            label_sort.clone(),
            semantic_cast_items,
            Some(Label::new("#SemanticCastToK")),
            false,
            false,
            "syntax K ::= K \":K\" [format(%1%2), org.kframework.kore.Sort(K)]",
        )?;
    } else {
        grammar.add(
            label_sort.clone(),
            semantic_cast_items,
            Some(Label::semantic_cast(label_sort)),
            false,
            false,
        )?;
    }
    if let Some(operand) = target.projection_operand() {
        grammar.add(
            label_sort.clone(),
            vec![
                ProductionItem::Terminal("{".into()),
                ProductionItem::NonTerminal {
                    sort: operand,
                    name: None,
                },
                ProductionItem::Terminal("}".into()),
                ProductionItem::Terminal(format!(":>{cast_sort}")),
            ],
            Some(Label::new("#OuterCast")),
            false,
            false,
        )?;
    }
    Ok(())
}

pub(super) fn nonterminal(sort: &str) -> ProductionItem {
    ProductionItem::NonTerminal {
        sort: Sort::new(sort),
        name: None,
    }
}

pub(super) fn truth() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn regex(regex: &str) -> String {
        format!("r{regex:?}")
    }

    fn load_with_prelude(
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

    #[test]
    fn a_declared_numeral_receives_no_configuration_grammar_production() {
        let source = r#"module MAIN
  syntax 8
  configuration <k> $PGM:8 </k>
endmodule
"#;
        let error = load_with_prelude(source).expect_err("a width has no configuration position");
        assert!(
            error.to_string().contains("could not parse configuration"),
            "{error}"
        );
    }

    /// The configuration grammar of MAIN in `source`, loaded with the prelude.
    fn main_configuration_grammar(source: &str) -> Grammar {
        let loaded =
            load_with_prelude(source).unwrap_or_else(|error| panic!("MAIN loads: {error}"));
        let resolved = loaded.resolved();
        let module = resolved.module_id("MAIN").expect("MAIN is resolved");
        configuration_grammar(resolved, module).expect("the configuration grammar builds")
    }

    /// A user sort is a sort of K items, so `syntax Exp ::= KItem` closes `Exp < KItem < Exp`
    /// with the kernel position the configuration grammar gives `Exp`. Built without the load,
    /// which would report the declaration first, the configuration grammar rejects the view with
    /// that cycle before it generates any production.
    #[test]
    fn a_view_contradicting_a_kernel_position_has_no_configuration_grammar() {
        let source = "module MAIN\n  syntax KItem\n  syntax Exp ::= \"a\"\n  syntax Exp ::= KItem\nendmodule\n";
        let parsed = crate::outer::parse("main.k", source).expect("MAIN parses");
        let definition = crate::outer::lower(&parsed, "MAIN").expect("MAIN lowers");
        let resolved = ResolvedDefinition::resolve(&definition).expect("MAIN resolves");
        match configuration_grammar(&resolved, resolved.main_module_id()) {
            Err(ParseError::CircularSubsorts { path }) => {
                assert!(path.contains(&Sort::new("Exp")), "{path:?}");
                assert!(path.contains(&KernelSort::KItem.sort()), "{path:?}");
            }
            Err(error) => panic!("expected the kernel-position cycle, got {error}"),
            Ok(_) => panic!("the configuration grammar of a contradicting view was built"),
        }
    }

    fn unary(child: &str) -> [ProductionItem; 1] {
        [nonterminal(child)]
    }

    /// 86a21b90 in the configuration grammar: the parameters `Sort`, `Sort1` and `Sort2` of the
    /// ML productions are bound by each production alone, so they are not sorts of the module and
    /// no production of the grammar has one as its result or as a nonterminal item. A sort the
    /// grammar has no id for occurs in no production, since every production's result and items
    /// are interned when it is added.
    #[test]
    fn the_configuration_grammar_has_no_production_at_a_sort_parameter_of_the_ml_productions() {
        let source = r#"
module MAIN
  imports ML-SYNTAX
  syntax Foo ::= "foo"
endmodule
"#;
        let loaded =
            load_with_prelude(source).unwrap_or_else(|error| panic!("MAIN loads: {error}"));
        let resolved = loaded.resolved();
        let module = resolved.module_id("MAIN").expect("MAIN is resolved");
        let mut visible = resolved.signature_sentences(module);
        add_implicit_ml_syntax(resolved, &mut visible);
        for parameter in ["Sort", "Sort1", "Sort2"] {
            assert!(
                visible.iter().any(|sentence| matches!(sentence,
                    Sentence::Production { parameters, .. }
                        if parameters.iter().any(|bound| bound.name == parameter))),
                "an ML production binding {parameter} is visible"
            );
        }

        let grammar = configuration_grammar(resolved, module).expect("the grammar builds");

        for parameter in ["Sort", "Sort1", "Sort2"] {
            assert_eq!(
                grammar.sort_id(&Sort::new(parameter)),
                None,
                "a production of the configuration grammar mentions {parameter}"
            );
        }
        // Control: the declared sort receives its per-sort productions.
        assert!(grammar.has_equivalent_production(&Sort::new("Foo"), &unary("KConfigVar"), false));
        assert!(grammar.has_equivalent_production(&Sort::new("KItem"), &unary("Foo"), false));
    }

    /// F9: the bottom subsorts of a declared instance have the whole sort as their result, so a
    /// configuration variable and a variable stand at `MInt{8}`; the bare head `MInt` is not a
    /// sort and receives no production.
    #[test]
    fn the_configuration_grammar_gives_a_declared_instance_its_variable_subsorts() {
        let grammar = main_configuration_grammar(
            r#"
module MAIN
  syntax MInt{8}
  syntax Foo ::= foo(MInt{8})
endmodule
"#,
        );
        let instance = Sort::with_parameters("MInt", vec![Sort::new("8")]);

        for child in ["KConfigVar", "#KVariable"] {
            assert!(
                grammar.has_equivalent_production(&instance, &unary(child), false),
                "MInt{{8}} ::= {child}"
            );
            assert!(
                !grammar.has_equivalent_production(&Sort::new("MInt"), &unary(child), false),
                "MInt ::= {child}"
            );
        }
        assert!(grammar.has_equivalent_production(
            &Sort::new("KItem"),
            &[ProductionItem::NonTerminal {
                sort: instance,
                name: None,
            }],
            false
        ));
        assert_eq!(grammar.sort_id(&Sort::new("MInt")), None);
    }

    /// A view that sees KAST declares `KLabel`, `KList` and `KString`, but a label, an argument
    /// sequence and a token spelling are not K items: the configuration grammar gives none of the
    /// three a `KItem` subsort, which for `KList` would close the cycle `KItem < K < KList < KItem`
    /// with the declared `KList ::= K` and `K ::= KItem`. A variable and a configuration variable
    /// still stand at each of them, and a defined sort keeps its `KItem` subsort.
    ///
    /// The module has no configuration, so the loader parses nothing with this grammar and the
    /// test reads the productions themselves; that a configuration of such a view parses is
    /// `a_configuration_of_a_view_that_sees_kast_parses` in `inner::rules`.
    #[test]
    fn the_configuration_grammar_places_no_kast_sort_below_kitem() {
        let grammar = main_configuration_grammar(
            r#"
module MAIN
  imports KAST
  syntax Foo ::= "foo"
endmodule
"#,
        );
        let kitem = Sort::new("KItem");

        for kast in ["KList", "KLabel", "KString"] {
            assert!(
                !grammar.has_equivalent_production(&kitem, &unary(kast), false),
                "KItem ::= {kast}"
            );
        }
        for child in ["KConfigVar", "#KVariable"] {
            assert!(
                grammar.has_equivalent_production(&Sort::new("KList"), &unary(child), false),
                "KList ::= {child}"
            );
        }
        assert!(grammar.has_equivalent_production(&kitem, &unary("Foo"), false));
    }

    /// A definition whose operand sort no module declares is rejected by the sort check, which
    /// runs on every module before any configuration is parsed; the configuration grammar is
    /// never built for it.
    #[test]
    fn an_undeclared_operand_sort_of_a_configuration_is_reported_by_the_sort_check() {
        let source = r#"
module MAIN
  syntax Foo ::= f(Bar)
  configuration <k> f($PGM) </k>
endmodule
"#;
        let error = match load_with_prelude(source) {
            Ok(_) => panic!("MAIN uses the undeclared sort Bar and must not load"),
            Err(error) => error,
        };
        let crate::outer::LoadError::SourceDiagnostics(diagnostics) = &error else {
            panic!("expected the sort check's diagnostics, got {error}");
        };
        assert!(
            diagnostics.iter().any(|diagnostic| diagnostic.code
                == crate::diagnostic::DiagnosticCode::UndefinedSort
                && diagnostic.message == "Could not find sorts: [Bar]"),
            "{diagnostics:?}"
        );
    }

    /// A visible production's operand sort whose declaration the configuration module cannot
    /// see (FOO imports BAR privately) is still a position of that production, so a
    /// configuration variable must be able to stand there: the sort receives its variable
    /// subsorts and the configuration `f($PGM)` parses.
    #[test]
    fn an_operand_sort_declared_behind_a_private_import_receives_its_variable_subsorts() {
        let source = r#"
module BAR
  syntax Bar ::= "b"
endmodule

module FOO
  imports private BAR
  syntax Foo ::= f(Bar)
endmodule

module MAIN
  imports FOO
  configuration <k> f($PGM) </k>
endmodule
"#;
        let loaded =
            load_with_prelude(source).unwrap_or_else(|error| panic!("MAIN loads: {error}"));
        let resolved = loaded.resolved();
        let module = resolved.module_id("MAIN").expect("MAIN is resolved");
        let bar = Sort::new("Bar");
        // The shape under test: no sentence visible to MAIN declares Bar.
        let visible = resolved.signature_sentences(module);
        assert!(
            !crate::definition::SortCatalog::from_visible(visible.iter().copied())
                .all_sorts()
                .contains(&bar),
            "Bar is declared by a sentence visible to MAIN"
        );

        let grammar = configuration_grammar(resolved, module).expect("the grammar builds");

        for child in ["KConfigVar", "#KVariable"] {
            assert!(
                grammar.has_equivalent_production(&bar, &unary(child), false),
                "Bar ::= {child}"
            );
        }
    }

    #[test]
    fn scanner_winner_table_matches_scanner_get_tokens() {
        for precedence in 0..=3 {
            let mut grammar = Grammar::default();
            add_k_syntax(&mut grammar, BuiltinTokenGrammar::Rule).unwrap();
            grammar
                .add_token_with_precedence(
                    Sort::new("Id"),
                    ProductionItem::regex(r"[A-Za-z_][A-Za-z_0-9]*"),
                    &precedence.to_string(),
                )
                .unwrap();

            let user_id = r"[A-Za-z_][A-Za-z_0-9]*";
            assert_eq!(
                grammar.scanner().winner_description("foo"),
                Some(regex(if precedence < 2 {
                    r"[a-z][a-zA-Z0-9]*"
                } else {
                    user_id
                }))
            );
            assert_eq!(
                grammar.scanner().winner_description("Foo"),
                Some(regex(if precedence < 3 {
                    r"[A-Z][a-zA-Z0-9]*"
                } else {
                    user_id
                }))
            );
            assert_eq!(
                grammar.scanner().winner_description("foo_bar"),
                Some(regex(user_id))
            );
            assert_eq!(
                grammar.scanner().winner_description("X'"),
                Some(regex(
                    r"(\!|\?|@)?([A-Z][A-Za-z0-9'_]*|_|_[A-Z][A-Za-z0-9'_]*)"
                ))
            );
            assert_eq!(
                grammar.scanner().winner_description("`foo`"),
                Some(regex(r"`(\\`|\\\\|[^`\\\n\r])+`"))
            );
            assert_eq!(
                grammar.scanner().winner_description("#foo"),
                Some(regex(r"[#a-z][a-zA-Z0-9]*"))
            );
            assert_eq!(
                grammar.scanner().winner_description("$PGM"),
                Some(regex(r"(\$)([A-Z][A-Za-z0-9'_]*)"))
            );
            assert_eq!(
                grammar.scanner().winner_description("_"),
                Some(regex(if precedence < 2 {
                    r"(\!|\?|@)?([A-Z][A-Za-z0-9'_]*|_|_[A-Z][A-Za-z0-9'_]*)"
                } else {
                    user_id
                }))
            );
        }
    }

    #[test]
    fn builtin_lexemes_declared_by_the_definition_are_not_registered_twice() {
        let mut attributes = Attributes::default();
        attributes.insert("token", serde_json::json!(""));
        attributes.insert("prec", serde_json::json!("2"));
        let sentences = [Sentence::Production {
            label: None,
            parameters: Vec::new(),
            sort: Sort::new("#UpperId"),
            items: vec![ProductionItem::regex(r"[A-Z][a-zA-Z0-9]*")],
            attributes,
        }];
        let mut grammar = Grammar::from_sentences(&sentences).unwrap();

        add_k_syntax(&mut grammar, BuiltinTokenGrammar::Rule).unwrap();

        assert_eq!(
            grammar.equivalent_production_count(
                &Sort::new("#UpperId"),
                &[ProductionItem::regex(r"[A-Z][a-zA-Z0-9]*")],
                true,
            ),
            1
        );
    }

    #[test]
    fn builtin_lexemes_declared_with_another_precedence_are_rejected() {
        let mut attributes = Attributes::default();
        attributes.insert("token", serde_json::json!(""));
        attributes.insert("prec", serde_json::json!("1"));
        let sentences = [Sentence::Production {
            label: None,
            parameters: Vec::new(),
            sort: Sort::new("#UpperId"),
            items: vec![ProductionItem::regex(r"[A-Z][a-zA-Z0-9]*")],
            attributes,
        }];
        let mut grammar = Grammar::from_sentences(&sentences).unwrap();

        assert!(matches!(
            add_builtin_tokens(&mut grammar, BuiltinTokenGrammar::Rule),
            Err(ParseError::InconsistentTokenPrecedence { .. })
        ));
    }
}
