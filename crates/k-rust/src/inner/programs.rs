//! ```toml algorithm
//! id = "parser.programs.parse"
//! name = "user-program parsing with a cached grammar"
//! sites = ["ProgramParser::parse", "ProgramParser::parse_with_provenance", "ProgramParser::present", "ProgramParser::parse_for_presentation", "parse_program"]
//! variable = "g = grammar construction work; p = parse work"
//! counters = ["ParserGrammarBuilds", "ParserParseAttempts"]
//! produces = [{ type = "k_rust::inner::ParsedProgram", role = "parsed program" }]
//! constrains = [
//!   { id = "definition.catalog.production", site = "ProgramParser::parse", via = "the per-module ProductionCatalog that ProgramParser::from_resolved reads from ResolvedDefinition::production_catalog" },
//! ]
//!
//! [[cost]]
//! mode = "one parser and its parses"
//! bound = "O(g + sum p)"
//! ```
//!
//! ```toml algorithm
//! id = "parser.grammar.program_signature"
//! name = "collection of public program-grammar signatures"
//! sites = ["collect_public_signature", "prepared_program_sentences"]
//! variable = "M = reachable modules and imports; S = visible sentences"
//! counters = []
//! no_counter = "public-signature collection has no dedicated counter"
//!
//! [[cost]]
//! mode = "one program grammar"
//! bound = "O(M x S) EquivalenceAccumulator insertions"
//! ```
//!
//! User-program parsing with a cached module-derived concrete-syntax grammar.
//!
//! A `ProgramParser` builds one grammar, then each parse uses the Earley pipeline. Public syntax
//! collection is a visited-set DFS that rebuilds its equivalence accumulator over the collected
//! sentences for each visited module, O(modules * visible sentences); parse work is measured by
//! the parser counter family.

use std::collections::BTreeSet;
use std::fmt;
use std::sync::Arc;

use crate::definition::AttributeKey;
use crate::definition::{
    Attributes, Definition, EquivalenceAccumulator, ModuleId, ProductionItem, ResolveError,
    ResolvedDefinition, Sentence, SortCatalog, push_if_inequivalent,
};
use crate::kast::json as kast_json;
use crate::kast::names::PROGRAM_PARSING_POSTFIX;
use crate::kast::printer::Printer;
use crate::kast::{ProductionIdentity, Sort, Term};
use crate::provenance::SourceId;

use super::parser::{Grammar, ParseError, named_projection_productions};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProgramError {
    Definition(ResolveError),
    MissingModule(String),
    Grammar {
        module: String,
        error: Box<ParseError>,
    },
    Parse(ProgramParseError),
}

impl fmt::Display for ProgramError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Definition(error) => error.fmt(formatter),
            Self::MissingModule(module) => {
                write!(formatter, "program syntax module {module:?} was not found")
            }
            Self::Grammar { module, error } => {
                write!(
                    formatter,
                    "could not build program grammar for module {module:?}: {error}"
                )
            }
            Self::Parse(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for ProgramError {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgramParseError {
    pub module: String,
    pub start_sort: Sort,
    pub error: Box<ParseError>,
}

impl fmt::Display for ProgramParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "could not parse program as {} with module {:?}: {}",
            self.start_sort, self.module, self.error
        )
    }
}

impl std::error::Error for ProgramParseError {}

/// A program or configuration value as the program parser produced it: sort inference has
/// instantiated parametric productions, so labels carry inferred sort arguments, and macro
/// applications are as parsed.
///
/// It is neither user-facing KAST nor an executable input: [`ProgramParser::present`] produces
/// the first, and macro expansion in the executable module the second. The typed term is
/// reachable only through [`Self::typed_term`], which is for inspection, so a printer or a
/// converter cannot receive it by accident:
///
/// ```compile_fail,E0308
/// # use k_rust::{inner::ProgramParser, kast::{Sort, printer::Printer}};
/// # fn show(parser: &ProgramParser) -> Result<String, Box<dyn std::error::Error>> {
/// let parsed = parser.parse(&Sort::new("Pgm"), "p")?;
/// Ok(Printer::new().print_term(&parsed)) // 7c31c79d, b7fd8629
/// # }
/// ```
///
/// User-facing KAST prints the presentation of the parse:
///
/// ```
/// # use k_rust::{inner::ProgramParser, kast::{Sort, printer::Printer}};
/// # fn show(parser: &ProgramParser) -> Result<String, Box<dyn std::error::Error>> {
/// let presented = parser.parse_for_presentation(&Sort::new("Pgm"), "p")?;
/// assert_eq!(presented.to_kast_text(), Printer::new().print_term(presented.term()));
/// Ok(presented.to_kast_text())
/// # }
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
#[must_use]
pub struct ParsedProgram(Term);

impl ParsedProgram {
    /// A program term built without the parser, at the parser's stage.
    pub fn from_term(term: Term) -> Self {
        Self(term)
    }

    /// The typed parser term, for inspection only.
    ///
    /// It is neither a presentation nor an executable input; see [`ParsedProgram`].
    #[must_use]
    pub fn typed_term(&self) -> &Term {
        &self.0
    }

    /// The typed parser term, handed to macro expansion by the initial-configuration assembler.
    pub(crate) fn into_typed_term(self) -> Term {
        self.0
    }
}

/// A program as user-facing KAST shows it: the parsed term with every inferred production sort
/// argument removed from its labels, and macro applications as parsed.
///
/// Only [`ProgramParser::present`] produces one, from the parser's own catalog.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PresentedProgram(Term);

impl PresentedProgram {
    /// The presented term.
    #[must_use]
    pub fn term(&self) -> &Term {
        &self.0
    }

    /// The presented term as textual KAST.
    #[must_use]
    pub fn to_kast_text(&self) -> String {
        Printer::new().print_term(&self.0)
    }

    /// The presented term as compact KAST JSON.
    pub fn to_kast_json(&self) -> Result<String, kast_json::Error> {
        kast_json::to_string(&self.0)
    }

    /// The presented term as indented KAST JSON.
    pub fn to_kast_json_pretty(&self) -> Result<String, kast_json::Error> {
        kast_json::to_string_pretty(&self.0)
    }
}

/// A reusable parser for the concrete program syntax visible from one module.
#[derive(Clone, Debug)]
pub struct ProgramParser {
    module: String,
    grammar: Grammar,
    /// The identities of the parametric productions of the catalog the grammar was built from:
    /// a label a parse builds from one of them carries sort arguments that inference supplied.
    parametric_productions: BTreeSet<ProductionIdentity>,
}

impl ProgramParser {
    pub fn new(definition: &Definition, module: &str) -> Result<Self, ProgramError> {
        let resolved = ResolvedDefinition::resolve(definition).map_err(ProgramError::Definition)?;
        Self::from_resolved(&resolved, module)
    }

    pub fn from_resolved(
        definition: &ResolvedDefinition,
        module: &str,
    ) -> Result<Self, ProgramError> {
        let module_id = definition
            .module_id(module)
            .ok_or_else(|| ProgramError::MissingModule(module.to_owned()))?;
        let sentences = prepared_program_sentences(definition, module_id);
        let source_catalog = definition.production_catalog(module_id);
        let grammar =
            Grammar::from_program_sentences(&sentences, &source_catalog).map_err(|error| {
                ProgramError::Grammar {
                    module: module.to_owned(),
                    error: Box::new(error),
                }
            })?;
        let parametric_productions = source_catalog
            .productions()
            .filter(|(_, production)| {
                matches!(
                    production,
                    Sentence::Production { parameters, .. } if !parameters.is_empty()
                )
            })
            .map(|(id, _)| source_catalog.identity(id))
            .collect();
        Ok(Self {
            module: module.to_owned(),
            grammar,
            parametric_productions,
        })
    }

    pub fn module(&self) -> &str {
        &self.module
    }

    /// Parse a program without claiming that it belongs to a known logical source.
    ///
    /// Production and sort metadata remain available, but source spans are omitted.
    /// Use [`Self::parse_with_provenance`] when the caller owns a [`SourceId`].
    pub fn parse(
        &self,
        start_sort: &Sort,
        source: &str,
    ) -> Result<ParsedProgram, ProgramParseError> {
        self.grammar
            .parse(start_sort, source)
            .map(|term| ParsedProgram(without_source_spans(term)))
            .map_err(|error| ProgramParseError {
                module: self.module.clone(),
                start_sort: start_sort.clone(),
                error: Box::new(error),
            })
    }

    /// Parse a program whose byte zero belongs to `source_id`.
    pub fn parse_with_provenance(
        &self,
        start_sort: &Sort,
        source: &str,
        source_id: SourceId,
    ) -> Result<ParsedProgram, ProgramParseError> {
        self.grammar
            .parse_with_provenance(start_sort, source, source_id, 0)
            .map(ParsedProgram)
            .map_err(|error| ProgramParseError {
                module: self.module.clone(),
                start_sort: start_sort.clone(),
                error: Box::new(error),
            })
    }

    /// Present a parse as user-facing KAST: remove from its labels the sort arguments that
    /// inference supplied for this parser's parametric productions.
    pub fn present(&self, program: ParsedProgram) -> PresentedProgram {
        PresentedProgram(strip_inferred_parameters(
            program.0,
            &self.parametric_productions,
        ))
    }

    /// Parse a program for user-facing KAST; see [`Self::present`].
    pub fn parse_for_presentation(
        &self,
        start_sort: &Sort,
        source: &str,
    ) -> Result<PresentedProgram, ProgramParseError> {
        self.parse(start_sort, source)
            .map(|program| self.present(program))
    }
}

/// Build the program grammar sentence set shared by the in-process parser and generated parsers.
///
/// Keeping this boundary in one place prevents standalone parser generation from drifting from
/// the import substitution, named projection, and KItem subsort rules used by [`ProgramParser`].
pub(crate) fn prepared_program_sentences(
    definition: &ResolvedDefinition,
    module: ModuleId,
) -> Vec<Sentence> {
    prepared_program_sentences_with(definition, module, false)
}

/// Build the standalone Bison grammar after removing sentences declared by `not-lr1` modules.
///
/// K applies this module filter before it concretizes parametric productions. In particular,
/// excluding `ML-SYNTAX` prevents its generic logical productions from being instantiated at
/// every user sort and turning a two-sort program grammar into a large IELR automaton.
#[cfg(any(feature = "cli", test))]
pub(crate) fn prepared_bison_program_sentences(
    definition: &ResolvedDefinition,
    module: ModuleId,
) -> Vec<Sentence> {
    prepared_program_sentences_with(definition, module, true)
}

fn prepared_program_sentences_with(
    definition: &ResolvedDefinition,
    module: ModuleId,
    exclude_not_lr1: bool,
) -> Vec<Sentence> {
    let mut sentences = program_sentences(definition, module, exclude_not_lr1);
    sentences.extend(named_projection_productions(&sentences));
    with_kitem_subsorts(sentences)
}

/// The definition against which a parsed program is converted: every module gains the
/// named-field projection productions of its own productions, as the parsing grammars declare
/// them (`named_projection_productions`), so that the projection applied by a program has a
/// production, a signature and a KORE symbol before the kompile pass adds its rules. The
/// compiled definition already carries the same productions from `generate_sort_projections`.
pub fn definition_with_named_projections(definition: &Definition) -> Definition {
    let mut output = definition.clone();
    for module in &mut output.modules {
        let generated =
            named_projection_productions(module.local_sentences.iter().map(Arc::as_ref));
        module
            .local_sentences
            .extend(generated.into_iter().map(Arc::new));
    }
    output
}

fn without_source_spans(term: Term) -> Term {
    match term {
        Term::Annotated { term, mut metadata } => {
            metadata.span = None;
            without_source_spans(*term).with_metadata(metadata)
        }
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(without_source_spans(*left)),
            right: Box::new(without_source_spans(*right)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(without_source_spans(*pattern)),
            alias: Box::new(without_source_spans(*alias)),
        },
        Term::Sequence(items) => {
            Term::Sequence(items.into_iter().map(without_source_spans).collect())
        }
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments.into_iter().map(without_source_spans).collect(),
        },
        term @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => term,
    }
}

/// Parse one program using the concrete syntax visible from `module`.
pub fn parse_program(
    definition: &Definition,
    module: &str,
    start_sort: &Sort,
    source: &str,
    source_id: SourceId,
) -> Result<ParsedProgram, ProgramError> {
    let parser = ProgramParser::new(definition, module)?;
    parser
        .parse_with_provenance(start_sort, source, source_id)
        .map_err(ProgramError::Parse)
}

fn program_sentences(
    definition: &ResolvedDefinition,
    module: ModuleId,
    exclude_not_lr1: bool,
) -> Vec<Sentence> {
    let substitute_imports = !definition
        .module(module)
        .name
        .ends_with(PROGRAM_PARSING_POSTFIX);

    let mut visited = BTreeSet::new();
    let mut sentences = Vec::new();
    for import in definition.direct_imports(module) {
        let (imported, substituted) = if substitute_imports {
            program_import(definition, import.module)
        } else {
            (import.module, false)
        };
        collect_public_signature(
            definition,
            imported,
            substitute_imports && !substituted,
            exclude_not_lr1,
            &mut visited,
            &mut sentences,
        );
    }
    if !exclude_not_lr1
        || definition
            .module(module)
            .attributes
            .value(AttributeKey::NotLr1)
            .is_none()
    {
        append_unique(
            &mut sentences,
            definition
                .module(module)
                .local_sentences
                .iter()
                .map(std::sync::Arc::as_ref),
        );
    }
    sentences
}

/// `PROGRAM-LISTS` extends a program grammar with `KItem ::= S` for every
/// non-parser, non-list sort in the syntax-module signature. These productions
/// participate in both parsing and sort inference and lower transparently.
fn with_kitem_subsorts(mut sentences: Vec<Sentence>) -> Vec<Sentence> {
    let sorts = {
        let catalog = SortCatalog::from_visible(sentences.iter());
        catalog
            .all_sorts()
            .iter()
            .filter(|sort| {
                sort.role().has_implicit_kitem_subsort() && !catalog.list_sorts().contains(sort)
            })
            .cloned()
            .collect::<Vec<_>>()
    };
    let mut generated = Attributes::default();
    generated.mark(AttributeKey::GeneratedRuleSyntax);
    for sort in sorts {
        sentences.push(Sentence::Production {
            label: None,
            parameters: Vec::new(),
            sort: Sort::new("KItem"),
            items: vec![ProductionItem::NonTerminal { sort, name: None }],
            attributes: generated.clone(),
        });
    }
    sentences
}

fn collect_public_signature(
    definition: &ResolvedDefinition,
    module: ModuleId,
    substitute_imports: bool,
    exclude_not_lr1: bool,
    visited: &mut BTreeSet<(ModuleId, bool)>,
    sentences: &mut Vec<Sentence>,
) {
    // Invariant: `visited` contains expanded `(module, substitution)` states; recursion follows
    // one public import and appends only first-equivalent sentences.
    if !visited.insert((module, substitute_imports)) {
        return;
    }
    for import in definition
        .direct_imports(module)
        .into_iter()
        .filter(|import| import.public)
    {
        let (imported, substituted) = if substitute_imports {
            program_import(definition, import.module)
        } else {
            (import.module, false)
        };
        collect_public_signature(
            definition,
            imported,
            substitute_imports && !substituted,
            exclude_not_lr1,
            visited,
            sentences,
        );
    }
    if !exclude_not_lr1
        || definition
            .module(module)
            .attributes
            .value(AttributeKey::NotLr1)
            .is_none()
    {
        append_unique(sentences, definition.public_sentences(module));
    }
}

fn program_import(definition: &ResolvedDefinition, module: ModuleId) -> (ModuleId, bool) {
    let imported_name = &definition.module(module).name;
    let companion_name = format!("{imported_name}{PROGRAM_PARSING_POSTFIX}");
    definition
        .module_id(&companion_name)
        .map_or((module, false), |companion| (companion, true))
}

fn append_unique<'a>(
    sentences: &mut Vec<Sentence>,
    incoming: impl IntoIterator<Item = &'a Sentence>,
) {
    let mut seen = EquivalenceAccumulator::from_sentences(sentences.iter());
    let accepted = incoming
        .into_iter()
        .filter(|sentence| push_if_inequivalent(&mut seen, sentence))
        .cloned()
        .collect::<Vec<_>>();
    sentences.extend(accepted);
}

/// Remove, from every label of `term` built by one of `parametric_productions`, the sort
/// arguments that sort inference supplied.
///
/// A user-facing KAST term describes the parse of the user's text. That text wrote no sort
/// argument for a parametric production: inference instantiated the production's parameters to
/// type the term, so the arguments are facts of the typed term, not of the text. Labels of
/// non-parametric productions, labels without production metadata, and every other node are kept.
fn strip_inferred_parameters(
    term: Term,
    parametric_productions: &BTreeSet<ProductionIdentity>,
) -> Term {
    let metadata = term.metadata().cloned();
    let inferred_production_parameters = metadata
        .as_ref()
        .and_then(|metadata| metadata.production)
        .is_some_and(|production| parametric_productions.contains(&production));
    let rebuilt = match term.into_unannotated() {
        Term::Apply {
            mut label,
            arguments,
        } => {
            if inferred_production_parameters {
                label.parameters.clear();
            }
            Term::Apply {
                label,
                arguments: arguments
                    .into_iter()
                    .map(|argument| strip_inferred_parameters(argument, parametric_productions))
                    .collect(),
            }
        }
        Term::InjectedLabel(mut label) => {
            if inferred_production_parameters {
                label.parameters.clear();
            }
            Term::InjectedLabel(label)
        }
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(strip_inferred_parameters(*left, parametric_productions)),
            right: Box::new(strip_inferred_parameters(*right, parametric_productions)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(strip_inferred_parameters(*pattern, parametric_productions)),
            alias: Box::new(strip_inferred_parameters(*alias, parametric_productions)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| strip_inferred_parameters(item, parametric_productions))
                .collect(),
        ),
        leaf @ (Term::Variable { .. } | Term::Token { .. }) => leaf,
        Term::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
    };
    match metadata {
        Some(metadata) => rebuilt.with_metadata(metadata),
        None => rebuilt,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bison_preparation_excludes_not_lr1_module_sentences_before_concretization() {
        let parsed = crate::outer::parse(
            "not-lr1.k",
            r#"
module GENERIC-LOGIC [not-lr1]
  syntax {S} S ::= S "blocked" S [symbol(blocked)]
endmodule

module PROGRAM
  imports GENERIC-LOGIC
  syntax Pgm ::= "ok" [symbol(ok)]
endmodule
"#,
        )
        .unwrap();
        let definition = crate::outer::lower(&parsed, "PROGRAM").unwrap();
        let resolved = ResolvedDefinition::resolve(&definition).unwrap();
        let module = resolved.module_id("PROGRAM").unwrap();
        let contains_blocked = |sentences: &[Sentence]| {
            sentences.iter().any(|sentence| {
                matches!(sentence, Sentence::Production { items, .. }
                    if items.iter().any(|item| matches!(item, ProductionItem::Terminal(value) if value == "blocked")))
            })
        };

        assert!(contains_blocked(&prepared_program_sentences(
            &resolved, module
        )));
        assert!(!contains_blocked(&prepared_bison_program_sentences(
            &resolved, module
        )));
    }
}
