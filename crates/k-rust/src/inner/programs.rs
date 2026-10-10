//! ```toml algorithm
//! id = "parser.programs.parse"
//! name = "user-program parsing with a cached grammar"
//! sites = ["ProgramParser::parse", "ProgramParser::parse_with_provenance",
//!     "ProgramParser::present", "ProgramParser::parse_for_presentation", "parse_program"]
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
//! variable = "M = reachable modules and imports; S = visible syntax declarations"
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

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use crate::definition::{AttributeKey, Location};
use crate::definition::{
    Attributes, Definition, EquivalenceAccumulator, ModuleId, ProductionCatalog, ProductionItem,
    ResolveError, ResolvedDefinition, Sentence, SortCatalog, SortHead, SortSynonyms,
    push_if_inequivalent,
};
use crate::kast::json as kast_json;
use crate::kast::names::PROGRAM_PARSING_POSTFIX;
use crate::kast::printer::Printer;
use crate::kast::{Label, ProductionIdentity, Sort, Term, TermParts};
use crate::names::{BuiltinSort, WellKnownSymbol};
use crate::provenance::SourceId;

use super::location::{TextPositions, locate_ambiguity_places_in_text};
use super::parser::{DiagnosticWork, Grammar, ParseError, named_projection_productions};

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
    /// The failed item reading when a configuration value subsequently failed at K.
    pub item_attempt: Option<Box<ProgramParseError>>,
}

impl fmt::Display for ProgramParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(item_attempt) = &self.item_attempt {
            write!(
                formatter,
                "could not parse configuration value declared K: item attempt: {item_attempt}; K attempt: "
            )?;
        }
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
/// Macro expansion discards the parser's parametric instances and infers each application's
/// instance from the current value at its supplied position, which the expanded value carries
/// into sort injection.
///
/// It is neither user-facing KAST nor an executable input: [`ProgramParser::present`] produces
/// the first and [`MacroExpansionDefinition::expand_program`] the second. The typed term is
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
///
/// [`MacroExpansionDefinition::expand_program`]:
///     crate::kompile::MacroExpansionDefinition::expand_program
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

    /// The typed parser term, handed to macro expansion by
    /// [`crate::kompile::MacroExpansionDefinition::expand_program`].
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
    /// What locating a parse needs; `None` when no sort of the grammar declares `[locations]`.
    locations: Option<Locations>,
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
        let grammar = Grammar::from_program_sentences(
            &sentences,
            &source_catalog,
            SortSynonyms::of_module(definition, module_id)
                .denotations()
                .clone(),
        )
        .map_err(|error| ProgramError::Grammar {
            module: module.to_owned(),
            error: Box::new(error),
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
        let locations = Locations::of(&sentences, &source_catalog);
        Ok(Self {
            module: module.to_owned(),
            grammar,
            parametric_productions,
            locations,
        })
    }

    pub fn module(&self) -> &str {
        &self.module
    }

    /// The sort a start spelling denotes in this parser's module's full view.
    pub fn start_sort<'s>(&'s self, spelling: &'s Sort) -> &'s Sort {
        self.grammar.start_sort(spelling)
    }

    /// Parse a program read from no file (standard input, or text given as an argument), without
    /// claiming that it belongs to a known logical source: [`Self::parse_file`] with the file name
    /// [`UNNAMED_PROGRAM`].
    ///
    /// Production and sort metadata remain available, but source spans are omitted.
    /// Use [`Self::parse_with_provenance`] when the caller owns a [`SourceId`].
    pub fn parse(
        &self,
        start_sort: &Sort,
        source: &str,
    ) -> Result<ParsedProgram, ProgramParseError> {
        self.parse_file(start_sort, source, UNNAMED_PROGRAM)
    }

    /// Parse a program read from the file `file`, the name the `#location` wrappers of its
    /// `[locations]` sorts carry (see [`Locations`]).
    pub fn parse_file(
        &self,
        start_sort: &Sort,
        source: &str,
        file: &str,
    ) -> Result<ParsedProgram, ProgramParseError> {
        self.parse_within(start_sort, source, file, DiagnosticWork::from_environment())
    }

    /// `parse_file`, with the diagnostic of a failure limited to `diagnostic_work`.
    fn parse_within(
        &self,
        start_sort: &Sort,
        source: &str,
        file: &str,
        diagnostic_work: DiagnosticWork,
    ) -> Result<ParsedProgram, ProgramParseError> {
        self.grammar
            .parse_with_diagnostic_work(start_sort, source, diagnostic_work)
            .map(|term| {
                ParsedProgram(without_source_spans(
                    self.locate(start_sort, source, file, term),
                ))
            })
            .map_err(|error| self.parse_error(start_sort, source, error))
    }

    /// `term`, parsed from `source` at `start_sort`, with its `[locations]` sorts located in
    /// `file`.
    fn locate(&self, start_sort: &Sort, source: &str, file: &str, term: Term) -> Term {
        match &self.locations {
            Some(locations) => locations.locate(
                term,
                self.grammar.start_sort(start_sort),
                &ProgramText { source, file },
            ),
            None => term,
        }
    }

    /// The failure to parse `source` as `start_sort`: each subterm an ambiguity report names is
    /// located by line and column in `source`, the text the user wrote.
    fn parse_error(
        &self,
        start_sort: &Sort,
        source: &str,
        mut error: ParseError,
    ) -> ProgramParseError {
        locate_ambiguity_places_in_text(&mut error, source);
        ProgramParseError {
            module: self.module.clone(),
            start_sort: start_sort.clone(),
            error: Box::new(error),
            item_attempt: None,
        }
    }

    /// Parse a K-declared configuration binding, preferring an existing item reading.
    /// Only absence of a reading permits trying the grammar's existing K entry;
    /// ambiguity, inference and validation failures retain their original diagnostics.
    ///
    /// An item attempt whose diagnostic stopped at its work limit (`DiagnosticWork`) has not
    /// decided whether the input has a reading that breaks a relation, which is not an absence of
    /// a reading. Where the K entry then accepts the input, the item attempt is decided again
    /// without the limit, so that whether the binding is accepted never depends on it.
    pub fn parse_configuration_k_value(
        &self,
        source: &str,
    ) -> Result<ParsedProgram, ProgramParseError> {
        self.parse_configuration_k_value_within(source, DiagnosticWork::from_environment())
    }

    fn parse_configuration_k_value_within(
        &self,
        source: &str,
        diagnostic_work: DiagnosticWork,
    ) -> Result<ParsedProgram, ProgramParseError> {
        let item = Sort::new("KItem");
        let file = UNNAMED_PROGRAM;
        match self.parse_within(&item, source, file, diagnostic_work) {
            Ok(program) => Ok(program),
            Err(item_attempt) if matches!(*item_attempt.error, ParseError::NoParse { .. }) => {
                let program = self
                    .parse_within(&Sort::new("K"), source, file, diagnostic_work)
                    .map_err(|mut error| {
                        error.item_attempt = Some(Box::new(item_attempt.clone()));
                        error
                    })?;
                if !matches!(
                    *item_attempt.error,
                    ParseError::NoParse {
                        work_limit: Some(_),
                        ..
                    }
                ) {
                    return Ok(program);
                }
                match self.parse_within(&item, source, file, DiagnosticWork::Unlimited) {
                    Err(item_attempt)
                        if matches!(*item_attempt.error, ParseError::NoParse { .. }) =>
                    {
                        Ok(program)
                    }
                    Err(error) => Err(error),
                    Ok(_) => unreachable!("an input the item grammar rejected is rejected again"),
                }
            }
            Err(error) => Err(error),
        }
    }

    /// Parse a program whose byte zero belongs to `source_id`, read from no file (see
    /// [`Self::parse`]).
    pub fn parse_with_provenance(
        &self,
        start_sort: &Sort,
        source: &str,
        source_id: SourceId,
    ) -> Result<ParsedProgram, ProgramParseError> {
        self.grammar
            .parse_with_provenance(start_sort, source, source_id, 0)
            .map(|term| ParsedProgram(self.locate(start_sort, source, UNNAMED_PROGRAM, term)))
            .map_err(|error| self.parse_error(start_sort, source, error))
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

#[cfg(feature = "cli")]
pub(crate) fn program_start_sort(
    definition: &ResolvedDefinition,
    module: ModuleId,
    spelling: &Sort,
) -> Sort {
    SortSynonyms::of_module(definition, module)
        .denotations()
        .denote(spelling)
        .clone()
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

/// The file name a program's locations carry when it was read from no file: from standard input,
/// or given as text on a command line or to a library call. No file is named `-` on a command
/// line that takes a program path, where `-` already means standard input.
pub const UNNAMED_PROGRAM: &str = "-";

/// The file name a program read from `path` carries in its locations: the path as it was given,
/// each of its bytes that is not part of a UTF-8 sequence read as the code point of its value, so
/// that a path names one sequence of characters whatever bytes it holds.
pub fn program_file_name(path: &std::path::Path) -> String {
    let mut name = String::new();
    for chunk in path.as_os_str().as_encoded_bytes().utf8_chunks() {
        name.push_str(chunk.valid());
        name.extend(chunk.invalid().iter().copied().map(char::from));
    }
    name
}

/// The label of `syntax {Sort} Sort ::= #location(Sort, String, Int, Int, Int, Int)`, module
/// `K-LOCATIONS` of `kast.md`: a term, the file of its text, and the first line and column of that
/// text and the line and column just after it.
const LOCATION_LABEL: &str = "#location";

/// A program's text and the file name its locations carry.
struct ProgramText<'a> {
    source: &'a str,
    file: &'a str,
}

/// How a parse is located.
///
/// A sort that declares `[locations]` asks that each term of that sort a program's text denotes
/// carry where that text is: such a term `t` is the term `#location{S}(t, file, l1, c1, l2, c2)`,
/// lines and columns as in diagnostics (`location::advance`), the end the position after the
/// text's last character. A term is of sort `S` in two ways, so it is located at `S` when either
/// is `S`:
///
/// - its own sort, the result sort of the production that built it, or a token's sort;
/// - the sort of its position, the argument of its parent production or the start sort, which a
///   term of a subsort fills through that subsort: `1` at an `Exp` position of `Exp ::= Int` is
///   an expression, located as one even when `Int` asks for nothing.
///
/// A term located at its position's sort `S` but of another sort `A` is placed under the wrapper
/// by its injection, `#location{S}(inj{A, S}(t), ...)`: the instance of `#location` is the sort
/// the term is located at, and the injection states it where the instance is inferred again from
/// the argument's sort (macro expansion erases a parse's instances), which would otherwise give
/// the least instance, `A`. When both sorts ask and differ, the term is located at its own sort
/// inside its location at its position's sort, `#location{S}(inj{A, S}(#location{A}(t, ...)), ...)`. A
/// subsort chain between the two sorts has no text of its own, so its intermediate sorts locate
/// nothing, and the result does not depend on which chain a parse went through. A term whose text
/// is empty, such as a list's terminator, is located at the empty span where it stands.
#[derive(Clone, Debug)]
struct Locations {
    sorts: BTreeSet<SortHead>,
    /// The productions of the parser's catalog, by the identity a parse records.
    productions: BTreeMap<ProductionIdentity, ProductionShape>,
}

/// A production's parameters, result sort and argument sorts (its nonterminals, in order).
#[derive(Clone, Debug)]
struct ProductionShape {
    parameters: Vec<Sort>,
    result: Sort,
    arguments: Vec<Sort>,
}

impl ProductionShape {
    /// `sort` with each of this production's parameters replaced by its sort in `instance`.
    fn instance(&self, sort: &Sort, instance: &[Sort]) -> Sort {
        if let Some(index) = self
            .parameters
            .iter()
            .position(|parameter| parameter == sort)
        {
            return instance[index].clone();
        }
        Sort::with_parameters(
            sort.name.clone(),
            sort.parameters
                .iter()
                .map(|sort| self.instance(sort, instance))
                .collect(),
        )
    }
}

impl Locations {
    /// The locations of the grammar of `sentences`, whose parses record identities of `catalog`;
    /// `None` when no sort declares `[locations]`.
    fn of(sentences: &[Sentence], catalog: &ProductionCatalog<'_>) -> Option<Self> {
        let sort_catalog = SortCatalog::from_visible(sentences.iter());
        let sorts = sentences
            .iter()
            .filter_map(|sentence| match sentence {
                Sentence::SyntaxSort { sort, .. } | Sentence::Production { sort, .. } => {
                    Some(SortHead::from(sort))
                }
                _ => None,
            })
            .filter(|sort| {
                sort_catalog
                    .attributes_for(sort)
                    .is_some_and(|attributes| attributes.value(AttributeKey::Locations).is_some())
            })
            .collect::<BTreeSet<_>>();
        if sorts.is_empty() {
            return None;
        }
        let productions = catalog
            .productions()
            .filter_map(|(id, production)| match production {
                Sentence::Production {
                    parameters,
                    sort,
                    items,
                    ..
                } => Some((
                    catalog.identity(id),
                    ProductionShape {
                        parameters: parameters.clone(),
                        result: sort.clone(),
                        arguments: items
                            .iter()
                            .filter_map(|item| match item {
                                ProductionItem::NonTerminal { sort, .. } => Some(sort.clone()),
                                ProductionItem::RegexTerminal { .. }
                                | ProductionItem::Terminal(_) => None,
                            })
                            .collect(),
                    },
                )),
                _ => None,
            })
            .collect();
        Some(Self { sorts, productions })
    }

    fn located(&self, sort: &Sort) -> bool {
        self.sorts.contains(&SortHead::from(sort))
    }

    /// `term`, a parse of `text` at `start`, located.
    fn locate(&self, term: Term, start: &Sort, text: &ProgramText<'_>) -> Term {
        let mut offsets = Vec::new();
        span_offsets(&term, &mut offsets);
        let positions = TextPositions::new(text.source, offsets);
        self.locate_at(term, Some(start), text.file, &positions)
    }

    /// `term`, at a position of sort `position` when that is known, located.
    fn locate_at(
        &self,
        term: Term,
        position: Option<&Sort>,
        file: &str,
        positions: &TextPositions,
    ) -> Term {
        let metadata = term.metadata().cloned();
        let shape = metadata
            .as_ref()
            .and_then(|metadata| metadata.production)
            .and_then(|production| self.productions.get(&production));
        let locate =
            |term, position: Option<&Sort>| self.locate_at(term, position, file, positions);
        let (term, own) = match term.into_unannotated().into_parts() {
            TermParts::Apply { label, arguments } => {
                let shape = shape.filter(|shape| {
                    shape.arguments.len() == arguments.len()
                        && shape.parameters.len() == label.parameters.len()
                });
                let arguments = arguments
                    .into_iter()
                    .enumerate()
                    .map(|(index, argument)| {
                        let position = shape.map(|shape| {
                            shape.instance(&shape.arguments[index], &label.parameters)
                        });
                        locate(argument, position.as_ref())
                    })
                    .collect();
                let own = shape.map(|shape| shape.instance(&shape.result, &label.parameters));
                (Term::Apply { label, arguments }, own)
            }
            TermParts::Token { token, sort } => {
                let own = Some(sort.clone());
                (Term::Token { token, sort }, own)
            }
            TermParts::Rewrite { left, right } => (
                Term::Rewrite {
                    left: Box::new(locate(*left, None)),
                    right: Box::new(locate(*right, None)),
                },
                None,
            ),
            TermParts::As { pattern, alias } => (
                Term::As {
                    pattern: Box::new(locate(*pattern, None)),
                    alias: Box::new(locate(*alias, None)),
                },
                None,
            ),
            TermParts::Sequence(items) => (
                Term::Sequence(items.into_iter().map(|item| locate(item, None)).collect()),
                None,
            ),
            leaf @ (TermParts::InjectedLabel(_) | TermParts::Variable { .. }) => {
                (Term::from(leaf), None)
            }
            TermParts::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
        };
        let Some(metadata) = metadata else {
            return term;
        };
        let location = metadata
            .span
            .and_then(|span| positions.location(span.start, span.end));
        let mut term = term.with_metadata(metadata);
        let Some(location) = location else {
            return term;
        };
        if let Some(own) = own.as_ref().filter(|own| self.located(own)) {
            term = location_term(own, term, file, location);
        }
        if let Some(position) =
            position.filter(|position| self.located(position) && own.as_ref() != Some(*position))
        {
            if let Some(own) = &own {
                term = Term::Apply {
                    label: Label::with_parameters(
                        WellKnownSymbol::Inj.as_str(),
                        vec![own.clone(), position.clone()],
                    ),
                    arguments: vec![term],
                };
            }
            term = location_term(position, term, file, location);
        }
        term
    }
}

/// Every span boundary in `term`.
fn span_offsets(term: &Term, offsets: &mut Vec<usize>) {
    if let Some(span) = term.metadata().and_then(|metadata| metadata.span) {
        offsets.extend([span.start, span.end]);
    }
    match term.unannotated() {
        Term::Apply { arguments, .. } => {
            for argument in arguments {
                span_offsets(argument, offsets);
            }
        }
        Term::Rewrite { left, right } => {
            span_offsets(left, offsets);
            span_offsets(right, offsets);
        }
        Term::As { pattern, alias } => {
            span_offsets(pattern, offsets);
            span_offsets(alias, offsets);
        }
        Term::Sequence(items) => {
            for item in items {
                span_offsets(item, offsets);
            }
        }
        Term::InjectedLabel(_)
        | Term::Variable { .. }
        | Term::Token { .. }
        | Term::Annotated { .. } => {}
    }
}

/// `#location{sort}(term, file, ...)` with the lines and columns of `location`; `term` is of sort
/// `sort`.
fn location_term(sort: &Sort, term: Term, file: &str, location: Location) -> Term {
    let int = |value: u32| Term::Token {
        token: value.to_string(),
        sort: Sort::builtin(BuiltinSort::Int),
    };
    Term::Apply {
        label: Label {
            name: LOCATION_LABEL.to_owned(),
            parameters: vec![sort.clone()],
        },
        arguments: vec![
            term,
            Term::Token {
                token: crate::kast::string::quote(file),
                sort: Sort::builtin(BuiltinSort::String),
            },
            int(location.start_line),
            int(location.start_column),
            int(location.end_line),
            int(location.end_column),
        ],
    }
}

fn without_source_spans(term: Term) -> Term {
    crate::stack::guarded(|| match term.into_parts() {
        TermParts::Annotated { term, mut metadata } => {
            metadata.span = None;
            without_source_spans(*term).with_metadata(metadata)
        }
        TermParts::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(without_source_spans(*left)),
            right: Box::new(without_source_spans(*right)),
        },
        TermParts::As { pattern, alias } => Term::As {
            pattern: Box::new(without_source_spans(*pattern)),
            alias: Box::new(without_source_spans(*alias)),
        },
        TermParts::Sequence(items) => {
            Term::Sequence(items.into_iter().map(without_source_spans).collect())
        }
        TermParts::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments.into_iter().map(without_source_spans).collect(),
        },
        term @ (TermParts::InjectedLabel(_)
        | TermParts::Variable { .. }
        | TermParts::Token { .. }) => Term::from(term),
    })
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
        append_unique_syntax(
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
        append_unique_syntax(sentences, definition.public_sentences(module));
    }
}

fn program_import(definition: &ResolvedDefinition, module: ModuleId) -> (ModuleId, bool) {
    let imported_name = &definition.module(module).name;
    let companion_name = format!("{imported_name}{PROGRAM_PARSING_POSTFIX}");
    definition
        .module_id(&companion_name)
        .map_or((module, false), |companion| (companion, true))
}

/// Append the syntax declarations of `incoming` not equivalent to one already collected.
///
/// A program grammar is the syntax its module sees, and only syntax declarations define it
/// ([`Sentence::is_syntax`]): every step that builds the grammar from the collected set reads
/// productions, sort declarations, synonyms, lexical identifiers and priority and associativity
/// declarations, and skips every other sentence. Rules, claims, contexts and configuration
/// declarations are therefore never collected, so a parser's preparation neither copies nor
/// compares their terms, whatever their size or depth.
fn append_unique_syntax<'a>(
    sentences: &mut Vec<Sentence>,
    incoming: impl IntoIterator<Item = &'a Sentence>,
) {
    let mut seen = EquivalenceAccumulator::from_sentences(sentences.iter());
    let accepted = incoming
        .into_iter()
        .filter(|sentence| sentence.is_syntax())
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
    crate::stack::guarded(|| {
        let metadata = term.metadata().cloned();
        let inferred_production_parameters = metadata
            .as_ref()
            .and_then(|metadata| metadata.production)
            .is_some_and(|production| parametric_productions.contains(&production));
        let rebuilt = match term.into_unannotated().into_parts() {
            TermParts::Apply {
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
            TermParts::InjectedLabel(mut label) => {
                if inferred_production_parameters {
                    label.parameters.clear();
                }
                Term::InjectedLabel(label)
            }
            TermParts::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(strip_inferred_parameters(*left, parametric_productions)),
                right: Box::new(strip_inferred_parameters(*right, parametric_productions)),
            },
            TermParts::As { pattern, alias } => Term::As {
                pattern: Box::new(strip_inferred_parameters(*pattern, parametric_productions)),
                alias: Box::new(strip_inferred_parameters(*alias, parametric_productions)),
            },
            TermParts::Sequence(items) => Term::Sequence(
                items
                    .into_iter()
                    .map(|item| strip_inferred_parameters(item, parametric_productions))
                    .collect(),
            ),
            leaf @ (TermParts::Variable { .. } | TermParts::Token { .. }) => Term::from(leaf),
            TermParts::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
        };
        match metadata {
            Some(metadata) => rebuilt.with_metadata(metadata),
            None => rebuilt,
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parser(source: &str) -> ProgramParser {
        let parsed = crate::outer::parse("configuration-binding.k", source).unwrap();
        let definition = crate::outer::lower(&parsed, "MAIN").unwrap();
        ProgramParser::new(&definition, "MAIN").unwrap()
    }

    #[test]
    fn configuration_k_binding_prefers_an_item_reading() {
        let parser = parser(
            r#"
module MAIN
  syntax KItem ::= "same" [symbol(item)]
  syntax K ::= "same" [symbol(whole)]
endmodule
"#,
        );
        assert_eq!(
            parser.parse_configuration_k_value("same").unwrap(),
            parser.parse(&Sort::new("KItem"), "same").unwrap(),
        );
    }

    #[test]
    fn configuration_k_binding_falls_back_only_after_no_item_reading() {
        let parser = parser(
            r#"
module MAIN
  syntax KItem ::= "item" [symbol(item)]
  syntax K ::= "whole" [symbol(whole)]
endmodule
"#,
        );
        assert_eq!(
            parser.parse_configuration_k_value("whole").unwrap(),
            parser.parse(&Sort::new("K"), "whole").unwrap(),
        );
        let error = parser.parse_configuration_k_value("missing").unwrap_err();
        assert_eq!(error.start_sort, Sort::new("K"));
        assert_eq!(
            error.item_attempt.as_ref().unwrap().start_sort,
            Sort::new("KItem")
        );
        assert!(error.to_string().contains("declared K"));
        assert!(error.to_string().contains("item attempt:"));
        assert!(error.to_string().contains("K attempt:"));
    }

    #[test]
    fn configuration_k_binding_retains_item_only_modules_and_missing_item_entry() {
        let item_only = parser(
            r#"
module MAIN
  syntax KItem ::= "item" [symbol(item)]
endmodule
"#,
        );
        assert_eq!(
            item_only.parse_configuration_k_value("item").unwrap(),
            item_only.parse(&Sort::new("KItem"), "item").unwrap()
        );
        let k_only = parser(
            r#"
module MAIN
  syntax K ::= "whole" [symbol(whole)]
endmodule
"#,
        );
        assert_eq!(
            k_only.parse_configuration_k_value("whole").unwrap(),
            k_only.parse(&Sort::new("K"), "whole").unwrap()
        );
    }

    #[test]
    fn a_program_ambiguity_locates_its_subterms_by_line_and_column() {
        let parser = parser(
            r#"
module MAIN
  syntax Exp ::= "x" [symbol(first)] | "x" [symbol(second)]
  syntax Pgm ::= "f" "(" Exp "," Exp ")" [symbol(f)]
endmodule
"#,
        );
        // Each `x` reads two ways independently, so the report names the two `x` as its
        // subterms, located in the program text from line 1, column 1.
        let error = parser.parse(&Sort::new("Pgm"), "f(x,\n  x)").unwrap_err();
        let ParseError::Ambiguous { places, .. } = &*error.error else {
            panic!("expected an ambiguity, got {error}");
        };
        let starts = places
            .iter()
            .map(|place| {
                place
                    .location
                    .map(|location| (location.start_line, location.start_column))
            })
            .collect::<Vec<_>>();
        assert_eq!(starts, [Some((1, 3)), Some((2, 3))]);
        let message = error.to_string();
        assert!(
            message.contains("Subterm 1 at 1:3:") && message.contains("Subterm 2 at 2:3:"),
            "{message}"
        );
    }

    #[test]
    fn configuration_k_binding_retains_ambiguous_item_diagnostic() {
        let parser = parser(
            r#"
module MAIN
  syntax KItem ::= "same" [symbol(first)] | "same" [symbol(second)]
  syntax K ::= "same" [symbol(whole)]
endmodule
"#,
        );
        let item_error = parser.parse(&Sort::new("KItem"), "same").unwrap_err();
        assert!(matches!(*item_error.error, ParseError::Ambiguous { .. }));
        assert_eq!(parser.parse_configuration_k_value("same"), Err(item_error));
    }

    /// Whether a `K` binding is accepted does not depend on the diagnostic's work limit: an item
    /// attempt abandoned at the limit has not decided that the input has no item reading, so
    /// where the `K` entry accepts, the item attempt is decided without the limit. Here every
    /// item reading of `a + ... + a - a - b` nests the non-associative `-` in itself, and the
    /// `K` entry reads the last `-` as its own: the item attempt's relation error is reported,
    /// within the limit or past it. (The sums below the `-` make the item attempt's diagnostic
    /// cubic, so that it reaches a limit proportional to its first attempt.)
    #[test]
    fn configuration_k_binding_does_not_depend_on_the_diagnostic_work_limit() {
        let parser = parser(
            r#"
module MAIN
  syntax KItem ::= "a" [symbol(a)] | "b" [symbol(b)]
                 | KItem "+" KItem [left, symbol(plus)]
                 > KItem "-" KItem [non-assoc, symbol(minus)]
  syntax K ::= KItem "-" "b" [symbol(whole)]
endmodule
"#,
        );
        let source = vec!["a"; 20].join(" + ") + " - a - b";
        let unlimited = parser
            .parse_configuration_k_value_within(&source, DiagnosticWork::Unlimited)
            .unwrap_err();
        assert!(
            matches!(*unlimited.error, ParseError::Associativity { .. }),
            "{unlimited}"
        );
        let limited = parser
            .parse_within(
                &Sort::new("KItem"),
                &source,
                UNNAMED_PROGRAM,
                DiagnosticWork::Limited { floor: 0 },
            )
            .unwrap_err();
        assert!(
            matches!(
                *limited.error,
                ParseError::NoParse {
                    work_limit: Some(_),
                    ..
                }
            ),
            "the item attempt must reach its limit: {limited}"
        );
        assert!(
            parser
                .parse_within(
                    &Sort::new("K"),
                    &source,
                    UNNAMED_PROGRAM,
                    DiagnosticWork::Limited { floor: 0 }
                )
                .is_ok()
        );
        assert_eq!(
            parser
                .parse_configuration_k_value_within(&source, DiagnosticWork::Limited { floor: 0 }),
            Err(unlimited)
        );
    }

    /// A definition whose two modules, the program module and one it imports, each hold a rule,
    /// a claim, a context, a context alias and a configuration declaration whose first term is
    /// `depth` levels deep.
    fn with_semantic_sentences(depth: usize) -> Definition {
        let parsed = crate::outer::parse(
            "semantic-sentences.k",
            r#"
module LIB
  syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
endmodule

module MAIN
  imports LIB
  syntax KItem ::= "go" [symbol(go)]
endmodule
"#,
        )
        .unwrap();
        let mut definition = crate::outer::lower(&parsed, "MAIN").unwrap();
        let deep = || {
            (0..depth).fold(Term::apply("z", Vec::new()), |term, _| {
                Term::apply("s", vec![term])
            })
        };
        let side = || Term::variable("C");
        for module in &mut definition.modules {
            if module.name != "LIB" && module.name != "MAIN" {
                continue;
            }
            module.local_sentences.extend(
                [
                    Sentence::Rule {
                        body: deep(),
                        requires: side(),
                        ensures: side(),
                        attributes: Attributes::default(),
                    },
                    Sentence::Claim {
                        body: deep(),
                        requires: side(),
                        ensures: side(),
                        attributes: Attributes::default(),
                    },
                    Sentence::Context {
                        body: deep(),
                        requires: side(),
                        attributes: Attributes::default(),
                    },
                    Sentence::ContextAlias {
                        body: deep(),
                        requires: side(),
                        attributes: Attributes::default(),
                    },
                    Sentence::Configuration {
                        body: deep(),
                        ensures: side(),
                        attributes: Attributes::default(),
                    },
                ]
                .map(Arc::new),
            );
        }
        definition
    }

    /// A program grammar is the syntax its module sees: the sentence sets prepared for the
    /// in-process parser and for a generated Bison parser hold syntax declarations only, not the
    /// rules, claims, contexts and configuration declarations of the program module or of the
    /// modules it imports.
    #[test]
    fn program_grammar_sentences_are_syntax_declarations_only() {
        let definition = with_semantic_sentences(3);
        let resolved = ResolvedDefinition::resolve(&definition).unwrap();
        let module = resolved.module_id("MAIN").unwrap();
        for sentences in [
            prepared_program_sentences(&resolved, module),
            prepared_bison_program_sentences(&resolved, module),
        ] {
            assert!(
                sentences.iter().any(|sentence| matches!(
                    sentence,
                    Sentence::Production { label: Some(label), .. } if label.name == "s"
                )),
                "the imported syntax is part of the grammar"
            );
            let semantic = sentences
                .iter()
                .filter(|sentence| !sentence.is_syntax())
                .collect::<Vec<_>>();
            assert!(semantic.is_empty(), "{semantic:#?}");
        }
    }

    /// Preparing a program parser reads no semantic sentence, so the depth of a rule's terms
    /// does not bound it: a parser is built, and parses, beside rules 100,000 levels deep on a
    /// thread of 2 MiB of stack.
    #[test]
    fn a_program_parser_is_built_beside_semantic_sentences_of_any_depth() {
        let definition = with_semantic_sentences(100_000);
        std::thread::Builder::new()
            .stack_size(2 << 20)
            .spawn(move || {
                let resolved = ResolvedDefinition::resolve(&definition).unwrap();
                let parser = ProgramParser::from_resolved(&resolved, "MAIN").unwrap();
                let program = parser.parse(&Sort::new("KItem"), "go").unwrap();
                assert!(matches!(
                    program.typed_term().unannotated(),
                    Term::Apply { label, arguments } if label.name == "go" && arguments.is_empty()
                ));
            })
            .expect("the worker should spawn")
            .join()
            .expect("the worker should finish");
    }

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
