//! ```toml algorithm
//! id = "parser.earley.recognize"
//! name = "agenda-driven Earley recognition"
//! sites = ["Grammar::parse_attempt", "Grammar::parse", "Grammar::parse_with_context_and_diagnostic_provenance"]
//! variable = "p = chart-agenda pops; d = dispatch cost and derivations read; B = input bytes; s = interned sorts"
//! counters = ["ParserParseAttempts", "ParserChartAgendaPops", "ParserChartRevisitPops", "ParserChartDerivationsRead", "ParserChartPredictionAttempts", "ParserChartCompletionCandidates", "ParserTerminalPredictionsSkipped", "ParserNonterminalPredictionsSkipped"]
//! span = "per problem"
//!
//! [[cost]]
//! mode = "recognition (the chart loop of parse_attempt)"
//! bound = "O(B x s) chart allocation plus O(p x d)"
//!
//! [[cost]]
//! mode = "one parse attempt (parse_attempt)"
//! bound = "recognition plus the post-recognition passes called at the end of parse_attempt, each carried by its own card (prepare_packed_forest, inference, resolve_terminators, filter_overloads, insert_empty_lists, remove_brackets_casts, factor and resolve ambiguity)"
//!
//! [[cost]]
//! mode = "filtered attempt with unfiltered retry (parse_with_context_and_diagnostic_provenance)"
//! bound = "at most two parse attempts"
//! ```
//!
//! ```toml algorithm
//! id = "parser.lower.term"
//! name = "lowering of parsed terms into KAST"
//! sites = ["lower_term"]
//! variable = "N = parsed tree nodes; h = parsed tree height"
//! counters = []
//! no_counter = "term lowering has no dedicated counter"
//! consumes = [{ type = "k_rust::inner::parser::forest::ParsedTerm", role = "sorted tree" }]
//! produces = [{ type = "k_rust::kast::Term", role = "parsed term" }]
//! span = "none"
//!
//! [[cost]]
//! mode = "one parsed tree"
//! bound = "O(N x h), one subtree clone per lowered node"
//! ```
//!
//! ```toml algorithm
//! id = "parser.lower.regex"
//! name = "expansion of named lexical references in regex bodies during scanner compilation"
//! sites = ["expand_regex_body"]
//! variable = "B = regex syntax bytes; e = nodes of the regex body after every named reference is inlined"
//! counters = []
//! no_counter = "regex-body expansion has no dedicated counter"
//!
//! [[cost]]
//! mode = "one regex"
//! bound = "O(e)"
//! ```
//!
//! ```toml algorithm
//! id = "parser.diagnostic.no_parse"
//! name = "rendering of no-parse diagnostics"
//! sites = ["Grammar::no_parse"]
//! variable = "B = input bytes; K = state keys at the furthest non-empty chart; E = expected item descriptions; L = registered lexemes"
//! counters = []
//! no_counter = "diagnostic rendering has no dedicated counter"
//!
//! [[cost]]
//! mode = "one failed parse"
//! bound = "O(B + K x log E) plus O(L) per scanner.winner call on a position whose cache entry is empty, at most B calls"
//! ```
//!
//! ```toml algorithm
//! id = "parser.diagnostic.ambiguity"
//! name = "rendering of ambiguity diagnostics"
//! sites = ["AmbiguousParse"]
//! variable = "A = reported alternatives and their rendered terms"
//! counters = []
//! no_counter = "ambiguity rendering has no dedicated counter"
//!
//! [[cost]]
//! mode = "one ambiguous parse"
//! bound = "O(A)"
//! ```
//!
//! Agenda-driven Earley recognition over lowered K productions.
//!
//! Each attempt is O(pops * dispatch cost): `ParserChartAgendaPops` counts pops,
//! `ParserChartPredictionAttempts` plus the skipped-prediction counters count predictor work,
//! and `ParserParseAttempts` includes a possible FIRST-filtered then unfiltered retry.
//! Completion builds the packed forest; normalization, sort inference, tree disambiguation,
//! and lowering run in that order after recognition.

mod chart;
mod disambiguation;
mod forest;
mod grammar;
mod inference;
mod lists;
mod parametric;
mod prediction;
mod record;
mod scanner;
#[cfg(feature = "z3-inference")]
mod z3_inference;

use self::chart::*;
use self::disambiguation::PackedPriorityMemos;
use self::forest::*;
use self::grammar::catalog_production;
pub(super) use self::grammar::named_projection_productions;
#[cfg(feature = "z3-inference")]
use self::grammar::{render_added_production, render_production};

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::rc::Rc;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

use k_rust_kore::measure::{self, Algorithm, Counter};

#[cfg(test)]
use crate::definition::Sentence;
use crate::definition::{
    AssociativityRelations, AttributeKey, Attributes, PartialOrder, ProductionItem,
    Regex as KRegex, RegexBody,
};
use crate::kast::{
    FrontendSort, InternalLabel, Label, ProductionIdentity, Sort, Term, TermMetadata, TermSpan,
};
use crate::names::BuiltinSort;
use crate::provenance::SourceId;

use self::lists::UserList;
#[cfg(feature = "cli")]
pub(crate) use self::parametric::concretize_parametric_productions;
pub(crate) use self::parametric::is_parser_sort;
use self::prediction::PredictionAnalysis;
#[cfg(feature = "cli")]
pub(crate) use self::scanner::DEFAULT_LAYOUT;
pub(super) use self::scanner::Scanner;
use self::scanner::{Item, Layout, ScanCacheEntry, ScanWinner};

/// The name under which sort inference treats a leaf as a variable: a `#KVariable` token, or a
/// `KConfigVar` token such as `$PGM`, which both reference engines treat exactly like a variable
/// (SortInferencer.java:228 and :563, TypeInferencer.java:636 and :677,
/// TypeInferenceVisitor.java:221-233) and wrap in `#SemanticCastTo<inferred sort>`.
pub(crate) fn inferred_variable_name(term: &Term) -> Option<&str> {
    match term.unannotated() {
        Term::Variable { name, .. } => Some(name),
        Term::Token { token, sort } if sort.is_builtin(BuiltinSort::KConfigVar) => Some(token),
        _ => None,
    }
}

#[derive(Clone, Copy)]
struct ParseProvenance {
    source: SourceId,
    base_offset: usize,
}

#[derive(Clone, Copy)]
struct ParseContext {
    is_anywhere: bool,
    provenance: ParseProvenance,
    diagnostic_provenance: bool,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum PredictionMode {
    Filtered,
    Unfiltered,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AmbiguousParse {
    pub production: Option<String>,
    pub term: String,
}

/// Input encountered at the furthest point reached by the recognizer.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NoParseInput {
    /// A registered scanner token that is not accepted by the remaining grammar states.
    Token { value: String },
    /// The physical end of the input.
    EndOfInput,
    /// The smallest Unicode scalar for which the scanner has no registered winner.
    UnrecognizedInput { value: String },
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct TokenPrecedenceDeclaration {
    pub source: Option<String>,
    pub location: Option<crate::definition::Location>,
    pub production: String,
    pub precedence: i32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ParseError {
    InvalidRegex {
        regex: String,
        message: String,
    },
    InvalidTokenPrecedence {
        value: String,
    },
    InconsistentTokenPrecedence {
        token: String,
        declarations: Vec<TokenPrecedenceDeclaration>,
    },
    InvalidLayoutProduction,
    EmptyLayout,
    NoParse {
        position: usize,
        expected: Vec<String>,
        input: NoParseInput,
        previous: Option<String>,
        span: Option<TermSpan>,
    },
    InvalidParseShape {
        expected: String,
    },
    Ambiguous {
        parses: usize,
        alternatives: Vec<AmbiguousParse>,
        span: Option<TermSpan>,
    },
    CyclicParseForest,
    CircularPriorities {
        path: Vec<String>,
    },
    CircularSubsorts {
        path: Vec<Sort>,
    },
    CircularOverloads {
        path: Vec<String>,
    },
    InvalidApplyPriority {
        value: String,
        position: String,
    },
    Priority {
        parent: String,
        child: String,
    },
    Associativity {
        parent: String,
        child: String,
        side: &'static str,
    },
    CastPriority {
        cast: String,
        child: String,
    },
    Scope {
        parent: String,
        child: String,
    },
    UnknownApplication {
        label: String,
        arity: usize,
    },
    SortInference {
        message: String,
    },
    Z3InferenceRequired {
        ambiguity: bool,
        parametric_sorts: bool,
    },
    RecordProduction {
        message: String,
    },
    OverloadedTerminator {
        possible_sorts: Vec<Sort>,
    },
    UserList {
        message: String,
    },
    ListTerminator {
        possible_sorts: Vec<Sort>,
    },
}

impl fmt::Display for ParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidRegex { regex, message } => {
                write!(formatter, "invalid terminal regex {regex:?}: {message}")
            }
            Self::InvalidTokenPrecedence { value } => {
                write!(formatter, "invalid token precedence {value:?}")
            }
            Self::InconsistentTokenPrecedence {
                token,
                declarations,
            } => {
                formatter.write_str("Inconsistent token precedence detected.")?;
                for declaration in declarations {
                    formatter.write_str("\n")?;
                    if let Some(source) = &declaration.source {
                        write!(formatter, "{source}")?;
                        if let Some(location) = declaration.location {
                            write!(
                                formatter,
                                ":{}:{}",
                                location.start_line, location.start_column
                            )?;
                        }
                        formatter.write_str(": ")?;
                    }
                    write!(
                        formatter,
                        "{} [prec({})] ({token})",
                        declaration.production, declaration.precedence
                    )?;
                }
                Ok(())
            }
            Self::InvalidLayoutProduction => formatter
                .write_str("productions of sort `#Layout` must contain exactly one regex terminal"),
            Self::EmptyLayout => {
                formatter.write_str("a `#Layout` regular expression must not match empty input")
            }
            Self::NoParse {
                input, previous, ..
            } => match input {
                NoParseInput::Token { value } => {
                    write!(formatter, "Parse error: unexpected token '{value}'")?;
                    if let Some(previous) = previous {
                        write!(formatter, " following token '{previous}'")?;
                    }
                    formatter.write_str(".")
                }
                NoParseInput::EndOfInput => {
                    formatter.write_str("Parse error: unexpected end of file")?;
                    if let Some(previous) = previous {
                        write!(formatter, " following token '{previous}'")?;
                    }
                    formatter.write_str(".")
                }
                NoParseInput::UnrecognizedInput { value } => write!(
                    formatter,
                    "Scanner error: unexpected character sequence '{value}'."
                ),
            },
            Self::InvalidParseShape { expected } => {
                write!(
                    formatter,
                    "parsed term does not have the expected {expected} shape"
                )
            }
            Self::Ambiguous { alternatives, .. } => {
                formatter.write_str("Parsing ambiguity.")?;
                for (index, alternative) in alternatives.iter().enumerate() {
                    write!(
                        formatter,
                        "\n{}: {}\n    {}",
                        index + 1,
                        alternative.production.as_deref().unwrap_or(""),
                        alternative.term
                    )?;
                }
                Ok(())
            }
            Self::CyclicParseForest => {
                formatter.write_str("parse forest is infinite because of a productive unary cycle")
            }
            Self::CircularPriorities { path } => {
                write!(
                    formatter,
                    "illegal circular syntax priority: {}",
                    path.join(" > ")
                )
            }
            Self::CircularSubsorts { path } => write!(
                formatter,
                "illegal circular subsort relation: {}",
                path.iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" < ")
            ),
            Self::CircularOverloads { path } => write!(
                formatter,
                "illegal circular overload relation: {}",
                path.iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" < ")
            ),
            Self::InvalidApplyPriority { value, position } => write!(
                formatter,
                "invalid applyPriority value {position:?} in {value:?}"
            ),
            Self::Priority { parent, child } => write!(
                formatter,
                "cannot use {child} as an immediate child of {parent} because of syntax priority"
            ),
            Self::Associativity {
                parent,
                child,
                side,
            } => write!(
                formatter,
                "cannot use {child} as the immediate {side} child of {parent} because of associativity"
            ),
            Self::CastPriority { cast, child } => write!(
                formatter,
                "{child} is not allowed to be an immediate child of {cast}; use parentheses around the child to set the cast's scope"
            ),
            Self::Scope { parent, child } => write!(
                formatter,
                "{child} is not allowed to be an immediate child of {parent}; use parentheses to set the operation's scope"
            ),
            Self::UnknownApplication { label, arity } => write!(
                formatter,
                "could not find a production for K label {label:?} with arity {arity}"
            ),
            Self::SortInference { message } => formatter.write_str(message),
            Self::Z3InferenceRequired {
                ambiguity,
                parametric_sorts,
            } => {
                formatter.write_str("this term requires native Z3 sort inference")?;
                match (*ambiguity, *parametric_sorts) {
                    (true, true) => formatter
                        .write_str(" because its parse is ambiguous and contains parametric sorts"),
                    (true, false) => formatter.write_str(" because its parse is ambiguous"),
                    (false, true) => formatter.write_str(" because it contains parametric sorts"),
                    (false, false) => Ok(()),
                }
            }
            Self::RecordProduction { message } => formatter.write_str(message),
            Self::OverloadedTerminator { possible_sorts } => write!(
                formatter,
                "overloaded term does not have a least sort; possible sorts: {}",
                possible_sorts
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::UserList { message } => formatter.write_str(message),
            Self::ListTerminator { possible_sorts } => write!(
                formatter,
                "list terminator for overloaded term does not have a least sort; possible sorts: {}",
                possible_sorts
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

impl std::error::Error for ParseError {}

#[derive(Clone, Debug)]
struct Production {
    result: Sort,
    result_id: usize,
    declared_items: Vec<ProductionItem>,
    items: Vec<Item>,
    item_sort_ids: Vec<Option<usize>>,
    label: Option<Label>,
    token: bool,
    transparent: bool,
    bracket: bool,
    syntactic_subsort: bool,
    parse_label: Option<String>,
    apply_priority: Option<BTreeSet<usize>>,
    function: bool,
    macro_like: bool,
    prefer: bool,
    avoid: bool,
    source_production: Option<ProductionIdentity>,
    source_production_text: Option<String>,
    user_list: bool,
    user_list_nonempty: bool,
    field_names: Vec<Option<String>>,
    record: Option<RecordProduction>,
    parametric_origin: Option<ParametricOrigin>,
    /// Production identity retained in the parse forest after a temporary grammar production
    /// recognizes its input. Java's Earley parser uses `originalPrd` for this same boundary.
    term_production: Option<usize>,
    /// The `hook` attribute of the declaring sentence; a case-2 instantiation carries its
    /// parametric origin's hook (`EarleyParser.EarleyProduction.isMInt`).
    hook: Option<String>,
}

impl Production {
    /// Whether the production recognizes machine-integer literals, whose sort parameter is the
    /// width spelled after the `p`/`P` of the token text rather than the instantiation that
    /// scanned it (`EarleyParser.java:343-359`).
    fn is_mint_literal(&self) -> bool {
        self.token
            && (self.hook.as_deref() == Some(MINT_LITERAL_HOOK)
                || self
                    .parametric_origin
                    .as_ref()
                    .is_some_and(|origin| origin.hook() == Some(MINT_LITERAL_HOOK)))
    }
}

const MINT_LITERAL_HOOK: &str = "MINT.literal";

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParametricOrigin {
    pub(crate) label: Option<Label>,
    pub(crate) parameters: Vec<Sort>,
    pub(crate) result: Sort,
    pub(crate) items: Vec<ProductionItem>,
    pub(crate) attributes: Attributes,
    pub(crate) substitution: BTreeMap<Sort, Sort>,
}

impl ParametricOrigin {
    fn hook(&self) -> Option<&str> {
        self.attributes.string(AttributeKey::Hook)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RecordProduction {
    original: usize,
    kind: RecordProductionKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum RecordProductionKind {
    Zero,
    One(String),
    Main,
    Empty,
    Subsort,
    Repeat,
    Item(String),
}

#[derive(Clone, Debug, Default)]
struct ProductionOptions<'a> {
    token: bool,
    transparent: bool,
    bracket: bool,
    bracket_label: Option<String>,
    apply_priority: Option<&'a str>,
    function: bool,
    macro_like: bool,
    prefer: bool,
    avoid: bool,
    source_production: Option<ProductionIdentity>,
    source_production_text: Option<&'a str>,
    source: Option<&'a str>,
    location: Option<crate::definition::Location>,
    user_list: bool,
    user_list_nonempty: bool,
    precedence: Option<&'a str>,
    hook: Option<&'a str>,
    /// `RuleGrammarGenerator.java:629-637`: the `MInt{K} ::= MInt{64}` bridge between a declared
    /// instantiation and the placeholder sort exists in the parsing module only; it is added after
    /// `disambProds` is captured (:627), so the disambiguation module's subsort relations, which
    /// the sort inferencers and the priority and empty-list passes read, never contain it.
    parsing_only_subsort: bool,
}

/// A test view of one `k_rust_kore::measure` counter with the `set`/`get` shape of the scalar
/// `Cell` counters the parser tests were written against.
#[cfg(test)]
#[derive(Clone, Copy)]
struct CounterCell(Counter);

#[cfg(test)]
impl CounterCell {
    fn get(self) -> usize {
        measure::snapshot().get(self.0) as usize
    }

    fn set(self, value: usize) {
        let current = measure::snapshot().get(self.0);
        measure::add(self.0, (value as u64).wrapping_sub(current));
    }
}

#[cfg(test)]
const PACKED_STRUCTURAL_COMPARISONS: CounterCell =
    CounterCell(Counter::ParserPackedStructuralComparisons);
#[cfg(test)]
const UNPACKED_NODES: CounterCell = CounterCell(Counter::ParserUnpackedNodes);
#[cfg(test)]
const PACKED_APPLICATION_RESOLUTIONS: CounterCell =
    CounterCell(Counter::ParserPackedApplicationResolutions);
#[cfg(test)]
const PACKED_PRIORITY_COMPUTATIONS: CounterCell =
    CounterCell(Counter::ParserPackedPriorityComputations);
#[cfg(test)]
const CHART_COMPLETION_CANDIDATES: CounterCell =
    CounterCell(Counter::ParserChartCompletionCandidates);
#[cfg(test)]
const CHART_PREDICTION_ATTEMPTS: CounterCell = CounterCell(Counter::ParserChartPredictionAttempts);
#[cfg(test)]
const PARSE_ATTEMPTS: CounterCell = CounterCell(Counter::ParserParseAttempts);
#[cfg(test)]
const PREDICTION_ANALYSIS_BUILDS: CounterCell =
    CounterCell(Counter::ParserPredictionAnalysisBuilds);
#[cfg(test)]
const NONTERMINAL_PREDICTIONS_SKIPPED: CounterCell =
    CounterCell(Counter::ParserNonterminalPredictionsSkipped);

#[cfg(test)]
fn reset_packed_application_resolutions() {
    PACKED_APPLICATION_RESOLUTIONS.set(0);
}

#[cfg(test)]
fn packed_application_resolutions() -> usize {
    PACKED_APPLICATION_RESOLUTIONS.get()
}

#[cfg(test)]
fn reset_packed_priority_computations() {
    PACKED_PRIORITY_COMPUTATIONS.set(0);
}

#[cfg(test)]
fn packed_priority_computations() -> usize {
    PACKED_PRIORITY_COMPUTATIONS.get()
}

#[cfg(test)]
fn reset_chart_completion_candidates() {
    CHART_COMPLETION_CANDIDATES.set(0);
}

#[cfg(test)]
fn chart_completion_candidates() -> usize {
    CHART_COMPLETION_CANDIDATES.get()
}

/// A reusable inner grammar derived from visible productions.
///
/// Parametric productions are concretized for parsing while retaining a link to
/// their original form for sort inference.
#[derive(Clone, Debug)]
pub struct Grammar {
    generation: u64,
    productions: Vec<Production>,
    sorts: Vec<Sort>,
    sort_ids: BTreeMap<Sort, usize>,
    by_result: Vec<Vec<usize>>,
    scanner: Scanner,
    prediction_analysis: OnceLock<PredictionAnalysis>,
    source_production_texts: BTreeMap<ProductionIdentity, String>,
    layout: Layout,
    priorities: PartialOrder<String>,
    associativities: AssociativityRelations,
    subsort_relations: BTreeSet<(Sort, Sort)>,
    syntactic_subsort_relations: BTreeSet<(Sort, Sort)>,
    overloads: PartialOrder<ProductionIdentity>,
    user_lists: BTreeMap<Sort, UserList>,
    productive_unary_cycles: BTreeSet<usize>,
    role: ParserRole,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum ParserRole {
    Program,
    #[default]
    Rule,
}

impl Default for Grammar {
    fn default() -> Self {
        Self {
            generation: next_grammar_generation(),
            productions: Vec::new(),
            sorts: Vec::new(),
            sort_ids: BTreeMap::new(),
            by_result: Vec::new(),
            scanner: Scanner::default(),
            prediction_analysis: OnceLock::new(),
            source_production_texts: BTreeMap::new(),
            layout: Layout::default(),
            priorities: PartialOrder::new([]).expect("an empty relation is acyclic"),
            associativities: AssociativityRelations::default(),
            subsort_relations: BTreeSet::new(),
            syntactic_subsort_relations: BTreeSet::new(),
            overloads: PartialOrder::new([]).expect("an empty relation is acyclic"),
            user_lists: BTreeMap::new(),
            productive_unary_cycles: BTreeSet::new(),
            role: ParserRole::Rule,
        }
    }
}

impl Grammar {
    fn invalidate_prediction_analysis(&mut self) {
        self.prediction_analysis.take();
        self.generation = next_grammar_generation();
    }

    fn add_chart_state(
        &self,
        chart: &mut Chart,
        state: State,
        derivations: impl IntoIterator<Item = Derivation>,
    ) -> Result<bool, ParseError> {
        let production = &self.productions[state.production];
        let (changed, new_state) = chart.add_with_status(state, derivations)?;
        if changed && state.dot == production.items.len() {
            chart.invalidate_completed_node(production.result_id, state.origin);
        }
        if changed && new_state {
            if production
                .item_sort_ids
                .get(state.dot)
                .copied()
                .flatten()
                .is_some()
            {
                let sort_id =
                    production.item_sort_ids[state.dot].expect("nonterminal has a sort id");
                chart.waiting.entry(sort_id).or_default().push(state);
            } else if state.dot == production.items.len() {
                chart
                    .completed
                    .entry(production.result_id)
                    .or_default()
                    .push(state);
            }
        }
        Ok(changed)
    }

    pub fn parse(&self, start: &Sort, input: &str) -> Result<Term, ParseError> {
        self.parse_with_context_and_diagnostic_provenance(
            start,
            input,
            false,
            SourceId(0),
            0,
            false,
        )
    }

    /// Parse semantic text whose byte zero begins at `base_offset` in `source`.
    pub fn parse_with_provenance(
        &self,
        start: &Sort,
        input: &str,
        source: SourceId,
        base_offset: usize,
    ) -> Result<Term, ParseError> {
        self.parse_with_context_and_diagnostic_provenance(
            start,
            input,
            false,
            source,
            base_offset,
            true,
        )
    }

    pub(crate) fn parse_with_context(
        &self,
        start: &Sort,
        input: &str,
        is_anywhere: bool,
        source: SourceId,
        base_offset: usize,
    ) -> Result<Term, ParseError> {
        self.parse_with_context_and_diagnostic_provenance(
            start,
            input,
            is_anywhere,
            source,
            base_offset,
            true,
        )
    }

    pub(crate) fn parse_with_context_without_provenance(
        &self,
        start: &Sort,
        input: &str,
        is_anywhere: bool,
    ) -> Result<Term, ParseError> {
        self.parse_with_context_and_diagnostic_provenance(
            start,
            input,
            is_anywhere,
            SourceId(0),
            0,
            false,
        )
    }

    fn parse_with_context_and_diagnostic_provenance(
        &self,
        start: &Sort,
        input: &str,
        is_anywhere: bool,
        source: SourceId,
        base_offset: usize,
        diagnostic_provenance: bool,
    ) -> Result<Term, ParseError> {
        let provenance = ParseProvenance {
            source,
            base_offset,
        };
        let context = ParseContext {
            is_anywhere,
            provenance,
            diagnostic_provenance,
        };
        let mut pruned = false;
        let result =
            self.parse_attempt(start, input, context, PredictionMode::Filtered, &mut pruned);
        // Failed first scans still contribute to chart-derived diagnostics. Retry the complete
        // pipeline so every error, including inference and ambiguity errors, stays unchanged.
        // Invariant: an unfiltered retry occurs exactly when the filtered recognizer pruned at
        // least one prediction, and it reruns the complete pipeline with the same context.
        if result.is_err() && pruned {
            self.parse_attempt(
                start,
                input,
                context,
                PredictionMode::Unfiltered,
                &mut pruned,
            )
        } else {
            result
        }
    }

    fn parse_attempt(
        &self,
        start: &Sort,
        input: &str,
        context: ParseContext,
        prediction_mode: PredictionMode,
        pruned: &mut bool,
    ) -> Result<Term, ParseError> {
        let _span = measure::algorithm_span(Algorithm::ParserEarleyRecognize);
        let ParseContext {
            is_anywhere,
            provenance,
            diagnostic_provenance,
        } = context;
        measure::bump(Counter::ParserParseAttempts);
        let priority_memos = RefCell::new(PackedPriorityMemos::default());
        let prediction_analysis = (prediction_mode == PredictionMode::Filtered).then(|| {
            self.prediction_analysis
                .get_or_init(|| PredictionAnalysis::new(self))
        });
        let mut charts = (0..=input.len())
            .map(|_| Chart::new(self.sorts.len()))
            .collect::<Vec<_>>();
        let mut scanner_cache = vec![None; input.len() + 1];
        let start_position = self.canonical_position(input, 0, &mut scanner_cache);
        let Some(start_id) = self.sort_id(start) else {
            return Err(self.no_parse(
                input,
                provenance,
                diagnostic_provenance,
                &charts,
                &mut scanner_cache,
            ));
        };
        for production in self.productions_for_id(start_id) {
            self.add_chart_state(
                &mut charts[start_position],
                State {
                    production,
                    dot: 0,
                    origin: start_position,
                },
                [Vec::new()],
            )?;
        }
        charts[start_position].predicted[start_id] = true;
        let mut first_violation = None;

        // Recognition phase: saturate each position's agenda before moving to the next byte.
        for position in start_position..=input.len() {
            // Empty charts can lie inside a UTF-8 character; only evaluate layout on dispatch.
            let mut canonical_position = None;
            // Invariant: every queued state has new derivation information not yet dispatched;
            // processing either advances it or monotonically grows a chart state.
            while let Some(state) = charts[position].agenda.pop_front() {
                measure::bump(Counter::ParserChartAgendaPops);
                #[cfg(any(test, feature = "measure"))]
                let revisit = !charts[position].popped.insert(state);
                #[cfg(any(test, feature = "measure"))]
                if revisit {
                    measure::bump(Counter::ParserChartRevisitPops);
                }
                #[cfg(test)]
                update_chart_work_counters(|counters| {
                    counters.agenda_pops += 1;
                    if revisit {
                        counters.revisit_pops += 1;
                    }
                });
                let Some(derivations) = charts[position].states.get(&state).cloned() else {
                    continue;
                };
                measure::add(
                    Counter::ParserChartDerivationsRead,
                    derivations.len() as u64,
                );
                #[cfg(test)]
                let derivation_count = {
                    let derivation_count = derivations.len();
                    update_chart_work_counters(|counters| {
                        counters.derivations_read += derivation_count;
                        if revisit {
                            counters.revisit_derivations_read += derivation_count;
                        }
                    });
                    derivation_count
                };
                let production = &self.productions[state.production];
                let canonical = *canonical_position.get_or_insert_with(|| {
                    self.canonical_position(input, position, &mut scanner_cache)
                });
                if state.dot < production.items.len() && canonical != position {
                    #[cfg(test)]
                    record_chart_dispatch(ChartDispatchKind::Relocation, derivation_count, revisit);
                    self.add_chart_state(&mut charts[canonical], state, derivations)?;
                    continue;
                }

                match production.items.get(state.dot) {
                    Some(Item::NonTerminal(_sort)) => {
                        let sort_id = production.item_sort_ids[state.dot]
                            .expect("nonterminal item has a sort id");
                        #[cfg(test)]
                        record_chart_dispatch(
                            ChartDispatchKind::Nonterminal,
                            derivation_count,
                            revisit,
                        );
                        if !charts[position].predicted[sort_id] {
                            charts[position].predicted[sort_id] = true;
                            let winner = prediction_analysis.and_then(|_| {
                                self.scanner
                                    .winner(
                                        &self.layout,
                                        input,
                                        position,
                                        &mut scanner_cache[position],
                                    )
                                    .and_then(|winner| match winner {
                                        ScanWinner::Token { lexeme, .. } => Some(lexeme),
                                        ScanWinner::Layout { .. } => None,
                                    })
                            });
                            let (candidates, excluded): (Box<dyn Iterator<Item = usize> + '_>, _) =
                                if let Some(analysis) = prediction_analysis {
                                    let (candidates, excluded) =
                                        analysis.candidates(sort_id, winner);
                                    (Box::new(candidates), excluded)
                                } else {
                                    (Box::new(self.productions_for_id(sort_id)), 0)
                                };
                            if excluded != 0 {
                                measure::add(
                                    Counter::ParserTerminalPredictionsSkipped,
                                    excluded as u64,
                                );
                                *pruned = true;
                            }
                            // Invariant: each indexed survivor in this newly predicted sort bucket
                            // is either inserted once or conservatively filtered as nonterminal-first.
                            for predicted in candidates {
                                if let Some(analysis) = prediction_analysis
                                    && analysis.can_filter(predicted)
                                    && analysis.cannot_start(predicted, winner)
                                {
                                    measure::bump(Counter::ParserNonterminalPredictionsSkipped);
                                    *pruned = true;
                                    continue;
                                }
                                measure::bump(Counter::ParserChartPredictionAttempts);
                                self.add_chart_state(
                                    &mut charts[position],
                                    State {
                                        production: predicted,
                                        dot: 0,
                                        origin: position,
                                    },
                                    [Vec::new()],
                                )?;
                            }
                        }

                        // Aycock/Horspool nullable fix: a completed nullable
                        // production may have been processed before this caller.
                        let (completed, violation) = completed_nodes(
                            &charts[position],
                            self,
                            sort_id,
                            position,
                            position,
                            input,
                            provenance,
                            &priority_memos,
                        );
                        if first_violation.is_none() {
                            first_violation = violation;
                        }
                        let completed = self.filter_associative_boundary(
                            state,
                            &completed,
                            &mut first_violation,
                        );
                        if !completed.is_empty() {
                            let advanced = append_nodes(&derivations, &completed);
                            self.add_chart_state(
                                &mut charts[position],
                                State {
                                    dot: state.dot + 1,
                                    ..state
                                },
                                advanced,
                            )?;
                        }
                    }
                    Some(item) => {
                        #[cfg(test)]
                        record_chart_dispatch(ChartDispatchKind::Scan, derivation_count, revisit);
                        for end in self.scanner.matches(
                            &self.layout,
                            item,
                            input,
                            position,
                            &mut scanner_cache[position],
                        ) {
                            self.add_chart_state(
                                &mut charts[end],
                                State {
                                    dot: state.dot + 1,
                                    ..state
                                },
                                derivations.clone(),
                            )?;
                        }
                    }
                    None => {
                        #[cfg(test)]
                        record_chart_dispatch(
                            ChartDispatchKind::Completion,
                            derivation_count,
                            revisit,
                        );
                        if self.productive_unary_cycles.contains(&state.production) {
                            return Err(ParseError::CyclicParseForest);
                        }
                        let mut nodes = BTreeSet::new();
                        let mut invalid = Vec::new();
                        for children in &derivations {
                            measure::bump(Counter::ParserChartCompletionCandidates);
                            #[cfg(test)]
                            update_chart_work_counters(|counters| {
                                counters.primary_completion_candidates += 1;
                            });
                            let term = build_packed_term(
                                state.production,
                                production,
                                children,
                                input,
                                state.origin,
                                position,
                                provenance,
                            );
                            match self
                                .filter_or_defer_packed_priority(Rc::clone(&term), &priority_memos)
                            {
                                Ok(term) => {
                                    nodes.insert(term);
                                }
                                Err(error) => {
                                    invalid.push((term, error));
                                }
                            }
                        }
                        if first_violation.is_none() && !invalid.is_empty() {
                            first_violation = Some(canonical_packed_error(invalid));
                        }
                        let callers = charts[state.origin]
                            .waiting
                            .get(&production.result_id)
                            .into_iter()
                            .flatten()
                            .filter_map(|caller| {
                                charts[state.origin]
                                    .states
                                    .get(caller)
                                    .map(|derivations| (*caller, derivations.clone()))
                            })
                            .collect::<Vec<_>>();
                        for (caller, caller_derivations) in callers {
                            #[cfg(test)]
                            update_chart_work_counters(|counters| {
                                counters.completion_caller_derivations_read +=
                                    caller_derivations.len();
                            });
                            let completed = self.filter_associative_boundary(
                                caller,
                                &nodes,
                                &mut first_violation,
                            );
                            if completed.is_empty() {
                                continue;
                            }
                            self.add_chart_state(
                                &mut charts[position],
                                State {
                                    dot: caller.dot + 1,
                                    ..caller
                                },
                                append_nodes(&caller_derivations, &completed),
                            )?;
                        }
                    }
                }
            }
        }

        // Root collection phase: keep completed start productions whose suffix is layout only.
        let mut parses = BTreeSet::new();
        for (position, chart) in charts.iter().enumerate().skip(start_position) {
            if chart.states.is_empty() {
                continue;
            }
            if self.canonical_position(input, position, &mut scanner_cache) != input.len() {
                continue;
            }
            let (completed, violation) = completed_nodes(
                chart,
                self,
                start_id,
                start_position,
                position,
                input,
                provenance,
                &priority_memos,
            );
            parses.extend(completed);
            if first_violation.is_none() {
                first_violation = violation;
            }
        }
        if parses.is_empty() {
            return Err(first_violation.unwrap_or_else(|| {
                self.no_parse(
                    input,
                    provenance,
                    diagnostic_provenance,
                    &charts,
                    &mut scanner_cache,
                )
            }));
        }
        // The chart can retain the whole packed forest through its states. Release it before any
        // post-parse allocation, then apply the root priority preference while alternatives still
        // share their descendants. In particular, do not expand losing non-rewrite parses before
        // Java's root rewrite/sequence/let preference has selected the corresponding sibling.
        drop(charts);
        // Packed normalization and inference phase: preserve sharing until losing alternatives
        // are removed, then materialize exactly the retained inferred trees.
        // Java applies `PriorityVisitor` to the packed root ambiguity. Its rewrite/sequence/let
        // preference must therefore run before descending into losing alternatives; filtering
        // each root independently incorrectly rejects inputs whose winning interpretation is a
        // top-level rewrite (for example a rewrite inside a competing map-item parse).
        let forest = self.prepare_packed_forest(PackedTerm::ambiguity(parses), &priority_memos)?;
        let inferred = self.infer_packed_sorts(forest, start, is_anywhere)?;
        let resolved = self.resolve_overloaded_terminators(inferred)?;
        let filtered = self.filter_overloads_prefer_avoid(resolved);
        let listed = self.add_empty_lists(filtered, start)?;
        let cleaned = self.remove_brackets_and_syntactic_casts(listed);
        let cleaned = self.factor_ambiguities(cleaned);
        self.resolve_ambiguities(cleaned)
    }

    /// Drop completed nodes whose top label violates the caller's associativity on the side they
    /// would occupy. Rejecting those boundaries before the caller packs its derivations keeps a
    /// long associative chain from expanding into a Catalan-sized forest. Every other boundary
    /// check waits for the priority pass over the completed caller.
    fn filter_associative_boundary(
        &self,
        caller: State,
        nodes: &BTreeSet<Rc<PackedTerm>>,
        first_violation: &mut Option<ParseError>,
    ) -> BTreeSet<Rc<PackedTerm>> {
        let production = &self.productions[caller.production];
        let Some(parent) = production.parse_label.as_deref() else {
            return nodes.clone();
        };
        let (relation, side) = if caller.dot == 0 {
            (&self.associativities.right, "left")
        } else if caller.dot + 1 == production.items.len() {
            (&self.associativities.left, "right")
        } else {
            return nodes.clone();
        };
        nodes
            .iter()
            .filter(|node| {
                let Some(child) = self.packed_top_parse_label(node) else {
                    return true;
                };
                if !relation.contains(&(parent.to_owned(), child.to_owned())) {
                    return true;
                }
                first_violation.get_or_insert_with(|| ParseError::Associativity {
                    parent: parent.to_owned(),
                    child: child.to_owned(),
                    side,
                });
                false
            })
            .cloned()
            .collect()
    }

    /// Cross the shared packed-forest boundary only after Java's pre-inference transforms.
    ///
    /// Record collapse allocates generated variables against every name in the original forest,
    /// including losing root interpretations. Collect that small context before pruning so the
    /// allocation remains stable without materializing those losing trees. Every transformer
    /// before inference operates on the identity-shared DAG, matching Java's memoizing visitors.
    /// Priority runs after collapse because generated record productions deliberately defer edge
    /// checks until they have exposed their original production.
    fn prepare_packed_forest(
        &self,
        forest: Rc<PackedTerm>,
        priority_memos: &RefCell<PackedPriorityMemos>,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        let reserved_names = packed_variable_names(&forest);
        let forest = self.collapse_packed_record_productions(forest, reserved_names)?;
        let forest = self.filter_packed_priority(forest, priority_memos)?;
        let forest = self.resolve_packed_applications(forest)?;
        let forest = self.factor_pre_inference_packed_ambiguities(forest);
        let forest = self.push_top_lhs_packed_ambiguity_up(forest);
        Ok(forest)
    }

    #[cfg(test)]
    fn materialize_packed_forest(&self, forest: Rc<PackedTerm>) -> Result<ParsedTerm, ParseError> {
        Ok(self
            .prepare_packed_forest(forest, &RefCell::new(PackedPriorityMemos::default()))?
            .unpack())
    }

    fn intern_sort(&mut self, sort: &Sort) -> usize {
        if let Some(id) = self.sort_ids.get(sort).copied() {
            return id;
        }
        let id = self.sorts.len();
        self.sorts.push(sort.clone());
        self.sort_ids.insert(sort.clone(), id);
        self.by_result.push(Vec::new());
        id
    }

    pub(super) fn sort_id(&self, sort: &Sort) -> Option<usize> {
        self.sort_ids.get(sort).copied()
    }

    fn productions_for_id(&self, sort_id: usize) -> impl Iterator<Item = usize> + '_ {
        self.by_result.get(sort_id).into_iter().flatten().copied()
    }

    fn productions_for(&self, sort: &Sort) -> impl Iterator<Item = usize> + '_ {
        self.sort_id(sort)
            .into_iter()
            .flat_map(|sort_id| self.productions_for_id(sort_id))
    }

    fn canonical_position(
        &self,
        input: &str,
        mut position: usize,
        scanner_cache: &mut [ScanCacheEntry],
    ) -> usize {
        // Invariant: `position` begins at a token boundary and strictly increases whenever a
        // nonempty layout winner is consumed, so the loop terminates at a canonical boundary.
        loop {
            match self
                .scanner
                .winner(&self.layout, input, position, &mut scanner_cache[position])
            {
                Some(ScanWinner::Layout { end }) if end > position => position = end,
                _ => return position,
            }
        }
    }

    fn no_parse(
        &self,
        input: &str,
        provenance: ParseProvenance,
        diagnostic_provenance: bool,
        charts: &[Chart],
        scanner_cache: &mut [ScanCacheEntry],
    ) -> ParseError {
        let chart_position = charts
            .iter()
            .rposition(|chart| !chart.states.is_empty())
            .unwrap_or(0);
        let expected = charts[chart_position]
            .states
            .keys()
            .filter_map(|state| {
                self.productions[state.production]
                    .items
                    .get(state.dot)
                    .map(Item::description)
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let position = self.canonical_position(input, chart_position, scanner_cache);
        let (input_kind, end) = if position == input.len() {
            (NoParseInput::EndOfInput, position)
        } else {
            match self
                .scanner
                .winner(&self.layout, input, position, &mut scanner_cache[position])
            {
                Some(ScanWinner::Token { end, .. }) => (
                    NoParseInput::Token {
                        value: input[position..end].to_owned(),
                    },
                    end,
                ),
                Some(ScanWinner::Layout { .. }) => {
                    unreachable!("the diagnostic position was canonicalized past layout")
                }
                None => {
                    let end = position
                        + input[position..]
                            .chars()
                            .next()
                            .expect("a non-EOF parse position starts a Unicode scalar")
                            .len_utf8();
                    (
                        NoParseInput::UnrecognizedInput {
                            value: input[position..end].to_owned(),
                        },
                        end,
                    )
                }
            }
        };
        let mut previous = None;
        let mut cursor = 0;
        // Invariant: `cursor` is canonical, never passes `position`, and `previous` is the last
        // non-layout token ending at or before it.
        while cursor < position {
            let Some(winner) =
                self.scanner
                    .winner(&self.layout, input, cursor, &mut scanner_cache[cursor])
            else {
                break;
            };
            let winner_end = match winner {
                ScanWinner::Layout { end } => end,
                ScanWinner::Token { end, .. } => {
                    if end <= position {
                        previous = Some(input[cursor..end].to_owned());
                    }
                    end
                }
            };
            if winner_end <= cursor || winner_end > position {
                break;
            }
            cursor = winner_end;
        }
        ParseError::NoParse {
            position,
            expected,
            input: input_kind,
            previous,
            span: diagnostic_provenance.then_some(TermSpan {
                source: provenance.source,
                start: provenance.base_offset + position,
                end: provenance.base_offset + end,
            }),
        }
    }
}

static NEXT_GRAMMAR_GENERATION: AtomicU64 = AtomicU64::new(1);

fn next_grammar_generation() -> u64 {
    NEXT_GRAMMAR_GENERATION.fetch_add(1, Ordering::Relaxed)
}

/// Inline named lexical references in a regex body, rejecting recursive and undefined names.
pub(super) fn expand_regex_body(
    body: &RegexBody,
    lexical: &BTreeMap<String, KRegex>,
    stack: &mut Vec<String>,
) -> Result<RegexBody, ParseError> {
    Ok(match body {
        RegexBody::Named(name) => {
            if stack.contains(name) {
                stack.push(name.clone());
                return Err(ParseError::InvalidRegex {
                    regex: format!("{{{name}}}"),
                    message: format!("recursive lexical reference: {}", stack.join(" -> ")),
                });
            }
            let Some(definition) = lexical.get(name) else {
                return Err(ParseError::InvalidRegex {
                    regex: format!("{{{name}}}"),
                    message: format!("undefined lexical identifier {name:?}"),
                });
            };
            stack.push(name.clone());
            let expanded = expand_regex_body(&definition.body, lexical, stack)?;
            stack.pop();
            expanded
        }
        RegexBody::Union { left, right } => RegexBody::Union {
            left: Box::new(expand_regex_body(left, lexical, stack)?),
            right: Box::new(expand_regex_body(right, lexical, stack)?),
        },
        RegexBody::Concat(members) => RegexBody::Concat(
            members
                .iter()
                .map(|member| expand_regex_body(member, lexical, stack))
                .collect::<Result<_, _>>()?,
        ),
        RegexBody::ZeroOrMore(body) => {
            RegexBody::ZeroOrMore(Box::new(expand_regex_body(body, lexical, stack)?))
        }
        RegexBody::ZeroOrOne(body) => {
            RegexBody::ZeroOrOne(Box::new(expand_regex_body(body, lexical, stack)?))
        }
        RegexBody::OneOrMore(body) => {
            RegexBody::OneOrMore(Box::new(expand_regex_body(body, lexical, stack)?))
        }
        RegexBody::Exactly { body, count } => RegexBody::Exactly {
            body: Box::new(expand_regex_body(body, lexical, stack)?),
            count: *count,
        },
        RegexBody::AtLeast { body, count } => RegexBody::AtLeast {
            body: Box::new(expand_regex_body(body, lexical, stack)?),
            count: *count,
        },
        RegexBody::Range {
            body,
            at_least,
            at_most,
        } => RegexBody::Range {
            body: Box::new(expand_regex_body(body, lexical, stack)?),
            at_least: *at_least,
            at_most: *at_most,
        },
        body @ (RegexBody::Char(_) | RegexBody::AnyChar | RegexBody::CharClass { .. }) => {
            body.clone()
        }
    })
}

/// `EarleyParser.java:347-358`: the width of a machine-integer literal is the text after its
/// first `p`/`P`; a token without one keeps the scanning instantiation's sort.
fn mint_literal_sort(result: &Sort, token: &str) -> Sort {
    token.find(['p', 'P']).map_or_else(
        || result.clone(),
        |index| Sort::with_parameters(result.name.clone(), vec![Sort::new(&token[index + 1..])]),
    )
}

fn term_metadata(
    production: &Production,
    source: SourceId,
    start: usize,
    end: usize,
) -> TermMetadata {
    TermMetadata {
        span: Some(TermSpan { source, start, end }),
        production: production.source_production,
        sort: None,
        origin: None,
    }
}

fn lower_term(production: &Production, children: &[Term]) -> Term {
    if production.transparent || production.label.is_none() && children.len() == 1 {
        return children[0].clone();
    }
    let mut label = production
        .label
        .clone()
        .unwrap_or_else(|| Label::new("#anonymous"));
    // Scala's `TreeNodesToKORE` does not preserve the parser-only outer-cast label. It lowers
    // `{term}:>Sort` to the sort projection generated for the cast's result sort.
    if label.is(InternalLabel::OuterCast) {
        label = Label::projection(&production.result);
    }
    if label.is(InternalLabel::KToken)
        && let [value, sort] = children
        && let (Some(value), Some(sort)) = (kstring_token(value), kstring_token(sort))
        && let (Ok(value), Ok(sort)) = (
            crate::kast::string::unquote(value),
            crate::kast::string::unquote(sort),
        )
        && let Ok(sort) = crate::kast::parser::parse_sort_text(&sort)
    {
        return Term::Token { token: value, sort };
    }
    match (InternalLabel::of(&label.name), children) {
        (Some(InternalLabel::EmptyK), []) => Term::Sequence(Vec::new()),
        (Some(InternalLabel::KSequence), items) => Term::sequence(items.iter().cloned()),
        (Some(InternalLabel::KRewrite), [left, right]) => Term::Rewrite {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        },
        (Some(InternalLabel::KAs), [pattern, alias]) => Term::As {
            pattern: Box::new(pattern.clone()),
            alias: Box::new(alias.clone()),
        },
        _ => Term::Apply {
            label,
            arguments: children.to_vec(),
        },
    }
}

fn kstring_token(term: &Term) -> Option<&str> {
    match term.unannotated() {
        Term::Token { token, sort } if sort.is_frontend(FrontendSort::KString) => Some(token),
        _ => None,
    }
}

#[cfg(test)]
mod chart_tests {
    use super::*;

    mod prediction_filter_tests {
        use super::*;

        fn nonterminal(name: &str) -> ProductionItem {
            ProductionItem::NonTerminal {
                sort: Sort::new(name),
                name: None,
            }
        }

        fn production(result: &str, items: Vec<ProductionItem>, label: &str) -> Sentence {
            Sentence::Production {
                label: Some(Label::new(label)),
                parameters: vec![],
                sort: Sort::new(result),
                items,
                attributes: Attributes::default(),
            }
        }

        fn unfiltered(grammar: &Grammar, start: &str, input: &str) -> Result<Term, ParseError> {
            grammar.parse_attempt(
                &Sort::new(start),
                input,
                ParseContext {
                    is_anywhere: false,
                    provenance: ParseProvenance {
                        source: SourceId(0),
                        base_offset: 0,
                    },
                    diagnostic_provenance: false,
                },
                PredictionMode::Unfiltered,
                &mut false,
            )
        }

        #[test]
        fn skips_dead_first_scans_and_preserves_byte_metadata() {
            let mut sentences = vec![production("Start", vec![nonterminal("Choice")], "start")];
            for index in 0..64 {
                sentences.push(production(
                    "Choice",
                    vec![ProductionItem::Terminal(format!("dead{index}"))],
                    "dead",
                ));
            }
            sentences.push(production(
                "Choice",
                vec![ProductionItem::Terminal("é".into())],
                "chosen",
            ));
            let grammar = Grammar::from_sentences(&sentences).unwrap();
            let chosen_identity = crate::definition::production_identity(
                sentences.last().expect("chosen production"),
            );
            CHART_PREDICTION_ATTEMPTS.set(0);
            let baseline = unfiltered(&grammar, "Start", " \né ").unwrap();
            assert_eq!(CHART_PREDICTION_ATTEMPTS.get(), 65);

            CHART_PREDICTION_ATTEMPTS.set(0);
            PARSE_ATTEMPTS.set(0);
            assert_eq!(
                grammar.parse(&Sort::new("Start"), " \né ").unwrap(),
                baseline
            );
            assert_eq!(CHART_PREDICTION_ATTEMPTS.get(), 1);
            assert_eq!(PARSE_ATTEMPTS.get(), 1);
            let parsed = grammar
                .parse_with_provenance(&Sort::new("Start"), " \né ", SourceId(7), 100)
                .unwrap();
            let Term::Apply { arguments, .. } = parsed.unannotated() else {
                panic!("start constructor")
            };
            let metadata = arguments[0].metadata().unwrap();
            assert_eq!(
                metadata.span,
                Some(TermSpan {
                    source: SourceId(7),
                    start: 102,
                    end: 104
                })
            );
            assert_eq!(metadata.production, chosen_identity);
        }

        #[test]
        fn retries_exact_rejections_only_when_a_prediction_was_pruned() {
            let grammar = Grammar::from_sentences(&[
                production("Start", vec![nonterminal("Choice")], "start"),
                production("Choice", vec![ProductionItem::Terminal("a".into())], "a"),
                production("Choice", vec![ProductionItem::Terminal("b".into())], "b"),
                // A global competitor outside the predicted bucket wins the longer spelling.
                production("Other", vec![ProductionItem::Terminal("ab".into())], "ab"),
            ])
            .unwrap();
            for (input, input_kind) in [
                ("?", NoParseInput::UnrecognizedInput { value: "?".into() }),
                ("", NoParseInput::EndOfInput),
                ("ab", NoParseInput::Token { value: "ab".into() }),
            ] {
                let baseline = unfiltered(&grammar, "Start", input);
                assert_eq!(
                    baseline,
                    Err(ParseError::NoParse {
                        position: 0,
                        expected: vec!["\"a\"".into(), "\"b\"".into(), "Choice".into()],
                        input: input_kind,
                        previous: None,
                        span: None,
                    })
                );
                PARSE_ATTEMPTS.set(0);
                assert_eq!(grammar.parse(&Sort::new("Start"), input), baseline);
                assert_eq!(PARSE_ATTEMPTS.get(), 2);
            }
            PARSE_ATTEMPTS.set(0);
            assert_eq!(
                grammar.parse(&Sort::new("Missing"), "?"),
                Err(ParseError::NoParse {
                    position: 0,
                    expected: vec![],
                    input: NoParseInput::UnrecognizedInput { value: "?".into() },
                    previous: None,
                    span: None,
                })
            );
            assert_eq!(PARSE_ATTEMPTS.get(), 1);
            // Start seeding remains unfiltered, even when its first terminal cannot match.
            PARSE_ATTEMPTS.set(0);
            assert!(grammar.parse(&Sort::new("Other"), "?").is_err());
            assert_eq!(PARSE_ATTEMPTS.get(), 1);
        }

        #[test]
        fn layout_token_competition_prediction_uses_token_winner_once() {
            let grammar = Grammar::from_sentences(&[
                production("Start", vec![nonterminal("Choice")], "start"),
                production(
                    "Choice",
                    vec![ProductionItem::Terminal("ab".into())],
                    "chosen",
                ),
                production(
                    "Choice",
                    vec![ProductionItem::Terminal("dead".into())],
                    "dead",
                ),
                production("#Layout", vec![ProductionItem::regex("a")], "layout"),
            ])
            .unwrap();
            let baseline = unfiltered(&grammar, "Start", "ab").unwrap();
            assert_eq!(
                baseline,
                Term::apply("start", vec![Term::apply("chosen", vec![])])
            );
            PARSE_ATTEMPTS.set(0);
            assert_eq!(grammar.parse(&Sort::new("Start"), "ab").unwrap(), baseline);
            assert_eq!(PARSE_ATTEMPTS.get(), 1);
        }

        #[test]
        fn layout_token_competition_retry_preserves_exact_error() {
            let grammar = Grammar::from_sentences(&[
                production("Start", vec![nonterminal("Choice")], "start"),
                production(
                    "Choice",
                    vec![
                        ProductionItem::Terminal("ab".into()),
                        ProductionItem::Terminal("z".into()),
                    ],
                    "chosen",
                ),
                production(
                    "Choice",
                    vec![ProductionItem::Terminal("dead".into())],
                    "dead",
                ),
                production("#Layout", vec![ProductionItem::regex("a")], "layout"),
            ])
            .unwrap();
            let baseline = unfiltered(&grammar, "Start", "ab?");
            assert_eq!(
                baseline,
                Err(ParseError::NoParse {
                    position: 2,
                    expected: vec!["\"z\"".into()],
                    input: NoParseInput::UnrecognizedInput { value: "?".into() },
                    previous: Some("ab".into()),
                    span: None,
                })
            );
            PARSE_ATTEMPTS.set(0);
            assert_eq!(grammar.parse(&Sort::new("Start"), "ab?"), baseline);
            assert_eq!(PARSE_ATTEMPTS.get(), 2);
        }

        #[test]
        fn retries_errors_after_forest_construction() {
            let grammar = Grammar::from_sentences(&[
                production("Start", vec![nonterminal("Choice")], "start"),
                production(
                    "Choice",
                    vec![ProductionItem::Terminal("x".into())],
                    "first",
                ),
                production(
                    "Choice",
                    vec![ProductionItem::Terminal("x".into())],
                    "second",
                ),
                production(
                    "Choice",
                    vec![ProductionItem::Terminal("dead".into())],
                    "dead",
                ),
            ])
            .unwrap();
            let baseline = unfiltered(&grammar, "Start", "x");
            #[cfg(feature = "z3-inference")]
            assert!(matches!(
                &baseline,
                Err(ParseError::Ambiguous { parses: 2, .. })
            ));
            #[cfg(not(feature = "z3-inference"))]
            assert!(matches!(
                &baseline,
                Err(ParseError::Z3InferenceRequired {
                    ambiguity: true,
                    ..
                })
            ));
            PARSE_ATTEMPTS.set(0);
            assert_eq!(grammar.parse(&Sort::new("Start"), "x"), baseline);
            assert_eq!(PARSE_ATTEMPTS.get(), 2);
        }

        #[test]
        fn retains_zero_width_regex_winners_at_eof_and_interior_positions() {
            let grammar = Grammar::from_sentences(&[
                production(
                    "Start",
                    vec![ProductionItem::Terminal("p".into()), nonterminal("Zero")],
                    "start",
                ),
                production("Zero", vec![ProductionItem::regex("z*")], "zero"),
                production(
                    "Zero",
                    vec![ProductionItem::Terminal("dead".into())],
                    "dead",
                ),
            ])
            .unwrap();
            for input in ["p", "pz"] {
                let baseline = unfiltered(&grammar, "Start", input).unwrap();
                assert_eq!(
                    baseline,
                    Term::apply("start", vec![Term::apply("zero", vec![])])
                );
                PARSE_ATTEMPTS.set(0);
                assert_eq!(grammar.parse(&Sort::new("Start"), input).unwrap(), baseline);
                assert_eq!(PARSE_ATTEMPTS.get(), 1);
            }
            // At byte one the regex wins without consuming '?'. It must still be inserted;
            // the resulting root stops short of EOF, so this whole input is correctly rejected.
            let mut pruned = false;
            CHART_PREDICTION_ATTEMPTS.set(0);
            let result = grammar.parse_attempt(
                &Sort::new("Start"),
                "p?",
                ParseContext {
                    is_anywhere: false,
                    provenance: ParseProvenance {
                        source: SourceId(0),
                        base_offset: 0,
                    },
                    diagnostic_provenance: false,
                },
                PredictionMode::Filtered,
                &mut pruned,
            );
            assert!(result.is_err());
            assert!(pruned);
            assert_eq!(CHART_PREDICTION_ATTEMPTS.get(), 1);
        }
    }

    #[test]
    fn predicts_a_shared_sort_bucket_once_per_parse() {
        let mut grammar = Grammar::default();
        for index in 0..32 {
            grammar
                .add(
                    Sort::new("Start"),
                    vec![
                        ProductionItem::NonTerminal {
                            sort: Sort::new("Empty"),
                            name: None,
                        },
                        ProductionItem::Terminal(format!("end{index}")),
                    ],
                    Some(Label::new(format!("start{index}"))),
                    false,
                    false,
                )
                .unwrap();
        }
        grammar
            .add(
                Sort::new("Empty"),
                vec![],
                Some(Label::new("empty")),
                false,
                false,
            )
            .unwrap();

        for index in [0, 31] {
            CHART_PREDICTION_ATTEMPTS.set(0);
            assert_eq!(
                grammar
                    .parse(&Sort::new("Start"), &format!("end{index}"))
                    .unwrap(),
                Term::apply(format!("start{index}"), vec![Term::apply("empty", vec![])]),
            );
            // All 32 callers request Empty at byte zero; only one insertion is needed.
            assert_eq!(CHART_PREDICTION_ATTEMPTS.get(), 1);
        }
    }

    fn variable(name: &str) -> ParsedTerm {
        ParsedTerm::Term(Term::Variable {
            name: name.to_owned(),
            sort: None,
        })
    }

    fn derivation(term: ParsedTerm) -> Derivation {
        fn pack(term: ParsedTerm) -> Rc<PackedTerm> {
            match term {
                ParsedTerm::Term(term) => PackedTerm::leaf(term),
                ParsedTerm::Production {
                    production,
                    children,
                    metadata,
                } => PackedTerm::production(
                    production,
                    children.into_iter().map(pack).collect(),
                    metadata,
                ),
                ParsedTerm::Ambiguity(alternatives) => {
                    PackedTerm::ambiguity(alternatives.into_iter().map(pack).collect())
                }
                ParsedTerm::InstantiatedProduction { .. } => {
                    panic!("chart tests do not construct post-inference productions")
                }
            }
        }
        vec![pack(term)]
    }

    #[test]
    fn completed_casts_reject_an_unparenthesized_infix_child() {
        let mut grammar = Grammar::default();
        let sort = Sort::new("S");
        grammar
            .add(
                sort.clone(),
                vec![
                    ProductionItem::NonTerminal {
                        sort: sort.clone(),
                        name: None,
                    },
                    ProductionItem::Terminal("+".to_owned()),
                    ProductionItem::NonTerminal {
                        sort: sort.clone(),
                        name: None,
                    },
                ],
                Some(Label::new("plus")),
                false,
                false,
            )
            .unwrap();
        grammar
            .add(
                sort,
                vec![
                    ProductionItem::NonTerminal {
                        sort: Sort::new("S"),
                        name: None,
                    },
                    ProductionItem::Terminal(":S".to_owned()),
                ],
                Some(Label::new("#SemanticCastToS")),
                false,
                false,
            )
            .unwrap();
        let operand = || {
            PackedTerm::leaf(Term::Variable {
                name: "X".to_owned(),
                sort: None,
            })
        };
        let infix = PackedTerm::production(0, vec![operand(), operand()], TermMetadata::default());
        let cast = PackedTerm::production(1, vec![infix], TermMetadata::default());

        assert_eq!(
            grammar.filter_or_defer_packed_priority(
                cast,
                &RefCell::new(PackedPriorityMemos::default()),
            ),
            Err(ParseError::CastPriority {
                cast: "#SemanticCastToS".to_owned(),
                child: "plus".to_owned(),
            })
        );
    }

    #[test]
    fn casted_associative_chains_have_polynomial_completion_work() {
        fn assert_operand(term: &Term) {
            let Term::Apply { label, arguments } = term.unannotated() else {
                panic!("expected semantic cast operand, got {term}");
            };
            assert_eq!(label.name, "#SemanticCastToS");
            let [argument] = arguments.as_slice() else {
                panic!("semantic cast has the wrong arity: {term}");
            };
            assert!(
                matches!(argument.unannotated(), Term::Apply { label, arguments } if label.name == "x" && arguments.is_empty()),
                "unexpected cast operand: {argument}"
            );
        }

        fn assert_left_chain(term: &Term, operands: usize) {
            if operands == 1 {
                assert_operand(term);
                return;
            }
            let Term::Apply { label, arguments } = term.unannotated() else {
                panic!("expected plus prefix, got {term}");
            };
            assert_eq!(label.name, "plus");
            let [prefix, operand] = arguments.as_slice() else {
                panic!("plus has the wrong arity: {term}");
            };
            assert_left_chain(prefix, operands - 1);
            assert_operand(operand);
        }

        let mut grammar = Grammar::default();
        let sort = Sort::new("S");
        grammar
            .add(
                sort.clone(),
                vec![ProductionItem::Terminal("x".to_owned())],
                Some(Label::new("x")),
                false,
                false,
            )
            .unwrap();
        grammar
            .add(
                sort.clone(),
                vec![
                    ProductionItem::NonTerminal {
                        sort: sort.clone(),
                        name: None,
                    },
                    ProductionItem::Terminal("+".to_owned()),
                    ProductionItem::NonTerminal {
                        sort: sort.clone(),
                        name: None,
                    },
                ],
                Some(Label::new("plus")),
                false,
                false,
            )
            .unwrap();
        grammar
            .add(
                sort.clone(),
                vec![
                    ProductionItem::NonTerminal {
                        sort: sort.clone(),
                        name: None,
                    },
                    ProductionItem::Terminal(":S".to_owned()),
                ],
                Some(Label::new("#SemanticCastToS")),
                false,
                false,
            )
            .unwrap();
        grammar
            .associativities
            .left
            .insert(("plus".to_owned(), "plus".to_owned()));
        let operands = 30;
        let input = std::iter::repeat_n("x:S", operands)
            .collect::<Vec<_>>()
            .join("+");
        reset_chart_completion_candidates();
        reset_chart_work_counters();

        let parsed = grammar
            .parse(&sort, &input)
            .expect("casted chain should parse");
        let completion_candidates = chart_completion_candidates();
        let chart_work = chart_work_counters();

        assert_left_chain(&parsed, operands);
        eprintln!("Casted-chain completion candidates: {completion_candidates}");
        eprintln!("Casted-chain chart work: {chart_work:?}");
        assert!(
            completion_candidates <= 2 * operands * operands,
            "{} completion candidates exceeded the polynomial-work contract",
            completion_candidates
        );
    }

    fn incremental_ambiguity_grammar(trailing_terminal: bool) -> Grammar {
        let nonterminal = |name| ProductionItem::NonTerminal {
            sort: Sort::new(name),
            name: None,
        };
        let mut grammar = Grammar::default();
        let mut start_items = vec![nonterminal("A")];
        if trailing_terminal {
            start_items.push(ProductionItem::Terminal("!".to_owned()));
        }
        for (result, items, label) in [
            ("Start", start_items, "start"),
            ("A", vec![nonterminal("B")], "fromB"),
            ("A", vec![nonterminal("C")], "fromC"),
            ("B", vec![ProductionItem::Terminal("x".to_owned())], "b"),
            ("C", vec![ProductionItem::Terminal("x".to_owned())], "c"),
        ] {
            grammar
                .add(
                    Sort::new(result),
                    items,
                    Some(Label::new(label)),
                    false,
                    false,
                )
                .unwrap();
        }
        grammar
    }

    fn assert_incremental_ambiguity(result: Result<Term, ParseError>) {
        #[cfg(feature = "z3-inference")]
        {
            let ParseError::Ambiguous {
                parses,
                alternatives,
                ..
            } = result.unwrap_err()
            else {
                panic!("the two production-distinct alternatives must remain ambiguous");
            };
            assert_eq!(parses, 2);
            assert!(
                alternatives
                    .iter()
                    .all(|alternative| alternative.production.is_none())
            );
            assert_eq!(
                alternatives
                    .into_iter()
                    .map(|alternative| alternative.term)
                    .collect::<BTreeSet<_>>(),
                BTreeSet::from([
                    Term::apply("fromB", vec![Term::apply("b", vec![])]).to_string(),
                    Term::apply("fromC", vec![Term::apply("c", vec![])]).to_string(),
                ]),
            );
        }
        #[cfg(not(feature = "z3-inference"))]
        assert_eq!(
            result,
            Err(ParseError::Z3InferenceRequired {
                ambiguity: true,
                parametric_sorts: false,
            })
        );
    }

    #[test]
    fn fe19_incremental_ambiguity_revisits_scan_derivations() {
        let grammar = incremental_ambiguity_grammar(true);
        reset_chart_work_counters();

        assert_incremental_ambiguity(grammar.parse(&Sort::new("Start"), "x!"));

        let counters = chart_work_counters();
        eprintln!("FE19 incremental scan chart work: {counters:?}");
        assert!(counters.existing_state_growth_changes > 0);
        assert!(counters.revisit_pops > 0);
        assert!(counters.revisit_derivations_read > 0);
        assert!(counters.scan_revisit_derivations_read > 0);
    }

    #[test]
    fn fe19_incremental_ambiguity_revisits_completion_derivations() {
        let grammar = incremental_ambiguity_grammar(false);
        reset_chart_work_counters();

        assert_incremental_ambiguity(grammar.parse(&Sort::new("Start"), "x"));

        let counters = chart_work_counters();
        eprintln!("FE19 incremental completion chart work: {counters:?}");
        assert!(counters.existing_state_growth_changes > 0);
        assert!(counters.revisit_pops > 0);
        assert!(counters.revisit_derivations_read > 0);
        assert!(counters.completion_revisit_derivations_read > 0);
        assert!(counters.primary_completion_candidates > 0);
    }

    #[test]
    fn root_priority_filters_a_losing_packed_dag_before_materialization() {
        let mut grammar = Grammar::default();
        grammar
            .add(
                Sort::new("Rule"),
                Vec::new(),
                Some(Label::new("#KRewrite")),
                false,
                false,
            )
            .unwrap();
        grammar
            .add(
                Sort::new("Rule"),
                Vec::new(),
                Some(Label::new("ordinary")),
                false,
                false,
            )
            .unwrap();
        let mut losing = PackedTerm::leaf(Term::Variable {
            name: "leaf".to_owned(),
            sort: None,
        });
        let depth = 12;
        for _ in 0..depth {
            losing = PackedTerm::production(
                1,
                vec![Rc::clone(&losing), Rc::clone(&losing)],
                TermMetadata::default(),
            );
        }
        let preferred = PackedTerm::production(0, Vec::new(), TermMetadata::default());
        let forest = PackedTerm::ambiguity(BTreeSet::from([losing, preferred]));
        reset_unpacked_nodes();

        let materialized = grammar
            .materialize_packed_forest(forest)
            .expect("the preferred packed root satisfies post-parse checks");

        assert!(matches!(
            materialized,
            ParsedTerm::Production { production: 0, .. }
        ));
        assert_eq!(unpacked_nodes(), 1);
    }

    #[test]
    fn materialization_factors_a_retained_packed_diamond_before_unpacking() {
        let mut grammar = Grammar::default();
        grammar
            .add(
                Sort::new("Node"),
                vec![
                    ProductionItem::NonTerminal {
                        sort: Sort::new("Node"),
                        name: None,
                    },
                    ProductionItem::NonTerminal {
                        sort: Sort::new("Leaf"),
                        name: None,
                    },
                ],
                Some(Label::new("node")),
                false,
                false,
            )
            .unwrap();
        let left = PackedTerm::leaf(Term::Variable {
            name: "left".to_owned(),
            sort: None,
        });
        let right = PackedTerm::leaf(Term::Variable {
            name: "right".to_owned(),
            sort: None,
        });
        let mut shared = PackedTerm::leaf(Term::Variable {
            name: "root".to_owned(),
            sort: None,
        });
        let depth = 12;
        for _ in 0..depth {
            let alternatives = [Rc::clone(&left), Rc::clone(&right)]
                .into_iter()
                .map(|choice| {
                    PackedTerm::production(
                        0,
                        vec![Rc::clone(&shared), choice],
                        TermMetadata::default(),
                    )
                })
                .collect();
            shared = PackedTerm::ambiguity(alternatives);
        }
        let baseline_names = packed_variable_names(&shared);
        let baseline = grammar
            .filter_packed_priority(
                Rc::clone(&shared),
                &RefCell::new(PackedPriorityMemos::default()),
            )
            .expect("the packed diamond satisfies priority")
            .unpack();
        let baseline = grammar
            .collapse_record_productions(baseline, baseline_names)
            .expect("the packed diamond contains no records");
        let baseline = grammar
            .filter_priority(baseline)
            .expect("the owned diamond satisfies priority");
        let baseline = grammar
            .resolve_applications(baseline)
            .expect("the packed diamond contains no applications");
        let baseline = grammar.push_top_lhs_ambiguity_up(grammar.factor_ambiguities(baseline));
        reset_unpacked_nodes();

        let materialized = grammar
            .materialize_packed_forest(shared)
            .expect("the retained packed diamond satisfies post-parse checks");
        let materialized = grammar
            .resolve_applications(materialized)
            .expect("the factored diamond contains no applications");
        let materialized =
            grammar.push_top_lhs_ambiguity_up(grammar.factor_ambiguities(materialized));

        assert_eq!(unpacked_nodes(), 1 + depth * 4);
        assert_eq!(materialized, baseline);
    }

    #[test]
    fn record_collapse_preserves_a_shared_diamond_until_it_can_be_factored() {
        let mut grammar = Grammar::default();
        grammar
            .add(
                Sort::new("Node"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("Leaf"),
                    name: None,
                }],
                Some(Label::new("record")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[0].field_names = vec![Some("body".to_owned())];
        grammar
            .add(
                Sort::new("Node"),
                Vec::new(),
                Some(Label::new("record")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[1].record = Some(RecordProduction {
            original: 0,
            kind: RecordProductionKind::Zero,
        });
        grammar
            .add(
                Sort::new("Node"),
                vec![
                    ProductionItem::NonTerminal {
                        sort: Sort::new("Node"),
                        name: None,
                    },
                    ProductionItem::NonTerminal {
                        sort: Sort::new("Leaf"),
                        name: None,
                    },
                ],
                Some(Label::new("node")),
                false,
                false,
            )
            .unwrap();
        let left = PackedTerm::leaf(Term::Variable {
            name: "left".to_owned(),
            sort: None,
        });
        let right = PackedTerm::leaf(Term::Variable {
            name: "right".to_owned(),
            sort: None,
        });
        let mut shared = PackedTerm::production(1, Vec::new(), TermMetadata::default());
        let depth = 10;
        for _ in 0..depth {
            shared = PackedTerm::ambiguity(
                [Rc::clone(&left), Rc::clone(&right)]
                    .into_iter()
                    .map(|choice| {
                        PackedTerm::production(
                            2,
                            vec![Rc::clone(&shared), choice],
                            TermMetadata::default(),
                        )
                    })
                    .collect(),
            );
        }
        reset_unpacked_nodes();

        let materialized = grammar
            .materialize_packed_forest(shared)
            .expect("the collapsed record diamond satisfies priority");

        assert_eq!(unpacked_nodes(), 2 + depth * 4);
        assert!(matches!(
            materialized,
            ParsedTerm::Production { production: 2, .. }
        ));
    }

    #[test]
    fn packed_record_collapse_discards_a_duplicate_key_ambiguity_sibling() {
        let mut grammar = Grammar::default();
        grammar
            .add(
                Sort::new("Record"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("Value"),
                    name: None,
                }],
                Some(Label::new("record")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[0].field_names = vec![Some("body".to_owned())];
        grammar
            .add(
                Sort::new("Record"),
                Vec::new(),
                Some(Label::new("record")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[1].record = Some(RecordProduction {
            original: 0,
            kind: RecordProductionKind::Zero,
        });
        grammar
            .add(
                Sort::new("RecordItem"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("Value"),
                    name: None,
                }],
                Some(Label::new("recordItem")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[2].record = Some(RecordProduction {
            original: 0,
            kind: RecordProductionKind::Item("body".to_owned()),
        });
        grammar
            .add(
                Sort::new("Record"),
                vec![
                    ProductionItem::NonTerminal {
                        sort: Sort::new("RecordItem"),
                        name: None,
                    },
                    ProductionItem::NonTerminal {
                        sort: Sort::new("RecordItem"),
                        name: None,
                    },
                ],
                Some(Label::new("recordRepeat")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[3].record = Some(RecordProduction {
            original: 0,
            kind: RecordProductionKind::Repeat,
        });
        let valid = |start| {
            PackedTerm::production(
                1,
                Vec::new(),
                TermMetadata {
                    span: Some(TermSpan {
                        source: SourceId(0),
                        start,
                        end: start + 1,
                    }),
                    ..TermMetadata::default()
                },
            )
        };
        let nested_valid = PackedTerm::ambiguity(BTreeSet::from([valid(0), valid(1)]));
        let item = |name: &str| {
            PackedTerm::production(
                2,
                vec![PackedTerm::leaf(Term::Variable {
                    name: name.to_owned(),
                    sort: None,
                })],
                TermMetadata::default(),
            )
        };
        let duplicate = PackedTerm::production(
            3,
            vec![item("first"), item("second")],
            TermMetadata::default(),
        );

        assert_eq!(
            grammar.collapse_packed_record_productions(Rc::clone(&duplicate), BTreeSet::new(),),
            Err(ParseError::RecordProduction {
                message: "Duplicate record production key: body".to_owned(),
            })
        );

        let collapsed = grammar
            .collapse_packed_record_productions(
                PackedTerm::ambiguity(BTreeSet::from([nested_valid, duplicate])),
                BTreeSet::new(),
            )
            .expect("a valid record alternative survives its duplicate-key sibling");
        let PackedNode::Ambiguity(alternatives) = &collapsed.node else {
            panic!("expected two flat successful alternatives");
        };
        assert_eq!(alternatives.len(), 2);
        assert!(
            alternatives
                .iter()
                .all(|alternative| !matches!(&alternative.node, PackedNode::Ambiguity(_)))
        );
        let names = packed_terms_in_structural_order(alternatives)
            .into_iter()
            .map(|alternative| {
                let PackedNode::Production { children, .. } = &alternative.node else {
                    panic!("expected collapsed record production");
                };
                let PackedNode::Term(Term::Variable { name, .. }) = &children[0].node else {
                    panic!("expected generated record variable");
                };
                name.clone()
            })
            .collect::<Vec<_>>();
        assert_eq!(names, ["_body0", "_body1"]);
    }

    #[test]
    fn packed_record_collapse_selects_the_structurally_first_all_invalid_error() {
        let mut grammar = Grammar::default();
        grammar
            .add(
                Sort::new("Record"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("Value"),
                    name: None,
                }],
                Some(Label::new("record")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[0].field_names = vec![Some("body".to_owned())];
        for kind in [
            RecordProductionKind::Main,
            RecordProductionKind::One("body".to_owned()),
        ] {
            grammar
                .add(
                    Sort::new("Record"),
                    Vec::new(),
                    Some(Label::new("record")),
                    false,
                    false,
                )
                .unwrap();
            let production = grammar.productions.len() - 1;
            grammar.productions[production].record = Some(RecordProduction { original: 0, kind });
        }
        let malformed_list = PackedTerm::production(1, Vec::new(), TermMetadata::default());
        let malformed_item = PackedTerm::production(2, Vec::new(), TermMetadata::default());

        let error = grammar
            .collapse_packed_record_productions(
                PackedTerm::ambiguity(BTreeSet::from([malformed_item, malformed_list])),
                BTreeSet::new(),
            )
            .expect_err("all malformed record alternatives fail");

        assert_eq!(
            error,
            ParseError::RecordProduction {
                message: "malformed generated record list".to_owned(),
            }
        );
    }

    #[test]
    fn nested_packed_record_errors_follow_owned_structural_order() {
        let mut grammar = Grammar::default();
        grammar
            .add(
                Sort::new("Record"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("Value"),
                    name: None,
                }],
                Some(Label::new("record")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[0].field_names = vec![Some("body".to_owned())];
        grammar
            .add(
                Sort::new("Record"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("Record"),
                    name: None,
                }],
                Some(Label::new("record")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[1].record = Some(RecordProduction {
            original: 0,
            kind: RecordProductionKind::Main,
        });
        let candidates = (0..64)
            .map(|index| {
                let kind = if index % 2 == 0 {
                    RecordProductionKind::Main
                } else {
                    RecordProductionKind::One("body".to_owned())
                };
                grammar
                    .add(
                        Sort::new("Record"),
                        Vec::new(),
                        Some(Label::new("record")),
                        false,
                        false,
                    )
                    .unwrap();
                let production = grammar.productions.len() - 1;
                grammar.productions[production].record = Some(RecordProduction {
                    original: 0,
                    kind: kind.clone(),
                });
                let message = match kind {
                    RecordProductionKind::Main => "malformed generated record list",
                    RecordProductionKind::One(_) => "malformed generated record item",
                    _ => unreachable!(),
                };
                (
                    PackedTerm::production(production, Vec::new(), TermMetadata::default()),
                    message,
                )
            })
            .collect::<Vec<_>>();
        let (left, right) = candidates
            .iter()
            .enumerate()
            .flat_map(|(index, left)| {
                candidates[index + 1..]
                    .iter()
                    .map(move |right| (left, right))
            })
            .find(|((left, left_message), (right, right_message))| {
                left_message != right_message
                    && left.cmp(right) != cmp_packed_structurally(left, right)
            })
            .expect("fingerprint and structural order differ for two malformed record shapes");
        let expected = if cmp_packed_structurally(&left.0, &right.0).is_lt() {
            left.1
        } else {
            right.1
        };
        let nested =
            PackedTerm::ambiguity(BTreeSet::from([Rc::clone(&left.0), Rc::clone(&right.0)]));
        let wrapper = PackedTerm::production(1, vec![nested], TermMetadata::default());

        assert_eq!(
            grammar.collapse_packed_record_productions(wrapper, BTreeSet::new()),
            Err(ParseError::RecordProduction {
                message: expected.to_owned(),
            })
        );
    }

    #[test]
    fn canonical_packed_error_does_not_unpack_deep_invalid_dags() {
        let deep = |root, name: &str| {
            let mut term = PackedTerm::leaf(Term::Variable {
                name: name.to_owned(),
                sort: None,
            });
            for production in 2..14 {
                term = PackedTerm::production(
                    production,
                    vec![Rc::clone(&term), Rc::clone(&term)],
                    TermMetadata::default(),
                );
            }
            PackedTerm::production(root, vec![term], TermMetadata::default())
        };
        let first = deep(0, "first");
        let second = deep(1, "second");
        reset_unpacked_nodes();

        let selected = canonical_packed_error(vec![
            (
                second,
                ParseError::RecordProduction {
                    message: "second".to_owned(),
                },
            ),
            (
                first,
                ParseError::RecordProduction {
                    message: "first".to_owned(),
                },
            ),
        ]);

        assert_eq!(
            selected,
            ParseError::RecordProduction {
                message: "first".to_owned(),
            }
        );
        assert_eq!(unpacked_nodes(), 0);
    }

    #[cfg(feature = "z3-inference")]
    #[test]
    fn z3_inference_prunes_a_shared_dag_before_owned_materialization() {
        let mut grammar = Grammar::default();
        for (result, child, label) in [
            ("Good", "Good", "good"),
            ("Bad", "Good", "bad"),
            ("Good", "K", "#SemanticCastToGood"),
        ] {
            grammar
                .add(
                    Sort::new(result),
                    vec![ProductionItem::NonTerminal {
                        sort: Sort::new(child),
                        name: None,
                    }],
                    Some(Label::new(label)),
                    false,
                    false,
                )
                .unwrap();
        }
        grammar
            .syntactic_subsort_relations
            .remove(&(Sort::new("Good"), Sort::new("Good")));
        let mut shared = PackedTerm::leaf(Term::Variable {
            name: "_".to_owned(),
            sort: None,
        });
        let depth = 12;
        for _ in 0..depth {
            shared = PackedTerm::ambiguity(BTreeSet::from([
                PackedTerm::production(0, vec![Rc::clone(&shared)], TermMetadata::default()),
                PackedTerm::production(1, vec![shared], TermMetadata::default()),
            ]));
        }
        reset_unpacked_nodes();
        let baseline = grammar
            .infer_sorts_z3(shared.unpack(), &Sort::new("Good"), false)
            .expect("the owned baseline retains the recursively well-sorted alternative");
        let baseline_unpack_visits = unpacked_nodes();
        reset_unpacked_nodes();

        let inferred = grammar
            .infer_packed_sorts(Rc::clone(&shared), &Sort::new("Good"), false)
            .expect("Z3 retains the recursively well-sorted alternative");

        assert_eq!(inferred, baseline);
        assert_eq!(Grammar::ambiguity_count(&inferred), 1);
        assert_eq!(baseline_unpack_visits, (1 << (depth + 2)) - 3);
        assert_eq!(unpacked_nodes(), depth + 2);
    }

    #[test]
    fn losing_record_roots_consume_generated_uids_before_priority_selection() {
        let mut grammar = Grammar::default();
        grammar
            .add(
                Sort::new("Record"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("Value"),
                    name: None,
                }],
                Some(Label::new("record")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[0].field_names = vec![Some("body".to_owned())];
        grammar
            .add(
                Sort::new("Record"),
                Vec::new(),
                Some(Label::new("record")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[1].record = Some(RecordProduction {
            original: 0,
            kind: RecordProductionKind::Zero,
        });
        for label in ["ordinary", "#KRewrite"] {
            grammar
                .add(
                    Sort::new("Rule"),
                    vec![ProductionItem::NonTerminal {
                        sort: Sort::new("Record"),
                        name: None,
                    }],
                    Some(Label::new(label)),
                    false,
                    false,
                )
                .unwrap();
        }
        let record = |start| {
            PackedTerm::production(
                1,
                Vec::new(),
                TermMetadata {
                    span: Some(TermSpan {
                        source: SourceId(0),
                        start,
                        end: start + 1,
                    }),
                    ..TermMetadata::default()
                },
            )
        };
        let losing = PackedTerm::production(2, vec![record(0)], TermMetadata::default());
        let preferred = PackedTerm::production(3, vec![record(1)], TermMetadata::default());

        let materialized = grammar
            .materialize_packed_forest(PackedTerm::ambiguity(BTreeSet::from([losing, preferred])))
            .expect("the preferred collapsed record satisfies priority");
        let ParsedTerm::Production { children, .. } = materialized else {
            panic!("expected preferred rewrite root");
        };
        let ParsedTerm::Production { children, .. } = &children[0] else {
            panic!("expected collapsed record");
        };
        let ParsedTerm::Term(Term::Variable { name, .. }) = &children[0] else {
            panic!("expected generated record variable");
        };

        assert_eq!(name, "_body1");
    }

    #[test]
    fn a_shared_failing_record_consumes_generated_uids_only_once() {
        let mut grammar = Grammar::default();
        for label in ["first", "second", "survivor"] {
            grammar
                .add(
                    Sort::new("Rule"),
                    vec![ProductionItem::NonTerminal {
                        sort: Sort::new("Record"),
                        name: None,
                    }],
                    Some(Label::new(label)),
                    false,
                    false,
                )
                .unwrap();
        }
        grammar
            .add(
                Sort::new("Record"),
                vec![
                    ProductionItem::NonTerminal {
                        sort: Sort::new("Value"),
                        name: None,
                    },
                    ProductionItem::NonTerminal {
                        sort: Sort::new("Record"),
                        name: None,
                    },
                ],
                Some(Label::new("failingRecord")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[3].field_names =
            vec![Some("missing".to_owned()), Some("bad".to_owned())];
        grammar
            .add(
                Sort::new("Record"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("Record"),
                    name: None,
                }],
                Some(Label::new("failingRecord")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[4].record = Some(RecordProduction {
            original: 3,
            kind: RecordProductionKind::One("bad".to_owned()),
        });
        grammar
            .add(
                Sort::new("Record"),
                Vec::new(),
                Some(Label::new("malformed")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[5].record = Some(RecordProduction {
            original: 3,
            kind: RecordProductionKind::Main,
        });
        grammar
            .add(
                Sort::new("Record"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("Value"),
                    name: None,
                }],
                Some(Label::new("survivingRecord")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[6].field_names = vec![Some("kept".to_owned())];
        grammar
            .add(
                Sort::new("Record"),
                Vec::new(),
                Some(Label::new("survivingRecord")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[7].record = Some(RecordProduction {
            original: 6,
            kind: RecordProductionKind::Zero,
        });
        let malformed = PackedTerm::production(5, Vec::new(), TermMetadata::default());
        let shared_failing = PackedTerm::production(4, vec![malformed], TermMetadata::default());
        let first =
            PackedTerm::production(0, vec![Rc::clone(&shared_failing)], TermMetadata::default());
        let second = PackedTerm::production(1, vec![shared_failing], TermMetadata::default());
        let survivor = PackedTerm::production(
            2,
            vec![PackedTerm::production(
                7,
                Vec::new(),
                TermMetadata::default(),
            )],
            TermMetadata::default(),
        );

        let materialized = grammar
            .materialize_packed_forest(PackedTerm::ambiguity(BTreeSet::from([
                first, second, survivor,
            ])))
            .expect("the surviving record remains after both shared failures");
        let ParsedTerm::Production { children, .. } = materialized else {
            panic!("expected surviving wrapper");
        };
        let ParsedTerm::Production { children, .. } = &children[0] else {
            panic!("expected surviving collapsed record");
        };
        let ParsedTerm::Term(Term::Variable { name, .. }) = &children[0] else {
            panic!("expected generated surviving field");
        };

        assert_eq!(name, "_kept1");
    }

    #[test]
    fn packed_record_collapse_visits_later_children_after_an_earlier_failure() {
        let mut grammar = Grammar::default();
        grammar
            .add(
                Sort::new("Rule"),
                vec![
                    ProductionItem::NonTerminal {
                        sort: Sort::new("Record"),
                        name: None,
                    },
                    ProductionItem::NonTerminal {
                        sort: Sort::new("Record"),
                        name: None,
                    },
                ],
                Some(Label::new("failingWrapper")),
                false,
                false,
            )
            .unwrap();
        grammar
            .add(
                Sort::new("Rule"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("Record"),
                    name: None,
                }],
                Some(Label::new("survivingWrapper")),
                false,
                false,
            )
            .unwrap();
        for (name, original, generated) in [("spent", 2, 3), ("kept", 4, 5)] {
            grammar
                .add(
                    Sort::new("Record"),
                    vec![ProductionItem::NonTerminal {
                        sort: Sort::new("Value"),
                        name: None,
                    }],
                    Some(Label::new(format!("{name}Record"))),
                    false,
                    false,
                )
                .unwrap();
            assert_eq!(grammar.productions.len() - 1, original);
            grammar.productions[original].field_names = vec![Some(name.to_owned())];
            grammar
                .add(
                    Sort::new("Record"),
                    Vec::new(),
                    Some(Label::new(format!("{name}Record"))),
                    false,
                    false,
                )
                .unwrap();
            assert_eq!(grammar.productions.len() - 1, generated);
            grammar.productions[generated].record = Some(RecordProduction {
                original,
                kind: RecordProductionKind::Zero,
            });
        }
        grammar
            .add(
                Sort::new("Record"),
                Vec::new(),
                Some(Label::new("malformed")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[6].record = Some(RecordProduction {
            original: 2,
            kind: RecordProductionKind::Main,
        });
        let failing = PackedTerm::production(
            0,
            vec![
                PackedTerm::production(6, Vec::new(), TermMetadata::default()),
                PackedTerm::production(3, Vec::new(), TermMetadata::default()),
            ],
            TermMetadata::default(),
        );
        let surviving = PackedTerm::production(
            1,
            vec![PackedTerm::production(
                5,
                Vec::new(),
                TermMetadata::default(),
            )],
            TermMetadata::default(),
        );

        let materialized = grammar
            .materialize_packed_forest(PackedTerm::ambiguity(BTreeSet::from([failing, surviving])))
            .expect("the later ambiguity alternative survives");
        let ParsedTerm::Production { children, .. } = materialized else {
            panic!("expected surviving wrapper");
        };
        let ParsedTerm::Production { children, .. } = &children[0] else {
            panic!("expected surviving collapsed record");
        };
        let ParsedTerm::Term(Term::Variable { name, .. }) = &children[0] else {
            panic!("expected generated surviving field");
        };

        assert_eq!(name, "_kept1");
    }

    #[test]
    fn packed_application_resolution_preserves_more_than_sixty_four_alternatives() {
        let mut grammar = Grammar::default();
        grammar
            .add(
                Sort::new("K"),
                vec![
                    ProductionItem::NonTerminal {
                        sort: Sort::new("KLabel"),
                        name: None,
                    },
                    ProductionItem::NonTerminal {
                        sort: Sort::new("KList"),
                        name: None,
                    },
                ],
                Some(Label::new("#KApply")),
                false,
                false,
            )
            .unwrap();
        grammar
            .add(
                Sort::new("K"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("K"),
                    name: None,
                }],
                Some(Label::new("foo")),
                false,
                false,
            )
            .unwrap();
        let application = |alternatives| {
            let label = PackedTerm::leaf(Term::Token {
                token: "foo".to_owned(),
                sort: Sort::new("KLabel"),
            });
            let arguments = PackedTerm::ambiguity(
                (0..alternatives)
                    .map(|index| {
                        PackedTerm::leaf(Term::Variable {
                            name: format!("V{index}"),
                            sort: None,
                        })
                    })
                    .collect(),
            );
            PackedTerm::production(0, vec![label, arguments], TermMetadata::default())
        };

        let retained = grammar
            .materialize_packed_forest(application(70))
            .expect("application resolution must not truncate a valid packed forest");

        assert_eq!(Grammar::ambiguity_count(&retained), 70);
    }

    #[test]
    fn a_shared_over_limit_application_is_resolved_only_once() {
        let mut grammar = Grammar::default();
        for label in ["first", "second"] {
            grammar
                .add(
                    Sort::new("K"),
                    vec![ProductionItem::NonTerminal {
                        sort: Sort::new("K"),
                        name: None,
                    }],
                    Some(Label::new(label)),
                    false,
                    false,
                )
                .unwrap();
        }
        grammar
            .add(
                Sort::new("K"),
                vec![
                    ProductionItem::NonTerminal {
                        sort: Sort::new("KLabel"),
                        name: None,
                    },
                    ProductionItem::NonTerminal {
                        sort: Sort::new("KList"),
                        name: None,
                    },
                ],
                Some(Label::new("#KApply")),
                false,
                false,
            )
            .unwrap();
        grammar
            .add(
                Sort::new("K"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("K"),
                    name: None,
                }],
                Some(Label::new("foo")),
                false,
                false,
            )
            .unwrap();
        let label = PackedTerm::leaf(Term::Token {
            token: "foo".to_owned(),
            sort: Sort::new("KLabel"),
        });
        let arguments = PackedTerm::ambiguity(
            (0..70)
                .map(|index| {
                    PackedTerm::leaf(Term::Variable {
                        name: format!("V{index}"),
                        sort: None,
                    })
                })
                .collect(),
        );
        let shared = PackedTerm::production(2, vec![label, arguments], TermMetadata::default());
        let forest = PackedTerm::ambiguity(BTreeSet::from([
            PackedTerm::production(0, vec![Rc::clone(&shared)], TermMetadata::default()),
            PackedTerm::production(1, vec![shared], TermMetadata::default()),
        ]));
        reset_packed_application_resolutions();

        let resolved = grammar
            .resolve_packed_applications(forest)
            .expect("a shared application may resolve to more than 64 alternatives");

        assert!(
            matches!(&resolved.node, PackedNode::Ambiguity(alternatives) if alternatives.len() == 2)
        );
        assert_eq!(packed_application_resolutions(), 1);
    }

    #[test]
    fn a_shared_priority_failing_parent_is_filtered_only_once() {
        let mut grammar = Grammar::default();
        for label in ["first", "second"] {
            grammar
                .add(
                    Sort::new("K"),
                    vec![ProductionItem::NonTerminal {
                        sort: Sort::new("K"),
                        name: None,
                    }],
                    Some(Label::new(label)),
                    false,
                    false,
                )
                .unwrap();
        }
        grammar
            .add(
                Sort::new("K"),
                vec![
                    ProductionItem::NonTerminal {
                        sort: Sort::new("K"),
                        name: None,
                    },
                    ProductionItem::Terminal(";".to_owned()),
                ],
                Some(Label::new("failing")),
                false,
                false,
            )
            .unwrap();
        grammar
            .add(
                Sort::new("K"),
                Vec::new(),
                Some(Label::new("#KRewrite")),
                false,
                false,
            )
            .unwrap();
        let rewrite = PackedTerm::production(3, Vec::new(), TermMetadata::default());
        let shared = PackedTerm::production(2, vec![rewrite], TermMetadata::default());
        let forest = PackedTerm::ambiguity(BTreeSet::from([
            PackedTerm::production(0, vec![Rc::clone(&shared)], TermMetadata::default()),
            PackedTerm::production(1, vec![shared], TermMetadata::default()),
        ]));
        reset_packed_priority_computations();

        let error = grammar
            .filter_packed_priority(forest, &RefCell::new(PackedPriorityMemos::default()))
            .expect_err("the shared parent cannot contain an unscoped rewrite");

        assert_eq!(
            error,
            ParseError::Scope {
                parent: "failing".to_owned(),
                child: "#KRewrite".to_owned(),
            }
        );
        assert_eq!(packed_priority_computations(), 4);
    }

    #[test]
    fn record_collapse_exposes_edges_to_owned_priority_filtering() {
        let mut grammar = Grammar::default();
        grammar
            .add(
                Sort::new("Rule"),
                vec![
                    ProductionItem::NonTerminal {
                        sort: Sort::new("Rule"),
                        name: None,
                    },
                    ProductionItem::Terminal(";".to_owned()),
                ],
                Some(Label::new("ordinary")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[0].field_names = vec![Some("body".to_owned())];
        grammar
            .add(
                Sort::new("Rule"),
                Vec::new(),
                Some(Label::new("#KRewrite")),
                false,
                false,
            )
            .unwrap();
        grammar
            .add(
                Sort::new("Rule"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("Rule"),
                    name: None,
                }],
                Some(Label::new("ordinary")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[2].record = Some(RecordProduction {
            original: 0,
            kind: RecordProductionKind::One("body".to_owned()),
        });
        let rewrite = PackedTerm::production(1, Vec::new(), TermMetadata::default());
        let record = PackedTerm::production(2, vec![rewrite], TermMetadata::default());

        assert_eq!(
            grammar.materialize_packed_forest(record),
            Err(ParseError::Scope {
                parent: "ordinary".to_owned(),
                child: "#KRewrite".to_owned(),
            })
        );
    }

    #[test]
    fn losing_packed_roots_still_reserve_record_generated_names() {
        let mut grammar = Grammar::default();
        grammar
            .add(
                Sort::new("Record"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("Value"),
                    name: None,
                }],
                Some(Label::new("record")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[0].field_names = vec![Some("body".to_owned())];
        grammar
            .add(
                Sort::new("Record"),
                Vec::new(),
                Some(Label::new("record")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[1].record = Some(RecordProduction {
            original: 0,
            kind: RecordProductionKind::Zero,
        });
        grammar
            .add(
                Sort::new("Rule"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("Record"),
                    name: None,
                }],
                Some(Label::new("#KRewrite")),
                false,
                false,
            )
            .unwrap();
        grammar
            .add(
                Sort::new("Rule"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("Value"),
                    name: None,
                }],
                Some(Label::new("ordinary")),
                false,
                false,
            )
            .unwrap();
        let record = PackedTerm::production(1, Vec::new(), TermMetadata::default());
        let preferred = PackedTerm::production(2, vec![record], TermMetadata::default());
        let reserved = PackedTerm::leaf(Term::Variable {
            name: "_body0".to_owned(),
            sort: None,
        });
        let losing = PackedTerm::production(3, vec![reserved], TermMetadata::default());
        let forest = PackedTerm::ambiguity(BTreeSet::from([preferred, losing]));

        let materialized = grammar
            .materialize_packed_forest(forest)
            .expect("the preferred root and collapsed record satisfy priority");
        let ParsedTerm::Production { children, .. } = materialized else {
            panic!("expected preferred root production");
        };
        let ParsedTerm::Production { children, .. } = &children[0] else {
            panic!("expected collapsed record production");
        };
        let ParsedTerm::Term(Term::Variable { name, .. }) = &children[0] else {
            panic!("expected generated record variable");
        };

        assert_eq!(name, "_body1");
    }

    #[test]
    fn packed_record_collapse_allocates_names_in_owned_structural_order() {
        let mut grammar = Grammar::default();
        grammar
            .add(
                Sort::new("Record"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("Value"),
                    name: None,
                }],
                Some(Label::new("record")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[0].field_names = vec![Some("body".to_owned())];
        grammar
            .add(
                Sort::new("Record"),
                Vec::new(),
                Some(Label::new("record")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[1].record = Some(RecordProduction {
            original: 0,
            kind: RecordProductionKind::Zero,
        });
        let candidates = (0..64)
            .map(|start| {
                PackedTerm::production(
                    1,
                    Vec::new(),
                    TermMetadata {
                        span: Some(TermSpan {
                            source: SourceId(0),
                            start,
                            end: start + 1,
                        }),
                        ..TermMetadata::default()
                    },
                )
            })
            .collect::<Vec<_>>();
        let (left, right) = candidates
            .iter()
            .enumerate()
            .flat_map(|(index, left)| {
                candidates[index + 1..]
                    .iter()
                    .map(move |right| (left, right))
            })
            .find(|(left, right)| left.cmp(right) != cmp_packed_structurally(left, right))
            .expect("fingerprint and structural order differ for at least one metadata pair");
        let forest = PackedTerm::ambiguity(BTreeSet::from([Rc::clone(left), Rc::clone(right)]));
        let baseline_names = packed_variable_names(&forest);
        let baseline = grammar
            .collapse_record_productions(forest.unpack(), baseline_names)
            .expect("the generated records are well formed");
        let baseline = grammar
            .filter_priority(baseline)
            .expect("the collapsed records satisfy priority");
        let baseline = grammar
            .resolve_applications(baseline)
            .expect("the collapsed records contain no applications");
        let baseline = grammar.push_top_lhs_ambiguity_up(grammar.factor_ambiguities(baseline));

        let materialized = grammar
            .materialize_packed_forest(forest)
            .expect("the packed records satisfy pre-inference disambiguation");

        assert_eq!(materialized, baseline);
    }

    #[test]
    fn indexes_waiting_and_completed_states_exactly_once() {
        let mut grammar = Grammar::default();
        let parent = Sort::new("Parent");
        let child = Sort::new("Child");
        grammar
            .add(
                parent.clone(),
                vec![ProductionItem::NonTerminal {
                    sort: child.clone(),
                    name: None,
                }],
                Some(Label::new("parent")),
                false,
                false,
            )
            .unwrap();
        let mut chart = Chart::default();
        let waiting = State {
            production: 0,
            dot: 0,
            origin: 0,
        };
        let completed = State { dot: 1, ..waiting };

        assert!(
            !grammar
                .add_chart_state(&mut chart, waiting, Vec::<Derivation>::new())
                .unwrap()
        );
        assert!(chart.states.is_empty());
        assert!(chart.waiting.is_empty());
        assert!(chart.completed.is_empty());

        assert!(
            grammar
                .add_chart_state(&mut chart, waiting, [Vec::new()])
                .unwrap()
        );
        assert!(
            !grammar
                .add_chart_state(&mut chart, waiting, [Vec::new()])
                .unwrap()
        );
        let child_id = grammar.sort_id(&child).unwrap();
        assert_eq!(chart.waiting[&child_id], vec![waiting]);

        assert!(
            grammar
                .add_chart_state(&mut chart, completed, [derivation(variable("A"))])
                .unwrap()
        );
        assert!(
            !grammar
                .add_chart_state(&mut chart, completed, [derivation(variable("A"))])
                .unwrap()
        );
        let parent_id = grammar.sort_id(&parent).unwrap();
        assert_eq!(chart.completed[&parent_id], vec![completed]);
    }

    #[test]
    fn canonicalizes_k_sequences_as_right_associative() {
        let mut grammar = Grammar::default();
        let k = Sort::new("K");
        for name in ["a", "b", "c"] {
            grammar
                .add(
                    k.clone(),
                    vec![ProductionItem::Terminal(name.into())],
                    Some(Label::new(name)),
                    false,
                    false,
                )
                .unwrap();
        }
        grammar
            .add(
                k.clone(),
                vec![
                    ProductionItem::NonTerminal {
                        sort: k.clone(),
                        name: None,
                    },
                    ProductionItem::Terminal("~>".into()),
                    ProductionItem::NonTerminal {
                        sort: k.clone(),
                        name: None,
                    },
                ],
                Some(Label::new("#KSequence")),
                false,
                false,
            )
            .unwrap();
        grammar.add_right_associative("#KSequence");

        let atom = |name| Term::Apply {
            label: Label::new(name),
            arguments: Vec::new(),
        };
        assert_eq!(
            grammar.parse(&k, "a ~> b ~> c").unwrap().unannotated(),
            &Term::sequence([atom("a"), atom("b"), atom("c")])
        );
    }
}
