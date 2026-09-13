//! A portable chart parser over lowered K productions.

mod disambiguation;
mod inference;
mod lists;
mod parametric;
mod prediction;
mod record;
mod scanner;
#[cfg(feature = "z3-inference")]
mod z3_inference;

#[cfg(test)]
use std::cell::Cell;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashSet, VecDeque};
use std::fmt;
use std::rc::Rc;
use std::sync::OnceLock;

use crate::definition::{
    AssociativityRelations, Attributes, PartialOrder, ProductionCatalog, ProductionId,
    ProductionItem, Regex as KRegex, RegexBody, Sentence, compute_associativities,
    compute_disambiguation_subsorts, compute_overloads, compute_priorities, compute_subsorts,
    parse_regex, sentence_equivalent,
};
use crate::kast::{Label, ResolvedProductionId, Sort, Term, TermMetadata, TermSpan};
use crate::provenance::SourceId;

use self::disambiguation::parse_apply_priority;
use self::lists::UserList;
#[cfg(feature = "cli")]
pub(crate) use self::parametric::concretize_parametric_productions;
pub(crate) use self::parametric::is_parser_sort;
use self::prediction::PredictionAnalysis;
#[cfg(feature = "cli")]
pub(crate) use self::scanner::DEFAULT_LAYOUT;
pub(super) use self::scanner::Scanner;
use self::scanner::{Item, Layout, ScanCacheEntry, ScanWinner, compile_item};

/// The name under which sort inference treats a leaf as a variable: a `#KVariable` token, or a
/// `KConfigVar` token such as `$PGM`, which both reference engines treat exactly like a variable
/// (SortInferencer.java:228 and :563, TypeInferencer.java:636 and :677,
/// TypeInferenceVisitor.java:221-233) and wrap in `#SemanticCastTo<inferred sort>`.
pub(crate) fn inferred_variable_name(term: &Term) -> Option<&str> {
    match term.unannotated() {
        Term::Variable { name, .. } => Some(name),
        Term::Token { token, sort } if sort.name == "KConfigVar" && sort.parameters.is_empty() => {
            Some(token)
        }
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
        path: Vec<ProductionId>,
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
    declared_items: Vec<ProductionItem>,
    items: Vec<Item>,
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
    source_production: Option<ProductionId>,
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
        self.attributes.get_str("hook")
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
    source_production: Option<ProductionId>,
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

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ParsedTerm {
    Production {
        production: usize,
        children: Vec<ParsedTerm>,
        metadata: TermMetadata,
    },
    #[cfg_attr(not(feature = "z3-inference"), allow(dead_code))]
    InstantiatedProduction {
        production: usize,
        parameters: Vec<Sort>,
        children: Vec<ParsedTerm>,
        metadata: TermMetadata,
    },
    Term(Term),
    Ambiguity(BTreeSet<ParsedTerm>),
}

/// Shared parse-forest node used through the ordering-sensitive parser and Z3-inference pipeline.
///
/// Keeping children behind `Rc` prevents chart diamonds from expanding while record syntax,
/// priority, applications, rewrite preferences, ambiguities, and sort constraints are normalized.
/// Ambiguous forests are materialized as an owned [`ParsedTerm`] only after Z3 model application
/// has discarded ill-sorted branches.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum PackedNode {
    Production {
        production: usize,
        children: Vec<Rc<PackedTerm>>,
        metadata: TermMetadata,
    },
    #[cfg_attr(not(feature = "z3-inference"), allow(dead_code))]
    InstantiatedProduction {
        production: usize,
        parameters: Vec<Sort>,
        children: Vec<Rc<PackedTerm>>,
        metadata: TermMetadata,
    },
    Term(Term),
    Ambiguity(BTreeSet<Rc<PackedTerm>>),
}

#[derive(Clone, Debug)]
struct PackedTerm {
    fingerprint: u64,
    node: PackedNode,
}

#[cfg(test)]
thread_local! {
    static CHART_WORK_COUNTERS: Cell<ChartWorkCounters> = const { Cell::new(ChartWorkCounters::ZERO) };
    static PACKED_STRUCTURAL_COMPARISONS: Cell<usize> = const { Cell::new(0) };
    static UNPACKED_NODES: Cell<usize> = const { Cell::new(0) };
    static PACKED_APPLICATION_RESOLUTIONS: Cell<usize> = const { Cell::new(0) };
    static PACKED_PRIORITY_COMPUTATIONS: Cell<usize> = const { Cell::new(0) };
    static CHART_COMPLETION_CANDIDATES: Cell<usize> = const { Cell::new(0) };
    static CHART_PREDICTION_ATTEMPTS: Cell<usize> = const { Cell::new(0) };
    static PARSE_ATTEMPTS: Cell<usize> = const { Cell::new(0) };
    static PREDICTION_ANALYSIS_BUILDS: Cell<usize> = const { Cell::new(0) };
    static TERMINAL_PREDICTIONS_SKIPPED: Cell<usize> = const { Cell::new(0) };
    static NONTERMINAL_PREDICTIONS_SKIPPED: Cell<usize> = const { Cell::new(0) };
}

#[cfg(test)]
#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ChartWorkCounters {
    add_calls: usize,
    new_state_changes: usize,
    existing_state_growth_changes: usize,
    agenda_enqueues: usize,
    agenda_pops: usize,
    revisit_pops: usize,
    derivations_read: usize,
    revisit_derivations_read: usize,
    relocation_derivations_read: usize,
    relocation_revisit_derivations_read: usize,
    nonterminal_derivations_read: usize,
    nonterminal_revisit_derivations_read: usize,
    scan_derivations_read: usize,
    scan_revisit_derivations_read: usize,
    completion_derivations_read: usize,
    completion_revisit_derivations_read: usize,
    primary_completion_candidates: usize,
    helper_completion_candidates: usize,
    completed_nodes_calls: usize,
    completed_nodes_hits: usize,
    completed_nodes_misses: usize,
    completed_nodes_invalidation_entries: usize,
    completion_caller_derivations_read: usize,
}

#[cfg(test)]
impl ChartWorkCounters {
    const ZERO: Self = Self {
        add_calls: 0,
        new_state_changes: 0,
        existing_state_growth_changes: 0,
        agenda_enqueues: 0,
        agenda_pops: 0,
        revisit_pops: 0,
        derivations_read: 0,
        revisit_derivations_read: 0,
        relocation_derivations_read: 0,
        relocation_revisit_derivations_read: 0,
        nonterminal_derivations_read: 0,
        nonterminal_revisit_derivations_read: 0,
        scan_derivations_read: 0,
        scan_revisit_derivations_read: 0,
        completion_derivations_read: 0,
        completion_revisit_derivations_read: 0,
        primary_completion_candidates: 0,
        helper_completion_candidates: 0,
        completed_nodes_calls: 0,
        completed_nodes_hits: 0,
        completed_nodes_misses: 0,
        completed_nodes_invalidation_entries: 0,
        completion_caller_derivations_read: 0,
    };
}

#[cfg(test)]
#[derive(Clone, Copy)]
enum ChartDispatchKind {
    Relocation,
    Nonterminal,
    Scan,
    Completion,
}

#[cfg(test)]
fn update_chart_work_counters(update: impl FnOnce(&mut ChartWorkCounters)) {
    let mut counters = CHART_WORK_COUNTERS.get();
    update(&mut counters);
    CHART_WORK_COUNTERS.set(counters);
}

#[cfg(test)]
fn reset_chart_work_counters() {
    CHART_WORK_COUNTERS.set(ChartWorkCounters::ZERO);
}

#[cfg(test)]
fn chart_work_counters() -> ChartWorkCounters {
    CHART_WORK_COUNTERS.get()
}

#[cfg(test)]
fn record_chart_dispatch(kind: ChartDispatchKind, derivations: usize, revisit: bool) {
    update_chart_work_counters(|counters| match kind {
        ChartDispatchKind::Relocation => {
            counters.relocation_derivations_read += derivations;
            if revisit {
                counters.relocation_revisit_derivations_read += derivations;
            }
        }
        ChartDispatchKind::Nonterminal => {
            counters.nonterminal_derivations_read += derivations;
            if revisit {
                counters.nonterminal_revisit_derivations_read += derivations;
            }
        }
        ChartDispatchKind::Scan => {
            counters.scan_derivations_read += derivations;
            if revisit {
                counters.scan_revisit_derivations_read += derivations;
            }
        }
        ChartDispatchKind::Completion => {
            counters.completion_derivations_read += derivations;
            if revisit {
                counters.completion_revisit_derivations_read += derivations;
            }
        }
    });
}

impl PartialEq for PackedTerm {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}

impl Eq for PackedTerm {}

impl PartialOrd for PackedTerm {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PackedTerm {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if std::ptr::eq(self, other) {
            return std::cmp::Ordering::Equal;
        }
        // The fingerprint is a fast ordering key, not an identity. Equal keys still compare the
        // complete structure, so even an FNV collision cannot merge distinct parses.
        self.fingerprint.cmp(&other.fingerprint).then_with(|| {
            #[cfg(test)]
            PACKED_STRUCTURAL_COMPARISONS.set(PACKED_STRUCTURAL_COMPARISONS.get() + 1);
            self.node.cmp(&other.node)
        })
    }
}

impl PackedTerm {
    fn leaf(term: Term) -> Rc<Self> {
        let mut fingerprint = Fingerprint::new(2);
        fingerprint.write(term.to_string().as_bytes());
        Rc::new(Self {
            fingerprint: fingerprint.finish(),
            node: PackedNode::Term(term),
        })
    }

    fn production(production: usize, children: Vec<Rc<Self>>, metadata: TermMetadata) -> Rc<Self> {
        let mut fingerprint = Fingerprint::new(0);
        fingerprint.write_usize(production);
        fingerprint.write_metadata(&metadata);
        for child in &children {
            fingerprint.write_u64(child.fingerprint);
        }
        Rc::new(Self {
            fingerprint: fingerprint.finish(),
            node: PackedNode::Production {
                production,
                children,
                metadata,
            },
        })
    }

    #[cfg_attr(not(feature = "z3-inference"), allow(dead_code))]
    fn instantiated_production(
        production: usize,
        parameters: Vec<Sort>,
        children: Vec<Rc<Self>>,
        metadata: TermMetadata,
    ) -> Rc<Self> {
        let mut fingerprint = Fingerprint::new(1);
        fingerprint.write_usize(production);
        fingerprint.write_metadata(&metadata);
        for parameter in &parameters {
            fingerprint.write(parameter.to_string().as_bytes());
        }
        for child in &children {
            fingerprint.write_u64(child.fingerprint);
        }
        Rc::new(Self {
            fingerprint: fingerprint.finish(),
            node: PackedNode::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            },
        })
    }

    fn ambiguity(alternatives: BTreeSet<Rc<Self>>) -> Rc<Self> {
        if alternatives.len() == 1 {
            return alternatives
                .into_iter()
                .next()
                .expect("one packed alternative exists");
        }
        let mut fingerprint = Fingerprint::new(3);
        for alternative in &alternatives {
            fingerprint.write_u64(alternative.fingerprint);
        }
        Rc::new(Self {
            fingerprint: fingerprint.finish(),
            node: PackedNode::Ambiguity(alternatives),
        })
    }

    fn unpack(&self) -> ParsedTerm {
        #[cfg(test)]
        UNPACKED_NODES.set(UNPACKED_NODES.get() + 1);
        match &self.node {
            PackedNode::Production {
                production,
                children,
                metadata,
            } => ParsedTerm::Production {
                production: *production,
                children: children.iter().map(|child| child.unpack()).collect(),
                metadata: metadata.clone(),
            },
            PackedNode::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } => ParsedTerm::InstantiatedProduction {
                production: *production,
                parameters: parameters.clone(),
                children: children.iter().map(|child| child.unpack()).collect(),
                metadata: metadata.clone(),
            },
            PackedNode::Term(term) => ParsedTerm::Term(term.clone()),
            PackedNode::Ambiguity(alternatives) => {
                ParsedTerm::Ambiguity(alternatives.iter().map(|term| term.unpack()).collect())
            }
        }
    }
}

fn cmp_packed_structurally(left: &Rc<PackedTerm>, right: &Rc<PackedTerm>) -> std::cmp::Ordering {
    fn compare(
        left: &Rc<PackedTerm>,
        right: &Rc<PackedTerm>,
        memo: &mut std::collections::HashMap<
            (*const PackedTerm, *const PackedTerm),
            std::cmp::Ordering,
        >,
    ) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        if Rc::ptr_eq(left, right) {
            return Ordering::Equal;
        }
        let key = (Rc::as_ptr(left), Rc::as_ptr(right));
        if let Some(ordering) = memo.get(&key) {
            return *ordering;
        }
        let ordering = match (&left.node, &right.node) {
            (
                PackedNode::Production {
                    production: left_production,
                    children: left_children,
                    metadata: left_metadata,
                },
                PackedNode::Production {
                    production: right_production,
                    children: right_children,
                    metadata: right_metadata,
                },
            ) => left_production
                .cmp(right_production)
                .then_with(|| {
                    left_children
                        .iter()
                        .zip(right_children)
                        .map(|(left, right)| compare(left, right, memo))
                        .find(|ordering| !ordering.is_eq())
                        .unwrap_or_else(|| left_children.len().cmp(&right_children.len()))
                })
                .then_with(|| left_metadata.cmp(right_metadata)),
            (
                PackedNode::InstantiatedProduction {
                    production: left_production,
                    parameters: left_parameters,
                    children: left_children,
                    metadata: left_metadata,
                },
                PackedNode::InstantiatedProduction {
                    production: right_production,
                    parameters: right_parameters,
                    children: right_children,
                    metadata: right_metadata,
                },
            ) => left_production
                .cmp(right_production)
                .then_with(|| left_parameters.cmp(right_parameters))
                .then_with(|| {
                    left_children
                        .iter()
                        .zip(right_children)
                        .map(|(left, right)| compare(left, right, memo))
                        .find(|ordering| !ordering.is_eq())
                        .unwrap_or_else(|| left_children.len().cmp(&right_children.len()))
                })
                .then_with(|| left_metadata.cmp(right_metadata)),
            (PackedNode::Production { .. }, _) => Ordering::Less,
            (_, PackedNode::Production { .. }) => Ordering::Greater,
            (PackedNode::InstantiatedProduction { .. }, _) => Ordering::Less,
            (_, PackedNode::InstantiatedProduction { .. }) => Ordering::Greater,
            (PackedNode::Term(left), PackedNode::Term(right)) => left.cmp(right),
            (PackedNode::Term(_), PackedNode::Ambiguity(_)) => Ordering::Less,
            (PackedNode::Ambiguity(_), PackedNode::Term(_)) => Ordering::Greater,
            (PackedNode::Ambiguity(left), PackedNode::Ambiguity(right)) => {
                let mut left = left.iter().cloned().collect::<Vec<_>>();
                let mut right = right.iter().cloned().collect::<Vec<_>>();
                left.sort_by(|left, right| compare(left, right, memo));
                right.sort_by(|left, right| compare(left, right, memo));
                left.iter()
                    .zip(&right)
                    .map(|(left, right)| compare(left, right, memo))
                    .find(|ordering| !ordering.is_eq())
                    .unwrap_or_else(|| left.len().cmp(&right.len()))
            }
        };
        memo.insert(key, ordering);
        memo.insert((key.1, key.0), ordering.reverse());
        ordering
    }

    compare(left, right, &mut std::collections::HashMap::new())
}

fn packed_terms_in_structural_order(terms: &BTreeSet<Rc<PackedTerm>>) -> Vec<Rc<PackedTerm>> {
    let mut terms = terms.iter().cloned().collect::<Vec<_>>();
    terms.sort_by(cmp_packed_structurally);
    terms
}

fn packed_variable_names(root: &Rc<PackedTerm>) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    let mut visited = HashSet::new();
    let mut pending = vec![Rc::clone(root)];
    while let Some(term) = pending.pop() {
        if !visited.insert(Rc::as_ptr(&term)) {
            continue;
        }
        match &term.node {
            PackedNode::InstantiatedProduction { .. } => {
                unreachable!("instantiated productions are created after variable reservation")
            }
            PackedNode::Term(term) => {
                if let Term::Variable { name, .. } = term.unannotated() {
                    names.insert(name.clone());
                }
            }
            PackedNode::Production { children, .. } => {
                pending.extend(children.iter().cloned());
            }
            PackedNode::Ambiguity(alternatives) => {
                pending.extend(alternatives.iter().cloned());
            }
        }
    }
    names
}

struct Fingerprint(u64);

impl Fingerprint {
    const OFFSET: u64 = 0xcbf29ce484222325;
    const PRIME: u64 = 0x100000001b3;

    fn new(kind: u8) -> Self {
        let mut fingerprint = Self(Self::OFFSET);
        fingerprint.write(&[kind]);
        fingerprint
    }

    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.0 ^= u64::from(*byte);
            self.0 = self.0.wrapping_mul(Self::PRIME);
        }
    }

    fn write_u64(&mut self, value: u64) {
        self.write(&value.to_le_bytes());
    }

    fn write_usize(&mut self, value: usize) {
        self.write_u64(value as u64);
    }

    fn write_metadata(&mut self, metadata: &TermMetadata) {
        if let Some(span) = metadata.span {
            self.write(&[1]);
            self.write_usize(span.source.0);
            self.write_usize(span.start);
            self.write_usize(span.end);
        }
        if let Some(production) = metadata.production {
            self.write(&[2]);
            self.write_usize(production.0);
        }
        if let Some(sort) = &metadata.sort {
            self.write(&[3]);
            self.write(sort.to_string().as_bytes());
        }
        // Chart-produced metadata never carries compiler-origin receipts. Omitting that optional
        // field remains collision-safe because equal fingerprints still compare full metadata.
    }

    fn finish(self) -> u64 {
        self.0
    }
}

#[cfg(test)]
fn reset_packed_structural_comparisons() {
    PACKED_STRUCTURAL_COMPARISONS.set(0);
}

#[cfg(test)]
fn packed_structural_comparisons() -> usize {
    PACKED_STRUCTURAL_COMPARISONS.get()
}

#[cfg(test)]
fn reset_unpacked_nodes() {
    UNPACKED_NODES.set(0);
}

#[cfg(test)]
fn unpacked_nodes() -> usize {
    UNPACKED_NODES.get()
}

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

type Derivation = Vec<Rc<PackedTerm>>;

impl ParsedTerm {
    #[cfg(test)]
    fn leaf(&self) -> Option<&Term> {
        match self {
            Self::Term(term) => Some(term.unannotated()),
            _ => None,
        }
    }
}

/// A reusable inner grammar derived from visible productions.
///
/// Parametric productions are concretized for parsing while retaining a link to
/// their original form for sort inference.
#[derive(Clone, Debug)]
pub struct Grammar {
    productions: Vec<Production>,
    by_result: BTreeMap<Sort, Vec<usize>>,
    scanner: Scanner,
    prediction_analysis: OnceLock<PredictionAnalysis>,
    source_production_texts: BTreeMap<ProductionId, String>,
    layout: Layout,
    priorities: PartialOrder<String>,
    associativities: AssociativityRelations,
    subsort_relations: BTreeSet<(Sort, Sort)>,
    syntactic_subsort_relations: BTreeSet<(Sort, Sort)>,
    overloads: PartialOrder<ProductionId>,
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
            productions: Vec::new(),
            by_result: BTreeMap::new(),
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
    pub(super) fn from_program_sentences<'a>(
        sentences: impl IntoIterator<Item = &'a Sentence>,
        source_catalog: &ProductionCatalog<'_>,
    ) -> Result<Self, ParseError> {
        let mut sentences = sentences.into_iter().cloned().collect::<Vec<_>>();
        // Program grammars parse the empty list as the empty string rather than the
        // `.Sort` terminator. Record each erased terminator's source production at
        // the moment of erasure so the link survives the rewrite.
        let mut erased = Vec::new();
        for sentence in &mut sentences {
            let is_terminator = matches!(
                &*sentence,
                Sentence::Production { items, attributes, .. }
                    if matches!(
                        attributes.get_str("userList"),
                        Some("*") | Some("+")
                    )
                        && !items
                            .iter()
                            .any(|item| matches!(item, ProductionItem::NonTerminal { .. }))
            );
            if !is_terminator {
                continue;
            }
            let source = catalog_production(source_catalog, sentence);
            if let Sentence::Production { items, .. } = sentence {
                items.clear();
            }
            if let Some(source) = source {
                erased.push((sentence.clone(), source));
            }
        }
        Self::from_collected_sentences(
            sentences.iter().collect(),
            Some(SourceLinks {
                catalog: source_catalog,
                erased,
            }),
            ParserRole::Program,
            false,
            None,
        )
    }

    pub fn from_sentences<'a>(
        sentences: impl IntoIterator<Item = &'a Sentence>,
    ) -> Result<Self, ParseError> {
        let sentences = sentences.into_iter().collect::<Vec<_>>();
        Self::from_collected_sentences(sentences, None, ParserRole::Rule, false, None)
    }

    pub(super) fn from_configuration_sentences<'a>(
        sentences: impl IntoIterator<Item = &'a Sentence>,
    ) -> Result<Self, ParseError> {
        let sentences = sentences.into_iter().collect::<Vec<_>>();
        Self::from_collected_sentences(sentences, None, ParserRole::Rule, true, None)
    }

    pub(super) fn from_rule_sentences<'a>(
        sentences: impl IntoIterator<Item = &'a Sentence>,
        source_catalog: &ProductionCatalog<'_>,
        scanner_seed: Option<&Scanner>,
    ) -> Result<Self, ParseError> {
        let sentences = sentences.into_iter().collect::<Vec<_>>();
        Self::from_collected_sentences(
            sentences,
            Some(SourceLinks::catalog(source_catalog)),
            ParserRole::Rule,
            true,
            scanner_seed,
        )
    }

    fn from_collected_sentences(
        sentences: Vec<&Sentence>,
        source_links: Option<SourceLinks<'_, '_>>,
        role: ParserRole,
        include_default_layout: bool,
        scanner_seed: Option<&Scanner>,
    ) -> Result<Self, ParseError> {
        let lexical = sentences
            .iter()
            .filter_map(|sentence| match sentence {
                Sentence::SyntaxLexical { name, regex, .. } => Some((name, regex)),
                _ => None,
            })
            .map(|(name, regex)| {
                parse_regex(regex)
                    .map(|regex| (name.clone(), regex))
                    .map_err(|error| ParseError::InvalidRegex {
                        regex: regex.clone(),
                        message: error.to_string(),
                    })
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        let layout_declared = sentences.iter().any(|sentence| match sentence {
            Sentence::SyntaxSort { sort, .. } | Sentence::Production { sort, .. } => {
                sort.name == "#Layout"
            }
            _ => false,
        });
        let layout_sources = sentences
            .iter()
            .filter_map(|sentence| match sentence {
                Sentence::Production { sort, items, .. } if sort.name == "#Layout" => Some(items),
                _ => None,
            })
            .map(|items| match items.as_slice() {
                [
                    ProductionItem::RegexTerminal {
                        precede_regex: None,
                        regex,
                        follow_regex: None,
                    },
                ] => Ok(regex.clone()),
                _ => Err(ParseError::InvalidLayoutProduction),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let priorities = compute_priorities(sentences.iter().copied())
            .map_err(|cycle| ParseError::CircularPriorities { path: cycle.path })?;
        let associativities = compute_associativities(sentences.iter().copied());
        let semantic_subsorts = match role {
            ParserRole::Program => compute_subsorts(sentences.iter().copied(), false),
            ParserRole::Rule => compute_disambiguation_subsorts(&sentences),
        }
        .map_err(|cycle| ParseError::CircularSubsorts { path: cycle.path })?;
        let overloads = compute_overloads(sentences.iter().copied(), &semantic_subsorts)
            .map_err(|cycle| ParseError::CircularOverloads { path: cycle.path })?;
        let external = source_links.is_some();
        let source_links =
            source_links.unwrap_or_else(|| SourceLinks::catalog(overloads.catalog()));
        let source_production_texts = source_links
            .catalog
            .productions()
            .filter_map(|(id, sentence)| render_production(sentence).map(|text| (id, text)))
            .collect();
        let overload_order = if external {
            let relations = overloads
                .order()
                .direct_relations()
                .iter()
                .filter_map(|(lesser, greater)| {
                    let lesser = source_links.resolve(overloads.catalog().production(*lesser))?;
                    let greater = source_links.resolve(overloads.catalog().production(*greater))?;
                    (lesser != greater).then_some((lesser, greater))
                })
                .collect::<BTreeSet<_>>();
            PartialOrder::new(relations)
                .map_err(|cycle| ParseError::CircularOverloads { path: cycle.path })?
        } else {
            overloads.order().clone()
        };
        let mut grammar = Self {
            scanner: scanner_seed.cloned().unwrap_or_default(),
            source_production_texts,
            layout: if include_default_layout {
                Layout::compile_with_default(&layout_sources, &lexical)?
            } else if layout_declared {
                Layout::compile(&layout_sources, &lexical)?
            } else {
                Layout::default()
            },
            priorities,
            associativities,
            overloads: overload_order,
            role,
            ..Self::default()
        };
        for sentence in &sentences {
            let Sentence::Production {
                label,
                parameters,
                sort,
                items,
                attributes,
            } = *sentence
            else {
                continue;
            };
            if sort.name == "#Layout" {
                continue;
            }
            // RuleGrammarGenerator concretizes these before Earley parsing. The
            // configuration grammar adds the concrete bridge productions it needs.
            if !parameters.is_empty() {
                continue;
            }
            let source_production = source_links.resolve(sentence);
            let source_production_text =
                source_production.and_then(|_| render_production(sentence));
            grammar.add_production_with_lexical(
                sort.clone(),
                items,
                label.clone(),
                ProductionOptions {
                    token: attributes.get("token").is_some(),
                    transparent: attributes.get("bracket").is_some(),
                    bracket: attributes.get("bracket").is_some(),
                    bracket_label: attributes.label("bracketLabel").map(|label| label.name),
                    apply_priority: attributes.get_str("applyPriority"),
                    function: attributes.get("function").is_some(),
                    macro_like: ["macro", "macro-rec", "alias", "alias-rec"]
                        .iter()
                        .any(|key| attributes.get(key).is_some()),
                    prefer: attributes.get("prefer").is_some(),
                    avoid: attributes.get("avoid").is_some(),
                    source_production,
                    source_production_text: source_production_text.as_deref(),
                    source: attributes.source(),
                    location: attributes.location(),
                    user_list: attributes.get("userList").is_some(),
                    user_list_nonempty: attributes.get_str("userList") == Some("+"),
                    precedence: attributes.get_str("prec"),
                    hook: attributes.get_str("hook"),
                    parsing_only_subsort: false,
                },
                &lexical,
            )?;
        }
        grammar.add_parametric_productions(&sentences, &lexical, source_links.catalog)?;
        grammar.initialize_user_lists()?;
        let original_productions = grammar.productions.len();
        for production in 0..original_productions {
            grammar.add_record_productions(production)?;
        }
        grammar.identify_productive_unary_cycles();
        Ok(grammar)
    }

    fn add_chart_state(
        &self,
        chart: &mut Chart,
        state: State,
        derivations: impl IntoIterator<Item = Derivation>,
    ) -> Result<bool, ParseError> {
        let production = &self.productions[state.production];
        let new_state = !chart.states.contains_key(&state);
        let changed = chart.add(state, derivations)?;
        if changed && new_state {
            if let Some(Item::NonTerminal(sort)) = production.items.get(state.dot) {
                chart.waiting.entry(sort.clone()).or_default().push(state);
            } else if state.dot == production.items.len() {
                chart
                    .completed
                    .entry(production.result.clone())
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
        let ParseContext {
            is_anywhere,
            provenance,
            diagnostic_provenance,
        } = context;
        #[cfg(test)]
        PARSE_ATTEMPTS.set(PARSE_ATTEMPTS.get() + 1);
        let prediction_analysis = (prediction_mode == PredictionMode::Filtered).then(|| {
            self.prediction_analysis
                .get_or_init(|| PredictionAnalysis::new(self))
        });
        let mut charts = (0..=input.len())
            .map(|_| Chart::default())
            .collect::<Vec<_>>();
        let mut scanner_cache = vec![None; input.len() + 1];
        let start_position = self.canonical_position(input, 0, &mut scanner_cache);
        for production in self.productions_for(start) {
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
        charts[start_position].predicted.insert(start.clone());
        let mut first_violation = None;

        for position in start_position..=input.len() {
            // Empty charts can lie inside a UTF-8 character; only evaluate layout on dispatch.
            let mut canonical_position = None;
            while let Some(state) = charts[position].agenda.pop_front() {
                #[cfg(test)]
                let revisit = {
                    let revisit = !charts[position].popped.insert(state);
                    update_chart_work_counters(|counters| {
                        counters.agenda_pops += 1;
                        if revisit {
                            counters.revisit_pops += 1;
                        }
                    });
                    revisit
                };
                let Some(derivations) = charts[position].states.get(&state).cloned() else {
                    continue;
                };
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
                    Some(Item::NonTerminal(sort)) => {
                        #[cfg(test)]
                        record_chart_dispatch(
                            ChartDispatchKind::Nonterminal,
                            derivation_count,
                            revisit,
                        );
                        if charts[position].predicted.insert(sort.clone()) {
                            for predicted in self.productions_for(sort) {
                                if let Some(analysis) = prediction_analysis
                                    && analysis.can_filter(predicted, &charts[position].predicted)
                                    && analysis.cannot_start(
                                        predicted,
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
                                            }),
                                    )
                                {
                                    #[cfg(test)]
                                    if matches!(
                                        self.productions[predicted].items.first(),
                                        Some(Item::NonTerminal(_))
                                    ) {
                                        NONTERMINAL_PREDICTIONS_SKIPPED
                                            .set(NONTERMINAL_PREDICTIONS_SKIPPED.get() + 1);
                                    } else {
                                        TERMINAL_PREDICTIONS_SKIPPED
                                            .set(TERMINAL_PREDICTIONS_SKIPPED.get() + 1);
                                    }
                                    // This bucket's initial state would be new. Preserve its
                                    // snapshot invalidation so packed sharing and anonymous
                                    // inference identities follow the unfiltered parse.
                                    charts[position].invalidate_completed_nodes();
                                    *pruned = true;
                                    continue;
                                }
                                #[cfg(test)]
                                CHART_PREDICTION_ATTEMPTS.set(CHART_PREDICTION_ATTEMPTS.get() + 1);
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
                            sort,
                            position,
                            position,
                            input,
                            provenance,
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
                            #[cfg(test)]
                            {
                                CHART_COMPLETION_CANDIDATES
                                    .set(CHART_COMPLETION_CANDIDATES.get() + 1);
                                update_chart_work_counters(|counters| {
                                    counters.primary_completion_candidates += 1;
                                });
                            }
                            let term = build_packed_term(
                                state.production,
                                production,
                                children,
                                input,
                                state.origin,
                                position,
                                provenance,
                            );
                            match self.filter_or_defer_packed_priority(Rc::clone(&term)) {
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
                            .get(&production.result)
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
                start,
                start_position,
                position,
                input,
                provenance,
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
        // Java applies `PriorityVisitor` to the packed root ambiguity. Its rewrite/sequence/let
        // preference must therefore run before descending into losing alternatives; filtering
        // each root independently incorrectly rejects inputs whose winning interpretation is a
        // top-level rewrite (for example a rewrite inside a competing map-item parse).
        let forest = self.prepare_packed_forest(PackedTerm::ambiguity(parses))?;
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
    fn prepare_packed_forest(&self, forest: Rc<PackedTerm>) -> Result<Rc<PackedTerm>, ParseError> {
        let reserved_names = packed_variable_names(&forest);
        let forest = self.collapse_packed_record_productions(forest, reserved_names)?;
        let forest = self.filter_packed_priority(forest)?;
        let forest = self.resolve_packed_applications(forest)?;
        let forest = self.factor_pre_inference_packed_ambiguities(forest);
        let forest = self.push_top_lhs_packed_ambiguity_up(forest);
        Ok(forest)
    }

    #[cfg(test)]
    fn materialize_packed_forest(&self, forest: Rc<PackedTerm>) -> Result<ParsedTerm, ParseError> {
        Ok(self.prepare_packed_forest(forest)?.unpack())
    }

    pub(crate) fn add(
        &mut self,
        result: Sort,
        items: Vec<ProductionItem>,
        label: Option<Label>,
        token: bool,
        transparent: bool,
    ) -> Result<(), ParseError> {
        self.add_production(result, &items, label, token, transparent)
    }

    pub(crate) fn add_with_source_text(
        &mut self,
        result: Sort,
        items: Vec<ProductionItem>,
        label: Option<Label>,
        token: bool,
        transparent: bool,
        source_production_text: &str,
    ) -> Result<(), ParseError> {
        self.add_production_with_lexical(
            result,
            &items,
            label,
            ProductionOptions {
                token,
                transparent,
                source_production_text: Some(source_production_text),
                ..ProductionOptions::default()
            },
            &BTreeMap::new(),
        )
    }

    pub(crate) fn add_token_with_precedence(
        &mut self,
        result: Sort,
        item: ProductionItem,
        precedence: &str,
    ) -> Result<(), ParseError> {
        self.prediction_analysis.take();
        if self.has_equivalent_production(&result, std::slice::from_ref(&item), true) {
            let compiled = compile_item(&item, &BTreeMap::new())?;
            self.scanner.register(
                &compiled,
                Some(precedence),
                TokenPrecedenceDeclaration {
                    source: None,
                    location: None,
                    production: render_added_production(
                        &result,
                        std::slice::from_ref(&item),
                        true,
                        Some(precedence),
                    ),
                    precedence: 0,
                },
            )?;
            return Ok(());
        }
        self.add_production_with_lexical(
            result,
            &[item],
            None,
            ProductionOptions {
                token: true,
                precedence: Some(precedence),
                ..ProductionOptions::default()
            },
            &BTreeMap::new(),
        )
    }

    pub(crate) fn add_token_subsort(
        &mut self,
        result: impl Into<String>,
        child: impl Into<String>,
    ) -> Result<(), ParseError> {
        let result = Sort::new(result);
        let item = ProductionItem::NonTerminal {
            sort: Sort::new(child),
            name: None,
        };
        if self.has_equivalent_production(&result, std::slice::from_ref(&item), true) {
            return Ok(());
        }
        self.add_production_with_lexical(
            result,
            &[item],
            None,
            ProductionOptions {
                token: true,
                ..ProductionOptions::default()
            },
            &BTreeMap::new(),
        )
    }

    pub(crate) fn has_equivalent_production(
        &self,
        result: &Sort,
        items: &[ProductionItem],
        token: bool,
    ) -> bool {
        self.productions.iter().any(|production| {
            &production.result == result
                && production.declared_items == items
                && production.token == token
        })
    }

    #[cfg(test)]
    pub(crate) fn equivalent_production_count(
        &self,
        result: &Sort,
        items: &[ProductionItem],
        token: bool,
    ) -> usize {
        self.productions
            .iter()
            .filter(|production| {
                &production.result == result
                    && production.declared_items == items
                    && production.token == token
            })
            .count()
    }

    pub(super) fn scanner(&self) -> &Scanner {
        &self.scanner
    }

    pub(crate) fn add_bracket(
        &mut self,
        result: Sort,
        items: Vec<ProductionItem>,
        source_attributes: Option<&Attributes>,
    ) -> Result<(), ParseError> {
        // Parametric source brackets have already been instantiated in this grammar.
        // Preserve their parse label and applyPriority contract: an untagged fallback
        // with the same syntax would keep alternatives that the source bracket rejects.
        if self.productions_for(&result).any(|index| {
            let production = &self.productions[index];
            production.bracket && production.declared_items == items
        }) {
            return Ok(());
        }
        let bracket_label = source_attributes
            .and_then(|attributes| attributes.label("bracketLabel"))
            .map_or_else(|| format!("#bracket:{result}"), |label| label.name);
        self.add_production_with_lexical(
            result,
            &items,
            None,
            ProductionOptions {
                transparent: true,
                bracket: true,
                bracket_label: Some(bracket_label),
                apply_priority: source_attributes
                    .and_then(|attributes| attributes.get_str("applyPriority")),
                ..ProductionOptions::default()
            },
            &BTreeMap::new(),
        )
    }

    pub(crate) fn add_left_associative(&mut self, label: impl Into<String>) {
        let label = label.into();
        self.associativities.left.insert((label.clone(), label));
    }

    #[cfg(test)]
    pub(crate) fn add_right_associative(&mut self, label: impl Into<String>) {
        let label = label.into();
        self.associativities.right.insert((label.clone(), label));
    }

    pub(super) fn add_matching_terminal_tokens(
        &mut self,
        result: Sort,
        predicate: impl Fn(&str) -> bool,
    ) -> Result<(), ParseError> {
        let terminals = self
            .productions
            .iter()
            .flat_map(|production| &production.items)
            .filter_map(|item| match item {
                Item::Terminal(value) if predicate(value) => Some(value.clone()),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        for terminal in terminals {
            self.add(
                result.clone(),
                vec![ProductionItem::Terminal(terminal)],
                None,
                true,
                false,
            )?;
        }
        Ok(())
    }

    fn identify_productive_unary_cycles(&mut self) {
        let edges = self
            .productions
            .iter()
            .filter_map(|production| match production.items.as_slice() {
                [Item::NonTerminal(child)] => Some((production.result.clone(), child.clone())),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        self.productive_unary_cycles = self
            .productions
            .iter()
            .enumerate()
            .filter_map(|(index, production)| {
                let [Item::NonTerminal(child)] = production.items.as_slice() else {
                    return None;
                };
                (production.label.is_some()
                    && !production.transparent
                    && unary_reachable(child, &production.result, &edges))
                .then_some(index)
            })
            .collect();
    }

    fn add_production(
        &mut self,
        result: Sort,
        items: &[ProductionItem],
        label: Option<Label>,
        token: bool,
        transparent: bool,
    ) -> Result<(), ParseError> {
        self.add_production_with_lexical(
            result,
            items,
            label,
            ProductionOptions {
                token,
                transparent,
                ..ProductionOptions::default()
            },
            &BTreeMap::new(),
        )
    }

    fn add_production_with_lexical(
        &mut self,
        result: Sort,
        items: &[ProductionItem],
        label: Option<Label>,
        options: ProductionOptions<'_>,
        lexical: &BTreeMap<String, KRegex>,
    ) -> Result<(), ParseError> {
        // Registration of an earlier item can survive a later compile/attribute failure.
        self.prediction_analysis.take();
        let declared_items = items
            .iter()
            .filter(|item| !matches!(item, ProductionItem::Terminal(value) if value.is_empty()))
            .cloned()
            .collect();
        let field_names = items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { name, .. } => Some(name.clone()),
                ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
            })
            .collect();
        let declaration = TokenPrecedenceDeclaration {
            source: options.source.map(str::to_owned),
            location: options.location,
            production: options.source_production_text.map_or_else(
                || render_added_production(&result, items, options.token, options.precedence),
                str::to_owned,
            ),
            precedence: 0,
        };
        let mut compiled_items = Vec::new();
        for item in items
            .iter()
            .filter(|item| !matches!(item, ProductionItem::Terminal(value) if value.is_empty()))
        {
            let item = compile_item(item, lexical)?;
            self.scanner
                .register(&item, options.precedence, declaration.clone())?;
            compiled_items.push(item);
        }
        let items = compiled_items;
        let index = self.productions.len();
        // Java's `Production.isSyntacticSubsort` is purely shape-based; unlike `isSubsort`,
        // it does not require the production to be unlabeled. Priority filtering uses the
        // former, while the semantic subsort relation uses the latter.
        let syntactic_subsort =
            !options.bracket && matches!(items.as_slice(), [Item::NonTerminal(_)]);
        let parse_label = label
            .as_ref()
            .map(|label| label.name.clone())
            .or_else(|| options.bracket_label.clone())
            .or_else(|| {
                options
                    .bracket
                    .then(|| format!("#bracket:{result}:{index}"))
            });
        let apply_priority = options
            .apply_priority
            .map(parse_apply_priority)
            .transpose()?;
        if label.is_none()
            && syntactic_subsort
            && !options.parsing_only_subsort
            && let [Item::NonTerminal(child)] = items.as_slice()
        {
            self.subsort_relations
                .insert((child.clone(), result.clone()));
        }
        if !options.bracket
            && !options.parsing_only_subsort
            && let [Item::NonTerminal(child)] = items.as_slice()
        {
            self.syntactic_subsort_relations
                .insert((child.clone(), result.clone()));
        }
        self.productions.push(Production {
            result: result.clone(),
            declared_items,
            items,
            label,
            token: options.token,
            transparent: options.transparent,
            bracket: options.bracket,
            syntactic_subsort,
            parse_label,
            apply_priority,
            function: options.function,
            macro_like: options.macro_like,
            prefer: options.prefer,
            avoid: options.avoid,
            source_production: options.source_production,
            source_production_text: options.source_production_text.map(str::to_owned),
            user_list: options.user_list,
            user_list_nonempty: options.user_list_nonempty,
            field_names,
            record: None,
            parametric_origin: None,
            term_production: None,
            hook: options.hook.map(str::to_owned),
        });
        self.by_result.entry(result).or_default().push(index);
        Ok(())
    }

    fn productions_for(&self, sort: &Sort) -> impl Iterator<Item = usize> + '_ {
        self.by_result.get(sort).into_iter().flatten().copied()
    }

    fn canonical_position(
        &self,
        input: &str,
        mut position: usize,
        scanner_cache: &mut [ScanCacheEntry],
    ) -> usize {
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

/// Links from grammar sentences back to the source production catalog.
struct SourceLinks<'c, 'a> {
    catalog: &'c ProductionCatalog<'a>,
    /// Sentences rewritten by the program grammar, paired with the source
    /// production they were derived from.
    erased: Vec<(Sentence, ProductionId)>,
}

impl<'c, 'a> SourceLinks<'c, 'a> {
    fn catalog(catalog: &'c ProductionCatalog<'a>) -> Self {
        Self {
            catalog,
            erased: Vec::new(),
        }
    }

    fn resolve(&self, sentence: &Sentence) -> Option<ProductionId> {
        self.erased
            .iter()
            .find_map(|(erased, source)| (erased == sentence).then_some(*source))
            .or_else(|| catalog_production(self.catalog, sentence))
    }
}

/// `GenerateSortProjections.gen(Production)` as `RuleGrammarGenerator.getCombinedGrammar`
/// (RuleGrammarGenerator.java:400-401) applies it to every production of a parsing module,
/// rules and programs alike: one function production `Field ::= name "(" Sort ")"` labelled
/// `project:<klabel>:<name>` per named nonterminal of a labelled production that is neither a
/// function nor a macro, unless the module already defines one of those labels itself. The
/// projection rules are the kompile pass's; a parsing grammar needs only the syntax.
pub(super) fn named_projection_productions<'a>(
    sentences: impl IntoIterator<Item = &'a Sentence>,
) -> Vec<Sentence> {
    let sentences = sentences.into_iter().collect::<Vec<_>>();
    let defined = sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label), ..
            } => Some(label.name.as_str()),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let mut generated = Vec::new();
    for sentence in &sentences {
        let Sentence::Production {
            label: Some(label),
            sort,
            items,
            attributes,
            ..
        } = sentence
        else {
            continue;
        };
        if attributes.get("function").is_some() || crate::definition::catalog::is_macro(attributes)
        {
            continue;
        }
        let fields = items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal {
                    sort,
                    name: Some(name),
                } => Some((sort, name)),
                _ => None,
            })
            .collect::<Vec<_>>();
        if fields.is_empty()
            || fields.iter().any(|(_, name)| {
                defined.contains(format!("project:{}:{name}", label.name).as_str())
            })
        {
            continue;
        }
        for (field_sort, name) in fields {
            let mut generated_attributes = Attributes::default();
            generated_attributes.insert("function", serde_json::json!(""));
            generated_attributes.insert("generatedRuleSyntax", serde_json::json!(""));
            generated.push(Sentence::Production {
                label: Some(Label::new(format!("project:{}:{name}", label.name))),
                parameters: Vec::new(),
                sort: field_sort.clone(),
                items: vec![
                    ProductionItem::Terminal(name.clone()),
                    ProductionItem::Terminal("(".into()),
                    ProductionItem::NonTerminal {
                        sort: sort.clone(),
                        name: None,
                    },
                    ProductionItem::Terminal(")".into()),
                ],
                attributes: generated_attributes,
            });
        }
    }
    generated
}

fn catalog_production(
    catalog: &ProductionCatalog<'_>,
    sentence: &Sentence,
) -> Option<ProductionId> {
    if matches!(sentence, Sentence::Production { attributes, .. } if attributes.get("generatedRuleSyntax").is_some())
    {
        return None;
    }
    catalog
        .productions()
        .find_map(|(id, candidate)| sentence_equivalent(candidate, sentence).then_some(id))
}

fn render_production(sentence: &Sentence) -> Option<String> {
    let Sentence::Production {
        parameters,
        sort,
        items,
        attributes,
        ..
    } = sentence
    else {
        return None;
    };
    let parameters = if parameters.is_empty() {
        String::new()
    } else {
        format!(
            "{{{}}} ",
            parameters
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    let items = items
        .iter()
        .map(render_production_item)
        .collect::<Vec<_>>()
        .join(" ");
    let attributes = attributes
        .entries()
        .iter()
        .filter(|(key, _)| {
            !matches!(
                key.as_str(),
                "org.kframework.attributes.Source"
                    | "org.kframework.attributes.Location"
                    | "org.kframework.attributes.SourceId"
                    | "org.krust.provenance.SentenceStartOffset"
                    | "org.krust.provenance.SentenceEndOffset"
            )
        })
        .map(|(key, value)| match value {
            serde_json::Value::String(value) if value.is_empty() => key.clone(),
            serde_json::Value::Null => key.clone(),
            serde_json::Value::String(value) => format!("{key}({value})"),
            value => format!("{key}({value})"),
        })
        .collect::<Vec<_>>();
    let attributes = if attributes.is_empty() {
        String::new()
    } else {
        format!(" [{}]", attributes.join(", "))
    };
    Some(format!("syntax {parameters}{sort} ::= {items}{attributes}"))
}

fn render_added_production(
    result: &Sort,
    items: &[ProductionItem],
    token: bool,
    precedence: Option<&str>,
) -> String {
    let items = items
        .iter()
        .map(render_production_item)
        .collect::<Vec<_>>()
        .join(" ");
    let mut attributes = Vec::new();
    if token {
        attributes.push("token".to_owned());
    }
    if let Some(precedence) = precedence {
        attributes.push(format!("prec({precedence})"));
    }
    let attributes = if attributes.is_empty() {
        String::new()
    } else {
        format!(" [{}]", attributes.join(", "))
    };
    format!("syntax {result} ::= {items}{attributes}")
}

fn render_production_item(item: &ProductionItem) -> String {
    match item {
        ProductionItem::NonTerminal { sort, name } => name
            .as_ref()
            .map_or_else(|| sort.to_string(), |name| format!("{name}:{sort}")),
        ProductionItem::RegexTerminal { regex, .. } => {
            format!("r{}", crate::kast::string::quote(regex))
        }
        ProductionItem::Terminal(value) => crate::kast::string::quote(value),
    }
}

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

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct State {
    production: usize,
    dot: usize,
    origin: usize,
}

type CompletedNodeKey = (Sort, usize, usize, SourceId, usize);
type CompletedNodeResult = (BTreeSet<Rc<PackedTerm>>, Option<ParseError>);

#[derive(Clone, Debug)]
struct Chart {
    states: BTreeMap<State, Derivations>,
    // Each bucket is considered once at this position. Its marker also permits omission of
    // impossible callers that would not expand the same bucket again. Caller-specific nullable
    // completion must still run on every request.
    predicted: BTreeSet<Sort>,
    waiting: BTreeMap<Sort, Vec<State>>,
    completed: BTreeMap<Sort, Vec<State>>,
    agenda: VecDeque<State>,
    #[cfg(test)]
    popped: BTreeSet<State>,
    // Java exposes one completed node for each stable (sort, origin, end) chart boundary. Retain
    // that identity until the chart changes; `add` invalidates this snapshot before reprocessing.
    completed_nodes: RefCell<BTreeMap<CompletedNodeKey, CompletedNodeResult>>,
}

impl Default for Chart {
    fn default() -> Self {
        Self {
            states: BTreeMap::new(),
            predicted: BTreeSet::new(),
            waiting: BTreeMap::new(),
            completed: BTreeMap::new(),
            agenda: VecDeque::new(),
            #[cfg(test)]
            popped: BTreeSet::new(),
            completed_nodes: RefCell::new(BTreeMap::new()),
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
enum Derivations {
    #[default]
    Empty,
    One(Derivation),
    Many(BTreeSet<Derivation>),
}

impl Derivations {
    fn insert(&mut self, candidate: Derivation) -> bool {
        match std::mem::take(self) {
            Self::Empty => {
                *self = Self::One(candidate);
                true
            }
            Self::One(existing) => {
                if derivation_covers(&existing, &candidate) {
                    *self = Self::One(existing);
                    false
                } else if derivation_covers(&candidate, &existing) {
                    *self = Self::One(candidate);
                    true
                } else {
                    let mut stored = BTreeSet::from([existing, candidate]);
                    factor_derivations(&mut stored);
                    *self = Self::from_set(stored);
                    true
                }
            }
            Self::Many(mut stored) => {
                if stored
                    .iter()
                    .any(|existing| derivation_covers(existing, &candidate))
                {
                    *self = Self::Many(stored);
                    return false;
                }
                stored.retain(|existing| !derivation_covers(&candidate, existing));
                stored.insert(candidate);
                factor_derivations(&mut stored);
                *self = Self::from_set(stored);
                true
            }
        }
    }

    fn from_set(mut stored: BTreeSet<Derivation>) -> Self {
        if stored.len() == 1 {
            Self::One(stored.pop_first().expect("one derivation exists"))
        } else if stored.is_empty() {
            Self::Empty
        } else {
            Self::Many(stored)
        }
    }

    fn iter(&self) -> DerivationIter<'_> {
        match self {
            Self::Empty => DerivationIter::Empty,
            Self::One(derivation) => DerivationIter::One(Some(derivation)),
            Self::Many(derivations) => DerivationIter::Many(derivations.iter()),
        }
    }

    #[cfg(test)]
    fn len(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::One(_) => 1,
            Self::Many(derivations) => derivations.len(),
        }
    }
}

enum DerivationIter<'a> {
    Empty,
    One(Option<&'a Derivation>),
    Many(std::collections::btree_set::Iter<'a, Derivation>),
}

impl<'a> Iterator for DerivationIter<'a> {
    type Item = &'a Derivation;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Empty => None,
            Self::One(derivation) => derivation.take(),
            Self::Many(derivations) => derivations.next(),
        }
    }
}

impl<'a> IntoIterator for &'a Derivations {
    type Item = &'a Derivation;
    type IntoIter = DerivationIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

enum DerivationIntoIter {
    Empty,
    One(Option<Derivation>),
    Many(std::collections::btree_set::IntoIter<Derivation>),
}

impl Iterator for DerivationIntoIter {
    type Item = Derivation;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Empty => None,
            Self::One(derivation) => derivation.take(),
            Self::Many(derivations) => derivations.next(),
        }
    }
}

impl IntoIterator for Derivations {
    type Item = Derivation;
    type IntoIter = DerivationIntoIter;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Self::Empty => DerivationIntoIter::Empty,
            Self::One(derivation) => DerivationIntoIter::One(Some(derivation)),
            Self::Many(derivations) => DerivationIntoIter::Many(derivations.into_iter()),
        }
    }
}

impl Chart {
    fn invalidate_completed_nodes(&mut self) {
        let completed_nodes = self.completed_nodes.get_mut();
        #[cfg(test)]
        update_chart_work_counters(|counters| {
            counters.completed_nodes_invalidation_entries += completed_nodes.len();
        });
        completed_nodes.clear();
    }

    fn add(
        &mut self,
        state: State,
        derivations: impl IntoIterator<Item = Derivation>,
    ) -> Result<bool, ParseError> {
        #[cfg(test)]
        update_chart_work_counters(|counters| counters.add_calls += 1);
        let mut derivations = derivations.into_iter().peekable();
        if derivations.peek().is_none() {
            return Ok(false);
        }
        #[cfg(test)]
        let new_state = !self.states.contains_key(&state);
        let stored = self.states.entry(state).or_default();
        let mut changed = false;
        for derivation in derivations {
            changed |= stored.insert(derivation);
        }
        if !changed {
            return Ok(false);
        }
        #[cfg(test)]
        update_chart_work_counters(|counters| {
            if new_state {
                counters.new_state_changes += 1;
            } else {
                counters.existing_state_growth_changes += 1;
            }
            counters.agenda_enqueues += 1;
        });
        self.invalidate_completed_nodes();
        self.agenda.push_back(state);
        Ok(true)
    }
}

fn derivation_covers(existing: &[Rc<PackedTerm>], candidate: &[Rc<PackedTerm>]) -> bool {
    existing.len() == candidate.len()
        && existing
            .iter()
            .zip(candidate)
            .all(|(existing, candidate)| parsed_term_covers(existing.as_ref(), candidate.as_ref()))
}

fn parsed_term_covers(existing: &PackedTerm, candidate: &PackedTerm) -> bool {
    match (&existing.node, &candidate.node) {
        (PackedNode::Ambiguity(existing), PackedNode::Ambiguity(candidate)) => {
            candidate.is_subset(existing)
        }
        (PackedNode::Ambiguity(existing), _) => existing.contains(candidate),
        (_, PackedNode::Ambiguity(candidate)) => {
            candidate.len() == 1 && candidate.contains(existing)
        }
        (existing, candidate) => existing == candidate,
    }
}

/// Pack derivations that use the same child boundaries.
///
/// For a fixed production and a fixed sequence of child spans, every parse of one child can be
/// combined independently with every parse of the other children. Keeping those combinations as
/// separate vectors materializes the Cartesian product that a packed parse forest is meant to
/// share. Different boundary sequences remain separate because combining those could splice
/// overlapping parses into a tree the grammar never recognized. A derivation with an unspanned
/// child has no boundaries to compare and is retained as it is.
///
/// Coverage-aware insertion and factoring are complementary: coverage removes whole derivations
/// subsumed by an existing ambiguity, while factoring creates that shared ambiguity from sibling
/// derivations with identical boundaries.
fn factor_derivations(derivations: &mut BTreeSet<Derivation>) {
    if derivations.len() < 2 {
        return;
    }

    let mut groups = BTreeMap::<Vec<TermSpan>, Vec<Derivation>>::new();
    let mut unspanned = BTreeSet::new();
    for derivation in std::mem::take(derivations) {
        match derivation
            .iter()
            .map(|node| packed_term_span(node))
            .collect::<Option<Vec<_>>>()
        {
            Some(spans) => groups.entry(spans).or_default().push(derivation),
            None => {
                unspanned.insert(derivation);
            }
        }
    }
    for (spans, group) in groups {
        if group.len() == 1 {
            derivations.extend(group);
            continue;
        }
        let packed = (0..spans.len())
            .map(|index| {
                pack_alternatives(
                    group
                        .iter()
                        .map(|derivation| Rc::clone(&derivation[index]))
                        .collect(),
                )
            })
            .collect();
        derivations.insert(packed);
    }
    derivations.extend(unspanned);
}

fn packed_term_span(term: &PackedTerm) -> Option<TermSpan> {
    match &term.node {
        PackedNode::Production { metadata, .. }
        | PackedNode::InstantiatedProduction { metadata, .. } => metadata.span,
        PackedNode::Term(term) => term.metadata().and_then(|metadata| metadata.span),
        PackedNode::Ambiguity(alternatives) => {
            let mut spans = alternatives
                .iter()
                .map(|alternative| packed_term_span(alternative));
            let span = spans.next().flatten()?;
            spans
                .all(|candidate| candidate == Some(span))
                .then_some(span)
        }
    }
}

fn pack_alternatives(mut nodes: BTreeSet<Rc<PackedTerm>>) -> Rc<PackedTerm> {
    if nodes.len() == 1 {
        return nodes.pop_first().expect("one alternative exists");
    }
    let mut alternatives = BTreeSet::new();
    for node in nodes {
        match &node.node {
            PackedNode::Ambiguity(nested) => alternatives.extend(nested.iter().cloned()),
            _ => {
                alternatives.insert(node);
            }
        }
    }
    PackedTerm::ambiguity(alternatives)
}

fn unary_reachable(start: &Sort, target: &Sort, edges: &BTreeSet<(Sort, Sort)>) -> bool {
    let mut pending = vec![start.clone()];
    let mut visited = BTreeSet::new();
    while let Some(sort) = pending.pop() {
        if &sort == target {
            return true;
        }
        if !visited.insert(sort.clone()) {
            continue;
        }
        pending.extend(
            edges
                .iter()
                .filter(|(from, _)| from == &sort)
                .map(|(_, to)| to.clone()),
        );
    }
    false
}

fn completed_nodes(
    chart: &Chart,
    grammar: &Grammar,
    sort: &Sort,
    origin: usize,
    end: usize,
    input: &str,
    provenance: ParseProvenance,
) -> (BTreeSet<Rc<PackedTerm>>, Option<ParseError>) {
    #[cfg(test)]
    update_chart_work_counters(|counters| counters.completed_nodes_calls += 1);
    let key = (
        sort.clone(),
        origin,
        end,
        provenance.source,
        provenance.base_offset,
    );
    if let Some(completed) = chart.completed_nodes.borrow().get(&key) {
        #[cfg(test)]
        update_chart_work_counters(|counters| counters.completed_nodes_hits += 1);
        return completed.clone();
    }
    #[cfg(test)]
    update_chart_work_counters(|counters| counters.completed_nodes_misses += 1);
    let mut nodes = BTreeSet::new();
    let mut invalid = Vec::new();
    for state in chart.completed.get(sort).into_iter().flatten() {
        if state.origin != origin {
            continue;
        }
        let derivations = &chart.states[state];
        let production = &grammar.productions[state.production];
        for children in derivations {
            #[cfg(test)]
            {
                CHART_COMPLETION_CANDIDATES.set(CHART_COMPLETION_CANDIDATES.get() + 1);
                update_chart_work_counters(|counters| {
                    counters.helper_completion_candidates += 1;
                });
            }
            let term = build_packed_term(
                state.production,
                production,
                children,
                input,
                state.origin,
                end,
                provenance,
            );
            match grammar.filter_or_defer_packed_priority(Rc::clone(&term)) {
                Ok(term) => {
                    nodes.insert(term);
                }
                Err(error) => {
                    invalid.push((term, error));
                }
            }
        }
    }
    let violation = (!invalid.is_empty()).then(|| canonical_packed_error(invalid));
    let completed = (nodes, violation);
    chart
        .completed_nodes
        .borrow_mut()
        .insert(key, completed.clone());
    completed
}

fn canonical_packed_error(errors: Vec<(Rc<PackedTerm>, ParseError)>) -> ParseError {
    errors
        .into_iter()
        .min_by(|(left, _), (right, _)| cmp_packed_structurally(left, right))
        .map(|(_, error)| error)
        .expect("an empty packed ambiguity had no invalid alternative")
}

fn append_nodes(
    derivations: &Derivations,
    nodes: &BTreeSet<Rc<PackedTerm>>,
) -> BTreeSet<Derivation> {
    let node = (!nodes.is_empty()).then(|| pack_alternatives(nodes.clone()));
    derivations
        .iter()
        .filter_map(|derivation| {
            let mut combined = derivation.clone();
            combined.push(node.clone()?);
            Some(combined)
        })
        .collect()
}

fn build_packed_term(
    production_index: usize,
    production: &Production,
    children: &[Rc<PackedTerm>],
    input: &str,
    start: usize,
    end: usize,
    provenance: ParseProvenance,
) -> Rc<PackedTerm> {
    if production.token {
        if production.result.name == "#KVariable" {
            return PackedTerm::leaf(
                Term::Variable {
                    name: input[start..end].to_owned(),
                    sort: None,
                }
                .with_metadata(term_metadata(
                    production,
                    provenance.source,
                    provenance.base_offset + start,
                    provenance.base_offset + end,
                )),
            );
        }
        let token = &input[start..end];
        // EarleyParser substitutes the digits after the first `p`/`P` of a MINT.literal token
        // into the parametric production, so `0p32` is an `MInt{32}` whichever declared
        // instantiation scanned it; the metadata still names the scanning production.
        let sort = if production.is_mint_literal() {
            mint_literal_sort(&production.result, token)
        } else {
            production.result.clone()
        };
        return PackedTerm::leaf(
            Term::Token {
                token: token.to_owned(),
                sort,
            }
            .with_metadata(term_metadata(
                production,
                provenance.source,
                provenance.base_offset + start,
                provenance.base_offset + end,
            )),
        );
    }
    if production.record.is_none()
        && !production.bracket
        && (production.transparent || production.label.is_none())
        && let [child] = children
    {
        return Rc::clone(child);
    }
    PackedTerm::production(
        production.term_production.unwrap_or(production_index),
        children.to_vec(),
        term_metadata(
            production,
            provenance.source,
            provenance.base_offset + start,
            provenance.base_offset + end,
        ),
    )
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
        production: production
            .source_production
            .map(|production| ResolvedProductionId(production.0)),
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
    if label.name == "#OuterCast" {
        label = Label::new(format!("project:{}", production.result));
    }
    if label.name == "#KToken"
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
    match (label.name.as_str(), children) {
        ("#EmptyK", []) => Term::Sequence(Vec::new()),
        ("#KSequence", items) => Term::sequence(items.iter().cloned()),
        ("#KRewrite", [left, right]) => Term::Rewrite {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        },
        ("#KAs", [pattern, alias]) => Term::As {
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
        Term::Token { token, sort } if sort.name == "KString" => Some(token),
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
            assert_eq!(metadata.production, Some(ResolvedProductionId(65)));
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

        #[test]
        fn retains_productive_cycles_after_a_viable_prefix() {
            let grammar = Grammar::from_sentences(&[
                production(
                    "Start",
                    vec![ProductionItem::Terminal("x".into()), nonterminal("Tail")],
                    "start",
                ),
                production(
                    "Tail",
                    vec![nonterminal("Cycle"), ProductionItem::Terminal("z".into())],
                    "tail",
                ),
                production(
                    "Tail",
                    vec![ProductionItem::Terminal("dead".into())],
                    "dead",
                ),
                production("Cycle", vec![nonterminal("Cycle")], "wrap"),
                production("Cycle", vec![], "unit"),
            ])
            .unwrap();
            for input in ["x", "x y"] {
                assert_eq!(
                    unfiltered(&grammar, "Start", input),
                    Err(ParseError::CyclicParseForest)
                );
                PARSE_ATTEMPTS.set(0);
                assert_eq!(
                    grammar.parse(&Sort::new("Start"), input),
                    Err(ParseError::CyclicParseForest)
                );
                assert_eq!(PARSE_ATTEMPTS.get(), 2);
            }
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

    fn ambiguity(names: &[&str]) -> ParsedTerm {
        ParsedTerm::Ambiguity(names.iter().map(|name| variable(name)).collect())
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
    fn completed_parent_reuses_its_packed_child_allocation() {
        let mut grammar = Grammar::default();
        grammar
            .add(
                Sort::new("Parent"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("Child"),
                    name: None,
                }],
                Some(Label::new("parent")),
                false,
                false,
            )
            .unwrap();
        grammar
            .add(
                Sort::new("Child"),
                Vec::new(),
                Some(Label::new("child")),
                false,
                false,
            )
            .unwrap();
        let child = PackedTerm::production(1, Vec::new(), TermMetadata::default());
        let parent = build_packed_term(
            0,
            &grammar.productions[0],
            std::slice::from_ref(&child),
            "child",
            0,
            5,
            ParseProvenance {
                source: SourceId(0),
                base_offset: 0,
            },
        );
        let parent = grammar
            .filter_or_defer_packed_priority(parent)
            .expect("packed parent satisfies priority");
        let PackedNode::Production { children, .. } = &parent.node else {
            panic!("expected packed production");
        };

        assert!(Rc::ptr_eq(&children[0], &child));
    }

    #[test]
    fn completed_nodes_are_canonical_for_their_chart_boundary() {
        let mut grammar = Grammar::default();
        grammar
            .add(
                Sort::new("S"),
                Vec::new(),
                Some(Label::new("unit")),
                false,
                false,
            )
            .unwrap();
        let state = State {
            production: 0,
            dot: 0,
            origin: 0,
        };
        let mut chart = Chart::default();
        chart.add(state, [Vec::new()]).unwrap();
        chart
            .completed
            .entry(Sort::new("S"))
            .or_default()
            .push(state);
        let provenance = ParseProvenance {
            source: SourceId(0),
            base_offset: 0,
        };

        let mut first = completed_nodes(&chart, &grammar, &Sort::new("S"), 0, 0, "", provenance).0;
        let mut second = completed_nodes(&chart, &grammar, &Sort::new("S"), 0, 0, "", provenance).0;
        let first = first.pop_first().expect("first completed node exists");
        let second = second.pop_first().expect("second completed node exists");

        assert!(Rc::ptr_eq(&first, &second));
    }

    #[test]
    fn comparing_a_shared_packed_node_uses_its_identity() {
        let node = PackedTerm::production(0, Vec::new(), TermMetadata::default());
        let shared = Rc::clone(&node);
        reset_packed_structural_comparisons();

        assert_eq!(node.cmp(&shared), std::cmp::Ordering::Equal);
        assert_eq!(packed_structural_comparisons(), 0);
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
            grammar.filter_or_defer_packed_priority(cast),
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
            .filter_packed_priority(Rc::clone(&shared))
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
            .filter_packed_priority(forest)
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
    fn unequal_deep_packed_nodes_compare_without_walking_their_children() {
        let chain = |name| {
            let ParsedTerm::Term(leaf) = variable(name) else {
                unreachable!()
            };
            let mut node = PackedTerm::leaf(leaf);
            for production in 0..256 {
                node = PackedTerm::production(production, vec![node], TermMetadata::default());
            }
            node
        };
        let left = chain("left");
        let right = chain("right");
        reset_packed_structural_comparisons();

        assert_ne!(left.cmp(&right), std::cmp::Ordering::Equal);
        assert_eq!(packed_structural_comparisons(), 0);
    }

    #[test]
    fn production_metadata_participates_in_packed_fingerprints() {
        let metadata = |production| TermMetadata {
            production: Some(ResolvedProductionId(production)),
            ..TermMetadata::default()
        };
        let left = PackedTerm::production(0, Vec::new(), metadata(1));
        let right = PackedTerm::production(0, Vec::new(), metadata(2));

        assert_ne!(left.fingerprint, right.fingerprint);
        assert_ne!(left, right);
    }

    #[test]
    fn packed_fingerprint_collisions_fall_back_to_complete_structure() {
        let PackedTerm { node: left, .. } =
            Rc::unwrap_or_clone(derivation(variable("left")).pop().unwrap());
        let PackedTerm { node: right, .. } =
            Rc::unwrap_or_clone(derivation(variable("right")).pop().unwrap());
        let left = PackedTerm {
            fingerprint: 0,
            node: left,
        };
        let right = PackedTerm {
            fingerprint: 0,
            node: right,
        };

        assert_ne!(left.cmp(&right), std::cmp::Ordering::Equal);
        assert_ne!(left, right);
    }

    #[test]
    fn does_not_enqueue_a_derivation_covered_by_a_stored_ambiguity() {
        let state = State {
            production: 0,
            dot: 1,
            origin: 0,
        };
        let mut chart = Chart::default();
        assert!(
            chart
                .add(state, [derivation(ambiguity(&["A", "B"]))])
                .unwrap()
        );
        assert_eq!(chart.agenda.pop_front(), Some(state));

        assert!(!chart.add(state, [derivation(variable("A"))]).unwrap());
        assert!(chart.agenda.is_empty());
        assert_eq!(chart.states[&state].len(), 1);
    }

    #[test]
    fn replaces_covered_derivations_with_a_superseding_ambiguity() {
        let state = State {
            production: 0,
            dot: 1,
            origin: 0,
        };
        let mut chart = Chart::default();
        assert!(chart.add(state, [derivation(variable("A"))]).unwrap());
        chart.agenda.clear();

        assert!(
            chart
                .add(state, [derivation(ambiguity(&["A", "B"]))])
                .unwrap()
        );
        assert_eq!(chart.agenda.into_iter().collect::<Vec<_>>(), vec![state]);
        assert_eq!(
            chart.states[&state]
                .iter()
                .cloned()
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([derivation(ambiguity(&["A", "B"]))]),
        );
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
        assert_eq!(chart.waiting[&child], vec![waiting]);

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
        assert_eq!(chart.completed[&parent], vec![completed]);
    }

    #[test]
    fn external_catalog_overloads_remain_in_source_production_id_space() {
        let production = |sort: &str,
                          child: Option<&str>,
                          terminal: Option<&str>,
                          label: Option<&str>,
                          attributes: Attributes| {
            let items = child
                .map(|child| ProductionItem::NonTerminal {
                    sort: Sort::new(child),
                    name: None,
                })
                .into_iter()
                .chain(terminal.map(|terminal| ProductionItem::Terminal(terminal.into())))
                .collect();
            Sentence::Production {
                label: label.map(Label::new),
                parameters: Vec::new(),
                sort: Sort::new(sort),
                items,
                attributes,
            }
        };
        let mut cell_attributes = Attributes::default();
        cell_attributes.insert("cell", serde_json::json!(""));
        let sentences = vec![
            production("Cell", None, Some("<cell>"), Some("cell"), cell_attributes),
            production("Big", Some("Small"), None, None, Attributes::default()),
            production(
                "Small",
                None,
                Some("x"),
                Some("value"),
                Attributes::default(),
            ),
            production("Big", None, Some("x"), Some("value"), Attributes::default()),
        ];
        let source_catalog = ProductionCatalog::from_visible(&sentences);
        let parsing_sentences = sentences
            .iter()
            .filter(|sentence| {
                !matches!(sentence, Sentence::Production { attributes, .. }
                if attributes.get("cell").is_some())
            })
            .collect::<Vec<_>>();
        let grammar =
            Grammar::from_rule_sentences(parsing_sentences, &source_catalog, None).unwrap();
        let source_id = |sort: &str| {
            source_catalog
                .productions()
                .find_map(|(id, sentence)| match sentence {
                    Sentence::Production {
                        label: Some(label),
                        sort: result,
                        ..
                    } if label.name == "value" && result.name == sort => Some(id),
                    _ => None,
                })
                .unwrap()
        };
        let small = source_id("Small");
        let big = source_id("Big");

        assert!(grammar.overloads.less_than(&small, &big));
        assert!(!grammar.overloads.contains(&ProductionId(0)));

        let parsed = |source| {
            let production = grammar
                .productions
                .iter()
                .position(|production| production.source_production == Some(source))
                .unwrap();
            ParsedTerm::Production {
                production,
                children: Vec::new(),
                metadata: TermMetadata::default(),
            }
        };
        let filtered =
            grammar.filter_overloads_prefer_avoid(ParsedTerm::Ambiguity(BTreeSet::from([
                parsed(small),
                parsed(big),
            ])));
        assert!(matches!(filtered, ParsedTerm::Production { production, .. }
            if grammar.productions[production].source_production == Some(small)));
    }

    #[test]
    fn packs_growing_completed_node_alternatives_in_one_derivation() {
        let state = State {
            production: 0,
            dot: 1,
            origin: 0,
        };
        let mut chart = Chart::default();

        for count in 1..=70 {
            let alternatives = (0..count)
                .map(|index| {
                    ParsedTerm::Term(Term::Variable {
                        name: format!("V{index}"),
                        sort: None,
                    })
                })
                .collect();
            chart
                .add(state, [derivation(ParsedTerm::Ambiguity(alternatives))])
                .expect("growing subsets should be packed, not counted as separate derivations");
        }

        let stored = &chart.states[&state];
        assert_eq!(stored.len(), 1);
        assert!(matches!(
            &stored.iter().next().expect("one derivation exists")[0].node,
            PackedNode::Ambiguity(alternatives)
                if alternatives.len() == 70
        ));
    }

    #[test]
    fn chart_accepts_more_than_sixty_four_boundary_distinct_derivations() {
        let state = State {
            production: 0,
            dot: 2,
            origin: 0,
        };
        let mut chart = Chart::default();
        let derivations = (0..70).map(|index| {
            vec![
                derivation(variable(&format!("L{index}"))).pop().unwrap(),
                derivation(variable(&format!("R{index}"))).pop().unwrap(),
            ]
        });

        assert_eq!(chart.add(state, derivations), Ok(true));
        assert_eq!(chart.states[&state].len(), 70);
    }

    fn spanned_node(production: usize, start: usize, end: usize) -> Rc<PackedTerm> {
        PackedTerm::production(
            production,
            Vec::new(),
            TermMetadata {
                span: Some(TermSpan {
                    source: SourceId(0),
                    start,
                    end,
                }),
                ..TermMetadata::default()
            },
        )
    }

    #[test]
    fn packs_independent_child_choices_with_matching_boundaries() {
        let mut derivations = BTreeSet::from([
            vec![spanned_node(0, 0, 1), spanned_node(2, 1, 2)],
            vec![spanned_node(1, 0, 1), spanned_node(3, 1, 2)],
        ]);

        factor_derivations(&mut derivations);

        let packed = derivations.first().expect("one packed derivation");
        assert_eq!(derivations.len(), 1);
        assert!(matches!(&packed[0].node, PackedNode::Ambiguity(items) if items.len() == 2));
        assert!(matches!(&packed[1].node, PackedNode::Ambiguity(items) if items.len() == 2));
    }

    #[test]
    fn keeps_different_child_boundaries_correlated() {
        let mut derivations = BTreeSet::from([
            vec![spanned_node(0, 0, 1), spanned_node(1, 1, 3)],
            vec![spanned_node(2, 0, 2), spanned_node(3, 2, 3)],
        ]);

        factor_derivations(&mut derivations);

        assert_eq!(derivations.len(), 2);
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
