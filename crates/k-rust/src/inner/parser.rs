//! A portable chart parser over lowered K productions.

mod disambiguation;
mod inference;
mod lists;
mod parametric;
mod record;
mod scanner;
#[cfg(feature = "z3-inference")]
mod z3_inference;

#[cfg(test)]
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet, HashSet, VecDeque};
use std::fmt;
use std::rc::Rc;

use crate::definition::{
    AssociativityRelations, Attributes, PartialOrder, ProductionCatalog, ProductionId,
    ProductionItem, Regex as KRegex, RegexBody, Sentence, compute_associativities,
    compute_overloads, compute_priorities, compute_subsorts, parse_regex, sentence_equivalent,
};
use crate::kast::{Label, ResolvedProductionId, Sort, Term, TermMetadata, TermSpan};
use crate::provenance::SourceId;

use self::disambiguation::parse_apply_priority;
use self::lists::UserList;
use self::scanner::{Item, Layout, Scanner, compile_item};

const MAX_DERIVATIONS_PER_STATE: usize = 64;

#[derive(Clone, Copy)]
struct ParseProvenance {
    source: SourceId,
    base_offset: usize,
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
    },
    InvalidLayoutProduction,
    EmptyLayout,
    NoParse {
        position: usize,
        expected: Vec<String>,
    },
    Ambiguous {
        parses: usize,
    },
    TooManyParses {
        limit: usize,
    },
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
            Self::InconsistentTokenPrecedence { token } => {
                write!(formatter, "inconsistent token precedence for {token}")
            }
            Self::InvalidLayoutProduction => formatter
                .write_str("productions of sort `#Layout` must contain exactly one regex terminal"),
            Self::EmptyLayout => {
                formatter.write_str("a `#Layout` regular expression must not match empty input")
            }
            Self::NoParse { position, expected } => {
                write!(formatter, "could not parse input at byte {position}")?;
                if !expected.is_empty() {
                    write!(formatter, "; expected {}", expected.join(", "))?;
                }
                Ok(())
            }
            Self::Ambiguous { parses } => write!(formatter, "input has {parses} parses"),
            Self::TooManyParses { limit } => write!(
                formatter,
                "parse forest exceeded the per-state limit of {limit} derivations"
            ),
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
    user_list: bool,
    field_names: Vec<Option<String>>,
    record: Option<RecordProduction>,
    parametric_origin: Option<ParametricOrigin>,
    /// Production identity retained in the parse forest after a temporary grammar production
    /// recognizes its input. Java's Earley parser uses `originalPrd` for this same boundary.
    term_production: Option<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParametricOrigin {
    label: Option<Label>,
    parameters: Vec<Sort>,
    result: Sort,
    items: Vec<ProductionItem>,
    attributes: Attributes,
    substitution: BTreeMap<Sort, Sort>,
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

#[derive(Clone, Copy, Debug, Default)]
struct ProductionOptions<'a> {
    token: bool,
    transparent: bool,
    bracket: bool,
    bracket_label: Option<&'a str>,
    apply_priority: Option<&'a str>,
    function: bool,
    macro_like: bool,
    prefer: bool,
    avoid: bool,
    source_production: Option<ProductionId>,
    user_list: bool,
    precedence: Option<&'a str>,
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
    static PACKED_STRUCTURAL_COMPARISONS: Cell<usize> = const { Cell::new(0) };
    static UNPACKED_NODES: Cell<usize> = const { Cell::new(0) };
    static PACKED_APPLICATION_RESOLUTIONS: Cell<usize> = const { Cell::new(0) };
    static PACKED_PRIORITY_COMPUTATIONS: Cell<usize> = const { Cell::new(0) };
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

    #[cfg(feature = "z3-inference")]
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
                    if attributes.get_str("userList") == Some("*")
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
        )
    }

    pub fn from_sentences<'a>(
        sentences: impl IntoIterator<Item = &'a Sentence>,
    ) -> Result<Self, ParseError> {
        let sentences = sentences.into_iter().collect::<Vec<_>>();
        Self::from_collected_sentences(sentences, None, ParserRole::Rule, false)
    }

    pub(super) fn from_configuration_sentences<'a>(
        sentences: impl IntoIterator<Item = &'a Sentence>,
    ) -> Result<Self, ParseError> {
        let sentences = sentences.into_iter().collect::<Vec<_>>();
        Self::from_collected_sentences(sentences, None, ParserRole::Rule, true)
    }

    pub(super) fn from_rule_sentences<'a>(
        sentences: impl IntoIterator<Item = &'a Sentence>,
        source_catalog: &ProductionCatalog<'_>,
    ) -> Result<Self, ParseError> {
        let sentences = sentences.into_iter().collect::<Vec<_>>();
        Self::from_collected_sentences(
            sentences,
            Some(SourceLinks::catalog(source_catalog)),
            ParserRole::Rule,
            true,
        )
    }

    fn from_collected_sentences(
        sentences: Vec<&Sentence>,
        source_links: Option<SourceLinks<'_, '_>>,
        role: ParserRole,
        include_default_layout: bool,
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
                ] => expand_regex(regex, &lexical),
                _ => Err(ParseError::InvalidLayoutProduction),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let priorities = compute_priorities(sentences.iter().copied())
            .map_err(|cycle| ParseError::CircularPriorities { path: cycle.path })?;
        let associativities = compute_associativities(sentences.iter().copied());
        let semantic_subsorts = compute_subsorts(sentences.iter().copied(), false)
            .map_err(|cycle| ParseError::CircularSubsorts { path: cycle.path })?;
        let overloads = compute_overloads(sentences.iter().copied(), &semantic_subsorts)
            .map_err(|cycle| ParseError::CircularOverloads { path: cycle.path })?;
        let external = source_links.is_some();
        let source_links =
            source_links.unwrap_or_else(|| SourceLinks::catalog(overloads.catalog()));
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
            layout: if include_default_layout {
                Layout::compile_with_default(&layout_sources)?
            } else if layout_declared {
                Layout::compile(&layout_sources)?
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
            grammar.add_production_with_lexical(
                sort.clone(),
                items,
                label.clone(),
                ProductionOptions {
                    token: attributes.get("token").is_some(),
                    transparent: attributes.get("bracket").is_some(),
                    bracket: attributes.get("bracket").is_some(),
                    bracket_label: attributes.get_str("bracketLabel"),
                    apply_priority: attributes.get_str("applyPriority"),
                    function: attributes.get("function").is_some(),
                    macro_like: ["macro", "macro-rec", "alias", "alias-rec"]
                        .iter()
                        .any(|key| attributes.get(key).is_some()),
                    prefer: attributes.get("prefer").is_some(),
                    avoid: attributes.get("avoid").is_some(),
                    source_production: source_links.resolve(sentence),
                    user_list: attributes.get("userList").is_some(),
                    precedence: attributes.get_str("prec"),
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
        self.parse_with_provenance(start, input, SourceId(0), 0)
    }

    /// Parse semantic text whose byte zero begins at `base_offset` in `source`.
    pub fn parse_with_provenance(
        &self,
        start: &Sort,
        input: &str,
        source: SourceId,
        base_offset: usize,
    ) -> Result<Term, ParseError> {
        self.parse_with_context(start, input, false, source, base_offset)
    }

    pub(crate) fn parse_with_context(
        &self,
        start: &Sort,
        input: &str,
        is_anywhere: bool,
        source: SourceId,
        base_offset: usize,
    ) -> Result<Term, ParseError> {
        let provenance = ParseProvenance {
            source,
            base_offset,
        };
        let mut charts = (0..=input.len())
            .map(|_| Chart::default())
            .collect::<Vec<_>>();
        let mut scanner_cache = vec![None; input.len() + 1];
        let start_position = self.layout.skip(input, 0);
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
        let mut first_violation = None;

        for position in start_position..=input.len() {
            while let Some(state) = charts[position].agenda.pop_front() {
                let Some(derivations) = charts[position].states.get(&state).cloned() else {
                    continue;
                };
                let production = &self.productions[state.production];
                let canonical = self.layout.skip(input, position);
                if state.dot < production.items.len() && canonical != position {
                    self.add_chart_state(&mut charts[canonical], state, derivations)?;
                    continue;
                }

                match production.items.get(state.dot) {
                    Some(Item::NonTerminal(sort)) => {
                        for predicted in self.productions_for(sort) {
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
                        for end in self.scanner.matches(
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
                        if self.productive_unary_cycles.contains(&state.production) {
                            return Err(ParseError::TooManyParses {
                                limit: MAX_DERIVATIONS_PER_STATE,
                            });
                        }
                        let mut nodes = BTreeSet::new();
                        let mut invalid = Vec::new();
                        for children in &derivations {
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
                            self.add_chart_state(
                                &mut charts[position],
                                State {
                                    dot: caller.dot + 1,
                                    ..caller
                                },
                                append_nodes(&caller_derivations, &nodes),
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
            if self.layout.skip(input, position) != input.len() {
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
            return Err(first_violation.unwrap_or_else(|| self.no_parse(&charts)));
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
        let parses = Grammar::ambiguity_count(&cleaned);
        if parses > 1 {
            Err(ParseError::Ambiguous { parses })
        } else {
            Ok(self.lower(cleaned))
        }
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
        let forest = self.prefer_exact_packed_rewrite_sibling_sorts(forest);
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

    pub(crate) fn add_token_with_precedence(
        &mut self,
        result: Sort,
        item: ProductionItem,
        precedence: &str,
    ) -> Result<(), ParseError> {
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

    pub(crate) fn add_bracket(
        &mut self,
        result: Sort,
        items: Vec<ProductionItem>,
    ) -> Result<(), ParseError> {
        let bracket_label = format!("#bracket:{result}");
        self.add_production_with_lexical(
            result,
            &items,
            None,
            ProductionOptions {
                transparent: true,
                bracket: true,
                bracket_label: Some(&bracket_label),
                ..ProductionOptions::default()
            },
            &BTreeMap::new(),
        )
    }

    pub(crate) fn add_left_associative(&mut self, label: impl Into<String>) {
        let label = label.into();
        self.associativities.left.insert((label.clone(), label));
    }

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
        let field_names = items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { name, .. } => Some(name.clone()),
                ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
            })
            .collect();
        let mut compiled_items = Vec::new();
        for item in items
            .iter()
            .filter(|item| !matches!(item, ProductionItem::Terminal(value) if value.is_empty()))
        {
            let item = compile_item(item, lexical)?;
            self.scanner.register(&item, options.precedence)?;
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
            .or_else(|| options.bracket_label.map(str::to_owned))
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
            && let [Item::NonTerminal(child)] = items.as_slice()
        {
            self.subsort_relations
                .insert((child.clone(), result.clone()));
        }
        if !options.bracket
            && let [Item::NonTerminal(child)] = items.as_slice()
        {
            self.syntactic_subsort_relations
                .insert((child.clone(), result.clone()));
        }
        self.productions.push(Production {
            result: result.clone(),
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
            user_list: options.user_list,
            field_names,
            record: None,
            parametric_origin: None,
            term_production: None,
        });
        self.by_result.entry(result).or_default().push(index);
        Ok(())
    }

    fn productions_for(&self, sort: &Sort) -> impl Iterator<Item = usize> + '_ {
        self.by_result.get(sort).into_iter().flatten().copied()
    }

    fn no_parse(&self, charts: &[Chart]) -> ParseError {
        let position = charts
            .iter()
            .rposition(|chart| !chart.states.is_empty())
            .unwrap_or(0);
        let expected = charts[position]
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
        ParseError::NoParse { position, expected }
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

fn expand_regex(source: &str, lexical: &BTreeMap<String, KRegex>) -> Result<String, ParseError> {
    if lexical.is_empty() {
        return Ok(source.to_owned());
    }
    let parsed = parse_regex(source).map_err(|error| ParseError::InvalidRegex {
        regex: source.to_owned(),
        message: error.to_string(),
    })?;
    let body = expand_regex_body(&parsed.body, lexical, &mut Vec::new())?;
    Ok(KRegex {
        start_line: parsed.start_line,
        body,
        end_line: parsed.end_line,
    }
    .to_source_string())
}

fn expand_regex_body(
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

#[derive(Clone, Debug, Default)]
struct Chart {
    states: BTreeMap<State, Derivations>,
    waiting: BTreeMap<Sort, Vec<State>>,
    completed: BTreeMap<Sort, Vec<State>>,
    agenda: VecDeque<State>,
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
    fn add(
        &mut self,
        state: State,
        derivations: impl IntoIterator<Item = Derivation>,
    ) -> Result<bool, ParseError> {
        let mut derivations = derivations.into_iter().peekable();
        if derivations.peek().is_none() {
            return Ok(false);
        }
        let stored = self.states.entry(state).or_default();
        let mut changed = false;
        for derivation in derivations {
            changed |= stored.insert(derivation);
        }
        if !changed {
            return Ok(false);
        }
        if stored.len() > MAX_DERIVATIONS_PER_STATE {
            return Err(ParseError::TooManyParses {
                limit: MAX_DERIVATIONS_PER_STATE,
            });
        }
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

/// Pack derivations that differ at only one child position.
///
/// Earley completion revisits callers as a completed node gains alternatives. Without replacing
/// the previously observed subset, a state retains `{a}`, `{a,b}`, `{a,b,c}`, and so on as
/// distinct derivations. Those sets denote the same choice once the largest set is present. This
/// fixed-point factoring preserves correlations between children while sharing every choice whose
/// surrounding children are identical.
///
/// Coverage-aware insertion and factoring are complementary: coverage removes whole derivations
/// subsumed by an existing ambiguity, while factoring creates that shared ambiguity from sibling
/// derivations which differ at one child position.
fn factor_derivations(derivations: &mut BTreeSet<Derivation>) {
    let width = derivations.first().map_or(0, Vec::len);
    if derivations.len() < 2 || width == 0 {
        return;
    }

    loop {
        let before = derivations.len();
        for index in 0..width {
            let mut groups = BTreeMap::<Derivation, BTreeSet<Rc<PackedTerm>>>::new();
            for derivation in std::mem::take(derivations) {
                let mut key = derivation;
                let node = key.remove(index);
                groups.entry(key).or_default().insert(node);
            }
            for (mut key, nodes) in groups {
                key.insert(index, pack_alternatives(nodes));
                derivations.insert(key);
            }
        }
        if derivations.len() == before {
            break;
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
    let mut nodes = BTreeSet::new();
    let mut invalid = Vec::new();
    for state in chart.completed.get(sort).into_iter().flatten() {
        if state.origin != origin {
            continue;
        }
        let derivations = &chart.states[state];
        let production = &grammar.productions[state.production];
        for children in derivations {
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
    (nodes, violation)
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
        return PackedTerm::leaf(
            Term::Token {
                token: input[start..end].to_owned(),
                sort: production.result.clone(),
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
    match (label.name.as_str(), children) {
        ("#KToken", [value, sort])
            if let (Some(value), Some(sort)) = (kstring_token(value), kstring_token(sort))
                && let (Ok(value), Ok(sort)) = (
                    crate::kast::string::unquote(value),
                    crate::kast::string::unquote(sort),
                )
                && let Ok(sort) = crate::kast::parser::parse_sort_text(&sort) =>
        {
            Term::Token { token: value, sort }
        }
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
        let baseline = grammar.prefer_exact_rewrite_sibling_sorts(baseline);
        let baseline = grammar.push_top_lhs_ambiguity_up(grammar.factor_ambiguities(baseline));
        reset_unpacked_nodes();

        let materialized = grammar
            .materialize_packed_forest(shared)
            .expect("the retained packed diamond satisfies post-parse checks");
        let materialized = grammar
            .resolve_applications(materialized)
            .expect("the factored diamond contains no applications");
        let materialized = grammar.prefer_exact_rewrite_sibling_sorts(materialized);
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
    fn packed_application_resolution_keeps_the_per_node_derivation_limit() {
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
            .materialize_packed_forest(application(MAX_DERIVATIONS_PER_STATE))
            .expect("exactly the per-node application limit is retained");
        let rejected =
            grammar.materialize_packed_forest(application(MAX_DERIVATIONS_PER_STATE + 1));

        assert_eq!(
            Grammar::ambiguity_count(&retained),
            MAX_DERIVATIONS_PER_STATE
        );
        assert_eq!(
            rejected,
            Err(ParseError::TooManyParses {
                limit: MAX_DERIVATIONS_PER_STATE,
            })
        );
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
            (0..=MAX_DERIVATIONS_PER_STATE)
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

        let error = grammar
            .resolve_packed_applications(forest)
            .expect_err("the shared application exceeds the per-node limit");

        assert_eq!(
            error,
            ParseError::TooManyParses {
                limit: MAX_DERIVATIONS_PER_STATE,
            }
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
        let baseline = grammar.prefer_exact_rewrite_sibling_sorts(baseline);
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
        let grammar = Grammar::from_rule_sentences(parsing_sentences, &source_catalog).unwrap();
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

        for count in 1..=MAX_DERIVATIONS_PER_STATE + 1 {
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
                if alternatives.len() == MAX_DERIVATIONS_PER_STATE + 1
        ));
    }

    #[test]
    fn retains_the_derivation_limit_for_uncovered_forests() {
        let state = State {
            production: 0,
            dot: 2,
            origin: 0,
        };
        let mut chart = Chart::default();
        let derivations = (0..=MAX_DERIVATIONS_PER_STATE).map(|index| {
            vec![
                derivation(variable(&format!("L{index}"))).pop().unwrap(),
                derivation(variable(&format!("R{index}"))).pop().unwrap(),
            ]
        });

        assert_eq!(
            chart.add(state, derivations),
            Err(ParseError::TooManyParses {
                limit: MAX_DERIVATIONS_PER_STATE,
            })
        );
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
