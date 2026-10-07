//! ```toml algorithm
//! id = "parser.earley.recognize"
//! name = "agenda-driven Earley recognition"
//! sites = ["Grammar::parse_attempt", "Grammar::recognize", "Grammar::explain_violation", "Grammar::lower_inferred", "Grammar::parse", "Grammar::parse_with_context_and_diagnostic_provenance", "Grammar::advanced_item_useful", "Grammar::completion_useful", "Grammar::node_reaches_root", "Grammar::priority_admits", "RemainingTokens::new", "Reach::rest_follows", "InstanceNodes::intern"]
//! variable = "p = chart-agenda pops; d = dispatch cost and derivations read; B = input bytes; s = interned sorts; P = distinct lexemes among the input's tokens; u = (chart, production, next token) pairs whose usefulness the completion lookahead decides, each once, and (chart, production) pairs whose root reachability it searches, each again only when asked with a later earliest end than the bounds already known for it, each search over the waiting items of the charts it reaches, each item judged by the priority relation at its edge (in a grammar without rewrite, sequence or #let) and by where the input's next token its rest can begin with lies (O(P log B))"
//! counters = ["ParserParseAttempts", "ParserChartAgendaPops", "ParserChartRevisitPops", "ParserChartDerivationsRead", "ParserChartPredictionAttempts", "ParserChartCompletionCandidates", "ParserTerminalPredictionsSkipped", "ParserNonterminalPredictionsSkipped"]
//! span = "per problem"
//!
//! [[cost]]
//! mode = "recognition (the chart loop of recognize)"
//! bound = "O(B x s) chart allocation plus O(p x d) plus the memoized usefulness searches, O(u) pairs each over the waiting items of one chart; a filtered recognition skips the completions no parse can contain, so p is linear in the input for right-recursive lists and associativity-disambiguated chains, also beside other operators of their sort and in a rule body, which complete every enclosing list or chain at every position (quadratic p) without it; the input's tokens from the first position a completion is judged at are read once, O(B) scanner reads; the instances of one parametric production completed over one span with the same children are one node (one hashed lookup each), so d does not grow with the depth of a nesting of them"
//!
//! [[cost]]
//! mode = "one parse attempt (parse_attempt)"
//! bound = "recognition plus the post-recognition passes called at the end of parse_attempt, each carried by its own card (prepare_packed_forest, inference, then through lower_inferred resolve_terminators, filter_overloads, insert_empty_lists, remove_brackets_casts, factor and resolve ambiguity)"
//!
//! [[cost]]
//! mode = "one failed parse attempt whose recognition removed a derivation for a priority or associativity violation (explain_violation)"
//! bound = "two recognitions, the second with the relations ignored and every node one stand-in (each item processed once, no forest), plus either one no-parse diagnostic or, when the second finds a derivation of the whole input, a third, forest-building recognition with the relations ignored and prepare_packed_forest over its complete derivations; a grammar with a same-span cycle builds that forest instead of the second"
//!
//! [[cost]]
//! mode = "filtered attempt with retry (parse_with_context_and_diagnostic_provenance)"
//! bound = "at most two parse attempts, the second only when the first found no derivation of the input (its error is read from the chart; an error computed from the forest is the first attempt's); the retry makes every prediction and, before the last chart the first attempt reached, skips only the completions the input cannot continue, judged without the priority and associativity relations, and cuts a node that repeats itself over one span instead of reporting a cycle, so a failed parse of an associativity-disambiguated chain takes the cubic recognition of that chain's relation-free grammar"
//! ```
//!
//! ```toml algorithm
//! id = "parser.lower.term"
//! name = "lowering of parsed terms into KAST"
//! sites = ["lower_term"]
//! variable = "N = parsed tree nodes"
//! counters = []
//! no_counter = "term lowering has no dedicated counter"
//! consumes = [{ type = "k_rust::inner::parser::forest::ParsedTerm", role = "sorted tree" }]
//! produces = [{ type = "k_rust::kast::Term", role = "parsed term" }]
//! span = "none"
//!
//! [[cost]]
//! mode = "one parsed tree"
//! bound = "O(N), each node built from its lowered children, which it takes over without copying"
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
mod cycles;
mod disambiguation;
mod forest;
mod grammar;
mod inference;
mod lists;
mod parametric;
mod prediction;
mod record;
mod scanner;
#[cfg(debug_assertions)]
mod sort_check;
#[cfg(feature = "z3-inference")]
mod z3_inference;

use self::chart::*;
use self::cycles::{SameSpanCycles, check_same_span_repetition};
use self::disambiguation::PackedPriorityMemos;
use self::forest::*;
use self::grammar::Placeholder;
use self::grammar::ProductionText;
use self::grammar::catalog_production;
pub(super) use self::grammar::named_projection_productions;
#[cfg(feature = "z3-inference")]
use self::grammar::{render_added_production, render_production};

use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::rc::Rc;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

use k_rust_kore::measure::{self, Algorithm, Counter};

#[cfg(test)]
use crate::definition::Sentence;
use crate::definition::{
    AssociativityRelations, AttributeKey, Attributes, PartialOrder, PartialOrderCycle,
    ProductionItem, Regex as KRegex, RegexBody, SortDenotations,
};
use crate::kast::sort_role::{NumeralSpelling, numeral_spelling};
use crate::kast::{
    FrontendSort, InternalLabel, Label, ProductionIdentity, Sort, Term, TermMetadata, TermSpan,
};
use crate::names::BuiltinSort;
use crate::provenance::SourceId;

#[cfg(feature = "cli")]
pub(crate) use self::disambiguation::parse_apply_priority;
use self::lists::UserList;
#[cfg(feature = "cli")]
pub(crate) use self::parametric::concretize_parametric_productions;
use self::prediction::{DeferredScopes, PredictionAnalysis};
#[cfg(feature = "cli")]
pub(crate) use self::scanner::DEFAULT_LAYOUT;
pub(super) use self::scanner::Scanner;
use self::scanner::{Item, Layout, ScanCacheEntry, ScanWinner};

/// The name under which sort inference treats a leaf as a variable: a `#KVariable` token, or a
/// `KConfigVar` token such as `$PGM`. A configuration variable stands for the value supplied for
/// it when the configuration is initialized, a term the definition does not fix, so inference
/// types it exactly like a variable and wraps it in `#SemanticCastTo<inferred sort>`, which
/// checks the supplied value against that sort.
pub(crate) fn inferred_variable_name(term: &Term) -> Option<&str> {
    match term.unannotated() {
        Term::Variable { name, .. } => Some(name),
        Term::Token { token, sort } if sort.is_builtin(BuiltinSort::KConfigVar) => Some(token),
        _ => None,
    }
}

/// The variable leaf `term` with `sort` recorded as the variable's own sort, keeping its metadata,
/// or `None` when `term` is not a variable node (a `KConfigVar` token has no sort to record).
///
/// A semantic cast `X:S` only bounds X from above, so when inference gives X a sort below `S`, the
/// occurrence under the cast records that sort on X itself: `#SemanticCastToS(X:Inferred)`.
pub(crate) fn variable_with_inferred_sort(term: &Term, sort: &Sort) -> Option<Term> {
    let Term::Variable { name, .. } = term.unannotated() else {
        return None;
    };
    let variable = Term::Variable {
        name: name.clone(),
        sort: Some(sort.clone()),
    };
    Some(match term.metadata() {
        Some(metadata) => variable.with_metadata(metadata.clone()),
        None => variable,
    })
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

/// Which work a recognition may skip because it cannot contribute to a parse.
///
/// The scanner is deterministic: the only token any item can scan at a position is the
/// scanner's winner there. A prediction whose production cannot begin with that token, and a
/// completion whose callers can continue neither with it nor through a nullable rest to a
/// caller that can, are part of no parse of the input. Skipping them leaves every parse, and
/// so the forest and every error computed from it, as it is; it does change what the
/// diagnostic of an attempt that finds no derivation reads (the items of its last chart), so
/// such an attempt that skipped anything is retried with `Retry`
/// (`Grammar::parse_with_context_and_diagnostic_provenance`).
#[derive(Clone, Copy, Eq, PartialEq)]
enum PredictionMode {
    /// Skip predictions and completions that cannot contribute to a parse.
    Filtered,
    /// Make every prediction and completion.
    Unfiltered,
    /// Make every prediction, and skip a completion only where the next token starts before
    /// `horizon` (the last chart a failed `Filtered` attempt reached) and only when the input
    /// cannot continue the item it would advance: its rest cannot begin with the next token,
    /// nor complete through a nullable rest into an item whose rest can, whatever the priority
    /// and associativity relations say. Such an item scans nothing and completes into nothing
    /// that scans, so every chart from the horizon on, including the last non-empty one that
    /// the no-parse diagnostic reads, has the items of `Unfiltered` (the `Filtered` attempt
    /// keeps a subset of them, so its last chart is not after theirs). An item a completion
    /// adds is relocated to the position of the next token, so nothing skipped where the next
    /// token starts before the horizon can reach those charts. And every item of a derivation
    /// of the whole input is kept, so when the relations reject every derivation the retry
    /// meets a rejection and reports a violation, as `Unfiltered` does. `Filtered` also skips
    /// items whose node the relations forbid wherever it could sit; that keeps every parse but
    /// drops items that scan, so a retry must not.
    Retry { horizon: usize },
}

impl PredictionMode {
    /// Whether completions that cannot contribute to a parse are skipped where the next token
    /// starts at `position`.
    fn prunes_completions_at(self, position: usize) -> bool {
        match self {
            Self::Filtered => true,
            Self::Unfiltered => false,
            Self::Retry { horizon } => position < horizon,
        }
    }
}

/// What a filtered recognition judges a skipped completion by (`Grammar::advanced_item_useful`).
#[derive(Clone, Copy)]
struct Reach<'a> {
    analysis: &'a PredictionAnalysis,
    cycles: &'a SameSpanCycles,
    /// The relations judged: `Ignored` keeps every item the input can continue, whatever the
    /// relations say of where its node could sit (`PredictionMode::Retry`).
    filter: PriorityFilter,
    /// The start position and the start sort's id.
    root: (usize, usize),
    /// The tokens of the input from some position at or before `from` on; read when the
    /// relations are judged.
    remaining: Option<&'a RemainingTokens>,
    /// The position of the next token, where every caller's rest begins at the earliest.
    from: usize,
}

impl Reach<'_> {
    /// Where the callers of an item's node can begin their own rests, when the items of
    /// `production` from `dot` on are matched by the tokens of the input after `after`, where
    /// the node's span ends at the earliest: `after` itself when they can all match the empty
    /// string, otherwise just past the first token they can begin with that occurs at or after
    /// `after` (the node ends past every token its rest scans, and the callers' rests come
    /// after it); `None` when no such token remains, so that no node of the item can end. With
    /// the tokens not read (`remaining` unset) every rest is taken to follow at `after`.
    fn rest_follows(self, production: usize, dot: usize, after: usize) -> Option<usize> {
        if self.analysis.rest_is_nullable(production, dot) {
            return Some(after);
        }
        let Some(remaining) = self.remaining else {
            return Some(after);
        };
        remaining
            .first_from(after, |lexeme| {
                self.analysis
                    .rest_can_start_with(production, dot, Some(lexeme))
            })
            .map(|position| position + 1)
    }

    /// The latest position at which the items of `production` from `dot` on can begin so that
    /// [`Self::rest_follows`] is at most `latest`: the inverse bound, with which a node whose
    /// callers' rests may begin up to `latest` passes the bound down to the item's own node.
    /// `None` when no position does.
    fn rest_latest(self, production: usize, dot: usize, latest: usize) -> Option<usize> {
        if self.analysis.rest_is_nullable(production, dot) {
            return Some(latest);
        }
        let Some(remaining) = self.remaining else {
            return Some(latest);
        };
        remaining.last_up_to(latest.checked_sub(1)?, |lexeme| {
            self.analysis
                .rest_can_start_with(production, dot, Some(lexeme))
        })
    }
}

/// Where each lexeme is the scanner's token, in the input read from one position on.
///
/// The scanner is deterministic: an item scans at a position only the scanner's winner there,
/// and the next item is relocated to the next position past its layout. So the input is one
/// sequence of tokens, and whether an item's rest can begin at or after a position is whether
/// one of the lexemes it can begin with is a token there or later.
struct RemainingTokens {
    /// The positions of each lexeme's tokens, ascending, by lexeme.
    positions: HashMap<usize, Vec<usize>>,
    /// The positions, ascending, of the tokens that witness a node whose scope error the
    /// priority filter defers (`DeferredScopes::Witnessed`).
    deferrals: Vec<usize>,
}

impl RemainingTokens {
    /// Read the tokens from `from`, a position the recognizer reached, to the end of the input
    /// or to the first position where no token wins or a token matches nothing (an empty token
    /// leaves the position, and so the next token, unchanged, so no item reads past it).
    fn new(
        grammar: &Grammar,
        input: &str,
        from: usize,
        deferred_scopes: &DeferredScopes,
        scanner_cache: &mut [ScanCacheEntry],
    ) -> Self {
        let mut positions = HashMap::<usize, Vec<usize>>::new();
        let mut deferrals = Vec::new();
        let mut position = from;
        // Invariant: `position` is a token boundary reached from `from`; it strictly increases
        // at every token read, so the loop ends, and each lexeme's positions are ascending.
        loop {
            let canonical = grammar.canonical_position(input, position, scanner_cache);
            let Some(ScanWinner::Token { lexeme, end }) = grammar.scanner.winner(
                &grammar.layout,
                input,
                canonical,
                &mut scanner_cache[canonical],
            ) else {
                break;
            };
            positions.entry(lexeme).or_default().push(canonical);
            if deferred_scopes.witnesses(lexeme) {
                deferrals.push(canonical);
            }
            if end <= canonical {
                break;
            }
            position = end;
        }
        Self {
            positions,
            deferrals,
        }
    }

    /// The first token at or after `position` that witnesses a node whose scope error the
    /// priority filter defers.
    fn first_deferral_from(&self, position: usize) -> Option<usize> {
        self.deferrals
            .get(
                self.deferrals
                    .partition_point(|deferral| *deferral < position),
            )
            .copied()
    }

    /// How many such witnesses come before `position`.
    fn deferrals_before(&self, position: usize) -> usize {
        self.deferrals
            .partition_point(|deferral| *deferral < position)
    }

    /// The first position at or after `after` where the token is a lexeme for which `accepts`
    /// holds.
    fn first_from(&self, after: usize, accepts: impl Fn(usize) -> bool) -> Option<usize> {
        self.positions
            .iter()
            .filter(|(lexeme, _)| accepts(**lexeme))
            .filter_map(|(_, positions)| {
                positions
                    .get(positions.partition_point(|position| *position < after))
                    .copied()
            })
            .min()
    }

    /// The last position at or before `before` where the token is a lexeme for which
    /// `accepts` holds.
    fn last_up_to(&self, before: usize, accepts: impl Fn(usize) -> bool) -> Option<usize> {
        self.positions
            .iter()
            .filter(|(lexeme, _)| accepts(**lexeme))
            .filter_map(|(_, positions)| {
                positions
                    .partition_point(|position| *position <= before)
                    .checked_sub(1)
                    .map(|index| positions[index])
            })
            .max()
    }
}

/// Whether a caller can hold a node at its dot in a reading the priority filter keeps
/// (`Grammar::boundary_admits`).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Admission {
    No,
    Yes,
    /// Only when the caller's own node ends past the token at this position: the edge breaks a
    /// relation, which drops the caller's node at completion unless an earlier check of it
    /// meets a scope error the filter defers, and such an error needs a node of a rewrite,
    /// sequence or `#let`, which contains a token that witnesses it, the first of which at or
    /// after the caller's origin lies here.
    IfEndsAfter(usize),
}

impl Admission {
    /// The earliest `after` of the caller's node, given the earliest its rest allows.
    fn after(self, after: usize) -> Option<usize> {
        match self {
            Self::No => None,
            Self::Yes => Some(after),
            Self::IfEndsAfter(witness) => Some(after.max(witness + 1)),
        }
    }
}

/// What the root-reachability searches of one recognition learned of a node
/// (`Grammar::node_reaches_root`): it can be part of a parse when its callers' rests may begin
/// at any position up to `reaches_up_to`, and cannot when they begin at `fails_from` or later.
/// Both bounds are exact for the position they were found at and carry over in the one
/// direction: a later start only removes tokens a rest can use.
#[derive(Clone, Copy, Default)]
struct Reaching {
    reaches_up_to: Option<usize>,
    fails_from: Option<usize>,
}

impl Reaching {
    fn known(self, after: usize) -> Option<bool> {
        if self.fails_from.is_some_and(|fails| fails <= after) {
            Some(false)
        } else if self.reaches_up_to.is_some_and(|reaches| after <= reaches) {
            Some(true)
        } else {
            None
        }
    }
}

/// The nodes a recognition built for instances of parametric productions, by production of the
/// parsed term, span and children.
///
/// Every concrete instance of one parametric production is one production of the parsed term
/// (`Production::term_production`), so instances that complete over one span with the same
/// children build one node, as the forest means it: under `syntax {S} S ::= wrap(S)`, the `wrap`
/// of a `Nat` read at `Nat` and at `KItem` are the same `wrap` node. Built separately, they are
/// equal but distinct, and so are the nodes above them, all the way up a nesting, so that
/// comparing two of them (a chart deciding whether a derivation is new) descends the whole
/// nesting: quadratic work in its depth. Interned, each pair is one node and the comparison
/// stops at the first level. Keys name children by address; the table holds every node it
/// names, and so its children, for the rest of the recognition, so an address is not reused.
#[derive(Default)]
struct InstanceNodes(HashMap<(usize, usize, usize, Vec<*const PackedTerm>), Rc<PackedTerm>>);

impl InstanceNodes {
    /// The node equal to `term`, built over `start..end`, that this recognition built first.
    fn intern(&mut self, term: Rc<PackedTerm>, start: usize, end: usize) -> Rc<PackedTerm> {
        let PackedNode::Production {
            production,
            children,
            ..
        } = &term.node
        else {
            return term;
        };
        let key = (
            *production,
            start,
            end,
            children.iter().map(Rc::as_ptr).collect::<Vec<_>>(),
        );
        match self.0.entry(key) {
            std::collections::hash_map::Entry::Occupied(entry) => {
                if entry.get().node == term.node {
                    Rc::clone(entry.get())
                } else {
                    term
                }
            }
            std::collections::hash_map::Entry::Vacant(entry) => Rc::clone(entry.insert(term)),
        }
    }
}

/// What a parse attempt skipped, for the decision to retry it.
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct Pruning {
    /// Whether the attempt skipped a prediction or a completion an unfiltered attempt makes.
    pub(super) pruned: bool,
    /// The last non-empty chart of the attempt's recognition of the whole input under the
    /// priority and associativity relations, when it found no derivation of the input; `None`
    /// when it found one, or when recognition itself failed (a cycle).
    pub(super) furthest: Option<usize>,
}

/// Whether recognition drops the derivations that the priority and associativity relations rule
/// out. A violation explains a failed parse only when the input has a derivation that the
/// violation rules out, so a failed parse that recorded one is recognized once more with the
/// relations ignored to tell the two apart (`Grammar::parse_attempt`).
#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum PriorityFilter {
    Enforced,
    Ignored,
}

/// The outcome of the recognition phase of one parse attempt.
struct Recognition {
    charts: Vec<Chart>,
    /// The completed start productions spanning the whole input.
    parses: BTreeSet<Rc<PackedTerm>>,
    /// The first priority or associativity violation that removed a derivation, in chart order.
    first_violation: Option<ParseError>,
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

/// A sort that derives itself over `text` without consuming input, so the text has infinitely
/// many parses.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CyclicDerivation {
    pub sort: Sort,
    pub text: String,
    /// The productions of the repeated derivation, outermost first.
    pub productions: Vec<String>,
    /// The items that the repetition matched with the empty string.
    pub empty: Vec<String>,
    pub span: Option<TermSpan>,
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
    /// A sort derives itself over a text without consuming input.
    CyclicDerivation(Box<CyclicDerivation>),
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
    /// Checked inference only (`KRUST_TYPE_INFERENCE_MODE=checked`): the portable and Z3
    /// engines reached different outcomes on one term. Each engine's outcome is `Ok` with the
    /// `Debug` rendering of the term it inferred (for an ambiguous parse, of the term it
    /// lowered the parse to) or `Err` with the message of its rejection. The checked
    /// comparison never builds one in which both engines rejected: that is agreement.
    ///
    /// It is kept apart from `SortInference`, so a caller that expects a rejection does not
    /// take a term that one engine accepted, or that the engines inferred differently, for one.
    InferenceEngineDisagreement {
        portable: Result<String, String>,
        z3: Result<String, String>,
        /// Whether the engines decided an ambiguous parse, so what they produced is the
        /// lowered term rather than the inferred tree.
        ambiguous_parse: bool,
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
    /// A production labelled `#OuterCast` reads its operand as a term of its result sort
    /// through that sort's projection, and the result sort has none: no K term has that sort.
    /// Only a definition's own `#OuterCast` production can have such a result, because the
    /// generated projection casts exist only for sorts with a sort projection.
    ProjectionCastWithoutProjection {
        sort: Sort,
        span: Option<TermSpan>,
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
            Self::CyclicDerivation(cycle) => {
                let CyclicDerivation {
                    sort,
                    text,
                    productions,
                    empty,
                    ..
                } = &**cycle;
                // The span of a node ends after the layout that follows it; the reader needs only
                // the text itself.
                match text.trim() {
                    "" => formatter.write_str("Parsing ambiguity: the empty text")?,
                    text => write!(formatter, "Parsing ambiguity: `{text}`")?,
                }
                write!(
                    formatter,
                    " has infinitely many parses because these productions derive {sort} from itself without consuming input:"
                )?;
                for production in productions {
                    write!(formatter, "\n    {production}")?;
                }
                match empty.as_slice() {
                    [] => Ok(()),
                    [item] => write!(formatter, "\nwhere {item} matches the empty string."),
                    items => write!(
                        formatter,
                        "\nwhere {} match the empty string.",
                        items.join(", ")
                    ),
                }
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
            Self::InferenceEngineDisagreement {
                portable,
                z3,
                ambiguous_parse,
            } => {
                formatter.write_str("portable and Z3 sort inference ")?;
                if let (Ok(portable), Ok(z3)) = (portable, z3) {
                    let outcome = if *ambiguous_parse {
                        "lowered an ambiguous parse to different terms"
                    } else {
                        "produced different terms"
                    };
                    return write!(formatter, "{outcome}: portable {portable}; Z3 {z3}");
                }
                let (disagree, accepted) = if *ambiguous_parse {
                    ("disagree on an ambiguous parse", "lowered to")
                } else {
                    ("disagree", "accepted")
                };
                let side = |outcome: &Result<String, String>| match outcome {
                    Ok(term) => format!("{accepted} {term}"),
                    Err(message) => format!("rejected with {message}"),
                };
                write!(
                    formatter,
                    "{disagree}: portable {}; Z3 {}",
                    side(portable),
                    side(z3)
                )
            }
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
            Self::ProjectionCastWithoutProjection { sort, .. } => write!(
                formatter,
                "projection cast to sort {sort}, which has no sort projection because no K term has sort {sort}"
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
    /// Compiled items; a nonterminal carries the sort the production declares for that child,
    /// which is the sort semantic passes (inference, priorities, list completion) reason about.
    items: Vec<Item>,
    /// The sort id the recognizer predicts at each nonterminal item. It is the id of the
    /// declared item sort, except where `Grammar::admit_rewrites_in_argument_positions`
    /// widened a position to the rule-scaffolding sort that also derives a rewrite of it.
    item_sort_ids: Vec<Option<usize>>,
    /// The scanner's lexeme id of each terminal or regex item, returned when the item was
    /// registered. The grammar's scanner only grows, and a production is never moved to another
    /// scanner, so the ids stay valid for the grammar and its clones.
    item_lexeme_ids: Vec<Option<usize>>,
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
    source_production_text: Option<ProductionText>,
    user_list: bool,
    user_list_nonempty: bool,
    field_names: Vec<Option<String>>,
    record: Option<RecordProduction>,
    parametric_origin: Option<ParametricOrigin>,
    /// Production identity retained in the parse forest after a temporary grammar production
    /// recognizes its input. The split forms of a user list and the instantiations of a
    /// parametric production only recognize input: the term they build applies the production
    /// the definition declares.
    term_production: Option<usize>,
    /// The `hook` attribute of the declaring sentence; a case-2 instantiation carries its
    /// parametric origin's hook, so an instantiated machine-integer token production is still
    /// recognized as one.
    hook: Option<String>,
}

impl Production {
    /// Whether the production recognizes machine-integer literals. A literal such as `3p8`
    /// spells its width after the `p`/`P`, so it denotes a value of the machine-integer sort of
    /// that width: its sort parameter comes from the token text, not from the instantiation that
    /// scanned it.
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
    source_production_text: Option<&'a ProductionText>,
    source: Option<&'a str>,
    location: Option<crate::definition::Location>,
    user_list: bool,
    user_list_nonempty: bool,
    precedence: Option<&'a str>,
    hook: Option<&'a str>,
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

/// A grammar's subsort relation with the partial order it generates, built on first use.
///
/// The order is a function of the relation alone, so every parse over one grammar shares one
/// construction. Mutable access goes through `DerefMut`, which discards the built order, so the
/// order can never describe an earlier relation.
#[derive(Clone, Debug, Default)]
pub(crate) struct SubsortRelations {
    relations: BTreeSet<(Sort, Sort)>,
    order: OnceLock<Result<PartialOrder<Sort>, PartialOrderCycle<Sort>>>,
}

impl SubsortRelations {
    /// The partial order of the relation, or the cycle that prevents one.
    pub(crate) fn order(&self) -> Result<&PartialOrder<Sort>, &PartialOrderCycle<Sort>> {
        self.order
            .get_or_init(|| PartialOrder::new(self.relations.iter().cloned()))
            .as_ref()
    }
}

impl std::ops::Deref for SubsortRelations {
    type Target = BTreeSet<(Sort, Sort)>;

    fn deref(&self) -> &Self::Target {
        &self.relations
    }
}

impl std::ops::DerefMut for SubsortRelations {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.order.take();
        &mut self.relations
    }
}

/// A reusable inner grammar derived from visible productions.
///
/// Parametric productions are concretized for parsing while retaining a link to
/// their original form for sort inference.
#[derive(Clone, Debug)]
pub struct Grammar {
    generation: u64,
    sort_denotations: SortDenotations,
    productions: Vec<Production>,
    sorts: Vec<Sort>,
    sort_ids: BTreeMap<Sort, usize>,
    by_result: Vec<Vec<usize>>,
    scanner: Scanner,
    prediction_analysis: OnceLock<PredictionAnalysis>,
    // Invariant: when set, this is `SameSpanCycles::new(self)`; cleared with the prediction
    // analysis on every grammar change.
    same_span_cycles: OnceLock<SameSpanCycles>,
    source_production_texts: BTreeMap<ProductionIdentity, ProductionText>,
    layout: Layout,
    priorities: PartialOrder<String>,
    associativities: AssociativityRelations,
    subsort_relations: SubsortRelations,
    syntactic_subsort_relations: SubsortRelations,
    overloads: PartialOrder<ProductionIdentity>,
    user_lists: BTreeMap<Sort, UserList>,
    /// Recognition placeholders `H{K}`: the sort a slot of the parametric head `H` is recognized
    /// at when its parameter has no parse-time value, with whether the definition also declares
    /// that spelling as an instance of `H` (`Placeholder`). The recognition bridges into a
    /// placeholder (`add_recognition_bridge`) and every unary production touching a scaffolding
    /// placeholder only widen what the recognizer accepts and contribute no subsort pair.
    /// Registered only by `placeholder_sort`, before any production is added, never recognized
    /// by spelling.
    placeholders: BTreeMap<Sort, Placeholder>,
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
            sort_denotations: SortDenotations::default(),
            productions: Vec::new(),
            sorts: Vec::new(),
            sort_ids: BTreeMap::new(),
            by_result: Vec::new(),
            scanner: Scanner::default(),
            prediction_analysis: OnceLock::new(),
            same_span_cycles: OnceLock::new(),
            source_production_texts: BTreeMap::new(),
            layout: Layout::default(),
            priorities: PartialOrder::new([]).expect("an empty relation is acyclic"),
            associativities: AssociativityRelations::default(),
            subsort_relations: SubsortRelations::default(),
            syntactic_subsort_relations: SubsortRelations::default(),
            overloads: PartialOrder::new([]).expect("an empty relation is acyclic"),
            user_lists: BTreeMap::new(),
            placeholders: BTreeMap::new(),
            productive_unary_cycles: BTreeSet::new(),
            role: ParserRole::Rule,
        }
    }
}

impl Grammar {
    fn invalidate_prediction_analysis(&mut self) {
        self.prediction_analysis.take();
        self.same_span_cycles.take();
        self.generation = next_grammar_generation();
    }

    fn add_chart_state(
        &self,
        chart: &mut Chart,
        state: State,
        derivations: impl IntoIterator<Item = Derivation>,
    ) -> Result<bool, ParseError> {
        let (changed, new_state) = chart.add_with_status(state, derivations)?;
        Ok(self.record_chart_addition(chart, state, changed, new_state))
    }

    /// Add each of `prefixes` extended by `last` (when given) to `state`; see
    /// `Chart::add_extensions_with_status`.
    fn add_chart_extensions(
        &self,
        chart: &mut Chart,
        state: State,
        prefixes: &Derivations,
        last: Option<&Rc<PackedTerm>>,
    ) -> Result<bool, ParseError> {
        let (changed, new_state) = chart.add_extensions_with_status(state, prefixes, last)?;
        Ok(self.record_chart_addition(chart, state, changed, new_state))
    }

    fn record_chart_addition(
        &self,
        chart: &mut Chart,
        state: State,
        changed: bool,
        new_state: bool,
    ) -> bool {
        let production = &self.productions[state.production];
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
        changed
    }

    /// The sort that a spelling denotes in this grammar's module.
    pub fn start_sort<'s>(&'s self, spelling: &'s Sort) -> &'s Sort {
        self.sort_denotations.denote(spelling)
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
        let start = self.sort_denotations.denote(start);
        let provenance = ParseProvenance {
            source,
            base_offset,
        };
        let context = ParseContext {
            is_anywhere,
            provenance,
            diagnostic_provenance,
        };
        let mut pruning = Pruning::default();
        let result = self.parse_attempt(
            start,
            input,
            context,
            PredictionMode::Filtered,
            &mut pruning,
        );
        // A failure without a derivation is explained from the chart, whose items the skipped
        // work changes: retry it with the skipped work restored where the diagnostic reads it.
        // A failure after recognition (an ambiguity, sort inference, a relation error of the
        // forest, a cycle) is computed from the forest, which skipping leaves as it is
        // (`PredictionMode`), so it is already the error of an unfiltered recognition.
        // Invariant: a retry occurs exactly when the filtered recognizer pruned at least one
        // prediction or completion and found no derivation of the input, and it reruns the
        // complete pipeline with the same context, skipping completions only before the last
        // chart the filtered recognition reached.
        if let (Err(_), true, Some(horizon)) = (&result, pruning.pruned, pruning.furthest) {
            self.parse_attempt(
                start,
                input,
                context,
                PredictionMode::Retry { horizon },
                &mut Pruning::default(),
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
        pruning: &mut Pruning,
    ) -> Result<Term, ParseError> {
        let ParseContext {
            is_anywhere,
            provenance,
            diagnostic_provenance,
        } = context;
        let _span = measure::algorithm_span(Algorithm::ParserEarleyRecognize);
        measure::bump(Counter::ParserParseAttempts);
        let priority_memos = RefCell::new(PackedPriorityMemos::default());
        let mut scanner_cache = vec![None; input.len() + 1];
        let start_position = self.canonical_position(input, 0, &mut scanner_cache);
        let Some(start_id) = self.sort_id(start) else {
            let charts = (0..=input.len())
                .map(|_| Chart::new(self.sorts.len()))
                .collect::<Vec<_>>();
            return Err(self.no_parse(
                input,
                provenance,
                diagnostic_provenance,
                &charts,
                &mut scanner_cache,
            ));
        };
        let Recognition {
            charts,
            parses,
            first_violation,
        } = self.recognize(
            start_id,
            start_position,
            input,
            provenance,
            prediction_mode,
            PriorityFilter::Enforced,
            None,
            &mut pruning.pruned,
            &mut scanner_cache,
            &priority_memos,
        )?;
        if parses.is_empty() {
            pruning.furthest = Some(
                charts
                    .iter()
                    .rposition(|chart| !chart.states.is_empty())
                    .unwrap_or(0),
            );
            return Err(match first_violation {
                None => self.no_parse(
                    input,
                    provenance,
                    diagnostic_provenance,
                    &charts,
                    &mut scanner_cache,
                ),
                Some(first_violation) => {
                    drop(charts);
                    self.explain_violation(
                        first_violation,
                        start_id,
                        start_position,
                        input,
                        context,
                        prediction_mode,
                        &mut pruning.pruned,
                        &mut scanner_cache,
                    )
                }
            });
        }
        // The chart can retain the whole packed forest through its states. Release it before any
        // post-parse allocation, then apply the root priority preference while alternatives still
        // share their descendants. In particular, do not expand losing non-rewrite parses before
        // the root rewrite/sequence/let preference has selected the corresponding sibling.
        drop(charts);
        drop(_span);
        // Packed normalization and inference phase: preserve sharing until losing alternatives
        // are removed, then materialize exactly the retained inferred trees.
        // A rule body's rewrite, sequence and `#let` scope over the user syntax around them, so
        // among the readings of the root ambiguity one rooted at them is preferred. That
        // preference compares the root's alternatives with each other, so it runs on the packed
        // root ambiguity before descending into losing alternatives; filtering each root
        // independently incorrectly rejects inputs whose winning interpretation is a top-level
        // rewrite (for example a rewrite inside a competing map-item parse).
        let forest = self.prepare_packed_forest(PackedTerm::ambiguity(parses), &priority_memos)?;
        // Checked mode compares the engines on an ambiguous forest by what each lowers to.
        #[cfg(feature = "z3-inference")]
        if inference::checked_inference_requested()
            && let Some(checked) =
                self.checked_ambiguous_parse(&forest, start, is_anywhere, |tree| {
                    self.lower_inferred(tree, start)
                })
        {
            return checked;
        }
        self.infer_packed_sorts(forest, start, is_anywhere, |tree| {
            self.lower_inferred(tree, start)
        })
    }

    /// Why a parse whose recognition removed a derivation for `first_violation` failed.
    ///
    /// The violation explains the failure only when some derivation of the whole input breaks
    /// the priority and associativity relations; a derivation the relations removed while
    /// recognition explored a reading that fails anyway (for instance `A => B` as the left
    /// operand of a `=>` that never comes) does not. The input is therefore recognized again
    /// with the relations ignored: when that recognition also fails, the input has no derivation
    /// at all and the error is the place where it stops; otherwise the error is a violation of a
    /// derivation of the whole input.
    ///
    /// Whether a derivation exists, and the items of the last chart where none does, do not
    /// depend on the parse forest, which for an ambiguous grammar (every chain of a binary
    /// operator) grows far faster than its chart. So the input is first recognized with every
    /// node replaced by one stand-in node: each item then has one derivation and is processed
    /// once, and with the relations ignored nothing is filtered by a node's structure, so the
    /// items of every chart and the start items spanning the input are those of the
    /// forest-building recognition. Only a derivation of the whole input needs the forest. A
    /// grammar with a production on a same-span cycle, whose detection reads node structure,
    /// always builds it.
    #[allow(clippy::too_many_arguments)]
    fn explain_violation(
        &self,
        first_violation: ParseError,
        start_id: usize,
        start_position: usize,
        input: &str,
        context: ParseContext,
        prediction_mode: PredictionMode,
        pruned: &mut bool,
        scanner_cache: &mut [ScanCacheEntry],
    ) -> ParseError {
        let priority_memos = RefCell::new(PackedPriorityMemos::default());
        let cycles = self
            .same_span_cycles
            .get_or_init(|| SameSpanCycles::new(self));
        if cycles.is_empty() {
            let stand_in = PackedTerm::leaf(Term::Token {
                token: String::new(),
                sort: Sort::new("K"),
            });
            // A recognition error (a cycle) that only the ignored relations let through says
            // nothing about this input's failure.
            let Ok(Recognition { charts, parses, .. }) = self.recognize(
                start_id,
                start_position,
                input,
                context.provenance,
                prediction_mode,
                PriorityFilter::Ignored,
                Some(&stand_in),
                pruned,
                scanner_cache,
                &priority_memos,
            ) else {
                return first_violation;
            };
            if parses.is_empty() {
                return self.no_parse(
                    input,
                    context.provenance,
                    context.diagnostic_provenance,
                    &charts,
                    scanner_cache,
                );
            }
        }
        let Ok(Recognition { charts, parses, .. }) = self.recognize(
            start_id,
            start_position,
            input,
            context.provenance,
            prediction_mode,
            PriorityFilter::Ignored,
            None,
            pruned,
            scanner_cache,
            &priority_memos,
        ) else {
            return first_violation;
        };
        if parses.is_empty() {
            return self.no_parse(
                input,
                context.provenance,
                context.diagnostic_provenance,
                &charts,
                scanner_cache,
            );
        }
        drop(charts);
        match self.prepare_packed_forest(PackedTerm::ambiguity(parses), &priority_memos) {
            Err(violation) => violation,
            Ok(_) => first_violation,
        }
    }

    /// The recognition phase of a parse attempt: the Earley chart of `input` from the start sort
    /// and the completed start productions spanning it, dropping the derivations that violate the
    /// priority and associativity relations when `filter` enforces them. With a `stand_in`,
    /// every completed node is that node, so the recognition decides which items exist without
    /// building a forest (`Grammar::explain_violation`); it is used only with the relations
    /// ignored, and only for a grammar without same-span cycles.
    #[allow(clippy::too_many_arguments)]
    fn recognize(
        &self,
        start_id: usize,
        start_position: usize,
        input: &str,
        provenance: ParseProvenance,
        prediction_mode: PredictionMode,
        filter: PriorityFilter,
        stand_in: Option<&Rc<PackedTerm>>,
        pruned: &mut bool,
        scanner_cache: &mut [ScanCacheEntry],
        priority_memos: &RefCell<PackedPriorityMemos>,
    ) -> Result<Recognition, ParseError> {
        let prediction_analysis = (prediction_mode == PredictionMode::Filtered).then(|| {
            self.prediction_analysis
                .get_or_init(|| PredictionAnalysis::new(self))
        });
        let completion_analysis = (prediction_mode != PredictionMode::Unfiltered).then(|| {
            self.prediction_analysis
                .get_or_init(|| PredictionAnalysis::new(self))
        });
        // Whether a completion over `[origin, position]` of a production is useful when the
        // scanner's next token is `winner`, by `(origin, production, winner)`.
        let mut useful_completions = HashMap::new();
        // Whether a node of a production starting in a chart can be part of a parse of the whole
        // input, by `(origin, production)`.
        let mut reaching_nodes = HashMap::new();
        // The tokens of the input from the first position a completion asks about them on,
        // read once, when the relations decide whether a node can reach the root.
        let mut remaining_tokens = None;
        // The relations a skipped completion is judged by (`PredictionMode`): a retry judges
        // only whether the input can continue an item, never where the relations let its node
        // sit.
        let usefulness_filter = match prediction_mode {
            PredictionMode::Retry { .. } => PriorityFilter::Ignored,
            PredictionMode::Filtered | PredictionMode::Unfiltered => filter,
        };
        // A retry recognizes a failed parse again only for its diagnostic: the items of the last
        // chart reached and the violation met. It cuts a node that repeats itself over one span
        // instead of reporting a cycle: the repetition adds no item (the node it repeats already
        // completed the same state) and has passed the filter, and the first attempt, which
        // keeps every derivation the relations allow, found none, so the repetition is part of
        // no reading of the input that the relations allow. The recognitions with the relations
        // ignored that explain a violation (`Grammar::explain_violation`) keep their own rule.
        let cut_repetitions = matches!(prediction_mode, PredictionMode::Retry { .. })
            && filter == PriorityFilter::Enforced;
        let mut instance_nodes = InstanceNodes::default();
        let root = (start_position, start_id);
        let cycles = self
            .same_span_cycles
            .get_or_init(|| SameSpanCycles::new(self));
        let mut charts = (0..=input.len())
            .map(|_| Chart::new(self.sorts.len()))
            .collect::<Vec<_>>();
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
            // The lexeme of the token the scanner reads next, once a completion here asks for
            // it: `Some(None)` where no token follows, and `None` until asked or at the end of
            // the input, where nothing is skipped.
            let mut lookahead: Option<Option<Option<usize>>> = None;
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
                let canonical = *canonical_position
                    .get_or_insert_with(|| self.canonical_position(input, position, scanner_cache));
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
                        let completed = completed_nodes(
                            &charts[position],
                            self,
                            sort_id,
                            position,
                            position,
                            input,
                            provenance,
                            priority_memos,
                            filter,
                            cycles,
                            stand_in,
                            cut_repetitions,
                        );
                        if let Some(cycle) = &completed.cycle {
                            return Err(cycle.clone());
                        }
                        if first_violation.is_none() {
                            first_violation.clone_from(&completed.violation);
                        }
                        let completed = self.filter_associative_boundary(
                            state,
                            &completed.nodes,
                            filter,
                            &mut first_violation,
                        );
                        if !completed.is_empty() {
                            self.add_chart_extensions(
                                &mut charts[position],
                                State {
                                    dot: state.dot + 1,
                                    ..state
                                },
                                &derivations,
                                Some(&pack_alternatives(&completed)),
                            )?;
                        }
                    }
                    Some(_) => {
                        #[cfg(test)]
                        record_chart_dispatch(ChartDispatchKind::Scan, derivation_count, revisit);
                        if let Some(end) =
                            production.item_lexeme_ids[state.dot].and_then(|lexeme| {
                                self.scanner.matches(
                                    &self.layout,
                                    lexeme,
                                    input,
                                    position,
                                    &mut scanner_cache[position],
                                )
                            })
                        {
                            self.add_chart_extensions(
                                &mut charts[end],
                                State {
                                    dot: state.dot + 1,
                                    ..state
                                },
                                &derivations,
                                None,
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
                        // A retry builds the node: its first lap may be the only node of its sort
                        // over the span, and the callers it advances are items of the chart the
                        // diagnostic reads. `SameSpanCycles` flags every such production (a
                        // labelled unary production whose child derives its result through unary
                        // productions), so its second lap is a repetition over one span, which
                        // the retry cuts below (`cut_repetitions`).
                        if self.productive_unary_cycles.contains(&state.production)
                            && !cut_repetitions
                        {
                            return Err(self.productive_unary_cycle_error(
                                state.production,
                                input,
                                state.origin,
                                position,
                                provenance,
                            ));
                        }
                        let mut nodes = BTreeSet::new();
                        let mut invalid = Vec::new();
                        for children in &derivations {
                            measure::bump(Counter::ParserChartCompletionCandidates);
                            #[cfg(test)]
                            update_chart_work_counters(|counters| {
                                counters.primary_completion_candidates += 1;
                            });
                            let term = if let Some(stand_in) = stand_in {
                                Rc::clone(stand_in)
                            } else {
                                let term = build_packed_term(
                                    state.production,
                                    production,
                                    children,
                                    input,
                                    state.origin,
                                    position,
                                    provenance,
                                );
                                if production.term_production.is_some() {
                                    instance_nodes.intern(term, state.origin, position)
                                } else {
                                    term
                                }
                            };
                            match match filter {
                                PriorityFilter::Enforced => self.filter_or_defer_packed_priority(
                                    Rc::clone(&term),
                                    priority_memos,
                                ),
                                PriorityFilter::Ignored => Ok(Rc::clone(&term)),
                            } {
                                Ok(term) => {
                                    // A repetition over one span makes the forest infinite; a
                                    // retry cuts it (`cut_repetitions`).
                                    let repeats = cycles.contains(state.production)
                                        && match check_same_span_repetition(
                                            self,
                                            &charts[position],
                                            state.production,
                                            &term,
                                            input,
                                            state.origin,
                                            position,
                                        ) {
                                            Ok(()) => false,
                                            Err(_) if cut_repetitions => true,
                                            Err(cycle) => return Err(cycle),
                                        };
                                    if !repeats {
                                        nodes.insert(term);
                                    }
                                }
                                Err(error) => {
                                    invalid.push((term, error));
                                }
                            }
                        }
                        if first_violation.is_none() && !invalid.is_empty() {
                            first_violation = Some(canonical_packed_error(invalid));
                        }
                        // A nonempty completion before the horizon advances only the callers
                        // whose advanced item can contribute to a parse (`PredictionMode`).
                        let winner = match completion_analysis {
                            Some(_)
                                if state.origin < position
                                    && prediction_mode.prunes_completions_at(canonical) =>
                            {
                                if usefulness_filter == PriorityFilter::Enforced
                                    && remaining_tokens.is_none()
                                    && let Some(analysis) = completion_analysis
                                {
                                    remaining_tokens = Some(RemainingTokens::new(
                                        self,
                                        input,
                                        start_position,
                                        analysis.deferred_scopes(),
                                        scanner_cache,
                                    ));
                                }
                                *lookahead.get_or_insert_with(|| {
                                    (canonical < input.len()).then(|| {
                                        match self.scanner.winner(
                                            &self.layout,
                                            input,
                                            canonical,
                                            &mut scanner_cache[canonical],
                                        ) {
                                            Some(ScanWinner::Token { lexeme, .. }) => Some(lexeme),
                                            Some(ScanWinner::Layout { .. }) | None => None,
                                        }
                                    })
                                })
                            }
                            _ => None,
                        };
                        let mut advance = |chart: &mut Chart,
                                           caller: State,
                                           caller_derivations: &Derivations,
                                           earlier: Option<&[Chart]>|
                         -> Result<(), ParseError> {
                            #[cfg(test)]
                            update_chart_work_counters(|counters| {
                                counters.completion_caller_derivations_read +=
                                    caller_derivations.len();
                            });
                            let completed = self.filter_associative_boundary(
                                caller,
                                &nodes,
                                filter,
                                &mut first_violation,
                            );
                            let advanced = State {
                                dot: caller.dot + 1,
                                ..caller
                            };
                            if let (Some(analysis), Some(winner), Some(earlier)) =
                                (completion_analysis, winner, earlier)
                                && !completed.is_empty()
                                && !self.advanced_item_useful(
                                    earlier,
                                    advanced,
                                    winner,
                                    Reach {
                                        analysis,
                                        cycles,
                                        filter: usefulness_filter,
                                        root,
                                        remaining: remaining_tokens.as_ref(),
                                        from: canonical,
                                    },
                                    &mut useful_completions,
                                    &mut reaching_nodes,
                                )
                            {
                                *pruned = true;
                                return Ok(());
                            }
                            if !completed.is_empty() {
                                self.add_chart_extensions(
                                    chart,
                                    State {
                                        dot: caller.dot + 1,
                                        ..caller
                                    },
                                    caller_derivations,
                                    Some(&pack_alternatives(&completed)),
                                )?;
                            }
                            Ok(())
                        };
                        if state.origin < position {
                            // Advancing adds only to this position's chart, so the origin chart's
                            // callers and their derivations are read in place.
                            let (earlier, later) = charts.split_at_mut(position);
                            let origin = &earlier[state.origin];
                            for caller in origin
                                .waiting
                                .get(&production.result_id)
                                .into_iter()
                                .flatten()
                            {
                                if let Some(caller_derivations) = origin.states.get(caller) {
                                    advance(
                                        &mut later[0],
                                        *caller,
                                        caller_derivations,
                                        Some(&*earlier),
                                    )?;
                                }
                            }
                        } else {
                            // An empty completion extends its own origin chart; advance a
                            // snapshot of the callers and derivations as they were before it.
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
                                advance(&mut charts[position], caller, &caller_derivations, None)?;
                            }
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
            if self.canonical_position(input, position, scanner_cache) != input.len() {
                continue;
            }
            let completed = completed_nodes(
                chart,
                self,
                start_id,
                start_position,
                position,
                input,
                provenance,
                priority_memos,
                filter,
                cycles,
                stand_in,
                cut_repetitions,
            );
            if let Some(cycle) = &completed.cycle {
                return Err(cycle.clone());
            }
            parses.extend(completed.nodes.iter().cloned());
            if first_violation.is_none() {
                first_violation.clone_from(&completed.violation);
            }
        }
        Ok(Recognition {
            charts,
            parses,
            first_violation,
        })
    }

    /// The post-inference passes that turn a sort-inferred tree into the parsed term.
    fn lower_inferred(&self, inferred: ParsedTerm, start: &Sort) -> Result<Term, ParseError> {
        let resolved = self.resolve_overloaded_terminators(inferred)?;
        let filtered = self.filter_overloads_prefer_avoid(resolved);
        let listed = self.add_empty_lists(filtered, start)?;
        let cleaned = self.remove_brackets_and_syntactic_casts(listed);
        let cleaned = self.factor_ambiguities(cleaned);
        self.resolve_ambiguities(cleaned)
    }

    /// Whether `advanced`, an item a nonempty completion ending at the current position
    /// advances, can contribute to a parse when the scanner's next token is the lexeme `winner`
    /// (`None` where no token follows): its remaining items can begin with that token, or they
    /// can all match the empty string and the completion of its production is useful
    /// ([`Self::completion_useful`]). `earlier` holds the charts before the current position,
    /// which are final.
    fn advanced_item_useful(
        &self,
        earlier: &[Chart],
        advanced: State,
        winner: Option<usize>,
        reach: Reach<'_>,
        memo: &mut HashMap<(usize, usize, Option<usize>, usize), bool>,
        reaching: &mut HashMap<(usize, usize), Reaching>,
    ) -> bool {
        if reach
            .analysis
            .rest_can_start_with(advanced.production, advanced.dot, winner)
        {
            return reach
                .rest_follows(advanced.production, advanced.dot, reach.from)
                .is_some_and(|after| {
                    self.node_reaches_root(
                        earlier,
                        advanced.origin,
                        advanced.production,
                        after,
                        reach,
                        reaching,
                    )
                });
        }
        reach
            .analysis
            .rest_is_nullable(advanced.production, advanced.dot)
            && self.completion_useful(
                earlier,
                advanced.origin,
                advanced.production,
                winner,
                reach,
                memo,
                reaching,
            )
    }

    /// Whether a node of `production` starting in chart `origin`, whose callers' rests begin at
    /// `after` at the earliest, can be part of a parse of the whole input: it is a node of the
    /// start sort at the start, or some item waiting for its sort in chart `origin` admits it at
    /// its dot ([`Self::boundary_admits`]), can finish its own production on the tokens from
    /// `after` on ([`Reach::rest_follows`]), and its own node can be part of a parse in turn,
    /// with its callers' rests beginning past the first token that rest scans. This is what the
    /// relations and the input decide of a chain: under `E ::= E "+" E [left]`, a sum starting
    /// after the first operand can only become the right operand of a sum, which the relation
    /// forbids, or the left operand of another operator at its origin, which the priorities may
    /// forbid (`E "*" E > E "+" E`) and which, when the input holds no such operator from
    /// `after` on (the K prelude's `#And` at every sort), can never be finished; in a rule body,
    /// the left operand of the rule's own rewrite, whose `=>` comes after the `)` that closes
    /// the call around the chain, so that the rewrite would end where no `)` is left. So its
    /// items are part of no parse. A production on a same-span or productive unary cycle can,
    /// as in [`Self::completion_useful`].
    ///
    /// The answer depends on `(origin, production)`, the final chart `origin` and `after`, and
    /// a later `after` only removes tokens the rests can use; it is memoized in `memo` by
    /// `(origin, production)` as the bounds of `after` it is known for ([`Reaching`]), and
    /// searched with an explicit stack, as in [`Self::completion_useful`].
    ///
    /// Judged without the relations (`filter` ignored) every node is taken to reach the root:
    /// this question is about where a node can sit in a parse, and a recognition that must
    /// keep every item the input can continue does not ask it.
    fn node_reaches_root(
        &self,
        earlier: &[Chart],
        origin: usize,
        production: usize,
        after: usize,
        reach: Reach<'_>,
        memo: &mut HashMap<(usize, usize), Reaching>,
    ) -> bool {
        if reach.filter == PriorityFilter::Ignored {
            return true;
        }
        if let Some(reaches) = memo
            .get(&(origin, production))
            .and_then(|known| known.known(after))
        {
            return reaches;
        }
        let reaches_by_itself = |origin: usize, production: usize| {
            (origin, self.productions[production].result_id) == reach.root
                || reach.cycles.contains(production)
                || self.productive_unary_cycles.contains(&production)
        };
        // The earliest `after` each node was pushed with: a node pushed again with the same or
        // a later one can reach no more than it could then.
        let mut visited = HashMap::from([((origin, production), after)]);
        // Each frame: the node, its `after`, the waiting items examined, and the rest
        // (production, dot) of the caller that admitted the node below it (none for the first).
        let mut stack = vec![(origin, production, after, 0usize, None::<(usize, usize)>)];
        // Invariant: `stack` is a chain of nodes, each admitted by an item waiting for it whose
        // rest the tokens from the node's `after` on can follow and whose node is the next,
        // with that next node's `after` past the first token the rest scans; `visited` holds
        // every node pushed, with the earliest `after` it was pushed with, and the fourth
        // component counts the waiting items of each already examined.
        // The latest `after` with which the node of the top frame, by the path found, reaches
        // the root.
        let found = 'search: loop {
            let Some((origin, production, after, next_caller, _)) = stack.last_mut() else {
                break 'search None;
            };
            if *next_caller == 0 && reaches_by_itself(*origin, *production) {
                break 'search Some(usize::MAX);
            }
            let callers = earlier[*origin]
                .waiting
                .get(&self.productions[*production].result_id)
                .map_or(&[][..], Vec::as_slice);
            let Some(caller) = callers.get(*next_caller).copied() else {
                stack.pop();
                continue;
            };
            *next_caller += 1;
            let Some(caller_after) = reach
                .rest_follows(caller.production, caller.dot + 1, *after)
                .and_then(|caller_after| {
                    self.boundary_admits(caller, *production, reach)
                        .after(caller_after)
                })
            else {
                continue;
            };
            let node = (caller.origin, caller.production);
            let rest = (caller.production, caller.dot + 1);
            let known = memo.get(&node).copied().unwrap_or_default();
            match known.known(caller_after) {
                Some(true) => {
                    let latest = known
                        .reaches_up_to
                        .expect("a node known to reach has a bound");
                    break 'search Some(
                        reach
                            .rest_latest(rest.0, rest.1, latest)
                            .expect("the rest follows at the node's own bound"),
                    );
                }
                Some(false) => {}
                None => {
                    if visited
                        .get(&node)
                        .is_none_or(|pushed| caller_after < *pushed)
                    {
                        visited.insert(node, caller_after);
                        stack.push((node.0, node.1, caller_after, 0, Some(rest)));
                    }
                }
            }
        };
        match found {
            Some(mut latest) => {
                // Pass the bound down the path: each node reaches the root, by it, with any
                // `after` up to the latest at which the rest that admits it into the next node
                // can still begin.
                for (origin, production, after, _, rest) in stack.into_iter().rev() {
                    debug_assert!(after <= latest);
                    let known = memo.entry((origin, production)).or_default();
                    known.reaches_up_to = known.reaches_up_to.max(Some(latest));
                    if let Some((rest_production, rest_dot)) = rest {
                        latest = reach
                            .rest_latest(rest_production, rest_dot, latest)
                            .expect("the rest follows at the node's own bound");
                    }
                }
                true
            }
            None => {
                for (node, after) in visited {
                    let known = memo.entry(node).or_default();
                    known.fails_from =
                        Some(known.fails_from.map_or(after, |fails| fails.min(after)));
                }
                false
            }
        }
    }

    /// Whether a completion of `production` over `[origin, here]` can contribute to a parse
    /// when the scanner's next token is the lexeme `winner`: some item waiting for its sort in
    /// chart `origin` admits a node of it ([`Self::boundary_admits`]) and its advanced item is
    /// useful ([`Self::advanced_item_useful`]). A production that can take part in a same-span
    /// or productive unary cycle is useful, so that a node it repeats is built and the cycle is
    /// reported; a cycle that only items the input cannot continue would reach is part of no
    /// parse of the input (whose forest is then finite) and is not met, as with a skipped
    /// prediction. An item that can continue with `winner` counts only when its node can be part
    /// of a parse of the whole input ([`Self::node_reaches_root`]).
    ///
    /// The answer depends only on `(origin, production, winner)` and the final chart `origin`
    /// (and, through [`Self::node_reaches_root`], on the tokens that remain, which only shrink),
    /// so it is memoized in `memo`. The search over the chain of callers uses an explicit
    /// stack; when it finds no useful item, no item it visited reaches one, and all of them are
    /// recorded as useless.
    #[allow(clippy::too_many_arguments)]
    fn completion_useful(
        &self,
        earlier: &[Chart],
        origin: usize,
        production: usize,
        winner: Option<usize>,
        reach: Reach<'_>,
        memo: &mut HashMap<(usize, usize, Option<usize>, usize), bool>,
        reaching: &mut HashMap<(usize, usize), Reaching>,
    ) -> bool {
        // A caller completed here through a nullable rest ends here, so whether its node holds
        // a witness of a deferred scope error (`Admission::IfEndsAfter`) depends on how many
        // witnesses come before this position, which is part of the key.
        let region = reach
            .remaining
            .map_or(0, |remaining| remaining.deferrals_before(reach.from));
        if let Some(useful) = memo.get(&(origin, production, winner, region)) {
            return *useful;
        }
        let mut visited = HashSet::from([(origin, production)]);
        let mut stack = vec![(origin, production, 0usize)];
        // Invariant: `stack` is a chain of completions, each of which some caller of the one
        // before it would complete through a nullable rest; `visited` holds every completion
        // pushed, and the third component counts the callers of each already examined.
        let found = 'search: loop {
            let Some((origin, production, next_caller)) = stack.last_mut() else {
                break 'search false;
            };
            if *next_caller == 0
                && (reach.cycles.contains(*production)
                    || self.productive_unary_cycles.contains(production))
            {
                break 'search true;
            }
            let callers = earlier[*origin]
                .waiting
                .get(&self.productions[*production].result_id)
                .map_or(&[][..], Vec::as_slice);
            let Some(caller) = callers.get(*next_caller).copied() else {
                stack.pop();
                continue;
            };
            *next_caller += 1;
            let admission = self.boundary_admits(caller, *production, reach);
            if admission == Admission::No {
                continue;
            }
            let dot = caller.dot + 1;
            if reach
                .analysis
                .rest_can_start_with(caller.production, dot, winner)
                && reach
                    .rest_follows(caller.production, dot, reach.from)
                    .and_then(|after| admission.after(after))
                    .is_some_and(|after| {
                        self.node_reaches_root(
                            earlier,
                            caller.origin,
                            caller.production,
                            after,
                            reach,
                            reaching,
                        )
                    })
            {
                break 'search true;
            }
            if !reach.analysis.rest_is_nullable(caller.production, dot)
                || admission.after(reach.from) != Some(reach.from)
            {
                continue;
            }
            match memo.get(&(caller.origin, caller.production, winner, region)) {
                Some(true) => break 'search true,
                Some(false) => {}
                None => {
                    if visited.insert((caller.origin, caller.production)) {
                        stack.push((caller.origin, caller.production, 0));
                    }
                }
            }
        };
        if found {
            for (origin, production, _) in stack {
                memo.insert((origin, production, winner, region), true);
            }
        } else {
            for (origin, production) in visited {
                memo.insert((origin, production, winner, region), false);
            }
        }
        found
    }

    /// Whether `caller` can hold a node built by `child` at its dot in a reading the filters
    /// keep. The associativity boundary [`Self::filter_associative_boundary`] drops the node
    /// before the caller packs it, in every grammar (judged from `child`'s own parse label; a
    /// production without one passes its child's label up, which is not known here, so it is
    /// kept). The priority filter judges the edge when the caller completes
    /// ([`Self::priority_admits`]): a violation drops the caller's node, unless the filter has
    /// already met, in an earlier child or in another reading of this one, a rewrite, sequence
    /// or `#let` below an operator, a scope error it defers so that a reading rooted at the
    /// rewrite can be preferred over the one with the error, keeping the doomed node in the
    /// forest until then. Such an error needs a node of a rewrite, sequence or `#let` inside
    /// the caller's node, so a violation removes the reading wherever the caller's node holds no
    /// token that witnesses one ([`DeferredScopes`]); in a grammar without them, always.
    fn boundary_admits(&self, caller: State, child: usize, reach: Reach<'_>) -> Admission {
        if reach.filter == PriorityFilter::Ignored {
            return Admission::Yes;
        }
        if !self.associativity_admits(caller, child) {
            return Admission::No;
        }
        if self.priority_admits(caller, child) {
            return Admission::Yes;
        }
        match reach.analysis.deferred_scopes() {
            DeferredScopes::Absent => Admission::No,
            DeferredScopes::Unwitnessed => Admission::Yes,
            DeferredScopes::Witnessed(_) => match reach.remaining {
                None => Admission::Yes,
                Some(remaining) => remaining
                    .first_deferral_from(caller.origin)
                    .map_or(Admission::No, Admission::IfEndsAfter),
            },
        }
    }

    /// Whether [`Self::filter_associative_boundary`] keeps a node built by `child` as the
    /// child of `caller` at its dot.
    fn associativity_admits(&self, caller: State, child: usize) -> bool {
        let production = &self.productions[caller.production];
        let Some(parent) = production.parse_label.as_deref() else {
            return true;
        };
        let relation = if caller.dot == 0 {
            &self.associativities.right
        } else if caller.dot + 1 == production.items.len() {
            &self.associativities.left
        } else {
            return true;
        };
        let Some(child) = self.productions[child].parse_label.as_deref() else {
            return true;
        };
        !relation.contains(&(parent.to_owned(), child.to_owned()))
    }

    /// Whether the priority filter's check of the edge between `caller`'s node and a node built
    /// by `child` at the caller's dot passes ([`Grammar::edge_rejects`]: no scope, cast,
    /// priority or associativity violation there). A temporary recognition production builds
    /// the node of another production (`Production::term_production`) whose child positions it
    /// does not know: it passes.
    fn priority_admits(&self, caller: State, child: usize) -> bool {
        let recognizer = &self.productions[caller.production];
        if recognizer.term_production.is_some() {
            return true;
        }
        let position = recognizer.items[..caller.dot]
            .iter()
            .filter(|item| matches!(item, Item::NonTerminal(_)))
            .count()
            + 1;
        let node = self.productions[child].term_production.unwrap_or(child);
        !self.edge_rejects(caller.production, node, position)
    }

    /// Drop completed nodes whose top label violates the caller's associativity on the side they
    /// would occupy. Rejecting those boundaries before the caller packs its derivations keeps a
    /// long associative chain from expanding into a Catalan-sized forest. Every other boundary
    /// check waits for the priority pass over the completed caller.
    fn filter_associative_boundary<'a>(
        &self,
        caller: State,
        nodes: &'a BTreeSet<Rc<PackedTerm>>,
        filter: PriorityFilter,
        first_violation: &mut Option<ParseError>,
    ) -> Cow<'a, BTreeSet<Rc<PackedTerm>>> {
        let production = &self.productions[caller.production];
        let Some(parent) = production.parse_label.as_deref() else {
            return Cow::Borrowed(nodes);
        };
        if filter == PriorityFilter::Ignored {
            return Cow::Borrowed(nodes);
        }
        let (relation, side) = if caller.dot == 0 {
            (&self.associativities.right, "left")
        } else if caller.dot + 1 == production.items.len() {
            (&self.associativities.left, "right")
        } else {
            return Cow::Borrowed(nodes);
        };
        let violates = |node: &PackedTerm| {
            self.packed_top_parse_label(node)
                .is_some_and(|child| relation.contains(&(parent.to_owned(), child.to_owned())))
        };
        // Most boundaries reject nothing; they pass the caller's set through without copying it.
        if !nodes.iter().any(|node| violates(node)) {
            return Cow::Borrowed(nodes);
        }
        Cow::Owned(
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
                .collect(),
        )
    }

    /// Cross the shared packed-forest boundary only after the transforms that precede inference.
    ///
    /// Record collapse allocates generated variables against every name in the original forest,
    /// including losing root interpretations. Collect that small context before pruning so the
    /// allocation remains stable without materializing those losing trees. Every transformer
    /// before inference operates on the identity-shared DAG, so a subterm that several
    /// alternatives share is transformed once and stays shared.
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

/// A machine-integer literal's width is the number its digits after the first `p`/`P` spell,
/// in canonical decimal spelling; a token without one keeps the scanning instantiation's sort.
fn mint_literal_sort(result: &Sort, token: &str) -> Sort {
    token.find(['p', 'P']).map_or_else(
        || result.clone(),
        |index| {
            let width = &token[index + 1..];
            let width = match numeral_spelling(width) {
                NumeralSpelling::NonCanonical { canonical } => canonical,
                NumeralSpelling::Canonical | NumeralSpelling::NotNumeral => width,
            };
            Sort::with_parameters(result.name.clone(), vec![Sort::new(width)])
        },
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

/// The term a completed production denotes over its lowered children.
///
/// Fails only for a production labelled `#OuterCast` whose result sort has no sort projection;
/// `span` locates that diagnostic.
/// The KAST term of one node of `production` over its lowered `children`, which it takes over:
/// a node is built from its children without copying them, so lowering a tree costs time in
/// proportion to its size, whatever its height.
fn lower_term(
    production: &Production,
    mut children: Vec<Term>,
    span: Option<TermSpan>,
    denotations: &SortDenotations,
) -> Result<Term, ParseError> {
    if production.transparent || production.label.is_none() && children.len() == 1 {
        return Ok(children.swap_remove(0));
    }
    let mut label = production
        .label
        .clone()
        .unwrap_or_else(|| Label::new("#anonymous"));
    // The outer-cast label is parser-only: `{term}:>Sort` reads `term` as a term of the cast's
    // result sort, which is the sort projection of that sort. `add_casts` adds `#OuterCast`
    // productions only for result sorts with a sort projection; a definition's own production
    // labelled `#OuterCast` may have any result, and one without a projection denotes nothing.
    if label.is(InternalLabel::OuterCast) {
        label = Label::projection(&production.result).ok_or_else(|| {
            ParseError::ProjectionCastWithoutProjection {
                sort: production.result.clone(),
                span,
            }
        })?;
    }
    if label.is(InternalLabel::KToken)
        && let [value, sort] = children.as_slice()
        && let (Some(value), Some(sort)) = (kstring_token(value), kstring_token(sort))
        && let (Ok(value), Ok(sort)) = (
            crate::kast::string::unquote(value),
            crate::kast::string::unquote(sort),
        )
        && let Ok(sort) = crate::kast::parser::parse_sort_text(&sort)
    {
        return Ok(Term::Token {
            token: value,
            sort: denotations.denote(&sort).clone(),
        });
    }
    let pair = |children: Vec<Term>| -> [Box<Term>; 2] {
        let [first, second] = <[Term; 2]>::try_from(children)
            .unwrap_or_else(|_| unreachable!("the arm matched two children"));
        [Box::new(first), Box::new(second)]
    };
    Ok(match (InternalLabel::of(&label.name), children.len()) {
        (Some(InternalLabel::EmptyK), 0) => Term::Sequence(Vec::new()),
        (Some(InternalLabel::KSequence), _) => Term::sequence(children),
        (Some(InternalLabel::KRewrite), 2) => {
            let [left, right] = pair(children);
            Term::Rewrite { left, right }
        }
        (Some(InternalLabel::KAs), 2) => {
            let [pattern, alias] = pair(children);
            Term::As { pattern, alias }
        }
        _ => Term::Apply {
            label,
            arguments: children,
        },
    })
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
                &mut Pruning::default(),
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
        fn reports_errors_after_forest_construction_without_a_retry() {
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
            assert!(matches!(
                &baseline,
                Err(ParseError::Ambiguous { parses: 2, .. })
            ));
            PARSE_ATTEMPTS.set(0);
            assert_eq!(grammar.parse(&Sort::new("Start"), "x"), baseline);
            assert_eq!(PARSE_ATTEMPTS.get(), 1);
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
            let mut pruning = Pruning::default();
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
                &mut pruning,
            );
            assert!(result.is_err());
            assert!(pruning.pruned);
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
            match term.into_parts() {
                ParsedParts::Term(term) => PackedTerm::leaf(term),
                ParsedParts::Production {
                    production,
                    children,
                    metadata,
                } => PackedTerm::production(
                    production,
                    children.into_iter().map(pack).collect(),
                    metadata,
                ),
                ParsedParts::Ambiguity(alternatives) => {
                    PackedTerm::ambiguity(alternatives.into_iter().map(pack).collect())
                }
                ParsedParts::InstantiatedProduction { .. } => {
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
    }

    #[test]
    fn incremental_ambiguity_revisits_scan_derivations() {
        let grammar = incremental_ambiguity_grammar(true);
        reset_chart_work_counters();

        assert_incremental_ambiguity(grammar.parse(&Sort::new("Start"), "x!"));

        let counters = chart_work_counters();
        eprintln!("Incremental ambiguity scan chart work: {counters:?}");
        assert!(counters.existing_state_growth_changes > 0);
        assert!(counters.revisit_pops > 0);
        assert!(counters.revisit_derivations_read > 0);
        assert!(counters.scan_revisit_derivations_read > 0);
    }

    #[test]
    fn incremental_ambiguity_revisits_completion_derivations() {
        let grammar = incremental_ambiguity_grammar(false);
        reset_chart_work_counters();

        assert_incremental_ambiguity(grammar.parse(&Sort::new("Start"), "x"));

        let counters = chart_work_counters();
        eprintln!("Incremental ambiguity completion chart work: {counters:?}");
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
        // The labelled chains are constructors, so they give no subsort order; the order is
        // the one every definition has, with `K` above the user sorts. Without that top an
        // anonymous variable under a losing alternative is unconstrained, and each of the
        // incomparable sorts it can take is a separate maximal typing.
        grammar.subsort_relations.extend([
            (Sort::new("Good"), Sort::new("K")),
            (Sort::new("Bad"), Sort::new("K")),
        ]);
        let mut shared = PackedTerm::leaf(Term::Variable {
            name: "_".to_owned(),
            sort: None,
        });
        // Unpacking the DAG into an owned tree visits 2^(depth + 2) - 3 nodes and the pruned
        // path depth + 2: 4093 against 12 here. A deeper DAG separates them no further and only
        // makes the owned Z3 baseline exponentially slower to solve.
        let depth = 10;
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
            .infer_packed_sorts(Rc::clone(&shared), &Sort::new("Good"), false, Ok)
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
        let ParsedParts::Production { children, .. } = materialized.into_parts() else {
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
        let ParsedParts::Production { children, .. } = materialized.into_parts() else {
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
        let ParsedParts::Production { children, .. } = materialized.into_parts() else {
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
        let ParsedParts::Production { children, .. } = materialized.into_parts() else {
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

#[cfg(test)]
mod mint_literal_tests {
    use super::*;

    /// The width is the number the digits spell, so every spelling of eight names `MInt{8}`;
    /// this holds in both builds, whatever inference later decides about the parametric sort.
    #[test]
    fn mint_literal_width_is_the_canonical_numeral() {
        let mint = Sort::new("MInt");
        let mint_eight = Sort::with_parameters("MInt", vec![Sort::new("8")]);
        for token in ["0p8", "0p08", "0P008"] {
            assert_eq!(mint_literal_sort(&mint, token), mint_eight, "{token}");
        }
        assert_eq!(
            mint_literal_sort(&mint, "1p000"),
            Sort::with_parameters("MInt", vec![Sort::new("0")])
        );
        assert_eq!(mint_literal_sort(&mint_eight, "12"), mint_eight);
    }
}
