//! ```toml algorithm
//! id = "parser.earley.recognize"
//! name = "agenda-driven Earley recognition"
//! sites = ["Grammar::parse_attempt", "Grammar::recognize", "Grammar::explain_violation", "Grammar::lower_inferred", "Grammar::parse", "Grammar::parse_with_context_and_diagnostic_provenance", "Grammar::parse_in_context", "Grammar::diagnose", "Grammar::explain", "Grammar::advanced_item_useful", "Grammar::completion_useful", "Grammar::node_reaches_root", "Grammar::priority_admits", "RemainingTokens::new", "Reach::rest_follows", "InstanceNodes::intern"]
//! variable = "p = chart-agenda pops; d = dispatch cost and derivations read; B = input bytes; s = interned sorts; P = distinct lexemes among the input's tokens; u = nodes (chart, production, and the production of the node it is in the forest, which differs only for a production that passes its child through) whose usefulness the completion lookahead decides once per next token and count of deferred-scope witnesses before the position, and whose root reachability it searches, each again only when asked with a later earliest end than the bounds already known for it, each search over the waiting items of the charts it reaches, each item judged by the associativity and priority relations at its edge (a priority violation, where a rewrite, sequence or #let could defer a scope error, only against the first witness token after the caller's origin) and by where the input's next token its rest can begin with lies (O(P log B))"
//! counters = ["ParserParseAttempts", "ParserChartAgendaPops", "ParserChartRevisitPops", "ParserChartDerivationsRead", "ParserChartPredictionAttempts", "ParserChartCompletionCandidates", "ParserTerminalPredictionsSkipped", "ParserNonterminalPredictionsSkipped"]
//! span = "per problem"
//!
//! [[cost]]
//! mode = "recognition (the chart loop of recognize)"
//! bound = "O(B x s) chart allocation plus O(p x d) plus the memoized usefulness searches, O(u) pairs each over the waiting items of one chart; a filtered recognition skips the completions no parse can contain, so p is linear in the input for right-recursive lists and associativity-disambiguated chains, also beside other operators of their sort and in a rule body, which complete every enclosing list or chain at every position (quadratic p) without it; a chain written directly as a side of a rewrite keeps every doomed reading that takes the rewrite as an operand (cubic) unless the input has only one token that can begin a rewrite, sequence or #let, where the first attempt skips them (DoomedEdges); the input's tokens from the first position a completion is judged at are read once, O(B) scanner reads; the instances of one parametric production completed over one span with the same children are one node (one hashed lookup each), so d does not grow with the depth of a nesting of them"
//!
//! [[cost]]
//! mode = "one parse attempt (parse_attempt)"
//! bound = "recognition plus the post-recognition passes called at the end of parse_attempt, each carried by its own card (prepare_packed_forest, inference, then through lower_inferred resolve_terminators, filter_overloads, insert_empty_lists, remove_brackets_casts, factor and resolve ambiguity)"
//!
//! [[cost]]
//! mode = "one failed parse attempt whose recognition removed a derivation for a priority or associativity violation (explain_violation)"
//! bound = "two recognitions, the second with the relations ignored and every node one stand-in (each item processed once, no forest), plus either one no-parse diagnostic or, when the second finds a derivation of the whole input, a third, forest-building recognition with the relations ignored and the error-reporting passes of prepare_packed_forest over its complete derivations; a grammar with a same-span cycle builds that forest instead of the second; the forest-building recognition cuts a node that repeats itself over one span, so the violation reported is one a derivation of the input breaks; every recognition charges its chart steps (an item, the derivations it reads, the callers a completion advances) and the forest passes as many again as the recognition that built the forest against the diagnostic's work limit (DiagnosticWork), and stops when it is reached"
//!
//! [[cost]]
//! mode = "filtered attempt with retry (parse_in_context, diagnose)"
//! bound = "at most two parse attempts, after a first that skipped edges to doomed readings (DoomedEdges) and failed, which is then made again keeping them; the second only when the first found no derivation of the input (its error is read from the chart; an error computed from the forest is the first attempt's); the retry makes every prediction and, before the last chart the first attempt reached, skips only the completions the input cannot continue, judged without the priority and associativity relations, and cuts a node that repeats itself over one span instead of reporting a cycle, so a failed parse of an associativity-disambiguated chain would take the cubic recognition of that chain's relation-free grammar; every attempt and explanation after the first shares one work limit (DiagnosticWork), the larger of a floor and 16 times the first attempt's chart steps, past which the first attempt's own error is reported, so a failed parse takes chart work linear in its first attempt's plus the floor"
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
pub(crate) mod exclusion;
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
use self::exclusion::{Exclusions, NodeShape, Side};
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
use std::num::NonZeroU64;
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
    /// The work the diagnostic of a failure may take after the first attempt.
    diagnostic_work: DiagnosticWork,
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
/// (`Grammar::diagnose`).
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
    /// Which edges to a doomed node may be skipped.
    doomed: DoomedEdges,
    /// Set when an edge that `DoomedEdges::Kept` keeps is skipped.
    doomed_pruned: &'a std::cell::Cell<bool>,
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

    /// How many such witnesses the input holds.
    fn deferral_count(&self) -> usize {
        self.deferrals.len()
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

/// A node the root-reachability searches judge: its origin, the production that builds it, and
/// the production of the node it is in the forest (`Grammar::stands_for`).
type NodeKey = (usize, usize, usize);

/// A completion `Grammar::completion_useful` judges: the node, the scanner's next token, and
/// how many witnesses of a deferred scope error come before the position.
type CompletionKey = (NodeKey, Option<usize>, usize);

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
    /// Which edges to a doomed node the attempt may skip (`DoomedEdges`); set by the caller.
    pub(super) doomed: DoomedEdges,
    /// Whether the attempt skipped an edge that `DoomedEdges::Kept` keeps.
    pub(super) doomed_pruned: bool,
    /// Whether the attempt skipped a prediction or a completion an unfiltered attempt makes.
    pub(super) pruned: bool,
    /// The last non-empty chart of the attempt's recognition of the whole input under the
    /// priority and associativity relations, when it found no derivation of the input; `None`
    /// when it found one, or when recognition itself failed (a cycle).
    pub(super) furthest: Option<usize>,
}

/// How much chart work the diagnostic of a failed parse may take after the parse's first
/// attempt.
///
/// A failed parse is reported by the diagnostic of its context-free grammar: a relation that a
/// derivation of the input breaks, or where the grammar's longest viable prefix ends. Finding it
/// means recognizing the input again without the pruning the relations allow, and possibly
/// without the relations, which is cubic in the length of an associativity-disambiguated chain
/// (the chart of an ambiguous grammar). Under a limit, a diagnostic that would take more chart
/// steps than the limit is abandoned and the failure is reported by the first attempt's own
/// error, read from the recognition under the relations, which then says that it was not
/// explained (`ParseError::NoParse::work_limit`). The limit is the larger of `floor` and
/// [`DiagnosticWork::FACTOR`] times the steps of the first attempt, so a failed parse costs at
/// most a constant factor of its first attempt, plus `floor`, and a diagnostic whose work is
/// within that factor of the first attempt's is never abandoned. A chart step is one item taken
/// from a chart's agenda, one derivation it reads, or one caller a completion advances.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DiagnosticWork {
    /// At most the larger of `floor` chart steps and `FACTOR` times the first attempt's.
    Limited { floor: u64 },
    /// Always the context-free diagnostic, whatever it costs.
    Unlimited,
}

impl DiagnosticWork {
    /// The factor of the first attempt's chart steps that a diagnostic may always take.
    pub const FACTOR: u64 = 16;
    /// The default limit: a floor of 2^20 chart steps, from about a tenth of a second of chart
    /// work in a release build (a chain's relation-free chart) to about half a second (a
    /// relation-free forest and the passes over it).
    pub const DEFAULT: Self = Self::Limited { floor: 1 << 20 };
    /// The environment variable that sets the limit: `unlimited`, or the floor in chart steps.
    pub const VARIABLE: &'static str = "KRUST_PARSE_DIAGNOSTIC_WORK";

    /// The limit [`Self::VARIABLE`] sets, or [`Self::DEFAULT`] when it is unset or holds
    /// anything [`Self::parse`] does not read. Read once per process. `krust` refuses an
    /// unreadable value before it parses anything ([`Self::environment`]), so this fallback
    /// serves only an embedder that does not check.
    pub fn from_environment() -> Self {
        static FROM_ENVIRONMENT: OnceLock<DiagnosticWork> = OnceLock::new();
        *FROM_ENVIRONMENT
            .get_or_init(|| Self::environment().ok().flatten().unwrap_or(Self::DEFAULT))
    }

    /// The limit [`Self::VARIABLE`] sets: `None` when it is unset or empty, and an error naming
    /// the variable and its value when it holds anything else [`Self::parse`] does not read. A
    /// value set to change the limit and read as the default would leave a diagnostic other than
    /// the one asked for, with nothing to say so.
    pub fn environment() -> Result<Option<Self>, String> {
        let value = match std::env::var(Self::VARIABLE) {
            Ok(value) if value.trim().is_empty() => return Ok(None),
            Ok(value) => value,
            Err(std::env::VarError::NotPresent) => return Ok(None),
            Err(std::env::VarError::NotUnicode(value)) => value.to_string_lossy().into_owned(),
        };
        Self::parse(&value).map(Some).ok_or_else(|| {
            format!(
                "{} must be `unlimited` or a number of chart steps, not `{value}`",
                Self::VARIABLE
            )
        })
    }

    /// `unlimited`, or a decimal number of chart steps for the floor (`_` separators allowed).
    pub fn parse(value: &str) -> Option<Self> {
        let value = value.trim();
        if value.eq_ignore_ascii_case("unlimited") {
            Some(Self::Unlimited)
        } else {
            value
                .replace('_', "")
                .parse()
                .ok()
                .map(|floor| Self::Limited { floor })
        }
    }

    /// The chart steps the diagnostic may take after a first attempt of `first` steps, at least
    /// one.
    fn limit(self, first: u64) -> NonZeroU64 {
        match self {
            Self::Limited { floor } => NonZeroU64::MIN.saturating_add(
                floor
                    .max(first.saturating_mul(Self::FACTOR))
                    .saturating_sub(1),
            ),
            Self::Unlimited => NonZeroU64::MAX,
        }
    }
}

/// The chart steps recognitions took, against a limit (`DiagnosticWork`).
#[derive(Clone, Copy, Debug)]
pub(super) struct WorkMeter {
    spent: u64,
    limit: u64,
}

impl WorkMeter {
    pub(super) const fn unlimited() -> Self {
        Self::limited(u64::MAX)
    }

    const fn limited(limit: u64) -> Self {
        Self { spent: 0, limit }
    }

    /// Counts `steps`; whether the total is still within the limit.
    fn charge(&mut self, steps: usize) -> bool {
        #[cfg(test)]
        update_chart_work_counters(|counters| counters.chart_steps += steps);
        self.spent = self
            .spent
            .saturating_add(u64::try_from(steps).unwrap_or(u64::MAX));
        self.spent <= self.limit
    }
}

/// A diagnostic recognition ran past its work limit (`DiagnosticWork`).
struct WorkLimitReached;

/// Why one parse attempt failed, before a violation it met is explained.
enum Failure {
    /// The attempt's error, final.
    Error(ParseError),
    /// The attempt found no derivation of the input.
    NoDerivation(Box<NoDerivation>),
    /// The attempt's recognition ran past its work limit.
    WorkLimit,
}

impl From<ParseError> for Failure {
    fn from(error: ParseError) -> Self {
        Self::Error(error)
    }
}

/// An attempt that found no derivation of the input.
struct NoDerivation {
    /// The no-parse diagnostic of the attempt's own chart.
    no_parse: ParseError,
    /// The violation the recognition met first, when it is to be explained: an attempt that
    /// skipped an edge to a doomed node (`DoomedEdges`) is made again keeping them instead.
    violation: Option<ParseError>,
    start_id: usize,
    start_position: usize,
    prediction_mode: PredictionMode,
}

/// Whether recognition drops the derivations that the priority and associativity relations rule
/// out. A violation explains a failed parse only when the input has a derivation that the
/// violation rules out, so a failed parse that recorded one is recognized once more with the
/// relations ignored to tell the two apart (`Grammar::explain_violation`).
#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum PriorityFilter {
    Enforced,
    Ignored,
}

/// Whether a filtered recognition may skip an edge that would build a doomed node: one that
/// breaks a relation but that the priority filter keeps for the preference among the readings
/// of the root, because it, or a child checked before the breaking edge, holds a rewrite,
/// sequence or `#let` below an operator (a scope error the filter defers).
///
/// The preference reads a doomed node only when it is, or lies inside, a reading of the root
/// rooted at a rewrite, sequence or `#let`; every other doomed node is dropped by the filter
/// after recognition, or discarded with the losing readings. Such a node contains a rewrite,
/// sequence or `#let` node, and so a token of its first lexical item (`DeferredScopes`); a
/// rewrite, sequence or `#let` node above it holds its own such token, outside every child.
/// So in an input with one such token in all, no doomed node is read by the preference, and
/// skipping the edges to them leaves every reading that can be the parse. What it changes is
/// the forest a failed parse is explained from: an attempt that skipped one and failed is made
/// again keeping them (`Grammar::diagnose`).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) enum DoomedEdges {
    /// Keep every edge the filter could keep for the preference.
    #[default]
    Kept,
    /// Skip every edge that breaks a relation when the input has one token that can begin a
    /// rewrite, sequence or `#let`.
    SkippedBesideOneScope,
}

/// The outcome of the recognition phase of one parse attempt.
struct Recognition {
    charts: Vec<Chart>,
    /// The completed start productions spanning the whole input.
    parses: BTreeSet<Rc<PackedTerm>>,
    /// The first priority or associativity violation that removed a derivation, in chart order.
    first_violation: Option<ParseError>,
    /// Whether an edge that `DoomedEdges::Kept` keeps was skipped.
    doomed_pruned: bool,
    /// Whether the recognition stopped at its work limit; its charts and parses are then
    /// incomplete and say nothing about the input.
    work_limit_reached: bool,
}

/// One entry of the readings reported at an ambiguous subterm, one per root key (head and
/// arity) of those readings: the least of the readings with that key in term order, rendered
/// with the text of the production its root came from when the definition has one.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AmbiguousParse {
    pub production: Option<String>,
    pub term: String,
    /// Whether other readings have the root key of this one.
    pub more_with_same_root: bool,
}

/// One of several subterms at which the readings of an ambiguous parse differ: the span it
/// covers and one entry per root key of its readings, of which it has several.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AmbiguityPlace {
    pub span: Option<TermSpan>,
    /// The source location of `span`, when the caller that knows the source sets it.
    pub location: Option<crate::definition::Location>,
    pub alternatives: Vec<AmbiguousParse>,
}

/// The entries of a reported subterm, numbered from 1 (`ParseError::Ambiguous`).
fn write_ambiguous_parses(
    formatter: &mut fmt::Formatter<'_>,
    alternatives: &[AmbiguousParse],
) -> fmt::Result {
    for (index, alternative) in alternatives.iter().enumerate() {
        write!(
            formatter,
            "\n{}: {}\n    {}",
            index + 1,
            alternative.production.as_deref().unwrap_or(""),
            alternative.term
        )?;
        if alternative.more_with_same_root {
            formatter.write_str("\n    and other readings with the same root")?;
        }
    }
    Ok(())
}

/// One subterm of an ambiguity reported as several (`ParseError::Ambiguous`), numbered
/// `number` and located by its source location, or else by its span.
fn write_ambiguity_place(
    formatter: &mut fmt::Formatter<'_>,
    number: usize,
    place: &AmbiguityPlace,
) -> fmt::Result {
    write!(formatter, "\nSubterm {number}")?;
    match (place.location, place.span) {
        (Some(location), _) => write!(
            formatter,
            " at {}:{}",
            location.start_line, location.start_column
        )?,
        (None, Some(span)) => write!(formatter, " at bytes {}..{}", span.start, span.end)?,
        (None, None) => {}
    }
    formatter.write_str(":")?;
    write_ambiguous_parses(formatter, &place.alternatives)
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
        expected: Box<[String]>,
        input: NoParseInput,
        previous: Option<String>,
        span: Option<TermSpan>,
        /// The chart steps the diagnostic was limited to, when it was abandoned there
        /// (`DiagnosticWork`): the position is then where the recognition under the priority
        /// and associativity relations stopped, and whether the input breaks one of them was
        /// not decided. `None` for the diagnostic of the context-free grammar.
        work_limit: Option<NonZeroU64>,
    },
    InvalidParseShape {
        expected: String,
    },
    /// The input has several readings, the distinct terms its parses lower to.
    Ambiguous {
        /// One entry per root key of the readings of the subterm at `span`, when they have
        /// several there; empty when they are reported as several subterms (`places`).
        alternatives: Vec<AmbiguousParse>,
        /// The smallest subterm outside which every reading agrees.
        span: Option<TermSpan>,
        /// When the readings at `span` have one root key, the subterms below it at which they
        /// differ, each with one entry per root key of its readings.
        places: Vec<AmbiguityPlace>,
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
    /// lowered the parse to) or `Err` with the message of its rejection. Two rejections are
    /// agreement unless one of them is an ambiguity the other does not report alike, since
    /// an ambiguity is reported from the readings both engines must keep.
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
                input,
                previous,
                work_limit,
                ..
            } => {
                match input {
                    NoParseInput::Token { value } => {
                        write!(formatter, "Parse error: unexpected token '{value}'")?;
                        if let Some(previous) = previous {
                            write!(formatter, " following token '{previous}'")?;
                        }
                        formatter.write_str(".")?;
                    }
                    NoParseInput::EndOfInput => {
                        formatter.write_str("Parse error: unexpected end of file")?;
                        if let Some(previous) = previous {
                            write!(formatter, " following token '{previous}'")?;
                        }
                        formatter.write_str(".")?;
                    }
                    NoParseInput::UnrecognizedInput { value } => write!(
                        formatter,
                        "Scanner error: unexpected character sequence '{value}'."
                    )?,
                }
                if let Some(limit) = work_limit {
                    write!(
                        formatter,
                        " No reading of the input that respects the priority and associativity \
                         relations and finds later in the input the tokens it still needs (a \
                         closing parenthesis, say) can be completed past this point; whether one \
                         that breaks a relation can was not decided within the diagnostic's limit \
                         of {limit} chart steps ({} raises it).",
                        DiagnosticWork::VARIABLE
                    )?;
                }
                Ok(())
            }
            Self::InvalidParseShape { expected } => {
                write!(
                    formatter,
                    "parsed term does not have the expected {expected} shape"
                )
            }
            Self::Ambiguous {
                alternatives,
                places,
                ..
            } => {
                if places.is_empty() {
                    formatter.write_str("Parsing ambiguity.")?;
                    return write_ambiguous_parses(formatter, alternatives);
                }
                write!(
                    formatter,
                    "Parsing ambiguity: the readings differ in {} subterms.",
                    places.len()
                )?;
                for (index, place) in places.iter().enumerate() {
                    write_ambiguity_place(formatter, index + 1, place)?;
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
    /// The number of nonterminal items, and whether the first and the last item are
    /// nonterminals. The exclusions read them for every edge they judge, and `items` does not
    /// change once the production is added, so they are counted there and `shape` copies them.
    nonterminals: usize,
    first_nonterminal: bool,
    last_nonterminal: bool,
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
    /// The production as the relation filter sees its node ([`NodeShape`]).
    fn shape(&self) -> NodeShape<'_> {
        NodeShape {
            parse_label: self.parse_label.as_ref(),
            labelled: self.label.is_some(),
            token: self.token,
            bracket: self.bracket,
            transparent: self.transparent,
            record: self.record.is_some(),
            items: self.items.len(),
            nonterminals: self.nonterminals,
            first_nonterminal: self.first_nonterminal,
            last_nonterminal: self.last_nonterminal,
            apply_priority: self.apply_priority.as_ref(),
        }
    }

    /// Whether a node of this production is its only child itself (`build_packed_term`,
    /// [`NodeShape::passes_child_through`]), so the filters judge the child wherever it stands.
    fn passes_child_through(&self) -> bool {
        self.shape().passes_child_through()
    }

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

/// The most decisions of what it gives its waiting callers that one completion on this thread
/// made since the last call ([`chart::ChartWorkCounters::most_caller_group_decisions`]).
#[cfg(test)]
pub(in crate::inner) fn take_most_caller_group_decisions() -> usize {
    let most = chart_work_counters().most_caller_group_decisions;
    update_chart_work_counters(|counters| counters.most_caller_group_decisions = 0);
    most
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
    // Invariant: when set, this indexes `priorities` and `associativities`; cleared whenever
    // either changes.
    relation_index: OnceLock<RelationIndex>,
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

/// The grammar's relations ([`Exclusions`]), with each production's parse label numbered when
/// it occurs in an associativity relation, so that a pair of labels, or of the productions
/// carrying them, is looked up without hashing or copying either label.
#[derive(Clone, Debug)]
struct RelationIndex {
    exclusions: Exclusions,
    /// The number of each production's parse label, when that label occurs in an associativity
    /// relation.
    production_labels: Vec<Option<u32>>,
    /// For each production and each dot position before its end, the edge
    /// [`Grammar::associativity_edge`] selects there, computed once per grammar.
    edges: Vec<Box<[AssociativityEdge]>>,
}

impl RelationIndex {
    fn new(
        priorities: &PartialOrder<String>,
        relations: &AssociativityRelations,
        productions: &[Production],
    ) -> Self {
        let exclusions = Exclusions::new(priorities.clone(), relations);
        let production_labels = productions
            .iter()
            .map(|production| {
                production
                    .parse_label
                    .as_deref()
                    .and_then(|label| exclusions.associativity_id(label))
            })
            .collect::<Vec<_>>();
        let edges = productions
            .iter()
            .enumerate()
            .map(|(index, recognizer)| {
                (0..recognizer.items.len())
                    .map(|dot| associativity_edge_at(productions, &production_labels, index, dot))
                    .collect()
            })
            .collect();
        Self {
            exclusions,
            production_labels,
            edges,
        }
    }

    fn forbids(&self, parent: u32, child: u32, left_child: bool) -> bool {
        self.exclusions.associativity_forbids(
            parent,
            child,
            if left_child { Side::Left } else { Side::Right },
        )
    }
}

/// An edge the associativity relations judge: the production of the node, and whether the
/// child is its left (`true`) or its right child; `None` where they judge none.
type AssociativityEdge = Option<(usize, bool)>;

/// [`Grammar::associativity_edge`] at `dot` of `production`, computed once per grammar.
fn associativity_edge_at(
    productions: &[Production],
    production_labels: &[Option<u32>],
    production: usize,
    dot: usize,
) -> AssociativityEdge {
    let recognizer = &productions[production];
    if recognizer.passes_child_through() {
        return None;
    }
    let node = recognizer.term_production.unwrap_or(production);
    production_labels[node]?;
    // A node's children are the recognizer's nonterminals, in order (`build_packed_term`).
    let nonterminals = |items: &[Item]| {
        items
            .iter()
            .filter(|item| matches!(item, Item::NonTerminal(_)))
            .count()
    };
    let position = nonterminals(&recognizer.items[..dot]) + 1;
    match productions[node]
        .shape()
        .judged_side(position, nonterminals(&recognizer.items))
    {
        Some(Side::Left) => Some((node, true)),
        Some(Side::Right) => Some((node, false)),
        Some(Side::Middle) | None => None,
    }
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
            relation_index: OnceLock::new(),
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
        self.parse_in_context(
            start,
            input,
            ParseContext {
                is_anywhere,
                provenance: ParseProvenance {
                    source,
                    base_offset,
                },
                diagnostic_provenance,
                diagnostic_work: DiagnosticWork::from_environment(),
            },
        )
    }

    /// Parse `input` from the sort `start` denotes, with the diagnostic of a failure limited to
    /// `diagnostic_work` after the first attempt (`DiagnosticWork`).
    pub fn parse_with_diagnostic_work(
        &self,
        start: &Sort,
        input: &str,
        diagnostic_work: DiagnosticWork,
    ) -> Result<Term, ParseError> {
        self.parse_in_context(
            start,
            input,
            ParseContext {
                is_anywhere: false,
                provenance: ParseProvenance {
                    source: SourceId(0),
                    base_offset: 0,
                },
                diagnostic_provenance: false,
                diagnostic_work,
            },
        )
    }

    /// A parse: one filtered attempt and, when it fails, the diagnostic of the failure, within
    /// `context.diagnostic_work` (`DiagnosticWork`). A diagnostic abandoned at its limit
    /// reports the first attempt's error unexplained: for an attempt that found no derivation,
    /// its own no-parse diagnostic, marked with the limit.
    fn parse_in_context(
        &self,
        start: &Sort,
        input: &str,
        context: ParseContext,
    ) -> Result<Term, ParseError> {
        let start = self.sort_denotations.denote(start);
        let mut pruning = Pruning {
            doomed: DoomedEdges::SkippedBesideOneScope,
            ..Pruning::default()
        };
        let mut first_work = WorkMeter::unlimited();
        let failure = match self.parse_attempt(
            start,
            input,
            context,
            PredictionMode::Filtered,
            &mut pruning,
            &mut first_work,
        ) {
            Ok(term) => return Ok(term),
            Err(failure) => failure,
        };
        let unexplained = match &failure {
            Failure::Error(error) => error.clone(),
            Failure::NoDerivation(failure) => failure.no_parse.clone(),
            Failure::WorkLimit => unreachable!("the first attempt has no work limit"),
        };
        let limit = context.diagnostic_work.limit(first_work.spent);
        match self.diagnose(
            start,
            input,
            context,
            failure,
            pruning,
            &mut WorkMeter::limited(limit.get()),
        ) {
            Ok(result) => result,
            Err(WorkLimitReached) => Err(match unexplained {
                ParseError::NoParse {
                    position,
                    expected,
                    input,
                    previous,
                    span,
                    work_limit: _,
                } => ParseError::NoParse {
                    position,
                    expected,
                    input,
                    previous,
                    span,
                    work_limit: Some(limit),
                },
                error => error,
            }),
        }
    }

    /// The outcome of a parse whose first attempt failed with `failure`, after `pruning`.
    ///
    /// Skipping the edges to doomed nodes keeps every reading that can be the parse, but not the
    /// forest a failure is computed from (`DoomedEdges`): such a failure is computed again
    /// keeping them. A failure without a derivation is explained from the chart, whose items the
    /// skipped work changes: it is retried with the skipped work restored where the diagnostic
    /// reads it. A failure after recognition (an ambiguity, sort inference, a relation error of
    /// the forest, a cycle) is computed from the forest, which skipping leaves as it is
    /// (`PredictionMode`), so it is already the error of an unfiltered recognition.
    /// Invariant: a retry occurs exactly when the filtered recognizer, or the recognition
    /// explaining its violation, pruned at least one prediction or completion and found no
    /// derivation of the input, and it reruns the complete pipeline with the same context,
    /// skipping completions only before the last chart the filtered recognition reached. An
    /// explanation a retry would replace is not computed.
    fn diagnose(
        &self,
        start: &Sort,
        input: &str,
        context: ParseContext,
        mut failure: Failure,
        mut pruning: Pruning,
        work: &mut WorkMeter,
    ) -> Result<Result<Term, ParseError>, WorkLimitReached> {
        if pruning.doomed_pruned {
            pruning = Pruning::default();
            failure = match self.parse_attempt(
                start,
                input,
                context,
                PredictionMode::Filtered,
                &mut pruning,
                work,
            ) {
                Ok(term) => return Ok(Ok(term)),
                Err(failure) => failure,
            };
        }
        let error = if pruning.pruned && pruning.furthest.is_some() {
            None
        } else {
            Some(self.explain(failure, input, context, &mut pruning.pruned, work)?)
        };
        if let (true, Some(horizon)) = (pruning.pruned, pruning.furthest) {
            return match self.parse_attempt(
                start,
                input,
                context,
                PredictionMode::Retry { horizon },
                &mut Pruning::default(),
                work,
            ) {
                Ok(term) => Ok(Ok(term)),
                Err(failure) => Ok(Err(self.explain(failure, input, context, &mut false, work)?)),
            };
        }
        Ok(Err(
            error.expect("a failure that is not retried is explained")
        ))
    }

    /// The error of a failed attempt: its violation explained (`Grammar::explain_violation`),
    /// or its own error.
    fn explain(
        &self,
        failure: Failure,
        input: &str,
        context: ParseContext,
        pruned: &mut bool,
        work: &mut WorkMeter,
    ) -> Result<ParseError, WorkLimitReached> {
        match failure {
            Failure::Error(error) => Ok(error),
            Failure::WorkLimit => Err(WorkLimitReached),
            Failure::NoDerivation(failure) => match failure.violation {
                None => Ok(failure.no_parse),
                Some(violation) => self.explain_violation(
                    violation,
                    failure.start_id,
                    failure.start_position,
                    input,
                    context,
                    failure.prediction_mode,
                    pruned,
                    work,
                ),
            },
        }
    }

    /// One parse attempt, with its violation explained and no work limit.
    #[cfg(test)]
    fn parse_attempt_explained(
        &self,
        start: &Sort,
        input: &str,
        context: ParseContext,
        prediction_mode: PredictionMode,
        pruning: &mut Pruning,
    ) -> Result<Term, ParseError> {
        let mut work = WorkMeter::unlimited();
        self.parse_attempt(start, input, context, prediction_mode, pruning, &mut work)
            .map_err(|failure| {
                self.explain(failure, input, context, &mut pruning.pruned, &mut work)
                    .unwrap_or_else(|WorkLimitReached| unreachable!("no work limit"))
            })
    }

    /// One parse attempt. A failure without a derivation of the input is returned with the
    /// attempt's no-parse diagnostic and the violation to explain, if any; explaining it is the
    /// caller's (`Grammar::explain`).
    fn parse_attempt(
        &self,
        start: &Sort,
        input: &str,
        context: ParseContext,
        prediction_mode: PredictionMode,
        pruning: &mut Pruning,
        work: &mut WorkMeter,
    ) -> Result<Term, Failure> {
        let ParseContext {
            is_anywhere,
            provenance,
            diagnostic_provenance,
            ..
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
            return Err(Failure::Error(self.no_parse(
                input,
                provenance,
                diagnostic_provenance,
                &charts,
                &mut scanner_cache,
            )));
        };
        let Recognition {
            charts,
            parses,
            first_violation,
            doomed_pruned,
            work_limit_reached,
        } = self.recognize(
            start_id,
            start_position,
            input,
            provenance,
            prediction_mode,
            PriorityFilter::Enforced,
            None,
            matches!(prediction_mode, PredictionMode::Retry { .. }),
            pruning.doomed,
            &mut pruning.pruned,
            work,
            &mut scanner_cache,
            &priority_memos,
        )?;
        if work_limit_reached {
            return Err(Failure::WorkLimit);
        }
        pruning.doomed_pruned = doomed_pruned;
        if parses.is_empty() {
            pruning.furthest = Some(
                charts
                    .iter()
                    .rposition(|chart| !chart.states.is_empty())
                    .unwrap_or(0),
            );
            let no_parse = self.no_parse(
                input,
                provenance,
                diagnostic_provenance,
                &charts,
                &mut scanner_cache,
            );
            return Err(Failure::NoDerivation(Box::new(NoDerivation {
                no_parse,
                // An attempt that skipped edges to doomed nodes and failed is made again keeping
                // them, which explains the failure; this one is not explained.
                violation: first_violation.filter(|_| !doomed_pruned),
                start_id,
                start_position,
                prediction_mode,
            })));
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
            return checked.map_err(Failure::Error);
        }
        self.infer_packed_sorts(forest, start, is_anywhere, |tree| {
            self.lower_inferred(tree, start)
        })
        .map_err(Failure::Error)
    }

    /// Why a parse whose recognition removed a derivation for `first_violation` failed.
    ///
    /// The violation explains the failure only when some derivation of the whole input breaks
    /// the priority and associativity relations; a derivation the relations removed while
    /// recognition explored a reading that fails anyway (for instance `A => B` as the left
    /// operand of a `=>` that never comes) does not. The input is therefore recognized again
    /// with the relations ignored: when that recognition also fails, the input has no derivation
    /// at all and the error is the place where it stops; otherwise the error is a violation of a
    /// derivation of the whole input, read from the forest of those derivations. That forest
    /// leaves out a node that repeats itself over one span (`Grammar::recognize`): no reading
    /// passes the relations, so the repetition is no cycle of a reading, and the derivations
    /// without it break the relations as every derivation does. Reporting instead the violation
    /// the failed recognition met first would make the error depend on the order it met items
    /// in, and on which items it skipped, including items no derivation of the input contains.
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
    ///
    /// Both recognitions count their chart steps against `work`; past its limit the explanation
    /// is abandoned (`DiagnosticWork`).
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
        work: &mut WorkMeter,
    ) -> Result<ParseError, WorkLimitReached> {
        let scanner_cache = &mut vec![None; input.len() + 1][..];
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
            let Ok(Recognition {
                charts,
                parses,
                work_limit_reached,
                ..
            }) = self.recognize(
                start_id,
                start_position,
                input,
                context.provenance,
                prediction_mode,
                PriorityFilter::Ignored,
                Some(&stand_in),
                false,
                DoomedEdges::Kept,
                pruned,
                work,
                scanner_cache,
                &priority_memos,
            )
            else {
                return Ok(first_violation);
            };
            if work_limit_reached {
                return Err(WorkLimitReached);
            }
            if parses.is_empty() {
                return Ok(self.no_parse(
                    input,
                    context.provenance,
                    context.diagnostic_provenance,
                    &charts,
                    scanner_cache,
                ));
            }
        }
        let before = work.spent;
        let Ok(Recognition {
            charts,
            parses,
            work_limit_reached,
            ..
        }) = self.recognize(
            start_id,
            start_position,
            input,
            context.provenance,
            prediction_mode,
            PriorityFilter::Ignored,
            None,
            true,
            DoomedEdges::Kept,
            pruned,
            work,
            scanner_cache,
            &priority_memos,
        )
        else {
            // Only a recognition error other than a repetition (which this recognition cuts)
            // ends here; the violation met first is then the only one known.
            return Ok(first_violation);
        };
        if work_limit_reached {
            return Err(WorkLimitReached);
        }
        if parses.is_empty() {
            return Ok(self.no_parse(
                input,
                context.provenance,
                context.diagnostic_provenance,
                &charts,
                scanner_cache,
            ));
        }
        drop(charts);
        // The passes over the forest are charged as many steps as the recognition that built it
        // took, which bounds the forest they read.
        let forest_steps = work.spent - before;
        if !work.charge(usize::try_from(forest_steps).unwrap_or(usize::MAX)) {
            return Err(WorkLimitReached);
        }
        let violation = self
            .check_packed_forest(PackedTerm::ambiguity(parses), &priority_memos)
            .err();
        // The check at hand-off judges an edge only where the filter judges it, and in the same
        // way, so a derivation the filter admits at every edge survives the recognition that
        // enforces the relations. That recognition can then fail although such a derivation
        // exists only when a scope error is deferred (a node built by a rewrite, a sequence or a
        // `#let` production) and the root preference keeps a reading that fails.
        debug_assert!(
            violation.is_some()
                || self.productions.iter().any(|production| {
                    production.parse_label.as_deref().is_some_and(|label| {
                        [
                            InternalLabel::KRewrite,
                            InternalLabel::KSequence,
                            InternalLabel::Let,
                        ]
                        .iter()
                        .any(|scope| scope.as_str() == label)
                    })
                }),
            "a failed recognition without deferred scope errors has a derivation every edge of \
             which the relations admit"
        );
        Ok(violation.unwrap_or(first_violation))
    }

    /// The recognition phase of a parse attempt: the Earley chart of `input` from the start sort
    /// and the completed start productions spanning it, dropping the derivations that violate the
    /// priority and associativity relations when `filter` enforces them. With a `stand_in`,
    /// every completed node is that node, so the recognition decides which items exist without
    /// building a forest (`Grammar::explain_violation`); it is used only with the relations
    /// ignored, and only for a grammar without same-span cycles.
    ///
    /// With `cut_repetitions`, a node that repeats itself over one span is left out of the
    /// forest instead of being reported as a cycle. Only a recognition made for the diagnostic of
    /// a failed parse cuts: a retry (`PredictionMode::Retry`), and the recognition with the
    /// relations ignored that explains a violation. A repetition adds no item (the node it
    /// repeats already completed the same state), so the charts are those of a recognition that
    /// reports it; and a failed parse has no reading the relations allow, so the repetition is
    /// part of no reading of the input the recognition could report as infinitely ambiguous.
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
        cut_repetitions: bool,
        doomed: DoomedEdges,
        pruned: &mut bool,
        work: &mut WorkMeter,
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
        // scanner's next token is `winner`, by `(origin, production, stands for, winner, region)`
        // (`Grammar::completion_useful`).
        let mut useful_completions = HashMap::new();
        // Whether a node of a production starting in a chart can be part of a parse of the whole
        // input, by `(origin, production, stands for)` (`Grammar::node_reaches_root`).
        let mut reaching_nodes = HashMap::new();
        // The tokens of the input from the first position a completion asks about them on,
        // read once, when the relations decide whether a node can reach the root.
        let mut remaining_tokens = None;
        // What a completion gives each group of its callers (below), kept across completions so
        // that it is allocated once per recognition.
        let mut boundaries: Vec<(usize, usize, Option<Rc<PackedTerm>>)> = Vec::new();
        let doomed_pruned = std::cell::Cell::new(false);
        // The relations a skipped completion is judged by (`PredictionMode`): a retry judges
        // only whether the input can continue an item, never where the relations let its node
        // sit.
        let usefulness_filter = match prediction_mode {
            PredictionMode::Retry { .. } => PriorityFilter::Ignored,
            PredictionMode::Filtered | PredictionMode::Unfiltered => filter,
        };
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
                // The work of this item: itself, the derivations it reads and, for a
                // completion, the callers it advances.
                let callers = if state.dot == production.items.len() {
                    charts[state.origin]
                        .waiting
                        .get(&production.result_id)
                        .map_or(0, Vec::len)
                } else {
                    0
                };
                if !work.charge(1 + derivations.len() + callers) {
                    return Ok(Recognition {
                        charts,
                        parses: BTreeSet::new(),
                        first_violation: None,
                        doomed_pruned: doomed_pruned.get(),
                        work_limit_reached: true,
                    });
                }
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
                        // What a caller receives from these nodes depends on its production and
                        // dot only (`filter_associative_boundary`), not on its origin; the callers
                        // waiting in one chart share a few of those, however many origins they
                        // have, so each is filtered and packed once per completion.
                        boundaries.clear();
                        #[cfg(test)]
                        update_chart_work_counters(|counters| counters.caller_group_decisions = 0);
                        let mut boundary = |caller: &State| {
                            if let Some((_, _, completed)) =
                                boundaries.iter().find(|(production, dot, _)| {
                                    *production == caller.production && *dot == caller.dot
                                })
                            {
                                return completed.clone();
                            }
                            #[cfg(test)]
                            update_chart_work_counters(|counters| {
                                counters.caller_group_decisions += 1;
                                counters.most_caller_group_decisions = counters
                                    .most_caller_group_decisions
                                    .max(counters.caller_group_decisions);
                            });
                            let completed = self.filter_associative_boundary(
                                *caller,
                                &nodes,
                                filter,
                                &mut first_violation,
                            );
                            let completed =
                                (!completed.is_empty()).then(|| pack_alternatives(&completed));
                            boundaries.push((caller.production, caller.dot, completed.clone()));
                            completed
                        };
                        let mut advance = |chart: &mut Chart,
                                           caller: State,
                                           caller_derivations: &Derivations,
                                           completed: Rc<PackedTerm>,
                                           earlier: Option<&[Chart]>|
                         -> Result<(), ParseError> {
                            #[cfg(test)]
                            update_chart_work_counters(|counters| {
                                counters.completion_caller_derivations_read +=
                                    caller_derivations.len();
                            });
                            let advanced = State {
                                dot: caller.dot + 1,
                                ..caller
                            };
                            if let (Some(analysis), Some(winner), Some(earlier)) =
                                (completion_analysis, winner, earlier)
                                && !self.advanced_item_useful(
                                    earlier,
                                    advanced,
                                    self.stands_for(advanced.production, state.production),
                                    winner,
                                    Reach {
                                        analysis,
                                        cycles,
                                        filter: usefulness_filter,
                                        root,
                                        remaining: remaining_tokens.as_ref(),
                                        from: canonical,
                                        doomed,
                                        doomed_pruned: &doomed_pruned,
                                    },
                                    &mut useful_completions,
                                    &mut reaching_nodes,
                                )
                            {
                                *pruned = true;
                                return Ok(());
                            }
                            self.add_chart_extensions(
                                chart,
                                advanced,
                                caller_derivations,
                                Some(&completed),
                            )?;
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
                                if let Some(completed) = boundary(caller)
                                    && let Some(caller_derivations) = origin.states.get(caller)
                                {
                                    advance(
                                        &mut later[0],
                                        *caller,
                                        caller_derivations,
                                        completed,
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
                                    let completed = boundary(caller)?;
                                    charts[state.origin].states.get(caller).map(|derivations| {
                                        (*caller, derivations.clone(), completed)
                                    })
                                })
                                .collect::<Vec<_>>();
                            for (caller, caller_derivations, completed) in callers {
                                advance(
                                    &mut charts[position],
                                    caller,
                                    &caller_derivations,
                                    completed,
                                    None,
                                )?;
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
            doomed_pruned: doomed_pruned.get(),
            work_limit_reached: false,
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
    /// which are final. `stands_for` is the production of the node the advanced item's node is
    /// in the forest ([`Self::stands_for`]).
    #[allow(clippy::too_many_arguments)]
    fn advanced_item_useful(
        &self,
        earlier: &[Chart],
        advanced: State,
        stands_for: usize,
        winner: Option<usize>,
        reach: Reach<'_>,
        memo: &mut HashMap<CompletionKey, bool>,
        reaching: &mut HashMap<NodeKey, Reaching>,
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
                        (advanced.origin, advanced.production, stands_for),
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
                (advanced.origin, advanced.production, stands_for),
                winner,
                reach,
                memo,
                reaching,
            )
    }

    /// The production of the node that a node of `production` over a child built by `child` is
    /// in the forest: the child's own when `production` passes its child through
    /// ([`Production::passes_child_through`]), so that the relations judge the node they will
    /// see at each edge. A `child` that itself passes its child through stands for a node of a
    /// production the search does not know; it is judged as itself, which has no label, and no
    /// relation rejects it.
    fn stands_for(&self, production: usize, child: usize) -> usize {
        if self.productions[production].passes_child_through() {
            child
        } else {
            production
        }
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
    /// as in [`Self::completion_useful`]. A node is `(origin, production, stands for)`: each
    /// edge is judged with the production of the node the filters will see there
    /// ([`Self::stands_for`]), so that a sum that becomes an operand through an unlabelled
    /// production (`#RuleE ::= E` in a rule grammar whose argument positions admit rewrites) is
    /// judged as the sum.
    ///
    /// The answer depends on the node, the final chart `origin` and `after`, and a later
    /// `after` only removes tokens the rests can use; it is memoized in `memo` by node as the
    /// bounds of `after` it is known for ([`Reaching`]), and searched with an explicit stack, as
    /// in [`Self::completion_useful`].
    ///
    /// Judged without the relations (`filter` ignored) every node is taken to reach the root:
    /// this question is about where a node can sit in a parse, and a recognition that must
    /// keep every item the input can continue does not ask it.
    fn node_reaches_root(
        &self,
        earlier: &[Chart],
        node: NodeKey,
        after: usize,
        reach: Reach<'_>,
        memo: &mut HashMap<NodeKey, Reaching>,
    ) -> bool {
        if reach.filter == PriorityFilter::Ignored {
            return true;
        }
        if let Some(reaches) = memo.get(&node).and_then(|known| known.known(after)) {
            return reaches;
        }
        let reaches_by_itself = |origin: usize, production: usize| {
            (origin, self.productions[production].result_id) == reach.root
                || reach.cycles.contains(production)
                || self.productive_unary_cycles.contains(&production)
        };
        // The earliest `after` each node was pushed with: a node pushed again with the same or
        // a later one can reach no more than it could then.
        let mut visited = HashMap::from([(node, after)]);
        // Each frame: the node, its `after`, the waiting items examined, and the rest
        // (production, dot) of the caller that admitted the node below it (none for the first).
        let mut stack = vec![(node, after, 0usize, None::<(usize, usize)>)];
        // Invariant: `stack` is a chain of nodes, each admitted by an item waiting for it whose
        // rest the tokens from the node's `after` on can follow and whose node is the next,
        // with that next node's `after` past the first token the rest scans; `visited` holds
        // every node pushed, with the earliest `after` it was pushed with, and the fourth
        // component counts the waiting items of each already examined.
        // The latest `after` with which the node of the top frame, by the path found, reaches
        // the root.
        let found = 'search: loop {
            let Some(((origin, production, stands_for), after, next_caller, _)) = stack.last_mut()
            else {
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
                    self.boundary_admits(caller, *stands_for, reach)
                        .after(caller_after)
                })
            else {
                continue;
            };
            let node = (
                caller.origin,
                caller.production,
                self.stands_for(caller.production, *stands_for),
            );
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
                        stack.push((node, caller_after, 0, Some(rest)));
                    }
                }
            }
        };
        match found {
            Some(mut latest) => {
                // Pass the bound down the path: each node reaches the root, by it, with any
                // `after` up to the latest at which the rest that admits it into the next node
                // can still begin.
                for (node, after, _, rest) in stack.into_iter().rev() {
                    debug_assert!(after <= latest);
                    let known = memo.entry(node).or_default();
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
    /// The answer depends only on the node `(origin, production, stands for)` (as in
    /// [`Self::node_reaches_root`]), `winner` and the final chart `origin` (and, through
    /// [`Self::node_reaches_root`], on the tokens that remain, which only shrink), so it is
    /// memoized in `memo`. The search over the chain of callers uses an explicit
    /// stack; when it finds no useful item, no item it visited reaches one, and all of them are
    /// recorded as useless.
    fn completion_useful(
        &self,
        earlier: &[Chart],
        node: NodeKey,
        winner: Option<usize>,
        reach: Reach<'_>,
        memo: &mut HashMap<CompletionKey, bool>,
        reaching: &mut HashMap<NodeKey, Reaching>,
    ) -> bool {
        // A caller completed here through a nullable rest ends here, so whether its node holds
        // a witness of a deferred scope error (`Admission::IfEndsAfter`) depends on how many
        // witnesses come before this position, which is part of the key.
        let region = reach
            .remaining
            .map_or(0, |remaining| remaining.deferrals_before(reach.from));
        if let Some(useful) = memo.get(&(node, winner, region)) {
            return *useful;
        }
        let mut visited = HashSet::from([node]);
        let mut stack = vec![(node, 0usize)];
        // Invariant: `stack` is a chain of completions, each of which some caller of the one
        // before it would complete through a nullable rest; `visited` holds every completion
        // pushed, and the third component counts the callers of each already examined.
        let found = 'search: loop {
            let Some(((origin, production, stands_for), next_caller)) = stack.last_mut() else {
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
            let admission = self.boundary_admits(caller, *stands_for, reach);
            if admission == Admission::No {
                continue;
            }
            let dot = caller.dot + 1;
            let caller_node = (
                caller.origin,
                caller.production,
                self.stands_for(caller.production, *stands_for),
            );
            if reach
                .analysis
                .rest_can_start_with(caller.production, dot, winner)
                && reach
                    .rest_follows(caller.production, dot, reach.from)
                    .and_then(|after| admission.after(after))
                    .is_some_and(|after| {
                        self.node_reaches_root(earlier, caller_node, after, reach, reaching)
                    })
            {
                break 'search true;
            }
            if !reach.analysis.rest_is_nullable(caller.production, dot)
                || admission.after(reach.from) != Some(reach.from)
            {
                continue;
            }
            match memo.get(&(caller_node, winner, region)) {
                Some(true) => break 'search true,
                Some(false) => {}
                None => {
                    if visited.insert(caller_node) {
                        stack.push((caller_node, 0));
                    }
                }
            }
        };
        if found {
            for (node, _) in stack {
                memo.insert((node, winner, region), true);
            }
        } else {
            for node in visited {
                memo.insert((node, winner, region), false);
            }
        }
        found
    }

    /// Whether `caller` can hold a node built by `child` at its dot in a reading the filters
    /// keep; `child` is the production of the node the filters see there
    /// ([`Self::stands_for`]). The associativity boundary [`Self::filter_associative_boundary`]
    /// drops the node before the caller packs it, in every grammar (judged from `child`'s own
    /// parse label; a production without one whose node stands for a node of an unknown
    /// production passes that node's label up, which is not known here, so it is kept). The priority filter judges the edge when the caller completes
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
                Some(remaining) => match remaining.first_deferral_from(caller.origin) {
                    None => Admission::No,
                    Some(_)
                        if reach.doomed == DoomedEdges::SkippedBesideOneScope
                            && remaining.deferral_count() == 1 =>
                    {
                        reach.doomed_pruned.set(true);
                        Admission::No
                    }
                    Some(witness) => Admission::IfEndsAfter(witness),
                },
            },
        }
    }

    /// Whether [`Self::filter_associative_boundary`] keeps a node built by `child` as the
    /// child of `caller` at its dot. The node is judged as that check judges it: by the parse
    /// label of the production it is a node of (`Production::term_production`), at the end
    /// [`Self::associativity_edge`] selects. A token builds a leaf, which has no label, and a
    /// production that passes its child through stands for a node this question does not know
    /// ([`Self::stands_for`]): both are kept.
    fn associativity_admits(&self, caller: State, child: usize) -> bool {
        let Some((parent, left_child)) = self.associativity_edge(caller) else {
            return true;
        };
        let descriptor = &self.productions[child];
        if descriptor.token || descriptor.passes_child_through() {
            return true;
        }
        let index = self.relation_index();
        let (Some(parent), Some(child)) = (
            index.production_labels[parent],
            index.production_labels[descriptor.term_production.unwrap_or(child)],
        ) else {
            return true;
        };
        !index.forbids(parent, child, left_child)
    }

    /// The edge at which the associativity relations judge the node `caller` holds at its dot:
    /// the production of the node `caller` builds (`Production::term_production`), and whether
    /// the child is its left (`true`) or its right child. This is the end position the relation
    /// filter judges there ([`NodeShape::judged_side`]), so the check at hand-off
    /// ([`Self::filter_associative_boundary`]) is the filter's own associativity check of that
    /// edge, made earlier, and drops only nodes the filter would drop from that tree. `None`
    /// where the filter judges no associativity: a middle position, a position `applyPriority`
    /// leaves out, below a record or a syntactic subsort, below a production that passes its
    /// child through (it builds no node, so the child is judged at its caller's edge), and
    /// below a production whose label is in no associativity relation.
    fn associativity_edge(&self, caller: State) -> Option<(usize, bool)> {
        self.relation_index().edges[caller.production]
            .get(caller.dot)
            .copied()
            .flatten()
    }

    fn relation_index(&self) -> &RelationIndex {
        self.relation_index.get_or_init(|| {
            RelationIndex::new(&self.priorities, &self.associativities, &self.productions)
        })
    }

    /// Whether the associativity relations forbid a node labelled `child` as the leftmost
    /// (`left_child`) or the rightmost child of one labelled `parent`.
    pub(super) fn associativity_forbids(
        &self,
        parent: &str,
        child: &str,
        left_child: bool,
    ) -> bool {
        let exclusions = &self.relation_index().exclusions;
        let (Some(parent), Some(child)) = (
            exclusions.associativity_id(parent),
            exclusions.associativity_id(child),
        ) else {
            return false;
        };
        exclusions.associativity_forbids(
            parent,
            child,
            if left_child { Side::Left } else { Side::Right },
        )
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

    /// Drop completed nodes that the associativity relations forbid as the caller's child at
    /// its dot, at the edge [`Self::associativity_edge`] selects: the relation filter's own
    /// associativity check of that edge, which would drop the caller's reading over such a node
    /// when the caller completes, made before the caller packs its derivations. That keeps a
    /// long associative chain from expanding into a Catalan-sized forest. A node is judged by
    /// the label of its own production, as the filter judges a child; an ambiguity is passed,
    /// because the filter judges each of its alternatives at the same edge later. Every other
    /// edge check waits for the filter's pass over the completed caller.
    fn filter_associative_boundary<'a>(
        &self,
        caller: State,
        nodes: &'a BTreeSet<Rc<PackedTerm>>,
        filter: PriorityFilter,
        first_violation: &mut Option<ParseError>,
    ) -> Cow<'a, BTreeSet<Rc<PackedTerm>>> {
        if filter == PriorityFilter::Ignored {
            return Cow::Borrowed(nodes);
        }
        let Some((parent, left_child)) = self.associativity_edge(caller) else {
            return Cow::Borrowed(nodes);
        };
        let parent = self.productions[parent]
            .parse_label
            .as_deref()
            .expect("a production in an associativity relation has a parse label");
        let side = if left_child { "left" } else { "right" };
        let label = |node: &PackedTerm| match &node.node {
            PackedNode::Production { production, .. } => {
                self.productions[*production].parse_label.as_deref()
            }
            PackedNode::Term(_)
            | PackedNode::Ambiguity(_)
            | PackedNode::InstantiatedProduction { .. } => None,
        };
        let violates = |node: &PackedTerm| {
            label(node).is_some_and(|child| self.associativity_forbids(parent, child, left_child))
        };
        // Most boundaries reject nothing; they pass the caller's set through without copying it.
        if !nodes.iter().any(|node| violates(node)) {
            return Cow::Borrowed(nodes);
        }
        Cow::Owned(
            nodes
                .iter()
                .filter(|node| {
                    let Some(child) = label(node) else {
                        return true;
                    };
                    if !self.associativity_forbids(parent, child, left_child) {
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
        let forest = self.check_packed_forest(forest, priority_memos)?;
        let forest = self.factor_pre_inference_packed_ambiguities(forest);
        let forest = self.push_top_lhs_packed_ambiguity_up(forest);
        Ok(forest)
    }

    /// The passes of `prepare_packed_forest` that can report an error, which are all that the
    /// explanation of a failed parse reads (`Grammar::explain_violation`).
    fn check_packed_forest(
        &self,
        forest: Rc<PackedTerm>,
        priority_memos: &RefCell<PackedPriorityMemos>,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        let reserved_names = packed_variable_names(&forest);
        let forest = self.collapse_packed_record_productions(forest, reserved_names)?;
        let forest = self.filter_packed_priority(forest, priority_memos)?;
        self.resolve_packed_applications(forest)
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
            work_limit: None,
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
            grammar.parse_attempt_explained(
                &Sort::new(start),
                input,
                ParseContext {
                    is_anywhere: false,
                    provenance: ParseProvenance {
                        source: SourceId(0),
                        base_offset: 0,
                    },
                    diagnostic_provenance: false,
                    diagnostic_work: DiagnosticWork::Unlimited,
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
                        expected: vec!["\"a\"".into(), "\"b\"".into(), "Choice".into()].into(),
                        input: input_kind,
                        previous: None,
                        span: None,
                        work_limit: None,
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
                    expected: vec![].into(),
                    input: NoParseInput::UnrecognizedInput { value: "?".into() },
                    previous: None,
                    span: None,
                    work_limit: None,
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
                    expected: vec!["\"z\"".into()].into(),
                    input: NoParseInput::UnrecognizedInput { value: "?".into() },
                    previous: Some("ab".into()),
                    span: None,
                    work_limit: None,
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
                Err(ParseError::Ambiguous { alternatives, .. }) if alternatives.len() == 2
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
            let result = grammar.parse_attempt_explained(
                &Sort::new("Start"),
                "p?",
                ParseContext {
                    is_anywhere: false,
                    provenance: ParseProvenance {
                        source: SourceId(0),
                        base_offset: 0,
                    },
                    diagnostic_provenance: false,
                    diagnostic_work: DiagnosticWork::Unlimited,
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
        grammar.add_left_associative("plus");
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
            let ParseError::Ambiguous { alternatives, .. } = result.unwrap_err() else {
                panic!("the two production-distinct alternatives must remain ambiguous");
            };
            assert_eq!(alternatives.len(), 2);
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
mod diagnostic_work_tests {
    use super::*;

    /// `S ::= "x" | S "+" S`, with the sum left-associative, or neither way when
    /// `non_associative`.
    fn sums(non_associative: bool) -> Grammar {
        let sort = Sort::new("S");
        let operand = || ProductionItem::NonTerminal {
            sort: sort.clone(),
            name: None,
        };
        let mut grammar = Grammar::default();
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
                    operand(),
                    ProductionItem::Terminal("+".to_owned()),
                    operand(),
                ],
                Some(Label::new("plus")),
                false,
                false,
            )
            .unwrap();
        grammar.add_left_associative("plus");
        if non_associative {
            grammar.add_right_associative("plus");
        }
        grammar
    }

    /// `operands` operands joined by `+`, then `suffix`.
    fn chain(operands: usize, suffix: &str) -> String {
        vec!["x"; operands].join("+") + suffix
    }

    /// The outcome of parsing `input` as `S` under `work`, and the chart steps it took.
    fn parse(grammar: &Grammar, input: &str, work: DiagnosticWork) -> (ParseError, usize) {
        reset_chart_work_counters();
        let error = grammar
            .parse_with_diagnostic_work(&Sort::new("S"), input, work)
            .unwrap_err();
        (error, chart_work_counters().chart_steps)
    }

    const NO_FLOOR: DiagnosticWork = DiagnosticWork::Limited { floor: 0 };

    /// A chain with a syntax error at its end is located where its longest viable prefix ends
    /// within the limit, and where the recognition under the relations stops past it: here the
    /// same place, which the error marks as not explained.
    #[test]
    fn a_syntax_error_is_located_within_the_limit_and_past_it() {
        let grammar = sums(false);
        let input = chain(60, "+");
        let (explained, _) = parse(&grammar, &input, DiagnosticWork::Unlimited);
        let ParseError::NoParse {
            position,
            input: NoParseInput::EndOfInput,
            previous,
            work_limit: None,
            ..
        } = &explained
        else {
            panic!("expected the grammar's diagnostic: {explained:?}")
        };
        assert_eq!(
            explained,
            parse(&grammar, &input, DiagnosticWork::DEFAULT).0
        );
        let (unexplained, _) = parse(&grammar, &input, NO_FLOOR);
        let ParseError::NoParse {
            position: unexplained_position,
            input: NoParseInput::EndOfInput,
            previous: unexplained_previous,
            work_limit: Some(_),
            ..
        } = &unexplained
        else {
            panic!("expected the first attempt's diagnostic: {unexplained:?}")
        };
        assert_eq!(
            (unexplained_position, unexplained_previous),
            (position, previous)
        );
        let message = unexplained.to_string();
        assert!(
            message.starts_with("Parse error: unexpected end of file following token '+'. ")
                && message.contains(DiagnosticWork::VARIABLE),
            "{message}"
        );
    }

    /// An input that the grammar derives, but whose every derivation breaks a relation, is
    /// reported by the relation within the limit; past it, by where the recognition under the
    /// relations stops, which is the operator the relation forbids there.
    #[test]
    fn a_broken_relation_is_reported_within_the_limit_and_located_past_it() {
        let grammar = sums(true);
        let (error, _) = parse(&grammar, &chain(3, ""), DiagnosticWork::DEFAULT);
        assert!(
            matches!(&error, ParseError::Associativity { .. }),
            "{error:?}"
        );
        let long = chain(20, "");
        assert!(matches!(
            parse(&grammar, &long, DiagnosticWork::Unlimited).0,
            ParseError::Associativity { .. }
        ));
        let (unexplained, _) = parse(&grammar, &long, NO_FLOOR);
        assert!(
            matches!(
                &unexplained,
                ParseError::NoParse {
                    position: 3,
                    input: NoParseInput::Token { value },
                    previous: Some(previous),
                    work_limit: Some(_),
                    ..
                } if value == "+" && previous == "x"
            ),
            "{unexplained:?}"
        );
    }

    /// The diagnostic of a failed chain takes chart steps linear in its length under a limit
    /// proportional to the first attempt's, while without one it recognizes the chain's
    /// ambiguous relation-free grammar, whose chart is cubic in its length.
    #[test]
    fn a_failed_chain_is_diagnosed_in_work_linear_in_its_length() {
        let grammar = sums(false);
        let steps = |operands: usize, work: DiagnosticWork| {
            let (error, steps) = parse(&grammar, &chain(operands, "+"), work);
            assert!(matches!(error, ParseError::NoParse { .. }), "{error:?}");
            steps
        };
        let unlimited = [40, 80].map(|operands| steps(operands, DiagnosticWork::Unlimited));
        let limited = [200, 400, 800].map(|operands| steps(operands, NO_FLOOR));
        eprintln!("unlimited at 40 and 80 operands: {unlimited:?}");
        eprintln!("limited at 200, 400 and 800 operands: {limited:?}");
        assert!(unlimited[1] > 4 * unlimited[0], "{unlimited:?}");
        for pair in limited.windows(2) {
            assert!(pair[1] <= 3 * pair[0], "{limited:?}");
        }
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
