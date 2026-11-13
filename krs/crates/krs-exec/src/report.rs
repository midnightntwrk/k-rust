//! The `krs-exec` report shapes shared by `--output json` and the browser JSON ABI.
//!
//! A run document is `krs-exec/7` ([`RUN_REPORT_SCHEMA`]), whose stop rule and coverage rows name
//! their item with its package, which may end `stop-undecided` and count its arrivals beside its
//! stop events, which lists the stop rules it went on past, and which summarizes the run's
//! declared observations; a search document is `krs-exec/1` ([`SEARCH_REPORT_SCHEMA`]); a proof
//! document is `krs-exec/2` ([`PROVE_REPORT_SCHEMA`]), whose verdicts include `crashed` and
//! `timeout` and which names the solver its claims were proved with ([`SolverReport`]).
//!
//! The crate documentation, "Report versions", states how the versions are numbered.

use std::collections::HashMap;
use std::sync::{Arc, OnceLock};

use k_rust::{
    backend::{ChosenValueOutput, HaltReasonOutput, HeldState},
    kast::{Term as KastTerm, convert::Converter, json as kast_json, printer::Printer},
    kore::{
        ast::Pattern,
        node::{PatternNode, PatternSource, materialize},
        walk,
    },
    names::WellKnownSymbol,
};
use serde::{Deserialize, Serialize, Serializer};

use crate::ExecError;

/// The schema name a serialized run envelope carries (`krs run`; [report
/// versions](crate#report-versions)).
///
/// A run document's stop rule and each row of its coverage name their item with the package that
/// declares it, as a stop names an item ([`NamedRule::item`], [`CoveredRule::item`]:
/// `crate::boundary`, `lang::step`), and the difference of its expectation names its own format
/// (`format`, [`crate::DIFFERENCE_FORMAT`]). A `krs-exec/1` run document named both items by
/// their Rust path below their crate root (`boundary`), and a `krs-exec/3` one named the stop
/// rule's item with its package and a coverage row's still below its crate root. A reader of
/// either would read `crate::boundary` in a coverage row as a path through a module `crate`, and
/// could not tell a dependency's `step` from the main package's, so a run document is a format
/// of its own version.
///
/// A run under a stop condition ([`crate::StopWhen`]) may end `stop-undecided`
/// ([`Halt::StopUndecided`]), a halt a `krs-exec/4` reader does not know, where it says where
/// and why (`undecided`, [`RunReport::undecided`]), and reports every
/// arrival it passed (`arrivals`) beside the stop events it counted (`stops`), which a
/// `krs-exec/4` reader would read as all its arrivals: a run document with a condition is a
/// format of its own version, `krs-exec/5`.
///
/// A run with stop rules reports `stops` whenever it has them, 0 included, where a `krs-exec/5`
/// run document omitted it at 0, and lists the stop rules it went on past at a state with another
/// successor (`passed_stops`, [`RunReport::passed_stops`]); its `undecided` says whether a larger
/// budget can decide it (`budget_spent`). A `krs-exec/5` reader would read a run with no `stops`
/// and no `passed_stops` as one that passed none, so a run document was `krs-exec/6`.
///
/// A run with declared observations ([`crate::RunOptions::observe`]) reports a summary of them
/// (`observations`, [`RunReport::observations`]): each channel's elements, how the path's end
/// closed it, or where it stopped being known. Such a run's answer is its observations beside its
/// end, and a `krs-exec/6` reader would take the end alone for the answer, so a run document is
/// `krs-exec/7`.
pub const RUN_REPORT_SCHEMA: &str = "krs-exec/7";

/// The schema name a serialized run envelope carries for a definition that declares ends
/// ([`crate::Semantics::declares_ends`], [`run_report_schema`]).
///
/// A run of such a definition that ends where no rule applies reports the declared class of its
/// end (`end`, [`RunReport::end`]), and a state outside every declared end is a gap, which is no
/// completed result of the definition.
/// A `krs-exec/7` reader knows `halt: "stuck"` as a completed run and would take a gap for one,
/// and it does not know the halt `end-undecided` ([`Halt::EndUndecided`]), so every run document
/// of a declaring definition is a format of its own version.
/// A definition that declares no end keeps [`RUN_REPORT_SCHEMA`], and its documents their bytes.
pub const RUN_REPORT_SCHEMA_DECLARED_ENDS: &str = "krs-exec/8";

/// The schema name of a run document of a definition that declares ends (`declares_ends`) or
/// none: [`RUN_REPORT_SCHEMA_DECLARED_ENDS`] or [`RUN_REPORT_SCHEMA`].
#[must_use]
pub const fn run_report_schema(declares_ends: bool) -> &'static str {
    if declares_ends {
        RUN_REPORT_SCHEMA_DECLARED_ENDS
    } else {
        RUN_REPORT_SCHEMA
    }
}

/// The schema name a serialized search envelope carries (`krs search`; [report
/// versions](crate#report-versions)).
///
/// A search document names no rule's item. The difference of its expectation names its own
/// format (`format`, [`crate::DIFFERENCE_FORMAT`]) and is read by it, so a reader that knows only
/// an earlier difference format refuses the difference rather than misreading it; the search
/// document keeps `krs-exec/1`.
pub const SEARCH_REPORT_SCHEMA: &str = "krs-exec/1";

/// The schema name a serialized proof envelope carries: a reader of `krs-exec/1` proof documents
/// knows no `crashed` or `timeout` verdict and no `crash` record, so a proof document is a format
/// of its own version, while run and search documents, which that change left alone, kept
/// theirs.
pub const PROVE_REPORT_SCHEMA: &str = "krs-exec/2";

/// One configuration or term: its KORE pattern, and its user-facing KAST.
///
/// The KAST is a second term of the pattern's size, converted through a normalized copy of the
/// pattern, a third. A term built with its KAST holds it; a run's end built without it
/// ([`crate::EndKast::WhenRead`]) converts it when it is first read ([`Self::kast`]), so a
/// report nothing reads as KAST holds the pattern alone.
///
/// A run's end built without its pattern ([`crate::EndPattern::WhenRead`]) holds the state as
/// the backend has it, and builds the pattern when it is first read ([`Self::kore`]): the same
/// pattern, a tree of the end's size beside the backend's term. What a run and its status line
/// ask of an end (whether it holds a term with no value or a Float, its stdout buffer, the head
/// of its main cell) is asked of the held state, which answers as the pattern would without
/// building it.
///
/// It serializes as the KAST JSON envelope that `krun --output json` prints,
/// so a gate normalizes the native and Java results with one policy.
#[derive(Clone, Debug)]
pub struct Term {
    kore: Kore,
    kast: Kast,
}

/// A term's KORE pattern.
#[derive(Clone, Debug)]
enum Kore {
    /// Built when the term was.
    Built(Pattern),
    /// Built from the backend's state when it is first read.
    WhenRead {
        held: HeldState,
        built: OnceLock<Pattern>,
        /// The first cell of the pattern with a label asked for ([`Term::computation_head_kore`]),
        /// built alone: the label, and the cell where the pattern has one.
        cell: OnceLock<(String, Option<Pattern>)>,
    },
}

/// A term's KAST.
#[derive(Clone, Debug)]
enum Kast {
    /// Converted when the term was built.
    Held(KastTerm),
    /// Converted when it is first read, with the definition's sort hooks.
    WhenRead {
        hooks: Arc<HashMap<String, String>>,
        converted: OnceLock<KastTerm>,
    },
}

impl Term {
    pub(crate) const fn new(kore: Pattern, kast: KastTerm) -> Self {
        Self {
            kore: Kore::Built(kore),
            kast: Kast::Held(kast),
        }
    }

    /// `kore` as a term whose KAST is converted with `hooks` when it is first read.
    pub(crate) const fn unconverted(kore: Pattern, hooks: Arc<HashMap<String, String>>) -> Self {
        Self {
            kore: Kore::Built(kore),
            kast: Kast::WhenRead {
                hooks,
                converted: OnceLock::new(),
            },
        }
    }

    /// `held` as a term whose pattern is built when it is first read, and whose KAST is
    /// converted from it with `hooks` when that is first read.
    pub(crate) const fn unbuilt(held: HeldState, hooks: Arc<HashMap<String, String>>) -> Self {
        Self {
            kore: Kore::WhenRead {
                held,
                built: OnceLock::new(),
                cell: OnceLock::new(),
            },
            kast: Kast::WhenRead {
                hooks,
                converted: OnceLock::new(),
            },
        }
    }

    /// The KORE pattern, as the backend returned it, built now if the term was built without
    /// it; a run or search result has its Floats in the form `krun` prints them.
    #[must_use]
    pub fn kore(&self) -> &Pattern {
        match &self.kore {
            Kore::Built(kore) => kore,
            Kore::WhenRead { held, built, .. } => built.get_or_init(|| held.kore()),
        }
    }

    /// Whether the term holds its KORE pattern: it was built with it, or it has been read
    /// ([`Self::kore`]).
    #[must_use]
    pub fn holds_kore(&self) -> bool {
        match &self.kore {
            Kore::Built(_) => true,
            Kore::WhenRead { built, .. } => built.get().is_some(),
        }
    }

    /// The backend's state the pattern is built from, where the term does not hold its pattern.
    pub(crate) fn held(&self) -> Option<&HeldState> {
        match &self.kore {
            Kore::WhenRead { held, built, .. } if built.get().is_none() => Some(held),
            Kore::Built(_) | Kore::WhenRead { .. } => None,
        }
    }

    /// The KAST term converted from the KORE pattern, converted now if the term was built
    /// without it.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Result`] when the pattern has no KAST form, which a term built with
    /// its KAST never does.
    pub fn kast(&self) -> Result<&KastTerm, ExecError> {
        match &self.kast {
            Kast::Held(kast) => Ok(kast),
            Kast::WhenRead { hooks, converted } => {
                if let Some(kast) = converted.get() {
                    return Ok(kast);
                }
                let kast = convert(self.kore(), hooks)?;
                Ok(converted.get_or_init(|| kast))
            }
        }
    }

    /// Whether the term holds its KAST: it was built with it, or it has been read
    /// ([`Self::kast`]).
    #[must_use]
    pub fn holds_kast(&self) -> bool {
        match &self.kast {
            Kast::Held(_) => true,
            Kast::WhenRead { converted, .. } => converted.get().is_some(),
        }
    }

    /// The KORE pattern, given up.
    pub(crate) fn into_kore(self) -> Pattern {
        match self.kore {
            Kore::Built(kore) => kore,
            Kore::WhenRead { held, built, .. } => built.into_inner().unwrap_or_else(|| held.kore()),
        }
    }

    /// The first item of the computation cell `<cell>` (the definition's main cell,
    /// [`crate::Semantics::main_cell`]) as textual KAST: `Some(None)` when the cell is empty,
    /// `None` without such a cell.
    ///
    /// # Errors
    ///
    /// As [`Self::kast`], which this reads.
    pub fn computation_head(&self, cell: &str) -> Result<Option<Option<String>>, ExecError> {
        let label_name = format!("<{cell}>");
        let mut stack = vec![self.kast()?];
        while let Some(term) = stack.pop() {
            match term {
                KastTerm::Apply { label, arguments } if label.name == label_name => {
                    let [content] = arguments.as_slice() else {
                        return Ok(None);
                    };
                    return Ok(Some(match content {
                        KastTerm::Sequence(items) => {
                            items.first().map(|item| Printer::new().print_term(item))
                        }
                        item => Some(Printer::new().print_term(item)),
                    }));
                }
                KastTerm::Apply { arguments, .. } => stack.extend(arguments.iter().rev()),
                KastTerm::Annotated { term, .. } => stack.push(term),
                _ => {}
            }
        }
        Ok(None)
    }

    /// The first item of the computation cell `<cell>` as a KORE pattern, the subterm
    /// [`Term::computation_head`] prints: `Some(None)` when the cell is empty, `None` without
    /// such a cell.
    ///
    /// Nested `kseq` and `append` applications are one flat sequence, as in KAST, so the first
    /// item is the leftmost pattern that is neither of them nor `dotk`.
    ///
    /// A term that does not hold its pattern builds the cell alone: the first application of
    /// the cell's symbol in the pattern's pre-order is found by reading the backend's state,
    /// and the pattern built from that node is the subpattern the search of the whole finds.
    #[must_use]
    pub fn computation_head_kore(&self, cell: &str) -> Option<Option<&Pattern>> {
        let label_name = format!("<{cell}>");
        let whole = match (&self.kore, self.held()) {
            (Kore::WhenRead { cell: found, .. }, Some(held)) => {
                let (label, found) =
                    found.get_or_init(|| (label_name.clone(), first_cell(held, &label_name)));
                if *label == label_name {
                    // The search below finds the cell at the root of what it is given.
                    found.as_ref()?
                } else {
                    self.kore()
                }
            }
            _ => self.kore(),
        };
        let mut stack = vec![whole];
        while let Some(pattern) = stack.pop() {
            if let Pattern::Application { symbol, arguments }
            | Pattern::AssociativeApplication {
                symbol, arguments, ..
            } = pattern
                && krs_unparse::label_name(&symbol.name) == label_name
            {
                let [content] = arguments.as_slice() else {
                    return None;
                };
                return Some(first_item(content));
            }
            stack.extend(walk::children(pattern).into_iter().rev());
        }
        None
    }

    /// Every leaf cell of the configuration, a cell no cell is inside, in the order the term
    /// holds them: its KORE symbol (`Lbl'-LT-'env'-GT-'`) and its content.
    #[must_use]
    pub fn leaf_cells(&self) -> Vec<(&str, &Pattern)> {
        let mut cells = Vec::new();
        leaf_cells(self.kore(), &mut cells);
        cells
    }

    /// The KAST JSON envelope text.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Result`] when the term has no KAST form ([`Self::kast`]) or cannot
    /// be encoded.
    pub fn kast_json(&self) -> Result<String, ExecError> {
        kast_json::to_string(self.kast()?).map_err(|error| ExecError::Result(error.to_string()))
    }
}

/// The first application, in the pre-order of the pattern of `held`, of a symbol whose label is
/// `label_name`, built as a pattern; `None` where the pattern has none.
fn first_cell(held: &HeldState, label_name: &str) -> Option<Pattern> {
    let mut pending = vec![held.source()];
    while let Some(source) = pending.pop() {
        let node = source.node();
        if let PatternNode::Application { symbol, .. } = &node
            && krs_unparse::label_name(&symbol.name) == label_name
        {
            return Some(materialize(source));
        }
        let (_, children) = node.split();
        pending.extend(children.into_iter().rev());
    }
    None
}

/// The KAST of `kore`, a pattern of a definition whose sort hooks are `sort_hooks`: a domain
/// value is a token whose text depends on its sort's hook.
pub(crate) fn convert(
    kore: &Pattern,
    sort_hooks: &HashMap<String, String>,
) -> Result<KastTerm, ExecError> {
    Converter::new(sort_hooks)
        .convert(kore)
        .map_err(|error| ExecError::Result(error.to_string()))
}

/// The cell `pattern` is, if it is one: its symbol and content.
fn cell(pattern: &Pattern) -> Option<(&str, &Pattern)> {
    let (Pattern::Application { symbol, arguments }
    | Pattern::AssociativeApplication {
        symbol, arguments, ..
    }) = pattern
    else {
        return None;
    };
    let label = krs_unparse::label_name(&symbol.name);
    match arguments.as_slice() {
        [content] if label.starts_with('<') && label.ends_with('>') => {
            Some((symbol.name.as_str(), content))
        }
        _ => None,
    }
}

/// Whether a cell is inside `pattern`, or `pattern` is one.
fn holds_cell(pattern: &Pattern) -> bool {
    cell(pattern).is_some() || walk::children(pattern).into_iter().any(holds_cell)
}

fn leaf_cells<'t>(pattern: &'t Pattern, cells: &mut Vec<(&'t str, &'t Pattern)>) {
    if let Some((symbol, content)) = cell(pattern)
        && !holds_cell(content)
    {
        cells.push((symbol, content));
        return;
    }
    for child in walk::children(pattern) {
        leaf_cells(child, cells);
    }
}

/// The first item of a K sequence, `None` when it is empty.
pub(crate) fn first_item(sequence: &Pattern) -> Option<&Pattern> {
    match sequence {
        Pattern::Application { symbol, arguments }
        | Pattern::AssociativeApplication {
            symbol, arguments, ..
        } if symbol.name == WellKnownSymbol::KSeq.as_str()
            || symbol.name == WellKnownSymbol::Append.as_str() =>
        {
            arguments.iter().find_map(first_item)
        }
        Pattern::Application { symbol, .. } if symbol.name == WellKnownSymbol::DotK.as_str() => {
            None
        }
        item => Some(item),
    }
}

impl Serialize for Term {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let text = self.kast_json().map_err(serde::ser::Error::custom)?;
        let mut decoder = serde_json::Deserializer::from_str(&text);
        decoder.disable_recursion_limit();
        let value = <serde_json::Value as serde::Deserialize>::deserialize(&mut decoder)
            .map_err(serde::ser::Error::custom)?;
        value.serialize(serializer)
    }
}

/// How a run or one search path ended.
///
/// `stuck`, `depth-bound` and `undefined` are completed results: K has no
/// distinguished finished state, so a program is finished when `<k>` holds only `.K`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Halt {
    /// No rule applies.
    Stuck,
    /// The `--depth` bound was reached.
    DepthBound,
    /// The state is `#Bottom`: a partial function was applied outside its domain.
    Undefined,
    /// Rule applicability could not be decided (no SMT solver, or an undecided condition).
    Indeterminate,
    /// A hooked function has no implementation in the native backend.
    UnsupportedHook,
    /// Simplification failed.
    SimplificationError,
    /// A step exceeded its time budget.
    Timeout,
    /// The run ended at one of its stop rules ([`crate::StopRules`], [`RunReport::stop`]).
    Stopped,
    /// The backend stopped for a reason a run does not request (branch, breadth or work bound,
    /// cancellation, a probe's answer: no run asks a probe).
    Interrupted,
    /// The run's stop condition was left undecided at an arrival ([`crate::StopWhen`]): its
    /// evaluation spent its budget, met another stop, or ended short of a value after the
    /// solver answered `Unknown`, so whether the run ends there is not known.
    StopUndecided,
    /// No rule applies, and whether a declared end holds at the state was left undecided
    /// ([`crate::declared_ends`], [`RunReport::end_undecided`]): the evaluation of an end's
    /// function spent its budget, met another stop, or ended short of a value, so the class of
    /// the end is not known. Only a run of a definition that declares ends halts so.
    EndUndecided,
}

impl Halt {
    pub(crate) const fn from_backend(reason: HaltReasonOutput) -> Self {
        match reason {
            HaltReasonOutput::Stuck => Self::Stuck,
            HaltReasonOutput::DepthBound => Self::DepthBound,
            HaltReasonOutput::Trivial | HaltReasonOutput::Vacuous => Self::Undefined,
            HaltReasonOutput::Indeterminate => Self::Indeterminate,
            HaltReasonOutput::UnsupportedHook => Self::UnsupportedHook,
            HaltReasonOutput::SimplificationError => Self::SimplificationError,
            HaltReasonOutput::Timeout => Self::Timeout,
            HaltReasonOutput::CutPoint | HaltReasonOutput::Terminal => Self::Stopped,
            HaltReasonOutput::StopUndecided => Self::StopUndecided,
            HaltReasonOutput::Cancelled
            | HaltReasonOutput::Branch
            | HaltReasonOutput::BreadthBound
            | HaltReasonOutput::WorkBound
            | HaltReasonOutput::PollBound
            | HaltReasonOutput::ProbeDifference
            | HaltReasonOutput::ProbeDone => Self::Interrupted,
        }
    }

    /// The printed status word.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Stuck => "stuck",
            Self::DepthBound => "depth-bound",
            Self::Undefined => "undefined",
            Self::Indeterminate => "indeterminate",
            Self::UnsupportedHook => "unsupported-hook",
            Self::SimplificationError => "simplification-error",
            Self::Timeout => "timeout",
            Self::Stopped => "stopped",
            Self::Interrupted => "interrupted",
            Self::StopUndecided => "stop-undecided",
            Self::EndUndecided => "end-undecided",
        }
    }

    /// Whether the result is complete (exit status 0) rather than inconclusive (exit status 3):
    /// a stop rule, as the depth bound, ends a run where it was asked to.
    #[must_use]
    pub const fn is_complete(self) -> bool {
        matches!(
            self,
            Self::Stuck | Self::DepthBound | Self::Undefined | Self::Stopped
        )
    }
}

/// Where a rewrite step's rule came from.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum StepOrigin {
    /// An authored KRS sentence.
    Authored {
        /// Package-relative source path.
        file: String,
        /// One-based line, when the source text was supplied.
        #[serde(skip_serializing_if = "Option::is_none")]
        line: Option<u32>,
        /// One-based Unicode-scalar column, when the source text was supplied.
        #[serde(skip_serializing_if = "Option::is_none")]
        column: Option<u32>,
    },
    /// A rule generated by a compiler pass, with the authored sentence it came from when known.
    Generated {
        /// The generating pass (for example `strict`).
        pass: String,
        /// The authored sentence the pass started from.
        #[serde(skip_serializing_if = "Option::is_none")]
        from: Option<SourceSpan>,
    },
    /// A rule of K's builtin closure.
    Builtin {
        /// The K module that declares it.
        module: String,
    },
}

/// An authored location.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SourceSpan {
    /// Package-relative source path.
    pub file: String,
    /// One-based line, when the source text was supplied.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line: Option<u32>,
    /// One-based Unicode-scalar column, when the source text was supplied.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub column: Option<u32>,
}

impl std::fmt::Display for SourceSpan {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.file)?;
        if let (Some(line), Some(column)) = (self.line, self.column) {
            write!(formatter, ":{line}:{column}")?;
        }
        Ok(())
    }
}

/// One rewrite step of a trace. Equation evaluation is not a step.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Step {
    /// One-based step number.
    pub index: u64,
    /// K's rule label (for example `KRS-TOUR-MINIMAL.foo-to-bar`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
    /// The backend's `UNIQUE_ID` of the rule.
    pub rule_id: String,
    /// Where the rule came from.
    pub origin: StepOrigin,
}

/// What kind of sentence a rule identity is, as the backend loaded it.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum RuleKind {
    /// A rewrite rule: it takes a step.
    Rule,
    /// A function equation: it evaluates an application, which is not a step.
    Equation,
    /// A simplification.
    Simplification,
    /// A definedness (`#Ceil`) equation.
    Definedness,
}

impl RuleKind {
    /// The printed word.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Rule => "rule",
            Self::Equation => "equation",
            Self::Simplification => "simplification",
            Self::Definedness => "definedness",
        }
    }
}

/// One rule or equation a run's coverage names, with the predicates that hold of it.
///
/// The predicates are k-rust's (its `docs/compatibility.md`, "Run coverage"), each of which
/// implies the one before it: `matched`, `applied`, `committed`.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct CoveredRule {
    /// The backend's `UNIQUE_ID`.
    pub rule_id: String,
    /// K's label, as the definition carries it (`SM83.boundary-fetch`, or KRS's default `nat--plus_zero`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
    /// The KRS item that wrote the sentence, with the package that declares it, spelled as a stop
    /// spells an item ([`crate::StopRules`], [`crate::item_spelling`]): its Rust path with
    /// `crate::` for an item of the definition's main package (`crate::interrupt::boundary_fetch`),
    /// with its crate's name for a dependency's (`lang::step`). Absent for a sentence of K's
    /// builtin closure, or one a compiler pass generated from no authored item.
    ///
    /// The path is the item's in the source `krs expand` prints, which is the authored source
    /// except where the expansion writes items of its own for one authored item: a function's
    /// equation is the item the expansion names after the function and its branch
    /// (`crate::expected` for the one equation of `fn Expected`, `crate::clamp_2` for the second
    /// branch of `fn Clamp`), and a stop reads that name, not the function's.
    ///
    /// The name is the item's: every sentence an item lowers to (a context's heat and cool rules)
    /// has it, and `label` tells the sentences apart. A stop reads it as
    /// this item alone except where two packages of one crate name each have an item at the path,
    /// or the main package has an item at the whole of a dependency item's spelling; there the
    /// sentence's `label` names it ([`crate::Semantics::keeps_label`]). A stop refuses the name of
    /// an item that wrote no rewrite rule, naming the kinds of its sentences.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub item: Option<String>,
    /// What kind of sentence it is; absent for an identity the backend's catalog lacks.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub kind: Option<RuleKind>,
    /// Where it came from.
    pub origin: StepOrigin,
    /// The run began to decide its condition for an instance its left-hand side matched,
    /// whatever the verdict, or applied it. `false` only for a rule the run offered alone
    /// ([`Coverage::offered`]).
    pub matched: bool,
    /// The run applied it: a step by the rule built a successor or found the step undefined, or
    /// an instance of the equation gave a result.
    pub applied: bool,
    /// How many times the run applied it (0 when it did not); an evaluation served from a memo
    /// of the run counts once.
    pub applications: u64,
    /// A path took a step by the rule: its successor was committed, its own normalization having
    /// shown it defined. Only a rewrite rule is committed.
    pub committed: bool,
}

/// The rules and equations one run used: k-rust's run coverage, by identity.
///
/// It covers every state the run explored, the steps it tried and did not take included, and
/// every equation it applied to evaluate, wherever (a state, a condition, a right-hand side);
/// a run a bound or a stop cut short reports what it covered before it ended. It never names a
/// builtin hook, which is no sentence.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Coverage {
    /// Whether rules the run only offered are listed: a rule or equation whose left-hand side
    /// matched a subject the run selected it as a candidate for, tried there or not
    /// ([`crate::CoverageOptions::offered`]). Without it every rule listed is `matched`.
    pub offered: bool,
    /// Every rule and equation the run matched (and, with `offered`, offered), in `rule_id`
    /// order.
    pub rules: Vec<CoveredRule>,
}

/// Where a stop rule ended a run ([`crate::StopRules`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum StopAt {
    /// Before the rule's step: the run's state is the one the rule would rewrite.
    Before,
    /// After the rule's step: the run's state is the rule's successor.
    After,
}

/// The arrival a run's stop condition was left undecided at, which ended the run
/// ([`RunReport::undecided`], [`Halt::StopUndecided`]).
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Undecided {
    /// Whether the stop state is the state before the rule's step or its successor.
    pub at: StopAt,
    /// The stop rule.
    pub rule: NamedRule,
    /// Why whether the condition holds there is not known: its evaluation spent its budget of
    /// polls or met another stop, or ended short of a value after the solver answered
    /// `Unknown`. A larger budget can decide the first, never the others.
    pub reason: String,
    /// Whether its evaluation spent its budget of polls, which a larger budget can decide; false
    /// for another stop and for an `Unknown` answer of the solver, which it cannot.
    pub budget_spent: bool,
}

/// A stop rule the run went on past: at a state whose successors were more than the stop
/// rule's one step, so the step was no arrival ([`RunReport::passed_stops`]).
#[derive(Clone, Debug, Serialize)]
pub struct PassedStop {
    /// The stop rule.
    pub rule: NamedRule,
    /// The steps from the run's start to the first state at which the run went on past it.
    pub depth: u64,
}

/// A rule, by its identities and origin.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct NamedRule {
    /// The backend's `UNIQUE_ID`.
    pub rule_id: String,
    /// K's label, as the definition carries it.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
    /// The KRS item that wrote the rule, with the package that declares it, spelled as a stop
    /// spells an item ([`crate::StopRules`]): its Rust path with `crate::` for an item of the
    /// definition's main package (`crate::interrupt::boundary_fetch`), with its crate's name for
    /// a dependency's (`lang::step`).
    ///
    /// A stop reads the spelling as this item alone except in two cases, where it selects
    /// another item's rules too and is refused as ambiguous: two packages of one crate name each
    /// have an item at the path, or the main package has an item at the whole of a dependency
    /// item's spelling (`crate::lang::step` beside the dependency `lang`'s `step`). There the
    /// rule's `label` names it to a stop; a stopped end's class always holds a name a stop
    /// accepts ([`crate::EndClass::rule`]).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub item: Option<String>,
    /// Where it came from.
    pub origin: StepOrigin,
}

/// The stop rule that ended a run ([`RunReport::stop`]).
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Stop {
    /// Whether the run ended before or after the rule's step.
    pub at: StopAt,
    /// The rule: named always before its step; after it, when the run's stop rules select one
    /// rule identity or the run kept its trace ([`crate::StopRules::after`]). k-rust names a
    /// terminal rule only in the leaf's `detail` text, which is no stable encoding and which
    /// krs-exec does not read.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rule: Option<NamedRule>,
    /// Which arrival at a stop it is, counted along the run from 1
    /// ([`crate::StopCriterion::Rules`]); omitted when 1.
    #[serde(skip_serializing_if = "is_one")]
    pub nth: u64,
}

#[expect(
    clippy::trivially_copy_pass_by_ref,
    reason = "serde's skip_serializing_if passes the field by reference"
)]
const fn is_one(value: &u64) -> bool {
    *value == 1
}

/// The result of `run`: one path, as krun follows it.
#[derive(Clone, Debug, Serialize)]
pub struct RunReport {
    /// How the run ended.
    pub halt: Halt,
    /// Rewrite steps taken.
    pub steps: u64,
    /// The final configuration, with each binary32 and binary64 Float as `krun` prints it.
    pub state: Term,
    /// Rewrite steps, when a trace was requested.
    pub trace: Vec<Step>,
    /// The bytes the `stream = "stdout"` cell holds when the run ends; `None` without one.
    pub stdout: Option<Vec<u8>>,
    /// The exit cell's final value after a complete run; `None` without an exit cell.
    pub exit_code: Option<i64>,
    /// The lines `io::log` (K's `IO.logString`) wrote on this path, in order; krun prints each
    /// to standard error.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub log: Vec<String>,
    /// Every value the definition leaves open that the run read, as k-rust marks it
    /// (`ExecutionResult::implementation_chosen_values`, k-rust's `docs/compatibility.md`,
    /// "Implementation-chosen hook values"), distinct and in the order the run first read it;
    /// omitted when empty.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub implementation_chosen_values: Vec<ChosenValueOutput>,
    /// The terms with no value a rule's condition read, which the backend could not evaluate:
    /// those the state holds, which make an `undefined` run's state have none, or else those the
    /// condition built, where the rule did not apply; omitted when empty.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub valueless: Vec<Term>,
    /// The run's coverage, when [`crate::RunOptions::coverage`] asked for it; omitted otherwise.
    /// A run that ends before a step with no value is followed again to its last state with a
    /// value, and its coverage is the first run's, the step that found no value included.
    /// The step by a rule a run stopped before is the resumed run's: that run's coverage commits
    /// the rule and counts the application, and the stopped run's does not
    /// ([`crate::StopRules::before`]).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub coverage: Option<Coverage>,
    /// The stop rule that ended the run, when one did ([`Halt::Stopped`]); omitted otherwise.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stop: Option<Stop>,
    /// How many arrivals at a stop the run counted, the one that ended it included
    /// ([`crate::StopCriterion::Rules`]): the count it was asked for when it ended at a stop,
    /// fewer when it ended on its own first. Under a stop condition ([`crate::StopWhen`]) it
    /// counts the stop events, the arrivals where the condition held. Reported whenever the run
    /// has stop rules, 0 included, and omitted without them.
    #[serde(skip)]
    pub stops: u64,
    /// [`Self::stops`] as the report serializes it: `Some` exactly when the run has stop rules.
    #[serde(rename = "stops", skip_serializing_if = "Option::is_none")]
    pub(crate) stops_reported: Option<u64>,
    /// Under a stop condition, every arrival at a stop the run passed, whatever the condition
    /// answered there, the one that ended it included; `None` (omitted) without a condition,
    /// where every arrival is an event and [`Self::stops`] counts them.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub arrivals: Option<u64>,
    /// Where and why the stop condition was left undecided, when it was
    /// ([`Halt::StopUndecided`]); omitted otherwise.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub undecided: Option<Undecided>,
    /// Each stop rule the run went on past at a state with another successor beside the rule's
    /// step, with the first such state's depth, in order of depth: such a step is no arrival, so
    /// it stops nothing and the condition is not asked there, and the run took one of the
    /// successors. Omitted when empty, and always without stop rules.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub passed_stops: Vec<PassedStop>,
    /// The run's observations, when it declared some ([`crate::RunOptions::observe`]): every
    /// channel's elements along the path, each rule named as a stop names it. The report
    /// serializes a summary (each channel's name, kind, number of elements, `closed` and
    /// `open`); [`crate::Observations::document`] writes the elements. Omitted without a
    /// declaration.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub observations: Option<crate::Observations>,
    /// The declared class of the run's end ([`crate::declared_ends`]): `Some` exactly when the
    /// definition declares ends and the run ended where no rule applies ([`Halt::Stuck`]).
    /// A run a step bound or a stop ended has none, since its last state is not known to be one
    /// no rule applies to; omitted then, and always for a definition that declares no end.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub end: Option<crate::RunEnd>,
    /// Which declared end was left undecided, and why, when one was ([`Halt::EndUndecided`]);
    /// omitted otherwise.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub end_undecided: Option<crate::EndUndecided>,
    /// The state a later run goes on from, when it is not `state`'s own pattern
    /// ([`Self::resume`]).
    #[serde(skip)]
    pub(crate) resume: Option<crate::State>,
}

impl RunReport {
    /// [`Self::stops`] where the run has stop rules, as the report serializes it; `None`
    /// without them.
    #[must_use]
    pub const fn reported_stops(&self) -> Option<u64> {
        self.stops_reported
    }

    /// The state a later run goes on from ([`crate::Semantics::run`]): where this run ended, as
    /// the backend reached it (with its Floats as k-rust writes them, not as `state` prints
    /// them). The later run's depth bound and step count start there.
    ///
    /// After a stop before a rule, the later run's first step is that rule's, which this run did
    /// not take: the later run counts it in its `steps`, trace, depth bound and coverage, and goes
    /// on from the rule's successor, so it does not stop at the same step again
    /// ([`crate::StopRules::before`]).
    #[must_use]
    pub fn resume(&self) -> crate::State {
        self.resume
            .clone()
            .unwrap_or_else(|| crate::State::new(self.state.kore().clone()))
    }
}

/// One final state of a search.
#[derive(Clone, Debug, Serialize)]
pub struct Solution {
    /// The state, with each binary32 and binary64 Float as `krun` prints it.
    pub state: Term,
    /// Rewrite steps from the initial state.
    pub depth: u64,
    /// Rewrite steps, when a trace was requested.
    pub trace: Vec<Step>,
}

/// The result of `search`: the set of reachable states that match the mode.
#[derive(Clone, Debug, Serialize)]
pub struct SearchReport {
    /// Whether every path was explored within the bounds and no solution was dropped.
    pub complete: bool,
    /// The solutions, in backend order.
    pub solutions: Vec<Solution>,
    /// The lines `io::log` (K's `IO.logString`) wrote while the search explored, in order;
    /// `krun --search` prints each to standard error.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub log: Vec<String>,
    /// Every value the definition leaves open that the search read, as k-rust marks it
    /// (`SearchResponse::implementation_chosen_values`), distinct and in first-read order;
    /// omitted when empty.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub implementation_chosen_values: Vec<ChosenValueOutput>,
}

/// K's reachability modality.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Modality {
    /// `all-path`.
    AllPath,
    /// `one-path`.
    OnePath,
}

/// The verdict of one claim, in k-rust's words.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Verdict {
    /// The weak reachability claim is proven; this does not certify termination.
    Proven,
    /// A path reaches a state that refutes the claim.
    Disproved,
    /// The proof failed without a counterexample.
    Failed,
    /// The backend could not decide (no SMT solver, an undecided condition, or an internal
    /// error of the solver on a condition, which a leaf's `detail` names as a defect of the
    /// solver; a Z3 that ends the process on the error gives [`Self::Crashed`] instead).
    Indeterminate,
    /// The `--depth` bound stopped the proof.
    DepthBound,
    /// The breadth bound stopped the proof.
    BreadthBound,
    /// The claim is `trusted` (KF-042): assumed without proof, never proven.
    Trusted,
    /// The process proving the claim ended abnormally (a signal, or an exit status krs never
    /// returns) before the claim's proof finished; [`ProofReport::crash`] says how.
    /// Nothing is known about the claim.
    Crashed,
    /// The claim's proof did not end within the wall-clock time it was given (`krs prove
    /// --claim-timeout`) and was cancelled, and no part of it proven before refutes the claim.
    /// It depends on the host's speed and load, unlike every other verdict under a
    /// resource-bounded solver, so nothing may store it as a fact about the claim.
    Timeout,
}

impl Verdict {
    /// The weaker of two backend verdicts, for a claim that holds only if both of its parts do:
    /// a counterexample before a failure, a failure before a timeout, a timeout before an
    /// undecided result, and an undecided result before a bound. A counterexample or a failure
    /// refutes the claim whatever the parts not yet proven give, so a timeout does not replace
    /// it; a timeout replaces an undecided or bounded part, since the claim's verdict then
    /// depends on the time it was given.
    pub(crate) fn weakest(self, other: Self) -> Self {
        let rank = |verdict: Self| match verdict {
            Self::Disproved => 0,
            Self::Failed => 1,
            // Never a backend verdict: a crash ends the whole claim, so it is never combined.
            Self::Crashed => 2,
            Self::Timeout => 3,
            Self::Indeterminate => 4,
            Self::DepthBound => 5,
            Self::BreadthBound => 6,
            Self::Trusted => 7,
            Self::Proven => 8,
        };
        if rank(other) < rank(self) {
            other
        } else {
            self
        }
    }

    pub(crate) fn from_backend(status: &str) -> Option<Self> {
        Some(match status {
            "proven" => Self::Proven,
            "disproved" => Self::Disproved,
            "failed" => Self::Failed,
            "indeterminate" => Self::Indeterminate,
            "depth-bound" => Self::DepthBound,
            "breadth-bound" => Self::BreadthBound,
            _ => return None,
        })
    }

    /// The printed verdict word.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Proven => "proven",
            Self::Disproved => "disproved",
            Self::Failed => "failed",
            Self::Indeterminate => "indeterminate",
            Self::DepthBound => "depth-bound",
            Self::BreadthBound => "breadth-bound",
            Self::Trusted => "trusted",
            Self::Crashed => "crashed",
            Self::Timeout => "timeout",
        }
    }
}

/// One residual leaf of a proof.
#[derive(Clone, Debug, Serialize)]
pub struct ProofLeaf {
    /// The leaf state, with its constraint.
    pub state: Term,
    /// Semantic and claim transitions from the left-hand side; normalization is not a step.
    pub depth: u64,
    /// The backend's leaf outcome, as the k-rust host wire names it (`stuck`, `indeterminate`, ...).
    pub outcome: String,
    /// Whether this stuck leaf is a certified counterexample rather than an unresolved leaf.
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub certified: bool,
    /// This leaf was proven by vacuity; its displayed predecessor is not necessarily empty.
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub vacuous: bool,
    /// Actual claim applications, using the backend's labels, ids and proof depths.
    /// These may be guarded circularities; they do not certify a finite execution.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub claim_steps: Vec<k_rust::backend::TraceEntry>,
    /// A contradicted total declaration behind emptiness or an undefined step; terms are KAST envelopes.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub contradicted_total: Option<k_rust::backend::ContradictedTotalOutput<Term>>,
    /// Why a `timeout`, `stack-exhausted` or `indeterminate` leaf ended there, in the backend's
    /// words; absent for every other outcome.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
}

/// The result of proving one claim.
#[derive(Clone, Debug, Serialize)]
pub struct ProofReport {
    /// The claim label, as `kprove --claims` spells it (`<MAIN>-SPEC.label`).
    pub claim: String,
    /// The claim's modality.
    pub modality: Modality,
    /// The authored claim.
    pub origin: Option<SourceSpan>,
    /// The verdict.
    pub verdict: Verdict,
    /// Trusted reachability claims available to these proof requests, not every definition axiom.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub trusted_claims: Vec<String>,
    /// Residual leaves.
    pub leaves: Vec<ProofLeaf>,
    /// How the proof process ended, for a [`Verdict::Crashed`] claim; absent otherwise.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub crash: Option<Crash>,
}

impl ProofReport {
    /// The report of `claim`, whose proof process ended as `crash` says before the proof finished:
    /// verdict [`Verdict::Crashed`], no leaves.
    #[must_use]
    pub fn crashed(claim: &ClaimInfo, crash: Crash) -> Self {
        Self {
            claim: claim.label.clone(),
            modality: claim.modality,
            origin: claim.origin.clone(),
            verdict: Verdict::Crashed,
            trusted_claims: Vec::new(),
            leaves: Vec::new(),
            crash: Some(crash),
        }
    }
}

/// The exit status of a krs process that panicked (the status a Rust program's panic ends it
/// with), which krs never returns otherwise: a worker of a supervising `krs prove` that panics
/// ends with it, so the supervisor records the claim it was proving as [`Verdict::Crashed`].
pub const PANIC_EXIT_STATUS: i32 = 101;

/// How the process proving a [`Verdict::Crashed`] claim ended: one of `exit_status` and `signal`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Crash {
    /// The exit status, when the process exited with a status krs never returns (Z3, for one,
    /// exits with 114 on an internal error; a krs worker that panics exits with
    /// [`PANIC_EXIT_STATUS`]).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub exit_status: Option<i32>,
    /// The signal that killed the process (6 for an abort, 9 for a kill, such as the kernel's
    /// out-of-memory killer's).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub signal: Option<i32>,
    /// The Z3 library the process linked (`Z3_get_full_version`), absent in a build without
    /// one: the solver runs in the proof process, so it is part of what reproduces the crash.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub z3: Option<String>,
}

impl std::fmt::Display for Crash {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match (self.exit_status, self.signal) {
            (_, Some(signal)) => {
                write!(formatter, "the proof process was killed by signal {signal}")?;
                if let Some(name) = signal_name(signal) {
                    write!(formatter, " ({name})")?;
                }
                Ok(())
            }
            (Some(PANIC_EXIT_STATUS), None) => write!(
                formatter,
                "the proof process panicked (exit status {PANIC_EXIT_STATUS})"
            ),
            (Some(status), None) => {
                write!(formatter, "the proof process exited with status {status}")
            }
            (None, None) => formatter.write_str("the proof process ended without a status"),
        }
    }
}

/// The POSIX name of a signal whose number is the same on every platform krs runs on.
const fn signal_name(signal: i32) -> Option<&'static str> {
    Some(match signal {
        1 => "SIGHUP",
        2 => "SIGINT",
        3 => "SIGQUIT",
        4 => "SIGILL",
        6 => "SIGABRT",
        8 => "SIGFPE",
        9 => "SIGKILL",
        11 => "SIGSEGV",
        13 => "SIGPIPE",
        14 => "SIGALRM",
        15 => "SIGTERM",
        _ => return None,
    })
}

/// The solver a proof document's claims were proved with (the document's `solver` member):
/// k-rust's solver record, which every output whose content depends on a solver answer carries.
pub use k_rust::backend::{SolverBuild, SolverReport};

/// What a compiled definition supports in this build.
///
/// The fields match the browser lesson's `ExecutionCapabilities`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[expect(
    clippy::struct_excessive_bools,
    reason = "The fields mirror the browser lesson's ExecutionCapabilities record."
)]
pub struct Capabilities {
    /// `run`.
    pub execute: bool,
    /// `search`.
    pub search: bool,
    /// `prove`.
    pub prove: bool,
    /// An SMT solver decides symbolic conditions.
    pub smt: bool,
}

/// One configuration variable: the `#[k::init]` parameter that binds it, and its sort.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ConfigVariable {
    /// K's variable name without `$` (`ENV`).
    pub name: String,
    /// The `#[k::init]` parameter's Rust name (`env`); for a stream variable the language adds
    /// (`$IO`, `$STDIN`), which no parameter declares, the ASCII lowercase of the K name.
    pub parameter: String,
    /// The declared sort.
    pub sort: String,
    /// Whether this is the main parameter's variable, which FILE binds
    /// ([`crate::Parameter::main`]).
    pub is_main: bool,
}

impl std::fmt::Display for ConfigVariable {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "${} (init parameter {}): {}",
            self.name, self.parameter, self.sort
        )
    }
}

/// One claim of the compiled definition.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct ClaimInfo {
    /// The label as `kprove --claims` spells it (`<MAIN>-SPEC.label`).
    pub label: String,
    /// The emitted K module that holds the claim.
    pub module: String,
    /// The claim's modality.
    pub modality: Modality,
    /// The authored claim.
    pub origin: Option<SourceSpan>,
    /// Whether the claim is `trusted`: assumed without proof (KF-042).
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub trusted: bool,
    /// The backend's label for the claim; empty in a claim read back from its serialization.
    #[serde(skip)]
    pub(crate) backend_label: String,
}
