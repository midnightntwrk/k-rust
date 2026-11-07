//! Parse, run, search, and prove a KRS definition through the in-process k-rust backend.
//!
//! [`Semantics::compile`] lowers Definition IR through [`krs_k_rust::compile_definition_with_context_timed`] with the symbolic (Haskell-dialect) backend, as `krs-gate` always has, and loads the KORE into a [`k_rust::backend::Backend`].
//! Every operation then works on that one compiled definition:
//!
//! - [`Semantics::parse`] parses program text at a sort, as `kast --sort` does;
//! - [`Semantics::configure`] builds `initGeneratedTopCell` from the `#[k::init]` parameters' values, as krun does from `$PGM` and the other configuration variables;
//! - [`Semantics::decode_input`] and [`Semantics::case_inputs`] read a parameter's value, or a case's values, written in the one typed encoding, whose normative statement is the documentation of [`inputs`];
//! - [`Semantics::run`] follows one path with strategy `any`, as krun does;
//! - [`Semantics::search`] returns the set of reachable states, as `krun --search` does;
//! - [`Semantics::prove`] proves the selected claims, as kprove does;
//! - [`Semantics::unparse`] prints a term through the definition's grammar, as `krun --output pretty` does, and [`Semantics::unparse_program`] prints a parsed program as `kast --output program` does (`krs-unparse`).
//! - [`Semantics::values`] names constructors and sorts by their KRS declarations, so a configuration variable can be given as a [`Value`] ([`ConfigValue::Value`]), and [`Semantics::views`] reads a result's cells as values by their Rust field names.
//! - [`Semantics::end_of`] and [`Semantics::ends_of`] read a run's or a search's ends, [`Semantics::read_end`] and [`Semantics::end_document`] read and write an end as a document of the typed encoding, and [`Semantics::compare_ends`] and [`Semantics::check_expectation`] compare ends on their observable cells by Rust field path; the documentation of [`ends`] is their normative statement.
//! - [`Semantics::evaluate`] computes a function's value as a consequence of the definition, and [`Semantics::cell_views`] resolves the views a comparison applies to cells; the documentation of [`views`] is their normative statement.
//!
//! The crate is filesystem-free: the caller supplies Definition IR, program text, and (optionally) the authored source text that trace origins are positioned in.
//! The serialized reports form the `krs-exec` JSON shapes that `--output json` prints: `krs-exec/5` for a run ([`RUN_REPORT_SCHEMA`]), `krs-exec/1` for a search ([`SEARCH_REPORT_SCHEMA`]), `krs-exec/2` for a proof ([`PROVE_REPORT_SCHEMA`]).
//! Every operation can recurse deeply through large terms: callers run it on a thread with a large stack, as the CLI and the gate session do (64 MiB).
//!
//! # Features
//!
//! The features choose only how Z3 is linked; every operation exists in every build.
//! `z3-inference-gh-release` (the default, krs-cli's) links k-rust's release download of Z3, and `z3-inference` links the Z3 the build environment provides.
//! With `default-features = false` no Z3 is linked: the backend then has no SMT solver ([`Semantics::capabilities`] reports `smt` false, [`z3_version`] is `None`), and every query a step, a simplification or a proof puts to a solver fails as unavailable at once.
//! A library user that only compiles a definition, configures starts ([`Semantics::configure`], [`Semantics::case_inputs`]) and reads or writes end documents ([`Semantics::read_end`], [`Semantics::end_document`]) needs no feature: reading and writing a document asks no solver, and configuring evaluates the initializer at the values given, where the equations' conditions are ground and the simplifier decides them without one.
//! A solver matters to a run, a search or a proof whose conditions are not decided at values, where its absence leaves the question undecided (an `indeterminate` halt, an unknown verdict) rather than answered otherwise.
//!
//! # Report versions
//!
//! A `krs-exec/N` name states which shape a document has, so a reader can refuse one it does not know.
//! A kind's version must change when a reader of its old version would read a document of the new shape falsely, a field that keeps its name and changes what it denotes included.
//! Each document kind (run, search, proof) carries the version of its own last change, and the numbers are one sequence shared by every kind: a change to any kind's shape takes the number after the highest any kind uses, never a number another kind already uses.
//! A version therefore names one shape of each kind, whatever kind a reader expects.

mod cell_types;
mod claims;
pub mod condition;
mod configuration;
mod console;
mod decided;
mod encode;
pub mod ends;
pub mod inputs;
mod instance_text;
mod origin;
mod overloads;
mod read_back;
mod report;
mod reversal;
mod rules;
pub mod skipped_operand;
mod stage;
mod valueless;
mod values;
mod view;
pub mod views;

use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroU64;
use std::sync::Arc;
use std::{collections::HashMap, fmt};

use k_rust::{
    backend::{
        Backend, EffectOutput, ExecuteRequest, ExecutionCandidateOutput, ExecutionStrategy,
        HaltReasonOutput, KoreExecutionLeaf, KoreExecutionResult, KoreSearchResponse, ProveRequest,
        RunCoverageOutput, SearchRequest, SearchTypeArg, TraceEntry,
    },
    inner::{ParseError, ProgramError, ProgramParseError},
    k_rust_backend::definition::Admission,
    kast::{
        Sort as KastSort,
        convert::{Converter, sort_hooks},
        json as kast_json,
        printer::Printer,
    },
    kore::ast::Pattern,
};
use krs_ir::{SourceFileId, measure::Timings};
use krs_ir_levels::DefinitionIr;
use krs_k_rust::{
    CompileOptions, CompiledArtifacts, ConfigurationContext, DefinitionCompileError,
    NativeDefinition, SentenceProvenance, compile_definition_with_context_timed,
    compile_spec_definition_with_context_timed,
};
use krs_unparse::ListSpelling;
pub use stage::{CompiledStage, SPEC_STAGE_FORMAT, STAGE_FORMAT, SpecStage};

use condition::ConditionOracle;
pub use condition::{ArrivalObservation, ObservationError, ResolvedCondition};
pub use configuration::Configuration;
pub use encode::{EncodeError, EncodeErrorKind, canonical_text, decode, encode};
pub use ends::{
    CellInfo, Compared, Comparison, DIFFERENCE_FORMAT, Difference, DifferenceAt, DifferenceSide,
    End, EndCell, EndCells, EndClass, EndError, Ends, Rendered, Side, VALUE_CAP,
};
pub use inputs::{
    Case, CaseDocument, CaseRun, Expectation, InputError, InputFiles, InputType, MainVariable,
    NoFiles, Parameter, declares_variable, json_document, main_variable, toml_document,
    toml_text_document,
};
pub use k_rust::backend::{
    BackendError, BackendOptions, ChosenValueOutput, DEFAULT_SMT_RESOURCE_LIMIT,
};
use k_rust::backend::{BackendErrorKind, StopSide};
/// The printer crate, for callers that print a term through [`Semantics::unparser`].
pub use krs_unparse as unparse;
pub use krs_unparse::{Mode as UnparseMode, Printed, Warning as UnparseWarning};
pub use origin::{Origins, item_spelling};
pub use read_back::{PrintedCell, ReadBack};
pub use report::{
    Capabilities, ClaimInfo, ConfigVariable, Coverage, CoveredRule, Crash, Halt, Modality,
    NamedRule, PANIC_EXIT_STATUS, PROVE_REPORT_SCHEMA, ProofLeaf, ProofReport, RUN_REPORT_SCHEMA,
    RuleKind, RunReport, SEARCH_REPORT_SCHEMA, SearchReport, Solution, SolverBuild, SolverReport,
    SourceSpan, Step, StepOrigin, Stop, StopAt, Term, Undecided, Verdict,
};
pub use values::{Ctor, Decl, Float, SortRef, Value, ValueError, ValueIndex};
pub use view::{CellError, StateView, View};
pub use views::{CellViews, EvaluationError};

/// The Z3 library this build links (`Z3_get_full_version`), or `None` in a build without one.
#[must_use]
pub fn z3_version() -> Option<&'static str> {
    k_rust::backend::z3_version()
}

/// Authored source text by file identity, used to position trace and claim origins.
///
/// A provider returns `None` when the text is unavailable or no longer matches the file's digest;
/// origins then carry the file without a line and column.
pub type SourceText = Box<dyn Fn(&SourceFileId) -> Option<String>>;

/// Options for [`Semantics::run`].
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RunOptions {
    /// At most this many rewrite steps; equation evaluation is not a step. A step is the
    /// compiled definition's, the heating and cooling steps of strictness and contexts included,
    /// so the bound is a budget, not a point of the program's run ([`StopCriterion`] names one).
    pub depth: Option<u64>,
    /// Record each rewrite step ([`RunReport::trace`]).
    ///
    /// Only then does the backend keep its trace of the path (k-rust's `ExecuteRequest::trace`),
    /// which holds an entry for every rewrite and simplification the run makes, so a run without
    /// it holds nothing that grows with its length on that account.
    pub trace: bool,
    /// Check that a run reported stuck ended where no rule applies, at a state that is its own
    /// value, as `KRS_CHECK_ENDS=1` asks of every run (`check_final_state`).
    pub check_ends: bool,
    /// Report the run's coverage ([`RunReport::coverage`]): the rules and equations it matched,
    /// applied and committed, with how many times it applied each.
    pub coverage: Option<CoverageOptions>,
    /// End the run at the stop the criterion names ([`RunReport::stop`]); by default the run
    /// ends only on its own. A [`StopRules`] converts into the criterion that ends the run at
    /// its first stop (`stop: rules.into()`).
    pub stop: StopCriterion,
    /// The budget of polls of each evaluation of the stop condition ([`StopWhen`]), as
    /// [`CellViews::evaluate_within`] bounds a view's; `None` for no bound.
    pub condition_budget: Option<u64>,
}

/// Where a run ends besides its own end ([`RunOptions::stop`]).
///
/// Whatever the criterion, a run ends on its own (no rule applies, or the state has no value)
/// and is cut off by a bound (the step budget [`RunOptions::depth`], or the backend's); a
/// criterion only adds ends. A bound is no end of the run: a run that reaches its step budget
/// reports `depth-bound`, never a stop, and counts no arrival there, and an expectation is never
/// met by it ([`ends`], "Results"): checked against an expectation, such a run is inconclusive.
#[non_exhaustive]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub enum StopCriterion {
    /// The run ends only on its own.
    #[default]
    None,
    /// The run ends at its `count`th arrival at a stop of `rules`.
    ///
    /// An arrival is what ends a run at the stop rules: a step by a stop rule that is its
    /// state's one successor, the run ending at that state for a stop-before rule and at the
    /// step's successor for a stop-after rule; a step by a stop rule from a state with several
    /// successors is no arrival. The backend counts the arrivals along the path (k-rust's
    /// `ExecuteRequest::stop_count`) and takes each one before the `count`th as any other step,
    /// so the run is one request, one path, and its `steps`, trace, depth bound and coverage are
    /// the uncut run's up to where it ends. The states it passes are read as the uncut run reads
    /// the states of its path: only the end is read for a term with no value. A run that ends
    /// on its own first reports that end, and how many arrivals it counted
    /// ([`RunReport::stops`]).
    ///
    /// With a stop condition ([`StopWhen`]) the count counts the arrivals whose stop state the
    /// condition holds of, and every other arrival is taken as any other step.
    Rules {
        /// The rules a stop is a step by.
        rules: StopRules,
        /// The arrival the run ends at: the stop event, with a condition.
        count: NonZeroU64,
        /// The condition an arrival's stop state must satisfy to be a stop event; `None` for
        /// none, every arrival an event.
        when: Option<StopWhen>,
    },
}

impl StopCriterion {
    /// The arrival a run ends at, `None` when it ends only on its own.
    #[must_use]
    pub const fn count(&self) -> Option<NonZeroU64> {
        match self {
            Self::None => None,
            Self::Rules { count, .. } => Some(*count),
        }
    }

    /// The stop condition, if the criterion has one.
    #[must_use]
    pub const fn when(&self) -> Option<&StopWhen> {
        match self {
            Self::Rules {
                when: Some(when), ..
            } => Some(when),
            _ => None,
        }
    }
}

/// A stop condition ([`StopCriterion::Rules`], [module documentation](crate::condition)): a
/// function of named cells, of result sort `Bool`, that an arrival's stop state must satisfy to
/// be a stop event, evaluated in one fixed observer definition.
///
/// The stop state is the state the run would end at there: the state before a stop-before
/// rule's step, the successor of a stop-after rule's. The condition is asked only at arrivals.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StopWhen {
    /// The function, by its KRS path or a `::`-aligned suffix of it, as a view names one
    /// ([`ValueIndex::function_decl`]).
    pub function: String,
    /// The leaf cells it reads, by Rust field path, in the order of its parameters.
    pub cells: Vec<String>,
    /// The definition it is evaluated in, `PACKAGE:DEFINITION` as an observer is named; `None`
    /// for the run's own definition. A front end resolves the name and passes the definition to
    /// [`Semantics::run_observed`].
    pub observer: Option<String>,
}

/// The criterion that ends a run at its first stop of `rules`, or only on its own where `rules`
/// names none.
impl From<StopRules> for StopCriterion {
    fn from(rules: StopRules) -> Self {
        if rules.is_empty() {
            Self::None
        } else {
            Self::Rules {
                rules,
                count: NonZeroU64::MIN,
                when: None,
            }
        }
    }
}

/// The rewrite rules at which a run ends ([`RunOptions::stop`]): k-rust's cut-point and terminal
/// rules (`ExecuteRequest::cut_point_rules`, `terminal_rules`).
///
/// A name is a KRS item or a K label.
///
/// - A name with `::` is a KRS item, by its Rust path: `crate::` and the path below the root
///   crate's root (`crate::ppu::frame_end`), or a dependency's own crate name, the crate name of
///   its library whatever a depending manifest renames it to, and the path below its root
///   (`lang::step`). The root package is
///   the one whose module is the definition's main module. A path with neither prefix
///   (`ppu::frame_end`) is read both ways, as Rust reads a path at the crate root. The name
///   selects every rewrite rule the item lowers to (a context's heat and cool rules, a strict
///   production's), whatever their labels. It is an error where the item lowers to no rewrite
///   rule ([`ExecError::UnknownItem`]), or where the path names items of several packages
///   ([`ExecError::AmbiguousItem`]). No label KRS emits holds `::`, so a KRS label is never
///   read as an item.
/// - Any other name is a K label, exactly (`SM83.boundary-fetch`) or a unique `.`-suffix
///   (`boundary-fetch`), as `krs prove --claim` names a claim; a label several rules carry names
///   each of them. The name is resolved among the labels of every sentence, an exact label
///   winning over every suffix, and is an error where it selects no sentence, several labels, or
///   a sentence that is no rewrite rule ([`ExecError::UnknownRule`],
///   [`ExecError::AmbiguousRule`]).
///
/// An equation, a simplification or a definedness equation takes no step, so no run stops at it.
///
/// A run that ends at a stop rule reports `stopped` ([`Halt::Stopped`]) and the stop
/// ([`RunReport::stop`]), and a later run from [`RunReport::resume`] goes on along the path from
/// there; any run can be resumed so, whatever ended it.
/// Each step of the path is then taken by exactly one of the runs: summed over a run cut at stop
/// rules and resumed, the runs' `steps`, their traces in order and their coverage are the uncut
/// run's (coverage's counts but for an equation instance the uncut run serves from its memo,
/// which a later run evaluates again).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct StopRules {
    /// End before a step by one of these rules: the run ends at the state the rule would rewrite,
    /// and the step is the resumed run's first, which its `steps`, its trace, its depth bound and
    /// its coverage count (the stopped run's count none of it, the backend's proposal of the
    /// step's successor included), so the resumed run does not stop at the same step again.
    /// The stop names the rule.
    ///
    /// The proposed successor is read as a run's end is: where it holds a term with no value
    /// (`Semantics::run`'s reading, which the backend's own normalization does not decide), the
    /// step reaches no state, so the run does not stop but ends undefined at the state the rule
    /// would rewrite, as the uncut run does where its end holds that term.
    pub before: Vec<String>,
    /// End after a step by one of these rules: the run ends at the rule's successor, and resumes
    /// from there. The stop names the rule when these names select one rule identity, or the run
    /// keeps its trace ([`RunOptions::trace`]), whose last step it is; otherwise it does not:
    /// k-rust names a terminal rule only in the leaf's `detail`, legacy text that is no stable
    /// encoding, which krs-exec does not read.
    pub after: Vec<String>,
}

impl StopRules {
    /// Whether no rule is named.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.before.is_empty() && self.after.is_empty()
    }
}

/// The stop rules of one run by `UNIQUE_ID`, as the backend selects them, and the arrival at a
/// stop the run ends at.
#[derive(Clone, Debug, Eq, PartialEq)]
struct StopIds {
    before: Vec<String>,
    after: Vec<String>,
    count: NonZeroU64,
}

impl Default for StopIds {
    fn default() -> Self {
        Self {
            before: Vec::new(),
            after: Vec::new(),
            count: NonZeroU64::MIN,
        }
    }
}

impl StopIds {
    /// Whether no rule is selected, so the run has no stop to count.
    fn is_empty(&self) -> bool {
        self.before.is_empty() && self.after.is_empty()
    }
}

/// What a run's coverage also reports ([`RunOptions::coverage`]).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CoverageOptions {
    /// Also list the rules and equations the run only offered ([`Coverage::offered`]). It costs
    /// one left-hand-side match at every visit of a site for each candidate the site skipped,
    /// so it grows with the visits (k-rust's `ExecuteRequest::collect_offered`).
    pub offered: bool,
}

/// K's search modes.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum SearchMode {
    /// `=>!`: final states (the default).
    #[default]
    Final,
    /// `=>*`: every reachable state.
    All,
    /// `=>1`: states one step away.
    OneStep,
    /// `=>+`: states one or more steps away.
    OneOrMoreSteps,
}

impl SearchMode {
    /// Every mode, in command-line catalog order.
    pub const ALL: [Self; 4] = [Self::Final, Self::All, Self::OneStep, Self::OneOrMoreSteps];

    /// The command-line spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Final => "final",
            Self::All => "all",
            Self::OneStep => "one-step",
            Self::OneOrMoreSteps => "one-or-more-steps",
        }
    }

    const fn backend(self) -> SearchTypeArg {
        match self {
            Self::Final => SearchTypeArg::Final,
            Self::All => SearchTypeArg::All,
            Self::OneStep => SearchTypeArg::OneStep,
            Self::OneOrMoreSteps => SearchTypeArg::OneOrMoreSteps,
        }
    }
}

/// Options for [`Semantics::search`].
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SearchOptions {
    /// Which states count as solutions.
    pub mode: SearchMode,
    /// At most this many rewrite steps on any path.
    pub depth: Option<u64>,
    /// At most this many solutions.
    pub max_solutions: Option<usize>,
    /// Record each solution's rewrite steps.
    pub trace: bool,
}

/// Options for [`Semantics::prove`].
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ProveOptions {
    /// An author spec module (KF-041); `None` selects the generated `<MAIN>-SPEC`.
    pub module: Option<String>,
    /// Claim labels, resolved by exact match or unique `.`-suffix; empty selects every claim.
    pub claims: Vec<String>,
    /// At most this many proof transitions, counting semantic rewrites and applied claims.
    pub depth: Option<u64>,
    /// The wall-clock time one claim's proof may take ([`Semantics::prove_claim`]): a proof
    /// still running then is cancelled and the claim's verdict is [`Verdict::Timeout`], unless
    /// a part of the claim already refutes it; the report keeps the leaves of the disjuncts of the
    /// claim's left-hand side whose proofs ended before. The cancellation takes effect at the
    /// backend's next stop check, after the Z3 attempt in progress ends. A zero duration cancels
    /// before the proof starts. `None`: no wall-clock bound.
    pub claim_timeout: Option<std::time::Duration>,
}

/// Program text, with the name diagnostics cite: FILE, which binds the main parameter, or a
/// text file an input names (`$text-file`).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgramInput {
    /// The file name, or `<stdin>`.
    pub name: String,
    /// The program text.
    pub text: String,
}

/// What a program file binds to the main parameter ([`Semantics::program_file`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProgramFile {
    /// The file's text, which [`ConfigInputs::program`] binds.
    Text(ProgramInput),
    /// The file's bytes, the `Bytes` value of the main parameter.
    Bytes {
        /// The main parameter's Rust name, which binds it by name.
        parameter: String,
        /// The file's bytes, unchanged.
        value: Value,
    },
}

/// The value of one configuration variable.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConfigValue {
    /// Surface text, parsed at the variable's declared sort as `krun -c` parses it.
    Text(String),
    /// The text of a file, parsed as [`Self::Text`] is; a parse error is located in the file.
    TextFile(ProgramInput),
    /// A value, typed at the variable's declared sort without a parse
    /// ([`ValueIndex::ctor`], [`Value::map`], ...).
    Value(Value),
}

impl From<String> for ConfigValue {
    fn from(text: String) -> Self {
        Self::Text(text)
    }
}

impl From<&str> for ConfigValue {
    fn from(text: &str) -> Self {
        Self::Text(text.to_owned())
    }
}

impl From<Value> for ConfigValue {
    fn from(value: Value) -> Self {
        Self::Value(value)
    }
}

/// The inputs of one initial configuration.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ConfigInputs {
    /// FILE's text, bound to the main parameter ([`Parameter::main`]), whatever its K name. A
    /// main parameter of type exactly `Bytes` takes the file's bytes instead, bound by name
    /// ([`Semantics::program_file`]).
    pub program: Option<ProgramInput>,
    /// Bindings by name, as `-c NAME=TEXT` gives them in command-line order. NAME is a
    /// `#[k::init]` parameter's Rust name (`env`) or its configuration variable's K name (`ENV`
    /// or `$ENV`), the main parameter's included; text and values may be mixed.
    pub variables: Vec<(String, ConfigValue)>,
    /// Console input for the `stream = "stdin"` cell, as krun reads standard input under `--io off`;
    /// `None` binds an empty stream. It is ignored when the definition has no stdin stream cell.
    pub stdin: Option<Vec<u8>>,
}

/// A state to run or search from: an initial configuration ([`Semantics::configure`]), or the
/// state a run left off at ([`RunReport::resume`]).
#[derive(Clone, Debug)]
pub struct State {
    /// The pattern a run or search from the state starts at.
    pattern: Pattern,
    /// The step a run that stopped before its rule did not take ([`StopRules::before`]), which
    /// a run from this state takes first; `pattern` is the step's successor.
    taken: Option<TakenStep>,
}

impl State {
    pub(crate) const fn new(pattern: Pattern) -> Self {
        Self {
            pattern,
            taken: None,
        }
    }

    /// The KORE pattern a run or search from the state starts at: `initGeneratedTopCell`
    /// applied to the inputs for an initial configuration, the configuration itself for the
    /// state a run left off at, and after a stop before a rule, that rule's successor: a search
    /// starts there, and a run takes the rule's step first ([`Semantics::run`]).
    #[must_use]
    pub const fn kore(&self) -> &Pattern {
        &self.pattern
    }
}

/// The step by a stop-before rule that a run proposed and did not take (`State::taken`).
#[derive(Clone, Debug)]
struct TakenStep {
    /// The state the step rewrites, where a run that takes no step ends.
    before: Pattern,
    /// The rule's `UNIQUE_ID`.
    rule_id: String,
    /// The rule's label.
    label: Option<String>,
}

/// The successor a stop before a rule proposes ([`read_proposal`]).
struct Proposal {
    successor: Pattern,
    rule_id: String,
    label: Option<String>,
}

/// How [`Semantics::print`] renders a term.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum PrintStyle {
    /// Textual KAST, as `kast --output kast` prints it.
    #[default]
    Kast,
    /// The KAST JSON envelope, as `--output json` prints it.
    Json,
    /// KORE text, as `--output kore` prints it.
    Kore,
    /// Grammar-directed text without colour, as `krun --output pretty` prints it; warnings are dropped (see [`Semantics::unparse`]).
    Pretty,
}

/// A part of a configuration value that does not fit the element types its variable is declared
/// with ([`ExecError::CollectionElementSort`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElementSortMismatch {
    /// The variable, without `$`.
    pub variable: String,
    /// The `#[k::init]` parameter that declares the variable.
    pub parameter: String,
    /// The variable's declared type (`Map<Id, Value>`).
    pub declared: String,
    /// Where the part is in the value (``the value at key `x` ``).
    pub position: String,
    /// The part, printed through the definition's grammar.
    pub element: String,
    /// The part's sort.
    pub sort: String,
    /// The declared element sort it is not at most.
    pub expected: String,
    /// What the prints of the position and the part say of themselves
    /// ([`krs_unparse::Warning`]), each once.
    pub warnings: Vec<String>,
}

impl fmt::Display for ElementSortMismatch {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            variable,
            parameter: _,
            declared,
            position,
            element,
            sort,
            expected,
            warnings,
        } = self;
        write!(
            formatter,
            "configuration variable `${variable}`, declared `{declared}`: {position} is `{element}` of sort {sort}, which is not a subsort of {expected}"
        )?;
        for warning in warnings {
            write!(formatter, " (as printed: {warning})")?;
        }
        Ok(())
    }
}

/// The first segment of a KRS item path that names no item, where it names no package the way
/// a stop names one ([`ExecError::UnknownItem`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UnknownCrate {
    /// A name the definition records no package by, such as a depending manifest's rename of a
    /// dependency: a stop names a dependency by the crate name of its library.
    Unrecorded(String),
    /// The package name, with `-` written `_`, of a dependency whose `[lib]` section names its
    /// library otherwise, with that library's crate name: Rust names the crate by it, and so does
    /// a stop.
    PackageName(String),
    /// The root package's own crate name, or `self`: names of the root package, whose items a
    /// stop names `crate::` and their path.
    Root(String),
    /// The crate name of a dependency none of whose items writes a rule or an equation of the
    /// definition: the package is the definition's, and no item path below it names a sentence.
    NoItem(String),
}

/// A failure of a `krs-exec` operation.
#[derive(Debug)]
pub enum ExecError {
    /// The definition did not compile.
    Compile(DefinitionCompileError),
    /// The backend rejected an operation.
    Backend(String),
    /// FILE was given but the `#[k::init]` has no main parameter for it to bind.
    StrayProgram {
        /// Every parameter, in declaration order, to bind by name instead.
        parameters: Vec<Parameter>,
    },
    /// FILE is not UTF-8 text, and the main parameter reads a file as text.
    ProgramNotText {
        /// The file name, or `<stdin>`.
        file: String,
        /// The main parameter, boxed: beside the file name it is the largest payload of any
        /// variant, and every `Result` that carries an `ExecError` would otherwise grow to fit it.
        parameter: Box<Parameter>,
    },
    /// The main parameter was bound neither by FILE nor by name.
    MissingProgram {
        /// The main parameter.
        parameter: Parameter,
    },
    /// `-c` named a variable the definition does not declare.
    UnknownVariable {
        /// The name as written.
        name: String,
        /// Every declared variable.
        variables: Vec<ConfigVariable>,
    },
    /// A typed input named a console stream (`$STDIN`, `$IO`), which no `#[k::init]` parameter
    /// declares and the console fills.
    StreamInput {
        /// The stream's K name, without `$`.
        variable: String,
    },
    /// A variable was bound twice: by FILE and by name, or by two spellings of its name.
    DuplicateVariable(ConfigVariable),
    /// Declared variables that were not bound.
    MissingVariables(Vec<ConfigVariable>),
    /// Program or `-c` text that does not parse.
    Parse {
        /// The input (`prog.imp`, `<stdin>`, or `-c ENV`).
        input: String,
        /// The sort it was parsed at.
        sort: String,
        /// The parser's message, with its location.
        message: String,
    },
    /// `--sort` named a sort the program grammar does not have.
    UnknownSort {
        /// The sort as written.
        sort: String,
        /// The program sorts.
        sorts: Vec<String>,
    },
    /// `krs parse` without `--sort` on a definition without a main parameter.
    NoProgramSort,
    /// A document that is no value of its input in the typed encoding ([`Semantics::decode_input`]).
    Input(InputError),
    /// `--claim` matched no claim.
    UnknownClaim {
        /// The label as written.
        requested: String,
        /// A close label, when one exists.
        suggestion: Option<String>,
    },
    /// `--claim` matched several claims by suffix.
    AmbiguousClaim {
        /// The label as written.
        requested: String,
        /// The matching labels.
        matches: Vec<String>,
    },
    /// A stop rule ([`StopRules`]) named no rewrite rule.
    UnknownRule {
        /// The label as written.
        requested: String,
        /// The label and kind of the sentence that is no rewrite rule the name selects instead,
        /// when it selects one (an equation, a simplification or a definedness equation).
        sentence: Option<(String, RuleKind)>,
        /// A close rewrite-rule label, when one exists.
        suggestion: Option<String>,
    },
    /// A stop rule ([`StopRules`]) matched several rewrite-rule labels by suffix.
    AmbiguousRule {
        /// The label as written.
        requested: String,
        /// The matching labels.
        matches: Vec<String>,
    },
    /// A stop named by KRS item ([`StopRules`]) lowers to no rewrite rule.
    UnknownItem {
        /// The item as written.
        requested: String,
        /// The kinds of the sentences the item lowers to, none of them a rewrite rule, each
        /// once; empty where no sentence of the definition is the item's.
        kinds: Vec<RuleKind>,
        /// Where no sentence is the item's: the path's first segment, when it is neither
        /// `crate`, nor a dependency's crate name, nor a module of the root package's items, and
        /// what it is instead.
        unknown_crate: Option<UnknownCrate>,
        /// Where no sentence is the item's: the names that select the items with a rewrite rule
        /// at the path below the first segment (`my_lang::step` for `lang::step`), sorted.
        suggestions: Vec<String>,
    },
    /// A stop named by KRS item ([`StopRules`]) names items of several packages.
    AmbiguousItem {
        /// The item as written.
        requested: String,
        /// Each item it names, by the spelling that names it where any does (`crate::step`,
        /// `lang::step`), with its package's K namespace, ordered by namespace.
        matches: Vec<(String, String)>,
    },
    /// `prove` on a definition without claims.
    NoClaims,
    /// `--spec-module` named an author spec module without claims (KF-041).
    NoSpecClaims(String),
    /// `--spec-module` named no author spec module, or (without it) every
    /// claim is in a spec module (KF-041).
    UnknownSpecModule {
        /// The module as written, or `None` when `--spec-module` was not given.
        requested: Option<String>,
        /// The author spec modules.
        modules: Vec<String>,
        /// The generated module of the loose claims.
        generated: String,
    },
    /// `search` on a definition with stream cells.
    SearchWithStreams,
    /// An operation this build or this unit does not provide.
    Unavailable(String),
    /// The backend returned a result KRS cannot read.
    Result(String),
    /// A run reaches several states under conditions over terms that may have values, which it
    /// cannot decide (`one_path`); the message names them.
    Undecided(String),
    /// A configuration value that is no term of the definition, or not of its variable's sort.
    Value {
        /// The variable, without `$`.
        variable: String,
        /// Why the value does not fit.
        error: ValueError,
    },
    /// A configuration value with a part that does not fit the element types of the typed
    /// collection cell the variable fills (`skip` stored in a `Map<Id, Value>` cell).
    CollectionElementSort(Box<ElementSortMismatch>),
    /// A configuration variable's text applies a function evaluated in one instance of a Map
    /// collection, which receives the instance's key, while an input is evaluated in no instance.
    InstanceFunction {
        /// The variable, without `$`.
        variable: String,
        /// Why the function cannot be applied there.
        reason: String,
    },
    /// A case document that is none, has no case of a requested name, or whose expectation is no
    /// partial end of the definition or does not state a cell it is compared on
    /// ([`Semantics::expectation`]); the message names the position.
    Case(String),
    /// A stop condition that cannot be asked ([`Semantics::stop_condition`]): a function or a
    /// cell it names is not one it may read, or no observer was given to evaluate it in; the
    /// message names the cause.
    StopWhen(String),
    /// The stop condition has no value at an arrival of the run: the observation does not exist
    /// at a reached state, so the stop criterion is undefined on this run.
    StopCondition {
        /// The stop rule, as a report names it.
        rule: String,
        /// The run's steps to the arrival's stop state.
        steps: u64,
        /// Why, naming the cell or the evaluation.
        reason: String,
    },
}

impl fmt::Display for ExecError {
    #[expect(
        clippy::too_many_lines,
        reason = "One arm per error variant keeps every message in one place."
    )]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Compile(error) => error.fmt(formatter),
            Self::Backend(message)
            | Self::Unavailable(message)
            | Self::Result(message)
            | Self::Undecided(message)
            | Self::StopWhen(message)
            | Self::Case(message) => {
                formatter.write_str(message)
            }
            Self::StopCondition {
                rule,
                steps,
                reason,
            } => write!(
                formatter,
                "the stop condition has no value at the arrival at `{rule}` after {steps} step{}: {reason}",
                if *steps == 1 { "" } else { "s" }
            ),
            Self::StrayProgram { parameters } => {
                formatter.write_str(NO_MAIN_PARAMETER)?;
                formatter.write_str(", so FILE binds nothing; bind its parameters by name")?;
                if parameters.is_empty() {
                    return formatter.write_str(" (it has none)");
                }
                formatter.write_str(": ")?;
                for (index, parameter) in parameters.iter().enumerate() {
                    if index > 0 {
                        formatter.write_str(", ")?;
                    }
                    write!(formatter, "{parameter}")?;
                }
                Ok(())
            }
            Self::ProgramNotText { file, parameter } => write!(
                formatter,
                "`{file}` is not UTF-8 text, and {}",
                parameter.reads_file_text()
            ),
            Self::MissingProgram { parameter } => write!(
                formatter,
                "the main parameter `{}` (${}: {}) is unbound; pass FILE, `-` for standard input, or bind `{}` by name",
                parameter.name, parameter.variable, parameter.ty, parameter.name
            ),
            Self::UnknownVariable { name, variables } => {
                write!(formatter, "unknown configuration variable `{name}`")?;
                write_variables(formatter, "the definition declares", variables)
            }
            Self::StreamInput { variable } => write!(
                formatter,
                "configuration variable `${variable}` is a console stream, which the console fills; no #[k::init] parameter declares it, so it takes no value by name"
            ),
            Self::DuplicateVariable(variable) => write!(
                formatter,
                "configuration variable `${}` (init parameter {}) is bound twice",
                variable.name, variable.parameter
            ),
            Self::MissingVariables(variables) => {
                let names = variables
                    .iter()
                    .map(|variable| format!("-c {}=VALUE", variable.parameter))
                    .collect::<Vec<_>>()
                    .join(" and ");
                write!(formatter, "missing configuration variables; pass {names}")?;
                write_variables(formatter, "missing", variables)
            }
            Self::Parse {
                input,
                sort,
                message,
            } => write!(formatter, "{input} does not parse at sort {sort}: {message}"),
            Self::UnknownSort { sort, sorts } => write!(
                formatter,
                "the program grammar has no sort `{sort}`; program sorts: {}",
                sorts.join(", ")
            ),
            Self::NoProgramSort => {
                formatter.write_str(NO_MAIN_PARAMETER)?;
                formatter.write_str(", so there is no default sort; pass --sort")
            }
            Self::Input(error) => error.fmt(formatter),
            Self::UnknownClaim {
                requested,
                suggestion,
            } => {
                write!(formatter, "no claim has label `{requested}`")?;
                if let Some(suggestion) = suggestion {
                    write!(formatter, "; did you mean `{suggestion}`?")?;
                }
                Ok(())
            }
            Self::AmbiguousClaim { requested, matches } => write!(
                formatter,
                "claim label `{requested}` is ambiguous; matches {}",
                matches
                    .iter()
                    .map(|label| format!("`{label}`"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::UnknownRule {
                requested,
                sentence,
                suggestion,
            } => write_unknown_rule(
                formatter,
                requested,
                sentence.as_ref().map(|(label, kind)| (label.as_str(), *kind)),
                suggestion.as_deref(),
            ),
            Self::AmbiguousRule { requested, matches } => write!(
                formatter,
                "rule label `{requested}` is ambiguous; matches {}",
                matches
                    .iter()
                    .map(|label| format!("`{label}`"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::UnknownItem {
                requested,
                kinds,
                unknown_crate,
                suggestions,
            } => write_unknown_item(
                formatter,
                requested,
                kinds,
                unknown_crate.as_ref(),
                suggestions,
            ),
            Self::AmbiguousItem { requested, matches } => write!(
                formatter,
                "KRS item `{requested}` is ambiguous: it names {}; `crate::` names the root package's item alone, and a K label names one package's rule",
                matches
                    .iter()
                    .map(|(item, namespace)| format!(
                        "`{item}` of the package of K namespace `{namespace}`"
                    ))
                    .collect::<Vec<_>>()
                    .join(" and ")
            ),
            Self::NoClaims => formatter.write_str("this definition has no claims"),
            Self::NoSpecClaims(module) => write!(
                formatter,
                "spec module `{module}` has no claims of its own or through its imports"
            ),
            Self::UnknownSpecModule {
                requested,
                modules,
                generated,
            } => {
                let modules = modules
                    .iter()
                    .map(|module| format!("`{module}`"))
                    .collect::<Vec<_>>()
                    .join(", ");
                match requested {
                    Some(requested) => write!(
                        formatter,
                        "no spec module is named `{requested}`; the definition's spec modules are {} and the generated `{generated}`",
                        if modules.is_empty() { "none".to_owned() } else { modules }
                    ),
                    None => write!(
                        formatter,
                        "every claim of this definition is in a spec module; pass --spec-module with one of {modules}"
                    ),
                }
            }
            Self::Value { variable, error } => {
                write!(formatter, "configuration variable `${variable}`: {error}")
            }
            Self::CollectionElementSort(mismatch) => mismatch.fmt(formatter),
            Self::InstanceFunction { variable, reason } => {
                write!(formatter, "configuration variable `${variable}`: {reason}")
            }
            Self::SearchWithStreams => formatter.write_str(
                "krs search cannot run a definition with stream cells; K's search has no console I/O (k-rust rejects --io on in search)",
            ),
        }
    }
}

/// Why a definition takes no program file.
const NO_MAIN_PARAMETER: &str = "the #[k::init] has no main parameter (none is marked #[k::config_var(main)] or read in the computation cell)";

/// Each configuration variable of `pattern`, an assembled `initGeneratedTopCell`, by name without
/// `$` in name order, with its value unboxed ([`unboxed_configuration_value`]).
fn configuration_bindings<'p>(
    values: &ValueIndex,
    pattern: &'p Pattern,
) -> Vec<(String, &'p Pattern)> {
    let Pattern::Application { arguments, .. } = pattern else {
        return Vec::new();
    };
    let Some(entries) = arguments
        .first()
        .and_then(|map| values.collection_items(map, krs_ir::BuiltinSort::Map))
    else {
        return Vec::new();
    };
    let mut bindings = entries
        .iter()
        .filter_map(|entry| {
            let [key, value] = entry.as_slice() else {
                return None;
            };
            let Pattern::DomainValue { value: name, .. } = values::strip_injections(key) else {
                return None;
            };
            let name = name.as_utf8().ok()?.strip_prefix('$')?.to_owned();
            Some((name, unboxed_configuration_value(value)))
        })
        .collect::<Vec<_>>();
    bindings.sort_by(|left, right| left.0.cmp(&right.0));
    bindings
}

/// The value of an `initGeneratedTopCell` map entry: the map holds each value boxed as one
/// `KItem`, `#KConfigValue(V ~> .K)`, and `V` is the sequence's one item.
fn unboxed_configuration_value(boxed: &Pattern) -> &Pattern {
    let box_symbol = k_rust::kompile::encode_kore_label(&k_rust::kast::Label::new("#KConfigValue"));
    let Pattern::Application { symbol, arguments } = boxed else {
        return boxed;
    };
    let [sequence] = arguments.as_slice() else {
        return boxed;
    };
    if symbol.name != box_symbol.name {
        return boxed;
    }
    match sequence {
        Pattern::Application { symbol, arguments }
            if symbol.name == k_rust::names::WellKnownSymbol::KSeq.as_str() =>
        {
            match arguments.as_slice() {
                [item, Pattern::Application { symbol: tail, .. }]
                    if tail.name == k_rust::names::WellKnownSymbol::DotK.as_str() =>
                {
                    item
                }
                _ => sequence,
            }
        }
        _ => sequence,
    }
}

/// A sentence kind with its article, as a refusal names it.
const fn kind_phrase(kind: RuleKind) -> &'static str {
    match kind {
        RuleKind::Equation => "a function equation",
        RuleKind::Simplification => "a simplification",
        RuleKind::Definedness => "a definedness (`#Ceil`) equation",
        RuleKind::Rule => "a rewrite rule",
    }
}

fn write_unknown_item(
    formatter: &mut fmt::Formatter<'_>,
    requested: &str,
    kinds: &[RuleKind],
    unknown_crate: Option<&UnknownCrate>,
    suggestions: &[String],
) -> fmt::Result {
    if kinds.is_empty() {
        write!(
            formatter,
            "no rewrite rule is written by KRS item `{requested}`: no sentence of the definition is the item's"
        )?;
        match unknown_crate {
            Some(UnknownCrate::Unrecorded(krate)) => write!(
                formatter,
                ", and the definition records no package by the name `{krate}`: a dependency's item is named by the crate name of its library, never by a name a depending package's manifest renames it to"
            )?,
            Some(UnknownCrate::PackageName(krate)) => write!(
                formatter,
                ", and `{package}` is the package name of a dependency whose `[lib]` section names its library `{krate}`: a dependency's item is named by the crate name of its library, `{krate}`",
                package = requested.split_once("::").map_or(requested, |(first, _)| first)
            )?,
            Some(UnknownCrate::NoItem(krate)) => write!(
                formatter,
                ", and no item of the package `{krate}` writes a rule or an equation of the definition"
            )?,
            Some(UnknownCrate::Root(name)) => write!(
                formatter,
                ", and `{name}` names the root package, whose items are named `crate::` and their path"
            )?,
            None => formatter.write_str(
                " (an item is named by its Rust path: `crate::` and its path in the root package, or a dependency's own crate name and its path there)",
            )?,
        }
        return match suggestions {
            [] => Ok(()),
            [one] => write!(formatter, "; did you mean `{one}`?"),
            many => write!(
                formatter,
                "; did you mean one of {}?",
                many.iter()
                    .map(|name| format!("`{name}`"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        };
    }
    let kinds = kinds
        .iter()
        .map(|kind| kind_phrase(*kind))
        .collect::<Vec<_>>()
        .join(" or ");
    write!(
        formatter,
        "no rewrite rule is written by KRS item `{requested}`: each of its sentences is {kinds}, which a run applies without taking a step, so no step can stop at it"
    )
}

fn write_unknown_rule(
    formatter: &mut fmt::Formatter<'_>,
    requested: &str,
    sentence: Option<(&str, RuleKind)>,
    suggestion: Option<&str>,
) -> fmt::Result {
    write!(formatter, "no rewrite rule has label `{requested}`")?;
    if let Some((label, kind)) = sentence {
        let kind = kind_phrase(kind);
        write!(
            formatter,
            ": `{label}` is {kind}, which a run applies without taking a step, so no step can stop at it"
        )?;
    } else if let Some(suggestion) = suggestion {
        write!(formatter, "; did you mean `{suggestion}`?")?;
    }
    Ok(())
}

fn write_variables(
    formatter: &mut fmt::Formatter<'_>,
    heading: &str,
    variables: &[ConfigVariable],
) -> fmt::Result {
    write!(formatter, "; {heading}:")?;
    for variable in variables {
        write!(formatter, "\n  {variable}")?;
    }
    Ok(())
}

impl std::error::Error for ExecError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Compile(error) => Some(error),
            _ => None,
        }
    }
}

impl From<BackendError> for ExecError {
    fn from(error: BackendError) -> Self {
        Self::Backend(error.message().to_owned())
    }
}

/// The prints [`Semantics::unparse_program`] chooses among, by whether they reverse aliases and
/// how they spell user lists: through the aliases, unreversed, and unreversed in K's spelling.
const PROGRAM_PRINTS: [(bool, ListSpelling); 3] = [
    (true, ListSpelling::Program),
    (false, ListSpelling::Program),
    (false, ListSpelling::K),
];

/// One compiled definition, ready to parse, configure, run, search, and prove.
pub struct Semantics {
    backend: Backend,
    /// The sort hooks of `backend`'s definition, by KAST sort name, with which its results are
    /// converted to KAST (`result_sort_hooks`).
    sort_hooks: HashMap<String, String>,
    unparser: Arc<krs_unparse::Unparser>,
    configuration: Configuration,
    values: Arc<ValueIndex>,
    /// The typed cells configuration variables fill, which [`Self::configure`] checks.
    cell_types: cell_types::CellTypes,
    frontend_definition: NativeDefinition,
    main_module: String,
    definition_kore: String,
    provenance: SentenceProvenance,
    variables: Vec<ConfigVariable>,
    /// The `#[k::init]` parameters, in declaration order.
    parameters: Vec<Parameter>,
    claims: Vec<ClaimInfo>,
    user_sorts: Vec<String>,
    origins: origin::Origins,
    /// The rules and equations of `backend`'s definition, by `UNIQUE_ID`.
    rules: rules::Rules,
    console: console::ConsoleCells,
    /// The author spec modules (KF-041), by name.
    spec_modules: Vec<String>,
    /// The Definition IR, kept to compile a spec module's proof definition on demand.
    spec_definition: Option<Box<DefinitionIr>>,
    /// Compiled spec-module proof definitions, by spec module.
    spec_provers: BTreeMap<String, SpecProver>,
    /// The main cell's K name ([`Self::main_cell`]).
    main_cell: Option<String>,
    /// The printed texts [`Self::read_back`] read, by grammar, cell, sort and text.
    print_reads: BTreeMap<read_back::ReadKey, read_back::Read>,
    /// The solver options of every backend of these semantics ([`Self::solver`]).
    solver: BackendOptions,
    /// The execute requests runs sent the backend ([`Self::execute_requests`]).
    execute_requests: u64,
    /// The grammar text applying a function evaluated in one instance is read back with
    /// ([`instance_text`]), built on first use.
    authored_parser: instance_text::AuthoredParser,
}

/// One author spec module's compiled proof definition (KF-041).
struct SpecProver {
    backend: Backend,
    /// The sort hooks of `backend`'s definition (`result_sort_hooks`).
    sort_hooks: HashMap<String, String>,
    claims: Vec<ClaimInfo>,
}

impl Semantics {
    /// Compile Definition IR without authored source text.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Compile`] when the native frontend rejects the definition, or [`ExecError::Backend`] when the backend cannot load it.
    pub fn compile(definition: &DefinitionIr) -> Result<Self, ExecError> {
        Self::compile_with(definition, None, &mut Timings::disabled())
    }

    /// Compile Definition IR, positioning origins in the source text `sources` supplies, and recording `native.*` spans.
    ///
    /// # Errors
    ///
    /// Fails exactly when [`Self::compile`] fails.
    pub fn compile_with(
        definition: &DefinitionIr,
        sources: Option<SourceText>,
        timings: &mut Timings,
    ) -> Result<Self, ExecError> {
        let stage = CompiledStage::compile(definition, timings)?;
        Self::from_stage(definition, stage, sources, timings)
    }

    /// Build the semantics of `definition` from its compiled stage, which [`CompiledStage::compile`] made from the same Definition IR (or [`CompiledStage::decode`] read back), recording `exec.*` spans.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Backend`] when the backend, the program grammar, or the printer cannot load the stage.
    pub fn from_stage(
        definition: &DefinitionIr,
        stage: CompiledStage,
        sources: Option<SourceText>,
        timings: &mut Timings,
    ) -> Result<Self, ExecError> {
        Self::from_stage_with_solver(
            definition,
            stage,
            sources,
            BackendOptions::RESOURCE_BOUNDED,
            timings,
        )
    }

    /// [`Self::from_stage`] with the solver options `solver` for every backend of the semantics,
    /// the definition's and each author spec module's: [`Self::from_stage`] gives them
    /// [`BackendOptions::RESOURCE_BOUNDED`], under which whether a query is decided does not depend
    /// on the machine's speed or load.
    ///
    /// # Errors
    ///
    /// Fails exactly when [`Self::from_stage`] fails.
    pub fn from_stage_with_solver(
        definition: &DefinitionIr,
        stage: CompiledStage,
        sources: Option<SourceText>,
        solver: BackendOptions,
        timings: &mut Timings,
    ) -> Result<Self, ExecError> {
        let CompiledStage {
            definition_kore,
            syntax_definition_kore,
            macros_kore,
            provenance: sentence_provenance,
            frontend_definition,
            source_table: _,
            configuration_variables,
        } = stage;

        let main_module = frontend_definition.main_module.clone();
        let declared_variables = configuration_variables.clone();
        let mut configuration = timings.try_span("exec.configuration", |_| {
            Configuration::new(&frontend_definition, configuration_variables)
                .map_err(|error| ExecError::Backend(error.to_string()))
        })?;
        let mut backend = timings.try_span("exec.backend", |_| {
            Backend::new(&definition_kore, main_module.clone(), solver).map_err(ExecError::from)
        })?;
        let sort_hooks = result_sort_hooks(&mut backend)?;
        let (values, cell_types) = timings.try_span("exec.values", |_| {
            let backend_definition = backend
                .select_definition(None)
                .map_err(|error| ExecError::Backend(error.to_string()))?;
            let values = ValueIndex::new(definition, &backend_definition, &sort_hooks);
            let cell_types = cell_types::CellTypes::new(definition, &backend_definition, &values);
            Ok::<_, ExecError>((Arc::new(values), cell_types))
        })?;
        let parameters = inputs::parameters(definition, &values, &declared_variables);
        let variables = config_variables(&declared_variables, &parameters);
        // The printer reverses the alias clauses `reversal` judges by the definition's reading
        // of their tokens' values, so it is built after the values.
        let unparser = timings.try_span("exec.unparser", |_| {
            let unparser = krs_unparse::Unparser::from_kore(&syntax_definition_kore, &macros_kore)
                .map_err(|error| ExecError::Backend(error.to_string()))?
                .with_program_grammar(&frontend_definition);
            let reversed = reversal::reversed(definition, &unparser, &mut configuration, &values)
                .map_err(|error| {
                    ExecError::Backend(format!(
                        "the program grammar, which judges the aliases printing reverses, cannot be built: {error}"
                    ))
                })?;
            Ok::<_, ExecError>(unparser.reversing_only(|label| reversed.contains(label)))
        })?;
        let user_sorts = user_sorts(definition, &frontend_definition);
        let console = console::ConsoleCells::of(definition);
        let mut origins = origin::Origins::new(sources);
        let claims = claims::catalog(
            &definition_kore,
            &main_module,
            &sentence_provenance,
            &mut origins,
        )?;
        let spec_modules = definition
            .modules()
            .iter()
            .filter(|module| module.is_spec())
            .map(|module| module.id().as_str().to_owned())
            .collect::<Vec<_>>();
        let spec_definition = (!spec_modules.is_empty()).then(|| Box::new(definition.clone()));
        let main_cell = main_cell_name(definition);
        let rules = rules::Rules::new(&backend, &main_module, definition, |id| {
            sentence_provenance.get(id)
        })?;
        Ok(Self {
            backend,
            sort_hooks,
            unparser: Arc::new(unparser),
            configuration,
            values,
            cell_types,
            frontend_definition,
            main_module,
            definition_kore,
            provenance: sentence_provenance,
            variables,
            parameters,
            claims,
            user_sorts,
            origins,
            rules,
            console,
            spec_modules,
            spec_definition,
            spec_provers: BTreeMap::new(),
            main_cell,
            print_reads: BTreeMap::new(),
            solver,
            execute_requests: 0,
            authored_parser: None,
        })
    }

    /// The solver options of every backend of these semantics.
    #[must_use]
    pub const fn solver(&self) -> BackendOptions {
        self.solver
    }

    /// The author spec modules (KF-041), by name.
    #[must_use]
    pub fn spec_modules(&self) -> &[String] {
        &self.spec_modules
    }

    /// The claims of one author spec module's proof definition, compiling it on first use.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::UnknownSpecModule`], or the compile or backend error.
    pub fn spec_claims(&mut self, module: &str) -> Result<&[ClaimInfo], ExecError> {
        Ok(&self.spec_prover(module)?.claims)
    }

    /// Load one author spec module's compiled proof definition, which [`SpecStage::compile`] made from this Definition IR (or [`SpecStage::decode`] read back); a later proof of that module uses it instead of compiling.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::UnknownSpecModule`] when the stage is not of one of [`Self::spec_modules`], or [`ExecError::Backend`] when the backend cannot load it.
    pub fn load_spec_stage(&mut self, stage: SpecStage) -> Result<(), ExecError> {
        if !self.spec_modules.contains(&stage.module) {
            return Err(self.unknown_spec_module(&stage.module));
        }
        let mut backend = Backend::new(&stage.definition_kore, stage.module.clone(), self.solver)?;
        let sort_hooks = result_sort_hooks(&mut backend)?;
        let claims =
            claims::spec_catalog(&stage.definition_kore, &stage.provenance, &mut self.origins)?;
        self.spec_provers.insert(
            stage.module,
            SpecProver {
                backend,
                sort_hooks,
                claims,
            },
        );
        Ok(())
    }

    fn unknown_spec_module(&self, module: &str) -> ExecError {
        ExecError::UnknownSpecModule {
            requested: Some(module.to_owned()),
            modules: self.spec_modules.clone(),
            generated: claims::spec_module(&self.main_module),
        }
    }

    fn spec_prover(&mut self, module: &str) -> Result<&mut SpecProver, ExecError> {
        if !self.spec_provers.contains_key(module) {
            let definition = self
                .spec_definition
                .as_deref()
                .filter(|_| self.spec_modules.iter().any(|name| name == module))
                .ok_or_else(|| self.unknown_spec_module(module))?;
            let stage = SpecStage::compile(definition, module, &mut Timings::disabled())?;
            self.load_spec_stage(stage)?;
        }
        Ok(self
            .spec_provers
            .get_mut(module)
            .expect("the spec prover was just loaded"))
    }

    /// The compiled KORE definition text.
    #[must_use]
    pub fn definition_kore(&self) -> &str {
        &self.definition_kore
    }

    /// The main module's name.
    #[must_use]
    pub fn main_module(&self) -> &str {
        &self.main_module
    }

    /// The prepared frontend definition the program grammar was built from.
    #[must_use]
    pub const fn frontend_definition(&self) -> &NativeDefinition {
        &self.frontend_definition
    }

    /// The surface parsing context, for callers that parse cell expectations.
    pub const fn configuration_mut(&mut self) -> &mut Configuration {
        &mut self.configuration
    }

    /// The loaded backend, for callers that issue raw k-rust requests.
    pub const fn backend_mut(&mut self) -> &mut Backend {
        &mut self.backend
    }

    /// How many execute requests [`Self::run`] and [`Self::other_ends`] sent the backend so far.
    ///
    /// A run sends one, whatever its stop criterion's count, and one more to check its end
    /// where [`RunOptions::check_ends`] asks; a run whose end holds a term with no value sends
    /// one more for each earlier state it follows the path again to. [`Self::other_ends`] sends
    /// one.
    #[must_use]
    pub const fn execute_requests(&self) -> u64 {
        self.execute_requests
    }

    /// Send `request` to the backend, counted ([`Self::execute_requests`]), with the stop
    /// condition `oracle` asks when there is one; `offset` is the steps the run took before the
    /// request's start, which a refusal's step count includes.
    fn execute(
        &mut self,
        request: ExecuteRequest,
        oracle: Option<&mut ConditionOracle<'_>>,
        offset: u64,
    ) -> Result<KoreExecutionResult, ExecError> {
        self.execute_requests = self.execute_requests.saturating_add(1);
        let Some(oracle) = oracle else {
            return Ok(self.backend.execute_kore(request)?);
        };
        match self.backend.execute_kore_with_condition(request, oracle) {
            Ok(result) => Ok(result),
            Err(error) if error.kind() == Some(BackendErrorKind::StopConditionRefused) => {
                Err(match oracle.refusal.take() {
                    Some(refusal) => ExecError::StopCondition {
                        rule: self
                            .rules
                            .stop_name(&refusal.rule_id)
                            .unwrap_or(refusal.rule_id),
                        steps: refusal.depth.saturating_add(offset),
                        reason: refusal.reason,
                    },
                    None => ExecError::Backend(error.to_string()),
                })
            }
            Err(error) => Err(error.into()),
        }
    }

    /// The observer and the resolved stop condition of a run under `criterion`, when it has a
    /// condition: `observer` is the definition it is evaluated in.
    fn condition_of<'o>(
        &self,
        criterion: &StopCriterion,
        observer: Option<&'o mut Self>,
    ) -> Result<Option<(ResolvedCondition, &'o mut Self)>, ExecError> {
        let Some(when) = criterion.when() else {
            return Ok(None);
        };
        let Some(observer) = observer else {
            return Err(ExecError::StopWhen(format!(
                "the stop condition `{}` is evaluated in an observer definition, and none was given",
                when.function
            )));
        };
        let resolved = self.stop_condition(observer, when)?;
        Ok(Some((resolved, observer)))
    }

    /// What this build supports. Every route of this crate executes, searches, and proves; SMT needs the `z3-inference` feature.
    #[must_use]
    pub fn capabilities(&self) -> Capabilities {
        let backend = self.backend.capabilities();
        Capabilities {
            execute: backend.execution,
            search: backend.search,
            prove: backend.proving,
            smt: backend.smt,
        }
    }

    /// The configuration variables, the main parameter's first, then by K name.
    #[must_use]
    pub fn variables(&self) -> &[ConfigVariable] {
        &self.variables
    }

    /// The `#[k::init]` parameters, the definition's inputs, in declaration order.
    #[must_use]
    pub fn parameters(&self) -> &[Parameter] {
        &self.parameters
    }

    /// The main parameter, which a program file binds; `None` when the `#[k::init]` marks none
    /// and its computation cell reads none.
    #[must_use]
    pub fn main_parameter(&self) -> Option<&Parameter> {
        self.parameters.iter().find(|parameter| parameter.main)
    }

    /// The main parameter, for a front end that was given a program file and checks it before
    /// reading it.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::StrayProgram`], listing every parameter, when there is none.
    pub fn program_parameter(&self) -> Result<&Parameter, ExecError> {
        self.main_parameter()
            .ok_or_else(|| ExecError::StrayProgram {
                parameters: self.parameters.clone(),
            })
    }

    /// What the program file `name`, whose bytes are `bytes`, binds to the main parameter: the
    /// bytes, unchanged, where the parameter's type is exactly `Bytes`
    /// ([`Parameter::reads_file_bytes`]), and the file's text, parsed at the parameter's sort as
    /// [`Self::configure`] parses [`ConfigInputs::program`], otherwise.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::StrayProgram`] when there is no main parameter, and
    /// [`ExecError::ProgramNotText`] when the parameter reads text and `bytes` are not UTF-8.
    pub fn program_file(&self, name: &str, bytes: Vec<u8>) -> Result<ProgramFile, ExecError> {
        let main = self.program_parameter()?;
        if main.reads_file_bytes() {
            return Ok(ProgramFile::Bytes {
                parameter: main.name.clone(),
                value: Value::Bytes(bytes),
            });
        }
        let text = String::from_utf8(bytes).map_err(|_| ExecError::ProgramNotText {
            file: name.to_owned(),
            parameter: Box::new(main.clone()),
        })?;
        Ok(ProgramFile::Text(ProgramInput {
            name: name.to_owned(),
            text,
        }))
    }

    /// The parameter `written` names: its Rust name (`env`) or its configuration variable's K
    /// name, with or without `$` (`ENV`, `$ENV`).
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::UnknownVariable`], or [`ExecError::StreamInput`] for a console
    /// stream the definition declares but no parameter does.
    pub fn parameter(&self, written: &str) -> Result<&Parameter, ExecError> {
        let variable = self.resolve_variable(written)?;
        self.parameters
            .iter()
            .find(|parameter| parameter.variable == variable.name)
            .ok_or_else(|| ExecError::StreamInput {
                variable: variable.name.clone(),
            })
    }

    /// The value `document` writes for the input `parameter` (its Rust or K name), decoded at
    /// the parameter's declared type in the typed encoding ([`inputs`]): [`ConfigValue::Text`]
    /// or [`ConfigValue::TextFile`] for `$text` or `$text-file`, which [`Self::configure`]
    /// parses at the parameter's sort, and [`ConfigValue::Value`] otherwise. `files` reads the
    /// files the document names.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::UnknownVariable`] for an unknown input, [`ExecError::StreamInput`]
    /// for a console stream, or [`ExecError::Input`] naming the parameter, its declared type,
    /// the position in the document and the reason.
    pub fn decode_input(
        &self,
        parameter: &str,
        document: &serde_json::Value,
        files: &mut dyn InputFiles,
    ) -> Result<ConfigValue, ExecError> {
        self.decode_input_in(parameter, document, None, files)
    }

    /// [`Self::decode_input`] of a document written in the data file `from` (a resolved name
    /// `files` returned), which its paths are relative to, or in the top document (`None`).
    fn decode_input_in(
        &self,
        parameter: &str,
        document: &serde_json::Value,
        from: Option<&str>,
        files: &mut dyn InputFiles,
    ) -> Result<ConfigValue, ExecError> {
        let parameter = self.parameter(parameter)?;
        inputs::decode(&self.values, files, from, document, &parameter.ty)
            .map(ConfigValue::from)
            .map_err(|refusal| {
                ExecError::Input(InputError {
                    parameter: Some(parameter.name.clone()),
                    declared: Some(parameter.ty.to_string()),
                    position: refusal.position,
                    message: refusal.message,
                })
            })
    }

    /// The configuration variable (its K name, without `$`) and the KAST term that `value`
    /// binds for the input `parameter`, for a front end that assembles configurations with its
    /// own grammar of the same definition: the term this crate's own [`Self::configure`] binds.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::UnknownVariable`], [`ExecError::StreamInput`], or
    /// [`ExecError::Value`] for a value that is no term of the definition.
    pub fn input_term(
        &self,
        parameter: &str,
        value: &Value,
    ) -> Result<(String, k_rust::kast::Term), ExecError> {
        let parameter = self.parameter(parameter)?;
        let term = self
            .values
            .to_kast(value)
            .map_err(|error| ExecError::Value {
                variable: parameter.variable.clone(),
                error,
            })?;
        Ok((parameter.variable.clone(), term))
    }

    /// The inputs of `case`, each decoded at its parameter's declared type
    /// ([`Self::decode_input`]), with `program` (FILE) bound to the main parameter; `files`
    /// reads the files the case names, relative to the document the case is written in
    /// ([`Case::file`]).
    ///
    /// # Errors
    ///
    /// Fails as [`Self::decode_input`] does, at the first input that fails, in name order.
    pub fn case_inputs(
        &self,
        case: &Case,
        program: Option<ProgramInput>,
        files: &mut dyn InputFiles,
    ) -> Result<ConfigInputs, ExecError> {
        let variables = case
            .inputs
            .iter()
            .map(|(name, document)| {
                let value = self.decode_input_in(name, document, case.file.as_deref(), files)?;
                Ok((name.clone(), value))
            })
            .collect::<Result<_, ExecError>>()?;
        Ok(ConfigInputs {
            program,
            variables,
            stdin: None,
        })
    }

    /// The expectation an `expect` table states ([`inputs`], "Expectations"), read against the
    /// definition: its end as [`Self::read_end_in`] reads an end document, never `depth-bound`
    /// ([`ends`], "Results"), its file paths
    /// relative to the data file `from` (a resolved name `files` returned) or the top document
    /// (`None`), its `compare` narrowing, and its `views` and `observer` as the document names
    /// them, which the caller resolves in the observer it names
    /// ([`Expectation::comparison`]). It is refused here, before the case runs, for any cell it
    /// is compared on that it does not state, as every comparison of it would be.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Case`] naming the position (`expect.cells.pc`) and the reason.
    pub fn expectation(
        &self,
        document: &serde_json::Value,
        from: Option<&str>,
        files: &mut dyn InputFiles,
    ) -> Result<Expectation, ExecError> {
        let refuse = |position: &str, message: &str| {
            ExecError::Case(if position.is_empty() {
                format!("`expect`: {message}")
            } else {
                format!("`expect.{position}`: {message}")
            })
        };
        let serde_json::Value::Object(table) = document else {
            return Err(refuse(
                "",
                "the expected end is a table of `halt`, `rule`, `cells`, `compare`, `views` and `observer`",
            ));
        };
        let mut end_document = table.clone();
        let compare = match end_document.remove("compare") {
            None => None,
            Some(serde_json::Value::Array(paths)) => Some(
                paths
                    .iter()
                    .map(|path| path.as_str().map(str::to_owned))
                    .collect::<Option<Vec<_>>>()
                    .ok_or_else(|| {
                        refuse(
                            "compare",
                            "`compare` is an array of cell paths, each a string",
                        )
                    })?,
            ),
            Some(_) => {
                return Err(refuse(
                    "compare",
                    "`compare` is an array of cell paths, each a string",
                ));
            }
        };
        let (views, observer) = expectation_views(&mut end_document)
            .map_err(|(position, message)| refuse(&position, message))?;
        if let Some(key) = end_document
            .keys()
            .find(|key| !matches!(key.as_str(), "halt" | "rule" | "cells"))
        {
            return Err(refuse(
                key,
                "an expected end holds `halt`, `rule`, `cells`, `compare`, `views` and `observer` only",
            ));
        }
        if end_document.get("halt").and_then(serde_json::Value::as_str)
            == Some(Halt::DepthBound.as_str())
        {
            return Err(refuse(
                "halt",
                &format!("{DEPTH_BOUND_REFUSAL}{DEPTH_BOUND_GUIDANCE}"),
            ));
        }
        let end = self
            .read_end_in(&serde_json::Value::Object(end_document), from, files)
            .map_err(|error| match error {
                EndError::Document { position, message } => refuse(&position, &message),
                EndError::UnknownCell { .. } => refuse("cells", &error.to_string()),
                other => refuse("", &other.to_string()),
            })?;
        let comparison = Comparison {
            compare,
            ..Comparison::default()
        };
        self.check_stated(&comparison, &end, "expected")
            .map_err(|error| match &error {
                EndError::UnknownCell { .. }
                | EndError::Unobservable { .. }
                | EndError::UncomparedKey { .. } => refuse("compare", &error.to_string()),
                _ => refuse("cells", &error.to_string()),
            })?;
        Ok(Expectation {
            end,
            comparison,
            views,
            observer,
        })
    }

    /// The rewrite rules the stop name `written` selects, exactly as a run's stop selects them
    /// ([`StopRules`]: a name with `::` by KRS item, `crate::` for the root package and a
    /// dependency's crate name for its items, any other by K label), each as its `UNIQUE_ID` and
    /// its label (`None` for a rule with none), in identity order: for a front end that hands
    /// the stop to another engine by label (`krs kink`). An item selects every rewrite rule it
    /// lowers to, those K generates from it (a context's heat and cool rules) included.
    ///
    /// # Errors
    ///
    /// The error a run's stop refuses `written` with: [`ExecError::UnknownRule`],
    /// [`ExecError::AmbiguousRule`], [`ExecError::UnknownItem`] or
    /// [`ExecError::AmbiguousItem`].
    pub fn stop_rules(&self, written: &str) -> Result<Vec<(String, Option<String>)>, ExecError> {
        Ok(self
            .rules
            .resolve_stop(written)?
            .into_iter()
            .map(|id| {
                let label = self.rules.get(&id).and_then(|rule| rule.label.clone());
                (id, label)
            })
            .collect())
    }

    /// The claims of the generated spec module, in label order.
    #[must_use]
    pub fn claims(&self) -> &[ClaimInfo] {
        &self.claims
    }

    /// Whether the definition declares stream cells (`$STDIN` or `$IO`).
    #[must_use]
    pub fn has_stream_cells(&self) -> bool {
        self.variables
            .iter()
            .any(|variable| matches!(variable.name.as_str(), "STDIN" | "IO"))
    }

    /// Parse program text at `sort` (default: the main parameter's sort) with the program grammar.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::UnknownSort`], [`ExecError::NoProgramSort`], or [`ExecError::Parse`].
    pub fn parse(&mut self, sort: Option<&str>, input: &ProgramInput) -> Result<Term, ExecError> {
        let sort = self.program_sort(sort)?;
        let parsed = self
            .configuration
            .parse_program(&sort, &input.text)
            .map_err(|error| parse_error(input, &sort, error.as_ref()))?;
        let kast = parsed.term().clone();
        let kore = self
            .configuration
            .parse_program_kore(&sort, &input.text)
            .map_err(|error| ExecError::Parse {
                input: input.name.clone(),
                sort: sort.to_string(),
                message: error.to_string(),
            })?;
        Ok(Term::new(kore, kast))
    }

    /// Parse program text as [`Self::parse`] does and print it through the program grammar, as `kast --output program` does.
    ///
    /// Macros print as parsed, and the main module's aliases are reversed where the print reads
    /// back: a reversal can put a child under a production that binds tighter than the child,
    /// where no bracket the definition declares groups it. So the print through the aliases is
    /// read back ([`Self::read_back_program`]'s rule); where it does not read back as the
    /// program, the program prints unreversed, which the parser read without such a bracket.
    /// Where neither print reads back, the unreversed print is printed with what it says of
    /// itself (a child printed bare, [`krs_unparse::Warning::Ungrouped`]). A print that reads
    /// back says nothing of a bracket it lacks: the bracket algorithm can ask for one the text
    /// does not need.
    ///
    /// # Errors
    ///
    /// Fails exactly when [`Self::parse`] fails.
    pub fn unparse_program(
        &mut self,
        sort: Option<&str>,
        input: &ProgramInput,
        color: bool,
    ) -> Result<Printed, ExecError> {
        let (presented, expanded) = self.program_forms(sort, input)?;
        let print = |printer: &krs_unparse::Unparser,
                     reverse_aliases: bool,
                     list_spelling: ListSpelling,
                     color: bool| {
            printer.print_kore(
                &presented,
                &krs_unparse::Options {
                    reverse_aliases,
                    list_spelling,
                    ..krs_unparse::Options::new(krs_unparse::Mode::Program).with_color(color)
                },
            )
        };
        let prints = PROGRAM_PRINTS.map(|(reverse_aliases, list_spelling)| {
            print(&self.unparser, reverse_aliases, list_spelling, false)
        });
        let (reverse_aliases, list_spelling, printed) = self.program_print(sort, &expanded, prints);
        // The prints are judged without colour, which no grammar reads.
        if !color {
            return Ok(printed);
        }
        Ok(Printed {
            warnings: printed.warnings,
            ..print(&self.unparser, reverse_aliases, list_spelling, true)
        })
    }

    /// [`Self::unparse_program`], printed by `printer` (such as one that reverses only some of
    /// the definition's aliases) and without colour.
    ///
    /// # Errors
    ///
    /// Fails exactly when [`Self::parse`] fails.
    pub fn unparse_program_by(
        &mut self,
        printer: &krs_unparse::Unparser,
        sort: Option<&str>,
        input: &ProgramInput,
    ) -> Result<Printed, ExecError> {
        let (presented, expanded) = self.program_forms(sort, input)?;
        let prints = PROGRAM_PRINTS.map(|(reverse_aliases, list_spelling)| {
            printer.print_kore(
                &presented,
                &krs_unparse::Options {
                    reverse_aliases,
                    list_spelling,
                    ..krs_unparse::Options::new(krs_unparse::Mode::Program)
                },
            )
        });
        Ok(self.program_print(sort, &expanded, prints).2)
    }

    /// Of `[reversed, unreversed, stated]`, the prints of a program at `sort` whose expansion is
    /// `expanded` ([`PROGRAM_PRINTS`]), the one [`Self::unparse_program`] prints, beside whether
    /// it reverses aliases and how it spells user lists: `reversed` where it reads back, else
    /// `unreversed` where it reads back. Where neither does, and `unreversed` spells its lists
    /// without a stated fallback, `stated`, which says so ([`krs_unparse::Warning::EmptyList`]):
    /// the program spelling of a list is judged on the grammar before the text exists, and is
    /// no program text where the grammar reads that text otherwise. Else `unreversed`, with what
    /// it says of itself.
    fn program_print(
        &mut self,
        sort: Option<&str>,
        expanded: &Pattern,
        [reversed, unreversed, stated]: [Printed; 3],
    ) -> (bool, ListSpelling, Printed) {
        let reads = |semantics: &mut Self, printed: &Printed| {
            semantics.program_read_back(sort, expanded, printed) == ReadBack::Reads
        };
        let without_ungrouped = |mut printed: Printed| {
            printed
                .warnings
                .retain(|warning| !matches!(warning, krs_unparse::Warning::Ungrouped(_)));
            printed
        };
        if reads(self, &reversed) {
            return (true, ListSpelling::Program, without_ungrouped(reversed));
        }
        if reversed.text != unreversed.text && reads(self, &unreversed) {
            return (false, ListSpelling::Program, without_ungrouped(unreversed));
        }
        let states_lists = unreversed
            .warnings
            .iter()
            .any(|warning| matches!(warning, krs_unparse::Warning::EmptyList(_)));
        if !states_lists && stated.text != unreversed.text {
            return (false, ListSpelling::K, stated);
        }
        (false, ListSpelling::Program, unreversed)
    }

    /// The two KORE forms of one reading of the program `input` at `sort` (by default the main
    /// parameter's):
    /// as parsed, which [`Self::unparse_program`] prints, and expanded
    /// ([`configuration::Configuration::parse_program_forms`]).
    pub(crate) fn program_forms(
        &mut self,
        sort: Option<&str>,
        input: &ProgramInput,
    ) -> Result<(Pattern, Pattern), ExecError> {
        let sort = self.program_sort(sort)?;
        self.configuration
            .parse_program_forms(&sort, &input.text)
            .map_err(|error| parse_error(input, &sort, error.as_ref()))
    }

    fn program_sort(&self, sort: Option<&str>) -> Result<KastSort, ExecError> {
        match sort {
            Some(name) => {
                let sorts = self.configuration.program_sorts();
                if !sorts.contains(name) {
                    return Err(ExecError::UnknownSort {
                        sort: name.to_owned(),
                        sorts: self
                            .user_sorts
                            .iter()
                            .filter(|sort| sorts.contains(*sort))
                            .cloned()
                            .collect(),
                    });
                }
                Ok(KastSort::new(name))
            }
            None => self
                .main_parameter()
                .and_then(|main| self.configuration.variables().get(&main.variable))
                .cloned()
                .ok_or(ExecError::NoProgramSort),
        }
    }

    /// Build the initial configuration from FILE and the bindings by name.
    ///
    /// FILE binds the main parameter ([`Self::main_parameter`]): parsed as a program, with the
    /// syntax module at the start position of its sort, where that parameter is `$PGM`, and as
    /// `-c` text of the parameter otherwise. Any parameter, the main one included, may instead
    /// be bound by name.
    ///
    /// # Errors
    ///
    /// Returns a typed error for a FILE without a main parameter, an unbound main parameter, an
    /// unknown, duplicate, or missing variable, or text that does not parse.
    pub fn configure(&mut self, inputs: &ConfigInputs) -> Result<State, ExecError> {
        let mut program: Option<configuration::Binding> = None;
        let mut bound = BTreeMap::new();
        // Where each bound variable's text came from, for a parse error's message.
        let mut sources = BTreeMap::new();
        if let Some(file) = &inputs.program {
            let main = self.program_parameter()?.variable.clone();
            let binding = configuration::Binding::Text(file.text.clone());
            if main == "PGM" {
                program = Some(binding);
            } else {
                bound.insert(main.clone(), binding);
            }
            sources.insert(main, Source::file(file));
        }
        for (written, value) in &inputs.variables {
            let variable = self.resolve_variable(written)?;
            let (binding, source) = match value {
                ConfigValue::Text(text) => (
                    configuration::Binding::Text(text.clone()),
                    Source::option(written),
                ),
                ConfigValue::TextFile(file) => (
                    configuration::Binding::Text(file.text.clone()),
                    Source::file(file),
                ),
                ConfigValue::Value(value) => (
                    configuration::Binding::Term(self.values.to_kast(value).map_err(|error| {
                        ExecError::Value {
                            variable: variable.name.clone(),
                            error,
                        }
                    })?),
                    Source::option(written),
                ),
            };
            let twice = if variable.name == "PGM" {
                program.replace(binding).is_some()
            } else {
                bound.insert(variable.name.clone(), binding).is_some()
            };
            if twice {
                return Err(ExecError::DuplicateVariable(variable.clone()));
            }
            sources.insert(variable.name.clone(), source);
        }
        if let Some(main) = self.main_parameter()
            && !sources.contains_key(&main.variable)
        {
            return Err(ExecError::MissingProgram {
                parameter: main.clone(),
            });
        }
        let missing = self
            .variables
            .iter()
            .filter(|variable| {
                !matches!(variable.name.as_str(), "IO" | "STDIN")
                    && !sources.contains_key(&variable.name)
            })
            .cloned()
            .collect::<Vec<_>>();
        if !missing.is_empty() {
            return Err(ExecError::MissingVariables(missing));
        }
        let stdin = inputs
            .stdin
            .as_deref()
            .filter(|_| self.console.stdin)
            .map(console::buffered_input);
        let pattern =
            match self
                .configuration
                .assemble_pattern(program.as_ref(), &bound, stdin.as_deref())
            {
                Ok(pattern) => pattern,
                Err(error) => {
                    return Err(self.assembly_error(error, program.as_ref(), &bound, &sources));
                }
            };
        self.check_instance_functions(&pattern)?;
        self.check_cell_types(&pattern)?;
        Ok(State::new(pattern))
    }

    /// The initial configuration `state` ([`Self::configure`]) with the instances `case`'s
    /// `instances` table states ([`inputs`], "Instances"); `state` itself where the case states
    /// none. `files` reads the files the table's values name, relative to the document the case
    /// is written in ([`Case::file`]).
    ///
    /// Each stated cell replaces its start in the term the initializer builds, so a cell no
    /// instance states starts as the template says, evaluated under the case's inputs when the
    /// first state is simplified, as every other initializer is.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Case`] naming the position (`instances.harts.hart[1]`) for a table
    /// that is no statement of instances of this configuration ([`inputs`], "Instances"), and
    /// [`ExecError::Backend`] for a `state` that is no initial configuration or a definition
    /// whose initializers do not unfold.
    pub fn state_instances(
        &mut self,
        state: State,
        case: &Case,
        files: &mut dyn InputFiles,
    ) -> Result<State, ExecError> {
        let Some(document) = &case.instances else {
            return Ok(state);
        };
        if state.taken.is_some() {
            return Err(ExecError::Backend(
                "a case states the instances of an initial configuration, not of a state a run left off at".to_owned(),
            ));
        }
        let definition = self
            .backend
            .select_definition(None)
            .map_err(|error| ExecError::Backend(error.to_string()))?;
        let values = self.values.clone();
        let from = case.file.as_deref();
        let stated = inputs::read_instances(values.cells(), document, &mut |node, document, _| {
            self.stated_leaf(&definition, files, from, node, document)
        })
        .map_err(|error| ExecError::Case(format!("`{}`: {}", error.position, error.message)))?;
        let pattern = configuration::InstanceTerms::new(&definition, &state.pattern)
            .and_then(|terms| terms.configuration(&state.pattern, values.cells(), &stated))
            .map_err(|error| {
                ExecError::Backend(format!(
                    "the initial configuration cannot state the case's instances: {error}"
                ))
            })?;
        Ok(State::new(pattern))
    }

    /// The content `document` states of the leaf cell `node` in a case's `instances` table
    /// ([`inputs`], "Instances"): read at the cell's declared type as an input's value is, or
    /// parsed at its content sort as K text, typed at the position the cell holds it at, and
    /// checked against its element types; the error is the refusal's message.
    fn stated_leaf(
        &mut self,
        definition: &k_rust::k_rust_backend::definition::BackendDefinition,
        files: &mut dyn InputFiles,
        from: Option<&str>,
        node: &values::CellNode,
        document: &serde_json::Value,
    ) -> Result<inputs::StatedLeaf, String> {
        let ty = node
            .content
            .as_ref()
            .and_then(|(sort, arguments)| inputs::input_type(&self.values, sort, arguments))
            .unwrap_or_else(InputType::untyped);
        let content = match definition
            .symbols()
            .get(node.symbol.as_str())
            .map(|symbol| symbol.argument_sorts.as_slice())
        {
            Some([sort]) => match sort.node() {
                k_rust::k_rust_backend::term::SortNode::Application { name, arguments }
                    if arguments.is_empty() =>
                {
                    name.to_string()
                }
                _ => return Err(format!("the cell `{}` holds a parametric sort", node.field)),
            },
            _ => {
                return Err(format!(
                    "`{}` is no leaf cell of the definition",
                    node.field
                ));
            }
        };
        let sort = KastSort::new(krs_unparse::decode_kore(
            content.strip_prefix("Sort").unwrap_or(&content),
        ));
        let decoded =
            inputs::decode(&self.values, files, from, document, &ty).map_err(|refusal| {
                let at = if refusal.position.is_empty() {
                    String::new()
                } else {
                    format!("at `{}`: ", refusal.position)
                };
                format!("{at}{} (the cell's type is {ty})", refusal.message)
            })?;
        let term = match decoded {
            inputs::Decoded::Value(value) => {
                let term = self
                    .values
                    .to_kast(&value)
                    .map_err(|error| error.to_string())?;
                self.configuration
                    .typed_kore_at(&term, &sort)
                    .map_err(|error| error.to_string())?
            }
            inputs::Decoded::Text(text) => self.stated_text(node, &sort, &text)?,
            inputs::Decoded::TextFile(file) => self.stated_text(node, &sort, &file.text)?,
        };
        if let Some(decl) = self.values.instance_application(&term) {
            return Err(self
                .values
                .instance_function(&decl, "an input")
                .expect("an instance application applies an instance function"));
        }
        if let Some(mismatch) = self
            .cell_types
            .check_cell(&self.values, &node.symbol, &term)
        {
            let position = cell_types::describe(&mismatch.path, ToString::to_string);
            return Err(format!(
                "{position} has sort {}, which is not at most {}, the declared {} of `{}`",
                mismatch.sort, mismatch.expected, mismatch.declared, mismatch.parameter
            ));
        }
        let value = self
            .values
            .decode(&term)
            .ok()
            .filter(|value| is_data(&self.values, value));
        let shown = value
            .as_ref()
            .and_then(|value| encode(&self.values, value, &ty).ok())
            .map_or_else(|| term.to_string(), |document| canonical_text(&document));
        Ok(inputs::StatedLeaf { term, value, shown })
    }

    /// The K text `text` a case states of the leaf cell `node`, parsed at its content sort `sort`
    /// as a cell's printed content is; where no grammar parses it, a reading that applies a
    /// function evaluated in one instance of a Map collection with its authored arguments is
    /// refused with that reason, as an input's text is.
    fn stated_text(
        &mut self,
        node: &values::CellNode,
        sort: &KastSort,
        text: &str,
    ) -> Result<Pattern, String> {
        self.configuration
            .parse_cell_at(&node.field, sort, text)
            .map_err(
                |error| match self.instance_text_refusal(&node.field, sort, text) {
                    Some(ExecError::InstanceFunction { reason, .. }) => reason,
                    _ => error.to_string(),
                },
            )
    }

    /// The error of [`Self::configure`] for the assembler's `error`, given the program and the
    /// variables it bound and where each one's text came from: text that no grammar parses is
    /// refused with the reason where it applies a function evaluated in one instance of a Map
    /// collection with its authored arguments ([`instance_text`]).
    fn assembly_error(
        &mut self,
        error: configuration::AssemblyError,
        program: Option<&configuration::Binding>,
        bound: &BTreeMap<String, configuration::Binding>,
        sources: &BTreeMap<String, Source>,
    ) -> ExecError {
        match error {
            configuration::AssemblyError::Value { variable, error } => ExecError::Value {
                variable,
                error: ValueError::Unencodable(match error.as_ref() {
                    k_rust::kompile::ConfigurationError::ValueSort(mismatch) => format!(
                        "its sort {} is not at most the declared sort {}",
                        mismatch.actual, mismatch.declared
                    ),
                    error => error.to_string(),
                }),
            },
            configuration::AssemblyError::Configuration(error) => {
                let text = |name: &str| {
                    let binding = if name == "PGM" {
                        program
                    } else {
                        bound.get(name)
                    };
                    match binding {
                        Some(configuration::Binding::Text(text)) => Some(text.as_str()),
                        _ => None,
                    }
                };
                self.unparsed_instance_text(&error, text)
                    .unwrap_or_else(|| configuration_error(&error, sources, &self.variables))
            }
        }
    }

    /// Refuse a configuration variable's value in `pattern`, an assembled `initGeneratedTopCell`,
    /// that applies a function evaluated in one instance of a Map collection
    /// ([`ValueIndex::instance_function`]). A typed value is refused as it is decoded; text is
    /// read by the main module's grammar where the syntax module's does not read it, and that
    /// grammar holds such a function with its hidden key, so text spelling the key parses and is
    /// refused here, before the run, with the reason a typed value gets.
    fn check_instance_functions(&self, pattern: &Pattern) -> Result<(), ExecError> {
        for (variable, value) in configuration_bindings(&self.values, pattern) {
            if let Some(decl) = self.values.instance_application(value) {
                let reason = self
                    .values
                    .instance_function(&decl, "an input")
                    .expect("an instance application applies an instance function");
                return Err(ExecError::InstanceFunction { variable, reason });
            }
        }
        Ok(())
    }

    /// Check every configuration variable's value in `pattern`, an assembled
    /// `initGeneratedTopCell`, against the type the variable is declared with ([`cell_types`]).
    fn check_cell_types(&self, pattern: &Pattern) -> Result<(), ExecError> {
        let bindings = configuration_bindings(&self.values, pattern);
        // The prints' warnings are the mismatch's: what a printed part says it is not.
        let warnings = std::cell::RefCell::new(Vec::<String>::new());
        let print = |pattern: &Pattern| {
            let printed = self.unparser.print_kore(
                pattern,
                &krs_unparse::Options::new(krs_unparse::Mode::Pretty),
            );
            let mut warnings = warnings.borrow_mut();
            for warning in printed.warnings {
                let warning = warning.to_string();
                if !warnings.contains(&warning) {
                    warnings.push(warning);
                }
            }
            printed.text
        };
        for (variable, value) in bindings {
            if let Some(mismatch) = self.cell_types.check(&self.values, &variable, value) {
                let position = cell_types::describe(&mismatch.path, print);
                let element = print(mismatch.element);
                return Err(ExecError::CollectionElementSort(Box::new(
                    ElementSortMismatch {
                        variable,
                        parameter: mismatch.parameter,
                        declared: mismatch.declared,
                        position,
                        element,
                        sort: mismatch.sort,
                        expected: mismatch.expected,
                        warnings: warnings.take(),
                    },
                )));
            }
        }
        Ok(())
    }

    /// Assemble the initial configuration from surface text as [`Configuration::configure`] does,
    /// and refuse and check its variables as [`Self::configure`] does: text that applies a
    /// function evaluated in one instance of a Map collection, and the typed cells they fill.
    /// The JSON holds the pattern and each variable rendered on its own as KORE, for routes that
    /// pass a value to another tool.
    ///
    /// # Errors
    ///
    /// Returns the assembler's error, [`ExecError::InstanceFunction`], or
    /// [`ExecError::CollectionElementSort`].
    pub fn configure_surface(
        &mut self,
        variables: &serde_json::Map<String, serde_json::Value>,
    ) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
        let (pattern, configured) = match self.configuration.configure_pattern(variables) {
            Ok(configured) => configured,
            Err(error) => {
                let refusal = error
                    .downcast_ref::<k_rust::kompile::ConfigurationError>()
                    .and_then(|error| {
                        self.unparsed_instance_text(error, |name| {
                            variables.get(name).and_then(serde_json::Value::as_str)
                        })
                    });
                return Err(refusal.map_or(error, Into::into));
            }
        };
        self.check_instance_functions(&pattern)?;
        self.check_cell_types(&pattern)?;
        Ok(configured)
    }

    /// The refusal of a configuration variable's text that no grammar of the definition parses
    /// (`error`) where it applies a function evaluated in one instance of a Map collection with
    /// its authored arguments ([`instance_text`]); `text` gives the text bound to a variable by
    /// its K name without `$`.
    fn unparsed_instance_text<'t>(
        &mut self,
        error: &k_rust::kompile::ConfigurationError,
        text: impl Fn(&str) -> Option<&'t str>,
    ) -> Option<ExecError> {
        use k_rust::kompile::ConfigurationError as Error;
        let (variable, sort) = match error {
            Error::Program(_) => ("PGM", self.configuration.variables().get("PGM")?.clone()),
            Error::Parse { variable, sort, .. } => {
                (variable.strip_prefix('$').unwrap_or(variable), sort.clone())
            }
            _ => return None,
        };
        let text = text(variable)?;
        self.instance_text_refusal(variable, &sort, text)
    }

    /// The configuration variable `written` names: a parameter's Rust name, or a K name with or
    /// without `$`. A K name wins over a Rust name, which the IR keeps distinct from every
    /// other parameter's but not from another variable's K name.
    fn resolve_variable(&self, written: &str) -> Result<&ConfigVariable, ExecError> {
        let name = written.strip_prefix('$').unwrap_or(written);
        self.variables
            .iter()
            .find(|variable| variable.name == name)
            .or_else(|| {
                self.variables
                    .iter()
                    .find(|variable| !written.starts_with('$') && variable.parameter == name)
            })
            .ok_or_else(|| ExecError::UnknownVariable {
                name: written.to_owned(),
                variables: self.variables.clone(),
            })
    }

    /// Follow one path from `state`, with strategy `any`, as krun does.
    ///
    /// From the state a run that stopped before a rule left off at ([`RunReport::resume`]), the
    /// run's first step is that rule's, which its `steps`, trace, depth bound and coverage count
    /// ([`StopRules::before`]); a depth bound of 0 leaves it untaken, so the run ends where the
    /// stopped run did.
    ///
    /// Under a stop criterion with a count N ([`StopCriterion::Rules`]), the backend counts the
    /// arrivals at a stop along the path and ends it at the Nth, so the run is one request
    /// whatever N is: its `steps`, trace, logs, coverage and depth bound are the whole path's,
    /// as for a run to its first stop.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::UnknownRule`], [`ExecError::AmbiguousRule`],
    /// [`ExecError::UnknownItem`] or [`ExecError::AmbiguousItem`] when a stop names no rewrite
    /// rule, several labels by suffix, or items of several packages ([`StopRules`]),
    /// [`ExecError::Backend`] when the
    /// backend fails, [`ExecError::Undecided`] when the run reaches several states under
    /// conditions it cannot decide, or [`ExecError::Result`] when the backend returns several
    /// states under no condition, or none.
    pub fn run(&mut self, state: &State, options: RunOptions) -> Result<RunReport, ExecError> {
        self.run_observed(state, options, None)
    }

    /// [`Self::run`] under a criterion that may have a stop condition ([`StopWhen`]), evaluated
    /// in `observer`: the definition the condition names, or another [`Semantics`] of this
    /// definition when it names none (the run's own backend runs the path while the condition
    /// is asked). The run is still one request: the backend asks the condition at each arrival.
    ///
    /// # Errors
    ///
    /// Fails as [`Self::run`] does, and with [`ExecError::StopWhen`] for a condition that cannot
    /// be resolved or has no observer, and [`ExecError::StopCondition`] for a condition with no
    /// value at an arrival.
    pub fn run_observed(
        &mut self,
        state: &State,
        options: RunOptions,
        observer: Option<&mut Self>,
    ) -> Result<RunReport, ExecError> {
        let stops = self.stop_ids(&options.stop)?;
        let condition = self.condition_of(&options.stop, observer)?;
        let (resolved, observer) = match condition {
            Some((resolved, observer)) => (Some(resolved), Some(observer)),
            None => (None, None),
        };
        let mut oracle = match (&resolved, observer) {
            (Some(resolved), Some(observer)) => Some(ConditionOracle::new(
                ArrivalObservation::new(resolved, observer, options.condition_budget)?,
            )),
            _ => None,
        };
        let Some(taken) = &state.taken else {
            return self.run_from(&state.pattern, &options, &stops, None, oracle.as_mut());
        };
        // The bound left once the taken step is counted: `None` where the bound allows no step.
        let Some(depth) = options
            .depth
            .map_or(Some(None), |depth| depth.checked_sub(1).map(Some))
        else {
            // The bound allows no step, so not the one the stopped run left: the run ends where
            // that run did, having used nothing ([`RunReport::coverage`]).
            let untaken = RunOptions {
                depth: Some(0),
                trace: options.trace,
                ..RunOptions::default()
            };
            let mut report =
                self.run_from(&taken.before, &untaken, &StopIds::default(), None, None)?;
            report.coverage = options.coverage.map(|asked| Coverage {
                offered: asked.offered,
                rules: Vec::new(),
            });
            report.resume = Some(state.clone());
            return Ok(report);
        };
        let options = RunOptions { depth, ..options };
        self.run_from(
            &state.pattern,
            &options,
            &stops,
            Some(taken),
            oracle.as_mut(),
        )
    }

    /// Why the definition may end otherwise from `state` than at the end of `report`, the run
    /// from `state` under `options` ([`Self::run`]); `None` when that end is its only one within
    /// the run's depth bound and stop rules.
    ///
    /// A run follows one path, taking one successor of each state, so its end is every end only
    /// where no state before it has several successors and nothing the definition leaves open
    /// decided the path. The end may be otherwise:
    ///
    /// - where the run read a value the definition leaves open
    ///   ([`RunReport::implementation_chosen_values`], [`open_values`]): another implementation
    ///   of the definition may choose another value, and end elsewhere;
    /// - where a state of the path has several successors: another path goes on from another
    ///   one. The path is followed again from `state` under the same bound and stop rules with
    ///   every rule tried at each step (strategy `all`), ending at the first state with several
    ///   successors (k-rust's `stop_at_branch`, a `branch` leaf), which names it. A state of one
    ///   successor is stepped to it by either strategy, so where no state has several the path
    ///   followed again is the run's own, and its end the run's. The step a run resumed after a
    ///   stop before a rule takes first ([`StopRules::before`]) is that rule's, the one successor
    ///   of its state, so it chooses nothing.
    ///
    /// Under a stop criterion with a count N ([`StopCriterion::Rules`]) the path is followed
    /// again to its Nth arrival at a stop, the backend counting the arrivals as the run's did:
    /// one request, whatever N is. An arrival is a step by a stop rule that is its state's one
    /// successor, so it chooses nothing, and the path goes on past each one before the Nth.
    ///
    /// Two successors that are equal are still two, so the reason is conservative there.
    ///
    /// # Errors
    ///
    /// Fails as [`Self::run`] does.
    pub fn other_ends(
        &mut self,
        state: &State,
        options: &RunOptions,
        report: &RunReport,
    ) -> Result<Option<String>, ExecError> {
        self.other_ends_observed(state, options, report, None)
    }

    /// [`Self::other_ends`] of a run under a criterion that may have a stop condition, evaluated
    /// in `observer` as [`Self::run_observed`] evaluates it: the path is followed again under
    /// the same stop rules, count and condition.
    ///
    /// # Errors
    ///
    /// Fails as [`Self::run_observed`] does.
    pub fn other_ends_observed(
        &mut self,
        state: &State,
        options: &RunOptions,
        report: &RunReport,
        observer: Option<&mut Self>,
    ) -> Result<Option<String>, ExecError> {
        if let Some(reason) = open_values(&report.implementation_chosen_values) {
            return Ok(Some(format!("the run {reason}")));
        }
        let stops = self.stop_ids(&options.stop)?;
        let condition = self.condition_of(&options.stop, observer)?;
        let (resolved, observer) = match condition {
            Some((resolved, observer)) => (Some(resolved), Some(observer)),
            None => (None, None),
        };
        let mut oracle = match (&resolved, observer) {
            (Some(resolved), Some(observer)) => Some(ConditionOracle::new(
                ArrivalObservation::new(resolved, observer, options.condition_budget)?,
            )),
            _ => None,
        };
        self.branch_in_path(state, options.depth, &stops, oracle.as_mut())
    }

    /// Why a run from `state`, to its arrival at a stop of `stops` that `stops` counts to within
    /// `depth` steps, may end otherwise ([`Self::other_ends`]); `None` when no state of it has
    /// several successors.
    fn branch_in_path(
        &mut self,
        state: &State,
        depth: Option<u64>,
        stops: &StopIds,
        oracle: Option<&mut ConditionOracle<'_>>,
    ) -> Result<Option<String>, ExecError> {
        // The taken step counts as the run's first and takes one step of the bound.
        let (depth, taken) = match (&state.taken, depth) {
            (None, depth) => (depth, 0),
            (Some(_), None) => (None, 1),
            (Some(_), Some(depth)) => match depth.checked_sub(1) {
                Some(depth) => (Some(depth), 1),
                // The bound allows no step: the run took none, and chose none.
                None => return Ok(None),
            },
        };
        let mut request = run_request(
            &state.pattern,
            &RunOptions {
                depth,
                ..RunOptions::default()
            },
            stops,
        );
        request.strategy = ExecutionStrategy::All;
        request.stop_at_branch = true;
        let leaves = self.execute(request, oracle, taken)?.leaves;
        let Some(branch) = leaves
            .iter()
            .find(|leaf| leaf.reason == HaltReasonOutput::Branch)
        else {
            return Ok(None);
        };
        let after = branch.depth.saturating_add(taken);
        // A successor per candidate, and one more where none applies (the remainder); the
        // candidates are named once each, in order, since several can share a name.
        let candidates = branch.candidates.iter().flatten().collect::<Vec<_>>();
        let mut rules = Vec::<String>::new();
        for candidate in &candidates {
            let name = self
                .rules
                .stop_name(&candidate.unique_id)
                .or_else(|| candidate.label.clone())
                .unwrap_or_else(|| candidate.unique_id.clone());
            let name = format!("`{name}`");
            if !rules.contains(&name) {
                rules.push(name);
            }
        }
        let successors = match (candidates.len(), branch.remainder.is_some()) {
            (0, _) => "several successors".to_owned(),
            (count, false) => format!("{count} successors, by {}", rules.join(", ")),
            (count, true) => format!(
                "{} successors, by {} and one where none of them applies",
                count + 1,
                rules.join(", ")
            ),
        };
        Ok(Some(format!(
            "the run took one successor of the state after {after} step{}, which has {successors}, so another path may end otherwise",
            if after == 1 { "" } else { "s" }
        )))
    }

    /// A run from `start` ([`Self::run`]); `taken` is the step that leads to `start`, which the
    /// run counts as its first, after a stop before its rule.
    #[expect(
        clippy::too_many_lines,
        reason = "One run: the request, the path read, the proposal, the checks and the report."
    )]
    fn run_from(
        &mut self,
        start: &Pattern,
        options: &RunOptions,
        stops: &StopIds,
        taken: Option<&TakenStep>,
        mut oracle: Option<&mut ConditionOracle<'_>>,
    ) -> Result<RunReport, ExecError> {
        let asked = oracle.is_some();
        let offset = u64::from(taken.is_some());
        let KoreExecutionResult {
            leaves,
            implementation_chosen_values,
            unsupported_hooks,
            coverage,
            ..
        } = self.execute(
            run_request(start, options, stops),
            oracle.as_deref_mut(),
            offset,
        )?;
        // A hook the backend left unevaluated may leave an equation's condition open, so no
        // application is decided to have no value ([`decided`]).
        let decides = unsupported_hooks.is_empty();
        let path = one_path(leaves, self.heads(decides));
        let OnePath {
            mut leaf,
            mut valueless,
            held,
        } = match path {
            Ok(path) => path,
            Err(error) => return Err(self.path_error(error)),
        };
        if held && leaf.depth > 0 {
            leaf = self.before_valueless(
                start,
                leaf,
                decides,
                options.trace,
                stops,
                oracle.as_deref_mut(),
                offset,
            )?;
        }
        // The arrivals the path counted, the one it ends at included: under a condition, the
        // stop events, and every arrival beside them.
        let mut arrivals = leaf.stops.unwrap_or_default();
        let mut passed = leaf.arrivals.filter(|_| asked);
        let mut proposal = None;
        if leaf.reason == HaltReasonOutput::CutPoint {
            let (read, proposed) =
                read_proposal(leaf, self.heads(decides)).map_err(|error| self.path_error(error))?;
            leaf = read;
            match proposed {
                Ok(proposed) => proposal = Some(proposed),
                // The step reaches no state, so it is no arrival.
                Err(terms) => {
                    valueless.extend(terms);
                    arrivals = arrivals.saturating_sub(1);
                    passed = passed.map(|passed| passed.saturating_sub(1));
                }
            }
        }
        if leaf.reason == HaltReasonOutput::Stuck && (options.check_ends || check_ends()) {
            self.execute_requests = self.execute_requests.saturating_add(1);
            // The definition's heads, borrowed beside the backend ([`Self::heads`]).
            let heads: &dyn valueless::Heads = if decides {
                self.values.as_ref()
            } else {
                &valueless::Undecided
            };
            check_final_state(&mut self.backend, heads, &leaf.state, "the run ended stuck")?;
        }
        let valueless = valueless
            .into_iter()
            .map(|kore| self.term(kore))
            .collect::<Result<Vec<_>, _>>()?;
        let trace = if options.trace {
            let trace = self.steps(&leaf.trace);
            match taken {
                Some(taken) => self.taken_first(taken, trace),
                None => trace,
            }
        } else {
            Vec::new()
        };
        let coverage = options.coverage.zip(coverage).map(|(asked, coverage)| {
            self.coverage(
                coverage,
                asked.offered,
                taken.map(|taken| taken.rule_id.as_str()),
                proposal.as_ref().map(|proposal| proposal.rule_id.as_str()),
            )
        });
        let stop = self.stop(&leaf, stops, &trace, arrivals);
        let halt = Halt::from_backend(leaf.reason);
        // The one path ends at the arrival the condition was last left undecided at.
        let undecided = oracle
            .and_then(|oracle| oracle.undecided.take())
            .filter(|_| halt == Halt::StopUndecided)
            .map(|undecided| Undecided {
                at: match undecided.side {
                    StopSide::Before => StopAt::Before,
                    StopSide::After => StopAt::After,
                },
                rule: self.named_rule(undecided.rule_id),
                reason: undecided.reason,
            });
        let reached = term(leaf.state, &self.sort_hooks)?;
        let stdout = if self.console.stdout {
            console::stdout_buffer(reached.kore())
        } else {
            None
        };
        let exit_code = if self.console.exit && halt.is_complete() {
            self.exit_code(&reached)?
        } else {
            None
        };
        let (state, resume) = self.reported(reached, proposal)?;
        Ok(RunReport {
            halt,
            steps: leaf.depth.saturating_add(u64::from(taken.is_some())),
            state,
            trace,
            stdout,
            exit_code,
            log: log_lines(&leaf.effects),
            implementation_chosen_values,
            valueless,
            coverage,
            stop,
            stops: arrivals,
            arrivals: passed,
            undecided,
            resume,
        })
    }

    /// A run's reported state, its Floats as krun prints them ([`Self::krun_floats`]), and the
    /// state a later run goes on from where it is not the reported state's pattern
    /// ([`RunReport::resume`]): the backend's own state, not the one printed with krun's Floats,
    /// and after a stop before a rule, the rule's successor, the rule's step to be taken first.
    fn reported(
        &self,
        reached: Term,
        proposal: Option<Proposal>,
    ) -> Result<(Term, Option<State>), ExecError> {
        let resume = proposal.map(|proposal| State {
            pattern: proposal.successor,
            taken: Some(TakenStep {
                before: reached.kore().clone(),
                rule_id: proposal.rule_id,
                label: proposal.label,
            }),
        });
        Ok(match self.unparser.llvm_floats(reached.kore()) {
            Some(kore) => (
                self.term(kore)?,
                resume.or_else(|| Some(State::new(reached.into_kore()))),
            ),
            None => (reached, resume),
        })
    }

    /// The trace of a run from the state a stop before a rule left off at: the step by that rule
    /// first, then `trace`, renumbered after it ([`StopRules::before`]).
    fn taken_first(&mut self, taken: &TakenStep, trace: Vec<Step>) -> Vec<Step> {
        let first = Step {
            index: 1,
            label: taken.label.clone(),
            rule_id: taken.rule_id.clone(),
            origin: self
                .origins
                .step_origin(self.provenance.get(&taken.rule_id)),
        };
        std::iter::once(first)
            .chain(trace.into_iter().map(|step| Step {
                index: step.index.saturating_add(1),
                ..step
            }))
            .collect()
    }

    /// A name of the rewrite rule `rule_id` that a stop accepts ([`StopRules`]) and that
    /// selects it, as a report names a stop to its reader: its KRS item's spelling
    /// (`crate::ppu::frame_end`, `lang::step`) where that names the item alone, else its K label
    /// where that selects it. `None` where neither does, or the identity is no rule of the
    /// definition.
    #[must_use]
    pub fn stop_name(&self, rule_id: &str) -> Option<String> {
        self.rules.stop_name(rule_id)
    }

    /// Whether a reader names the sentence `rule_id` by its K label beside its KRS item's spelling
    /// (a coverage row's `item`): the item's spelling names some other item too, as where two
    /// packages of one crate name each have an item at its path, or the main package has an item
    /// at the whole of a dependency item's spelling, so the spelling alone does not tell which
    /// item wrote the sentence. `false` for an identity no item wrote or that is no sentence of
    /// the definition.
    #[must_use]
    pub fn keeps_label(&self, rule_id: &str) -> bool {
        self.rules.needs_label(rule_id)
    }

    /// The `UNIQUE_ID`s of a run's stop rules, each name resolved among the rewrite rules
    /// ([`StopRules`]), and the arrival the run ends at.
    fn stop_ids(&self, criterion: &StopCriterion) -> Result<StopIds, ExecError> {
        let (stop, count) = match criterion {
            StopCriterion::None => return Ok(StopIds::default()),
            StopCriterion::Rules { rules, count, .. } => (rules, *count),
        };
        let resolve = |names: &[String]| {
            let mut ids = BTreeSet::new();
            for name in names {
                ids.extend(self.rules.resolve_stop(name)?);
            }
            Ok::<_, ExecError>(ids.into_iter().collect::<Vec<_>>())
        };
        Ok(StopIds {
            before: resolve(&stop.before)?,
            after: resolve(&stop.after)?,
            count,
        })
    }

    /// The stop a run's end is, if it is one, the `nth` arrival at a stop: a cut-point leaf names
    /// its rule as its one candidate's; a terminal leaf names it only in its `detail` text,
    /// which is no stable encoding, so the rule is the one identity the stop rules select, or the
    /// last step of the trace.
    fn stop(
        &mut self,
        leaf: &KoreExecutionLeaf,
        stops: &StopIds,
        trace: &[Step],
        nth: u64,
    ) -> Option<Stop> {
        let (at, rule_id) = match leaf.reason {
            HaltReasonOutput::CutPoint => (
                StopAt::Before,
                leaf.candidates
                    .as_deref()
                    .and_then(|candidates| match candidates {
                        [candidate] => Some(candidate.unique_id.clone()),
                        _ => None,
                    }),
            ),
            HaltReasonOutput::Terminal => (
                StopAt::After,
                match stops.after.as_slice() {
                    [id] => Some(id.clone()),
                    _ => trace.last().map(|step| step.rule_id.clone()),
                },
            ),
            _ => return None,
        };
        let rule = rule_id.map(|rule_id| self.named_rule(rule_id));
        Some(Stop { at, rule, nth })
    }

    /// The rule `rule_id`, by its identities and origin.
    fn named_rule(&mut self, rule_id: String) -> NamedRule {
        let provenance = self.provenance.get(&rule_id);
        NamedRule {
            label: self.rules.get(&rule_id).and_then(|rule| rule.label.clone()),
            item: origin::item_path(provenance, self.rules.crate_names())
                .map(|item| self.rules.spelling(&item)),
            origin: self.origins.step_origin(provenance),
            rule_id,
        }
    }

    /// A run's coverage by identity, from k-rust's lists ([`Coverage`]): each identity once, with
    /// the predicates that hold of it, its label and kind from the definition's catalog, and its
    /// KRS origin.
    ///
    /// The step by a stop-before rule is the resumed run's ([`StopRules::before`]): `proposed`,
    /// the rule a run stopped before, loses the application the backend counts for the
    /// successor it proposed, and `taken`, the rule whose step leads to the run's start, is
    /// committed and gains it.
    fn coverage(
        &mut self,
        coverage: RunCoverageOutput<Pattern>,
        offered: bool,
        taken: Option<&str>,
        proposed: Option<&str>,
    ) -> Coverage {
        let RunCoverageOutput {
            applied,
            matched,
            offered: offered_ids,
            applied_counts,
            committed,
            ..
        } = coverage;
        let mut applied = applied.into_iter().collect::<BTreeSet<_>>();
        let matched = matched.into_iter().collect::<BTreeSet<_>>();
        let mut committed = committed
            .unwrap_or_default()
            .into_iter()
            .collect::<BTreeSet<_>>();
        let mut counts = applied_counts.unwrap_or_default();
        if let Some(id) = proposed
            && let Some(count) = counts.get_mut(id)
        {
            *count = count.saturating_sub(1);
            if *count == 0 {
                counts.remove(id);
                if !committed.contains(id) {
                    applied.remove(id);
                }
            }
        }
        if let Some(id) = taken {
            applied.insert(id.to_owned());
            committed.insert(id.to_owned());
            let count = counts.entry(id.to_owned()).or_default();
            *count = count.saturating_add(1);
        }
        // Each list is included in the one before it (k-rust's "Run coverage"); the union is
        // taken anyway, so an identity is listed whichever list names it.
        let ids = offered_ids
            .into_iter()
            .flatten()
            .chain(matched.iter().cloned())
            .chain(applied.iter().cloned())
            .chain(committed.iter().cloned())
            .collect::<BTreeSet<_>>();
        let rules = ids
            .into_iter()
            .map(|id| {
                let catalog = self.rules.get(&id);
                let provenance = self.provenance.get(&id);
                let is_applied = applied.contains(&id) || committed.contains(&id);
                CoveredRule {
                    label: catalog.and_then(|rule| rule.label.clone()),
                    kind: catalog.map(|rule| rule.kind),
                    item: origin::item_path(provenance, self.rules.crate_names())
                        .map(|item| self.rules.spelling(&item)),
                    origin: self.origins.step_origin(provenance),
                    matched: is_applied || matched.contains(&id),
                    applied: is_applied,
                    applications: counts.get(&id).copied().unwrap_or_default(),
                    committed: committed.contains(&id),
                    rule_id: id,
                }
            })
            .collect();
        Coverage { offered, rules }
    }

    /// The heads a run's reading asks about ([`valueless::Heads`]): the definition's, or, where
    /// `decides` is false, heads of which no application is decided to have no value.
    fn heads(&self, decides: bool) -> &dyn valueless::Heads {
        if decides {
            self.values.as_ref()
        } else {
            &valueless::Undecided
        }
    }

    /// The end of a run whose path reached, after `leaf.depth` steps, a state with no value
    /// ([`one_path`]): the step into it reached no state, so the run is undefined after the
    /// steps before it, at the last state with a value, as where the backend finds a step's
    /// result undefined. The run is followed again to each earlier depth until a state with a
    /// value is found, or the first state, which then has none. Each run keeps its trace only
    /// when `trace` asks for the report's.
    #[expect(
        clippy::too_many_arguments,
        reason = "The path followed again takes the run's request, its condition and its offset."
    )]
    fn before_valueless(
        &mut self,
        start: &Pattern,
        mut leaf: KoreExecutionLeaf,
        decides: bool,
        trace: bool,
        stops: &StopIds,
        mut oracle: Option<&mut ConditionOracle<'_>>,
        offset: u64,
    ) -> Result<KoreExecutionLeaf, ExecError> {
        let mut depth = leaf.depth;
        while depth > 0 {
            depth -= 1;
            let request = run_request(
                start,
                &RunOptions {
                    depth: Some(depth),
                    trace,
                    ..RunOptions::default()
                },
                stops,
            );
            let leaves = self.execute(request, oracle.as_deref_mut(), offset)?.leaves;
            let earlier = match one_path(leaves, self.heads(decides)) {
                Ok(earlier) => earlier,
                Err(error) => return Err(self.path_error(error)),
            };
            let mut earlier_leaf = earlier.leaf;
            earlier_leaf.reason = HaltReasonOutput::Vacuous;
            leaf = earlier_leaf;
            if !earlier.held {
                break;
            }
        }
        Ok(leaf)
    }

    /// The error of a run whose leaves are no one path ([`one_path`]).
    fn path_error(&self, error: PathError) -> ExecError {
        match error {
            PathError::None => ExecError::Result(
                "a run must end in exactly one state; the backend returned none".to_owned(),
            ),
            PathError::Several(states) => ExecError::Result(format!(
                "a run must end in exactly one state; the backend returned {states} defined states"
            )),
            PathError::Unread(error) => error,
            PathError::Undecided { states, over } => {
                let terms = over
                    .into_iter()
                    .map(|kore| {
                        let symbolic = valueless::is_symbolic(&kore);
                        let printed = self.term(kore).map_or_else(
                            |error| format!("a term that does not print ({error})"),
                            |term| format!("`{}`", self.unparse(&term, false).text.trim()),
                        );
                        if symbolic {
                            format!("{printed}, which holds a value the run has not fixed")
                        } else {
                            format!(
                                "{printed}, which may have a value the definition leaves open: no equation evaluated it, and its function is not one whose equations, each decided at values, are its whole definition"
                            )
                        }
                    })
                    .collect::<Vec<_>>();
                ExecError::Undecided(format!(
                    "the run reaches {states} states, under conditions over {}; the run cannot decide which holds, so it has no one path; `krs search` prints each state with its condition",
                    terms.join(" and ")
                ))
            }
        }
    }

    /// A run or search result with each binary32 and binary64 Float as `krun` prints it in every
    /// output format, in the LLVM runtime's form (`0.15000000000000000e1`, not k-rust's
    /// `1.5000000000000000e+00p53x11`).
    fn krun_floats(&self, state: Term) -> Result<Term, ExecError> {
        match self.unparser.llvm_floats(state.kore()) {
            Some(kore) => self.term(kore),
            None => Ok(state),
        }
    }

    /// The exit cell's final value: `getExitCode` of the final configuration, as krun computes the status.
    fn exit_code(&mut self, state: &Term) -> Result<Option<i64>, ExecError> {
        let Some(request) = console::exit_code_request(state.kore()) else {
            return Ok(None);
        };
        let simplified = self
            .backend
            .simplify_kore(None, &request, Admission::Unverified)?;
        Ok(console::exit_value(&simplified))
    }

    /// Return the set of reachable states that match the search mode, as `krun --search` does.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::SearchWithStreams`] for a definition with stream cells, or [`ExecError::Backend`] when the backend fails.
    pub fn search(
        &mut self,
        state: &State,
        options: SearchOptions,
    ) -> Result<SearchReport, ExecError> {
        if self.has_stream_cells() {
            return Err(ExecError::SearchWithStreams);
        }
        let response = search_backend(&mut self.backend, state.pattern.clone(), options)?;
        // A final state of `=>!` is one no rule applies to; one at the step bound may not be.
        if options.mode == SearchMode::Final && check_ends() {
            for solution in &response.states {
                if options.depth.is_none_or(|bound| solution.depth < bound) {
                    check_final_state(
                        &mut self.backend,
                        &valueless::Undecided,
                        &solution.state,
                        "the search found a final state",
                    )?;
                }
            }
        }
        let complete = response.incomplete.is_empty()
            && options
                .max_solutions
                .is_none_or(|limit| response.states.len() < limit);
        let KoreSearchResponse {
            states,
            effects,
            implementation_chosen_values,
            ..
        } = response;
        let solutions = states
            .into_iter()
            .map(|solution| {
                Ok(Solution {
                    state: self.krun_floats(term(solution.state, &self.sort_hooks)?)?,
                    depth: solution.depth,
                    trace: if options.trace {
                        self.steps(&solution.trace)
                    } else {
                        Vec::new()
                    },
                })
            })
            .collect::<Result<Vec<_>, ExecError>>()?;
        Ok(SearchReport {
            complete,
            solutions,
            log: log_lines(&effects),
            implementation_chosen_values,
        })
    }

    /// Prove the selected claims, one backend proof per claim, in selection order: the reports
    /// of [`Semantics::prove_claim`] for each claim of [`Semantics::prove_selection`].
    ///
    /// # Errors
    ///
    /// Returns an error of [`Semantics::prove_selection`] or [`Semantics::prove_claim`].
    pub fn prove(&mut self, options: &ProveOptions) -> Result<Vec<ProofReport>, ExecError> {
        let selection = self.prove_selection(options)?;
        selection
            .iter()
            .map(|claim| self.prove_claim(options, claim))
            .collect()
    }

    /// The claims `options` selects, in selection order: its module's claims, resolved from
    /// [`ProveOptions::claims`] once, so a caller proving them one at a time
    /// ([`Semantics::prove_claim`]) can report each as it starts and ends.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::NoClaims`], a claim-resolution error, or [`ExecError::Unavailable`] for an author spec module.
    pub fn prove_selection(&mut self, options: &ProveOptions) -> Result<Vec<ClaimInfo>, ExecError> {
        let prover = self.prover(options.module.as_deref())?;
        Ok(claims::select(prover.claims, &options.claims)?
            .into_iter()
            .map(|index| prover.claims[index].clone())
            .collect())
    }

    /// Prove `claim`, one of [`Semantics::prove_selection`]'s for the same `options`, as one
    /// backend proof per disjunct of its left-hand side.
    ///
    /// # Errors
    ///
    /// Returns an error of [`Semantics::prove_selection`], or [`ExecError::Backend`].
    pub fn prove_claim(
        &mut self,
        options: &ProveOptions,
        claim: &ClaimInfo,
    ) -> Result<ProofReport, ExecError> {
        let prover = self.prover(options.module.as_deref())?;
        // A claim read back from its serialization has lost its backend label: find it again.
        let claim = if claim.backend_label.is_empty() {
            let index = claims::select(prover.claims, std::slice::from_ref(&claim.label))?[0];
            &prover.claims[index]
        } else {
            claim
        };
        prove_claim(
            prover.backend,
            prover.sort_hooks,
            claim,
            options.depth,
            options.claim_timeout,
        )
    }

    /// The backend and claim catalog of the spec module `module` (`None`: the generated
    /// `<MAIN>-SPEC`), which must hold a claim.
    fn prover(&mut self, module: Option<&str>) -> Result<Prover<'_>, ExecError> {
        if let Some(module) = module
            && module != claims::spec_module(&self.main_module)
        {
            let prover = self.spec_prover(module)?;
            if prover.claims.is_empty() {
                return Err(ExecError::NoSpecClaims(module.to_owned()));
            }
            return Ok(Prover {
                backend: &mut prover.backend,
                sort_hooks: &prover.sort_hooks,
                claims: &prover.claims,
            });
        }
        if self.claims.is_empty() {
            if !self.spec_modules.is_empty() {
                return Err(ExecError::UnknownSpecModule {
                    requested: None,
                    modules: self.spec_modules.clone(),
                    generated: claims::spec_module(&self.main_module),
                });
            }
            return Err(ExecError::NoClaims);
        }
        Ok(Prover {
            backend: &mut self.backend,
            sort_hooks: &self.sort_hooks,
            claims: &self.claims,
        })
    }

    /// The value tables of this definition: names constructors and sorts
    /// ([`ValueIndex::decl`], [`ValueIndex::ctor`]) and decodes patterns ([`ValueIndex::decode`]).
    #[must_use]
    pub const fn values(&self) -> &Arc<ValueIndex> {
        &self.values
    }

    /// The canonical document of `value` at the position `ty` ([`encode()`]).
    ///
    /// # Errors
    ///
    /// Returns [`EncodeError`] for a value with no document there.
    pub fn encode(&self, value: &Value, ty: &InputType) -> Result<serde_json::Value, EncodeError> {
        encode::encode(&self.values, value, ty)
    }

    /// The states of a result term, one for each disjunct of a `\or` (a run's or search
    /// solution's state is one), with their cells addressed by KRS names.
    ///
    /// # Errors
    ///
    /// Returns [`ValueError::Malformed`] when a disjunct is not `\bottom` and not one
    /// configuration of this definition conjoined with predicates.
    pub fn views<'t>(&self, term: &'t Term) -> Result<Vec<View<'t>>, ValueError> {
        view::views(&self.values, term.kore())
    }

    /// The state of a result term that is not a disjunction, as [`Self::views`] reads it.
    ///
    /// # Errors
    ///
    /// Fails as [`Self::views`] does, and with [`ValueError::Malformed`] for a disjunction of
    /// several states.
    pub fn view<'t>(&self, term: &'t Term) -> Result<View<'t>, ValueError> {
        let mut views = self.views(term)?;
        if views.len() != 1 {
            return Err(ValueError::Malformed(format!(
                "the term is a disjunction of {} states; read them with `views`",
                views.len()
            )));
        }
        Ok(views.remove(0))
    }

    /// A term from a KORE pattern of this definition, with its KAST conversion, which renders
    /// each domain value by its sort's hook.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Result`] when the pattern has no KAST form.
    pub fn term(&self, kore: Pattern) -> Result<Term, ExecError> {
        term(kore, &self.sort_hooks)
    }

    /// Render a term. Only a [`PrintStyle::Pretty`] print can carry warnings (what
    /// [`Self::unparse`] says of it).
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Result`] when the term cannot be encoded.
    pub fn print(&self, term: &Term, style: PrintStyle) -> Result<Printed, ExecError> {
        let text = match style {
            PrintStyle::Kast => Printer::new().print_term(term.kast()),
            PrintStyle::Json => kast_json::to_string(term.kast())
                .map_err(|error| ExecError::Result(error.to_string()))?,
            PrintStyle::Kore => term.kore().to_string(),
            PrintStyle::Pretty => return Ok(self.unparse(term, false)),
        };
        Ok(Printed {
            text,
            warnings: Vec::new(),
            grouped: Vec::new(),
        })
    }

    /// Print a term through the definition's grammar, as `krun --output pretty` prints a configuration (KF-017).
    ///
    /// The text has no trailing newline; [`Printed::warnings`] lists the problems that degraded it (labels printed as KAST, invalid colour lists).
    /// It is the text of a configuration value, as `krs run`, `krs search` and `krs prove` print a state: a child grouped in K's default bracket `( .. )` where the definition declares no bracket is a stated fallback ([`krs_unparse::Warning::Grouped`]).
    #[must_use]
    pub fn unparse(&self, term: &Term, color: bool) -> Printed {
        self.unparser.print_kore(
            term.kore(),
            &krs_unparse::Options::new(krs_unparse::Mode::Pretty).with_color(color),
        )
    }

    /// The definition's main cell, by its K name: the computation cell the program starts in
    /// (`krs_ir_levels::k_surface::main_cell`), whatever its name; `None` in a configuration
    /// without one.
    #[must_use]
    pub fn main_cell(&self) -> Option<&str> {
        self.main_cell.as_deref()
    }

    /// Print the first item of a term's main cell ([`Self::main_cell`]) through the
    /// definition's grammar, as [`Semantics::unparse`] prints it inside the whole term:
    /// `Some(None)` when the cell is empty, `None` without a main cell (see
    /// [`Term::computation_head_kore`]).
    ///
    /// A symbol without a printable production is printed as KAST and reported in [`Printed::warnings`].
    #[must_use]
    pub fn unparse_computation_head(&self, term: &Term) -> Option<Option<Printed>> {
        let cell = self.main_cell()?;
        term.computation_head_kore(cell).map(|head| {
            head.map(|item| {
                self.unparser
                    .print_kore(item, &krs_unparse::Options::new(krs_unparse::Mode::Pretty))
            })
        })
    }

    /// The printer `krs run` prints this definition's results with.
    #[must_use]
    pub fn unparser(&self) -> &krs_unparse::Unparser {
        &self.unparser
    }

    /// Read the main cell's first item back from the text
    /// [`Semantics::unparse_computation_head`] prints: parsed with the main module's grammar,
    /// which has the builtin collections' syntax too, at `KItem`, with its aliases and desugars
    /// expanded as a program's are.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Parse`] when the text does not parse.
    pub fn parse_computation_head(&mut self, text: &str) -> Result<Pattern, ExecError> {
        let cell = self.main_cell.clone().unwrap_or_else(|| "k".to_owned());
        self.configuration
            .parse_head(&cell, text)
            .map_err(|error| ExecError::Parse {
                input: format!("the printed <{cell}> head"),
                sort: "KItem".to_owned(),
                message: error.to_string(),
            })
    }

    /// [`Self::parse_computation_head`], where an ambiguous text gives each of its readings the
    /// parser lists ([`k_rust::inner::ProgramParser::parse_readings`]).
    pub(crate) fn parse_computation_head_readings(
        &mut self,
        text: &str,
    ) -> Result<Vec<Pattern>, ExecError> {
        let cell = self.main_cell.clone().unwrap_or_else(|| "k".to_owned());
        self.configuration
            .parse_head_readings(&cell, text, configuration::Readings::Listed)
            .map_err(|error| ExecError::Parse {
                input: format!("the printed <{cell}> head"),
                sort: "KItem".to_owned(),
                message: error.to_string(),
            })
    }

    /// [`Self::parse_cell`], where an ambiguous text gives each of its readings the parser
    /// lists ([`k_rust::inner::ProgramParser::parse_readings`]).
    pub(crate) fn parse_cell_readings(
        &mut self,
        cell: &str,
        sort: &str,
        text: &str,
    ) -> Result<Vec<Pattern>, ExecError> {
        self.configuration
            .parse_cell_readings(
                cell,
                &KastSort::new(sort),
                text,
                configuration::Readings::Listed,
            )
            .map_err(|error| ExecError::Parse {
                input: format!("the printed <{cell}>"),
                sort: sort.to_owned(),
                message: error.to_string(),
            })
    }

    /// Read a cell's content back from its printed text: parsed with the main module's grammar
    /// at `sort`, the cell's declared sort (a `K` cell's as a sequence), with its aliases and
    /// desugars expanded as a program's are.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Parse`] when the text does not parse.
    pub fn parse_cell(&mut self, cell: &str, sort: &str, text: &str) -> Result<Pattern, ExecError> {
        self.configuration
            .parse_cell(cell, &KastSort::new(sort), text)
            .map_err(|error| ExecError::Parse {
                input: format!("the printed <{cell}>"),
                sort: sort.to_owned(),
                message: error.to_string(),
            })
    }

    fn steps(&mut self, trace: &[TraceEntry]) -> Vec<Step> {
        trace
            .iter()
            .filter(|entry| entry.kind == "rewrite")
            .enumerate()
            .map(|(index, entry)| Step {
                index: u64::try_from(index).unwrap_or(u64::MAX).saturating_add(1),
                label: entry.label.clone(),
                rule_id: entry.unique_id.clone(),
                origin: self
                    .origins
                    .step_origin(self.provenance.get(&entry.unique_id)),
            })
            .collect()
    }
}

/// Why ends whose run or search read `values`, values the definition leaves open (k-rust's
/// implementation-chosen hook values), may not be every end of the definition, as a phrase after
/// "the run" or "the search" that names each value's hook; `None` when it read none.
///
/// Where it read none, every model of the definition that agrees with the inputs gives the same
/// ends (k-rust's `ExecutionResult::implementation_chosen_values`); where it read one, another
/// implementation may choose another value there, and end elsewhere.
#[must_use]
pub fn open_values(values: &[ChosenValueOutput]) -> Option<String> {
    if values.is_empty() {
        return None;
    }
    let mut hooks = Vec::<String>::new();
    for value in values {
        let hook = format!("`{}`", value.hook);
        if !hooks.contains(&hook) {
            hooks.push(hook);
        }
    }
    let hooks = hooks.join(", ");
    Some(format!(
        "read values the definition leaves open ({hooks}), so another implementation of it may end otherwise"
    ))
}

/// The backend request of a run from `start` under `options`: strategy `any`, as krun follows one
/// path, with the backend's trace kept only for a run that reports one (k-rust keeps it unless
/// asked not to, an entry per rewrite and simplification of the path), and the stop rules by
/// `UNIQUE_ID`, which the backend selects as it selects them by label, with the arrival it
/// counts to.
fn run_request(start: &Pattern, options: &RunOptions, stops: &StopIds) -> ExecuteRequest {
    let mut request = ExecuteRequest::new(start.clone());
    request.strategy = ExecutionStrategy::Any;
    request.max_depth = options.depth;
    request.trace = options.trace;
    request.cut_point_rules.clone_from(&stops.before);
    request.terminal_rules.clone_from(&stops.after);
    if !stops.is_empty() {
        request.stop_count = Some(stops.count);
    }
    if let Some(coverage) = options.coverage {
        request.collect_coverage = true;
        request.collect_counts = true;
        request.collect_committed = true;
        request.collect_offered = coverage.offered;
    }
    request
}

/// The successor a cut-point leaf proposes for the step by its stop rule
/// ([`StopRules::before`]), read as the end of a run is ([`one_path`]): where it has no value,
/// the step reaches no state, and the leaf, at the state the rule would rewrite, is then
/// undefined (`vacuous`), with the terms with no value (`Err`); otherwise it stays the stop.
fn read_proposal(
    mut leaf: KoreExecutionLeaf,
    heads: &dyn valueless::Heads,
) -> Result<(KoreExecutionLeaf, Result<Proposal, Vec<Pattern>>), PathError> {
    let candidate = cut_point_candidate(&leaf).map_err(PathError::Unread)?;
    let (successor, rule_id, label) = (
        candidate.state.clone(),
        candidate.unique_id.clone(),
        candidate.label.clone(),
    );
    // The leaf is read at the successor, which its reading may replace by its configuration;
    // the proposal keeps the successor as the backend proposed it.
    let at = std::mem::replace(&mut leaf.state, successor.clone());
    let read = one_path(vec![leaf], heads)?;
    let mut leaf = read.leaf;
    leaf.state = at;
    if read.held {
        leaf.reason = HaltReasonOutput::Vacuous;
        return Ok((leaf, Err(read.valueless)));
    }
    leaf.reason = HaltReasonOutput::CutPoint;
    Ok((
        leaf,
        Ok(Proposal {
            successor,
            rule_id,
            label,
        }),
    ))
}

/// The one candidate of a cut-point leaf: the stop rule's step, its successor normalized by the
/// backend as any successor is.
fn cut_point_candidate(
    leaf: &KoreExecutionLeaf,
) -> Result<&ExecutionCandidateOutput<Pattern>, ExecError> {
    match leaf.candidates.as_deref() {
        Some([candidate]) => Ok(candidate),
        candidates => Err(ExecError::Result(format!(
            "a stop before a rule must propose one successor; the backend proposed {}",
            candidates.map_or(0, <[_]>::len)
        ))),
    }
}

/// The K name of the main cell of the definition's configuration, the cell both backends mark
/// (`krs_ir_levels::k_surface::main_cell`); `None` where the configuration has none. A
/// definition without a configuration has K's, whose computation cell is `k`.
fn main_cell_name(definition: &DefinitionIr) -> Option<String> {
    let configuration = definition.modules().iter().find_map(|module| {
        module
            .sentences()
            .iter()
            .find_map(|sentence| match sentence {
                krs_ir_levels::DefinitionSentence::Configuration(configuration) => {
                    Some(configuration)
                }
                _ => None,
            })
    });
    match configuration {
        Some(configuration) => krs_ir_levels::k_surface::main_cell(configuration)
            .cell()
            .map(|cell| cell.name().to_owned()),
        None => Some("k".to_owned()),
    }
}

/// Compile Definition IR to symbolic KORE with the options every `krs-exec` operation and the gate's one-shot compiler share.
///
/// # Errors
///
/// Returns the native frontend's typed rejection.
pub fn compile_definition(
    definition: &DefinitionIr,
    timings: &mut Timings,
) -> Result<(CompiledArtifacts, ConfigurationContext), DefinitionCompileError> {
    compile_definition_with_context_timed(
        definition,
        CompileOptions {
            backend: krs_k_rust::Backend::Haskell,
            ..CompileOptions::default()
        },
        timings,
    )
}

/// Compile the proof definition of one author spec module to symbolic KORE with the same options as [`compile_definition`].
fn compile_spec_definition(
    definition: &DefinitionIr,
    module: &str,
    timings: &mut Timings,
) -> Result<CompiledArtifacts, DefinitionCompileError> {
    compile_spec_definition_with_context_timed(
        definition,
        module,
        CompileOptions {
            backend: krs_k_rust::Backend::Haskell,
            ..CompileOptions::default()
        },
        timings,
    )
    .map(|(artifacts, _)| artifacts)
}

/// The refusal of an expectation whose `halt` is `depth-bound` ([`ends`], "Results"): this
/// statement, then [`DEPTH_BOUND_GUIDANCE`]. Both are fixed texts, the same for every case, so a
/// caller that refuses several cases for it may state the guidance once.
pub const DEPTH_BOUND_REFUSAL: &str = "an expected end is never `depth-bound`";

/// What follows [`DEPTH_BOUND_REFUSAL`] in the refusal: why no expectation is `depth-bound`, and
/// how to state the state at a point of a run instead, with a stop, its count, and how to find
/// the count.
pub const DEPTH_BOUND_GUIDANCE: &str = ": the depth counts the compiled definition's steps, the \
     heating and cooling steps of strictness and contexts included, so the state after N steps is \
     no fact about the definition, and a run that reaches its bound is not known to have ended; to \
     expect the state at a point of the run, stop the run at an item of the definition, count its \
     arrivals there and expect that stop, for example \
     `run = { stop_before = [\"crate::machine::boundary\"], stop_count = N }` with \
     `halt = \"stopped\", rule = \"crate::machine::boundary\"`, where `rule` names the one item \
     the run stopped at, as the status line of `krs run --case` names it (krs run: stopped after S \
     steps, before `crate::machine::boundary` (stop N of N)), whichever of several stop items it \
     is; `depth` may stay in `run` beside the stop as a backstop, under which a run that never reaches the stop ends `depth-bound` and its \
     expectation is inconclusive; to find N, run the case without its `expect` table and with a \
     count larger than the run reaches (`krs run --case FILE#NAME --stop-before ITEM --stop-count \
     1000000` beside a `run` table that holds only `depth`), which prints how many arrivals it \
     reached (`depth-bound after S steps, A of 1000000 stops reached`)";

/// An expectation's views by cell path, and the observer it names.
type ExpectationViews = (BTreeMap<String, String>, Option<String>);

/// The `views` and `observer` of an `expect` table, removed from `table`; a refusal is its
/// position below `expect` and the reason.
fn expectation_views(
    table: &mut serde_json::Map<String, serde_json::Value>,
) -> Result<ExpectationViews, (String, &'static str)> {
    let views = match table.remove("views") {
        None => BTreeMap::new(),
        Some(serde_json::Value::Object(views)) => views
            .into_iter()
            .map(|(cell, function)| match function {
                serde_json::Value::String(function) if !function.is_empty() => Ok((cell, function)),
                _ => Err((
                    format!("views.{cell}"),
                    "a view is the name of a function, a non-empty string",
                )),
            })
            .collect::<Result<_, _>>()?,
        Some(_) => {
            return Err((
                "views".to_owned(),
                "`views` is a table of a function name by cell path",
            ));
        }
    };
    let observer = match table.remove("observer") {
        None => None,
        Some(serde_json::Value::String(observer)) if !observer.is_empty() => Some(observer),
        Some(_) => {
            return Err((
                "observer".to_owned(),
                "`observer` names the definition the views are evaluated in, a non-empty string",
            ));
        }
    };
    if observer.is_some() && views.is_empty() {
        return Err((
            "observer".to_owned(),
            "`observer` names the definition the views are evaluated in, and the expectation names no view",
        ));
    }
    Ok((views, observer))
}

/// A spec module's backend and claim catalog ([`Semantics::prover`]).
struct Prover<'a> {
    backend: &'a mut Backend,
    sort_hooks: &'a HashMap<String, String>,
    claims: &'a [ClaimInfo],
}

/// Prove `claim` on `backend`, at most `depth` proof transitions per disjunct, within the wall
/// `timeout` ([`ProveOptions::claim_timeout`]).
fn prove_claim(
    backend: &mut Backend,
    sort_hooks: &HashMap<String, String>,
    claim: &ClaimInfo,
    depth: Option<u64>,
    timeout: Option<std::time::Duration>,
) -> Result<ProofReport, ExecError> {
    let Some(timeout) = timeout else {
        return prove_claim_within(backend, sort_hooks, claim, depth, None);
    };
    let token = k_rust::backend::CancellationToken::new();
    if timeout.is_zero() {
        token.cancel();
        return prove_claim_within(backend, sort_hooks, claim, depth, Some(&token));
    }
    // The wall: a thread that cancels the proof's token when `timeout` passes, unless the proof
    // ends first and drops the channel's sender, which wakes it.
    let (ended, wall) = std::sync::mpsc::channel::<()>();
    let cancel = token.clone();
    std::thread::scope(|scope| {
        scope.spawn(move || {
            if wall.recv_timeout(timeout) == Err(std::sync::mpsc::RecvTimeoutError::Timeout) {
                cancel.cancel();
            }
        });
        let report = prove_claim_within(backend, sort_hooks, claim, depth, Some(&token));
        drop(ended);
        report
    })
}

/// [`prove_claim`], each disjunct's proof run in the scope of `token` when there is one: a proof
/// the token cancelled ends the claim, whose verdict is then [`Verdict::Timeout`] unless a part
/// proven before it refutes the claim (a counterexample or a failure, which more time cannot
/// undo). The report keeps the leaves of the disjuncts whose proofs ended before the cancelled
/// one, the evidence of such a refutation among them, and has none of the cancelled one's.
fn prove_claim_within(
    backend: &mut Backend,
    sort_hooks: &HashMap<String, String>,
    claim: &ClaimInfo,
    depth: Option<u64>,
    token: Option<&k_rust::backend::CancellationToken>,
) -> Result<ProofReport, ExecError> {
    let claim = claim.clone();
    // A claim whose left-hand side is a disjunction is one backend claim per disjunct, each
    // proven by its own request; the claim holds only if every disjunct does, so its verdict
    // is the weakest of theirs and its leaves are all of theirs.
    let disjuncts = backend.claim_disjuncts(None, &claim.backend_label)?;
    let selectors = if disjuncts.len() > 1 {
        disjuncts
    } else {
        vec![claim.backend_label.clone()]
    };
    let mut verdict = Verdict::Proven;
    let mut leaves = Vec::new();
    let mut trusted_claims = std::collections::BTreeSet::new();
    for selector in selectors {
        let request = ProveRequest {
            claim: Some(selector),
            max_depth: depth,
            ..ProveRequest::default()
        };
        let result = match token {
            Some(token) => token.scope(|| backend.prove_kore(request)),
            None => backend.prove_kore(request),
        };
        // A cancelled proof answers `Err` with the `Cancelled` cause unless its verdict no longer
        // depends on the work the cancellation prevented (k-rust's "Bounding an operation"); only
        // this function's token cancels it.
        let result = match result {
            Err(error)
                if error.stop_cause() == Some(&k_rust::backend::StopCause::Cancelled)
                    && token.is_some() =>
            {
                verdict = verdict.weakest(Verdict::Timeout);
                break;
            }
            result => result?,
        };
        let disjunct = Verdict::from_backend(&result.status).ok_or_else(|| {
            ExecError::Result(format!("unknown proof status `{}`", result.status))
        })?;
        verdict = verdict.weakest(disjunct);
        trusted_claims.extend(result.trusted_claims);
        for leaf in result.leaves {
            leaves.push(ProofLeaf {
                state: term(leaf.state, sort_hooks)?,
                depth: leaf.depth,
                outcome: leaf.outcome.name().to_owned(),
                detail: leaf.detail,
                certified: leaf.certified,
                vacuous: leaf.vacuous,
                claim_steps: leaf.claim_steps,
                contradicted_total: leaf
                    .contradicted_total
                    .map(|record| {
                        Ok::<_, ExecError>(k_rust::backend::ContradictedTotalOutput {
                            symbol: record.symbol,
                            k_label: record.k_label,
                            rule_id: record.rule_id,
                            rule_label: record.rule_label,
                            origin: record.origin,
                            application: term(record.application, sort_hooks)?,
                            undefined: term(record.undefined, sort_hooks)?,
                        })
                    })
                    .transpose()?,
            });
        }
    }
    // The backend assumes a trusted claim and reports it proven; KRS never calls an
    // assumption proven (KF-042).
    if claim.trusted && verdict == Verdict::Proven {
        verdict = Verdict::Trusted;
    }
    Ok(ProofReport {
        claim: claim.label,
        modality: claim.modality,
        origin: claim.origin,
        verdict,
        trusted_claims: trusted_claims.into_iter().collect(),
        leaves,
        crash: None,
    })
}

/// The `io::log` lines among committed backend effects, in order.
fn log_lines(effects: &[EffectOutput]) -> Vec<String> {
    effects
        .iter()
        .map(|effect| match effect {
            EffectOutput::UserLog { message } => message.clone(),
        })
        .collect()
}

/// `KRS_CHECK_ENDS=1`: a run reported stuck, or a final state `=>!` search found, at `state`
/// ended where no rule applies, at a state that is its own value. One more step from the state,
/// trying every rule, must take none and give back that state: a step, a successor, or another
/// state means the report states what does not hold of the state. The cost is one
/// simplification and one rule attempt per state checked.
///
/// The step's leaves are read with `heads` as a run reads its own ([`one_path`]): a rule whose
/// condition reads a term with no value does not apply, so the leaf where the backend took it
/// under that condition is no state, and the leaf where it did not is the state, its
/// configuration where the reading decided its condition holds. A run reads with the
/// definition's heads; a search, which prints the backend's states with their conditions, with
/// [`valueless::Undecided`], under which every leaf is read as returned.
fn check_final_state(
    backend: &mut Backend,
    heads: &dyn valueless::Heads,
    state: &Pattern,
    what: &str,
) -> Result<(), ExecError> {
    let mut request = ExecuteRequest::new(state.clone());
    request.strategy = ExecutionStrategy::All;
    request.max_depth = Some(1);
    request.trace = false;
    let again = backend.execute_kore(request)?.leaves;
    let mut states = Vec::new();
    for end in &again {
        let split = valueless::split(&end.state);
        let mut read = Vec::new();
        match valueless::read(&split.predicates, heads, &mut read) {
            valueless::Reading::Fails => {}
            reading => {
                let decided = reading == valueless::Reading::Holds && !read.is_empty();
                let reached = match split.configuration {
                    Some(configuration) if decided => configuration,
                    _ => &end.state,
                };
                states.push((end, reached));
            }
        }
    }
    let holds = matches!(
        states.as_slice(),
        [(end, reached)] if end.depth == 0 && end.reason == HaltReasonOutput::Stuck && *reached == state
    );
    if holds {
        return Ok(());
    }
    Err(ExecError::Result(format!(
        "KRS_CHECK_ENDS: {what} at a state that a step from it does not leave as it is: {}",
        again
            .iter()
            .map(|end| format!("{:?} after {} step(s)", end.reason, end.depth))
            .collect::<Vec<_>>()
            .join(", ")
    )))
}

/// Whether `KRS_CHECK_ENDS=1` asks every run reported stuck, and every final state of a `=>!`
/// search, to be checked to end where no rule applies ([`check_final_state`]).
fn check_ends() -> bool {
    std::env::var_os("KRS_CHECK_ENDS").as_deref() == Some(std::ffi::OsStr::new("1"))
}

/// The leaf that is the path of a one-path run.
///
/// A `trivial` or `vacuous` leaf denotes no configuration: its result or its path condition is
/// `#Bottom`, as where a partial function is applied outside its domain.
/// Where the backend splits on whether a result is defined, it returns the leaf under that
/// definedness and such an undefined leaf beside it; their disjunction is the defined leaf alone,
/// so that leaf is the path.
/// The run is undefined only when every leaf is.
///
/// A defined leaf's condition and configuration are read with every term [`valueless`] shows has
/// no value (a ground application of a partial function defined by its equations alone, each
/// decided at values ([`decided`]), which the backend left unevaluated):
/// - A leaf whose condition gives such a term a value denotes no state: where the backend split
///   a step on a rule's condition over it, the leaf where the condition holds is no state, and
///   the leaf where it does not is the path, its condition printed where it holds a term the
///   reading does not decide. Where every leaf is no state, the run is undefined at the first.
/// - A path whose configuration holds such a term has no value: the run is undefined there
///   (`Semantics::run` reports it at the last state with a value, `Semantics::before_valueless`).
///   Otherwise, where its condition read one, the rule whose condition read it did not apply,
///   and the run ends as the leaf does.
///
/// Either way the path names the terms with no value. Several leaves that remain are a split
/// over terms that may have values, which the run does not decide ([`PathError::Undecided`]).
fn one_path(
    leaves: Vec<KoreExecutionLeaf>,
    heads: &dyn valueless::Heads,
) -> Result<OnePath, PathError> {
    let (undefined, defined): (Vec<_>, Vec<_>) = leaves.into_iter().partition(|leaf| {
        matches!(
            leaf.reason,
            HaltReasonOutput::Trivial | HaltReasonOutput::Vacuous
        )
    });
    if defined.is_empty() {
        return undefined
            .into_iter()
            .next()
            .map(|leaf| OnePath {
                leaf,
                valueless: Vec::new(),
                held: false,
            })
            .ok_or(PathError::None);
    }
    let several = defined.len();
    let mut kept = Vec::new();
    let mut failed = None;
    let mut over = Vec::<Pattern>::new();
    for leaf in defined {
        let split = valueless::split(&leaf.state);
        let mut read = Vec::new();
        let reading = valueless::read(&split.predicates, heads, &mut read);
        let read = read.into_iter().cloned().collect::<Vec<_>>();
        match reading {
            valueless::Reading::Fails => {
                if failed.is_none() {
                    failed = Some((leaf, read));
                }
            }
            valueless::Reading::Holds => kept.push((leaf, read, true)),
            valueless::Reading::Open { over: open } => {
                for term in open {
                    if !over.contains(term) {
                        over.push(term.clone());
                    }
                }
                kept.push((leaf, read, false));
            }
        }
    }
    let (mut leaf, read, holds) = match <[_; 1]>::try_from(kept) {
        Ok([kept]) => kept,
        Err(kept) if kept.is_empty() => {
            // Every leaf gives a term with no value a value: the step has no state.
            let (leaf, read) = failed.expect("a defined leaf");
            let mut leaf = configured(leaf);
            leaf.reason = HaltReasonOutput::Vacuous;
            return Ok(OnePath {
                leaf,
                valueless: read,
                held: true,
            });
        }
        Err(kept) if over.is_empty() => {
            return Err(PathError::Several(kept.len().max(several)));
        }
        Err(kept) => {
            return Err(PathError::Undecided {
                states: kept.len(),
                over,
            });
        }
    };
    // A condition the reading decided holds is the state's: the state is its configuration.
    if holds && !read.is_empty() {
        leaf = configured(leaf);
    }
    let mut held = Vec::new();
    if let Some(configuration) = valueless::split(&leaf.state).configuration {
        valueless::witnesses(configuration, heads, &mut held);
    }
    if held.is_empty() {
        return Ok(OnePath {
            leaf,
            valueless: read,
            held: false,
        });
    }
    let held = held.into_iter().cloned().collect();
    leaf.reason = HaltReasonOutput::Vacuous;
    Ok(OnePath {
        leaf,
        valueless: held,
        held: true,
    })
}

/// `leaf` at its state's configuration, where its state has one ([`valueless::split`]), moved
/// out of the state; otherwise `leaf` as it is.
fn configured(leaf: KoreExecutionLeaf) -> KoreExecutionLeaf {
    if valueless::split(&leaf.state).configuration.is_none() {
        return leaf;
    }
    let state = valueless::into_configuration(leaf.state)
        .expect("a state `split` finds a configuration in has one");
    KoreExecutionLeaf { state, ..leaf }
}

/// The path of a one-path run ([`one_path`]): its leaf, and the terms with no value it holds
/// or its condition read.
#[derive(Debug)]
struct OnePath {
    leaf: KoreExecutionLeaf,
    valueless: Vec<Pattern>,
    /// Whether the leaf's state has no value: it holds such a term, or its condition gives one a
    /// value; the run is then undefined.
    held: bool,
}

/// Why a run's leaves are no one path ([`one_path`]).
#[derive(Debug)]
enum PathError {
    /// The backend returned no leaf.
    None,
    /// Several leaves under conditions that read no term: the backend broke a run's contract.
    Several(usize),
    /// `states` leaves remain under conditions over the terms `over`, which may have values.
    Undecided { states: usize, over: Vec<Pattern> },
    /// A leaf is not what the run asked for: a stop before a rule that proposes no one
    /// successor ([`cut_point_candidate`]).
    Unread(ExecError),
}

fn search_backend(
    backend: &mut Backend,
    state: Pattern,
    options: SearchOptions,
) -> Result<KoreSearchResponse, ExecError> {
    let mut request = SearchRequest::new(state);
    request.search_type = options.mode.backend();
    request.max_depth = options.depth;
    request.max_results = options.max_solutions;
    Ok(backend.search_kore(request)?)
}

/// The sort hooks of the definition `backend` runs, by KAST sort name: a result's domain value
/// is a token whose text depends on its sort's hook (a `BYTES.Bytes` value is a byte string,
/// not UTF-8 text, and a `STRING.String` value is quoted), and only the definition states them.
fn result_sort_hooks(backend: &mut Backend) -> Result<HashMap<String, String>, ExecError> {
    let definition = backend
        .select_definition(None)
        .map_err(|error| ExecError::Backend(error.to_string()))?;
    Ok(sort_hooks(definition.sorts().iter().filter_map(
        |(name, sort)| Some((name.as_ref(), sort.hook.as_deref()?)),
    )))
}

/// A backend result's pattern as a term, converted to KAST with its definition's `sort_hooks`.
fn term(kore: Pattern, sort_hooks: &HashMap<String, String>) -> Result<Term, ExecError> {
    let kast = Converter::new(sort_hooks)
        .convert(&kore)
        .map_err(|error| ExecError::Result(error.to_string()))?;
    Ok(Term::new(kore, kast))
}

/// The compiled definition's configuration variables (`declared`), each with the `#[k::init]`
/// parameter that declares it; a stream variable the language adds (`$IO`, `$STDIN`), which no
/// parameter declares, is named by its K name's lowercase.
fn config_variables(
    declared: &BTreeMap<String, KastSort>,
    parameters: &[Parameter],
) -> Vec<ConfigVariable> {
    let mut variables = declared
        .iter()
        .map(|(name, sort)| {
            let parameter = parameters
                .iter()
                .find(|parameter| parameter.variable == *name);
            ConfigVariable {
                name: name.clone(),
                parameter: parameter.map_or_else(
                    || name.to_ascii_lowercase(),
                    |parameter| parameter.name.clone(),
                ),
                sort: sort.to_string(),
                is_main: parameter.is_some_and(|parameter| parameter.main),
            }
        })
        .collect::<Vec<_>>();
    variables.sort_by_key(|variable| (!variable.is_main, variable.name.clone()));
    variables
}

/// The sorts the package's own modules declare, by name: the program sorts worth listing.
fn user_sorts(definition: &DefinitionIr, frontend: &NativeDefinition) -> Vec<String> {
    let modules = definition
        .modules()
        .iter()
        .map(|module| module.id().as_str())
        .collect::<std::collections::BTreeSet<_>>();
    frontend
        .modules
        .iter()
        .filter(|module| modules.contains(module.name.as_str()))
        .flat_map(|module| &module.local_sentences)
        .filter_map(|sentence| match &**sentence {
            k_rust::definition::Sentence::SyntaxSort { sort, .. }
            | k_rust::definition::Sentence::Production { sort, .. } => Some(sort.name.clone()),
            _ => None,
        })
        .filter(|sort| !sort.starts_with('#') && !sort.ends_with("Cell"))
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn parse_error(
    input: &ProgramInput,
    sort: &KastSort,
    error: &(dyn std::error::Error + 'static),
) -> ExecError {
    ExecError::Parse {
        input: located(&input.name, &input.text, boxed_parse_position(error)),
        sort: sort.to_string(),
        message: error.to_string(),
    }
}

/// The byte offset at which program text stopped parsing, when the parser reports one.
fn parse_position(error: &ProgramParseError) -> Option<usize> {
    match error.error.as_ref() {
        ParseError::NoParse { position, .. } => Some(*position),
        _ => None,
    }
}

/// Where a configuration variable's text stops being readable, given the failure of the last
/// grammar that read it (`error`) and, where the syntax module's grammar read it first, that
/// grammar's (`syntax_attempt`).
///
/// The reading rule admits a text when either grammar parses it, so a prefix of the text still
/// extends to an admitted text exactly when it does under one of the grammars: the text stops at
/// the later of the two failures' positions. A failure that is no `NoParse` (an ambiguity, a
/// grammar defect) did not stop at a point of the text, so then no position is given.
fn variable_parse_position(
    error: &ProgramParseError,
    syntax_attempt: Option<&ProgramParseError>,
) -> Option<usize> {
    let main = parse_position(error);
    match syntax_attempt {
        None => main,
        Some(syntax_attempt) => main
            .zip(parse_position(syntax_attempt))
            .map(|(main, syntax)| main.max(syntax)),
    }
}

fn boxed_parse_position(error: &(dyn std::error::Error + 'static)) -> Option<usize> {
    if let Some(ProgramError::Parse(error)) = error.downcast_ref::<ProgramError>() {
        return parse_position(error);
    }
    error
        .downcast_ref::<ProgramParseError>()
        .and_then(parse_position)
}

/// `name:line:column` for a byte offset in `text`, or `name` when the offset is unknown.
fn located(name: &str, text: &str, position: Option<usize>) -> String {
    let index = krs_ir::LineIndex::new(text);
    match position.and_then(|position| index.byte_to_position(position).ok()) {
        Some(position) => format!("{name}:{}:{}", position.line(), position.scalar_column()),
        None => name.to_owned(),
    }
}

/// Where a bound variable's text came from, as a parse error names it.
struct Source {
    /// `-c NAME`, or a file's name.
    label: String,
    /// A file's text, in which a parse error is located; `None` for a `-c` binding.
    text: Option<String>,
}

impl Source {
    fn option(written: &str) -> Self {
        Self {
            label: format!("-c {written}"),
            text: None,
        }
    }

    fn file(file: &ProgramInput) -> Self {
        Self {
            label: file.name.clone(),
            text: Some(file.text.clone()),
        }
    }

    fn located(&self, position: Option<usize>) -> String {
        match &self.text {
            Some(text) => located(&self.label, text, position),
            None => self.label.clone(),
        }
    }
}

fn configuration_error(
    error: &k_rust::kompile::ConfigurationError,
    sources: &BTreeMap<String, Source>,
    variables: &[ConfigVariable],
) -> ExecError {
    use k_rust::kompile::ConfigurationError as Error;
    let sort_of = |name: &str| {
        variables
            .iter()
            .find(|variable| variable.name == name)
            .map_or_else(String::new, |variable| variable.sort.clone())
    };
    match error {
        Error::Program(parse) => ExecError::Parse {
            input: sources.get("PGM").map_or_else(
                || "the program".to_owned(),
                |source| source.located(parse_position(parse)),
            ),
            sort: sort_of("PGM"),
            message: parse.to_string(),
        },
        Error::Parse {
            variable,
            sort,
            error,
            syntax_attempt,
        } => {
            let name = variable.strip_prefix('$').unwrap_or(variable);
            let syntax_attempt = syntax_attempt.as_deref();
            ExecError::Parse {
                input: sources.get(name).map_or_else(
                    || format!("-c {name}"),
                    |source| source.located(variable_parse_position(error, syntax_attempt)),
                ),
                sort: sort.to_string(),
                // Read with the syntax module's grammar first and then the main module's, the
                // text is no value under either, so neither failure alone says why.
                message: syntax_attempt.map_or_else(
                    || error.to_string(),
                    |syntax_attempt| {
                        format!(
                            "syntax module attempt: {syntax_attempt}; main module attempt: {error}"
                        )
                    },
                ),
            }
        }
        Error::Missing { names: missing } => ExecError::MissingVariables(
            variables
                .iter()
                .filter(|variable| {
                    missing
                        .iter()
                        .any(|name| name.trim_start_matches('$') == variable.name)
                })
                .cloned()
                .collect(),
        ),
        other => ExecError::Backend(other.to_string()),
    }
}

/// Whether `value` is data: no opaque part and no application of a function, so that it is its
/// own value and two such values are equal exactly when they are the same value.
fn is_data(values: &ValueIndex, value: &Value) -> bool {
    match value {
        Value::Ctor(ctor) => {
            values.info(ctor.decl()).is_some_and(|info| !info.function)
                && ctor
                    .fields()
                    .iter()
                    .all(|(_, field)| is_data(values, field))
        }
        Value::Seq(items) | Value::List(items) => items.iter().all(|item| is_data(values, item)),
        Value::Set(items) => items.iter().all(|item| is_data(values, item)),
        Value::Map(entries) => entries
            .iter()
            .all(|(key, value)| is_data(values, key) && is_data(values, value)),
        Value::Opaque(_) => false,
        Value::Int(_)
        | Value::Bool(_)
        | Value::String(_)
        | Value::Bytes(_)
        | Value::Float(_)
        | Value::Token { .. } => true,
    }
}

#[cfg(test)]
mod tests;
