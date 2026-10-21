//! The executor: one definition's backend, its normal-termination matcher, and the judgement of
//! every leaf of a case (ARCHITECTURE 5.1, 5.2).

use k_rust::{
    backend::{
        Backend, BackendDiagnosticOutput, BackendError, CancellationToken, ChosenValueOutput,
        ContradictedClaimOutput, ExecuteRequest, ExecutionLeaf, ExecutionResult, HaltReasonOutput,
        ObservedInOutput, ObservedRequest, StopCause, search::prepare_backend_match_target,
    },
    definition::{AttributeKey, Attributes, ResolvedDefinition},
    k_rust_backend::{
        definition::BackendDefinition,
        evaluation::{EvaluationMode, with_evaluation},
        rewrite::Pattern,
        search::{PatternMatch, PatternMatchError, match_disjunction_with_solver},
        simplify::SimplificationOptions,
        smt::{SmtError, SmtSolver},
        stop::Stoppable,
        term::{HeadRole, Term},
    },
    kompile::{CompiledSearchPattern, ProgramGrammar, compile_search_pattern},
    kore::{ast::Pattern as KorePattern, codec},
};

use super::{
    Abort, CaseFailure, CaseRequestShape, CaseResult, FailureCause, LOAD_ALLOWANCE_REFUSAL,
    LOAD_STACK_STOP, LeafReport, UncleanReason,
};
use crate::{
    assemble::ProgramAssembly,
    error::CampaignError,
    report::LoadRecord,
    spec::{CaseOptions, CompiledDefinition},
};

/// The default normal-termination pattern: an empty `<k>` cell, the rest of the configuration
/// free (ARCHITECTURE 5.2, R-2).
const DEFAULT_NORMAL_END: &str = "<k> .K </k>";

/// Compiles surface patterns (krun's `--pattern` syntax) against one definition: the program
/// grammar parses them and the execution definition, resolved once here, gives them their
/// meaning (`compile_search_pattern`). The result is backend-independent KORE, so a campaign
/// compiles each pattern once and prepares it on every fresh backend ([`LeafMatcher::prepare`];
/// FZ-06's confirmation request).
pub(crate) struct PatternCompiler {
    execution_resolved: ResolvedDefinition,
    main_module: String,
}

impl PatternCompiler {
    /// Resolve `definition`'s execution definition.
    ///
    /// # Errors
    ///
    /// [`CampaignError::Definition`] when it does not resolve.
    pub(crate) fn new(definition: &CompiledDefinition) -> Result<Self, CampaignError> {
        let execution_resolved = ResolvedDefinition::resolve(&definition.execution_definition)
            .map_err(|error| CampaignError::Definition {
                message: format!("the execution definition does not resolve: {error}"),
            })?;
        Ok(Self {
            execution_resolved,
            main_module: definition.main_module.clone(),
        })
    }

    /// Compile `pattern` (`requires` allowed) with the program grammar `grammar`.
    ///
    /// # Errors
    ///
    /// The compiler's message.
    pub(crate) fn compile(
        &self,
        grammar: &ProgramGrammar,
        pattern: &str,
    ) -> Result<CompiledPattern, String> {
        compile_search_pattern(
            grammar.resolved(),
            &self.execution_resolved,
            &self.main_module,
            pattern,
            pattern_attributes(pattern),
        )
        .map(|search| CompiledPattern { search })
        .map_err(|error| error.to_string())
    }

    /// Compile the normal-termination pattern of `options`: the given one, or `<k> .K </k>`.
    ///
    /// # Errors
    ///
    /// [`CampaignError::NormalEndPattern`] when it does not compile.
    pub(crate) fn normal_end(
        &self,
        grammar: &ProgramGrammar,
        options: &CaseOptions,
    ) -> Result<NormalEnd, CampaignError> {
        let (text, default) = match options.normal_end_pattern.as_deref() {
            Some(pattern) => (pattern, false),
            None => (DEFAULT_NORMAL_END, true),
        };
        let pattern = self
            .compile(grammar, text)
            .map_err(|message| CampaignError::NormalEndPattern { message })?;
        Ok(NormalEnd { pattern, default })
    }
}

/// A compiled surface pattern, independent of any backend.
#[derive(Clone, Debug)]
pub(crate) struct CompiledPattern {
    search: CompiledSearchPattern,
}

impl CompiledPattern {
    /// The compiled KORE pattern: the configuration and its `requires` (the dictionary reads
    /// a pattern target's literals from it, ARCHITECTURE 8.3).
    pub(crate) fn kore(&self) -> &KorePattern {
        &self.search.pattern
    }
}

/// A campaign's compiled normal-termination pattern.
#[derive(Clone, Debug)]
pub(crate) struct NormalEnd {
    pattern: CompiledPattern,
    /// It is the default `<k> .K </k>`, which applies only to a configuration with exactly one
    /// `<k>` cell.
    default: bool,
}

/// A pattern prepared for leaf matching in one definition: `compile_search_pattern` over the
/// program grammar and the execution definition, then `prepare_backend_match_target`
/// (ARCHITECTURE 4.1, 5.2; `crates/k-rust/src/backend/execution.rs:1673-1686`). It holds
/// internal terms of one backend's definition, so it is used only with the [`Executor`] whose
/// backend prepared it.
///
/// The prepared target is kept across cases rather than prepared again in every case
/// (`workers/interfaces.md`, question 3): it is built from the author's pattern text and the
/// configuration's cells, and every operation that matches it passes its KORE form to
/// `Backend::with_solver_over`, so the operation's stack is measured for it too.
pub(crate) struct LeafMatcher {
    /// The backend-independent compiled pattern this matcher was prepared from, which another
    /// backend of the same definition can prepare again ([`Self::compiled`]).
    compiled: CompiledPattern,
    /// The compiled KORE pattern, for the depth `with_solver_over` measures.
    kore: KorePattern,
    /// The prepared internal target.
    target: Pattern,
    /// The target has no constraints and every application in it has a free-constructor head,
    /// so matching it evaluates nothing and its verdict is the same in every evaluation mode.
    mode_independent: bool,
}

impl LeafMatcher {
    /// Compile `pattern` (krun's `--pattern` surface syntax, `requires` allowed) for leaves of
    /// `executor`'s backend.
    ///
    /// # Errors
    ///
    /// The compiler's or backend's message.
    pub(crate) fn compile(
        executor: &mut Executor,
        definition: &CompiledDefinition,
        assembly: &ProgramAssembly,
        pattern: &str,
    ) -> Result<Self, String> {
        Self::compile_with(executor, assembly.grammar(), definition, pattern)
    }

    /// [`Self::compile`] with the program grammar given directly: [`Executor::compile_pattern`],
    /// then [`Self::prepare`].
    ///
    /// # Errors
    ///
    /// The compiler's or backend's message.
    pub(crate) fn compile_with(
        executor: &mut Executor,
        grammar: &ProgramGrammar,
        definition: &CompiledDefinition,
        pattern: &str,
    ) -> Result<Self, String> {
        let compiled = executor.compile_pattern(grammar, definition, pattern)?;
        Self::prepare(executor, &compiled)
    }

    /// Prepare a compiled pattern on `executor`'s backend (`prepare_backend_match_target`).
    ///
    /// # Errors
    ///
    /// The backend's message.
    pub(crate) fn prepare(
        executor: &mut Executor,
        pattern: &CompiledPattern,
    ) -> Result<Self, String> {
        prepare_matcher(&mut executor.backend, pattern)
    }

    /// The backend-independent compiled pattern this matcher was prepared from.
    pub(crate) fn compiled(&self) -> &CompiledPattern {
        &self.compiled
    }
}

/// The attributes krun gives a command-line pattern (`crates/k-rust/src/main.rs`,
/// `command_line_pattern_attributes`): source `<command line>`, a location spanning the text.
fn pattern_attributes(contents: &str) -> Attributes {
    let mut end_line = 1_u32;
    let mut end_column = 1_u32;
    for character in contents.chars() {
        if character == '\n' {
            end_line += 1;
            end_column = 1;
        } else {
            end_column += 1;
        }
    }
    let mut attributes = Attributes::default();
    attributes.set(AttributeKey::Source, serde_json::json!("<command line>"));
    attributes.set(AttributeKey::SourceId, serde_json::json!(0));
    attributes.set(
        AttributeKey::Location,
        serde_json::json!([1, 1, end_line, end_column]),
    );
    attributes.set(AttributeKey::ContentStartOffset, serde_json::json!(0));
    attributes.set(AttributeKey::ContentStartLine, serde_json::json!(1));
    attributes.set(AttributeKey::ContentStartColumn, serde_json::json!(1));
    attributes
}

fn prepare_matcher(
    backend: &mut Backend,
    pattern: &CompiledPattern,
) -> Result<LeafMatcher, String> {
    let compiled = pattern.search.clone();
    let kore = compiled.pattern.clone();
    let (target, mode_independent) = backend
        .with_solver_over(None, &[&kore], |definition, _solver| {
            let target = prepare_backend_match_target(definition, compiled)
                .map_err(|error| BackendError::new(error.to_string()))?;
            let independent = target.pattern.constraints.is_empty()
                && only_free_constructors(&target.pattern.term);
            Ok::<_, BackendError>((target.pattern, independent))
        })
        .map_err(|error| error.to_string())?;
    Ok(LeafMatcher {
        compiled: pattern.clone(),
        kore,
        target,
        mode_independent,
    })
}

/// Whether every application in `term` has a free-constructor head (collections and domain
/// values have none).
fn only_free_constructors(term: &Term) -> bool {
    let mut free = true;
    term.visit_symbols(&mut |symbol| {
        free &= symbol.attributes.head_role() == HeadRole::FreeConstructor;
    });
    free
}

/// One definition's backend and normal-termination matcher; runs and judges cases.
pub(crate) struct Executor {
    backend: Backend,
    normal_end: LeafMatcher,
    /// The normal-termination pattern is the default `<k> .K </k>`.
    default_normal_end: bool,
    /// The pattern compiler, built on the first [`Self::compile_pattern`] when the executor was
    /// built from a compiled normal-end pattern without one.
    compiler: Option<PatternCompiler>,
    max_simplification_iterations: usize,
    /// Stops for lack of stack in the definition's load (ARCHITECTURE 5.4).
    load_stack_stops: usize,
    /// The per-case safety limit, in milliseconds; wasm32 refuses it, so there it is never set.
    #[cfg(not(target_arch = "wasm32"))]
    safety_limit_ms: Option<u64>,
    #[cfg(not(target_arch = "wasm32"))]
    watchdog: Option<super::watchdog::Watchdog>,
}

impl Executor {
    #[cfg(test)]
    /// Build the backend on `definition`'s route ([`crate::assemble::build_backend`]) and
    /// compile the normal-termination pattern of `options` (`<k> .K </k>` with the rest free
    /// when absent, which needs exactly one `<k>` cell; ARCHITECTURE 5.2, R-2).
    ///
    /// # Errors
    ///
    /// [`CampaignError::Definition`] when the backend cannot be built;
    /// [`CampaignError::NormalEndPattern`] when the pattern is missing or does not compile;
    /// [`CampaignError::InvalidOptions`] for a safety limit on wasm32, which has no threads.
    pub(crate) fn new(
        definition: &CompiledDefinition,
        assembly: &ProgramAssembly,
        options: &CaseOptions,
    ) -> Result<Self, CampaignError> {
        let backend = crate::assemble::build_backend(definition, options.backend.options())?;
        Self::with_backend(backend, assembly.grammar(), definition, options)
    }

    #[cfg(test)]
    /// [`Self::new`] over a backend the caller built on `definition`'s route, with the program
    /// grammar given directly.
    ///
    /// # Errors
    ///
    /// As [`Self::new`], but for building the backend.
    pub(crate) fn with_backend(
        backend: Backend,
        grammar: &ProgramGrammar,
        definition: &CompiledDefinition,
        options: &CaseOptions,
    ) -> Result<Self, CampaignError> {
        let compiler = PatternCompiler::new(definition)?;
        let normal_end = compiler.normal_end(grammar, options)?;
        Ok(Self::with_normal_end(backend, &normal_end, options)?.with_compiler(compiler))
    }

    /// This executor, with `compiler` (built for its definition) as the compiler of
    /// [`Self::compile_pattern`], so that the execution definition is not resolved again.
    #[must_use]
    pub(crate) fn with_compiler(mut self, compiler: PatternCompiler) -> Self {
        self.compiler = Some(compiler);
        self
    }

    /// Compile `pattern` (krun's `--pattern` surface syntax, `requires` allowed) with the program
    /// grammar `grammar`, backend-independently ([`PatternCompiler::compile`]). An executor built
    /// without a compiler resolves `definition`'s execution definition on its first call.
    ///
    /// # Errors
    ///
    /// The compiler's message.
    pub(crate) fn compile_pattern(
        &mut self,
        grammar: &ProgramGrammar,
        definition: &CompiledDefinition,
        pattern: &str,
    ) -> Result<CompiledPattern, String> {
        if self.compiler.is_none() {
            self.compiler =
                Some(PatternCompiler::new(definition).map_err(|error| error.to_string())?);
        }
        self.compiler
            .as_ref()
            .expect("the compiler was just built")
            .compile(grammar, pattern)
    }

    /// An executor over a backend the caller built on the definition's route, with the
    /// normal-termination pattern compiled once per campaign ([`PatternCompiler::normal_end`]);
    /// only its preparation on this backend runs here. Confirmations use it with a fresh backend
    /// (FZ-06's request).
    ///
    /// # Errors
    ///
    /// [`CampaignError::Definition`] when the main module does not load;
    /// [`CampaignError::NormalEndPattern`] when the pattern does not prepare on this backend;
    /// [`CampaignError::InvalidOptions`] for a safety limit on wasm32, which has no threads.
    pub(crate) fn with_normal_end(
        mut backend: Backend,
        normal_end: &NormalEnd,
        options: &CaseOptions,
    ) -> Result<Self, CampaignError> {
        #[cfg(target_arch = "wasm32")]
        if options.safety_limit_ms.is_some() {
            return Err(CampaignError::InvalidOptions {
                message: "the per-case safety limit needs a watchdog thread, which this \
                          WebAssembly build does not have"
                    .to_owned(),
            });
        }
        let loaded =
            backend
                .select_definition(None)
                .map_err(|error| CampaignError::Definition {
                    message: format!("the main module does not load: {error}"),
                })?;
        let load_stack_stops = load_stack_stops(&loaded);
        drop(loaded);
        let prepared = prepare_matcher(&mut backend, &normal_end.pattern)
            .map_err(|message| CampaignError::NormalEndPattern { message })?;
        Ok(Self {
            backend,
            normal_end: prepared,
            default_normal_end: normal_end.default,
            compiler: None,
            max_simplification_iterations: options.max_simplification_iterations,
            load_stack_stops,
            #[cfg(not(target_arch = "wasm32"))]
            safety_limit_ms: options.safety_limit_ms,
            #[cfg(not(target_arch = "wasm32"))]
            watchdog: options
                .safety_limit_ms
                .map(|_| super::watchdog::Watchdog::new()),
        })
    }

    /// The backend, for target resolution (`rule_catalog`) and pattern compilation.
    pub(crate) fn backend_mut(&mut self) -> &mut Backend {
        &mut self.backend
    }

    /// Execute `initial` with `shape` through `Backend::execute`, within `cancel`'s scope and
    /// the per-case safety limit, then judge every leaf: clean (ARCHITECTURE 5.2), natural end,
    /// and each of `matchers` (prepared by this executor). Load-time records go to
    /// [`CaseResult::load_records`], never onto leaves. An `Err` result becomes
    /// [`CaseResult::failure`] with its cause.
    ///
    /// # Errors
    ///
    /// [`Abort`] for a failed solver prelude.
    pub(crate) fn run(
        &mut self,
        initial: &KorePattern,
        shape: &CaseRequestShape,
        matchers: &[&LeafMatcher],
        cancel: Option<&CancellationToken>,
    ) -> Result<CaseResult, Abort> {
        self.run_with(initial, shape, matchers, cancel, Execution::Plain)
            .map(|(result, _)| result)
    }

    /// [`Self::run`] through `Backend::execute_observed` with the event allowlist `rules`, in the
    /// same token scope, safety limit and work budget, so that an observer case runs once
    /// (FZ-10's request). `execute_observed` answers the same leaves in the same order as
    /// `execute`; the raw observed leaves (branch identities and observations) are returned
    /// beside the judged result, empty when the result is a failure.
    ///
    /// # Errors
    ///
    /// [`Abort`] for a failed solver prelude.
    pub(crate) fn run_observed(
        &mut self,
        initial: &KorePattern,
        shape: &CaseRequestShape,
        matchers: &[&LeafMatcher],
        cancel: Option<&CancellationToken>,
        rules: Option<Vec<String>>,
    ) -> Result<(CaseResult, Vec<ExecutionLeaf>), Abort> {
        self.run_with(
            initial,
            shape,
            matchers,
            cancel,
            Execution::Observed { rules },
        )
    }

    fn run_with(
        &mut self,
        initial: &KorePattern,
        shape: &CaseRequestShape,
        matchers: &[&LeafMatcher],
        cancel: Option<&CancellationToken>,
        execution: Execution,
    ) -> Result<(CaseResult, Vec<ExecutionLeaf>), Abort> {
        let request = shape.request(initial.clone());
        let judge = Judge {
            normal_end: &self.normal_end,
            default_normal_end: self.default_normal_end,
            matchers,
            options: SimplificationOptions {
                max_iterations: self.max_simplification_iterations,
                ..SimplificationOptions::default()
            },
            constructor_only: shape.constructor_only,
            terminal_allowed: shape.has_terminal_rules(),
            load_stack_stops: self.load_stack_stops,
            forward: None,
        };
        let backend = &mut self.backend;
        #[cfg(not(target_arch = "wasm32"))]
        if let (Some(limit), Some(watchdog)) = (self.safety_limit_ms, self.watchdog.as_ref()) {
            let token = CancellationToken::new();
            // The watchdog thread forwards the caller's cancellation while the case runs; the
            // checks at the start and at the end make it take effect whatever the thread's
            // scheduling (review S2).
            if cancel.is_some_and(CancellationToken::is_cancelled) {
                token.cancel();
            }
            let armed = watchdog.arm(
                token.clone(),
                std::time::Duration::from_millis(limit),
                cancel.cloned(),
            );
            let judge = Judge {
                forward: cancel.map(|caller| (caller.clone(), token.clone())),
                ..judge
            };
            let outcome = token.scope(|| judge.execute(backend, request, execution));
            // A deadline that passes after the run returned and before this disarm still marks
            // the case `timeout` though its result is complete: conservative (review N3).
            let fired = armed.disarm();
            return outcome.map(|(mut result, leaves)| {
                result.safety_limit_hit = fired;
                (result, leaves)
            });
        }
        match cancel {
            Some(token) => token.scope(|| judge.execute(backend, request, execution)),
            None => judge.execute(backend, request, execution),
        }
    }
}

#[cfg(test)]
impl Executor {
    /// The internal judgement's reasons for `state` as a `stuck` leaf, for tests of the
    /// clean-leaf rule on states no run produces.
    pub(super) fn judge_stuck_state(&mut self, state: KorePattern) -> Vec<UncleanReason> {
        let leaf = LeafReport {
            halt: HaltReasonOutput::Stuck,
            depth: 0,
            state,
            unclean: Vec::new(),
            natural_end: false,
            matches: Vec::new(),
            rewrites: Vec::new(),
            constructor_only: None,
        };
        let judge = Judge {
            normal_end: &self.normal_end,
            default_normal_end: self.default_normal_end,
            matchers: &[],
            options: SimplificationOptions::default(),
            constructor_only: false,
            terminal_allowed: false,
            load_stack_stops: 0,
            forward: None,
        };
        let mut internal = judge
            .judge_internally(&mut self.backend, std::slice::from_ref(&leaf))
            .expect("the judgement runs");
        internal.pop().expect("one leaf").reasons
    }
}

/// Load-time stops for lack of stack of a loaded definition (`docs/compatibility.md`,
/// "Determinism and concurrency").
fn load_stack_stops(definition: &BackendDefinition) -> usize {
    definition.value_claims().counts().condition_stack_stops
        + definition.discharge_counts().stack_stops
}

/// How a case is executed.
enum Execution {
    /// `Backend::execute`.
    Plain,
    /// `Backend::execute_observed` with the observation filter `rules` (every event when
    /// `None`).
    Observed { rules: Option<Vec<String>> },
}

/// What one case's judgement needs besides the backend.
struct Judge<'a> {
    normal_end: &'a LeafMatcher,
    default_normal_end: bool,
    matchers: &'a [&'a LeafMatcher],
    options: SimplificationOptions,
    constructor_only: bool,
    terminal_allowed: bool,
    load_stack_stops: usize,
    /// Under the safety limit, the caller's token and the case's own: the caller's cancellation
    /// is forwarded synchronously when the run ends, before the leaves are judged (review S2).
    forward: Option<(CancellationToken, CancellationToken)>,
}

/// A leaf pattern's verdict on one leaf.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum MatchVerdict {
    Matched,
    NotMatched,
    /// Undecided, matched only under constraints, or matched in execution mode only.
    Undecided,
}

/// What the internal judgement found on one leaf.
#[derive(Debug, Default)]
struct Internal {
    reasons: Vec<UncleanReason>,
    /// The normal-termination pattern matched (a `stuck` leaf whose state was decided).
    normal_end: bool,
    matches: Vec<bool>,
    constructor_only: Option<bool>,
    /// Solver `unknown`s the leaf's matching met, in either evaluation mode (review 2, NI-2).
    smt_unknowns: usize,
}

impl Judge<'_> {
    fn execute(
        &self,
        backend: &mut Backend,
        request: ExecuteRequest,
        execution: Execution,
    ) -> Result<(CaseResult, Vec<ExecutionLeaf>), Abort> {
        let executed = match execution {
            Execution::Plain => backend.execute(request),
            Execution::Observed { rules } => {
                backend.execute_observed(ObservedRequest { request, rules })
            }
        };
        if let Some((caller, case)) = &self.forward
            && caller.is_cancelled()
        {
            case.cancel();
        }
        match executed {
            Ok(result) => {
                let judged = self.judge(backend, &result)?;
                Ok((judged, result.leaves))
            }
            Err(error) => Ok((self.failed(failure_of(&error)?), Vec::new())),
        }
    }

    /// A case whose execution or judgement answered `Err`.
    fn failed(&self, failure: CaseFailure) -> CaseResult {
        CaseResult {
            leaves: Vec::new(),
            work: 0,
            coverage: None,
            stack_stops: 0,
            smt_unknowns: 0,
            run_allowance_refusals: 0,
            load_records: self.load_stack_stop_record().into_iter().collect(),
            safety_limit_hit: false,
            failure: Some(failure),
            run_facts_off_leaves: false,
        }
    }

    fn load_stack_stop_record(&self) -> Option<LoadRecord> {
        (self.load_stack_stops > 0).then(|| LoadRecord {
            kind: LOAD_STACK_STOP.to_owned(),
            detail: format!(
                "{} stops for lack of stack in the definition's load",
                self.load_stack_stops
            ),
        })
    }

    fn judge(&self, backend: &mut Backend, result: &ExecutionResult) -> Result<CaseResult, Abort> {
        let run_allowance_refusals = result
            .allowance_refusals
            .iter()
            .filter(|refusal| refusal.observed_in == ObservedInOutput::Run)
            .count();
        let mut run_reasons = Vec::new();
        if result.stack_stops > 0 {
            run_reasons.push(UncleanReason::StackStops);
        }
        if result.smt_unknowns > 0 {
            run_reasons.push(UncleanReason::SmtUnknowns);
        }
        if run_allowance_refusals > 0 {
            run_reasons.push(UncleanReason::AllowanceRefusal);
        }
        // D21: an application left unevaluated as an unsupported hook can steer the equation
        // evaluator, which applies another equation of the priority group when a condition over
        // it is undecided (FZ-08 review 2, `steer.k`), and no leaf records the choice.
        if result
            .unsupported_hooks
            .iter()
            .any(|hook| hook.observed_in == ObservedInOutput::Run)
        {
            run_reasons.push(UncleanReason::UnsupportedHook);
        }
        let mut leaves = Vec::with_capacity(result.leaves.len());
        for (index, leaf) in result.leaves.iter().enumerate() {
            let Ok(state) = codec::from_value(&leaf.state) else {
                return Ok(self.failed(CaseFailure::other(format!(
                    "the state of leaf {index} does not decode as KORE"
                ))));
            };
            let mut unclean = run_reasons.clone();
            unclean.extend(self.leaf_reasons(leaf));
            leaves.push(LeafReport {
                halt: leaf.reason,
                depth: leaf.depth,
                state,
                unclean,
                natural_end: false,
                matches: vec![false; self.matchers.len()],
                rewrites: established_rewrites(leaf),
                constructor_only: None,
            });
        }
        let internal = match self.judge_internally(backend, &leaves) {
            Ok(internal) => internal,
            Err(error) => return Ok(self.failed(failure_of(&error)?)),
        };
        let mut smt_unknowns = result.smt_unknowns;
        for (leaf, internal) in leaves.iter_mut().zip(internal) {
            smt_unknowns = smt_unknowns.saturating_add(internal.smt_unknowns);
            leaf.unclean.extend(internal.reasons);
            leaf.unclean.sort();
            leaf.unclean.dedup();
            leaf.natural_end = leaf.is_clean() && internal.normal_end;
            leaf.matches = internal.matches;
            leaf.constructor_only = internal.constructor_only;
        }
        let run_facts_off_leaves = run_facts_off_leaves(result);
        let mut load_records = load_records(result);
        load_records.extend(self.load_stack_stop_record());
        Ok(CaseResult {
            leaves,
            work: result.work,
            coverage: result.coverage.clone(),
            stack_stops: result.stack_stops,
            smt_unknowns,
            run_allowance_refusals,
            load_records,
            safety_limit_hit: false,
            failure: None,
            run_facts_off_leaves,
        })
    }

    /// The reasons a leaf's halt and its own diagnostics give (ARCHITECTURE 5.2).
    #[deny(clippy::wildcard_enum_match_arm)]
    fn leaf_reasons(&self, leaf: &ExecutionLeaf) -> Vec<UncleanReason> {
        let mut reasons = Vec::new();
        let end = match leaf.reason {
            HaltReasonOutput::Stuck => true,
            HaltReasonOutput::Terminal => self.terminal_allowed,
            HaltReasonOutput::Cancelled
            | HaltReasonOutput::Trivial
            | HaltReasonOutput::Vacuous
            | HaltReasonOutput::Branch
            | HaltReasonOutput::CutPoint
            | HaltReasonOutput::DepthBound
            | HaltReasonOutput::BreadthBound
            | HaltReasonOutput::WorkBound
            | HaltReasonOutput::Indeterminate
            | HaltReasonOutput::UnsupportedHook
            | HaltReasonOutput::SimplificationError
            | HaltReasonOutput::Timeout => false,
        };
        if !end {
            reasons.push(UncleanReason::Halt);
        }
        for diagnostic in &leaf.diagnostics {
            match diagnostic {
                BackendDiagnosticOutput::ImplementationChosenValue { .. } => {
                    reasons.push(UncleanReason::ImplementationChosenValue);
                }
                // A leaf carries the run's records only; a load record on a leaf would contradict
                // the backend's contract, and counting it is the conservative reading.
                BackendDiagnosticOutput::ContradictedClaim(_) => {
                    reasons.push(UncleanReason::ContradictedClaim);
                }
                BackendDiagnosticOutput::SimplificationBudgetExhausted { .. }
                | BackendDiagnosticOutput::RuleConditionUnsimplified { .. } => {
                    reasons.push(UncleanReason::IterationExhaustion);
                }
                BackendDiagnosticOutput::RuleConditionFailed { .. } => {
                    reasons.push(UncleanReason::SimplificationFailure);
                }
                // The initial configuration is defined only where these obligations hold, and
                // the backend keeps them in `ExecutionState::defined_where`, never in the
                // leaf's constraints: an instance where they fail has no run at all (review B2).
                BackendDiagnosticOutput::UndefinedInitialInstances { .. } => {
                    reasons.push(UncleanReason::Undecided);
                }
                // An undecided condition or predicate, or an unevaluated hook, leaves a function
                // application or a constraint. A partial application is not `ceil_free`, and a
                // constraint makes the leaf undecided. A total one is ceil-free and denotes a
                // value: no rewrite rule and no leaf matcher refutes a function-headed subject
                // (`k_rust_backend::matching`), so a step that needs its value halts
                // `indeterminate`, and a target `requires` that reads it is refused as an
                // uncomputed application (`k_rust_backend::search`), so neither can rest on it
                // (review N1).
                BackendDiagnosticOutput::UndecidedCondition { .. }
                | BackendDiagnosticOutput::UndecidedPredicate { .. }
                | BackendDiagnosticOutput::UnsupportedHookUnevaluated { .. } => {}
            }
        }
        reasons
    }

    /// Internalize every leaf in its definition and judge it: decided, ceil-free, natural end,
    /// each matcher, constructor-only. One operation over every leaf state and every matcher.
    fn judge_internally(
        &self,
        backend: &mut Backend,
        leaves: &[LeafReport],
    ) -> Result<Vec<Internal>, BackendError> {
        let mut patterns: Vec<&KorePattern> = leaves.iter().map(|leaf| &leaf.state).collect();
        patterns.push(&self.normal_end.kore);
        patterns.extend(self.matchers.iter().map(|matcher| &matcher.kore));
        backend.with_solver_over(None, &patterns, |definition, solver| {
            leaves
                .iter()
                .map(|leaf| self.judge_leaf(definition, solver, leaf))
                .collect()
        })
    }

    fn judge_leaf(
        &self,
        definition: &BackendDefinition,
        solver: &dyn SmtSolver,
        leaf: &LeafReport,
    ) -> Result<Internal, BackendError> {
        let mut internal = Internal {
            matches: vec![false; self.matchers.len()],
            ..Internal::default()
        };
        // The ends of a path: a hit, a comparison, a set of ends or a `pattern at: final` match
        // may rest on these (D16).
        let end_like = matches!(
            leaf.halt,
            HaltReasonOutput::Stuck | HaltReasonOutput::Terminal | HaltReasonOutput::Trivial
        );
        // A depth or breadth cut leaves a state in the simplifier's normal form, which may carry
        // a reach under `run-to-completion`; it must be clean apart from its halt to be
        // `reached-unfinished` (review S1). A `work-bound`, `timeout` or `cancelled` leaf holds
        // the stopped state as taken from the worklist, unexpanded and unnormalised, which is not
        // a reached result (`HaltReasonOutput::WorkBound`), so its state is not judged: such a
        // leaf can be reached only through its path's trace.
        let judged = end_like
            || matches!(
                leaf.halt,
                HaltReasonOutput::DepthBound | HaltReasonOutput::BreadthBound
            );
        if !judged {
            return Ok(internal);
        }
        let pattern = match definition
            .admit_unverified(&leaf.state, &[])
            .internalize_pattern()
        {
            Ok(pattern) => pattern,
            Err(error) => {
                internal
                    .reasons
                    .push(UncleanReason::Internalization(error.to_string()));
                return Ok(internal);
            }
        };
        let attributes = pattern.term.attributes();
        let decided = pattern.constraints.is_empty() && attributes.variables.is_empty();
        if !decided {
            internal.reasons.push(UncleanReason::Undecided);
        }
        if !attributes.ceil_free() {
            internal.reasons.push(UncleanReason::NotCeilFree);
        }
        if !decided || !end_like {
            return Ok(internal);
        }
        if self.constructor_only {
            internal.constructor_only = Some(attributes.constructor_like);
        }
        if leaf.halt == HaltReasonOutput::Stuck {
            if self.default_normal_end && attributes.k_cells() != 1 {
                internal.reasons.push(UncleanReason::NaturalEndUndecided);
            } else {
                match self.match_leaf(
                    definition,
                    solver,
                    self.normal_end,
                    &pattern,
                    &mut internal,
                )? {
                    MatchVerdict::Matched => internal.normal_end = true,
                    MatchVerdict::NotMatched => {}
                    MatchVerdict::Undecided => {
                        internal.reasons.push(UncleanReason::NaturalEndUndecided);
                    }
                }
            }
        }
        for (index, matcher) in self.matchers.iter().enumerate() {
            match self.match_leaf(definition, solver, matcher, &pattern, &mut internal)? {
                MatchVerdict::Matched => internal.matches[index] = true,
                MatchVerdict::NotMatched => {}
                MatchVerdict::Undecided => internal.reasons.push(UncleanReason::UndecidedMatch),
            }
        }
        Ok(internal)
    }

    /// Match `subject` against `matcher` as `krun --pattern` does, in execution mode; a match
    /// counts only with empty constraints. A target that evaluates something (it has
    /// constraints, or a head that is not a free constructor) is also matched in proof mode,
    /// where a value the definition leaves to the implementation stays unevaluated, and the two
    /// verdicts must agree: `Matched` only when both match, `NotMatched` only when both refute,
    /// `Undecided` otherwise (D16, review B1). The matcher reports no path facts, so this is how
    /// a verdict resting on k-rust's chosen value is caught in either direction. A verdict
    /// resting on a contradicted claim met while the target's `requires` is evaluated is not
    /// caught: k-rust reads the undefined value as undefined in both modes
    /// (GAP-REQUIRES-CLAIMS, review S4).
    fn match_leaf(
        &self,
        definition: &BackendDefinition,
        solver: &dyn SmtSolver,
        matcher: &LeafMatcher,
        subject: &Pattern,
        internal: &mut Internal,
    ) -> Result<MatchVerdict, BackendError> {
        let run = |mode| {
            with_evaluation(mode, || {
                match_disjunction_with_solver(
                    definition,
                    &matcher.target,
                    std::slice::from_ref(subject),
                    self.options,
                    solver,
                )
            })
        };
        let mut decide = |outcome| {
            let (verdict, unknown) = verdict(outcome)?;
            internal.smt_unknowns += usize::from(unknown);
            Ok::<_, BackendError>(verdict)
        };
        let execution = decide(run(EvaluationMode::Execution))?;
        if matcher.mode_independent || execution == MatchVerdict::Undecided {
            return Ok(execution);
        }
        let proof = decide(run(EvaluationMode::Proof))?;
        Ok(if proof == execution {
            execution
        } else {
            MatchVerdict::Undecided
        })
    }
}

/// A matcher outcome's verdict, and whether the matcher met a solver `unknown`, which depends on
/// the clock (review 2, NI-2).
pub(super) fn verdict(
    outcome: Stoppable<Result<Vec<PatternMatch>, PatternMatchError>>,
) -> Result<(MatchVerdict, bool), BackendError> {
    Ok(
        match outcome.map_err(|stop| BackendError::from(stop.into_cause()))? {
            Ok(matches) if matches.iter().any(|found| found.constraints.is_empty()) => {
                (MatchVerdict::Matched, false)
            }
            Ok(matches) if matches.is_empty() => (MatchVerdict::NotMatched, false),
            Err(PatternMatchError::Smt(SmtError::Unknown(_))) => (MatchVerdict::Undecided, true),
            Ok(_) | Err(_) => (MatchVerdict::Undecided, false),
        },
    )
}

/// The unique ids of a leaf's `Rewrite` trace entries whose step results exist. A `work-bound`,
/// `timeout` or `cancelled` leaf holds the state where exploration stopped, as taken from the
/// worklist, unexpanded and unnormalised: its last rewrite built that state, which may still
/// normalize to `\bottom` (an undefined step, or a candidate a sibling covers), so that entry
/// is not established and is left out (review 2, S1). Every earlier entry built a state that
/// the run went on to step.
pub(super) fn established_rewrites(leaf: &ExecutionLeaf) -> Vec<String> {
    let mut rewrites: Vec<String> = leaf
        .trace
        .iter()
        .filter(|entry| entry.kind == "rewrite")
        .map(|entry| entry.unique_id.clone())
        .collect();
    if stopped_unnormalised(leaf.reason) {
        rewrites.pop();
    }
    rewrites
}

/// Whether a leaf of this halt holds an unexpanded, unnormalised stopped state, which is not a
/// reached result (`HaltReasonOutput::WorkBound`; a timeout or cancellation stops a state the
/// same way).
fn stopped_unnormalised(halt: HaltReasonOutput) -> bool {
    matches!(
        halt,
        HaltReasonOutput::WorkBound | HaltReasonOutput::Timeout | HaltReasonOutput::Cancelled
    )
}

/// The failure an `Err` stands for, or [`Abort`] for a failed solver prelude.
fn failure_of(error: &BackendError) -> Result<CaseFailure, Abort> {
    let message = error.message().to_owned();
    let cause = match error.stop_cause() {
        Some(StopCause::SolverPrelude(_)) => return Err(Abort { reason: message }),
        Some(cause) => FailureCause::Stop(cause.clone()),
        // `Backend::execute` validates and internalizes the state before it runs it.
        None if message.starts_with("invalid executable state")
            || message.starts_with("could not internalize execution state") =>
        {
            FailureCause::StateRefused
        }
        None => FailureCause::Other,
    };
    Ok(CaseFailure { message, cause })
}

/// The run-level records the definition's load observed (T-5), in the result's order.
fn load_records(result: &ExecutionResult) -> Vec<LoadRecord> {
    let mut records = Vec::new();
    for claim in &result.contradicted_claims {
        if claim.observed_in == ObservedInOutput::Load {
            let kind = serde_json::to_value(claim.claim)
                .ok()
                .and_then(|value| value.as_str().map(str::to_owned))
                .unwrap_or_default();
            let subject = claim.symbol.as_deref().unwrap_or(&claim.rule_id);
            records.push(LoadRecord {
                kind: "contradicted-claim".to_owned(),
                detail: format!("{kind} claim of {subject} (equation {})", claim.rule_id),
            });
        }
    }
    for (kind, hooks) in [
        (LOAD_ALLOWANCE_REFUSAL, &result.allowance_refusals),
        ("unsupported-hook", &result.unsupported_hooks),
    ] {
        for hook in hooks {
            if hook.observed_in == ObservedInOutput::Load {
                records.push(LoadRecord {
                    kind: kind.to_owned(),
                    detail: format!("{}: {}", hook.hook, hook.reason),
                });
            }
        }
    }
    records
}

/// Whether the run noted an implementation-chosen value or a contradicted claim (`observedIn:
/// run`) that no leaf's diagnostics carry (D16, review B3).
fn run_facts_off_leaves(result: &ExecutionResult) -> bool {
    let leaf_diagnostics = || result.leaves.iter().flat_map(|leaf| &leaf.diagnostics);
    facts_off_leaves(
        &result.implementation_chosen_values,
        &result.contradicted_claims,
        leaf_diagnostics,
    )
}

/// [`run_facts_off_leaves`] over the run's lists and the leaves' diagnostics.
pub(super) fn facts_off_leaves<'a, I>(
    chosen: &[ChosenValueOutput],
    claims: &[ContradictedClaimOutput],
    leaf_diagnostics: impl Fn() -> I,
) -> bool
where
    I: Iterator<Item = &'a BackendDiagnosticOutput>,
{
    let chosen_off = chosen.iter().any(|value| {
        !leaf_diagnostics().any(|diagnostic| {
            matches!(
                diagnostic,
                BackendDiagnosticOutput::ImplementationChosenValue { hook, class }
                    if *hook == value.hook && *class == value.class
            )
        })
    });
    let claim_off = claims
        .iter()
        .filter(|claim| claim.observed_in == ObservedInOutput::Run)
        .any(|claim| {
            !leaf_diagnostics().any(|diagnostic| {
                matches!(
                    diagnostic,
                    BackendDiagnosticOutput::ContradictedClaim(record) if record == claim
                )
            })
        });
    chosen_off || claim_off
}
