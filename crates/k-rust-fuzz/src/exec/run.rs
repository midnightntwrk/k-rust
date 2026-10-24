//! The executor: one definition's backend, its normal-termination matcher, and the judgement of
//! every leaf of a case (ARCHITECTURE 5.1, 5.2).

use k_rust::{
    backend::{
        Backend, BackendDiagnosticOutput, BackendError, CancellationToken, ChosenValueOutput,
        ContradictedClaimOutput, ExecuteRequest, ExecutionLeaf, ExecutionResult, HaltReasonOutput,
        ObservedInOutput, ObservedRequest, StopCause, search::prepare_backend_match_target,
    },
    definition::{AttributeKey, Attributes, ProductionItem, ResolvedDefinition, Sentence},
    k_rust_backend::{
        data_term::DataHeads,
        definition::BackendDefinition,
        evaluation::{EvaluationMode, with_evaluation},
        rewrite::Pattern,
        search::{PatternMatch, PatternMatchError, match_disjunction_with_solver},
        simplify::SimplificationOptions,
        smt::{SmtError, SmtSolver},
        stop::Stoppable,
        term::{FunctionType, HeadRole, SymbolType, Term, TermKind},
    },
    kompile::{CompiledSearchPattern, ProgramGrammar, compile_search_pattern},
    kore::{ast::Pattern as KorePattern, codec},
    names::{BuiltinSort, WellKnownSymbol},
};

use super::{
    Abort, CaseFailure, CaseRequestShape, CaseResult, FailureCause, LOAD_ALLOWANCE_REFUSAL,
    LOAD_STACK_STOP, LeafDiagnostic, LeafReport, NormalEndKind, UncleanReason, UnjudgedReason,
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
    /// The configuration's `<k>` cell lies under a cell of multiplicity `*` or `?`
    /// ([`k_under_multiplicity`]), so the default normal end is [`NormalEndKind::EveryK`].
    k_under_multiplicity: bool,
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
        let k_under_multiplicity =
            k_under_multiplicity(&execution_resolved, &definition.main_module);
        Ok(Self {
            execution_resolved,
            main_module: definition.main_module.clone(),
            k_under_multiplicity,
        })
    }

    /// Compile `pattern` (`requires` allowed) with the program grammar `grammar`.
    ///
    /// A pattern whose `requires` reads a variable that its configuration does not bind is
    /// refused ([`unbound_condition_variables`]). Such a variable is almost always a
    /// misspelling (of a variable the configuration names, or of a key), and a leaf's match
    /// then leaves a condition over it, which the leaf judgement decides only when it
    /// simplifies to true or false without the variable (`R ==Int R`, `... orBool true`) and
    /// classes as undecided (`unsupported`) otherwise. The refusal is a rule of use, not a
    /// fact that no leaf could match: it refuses a few patterns some leaves would match.
    /// (`krust krun --pattern` answers such a match with the remaining condition in its result
    /// instead.)
    ///
    /// # Errors
    ///
    /// The compiler's message, or the refusal naming the unbound variables.
    pub(crate) fn compile(
        &self,
        grammar: &ProgramGrammar,
        pattern: &str,
    ) -> Result<CompiledPattern, String> {
        let search = compile_search_pattern(
            grammar.resolved(),
            &self.execution_resolved,
            &self.main_module,
            pattern,
            pattern_attributes(pattern),
        )
        .map_err(|error| relocate_positions(&error.to_string()))?;
        let unbound = unbound_condition_variables(&search);
        if !unbound.is_empty() {
            let names = unbound
                .iter()
                .map(|name| format!("`{name}`"))
                .collect::<Vec<_>>()
                .join(", ");
            let (noun, verb) = if unbound.len() == 1 {
                ("variable", "it")
            } else {
                ("variables", "them")
            };
            return Err(format!(
                "its `requires` reads the {noun} {names}, which the pattern's configuration does \
                 not bind; such a variable is almost always a misspelling (of a variable the \
                 configuration names, or of a key), and a condition on {verb} is decided only \
                 when it is trivially true or false, so the pattern is refused: bind {verb} in \
                 the configuration or remove {verb} from the condition"
            ));
        }
        Ok(CompiledPattern { search })
    }

    /// Compile the normal-termination pattern of `options`: the given one
    /// ([`NormalEndKind::Pattern`]), or `<k> .K </k>`, which is judged on every `<k>` cell when
    /// the configuration's `<k>` cell lies under a multiplicity cell ([`NormalEndKind::EveryK`])
    /// and on the one `<k>` cell otherwise ([`NormalEndKind::SingleK`]).
    ///
    /// # Errors
    ///
    /// [`CampaignError::NormalEndPattern`] when it does not compile.
    pub(crate) fn normal_end(
        &self,
        grammar: &ProgramGrammar,
        options: &CaseOptions,
    ) -> Result<NormalEnd, CampaignError> {
        let (text, kind) = match options.normal_end_pattern.as_deref() {
            Some(pattern) => (pattern, NormalEndKind::Pattern),
            None if self.k_under_multiplicity => (DEFAULT_NORMAL_END, NormalEndKind::EveryK),
            None => (DEFAULT_NORMAL_END, NormalEndKind::SingleK),
        };
        let pattern = self
            .compile(grammar, text)
            .map_err(|message| CampaignError::NormalEndPattern { message })?;
        Ok(NormalEnd { pattern, kind })
    }
}

/// `message` with each position `<command line>:LINE:COLUMN:` that the frontend gives a
/// pattern's text (krun's source name for a command-line pattern, [`pattern_attributes`])
/// written as `line LINE, column COLUMN:` of the pattern's own text: a campaign's pattern comes
/// from a campaign file, a flag or a library call, and its client names which.
fn relocate_positions(message: &str) -> String {
    use std::fmt::Write as _;
    const SOURCE: &str = "<command line>:";
    let mut relocated = String::with_capacity(message.len());
    let mut rest = message;
    while let Some(start) = rest.find(SOURCE) {
        relocated.push_str(&rest[..start]);
        let after = &rest[start + SOURCE.len()..];
        let digits = |text: &str| text.bytes().take_while(u8::is_ascii_digit).count();
        let line = digits(after);
        let column = after
            .get(line..)
            .and_then(|text| text.strip_prefix(':'))
            .map_or(0, digits);
        match after.get(line + 1 + column..) {
            Some(tail) if line > 0 && column > 0 && tail.starts_with(':') => {
                let _ = write!(
                    relocated,
                    "line {}, column {}:",
                    &after[..line],
                    &after[line + 1..line + 1 + column]
                );
                rest = &tail[1..];
            }
            _ => {
                relocated.push_str("the pattern:");
                rest = after;
            }
        }
    }
    relocated.push_str(rest);
    relocated
}

/// The K names of the free variables of `search`'s condition that its configuration does not
/// bind, sorted. The compiled pattern is the conjunction of the configuration (its first
/// conjunct) and one predicate per conjunct of the condition (`compile_search_pattern`); a
/// variable a quantifier of the condition binds is not free. An anonymous variable is named
/// `_`.
fn unbound_condition_variables(search: &CompiledSearchPattern) -> Vec<String> {
    let KorePattern::And { arguments, .. } = &search.pattern else {
        return Vec::new();
    };
    let Some((configuration, condition)) = arguments.split_first() else {
        return Vec::new();
    };
    let bound = configuration.free_variables();
    let mut names = std::collections::BTreeSet::new();
    for predicate in condition {
        for variable in predicate.free_variables() {
            if bound.contains(&variable) {
                continue;
            }
            let generated = search
                .generated_anonymous_variables
                .iter()
                .any(|identity| identity.kind == variable.kind && identity.name == variable.name);
            let name = if generated {
                "_".to_owned()
            } else {
                k_rust::kast::identifier::decode_variable(&variable.name)
                    .1
                    .unwrap_or_else(|_| variable.name.clone())
            };
            names.insert(name);
        }
    }
    names.into_iter().collect()
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

    /// The pattern's configuration without its `requires`, when it has one: the conjunction of
    /// the configuration (the compiled pattern's first conjunct) and `\top`, as a pattern
    /// without `requires` compiles (`compile_search_pattern`). `None` for a pattern without
    /// `requires`, which is its own configuration.
    pub(crate) fn body_only(&self) -> Option<Self> {
        let KorePattern::And { sort, arguments } = &self.search.pattern else {
            return None;
        };
        let (configuration, condition) = arguments.split_first()?;
        if condition
            .iter()
            .all(|predicate| matches!(predicate, KorePattern::Top { .. }))
        {
            return None;
        }
        let occurring = configuration.free_variables();
        let generated_anonymous_variables = self
            .search
            .generated_anonymous_variables
            .iter()
            .filter(|identity| {
                occurring.iter().any(|variable| {
                    variable.kind == identity.kind && variable.name == identity.name
                })
            })
            .cloned()
            .collect();
        Some(Self {
            search: CompiledSearchPattern {
                pattern: KorePattern::And {
                    sort: sort.clone(),
                    arguments: vec![
                        configuration.clone(),
                        KorePattern::Top { sort: sort.clone() },
                    ],
                },
                generated_anonymous_variables,
            },
        })
    }
}

/// A campaign's compiled normal-termination pattern.
#[derive(Clone, Debug)]
pub(crate) struct NormalEnd {
    pattern: CompiledPattern,
    /// Which normal end applies: the campaign's pattern, or the default `<k> .K </k>` on the one
    /// `<k>` cell or on every `<k>` cell.
    kind: NormalEndKind,
}

impl NormalEnd {
    /// Which normal end applies.
    pub(crate) fn kind(&self) -> NormalEndKind {
        self.kind
    }
}

/// Whether the `<k>` cell of the configuration `definition`'s main module declares lies under
/// (or is) a cell of multiplicity `*` or `?`, so that a configuration may hold any number of
/// `<k>` cells, none included.
///
/// The configuration's cells are the productions with the `cell` attribute, each with its
/// declared `multiplicity`; a cell's children are the cell sorts among its non-terminals (a
/// child of multiplicity `*` appears through its collection sort, which is no cell sort). Cell
/// names are unique in a configuration, so the `<k>` cell has one path from `<generatedTop>`.
/// The answer is `true` exactly when that path is not one of multiplicity-1 cells: the `<k>`
/// cell is declared, and it cannot be reached from `<generatedTop>` through cells of
/// multiplicity 1 alone. A definition whose top cell or `<k>` cell is not found gives `false`,
/// which keeps the single-`<k>` default.
fn k_under_multiplicity(definition: &ResolvedDefinition, main_module: &str) -> bool {
    let Some(module) = definition.module_id(main_module) else {
        return false;
    };
    // Cell sort -> (multiplicity is 1, non-terminal sorts).
    let mut cells = std::collections::BTreeMap::<String, (bool, Vec<String>)>::new();
    for sentence in definition.sentences(module) {
        let Sentence::Production {
            sort,
            items,
            attributes,
            ..
        } = sentence
        else {
            continue;
        };
        if !attributes.has(AttributeKey::Cell) {
            continue;
        }
        let single = attributes
            .string(AttributeKey::Multiplicity)
            .is_none_or(|multiplicity| multiplicity == "1");
        let children = items.iter().filter_map(|item| match item {
            ProductionItem::NonTerminal { sort, .. } => Some(sort.name.clone()),
            _ => None,
        });
        let entry = cells
            .entry(sort.name.clone())
            .or_insert_with(|| (single, Vec::new()));
        entry.0 &= single;
        entry.1.extend(children);
    }
    let top = BuiltinSort::GeneratedTopCell.k_name();
    let k = k_rust::definition::configuration::cell_sort_name("k");
    if !cells.contains_key(top) || !cells.contains_key(&k) {
        return false;
    }
    let mut seen = std::collections::BTreeSet::from([top.to_owned()]);
    let mut stack = vec![top.to_owned()];
    while let Some(cell) = stack.pop() {
        if cell == k {
            return false;
        }
        for child in &cells[&cell].1 {
            if cells.get(child).is_some_and(|(single, _)| *single) && seen.insert(child.clone()) {
                stack.push(child.clone());
            }
        }
    }
    true
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
    /// The matcher only informs: its verdict is reported in
    /// [`crate::exec::LeafReport::matches`] when it matches, and an undecided verdict, a solver
    /// `unknown` or a failure of its matching leaves the leaf as it was ([`Self::informational`]).
    informational: bool,
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

    /// This matcher as one that only informs: no verdict of it makes a leaf unclean, since no
    /// judgement rests on it (a pattern's configuration without its `requires`, counted for the
    /// report; FZ-POLISH S2).
    #[must_use]
    pub(crate) fn informational(mut self) -> Self {
        self.informational = true;
        self
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
        informational: false,
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
    /// Which normal end applies ([`NormalEnd::kind`]).
    normal_end_kind: NormalEndKind,
    /// Under [`NormalEndKind::EveryK`], whether the definition's initial configuration holds a
    /// `<k>` cell, found on the first leaf with no `<k>` cell left ([`initial_has_k`]) and kept:
    /// the cells of the initial configuration are fixed by the configuration declaration, which
    /// configuration variables only fill.
    initial_has_k: std::cell::Cell<Option<bool>>,
    /// The pattern compiler, built on the first [`Self::compile_pattern`] when the executor was
    /// built from a compiled normal-end pattern without one.
    compiler: Option<PatternCompiler>,
    max_simplification_iterations: usize,
    /// Stops for lack of stack in the definition's load (ARCHITECTURE 5.4).
    load_stack_stops: usize,
    /// The definition's overload data heads and refused symbols
    /// ([`BackendDefinition::data_heads`]), which [`LeafReport::data_end`] reads; computed on
    /// first need ([`Self::data_heads`]), since it runs the definition's full critical-pair
    /// check, or given by the campaign's cache ([`Self::with_data_heads`]).
    data_heads: Option<DataHeads>,
    /// The pairs the data judgement reads as joined (`CaseOptions::assume_joined`, the names
    /// that apply on this executor's definition), applied to [`Self::data_heads`] when they are
    /// computed ([`Self::with_assume_joined`]).
    assume_joined: Vec<String>,
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
            normal_end_kind: normal_end.kind,
            initial_has_k: std::cell::Cell::new(None),
            compiler: None,
            max_simplification_iterations: options.max_simplification_iterations,
            load_stack_stops,
            data_heads: None,
            assume_joined: Vec::new(),
            #[cfg(not(target_arch = "wasm32"))]
            safety_limit_ms: options.safety_limit_ms,
            #[cfg(not(target_arch = "wasm32"))]
            watchdog: options
                .safety_limit_ms
                .map(|_| super::watchdog::Watchdog::new()),
        })
    }

    /// Whether `state`, an end of the other definition of a differential pair, is data in this
    /// executor's definition as well (`k_rust_backend::data_term`, "Two definitions"): it
    /// internalizes here, is decided, and [`BackendDefinition::is_data`] holds with this
    /// definition's own heads. Any failure reads as not data.
    pub(crate) fn is_data_here(&mut self, state: &KorePattern) -> bool {
        if self.data_heads().is_err() {
            return false;
        }
        let heads = self.data_heads.as_ref().expect("computed just above");
        self.backend
            .with_solver_over(None, &[state], |definition, _| {
                Ok::<_, BackendError>(
                    definition
                        .admit_unverified(state, &[])
                        .internalize_pattern()
                        .is_ok_and(|pattern| {
                            pattern.constraints.is_empty()
                                && pattern.term.attributes().variables.is_empty()
                                && definition.is_data(&pattern.term, heads)
                        }),
                )
            })
            .unwrap_or(false)
    }

    /// The definition's data heads and the findings of its full critical-pair check
    /// ([`BackendDefinition::data_heads`]), with the pairs `CaseOptions::assume_joined` names
    /// read as joined ([`BackendDefinition::data_heads_assuming`]), computed once.
    ///
    /// # Errors
    ///
    /// When the main module does not load.
    pub(crate) fn data_heads(&mut self) -> Result<&DataHeads, String> {
        if self.data_heads.is_none() {
            let loaded = self
                .backend
                .select_definition(None)
                .map_err(|error| error.to_string())?;
            let mut heads = loaded.data_heads();
            if !self.assume_joined.is_empty() {
                heads = loaded.data_heads_assuming(&heads, |finding| {
                    crate::findings::assumed(&self.assume_joined, finding)
                });
            }
            self.data_heads = Some(heads);
        }
        Ok(self.data_heads.as_ref().expect("computed just above"))
    }

    /// The data heads, when already computed.
    pub(crate) fn computed_data_heads(&self) -> Option<&DataHeads> {
        self.data_heads.as_ref()
    }

    /// This executor, reading the pairs `names` names (side prefixes removed,
    /// `crate::findings::for_side`) as joined when it computes its data heads.
    #[must_use]
    pub(crate) fn with_assume_joined(mut self, names: Vec<String>) -> Self {
        self.assume_joined = names;
        self
    }

    /// This executor, with `heads` (computed for its definition) as its data heads, so that
    /// the full critical-pair check does not run again.
    #[must_use]
    pub(crate) fn with_data_heads(mut self, heads: Option<DataHeads>) -> Self {
        if heads.is_some() {
            self.data_heads = heads;
        }
        self
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
        self.run_with(initial, shape, matchers, cancel, Execution::Plain, None)
            .map(|(result, _, _)| result)
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
            None,
        )
        .map(|(result, leaves, _)| (result, leaves))
    }

    /// [`Self::run_observed`] with every observation event (`rules: None`) and no leaf matcher,
    /// for an `at: any-state` pattern target (ARCHITECTURE 4.1): after the leaves are judged,
    /// every configuration `plan` places on the case's path tree is judged against `matcher`
    /// ([`ConfigurationVerdict`]), within the same token scope and per-case safety limit as the
    /// run. Solver `unknown`s that matching meets are added to [`CaseResult::smt_unknowns`]. The
    /// verdicts are empty for a failed case and for a case outside the determinism contract
    /// (`CaseResult::determinism_breaks`), which no configuration can decide; a backend error
    /// while matching makes the case a failure, as one judging its leaves does.
    ///
    /// A filtered run would give a transition outside the filter no event, so its path could
    /// not be shown (P7-ADDENDUM review, N4).
    ///
    /// # Errors
    ///
    /// [`Abort`] for a failed solver prelude.
    pub(crate) fn run_any_state(
        &mut self,
        initial: &KorePattern,
        shape: &CaseRequestShape,
        matcher: &LeafMatcher,
        plan: ConfigurationPlan,
        cancel: Option<&CancellationToken>,
    ) -> Result<(CaseResult, Vec<ExecutionLeaf>, Vec<ConfigurationVerdict>), Abort> {
        self.run_with(
            initial,
            shape,
            &[],
            cancel,
            Execution::Observed { rules: None },
            Some(AnyState { matcher, plan }),
        )
    }

    fn run_with(
        &mut self,
        initial: &KorePattern,
        shape: &CaseRequestShape,
        matchers: &[&LeafMatcher],
        cancel: Option<&CancellationToken>,
        execution: Execution,
        any_state: Option<AnyState<'_>>,
    ) -> Result<Executed, Abort> {
        let request = shape.request(initial.clone());
        if shape.data_end {
            // A main module that does not load fails the run itself.
            let _ = self.data_heads();
        }
        let judge = Judge {
            normal_end: &self.normal_end,
            normal_end_kind: self.normal_end_kind,
            initial_has_k: &self.initial_has_k,
            matchers,
            options: SimplificationOptions {
                max_iterations: self.max_simplification_iterations,
                ..SimplificationOptions::default()
            },
            data_heads: if shape.data_end {
                self.data_heads.as_ref()
            } else {
                None
            },
            terminal_allowed: shape.has_terminal_rules(),
            load_stack_stops: self.load_stack_stops,
            forward: None,
            any_state,
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
            return outcome.map(|(mut result, leaves, verdicts)| {
                result.safety_limit_hit = fired;
                (result, leaves, verdicts)
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
        self.judge_stuck_leaf(state).0
    }

    /// [`Self::judge_stuck_state`], with whether the state holds a term-level `\and`
    /// ([`LeafReport::term_conjunction`]).
    pub(super) fn judge_stuck_leaf(&mut self, state: KorePattern) -> (Vec<UncleanReason>, bool) {
        let leaf = LeafReport {
            halt: HaltReasonOutput::Stuck,
            depth: 0,
            state,
            unclean: Vec::new(),
            natural_end: false,
            matches: Vec::new(),
            rewrites: Vec::new(),
            data_end: None,
            diagnostics: Vec::new(),
            term_conjunction: false,
        };
        let judge = Judge {
            normal_end: &self.normal_end,
            normal_end_kind: self.normal_end_kind,
            initial_has_k: &self.initial_has_k,
            matchers: &[],
            options: SimplificationOptions::default(),
            data_heads: None,
            terminal_allowed: false,
            load_stack_stops: 0,
            forward: None,
            any_state: None,
        };
        let mut internal = judge
            .judge_internally(&mut self.backend, std::slice::from_ref(&leaf))
            .expect("the judgement runs");
        let internal = internal.pop().expect("one leaf");
        (internal.reasons, internal.term_conjunction)
    }
}

/// Load-time stops for lack of stack of a loaded definition (`docs/compatibility.md`,
/// "Determinism and concurrency").
fn load_stack_stops(definition: &BackendDefinition) -> usize {
    definition.value_claims().counts().condition_stack_stops
        + definition.discharge_counts().stack_stops
}

/// What [`Executor::run_with`] returns: the judged result, the raw leaves of an observed run,
/// and an any-state target's configuration verdicts.
type Executed = (CaseResult, Vec<ExecutionLeaf>, Vec<ConfigurationVerdict>);

/// One node of a case's path tree that an `at: any-state` pattern target judges
/// ([`Executor::run_any_state`]; the tree is `crate::target`'s).
#[derive(Clone, Copy, Debug)]
pub(crate) struct PlannedConfiguration<'l> {
    /// The node's parent: an earlier index of the plan, or `None` for the root (the initial
    /// configuration).
    pub(crate) parent: Option<usize>,
    /// The normalized configuration at the node, as the backend reports it (KORE JSON); `None`
    /// when the walk shows none there.
    pub(crate) configuration: Option<&'l serde_json::Value>,
}

/// Places the configurations of an observed run's `leaves` on their path tree, every parent
/// before its children.
pub(crate) type ConfigurationPlan =
    for<'l> fn(&'l [ExecutionLeaf]) -> Vec<PlannedConfiguration<'l>>;

/// What an `at: any-state` pattern target's matcher says about one configuration
/// ([`Executor::run_any_state`]). A configuration is judged as an end leaf's state is
/// (ARCHITECTURE 5.2): internalized in its definition, then matched as `krun --pattern` does.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ConfigurationVerdict {
    /// It is decided (no constraint, no variable), ceil-free, and matches with empty
    /// constraints: the target is reached there. `term_conjunction`: its term holds a
    /// term-level `\and` (of equal sides, since it is ceil-free), which kink's query refuses
    /// ([`super::comparable::query_conditions`], Q4').
    Reaches {
        /// The configuration's term holds a term-level `\and`.
        term_conjunction: bool,
    },
    /// The matcher refuted it.
    Refuted,
    /// It cannot be decided: it matches but is not ceil-free (it may denote nothing), the match
    /// is undecided, it is not a decided state, or it does not decode or internalize. The
    /// reason the case is `unsupported` when nothing reaches.
    Unresolved(UnjudgedReason),
    /// Not judged: the plan shows no configuration here, or a configuration above it on its
    /// path reaches or was not judged.
    NotJudged,
}

/// An any-state target's part of a case's judgement ([`Executor::run_any_state`]).
#[derive(Clone, Copy)]
struct AnyState<'a> {
    matcher: &'a LeafMatcher,
    plan: ConfigurationPlan,
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
    normal_end_kind: NormalEndKind,
    initial_has_k: &'a std::cell::Cell<Option<bool>>,
    matchers: &'a [&'a LeafMatcher],
    options: SimplificationOptions,
    /// When the request asks for [`LeafReport::data_end`], the overload heads a data end may
    /// hold.
    data_heads: Option<&'a DataHeads>,
    terminal_allowed: bool,
    load_stack_stops: usize,
    /// Under the safety limit, the caller's token and the case's own: the caller's cancellation
    /// is forwarded synchronously when the run ends, before the leaves are judged (review S2).
    forward: Option<(CancellationToken, CancellationToken)>,
    /// For an `at: any-state` pattern target, its matcher and the plan of the configurations it
    /// judges.
    any_state: Option<AnyState<'a>>,
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
    /// The every-`<k>` default matched a leaf with no `<k>` cell left: a natural end only when
    /// the initial configuration held a `<k>` cell ([`Judge::judge`]).
    vacuous: bool,
    matches: Vec<bool>,
    data_end: Option<bool>,
    /// Solver `unknown`s the leaf's matching met, in either evaluation mode (review 2, NI-2).
    smt_unknowns: usize,
    /// [`LeafReport::term_conjunction`].
    term_conjunction: bool,
}

impl Judge<'_> {
    fn execute(
        &self,
        backend: &mut Backend,
        request: ExecuteRequest,
        execution: Execution,
    ) -> Result<Executed, Abort> {
        // The initial state, kept for the one probe of whether it holds a `<k>` cell.
        let probe = (self.normal_end_kind == NormalEndKind::EveryK
            && self.initial_has_k.get().is_none())
        .then(|| request.state.clone());
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
                let mut judged = self.judge(backend, &result, probe.as_ref())?;
                let verdicts = match self.any_state {
                    // A case outside the determinism contract is judged without its
                    // configurations (`crate::target`), so they are not matched.
                    Some(any_state)
                        if judged.failure.is_none() && judged.determinism_breaks().is_empty() =>
                    {
                        match self.judge_configurations(backend, any_state, &result.leaves) {
                            Ok((verdicts, unknowns)) => {
                                judged.smt_unknowns = judged.smt_unknowns.saturating_add(unknowns);
                                verdicts
                            }
                            Err(error) => {
                                return Ok((
                                    self.failed(failure_of(&error)?),
                                    Vec::new(),
                                    Vec::new(),
                                ));
                            }
                        }
                    }
                    Some(_) | None => Vec::new(),
                };
                Ok((judged, result.leaves, verdicts))
            }
            Err(error) => Ok((self.failed(failure_of(&error)?), Vec::new(), Vec::new())),
        }
    }

    /// Judge the configurations `any_state`'s plan places on the path tree of `leaves`, parents
    /// first: a node is judged when it shows a configuration and its parent, if any, was judged
    /// and does not reach, so nothing below a reaching configuration is matched. One operation
    /// over every shown configuration and the matcher. Also the solver `unknown`s the matching
    /// met (review 2, NI-2).
    fn judge_configurations(
        &self,
        backend: &mut Backend,
        any_state: AnyState<'_>,
        leaves: &[ExecutionLeaf],
    ) -> Result<(Vec<ConfigurationVerdict>, usize), BackendError> {
        let plan = (any_state.plan)(leaves);
        let decoded: Vec<Option<Option<KorePattern>>> = plan
            .iter()
            .map(|node| {
                node.configuration
                    .map(|configuration| codec::from_value(configuration).ok())
            })
            .collect();
        let mut patterns: Vec<&KorePattern> = decoded.iter().flatten().flatten().collect();
        patterns.push(&any_state.matcher.kore);
        backend.with_solver_over(None, &patterns, |definition, solver| {
            let mut verdicts: Vec<ConfigurationVerdict> = Vec::with_capacity(plan.len());
            let mut unknowns = 0;
            for (node, configuration) in plan.iter().zip(&decoded) {
                let open = node.parent.is_none_or(|parent| {
                    matches!(
                        verdicts[parent],
                        ConfigurationVerdict::Refuted | ConfigurationVerdict::Unresolved(_)
                    )
                });
                let verdict = match configuration {
                    Some(Some(state)) if open => self.judge_configuration(
                        definition,
                        solver,
                        any_state.matcher,
                        state,
                        &mut unknowns,
                    )?,
                    Some(None) if open => {
                        ConfigurationVerdict::Unresolved(UnjudgedReason::Unobservable)
                    }
                    Some(_) | None => ConfigurationVerdict::NotJudged,
                };
                verdicts.push(verdict);
            }
            Ok((verdicts, unknowns))
        })
    }

    /// One configuration's [`ConfigurationVerdict`]: internalized and matched as an end leaf's
    /// state is in [`Self::judge_leaf`], with the target's matcher in both evaluation modes
    /// ([`Self::match_leaf`]). A match reaches only on a decided, ceil-free configuration, which
    /// denotes one value; a configuration that is not ceil-free may denote nothing, so a match
    /// there leaves the case unresolved (`NotCeilFree`), and so does an undecided match.
    fn judge_configuration(
        &self,
        definition: &BackendDefinition,
        solver: &dyn SmtSolver,
        matcher: &LeafMatcher,
        state: &KorePattern,
        unknowns: &mut usize,
    ) -> Result<ConfigurationVerdict, BackendError> {
        let Ok(pattern) = definition
            .admit_unverified(state, &[])
            .internalize_pattern()
        else {
            return Ok(ConfigurationVerdict::Unresolved(
                UnjudgedReason::InternalizationFailed,
            ));
        };
        let attributes = pattern.term.attributes();
        if !pattern.constraints.is_empty() || !attributes.variables.is_empty() {
            return Ok(ConfigurationVerdict::Unresolved(
                UnjudgedReason::UndecidedState,
            ));
        }
        let mut internal = Internal::default();
        let verdict = self.match_leaf(definition, solver, matcher, &pattern, &mut internal)?;
        *unknowns = unknowns.saturating_add(internal.smt_unknowns);
        Ok(match verdict {
            MatchVerdict::Matched if attributes.ceil_free() => ConfigurationVerdict::Reaches {
                term_conjunction: holds_term_conjunction(&pattern.term),
            },
            MatchVerdict::Matched => ConfigurationVerdict::Unresolved(UnjudgedReason::NotCeilFree),
            MatchVerdict::NotMatched => ConfigurationVerdict::Refuted,
            MatchVerdict::Undecided => {
                ConfigurationVerdict::Unresolved(UnjudgedReason::UndecidedMatch)
            }
        })
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

    fn judge(
        &self,
        backend: &mut Backend,
        result: &ExecutionResult,
        probe: Option<&KorePattern>,
    ) -> Result<CaseResult, Abort> {
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
                data_end: None,
                diagnostics: LeafDiagnostic::of_leaf(leaf),
                term_conjunction: false,
            });
        }
        let mut internal = match self.judge_internally(backend, &leaves) {
            Ok(internal) => internal,
            Err(error) => return Ok(self.failed(failure_of(&error)?)),
        };
        // A leaf with no `<k>` cell left is a natural end only when the initial configuration
        // held one: otherwise no thread ever ran there, and the program may have stopped
        // elsewhere having done nothing (FZ-UNSUPPORTED review N1).
        if internal
            .iter()
            .any(|judged| judged.vacuous && judged.normal_end)
        {
            let known = self.initial_has_k.get().or_else(|| {
                let found = probe.and_then(|state| initial_has_k(backend, state));
                if found.is_some() {
                    self.initial_has_k.set(found);
                }
                found
            });
            if known != Some(true) {
                for judged in internal.iter_mut().filter(|judged| judged.vacuous) {
                    judged.normal_end = false;
                    judged.reasons.push(UncleanReason::NaturalEndUndecided);
                }
            }
        }
        let mut smt_unknowns = result.smt_unknowns;
        for (leaf, internal) in leaves.iter_mut().zip(internal) {
            smt_unknowns = smt_unknowns.saturating_add(internal.smt_unknowns);
            leaf.unclean.extend(internal.reasons);
            leaf.unclean.sort();
            leaf.unclean.dedup();
            leaf.natural_end = leaf.is_clean() && internal.normal_end;
            leaf.matches = internal.matches;
            leaf.data_end = internal.data_end;
            leaf.term_conjunction = internal.term_conjunction;
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
    /// each matcher, data. One operation over every leaf state and every matcher.
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
            internal
                .reasons
                .push(UncleanReason::NotCeilFree(partial_application(
                    &pattern.term,
                )));
        }
        if !decided || !end_like {
            return Ok(internal);
        }
        internal.term_conjunction = holds_term_conjunction(&pattern.term);
        if let Some(heads) = self.data_heads {
            internal.data_end = Some(definition.is_data(&pattern.term, heads));
        }
        if leaf.halt == HaltReasonOutput::Stuck {
            let verdict = match self.normal_end_kind {
                NormalEndKind::EveryK => {
                    let verdict = every_k_cell_empty(&pattern.term);
                    internal.vacuous =
                        verdict == MatchVerdict::Matched && attributes.k_cells() == 0;
                    verdict
                }
                NormalEndKind::SingleK if attributes.k_cells() != 1 => MatchVerdict::Undecided,
                NormalEndKind::SingleK | NormalEndKind::Pattern => {
                    self.match_leaf(definition, solver, self.normal_end, &pattern, &mut internal)?
                }
            };
            match verdict {
                MatchVerdict::Matched => internal.normal_end = true,
                MatchVerdict::NotMatched => {}
                MatchVerdict::Undecided => {
                    internal.reasons.push(UncleanReason::NaturalEndUndecided);
                }
            }
        }
        for (index, matcher) in self.matchers.iter().enumerate() {
            if matcher.informational {
                // Its own scratch record: what its matching meets is no fact of the leaf.
                let mut scratch = Internal::default();
                internal.matches[index] = matches!(
                    self.match_leaf(definition, solver, matcher, &pattern, &mut scratch),
                    Ok(MatchVerdict::Matched)
                );
                continue;
            }
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

/// The every-`<k>` default normal end on a decided leaf term (ARCHITECTURE 5.2, as amended by
/// FZ-UNSUPPORTED): `Matched` when every `<k>` cell not nested in a `<k>` cell holds `.K`, none
/// included; `NotMatched` when some `<k>` cell holds a K sequence `kseq(_, _)`, which is never
/// `.K` (a sequence's head is a `KItem`, and `.K` is no `KItem`), whatever the other cells
/// hold; `Undecided` otherwise (a cell holding a function application or anything else whose
/// equality with `.K` the term alone does not decide). These are the verdicts the matcher gives
/// `<k> .K </k>` on each cell: it matches `dotk` against `dotk`, refutes it against the
/// constructor `kseq`, and refutes no function-headed subject.
pub(super) fn every_k_cell_empty(term: &Term) -> MatchVerdict {
    let mut verdict = MatchVerdict::Matched;
    visit_k_cells(term, &mut |cell| {
        let TermKind::Application { arguments, .. } = cell.kind() else {
            verdict = both(verdict, MatchVerdict::Undecided);
            return;
        };
        let cell_verdict = match arguments.as_slice() {
            [contents] => match contents.kind() {
                TermKind::Application {
                    symbol, arguments, ..
                } if symbol.is(WellKnownSymbol::DotK) && arguments.is_empty() => {
                    MatchVerdict::Matched
                }
                TermKind::Application { symbol, .. } if symbol.is(WellKnownSymbol::KSeq) => {
                    MatchVerdict::NotMatched
                }
                _ => MatchVerdict::Undecided,
            },
            _ => MatchVerdict::Undecided,
        };
        verdict = both(verdict, cell_verdict);
    });
    verdict
}

/// Whether the initial configuration `state` holds a `<k>` cell: `state` run to depth 0, so
/// that the configuration's initializers are evaluated, and its one leaf internalized. `None`
/// when that run or the internalization fails (then nothing is kept, and the leaf it was asked
/// for stays undecided).
fn initial_has_k(backend: &mut Backend, state: &KorePattern) -> Option<bool> {
    let request = ExecuteRequest {
        max_depth: Some(0),
        max_work: None,
        max_breadth: None,
        terminal_rules: Vec::new(),
        cut_point_rules: Vec::new(),
        stop_at_branch: false,
        collect_coverage: false,
        collect_offered: false,
        trace: false,
        step_timeout_ms: None,
        ..ExecuteRequest::new(state.clone())
    };
    let result = backend.execute(request).ok()?;
    let leaf = result.leaves.first()?;
    let initial = codec::from_value(&leaf.state).ok()?;
    backend
        .with_solver_over(None, &[&initial], |definition, _solver| {
            Ok::<_, BackendError>(
                definition
                    .admit_unverified(&initial, &[])
                    .internalize_pattern()
                    .ok()
                    .map(|pattern| pattern.term.attributes().k_cells() > 0),
            )
        })
        .ok()
        .flatten()
}

/// The note of [`UncleanReason::NotCeilFree`] for a term-level `\and` of two different sides.
pub(crate) const AND_NOTE: &str = r"\and";

/// The K label of the first application of a partial function in `term`, in preorder, looking
/// only into subterms that are not `ceil_free`, or [`AND_NOTE`] for a term-level conjunction of
/// two different sides found first, which owes their equality and may denote nothing
/// (`k_rust_backend::definedness::ceil_term`); `None` when the term is not ceil-free for another
/// reason (a malformed map or set, a set variable).
fn partial_application(term: &Term) -> Option<String> {
    if term.attributes().ceil_free() {
        return None;
    }
    let mut children: Vec<&Term> = Vec::new();
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => {
            if symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Partial) {
                let name: &str = &symbol.name;
                return Some(
                    k_rust::kast::identifier::decode_label(name)
                        .unwrap_or_else(|_| name.to_owned()),
                );
            }
            children.extend(arguments);
        }
        TermKind::And(left, right) => {
            if left != right {
                return Some(AND_NOTE.to_owned());
            }
            children.extend([left, right]);
        }
        TermKind::Injection { term, .. } => children.push(term),
        TermKind::Map { entries, rest, .. } => {
            for (key, value) in entries {
                children.extend([key, value]);
            }
            children.extend(rest);
        }
        TermKind::List { heads, rest, .. } => {
            children.extend(heads);
            if let Some((middle, tails)) = rest {
                children.push(middle);
                children.extend(tails);
            }
        }
        TermKind::Set { elements, rest, .. } => {
            children.extend(elements);
            children.extend(rest);
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
    }
    children.into_iter().find_map(partial_application)
}

/// Whether `term` holds a term-level `\and` anywhere (`k_rust_backend::term::TermKind::And`),
/// with equal sides or not.
fn holds_term_conjunction(term: &Term) -> bool {
    match term.kind() {
        TermKind::And(..) => true,
        TermKind::Application { arguments, .. } => arguments.iter().any(holds_term_conjunction),
        TermKind::Injection { term, .. } => holds_term_conjunction(term),
        TermKind::Map { entries, rest, .. } => {
            entries
                .iter()
                .any(|(key, value)| holds_term_conjunction(key) || holds_term_conjunction(value))
                || rest.as_ref().is_some_and(holds_term_conjunction)
        }
        TermKind::List { heads, rest, .. } => {
            heads.iter().any(holds_term_conjunction)
                || rest.as_ref().is_some_and(|(middle, tails)| {
                    holds_term_conjunction(middle) || tails.iter().any(holds_term_conjunction)
                })
        }
        TermKind::Set { elements, rest, .. } => {
            elements.iter().any(holds_term_conjunction)
                || rest.as_ref().is_some_and(holds_term_conjunction)
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => false,
    }
}

/// The verdict on two cells together: refuted when either is, undecided when either is,
/// matched otherwise.
fn both(left: MatchVerdict, right: MatchVerdict) -> MatchVerdict {
    use MatchVerdict as V;
    match (left, right) {
        (V::NotMatched, _) | (_, V::NotMatched) => V::NotMatched,
        (V::Undecided, _) | (_, V::Undecided) => V::Undecided,
        (V::Matched, V::Matched) => V::Matched,
    }
}

/// Call `visit` on every `<k>` cell of `term`, not descending into a `<k>` cell.
fn visit_k_cells<'a>(term: &'a Term, visit: &mut impl FnMut(&'a Term)) {
    if term.attributes().k_cells() == 0 {
        return;
    }
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => {
            if symbol.is(WellKnownSymbol::KCell) {
                visit(term);
                return;
            }
            for argument in arguments {
                visit_k_cells(argument, visit);
            }
        }
        TermKind::And(left, right) => {
            visit_k_cells(left, visit);
            visit_k_cells(right, visit);
        }
        TermKind::Injection { term, .. } => visit_k_cells(term, visit),
        TermKind::Map { entries, rest, .. } => {
            for (key, value) in entries {
                visit_k_cells(key, visit);
                visit_k_cells(value, visit);
            }
            if let Some(rest) = rest {
                visit_k_cells(rest, visit);
            }
        }
        TermKind::List { heads, rest, .. } => {
            for head in heads {
                visit_k_cells(head, visit);
            }
            if let Some((middle, tails)) = rest {
                visit_k_cells(middle, visit);
                for tail in tails {
                    visit_k_cells(tail, visit);
                }
            }
        }
        TermKind::Set { elements, rest, .. } => {
            for element in elements {
                visit_k_cells(element, visit);
            }
            if let Some(rest) = rest {
                visit_k_cells(rest, visit);
            }
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
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
