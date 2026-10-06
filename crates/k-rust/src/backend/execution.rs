//! Shared execution orchestration and the CLI result contract.
//!
//! ```toml algorithm
//! id = "backend.execution.captured_stdout"
//! name = "find captured stdout buffers in backend execution leaves"
//! sites = ["captured_stdout_buffer", "stdout_stream_buffers", "stdout_stream_buffer", "stream_list_items", "stream_buffer"]
//! variable = "d = distinct backend terms, l = candidate stream-list nodes, b = buffered stdout bytes in the expanded term, h = maximum term depth"
//! counters = []
//! no_counter = "the output byte count and allocations are recorded for captured workloads"
//!
//! [[cost]]
//! mode = "one final leaf"
//! bound = "O(d + l + b * h) term visits and buffer copies; only stream-cell paths are externalized"
//! ```

#![deny(clippy::wildcard_enum_match_arm)]

use std::{
    collections::{BTreeSet, HashMap, HashSet},
    error::Error,
    fmt, fs, io,
    path::{Path, PathBuf},
    time::Duration,
};

use k_rust_backend::{
    builtin::BuiltinEffect,
    definition::BackendDefinition,
    diagnostic::{self, BackendDiagnostic},
    externalize::{self, External},
    fresh::RequestNames,
    rewrite::{
        ExecutionBranchMode, ExecutionLeaf, ExecutionMode, ExecutionOptions, ExecutionResult,
        HaltReason, IndeterminateReason, Pattern,
        execute_disjunction_with_solver_and_io_state_and_observer_with_initial_status,
        execute_disjunction_with_solver_and_observer_with_initial_status, execute_with_solver,
    },
    rule::{ClassifiedAxiom, Predicate, RuleOrigin},
    search::{
        IncompleteSearch, PatternMatchError, SearchEnd, SearchOptions, SearchType,
        match_disjunction_with_solver, search_pattern_disjunction_with_solver,
    },
    simplify::{
        BudgetSubject, ConditionIndeterminacy, ContradictedTotal, SimplificationError,
        SimplificationOptions, simplify_pattern_with_solver,
    },
    smt::{SmtError, SmtSolver, TranslationError},
    stop::StopCause,
    term::{Sort, Term, TermKind, Variable},
    transition::{DescriptorTranscriptEntry, ExecutionIoState},
};
use num_bigint::BigInt;
use num_traits::ToPrimitive;

use crate::{
    kore::{
        ast::{Pattern as KorePattern, Sort as KoreSort},
        codec as kore_codec,
        node::{PatternNode, PatternSource, compare, materialize},
        printer::Printer as KorePrinter,
    },
    names::BuiltinSort,
};

use super::{
    Backend, BackendError,
    search::{BackendMatchTarget, MatchOutput, pattern_matches_output, search_output},
};

#[derive(Debug)]
pub struct SearchRunOptions {
    pub search_type: SearchType,
    pub pattern: Option<PathBuf>,
    pub bound: Option<usize>,
}

#[derive(Debug)]
pub struct BackendRunOptions {
    pub depth: u64,
    pub max_simplification_iterations: usize,
    pub breadth_limit: Option<usize>,
    pub execute_to_branch: bool,
    pub cut_point_rules: BTreeSet<String>,
    pub terminal_rules: BTreeSet<String>,
    pub strategy: ExecutionMode,
    pub search: Option<SearchRunOptions>,
    pub match_target: Option<BackendMatchTarget>,
    pub function_symbols: BTreeSet<String>,
    pub stop_leaves: Option<PathBuf>,
    pub step_timeout: Option<Duration>,
    pub moving_average_timeout: bool,
    pub capture_stdout: bool,
    pub execution_input: Option<Vec<u8>>,
}

pub struct BackendRunOutput {
    pub pattern: RunPattern,
    pub exit_code: u8,
    pub captured_stdout: Option<Vec<u8>>,
    pub live_transcript: Option<Vec<DescriptorTranscriptEntry>>,
}

/// The result pattern of a run, kept as the backend data it is externalized from, so that
/// printing it reads the shared backend terms instead of a KORE tree that writes out each shared
/// subterm at every use.
#[derive(Debug)]
pub enum RunPattern {
    /// The filtered, ordered, and deduplicated match conditions of a search or match target.
    Matches(MatchOutput),
    /// The final states of an execution.
    States(StatesOutput),
}

impl RunPattern {
    /// Call `consume` with the source of the result pattern.
    pub fn with_source<R>(&self, consume: impl FnOnce(External<'_>) -> R) -> R {
        match self {
            Self::Matches(output) => output.with_source(consume),
            Self::States(output) => output.with_source(consume),
        }
    }

    /// The result pattern as a tree.
    pub fn to_pattern(&self) -> KorePattern {
        self.with_source(|source| materialize(source))
    }
}

/// The final states of an execution: `\bottom` at `output_sort` for none, the constrained
/// pattern for one, and otherwise the `\or` at `final_sort` of the constrained patterns in the
/// structural order of their KORE. States are never deduplicated here.
#[derive(Debug)]
pub struct StatesOutput {
    states: Vec<Pattern>,
    output_sort: KoreSort,
    final_sort: KoreSort,
}

impl StatesOutput {
    pub const fn new(states: Vec<Pattern>, output_sort: KoreSort, final_sort: KoreSort) -> Self {
        Self {
            states,
            output_sort,
            final_sort,
        }
    }

    /// Call `consume` with the source of the result pattern. The states are ordered by
    /// comparing their sources, which reads each pair only up to its first difference.
    pub fn with_source<R>(&self, consume: impl FnOnce(External<'_>) -> R) -> R {
        let printable = self
            .states
            .iter()
            .map(externalize::Printable::pattern)
            .collect::<Vec<_>>();
        let mut states = printable
            .iter()
            .map(|state| External::Constrained(state.source()))
            .collect::<Vec<_>>();
        states.sort_by(|left, right| compare(*left, *right));
        let source = match states.as_slice() {
            [] => External::Bottom(&self.output_sort),
            [state] => *state,
            states => External::Connective {
                and: false,
                shape: externalize::ConjunctionShape::Flat,
                sort: &self.final_sort,
                operands: states,
            },
        };
        consume(source)
    }
}

/// Execute one already-internalized pattern with the facade's cached solver.
pub fn run(
    definition: &BackendDefinition,
    initial: Pattern,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
) -> ExecutionResult {
    execute_with_solver(definition, initial, options, solver)
}

/// The written position of an equation, `path:line:column`, from its KORE `Source` and
/// `Location` attributes; `None` when the KORE carries neither.
fn written_position(origin: &RuleOrigin) -> Option<String> {
    let source = origin.source.as_deref().map(|source| {
        source
            .strip_prefix("Source(")
            .and_then(|path| path.strip_suffix(')'))
            .unwrap_or(source)
    });
    let location = origin.location.as_deref().map(|location| {
        let inner = location
            .strip_prefix("Location(")
            .and_then(|inner| inner.strip_suffix(')'));
        match inner.map(|inner| inner.split(',').take(2).collect::<Vec<_>>()) {
            Some(parts) if parts.len() == 2 => format!("{}:{}", parts[0], parts[1]),
            _ => location.to_owned(),
        }
    });
    match (source, location) {
        (Some(source), Some(location)) => Some(format!("{source}:{location}")),
        (Some(source), None) => Some(source.to_owned()),
        (None, Some(location)) => Some(location),
        (None, None) => None,
    }
}

/// What the author is told when an equation of a symbol declared `total` (or `functional`)
/// reduced an application of it to bottom (`ContradictedTotal`): the symbol by its K label, the
/// equation with
/// its written position, the application, and the undefined term its result reached.
///
/// The attribute is an axiom k-rust trusts, and the equation is another axiom of the same
/// definition; on this application they contradict each other, so the definition is
/// inconsistent there. Nothing about the run changes: the message only explains the empty leaf.
pub fn contradicted_total_message(contradicted: &ContradictedTotal) -> String {
    let application =
        KorePrinter::compact().print_pattern(&externalize::term(&contradicted.application));
    let undefined =
        KorePrinter::compact().print_pattern(&externalize::term(&contradicted.undefined_term));
    let equation = contradicted
        .label
        .as_deref()
        .unwrap_or(&contradicted.rule_id);
    let position = contradicted
        .origin
        .as_ref()
        .and_then(written_position)
        .map(|position| format!(" at {position}"))
        .unwrap_or_default();
    format!(
        "the `total` attribute of {symbol} is contradicted on this input: its equation {equation}{position} reduces {application} to bottom (undefined at {undefined}); the attribute is trusted, so the definition is inconsistent here",
        symbol = k_label(contradicted.symbol()),
    )
}

/// The K label a KORE symbol name encodes (`LbltDiv'LParUndsRParUnds'M'Unds'Int'Unds'Int` is
/// `tDiv(_)_M_Int_Int`, and a production with `symbol(td)` is `td`), which is how the author
/// wrote or declared the production; the KORE name itself when it is not a label encoding.
pub fn k_label(kore_name: &str) -> String {
    crate::kast::identifier::decode_label(kore_name).unwrap_or_else(|_| kore_name.to_owned())
}

/// How a warning names a rule: its label, or its `UNIQUE_ID` when it has none, and the position
/// it is written at when the KORE carries one.
fn rule_description(definition: &BackendDefinition, rule_id: &str) -> String {
    let attributes = definition
        .classified_axioms()
        .iter()
        .map(ClassifiedAxiom::attributes)
        .find(|attributes| attributes.unique_id == rule_id);
    let name = attributes
        .and_then(|attributes| attributes.label.as_deref())
        .unwrap_or(rule_id);
    let position = attributes
        .and_then(|attributes| attributes.origins.first())
        .and_then(written_position)
        .map(|position| format!(" at {position}"))
        .unwrap_or_default();
    format!("{name}{position}")
}

/// A variable as the author wrote it: the K name a KORE variable name encodes (`VarY` is `Y`),
/// or the KORE name itself when it encodes none.
fn written_variable(definition_name: &str) -> String {
    match crate::kast::identifier::decode_variable(definition_name) {
        (_, Ok(name)) if !name.is_empty() => name,
        _ => definition_name.to_owned(),
    }
}

/// `items` joined as an English list: `A`, `A and B`, `A, B and C`.
fn english_list(items: &[String]) -> String {
    match items {
        [] => String::new(),
        [only] => only.clone(),
        [init @ .., last] => format!("{} and {last}", init.join(", ")),
    }
}

/// Predicates as compact KORE, joined by `, `.
fn printed_predicates(predicates: &[Predicate], result_sort: &Sort) -> String {
    predicates
        .iter()
        .map(|predicate| {
            KorePrinter::compact()
                .print_pattern(&externalize::predicate_pattern(predicate, result_sort))
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// The warning for an `UndecidedCondition` diagnostic of the equation `rule_id`.
///
/// Its predicates are printed as KORE, where a variable the equation's left-hand side does not
/// bind keeps the backend's marker (`Eq-hVarY`); the warning says which variable of the
/// equation each such name is, as the author wrote it (`Y`). An equation whose result has
/// variables its left-hand side does not bind is not a solver verdict: the backend reports it
/// only when no other equation rewrote the term and the attempt was not made while simplifying
/// the condition of an enclosing attempt that was refuted or superseded, so the warning says
/// that the term was left unevaluated, and why. A solver verdict may be on the equation's
/// `requires` or on the definedness of the terms its match bound, so its warning names the
/// predicates without saying which.
#[allow(clippy::too_many_arguments)]
fn undecided_condition_message(
    definition: &BackendDefinition,
    rule_id: &str,
    reason: &ConditionIndeterminacy,
    predicates: &[Predicate],
    rule_variables: &[Variable],
    result_sort: &Sort,
    depth: u64,
) -> String {
    let rule = rule_description(definition, rule_id);
    let (predicates, rule_variables) = diagnostic::printable_condition(predicates, rule_variables);
    let explained = rule_variables
        .iter()
        .map(|rule_variable| {
            format!(
                "{} is the equation's variable {}",
                externalize::external_variable_name(&rule_variable.variable.name),
                written_variable(&rule_variable.definition_name)
            )
        })
        .collect::<Vec<_>>();
    let explained = if explained.is_empty() {
        String::new()
    } else {
        format!(" ({})", english_list(&explained))
    };
    if let ConditionIndeterminacy::UnboundResultVariables(variables) = reason {
        let variables = variables
            .iter()
            .map(|variable| written_variable(variable))
            .collect::<Vec<_>>();
        let shown = predicates
            .iter()
            .filter(|predicate| !matches!(predicate, Predicate::True))
            .cloned()
            .collect::<Vec<_>>();
        let requires = if shown.is_empty() {
            String::new()
        } else {
            format!(
                "; its requires on this term is {}{explained}",
                printed_predicates(&shown, result_sort)
            )
        };
        return format!(
            "equation {rule} was not applied at depth {depth}: its right-hand side or ensures uses {}, which its left-hand side does not bind, so matching it gives no value for {}; no other equation rewrote the term it matched, which was left unevaluated{requires}",
            english_list(&variables),
            if variables.len() == 1 { "it" } else { "them" },
        );
    }
    format!(
        "condition of equation {rule} remained undecided at depth {depth} ({reason:?}, predicates: [{}]){explained}; the result may retain an unresolved condition",
        printed_predicates(&predicates, result_sort),
    )
}

fn report_diagnostics<'a>(
    definition: &BackendDefinition,
    diagnostics: impl IntoIterator<Item = &'a BackendDiagnostic>,
    result_sort: &Sort,
    depth: u64,
) {
    let mut seen = HashSet::new();
    for diagnostic in diagnostics {
        if !seen.insert(diagnostic) {
            continue;
        }
        match diagnostic {
            BackendDiagnostic::SimplificationBudgetExhausted { limit, subject } => {
                let subject = match subject {
                    BudgetSubject::Term => "the term",
                    BudgetSubject::Predicates => "predicates",
                };
                eprintln!(
                    "warning: simplification budget {limit} exhausted while simplifying {subject} at depth {depth}; the result may not be fully simplified"
                );
            }
            BackendDiagnostic::UndecidedCondition {
                rule_id,
                reason,
                predicates,
                rule_variables,
            } => eprintln!(
                "warning: {}",
                undecided_condition_message(
                    definition,
                    rule_id,
                    reason,
                    predicates,
                    rule_variables,
                    result_sort,
                    depth
                )
            ),
            BackendDiagnostic::UndecidedPredicate { predicate, reason } => eprintln!(
                "warning: predicate {} remained undecided at depth {depth} ({reason:?}); the result may retain an unresolved constraint",
                printed_predicates(std::slice::from_ref(predicate), result_sort)
            ),
            BackendDiagnostic::RuleConditionUnsimplified { rule_id, limit } => eprintln!(
                "warning: condition of rule {rule_id} was decided without full simplification at depth {depth} after budget {limit} was exhausted"
            ),
            BackendDiagnostic::RuleConditionFailed { rule_id, failure } => eprintln!(
                "warning: condition of rule {rule_id} was decided without full simplification at depth {depth} because simplifying it failed ({failure}); the rule may have been left unapplied"
            ),
            BackendDiagnostic::UnsupportedHookUnevaluated { hook, reason } => eprintln!(
                "warning: hook {hook} was left unevaluated at depth {depth} ({reason}); the result may not be fully simplified"
            ),
        }
    }
}

fn captured_stdout_buffer(finals: &[&ExecutionLeaf]) -> Result<Vec<u8>, io::Error> {
    let details = finals
        .iter()
        .map(|leaf| {
            (
                leaf.pattern.constraints.len(),
                stdout_stream_buffers(&leaf.pattern.term),
            )
        })
        .collect::<Vec<_>>();
    let valid_shape =
        finals.len() == 1 && finals[0].pattern.constraints.is_empty() && details[0].1.len() == 1;
    if !valid_shape {
        let summary = details
            .iter()
            .map(|(constraints, buffers)| {
                format!(
                    "constraints={constraints}, stdout stream buffers={}",
                    buffers.len()
                )
            })
            .collect::<Vec<_>>()
            .join("; ");
        return Err(io::Error::other(format!(
            "captured output requires exactly one execution leaf, unconstrained and with exactly one stdout stream buffer; found {} {}{}{}",
            finals.len(),
            if finals.len() == 1 { "leaf" } else { "leaves" },
            if summary.is_empty() { "" } else { ": " },
            summary,
        )));
    }
    let leaf = finals[0];
    if !matches!(
        leaf.halt_reason,
        HaltReason::Stuck | HaltReason::TerminalRule { .. }
    ) {
        return Err(io::Error::other(format!(
            "captured output requires one complete terminal execution leaf; leaf halted at depth {} with {:?}",
            leaf.depth, leaf.halt_reason
        )));
    }
    Ok(details[0].1[0].clone())
}

fn stdout_stream_buffers(term: &Term) -> Vec<Vec<u8>> {
    fn visit(term: &Term, memo: &mut HashMap<Term, Vec<Vec<u8>>>) -> Vec<Vec<u8>> {
        if let Some(buffers) = memo.get(term) {
            return buffers.clone();
        }
        let mut buffers = Vec::new();
        match term.kind() {
            TermKind::Application { arguments, .. } => {
                if let Some(buffer) = stdout_stream_buffer(External::Term(term)) {
                    buffers.push(buffer);
                }
                for argument in arguments {
                    buffers.extend(visit(argument, memo));
                }
            }
            TermKind::Injection { term, .. } => buffers.extend(visit(term, memo)),
            TermKind::Map { entries, rest, .. } => {
                for (key, value) in entries {
                    buffers.extend(visit(key, memo));
                    buffers.extend(visit(value, memo));
                }
                if let Some(rest) = rest {
                    buffers.extend(visit(rest, memo));
                }
            }
            TermKind::List {
                definition,
                heads,
                rest,
            } => {
                for head in heads {
                    if let Some(buffer) =
                        stdout_stream_buffer(External::Element(&definition.symbols.element, head))
                    {
                        buffers.push(buffer);
                    }
                    buffers.extend(visit(head, memo));
                }
                if let Some((middle, tails)) = rest {
                    buffers.extend(visit(middle, memo));
                    for tail in tails {
                        if let Some(buffer) = stdout_stream_buffer(External::Element(
                            &definition.symbols.element,
                            tail,
                        )) {
                            buffers.push(buffer);
                        }
                        buffers.extend(visit(tail, memo));
                    }
                }
            }
            TermKind::Set {
                definition,
                elements,
                rest,
            } => {
                for element in elements {
                    if let Some(buffer) = stdout_stream_buffer(External::Element(
                        &definition.symbols.element,
                        element,
                    )) {
                        buffers.push(buffer);
                    }
                    buffers.extend(visit(element, memo));
                }
                if let Some(rest) = rest {
                    buffers.extend(visit(rest, memo));
                }
            }
            // The previous KORE-pattern visitor did not descend through an And node.
            TermKind::And(..) | TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
        }
        memo.insert(term.clone(), buffers.clone());
        buffers
    }

    visit(term, &mut HashMap::new())
}

fn stdout_stream_buffer<'a, S: PatternSource<'a>>(pattern: S) -> Option<Vec<u8>> {
    let PatternNode::Application { symbol, arguments } = pattern.node() else {
        return None;
    };
    if !symbol.name.starts_with("Lbl'-LT-'")
        || !symbol.name.contains("'-GT-'")
        || arguments.len() != 1
    {
        return None;
    }
    let items = stream_list_items(arguments.into_iter().next()?)?;
    let [descriptor, mode, buffer] = items.as_slice() else {
        return None;
    };
    if !is_stream_descriptor(descriptor.clone(), "Lbl'Hash'ostream", "SortInt", "1")
        || !domain_value(unwrap_injections(mode.clone()), "SortString", "off")
    {
        return None;
    }
    stream_buffer(buffer.clone())
}

fn stream_list_items<'a, S: PatternSource<'a>>(pattern: S) -> Option<Vec<S>> {
    fn append<'a, S: PatternSource<'a>>(pattern: S, items: &mut Vec<S>) -> bool {
        let PatternNode::Application { symbol, arguments } = unwrap_injections(pattern).node()
        else {
            return false;
        };
        if symbol.name == "Lbl'Unds'List'Unds'" && arguments.len() == 2 {
            append(arguments[0].clone(), items) && append(arguments[1].clone(), items)
        } else if symbol.name == "LblListItem" && arguments.len() == 1 {
            items.push(arguments[0].clone());
            true
        } else {
            false
        }
    }

    let mut items = Vec::new();
    append(pattern, &mut items).then_some(items)
}

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "PatternNode is syntax; only the listed variants are special here"
)]
fn unwrap_injections<'a, S: PatternSource<'a>>(mut pattern: S) -> S {
    loop {
        match pattern.clone().node() {
            PatternNode::Application { symbol, arguments }
                if symbol.name == "inj" && arguments.len() == 1 =>
            {
                pattern = arguments[0].clone();
            }
            _ => return pattern,
        }
    }
}

fn domain_value<'a, S: PatternSource<'a>>(pattern: S, sort_name: &str, expected: &str) -> bool {
    matches!(pattern.node(), PatternNode::DomainValue { sort, value }
        if matches!(sort.as_ref(), KoreSort::Application { name, arguments }
            if name == sort_name && arguments.is_empty())
        && value.as_utf8().ok() == Some(expected))
}

fn is_stream_descriptor<'a, S: PatternSource<'a>>(
    pattern: S,
    symbol_prefix: &str,
    sort_name: &str,
    value: &str,
) -> bool {
    let PatternNode::Application { symbol, arguments } = unwrap_injections(pattern).node() else {
        return false;
    };
    symbol.name.starts_with(symbol_prefix)
        && arguments.len() == 1
        && domain_value(unwrap_injections(arguments[0].clone()), sort_name, value)
}

fn stream_buffer<'a, S: PatternSource<'a>>(pattern: S) -> Option<Vec<u8>> {
    let PatternNode::Application { symbol, arguments } = unwrap_injections(pattern).node() else {
        return None;
    };
    if !symbol.name.starts_with("Lbl'Hash'buffer") || arguments.len() != 1 {
        return None;
    }
    let PatternNode::Application {
        symbol: sequence,
        arguments: sequence_arguments,
    } = unwrap_injections(arguments[0].clone()).node()
    else {
        return None;
    };
    if sequence.name != "kseq" || sequence_arguments.len() != 2 {
        return None;
    }
    let PatternNode::Application {
        symbol: terminator,
        arguments: terminator_arguments,
    } = sequence_arguments[1].clone().node()
    else {
        return None;
    };
    if terminator.name != "dotk" || !terminator_arguments.is_empty() {
        return None;
    }
    domain_value_bytes(
        unwrap_injections(sequence_arguments[0].clone()),
        "SortString",
    )
}

/// The console bytes of a `String` buffer: each character is one byte, its code point, as
/// `IO.write` writes it; `None` when a code point is above 255, which is no byte.
fn domain_value_bytes<'a, S: PatternSource<'a>>(pattern: S, sort_name: &str) -> Option<Vec<u8>> {
    let PatternNode::DomainValue { sort, value } = pattern.node() else {
        return None;
    };
    if !matches!(sort.as_ref(), KoreSort::Application { name, arguments }
        if name == sort_name && arguments.is_empty())
    {
        return None;
    }
    value
        .as_utf8()
        .ok()?
        .chars()
        .map(|character| u8::try_from(u32::from(character)).ok())
        .collect()
}

impl Backend {
    pub fn run_cli(
        &mut self,
        module: Option<&str>,
        initial: Vec<Pattern>,
        options: BackendRunOptions,
    ) -> Result<BackendRunOutput, Box<dyn Error>> {
        self.with_solver(module, |definition, solver| {
            run_backend_with_solver(definition, solver, initial, options)
                .map_err(|error| BackendError(error.to_string()))
        })
        .map_err(Into::into)
    }

    pub fn load_patterns(
        &mut self,
        module: Option<&str>,
        path: &Path,
        purpose: &str,
    ) -> Result<Vec<Pattern>, BackendError> {
        self.with_solver(module, |definition, _| {
            load_backend_patterns(definition, path, purpose)
                .map_err(|error| BackendError(error.to_string()))
        })
    }
}

fn run_backend_with_solver(
    backend: &BackendDefinition,
    solver: &dyn SmtSolver,
    initial: Vec<Pattern>,
    options: BackendRunOptions,
) -> Result<BackendRunOutput, Box<dyn Error>> {
    let Some(first_initial) = initial.first() else {
        return Err(io::Error::other("initial pattern has no live disjuncts").into());
    };
    let output_sort = externalize::sort(&first_initial.term.sort());
    let mut match_target = options.match_target;
    if let Some(search) = options.search {
        if options.stop_leaves.is_some() {
            return Err(io::Error::other("--stop-leaves is only supported for execution").into());
        }
        let target = match match_target.take() {
            Some(target) => target,
            None => match search.pattern {
                Some(path) => load_backend_target(backend, &path, "search")?,
                None => BackendMatchTarget {
                    pattern: default_search_pattern(&initial)
                        .ok_or_else(|| io::Error::other("initial pattern has no live disjuncts"))?,
                    generated_anonymous_variables: BTreeSet::new(),
                    request_names: RequestNames::default(),
                },
            },
        };
        let result = search_pattern_disjunction_with_solver(
            backend,
            initial,
            &target.pattern,
            SearchOptions {
                search_type: search.search_type,
                max_depth: options.depth,
                max_breadth: options.breadth_limit,
                max_results: search.bound,
                max_simplification_iterations: options.max_simplification_iterations,
                request_names: target.request_names.clone(),
            },
            solver,
        );
        for effect in &result.effects {
            match effect {
                BuiltinEffect::UserLog(message) => eprintln!("{message}"),
            }
        }
        // Depth and result bounds are limits the user asked for, not engine failures: the
        // states found are still valid answers, so report the truncation and succeed.
        match &result.end {
            SearchEnd::ResultBound(_) => {
                eprintln!("search stopped at the requested result bound; further results may exist")
            }
            // Nothing remained, or the breadth frontier or the stopped state is an entry of
            // `incomplete`, classified below.
            SearchEnd::Exhausted(_) | SearchEnd::BreadthBound(_) | SearchEnd::Stopped(_) => {}
        }
        if let Some(incomplete) = result.incomplete.iter().find(|incomplete| {
            search_incomplete_disposition(incomplete) == IncompleteDisposition::Failure
        }) {
            return Err(io::Error::other(format!(
                "in-process backend search was incomplete: {}",
                describe_incomplete_search(incomplete)
            ))
            .into());
        }
        for matched in &result.matches {
            report_diagnostics(
                backend,
                matched.state.diagnostics.iter().chain(&matched.diagnostics),
                &matched.state.pattern.term.sort(),
                matched.state.depth,
            );
        }
        return Ok(BackendRunOutput {
            pattern: RunPattern::Matches(search_output(
                &result,
                &output_sort,
                &target.generated_anonymous_variables,
                &options.function_symbols,
            )),
            exit_code: 0,
            captured_stdout: None,
            live_transcript: None,
        });
    }
    let execution_options = ExecutionOptions {
        max_depth: options.depth,
        max_breadth: options.breadth_limit,
        max_simplification_iterations: options.max_simplification_iterations,
        mode: options.strategy,
        branch_mode: if options.execute_to_branch {
            ExecutionBranchMode::StopAtBranch
        } else {
            ExecutionBranchMode::ExploreAll
        },
        cut_point_rules: options.cut_point_rules,
        terminal_rules: options.terminal_rules,
        step_timeout: options.step_timeout,
        moving_average_timeout: options.moving_average_timeout,
        retain_trace: false,
        // Executing and then matching a target is one request: no name the execution mints is
        // spelled like a variable of the target either.
        request_names: match_target
            .as_ref()
            .map(|target| {
                let mut names = RequestNames::of(&[&target.pattern]);
                names.extend(&target.request_names);
                names
            })
            .unwrap_or_default(),
        ..ExecutionOptions::default()
    };
    let live_io = options.execution_input.is_some();
    let (execution, initial_simplification) = if let Some(input) = options.execution_input {
        execute_disjunction_with_solver_and_io_state_and_observer_with_initial_status(
            backend,
            initial,
            execution_options,
            solver,
            ExecutionIoState::new(input),
            |effect| match effect {
                BuiltinEffect::UserLog(message) => eprintln!("{message}"),
            },
        )
    } else {
        execute_disjunction_with_solver_and_observer_with_initial_status(
            backend,
            initial,
            execution_options,
            solver,
            |effect| match effect {
                BuiltinEffect::UserLog(message) => eprintln!("{message}"),
            },
        )
    };
    if let Some(leaf) = execution
        .leaves
        .iter()
        .find(|leaf| match &leaf.halt_reason {
            HaltReason::Stopped(cause) => stop_fails_the_run(cause),
            HaltReason::Indeterminate(_) | HaltReason::Simplification(_) => true,
            HaltReason::Stuck
            | HaltReason::Trivial { .. }
            | HaltReason::Vacuous { .. }
            | HaltReason::Branch { .. }
            | HaltReason::CutPointRule { .. }
            | HaltReason::TerminalRule { .. }
            | HaltReason::DepthBound
            | HaltReason::BreadthBound => false,
        })
    {
        let result_sort = leaf.pattern.term.sort();
        let reason = match &leaf.halt_reason {
            HaltReason::Simplification(error) => describe_simplification_error(error, &result_sort),
            HaltReason::Indeterminate(reason) => describe_indeterminate(reason, &result_sort),
            reason @ HaltReason::Stopped(_)
            | reason @ HaltReason::Stuck
            | reason @ HaltReason::Trivial { .. }
            | reason @ HaltReason::Vacuous { .. }
            | reason @ HaltReason::Branch { .. }
            | reason @ HaltReason::CutPointRule { .. }
            | reason @ HaltReason::TerminalRule { .. }
            | reason @ HaltReason::DepthBound
            | reason @ HaltReason::BreadthBound => format!("{reason:?}"),
        };
        return Err(io::Error::other(format!(
            "in-process backend halted at depth {}: {reason}",
            leaf.depth
        ))
        .into());
    }
    for leaf in &execution.leaves {
        report_diagnostics(
            backend,
            &leaf.diagnostics,
            &leaf.pattern.term.sort(),
            leaf.depth,
        );
    }
    if let Some(path) = options.stop_leaves {
        let depth_bounded = execution
            .leaves
            .iter()
            .filter(|leaf| matches!(leaf.halt_reason, HaltReason::DepthBound))
            .collect::<Vec<_>>();
        let sort = depth_bounded
            .first()
            .map(|leaf| externalize::sort(&leaf.pattern.term.sort()))
            .unwrap_or_else(|| output_sort.clone());
        let printable = depth_bounded
            .into_iter()
            .map(|leaf| externalize::Printable::pattern(&leaf.pattern))
            .collect::<Vec<_>>();
        let leaves = printable
            .iter()
            .map(|leaf| External::Constrained(leaf.source()))
            .collect::<Vec<_>>();
        // The `\or` of the leaves (of any number), rendered into the file as it is produced from
        // the leaves' terms, so that neither the text nor the KORE tree is held whole.
        let marker = External::Connective {
            and: false,
            shape: externalize::ConjunctionShape::Flat,
            sort: &sort,
            operands: &leaves,
        };
        let mut file = io::BufWriter::with_capacity(1 << 20, fs::File::create(path)?);
        KorePrinter::pretty(100).write_source(marker, &mut file)?;
        file.into_inner().map_err(io::IntoInnerError::into_error)?;
    }
    let final_sort = execution
        .leaves
        .first()
        .map(|leaf| externalize::sort(&leaf.pattern.term.sort()))
        .unwrap_or_else(|| output_sort.clone());
    let initial_is_bottom = initial_simplification.simplified_to_bottom();
    let finals = execution
        .leaves
        .iter()
        .filter(|leaf| {
            !matches!(
                leaf.halt_reason,
                HaltReason::Trivial { .. } | HaltReason::Vacuous { .. }
            )
        })
        .collect::<Vec<_>>();
    let captured_stdout = options
        .capture_stdout
        .then(|| captured_stdout_buffer(&finals))
        .transpose()?;
    let live_transcript = if live_io {
        match execution.leaves.as_slice() {
            [leaf] => Some(leaf.io.transcript().to_vec()),
            leaves if leaves.iter().all(|leaf| leaf.io.transcript().is_empty()) => Some(Vec::new()),
            leaves => {
                return Err(io::Error::other(format!(
                    "--io on cannot select console output from {} retained execution traces",
                    leaves.len()
                ))
                .into());
            }
        }
    } else {
        None
    };
    let exit_code = exit_code_of(
        backend,
        solver,
        &finals,
        options.max_simplification_iterations,
    )?;
    if initial_is_bottom {
        eprintln!(
            "warning: the initial configuration simplified to \\bottom before any rewrite step; check the configuration variables"
        );
    } else if finals.is_empty()
        && execution.leaves.iter().all(|leaf| {
            matches!(
                leaf.halt_reason,
                HaltReason::Trivial { .. } | HaltReason::Vacuous { .. }
            )
        })
    {
        for leaf in &execution.leaves {
            let result_sort = leaf.pattern.term.sort();
            match &leaf.halt_reason {
                HaltReason::Trivial {
                    depth,
                    rule_id,
                    label,
                    obligation,
                    ..
                } => {
                    let obligation = KorePrinter::compact()
                        .print_pattern(&externalize::ml_pattern(obligation, &result_sort));
                    if let Some(rule) = label.as_ref().or(rule_id.as_ref()) {
                        eprintln!(
                            "warning: execution ended with no successor at depth {depth}: rule {rule} applied with an undefined result; refuted obligation {obligation}"
                        );
                    } else {
                        eprintln!(
                            "warning: execution ended with no successor at depth {depth}: the result simplified to bottom; refuted obligation {obligation}"
                        );
                    }
                }
                HaltReason::Vacuous {
                    depth,
                    rule_id,
                    label,
                    constraint,
                    ..
                } => {
                    let constraint = KorePrinter::compact()
                        .print_pattern(&externalize::ml_pattern(constraint, &result_sort));
                    if let Some(rule) = label.as_ref().or(rule_id.as_ref()) {
                        eprintln!(
                            "warning: execution ended with no successor at depth {depth}: rule {rule} applied with a false path constraint; refuted obligation {constraint}"
                        );
                    } else {
                        eprintln!(
                            "warning: execution ended with no successor at depth {depth}: the path constraint is false; refuted obligation {constraint}"
                        );
                    }
                }
                HaltReason::Stopped(_)
                | HaltReason::Stuck
                | HaltReason::Branch { .. }
                | HaltReason::CutPointRule { .. }
                | HaltReason::TerminalRule { .. }
                | HaltReason::DepthBound
                | HaltReason::BreadthBound
                | HaltReason::Indeterminate(_)
                | HaltReason::Simplification(_) => {
                    unreachable!("all dropped leaves were checked above")
                }
            }
            if let HaltReason::Trivial {
                contradicted_total: Some(contradicted),
                ..
            }
            | HaltReason::Vacuous {
                contradicted_total: Some(contradicted),
                ..
            } = &leaf.halt_reason
            {
                eprintln!("warning: {}", contradicted_total_message(contradicted));
            }
        }
    }
    if let Some(target) = match_target {
        let subjects = finals
            .iter()
            .map(|leaf| leaf.pattern.clone())
            .collect::<Vec<_>>();
        let matches = match_disjunction_with_solver(
            backend,
            &target.pattern,
            &subjects,
            SimplificationOptions {
                max_iterations: options.max_simplification_iterations,
                ..SimplificationOptions::default()
            },
            solver,
        )
        .map_err(|stop| io::Error::other(stop.into_cause().to_string()))?
        .map_err(pattern_match_error)?;
        return Ok(BackendRunOutput {
            pattern: RunPattern::Matches(pattern_matches_output(
                &matches,
                &output_sort,
                &target.pattern.term.sort(),
                &target.generated_anonymous_variables,
                &options.function_symbols,
            )),
            exit_code,
            captured_stdout,
            live_transcript,
        });
    }
    let states = finals.iter().map(|leaf| leaf.pattern.clone()).collect();
    Ok(BackendRunOutput {
        pattern: RunPattern::States(StatesOutput::new(states, output_sort, final_sort)),
        exit_code,
        captured_stdout,
        live_transcript,
    })
}

/// Whether a stopped execution leaf fails the run. A cancelled request, an exhausted stack and a
/// failed solver prelude leave the state without an answer; a passed step deadline ends only its
/// state under a bound the run was given, so its leaf is printed like the others.
#[deny(clippy::wildcard_enum_match_arm)]
fn stop_fails_the_run(cause: &StopCause) -> bool {
    match cause {
        StopCause::Cancelled | StopCause::StackExhausted | StopCause::SolverPrelude(_) => true,
        StopCause::Deadline(_) => false,
    }
}

/// Whether a state a search left unexplored is a limit the user asked for or an engine failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum IncompleteDisposition {
    UserLimit,
    Failure,
}

/// Classify one state a search left unexplored.
#[deny(clippy::wildcard_enum_match_arm)]
/// A reader's account of a search entry left incomplete: the reason, the terms it names and the
/// state's configuration, each term printed in KORE, and the state's depth. The entry's `Debug`
/// form spells out term internals (attributes, hashes, whole symbol declarations at every node),
/// which are not part of the reason and grow with the state far faster than its KORE does.
fn describe_incomplete_search(incomplete: &IncompleteSearch) -> String {
    let (state, reason) = match incomplete {
        IncompleteSearch::DepthBound(state) => (state, "the depth bound was reached".to_owned()),
        IncompleteSearch::BreadthBound(states) => {
            return format!(
                "the breadth bound was exceeded with {} states at the frontier",
                states.len()
            );
        }
        IncompleteSearch::Indeterminate { state, reason } => (
            state,
            describe_indeterminate(reason, &state.pattern.term.sort()),
        ),
        IncompleteSearch::Stopped { state, cause } => (state, cause.to_string()),
        IncompleteSearch::Simplification { state, error } => (
            state,
            describe_simplification_error(error, &state.pattern.term.sort()),
        ),
        IncompleteSearch::Match {
            state, remainder, ..
        } => (
            state,
            format!(
                "the match of the target pattern left an undecided remainder:{}",
                describe_equalities(remainder)
            ),
        ),
        IncompleteSearch::Smt { state, error } => (
            state,
            format!("the solver failed: {}", describe_smt_error(error)),
        ),
    };
    format!(
        "{reason}\nin the state at depth {}:\n{}",
        state.depth,
        KorePrinter::pretty(100).print_pattern(&externalize::constrained_pattern(&state.pattern))
    )
}

/// A simplification failure with the term or predicate it names printed in KORE; a predicate is
/// printed at the sort of the pattern it constrains.
fn describe_simplification_error(error: &SimplificationError, sort: &Sort) -> String {
    match error {
        SimplificationError::UnsupportedHook { term, .. } => format!(
            "{error}\n{}",
            KorePrinter::pretty(100).print_pattern(&externalize::term(term))
        ),
        SimplificationError::IterationLimit { limit, term } => format!(
            "simplification reached its limit of {limit} iterations on\n{}",
            KorePrinter::pretty(100).print_pattern(&externalize::term(term))
        ),
        SimplificationError::PredicateIterationLimit { limit, predicate } => format!(
            "simplification reached its limit of {limit} iterations on the predicate\n{}",
            describe_predicate(predicate, sort)
        ),
        SimplificationError::SmtPredicate { predicate, error } => format!(
            "the solver failed ({}) on the predicate\n{}",
            describe_smt_error(error),
            describe_predicate(predicate, sort)
        ),
        SimplificationError::Smt { rule_id, error } => format!(
            "the solver failed on rule {rule_id}: {}",
            describe_smt_error(error)
        ),
        SimplificationError::Builtin(_)
        | SimplificationError::DisjunctiveResult { .. }
        | SimplificationError::TopEquationOutsideConjunction { .. }
        | SimplificationError::InvalidBuiltinResultSymbol { .. } => error.to_string(),
    }
}

/// Why a rewrite step could not decide its successors, with the terms and predicates it names
/// printed in KORE at the sort of the state.
fn describe_indeterminate(reason: &IndeterminateReason, sort: &Sort) -> String {
    match reason {
        IndeterminateReason::SurvivingMacroOrAlias { symbol } => {
            format!("the macro or alias symbol {symbol} survived into an executable term")
        }
        IndeterminateReason::Match {
            rule_id, remainder, ..
        } => format!(
            "rule {rule_id} matched with an undecided remainder:{}",
            describe_equalities(remainder)
        ),
        IndeterminateReason::Instantiation {
            rule_id,
            missing_variables,
        } => format!(
            "rule {rule_id} leaves {} uninstantiated in concrete execution",
            missing_variables
                .iter()
                .map(|variable| externalize::external_variable_name(&variable.name))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        IndeterminateReason::Requires {
            rule_id,
            predicates,
        } => format!(
            "the requires clause of rule {rule_id} is undecided:{}",
            describe_predicates(predicates, sort)
        ),
        IndeterminateReason::Smt { rule_id, error } => format!(
            "the solver failed on rule {rule_id}: {}",
            describe_smt_error(error)
        ),
        IndeterminateReason::Remainder {
            rule_ids,
            predicates,
            satisfiability,
        } => format!(
            "the remainder of rules {} is undecided ({}):{}",
            rule_ids.join(", "),
            match satisfiability {
                Ok(satisfiability) => format!("{satisfiability:?}"),
                Err(error) => describe_smt_error(error),
            },
            describe_predicates(predicates, sort)
        ),
    }
}

/// A solver failure; a term a translation failure names is printed in KORE.
fn describe_smt_error(error: &SmtError) -> String {
    match error {
        SmtError::Translation(TranslationError::NonBooleanAnd(term)) => format!(
            "a term conjunction that is not Boolean cannot be translated: {}",
            KorePrinter::compact().print_pattern(&externalize::term(term))
        ),
        SmtError::Translation(TranslationError::SmtLemmaSurplusMappings { rule_id, terms }) => {
            format!(
                "the smt-lemma {rule_id} maps surplus terms: {}",
                terms
                    .iter()
                    .map(|term| KorePrinter::compact().print_pattern(&externalize::term(term)))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
        SmtError::Translation(TranslationError::SmtLemmaSurplusPredicates {
            rule_id,
            predicates,
        }) => format!(
            "the smt-lemma {rule_id} has surplus predicates: {}",
            predicates.len()
        ),
        SmtError::Translation(
            translation @ (TranslationError::PlaceholderOutOfBounds { .. }
            | TranslationError::UnsupportedPredicate(_)
            | TranslationError::ParametricSort(_)
            | TranslationError::MissingSmtLemmaVariable { .. }),
        ) => format!("{translation:?}"),
        error @ (SmtError::Unavailable
        | SmtError::Unknown(_)
        | SmtError::InconsistentGroundTruth
        | SmtError::MissingModel
        | SmtError::MissingModelValue(_)
        | SmtError::InvalidModelValue { .. }) => format!("{error:?}"),
    }
}

fn describe_predicate(predicate: &Predicate, sort: &Sort) -> String {
    KorePrinter::pretty(100).print_pattern(&externalize::ml_pattern(predicate, sort))
}

fn describe_predicates(predicates: &[Predicate], sort: &Sort) -> String {
    predicates
        .iter()
        .map(|predicate| format!("\n{}", describe_predicate(predicate, sort)))
        .collect()
}

fn describe_equalities(equalities: &[(Term, Term)]) -> String {
    equalities
        .iter()
        .map(|(left, right)| {
            format!(
                "\n{} = {}",
                KorePrinter::compact().print_pattern(&externalize::term(left)),
                KorePrinter::compact().print_pattern(&externalize::term(right))
            )
        })
        .collect()
}

fn search_incomplete_disposition(incomplete: &IncompleteSearch) -> IncompleteDisposition {
    match incomplete {
        IncompleteSearch::DepthBound(_) => IncompleteDisposition::UserLimit,
        // An exceeded `--breadth` fails the run although it is a limit the user asked for, like
        // `--depth` and `--bound`; this arm is where that decision is made, apart from the
        // engine failures, so that it can be revisited on its own.
        IncompleteSearch::BreadthBound(_) => IncompleteDisposition::Failure,
        IncompleteSearch::Indeterminate { .. }
        | IncompleteSearch::Stopped { .. }
        | IncompleteSearch::Simplification { .. }
        | IncompleteSearch::Match { .. }
        | IncompleteSearch::Smt { .. } => IncompleteDisposition::Failure,
    }
}

/// Match `Kore.Exec.getExitCode` over the merged, non-bottom final configurations.
fn exit_code_of(
    backend: &BackendDefinition,
    solver: &dyn SmtSolver,
    finals: &[&ExecutionLeaf],
    max_iterations: usize,
) -> Result<u8, Box<dyn Error>> {
    let Some(symbol) = backend.symbols().get("LblgetExitCode") else {
        return Ok(0);
    };
    let mut results = BTreeSet::new();
    // Invariant: results contains the distinct satisfiable exit values of leaves already visited.
    for leaf in finals {
        let simplified = simplify_pattern_with_solver(
            backend,
            &Pattern {
                term: Term::application(
                    symbol.clone(),
                    Vec::new(),
                    vec![leaf.pattern.term.clone()],
                ),
                constraints: leaf.pattern.constraints.clone(),
            },
            SimplificationOptions {
                max_iterations,
                ..SimplificationOptions::default()
            },
            solver,
        )
        .map_err(|stop| stop.into_cause().to_string())
        .and_then(|simplified| simplified.map_err(|error| error.to_string()))
        .map_err(|error| {
            io::Error::other(format!(
                "could not evaluate getExitCode on a final configuration: {error}"
            ))
        })?;
        if !simplified
            .constraints
            .iter()
            .any(|predicate| matches!(predicate, Predicate::False))
        {
            results.insert(simplified.term);
        }
    }

    let mut distinct = results.into_iter();
    let Some(term) = distinct.next() else {
        return Ok(111);
    };
    if distinct.next().is_some() {
        return Ok(111);
    }
    Ok(term_exit_code(&term).unwrap_or(111))
}

pub fn term_exit_code(term: &Term) -> Option<u8> {
    let TermKind::DomainValue { sort, value } = term.kind() else {
        return None;
    };
    if !sort.is_builtin(BuiltinSort::Int) {
        return None;
    }
    let value = value.as_utf8().ok()?.parse::<BigInt>().ok()?;
    let modulus = BigInt::from(256_u16);
    (((value % &modulus) + &modulus) % modulus).to_u8()
}

/// The target of a search given no target pattern: one variable, at the sort of the first
/// initial term, that matches every state the search reaches.
///
/// It is spelled `VarResult`, reference krun's KORE spelling of the K variable `Result`, unless a
/// variable of the request (free or bound, in any initial pattern) is already spelled so; then it
/// is `VarResult{N}` for the least `N` that no request variable spells. The target is a pattern
/// of the request, so its variable must be apart from every request variable: one of the same
/// name would be identified with it by the match, or share its printed name at another sort, and
/// the search would answer about other states than those reached.
///
/// `None` when there is no initial pattern.
pub fn default_search_pattern(initial: &[Pattern]) -> Option<Pattern> {
    let sort = initial.first()?.term.sort();
    let request = RequestNames::of(&initial.iter().collect::<Vec<_>>());
    let name = std::iter::once("VarResult".to_owned())
        .chain((0_u64..).map(|index| format!("VarResult{index}")))
        .find(|name| !request.spells(name))?;
    Some(Pattern {
        term: Term::variable(Variable::new(name, sort)),
        constraints: Vec::new(),
    })
}

/// The search target read from `path`, with the spellings of the target as read, which
/// unfolding its aliases may drop from the internalized pattern.
fn load_backend_target(
    definition: &BackendDefinition,
    path: &Path,
    purpose: &str,
) -> Result<BackendMatchTarget, Box<dyn Error>> {
    let input = fs::read(path)?;
    let syntax = decode_kore_syntax(path, purpose, &input)?;
    let pattern = definition
        .verify_standalone_pattern(&syntax, &[])?
        .internalize_pattern()?;
    Ok(BackendMatchTarget {
        pattern,
        generated_anonymous_variables: BTreeSet::new(),
        request_names: RequestNames::of_received(&[&syntax]),
    })
}

fn load_backend_patterns(
    definition: &BackendDefinition,
    path: &Path,
    purpose: &str,
) -> Result<Vec<Pattern>, Box<dyn Error>> {
    let input = fs::read(path)?;
    let syntax = decode_kore_syntax(path, purpose, &input)?;
    let admitted = definition.verify_standalone_pattern(&syntax, &[])?;
    definition.validate_executable_pattern(&syntax)?;
    admitted.internalize_disjunction().map_err(Into::into)
}

fn decode_kore_syntax(
    path: &Path,
    purpose: &str,
    input: &[u8],
) -> Result<KorePattern, Box<dyn Error>> {
    kore_codec::decode_bytes(input)
        .map_err(|error| invalid_kore_pattern(path, purpose, error.encoding, error.cause))
}

fn invalid_kore_pattern(
    path: &Path,
    purpose: &str,
    encoding: impl fmt::Display,
    error: impl fmt::Display,
) -> Box<dyn Error> {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!(
            "could not decode {purpose} {encoding} KORE pattern {}: {error}",
            path.display()
        ),
    )
    .into()
}

fn pattern_match_error(error: PatternMatchError) -> io::Error {
    io::Error::other(format!("KORE pattern match was indeterminate: {error:?}"))
}

#[cfg(test)]
mod captured_stdout_tests {
    use std::sync::Arc;

    use k_rust_backend::{
        rewrite::{ExecutionLeaf, HaltReason, Pattern},
        rule::Predicate,
        term::{CollectionSymbols, ListDefinition, MapDefinition, Sort, Symbol, Term},
        transition::ExecutionIoState,
    };

    use super::{captured_stdout_buffer, stdout_stream_buffers};

    fn app(name: &str, arguments: Vec<Term>) -> Term {
        let sort = Sort::simple("SortK");
        let symbol = Symbol::constructor(name, arguments.iter().map(Term::sort).collect(), sort);
        Term::application(Arc::new(symbol), Vec::new(), arguments)
    }

    fn item(term: Term) -> Term {
        app("LblListItem", vec![term])
    }

    fn list(items: Vec<Term>) -> Term {
        let mut items = items.into_iter();
        let first = items.next().unwrap();
        items.fold(first, |left, right| {
            app("Lbl'Unds'List'Unds'", vec![left, right])
        })
    }

    fn stdout_cell(buffer: Term) -> Term {
        app(
            "Lbl'-LT-'output'-GT-'",
            vec![list(vec![
                item(app(
                    "Lbl'Hash'ostream",
                    vec![Term::domain_value(Sort::simple("SortInt"), "1")],
                )),
                item(Term::domain_value(Sort::simple("SortString"), "off")),
                item(buffer),
            ])],
        )
    }

    fn buffer(value: Term) -> Term {
        app(
            "Lbl'Hash'buffer",
            vec![app("kseq", vec![value, app("dotk", vec![])])],
        )
    }

    #[test]
    fn finds_only_well_shaped_stdout_cells_and_preserves_shared_occurrences() {
        let output = stdout_cell(buffer(Term::domain_value(
            Sort::simple("SortString"),
            "\u{0}ok\u{ff}",
        )));
        let shared = app("wrap", vec![output]);
        let doubled = app("pair", vec![shared.clone(), shared]);
        assert_eq!(
            stdout_stream_buffers(&doubled),
            vec![vec![0, b'o', b'k', 255]; 2]
        );

        let missing = app("other", vec![]);
        let non_list = app("Lbl'-LT-'output'-GT-'", vec![app("other", vec![])]);
        let non_string = stdout_cell(buffer(Term::domain_value(Sort::simple("SortInt"), "2")));
        let non_buffer = stdout_cell(app("other", vec![]));
        for malformed in [missing, non_list, non_string, non_buffer] {
            assert!(stdout_stream_buffers(&malformed).is_empty());
        }
    }

    fn list_definition(element: &str, sort: &str) -> Arc<ListDefinition> {
        Arc::new(ListDefinition {
            symbols: CollectionSymbols {
                unit: format!("Lbl'Stop'{sort}").into(),
                element: element.into(),
                concat: format!("Lbl'Unds'{sort}'Unds'").into(),
            },
            element_sort: "SortKItem".into(),
            list_sort: format!("Sort{sort}").into(),
        })
    }

    fn map_definition() -> Arc<MapDefinition> {
        Arc::new(MapDefinition {
            symbols: CollectionSymbols {
                unit: "Lbl'Stop'Map".into(),
                element: "Lbl'UndsPipe'-'-GT-Unds'".into(),
                concat: "Lbl'Unds'Map'Unds'".into(),
            },
            key_sort: "SortKItem".into(),
            value_sort: "SortKItem".into(),
            map_sort: "SortMap".into(),
        })
    }

    /// The three-item stream list `#ostream(1) "off" #buffer(text)` as an internal list.
    fn stream_items(text: &[u8]) -> Term {
        Term::list(
            list_definition("LblListItem", "List"),
            vec![
                app(
                    "Lbl'Hash'ostream",
                    vec![Term::domain_value(Sort::simple("SortInt"), "1")],
                ),
                Term::domain_value(Sort::simple("SortString"), "off"),
                buffer(Term::domain_value(
                    Sort::simple("SortString"),
                    text.to_vec(),
                )),
            ],
            None,
        )
    }

    fn internal_stdout_cell(text: &[u8]) -> Term {
        app("Lbl'-LT-'stdout'-GT-'", vec![stream_items(text)])
    }

    fn int(value: u32) -> Term {
        Term::domain_value(Sort::simple("SortInt"), value.to_string())
    }

    fn sorted(mut buffers: Vec<Vec<u8>>) -> Vec<Vec<u8>> {
        buffers.sort();
        buffers
    }

    /// `backend.execution.captured_stdout`: every stdout stream cell of the externalized leaf is
    /// found, wherever an internal Map, List or Set holds it: Map keys, values and rest, List
    /// heads, middle and tails, Set elements and rest.
    #[test]
    fn finds_stdout_cells_held_by_maps_lists_and_sets() {
        let cell = |byte: u8| internal_stdout_cell(&[byte]);
        let map = Term::map(
            map_definition(),
            vec![
                (int(1), app("Lbl'-LT-'thread'-GT-'", vec![cell(b'a')])),
                (app("key", vec![cell(b'b')]), int(2)),
            ],
            Some(app("restMap", vec![cell(b'c')])),
        );
        let list = Term::list(
            list_definition("LblListItem", "List"),
            vec![cell(b'd'), int(3)],
            Some((
                app("middleList", vec![cell(b'e')]),
                vec![int(4), cell(b'f')],
            )),
        );
        let set = Term::set(
            list_definition("LblSetItem", "Set"),
            vec![cell(b'g'), int(5)],
            Some(app("restSet", vec![cell(b'h')])),
        );
        for (collection, expected) in [
            (&map, &b"abc"[..]),
            (&list, &b"def"[..]),
            (&set, &b"gh"[..]),
        ] {
            let configuration = app("Lbl'-LT-'generatedTop'-GT-'", vec![collection.clone()]);
            assert_eq!(
                sorted(stdout_stream_buffers(&configuration)),
                expected.iter().map(|byte| vec![*byte]).collect::<Vec<_>>(),
                "{collection:?}"
            );
        }
        let all = app("top", vec![map, list, set]);
        assert_eq!(
            sorted(stdout_stream_buffers(&all)),
            b"abcdefgh"
                .iter()
                .map(|byte| vec![*byte])
                .collect::<Vec<_>>()
        );
    }

    /// `backend.execution.captured_stdout`: a collection element exists as an application only
    /// in the externalized term, so a List or Set whose element symbol is itself a stdout cell
    /// label holds a stdout cell at each element.
    #[test]
    fn finds_stdout_cells_formed_by_collection_elements() {
        let list = Term::list(
            list_definition("Lbl'-LT-'out'-GT-'", "OutList"),
            vec![stream_items(b"head")],
            Some((app("middle", vec![]), vec![stream_items(b"tail")])),
        );
        let set = Term::set(
            list_definition("Lbl'-LT-'out'-GT-'", "OutSet"),
            vec![stream_items(b"element")],
            None,
        );
        assert_eq!(
            sorted(stdout_stream_buffers(&app("top", vec![list, set]))),
            vec![b"element".to_vec(), b"head".to_vec(), b"tail".to_vec()]
        );
    }

    fn leaf(term: Term, constraints: Vec<Predicate>, halt_reason: HaltReason) -> ExecutionLeaf {
        ExecutionLeaf {
            pattern: Pattern { term, constraints },
            depth: 7,
            trace: Vec::new(),
            branch: Vec::new(),
            observations: Vec::new(),
            effects: Vec::new(),
            io: ExecutionIoState::default(),
            halt_reason,
            diagnostics: Vec::new(),
        }
    }

    /// `backend.execution.captured_stdout`: captured output exists only for one unconstrained,
    /// complete leaf holding exactly one stdout stream, here under a Map-shaped configuration.
    #[test]
    fn captured_output_requires_one_complete_unconstrained_leaf_with_one_stream() {
        let configuration = |cells: &[&[u8]]| {
            Term::map(
                map_definition(),
                cells
                    .iter()
                    .enumerate()
                    .map(|(key, text)| {
                        let key = u32::try_from(key).unwrap();
                        (int(key), internal_stdout_cell(text))
                    })
                    .collect(),
                None,
            )
        };
        let terminal = || HaltReason::TerminalRule { rule: "r".into() };
        for halt_reason in [HaltReason::Stuck, terminal()] {
            let leaf = leaf(configuration(&[b"out"]), Vec::new(), halt_reason);
            assert_eq!(captured_stdout_buffer(&[&leaf]).unwrap(), b"out");
        }

        let none = leaf(configuration(&[]), Vec::new(), HaltReason::Stuck);
        let two = leaf(configuration(&[b"1", b"2"]), Vec::new(), HaltReason::Stuck);
        let constrained = leaf(configuration(&[b"out"]), vec![Predicate::True], terminal());
        let one = leaf(configuration(&[b"out"]), Vec::new(), HaltReason::Stuck);
        let bounded = leaf(configuration(&[b"out"]), Vec::new(), HaltReason::DepthBound);
        for (finals, message) in [
            (vec![], "found 0 leaves"),
            (
                vec![&none],
                "found 1 leaf: constraints=0, stdout stream buffers=0",
            ),
            (
                vec![&two],
                "found 1 leaf: constraints=0, stdout stream buffers=2",
            ),
            (
                vec![&constrained],
                "found 1 leaf: constraints=1, stdout stream buffers=1",
            ),
            (
                vec![&one, &one],
                "found 2 leaves: constraints=0, stdout stream buffers=1; constraints=0, stdout stream buffers=1",
            ),
            (vec![&bounded], "leaf halted at depth 7 with DepthBound"),
        ] {
            let error = captured_stdout_buffer(&finals).unwrap_err().to_string();
            assert!(error.ends_with(message), "{error}");
        }
    }
}
