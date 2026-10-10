//! Every reason the backend gives for an outcome, in words.
//!
//! A reason is a fact about the request, the definition, the solver or the backend's limits, and
//! a reader is told that fact, never the Rust value that carries it. Each reason type has one
//! description: `Display` when the reason carries everything its words need, and `at(sort)` when
//! it names a predicate, which is printed as a pattern of the sort of the state it constrains.
//! Every description is an exhaustive `match` without a catch-all arm, so a new variant does not
//! compile until it is given words.

use std::fmt::{self, Display};

use k_rust_kore::kore::printer::Printer;

use crate::{
    builtin::BuiltinError,
    externalize,
    rewrite::{AppliedRule, HaltReason, IndeterminateReason},
    rule::Predicate,
    search::{IncompleteSearch, PatternMatchError},
    simplify::{ConditionIndeterminacy, SimplificationError},
    smt::{Satisfiability, SmtError, TranslationError},
    term::{Sort, Term, Variable},
};

/// A reason together with the sort of the state it concerns, which its predicates are printed
/// at: the value of [`HaltReason::at`], [`IndeterminateReason::at`] and
/// [`SimplificationError::at`].
pub struct AtSort<'a, T> {
    reason: &'a T,
    sort: &'a Sort,
}

impl HaltReason {
    /// Why a leaf halted; a predicate it names is printed at `sort`, the sort of the leaf's term.
    pub fn at<'a>(&'a self, sort: &'a Sort) -> AtSort<'a, Self> {
        AtSort { reason: self, sort }
    }
}

impl IndeterminateReason {
    /// Why a step could not decide its successors; a predicate it names is printed at `sort`,
    /// the sort of the state.
    pub fn at<'a>(&'a self, sort: &'a Sort) -> AtSort<'a, Self> {
        AtSort { reason: self, sort }
    }
}

impl SimplificationError {
    /// The failure with the term or predicate it names printed below it; a predicate is
    /// printed at `sort`, the sort of the pattern it constrains. `Display` gives the sentence
    /// alone.
    pub fn at<'a>(&'a self, sort: &'a Sort) -> AtSort<'a, Self> {
        AtSort { reason: self, sort }
    }
}

impl PatternMatchError {
    /// Why a match against a target pattern was not decided; a predicate it names is printed
    /// at `sort`, the sort of the target's term.
    pub fn at<'a>(&'a self, sort: &'a Sort) -> AtSort<'a, Self> {
        AtSort { reason: self, sort }
    }
}

fn pretty_term(term: &Term) -> String {
    Printer::pretty(100).print_pattern(&externalize::term(term))
}

fn compact_term(term: &Term) -> String {
    Printer::compact().print_pattern(&externalize::term(term))
}

fn pretty_predicate(predicate: &Predicate, sort: &Sort) -> String {
    Printer::pretty(100).print_pattern(&externalize::ml_pattern(predicate, sort))
}

fn printed_sort(sort: &Sort) -> String {
    externalize::sort(sort).to_string()
}

fn printed_variable(variable: &Variable) -> String {
    externalize::external_variable_name(&variable.name)
}

/// Each predicate on its own line, after a line break.
fn predicate_lines(predicates: &[Predicate], sort: &Sort) -> String {
    predicates
        .iter()
        .map(|predicate| format!("\n{}", pretty_predicate(predicate, sort)))
        .collect()
}

/// Each equation `left = right` of a match remainder on its own line, after a line break.
fn equality_lines(equalities: &[(Term, Term)]) -> String {
    equalities
        .iter()
        .map(|(left, right)| format!("\n{} = {}", compact_term(left), compact_term(right)))
        .collect()
}

/// `items` joined as an English list: `A`, `A and B`, `A, B and C`.
fn english_list(items: &[String]) -> String {
    match items {
        [] => String::new(),
        [only] => only.clone(),
        [init @ .., last] => format!("{} and {last}", init.join(", ")),
    }
}

/// A rule as a reader knows it: its label, or its unique id when it has none.
fn rule_name<'a>(label: Option<&'a str>, unique_id: &'a str) -> &'a str {
    label.unwrap_or(unique_id)
}

fn applied_rule_names(applied: &[AppliedRule]) -> String {
    english_list(
        &applied
            .iter()
            .map(|rule| rule_name(rule.label.as_deref(), &rule.unique_id).to_owned())
            .collect::<Vec<_>>(),
    )
}

fn plural(count: usize, one: &str, many: &str) -> String {
    format!("{count} {}", if count == 1 { one } else { many })
}

impl Display for AtSort<'_, HaltReason> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.reason {
            HaltReason::Stopped(cause) => write!(formatter, "{cause}"),
            HaltReason::Stuck => formatter.write_str("no rule rewrites the state"),
            HaltReason::Trivial {
                depth,
                rule_id,
                label,
                ..
            } => match rule_id {
                Some(rule_id) => write!(
                    formatter,
                    "rule {} applies and gives the state no defined successor at depth {depth}",
                    rule_name(label.as_deref(), rule_id)
                ),
                None => write!(
                    formatter,
                    "the step gives the state no defined successor at depth {depth}"
                ),
            },
            HaltReason::Vacuous {
                depth,
                rule_id,
                label,
                ..
            } => match rule_id {
                Some(rule_id) => write!(
                    formatter,
                    "the path condition became unsatisfiable at depth {depth}, after rule {}",
                    rule_name(label.as_deref(), rule_id)
                ),
                None => write!(
                    formatter,
                    "the path condition became unsatisfiable at depth {depth}"
                ),
            },
            HaltReason::Branch {
                branches,
                remainder,
            } => {
                write!(
                    formatter,
                    "the step branches into {} by rules {}",
                    plural(branches.len(), "successor", "successors"),
                    applied_rule_names(branches)
                )?;
                match remainder {
                    Some(remainder) => write!(
                        formatter,
                        ", and the remainder where none of rules {} applies",
                        english_list(&remainder.rule_ids)
                    ),
                    None => Ok(()),
                }
            }
            HaltReason::CutPointRule { rule, next_states } => write!(
                formatter,
                "the cut-point rule {rule} applies, with {}",
                plural(next_states.len(), "next state", "next states")
            ),
            HaltReason::TerminalRule { rule } => {
                write!(formatter, "the terminal rule {rule} applied")
            }
            HaltReason::DepthBound => formatter.write_str("the depth bound was reached"),
            HaltReason::BreadthBound => formatter.write_str("the breadth bound was exceeded"),
            HaltReason::Indeterminate(reason) => write!(formatter, "{}", reason.at(self.sort)),
            HaltReason::Simplification(error) => write!(formatter, "{}", error.at(self.sort)),
        }
    }
}

impl Display for AtSort<'_, IndeterminateReason> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.reason {
            IndeterminateReason::SurvivingMacroOrAlias { symbol } => write!(
                formatter,
                "the macro or alias symbol {symbol} survived into an executable term"
            ),
            IndeterminateReason::Match {
                rule_id, remainder, ..
            } => write!(
                formatter,
                "rule {rule_id} matched with an undecided remainder:{}",
                equality_lines(remainder)
            ),
            IndeterminateReason::Instantiation {
                rule_id,
                missing_variables,
            } => write!(
                formatter,
                "rule {rule_id} leaves {} uninstantiated in concrete execution",
                missing_variables
                    .iter()
                    .map(printed_variable)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            IndeterminateReason::Requires {
                rule_id,
                predicates,
            } => write!(
                formatter,
                "the requires clause of rule {rule_id} is undecided:{}",
                predicate_lines(predicates, self.sort)
            ),
            IndeterminateReason::Smt { rule_id, error } => {
                write!(formatter, "the solver failed on rule {rule_id}: {error}")
            }
            IndeterminateReason::Remainder {
                rule_ids,
                predicates,
                satisfiability,
            } => {
                write!(
                    formatter,
                    "the remainder of rules {} is undecided (",
                    rule_ids.join(", ")
                )?;
                match satisfiability {
                    Ok(satisfiability) => write!(formatter, "{satisfiability}")?,
                    Err(error) => write!(formatter, "{error}")?,
                }
                write!(formatter, "):{}", predicate_lines(predicates, self.sort))
            }
        }
    }
}

impl Display for SimplificationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Builtin(error) => write!(formatter, "{error}"),
            Self::DisjunctiveResult {
                rule_id,
                alternatives,
            } => write!(
                formatter,
                "equation {rule_id} gives {alternatives} alternative results where simplification needs one"
            ),
            Self::Smt { rule_id, error } => {
                write!(formatter, "the solver failed on rule {rule_id}: {error}")
            }
            Self::SmtPredicate { error, .. } => {
                write!(formatter, "the solver failed ({error}) on a predicate")
            }
            Self::IterationLimit { limit, .. } => write!(
                formatter,
                "simplification reached its limit of {limit} iterations on a term"
            ),
            Self::PredicateIterationLimit { limit, .. } => write!(
                formatter,
                "simplification reached its limit of {limit} iterations on a predicate"
            ),
            Self::InvalidBuiltinResultSymbol { hook, symbol } => write!(
                formatter,
                "the result of hook {hook} is the symbol {symbol}, which the definition does not declare as a constant"
            ),
            Self::UnsupportedHook { hook, reason, .. } => write!(
                formatter,
                "unsupported hook '{hook}' on constructor-like arguments: {reason}"
            ),
        }
    }
}

impl Display for AtSort<'_, SimplificationError> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let error = self.reason;
        match error {
            SimplificationError::UnsupportedHook { term, .. } => {
                write!(formatter, "{error}\n{}", pretty_term(term))
            }
            SimplificationError::IterationLimit { limit, term } => write!(
                formatter,
                "simplification reached its limit of {limit} iterations on\n{}",
                pretty_term(term)
            ),
            SimplificationError::PredicateIterationLimit { limit, predicate } => write!(
                formatter,
                "simplification reached its limit of {limit} iterations on the predicate\n{}",
                pretty_predicate(predicate, self.sort)
            ),
            SimplificationError::SmtPredicate { predicate, error } => write!(
                formatter,
                "the solver failed ({error}) on the predicate\n{}",
                pretty_predicate(predicate, self.sort)
            ),
            SimplificationError::Builtin(_)
            | SimplificationError::DisjunctiveResult { .. }
            | SimplificationError::Smt { .. }
            | SimplificationError::InvalidBuiltinResultSymbol { .. } => {
                write!(formatter, "{error}")
            }
        }
    }
}

impl Display for BuiltinError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongArity {
                hook,
                expected,
                actual,
            } => write!(
                formatter,
                "hook {hook} takes {} and was given {actual}",
                plural(*expected, "argument", "arguments")
            ),
            Self::UnexpectedSort {
                hook,
                expected,
                actual,
            } => write!(
                formatter,
                "hook {hook} takes an argument of sort {} and was given one of sort {}",
                printed_sort(expected),
                printed_sort(actual)
            ),
            Self::AlternativeSortsDiffer {
                then_sort,
                else_sort,
            } => write!(
                formatter,
                "the alternatives of a conditional have different sorts, {} and {}",
                printed_sort(then_sort),
                printed_sort(else_sort)
            ),
            Self::IncompatibleMapSorts { left, right } => write!(
                formatter,
                "maps of the sorts {} and {} cannot be combined",
                printed_sort(left),
                printed_sort(right)
            ),
            Self::InvalidFloatToken { hook, token } => write!(
                formatter,
                "hook {hook} cannot read {token} as a floating-point number"
            ),
            Self::UnsupportedFloatFormat {
                hook,
                precision,
                exponent_bits,
            } => write!(
                formatter,
                "hook {hook} does not compute on floating-point numbers of precision {precision} with {exponent_bits} exponent bits"
            ),
            Self::UnsupportedFloatFormatParameters {
                hook,
                precision,
                exponent_bits,
            } => write!(
                formatter,
                "hook {hook} cannot read a floating-point format of precision {precision} with {exponent_bits} exponent bits"
            ),
            Self::MismatchedFloatFormats {
                hook,
                left_precision,
                left_exponent_bits,
                right_precision,
                right_exponent_bits,
            } => write!(
                formatter,
                "hook {hook} was given floating-point numbers of two formats, precision {left_precision} with {left_exponent_bits} exponent bits and precision {right_precision} with {right_exponent_bits} exponent bits"
            ),
        }
    }
}

impl Display for ConditionIndeterminacy {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoSolver => formatter.write_str("no solver was asked to decide it"),
            Self::ImplicationIndeterminate => formatter
                .write_str("the path condition neither implies it nor refutes it"),
            Self::SmtUnknown(reason) => {
                write!(formatter, "the solver did not decide it ({reason})")
            }
            Self::InconsistentPathCondition => formatter
                .write_str("the solver found the path condition it was decided under unsatisfiable"),
            Self::Untranslatable(error) => {
                write!(formatter, "the solver's encoding cannot pose it: {error}")
            }
            Self::NonFunctionalBinding => formatter.write_str(
                "the match binds an element variable to a pattern containing a set variable, which is not known to denote a single value",
            ),
            Self::UnboundResultVariables(variables) => write!(
                formatter,
                "the right-hand side or ensures uses {}, which the left-hand side does not bind",
                english_list(variables)
            ),
        }
    }
}

impl Display for Satisfiability {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Sat => formatter.write_str("the solver found a model"),
            Self::Unsat => formatter.write_str("the solver found it unsatisfiable"),
            Self::Unknown(reason) => write!(formatter, "the solver did not decide it ({reason})"),
        }
    }
}

impl Display for SmtError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Translation(error) => write!(formatter, "{error}"),
            Self::Unavailable => formatter.write_str("no solver is available"),
            Self::Unknown(reason) => write!(formatter, "the solver did not decide it ({reason})"),
            Self::InconsistentGroundTruth => {
                formatter.write_str("the solver found the path condition unsatisfiable")
            }
            Self::MissingModel => formatter.write_str("the solver gave no model"),
            Self::MissingModelValue(variable) => write!(
                formatter,
                "the solver's model gives no value to {}",
                printed_variable(variable)
            ),
            Self::InvalidModelValue { variable, value } => write!(
                formatter,
                "the solver's model gives {} the value {value}, which is not a value of its sort",
                printed_variable(variable)
            ),
        }
    }
}

impl Display for TranslationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NonBooleanAnd(term) => write!(
                formatter,
                "a term conjunction that is not Boolean cannot be translated: {}",
                compact_term(term)
            ),
            Self::PlaceholderOutOfBounds {
                placeholder,
                arguments,
            } => write!(
                formatter,
                "an SMT hook names its argument #{placeholder} on an application of {}",
                plural(*arguments, "argument", "arguments")
            ),
            Self::UnsupportedPredicate(connective) => {
                write!(formatter, "the encoding has no translation of {connective}")
            }
            Self::ParametricSort(sort) => write!(
                formatter,
                "the encoding has no translation of the parametric sort {}",
                printed_sort(sort)
            ),
            Self::SmtLemmaSurplusMappings { rule_id, terms } => write!(
                formatter,
                "the smt-lemma {rule_id} maps surplus terms: {}",
                terms
                    .iter()
                    .map(compact_term)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::SmtLemmaSurplusPredicates {
                rule_id,
                predicates,
            } => write!(
                formatter,
                "the smt-lemma {rule_id} has surplus predicates: {}",
                predicates.len()
            ),
            Self::MissingSmtLemmaVariable { rule_id, variable } => write!(
                formatter,
                "the smt-lemma {rule_id} gives its variable {} no translation of its own",
                printed_variable(variable)
            ),
        }
    }
}

impl Display for AtSort<'_, PatternMatchError> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.reason {
            PatternMatchError::Indeterminate { remainder, .. } => write!(
                formatter,
                "the match left an undecided remainder:{}",
                equality_lines(remainder)
            ),
            PatternMatchError::Simplification(error) => {
                write!(formatter, "{}", error.at(self.sort))
            }
            PatternMatchError::Smt(error) => write!(formatter, "the solver failed: {error}"),
        }
    }
}

/// A reader's account of a search entry left incomplete: the reason, the terms it names and the
/// state's configuration, each term printed in KORE, and the state's depth.
impl Display for IncompleteSearch {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (state, reason) = match self {
            Self::DepthBound(state) => (state, "the depth bound was reached".to_owned()),
            Self::BreadthBound(states) => {
                return write!(
                    formatter,
                    "the breadth bound was exceeded with {} states at the frontier",
                    states.len()
                );
            }
            Self::Indeterminate { state, reason } => {
                (state, reason.at(&state.pattern.term.sort()).to_string())
            }
            Self::Stopped { state, cause } => (state, cause.to_string()),
            Self::Simplification { state, error } => {
                (state, error.at(&state.pattern.term.sort()).to_string())
            }
            Self::Match {
                state, remainder, ..
            } => (
                state,
                format!(
                    "the match of the target pattern left an undecided remainder:{}",
                    equality_lines(remainder)
                ),
            ),
            Self::Smt { state, error } => (state, format!("the solver failed: {error}")),
        };
        write!(
            formatter,
            "{reason}\nin the state at depth {}:\n{}",
            state.depth,
            Printer::pretty(100).print_pattern(&externalize::constrained_pattern(&state.pattern))
        )
    }
}
