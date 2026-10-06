//! In-process evaluation of backend hooks implemented by Booster: dispatch by `HookName` to the
//! per-namespace modules, each hook a bounded computation on evaluated arguments; counted by the
//! caller as `Counter::SimplifyBuiltinEvaluations`; a responsibility, not an algorithm; no
//! worklist.

use std::{fmt, sync::Arc};

use num_bigint::{BigInt, Sign};
use num_traits::{One, Signed, ToPrimitive, Zero};

mod bytes;
mod float;
#[cfg(test)]
mod hook_models;
mod krypto;
mod list;
mod map;
mod set;
mod string;
mod substitution;

pub(crate) use substitution::KVarSorts;

use k_rust_kore::names::{BuiltinSort, WellKnownSymbol};

use crate::{
    definition::BackendDefinition,
    matching::{InjectionEquality, SortGraph, match_injection_equality},
    stop::{Layered, Stoppable, Unwind},
    term::{
        Sort, Term, TermKind,
        head::{FixedRoot, Head, NoEvidence, RootComparison, classify_value, compare_roots},
        names::{HookName, HookNamespace},
    },
    transition::ExecutionEvaluationContext,
};

/// The result of a hook inside this module: `?` propagates a stop and a failure alike, and the
/// public entry points separate them with [`Layered::layered`].
pub(crate) type HookResult<T> = Result<T, Unwind<BuiltinError>>;

/// A failure determined by a hook's arguments, separate from a stop of its evaluation.
///
/// An interruption cannot be constructed as a builtin failure:
///
/// ```compile_fail,E0599
/// use k_rust_backend::builtin::BuiltinError;
/// let _ = BuiltinError::Interrupted;
/// ```
///
/// An argument failure can be constructed:
///
/// ```
/// use k_rust_backend::builtin::BuiltinError;
/// let _ = BuiltinError::WrongArity { hook: "INT.add".into(), expected: 2, actual: 1 };
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum BuiltinError {
    WrongArity {
        hook: String,
        expected: usize,
        actual: usize,
    },
    UnexpectedSort {
        hook: String,
        expected: Sort,
        actual: Sort,
    },
    AlternativeSortsDiffer {
        then_sort: Sort,
        else_sort: Sort,
    },
    IncompatibleMapSorts {
        left: Sort,
        right: Sort,
    },
    InvalidFloatToken {
        hook: String,
        token: String,
    },
    UnsupportedFloatFormat {
        hook: String,
        precision: u32,
        exponent_bits: u32,
    },
    UnsupportedFloatFormatParameters {
        hook: String,
        precision: String,
        exponent_bits: String,
    },
    MismatchedFloatFormats {
        hook: String,
        left_precision: u32,
        left_exponent_bits: u32,
        right_precision: u32,
        right_exponent_bits: u32,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BuiltinResult {
    NotApplicable,
    Value(Term),
    Bottom,
    Effect(BuiltinEffect),
    Unsupported(UnsupportedHookReason),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum UnsupportedHookReason {
    NotImplemented,
    ArgumentOutOfRange {
        detail: String,
    },
    /// The application has a value, larger than a result size bound (such as
    /// [`MAX_INT_RESULT_BITS`]), that the backend does not compute. It is left unevaluated, a
    /// term that denotes that value, and it is not an unsupported-hook error on constructor-like
    /// arguments: the bound is a resource limit, not a missing implementation, and an error
    /// would fail runs that never use the value.
    ///
    /// An evaluator reports it only where the hook is defined (after its undefinedness checks),
    /// so the simplifier takes the application's `\ceil` to hold.
    ResultTooLarge {
        detail: String,
    },
    /// The definition does not determine the application's value: the hook is `total` and its
    /// documentation gives no value on these arguments, or the definition's documents disagree
    /// on whether a value exists. The application denotes whatever value the definition admits.
    /// It is left unevaluated, and it is not an unsupported-hook error on constructor-like
    /// arguments, since there is no value for an implementation to compute.
    Unspecified {
        detail: String,
    },
}

impl fmt::Display for UnsupportedHookReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotImplemented => formatter
                .write_str("no evaluator in this backend and no equations in the definition"),
            Self::ArgumentOutOfRange { detail } | Self::ResultTooLarge { detail } => {
                formatter.write_str(detail)
            }
            Self::Unspecified { detail } => {
                write!(
                    formatter,
                    "the definition does not determine its value: {detail}"
                )
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BuiltinEffect {
    UserLog(String),
}

impl BuiltinEffect {
    pub(crate) const fn hook(&self) -> &'static str {
        match self {
            Self::UserLog(_) => "IO.logString",
        }
    }
}

impl From<Option<Term>> for BuiltinResult {
    fn from(value: Option<Term>) -> Self {
        value.map_or(Self::NotApplicable, Self::Value)
    }
}

/// Evaluate a hooked application, returning `None` when its arguments are not determined enough.
///
/// A fallback on a builtin failure must first propagate the stop layer:
///
/// ```compile_fail,E0308
/// use k_rust_backend::{builtin::{evaluate, BuiltinResult}, stop::Stoppable, term::Term};
/// fn f(term: &Term) -> BuiltinResult {
///     evaluate(term).unwrap_or(BuiltinResult::NotApplicable)
/// }
/// ```
///
/// ```
/// use k_rust_backend::{builtin::{evaluate, BuiltinResult}, stop::Stoppable, term::Term};
/// fn f(term: &Term) -> Stoppable<BuiltinResult> {
///     Ok(evaluate(term)?.unwrap_or(BuiltinResult::NotApplicable))
/// }
/// ```
pub fn evaluate(term: &Term) -> Stoppable<Result<BuiltinResult, BuiltinError>> {
    evaluate_with_sort_graph(term, None).layered()
}

pub(crate) fn evaluate_in_definition(
    term: &Term,
    definition: &BackendDefinition,
) -> Stoppable<Result<BuiltinResult, BuiltinError>> {
    evaluate_with_definition(term, Some(definition)).layered()
}

/// Evaluate a hook candidate with buffered execution state available.
///
/// This entry point establishes the console capability boundary without exposing buffered
/// descriptors to pure simplification.
pub(crate) fn evaluate_in_execution(
    term: &Term,
    definition: &BackendDefinition,
    execution: &mut ExecutionEvaluationContext,
) -> Stoppable<Result<BuiltinResult, BuiltinError>> {
    evaluate_with_context(
        term,
        Some(definition.sort_graph()),
        Some(definition),
        Some(execution),
    )
    .layered()
}

fn evaluate_with_sort_graph(
    term: &Term,
    sort_graph: Option<&SortGraph>,
) -> HookResult<BuiltinResult> {
    evaluate_with_context(term, sort_graph, None, None)
}

fn evaluate_with_definition(
    term: &Term,
    definition: Option<&BackendDefinition>,
) -> HookResult<BuiltinResult> {
    evaluate_with_context(
        term,
        definition.map(|definition| definition.sort_graph()),
        definition,
        None,
    )
}

fn evaluate_with_context(
    term: &Term,
    sort_graph: Option<&SortGraph>,
    definition: Option<&BackendDefinition>,
    execution: Option<&mut ExecutionEvaluationContext>,
) -> HookResult<BuiltinResult> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(hook) = symbol.attributes.hook.as_deref() else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let result_sort = term.sort();
    evaluate_hook_with_context(
        hook,
        arguments,
        Some(&result_sort),
        sort_graph,
        definition,
        execution,
    )
}

pub use crate::term::names::PLUGIN_HOOK_NAMESPACES;
pub use float::is_float_syntax;

pub fn evaluate_hook(
    hook: &str,
    arguments: &[Term],
) -> Stoppable<Result<BuiltinResult, BuiltinError>> {
    evaluate_hook_with_context(hook, arguments, None, None, None, None).layered()
}

fn evaluate_hook_with_context(
    hook: &str,
    arguments: &[Term],
    result_sort: Option<&Sort>,
    sort_graph: Option<&SortGraph>,
    definition: Option<&BackendDefinition>,
    execution: Option<&mut ExecutionEvaluationContext>,
) -> HookResult<BuiltinResult> {
    crate::stop::check()?;
    match hook {
        "INT.ediv" => return int_partial_binary(hook, arguments, euclidean_division),
        "INT.emod" => return int_partial_binary(hook, arguments, euclidean_modulus),
        "INT.tdiv" => return int_partial_binary(hook, arguments, truncating_division),
        "INT.tmod" => return int_partial_binary(hook, arguments, truncating_modulus),
        "INT.pow" => return int_pow(arguments),
        "INT.powmod" => return int_powmod(arguments),
        "INT.log2" => return int_log2(arguments),
        "INT.shl" => return int_shift(hook, arguments, false),
        "INT.shr" => return int_shift(hook, arguments, true),
        _ => {}
    }
    let result = match hook {
        "BOOL.or" => bool_or(arguments),
        "BOOL.orElse" => bool_or(arguments),
        "BOOL.and" => bool_and(arguments),
        "BOOL.andThen" => bool_and(arguments),
        "BOOL.xor" => bool_binary(hook, arguments, |left, right| left != right),
        "BOOL.eq" => bool_binary(hook, arguments, |left, right| left == right),
        "BOOL.ne" => bool_binary(hook, arguments, |left, right| left != right),
        "BOOL.not" => bool_not(arguments),
        "BOOL.implies" => bool_implies(arguments),
        "INT.gt" => int_compare(hook, arguments, |left, right| left > right),
        "INT.ge" => int_compare(hook, arguments, |left, right| left >= right),
        "INT.eq" => int_compare(hook, arguments, |left, right| left == right),
        "INT.le" => int_compare(hook, arguments, |left, right| left <= right),
        "INT.lt" => int_compare(hook, arguments, |left, right| left < right),
        "INT.ne" => int_compare(hook, arguments, |left, right| left != right),
        "INT.add" => int_binary(hook, arguments, |left, right| left + right),
        "INT.sub" => int_binary(hook, arguments, |left, right| left - right),
        "INT.mul" => int_binary(hook, arguments, |left, right| left * right),
        "INT.abs" => int_abs(arguments),
        "INT.min" => int_binary(hook, arguments, std::cmp::min),
        "INT.max" => int_binary(hook, arguments, std::cmp::max),
        "INT.and" => int_binary(hook, arguments, |left, right| left & right),
        "INT.or" => int_binary(hook, arguments, |left, right| left | right),
        "INT.xor" => int_binary(hook, arguments, |left, right| left ^ right),
        "INT.not" => int_unary(hook, arguments, |value| !value),
        "KEQUAL.ite" => kequal_ite(arguments),
        "KEQUAL.eq" => kequal(arguments, false, sort_graph),
        "KEQUAL.ne" => kequal(arguments, true, sort_graph),
        "IO.logString" => return io_log_string(arguments),
        "IO.getc" => {
            return io_getc(arguments, result_sort, definition, execution);
        }
        "IO.read" => {
            return io_read(arguments, result_sort, execution);
        }
        "IO.putc" => {
            return io_putc(arguments, result_sort, definition, execution);
        }
        "IO.write" => {
            return io_write(arguments, result_sort, definition, execution);
        }
        _ => {
            return match HookName::parse(hook).map(HookName::kind) {
                Some(HookNamespace::List) => list::evaluate(hook, arguments, sort_graph),
                Some(HookNamespace::Map) => map::evaluate(hook, arguments, sort_graph),
                Some(HookNamespace::Set) => set::evaluate(hook, arguments, sort_graph),
                Some(HookNamespace::Bytes) => bytes::evaluate(hook, arguments),
                Some(HookNamespace::Float) => float::evaluate(hook, arguments),
                Some(HookNamespace::Plugin) => krypto::evaluate(hook, arguments, definition),
                Some(HookNamespace::String) => string::evaluate(hook, arguments, result_sort),
                Some(HookNamespace::Substitution) => {
                    substitution::evaluate(hook, arguments, definition)
                }
                _ => Ok(BuiltinResult::Unsupported(
                    UnsupportedHookReason::NotImplemented,
                )),
            };
        }
    }?;
    Ok(result.into())
}

fn execution_context(
    execution: Option<&mut ExecutionEvaluationContext>,
) -> Result<&mut ExecutionEvaluationContext, BuiltinResult> {
    execution.ok_or(BuiltinResult::Unsupported(
        UnsupportedHookReason::NotImplemented,
    ))
}

fn io_getc(
    arguments: &[Term],
    result_sort: Option<&Sort>,
    definition: Option<&BackendDefinition>,
    execution: Option<&mut ExecutionEvaluationContext>,
) -> HookResult<BuiltinResult> {
    let Ok(execution) = execution_context(execution) else {
        return Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::NotImplemented,
        ));
    };
    expect_arity("IO.getc", arguments, 1)?;
    let Some(descriptor) = read_int(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if descriptor != BigInt::ZERO {
        return Ok(unsupported_console_descriptor("IO.getc", &descriptor, 0));
    }
    let Some(result_sort) = result_sort else {
        return Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::NotImplemented,
        ));
    };
    let Some(byte) = execution.read(1).first().copied() else {
        let Some(definition) = definition else {
            return Ok(BuiltinResult::Unsupported(
                UnsupportedHookReason::NotImplemented,
            ));
        };
        const EOF_SYMBOL: &str = "Lbl'Hash'EOF";
        let Some(symbol) = definition.symbols().get(EOF_SYMBOL) else {
            return Ok(BuiltinResult::Unsupported(
                UnsupportedHookReason::ArgumentOutOfRange {
                    detail: format!("IO.getc result symbol {EOF_SYMBOL} is absent"),
                },
            ));
        };
        let value = Term::application(symbol.clone(), Vec::new(), Vec::new());
        return Ok(BuiltinResult::Value(inject_result(value, result_sort)));
    };
    Ok(BuiltinResult::Value(inject_result(
        int_term(BigInt::from(byte)),
        result_sort,
    )))
}

fn io_read(
    arguments: &[Term],
    result_sort: Option<&Sort>,
    execution: Option<&mut ExecutionEvaluationContext>,
) -> HookResult<BuiltinResult> {
    let Ok(execution) = execution_context(execution) else {
        return Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::NotImplemented,
        ));
    };
    expect_arity("IO.read", arguments, 2)?;
    let (Some(descriptor), Some(maximum)) = (read_int(&arguments[0]), read_int(&arguments[1]))
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if descriptor != BigInt::ZERO {
        return Ok(unsupported_console_descriptor("IO.read", &descriptor, 0));
    }
    let Some(maximum) = maximum.to_usize() else {
        return Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::ArgumentOutOfRange {
                detail: format!("IO.read length {maximum} is not representable as usize"),
            },
        ));
    };
    let Some(result_sort) = result_sort else {
        return Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::NotImplemented,
        ));
    };
    let bytes = execution.read(maximum);
    Ok(BuiltinResult::Value(inject_result(
        Term::domain_value(Sort::builtin(BuiltinSort::String), bytes.to_vec()),
        result_sort,
    )))
}

fn io_putc(
    arguments: &[Term],
    result_sort: Option<&Sort>,
    definition: Option<&BackendDefinition>,
    execution: Option<&mut ExecutionEvaluationContext>,
) -> HookResult<BuiltinResult> {
    let Ok(execution) = execution_context(execution) else {
        return Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::NotImplemented,
        ));
    };
    expect_arity("IO.putc", arguments, 2)?;
    let (Some(descriptor), Some(value)) = (read_int(&arguments[0]), read_int(&arguments[1])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(descriptor) = output_descriptor(&descriptor) else {
        return Ok(unsupported_console_descriptor("IO.putc", &descriptor, 1));
    };
    let Some(value) = value.to_u8() else {
        return Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::ArgumentOutOfRange {
                detail: format!("IO.putc value {value} is outside the byte range 0..=255"),
            },
        ));
    };
    let unit = io_k_unit("IO.putc", result_sort, definition);
    if !matches!(unit, BuiltinResult::Value(_)) {
        return Ok(unit);
    }
    execution.append("IO.putc", descriptor, Arc::<[u8]>::from([value]));
    Ok(unit)
}

fn io_write(
    arguments: &[Term],
    result_sort: Option<&Sort>,
    definition: Option<&BackendDefinition>,
    execution: Option<&mut ExecutionEvaluationContext>,
) -> HookResult<BuiltinResult> {
    let Ok(execution) = execution_context(execution) else {
        return Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::NotImplemented,
        ));
    };
    expect_arity("IO.write", arguments, 2)?;
    let Some(descriptor) = read_int(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(descriptor) = output_descriptor(&descriptor) else {
        return Ok(unsupported_console_descriptor("IO.write", &descriptor, 1));
    };
    let TermKind::DomainValue { sort, value } = arguments[1].kind() else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if !sort.is_builtin(BuiltinSort::String) {
        return Ok(BuiltinResult::NotApplicable);
    }
    let unit = io_k_unit("IO.write", result_sort, definition);
    if !matches!(unit, BuiltinResult::Value(_)) {
        return Ok(unit);
    }
    execution.append("IO.write", descriptor, Arc::<[u8]>::from(value.as_bytes()));
    Ok(unit)
}

fn io_k_unit(
    hook: &'static str,
    result_sort: Option<&Sort>,
    definition: Option<&BackendDefinition>,
) -> BuiltinResult {
    let (Some(result_sort), Some(definition)) = (result_sort, definition) else {
        return BuiltinResult::Unsupported(UnsupportedHookReason::NotImplemented);
    };
    let Some(dotk) = definition.symbols().get(WellKnownSymbol::DotK.as_str()) else {
        return BuiltinResult::Unsupported(UnsupportedHookReason::ArgumentOutOfRange {
            detail: format!(
                "{hook} result symbol {} is absent",
                WellKnownSymbol::DotK.as_str()
            ),
        });
    };
    if !dotk.sort_variables.is_empty() || !dotk.argument_sorts.is_empty() {
        return BuiltinResult::Unsupported(UnsupportedHookReason::ArgumentOutOfRange {
            detail: format!(
                "{hook} result symbol {} is not nullary",
                WellKnownSymbol::DotK.as_str()
            ),
        });
    }
    let mut dotk = dotk.as_ref().clone();
    dotk.result_sort = result_sort.clone();
    BuiltinResult::Value(Term::application(Arc::new(dotk), Vec::new(), Vec::new()))
}

fn output_descriptor(descriptor: &BigInt) -> Option<i32> {
    match descriptor.to_i32() {
        Some(descriptor @ (1 | 2)) => Some(descriptor),
        _ => None,
    }
}

fn unsupported_console_descriptor(
    hook: &'static str,
    descriptor: &BigInt,
    expected: i32,
) -> BuiltinResult {
    let direction = if expected == 0 { "input" } else { "output" };
    BuiltinResult::Unsupported(UnsupportedHookReason::ArgumentOutOfRange {
        detail: format!(
            "{hook} descriptor {descriptor} is not a supported console {direction} descriptor"
        ),
    })
}

fn inject_result(value: Term, result_sort: &Sort) -> Term {
    let source = value.sort();
    if &source == result_sort {
        value
    } else {
        Term::injection(source, result_sort.clone(), value)
    }
}

fn io_log_string(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("IO.logString", arguments, 1)?;
    let TermKind::DomainValue { sort, value } = arguments[0].kind() else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if !sort.is_builtin(BuiltinSort::String) {
        return Ok(BuiltinResult::NotApplicable);
    }
    let Ok(value) = value.as_utf8() else {
        return Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::ArgumentOutOfRange {
                detail: "IO.logString argument is not valid UTF-8".into(),
            },
        ));
    };
    Ok(BuiltinResult::Effect(BuiltinEffect::UserLog(
        value.to_owned(),
    )))
}

fn bool_or(arguments: &[Term]) -> HookResult<Option<Term>> {
    expect_arity("BOOL.or", arguments, 2)?;
    let [left, right] = arguments else {
        unreachable!()
    };
    Ok(match (read_bool(left), read_bool(right)) {
        (Some(true), _) | (_, Some(true)) => Some(bool_term(true)),
        (Some(false), Some(false)) => Some(bool_term(false)),
        _ => None,
    })
}

fn bool_and(arguments: &[Term]) -> HookResult<Option<Term>> {
    expect_arity("BOOL.and", arguments, 2)?;
    let [left, right] = arguments else {
        unreachable!()
    };
    Ok(match (read_bool(left), read_bool(right)) {
        (Some(false), _) | (_, Some(false)) => Some(bool_term(false)),
        (Some(true), Some(true)) => Some(bool_term(true)),
        _ => None,
    })
}

fn bool_binary(
    hook: &str,
    arguments: &[Term],
    operation: impl FnOnce(bool, bool) -> bool,
) -> HookResult<Option<Term>> {
    expect_arity(hook, arguments, 2)?;
    let [left, right] = arguments else {
        unreachable!()
    };
    Ok(read_bool(left)
        .zip(read_bool(right))
        .map(|(left, right)| bool_term(operation(left, right))))
}

fn bool_not(arguments: &[Term]) -> HookResult<Option<Term>> {
    expect_arity("BOOL.not", arguments, 1)?;
    Ok(read_bool(&arguments[0]).map(|value| bool_term(!value)))
}

fn bool_implies(arguments: &[Term]) -> HookResult<Option<Term>> {
    expect_arity("BOOL.implies", arguments, 2)?;
    let [left, right] = arguments else {
        unreachable!()
    };
    Ok(match (read_bool(left), read_bool(right)) {
        (Some(false), _) => Some(bool_term(true)),
        (Some(true), Some(right)) => Some(bool_term(right)),
        _ => None,
    })
}

fn int_compare(
    hook: &str,
    arguments: &[Term],
    comparison: impl FnOnce(&BigInt, &BigInt) -> bool,
) -> HookResult<Option<Term>> {
    expect_arity(hook, arguments, 2)?;
    if let Some((left, right)) = read_int(&arguments[0]).zip(read_int(&arguments[1])) {
        return Ok(Some(bool_term(comparison(&left, &right))));
    }
    if arguments[0] == arguments[1] {
        return Ok(match hook {
            "INT.eq" => Some(bool_term(true)),
            "INT.ne" => Some(bool_term(false)),
            _ => None,
        });
    }
    Ok(None)
}

fn int_binary(
    hook: &str,
    arguments: &[Term],
    operation: impl FnOnce(BigInt, BigInt) -> BigInt,
) -> HookResult<Option<Term>> {
    expect_arity(hook, arguments, 2)?;
    Ok(read_int(&arguments[0])
        .zip(read_int(&arguments[1]))
        .map(|(left, right)| int_term(operation(left, right))))
}

fn int_abs(arguments: &[Term]) -> HookResult<Option<Term>> {
    expect_arity("INT.abs", arguments, 1)?;
    Ok(read_int(&arguments[0]).map(|value| {
        if value.sign() == Sign::Minus {
            int_term(-value)
        } else {
            int_term(value)
        }
    }))
}

fn int_unary(
    hook: &str,
    arguments: &[Term],
    operation: impl FnOnce(BigInt) -> BigInt,
) -> HookResult<Option<Term>> {
    expect_arity(hook, arguments, 1)?;
    Ok(read_int(&arguments[0]).map(|value| int_term(operation(value))))
}

fn int_partial_binary(
    hook: &str,
    arguments: &[Term],
    operation: impl FnOnce(BigInt, BigInt) -> Option<BigInt>,
) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 2)?;
    let Some((left, right)) = read_int(&arguments[0]).zip(read_int(&arguments[1])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(operation(left, right)
        .map(int_term)
        .map_or(BuiltinResult::Bottom, BuiltinResult::Value))
}

fn truncating_division(left: BigInt, right: BigInt) -> Option<BigInt> {
    (!right.is_zero()).then(|| left / right)
}

fn truncating_modulus(left: BigInt, right: BigInt) -> Option<BigInt> {
    (!right.is_zero()).then(|| left % right)
}

fn euclidean_modulus(left: BigInt, right: BigInt) -> Option<BigInt> {
    if right.is_zero() {
        return None;
    }
    let modulus = right.abs();
    let remainder = left % &modulus;
    Some(if remainder.sign() == Sign::Minus {
        remainder + modulus
    } else {
        remainder
    })
}

fn euclidean_division(left: BigInt, right: BigInt) -> Option<BigInt> {
    let remainder = euclidean_modulus(left.clone(), right.clone())?;
    Some((left - remainder) / right)
}

/// The largest integer result, in bits, that `^Int` and `<<Int` compute: 2^20 bits, 315,653
/// decimal digits. A larger one is reported as too large (`ResultTooLarge`) instead of computed,
/// and the application stays unevaluated.
///
/// The bound keeps the cost of one hook application polynomial in the size of its arguments.
/// These two hooks are the only `Int` hooks whose result is exponential in that size: the
/// exponent or shift amount is written in a number of digits logarithmic in its value. (A
/// product has the size of its factors together, so a program that grows a value by
/// multiplication pays in each step for what it has already built.) The constant is chosen from
/// the cost of using the result: an `Int` is held as its decimal domain value and read back on
/// every hook application, and converting between decimal and binary grows faster than linearly
/// in the length: at 2^20 bits one conversion takes tens of milliseconds, at 2^22 bits about a
/// second, at 2^32 bits it does not end in practice. The constant folder uses the same bound, so
/// it never writes a value this backend would not compute.
pub const MAX_INT_RESULT_BITS: u64 = 1 << 20;

fn int_pow(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("INT.pow", arguments, 2)?;
    let Some((mut base, exponent)) = read_int(&arguments[0]).zip(read_int(&arguments[1])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if exponent.sign() == Sign::Minus {
        return Ok(BuiltinResult::Bottom);
    }
    if exponent.is_zero() || base.is_one() {
        return Ok(BuiltinResult::Value(int_term(BigInt::one())));
    }
    if base.is_zero() {
        return Ok(BuiltinResult::Value(int_term(BigInt::zero())));
    }
    if base == -BigInt::one() {
        let odd = (&exponent & BigInt::one()).is_one();
        return Ok(BuiltinResult::Value(int_term(if odd {
            -BigInt::one()
        } else {
            BigInt::one()
        })));
    }
    let Some(mut exponent) = exponent.to_u64() else {
        return Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::ResultTooLarge {
                detail: format!(
                    "{base} ^Int {exponent} needs more than {MAX_INT_RESULT_BITS} bits"
                ),
            },
        ));
    };
    // |base|^exponent has between (bits - 1) * exponent + 1 and bits * exponent bits, so the
    // first bound refuses only results that are too large, and a result the second admits needs
    // at most twice the bound to compute before its exact length is checked.
    let bits = base.bits();
    let detail = format!("{base} ^Int {exponent} needs more than {MAX_INT_RESULT_BITS} bits");
    let too_large = || {
        Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::ResultTooLarge {
                detail: detail.clone(),
            },
        ))
    };
    if (bits - 1)
        .checked_mul(exponent)
        .and_then(|minimum| minimum.checked_add(1))
        .is_none_or(|minimum| minimum > MAX_INT_RESULT_BITS)
    {
        return too_large();
    }
    let mut result = BigInt::one();
    while exponent != 0 {
        crate::stop::check()?;
        if exponent & 1 == 1 {
            result *= &base;
        }
        exponent >>= 1;
        if exponent != 0 {
            base = &base * &base;
        }
    }
    if result.bits() > MAX_INT_RESULT_BITS {
        return too_large();
    }
    Ok(BuiltinResult::Value(int_term(result)))
}

fn int_powmod(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("INT.powmod", arguments, 3)?;
    let Some((base, exponent, modulus)) = read_int(&arguments[0])
        .zip(read_int(&arguments[1]))
        .zip(read_int(&arguments[2]))
        .map(|((base, exponent), modulus)| (base, exponent, modulus))
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if modulus.is_zero() {
        return Ok(BuiltinResult::Bottom);
    }
    let modulus = modulus.abs();
    let (base, exponent) = if exponent.sign() == Sign::Minus {
        let Some(inverse) = modular_inverse(&base, &modulus)? else {
            return Ok(BuiltinResult::Bottom);
        };
        (inverse, -exponent)
    } else {
        (base, exponent)
    };
    let mut base = euclidean_modulus(base, modulus.clone()).expect("non-zero modulus");
    let mut exponent = exponent;
    let mut result = BigInt::one();
    while !exponent.is_zero() {
        crate::stop::check()?;
        if (&exponent & BigInt::one()) == BigInt::one() {
            result = (result * &base) % &modulus;
        }
        exponent >>= 1;
        if !exponent.is_zero() {
            base = (&base * &base) % &modulus;
        }
    }
    Ok(BuiltinResult::Value(int_term(result % modulus)))
}

fn modular_inverse(value: &BigInt, modulus: &BigInt) -> HookResult<Option<BigInt>> {
    let (mut old_r, mut r) = (value.clone(), modulus.clone());
    let (mut old_s, mut s) = (BigInt::one(), BigInt::zero());
    while !r.is_zero() {
        crate::stop::check()?;
        let quotient = &old_r / &r;
        (old_r, r) = (r.clone(), old_r - &quotient * r);
        (old_s, s) = (s.clone(), old_s - quotient * s);
    }
    if old_r.abs() != BigInt::one() {
        return Ok(None);
    }
    if old_r.sign() == Sign::Minus {
        old_s = -old_s;
    }
    Ok(euclidean_modulus(old_s, modulus.clone()))
}

fn int_log2(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("INT.log2", arguments, 1)?;
    let Some(value) = read_int(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if value <= BigInt::zero() {
        return Ok(BuiltinResult::Bottom);
    }
    Ok(BuiltinResult::Value(int_term(BigInt::from(
        value.bits() - 1,
    ))))
}

fn int_shift(hook: &str, arguments: &[Term], right: bool) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 2)?;
    let Some((value, amount)) = read_int(&arguments[0]).zip(read_int(&arguments[1])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    // Shifting by a negative quantity is undefined (`#False` in `domains.md`) for both shifts.
    if amount.sign() == Sign::Minus {
        return Ok(BuiltinResult::Bottom);
    }
    let shifts_left = !right;
    let too_large = || {
        Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::ResultTooLarge {
                detail: format!("{value} {}Int {amount}", if right { ">>" } else { "<<" }),
            },
        ))
    };
    if shifts_left
        && !value.is_zero()
        && amount
            .to_u64()
            .and_then(|amount| amount.checked_add(value.bits()))
            .is_none_or(|bits| bits > MAX_INT_RESULT_BITS)
    {
        return too_large();
    }
    if let Some(magnitude) = amount.to_usize() {
        let result = if shifts_left {
            value << magnitude
        } else {
            value >> magnitude
        };
        return Ok(BuiltinResult::Value(int_term(result)));
    }
    if !shifts_left {
        return Ok(BuiltinResult::Value(int_term(
            if value.sign() == Sign::Minus {
                -BigInt::one()
            } else {
                BigInt::zero()
            },
        )));
    }
    if value.is_zero() {
        return Ok(BuiltinResult::Value(int_term(BigInt::zero())));
    }
    too_large()
}

fn kequal_ite(arguments: &[Term]) -> HookResult<Option<Term>> {
    expect_arity("KEQUAL.ite", arguments, 3)?;
    let [condition, then_value, else_value] = arguments else {
        unreachable!()
    };
    expect_sort("KEQUAL.ite", condition, &Sort::builtin(BuiltinSort::Bool))?;
    if then_value.sort() != else_value.sort() {
        return Err(BuiltinError::AlternativeSortsDiffer {
            then_sort: then_value.sort(),
            else_sort: else_value.sort(),
        }
        .into());
    }
    Ok(match read_bool(condition) {
        Some(true) => Some(then_value.clone()),
        Some(false) => Some(else_value.clone()),
        None => None,
    })
}

fn kequal(
    arguments: &[Term],
    negate: bool,
    sort_graph: Option<&SortGraph>,
) -> HookResult<Option<Term>> {
    expect_arity(if negate { "KEQUAL.ne" } else { "KEQUAL.eq" }, arguments, 2)?;
    if let (Some(left), Some(right)) = (
        k_sequence_injection(&arguments[0]),
        k_sequence_injection(&arguments[1]),
    ) {
        match match_injection_equality(sort_graph, left, right) {
            Some(
                InjectionEquality::Direct(left, right) | InjectionEquality::Split(left, right),
            ) => {
                return Ok(evaluate_equality(&left, &right, sort_graph)
                    .map(|equal| bool_term(equal != negate)));
            }
            Some(InjectionEquality::Distinct) => return Ok(Some(bool_term(negate))),
            Some(InjectionEquality::Unknown) | None => {}
        }
    }
    let Some(left) = k_sequence_item(&arguments[0]) else {
        return Ok(None);
    };
    let Some(right) = k_sequence_item(&arguments[1]) else {
        return Ok(None);
    };
    Ok(evaluate_equality(left, right, sort_graph).map(|equal| bool_term(equal != negate)))
}

/// R-val: strict hook operands, defined wherever the result exists, denote different
/// values when both are constructor-like and differ syntactically, or when they are apart.
pub(super) fn values_differ(sorts: Option<&SortGraph>, left: &Term, right: &Term) -> bool {
    (left.attributes().constructor_like && right.attributes().constructor_like && left != right)
        || crate::definedness::terms_apart(sorts, left, right).is_some()
}

/// Whether two operands of `KEQUAL` denote equal values, or `None` when that is not decided.
///
/// Two constructor-like terms (values built from free constructors, domain values, injections
/// and collections) are equal exactly when they are the same term. Apart operands differ
/// wherever the strict hook has a result. Otherwise each operand is classified as the value
/// it denotes, with no evidence for an equation head (`NoEvidence`), and
/// the roots decide only when one of them is a free-constructor application and the other is a
/// fixed root too: different roots are different values, and two applications of one
/// free symbol are equal exactly when their arguments are.
fn evaluate_equality(left: &Term, right: &Term, sort_graph: Option<&SortGraph>) -> Option<bool> {
    if left.attributes().constructor_like && right.attributes().constructor_like {
        return Some(left == right);
    }
    // Strict hook operands have values. Separate every pair the predicate layer separates,
    // so `a ==K b` is never less decided than `\equals(a, b)`.
    if crate::definedness::terms_apart(sort_graph, left, right).is_some() {
        return Some(false);
    }
    evaluate_equality_by_roots(left, right, sort_graph)
}

/// Compare operands after the shared apartness walk found no separation.
/// That walk already visits free-constructor argument pairs and equivalent injection
/// operands, so recursion through those pairs need not scan their subtrees again.
#[deny(clippy::wildcard_enum_match_arm)]
fn evaluate_equality_by_roots(
    left: &Term,
    right: &Term,
    sort_graph: Option<&SortGraph>,
) -> Option<bool> {
    if left.attributes().constructor_like && right.attributes().constructor_like {
        return Some(left == right);
    }
    let fixed = |term| match classify_value(term, &mut NoEvidence) {
        Head::Fixed(fixed) => Some(fixed),
        Head::Open(_) | Head::Residual => None,
    };
    if let (Some(left_root), Some(right_root)) = (fixed(left), fixed(right))
        && (left_root.root() == FixedRoot::FreeConstructor
            || right_root.root() == FixedRoot::FreeConstructor)
    {
        let arguments_equal = |pairs: &mut dyn Iterator<Item = (&Term, &Term)>| {
            let mut undecided = false;
            for (left, right) in pairs {
                match evaluate_equality_by_roots(left, right, sort_graph) {
                    Some(false) => return Some(false),
                    None => undecided = true,
                    Some(true) => {}
                }
            }
            (!undecided).then_some(true)
        };
        return match compare_roots(left_root, right_root) {
            RootComparison::Distinct(_) | RootComparison::ArityMismatch => Some(false),
            RootComparison::SameApplication(same) => arguments_equal(&mut same.pairs()),
            RootComparison::DomainValues
            | RootComparison::Injections
            | RootComparison::Collections(_) => {
                unreachable!("one of the two roots is a free-constructor application")
            }
        };
    }
    match (left.kind(), right.kind()) {
        (TermKind::Injection { .. }, TermKind::Injection { .. }) => {
            match match_injection_equality(sort_graph, left, right)? {
                InjectionEquality::Direct(left, right) | InjectionEquality::Split(left, right) => {
                    evaluate_equality_by_roots(&left, &right, sort_graph)
                }
                InjectionEquality::Distinct => Some(false),
                InjectionEquality::Unknown => None,
            }
        }
        (TermKind::DomainValue { .. }, TermKind::DomainValue { .. }) => Some(left == right),
        _ if left == right => Some(true),
        _ => None,
    }
}

pub(crate) fn k_sequence_item(term: &Term) -> Option<&Term> {
    let injection = k_sequence_injection(term)?;
    let TermKind::Injection { term: item, .. } = injection.kind() else {
        unreachable!("k_sequence_injection returns an injection")
    };
    Some(item)
}

fn k_sequence_injection(term: &Term) -> Option<&Term> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return None;
    };
    let [first, tail] = arguments.as_slice() else {
        return None;
    };
    let TermKind::Injection { .. } = first.kind() else {
        return None;
    };
    let TermKind::Application {
        symbol: tail_symbol,
        arguments: tail_arguments,
        ..
    } = tail.kind()
    else {
        return None;
    };
    (symbol.is(WellKnownSymbol::KSeq)
        && tail_symbol.is(WellKnownSymbol::DotK)
        && tail_arguments.is_empty())
    .then_some(first)
}

fn read_bool(term: &Term) -> Option<bool> {
    let TermKind::DomainValue { sort, value } = term.kind() else {
        return None;
    };
    if !sort.is_builtin(BuiltinSort::Bool) {
        return None;
    }
    match value.as_utf8().ok()? {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

pub(super) fn read_int(term: &Term) -> Option<BigInt> {
    let TermKind::DomainValue { sort, value } = term.kind() else {
        return None;
    };
    sort.is_builtin(BuiltinSort::Int)
        .then(|| value.as_utf8().ok()?.parse().ok())
        .flatten()
}

pub(super) fn bool_term(value: bool) -> Term {
    Term::domain_value(
        Sort::builtin(BuiltinSort::Bool),
        if value { "true" } else { "false" },
    )
}

pub(super) fn int_term(value: BigInt) -> Term {
    Term::domain_value(Sort::builtin(BuiltinSort::Int), value.to_string())
}

pub(super) fn expect_arity(hook: &str, arguments: &[Term], expected: usize) -> HookResult<()> {
    if arguments.len() == expected {
        Ok(())
    } else {
        Err(BuiltinError::WrongArity {
            hook: hook.into(),
            expected,
            actual: arguments.len(),
        }
        .into())
    }
}

pub(super) fn expect_sort(hook: &str, term: &Term, expected: &Sort) -> HookResult<()> {
    let actual = term.sort();
    if &actual == expected {
        Ok(())
    } else {
        Err(BuiltinError::UnexpectedSort {
            hook: hook.into(),
            expected: expected.clone(),
            actual,
        }
        .into())
    }
}

#[cfg(test)]
mod tests {
    use std::{sync::Arc, time::Duration};

    use super::*;
    use crate::{
        stop::{Stop, StopCause},
        term::{
            AlgebraicAxioms, CollectionSymbols, FunctionType, HeadRole, ListDefinition,
            MapDefinition, Symbol, SymbolAttributes, SymbolType, Variable,
        },
        timeout::{StepTimeoutController, StepTimeoutOptions},
    };

    fn hooked(hook: &str, result_sort: Sort, arguments: Vec<Term>) -> Term {
        let argument_sorts = arguments.iter().map(Term::sort).collect();
        Term::application(
            Arc::new(Symbol {
                name: format!("hook-{hook}").into(),
                sort_variables: Vec::new(),
                argument_sorts,
                result_sort,
                attributes: {
                    let mut attributes =
                        SymbolAttributes::constructor().with_declared_function(true);
                    attributes.symbol_type = SymbolType::Function(FunctionType::Total);
                    attributes.hook = Some(hook.into());
                    attributes
                },
            }),
            Vec::new(),
            arguments,
        )
    }

    fn k_sequence(item: Term) -> Term {
        let item_sort = item.sort();
        let k_item_sort = Sort::simple("SortKItem");
        let k_sort = Sort::simple("SortK");
        Term::application(
            Arc::new(Symbol::constructor(
                "kseq",
                vec![k_item_sort.clone(), k_sort.clone()],
                k_sort.clone(),
            )),
            Vec::new(),
            vec![
                Term::injection(item_sort, k_item_sort, item),
                Term::application(
                    Arc::new(Symbol::constructor("dotk", Vec::new(), k_sort)),
                    Vec::new(),
                    Vec::new(),
                ),
            ],
        )
    }

    #[test]
    fn fu17_equality_checks_every_constructor_argument() {
        let int = Sort::simple("SortInt");
        let p = Arc::new(Symbol::constructor(
            "p",
            vec![int.clone(), int.clone()],
            Sort::simple("SortPair"),
        ));
        let pair = |name, value| {
            Term::application(
                p.clone(),
                Vec::new(),
                vec![
                    Term::variable(Variable::new(name, int.clone())),
                    int_term(BigInt::from(value)),
                ],
            )
        };
        let left = pair("A", 1);
        assert_eq!(evaluate_equality(&left, &pair("B", 2), None), Some(false));
        assert_eq!(evaluate_equality(&left, &pair("B", 1), None), None);
        assert_eq!(evaluate_equality(&left, &left, None), Some(true));
        assert_eq!(evaluate_equality(&pair("B", 2), &left, None), Some(false));
    }

    /// Identifying axioms permit different roots or arguments to denote the same value.
    #[test]
    fn algebraic_equality_decides_only_syntactic_identity() {
        let sort = Sort::simple("SortElem");
        let constant = |name| {
            Term::application(
                Arc::new(Symbol::constructor(name, Vec::new(), sort.clone())),
                Vec::new(),
                Vec::new(),
            )
        };
        let a = constant("a");
        let b = constant("b");
        for axioms in [
            AlgebraicAxioms::assoc(),
            AlgebraicAxioms::comm(),
            AlgebraicAxioms::idem(),
            AlgebraicAxioms::unit(),
        ] {
            let mut g = Symbol::constructor("g", vec![sort.clone(); 2], sort.clone());
            g.attributes.symbol_type = SymbolType::Function(FunctionType::Total);
            g.attributes = g.attributes.with_algebraic_axioms(axioms);
            let g = Arc::new(g);
            let apply = |x, y| Term::application(g.clone(), Vec::new(), vec![x, y]);
            let ab = apply(a.clone(), b.clone());
            assert_eq!(evaluate_equality(&ab, &ab, None), Some(true));
            for (left, right) in [
                (
                    apply(a.clone(), ab.clone()),
                    apply(apply(a.clone(), a.clone()), b.clone()),
                ),
                (ab.clone(), apply(b.clone(), a.clone())),
                (apply(a.clone(), a.clone()), a.clone()),
            ] {
                assert_eq!(evaluate_equality(&left, &right, None), None);
                assert_eq!(evaluate_equality(&right, &left, None), None);
                assert!(!left.concrete_after_normalization());
            }
        }
    }

    #[test]
    fn fu17_equality_leaves_algebraic_argument_mismatches_undecided() {
        let sort = Sort::simple("SortElem");
        let c = Arc::new(Symbol::constructor(
            "c",
            vec![Sort::simple("SortInt")],
            sort.clone(),
        ));
        let constant =
            |value| Term::application(c.clone(), Vec::new(), vec![int_term(BigInt::from(value))]);
        for (axioms, associative) in [
            (AlgebraicAxioms::assoc(), true),
            (AlgebraicAxioms::idem(), false),
        ] {
            let mut g = Symbol::constructor("g", vec![sort.clone(), sort.clone()], sort.clone());
            g.attributes.symbol_type = SymbolType::Function(FunctionType::Total);
            g.attributes = g.attributes.with_algebraic_axioms(axioms);
            let g = Arc::new(g);
            let apply = |left, right| Term::application(g.clone(), Vec::new(), vec![left, right]);
            let x = Term::variable(Variable::new("X", sort.clone()));
            let y = Term::variable(Variable::new("Y", sort.clone()));
            let left = apply(constant(1), x);
            let right = apply(
                apply(constant(1), constant(if associative { 2 } else { 1 })),
                y,
            );
            // Associativity makes the sides equal at X = g(c(2), Y); idempotence
            // makes them equal at X = Y, since g(c(1), c(1)) = c(1).
            // Their differing first arguments therefore cannot refute equality.
            assert_eq!(evaluate_equality(&left, &right, None), None);
            assert_eq!(evaluate_equality(&right, &left, None), None);
            assert_eq!(evaluate_equality(&left, &left, None), Some(true));
        }
    }

    #[test]
    fn kequal_treats_signed_and_unsigned_int_literals_as_equal() {
        let int_sort = Sort::simple("SortInt");
        let arguments = [
            k_sequence(Term::domain_value(int_sort.clone(), "3")),
            k_sequence(Term::domain_value(int_sort, "+3")),
        ];

        assert_eq!(
            evaluate_hook("KEQUAL.eq", &arguments),
            Ok(Ok(BuiltinResult::Value(bool_term(true))))
        );
        assert_eq!(
            evaluate_hook("KEQUAL.ne", &arguments),
            Ok(Ok(BuiltinResult::Value(bool_term(false))))
        );
    }

    #[test]
    fn kequal_decides_distinct_sort_injections() {
        let arguments = [
            k_sequence(Term::variable(Variable::new("I", Sort::simple("SortInt")))),
            k_sequence(bool_term(true)),
        ];

        assert_eq!(
            evaluate_hook("KEQUAL.eq", &arguments),
            Ok(Ok(BuiltinResult::Value(bool_term(false))))
        );
        assert_eq!(
            evaluate_hook("KEQUAL.ne", &arguments),
            Ok(Ok(BuiltinResult::Value(bool_term(true))))
        );
    }

    #[test]
    fn boolean_hooks_short_circuit_unknown_arguments() {
        let unknown = Term::variable(Variable::new("B", Sort::simple("SortBool")));
        let false_and_unknown = hooked(
            "BOOL.and",
            Sort::simple("SortBool"),
            vec![bool_term(false), unknown.clone()],
        );
        let true_and_unknown = hooked(
            "BOOL.and",
            Sort::simple("SortBool"),
            vec![bool_term(true), unknown],
        );

        assert_eq!(
            evaluate(&false_and_unknown),
            Ok(Ok(BuiltinResult::Value(bool_term(false))))
        );
        assert_eq!(
            evaluate(&true_and_unknown),
            Ok(Ok(BuiltinResult::NotApplicable))
        );
    }

    #[test]
    fn integer_hooks_preserve_arbitrary_precision() {
        let left = BigInt::parse_bytes(b"99999999999999999999999999999999999999", 10).unwrap();
        let right = BigInt::from(2);
        let addition = hooked(
            "INT.add",
            Sort::simple("SortInt"),
            vec![int_term(left.clone()), int_term(right.clone())],
        );
        let comparison = hooked(
            "INT.gt",
            Sort::simple("SortBool"),
            vec![int_term(left.clone()), int_term(right)],
        );

        assert_eq!(
            evaluate(&addition),
            Ok(Ok(BuiltinResult::Value(int_term(left + 2))))
        );
        assert_eq!(
            evaluate(&comparison),
            Ok(Ok(BuiltinResult::Value(bool_term(true))))
        );
    }

    #[test]
    fn int_pow_handles_exponents_beyond_u32() {
        let beyond_u32 = BigInt::one() << 32;
        let enormous: BigInt = BigInt::one() << 40;

        assert_eq!(
            evaluate_hook("INT.pow", &[int_term(BigInt::one()), int_term(beyond_u32)]),
            Ok(Ok(BuiltinResult::Value(int_term(BigInt::one()))))
        );
        assert_eq!(
            evaluate_hook(
                "INT.pow",
                &[int_term(BigInt::zero()), int_term(enormous.clone())],
            ),
            Ok(Ok(BuiltinResult::Value(int_term(BigInt::zero()))))
        );
        assert_eq!(
            evaluate_hook(
                "INT.pow",
                &[
                    int_term(BigInt::from(-1)),
                    int_term(&enormous + BigInt::one()),
                ],
            ),
            Ok(Ok(BuiltinResult::Value(int_term(BigInt::from(-1)))))
        );
        assert!(matches!(
            evaluate_hook("INT.pow", &[int_term(BigInt::from(2)), int_term(enormous)]),
            Ok(Ok(BuiltinResult::Unsupported(
                UnsupportedHookReason::ResultTooLarge { .. }
            )))
        ));
        assert_eq!(
            evaluate_hook(
                "INT.pow",
                &[int_term(BigInt::from(2)), int_term(BigInt::from(-1))],
            ),
            Ok(Ok(BuiltinResult::Bottom))
        );
    }

    /// A left shift whose result would exceed the integer result bound is reported as too large
    /// rather than allocated; a zero value and results within the bound are still computed.
    #[test]
    fn int_shl_beyond_the_result_bound_is_unsupported() {
        let shl = |value: BigInt, amount: BigInt| {
            evaluate_hook("INT.shl", &[int_term(value), int_term(amount)])
        };
        for amount in [
            BigInt::one() << 32u32,
            (BigInt::one() << 32u32) + 1,
            BigInt::one() << 40u32,
        ] {
            assert!(
                matches!(
                    shl(BigInt::one(), amount.clone()),
                    Ok(Ok(BuiltinResult::Unsupported(
                        UnsupportedHookReason::ResultTooLarge { .. }
                    )))
                ),
                "1 <<Int {amount}"
            );
            assert_eq!(
                shl(BigInt::zero(), amount.clone()),
                Ok(Ok(BuiltinResult::Value(int_term(BigInt::zero())))),
                "0 <<Int {amount}"
            );
        }
        assert_eq!(
            shl(BigInt::from(3), BigInt::from(100)),
            Ok(Ok(BuiltinResult::Value(int_term(
                BigInt::from(3) << 100u32
            ))))
        );
    }

    /// `A ^%Int B C` is `(mod (^ A B) C)` (its `smt-hook`, through which the backend states such
    /// terms to the SMT solver): the Euclidean remainder, in [0, |C|) whatever the signs of the
    /// power and of C. Zero C is undefined.
    #[test]
    fn powmod_is_the_euclidean_remainder_of_the_power() {
        let powmod = |base: i64, exponent: i64, modulus: i64| {
            evaluate_hook(
                "INT.powmod",
                &[
                    int_term(BigInt::from(base)),
                    int_term(BigInt::from(exponent)),
                    int_term(BigInt::from(modulus)),
                ],
            )
        };
        for (base, exponent, modulus, expected) in [
            (-2, 3, 5, 2),
            (-2, 3, -5, 2),
            (2, 3, -5, 3),
            (-1, 1, 5, 4),
            (-3, 2, 5, 4),
        ] {
            assert_eq!(
                powmod(base, exponent, modulus),
                Ok(Ok(BuiltinResult::Value(int_term(BigInt::from(expected))))),
                "{base} ^%Int {exponent} {modulus}"
            );
        }
        assert_eq!(powmod(2, 3, 0), Ok(Ok(BuiltinResult::Bottom)));
    }

    /// A result of exactly 2^20 bits is computed and one more bit is reported as too large, for
    /// `^Int` and `<<Int` alike.
    #[test]
    fn int_results_are_computed_up_to_the_result_bound() {
        let bound = BigInt::from(1u32 << 20);
        let too_large = |result: Stoppable<Result<BuiltinResult, BuiltinError>>| {
            matches!(
                result,
                Ok(Ok(BuiltinResult::Unsupported(
                    UnsupportedHookReason::ResultTooLarge { .. }
                )))
            )
        };
        for amount in [&bound - 1u8, bound.clone()] {
            let shifted = evaluate_hook(
                "INT.shl",
                &[int_term(BigInt::one()), int_term(amount.clone())],
            );
            let powered = evaluate_hook(
                "INT.pow",
                &[int_term(BigInt::from(2)), int_term(amount.clone())],
            );
            if amount < bound {
                let expected = Ok(Ok(BuiltinResult::Value(int_term(
                    BigInt::one() << amount.to_usize().unwrap(),
                ))));
                assert_eq!(shifted, expected, "1 <<Int {amount}");
                assert_eq!(powered, expected, "2 ^Int {amount}");
            } else {
                assert!(too_large(shifted), "1 <<Int {amount}");
                assert!(too_large(powered), "2 ^Int {amount}");
            }
        }
    }

    /// `domains.md`: shifting by a negative quantity is `#False`, in either direction and
    /// whatever the shifted value; it is not a shift the other way.
    #[test]
    fn int_shift_by_a_negative_amount_is_undefined() {
        for hook in ["INT.shl", "INT.shr"] {
            for (value, amount) in [(8, -1), (0, -1), (-8, -2)] {
                assert_eq!(
                    evaluate_hook(
                        hook,
                        &[
                            int_term(BigInt::from(value)),
                            int_term(BigInt::from(amount))
                        ],
                    ),
                    Ok(Ok(BuiltinResult::Bottom)),
                    "{value} {hook} {amount}"
                );
            }
            assert_eq!(
                evaluate_hook(
                    hook,
                    &[int_term(BigInt::one()), int_term(-(BigInt::one() << 70u32))]
                ),
                Ok(Ok(BuiltinResult::Bottom)),
                "{hook} by -2^70"
            );
        }
    }

    #[test]
    fn int_shift_beyond_usize_is_computed_or_unsupported() {
        let beyond_usize = BigInt::one() << usize::BITS;

        assert_eq!(
            evaluate_hook(
                "INT.shr",
                &[int_term(BigInt::from(8)), int_term(beyond_usize.clone())],
            ),
            Ok(Ok(BuiltinResult::Value(int_term(BigInt::zero()))))
        );
        assert_eq!(
            evaluate_hook(
                "INT.shr",
                &[int_term(BigInt::from(-8)), int_term(beyond_usize.clone()),],
            ),
            Ok(Ok(BuiltinResult::Value(int_term(BigInt::from(-1)))))
        );
        assert_eq!(
            evaluate_hook(
                "INT.shl",
                &[int_term(BigInt::zero()), int_term(beyond_usize.clone())],
            ),
            Ok(Ok(BuiltinResult::Value(int_term(BigInt::zero()))))
        );
        assert!(matches!(
            evaluate_hook(
                "INT.shl",
                &[int_term(BigInt::one()), int_term(beyond_usize)],
            ),
            Ok(Ok(BuiltinResult::Unsupported(
                UnsupportedHookReason::ResultTooLarge { .. }
            )))
        ));
    }

    #[test]
    fn int_equality_is_reflexive_on_function_patterns() {
        let argument = hooked(
            "TEST.function",
            Sort::simple("SortInt"),
            vec![Term::variable(Variable::new("X", Sort::simple("SortInt")))],
        );

        assert_eq!(
            evaluate_hook("INT.eq", &[argument.clone(), argument.clone()]),
            Ok(Ok(BuiltinResult::Value(bool_term(true))))
        );
        assert_eq!(
            evaluate_hook("INT.ne", &[argument.clone(), argument]),
            Ok(Ok(BuiltinResult::Value(bool_term(false))))
        );
    }

    #[test]
    fn kequal_decides_distinct_constructor_like_collections() {
        let symbols = CollectionSymbols {
            unit: "unit".into(),
            element: "element".into(),
            concat: "concat".into(),
        };
        let map_definition = Arc::new(MapDefinition {
            symbols: symbols.clone(),
            key_sort: "SortInt".into(),
            value_sort: "SortInt".into(),
            map_sort: "SortMap".into(),
        });
        let list_definition = Arc::new(ListDefinition {
            symbols,
            element_sort: "SortInt".into(),
            list_sort: "SortList".into(),
        });
        let left_map = Term::map(
            map_definition.clone(),
            vec![(int_term(BigInt::one()), int_term(BigInt::from(2)))],
            None,
        );
        let right_map = Term::map(
            map_definition,
            vec![(int_term(BigInt::one()), int_term(BigInt::from(3)))],
            None,
        );
        let left_list = Term::list(list_definition.clone(), vec![int_term(BigInt::one())], None);
        let right_list = Term::list(list_definition, vec![int_term(BigInt::from(2))], None);

        assert_eq!(evaluate_equality(&left_map, &right_map, None), Some(false));
        assert_eq!(
            evaluate_equality(&left_list, &right_list, None),
            Some(false)
        );
        assert_eq!(evaluate_equality(&left_map, &left_map, None), Some(true));
    }

    #[test]
    fn string_to_token_uses_the_application_result_sort() {
        let token_sort = Sort::simple("SortIdentifier");
        let application = hooked(
            "STRING.string2token",
            token_sort.clone(),
            vec![Term::domain_value(Sort::simple("SortString"), "alpha")],
        );

        assert_eq!(
            evaluate(&application),
            Ok(Ok(BuiltinResult::Value(Term::domain_value(
                token_sort, "alpha"
            ))))
        );
    }

    fn evaluate_int(
        hook: &str,
        arguments: &[i64],
    ) -> Stoppable<Result<BuiltinResult, BuiltinError>> {
        evaluate_hook(
            hook,
            &arguments
                .iter()
                .copied()
                .map(BigInt::from)
                .map(int_term)
                .collect::<Vec<_>>(),
        )
    }

    fn float_term(value: &str) -> Term {
        Term::domain_value(Sort::simple("SortFloat"), value)
    }

    #[test]
    fn float_representation_hooks_use_canonical_k_tokens() {
        let cases = [
            (
                "FLOAT.precision",
                vec![float_term("0.1f")],
                BuiltinResult::Value(int_term(BigInt::from(24))),
            ),
            (
                "FLOAT.exponentBits",
                vec![float_term("0.1p53x11")],
                BuiltinResult::Value(int_term(BigInt::from(11))),
            ),
            (
                "FLOAT.sign",
                vec![float_term("-0.0p24x8")],
                BuiltinResult::Value(bool_term(true)),
            ),
            (
                "FLOAT.isNaN",
                vec![float_term("NaNp53x11")],
                BuiltinResult::Value(bool_term(true)),
            ),
            (
                "FLOAT.neg",
                vec![float_term("0.1")],
                BuiltinResult::Value(float_term("-1.0000000000000001e-01p53x11")),
            ),
            (
                "FLOAT.neg",
                vec![float_term("0.1f")],
                BuiltinResult::Value(float_term("-1.00000001e-01p24x8")),
            ),
            (
                "FLOAT.neg",
                vec![float_term("0.0f")],
                BuiltinResult::Value(float_term("-0e+00p24x8")),
            ),
            (
                "FLOAT.neg",
                vec![float_term("-Infinity")],
                BuiltinResult::Value(float_term("Infinityp53x11")),
            ),
        ];

        for (hook, arguments, expected) in cases {
            assert_eq!(evaluate_hook(hook, &arguments), Ok(Ok(expected)), "{hook}");
        }
    }

    #[test]
    fn float_tokens_reject_unsupported_or_malformed_ground_formats() {
        assert_eq!(
            evaluate_hook("FLOAT.precision", &[float_term("1.0p2x8")]),
            Ok(Err(BuiltinError::UnsupportedFloatFormat {
                hook: "FLOAT.precision".into(),
                precision: 2,
                exponent_bits: 8,
            }))
        );
        // A Float domain value names an element in FLOAT-SYNTAX only; spellings that general
        // float parsers also read name none.
        for token in [
            "not-a-float",
            "inf",
            "inff",
            "-infinity",
            "nan",
            "-NaN",
            "-.5",
            " 1.0",
            "1.0 ",
            "1e",
            "0x1p3",
        ] {
            assert_eq!(
                evaluate_hook("FLOAT.sign", &[float_term(token)]),
                Ok(Err(BuiltinError::InvalidFloatToken {
                    hook: "FLOAT.sign".into(),
                    token: token.into(),
                })),
                "{token:?}"
            );
        }
        for (token, negative) in [
            ("+Infinity", false),
            ("-Infinityf", true),
            ("-0.5e-3d", true),
            (".5p24x8", false),
            ("7.", false),
        ] {
            assert_eq!(
                evaluate_hook("FLOAT.sign", &[float_term(token)]),
                Ok(Ok(BuiltinResult::Value(bool_term(negative)))),
                "{token:?}"
            );
        }

        let symbolic = Term::variable(Variable::new("F", Sort::simple("SortFloat")));
        assert_eq!(
            evaluate_hook("FLOAT.sign", &[symbolic]),
            Ok(Ok(BuiltinResult::NotApplicable))
        );
    }

    #[test]
    fn float_unary_hooks_cover_ieee_special_values() {
        let cases = [
            ("FLOAT.abs", "-Infinityf", float_term("Infinityp24x8")),
            ("FLOAT.abs", "-0.0", float_term("0e+00p53x11")),
            ("FLOAT.floor", "1.75f", float_term("1.00000000e+00p24x8")),
            (
                "FLOAT.ceil",
                "-1.25",
                float_term("-1.0000000000000000e+00p53x11"),
            ),
            ("FLOAT.trunc", "-1.75f", float_term("-1.00000000e+00p24x8")),
            (
                "FLOAT.trunc",
                "-1.40129846e-45p24x8",
                float_term("-0e+00p24x8"),
            ),
            ("FLOAT.floor", "NaN", float_term("NaNp53x11")),
        ];

        for (hook, argument, expected) in cases {
            assert_eq!(
                evaluate_hook(hook, &[float_term(argument)]),
                Ok(Ok(BuiltinResult::Value(expected))),
                "{hook}({argument})"
            );
        }
    }

    #[test]
    fn float_arithmetic_hooks_match_native_ieee_results() {
        let cases = [
            ("FLOAT.add", "1.5f", "2.25f", "3.75000000e+00p24x8"),
            ("FLOAT.sub", "1.5f", "2.25f", "-7.50000000e-01p24x8"),
            ("FLOAT.mul", "1.5f", "2.25f", "3.37500000e+00p24x8"),
            ("FLOAT.div", "1.5f", "2.0f", "7.50000000e-01p24x8"),
            ("FLOAT.add", "0.1", "0.2", "3.0000000000000004e-01p53x11"),
            (
                "FLOAT.add",
                "1.40129846e-45p24x8",
                "0.0f",
                "1.40129846e-45p24x8",
            ),
            ("FLOAT.div", "1.0", "0.0", "Infinityp53x11"),
            ("FLOAT.div", "0.0", "0.0", "NaNp53x11"),
            ("FLOAT.mul", "Infinityf", "0.0f", "NaNp24x8"),
        ];

        for (hook, left, right, expected) in cases {
            assert_eq!(
                evaluate_hook(hook, &[float_term(left), float_term(right)]),
                Ok(Ok(BuiltinResult::Value(float_term(expected)))),
                "{hook}({left}, {right})"
            );
        }
    }

    /// `rootFloat(F, 2)` is the root of degree 2, IEEE 754 rootn(F, 2): the square root, except
    /// that the even root of -0 is +0 (and so is `sqrtFloat(-0.0)`, the K rule
    /// `rootFloat(F, 2)`). Other degrees are not implemented.
    #[test]
    fn float_root_of_degree_two_is_the_ieee_even_root() {
        let cases = [
            ("4.0f", "2.00000000e+00p24x8"),
            ("2.0", "1.4142135623730951e+00p53x11"),
            ("-4.0f", "NaNp24x8"),
            ("NaN", "NaNp53x11"),
            ("Infinityf", "Infinityp24x8"),
            ("-Infinity", "NaNp53x11"),
            ("0.0", "0e+00p53x11"),
            ("-0.0f", "0e+00p24x8"),
            ("-0.0", "0e+00p53x11"),
        ];
        for (value, expected) in cases {
            assert_eq!(
                evaluate_hook(
                    "FLOAT.root",
                    &[float_term(value), int_term(BigInt::from(2))],
                ),
                Ok(Ok(BuiltinResult::Value(float_term(expected)))),
                "root({value}, 2)"
            );
        }

        assert_eq!(
            evaluate_hook(
                "FLOAT.root",
                &[float_term("8.0f"), int_term(BigInt::from(3))],
            ),
            Ok(Ok(BuiltinResult::Unsupported(
                UnsupportedHookReason::ArgumentOutOfRange {
                    detail: "root degree 3 (only 2 is implemented)".into(),
                }
            )))
        );
    }

    #[test]
    fn float_min_max_and_comparisons_follow_k_ieee_contracts() {
        let float_cases = [
            ("FLOAT.min", "NaNf", "2.0f", "2.00000000e+00p24x8"),
            ("FLOAT.max", "2.0", "NaN", "2.0000000000000000e+00p53x11"),
            ("FLOAT.min", "-0.0f", "0.0f", "-0e+00p24x8"),
            ("FLOAT.max", "-0.0", "0.0", "0e+00p53x11"),
        ];
        for (hook, left, right, expected) in float_cases {
            assert_eq!(
                evaluate_hook(hook, &[float_term(left), float_term(right)]),
                Ok(Ok(BuiltinResult::Value(float_term(expected)))),
                "{hook}({left}, {right})"
            );
        }

        let bool_cases = [
            ("FLOAT.lt", "1.0f", "2.0", true),
            ("FLOAT.le", "2.0f", "2.0", true),
            ("FLOAT.gt", "2.0f", "1.0", true),
            ("FLOAT.ge", "2.0f", "2.0", true),
            ("FLOAT.eq", "-0.0f", "0.0", true),
        ];
        for (hook, left, right, expected) in bool_cases {
            assert_eq!(
                evaluate_hook(hook, &[float_term(left), float_term(right)]),
                Ok(Ok(BuiltinResult::Value(bool_term(expected)))),
                "{hook}({left}, {right})"
            );
        }
        for hook in ["FLOAT.lt", "FLOAT.le", "FLOAT.gt", "FLOAT.ge", "FLOAT.eq"] {
            assert_eq!(
                evaluate_hook(hook, &[float_term("NaNf"), float_term("1.0")]),
                Ok(Ok(BuiltinResult::Value(bool_term(false)))),
                "{hook}(NaN, 1)"
            );
        }
    }

    #[test]
    fn float_arithmetic_rejects_mixed_formats() {
        assert_eq!(
            evaluate_hook("FLOAT.add", &[float_term("1.0f"), float_term("1.0")]),
            Ok(Err(BuiltinError::MismatchedFloatFormats {
                hook: "FLOAT.add".into(),
                left_precision: 24,
                left_exponent_bits: 8,
                right_precision: 53,
                right_exponent_bits: 11,
            }))
        );
    }

    #[test]
    fn float_round_uses_ieee_ties_to_even_and_target_format() {
        let cases = [
            (
                "1.000000059604644775390625p53x11",
                24,
                8,
                "1.00000000e+00p24x8",
            ),
            (
                "1.000000178813934326171875p53x11",
                24,
                8,
                "1.00000024e+00p24x8",
            ),
            ("0.1f", 53, 11, "1.0000000149011612e-01p53x11"),
            ("-0.0", 24, 8, "-0e+00p24x8"),
            ("Infinity", 24, 8, "Infinityp24x8"),
            ("NaN", 24, 8, "NaNp24x8"),
        ];
        for (value, precision, exponent_bits, expected) in cases {
            assert_eq!(
                evaluate_hook(
                    "FLOAT.round",
                    &[
                        float_term(value),
                        int_term(BigInt::from(precision)),
                        int_term(BigInt::from(exponent_bits)),
                    ],
                ),
                Ok(Ok(BuiltinResult::Value(float_term(expected)))),
                "round({value}, {precision}, {exponent_bits})"
            );
        }
        assert_eq!(
            evaluate_hook(
                "FLOAT.round",
                &[
                    float_term("1.0"),
                    int_term(BigInt::from(2)),
                    int_term(BigInt::from(8)),
                ],
            ),
            Ok(Err(BuiltinError::UnsupportedFloatFormat {
                hook: "FLOAT.round".into(),
                precision: 2,
                exponent_bits: 8,
            }))
        );
    }

    #[test]
    fn float_integer_conversions_are_arbitrary_precision_and_ties_to_even() {
        let int_to_float_cases = [
            (
                BigInt::from(16_777_217_u64),
                24,
                8,
                "1.67772160e+07p24x8",
            ),
            (
                BigInt::from(9_007_199_254_740_993_u64),
                53,
                11,
                "9.0071992547409920e+15p53x11",
            ),
            (
                BigInt::parse_bytes(
                    b"10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
                    10,
                )
                .unwrap(),
                53,
                11,
                "Infinityp53x11",
            ),
        ];
        for (integer, precision, exponent_bits, expected) in int_to_float_cases {
            assert_eq!(
                evaluate_hook(
                    "FLOAT.int2float",
                    &[
                        int_term(integer),
                        int_term(BigInt::from(precision)),
                        int_term(BigInt::from(exponent_bits)),
                    ],
                ),
                Ok(Ok(BuiltinResult::Value(float_term(expected)))),
                "int2float(_, {precision}, {exponent_bits})"
            );
        }

        let float_to_int_cases = [
            ("10.5", 10),
            ("11.5", 12),
            ("-10.5f", -10),
            ("1.40129846e-45p24x8", 0),
        ];
        for (value, expected) in float_to_int_cases {
            assert_eq!(
                evaluate_hook("FLOAT.float2int", &[float_term(value)]),
                Ok(Ok(BuiltinResult::Value(int_term(BigInt::from(expected))))),
                "float2int({value})"
            );
        }
        // `Float2Int` is total, and NaN and the infinities have no nearest integer: the value
        // there is not given by the definition.
        for value in ["Infinity", "-Infinityf", "NaNf", "NaN"] {
            assert!(
                matches!(
                    evaluate_hook("FLOAT.float2int", &[float_term(value)]),
                    Ok(Ok(BuiltinResult::Unsupported(
                        UnsupportedHookReason::Unspecified { .. }
                    )))
                ),
                "float2int({value})"
            );
        }
    }

    #[test]
    fn float_max_value_matches_ieee_format_limits() {
        let cases = [
            (24, 8, "3.40282347e+38p24x8"),
            (53, 11, "1.7976931348623157e+308p53x11"),
        ];
        for (precision, exponent_bits, expected) in cases {
            assert_eq!(
                evaluate_hook(
                    "FLOAT.maxValue",
                    &[
                        int_term(BigInt::from(precision)),
                        int_term(BigInt::from(exponent_bits)),
                    ],
                ),
                Ok(Ok(BuiltinResult::Value(float_term(expected)))),
                "maxValue({precision}, {exponent_bits})"
            );
        }
    }

    #[test]
    fn integer_fallback_hooks_match_kore_arithmetic() {
        let cases = [
            ("INT.tdiv", &[-5, -3][..], 1),
            ("INT.tmod", &[-5, -3][..], -2),
            ("INT.ediv", &[-5, -3][..], 2),
            ("INT.emod", &[-5, -3][..], 1),
            ("INT.pow", &[2, 10][..], 1_024),
            ("INT.powmod", &[3, -1, 7][..], 5),
            ("INT.log2", &[1_024][..], 10),
            ("INT.and", &[6, 3][..], 2),
            ("INT.or", &[4, 3][..], 7),
            ("INT.xor", &[6, 3][..], 5),
            ("INT.shl", &[3, 4][..], 48),
            ("INT.shr", &[-16, 2][..], -4),
            ("INT.min", &[-2, 3][..], -2),
            ("INT.max", &[-2, 3][..], 3),
        ];
        for (hook, arguments, expected) in cases {
            assert_eq!(
                evaluate_int(hook, arguments),
                Ok(Ok(BuiltinResult::Value(int_term(BigInt::from(expected))))),
                "{hook}"
            );
        }
        assert_eq!(
            evaluate_int("INT.not", &[0]),
            Ok(Ok(BuiltinResult::Value(int_term(BigInt::from(-1)))))
        );
    }

    #[test]
    fn undefined_integer_operations_are_bottom() {
        assert_eq!(
            evaluate_int("INT.ediv", &[1, 0]),
            Ok(Ok(BuiltinResult::Bottom))
        );
        assert_eq!(
            evaluate_int("INT.pow", &[2, -1]),
            Ok(Ok(BuiltinResult::Bottom))
        );
        assert_eq!(
            evaluate_int("INT.log2", &[0]),
            Ok(Ok(BuiltinResult::Bottom))
        );
        assert_eq!(
            evaluate_int("INT.powmod", &[2, -1, 4]),
            Ok(Ok(BuiltinResult::Bottom))
        );
    }

    #[test]
    fn native_hooks_observe_the_active_step_deadline() {
        let controller = StepTimeoutController::new(StepTimeoutOptions {
            manual: Some(Duration::ZERO),
            moving_average: false,
        });
        let _timer = controller.begin_step();

        assert!(matches!(
            evaluate_hook("INT.pow", &[int_term(2.into()), int_term(10.into())])
                .map_err(Stop::into_cause),
            Err(StopCause::Deadline(..))
        ));
    }

    #[test]
    fn reports_wrong_builtin_arity() {
        let term = hooked(
            "INT.add",
            Sort::simple("SortInt"),
            vec![int_term(BigInt::from(1))],
        );

        assert_eq!(
            evaluate(&term),
            Ok(Err(BuiltinError::WrongArity {
                hook: "INT.add".into(),
                expected: 2,
                actual: 1,
            }))
        );
    }

    #[test]
    fn krypto_wrong_arity_is_an_error_not_a_fallthrough() {
        let dummy = Term::domain_value(Sort::simple("SortBytes"), "");
        let cases = [
            ("KRYPTO.keccak256", 1),
            ("HASH.keccak256", 1),
            ("KRYPTO.keccak256raw", 1),
            ("KRYPTO.sha256", 1),
            ("HASH.sha256", 1),
            ("KRYPTO.sha3256", 1),
            ("HASH.sha3_256", 1),
            ("KRYPTO.sha512_256raw", 1),
            ("KRYPTO.ripemd160", 1),
            ("HASH.ripemd160", 1),
            ("KRYPTO.ecdsaPubKey", 1),
            ("KRYPTO.ecdsaRecover", 4),
            ("SECP256K1.ecdsaRecover", 4),
        ];

        for (hook, expected) in cases {
            let arguments = vec![dummy.clone(); expected + 1];
            assert_eq!(
                evaluate_hook(hook, &arguments),
                Ok(Err(BuiltinError::WrongArity {
                    hook: hook.into(),
                    expected,
                    actual: expected + 1,
                })),
                "{hook}"
            );
        }
    }

    #[test]
    fn raw_hash_hooks_are_evaluated_through_the_public_dispatcher() {
        let empty = bytes::bytes_term(&[]);

        for hook in ["KRYPTO.sha256raw", "KRYPTO.ripemd160raw"] {
            assert!(
                matches!(
                    evaluate_hook(hook, std::slice::from_ref(&empty)),
                    Ok(Ok(BuiltinResult::Value(_)))
                ),
                "{hook}"
            );
        }
    }

    #[test]
    fn bn128_validity_hooks_are_registered_with_the_public_evaluator() {
        let dummy = Term::domain_value(Sort::simple("SortCapabilityAuditDummy"), "dummy");

        for hook in ["KRYPTO.bn128valid", "KRYPTO.bn128g2valid"] {
            assert_eq!(
                evaluate_hook(hook, &[dummy.clone(), dummy.clone()]),
                Ok(Err(BuiltinError::WrongArity {
                    hook: hook.into(),
                    expected: 1,
                    actual: 2,
                })),
                "{hook}"
            );
        }
    }

    #[test]
    fn bn128_arithmetic_hooks_are_registered_with_the_public_evaluator() {
        let dummy = Term::domain_value(Sort::simple("SortCapabilityAuditDummy"), "dummy");

        for hook in ["KRYPTO.bn128add", "KRYPTO.bn128mul"] {
            let arguments = vec![dummy.clone(); 3];
            assert_eq!(
                evaluate_hook(hook, &arguments),
                Ok(Err(BuiltinError::WrongArity {
                    hook: hook.into(),
                    expected: 2,
                    actual: 3,
                })),
                "{hook}"
            );
        }
    }

    #[test]
    fn bn128_pairing_hook_is_registered_with_the_public_evaluator() {
        let dummy = Term::domain_value(Sort::simple("SortCapabilityAuditDummy"), "dummy");
        let arguments = vec![dummy; 3];

        assert_eq!(
            evaluate_hook("KRYPTO.bn128ate", &arguments),
            Ok(Err(BuiltinError::WrongArity {
                hook: "KRYPTO.bn128ate".into(),
                expected: 2,
                actual: 3,
            }))
        );
    }

    /// Equality expectations from declared roles, extended by R-val for certified roots.
    /// Independent of the classifier and apartness implementation.
    fn role_equality(left: &Term, right: &Term) -> Option<bool> {
        let free = |symbol: &Symbol| symbol.attributes.head_role() == HeadRole::FreeConstructor;
        let certified = |term: &Term| {
            matches!(term.kind(), TermKind::Application { symbol, .. }
                if symbol.attributes.head_role() == HeadRole::EquationHead
                    && term.attributes().evaluated)
        };
        let rigid_non_application = |kind: &TermKind| {
            matches!(
                kind,
                TermKind::DomainValue { .. }
                    | TermKind::Injection { .. }
                    | TermKind::Map { .. }
                    | TermKind::List { .. }
                    | TermKind::Set { .. }
            )
        };
        if left.attributes().constructor_like && right.attributes().constructor_like {
            return Some(left == right);
        }
        match (left.kind(), right.kind()) {
            (
                TermKind::Application {
                    symbol: left_symbol,
                    sort_arguments: left_sorts,
                    ..
                },
                TermKind::Application {
                    symbol: right_symbol,
                    sort_arguments: right_sorts,
                    ..
                },
            ) if ((free(left_symbol) && certified(right))
                || (certified(left) && free(right_symbol)))
                && (left_symbol.name != right_symbol.name || left_sorts != right_sorts) =>
            {
                // R-val: a free constructor and a certified equation head with different
                // roots are apart, so strict hook operands denote different values.
                Some(false)
            }
            (TermKind::Application { .. }, TermKind::Injection { .. }) if certified(left) => {
                Some(false)
            }
            (TermKind::Injection { .. }, TermKind::Application { .. }) if certified(right) => {
                Some(false)
            }
            (
                TermKind::Application {
                    symbol: left_symbol,
                    sort_arguments: left_sorts,
                    arguments: left_arguments,
                },
                TermKind::Application {
                    symbol: right_symbol,
                    sort_arguments: right_sorts,
                    arguments: right_arguments,
                },
            ) if free(left_symbol) && free(right_symbol) => {
                if left_symbol != right_symbol
                    || left_sorts != right_sorts
                    || left_arguments.len() != right_arguments.len()
                {
                    return Some(false);
                }
                let mut equal = true;
                for (left, right) in left_arguments.iter().zip(right_arguments) {
                    equal &= role_equality(left, right)?;
                }
                Some(equal)
            }
            (TermKind::Application { symbol, .. }, right)
                if free(symbol) && rigid_non_application(right) =>
            {
                Some(false)
            }
            (left, TermKind::Application { symbol, .. })
                if free(symbol) && rigid_non_application(left) =>
            {
                Some(false)
            }
            (TermKind::Injection { .. }, TermKind::Injection { .. }) => {
                match match_injection_equality(None, left, right)? {
                    InjectionEquality::Direct(left, right)
                    | InjectionEquality::Split(left, right) => role_equality(&left, &right),
                    InjectionEquality::Distinct => Some(false),
                    InjectionEquality::Unknown => None,
                }
            }
            (TermKind::DomainValue { .. }, TermKind::DomainValue { .. }) => Some(left == right),
            _ if left == right => Some(true),
            _ => None,
        }
    }

    /// Builtin equality preserves the role decisions and separates certified roots under R-val, on
    /// every ordered pair of a set of terms covering each root kind: domain values, free
    /// constructors over values and over function applications (which bypass the
    /// constructor-like shortcut), applications of one symbol with different arities, an
    /// algebraic application, equation heads with and without the certificate, injections,
    /// a list, a function application, a macro, and those
    /// terms under one free constructor.
    #[test]
    fn equality_decides_the_pairs_it_decided_by_symbol_role() {
        let sort = Sort::simple("SortS");
        let symbol = |name: &str, arity: usize, build: &dyn Fn(&mut SymbolAttributes)| {
            let mut symbol = Symbol::constructor(name, vec![sort.clone(); arity], sort.clone());
            build(&mut symbol.attributes);
            Arc::new(symbol)
        };
        let apply = |symbol: &Arc<Symbol>, arguments: Vec<Term>| {
            Term::application(symbol.clone(), Vec::new(), arguments)
        };
        let c = symbol("c", 1, &|_| {});
        let d = symbol("d", 1, &|_| {});
        let k = symbol("k", 1, &|_| {});
        let assoc = symbol("g", 2, &|attributes| {
            attributes.symbol_type = SymbolType::Function(FunctionType::Total);
            *attributes = attributes
                .clone()
                .with_algebraic_axioms(AlgebraicAxioms::assoc());
        });
        let wrap = symbol("wrap", 1, &|attributes| {
            *attributes = attributes.clone().with_anywhere(true);
        });
        let function = symbol("f", 1, &|attributes| {
            attributes.symbol_type = SymbolType::Function(FunctionType::Total);
        });
        let residual = symbol("m", 1, &|attributes| attributes.macro_or_alias = true);
        let one = Term::domain_value(sort.clone(), "1");
        let two = Term::domain_value(sort.clone(), "2");
        let f_one = apply(&function, vec![one.clone()]);
        let f_two = apply(&function, vec![two.clone()]);
        let sub = Sort::simple("SortSub");
        let list = Term::list(
            Arc::new(ListDefinition {
                symbols: CollectionSymbols {
                    unit: "unit".into(),
                    element: "element".into(),
                    concat: "concat".into(),
                },
                element_sort: "SortS".into(),
                list_sort: "SortList".into(),
            }),
            vec![f_one.clone()],
            None,
        );
        let c_one = apply(&c, vec![one.clone()]);
        let wrap_one = apply(&wrap, vec![one.clone()]);
        let certified_wrap_one = wrap_one.with_evaluated_mark_for_test();
        // `c` and certified `wrap` have different fixed roots: they are apart, so the
        // defined operands of the strict equality hook differ. Without the certificate,
        // `wrap` may reduce to a value rooted at `c`, and the comparison stays undecided.
        assert_eq!(
            evaluate_equality(&c_one, &certified_wrap_one, None),
            Some(false)
        );
        assert_eq!(
            evaluate_equality(&certified_wrap_one, &c_one, None),
            Some(false)
        );
        assert_eq!(evaluate_equality(&c_one, &wrap_one, None), None);
        assert_eq!(evaluate_equality(&wrap_one, &c_one, None), None);
        let base = vec![
            one.clone(),
            two.clone(),
            c_one,
            apply(&c, vec![f_one.clone()]),
            apply(&c, vec![f_two.clone()]),
            apply(&d, vec![f_one.clone()]),
            apply(&k, vec![f_one.clone()]),
            apply(&k, vec![f_one.clone(), f_two.clone()]),
            apply(&assoc, vec![f_one.clone(), one.clone()]),
            apply(&assoc, vec![f_one.clone(), two.clone()]),
            wrap_one,
            certified_wrap_one,
            Term::injection(sub.clone(), sort.clone(), f_one.clone()),
            Term::injection(sub.clone(), sort.clone(), two.clone()),
            Term::injection(Sort::simple("SortOther"), sort.clone(), f_two.clone()),
            list,
            f_one.clone(),
            apply(&residual, vec![f_one.clone()]),
        ];
        let terms = base
            .iter()
            .cloned()
            .chain(base.iter().map(|term| apply(&c, vec![term.clone()])))
            .collect::<Vec<_>>();
        let mut answers = [0_usize; 3];
        for left in &terms {
            for right in &terms {
                let expected = role_equality(left, right);
                assert_eq!(
                    evaluate_equality(left, right, None),
                    expected,
                    "{left:?} against {right:?}"
                );
                answers[match expected {
                    Some(true) => 0,
                    Some(false) => 1,
                    None => 2,
                }] += 1;
            }
        }
        assert!(answers.iter().all(|&count| count > 0), "{answers:?}");
    }
}
