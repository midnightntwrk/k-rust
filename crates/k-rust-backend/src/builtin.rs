//! In-process evaluation of the backend hooks: dispatch by `HookName` to the
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
mod hook_signature;
mod krypto;
mod list;
mod map;
mod mint;
mod result_collection;
mod set;
mod string;
mod substitution;

pub(crate) use hook_signature::LoadedSorts;
pub use hook_signature::{CollectionShape, SortFacts, misfit as collection_hook_misfit};
pub(crate) use result_collection::ResultCollection;
pub(crate) use substitution::KVarSorts;

use k_rust_kore::names::{BuiltinSort, WellKnownSymbol};

use crate::{
    allowance::Allowance,
    definition::BackendDefinition,
    matching::{InjectionEquality, SortGraph, match_injection_equality},
    stop::{Layered, Stoppable, Unwind},
    term::{
        Sort, Term, TermKind,
        head::{Fixed, FixedRoot, Head, NoEvidence, RootComparison, classify_value, compare_roots},
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
    /// [`MAX_INT_RESULT_BITS`]), that the backend does not compute. Term simplification leaves
    /// it unevaluated, a term that denotes that value, without an unsupported-hook error on
    /// constructor-like arguments, so that a subterm whose value is never used fails nothing. A
    /// run never decides a condition over one and never ends stuck or final on one: the step or
    /// search match that would is the unsupported-hook error
    /// (`simplify::refuse_uncomputed_applications`).
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
    /// arguments, since there is no value for an implementation to compute. The verdict reads
    /// the hook's documentation only: the symbol's function equations, axioms of the definition
    /// being run, still give the application the value they state. An equation whose evaluation
    /// still needs the value of the same application, or of one whose evaluation encloses it,
    /// gives none and is undone, and the application stays unevaluated only if none of its
    /// equations gives one (`simplify::UnspecifiedFrame`).
    ///
    /// Outside an execution it is also the outcome of a hook whose value on these arguments is
    /// one of several the definition admits, such as `keys_list` of a map of two or more keys,
    /// whose order domains.md does not fix: an execution takes k-rust's documented value, and
    /// every other evaluation leaves the application unevaluated, with `defined` set
    /// (`crate::evaluation`).
    Unspecified {
        detail: String,
        /// The value exists and is one of several the definition admits: the application is
        /// defined, so its `\ceil` holds although its value is not computed. `false` where the
        /// definition leaves open whether a value exists, or gives none.
        defined: bool,
    },
}

impl fmt::Display for UnsupportedHookReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotImplemented => formatter.write_str(
                "no evaluator in this backend, and no equation of the definition applies",
            ),
            Self::ArgumentOutOfRange { detail } | Self::ResultTooLarge { detail } => {
                formatter.write_str(detail)
            }
            Self::Unspecified { detail, .. } => {
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

/// Why the definition admits several values of `term`, a hooked application whose evaluator
/// computes one, so that the value is k-rust's choice rather than a consequence of the
/// definition; `None` when every value the definition admits is the same.
///
/// `keys_list(M)` and `values(M)` of a closed map with two or more bindings whose keys are all
/// constructor-like, and `Set2List(S)` of a closed set of two or more constructor-like elements,
/// are some listing of the items: domains.md fixes no order, so every order of the items is a
/// value some model gives. With zero or one item every listing is the same. The condition is the
/// one under which the evaluators list the items (`map::ordered_entries`, `set::concrete_set`),
/// read on the argument, not on the result. An application this names is defined exactly when
/// its argument is: a closed map with distinct constructor-like keys is defined when its values
/// are, a set of such elements is defined, and each has a listing.
pub(crate) fn implementation_chosen(term: &Term) -> Option<String> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return None;
    };
    let hook = symbol.attributes.hook.as_deref()?;
    let several = match hook {
        "MAP.keys_list" | "MAP.values" => map::lists_several_items(arguments),
        "SET.set2list" => set::lists_several_items(arguments),
        _ => false,
    };
    several.then(|| {
        format!(
            "{hook} of two or more items lists them in an order domains.md does not fix, which \
             only an execution chooses"
        )
    })
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
    let result = evaluate_hook_with_context(
        hook,
        arguments,
        Some(&result_sort),
        ResultCollection::declared(symbol.attributes.result_collection.as_ref(), sort_graph),
        sort_graph,
        definition,
        execution,
    )?;
    #[cfg(debug_assertions)]
    if let BuiltinResult::Value(value) = &result {
        debug_assert_value_of_sort(hook, value, &result_sort);
    }
    Ok(result)
}

/// Evaluation does not change the sort of the term it evaluates: the value of an application
/// of `f : ... -> S` is a value of exactly `S` (KORE has no implicit subsorting), and a
/// collection value holds elements of exactly its collection's element sorts.
#[cfg(debug_assertions)]
fn debug_assert_value_of_sort(hook: &str, value: &Term, result_sort: &Sort) {
    debug_assert_eq!(
        &value.sort(),
        result_sort,
        "{hook} evaluated to a value of another sort than its application: {value:?}"
    );
    match value.kind() {
        // The items' summaries keep their sorts when they all agree, so a list is checked
        // without reading the items the hook did not touch.
        TermKind::List {
            definition,
            heads,
            rest,
        } => {
            let sort = &definition.element_sort;
            debug_assert!(
                heads.summary().extra.all_of_sorts(sort, sort)
                    && rest
                        .as_ref()
                        .is_none_or(|(_, tails)| tails.summary().extra.all_of_sorts(sort, sort)),
                "{hook} evaluated to a list holding an element of another sort than its \
                 collection's: {value:?}"
            );
        }
        // The elements' summary keeps their sorts when they all agree, so a set is checked
        // without reading the elements the hook did not touch.
        TermKind::Set {
            definition,
            elements,
            ..
        } => {
            debug_assert!(
                elements
                    .summary()
                    .extra
                    .all_of_sorts(&definition.element_sort, &definition.element_sort),
                "{hook} evaluated to a set holding an element of another sort than its \
                 collection's: {value:?}"
            );
        }
        // The entries' summary keeps their sorts when they all agree, so a map is checked
        // without reading the entries the hook did not touch.
        TermKind::Map {
            definition,
            entries,
            ..
        } => {
            debug_assert!(
                entries
                    .summary()
                    .extra
                    .all_of_sorts(&definition.key_sort, &definition.value_sort),
                "{hook} evaluated to a map holding a key or value of another sort than its \
                 collection's: {value:?}"
            );
        }
        _ => {}
    }
}

pub use crate::term::names::PLUGIN_HOOK_NAMESPACES;
pub use float::is_float_syntax;

/// Evaluate `hook` on `arguments` without an applied symbol, so without a declared result sort:
/// a collection hook that transforms a collection argument builds its result in that argument's
/// collection, and one that introduces a collection (`LIST.unit`, `MAP.keys`, ...) declines.
pub fn evaluate_hook(
    hook: &str,
    arguments: &[Term],
) -> Stoppable<Result<BuiltinResult, BuiltinError>> {
    evaluate_hook_with_context(
        hook,
        arguments,
        None,
        ResultCollection::undeclared(None),
        None,
        None,
        None,
    )
    .layered()
}

/// Evaluate `hook` on `arguments` as an application whose declared result sort's collection is
/// `result` (`None`: its result sort is no collection sort).
#[cfg(test)]
pub(crate) fn evaluate_hook_into(
    hook: &str,
    arguments: &[Term],
    result: Option<&crate::term::CollectionMetadata>,
) -> Stoppable<Result<BuiltinResult, BuiltinError>> {
    evaluate_hook_with_context(
        hook,
        arguments,
        None,
        ResultCollection::declared(result, None),
        None,
        None,
        None,
    )
    .layered()
}

/// The value of a hook that gives one element of a collection argument (`LIST.get`,
/// `MAP.lookup`, `MAP.lookupOrDefault`) as a value of the application's sort: the element's sort
/// is that sort or a subsort of it, as the load checks (`hook_signature::misfit`), and a value of
/// a strict subsort is a value of the result once injected.
fn member_in_result(
    hook: &str,
    result: BuiltinResult,
    result_sort: Option<&Sort>,
    sort_graph: Option<&SortGraph>,
) -> HookResult<BuiltinResult> {
    match result {
        BuiltinResult::Value(value) if hook_signature::gives_member(hook) => Ok(
            hook_signature::member_of_result(value, result_sort, sort_graph)
                .map_or(BuiltinResult::NotApplicable, BuiltinResult::Value),
        ),
        result => Ok(result),
    }
}

fn evaluate_hook_with_context(
    hook: &str,
    arguments: &[Term],
    result_sort: Option<&Sort>,
    result_collection: ResultCollection<'_>,
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
                Some(HookNamespace::List) => member_in_result(
                    hook,
                    list::evaluate(hook, arguments, sort_graph, result_collection)?,
                    result_sort,
                    sort_graph,
                ),
                Some(HookNamespace::Map) => member_in_result(
                    hook,
                    map::evaluate(hook, arguments, sort_graph, result_collection)?,
                    result_sort,
                    sort_graph,
                ),
                Some(HookNamespace::Set) => {
                    set::evaluate(hook, arguments, sort_graph, result_collection)
                }
                Some(HookNamespace::Bytes) => bytes::evaluate(hook, arguments),
                Some(HookNamespace::Float) => float::evaluate(hook, arguments),
                Some(HookNamespace::MInt) => mint::evaluate(hook, arguments, result_sort),
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
    // Each byte read is one character, the code point of its value, as for `IO.getc`.
    let bytes = execution.read(maximum);
    Ok(BuiltinResult::Value(inject_result(
        Term::domain_value(Sort::builtin(BuiltinSort::String), console_text(bytes)),
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
    // Each character is written as one byte, its code point, as `IO.putc` writes one; a code
    // point above 255 has no byte.
    let Some(bytes) = value.as_utf8().ok().and_then(console_bytes) else {
        return Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::ArgumentOutOfRange {
                detail: "IO.write of a code point above 255, which is no byte".into(),
            },
        ));
    };
    let unit = io_k_unit("IO.write", result_sort, definition);
    if !matches!(unit, BuiltinResult::Value(_)) {
        return Ok(unit);
    }
    execution.append("IO.write", descriptor, Arc::<[u8]>::from(bytes));
    Ok(unit)
}

/// The `String` of console bytes: K's console hooks are POSIX operations on characters, and
/// `IO.getc` and `IO.putc` read and write one character as one byte, its code point; `IO.read`
/// and `IO.write` read and write a string of such characters, so each byte is the code point of
/// its value and back. (`domains.md` supports exactly the code points up to 255 in strings.)
pub(crate) fn console_text(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| char::from(*byte)).collect()
}

/// The console bytes of `text` (see [`console_text`]), `None` when a code point is above 255.
fn console_bytes(text: &str) -> Option<Vec<u8>> {
    text.chars()
        .map(|character| u8::try_from(u32::from(character)).ok())
        .collect()
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

/// The floor of the size bound on the `Int` results of `^Int` and `<<Int`, in bits (see
/// `result_size_limit`): 2^24 bits, 5,050,446 decimal digits. A result above its bound is
/// reported as too large (`ResultTooLarge`) instead of computed, and the application stays
/// unevaluated.
///
/// The floor bounds time, not memory: the cost of converting an `Int` between decimal text and
/// binary. A term holds an `Int` as its decimal domain value (`int_term` writes it with
/// `to_string`), and every hook application on it parses that text again (`read_int`), so a
/// value is paid for once per use, not once per run. Parsing decimal is quadratic in the length
/// in num-bigint 0.4.8, four times the work per doubling (release build, `perf stat` user
/// instructions: 2.2·10^10 at 2^22 bits, 8.7·10^10 at 2^23, 3.5·10^11 at 2^24, 1.4·10^12 at
/// 2^25; on a loaded host 1.2 s, 5.2 s, 23 s and 75 s), so one read of a 2^32-bit value would
/// take days. Rendering grows more slowly (at most 4·10^10 instructions, 3 s, at 2^24 bits).
/// The floor is where a refused result could not be used in reasonable time anyway: a run can
/// afford a few reads of a 2^23-bit value, not of a 2^25-bit one. It is a judgment about that
/// cost, not a property of the semantics, and it is fixed rather than read from the host: a
/// faster host divides the times by a constant, which leaves the growth unchanged. Memory is not
/// what it bounds: a 2^24-bit value is 2 MiB, 5,050,446 bytes of decimal text, far below what a
/// process may use (`Bytes` results are capped by that instead, see `ResultCap`).
pub const MAX_INT_RESULT_BITS: u64 = 1 << 24;

/// The most bytes one `padRightBytes`, `padLeftBytes` or `Int2Bytes` application holds at once,
/// per byte of its result, beyond reading its arguments: 2, the result as the hook builds it, in
/// one buffer of exactly its length, and its copy into the term that holds it (see [`ResultCap`]).
///
/// Measured, not chosen: `bytes_hooks_hold_twice_their_result` in `builtin/bytes.rs` records the
/// most memory one application allocates and has not freed, with a counting allocator, at two
/// result lengths, for each hook and for padded inputs empty, one byte long, a quarter, half and
/// all but one byte as long as the result, and takes the factor as the growth of that peak per
/// byte of result between the two lengths, which leaves out the few bytes every application holds
/// whatever its length.
pub(crate) const BYTES_RESULT_PEAK_FACTOR: u64 = 2;

/// The largest result a hook whose result size an argument's value sets computes, in bytes: the
/// result of `R` bytes is computed exactly when `factor * R <= L`, `L` the memory the process may
/// use ([`Allowance`]) and `factor` the most bytes one application of the hook holds per byte of
/// its result, and when `R` is at most `target`, what one result may take on this target.
///
/// Above the cap the application itself cannot fit the memory the process is allowed: its
/// allocations would fail and abort the process, or get it killed while the result is written.
/// Below it the result is computed however large, and its cost, time linear in its size for these
/// hooks, is bounded by the step timeout, not by a chosen size. The allowance is not reduced by
/// what the run already holds (see [`crate::allowance`]), so a result within the cap that does
/// not fit in what is left fails as any other allocation does.
pub(crate) struct ResultCap<'a> {
    allowance: &'a Allowance,
    factor: u64,
    target: u64,
    target_reason: &'static str,
}

impl<'a> ResultCap<'a> {
    /// The cap of a hook holding `factor` bytes per byte of its result under `allowance`, and at
    /// most `target` bytes on this target, for the reason `target_reason`.
    pub(crate) const fn new(
        allowance: &'a Allowance,
        factor: u64,
        target: u64,
        target_reason: &'static str,
    ) -> Self {
        Self {
            allowance,
            factor,
            target,
            target_reason,
        }
    }

    /// The largest result computed, in bytes.
    pub(crate) const fn bytes(&self) -> u64 {
        let allowed = self.allowance.bytes() / self.factor;
        if allowed < self.target {
            allowed
        } else {
            self.target
        }
    }

    /// The limit that sets the cap, for the detail of a refusal: the allowance with its source and
    /// the factor, or the target.
    pub(crate) fn reason(&self) -> String {
        if self.allowance.bytes() / self.factor > self.target {
            return self.target_reason.to_owned();
        }
        let share = match self.factor {
            1 => "all".to_owned(),
            2 => "half".to_owned(),
            3 => "a third".to_owned(),
            4 => "a quarter".to_owned(),
            factor => format!("1/{factor}"),
        };
        let unit = if self.factor == 1 { "byte" } else { "bytes" };
        format!(
            "{share} of the {} this process may use ({}), since one application holds {} {unit} \
             per byte of its result",
            describe_bytes(self.allowance.bytes()),
            self.allowance.source(),
            self.factor,
        )
    }
}

/// A number of bytes for a message: exact below 1 KiB, otherwise in the largest binary unit it
/// reaches, with one decimal where it is not whole.
pub(crate) fn describe_bytes(bytes: u64) -> String {
    const UNITS: [&str; 6] = ["KiB", "MiB", "GiB", "TiB", "PiB", "EiB"];
    if bytes < 1 << 10 {
        return format!("{bytes} bytes");
    }
    let exponent = ((63 - bytes.leading_zeros()) / 10).min(6);
    let scaled = bytes as f64 / (1_u64 << (10 * exponent)) as f64;
    let text = format!("{scaled:.1}");
    let text = text.strip_suffix(".0").unwrap_or(&text);
    format!("{text} {}", UNITS[exponent as usize - 1])
}

/// The longest `Bytes` result whose length an argument's value sets on this target
/// ([`target_bytes_result_len`] of `isize::MAX`): 2^27 bytes, 128 MiB, on a 32-bit target, and
/// 2^59 bytes on a 64-bit one, where it never binds.
pub(crate) const TARGET_BYTES_RESULT_LEN: u64 = target_bytes_result_len(isize::MAX as u64);

// Checked where the backend is built for a 32-bit target (`k-rust-wasm` on wasm32), whose tests
// do not build there: the target term binds below what the 4 GiB address space allows.
const _: () = assert!(
    usize::BITS != 32
        || (TARGET_BYTES_RESULT_LEN == 1 << 27
            && TARGET_BYTES_RESULT_LEN < (1 << 32) / BYTES_RESULT_PEAK_FACTOR)
);

/// The longest `Bytes` result on a target whose largest allocation is `largest_allocation`
/// bytes: a sixteenth of it, `(largest_allocation + 1) / 16`.
///
/// A `Bytes` value is also rendered when a run reports it, and its rendering is the largest form
/// it takes. KORE has no escape shorter than `\xhh` for a byte outside printable ASCII, so the
/// KORE text of a value of length `L` takes up to `4L + 2` bytes and its KORE JSON (`\u00hh`)
/// up to `6L + 2`; the library's JSON response holds the value, its externalized copy, the JSON
/// string of its characters (up to `2L`), the KORE JSON text and the response embedding it, about
/// `16L` at once. A sixteenth of the largest allocation keeps that peak within half of a 32-bit
/// address space, and its largest single allocation, `6L + 2`, below `isize::MAX`, which Rust
/// refuses to exceed by panicking. On a 64-bit target the term is 2^59 bytes and never binds.
pub(crate) const fn target_bytes_result_len(largest_allocation: u64) -> u64 {
    largest_allocation.saturating_add(1) / 16
}

/// The largest result `^Int` and `<<Int` compute when the result's size is set by the value of an
/// argument (`^Int`'s exponent, `<<Int`'s shift amount), given the total size `arguments` of its
/// arguments and the `floor` of the result's unit: `max(floor, 2 * arguments)`.
///
/// The bound keeps the cost of one hook application polynomial in the size of its arguments, so
/// it refuses only a result that is large relative to them: one that the exponent or length,
/// written in a number of digits logarithmic in its value, makes exponentially larger than what
/// the run already holds. Within twice the arguments' size a result is at most what one `*Int`
/// makes from the same values (`Y *Int Y`), and `*Int` is not bounded: a program that grows a
/// value by multiplication pays in each step for what it already built, so `Y <<Int 1`,
/// `Y ^Int 1` and `Y ^Int 2` are computed whatever the size of `Y`, as `Y *Int 2` and
/// `Y *Int Y` are.
pub(crate) const fn result_size_limit(floor: u64, arguments: u64) -> u64 {
    let relative = arguments.saturating_mul(2);
    if relative > floor { relative } else { floor }
}

/// How the bit length of `|base| ^Int exponent` compares with `bound`, decided without computing
/// the power where possible.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PowerSize {
    Fits,
    TooLarge,
    /// Not decided without computing the power.
    Undecided,
}

/// For `|base| >= 2` and `exponent >= 1`: whether `|base| ^Int exponent` has at most `bound` bits.
///
/// A positive integer `x` has `floor(log2 x) + 1` bits, so the power fits exactly when
/// `exponent * log2 |base| < bound`. For a power of two that product is the integer
/// `exponent * (bits - 1)`. Otherwise it is estimated in `f64` from the base's leading 64 bits:
/// once the minimum length `(bits - 1) * exponent + 1` is within the bound, the product is below
/// `2 * bound`, and the estimate's error (the truncated low bits, below `2^-62` in the
/// logarithm, and a few rounding steps, each relative to `2^-52`, in the logarithm, the product
/// and the bound's conversion) is below `bound * 2^-48`, far below the margin
/// `max(10^-6, bound * 2^-40)`. Only an estimate within that margin of the bound is left
/// `Undecided`, which no product of a base that is not a power of two and an exponent reaches
/// exactly, since its logarithm is irrational.
fn power_size(base: &BigInt, exponent: u64, bound: u64) -> PowerSize {
    let magnitude = base.magnitude();
    let bits = magnitude.bits();
    let Some(minimum) = (bits - 1)
        .checked_mul(exponent)
        .and_then(|minimum| minimum.checked_add(1))
    else {
        return PowerSize::TooLarge;
    };
    if minimum > bound {
        return PowerSize::TooLarge;
    }
    if magnitude.trailing_zeros() == Some(bits - 1) {
        // |base| = 2^(bits - 1): the power is 2^((bits - 1) * exponent), of `minimum` bits.
        return PowerSize::Fits;
    }
    let dropped = bits.saturating_sub(64);
    let leading = (magnitude >> dropped)
        .to_u64()
        .expect("at most 64 leading bits");
    // An estimate whose error the margin covers (above).
    let product = exponent as f64 * ((leading as f64).log2() + dropped as f64);
    let bound = bound as f64;
    let margin = (bound * 2f64.powi(-40)).max(1e-6);
    if product < bound - margin {
        PowerSize::Fits
    } else if product >= bound + margin {
        PowerSize::TooLarge
    } else {
        PowerSize::Undecided
    }
}

fn int_pow(arguments: &[Term]) -> HookResult<BuiltinResult> {
    int_pow_within(arguments, MAX_INT_RESULT_BITS)
}

/// `^Int` with `floor` as the floor of its result bound (`result_size_limit`).
///
/// `domains.md` describes `^Int` as "the exponentiation of two integers", of sort `Int`, and does
/// not declare it `total`. For a negative exponent `-n`, `b ^Int -n` is the integer `1 / b^n`
/// exactly when `|b| = 1`: the powers of 1 and -1 have a value for every exponent, and those of
/// any other base (0, or a magnitude of at least 2) have no integer value there, so the
/// application is undefined.
fn int_pow_within(arguments: &[Term], floor: u64) -> HookResult<BuiltinResult> {
    expect_arity("INT.pow", arguments, 2)?;
    let Some((mut base, exponent)) = read_int(&arguments[0]).zip(read_int(&arguments[1])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if base.is_one() {
        return Ok(BuiltinResult::Value(int_term(BigInt::one())));
    }
    if base == -BigInt::one() {
        // The parity of the two's complement, also for a negative exponent.
        let odd = (&exponent & BigInt::one()).is_one();
        return Ok(BuiltinResult::Value(int_term(if odd {
            -BigInt::one()
        } else {
            BigInt::one()
        })));
    }
    if exponent.sign() == Sign::Minus {
        return Ok(BuiltinResult::Bottom);
    }
    if exponent.is_zero() {
        return Ok(BuiltinResult::Value(int_term(BigInt::one())));
    }
    if base.is_zero() {
        return Ok(BuiltinResult::Value(int_term(BigInt::zero())));
    }
    let limit = result_size_limit(floor, base.bits().saturating_add(exponent.bits()));
    // Described only when refused, by the operands' sizes (`describe_int`).
    let too_large = |base: String| {
        Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::ResultTooLarge {
                detail: format!(
                    "{base} ^Int {} needs more than {limit} bits",
                    describe_int(&exponent)
                ),
            },
        ))
    };
    let Some(mut remaining) = exponent.to_u64() else {
        return too_large(describe_int(&base));
    };
    let size = power_size(&base, remaining, limit);
    if size == PowerSize::TooLarge {
        return too_large(describe_int(&base));
    }
    // The base is squared in place below; an undecided size is checked after computing.
    let undecided_base = (size == PowerSize::Undecided).then(|| describe_int(&base));
    let mut result = BigInt::one();
    while remaining != 0 {
        crate::stop::check()?;
        if remaining & 1 == 1 {
            result *= &base;
        }
        remaining >>= 1;
        if remaining != 0 {
            base = &base * &base;
        }
    }
    // Only an `Undecided` size gets here above the bound.
    if let Some(base) = undecided_base
        && result.bits() > limit
    {
        return too_large(base);
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
    // `A ^%Int B C` is `(A ^Int B) mod C`. For a negative exponent the power is an integer only
    // for a base of 1 or -1 (`int_pow_within`), and otherwise undefined, and so is the remainder.
    if exponent.sign() == Sign::Minus {
        if !base.magnitude().is_one() {
            return Ok(BuiltinResult::Bottom);
        }
        let odd = (&exponent & BigInt::one()).is_one();
        let power = if base.sign() == Sign::Minus && odd {
            -BigInt::one()
        } else {
            BigInt::one()
        };
        return Ok(BuiltinResult::Value(int_term(
            euclidean_modulus(power, modulus).expect("non-zero modulus"),
        )));
    }
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
    int_shift_within(hook, arguments, right, MAX_INT_RESULT_BITS)
}

/// `<<Int` (or `>>Int`, when `right`) with `floor` as the floor of a left shift's result bound
/// (`result_size_limit`).
fn int_shift_within(
    hook: &str,
    arguments: &[Term],
    right: bool,
    floor: u64,
) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 2)?;
    let Some((value, amount)) = read_int(&arguments[0]).zip(read_int(&arguments[1])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    // Shifting by a negative quantity is undefined (`#False` in `domains.md`) for both shifts.
    if amount.sign() == Sign::Minus {
        return Ok(BuiltinResult::Bottom);
    }
    let shifts_left = !right;
    let limit = result_size_limit(floor, value.bits().saturating_add(amount.bits()));
    let too_large = || {
        Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::ResultTooLarge {
                detail: format!(
                    "{} <<Int {} needs more than {limit} bits",
                    describe_int(&value),
                    describe_int(&amount)
                ),
            },
        ))
    };
    if shifts_left
        && !value.is_zero()
        && amount
            .to_u64()
            .and_then(|amount| amount.checked_add(value.bits()))
            .is_none_or(|bits| bits > limit)
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
            Some(InjectionEquality::Unknown) | None => {
                // Items of sorts that may share values: compare the injected operands, which
                // separates two certified normal forms of different heads.
                let (Some(left), Some(right)) = (
                    k_sequence_item(&arguments[0]),
                    k_sequence_item(&arguments[1]),
                ) else {
                    unreachable!("both operands are one-element sequences of an injection")
                };
                return Ok(evaluate_equality(left, right, sort_graph)
                    .map(|equal| bool_term(equal != negate)));
            }
        }
    }
    // Every other pair of operands of one sort is compared whole. `K` is generated by the free
    // constructors `dotk` and `kseq`, so the empty sequence, a sequence of any length and an item
    // of sort `KItem` itself are values like a single injected item; two operands of a function
    // hooked `KEQUAL` on one other sort are values of that sort. Operands of two different sorts
    // (a function hooked `KEQUAL` on `Foo` and `Bar`) spell one value differently, `inj{Bar,
    // Foo}(z())` and `z()`, so their spellings are no evidence and the pair is left undecided.
    if arguments[0].sort() != arguments[1].sort() {
        return Ok(None);
    }
    Ok(evaluate_equality(&arguments[0], &arguments[1], sort_graph)
        .map(|equal| bool_term(equal != negate)))
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
/// operands, so the pairs below them need not be scanned for apartness again.
///
/// The answer is `Some(false)` when some pair reached through free-constructor arguments and
/// equivalent injection operands is decided unequal, otherwise `None` when some such pair is
/// undecided, otherwise `Some(true)`; it does not depend on the order the pairs are visited in,
/// so they are kept on a work list rather than the native stack. The hook runs between two
/// stack checks of the simplifier on operands of any height.
#[deny(clippy::wildcard_enum_match_arm)]
fn evaluate_equality_by_roots(
    left: &Term,
    right: &Term,
    sort_graph: Option<&SortGraph>,
) -> Option<bool> {
    fn fixed(term: &Term) -> Option<Fixed<'_>> {
        match classify_value(term, &mut NoEvidence) {
            Head::Fixed(fixed) => Some(fixed),
            Head::Open(_) | Head::Residual => None,
        }
    }
    let mut undecided = false;
    let mut pending = vec![(left.clone(), right.clone())];
    while let Some((left, right)) = pending.pop() {
        if left.attributes().constructor_like && right.attributes().constructor_like {
            if left != right {
                return Some(false);
            }
            continue;
        }
        if let (Some(left_root), Some(right_root)) = (fixed(&left), fixed(&right))
            && (left_root.root() == FixedRoot::FreeConstructor
                || right_root.root() == FixedRoot::FreeConstructor)
        {
            match compare_roots(left_root, right_root) {
                RootComparison::Distinct(_) | RootComparison::ArityMismatch => return Some(false),
                // Two applications of one free symbol are equal exactly when their arguments
                // are.
                RootComparison::SameApplication(same) => pending.extend(
                    same.pairs()
                        .map(|(left, right)| (left.clone(), right.clone())),
                ),
                RootComparison::DomainValues
                | RootComparison::Injections
                | RootComparison::Collections(_) => {
                    unreachable!("one of the two roots is a free-constructor application")
                }
            }
            continue;
        }
        match (left.kind(), right.kind()) {
            (TermKind::Injection { .. }, TermKind::Injection { .. }) => {
                match match_injection_equality(sort_graph, &left, &right) {
                    Some(
                        InjectionEquality::Direct(left, right)
                        | InjectionEquality::Split(left, right),
                    ) => pending.push((left, right)),
                    Some(InjectionEquality::Distinct) => return Some(false),
                    Some(InjectionEquality::Unknown) | None => undecided = true,
                }
            }
            (TermKind::DomainValue { .. }, TermKind::DomainValue { .. }) => {
                if left != right {
                    return Some(false);
                }
            }
            _ if left == right => {}
            _ => undecided = true,
        }
    }
    (!undecided).then_some(true)
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

/// An integer operand as a refusal or diagnostic message shows it: in decimal when it has at most
/// 64 bits, otherwise by its size, so that a message about a value too large to compute does not
/// cost the decimal rendering of its operands, which grows faster than linearly in their length.
pub(crate) fn describe_int(value: &BigInt) -> String {
    let bits = value.bits();
    if bits <= 64 {
        value.to_string()
    } else if value.sign() == Sign::Minus {
        format!("a negative {bits}-bit integer")
    } else {
        format!("a {bits}-bit integer")
    }
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

    /// `KEQUAL` over operands 20,000 free-constructor applications deep, on a 256 KiB thread:
    /// the equality walks the common spine with its pending pairs on the heap (a recursion per
    /// level overflowed here in every build). The operands share no node and end in a variable,
    /// so neither is constructor-like and the spine is walked to its end, where `X` against a
    /// copy of `X` is equal and `X` against `Y` undecided. They are built and dropped on a
    /// larger thread, since dropping a term recurses.
    #[test]
    fn equality_of_deep_operands_is_decided_on_a_small_stack() {
        const LEVELS: usize = 20_000;
        std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn(|| {
                let sort = Sort::simple("SortS");
                let wrap = Arc::new(Symbol::constructor("w", vec![sort.clone()], sort.clone()));
                let chain = |name: &str| {
                    (0..LEVELS).fold(
                        Term::variable(Variable::new(name, sort.clone())),
                        |term, _| Term::application(wrap.clone(), Vec::new(), vec![term]),
                    )
                };
                let (x, x_copy, y) = (chain("X"), chain("X"), chain("Y"));
                let decided = std::thread::scope(|scope| {
                    std::thread::Builder::new()
                        .stack_size(256 * 1024)
                        .spawn_scoped(scope, || {
                            (
                                evaluate_equality(&x, &x_copy, None),
                                evaluate_equality(&x, &y, None),
                            )
                        })
                        .unwrap()
                        .join()
                        .unwrap()
                });
                assert_eq!(decided, (Some(true), None));
            })
            .unwrap()
            .join()
            .unwrap();
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

    /// `K` values built from `dotk`, `kseq` and items of sort `KItem` (with or without an
    /// injection), and operands of a user sort that are not `K` values, on both sides of
    /// `KEQUAL.eq`/`KEQUAL.ne`; operands of two different sorts are left undecided.
    #[test]
    fn kequal_compares_whole_k_sequences() {
        let k_item = Sort::simple("SortKItem");
        let k = Sort::simple("SortK");
        let kseq = Arc::new(Symbol::constructor(
            "kseq",
            vec![k_item.clone(), k.clone()],
            k.clone(),
        ));
        let dotk = Term::application(
            Arc::new(Symbol::constructor("dotk", Vec::new(), k.clone())),
            Vec::new(),
            Vec::new(),
        );
        let seq =
            |item: Term, tail: Term| Term::application(kseq.clone(), Vec::new(), vec![item, tail]);
        let item = |name: &str| {
            Term::application(
                Arc::new(Symbol::constructor(name, Vec::new(), k_item.clone())),
                Vec::new(),
                Vec::new(),
            )
        };
        let injected = |value: i64| {
            Term::injection(
                Sort::simple("SortInt"),
                k_item.clone(),
                int_term(BigInt::from(value)),
            )
        };
        let tail = Term::variable(Variable::new("K", k.clone()));
        let a = item("a");
        let b = item("b");
        let a_b = seq(a.clone(), seq(b.clone(), dotk.clone()));
        // Operands of a user symbol hooked `KEQUAL.eq` on a sort `Foo` above `Bar`: not K
        // sequences at all.
        let foo = Sort::simple("SortFoo");
        let user = |name: &str, sort: &Sort, arguments: Vec<Term>| {
            let argument_sorts = arguments.iter().map(Term::sort).collect();
            Term::application(
                Arc::new(Symbol::constructor(name, argument_sorts, sort.clone())),
                Vec::new(),
                arguments,
            )
        };
        let x = user("x", &foo, Vec::new());
        let y_1 = user("y", &foo, vec![int_term(BigInt::from(1))]);
        let z = Term::injection(
            Sort::simple("SortBar"),
            foo.clone(),
            user("z", &Sort::simple("SortBar"), Vec::new()),
        );
        let cases = [
            (dotk.clone(), dotk.clone(), Some(true)),
            (dotk.clone(), seq(a.clone(), dotk.clone()), Some(false)),
            (
                seq(a.clone(), dotk.clone()),
                seq(a.clone(), dotk.clone()),
                Some(true),
            ),
            (
                seq(a.clone(), dotk.clone()),
                seq(b.clone(), dotk.clone()),
                Some(false),
            ),
            (a_b.clone(), a_b.clone(), Some(true)),
            (a_b.clone(), seq(a.clone(), dotk.clone()), Some(false)),
            (
                seq(injected(1), dotk.clone()),
                seq(a.clone(), dotk.clone()),
                Some(false),
            ),
            (
                seq(injected(1), a_b.clone()),
                seq(injected(1), a_b.clone()),
                Some(true),
            ),
            (seq(a.clone(), tail.clone()), dotk.clone(), Some(false)),
            (
                seq(a.clone(), tail.clone()),
                seq(b.clone(), dotk.clone()),
                Some(false),
            ),
            (tail.clone(), tail.clone(), Some(true)),
            (
                seq(a.clone(), tail.clone()),
                seq(a.clone(), dotk.clone()),
                None,
            ),
            (tail.clone(), dotk.clone(), None),
            (y_1.clone(), y_1.clone(), Some(true)),
            (x.clone(), y_1.clone(), Some(false)),
            (z.clone(), x.clone(), Some(false)),
        ];
        // Operands of two different sorts, `Foo` and `Bar` (one value, `z()`, spelled at each),
        // and `KItem` and `K`: no answer.
        let bare_z = user("z", &Sort::simple("SortBar"), Vec::new());
        let cases = cases.into_iter().chain([
            (z.clone(), bare_z.clone(), None),
            (x.clone(), bare_z, None),
            (a.clone(), seq(a.clone(), dotk.clone()), None),
        ]);
        for (left, right, expected) in cases {
            for (left, right) in [(&left, &right), (&right, &left)] {
                let arguments = [left.clone(), right.clone()];
                let result = |hook| match evaluate_hook(hook, &arguments) {
                    Ok(Ok(BuiltinResult::Value(value))) => read_bool(&value),
                    Ok(Ok(BuiltinResult::NotApplicable)) => None,
                    other => panic!("{hook} on {left:?} and {right:?}: {other:?}"),
                };
                assert_eq!(result("KEQUAL.eq"), expected, "{left:?} ==K {right:?}");
                assert_eq!(
                    result("KEQUAL.ne"),
                    expected.map(|equal| !equal),
                    "{left:?} =/=K {right:?}"
                );
            }
        }
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
            // A negative exponent: the powers of 1 and -1, reduced likewise.
            (-1, -1, 5, 4),
            (-1, -3, -7, 6),
            (-1, -2, 7, 1),
            (1, -5, 7, 1),
            (1, -1, 1, 0),
        ] {
            assert_eq!(
                powmod(base, exponent, modulus),
                Ok(Ok(BuiltinResult::Value(int_term(BigInt::from(expected))))),
                "{base} ^%Int {exponent} {modulus}"
            );
        }
        assert_eq!(powmod(2, 3, 0), Ok(Ok(BuiltinResult::Bottom)));
    }

    /// From one-word arguments, a result of exactly `MAX_INT_RESULT_BITS` bits is computed and
    /// one more bit is reported as too large, for `^Int` and `<<Int` alike.
    #[test]
    fn int_results_are_computed_up_to_the_result_bound() {
        let bound = BigInt::from(MAX_INT_RESULT_BITS);
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

    /// A refusal names an operand above 64 bits by its size, not its digits: the message of a
    /// result too large to compute must not cost the decimal rendering of its operands, which
    /// grows faster than linearly in their length (and was paid on every evaluation of `^Int`).
    #[test]
    fn a_refusal_describes_large_operands_by_their_size() {
        let base = num_traits::pow(BigInt::from(3), 200_000);
        let bits = base.bits();
        let amount = BigInt::from(1_u64 << 40);
        for (hook, operator) in [("INT.pow", "^Int"), ("INT.shl", "<<Int")] {
            let refused = evaluate_hook(hook, &[int_term(base.clone()), int_term(amount.clone())]);
            let Ok(Ok(BuiltinResult::Unsupported(UnsupportedHookReason::ResultTooLarge {
                detail,
            }))) = refused
            else {
                panic!("{hook}: {refused:?}");
            };
            assert!(
                detail.starts_with(&format!("a {bits}-bit integer {operator} 1099511627776 ")),
                "{hook}: {detail}"
            );
            assert!(detail.len() < 120, "{hook}: {detail}");
        }
        assert_eq!(describe_int(&BigInt::from(-5)), "-5");
        assert_eq!(
            describe_int(&-(BigInt::one() << 64u32)),
            "a negative 65-bit integer"
        );
    }

    /// A result is refused only when it is large relative to its arguments
    /// (`result_size_limit`): within twice their size it is computed whatever the floor, as
    /// `*Int` computes `Y *Int Y`; from small arguments the floor applies. A floor of 64 bits
    /// stands for `MAX_INT_RESULT_BITS` here.
    #[test]
    fn results_are_bounded_relative_to_their_arguments() {
        let floor = 64;
        let value = |result: HookResult<BuiltinResult>| match result {
            Ok(BuiltinResult::Value(term)) => read_int(&term),
            _ => None,
        };
        let refused = |result: HookResult<BuiltinResult>| {
            matches!(
                result,
                Ok(BuiltinResult::Unsupported(
                    UnsupportedHookReason::ResultTooLarge { .. }
                ))
            )
        };
        let pow = |base: &BigInt, exponent: u64| {
            int_pow_within(
                &[int_term(base.clone()), int_term(BigInt::from(exponent))],
                floor,
            )
        };
        let shl = |value: &BigInt, amount: u64| {
            int_shift_within(
                "INT.shl",
                &[int_term(value.clone()), int_term(BigInt::from(amount))],
                false,
                floor,
            )
        };
        // A 100-bit value, above the floor, as `*Int` can build one.
        let y = (BigInt::one() << 99u32) + 12_345u32;
        assert_eq!(value(pow(&y, 1)), Some(y.clone()));
        // 200 bits, within 2 * (100 + 2); 300 bits is not.
        assert_eq!(value(pow(&y, 2)), Some(&y * &y));
        assert!(refused(pow(&y, 3)));
        assert_eq!(value(shl(&y, 1)), Some(&y << 1u32));
        // 214 bits is exactly 2 * (100 + 7), 7 being the length of the shift amount.
        assert_eq!(value(shl(&y, 114)), Some(&y << 114u32));
        assert!(refused(shl(&y, 115)));
        // From one- and two-bit arguments, the floor.
        assert_eq!(value(shl(&BigInt::one(), 63)), Some(BigInt::one() << 63u32));
        assert!(refused(shl(&BigInt::one(), 64)));
        assert_eq!(
            value(pow(&BigInt::from(2), 63)),
            Some(BigInt::one() << 63u32)
        );
        assert!(refused(pow(&BigInt::from(2), 64)));
        assert!(refused(pow(&BigInt::from(3), 41)));
        assert_eq!(
            value(pow(&BigInt::from(3), 40)),
            Some(num_traits::pow(BigInt::from(3), 40))
        );
        assert_eq!(result_size_limit(64, 10), 64);
        assert_eq!(result_size_limit(64, 33), 66);
        assert_eq!(result_size_limit(64, u64::MAX), u64::MAX);
    }

    /// The size of a power is decided before it is computed, so a power above the bound is
    /// never computed only to be refused (`3 ^Int 700000` has at least 700,001 bits, below a
    /// bound of 2^20 bits, and in fact 1,109,474, above it); and the decision agrees with the
    /// exact length.
    #[test]
    fn power_size_is_decided_before_computing() {
        let bound = 1 << 20;
        for (base, exponent, expected) in [
            (3, 700_000, PowerSize::TooLarge),
            (-3, 700_000, PowerSize::TooLarge),
            (3, 600_000, PowerSize::Fits),
            (2, bound, PowerSize::TooLarge),
            (2, bound - 1, PowerSize::Fits),
            (-2, bound - 1, PowerSize::Fits),
            (4, bound / 2, PowerSize::TooLarge),
            (4, bound / 2 - 1, PowerSize::Fits),
        ] {
            assert_eq!(
                power_size(&BigInt::from(base), exponent, bound),
                expected,
                "{base} ^Int {exponent}"
            );
        }
        // log2 of 3 * 2^199 + 12345 is about 200.585: 5227 * 200.585 < 2^20 < 5228 * 200.585,
        // and both exponents pass the minimum-length check (200 * 5228 + 1 < 2^20).
        let large_base = (BigInt::from(3) << 199u32) + 12_345u32;
        assert_eq!(power_size(&large_base, 5_228, bound), PowerSize::TooLarge);
        assert_eq!(power_size(&large_base, 5_227, bound), PowerSize::Fits);
        // Against the exact length, for small bounds: a decided answer is never wrong.
        for bound in [8u64, 63, 64, 65, 200, 1000] {
            for base in 2u32..300 {
                for exponent in 1u32..80 {
                    let bits = BigInt::from(base).pow(exponent).bits();
                    match power_size(&BigInt::from(base), u64::from(exponent), bound) {
                        PowerSize::Fits => assert!(bits <= bound, "{base}^{exponent} {bound}"),
                        PowerSize::TooLarge => assert!(bits > bound, "{base}^{exponent} {bound}"),
                        PowerSize::Undecided => {
                            panic!("{base}^{exponent} against {bound} left undecided")
                        }
                    }
                }
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
            key_sort: Sort::simple("SortInt"),
            value_sort: Sort::simple("SortInt"),
            map_sort: "SortMap".into(),
        });
        let list_definition = Arc::new(ListDefinition {
            symbols,
            element_sort: Sort::simple("SortInt"),
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

    /// `rootFloat(F, N)` is IEEE 754 rootn(F, N) for every degree. Degree 2 is the square root,
    /// except that the even root of -0 is +0 (and so is `sqrtFloat(-0.0)`, the K rule
    /// `rootFloat(F, 2)`); degree 0 and an even root of a negative value are NaN; a zero gives a
    /// zero of its sign for an odd positive degree, +0 for an even one, an infinity of its sign
    /// for an odd negative degree and +inf for an even one; an infinity gives an infinity for a
    /// positive degree and a zero for a negative one, with its sign for an odd degree and NaN for
    /// an even root of -inf.
    #[test]
    fn float_root_is_the_ieee_rootn_of_every_degree() {
        let cases = [
            ("4.0f", 2, "2.00000000e+00p24x8"),
            ("2.0", 2, "1.4142135623730951e+00p53x11"),
            ("-4.0f", 2, "NaNp24x8"),
            ("NaN", 2, "NaNp53x11"),
            ("Infinityf", 2, "Infinityp24x8"),
            ("-Infinity", 2, "NaNp53x11"),
            ("0.0", 2, "0e+00p53x11"),
            ("-0.0f", 2, "0e+00p24x8"),
            ("-0.0", 2, "0e+00p53x11"),
            ("8.0f", 3, "2.00000000e+00p24x8"),
            ("-8.0", 3, "-2.0000000000000000e+00p53x11"),
            ("27.0", 3, "3.0000000000000000e+00p53x11"),
            ("16.0", -4, "5.0000000000000000e-01p53x11"),
            ("-8.0", 4, "NaNp53x11"),
            ("2.0", 0, "NaNp53x11"),
            ("2.0", 1, "2.0000000000000000e+00p53x11"),
            ("4.0", -1, "2.5000000000000000e-01p53x11"),
            ("-0.0", 3, "-0e+00p53x11"),
            ("-0.0", -3, "-Infinityp53x11"),
            ("-0.0", -2, "Infinityp53x11"),
            ("0.0f", -3, "Infinityp24x8"),
            ("Infinity", -3, "0e+00p53x11"),
            ("-Infinity", 3, "-Infinityp53x11"),
            ("-Infinity", -3, "-0e+00p53x11"),
            ("-Infinityf", 4, "NaNp24x8"),
        ];
        for (value, degree, expected) in cases {
            assert_eq!(
                evaluate_hook(
                    "FLOAT.root",
                    &[float_term(value), int_term(BigInt::from(degree))],
                ),
                Ok(Ok(BuiltinResult::Value(float_term(expected)))),
                "root({value}, {degree})"
            );
        }
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
            ("INT.powmod", &[-1, -1, 7][..], 6),
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

    /// `b ^Int -n` is the integer `1 / b^n` exactly when `|b| = 1`, so the powers of 1 and -1
    /// have values for every exponent (and those of other bases are undefined, in
    /// `undefined_integer_operations_are_bottom`).
    #[test]
    fn unit_bases_have_a_power_for_every_exponent() {
        for (base, exponent, expected) in [
            (1, -1, 1),
            (1, -7, 1),
            (-1, -1, -1),
            (-1, -2, 1),
            (-1, -3, -1),
            (-1, 0, 1),
            (1, 0, 1),
        ] {
            assert_eq!(
                evaluate_int("INT.pow", &[base, exponent]),
                Ok(Ok(BuiltinResult::Value(int_term(BigInt::from(expected))))),
                "{base} ^Int {exponent}"
            );
        }
        let huge = -(BigInt::one() << 100u32) - 1u8;
        assert_eq!(
            evaluate_hook("INT.pow", &[int_term(-BigInt::one()), int_term(huge)]),
            Ok(Ok(BuiltinResult::Value(int_term(-BigInt::one()))))
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
            evaluate_int("INT.pow", &[0, -1]),
            Ok(Ok(BuiltinResult::Bottom))
        );
        assert_eq!(
            evaluate_int("INT.pow", &[-3, -2]),
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
        // `(A ^Int B) mod C` has no value where `A ^Int B` has none, even where A is invertible
        // modulo C.
        for (base, exponent, modulus) in [(3, -1, 7), (2, -1, 7), (-2, -3, 7), (0, -1, 5)] {
            assert_eq!(
                evaluate_int("INT.powmod", &[base, exponent, modulus]),
                Ok(Ok(BuiltinResult::Bottom)),
                "{base} ^%Int {exponent} {modulus}"
            );
        }
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
                    && term.attributes().value_claimed())
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
                element_sort: Sort::simple("SortS"),
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
