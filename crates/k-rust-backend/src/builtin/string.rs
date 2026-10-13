//! Deterministic `STRING` hooks: per-call operations on strings.

use num_bigint::{BigInt, Sign};
use num_traits::ToPrimitive;

use k_rust_kore::kore::ast::KoreString;
use k_rust_kore::kore::string::LiteralEncoding;
use k_rust_kore::names::BuiltinSort;

use super::{
    BuiltinResult, HookResult, UnsupportedHookReason, bool_term, expect_arity, int_term, read_int,
};
use crate::{
    definition::BackendDefinition,
    externalize,
    term::{
        DomainKind, Sort, Term, TermKind,
        domain::{TextRejection, validate_text},
    },
};

/// The application a `STRING` hook evaluates, beyond its arguments: its declared result sort,
/// the definition it belongs to, and whether its symbol is declared `total`.
#[derive(Clone, Copy)]
pub(super) struct Declaration<'a> {
    pub(super) result_sort: Option<&'a Sort>,
    pub(super) definition: Option<&'a BackendDefinition>,
    pub(super) total: bool,
}

pub(super) fn evaluate(
    hook: &str,
    arguments: &[Term],
    declaration: Declaration<'_>,
) -> HookResult<BuiltinResult> {
    match hook {
        "STRING.eq" => compare(hook, arguments, |left, right| left == right),
        "STRING.ne" => compare(hook, arguments, |left, right| left != right),
        "STRING.lt" => compare(hook, arguments, |left, right| left < right),
        "STRING.le" => compare(hook, arguments, |left, right| left <= right),
        "STRING.gt" => compare(hook, arguments, |left, right| left > right),
        "STRING.ge" => compare(hook, arguments, |left, right| left >= right),
        "STRING.concat" => concatenate(arguments),
        "STRING.substr" => substring(arguments),
        "STRING.length" => length(arguments),
        "STRING.countAllOccurrences" => count_all_occurrences(arguments),
        "STRING.replaceAll" => replace_all(arguments),
        "STRING.find" => find(arguments, false),
        "STRING.rfind" => find(arguments, true),
        "STRING.string2base" => string_to_base(arguments),
        "STRING.base2string" => base_to_string(arguments),
        "STRING.string2int" => string_to_int(arguments),
        "STRING.int2string" => int_to_string(arguments),
        "STRING.chr" => chr(arguments),
        "STRING.ord" => ord(arguments),
        "STRING.token2string" => token_to_string(arguments),
        "STRING.string2token" => string_to_token(arguments, declaration),
        _ => Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::NotImplemented,
        )),
    }
}

fn compare(
    hook: &str,
    arguments: &[Term],
    comparison: impl FnOnce(&[u8], &[u8]) -> bool,
) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 2)?;
    let Some((left, right)) = read_string(&arguments[0]).zip(read_string(&arguments[1])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    // UTF-8 orders byte strings as it orders the code point sequences they encode.
    Ok(BuiltinResult::Value(bool_term(comparison(
        left.as_bytes(),
        right.as_bytes(),
    ))))
}

fn concatenate(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.concat", arguments, 2)?;
    let Some((left, right)) = read_string(&arguments[0]).zip(read_string(&arguments[1])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let mut result = String::with_capacity(left.len().saturating_add(right.len()));
    result.push_str(left);
    result.push_str(right);
    Ok(BuiltinResult::Value(string_term(result)))
}

/// `substrString(S, START, END)` is the code points of S in `[START..END)` when
/// `0 <= START <= END <= lengthString(S)`. `domains.md` declares it `total` but says it is "only
/// defined on valid indices", so outside them it has a value the definition does not give: the
/// application is left unevaluated (`Unspecified`). Valid indices include `START == END`, which
/// the `domains.md` equations of `replaceFirst`, `findChar` and `countAllOccurrences` use.
fn substring(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.substr", arguments, 3)?;
    let Some(value) = read_string(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some((start, end)) = read_int(&arguments[1]).zip(read_int(&arguments[2])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    // The byte offsets at which code points `start` and `end` begin, the end of the value
    // being where the code point after the last would begin; scanning stops at `end`.
    let mut offsets = (None, None);
    if start.sign() != Sign::Minus
        && start <= end
        && let (Some(start), Some(end)) = (start.to_usize(), end.to_usize())
    {
        let boundaries = code_point_offsets(value).chain(std::iter::once(value.len()));
        for (unit, offset) in boundaries.enumerate() {
            if unit == start {
                offsets.0 = Some(offset);
            }
            if unit == end {
                offsets.1 = Some(offset);
                break;
            }
        }
    }
    let (Some(start_offset), Some(end_offset)) = offsets else {
        return Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::Unspecified {
                detail: format!(
                    "substrString from {start} to {end} on a string of length {}, outside the valid indices 0 <= start <= end <= length",
                    value.chars().count()
                ),
            },
        ));
    };
    Ok(BuiltinResult::Value(string_term(
        &value[start_offset..end_offset],
    )))
}

fn length(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.length", arguments, 1)?;
    let Some(value) = read_string(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(int_term(BigInt::from(
        value.chars().count(),
    ))))
}

/// `countAllOccurrences(S, N)` is the number of occurrences of `N` in `S` found from the left,
/// each search starting after the previous match: the `domains.md` equations count one at the
/// first occurrence and continue on the rest of `S` after it. For an empty `N` those equations
/// give `countAllOccurrences(S, "") = 1 +Int countAllOccurrences(S, "")` (the empty needle is
/// found at 0 and nothing is consumed), which no integer satisfies, so the `total` hook has a
/// value the definition does not determine, whatever `S` is, a symbolic one included:
/// `Unspecified`, which also keeps the simplifier from applying the diverging equations.
///
/// Matching the UTF-8 of `N` in the UTF-8 of `S` finds exactly the occurrences that start and end
/// on code point boundaries, since no code point's encoding starts inside another's.
fn count_all_occurrences(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.countAllOccurrences", arguments, 2)?;
    if let Some(unspecified) = empty_needle("countAllOccurrences", &arguments[1]) {
        return Ok(unspecified);
    }
    let Some((haystack, needle)) = read_string(&arguments[0]).zip(read_string(&arguments[1]))
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(int_term(BigInt::from(
        haystack.matches(needle).count(),
    ))))
}

/// `replaceAll(S, N, R)` replaces the occurrences `countAllOccurrences(S, N)` counts, found from
/// the left without overlap, by `R` (the `domains.md` equation `replace(S, N, R,
/// countAllOccurrences(S, N))`); for an empty `N` that count, and so this value, is not
/// determined.
fn replace_all(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.replaceAll", arguments, 3)?;
    if let Some(unspecified) = empty_needle("replaceAll", &arguments[1]) {
        return Ok(unspecified);
    }
    let (Some(haystack), Some(needle), Some(replacement)) = (
        read_string(&arguments[0]),
        read_string(&arguments[1]),
        read_string(&arguments[2]),
    ) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(string_term(
        haystack.replace(needle, replacement),
    )))
}

/// `Unspecified` when `needle` is the empty string, whose occurrences `domains.md`'s counting
/// equations do not determine.
fn empty_needle(operation: &str, needle: &Term) -> Option<BuiltinResult> {
    read_string(needle).is_some_and(str::is_empty).then(|| {
        BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified {
            detail: format!(
                "{operation} with an empty needle: the domains.md equations give count = 1 + count"
            ),
        })
    })
}

/// `findString(S, N, I)` is the first occurrence of N in S starting at or after code point I,
/// and `rfindString(S, N, I)` the last starting at or before it, -1 when there is none; both are
/// defined for every integer I (`domains.md`: "starting at a certain index"). A negative I
/// searches `find` from 0 and leaves `rfind` nothing; an I past the end leaves `find` nothing
/// and searches `rfind` from the end.
fn find(arguments: &[Term], reverse: bool) -> HookResult<BuiltinResult> {
    let hook = if reverse {
        "STRING.rfind"
    } else {
        "STRING.find"
    };
    expect_arity(hook, arguments, 3)?;
    let Some((haystack, needle)) = read_string(&arguments[0]).zip(read_string(&arguments[1]))
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(start) = read_int(&arguments[2]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if reverse && start.sign() == Sign::Minus {
        return Ok(BuiltinResult::Value(int_term(BigInt::from(-1))));
    }
    let start = saturating_i64(&start);
    let start = usize::try_from(start.max(0)).unwrap_or(usize::MAX);
    // `starts[unit]` is the byte offset at which code point `unit` starts, the end of the
    // haystack after the last. The UTF-8 of the needle occurring at the start of a code point
    // ends on the end of one, since no code point's encoding starts inside another's.
    let mut starts = code_point_offsets(haystack).collect::<Vec<_>>();
    let units = starts.len();
    starts.push(haystack.len());
    let occurs_at = |unit: usize| haystack[starts[unit]..].starts_with(needle);
    let candidates: Box<dyn Iterator<Item = usize>> = if reverse {
        Box::new((0..=start.min(units)).rev())
    } else {
        Box::new(start.min(units + 1)..=units)
    };
    let mut found = None;
    for (step, unit) in candidates.enumerate() {
        if step % 1024 == 0 {
            crate::stop::check()?;
        }
        if occurs_at(unit) {
            found = Some(unit);
            break;
        }
    }
    Ok(BuiltinResult::Value(int_term(BigInt::from(
        found
            .and_then(|index| i64::try_from(index).ok())
            .unwrap_or(-1),
    ))))
}

/// Byte offsets at which the code points of a `String` value, stored as UTF-8, start.
fn code_point_offsets(value: &str) -> impl Iterator<Item = usize> + '_ {
    value.char_indices().map(|(offset, _)| offset)
}

fn string_to_base(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.string2base", arguments, 2)?;
    let Some(value) = read_string(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(base) = read_int(&arguments[1]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(base) = read_base(&base) else {
        return Ok(BuiltinResult::Bottom);
    };
    Ok(parse_integer(value, base)
        .map(int_term)
        .map_or(BuiltinResult::Bottom, BuiltinResult::Value))
}

/// An optional sign followed by one or more digits of `radix`, in either case. The integer
/// parser alone would also skip `_` separators, which are not digits.
fn parse_integer(value: &str, radix: u32) -> Option<BigInt> {
    let digits = value.strip_prefix(['+', '-']).unwrap_or(value);
    let well_formed =
        !digits.is_empty() && digits.chars().all(|character| character.is_digit(radix));
    well_formed
        .then(|| BigInt::parse_bytes(value.as_bytes(), radix))
        .flatten()
}

fn base_to_string(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.base2string", arguments, 2)?;
    let Some(value) = read_int(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(base) = read_int(&arguments[1]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(base) = read_base(&base) else {
        return Ok(BuiltinResult::Bottom);
    };
    Ok(BuiltinResult::Value(string_term(value.to_str_radix(base))))
}

fn string_to_int(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.string2int", arguments, 1)?;
    let Some(value) = read_string(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(parse_integer(value, 10)
        .map(int_term)
        .map_or(BuiltinResult::Bottom, BuiltinResult::Value))
}

fn int_to_string(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.int2string", arguments, 1)?;
    let Some(value) = read_int(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(string_term(value.to_string())))
}

/// `chrChar(N)` is the string of the one code point N. A number outside the code points
/// `[0, 0x10FFFF]` is no character, so `chrChar` of one has no value: it is undefined (the hook
/// is partial).
///
/// A surrogate code point (U+D800 to U+DFFF) is left `Unspecified`: K's string syntax writes one
/// (`\uFFFF` is "a code point between 0x0000 and 0xffff"), and KORE's string literals, in which
/// every `String` domain value is written, cannot. The definition does not settle whether a
/// String holds one, so neither a value nor `\bottom` follows from it; the unevaluated
/// application denotes whichever it is.
fn chr(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.chr", arguments, 1)?;
    // A symbolic code point may be valid on some instances and invalid on others.
    let Some(value) = read_int(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(value) = value.to_u32().filter(|value| *value <= 0x10ffff) else {
        return Ok(BuiltinResult::Bottom);
    };
    Ok(char::from_u32(value).map_or_else(
        || {
            BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified {
                detail: format!(
                    "chrChar({value}): a surrogate code point, which K's string syntax writes \
                     and KORE's string literals cannot"
                ),
            })
        },
        |value| BuiltinResult::Value(string_term(value.to_string())),
    ))
}

/// `ordChar(S)` is the number of the one code point of S, undefined for any other length.
fn ord(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.ord", arguments, 1)?;
    let Some(value) = read_string(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let mut characters = value.chars();
    let (Some(character), None) = (characters.next(), characters.next()) else {
        return Ok(BuiltinResult::Bottom);
    };
    Ok(BuiltinResult::Value(int_term(BigInt::from(u32::from(
        character,
    )))))
}

/// The token's code points as a `String`. A `Bytes` payload holds one byte per code point, every
/// other payload their UTF-8 (`kore::string::LiteralEncoding`).
fn token_to_string(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.token2string", arguments, 1)?;
    let TermKind::DomainValue { sort, value } = arguments[0].kind() else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let value = if sort.is_builtin(BuiltinSort::Bytes) {
        KoreString::from(
            value
                .as_bytes()
                .iter()
                .map(|byte| char::from(*byte))
                .collect::<String>(),
        )
    } else {
        value.clone()
    };
    Ok(BuiltinResult::Value(Term::domain_value_of(
        DomainKind::String,
        Sort::builtin(BuiltinSort::String),
        value,
    )))
}

/// `String2Token(S)` (`STRING.string2token`, declared at the result sort of its application) is
/// the domain value of that sort whose text is the code points of `S`, read as the definition
/// reads a literal of the sort: with the kind the sort's hook gives
/// ([`BackendDefinition::domain_kind`]), validated and stored in the kind's canonical text, so
/// that `"07"` at a sort hooked `INT.Int` is the integer 7. The payload is stored in the encoding
/// of the sort's KORE name, as every KORE reader stores it (`LiteralEncoding::of_domain_value`).
///
/// A text that names no element of the sort has no value the definition gives: the application
/// of a `total` declaration has a value the definition does not determine (`Unspecified`), and
/// that of a partial one is undefined (`\bottom`). A text that names an element whose canonical
/// text is beyond a bound of k-rust is the resource refusal whatever the declaration's
/// totality, never `\bottom`. Without a definition, or at a sort without domain values, the
/// result sort has no kind, and the application is not evaluated.
fn string_to_token(arguments: &[Term], declaration: Declaration<'_>) -> HookResult<BuiltinResult> {
    expect_arity("STRING.string2token", arguments, 1)?;
    let Some(text) = read_string(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let (Some(result_sort), Some(definition)) = (declaration.result_sort, declaration.definition)
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let names_no_element = || {
        Ok(if declaration.total {
            BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified {
                detail: format!(
                    "String2Token of {}: the text names no element of {}",
                    described_text(text),
                    externalize::sort(result_sort)
                ),
            })
        } else {
            BuiltinResult::Bottom
        })
    };
    let Some(kind) = definition.domain_kind(result_sort) else {
        // Only a sort hooked `MINT.MInt` that names no width has domain values and no kind; no
        // text is a literal of it.
        let admits_domain_values = matches!(result_sort, Sort::Application { name, .. }
            if definition.sorts().get(name).is_some_and(|info| info.has_domain_values));
        return if admits_domain_values {
            names_no_element()
        } else {
            Ok(BuiltinResult::NotApplicable)
        };
    };
    let encoding = if result_sort.is_builtin(BuiltinSort::Bytes) {
        LiteralEncoding::Bytes
    } else {
        LiteralEncoding::Utf8
    };
    // A code point above U+00FF has no byte of `SortBytes`'s payload, as in a literal.
    let Some(value) = encoding.store(text) else {
        return names_no_element();
    };
    match validate_text(kind, result_sort, &value) {
        Ok(()) => Ok(BuiltinResult::Value(Term::domain_value_of(
            kind,
            result_sort.clone(),
            value,
        ))),
        Err(TextRejection::NamesNoElement(_)) => names_no_element(),
        Err(TextRejection::BeyondBound) => Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::ResultTooLarge {
                detail: format!(
                    "String2Token of {}: the canonical text of the value it names at {} is \
                     beyond the bound on the integers the backend computes",
                    described_text(text),
                    externalize::sort(result_sort)
                ),
            },
        )),
    }
}

/// A string operand as a message shows it: quoted when it is short, otherwise by its length.
fn described_text(text: &str) -> String {
    if text.len() <= 64 {
        format!("{text:?}")
    } else {
        format!("a string of {} bytes", text.len())
    }
}

/// The radix of `String2Base` and `Base2String`. `domains.md` says it "can be anywhere between 2
/// and 36" and gives the digits of exactly those radixes; both hooks are partial, so outside that
/// range there is no conversion the definition describes, and the application is undefined.
fn read_base(base: &BigInt) -> Option<u32> {
    base.to_u32().filter(|base| (2..=36).contains(base))
}

fn saturating_i64(value: &BigInt) -> i64 {
    value.to_i64().unwrap_or_else(|| {
        if value.sign() == Sign::Minus {
            i64::MIN
        } else {
            i64::MAX
        }
    })
}

/// A `String` domain value's code points, stored as UTF-8 (`kore::string::LiteralEncoding`).
/// Every reader stores them so; a payload built otherwise is not a `String` value these hooks
/// evaluate.
pub(super) fn read_string(term: &Term) -> Option<&str> {
    let TermKind::DomainValue { sort, value } = term.kind() else {
        return None;
    };
    sort.is_builtin(BuiltinSort::String)
        .then(|| value.as_utf8().ok())
        .flatten()
}

fn string_term(value: impl AsRef<str>) -> Term {
    Term::string(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn evaluate(hook: &str, arguments: Vec<Term>) -> BuiltinResult {
        super::evaluate(hook, &arguments, declared(None)).unwrap()
    }

    /// An application declared at `result_sort`, outside any definition, not `total`.
    fn declared(result_sort: Option<&Sort>) -> Declaration<'_> {
        Declaration {
            result_sort,
            definition: None,
            total: false,
        }
    }

    /// A `SortString` domain value holding `payload` as given, UTF-8 or not.
    fn string_payload(payload: Vec<u8>) -> Term {
        Term::raw_domain_value(Sort::builtin(BuiltinSort::String), payload)
    }

    #[test]
    fn evaluates_string_operations_by_code_point() {
        assert_eq!(
            evaluate("STRING.length", vec![string_term("a🦀é")]),
            BuiltinResult::Value(int_term(BigInt::from(3)))
        );
        assert_eq!(
            evaluate(
                "STRING.substr",
                vec![string_term("a🦀é"), int_term(1.into()), int_term(2.into())]
            ),
            BuiltinResult::Value(string_term("🦀"))
        );
        assert_eq!(
            evaluate(
                "STRING.find",
                vec![string_term("a🦀é🦀"), string_term("🦀"), int_term(2.into())]
            ),
            BuiltinResult::Value(int_term(BigInt::from(3)))
        );
    }

    /// `countAllOccurrences` and `replaceAll` take the occurrences found from the left, each
    /// search after the previous match; with an empty needle the `domains.md` equations give
    /// `count = 1 + count`, so neither value is determined, whatever the haystack.
    #[test]
    fn count_and_replace_all_take_leftmost_disjoint_matches_and_no_empty_needle() {
        let count = |haystack: Term, needle: &str| {
            evaluate(
                "STRING.countAllOccurrences",
                vec![haystack, string_term(needle)],
            )
        };
        let replace_all = |haystack: Term, needle: &str, replacement: &str| {
            evaluate(
                "STRING.replaceAll",
                vec![haystack, string_term(needle), string_term(replacement)],
            )
        };
        for (haystack, needle, occurrences, replaced) in [
            ("abab", "ab", 2, "xx"),
            ("aaa", "aa", 1, "xa"),
            ("a🦀é🦀", "🦀", 2, "axéx"),
            ("abc", "d", 0, "abc"),
            ("", "a", 0, ""),
        ] {
            assert_eq!(
                count(string_term(haystack), needle),
                BuiltinResult::Value(int_term(BigInt::from(occurrences))),
                "countAllOccurrences({haystack:?}, {needle:?})"
            );
            assert_eq!(
                replace_all(string_term(haystack), needle, "x"),
                BuiltinResult::Value(string_term(replaced)),
                "replaceAll({haystack:?}, {needle:?}, \"x\")"
            );
        }
        let symbolic = Term::variable(crate::term::Variable::new(
            "S",
            Sort::builtin(BuiltinSort::String),
        ));
        for haystack in [string_term("ab"), string_term(""), symbolic.clone()] {
            assert!(
                matches!(
                    count(haystack.clone(), ""),
                    BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified { .. })
                ),
                "countAllOccurrences({haystack:?}, \"\")"
            );
            assert!(
                matches!(
                    replace_all(haystack.clone(), "", "x"),
                    BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified { .. })
                ),
                "replaceAll({haystack:?}, \"\", \"x\")"
            );
        }
        assert_eq!(count(symbolic, "a"), BuiltinResult::NotApplicable);
    }

    #[test]
    fn a_character_is_one_code_point_long() {
        for code_point in [233, 0xd7ff, 0xe000, 0x1f980] {
            let BuiltinResult::Value(character) =
                evaluate("STRING.chr", vec![int_term(code_point.into())])
            else {
                panic!("chrChar({code_point}) is defined");
            };
            assert_eq!(
                evaluate("STRING.length", vec![character]),
                BuiltinResult::Value(int_term(BigInt::from(1))),
                "lengthString(chrChar({code_point}))"
            );
        }
    }

    #[test]
    fn find_matches_whole_code_points_only() {
        // U+00C3, the code point whose number is the first byte of the UTF-8 of "é", does not
        // occur in "é" (U+00E9).
        assert_eq!(
            evaluate(
                "STRING.find",
                vec![string_term("é"), string_term("\u{c3}"), int_term(0.into())]
            ),
            BuiltinResult::Value(int_term(BigInt::from(-1)))
        );
        assert_eq!(
            evaluate(
                "STRING.find",
                vec![
                    string_term("\u{c3}x\u{c3}"),
                    string_term("\u{c3}"),
                    int_term(1.into())
                ]
            ),
            BuiltinResult::Value(int_term(BigInt::from(2)))
        );
        assert_eq!(
            evaluate(
                "STRING.find",
                vec![string_term("aé"), string_term(""), int_term(2.into())]
            ),
            BuiltinResult::Value(int_term(BigInt::from(2)))
        );
        assert_eq!(
            evaluate(
                "STRING.find",
                vec![string_term("aé"), string_term(""), int_term(3.into())]
            ),
            BuiltinResult::Value(int_term(BigInt::from(-1)))
        );
    }

    #[test]
    /// The code points up to U+00FF, the ones a `\xNN` escape writes, are characters like any
    /// other, a NUL included, and order by their numbers.
    fn string_operations_take_every_code_point_up_to_255() {
        let low = || string_term("\u{ff}\u{80}\u{0}A");
        assert_eq!(
            evaluate("STRING.length", vec![low()]),
            BuiltinResult::Value(int_term(BigInt::from(4)))
        );
        assert_eq!(
            evaluate(
                "STRING.substr",
                vec![low(), int_term(1.into()), int_term(3.into())]
            ),
            BuiltinResult::Value(string_term("\u{80}\u{0}"))
        );
        assert_eq!(
            evaluate(
                "STRING.find",
                vec![low(), string_term("\u{80}\u{0}"), int_term(0.into())]
            ),
            BuiltinResult::Value(int_term(BigInt::from(1)))
        );
        assert_eq!(
            evaluate(
                "STRING.concat",
                vec![string_term("\u{ff}"), string_term("\u{80}\u{0}")]
            ),
            BuiltinResult::Value(string_term("\u{ff}\u{80}\u{0}"))
        );
        assert_eq!(
            evaluate("STRING.eq", vec![low(), low()]),
            BuiltinResult::Value(bool_term(true))
        );
        for (left, right) in [("\u{80}", "\u{ff}"), ("\u{ff}", "\u{100}"), ("é", "€")] {
            assert_eq!(
                evaluate("STRING.lt", vec![string_term(left), string_term(right)]),
                BuiltinResult::Value(bool_term(true)),
                "{left:?} <String {right:?}"
            );
        }
    }

    /// A payload that is not UTF-8 is not how any reader stores a `String` value, so the hooks do
    /// not evaluate it.
    #[test]
    fn a_payload_that_is_not_utf8_is_no_string_value() {
        let stray = || string_payload(vec![0xff, 0x80, 0x00, b'A']);
        for (hook, arguments) in [
            ("STRING.length", vec![stray()]),
            ("STRING.ord", vec![string_payload(vec![0xe9])]),
            ("STRING.eq", vec![stray(), stray()]),
            ("STRING.concat", vec![stray(), string_term("a")]),
        ] {
            assert_eq!(
                evaluate(hook, arguments),
                BuiltinResult::NotApplicable,
                "{hook}"
            );
        }
    }

    #[test]
    fn converts_strings_in_decimal_and_explicit_bases() {
        assert_eq!(
            evaluate("STRING.string2int", vec![string_term("-42")]),
            BuiltinResult::Value(int_term(BigInt::from(-42)))
        );
        assert_eq!(
            evaluate(
                "STRING.string2base",
                vec![string_term("-ff"), int_term(16.into())]
            ),
            BuiltinResult::Value(int_term(BigInt::from(-255)))
        );
        assert_eq!(
            evaluate(
                "STRING.base2string",
                vec![int_term((-255).into()), int_term(16.into())]
            ),
            BuiltinResult::Value(string_term("-ff"))
        );
        assert_eq!(
            evaluate("STRING.string2int", vec![string_term("4x")]),
            BuiltinResult::Bottom
        );
    }

    #[test]
    fn converts_unicode_scalar_values() {
        assert_eq!(
            evaluate("STRING.chr", vec![int_term(0x1f980.into())]),
            BuiltinResult::Value(string_term("🦀"))
        );
        assert_eq!(
            evaluate("STRING.ord", vec![string_term("🦀")]),
            BuiltinResult::Value(int_term(BigInt::from(0x1f980)))
        );
        assert_eq!(
            evaluate("STRING.ord", vec![string_term("ab")]),
            BuiltinResult::Bottom
        );
    }

    /// `substrString` has its value on `0 <= start <= end <= length`, including empty ranges, and
    /// a value the definition leaves open elsewhere, so it is left unevaluated there.
    #[test]
    fn substr_is_unspecified_outside_valid_indices() {
        for (start, end, expected) in [(0, 0, ""), (5, 5, ""), (1, 3, "el"), (0, 5, "hello")] {
            assert_eq!(
                evaluate(
                    "STRING.substr",
                    vec![
                        string_term("hello"),
                        int_term(start.into()),
                        int_term(end.into())
                    ],
                ),
                BuiltinResult::Value(string_term(expected)),
                "substrString(hello, {start}, {end})"
            );
        }
        let beyond_i64: BigInt = BigInt::from(1_u8) << 100;
        for (start, end) in [
            (BigInt::from(-2), BigInt::from(3)),
            (BigInt::from(1), BigInt::from(10)),
            (BigInt::from(3), BigInt::from(1)),
            (BigInt::from(-3), BigInt::from(-1)),
            (BigInt::from(6), BigInt::from(6)),
            (-&beyond_i64, beyond_i64.clone()),
            (beyond_i64.clone(), beyond_i64.clone()),
        ] {
            assert!(
                matches!(
                    evaluate(
                        "STRING.substr",
                        vec![
                            string_term("hello"),
                            int_term(start.clone()),
                            int_term(end.clone())
                        ],
                    ),
                    BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified { .. })
                ),
                "substrString(hello, {start}, {end})"
            );
        }
    }

    /// A number outside the code points is no character, so `chrChar` of one is undefined.
    /// Whether a String holds a surrogate code point the definition does not settle (K's string
    /// syntax writes one, KORE's literals cannot), so `chrChar` of one stays unevaluated as
    /// `Unspecified`. `ordChar(chrChar(N)) == N` wherever `chrChar(N)` is computed.
    #[test]
    fn chr_of_a_surrogate_is_unspecified_and_of_a_non_code_point_undefined() {
        for code_point in [0xd800, 0xdbff, 0xdc00, 0xdfff] {
            assert!(
                matches!(
                    evaluate("STRING.chr", vec![int_term(code_point.into())]),
                    BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified { .. })
                ),
                "chrChar({code_point})"
            );
        }
        for code_point in [0, 0xd7ff, 0xe000, 0x10ffff] {
            let BuiltinResult::Value(character) =
                evaluate("STRING.chr", vec![int_term(code_point.into())])
            else {
                panic!("chrChar({code_point}) is defined");
            };
            assert_eq!(
                evaluate("STRING.ord", vec![character]),
                BuiltinResult::Value(int_term(code_point.into())),
                "ordChar(chrChar({code_point}))"
            );
        }
        assert_eq!(
            evaluate("STRING.chr", vec![int_term((-1).into())]),
            BuiltinResult::Bottom
        );
        assert_eq!(
            evaluate("STRING.chr", vec![int_term(0x110000.into())]),
            BuiltinResult::Bottom
        );
        assert_eq!(
            evaluate("STRING.chr", vec![int_term(0x1f980.into())]),
            BuiltinResult::Value(string_term("🦀"))
        );
    }

    /// The code point a `\xNN` escape writes is U+00NN, whose number is the escape's; a string
    /// of more or fewer than one code point has no `ordChar`.
    #[test]
    fn ord_of_an_escaped_code_point_is_its_value() {
        for (literal, expected) in [(r#""\xe9""#, 233), (r#""\x80""#, 128), (r#""\xff""#, 255)] {
            let value = k_rust_kore::kore::string::unquote(literal).unwrap();
            assert_eq!(
                evaluate("STRING.ord", vec![string_term(value.as_utf8().unwrap())]),
                BuiltinResult::Value(int_term(BigInt::from(expected))),
                "ordChar({literal})"
            );
        }
        assert_eq!(
            evaluate("STRING.ord", vec![string_term("é")]),
            BuiltinResult::Value(int_term(BigInt::from(233)))
        );
        for text in ["\u{ff}\u{fe}", "\u{ff}a", ""] {
            assert_eq!(
                evaluate("STRING.ord", vec![string_term(text)]),
                BuiltinResult::Bottom,
                "ordChar({text:?})"
            );
        }
    }

    /// `Id2String` (`STRING.token2string`) reads a token's text back as a `String`. Without a
    /// definition the result sort of `String2Id` (`STRING.string2token`) has no kind, so the
    /// application is not decided, nor on a string the hook cannot read; with one, the token is
    /// built by the kind of its sort (`tests::domain_values` of the crate).
    #[test]
    fn token2string_reads_a_token_and_string2token_needs_a_definition() {
        let id = Sort::simple("SortId");
        for text in ["x", "_42"] {
            assert_eq!(
                evaluate(
                    "STRING.token2string",
                    vec![Term::raw_domain_value(id.clone(), text)]
                ),
                BuiltinResult::Value(string_term(text)),
                "Id2String({text:?})"
            );
            assert_eq!(
                super::evaluate(
                    "STRING.string2token",
                    &[string_term(text)],
                    declared(Some(&id))
                )
                .unwrap(),
                BuiltinResult::NotApplicable,
                "String2Id({text:?}) without a definition"
            );
        }
        assert_eq!(
            evaluate("STRING.string2token", vec![string_term("x")]),
            BuiltinResult::NotApplicable
        );
        let symbolic = Term::variable(crate::term::Variable::new(
            "S",
            Sort::builtin(BuiltinSort::String),
        ));
        assert_eq!(
            super::evaluate("STRING.string2token", &[symbolic], declared(Some(&id))).unwrap(),
            BuiltinResult::NotApplicable
        );
    }

    /// A symbolic code point may be valid on some instances, so `chrChar` of it is not decided.
    #[test]
    fn chr_of_a_symbolic_code_point_is_undecided() {
        let code_point = Term::variable(crate::term::Variable::new(
            "C",
            Sort::builtin(BuiltinSort::Int),
        ));
        assert_eq!(
            evaluate("STRING.chr", vec![code_point]),
            BuiltinResult::NotApplicable
        );
    }

    /// `findString` is the first occurrence starting at or after its index, whatever the index:
    /// a negative one searches from 0, one past the end finds nothing.
    #[test]
    fn find_searches_forward_from_any_index() {
        for (needle, start, expected) in [
            ("l", 1, 2),
            ("l", 3, 3),
            ("", 5, 5),
            ("", 6, -1),
            ("l", -5, 2),
            ("", -1, 0),
        ] {
            assert_eq!(
                evaluate(
                    "STRING.find",
                    vec![
                        string_term("hello"),
                        string_term(needle),
                        int_term(start.into()),
                    ],
                ),
                BuiltinResult::Value(int_term(expected.into())),
                "findString(hello, {needle:?}, {start})"
            );
        }

        let beyond_i64: BigInt = BigInt::from(1_u8) << 100;
        assert_eq!(
            evaluate(
                "STRING.find",
                vec![
                    string_term("hello"),
                    string_term("h"),
                    int_term(-&beyond_i64),
                ],
            ),
            BuiltinResult::Value(int_term(BigInt::from(0)))
        );
        assert_eq!(
            evaluate(
                "STRING.find",
                vec![string_term("hello"), string_term("h"), int_term(beyond_i64),],
            ),
            BuiltinResult::Value(int_term(BigInt::from(-1)))
        );
    }

    /// `rfindString` is the last occurrence starting at or before its index, whatever the index:
    /// none for a negative one, the last in the string for one past the end.
    #[test]
    fn rfind_searches_back_from_any_index() {
        let beyond_i64: BigInt = BigInt::from(1_u8) << 100;
        for (haystack, needle, start, expected) in [
            ("hello", "l", BigInt::from(4), 3),
            ("hello", "l", BigInt::from(2), 2),
            ("hello", "l", BigInt::from(1), -1),
            ("hello", "l", BigInt::from(100), 3),
            ("hello", "l", beyond_i64.clone(), 3),
            ("hello", "", BigInt::from(3), 3),
            ("hello", "", beyond_i64.clone(), 5),
            ("hello", "h", BigInt::from(-1), -1),
            ("hello", "", -beyond_i64.clone(), -1),
            ("a🦀é🦀", "🦀", BigInt::from(2), 1),
            ("a🦀é🦀", "🦀", BigInt::from(3), 3),
            ("", "", BigInt::from(0), 0),
        ] {
            assert_eq!(
                evaluate(
                    "STRING.rfind",
                    vec![
                        string_term(haystack),
                        string_term(needle),
                        int_term(start.clone())
                    ],
                ),
                BuiltinResult::Value(int_term(expected.into())),
                "rfindString({haystack:?}, {needle:?}, {start})"
            );
        }
        // U+00C3, the code point numbered like the first byte of the UTF-8 of "é", does not
        // occur in "é".
        assert_eq!(
            evaluate(
                "STRING.rfind",
                vec![string_term("é"), string_term("\u{c3}"), int_term(1.into())]
            ),
            BuiltinResult::Value(int_term(BigInt::from(-1)))
        );
    }

    /// The radix "can be anywhere between 2 and 36" (`domains.md`), and both hooks are partial:
    /// outside that range the conversion is undefined, in both directions.
    #[test]
    fn bases_outside_two_through_thirty_six_are_undefined() {
        for (hook, value) in [
            ("STRING.string2base", string_term("11")),
            ("STRING.base2string", int_term(255.into())),
        ] {
            for base in [-2_i64, 0, 1, 37, 1 << 40] {
                assert_eq!(
                    evaluate(hook, vec![value.clone(), int_term(base.into())]),
                    BuiltinResult::Bottom,
                    "{hook} base {base}"
                );
            }
            for base in [2, 36] {
                assert!(
                    matches!(
                        evaluate(hook, vec![value.clone(), int_term(base.into())]),
                        BuiltinResult::Value(_)
                    ),
                    "{hook} base {base}"
                );
            }
        }
    }

    /// `String2Int` reads an optional sign and decimal digits, and `String2Base` the digits of
    /// its base in either case; a `_` separator is neither, so such strings are undefined.
    #[test]
    fn integer_conversions_accept_only_signed_digits() {
        let to_int = |text: &str| evaluate("STRING.string2int", vec![string_term(text)]);
        let to_base = |text: &str, base: i64| {
            evaluate(
                "STRING.string2base",
                vec![string_term(text), int_term(base.into())],
            )
        };
        assert_eq!(to_int("+15"), BuiltinResult::Value(int_term(15.into())));
        assert_eq!(to_int("-007"), BuiltinResult::Value(int_term((-7).into())));
        assert_eq!(
            to_base("fF", 16),
            BuiltinResult::Value(int_term(255.into()))
        );
        for text in ["1_0", "1_", "_1", "-_1", "", "+", "-", "+-1", " 1", "1e3"] {
            assert_eq!(to_int(text), BuiltinResult::Bottom, "{text:?}");
        }
        assert_eq!(to_base("f_f", 16), BuiltinResult::Bottom);
        assert_eq!(to_base("12", 2), BuiltinResult::Bottom);
        // A radix numeral carries the sign of `String2Int`'s syntax, so that `String2Base` reads
        // back every `Base2String`, negative ones included.
        assert_eq!(
            to_base("+fF", 16),
            BuiltinResult::Value(int_term(255.into()))
        );
        assert_eq!(
            to_base("-z", 36),
            BuiltinResult::Value(int_term((-35).into()))
        );
        for text in ["+", "-", "+-1", "--1", "1-"] {
            assert_eq!(to_base(text, 16), BuiltinResult::Bottom, "{text:?}");
        }
    }
}
