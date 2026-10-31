//! The texts of domain values: which payloads are values of a kind at a sort
//! ([`validate_text`]), and the canonical text of the element a payload names
//! ([`canonical_text`]), so that equal elements of one sort have one text.

use num_bigint::{BigInt, BigUint};

use crate::float::{
    FloatTextRefusal, MAX_FLOAT_CANONICAL_BITS, canonical_float_text, float_canonical_bits_estimate,
};
use crate::kind::{BYTES_SORT, DomainKind, DomainSort, MIntWidth, is_nullary, mint_width_digits};

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

/// Why a domain value names no element of its sort.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InvalidDomainValueReason {
    /// The text is not in the literal syntax of the sort's hook.
    NotALiteral,
    /// A machine-integer literal whose suffix names another width than its sort's.
    OtherWidth,
    /// A sort hooked `MINT.MInt` that is not `SortMInt` applied to a numeral sort, so that it
    /// has no width and no text is a literal of it.
    NoWidth,
    /// A Float literal whose precision or exponent-bits field is 0, which names no format.
    NoFloatFormat,
}

/// The bound of k-rust that a domain value is beyond: its text names an element of its sort
/// whose canonical text k-rust declines to build.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DomainValueBound {
    /// A negative literal of a machine-integer sort wider than `limit_bits`
    /// (`MAX_INT_RESULT_BITS`), whose residue modulo `2^W` would be a decimal of about `W` bits.
    MIntResidue { limit_bits: u64 },
    /// A Float literal whose canonical text (the exact decimal of the value it rounds to), or
    /// the exact arithmetic that finds it, is estimated at `estimate_bits`, more than
    /// `limit_bits` (`MAX_FLOAT_CANONICAL_BITS`).
    FloatCanonicalText { limit_bits: u64, estimate_bits: u64 },
    /// A Float literal of a format whose precision or exponent-bits field is 1, which has no
    /// IEEE-like parameters and which k-rust does not compute.
    FloatFormat,
}

/// Why a text is no domain value of a kind at a sort.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TextRejection {
    /// The text names no element of the sort: it is outside the kind's literal syntax, a
    /// machine-integer suffix names another width or the sort names none, or a `Bytes` code
    /// point is above U+00FF.
    NamesNoElement(InvalidDomainValueReason),
    /// The text names an element whose canonical text k-rust declines to compute: a negative
    /// machine-integer literal of a width beyond `MAX_INT_RESULT_BITS`, a Float literal of a
    /// format with a field of 1, or one whose canonical text is beyond
    /// `MAX_FLOAT_CANONICAL_BITS`.
    BeyondBound(DomainValueBound),
}

/// Whether the payload `value` is a domain value of `kind` at `sort`: the validator every
/// construction route with a text from outside the backend applies before building the value
/// (definition load and requests, `STRING.string2token`), and [`crate::token_value`].
///
/// - `Int`: a decimal integer, with an optional sign.
/// - `Bool`: `true` or `false`.
/// - `MInt(W)`: a literal `[+-]?[0-9]+[pP][0-9]+` whose suffix names the sort's width; a sort
///   that names no width has no literal.
/// - `Bytes`: any payload at `SortBytes`, whose payload is one byte per code point; elsewhere the
///   UTF-8 of code points each at most U+00FF, since a larger code point names no byte.
/// - `Float`: a text in FLOAT-SYNTAX whose suffix names a format (no field of 0). A format with a
///   field of 1, which k-rust does not compute, and a literal whose canonical text is estimated
///   beyond `MAX_FLOAT_CANONICAL_BITS` name values k-rust declines to build.
/// - `String` and `Token`: every text.
pub fn validate_text<S: DomainSort>(
    kind: DomainKind,
    sort: &S,
    value: &[u8],
) -> Result<(), TextRejection> {
    let text = std::str::from_utf8(value).ok();
    let no_element = |reason| Err(TextRejection::NamesNoElement(reason));
    match kind {
        DomainKind::Int if !text.is_some_and(is_decimal_integer) => {
            no_element(InvalidDomainValueReason::NotALiteral)
        }
        DomainKind::Bool if !matches!(text, Some("true" | "false")) => {
            no_element(InvalidDomainValueReason::NotALiteral)
        }
        DomainKind::MInt(width) => {
            let digits = match (width, mint_width_digits(sort)) {
                (MIntWidth::Bits(_) | MIntWidth::Unrepresentable, Some(digits)) => digits,
                _ => return no_element(InvalidDomainValueReason::NoWidth),
            };
            let Some(literal) = text.and_then(MIntLiteral::parse) else {
                return no_element(InvalidDomainValueReason::NotALiteral);
            };
            if !literal.names_width(digits) {
                return no_element(InvalidDomainValueReason::OtherWidth);
            }
            if literal.is_negative() && mint_width_beyond_bound(width) {
                return Err(TextRejection::BeyondBound(DomainValueBound::MIntResidue {
                    limit_bits: MAX_INT_RESULT_BITS,
                }));
            }
            Ok(())
        }
        DomainKind::Float => match text.map(float_canonical_bits_estimate) {
            Some(Ok(_)) => Ok(()),
            None | Some(Err(FloatTextRefusal::NotALiteral)) => {
                no_element(InvalidDomainValueReason::NotALiteral)
            }
            Some(Err(FloatTextRefusal::ZeroFormatField)) => {
                no_element(InvalidDomainValueReason::NoFloatFormat)
            }
            Some(Err(FloatTextRefusal::UncomputedFormat)) => {
                Err(TextRejection::BeyondBound(DomainValueBound::FloatFormat))
            }
            Some(Err(FloatTextRefusal::BeyondBound { estimate_bits })) => Err(
                TextRejection::BeyondBound(DomainValueBound::FloatCanonicalText {
                    limit_bits: MAX_FLOAT_CANONICAL_BITS,
                    estimate_bits,
                }),
            ),
        },
        DomainKind::Bytes
            if !is_nullary(sort, BYTES_SORT)
                && !text
                    .is_some_and(|text| text.chars().all(|character| character <= '\u{ff}')) =>
        {
            no_element(InvalidDomainValueReason::NotALiteral)
        }
        DomainKind::Int
        | DomainKind::Bool
        | DomainKind::Bytes
        | DomainKind::String
        | DomainKind::Token => Ok(()),
    }
}

/// A decimal integer with an optional sign, the literal syntax of `INT.Int`.
fn is_decimal_integer(value: &str) -> bool {
    let digits = value.strip_prefix(['+', '-']).unwrap_or(value).as_bytes();
    !digits.is_empty() && digits.iter().all(u8::is_ascii_digit)
}

/// A machine-integer literal `[+-]?[0-9]+[pP][0-9]+` (`domains.md`, `MINT.literal`): a signed
/// decimal integer and the decimal digits of a width.
#[derive(Clone, Copy, Debug)]
struct MIntLiteral<'a> {
    sign: Option<u8>,
    magnitude: &'a str,
    separator: u8,
    width: &'a str,
}

impl<'a> MIntLiteral<'a> {
    fn parse(text: &'a str) -> Option<Self> {
        let (sign, rest) = match text.as_bytes().first() {
            Some(&sign @ (b'+' | b'-')) => (Some(sign), &text[1..]),
            _ => (None, text),
        };
        let (magnitude, tail) = rest.split_at(rest.find(['p', 'P'])?);
        let width = &tail[1..];
        let digits =
            |part: &str| !part.is_empty() && part.bytes().all(|byte| byte.is_ascii_digit());
        (digits(magnitude) && digits(width)).then_some(Self {
            sign,
            magnitude,
            separator: tail.as_bytes()[0],
            width,
        })
    }

    /// True when the literal's suffix names the width `digits` name, leading zeros aside.
    fn names_width(&self, digits: &str) -> bool {
        self.width.trim_start_matches('0') == digits.trim_start_matches('0')
    }

    /// True for a negative literal other than a zero: its residue is `2^W` minus its
    /// magnitude's, a number of about `W` bits whatever the length of the literal.
    fn is_negative(&self) -> bool {
        self.sign == Some(b'-') && self.magnitude.bytes().any(|byte| byte != b'0')
    }
}

/// True when a negative literal of a machine-integer sort of `width` is refused by the bound on
/// the integers the backend computes: its residue would be a decimal of about `width` bits.
fn mint_width_beyond_bound(width: MIntWidth) -> bool {
    match width {
        MIntWidth::Bits(bits) => bits > MAX_INT_RESULT_BITS,
        MIntWidth::Unrepresentable => true,
        MIntWidth::NoWidth => false,
    }
}

#[cfg(any(test, feature = "measure"))]
thread_local! {
    /// The machine-integer literals whose decimal magnitude this thread's canonicalizer parsed.
    static MINT_TEXT_PARSES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The machine-integer literals whose decimal magnitude this thread's canonicalizer has parsed.
#[cfg(any(test, feature = "measure"))]
pub fn mint_text_parses() -> usize {
    MINT_TEXT_PARSES.get()
}

/// The payload `value` in the canonical text of `kind` at `sort`: `None` when it is already
/// canonical or names no element, so that it is kept as it is.
pub fn canonical_text<S: DomainSort>(kind: DomainKind, sort: &S, value: &[u8]) -> Option<String> {
    match kind {
        DomainKind::Int => canonical_int_text(std::str::from_utf8(value).ok()?),
        DomainKind::MInt(width) => {
            canonical_mint_text(width, sort, std::str::from_utf8(value).ok()?)
        }
        DomainKind::Float => canonical_float_value(std::str::from_utf8(value).ok()?),
        DomainKind::Bool | DomainKind::String | DomainKind::Bytes | DomainKind::Token => None,
    }
}

/// `text` in the canonical text of the Float value it names; `None` when it already is, and when
/// it names no value the backend builds (load refuses it: outside FLOAT-SYNTAX, a format field of
/// 0 or 1, beyond the size bound), which is kept as written.
fn canonical_float_value(text: &str) -> Option<String> {
    match canonical_float_text(text) {
        Ok(canonical) if canonical != text => Some(canonical),
        Ok(_) | Err(_) => None,
    }
}

/// The residue of the literal `text` modulo `2^W` in `[0, 2^W)`, followed by `p` and the
/// digits of `sort`'s width argument as written, so that the text stays a literal of its own
/// sort. The text is kept as written when it is no literal of `sort` (load refuses it), and for
/// a negative literal of a width beyond `MAX_INT_RESULT_BITS` (refused at load by that bound),
/// whose residue would be a decimal of about `W` bits. A nonnegative literal is reduced within
/// its own size. `None` when the text is kept as written, or is already canonical.
fn canonical_mint_text<S: DomainSort>(width: MIntWidth, sort: &S, text: &str) -> Option<String> {
    let bits = match width {
        MIntWidth::Bits(bits) => Some(bits),
        MIntWidth::Unrepresentable => None,
        MIntWidth::NoWidth => return None,
    };
    let sort_digits = mint_width_digits(sort)?;
    let literal = MIntLiteral::parse(text)?;
    if !literal.names_width(sort_digits) {
        return None;
    }
    let negative = literal.is_negative();
    if negative && mint_width_beyond_bound(width) {
        return None;
    }
    #[cfg(any(test, feature = "measure"))]
    MINT_TEXT_PARSES.set(MINT_TEXT_PARSES.get() + 1);
    let magnitude: BigUint = literal
        .magnitude
        .parse()
        .expect("a literal's magnitude is decimal digits");
    let residue = match bits {
        Some(bits) if negative => {
            let modulus = BigUint::from(1_u8) << bits;
            let reduced = magnitude % &modulus;
            if reduced == BigUint::ZERO {
                reduced
            } else {
                modulus - reduced
            }
        }
        Some(bits) if magnitude.bits() > bits => magnitude % (BigUint::from(1_u8) << bits),
        // Below `2^W`: the magnitude is its own residue.
        _ => {
            let canonical = literal.sign.is_none()
                && literal.separator == b'p'
                && literal.width == sort_digits
                && (literal.magnitude.len() == 1 || !literal.magnitude.starts_with('0'));
            if canonical {
                return None;
            }
            magnitude
        }
    };
    Some(format!("{residue}p{sort_digits}"))
}

/// `text` in canonical decimal (no `+`, no leading zero, `0` unsigned); `None` when it already
/// is, and when it is no decimal integer, which is kept as written.
fn canonical_int_text(text: &str) -> Option<String> {
    let bytes = text.as_bytes();
    let canonical = match bytes {
        [b'0'] => true,
        [b'-', b'1'..=b'9', rest @ ..] | [b'1'..=b'9', rest @ ..] => {
            rest.iter().all(u8::is_ascii_digit)
        }
        _ => false,
    };
    if canonical {
        return None;
    }
    text.parse::<BigInt>()
        .ok()
        .map(|integer| integer.to_string())
}
