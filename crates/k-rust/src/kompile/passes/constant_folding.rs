//! Compile-time evaluation of pure Boolean, integer, and string hooks.

use std::{cmp::Ordering, collections::BTreeMap, fmt, str::FromStr};

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::{
    definition::{
        Definition, LabelHead, ModuleId, ProductionCatalog, ResolvedDefinition, Sentence,
        SortCatalog, SortHead,
    },
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{Label, Sort, Term},
};

#[cfg(feature = "mpfr-folding")]
#[path = "constant_folding_float.rs"]
mod float;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConstantFoldingError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for ConstantFoldingError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "constant folding produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for ConstantFoldingError {}

/// Apply Java's rewrite-aware `ConstantFolding` transformation to local rules.
pub fn constant_fold(definition: &Definition) -> Result<Definition, ConstantFoldingError> {
    let resolved =
        ResolvedDefinition::resolve(definition).map_err(|error| ConstantFoldingError {
            diagnostics: vec![Diagnostic {
                severity: Severity::Error,
                code: DiagnosticCode::InvalidConstantFolding,
                message: error.to_string(),
                source: None,
                location: None,
            }],
        })?;
    let mut output = definition.clone();
    let mut diagnostics = Vec::new();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let folder = Folder::new(&resolved, module_id);
        for sentence in &mut module.local_sentences {
            let Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
                ..
            } = sentence
            else {
                continue;
            };
            *body = folder.fold(body.clone(), Position::Both, attributes, &mut diagnostics);
            *requires = folder.fold(
                requires.clone(),
                Position::Right,
                attributes,
                &mut diagnostics,
            );
            *ensures = folder.fold(
                ensures.clone(),
                Position::Right,
                attributes,
                &mut diagnostics,
            );
        }
    }
    if diagnostics.is_empty() {
        Ok(output)
    } else {
        diagnostics.sort();
        Err(ConstantFoldingError { diagnostics })
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Position {
    Both,
    Left,
    Right,
}

struct Folder<'a> {
    productions: ProductionCatalog<'a>,
    sorts: SortCatalog<'a>,
}

impl<'a> Folder<'a> {
    fn new(definition: &'a ResolvedDefinition, module: ModuleId) -> Self {
        Self {
            productions: definition.production_catalog(module),
            sorts: definition.sort_catalog(module),
        }
    }

    fn fold(
        &self,
        term: Term,
        position: Position,
        sentence_attributes: &crate::definition::Attributes,
        diagnostics: &mut Vec<Diagnostic>,
    ) -> Term {
        let metadata = term.metadata().cloned();
        let rebuilt = match term.into_unannotated() {
            Term::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.fold(*left, Position::Left, sentence_attributes, diagnostics)),
                right: Box::new(self.fold(
                    *right,
                    Position::Right,
                    sentence_attributes,
                    diagnostics,
                )),
            },
            Term::As { pattern, alias } => Term::As {
                pattern: Box::new(self.fold(*pattern, position, sentence_attributes, diagnostics)),
                alias: Box::new(self.fold(*alias, position, sentence_attributes, diagnostics)),
            },
            Term::Sequence(items) => Term::Sequence(
                items
                    .into_iter()
                    .map(|item| self.fold(item, position, sentence_attributes, diagnostics))
                    .collect(),
            ),
            Term::Apply { label, arguments } => {
                let arguments = arguments
                    .into_iter()
                    .map(|argument| self.fold(argument, position, sentence_attributes, diagnostics))
                    .collect::<Vec<_>>();
                if position == Position::Right {
                    match self.try_fold(&label, &arguments) {
                        Ok(Some(token)) => return token,
                        Ok(None) => {}
                        Err(message) => diagnostics.push(Diagnostic::error_at(
                            DiagnosticCode::InvalidConstantFolding,
                            message,
                            sentence_attributes,
                        )),
                    }
                }
                Term::Apply { label, arguments }
            }
            leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
            Term::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
        };
        metadata.map_or(rebuilt.clone(), |metadata| rebuilt.with_metadata(metadata))
    }

    fn try_fold(&self, label: &Label, arguments: &[Term]) -> Result<Option<Term>, String> {
        let Some(production) = self
            .productions
            .productions_for(&LabelHead::from(label))
            .first()
            .map(|id| self.productions.production(*id))
        else {
            return Ok(None);
        };
        let Sentence::Production {
            parameters,
            sort,
            attributes,
            ..
        } = production
        else {
            unreachable!()
        };
        let Some(hook) = attributes.get_str("hook") else {
            return Ok(None);
        };
        if attributes.get("impure").is_some()
            || !matches!(
                hook.split_once('.').map(|pair| pair.0),
                Some("BOOL" | "INT" | "STRING" | "FLOAT")
            )
        {
            return Ok(None);
        }
        let tokens = arguments
            .iter()
            .map(|argument| match argument.unannotated() {
                Term::Token { token, sort } => Some((token.as_str(), sort)),
                _ => None,
            })
            .collect::<Option<Vec<_>>>();
        let Some(tokens) = tokens else {
            return Ok(None);
        };
        let substitution = parameters
            .iter()
            .cloned()
            .zip(label.parameters.iter().cloned())
            .collect::<BTreeMap<_, _>>();
        let result_sort = substitute_sort(sort, &substitution);
        let value = self.evaluate(hook, &tokens)?;
        Ok(Some(Term::Token {
            token: self.wrap(value, &result_sort),
            sort: result_sort,
        }))
    }

    fn evaluate(&self, hook: &str, tokens: &[(&str, &Sort)]) -> Result<Value, String> {
        let values = tokens
            .iter()
            .map(|(token, sort)| self.unwrap(token, sort))
            .collect::<Result<Vec<_>, _>>()?;
        #[cfg(feature = "mpfr-folding")]
        if let Some(result) = float::evaluate(hook, &values) {
            return result;
        }
        match hook {
            "BOOL.not" => unary_bool(&values, |a| !a),
            "BOOL.and" | "BOOL.andThen" => binary_bool(&values, |a, b| a && b),
            "BOOL.xor" => binary_bool(&values, |a, b| a ^ b),
            "BOOL.or" | "BOOL.orElse" => binary_bool(&values, |a, b| a || b),
            "BOOL.implies" => binary_bool(&values, |a, b| !a || b),
            "BOOL.eq" => binary_bool(&values, |a, b| a == b),
            "BOOL.ne" => binary_bool(&values, |a, b| a != b),
            "INT.not" => unary_int(&values, |a| Ok(Value::Int(!a))),
            "INT.pow" => binary_int(&values, |a, b| Ok(a.pow(unsigned_32(&b, "INT.pow")?))),
            "INT.powmod" => ternary_int(&values, int_powmod),
            "INT.mul" => binary_int(&values, |a, b| Ok(a * b)),
            "INT.tdiv" => binary_int(&values, |a, b| checked_div(a, b, false)),
            "INT.tmod" => binary_int(&values, |a, b| checked_rem(a, b, false)),
            "INT.ediv" => binary_int(&values, |a, b| checked_div(a, b, true)),
            "INT.emod" => binary_int(&values, |a, b| checked_rem(a, b, true)),
            "INT.add" => binary_int(&values, |a, b| Ok(a + b)),
            "INT.sub" => binary_int(&values, |a, b| Ok(a - b)),
            "INT.shr" => binary_int(&values, |a, b| Ok(a >> unsigned_32(&b, "INT.shr")?)),
            "INT.shl" => binary_int(&values, |a, b| Ok(a << unsigned_32(&b, "INT.shl")?)),
            "INT.and" => binary_int(&values, |a, b| Ok(a & b)),
            "INT.xor" => binary_int(&values, |a, b| Ok(a ^ b)),
            "INT.or" => binary_int(&values, |a, b| Ok(a | b)),
            "INT.min" => binary_int(&values, |a, b| Ok(a.min(b))),
            "INT.max" => binary_int(&values, |a, b| Ok(a.max(b))),
            "INT.abs" => unary_int(&values, |a| Ok(Value::Int(a.abs()))),
            "INT.log2" => unary_int(&values, int_log2),
            "INT.bitRange" => ternary_int(&values, int_bit_range),
            "INT.signExtendBitRange" => ternary_int(&values, int_sign_extend_bit_range),
            "INT.lt" => compare_int(&values, |ordering| ordering == Ordering::Less),
            "INT.gt" => compare_int(&values, |ordering| ordering == Ordering::Greater),
            "INT.le" => compare_int(&values, |ordering| ordering != Ordering::Greater),
            "INT.ge" => compare_int(&values, |ordering| ordering != Ordering::Less),
            "INT.eq" => compare_int(&values, |ordering| ordering == Ordering::Equal),
            "INT.ne" => compare_int(&values, |ordering| ordering != Ordering::Equal),
            "STRING.concat" => binary_string(&values, |a, b| Ok(format!("{a}{b}"))),
            "STRING.length" => {
                unary_string(&values, |a| Ok(Value::Int(BigInt::from(a.chars().count()))))
            }
            "STRING.chr" => unary_int(&values, string_chr),
            "STRING.ord" => unary_string(&values, string_ord),
            "STRING.substr" => string_substr(&values),
            "STRING.find" => string_find(&values, false, false),
            "STRING.rfind" => string_find(&values, true, false),
            "STRING.findChar" => string_find(&values, false, true),
            "STRING.rfindChar" => string_find(&values, true, true),
            "STRING.string2int" => unary_string(&values, |a| parse_int(a, 10)),
            "STRING.int2string" => unary_int(&values, |a| Ok(Value::String(a.to_string()))),
            "STRING.string2base" => string_to_base(&values),
            "STRING.base2string" => base_to_string(&values),
            "STRING.replaceAll" => replace_string(&values, None, false),
            "STRING.replace" => replace_string(&values, Some(3), false),
            "STRING.replaceFirst" => replace_string(&values, None, true),
            "STRING.countAllOccurrences" => count_occurrences(&values),
            "STRING.eq" => compare_string(&values, |ordering| ordering == Ordering::Equal),
            "STRING.ne" => compare_string(&values, |ordering| ordering != Ordering::Equal),
            "STRING.lt" => compare_string(&values, |ordering| ordering == Ordering::Less),
            "STRING.gt" => compare_string(&values, |ordering| ordering == Ordering::Greater),
            "STRING.le" => compare_string(&values, |ordering| ordering != Ordering::Greater),
            "STRING.ge" => compare_string(&values, |ordering| ordering != Ordering::Less),
            "STRING.token2string" | "STRING.string2token" => {
                unary_string(&values, |a| Ok(Value::String(a.to_owned())))
            }
            hook if hook.starts_with("FLOAT.")
                || hook.starts_with("STRING.float")
                || hook == "STRING.string2float" =>
            {
                Err(format!(
                    "floating-point constant folding for hook {hook} requires the native MPFR implementation"
                ))
            }
            _ => Err(format!(
                "Missing constant-folding implementation for hook {hook}"
            )),
        }
    }

    fn unwrap(&self, token: &str, sort: &Sort) -> Result<Value, String> {
        match self
            .sorts
            .attributes_for(&SortHead::from(sort))
            .and_then(|attributes| attributes.get_str("hook"))
        {
            Some("BOOL.Bool") => bool::from_str(token)
                .map(Value::Bool)
                .map_err(|_| format!("invalid Bool token {token:?}")),
            Some("INT.Int") => BigInt::from_str(token)
                .map(Value::Int)
                .map_err(|_| format!("invalid Int token {token:?}")),
            Some("STRING.String") => crate::kast::string::unquote(token).map(Value::String),
            Some("FLOAT.Float") => {
                #[cfg(feature = "mpfr-folding")]
                {
                    float::KFloat::parse(token).map(Value::Float)
                }
                #[cfg(not(feature = "mpfr-folding"))]
                {
                    Ok(Value::Float(token.to_owned()))
                }
            }
            _ => Ok(Value::String(token.to_owned())),
        }
    }

    fn wrap(&self, value: Value, sort: &Sort) -> String {
        let string_sort = self
            .sorts
            .attributes_for(&SortHead::from(sort))
            .and_then(|attributes| attributes.get_str("hook"))
            .is_some_and(|hook| matches!(hook, "STRING.String" | "BYTES.Bytes"));
        match value {
            Value::Bool(value) => value.to_string(),
            Value::Int(value) => value.to_string(),
            Value::String(value) if string_sort => crate::kast::string::quote(&value),
            Value::String(value) => value,
            #[cfg(feature = "mpfr-folding")]
            Value::Float(value) => value.token(),
            #[cfg(not(feature = "mpfr-folding"))]
            Value::Float(value) => value,
        }
    }
}

#[derive(Clone, Debug)]
enum Value {
    Bool(bool),
    Int(BigInt),
    String(String),
    #[cfg(feature = "mpfr-folding")]
    Float(float::KFloat),
    #[cfg(not(feature = "mpfr-folding"))]
    Float(String),
}

fn bool_value(value: &Value) -> Result<bool, String> {
    match value {
        Value::Bool(value) => Ok(*value),
        _ => Err("constant-folding hook expected Bool".into()),
    }
}
fn int_value(value: &Value) -> Result<BigInt, String> {
    match value {
        Value::Int(value) => Ok(value.clone()),
        _ => Err("constant-folding hook expected Int".into()),
    }
}
fn string_value(value: &Value) -> Result<&str, String> {
    match value {
        Value::String(value) => Ok(value),
        _ => Err("constant-folding hook expected String or token".into()),
    }
}
fn unary_bool(values: &[Value], f: impl FnOnce(bool) -> bool) -> Result<Value, String> {
    let [a] = values else {
        return Err("constant-folding hook expected one argument".into());
    };
    Ok(Value::Bool(f(bool_value(a)?)))
}
fn binary_bool(values: &[Value], f: impl FnOnce(bool, bool) -> bool) -> Result<Value, String> {
    let [a, b] = values else {
        return Err("constant-folding hook expected two arguments".into());
    };
    Ok(Value::Bool(f(bool_value(a)?, bool_value(b)?)))
}
fn unary_int(
    values: &[Value],
    f: impl FnOnce(BigInt) -> Result<Value, String>,
) -> Result<Value, String> {
    let [a] = values else {
        return Err("constant-folding hook expected one argument".into());
    };
    f(int_value(a)?)
}
fn binary_int(
    values: &[Value],
    f: impl FnOnce(BigInt, BigInt) -> Result<BigInt, String>,
) -> Result<Value, String> {
    let [a, b] = values else {
        return Err("constant-folding hook expected two arguments".into());
    };
    f(int_value(a)?, int_value(b)?).map(Value::Int)
}
fn ternary_int(
    values: &[Value],
    f: impl FnOnce(BigInt, BigInt, BigInt) -> Result<BigInt, String>,
) -> Result<Value, String> {
    let [a, b, c] = values else {
        return Err("constant-folding hook expected three arguments".into());
    };
    f(int_value(a)?, int_value(b)?, int_value(c)?).map(Value::Int)
}
fn compare_int(values: &[Value], f: impl FnOnce(Ordering) -> bool) -> Result<Value, String> {
    let [a, b] = values else {
        return Err("constant-folding hook expected two arguments".into());
    };
    Ok(Value::Bool(f(int_value(a)?.cmp(&int_value(b)?))))
}
fn unary_string(
    values: &[Value],
    f: impl FnOnce(&str) -> Result<Value, String>,
) -> Result<Value, String> {
    let [a] = values else {
        return Err("constant-folding hook expected one argument".into());
    };
    f(string_value(a)?)
}
fn binary_string(
    values: &[Value],
    f: impl FnOnce(&str, &str) -> Result<String, String>,
) -> Result<Value, String> {
    let [a, b] = values else {
        return Err("constant-folding hook expected two arguments".into());
    };
    f(string_value(a)?, string_value(b)?).map(Value::String)
}
fn compare_string(values: &[Value], f: impl FnOnce(Ordering) -> bool) -> Result<Value, String> {
    let [a, b] = values else {
        return Err("constant-folding hook expected two arguments".into());
    };
    Ok(Value::Bool(f(string_value(a)?.cmp(string_value(b)?))))
}

fn unsigned_32(value: &BigInt, hook: &str) -> Result<u32, String> {
    value.to_u32().ok_or_else(|| {
        format!("Argument to hook {hook} out of range. Expected a 32-bit unsigned integer.")
    })
}
fn checked_div(a: BigInt, b: BigInt, euclidean: bool) -> Result<BigInt, String> {
    if b.is_zero() {
        return Err("Division by zero.".into());
    }
    if !euclidean {
        return Ok(a / b);
    }
    let rem = checked_rem(a.clone(), b.clone(), true)?;
    Ok((a - rem) / b)
}
fn checked_rem(a: BigInt, b: BigInt, euclidean: bool) -> Result<BigInt, String> {
    if b.is_zero() {
        return Err(if euclidean {
            "Division by zero."
        } else {
            "Modulus by zero."
        }
        .into());
    }
    let rem = a % &b;
    Ok(if euclidean && rem.is_negative() {
        rem + b.abs()
    } else {
        rem
    })
}
fn int_log2(mut value: BigInt) -> Result<Value, String> {
    if value <= BigInt::zero() {
        return Err("Argument to hook INT.log2 out of range. Expected a positive integer.".into());
    }
    let mut result = 0u64;
    while value > BigInt::one() {
        value >>= 1usize;
        result += 1;
    }
    Ok(Value::Int(result.into()))
}
fn int_bit_range(value: BigInt, index: BigInt, length: BigInt) -> Result<BigInt, String> {
    let index = unsigned_32(&index, "INT.bitRange")? as usize;
    let length = unsigned_32(&length, "INT.bitRange")? as usize;
    Ok((value & ((BigInt::one() << length) - 1u8) << index) >> index)
}
fn int_sign_extend_bit_range(
    value: BigInt,
    index: BigInt,
    length: BigInt,
) -> Result<BigInt, String> {
    let index_u = unsigned_32(&index, "INT.signExtendBitRange")? as usize;
    let length_u = unsigned_32(&length, "INT.signExtendBitRange")? as usize;
    if length_u == 0 {
        return Ok(BigInt::zero());
    }
    let result = int_bit_range(value.clone(), index, length.clone())?;
    if ((value >> (index_u + length_u - 1)) & BigInt::one()).is_one() {
        Ok(result - (BigInt::one() << length_u))
    } else {
        Ok(result)
    }
}
fn int_powmod(a: BigInt, exponent: BigInt, modulus: BigInt) -> Result<BigInt, String> {
    if modulus <= BigInt::zero() {
        return Err("Argument to hook INT.powmod is invalid. Modulus must be positive and negative exponents are only allowed when value and modulus are relatively prime.".into());
    }
    if exponent.is_negative() {
        let inverse = modular_inverse(a, modulus.clone()).ok_or_else(|| "Argument to hook INT.powmod is invalid. Modulus must be positive and negative exponents are only allowed when value and modulus are relatively prime.".to_owned())?;
        Ok(inverse.modpow(&(-exponent), &modulus))
    } else {
        Ok(a.modpow(&exponent, &modulus))
    }
}
fn modular_inverse(a: BigInt, modulus: BigInt) -> Option<BigInt> {
    let (mut old_r, mut r) = (a, modulus.clone());
    let (mut old_s, mut s) = (BigInt::one(), BigInt::zero());
    while !r.is_zero() {
        let q = &old_r / &r;
        (old_r, r) = (r.clone(), old_r - &q * r);
        (old_s, s) = (s.clone(), old_s - q * s);
    }
    if old_r.abs() != BigInt::one() {
        None
    } else {
        Some(((old_s % &modulus) + &modulus) % modulus)
    }
}

fn string_chr(value: BigInt) -> Result<Value, String> {
    let Some(value) = value.to_u32().and_then(char::from_u32) else {
        return Err(
            "Argument to hook STRING.chr out of range. Expected a number between 0 and 1114111."
                .into(),
        );
    };
    Ok(Value::String(value.to_string()))
}
fn string_ord(value: &str) -> Result<Value, String> {
    let mut chars = value.chars();
    let Some(character) = chars.next() else {
        return Err(
            "Argument to hook STRING.ord out of range. Expected a single character.".into(),
        );
    };
    if chars.next().is_some() {
        return Err(
            "Argument to hook STRING.ord out of range. Expected a single character.".into(),
        );
    }
    Ok(Value::Int((character as u32).into()))
}
fn string_substr(values: &[Value]) -> Result<Value, String> {
    let [text, start, end] = values else {
        return Err("constant-folding hook expected three arguments".into());
    };
    let text = string_value(text)?;
    let start = unsigned_32(&int_value(start)?, "STRING.substr")? as usize;
    let end = unsigned_32(&int_value(end)?, "STRING.substr")? as usize;
    let chars = text.chars().collect::<Vec<_>>();
    if start > end || end > chars.len() {
        return Err("Argument to hook STRING.substr out of range. Expected two indices >= 0 and <= the length of the string.".into());
    }
    Ok(Value::String(chars[start..end].iter().collect()))
}
fn string_find(values: &[Value], reverse: bool, any_char: bool) -> Result<Value, String> {
    let [haystack, needles, index] = values else {
        return Err("constant-folding hook expected three arguments".into());
    };
    let haystack = string_value(haystack)?;
    let needles = string_value(needles)?;
    let index = unsigned_32(
        &int_value(index)?,
        if reverse {
            "STRING.rfind"
        } else {
            "STRING.find"
        },
    )? as usize;
    let chars = haystack.chars().collect::<Vec<_>>();
    if index > chars.len() {
        return Err(format!(
            "Argument to hook STRING.{} out of range. Expected an index >= 0 and <= the length of the string to search.",
            if reverse { "rfind" } else { "find" }
        ));
    }
    let found = if any_char {
        if reverse {
            (0..=index.min(chars.len().saturating_sub(1)))
                .rev()
                .find(|&i| needles.contains(chars[i]))
        } else {
            (index..chars.len()).find(|&i| needles.contains(chars[i]))
        }
    } else {
        let needle = needles.chars().collect::<Vec<_>>();
        if reverse {
            (0..=index.min(chars.len()))
                .rev()
                .find(|&i| i + needle.len() <= chars.len() && chars[i..i + needle.len()] == needle)
        } else {
            (index..=chars.len())
                .find(|&i| i + needle.len() <= chars.len() && chars[i..i + needle.len()] == needle)
        }
    };
    Ok(Value::Int(found.map_or(-1i64, |i| i as i64).into()))
}
fn parse_int(value: &str, radix: u32) -> Result<Value, String> {
    BigInt::parse_bytes(value.as_bytes(), radix)
        .map(Value::Int)
        .ok_or_else(|| {
            "Argument to hook STRING.string2int invalid. Expected a valid integer.".into()
        })
}
fn radix(value: &Value) -> Result<u32, String> {
    let radix = int_value(value)?
        .to_u32()
        .filter(|value| (2..=36).contains(value))
        .ok_or_else(|| {
            "Argument to string/base conversion out of range. Expected a number between 2 and 36."
                .to_owned()
        })?;
    Ok(radix)
}
fn string_to_base(values: &[Value]) -> Result<Value, String> {
    let [text, base] = values else {
        return Err("constant-folding hook expected two arguments".into());
    };
    parse_int(string_value(text)?, radix(base)?)
}
fn base_to_string(values: &[Value]) -> Result<Value, String> {
    let [value, base] = values else {
        return Err("constant-folding hook expected two arguments".into());
    };
    Ok(Value::String(int_value(value)?.to_str_radix(radix(base)?)))
}
fn replace_string(
    values: &[Value],
    count_index: Option<usize>,
    first: bool,
) -> Result<Value, String> {
    let [haystack, needle, replacement, ..] = values else {
        return Err("constant-folding hook expected at least three arguments".into());
    };
    let mut remaining = string_value(haystack)?.to_owned();
    let needle = string_value(needle)?;
    let replacement = string_value(replacement)?;
    let count = if first {
        1
    } else if let Some(index) = count_index {
        unsigned_32(&int_value(&values[index])?, "STRING.replace")? as usize
    } else {
        usize::MAX
    };
    if needle.is_empty() || count == 0 {
        return Ok(Value::String(remaining));
    }
    let mut out = String::new();
    for _ in 0..count {
        let Some(index) = remaining.find(needle) else {
            break;
        };
        out.push_str(&remaining[..index]);
        out.push_str(replacement);
        remaining = remaining[index + needle.len()..].to_owned();
    }
    out.push_str(&remaining);
    Ok(Value::String(out))
}
fn count_occurrences(values: &[Value]) -> Result<Value, String> {
    let [haystack, needle] = values else {
        return Err("constant-folding hook expected two arguments".into());
    };
    let haystack = string_value(haystack)?;
    let needle = string_value(needle)?;
    Ok(Value::Int(
        if needle.is_empty() {
            0usize
        } else {
            haystack.match_indices(needle).count()
        }
        .into(),
    ))
}

fn substitute_sort(sort: &Sort, substitution: &BTreeMap<Sort, Sort>) -> Sort {
    substitution.get(sort).cloned().unwrap_or_else(|| {
        Sort::with_parameters(
            &sort.name,
            sort.parameters
                .iter()
                .map(|parameter| substitute_sort(parameter, substitution))
                .collect(),
        )
    })
}
