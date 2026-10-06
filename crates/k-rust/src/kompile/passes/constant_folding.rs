//! ```toml algorithm
//! id = "kompile.constant_folding.evaluate"
//! name = "bottom-up evaluation of constant hooked operations"
//! sites = ["constant_fold", "constant_fold_pass", "Folder::fold", "Folder::evaluate"]
//! variable = "N = visited term nodes; h = term height"
//! counters = []
//! no_counter = "constant folding has no dedicated counter; the shared pass scaffolding bumps KompileResolveCalls, KompileSentenceCopies and KompilePartialOrdersBuilt, and KompileSentencesTransformed is added once per compile"
//!
//! [[cost]]
//! mode = "one definition"
//! bound = "O(N x h) plus hook-specific arithmetic cost"
//! ```
//!
//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Compile-time evaluation of pure Boolean, integer, and string hooks.
#![deny(clippy::wildcard_enum_match_arm)]

use std::{cmp::Ordering, collections::BTreeMap, fmt, str::FromStr};

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::definition::AttributeKey;
use crate::{
    definition::{
        Definition, DefinitionViews, LabelHead, ModuleId, ProductionCatalog, Sentence, SortCatalog,
        SortHead,
    },
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{Label, Sort, Term, TermParts},
    provenance::GeneratingPass,
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
    super::super::pipeline::run_standalone(
        definition,
        constant_fold_pass,
        Some(GeneratingPass::ConstantFolding),
    )
}

pub(crate) fn constant_fold_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ConstantFoldingError> {
    let resolved = input.resolved_raw().map_err(|error| ConstantFoldingError {
        diagnostics: vec![Diagnostic {
            severity: Severity::Error,
            code: DiagnosticCode::InvalidConstantFolding,
            message: error.to_string(),
            source: None,
            location: None,
            input_addresses: Vec::new(),
        }],
    })?;
    let views = resolved.views();
    let mut output = input.definition.clone();
    let mut diagnostics = Vec::new();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let folder = Folder::new(&views, module_id);
        for sentence in &mut module.local_sentences {
            // Only rules change. The kind is decided before taking a mutable sentence, which
            // copies a shared one, so every other kind stays shared.
            match &**sentence {
                Sentence::Rule { .. } => {}
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Context { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => continue,
            }
            let sentence = crate::definition::sentence_mut(sentence);
            let Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
                ..
            } = sentence
            else {
                unreachable!("copy-on-write keeps the kind decided above");
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

struct Folder<'view, 'definition> {
    productions: &'view ProductionCatalog<'definition>,
    sorts: &'view SortCatalog<'definition>,
}

impl<'view, 'definition> Folder<'view, 'definition> {
    fn new(views: &'view DefinitionViews<'definition>, module: ModuleId) -> Self {
        Self {
            productions: views.production_catalog(module),
            sorts: views.sort_catalog(module),
        }
    }

    // Invariant: `fold` rebuilds `term` bottom-up, folding an `Apply` in `Position::Right` only after its `arguments` are folded; each call recurses into the immediate subterms of `term`, so its finite depth bounds the recursion.
    fn fold(
        &self,
        term: Term,
        position: Position,
        sentence_attributes: &crate::definition::Attributes,
        diagnostics: &mut Vec<Diagnostic>,
    ) -> Term {
        let metadata = term.metadata().cloned();
        let rebuilt = match term.into_unannotated().into_parts() {
            TermParts::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.fold(*left, Position::Left, sentence_attributes, diagnostics)),
                right: Box::new(self.fold(
                    *right,
                    Position::Right,
                    sentence_attributes,
                    diagnostics,
                )),
            },
            TermParts::As { pattern, alias } => Term::As {
                pattern: Box::new(self.fold(*pattern, position, sentence_attributes, diagnostics)),
                alias: Box::new(self.fold(*alias, position, sentence_attributes, diagnostics)),
            },
            TermParts::Sequence(items) => Term::Sequence(
                items
                    .into_iter()
                    .map(|item| self.fold(item, position, sentence_attributes, diagnostics))
                    .collect(),
            ),
            TermParts::Apply { label, arguments } => {
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
            leaf @ (TermParts::InjectedLabel(_)
            | TermParts::Variable { .. }
            | TermParts::Token { .. }) => Term::from(leaf),
            TermParts::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
        };
        match metadata {
            Some(metadata) => rebuilt.with_metadata(metadata),
            None => rebuilt,
        }
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
        let Some(hook) = attributes.string(AttributeKey::Hook) else {
            return Ok(None);
        };
        if attributes.has(AttributeKey::Impure)
            || !matches!(
                hook.split_once('.').map(|pair| pair.0),
                Some("BOOL" | "INT" | "STRING" | "FLOAT")
            )
        {
            return Ok(None);
        }
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "Term is syntax; only the listed variants are special here"
        )]
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
        // A result sort that mentions a sort parameter is known only through the label's
        // instance; a label without one (as loaded, before sort injection solves it) gives the
        // folded token no sort. A result sort free of parameters is the token's sort whatever
        // the instance.
        if parameters.len() != label.parameters.len()
            && parameters
                .iter()
                .any(|parameter| sort_mentions(sort, parameter))
        {
            return Ok(None);
        }
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
            .and_then(|attributes| attributes.string(AttributeKey::Hook))
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
            .and_then(|attributes| attributes.string(AttributeKey::Hook))
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
        Value::Int(_) | Value::String(_) | Value::Float(_) => {
            Err("constant-folding hook expected Bool".into())
        }
    }
}
fn int_value(value: &Value) -> Result<BigInt, String> {
    match value {
        Value::Int(value) => Ok(value.clone()),
        Value::Bool(_) | Value::String(_) | Value::Float(_) => {
            Err("constant-folding hook expected Int".into())
        }
    }
}
fn string_value(value: &Value) -> Result<&str, String> {
    match value {
        Value::String(value) => Ok(value),
        Value::Bool(_) | Value::Int(_) | Value::Float(_) => {
            Err("constant-folding hook expected String or token".into())
        }
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
    value
        .to_u32()
        .filter(|value| *value <= i32::MAX as u32)
        .ok_or_else(|| {
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
    // Invariant: `value` is the argument shifted right by `result` bits and stays at least 1; each iteration halves `value`, so the loop runs floor(log2) times.
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
    // `domains.md` defines the result through `1 <<Int (LEN -Int 1)`, a shift by a negative
    // quantity, and therefore undefined, when the length is zero.
    if length_u == 0 {
        return Err(
            "Argument to hook INT.signExtendBitRange out of range. Expected a positive length."
                .into(),
        );
    }
    let result = int_bit_range(value.clone(), index, length.clone())?;
    if ((value >> (index_u + length_u - 1)) & BigInt::one()).is_one() {
        Ok(result - (BigInt::one() << length_u))
    } else {
        Ok(result)
    }
}
fn int_powmod(a: BigInt, exponent: BigInt, modulus: BigInt) -> Result<BigInt, String> {
    const INVALID: &str = "Argument to hook INT.powmod is invalid. Modulus must be nonzero and negative exponents are only allowed when value and modulus are relatively prime.";
    if modulus.is_zero() {
        return Err(INVALID.into());
    }
    // `^%Int` is `(A ^Int B) mod C` (its `smt-hook`): the Euclidean remainder, which lies in
    // [0, |C|) and is therefore the same for C and -C.
    let modulus = modulus.abs();
    if exponent.is_negative() {
        let inverse = modular_inverse(a, modulus.clone()).ok_or_else(|| INVALID.to_owned())?;
        Ok(inverse.modpow(&(-exponent), &modulus))
    } else {
        Ok(a.modpow(&exponent, &modulus))
    }
}
fn modular_inverse(a: BigInt, modulus: BigInt) -> Option<BigInt> {
    let (mut old_r, mut r) = (a, modulus.clone());
    let (mut old_s, mut s) = (BigInt::one(), BigInt::zero());
    // Invariant: `old_r - old_s * a` and `r - s * a` are multiples of `modulus`, and gcd(`old_r`, `r`) equals gcd(`a`, `modulus`); each iteration replaces `r` by the remainder of `old_r / r`, whose absolute value is strictly smaller.
    while !r.is_zero() {
        let q = &old_r / &r;
        (old_r, r) = (r.clone(), old_r - &q * r);
        (old_s, s) = (s.clone(), old_s - q * s);
    }
    if old_r.abs() != BigInt::one() {
        return None;
    }
    // `old_s * a` is congruent to `old_r`, which is 1 or -1; for -1 the inverse is `-old_s`.
    if old_r.is_negative() {
        old_s = -old_s;
    }
    Some(((old_s % &modulus) + &modulus) % modulus)
}

fn string_chr(value: BigInt) -> Result<Value, String> {
    let Some(value) = value.to_u32().filter(|value| *value <= 0x10ffff) else {
        return Err(
            "Argument to hook STRING.chr out of range. Expected a number between 0 and 1114111."
                .into(),
        );
    };
    let Some(value) = char::from_u32(value) else {
        return Err(
            "Argument to hook STRING.chr is a surrogate code point. Expected a Unicode scalar value."
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
    // Invariant: each `find` scans candidate start indices of `chars` from `index` forward, or backward when `reverse`, and returns the first index holding a character of `needles` (when `any_char`) or the whole `needle`; the finite index range bounds the scan, O(`chars.len()` * `needle.len()`) for a substring search.
    let found = if any_char {
        if reverse {
            // The candidates are the positions at or before `index` that hold a character.
            (0..chars.len().min(index + 1))
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
    // An optional sign and one or more digits of the base. The integer parser alone would also
    // skip `_` separators, which are not digits.
    let digits = value.strip_prefix(['+', '-']).unwrap_or(value);
    let well_formed =
        !digits.is_empty() && digits.chars().all(|character| character.is_digit(radix));
    well_formed
        .then(|| BigInt::parse_bytes(value.as_bytes(), radix))
        .flatten()
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
    if count == 0 {
        return Ok(Value::String(remaining));
    }
    if needle.is_empty() {
        // `domains.md` defines `replace` by finding the needle from index 0 and recursing on the
        // rest of the haystack after it. An empty needle is found at 0 and leaves the whole
        // haystack as the rest, so `replace` and `replaceFirst` put `count` copies of the
        // replacement in front. `replaceAll` first counts the occurrences, a recursion that
        // does not terminate for an empty needle; it keeps the haystack unchanged.
        if count_index.is_none() && !first {
            return Ok(Value::String(remaining));
        }
        return Ok(Value::String(replacement.repeat(count) + &remaining));
    }
    let mut out = String::new();
    // Invariant: `out` holds the input before `remaining` with every occurrence of `needle` found so far replaced by `replacement`; each iteration consumes one occurrence, and at most `count` iterations run.
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

/// Whether `sort` is `parameter` or has it among its (nested) sort arguments.
fn sort_mentions(sort: &Sort, parameter: &Sort) -> bool {
    sort == parameter
        || sort
            .parameters
            .iter()
            .any(|argument| sort_mentions(argument, parameter))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(value: i64) -> BigInt {
        BigInt::from(value)
    }

    /// A negative base ends the Euclidean recursion on a remainder of -1, so its inverse is the
    /// negated Bezout coefficient: -1 * 4 = -4 and -2 * 3 = -6 are both 1 modulo 5 and 7.
    #[test]
    fn powmod_inverts_negative_bases() {
        assert_eq!(int_powmod(int(-1), int(-1), int(5)), Ok(int(4)));
        assert_eq!(int_powmod(int(-2), int(-1), int(7)), Ok(int(3)));
        assert_eq!(int_powmod(int(-2), int(-3), int(7)), Ok(int(6)));
        assert_eq!(int_powmod(int(3), int(-1), int(7)), Ok(int(5)));
    }

    /// The Euclidean remainder modulo -C is the remainder modulo C, so a negative modulus folds
    /// like its absolute value; only a zero modulus is undefined.
    #[test]
    fn powmod_reduces_by_the_magnitude_of_a_negative_modulus() {
        assert_eq!(int_powmod(int(2), int(3), int(-5)), Ok(int(3)));
        assert_eq!(int_powmod(int(-2), int(3), int(-5)), Ok(int(2)));
        assert_eq!(int_powmod(int(3), int(-1), int(-7)), Ok(int(5)));
        assert_eq!(int_powmod(int(0), int(0), int(-1)), Ok(int(0)));
        assert!(int_powmod(int(2), int(3), int(0)).is_err());
    }

    /// `rfindChar` scans the characters at or before its index, and an empty haystack has none.
    #[test]
    fn rfind_char_scans_only_existing_characters() {
        let found = |haystack: &str, needles: &str, index: i64| {
            let values = [
                Value::String(haystack.into()),
                Value::String(needles.into()),
                Value::Int(int(index)),
            ];
            match string_find(&values, true, true) {
                Ok(Value::Int(position)) => position,
                other => panic!("rfindChar({haystack:?}, {needles:?}, {index}) gave {other:?}"),
            }
        };
        assert_eq!(found("", "a", 0), int(-1));
        assert_eq!(found("", "", 0), int(-1));
        assert_eq!(found("ab", "b", 2), int(1));
        assert_eq!(found("ab", "b", 0), int(-1));
        assert_eq!(found("aba", "ab", 1), int(1));
    }

    /// An empty needle occurs at index 0 with the whole haystack after it, so each replacement
    /// `replace` and `replaceFirst` make goes in front.
    #[test]
    fn replacing_an_empty_needle_prepends_the_replacement() {
        let replaced =
            |values: &[Value], count_index, first| match replace_string(values, count_index, first)
            {
                Ok(Value::String(text)) => text,
                other => panic!("{values:?} gave {other:?}"),
            };
        let text = |value: &str| Value::String(value.into());
        let arguments = |count| [text("ab"), text(""), text("x"), Value::Int(int(count))];
        assert_eq!(replaced(&arguments(1), None, true), "xab");
        assert_eq!(replaced(&arguments(0), Some(3), false), "ab");
        assert_eq!(replaced(&arguments(3), Some(3), false), "xxxab");
        assert_eq!(replaced(&arguments(2), None, false), "ab");
        assert_eq!(
            replaced(
                &[text("abab"), text("b"), text("x"), Value::Int(int(1))],
                Some(3),
                false
            ),
            "axab"
        );
    }

    /// `signExtendBitRangeInt(I, IDX, LEN)` is `(bitRangeInt(I, IDX, LEN) +Int (1 <<Int (LEN -Int
    /// 1))) modInt (1 <<Int LEN) -Int (1 <<Int (LEN -Int 1))`, undefined for a zero length.
    #[test]
    fn sign_extension_of_an_empty_bit_range_is_undefined() {
        assert!(int_sign_extend_bit_range(int(5), int(0), int(0)).is_err());
        assert!(int_sign_extend_bit_range(int(-1), int(3), int(0)).is_err());
        assert_eq!(
            int_sign_extend_bit_range(int(5), int(0), int(1)),
            Ok(int(-1))
        );
        assert_eq!(
            int_sign_extend_bit_range(int(5), int(1), int(2)),
            Ok(int(-2))
        );
        assert_eq!(
            int_sign_extend_bit_range(int(5), int(0), int(4)),
            Ok(int(5))
        );
        assert_eq!(int_bit_range(int(5), int(0), int(0)), Ok(int(0)));
    }

    /// `String2Int` reads an optional sign and decimal digits, and `String2Base` the digits of
    /// its base in either case; a `_` separator is neither.
    #[test]
    fn integer_parsing_accepts_only_signed_digits() {
        let parsed = |text: &str, radix| match parse_int(text, radix) {
            Ok(Value::Int(value)) => Some(value),
            _ => None,
        };
        assert_eq!(parsed("+15", 10), Some(int(15)));
        assert_eq!(parsed("-007", 10), Some(int(-7)));
        assert_eq!(parsed("fF", 16), Some(int(255)));
        for text in ["1_0", "1_", "_1", "-_1", "", "+", "-", "+-1", " 1", "1e3"] {
            assert_eq!(parsed(text, 10), None, "{text:?}");
        }
        assert_eq!(parsed("f_f", 16), None);
        assert_eq!(parsed("12", 2), None);
    }
}

#[cfg(test)]
#[path = "constant_folding_oracle.rs"]
mod oracle;
