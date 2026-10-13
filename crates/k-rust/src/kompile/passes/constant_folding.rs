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

use k_rust_backend::builtin::{
    FloatTextRefusal, MAX_FLOAT_CANONICAL_BITS, float_canonical_bits_estimate,
};

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

/// Replace constant applications of pure hooks on the right-hand sides and conditions of local
/// rules by the literals of their values, leaving every application the fold does not evaluate.
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
                ..
            } = sentence
            else {
                unreachable!("copy-on-write keeps the kind decided above");
            };
            *body = folder.fold(body.clone(), Position::Both);
            *requires = folder.fold(requires.clone(), Position::Right);
            *ensures = folder.fold(ensures.clone(), Position::Right);
        }
    }
    Ok(output)
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
    fn fold(&self, term: Term, position: Position) -> Term {
        let metadata = term.metadata().cloned();
        let rebuilt = match term.into_unannotated().into_parts() {
            TermParts::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.fold(*left, Position::Left)),
                right: Box::new(self.fold(*right, Position::Right)),
            },
            TermParts::As { pattern, alias } => Term::As {
                pattern: Box::new(self.fold(*pattern, position)),
                alias: Box::new(self.fold(*alias, position)),
            },
            TermParts::Sequence(items) => Term::Sequence(
                items
                    .into_iter()
                    .map(|item| self.fold(item, position))
                    .collect(),
            ),
            TermParts::Apply { label, arguments } => {
                let arguments = arguments
                    .into_iter()
                    .map(|argument| self.fold(argument, position))
                    .collect::<Vec<_>>();
                // An application the fold does not evaluate keeps its meaning as written: the
                // fold only replaces a term by a token that denotes the same value (`Unfolded`).
                if position == Position::Right
                    && let Ok(Some(token)) = self.try_fold(&label, &arguments)
                {
                    return token;
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

    /// The token an application folds to; `Ok(None)` when it is not an application of a pure
    /// hook to tokens, and `Err` when it is one that the fold leaves as written.
    fn try_fold(&self, label: &Label, arguments: &[Term]) -> Result<Option<Term>, Unfolded> {
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
        let bits = value_bits(&value);
        if bits > MAX_FOLDED_BITS {
            return Err(Unfolded::TooLarge(format!(
                "the value of hook {hook} has {bits} bits, more than {MAX_FOLDED_BITS}"
            )));
        }
        let is_float = matches!(value, Value::Float(_));
        let token = self.wrap(value, &result_sort);
        if is_float {
            loadable_float(hook, &token)?;
        }
        Ok(Some(Term::Token {
            token,
            sort: result_sort,
        }))
    }

    fn evaluate(&self, hook: &str, tokens: &[(&str, &Sort)]) -> Result<Value, Unfolded> {
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
            "INT.pow" => binary_int(&values, int_pow),
            "INT.powmod" => ternary_int(&values, int_powmod),
            "INT.mul" => binary_int(&values, |a, b| Ok(a * b)),
            "INT.tdiv" => binary_int(&values, |a, b| checked_div(a, b, false)),
            "INT.tmod" => binary_int(&values, |a, b| checked_rem(a, b, false)),
            "INT.ediv" => binary_int(&values, |a, b| checked_div(a, b, true)),
            "INT.emod" => binary_int(&values, |a, b| checked_rem(a, b, true)),
            "INT.add" => binary_int(&values, |a, b| Ok(a + b)),
            "INT.sub" => binary_int(&values, |a, b| Ok(a - b)),
            "INT.shr" => binary_int(&values, |a, b| Ok(int_shr(a, natural(&b, "INT.shr")?))),
            "INT.shl" => binary_int(&values, int_shl),
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
                Err(Unfolded::Unsupported(format!(
                    "floating-point constant folding for hook {hook} requires the native MPFR implementation"
                )))
            }
            _ => Err(Unfolded::Unsupported(format!(
                "no constant-folding implementation for hook {hook}"
            ))),
        }
    }

    fn unwrap(&self, token: &str, sort: &Sort) -> Result<Value, Unfolded> {
        match self
            .sorts
            .attributes_for(&SortHead::from(sort))
            .and_then(|attributes| attributes.string(AttributeKey::Hook))
        {
            Some("BOOL.Bool") => bool::from_str(token)
                .map(Value::Bool)
                .map_err(|_| Unfolded::Unsupported(format!("invalid Bool token {token:?}"))),
            Some("INT.Int") => BigInt::from_str(token)
                .map(Value::Int)
                .map_err(|_| Unfolded::Unsupported(format!("invalid Int token {token:?}"))),
            Some("STRING.String") => crate::kast::string::unquote(token)
                .map(Value::String)
                .map_err(Unfolded::Unsupported),
            Some("FLOAT.Float") => {
                #[cfg(feature = "mpfr-folding")]
                {
                    float::KFloat::parse(token)
                        .map(Value::Float)
                        .map_err(|unfolded| Unfolded::Unsupported(unfolded.message().to_owned()))
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

/// Why the fold leaves a constant application of a pure hook as written. Folding replaces a term
/// by a token that denotes the same value, so where there is no such token, or the fold does not
/// compute it, the application stays and execution evaluates it; a definition never fails to
/// compile because of a constant's value.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Unfolded {
    /// The hook is undefined (`#Bottom`) on these arguments.
    Undefined(String),
    /// The hook is `total` and its documentation gives no value on these arguments, or the
    /// value is one the definition leaves to a reading k-rust applies only in an execution (a
    /// Float operation over two formats): the application denotes a value the definition does
    /// not determine.
    Unspecified(String),
    /// The value is defined but larger than `MAX_FOLDED_BITS`.
    TooLarge(String),
    /// The fold does not evaluate this hook, or cannot read these arguments.
    Unsupported(String),
}

/// The largest value the fold writes into a definition, in bits: an `Int`'s bit length, eight
/// times a `String`'s UTF-8 length, a `Float`'s precision. A compile must not spend time or
/// memory unrelated to the size of its input, and a folded token is part of the emitted
/// definition, read on every load, so a larger value is left for execution: 2^20 bits is
/// 315,653 decimal digits. The backend's bound on `^Int` and `<<Int` results is never below this
/// one (asserted below), so the fold never writes a value the backend would not compute.
pub(crate) const MAX_FOLDED_BITS: u64 = 1 << 20;

const _: () = assert!(MAX_FOLDED_BITS <= k_rust_backend::builtin::MAX_INT_RESULT_BITS);

/// Whether the backend loads the folded Float token `token`: it reads a Float token as the
/// canonical text of its value, the exact decimal outside binary32 and binary64, and refuses one
/// whose canonical text is estimated beyond `MAX_FLOAT_CANONICAL_BITS`, so such a result of
/// `hook` is left for execution.
fn loadable_float(hook: &str, token: &str) -> Result<(), Unfolded> {
    float_canonical_bits_estimate(token)
        .map(|_| ())
        .map_err(|refusal| match refusal {
            FloatTextRefusal::BeyondBound { estimate_bits } => Unfolded::TooLarge(format!(
                "the canonical text of the value of hook {hook} is estimated at {estimate_bits} \
                 bits, more than {MAX_FLOAT_CANONICAL_BITS}"
            )),
            refusal @ (FloatTextRefusal::NotALiteral
            | FloatTextRefusal::ZeroFormatField
            | FloatTextRefusal::UncomputedFormat) => Unfolded::Unsupported(format!(
                "the value of hook {hook} has no canonical Float text: {refusal:?}"
            )),
        })
}

/// The size of a value in the unit of `MAX_FOLDED_BITS`.
fn value_bits(value: &Value) -> u64 {
    match value {
        Value::Bool(_) => 1,
        Value::Int(value) => value.bits(),
        Value::String(value) => 8 * value.len() as u64,
        #[cfg(feature = "mpfr-folding")]
        Value::Float(value) => value.bits(),
        #[cfg(not(feature = "mpfr-folding"))]
        Value::Float(value) => 8 * value.len() as u64,
    }
}

fn too_large(hook: &str, bits: impl fmt::Display) -> Unfolded {
    Unfolded::TooLarge(format!(
        "the value of hook {hook} has at least {bits} bits, more than {MAX_FOLDED_BITS}"
    ))
}

impl Unfolded {
    #[cfg(feature = "mpfr-folding")]
    fn message(&self) -> &str {
        match self {
            Self::Undefined(message)
            | Self::Unspecified(message)
            | Self::TooLarge(message)
            | Self::Unsupported(message) => message,
        }
    }
}

impl From<String> for Unfolded {
    fn from(message: String) -> Self {
        Self::Undefined(message)
    }
}

impl From<&str> for Unfolded {
    fn from(message: &str) -> Self {
        Self::Undefined(message.to_owned())
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

fn bool_value(value: &Value) -> Result<bool, Unfolded> {
    match value {
        Value::Bool(value) => Ok(*value),
        Value::Int(_) | Value::String(_) | Value::Float(_) => Err(Unfolded::Unsupported(
            "constant-folding hook expected Bool".into(),
        )),
    }
}
fn int_value(value: &Value) -> Result<BigInt, Unfolded> {
    match value {
        Value::Int(value) => Ok(value.clone()),
        Value::Bool(_) | Value::String(_) | Value::Float(_) => Err(Unfolded::Unsupported(
            "constant-folding hook expected Int".into(),
        )),
    }
}
fn string_value(value: &Value) -> Result<&str, Unfolded> {
    match value {
        Value::String(value) => Ok(value),
        Value::Bool(_) | Value::Int(_) | Value::Float(_) => Err(Unfolded::Unsupported(
            "constant-folding hook expected String or token".into(),
        )),
    }
}
fn unary_bool(values: &[Value], f: impl FnOnce(bool) -> bool) -> Result<Value, Unfolded> {
    let [a] = values else {
        return Err(Unfolded::Unsupported(
            "constant-folding hook expected one argument".into(),
        ));
    };
    Ok(Value::Bool(f(bool_value(a)?)))
}
fn binary_bool(values: &[Value], f: impl FnOnce(bool, bool) -> bool) -> Result<Value, Unfolded> {
    let [a, b] = values else {
        return Err(Unfolded::Unsupported(
            "constant-folding hook expected two arguments".into(),
        ));
    };
    Ok(Value::Bool(f(bool_value(a)?, bool_value(b)?)))
}
fn unary_int(
    values: &[Value],
    f: impl FnOnce(BigInt) -> Result<Value, Unfolded>,
) -> Result<Value, Unfolded> {
    let [a] = values else {
        return Err(Unfolded::Unsupported(
            "constant-folding hook expected one argument".into(),
        ));
    };
    f(int_value(a)?)
}
fn binary_int(
    values: &[Value],
    f: impl FnOnce(BigInt, BigInt) -> Result<BigInt, Unfolded>,
) -> Result<Value, Unfolded> {
    let [a, b] = values else {
        return Err(Unfolded::Unsupported(
            "constant-folding hook expected two arguments".into(),
        ));
    };
    f(int_value(a)?, int_value(b)?).map(Value::Int)
}
fn ternary_int(
    values: &[Value],
    f: impl FnOnce(BigInt, BigInt, BigInt) -> Result<BigInt, Unfolded>,
) -> Result<Value, Unfolded> {
    let [a, b, c] = values else {
        return Err(Unfolded::Unsupported(
            "constant-folding hook expected three arguments".into(),
        ));
    };
    f(int_value(a)?, int_value(b)?, int_value(c)?).map(Value::Int)
}
fn compare_int(values: &[Value], f: impl FnOnce(Ordering) -> bool) -> Result<Value, Unfolded> {
    let [a, b] = values else {
        return Err(Unfolded::Unsupported(
            "constant-folding hook expected two arguments".into(),
        ));
    };
    Ok(Value::Bool(f(int_value(a)?.cmp(&int_value(b)?))))
}
fn unary_string(
    values: &[Value],
    f: impl FnOnce(&str) -> Result<Value, Unfolded>,
) -> Result<Value, Unfolded> {
    let [a] = values else {
        return Err(Unfolded::Unsupported(
            "constant-folding hook expected one argument".into(),
        ));
    };
    f(string_value(a)?)
}
fn binary_string(
    values: &[Value],
    f: impl FnOnce(&str, &str) -> Result<String, Unfolded>,
) -> Result<Value, Unfolded> {
    let [a, b] = values else {
        return Err(Unfolded::Unsupported(
            "constant-folding hook expected two arguments".into(),
        ));
    };
    f(string_value(a)?, string_value(b)?).map(Value::String)
}
fn compare_string(values: &[Value], f: impl FnOnce(Ordering) -> bool) -> Result<Value, Unfolded> {
    let [a, b] = values else {
        return Err(Unfolded::Unsupported(
            "constant-folding hook expected two arguments".into(),
        ));
    };
    Ok(Value::Bool(f(string_value(a)?.cmp(string_value(b)?))))
}

/// A parameter that must be a natural number (a shift amount, an exponent, a bit index or
/// length, a count): a negative one makes the hook undefined.
fn natural<'a>(value: &'a BigInt, hook: &str) -> Result<&'a BigInt, Unfolded> {
    if value.is_negative() {
        return Err(Unfolded::Undefined(format!(
            "Argument to hook {hook} out of range. Expected a nonnegative integer."
        )));
    }
    Ok(value)
}
/// A natural number as a length or count; one beyond `usize` saturates, and every caller reads
/// the saturated value as larger than any string or bit length it compares it with.
fn saturating_usize(value: &BigInt) -> usize {
    value.to_usize().unwrap_or(usize::MAX)
}
fn checked_div(a: BigInt, b: BigInt, euclidean: bool) -> Result<BigInt, Unfolded> {
    if b.is_zero() {
        return Err("Division by zero.".into());
    }
    if !euclidean {
        return Ok(a / b);
    }
    let rem = checked_rem(a.clone(), b.clone(), true)?;
    Ok((a - rem) / b)
}
fn checked_rem(a: BigInt, b: BigInt, euclidean: bool) -> Result<BigInt, Unfolded> {
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
/// `base ^Int exponent`, the exponentiation of two integers: the powers of 1 and -1 for every
/// exponent (for a negative one, `b^-n` is the integer `1 / b^n` exactly when `|b| = 1`), those of
/// any other base for every natural exponent, and none for a negative one, where no integer is the
/// power. The powers of 0, 1 and -1 stay small, and another base's power is computed only when it
/// fits the bound, since |base|^exponent has at least (bits - 1) * exponent + 1 bits (the result
/// is checked again when it is folded).
fn int_pow(base: BigInt, exponent: BigInt) -> Result<BigInt, Unfolded> {
    if base.magnitude().is_one() {
        // The parity of the two's complement, also for a negative exponent.
        let odd = (&exponent & BigInt::one()).is_one();
        return Ok(if base.is_negative() && odd {
            base
        } else {
            BigInt::one()
        });
    }
    let exponent = natural(&exponent, "INT.pow")?;
    if exponent.is_zero() {
        return Ok(BigInt::one());
    }
    if base.magnitude().bits() <= 1 {
        let odd = (exponent & BigInt::one()).is_one();
        return Ok(if base.is_negative() && !odd {
            BigInt::one()
        } else {
            base
        });
    }
    let minimum = (base.bits() - 1)
        .saturating_mul(exponent.to_u64().unwrap_or(u64::MAX))
        .saturating_add(1);
    if minimum > MAX_FOLDED_BITS {
        return Err(too_large("INT.pow", minimum));
    }
    let exponent = exponent
        .to_u32()
        .expect("an exponent within the bound fits 32 bits");
    Ok(base.pow(exponent))
}
/// `value <<Int amount` for every natural amount: zero stays zero, and another value gains
/// `amount` bits.
fn int_shl(value: BigInt, amount: BigInt) -> Result<BigInt, Unfolded> {
    let amount = natural(&amount, "INT.shl")?;
    if value.is_zero() {
        return Ok(value);
    }
    let bits = value
        .bits()
        .saturating_add(amount.to_u64().unwrap_or(u64::MAX));
    if bits > MAX_FOLDED_BITS {
        return Err(too_large("INT.shl", bits));
    }
    Ok(value << saturating_usize(amount))
}
/// `value >>Int amount`, the floor of `value / 2^amount`: 0 or -1 once the amount reaches the
/// value's bit length, however large it is.
fn int_shr(value: BigInt, amount: &BigInt) -> BigInt {
    match amount.to_u64().filter(|amount| *amount <= value.bits()) {
        Some(amount) => value >> amount,
        None if value.is_negative() => -BigInt::one(),
        None => BigInt::zero(),
    }
}
fn int_log2(mut value: BigInt) -> Result<Value, Unfolded> {
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
/// `bitRangeInt(I, IDX, LEN)` is `(I >>Int IDX) modInt (1 <<Int LEN)` (`domains.md`). A
/// nonnegative `I >>Int IDX` shorter than `LEN` bits is its own residue; otherwise the residue
/// has at most `LEN` bits.
fn int_bit_range(value: BigInt, index: BigInt, length: BigInt) -> Result<BigInt, Unfolded> {
    let shifted = int_shr(value, natural(&index, "INT.bitRange")?);
    let length = natural(&length, "INT.bitRange")?;
    let length = length.to_u64().unwrap_or(u64::MAX);
    if !shifted.is_negative() && shifted.bits() <= length {
        return Ok(shifted);
    }
    if length > MAX_FOLDED_BITS {
        return Err(too_large("INT.bitRange", length));
    }
    Ok(shifted & ((BigInt::one() << length) - 1u8))
}
/// `signExtendBitRangeInt(I, IDX, LEN)` is `(bitRangeInt(I, IDX, LEN) +Int (1 <<Int (LEN -Int
/// 1))) modInt (1 <<Int LEN) -Int (1 <<Int (LEN -Int 1))` (`domains.md`): the residue of
/// `I >>Int IDX` modulo 2^LEN in [-2^(LEN - 1), 2^(LEN - 1)), which is `I >>Int IDX` itself when
/// that already lies there. A zero length shifts by -1 and is undefined.
fn int_sign_extend_bit_range(
    value: BigInt,
    index: BigInt,
    length: BigInt,
) -> Result<BigInt, Unfolded> {
    let shifted = int_shr(value, natural(&index, "INT.signExtendBitRange")?);
    let length = natural(&length, "INT.signExtendBitRange")?;
    let length = length.to_u64().unwrap_or(u64::MAX);
    if length == 0 {
        return Err(Unfolded::Undefined(
            "Argument to hook INT.signExtendBitRange out of range. Expected a positive length."
                .into(),
        ));
    }
    // A value of fewer than LEN bits in magnitude, or -2^(LEN - 1), lies in the signed range.
    if shifted.bits() < length {
        return Ok(shifted);
    }
    // Otherwise LEN is at most the magnitude's bit length, so the masks stay that small.
    let modulus = BigInt::one() << length;
    let half = BigInt::one() << (length - 1);
    let residue = ((shifted + &half) % &modulus + &modulus) % &modulus;
    Ok(residue - half)
}
/// `A ^%Int B C` is `(A ^Int B) mod C`, the Euclidean remainder (its `smt-hook`), which lies in
/// [0, |C|) and is therefore the same for C and -C. It is undefined for a zero C, and for a
/// negative B wherever `A ^Int B` is (every A but 1 and -1, `int_pow`).
fn int_powmod(a: BigInt, exponent: BigInt, modulus: BigInt) -> Result<BigInt, Unfolded> {
    if modulus.is_zero() {
        return Err("Argument to hook INT.powmod is invalid. The modulus is zero.".into());
    }
    let modulus = modulus.abs();
    if exponent.is_negative() {
        if !a.magnitude().is_one() {
            return Err(
                "Argument to hook INT.powmod is invalid. The power is not an integer.".into(),
            );
        }
        let power = int_pow(a, exponent)?;
        return Ok(((power % &modulus) + &modulus) % modulus);
    }
    Ok(a.modpow(&exponent, &modulus))
}

fn string_chr(value: BigInt) -> Result<Value, Unfolded> {
    let Some(value) = value.to_u32().filter(|value| *value <= 0x10ffff) else {
        return Err(
            "Argument to hook STRING.chr out of range. Expected a number between 0 and 1114111."
                .into(),
        );
    };
    // Whether a String holds a surrogate the definition does not settle: K's string syntax
    // writes one, KORE's string literals cannot.
    let Some(value) = char::from_u32(value) else {
        return Err(Unfolded::Unspecified(format!(
            "chrChar({value}) is a surrogate code point, which K's string syntax writes and \
             KORE's string literals cannot"
        )));
    };
    Ok(Value::String(value.to_string()))
}
fn string_ord(value: &str) -> Result<Value, Unfolded> {
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
/// `substrString(S, START, END)`: the characters in `[START..END)` on the valid indices
/// `0 <= START <= END <= lengthString(S)`. The hook is `total`, and `domains.md` gives it no
/// value on other indices.
fn string_substr(values: &[Value]) -> Result<Value, Unfolded> {
    let [text, start, end] = values else {
        return Err(Unfolded::Unsupported(
            "constant-folding hook expected three arguments".into(),
        ));
    };
    let chars = string_value(text)?.chars().collect::<Vec<_>>();
    let (start, end) = (int_value(start)?, int_value(end)?);
    if start.is_negative() || start > end || end > BigInt::from(chars.len()) {
        return Err(Unfolded::Unspecified(format!(
            "substrString from {start} to {end} on a string of length {}, outside the valid indices",
            chars.len()
        )));
    }
    let (start, end) = (saturating_usize(&start), saturating_usize(&end));
    Ok(Value::String(chars[start..end].iter().collect()))
}
fn string_find(values: &[Value], reverse: bool, any_char: bool) -> Result<Value, Unfolded> {
    let [haystack, needles, index] = values else {
        return Err(Unfolded::Unsupported(
            "constant-folding hook expected three arguments".into(),
        ));
    };
    let haystack = string_value(haystack)?;
    let needles = string_value(needles)?;
    let index = int_value(index)?;
    let chars = haystack.chars().collect::<Vec<_>>();
    // `findString(S, N, I)` is the first occurrence starting at or after index I, and
    // `rfindString` the last starting at or before it, for every integer I (`domains.md`; the
    // `findChar` and `rfindChar` equations pass I to them unchanged). A negative I therefore
    // searches `find` from 0 and leaves `rfind` no candidate; an I past the end leaves `find`
    // none and searches `rfind` from the end.
    let index = if reverse {
        if index.is_negative() {
            return Ok(Value::Int((-1).into()));
        }
        saturating_usize(&index).min(chars.len())
    } else {
        if index > BigInt::from(chars.len()) {
            return Ok(Value::Int((-1).into()));
        }
        saturating_usize(&index.max(BigInt::zero()))
    };
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
fn parse_int(value: &str, radix: u32) -> Result<Value, Unfolded> {
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
fn radix(value: &Value) -> Result<u32, Unfolded> {
    let radix = int_value(value)?
        .to_u32()
        .filter(|value| (2..=36).contains(value))
        .ok_or_else(|| {
            "Argument to string/base conversion out of range. Expected a number between 2 and 36."
                .to_owned()
        })?;
    Ok(radix)
}
fn string_to_base(values: &[Value]) -> Result<Value, Unfolded> {
    let [text, base] = values else {
        return Err(Unfolded::Unsupported(
            "constant-folding hook expected two arguments".into(),
        ));
    };
    parse_int(string_value(text)?, radix(base)?)
}
fn base_to_string(values: &[Value]) -> Result<Value, Unfolded> {
    let [value, base] = values else {
        return Err(Unfolded::Unsupported(
            "constant-folding hook expected two arguments".into(),
        ));
    };
    Ok(Value::String(int_value(value)?.to_str_radix(radix(base)?)))
}
fn replace_string(
    values: &[Value],
    count_index: Option<usize>,
    first: bool,
) -> Result<Value, Unfolded> {
    let [haystack, needle, replacement, ..] = values else {
        return Err(Unfolded::Unsupported(
            "constant-folding hook expected at least three arguments".into(),
        ));
    };
    let haystack = string_value(haystack)?;
    let needle = string_value(needle)?;
    let replacement = string_value(replacement)?;
    let count = if first {
        1
    } else if let Some(index) = count_index {
        saturating_usize(natural(&int_value(&values[index])?, "STRING.replace")?)
    } else {
        usize::MAX
    };
    if count == 0 {
        return Ok(Value::String(haystack.to_owned()));
    }
    let hook = match (first, count_index) {
        (true, _) => "STRING.replaceFirst",
        (false, Some(_)) => "STRING.replace",
        (false, None) => "STRING.replaceAll",
    };
    // The result's length in bytes, from the number of replacements, checked before it is built.
    let fits = |replaced: usize, removed: usize| {
        let bytes = (haystack.len() as u64 - removed as u64)
            .saturating_add((replaced as u64).saturating_mul(replacement.len() as u64));
        let bits = bytes.saturating_mul(8);
        if bits > MAX_FOLDED_BITS {
            Err(too_large(hook, bits))
        } else {
            Ok(())
        }
    };
    if needle.is_empty() {
        // `domains.md` defines `replace` by finding the needle from index 0 and recursing on the
        // rest of the haystack after it. An empty needle is found at 0 and leaves the whole
        // haystack as the rest, so `replace` and `replaceFirst` put `count` copies of the
        // replacement in front. `replaceAll` replaces `countAllOccurrences` of them, which has
        // no value for an empty needle (`count_occurrences`).
        if count_index.is_none() && !first {
            return Err(Unfolded::Unspecified(
                "replaceAll with an empty needle replaces countAllOccurrences(S, \"\") copies, which has no value".into(),
            ));
        }
        fits(count, 0)?;
        return Ok(Value::String(replacement.repeat(count) + haystack));
    }
    let occurrences = haystack
        .match_indices(needle)
        .take(count)
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    fits(occurrences.len(), occurrences.len() * needle.len())?;
    let mut out = String::new();
    let mut rest = 0;
    // Invariant: `out` holds `haystack[..rest]` with the occurrences before `rest` replaced; each iteration consumes one of the at most `count` leftmost non-overlapping occurrences.
    for index in occurrences {
        out.push_str(&haystack[rest..index]);
        out.push_str(replacement);
        rest = index + needle.len();
    }
    out.push_str(&haystack[rest..]);
    Ok(Value::String(out))
}
/// `countAllOccurrences(S, N)`, the number of leftmost non-overlapping occurrences of N in S.
/// The hook is `total`, and for an empty needle `domains.md` defines it by
/// `countAllOccurrences(S, "") = 1 +Int countAllOccurrences(S, "")`, which no integer satisfies,
/// so the definition gives it no value.
fn count_occurrences(values: &[Value]) -> Result<Value, Unfolded> {
    let [haystack, needle] = values else {
        return Err(Unfolded::Unsupported(
            "constant-folding hook expected two arguments".into(),
        ));
    };
    let haystack = string_value(haystack)?;
    let needle = string_value(needle)?;
    if needle.is_empty() {
        return Err(Unfolded::Unspecified(
            "countAllOccurrences with an empty needle has no value".into(),
        ));
    }
    Ok(Value::Int(haystack.match_indices(needle).count().into()))
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

    /// `b ^Int -n` is the integer `1 / b^n` exactly when `|b| = 1`: the powers of 1 and -1 fold
    /// for every exponent, and those of any other base are undefined for a negative one.
    #[test]
    fn folds_powers_of_unit_bases_for_every_exponent() {
        for (base, exponent, expected) in [(1, -1, 1), (1, -8, 1), (-1, -1, -1), (-1, -2, 1)] {
            assert_eq!(
                int_pow(int(base), int(exponent)),
                Ok(int(expected)),
                "{base} ^Int {exponent}"
            );
        }
        let huge = -(BigInt::one() << 100u32) - 1u8;
        assert_eq!(int_pow(int(-1), huge), Ok(int(-1)));
        for (base, exponent) in [(0, -1), (2, -1), (-3, -2)] {
            assert!(
                matches!(
                    int_pow(int(base), int(exponent)),
                    Err(Unfolded::Undefined(_))
                ),
                "{base} ^Int {exponent}"
            );
        }
    }

    /// `A ^%Int B C` is `(A ^Int B) mod C`: with a negative B, the remainder of the power of 1 or
    /// -1, and undefined for every other base, whose power is not an integer, even where it is
    /// invertible modulo C. The remainder of -1 is C - 1.
    #[test]
    fn powmod_of_a_negative_exponent_is_the_remainder_of_a_unit_power() {
        assert_eq!(int_powmod(int(-1), int(-1), int(5)), Ok(int(4)));
        assert_eq!(int_powmod(int(-1), int(-3), int(7)), Ok(int(6)));
        assert_eq!(int_powmod(int(-1), int(-2), int(7)), Ok(int(1)));
        assert_eq!(int_powmod(int(1), int(-1), int(7)), Ok(int(1)));
        assert_eq!(int_powmod(int(1), int(-1), int(1)), Ok(int(0)));
        for (base, exponent) in [(-2, -1), (-2, -3), (3, -1), (0, -1)] {
            assert!(
                matches!(
                    int_powmod(int(base), int(exponent), int(7)),
                    Err(Unfolded::Undefined(_))
                ),
                "{base} ^%Int {exponent} 7"
            );
        }
    }

    /// The Euclidean remainder modulo -C is the remainder modulo C, so a negative modulus folds
    /// like its absolute value; only a zero modulus is undefined.
    #[test]
    fn powmod_reduces_by_the_magnitude_of_a_negative_modulus() {
        // The remainder is Euclidean whatever the sign of the power, as the `smt-hook`
        // `(mod (^ #1 #2) #3)` states it to the solver: (-2)^3 = -8 is 2 modulo 5.
        assert_eq!(int_powmod(int(-2), int(3), int(5)), Ok(int(2)));
        assert_eq!(int_powmod(int(-3), int(2), int(5)), Ok(int(4)));
        assert_eq!(int_powmod(int(2), int(3), int(-5)), Ok(int(3)));
        assert_eq!(int_powmod(int(-2), int(3), int(-5)), Ok(int(2)));
        assert_eq!(int_powmod(int(-1), int(-1), int(-7)), Ok(int(6)));
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

    /// `chrChar` is folded on every code point outside the surrogates. Whether a String holds
    /// a surrogate code point the definition does not settle, so that value is unspecified; a
    /// number that is no code point has no character.
    #[test]
    fn folds_chr_only_on_code_points_outside_the_surrogates() {
        for (code_point, expected) in [(0x41, "A"), (0xd7ff, "\u{d7ff}"), (0xe000, "\u{e000}")] {
            assert!(
                matches!(string_chr(int(code_point)), Ok(Value::String(text)) if text == expected),
                "chrChar({code_point})"
            );
        }
        // Whether a String holds a surrogate the definition does not settle: unspecified.
        for code_point in [0xd800, 0xdfff] {
            assert!(
                matches!(string_chr(int(code_point)), Err(Unfolded::Unspecified(_))),
                "chrChar({code_point})"
            );
        }
        // A number outside the code points is no character: undefined.
        for code_point in [-1, 0x11_0000] {
            assert!(
                matches!(string_chr(int(code_point)), Err(Unfolded::Undefined(_))),
                "chrChar({code_point})"
            );
        }
    }

    /// `substrString` is folded on `0 <= start <= end <= length`, empty ranges included; it is
    /// `total`, and `domains.md` gives it no value on other indices, so those stay unfolded.
    #[test]
    fn folds_substrings_only_on_valid_indices() {
        let substring = |start: BigInt, end: BigInt| {
            string_substr(&[
                Value::String("héllo".into()),
                Value::Int(start),
                Value::Int(end),
            ])
        };
        for (start, end, expected) in [(0, 0, ""), (5, 5, ""), (1, 3, "él"), (0, 5, "héllo")] {
            assert!(
                matches!(substring(int(start), int(end)), Ok(Value::String(text)) if text == expected),
                "substrString(héllo, {start}, {end})"
            );
        }
        let huge = BigInt::one() << 100u32;
        for (start, end) in [
            (int(-2), int(3)),
            (int(1), int(10)),
            (int(3), int(1)),
            (int(-3), int(-1)),
            (int(6), int(6)),
            (huge.clone(), huge),
        ] {
            assert!(
                matches!(
                    substring(start.clone(), end.clone()),
                    Err(Unfolded::Unspecified(_))
                ),
                "substrString(héllo, {start}, {end})"
            );
        }
    }

    /// The search hooks find the first occurrence at or after their index, or the last at or
    /// before it, for every integer index.
    #[test]
    fn searches_from_any_integer_index() {
        let huge = BigInt::one() << 100u32;
        let found = |hook: &str, haystack: &str, needles: &str, index: BigInt| {
            let (reverse, any_char) = match hook {
                "find" => (false, false),
                "rfind" => (true, false),
                "findChar" => (false, true),
                _ => (true, true),
            };
            let values = [
                Value::String(haystack.into()),
                Value::String(needles.into()),
                Value::Int(index),
            ];
            match string_find(&values, reverse, any_char) {
                Ok(Value::Int(position)) => position,
                other => panic!("{hook}({haystack:?}, {needles:?}) gave {other:?}"),
            }
        };
        assert_eq!(found("find", "hello", "l", int(-5)), int(2));
        assert_eq!(found("find", "hello", "", int(-1)), int(0));
        assert_eq!(found("find", "hello", "", int(5)), int(5));
        assert_eq!(found("find", "hello", "", int(6)), int(-1));
        assert_eq!(found("find", "hello", "h", huge.clone()), int(-1));
        assert_eq!(found("rfind", "hello", "l", int(100)), int(3));
        assert_eq!(found("rfind", "hello", "", huge.clone()), int(5));
        assert_eq!(found("rfind", "hello", "h", int(-1)), int(-1));
        assert_eq!(found("rfind", "hello", "", -huge.clone()), int(-1));
        assert_eq!(found("findChar", "hello", "ol", int(-3)), int(2));
        assert_eq!(found("findChar", "hello", "ol", huge.clone()), int(-1));
        assert_eq!(found("rfindChar", "hello", "he", huge.clone()), int(1));
        assert_eq!(found("rfindChar", "hello", "he", int(-1)), int(-1));
    }

    /// An empty needle occurs at index 0 with the whole haystack after it, so each replacement
    /// `replace` and `replaceFirst` make goes in front. `countAllOccurrences` of an empty needle,
    /// and so `replaceAll` with one, have no value.
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
        assert!(matches!(
            replace_string(&arguments(2), None, false),
            Err(Unfolded::Unspecified(_))
        ));
        assert!(matches!(
            count_occurrences(&[text("ab"), text("")]),
            Err(Unfolded::Unspecified(_))
        ));
        assert!(matches!(
            count_occurrences(&[text("abab"), text("ab")]),
            Ok(Value::Int(count)) if count == int(2)
        ));
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

    /// The fold writes values of at most 2^20 bits and leaves larger ones, checking the operations
    /// whose result can outgrow their arguments before computing them.
    #[test]
    fn folds_results_only_up_to_the_result_bound() {
        let bound = 1u32 << 20;
        assert_eq!(MAX_FOLDED_BITS, u64::from(bound));
        let too_large =
            |result: Result<BigInt, Unfolded>| matches!(result, Err(Unfolded::TooLarge(_)));
        assert_eq!(
            int_pow(int(2), (bound - 1).into()).map(|value| value.bits()),
            Ok(u64::from(bound))
        );
        assert!(too_large(int_pow(int(2), bound.into())));
        assert!(too_large(int_pow(int(-3), bound.into())));
        assert_eq!(
            int_shl(int(1), (bound - 1).into()).map(|value| value.bits()),
            Ok(u64::from(bound))
        );
        assert!(too_large(int_shl(int(1), bound.into())));
        let range = |value: i64, length: u32| int_bit_range(int(value), int(0), length.into());
        assert_eq!(range(5, i32::MAX as u32), Ok(int(5)));
        assert_eq!(
            range(-1, bound).map(|value| value.bits()),
            Ok(u64::from(bound))
        );
        assert!(too_large(range(-1, bound + 1)));
        let extend =
            |value: i64, length: u32| int_sign_extend_bit_range(int(value), int(0), length.into());
        assert_eq!(extend(-1, i32::MAX as u32), Ok(int(-1)));
        assert_eq!(extend(5, i32::MAX as u32), Ok(int(5)));
        assert_eq!(extend(5, 3), Ok(int(-3)));

        let text = |value: &str| Value::String(value.into());
        let replaced = |values: &[Value]| match replace_string(values, Some(3), false) {
            Ok(Value::String(text)) => Ok(text.len()),
            Err(unfolded) => Err(unfolded),
            other => panic!("{other:?}"),
        };
        let prepend = |count: usize| [text(""), text(""), text("x"), Value::Int(count.into())];
        assert_eq!(replaced(&prepend(1 << 17)), Ok(1 << 17));
        assert!(matches!(
            replaced(&prepend((1 << 17) + 1)),
            Err(Unfolded::TooLarge(_))
        ));
        let wide = "x".repeat(1 << 16);
        let every = |haystack: &str| [text(haystack), text("a"), text(&wide), Value::Int(int(9))];
        assert_eq!(replaced(&every("aa")), Ok(1 << 17));
        assert!(matches!(
            replaced(&every("aaa")),
            Err(Unfolded::TooLarge(_))
        ));

        assert_eq!(value_bits(&Value::String("ab".into())), 16);
        assert_eq!(value_bits(&Value::Int(int(-8))), 4);
    }

    /// A shift amount, exponent, bit index or length, or replacement count is any natural number:
    /// the results that stay small are folded however large the parameter, and a negative one
    /// is undefined.
    #[test]
    fn folds_parameters_of_any_magnitude() {
        let huge = BigInt::one() << 100u32;
        for amount in [
            BigInt::from(i32::MAX) + 1,
            BigInt::from(u64::MAX),
            huge.clone(),
        ] {
            assert_eq!(int_shr(int(12345), &amount), int(0));
            assert_eq!(int_shr(int(-12345), &amount), int(-1));
            assert_eq!(int_shl(int(0), amount.clone()), Ok(int(0)));
            assert!(matches!(
                int_shl(int(1), amount.clone()),
                Err(Unfolded::TooLarge(_))
            ));
            assert_eq!(int_pow(int(0), amount.clone()), Ok(int(0)));
            assert_eq!(int_pow(int(1), amount.clone()), Ok(int(1)));
            let odd = (&amount & BigInt::one()).is_one();
            let (even, odd) = if odd {
                (&amount + 1u8, amount.clone())
            } else {
                (amount.clone(), &amount + 1u8)
            };
            assert_eq!(int_pow(int(-1), even), Ok(int(1)));
            assert_eq!(int_pow(int(-1), odd), Ok(int(-1)));
            assert!(matches!(
                int_pow(int(2), amount.clone()),
                Err(Unfolded::TooLarge(_))
            ));
            assert_eq!(
                int_bit_range(int(5), amount.clone(), amount.clone()),
                Ok(int(0))
            );
            assert_eq!(int_bit_range(int(5), int(0), amount.clone()), Ok(int(5)));
            assert!(matches!(
                int_bit_range(int(-1), int(0), amount.clone()),
                Err(Unfolded::TooLarge(_))
            ));
            assert_eq!(
                int_sign_extend_bit_range(int(-6), int(1), amount.clone()),
                Ok(int(-3))
            );
            assert_eq!(
                int_sign_extend_bit_range(int(6), amount.clone(), int(4)),
                Ok(int(0))
            );
        }
        assert_eq!(int_pow(int(3), int(0)), Ok(int(1)));
        assert_eq!(int_shr(int(-7), &int(1)), int(-4));
        assert!(matches!(
            int_pow(int(2), int(-1)),
            Err(Unfolded::Undefined(_))
        ));
        assert!(matches!(
            int_shl(int(2), int(-1)),
            Err(Unfolded::Undefined(_))
        ));
        assert!(matches!(
            int_bit_range(int(2), int(-1), int(3)),
            Err(Unfolded::Undefined(_))
        ));

        let text = |value: &str| Value::String(value.into());
        assert!(matches!(
            replace_string(&[text("abab"), text("b"), text("x"), Value::Int(huge)], Some(3), false),
            Ok(Value::String(text)) if text == "axax"
        ));
        assert!(matches!(
            replace_string(
                &[text("ab"), text("b"), text("x"), Value::Int(int(-1))],
                Some(3),
                false
            ),
            Err(Unfolded::Undefined(_))
        ));
    }

    /// The radix "can be anywhere between 2 and 36" (`domains.md`), and both conversions are
    /// partial: outside that range they are undefined, and the fold leaves them for execution.
    #[test]
    fn base_conversions_outside_two_through_thirty_six_are_undefined() {
        for base in [-2, 0, 1, 37, 1 << 40] {
            let base = Value::Int(int(base));
            assert!(
                matches!(
                    string_to_base(&[Value::String("ff".into()), base.clone()]),
                    Err(Unfolded::Undefined(_))
                ),
                "String2Base(ff, {base:?})"
            );
            assert!(
                matches!(
                    base_to_string(&[Value::Int(int(255)), base.clone()]),
                    Err(Unfolded::Undefined(_))
                ),
                "Base2String(255, {base:?})"
            );
        }
        assert!(matches!(
            base_to_string(&[Value::Int(int(255)), Value::Int(int(36))]),
            Ok(Value::String(text)) if text == "73"
        ));
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
        // A radix numeral carries the same sign, so `String2Base` reads back every
        // `Base2String`, negative ones included.
        assert_eq!(parsed("+fF", 16), Some(int(255)));
        assert_eq!(parsed("-z", 36), Some(int(-35)));
        for text in ["+", "-", "+-1", "--1", "1-"] {
            assert_eq!(parsed(text, 16), None, "{text:?}");
        }
    }
}

#[cfg(test)]
#[path = "constant_folding_oracle.rs"]
mod oracle;
