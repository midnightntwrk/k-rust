//! `k::bits!("00 yyy 100")`: bit-field templates, pattern sugar of `Int`.
//!
//! A template of width `w` matches exactly the integers `n` with
//! `0 <= n < 2^w` whose fixed bits are as written; a field letter names
//! `bitRangeInt(n, offset, length)`. The template is sugar for its long form,
//! which this module writes into the sentence's fn item before the item is
//! parsed:
//!
//! - the template becomes a variable: the alias of `op @ k::bits!(..)`, or a
//!   hidden generated binder authors cannot write (it holds the reserved
//!   marker); a template without free bits becomes its decimal literal;
//! - the sentence's `requires` gains, before any authored condition,
//!   `X >= 0 && X < 2^w` and one `bit_range(X, o, l) == v` per maximal run of
//!   fixed bits within a space-separated group, most significant first;
//! - every field occurrence in the `requires`, `ensures`, and result becomes
//!   `X.bit_range::<Int>(o, l)`.
//!
//! The macro and the collector both run this rewrite on the same authored
//! tokens, so the generated tokens, which carry the template's span, have the
//! same provenance on both sides.
//!
//! `k::bits!(value, "..")` is the template as a `Bool` test, in any term: the
//! range and the fixed-run equalities of the pattern's guard, on `value`, in
//! the guard's order ([`expand_bit_tests`]).

use std::cell::RefCell;
use std::collections::BTreeMap;

use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{ToTokens, quote_spanned};
use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::visit_mut::VisitMut;
use syn::{Attribute, Expr, FnArg, Ident, ItemFn, LitInt, LitStr, Macro, Pat, Path, Token};

use crate::{SyntaxError, SyntaxErrorKind, TokenRange};

/// The prefix of a hidden template binder. It holds the reserved marker, so
/// no authored binder may spell it (`validate_authored_binder`).
pub(crate) const GENERATED_BINDER_PREFIX: &str = "__krs_bits_";

/// The widest template, in bits: its literals are computed in `u128`.
const MAXIMUM_WIDTH: u32 = 128;

/// One run of adjacent fixed bits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct FixedRun {
    /// Index of the run's least significant bit.
    pub offset: u32,
    /// Number of bits.
    pub length: u32,
    /// The run's bits read as an unsigned number.
    pub value: u128,
}

/// One named field: a contiguous bit range.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct BitField {
    /// The field letter.
    pub name: char,
    /// Index of the field's least significant bit.
    pub offset: u32,
    /// Number of bits.
    pub length: u32,
}

/// A parsed bit template.
#[derive(Clone, Debug)]
pub(crate) struct BitTemplate {
    width: u32,
    /// Fixed runs, most significant first.
    runs: Vec<FixedRun>,
    /// Fields, most significant first.
    fields: Vec<BitField>,
    span: Span,
}

impl BitTemplate {
    /// Parses the string literal of `k::bits!("..")`.
    pub(crate) fn parse(literal: &LitStr) -> Result<Self, SyntaxError> {
        if !literal.suffix().is_empty() {
            return Err(invalid(
                "a bit template is a plain string literal, without a suffix".to_owned(),
                literal.span(),
            ));
        }
        let text = literal.value();
        // Each bit character, most significant first, with its group: the
        // number of spaces before it.
        let mut bits = Vec::new();
        let mut group = 0_usize;
        for (index, character) in text.chars().enumerate() {
            match character {
                ' ' => group += 1,
                '0' | '1' | '_' | 'a'..='z' => bits.push((group, character)),
                _ => {
                    return Err(invalid(
                        format!(
                            "character {index} of the bit template, `{}`, is not a bit: write `0` or `1` for a fixed bit, `_` for a bit that may be either, a lowercase letter for a field bit, and spaces to separate groups",
                            character.escape_default()
                        ),
                        literal.span(),
                    ));
                }
            }
        }
        if bits.is_empty() {
            return Err(invalid(
                "a bit template needs at least one bit; its width is the number of `0`, `1`, `_`, and field letters".to_owned(),
                literal.span(),
            ));
        }
        let width = u32::try_from(bits.len())
            .ok()
            .filter(|width| *width <= MAXIMUM_WIDTH)
            .ok_or_else(|| {
                invalid(
                    format!(
                        "a bit template is at most {MAXIMUM_WIDTH} bits wide; this one has {}",
                        bits.len()
                    ),
                    literal.span(),
                )
            })?;
        let position = |index: usize| width - 1 - u32::try_from(index).unwrap_or(u32::MAX);
        let mut runs = Vec::<FixedRun>::new();
        let mut fields = Vec::<BitField>::new();
        let mut previous: Option<(usize, char)> = None;
        for (index, (group, character)) in bits.iter().enumerate() {
            let bit = position(index);
            match character {
                // A run of fixed bits ends at a space as well: the guard's
                // terms then follow the author's grouping, so templates
                // written on one grid (`xx yyy zzz`) test the same terms.
                '0' | '1' => {
                    let value = u128::from(*character == '1');
                    match runs.last_mut() {
                        Some(run) if matches!(previous, Some((before, '0' | '1')) if before == *group) =>
                        {
                            run.offset = bit;
                            run.length += 1;
                            run.value = (run.value << 1) | value;
                        }
                        _ => runs.push(FixedRun {
                            offset: bit,
                            length: 1,
                            value,
                        }),
                    }
                }
                '_' => {}
                letter => {
                    if previous.is_some_and(|(_, before)| before == *letter) {
                        let field = fields.last_mut().expect("the previous bit opened a field");
                        field.offset = bit;
                        field.length += 1;
                    } else if fields.iter().any(|field| field.name == *letter) {
                        return Err(invalid(
                            format!(
                                "field `{letter}` is split: its bits are not adjacent, and a field is one contiguous bit range; name each part with its own letter and combine them in the result"
                            ),
                            literal.span(),
                        ));
                    } else {
                        fields.push(BitField {
                            name: *letter,
                            offset: bit,
                            length: 1,
                        });
                    }
                }
            }
            previous = Some((*group, *character));
        }
        Ok(Self {
            width,
            runs,
            fields,
            span: literal.span(),
        })
    }

    /// The template's width in bits.
    pub(crate) const fn width(&self) -> u32 {
        self.width
    }

    /// The fixed runs, most significant first.
    #[cfg(test)]
    pub(crate) fn runs(&self) -> &[FixedRun] {
        &self.runs
    }

    /// The fields, most significant first.
    pub(crate) fn fields(&self) -> &[BitField] {
        &self.fields
    }

    /// The one integer the template matches, when every bit is fixed.
    pub(crate) fn literal(&self) -> Option<u128> {
        let (mask, value) = self.cube();
        (mask == low_ones(self.width)).then_some(value)
    }

    /// The mask of the fixed bits and their values, as `(mask, value)`.
    pub(crate) fn cube(&self) -> (u128, u128) {
        self.runs.iter().fold((0, 0), |(mask, value), run| {
            let ones = low_ones(run.length) << run.offset;
            (mask | ones, value | (run.value << run.offset))
        })
    }

    /// The template's guard on `subject`: the range, then one equality per
    /// fixed run, most significant first.
    /// Every generated token carries `span`; the pattern's guard passes a
    /// subject spanned alike, so its provenance range lies where the
    /// sentence's condition starts (see [`desugar`]).
    fn guard(&self, subject: &TokenStream, span: Span) -> TokenStream {
        let bound = LitInt::new(&power_of_two(self.width), span);
        let zero = LitInt::new("0", span);
        let mut guard = quote_spanned! {span=>
            #subject.ge::<Int>(#zero) && #subject.lt::<Int>(#bound)
        };
        for run in &self.runs {
            let offset = LitInt::new(&run.offset.to_string(), span);
            let length = LitInt::new(&run.length.to_string(), span);
            let value = LitInt::new(&run.value.to_string(), span);
            guard.extend(quote_spanned! {span=>
                && #subject.bit_range::<Int>(#offset, #length).eq::<Int>(#value)
            });
        }
        guard
    }
}

const fn low_ones(length: u32) -> u128 {
    if length >= 128 {
        u128::MAX
    } else {
        (1 << length) - 1
    }
}

/// `2^exponent` in decimal, for any exponent up to [`MAXIMUM_WIDTH`].
fn power_of_two(exponent: u32) -> String {
    // Little-endian decimal digits.
    let mut digits = vec![1_u8];
    for _ in 0..exponent {
        let mut carry = 0;
        for digit in &mut digits {
            let doubled = *digit * 2 + carry;
            *digit = doubled % 10;
            carry = doubled / 10;
        }
        if carry > 0 {
            digits.push(carry);
        }
    }
    digits
        .iter()
        .rev()
        .map(|digit| char::from(b'0' + digit))
        .collect()
}

fn invalid(reason: String, span: Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::InvalidBitTemplate { reason }, span)
}

fn position_error(reason: &str, span: Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::BitTemplatePosition {
            reason: reason.to_owned(),
        },
        span,
    )
}

fn collision(reason: String, span: Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::BitFieldCollision { reason }, span)
}

/// Whether `path` names `k::bits!`.
pub(crate) fn is_bits_macro(path: &Path) -> bool {
    crate::path::is_plain_path(path)
        && path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "bits")
}

/// The error for `k::bits!` where no pattern is matched.
pub(crate) fn misplaced(span: Span) -> SyntaxError {
    position_error(
        "`k::bits!` is a pattern: it matches an `Int` argument of a rule's or equation's left-hand side (a `k::equations!` row, a `#[k::equation]` or `#[k::rule]` fn, or a `k::rules!` clause), and its fields name parts of the matched value in the `requires` and the result; it is not a term, a guard, or a cell pattern. To test a value against a template in a condition or a claim, write `k::bits!(value, \"..\")`",
        span,
    )
}

/// Parses the template of a `k::bits!` invocation.
pub(crate) fn template_of(invocation: &Macro) -> Result<BitTemplate, SyntaxError> {
    let literal = syn::parse2::<LitStr>(invocation.tokens.clone()).map_err(|_| {
        let reason = if Punctuated::<Expr, Token![,]>::parse_terminated
            .parse2(invocation.tokens.clone())
            .is_ok_and(|arguments| arguments.len() > 1)
        {
            "in a pattern, `k::bits!` takes one string literal, the template, as in `k::bits!(\"00 yyy 100\")`; a second argument is reserved for modifiers such as signed fields, which are not supported yet. The test `k::bits!(value, \"..\")` is a `Bool` term, for a condition or a claim"
        } else {
            "`k::bits!` takes exactly one string literal, the template, as in `k::bits!(\"00 yyy 100\")`"
        };
        invalid(reason.to_owned(), invocation.tokens.span())
    })?;
    BitTemplate::parse(&literal)
}

thread_local! {
    /// The hidden binders of the item being parsed, which
    /// `validate_authored_binder` accepts although they hold the reserved
    /// marker.
    static GENERATED: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
}

/// Whether `spelling` is a hidden binder of the item being parsed.
///
/// The exemption is by origin: [`desugar`] rejects every authored identifier
/// with the hidden prefix before it rewrites the item, so a listed spelling
/// that occurs in the rewritten item was inserted by the rewrite.
pub(crate) fn is_generated_binder(spelling: &str) -> bool {
    GENERATED.with(|generated| generated.borrow().iter().any(|name| name == spelling))
}

/// Whether `spelling` is a hidden template binder's spelling.
#[must_use]
pub fn is_hidden_binder(spelling: &str) -> bool {
    spelling
        .strip_prefix(GENERATED_BINDER_PREFIX)
        .is_some_and(|ordinal| {
            !ordinal.is_empty() && ordinal.bytes().all(|byte| byte.is_ascii_digit())
        })
}

/// While alive, lets the item's hidden binders through binder validation.
pub(crate) struct GeneratedBinders {
    previous: Vec<String>,
}

impl GeneratedBinders {
    pub(crate) fn allow(names: Vec<String>) -> Self {
        Self {
            previous: GENERATED
                .with(|generated| std::mem::replace(&mut *generated.borrow_mut(), names)),
        }
    }
}

impl Drop for GeneratedBinders {
    fn drop(&mut self) {
        let previous = std::mem::take(&mut self.previous);
        GENERATED.with(|generated| *generated.borrow_mut() = previous);
    }
}

/// One template of an item, with the binder that names its value.
struct Occurrence {
    template: BitTemplate,
    binder: Ident,
    /// Whether the binder is hidden (no `op @`).
    hidden: bool,
}

/// Rewrites every `k::bits!` template of `item`'s parameters into its long
/// form and returns the hidden binders it introduced, or `None` when the item
/// has no template. `allowed` is false for sentences that take no template.
///
/// # Errors
///
/// A malformed template, a template in an or-pattern, a field that collides
/// with a binder, an authored identifier spelled like a hidden binder, and a
/// hidden binder in a sentence with a binder list.
pub fn desugar_bit_templates(item: &mut ItemFn) -> Result<Option<Vec<String>>, SyntaxError> {
    desugar(item, true)
}

/// [`desugar_bit_templates`]; when `allowed` is false, a template is an error.
pub(crate) fn desugar(
    item: &mut ItemFn,
    allowed: bool,
) -> Result<Option<Vec<String>>, SyntaxError> {
    reject_hidden_spellings(&item.to_token_stream())?;
    if !allowed {
        for argument in &item.sig.inputs {
            if let Some(span) = first_template(&argument.to_token_stream()) {
                return Err(misplaced(span));
            }
        }
        return Ok(None);
    }
    if !item
        .sig
        .inputs
        .iter()
        .any(|argument| contains_template(&argument.to_token_stream()))
    {
        return Ok(None);
    }
    let mut occurrences = Vec::new();
    for argument in &mut item.sig.inputs {
        let FnArg::Typed(argument) = argument else {
            continue;
        };
        rewrite_parameter(&mut argument.pat, &mut occurrences)?;
    }
    check_binders(item, &occurrences)?;
    let fields = field_terms(&occurrences);
    let mut substitution = Substitution {
        fields: &fields,
        error: None,
    };
    substitution.visit_block_mut(&mut item.block);
    let mut requires = None;
    for (index, attribute) in item.attrs.iter_mut().enumerate() {
        let Some(name) = condition_name(attribute) else {
            continue;
        };
        if let syn::Meta::List(list) = &mut attribute.meta
            && let Ok(mut condition) = syn::parse2::<Expr>(list.tokens.clone())
        {
            substitution.visit_expr_mut(&mut condition);
            list.tokens = condition.to_token_stream();
            if name == "requires" {
                requires = Some(index);
            }
        }
    }
    if let Some(error) = substitution.error {
        return Err(error);
    }
    insert_guard(item, &occurrences, requires);
    Ok(Some(
        occurrences
            .iter()
            .filter(|occurrence| occurrence.hidden)
            .map(|occurrence| occurrence.binder.to_string())
            .collect(),
    ))
}

/// Writes the fields of the templates in a readable clause's `pattern` into
/// its authored `result`, as [`desugar`] writes them into an item's result.
///
/// A readable clause is parsed as an item whose result may be a placeholder
/// (a splice or an erasure is no term), so the clause keeps its own result
/// and substitutes it here. The binders are those [`desugar`] gives the
/// clause's item, which has `pattern` as its one parameter.
///
/// # Errors
///
/// A malformed template, an authored identifier spelled like a hidden
/// binder, a field bound again, and a field in a macro body that is no list
/// of terms.
pub(crate) fn substitute_clause_result(
    pattern: &Pat,
    result: &mut Expr,
) -> Result<(), SyntaxError> {
    reject_hidden_spellings(&result.to_token_stream())?;
    if !pattern_contains_template(pattern) {
        return Ok(());
    }
    let mut occurrences = Vec::new();
    rewrite_pattern(&mut pattern.clone(), &mut occurrences)?;
    let fields = field_terms(&occurrences);
    let mut substitution = Substitution {
        fields: &fields,
        error: None,
    };
    substitution.visit_expr_mut(result);
    substitution.error.map_or(Ok(()), Err)
}

/// Rewrites every `k::bits!(value, "..")` test in `expression`, including
/// inside the term lists of nested macros, into its long form; a template
/// without a value there is out of place.
///
/// # Errors
///
/// A template without a value, a value that is no variable or bit range of
/// one, and a malformed template.
pub(crate) fn expand_bit_tests(expression: &mut Expr) -> Result<(), SyntaxError> {
    let mut tests = Tests { error: None };
    tests.visit_expr_mut(expression);
    tests.error.map_or(Ok(()), Err)
}

/// Replaces `k::bits!(value, "..")` tests with their long forms.
struct Tests {
    error: Option<SyntaxError>,
}

impl VisitMut for Tests {
    fn visit_expr_mut(&mut self, expression: &mut Expr) {
        if self.error.is_some() {
            return;
        }
        if let Expr::Macro(invocation) = expression
            && is_bits_macro(&invocation.mac.path)
        {
            match test_long_form(&invocation.mac) {
                Ok(long) => *expression = long,
                Err(error) => self.error = Some(error),
            }
            return;
        }
        syn::visit_mut::visit_expr_mut(self, expression);
    }

    fn visit_macro_mut(&mut self, invocation: &mut Macro) {
        if self.error.is_some() || first_template(&invocation.tokens).is_none() {
            return;
        }
        // A test inside a nested term list (`k::or_bool!`, `k::k!`) is
        // rewritten there; any other body keeps its template, which its own
        // parse rejects.
        if let Ok(mut arguments) =
            Punctuated::<Expr, Token![,]>::parse_terminated.parse2(invocation.tokens.clone())
        {
            for argument in &mut arguments {
                self.visit_expr_mut(argument);
            }
            invocation.tokens = arguments.to_token_stream();
        }
    }
}

/// The long form of the test `k::bits!(value, "..")`, parenthesized.
fn test_long_form(invocation: &Macro) -> Result<Expr, SyntaxError> {
    let parser = |input: syn::parse::ParseStream<'_>| {
        let value: Expr = input.parse()?;
        input.parse::<Token![,]>()?;
        let template: LitStr = input.parse()?;
        input.parse::<Option<Token![,]>>()?;
        Ok((value, template))
    };
    let Ok((value, template)) = parser.parse2(invocation.tokens.clone()) else {
        if syn::parse2::<LitStr>(invocation.tokens.clone()).is_ok() {
            return Err(misplaced(invocation.path.span()));
        }
        return Err(invalid(
            "a `k::bits!` test takes the value and the template, as in `k::bits!(op, \"00 yyy 100\")`".to_owned(),
            invocation.tokens.span(),
        ));
    };
    if !is_test_value(&value) {
        return Err(invalid(
            "the value a `k::bits!` test reads is a variable, a field of a bit template, or a bit range of a variable (`x.bit_range::<Int>(0, 8)`): the test's long form reads it once per guard term, so bind a larger term to a name first".to_owned(),
            value.span(),
        ));
    }
    let template = BitTemplate::parse(&template)?;
    let guard = template.guard(&value.to_token_stream(), template.span);
    let condition: Expr = syn::parse2(guard).expect("a test's long form is an expression");
    let delimiter = match &invocation.delimiter {
        syn::MacroDelimiter::Paren(paren) => paren.span,
        syn::MacroDelimiter::Brace(brace) => brace.span,
        syn::MacroDelimiter::Bracket(bracket) => bracket.span,
    };
    Ok(Expr::Paren(syn::ExprParen {
        attrs: Vec::new(),
        paren_token: syn::token::Paren { span: delimiter },
        expr: Box::new(condition),
    }))
}

/// Whether `value` may be the value of a test: a variable, or a bit range of
/// one with literal bounds, which is also what a field stands for.
fn is_test_value(value: &Expr) -> bool {
    let is_variable = |expression: &Expr| {
        matches!(expression, Expr::Path(path)
            if path.qself.is_none() && path.attrs.is_empty() && path.path.get_ident().is_some())
    };
    match value {
        Expr::MethodCall(call) => {
            call.method == "bit_range"
                && is_variable(&call.receiver)
                && call.args.len() == 2
                && call.args.iter().all(|argument| {
                    matches!(
                        argument,
                        Expr::Lit(syn::ExprLit {
                            lit: syn::Lit::Int(_),
                            ..
                        })
                    )
                })
        }
        other => is_variable(other),
    }
}

/// Puts the templates' guards into the item's `requires`, before the
/// authored condition at attribute `requires`, if any.
fn insert_guard(item: &mut ItemFn, occurrences: &[Occurrence], requires: Option<usize>) {
    // The guard precedes an authored condition: a template is part of the
    // pattern, matched before any guard, and `&&` (K's `andThenBool`)
    // evaluates left to right, so an authored condition that is defined only
    // on the template's values is never evaluated outside them. Provenance
    // ranges run forward through the source, and the authored condition
    // precedes the parameters, so the guard's tokens take the span of the
    // condition's first token; without a condition they take the template's.
    let span = requires
        .and_then(|index| match &item.attrs[index].meta {
            syn::Meta::List(list) => list
                .tokens
                .clone()
                .into_iter()
                .next()
                .map(|token| token.span()),
            _ => None,
        })
        .unwrap_or_else(|| {
            occurrences
                .first()
                .map_or_else(Span::call_site, |occurrence| occurrence.template.span)
        });
    let guards = occurrences
        .iter()
        .filter(|occurrence| occurrence.template.literal().is_none())
        .map(|occurrence| {
            let binder = Ident::new(&occurrence.binder.to_string(), span);
            occurrence.template.guard(&binder.to_token_stream(), span)
        })
        .collect::<Vec<_>>();
    if !guards.is_empty() {
        let mut guard = TokenStream::new();
        for (index, part) in guards.into_iter().enumerate() {
            if index > 0 {
                guard.extend(quote_spanned!(span=> &&));
            }
            guard.extend(part);
        }
        if let Some(index) = requires {
            let syn::Meta::List(list) = &mut item.attrs[index].meta else {
                unreachable!("a parsed condition is a list attribute");
            };
            let authored = syn::parse2::<Expr>(list.tokens.clone())
                .expect("the condition parsed before the substitution");
            let authored = if binds_looser_than_and(&authored) {
                // The parentheses take the span of the condition's last
                // leaf. `Spanned::span` would join the condition's spans in
                // the collector's reparse but fall back to its first token
                // in the macro, where joining is unstable, so the closing
                // parenthesis, and with it the condition's range, would end
                // at different places.
                let closing = TokenRange::for_tokens(&authored).map_or(span, TokenRange::last);
                quote_spanned!(closing=> (#authored))
            } else {
                authored.to_token_stream()
            };
            list.tokens = quote_spanned!(span=> #guard && #authored);
        } else {
            let attribute: Attribute = syn::parse_quote_spanned!(span=> #[k::requires(#guard)]);
            let position = item
                .attrs
                .iter()
                .position(|attribute| !is_documentation(attribute))
                .unwrap_or(item.attrs.len());
            item.attrs.insert(position, attribute);
        }
    }
}

/// Whether `expression` must be parenthesized as the right operand of `&&`.
fn binds_looser_than_and(expression: &Expr) -> bool {
    matches!(
        expression,
        Expr::Binary(syn::ExprBinary {
            op: syn::BinOp::Or(_),
            ..
        }) | Expr::Assign(_)
            | Expr::Range(_)
            | Expr::Closure(_)
    )
}

fn is_documentation(attribute: &Attribute) -> bool {
    attribute.path().is_ident("doc")
}

/// `requires` or `ensures` for a sentence condition helper.
fn condition_name(attribute: &Attribute) -> Option<&'static str> {
    let path = attribute.path();
    if path.segments.len() < 2 {
        return None;
    }
    match path.segments.last()?.ident.to_string().as_str() {
        "requires" => Some("requires"),
        "ensures" => Some("ensures"),
        _ => None,
    }
}

/// Rejects an authored identifier spelled like a hidden binder.
fn reject_hidden_spellings(tokens: &TokenStream) -> Result<(), SyntaxError> {
    for token in tokens.clone() {
        match token {
            TokenTree::Ident(ident) if ident.to_string().starts_with(GENERATED_BINDER_PREFIX) => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::ReservedBinder,
                    ident.span(),
                ));
            }
            TokenTree::Group(group) => reject_hidden_spellings(&group.stream())?,
            _ => {}
        }
    }
    Ok(())
}

/// Rewrites the templates of one parameter pattern, looking inside a
/// `k::term![..]` pattern.
fn rewrite_parameter(
    pattern: &mut Pat,
    occurrences: &mut Vec<Occurrence>,
) -> Result<(), SyntaxError> {
    if let Pat::Macro(invocation) = pattern
        && crate::term::is_term_macro(&invocation.mac.path)
    {
        if !contains_template(&invocation.mac.tokens) {
            return Ok(());
        }
        let Ok(mut inner) = Pat::parse_multi.parse2(invocation.mac.tokens.clone()) else {
            return Ok(());
        };
        rewrite_pattern(&mut inner, occurrences)?;
        invocation.mac.tokens = inner.to_token_stream();
        return Ok(());
    }
    rewrite_pattern(pattern, occurrences)
}

/// Whether `tokens` hold a `bits!` invocation anywhere.
fn contains_template(tokens: &TokenStream) -> bool {
    first_template(tokens).is_some()
}

/// The span of the first `bits!` invocation in `tokens`.
fn first_template(tokens: &TokenStream) -> Option<Span> {
    let tokens = tokens.clone().into_iter().collect::<Vec<_>>();
    tokens.iter().enumerate().find_map(|(index, token)| match token {
        TokenTree::Ident(ident)
            if ident == "bits"
                && matches!(tokens.get(index + 1), Some(TokenTree::Punct(punct)) if punct.as_char() == '!') =>
        {
            Some(ident.span())
        }
        TokenTree::Group(group) => first_template(&group.stream()),
        _ => None,
    })
}

fn pattern_contains_template(pattern: &Pat) -> bool {
    contains_template(&pattern.to_token_stream())
}

fn rewrite_pattern(
    pattern: &mut Pat,
    occurrences: &mut Vec<Occurrence>,
) -> Result<(), SyntaxError> {
    match pattern {
        Pat::Macro(invocation) if is_bits_macro(&invocation.mac.path) => {
            let template = template_of(&invocation.mac)?;
            if let Some(value) = template.literal() {
                *pattern = literal_pattern(value, template.span);
                return Ok(());
            }
            let binder = Ident::new(
                &format!(
                    "{GENERATED_BINDER_PREFIX}{}",
                    occurrences
                        .iter()
                        .filter(|occurrence| occurrence.hidden)
                        .count()
                ),
                template.span,
            );
            *pattern = Pat::Ident(syn::PatIdent {
                attrs: Vec::new(),
                by_ref: None,
                mutability: None,
                ident: binder.clone(),
                subpat: None,
            });
            occurrences.push(Occurrence {
                template,
                binder,
                hidden: true,
            });
            Ok(())
        }
        Pat::Ident(identifier) => {
            let Some((_, subpattern)) = &mut identifier.subpat else {
                return Ok(());
            };
            if let Pat::Macro(invocation) = &**subpattern
                && is_bits_macro(&invocation.mac.path)
            {
                let template = template_of(&invocation.mac)?;
                if let Some(value) = template.literal() {
                    **subpattern = literal_pattern(value, template.span);
                } else {
                    identifier.subpat = None;
                    occurrences.push(Occurrence {
                        template,
                        binder: identifier.ident.clone(),
                        hidden: false,
                    });
                }
                return Ok(());
            }
            rewrite_pattern(subpattern, occurrences)
        }
        Pat::Or(or) => {
            if let Some(case) = or.cases.iter().find(|case| pattern_contains_template(case)) {
                return Err(position_error(
                    "a bit template cannot be an alternative of `|`: each alternative would need its own guard; write one row or rule per alternative",
                    case.span(),
                ));
            }
            Ok(())
        }
        Pat::Paren(inner) => rewrite_pattern(&mut inner.pat, occurrences),
        Pat::Reference(inner) => rewrite_pattern(&mut inner.pat, occurrences),
        Pat::Tuple(tuple) => tuple
            .elems
            .iter_mut()
            .try_for_each(|element| rewrite_pattern(element, occurrences)),
        Pat::TupleStruct(tuple) => tuple
            .elems
            .iter_mut()
            .try_for_each(|element| rewrite_pattern(element, occurrences)),
        Pat::Slice(slice) => slice
            .elems
            .iter_mut()
            .try_for_each(|element| rewrite_pattern(element, occurrences)),
        Pat::Struct(record) => record
            .fields
            .iter_mut()
            .try_for_each(|field| rewrite_pattern(&mut field.pat, occurrences)),
        Pat::Type(typed) => rewrite_pattern(&mut typed.pat, occurrences),
        _ => Ok(()),
    }
}

fn literal_pattern(value: u128, span: Span) -> Pat {
    Pat::Lit(syn::PatLit {
        attrs: Vec::new(),
        lit: syn::Lit::Int(LitInt::new(&value.to_string(), span)),
    })
}

/// Checks that no field letter collides with another name of the sentence's
/// patterns, and that a hidden binder is not needed in a binder list.
fn check_binders(item: &ItemFn, occurrences: &[Occurrence]) -> Result<(), SyntaxError> {
    let mut seen = BTreeMap::<char, Span>::new();
    for occurrence in occurrences {
        for field in occurrence.template.fields() {
            if seen.insert(field.name, occurrence.template.span).is_some() {
                return Err(collision(
                    format!(
                        "field `{}` is named by two bit templates of this sentence; give each field its own letter",
                        field.name
                    ),
                    occurrence.template.span,
                ));
            }
        }
    }
    let mut binders = Vec::new();
    for argument in &item.sig.inputs {
        if let FnArg::Typed(argument) = argument {
            pattern_binders(&argument.pat, &mut binders);
        }
    }
    for occurrence in occurrences {
        for field in occurrence.template.fields() {
            if let Some(binder) = binders
                .iter()
                .find(|binder| binder.to_string() == field.name.to_string())
            {
                return Err(collision(
                    format!(
                        "field `{}` of the bit template is also a binder of the pattern; a field is a name for part of the matched value, so give it another letter or rename the binder",
                        field.name
                    ),
                    binder.span(),
                ));
            }
        }
    }
    if occurrences.iter().any(|occurrence| occurrence.hidden)
        && item.sig.inputs.len() > 1
        && item.sig.inputs.iter().any(|argument| {
            matches!(argument, FnArg::Typed(typed) if matches!(&*typed.pat, Pat::Ident(identifier) if identifier.subpat.is_none()))
        })
    {
        let span = occurrences
            .iter()
            .find(|occurrence| occurrence.hidden)
            .map_or_else(Span::call_site, |occurrence| occurrence.template.span);
        return Err(position_error(
            "this sentence lists its binders, so the bit template's value needs a name to list: write `op @ k::bits!(..)` and list `op`",
            span,
        ));
    }
    Ok(())
}

/// The identifiers a pattern binds, including aliases, in any position.
fn pattern_binders(pattern: &Pat, binders: &mut Vec<Ident>) {
    match pattern {
        Pat::Ident(identifier) => {
            binders.push(identifier.ident.clone());
            if let Some((_, subpattern)) = &identifier.subpat {
                pattern_binders(subpattern, binders);
            }
        }
        Pat::Macro(invocation) if crate::term::is_term_macro(&invocation.mac.path) => {
            if let Ok(inner) = Pat::parse_multi.parse2(invocation.mac.tokens.clone()) {
                pattern_binders(&inner, binders);
            }
        }
        Pat::Or(or) => or
            .cases
            .iter()
            .for_each(|case| pattern_binders(case, binders)),
        Pat::Paren(inner) => pattern_binders(&inner.pat, binders),
        Pat::Reference(inner) => pattern_binders(&inner.pat, binders),
        Pat::Tuple(tuple) => tuple
            .elems
            .iter()
            .for_each(|element| pattern_binders(element, binders)),
        Pat::TupleStruct(tuple) => tuple
            .elems
            .iter()
            .for_each(|element| pattern_binders(element, binders)),
        Pat::Slice(slice) => slice
            .elems
            .iter()
            .for_each(|element| pattern_binders(element, binders)),
        Pat::Struct(record) => record
            .fields
            .iter()
            .for_each(|field| pattern_binders(&field.pat, binders)),
        Pat::Type(typed) => pattern_binders(&typed.pat, binders),
        _ => {}
    }
}

/// A field's term: its template's binder and its bit range.
struct FieldTerm {
    binder: Ident,
    offset: u32,
    length: u32,
}

fn field_terms(occurrences: &[Occurrence]) -> BTreeMap<String, FieldTerm> {
    let mut fields = BTreeMap::new();
    for occurrence in occurrences {
        for field in occurrence.template.fields() {
            fields.insert(
                field.name.to_string(),
                FieldTerm {
                    binder: occurrence.binder.clone(),
                    offset: field.offset,
                    length: field.length,
                },
            );
        }
    }
    fields
}

impl FieldTerm {
    /// `binder.bit_range::<Int>(offset, length)` at the occurrence's span.
    fn term(&self, span: Span) -> Expr {
        let binder = Ident::new(&self.binder.to_string(), span);
        let offset = LitInt::new(&self.offset.to_string(), span);
        let length = LitInt::new(&self.length.to_string(), span);
        syn::parse_quote_spanned!(span=> #binder.bit_range::<Int>(#offset, #length))
    }
}

/// Replaces field occurrences with their terms, and records a field rebound
/// by a `let` or `k::matches!` pattern.
struct Substitution<'a> {
    fields: &'a BTreeMap<String, FieldTerm>,
    error: Option<SyntaxError>,
}

impl Substitution<'_> {
    fn field(&self, path: &syn::ExprPath) -> Option<&FieldTerm> {
        if path.qself.is_some() || path.path.leading_colon.is_some() {
            return None;
        }
        let identifier = path.path.get_ident()?;
        self.fields.get(&identifier.to_string())
    }

    fn rebound(&mut self, identifier: &Ident) {
        if self.error.is_none() && self.fields.contains_key(&identifier.to_string()) {
            self.error = Some(collision(
                format!(
                    "`{identifier}` is a field of the sentence's bit template and cannot be bound again here; give the field or this binder another name"
                ),
                identifier.span(),
            ));
        }
    }

    fn substitute_macro(&mut self, invocation: &mut Macro) {
        let last = invocation
            .path
            .segments
            .last()
            .map(|segment| segment.ident.to_string());
        if last.as_deref() == Some("matches") {
            let parser = |input: syn::parse::ParseStream<'_>| {
                let subject: Expr = input.parse()?;
                let comma: Token![,] = input.parse()?;
                let pattern = Pat::parse_multi(input)?;
                let trailing: Option<Token![,]> = input.parse()?;
                Ok((subject, comma, pattern, trailing))
            };
            match parser.parse2(invocation.tokens.clone()) {
                Ok((mut subject, comma, pattern, trailing)) => {
                    self.visit_expr_mut(&mut subject);
                    let mut binders = Vec::new();
                    pattern_binders(&pattern, &mut binders);
                    for binder in &binders {
                        self.rebound(binder);
                    }
                    invocation.tokens = quote::quote!(#subject #comma #pattern #trailing);
                }
                Err(_) => self.unreachable_field(invocation),
            }
            return;
        }
        match Punctuated::<Expr, Token![,]>::parse_terminated.parse2(invocation.tokens.clone()) {
            Ok(mut arguments) => {
                for argument in &mut arguments {
                    self.visit_expr_mut(argument);
                }
                invocation.tokens = arguments.to_token_stream();
            }
            Err(_) => self.unreachable_field(invocation),
        }
    }

    /// Records an error at a field that occurs in a macro body that is no
    /// list of terms, where the field cannot be replaced by its bit range.
    /// A body that mentions no field needs no substitution.
    fn unreachable_field(&mut self, invocation: &Macro) {
        if self.error.is_some() {
            return;
        }
        if let Some(field) = first_field(&invocation.tokens, self.fields) {
            let name = invocation
                .path
                .segments
                .last()
                .map_or_else(String::new, |segment| segment.ident.to_string());
            self.error = Some(position_error(
                &format!(
                    "`{field}` is a field of the sentence's bit template, but it occurs in the body of `{name}!`, which is not a list of terms, so it cannot be replaced by its bit range; bind the field's value outside the macro, or name the template's value (`op @ k::bits!(..)`) and write `op.bit_range::<Int>(offset, length)`"
                ),
                field.span(),
            ));
        }
    }
}

/// The first identifier in `tokens` that names a field.
fn first_field(tokens: &TokenStream, fields: &BTreeMap<String, FieldTerm>) -> Option<Ident> {
    tokens.clone().into_iter().find_map(|token| match token {
        TokenTree::Ident(ident) if fields.contains_key(&ident.to_string()) => Some(ident),
        TokenTree::Group(group) => first_field(&group.stream(), fields),
        _ => None,
    })
}

impl VisitMut for Substitution<'_> {
    fn visit_expr_mut(&mut self, expression: &mut Expr) {
        if let Expr::Path(path) = expression
            && let Some(field) = self.field(path)
        {
            *expression = field.term(path.span());
            return;
        }
        syn::visit_mut::visit_expr_mut(self, expression);
    }

    fn visit_field_value_mut(&mut self, field: &mut syn::FieldValue) {
        if field.colon_token.is_none()
            && let syn::Member::Named(name) = &field.member
            && let Some(term) = self.fields.get(&name.to_string())
        {
            field.expr = term.term(name.span());
            field.colon_token = Some(Token![:](name.span()));
            return;
        }
        syn::visit_mut::visit_field_value_mut(self, field);
    }

    fn visit_pat_mut(&mut self, pattern: &mut Pat) {
        let mut binders = Vec::new();
        pattern_binders(pattern, &mut binders);
        for binder in &binders {
            self.rebound(binder);
        }
    }

    fn visit_macro_mut(&mut self, invocation: &mut Macro) {
        self.substitute_macro(invocation);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn template(text: &str) -> Result<BitTemplate, SyntaxError> {
        BitTemplate::parse(&LitStr::new(text, Span::call_site()))
    }

    #[test]
    fn templates_read_most_significant_bit_first() {
        let parsed = template("00 yyy 100").unwrap();
        assert_eq!(parsed.width(), 8);
        assert_eq!(
            parsed.runs(),
            [
                FixedRun {
                    offset: 6,
                    length: 2,
                    value: 0
                },
                FixedRun {
                    offset: 0,
                    length: 3,
                    value: 4
                },
            ]
        );
        assert_eq!(
            parsed.fields(),
            [BitField {
                name: 'y',
                offset: 3,
                length: 3
            }]
        );
        assert_eq!(parsed.cube(), (0b1100_0111, 0b0000_0100));
        assert_eq!(parsed.literal(), None);
    }

    #[test]
    fn fixed_runs_end_at_spaces_and_fields_continue_across_them() {
        let parsed = template("11 qq0 1_1").unwrap();
        assert_eq!(
            parsed.runs(),
            [
                FixedRun {
                    offset: 6,
                    length: 2,
                    value: 3
                },
                FixedRun {
                    offset: 3,
                    length: 1,
                    value: 0
                },
                FixedRun {
                    offset: 2,
                    length: 1,
                    value: 1
                },
                FixedRun {
                    offset: 0,
                    length: 1,
                    value: 1
                },
            ]
        );
        assert_eq!(
            parsed.fields(),
            [BitField {
                name: 'q',
                offset: 4,
                length: 2
            }]
        );
        assert_eq!(template("yy y").unwrap().fields()[0].length, 3);
        assert_eq!(
            template("0011 01").unwrap().runs(),
            [
                FixedRun {
                    offset: 2,
                    length: 4,
                    value: 3
                },
                FixedRun {
                    offset: 0,
                    length: 2,
                    value: 1
                },
            ]
        );
    }

    #[test]
    fn a_fully_fixed_template_is_its_literal() {
        assert_eq!(template("01 110 110").unwrap().literal(), Some(118));
        assert_eq!(template("0").unwrap().literal(), Some(0));
        assert_eq!(template("0_").unwrap().literal(), None);
    }

    #[test]
    fn malformed_templates_are_rejected() {
        for (text, needle) in [
            ("", "at least one bit"),
            ("   ", "at least one bit"),
            ("0x2", "character 2"),
            ("00 Y", "character 3"),
            ("aa0aa", "field `a` is split"),
        ] {
            let error = template(text).unwrap_err().to_string();
            assert!(error.contains(needle), "{text:?}: {error}");
        }
        assert!(template(&"0".repeat(128)).is_ok());
        assert!(
            template(&"0".repeat(129))
                .unwrap_err()
                .to_string()
                .contains("at most 128")
        );
    }

    #[test]
    fn powers_of_two_are_exact() {
        assert_eq!(power_of_two(0), "1");
        assert_eq!(power_of_two(8), "256");
        assert_eq!(power_of_two(128), "340282366920938463463374607431768211456");
    }

    fn desugar(source: &str) -> (String, Option<Vec<String>>) {
        let mut item: ItemFn = syn::parse_str(source).unwrap();
        let hidden = desugar_bit_templates(&mut item).unwrap();
        (item.to_token_stream().to_string(), hidden)
    }

    #[test]
    fn the_long_form_names_the_value_guards_it_and_substitutes_fields() {
        let (long, hidden) = desugar(
            "fn decode_inc_r(k::term![Decode(k::bits!(\"00 yyy 100\"))]: k::Term<Instr>) -> k::Term<Instr> { k::term![Update8(Inc, R8(y))] }",
        );
        assert_eq!(hidden, Some(vec!["__krs_bits_0".to_owned()]));
        assert_eq!(
            long,
            "# [k :: requires (__krs_bits_0 . ge :: < Int > (0) && __krs_bits_0 . lt :: < Int > (256) && __krs_bits_0 . bit_range :: < Int > (6 , 2) . eq :: < Int > (0) && __krs_bits_0 . bit_range :: < Int > (0 , 3) . eq :: < Int > (4))] fn decode_inc_r (k :: term ! [Decode (__krs_bits_0)] : k :: Term < Instr >) -> k :: Term < Instr > { k :: term ! [Update8 (Inc , R8 (__krs_bits_0 . bit_range :: < Int > (3 , 3)))] }"
        );
    }

    #[test]
    fn an_alias_names_the_value_and_the_guard_precedes_an_authored_condition() {
        let (long, hidden) = desugar(
            "#[k::requires(op.ne::<Int>(118) || flag)] fn r(Decode(op @ k::bits!(\"01 yyy zz_\"), flag): Instr) -> Instr { Ld { dst: y, z } }",
        );
        assert_eq!(hidden, Some(Vec::new()));
        assert!(long.starts_with("# [k :: requires (op . ge :: < Int > (0) && op . lt :: < Int > (256) && op . bit_range :: < Int > (6 , 2) . eq :: < Int > (1) && (op . ne :: < Int > (118) || flag))]"), "{long}");
        assert!(long.contains("Decode (op , flag)"), "{long}");
        assert!(long.contains("Ld { dst : op . bit_range :: < Int > (3 , 3) , z : op . bit_range :: < Int > (1 , 2) }"), "{long}");
    }

    #[test]
    fn fixed_templates_become_literals_without_a_guard() {
        let (long, hidden) =
            desugar("fn halt(Decode(k::bits!(\"01 110 110\")): Instr) -> Instr { Halt }");
        assert_eq!(hidden, Some(Vec::new()));
        assert_eq!(long, "fn halt (Decode (118) : Instr) -> Instr { Halt }");
        let (long, _) = desugar("fn halt(Decode(op @ k::bits!(\"0111\")): Instr) -> Instr { op }");
        assert_eq!(long, "fn halt (Decode (op @ 7) : Instr) -> Instr { op }");
    }

    #[test]
    fn items_without_templates_are_untouched() {
        let (long, hidden) = desugar("fn f(F(x): Int) -> Int { x }");
        assert_eq!(hidden, None);
        assert_eq!(long, "fn f (F (x) : Int) -> Int { x }");
    }

    fn head_results(source: &str) -> Vec<String> {
        let block =
            <crate::RuleBlock as crate::KrsSyntax>::parse_tokens(source.parse().unwrap()).unwrap();
        block
            .clauses()
            .iter()
            .map(|clause| clause.head_result().unwrap().spelling())
            .collect()
    }

    #[test]
    fn a_readable_clause_substitutes_fields_in_its_own_result() {
        assert_eq!(
            head_results(
                "for Exp; use ExpSyntax::*; \
                 code_a: CodeOf(k::bits!(\"0aaa\")) => a; \
                 code_op: CodeOf(op @ k::bits!(\"1aaa\")) => a.add::<Int>(op); \
                 pair: PairOf(k::bits!(\"0a\"), k::bits!(\"b1\")) => k![a, b];"
            ),
            [
                "__krs_bits_0 . bit_range :: < Int > (0 , 3)",
                "op . bit_range :: < Int > (0 , 3) . add :: < Int > (op)",
                "k![__krs_bits_0 . bit_range :: < Int > (0 , 1), __krs_bits_1 . bit_range :: < Int > (1 , 1)]",
            ]
        );
    }

    #[test]
    fn a_field_in_a_macro_body_that_is_no_term_list_is_an_error() {
        let pattern: Pat = Pat::parse_single
            .parse_str("CodeOf(k::bits!(\"0aaa\"))")
            .unwrap();
        let mut result: Expr = syn::parse_str("k::map! { a => 1 }").unwrap();
        let error = substitute_clause_result(&pattern, &mut result).unwrap_err();
        assert_eq!(
            error.kind().code().as_str(),
            "krs::syntax::bit-template-position"
        );
        assert!(error.to_string().contains("`a` is a field"), "{error}");
        // A body without a field needs no substitution.
        let mut result: Expr = syn::parse_str("k::map! { b => 1 }").unwrap();
        substitute_clause_result(&pattern, &mut result).unwrap();
        let mut item: ItemFn =
            syn::parse_str("fn f(F(k::bits!(\"0aaa\")): Int) -> Int { k::cells! { k: a } }")
                .unwrap();
        let error = desugar_bit_templates(&mut item).unwrap_err();
        assert!(error.to_string().contains("body of `cells!`"), "{error}");
    }

    #[test]
    fn a_template_at_the_root_of_a_condition_or_a_cell_pattern_is_misplaced() {
        for source in [
            "#[k::requires(k::bits!(\"01\"))] fn f(k::term![F(n)]: Term<Int>) -> Term<Int> { n }",
            "fn f(k::term![F(n)]: Term<Int>) -> Term<Int> { k::bits!(\"01\") }",
        ] {
            let error = crate::RuleItem::parse_equation_source(source).unwrap_err();
            assert_eq!(
                error.kind().code().as_str(),
                "krs::syntax::bit-template-position",
                "{source}: {error}"
            );
        }
        let rule = "fn r(n: Int, k::cells! { k: k::configuration::KCell(k::bits!(\"1_\"), tail @ ..), state @ .. }: Machine) -> Machine { k::cells! { k: k::configuration::KCell(0, ..tail), ..state } }";
        let error = <crate::StateRuleItem as crate::KrsSyntax>::parse_tokens(rule.parse().unwrap())
            .unwrap_err();
        assert_eq!(
            error.kind().code().as_str(),
            "krs::syntax::bit-template-position",
            "{error}"
        );
    }

    fn tested(source: &str) -> Result<String, SyntaxError> {
        let mut expression: Expr = syn::parse_str(source).unwrap();
        expand_bit_tests(&mut expression)?;
        Ok(expression.to_token_stream().to_string())
    }

    #[test]
    fn a_test_is_the_guard_of_the_pattern_with_the_same_template() {
        for template in ["00 yyy 100", "0111", "1___ ____", "11 qq0 1_1", "a", "0"] {
            let (long, _) = desugar(&format!(
                "fn f(F(op @ k::bits!(\"{template}\"), x): I) -> I {{ x }}"
            ));
            let guard = long
                .strip_prefix("# [k :: requires (")
                .and_then(|rest| rest.split_once(")] fn"))
                .map(|(guard, _)| guard.to_owned());
            let test = tested(&format!("k::bits!(op, \"{template}\")")).unwrap();
            match guard {
                // The pattern's guard and the test's long form are the same
                // terms in the same order.
                Some(guard) => assert_eq!(test, format!("({guard})"), "{template}"),
                // A template without free bits is a literal in a pattern,
                // and its test still reads the range and every run.
                None => assert!(
                    test.starts_with("(op . ge :: < Int > (0) && op . lt :: < Int >"),
                    "{template}: {test}"
                ),
            }
        }
        assert_eq!(
            tested("k::bits!(op, \"0111\")").unwrap(),
            "(op . ge :: < Int > (0) && op . lt :: < Int > (16) && op . bit_range :: < Int > (0 , 4) . eq :: < Int > (7))"
        );
    }

    #[test]
    fn a_test_binds_nothing_and_reads_a_variable_or_a_bit_range() {
        // Field letters and `_` constrain nothing, and no letter survives.
        let test = tested("k::bits!(n, \"0a\") && a.eq::<Int>(1)").unwrap();
        assert_eq!(
            test,
            "(n . ge :: < Int > (0) && n . lt :: < Int > (4) && n . bit_range :: < Int > (1 , 1) . eq :: < Int > (0)) && a . eq :: < Int > (1)"
        );
        assert!(tested("k::bits!(x.bit_range::<Int>(3, 3), \"1__\")").is_ok());
        assert!(
            tested("k::or_bool!(k::bits!(n, \"1\"), k::bits!(n, \"0\"))")
                .unwrap()
                .contains("or_bool ! ((n .")
        );
        for (source, needle) in [
            (
                "k::bits!(n.add::<Int>(1), \"01\")",
                "krs::syntax::invalid-bit-template: the value a `k::bits!` test reads",
            ),
            (
                "k::bits!(F(n), \"01\")",
                "krs::syntax::invalid-bit-template: the value",
            ),
            (
                "k::bits!(n, \"0X\")",
                "krs::syntax::invalid-bit-template: character 1",
            ),
            (
                "k::bits!(n)",
                "krs::syntax::invalid-bit-template: a `k::bits!` test takes the value and the template",
            ),
            (
                "n && k::bits!(\"01\")",
                "krs::syntax::bit-template-position",
            ),
        ] {
            let error = tested(source).unwrap_err();
            let error = format!("{}: {error}", error.kind().code().as_str());
            assert!(error.contains(needle), "{source}: {error}");
        }
    }

    #[test]
    fn a_second_argument_in_a_pattern_is_reserved() {
        let error = desugar_error("fn f(F(k::bits!(n, \"01\")): Int) -> Int { 0 }");
        assert!(
            error.contains("reserved for modifiers such as signed fields"),
            "{error}"
        );
    }

    fn desugar_error(source: &str) -> String {
        let mut item: ItemFn = syn::parse_str(source).unwrap();
        let error = desugar_bit_templates(&mut item).unwrap_err();
        format!("{}: {error}", error.kind().code().as_str())
    }

    #[test]
    fn collisions_and_misplaced_templates_are_rejected() {
        for (source, needle) in [
            (
                "fn f(F(k::bits!(\"yy\"), y): Int) -> Int { y }",
                "krs::syntax::bit-field-collision: field `y`",
            ),
            (
                "fn f(F(y @ k::bits!(\"yy\")): Int) -> Int { y }",
                "krs::syntax::bit-field-collision: field `y`",
            ),
            (
                "fn f(F(k::bits!(\"yy\"), k::bits!(\"y0\")): Int) -> Int { y }",
                "two bit templates",
            ),
            (
                "fn f(F(k::bits!(\"yy\")): Int) -> Int { { let y = 1; y } }",
                "cannot be bound again",
            ),
            (
                "fn f(F(k::bits!(\"y1\") | 0): Int) -> Int { 0 }",
                "krs::syntax::bit-template-position",
            ),
            (
                "fn f(x: Int, F(x, k::bits!(\"y1\")): Int) -> Int { x }",
                "write `op @ k::bits!(..)`",
            ),
            (
                "fn f(F(__krs_bits_0): Int) -> Int { 0 }",
                "krs::syntax::reserved-binder",
            ),
            (
                "fn f(F(k::bits!(1)): Int) -> Int { 0 }",
                "exactly one string literal",
            ),
        ] {
            let error = desugar_error(source);
            assert!(error.contains(needle), "{source}: {error}");
        }
    }
}
