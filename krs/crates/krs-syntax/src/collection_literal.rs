//! Collection literals: `map![k1 -> v1, .., kn -> vn]` and `set![x1, .., xn]`
//! wherever a term is built, each with an optional base `..rest`, written
//! last.
//!
//! A literal is notation for the builtin calls that build its collection, and
//! has no meaning of its own:
//!
//! - `map![k1 -> v1, .., kn -> vn]` is
//!   `map::update(..map::update(map::empty(), k1, v1).., kn, vn)`: each entry
//!   is written over the map before it, so the map is total, like a Rust map
//!   literal, and of two keys that evaluate equal the later one wins;
//! - `map![k -> v, ..m]` is `map::update(m, k, v)`: the rest is the base the
//!   written entries are applied over, as a record update `Ctor { f: e, ..t }`
//!   writes its fields over the record `t`;
//! - `set![x1, .., xn]` is `set::union(..set::union(set::item(x1),
//!   set::item(x2)).., set::item(xn))`, so elements that evaluate equal
//!   collapse, where `set::concat`, which is defined only on disjoint sets,
//!   would be undefined;
//! - `set![x, ..s]` is `set::union(s, set![x])`;
//! - `map![]` and `set![]` are `map::empty()` and `set::empty()`.
//!
//! Two keys written as the same term could never differ, so a map's earlier
//! value would never be read: a literal that writes a key twice is an error, as
//! a pattern that reads one key twice is. Two elements written as the same term
//! are one element, and `set![a, a]` is exactly the set `set![a]`.
//!
//! A `cells!` entry's and an initializer's `map![..]` are those surfaces' own
//! spelling of a cell's map, which they read before any term is (as K's
//! concatenation); this module reads a literal where a term stands.
//!
//! As for list notation (`crate::list_notation`), each function here returns
//! one level, a call of the operation's path in the facade's `builtin` module
//! (`map::update`), and leaves the remaining entries as a literal of their
//! own, so that term validation, which marks each notation call it validates,
//! reaches every level. Each level's head starts at its own token: an entry's
//! key, an element, the comma before an element a union adds, a rest's `..`,
//! or, for the empty collection, the brackets.

use proc_macro2::{Span, TokenStream};
use quote::ToTokens;
use syn::parse::{ParseStream, Parser};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{
    Expr, ExprCall, ExprMacro, ExprPath, Ident, Macro, MacroDelimiter, Path, PathSegment, Token,
};

use crate::{SyntaxError, SyntaxErrorKind};

/// The collection a literal builds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Collection {
    /// `map![..]`.
    Map,
    /// `set![..]`.
    Set,
}

impl Collection {
    const fn module(self) -> &'static str {
        match self {
            Self::Map => "map",
            Self::Set => "set",
        }
    }
}

/// The collection the literal macro `path` builds: a plain path whose last
/// segment is `map` or `set` (`map!`, `k::map!`), as the compiler-owned
/// islands are named.
pub(crate) fn literal_collection(path: &Path) -> Option<Collection> {
    if !crate::path::is_plain_path(path) {
        return None;
    }
    match path.segments.last()?.ident.to_string().as_str() {
        "map" => Some(Collection::Map),
        "set" => Some(Collection::Set),
        _ => None,
    }
}

/// Whether `expression` is a collection literal at its root: `map![..]` or
/// `set![..]`, notation for the builtin calls that build its collection.
#[must_use]
pub fn is_collection_literal(expression: &Expr) -> bool {
    matches!(expression, Expr::Macro(literal) if literal_collection(&literal.mac.path).is_some())
}

/// Whether `head`, the head of a notation application, builds a collection
/// value rather than applying an operation: the empty map or set and a set's
/// singleton, which only a literal generates as notation.
pub(crate) fn is_value_head(head: &Path) -> bool {
    matches!(
        crate::path::path_text(head).as_str(),
        "map::empty" | "set::empty" | "set::item"
    )
}

fn literal_error(reason: impl Into<String>, span: Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::InvalidExpressionNotation {
            reason: reason.into(),
        },
        span,
    )
}

/// One written entry: a map's `key -> value` or a set's element, with its
/// tokens, which the remaining literal of a level is written with.
struct Entry {
    tokens: TokenStream,
    key: Expr,
    value: Option<Expr>,
    /// The comma that follows the entry, if any.
    comma: Option<Token![,]>,
}

/// The base `..rest`, with its tokens.
struct Rest {
    tokens: TokenStream,
    dots: Token![..],
    base: Expr,
}

struct Parts {
    entries: Vec<Entry>,
    rest: Option<Rest>,
}

/// One level of the literal `literal`, a collection literal at a term
/// position: the call it denotes, whose operands are the written terms and
/// what remains of the literal.
///
/// # Errors
///
/// Returns [`SyntaxErrorKind::InvalidExpressionNotation`] for a malformed
/// entry, a key or an element written twice, an anonymous `..`, a rest that
/// is not last, and a rest with no entry.
pub(crate) fn literal_level(literal: &ExprMacro) -> Result<ExprCall, SyntaxError> {
    crate::term::reject_attributes(&literal.attrs, literal.span())?;
    let collection =
        literal_collection(&literal.mac.path).expect("only a collection literal has a level");
    let close = delimiter_span(&literal.mac.delimiter);
    let parts = parse_parts(collection, literal.mac.tokens.clone())?;
    if collection == Collection::Map {
        reject_repeated_keys(&parts.entries)?;
    }
    let module = collection.module();
    let remaining =
        |entries: &[Entry], rest: Option<&Rest>| remaining_literal(literal, close, entries, rest);
    // The authored literal's level spans the whole literal, from its path to
    // its brackets, where a mistake of the whole term is told; each remaining
    // level starts at the token of the entry it adds.
    let whole =
        (!is_remainder(&literal.mac.path)).then(|| first_span(&literal.mac.path.to_token_stream()));
    let Some((last, init)) = parts.entries.split_last() else {
        if let Some(rest) = &parts.rest {
            return Err(literal_error(
                format!(
                    "`{module}![..{base}]` has no entry: it is the {module} `{base}` itself, so write `{base}`",
                    base = rest.base.to_token_stream()
                ),
                rest.dots.spans[0],
            ));
        }
        return Ok(call(
            head(module, "empty", whole.unwrap_or(close), close),
            close,
            [],
        ));
    };
    match collection {
        Collection::Map => {
            let value = last.value.clone().expect("a map entry has a value");
            let head = head(
                module,
                "update",
                whole.unwrap_or_else(|| first_span(&last.tokens)),
                close,
            );
            let base = remaining(init, parts.rest.as_ref());
            Ok(call(head, close, [base, last.key.clone(), value]))
        }
        Collection::Set => {
            if let Some(rest) = &parts.rest {
                let head = head(module, "union", whole.unwrap_or(rest.dots.spans[0]), close);
                let elements = remaining(&parts.entries, None);
                return Ok(call(head, close, [rest.base.clone(), elements]));
            }
            let Some(before) = init.last() else {
                let head = head(
                    module,
                    "item",
                    whole.unwrap_or_else(|| first_span(&last.tokens)),
                    close,
                );
                return Ok(call(head, close, [last.key.clone()]));
            };
            let comma = before
                .comma
                .expect("an element that another follows ends in a comma");
            let head = head(module, "union", whole.unwrap_or(comma.span), close);
            let element = remaining(std::slice::from_ref(last), None);
            Ok(call(head, close, [remaining(init, None), element]))
        }
    }
}

/// The span of a literal's delimiters, which is the same where a macro
/// re-emits the tokens and where the collector reparses the source.
fn delimiter_span(delimiter: &MacroDelimiter) -> Span {
    match delimiter {
        MacroDelimiter::Paren(paren) => paren.span.join(),
        MacroDelimiter::Brace(brace) => brace.span.join(),
        MacroDelimiter::Bracket(bracket) => bracket.span.join(),
    }
}

/// What remains of a literal after one level: `rest` alone is the base
/// itself, and anything else a literal of the same collection, in brackets
/// that span the authored literal, under a path no author writes.
fn remaining_literal(
    literal: &ExprMacro,
    close: Span,
    entries: &[Entry],
    rest: Option<&Rest>,
) -> Expr {
    if let (true, Some(rest)) = (entries.is_empty(), rest) {
        return rest.base.clone();
    }
    let mut tokens = TokenStream::new();
    for (index, entry) in entries.iter().enumerate() {
        tokens.extend(entry.tokens.clone());
        if index + 1 < entries.len() || rest.is_some() {
            match entry.comma {
                Some(comma) => comma.to_tokens(&mut tokens),
                None => Token![,](close).to_tokens(&mut tokens),
            }
        }
    }
    if let Some(rest) = rest {
        tokens.extend(rest.tokens.clone());
    }
    let mut group = proc_macro2::Group::new(proc_macro2::Delimiter::Bracket, TokenStream::new());
    group.set_span(close);
    let name = literal
        .mac
        .path
        .segments
        .last()
        .expect("a literal's path names it")
        .ident
        .clone();
    let mut path = Path::from(Ident::new(REMAINDER, name.span()));
    path.segments.push(PathSegment::from(name));
    Expr::Macro(ExprMacro {
        attrs: Vec::new(),
        mac: Macro {
            path,
            bang_token: literal.mac.bang_token,
            delimiter: MacroDelimiter::Bracket(syn::token::Bracket(group.delim_span())),
            tokens,
        },
    })
}

/// The first segment of the path of what remains of a literal after a level,
/// which no author writes.
const REMAINDER: &str = "__krs_literal_remainder";

/// Whether `path` names what remains of a literal after a level.
fn is_remainder(path: &Path) -> bool {
    path.segments.len() == 2 && path.segments[0].ident == REMAINDER
}

/// Reads a literal's entries and its rest.
fn parse_parts(collection: Collection, tokens: TokenStream) -> Result<Parts, SyntaxError> {
    // A mistake is reported where it is found: the tokens after it are read
    // as part of the error, so the parser does not report them instead.
    let parser = |input: ParseStream<'_>| -> syn::Result<Result<Parts, SyntaxError>> {
        let parts = read_parts(collection, input);
        if parts.is_err() {
            input.parse::<TokenStream>()?;
        }
        Ok(parts)
    };
    parser.parse2(tokens)?
}

fn read_parts(collection: Collection, input: ParseStream<'_>) -> Result<Parts, SyntaxError> {
    let mut entries: Vec<Entry> = Vec::new();
    let mut rest = None;
    while !input.is_empty() {
        if input.peek(Token![..]) {
            rest = Some(parse_rest(collection, input)?);
            break;
        }
        let start = input.cursor();
        let (key, value) = match collection {
            Collection::Map => {
                let (key, value) = parse_map_entry(input)?;
                (key, Some(value))
            }
            Collection::Set => {
                if input.peek(Token![.]) && !input.peek(Token![..]) {
                    return Err(literal_error(
                        "`.Set` is K's empty set; a term writes the empty set `set![]`",
                        input.span(),
                    ));
                }
                (parse_part(input)?, None)
            }
        };
        let tokens = crate::term::tokens_between(start, input.cursor());
        let comma = if input.is_empty() {
            None
        } else {
            Some(input.parse::<Token![,]>().map_err(|_| {
                literal_error(
                    format!(
                        "expected `,` between the {} of a `{}![..]`",
                        match collection {
                            Collection::Map => "entries",
                            Collection::Set => "elements",
                        },
                        collection.module()
                    ),
                    input.span(),
                )
            })?)
        };
        entries.push(Entry {
            tokens,
            key,
            value,
            comma,
        });
    }
    Ok(Parts { entries, rest })
}

/// Reads `key -> value`. The key runs to its arrow, so a comma inside it, as
/// in a turbofish `Wrap::<A, B>(x)`, is the key's; a comma that separates
/// what no arrow follows, or what is no term, ends an entry without one.
fn parse_map_entry(input: ParseStream<'_>) -> Result<(Expr, Expr), SyntaxError> {
    let start = input.span();
    if input.peek(Token![.]) && !input.peek(Token![..]) {
        return Err(literal_error(
            "`.Map` is K's empty map; a term writes the empty map `map![]`",
            start,
        ));
    }
    let without_arrow = |span| literal_error("a map's entry is written `key -> value`", span);
    let mut key = TokenStream::new();
    let mut comma = None;
    while !input.is_empty() && !input.peek(Token![->]) && !input.peek(Token![=>]) {
        if comma.is_none() && input.peek(Token![,]) {
            comma = Some(input.span());
        }
        key.extend([input
            .parse::<proc_macro2::TokenTree>()
            .map_err(SyntaxError::from)?]);
    }
    if input.peek(Token![=>]) {
        return Err(literal_error(
            "`=>` is a rewrite; a map's entry is written `key -> value`",
            input.span(),
        ));
    }
    if key.is_empty() {
        return Err(without_arrow(input.span()));
    }
    if !input.peek(Token![->]) {
        return Err(without_arrow(comma.unwrap_or(start)));
    }
    input.parse::<Token![->]>().map_err(SyntaxError::from)?;
    // A key that is no term past a comma is entries the comma separates, the
    // last of which has the arrow.
    let key = crate::term::parse_term_expression
        .parse2(key)
        .map_err(|error| comma.map_or_else(|| error.into(), without_arrow))?;
    let value = parse_part(input)?;
    Ok((key, value))
}

/// Reads one term of a literal: a value, or a set's element.
fn parse_part(input: ParseStream<'_>) -> Result<Expr, SyntaxError> {
    input
        .call(crate::term::parse_term_expression)
        .map_err(SyntaxError::from)
}

/// Reads the base `..rest`, which ends the literal.
fn parse_rest(collection: Collection, input: ParseStream<'_>) -> Result<Rest, SyntaxError> {
    let module = collection.module();
    let start = input.cursor();
    let dots = input.parse::<Token![..]>().map_err(SyntaxError::from)?;
    if input.is_empty() || input.peek(Token![,]) {
        let reason = match collection {
            Collection::Map => {
                "in a term, `map![..]` is a literal, and its rest is the map its entries are written over, `map![k -> v, ..m]`; an anonymous `..` names no map. A pattern reads a map's entries with `{ k -> v, .. }`, or `map![k -> v, ..]` in a `cells!` entry"
            }
            Collection::Set => {
                "in a term, `set![..]` is a literal, and its rest is the set its elements join, `set![x, ..s]`; an anonymous `..` names no set. A pattern matches a set's elements with `set::concat(set::item(x), rest)`"
            }
        };
        return Err(literal_error(reason, dots.spans[0]));
    }
    if input.peek(Token![=]) {
        return Err(literal_error(
            format!("the base of a `{module}![..]` is written `..base`"),
            input.span(),
        ));
    }
    let base = input
        .call(crate::term::parse_term_expression)
        .map_err(SyntaxError::from)?;
    let tokens = crate::term::tokens_between(start, input.cursor());
    // A trailing comma ends the literal; anything else follows the base.
    if input.peek(Token![,]) {
        input.parse::<Token![,]>().map_err(SyntaxError::from)?;
    }
    if !input.is_empty() {
        return Err(literal_error(
            format!(
                "the base `..rest` of a `{module}![..]` comes last: the written {} are applied over it, as `Ctor {{ f: e, ..base }}` writes its fields over `base`",
                match collection {
                    Collection::Map => "entries",
                    Collection::Set => "elements",
                }
            ),
            dots.spans[0].join(base.span()).unwrap_or(dots.spans[0]),
        ));
    }
    Ok(Rest { tokens, dots, base })
}

/// Rejects a map's key written twice: the two could never differ, so the
/// earlier entry's value would never be read. A set's element written twice is
/// the same element, and the union denotes the set exactly, so it is no
/// mistake.
fn reject_repeated_keys(entries: &[Entry]) -> Result<(), SyntaxError> {
    let mut seen = Vec::with_capacity(entries.len());
    for entry in entries {
        let text = entry.key.to_token_stream().to_string();
        if seen.contains(&text) {
            return Err(literal_error(
                format!(
                    "the key `{text}` is written twice; two keys written as the same term are one key, so the earlier entry's value would never be read: write the key once, with the value it maps to"
                ),
                entry.key.span(),
            ));
        }
        seen.push(text);
    }
    Ok(())
}

/// The first span of a term's tokens.
fn first_span(tokens: &TokenStream) -> Span {
    tokens
        .clone()
        .into_iter()
        .next()
        .map_or_else(Span::call_site, |token| match token {
            proc_macro2::TokenTree::Group(group) => group.span_open(),
            other => other.span(),
        })
}

/// `module::operation`, its module at `first` and its operation at `last`.
fn head(module: &str, operation: &str, first: Span, last: Span) -> Path {
    let mut segments = Punctuated::new();
    segments.push_value(PathSegment::from(Ident::new(module, first)));
    segments.push_punct(Token![::](last));
    segments.push_value(PathSegment::from(Ident::new(operation, last)));
    Path {
        leading_colon: None,
        segments,
    }
}

fn call<const N: usize>(head: Path, close: Span, operands: [Expr; N]) -> ExprCall {
    let mut args = Punctuated::new();
    for operand in operands {
        if !args.is_empty() {
            args.push_punct(Token![,](close));
        }
        args.push_value(operand);
    }
    ExprCall {
        attrs: Vec::new(),
        func: Box::new(Expr::Path(ExprPath {
            attrs: Vec::new(),
            qself: None,
            path: head,
        })),
        paren_token: syn::token::Paren(close),
        args,
    }
}
