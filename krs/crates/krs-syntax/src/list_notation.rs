//! Bracket notation for cons lists (F6): `[a, b, ..rest]` in a result and
//! `[a, b, rest @ ..]` in a pattern.
//!
//! A cons list is built from its front, so the brackets read like Rust's
//! slice pattern: the elements, front first, then optionally the rest of the
//! list. Each bracket level is notation for one constructor application, so
//! `[a, b, ..rest]` is `cons(a, cons(b, rest))` and `[a, b]` is
//! `cons(a, cons(b, empty()))`. The brackets do not name the list's sort, so
//! the parser writes each level as a call of the list marker
//! (`__list::cons`, `__list::empty`), which semantic analysis replaces with
//! the constructor of the cons list the position expects.
//!
//! The functions here return one level and leave the tail as notation (the
//! remaining brackets), so term validation, which marks each notation call it
//! validates, reaches every level.

use proc_macro2::Span;
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{
    Expr, ExprArray, ExprCall, ExprPath, Ident, Pat, PatIdent, PatSlice, PatWild, Path,
    PathSegment, RangeLimits, Token,
};

use crate::{SyntaxError, SyntaxErrorKind};

fn list_error(reason: impl Into<String>, span: Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::InvalidListNotation {
            reason: reason.into(),
        },
        span,
    )
}

/// The reason given for a `..` before the last element.
const REST_NOT_LAST: &str = "`..` may only end a list: a cons list is matched and built from its front, so its back is no constructor pattern; name the elements before the rest";

/// `__list::cons` or `__list::empty`, its module at `first` and its name at
/// `last`.
fn marker_path(name: &str, first: Span, last: Span) -> Path {
    let mut segments = Punctuated::new();
    segments.push_value(PathSegment::from(Ident::new("__list", first)));
    segments.push_punct(Token![::](last));
    segments.push_value(PathSegment::from(Ident::new(name, last)));
    Path {
        leading_colon: None,
        segments,
    }
}

/// The marker path of one level: `__list::cons` from the level's first
/// element to the end of the authored brackets `list`, or `__list::empty`
/// over the brackets when no element remains.
///
/// The authored brackets' whole span is the one bracket span that is the
/// same where a macro re-emits the tokens and where the collector reparses
/// the source: a re-emitted group's closing span may cover the whole group.
pub(crate) fn level_head(first: Option<Span>, list: Span) -> Path {
    match first {
        Some(first) => marker_path("cons", first, list),
        None => marker_path("empty", list, list),
    }
}

/// The first span of an element's tokens.
fn first_span(tokens: &impl quote::ToTokens) -> Span {
    tokens
        .to_token_stream()
        .into_iter()
        .next()
        .map_or_else(Span::call_site, |token| match token {
            proc_macro2::TokenTree::Group(group) => group.span_open(),
            other => other.span(),
        })
}

/// One level of a result `[e1, .., en]`, `[e1, .., en, ..rest]`: the call
/// `__list::cons(e1, tail)`, where the tail is `[e2, ..]`, the expression
/// `rest` once only `..rest` remains, or `[]`, which is `__list::empty()`.
///
/// # Errors
///
/// Returns [`SyntaxErrorKind::InvalidListNotation`] for a `..` before the
/// last element, `[..rest]`, an anonymous `..` (which keeps a rest only in a
/// readable record cell), and `..=`.
pub(crate) fn result_level(array: &ExprArray) -> Result<ExprCall, SyntaxError> {
    crate::term::reject_attributes(&array.attrs, array.span())?;
    let close = array.bracket_token.span.join();
    let elements = array.elems.iter().collect::<Vec<_>>();
    for (index, element) in elements.iter().enumerate() {
        let Expr::Range(range) = element else {
            continue;
        };
        if index + 1 != elements.len() {
            return Err(list_error(REST_NOT_LAST, range.limits.span()));
        }
        if range.start.is_some() || matches!(range.limits, RangeLimits::Closed(_)) {
            return Err(list_error(
                "a list's rest is written `..rest`, after the elements it follows",
                range.span(),
            ));
        }
        if range.end.is_none() {
            return Err(list_error(
                "an anonymous `..` keeps the rest only in a readable record cell, where the pattern's `..` matched it; elsewhere name it: `rest @ ..` in the pattern and `..rest` in the result",
                range.limits.span(),
            ));
        }
        if index == 0 {
            return Err(list_error(
                "`[..rest]` has no element: it is the list `rest` itself, so write `rest`",
                range.limits.span(),
            ));
        }
    }
    let mut arguments = Punctuated::new();
    let Some((first, rest)) = elements.split_first() else {
        return Ok(call(level_head(None, close), close, arguments));
    };
    let head = level_head(Some(first_span(first)), close);
    arguments.push_value((*first).clone());
    arguments.push_punct(Token![,](close));
    let tail = match rest {
        [Expr::Range(range)] => range
            .end
            .as_deref()
            .cloned()
            .expect("an anonymous rest is rejected above"),
        rest => {
            let mut elems = Punctuated::new();
            for element in rest {
                elems.push((*element).clone());
            }
            Expr::Array(ExprArray {
                attrs: Vec::new(),
                bracket_token: tail_brackets(close),
                elems,
            })
        }
    };
    arguments.push_value(tail);
    Ok(call(head, close, arguments))
}

/// The brackets of the tail of a level, which span the authored list: the
/// next level's marker spans from its first element to the list's end.
fn tail_brackets(close: Span) -> syn::token::Bracket {
    let mut group = proc_macro2::Group::new(
        proc_macro2::Delimiter::Bracket,
        proc_macro2::TokenStream::new(),
    );
    group.set_span(close);
    syn::token::Bracket(group.delim_span())
}

fn call(head: Path, close: Span, args: Punctuated<Expr, Token![,]>) -> ExprCall {
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

/// One level of a pattern `[p1, .., pn]`, `[p1, .., pn, ..]`, or
/// `[p1, .., pn, rest @ ..]`: the marker head and its operands, `p1` and the
/// tail, which is `[p2, ..]`, the binder `rest`, `_` for an anonymous `..`,
/// or no operand at all for `[]`.
///
/// # Errors
///
/// Returns [`SyntaxErrorKind::InvalidListNotation`] for a `..` before the
/// last element, `[..]` and `[rest @ ..]`, which name no element, and a rest
/// that is neither `..` nor `name @ ..`.
pub(crate) fn pattern_level(slice: &PatSlice) -> Result<(Path, Vec<Pat>), SyntaxError> {
    crate::term::reject_attributes(&slice.attrs, slice.span())?;
    let close = slice.bracket_token.span.join();
    let elements = slice.elems.iter().collect::<Vec<_>>();
    for (index, element) in elements.iter().enumerate() {
        let Some(rest) = rest_of(element) else {
            continue;
        };
        if index + 1 != elements.len() {
            return Err(list_error(REST_NOT_LAST, rest.span()));
        }
        if index == 0 {
            return Err(list_error(
                "`[..]` and `[rest @ ..]` name no element: the first matches any list, so write `_`, and the second is the binder `rest` itself",
                rest.span(),
            ));
        }
    }
    let Some((first, rest)) = elements.split_first() else {
        return Ok((level_head(None, close), Vec::new()));
    };
    let head = level_head(Some(first_span(first)), close);
    let tail = match rest {
        [Pat::Rest(dots)] => Pat::Wild(PatWild {
            attrs: Vec::new(),
            underscore_token: Token![_](dots.dot2_token.spans[0]),
        }),
        [
            Pat::Ident(
                identifier @ PatIdent {
                    subpat: Some((_, subpattern)),
                    ..
                },
            ),
        ] if matches!(subpattern.as_ref(), Pat::Rest(_)) => Pat::Ident(PatIdent {
            subpat: None,
            ..identifier.clone()
        }),
        rest => {
            let mut elems = Punctuated::new();
            for element in rest {
                elems.push((*element).clone());
            }
            Pat::Slice(PatSlice {
                attrs: Vec::new(),
                bracket_token: tail_brackets(close),
                elems,
            })
        }
    };
    Ok((head, vec![(*first).clone(), tail]))
}

/// The rest element of a slice pattern, `..` or `name @ ..`, if `element`
/// is one.
fn rest_of(element: &Pat) -> Option<&Pat> {
    match element {
        Pat::Rest(_) => Some(element),
        Pat::Ident(PatIdent {
            subpat: Some((_, subpattern)),
            ..
        }) if matches!(subpattern.as_ref(), Pat::Rest(_)) => Some(element),
        _ => None,
    }
}
