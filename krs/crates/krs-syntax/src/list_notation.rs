//! Bracket list notation: `[a, b, ..rest]` in a result and
//! `[a, b, rest @ ..]` in a pattern, for cons lists (F6) and K's builtin
//! `List`.
//!
//! The brackets read like Rust's slice pattern: the elements, front first,
//! and at most one rest, anywhere. Elements before the rest are the list's
//! front and elements after it its back. Each bracket level is notation for
//! one step of building the list: `[a, ..rest]` is `cons(a, rest)`, the list
//! whose first element is `a`, and `[..rest, z]` is `snoc(rest, z)`, the list
//! whose last element is `z`; `[a, b]` is `cons(a, cons(b, empty()))` and
//! `[a, ..mid, z]` is `cons(a, snoc(mid, z))`. The brackets do not name the
//! list's sort, so the parser writes each level as a call of the list marker
//! (`__list::cons`, `__list::snoc`, `__list::empty`), which semantic analysis
//! replaces with the terms of the list the position expects: a cons list's
//! constructors, which build a list from its front only, or K's `List`
//! items.
//!
//! The functions here return one level and leave the remaining elements as
//! notation (the remaining brackets), so term validation, which marks each
//! notation call it validates, reaches every level.

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

/// The reason given for a second rest in one bracket.
pub(crate) const TWO_RESTS: &str = "a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`";

/// `__list::cons`, `__list::snoc`, or `__list::empty`, its module at `first`
/// and its name at `last`.
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

/// Whether `head` is the marker of a level of list notation, which denotes a
/// list's constructors rather than an operation.
pub(crate) fn is_level_head(head: &Path) -> bool {
    head.leading_colon.is_none()
        && head.segments.len() == 2
        && head.segments[0].ident == "__list"
        && ["cons", "snoc", "empty"]
            .iter()
            .any(|name| head.segments[1].ident == name)
}

/// The marker path of a level taken from the back, `__list::snoc`, from the
/// level's last element to the end of the authored brackets. Each
/// element is the head of exactly one level, so no two levels of one
/// bracket share a marker span.
fn snoc_head(last: Span, brackets: Span) -> Path {
    marker_path("snoc", last, brackets)
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

/// One level of a result `[e1, .., en]`, `[e1, .., ei, ..rest, .., en]`:
/// while the first entry is an element, the call `__list::cons(e1, tail)`,
/// where the tail is the remaining brackets `[e2, ..]`; once the rest leads,
/// the call `__list::snoc(init, en)`, where the init is `[..rest, .., en-1]`.
/// Brackets holding only `..rest` are the expression `rest`, and `[]` is
/// `__list::empty()`.
///
/// # Errors
///
/// Returns [`SyntaxErrorKind::InvalidListNotation`] for a second rest,
/// `[..rest]`, an anonymous `..` (which keeps a rest only in a readable
/// record cell), and `..=`.
pub(crate) fn result_level(array: &ExprArray) -> Result<ExprCall, SyntaxError> {
    crate::term::reject_attributes(&array.attrs, array.span())?;
    let close = array.bracket_token.span.join();
    let elements = array.elems.iter().collect::<Vec<_>>();
    let mut rest_index = None;
    for (index, element) in elements.iter().enumerate() {
        let Expr::Range(range) = element else {
            continue;
        };
        if rest_index.is_some() {
            return Err(list_error(TWO_RESTS, range.limits.span()));
        }
        if range.start.is_some() || matches!(range.limits, RangeLimits::Closed(_)) {
            return Err(list_error(
                "a list's rest is written `..rest`, where the list `rest` stands among the elements",
                range.span(),
            ));
        }
        if range.end.is_none() {
            return Err(list_error(
                "an anonymous `..` keeps the rest only in a readable record cell, where the pattern's `..` matched it; elsewhere name it: `rest @ ..` in the pattern and `..rest` in the result",
                range.limits.span(),
            ));
        }
        if elements.len() == 1 {
            return Err(list_error(
                "`[..rest]` has no element: it is the list `rest` itself, so write `rest`",
                range.limits.span(),
            ));
        }
        rest_index = Some(index);
    }
    let mut arguments = Punctuated::new();
    let Some(first) = elements.first() else {
        return Ok(call(level_head(None, close), close, arguments));
    };
    if rest_index == Some(0) {
        let (last, init) = elements
            .split_last()
            .expect("the rest is followed by an element");
        arguments.push_value(result_remainder(init, close));
        arguments.push_punct(Token![,](close));
        arguments.push_value((*last).clone());
        return Ok(call(snoc_head(first_span(last), close), close, arguments));
    }
    let head = level_head(Some(first_span(first)), close);
    arguments.push_value((*first).clone());
    arguments.push_punct(Token![,](close));
    arguments.push_value(result_remainder(&elements[1..], close));
    Ok(call(head, close, arguments))
}

/// What remains of a result's brackets after one level: the expression
/// `rest` when only `..rest` remains, else the remaining brackets.
fn result_remainder(remaining: &[&Expr], close: Span) -> Expr {
    if let [Expr::Range(range)] = remaining {
        return range
            .end
            .as_deref()
            .cloned()
            .expect("an anonymous rest is rejected before");
    }
    let mut elems = Punctuated::new();
    for element in remaining {
        elems.push((*element).clone());
    }
    Expr::Array(ExprArray {
        attrs: Vec::new(),
        bracket_token: tail_brackets(close),
        elems,
    })
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

/// One level of a pattern `[p1, .., pn]`, `[p1, .., pi, .., pn]`, or
/// `[p1, .., pi, rest @ .., .., pn]`: while the first entry is an element,
/// the marker `__list::cons` and its operands `p1` and the remaining
/// brackets `[p2, ..]`; once the rest leads, the marker `__list::snoc` and
/// its operands, the brackets `[rest @ .., .., pn-1]` and `pn`. Brackets
/// holding only the rest are the binder `rest`, or `_` for an anonymous
/// `..`, and `[]` is the marker `__list::empty` with no operand.
///
/// # Errors
///
/// Returns [`SyntaxErrorKind::InvalidListNotation`] for a second rest,
/// `[..]` and `[rest @ ..]`, which name no element, and a rest that is
/// neither `..` nor `name @ ..`.
pub(crate) fn pattern_level(slice: &PatSlice) -> Result<(Path, Vec<Pat>), SyntaxError> {
    crate::term::reject_attributes(&slice.attrs, slice.span())?;
    let close = slice.bracket_token.span.join();
    let elements = slice.elems.iter().collect::<Vec<_>>();
    let mut rest_index = None;
    for (index, element) in elements.iter().enumerate() {
        let Some(rest) = rest_of(element) else {
            continue;
        };
        if rest_index.is_some() {
            return Err(list_error(TWO_RESTS, rest.span()));
        }
        if elements.len() == 1 {
            return Err(list_error(
                "`[..]` and `[rest @ ..]` name no element: the first matches any list, so write `_`, and the second is the binder `rest` itself",
                rest.span(),
            ));
        }
        rest_index = Some(index);
    }
    let Some(first) = elements.first() else {
        return Ok((level_head(None, close), Vec::new()));
    };
    if rest_index == Some(0) {
        let (last, init) = elements
            .split_last()
            .expect("the rest is followed by an element");
        return Ok((
            snoc_head(first_span(last), close),
            vec![pattern_remainder(init, close), (*last).clone()],
        ));
    }
    let head = level_head(Some(first_span(first)), close);
    Ok((
        head,
        vec![(*first).clone(), pattern_remainder(&elements[1..], close)],
    ))
}

/// What remains of a pattern's brackets after one level: `_` when only an
/// anonymous `..` remains, the binder `rest` when only `rest @ ..` remains,
/// else the remaining brackets.
fn pattern_remainder(remaining: &[&Pat], close: Span) -> Pat {
    match remaining {
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
        remaining => {
            let mut elems = Punctuated::new();
            for element in remaining {
                elems.push((*element).clone());
            }
            Pat::Slice(PatSlice {
                attrs: Vec::new(),
                bracket_token: tail_brackets(close),
                elems,
            })
        }
    }
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
