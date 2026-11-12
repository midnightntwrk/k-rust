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

thread_local! {
    /// Whether the brackets being read are a `k::patterns!` step's, where a list may hold
    /// several rests (FB-49 R-2).
    static PATTERN_STEP: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Runs `read` with the brackets it reads taken as a `k::patterns!` step's: a list there may
/// hold several rests, `[.., a, .., b, ..]`, the items occurring in that order. A step is a
/// set of states and holds when some split of the list matches, so the one-rest rule's
/// reason, that a result uses one binding, does not apply to it.
pub fn with_pattern_steps<T>(read: impl FnOnce() -> T) -> T {
    /// Restores the outer reading when dropped, so a read that unwinds (a proc-macro server
    /// reuses its threads) leaves no later bracket read as a pattern step's.
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            PATTERN_STEP.with(|step| step.set(self.0));
        }
    }
    let _restore = Restore(PATTERN_STEP.with(|step| step.replace(true)));
    read()
}

/// Whether `group`, a bracketed value, holds two or more rests (`..` or `name @ ..`).
pub(crate) fn holds_several_rests(group: &proc_macro2::Group) -> bool {
    use proc_macro2::TokenTree;
    let items = group.stream().into_iter().collect::<Vec<_>>();
    items
        .split(|token| matches!(token, TokenTree::Punct(comma) if comma.as_char() == ','))
        .filter(|item| {
            let rest = match item {
                [TokenTree::Ident(_), TokenTree::Punct(at), rest @ ..] if at.as_char() == '@' => {
                    rest
                }
                rest => rest,
            };
            matches!(rest, [TokenTree::Punct(a), TokenTree::Punct(b)]
                if a.as_char() == '.' && b.as_char() == '.')
        })
        .count()
        > 1
}

/// Whether the brackets being read are a pattern step's ([`with_pattern_steps`]).
pub(crate) fn in_pattern_step() -> bool {
    PATTERN_STEP.with(std::cell::Cell::get)
}

/// The marker path of a pattern step's level `__list::join(rest, remaining)`, at its rest.
fn join_head(rest: Span, brackets: Span) -> Path {
    marker_path("join", rest, brackets)
}

/// The reason given for a second rest in one bracket.
pub(crate) const TWO_RESTS: &str = "a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`";

/// The refusal of a second rest in one bracket, at `span` ([`TWO_RESTS`]).
pub(crate) fn two_rests(span: Span) -> SyntaxError {
    list_error(TWO_RESTS, span)
}

/// Whether `error` is the refusal of a second rest in one bracket ([`TWO_RESTS`]).
pub(crate) fn is_two_rests(error: &SyntaxError) -> bool {
    matches!(
        error.kind(),
        SyntaxErrorKind::InvalidListNotation { reason } if reason == TWO_RESTS
    )
}

/// The reason given for an anonymous `..` in a result's list notation, which names no list: a
/// result's `..` keeps a rest only in a cell's own brackets, a list cell's (a readable record's
/// list cell, a `cells!` leaf's `Cell([x, ..])` or `Cell([..])`) or an instance's child's, where
/// it is read before list notation is. Elsewhere it is a term's list notation, where the rest is
/// named. A result's group record and `Some(..)` say their own ([`GROUP_CHILD_ANONYMOUS_REST`],
/// [`PRESENT_ANONYMOUS_REST`]).
pub(crate) const ANONYMOUS_REST: &str = "an anonymous `..` keeps the rest only in a cell's own brackets, a list cell's or an instance's child's, where the pattern's `..` matched it; elsewhere a list's rest is named: `rest @ ..` in the pattern and `..rest` in the result";

/// [`ANONYMOUS_REST`] in a result's group record (`H { hl: [x, ..], hb: 0 }`, a `cells!`
/// `k::fragment![..]`, a present `?` group's record): the record is read as one term of the
/// group, which writes each child's whole content, so no child keeps a rest there yet. A list
/// child names its rest; a fixed group's computation child is written as its own cell, where its
/// `..` keeps the rest; a `?` group's computation child is not lowered at all yet (F5).
pub(crate) const GROUP_CHILD_ANONYMOUS_REST: &str = "an anonymous `..` in a result group record's child keeps no rest yet (a stated limitation): the record is read as one term of the group, which writes each child's whole content; a list child's rest is named instead, `rest @ ..` in the pattern and `..rest` in the result, and a fixed group's computation child keeps its rest written as its own cell (`c: [x, ..]` in a readable record, `G::c: KCell(x, ..)` in `cells!`); a `?` group's computation child (`Some(G { c: [x, ..], .. })`) is not supported yet in a rule, with or without a rest";

/// [`ANONYMOUS_REST`] inside a result's `Some(..)` (`Some([x, ..])`): the present cell's content
/// keeps no rest there yet, but over the subject's `Some([..])`, which keeps the present cell.
pub(crate) const PRESENT_ANONYMOUS_REST: &str = "an anonymous `..` inside a result's `Some(..)` keeps no rest yet (a stated limitation), except as `Some([..])` over the subject's `Some([..])`, which keeps the present cell; elsewhere the rest is named: `rest @ ..` in the pattern and `..rest` in the result";

/// Whether `error` is the refusal of an anonymous `..` in a result's list notation, in any of the
/// places that say it ([`ANONYMOUS_REST`]).
pub(crate) fn is_anonymous_rest(error: &SyntaxError) -> bool {
    matches!(
        error.kind(),
        SyntaxErrorKind::InvalidListNotation { reason }
            if [ANONYMOUS_REST, GROUP_CHILD_ANONYMOUS_REST, PRESENT_ANONYMOUS_REST]
                .contains(&reason.as_str())
    )
}

/// `error` as the place `reason` says it, where `error` is the refusal of an anonymous `..` in a
/// result's list notation ([`ANONYMOUS_REST`]); any other error as it is.
pub(crate) fn anonymous_rest_in(error: SyntaxError, reason: &'static str) -> SyntaxError {
    if is_anonymous_rest(&error) {
        list_error(reason, error.span())
    } else {
        error
    }
}

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
        && ["cons", "snoc", "empty", "join"]
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
/// `[..rest]`, an anonymous `..` (which keeps a rest only in a list cell's
/// own brackets, read before this), and `..=`.
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
            return Err(list_error(ANONYMOUS_REST, range.limits.span()));
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
    let several = in_pattern_step()
        && elements
            .iter()
            .filter(|element| rest_of(element).is_some())
            .count()
            > 1;
    if several {
        // A step's list with several rests: a rest first is `join(rest, remaining)`, an item
        // first `cons(item, remaining)`, so the levels spell the items in order between rests.
        if elements.iter().all(|element| rest_of(element).is_some()) {
            return Err(list_error(
                "`[.., ..]` names no element: it matches any list, so write `_`",
                slice.span(),
            ));
        }
        let first = elements[0];
        return Ok(if rest_of(first).is_some() {
            (
                join_head(first_span(first), close),
                vec![
                    pattern_remainder(&[first], close),
                    pattern_remainder(&elements[1..], close),
                ],
            )
        } else {
            (
                level_head(Some(first_span(first)), close),
                vec![first.clone(), pattern_remainder(&elements[1..], close)],
            )
        });
    }
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
                "`[..]` and `[rest @ ..]` name no element: the first matches any list, so write `_`, or a binder `rest` to write the list again (`[a, ..rest]`), and the second is the binder `rest` itself",
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
