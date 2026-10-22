//! Width-bounded layout of KRS term token trees.
//!
//! A term is turned into a [`Doc`] whose groups are the term's delimited
//! groups (calls, records, tuples, lists) and its top-level alternatives
//! (`A | B` in a pattern, `a || b` and `a && b` in an expression).
//! The printer lays a group out on one line when it fits in the remaining
//! width, and otherwise breaks it, outside in: a delimited group puts one
//! item per line, indented, and an alternative chain puts one alternative per
//! line with its operator leading.
//! Layout depends only on the tokens and on where line comments sit between
//! them, never on the input's whitespace, so formatting is idempotent.
//! Tokens are never added, removed, or reordered: a broken list keeps exactly
//! the commas its source has.

use krs_syntax::SourceRange;
use proc_macro2::{Delimiter, Group, Spacing, TokenTree};
use unicode_width::UnicodeWidthStr;

/// One layout document.
#[derive(Clone, Debug)]
pub(crate) enum Doc {
    /// Text without a newline.
    Text(String),
    /// A line comment, with any separating space; it does not count toward
    /// the width, since no break can shorten it.
    Comment(String),
    /// A break: its text when the enclosing group fits on one line, else a
    /// new line at the nesting indentation.
    Line(&'static str),
    /// A new line that always happens (after a line comment); a group
    /// holding one never fits on one line.
    Hard,
    /// Its document with the nesting indentation increased.
    Nest(usize, Box<Doc>),
    /// A unit laid out flat when it fits, or broken; `broken` forces it broken.
    Group { doc: Box<Doc>, broken: bool },
    /// Documents in sequence.
    Concat(Vec<Doc>),
    /// A clause's ` => result`: it stays on the current line when the
    /// result fits there whole, or when the result must break anyway and
    /// its first line fits; otherwise `=> result` starts a new line.
    Arm(Box<Doc>),
}

impl Doc {
    pub(crate) fn text(text: impl Into<String>) -> Self {
        Self::Text(text.into())
    }

    pub(crate) fn group(doc: Self) -> Self {
        Self::Group {
            doc: Box::new(doc),
            broken: false,
        }
    }

    pub(crate) fn nest(indent: usize, doc: Self) -> Self {
        Self::Nest(indent, Box::new(doc))
    }
}

/// Indentation of one nesting level, Rust's four spaces.
pub(crate) const INDENT: usize = 4;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Mode {
    Flat,
    Break,
    /// Measuring a document's first line when its outermost group breaks:
    /// text before that group.
    Head,
    /// Inside that outermost group, whose own breaks end the line and whose
    /// nested groups stay flat.
    Outer,
}

/// Lays `doc` out in `width` columns; a line exceeds the width only where
/// no break is possible.
pub(crate) fn print(doc: &Doc, width: usize) -> Vec<String> {
    let mut printer = Printer::default();
    let mut stack = vec![(0_usize, Mode::Break, doc)];
    while let Some((indent, mode, doc)) = stack.pop() {
        match doc {
            Doc::Text(text) | Doc::Comment(text) => printer.push(text),
            Doc::Line(flat) if mode == Mode::Flat => printer.push(flat),
            Doc::Line(_) | Doc::Hard => printer.newline(indent),
            Doc::Nest(extra, inner) => stack.push((indent + extra, mode, inner)),
            Doc::Concat(items) => stack.extend(items.iter().rev().map(|item| (indent, mode, item))),
            Doc::Group { doc: inner, broken } => {
                let flat = mode == Mode::Flat
                    || (!broken
                        && fits(
                            width.saturating_sub(printer.column),
                            &[(Mode::Flat, inner)],
                            &stack,
                        ));
                stack.push((indent, if flat { Mode::Flat } else { Mode::Break }, inner));
            }
            Doc::Arm(result) => {
                let remaining = width.saturating_sub(printer.column + ARROW.len());
                let whole = mode == Mode::Flat || fits(remaining, &[(Mode::Flat, result)], &stack);
                let next_line = width.saturating_sub(indent + ARROW.trim_start().len());
                let same_line = whole
                    || (!fits(next_line, &[(Mode::Flat, result)], &stack)
                        && fits(remaining, &[(Mode::Head, result)], &stack));
                if same_line {
                    printer.push(ARROW);
                } else {
                    printer.newline(indent);
                    printer.push(ARROW.trim_start());
                }
                stack.push((indent, if whole { Mode::Flat } else { Mode::Break }, result));
            }
        }
    }
    printer.finish()
}

const ARROW: &str = " => ";

/// The one-line form of a document without forced breaks.
pub(crate) fn flat(doc: &Doc) -> Option<String> {
    let lines = print(doc, usize::MAX);
    match lines.as_slice() {
        [] => Some(String::new()),
        [line] => Some(line.clone()),
        _ => None,
    }
}

/// Whether `first`, flat, and what follows it up to the next possible break
/// fit in `remaining` columns.
fn fits(remaining: usize, first: &[(Mode, &Doc)], rest: &[(usize, Mode, &Doc)]) -> bool {
    let mut remaining = remaining;
    let mut stack = first.to_vec();
    let mut rest = rest.iter().rev();
    loop {
        let (mode, doc) = match stack.pop() {
            Some(entry) => entry,
            None => match rest.next() {
                Some(&(_, mode, doc)) => (mode, doc),
                None => return true,
            },
        };
        match doc {
            Doc::Text(text) => match remaining.checked_sub(text.width()) {
                Some(left) => remaining = left,
                None => return false,
            },
            Doc::Comment(_) => {}
            Doc::Line(flat) if mode == Mode::Flat => match remaining.checked_sub(flat.width()) {
                Some(left) => remaining = left,
                None => return false,
            },
            Doc::Hard => return mode != Mode::Flat,
            Doc::Nest(_, inner) => stack.push((mode, inner)),
            Doc::Concat(items) => stack.extend(items.iter().rev().map(|item| (mode, item))),
            // An arm that follows may start a new line.
            Doc::Arm(result) if mode == Mode::Flat => match remaining.checked_sub(ARROW.len()) {
                Some(left) => {
                    remaining = left;
                    stack.push((mode, result));
                }
                None => return false,
            },
            Doc::Line(_) | Doc::Arm(_) => return true,
            // A group that follows may still break at its first line, so
            // only the text before that line must fit.
            Doc::Group { doc: inner, broken } => stack.push((
                match mode {
                    Mode::Flat if *broken => return false,
                    Mode::Outer if *broken => Mode::Break,
                    Mode::Flat | Mode::Outer => Mode::Flat,
                    Mode::Break => Mode::Break,
                    Mode::Head => Mode::Outer,
                },
                inner,
            )),
        }
    }
}

#[derive(Default)]
struct Printer {
    lines: Vec<String>,
    current: String,
    column: usize,
}

impl Printer {
    fn push(&mut self, text: &str) {
        self.current.push_str(text);
        self.column += text.width();
    }

    /// Starts a line at `indent`; a line holding only indentation is reused,
    /// so a comment's forced break and a group's break make one new line.
    fn newline(&mut self, indent: usize) {
        if !self.current.trim().is_empty() {
            self.lines
                .push(std::mem::take(&mut self.current).trim_end().to_owned());
        }
        self.current = " ".repeat(indent);
        self.column = indent;
    }

    fn finish(mut self) -> Vec<String> {
        if !self.current.trim().is_empty() {
            self.lines.push(self.current.trim_end().to_owned());
        }
        self.lines
    }
}

/// The syntactic position of a term, which decides where it may break
/// besides its delimited groups.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Context {
    /// A left-hand side: `|` separates alternatives, aligned with the first.
    Pattern,
    /// A right-hand side or condition: `||`, else `&&`, separates operands,
    /// continued one level deeper.
    Expression,
    /// A macro invocation's arguments, which break only at their commas.
    Macro,
}

/// The line comments of one source and the text they are sliced from.
#[derive(Clone, Copy)]
pub(crate) struct Comments<'a> {
    source: &'a str,
    ranges: &'a [SourceRange],
}

impl<'a> Comments<'a> {
    pub(crate) fn new(source: &'a str, ranges: &'a [SourceRange]) -> Self {
        Self { source, ranges }
    }

    pub(crate) fn none() -> Self {
        Self {
            source: "",
            ranges: &[],
        }
    }

    fn within(&self, start: usize, end: usize) -> impl Iterator<Item = &SourceRange> {
        self.ranges
            .iter()
            .filter(move |range| range.start() >= start && range.end() <= end)
    }

    fn text(&self, range: &SourceRange) -> String {
        range
            .text(self.source)
            .unwrap_or_default()
            .trim_end()
            .to_owned()
    }
}

#[derive(Clone, Debug)]
enum AtomKind {
    Word,
    Group(Delimiter),
    Punctuation(String),
}

#[derive(Clone, Debug)]
struct Atom {
    kind: AtomKind,
    text: String,
    /// The layout of a delimited group.
    doc: Option<Doc>,
    start: usize,
    end: usize,
}

impl Atom {
    fn is(&self, text: &str) -> bool {
        matches!(&self.kind, AtomKind::Punctuation(value) if value == text)
    }

    fn doc(&self) -> Doc {
        self.doc.clone().unwrap_or_else(|| Doc::text(&self.text))
    }
}

/// Tokens parsed from a slice of a larger source, with the slice's offset.
#[derive(Clone, Debug)]
pub(crate) struct Component {
    pub(crate) tokens: Vec<TokenTree>,
    pub(crate) offset: usize,
}

impl Component {
    /// The source ranges strictly inside the component's top-level groups,
    /// where comments stay in place instead of moving before the clause.
    pub(crate) fn group_interiors(&self) -> Vec<(usize, usize)> {
        self.tokens
            .iter()
            .filter_map(|token| match token {
                TokenTree::Group(group) => Some((
                    self.offset + group.span_open().byte_range().end,
                    self.offset + group.span_close().byte_range().start,
                )),
                _ => None,
            })
            .collect()
    }
}

/// The layout of a sequence of tokens, such as a clause's pattern, breaking
/// at its top-level alternatives and inside its groups.
pub(crate) fn sequence(component: &Component, context: Context, comments: Comments<'_>) -> Doc {
    let atoms = atoms(&component.tokens, component.offset, context, comments);
    let spaces = spacing(&atoms);
    item(&atoms, &spaces, 0..atoms.len(), &[], context)
}

/// One-line rendering of tokens that hold no comments.
pub(crate) fn render(tokens: &[TokenTree]) -> String {
    let component = Component {
        tokens: tokens.to_vec(),
        offset: 0,
    };
    flat(&sequence(&component, Context::Expression, Comments::none())).unwrap_or_default()
}

/// The layout of a comma-separated list of top-level items, such as a
/// `where` list: flat after a space, or one item per line, indented.
pub(crate) fn list(component: &Component, context: Context, comments: Comments<'_>) -> Doc {
    let atoms = atoms(&component.tokens, component.offset, context, comments);
    let spaces = spacing(&atoms);
    let mut body = Vec::new();
    for (range, separator) in split_items(&atoms) {
        body.push(Doc::Line(" "));
        body.push(item(&atoms, &spaces, range, &[], context));
        if let Some(separator) = separator {
            body.push(Doc::text(&atoms[separator].text));
        }
    }
    Doc::group(Doc::nest(INDENT, Doc::Concat(body)))
}

/// The layout of a delimited group; `broken` puts its items on their own
/// lines even when they would fit on one.
pub(crate) fn delimited(
    component: &Component,
    context: Context,
    comments: Comments<'_>,
    broken: bool,
) -> Option<Doc> {
    let [TokenTree::Group(group)] = component.tokens.as_slice() else {
        return None;
    };
    Some(group_doc(
        group,
        component.offset,
        context,
        comments,
        if broken { Shape::Broken } else { Shape::Free },
    ))
}

fn atoms(
    tokens: &[TokenTree],
    offset: usize,
    context: Context,
    comments: Comments<'_>,
) -> Vec<Atom> {
    let mut output: Vec<Atom> = Vec::new();
    let mut index = 0_usize;
    while index < tokens.len() {
        let range = tokens[index].span().byte_range();
        let (start, end) = (offset + range.start, offset + range.end);
        match &tokens[index] {
            TokenTree::Group(group) => {
                // A macro's arguments break only at their commas.
                let inner = if output.last().is_some_and(|atom| atom.is("!")) {
                    Context::Macro
                } else {
                    context
                };
                let shape = if output
                    .last()
                    .is_some_and(|atom| matches!(atom.kind, AtomKind::Word | AtomKind::Group(_)))
                {
                    Shape::Arguments
                } else {
                    Shape::Free
                };
                output.push(Atom {
                    kind: AtomKind::Group(group.delimiter()),
                    text: String::new(),
                    doc: Some(group_doc(group, offset, inner, comments, shape)),
                    start,
                    end,
                });
                index += 1;
            }
            TokenTree::Ident(ident) => {
                output.push(Atom {
                    kind: AtomKind::Word,
                    text: ident.to_string(),
                    doc: None,
                    start,
                    end,
                });
                index += 1;
            }
            TokenTree::Literal(literal) => {
                output.push(Atom {
                    kind: AtomKind::Word,
                    text: literal.to_string(),
                    doc: None,
                    start,
                    end,
                });
                index += 1;
            }
            // A minus after an operator or at the start, followed by a literal,
            // is the sign of a negative literal such as `-1`: keep it attached.
            TokenTree::Punct(punct)
                if punct.as_char() == '-'
                    && matches!(tokens.get(index + 1), Some(TokenTree::Literal(_)))
                    && output
                        .last()
                        .is_none_or(|atom| matches!(atom.kind, AtomKind::Punctuation(_))) =>
            {
                let Some(TokenTree::Literal(literal)) = tokens.get(index + 1) else {
                    unreachable!("the guard requires a following literal");
                };
                output.push(Atom {
                    kind: AtomKind::Word,
                    text: format!("-{literal}"),
                    doc: None,
                    start,
                    end: offset + literal.span().byte_range().end,
                });
                index += 2;
            }
            TokenTree::Punct(punct) => {
                let mut text = punct.as_char().to_string();
                let mut end = end;
                index += 1;
                if punct.spacing() == Spacing::Joint
                    && let Some(TokenTree::Punct(next)) = tokens.get(index)
                    && punctuation_pair(punct.as_char(), next.as_char())
                {
                    text.push(next.as_char());
                    end = offset + next.span().byte_range().end;
                    index += 1;
                    if text == ".."
                        && next.spacing() == Spacing::Joint
                        && let Some(TokenTree::Punct(last)) = tokens.get(index)
                        && last.as_char() == '='
                    {
                        text.push('=');
                        end = offset + last.span().byte_range().end;
                        index += 1;
                    }
                }
                output.push(Atom {
                    kind: AtomKind::Punctuation(text.clone()),
                    text,
                    doc: None,
                    start,
                    end,
                });
            }
        }
    }
    output
}

fn punctuation_pair(first: char, second: char) -> bool {
    matches!(
        (first, second),
        (':', ':')
            | ('=' | '-', '>')
            | ('.', '.')
            | ('<', '<' | '=')
            | ('>', '>' | '=')
            | ('&', '&' | '=')
            | ('|', '|' | '=')
            | ('=' | '!' | '+' | '-' | '*' | '/' | '%' | '^', '=')
    )
}

/// Whether a space precedes each atom on one line.
fn spacing(atoms: &[Atom]) -> Vec<bool> {
    let mut output = Vec::with_capacity(atoms.len());
    // Open turbofish angle brackets (`Choose::<Exp>`, KF-027), which hug
    // their arguments like Rust's own spelling.
    let mut turbofish = 0_usize;
    let mut after_close = false;
    for (index, atom) in atoms.iter().enumerate() {
        let opens = index > 0 && atom.is("<") && atoms[index - 1].is("::");
        let closes = turbofish > 0 && atom.is(">");
        let after_open = index > 0 && turbofish > 0 && atoms[index - 1].is("<");
        let call = after_close && matches!(atom.kind, AtomKind::Group(Delimiter::Parenthesis));
        // A bit range between integers, as in a `k::bits!` modifier's
        // `[10:5]`, keeps the spelling of the ISA manuals.
        let integer = |atom: &Atom| {
            matches!(atom.kind, AtomKind::Word)
                && atom
                    .text
                    .starts_with(|character: char| character.is_ascii_digit())
        };
        let bit_range =
            index > 1 && integer(atom) && atoms[index - 1].is(":") && integer(&atoms[index - 2]);
        output.push(
            index > 0
                && !closes
                && !after_open
                && !call
                && !bit_range
                && needs_space(
                    index.checked_sub(2).map(|before| &atoms[before]),
                    &atoms[index - 1],
                    atom,
                ),
        );
        if opens {
            turbofish += 1;
        }
        if closes {
            turbofish -= 1;
        }
        after_close = closes;
    }
    output
}

/// Whether a space separates `current` from `previous`, which follows
/// `before` (`None` at the start of a group).
fn needs_space(before: Option<&Atom>, previous: &Atom, current: &Atom) -> bool {
    if matches!(&current.kind, AtomKind::Punctuation(value) if matches!(value.as_str(), "," | ";" | ":" | "::" | "." | "?"))
    {
        return false;
    }
    if matches!(&previous.kind, AtomKind::Punctuation(value) if matches!(value.as_str(), "::" | "." | "#" | "$" | "!"))
    {
        return false;
    }
    // A record's rest `..base` (F5) hugs its base, as Rust's struct update
    // does; `..` after an operand is a range.
    if previous.is("..") && matches!(current.kind, AtomKind::Word) {
        return before.is_some_and(|before| !before.is(",") && !before.is("@"));
    }
    // A macro's `!` follows its name; a unary `!` after an operator does not.
    if matches!(&current.kind, AtomKind::Punctuation(value) if value == "!") {
        return matches!(previous.kind, AtomKind::Punctuation(_));
    }
    if matches!(
        (&previous.kind, &current.kind),
        (
            AtomKind::Word | AtomKind::Group(_),
            AtomKind::Group(Delimiter::Parenthesis | Delimiter::Bracket)
        )
    ) {
        return false;
    }
    // A prefix `&`, `*`, or `-` hugs its operand; after an operand it is a
    // binary operator, as in `a & 15`.
    if matches!(&previous.kind, AtomKind::Punctuation(value) if matches!(value.as_str(), "&" | "*" | "-"))
    {
        return before
            .is_some_and(|before| matches!(before.kind, AtomKind::Word | AtomKind::Group(_)));
    }
    true
}

/// A comment's place among a group's atoms.
struct Placed {
    text: String,
    /// It ends the line of the token before it.
    trailing: bool,
}

/// The items of a group: atom ranges and their separators.
fn split_items(atoms: &[Atom]) -> Vec<(std::ops::Range<usize>, Option<usize>)> {
    let mut items = Vec::new();
    let mut start = 0;
    for (index, atom) in atoms.iter().enumerate() {
        if atom.is(",") || atom.is(";") {
            items.push((start..index, Some(index)));
            start = index + 1;
        }
    }
    if start < atoms.len() {
        items.push((start..atoms.len(), None));
    }
    items
}

#[derive(Default)]
struct ItemComments {
    leading: Vec<String>,
    /// Comments ending the item's line, after its separator.
    trailing: Vec<String>,
}

/// How a delimited group may be laid out besides one item per line.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Shape {
    /// A parenthesized term, which hugs a chain of alternatives.
    Free,
    /// A call's or constructor's arguments.
    Arguments,
    /// Always one item per line, as a cell record is.
    Broken,
}

/// Where a group's own comments go.
struct Placement {
    /// Comments ending the open delimiter's line.
    after_open: Vec<String>,
    /// Comments on their own lines after the last item.
    dangling: Vec<String>,
    items: Vec<ItemComments>,
    /// Comments inside an item, before the atom of the same index.
    stray: Vec<Vec<Placed>>,
}

/// Places the comments directly in a group, not in a nested one: they keep
/// their place between items, and one inside an item breaks the item there.
fn place_comments(
    atoms: &[Atom],
    items: &[(std::ops::Range<usize>, Option<usize>)],
    open_end: usize,
    close_start: usize,
    comments: Comments<'_>,
) -> Placement {
    let mut after_open = Vec::new();
    let mut dangling = Vec::new();
    let mut item_comments = items
        .iter()
        .map(|_| ItemComments::default())
        .collect::<Vec<_>>();
    let mut stray: Vec<Vec<Placed>> = atoms.iter().map(|_| Vec::new()).collect();
    for range in comments.within(open_end, close_start) {
        if atoms
            .iter()
            .any(|atom| atom.doc.is_some() && atom.start < range.start() && range.end() < atom.end)
        {
            continue;
        }
        let mut before = atoms
            .iter()
            .position(|atom| atom.start >= range.end())
            .unwrap_or(atoms.len());
        let previous_end = if before == 0 {
            open_end
        } else {
            atoms[before - 1].end
        };
        let trailing = !comments.source[previous_end..range.start()].contains('\n');
        // A comment just before a separator moves after it.
        if before < atoms.len() && (atoms[before].is(",") || atoms[before].is(";")) {
            before += 1;
        }
        let text = comments.text(range);
        if before == atoms.len() {
            match item_comments.last_mut() {
                Some(last) if trailing => last.trailing.push(text),
                None if trailing => after_open.push(text),
                _ => dangling.push(text),
            }
        } else if let Some(index) = items.iter().position(|(item, _)| item.start == before) {
            match index.checked_sub(1) {
                Some(previous) if trailing => item_comments[previous].trailing.push(text),
                None if trailing => after_open.push(text),
                _ => item_comments[index].leading.push(text),
            }
        } else {
            stray[before].push(Placed { text, trailing });
        }
    }
    Placement {
        after_open,
        dangling,
        items: item_comments,
        stray,
    }
}

fn group_doc(
    group: &Group,
    offset: usize,
    context: Context,
    comments: Comments<'_>,
    shape: Shape,
) -> Doc {
    let broken = shape == Shape::Broken;
    let tokens = group.stream().into_iter().collect::<Vec<_>>();
    let atoms = atoms(&tokens, offset, context, comments);
    let spaces = spacing(&atoms);
    let (open, close, pad) = match group.delimiter() {
        Delimiter::Parenthesis => ("(", ")", ""),
        Delimiter::Bracket => ("[", "]", ""),
        Delimiter::Brace => ("{", "}", " "),
        Delimiter::None => ("", "", ""),
    };
    let open_end = offset + group.span_open().byte_range().end;
    let close_start = offset + group.span_close().byte_range().start;
    let items = split_items(&atoms);

    let Placement {
        after_open,
        dangling,
        items: item_comments,
        stray,
    } = place_comments(&atoms, &items, open_end, close_start, comments);

    if atoms.is_empty() && after_open.is_empty() && dangling.is_empty() {
        return if broken {
            Doc::Concat(vec![Doc::text(open), Doc::Hard, Doc::text(close)])
        } else {
            Doc::text(format!("{open}{close}"))
        };
    }

    // A parenthesized chain of alternatives hugs its parentheses, its
    // alternatives aligned with the line: `op @ (A` / `| B)`. A call's
    // single argument does not: it moves to its own line.
    let hugs = group.delimiter() == Delimiter::Parenthesis
        && shape == Shape::Free
        && items.len() == 1
        && items[0].1.is_none()
        && after_open.is_empty()
        && dangling.is_empty()
        && item_comments[0].leading.is_empty()
        && item_comments[0].trailing.is_empty()
        && operator_splits(&atoms, items[0].0.clone(), operators(context)).is_some();
    if hugs {
        return Doc::Concat(vec![
            Doc::text(open),
            item(&atoms, &spaces, items[0].0.clone(), &stray, context),
            Doc::text(close),
        ]);
    }

    let mut body = Vec::new();
    for text in after_open {
        body.push(Doc::Comment(format!(" {text}")));
        body.push(Doc::Hard);
    }
    for (index, ((range, separator), comments)) in items.iter().zip(item_comments).enumerate() {
        body.push(Doc::Line(if index == 0 { pad } else { " " }));
        for text in comments.leading {
            body.push(Doc::Comment(text));
            body.push(Doc::Hard);
        }
        body.push(item(&atoms, &spaces, range.clone(), &stray, context));
        if let Some(separator) = separator {
            body.push(Doc::text(&atoms[*separator].text));
        }
        for text in comments.trailing {
            body.push(Doc::Comment(format!(" {text}")));
            body.push(Doc::Hard);
        }
    }
    for text in dangling {
        body.push(Doc::Hard);
        body.push(Doc::Comment(text));
    }
    Doc::Group {
        doc: Box::new(Doc::Concat(vec![
            Doc::text(open),
            Doc::nest(INDENT, Doc::Concat(body)),
            Doc::Line(pad),
            Doc::text(close),
        ])),
        broken,
    }
}

/// The operators an item may break before, loosest first.
fn operators(context: Context) -> &'static [&'static str] {
    match context {
        Context::Pattern => &["|"],
        Context::Expression => &["||", "&&"],
        Context::Macro => &[],
    }
}

/// The loosest of `operators` at an item's top level and where it occurs.
fn operator_splits<'o>(
    atoms: &[Atom],
    range: std::ops::Range<usize>,
    operators: &'o [&'o str],
) -> Option<(usize, Vec<usize>)> {
    operators.iter().enumerate().find_map(|(rank, operator)| {
        // An operator first in the item is a prefix, as a leading `|` is.
        let splits = (range.start + 1..range.end)
            .filter(|&index| atoms[index].is(operator))
            .collect::<Vec<_>>();
        (!splits.is_empty()).then_some((rank, splits))
    })
}

fn item(
    atoms: &[Atom],
    spaces: &[bool],
    range: std::ops::Range<usize>,
    stray: &[Vec<Placed>],
    context: Context,
) -> Doc {
    operands(atoms, spaces, range, stray, context, operators(context))
}

/// An item broken before its loosest operator, each operand broken in turn
/// before the next tighter one.
fn operands(
    atoms: &[Atom],
    spaces: &[bool],
    range: std::ops::Range<usize>,
    stray: &[Vec<Placed>],
    context: Context,
    operators: &[&str],
) -> Doc {
    let Some((rank, splits)) = operator_splits(atoms, range.clone(), operators) else {
        return run(atoms, spaces, range, stray);
    };
    let tighter = &operators[rank + 1..];
    let mut rest = Vec::new();
    let mut start = range.start;
    let mut first = None;
    for &split in splits.iter().chain(std::iter::once(&range.end)) {
        let part = operands(atoms, spaces, start..split, stray, context, tighter);
        if first.is_none() {
            first = Some(part);
        } else {
            // A comment before the operator ends the previous operand's line
            // or takes a line of its own.
            rest.extend(comments_before(stray.get(start - 1)));
            rest.push(Doc::Line(" "));
            rest.push(Doc::text(&atoms[start - 1].text));
            if stray.get(start).is_none_or(Vec::is_empty) {
                rest.push(Doc::text(" "));
            }
            rest.push(part);
        }
        start = split + 1;
    }
    let indent = if context == Context::Pattern {
        0
    } else {
        INDENT
    };
    Doc::group(Doc::Concat(vec![
        first.expect("an item has a first operand"),
        Doc::nest(indent, Doc::Concat(rest)),
    ]))
}

/// The layout of the comments inside an item before one of its atoms: a
/// trailing one ends the line, a leading one takes a line of its own.
fn comments_before(placed: Option<&Vec<Placed>>) -> Vec<Doc> {
    let mut docs = Vec::new();
    for placed in placed.into_iter().flatten() {
        if placed.trailing {
            docs.push(Doc::Comment(format!(" {}", placed.text)));
        } else {
            docs.push(Doc::Hard);
            docs.push(Doc::Comment(placed.text.clone()));
        }
        docs.push(Doc::Hard);
    }
    docs
}

fn run(
    atoms: &[Atom],
    spaces: &[bool],
    range: std::ops::Range<usize>,
    stray: &[Vec<Placed>],
) -> Doc {
    let mut docs = Vec::new();
    let first = range.start;
    for index in range {
        let comments = comments_before(stray.get(index));
        let fresh = !comments.is_empty();
        docs.extend(comments);
        if index > first && spaces[index] && !fresh {
            docs.push(Doc::text(" "));
        }
        docs.push(atoms[index].doc());
    }
    Doc::Concat(docs)
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use proc_macro2::TokenStream;

    use super::*;

    fn component(source: &str) -> Component {
        Component {
            tokens: TokenStream::from_str(source)
                .expect("tokenize")
                .into_iter()
                .collect(),
            offset: 0,
        }
    }

    /// A record's `..base` hugs its base; `..` alone, a rest pattern, and a
    /// range keep their spacing.
    #[test]
    fn record_rest_hugs_its_base() {
        for (source, expected) in [
            ("Frame { pc: e, .. saved }", "Frame { pc: e, ..saved }"),
            ("Frame { .. t }", "Frame { ..t }"),
            ("[a, rest @ ..]", "[a, rest @ ..]"),
            ("Frame { pc, .. }", "Frame { pc, .. }"),
            ("a .. b", "a .. b"),
        ] {
            assert_eq!(render(&component(source).tokens), expected, "{source}");
        }
    }

    /// Brackets break like any group, so a slice pattern over a cons list
    /// (`[a, b, rest @ ..]`) wraps one element per line, its alternatives
    /// one per line in turn.
    #[test]
    fn bracket_patterns_wrap_generically() {
        let doc = sequence(
            &component("[first @ (Op::Push | Op::Pop | Op::Swap), second_element, rest @ ..]"),
            Context::Pattern,
            Comments::none(),
        );
        assert_eq!(
            print(&doc, 80),
            ["[first @ (Op::Push | Op::Pop | Op::Swap), second_element, rest @ ..]"]
        );
        expect_test::expect![[r"
            [
                first @ (Op::Push
                | Op::Pop
                | Op::Swap),
                second_element,
                rest @ ..
            ]"]]
        .assert_eq(&print(&doc, 24).join("\n"));
    }

    /// A call's single argument moves to its own line; a parenthesized
    /// chain hugs its parentheses.
    #[test]
    fn calls_break_their_argument_and_parentheses_hug_a_chain() {
        let call = sequence(
            &component("requires(first.gt(0) && second.lt(third) && fourth)"),
            Context::Expression,
            Comments::none(),
        );
        expect_test::expect![[r"
            requires(
                first.gt(0)
                    && second.lt(third)
                    && fourth
            )"]]
        .assert_eq(&print(&call, 30).join("\n"));
        let parenthesized = sequence(
            &component("(first.gt(0) && second.lt(third) && fourth)"),
            Context::Expression,
            Comments::none(),
        );
        expect_test::expect![[r"
            (first.gt(0)
                && second.lt(third)
                && fourth)"]]
        .assert_eq(&print(&parenthesized, 30).join("\n"));
    }
}
