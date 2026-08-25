//! Lossless source-trivia recovery layered over the semantic token parsers.
//!
//! `proc_macro2` remains the sole authority for token boundaries. This module
//! classifies only the byte gaps between its token spans, so strings and other
//! token contents can never be mistaken for comments.

use std::cmp::{max, min};

use proc_macro2::{Span, TokenStream, TokenTree};

use crate::{SyntaxError, SyntaxErrorKind};

/// Half-open byte range in the exact string passed to a `_source` parser.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SourceRange {
    start: usize,
    end: usize,
}

impl SourceRange {
    /// Creates a half-open byte range. Validation happens when source is read.
    #[must_use]
    pub const fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    /// Inclusive start byte offset.
    #[must_use]
    pub const fn start(self) -> usize {
        self.start
    }

    /// Exclusive end byte offset.
    #[must_use]
    pub const fn end(self) -> usize {
        self.end
    }

    /// Length in bytes.
    #[must_use]
    pub const fn len(self) -> usize {
        self.end.saturating_sub(self.start)
    }

    /// Whether the range contains no bytes.
    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.start == self.end
    }

    /// Extracts this range from its source string.
    #[must_use]
    pub fn text(self, source: &str) -> Option<&str> {
        source.get(self.start..self.end)
    }
}

/// Classified whitespace from one token gap.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WhitespaceTrivia {
    newline_count: usize,
}

impl WhitespaceTrivia {
    /// Number of line-feed bytes in this whitespace run.
    #[must_use]
    pub const fn newline_count(self) -> usize {
        self.newline_count
    }
}

/// One non-structural `//` comment, excluding its line terminator.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LineCommentTrivia;

/// Documentation flavor of a block comment when one reaches gap lexing.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DocCommentStyle {
    /// `/** ... */` outer documentation.
    Outer,
    /// `/*! ... */` inner documentation.
    Inner,
}

/// One possibly nested `/* ... */` comment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BlockCommentTrivia {
    maximum_nesting: usize,
    documentation: Option<DocCommentStyle>,
}

impl BlockCommentTrivia {
    /// Greatest nesting depth reached by this comment.
    #[must_use]
    pub const fn maximum_nesting(self) -> usize {
        self.maximum_nesting
    }

    /// Documentation flavor, or `None` for a non-doc block comment.
    #[must_use]
    pub const fn documentation(self) -> Option<DocCommentStyle> {
        self.documentation
    }
}

/// Typed source trivia.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TriviaKind {
    /// Whitespace outside token ranges.
    Whitespace(WhitespaceTrivia),
    /// A non-structural line comment.
    LineComment(LineCommentTrivia),
    /// A block comment. DSL source entry points reject non-doc instances.
    BlockComment(BlockCommentTrivia),
}

/// Token ownership assigned from original source geometry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TriviaAttachment {
    /// Trivia leads the token at this byte range.
    Leading(SourceRange),
    /// Trivia trails the token at this byte range.
    Trailing(SourceRange),
    /// Trivia in a token-free source string.
    Detached,
}

/// One classified, byte-exact trivia run.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Trivia {
    range: SourceRange,
    kind: TriviaKind,
    attachment: TriviaAttachment,
}

impl Trivia {
    /// Byte range of the authored trivia.
    #[must_use]
    pub const fn range(self) -> SourceRange {
        self.range
    }

    /// Whitespace/comment classification.
    #[must_use]
    pub const fn kind(self) -> TriviaKind {
        self.kind
    }

    /// Leading/trailing token ownership.
    #[must_use]
    pub const fn attachment(self) -> TriviaAttachment {
        self.attachment
    }
}

/// Token ranges and their complete, ordered trivia complement.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TriviaTable {
    source_len: usize,
    token_ranges: Vec<SourceRange>,
    trivia: Vec<Trivia>,
}

impl TriviaTable {
    /// Length of the parsed source in bytes.
    #[must_use]
    pub const fn source_len(&self) -> usize {
        self.source_len
    }

    /// Sorted, non-overlapping authored token ranges.
    ///
    /// Synthesized proc-macro tokens sharing a span (notably doc comments) are
    /// represented by one union range.
    #[must_use]
    pub fn token_ranges(&self) -> &[SourceRange] {
        &self.token_ranges
    }

    /// Complete trivia sequence, ordered by byte offset.
    #[must_use]
    pub fn trivia(&self) -> &[Trivia] {
        &self.trivia
    }

    /// Trivia beginning at one byte offset.
    #[must_use]
    pub fn at(&self, byte_offset: usize) -> Option<&Trivia> {
        self.trivia
            .binary_search_by_key(&byte_offset, |item| item.range.start)
            .ok()
            .map(|index| &self.trivia[index])
    }

    pub(crate) fn reject_non_doc_block_comments(
        &self,
        macro_name: &'static str,
    ) -> Result<(), SyntaxError> {
        let rejected = self.trivia.iter().find(|trivia| {
            matches!(
                trivia.kind,
                TriviaKind::BlockComment(BlockCommentTrivia {
                    documentation: None,
                    ..
                })
            )
        });
        match rejected {
            Some(trivia) => Err(SyntaxError::new(
                SyntaxErrorKind::UnsupportedDslBlockComment { macro_name },
                Span::call_site(),
            )
            .with_source_range(trivia.range)),
            None => Ok(()),
        }
    }
}

/// Classifies the complete complement of proc-macro token byte ranges.
///
/// Overlapping or shared token spans are unioned before gaps are scanned. The
/// result is validated together with the normalized token ranges to cover every
/// source byte exactly once.
///
/// # Errors
///
/// Returns [`SyntaxErrorKind::InvalidTrivia`] for an out-of-bounds token range,
/// non-trivia bytes in a gap, an unterminated block comment, or failed totality.
pub fn lex_gaps(source: &str, token_ranges: &[SourceRange]) -> Result<Vec<Trivia>, SyntaxError> {
    let token_ranges = normalize_token_ranges(source, token_ranges)?;
    let mut trivia = Vec::new();
    let mut cursor = 0;
    let mut left = None;

    for right in token_ranges.iter().copied() {
        if cursor < right.start {
            lex_gap(
                source,
                SourceRange::new(cursor, right.start),
                left,
                Some(right),
                &mut trivia,
            )?;
        }
        cursor = right.end;
        left = Some(right);
    }
    if cursor < source.len() {
        lex_gap(
            source,
            SourceRange::new(cursor, source.len()),
            left,
            None,
            &mut trivia,
        )?;
    }
    validate_totality(source.len(), &token_ranges, &trivia)?;
    Ok(trivia)
}

pub(crate) fn tokenize_with_trivia(
    source: &str,
) -> Result<(TokenStream, TriviaTable), SyntaxError> {
    let tokens = source.parse::<TokenStream>().map_err(|error| {
        SyntaxError::new(
            SyntaxErrorKind::RustSyntax(error.to_string()),
            Span::call_site(),
        )
    })?;
    let raw_ranges = collect_token_ranges(&tokens);
    let token_ranges = normalize_token_ranges(source, &raw_ranges)?;
    let trivia = lex_gaps(source, &token_ranges)?;
    Ok((
        tokens,
        TriviaTable {
            source_len: source.len(),
            token_ranges,
            trivia,
        },
    ))
}

fn collect_token_ranges(tokens: &TokenStream) -> Vec<SourceRange> {
    fn visit(tokens: TokenStream, output: &mut Vec<SourceRange>) {
        for token in tokens {
            match token {
                TokenTree::Group(group) => {
                    push_span(group.span_open(), output);
                    visit(group.stream(), output);
                    push_span(group.span_close(), output);
                }
                other => push_span(other.span(), output),
            }
        }
    }

    fn push_span(span: Span, output: &mut Vec<SourceRange>) {
        let range = span.byte_range();
        if range.start != range.end {
            output.push(SourceRange::new(range.start, range.end));
        }
    }

    let mut output = Vec::new();
    visit(tokens.clone(), &mut output);
    output
}

fn normalize_token_ranges(
    source: &str,
    token_ranges: &[SourceRange],
) -> Result<Vec<SourceRange>, SyntaxError> {
    let mut ranges = token_ranges.to_vec();
    ranges.sort_unstable();
    let mut normalized: Vec<SourceRange> = Vec::with_capacity(ranges.len());

    for range in ranges {
        if range.start > range.end
            || range.end > source.len()
            || !source.is_char_boundary(range.start)
            || !source.is_char_boundary(range.end)
        {
            let diagnostic_start = min(min(range.start, range.end), source.len());
            let diagnostic_end = min(max(range.start, range.end), source.len());
            return Err(trivia_error(
                "token byte range is outside the source or splits a UTF-8 code point",
                SourceRange::new(diagnostic_start, diagnostic_end),
            ));
        }
        if range.is_empty() {
            continue;
        }
        match normalized.last_mut() {
            Some(previous) if range.start < previous.end => {
                previous.end = max(previous.end, range.end);
            }
            _ => normalized.push(range),
        }
    }
    Ok(normalized)
}

fn lex_gap(
    source: &str,
    gap: SourceRange,
    left: Option<SourceRange>,
    right: Option<SourceRange>,
    output: &mut Vec<Trivia>,
) -> Result<(), SyntaxError> {
    let first_newline = source[gap.start..gap.end]
        .find('\n')
        .map(|relative| gap.start + relative);
    let bytes = source.as_bytes();
    let mut cursor = gap.start;

    while cursor < gap.end {
        let start = cursor;
        let (kind, end) = if bytes[cursor..gap.end].starts_with(b"//") {
            let end = bytes[cursor..gap.end]
                .iter()
                .position(|byte| *byte == b'\n')
                .map_or(gap.end, |relative| cursor + relative);
            (TriviaKind::LineComment(LineCommentTrivia), end)
        } else if bytes[cursor..gap.end].starts_with(b"/*") {
            let (end, maximum_nesting) = block_comment_end(bytes, cursor, gap.end)?;
            let documentation =
                if bytes[cursor..gap.end].starts_with(b"/**") && end - cursor != "/**/".len() {
                    Some(DocCommentStyle::Outer)
                } else if bytes[cursor..gap.end].starts_with(b"/*!") {
                    Some(DocCommentStyle::Inner)
                } else {
                    None
                };
            (
                TriviaKind::BlockComment(BlockCommentTrivia {
                    maximum_nesting,
                    documentation,
                }),
                end,
            )
        } else {
            let Some(character) = source[cursor..gap.end].chars().next() else {
                break;
            };
            if !character.is_whitespace() {
                return Err(trivia_error(
                    "a token gap contains bytes which are neither whitespace nor a comment",
                    SourceRange::new(cursor, cursor + character.len_utf8()),
                ));
            }
            let split_limit = first_newline
                .filter(|split| cursor < *split)
                .unwrap_or(gap.end);
            cursor += character.len_utf8();
            while cursor < gap.end && cursor < split_limit {
                let character = source[cursor..gap.end]
                    .chars()
                    .next()
                    .expect("cursor is inside the source gap");
                if !character.is_whitespace() {
                    break;
                }
                cursor += character.len_utf8();
            }
            let range = SourceRange::new(start, cursor);
            let newline_count = source[range.start..range.end]
                .bytes()
                .filter(|byte| *byte == b'\n')
                .count();
            (
                TriviaKind::Whitespace(WhitespaceTrivia { newline_count }),
                cursor,
            )
        };
        cursor = end;
        let range = SourceRange::new(start, end);
        let attachment = attachment(range, first_newline, left, right);
        output.push(Trivia {
            range,
            kind,
            attachment,
        });
    }
    Ok(())
}

fn attachment(
    trivia: SourceRange,
    first_newline: Option<usize>,
    left: Option<SourceRange>,
    right: Option<SourceRange>,
) -> TriviaAttachment {
    match (left, right) {
        (None, Some(right)) => TriviaAttachment::Leading(right),
        (Some(left), None) => TriviaAttachment::Trailing(left),
        (Some(left), Some(right)) => match first_newline {
            Some(split) if trivia.start >= split => TriviaAttachment::Leading(right),
            Some(_) | None => TriviaAttachment::Trailing(left),
        },
        (None, None) => TriviaAttachment::Detached,
    }
}

fn block_comment_end(
    bytes: &[u8],
    start: usize,
    gap_end: usize,
) -> Result<(usize, usize), SyntaxError> {
    let mut cursor = start + 2;
    let mut depth = 1_usize;
    let mut maximum_nesting = depth;
    while cursor + 1 < gap_end {
        if bytes[cursor..gap_end].starts_with(b"/*") {
            depth += 1;
            maximum_nesting = max(maximum_nesting, depth);
            cursor += 2;
        } else if bytes[cursor..gap_end].starts_with(b"*/") {
            depth -= 1;
            cursor += 2;
            if depth == 0 {
                return Ok((cursor, maximum_nesting));
            }
        } else {
            cursor += 1;
        }
    }
    Err(trivia_error(
        "unterminated block comment",
        SourceRange::new(start, gap_end),
    ))
}

fn validate_totality(
    source_len: usize,
    token_ranges: &[SourceRange],
    trivia: &[Trivia],
) -> Result<(), SyntaxError> {
    let mut ranges = token_ranges.to_vec();
    ranges.extend(trivia.iter().map(|item| item.range));
    ranges.sort_unstable();
    let mut cursor = 0;
    for range in ranges {
        if range.start != cursor {
            return Err(trivia_error(
                "tokens and trivia do not cover every source byte exactly once",
                SourceRange::new(min(cursor, source_len), min(range.start, source_len)),
            ));
        }
        cursor = range.end;
    }
    if cursor != source_len {
        return Err(trivia_error(
            "tokens and trivia do not cover every source byte exactly once",
            SourceRange::new(min(cursor, source_len), source_len),
        ));
    }
    Ok(())
}

fn trivia_error(reason: &'static str, range: SourceRange) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::InvalidTrivia { reason }, Span::call_site())
        .with_source_range(range)
}
