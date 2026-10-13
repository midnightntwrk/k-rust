//! ```toml algorithm
//! id = "definition.outer.markdown"
//! name = "extraction of selected K blocks from Markdown"
//! sites = ["extract_fenced_k_code", "extract_fenced_k_code_with_map"]
//! variable = "B = Markdown bytes"
//! counters = []
//! no_counter = "Markdown extraction has no dedicated counter"
//!
//! [[cost]]
//! mode = "one Markdown source"
//! bound = "O(B)"
//! ```
//!
//! Markdown extraction is a fence-state machine that emits K code blocks in source order.
//! Complexity: O(B) over Markdown bytes.
//! It is linear in input lines; no dedicated counter.
//!
//! Literate K extraction from Markdown fenced code blocks.

use std::{collections::BTreeSet, fmt};

use super::parser::is_whitespace;
use crate::lines;
use crate::provenance::SourceOffsetMap;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MarkdownError {
    pub offset: usize,
    pub message: String,
}

impl fmt::Display for MarkdownError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{} at byte {}", self.message, self.offset)
    }
}

impl std::error::Error for MarkdownError {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MarkdownWarning {
    pub offset: usize,
    pub message: String,
}

/// Selected semantic K text and its byte mapping into the raw Markdown source.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExtractedKCode {
    pub text: String,
    pub offset_map: SourceOffsetMap,
    pub warnings: Vec<MarkdownWarning>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Selector {
    Tag(String),
    Not(Box<Self>),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
}

impl Selector {
    fn evaluate(&self, tags: &BTreeSet<String>) -> bool {
        match self {
            Self::Tag(tag) => tag == "*" || tags.contains(tag),
            Self::Not(inner) => !inner.evaluate(tags),
            Self::And(left, right) => left.evaluate(tags) && right.evaluate(tags),
            Self::Or(left, right) => left.evaluate(tags) || right.evaluate(tags),
        }
    }
}

/// Extract fenced code selected by K's Markdown selector language (`--md-selector`).
///
/// Text outside the selected code keeps its whitespace and has every other character replaced by
/// one space per byte, so the extracted text has the source's line ends and byte offsets, and the
/// selected code keeps its lines and columns.
pub fn extract_fenced_k_code(input: &str, selector: &str) -> Result<String, MarkdownError> {
    extract_fenced_k_code_with_map(input, selector).map(|extracted| extracted.text)
}

/// Extract selected fenced code and retain its raw-Markdown byte mapping.
pub fn extract_fenced_k_code_with_map(
    input: &str,
    selector: &str,
) -> Result<ExtractedKCode, MarkdownError> {
    let selector = SelectorParser::new(selector).parse()?;
    let mut selected = Vec::<(usize, usize)>::new();
    let mut warnings = Vec::new();
    let mut offset = 0;
    let mut open: Option<(char, usize, usize, bool)> = None;

    // Invariant: `offset` is the byte offset of `line` in `input`, `open` holds the fence opened by an earlier line and not yet closed, and `selected` holds the content range of every closed fence before `offset` whose tags satisfy `selector`; each iteration consumes one line of `input`.
    for line in lines::split_inclusive(input) {
        let line_end = offset + line.len();
        if let Some((marker, width, content_start, keep)) = open {
            if closing_fence(line, marker, width) {
                if keep {
                    selected.push((content_start, offset));
                }
                open = None;
            }
        } else if let Some((marker, width, info_offset, info)) = opening_fence(line) {
            let (tags, warning) = parse_tags(info, offset + info_offset)?;
            if let Some(warning) = warning {
                warnings.push(warning);
            }
            open = Some((marker, width, line_end, selector.evaluate(&tags)));
        }
        offset = line_end;
    }
    if let Some((_, _, content_start, keep)) = open
        && keep
    {
        selected.push((content_start, input.len()));
    }

    let mut output = String::with_capacity(input.len());
    let mut ranges = selected.into_iter().peekable();
    // Prose and unselected blocks are not part of the definition, so they contribute only layout,
    // and they keep their place: a character of the definition text's whitespace stays itself, and
    // every other prose character becomes one space per byte. No prose character reaches the outer
    // syntax as anything but layout, every character of the output is at its offset in `input`,
    // and the output has the line ends of `input`: a line end is decided by the characters on both
    // sides of it, and a space is not part of one, so a prose `\r` is not joined with a later `\n`
    // as it would be if the characters between them were dropped.
    // Invariant: `output` is `input[..index]` with every character outside a selected range that is not whitespace of the definition text replaced by as many spaces as it has bytes, and `ranges` has dropped every range ending at or before `index`; each iteration consumes one character and `ranges` only advances, so the pass is O(|input| + |selected|).
    for (index, character) in input.char_indices() {
        while ranges.peek().is_some_and(|(_, end)| index >= *end) {
            ranges.next();
        }
        let keep = ranges
            .peek()
            .is_some_and(|(start, end)| index >= *start && index < *end);
        if keep || is_whitespace(character) {
            output.push(character);
        } else {
            for _ in 0..character.len_utf8() {
                output.push(' ');
            }
        }
    }
    debug_assert_eq!(output.len(), input.len());
    let offset_map = SourceOffsetMap::identity(output.len());
    Ok(ExtractedKCode {
        text: output,
        offset_map,
        warnings,
    })
}

fn opening_fence(line: &str) -> Option<(char, usize, usize, &str)> {
    let without_line_end = lines::strip_terminator(line);
    let indent = without_line_end
        .bytes()
        .take_while(|byte| *byte == b' ')
        .count();
    if indent > 3 {
        return None;
    }
    let rest = &without_line_end[indent..];
    let marker = rest.chars().next()?;
    if !matches!(marker, '`' | '~') {
        return None;
    }
    let width = rest
        .chars()
        .take_while(|candidate| *candidate == marker)
        .count();
    if width < 3 {
        return None;
    }
    let marker_bytes = marker.len_utf8() * width;
    let info = &rest[marker_bytes..];
    if marker == '`' && info.contains('`') {
        return None;
    }
    Some((marker, width, indent + marker_bytes, info.trim()))
}

fn closing_fence(line: &str, marker: char, opening_width: usize) -> bool {
    let without_line_end = lines::strip_terminator(line);
    let indent = without_line_end
        .bytes()
        .take_while(|byte| *byte == b' ')
        .count();
    if indent > 3 {
        return false;
    }
    let rest = &without_line_end[indent..];
    let width = rest
        .chars()
        .take_while(|candidate| *candidate == marker)
        .count();
    width >= opening_width && rest[marker.len_utf8() * width..].trim().is_empty()
}

fn parse_tags(
    info: &str,
    offset: usize,
) -> Result<(BTreeSet<String>, Option<MarkdownWarning>), MarkdownError> {
    let info = info.trim();
    if info.is_empty() {
        return Ok((BTreeSet::new(), None));
    }
    for character in info.chars() {
        if !is_tag_character(character) {
            return Err(MarkdownError {
                offset,
                message: "malformed Markdown code block annotation".into(),
            });
        }
    }
    let contents = if let Some(contents) = info.strip_prefix('{') {
        let Some(contents) = contents.strip_suffix('}') else {
            return Ok((
                BTreeSet::new(),
                Some(MarkdownWarning {
                    offset,
                    message: "malformed Markdown code block annotation".into(),
                }),
            ));
        };
        contents
    } else {
        if info.split_whitespace().count() != 1 || info.contains('{') || info.contains('}') {
            return Ok((
                BTreeSet::new(),
                Some(MarkdownWarning {
                    offset,
                    message: "malformed Markdown code block annotation".into(),
                }),
            ));
        }
        info
    };
    Ok((
        contents
            .split_whitespace()
            .map(|tag| tag.strip_prefix('.').unwrap_or(tag).to_owned())
            .collect(),
        None,
    ))
}

fn is_tag_character(character: char) -> bool {
    character.is_ascii_alphanumeric()
        || matches!(
            character,
            '#' | '$' | '%' | '^' | '*' | '+' | '.' | '-' | '"' | '=' | '_' | '{' | '}'
        )
        || character.is_whitespace()
}

struct SelectorParser<'a> {
    input: &'a str,
    cursor: usize,
}

impl<'a> SelectorParser<'a> {
    fn new(input: &'a str) -> Self {
        Self { input, cursor: 0 }
    }

    fn parse(mut self) -> Result<Selector, MarkdownError> {
        let selector = self.or()?;
        self.whitespace()?;
        if self.cursor != self.input.len() {
            return Err(self.error("unexpected Markdown selector input"));
        }
        Ok(selector)
    }

    fn or(&mut self) -> Result<Selector, MarkdownError> {
        let left = self.and()?;
        if self.consume("|")? {
            Ok(Selector::Or(Box::new(left), Box::new(self.or()?)))
        } else {
            Ok(left)
        }
    }

    fn and(&mut self) -> Result<Selector, MarkdownError> {
        let left = self.not()?;
        if self.consume("&")? {
            Ok(Selector::And(Box::new(left), Box::new(self.and()?)))
        } else {
            Ok(left)
        }
    }

    fn not(&mut self) -> Result<Selector, MarkdownError> {
        if self.consume("!")? {
            Ok(Selector::Not(Box::new(self.atom()?)))
        } else {
            self.atom()
        }
    }

    fn atom(&mut self) -> Result<Selector, MarkdownError> {
        if self.consume("(")? {
            let selector = self.or()?;
            if !self.consume(")")? {
                return Err(self.error("expected ')' in Markdown selector"));
            }
            return Ok(selector);
        }
        self.tag().map(Selector::Tag)
    }

    fn tag(&mut self) -> Result<String, MarkdownError> {
        self.whitespace()?;
        let start = self.cursor;
        while let Some(character) = self.peek() {
            if character.is_whitespace() || matches!(character, '!' | '&' | '|' | '(' | ')') {
                break;
            }
            self.cursor += character.len_utf8();
        }
        if start == self.cursor {
            Err(self.error("expected tag in Markdown selector"))
        } else {
            let tag = &self.input[start..self.cursor];
            Ok(tag.strip_prefix('.').unwrap_or(tag).to_owned())
        }
    }

    fn consume(&mut self, expected: &str) -> Result<bool, MarkdownError> {
        self.whitespace()?;
        if self.input[self.cursor..].starts_with(expected) {
            self.cursor += expected.len();
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn whitespace(&mut self) -> Result<(), MarkdownError> {
        loop {
            while self.peek().is_some_and(char::is_whitespace) {
                self.cursor += self.peek().unwrap().len_utf8();
            }
            if !self.input[self.cursor..].starts_with("/*") {
                return Ok(());
            }
            let Some(end) = self.input[self.cursor + 2..].find("*/") else {
                return Err(self.error("unterminated Markdown selector comment"));
            };
            self.cursor += 2 + end + 2;
        }
    }

    fn peek(&self) -> Option<char> {
        self.input[self.cursor..].chars().next()
    }

    fn error(&self, message: impl Into<String>) -> MarkdownError {
        MarkdownError {
            offset: self.cursor,
            message: message.into(),
        }
    }
}
