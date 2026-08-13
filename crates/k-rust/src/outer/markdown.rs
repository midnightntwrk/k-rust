//! Literate K extraction from Markdown fenced code blocks.

use std::{collections::BTreeSet, fmt};

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

/// Extract fenced code selected by Java's Markdown selector language.
///
/// Non-code text is reduced to its whitespace, preserving source line and column positions.
pub fn extract_fenced_k_code(input: &str, selector: &str) -> Result<String, MarkdownError> {
    let selector = SelectorParser::new(selector).parse()?;
    let mut selected = Vec::<(usize, usize)>::new();
    let mut offset = 0;
    let mut open: Option<(char, usize, usize, bool)> = None;

    for line in input.split_inclusive('\n') {
        let line_end = offset + line.len();
        if let Some((marker, width, content_start, keep)) = open {
            if closing_fence(line, marker, width) {
                if keep {
                    selected.push((content_start, offset));
                }
                open = None;
            }
        } else if let Some((marker, width, info_offset, info)) = opening_fence(line) {
            let tags = parse_tags(info, offset + info_offset)?;
            open = Some((marker, width, line_end, selector.evaluate(&tags)));
        }
        offset = line_end;
    }
    if let Some((_, _, content_start, keep)) = open
        && keep
    {
        selected.push((content_start, input.len()));
    }

    let mut output = String::new();
    let mut ranges = selected.into_iter().peekable();
    for (index, character) in input.char_indices() {
        while ranges.peek().is_some_and(|(_, end)| index >= *end) {
            ranges.next();
        }
        let keep = ranges
            .peek()
            .is_some_and(|(start, end)| index >= *start && index < *end);
        if keep || character.is_whitespace() {
            output.push(character);
        }
    }
    Ok(output)
}

fn opening_fence(line: &str) -> Option<(char, usize, usize, &str)> {
    let without_newline = line.strip_suffix('\n').unwrap_or(line);
    let without_newline = without_newline
        .strip_suffix('\r')
        .unwrap_or(without_newline);
    let indent = without_newline
        .bytes()
        .take_while(|byte| *byte == b' ')
        .count();
    if indent > 3 {
        return None;
    }
    let rest = &without_newline[indent..];
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
    let without_newline = line.strip_suffix('\n').unwrap_or(line);
    let without_newline = without_newline
        .strip_suffix('\r')
        .unwrap_or(without_newline);
    let indent = without_newline
        .bytes()
        .take_while(|byte| *byte == b' ')
        .count();
    if indent > 3 {
        return false;
    }
    let rest = &without_newline[indent..];
    let width = rest
        .chars()
        .take_while(|candidate| *candidate == marker)
        .count();
    width >= opening_width && rest[marker.len_utf8() * width..].trim().is_empty()
}

fn parse_tags(info: &str, offset: usize) -> Result<BTreeSet<String>, MarkdownError> {
    let info = info.trim();
    if info.is_empty() {
        return Ok(BTreeSet::new());
    }
    let contents = if let Some(contents) = info.strip_prefix('{') {
        contents.strip_suffix('}').ok_or_else(|| MarkdownError {
            offset,
            message: "malformed Markdown code block annotation".into(),
        })?
    } else {
        if info.split_whitespace().count() != 1 {
            return Err(MarkdownError {
                offset,
                message: "malformed Markdown code block annotation".into(),
            });
        }
        info
    };
    Ok(contents
        .split_whitespace()
        .map(|tag| tag.strip_prefix('.').unwrap_or(tag).to_owned())
        .collect())
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
