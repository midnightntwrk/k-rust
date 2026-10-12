//! ```toml algorithm
//! id = "definition.regex.parse"
//! name = "parsing of structured K regular expressions"
//! sites = ["parse", "Parser::parse"]
//! variable = "B = regular-expression syntax bytes"
//! counters = []
//! no_counter = "structured-regex parsing has no dedicated counter"
//!
//! [[cost]]
//! mode = "one regular expression"
//! bound = "O(B)"
//! ```
//!
//! This definition-layer algorithm scans or transforms its model in deterministic declaration order.
//! Complexity: O(B) over regex syntax bytes.
//! Cost is linear in visited syntax unless its local documentation states another bound; no dedicated counter.
//!
//! K's structured regular-expression syntax.
//!
//! This crate is the whole definition-independent part of K token regexes: the AST, [`parse`],
//! the K, Flex, and Rust printers, and [`check`]. Whether a regex is well formed depends only on
//! its own text, so none of this needs a K definition, KORE, or a backend, and the crate has no
//! dependencies. Two rules do need the surrounding definition and stay with the definition checks:
//! resolving `{Name}` references (see [`RegexBody::named_references`]) against lexical
//! declarations, which rejects undeclared and circular names, and forbidding line anchors in named
//! lexical declarations.
//!
//! A regex that passes [`parse`] and yields no [`check`] issue is rejected by the definition
//! checks only for those two definition-dependent reasons.

use std::fmt::{Display, Write};

/// A K token regex: a body and two line anchors, which constrain where in the scanned text a token
/// may be, not what it contains.
///
/// The anchors apply to the whole body, alternation included (`^a|b$` is `^(a|b)$`); the parser
/// accepts `^` only as the first and `$` only as the last character of the whole regex.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Regex {
    /// `^`: the token starts a line, i.e. it starts at the start of the scanned text or right
    /// after a line terminator. The line terminators are the ones source locations count:
    /// `\r\n`, `\n`, `\r`, vertical tab, form feed, U+0085, U+2028 and U+2029, with `\r\n` one
    /// terminator, so no line starts or ends between its `\r` and its `\n` (k-rust's `lines`
    /// module holds the table).
    pub start_line: bool,
    pub body: RegexBody,
    /// `$`: the token ends a line, i.e. a line terminator follows it. The terminator is not part
    /// of the token, so it does not count in the longest-match comparison between candidate tokens
    /// either; and the end of the text is not a line end: text after the last terminator is an
    /// unterminated line.
    pub end_line: bool,
}

impl Regex {
    pub fn new(body: RegexBody) -> Self {
        Self {
            start_line: false,
            body,
            end_line: false,
        }
    }

    /// The canonical form, which `Display` prints: the parsed regex in K syntax, with exactly the
    /// anchors it holds. Two regexes with the same canonical form denote the same tokens; reparsing
    /// it gives back an equal [`Regex`].
    pub fn to_canonical_string(&self) -> String {
        let mut output = String::new();
        if self.start_line {
            output.push('^');
        }
        print_union(&self.body, &mut output).expect("writing to a string cannot fail");
        if self.end_line {
            output.push('$');
        }
        output
    }

    /// Render this regular expression as a deterministic Flex pattern.
    ///
    /// The line anchors are printed as held, as Flex's leading `^` and trailing `$`, which apply
    /// to the whole rule. Flex reads only `\n` as a line end, though, and its `$` is trailing
    /// context, whose newline Flex counts when it compares candidate matches, so a scanner that
    /// must give the anchors their meaning (see [`Regex::start_line`]) prints an anchored rule
    /// from its body and checks the anchors itself.
    /// The body is printed as [`RegexBody::to_flex_string`] prints it, for UTF-8 input.
    /// This is a semantic input to Flex, not a byte-parity contract with K's renderer.
    pub fn to_flex_string(&self) -> String {
        print_flex_regex(self, FlexClasses::Utf8)
    }

    /// This regular expression in Flex syntax with each character class and `.` as written: a
    /// name for its tokens in a generated parser's diagnostics, which a reader recognizes from the
    /// definition. It is no scanner pattern: Flex would read its classes as sets of bytes (see
    /// [`Regex::to_flex_string`]).
    pub fn to_flex_name(&self) -> String {
        print_flex_regex(self, FlexClasses::AsWritten)
    }

    /// Translate K's regex AST to a Rust regex body, keeping the line anchors beside it: Rust
    /// regex anchors match at different positions, so the matcher applies them itself.
    pub fn to_flex_pattern(&self) -> Result<FlexPattern, UnexpandedLexical> {
        Ok(FlexPattern {
            body: self.body.to_rust_string()?,
            start_line: self.start_line,
            end_line: self.end_line,
        })
    }
}

impl Display for Regex {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.to_canonical_string())
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RegexBody {
    Char(char),
    AnyChar,
    Named(String),
    CharClass {
        negated: bool,
        members: Vec<CharClass>,
    },
    Union {
        left: Box<Self>,
        right: Box<Self>,
    },
    Concat(Vec<Self>),
    ZeroOrMore(Box<Self>),
    ZeroOrOne(Box<Self>),
    OneOrMore(Box<Self>),
    Exactly {
        body: Box<Self>,
        count: u32,
    },
    AtLeast {
        body: Box<Self>,
        count: u32,
    },
    Range {
        body: Box<Self>,
        at_least: u32,
        at_most: u32,
    },
}

impl RegexBody {
    // Invariant: `visitor` has been applied to `self` before any of its subexpressions, and each recursive call descends into a strict subexpression of `self`, so the size of `self` bounds the calls.
    pub fn visit_preorder<'a>(&'a self, visitor: &mut impl FnMut(&'a Self)) {
        visitor(self);
        match self {
            Self::Union { left, right } => {
                left.visit_preorder(visitor);
                right.visit_preorder(visitor);
            }
            Self::Concat(members) => {
                for member in members {
                    member.visit_preorder(visitor);
                }
            }
            Self::ZeroOrMore(body)
            | Self::ZeroOrOne(body)
            | Self::OneOrMore(body)
            | Self::Exactly { body, .. }
            | Self::AtLeast { body, .. }
            | Self::Range { body, .. } => body.visit_preorder(visitor),
            Self::Char(_) | Self::AnyChar | Self::Named(_) | Self::CharClass { .. } => {}
        }
    }

    /// The `{Name}` lexical identifiers this body references, without duplicates, in preorder
    /// first-occurrence order.
    ///
    /// A reference means nothing without a lexical declaration of that name, so a caller that has
    /// no declarations in scope must reject any body for which this is nonempty.
    pub fn named_references(&self) -> Vec<&str> {
        let mut names = Vec::<&str>::new();
        self.visit_preorder(&mut |body| {
            if let Self::Named(name) = body
                && !names.contains(&name.as_str())
            {
                names.push(name);
            }
        });
        names
    }

    pub fn to_k_string(&self) -> String {
        let mut output = String::new();
        print_union(self, &mut output).expect("writing to a string cannot fail");
        output
    }

    /// Print this parsed K regex for Rust's regex engine.
    ///
    /// Every parsed character remains literal; in particular, K escapes such as
    /// `\d` and `\b` must not become Rust character classes or assertions.
    pub fn to_rust_string(&self) -> Result<String, UnexpandedLexical> {
        let mut output = String::new();
        print_rust_regex(self, &mut output)?;
        Ok(output)
    }

    /// Render this regular-expression body for Flex.
    ///
    /// The pattern matches the UTF-8 encodings of the texts the body denotes, the input a
    /// generated scanner reads: a character class and `.` each match one whole character (the
    /// byte sequences that encode exactly the characters they denote), and a character outside a
    /// class is its encoding, grouped so that a repetition applies to all of it. A named reference
    /// stays a Flex `{Name}` reference, with its name mangled by [`mangle_flex_identifier`].
    pub fn to_flex_string(&self) -> String {
        let mut output = String::new();
        print_flex_union(self, FlexClasses::Utf8, &mut output)
            .expect("writing to a string cannot fail");
        output
    }
}

impl Display for RegexBody {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.to_k_string())
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CharClass {
    Char(char),
    Range { start: char, end: char },
}

impl CharClass {
    pub fn to_k_string(&self) -> String {
        let mut output = String::new();
        print_class_member(self, &mut output).expect("writing to a string cannot fail");
        output
    }

    /// Render this character-class member for Flex.
    pub fn to_flex_string(&self) -> String {
        let mut output = String::new();
        print_flex_class_member(self, &mut output).expect("writing to a string cannot fail");
        output
    }
}

impl Display for CharClass {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.to_k_string())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FlexPattern {
    pub body: String,
    pub start_line: bool,
    pub end_line: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnexpandedLexical {
    pub name: String,
}

impl Display for UnexpandedLexical {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "lexical identifier {:?} was not expanded",
            self.name
        )
    }
}

impl std::error::Error for UnexpandedLexical {}

/// Convert a K lexical identifier to the identifier syntax accepted by Flex.
pub fn mangle_flex_identifier(name: &str) -> String {
    if let Some(name) = name.strip_prefix('#') {
        format!("_Hash_{name}")
    } else {
        name.to_owned()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseError {
    /// Position of the error in `input`, counted in `char`s, not bytes. It equals
    /// `input.chars().count()` when the error is at the end of the input.
    pub index: usize,
    pub message: String,
    pub input: String,
}

impl ParseError {
    /// Byte offset in `input` of the character at [`ParseError::index`], or `input.len()` when the
    /// error is at the end of the input; always a `char` boundary of `input`.
    pub fn byte_index(&self) -> usize {
        self.input
            .char_indices()
            .nth(self.index)
            .map_or(self.input.len(), |(offset, _)| offset)
    }
}

impl Display for ParseError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "Syntax error at index {} in regular expression: {:?}. {}",
            self.index, self.input, self.message
        )
    }
}

impl std::error::Error for ParseError {}

/// Parse K's structured token-regex syntax.
pub fn parse(input: &str) -> Result<Regex, ParseError> {
    Parser::new(input).parse()
}

/// A reason a parsed regex is still not an acceptable K token regex.
///
/// The variants fall in two groups:
///
/// - Well-formedness of the regex language: [`Issue::DescendingCharRange`] and
///   [`Issue::DescendingRepeat`] denote empty sets written in a form that is almost certainly a
///   mistake, so they are rejected rather than silently matching nothing.
/// - A restriction kept from a byte-level scanner target: [`Issue::NonAsciiInClassRange`] is well
///   formed as a regex. It was rejected because a Flex class of bytes cannot take a non-ASCII
///   character as a range endpoint; the Flex printer now writes every class as the UTF-8
///   encodings of its characters (see [`RegexBody::to_flex_string`]), so it would scan it, and
///   the restriction stays only until the definitions it rejects are decided separately. A
///   negated class may hold any character: both printers write it as the characters outside it.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum Issue {
    /// A class range `start-end` with `start > end`.
    DescendingCharRange { start: char, end: char },
    /// A repetition `body{at_least,at_most}` with `at_least > at_most`.
    DescendingRepeat {
        body: RegexBody,
        at_least: u32,
        at_most: u32,
    },
    /// Non-ASCII range endpoints in any class, without duplicates, in first-occurrence order.
    NonAsciiInClassRange(Vec<char>),
}

impl Display for Issue {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DescendingCharRange { start, end } => write!(
                formatter,
                "Invalid character range '{}'. Start of range U+{:04X} is greater than end of range U+{:04X}.",
                CharClass::Range {
                    start: *start,
                    end: *end
                },
                *start as u32,
                *end as u32
            ),
            Self::DescendingRepeat {
                body,
                at_least,
                at_most,
            } => write!(
                formatter,
                "Invalid numeric range '{}'. Start of range {at_least} is greater than end of range {at_most}.",
                RegexBody::Range {
                    body: Box::new(body.clone()),
                    at_least: *at_least,
                    at_most: *at_most,
                }
            ),
            Self::NonAsciiInClassRange(characters) => write!(
                formatter,
                "Unsupported non-ASCII characters found in character class range: [{}]",
                join_characters(characters)
            ),
        }
    }
}

impl std::error::Error for Issue {}

fn join_characters(characters: &[char]) -> String {
    characters
        .iter()
        .map(char::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

/// Report every [`Issue`] of a parsed regex that does not depend on a surrounding definition.
///
/// Descending ranges and repetitions come first, one per occurrence in preorder; then at most one
/// [`Issue::NonAsciiInClassRange`].
/// Named references are not examined; see [`RegexBody::named_references`].
pub fn check(regex: &Regex) -> Vec<Issue> {
    let mut issues = Vec::new();
    let mut range_non_ascii = Vec::new();
    regex.body.visit_preorder(&mut |body| match body {
        RegexBody::CharClass { members, .. } => {
            for member in members {
                match *member {
                    CharClass::Char(_) => {}
                    CharClass::Range { start, end } => {
                        for character in [start, end] {
                            if !character.is_ascii() {
                                push_unique(&mut range_non_ascii, character);
                            }
                        }
                        if start > end {
                            issues.push(Issue::DescendingCharRange { start, end });
                        }
                    }
                }
            }
        }
        RegexBody::Range {
            body,
            at_least,
            at_most,
        } if at_least > at_most => issues.push(Issue::DescendingRepeat {
            body: (**body).clone(),
            at_least: *at_least,
            at_most: *at_most,
        }),
        _ => {}
    });
    if !range_non_ascii.is_empty() {
        issues.push(Issue::NonAsciiInClassRange(range_non_ascii));
    }
    issues
}

fn push_unique(values: &mut Vec<char>, value: char) {
    if !values.contains(&value) {
        values.push(value);
    }
}

struct Parser {
    input: String,
    characters: Vec<char>,
    cursor: usize,
}

impl Parser {
    fn new(input: &str) -> Self {
        Self {
            input: input.to_owned(),
            characters: input.chars().collect(),
            cursor: 0,
        }
    }

    fn parse(mut self) -> Result<Regex, ParseError> {
        match self.input.as_str() {
            "" => return Err(self.error_at(0, "Cannot be empty.")),
            "^" | "$" => {
                return Err(self.error_at(
                    0,
                    format!(
                        "Cannot consist of only line anchors. Did you mean '\\{}'?",
                        self.input
                    ),
                ));
            }
            "^$" => {
                return Err(self.error_at(
                    0,
                    "Cannot consist of only line anchors. Did you mean '\\^' or '\\$'?",
                ));
            }
            _ => {}
        }
        let start_line = self.consume('^');
        let body = self.parse_union()?;
        let end_line = self.consume('$');
        if self.has_remaining() {
            // The top-level union stops only before a `)` or a `$`. After a consumed `$`, that `$`
            // is the offending token because it is not at the end; otherwise the leftover is an
            // unmatched `)`.
            if end_line {
                self.cursor -= 1;
                return Err(self.unescaped('$'));
            }
            return Err(self.unescaped(self.characters[self.cursor]));
        }
        Ok(Regex {
            start_line,
            body,
            end_line,
        })
    }

    // Invariant: each recursive call to `parse_union`, directly after a consumed `|` or through `parse_simple` after a consumed `(`, starts at a larger `self.cursor`, so the length of the pattern bounds the calls.
    fn parse_union(&mut self) -> Result<RegexBody, ParseError> {
        let left = self.parse_concat()?;
        if self.consume('|') {
            if !self.has_remaining() {
                self.cursor -= 1;
                return Err(self.unescaped('|'));
            }
            return Ok(RegexBody::Union {
                left: Box::new(left),
                right: Box::new(self.parse_union()?),
            });
        }
        Ok(left)
    }

    fn parse_concat(&mut self) -> Result<RegexBody, ParseError> {
        let mut members = vec![self.parse_repeat()?];
        while self
            .peek()
            .is_some_and(|next| !matches!(next, ')' | '|' | '$'))
        {
            members.push(self.parse_repeat()?);
        }
        if members.len() == 1 {
            Ok(members.pop().expect("length was one"))
        } else {
            Ok(RegexBody::Concat(members))
        }
    }

    fn parse_repeat(&mut self) -> Result<RegexBody, ParseError> {
        let mut body = self.parse_char_class()?;
        // Invariant: `body` is the operand wrapped in every postfix operator consumed so far; each iteration consumes at least one character or breaks, so the remaining input bounds the iterations.
        loop {
            body = match self.peek() {
                Some('?') => {
                    self.cursor += 1;
                    RegexBody::ZeroOrOne(Box::new(body))
                }
                Some('*') => {
                    self.cursor += 1;
                    RegexBody::ZeroOrMore(Box::new(body))
                }
                Some('+') => {
                    self.cursor += 1;
                    RegexBody::OneOrMore(Box::new(body))
                }
                Some('{') if self.peek_at(1).is_some_and(is_decimal_digit) => {
                    self.cursor += 1;
                    self.parse_repetition(body)?
                }
                _ => break,
            };
        }
        Ok(body)
    }

    fn parse_repetition(&mut self, body: RegexBody) -> Result<RegexBody, ParseError> {
        let lower = self.parse_integer()?;
        if self.consume('}') {
            return Ok(RegexBody::Exactly {
                body: Box::new(body),
                count: lower,
            });
        }
        self.expect(',')?;
        if self.consume('}') {
            return Ok(RegexBody::AtLeast {
                body: Box::new(body),
                count: lower,
            });
        }
        let upper = self.parse_integer()?;
        self.expect('}')?;
        Ok(RegexBody::Range {
            body: Box::new(body),
            at_least: lower,
            at_most: upper,
        })
    }

    fn parse_integer(&mut self) -> Result<u32, ParseError> {
        let start = self.cursor;
        while self.peek().is_some_and(is_decimal_digit) {
            self.cursor += 1;
        }
        if self.cursor == start {
            return Err(self.error("Expected a digit 0-9."));
        }
        let number = self.characters[start..self.cursor]
            .iter()
            .collect::<String>();
        let value = number
            .parse::<u64>()
            .map_err(|_| self.error_at(start, "Repetition count is too large."))?;
        if value > i32::MAX as u64 {
            return Err(self.error_at(start, "Repetition count is too large."));
        }
        Ok(value as u32)
    }

    fn parse_char_class(&mut self) -> Result<RegexBody, ParseError> {
        if !self.consume('[') {
            return self.parse_simple();
        }
        let negated = self.consume('^');
        let mut members = Vec::new();
        while !self.consume(']') {
            if !self.has_remaining() {
                return Err(self.error("Unexpected end of string. Expected ']'"));
            }
            members.push(self.parse_class_member()?);
        }
        if members.is_empty() {
            return Err(self.error("Character class cannot be empty."));
        }
        Ok(RegexBody::CharClass { negated, members })
    }

    fn parse_class_member(&mut self) -> Result<CharClass, ParseError> {
        let start = self.parse_character(true)?;
        if self.consume('-') {
            if self.peek() == Some(']') {
                self.cursor -= 1;
                return Err(self.unescaped('-'));
            }
            let end = self.parse_character(true)?;
            Ok(CharClass::Range { start, end })
        } else {
            Ok(CharClass::Char(start))
        }
    }

    fn parse_simple(&mut self) -> Result<RegexBody, ParseError> {
        if self.consume('.') {
            return Ok(RegexBody::AnyChar);
        }
        if self.consume('(') {
            let body = self.parse_union()?;
            self.expect(')')?;
            return Ok(body);
        }
        if self.consume('{') {
            let start = self.cursor;
            while self.peek().is_some_and(|next| next != '}') {
                self.cursor += 1;
            }
            if !self.consume('}') {
                return Err(self.error("Unexpected end of string. Expected '}'"));
            }
            let name = self.characters[start..self.cursor - 1]
                .iter()
                .collect::<String>();
            if !valid_identifier(&name) {
                return Err(self.error_at(
                    self.cursor - 1,
                    format!(
                        "Lexical identifier {{{name}}} is invalid. Identifiers should match the regular expression \"#?[A-Z][a-zA-Z0-9]*\"."
                    ),
                ));
            }
            return Ok(RegexBody::Named(name));
        }
        self.parse_character(false).map(RegexBody::Char)
    }

    fn parse_character(&mut self, in_class: bool) -> Result<char, ParseError> {
        if self.consume('\\') {
            let Some(escaped) = self.next() else {
                return Err(self.error("Unexpected end of string after '\\'."));
            };
            return Ok(match escaped {
                'n' => '\n',
                'r' => '\r',
                't' => '\t',
                other => other,
            });
        }
        let Some(next) = self.peek() else {
            return Err(self.error("Unexpected end of string."));
        };
        if if in_class {
            is_reserved_class(next)
        } else {
            is_reserved(next)
        } {
            return Err(self.unescaped(next));
        }
        self.cursor += 1;
        Ok(next)
    }

    fn expect(&mut self, expected: char) -> Result<(), ParseError> {
        match self.next() {
            Some(actual) if actual == expected => Ok(()),
            Some(actual) => Err(self.error_at(
                self.cursor - 1,
                format!("Expected '{expected}', but found '{actual}'"),
            )),
            None => Err(self.error(format!("Unexpected end of string. Expected '{expected}'"))),
        }
    }

    fn has_remaining(&self) -> bool {
        self.cursor < self.characters.len()
    }

    fn peek(&self) -> Option<char> {
        self.characters.get(self.cursor).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<char> {
        self.characters.get(self.cursor + offset).copied()
    }

    fn next(&mut self) -> Option<char> {
        let next = self.peek()?;
        self.cursor += 1;
        Some(next)
    }

    fn consume(&mut self, expected: char) -> bool {
        if self.peek() == Some(expected) {
            self.cursor += 1;
            true
        } else {
            false
        }
    }

    fn unescaped(&self, token: char) -> ParseError {
        self.error(format!(
            "Unexpected token '{token}'. Did you mean '\\{token}'?"
        ))
    }

    fn error(&self, message: impl Into<String>) -> ParseError {
        self.error_at(self.cursor, message)
    }

    fn error_at(&self, index: usize, message: impl Into<String>) -> ParseError {
        ParseError {
            index,
            message: message.into(),
            input: self.input.clone(),
        }
    }
}

/// How a Flex printer writes a character class and `.`.
#[derive(Clone, Copy)]
enum FlexClasses {
    /// As written, for naming a token: Flex would read such a class as a set of bytes.
    AsWritten,
    /// As the UTF-8 encodings of the characters they denote, for a scanner (see
    /// [`RegexBody::to_flex_string`]).
    Utf8,
}

fn print_flex_regex(regex: &Regex, classes: FlexClasses) -> String {
    let mut output = String::new();
    if regex.start_line {
        output.push('^');
    }
    print_flex_union(&regex.body, classes, &mut output).expect("writing to a string cannot fail");
    if regex.end_line {
        output.push('$');
    }
    output
}

// Invariant: `output` holds the Flex text printed so far, and each path back to `print_flex_union` through `print_flex_concat`, `print_flex_repeat`, `print_flex_class`, and `print_flex_simple` receives a strict subexpression of `body`, so the size of `body` bounds the calls.
fn print_flex_union(
    body: &RegexBody,
    classes: FlexClasses,
    output: &mut String,
) -> std::fmt::Result {
    if let RegexBody::Union { left, right } = body {
        print_flex_concat(left, classes, output)?;
        output.push('|');
        print_flex_concat(right, classes, output)
    } else {
        print_flex_concat(body, classes, output)
    }
}

fn print_flex_concat(
    body: &RegexBody,
    classes: FlexClasses,
    output: &mut String,
) -> std::fmt::Result {
    if let RegexBody::Concat(members) = body {
        for member in members {
            print_flex_repeat(member, classes, output)?;
        }
        Ok(())
    } else {
        print_flex_repeat(body, classes, output)
    }
}

fn print_flex_repeat(
    body: &RegexBody,
    classes: FlexClasses,
    output: &mut String,
) -> std::fmt::Result {
    let (body, suffix) = match body {
        RegexBody::ZeroOrOne(body) => (body, "?".to_owned()),
        RegexBody::ZeroOrMore(body) => (body, "*".to_owned()),
        RegexBody::OneOrMore(body) => (body, "+".to_owned()),
        RegexBody::Exactly { body, count } => (body, format!("{{{count}}}")),
        RegexBody::AtLeast { body, count } => (body, format!("{{{count},}}")),
        RegexBody::Range {
            body,
            at_least,
            at_most,
        } => (body, format!("{{{at_least},{at_most}}}")),
        _ => return print_flex_class(body, classes, output),
    };
    print_flex_class(body, classes, output)?;
    output.push_str(&suffix);
    Ok(())
}

fn print_flex_class(
    body: &RegexBody,
    classes: FlexClasses,
    output: &mut String,
) -> std::fmt::Result {
    match (body, classes) {
        (RegexBody::CharClass { negated, members }, FlexClasses::AsWritten) => {
            print_flex_class_as_written(*negated, members, output)
        }
        (RegexBody::CharClass { negated, members }, FlexClasses::Utf8) => {
            if !negated
                && members.iter().all(|member| match *member {
                    CharClass::Char(character) => character.is_ascii(),
                    CharClass::Range { start, end } => start.is_ascii() && end.is_ascii(),
                })
            {
                // Every character it denotes is one byte, so the class is its own encoding.
                print_flex_class_as_written(false, members, output)
            } else {
                print_flex_utf8_set(&class_scalar_ranges(*negated, members), output)
            }
        }
        (RegexBody::AnyChar, FlexClasses::Utf8) => {
            // `.` is every character but `\n`.
            let newline = u32::from(b'\n');
            print_flex_utf8_set(&complement_scalar_ranges(&[(newline, newline)]), output)
        }
        _ => print_flex_simple(body, classes, output),
    }
}

fn print_flex_class_as_written(
    negated: bool,
    members: &[CharClass],
    output: &mut String,
) -> std::fmt::Result {
    output.push('[');
    if negated {
        output.push('^');
    }
    for member in members {
        print_flex_class_member(member, output)?;
    }
    output.push(']');
    Ok(())
}

fn print_flex_class_member(member: &CharClass, output: &mut String) -> std::fmt::Result {
    match member {
        CharClass::Char(character) => print_flex_character(*character, true, output),
        CharClass::Range { start, end } => {
            print_flex_character(*start, true, output)?;
            output.push('-');
            print_flex_character(*end, true, output)
        }
    }
}

fn print_flex_simple(
    body: &RegexBody,
    classes: FlexClasses,
    output: &mut String,
) -> std::fmt::Result {
    match body {
        RegexBody::Char(character) => print_flex_character(*character, false, output),
        RegexBody::AnyChar => {
            output.push('.');
            Ok(())
        }
        RegexBody::Named(name) => write!(output, "{{{}}}", mangle_flex_identifier(name)),
        _ => {
            output.push('(');
            print_flex_union(body, classes, output)?;
            output.push(')');
            Ok(())
        }
    }
}

/// The largest Unicode scalar value.
const MAX_SCALAR: u32 = 0x10_FFFF;
/// The surrogate code points, which are no Unicode scalar value, so no character of a K regex or
/// of a UTF-8 text.
const SURROGATES: (u32, u32) = (0xD800, 0xDFFF);

/// The scalar values a class denotes, as sorted, disjoint ranges (a descending range denotes
/// none). A negated class's ranges may cover surrogate code points, which no text holds.
fn class_scalar_ranges(negated: bool, members: &[CharClass]) -> Vec<(u32, u32)> {
    let ranges = members.iter().filter_map(|member| match *member {
        CharClass::Char(character) => Some((character as u32, character as u32)),
        CharClass::Range { start, end } => (start <= end).then_some((start as u32, end as u32)),
    });
    let set = merge_scalar_ranges(ranges);
    if negated {
        complement_scalar_ranges(&set)
    } else {
        set
    }
}

/// The union of `ranges` (inclusive, each nonempty) as sorted, disjoint, non-adjacent ranges.
fn merge_scalar_ranges(ranges: impl Iterator<Item = (u32, u32)>) -> Vec<(u32, u32)> {
    let mut ranges = ranges.collect::<Vec<_>>();
    ranges.sort_unstable();
    let mut merged = Vec::<(u32, u32)>::with_capacity(ranges.len());
    for (start, end) in ranges {
        match merged.last_mut() {
            Some((_, last_end)) if start <= last_end.saturating_add(1) => {
                *last_end = (*last_end).max(end);
            }
            _ => merged.push((start, end)),
        }
    }
    merged
}

/// The scalar values outside the sorted, disjoint `set`, as sorted, disjoint ranges.
fn complement_scalar_ranges(set: &[(u32, u32)]) -> Vec<(u32, u32)> {
    let mut complement = Vec::with_capacity(set.len() + 1);
    let mut next = 0;
    for &(start, end) in set {
        if next < start {
            complement.push((next, start - 1));
        }
        next = end + 1;
    }
    if next <= MAX_SCALAR {
        complement.push((next, MAX_SCALAR));
    }
    complement
}

/// Print a Flex pattern that matches exactly the UTF-8 encodings of the scalar values in `set`
/// (sorted, disjoint ranges), one character each.
///
/// Flex reads its input as bytes, so a class that denotes characters matches only the one-byte
/// ones. The ASCII part of `set` is one byte class; each other character is a sequence of two to
/// four bytes, and [`utf8_sequences`] splits each range of them into sequences of byte ranges
/// whose concatenations are exactly the encodings of that range, so a scanner matches one whole
/// character where the in-process scanner does: never part of one, and never a byte sequence that
/// encodes no character (a surrogate, or not UTF-8 at all). The alternation is parenthesized, so a
/// repetition applies to the whole character.
fn print_flex_utf8_set(set: &[(u32, u32)], output: &mut String) -> std::fmt::Result {
    let mut alternatives = Vec::new();
    let ascii = set
        .iter()
        .filter(|(start, _)| *start <= 0x7F)
        .map(|&(start, end)| (start as u8, end.min(0x7F) as u8))
        .collect::<Vec<_>>();
    if !ascii.is_empty() {
        let mut class = String::from("[");
        for (start, end) in ascii {
            print_flex_byte(start, &mut class)?;
            if end > start {
                class.push('-');
                print_flex_byte(end, &mut class)?;
            }
        }
        class.push(']');
        alternatives.push(class);
    }
    let mut sequences = Vec::new();
    for &(start, end) in set {
        let start = start.max(0x80);
        if start <= end {
            utf8_sequences(start, end, &mut sequences);
        }
    }
    for sequence in sequences {
        let mut printed = String::new();
        for (start, end) in sequence {
            if start == end {
                print_flex_byte(start, &mut printed)?;
            } else {
                printed.push('[');
                print_flex_byte(start, &mut printed)?;
                printed.push('-');
                print_flex_byte(end, &mut printed)?;
                printed.push(']');
            }
        }
        alternatives.push(printed);
    }
    if alternatives.is_empty() {
        // The empty set, which no text matches: the class of no byte.
        output.push_str(r"[^\x00-\xFF]");
        return Ok(());
    }
    output.push('(');
    output.push_str(&alternatives.join("|"));
    output.push(')');
    Ok(())
}

/// The scalar values of each UTF-8 encoded length, in increasing order.
const UTF8_LENGTHS: [(u32, u32); 4] = [
    (0, 0x7F),
    (0x80, 0x7FF),
    (0x800, 0xFFFF),
    (0x1_0000, MAX_SCALAR),
];

/// Append to `sequences` the UTF-8 encodings of the scalar values in `start..=end`, the
/// surrogates excluded, as sequences of byte ranges, in increasing order of the values they
/// encode: a sequence `[(s1, e1), ..., (sn, en)]` stands for every `n`-byte string whose `i`th
/// byte lies in `si..=ei`, and the strings of all of them are exactly the encodings.
///
/// The encodings of a range whose values share their encoded length form such a product exactly
/// when, for each number `k` of trailing continuation bytes, the start and the end either agree
/// on every bit above those `k` bytes, or the start's `k` bytes are all minimal and the end's all
/// maximal: UTF-8 writes a value's bits in order, six to a continuation byte, so the bytes then
/// vary independently over their ranges. Any other range splits, at the first `k` that fails,
/// into a part that completes the start's `k` bytes and the rest, or into the rest and a part
/// that begins the end's.
fn utf8_sequences(start: u32, end: u32, sequences: &mut Vec<Vec<(u8, u8)>>) {
    let (low, high) = SURROGATES;
    for (length_start, length_end) in UTF8_LENGTHS {
        for (start, end) in [
            (start.max(length_start), end.min(length_end).min(low - 1)),
            (start.max(length_start).max(high + 1), end.min(length_end)),
        ] {
            if start <= end {
                utf8_sequences_of_one_length(start, end, sequences);
            }
        }
    }
}

// Invariant: `start..=end` is nonempty and holds scalar values of one encoded length and no
// surrogate; each recursive call receives a strict subrange of it, so the size of the range bounds
// the calls, and each split leaves one part aligned at the failing count of trailing bytes and at
// every smaller one, so the depth is at most twice the encoded length.
fn utf8_sequences_of_one_length(start: u32, end: u32, sequences: &mut Vec<Vec<(u8, u8)>>) {
    let length = char::from_u32(start).map_or(1, char::len_utf8);
    for trailing in 1..length {
        let mask = (1u32 << (6 * trailing)) - 1;
        if start & !mask != end & !mask {
            if start & mask != 0 {
                utf8_sequences_of_one_length(start, start | mask, sequences);
                utf8_sequences_of_one_length((start | mask) + 1, end, sequences);
                return;
            }
            if end & mask != mask {
                utf8_sequences_of_one_length(start, (end & !mask) - 1, sequences);
                utf8_sequences_of_one_length(end & !mask, end, sequences);
                return;
            }
        }
    }
    let encode = |value: u32| {
        let mut buffer = [0; 4];
        char::from_u32(value)
            .expect("the range holds scalar values only")
            .encode_utf8(&mut buffer);
        buffer
    };
    let (start_bytes, end_bytes) = (encode(start), encode(end));
    sequences.push(
        start_bytes[..length]
            .iter()
            .zip(&end_bytes[..length])
            .map(|(&start, &end)| (start, end))
            .collect(),
    );
}

/// A byte as a Flex hexadecimal escape, which means that byte in a class and outside one alike.
fn print_flex_byte(byte: u8, output: &mut String) -> std::fmt::Result {
    write!(output, "\\x{byte:02X}")
}

fn print_flex_character(character: char, in_class: bool, output: &mut String) -> std::fmt::Result {
    // Outside a class, a character of several bytes is grouped so that a repetition applies to
    // all of them; a class is printed with one only when it names a token (`FlexClasses`).
    let grouped = !in_class && !character.is_ascii();
    if grouped {
        output.push('(');
    }
    match character {
        '\n' => output.push_str("\\n"),
        '\r' => output.push_str("\\r"),
        '\t' => output.push_str("\\t"),
        character => {
            let reserved = if in_class {
                matches!(character, '^' | '-' | '\\' | '[' | ']' | ' ')
            } else {
                matches!(
                    character,
                    '^' | '$'
                        | '|'
                        | '?'
                        | '*'
                        | '+'
                        | '('
                        | ')'
                        | '{'
                        | '}'
                        | '['
                        | ']'
                        | '\\'
                        | '.'
                        | '"'
                        | '/'
                        | '<'
                        | '>'
                        | ' '
                )
            };
            if reserved {
                output.push('\\');
            }
            output.push(character);
        }
    }
    if grouped {
        output.push(')');
    }
    Ok(())
}

// Invariant: `output` holds the Rust regex text printed so far, and each recursive call prints a strict subexpression of `body`, so the size of `body` bounds the calls.
fn print_rust_regex(body: &RegexBody, output: &mut String) -> Result<(), UnexpandedLexical> {
    match body {
        RegexBody::Char(character) => print_rust_character(*character, false, output),
        RegexBody::AnyChar => output.push('.'),
        RegexBody::Named(name) => return Err(UnexpandedLexical { name: name.clone() }),
        RegexBody::CharClass {
            negated: true,
            members,
        } => print_rust_negated_class(members, output),
        RegexBody::CharClass {
            negated: false,
            members,
        } => {
            output.push('[');
            for member in members {
                match member {
                    CharClass::Char(character) => {
                        print_rust_character(*character, true, output);
                    }
                    CharClass::Range { start, end } => {
                        print_rust_character(*start, true, output);
                        output.push('-');
                        print_rust_character(*end, true, output);
                    }
                }
            }
            output.push(']');
        }
        RegexBody::Union { left, right } => {
            output.push_str("(?:");
            print_rust_regex(left, output)?;
            output.push('|');
            print_rust_regex(right, output)?;
            output.push(')');
        }
        RegexBody::Concat(members) => {
            for member in members {
                print_rust_regex(member, output)?;
            }
        }
        RegexBody::ZeroOrMore(body) => {
            print_rust_repeated(body, "*", output)?;
        }
        RegexBody::ZeroOrOne(body) => {
            print_rust_repeated(body, "?", output)?;
        }
        RegexBody::OneOrMore(body) => {
            print_rust_repeated(body, "+", output)?;
        }
        RegexBody::Exactly { body, count } => {
            print_rust_repeated(body, &format!("{{{count}}}"), output)?;
        }
        RegexBody::AtLeast { body, count } => {
            print_rust_repeated(body, &format!("{{{count},}}"), output)?;
        }
        RegexBody::Range {
            body,
            at_least,
            at_most,
        } => {
            print_rust_repeated(body, &format!("{{{at_least},{at_most}}}"), output)?;
        }
    }
    Ok(())
}

/// Print a negated class as the class of the characters outside it.
///
/// The `regex` crate's own negation is not exact: it reads `[^\x{D7FF}\x{E000}]`, two characters
/// on either side of the surrogate gap, as matching both of them (regex 1.13.1). The complement
/// computed here is a set of scalar values, so the class printed from it matches exactly the
/// characters the negated class denotes.
fn print_rust_negated_class(members: &[CharClass], output: &mut String) {
    let (low, high) = SURROGATES;
    let characters = class_scalar_ranges(true, members)
        .into_iter()
        .flat_map(|(start, end)| {
            [(start, end.min(low - 1)), (start.max(high + 1), end)]
                .into_iter()
                .filter(|(start, end)| start <= end)
        })
        .map(|(start, end)| {
            let character = |value| char::from_u32(value).expect("no surrogate is left");
            (character(start), character(end))
        })
        .collect::<Vec<_>>();
    if characters.is_empty() {
        // Every character is in the class, so it matches none.
        output.push_str(r"[^\x{0}-\x{10FFFF}]");
        return;
    }
    output.push('[');
    for (start, end) in characters {
        print_rust_character(start, true, output);
        if end > start {
            output.push('-');
            print_rust_character(end, true, output);
        }
    }
    output.push(']');
}

fn print_rust_repeated(
    body: &RegexBody,
    suffix: &str,
    output: &mut String,
) -> Result<(), UnexpandedLexical> {
    output.push_str("(?:");
    print_rust_regex(body, output)?;
    output.push(')');
    output.push_str(suffix);
    Ok(())
}

fn print_rust_character(character: char, in_class: bool, output: &mut String) {
    match character {
        '\n' => output.push_str("\\n"),
        '\r' => output.push_str("\\r"),
        '\t' => output.push_str("\\t"),
        character if character.is_control() => {
            write!(output, "\\x{{{:X}}}", character as u32)
                .expect("writing to a string cannot fail");
        }
        character => {
            let escaped = if in_class {
                matches!(character, '\\' | '[' | ']' | '^' | '-' | '&' | '~')
            } else {
                matches!(
                    character,
                    '\\' | '.'
                        | '+'
                        | '*'
                        | '?'
                        | '('
                        | ')'
                        | '|'
                        | '['
                        | ']'
                        | '{'
                        | '}'
                        | '^'
                        | '$'
                        | '#'
                        | '&'
                        | '-'
                        | '~'
                )
            };
            if escaped {
                output.push('\\');
            }
            output.push(character);
        }
    }
}

// Invariant: `output` holds the K regex text printed so far, and each path back to `print_union` through `print_concat`, `print_repeat`, `print_class`, and `print_simple` receives a strict subexpression of `body`, so the size of `body` bounds the calls.
fn print_union(body: &RegexBody, output: &mut String) -> std::fmt::Result {
    if let RegexBody::Union { left, right } = body {
        print_concat(left, output)?;
        output.push('|');
        print_concat(right, output)
    } else {
        print_concat(body, output)
    }
}

fn print_concat(body: &RegexBody, output: &mut String) -> std::fmt::Result {
    if let RegexBody::Concat(members) = body {
        for member in members {
            print_repeat(member, output)?;
        }
        Ok(())
    } else {
        print_repeat(body, output)
    }
}

fn print_repeat(body: &RegexBody, output: &mut String) -> std::fmt::Result {
    match body {
        RegexBody::ZeroOrOne(body) => {
            print_class(body, output)?;
            output.push('?');
        }
        RegexBody::ZeroOrMore(body) => {
            print_class(body, output)?;
            output.push('*');
        }
        RegexBody::OneOrMore(body) => {
            print_class(body, output)?;
            output.push('+');
        }
        RegexBody::Exactly { body, count } => {
            print_class(body, output)?;
            write!(output, "{{{count}}}")?;
        }
        RegexBody::AtLeast { body, count } => {
            print_class(body, output)?;
            write!(output, "{{{count},}}")?;
        }
        RegexBody::Range {
            body,
            at_least,
            at_most,
        } => {
            print_class(body, output)?;
            write!(output, "{{{at_least},{at_most}}}")?;
        }
        _ => print_class(body, output)?,
    }
    Ok(())
}

fn print_class(body: &RegexBody, output: &mut String) -> std::fmt::Result {
    if let RegexBody::CharClass { negated, members } = body {
        output.push('[');
        if *negated {
            output.push('^');
        }
        for member in members {
            print_class_member(member, output)?;
        }
        output.push(']');
        Ok(())
    } else {
        print_simple(body, output)
    }
}

fn print_class_member(member: &CharClass, output: &mut String) -> std::fmt::Result {
    match member {
        CharClass::Char(character) => print_character(*character, true, output),
        CharClass::Range { start, end } => {
            print_character(*start, true, output)?;
            output.push('-');
            print_character(*end, true, output)
        }
    }
}

fn print_simple(body: &RegexBody, output: &mut String) -> std::fmt::Result {
    match body {
        RegexBody::Char(character) => print_character(*character, false, output),
        RegexBody::AnyChar => {
            output.push('.');
            Ok(())
        }
        RegexBody::Named(name) => write!(output, "{{{name}}}"),
        _ => {
            output.push('(');
            print_union(body, output)?;
            output.push(')');
            Ok(())
        }
    }
}

fn print_character(character: char, in_class: bool, output: &mut String) -> std::fmt::Result {
    match character {
        '\n' => output.push_str("\\n"),
        '\r' => output.push_str("\\r"),
        '\t' => output.push_str("\\t"),
        character => {
            if if in_class {
                is_reserved_class(character)
            } else {
                is_reserved(character)
            } {
                output.push('\\');
            }
            output.push(character);
        }
    }
    Ok(())
}

fn is_reserved(character: char) -> bool {
    matches!(
        character,
        '^' | '$' | '|' | '?' | '*' | '+' | '(' | ')' | '{' | '}' | '[' | ']' | '\\' | '.' | '"'
    )
}

fn is_reserved_class(character: char) -> bool {
    matches!(character, '^' | '-' | '\\' | '[' | ']')
}

fn is_decimal_digit(character: char) -> bool {
    character.is_ascii_digit()
}

fn valid_identifier(name: &str) -> bool {
    let name = name.strip_prefix('#').unwrap_or(name);
    let mut characters = name.chars();
    characters
        .next()
        .is_some_and(|first| first.is_ascii_uppercase())
        && characters.all(|character| character.is_ascii_alphanumeric())
}

#[cfg(test)]
mod tests {
    use super::{MAX_SCALAR, utf8_sequences};

    /// The printer's UTF-8 range splitting gives the sequences `regex-syntax`'s independent
    /// implementation gives, for every range between values at the boundaries the encoding has:
    /// encoded lengths, continuation-byte carries, the surrogates and the last scalar value.
    #[test]
    fn utf8_sequences_agree_with_an_independent_implementation() {
        let mut points = vec![0, 0x7F, MAX_SCALAR];
        for boundary in [
            0x80, 0x800, 0x1000, 0xD800, 0xE000, 0x1_0000, 0x4_0000, 0x10_0000,
        ] {
            points.extend([boundary - 1, boundary, boundary + 1]);
        }
        points.extend([0xE9, 0x2028, 0xFFFD, 0x1_F642, 0x10_FFFE, 0x3_ABCD, 0xABCD]);
        let points = points
            .into_iter()
            .filter_map(char::from_u32)
            .collect::<Vec<_>>();
        for &start in &points {
            for &end in points.iter().filter(|&&end| end >= start) {
                let mut ours = Vec::new();
                utf8_sequences(start as u32, end as u32, &mut ours);
                let theirs = regex_syntax::utf8::Utf8Sequences::new(start, end)
                    .map(|sequence| {
                        sequence
                            .as_slice()
                            .iter()
                            .map(|range| (range.start, range.end))
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>();
                assert_eq!(ours, theirs, "{start:?}..={end:?}");
            }
        }
    }
}
