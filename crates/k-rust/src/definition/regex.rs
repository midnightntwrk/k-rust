//! K's structured regular-expression syntax.

use std::fmt::{Display, Write};

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Regex {
    pub start_line: bool,
    pub body: RegexBody,
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

    /// Match Java `RegexSyntax.K.print`, including its asymmetric-anchor bug.
    pub fn to_java_string(&self) -> String {
        print_regex(self, self.start_line)
    }

    /// Print both anchors represented by the AST without Java's anchor-loss bug.
    pub fn to_source_string(&self) -> String {
        print_regex(self, self.end_line)
    }
}

impl Display for Regex {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.to_java_string())
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
    pub fn visit_preorder(&self, visitor: &mut impl FnMut(&Self)) {
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

    pub fn to_k_string(&self) -> String {
        let mut output = String::new();
        print_union(self, &mut output).expect("writing to a string cannot fail");
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
}

impl Display for CharClass {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.to_k_string())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseError {
    pub index: usize,
    pub message: String,
    pub input: String,
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

pub fn parse(input: &str) -> Result<Regex, ParseError> {
    Parser::new(input).parse()
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
            self.cursor -= usize::from(end_line);
            return Err(self.unescaped('$'));
        }
        Ok(Regex {
            start_line,
            body,
            end_line,
        })
    }

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

fn print_regex(regex: &Regex, end_line: bool) -> String {
    let mut output = String::new();
    if regex.start_line {
        output.push('^');
    }
    print_union(&regex.body, &mut output).expect("writing to a string cannot fail");
    if end_line {
        output.push('$');
    }
    output
}

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
