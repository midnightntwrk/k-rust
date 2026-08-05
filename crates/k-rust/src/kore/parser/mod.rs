//! Recursive-descent parser for textual KORE.

mod definition;
mod pattern;
mod sentence;

use std::fmt;

use crate::kore::ast::{Definition, Module, Pattern, Sentence};
use crate::kore::lexer::{LexError, Token, TokenKind, lex};

pub fn parse_pattern(input: &str) -> Result<Pattern, ParseError> {
    Parser::new(input)?.finish(Parser::pattern)
}

pub fn parse_sentence(input: &str) -> Result<Sentence, ParseError> {
    Parser::new(input)?.finish(Parser::sentence)
}

pub fn parse_module(input: &str) -> Result<Module, ParseError> {
    Parser::new(input)?.finish(Parser::module)
}

pub fn parse_definition(input: &str) -> Result<Definition, ParseError> {
    Parser::new(input)?.finish(Parser::definition)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseError {
    pub offset: usize,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at byte {}", self.message, self.offset)
    }
}

impl std::error::Error for ParseError {}

impl From<LexError> for ParseError {
    fn from(error: LexError) -> Self {
        Self {
            offset: error.offset,
            message: error.message.into(),
        }
    }
}

struct Parser<'a> {
    tokens: Vec<Token<'a>>,
    cursor: usize,
    input_len: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Result<Self, ParseError> {
        Ok(Self {
            tokens: lex(input)?,
            cursor: 0,
            input_len: input.len(),
        })
    }

    fn finish<T>(
        mut self,
        parse: impl FnOnce(&mut Self) -> Result<T, ParseError>,
    ) -> Result<T, ParseError> {
        let value = parse(&mut self)?;
        if let Some(token) = self.peek() {
            return Err(ParseError {
                offset: token.offset,
                message: format!("unexpected trailing token {:?}", token.kind),
            });
        }
        Ok(value)
    }

    fn peek(&self) -> Option<Token<'a>> {
        self.tokens.get(self.cursor).copied()
    }

    fn at(&self, kind: TokenKind) -> bool {
        self.peek().is_some_and(|token| token.kind == kind)
    }

    fn consume(&mut self, kind: TokenKind) -> Option<Token<'a>> {
        if self.at(kind) {
            let token = self.tokens[self.cursor];
            self.cursor += 1;
            Some(token)
        } else {
            None
        }
    }

    fn expect(&mut self, kind: TokenKind) -> Result<Token<'a>, ParseError> {
        self.consume(kind).ok_or_else(|| self.expected(kind))
    }

    fn expected(&self, expected: TokenKind) -> ParseError {
        match self.peek() {
            Some(actual) => ParseError {
                offset: actual.offset,
                message: format!("expected {expected:?}, found {:?}", actual.kind),
            },
            None => ParseError {
                offset: self.input_len,
                message: format!("expected {expected:?}, found end of input"),
            },
        }
    }

    fn delimited<T>(
        &mut self,
        open: TokenKind,
        close: TokenKind,
        mut parse: impl FnMut(&mut Self) -> Result<T, ParseError>,
    ) -> Result<Vec<T>, ParseError> {
        self.expect(open)?;
        let mut values = Vec::new();
        if self.consume(close).is_some() {
            return Ok(values);
        }
        loop {
            values.push(parse(self)?);
            if self.consume(TokenKind::Comma).is_none() {
                self.expect(close)?;
                return Ok(values);
            }
        }
    }
}
