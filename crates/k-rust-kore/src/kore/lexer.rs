//! Lexical analysis for textual KORE.

use std::fmt;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TokenKind {
    Comma,
    Colon,
    Walrus,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    String,
    Id,
    SymbolId,
    SetVarId,
    MlTop,
    MlBottom,
    MlNot,
    MlAnd,
    MlOr,
    MlImplies,
    MlIff,
    MlExists,
    MlForall,
    MlMu,
    MlNu,
    MlCeil,
    MlFloor,
    MlEquals,
    MlIn,
    MlNext,
    MlRewrites,
    MlDv,
    MlLeftAssoc,
    MlRightAssoc,
    Module,
    EndModule,
    Import,
    Sort,
    HookedSort,
    Symbol,
    HookedSymbol,
    Axiom,
    Claim,
    Alias,
    Where,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Token<'a> {
    pub kind: TokenKind,
    pub text: &'a str,
    pub offset: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LexError {
    pub offset: usize,
    pub message: &'static str,
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at byte {}", self.message, self.offset)
    }
}

impl std::error::Error for LexError {}

pub fn lex(input: &str) -> Result<Vec<Token<'_>>, LexError> {
    Lexer { input, offset: 0 }.collect()
}

struct Lexer<'a> {
    input: &'a str,
    offset: usize,
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Token<'a>, LexError>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.next_token() {
            Ok(Some(token)) => Some(Ok(token)),
            Ok(None) => None,
            Err(error) => {
                self.offset = self.input.len();
                Some(Err(error))
            }
        }
    }
}

impl<'a> Lexer<'a> {
    fn next_token(&mut self) -> Result<Option<Token<'a>>, LexError> {
        self.skip_trivia()?;
        if self.offset == self.input.len() {
            return Ok(None);
        }

        let start = self.offset;
        let first = self.bump().expect("offset checked above");
        let kind = match first {
            ',' => TokenKind::Comma,
            ':' if self.consume('=') => TokenKind::Walrus,
            ':' => TokenKind::Colon,
            '(' => TokenKind::LParen,
            ')' => TokenKind::RParen,
            '{' => TokenKind::LBrace,
            '}' => TokenKind::RBrace,
            '[' => TokenKind::LBracket,
            ']' => TokenKind::RBracket,
            '"' => {
                self.scan_string(start)?;
                TokenKind::String
            }
            '\\' => self.scan_prefixed_id(start, Prefix::Symbol)?,
            '@' => self.scan_prefixed_id(start, Prefix::SetVariable)?,
            character if character.is_ascii_alphabetic() => {
                self.scan_id_tail();
                classify_id(&self.input[start..self.offset])
            }
            _ => return Err(error(start, "unexpected character")),
        };

        Ok(Some(Token {
            kind,
            text: &self.input[start..self.offset],
            offset: start,
        }))
    }

    fn skip_trivia(&mut self) -> Result<(), LexError> {
        loop {
            while self.peek().is_some_and(is_whitespace) {
                self.bump();
            }

            if self.remaining().starts_with("//") {
                self.offset += 2;
                while self.peek().is_some_and(|character| character != '\n') {
                    self.bump();
                }
            } else if self.remaining().starts_with("/*") {
                let start = self.offset;
                let Some(length) = self.remaining()[2..].find("*/") else {
                    return Err(error(start, "unterminated block comment"));
                };
                self.offset += 2 + length + 2;
            } else {
                return Ok(());
            }
        }
    }

    fn scan_string(&mut self, start: usize) -> Result<(), LexError> {
        loop {
            match self.bump() {
                Some('"') => return Ok(()),
                Some('\\') => {
                    if self.bump().is_none() {
                        return Err(error(start, "unterminated string"));
                    }
                }
                Some(_) => {}
                None => return Err(error(start, "unterminated string")),
            }
        }
    }

    fn scan_prefixed_id(&mut self, start: usize, prefix: Prefix) -> Result<TokenKind, LexError> {
        if !self
            .peek()
            .is_some_and(|character| character.is_ascii_alphabetic())
        {
            return Err(error(
                start,
                "identifier prefix must be followed by a letter",
            ));
        }
        self.bump();
        self.scan_id_tail();
        let text = &self.input[start..self.offset];
        Ok(match prefix {
            Prefix::SetVariable => TokenKind::SetVarId,
            Prefix::Symbol => classify_symbol(text),
        })
    }

    fn scan_id_tail(&mut self) {
        while self.peek().is_some_and(is_id_tail) {
            self.bump();
        }
    }

    fn consume(&mut self, expected: char) -> bool {
        if self.peek() == Some(expected) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn remaining(&self) -> &'a str {
        &self.input[self.offset..]
    }

    fn peek(&self) -> Option<char> {
        self.remaining().chars().next()
    }

    fn bump(&mut self) -> Option<char> {
        let character = self.peek()?;
        self.offset += character.len_utf8();
        Some(character)
    }
}

#[derive(Clone, Copy)]
enum Prefix {
    Symbol,
    SetVariable,
}

fn is_id_tail(character: char) -> bool {
    character.is_ascii_alphanumeric() || matches!(character, '\'' | '-')
}

fn is_whitespace(character: char) -> bool {
    matches!(character, ' ' | '\t' | '\n' | '\r')
}

fn classify_id(text: &str) -> TokenKind {
    match text {
        "module" => TokenKind::Module,
        "endmodule" => TokenKind::EndModule,
        "import" => TokenKind::Import,
        "sort" => TokenKind::Sort,
        "hooked-sort" => TokenKind::HookedSort,
        "symbol" => TokenKind::Symbol,
        "hooked-symbol" => TokenKind::HookedSymbol,
        "axiom" => TokenKind::Axiom,
        "claim" => TokenKind::Claim,
        "alias" => TokenKind::Alias,
        "where" => TokenKind::Where,
        _ => TokenKind::Id,
    }
}

fn classify_symbol(text: &str) -> TokenKind {
    match text {
        "\\top" => TokenKind::MlTop,
        "\\bottom" => TokenKind::MlBottom,
        "\\not" => TokenKind::MlNot,
        "\\and" => TokenKind::MlAnd,
        "\\or" => TokenKind::MlOr,
        "\\implies" => TokenKind::MlImplies,
        "\\iff" => TokenKind::MlIff,
        "\\exists" => TokenKind::MlExists,
        "\\forall" => TokenKind::MlForall,
        "\\mu" => TokenKind::MlMu,
        "\\nu" => TokenKind::MlNu,
        "\\ceil" => TokenKind::MlCeil,
        "\\floor" => TokenKind::MlFloor,
        "\\equals" => TokenKind::MlEquals,
        "\\in" => TokenKind::MlIn,
        "\\next" => TokenKind::MlNext,
        "\\rewrites" => TokenKind::MlRewrites,
        "\\dv" => TokenKind::MlDv,
        "\\left-assoc" => TokenKind::MlLeftAssoc,
        "\\right-assoc" => TokenKind::MlRightAssoc,
        _ => TokenKind::SymbolId,
    }
}

const fn error(offset: usize, message: &'static str) -> LexError {
    LexError { offset, message }
}
