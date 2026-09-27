//! KORE syntax, parsing, printing, and serialization.

pub mod ast;
pub mod binary;
pub mod codec;
pub mod json;
pub mod lexer;
pub mod lexical;
pub mod node;
pub mod normalize;
pub mod parser;
pub mod printer;
pub mod string;
pub mod walk;

#[cfg(test)]
mod deep;
