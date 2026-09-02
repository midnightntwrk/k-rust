//! Parsing of outer-syntax bubbles with module-derived inner grammars.

mod config;
mod parser;
mod programs;
mod rules;

pub use config::{ConfigError, resolve_configuration_bubbles};
pub use parser::{AmbiguousParse, Grammar, ParseError, TokenPrecedenceDeclaration};
pub use programs::{
    ProgramError, ProgramParseError, ProgramParser, parse_program, prepare_reference_kast,
};
pub use rules::{RuleError, RuleParseError, resolve_rule_bubbles};
