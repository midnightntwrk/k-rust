//! Parsing of outer-syntax bubbles with module-derived inner grammars.

mod config;
mod parser;
mod programs;
mod rules;

pub use config::{ConfigError, resolve_configuration_bubbles};
pub use parser::{AmbiguousParse, Grammar, ParseError, TokenPrecedenceDeclaration};
pub use programs::{
    ProgramError, ProgramParseError, ProgramParser, definition_with_named_projections,
    parse_program, parse_program_for_presentation, prepare_reference_kast,
};
pub use rules::{RuleError, RuleParseError, resolve_rule_bubbles};
