//! Parsing of outer-syntax bubbles with module-derived inner grammars.

mod config;
mod parser;
mod programs;
mod rules;

pub use config::{ConfigError, resolve_configuration_bubbles};
pub use parser::{Grammar, ParseError};
pub use programs::{ProgramError, ProgramParseError, ProgramParser, parse_program};
pub use rules::{RuleError, RuleParseError, resolve_rule_bubbles};
