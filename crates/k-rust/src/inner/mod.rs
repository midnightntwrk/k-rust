//! Parsing of outer-syntax bubbles with module-derived inner grammars.

mod config;
mod parser;
mod rules;

pub use config::{ConfigError, resolve_configuration_bubbles};
pub use parser::{Grammar, ParseError};
pub use rules::{RuleError, RuleParseError, resolve_rule_bubbles};
