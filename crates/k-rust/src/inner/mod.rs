//! Parsing of outer-syntax bubbles with module-derived inner grammars.

mod config;
mod parser;

pub use config::{ConfigError, resolve_configuration_bubbles};
pub use parser::{Grammar, ParseError};
