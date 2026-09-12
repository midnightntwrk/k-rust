//! Parsing of outer-syntax bubbles with module-derived inner grammars.

mod config;
mod parser;
mod programs;
mod rules;

pub use config::{ConfigError, resolve_configuration_bubbles};
pub use parser::{AmbiguousParse, Grammar, ParseError, TokenPrecedenceDeclaration};
#[cfg(feature = "cli")]
pub(crate) use parser::{DEFAULT_LAYOUT, concretize_parametric_productions};
#[cfg(feature = "cli")]
pub(crate) use programs::prepared_bison_program_sentences;
pub use programs::{
    ProgramError, ProgramParseError, ProgramParser, definition_with_named_projections,
    parse_program, parse_program_for_presentation, prepare_reference_kast,
};
pub use rules::{RuleError, RuleParseError, parse_rule_content, resolve_rule_bubbles};
