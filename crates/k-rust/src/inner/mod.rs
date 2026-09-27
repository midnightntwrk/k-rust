//! Inner parsing is a six-layer pipeline: grammar construction, global-winner scanning,
//! agenda-driven Earley recognition, packed-forest normalization, sort inference, and
//! tree disambiguation/lowering. Bubble drivers count work with
//! `Counter::KompileRuleBubblesParsed`; each algorithm module documents its own cost.

mod config;
mod location;
mod parser;
mod programs;
mod rules;

pub use config::{ConfigError, resolve_configuration_bubbles};
pub use parser::{
    AmbiguousParse, CyclicDerivation, Grammar, NoParseInput, ParseError, TokenPrecedenceDeclaration,
};
#[cfg(feature = "cli")]
pub(crate) use parser::{DEFAULT_LAYOUT, concretize_parametric_productions};
#[cfg(feature = "cli")]
pub(crate) use programs::prepared_bison_program_sentences;
pub use programs::{
    ProgramError, ProgramParseError, ProgramParser, definition_with_named_projections,
    parse_program, parse_program_for_presentation, prepare_reference_kast,
};
pub(crate) use rules::resolve_rule_bubbles_with_resolved;
pub use rules::{RuleError, RuleParseError, parse_rule_content, resolve_rule_bubbles};
