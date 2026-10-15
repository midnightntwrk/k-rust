//! Inner parsing is a six-layer pipeline: grammar construction, global-winner scanning,
//! agenda-driven Earley recognition, packed-forest normalization, sort inference, and
//! tree disambiguation/lowering. Bubble drivers count work with
//! `Counter::KompileRuleBubblesParsed`; each algorithm module documents its own cost.

mod config;
mod location;
mod parser;
mod programs;
mod rules;
mod sort_universe;

pub use config::{ConfigError, resolve_configuration_bubbles};
#[cfg(feature = "cli")]
pub(crate) use parser::exclusion::{Exclusions, NodeShape};
pub use parser::{
    AmbiguityPlace, AmbiguousParse, CyclicDerivation, DiagnosticWork, Grammar, NoParseInput,
    NoParseNotes, ParseError, ProgramTextConstruct, ProgramTextPhrase, ShadowedToken,
    TokenPrecedenceDeclaration,
};
#[cfg(feature = "cli")]
pub(crate) use parser::{DEFAULT_LAYOUT, concretize_parametric_productions, parse_apply_priority};
pub(crate) use programs::LOCATION_LABEL;
pub use programs::{
    ParsedProgram, PresentedProgram, ProgramError, ProgramParseError, ProgramParser,
    UNNAMED_PROGRAM, definition_with_named_projections, parse_program, program_file_name,
};
#[cfg(feature = "cli")]
pub(crate) use programs::{prepared_bison_program_sentences, program_start_sort};
pub use rules::{RuleError, RuleParseError, parse_rule_content, resolve_rule_bubbles};
pub(crate) use rules::{
    grammar_injected_sentences, resolve_rule_bubbles_with_resolved, rule_language_productions,
};
pub(crate) use sort_universe::unbound_sorts;
