//! Parsing user programs with a module's concrete syntax.

use std::collections::BTreeSet;
use std::fmt;

use crate::definition::{
    Definition, ModuleId, ResolveError, ResolvedDefinition, Sentence, sentence_equivalent,
};
use crate::kast::{Sort, Term};

use super::parser::{Grammar, ParseError};

const PROGRAM_PARSING_POSTFIX: &str = "-PROGRAM-PARSING";

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProgramError {
    Definition(ResolveError),
    MissingModule(String),
    Grammar { module: String, error: ParseError },
    Parse(ProgramParseError),
}

impl fmt::Display for ProgramError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Definition(error) => error.fmt(formatter),
            Self::MissingModule(module) => {
                write!(formatter, "program syntax module {module:?} was not found")
            }
            Self::Grammar { module, error } => {
                write!(
                    formatter,
                    "could not build program grammar for module {module:?}: {error}"
                )
            }
            Self::Parse(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for ProgramError {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgramParseError {
    pub module: String,
    pub start_sort: Sort,
    pub error: Box<ParseError>,
}

impl fmt::Display for ProgramParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "could not parse program as {} with module {:?}: {}",
            self.start_sort, self.module, self.error
        )
    }
}

impl std::error::Error for ProgramParseError {}

/// A reusable parser for the concrete program syntax visible from one module.
#[derive(Clone, Debug)]
pub struct ProgramParser {
    module: String,
    grammar: Grammar,
}

impl ProgramParser {
    pub fn new(definition: &Definition, module: &str) -> Result<Self, ProgramError> {
        let resolved = ResolvedDefinition::resolve(definition).map_err(ProgramError::Definition)?;
        Self::from_resolved(&resolved, module)
    }

    pub fn from_resolved(
        definition: &ResolvedDefinition,
        module: &str,
    ) -> Result<Self, ProgramError> {
        let module_id = definition
            .module_id(module)
            .ok_or_else(|| ProgramError::MissingModule(module.to_owned()))?;
        let sentences = program_sentences(definition, module_id);
        let grammar =
            Grammar::from_program_sentences(&sentences).map_err(|error| ProgramError::Grammar {
                module: module.to_owned(),
                error,
            })?;
        Ok(Self {
            module: module.to_owned(),
            grammar,
        })
    }

    pub fn module(&self) -> &str {
        &self.module
    }

    pub fn parse(&self, start_sort: &Sort, source: &str) -> Result<Term, ProgramParseError> {
        self.grammar
            .parse(start_sort, source)
            .map_err(|error| ProgramParseError {
                module: self.module.clone(),
                start_sort: start_sort.clone(),
                error: Box::new(error),
            })
    }
}

/// Parse one program using the concrete syntax visible from `module`.
pub fn parse_program(
    definition: &Definition,
    module: &str,
    start_sort: &Sort,
    source: &str,
) -> Result<Term, ProgramError> {
    let parser = ProgramParser::new(definition, module)?;
    parser
        .parse(start_sort, source)
        .map_err(ProgramError::Parse)
}

fn program_sentences(definition: &ResolvedDefinition, module: ModuleId) -> Vec<Sentence> {
    let substitute_imports = !definition
        .module(module)
        .name
        .ends_with(PROGRAM_PARSING_POSTFIX);

    let mut visited = BTreeSet::new();
    let mut sentences = Vec::new();
    for import in definition.direct_imports(module) {
        let (imported, substituted) = if substitute_imports {
            program_import(definition, import.module)
        } else {
            (import.module, false)
        };
        collect_public_signature(
            definition,
            imported,
            substitute_imports && !substituted,
            &mut visited,
            &mut sentences,
        );
    }
    append_unique(
        &mut sentences,
        definition.module(module).local_sentences.iter(),
    );
    sentences
}

fn collect_public_signature(
    definition: &ResolvedDefinition,
    module: ModuleId,
    substitute_imports: bool,
    visited: &mut BTreeSet<(ModuleId, bool)>,
    sentences: &mut Vec<Sentence>,
) {
    if !visited.insert((module, substitute_imports)) {
        return;
    }
    for import in definition
        .direct_imports(module)
        .into_iter()
        .filter(|import| import.public)
    {
        let (imported, substituted) = if substitute_imports {
            program_import(definition, import.module)
        } else {
            (import.module, false)
        };
        collect_public_signature(
            definition,
            imported,
            substitute_imports && !substituted,
            visited,
            sentences,
        );
    }
    append_unique(sentences, definition.public_sentences(module));
}

fn program_import(definition: &ResolvedDefinition, module: ModuleId) -> (ModuleId, bool) {
    let imported_name = &definition.module(module).name;
    let companion_name = format!("{imported_name}{PROGRAM_PARSING_POSTFIX}");
    definition
        .module_id(&companion_name)
        .map_or((module, false), |companion| (companion, true))
}

fn append_unique<'a>(
    sentences: &mut Vec<Sentence>,
    incoming: impl IntoIterator<Item = &'a Sentence>,
) {
    for sentence in incoming {
        if !sentences
            .iter()
            .any(|existing| sentence_equivalent(existing, sentence))
        {
            sentences.push(sentence.clone());
        }
    }
}
