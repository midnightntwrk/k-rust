//! Parsing user programs with a module's concrete syntax.

use std::collections::BTreeSet;
use std::fmt;

use crate::definition::{
    Definition, ModuleId, ProductionCatalog, ProductionId, ResolveError, ResolvedDefinition,
    Sentence, sentence_equivalent,
};
use crate::kast::{Sort, Term};
use crate::provenance::SourceId;

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
        let source_catalog = definition.production_catalog(module_id);
        let grammar =
            Grammar::from_program_sentences(&sentences, &source_catalog).map_err(|error| {
                ProgramError::Grammar {
                    module: module.to_owned(),
                    error,
                }
            })?;
        Ok(Self {
            module: module.to_owned(),
            grammar,
        })
    }

    pub fn module(&self) -> &str {
        &self.module
    }

    /// Parse a program without claiming that it belongs to a known logical source.
    ///
    /// Production and sort metadata remain available, but source spans are omitted.
    /// Use [`Self::parse_with_provenance`] when the caller owns a [`SourceId`].
    pub fn parse(&self, start_sort: &Sort, source: &str) -> Result<Term, ProgramParseError> {
        self.grammar
            .parse(start_sort, source)
            .map(without_source_spans)
            .map_err(|error| ProgramParseError {
                module: self.module.clone(),
                start_sort: start_sort.clone(),
                error: Box::new(error),
            })
    }

    /// Parse a program whose byte zero belongs to `source_id`.
    pub fn parse_with_provenance(
        &self,
        start_sort: &Sort,
        source: &str,
        source_id: SourceId,
    ) -> Result<Term, ProgramParseError> {
        self.grammar
            .parse_with_provenance(start_sort, source, source_id, 0)
            .map_err(|error| ProgramParseError {
                module: self.module.clone(),
                start_sort: start_sort.clone(),
                error: Box::new(error),
            })
    }
}

fn without_source_spans(term: Term) -> Term {
    match term {
        Term::Annotated { term, mut metadata } => {
            metadata.span = None;
            without_source_spans(*term).with_metadata(metadata)
        }
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(without_source_spans(*left)),
            right: Box::new(without_source_spans(*right)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(without_source_spans(*pattern)),
            alias: Box::new(without_source_spans(*alias)),
        },
        Term::Sequence(items) => {
            Term::Sequence(items.into_iter().map(without_source_spans).collect())
        }
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments.into_iter().map(without_source_spans).collect(),
        },
        term @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => term,
    }
}

/// Parse one program using the concrete syntax visible from `module`.
pub fn parse_program(
    definition: &Definition,
    module: &str,
    start_sort: &Sort,
    source: &str,
    source_id: SourceId,
) -> Result<Term, ProgramError> {
    let parser = ProgramParser::new(definition, module)?;
    parser
        .parse_with_provenance(start_sort, source, source_id)
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

/// Match the reference `kast` presentation boundary without weakening the typed term used by
/// execution and compilation. The reference concrete parser infers parametric production sorts
/// but omits those inferred arguments from the user-facing KLabel.
pub fn prepare_reference_kast(term: Term, productions: &ProductionCatalog<'_>) -> Term {
    let metadata = term.metadata().cloned();
    let inferred_production_parameters = metadata
        .as_ref()
        .and_then(|metadata| metadata.production)
        .is_some_and(|production| {
            production.0 < productions.len()
                && matches!(
                    productions.production(ProductionId(production.0)),
                    Sentence::Production { parameters, .. } if !parameters.is_empty()
                )
        });
    let rebuilt = match term.into_unannotated() {
        Term::Apply {
            mut label,
            arguments,
        } => {
            if inferred_production_parameters {
                label.parameters.clear();
            }
            Term::Apply {
                label,
                arguments: arguments
                    .into_iter()
                    .map(|argument| prepare_reference_kast(argument, productions))
                    .collect(),
            }
        }
        Term::InjectedLabel(mut label) => {
            if inferred_production_parameters {
                label.parameters.clear();
            }
            Term::InjectedLabel(label)
        }
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(prepare_reference_kast(*left, productions)),
            right: Box::new(prepare_reference_kast(*right, productions)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(prepare_reference_kast(*pattern, productions)),
            alias: Box::new(prepare_reference_kast(*alias, productions)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| prepare_reference_kast(item, productions))
                .collect(),
        ),
        leaf @ (Term::Variable { .. } | Term::Token { .. }) => leaf,
        Term::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
    };
    match metadata {
        Some(metadata) => rebuilt.with_metadata(metadata),
        None => rebuilt,
    }
}
