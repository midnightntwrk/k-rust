//! Recursive, host-independent loading of outer-syntax source graphs.

use std::{collections::BTreeMap, error::Error, fmt};

use crate::{
    definition::{
        ConfigurationError, Definition, ResolveError, ResolvedDefinition, apply_sort_synonyms,
        expand_configurations,
    },
    diagnostic::Diagnostic,
    inner::{ConfigError, resolve_configuration_bubbles},
};

use super::{ParseError, SourceFile, Span, lower::lower_files, parse};

/// Source text returned by a host resolver.
///
/// `source` is both the diagnostic name and the canonical identity used for
/// deduplication. Native callers should use a canonical path; browser callers
/// can use a stable URL or virtual-file identifier.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedSource {
    pub source: String,
    pub text: String,
}

impl ResolvedSource {
    pub fn new(source: impl Into<String>, text: impl Into<String>) -> Self {
        Self {
            source: source.into(),
            text: text.into(),
        }
    }
}

/// Resolves a `requires` path without coupling the portable frontend to a
/// filesystem, URL loader, editor workspace, or JavaScript host.
pub trait SourceResolver {
    fn resolve(&mut self, requiring_source: &str, required: &str)
    -> Result<ResolvedSource, String>;
}

impl<F> SourceResolver for F
where
    F: FnMut(&str, &str) -> Result<ResolvedSource, String>,
{
    fn resolve(
        &mut self,
        requiring_source: &str,
        required: &str,
    ) -> Result<ResolvedSource, String> {
        self(requiring_source, required)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LoadError {
    Parse {
        source: String,
        error: ParseError,
    },
    ResolveRequire {
        source: String,
        required: String,
        span: Span,
        message: String,
    },
    CircularRequires(Vec<String>),
    DuplicateModule {
        name: String,
        first_source: String,
        second_source: String,
    },
    SourceDiagnostics(Vec<Diagnostic>),
    DefinitionResolution(ResolveError),
    Configuration(ConfigError),
    ConfigurationExpansion(ConfigurationError),
}

impl fmt::Display for LoadError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse { source, error } => {
                write!(formatter, "failed to parse {source:?}: {error}")
            }
            Self::ResolveRequire {
                source,
                required,
                message,
                ..
            } => write!(
                formatter,
                "could not resolve {required:?} required by {source:?}: {message}"
            ),
            Self::CircularRequires(path) => {
                write!(formatter, "circular requires: {}", path.join(" -> "))
            }
            Self::DuplicateModule {
                name,
                first_source,
                second_source,
            } => write!(
                formatter,
                "module {name:?} is declared by both {first_source:?} and {second_source:?}"
            ),
            Self::SourceDiagnostics(diagnostics) => {
                write!(
                    formatter,
                    "outer source checks produced {} errors",
                    diagnostics.len()
                )
            }
            Self::DefinitionResolution(error) => error.fmt(formatter),
            Self::Configuration(error) => error.fmt(formatter),
            Self::ConfigurationExpansion(error) => error.fmt(formatter),
        }
    }
}

impl Error for LoadError {}

/// A completely loaded and import-resolved source graph.
#[derive(Clone, Debug)]
pub struct LoadedDefinition {
    /// Parsed files in dependency-first `requires` order.
    pub files: Vec<SourceFile>,
    pub definition: Definition,
    pub resolved: ResolvedDefinition,
}

/// Load one entry source, recursively resolve `requires`, lower all files with
/// one global tag index, and resolve the resulting module-import graph.
pub fn load(
    entry: ResolvedSource,
    main_module: impl Into<String>,
    resolver: &mut impl SourceResolver,
) -> Result<LoadedDefinition, LoadError> {
    let mut loader = Loader {
        resolver,
        states: BTreeMap::new(),
        stack: Vec::new(),
        files: Vec::new(),
    };
    loader.visit(entry)?;
    validate_unique_modules(&loader.files)?;

    let definition =
        lower_files(&loader.files, main_module).map_err(LoadError::SourceDiagnostics)?;
    let definition = apply_sort_synonyms(&definition).map_err(LoadError::DefinitionResolution)?;
    let definition =
        resolve_configuration_bubbles(&definition).map_err(LoadError::Configuration)?;
    let definition =
        expand_configurations(&definition).map_err(LoadError::ConfigurationExpansion)?;
    let resolved =
        ResolvedDefinition::resolve(&definition).map_err(LoadError::DefinitionResolution)?;
    Ok(LoadedDefinition {
        files: loader.files,
        definition,
        resolved,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum VisitState {
    Visiting,
    Complete,
}

struct Loader<'a, R> {
    resolver: &'a mut R,
    states: BTreeMap<String, VisitState>,
    stack: Vec<String>,
    files: Vec<SourceFile>,
}

impl<R: SourceResolver> Loader<'_, R> {
    fn visit(&mut self, source: ResolvedSource) -> Result<(), LoadError> {
        match self.states.get(&source.source) {
            Some(VisitState::Complete) => return Ok(()),
            Some(VisitState::Visiting) => return Err(self.cycle(&source.source)),
            None => {}
        }

        self.states
            .insert(source.source.clone(), VisitState::Visiting);
        self.stack.push(source.source.clone());
        let parsed =
            parse(source.source.clone(), &source.text).map_err(|error| LoadError::Parse {
                source: source.source.clone(),
                error,
            })?;

        for requirement in &parsed.requires {
            let required = self
                .resolver
                .resolve(&source.source, &requirement.path)
                .map_err(|message| LoadError::ResolveRequire {
                    source: source.source.clone(),
                    required: requirement.path.clone(),
                    span: requirement.span,
                    message,
                })?;
            self.visit(required)?;
        }

        let popped = self.stack.pop();
        debug_assert_eq!(popped.as_deref(), Some(source.source.as_str()));
        self.states.insert(source.source, VisitState::Complete);
        self.files.push(parsed);
        Ok(())
    }

    fn cycle(&self, source: &str) -> LoadError {
        let start = self
            .stack
            .iter()
            .position(|candidate| candidate == source)
            .expect("a visiting source is on the DFS stack");
        let mut path = self.stack[start..].to_vec();
        path.push(source.to_owned());
        LoadError::CircularRequires(path)
    }
}

fn validate_unique_modules(files: &[SourceFile]) -> Result<(), LoadError> {
    let mut modules = BTreeMap::<&str, &str>::new();
    for file in files {
        for module in &file.modules {
            if let Some(first_source) = modules.insert(&module.name, &file.source) {
                return Err(LoadError::DuplicateModule {
                    name: module.name.clone(),
                    first_source: first_source.to_owned(),
                    second_source: file.source.clone(),
                });
            }
        }
    }
    Ok(())
}
