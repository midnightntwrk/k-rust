//! Recursive, host-independent loading of outer-syntax source graphs.

use std::{collections::BTreeMap, error::Error, fmt};

use crate::{
    definition::{
        ConfigurationError, Definition, FlatImport, ResolveError, ResolvedDefinition, Sentence,
        apply_sort_synonyms, expand_configurations,
    },
    diagnostic::Diagnostic,
    inner::{ConfigError, RuleError, resolve_configuration_bubbles, resolve_rule_bubbles},
};

use super::{MarkdownError, extract_fenced_k_code};
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoadOptions {
    pub markdown_selector: String,
    /// Additional roots loaded before the entry source, such as Java's implicit prelude.
    pub implicit_sources: Vec<ResolvedSource>,
    /// Module attributes excluded by the selected backend before configuration and rule parsing.
    pub excluded_module_attributes: Vec<String>,
    /// Module that owns the configuration when it differs from the selected main module.
    pub configuration_module: Option<String>,
}

impl Default for LoadOptions {
    fn default() -> Self {
        Self {
            markdown_selector: "k".into(),
            implicit_sources: Vec::new(),
            excluded_module_attributes: Vec::new(),
            configuration_module: None,
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
    Markdown {
        source: String,
        error: MarkdownError,
    },
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
    DuplicateModule {
        name: String,
        first_source: String,
        second_source: String,
    },
    ExcludedMainModule {
        module: String,
        attribute: String,
    },
    MissingConfigurationModule(String),
    SourceDiagnostics(Vec<Diagnostic>),
    DefinitionResolution(ResolveError),
    Configuration(ConfigError),
    ConfigurationExpansion(ConfigurationError),
    RuleParsing(RuleError),
}

impl fmt::Display for LoadError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Markdown { source, error } => {
                write!(
                    formatter,
                    "failed to extract K code from {source:?}: {error}"
                )
            }
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
            Self::DuplicateModule {
                name,
                first_source,
                second_source,
            } => write!(
                formatter,
                "module {name:?} is declared by both {first_source:?} and {second_source:?}"
            ),
            Self::ExcludedMainModule { module, attribute } => {
                write!(
                    formatter,
                    "main module {module} has excluded attribute [{attribute}]"
                )
            }
            Self::MissingConfigurationModule(module) => {
                write!(
                    formatter,
                    "definition has no configuration module `{module}`"
                )
            }
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
            Self::RuleParsing(error) => error.fmt(formatter),
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
    load_with_options(entry, main_module, resolver, &LoadOptions::default())
}

pub fn load_with_options(
    entry: ResolvedSource,
    main_module: impl Into<String>,
    resolver: &mut impl SourceResolver,
    options: &LoadOptions,
) -> Result<LoadedDefinition, LoadError> {
    let mut loader = Loader {
        resolver,
        options,
        states: BTreeMap::new(),
        files: Vec::new(),
    };
    for source in &options.implicit_sources {
        loader.visit(source.clone())?;
    }
    loader.visit(entry)?;
    validate_unique_modules(&loader.files)?;

    let definition =
        lower_files(&loader.files, main_module).map_err(LoadError::SourceDiagnostics)?;
    let definition = apply_sort_synonyms(&definition).map_err(LoadError::DefinitionResolution)?;
    let definition =
        exclude_modules_by_attributes(definition, &options.excluded_module_attributes)?;
    let definition =
        add_implicit_configuration_imports(definition, options.configuration_module.as_deref())?;
    let definition =
        resolve_configuration_bubbles(&definition).map_err(LoadError::Configuration)?;
    let definition =
        expand_configurations(&definition).map_err(LoadError::ConfigurationExpansion)?;
    let definition = resolve_rule_bubbles(&definition).map_err(LoadError::RuleParsing)?;
    let resolved =
        ResolvedDefinition::resolve(&definition).map_err(LoadError::DefinitionResolution)?;
    Ok(LoadedDefinition {
        files: loader.files,
        definition,
        resolved,
    })
}

fn exclude_modules_by_attributes(
    mut definition: Definition,
    excluded_attributes: &[String],
) -> Result<Definition, LoadError> {
    for attribute in excluded_attributes {
        if definition
            .main_module()
            .is_some_and(|module| module.attributes.get(attribute).is_some())
        {
            return Err(LoadError::ExcludedMainModule {
                module: definition.main_module.clone(),
                attribute: attribute.clone(),
            });
        }
    }
    let excluded_names = definition
        .modules
        .iter()
        .filter(|module| {
            excluded_attributes
                .iter()
                .any(|attribute| module.attributes.get(attribute).is_some())
        })
        .map(|module| module.name.clone())
        .collect::<std::collections::BTreeSet<_>>();
    definition
        .modules
        .retain(|module| !excluded_names.contains(&module.name));
    for module in &mut definition.modules {
        module
            .imports
            .retain(|import| !excluded_names.contains(&import.name));
    }
    Ok(definition)
}

fn add_implicit_configuration_imports(
    mut definition: Definition,
    configuration_module: Option<&str>,
) -> Result<Definition, LoadError> {
    if let Some(configuration_module) = configuration_module
        && !definition
            .modules
            .iter()
            .any(|module| module.name == configuration_module)
    {
        return Err(LoadError::MissingConfigurationModule(
            configuration_module.into(),
        ));
    }
    let has_default = definition
        .modules
        .iter()
        .any(|module| module.name == "DEFAULT-CONFIGURATION");
    let has_map = definition.modules.iter().any(|module| module.name == "MAP");

    if has_default {
        let resolved =
            ResolvedDefinition::resolve(&definition).map_err(LoadError::DefinitionResolution)?;
        let configuration_module = configuration_module.unwrap_or(&definition.main_module);
        let configuration_module_id = resolved
            .module_id(configuration_module)
            .ok_or_else(|| LoadError::MissingConfigurationModule(configuration_module.into()))?;
        let has_visible_configuration = resolved
            .sentences(configuration_module_id)
            .into_iter()
            .any(is_configuration_sentence);
        if !has_visible_configuration {
            let module = definition
                .modules
                .iter_mut()
                .find(|module| module.name == configuration_module)
                .expect("the resolved configuration module exists");
            if !module
                .imports
                .iter()
                .any(|import| import.name == "DEFAULT-CONFIGURATION")
            {
                module.imports.push(FlatImport {
                    name: "DEFAULT-CONFIGURATION".into(),
                    public: true,
                });
            }
        }
    }

    if has_map {
        for module in &mut definition.modules {
            let has_local_configuration =
                module.local_sentences.iter().any(is_configuration_sentence);
            if has_local_configuration && !module.imports.iter().any(|import| import.name == "MAP")
            {
                module.imports.push(FlatImport {
                    name: "MAP".into(),
                    public: true,
                });
            }
        }
    }

    Ok(definition)
}

fn is_configuration_sentence(sentence: &Sentence) -> bool {
    matches!(sentence, Sentence::Configuration { .. })
        || matches!(sentence, Sentence::Bubble { sentence_type, .. } if sentence_type == "config")
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum VisitState {
    Visiting,
    Complete,
}

struct Loader<'a, R> {
    resolver: &'a mut R,
    options: &'a LoadOptions,
    states: BTreeMap<String, VisitState>,
    files: Vec<SourceFile>,
}

impl<R: SourceResolver> Loader<'_, R> {
    fn visit(&mut self, source: ResolvedSource) -> Result<(), LoadError> {
        match self.states.get(&source.source) {
            Some(VisitState::Complete | VisitState::Visiting) => return Ok(()),
            None => {}
        }

        self.states
            .insert(source.source.clone(), VisitState::Visiting);
        let text = if source.source.ends_with(".md") {
            extract_fenced_k_code(&source.text, &self.options.markdown_selector).map_err(
                |error| LoadError::Markdown {
                    source: source.source.clone(),
                    error,
                },
            )?
        } else {
            source.text
        };
        let parsed = parse(source.source.clone(), &text).map_err(|error| LoadError::Parse {
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

        self.states.insert(source.source, VisitState::Complete);
        self.files.push(parsed);
        Ok(())
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        definition::{Attributes, FlatImport, FlatModule},
        kast::{Sort, Term},
    };

    fn configuration_fixture(configuration: Sentence) -> Definition {
        Definition {
            main_module: "MAIN".into(),
            modules: vec![
                FlatModule {
                    name: "MAP".into(),
                    imports: vec![],
                    local_sentences: vec![],
                    attributes: Attributes::default(),
                },
                FlatModule {
                    name: "DEFAULT-CONFIGURATION".into(),
                    imports: vec![],
                    local_sentences: vec![],
                    attributes: Attributes::default(),
                },
                FlatModule {
                    name: "MAIN".into(),
                    imports: vec![],
                    local_sentences: vec![configuration],
                    attributes: Attributes::default(),
                },
            ],
            attributes: Attributes::default(),
        }
    }

    fn assert_configuration_controls_implicit_imports(configuration: Sentence) {
        let transformed =
            add_implicit_configuration_imports(configuration_fixture(configuration.clone()), None)
                .expect("the fixture is a valid definition");
        let main = transformed.main_module().expect("MAIN exists");

        assert_eq!(main.local_sentences, [configuration]);
        assert!(
            !main
                .imports
                .iter()
                .any(|import| import.name == "DEFAULT-CONFIGURATION"),
            "a visible configuration must suppress the default configuration"
        );
        assert!(
            main.imports
                .iter()
                .any(|import| import.name == "MAP" && import.public),
            "a local configuration must receive a public MAP import"
        );
    }

    #[test]
    fn structured_configuration_controls_implicit_imports() {
        assert_configuration_controls_implicit_imports(Sentence::Configuration {
            body: Term::variable("CONFIG"),
            ensures: Term::Token {
                token: "true".into(),
                sort: Sort::new("Bool"),
            },
            attributes: Attributes::default(),
        });
    }

    #[test]
    fn configuration_bubble_controls_implicit_imports() {
        assert_configuration_controls_implicit_imports(Sentence::Bubble {
            sentence_type: "config".into(),
            contents: "<k> $PGM:K </k>".into(),
            attributes: Attributes::default(),
        });
    }

    #[test]
    fn imported_configurations_suppress_default_but_do_not_import_map() {
        let configuration = Sentence::Configuration {
            body: Term::variable("CONFIG"),
            ensures: Term::Token {
                token: "true".into(),
                sort: Sort::new("Bool"),
            },
            attributes: Attributes::default(),
        };
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![
                FlatModule {
                    name: "MAP".into(),
                    imports: vec![],
                    local_sentences: vec![],
                    attributes: Attributes::default(),
                },
                FlatModule {
                    name: "DEFAULT-CONFIGURATION".into(),
                    imports: vec![],
                    local_sentences: vec![],
                    attributes: Attributes::default(),
                },
                FlatModule {
                    name: "HELPER".into(),
                    imports: vec![],
                    local_sentences: vec![configuration],
                    attributes: Attributes::default(),
                },
                FlatModule {
                    name: "MAIN".into(),
                    imports: vec![FlatImport {
                        name: "HELPER".into(),
                        public: true,
                    }],
                    local_sentences: vec![],
                    attributes: Attributes::default(),
                },
            ],
            attributes: Attributes::default(),
        };

        let transformed = add_implicit_configuration_imports(definition, None).unwrap();
        let main = transformed.main_module().unwrap();
        // DEFAULT-CONFIGURATION observes transitively visible sentences, whereas MAP is attached
        // only to the module that locally owns a configuration. This asymmetry is intentional.
        assert!(
            !main
                .imports
                .iter()
                .any(|import| { matches!(import.name.as_str(), "DEFAULT-CONFIGURATION" | "MAP") })
        );
        let helper = transformed
            .modules
            .iter()
            .find(|module| module.name == "HELPER")
            .unwrap();
        assert!(
            helper
                .imports
                .iter()
                .any(|import| import.name == "MAP" && import.public)
        );
    }
}
