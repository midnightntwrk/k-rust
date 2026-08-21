//! Stateful KORE module addition and definition selection.

use std::{collections::BTreeMap, error::Error, fmt, sync::Arc};

use k_rust_kore::kore::ast as kore;
use sha2::{Digest, Sha256};

use crate::definition::{BackendDefinition, DefinitionError};

/// A stateful collection of backend definitions derived from one compiled KORE definition.
///
/// Added modules are validated transactionally and cached as independent immutable backend views.
/// Existing views therefore remain valid and the default module is unaffected by an addition.
#[derive(Debug)]
pub struct BackendSession {
    syntax: kore::Definition,
    default_module: String,
    definitions: BTreeMap<String, Arc<BackendDefinition>>,
    added_sources: BTreeMap<String, String>,
    module_aliases: BTreeMap<String, String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SessionError {
    Definition(DefinitionError),
    IntroducesSorts(Vec<String>),
    IntroducesSymbols(Vec<String>),
    DuplicateModuleName(String),
}

impl fmt::Display for SessionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl Error for SessionError {}

impl From<DefinitionError> for SessionError {
    fn from(error: DefinitionError) -> Self {
        Self::Definition(error)
    }
}

impl BackendSession {
    /// Create a lazy session. The selected module is validated when first requested, allowing a
    /// session to select a module that will be supplied immediately through [`Self::add_module`].
    pub fn new(syntax: kore::Definition, default_module: impl Into<String>) -> Self {
        Self {
            syntax,
            default_module: default_module.into(),
            definitions: BTreeMap::new(),
            added_sources: BTreeMap::new(),
            module_aliases: BTreeMap::new(),
        }
    }

    pub fn default_module(&self) -> &str {
        &self.default_module
    }

    /// Obtain an immutable backend view for a module, compiling and caching it on first use.
    pub fn definition(
        &mut self,
        module: Option<&str>,
    ) -> Result<Arc<BackendDefinition>, SessionError> {
        let requested = module.unwrap_or(&self.default_module);
        let canonical = self
            .module_aliases
            .get(requested)
            .map_or(requested, String::as_str);
        if let Some(definition) = self.definitions.get(canonical) {
            return Ok(Arc::clone(definition));
        }
        let definition = Arc::new(BackendDefinition::internalize(&self.syntax, canonical)?);
        self.definitions
            .insert(canonical.to_owned(), Arc::clone(&definition));
        Ok(definition)
    }

    /// Add a rule module and return its canonical `m<sha256>` identifier.
    ///
    /// KORE RPC additions may introduce aliases, axioms, and claims, but not new sorts or symbols.
    /// When `name_as_id` is true, the module's source name also selects the canonical definition.
    pub fn add_module(
        &mut self,
        source: &str,
        mut module: kore::Module,
        name_as_id: bool,
    ) -> Result<String, SessionError> {
        let sorts = module
            .sentences
            .iter()
            .filter_map(|sentence| match sentence {
                kore::Sentence::SortDeclaration { name, .. } => Some(name.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();
        if !sorts.is_empty() {
            return Err(SessionError::IntroducesSorts(sorts));
        }
        let symbols = module
            .sentences
            .iter()
            .filter_map(|sentence| match sentence {
                kore::Sentence::SymbolDeclaration { symbol, .. } => Some(symbol.name.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();
        if !symbols.is_empty() {
            return Err(SessionError::IntroducesSymbols(symbols));
        }

        let source_name = module.name.clone();
        let module_id = module_id(source);
        if name_as_id
            && let Some(existing) = self.module_aliases.get(&source_name)
            && existing != &module_id
        {
            return Err(SessionError::DuplicateModuleName(source_name));
        }
        if let Some(existing) = self.added_sources.get(&module_id) {
            if existing != source {
                return Err(SessionError::DuplicateModuleName(module_id));
            }
            if name_as_id {
                self.module_aliases.insert(source_name, module_id.clone());
            }
            return Ok(module_id);
        }

        for sentence in &mut module.sentences {
            if let kore::Sentence::Import { module, .. } = sentence
                && let Some(canonical) = self.module_aliases.get(module)
            {
                *module = canonical.clone();
            }
        }
        module.name = module_id.clone();
        let mut syntax = self.syntax.clone();
        syntax.modules.push(module);
        let definition = Arc::new(BackendDefinition::internalize(&syntax, &module_id)?);

        self.syntax = syntax;
        self.definitions
            .insert(module_id.clone(), Arc::clone(&definition));
        self.added_sources
            .insert(module_id.clone(), source.to_owned());
        if name_as_id {
            self.module_aliases.insert(source_name, module_id.clone());
        }
        Ok(module_id)
    }
}

fn module_id(source: &str) -> String {
    let digest = Sha256::digest(source.as_bytes());
    let mut id = String::with_capacity(65);
    id.push('m');
    for byte in digest {
        use fmt::Write as _;
        write!(id, "{byte:02x}").expect("writing to a String cannot fail");
    }
    id
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_module};

    use super::*;

    const BASE: &str = r#"
        []
        module BASE
            sort SortState{} [hasDomainValues{}()]
            symbol state{}(SortState{}) : SortState{} [constructor{}()]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(
                    state{}(\dv{SortState{}}("a")), \top{SortState{}}()
                ),
                \and{SortState{}}(
                    state{}(\dv{SortState{}}("d")), \top{SortState{}}()
                )
            ) [label{}("BASE.AD")]
        endmodule []
    "#;

    const ADDED: &str = r#"module NEW
        import BASE []
        axiom{} \rewrites{SortState{}}(
            \and{SortState{}}(
                state{}(\dv{SortState{}}("d")), \top{SortState{}}()
            ),
            \and{SortState{}}(
                state{}(\dv{SortState{}}("e")), \top{SortState{}}()
            )
        ) [label{}("NEW.DE")]
        axiom{} \rewrites{SortState{}}(
            \and{SortState{}}(
                state{}(\dv{SortState{}}("e")), \top{SortState{}}()
            ),
            \and{SortState{}}(
                state{}(\dv{SortState{}}("f")), \top{SortState{}}()
            )
        ) [label{}("NEW.EF")]
    endmodule []"#;

    fn session(default_module: &str) -> BackendSession {
        BackendSession::new(
            parse_definition(BASE).expect("base definition should parse"),
            default_module,
        )
    }

    fn rule_count(definition: &BackendDefinition) -> usize {
        definition
            .rewrite_theory
            .values()
            .flat_map(BTreeMap::values)
            .map(Vec::len)
            .sum()
    }

    #[test]
    fn added_module_is_idempotent_selectable_and_does_not_change_the_default() {
        let module = parse_module(ADDED).expect("added module should parse");
        let mut session = session("BASE");
        let default = session.definition(None).unwrap();
        assert_eq!(rule_count(&default), 1);

        let id = session.add_module(ADDED, module.clone(), true).unwrap();
        assert_eq!(
            id,
            "m662deaa65f16b563cbc774410183536650dc7bcf8f482a131b4fa8eedf5f4809"
        );
        assert_eq!(session.add_module(ADDED, module, true).unwrap(), id);
        assert_eq!(rule_count(&session.definition(Some("NEW")).unwrap()), 3);
        assert_eq!(rule_count(&session.definition(Some(&id)).unwrap()), 3);
        assert_eq!(rule_count(&session.definition(None).unwrap()), 1);
    }

    #[test]
    fn selected_module_may_be_added_after_session_creation() {
        let mut session = session("NEW");
        session
            .add_module(ADDED, parse_module(ADDED).unwrap(), true)
            .unwrap();
        assert_eq!(rule_count(&session.definition(None).unwrap()), 3);
    }

    #[test]
    fn rejects_new_sorts_symbols_and_reused_source_names() {
        let mut session = session("BASE");
        let sort_source = "module SORTS sort SortNew{} [] endmodule []";
        assert_eq!(
            session
                .add_module(sort_source, parse_module(sort_source).unwrap(), false)
                .unwrap_err(),
            SessionError::IntroducesSorts(vec!["SortNew".into()])
        );
        let symbol_source = "module SYMBOLS symbol new{}() : SortState{} [] endmodule []";
        assert_eq!(
            session
                .add_module(symbol_source, parse_module(symbol_source).unwrap(), false)
                .unwrap_err(),
            SessionError::IntroducesSymbols(vec!["new".into()])
        );

        session
            .add_module(ADDED, parse_module(ADDED).unwrap(), true)
            .unwrap();
        let replacement = ADDED.replace("NEW.DE", "NEW.REPLACEMENT");
        assert_eq!(
            session
                .add_module(&replacement, parse_module(&replacement).unwrap(), true)
                .unwrap_err(),
            SessionError::DuplicateModuleName("NEW".into())
        );
    }

    #[test]
    fn rewrites_imports_through_prior_name_aliases() {
        let mut session = session("BASE");
        session
            .add_module(ADDED, parse_module(ADDED).unwrap(), true)
            .unwrap();
        let extension = r#"module EXTENSION
            import NEW []
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(
                    state{}(\dv{SortState{}}("f")), \top{SortState{}}()
                ),
                \and{SortState{}}(
                    state{}(\dv{SortState{}}("g")), \top{SortState{}}()
                )
            ) [label{}("EXTENSION.FG")]
        endmodule []"#;
        session
            .add_module(extension, parse_module(extension).unwrap(), true)
            .unwrap();

        assert_eq!(
            rule_count(&session.definition(Some("EXTENSION")).unwrap()),
            4
        );
    }
}
