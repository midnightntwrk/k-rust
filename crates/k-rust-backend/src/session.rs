//! Stateful KORE module addition and definition selection.

#![deny(clippy::wildcard_enum_match_arm)]

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt,
    sync::{Arc, Mutex},
};

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
    definitions: Mutex<BTreeMap<String, Arc<BackendDefinition>>>,
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
            definitions: Mutex::new(BTreeMap::new()),
            added_sources: BTreeMap::new(),
            module_aliases: BTreeMap::new(),
        }
    }

    /// Seed a session with an already internalized definition.
    pub fn with_definition(definition: BackendDefinition) -> Self {
        let default_module = definition.main_module().to_string();
        let mut definitions = BTreeMap::new();
        definitions.insert(default_module.clone(), Arc::new(definition));
        Self {
            syntax: kore::Definition {
                attributes: Default::default(),
                modules: Vec::new(),
            },
            default_module,
            definitions: Mutex::new(definitions),
            added_sources: BTreeMap::new(),
            module_aliases: BTreeMap::new(),
        }
    }

    pub fn default_module(&self) -> &str {
        &self.default_module
    }

    /// Obtain an immutable backend view for a module, compiling and caching it on first use.
    pub fn definition(&self, module: Option<&str>) -> Result<Arc<BackendDefinition>, SessionError> {
        let requested = module.unwrap_or(&self.default_module);
        let canonical = self
            .module_aliases
            .get(requested)
            .map_or(requested, String::as_str);
        let mut definitions = self
            .definitions
            .lock()
            .expect("definition cache lock poisoned");
        if let Some(definition) = definitions.get(canonical) {
            return Ok(Arc::clone(definition));
        }
        let definition = Arc::new(BackendDefinition::internalize_with_added(
            &self.syntax,
            canonical,
            &self.added_modules(),
        )?);
        definitions.insert(canonical.to_owned(), Arc::clone(&definition));
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
                kore::Sentence::Import { .. }
                | kore::Sentence::SymbolDeclaration { .. }
                | kore::Sentence::AliasDeclaration { .. }
                | kore::Sentence::Axiom { .. }
                | kore::Sentence::Claim { .. } => None,
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
                kore::Sentence::Import { .. }
                | kore::Sentence::SortDeclaration { .. }
                | kore::Sentence::AliasDeclaration { .. }
                | kore::Sentence::Axiom { .. }
                | kore::Sentence::Claim { .. } => None,
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
        if name_as_id
            && source_name != module_id
            && self
                .syntax
                .modules
                .iter()
                .any(|module| module.name == source_name)
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
        if self.module_aliases.contains_key(&module_id)
            || self
                .syntax
                .modules
                .iter()
                .any(|module| module.name == module_id)
        {
            return Err(SessionError::DuplicateModuleName(module_id));
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
        // The added module is budgeted for what it supplies, not for the definition it extends
        // (`BackendDefinition::internalize_with_added`).
        let mut added = self.added_modules();
        added.insert(&module_id);
        let definition = Arc::new(BackendDefinition::internalize_with_added(
            &syntax, &module_id, &added,
        )?);

        self.syntax = syntax;
        self.definitions
            .get_mut()
            .expect("definition cache lock poisoned")
            .insert(module_id.clone(), Arc::clone(&definition));
        self.added_sources
            .insert(module_id.clone(), source.to_owned());
        if name_as_id {
            self.module_aliases.insert(source_name, module_id.clone());
        }
        Ok(module_id)
    }

    /// The names, in `syntax`, of the modules added through [`Self::add_module`], each supplied
    /// by an operation of its own after the definition the session was created with.
    fn added_modules(&self) -> BTreeSet<&str> {
        self.added_sources.keys().map(String::as_str).collect()
    }
}

/// Canonical identifier of an RPC-added module, derived from its exact source bytes.
pub fn module_id(source: &str) -> String {
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
            sort SortToken{} [hasDomainValues{}()]
            sort SortState{} []
            symbol state{}(SortToken{}) : SortState{} [constructor{}()]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(
                    state{}(\dv{SortToken{}}("a")), \top{SortState{}}()
                ),
                \and{SortState{}}(
                    state{}(\dv{SortToken{}}("d")), \top{SortState{}}()
                )
            ) [label{}("BASE.AD")]
        endmodule []
    "#;

    const ADDED: &str = r#"module NEW
        import BASE []
        axiom{} \rewrites{SortState{}}(
            \and{SortState{}}(
                state{}(\dv{SortToken{}}("d")), \top{SortState{}}()
            ),
            \and{SortState{}}(
                state{}(\dv{SortToken{}}("e")), \top{SortState{}}()
            )
        ) [label{}("NEW.DE")]
        axiom{} \rewrites{SortState{}}(
            \and{SortState{}}(
                state{}(\dv{SortToken{}}("e")), \top{SortState{}}()
            ),
            \and{SortState{}}(
                state{}(\dv{SortToken{}}("f")), \top{SortState{}}()
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
            .rewrite_theory()
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
            "m1c55d05826f1595ff6eb2663d76f0cb699e7d6c28a2b9dfeb4409202e43841a6"
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
    fn rejects_collisions_between_canonical_ids_and_source_name_aliases() {
        let second_source = "module SECOND import BASE [] endmodule []";
        let second_id = module_id(second_source);
        let first_source = format!("module {second_id} import BASE [] endmodule []");
        let mut first_session = session("BASE");
        first_session
            .add_module(&first_source, parse_module(&first_source).unwrap(), true)
            .unwrap();
        assert_eq!(
            first_session
                .add_module(second_source, parse_module(second_source).unwrap(), false)
                .unwrap_err(),
            SessionError::DuplicateModuleName(second_id)
        );

        let first_source = "module FIRST import BASE [] endmodule []";
        let first_id = module_id(first_source);
        let second_source = format!("module {first_id} import BASE [] endmodule []");
        let mut second_session = session("BASE");
        second_session
            .add_module(first_source, parse_module(first_source).unwrap(), false)
            .unwrap();
        assert_eq!(
            second_session
                .add_module(&second_source, parse_module(&second_source).unwrap(), true)
                .unwrap_err(),
            SessionError::DuplicateModuleName(first_id)
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
                    state{}(\dv{SortToken{}}("f")), \top{SortState{}}()
                ),
                \and{SortState{}}(
                    state{}(\dv{SortToken{}}("g")), \top{SortState{}}()
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
    /// The disjuncts of `big`, a closed nullary alias of a condition, of about 360,000 units,
    /// declared by the base of [`alias_session`].
    const BIG_DISJUNCTS: usize = 40_000;

    /// A rewrite axiom of sort `S` labelled `label` that applies `big` once, as a condition of
    /// its left-hand side.
    fn applying_big(label: &str) -> String {
        format!(
            "    axiom{{}} \\rewrites{{S{{}}}}(\\and{{S{{}}}}(big{{}}(), pair{{}}(X:S{{}}, a{{}}())), a{{}}()) [label{{}}(\"{label}\")]\n"
        )
    }

    /// A session over module `BASE`, which declares `big` and has `rules` axioms applying it.
    fn alias_session(rules: usize) -> BackendSession {
        let mut base = String::from(
            "[]\nmodule BASE\n    sort S{} []\n    symbol pair{}(S{}, S{}) : S{} [constructor{}()]\n    symbol a{}() : S{} [constructor{}()]\n",
        );
        let body = vec![r"\equals{S{}, S{}}(a{}(), a{}())"; BIG_DISJUNCTS].join(", ");
        base.push_str(&format!(
            "    alias big{{}}() : S{{}} where big{{}}() := \\or{{S{{}}}}({body}) []\n"
        ));
        for rule in 0..rules {
            base.push_str(&applying_big(&format!("BASE.R{rule}")));
        }
        base.push_str("endmodule []\n");
        BackendSession::new(parse_definition(&base).unwrap(), "BASE")
    }

    /// A module `name` importing `import` with `rules` axioms applying `big`.
    fn module_applying_big(name: &str, import: &str, rules: usize) -> String {
        let mut module = format!("module {name}\n    import {import} []\n");
        for rule in 0..rules {
            module.push_str(&applying_big(&format!("{name}.R{rule}")));
        }
        module.push_str("endmodule []");
        module
    }

    fn add(session: &mut BackendSession, source: &str) -> Result<String, SessionError> {
        session.add_module(source, parse_module(source).unwrap(), true)
    }

    /// A module of a few kilobytes added to a session is budgeted for what it supplies: only the
    /// floor `UNFOLDING_LIMIT`, however large the definition it extends. A chain of 18 aliases,
    /// each applying the next twice, applied twice by one axiom, adds about 7.9 million units, so
    /// it is refused before it is built, although 32 times the base's size (about 11.5 million)
    /// would cover it.
    #[test]
    fn a_small_added_module_gets_only_the_floor_whatever_the_definition_it_extends() {
        let mut session = alias_session(0);
        session.definition(None).expect("the base loads");
        const LENGTH: usize = 18;
        let mut added = String::from("module NEW\n    import BASE []\n");
        for index in 0..LENGTH {
            let body = if index + 1 == LENGTH {
                "pair{}(X:S{}, X:S{})".to_owned()
            } else {
                let next = index + 1;
                format!("pair{{}}(al{next}{{}}(X:S{{}}), al{next}{{}}(X:S{{}}))")
            };
            added.push_str(&format!(
                "    alias al{index}{{}}(S{{}}) : S{{}} where al{index}{{}}(X:S{{}}) := {body} []\n"
            ));
        }
        added.push_str("    axiom{} \\rewrites{S{}}(\\and{S{}}(\\not{S{}}(pair{}(al0{}(X:S{}), al0{}(X:S{}))), pair{}(X:S{}, a{}())), a{}()) [label{}(\"NEW.R\")]\n");
        added.push_str("endmodule []");
        assert!(added.len() < 2_000);

        match add(&mut session, &added) {
            Err(SessionError::Definition(DefinitionError::AliasUnfoldingTooLarge {
                added,
                available,
            })) => {
                assert!(added > available);
                assert_eq!(available, crate::alias::UNFOLDING_LIMIT);
            }
            result => {
                panic!("a 2 KB module with an exponential unfolding was not refused: {result:?}")
            }
        }
    }

    /// The axioms of the definition a session was created with are charged to that definition's
    /// own budget, not to a module added to it: a small module extends a base whose own unfolding
    /// (12 copies of `big`, about 4.3 million units) exceeds the floor.
    #[test]
    fn a_small_module_extends_a_definition_whose_unfolding_exceeds_the_floor() {
        let mut session = alias_session(12);
        assert_eq!(rule_count(&session.definition(None).unwrap()), 12);
        let id = add(&mut session, &module_applying_big("NEW", "BASE", 1)).unwrap();
        assert_eq!(rule_count(&session.definition(Some(&id)).unwrap()), 13);
    }

    /// Each added module keeps a budget of its own, also when a later addition imports it: two
    /// modules that each apply `big` 7 times (about 2.5 million units each, more than the floor
    /// together) are both added, while one that applies it 12 times, though `big` is the base's,
    /// is refused, since what it makes the backend build is out of proportion to what it sent.
    #[test]
    fn each_added_module_is_budgeted_for_its_own_axioms() {
        let mut session = alias_session(0);
        add(&mut session, &module_applying_big("FIRST", "BASE", 7)).unwrap();
        let second = add(&mut session, &module_applying_big("SECOND", "FIRST", 7)).unwrap();
        assert_eq!(rule_count(&session.definition(Some(&second)).unwrap()), 14);

        match add(&mut session, &module_applying_big("THIRD", "BASE", 12)) {
            Err(SessionError::Definition(DefinitionError::AliasUnfoldingTooLarge {
                available,
                ..
            })) => assert!(available <= crate::alias::UNFOLDING_LIMIT),
            result => panic!("12 copies of the base's alias were not refused: {result:?}"),
        }
    }
}
