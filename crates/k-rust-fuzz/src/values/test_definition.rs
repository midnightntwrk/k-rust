//! Definitions the values tests resolve sorts against, compiled in-process in the portable build
//! the way `tests/support` compiles the fixtures (`load_for_compilation` with the embedded
//! prelude, then `compile_loaded_definition`), once per test binary.
//!
//! - IMP (`tests/data/imp/imp.k`, FZ-FIX);
//! - LEDGER (`tests/data/ledger/ledger.k`, FZ-FIX): the user record sorts `Tx` and `Account`;
//! - VALUES (`tests/data/values/values.k`): `MInt`, a renamed hooked Int sort, records, recursive
//!   and subsorted data sorts, and one configuration variable per hole sort, so that a value can
//!   be read back from an assembled configuration.

use std::{collections::BTreeMap, sync::OnceLock};

use k_rust::{
    backend::Backend,
    builtin::embedded,
    definition::Definition,
    k_rust_backend::definition::BackendDefinition,
    kast::Sort as KastSort,
    kompile::{
        CompilationBackend, CompileOptions, CompiledKoreArtifacts, ConfigurationAssembler,
        ProgramGrammar, compile_loaded_definition,
    },
    kore::{ast::Pattern, parser::parse_definition},
    outer::{LoadOptions, ResolvedSource, load_for_compilation},
};

use super::text::TextSyntax;

/// A definition compiled in-process.
pub(super) struct TestDefinition {
    pub main_module: &'static str,
    pub syntax_module: String,
    pub frontend: Definition,
    pub grammar: ProgramGrammar,
    pub artifacts: CompiledKoreArtifacts,
    pub backend: BackendDefinition,
}

impl TestDefinition {
    fn compile(file: &str, source: &str, main_module: &'static str) -> Self {
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let options = LoadOptions {
            implicit_sources: vec![embedded("prelude.md").expect("the prelude is embedded")],
            ..CompilationBackend::Rust.load_options()
        };
        let (loaded, syntax_module) = load_for_compilation(
            ResolvedSource::new(file, source),
            main_module,
            None,
            &mut resolver,
            &options,
        )
        .unwrap_or_else(|error| panic!("{file} does not load: {error:?}"));
        let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
            .unwrap_or_else(|error| panic!("{file} does not compile: {error}"));
        assert!(
            artifacts.diagnostics.is_empty(),
            "{file} compiles with diagnostics: {:#?}",
            artifacts.diagnostics
        );
        let frontend = loaded.into_definition();
        let grammar = ProgramGrammar::new(&frontend)
            .unwrap_or_else(|error| panic!("{file} has no program grammar: {error}"));
        let kore = parse_definition(&artifacts.definition_kore)
            .unwrap_or_else(|error| panic!("{file}'s KORE does not parse: {error}"));
        let backend = Backend::internalize_source_definition(
            &kore,
            main_module,
            &artifacts.execution_rewrite_order,
        )
        .unwrap_or_else(|error| panic!("{file} does not internalize: {error:?}"));
        Self {
            main_module,
            syntax_module,
            frontend,
            grammar,
            artifacts,
            backend,
        }
    }

    /// The K-text syntax of this definition, with `excluded` sorts left out of data tables.
    pub fn text_syntax(&self, excluded: &[&str]) -> TextSyntax {
        TextSyntax::new(
            &self.frontend,
            self.main_module,
            &self.artifacts.syntax_definition_kore,
            &self.artifacts.macros_kore,
            excluded.iter().map(|sort| (*sort).to_owned()),
        )
        .unwrap_or_else(|error| panic!("no text syntax: {error}"))
    }

    /// The configuration with `program` at start sort `Pgm` and `bindings` (name without `$`,
    /// text), assembled by the frontend's public assembler as krun assembles it.
    pub fn assemble(&self, program: &str, bindings: &[(&str, &str)]) -> Result<Pattern, String> {
        let variables: &BTreeMap<String, KastSort> = &self.artifacts.configuration_variables;
        let mut assembler = ConfigurationAssembler::new(
            &self.grammar,
            self.main_module,
            self.syntax_module.clone(),
            variables,
        );
        assembler
            .program(&KastSort::new("Pgm"), program)
            .map_err(|error| format!("{error:?}"))?;
        for (name, text) in bindings {
            assembler
                .bind(name, text)
                .map_err(|error| format!("${name} = {text}: {error:?}"))?;
        }
        assembler.finish().map_err(|error| format!("{error:?}"))
    }
}

/// IMP, compiled once per test binary.
pub(super) fn imp() -> &'static TestDefinition {
    static IMP: OnceLock<TestDefinition> = OnceLock::new();
    IMP.get_or_init(|| {
        TestDefinition::compile(
            "imp/imp.k",
            include_str!("../../tests/data/imp/imp.k"),
            "IMP",
        )
    })
}

/// VALUES, compiled once per test binary.
pub(super) fn values() -> &'static TestDefinition {
    static VALUES: OnceLock<TestDefinition> = OnceLock::new();
    VALUES.get_or_init(|| {
        TestDefinition::compile(
            "values/values.k",
            include_str!("../../tests/data/values/values.k"),
            "VALUES",
        )
    })
}

/// LEDGER, compiled once per test binary.
pub(super) fn ledger() -> &'static TestDefinition {
    static LEDGER: OnceLock<TestDefinition> = OnceLock::new();
    LEDGER.get_or_init(|| {
        TestDefinition::compile(
            "ledger/ledger.k",
            include_str!("../../tests/data/ledger/ledger.k"),
            "LEDGER",
        )
    })
}
