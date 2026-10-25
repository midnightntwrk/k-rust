//! Definitions the values tests resolve sorts against: the fixtures of `tests/support`
//! (`crate::support`), each with its backend definition, once per test binary.
//!
//! - IMP (`tests/data/imp/imp.k`);
//! - LEDGER (`tests/data/ledger/ledger.k`): the user record sorts `Tx` and `Account`;
//! - VALUES (`tests/data/values/values.k`): `MInt`, a renamed hooked Int sort, records, recursive
//!   and subsorted data sorts, and one configuration variable per hole sort, so that a value can
//!   be read back from an assembled configuration.

use std::{collections::BTreeMap, sync::OnceLock};

use k_rust::{
    backend::Backend,
    definition::Definition,
    k_rust_backend::definition::BackendDefinition,
    kast::Sort as KastSort,
    kompile::{CompiledKoreArtifacts, ConfigurationAssembler, ProgramGrammar},
    kore::ast::Pattern,
};

use super::text::TextSyntax;
use crate::support::{self, Fixture};

/// A fixture compiled in-process, with its backend definition on `krun`'s route.
pub(super) struct TestDefinition {
    pub main_module: &'static str,
    pub syntax_module: String,
    pub frontend: &'static Definition,
    pub grammar: &'static ProgramGrammar,
    pub artifacts: &'static CompiledKoreArtifacts,
    pub backend: BackendDefinition,
}

impl TestDefinition {
    fn of(fixture: &'static Fixture) -> Self {
        let compiled = fixture.compiled();
        let backend = Backend::internalize_source_definition(
            &compiled.kore,
            fixture.main_module,
            &compiled.artifacts.execution_rewrite_order,
        )
        .unwrap_or_else(|error| panic!("{} does not internalize: {error:?}", fixture.file));
        Self {
            main_module: fixture.main_module,
            syntax_module: compiled.syntax_module.clone(),
            frontend: compiled.frontend(),
            grammar: &compiled.grammar,
            artifacts: &compiled.artifacts,
            backend,
        }
    }

    /// The K-text syntax of this definition, with `excluded` sorts left out of data tables.
    pub fn text_syntax(&self, excluded: &[&str]) -> TextSyntax {
        TextSyntax::new(
            self.frontend,
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
            self.grammar,
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
    IMP.get_or_init(|| TestDefinition::of(&support::IMP))
}

/// VALUES, compiled once per test binary.
pub(super) fn values() -> &'static TestDefinition {
    static VALUES: OnceLock<TestDefinition> = OnceLock::new();
    VALUES.get_or_init(|| TestDefinition::of(&support::VALUES))
}

/// LEDGER, compiled once per test binary.
pub(super) fn ledger() -> &'static TestDefinition {
    static LEDGER: OnceLock<TestDefinition> = OnceLock::new();
    LEDGER.get_or_init(|| TestDefinition::of(&support::LEDGER))
}
