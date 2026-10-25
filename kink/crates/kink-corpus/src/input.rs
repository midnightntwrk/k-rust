//! Program parsing and configuration assembly through k-rust's concrete-input API.

use std::fmt;

use k_rust::{
    kast::Sort,
    kompile::{
        CompileOptions,
        initial_configuration::{
            ConfigurationAssembler, ConfigurationError, ProgramGrammar, program_start_position,
        },
    },
    kore::ast::Pattern,
};
use kink_native::{NativeValidator, ValidatedDefinition};

use crate::resolver::{LoadedSource, read_under_root};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProgramSource {
    Text(String),
    File(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TestInputSpec {
    pub program: ProgramSource,
    pub start_sort: Option<String>,
    pub variables: Vec<(String, String)>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum InputError {
    Parse(String),
    Assemble(String),
    Streams(String),
    MissingVariable(String),
}

impl fmt::Display for InputError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse(message)
            | Self::Assemble(message)
            | Self::Streams(message)
            | Self::MissingVariable(message) => f.write_str(message),
        }
    }
}
impl std::error::Error for InputError {}

/// Parse the program and declared variable texts, using deterministic, empty stream defaults.
///
/// It compiles `loaded`'s baseline for its configuration variables; a caller that already holds
/// that compile passes it to [`assemble_input_with`] instead, which gives the same configuration
/// without compiling again.
pub fn assemble_input(loaded: &LoadedSource, spec: &TestInputSpec) -> Result<Pattern, InputError> {
    assemble_input_with(loaded, None, spec)
}

/// [`assemble_input`] with `compiled`, the caller's compile of `loaded`'s baseline under
/// `CompileOptions::default()` (re-pin L1-4): a compile of the same loaded definition under the
/// same options, which k-rust's compile determinism makes the compile `assemble_input` would make
/// (the premise of `NativeValidator::compile_baseline`'s memo and of every kill). Each program
/// input then costs no compile: before L1-4 every program bound a fresh validator and compiled the
/// baseline again (`examples/imp` cold: 7 of the run's 9 baseline compiles, 1.6 s of 14.8 s).
///
/// The caller must pass the compile of the same loaded value (`loaded.baseline`, bound under
/// `CompileOptions::default()`); every caller does (kink-flow's admission, kink-corpus admission
/// and `Store::rebuild_tests`). The guard below is structural only: it refuses a `compiled` whose
/// options differ or whose source definition is unequal under k-rust's definition equality, and
/// then compiles the baseline here, as without it. That equality ignores term metadata (spans,
/// production identity, explicit compiler sorts, origins), so a compile of a definition that
/// differs from `loaded`'s only there passes the guard (re-pin L1-4 fix 1, review D7).
pub fn assemble_input_with(
    loaded: &LoadedSource,
    compiled: Option<&ValidatedDefinition>,
    spec: &TestInputSpec,
) -> Result<Pattern, InputError> {
    let text = match &spec.program {
        ProgramSource::Text(text) => text.clone(),
        ProgramSource::File(name) => {
            let (_, bytes) = read_under_root(&loaded.root, name)
                .map_err(|e| InputError::Parse(e.to_string()))?;
            String::from_utf8(bytes).map_err(|e| InputError::Parse(e.to_string()))?
        }
    };
    let fresh;
    let compiled = match compiled {
        Some(compiled)
            if *compiled.compile_options() == CompileOptions::default()
                && compiled.definition() == loaded.baseline.definition() =>
        {
            compiled
        }
        _ => {
            fresh = NativeValidator::bind(loaded.baseline.clone(), CompileOptions::default())
                .compile_baseline()
                .map_err(|e| InputError::Assemble(e.to_string()))?;
            &fresh
        }
    };
    let grammar = ProgramGrammar::new(loaded.baseline.definition()).map_err(input_error)?;
    let variables = &compiled.artifacts().configuration_variables;
    let start = spec.start_sort.as_ref().map_or_else(
        || program_start_position(variables.get("PGM").unwrap_or(&Sort::new("KItem"))),
        Sort::new,
    );
    let mut assembler = ConfigurationAssembler::new(
        &grammar,
        &loaded.baseline.definition().main_module,
        &loaded.syntax_module,
        variables,
    );
    assembler.program(&start, &text).map_err(input_error)?;
    for (name, text) in &spec.variables {
        assembler.bind(name, text).map_err(input_error)?;
    }
    assembler
        .bind_stream_defaults::<ConfigurationError>(false, false, || Ok(Vec::new()))
        .map_err(input_error)?;
    assembler.finish().map_err(input_error)
}

fn input_error(error: ConfigurationError) -> InputError {
    let message = error.to_string();
    match error {
        ConfigurationError::Program(_)
        | ConfigurationError::Parse { .. }
        | ConfigurationError::Parser(_) => InputError::Parse(message),
        ConfigurationError::Missing { names }
            if names
                .iter()
                .any(|name| matches!(name.as_str(), "$IO" | "$STDIN")) =>
        {
            InputError::Streams(message)
        }
        ConfigurationError::Missing { .. } | ConfigurationError::UnknownVariable { .. } => {
            InputError::MissingVariable(message)
        }
        _ => InputError::Assemble(message),
    }
}
