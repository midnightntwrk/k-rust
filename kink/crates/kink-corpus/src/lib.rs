//! kink's admission-and-input library and kink's corpus harness.
//!
//! The crate has two roles.
//!
//! It is the library every kink front end builds on: kink-flow, and through kink-flow the krs
//! front end (`krs kink`, in krs-cli). The library is
//! [`resolver`] (loading a K definition under a root, recording every file the load reads),
//! [`input`] (assembling a program's initial configuration from its program text and its
//! configuration variables),
//! the stage functions and records of [`admission`] (`check_refused_cases`,
//! `check_loaded_refused_cases`, `check_semantic_input`, `check_loaded_semantic_input`,
//! `compile_definition`, `compile_definition_with`, `input_backend`, `program_input`,
//! `input_refusal`, `check_initial_state`, `below_floor_cases`, `path_names_case`,
//! `REFUSED_CASE_STAGE`, `BELOW_FLOOR_CITATION`, `AdmissionRecord`, `AdmissionRefusal`,
//! `KompileWarning`),
//! [`Store`]'s atomic JSON files (`new`, `root`, `read_json`, `write_json`, `write_text`,
//! `write_bytes`) and their error, [`StoreError`],
//! [`runner::all_normal`], [`cli::DEFINITION_STACK_BYTES`], [`manifest::RefusedCase`] and
//! [`manifest::BELOW_FLOOR`]; and, for tests under the `measure` feature,
//! `input::input_grammar_builds`.
//!
//! It is also kink's corpus harness: the `kink-corpus` binary ([`cli`]) over a canonical-JSON
//! corpus manifest ([`manifest`]), which runs campaigns of kink-patch's generated mutants over
//! many K definitions, each definition in its own process ([`runner`]), keeps a digest-checked
//! store with resume (the corpus layout of [`store`]), aggregates a [`summary`] and re-derives a
//! stored report (`replay-check`); [`admission::admit_definition`] admits one definition of such
//! a manifest.
//! kink's tests and its maintainers use the harness; it is not a user tool.
//! A user describes a corpus in kink-flow's `FLOW.toml` and reads kink-flow's statuses;
//! the crate's README maps each capability of the harness manifest to the user tool's form, or
//! states why users have none.

pub mod admission;
pub mod cli;
pub mod input;
pub mod manifest;
pub mod resolver;
pub mod runner;
pub mod store;
pub mod summary;

pub use input::{
    InputAssembler, InputError, InputGrammar, ProgramSource, TestInputSpec, VariableInput,
    assemble_input, assemble_input_with,
};
pub use resolver::{CorpusSource, LoadError, LoadedSource, SourceFile, load_source};

pub use runner::{DefinitionOutcome, run_definition};
pub use store::{Store, StoreError};
