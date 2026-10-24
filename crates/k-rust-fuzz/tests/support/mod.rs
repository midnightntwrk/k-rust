//! Fixture definitions for the fuzz crate's tests (FZ-FIX).
//!
//! Each [`Fixture`] is a K definition under `tests/data` with the programs the tests run on it;
//! `tests/data/README.md` says what each one is for. [`Fixture::compiled`] compiles a fixture
//! in-process in the portable build, as `kcompile` does for the Rust backend: the definition is
//! loaded with [`load_for_compilation`] (the embedded prelude as an implicit source, the modules
//! [`CompilationBackend::Rust`] excludes left out) and compiled by [`compile_loaded_definition`].
//! Neither call is `cli`-gated, and neither reads a file: every source is embedded with
//! `include_str!`, and `requires` resolve only to k-rust's embedded builtins.
//!
//! A compiled fixture is built once per test binary and shared ([`OnceLock`]). Only immutable
//! artefacts are shared; every [`Backend`] and [`ConfigurationAssembler`] a test drives is built
//! by that test.
//!
//! Two process-wide variables reach what this module builds, and a test binary must keep both
//! fixed while it runs:
//! - `KRUST_TYPE_INFERENCE_MODE` selects the inference engine, but only in a build with k-rust's
//!   `z3-inference` feature: the portable `-p k-rust-fuzz` build never reads it, while a
//!   `--workspace` build unifies k-rust's default `cli` feature, which enables `z3-inference`,
//!   and does. The cache keeps the first build of the process.
//! - `KRUST_PARSE_DIAGNOSTIC_WORK`, read once per process, changes the text of parse-error
//!   messages, which can reach a report through a hole value that does not parse. A golden test
//!   must not vary it between its processes.
//!
//! [`Fixture::compiled`] refuses a fixture whose compilation reports any diagnostic other than
//! the ones it declares ([`Fixture::diagnostics`]), so that a fixture that drifts into a warning
//! fails here first.
//!
//! Test binaries include this module with `mod support;`; the crate's unit tests share one copy,
//! declared in `src/lib.rs` as `crate::support`.

#![allow(
    dead_code,
    reason = "each test binary uses a subset of the fixtures and their accessors"
)]

use std::{collections::BTreeMap, sync::OnceLock};

use k_rust::{
    backend::{Backend, BackendOptions, ExecutionDigest, execution_digest},
    builtin::embedded,
    definition::Definition,
    diagnostic::DiagnosticCode,
    kast::Sort,
    kompile::{
        CompilationBackend, CompileOptions, CompiledKoreArtifacts, ConfigurationAssembler,
        ConfigurationError, ProgramGrammar, compile_loaded_definition,
    },
    kore::{
        ast::{Definition as KoreDefinition, Pattern},
        parser::parse_definition,
    },
    outer::{LoadOptions, ResolvedSource, load_for_compilation},
    provenance::SourceTable,
};
use k_rust_fuzz::{BackendRoute, CompiledDefinition, ProgramSource, spec::ProgramText};

/// One program of a fixture: a runnable program text, and the configuration variables other
/// than `$PGM` the program binds, as `(name without $, value text)`.
#[derive(Debug)]
pub struct Program {
    /// The file under `tests/data`, which is also the name the program's locations carry.
    pub file: &'static str,
    pub text: &'static str,
    pub bindings: &'static [(&'static str, &'static str)],
}

/// A K definition under `tests/data` and the programs the tests run on it.
#[derive(Debug)]
pub struct Fixture {
    /// The definition file under `tests/data`, which is also its source name.
    pub file: &'static str,
    pub source: &'static str,
    pub main_module: &'static str,
    /// The sort the program parser starts at (`krun --sort`).
    pub start_sort: &'static str,
    pub programs: &'static [Program],
    /// The diagnostics the fixture compiles with on purpose, by code (TOY's missing syntax
    /// module); any other diagnostic, or a missing one, refuses it.
    pub diagnostics: &'static [DiagnosticCode],
    compiled: &'static OnceLock<Compiled>,
}

/// A fixture compiled in-process, with everything a campaign's `Definitions` is built from.
pub struct Compiled {
    pub fixture: &'static Fixture,
    /// The syntax module [`load_for_compilation`] selected (`<MAIN>-SYNTAX` in every fixture).
    pub syntax_module: String,
    /// The program grammar, over the loaded frontend definition
    /// ([`ProgramGrammar::definition`] is that definition).
    pub grammar: ProgramGrammar,
    /// The compiler's output: `definition_kore`, the configuration-variable sorts, the execution
    /// definition (for patterns) and the execution rewrite order.
    pub artifacts: CompiledKoreArtifacts,
    /// `artifacts.definition_kore`, parsed.
    pub kore: KoreDefinition,
    /// The loaded frontend definition, which `krust kcompile` stores in a compiled directory and
    /// the program grammar extends with named-field projections.
    pub loaded: Definition,
    /// The loaded definition's sources, which its provenance indexes.
    pub source_table: SourceTable,
}

impl std::fmt::Debug for Compiled {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Compiled")
            .field("fixture", &self.fixture.file)
            .field("syntax_module", &self.syntax_module)
            .finish_non_exhaustive()
    }
}

impl Fixture {
    /// The fixture compiled, built on first use in this test binary.
    ///
    /// # Panics
    ///
    /// If the fixture does not load or compile.
    pub fn compiled(&'static self) -> &'static Compiled {
        self.compiled.get_or_init(|| compile(self))
    }

    /// The program whose file is `file`.
    ///
    /// # Panics
    ///
    /// If the fixture has no such program.
    pub fn program(&self, file: &str) -> &'static Program {
        self.programs
            .iter()
            .find(|program| program.file == file)
            .unwrap_or_else(|| panic!("{} has no program {file}", self.file))
    }
}

/// Load `source`, whose source name is `file`, and compile it, as [`Fixture::compiled`] does:
/// the frontend definition, its source table, the syntax module and the compiler's output.
///
/// # Panics
///
/// If the definition does not load or compile, or compiles with diagnostics whose codes are
/// not exactly `expected`.
fn load_and_compile(
    file: &str,
    source: &str,
    main_module: &str,
    expected: &[DiagnosticCode],
) -> (Definition, SourceTable, String, CompiledKoreArtifacts) {
    load_and_compile_files(file, source, &[], main_module, expected)
}

/// The lexically normalized `path` (`.` dropped, `name/..` resolved), `/`-separated.
fn normalize(path: &str) -> String {
    let mut parts: Vec<&str> = Vec::new();
    for part in path.split('/') {
        match part {
            "" | "." => {}
            ".." if parts.last().is_some_and(|last| *last != "..") => {
                parts.pop();
            }
            _ => parts.push(part),
        }
    }
    let joined = parts.join("/");
    if path.starts_with('/') {
        format!("/{joined}")
    } else {
        joined
    }
}

/// [`load_and_compile`] of an entry that requires other sources: `files` maps each source name
/// to its text, and a `requires` resolves relative to the requiring source's directory, then to
/// an embedded builtin.
fn load_and_compile_files(
    file: &str,
    source: &str,
    files: &[(&str, &str)],
    main_module: &str,
    expected: &[DiagnosticCode],
) -> (Definition, SourceTable, String, CompiledKoreArtifacts) {
    let mut resolver = |requiring: &str, required: &str| {
        let directory = requiring
            .rsplit_once('/')
            .map_or("", |(directory, _)| directory);
        let name = if directory.is_empty() {
            normalize(required)
        } else {
            normalize(&format!("{directory}/{required}"))
        };
        files
            .iter()
            .find(|(file, _)| *file == name)
            .map(|(file, text)| ResolvedSource::new(*file, *text))
            .or_else(|| embedded(required))
            .ok_or_else(|| format!("unexpected require {required}"))
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
    let artifacts =
        compile_loaded_definition(&loaded, CompileOptions::default()).unwrap_or_else(|error| {
            panic!("{file} does not compile: {error}: {:#?}", error.diagnostics)
        });
    let codes: Vec<DiagnosticCode> = artifacts
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.code)
        .collect();
    assert_eq!(
        codes, expected,
        "{file} compiles with other diagnostics than expected: {:#?}",
        artifacts.diagnostics
    );
    let source_table = loaded.source_table().clone();
    (
        loaded.into_definition(),
        source_table,
        syntax_module,
        artifacts,
    )
}

fn compile(fixture: &'static Fixture) -> Compiled {
    let (frontend, source_table, syntax_module, artifacts) = load_and_compile(
        fixture.file,
        fixture.source,
        fixture.main_module,
        fixture.diagnostics,
    );
    let grammar = ProgramGrammar::new(&frontend)
        .unwrap_or_else(|error| panic!("{} has no program grammar: {error}", fixture.file));
    let kore = parse_definition(&artifacts.definition_kore)
        .unwrap_or_else(|error| panic!("{}'s KORE does not parse: {error}", fixture.file));
    Compiled {
        fixture,
        syntax_module,
        grammar,
        artifacts,
        kore,
        loaded: frontend,
        source_table,
    }
}

/// [`compile_source`] of an entry `file` that requires the sources of `files` (name and text),
/// each resolved relative to the directory of the source requiring it.
///
/// # Panics
///
/// If the definition does not load or compile, or compiles with any diagnostic.
pub fn compile_files(
    file: &str,
    source: &str,
    files: &[(&str, &str)],
    main_module: &str,
) -> CompiledDefinition {
    let (frontend, source_table, syntax_module, artifacts) =
        load_and_compile_files(file, source, files, main_module, &[]);
    CompiledDefinition::from_artifacts(
        main_module,
        syntax_module,
        frontend,
        source_table,
        artifacts,
    )
    .unwrap_or_else(|error| panic!("{file}: {error:?}"))
}

/// The campaign's view, on `krun`'s route, of a definition that is not a fixture: `source`
/// under the source name `file` (for example a path a test wrote it to), compiled as a fixture
/// is.
///
/// # Panics
///
/// If the definition does not load or compile, or compiles with any diagnostic.
pub fn compile_source(file: &str, source: &str, main_module: &str) -> CompiledDefinition {
    let (frontend, source_table, syntax_module, artifacts) =
        load_and_compile(file, source, main_module, &[]);
    CompiledDefinition::from_artifacts(
        main_module,
        syntax_module,
        frontend,
        source_table,
        artifacts,
    )
    .unwrap_or_else(|error| panic!("{file}: {error:?}"))
}

impl Compiled {
    pub fn main_module(&self) -> &'static str {
        self.fixture.main_module
    }

    /// The loaded frontend definition, whose grammar parses programs.
    pub fn frontend(&self) -> &Definition {
        self.grammar.definition()
    }

    /// The configuration-variable sorts, names without `$`.
    pub fn configuration_variables(&self) -> &BTreeMap<String, Sort> {
        &self.artifacts.configuration_variables
    }

    pub fn start_sort(&self) -> Sort {
        Sort::new(self.fixture.start_sort)
    }

    /// An assembler for this definition, as `krun` builds one.
    pub fn assembler(&self) -> ConfigurationAssembler<'_> {
        ConfigurationAssembler::new(
            &self.grammar,
            self.fixture.main_module,
            &self.syntax_module,
            &self.artifacts.configuration_variables,
        )
    }

    /// The initial configuration of `text` with `bindings`, assembled as `krun --io off` does
    /// with no standard input: `$PGM` parsed at the start sort, each binding parsed at its
    /// variable's sort, and every declared stream variable left unbound given its default.
    ///
    /// # Errors
    ///
    /// When the program or a binding does not parse or place.
    pub fn assemble(
        &self,
        file: &str,
        text: &str,
        bindings: &[(&str, &str)],
    ) -> Result<Pattern, ConfigurationError> {
        let mut assembler = self.assembler();
        assembler.program_file(&self.start_sort(), text, file)?;
        for (name, value) in bindings {
            assembler.bind(name, value)?;
        }
        assembler
            .bind_stream_defaults(false, false, || Ok::<_, ConfigurationError>(b"\n".to_vec()))?;
        assembler.finish()
    }

    /// The initial configuration of the fixture's program `file`, unchanged.
    ///
    /// # Panics
    ///
    /// If the program does not assemble.
    pub fn initial(&self, file: &str) -> Pattern {
        let program = self.fixture.program(file);
        self.assemble(program.file, program.text, program.bindings)
            .unwrap_or_else(|error| panic!("{file} does not assemble: {error}"))
    }

    /// A backend on `krun`'s route: the definition internalized with the compiler's rewrite
    /// order (`Backend::internalize_source_definition`), which orders rules and so selects the
    /// path strategy `any` follows.
    ///
    /// # Panics
    ///
    /// If the definition does not internalize.
    pub fn source_backend(&self) -> Backend {
        let definition = Backend::internalize_source_definition(
            &self.kore,
            self.fixture.main_module,
            &self.artifacts.execution_rewrite_order,
        )
        .unwrap_or_else(|error| panic!("{}: {error:?}", self.fixture.file));
        Backend::from_internalized(definition, BackendOptions::default())
            .unwrap_or_else(|error| panic!("{}: {error:?}", self.fixture.file))
    }

    /// A backend from the KORE alone (`Backend::from_definition`, the route that takes no
    /// rewrite order, as kink builds one).
    ///
    /// # Panics
    ///
    /// If the definition does not load.
    pub fn kore_backend(&self) -> Backend {
        Backend::from_definition(
            self.kore.clone(),
            self.fixture.main_module,
            BackendOptions::default(),
        )
        .unwrap_or_else(|error| panic!("{}: {error:?}", self.fixture.file))
    }

    /// The execution digest of `definition_kore`.
    ///
    /// # Panics
    ///
    /// If the definition has none (compiler output always has one).
    pub fn digest(&self) -> ExecutionDigest {
        execution_digest(&self.kore)
            .unwrap_or_else(|error| panic!("{}: {error:?}", self.fixture.file))
    }

    /// The campaign's view of this definition on `krun`'s route
    /// ([`BackendRoute::SourceExecution`] with the compiler's rewrite order).
    ///
    /// # Panics
    ///
    /// If the KORE does not parse (compiler output always parses).
    pub fn definition(&self) -> CompiledDefinition {
        CompiledDefinition::from_artifacts(
            self.fixture.main_module,
            self.syntax_module.clone(),
            self.loaded.clone(),
            self.source_table.clone(),
            self.artifacts.clone(),
        )
        .unwrap_or_else(|error| panic!("{}: {error:?}", self.fixture.file))
    }

    /// [`Self::definition`] on `route`.
    pub fn definition_on(&self, route: BackendRoute) -> CompiledDefinition {
        CompiledDefinition {
            route,
            ..self.definition()
        }
    }

    /// `definition_kore` with `attribute` added to the attributes of the one axiom labelled
    /// `<main module>.<label>`: for example `non-executable{}()` on a rewrite rule, which the K
    /// frontend refuses but the backend accepts from caller KORE (kink's route).
    ///
    /// # Panics
    ///
    /// If the label does not occur exactly once, or the edited KORE does not parse.
    pub fn kore_with_axiom_attribute(&self, label: &str, attribute: &str) -> KoreDefinition {
        let needle = format!("label{{}}(\"{}.{label}\")", self.fixture.main_module);
        let kore = &self.artifacts.definition_kore;
        assert_eq!(
            kore.matches(&needle).count(),
            1,
            "{needle} in {}",
            self.fixture.file
        );
        let edited = kore.replacen(&needle, &format!("{attribute}, {needle}"), 1);
        parse_definition(&edited)
            .unwrap_or_else(|error| panic!("{} edited: {error}", self.fixture.file))
    }

    /// [`Self::kore_with_axiom_attribute`] with `non-executable{}()`, as the campaign's view on
    /// [`BackendRoute::FromDefinition`], the route that builds a backend from caller KORE.
    pub fn definition_with_non_executable(&self, label: &str) -> CompiledDefinition {
        CompiledDefinition {
            kore: self.kore_with_axiom_attribute(label, "non-executable{}()"),
            ..self.definition_on(BackendRoute::FromDefinition)
        }
    }

    /// A backend over [`Self::kore_with_axiom_attribute`] with `non-executable{}()`, built with
    /// `Backend::from_definition`.
    ///
    /// # Panics
    ///
    /// If the edited definition does not load.
    pub fn backend_with_non_executable(&self, label: &str) -> Backend {
        Backend::from_definition(
            self.kore_with_axiom_attribute(label, "non-executable{}()"),
            self.fixture.main_module,
            BackendOptions::default(),
        )
        .unwrap_or_else(|error| panic!("{}: {error:?}", self.fixture.file))
    }

    /// The fixture's program `file` as a campaign's program input: its text unchanged, its
    /// start sort, and its configuration-variable bindings.
    pub fn program_source(&self, file: &str) -> ProgramSource {
        let program = self.fixture.program(file);
        ProgramSource {
            program: Some(ProgramText {
                name: program.file.to_owned(),
                text: program.text.to_owned(),
                start_sort: self.fixture.start_sort.to_owned(),
            }),
            config_vars: program
                .bindings
                .iter()
                .map(|(name, value)| ((*name).to_owned(), (*value).to_owned()))
                .collect(),
        }
    }
}

macro_rules! data {
    ($path:literal) => {
        include_str!(concat!("../data/", $path))
    };
}

macro_rules! program {
    ($path:literal) => {
        Program {
            file: $path,
            text: data!($path),
            bindings: &[],
        }
    };
    ($path:literal, $($name:literal = $value:literal),+) => {
        Program {
            file: $path,
            text: data!($path),
            bindings: &[$(($name, data!($value).trim_ascii_end())),+],
        }
    };
}

macro_rules! fixture {
    ($name:ident, $file:literal, $main:literal, $programs:expr) => {
        fixture!($name, $file, $main, $programs, diagnostics = []);
    };
    ($name:ident, $file:literal, $main:literal, $programs:expr, diagnostics = [$($code:ident),*]) => {
        pub static $name: Fixture = Fixture {
            file: $file,
            source: data!($file),
            main_module: $main,
            start_sort: "Pgm",
            programs: $programs,
            diagnostics: &[$(DiagnosticCode::$code),*],
            compiled: {
                static COMPILED: OnceLock<Compiled> = OnceLock::new();
                &COMPILED
            },
        };
    };
}

/// IMP, from the fz26 experiment, with signed Int literals.
pub const IMP_PROGRAMS: &[Program] = &[
    program!("imp/commute.imp"),
    program!("imp/le.imp"),
    program!("imp/div.imp"),
    program!("imp/loop.imp"),
];
fixture!(IMP, "imp/imp.k", "IMP", IMP_PROGRAMS);

fixture!(
    UNSIGNED,
    "unsigned/unsigned.k",
    "UNSIGNED",
    &[program!("unsigned/sum.pgm")]
);

/// The programs of `chosen.k` and of its mutant.
pub const CHOSEN_PROGRAMS: &[Program] = &[program!("chosen/keys.pgm"), program!("chosen/set.pgm")];
fixture!(CHOSEN, "chosen/chosen.k", "CHOSEN", CHOSEN_PROGRAMS);
fixture!(
    CHOSEN_KILL,
    "chosen/chosen-kill.k",
    "CHOSEN",
    CHOSEN_PROGRAMS
);

fixture!(
    RULES,
    "rules/rules.k",
    "RULES",
    &[
        program!("rules/div.pgm"),
        program!("rules/check.pgm"),
        program!("rules/twice.pgm"),
    ]
);

/// The programs of the baseline and of every mutant of `coin/`.
pub const COIN_PROGRAMS: &[Program] = &[program!("coin/flip.pgm"), program!("coin/count.pgm")];
fixture!(COIN, "coin/coin.k", "COIN", COIN_PROGRAMS);
fixture!(COIN_LAYOUT, "coin/coin-layout.k", "COIN", COIN_PROGRAMS);
fixture!(COIN_SWAPPED, "coin/coin-swapped.k", "COIN", COIN_PROGRAMS);
fixture!(COIN_PRIO, "coin/coin-prio.k", "COIN", COIN_PROGRAMS);
fixture!(COIN_KILL, "coin/coin-kill.k", "COIN", COIN_PROGRAMS);
fixture!(COIN_FUNC, "coin/coin-func.k", "COIN", COIN_PROGRAMS);

/// TRIAL2's IMP (the K tutorial's lesson-4 IMP, unchanged) and three of kink's mutants of it
/// (FZ-DIFFEND): the programs are TRIAL2's templates.
pub const IMP_DIFF_PROGRAMS: &[Program] = &[
    program!("imp-diff/primes.imp"),
    program!("imp-diff/sum.imp"),
];
fixture!(IMP_DIFF, "imp-diff/imp.k", "IMP", IMP_DIFF_PROGRAMS);
fixture!(
    IMP_DIV_GUARD_DROPPED,
    "imp-diff/imp-div-guard-dropped.k",
    "IMP",
    IMP_DIFF_PROGRAMS
);
// The mutant's `requires true` leaves the rule's `Rho` unused, which the compiler reports.
fixture!(
    IMP_DECL_ALLOWS_REDECLARATION,
    "imp-diff/imp-decl-allows-redeclaration.k",
    "IMP",
    IMP_DIFF_PROGRAMS,
    diagnostics = [UnusedVariable]
);
fixture!(
    IMP_ADD_COMMUTED,
    "imp-diff/imp-add-commuted.k",
    "IMP",
    IMP_DIFF_PROGRAMS
);

/// The claim pair (FZ-DIFFEND): a baseline that stops abnormally on `go(0)` and three mutants
/// whose step on `go(0)` is undefined, without a claim, against a `total` claim and against a
/// `preserves-definedness` claim.
pub const CLAIMSTEP_PROGRAMS: &[Program] = &[program!("claimstep/go.pgm")];
fixture!(
    CLAIMSTEP,
    "claimstep/claimstep.k",
    "CLAIMSTEP",
    CLAIMSTEP_PROGRAMS
);
fixture!(
    CLAIMSTEP_PARTIAL,
    "claimstep/claimstep-partial.k",
    "CLAIMSTEP",
    CLAIMSTEP_PROGRAMS
);
fixture!(
    CLAIMSTEP_TOTAL,
    "claimstep/claimstep-total.k",
    "CLAIMSTEP",
    CLAIMSTEP_PROGRAMS
);
fixture!(
    CLAIMSTEP_PRESERVES,
    "claimstep/claimstep-preserves.k",
    "CLAIMSTEP",
    CLAIMSTEP_PROGRAMS
);

/// The diamond pair (FZ-DIFFEND): two converging paths, one of which reads a chosen value whose
/// mark a state-set merge moves to the result's list.
pub const DIAMOND_PROGRAMS: &[Program] = &[program!("diamond/go.pgm")];
fixture!(DIAMOND, "diamond/diamond.k", "DIAMOND", DIAMOND_PROGRAMS);
fixture!(
    DIAMOND_PLUS,
    "diamond/diamond-plus.k",
    "DIAMOND",
    DIAMOND_PROGRAMS
);

/// The overloaded list family (FZ-OVERLIST, FZ-DATAEND): a baseline whose end holds an
/// irreducible application of the overload head `_,_Exps`, a mutant with the same overload
/// equations whose end differs, one whose overload equations differ, and one whose end holds an
/// unevaluated total function.
pub const OV_PROGRAMS: &[Program] = &[program!("ov/three.pgm")];
fixture!(OV, "ov/ov.k", "OV", OV_PROGRAMS);
fixture!(OV_PREPEND, "ov/ov-prepend.k", "OV", OV_PROGRAMS);
fixture!(OV_INTS, "ov/ov-ints.k", "OV", OV_PROGRAMS);
fixture!(OV_SIZE, "ov/ov-size.k", "OV", OV_PROGRAMS);

/// FZ-DATAEND review B2: a broken overload family whose axioms equate the constructor terms
/// `.Ids` and `.Vals`, stored by the baseline and the mutant.
pub const DIA_PROGRAMS: &[Program] = &[program!("dia/go.pgm")];
fixture!(DIA, "dia/dia.k", "DIA", DIA_PROGRAMS);
fixture!(DIA_M, "dia/dia-m.k", "DIA", DIA_PROGRAMS);

/// FZ-DATAEND review B1: an overload placed across `K`, and a mutant that adds a subsort below
/// the overload's argument sort.
pub const KPLACE_PROGRAMS: &[Program] = &[program!("kplace/go.pgm")];
fixture!(KPLACE, "kplace/kp.k", "KP", KPLACE_PROGRAMS);
fixture!(KPLACE_M, "kplace/kp-m.k", "KP", KPLACE_PROGRAMS);

/// FZ-DATAEND review round 2: each a baseline and a mutant whose theories read one end
/// differently (a parametric subsort, an added overload member, an added `anywhere` rule), and
/// a broken family that must not refuse unrelated symbols.
/// The parametric pair needs Z3 sort inference to compile, so it is not in [`ALL`], which the
/// portable build judges too; its campaign test is `z3`-gated.
pub const R2_PARAM_PROGRAMS: &[Program] = &[program!("r2-param/go.pgm")];
fixture!(R2_PARAM, "r2-param/b.k", "PM", R2_PARAM_PROGRAMS);
fixture!(R2_PARAM_M, "r2-param/m.k", "PM", R2_PARAM_PROGRAMS);
pub const R2_ADDMEMBER_PROGRAMS: &[Program] = &[program!("r2-addmember/go.pgm")];
fixture!(
    R2_ADDMEMBER,
    "r2-addmember/b.k",
    "AM",
    R2_ADDMEMBER_PROGRAMS
);
fixture!(
    R2_ADDMEMBER_M,
    "r2-addmember/m.k",
    "AM",
    R2_ADDMEMBER_PROGRAMS
);
pub const R2_ANYW_PROGRAMS: &[Program] = &[program!("r2-anyw/go.pgm")];
fixture!(R2_ANYW, "r2-anyw/b.k", "AW", R2_ANYW_PROGRAMS);
fixture!(R2_ANYW_M, "r2-anyw/m.k", "AW", R2_ANYW_PROGRAMS);
pub const R2_OVER_PROGRAMS: &[Program] = &[program!("r2-over/go.pgm")];
fixture!(R2_OVER, "r2-over/b.k", "KP", R2_OVER_PROGRAMS);
fixture!(R2_OVER_M, "r2-over/m.k", "KP", R2_OVER_PROGRAMS);

/// FZ-DATAEND review round 3: definitions whose equations are not confluent (an overlap modulo
/// an overload axiom, a broken family reached through a function, two function equations with
/// different results); each baseline stores `a` and its mutant `bb`, which its theory equates.
pub const R3_MODOV_PROGRAMS: &[Program] = &[program!("r3-modov/go.pgm")];
fixture!(R3_MODOV, "r3-modov/b.k", "MO", R3_MODOV_PROGRAMS);
fixture!(R3_MODOV_M, "r3-modov/m.k", "MO", R3_MODOV_PROGRAMS);
pub const R3_PROPAGATE_PROGRAMS: &[Program] = &[program!("r3-propagate/go.pgm")];
fixture!(
    R3_PROPAGATE,
    "r3-propagate/b.k",
    "PR",
    R3_PROPAGATE_PROGRAMS
);
fixture!(
    R3_PROPAGATE_M,
    "r3-propagate/m.k",
    "PR",
    R3_PROPAGATE_PROGRAMS
);
pub const R3_PLAINQ_PROGRAMS: &[Program] = &[program!("r3-plainq/go.pgm")];
fixture!(R3_PLAINQ, "r3-plainq/b.k", "PQ", R3_PLAINQ_PROGRAMS);
fixture!(R3_PLAINQ_M, "r3-plainq/m.k", "PQ", R3_PLAINQ_PROGRAMS);

/// FZ-DATAEND review round 4 (r4-hookite): an equation at a symbol hooked to `KEQUAL.ite` that
/// disagrees with the builtin, which the evaluator applies first; each baseline stores `a` and
/// its mutant `bb`, which its theory equates.
pub const R4_HOOKITE_PROGRAMS: &[Program] = &[program!("r4-hookite/go.pgm")];
fixture!(R4_HOOKITE, "r4-hookite/b.k", "HI", R4_HOOKITE_PROGRAMS);
fixture!(R4_HOOKITE_M, "r4-hookite/m.k", "HI", R4_HOOKITE_PROGRAMS);

/// FZ-CONFLUENCE review A (B1): `replace` (no builtin step) given a higher-priority equation, so
/// that `replaceAll`'s domains.md equation, through `replace`, disagrees with the builtin; each
/// baseline stores `"cb"` and its mutant `"ab"`, which its theory equates.
/// FZ-CONFLUENCE review A round 2 (R2-B1): a file named `domains.md` whose `replace`-hooked
/// symbol takes domains.md's label and two false rows at lines 1911 and 1915; each baseline
/// stores `"cb"` and its mutant `"ab"`, which its theory equates.
pub const R2_SPOOF_PROGRAMS: &[Program] = &[program!("r2-spoof/go.pgm")];
fixture!(
    R2_SPOOF,
    "r2-spoof/b/domains.md",
    "SPOOF",
    R2_SPOOF_PROGRAMS,
    diagnostics = [DeprecatedAttribute]
);
fixture!(
    R2_SPOOF_M,
    "r2-spoof/m/domains.md",
    "SPOOF",
    R2_SPOOF_PROGRAMS,
    diagnostics = [DeprecatedAttribute]
);

pub const REPLACE_PRIORITY_PROGRAMS: &[Program] = &[program!("replace-priority/go.pgm")];
fixture!(
    REPLACE_PRIORITY,
    "replace-priority/b.k",
    "RP",
    REPLACE_PRIORITY_PROGRAMS
);
fixture!(
    REPLACE_PRIORITY_M,
    "replace-priority/m.k",
    "RP",
    REPLACE_PRIORITY_PROGRAMS
);

/// The macro-only pair (phase-1 review B1): equal `definition.kore`, unequal `macros.kore`.
pub const MAC_PROGRAMS: &[Program] = &[program!("mac/inc.pgm")];
fixture!(MAC, "mac/mac.k", "MAC", MAC_PROGRAMS);
fixture!(MAC_KILL, "mac/mac-kill.k", "MAC", MAC_PROGRAMS);

/// The vanished-end pair (FZ-08 review B1).
pub const VANISH_PROGRAMS: &[Program] = &[program!("vanish/pick.pgm")];
fixture!(VANISH, "vanish/vanish.k", "VANISH", VANISH_PROGRAMS);
fixture!(
    VANISH_KILL,
    "vanish/vanish-kill.k",
    "VANISH",
    VANISH_PROGRAMS
);

fixture!(
    LEDGER,
    "ledger/ledger.k",
    "LEDGER",
    &[program!("ledger/settle.pgm", "TX" = "ledger/settle.tx")]
);

fixture!(
    LOADCLAIM,
    "loadclaim/loadclaim.k",
    "LOADCLAIM",
    &[program!("loadclaim/go.pgm")]
);

fixture!(
    TAINT,
    "taint/taint.k",
    "TAINT",
    &[
        program!("taint/get.pgm"),
        program!("taint/look.pgm"),
        program!("taint/guard.pgm"),
    ]
);

// The rule graph's fixtures (FZ-G8): the graph's tests (`src/graph/tests.rs`) run their
// programs and check their ends.
fixture!(
    GRAPH,
    "graph/graph.k",
    "GRAPH",
    &[
        program!("graph/start.pgm"),
        program!("graph/call.pgm"),
        program!("graph/stray.pgm"),
    ]
);
fixture!(
    VALUE,
    "graph/value.k",
    "VALUE",
    &[program!("graph/value.pgm", "N" = "graph/value.n")]
);
fixture!(
    SHAPE,
    "graph/shape.k",
    "SHAPE",
    &[program!("graph/shape.pgm", "SHAPE" = "graph/shape.s")]
);

fixture!(
    SIBLING,
    "sibling/sibling.k",
    "SIBLING",
    &[program!("sibling/sib.pgm")]
);

// An end steered by a hook k-rust does not compute (D21).
fixture!(
    STEER,
    "steer/steer.k",
    "UNSP",
    &[program!("steer/go.pgm"), program!("steer/big.pgm")]
);

// The hole overlay's and the values module's fixtures (FZ-02, FZ-03).
fixture!(
    TOY,
    "toy/toy.k",
    "TOY",
    &[program!("toy/send.pgm", "TX" = "toy/send.tx")],
    diagnostics = [MissingSyntaxModule]
);
fixture!(
    WRAPS,
    "wraps/wraps.k",
    "WRAPS",
    &[program!("wraps/one.pgm")]
);
fixture!(
    STREAMS,
    "streams/streams.k",
    "STREAMS",
    &[program!("streams/go.pgm", "LIMIT" = "streams/go.limit")]
);
// No program: the values tests assemble `run` with one binding per configuration variable.
fixture!(VALUES, "values/values.k", "VALUES", &[]);
// The hole-sort rule's reach beyond the program sort, and a round trip under locations (HARD-A).
fixture!(
    ELEMENTS,
    "elements/elements.k",
    "ELEMENTS",
    &[program!("elements/sum.pgm")]
);
fixture!(
    SYNTAXVARS,
    "syntaxvars/syntaxvars.k",
    "SYNTAXVARS",
    &[program!(
        "syntaxvars/go.pgm",
        "LIB" = "syntaxvars/go.lib",
        "LIB2" = "syntaxvars/go.lib2",
        "EXT" = "syntaxvars/go.ext",
        "C" = "syntaxvars/go.c",
        "SHAPE" = "syntaxvars/go.shape"
    )]
);
fixture!(
    LOCATED,
    "located/located.k",
    "LOCATED",
    &[program!("located/sum.pgm")]
);

// The stall benchmark's maze (FZ-13); `tests/data/maze/harness.rs` holds its cells.
fixture!(MAZE, "maze/maze.k", "MAZE", &[program!("maze/walk.pgm")]);

// The dictionary proposer's fixture (FZ-11): constants behind the rule graph and function calls.
fixture!(
    DICT,
    "dict/dict.k",
    "DICT",
    &[program!("dict/run.pgm"), program!("dict/probe.pgm")]
);

// The climb's score fixture (FZ-12): a guard that is undefined for some inputs.
fixture!(
    GUARD,
    "guard/guard.k",
    "GUARD",
    &[program!("guard/zero.pgm"), program!("guard/one.pgm")]
);

// The list-shaped stall benchmark (FZ-14); `tests/data/lock/harness.rs` holds its cells.
fixture!(
    LOCK,
    "lock/lock.k",
    "LOCK",
    &[program!("lock/open.pgm", "KEYS" = "lock/open.keys")]
);

// The ledger-shaped stall benchmark (FZ-14 round 2); `tests/data/bank/harness.rs` holds its
// cells.
fixture!(
    BANK,
    "bank/bank.k",
    "BANK",
    &[program!("bank/run.pgm", "TXS" = "bank/run.txs")]
);

// The loop-shaped stall benchmark (FZ-17); `tests/data/tally/harness.rs` holds its cells.
fixture!(
    TALLY,
    "tally/tally.k",
    "TALLY",
    &[program!("tally/run.pgm", "KEYS" = "tally/run.keys")]
);

// The tally with work proportional to the keys left after the loop (FZ-17 fix round): an
// equation (`NOISE`) and a rewrite rule (`DRAIN`); `tests/data/tally/harness.rs` holds the cells.
fixture!(
    NOISE,
    "tally/noise.k",
    "NOISE",
    &[program!("tally/run.pgm", "KEYS" = "tally/run.keys")]
);
fixture!(
    DRAIN,
    "tally/drain.k",
    "DRAIN",
    &[program!("tally/run.pgm", "KEYS" = "tally/run.keys")]
);

// The narrowing of Int holes to the program's syntax (FZ-INTGEN): a terminal that spells one
// negative literal, a grammar with no unary minus, and UNSIGNED with signed literals.
pub const INTGEN_PROGRAMS: &[Program] = &[program!("intgen/sum.pgm")];
fixture!(MINUSONE, "intgen/minusone.k", "MINUSONE", INTGEN_PROGRAMS);
fixture!(NOMINUS, "intgen/nominus.k", "NOMINUS", INTGEN_PROGRAMS);
fixture!(SIGNED, "intgen/signed.k", "UNSIGNED", INTGEN_PROGRAMS);
// A threaded language: its <k> cell lies under the multiplicity cell <thread>, so the default
// normal end is judged on every <k> cell (FZ-UNSUPPORTED).
fixture!(
    THREADS,
    "threads/threads.k",
    "THREADS",
    &[
        program!("threads/spawn.pgm"),
        program!("threads/keep.pgm"),
        program!("threads/fail.pgm"),
    ]
);

// The <k> cell under a `?` cell absent from the initial configuration, the program in <code>
// (FZ-UNSUPPORTED review N1).
fixture!(
    QOPT,
    "qopt/qopt.k",
    "QOPT",
    &[program!("qopt/bad.pgm"), program!("qopt/start.pgm")]
);

/// The re-run pair (INT7): a baseline with the ends `a(N)`, `c(N)` and `b(opaque(N))` (clean,
/// not data) and a mutant without the last, whose one path reaches `a(N)` and whose all-paths
/// re-run decides the case.
pub const RERUN_PROGRAMS: &[Program] = &[program!("rerun/go.pgm")];
fixture!(RERUN, "rerun/rerun.k", "RERUN", RERUN_PROGRAMS);
fixture!(RERUN_DROP, "rerun/rerun-drop.k", "RERUN", RERUN_PROGRAMS);

/// Every fixture that `tests/fixtures.rs` judges, in the order of `tests/data/README.md`: each
/// compiles, converts to a campaign definition on both routes, and assembles every program.
/// TOY is left out because its syntax module is its main module, where the check expects
/// `<MAIN>-SYNTAX`; `src/holes/tests.rs` covers it.
pub static ALL: [&Fixture; 80] = [
    &IMP,
    &UNSIGNED,
    &CHOSEN,
    &CHOSEN_KILL,
    &RULES,
    &COIN,
    &COIN_LAYOUT,
    &COIN_SWAPPED,
    &COIN_PRIO,
    &COIN_KILL,
    &COIN_FUNC,
    &MAC,
    &MAC_KILL,
    &VANISH,
    &VANISH_KILL,
    &LEDGER,
    &LOADCLAIM,
    &TAINT,
    &GRAPH,
    &VALUE,
    &SHAPE,
    &SIBLING,
    &STEER,
    &WRAPS,
    &STREAMS,
    &VALUES,
    &ELEMENTS,
    &SYNTAXVARS,
    &LOCATED,
    &MAZE,
    &DICT,
    &GUARD,
    &LOCK,
    &BANK,
    &TALLY,
    &NOISE,
    &DRAIN,
    &MINUSONE,
    &NOMINUS,
    &SIGNED,
    &IMP_DIFF,
    &IMP_DIV_GUARD_DROPPED,
    &IMP_DECL_ALLOWS_REDECLARATION,
    &IMP_ADD_COMMUTED,
    &CLAIMSTEP,
    &CLAIMSTEP_PARTIAL,
    &CLAIMSTEP_TOTAL,
    &CLAIMSTEP_PRESERVES,
    &DIAMOND,
    &DIAMOND_PLUS,
    &THREADS,
    &QOPT,
    &RERUN,
    &RERUN_DROP,
    &OV,
    &OV_PREPEND,
    &OV_INTS,
    &OV_SIZE,
    &DIA,
    &DIA_M,
    &KPLACE,
    &KPLACE_M,
    &R2_ADDMEMBER,
    &R2_ADDMEMBER_M,
    &R2_ANYW,
    &R2_ANYW_M,
    &R2_OVER,
    &R2_OVER_M,
    &R3_MODOV,
    &R3_MODOV_M,
    &R3_PROPAGATE,
    &R3_PROPAGATE_M,
    &R3_PLAINQ,
    &R3_PLAINQ_M,
    &R4_HOOKITE,
    &R4_HOOKITE_M,
    &REPLACE_PRIORITY,
    &REPLACE_PRIORITY_M,
    &R2_SPOOF,
    &R2_SPOOF_M,
];
