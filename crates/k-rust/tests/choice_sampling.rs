//! The seeded chooser (`k_rust_backend::choice_sampling`, feature `choice-sampling`) reaches
//! every class of implementation-chosen value and only the values the definition leaves open
//! (`docs/compatibility.md`, "Implementation-chosen hook values").
//!
//! A run whose `implementationChosenValues` list is empty is read as the run of every model of
//! the definition. Under `with_seed`, each site computing an open value computes another value
//! some model gives; a run without a mark must then be unchanged, and a probe of each class,
//! whose run is marked, must change under some seed (else the chooser does not reach the class
//! and a harness over unmarked runs tests nothing for it).
//!
//! Each program is compiled and run inside the seed's scope (a compile-time choice is read
//! there), for the seeds 1 to 3 and once without a scope, with a console (`#read`'s count is a
//! class) and in `Execution` mode, where k-rust takes its own value for every open application.
//! The chooser's count of the open values each class's sites took (`choice_sampling::take_counts`)
//! is read apart for the compilation and the run: a probe's class takes one under some seed, and
//! a control's run takes none.

use std::{
    collections::{BTreeMap, BTreeSet},
    num::NonZeroU64,
};

use k_rust::{
    backend::{Backend, BackendOptions},
    builtin::embedded,
    kast::Sort,
    kompile::{
        CompilationBackend, CompileOptions, ConfigurationAssembler, ProgramGrammar,
        compile_loaded_definition,
    },
    kore::ast::Pattern,
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use k_rust_backend::{
    choice_sampling,
    evaluation::EvaluationMode,
    rewrite::{ExecutionOptions, execute_with_io_state},
    transition::ExecutionIoState,
};

/// One probe per class, and a control beside it on which the value is determined.
const PROBES: &str = r#"
requires "substitution.md"
module MAIN
  imports INT
  imports FLOAT
  imports STRING
  imports MAP
  imports SET
  imports LIST
  imports COLLECTIONS
  imports SUBSTITUTION
  imports K-IO
  syntax Exp ::= KVar | lam(KVar, Exp) [binder] | app(Exp, Exp) | Int
  syntax Pgm ::= keys(Int) | vals(Int) | s2l(Int) | keysOne(Int) | choiceMap(Int) | choiceSet(Int)
               | choiceOne(Int) | mixed(Float) | nan(Float) | sg(Float) | b2s(Int) | mz(Float)
               | sub(Exp, Exp, KVar) | rd(Int) | done(KItem)
  configuration <k> $PGM:Pgm </k>
  rule keys(N) => done(keys_list((N |-> 0) (N +Int 1 |-> 0)))
  rule vals(N) => done(values((N |-> 0) (N +Int 1 |-> 1)))
  rule s2l(N) => done(Set2List(SetItem(N) SetItem(N +Int 1)))
  rule keysOne(N) => done(keys_list(N |-> 0))
  rule choiceMap(N) => done(choice((N |-> 0) (N +Int 1 |-> 0)))
  rule choiceSet(N) => done(choice(SetItem(N) SetItem(N +Int 1)))
  rule choiceOne(N) => done(choice(N |-> 0))
  rule mixed(F) => done(F +Float 2.0)
  rule nan(F) => done(signFloat(F /Float F))
  rule sg(F) => done(signFloat(F))
  rule b2s(I) => done(Base2String(I, 16))
  rule mz(F) => done(minFloat(F, --Float F))
  rule sub(T, V, X) => done(T[V / X])
  rule rd(N) => done(#read(0, N))
endmodule
"#;

/// `tests/implementation_chosen.rs`'s `FRESH`: `mk` binds two `!` names (class
/// `fresh-association`), `one` and `again` one each.
const FRESH: &str = r#"
module MAIN
  imports INT
  imports BOOL
  syntax Pgm ::= mk(Int) | one(Int) | go(Int)
  syntax KItem ::= "again"
  configuration <T> <k> $PGM:Pgm </k> <a> 7 </a> <b> 7 </b> <r> 7 </r> </T>
  rule [mk]: <k> mk(_) => .K ... </k> <a> _ => !_A:Int </a> <b> _ => !_B:Int </b>
  rule <k> one(_) => again ... </k> <a> _ => !_A:Int </a>
  rule <k> again => .K ... </k> <b> _ => !_B:Int </b>
  rule [div]: <k> go(_) => .K ... </k> <r> _ => 10 /Int !_A:Int </r> <b> _ => !_B:Int </b>
  rule <k> go(_) => .K ... </k>
endmodule
"#;

/// A program of a definition, and the class whose probe or control it is.
struct Program {
    class: &'static str,
    source: &'static str,
    program: &'static str,
}

const fn program(class: &'static str, source: &'static str, program: &'static str) -> Program {
    Program {
        class,
        source,
        program,
    }
}

/// The console input of every run: `rd(3)` may read one to three of its characters.
const CONSOLE: &[u8] = b"ABC";

/// Programs whose run reads a value of the class.
const POWER: &[Program] = &[
    program("order", PROBES, "keys(1)"),
    program("order", PROBES, "vals(1)"),
    program("order", PROBES, "s2l(1)"),
    program("item", PROBES, "choiceMap(1)"),
    program("item", PROBES, "choiceSet(1)"),
    program("float-destination", PROBES, "mixed(0.1f)"),
    program("nan-sign", PROBES, "nan(0.0)"),
    program("letter-case", PROBES, "b2s(255)"),
    program("signed-zero", PROBES, "mz(0.0)"),
    program("fresh-name", PROBES, "sub(lam(y, app(x, y)), 1, x)"),
    program("read-count", PROBES, "rd(3)"),
    program("fresh-association", FRESH, "mk(3)"),
];

/// Programs beside each probe whose value of the class is determined.
const CONTROLS: &[Program] = &[
    program("order", PROBES, "keysOne(1)"),
    program("item", PROBES, "choiceOne(1)"),
    program("float-destination", PROBES, "mixed(0.5)"),
    program("nan-sign", PROBES, "sg(-0.0)"),
    program("letter-case", PROBES, "b2s(9)"),
    program("signed-zero", PROBES, "mz(1.0)"),
    program("fresh-name", PROBES, "sub(app(x, x), 1, x)"),
    program("read-count", PROBES, "rd(1)"),
    program("fresh-association", FRESH, "one(3)"),
];

const SEEDS: [u64; 3] = [1, 2, 3];

/// What a run gives: its leaves, as the set of (state, halt reason), and the classes of the
/// run's list of implementation-chosen values.
#[derive(Debug, PartialEq, Eq)]
struct Run {
    leaves: BTreeSet<(String, String)>,
    classes: BTreeSet<&'static str>,
}

/// Compile `source` (main and syntax module `MAIN`) with the prelude and assemble the initial
/// configuration whose `$PGM` is `program` at sort `Pgm`.
fn compile(source: &str, program: &str) -> (String, Pattern) {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("test.k", source),
        "MAIN",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap();
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    let frontend = loaded.into_definition();
    let grammar = ProgramGrammar::new(&frontend).unwrap();
    let mut assembler =
        ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &artifacts.configuration_variables);
    assembler.program(&Sort::new("Pgm"), program).unwrap();
    (artifacts.definition_kore, assembler.finish().unwrap())
}

/// Per class name, the open values the chooser's sites took (`choice_sampling::take_counts`).
type Taken = BTreeMap<&'static str, u64>;

/// The open values taken while compiling, and while running.
#[derive(Debug, Default)]
struct Choices {
    compile: Taken,
    run: Taken,
}

/// Compile and run `program` with the console [`CONSOLE`], inside `seed`'s scope when there is
/// one.
fn run(program: &Program, seed: Option<u64>) -> Run {
    run_counting(program, seed).0
}

/// [`run`], and the open values the chooser took.
fn run_counting(program: &Program, seed: Option<u64>) -> (Run, Choices) {
    let go = || {
        choice_sampling::take_counts();
        let (kore, initial) = compile(program.source, program.program);
        let mut backend = Backend::new(&kore, "MAIN", BackendOptions::default()).unwrap();
        let definition = backend.select_definition(None).unwrap();
        let pattern = definition
            .admit_unverified(&initial, &[])
            .internalize_pattern()
            .unwrap();
        let compile = choice_sampling::take_counts();
        let result = execute_with_io_state(
            &definition,
            pattern,
            ExecutionOptions {
                evaluation: EvaluationMode::Execution,
                ..ExecutionOptions::default()
            },
            ExecutionIoState::new(CONSOLE.to_vec()),
        );
        let choices = Choices {
            compile,
            run: choice_sampling::take_counts(),
        };
        let run = Run {
            leaves: result
                .leaves
                .iter()
                .map(|leaf| {
                    (
                        format!("{:?}", leaf.pattern),
                        format!("{:?}", leaf.halt_reason),
                    )
                })
                .collect(),
            classes: result
                .implementation_chosen_values
                .iter()
                .map(|value| value.class.name())
                .collect(),
        };
        (run, choices)
    };
    match seed {
        Some(seed) => choice_sampling::with_seed(NonZeroU64::new(seed).unwrap(), go),
        None => go(),
    }
}

/// Every probe's default run lists its class's mark, takes no value under no seed, and some seed
/// gives the probe other leaves and takes a value of the class: the chooser reaches the class's
/// computing site.
#[test]
fn every_class_probe_reads_a_mark_and_some_seed_changes_it() {
    for probe in POWER {
        let context = format!("{} ({})", probe.program, probe.class);
        let (default, unseeded) = run_counting(probe, None);
        assert!(!default.leaves.is_empty(), "{context}: {default:#?}");
        assert!(
            default.classes.contains(probe.class),
            "{context}: the default run lists the class: {default:#?}"
        );
        assert!(
            unseeded.compile.is_empty() && unseeded.run.is_empty(),
            "{context}: no value is taken without a seed: {unseeded:?}"
        );
        let mut changed = false;
        let mut taken = false;
        for seed in SEEDS {
            let (seeded, choices) = run_counting(probe, Some(seed));
            changed |= seeded.leaves != default.leaves;
            taken |=
                choices.compile.contains_key(probe.class) || choices.run.contains_key(probe.class);
        }
        assert!(
            changed,
            "{context}: some seed changes the leaves of {default:#?}"
        );
        assert!(taken, "{context}: some seed takes a value of the class");
    }
}

/// Every control's default run has an empty list, and every seed gives it the same leaves and
/// list and takes no value while running: the chooser takes only values the definition leaves
/// open. (Compiling `FRESH` takes associations, of its rules with two names, which the control's
/// run does not apply.)
#[test]
fn no_seed_changes_a_control_probe() {
    for control in CONTROLS {
        let context = format!("{} ({} control)", control.program, control.class);
        let default = run(control, None);
        assert!(!default.leaves.is_empty(), "{context}: {default:#?}");
        assert!(
            default.classes.is_empty(),
            "{context}: the default run is unmarked: {default:#?}"
        );
        for seed in SEEDS {
            let (seeded, choices) = run_counting(control, Some(seed));
            assert_eq!(seeded, default, "{context}: seed {seed} changes the run");
            assert!(
                choices.run.is_empty(),
                "{context}: seed {seed}'s run takes {:?}",
                choices.run
            );
        }
    }
}
