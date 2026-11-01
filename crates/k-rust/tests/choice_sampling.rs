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
//! there), for the seeds 1 to 3 and once without a scope, with a console and in `Execution`
//! mode, where k-rust takes its own value for every open application.
//! The chooser's count of the open values each class's sites took (`choice_sampling::take_counts`)
//! is read apart for the compilation and the run: a probe's class takes one under some seed, and
//! a control's run takes none. The classes and sites the chooser has no other value for
//! (`literal`, `String2Token` naming no element; `k_rust_backend::choice_sampling`) are asserted
//! marked and unchanged under every seed instead.

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

/// GAP's classes (`docs/compatibility.md`, "Implementation-chosen hook values"): a Float
/// rounding, and the values and `\bottom`s of hooks outside their described domains, each probe
/// beside a control on which the value is determined; and the values the amendments AM-1, AM-2,
/// AM-3 and AM-7 of `docs/amendments.md` determine, as controls. A `\bottom` probe reaches the
/// pick as a step's result (`ord`, `upd`, `dec`, `rpl`, `add`), as a condition whose rule then
/// gives way to its `owise` rule (`cnd`), and as an operand a decided `#if` discards, whose
/// definedness alone is read (`skip`, a `suspend`ed evaluation).
const GAP: &str = r#"
module MAIN
  imports INT
  imports FLOAT
  imports STRING
  imports BYTES
  imports LIST
  imports K-EQUAL
  syntax String ::= Keccak256(Bytes) [function, hook(KRYPTO.keccak256)]
                  | ECDSAPubKey(Bytes) [function, hook(KRYPTO.ecdsaPubKey)]
  syntax Bytes ::= Keccak256raw(Bytes) [function, hook(KRYPTO.keccak256raw)]
                 | ECDSARecover(Bytes, Int, Bytes, Bytes) [function, hook(KRYPTO.ecdsaRecover)]
  syntax G1Point ::= g1(Int, Int)
  syntax G1Point ::= BN128Add(G1Point, G1Point) [function, hook(KRYPTO.bn128add)]
  syntax Pgm ::= kec(Bytes) | kraw(Bytes) | s2b(String) | b2s(Bytes) | enc(String) | i2f(Int)
               | rnd(Float) | f2i(Float) | rt(Float, Int) | fl(Float) | flinf(Float) | rec(Int)
               | pub(Bytes) | sub(Int) | fnd(Int) | rpl(Int) | ord(String) | upd(Int)
               | dec(Bytes) | cnd(String) | skip(Int) | add(Int, Int) | done(KItem)
  configuration <k> $PGM:Pgm </k>
  rule kec(B) => done(Keccak256(B))
  rule kraw(B) => done(Keccak256raw(B))
  rule s2b(S) => done(String2Bytes(S))
  rule b2s(B) => done(Bytes2String(B))
  rule enc(S) => done(encodeBytes("UTF-8", S))
  rule i2f(I) => done(Int2Float(I, 24, 8))
  rule rnd(F) => done(roundFloat(F, 24, 8))
  rule f2i(F) => done(Float2Int(F))
  rule rt(F, N) => done(rootFloat(F, N))
  rule fl(F) => done(floorFloat(F))
  rule flinf(F) => done(floorFloat(F /Float 0.0))
  rule rec(V) => done(ECDSARecover(b"", V, b"", b""))
  rule pub(B) => done(ECDSAPubKey(B))
  rule sub(I) => done(substrString("abc", I, I))
  rule fnd(I) => done(findString("abc", "a", I))
  rule rpl(I) => done(replaceAtBytes(b"\x01\x02\x03", I, b"\x00\x00"))
  rule ord(S) => done(ordChar(S))
  rule upd(I) => done(ListItem(1) [ I <- 0 ])
  rule dec(B) => done(decodeBytes("UTF-8", B))
  rule cnd(S) => done(1) requires ordChar(S) ==Int 0
  rule cnd(_) => done(2) [owise]
  rule skip(I) => done(#if true #then 1 #else size(ListItem(1) [ I <- 0 ]) #fi)
  rule add(X, Y) => done(BN128Add(g1(0, 0), g1(X, Y)))
endmodule
"#;

/// Open values inside an operand a decided `#if` discards, whose definedness alone is read (a
/// `suspend`ed evaluation, `k_rust_backend::path_facts`): `substrString` of an empty range
/// strictly inside its string (`outside-domain`, defined in every model: the symbol is
/// `total`), a failed `ECDSARecover` (`outside-domain` at a partial symbol, which a model may
/// leave undefined), and `replaceAtBytes` at a negative start at a symbol `RA` declared `total`
/// (`\bottom` is no model there, so k-rust takes no outcome at all), discarded (`rs`) and as a
/// step's result (`ra`).
const SUSPENDED: &str = r#"
module MAIN
  imports INT
  imports STRING
  imports BYTES
  imports K-EQUAL
  syntax Bytes ::= ECDSARecover(Bytes, Int, Bytes, Bytes) [function, hook(KRYPTO.ecdsaRecover)]
                 | RA(Bytes, Int, Bytes) [function, total, hook(BYTES.replaceAt)]
  syntax Pgm ::= ss(Int) | sr(Int) | rs(Int) | ra(Int) | done(KItem)
  configuration <k> $PGM:Pgm </k>
  rule ss(I) => done(#if true #then 1 #else lengthString(substrString("abc", I, I)) #fi)
  rule sr(V) => done(#if true #then 1 #else lengthBytes(ECDSARecover(b"", V, b"", b"")) #fi)
  rule rs(I) => done(#if true #then 1 #else lengthBytes(RA(b"\x01\x02\x03", I, b"\x00\x00")) #fi)
  rule ra(I) => done(RA(b"\x01\x02\x03", I, b"\x00\x00"))
endmodule
"#;

/// The classes and sites the chooser leaves at k-rust's value, each with its reason
/// (`k_rust_backend::choice_sampling`): a literal's element (`literal`, a machine integer its
/// width cannot hold: fixed when the definition is loaded), and `String2Token` of a text naming
/// no element of its sort (`outside-domain`: a value of the declared sort is a token its lexical
/// syntax admits, which the arguments do not give).
const EXEMPT: &str = r#"
module MAIN
  imports INT
  imports FLOAT
  imports MINT
  imports STRING
  syntax Int ::= String2PInt(String) [function, hook(STRING.string2token)]
  syntax MInt{8} ::= m8() [function]
  syntax Pgm ::= inf(Int) | wide(Int) | tok(String) | done(KItem)
  configuration <k> $PGM:Pgm </k>
  rule [inf]: inf(_) => done(Infinity)
  rule [wide]: wide(_) => done(256p8)
  rule [m8]: m8() => 1p8
  rule tok(S) => done(String2PInt(S))
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

/// The console input of every run: `rd(3)` reads its three characters.
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
    program("fresh-association", FRESH, "mk(3)"),
    program("float-rounding", GAP, "f2i(2.5)"),
    program("outside-domain", GAP, "rec(29)"),
    program("outside-domain", GAP, r#"pub(b"")"#),
    program("outside-domain", GAP, "rt(-4.0, 2)"),
    program("outside-domain", GAP, "sub(1)"),
    program("outside-domain", GAP, "fnd(-1)"),
    program("outside-domain", GAP, "rpl(-1)"),
    program("outside-domain", GAP, "add(1, 3)"),
    program("outside-domain", GAP, r#"ord("ab")"#),
    program("outside-domain", GAP, "upd(5)"),
    program("outside-domain", GAP, r#"dec(b"\xff")"#),
    program("outside-domain", GAP, r#"cnd("ab")"#),
    program("outside-domain", GAP, "skip(5)"),
];

/// Programs beside each probe whose value of the class is determined, and programs whose value
/// the console contract (`console`) or an amendment (`AM-<n>`) determines, labelled by that text.
/// GAP A2: the class-labelled controls include the conversions, the inexact root and the
/// roundings to an integer the amendments determine (`docs/amendments.md`, AM-4 to AM-6; K5's
/// probes of `float-rounding` and `outside-domain`), and the `Infinity` lexeme (AM-8; K5's
/// exempted `literal` probe).
const CONTROLS: &[Program] = &[
    program("order", PROBES, "keysOne(1)"),
    program("item", PROBES, "choiceOne(1)"),
    program("float-destination", PROBES, "mixed(0.5)"),
    program("nan-sign", PROBES, "sg(-0.0)"),
    program("letter-case", PROBES, "b2s(9)"),
    program("signed-zero", PROBES, "mz(1.0)"),
    program("fresh-name", PROBES, "sub(app(x, x), 1, x)"),
    program("console", PROBES, "rd(3)"),
    program("console", PROBES, "rd(1)"),
    program("fresh-association", FRESH, "one(3)"),
    program("AM-1", GAP, r#"s2b("\xe9")"#),
    program("AM-1", GAP, r#"b2s(b"\xc3\xa9")"#),
    program("AM-1", GAP, r#"enc("\xe9")"#),
    program("AM-2", GAP, r#"kec(b"")"#),
    program("AM-2", GAP, r#"kraw(b"")"#),
    program("AM-3", GAP, "add(1, 2)"),
    program("AM-7", GAP, "rpl(1)"),
    program("float-rounding", GAP, "i2f(3)"),
    program("float-rounding", GAP, "f2i(2.4)"),
    program("float-rounding", GAP, "rt(4.0, 2)"),
    program("float-rounding", GAP, "i2f(16777217)"),
    program("float-rounding", GAP, "i2f(0)"),
    program("float-rounding", GAP, "rnd(0.1)"),
    program("float-rounding", GAP, "rt(2.0, 3)"),
    program("outside-domain", GAP, "fl(1.5)"),
    program("outside-domain", GAP, "fl(0.5)"),
    program("outside-domain", GAP, "flinf(1.0)"),
    program("literal", EXEMPT, "inf(0)"),
    program("outside-domain", GAP, "sub(0)"),
    program("outside-domain", GAP, "fnd(0)"),
    program("outside-domain", GAP, "rpl(0)"),
    program("outside-domain", GAP, r#"ord("a")"#),
    program("outside-domain", GAP, "upd(0)"),
    program("outside-domain", GAP, r#"cnd("a")"#),
    program("outside-domain", GAP, "skip(0)"),
];

/// Programs whose run reads a value of a class, or a site, the chooser exempts ([`EXEMPT`]).
const EXEMPTED: &[Program] = &[
    program("literal", EXEMPT, "wide(0)"),
    program("outside-domain", EXEMPT, r#"tok("x")"#),
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
    // Every probe is run and the ones no seed changes are reported together.
    let mut unchanged = Vec::new();
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
        if !(changed && taken) {
            unchanged.push(format!(
                "{context}: changed {changed}, taken {taken}, default {default:?}"
            ));
        }
    }
    assert!(
        unchanged.is_empty(),
        "probes that no seed changes, or whose class no seed takes a value of: {unchanged:#?}"
    );
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

/// Every exempt program's default run lists its class's mark, and no seed changes it or takes a
/// value of the class: the chooser has no other value for it ([`EXEMPT`]), so a harness over
/// unmarked runs tests nothing for it, and its mark is the run's only record.
#[test]
fn exempt_classes_are_marked_and_no_seed_takes_another_value_of_them() {
    for exempt in EXEMPTED {
        let context = format!("{} ({} exempt)", exempt.program, exempt.class);
        let default = run(exempt, None);
        assert!(!default.leaves.is_empty(), "{context}: {default:#?}");
        assert!(
            default.classes.contains(exempt.class),
            "{context}: the default run lists the class: {default:#?}"
        );
        for seed in SEEDS {
            let (seeded, choices) = run_counting(exempt, Some(seed));
            assert_eq!(seeded, default, "{context}: seed {seed} changes the run");
            assert!(
                !choices.compile.contains_key(exempt.class)
                    && !choices.run.contains_key(exempt.class),
                "{context}: seed {seed} takes a value of the class: {choices:?}"
            );
        }
    }
}

/// A value taken where only the application's definedness is read (an operand a decided `#if`
/// discards) is counted exactly where its mark is noted. Where every model defines the
/// application (`substrString`, `total`) the value does not reach the run's result, the mark is
/// dropped, and the chooser counts no value taken, so an unmarked run takes none. Where a model
/// may leave it undefined (a failed `ECDSARecover` at a partial symbol) the definedness read is
/// the pick: the run is marked and the value is counted. Where the description gives no value
/// and the symbol is `total` (`replaceAtBytes` at a negative start), `\bottom` is no model and
/// k-rust takes no outcome, discarded (`rs(-1)`) or as a step's result (`ra(-1)`): no seed
/// takes one, and the run is unchanged and unmarked.
#[test]
fn a_value_taken_where_only_definedness_is_read_is_counted_as_its_mark_is() {
    let cases = [
        (program("outside-domain", SUSPENDED, "ss(1)"), false),
        (program("outside-domain", SUSPENDED, "sr(29)"), true),
        (program("outside-domain", SUSPENDED, "rs(-1)"), false),
        (program("outside-domain", SUSPENDED, "ra(-1)"), false),
    ];
    let mut failures = Vec::new();
    for (case, marked) in &cases {
        let context = format!("{} ({})", case.program, case.class);
        let default = run(case, None);
        assert!(!default.leaves.is_empty(), "{context}: {default:#?}");
        if default.classes.contains(case.class) != *marked {
            failures.push(format!(
                "{context}: default marked != {marked}: {default:?}"
            ));
        }
        for seed in SEEDS {
            let (seeded, choices) = run_counting(case, Some(seed));
            if seeded != default {
                failures.push(format!(
                    "{context}: seed {seed} changes the run (leaves changed: {}, classes {:?})",
                    seeded.leaves != default.leaves,
                    seeded.classes
                ));
            }
            if choices.run.contains_key(case.class) != *marked {
                failures.push(format!(
                    "{context}: seed {seed} takes a value != {marked}: {:?}",
                    choices.run
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}
