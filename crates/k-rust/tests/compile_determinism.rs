//! Loading and compiling equal inputs gives equal results, in any process, on any thread and on
//! every call (`docs/compatibility.md`, "Determinism and concurrency").
//!
//! The fixtures exercise the compile passes whose output a hash seed or an address could reach:
//! strictness and a `Map` cell, `owise`, fresh constants and a macro, a Markdown definition with
//! a selector, and `anywhere` and `simplification` rules. Two child processes of this test binary
//! have independent random hash seeds and address layouts, so output that depended on either
//! would differ between them. The detection is probabilistic: an order that depends on the seed
//! over a small map can agree in all three processes by chance, so one passing run is evidence,
//! not proof.

use std::{
    path::{Path, PathBuf},
    process::Command,
};

use indoc::indoc;
use k_rust::{
    builtin::embedded,
    kompile::{
        CompilationBackend, CompileOptions, CompiledKoreArtifacts, compile_loaded_definition,
    },
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

/// A definition to compile: its logical file name, text, main module and Markdown selector.
struct Fixture {
    file: &'static str,
    text: &'static str,
    main: &'static str,
    selector: &'static str,
}

/// An IMP-like language: strict operators, a configuration with a `Map` cell, rules that read
/// and update it, and a function with an `owise` rule.
const IMPISH: Fixture = Fixture {
    file: "impish.k",
    text: indoc! {r#"
        module IMPISH
          imports DOMAINS
          syntax AExp ::= Int | Id
                        | AExp "+" AExp [left, strict]
          syntax Stmt ::= Id "=" AExp ";" [strict(2)]
                        | Stmt Stmt [left]
          syntax KResult ::= Int
          configuration <T> <k> $PGM:Stmt </k> <state> .Map </state> </T>
          rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>
          rule I1:Int + I2:Int => I1 +Int I2
          rule <k> X = I:Int ; => .K ...</k> <state> S => S [X <- I] </state>
          rule S1:Stmt S2:Stmt => S1 ~> S2
          syntax Int ::= sign(Int) [function]
          rule sign(I) => 1 requires I >Int 0
          rule sign(_) => 0 [owise]
        endmodule
    "#},
    main: "IMPISH",
    selector: "k",
};

/// Fresh constants and a macro.
const FRESH_MACRO: Fixture = Fixture {
    file: "fresh-macro.k",
    text: indoc! {r#"
        module FRESH-MACRO
          imports DOMAINS
          syntax KItem ::= "start" | item(Int)
          syntax Int ::= twice(Int) [macro]
          rule twice(I) => I +Int I
          configuration <k> start </k> <items> .List </items>
          rule <k> start => item(twice(!N:Int)) ... </k>
          rule <k> item(I) => .K ... </k> <items> L => L ListItem(I) </items>
        endmodule
    "#},
    main: "FRESH-MACRO",
    selector: "k",
};

/// A Markdown definition of two selected code blocks and one the selector leaves out.
const MARKDOWN: Fixture = Fixture {
    file: "markdown.md",
    text: indoc! {r#"
        # A Markdown definition

        ```k
        module MD-SYNTAX
          imports INT-SYNTAX
          syntax Exp ::= Int | Exp "*" Exp [left, strict]
        endmodule
        ```

        ```{.k .skip}
        module MD-LEFT-OUT
        endmodule
        ```

        ```k
        module MD
          imports MD-SYNTAX
          imports INT
          syntax KResult ::= Int
          rule I1:Int * I2:Int => I1 *Int I2
        endmodule
        ```
    "#},
    main: "MD",
    selector: "k & ! skip",
};

/// `anywhere` rules and a `simplification` rule.
const ANYWHERE_SIMPLIFICATION: Fixture = Fixture {
    file: "anywhere-simplification.k",
    text: indoc! {r#"
        module ANYWHERE-SIMPLIFICATION
          imports INT
          syntax Val ::= v(Int)
          syntax Exp ::= Val | neg(Exp) | wrap(Exp)
          rule neg(neg(E)) => E [anywhere]
          rule wrap(E) => E [anywhere]
          syntax Int ::= f(Int) [function]
          rule f(I) => I +Int 1
          rule f(I) +Int 0 => f(I) [simplification]
        endmodule
    "#},
    main: "ANYWHERE-SIMPLIFICATION",
    selector: "k",
};

const FIXTURES: [&Fixture; 4] = [&IMPISH, &FRESH_MACRO, &MARKDOWN, &ANYWHERE_SIMPLIFICATION];

/// A definition whose rule adds a Boolean to an integer: its rule does not parse, so it fails
/// to load.
const ILL_SORTED: Fixture = Fixture {
    file: "ill-sorted.k",
    text: indoc! {r#"
        module ILL-SORTED
          imports INT
          imports BOOL
          syntax KItem ::= "go"
          rule go => true +Int 1
        endmodule
    "#},
    main: "ILL-SORTED",
    selector: "k",
};

/// A definition that loads and fails to compile, with one diagnostic per strict production:
/// each names a result sort that has no sort predicate, which heating and cooling need.
const HEAT_COOL: Fixture = Fixture {
    file: "heat-cool.k",
    text: indoc! {r#"
        module HEAT-COOL
          imports BOOL
          syntax 8
          syntax 9
          syntax KResult
          syntax Exp ::= foo(Exp) [strict, result(8)]
                       | bar(Exp) [strict, result(9)]
                       | baz(Exp) [strict, result(8)]
                       | "e"
        endmodule
    "#},
    main: "HEAT-COOL",
    selector: "k",
};

/// Load `fixture` with the embedded prelude for the Rust backend and compile it; a load or
/// compile failure is its `Debug` text, prefixed with `load error` or `compile error`.
fn compile(fixture: &Fixture) -> Result<CompiledKoreArtifacts, String> {
    compile_source(ResolvedSource::new(fixture.file, fixture.text), fixture)
}

/// [`compile`] with `source` as the entry source in place of `fixture`'s file and text.
fn compile_source(
    source: ResolvedSource,
    fixture: &Fixture,
) -> Result<CompiledKoreArtifacts, String> {
    let prelude = embedded("prelude.md").expect("the embedded prelude exists");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        source,
        fixture.main,
        &mut resolver,
        &LoadOptions {
            markdown_selector: fixture.selector.into(),
            implicit_sources: vec![prelude],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .map_err(|error| format!("load error: {error:#?}"))?;
    compile_loaded_definition(&loaded, CompileOptions::default())
        .map_err(|error| format!("compile error: {error:#?}"))
}

/// The text of `fixture`'s compile that a process writes: the `Debug` text of the whole
/// `CompiledKoreArtifacts`, which holds the three KORE texts and every other field.
fn artifact_text(fixture: &Fixture) -> String {
    let artifacts =
        compile(fixture).unwrap_or_else(|error| panic!("{} compiles: {error}", fixture.file));
    format!("{artifacts:#?}")
}

/// The `Debug` text of the failure of `fixture`, which must fail in the stage `prefix` names.
fn failure_text(fixture: &Fixture, prefix: &str) -> String {
    match compile(fixture) {
        Ok(_) => panic!("{} compiled", fixture.file),
        Err(error) => {
            assert!(error.starts_with(prefix), "{}: {error}", fixture.file);
            error
        }
    }
}

/// The texts one process writes in `mode`: one per fixture, or one per failure.
fn texts(mode: &str) -> Vec<(String, String)> {
    match mode {
        ARTIFACTS => FIXTURES
            .iter()
            .map(|fixture| (fixture.file.to_owned(), artifact_text(fixture)))
            .collect(),
        FAILURE => vec![
            (
                ILL_SORTED.file.to_owned(),
                failure_text(&ILL_SORTED, "load error"),
            ),
            (
                HEAT_COOL.file.to_owned(),
                failure_text(&HEAT_COOL, "compile error"),
            ),
        ],
        _ => panic!("unknown mode {mode}"),
    }
}

#[test]
fn compiling_twice_in_one_process_gives_equal_artifacts() {
    for fixture in FIXTURES {
        let first =
            compile(fixture).unwrap_or_else(|error| panic!("{} compiles: {error}", fixture.file));
        let second =
            compile(fixture).unwrap_or_else(|error| panic!("{} compiles: {error}", fixture.file));
        assert!(first == second, "{}: two compiles differ", fixture.file);
    }
}

/// The variable naming the directory a child process writes its texts to; the child does
/// nothing without it.
const CHILD_DIRECTORY: &str = "K_RUST_TEST_COMPILE_DETERMINISM_DIRECTORY";
/// The variable naming what the child writes: [`ARTIFACTS`] or [`FAILURE`].
const CHILD_MODE: &str = "K_RUST_TEST_COMPILE_DETERMINISM_MODE";
const ARTIFACTS: &str = "artifacts";
const FAILURE: &str = "failure";

/// The work of a child process of [`compiled_in_two_processes`]: writes its texts to the
/// directory it is given. It does nothing unless a parent runs it.
#[test]
fn compile_determinism_child() {
    let Some(directory) = std::env::var_os(CHILD_DIRECTORY) else {
        return;
    };
    let mode = std::env::var(CHILD_MODE).expect("the parent names the mode");
    for (file, text) in texts(&mode) {
        std::fs::write(Path::new(&directory).join(file), text).expect("the child writes its texts");
    }
}

/// Run [`compile_determinism_child`] in two processes of this test binary in `mode`, and assert
/// that both wrote, byte for byte, the texts this process computes.
fn compiled_in_two_processes(mode: &str) {
    /// Removes the children's directory however the test ends.
    struct Remove(PathBuf);
    impl Drop for Remove {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let root = std::env::temp_dir().join(format!(
        "k-rust-compile-determinism-{mode}-{}",
        std::process::id()
    ));
    let _remove = Remove(root.clone());
    let expected = texts(mode);
    for child in ["first", "second"] {
        let directory = root.join(child);
        std::fs::create_dir_all(&directory).expect("the child's directory is created");
        let output = Command::new(std::env::current_exe().expect("the test binary is known"))
            .args(["--exact", "compile_determinism_child", "--nocapture"])
            .args(["--test-threads", "1"])
            .env(CHILD_DIRECTORY, &directory)
            .env(CHILD_MODE, mode)
            .output()
            .expect("the test binary re-runs itself");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            output.status.success() && stdout.contains("1 passed"),
            "the {child} child failed ({}):\n{stdout}\n{}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        );
        for (file, text) in &expected {
            let written =
                std::fs::read_to_string(directory.join(file)).expect("the child wrote its text");
            assert!(
                written == *text,
                "{file}: the {child} child wrote other bytes than this process computes"
            );
        }
    }
}

#[test]
fn compiling_in_two_processes_gives_identical_bytes() {
    compiled_in_two_processes(ARTIFACTS);
}

/// A definition that fails to load and one that loads and fails to compile give the same error
/// in two processes.
#[test]
fn a_failed_compile_fails_identically_across_processes() {
    compiled_in_two_processes(FAILURE);
}

/// A compile on a thread with a small stack and compiles on concurrent threads give the
/// artifacts of a compile on the test's own thread.
#[test]
fn compiling_on_other_threads_gives_equal_artifacts() {
    let expected = compile(&IMPISH).expect("the fixture compiles");
    let small_stack = std::thread::Builder::new()
        .stack_size(512 << 10)
        .spawn(|| compile(&IMPISH).expect("the fixture compiles"))
        .expect("the thread starts")
        .join()
        .expect("the compile does not panic");
    assert!(
        small_stack == expected,
        "a 512 KiB thread compiled other artifacts"
    );
    let concurrent = std::thread::scope(|scope| {
        let compiles = (0..4)
            .map(|_| scope.spawn(|| compile(&IMPISH).expect("the fixture compiles")))
            .collect::<Vec<_>>();
        compiles
            .into_iter()
            .map(|compile| compile.join().expect("a compile does not panic"))
            .collect::<Vec<_>>()
    });
    for (thread, artifacts) in concurrent.iter().enumerate() {
        assert!(
            *artifacts == expected,
            "concurrent thread {thread} compiled other artifacts"
        );
    }
}

/// The resolver's identity of a source is an input: the same text and logical name under two
/// identities gives two `Source` attributes, so two different KORE texts, while one identity
/// gives identical texts.
#[test]
fn the_resolver_identity_of_a_source_is_an_input() {
    let under = |identity: &str| {
        compile_source(
            ResolvedSource::new(identity, FRESH_MACRO.text).with_logical(FRESH_MACRO.file),
            &FRESH_MACRO,
        )
        .expect("the fixture compiles")
        .definition_kore
    };
    let first = under("/checkout-a/fresh-macro.k");
    assert!(first.contains("Source(/checkout-a/fresh-macro.k)"));
    assert_eq!(first, under("/checkout-a/fresh-macro.k"));
    let second = under("/checkout-b/fresh-macro.k");
    assert!(second.contains("Source(/checkout-b/fresh-macro.k)"));
    assert_ne!(first, second);
}
