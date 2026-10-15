#![cfg(feature = "cli")]

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::Write,
    path::{Path, PathBuf},
    process::{Command, Output, Stdio},
    sync::atomic::{AtomicU64, Ordering},
};

use k_rust::kore::{ast::Pattern, parser::parse_definition, parser::parse_pattern};
use regex::Regex;

#[path = "support/execution_sources.rs"]
mod execution_sources;
#[path = "support/line_anchors.rs"]
mod line_anchors;
use execution_sources::{NO_EVALUATOR, PINNED_PLUGIN_BN128, SEARCH_BOUND, SIZE_BOUND};
#[path = "support/proof_sources.rs"]
mod proof_sources;
use proof_sources::{
    ANYWHERE_OVERLOAD_REMAINDER, DEFPROBE, DEFPROBE_REFUSED_SPEC, DEFPROBE_SPEC,
    LATER_BINDING_KEPT, LATER_BINDING_RECOVERED, LATER_BINDING_RULE, LET_PARTIAL_CONDITION,
    NEGATIVE_POWER, TERM_READ_AS_PREDICATE_CLAIMS, UNDEFINED_STEP,
};

/// A `KRUST-PROVENANCE` document written by the version 7 writer (k-rust `480a0d3b`), as an
/// artifact or prepared directory of that krust holds.
const PROVENANCE_VERSION_7: &str = include_str!("fixtures/provenance-version-7.json");

const DEFINITION: &str = r#"
requires "base.k"

module MAIN
  imports BASE
  syntax Exp ::= Int
  syntax Exp ::= Exp "+" Exp [comm, function, symbol(_+_)]
  rule 1 + 2 => 2 + 1 [simplification, comm]
endmodule
"#;

const BASE: &str = r#"
module BASE
  syntax Int ::= r"[0-9]+" [token]
endmodule
"#;

#[test]
fn reports_the_packaged_version() {
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("--version")
        .output()
        .unwrap();

    assert!(output.status.success());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        format!("krust {}\n", env!("CARGO_PKG_VERSION"))
    );
}

/// A diagnostic-work limit that cannot be read is refused before anything is parsed, rather than
/// replaced by the default the user set the variable to change.
#[test]
fn refuses_an_unreadable_parse_diagnostic_work_limit() {
    let (root, definition) = fixture();
    for value in ["1e6", "-1"] {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .env("KRUST_PARSE_DIAGNOSTIC_WORK", value)
            .args(["kcompile", definition.to_str().unwrap(), "-m", "MAIN", "-o"])
            .arg(root.join(format!("refused-{value}")))
            .stdin(std::process::Stdio::null())
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{value:?}");
        assert_eq!(
            String::from_utf8(output.stderr).unwrap(),
            format!(
                "error: KRUST_PARSE_DIAGNOSTIC_WORK must be `unlimited` or a number of chart \
                 steps, not `{value}`\n"
            ),
            "{value:?}"
        );
        assert!(!root.join(format!("refused-{value}")).exists());
    }
    // An empty value reads as unset.
    for value in ["unlimited", "1_000_000", ""] {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .env("KRUST_PARSE_DIAGNOSTIC_WORK", value)
            .args(["kcompile", definition.to_str().unwrap(), "-m", "MAIN", "-o"])
            .arg(root.join("accepted"))
            .stdin(std::process::Stdio::null())
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{value:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    fs::remove_dir_all(root).unwrap();
}

fn fixture() -> (PathBuf, PathBuf) {
    static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);
    let nonce = NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed);
    let root = std::env::temp_dir().join(format!("k-rust-cli-{}-{nonce}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let definition = root.join("definition.k");
    fs::write(&definition, DEFINITION).unwrap();
    fs::write(root.join("base.k"), BASE).unwrap();
    (root, definition)
}

mod watchdog {
    use std::{
        path::Path,
        process::{Command, Output, Stdio},
        thread,
        time::{Duration, Instant},
    };

    pub(super) enum Input<'a> {
        Source(&'a Path),
        Compiled(&'a Path),
    }

    pub(super) enum Compilation<'a> {
        Run { syntax_module: &'a str },
        Proof { definition_module: &'a str },
    }

    pub(super) enum Request<'a> {
        Compile {
            source: &'a Path,
            main_module: &'a str,
            output: &'a Path,
            kind: Compilation<'a>,
        },
        Krun {
            input: Input<'a>,
            main_module: &'a str,
            syntax_module: &'a str,
            sort: &'a str,
            expression: &'a str,
        },
        Kprove {
            input: Input<'a>,
            main_module: &'a str,
            definition_module: &'a str,
            claim: &'a str,
            smt_prelude: &'a Path,
        },
        KoreExec {
            definition: &'a Path,
            module: &'a str,
            pattern: &'a Path,
            search_final: bool,
        },
        KoreImplies {
            definition: &'a Path,
            module: &'a str,
            antecedent: &'a Path,
            consequent: &'a Path,
        },
    }

    const COMPILATION_BUDGET: Duration = Duration::from_secs(120);
    const BACKEND_BUDGET: Duration = Duration::from_secs(20);

    enum Scope {
        Compilation,
        SourceAndBackend,
        Backend,
    }

    impl Scope {
        fn policy(&self) -> (&'static str, Duration) {
            match self {
                Self::Compilation => ("compilation", COMPILATION_BUDGET),
                Self::SourceAndBackend => ("source-plus-backend", COMPILATION_BUDGET),
                Self::Backend => ("backend", BACKEND_BUDGET),
            }
        }
    }

    pub(super) fn output(request: Request<'_>) -> Output {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        let scope = match request {
            Request::Compile {
                source,
                main_module,
                output,
                kind,
            } => {
                command
                    .arg("kcompile")
                    .arg(source)
                    .args(["--main-module", main_module]);
                match kind {
                    Compilation::Run { syntax_module } => {
                        command.args(["--syntax-module", syntax_module]);
                    }
                    Compilation::Proof { definition_module } => {
                        command.args(["--definition-module", definition_module, "--for-proving"]);
                    }
                }
                command.arg("--output-directory").arg(output);
                Scope::Compilation
            }
            Request::Krun {
                input,
                main_module,
                syntax_module,
                sort,
                expression,
            } => {
                command.arg("krun");
                let scope = match input {
                    Input::Source(source) => {
                        command.arg(source);
                        Scope::SourceAndBackend
                    }
                    Input::Compiled(definition) => {
                        command.arg("--definition").arg(definition);
                        Scope::Backend
                    }
                };
                command.args([
                    "--main-module",
                    main_module,
                    "--syntax-module",
                    syntax_module,
                    "--sort",
                    sort,
                    "--expression",
                    expression,
                    "--strategy",
                    "all",
                    "--io",
                    "off",
                ]);
                scope
            }
            Request::Kprove {
                input,
                main_module,
                definition_module,
                claim,
                smt_prelude,
            } => {
                command.arg("kprove");
                let scope = match input {
                    Input::Source(source) => {
                        command.arg(source);
                        Scope::SourceAndBackend
                    }
                    Input::Compiled(definition) => {
                        command.arg("--compiled-definition").arg(definition);
                        Scope::Backend
                    }
                };
                command
                    .args([
                        "--main-module",
                        main_module,
                        "--definition-module",
                        definition_module,
                        "--claim",
                        claim,
                        "--smt-prelude",
                    ])
                    .arg(smt_prelude);
                scope
            }
            Request::KoreExec {
                definition,
                module,
                pattern,
                search_final,
            } => {
                command
                    .arg("kore-exec")
                    .arg(definition)
                    .args(["--module", module, "--pattern"])
                    .arg(pattern);
                if search_final {
                    command.arg("--search-final");
                }
                Scope::Backend
            }
            Request::KoreImplies {
                definition,
                module,
                antecedent,
                consequent,
            } => {
                command
                    .arg("kore-implies")
                    .arg(definition)
                    .args(["--module", module, "--antecedent"])
                    .arg(antecedent)
                    .arg("--consequent")
                    .arg(consequent);
                Scope::Backend
            }
        };
        run(command, scope)
    }

    /// Run a backend-only `krust` invocation (a `krun --definition` of a compiled definition)
    /// under the backend budget, so a run that does not end fails the test.
    pub(super) fn backend(command: Command) -> Output {
        run(command, Scope::Backend)
    }

    fn run(mut command: Command, scope: Scope) -> Output {
        let (class, duration) = scope.policy();
        let mut child = command
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let deadline = Instant::now() + duration;
        loop {
            if child.try_wait().unwrap().is_some() {
                return child.wait_with_output().unwrap();
            }
            if Instant::now() >= deadline {
                child.kill().unwrap();
                let output = child.wait_with_output().unwrap();
                panic!("{class} operation exceeded the watchdog ({duration:?}): {output:?}");
            }
            thread::sleep(Duration::from_millis(10));
        }
    }
}

#[test]
fn kore_exec_zero_query_run_accepts_an_inconsistent_smt_prelude() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        include_str!("fixtures/inconsistent-smt-prelude.kore"),
    )
    .unwrap();
    let initial = root.join("initial.kore");
    fs::write(&initial, "\\dv{SortInt{}}(\"1\")\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            initial.to_str().unwrap(),
            "--depth",
            "0",
        ])
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert_eq!(output.stdout, b"\\dv{SortInt{}}(\"1\")\n");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_exec_stops_after_a_prelude_failure_before_an_unbounded_sibling() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        include_str!("fixtures/inconsistent-smt-prelude-loop.kore"),
    )
    .unwrap();
    let initial = root.join("initial.kore");
    fs::write(
        &initial,
        r#"\or{SortInt{}}(probe{}(X:SortInt{}), wrap{}(\dv{SortInt{}}("0")))"#,
    )
    .unwrap();
    let output = watchdog::output(watchdog::Request::KoreExec {
        definition: &definition,
        module: "MAIN",
        pattern: &initial,
        search_final: false,
    });
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_eq!(output.stdout, b"");
    assert_eq!(
        output.stderr,
        b"error: could not initialize Z3: the SMT prelude (the definition's SMT axioms and any user prelude) is unsatisfiable\n"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_reports_a_prelude_failure_with_an_unbounded_rewrite_rule() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        include_str!("fixtures/inconsistent-smt-prelude-loop.k"),
    )
    .unwrap();
    let compiled = root.join("compiled");
    let preparation = watchdog::output(watchdog::Request::Compile {
        source: &definition,
        main_module: "LIVENESS-KRUN",
        output: &compiled,
        kind: watchdog::Compilation::Run {
            syntax_module: "LIVENESS-KRUN",
        },
    });
    assert!(
        preparation.status.success(),
        "run preparation failed: {}",
        String::from_utf8_lossy(&preparation.stderr)
    );
    for (context, input) in [
        ("compiled krun", watchdog::Input::Compiled(&compiled)),
        ("source krun", watchdog::Input::Source(&definition)),
    ] {
        let output = watchdog::output(watchdog::Request::Krun {
            input,
            main_module: "LIVENESS-KRUN",
            syntax_module: "LIVENESS-KRUN",
            sort: "State",
            expression: "start(f(0))",
        });
        assert_eq!(output.status.code(), Some(1), "{context}: {output:?}");
        assert_eq!(output.stdout, b"", "{context}: {output:?}");
        assert_eq!(
            output.stderr, b"error: could not initialize Z3: the SMT prelude (the definition's SMT axioms and any user prelude) is unsatisfiable\n",
            "{context}: {output:?}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

/// A function equation with a `#Top` right-hand side beside an `owise` one, a `#Top` equation at
/// priority 40 beside a priority-50 one, and an ordinary function `g`.
const TOP_FUNCTION_EQUATIONS: &str = r#"
module SKIP
  imports INT
  syntax Exp ::= Int
               | "pair" "(" Exp "," Exp ")" [symbol(pair)]
               | "tp" "(" Exp ")"           [symbol(tp)]
               | "done" "(" Exp ")"         [symbol(done)]
  syntax Exp ::= f(Exp)  [symbol(f), function]
               | fp(Exp) [symbol(fp), function]
  syntax Int ::= g(Int)  [symbol(g), function]
  configuration <k> $PGM:Exp </k>
  rule tp(E) => done(f(E))
  rule f(pair(_, _)) => #Top
  rule f(_) => 0 [owise]
  rule fp(pair(_, _)) => #Top [priority(40)]
  rule fp(_) => 0
  rule g(_) => 1
endmodule

module SKIP-SPEC
  imports SKIP
  claim [g-one]: <k> g(3) => 1 </k>
endmodule
"#;

#[test]
fn a_function_equation_whose_right_hand_side_is_top_is_refused_at_load() {
    // `f(pair(_, _)) = #Top` states that `f(pair(1, 2))` is every value of `Exp`, which has
    // several, while a function application has at most one value: the definition has no model.
    // `kcompile` does not load the backend definition, so it succeeds; `krun` and `kprove` refuse
    // the definition when they load it, naming the equation at its written position.
    let (root, _) = fixture();
    let source = root.join("skip.k");
    fs::write(&source, TOP_FUNCTION_EQUATIONS).unwrap();
    let position = |rule: &str| {
        let (index, line) = TOP_FUNCTION_EQUATIONS
            .lines()
            .enumerate()
            .find(|(_, line)| line.trim_start().starts_with(rule))
            .unwrap();
        let column = line.len() - line.trim_start().len() + 1;
        format!("{}:{}:{column}", source.display(), index + 1)
    };
    // The equation is named by its identifier, its written position and its head.
    let refusal = |rule: &str, head: &str| {
        format!(
            " at {} of {head} gives no term as its right-hand side, only \\top or predicates",
            position(rule)
        )
    };
    let compiled = root.join("compiled");
    let preparation = watchdog::output(watchdog::Request::Compile {
        source: &source,
        main_module: "SKIP",
        output: &compiled,
        kind: watchdog::Compilation::Run {
            syntax_module: "SKIP",
        },
    });
    assert!(preparation.status.success(), "{preparation:?}");

    let output = watchdog::output(watchdog::Request::Krun {
        input: watchdog::Input::Compiled(&compiled),
        main_module: "SKIP",
        syntax_module: "SKIP",
        sort: "Exp",
        expression: "tp(pair(1, 2))",
    });
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "{output:?}");
    assert_eq!(output.stdout, b"", "{output:?}");
    // The first `#Top` equation the load meets is named; which of the two that is depends on
    // the load order, so either one's position is accepted.
    assert!(
        stderr.contains(&refusal("rule f(pair", "Lblf"))
            || stderr.contains(&refusal("rule fp(pair", "Lblfp")),
        "{stderr}"
    );

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("kprove")
        .arg(&source)
        .args(["--main-module", "SKIP-SPEC", "--definition-module", "SKIP"])
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "{output:?}");
    assert!(
        stderr.contains(&refusal("rule f(pair", "Lblf"))
            || stderr.contains(&refusal("rule fp(pair", "Lblfp")),
        "{stderr}"
    );

    // Without the two `#Top` equations (and the claims) the definition loads and `g` evaluates.
    let (definition, _claims) = TOP_FUNCTION_EQUATIONS
        .split_once("module SKIP-SPEC")
        .unwrap();
    let without_top = definition
        .lines()
        .filter(|line| !line.contains("=> #Top"))
        .collect::<Vec<_>>()
        .join("\n");
    fs::write(&source, without_top).unwrap();
    let output = watchdog::output(watchdog::Request::Krun {
        input: watchdog::Input::Source(&source),
        main_module: "SKIP",
        syntax_module: "SKIP",
        sort: "Int",
        expression: "g(3)",
    });
    assert!(output.status.success(), "{output:?}");
    assert!(
        String::from_utf8_lossy(&output.stdout).contains(r#"\dv{SortInt{}}("1")"#),
        "{output:?}"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_exec_warns_when_a_returned_leaf_exhausts_its_simplification_budget() {
    let (root, definition) = fixture();
    fs::write(&definition, include_str!("fixtures/execution-budget.kore")).unwrap();
    let initial = root.join("initial.kore");
    fs::write(&initial, "start{}()\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            initial.to_str().unwrap(),
            "--max-simplification-iterations",
            "3",
        ])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(0));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert_eq!(
        stdout,
        include_str!("fixtures/execution-budget-stdout.kore")
    );
    assert_eq!(
        String::from_utf8(output.stderr).unwrap(),
        "warning: simplification budget 3 exhausted while simplifying the term on a path to the result at depth 1; the result may not be fully simplified\n"
    );

    let search = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            initial.to_str().unwrap(),
            "--max-simplification-iterations",
            "3",
            "--search-final",
        ])
        .output()
        .unwrap();
    assert_eq!(search.status.code(), Some(0));
    assert!(
        String::from_utf8(search.stdout)
            .unwrap()
            .contains("held{}("),
        "search must still print its result"
    );
    assert_eq!(
        String::from_utf8(search.stderr).unwrap(),
        "warning: simplification budget 3 exhausted while simplifying the term on a path to the result at depth 1; the result may not be fully simplified\n"
    );
    fs::remove_dir_all(root).unwrap();
}

/// Compiles `rule` over the semcast grammar and returns `definition.kore`.
fn compiled_semcast_kore(rule: &str, checked: bool) -> String {
    let (root, definition) = fixture();
    let source = include_str!("fixtures/reference/inner/semcast3/test.k")
        .replace("  rule bar(X:Big) => foo(X) ~> a(X)", rule);
    fs::write(&definition, source).unwrap();
    let compiled = root.join("compiled");
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command
        .args(["kcompile", definition.to_str().unwrap(), "-m", "TEST", "-o"])
        .arg(&compiled);
    if checked {
        command.env("KRUST_TYPE_INFERENCE_MODE", "checked");
    }
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{rule}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let kore = fs::read_to_string(compiled.join("definition.kore")).unwrap();
    fs::remove_dir_all(root).unwrap();
    kore
}

/// A semantic cast `X:Big` placed after the occurrence that narrows X to Small compiles X at
/// Small at every occurrence, injected upward into Big under `bar`, never downward.
#[test]
fn kcompile_keeps_the_inferred_sort_of_a_variable_under_a_later_semantic_cast() {
    let mut rules = vec![("  rule foo(X) ~> bar(X:Big) => .K", false)];
    #[cfg(feature = "z3-inference")]
    rules.extend([
        ("  rule foo(X) ~> bar(X:Big) => .K", true),
        ("  rule a(X) ~> bar(X:Big) => .K", false),
        ("  rule a(X) ~> bar(X:Big) => .K", true),
    ]);
    for (rule, checked) in rules {
        let kore = compiled_semcast_kore(rule, checked);
        assert!(
            !kore.contains("inj{SortBig{}, SortSmall{}}"),
            "{rule} (checked: {checked}) has a downward injection:\n{kore}"
        );
        assert!(
            !kore.contains("VarX:SortBig{}"),
            "{rule} (checked: {checked}) gives X the sort Big:\n{kore}"
        );
        assert!(
            kore.contains("Lblbar{}(inj{SortSmall{}, SortBig{}}(VarX:SortSmall{}))"),
            "{rule} (checked: {checked}):\n{kore}"
        );
    }
}

#[test]
fn runnable_compiled_artifact_is_equivalent_and_validated() {
    let (root, definition) = fixture();
    let definition_source = r#"
module MAIN
  syntax Input ::= "zero" | "twice" "(" Input ")" [macro]
  rule twice(I:Input) => I
  context alias [input]: HERE requires isInput(HOLE)
  configuration <top><k> $PGM:Input </k><env> $ENV:Input </env></top>
endmodule
"#;
    fs::write(&definition, definition_source).unwrap();
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kcompile", definition.to_str().unwrap(), "-m", "MAIN", "-o"])
        .arg(&compiled)
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    for name in [
        "runtime.json",
        "frontend.json",
        "execution.json",
        "definition.kore",
    ] {
        assert!(compiled.join(name).is_file(), "missing {name}");
    }
    assert!(!compiled.join("parsed.json").exists());

    let source = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "-m",
            "MAIN",
            "-s",
            "Input",
            "-e",
            "twice(zero)",
            "-c",
            "ENV=twice(zero)",
            "--search-final",
            "--pattern",
            "<k> ?K:K </k>",
        ])
        .output()
        .unwrap();
    assert!(
        source.status.success(),
        "{}",
        String::from_utf8_lossy(&source.stderr)
    );
    fs::remove_file(&definition).unwrap();
    let artifact = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "-s",
            "Input",
            "-e",
            "twice(zero)",
            "-c",
            "ENV=twice(zero)",
            "--search-final",
            "--pattern",
            "<k> ?K:K </k>",
        ])
        .output()
        .unwrap();
    assert!(
        artifact.status.success(),
        "{}",
        String::from_utf8_lossy(&artifact.stderr)
    );
    assert_eq!(artifact.stdout, source.stdout);

    fs::write(&definition, definition_source).unwrap();
    let compiled_again = root.join("compiled-again");
    let repeated = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kcompile", definition.to_str().unwrap(), "-m", "MAIN", "-o"])
        .arg(&compiled_again)
        .output()
        .unwrap();
    assert!(
        repeated.status.success(),
        "{}",
        String::from_utf8_lossy(&repeated.stderr)
    );
    for name in [
        "runtime.json",
        "frontend.json",
        "execution.json",
        "definition.kore",
    ] {
        assert_eq!(
            fs::read(compiled.join(name)).unwrap(),
            fs::read(compiled_again.join(name)).unwrap(),
            "nondeterministic {name}"
        );
    }

    let frontend = fs::read(compiled.join("frontend.json")).unwrap();
    let manifest = fs::read(compiled.join("runtime.json")).unwrap();
    fs::write(compiled.join("frontend.json"), "corrupt").unwrap();
    let corrupt = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "-s",
            "Input",
            "-e",
            "zero",
        ])
        .output()
        .unwrap();
    assert!(!corrupt.status.success());
    let stderr = String::from_utf8(corrupt.stderr).unwrap();
    assert!(stderr.contains("failed SHA-256 validation"), "{stderr}");
    assert!(stderr.contains("fresh runnable artifact"), "{stderr}");

    fs::write(compiled.join("frontend.json"), frontend).unwrap();

    // The execution definition is decoded only to compile a search pattern: a payload that
    // passes its digest check but does not decode fails the run that reads it, not every run.
    let execution = fs::read(compiled.join("execution.json")).unwrap();
    let undecodable = b"{}";
    let mut rehashed: serde_json::Value = serde_json::from_slice(&manifest).unwrap();
    rehashed["execution"]["sha256"] = {
        use sha2::{Digest, Sha256};
        Sha256::digest(undecodable)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>()
            .into()
    };
    fs::write(compiled.join("execution.json"), undecodable).unwrap();
    fs::write(
        compiled.join("runtime.json"),
        serde_json::to_vec(&rehashed).unwrap(),
    )
    .unwrap();
    let without_pattern = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "-s",
            "Input",
            "-e",
            "zero",
            "-c",
            "ENV=zero",
        ])
        .output()
        .unwrap();
    assert!(
        without_pattern.status.success(),
        "{}",
        String::from_utf8_lossy(&without_pattern.stderr)
    );
    let with_pattern = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "-s",
            "Input",
            "-e",
            "zero",
            "-c",
            "ENV=zero",
            "--search-final",
            "--pattern",
            "<k> ?K:K </k>",
        ])
        .output()
        .unwrap();
    assert!(!with_pattern.status.success());
    let stderr = String::from_utf8(with_pattern.stderr).unwrap();
    assert!(
        stderr.contains("runnable artifact payload `execution.json` is corrupt"),
        "{stderr}"
    );
    assert!(stderr.contains("fresh runnable artifact"), "{stderr}");
    fs::write(compiled.join("execution.json"), execution).unwrap();

    // A payload written in an earlier provenance version (here by the version 7 writer), with a
    // valid digest, is refused by its version, not reported as corrupt.
    let frontend = fs::read(compiled.join("frontend.json")).unwrap();
    let mut earlier: serde_json::Value = serde_json::from_slice(&manifest).unwrap();
    earlier["frontend"]["sha256"] = {
        use sha2::{Digest, Sha256};
        Sha256::digest(PROVENANCE_VERSION_7.as_bytes())
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>()
            .into()
    };
    fs::write(compiled.join("frontend.json"), PROVENANCE_VERSION_7).unwrap();
    fs::write(
        compiled.join("runtime.json"),
        serde_json::to_vec(&earlier).unwrap(),
    )
    .unwrap();
    let earlier_version = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "-s",
            "Input",
            "-e",
            "zero",
        ])
        .output()
        .unwrap();
    assert!(!earlier_version.status.success());
    let stderr = String::from_utf8(earlier_version.stderr).unwrap();
    assert!(
        stderr.contains(
            "runnable artifact payload `frontend.json` was written by another krust: \
             KRUST-PROVENANCE version 7 is not supported; this build reads version 8; \
             run `krust kcompile` again"
        ),
        "{stderr}"
    );
    fs::write(compiled.join("frontend.json"), frontend).unwrap();
    fs::write(compiled.join("runtime.json"), &manifest).unwrap();

    let mut incompatible: serde_json::Value = serde_json::from_slice(&manifest).unwrap();
    incompatible["version"] = 2.into();
    fs::write(
        compiled.join("runtime.json"),
        serde_json::to_vec(&incompatible).unwrap(),
    )
    .unwrap();
    let version = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "-s",
            "Input",
            "-e",
            "zero",
        ])
        .output()
        .unwrap();
    assert!(
        String::from_utf8_lossy(&version.stderr).contains("unsupported runnable artifact version"),
        "{}",
        String::from_utf8_lossy(&version.stderr)
    );

    incompatible["version"] = 1.into();
    incompatible["backend"] = "llvm".into();
    fs::write(
        compiled.join("runtime.json"),
        serde_json::to_vec(&incompatible).unwrap(),
    )
    .unwrap();
    let backend = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "-s",
            "Input",
            "-e",
            "zero",
        ])
        .output()
        .unwrap();
    assert!(
        String::from_utf8_lossy(&backend.stderr).contains("is not executable by the Rust backend"),
        "{}",
        String::from_utf8_lossy(&backend.stderr)
    );

    fs::remove_file(compiled.join("runtime.json")).unwrap();
    let partial = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "-s",
            "Input",
            "-e",
            "zero",
        ])
        .output()
        .unwrap();
    assert!(
        String::from_utf8_lossy(&partial.stderr).contains("manifest")
            && String::from_utf8_lossy(&partial.stderr).contains("missing or unreadable"),
        "{}",
        String::from_utf8_lossy(&partial.stderr)
    );
}

fn output_with_stdin(command: &mut Command, input: &[u8]) -> Output {
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(input).unwrap();
    child.wait_with_output().unwrap()
}

fn captured_output_command(compiled: &Path, expression: &str) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command.args([
        "krun",
        "--definition",
        compiled.to_str().unwrap(),
        "--sort",
        "Pgm",
        "--expression",
        expression,
        "--output",
        "captured",
    ]);
    command
}

fn compiled_live_io_fixture() -> (PathBuf, PathBuf) {
    let fixture_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/live-io/test.k");
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            fixture_path.to_str().unwrap(),
            "--main-module",
            "LIVE-IO",
            "--output-directory",
        ])
        .arg(&compiled)
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    (root, compiled)
}

fn live_io_command(compiled: &Path, expression: &str) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command.args([
        "krun",
        "--definition",
        compiled.to_str().unwrap(),
        "--sort",
        "Pgm",
        "--expression",
        expression,
        "--io",
        "on",
        "--output",
        "none",
    ]);
    command
}

fn pattern_binding<'a>(pattern: &'a Pattern, variable_name: &str) -> Option<&'a Pattern> {
    match pattern {
        Pattern::Equals { left, right, .. } => match (left.as_ref(), right.as_ref()) {
            (Pattern::Variable(variable), value) if variable.name == variable_name => Some(value),
            (value, Pattern::Variable(variable)) if variable.name == variable_name => Some(value),
            _ => None,
        },
        Pattern::And { arguments, .. } => arguments
            .iter()
            .find_map(|argument| pattern_binding(argument, variable_name)),
        _ => None,
    }
}

fn exit_reference_fixtures() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/exit")
}

/// `krun` on the stdin delimiter fixture. Its subject is how the `STDIN-STREAM` rules of the
/// embedded `domains.md` read integers from `$STDIN`, so it resolves builtins from the copies
/// compiled into `krust` and needs no K checkout.
fn stdin_delimiter_run_command() -> (Command, PathBuf) {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/execution/stdin-delimiter-run");
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command.args([
        "krun",
        fixtures.join("test.k").to_str().unwrap(),
        fixtures.join("three.pgm").to_str().unwrap(),
        "--main-module",
        "STDIN-DELIMITER-RUN",
        "--syntax-module",
        "STDIN-DELIMITER-RUN-SYNTAX",
        "--sort",
        "Stmt",
        "-I",
        fixtures.to_str().unwrap(),
        "--io",
        "off",
    ]);
    (command, fixtures)
}

fn exit_krun_command() -> Command {
    let fixtures = exit_reference_fixtures();
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command
        .arg("krun")
        .arg(fixtures.join("test.k"))
        .arg(fixtures.join("program.pgm"))
        .args([
            "--main-module",
            "EXIT",
            "--syntax-module",
            "EXIT",
            "--sort",
            "Int",
        ]);
    command
}

fn compiled_exit_fixture() -> (PathBuf, PathBuf, PathBuf) {
    let (root, _) = fixture();
    let fixtures = exit_reference_fixtures();
    let compiled = root.join("compiled");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("kcompile")
        .arg(fixtures.join("test.k"))
        .args([
            "--main-module",
            "EXIT",
            "--syntax-module",
            "EXIT",
            "--backend",
            "rust",
            "--output-directory",
        ])
        .arg(&compiled)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let initial = root.join("initial.kore");
    let output = exit_krun_command().args(["--depth", "0"]).output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    fs::write(&initial, output.stdout).unwrap();
    (root, compiled.join("definition.kore"), initial)
}

fn branching_search_fixture() -> (PathBuf, PathBuf) {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  syntax State ::= "a" | "b" | "c" | "d" | "e"
  configuration <k> $PGM:State </k>
  rule a => b
  rule b => c
  rule c => d
  rule c => e
endmodule
"#,
    )
    .unwrap();
    (root, definition)
}

#[test]
fn kast_parses_a_program_as_text_and_json() {
    let (root, definition) = fixture();
    let binary = env!("CARGO_BIN_EXE_krust");

    let text = Command::new(binary)
        .args([
            "kast",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--sort",
            "Exp",
            "--expression",
            "42",
            "--no-prelude",
        ])
        .output()
        .unwrap();
    assert!(
        text.status.success(),
        "{}",
        String::from_utf8_lossy(&text.stderr)
    );
    assert_eq!(
        String::from_utf8(text.stdout).unwrap(),
        "#token(\"42\",\"Int\")\n"
    );

    let json = Command::new(binary)
        .args([
            "kast",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--sort",
            "Exp",
            "--expression",
            "42",
            "--output",
            "json",
            "--no-prelude",
        ])
        .output()
        .unwrap();
    assert!(
        json.status.success(),
        "{}",
        String::from_utf8_lossy(&json.stderr)
    );
    let value: serde_json::Value = serde_json::from_slice(&json.stdout).unwrap();
    assert_eq!(value["format"], "KAST");
    assert_eq!(value["version"], 4);
    assert_eq!(value["term"]["token"], "42");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kast_parses_and_rejects_a_batch_with_one_frontend_load() {
    let (root, definition) = fixture();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kast",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--batch-case",
            "integer",
            "Exp",
            "42",
            "--batch-case",
            "addition",
            "Exp",
            "1 + 2",
            "--batch-reject-case",
            "malformed",
            "Exp",
            "+",
            "--output",
            "json",
            "--no-prelude",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let value: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(value["integer"]["term"]["token"], "42");
    assert_eq!(value["addition"]["term"]["node"], "KApply");
    assert!(value.get("malformed").is_none());

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kast_preserves_and_krun_expands_macros_in_concrete_programs() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax Input ::= Int | "twice" "(" Int ")" [macro]
  rule twice(I) => I +Int I
  configuration <k> $PGM:Input </k>
endmodule
"#,
    )
    .unwrap();
    let binary = env!("CARGO_BIN_EXE_krust");

    let kast = Command::new(binary)
        .args([
            "kast",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--sort",
            "Input",
            "--expression",
            "twice(21)",
            "--output",
            "json",
        ])
        .output()
        .unwrap();
    assert!(
        kast.status.success(),
        "{}",
        String::from_utf8_lossy(&kast.stderr)
    );
    let kast = String::from_utf8(kast.stdout).unwrap();
    assert!(kast.contains("twice"), "{kast}");
    assert!(!kast.contains("_+Int_"), "{kast}");

    let krun = Command::new(binary)
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "Input",
            "--expression",
            "twice(21)",
            "--depth",
            "1",
        ])
        .output()
        .unwrap();
    assert!(
        krun.status.success(),
        "{}",
        String::from_utf8_lossy(&krun.stderr)
    );
    let krun = String::from_utf8(krun.stdout).unwrap();
    assert!(!krun.contains("Lbltwice"), "{krun}");
    assert!(krun.contains(r#"\dv{SortInt{}}("42")"#), "{krun}");

    fs::remove_dir_all(root).unwrap();
}

/// `krun` runs a program whose initial configuration is as deep as macro expansion makes it:
/// `count(m(m(...200...(z))))` expands through `m(X) => s(...500...(X))` to 100,000 levels, which
/// the frontend instantiates and converts and the backend validates, internalizes and rewrites
/// once, on the main thread's stack, extended where the depth needs it. (One step: each step of
/// this countdown takes time in proportion to the term in the `dev` profile, where the suite
/// runs, and the printed result is quadratic in its depth.)
#[test]
fn krun_runs_a_program_whose_expansion_is_of_any_depth() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        format!(
            r#"
module MAIN
  syntax Nat ::= "z" | s(Nat)
  syntax Nat ::= m(Nat) [macro]
  syntax KItem ::= count(Nat)
  configuration <k> $PGM:KItem </k>
  rule <k> count(s(N)) => count(N) </k>
  rule m(X) => {}X{}
endmodule
"#,
            "s(".repeat(500),
            ")".repeat(500)
        ),
    )
    .unwrap();
    let program = format!("count({}z{})", "m(".repeat(200), ")".repeat(200));
    let krun = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "KItem",
            "--expression",
            &program,
            "--depth",
            "1",
            "--output",
            "none",
        ])
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap();
    assert!(
        krun.status.success(),
        "{}: {}",
        krun.status,
        String::from_utf8_lossy(&krun.stderr)
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_uses_main_module_macros_for_syntax_and_configuration_inputs() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module COMMON
  syntax Hidden
  syntax Input ::= Hidden
  syntax Input ::= "done" [symbol(done)]
                 | "programMacro" [macro, symbol(programMacro)]
                 | "configMacro" [macro, symbol(configMacro)]
                 | "hiddenMacro" [macro, symbol(hiddenMacro)]
                 | "hiddenConditional" [macro, symbol(hiddenConditional)]
endmodule

module SYNTAX
  imports COMMON
endmodule

module MACROS
  imports COMMON
  syntax Hidden ::= "$hidden" [token]
  rule configMacro => done
  rule hiddenMacro => $hidden
  rule hiddenConditional => done requires true
endmodule

module MAIN
  imports COMMON
  imports MACROS
  syntax Input ::= "wrapped" [symbol(mainWrap)]
  rule programMacro => wrapped
  configuration <k> $PGM:Input </k>
                <state parser="STATE, SYNTAX"> $STATE:Input </state>
                <local parser="LOCAL, SYNTAX"> $LOCAL:Input </local>
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--syntax-module",
            "SYNTAX",
            "--sort",
            "Input",
            "--expression",
            "programMacro",
            "-c",
            "STATE=configMacro",
            "-c",
            "LOCAL=hiddenMacro",
            "--depth",
            "0",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--syntax-module",
            "SYNTAX",
            "--output-directory",
        ])
        .arg(&compiled)
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    let artifact = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "--sort",
            "Input",
            "--expression",
            "programMacro",
            "-c",
            "STATE=configMacro",
            "-c",
            "LOCAL=hiddenMacro",
            "--depth",
            "0",
        ])
        .output()
        .unwrap();
    assert!(
        artifact.status.success(),
        "{}",
        String::from_utf8_lossy(&artifact.stderr)
    );
    assert_eq!(artifact.stdout, output.stdout);
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(!output.contains("LblprogramMacro"), "{output}");
    assert!(!output.contains("LblconfigMacro"), "{output}");
    assert!(!output.contains("LblhiddenMacro"), "{output}");
    assert!(
        output.contains("LblmainWrap{}()"),
        "expected a main-only application on a macro RHS to survive expansion: {output}"
    );
    assert!(
        output.contains("Lbldone{}()"),
        "expected the configuration input to expand: {output}"
    );
    assert!(
        output.contains(r#"\dv{SortHidden{}}("$hidden")"#),
        "expected the macro module's private token to survive expansion: {output}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_rejects_a_macro_symbol_that_survives_expansion() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  syntax Input ::= "stuck" [macro, symbol(stuckMacro)]
  configuration <k> $PGM:Input </k>
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "Input",
            "--expression",
            "stuck",
            "--depth",
            "1",
        ])
        .output()
        .unwrap();

    assert!(!output.status.success());
    let error = String::from_utf8(output.stderr).unwrap();
    assert!(error.contains("invalid executable input"), "{error}");
    assert!(error.contains("LblstuckMacro"), "{error}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_parses_programs_with_the_selected_syntax_module() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module SELECTED-SYNTAX
  syntax Input ::= "go" [symbol(selectedGo)]
endmodule

module ALTERNATE-SYNTAX
  syntax Input ::= "go" [symbol(alternateGo)]
endmodule

module MAIN
  imports SELECTED-SYNTAX
  imports ALTERNATE-SYNTAX
  configuration <k> $PGM:Input </k>
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--syntax-module",
            "SELECTED-SYNTAX",
            "--sort",
            "Input",
            "--expression",
            "go",
            "--depth",
            "0",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("LblselectedGo"), "{stdout}");
    assert!(!stdout.contains("LblalternateGo"), "{stdout}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_krun_parses_configuration_variables_with_the_main_module() {
    // reference: k/result/bin/krun 1.pgm --definition ref -cENV='two()' --output kore
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/cfg");
    let expected = fs::read_to_string(fixtures.join("config-main.kore")).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("test.k").to_str().unwrap(),
            fixtures.join("1.pgm").to_str().unwrap(),
            "--main-module",
            "CFG",
            "--syntax-module",
            "CFG-SYNTAX",
            "--sort",
            "Pgm",
            "-cENV=two()",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    let result = r#"\dv{SortInt{}}("3")"#;
    assert!(expected.contains(result), "reference fixture: {expected}");
    assert!(stdout.contains(result), "{stdout}");
}

#[test]
fn reference_krun_defaults_the_program_grammar_to_the_syntax_module() {
    // reference: k/result/bin/krun two.pgm --definition ref -cENV=1 exits 113
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/cfg");
    assert_eq!(
        fs::read_to_string(fixtures.join("program-reject.exit")).unwrap(),
        "113\n"
    );
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("test.k").to_str().unwrap(),
            fixtures.join("two.pgm").to_str().unwrap(),
            "--main-module",
            "CFG",
            "--sort",
            "Pgm",
            "-cENV=1",
        ])
        .output()
        .unwrap();

    assert!(!output.status.success(), "program unexpectedly parsed");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("could not parse program as Pgm"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn reference_krun_honours_the_configuration_cell_parser_attribute() {
    // reference: k/result/bin/krun go.pgm --definition parser-ref -cENV=selected --output kore
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/cfg");
    let expected = fs::read_to_string(fixtures.join("parser-config.kore")).unwrap();
    // Both runs parse their `-c` value with the per-cell parser of one compiled definition.
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    kcompile_for_krun(
        &fixtures.join("parser.k"),
        &["--main-module", "PARSER"],
        &compiled,
    );
    let krun = |configuration: &str| {
        Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["krun", "--definition"])
            .arg(&compiled)
            .arg(fixtures.join("go.pgm"))
            .args(["--sort", "Pgm", configuration, "--depth", "0"])
            .output()
            .unwrap()
    };
    let output = krun("-cENV=selected");

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        expected.contains("LblselectedEnv"),
        "reference fixture: {expected}"
    );
    assert!(stdout.contains("LblselectedEnv"), "{stdout}");

    let rejected = krun("-cENV=main");
    assert!(
        !rejected.status.success(),
        "the per-cell parser unexpectedly accepted main-module-only syntax"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_warns_when_the_default_syntax_module_is_missing() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  syntax State ::= "ready" [symbol(ready)]
  configuration <k> $PGM:State </k>
endmodule
"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "State",
            "--expression",
            "ready",
            "--depth",
            "0",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(
            "Could not find main syntax module with name MAIN-SYNTAX in definition.  Use --syntax-module to specify one. Using MAIN as default."
        ),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("Lblready"),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_at_kitem_matches_krun_at_the_concrete_sort() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/inner/programs/cast-kitem");
    let definition = fixtures.join("test.k");
    let program = fixtures.join("1.test");
    // Both sorts run the program on one compiled definition.
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    kcompile_for_krun(
        &definition,
        &["--main-module", "TEST", "--syntax-module", "TEST"],
        &compiled,
    );
    let run = |sort: &str| {
        Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["krun", "--definition"])
            .arg(&compiled)
            .arg(&program)
            .args(["--sort", sort, "--depth", "10"])
            .output()
            .unwrap()
    };

    let concrete = run("Int");
    assert!(
        concrete.status.success(),
        "{}",
        String::from_utf8_lossy(&concrete.stderr)
    );
    let at_kitem = run("KItem");
    assert!(
        at_kitem.status.success(),
        "{}",
        String::from_utf8_lossy(&at_kitem.stderr)
    );
    assert_eq!(at_kitem.stdout, concrete.stdout);
    fs::remove_dir_all(root).unwrap();
}

/// A list whose element symbol takes the closed instance `MInt{64}` compiles to a definition
/// that `krun` loads and runs: the list hooks build, measure and index it, and a rule matches an
/// element of it, giving the count and the words the program put in.
#[test]
fn krun_runs_a_list_of_machine_words() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports MINT
  imports INT
  syntax MInt{64}
  syntax WL [hook(LIST.List)]
  syntax WL ::= WL WL [left, function, total, hook(LIST.concat), symbol(_WL_), assoc, unit(.WL), element(wItem)]
  syntax WL ::= ".WL" [function, total, hook(LIST.unit), symbol(.WL)]
  syntax WL ::= wItem(MInt{64}) [function, total, hook(LIST.element), symbol(wItem)]
  syntax MInt{64} ::= WL "[" Int "]" [function, hook(LIST.get), symbol(wGet)]
  syntax Int ::= wSize(WL) [function, total, hook(LIST.size), symbol(wSize)]
  syntax MInt{64} ::= first(WL) [function, symbol(first)]
  rule first(wItem(W) _:WL) => W
  syntax Pgm ::= "go"
  syntax KItem ::= done(Int, MInt{64}, MInt{64}) [symbol(done)]
  configuration <k> $PGM:Pgm </k>
  rule go => done(wSize(wItem(3p64) wItem(5p64)), (wItem(3p64) wItem(5p64))[1], first(wItem(7p64) wItem(9p64)))
endmodule
"#,
    )
    .unwrap();
    let compiled = root.join("compiled");
    kcompile_for_krun(&definition, &["--main-module", "MAIN"], &compiled);
    let program = root.join("go.main");
    fs::write(&program, "go").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["krun", "--definition"])
        .arg(&compiled)
        .arg(&program)
        .args(["--sort", "Pgm"])
        .stdin(Stdio::null())
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    let compact: String = stdout.split_whitespace().collect();
    assert!(
        compact.contains(
            r#"Lbldone{}(\dv{SortInt{}}("2"),\dv{SortMInt{Sort64{}}}("5p64"),\dv{SortMInt{Sort64{}}}("7p64"))"#
        ),
        "{stdout}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// Rules that tell the element `255p8` of `MInt{8}` apart from every other element.
const MINT_SPELLINGS: &str = r#"
requires "domains.md"
module FP-SYNTAX
  imports INT-SYNTAX
  imports MINT-SYNTAX
  syntax MInt{8}
  syntax Pgm ::= step(MInt{8}) | stepm(MInt{8}) | done() | bad()
endmodule
module FP
  imports FP-SYNTAX
  imports INT
  imports MINT
  imports BOOL
  imports K-EQUAL
  configuration <k> $PGM:Pgm </k>
  rule <k> step(X) => bad() ... </k> requires X ==K 255p8
  rule <k> step(X) => done() ... </k> requires notBool (X ==K 255p8)
  rule <k> stepm(255p8) => bad() ... </k>
  rule <k> stepm(_) => done() ... </k> [owise]
endmodule
"#;

/// The literals `07` and `7` of a sort hooked `INT.Int` under its own name are one integer, so
/// the rule on `7` applies to `07` and the claim is false.
const HOOKED_INT_SPELLINGS: &str = r#"
requires "domains.md"
module HFP-SYNTAX
  imports INT-SYNTAX
  syntax MyInt [hook(INT.Int)]
  syntax MyInt ::= r"[0-9]+" [token, prec(2)]
  syntax Pgm ::= stepm(MyInt) | done() | bad()
endmodule
module HFP
  imports HFP-SYNTAX
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> $PGM:Pgm </k>
  rule <k> stepm(#token("7", "MyInt")) => bad() ... </k>
  rule <k> stepm(_) => done() ... </k> [owise]
endmodule
module HFP-SPEC
  imports HFP
  claim <k> stepm(#token("07", "MyInt")) => done() ... </k>
endmodule
"#;

/// `kprove` of `spec` in `source` against `definition_module`: the claim's verdict, and the
/// whole standard output.
fn kprove_single_claim(source: &str, spec: &str, definition_module: &str) -> (String, String) {
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            definition.to_str().unwrap(),
            "--main-module",
            spec,
            "--definition-module",
            definition_module,
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    let verdict = stdout
        .lines()
        .find_map(|line| line.strip_prefix("claim #1: "))
        .unwrap_or_else(|| {
            panic!(
                "{spec}: no verdict in {stdout}\n{}",
                String::from_utf8_lossy(&output.stderr)
            )
        })
        .split_whitespace()
        .next()
        .unwrap()
        .to_owned();
    fs::remove_dir_all(root).unwrap();
    (verdict, stdout)
}

/// Two spellings of one machine integer are one term: a claim that holds only if `-1p8` (or a
/// symbolic `X` equal to `511p8`) were another element than `255p8` is not proven, and its proof
/// ends at the `bad()` state the rules on `255p8` reach. On the ground claims that state is a
/// certified counterexample, so they are disproved.
#[test]
fn kprove_proves_nothing_through_two_spellings_of_one_mint_element() {
    // Each claim states that a spelling of `255p8` reaches `done()`: `-1p8` and `511p8` are the
    // integers -1 and 511 truncated to 8 bits, so the `bad()` rules apply and every claim is
    // false. Each claim is the only one of its spec module and file.
    for (spec, claim, expected) in [
        (
            "FP-A",
            "claim <k> step(-1p8) => done() ... </k>",
            "disproved",
        ),
        (
            "FP-A2",
            "claim <k> step(X) => done() ... </k> requires X ==K 511p8",
            "failed",
        ),
        (
            "FP-B",
            "claim <k> stepm(-1p8) => done() ... </k>",
            "disproved",
        ),
    ] {
        let source = format!("{MINT_SPELLINGS}module {spec}\n  imports FP\n  {claim}\nendmodule\n");
        let (verdict, stdout) = kprove_single_claim(&source, spec, "FP");
        assert_eq!(verdict, expected, "{spec}: {stdout}");
        assert!(
            stdout.contains(r"Lblbad'LParRParUnds'FP-SYNTAX'Unds'Pgm{}()"),
            "{spec}: no bad() leaf in {stdout}"
        );
    }
}

/// The load-time literals of a sort hooked `INT.Int` under its own name are read by the hook:
/// `#token("07", "MyInt")` and `#token("7", "MyInt")` are one term, so the claim that `07`
/// reaches `done()` is disproved by the certified `bad()` state.
#[test]
fn kprove_proves_nothing_through_two_spellings_of_one_hooked_int_value() {
    let (verdict, stdout) = kprove_single_claim(HOOKED_INT_SPELLINGS, "HFP-SPEC", "HFP");
    assert_eq!(verdict, "disproved", "{stdout}");
    assert!(
        stdout.contains(r"Lblbad'LParRParUnds'HFP-SYNTAX'Unds'Pgm{}()"),
        "no bad() leaf in {stdout}"
    );
}

/// A sort hooked `INT.Int` under its own name, and a function hooked `STRING.string2token` that
/// builds its values at run time from a `String`.
const STRING_TO_HOOKED_INT_DEFINITION: &str = r#"
requires "domains.md"
module S2T-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  syntax MyInt [hook(INT.Int)]
  syntax MyInt ::= r"[0-9]+" [token, prec(2)]
  syntax MyInt ::= String2MyInt(String) [function, total, hook(STRING.string2token)]
  syntax Pgm ::= go(String) | run(String) | stepm(MyInt) | done() | bad()
endmodule
module S2T
  imports S2T-SYNTAX
  imports INT
  imports STRING
  imports BOOL
  imports K-EQUAL
  configuration <k> $PGM:Pgm </k>
  syntax KItem ::= Bool | lit(MyInt)
  rule <k> go(S) => lit(String2MyInt(S)) ~> (String2MyInt(S) ==K #token("7", "MyInt")) ... </k>
  rule <k> run(S) => stepm(String2MyInt(S)) ... </k>
  rule <k> stepm(#token("7", "MyInt")) => bad() ... </k>
  rule <k> stepm(_) => done() ... </k> [owise]
endmodule
"#;

const STRING_TO_HOOKED_INT_SPEC: &str = r#"
module S2T-SPEC
  imports S2T
  claim <k> run("07") => done() ... </k>
endmodule
"#;

/// A value that `STRING.string2token` builds at run time at a sort hooked `INT.Int` is read by
/// that hook: `String2MyInt("07")` is the integer 7, the `bad()` rule on `7` applies, and the
/// ground claim that `run("07")` reaches `done()` is disproved at that leaf.
#[test]
fn kprove_proves_nothing_through_a_hooked_int_token_built_from_a_string() {
    let source = format!("{STRING_TO_HOOKED_INT_DEFINITION}{STRING_TO_HOOKED_INT_SPEC}");
    let (verdict, stdout) = kprove_single_claim(&source, "S2T-SPEC", "S2T");
    assert_eq!(verdict, "disproved", "{stdout}");
    assert!(
        stdout.contains(r"Lblbad'LParRParUnds'S2T-SYNTAX'Unds'Pgm{}()"),
        "no bad() leaf in {stdout}"
    );
}

/// `String2MyInt("07")` is stored as the canonical text of the integer it names, so it prints
/// as `7` and `==K` finds it equal to the literal `7` of the same sort.
#[test]
fn krun_reads_a_string_to_token_value_by_the_hook_of_its_sort() {
    let go = compact_success(&krun_mint_program(
        STRING_TO_HOOKED_INT_DEFINITION,
        "S2T",
        r#"go("07")"#,
    ));
    assert!(
        go.contains(
            r#"kseq{}(Lbllit'LParUndsRParUnds'S2T'Unds'KItem'Unds'MyInt{}(\dv{SortMyInt{}}("7")),kseq{}(inj{SortBool{},SortKItem{}}(\dv{SortBool{}}("true")),dotk{}()))"#
        ),
        "{go}"
    );
}

/// Rules that distinguish the binary64 value 1.0 and the p113x15 value 1.0 from every other value
/// of their formats (repro `map-set-choice-difference-hooks/r2/fq.k`).
const FLOAT_SPELLINGS: &str = r#"
module FQ-SYNTAX
  imports FLOAT-SYNTAX
  syntax Pgm ::= step(Float) | stepq(Float) | done() | bad()
endmodule
module FQ
  imports FQ-SYNTAX
  imports DOMAINS
  imports FLOAT
  configuration <k> $PGM:Pgm </k>
  rule <k> step(X) => bad() ... </k> requires X ==K 1.0
  rule <k> step(X) => done() ... </k> requires notBool (X ==K 1.0)
  rule <k> stepq(X) => bad() ... </k> requires X ==K 1.0p113x15
  rule <k> stepq(X) => done() ... </k> requires notBool (X ==K 1.0p113x15)
endmodule
"#;

/// `1.00` and `1.0` are one binary64 value, and `1.00p113x15` and `1.0p113x15` one p113x15 value,
/// each one term: the rule on `1.0` applies to `1.00`, so the claims that `1.00` reaches `done()`
/// are disproved at the `bad()` state.
#[test]
fn kprove_proves_nothing_through_two_spellings_of_one_float_value() {
    for claim in ["step(1.00)", "stepq(1.00p113x15)"] {
        let spec = format!(
            "{FLOAT_SPELLINGS}module FQ-SPEC\n  imports FQ\n  claim <k> {claim} => done() ... </k>\nendmodule\n"
        );
        let (verdict, stdout) = kprove_single_claim(&spec, "FQ-SPEC", "FQ");
        assert_eq!(verdict, "disproved", "{claim}: {stdout}");
        assert!(
            stdout.contains(r"Lblbad'LParRParUnds'FQ-SYNTAX'Unds'Pgm{}()"),
            "{claim}: no bad() leaf in {stdout}"
        );
    }
}

/// Comparisons and a rule on a p11x5 value (repro `r2/wideeq.k`): `1.0001p11x5` rounds to the
/// binary16 value 1, the value `1.0p11x5` names.
const WIDE_FLOAT_EQUALITY: &str = r#"
module WIDEEQ
  imports FLOAT
  imports BOOL
  imports INT
  imports K-EQUAL
  syntax Exp ::= Float | Bool | Int
               | "keq" "(" Float "," Float ")" [symbol(keq)]
               | "isone" "(" Float ")" [symbol(isone)]
  configuration <k> $PGM:Exp </k>
  rule keq(X, Y) => X ==K Y
  rule isone(1.0p11x5) => true
  rule isone(_) => false [owise]
endmodule
"#;

/// Two spellings of one p11x5 value are one term, so `==K` finds them equal and the rule on
/// `1.0p11x5` applies to `1.0001p11x5`: both claims that they differ are disproved.
#[test]
fn kprove_proves_nothing_through_two_spellings_of_one_wide_float_value() {
    for claim in ["keq(1.0p11x5, 1.0001p11x5)", "isone(1.0001p11x5)"] {
        let spec = format!(
            "{WIDE_FLOAT_EQUALITY}module WIDEEQ-SPEC\n  imports WIDEEQ\n  claim <k> {claim} => false </k>\nendmodule\n"
        );
        let (verdict, stdout) = kprove_single_claim(&spec, "WIDEEQ-SPEC", "WIDEEQ");
        assert_eq!(verdict, "disproved", "{claim}: {stdout}");
    }
}

/// A map and a set that hold one p11x5 value twice (repro `r3c/wide.k`), and the operations of
/// a format the backend does not compute.
const WIDE_FLOAT_KEYS: &str = r#"
module WIDE-SYNTAX
  imports FLOAT-SYNTAX
  syntax Pgm ::= sz() | ssz() | dv(Float, Float) | ab(Float) | done() | bad()
endmodule
module WIDE
  imports WIDE-SYNTAX
  imports DOMAINS
  imports FLOAT
  configuration <k> $PGM:Pgm </k>
  syntax KItem ::= r(K)
  rule <k> sz() => r(size(1.0p11x5 |-> 1 1.0001p11x5 |-> 2)) ... </k>
  rule <k> ssz() => r(size(SetItem(1.0p11x5) SetItem(1.0001p11x5))) ... </k>
  rule <k> dv(X, Y) => r(X /Float Y) ... </k>
  rule <k> ab(X) => r(absFloat(X)) ... </k>
endmodule
"#;

/// `1.0p11x5 |-> 1 1.0001p11x5 |-> 2` binds one key twice, so the map, and the step to its size,
/// is undefined, as is the set's concatenation of one element with itself: neither claim of size
/// 2 is proven.
#[test]
fn kprove_does_not_count_one_wide_float_key_twice() {
    for claim in ["sz()", "ssz()"] {
        let spec = format!(
            "{WIDE_FLOAT_KEYS}module WIDE-SPEC\n  imports WIDE\n  claim <k> {claim} => r(2) ... </k>\nendmodule\n"
        );
        let (verdict, stdout) = kprove_single_claim(&spec, "WIDE-SPEC", "WIDE");
        assert_eq!(verdict, "failed", "{claim}: {stdout}");
    }
}

/// A definition whose first step writes `absFloat` of its argument into a cell no later rule
/// reads, and whose second step ends the program: the application stays in the final
/// configuration.
const WIDE_FLOAT_AT_THE_END: &str = r#"
module WIDEEND-SYNTAX
  imports FLOAT-SYNTAX
  syntax Pgm ::= go(Float) | next() | done()
endmodule
module WIDEEND
  imports WIDEEND-SYNTAX
  imports DOMAINS
  imports FLOAT
  configuration <k> $PGM:Pgm </k> <out> 0.0 </out>
  rule <k> go(X) => next() ... </k> <out> _ => absFloat(X) </out>
  rule <k> next() => done() ... </k>
endmodule
"#;

/// A Float of a format the backend does not compute (p113x15) has a value the definition
/// gives: `/Float` of two such values halts with the unsupported-hook error naming the hook and
/// the format, not a builtin error, on the canonical text of its operands as on the written one.
/// `absFloat` is total, so its application is left unevaluated where it is computed and the run
/// goes on (`next()` reaches `done()`); it is refused only at the end, where the final
/// configuration holds it.
#[test]
fn krun_reports_a_float_format_it_does_not_compute_as_an_unsupported_hook() {
    for (program, hook) in [
        ("dv(1.0p113x15, 3.0p113x15)", "FLOAT.div"),
        ("ab(1.0p113x15)", "FLOAT.abs"),
    ] {
        let output = krun_mint_program(WIDE_FLOAT_KEYS, "WIDE", program);
        assert!(!output.status.success(), "{program}");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(&format!("unsupported hook '{hook}'")) && stderr.contains("p113x15"),
            "{program}: {stderr}"
        );
        assert!(
            !stderr.contains("does not compute on floating-point numbers"),
            "{program}: {stderr}"
        );
    }
    let output = krun_mint_program(WIDE_FLOAT_AT_THE_END, "WIDEEND", "go(1.0p113x15)");
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("unsupported hook 'FLOAT.abs'") && stderr.contains("p113x15"),
        "{stderr}"
    );
    assert!(
        stderr.contains("halted at depth 2"),
        "the run is refused at its end, after next() steps to done(): {stderr}"
    );
}

/// A sort named Float without the `FLOAT.Float` hook (repro `r3c/unhooked.k`): a token sort whose
/// tokens `1.0` and `1.00` are two values.
const UNHOOKED_FLOAT_TOKENS: &str = r#"
module UNHOOKED-SYNTAX
  syntax Int ::= r"[0-9]+" [token]
  syntax Float ::= r"[0-9]+[.][0-9]+" [token]
  syntax Pgm ::= go() | gf()
endmodule
module UNHOOKED
  imports UNHOOKED-SYNTAX
  configuration <k> $PGM:Pgm </k>
  syntax KItem ::= g(Float) | matched()
  rule <k> g(#token("1.0", "Float")) => matched() ... </k>
endmodule
module UNHOOKED-SPEC
  imports UNHOOKED
  claim <k> g(#token("1.00", "Float")) => matched() ... </k>
endmodule
"#;

/// The tokens of an unhooked sort named Float keep their text: the rule on `1.0` does not apply
/// to `1.00`, so the claim is disproved, never proven.
#[test]
fn kprove_keeps_the_tokens_of_an_unhooked_float_sort_distinct() {
    let (verdict, stdout) = kprove_single_claim(UNHOOKED_FLOAT_TOKENS, "UNHOOKED-SPEC", "UNHOOKED");
    assert_eq!(verdict, "disproved", "{stdout}");
}

/// Float programs over literals and over operands from the program (repro `fl.k`, `fl2.k`,
/// `fl3.k`).
const FLOAT_VALUES: &str = r#"
module FLV-SYNTAX
  imports FLOAT-SYNTAX
  imports INT-SYNTAX
  syntax Op ::= add(Float, Float) | key(Float, Float) | prog(Int)
endmodule
module FLV
  imports FLV-SYNTAX
  imports DOMAINS
  imports COLLECTIONS
  imports FLOAT
  configuration <k> $PGM:Op </k>
  syntax KItem ::= r(K)
  rule add(X, Y) => r(X +Float Y) ~> r((X +Float Y) ==K 2.0) ~> r((X +Float Y) ==Float 2.0)
  rule key(X, Y) => r(size(X |-> 1 Y |-> 2))
  rule prog(0) => r(size(1.0 |-> 1 1.00 |-> 2))
  rule prog(1) => r(keys_list(2.0 |-> 1 1.5 |-> 2))
  rule prog(2) => r(keys_list(0.2e1 |-> 1 1.5 |-> 2))
  rule prog(3) => r(2.0 ==K 0.2e1)
  rule prog(4) => r(1.0 ==K 1.00)
endmodule
"#;

/// A Float value is one term whatever its spelling: `1.0 +Float 1.0` is the literal `2.0`
/// (`==K` holds), `2.0 ==K 0.2e1` and `1.0 ==K 1.00` hold, the keys of two maps that bind one
/// value under two spellings are listed alike, and a map that binds one value twice under two
/// spellings is undefined.
#[test]
fn krun_compares_float_values_not_spellings() {
    let run = |program: &str| -> String {
        krun_sorted_program(FLOAT_VALUES, "FLV", "Op", program, &[])
            .split_whitespace()
            .collect()
    };
    let sum = run("add(1.0, 1.0)");
    assert!(
        sum.contains(r#"\dv{SortFloat{}}("2.0000000000000000e+00p53x11")"#)
            && sum.matches(r#"\dv{SortBool{}}("true")"#).count() == 2
            && !sum.contains(r#"\dv{SortBool{}}("false")"#),
        "{sum}"
    );
    for program in ["prog(3)", "prog(4)"] {
        let output = run(program);
        assert!(
            output.contains(r#"\dv{SortBool{}}("true")"#),
            "{program}: {output}"
        );
    }
    let keys = |program: &str| {
        let output = run(program);
        Regex::new(r#"\\dv\{SortFloat\{\}\}\("([^"]*)"\)"#)
            .unwrap()
            .captures_iter(&output)
            .map(|found| found[1].to_owned())
            .collect::<Vec<_>>()
    };
    assert_eq!(keys("prog(1)"), keys("prog(2)"));
    assert_eq!(keys("prog(1)").len(), 2);
    for program in ["prog(0)", "key(1.0, 1.00)"] {
        let output = run(program);
        assert!(
            output.contains(r"\bottom{SortGeneratedTopCell{}}()")
                && !output.contains(r#"\dv{SortInt{}}("2")"#),
            "{program} counts one key twice: {output}"
        );
    }
}

/// A membership hook declared with an item of a strict subsort of the collection's element sort:
/// `Val "inS" Set` asks whether a `Val` is an element of a set of `KItem`s, where a `Val` used as
/// a `KItem` is its injection.
const ITEM_OF_SUBSORT_MEMBERSHIP: &str = r#"
requires "domains.md"
module INS-SYNTAX
  imports BOOL-SYNTAX
  syntax Val ::= v() | w()
  syntax Pgm ::= go(Val) | check(Val) | done(Bool)
endmodule
module INS
  imports INS-SYNTAX
  imports SET
  imports BOOL
  configuration <k> $PGM:Pgm </k>
  syntax Bool ::= Val "inS" Set [function, total, hook(SET.in)]
  rule <k> go(V) => done(V inS SetItem(V)) ~> done(w() inS SetItem(V)) ... </k>
  rule <k> check(V) => done(V inS SetItem(V)) ... </k>
endmodule
"#;

/// `v() inS SetItem(v())` is `true`: the set holds `v()` injected into `KItem`, which is the
/// element the `Val` item denotes; `w() inS SetItem(v())` is `false`.
#[test]
fn krun_reads_a_membership_item_of_a_subsort_as_its_injection() {
    let go = compact_success(&krun_mint_program(
        ITEM_OF_SUBSORT_MEMBERSHIP,
        "INS",
        "go(v())",
    ));
    assert!(
        go.contains(
            r#"kseq{}(inj{SortPgm{},SortKItem{}}(Lbldone'LParUndsRParUnds'INS-SYNTAX'Unds'Pgm'Unds'Bool{}(\dv{SortBool{}}("true"))),kseq{}(inj{SortPgm{},SortKItem{}}(Lbldone'LParUndsRParUnds'INS-SYNTAX'Unds'Pgm'Unds'Bool{}(\dv{SortBool{}}("false"))),dotk{}()))"#
        ),
        "{go}"
    );
}

/// The claim that `v() inS SetItem(v())` is `false` is not proven: the item is the set's element,
/// and the ground claim is disproved at the `done(true)` leaf; the claim that it is `true` is
/// proven.
#[test]
fn kprove_does_not_prove_a_subsort_item_absent_from_a_set_holding_it() {
    for (spec, value, expected) in [
        ("INS-FALSE", "false", "disproved"),
        ("INS-TRUE", "true", "proven"),
    ] {
        let source = format!(
            "{ITEM_OF_SUBSORT_MEMBERSHIP}module {spec}\n  imports INS\n  \
             claim <k> check(v()) => done({value}) ... </k>\nendmodule\n"
        );
        let (verdict, stdout) = kprove_single_claim(&source, spec, "INS");
        assert_eq!(verdict, expected, "{spec}: {stdout}");
    }
}

/// `krun` of `program` (a `Pgm`) in the definition `source` with main module `module`.
fn krun_mint_program(source: &str, module: &str, program: &str) -> Output {
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();
    let compiled = root.join("compiled");
    kcompile_for_krun(&definition, &["--main-module", module], &compiled);
    let program_file = root.join("program.pgm");
    fs::write(&program_file, program).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["krun", "--definition"])
        .arg(&compiled)
        .arg(&program_file)
        .args(["--sort", "Pgm", "--io", "off"])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    fs::remove_dir_all(root).unwrap();
    output
}

/// The final configuration of a successful `krun`, without whitespace.
fn compact_success(output: &Output) -> String {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout)
        .split_whitespace()
        .collect()
}

const MINT_DOMAIN_VALUES: &str = r#"
requires "domains.md"
module MINTDV-SYNTAX
  imports INT-SYNTAX
  imports MINT-SYNTAX
  syntax MInt{8}
  syntax Pgm ::= go() | m()
endmodule
module MINTDV
  imports MINTDV-SYNTAX
  imports INT
  imports MINT
  imports BOOL
  imports K-EQUAL
  configuration <k> $PGM:Pgm </k>
  syntax KItem ::= Bool | f(MInt{8}) | matched() | lit(MInt{8})
  rule <k> go() => (256p8 ==K 0p8) ~> (-1p8 ==K 255p8) ~> lit(0377p8) ... </k>
  rule <k> m() => f(256p8) ... </k>
  rule <k> f(0p8) => matched() ... </k>
endmodule
"#;

/// A machine-integer literal denotes its signed decimal reduced modulo `2^W`: `256p8` is `0p8`,
/// `-1p8` is `255p8`, and `0377p8` (decimal digits) is `121p8`. `==K` and rule matching see one
/// term for each element, and the result prints the residue.
#[test]
fn krun_reads_mint_literals_as_their_residue() {
    let go = compact_success(&krun_mint_program(MINT_DOMAIN_VALUES, "MINTDV", "go()"));
    assert!(
        go.contains(
            r#"kseq{}(inj{SortBool{},SortKItem{}}(\dv{SortBool{}}("true")),kseq{}(inj{SortBool{},SortKItem{}}(\dv{SortBool{}}("true")),kseq{}(Lbllit'LParUndsRParUnds'MINTDV'Unds'KItem'Unds'MInt{}(\dv{SortMInt{Sort8{}}}("121p8")),dotk{}())))"#
        ),
        "{go}"
    );
    let m = compact_success(&krun_mint_program(MINT_DOMAIN_VALUES, "MINTDV", "m()"));
    assert!(
        m.contains("Lblmatched'LParRParUnds'MINTDV'Unds'KItem{}()"),
        "{m}"
    );
}

/// An `owise` equation applies only where no other equation does: `f(0p8)` is `f(256p8)`, which
/// the first equation gives the value 1.
#[test]
fn krun_owise_equation_sees_one_mint_element_in_two_spellings() {
    let source = r#"
requires "domains.md"
module OW-SYNTAX
  imports INT-SYNTAX
  imports MINT-SYNTAX
  syntax MInt{8}
  syntax Pgm ::= go()
endmodule
module OW
  imports OW-SYNTAX
  imports INT
  imports MINT
  configuration <k> $PGM:Pgm </k>
  syntax Int ::= f(MInt{8}) [function]
  rule f(256p8) => 1
  rule f(0p8) => 2 [owise]
  syntax KItem ::= Int
  rule <k> go() => f(0p8) ... </k>
endmodule
"#;
    let output = compact_success(&krun_mint_program(source, "OW", "go()"));
    assert!(
        output.contains(r#"kseq{}(inj{SortInt{},SortKItem{}}(\dv{SortInt{}}("1")),dotk{}())"#),
        "{output}"
    );
}

/// A token of `MInt{8}` outside the literal syntax names no element of the sort, so the
/// definition holding it is refused when `krun` loads it.
#[test]
fn krun_refuses_a_mint_token_outside_the_literal_syntax() {
    let source = r#"
requires "domains.md"
module TOK-SYNTAX
  imports INT-SYNTAX
  imports MINT-SYNTAX
  syntax MInt{8}
  syntax Pgm ::= go()
endmodule
module TOK
  imports TOK-SYNTAX
  imports MINT
  configuration <k> $PGM:Pgm </k>
  syntax KItem ::= t(MInt{8})
  rule <k> go() => t(#token("abcp8", "MInt{8}")) ... </k>
endmodule
"#;
    let output = krun_mint_program(source, "TOK", "go()");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success() && stderr.contains(r#"Invalid domain value "abcp8""#),
        "{stderr}\n{}",
        String::from_utf8_lossy(&output.stdout)
    );
}

/// A sort hooked `MINT.MInt` under its own name has no width argument, so no text is a literal of
/// it, and the definition holding one of its tokens is refused when `krun` loads it.
#[test]
fn krun_refuses_a_sort_hooked_mint_under_another_name() {
    let source = r#"
requires "domains.md"
module HOOKMINT-SYNTAX
  imports INT-SYNTAX
  syntax Word [hook(MINT.MInt)]
  syntax Word ::= r"[0-9]+w" [token, prec(2)]
  syntax Pgm ::= go()
endmodule
module HOOKMINT
  imports HOOKMINT-SYNTAX
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> $PGM:Pgm </k>
  syntax KItem ::= Bool
  rule <k> go() => (#token("07w", "Word") ==K #token("7w", "Word")) ... </k>
endmodule
"#;
    let output = krun_mint_program(source, "HOOKMINT", "go()");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success() && stderr.contains("Invalid domain value"),
        "{stderr}\n{}",
        String::from_utf8_lossy(&output.stdout)
    );
}

/// The total machine-integer hooks evaluate on literals: `Int2MInt` takes the width of the sort
/// its cast gives, `+MInt` and `*MInt` wrap modulo `2^8` (300 is 44; 20000 is 32), and the
/// unsigned order compares residues.
#[test]
fn krun_evaluates_the_total_mint_hooks_on_literals() {
    let source = r#"
requires "domains.md"
module MINT-PROBE-SYNTAX
  imports INT-SYNTAX
  imports MINT-SYNTAX
  syntax MInt{8}
  syntax Pgm ::= run(Int, Int)
endmodule
module MINT-PROBE
  imports MINT-PROBE-SYNTAX
  imports INT
  imports MINT
  imports BOOL
  configuration <k> $PGM:Pgm </k>
  syntax KItem ::= res(Int, Int, Int, Bool)
  rule <k> run(A, B) => res(
           MInt2Unsigned(Int2MInt(A)::MInt{8} +MInt Int2MInt(B)::MInt{8}),
           MInt2Signed(Int2MInt(A)::MInt{8} *MInt Int2MInt(B)::MInt{8}),
           bitwidthMInt(255p8),
           Int2MInt(A)::MInt{8} <uMInt Int2MInt(B)::MInt{8}) </k>
endmodule
"#;
    let output = compact_success(&krun_mint_program(source, "MINT-PROBE", "run(200, 100)"));
    assert!(
        output.contains(
            r#"(\dv{SortInt{}}("44"),\dv{SortInt{}}("32"),\dv{SortInt{}}("8"),\dv{SortBool{}}("false"))"#
        ),
        "{output}"
    );
}

/// Division, remainder and shifts of `MInt{8}`: `-100` is the pattern `156p8`, so
/// `/uMInt 3p8` is 52, `/sMInt` truncates `-100 / 3` toward zero (-33), `%sMInt` keeps the
/// dividend's sign (-1), a shift by 9 or 200 (at least the width) gives 0, and `>>aMInt` copies
/// the sign bit (206 is `-50`).
const MINT_DIVISION_AND_SHIFTS: &str = r#"
requires "domains.md"
module MINTLIT-SYNTAX
  imports INT-SYNTAX
  imports MINT-SYNTAX
  syntax MInt{8}
  syntax Pgm ::= go(Int)
endmodule
module MINTLIT
  imports MINTLIT-SYNTAX
  imports INT
  imports MINT
  configuration <k> $PGM:Pgm </k>
  syntax KItem ::= vals(Int, Int, Int, Int, Int, Int)
  rule <k> go(I) => vals(
     MInt2Unsigned(Int2MInt(I)::MInt{8} /uMInt 3p8),
     MInt2Signed(Int2MInt(I)::MInt{8} /sMInt 3p8),
     MInt2Signed(Int2MInt(I)::MInt{8} %sMInt 3p8),
     MInt2Unsigned(Int2MInt(I)::MInt{8} <<MInt 9p8),
     MInt2Unsigned(Int2MInt(I)::MInt{8} >>aMInt 1p8),
     MInt2Unsigned(Int2MInt(I)::MInt{8} >>lMInt 200p8)) </k>
endmodule
"#;

#[test]
fn krun_evaluates_mint_division_remainder_and_shifts_on_literals() {
    let output = compact_success(&krun_mint_program(
        MINT_DIVISION_AND_SHIFTS,
        "MINTLIT",
        "go(-100)",
    ));
    assert!(
        output.contains(
            r#"(\dv{SortInt{}}("52"),\dv{SortInt{}}("-33"),\dv{SortInt{}}("-1"),\dv{SortInt{}}("0"),\dv{SortInt{}}("206"),\dv{SortInt{}}("0"))"#
        ),
        "{output}"
    );
}

/// No quotient by zero exists and `/uMInt` is partial, so `1p8 /uMInt 0p8` is undefined.
#[test]
fn kore_simplify_of_a_mint_division_by_zero_is_bottom() {
    let (root, definition) = fixture();
    fs::write(&definition, MINT_DIVISION_AND_SHIFTS).unwrap();
    let compiled = root.join("compiled");
    kcompile_for_krun(&definition, &["--main-module", "MINTLIT"], &compiled);
    let pattern = root.join("udiv0.kore");
    fs::write(
        &pattern,
        r#"Lbl'UndsSlsh'uMInt'UndsUnds'MINT'Unds'MInt'Unds'MInt'Unds'MInt{Sort8{}}(\dv{SortMInt{Sort8{}}}("1p8"), \dv{SortMInt{Sort8{}}}("0p8"))"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kore-simplify", "-m", "MINTLIT", "-p"])
        .arg(&pattern)
        .arg(compiled.join("definition.kore"))
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap().trim(),
        r#"\bottom{SortMInt{Sort8{}}}()"#
    );
    fs::remove_dir_all(root).unwrap();
}

/// `krust kore-simplify` of `pattern` in `definition` (module `MAIN`): its standard output,
/// asserting success.
fn kore_simplify_in(root: &Path, definition: &Path, pattern: &str) -> String {
    let path = root.join("pattern.kore");
    fs::write(&path, pattern).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("kore-simplify")
        .arg(definition)
        .args(["--module", "MAIN", "--pattern"])
        .arg(&path)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{pattern}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

/// A sort named `SortInt` declared without the hook `INT.Int` is still the integers, as the SMT
/// translation and the INT hooks read it: its literal `07` is `7`, and `X = 07` contradicts
/// `X =/= 7`.
#[test]
fn kore_simplify_reads_an_unhooked_sort_int_as_the_integers() {
    let (root, _) = fixture();
    let definition = root.join("unhooked-int.kore");
    fs::write(
        &definition,
        r#"[]
module MAIN
  sort SortInt{} [hasDomainValues{}()]
  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
  sort SortK{} []
  symbol c{}(SortInt{}) : SortK{} [constructor{}(), functional{}(), injective{}()]
endmodule []
"#,
    )
    .unwrap();
    let compact = |text: String| text.split_whitespace().collect::<String>();
    assert_eq!(
        compact(kore_simplify_in(
            &root,
            &definition,
            r#"c{}(\dv{SortInt{}}("07"))"#
        )),
        r#"c{}(\dv{SortInt{}}("7"))"#
    );
    assert_eq!(
        compact(kore_simplify_in(
            &root,
            &definition,
            r#"\and{SortK{}}(c{}(X:SortInt{}), \and{SortK{}}(\equals{SortInt{}, SortK{}}(X:SortInt{}, \dv{SortInt{}}("07")), \not{SortK{}}(\equals{SortInt{}, SortK{}}(X:SortInt{}, \dv{SortInt{}}("7")))))"#
        )),
        r#"\bottom{SortK{}}()"#
    );
    fs::remove_dir_all(root).unwrap();
}

/// A definition compiled without the prelude declares `SortBool` without its hook, and its
/// generated sort-predicate equations hold the literals `true` and `false`; the backend loads it
/// and evaluates its functions.
#[test]
fn a_definition_compiled_without_the_prelude_loads_its_unhooked_booleans() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  syntax State ::= "a" [function, symbol(a)] | "b" [symbol(b)]
  rule a => b
endmodule
"#,
    )
    .unwrap();
    let compiled = root.join("compiled");
    kcompile_for_krun(
        &definition,
        &[
            "--main-module",
            "MAIN",
            "--syntax-module",
            "MAIN",
            "--no-prelude",
        ],
        &compiled,
    );
    let kore = compiled.join("definition.kore");
    let text = fs::read_to_string(&kore).unwrap();
    assert!(
        text.contains("sort SortBool{} [hasDomainValues{}()")
            && text.contains(r#"\dv{SortBool{}}("true")"#),
        "{text}"
    );
    assert_eq!(kore_simplify_in(&root, &kore, "Lbla{}()\n"), "Lblb{}()\n");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kast_omits_inferred_parametric_label_arguments() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  syntax A ::= "a" [symbol(a)]
  syntax {S} S ::= "pair(" S "," S ")" [symbol(pair)]
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kast",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--batch-case",
            "pair",
            "A",
            "pair(a,a)",
            "--output",
            "json",
            "--no-prelude",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let value: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(value["pair"]["term"]["label"]["name"], "pair");
    assert_eq!(
        value["pair"]["term"]["label"]["params"],
        serde_json::json!([])
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kast_backend_selects_the_matching_module_view() {
    let source = r#"
module SYMBOLIC [symbolic]
  syntax Exp ::= "symbolic" [symbol(symbolicOnly)]
endmodule

module CONCRETE [concrete]
  syntax Exp ::= "concrete" [symbol(concreteOnly)]
endmodule

module MAIN
  imports SYMBOLIC
  imports CONCRETE
endmodule
"#;
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();
    let binary = env!("CARGO_BIN_EXE_krust");
    let kast = |backend: Option<&str>, expression: &str| {
        let mut command = Command::new(binary);
        command.args([
            "kast",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--sort",
            "Exp",
            "--expression",
            expression,
            "--no-prelude",
        ]);
        if let Some(backend) = backend {
            command.args(["--backend", backend]);
        }
        command.output().unwrap()
    };

    // Without `--backend`, kast parses against the same Rust-backend view that `kcompile` and
    // `krun` use by default, so the grammar can never disagree with the compiled artifact.
    assert!(kast(None, "symbolic").status.success());
    assert!(!kast(None, "concrete").status.success());
    assert!(kast(Some("rust"), "symbolic").status.success());
    assert!(!kast(Some("rust"), "concrete").status.success());
    assert!(kast(Some("llvm"), "concrete").status.success());
    assert!(!kast(Some("llvm"), "symbolic").status.success());

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_binds_declared_configuration_variables() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  syntax State ::= "a" [symbol(a)]
  syntax State ::= "b" [symbol(b)]
  syntax Env ::= "ready" [symbol(ready)]
  configuration
    <top>
      <k> $PGM:State </k>
      <env> $ENV:Env </env>
    </top>
  rule <k> a => b </k> <env> ready </env>
endmodule
"#,
    )
    .unwrap();
    let binary = env!("CARGO_BIN_EXE_krust");
    let output = Command::new(binary)
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "State",
            "--expression",
            "a",
            "-cENV=ready",
            "--depth",
            "10",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("Lblb{}()"), "{stdout}");
    assert!(stdout.contains("Lblready{}()"), "{stdout}");
    assert!(
        !stdout.contains("\\bottom{SortGeneratedTopCell{}}("),
        "{stdout}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_runs_a_definition_that_declares_no_program_variable() {
    // K regression-new issue-946: `krun --definition test-kompiled` with no positional
    // argument runs a configuration without `$PGM`; the reference builds the initial
    // configuration from an empty variable map instead of reading standard input.
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax KItem ::= "start" [symbol(start)]
  configuration <k> start </k> <env> 1 </env>
endmodule
"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "KItem",
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("Lblstart{}()"), "{stdout}");
    assert!(stdout.contains("\\dv{SortInt{}}(\"1\")"), "{stdout}");
    assert!(
        !stdout.contains("\\bottom{SortGeneratedTopCell{}}("),
        "{stdout}"
    );

    fs::remove_dir_all(root).unwrap();
}

/// An equation whose right-hand side has a variable its left-hand side does not bind is not
/// used, so `f(3)` stays in the result; the warning says why, naming the variable as the rule
/// writes it, and names the equation's variable in its printed requires.
#[test]
fn krun_explains_a_call_kept_by_an_equation_with_an_unbound_result_variable() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  syntax KItem ::= done(Int) [symbol(done)]
  configuration <k> done(f(3)) </k>
  rule f(X) => Y requires Y ==Int X +Int 1
endmodule
"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "KItem",
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stderr}");
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        stdout.contains(r#"Lblf{}(\dv{SortInt{}}("3"))"#),
        "{stdout}"
    );
    let warnings = stderr
        .lines()
        .filter(|line| line.starts_with("warning: equation "))
        .collect::<Vec<_>>();
    assert_eq!(warnings.len(), 1, "{stderr}");
    let warning = warnings[0];
    assert!(warning.contains("definition.k:8:3"), "{warning}");
    assert!(
        warning.contains(
            "its right-hand side or ensures uses Y, which its left-hand side does not bind"
        ),
        "{warning}"
    );
    assert!(
        warning.contains(r#"Eq-hVarY:SortInt{}, \dv{SortInt{}}("4")"#)
            && warning.contains("(Eq-hVarY is the equation's variable Y)"),
        "{warning}"
    );

    fs::remove_dir_all(root).unwrap();
}

/// Run `krust krun` on `source` as the definition `MAIN` with sort `KItem`; its stdout and the
/// lines of its stderr that warn about an equation.
fn krun_equation_warnings(source: &str) -> (String, Vec<String>) {
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "KItem",
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stderr}");
    let warnings = stderr
        .lines()
        .filter(|line| {
            line.starts_with("warning: equation ") || line.starts_with("warning: condition of")
        })
        .map(str::to_owned)
        .collect();
    fs::remove_dir_all(root).unwrap();
    (String::from_utf8(output.stdout).unwrap(), warnings)
}

/// An equation passed over for an unbound result variable is not reported when another
/// equation evaluates the call: the same-priority function equation `gb`, or the
/// lower-priority simplification `hb`.
#[test]
fn krun_does_not_explain_a_call_that_another_equation_evaluates() {
    let (stdout, warnings) = krun_equation_warnings(
        r#"
module MAIN
  imports INT
  imports BOOL
  syntax Int ::= g(Int) [function, symbol(g)]
  syntax Int ::= h(Int) [function, symbol(h)]
  syntax KItem ::= done(Int, Int) [symbol(done)]
  configuration <k> done(g(3), h(5)) </k>
  rule [gu]: g(X) => Y requires Y ==Int X +Int 1
  rule [gb]: g(X) => X +Int 1
  rule [hu]: h(X) => Y requires Y ==Int X +Int 1 [simplification(10)]
  rule [hb]: h(X) => X +Int 1 [simplification(60)]
endmodule
"#,
    );
    assert!(
        stdout.contains(r#"Lbldone{}(\dv{SortInt{}}("4"), \dv{SortInt{}}("6"))"#),
        "{stdout}"
    );
    assert!(warnings.is_empty(), "{warnings:?}");
}

/// `h3(1)` is a normal form (the only equation of `h3` rewrites `h3(0)`), so it is a value other
/// than `k` and `k2`: `f(k)` and `f(k2)` fail `f(h3(1)) => 1` and take the `owise` rule, as
/// `f(h3(2))` does, and as they would with the two sides of the match exchanged.
#[test]
fn krun_reads_a_ground_normal_form_on_a_left_hand_side_as_its_value() {
    let (stdout, warnings) = krun_equation_warnings(
        r#"
module MAIN
  imports INT
  syntax A ::= "k" [symbol(k)] | "k2" [symbol(k2)] | h3(Int) [symbol(h3)]
  syntax Int ::= f(A) [function, symbol(f)]
  syntax KItem ::= done(Int, Int, Int, Int) [symbol(done)]
  configuration <k> done(f(k), f(k2), f(h3(1)), f(h3(2))) </k>
  rule h3(0) => k [anywhere]
  rule f(h3(1)) => 1
  rule f(_) => 2 [owise]
endmodule
"#,
    );
    assert!(
        stdout.contains(
            r#"Lbldone{}(\dv{SortInt{}}("2"), \dv{SortInt{}}("2"), \dv{SortInt{}}("1"), \dv{SortInt{}}("2"))"#
        ),
        "{stdout}"
    );
    assert!(warnings.is_empty(), "{warnings:?}");
}

/// The requires-only `Z` of `pz` reaches the subject `q(Z)` of `qu` while the requires of `pz`
/// is simplified. The warning for `qu` explains `qu`'s own `B` as the equation's variable, and
/// `pz`'s `Z` as a variable of an equation without calling it a variable of `qu`, whether `qu`
/// names its bound variable `A` or `Z`.
#[test]
fn krun_names_only_the_reported_equations_own_variables() {
    for bound in ["A", "Z"] {
        let (stdout, warnings) = krun_equation_warnings(&format!(
            r#"
module MAIN
  imports INT
  imports BOOL
  syntax Int ::= q(Int) [function, symbol(q)]
  syntax Bool ::= p(Int) [function, symbol(p)]
  syntax KItem ::= done(Bool) [symbol(done)]
  configuration <k> done(p(5)) </k>
  rule [qu]: q({bound}) => B requires B ==Int {bound} +Int 1
  rule [pz]: p(X) => true requires q(Z) ==Int X
  rule [po]: p(_) => false [owise]
endmodule
"#
        ));
        assert!(stdout.contains("Lblp{}"), "{bound}: {stdout}");
        let qu = warnings
            .iter()
            .filter(|warning| warning.starts_with("warning: equation MAIN.qu "))
            .collect::<Vec<_>>();
        assert_eq!(qu.len(), 1, "{bound}: {warnings:?}");
        assert!(
            qu[0].contains("Eq-hVarB is the equation's variable B"),
            "{bound}: {}",
            qu[0]
        );
        assert!(
            qu[0].contains("Eq-hVarZ is a variable of an equation, written Z there"),
            "{bound}: {}",
            qu[0]
        );
        assert!(
            !qu[0].contains("the equation's variable Z"),
            "{bound}: {}",
            qu[0]
        );
    }
}

/// A call left unevaluated only inside the `requires` of an enclosing equation that is then
/// refuted is not in the result, so it is not reported. `f(3)` is attempted while the requires
/// of `k1` on `k(3)` is simplified, since the arguments of `andBool` are simplified before it
/// short-circuits; `k1` is refuted and `k2` evaluates the call. The same holds at each of the 200
/// steps of a loop. A call the result keeps is still reported: in the `<k>` cell, and as the
/// argument of an equation that drops it, whose definedness the result carries. As the untaken
/// branch of `#if` the call is never attempted, so nothing reports it, though the result carries
/// its definedness.
#[test]
fn krun_reports_a_call_left_unevaluated_only_where_the_result_keeps_it() {
    let source = |configuration: &str| {
        format!(
            r#"
module MAIN
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Int ::= f(Int) [function, symbol(f)]
  syntax Int ::= k(Int) [function, symbol(k)]
  syntax Int ::= drop(Int) [function, symbol(drop)]
  syntax KItem ::= done(Int) [symbol(done)]
  syntax KItem ::= step(Int) [symbol(step)]
  configuration <k> {configuration} </k>
  rule [fu]: f(X) => Y requires Y ==Int X +Int 1
  rule [k1]: k(X) => 1 requires X <Int 0 andBool f(X) ==Int 4
  rule [k2]: k(_) => 2 [owise]
  rule drop(_) => 0
  rule <k> step(N) => step(N +Int k(N) -Int 1) </k> requires N <Int 200
  rule <k> step(N) => done(N) </k> requires N >=Int 200
endmodule
"#
        )
    };
    for (configuration, result) in [("done(k(3))", "2"), ("step(0)", "200")] {
        let (stdout, warnings) = krun_equation_warnings(&source(configuration));
        assert!(
            stdout.contains(&format!(r#"Lbldone{{}}(\dv{{SortInt{{}}}}("{result}"))"#)),
            "{configuration}: {stdout}"
        );
        assert!(warnings.is_empty(), "{configuration}: {warnings:?}");
    }
    let (stdout, warnings) =
        krun_equation_warnings(&source("done(#if true #then 7 #else f(3) #fi)"));
    assert!(stdout.contains("Lblf{}"), "{stdout}");
    assert!(warnings.is_empty(), "{warnings:?}");
    for configuration in ["done(f(3))", "done(drop(f(3)))"] {
        let (stdout, warnings) = krun_equation_warnings(&source(configuration));
        assert!(stdout.contains("Lblf{}"), "{configuration}: {stdout}");
        assert_eq!(warnings.len(), 1, "{configuration}: {warnings:?}");
        assert!(
            warnings[0].starts_with("warning: equation MAIN.fu ")
                && warnings[0].contains(
                    "no other equation rewrote the term it matched, which was left unevaluated"
                ),
            "{configuration}: {}",
            warnings[0]
        );
    }
}

/// A call that the same simplification leaves unevaluated and then drops is not in the result,
/// and the result does not depend on its value, so it is not reported. With `f` total, `f(3)`
/// is dropped by the requires of `k1`, whose first disjunct holds (so `k1` applies), and by
/// `drop`, whose definedness obligation `f` being total discharges; the same holds at each of
/// the 200 steps of a loop. A call the result keeps is still reported.
#[test]
fn krun_does_not_report_a_call_the_same_simplification_drops() {
    let source = |configuration: &str| {
        format!(
            r#"
module MAIN
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Int ::= f(Int) [function, total, symbol(f)]
  syntax Int ::= k(Int) [function, symbol(k)]
  syntax Int ::= drop(Int) [function, symbol(drop)]
  syntax KItem ::= done(Int) [symbol(done)]
  syntax KItem ::= step(Int) [symbol(step)]
  configuration <k> {configuration} </k>
  rule [fu]: f(X) => Y requires Y ==Int X +Int 1
  rule [k1]: k(X) => 1 requires X >=Int 0 orBool f(X) ==Int 4
  rule [k2]: k(_) => 2 [owise]
  rule drop(_) => 0
  rule <k> step(N) => step(N +Int k(N)) </k> requires N <Int 200
  rule <k> step(N) => done(N) </k> requires N >=Int 200
endmodule
"#
        )
    };
    for (configuration, result) in [
        ("done(k(3))", "1"),
        ("step(0)", "200"),
        ("done(drop(f(3)))", "0"),
    ] {
        let (stdout, warnings) = krun_equation_warnings(&source(configuration));
        assert!(
            stdout.contains(&format!(r#"Lbldone{{}}(\dv{{SortInt{{}}}}("{result}"))"#)),
            "{configuration}: {stdout}"
        );
        assert!(warnings.is_empty(), "{configuration}: {warnings:?}");
    }
    let (stdout, warnings) = krun_equation_warnings(&source("done(f(3))"));
    assert!(stdout.contains("Lblf{}"), "{stdout}");
    assert_eq!(warnings.len(), 1, "{warnings:?}");
    assert!(
        warnings[0].starts_with("warning: equation MAIN.fu "),
        "{}",
        warnings[0]
    );
}

#[test]
fn installed_cli_uses_embedded_pinned_builtins_by_default() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        "module MAIN\n  imports DOMAINS\n  syntax Exp ::= Int\nendmodule\n",
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kast",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--sort",
            "Exp",
            "--expression",
            "42",
        ])
        .current_dir(&root)
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "#token(\"42\",\"Int\")\n"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_executes_a_concrete_program_in_process() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  syntax State ::= "a" [symbol(a)]
  syntax State ::= "b" [symbol(b)]
  configuration <k> $PGM:State </k>
  rule <k> a => b </k>
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "State",
            "--expression",
            "a",
            "--depth",
            "10",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains("Lblb{}()"), "{output}");
    assert!(!output.contains("Lbla{}()"), "{output}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_fun_with_an_uncast_variable_executes_on_an_empty_user_list() {
    // reference: k/result/bin/kompile --backend haskell test.k && k/result/bin/krun program.pgm
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/kompile/fun-int-list-config");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "FUN-INT-LIST-CONFIG",
            "--syntax-module",
            "FUN-INT-LIST-CONFIG",
            "--sort",
            "KItem",
            fixtures.join("program.pgm").to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains(r#"\dv{SortInt{}}("0")"#), "{output}");
    assert!(!output.contains("Hash'lambda"), "{output}");
    assert!(!output.contains(r"\ceil"), "{output}");
}

#[test]
fn krun_populates_additional_configuration_variables() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports MAP
  syntax State ::= "a" [symbol(a)]
                 | "b" [symbol(b)]
  configuration <k> $PGM:State </k> <env> $ENV:Map </env>
  rule <k> a => b </k> <env> .Map </env>
endmodule
"#,
    )
    .unwrap();

    // Both runs, with and without `$ENV`, use one compiled definition.
    let compiled = root.join("compiled");
    kcompile_for_krun(&definition, &["--main-module", "MAIN"], &compiled);
    let krun = || {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args(["krun", "--definition"]).arg(&compiled).args([
            "--sort",
            "State",
            "--expression",
            "a",
        ]);
        command
    };
    let output = krun()
        .args(["-c", "ENV=.Map", "--depth", "10"])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains("Lblb{}()"), "{output}");
    assert!(output.contains("Lbl'Stop'Map{}()"), "{output}");

    let missing = krun().output().unwrap();
    assert!(!missing.status.success());
    assert!(
        String::from_utf8_lossy(&missing.stderr)
            .contains("missing required configuration variable $ENV; pass `-c ENV=VALUE`"),
        "{}",
        String::from_utf8_lossy(&missing.stderr)
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_krun_supplies_io_and_stdin_for_stream_cells() {
    // reference: k/result/bin/krun program.pgm --definition ref --output kore </dev/null
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/io");
    let expected =
        parse_pattern(&fs::read_to_string(fixtures.join("default.kore")).unwrap()).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("io.k").to_str().unwrap(),
            fixtures.join("program.pgm").to_str().unwrap(),
            "--main-module",
            "IO",
            "--sort",
            "Int",
            "--depth",
            "0",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert_eq!(parse_pattern(&stdout).unwrap(), expected);
    assert!(!stdout.contains(r"\bottom"), "{stdout}");
}

/// krust's console bytes for `program` of the `non-ascii-stdout` reference fixture, live I/O.
fn non_ascii_stdout(program: &str) -> Vec<u8> {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/cli/non-ascii-stdout");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("test.k").to_str().unwrap(),
            fixtures.join(program).to_str().unwrap(),
            "--main-module",
            "NON-ASCII-STDOUT",
            "--sort",
            "Pgm",
            "--output",
            "none",
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    output.stdout
}

/// A `String` is a sequence of code points, and the console writes each as one byte, its code
/// point (docs/compatibility.md, console input and output). `"café ÿ!"` is therefore the seven
/// bytes the reference's krun writes for the same program (the LLVM backend's, the pinned
/// reference backend with console I/O; `reference/cli/non-ascii-stdout/stdout.bin`).
/// `"caf\u00e9"` is the same value as `"café"`, so krust writes the same bytes for it; the
/// reference writes `é` as `c3 a9` there, so its console bytes depend on how the literal is
/// spelled (`escaped.stdout.bin`).
#[test]
fn krun_writes_each_non_ascii_character_to_the_console_as_the_byte_of_its_code_point() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/cli/non-ascii-stdout");
    let reference = fs::read(fixtures.join("stdout.bin")).unwrap();
    assert_eq!(reference, b"caf\xe9 \xff!");
    assert_eq!(non_ascii_stdout("program.pgm"), reference);

    assert_eq!(non_ascii_stdout("escaped.pgm"), b"caf\xe9");
    assert_eq!(
        fs::read(fixtures.join("escaped.stdout.bin")).unwrap(),
        b"caf\xc3\xa9"
    );
}

#[test]
fn krun_captured_output_emits_one_complete_stdout_buffer_without_kore_framing() {
    let fixture_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/captured-output/test.k");
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            fixture_path.to_str().unwrap(),
            "--main-module",
            "CAPTURED-OUTPUT",
            "--output-directory",
        ])
        .arg(&compiled)
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );

    let literal = output_with_stdin(&mut captured_output_command(&compiled, "literal"), b"");
    assert!(
        literal.status.success(),
        "{}",
        String::from_utf8_lossy(&literal.stderr)
    );
    assert_eq!(literal.stdout, b"literal output");
    assert!(
        literal.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&literal.stderr)
    );

    let empty = output_with_stdin(&mut captured_output_command(&compiled, "empty"), b"");
    assert!(
        empty.status.success(),
        "{}",
        String::from_utf8_lossy(&empty.stderr)
    );
    assert!(empty.stdout.is_empty());

    let from_stdin = output_with_stdin(
        &mut captured_output_command(&compiled, "stdin"),
        b"piped input\n",
    );
    assert!(
        from_stdin.status.success(),
        "{}",
        String::from_utf8_lossy(&from_stdin.stderr)
    );
    assert_eq!(from_stdin.stdout, b"piped input\noutput");

    let mut kore = Command::new(env!("CARGO_BIN_EXE_krust"));
    kore.args([
        "krun",
        "--definition",
        compiled.to_str().unwrap(),
        "--sort",
        "Pgm",
        "--expression",
        "literal",
        "--io",
        "off",
    ]);
    let kore = output_with_stdin(&mut kore, b"");
    assert!(
        kore.status.success(),
        "{}",
        String::from_utf8_lossy(&kore.stderr)
    );
    let kore_text = String::from_utf8(kore.stdout).unwrap();
    assert!(parse_pattern(&kore_text).is_ok(), "{kore_text}");
    assert_ne!(kore_text.as_bytes(), literal.stdout);

    for (expression, extra, expected) in [
        ("bottom", &[][..], "found 0 leaves"),
        (
            "residual",
            &[][..],
            "found 1 leaf: constraints=1, stdout stream buffers=1",
        ),
        ("branch", &["--strategy", "all"][..], "found 2 leaves"),
    ] {
        let mut command = captured_output_command(&compiled, expression);
        command.args(extra);
        let output = output_with_stdin(&mut command, b"");
        assert!(!output.status.success(), "{expression}");
        assert!(output.stdout.is_empty(), "{expression}");
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(
            stderr.contains(
                "captured output requires exactly one execution leaf, unconstrained and with exactly one stdout stream buffer"
            ),
            "{expression}: {stderr}"
        );
        assert!(stderr.contains(expected), "{expression}: {stderr}");
    }

    let mut explicit_on = captured_output_command(&compiled, "literal");
    explicit_on.args(["--io", "on"]);
    let explicit_on = explicit_on.output().unwrap();
    assert!(!explicit_on.status.success());
    assert!(explicit_on.stdout.is_empty());
    assert!(
        String::from_utf8_lossy(&explicit_on.stderr).contains(
            "--output captured uses buffered stream semantics and cannot be combined with --io on"
        ),
        "{}",
        String::from_utf8_lossy(&explicit_on.stderr)
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_io_on_delivers_committed_transitions_once_without_kore_framing() {
    let (root, compiled) = compiled_live_io_fixture();

    let output = output_with_stdin(&mut live_io_command(&compiled, "multi"), b"");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, b"first second");
    assert!(output.stderr.is_empty());

    let mut mixed = Command::new(env!("CARGO_BIN_EXE_krust"));
    mixed.args([
        "krun",
        "--definition",
        compiled.to_str().unwrap(),
        "--sort",
        "Pgm",
        "--expression",
        "multi",
        "--io",
        "on",
    ]);
    let mixed = output_with_stdin(&mut mixed, b"");
    assert!(!mixed.status.success());
    assert!(mixed.stdout.is_empty());
    assert!(
        String::from_utf8_lossy(&mixed.stderr).contains(
            "use --output none so program output remains separate from KORE result rendering"
        ),
        "{}",
        String::from_utf8_lossy(&mixed.stderr)
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_io_on_keeps_stderr_and_empty_stdout_writes_separate_from_kore_stdout() {
    let (root, compiled) = compiled_live_io_fixture();

    for (expression, expected_stderr) in [
        ("stderr-only", b"stderr only".as_slice()),
        ("empty-stdout", b"after empty stdout".as_slice()),
    ] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "--sort",
            "Pgm",
            "--expression",
            expression,
            "--io",
            "on",
        ]);
        let output = output_with_stdin(&mut command, b"");

        assert!(
            output.status.success(),
            "{expression}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.stderr, expected_stderr, "{expression}");
        let result = String::from_utf8(output.stdout).unwrap();
        assert!(parse_pattern(&result).is_ok(), "{expression}: {result}");
    }

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_io_on_preserves_descriptor_order_and_arbitrary_bytes() {
    let (root, compiled) = compiled_live_io_fixture();

    let ordered = output_with_stdin(&mut live_io_command(&compiled, "ordered"), b"");
    assert!(
        ordered.status.success(),
        "{}",
        String::from_utf8_lossy(&ordered.stderr)
    );
    assert_eq!(ordered.stdout, b"out-1out-2");
    assert_eq!(ordered.stderr, b"err-1!");

    let combined_path = root.join("combined-output");
    let combined = fs::File::create(&combined_path).unwrap();
    let mut combined_command = live_io_command(&compiled, "ordered");
    let mut child = combined_command
        .stdin(Stdio::null())
        .stdout(Stdio::from(combined.try_clone().unwrap()))
        .stderr(Stdio::from(combined))
        .spawn()
        .unwrap();
    assert!(child.wait().unwrap().success());
    assert_eq!(fs::read(&combined_path).unwrap(), b"out-1err-1out-2!");

    let bytes = [0xff, 0x80, 0x00, b'A'];
    let arbitrary = output_with_stdin(&mut live_io_command(&compiled, "bytes"), &bytes);
    assert!(
        arbitrary.status.success(),
        "{}",
        String::from_utf8_lossy(&arbitrary.stderr)
    );
    assert_eq!(arbitrary.stdout, bytes);
    assert!(arbitrary.stderr.is_empty());

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_io_on_prebuffers_input_and_withholds_rejected_candidate_output() {
    let (root, compiled) = compiled_live_io_fixture();

    let input = output_with_stdin(&mut live_io_command(&compiled, "input"), b"A");
    assert!(
        input.status.success(),
        "{}",
        String::from_utf8_lossy(&input.stderr)
    );
    assert_eq!(input.stdout, b"accepted");
    assert!(input.stderr.is_empty());

    // The first `rollback` rule's result is bottom, so its write is withheld; the step offers
    // the configuration to the next rule of the same priority, whose write is delivered.
    let rollback = output_with_stdin(&mut live_io_command(&compiled, "rollback"), b"");
    assert!(
        rollback.status.success(),
        "{}",
        String::from_utf8_lossy(&rollback.stderr)
    );
    assert_eq!(rollback.stdout, b"retained");
    assert!(
        !rollback
            .stderr
            .windows(b"leaked".len())
            .any(|part| part == b"leaked")
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_io_on_rejects_search_and_alternative_execution() {
    let (root, compiled) = compiled_live_io_fixture();

    let mut search = live_io_command(&compiled, "branch");
    search.arg("--search-final");
    let search = output_with_stdin(&mut search, b"");
    assert!(!search.status.success());
    assert!(search.stdout.is_empty());
    assert!(
        String::from_utf8_lossy(&search.stderr)
            .contains("--io on is supported only for ordinary execution, not search")
    );

    // Both alternatives have empty transcripts. The mode is rejected before execution rather
    // than relying on transcript selection to notice a conflict.
    let mut alternatives = live_io_command(&compiled, "branch-empty");
    alternatives.args(["--strategy", "all"]);
    let alternatives = output_with_stdin(&mut alternatives, b"");
    assert!(!alternatives.status.success());
    assert!(alternatives.stdout.is_empty());
    assert!(
        String::from_utf8_lossy(&alternatives.stderr).contains("--io on requires --strategy any")
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_krun_io_off_feeds_standard_input_into_stdin() {
    // reference: printf 'ab\n' | k/result/bin/krun program.pgm --definition ref --io off
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/io");
    let expected = parse_pattern(&fs::read_to_string(fixtures.join("off.kore")).unwrap()).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command.args([
        "krun",
        fixtures.join("io.k").to_str().unwrap(),
        fixtures.join("program.pgm").to_str().unwrap(),
        "--main-module",
        "IO",
        "--sort",
        "Int",
        "--depth",
        "0",
        "--io",
        "off",
    ]);
    let output = output_with_stdin(&mut command, b"ab\n");

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap(),
        expected
    );
    assert!(
        !String::from_utf8_lossy(&output.stderr)
            .contains("reading standard input into $STDIN until end of file"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn reference_krun_io_off_reads_single_delimiters() {
    let (mut command, fixtures) = stdin_delimiter_run_command();
    let input = fs::read(fixtures.join("single.in")).unwrap();
    let output = output_with_stdin(&mut command, &input);

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stdout.contains(r#"\dv{SortString{}}("241")"#), "{stdout}");
    assert!(
        !stderr.contains("execution ended with no successor"),
        "{stderr}"
    );
}

#[test]
fn reference_krun_io_off_reports_undefined_delimiter_runs() {
    // Both inputs run on one compilation; `reference_krun_io_off_reads_single_delimiters` runs
    // the same command from source.
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/execution/stdin-delimiter-run");
    kcompile_for_krun(
        &fixtures.join("test.k"),
        &[
            "--main-module",
            "STDIN-DELIMITER-RUN",
            "--syntax-module",
            "STDIN-DELIMITER-RUN-SYNTAX",
            "-I",
            fixtures.to_str().unwrap(),
        ],
        &compiled,
    );
    for input in ["runs.in", "leading.in"] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command
            .args(["krun", "--definition"])
            .arg(&compiled)
            .arg(fixtures.join("three.pgm"))
            .args(["--sort", "Stmt", "--io", "off"]);
        let output = output_with_stdin(&mut command, &fs::read(fixtures.join(input)).unwrap());

        assert!(
            output.status.success(),
            "{input}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            "\\bottom{SortGeneratedTopCell{}}()\n"
        );
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(
            stderr.contains("rule STDIN-STREAM.stdinParseInt applied with an undefined result"),
            "{input}: {stderr}"
        );
        assert!(stderr.contains("refuted obligation"), "{input}: {stderr}");
        assert!(stderr.contains("String2Int"), "{input}: {stderr}");
        assert!(
            stderr.contains(r#"(\dv{SortString{}}(""))"#),
            "{input}: {stderr}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_krun_io_off_surface_pattern_reads_closed_stdin() {
    // reference: printf 'ab\n' | k/result/bin/krun program.pgm --definition ref --io off
    //   --depth 0 --pattern '<k> KK:K </k>' --output kore
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/io");
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command.args([
        "krun",
        fixtures.join("io.k").to_str().unwrap(),
        fixtures.join("program.pgm").to_str().unwrap(),
        "--main-module",
        "IO",
        "--sort",
        "Int",
        "--depth",
        "0",
        "--io",
        "off",
        "--pattern",
        "<k> KK:K </k>",
    ]);
    let output = output_with_stdin(&mut command, b"ab\n");

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let actual = parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap();
    let expected_binding =
        parse_pattern(r#"kseq{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("5")), dotk{}())"#)
            .unwrap();
    assert_eq!(
        pattern_binding(&actual, "VarKK"),
        Some(&expected_binding),
        "{actual:?}"
    );
    assert!(
        !String::from_utf8_lossy(&output.stderr)
            .contains("reading standard input into $STDIN until end of file"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Wait up to `watchdog` for `child` to exit while the caller holds its standard input open;
/// returns whether it exited.
fn exit_with_open_stdin(child: &mut std::process::Child, watchdog: std::time::Duration) -> bool {
    let deadline = std::time::Instant::now() + watchdog;
    while std::time::Instant::now() < deadline {
        if child.try_wait().unwrap().is_some() {
            return true;
        }
        std::thread::sleep(std::time::Duration::from_millis(20));
    }
    false
}

#[test]
fn krun_io_on_does_not_wait_for_standard_input_when_the_definition_cannot_read_the_console() {
    // The watchdog only bounds a failure: a run that waits for standard input to end never
    // exits while the pipe is open, however long the test waits.
    let watchdog = std::time::Duration::from_secs(300);
    let (root, _) = fixture();
    let output_only = root.join("output-only.k");
    fs::write(
        &output_only,
        r#"requires "domains.md"
module OUTPUT-ONLY
  imports K-IO
  imports INT
  imports STRING
  syntax State ::= "a" | "b"
  configuration <k> $PGM:State </k>
  rule <k> a => #write(1, "hi\n") ~> b ...</k>
endmodule
"#,
    )
    .unwrap();
    let rewrite = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/rewrite.k");
    // No console hook at all, and a console write without a console read: neither run's result
    // depends on standard input, so each finishes while its input is still open.
    for (definition, module, stdout) in [
        (rewrite.as_path(), "REWRITE", None),
        (output_only.as_path(), "OUTPUT-ONLY", Some(&b"hi\n"[..])),
    ] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.arg("krun").arg(definition).args([
            "--main-module",
            module,
            "--sort",
            "State",
            "--expression",
            "a",
        ]);
        if stdout.is_some() {
            command.args(["--output", "none"]);
        }
        let mut child = command
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let input = child.stdin.take().unwrap();
        let exited = exit_with_open_stdin(&mut child, watchdog);
        if !exited {
            child.kill().unwrap();
        }
        drop(input);
        let output = child.wait_with_output().unwrap();
        assert!(
            exited,
            "{module}: krun waited for standard input to end: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            output.status.success(),
            "{module}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        if let Some(stdout) = stdout {
            assert_eq!(output.stdout, stdout, "{module}");
        }
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_io_on_reads_standard_input_to_end_of_file_when_the_definition_can_read_the_console() {
    let (root, compiled) = compiled_live_io_fixture();
    let mut child = live_io_command(&compiled, "input")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let mut input = child.stdin.take().unwrap();
    input.write_all(b"A").unwrap();
    input.flush().unwrap();
    // The run's input is all of standard input, so it cannot finish before the input ends,
    // even though the byte its read takes has arrived.
    let exited = exit_with_open_stdin(&mut child, std::time::Duration::from_secs(2));
    drop(input);
    let output = child.wait_with_output().unwrap();
    assert!(!exited, "krun finished before its standard input ended");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, b"accepted");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_accepts_explicit_stdin_and_io_overrides() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/io");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("io.k").to_str().unwrap(),
            fixtures.join("program.pgm").to_str().unwrap(),
            "--main-module",
            "IO",
            "--sort",
            "Int",
            "--depth",
            "0",
            "-cIO=\"off\"",
            "-cSTDIN=\"x\"",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains(r#"\dv{SortString{}}("x")"#), "{stdout}");
    assert_eq!(stdout.matches(r#"\dv{SortString{}}("off")"#).count(), 2);
}

#[test]
fn krun_search_defaults_io_off() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/io");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("io.k").to_str().unwrap(),
            fixtures.join("program.pgm").to_str().unwrap(),
            "--main-module",
            "IO",
            "--sort",
            "Int",
            "--depth",
            "0",
            "--search-final",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains(r#"\dv{SortString{}}("off")"#), "{stdout}");
    assert!(!stdout.contains(r#"\dv{SortString{}}("on")"#), "{stdout}");
}

#[test]
fn krun_io_off_preserves_non_utf8_stdin_bytes() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/io");
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command.args([
        "krun",
        fixtures.join("io.k").to_str().unwrap(),
        fixtures.join("program.pgm").to_str().unwrap(),
        "--main-module",
        "IO",
        "--sort",
        "Int",
        "--depth",
        "0",
        "--io",
        "off",
    ]);
    let output = output_with_stdin(&mut command, &[b'x', 0x80]);

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8(output.stdout)
            .unwrap()
            .contains(r#"\dv{SortString{}}("x\x80\n")"#)
    );
}

/// Under `--io off` a definition's `$STDIN` is standard input read to end of file as text, with
/// its trailing newlines replaced by exactly one (`docs/compatibility.md`, "Backend scope"): the
/// buffer always ends in one newline, also when standard input is empty (`"\n"`) or does not end
/// in one (`"ab"` gives `"ab\n"`), and keeps no empty line after its last line (`"ab\n\n\n"`
/// gives `"ab\n"`).
/// Interior newlines, carriage returns and every other byte are kept as read. Search runs with
/// the console off, so `--search-final` buffers alike.
#[test]
fn krun_io_off_buffers_stdin_with_its_trailing_newlines_replaced_by_one() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/io");
    let cases: [(&[u8], &[&str], &str); 5] = [
        (b"", &["--io", "off"], r#"\dv{SortString{}}("\n")"#),
        (b"", &["--search-final"], r#"\dv{SortString{}}("\n")"#),
        (b"ab", &["--io", "off"], r#"\dv{SortString{}}("ab\n")"#),
        (
            b"ab\n\n\n",
            &["--io", "off"],
            r#"\dv{SortString{}}("ab\n")"#,
        ),
        (
            b"a\r\n\nb\n",
            &["--io", "off"],
            r#"\dv{SortString{}}("a\r\n\nb\n")"#,
        ),
    ];
    // Every case buffers its standard input into one compiled definition's `$STDIN`.
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    kcompile_for_krun(&fixtures.join("io.k"), &["--main-module", "IO"], &compiled);
    for (input, mode, expected) in cases {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command
            .args(["krun", "--definition"])
            .arg(&compiled)
            .arg(fixtures.join("program.pgm"))
            .args(["--sort", "Int", "--depth", "0"]);
        command.args(mode);
        let output = output_with_stdin(&mut command, input);

        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(
            stdout.contains(expected),
            "stdin {input:?} under {mode:?} must buffer {expected}:\n{stdout}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_warns_when_the_initial_configuration_is_bottom() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax KItem ::= fail(Int) [function, symbol(fail)]
  rule fail(_:Int) => #Bottom
  configuration <k> fail($PGM:Int) </k>
endmodule
"#,
    )
    .unwrap();
    // An execution and a search both start from no configuration.
    for mode in [&["--depth", "0"][..], &["--search-all"]] {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                definition.to_str().unwrap(),
                "--main-module",
                "MAIN",
                "--sort",
                "Int",
                "--expression",
                "1",
            ])
            .args(mode)
            .output()
            .unwrap();

        assert!(
            output.status.success(),
            "{mode:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            "\\bottom{SortGeneratedTopCell{}}()\n"
        );
        assert!(
            String::from_utf8_lossy(&output.stderr).contains(
                "warning: the initial configuration simplified to \\bottom before any rewrite step; check the configuration variables and the functions it applies"
            ),
            "{mode:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_reports_when_the_first_semantic_rewrite_is_bottom() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax KItem ::= fail(Int) [symbol(fail)]
  rule fail(_:Int) => #Bottom [label(fail)]
  configuration <k> fail($PGM:Int) </k>
endmodule
"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "Int",
            "--expression",
            "1",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "\\bottom{SortGeneratedTopCell{}}()\n"
    );
    assert!(
        !String::from_utf8_lossy(&output.stderr)
            .contains("the initial configuration simplified to \\bottom"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(
            "execution ended with no successor at depth 1: rule fail applied with an undefined result; refuted obligation"
        ),
        "{stderr}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// Compile `source` for execution, with `syntax_module` as its program grammar.
fn compiled_for_execution(
    root: &Path,
    name: &str,
    source: &str,
    main_module: &str,
    syntax_module: &str,
) -> PathBuf {
    let definition = root.join(format!("{name}.k"));
    fs::write(&definition, source).unwrap();
    let compiled = root.join(name);
    let preparation = watchdog::output(watchdog::Request::Compile {
        source: &definition,
        main_module,
        output: &compiled,
        kind: watchdog::Compilation::Run { syntax_module },
    });
    assert!(
        preparation.status.success(),
        "{name}: {}",
        String::from_utf8_lossy(&preparation.stderr)
    );
    compiled
}

/// `krun` of `expression` against a compiled definition, bounded by the backend watchdog.
fn bounded_krun(compiled: &Path, sort: &str, expression: &str, extra: &[&str]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command
        .arg("krun")
        .arg("--definition")
        .arg(compiled)
        .args(["--sort", sort, "--expression", expression, "--io", "off"])
        .args(extra);
    watchdog::backend(command)
}

/// Assert that `output` is a run that halted at `depth` because a rule could apply only by
/// replacing the named left-hand-side variables with minted existentials.
fn assert_halts_uninstantiated(output: &Output, depth: u64, variables: Option<&str>) {
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_eq!(output.stdout, b"", "{output:?}");
    assert!(
        stderr.contains(&format!(
            "error: in-process backend halted at depth {depth}: rule "
        )),
        "{stderr}"
    );
    let reason = match variables {
        Some(variables) => {
            format!(" leaves {variables} uninstantiated on a variable-free configuration")
        }
        None => " uninstantiated on a variable-free configuration".to_owned(),
    };
    assert!(stderr.contains(&reason), "{stderr}");
}

const WRITTEN_LAMBDAS: &str = r#"
module WRITTEN
  imports INT
  syntax Exp ::= Int
               | "pair" "(" Exp "," Exp ")" [symbol(pair)]
               | "swap" "(" Exp ")"         [symbol(swap)]
  syntax Exp ::= lam(Exp) [symbol(lam), function]
  configuration <k> $PGM:Exp </k>
  rule lam(pair(X, Y)) => pair(Y, X)
  rule swap(E) => lam(E)
endmodule
"#;

const OWISE_LAMBDA: &str = r#"
module OW
  imports INT
  syntax Exp ::= Int
               | "pair" "(" Exp "," Exp ")" [symbol(pair)]
               | "swapB" "(" Exp ")"        [symbol(swapB)]
  syntax Exp ::= lamB(Exp) [symbol(lamB), function]
               | h(Int)    [symbol(h), function]
  configuration <k> $PGM:Exp </k>
  rule lamB(pair(X, Y)) => pair(Y, X)
  rule lamB(_) => #Bottom [owise]
  rule h(0) => pair(1, 2)
  rule swapB(E) => lamB(E)
endmodule
"#;

#[test]
fn krun_halts_instead_of_narrowing_a_variable_free_configuration() {
    // A variable-free configuration denotes at most one state. A rule whose left-hand side meets
    // an application no equation evaluates (`lam(3)`, `lamB(h(1))`) could apply only by replacing
    // its variable `E`'s match with a minted existential, which restates the application's
    // unknown value as a fresh unknown and leaves it in the successor; the run ends as an
    // incomplete outcome instead of narrowing again at every step.
    let (root, _) = fixture();
    let written = compiled_for_execution(&root, "written", WRITTEN_LAMBDAS, "WRITTEN", "WRITTEN");
    let output = bounded_krun(&written, "Exp", "swap(3)", &[]);
    assert_halts_uninstantiated(&output, 1, Some("Rule-hVarE"));

    let owise = compiled_for_execution(&root, "owise", OWISE_LAMBDA, "OW", "OW");
    let output = bounded_krun(&owise, "Exp", "swapB(h(1))", &[]);
    assert_halts_uninstantiated(&output, 1, Some("Rule-hVarE"));

    // Applications an equation decides are unchanged: the owise equation makes `lamB(3)`
    // undefined, and `h(0)` evaluates to a pair.
    let output = bounded_krun(&owise, "Exp", "swapB(3)", &[]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "\\bottom{SortGeneratedTopCell{}}()\n"
    );
    let output = bounded_krun(&owise, "Exp", "swapB(h(0))", &[]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        r#"Lbl'-LT-'generatedTop'-GT-'{}(
  Lbl'-LT-'k'-GT-'{}(
    kseq{}(
      inj{SortExp{}, SortKItem{}}(
        Lblpair{}(
          inj{SortInt{}, SortExp{}}(\dv{SortInt{}}("2")),
          inj{SortInt{}, SortExp{}}(\dv{SortInt{}}("1"))
        )
      ),
      dotk{}()
    )
  ),
  Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0"))
)
"#
    );

    // Search reaches the same boundary and reports itself incomplete at the halted state.
    let output = bounded_krun(&owise, "Exp", "swapB(h(1))", &["--search-all"]);
    let printed = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.status.code(), Some(1), "{printed}");
    assert!(
        printed.contains("error: in-process backend search was incomplete: rule ")
            && printed.contains(
                " leaves Rule-hVarE uninstantiated on a variable-free configuration\nin the state at depth 1:"
            ),
        "{printed}"
    );
    assert!(
        printed.contains(r#"LbllamB{}(Lblh{}(\dv{SortInt{}}("1")))"#),
        "{printed}"
    );
    assert!(!printed.contains("Ex-"), "{printed}");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_halts_in_a_lower_priority_group_instead_of_narrowing_a_variable_free_configuration() {
    // The first rule applies only where the undecided `p(3)` holds, so the remainder of the
    // configuration reaches the owise rule, which could apply only by narrowing `lam(3)`
    // against `pair(A, _)`: the lower priority group halts as the first would.
    let (root, _) = fixture();
    let low = compiled_for_execution(
        &root,
        "low",
        r#"
module LOW
  imports INT
  imports BOOL
  syntax Exp ::= Int
               | "pair" "(" Exp "," Exp ")" [symbol(pair)]
               | go(Exp)                    [symbol(go)]
               | done(Exp)                  [symbol(done)]
  syntax Exp ::= lam(Exp) [symbol(lam), function]
  syntax Bool ::= p(Int)  [symbol(p), function]
  configuration <k> $PGM:Exp </k>
  rule lam(pair(X, Y)) => pair(Y, X)
  rule go(E) => done(E) requires p(3)
  rule go(pair(A, _)) => go(A) [owise]
endmodule
"#,
        "LOW",
        "LOW",
    );
    let output = bounded_krun(&low, "Exp", "go(lam(3))", &[]);
    assert_halts_uninstantiated(&output, 0, Some("Rule-hVar'Unds'Gen0, Rule-hVarA"));
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_halts_on_a_ground_application_whose_concrete_equation_is_set_aside() {
    // `p(0)` is ground but not a constructor term, so the `concrete` equation of `w` is set
    // aside on `w(p(0))`; its `requires` is undecided there, so the `owise` equation does not
    // apply and `w(p(0))` stays. The rule `h(X) => w(p(X))` could then apply only by narrowing
    // the kept application, so the variable-free run halts instead of answering `mk(0)`.
    let (root, _) = fixture();
    let anyreq = compiled_for_execution(
        &root,
        "anyreq",
        r#"
module ANYREQ
  imports INT
  syntax W ::= w(Int) [symbol(w)] | mk(Int) [symbol(mk)] | h(Int) [symbol(h)]
  syntax Int ::= p(Int) [function, symbol(p)]
  configuration <k> $PGM:W </k>
  rule w(X) => mk(1) requires X >Int 10 [anywhere, concrete]
  rule w(_) => mk(0) [anywhere, owise]
  rule p(X) => X requires X >Int 0
  rule h(X) => w(p(X))
endmodule
"#,
        "ANYREQ",
        "ANYREQ",
    );
    let output = bounded_krun(&anyreq, "W", "w(p(0))", &[]);
    assert_halts_uninstantiated(&output, 0, Some("Rule-hVarX"));
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_halts_instead_of_narrowing_a_variable_free_configuration_modulo_algebraic_axioms() {
    // `&` and `;` are unhooked associative productions, which the backend matches only by
    // identity: `1 & 2 & 3` is `(1 & 2) & 3`, which is not the term `sum(I:Int & B)` spells, so
    // the pair is left undecided and binds neither `I` nor `B`. Narrowing that pair restates the
    // configuration's own value as fresh unknowns at every step; the variable-free configuration
    // halts instead.
    let (root, _) = fixture();
    let bag = compiled_for_execution(
        &root,
        "bag",
        r#"
module BAG-RW-SYNTAX
  imports INT-SYNTAX
  syntax Bag ::= "nil" [symbol(bagNil)]
               | Int
               | Bag "&" Bag [left, assoc, comm, unit(bagNil), symbol(bagCat)]
  syntax Pgm ::= sum(Bag) [symbol(sum)]
endmodule

module BAG-RW
  imports BAG-RW-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k> <acc> 0 </acc>
  rule <k> sum(I:Int & B:Bag) => sum(B) ... </k> <acc> A => A +Int I </acc>
  rule <k> sum(I:Int) => .K ... </k> <acc> A => A +Int I </acc>
  rule <k> sum(nil) => .K ... </k>
endmodule
"#,
        "BAG-RW",
        "BAG-RW-SYNTAX",
    );
    let output = bounded_krun(&bag, "Pgm", "sum(1 & 2 & 3)", &[]);
    assert_halts_uninstantiated(&output, 0, Some("Rule-hVarB, Rule-hVarI"));

    let sequence = compiled_for_execution(
        &root,
        "sequence",
        r#"
module SEQ-ASSOC-SYNTAX
  imports INT-SYNTAX
  syntax Seq ::= Int
               | Seq ";" Seq [left, assoc, symbol(seqCat)]
  syntax Pgm ::= sum(Seq) [symbol(sum)]
endmodule

module SEQ-ASSOC
  imports SEQ-ASSOC-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k> <acc> 0 </acc>
  rule <k> sum(I:Int ; S:Seq) => sum(S) ... </k> <acc> A => A +Int I </acc>
  rule <k> sum(I:Int) => .K ... </k> <acc> A => A +Int I </acc>
endmodule
"#,
        "SEQ-ASSOC",
        "SEQ-ASSOC-SYNTAX",
    );
    let output = bounded_krun(&sequence, "Pgm", "sum(1 ; 2 ; 3)", &[]);
    assert_halts_uninstantiated(&output, 0, Some("Rule-hVarI, Rule-hVarS"));

    let owise = compiled_for_execution(
        &root,
        "owise",
        r#"
module P3-SYNTAX
  imports INT-SYNTAX
  syntax Bag ::= "nil" [symbol(bagNil)]
               | Int
               | Bag "&" Bag [left, assoc, comm, unit(bagNil), symbol(bagCat)]
  syntax Pgm ::= h(Bag) [symbol(h)] | "a" [symbol(a)] | "b" [symbol(b)]
endmodule

module P3
  imports P3-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k>
  rule <k> h(_:Int & _:Bag) => a </k>
  rule <k> h(_) => b </k> [owise]
endmodule
"#,
        "P3",
        "P3-SYNTAX",
    );
    for program in ["h(1 & 2)", "h(3)"] {
        let output = bounded_krun(&owise, "Pgm", program, &[]);
        assert_halts_uninstantiated(&output, 0, None);
    }

    // A rule whose left-hand side is ground mints nothing: its match against the configuration
    // is a condition of the configuration alone, kept on each branch.
    let ground = compiled_for_execution(
        &root,
        "ground",
        r#"
module ROWISE2-SYNTAX
  imports INT-SYNTAX
  syntax Bag ::= "nil" [symbol(bagNil)]
               | Int
               | Bag "&" Bag [left, assoc, comm, unit(bagNil), symbol(bagCat)]
  syntax Pgm ::= h(Bag) [symbol(h)] | g(Bag) [symbol(g)]
               | "a" [symbol(a)] | "b" [symbol(b)] | "done" [symbol(done)]
endmodule

module ROWISE2
  imports ROWISE2-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k>
  rule <k> h(1 & 2) => a </k>
  rule <k> h(_) => b </k> [owise]
  rule <k> g(1 & 2) => done </k>
endmodule
"#,
        "ROWISE2",
        "ROWISE2-SYNTAX",
    );
    let output = bounded_krun(&ground, "Pgm", "h(2 & 1)", &[]);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(output.status.success(), "{output:?}");
    assert!(
        stdout.starts_with("\\or{SortGeneratedTopCell{}}(")
            && stdout.contains("Lbla{}()")
            && stdout.contains("Lblb{}()")
            && !stdout.contains("Ex-"),
        "{stdout}"
    );
    let output = bounded_krun(&ground, "Pgm", "g(1 & 2)", &[]);
    assert!(output.status.success(), "{output:?}");
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("Lbldone{}()"),
        "{output:?}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// An unhooked bag operation with `assoc`, `comm` and `unit`, with programs that compare,
/// collect and look up two of its ground applications equal by `comm`, and a rule whose ground
/// pattern shares the constant `1` with its right-hand side.
const ALGEBRAIC_GROUND_TERMS: &str = r#"
module ALG
  imports INT
  imports BOOL
  imports SET
  imports MAP
  imports K-EQUAL
  syntax Bag ::= "nil" [symbol(bagNil)]
               | Int
               | Bag "&" Bag [left, assoc, comm, unit(bagNil), symbol(bagCat)]
  syntax Pgm ::= "eqk" [symbol(eqk)] | "setsize" [symbol(setsize)] | "mapsize" [symbol(mapsize)]
               | g(Bag) [symbol(g)]
  configuration <k> $PGM:Pgm </k> <out> .K </out>
  rule <k> eqk => .K </k> <out> _ => ((1 & 2) ==K (2 & 1)) </out>
  rule <k> setsize => .K </k> <out> _ => size(SetItem(1 & 2) SetItem(2 & 1)) </out>
  rule <k> mapsize => .K </k> <out> _ => size(((1 & 2) |-> 7) ((2 & 1) |-> 8)) </out>
  rule <k> g(1 & 2) => .K </k> <out> _ => 1 </out>
endmodule
"#;

/// The compact `\not(1 & 2 = 2 & 1)` a configuration carries where two ground `bagCat`
/// applications equal by `comm` must be distinct.
const NOT_BAG_SWAP_EQUAL: &str = r#"\not{SortGeneratedTopCell{}}(\equals{SortBag{},SortGeneratedTopCell{}}(LblbagCat{}(inj{SortInt{},SortBag{}}(\dv{SortInt{}}("1")),inj{SortInt{},SortBag{}}(\dv{SortInt{}}("2"))),LblbagCat{}(inj{SortInt{},SortBag{}}(\dv{SortInt{}}("2")),inj{SortInt{},SortBag{}}(\dv{SortInt{}}("1")))))"#;

/// The backend decides a pair rooted at an unhooked algebraic symbol only by identity, so two
/// ground applications equal by `comm` are not identified: `==K` stays unevaluated, and a set
/// or map holding both is built under the condition that they differ (the map then has two
/// entries).
#[test]
fn ground_terms_equal_by_unhooked_algebraic_axioms_are_not_identified() {
    let (root, _) = fixture();
    let compiled = compiled_for_execution(&root, "alg", ALGEBRAIC_GROUND_TERMS, "ALG", "ALG");
    let run = |program: &str| {
        let output = bounded_krun(&compiled, "Pgm", program, &[]);
        assert!(output.status.success(), "{program}: {output:?}");
        String::from_utf8(output.stdout)
            .unwrap()
            .split_whitespace()
            .collect::<String>()
    };
    let eqk = run("eqk");
    assert!(
        eqk.starts_with("Lbl'-LT-'generatedTop'-GT-'{}(")
            && eqk.contains("Lbl'UndsEqlsEqls'K'Unds'{}(")
            && !eqk.contains(r"\dv{SortBool{}}"),
        "{eqk}"
    );
    let set_size = run("setsize");
    assert!(
        set_size.starts_with(r"\and{SortGeneratedTopCell{}}(")
            && set_size.contains("Lblsize'LParUndsRParUnds'SET'Unds'Int'Unds'Set{}(")
            && set_size.ends_with(&format!("{NOT_BAG_SWAP_EQUAL})")),
        "{set_size}"
    );
    let map_size = run("mapsize");
    assert!(
        map_size.starts_with(r"\and{SortGeneratedTopCell{}}(")
            && map_size.contains(
                r#"Lbl'-LT-'out'-GT-'{}(kseq{}(inj{SortInt{},SortKItem{}}(\dv{SortInt{}}("2")),dotk{}()))"#
            )
            && map_size.ends_with(&format!("{NOT_BAG_SWAP_EQUAL})")),
        "{map_size}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// `minimize_term_construction` shares the constant `1`, which the rule's right-hand side
/// writes too, as `\and(1, _Gen)`, so the rule's pattern `g(1 & 2)` holds a variable below the
/// algebraic application: matched only by identity, it never binds it, and the variable-free
/// run halts instead of applying the rule to the term it spells.
#[test]
fn a_ground_algebraic_pattern_with_a_shared_constant_halts_a_variable_free_run() {
    let (root, _) = fixture();
    let compiled = compiled_for_execution(&root, "alg", ALGEBRAIC_GROUND_TERMS, "ALG", "ALG");
    let output = bounded_krun(&compiled, "Pgm", "g(1 & 2)", &[]);
    assert_halts_uninstantiated(&output, 0, None);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("leaves Rule-hVar'Unds'Gen"), "{stderr}");
    fs::remove_dir_all(root).unwrap();
}

/// Function equations over an unhooked bag operation, each beside an `owise` equation.
const ALGEBRAIC_EQUATIONS: &str = r#"
module ALG-EQ
  imports INT
  syntax Bag ::= "nil" [symbol(bagNil)]
               | Int
               | Bag "&" Bag [left, assoc, comm, unit(bagNil), symbol(bagCat)]
  syntax Int ::= f(Bag) [function, symbol(f)]
               | g(Bag) [function, symbol(g)]
               | k(Bag) [function, symbol(k)]
  configuration <k> $PGM:Int </k>
  rule f(1 & 2) => 5
  rule f(_) => 0 [owise]
  rule g(1 & 2) => 1
  rule g(_) => 0 [owise]
  rule k(I:Int & _:Bag) => I
  rule k(_) => 0 [owise]
endmodule
"#;

/// An equation whose argument pattern holds the algebraic symbol applies only where the
/// argument is the same term as the compiled pattern: `f(1 & 2)` is `5`, but `g(1 & 2) => 1`
/// shares `1` and the pattern `k(I:Int & _)` holds variables below the symbol, so neither
/// applies even to the term it spells. No argument of the sort is shown apart from the pattern,
/// so each `owise` equation is blocked on every other argument, `nil` and `3` included.
#[test]
fn a_function_equation_over_an_unhooked_algebraic_argument_applies_only_to_its_compiled_pattern() {
    let (root, _) = fixture();
    let compiled = compiled_for_execution(&root, "alg-eq", ALGEBRAIC_EQUATIONS, "ALG-EQ", "ALG-EQ");
    let run = |program: &str| {
        let output = bounded_krun(&compiled, "Int", program, &[]);
        assert!(output.status.success(), "{program}: {output:?}");
        String::from_utf8(output.stdout)
            .unwrap()
            .split_whitespace()
            .collect::<String>()
    };
    assert_eq!(
        run("f(1 & 2)"),
        unconstrained_final(r#"inj{SortInt{},SortKItem{}}(\dv{SortInt{}}("5"))"#)
    );
    for (program, head) in [
        ("f(2 & 1)", "Lblf{}("),
        ("f(3)", "Lblf{}("),
        ("g(1 & 2)", "Lblg{}("),
        ("k(1 & 2)", "Lblk{}("),
        ("k(nil)", "Lblk{}("),
        ("k(3)", "Lblk{}("),
    ] {
        let stdout = run(program);
        assert!(
            stdout.starts_with("Lbl'-LT-'generatedTop'-GT-'{}(")
                && stdout.contains(&format!("kseq{{}}(inj{{SortInt{{}},SortKItem{{}}}}({head}")),
            "{program}: {stdout}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

/// Rewrite rules over an unhooked bag operation, for the claims below.
const ALGEBRAIC_PROOF: &str = r#"
module GP
  imports INT
  syntax Bag ::= "nil" [symbol(bagNil)]
               | Int
               | Bag "&" Bag [left, assoc, comm, unit(bagNil), symbol(bagCat)]
  syntax Pgm ::= h(Bag) [symbol(h)] | "done" [symbol(done)]
  configuration <k> $PGM:Pgm </k>
  rule <k> h(_:Int & _:Bag) => done </k>
  rule <k> h(_) => done </k> [owise]
endmodule
"#;

/// Claims whose unwritten cells are frame variables.
const ALGEBRAIC_FRAMED_CLAIMS: &str = r#"
module GP-SPEC
  imports GP
  claim [pair]: <k> h(1 & 2) => done </k>
  claim [atom]: <k> h(3) => done </k>
endmodule
"#;

/// Claims that write every cell, so their configurations are variable-free.
const ALGEBRAIC_FULL_CLAIMS: &str = r#"
module GP-FULL-SPEC
  imports GP
  claim [atom]: <k> h(3) => done </k> <generatedCounter> 0 </generatedCounter>
  claim [pair]: <k> h(1 & 2) => done </k> <generatedCounter> 0 </generatedCounter>
endmodule
"#;

/// Claims over an unhooked bag operation that hold in every model by `comm` or `unit`.
const ALGEBRAIC_VALID_CLAIMS: &str = r#"
module P2
  imports INT
  syntax Bag ::= "nil" [symbol(bagNil)]
               | Int
               | Bag "&" Bag [left, assoc, comm, unit(bagNil), symbol(bagCat)]
  syntax Pgm ::= go(Bag) [symbol(go)] | done(Bag) [symbol(done)] | start(Bag) [symbol(start)]
               | "fin" [symbol(fin)] | single(Bag) [symbol(single)]
               | "isone" [symbol(isone)] | "notone" [symbol(notone)]
  configuration <k> $PGM:Pgm </k>
  rule <k> go(B) => done(B) </k>
  rule <k> start(2 & 1) => fin </k>
  rule <k> single(I:Int) => isone </k> requires I ==Int 1
  rule <k> single(I:Int) => notone </k> requires I =/=Int 1
endmodule

module P2-SPEC
  imports P2
  claim [swap]: <k> go(1 & 2) => done(2 & 1) </k>
  claim [start]: <k> start(1 & 2) => fin </k>
  claim [unit]: <k> single(1 & nil) => isone </k>
  claim [unit-left]: <k> go(nil & 3) => done(3) </k>
  claim [start-one-path]: <k> start(1 & 2) => fin </k> [one-path]
  claim [false]: <k> go(1 & 2) => done(3) </k>
endmodule
"#;

/// `kprove` of `module` in `source` (definition module `definition`): its exit status and the
/// verdict word of each named claim.
fn algebraic_verdicts(
    source: &str,
    module: &str,
    definition: &str,
    claims: &[&str],
) -> (bool, Vec<String>) {
    let (root, spec) = fixture();
    fs::write(&spec, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("kprove")
        .arg(&spec)
        .args(["--main-module", module, "--definition-module", definition])
        .args(["--depth", "10"])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    let verdicts = claims
        .iter()
        .map(|claim| {
            let prefix = format!("claim {module}.{claim}: ");
            stdout
                .lines()
                .find_map(|line| line.strip_prefix(&prefix))
                .unwrap_or_else(|| panic!("no {claim} verdict in {stdout}"))
                .split_whitespace()
                .next()
                .unwrap()
                .to_owned()
        })
        .collect();
    fs::remove_dir_all(root).unwrap();
    (output.status.success(), verdicts)
}

/// On the proof route an unsolved pair rooted at the algebraic symbol is a branch condition:
/// a claim that holds on every branch is proven, one that needs two terms identified or
/// separated by the axioms is `failed`, and none valid in every model is disproved. A claim
/// that writes every cell over a constructor-like configuration meets the instantiation halt
/// and is `indeterminate`; one holding an application of the symbol narrows and is proven.
#[test]
fn kprove_over_an_unhooked_algebraic_operation_never_disproves_a_claim_valid_in_every_model() {
    let framed = format!("{ALGEBRAIC_PROOF}{ALGEBRAIC_FRAMED_CLAIMS}");
    let (success, verdicts) = algebraic_verdicts(&framed, "GP-SPEC", "GP", &["pair", "atom"]);
    assert!(success);
    assert_eq!(verdicts, ["proven", "proven"]);
    let full = format!("{ALGEBRAIC_PROOF}{ALGEBRAIC_FULL_CLAIMS}");
    let (success, verdicts) = algebraic_verdicts(&full, "GP-FULL-SPEC", "GP", &["atom", "pair"]);
    assert!(!success);
    assert_eq!(verdicts, ["indeterminate", "proven"]);
    let claims = [
        "swap",
        "start",
        "unit",
        "unit-left",
        "start-one-path",
        "false",
    ];
    let (success, verdicts) = algebraic_verdicts(ALGEBRAIC_VALID_CLAIMS, "P2-SPEC", "P2", &claims);
    assert!(!success);
    assert_eq!(verdicts, ["failed"; 6]);
}

/// `#let P = E #in B` denotes B under the match of E against P, and nothing when E is no
/// instance of P. `swap` and `shift` bind a constructor pattern (`shift`'s body also reads the
/// enclosing rule's `N`), `scale` and `dup` a variable narrower than the bound expression's sort.
const REFUTED_LETS: &str = r#"
module LET
  imports INT
  syntax Exp ::= Int
               | "pair" "(" Exp "," Exp ")" [symbol(pair)]
               | "swap" "(" Exp ")"         [symbol(swap)]
               | "dup" "(" Exp ")"          [symbol(dup)]
               | "shift" "(" Exp "," Int ")" [symbol(shift)]
  syntax Int ::= "scale" "(" Exp ")" [symbol(scale), function]
  configuration <k> $PGM:Exp </k>
  rule scale(E) => ( #let M:Int = E #in M *Int 2 )
  rule swap(E)  => ( #let pair(X, Y) = E #in pair(Y, X) )
  rule dup(E)   => ( #let M:Int = E #in pair(M, M) )
  rule shift(E, N) => ( #let pair(X, _) = E #in pair(X, N) )
endmodule
"#;

/// The `<k>` cell holding exactly `item` (KORE of a `KItem`), as `krun` prints it.
fn k_cell_output(item: &str) -> String {
    format!(
        "Lbl'-LT-'generatedTop'-GT-'{{}}(\n  Lbl'-LT-'k'-GT-'{{}}(kseq{{}}({item}, dotk{{}}())),\n  \
         Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\"))\n)\n"
    )
}

/// Assert that `output` is a run that ended at `\bottom` because a rewrite step at `depth`
/// produced an undefined result.
fn assert_undefined_step(output: &Output, depth: u64) {
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "\\bottom{SortGeneratedTopCell{}}()\n",
        "{stderr}"
    );
    assert!(
        stderr.contains(&format!(
            "warning: execution ended with no successor at depth {depth}: rule "
        )) && stderr.contains(" applied with an undefined result"),
        "{stderr}"
    );
}

#[test]
fn krun_a_refuted_constructor_let_ends_undefined() {
    // `3` is no instance of `pair(X, Y)`, so `#let pair(X, Y) = 3 #in pair(Y, X)` denotes
    // nothing and the step that produces it has no successor; it is not an unknown value that
    // could still equal `swap(V)` for some `V` and be rewritten again.
    let (root, _) = fixture();
    let lets = compiled_for_execution(&root, "lets", REFUTED_LETS, "LET", "LET");
    let output = bounded_krun(&lets, "Exp", "swap(3)", &[]);
    assert_undefined_step(&output, 1);
    // Within two steps the refutation is decided, not narrowed or halted.
    let output = bounded_krun(&lets, "Exp", "swap(3)", &["--depth", "2"]);
    assert_undefined_step(&output, 1);
    // A body that reads the enclosing rule's variable is refuted the same way.
    let output = bounded_krun(&lets, "Exp", "shift(3, 5)", &[]);
    assert_undefined_step(&output, 1);

    // An instance of the pattern is unchanged.
    let output = bounded_krun(&lets, "Exp", "swap(pair(1, 2))", &[]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        r#"Lbl'-LT-'generatedTop'-GT-'{}(
  Lbl'-LT-'k'-GT-'{}(
    kseq{}(
      inj{SortExp{}, SortKItem{}}(
        Lblpair{}(
          inj{SortInt{}, SortExp{}}(\dv{SortInt{}}("2")),
          inj{SortInt{}, SortExp{}}(\dv{SortInt{}}("1"))
        )
      ),
      dotk{}()
    )
  ),
  Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0"))
)
"#
    );
    let output = bounded_krun(&lets, "Exp", "shift(pair(1, 2), 5)", &[]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        r#"Lbl'-LT-'generatedTop'-GT-'{}(
  Lbl'-LT-'k'-GT-'{}(
    kseq{}(
      inj{SortExp{}, SortKItem{}}(
        Lblpair{}(
          inj{SortInt{}, SortExp{}}(\dv{SortInt{}}("1")),
          inj{SortInt{}, SortExp{}}(\dv{SortInt{}}("5"))
        )
      ),
      dotk{}()
    )
  ),
  Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0"))
)
"#
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_a_refuted_variable_let_ends_undefined() {
    // `M:Int` matches only an `Int`, so binding it to `pair(1, 2)` denotes nothing, whether a
    // rewrite step (`dup`) or a function in the initial configuration (`scale`) applies it.
    let (root, _) = fixture();
    let lets = compiled_for_execution(&root, "lets", REFUTED_LETS, "LET", "LET");
    let output = bounded_krun(&lets, "Exp", "dup(pair(1, 2))", &[]);
    assert_undefined_step(&output, 1);

    let output = bounded_krun(&lets, "Exp", "scale(pair(1, 2))", &[]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "\\bottom{SortGeneratedTopCell{}}()\n"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(
            "warning: the initial configuration simplified to \\bottom before any rewrite step; \
             check the configuration variables and the functions it applies"
        ),
        "{output:?}"
    );

    let output = bounded_krun(&lets, "Exp", "dup(3)", &[]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        r#"Lbl'-LT-'generatedTop'-GT-'{}(
  Lbl'-LT-'k'-GT-'{}(
    kseq{}(
      inj{SortExp{}, SortKItem{}}(
        Lblpair{}(
          inj{SortInt{}, SortExp{}}(\dv{SortInt{}}("3")),
          inj{SortInt{}, SortExp{}}(\dv{SortInt{}}("3"))
        )
      ),
      dotk{}()
    )
  ),
  Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0"))
)
"#
    );
    let output = bounded_krun(&lets, "Exp", "scale(3)", &[]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        k_cell_output(r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("6"))"#)
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_a_refuted_let_in_an_untaken_if_operand_is_undefined() {
    // `#if` is a function of all three operands, so an undefined operand makes the conditional
    // undefined whichever branch the condition selects: `fst(3)` is undefined, although the
    // condition selects `0`. A `requires` guard (`fstR`) does not apply the refuted equation.
    let (root, _) = fixture();
    let guard = compiled_for_execution(
        &root,
        "guard",
        r#"
module GUARD
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= Int
               | "pair" "(" Exp "," Exp ")" [symbol(pair)]
               | "fst" "(" Exp ")"          [symbol(fst)]
               | "fstR" "(" Exp ")"         [symbol(fstR)]
  syntax Bool ::= isPair(Exp) [function, total, symbol(isPair)]
  rule isPair(pair(_, _)) => true
  rule isPair(_) => false [owise]
  syntax Exp ::= g(Exp) [function, symbol(g)]
  rule g(E) => #let pair(X, _) = E #in X requires isPair(E)
  rule g(_) => 0 [owise]
  configuration <k> $PGM:Exp </k>
  rule fst(E) => #if isPair(E) #then (#let pair(X, _) = E #in X) #else 0 #fi
  rule fstR(E) => g(E)
endmodule
"#,
        "GUARD",
        "GUARD",
    );
    let output = bounded_krun(&guard, "Exp", "fst(3)", &[]);
    assert_undefined_step(&output, 1);
    let output = bounded_krun(&guard, "Exp", "fst(pair(1, 2))", &[]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        k_cell_output(r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1"))"#)
    );
    let output = bounded_krun(&guard, "Exp", "fstR(3)", &[]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        k_cell_output(r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("0"))"#)
    );
    fs::remove_dir_all(root).unwrap();
}

/// `stdout` and every `expected` fragment without whitespace, so that a fragment matches across
/// the printer's line breaks.
fn squashed(text: &str) -> String {
    text.split_whitespace().collect()
}

/// Assert that `output` is a successful run with no simplification-budget warning whose final
/// `<k>` cell holds `item` and whose constraints contain every `obligation` (KORE, compared
/// without whitespace).
fn assert_value_under(output: &Output, item: &str, obligations: &[&str]) {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    assert!(!stderr.contains("simplification budget"), "{stderr}");
    let printed = squashed(&stdout);
    assert!(
        printed.contains(&squashed(&format!("kseq{{}}({item}, dotk{{}}())"))),
        "{stdout}"
    );
    for obligation in obligations {
        assert!(
            printed.contains(&squashed(obligation)),
            "{obligation}: {stdout}"
        );
    }
}

/// The `\ceil` of `subject`, a KORE term of `sort`, as a constraint of a final configuration.
fn ceil_of(sort: &str, subject: &str) -> String {
    format!("\\ceil{{{sort}{{}}, SortGeneratedTopCell{{}}}}({subject})")
}

/// Recursion whose base case `#if`, `orElseBool` or `andThenBool` selects.
const GUARDED_RECURSION: &str = r#"
module FACT
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= Int | Bool
               | "go" "(" Int ")" [symbol(go)]
               | "goOr" "(" Int ")" [symbol(goOr)]
               | "goAnd" "(" Int ")" [symbol(goAnd)]
               | "goReq" "(" Int ")" [symbol(goReq)]
  syntax Int ::= fact(Int) [symbol(fact), function]
               | factReq(Int) [symbol(factReq), function]
  syntax Bool ::= zeroDown(Int) [symbol(zeroDown), function]
                | allPos(Int) [symbol(allPos), function]
  rule fact(N) => #if N <=Int 0 #then 1 #else N *Int fact(N -Int 1) #fi
  rule factReq(N) => 1 requires N <=Int 0
  rule factReq(N) => N *Int factReq(N -Int 1) requires N >Int 0
  rule zeroDown(N) => N ==Int 0 orElseBool zeroDown(N -Int 1)
  rule allPos(N) => N <=Int 0 orElseBool (N >Int 0 andThenBool allPos(N -Int 1))
  configuration <k> $PGM:Exp </k>
  rule go(N) => fact(N)
  rule goReq(N) => factReq(N)
  rule goOr(N) => zeroDown(N)
  rule goAnd(N) => allPos(N)
endmodule
"#;

#[test]
fn recursion_guarded_by_a_conditional_ends_under_the_definedness_of_the_untaken_call() {
    // `#if`, `orElseBool` and `andThenBool` evaluate their deciding operand first and never
    // the operand it discards, so the recursion stops at its base case. Application is strict,
    // so the value keeps the discarded call's definedness as an obligation: `fact(3)` is `6`
    // under `\ceil(fact(-1))`, its exact denotation, since the axioms also admit a `fact` that is
    // `\bottom` everywhere. The `requires` form never builds the untaken call.
    let (root, _) = fixture();
    let fact = compiled_for_execution(&root, "fact", GUARDED_RECURSION, "FACT", "FACT");
    let int = |value: &str| {
        format!(r#"inj{{SortInt{{}}, SortKItem{{}}}}(\dv{{SortInt{{}}}}("{value}"))"#)
    };
    let truth = r#"inj{SortBool{}, SortKItem{}}(\dv{SortBool{}}("true"))"#;
    let minus_one = r#"(\dv{SortInt{}}("-1"))"#;
    let output = bounded_krun(&fact, "Exp", "go(3)", &["-w", "all"]);
    assert_value_under(
        &output,
        &int("6"),
        &[&ceil_of("SortInt", &format!("Lblfact{{}}{minus_one}"))],
    );
    let output = bounded_krun(&fact, "Exp", "goOr(2)", &["-w", "all"]);
    assert_value_under(
        &output,
        truth,
        &[&ceil_of("SortBool", &format!("LblzeroDown{{}}{minus_one}"))],
    );
    let output = bounded_krun(&fact, "Exp", "goAnd(2)", &["-w", "all"]);
    assert_value_under(
        &output,
        truth,
        &[&ceil_of("SortBool", &format!("LblallPos{{}}{minus_one}"))],
    );
    let output = bounded_krun(&fact, "Exp", "goReq(3)", &["-w", "all"]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        k_cell_output(&int("6"))
    );
    fs::remove_dir_all(root).unwrap();
}

/// Discarded operands whose evaluation does not end, directly or through the definedness of
/// an enclosing partial application: a ceil equation's condition (`/Int`, `%Int`) and a map's
/// key distinctness.
const DISCARDED_DIVERGENCE: &str = r#"
module LEAK
  imports INT
  imports BOOL
  imports MAP
  imports K-EQUAL
  syntax Exp ::= Int | Bool
               | "iteLoop" "(" ")"     [symbol(iteLoop)]
               | "andThenLoop" "(" ")" [symbol(andThenLoop)]
               | "divLoop" "(" ")"     [symbol(divLoop)]
               | "modLoop" "(" ")"     [symbol(modLoop)]
               | "mapLoop" "(" ")"     [symbol(mapLoop)]
  syntax Int ::= loopi() [function, symbol(loopi)]
  syntax Bool ::= loopb() [function, symbol(loopb)]
  rule loopi() => loopi() +Int 1
  rule loopb() => notBool loopb()
  configuration <k> $PGM:Exp </k>
  rule iteLoop() => #if true #then 1 #else loopi() #fi
  rule andThenLoop() => false andThenBool loopb()
  rule divLoop() => #if true #then 1 #else 1 /Int loopi() #fi
  rule modLoop() => #if true #then 1 #else 1 %Int loopi() #fi
  rule mapLoop() => #if true #then 1 #else size(loopi() |-> 1 2 |-> 2) #fi
endmodule
"#;

#[test]
fn a_discarded_diverging_operand_is_not_evaluated() {
    // No equation of the definition is applied to a discarded operand, its definedness
    // conditions included: each run ends at once under the open obligations, where evaluating
    // `loopi()` or `loopb()` would not end.
    let (root, _) = fixture();
    let leak = compiled_for_execution(&root, "leak", DISCARDED_DIVERGENCE, "LEAK", "LEAK");
    let one = r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1"))"#;
    let loopi = ceil_of("SortInt", "Lblloopi{}()");
    let output = bounded_krun(&leak, "Exp", "iteLoop()", &["-w", "all"]);
    assert_value_under(&output, one, &[&loopi]);
    let output = bounded_krun(&leak, "Exp", "andThenLoop()", &["-w", "all"]);
    assert_value_under(
        &output,
        r#"inj{SortBool{}, SortKItem{}}(\dv{SortBool{}}("false"))"#,
        &[&ceil_of("SortBool", "Lblloopb{}()")],
    );
    for (expression, label) in [
        ("divLoop()", "Lbl'UndsSlsh'Int'Unds'"),
        ("modLoop()", "Lbl'UndsPerc'Int'Unds'"),
    ] {
        let output = bounded_krun(&leak, "Exp", expression, &["-w", "all"]);
        assert_value_under(
            &output,
            one,
            &[
                &ceil_of(
                    "SortInt",
                    &format!(r#"{label}{{}}(\dv{{SortInt{{}}}}("1"), Lblloopi{{}}())"#),
                ),
                &loopi,
            ],
        );
    }
    let output = bounded_krun(&leak, "Exp", "mapLoop()", &["-w", "all"]);
    assert_value_under(
        &output,
        one,
        &["\\ceil{SortMap{}, SortGeneratedTopCell{}}(", &loopi],
    );
    fs::remove_dir_all(root).unwrap();
}

/// Discarded operands builtin hooks decide on literals, or do not.
const DISCARDED_GROUND: &str = r#"
module GROUND
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= Int | Bool
               | "divz" "(" ")" [symbol(divz)]
               | "fdivz" "(" ")" [symbol(fdivz)]
               | "fdivok" "(" ")" [symbol(fdivok)]
               | "gdivz" "(" ")" [symbol(gdivz)]
               | "andDivz" "(" ")" [symbol(andDivz)]
               | "reqIte" "(" Int ")" [symbol(reqIte)]
               | "ok" [symbol(ok)]
  syntax Int ::= f(Int) [symbol(f), function]
               | g(Int) [symbol(g), function]
  rule f(N) => N +Int 1
  rule g(N) => f(N)
  configuration <k> $PGM:Exp </k>
  rule divz() => #if true #then 1 #else 1 /Int 0 #fi
  rule fdivz() => #if true #then 1 #else 1 /Int f(-1) #fi
  rule fdivok() => #if true #then 1 #else 1 /Int f(1) #fi
  rule gdivz() => #if true #then 1 #else 1 /Int g(-1) #fi
  rule andDivz() => false andThenBool (1 /Int 0 >Int 0)
  rule reqIte(N) => ok requires #if N >Int 0 #then true #else 1 /Int 0 >Int 0 #fi
endmodule
"#;

#[test]
fn a_discarded_operand_hooks_show_undefined_is_bottom() {
    // Builtin hooks fold a discarded operand on literals, and `1 /Int 0` folds to `\bottom`: the
    // conditional is `\bottom`, and the refuted obligation is the hook's.
    let (root, _) = fixture();
    let ground = compiled_for_execution(&root, "ground", DISCARDED_GROUND, "GROUND", "GROUND");
    for expression in ["divz()", "andDivz()"] {
        let output = bounded_krun(&ground, "Exp", expression, &[]);
        assert_undefined_step(&output, 1);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(r#"refuted obligation \ceil{SortInt{}, SortGeneratedTopCell{}}(Lbl'UndsSlsh'Int'Unds'{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("0")))"#),
            "{expression}: {stderr}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn a_discarded_operand_takes_the_value_of_one_ground_equation_step() {
    // `f(-1) = -1 +Int 1` is one equation step on a literal argument whose right-hand side
    // builtin hooks fold to `0`, so the discarded `1 /Int f(-1)` is `1 /Int 0`, undefined, and
    // `fdivz()` is `\bottom`; with `f(1)` the operand is defined and `fdivok()` is a bare `1`.
    // `g(-1) = f(-1)` would need a second step, which a discarded operand never gets: `gdivz()` is
    // `1` under the open `\ceil(1 /Int g(-1))`.
    let (root, _) = fixture();
    let ground = compiled_for_execution(&root, "ground", DISCARDED_GROUND, "GROUND", "GROUND");
    let output = bounded_krun(&ground, "Exp", "fdivz()", &[]);
    assert_undefined_step(&output, 1);
    let output = bounded_krun(&ground, "Exp", "fdivok()", &["-w", "all"]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        squashed(&String::from_utf8_lossy(&output.stdout)),
        squashed(&k_cell_output(
            r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1"))"#
        ))
    );
    let output = bounded_krun(&ground, "Exp", "gdivz()", &["-w", "all"]);
    let quotient = r#"Lbl'UndsSlsh'Int'Unds'{}(\dv{SortInt{}}("1"), Lblg{}(\dv{SortInt{}}("-1")))"#;
    assert_value_under(
        &output,
        r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1"))"#,
        &[&ceil_of("SortInt", quotient)],
    );
    fs::remove_dir_all(root).unwrap();
}

/// A conditional and each Boolean connective with a decided deciding operand, whose unused
/// operand applies a partial function without equations.
const UNTAKEN_OPERANDS: &str = r#"
module SHORTCIRCUIT
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= Int | Bool
               | "ite" "(" ")" [symbol(goIte)]
               | "iteFalse" "(" ")" [symbol(goIteFalse)]
               | "andThen" "(" ")" [symbol(goAndThen)]
               | "andB" "(" ")" [symbol(goAnd)]
               | "orElse" "(" ")" [symbol(goOrElse)]
               | "orB" "(" ")" [symbol(goOr)]
               | "implies" "(" ")" [symbol(goImplies)]
  syntax Int ::= "undef" "(" ")" [symbol(undef), function]
  syntax Bool ::= "undefb" "(" ")" [symbol(undefb), function]
  configuration <k> $PGM:Exp </k>
  rule ite() => #if true #then 1 #else undef() #fi
  rule iteFalse() => #if false #then undef() #else 2 #fi
  rule andThen() => false andThenBool undefb()
  rule andB() => false andBool undefb()
  rule orElse() => true orElseBool undefb()
  rule orB() => true orBool undefb()
  rule implies() => false impliesBool undefb()
endmodule
"#;

#[test]
fn krun_keeps_the_definedness_of_an_untaken_conditional_branch() {
    // `#if` and the Boolean connectives are applications of hooked symbols, undefined wherever
    // an operand is: each run prints the value its deciding operand gives under the `\ceil` of
    // the operand the value does not depend on, and nothing else.
    let (root, _) = fixture();
    let operands = compiled_for_execution(
        &root,
        "operands",
        UNTAKEN_OPERANDS,
        "SHORTCIRCUIT",
        "SHORTCIRCUIT",
    );
    let under = |item: &str, sort: &str, subject: &str| {
        format!(
            "\\and{{SortGeneratedTopCell{{}}}}({}, {})",
            k_cell_output(item).trim_end(),
            ceil_of(sort, subject)
        )
    };
    let int = |value: &str| {
        format!(r#"inj{{SortInt{{}}, SortKItem{{}}}}(\dv{{SortInt{{}}}}("{value}"))"#)
    };
    let bool = |value: &str| {
        format!(r#"inj{{SortBool{{}}, SortKItem{{}}}}(\dv{{SortBool{{}}}}("{value}"))"#)
    };
    for (expression, expected) in [
        ("ite()", under(&int("1"), "SortInt", "Lblundef{}()")),
        ("iteFalse()", under(&int("2"), "SortInt", "Lblundef{}()")),
        (
            "andThen()",
            under(&bool("false"), "SortBool", "Lblundefb{}()"),
        ),
        ("andB()", under(&bool("false"), "SortBool", "Lblundefb{}()")),
        (
            "orElse()",
            under(&bool("true"), "SortBool", "Lblundefb{}()"),
        ),
        ("orB()", under(&bool("true"), "SortBool", "Lblundefb{}()")),
        (
            "implies()",
            under(&bool("true"), "SortBool", "Lblundefb{}()"),
        ),
    ] {
        let output = bounded_krun(&operands, "Exp", expression, &["-w", "all"]);
        assert!(output.status.success(), "{expression}: {output:?}");
        assert_eq!(
            squashed(&String::from_utf8_lossy(&output.stdout)),
            squashed(&expected),
            "{expression}"
        );
    }

    // An unused operand that builtin hooks show undefined makes the value `\bottom`, and in a
    // `requires` the rule does not apply.
    let ground = compiled_for_execution(&root, "ground", DISCARDED_GROUND, "GROUND", "GROUND");
    let output = bounded_krun(&ground, "Exp", "divz()", &[]);
    assert_undefined_step(&output, 1);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(r#"refuted obligation \ceil{SortInt{}, SortGeneratedTopCell{}}(Lbl'UndsSlsh'Int'Unds'{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("0")))"#),
        "{stderr}"
    );
    let output = bounded_krun(&ground, "Exp", "reqIte(1)", &[]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        squashed(&String::from_utf8_lossy(&output.stdout)),
        squashed(&k_cell_output(
            r#"inj{SortExp{}, SortKItem{}}(LblreqIte{}(\dv{SortInt{}}("1")))"#
        )),
    );

    // Control: the obligation is the operand's own. With an equation that defines `undef()`, the
    // same conditional is a bare `1`.
    let defined = UNTAKEN_OPERANDS.replace(
        "  configuration <k> $PGM:Exp </k>",
        "  rule undef() => 0\n  configuration <k> $PGM:Exp </k>",
    );
    assert_ne!(defined, UNTAKEN_OPERANDS);
    let defined =
        compiled_for_execution(&root, "defined", &defined, "SHORTCIRCUIT", "SHORTCIRCUIT");
    let output = bounded_krun(&defined, "Exp", "ite()", &["-w", "all"]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        squashed(&String::from_utf8_lossy(&output.stdout)),
        squashed(&k_cell_output(&int("1"))),
    );
    fs::remove_dir_all(root).unwrap();
}

/// A conditional with a symbolic condition that a rule's left-hand side meets.
const SYMBOLIC_CONDITIONAL: &str = r#"
module SPLIT
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= start(Int) [symbol(start)] | mid(Int) [symbol(mid)] | one() [symbol(one)]
  syntax Int ::= undef() [function, symbol(undef)]
  configuration <k> $PGM:Exp </k>
  rule <k> start(N) => mid(#if N >Int 0 #then 1 #else undef() #fi) ...</k>
  rule <k> mid(1) => one() ...</k>
endmodule
"#;

#[test]
fn a_symbolic_conditional_splits_on_its_condition_under_the_unused_operands_definedness() {
    // `mid(#if N >Int 0 #then 1 #else undef() #fi)` meets `mid(1)`: where `N >Int 0` the
    // conditional is `1` only where `undef()` is defined, and where it does not hold the
    // conditional is `undef()`, which is `1` where the two are equal. The rest stays at `mid`.
    let (root, _) = fixture();
    let split = compiled_for_execution(&root, "split", SYMBOLIC_CONDITIONAL, "SPLIT", "SPLIT");
    let pattern = top_with("inj{SortExp{}, SortKItem{}}(Lblstart{}(VarN:SortInt{}))");
    let output = kore_exec_from(&root, &split, "SPLIT", &pattern, 3);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    let positive = r#"Lbl'Unds-GT-'Int'Unds'{}(VarN:SortInt{}, \dv{SortInt{}}("0"))"#;
    let holds = format!(
        r#"\equals{{SortBool{{}}, SortGeneratedTopCell{{}}}}(\dv{{SortBool{{}}}}("true"), {positive})"#
    );
    let fails = format!("\\not{{SortGeneratedTopCell{{}}}}({holds})");
    let equal = r#"\equals{SortInt{}, SortGeneratedTopCell{}}(\dv{SortInt{}}("1"), Lblundef{}())"#;
    let unequal = format!("\\not{{SortGeneratedTopCell{{}}}}({equal})");
    let defined = ceil_of("SortInt", "Lblundef{}()");
    let conditional =
        format!(r#"Lblite{{SortInt{{}}}}({positive}, \dv{{SortInt{{}}}}("1"), Lblundef{{}}())"#);
    let state = |item: &str, conditions: &[&str]| {
        format!(
            "\\and{{SortGeneratedTopCell{{}}}}({}, \\and{{SortGeneratedTopCell{{}}}}({}))",
            top_with(&format!("inj{{SortExp{{}}, SortKItem{{}}}}({item})")),
            conditions.join(", ")
        )
    };
    let expected = format!(
        "\\or{{SortGeneratedTopCell{{}}}}({}, {}, {})",
        state(&format!("Lblmid{{}}({conditional})"), &[&fails, &unequal]),
        state("Lblone{}()", &[&defined, &fails, equal]),
        state("Lblone{}()", &[&defined, &holds]),
    );
    assert_eq!(squashed(&stdout), squashed(&expected), "{stdout}");
    fs::remove_dir_all(root).unwrap();
}

/// A console write in the operand that the other operand of a Boolean connective makes
/// irrelevant to its value.
const CONNECTIVE_EFFECTS: &str = r#"
requires "domains.md"
module EFF-SYNTAX
  imports INT-SYNTAX
  syntax Stmt ::= "ab" | "ob" | "ib" | "at" | "oe"
endmodule
module EFF
  imports EFF-SYNTAX
  imports K-IO
  imports INT
  imports BOOL
  imports STRING
  imports K-EQUAL
  syntax Stmt ::= fin(Bool) [symbol(fin)]
  configuration <k> $PGM:Stmt </k>
  rule <k> ab => fin(false andBool (#putc(1, 65) ==K .K)) ...</k>
  rule <k> ob => fin(true orBool (#putc(1, 66) ==K .K)) ...</k>
  rule <k> ib => fin(false impliesBool (#putc(1, 67) ==K .K)) ...</k>
  rule <k> at => fin(false andThenBool (#putc(1, 68) ==K .K)) ...</k>
  rule <k> oe => fin(true orElseBool (#putc(1, 69) ==K .K)) ...</k>
endmodule
"#;

#[test]
fn the_strict_connectives_perform_the_effects_of_both_operands() {
    // `andBool`, `orBool` and `impliesBool` simplify both operands, so the write in the operand
    // that does not change the value is performed; `andThenBool` and `orElseBool` discard that
    // operand without performing it.
    let (root, _) = fixture();
    let effects = compiled_for_execution(&root, "effects", CONNECTIVE_EFFECTS, "EFF", "EFF-SYNTAX");
    for (expression, written) in [
        ("ab", &b"A"[..]),
        ("ob", b"B"),
        ("ib", b"C"),
        ("at", b""),
        ("oe", b""),
    ] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args([
            "krun",
            "--definition",
            effects.to_str().unwrap(),
            "--sort",
            "Stmt",
            "--expression",
            expression,
            "--io",
            "on",
            "--output",
            "none",
        ]);
        let output = output_with_stdin(&mut command, b"");
        assert!(output.status.success(), "{expression}: {output:?}");
        assert_eq!(output.stdout, written, "{expression}");
    }
    fs::remove_dir_all(root).unwrap();
}

/// Conditionals that discard a builtin hook application over a ground collection.
const DISCARDED_COLLECTION_HOOKS: &str = r#"
module GROUNDHOOK
  imports INT
  imports BOOL
  imports MAP
  imports LIST
  imports K-EQUAL
  syntax Exp ::= Int
               | "lookBad" "(" ")" [symbol(lookBad)]
               | "lookOk" "(" ")" [symbol(lookOk)]
               | "projBad" "(" ")" [symbol(projBad)]
               | "projOk" "(" ")" [symbol(projOk)]
               | "listed" "(" ")" [symbol(listed)]
               | "viaFun" "(" ")" [symbol(viaFun)]
               | lookSym(Map) [symbol(lookSym)]
  syntax Int ::= pick(Map) [function, symbol(pick)]
  rule pick(M) => {M[5]}:>Int
  configuration <k> $PGM:Exp </k>
  rule <k> lookBad() => #if true #then 7 #else (1 |-> 2)[5] #fi ...</k>
  rule <k> lookOk() => #if true #then 7 #else (1 |-> 2)[1] #fi ...</k>
  rule <k> projBad() => #if true #then 7 #else {(1 |-> 2)[5]}:>Int #fi ...</k>
  rule <k> projOk() => #if true #then 7 #else {(1 |-> 2)[1]}:>Int #fi ...</k>
  rule <k> listed() => #if true #then 7 #else size(keys_list(3 |-> 30 1 |-> 10)) #fi ...</k>
  rule <k> viaFun() => #if true #then 7 #else pick(1 |-> 2) #fi ...</k>
  rule <k> lookSym(M) => #if true #then 7 #else {M[1]}:>Int #fi ...</k>
endmodule
"#;

#[test]
fn a_discarded_hook_over_a_ground_collection_is_decided_by_the_hook() {
    // A builtin hook on ground constructor-like arguments applies no equation of the definition,
    // so it is one of the steps that decide a discarded operand's obligation: a lookup of a key
    // the map binds, and a listing of its keys, are defined and the conditional is a bare `7`;
    // a lookup of a key it does not bind is undefined, so the conditional is `\bottom`.
    let (root, _) = fixture();
    let hooks = compiled_for_execution(
        &root,
        "groundhook",
        DISCARDED_COLLECTION_HOOKS,
        "GROUNDHOOK",
        "GROUNDHOOK",
    );
    let seven = r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("7"))"#;
    for expression in ["lookOk()", "projOk()", "listed()"] {
        let output = bounded_krun(&hooks, "Exp", expression, &["-w", "all"]);
        assert!(output.status.success(), "{expression}: {output:?}");
        assert_eq!(
            squashed(&String::from_utf8_lossy(&output.stdout)),
            squashed(&k_cell_output(seven)),
            "{expression}"
        );
    }
    let lookup = r#"LblMap'Coln'lookup{}(Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1")), inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("2"))), inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("5")))"#;
    for expression in ["lookBad()", "projBad()"] {
        let output = bounded_krun(&hooks, "Exp", expression, &[]);
        assert_undefined_step(&output, 1);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            squashed(&stderr).contains(&squashed(&format!(
                "refuted obligation {}",
                ceil_of("SortKItem", lookup)
            ))),
            "{expression}: {stderr}"
        );
    }

    // A user function applied to the collection is not a hook: no equation of `pick` is applied
    // (its argument is no literal, so it takes no one-step value either), and the obligation
    // stays open although evaluating `pick(1 |-> 2)` would show it undefined.
    let output = bounded_krun(&hooks, "Exp", "viaFun()", &["-w", "all"]);
    let picked = r#"Lblpick{}(Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1")), inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("2"))))"#;
    assert_value_under(&output, seven, &[&ceil_of("SortInt", picked)]);

    // A hook over a map that is a variable has no value to give: the obligation stays open.
    let pattern = top_with("inj{SortExp{}, SortKItem{}}(LbllookSym{}(VarM:SortMap{}))");
    let output = kore_exec_from(&root, &hooks, "GROUNDHOOK", &pattern, 2);
    let symbolic =
        r#"LblMap'Coln'lookup{}(VarM:SortMap{}, inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1")))"#;
    assert_value_under(
        &output,
        seven,
        &[&format!(
            "\\ceil{{SortInt{{}}, SortGeneratedTopCell{{}}}}(Lblproject'Coln'Int{{}}(kseq{{}}({symbolic}, dotk{{}}())))"
        )],
    );
    fs::remove_dir_all(root).unwrap();
}

/// Conditionals that discard a `choice` over a ground map.
const DISCARDED_CHOICE: &str = r#"
module CHOICEHOOK
  imports INT
  imports BOOL
  imports MAP
  imports K-EQUAL
  syntax Exp ::= Int
               | "pickTwo" "(" ")" [symbol(pickTwo)]
               | "pickOne" "(" ")" [symbol(pickOne)]
               | "pickNone" "(" ")" [symbol(pickNone)]
  configuration <k> $PGM:Exp </k>
  rule <k> pickTwo() => #if true #then 7 #else {choice(3 |-> 30 1 |-> 10)}:>Int #fi ...</k>
  rule <k> pickOne() => #if true #then 7 #else {choice(3 |-> 30)}:>Int #fi ...</k>
  rule <k> pickNone() => #if true #then 7 #else {choice(.Map)}:>Int #fi ...</k>
endmodule
"#;

#[test]
fn a_discarded_choice_over_a_ground_map_is_decided_by_the_hook() {
    // `choice` of a closed map of literal keys is one of its keys, which an execution chooses
    // without an equation: the discarded operand is defined and the conditional is a bare `7`.
    // The empty map has no key, so `choice(.Map)` is undefined and the conditional is `\bottom`.
    let (root, _) = fixture();
    let choice = compiled_for_execution(
        &root,
        "choice",
        DISCARDED_CHOICE,
        "CHOICEHOOK",
        "CHOICEHOOK",
    );
    for expression in ["pickTwo()", "pickOne()"] {
        let output = bounded_krun(&choice, "Exp", expression, &["-w", "all"]);
        assert!(output.status.success(), "{expression}: {output:?}");
        assert_eq!(
            squashed(&String::from_utf8_lossy(&output.stdout)),
            squashed(&k_cell_output(
                r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("7"))"#
            )),
            "{expression}"
        );
    }
    let output = bounded_krun(&choice, "Exp", "pickNone()", &[]);
    assert_undefined_step(&output, 1);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("refuted obligation"), "{stderr}");
    assert!(
        stderr.contains("LblMap'Coln'choice{}(Lbl'Stop'Map{}())"),
        "{stderr}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// A simplification lemma that reaches a conditional below its root.
const LEMMA_OVER_CONDITIONAL: &str = r#"
module LEMMA
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= start(Int) [symbol(start)] | done(Int) [symbol(done)]
  syntax Int ::= loopi() [function, symbol(loopi)]
  rule loopi() => loopi() +Int 1
  rule #if B #then X #else Y #fi +Int Z => #if B #then X +Int Z #else Y +Int Z #fi [simplification]
  configuration <k> $PGM:Exp </k>
  rule <k> start(N) => done(#if N >Int 0 #then 1 #else loopi() #fi +Int 1) ...</k>
endmodule
"#;

#[test]
fn a_lemma_binding_an_operand_below_its_root_does_not_evaluate_it() {
    // The lemma's match binds `Y` to `loopi()`, an operand the conditional never evaluates while
    // `N >Int 0` is undecided; the binding's definedness is a deferred obligation, so the run ends
    // at the rewritten conditional instead of evaluating `loopi()`.
    let (root, _) = fixture();
    let lemma = compiled_for_execution(&root, "lemma", LEMMA_OVER_CONDITIONAL, "LEMMA", "LEMMA");
    let pattern = top_with("inj{SortExp{}, SortKItem{}}(Lblstart{}(VarN:SortInt{}))");
    let output = kore_exec_from(&root, &lemma, "LEMMA", &pattern, 2);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    assert!(!stderr.contains("stack"), "{stderr}");
    assert!(
        squashed(&stdout).contains(&squashed(
            r#"Lbl'UndsPlus'Int'Unds'{}(Lblloopi{}(), \dv{SortInt{}}("1"))"#
        )),
        "{stdout}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// A lemma rooted at a conditional that splits a map inside the operand the conditional does not
/// evaluate, binding `M` to a map the match builds from the entries it leaves.
const LEMMA_SPLITTING_AN_OPERAND: &str = r#"
module RESTL
  imports INT
  imports BOOL
  imports MAP
  imports K-EQUAL
  syntax Exp ::= start(Int) [symbol(start)] | done(Int) [symbol(done)]
  syntax Int ::= loopi() [function, symbol(loopi)]
  rule loopi() => loopi() +Int 1
  rule #if B #then X:Int #else size((1 |-> _) M) #fi => #if B #then X #else 1 +Int size(M) #fi [simplification]
  configuration <k> $PGM:Exp </k>
  rule <k> start(N) => done(#if N >Int 0 #then 1 #else size(1 |-> 2 3 |-> loopi()) #fi) ...</k>
endmodule
"#;

/// A lemma rooted at a conditional that binds `V`, of a sort above the operand's, to the
/// operand's `loopi()` injected into that sort.
const LEMMA_INJECTING_AN_OPERAND: &str = r#"
module REINJ
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Val ::= Int | "nil"
  syntax Exp ::= start(Int) [symbol(start)] | done(Int) [symbol(done)]
  syntax Int ::= loopi() [function, symbol(loopi)] | unk(KItem) [function, symbol(unk)]
  rule loopi() => loopi() +Int 1
  rule #if B #then X:Int #else unk(V:Val) #fi => #if B #then X #else unk(V) +Int 7 #fi [simplification]
  configuration <k> $PGM:Exp </k>
  rule <k> start(N) => done(#if N >Int 0 #then 1 #else unk(loopi()) #fi) ...</k>
endmodule
"#;

#[test]
fn a_lemma_binding_a_term_it_builds_from_an_operand_does_not_evaluate_it() {
    // Neither binding is a subterm of the subject: `M` is the map of the entries the split
    // leaves, and `V` is `loopi()` under an injection the subject does not hold. Both are parts
    // of an operand the conditional does not evaluate while `N >Int 0` is undecided, so their
    // definedness is a deferred obligation and the run ends at the rewritten conditional instead
    // of evaluating `loopi()`.
    let (root, _) = fixture();
    let pattern = top_with("inj{SortExp{}, SortKItem{}}(Lblstart{}(VarN:SortInt{}))");
    for (name, source, module, rewritten) in [
        (
            "restl",
            LEMMA_SPLITTING_AN_OPERAND,
            "RESTL",
            r#"Lbl'UndsPlus'Int'Unds'{}(\dv{SortInt{}}("1"), LblsizeMap{}(Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("3")), inj{SortInt{}, SortKItem{}}(Lblloopi{}()))))"#,
        ),
        (
            "reinj",
            LEMMA_INJECTING_AN_OPERAND,
            "REINJ",
            r#"Lbl'UndsPlus'Int'Unds'{}(Lblunk{}(inj{SortInt{}, SortKItem{}}(Lblloopi{}())), \dv{SortInt{}}("7"))"#,
        ),
    ] {
        let compiled = compiled_for_execution(&root, name, source, module, module);
        let output = kore_exec_from(&root, &compiled, module, &pattern, 2);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{name}: {stdout}\n{stderr}");
        assert!(!stderr.contains("stack"), "{name}: {stderr}");
        assert!(
            squashed(&stdout).contains(&squashed(rewritten)),
            "{name}: {stdout}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

/// A predicate lemma over a conditional whose right-hand side drops the conditional's second
/// operand.
const PREDICATE_LEMMA_OVER_CONDITIONAL: &str = r#"
module PEQBIND
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= start(Int) [symbol(start)] | done(Int) [symbol(done)]
  syntax Int ::= loopi() [function, symbol(loopi)]
  rule loopi() => loopi() +Int 1
  rule {#if B #then X:Int #else Y:Int #fi #Equals Z:Int} => {true #Equals B} #And {X #Equals Z} [simplification]
  configuration <k> $PGM:Exp </k>
  rule <k> start(N) => done(N) ...</k>
endmodule
"#;

#[test]
fn a_predicate_lemma_binding_a_discarded_operand_does_not_evaluate_it() {
    // The state's constraint `{#if N >Int 0 #then 1 #else loopi() #fi #Equals 1}` is an instance
    // of the lemma, whose match binds `Y` to `loopi()`, an operand the conditional does not
    // evaluate while `N >Int 0` is undecided. The binding's definedness is a deferred
    // obligation, so the lemma applies under it and the run ends instead of evaluating
    // `loopi()`.
    let (root, _) = fixture();
    let lemma = compiled_for_execution(
        &root,
        "peqbind",
        PREDICATE_LEMMA_OVER_CONDITIONAL,
        "PEQBIND",
        "PEQBIND",
    );
    let positive = r#"Lbl'Unds-GT-'Int'Unds'{}(VarN:SortInt{}, \dv{SortInt{}}("0"))"#;
    let pattern = format!(
        r#"\and{{SortGeneratedTopCell{{}}}}({}, \equals{{SortInt{{}}, SortGeneratedTopCell{{}}}}(Lblite{{SortInt{{}}}}({positive}, \dv{{SortInt{{}}}}("1"), Lblloopi{{}}()), \dv{{SortInt{{}}}}("1")))"#,
        top_with("inj{SortExp{}, SortKItem{}}(Lblstart{}(VarN:SortInt{}))")
    );
    let output = kore_exec_from(&root, &lemma, "PEQBIND", &pattern, 1);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    assert!(!stderr.contains("stack"), "{stderr}");
    // The request's constraint is admitted with its definedness stated (`Admitted`): the
    // deferred obligation of `loopi()` is hoisted ahead of the equality, and it stays first.
    let expected = format!(
        r#"\and{{SortGeneratedTopCell{{}}}}({}, \and{{SortGeneratedTopCell{{}}}}({}, \equals{{SortBool{{}}, SortGeneratedTopCell{{}}}}(\dv{{SortBool{{}}}}("true"), {positive})))"#,
        top_with("inj{SortExp{}, SortKItem{}}(Lbldone{}(VarN:SortInt{}))"),
        ceil_of("SortInt", "Lblloopi{}()"),
    );
    assert_eq!(squashed(&stdout), squashed(&expected), "{stdout}");

    // `#Not` is not strict in its operand, so the lemma over the negated equality cannot be
    // used under the open obligation of `Y`: the constraint is kept, and `loopi()` is not
    // evaluated to decide the obligation either.
    let negated = PREDICATE_LEMMA_OVER_CONDITIONAL.replace(
        "rule {#if B #then X:Int #else Y:Int #fi #Equals Z:Int} => {true #Equals B} #And {X #Equals Z} [simplification]",
        "rule #Not({#if B #then X:Int #else Y:Int #fi #Equals Z:Int}) => {false #Equals B} [simplification]",
    );
    assert_ne!(negated, PREDICATE_LEMMA_OVER_CONDITIONAL);
    let lemma = compiled_for_execution(&root, "peqnot", &negated, "PEQBIND", "PEQBIND");
    let constraint = format!(
        r#"\not{{SortGeneratedTopCell{{}}}}(\equals{{SortInt{{}}, SortGeneratedTopCell{{}}}}(Lblite{{SortInt{{}}}}({positive}, \dv{{SortInt{{}}}}("1"), Lblloopi{{}}()), \dv{{SortInt{{}}}}("1")))"#
    );
    let pattern = format!(
        "\\and{{SortGeneratedTopCell{{}}}}({}, {constraint})",
        top_with("inj{SortExp{}, SortKItem{}}(Lblstart{}(VarN:SortInt{}))")
    );
    let output = kore_exec_from(&root, &lemma, "PEQBIND", &pattern, 1);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    assert!(!stderr.contains("stack"), "{stderr}");
    // The constraint is admitted with the deferred obligation of `loopi()` stated in place under
    // the negation (`Admitted`), an equivalent form the lemma does not match either.
    let guarded = format!(
        r#"\not{{SortGeneratedTopCell{{}}}}(\and{{SortGeneratedTopCell{{}}}}({}, \equals{{SortInt{{}}, SortGeneratedTopCell{{}}}}(Lblite{{SortInt{{}}}}({positive}, \dv{{SortInt{{}}}}("1"), Lblloopi{{}}()), \dv{{SortInt{{}}}}("1"))))"#,
        ceil_of("SortInt", "Lblloopi{}()"),
    );
    let expected = format!(
        "\\and{{SortGeneratedTopCell{{}}}}({}, {guarded})",
        top_with("inj{SortExp{}, SortKItem{}}(Lbldone{}(VarN:SortInt{}))")
    );
    assert_eq!(squashed(&stdout), squashed(&expected), "{stdout}");
    fs::remove_dir_all(root).unwrap();
}

/// A conditional whose discarded operand's definedness depends on a console read.
const IMPURE_OPERAND: &str = r#"
requires "domains.md"
module MARKER
  imports K-IO
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= a(Int) [symbol(a)] | b(Int) [symbol(b)]
  configuration <k> $PGM:Exp </k>
  rule <k> a(N) => b(N) </k>
endmodule
"#;

/// The antecedent `b(1) /\ \ceil({#getc(0)}:>Int)` and the consequent
/// `b(#if true #then 1 #else 1 /Int ({#getc(0)}:>Int -Int 81) #fi)`, false in a model where the
/// read is 81.
fn impure_implication() -> (String, String) {
    let getc = "Lblproject'Coln'Int{}(kseq{}(inj{SortIOInt{}, SortKItem{}}(Lbl'Hash'getc'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int{}(\\dv{SortInt{}}(\"0\"))), dotk{}()))";
    let antecedent = format!(
        "\\and{{SortGeneratedTopCell{{}}}}({}, \\ceil{{SortInt{{}}, SortGeneratedTopCell{{}}}}({getc}))",
        top_with("inj{SortExp{}, SortKItem{}}(Lblb{}(\\dv{SortInt{}}(\"1\")))")
    );
    let consequent = top_with(&format!(
        "inj{{SortExp{{}}, SortKItem{{}}}}(Lblb{{}}(Lblite{{SortInt{{}}}}(\\dv{{SortBool{{}}}}(\"true\"), \\dv{{SortInt{{}}}}(\"1\"), Lbl'UndsSlsh'Int'Unds'{{}}(\\dv{{SortInt{{}}}}(\"1\"), Lbl'Unds'-Int'Unds'{{}}({getc}, \\dv{{SortInt{{}}}}(\"81\"))))))"
    ));
    (antecedent, consequent)
}

#[test]
fn an_implication_through_an_impure_discarded_operand_is_never_valid() {
    // The consequent's discarded operand `1 /Int ({#getc(0)}:>Int -Int 81)` is defined only where
    // the read is not 81, and its definedness depends on the read, which is never performed: the
    // implication is not decided, by `kore-implies` or by RPC `implies`, whatever the antecedent
    // states about the read.
    let (root, _) = fixture();
    let compiled = compiled_for_execution(&root, "marker", IMPURE_OPERAND, "MARKER", "MARKER");
    let definition = compiled.join("definition.kore");
    let (antecedent, consequent) = impure_implication();
    let antecedent_path = root.join("antecedent.kore");
    let consequent_path = root.join("consequent.kore");
    fs::write(&antecedent_path, &antecedent).unwrap();
    fs::write(&consequent_path, &consequent).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-implies",
            definition.to_str().unwrap(),
            "--module",
            "MARKER",
            "--antecedent",
            antecedent_path.to_str().unwrap(),
            "--consequent",
            consequent_path.to_str().unwrap(),
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let verdict: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(verdict["status"], "unknown", "{verdict:#}");

    use std::{
        io::{BufRead, BufReader},
        net::TcpStream,
        time::Duration,
    };
    let mut server = KoreRpcServer(
        Command::new(env!("CARGO_BIN_EXE_krust"))
            .arg("kore-rpc")
            .arg(&definition)
            .args(["--module", "MARKER", "--server-port", "0"])
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap(),
    );
    let mut announcement = String::new();
    BufReader::new(server.0.stderr.take().unwrap())
        .read_line(&mut announcement)
        .unwrap();
    let address = announcement
        .strip_prefix("KORE JSON-RPC listening on ")
        .unwrap_or_else(|| panic!("no listening address in {announcement:?}"))
        .trim();
    let stream = TcpStream::connect(address).unwrap();
    stream
        .set_read_timeout(Some(Duration::from_secs(60)))
        .unwrap();
    let mut writer = stream.try_clone().unwrap();
    let mut reader = BufReader::new(stream);
    let encode = |text: &str| k_rust::kore::json::to_value(&parse_pattern(text).unwrap()).unwrap();
    let request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "implies",
        "params": { "antecedent": encode(&antecedent), "consequent": encode(&consequent) },
    });
    writeln!(writer, "{request}").unwrap();
    let mut response = String::new();
    reader.read_line(&mut response).unwrap();
    let response: serde_json::Value = serde_json::from_str(&response).unwrap();
    assert_ne!(response["result"]["status"], "valid", "{response:#}");
    assert_ne!(response["result"]["valid"], true, "{response:#}");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn a_requires_conditional_is_strict_in_its_unused_operand() {
    // A `requires` holds only where it is defined, and `#if` is strict in every operand: with
    // `1 /Int 0` in the unused operand the condition is `\bottom` and the rule does not apply.
    let (root, _) = fixture();
    let ground = compiled_for_execution(&root, "ground", DISCARDED_GROUND, "GROUND", "GROUND");
    for value in ["1", "0"] {
        let output = bounded_krun(&ground, "Exp", &format!("reqIte({value})"), &[]);
        assert!(output.status.success(), "{output:?}");
        assert_eq!(
            squashed(&String::from_utf8_lossy(&output.stdout)),
            squashed(&k_cell_output(&format!(
                r#"inj{{SortExp{{}}, SortKItem{{}}}}(LblreqIte{{}}(\dv{{SortInt{{}}}}("{value}")))"#
            ))),
        );
    }
    fs::remove_dir_all(root).unwrap();
}

/// A discarded application decided by one equation step selected by matching alone.
const ONE_STEP: &str = r#"
module ONE
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= Int
               | "pick" "(" ")" [symbol(pick)]
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(1) => 5
  configuration <k> $PGM:Exp </k>
  rule pick() => #if true #then 0 #else f(1) #fi
endmodule
"#;

#[test]
fn a_deferred_atom_is_decided_by_one_equation_step_without_evaluation() {
    // `f(1) => 5` is an instance of an axiom whose right-hand side is defined, so the discarded
    // `f(1)` is defined and `pick()` is a bare `0`. A generated lambda applied to a value its
    // pattern refutes is `\bottom` by its `owise` equation, which the refutation of the
    // higher equation by matching selects (`krun_a_refuted_let_in_an_untaken_if_operand_is_undefined`).
    let (root, _) = fixture();
    let one = compiled_for_execution(&root, "one", ONE_STEP, "ONE", "ONE");
    let output = bounded_krun(&one, "Exp", "pick()", &["-w", "all"]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        k_cell_output(r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("0"))"#)
    );
    fs::remove_dir_all(root).unwrap();
}

/// `#if` at sort `K` with a condition only the path decides, and an Int `#if` met by a later
/// rule's left-hand side.
const PATH_DECIDED: &str = r#"
module KITE
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= Int
               | "startI" "(" Int ")" [symbol(startI)]
               | "startD" "(" Int ")" [symbol(startD)]
               | "done" [symbol(done)]
               | "other" [symbol(other)]
  syntax K ::= loopk() [function, symbol(loopk)]
  syntax Int ::= loopi() [function, symbol(loopi)]
  rule loopk() => other ~> loopk()
  rule loopi() => loopi() +Int 1
  configuration <k> $PGM:Exp </k>
  rule <k> startI(X) => #if X >Int 0 #then (done ~> .K) #else loopk() #fi ...</k> requires X >Int 0
  rule <k> startD(X) => #if X >Int 0 #then 7 #else loopi() #fi ...</k> requires X >Int 0
  rule <k> 7 => done ...</k>
endmodule
"#;

/// `krust kore-exec` of `compiled` from the initial state `pattern` (KORE text) to `depth`.
fn kore_exec_from(root: &Path, compiled: &Path, module: &str, pattern: &str, depth: u64) -> Output {
    let initial = root.join(format!(
        "initial-{}.kore",
        NEXT_INITIAL.fetch_add(1, Ordering::Relaxed)
    ));
    fs::write(&initial, pattern).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command.args([
        "kore-exec",
        compiled.join("definition.kore").to_str().unwrap(),
        "--module",
        module,
        "--pattern",
        initial.to_str().unwrap(),
        "--depth",
        &depth.to_string(),
    ]);
    watchdog::backend(command)
}

static NEXT_INITIAL: AtomicU64 = AtomicU64::new(0);

/// The initial configuration of the generated top cell with `item` in its `<k>` cell.
fn top_with(item: &str) -> String {
    format!(
        "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}({item}, dotk{{}}())), \
         Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\")))"
    )
}

#[test]
fn a_path_decided_conditional_defers_its_discarded_operand() {
    // With `X >Int 0` on the path, the `#if` equation at sort `K` selects `done ~> .K`, and the
    // operand it binds and drops, `loopk()`, keeps its definedness as a deferred obligation. An
    // Int `#if` that a later rule's left-hand side meets is split by its condition, and the
    // branch the path refutes is dropped before its operand `loopi()` is matched. Neither run
    // evaluates the discarded operand.
    let (root, _) = fixture();
    let kite = compiled_for_execution(&root, "kite", PATH_DECIDED, "KITE", "KITE");
    let done = r#"kseq{}(inj{SortExp{}, SortKItem{}}(Lbldone{}()), dotk{}())"#;
    for (start, obligation) in [
        ("LblstartI", ceil_of("SortK", "Lblloopk{}()")),
        ("LblstartD", ceil_of("SortInt", "Lblloopi{}()")),
    ] {
        let pattern = top_with(&format!(
            "inj{{SortExp{{}}, SortKItem{{}}}}({start}{{}}(VarX:SortInt{{}}))"
        ));
        let output = kore_exec_from(&root, &kite, "KITE", &pattern, 3);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{start}: {stdout}\n{stderr}");
        assert!(!stderr.contains("stack"), "{start}: {stderr}");
        let printed = squashed(&stdout);
        assert!(printed.contains(&squashed(done)), "{start}: {stdout}");
        assert!(
            printed.contains(&squashed(&obligation)),
            "{start}: {stdout}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn resuming_from_a_leaf_with_an_open_obligation_does_not_evaluate_it() {
    // A `\ceil` in a state given to execution is read as the deferred obligation a run reports
    // it as, so resuming from the leaf `1 /\ \ceil(loopi())` ends at the same leaf instead of
    // evaluating `loopi()`.
    let (root, _) = fixture();
    let leak = compiled_for_execution(&root, "leak", DISCARDED_DIVERGENCE, "LEAK", "LEAK");
    let one = r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1"))"#;
    let leaf = format!(
        "\\and{{SortGeneratedTopCell{{}}}}({}, {})",
        top_with(one),
        ceil_of("SortInt", "Lblloopi{}()")
    );
    let output = kore_exec_from(&root, &leak, "LEAK", &leaf, 1);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "{stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(squashed(&stdout), squashed(&leaf));
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn a_symbolic_conditional_keeps_its_operands_unevaluated() {
    // With `N` symbolic, no operand but the condition is simplified, so `go(N)` ends at the
    // first unfolding of `fact` without a budget warning.
    let (root, _) = fixture();
    let fact = compiled_for_execution(&root, "fact", GUARDED_RECURSION, "FACT", "FACT");
    let pattern = top_with("inj{SortExp{}, SortKItem{}}(Lblgo{}(VarN:SortInt{}))");
    let output = kore_exec_from(&root, &fact, "FACT", &pattern, 3);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    assert!(!stderr.contains("simplification budget"), "{stderr}");
    assert!(
        squashed(&stdout).contains(&squashed(
            r#"Lbl'UndsStar'Int'Unds'{}(VarN:SortInt{}, Lblfact{}(Lbl'Unds'-Int'Unds'{}(VarN:SortInt{}, \dv{SortInt{}}("1"))))"#
        )),
        "{stdout}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// A conditional whose discarded operand repeats its selected one.
const SHARED_OPERAND: &str = r#"
module VALUE
  imports INT
  imports BOOL
  imports STRING
  imports MAP
  imports K-EQUAL
  syntax Pred ::= "none" [symbol(none)] | p(Int) [symbol(p)] | Pred "and" Pred [symbol(and)]
  syntax Cmd ::= load(String) [symbol(load)]
  configuration <k> $PGM:Cmd </k> <g> none </g> <p> "a" |-> p(1) </p>
  rule <k> load(N) => .K ...</k>
       <g> X => #if X ==K none #then {M [ N ]}:>Pred #else X and {M [ N ]}:>Pred #fi </g>
       <p> M:Map </p>
endmodule
"#;

#[test]
fn a_discarded_operand_reads_an_evaluated_operand_as_its_value() {
    // The selected operand `{M["a"]}:>Pred` evaluates to `p(1)`, which the result is, so the
    // discarded operand's occurrence of it denotes `p(1)` too: its definedness is that of
    // `none and p(1)`, which holds, and no obligation is left. The discarded operand is still
    // not evaluated.
    let (root, _) = fixture();
    let value = compiled_for_execution(&root, "value", SHARED_OPERAND, "VALUE", "VALUE");
    let output = bounded_krun(&value, "Cmd", "load(\"a\")", &["-w", "all"]);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(output.status.success(), "{output:?}");
    assert!(
        squashed(&stdout).contains(&squashed(
            r#"Lbl'-LT-'g'-GT-'{}(Lblp{}(\dv{SortInt{}}("1")))"#
        )),
        "{stdout}"
    );
    assert!(!stdout.contains("\\ceil"), "{stdout}");
    fs::remove_dir_all(root).unwrap();
}

/// A `requires` whose conditional discards a diverging operand.
const CONDITIONAL_REQUIRES: &str = r#"
module RCEIL
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= Int | Bool
               | "run" "(" Bool ")" [symbol(run)]
               | "done" [symbol(done)]
  syntax Bool ::= loopb() [function, symbol(loopb)]
  rule loopb() => notBool loopb()
  configuration <k> $PGM:Exp </k>
  rule <k> run(B) => done ...</k> requires #if B #then true #else loopb() #fi
endmodule
"#;

#[test]
fn a_rule_condition_states_a_discarded_operand_as_a_deferred_obligation() {
    // The instantiated `requires` `#if true #then true #else loopb() #fi` is decided before it is
    // simplified, and its definedness is stated for the operand `true` discards as a deferred
    // obligation: the rule applies under `\ceil(loopb())`, and the instances where `loopb()` is
    // undefined stay at `run(true)`.
    let (root, _) = fixture();
    let rceil = compiled_for_execution(&root, "rceil", CONDITIONAL_REQUIRES, "RCEIL", "RCEIL");
    let output = bounded_krun(&rceil, "Exp", "run(true)", &["-w", "all"]);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    let printed = squashed(&stdout);
    let loopb = ceil_of("SortBool", "Lblloopb{}()");
    assert!(
        printed.contains(&squashed(
            "kseq{}(inj{SortExp{}, SortKItem{}}(Lbldone{}()), dotk{}())"
        )),
        "{stdout}"
    );
    assert!(printed.contains(&squashed(&loopb)), "{stdout}");
    assert!(
        printed.contains(&squashed(&format!(
            "\\not{{SortGeneratedTopCell{{}}}}({loopb})"
        ))),
        "{stdout}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// Console operations in operands `#if` and `andThenBool` discard.
const DISCARDED_CONSOLE: &str = r#"
requires "domains.md"

module IO-ITE-SYNTAX
  imports INT-SYNTAX
  syntax Stmt ::= "ite" | "itefalse" | "rd" | "rdDiv" | "rdNest" | "fp" | "fpReq" | "echo"
                | "andg" | "andgt" | "after" | "rq" | "out" "(" Int ")" [symbol(out)]
  syntax KResult
endmodule

module IO-ITE
  imports IO-ITE-SYNTAX
  imports K-IO
  imports INT
  imports BOOL
  imports STRING
  imports K-EQUAL
  syntax Int ::= fact(Int) [function, symbol(fact)]
               | factReq(Int) [function, symbol(factReq)]
               | h(Int) [function, symbol(h)]
  syntax Bool ::= g() [function, symbol(g)]
                | gt() [function, total, symbol(gt)]
  rule fact(N) => #if N <=Int 0 #then 1 #else N *Int fact(N -Int 1) #fi
  rule factReq(N) => 1 requires N <=Int 0
  rule factReq(N) => N *Int factReq(N -Int 1) requires N >Int 0
  rule g() => #write(1, "g") ==K .K
  rule gt() => #write(1, "g") ==K .K
  configuration <k> $PGM:Stmt </k>
  rule <k> ite => #if 1 <Int 2 #then #write(1, "taken") #else #write(1, "untaken") #fi ...</k>
  rule <k> itefalse => #if 2 <Int 1 #then #write(1, "untaken") #else #write(1, "taken") #fi ...</k>
  rule <k> rd => #if 1 <Int 2 #then .K #else #getc(0) ~> .K #fi ~> echo ...</k>
  rule <k> rdDiv => #putc(1, #if 1 <Int 2 #then 48 #else 1 /Int {#getc(0)}:>Int #fi) ~> echo ...</k>
  rule <k> rdNest => #putc(1, #if 1 <Int 2 #then 48 #else h({#getc(0)}:>Int) #fi) ~> echo ...</k>
  rule <k> echo => #putc(1, {#getc(0)}:>Int) ...</k>
  rule <k> fp => out(fact(3)) ...</k>
  rule <k> fpReq => out(factReq(3)) ...</k>
  rule <k> out(N) => #write(1, Int2String(N)) ...</k>
  rule <k> andg => #putc(1, #if false andThenBool g() #then 49 #else 48 #fi) ~> after ...</k>
  rule <k> andgt => #putc(1, #if false andThenBool gt() #then 49 #else 48 #fi) ~> after ...</k>
  rule <k> after => #write(1, "!") ...</k>
  rule <k> rq => after ...</k> requires #if 1 <Int 2 #then true #else 1 /Int {#getc(0)}:>Int >Int 0 #fi
endmodule
"#;

#[test]
fn a_discarded_conditional_operand_performs_no_console_effect() {
    // A discarded console operation is never performed. One whose definedness depends on a
    // read that is not performed (`1 /Int #getc(0)`, `h(#getc(0))`), or on a function whose
    // equation writes and which is not declared `total` (`g`), is the unsupported outcome at the
    // step that discards it, with nothing consumed or written; a `total` one (`gt`) is defined
    // by its declaration. After `#if`-guarded recursion the state carries an obligation, so the
    // console is unavailable for the rest of the path (`fp`); the `requires` form is not (`fpReq`).
    let (root, _) = fixture();
    let console = compiled_for_execution(
        &root,
        "console",
        DISCARDED_CONSOLE,
        "IO-ITE",
        "IO-ITE-SYNTAX",
    );
    let run = |expression: &str, input: &[u8]| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args([
            "krun",
            "--definition",
            console.to_str().unwrap(),
            "--sort",
            "Stmt",
            "--expression",
            expression,
            "--io",
            "on",
            "--output",
            "none",
        ]);
        output_with_stdin(&mut command, input)
    };
    for (expression, input, written) in [
        ("ite", &b""[..], &b"taken"[..]),
        ("itefalse", b"", b"taken"),
        ("rd", b"QR", b"Q"),
        ("fpReq", b"", b"6"),
        ("andgt", b"", b"0!"),
    ] {
        let output = run(expression, input);
        assert!(output.status.success(), "{expression}: {output:?}");
        assert_eq!(output.stdout, written, "{expression}");
    }
    for (expression, hook, depth) in [
        ("rdDiv", "IO.getc", 0),
        ("rdNest", "IO.getc", 0),
        ("andg", "Lblg", 0),
        ("rq", "IO.getc", 0),
        ("fp", "IO.write", 1),
    ] {
        let output = run(expression, b"QR");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(1), "{expression}: {stderr}");
        assert_eq!(output.stdout, b"", "{expression}");
        assert!(
            stderr.contains(&format!(
                "error: in-process backend halted at depth {depth}: unsupported hook '{hook}'"
            )),
            "{expression}: {stderr}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_a_refuted_let_in_requires_is_not_satisfied() {
    // A `requires` clause holds only where it is defined and true; a refuted `#let` in it is
    // undefined, so the rule does not apply: `r(3)` takes no step, and `g(3)` falls to the
    // `owise` equation.
    let (root, _) = fixture();
    let req = compiled_for_execution(
        &root,
        "req",
        r#"
module REQ
  imports INT
  imports BOOL
  syntax Exp ::= Int
               | "pair" "(" Exp "," Exp ")" [symbol(pair)]
               | r(Exp)                     [symbol(r)]
               | gg(Exp)                    [symbol(gg)]
               | done(Int)                  [symbol(done)]
  syntax Int ::= g(Exp) [function, symbol(g)]
  configuration <k> $PGM:Exp </k>
  rule r(E) => done(1) requires #let pair(X:Int, _) = E #in X >Int 0
  rule g(E) => 1 requires #let pair(X:Int, _) = E #in X >Int 0
  rule g(_) => 0 [owise]
  rule gg(E) => done(g(E))
endmodule
"#,
        "REQ",
        "REQ",
    );
    let output = bounded_krun(&req, "Exp", "r(3)", &[]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        r#"Lbl'-LT-'generatedTop'-GT-'{}(
  Lbl'-LT-'k'-GT-'{}(
    kseq{}(
      inj{SortExp{}, SortKItem{}}(Lblr{}(inj{SortInt{}, SortExp{}}(\dv{SortInt{}}("3")))),
      dotk{}()
    )
  ),
  Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0"))
)
"#
    );
    let done = |value: &str| {
        k_cell_output(&format!(
            r#"inj{{SortExp{{}}, SortKItem{{}}}}(Lbldone{{}}(\dv{{SortInt{{}}}}("{value}")))"#
        ))
    };
    for (program, value) in [
        ("gg(3)", "0"),
        ("r(pair(1, 2))", "1"),
        ("gg(pair(1, 2))", "1"),
    ] {
        let output = bounded_krun(&req, "Exp", program, &[]);
        assert!(output.status.success(), "{program}: {output:?}");
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            done(value),
            "{program}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

/// The equation that makes a refuted `#let` undefined applies only where its pattern is decided
/// not to match: a symbolic argument, or an application `h(N)` no equation evaluates, keeps the
/// lambda application, so the false claims stay unproven (each would be vacuously proven if the
/// refutation fired there), while the instances of the pattern are proven.
#[test]
fn kprove_does_not_refute_a_let_whose_bound_value_is_undecided() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module LETH
  imports INT
  syntax Exp ::= Int
               | "pair" "(" Exp "," Exp ")" [symbol(pair)]
               | "swap" "(" Exp ")"         [symbol(swap)]
  syntax Exp ::= h(Int) [symbol(h), function]
  configuration <k> $PGM:Exp </k>
  rule h(0) => pair(1, 2)
  rule swap(E) => ( #let pair(X, Y) = E #in pair(Y, X) )
endmodule

module LETH-SPEC
  imports LETH
  claim [sym-false]: <k> swap(_E:Exp) => 42 </k>
  claim [h-false]: <k> swap(h(_N:Int)) => 42 </k>
  claim [h0-true]: <k> swap(h(0)) => pair(2, 1) </k>
  claim [pair-true]: <k> swap(pair(A:Exp, B:Exp)) => pair(B, A) </k>
endmodule
"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            definition.to_str().unwrap(),
            "--main-module",
            "LETH-SPEC",
            "--definition-module",
            "LETH",
            "--depth",
            "20",
        ])
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(!output.status.success(), "{stdout}");
    let verdict = |claim: &str| {
        let prefix = format!("claim LETH-SPEC.{claim}: ");
        stdout
            .lines()
            .find_map(|line| line.strip_prefix(&prefix))
            .unwrap_or_else(|| panic!("no {claim} verdict in {stdout}"))
            .split_whitespace()
            .next()
            .unwrap()
            .to_owned()
    };
    assert_eq!(verdict("sym-false"), "failed", "{stdout}");
    assert_eq!(verdict("h-false"), "failed", "{stdout}");
    assert_eq!(verdict("h0-true"), "proven", "{stdout}");
    assert_eq!(verdict("pair-true"), "proven", "{stdout}");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_exec_reports_the_rule_that_precedes_a_vacuous_path() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax State ::= "a" | "b"
  configuration <k> $PGM:State </k>
  rule a => b [label(step)]
endmodule
"#,
    )
    .unwrap();
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--syntax-module",
            "MAIN",
            "--backend",
            "rust",
            "--output-directory",
            compiled.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );

    let initial = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--syntax-module",
            "MAIN",
            "--sort",
            "State",
            "--expression",
            "a",
            "--depth",
            "0",
        ])
        .output()
        .unwrap();
    assert!(
        initial.status.success(),
        "{}",
        String::from_utf8_lossy(&initial.stderr)
    );
    let initial_term = String::from_utf8(initial.stdout).unwrap();
    let constrained = format!(
        r#"\and{{SortGeneratedTopCell{{}}}}(
  {},
  \and{{SortGeneratedTopCell{{}}}}(
    \equals{{SortBool{{}}, SortGeneratedTopCell{{}}}}(
      Lbl'UndsEqlsEqls'Int'Unds'{{}}(N:SortInt{{}}, \dv{{SortInt{{}}}}("0")),
      \dv{{SortBool{{}}}}("true")
    ),
    \equals{{SortBool{{}}, SortGeneratedTopCell{{}}}}(
      Lbl'UndsEqlsSlshEqls'Int'Unds'{{}}(N:SortInt{{}}, \dv{{SortInt{{}}}}("0")),
      \dv{{SortBool{{}}}}("true")
    )
  )
)"#,
        initial_term.trim()
    );
    let initial_path = root.join("vacuous.kore");
    fs::write(&initial_path, constrained).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            compiled.join("definition.kore").to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            initial_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "\\bottom{SortGeneratedTopCell{}}()\n"
    );
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        stderr.contains(
            "execution ended with no successor at depth 1: rule step applied with a false path constraint; refuted obligation"
        ),
        "{stderr}"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_krun_exits_with_the_exit_cell_value_and_prints_the_final_pattern() {
    let output = exit_krun_command().output().unwrap();

    assert_eq!(output.status.code(), Some(7));
    assert!(
        output.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("Lbl'-LT-'exit'-GT-'{}"), "{stdout}");
    assert!(stdout.contains(r#"\dv{SortInt{}}("7")"#), "{stdout}");
}

#[test]
fn reference_kore_exec_exits_with_the_exit_cell_value() {
    let (root, definition, initial) = compiled_exit_fixture();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "EXIT",
            "--pattern",
            initial.to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(7));
    assert!(
        output.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8(output.stdout)
            .unwrap()
            .contains(r#"\dv{SortInt{}}("7")"#)
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_exits_zero_without_an_exit_cell() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  configuration <k> $PGM:Int </k>
  rule <k> _:Int => .K </k>
endmodule
"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--syntax-module",
            "MAIN",
            "--sort",
            "Int",
            "--expression",
            "7",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    fs::remove_dir_all(root).unwrap();
}

fn divergent_exit_fixture() -> (PathBuf, PathBuf) {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  configuration <k> $PGM:Int </k> <exit exit=""> 0 </exit>
  rule <k> N:Int => .K </k> <exit> _ => N </exit>
  rule <k> N:Int => .K </k> <exit> _ => N +Int 1 </exit>
endmodule
"#,
    )
    .unwrap();
    (root, definition)
}

fn divergent_exit_krun(definition: &Path, extra: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--syntax-module",
            "MAIN",
            "--sort",
            "Int",
            "--expression",
            "7",
        ])
        .args(extra)
        .output()
        .unwrap()
}

#[test]
fn krun_exits_111_on_divergent_exit_values_when_exploring_all_rules() {
    let (root, definition) = divergent_exit_fixture();
    let output = divergent_exit_krun(&definition, &["--strategy", "all", "--io", "off"]);

    assert_eq!(output.status.code(), Some(111));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains(r#"\dv{SortInt{}}("7")"#), "{stdout}");
    assert!(stdout.contains(r#"\dv{SortInt{}}("8")"#), "{stdout}");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_exits_with_the_first_rules_exit_value_by_default() {
    // krun runs the program once: it follows one successor per step, that of the first
    // applicable rule by priority and definition order, so the second rule never fires and the
    // exit cell holds the first rule's value. Every successor is what `--search` enumerates.
    let (root, definition) = divergent_exit_fixture();
    let output = divergent_exit_krun(&definition, &[]);

    assert_eq!(output.status.code(), Some(7));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains(r#"\dv{SortInt{}}("7")"#), "{stdout}");
    assert!(!stdout.contains(r#"\dv{SortInt{}}("8")"#), "{stdout}");
    assert!(!stdout.contains("\\or{"), "{stdout}");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_exec_exits_111_on_a_symbolic_exit_value() {
    let (root, definition, initial) = compiled_exit_fixture();
    let concrete = r#"Lbl'-LT-'exit'-GT-'{}(\dv{SortInt{}}("0"))"#;
    let symbolic = "Lbl'-LT-'exit'-GT-'{}(VarExit:SortInt{})";
    let initial_source = fs::read_to_string(&initial).unwrap();
    assert!(initial_source.contains(concrete), "{initial_source}");
    fs::write(&initial, initial_source.replacen(concrete, symbolic, 1)).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "EXIT",
            "--pattern",
            initial.to_str().unwrap(),
            "--depth",
            "0",
        ])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(111));
    assert!(
        String::from_utf8(output.stdout)
            .unwrap()
            .contains("VarExit:SortInt{}")
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_search_exits_zero_regardless_of_the_exit_cell() {
    let output = exit_krun_command().arg("--search-final").output().unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!output.stdout.is_empty());
}

#[test]
fn krun_bottom_final_with_an_exit_cell_exits_111() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax KItem ::= fail(Int) [function, symbol(fail)]
  rule fail(_:Int) => #Bottom
  configuration <k> fail($PGM:Int) </k> <exit exit=""> 0 </exit>
endmodule
"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--syntax-module",
            "MAIN",
            "--sort",
            "Int",
            "--expression",
            "7",
            "--depth",
            "0",
        ])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(111));
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "\\bottom{SortGeneratedTopCell{}}()\n"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_eliminates_a_k_sequence_rewritten_to_bottom() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax Marker ::= "marker"
  configuration <k> marker ~> $PGM:Int </k>
  rule <k> marker => #Bottom ... </k>
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "Int",
            "--expression",
            "1",
            "--depth",
            "10",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(
        output.contains(r"\bottom{SortGeneratedTopCell{}}()"),
        "{output}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_follows_the_first_rule_by_default_and_explores_with_strategy_all() {
    let (root, definition) = branching_search_fixture();
    // The three strategies run one compiled definition.
    let compiled = root.join("compiled");
    kcompile_for_krun(&definition, &["--main-module", "MAIN"], &compiled);
    let krun = |extra: &[&str]| {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["krun", "--definition"])
            .arg(&compiled)
            .args(["--sort", "State", "--expression", "a", "--depth", "10"])
            .args(extra)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).unwrap()
    };

    // Default: one successor per step, the first rule `c => d` by definition order.
    let output = krun(&[]);
    assert!(output.contains("Lbld'Unds'MAIN'Unds'State{}()"), "{output}");
    assert!(
        !output.contains("Lble'Unds'MAIN'Unds'State{}()"),
        "{output}"
    );
    assert!(!output.contains("\\or{"), "{output}");

    // `--strategy all` explores both rules and prints both final configurations.
    let output = krun(&["--strategy", "all", "--io", "off"]);
    assert!(output.contains("Lbld'Unds'MAIN'Unds'State{}()"), "{output}");
    assert!(output.contains("Lble'Unds'MAIN'Unds'State{}()"), "{output}");

    // `--execute-to-branch` stops at the branch point that `--strategy all` exposes.
    let output = krun(&["--strategy", "all", "--execute-to-branch", "--io", "off"]);
    assert!(output.contains("Lblc'Unds'MAIN'Unds'State{}()"), "{output}");
    assert!(
        !output.contains("Lbld'Unds'MAIN'Unds'State{}()"),
        "{output}"
    );
    assert!(
        !output.contains("Lble'Unds'MAIN'Unds'State{}()"),
        "{output}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_preserves_source_rule_order_across_kore_emission_sorting() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  syntax State ::= "a" | "d" | "e"
  configuration <k> $PGM:State </k>
  rule a => e
  rule a => d
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "State",
            "--expression",
            "a",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains("Lble'Unds'MAIN'Unds'State{}()"), "{output}");
    assert!(
        !output.contains("Lbld'Unds'MAIN'Unds'State{}()"),
        "{output}"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_heats_a_strict_production_in_one_order_by_default_and_search_enumerates_both() {
    // Two unevaluated arguments of a `strict` production have two heating rules with equal
    // priority. krun runs the program once, so it heats the first argument and follows that
    // single successor, and the pending frontier stays one state per step;
    // exploring both orders is exponential in the number of such heatings and is what
    // `--search` is for.
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module STRICT-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int | Exp "+" Exp [strict] | "(" Exp ")" [bracket]
endmodule

module STRICT
  imports STRICT-SYNTAX
  imports INT
  syntax KResult ::= Int
  configuration <k> $PGM:Exp </k>
  rule I1:Int + I2:Int => I1 +Int I2
endmodule
"#,
    )
    .unwrap();
    // The bounded run, the whole run and the search use one compiled definition.
    let compiled = root.join("compiled");
    kcompile_for_krun(
        &definition,
        &[
            "--main-module",
            "STRICT",
            "--syntax-module",
            "STRICT-SYNTAX",
        ],
        &compiled,
    );
    let krun = |extra: &[&str]| {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["krun", "--definition"])
            .arg(&compiled)
            .args(["--sort", "Exp", "--expression", "(1 + 2) + (3 + 4)"])
            .args(extra)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).unwrap()
    };
    let first_argument_heated = "'Unds'Exp0'Unds'{}(";
    let second_argument_heated = "'Unds'Exp1'Unds'{}(";

    // One step: exactly one configuration, the left argument heated (its freezer holds `3 + 4`).
    let output = krun(&["--depth", "1"]);
    assert!(!output.contains("\\or{"), "{output}");
    assert!(output.contains(first_argument_heated), "{output}");
    assert!(!output.contains(second_argument_heated), "{output}");

    // The whole run reaches the single final value.
    let output = krun(&[]);
    assert!(!output.contains("\\or{"), "{output}");
    assert!(output.contains(r#"\dv{SortInt{}}("10")"#), "{output}");

    // Control: search still enumerates both heating orders.
    let output = krun(&["--search-one-step"]);
    assert!(output.contains("\\or{"), "{output}");
    assert!(output.contains(first_argument_heated), "{output}");
    assert!(output.contains(second_argument_heated), "{output}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_search_explores_an_unconditional_branch() {
    let (root, definition) = branching_search_fixture();
    let search_pattern = root.join("target.kore");
    fs::write(&search_pattern, "Result:SortGeneratedTopCell{}").unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "State",
            "--expression",
            "a",
            "--depth",
            "10",
            "--search-final",
            "--search-pattern",
            search_pattern.to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains("Result:SortGeneratedTopCell{}"), "{output}");
    assert!(output.contains("Lbld'Unds'MAIN'Unds'State{}()"), "{output}");
    assert!(output.contains("Lble'Unds'MAIN'Unds'State{}()"), "{output}");
    assert!(
        !output.contains("Lblc'Unds'MAIN'Unds'State{}()"),
        "{output}"
    );

    fs::remove_dir_all(root).unwrap();
}

/// `krun --pattern` of `a` on the branching search fixture, from its source or, when `definition`
/// is a directory, from that compiled definition.
fn run_branching_surface_pattern(definition: &Path, pattern: &str, extra: &[&str]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command.arg("krun");
    if definition.is_dir() {
        command.arg("--definition").arg(definition);
    } else {
        command
            .arg(definition)
            .args(["--main-module", "MAIN", "--syntax-module", "MAIN"]);
    }
    command.args(["--sort", "State", "--expression", "a", "--pattern", pattern]);
    command.args(extra).output().unwrap()
}

/// The branching search fixture compiled once, for tests that run it several times.
fn compiled_branching_search_fixture() -> (PathBuf, PathBuf) {
    let (root, definition) = branching_search_fixture();
    let compiled = root.join("compiled");
    kcompile_for_krun(
        &definition,
        &["--main-module", "MAIN", "--syntax-module", "MAIN"],
        &compiled,
    );
    (root, compiled)
}

#[test]
fn krun_surface_pattern_projects_ordinary_final_states() {
    let (root, definition) = compiled_branching_search_fixture();

    let matching = run_branching_surface_pattern(&definition, "<k> d </k>", &[]);
    assert!(
        matching.status.success(),
        "{}",
        String::from_utf8_lossy(&matching.stderr)
    );
    assert!(matches!(
        parse_pattern(&String::from_utf8(matching.stdout).unwrap()).unwrap(),
        Pattern::Top { .. }
    ));

    let nonmatching = run_branching_surface_pattern(&definition, "<k> e </k>", &[]);
    assert!(
        nonmatching.status.success(),
        "{}",
        String::from_utf8_lossy(&nonmatching.stderr)
    );
    assert!(matches!(
        parse_pattern(&String::from_utf8(nonmatching.stdout).unwrap()).unwrap(),
        Pattern::Bottom { .. }
    ));

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_surface_pattern_projects_every_strategy_all_final_state() {
    let (root, definition) = branching_search_fixture();

    let output = run_branching_surface_pattern(
        &definition,
        "<k> S:State </k>",
        &["--strategy", "all", "--io", "off"],
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains("\\or{"), "{output}");
    assert!(output.contains("Lbld'Unds'MAIN'Unds'State{}()"), "{output}");
    assert!(output.contains("Lble'Unds'MAIN'Unds'State{}()"), "{output}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_surface_pattern_routes_through_each_explicit_search_mode() {
    let (root, definition) = compiled_branching_search_fixture();
    for (mode, pattern) in [
        ("--search-final", "<k> d </k>"),
        ("--search-all", "<k> a </k>"),
        ("--search-one-step", "<k> b </k>"),
        ("--search-one-or-more-steps", "<k> c </k>"),
    ] {
        let output = run_branching_surface_pattern(&definition, pattern, &[mode, "--depth", "10"]);
        assert!(
            output.status.success(),
            "{mode}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let output = parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap();
        assert!(matches!(output, Pattern::Top { .. }), "{mode}: {output:?}");
    }

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_surface_pattern_filters_only_generated_anonymous_bindings() {
    let (root, definition) = compiled_branching_search_fixture();

    let named = run_branching_surface_pattern(&definition, "<k> S:State </k>", &[]);
    assert!(
        named.status.success(),
        "{}",
        String::from_utf8_lossy(&named.stderr)
    );
    let named = String::from_utf8(named.stdout).unwrap();
    assert!(named.contains("VarS:SortState{}"), "{named}");

    let anonymous = run_branching_surface_pattern(&definition, "<k> _ </k>", &[]);
    assert!(
        anonymous.status.success(),
        "{}",
        String::from_utf8_lossy(&anonymous.stderr)
    );
    assert!(matches!(
        parse_pattern(&String::from_utf8(anonymous.stdout).unwrap()).unwrap(),
        Pattern::Top { .. }
    ));

    let authored = run_branching_surface_pattern(&definition, "<k> _Gen0:State </k>", &[]);
    assert!(
        authored.status.success(),
        "{}",
        String::from_utf8_lossy(&authored.stderr)
    );
    let authored = String::from_utf8(authored.stdout).unwrap();
    assert!(authored.contains("Var'Unds'Gen0:SortState{}"), "{authored}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_surface_pattern_preserves_the_ordinary_exit_code() {
    let output = exit_krun_command()
        .args(["--pattern", "<k> 999 </k>"])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(7));
    assert!(matches!(
        parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap(),
        Pattern::Bottom { .. }
    ));
}

#[test]
fn krun_surface_pattern_reports_command_line_parse_locations() {
    let (root, definition) = branching_search_fixture();
    let output = run_branching_surface_pattern(&definition, "<k>", &[]);

    assert!(!output.status.success());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("<command line>"), "{stderr}");
    // The incomplete cell fails at EOF, immediately after the opening tag.
    assert!(stderr.contains("1:4"), "{stderr}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn symbolic_depth_two_result_holds_the_stuck_leaves_and_the_path_at_the_depth_bound() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/search/symbolic-depth-bound");
    let (root, _) = fixture();
    let compiled = root.join("symbolic-depth-bound-kompiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "SD",
            "--syntax-module",
            "SD-SYNTAX",
            "--backend",
            "rust",
            "--output-directory",
            compiled.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    let execute = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            compiled.join("definition.kore").to_str().unwrap(),
            "--module",
            "SD",
            "--pattern",
            fixtures.join("symbolic.kore").to_str().unwrap(),
            "--depth",
            "2",
        ])
        .output()
        .unwrap();
    assert!(
        execute.status.success(),
        "{}",
        String::from_utf8_lossy(&execute.stderr)
    );

    let disjuncts = |mut pattern| match &mut pattern {
        Pattern::Or { arguments, .. } => std::mem::take(arguments),
        _ => vec![pattern],
    };
    let reference = disjuncts(
        parse_pattern(&fs::read_to_string(fixtures.join("depth-two.kore")).unwrap()).unwrap(),
    );
    let actual = disjuncts(parse_pattern(&String::from_utf8(execute.stdout).unwrap()).unwrap());
    assert_eq!(reference.len(), 2, "the reference records two stuck leaves");
    for expected in &reference {
        assert!(
            actual.contains(expected),
            "missing reference remainder leaf: {expected:#?}"
        );
    }
    // A depth-bounded result covers every path up to the bound: for X > 1 the path is at
    // count(X -Int 2) after two steps, a result whatever the halted branches did.
    let frontier = parse_pattern(
        r#"\and{SortGeneratedTopCell{}}(
            Lbl'-LT-'generatedTop'-GT-'{}(
                Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortPgm{}, SortKItem{}}(
                    Lblcount'LParUndsRParUnds'SD-SYNTAX'Unds'Pgm'Unds'Int{}(
                        Lbl'UndsPlus'Int'Unds'{}(VarX:SortInt{}, \dv{SortInt{}}("-2"))
                    )
                ), dotk{}())),
                Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0"))
            ),
            \equals{SortBool{}, SortGeneratedTopCell{}}(
                \dv{SortBool{}}("true"),
                Lbl'Unds-GT-'Int'Unds'{}(
                    Lbl'UndsPlus'Int'Unds'{}(VarX:SortInt{}, \dv{SortInt{}}("-1")),
                    \dv{SortInt{}}("0")
                )
            )
        )"#,
    )
    .unwrap();
    let extra = actual
        .iter()
        .filter(|leaf| !reference.contains(leaf))
        .collect::<Vec<_>>();
    assert_eq!(
        extra,
        [&frontier],
        "the port adds exactly the depth-bound leaf count(X -Int 2) with X -Int 1 >Int 0"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_exec_applies_rewrite_rules_tagged_concrete_and_symbolic() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/execution/concrete-symbolic-rules");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "CO",
            "--syntax-module",
            "CO-SYNTAX",
            "--sort",
            "Pgm",
            fixtures.join("concrete-input.pgm").to_str().unwrap(),
            "--depth",
            "2",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        stdout.contains("Lblh'LParUndsRParUnds'CO-SYNTAX'Unds'Pgm'Unds'Int"),
        "{stdout}"
    );
}

/// `concrete` and `symbolic` do not restrict a rewrite step, but a variable both name is still
/// one no term can match: kcompile reports it at the rule instead of compiling a definition the
/// backend then refuses to load.
#[test]
fn kcompile_reports_a_concrete_and_symbolic_overlap_on_a_rewrite_rule_at_the_rule() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"module CO-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= f(Int) | g(Int)
endmodule
module CO
  imports CO-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k>
  rule <k> f(N) => g(N) ... </k> [concrete, symbolic(N)]
endmodule
"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "CO",
            "--syntax-module",
            "CO-SYNTAX",
            "-o",
        ])
        .arg(root.join("out"))
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap();

    assert!(!output.status.success());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        stderr.contains(&format!(
            "{}:9:3: Error[InconsistentFunctionRuleAttributes]: Rule cannot be both concrete and symbolic in the same variable: [N]",
            definition.display()
        )),
        "{stderr}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_search_final_reports_states_cut_by_the_depth_bound() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/search/symbolic-depth-bound");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "SD",
            "--syntax-module",
            "SD-SYNTAX",
            "--sort",
            "Pgm",
            "--expression",
            "count(5)",
            "--search-final",
            "--depth",
            "2",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains(r#"\dv{SortInt{}}("3")"#), "{stdout}");
    assert!(!stdout.contains(r"\bottom"), "{stdout}");
}

#[test]
fn kore_exec_merges_converging_final_states() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/execution/branching-execution");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "BR",
            "--syntax-module",
            "BR-SYNTAX",
            "--sort",
            "Pgm",
            fixtures.join("start.pgm").to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("Lble'Unds'BR-SYNTAX'Unds'Pgm"), "{stdout}");
    assert!(!stdout.contains(r"\or{"), "{stdout}");
}

#[test]
fn krun_reports_bottom_when_the_only_matching_rule_has_a_false_ensures() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/execution/trivial-result-execution");
    // Execution and search run one compiled definition.
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    kcompile_for_krun(
        &fixtures.join("test.k"),
        &["--main-module", "TR", "--syntax-module", "TR-SYNTAX"],
        &compiled,
    );
    let run = |search: bool| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command
            .args(["krun", "--definition"])
            .arg(&compiled)
            .args(["--sort", "Pgm"])
            .arg(fixtures.join("false-ensures.pgm"));
        if search {
            command.arg("--search-final");
        }
        command.output().unwrap()
    };

    for search in [false, true] {
        let output = run(search);
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(
            stdout.contains(r"\bottom{SortGeneratedTopCell{}}()"),
            "search={search}: {stdout}"
        );
        assert!(
            !stdout.contains("Lblc'Unds'TR-SYNTAX'Unds'Pgm"),
            "search={search}: {stdout}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_hook_string_index_boundaries_follow_domains_md() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/hooks/string-index-boundaries");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("string-index-boundaries.k").to_str().unwrap(),
            "--main-module",
            "HOOKS",
            "--syntax-module",
            "HOOKS-SYNTAX",
            "--sort",
            "Pgm",
            fixtures
                .join("string-index-boundaries.hooks")
                .to_str()
                .unwrap(),
            "--depth",
            "10",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let expected = fs::read_to_string(fixtures.join("domains.out"))
        .unwrap()
        .lines()
        .filter_map(|line| {
            let value = line.trim().strip_prefix("ListItem ( ")?;
            let value = value
                .strip_suffix(" ) ~> .K")
                .or_else(|| value.strip_suffix(" )"))?;
            value.parse::<i64>().ok()
        })
        .collect::<Vec<_>>();
    let stdout = String::from_utf8(output.stdout).unwrap();
    // The list's Int items, as opposed to the Int arguments of the substrString applications.
    let integer =
        Regex::new(r#"inj\{SortInt\{\}, SortKItem\{\}\}\(\\dv\{SortInt\{\}\}\(\"(-?[0-9]+)\"\)\)"#)
            .unwrap();
    let actual = integer
        .captures_iter(&stdout)
        .map(|captures| captures[1].parse::<i64>().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(expected, vec![2, 3, 5, -1, 0]);
    assert_eq!(actual, expected);

    // substrString outside its valid indices has a value `domains.md` does not give, so it stays
    // unevaluated with the indices it was given.
    let substring = Regex::new(
        r#"LblsubstrString[^{]*\{\}\(\s*\\dv\{SortString\{\}\}\(\"hello\"\),\s*\\dv\{SortInt\{\}\}\(\"(-?[0-9]+)\"\),\s*\\dv\{SortInt\{\}\}\(\"(-?[0-9]+)\"\)"#,
    )
    .unwrap();
    let unevaluated = substring
        .captures_iter(&stdout)
        .map(|captures| {
            (
                captures[1].parse::<i64>().unwrap(),
                captures[2].parse::<i64>().unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(unevaluated, vec![(-2, 3), (1, 10), (3, 1)], "{stdout}");
}

#[test]
fn krun_executes_hook_edges_to_the_backend_results() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/hooks");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("hook-boundaries.k").to_str().unwrap(),
            "--main-module",
            "HOOK-BOUNDARIES",
            "--syntax-module",
            "HOOK-BOUNDARIES-SYNTAX",
            "--sort",
            "Pgm",
            fixtures.join("edges.hooks").to_str().unwrap(),
            "--depth",
            "10",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    let bool_value = Regex::new(r#"\\dv\{SortBool\{\}\}\(\"(true|false)\"\)"#).unwrap();
    let int_value = Regex::new(r#"\\dv\{SortInt\{\}\}\(\"(-?[0-9]+)\"\)"#).unwrap();
    let string_value = Regex::new(r#"\\dv\{SortString\{\}\}\(\"([^\"]*)\"\)"#).unwrap();

    let bools = bool_value
        .captures_iter(&stdout)
        .map(|captures| captures[1].parse::<bool>().unwrap())
        .collect::<Vec<_>>();
    let ints = int_value
        .captures_iter(&stdout)
        .take(2)
        .map(|captures| captures[1].parse::<i64>().unwrap())
        .collect::<Vec<_>>();
    let strings = string_value
        .captures_iter(&stdout)
        .map(|captures| captures[1].to_owned())
        .collect::<Vec<_>>();

    assert_eq!(bools, vec![false, false, false], "{stdout}");
    assert_eq!(ints, vec![1, 1], "{stdout}");
    assert_eq!(strings, vec![""], "{stdout}");
}

/// Whether a String holds a surrogate code point the definition does not settle (K's string
/// syntax writes one, KORE's literals cannot), so `chrChar(55296)` is neither a value nor
/// undefined: the run keeps the application unevaluated, with a warning, rather than ending in
/// `\bottom`.
#[test]
fn krun_leaves_chr_of_a_surrogate_unevaluated() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/hooks");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("hook-boundaries.k").to_str().unwrap(),
            "--main-module",
            "HOOK-BOUNDARIES",
            "--syntax-module",
            "HOOK-BOUNDARIES-SYNTAX",
            "--sort",
            "Pgm",
            fixtures.join("surrogate.hooks").to_str().unwrap(),
            "--depth",
            "10",
        ])
        .output()
        .unwrap();

    assert!(output.status.success(), "{output:?}");
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        stdout.contains("LblchrChar'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Int{}(")
            && stdout.contains(r#"\dv{SortInt{}}("55296")"#)
            && !stdout.contains("\\bottom"),
        "{stdout}"
    );
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        stderr.contains("hook STRING.chr was left unevaluated")
            && stderr.contains("the definition does not determine its value"),
        "{stderr}"
    );
}

/// A `String` is a sequence of code points, and a K escape names one: `"é"` and `"\xe9"` are
/// one value, and `"\xc3\xa9"` is the two code points U+00C3 U+00A9. KORE literals are code
/// points too, so a result is written with `\xhh` only for a code point up to U+00FF, and a
/// `Bytes` value with `\xhh` for each byte. `s` hides the constants from the constant folder.
#[test]
fn krun_reads_and_writes_strings_as_code_points() {
    const SOURCE: &str = r#"
module POINTS
  imports DOMAINS
  imports BYTES
  configuration <k> $PGM:Pgm </k>
  syntax Pgm ::= "same" | "two" | "joined" | "bytes"
  syntax KItem ::= r(K)
  syntax String ::= s(String) [function, total]
  rule s(S) => S
  rule <k> same => r(s("é") ==String s("\xe9")) </k>
  rule <k> two => r(lengthString(s("\xc3\xa9"))) </k>
  rule <k> joined => r(s("é") +String s("\u0101") +String s("\xc3")) </k>
  rule <k> bytes => r(String2Bytes(s("é\xc3"))) </k>
endmodule
"#;
    let (root, definition) = fixture();
    fs::write(&definition, SOURCE).unwrap();
    let run = |program: &str| {
        let input = root.join(format!("{program}.points"));
        fs::write(&input, program).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                definition.to_str().unwrap(),
                "--main-module",
                "POINTS",
                "--syntax-module",
                "POINTS",
                "--sort",
                "Pgm",
                input.to_str().unwrap(),
                "--io",
                "off",
            ])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert!(output.status.success(), "{program}: {output:?}");
        String::from_utf8(output.stdout).unwrap()
    };
    for (program, value) in [
        ("same", r#"\dv{SortBool{}}("true")"#),
        ("two", r#"\dv{SortInt{}}("2")"#),
        ("joined", r#"\dv{SortString{}}("\xe9\u0101\xc3")"#),
        ("bytes", r#"\dv{SortBytes{}}("\xe9\xc3")"#),
    ] {
        let stdout = run(program);
        assert!(stdout.contains(value), "{program}: {stdout}");
    }
    fs::remove_dir_all(root).unwrap();
}

/// `countAllOccurrences(S, "")` has no value the hook's documentation gives, and none its
/// `domains.md` equations give by evaluation (they state `count = 1 + count` for an empty
/// needle), so a run ends with the application unevaluated and a warning, instead of applying
/// those equations until the native stack runs out. `replaceAll(S, "", R)` has the value its
/// equation states, `replace(S, "", R, countAllOccurrences(S, ""))`, with the count unevaluated.
/// A value the definition gives by its own equation is that value (`given`: `substrString` with
/// reversed indices, which the hook's documentation leaves open). A non-empty needle is counted
/// and replaced. `s` and `i` hide the constants from the constant folder.
#[test]
fn krun_leaves_counting_an_empty_needle_unevaluated() {
    const SOURCE: &str = r#"
module NEEDLE
  imports INT
  imports STRING
  configuration <k> $PGM:Pgm </k>
  syntax Pgm ::= "count" | "replace" | "given" | "nonempty"
  syntax KItem ::= r(K)
  syntax String ::= s(String) [function, total]
  rule s(S) => S
  syntax Int ::= i(Int) [function, total]
  rule i(I) => I
  rule substrString(_, I, J) => "" requires J <Int I
  rule <k> count => r(countAllOccurrences(s("ab"), s(""))) </k>
  rule <k> replace => r(replaceAll(s("ab"), s(""), s("x"))) </k>
  rule <k> given => r(substrString(s("abc"), i(2), i(1))) </k>
  rule <k> nonempty => r(countAllOccurrences(s("abab"), s("ab")) +Int lengthString(replaceAll(s("aaa"), s("aa"), s("bcd")))) </k>
endmodule
"#;
    const COUNT: &str = "LblcountAllOccurrences'LParUndsCommUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String'Unds'String{}(";
    const REPLACE_ALL: &str = "LblreplaceAll'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'String'Unds'String'Unds'String{}(";
    const REPLACE: &str = "Lblreplace'LParUndsCommUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'String'Unds'String'Unds'String'Unds'Int{}(";
    let (root, definition) = fixture();
    fs::write(&definition, SOURCE).unwrap();
    let run = |program: &str| {
        let input = root.join(format!("{program}.needle"));
        fs::write(&input, program).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                definition.to_str().unwrap(),
                "--main-module",
                "NEEDLE",
                "--syntax-module",
                "NEEDLE",
                "--sort",
                "Pgm",
                input.to_str().unwrap(),
                "--depth",
                "10",
            ])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        (
            output.status.success(),
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap(),
        )
    };
    for program in ["count", "replace"] {
        let (success, stdout, stderr) = run(program);
        assert!(success, "{program}: {stdout}{stderr}");
        assert!(stdout.contains(COUNT), "{program}: {stdout}");
        assert!(
            stderr.contains("hook STRING.countAllOccurrences was left unevaluated")
                && stderr.contains("the definition does not determine its value"),
            "{program}: {stderr}"
        );
    }
    let (_, stdout, _) = run("replace");
    assert!(
        stdout.contains(REPLACE) && !stdout.contains(REPLACE_ALL),
        "replace: {stdout}"
    );
    let (success, stdout, stderr) = run("given");
    assert!(success, "given: {stdout}{stderr}");
    assert!(
        stdout.contains(r#"inj{SortString{}, SortKItem{}}(\dv{SortString{}}(""))"#),
        "given: {stdout}"
    );
    let (success, stdout, stderr) = run("nonempty");
    assert!(success, "nonempty: {stdout}{stderr}");
    assert!(
        stdout.contains(r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("6"))"#),
        "nonempty: {stdout}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// `replace` (hook `STRING.replace`) has no evaluator here and has equations in `domains.md`,
/// which the compiled definition holds. Where none of them applies (a count that is not a value),
/// the warning says that none applies, not that the definition has none.
#[test]
fn an_unevaluated_hook_with_equations_is_not_reported_as_having_none() {
    const SOURCE: &str = r#"
module REPLACE-COUNT
  imports STRING
  imports INT
  syntax Int ::= count() [function, no-evaluators]
  syntax Pgm ::= "go"
  configuration <k> $PGM:Pgm </k> <out> "" </out>
  rule <k> go => .K </k> <out> _ => replace("aa", "a", "b", count()) </out>
endmodule
"#;
    let (root, definition) = fixture();
    fs::write(&definition, SOURCE).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "-m",
            "REPLACE-COUNT",
            "-s",
            "Pgm",
            "-e",
            "go",
            "--io",
            "off",
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stderr}");
    assert!(
        stderr.contains("hook STRING.replace was left unevaluated")
            && stderr.contains("no equation of the definition applies"),
        "{stderr}"
    );
    assert!(
        !stderr.contains("no equations in the definition"),
        "{stderr}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// An equation attempt on an `Unspecified` application that fails is undone entirely, its
/// console effects included: what it read is unread and what it wrote unwritten. Here the first
/// equation writes, reads a byte, then needs the application's own value; the second reads a
/// byte and gives its code. Whichever is listed first, the run reads `A` once, gives `"65"`, and
/// writes nothing, the one outcome an evaluation of the definition has.
#[test]
fn krun_undoes_the_console_effects_of_a_failed_unspecified_attempt() {
    const RECURRING: &str = r#"rule substrString(S, I, J) => keep(#write(2, "E1 wrote\n"), keep(#getc(#stdin), substrString(S, I, J))) requires J <Int I"#;
    const READING: &str = r#"rule substrString(_, I, J) => code(#getc(#stdin)) requires J <Int I"#;
    let (root, definition) = fixture();
    let input = root.join("a.attempt");
    fs::write(&input, "a").unwrap();
    for (order, equations) in [
        ("recurring first", [RECURRING, READING]),
        ("reading first", [READING, RECURRING]),
    ] {
        fs::write(
            &definition,
            format!(
                r#"
module ATTEMPT
  imports DOMAINS
  imports K-IO
  configuration <k> $PGM:Pgm </k>
  syntax Pgm ::= "a"
  syntax KItem ::= r(K)
  syntax Int ::= n(Int) [function]
  rule n(I) => I
  syntax String ::= keep(K, String) [function]
  rule keep(_, X) => X
  syntax String ::= code(IOInt) [function]
  rule code(I:Int) => Int2String(I)
  {}
  {}
  rule <k> a => r(substrString("abc", n(2), n(1))) </k>
endmodule
"#,
                equations[0], equations[1]
            ),
        )
        .unwrap();
        let output = output_with_stdin(
            Command::new(env!("CARGO_BIN_EXE_krust")).args([
                "krun",
                definition.to_str().unwrap(),
                "--main-module",
                "ATTEMPT",
                "--syntax-module",
                "ATTEMPT",
                "--sort",
                "Pgm",
                input.to_str().unwrap(),
                "--io",
                "on",
            ]),
            b"AB",
        );
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{order}: {stdout}{stderr}");
        assert!(
            stdout.contains(r#"inj{SortString{}, SortKItem{}}(\dv{SortString{}}("65"))"#),
            "{order}: {stdout}"
        );
        assert!(!stderr.contains("E1 wrote"), "{order}: {stderr}");
        assert!(!stderr.contains("warning"), "{order}: {stderr}");
    }
    fs::remove_dir_all(root).unwrap();
}

/// Run `krust krun` on the program `a` of the module `ATTEMPT` written to `definition` with
/// `rules`, with the console on and `stdin` as its input.
fn run_attempt_module(definition: &Path, input: &Path, rules: &str, stdin: &[u8]) -> Output {
    fs::write(
        definition,
        format!(
            r#"
module ATTEMPT
  imports DOMAINS
  imports K-IO
  configuration <k> $PGM:Pgm </k>
  syntax Pgm ::= "a"
  syntax KItem ::= r(K)
  syntax Int ::= n(Int) [function]
  rule n(I) => I
  syntax String ::= keep(K, String) [function]
  rule keep(_, X) => X
  {rules}
  rule <k> a => r(substrString("abc", n(2), n(1))) </k>
endmodule
"#
        ),
    )
    .unwrap();
    output_with_stdin(
        Command::new(env!("CARGO_BIN_EXE_krust")).args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "ATTEMPT",
            "--syntax-module",
            "ATTEMPT",
            "--sort",
            "Pgm",
            input.to_str().unwrap(),
            "--io",
            "on",
        ]),
        stdin,
    )
}

/// A value an attempt computed with a console effect is computed again, effect included, when
/// the next equation needs it: the failed attempt's effect was undone, so reusing the value
/// without the effect would lose it. `T = substr("abc", 4, 1)` writes `T wrote` and is `"t"`;
/// `A = substr("abc", 2, 1)` first tries `keep(T, A)`, which fails, then `keep(T, "v")`. The
/// run ends with `"v"` and `T wrote` written once.
#[test]
fn krun_repeats_the_effects_of_a_value_a_failed_attempt_computed() {
    const RULES: &str = r#"
  rule substrString(_, 4, J) => keep(#write(2, "T wrote\n"), "t") requires J <Int 4
  rule substrString(S, 2, J) => keep(substrString(S, 4, J), substrString(S, 2, J)) requires J <Int 2
  rule substrString(S, 2, J) => keep(substrString(S, 4, J), "v") requires J <Int 2
"#;
    let (root, definition) = fixture();
    let input = root.join("a.attempt");
    fs::write(&input, "a").unwrap();
    let output = run_attempt_module(&definition, &input, RULES, b"");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}{stderr}");
    assert!(
        stdout.contains(r#"inj{SortString{}, SortKItem{}}(\dv{SortString{}}("v"))"#),
        "{stdout}"
    );
    assert_eq!(stderr.matches("T wrote").count(), 1, "{stderr}");
    fs::remove_dir_all(root).unwrap();
}

/// A rule condition's verdict does not depend on whether the execution happened to compute a
/// value it reads before. The console's own checks (the console position compared, and a console
/// hook noted as read) are pinned by `a_value_read_from_the_console_is_not_reused_without_it` and
/// `a_failed_evaluation_that_read_the_console_is_not_reused_after_it_moved_on`, and on a run by
/// `krun_does_not_reuse_a_failed_evaluation_that_read_stdin_after_the_console_moved_on`. This
/// test passes with either check removed, because `Record::holds` also refuses the execution's
/// record on its simplification options: the execution simplifies its term keeping a partial
/// result when the budget runs out (`BudgetPolicy::KeepPartial`), and a rule condition is
/// simplified failing then (`BudgetPolicy::Fail`). It fails only when that comparison is removed
/// as well.
/// `T = substr("abc", 4, 1)` reads standard input; `g`'s condition asks for `T`. Whether `A`
/// computes `T` before `g` (`g(T)`) or not (`g("")`), the condition is the same and `g` stays
/// unevaluated.
#[test]
fn krun_decides_a_condition_alike_whether_the_execution_computed_its_value_before() {
    let rules = |a: &str| {
        format!(
            r#"
  syntax String ::= rd(IOString) [function]
  rule rd(S:String) => S
  syntax String ::= g(String) [function]
  rule g(_) => "seen" requires lengthString(substrString("abc", 4, 1)) ==Int 0
  rule substrString(_, 4, J) => rd(#read(#stdin, 1)) requires J <Int 4
  rule substrString(S, 2, J) => {a} requires J <Int 2
"#
        )
    };
    let (root, definition) = fixture();
    let input = root.join("a.attempt");
    fs::write(&input, "a").unwrap();
    let results = ["g(substrString(S, 4, J))", r#"g("")"#].map(|a| {
        let output = run_attempt_module(&definition, &input, &rules(a), b"");
        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{a}: {stdout}{stderr}");
        assert!(
            !stdout.contains(r#"\dv{SortString{}}("seen")"#),
            "{a}: {stdout}"
        );
        stdout
    });
    assert_eq!(results[0], results[1]);
    fs::remove_dir_all(root).unwrap();
}

/// A failed evaluation that read standard input is not reused once the console has moved on:
/// its attempts read input that a later evaluation reads differently. `F = substr("abc", 4, 1)`
/// is `g` of one byte read, with `g("x") = F +String ""` (no value: `F` is open) and `g("y") =
/// "v"`; `A = substr("abc", 2, 1)` is `F +String (read +String F)` on the input `"xy"`. The
/// first `F` reads `"x"` and fails, its read undone; the read in `A` takes `"x"`; the second `F`
/// reads `"y"` and is `"v"`. Both evaluations of `F` are made by the execution's own
/// simplification, under the same options, solver and assumptions, so only the console's checks
/// tell them apart: the test fails when the console position is not compared, or when a console
/// hook is not noted as read.
#[test]
fn krun_does_not_reuse_a_failed_evaluation_that_read_stdin_after_the_console_moved_on() {
    const RULES: &str = r#"
  syntax String ::= rd(IOString) [function]
  rule rd(S:String) => S
  syntax String ::= g(String) [function]
  rule g(Z) => substrString("abc", 4, 1) +String "" requires Z ==String "x"
  rule g(Z) => "v" requires Z ==String "y"
  rule substrString(_, 4, J) => g(rd(#read(#stdin, 1))) requires J <Int 4
  rule substrString(S, 2, J) => substrString(S, 4, J) +String (rd(#read(#stdin, 1)) +String substrString(S, 4, J)) requires J <Int 2
"#;
    let (root, definition) = fixture();
    let input = root.join("a.attempt");
    fs::write(&input, "a").unwrap();
    let output = run_attempt_module(&definition, &input, RULES, b"xy");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}{stderr}");
    assert!(stdout.contains(r#"\dv{SortString{}}("xv")"#), "{stdout}");
    fs::remove_dir_all(root).unwrap();
}

/// An application on constructor-like arguments of a `total` hook this backend has no evaluator
/// for (`expFloat`) has a value the backend does not compute. Term simplification leaves it
/// unevaluated with a warning, so a run whose result does not depend on it ends with that result
/// (`false andBool B` is `false`, a discarded `#if` branch is discarded), while a run that would
/// decide a condition over it, or end on a configuration holding it, halts with the
/// unsupported-hook error. A partial hook without an evaluator (`logFloat`) is the error where
/// the simplifier reaches it: its definedness is unknown too, so even a discarded application
/// leaves an undecided condition. `i` and `fl` hide the constants from the constant folder.
#[test]
fn krun_refuses_an_application_without_an_evaluator_only_where_a_run_needs_it() {
    let (root, definition) = fixture();
    fs::write(&definition, NO_EVALUATOR).unwrap();
    let run = |program: &str| {
        let input = root.join(format!("{program}.noeval"));
        fs::write(&input, program).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                definition.to_str().unwrap(),
                "--main-module",
                "NOEVAL",
                "--syntax-module",
                "NOEVAL",
                "--sort",
                "Pgm",
                input.to_str().unwrap(),
                "--depth",
                "10",
            ])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        (
            output.status.success(),
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap(),
        )
    };
    for (program, value) in [
        (
            "unused",
            r#"inj{SortBool{}, SortKItem{}}(\dv{SortBool{}}("false"))"#,
        ),
        (
            "branch",
            r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("7"))"#,
        ),
    ] {
        let (success, stdout, stderr) = run(program);
        assert!(success, "{program}: {stdout}{stderr}");
        assert!(stdout.contains(value), "{program}: {stdout}");
        // The operand a decided `#if` discards (`branch`) is never evaluated.
        assert_eq!(
            stderr.contains("hook FLOAT.exp was left unevaluated"),
            program == "unused",
            "{program}: {stderr}"
        );
    }
    for (program, hook) in [
        ("used", "FLOAT.exp"),
        ("decide", "FLOAT.exp"),
        ("partial", "FLOAT.log"),
    ] {
        let (success, stdout, stderr) = run(program);
        assert!(!success, "{program}: {stdout}{stderr}");
        assert!(
            stderr.contains(&format!(
                "unsupported hook '{hook}' on constructor-like arguments"
            )),
            "{program}: {stderr}"
        );
        assert!(
            !stdout.contains("pos") && !stdout.contains("nonpos"),
            "{program}: {stdout}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

/// `^Int` and `<<Int` results above the backend's result size bound are not computed. A run
/// that does not use them still ends with its value (the application is left unevaluated with a
/// warning wherever the simplifier reaches it, and a discarded one leaves no definedness
/// condition), and so does one whose condition over them the solver decides, or one that
/// carries the application through a step and then drops it. A run halts with the
/// unsupported-hook error naming the bound instead of branching on a condition over one that
/// the solver cannot decide (`<<Int` has no interpreted SMT encoding, so `shl` would otherwise
/// end in both `pos` and the unreachable `nonpos`), or of ending in a configuration that holds
/// one. A result within the bound is computed (`computed`, 2^20 + 1 bits from one-word
/// arguments, under the 2^24-bit floor). `i` hides the constants from the constant folder.
#[test]
fn krun_neither_branches_nor_ends_on_a_result_above_the_size_bound() {
    let (root, definition) = fixture();
    fs::write(&definition, SIZE_BOUND).unwrap();
    let run = |program: &str| {
        let input = root.join(format!("{program}.bound"));
        fs::write(&input, program).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                definition.to_str().unwrap(),
                "--main-module",
                "BOUND",
                "--syntax-module",
                "BOUND",
                "--sort",
                "Pgm",
                input.to_str().unwrap(),
                "--depth",
                "10",
            ])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        (
            output.status.success(),
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap(),
        )
    };
    let warned = |stderr: &str, hook: &str| {
        stderr.contains(&format!("hook {hook} was left unevaluated"))
            && stderr.contains("needs more than 16777216 bits")
    };
    let halted = |stderr: &str, hook: &str| {
        stderr.contains(&format!(
            "unsupported hook '{hook}' on constructor-like arguments"
        )) && stderr.contains("needs more than 16777216 bits")
    };
    let item = |value: &str| {
        format!(r#"inj{{SortInt{{}}, SortKItem{{}}}}(\dv{{SortInt{{}}}}("{value}"))"#)
    };

    for (program, hook) in [("unused", "INT.pow"), ("unusedshl", "INT.shl")] {
        let (success, stdout, stderr) = run(program);
        assert!(success, "{program}: {stdout}{stderr}");
        // The dropped application is defined, so no definedness condition remains.
        assert!(
            stdout.contains(r#"inj{SortBool{}, SortKItem{}}(\dv{SortBool{}}("false"))"#)
                && !stdout.contains("\\ceil"),
            "{program}: {stdout}"
        );
        assert!(warned(&stderr, hook), "{program}: {stderr}");
    }
    for (program, value) in [
        ("branch", "7"),
        ("guard", "4"),
        ("decided", "1"),
        ("dropped", "9"),
    ] {
        let (success, stdout, stderr) = run(program);
        assert!(success, "{program}: {stdout}{stderr}");
        assert!(stdout.contains(&item(value)), "{program}: {stdout}");
    }
    // A result above 2^20 bits but within the 2^24-bit floor is computed.
    let (success, stdout, stderr) = run("computed");
    assert!(success, "computed: {stdout}{stderr}");
    assert!(
        stdout.contains(r#"inj{SortBool{}, SortKItem{}}(\dv{SortBool{}}("true"))"#)
            && !stderr.contains("left unevaluated"),
        "computed: {stdout}{stderr}"
    );
    for (program, hook) in [("used", "INT.pow"), ("shl", "INT.shl")] {
        let (success, stdout, stderr) = run(program);
        assert!(!success, "{program}: {stdout}{stderr}");
        assert!(halted(&stderr, hook), "{program}: {stderr}");
        assert!(
            !stdout.contains("\\or") && !stdout.contains("nonpos") && !stdout.contains("Lblpos"),
            "{program}: {stdout}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

/// A search pattern's condition over a `<<Int` result above the size bound is not decided by
/// the solver reading the hook as an arbitrary function: the search reports the state as
/// incomplete with the unsupported-hook error instead of a solution (no reachable state has
/// `X <=Int 0`). A pattern that only binds the value reports it. A condition the solver decides
/// over a `^Int` result above the bound (`^Int` has an interpreted SMT encoding) is decided: the
/// state is a solution of `X >Int 0` and not of `X <=Int 0`. `i` hides the shift amount and the
/// exponent from the constant folder.
#[test]
fn krun_search_matches_no_condition_on_a_result_above_the_size_bound() {
    let (root, definition) = fixture();
    fs::write(&definition, SEARCH_BOUND).unwrap();
    let input = root.join("go.search");
    fs::write(&input, "go").unwrap();
    let power = root.join("power.search");
    fs::write(&power, "power").unwrap();
    let search_from = |input: &Path, pattern: &str| {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                definition.to_str().unwrap(),
                "--main-module",
                "SEARCH-BOUND",
                "--syntax-module",
                "SEARCH-BOUND",
                "--sort",
                "Pgm",
                input.to_str().unwrap(),
                "--search-all",
                "--pattern",
                pattern,
            ])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        (
            output.status.success(),
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap(),
        )
    };
    let search = |pattern: &str| search_from(&input, pattern);
    for (condition, solution) in [("X >Int 0", true), ("X <=Int 0", false)] {
        let (success, stdout, stderr) =
            search_from(&power, &format!("<k> f(X) </k> requires {condition}"));
        assert!(success, "{condition}: {stdout}{stderr}");
        assert!(!stderr.contains("UnsupportedHook"), "{condition}: {stderr}");
        assert_eq!(stdout.contains("VarX"), solution, "{condition}: {stdout}");
    }
    for condition in ["X <=Int 0", "X >Int 0"] {
        let (success, stdout, stderr) = search(&format!("<k> f(X) </k> requires {condition}"));
        assert!(!success, "{condition}: {stdout}{stderr}");
        assert!(!stdout.contains("VarX"), "{condition}: {stdout}");
        // The incomplete entry is described, not dumped: the reason, the refused application
        // and the state in KORE, and the state's depth.
        assert!(
            stderr.contains(
                "unsupported hook 'INT.shl' on constructor-like arguments: 1 <<Int 16777217 needs more than"
            ) && stderr.contains("in the state at depth 1:")
                && stderr.contains(r#"Lbl'Unds-LT--LT-'Int'Unds'{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("16777217"))"#),
            "{condition}: {stderr}"
        );
        assert!(
            !stderr.contains("TermData") && !stderr.contains("SearchState"),
            "{condition}: {stderr}"
        );
    }
    let (success, stdout, stderr) = search("<k> f(X) </k>");
    assert!(success, "{stdout}{stderr}");
    assert!(
        stdout.contains("VarX:SortInt{}") && stdout.contains(r#"\dv{SortInt{}}("16777217")"#),
        "{stdout}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// `bitRangeInt` and `signExtendBitRangeInt` applied to the integers of the program, so that the
/// frontend's constant fold cannot compute them.
const BIT_RANGE_DEFINITION: &str = r#"
module BITRANGE-SYNTAX
  imports INT-SYNTAX
  syntax Op ::= br(Int, Int, Int) | sx(Int, Int, Int)
endmodule

module BITRANGE
  imports BITRANGE-SYNTAX
  imports INT
  configuration <k> $PGM:Op </k>
  syntax KItem ::= res(Int)
  rule br(I, X, L) => res(bitRangeInt(I, X, L))
  rule sx(I, X, L) => res(signExtendBitRangeInt(I, X, L))
endmodule
"#;

/// The hook attribute alone gives `bitRangeInt` and `signExtendBitRangeInt` their meaning: a
/// definition that imports `INT-COMMON`, which declares them, without `INT`, which states their
/// equations, evaluates them as one that imports `INT` does. With `INT` imported, a length whose
/// `1 <<Int LEN` is above the `Int` result bound still gives the small value of the bit range.
#[test]
fn krun_evaluates_bit_ranges_without_the_int_module_equations() {
    let common = BIT_RANGE_DEFINITION.replace("  imports INT\n", "  imports INT-COMMON\n");
    assert_ne!(common, BIT_RANGE_DEFINITION);
    let (root, _) = fixture();
    let compile = |name: &str, source: &str| {
        let path = root.join(format!("{name}.k"));
        fs::write(&path, source).unwrap();
        let compiled = root.join(name);
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kcompile",
                path.to_str().unwrap(),
                "--main-module",
                "BITRANGE",
                "--output-directory",
            ])
            .arg(&compiled)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        compiled
    };
    let run = |compiled: &Path, expression: &str| {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                "--definition",
                compiled.to_str().unwrap(),
                "--sort",
                "Op",
                "--expression",
                expression,
                "--io",
                "off",
            ])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(output.status.success(), "{expression}: {stderr}");
        stdout
    };
    let result = |value: &str| {
        format!(
            r#"Lblres'LParUndsRParUnds'BITRANGE'Unds'KItem'Unds'Int{{}}(\dv{{SortInt{{}}}}("{value}"))"#
        )
    };
    let common = compile("common", &common);
    for (expression, value) in [("br(255, 4, 4)", "15"), ("sx(255, 0, 8)", "-1")] {
        let stdout = run(&common, expression);
        assert!(stdout.contains(&result(value)), "{expression}: {stdout}");
    }
    let int = compile("int", BIT_RANGE_DEFINITION);
    let stdout = run(&int, "br(5, 0, 100000000)");
    assert!(stdout.contains(&result("5")), "{stdout}");
    fs::remove_dir_all(root).unwrap();
}

/// One ground application of every `equation_defined` hook of the capability inventory, its
/// arguments taken from the program so that the frontend's constant fold cannot compute it.
const EQUATION_DEFINED_DEFINITION: &str = r#"
module EQUATION-DEFINED-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  syntax Op ::= push(Int, Int) | rf(String, String, String) | fc(String, String, Int)
              | rfc(String, String, Int) | rep(String, String, String, Int)
endmodule

module EQUATION-DEFINED
  imports EQUATION-DEFINED-SYNTAX
  imports DOMAINS
  configuration <k> $PGM:Op </k>
  syntax KItem ::= res(K)
  rule push(A, B) => res(pushList(A, ListItem(B)))
  rule rf(S, N, R) => res(replaceFirst(S, N, R))
  rule fc(S, N, I) => res(findChar(S, N, I))
  rule rfc(S, N, I) => res(rfindChar(S, N, I))
  rule rep(S, N, R, C) => res(replace(S, N, R, C))
endmodule
"#;

/// A hook the capability inventory classifies `equation_defined` has no backend evaluator, and a
/// ground application of it evaluates to a value through the equations of its module, imported
/// here through `DOMAINS`. The applications below are exactly one per member of the class, so a
/// hook moved into or out of the class without its application fails here. That each member's
/// equations come from the module the inventory names is
/// `equation_defined_hooks_have_equations_in_their_named_module` in `hook_capabilities.rs`.
#[test]
fn krun_evaluates_equation_defined_hooks_through_their_equations() {
    let manifest: toml::Value =
        toml::from_str(include_str!("fixtures/hook-capabilities.toml")).unwrap();
    let members = manifest["equation_defined"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|group| group["hooks"].as_array().unwrap())
        .map(|hook| hook.as_str().unwrap())
        .collect::<BTreeSet<_>>();
    // (hook, program, the result's KItem with whitespace removed)
    let cases = [
        (
            "LIST.push",
            "push(1, 2)",
            r#"inj{SortList{},SortKItem{}}(Lbl'Unds'List'Unds'{}(LblListItem{}(inj{SortInt{},SortKItem{}}(\dv{SortInt{}}("1"))),LblListItem{}(inj{SortInt{},SortKItem{}}(\dv{SortInt{}}("2")))))"#,
        ),
        (
            "STRING.replaceFirst",
            r#"rf("abcabc", "b", "X")"#,
            r#"inj{SortString{},SortKItem{}}(\dv{SortString{}}("aXcabc"))"#,
        ),
        (
            "STRING.findChar",
            r#"fc("hello", "lo", 0)"#,
            r#"inj{SortInt{},SortKItem{}}(\dv{SortInt{}}("2"))"#,
        ),
        (
            "STRING.rfindChar",
            r#"rfc("hello", "lo", 4)"#,
            r#"inj{SortInt{},SortKItem{}}(\dv{SortInt{}}("4"))"#,
        ),
        (
            "STRING.replace",
            r#"rep("aaaa", "a", "b", 2)"#,
            r#"inj{SortString{},SortKItem{}}(\dv{SortString{}}("bbaa"))"#,
        ),
    ];
    let exercised = cases
        .iter()
        .map(|(hook, _, _)| *hook)
        .collect::<BTreeSet<_>>();
    assert_eq!(
        exercised, members,
        "every equation-defined hook, and only those, has a ground application here"
    );

    let (root, _) = fixture();
    let path = root.join("equation-defined.k");
    fs::write(&path, EQUATION_DEFINED_DEFINITION).unwrap();
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            path.to_str().unwrap(),
            "--main-module",
            "EQUATION-DEFINED",
            "--output-directory",
        ])
        .arg(&compiled)
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    for (hook, program, value) in cases {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                "--definition",
                compiled.to_str().unwrap(),
                "--sort",
                "Op",
                "--expression",
                program,
                "--io",
                "off",
            ])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{hook}: {program}: {stderr}");
        let stdout = String::from_utf8(output.stdout)
            .unwrap()
            .split_whitespace()
            .collect::<String>();
        let expected = format!(
            "Lblres'LParUndsRParUnds'EQUATION-DEFINED'Unds'KItem'Unds'K{{}}(kseq{{}}({value},dotk{{}}()))"
        );
        assert!(
            stdout.contains(&expected),
            "{hook}: {program}: expected {expected} in {stdout}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

/// A hook, the sorts of its arguments, its result sort, and argument tuples written as literals.
type FoldedHookCase = (
    &'static str,
    &'static [&'static str],
    &'static str,
    &'static [&'static [&'static str]],
);

/// Every hook the constant fold evaluates (the `BOOL`, `INT` and `STRING` hooks with a backend
/// evaluator), declared at its natural sorts, with literal arguments at the edges the hook models
/// draw from (`k-rust-backend/src/builtin/hook_models`): zero, signs, values beyond 64 and 128
/// bits, the empty string, escapes, and code points beyond ASCII, the Basic Multilingual Plane
/// and one byte. `STRING.string2token` is declared at `Id` and at a sort hooked `INT.Int` under
/// another name. Each argument tuple names a value of the hook, so a run of every case at once
/// ends in one configuration.
const FOLDED_HOOK_CASES: &[FoldedHookCase] = &[
    (
        "BOOL.and",
        &["Bool", "Bool"],
        "Bool",
        &[&["true", "false"], &["true", "true"]],
    ),
    (
        "BOOL.andThen",
        &["Bool", "Bool"],
        "Bool",
        &[&["false", "true"], &["true", "true"]],
    ),
    (
        "BOOL.eq",
        &["Bool", "Bool"],
        "Bool",
        &[&["true", "false"], &["false", "false"]],
    ),
    (
        "BOOL.implies",
        &["Bool", "Bool"],
        "Bool",
        &[&["true", "false"], &["false", "true"]],
    ),
    (
        "BOOL.ne",
        &["Bool", "Bool"],
        "Bool",
        &[&["true", "false"], &["true", "true"]],
    ),
    ("BOOL.not", &["Bool"], "Bool", &[&["true"], &["false"]]),
    (
        "BOOL.or",
        &["Bool", "Bool"],
        "Bool",
        &[&["false", "false"], &["false", "true"]],
    ),
    (
        "BOOL.orElse",
        &["Bool", "Bool"],
        "Bool",
        &[&["true", "false"], &["false", "false"]],
    ),
    (
        "BOOL.xor",
        &["Bool", "Bool"],
        "Bool",
        &[&["true", "false"], &["true", "true"]],
    ),
    (
        "INT.abs",
        &["Int"],
        "Int",
        &[&["-18446744073709551617"], &["0"], &["7"]],
    ),
    (
        "INT.add",
        &["Int", "Int"],
        "Int",
        &[&["18446744073709551615", "1"], &["-5", "3"]],
    ),
    (
        "INT.and",
        &["Int", "Int"],
        "Int",
        &[
            &["-1", "340282366920938463463374607431768211457"],
            &["12", "10"],
        ],
    ),
    (
        "INT.bitRange",
        &["Int", "Int", "Int"],
        "Int",
        &[&["-1", "3", "70"], &["255", "4", "4"]],
    ),
    (
        "INT.ediv",
        &["Int", "Int"],
        "Int",
        &[&["-7", "2"], &["7", "-2"]],
    ),
    (
        "INT.emod",
        &["Int", "Int"],
        "Int",
        &[&["-7", "2"], &["7", "-2"]],
    ),
    (
        "INT.eq",
        &["Int", "Int"],
        "Bool",
        &[&["-0", "0"], &["1", "2"]],
    ),
    (
        "INT.ge",
        &["Int", "Int"],
        "Bool",
        &[&["-1", "-1"], &["-2", "18446744073709551616"]],
    ),
    (
        "INT.gt",
        &["Int", "Int"],
        "Bool",
        &[&["2", "1"], &["1", "1"]],
    ),
    (
        "INT.le",
        &["Int", "Int"],
        "Bool",
        &[&["3", "-3"], &["-3", "3"]],
    ),
    (
        "INT.log2",
        &["Int"],
        "Int",
        &[&["1"], &["18446744073709551616"]],
    ),
    (
        "INT.lt",
        &["Int", "Int"],
        "Bool",
        &[&["-18446744073709551617", "0"], &["0", "0"]],
    ),
    (
        "INT.max",
        &["Int", "Int"],
        "Int",
        &[&["-1", "-2"], &["5", "18446744073709551616"]],
    ),
    (
        "INT.min",
        &["Int", "Int"],
        "Int",
        &[&["-1", "-2"], &["5", "18446744073709551616"]],
    ),
    (
        "INT.mul",
        &["Int", "Int"],
        "Int",
        &[
            &["-18446744073709551616", "18446744073709551616"],
            &["0", "-9"],
        ],
    ),
    (
        "INT.ne",
        &["Int", "Int"],
        "Bool",
        &[&["1", "2"], &["7", "7"]],
    ),
    (
        "INT.not",
        &["Int"],
        "Int",
        &[&["0"], &["-18446744073709551617"]],
    ),
    (
        "INT.or",
        &["Int", "Int"],
        "Int",
        &[&["-8", "5"], &["12", "10"]],
    ),
    (
        "INT.pow",
        &["Int", "Int"],
        "Int",
        &[&["-3", "41"], &["-1", "-5"], &["7", "0"]],
    ),
    (
        "INT.powmod",
        &["Int", "Int", "Int"],
        "Int",
        &[&["-2", "3", "5"], &["3", "200", "-1000000007"]],
    ),
    (
        "INT.shl",
        &["Int", "Int"],
        "Int",
        &[&["-3", "70"], &["0", "5"]],
    ),
    (
        "INT.shr",
        &["Int", "Int"],
        "Int",
        &[&["-7", "1"], &["12345", "18446744073709551616"]],
    ),
    (
        "INT.signExtendBitRange",
        &["Int", "Int", "Int"],
        "Int",
        &[&["255", "0", "8"], &["-6", "1", "70"]],
    ),
    (
        "INT.sub",
        &["Int", "Int"],
        "Int",
        &[&["0", "18446744073709551616"], &["-5", "-5"]],
    ),
    (
        "INT.tdiv",
        &["Int", "Int"],
        "Int",
        &[&["-7", "2"], &["7", "-2"]],
    ),
    (
        "INT.tmod",
        &["Int", "Int"],
        "Int",
        &[&["-7", "2"], &["7", "-2"]],
    ),
    (
        "INT.xor",
        &["Int", "Int"],
        "Int",
        &[&["-1", "5"], &["12", "10"]],
    ),
    (
        "STRING.base2string",
        &["Int", "Int"],
        "String",
        &[&["255", "16"], &["-35", "36"], &["0", "2"]],
    ),
    (
        "STRING.chr",
        &["Int"],
        "String",
        &[&["65"], &["955"], &["128000"], &["255"]],
    ),
    (
        "STRING.concat",
        &["String", "String"],
        "String",
        &[
            &[r#""λ""#, r#""\U0001f980""#],
            &[r#""a\"b""#, r#""\\""#],
            &[r#""""#, r#""""#],
        ],
    ),
    (
        "STRING.countAllOccurrences",
        &["String", "String"],
        "Int",
        &[&[r#""aaaa""#, r#""aa""#], &[r#""héllo""#, r#""l""#]],
    ),
    (
        "STRING.eq",
        &["String", "String"],
        "Bool",
        &[&[r#""é""#, r#""é""#], &[r#""a""#, r#""b""#]],
    ),
    (
        "STRING.find",
        &["String", "String", "Int"],
        "Int",
        &[
            &[r#""héllo""#, r#""l""#, "3"],
            &[r#""abc""#, r#""""#, "-5"],
            &[r#""abc""#, r#""d""#, "0"],
        ],
    ),
    (
        "STRING.ge",
        &["String", "String"],
        "Bool",
        &[&[r#""b""#, r#""ab""#], &[r#""""#, r#""a""#]],
    ),
    (
        "STRING.gt",
        &["String", "String"],
        "Bool",
        &[&[r#""\U0001f980""#, r#""￿""#], &[r#""a""#, r#""a""#]],
    ),
    (
        "STRING.int2string",
        &["Int"],
        "String",
        &[&["-340282366920938463463374607431768211456"], &["0"]],
    ),
    (
        "STRING.le",
        &["String", "String"],
        "Bool",
        &[&[r#""ab""#, r#""b""#], &[r#""b""#, r#""ab""#]],
    ),
    (
        "STRING.length",
        &["String"],
        "Int",
        &[&[r#""héllo\U0001f980""#], &[r#""""#]],
    ),
    (
        "STRING.lt",
        &["String", "String"],
        "Bool",
        &[&[r#""""#, r#""\x00""#], &[r#""b""#, r#""a""#]],
    ),
    (
        "STRING.ne",
        &["String", "String"],
        "Bool",
        &[&[r#""\n""#, r#""\t""#], &[r#""x""#, r#""x""#]],
    ),
    (
        "STRING.ord",
        &["String"],
        "Int",
        &[&[r#""\U0001f980""#], &[r#""é""#]],
    ),
    (
        "STRING.replaceAll",
        &["String", "String", "String"],
        "String",
        &[
            &[r#""abab""#, r#""b""#, r#""λ""#],
            &[r#""aaa""#, r#""aa""#, r#""""#],
        ],
    ),
    (
        "STRING.rfind",
        &["String", "String", "Int"],
        "Int",
        &[
            &[r#""héllo""#, r#""l""#, "100"],
            &[r#""abc""#, r#""a""#, "-1"],
        ],
    ),
    (
        "STRING.string2base",
        &["String", "Int"],
        "Int",
        &[&[r#""-fF""#, "16"], &[r#""z""#, "36"]],
    ),
    (
        "STRING.string2int",
        &["String"],
        "Int",
        &[&[r#""-007""#], &[r#""+18446744073709551616""#]],
    ),
    (
        "STRING.string2token",
        &["String"],
        "Id",
        &[&[r#""x""#], &[r#""_42""#]],
    ),
    (
        "STRING.string2token",
        &["String"],
        "MyInt",
        &[&[r#""07""#], &[r#""-0""#]],
    ),
    (
        "STRING.substr",
        &["String", "Int", "Int"],
        "String",
        &[&[r#""héllo""#, "1", "3"], &[r#""abc""#, "3", "3"]],
    ),
    (
        "STRING.token2string",
        &["Id"],
        "String",
        &[&[r#"#token("x", "Id")"#], &[r#"#token("Foo1", "Id")"#]],
    ),
];

/// The definition of [`FOLDED_HOOK_CASES`]: for each declaration `n`, a function `hk<n>` hooked
/// to its hook and an unhooked function `rt<n>` whose one equation applies `hk<n>` to its
/// variables. The rule for `lits` applies each `hk<n>` to its cases' literals, which the constant
/// fold computes; the rule for `rts` applies each `rt<n>` to the same literals, which only
/// execution evaluates, through the equation.
fn folded_hook_definition() -> String {
    let mut declarations = String::new();
    let (mut literal, mut runtime) = (Vec::new(), Vec::new());
    for (index, (hook, arguments, result, cases)) in FOLDED_HOOK_CASES.iter().enumerate() {
        let sorts = arguments.join(", ");
        let variables = (0..arguments.len())
            .map(|position| format!("X{position}"))
            .collect::<Vec<_>>()
            .join(", ");
        let typed = arguments
            .iter()
            .enumerate()
            .map(|(position, sort)| format!("X{position}:{sort}"))
            .collect::<Vec<_>>()
            .join(", ");
        declarations.push_str(&format!(
            "  syntax {result} ::= hk{index}({sorts}) [function, hook({hook}), symbol(hk{index})]\n\
             \x20 syntax {result} ::= rt{index}({sorts}) [function, symbol(rt{index})]\n\
             \x20 rule rt{index}({typed}) => hk{index}({variables})\n"
        ));
        for case in *cases {
            let case = case.join(", ");
            literal.push(format!("res(hk{index}({case}))"));
            runtime.push(format!("res(rt{index}({case}))"));
        }
    }
    format!(
        r#"
module FOLDED-HOOKS-SYNTAX
  syntax Op ::= "lits" [symbol(lits)] | "rts" [symbol(rts)]
endmodule

module FOLDED-HOOKS
  imports FOLDED-HOOKS-SYNTAX
  imports DOMAINS
  configuration <k> $PGM:Op </k>
  syntax MyInt [hook(INT.Int), token]
  syntax KItem ::= res(K) [symbol(res)]
{declarations}
  rule lits => {}
  rule rts => {}
endmodule
"#,
        literal.join(" ~> "),
        runtime.join(" ~> ")
    )
}

/// A hooked application the frontend folds on literals and the same application evaluated at
/// run time give one value: the fold writes the value the backend's evaluation entry computes,
/// and the emitted token reads back as that value. Every hook the fold evaluates is exercised,
/// and the `lits` rule of the compiled definition keeps none of its hooked applications.
#[test]
fn folded_and_evaluated_applications_agree() {
    let manifest: toml::Value =
        toml::from_str(include_str!("fixtures/hook-capabilities.toml")).unwrap();
    let folded = manifest["implemented"]
        .as_array()
        .unwrap()
        .iter()
        .map(|hook| hook.as_str().unwrap())
        .filter(|hook| matches!(hook.split_once('.'), Some(("BOOL" | "INT" | "STRING", _))))
        .collect::<BTreeSet<_>>();
    let exercised = FOLDED_HOOK_CASES
        .iter()
        .map(|(hook, ..)| *hook)
        .collect::<BTreeSet<_>>();
    assert_eq!(
        exercised, folded,
        "every hook the fold evaluates has cases here"
    );

    let (root, _) = fixture();
    let path = root.join("folded-hooks.k");
    fs::write(&path, folded_hook_definition()).unwrap();
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            path.to_str().unwrap(),
            "--main-module",
            "FOLDED-HOOKS",
            "--output-directory",
        ])
        .arg(&compiled)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    let kore =
        parse_definition(&fs::read_to_string(compiled.join("definition.kore")).unwrap()).unwrap();
    let literal_rule = kore
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| match sentence {
            k_rust::kore::ast::Sentence::Axiom { pattern, .. } => Some(pattern.to_string()),
            _ => None,
        })
        .find(|axiom| axiom.contains("Lbllits{}()") && axiom.contains("Lblres{}("))
        .expect("the rule for lits is emitted");
    assert!(
        !literal_rule.contains("Lblhk"),
        "the fold leaves a hooked application in {literal_rule}"
    );
    let run = |program: &str| {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                "--definition",
                compiled.to_str().unwrap(),
                "--sort",
                "Op",
                "--expression",
                program,
                "--io",
                "off",
            ])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{program}: {stderr}");
        String::from_utf8(output.stdout).unwrap()
    };
    let (literal, runtime) = (run("lits"), run("rts"));
    assert!(literal.contains("Lblres{}("), "{literal}");
    assert_eq!(literal, runtime);
    fs::remove_dir_all(root).unwrap();
}

/// Hooks declared at `Val`, a strict supersort of `Int`, the sort of their values: `INT.add` and
/// `MAP.size`. Their arguments come from the program, so the constant fold leaves them to
/// execution.
const SUBSORT_HOOK_DEFINITION: &str = r#"
module SUBSORT-HOOK-SYNTAX
  imports INT-SYNTAX
  syntax Op ::= tAddV(Int, Int) | tSzV(Int, Int)
endmodule

module SUBSORT-HOOK
  imports SUBSORT-HOOK-SYNTAX
  imports DOMAINS
  configuration <k> $PGM:Op </k>
  syntax Val ::= Int
  syntax KItem ::= res(K) [symbol(res)]
  syntax Val ::= addV(Int, Int) [function, total, hook(INT.add)]
  syntax Val ::= szV(Map) [function, total, hook(MAP.size)]
  rule tAddV(I, J) => res(addV(I, J))
  rule tSzV(I, J) => res(szV(I |-> J))
endmodule
"#;

/// A hook's value at a strict subsort of the declared result sort is its injection into that
/// sort, the one term of the result sort that denotes it, for every hook: `addV(2, 3)` at `Val`
/// is `inj{Int, Val}(5)` and `szV(2 |-> 3)` is `inj{Int, Val}(1)`. In the `K` cell, where `res`
/// injects it into `KItem`, the two injections compose to `inj{Int, KItem}`.
#[test]
fn krun_injects_a_hook_value_of_a_subsort_of_the_declared_sort() {
    let (root, _) = fixture();
    let path = root.join("subsort-hook.k");
    fs::write(&path, SUBSORT_HOOK_DEFINITION).unwrap();
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            path.to_str().unwrap(),
            "--main-module",
            "SUBSORT-HOOK",
            "--output-directory",
        ])
        .arg(&compiled)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    for (program, value) in [("tAddV(2, 3)", "5"), ("tSzV(2, 3)", "1")] {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                "--definition",
                compiled.to_str().unwrap(),
                "--sort",
                "Op",
                "--expression",
                program,
                "--io",
                "off",
            ])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{program}: {stderr}");
        let stdout = String::from_utf8(output.stdout)
            .unwrap()
            .split_whitespace()
            .collect::<String>();
        let expected = format!(
            r#"Lblres{{}}(kseq{{}}(inj{{SortInt{{}},SortKItem{{}}}}(\dv{{SortInt{{}}}}("{value}")),dotk{{}}()))"#
        );
        assert!(
            stdout.contains(&expected),
            "{program}: expected {expected} in {stdout}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

/// A definition over `STRING-BUFFER`, whose appends are nested to the left so that the sentence
/// has one reading whichever `+String` a frontend considers.
const STRING_BUFFER_DEFINITION: &str = r#"
module BUFFER2-SYNTAX
  imports STRING-SYNTAX
  syntax Prog ::= build(String, String, String)
endmodule

module BUFFER2
  imports BUFFER2-SYNTAX
  imports STRING
  imports STRING-BUFFER
  configuration <k> $PGM:Prog </k>
  syntax KItem ::= out(String) | buf(StringBuffer)
  rule build(A, B, C) => buf(((.StringBuffer +String A) +String B) +String C)
  rule buf(SB) => out(StringBuffer2String(SB))
endmodule
"#;

/// `STRING-BUFFER` imports a `[symbolic]` module that defines `StringBuffer` by equations over
/// `String` and a `[concrete]` module that hooks it to a mutable buffer. The Rust backend leaves
/// out `[concrete]` modules, so it compiles the first: an ordinary sort with `String` as a
/// subsort and three unhooked functions, which `krun` evaluates by their equations. Importing the
/// hooked module directly leaves `StringBuffer` undeclared, a user production hooked to
/// `BUFFER.concat` compiles but has no evaluator, and the hooks of the hooked module, which LLVM
/// KORE keeps, have no evaluator in `kore-simplify`.
#[test]
fn krun_runs_string_buffers_through_the_in_k_module() {
    use k_rust::kore::ast::{Attributes, Sentence, Sort};
    const IN_K_SYMBOLS: [&str; 3] = [
        "Lbl'Stop'StringBuffer'Unds'STRING-BUFFER-IN-K'Unds'StringBuffer",
        "Lbl'UndsPlus'String'UndsUnds'STRING-BUFFER-IN-K'Unds'StringBuffer'Unds'StringBuffer'Unds'String",
        "LblStringBuffer2String'LParUndsRParUnds'STRING-BUFFER-IN-K'Unds'String'Unds'StringBuffer",
    ];
    let attribute_names = |attributes: &Attributes| {
        attributes
            .0
            .iter()
            .filter_map(|attribute| match attribute {
                Pattern::Application { symbol, .. } => Some(symbol.name.clone()),
                _ => None,
            })
            .collect::<Vec<_>>()
    };

    let (root, definition) = fixture();
    fs::write(&definition, STRING_BUFFER_DEFINITION).unwrap();
    let compiled = root.join("rust");
    kcompile_for_krun(&definition, &["--main-module", "BUFFER2"], &compiled);
    let kore =
        parse_definition(&fs::read_to_string(compiled.join("definition.kore")).unwrap()).unwrap();
    let sentences = kore
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .collect::<Vec<_>>();
    let string_buffer_sorts = sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::SortDeclaration { hooked, name, .. } if name == "SortStringBuffer" => {
                Some(*hooked)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        string_buffer_sorts,
        [false],
        "SortStringBuffer is declared once, as an ordinary sort"
    );
    assert!(
        sentences.iter().any(|sentence| matches!(
            sentence,
            Sentence::Axiom { attributes, .. } if attributes.0.iter().any(|attribute| matches!(
                attribute,
                Pattern::Application { symbol, .. }
                    if symbol.name == "subsort"
                        && matches!(
                            &symbol.sort_parameters[..],
                            [
                                Sort::Application { name: sub, arguments: sub_arguments },
                                Sort::Application { name: sup, arguments: sup_arguments },
                            ] if sub == "SortString"
                                && sup == "SortStringBuffer"
                                && sub_arguments.is_empty()
                                && sup_arguments.is_empty()
                        )
            ))
        )),
        "the subsort axiom String < StringBuffer is emitted"
    );
    for name in IN_K_SYMBOLS {
        let declarations = sentences
            .iter()
            .filter_map(|sentence| match sentence {
                Sentence::SymbolDeclaration {
                    hooked,
                    symbol,
                    attributes,
                    ..
                } if symbol.name == name => Some((*hooked, attribute_names(attributes))),
                _ => None,
            })
            .collect::<Vec<_>>();
        let [(hooked, attributes)] = &declarations[..] else {
            panic!("{name} is declared once: {declarations:?}");
        };
        assert!(!hooked, "{name} is an ordinary symbol");
        assert!(
            attributes.iter().any(|attribute| attribute == "function")
                && attributes.iter().any(|attribute| attribute == "total")
                && !attributes.iter().any(|attribute| attribute == "hook"),
            "{name} is a total function without a hook: {attributes:?}"
        );
    }
    let run = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["krun", "--definition"])
        .arg(&compiled)
        .args([
            "--sort",
            "Prog",
            "--expression",
            r#"build("ab", "", "cd")"#,
            "--io",
            "off",
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8(run.stdout).unwrap();
    assert!(
        stdout.contains(
            r#"Lblout'LParUndsRParUnds'BUFFER2'Unds'KItem'Unds'String{}(\dv{SortString{}}("abcd"))"#
        ),
        "{stdout}"
    );

    // Importing the [concrete] module directly: it is left out, so StringBuffer is undeclared.
    let hooked_import = root.join("hooked-import.k");
    fs::write(
        &hooked_import,
        STRING_BUFFER_DEFINITION
            .replace("imports STRING-BUFFER\n", "imports STRING-BUFFER-HOOKED\n"),
    )
    .unwrap();
    let refused = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("kcompile")
        .arg(&hooked_import)
        .args(["--main-module", "BUFFER2", "--output-directory"])
        .arg(root.join("hooked"))
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&refused.stderr);
    assert!(!refused.status.success(), "{stderr}");
    assert!(
        stderr.contains("Error[UndefinedSort]: Could not find sorts: [StringBuffer]"),
        "{stderr}"
    );

    // A user production that declares a BUFFER hook compiles, and has no evaluator.
    let user_hook = root.join("user-hook.k");
    fs::write(
        &user_hook,
        r#"
module USER-HOOK
  imports STRING
  syntax Prog ::= go(String, String)
  syntax String ::= myconcat(String, String) [function, total, hook(BUFFER.concat)]
  syntax KItem ::= out(String)
  configuration <k> $PGM:Prog </k>
  rule go(A, B) => out(myconcat(A, B))
endmodule
"#,
    )
    .unwrap();
    let user_compiled = root.join("user");
    kcompile_for_krun(&user_hook, &["--main-module", "USER-HOOK"], &user_compiled);
    let user_run = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["krun", "--definition"])
        .arg(&user_compiled)
        .args([
            "--sort",
            "Prog",
            "--expression",
            r#"go("a", "b")"#,
            "--io",
            "off",
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&user_run.stderr);
    assert!(
        stderr.contains("unsupported hook 'BUFFER.concat' on constructor-like arguments"),
        "{stderr}"
    );

    // LLVM KORE keeps the hooked module; its hooks have no evaluator in the kore-* entry points.
    let llvm = root.join("llvm");
    kcompile_for_krun(
        &definition,
        &["--main-module", "BUFFER2", "--backend", "llvm"],
        &llvm,
    );
    let pattern = root.join("hooked-pattern.kore");
    fs::write(
        &pattern,
        r#"LblStringBuffer2String'LParUndsRParUnds'STRING-BUFFER-HOOKED'Unds'String'Unds'StringBuffer{}(Lbl'UndsPlus'String'UndsUnds'STRING-BUFFER-HOOKED'Unds'StringBuffer'Unds'StringBuffer'Unds'String{}(Lbl'Stop'StringBuffer'Unds'STRING-BUFFER-HOOKED'Unds'StringBuffer{}(), \dv{SortString{}}("ab")))"#,
    )
    .unwrap();
    let simplified = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kore-simplify", "-m", "BUFFER2", "-p"])
        .arg(&pattern)
        .arg(llvm.join("definition.kore"))
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&simplified.stderr);
    assert!(!simplified.status.success(), "{stderr}");
    assert!(
        stderr.contains("unsupported hook 'BUFFER.empty' on constructor-like arguments"),
        "{stderr}"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_reports_an_unsupported_hook_with_a_nonzero_exit() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/hooks");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("hook-boundaries.k").to_str().unwrap(),
            "--main-module",
            "HOOK-BOUNDARIES",
            "--syntax-module",
            "HOOK-BOUNDARIES-SYNTAX",
            "--sort",
            "Pgm",
            fixtures
                .join("unsupported-bytes-memset.hooks")
                .to_str()
                .unwrap(),
            "--depth",
            "10",
        ])
        .output()
        .unwrap();

    assert!(!output.status.success(), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        stderr.contains("unsupported hook 'BYTES.memset'"),
        "{stderr}"
    );
}

const CHOICE_DEFINITION: &str = r#"
module CHOICE-SYNTAX
  imports INT-SYNTAX
  syntax Op ::= mc(Int, Int) | sc(Int) | mempty() | sempty()
endmodule

module CHOICE
  imports CHOICE-SYNTAX
  imports INT
  imports MAP
  imports SET
  configuration <k> $PGM:Op </k>
  syntax KItem ::= res(KItem)
  rule mc(K, V) => res(choice(K |-> V))
  rule sc(E) => res(choice(SetItem(E)))
  rule mempty() => res(choice(.Map))
  rule sempty() => res(choice(.Set))
endmodule
"#;

/// `choice` of a map of one binding is its key, and of a set of one element that element: every
/// key (element) the declaration admits is that one. Of the empty map or set it is undefined, as
/// a partial hook without a value is, so the step that builds it has an undefined result and the
/// run ends in `\bottom`; at the base each was the unsupported-hook error.
#[test]
fn krun_evaluates_choice_of_one_binding() {
    let (root, definition) = fixture();
    fs::write(&definition, CHOICE_DEFINITION).unwrap();
    let compiled = root.join("compiled");
    kcompile_for_krun(&definition, &["--main-module", "CHOICE"], &compiled);
    let run = |program: &str| {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["krun", "--definition"])
            .arg(&compiled)
            .args(["--sort", "Op", "--expression", program, "--io", "off"])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        assert!(output.status.success(), "{program}: {stderr}");
        let stdout = String::from_utf8(output.stdout)
            .unwrap()
            .split_whitespace()
            .collect::<String>();
        (stdout, stderr)
    };
    for (program, key) in [("mc(5, 50)", "5"), ("sc(7)", "7")] {
        let expected = format!(
            r#"Lblres'LParUndsRParUnds'CHOICE'Unds'KItem'Unds'KItem{{}}(inj{{SortInt{{}},SortKItem{{}}}}(\dv{{SortInt{{}}}}("{key}")))"#
        );
        let (stdout, stderr) = run(program);
        assert!(stdout.contains(&expected), "{program}: {stdout}");
        assert!(!stderr.contains("unsupported hook"), "{program}: {stderr}");
    }
    for (program, symbol) in [
        ("mempty()", "LblMap'Coln'choice"),
        ("sempty()", "LblSet'Coln'choice"),
    ] {
        let (stdout, stderr) = run(program);
        assert_eq!(
            stdout, r#"\bottom{SortGeneratedTopCell{}}()"#,
            "{program}: {stderr}"
        );
        assert!(
            stderr.contains("applied with an undefined result") && stderr.contains(symbol),
            "{program}: {stderr}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

/// The one-item value of `choice` is a consequence of the definition, so a proof reads it as an
/// execution does: `choice(K |-> V)` is `K` and `choice(SetItem(X))` is `X` for every `K`, `V`
/// and `X`. The map's value is dropped from the result but not from its definedness: with `f`
/// defined only at 0, `choice(K |-> f(V))` is `K` only where `f(V)` is defined, so the claim is
/// proven under `V ==Int 0` and not without it.
#[test]
fn kprove_reads_choice_of_one_binding_and_keeps_the_definedness_of_its_value() {
    let source = format!(
        "{CHOICE_DEFINITION}
module CHOICE-PARTIAL
  imports CHOICE
  syntax Int ::= f(Int) [function]
  rule f(0) => 1
  syntax Op ::= pc(Int, Int)
  rule pc(K, V) => res(choice(K |-> f(V)))
endmodule

module CHOICE-SPEC
  imports CHOICE-PARTIAL
  claim [one-key]: <k> mc(K:Int, V:Int) => res(K) </k>
  claim [one-element]: <k> sc(X:Int) => res(X) </k>
  claim [partial-value]: <k> pc(K:Int, V:Int) => res(K) </k>
  claim [defined-value]: <k> pc(K:Int, V:Int) => res(K) </k> requires V ==Int 0
endmodule
"
    );
    let (verdicts, output) = order_claim_verdicts(&source, "CHOICE-PARTIAL", "CHOICE-SPEC");
    for claim in ["one-key", "one-element", "defined-value"] {
        assert_eq!(
            claim_verdict(&verdicts, claim, &output),
            "proven",
            "{claim}: {output}"
        );
    }
    assert_ne!(
        claim_verdict(&verdicts, "partial-value", &output),
        "proven",
        "{output}"
    );
}

/// `M1 -Map M2` keeps the bindings of `M1` that `M2` does not hold with the same value: of
/// `1 |-> 10 2 |-> 20 3 |-> 30` without `1 |-> 10 2 |-> 99`, the binding of 1 is removed, that
/// of 2 is kept because `M2` binds 2 to another value, and that of 3 because `M2` does not bind
/// 3. At the base the run halted with the unsupported-hook error on `MAP.difference`.
#[test]
fn krun_evaluates_map_difference_by_binding() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MDIFF-SYNTAX
  imports INT-SYNTAX
  syntax Op ::= "mdiff"
endmodule

module MDIFF
  imports MDIFF-SYNTAX
  imports DOMAINS
  imports COLLECTIONS
  configuration <k> $PGM:Op </k>
  syntax KItem ::= res(K)
  rule mdiff => res((1 |-> 10 2 |-> 20 3 |-> 30) -Map (1 |-> 10 2 |-> 99))
endmodule
"#,
    )
    .unwrap();
    let compiled = root.join("compiled");
    kcompile_for_krun(&definition, &["--main-module", "MDIFF"], &compiled);
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["krun", "--definition"])
        .arg(&compiled)
        .args(["--sort", "Op", "--expression", "mdiff", "--io", "off"])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stderr}");
    assert!(!stderr.contains("unsupported hook"), "{stderr}");
    let stdout = String::from_utf8(output.stdout)
        .unwrap()
        .split_whitespace()
        .collect::<String>();
    let int =
        |value: u32| format!(r#"inj{{SortInt{{}},SortKItem{{}}}}(\dv{{SortInt{{}}}}("{value}"))"#);
    let binding = |key, value| format!("Lbl'UndsPipe'-'-GT-Unds'{{}}({},{})", int(key), int(value));
    let expected = format!(
        "Lblres'LParUndsRParUnds'MDIFF'Unds'KItem'Unds'K{{}}(kseq{{}}(inj{{SortMap{{}},SortKItem{{}}}}(Lbl'Unds'Map'Unds'{{}}({},{})),dotk{{}}()))",
        binding(2, 20),
        binding(3, 30)
    );
    assert!(stdout.contains(&expected), "{stdout}");
    fs::remove_dir_all(root).unwrap();
}

/// `choice` over a map and a set of three Int items, and a fold over a map's values that takes
/// the chosen key's value and removes that key until the map is empty.
const CHOICE_OF_SEVERAL: &str = r#"
module CHOICES
  imports DOMAINS
  imports COLLECTIONS
  syntax Op ::= "mchoice" | "schoice" | "sum"
  configuration <k> $PGM:Op </k>
  syntax KItem ::= res(K)
  rule mchoice => res(choice(3 |-> 30 1 |-> 10 2 |-> 20))
  rule schoice => res(choice(SetItem(3) SetItem(1) SetItem(2)))
  syntax Int ::= sumValues(Map) [function]
  rule sumValues(.Map) => 0
  rule sumValues(M) => {M[choice(M)]}:>Int +Int sumValues(M[choice(M) <- undef]) requires size(M) >Int 0
  rule sum => res(sumValues(1 |-> 10 2 |-> 20 3 |-> 30))
endmodule
"#;

/// `choice` of two or more items reached through a rule `requires` (on 1), a function equation's
/// `requires` (on 2) and a right-hand side (on 0, and `pickr` of a map, `picks` of a set).
/// `f` is `total`: its `owise` equation gives every map a value.
const CHOICE_IN_CONDITIONS: &str = r#"
module CHOICEREQ
  imports DOMAINS
  imports COLLECTIONS
  syntax KItem ::= res(KItem) | cond(Bool) | fres(Int) | pickr(Map) | picks(Set)
  syntax Int ::= f(Map) [function, total]
  rule f(M) => 1 requires choice(M) ==K 1
  rule f(_) => 0 [owise]
  configuration <k> $PGM:Int </k>
  rule 0 => res(choice(1 |-> 10 2 |-> 20))
  rule 1 => cond(true) requires choice(1 |-> 10 2 |-> 20) ==K 1
  rule 2 => fres(f(1 |-> 10 2 |-> 20))
  rule pickr(M) => res(choice(M))
  rule picks(S) => res(choice(S))
endmodule
"#;

/// An execution evaluates `choice` of two or more items as the item the collection's listing
/// (`keys_list`, `Set2List`) puts first, k-rust's documented order: 1 of the keys 3, 1 and 2,
/// and 1 of the set. The fold over a map's values through `choice` sums them whatever the
/// choice. At the base each run halted with the unsupported-hook error on `MAP.choice` or
/// `SET.choice`.
#[test]
fn krun_evaluates_choice_as_the_first_listed_key() {
    for (program, value) in [("mchoice", "1"), ("schoice", "1"), ("sum", "60")] {
        let output = krun_sorted_program(CHOICE_OF_SEVERAL, "CHOICES", "Op", program, &[]);
        assert!(
            output.contains("Lblres") && printed_ints(&output).first() == Some(&value.to_owned()),
            "{program}: {output}"
        );
        assert!(!output.contains("choice"), "{program}: {output}");
    }
}

/// An execution evaluates `choice` also in the conditions it decides: a rule `requires` (on 1)
/// and a function equation's `requires` (on 2), with `krun` and with `krun --search-final`.
#[test]
fn krun_evaluates_choice_in_rule_and_equation_conditions() {
    let cond = Regex::new(r#"Lblcond[^(]*\(\\dv\{SortBool\{\}\}\("true"\)\)"#).unwrap();
    let fres = Regex::new(r#"Lblfres[^(]*\(\\dv\{SortInt\{\}\}\("1"\)\)"#).unwrap();
    for extra in [&[][..], &["--search-final"][..]] {
        let output = krun_int_program(CHOICE_IN_CONDITIONS, "CHOICEREQ", "1", extra);
        assert!(
            cond.is_match(&output) && !output.contains("choice"),
            "{extra:?}: {output}"
        );
        let output = krun_int_program(CHOICE_IN_CONDITIONS, "CHOICEREQ", "2", extra);
        assert!(
            fres.is_match(&output) && !output.contains("choice"),
            "{extra:?}: {output}"
        );
    }
}

/// Which key `choice` gives of a map of two keys, or which element of a set of two elements, is
/// not a consequence of the definition, so no claim that names it is proven or disproved, on a
/// right-hand side or through a rule's or a function equation's `requires`. `choice` of a non-empty map is defined, so no claim fails
/// through an undefined step.
#[test]
fn kprove_proves_no_claim_that_depends_on_choice() {
    let source = format!(
        "{CHOICE_IN_CONDITIONS}
module CHOICEREQ-SPEC
  imports CHOICEREQ
  claim [first-key]: <k> 0 => res(1) </k>
  claim [other-key]: <k> 0 => res(2) </k>
  claim [rule-requires]: <k> 1 => cond(true) </k>
  claim [equation-requires]: <k> 2 => fres(1) </k>
  claim [set-first]: <k> picks(SetItem(1) SetItem(2)) => res(1) </k>
  claim [set-other]: <k> picks(SetItem(1) SetItem(2)) => res(2) </k>
endmodule
"
    );
    let (verdicts, output) = order_claim_verdicts(&source, "CHOICEREQ", "CHOICEREQ-SPEC");
    for claim in [
        "first-key",
        "other-key",
        "rule-requires",
        "equation-requires",
        "set-first",
        "set-other",
    ] {
        assert_undecided(&verdicts, claim, &output);
    }
    // Left unevaluated as a defined value, not as an unsupported hook.
    assert!(
        !output.contains("undefined step") && !output.contains("unsupported hook"),
        "{output}"
    );
}

/// `choice` of a map of two keys (a set of two elements) left unevaluated outside an execution is
/// a defined value, so the step that writes it under `res` has a successor, and the claim that
/// `res` of some item is reached, which constrains the item in no way, is proven. The destination
/// is reachable only through that step.
#[test]
fn kprove_proves_an_order_free_claim_over_choice() {
    let source = format!(
        "{CHOICE_IN_CONDITIONS}
module CHOICE-FREE-SPEC
  imports CHOICEREQ
  claim [some-key]: <k> pickr(1 |-> 10 2 |-> 20) => res(?_K:KItem) </k>
  claim [some-element]: <k> picks(SetItem(1) SetItem(2)) => res(?_K:KItem) </k>
endmodule
"
    );
    let (verdicts, output) = order_claim_verdicts(&source, "CHOICEREQ", "CHOICE-FREE-SPEC");
    for claim in ["some-key", "some-element"] {
        assert_eq!(
            claim_verdict(&verdicts, claim, &output),
            "proven",
            "{claim}: {output}"
        );
    }
    // Left unevaluated as a defined value, not as an unsupported hook.
    assert!(
        !output.contains("undefined step") && !output.contains("unsupported hook"),
        "{output}"
    );
}

#[test]
fn search_without_a_pattern_binds_each_answer_to_var_result() {
    let (root, definition) = branching_search_fixture();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "State",
            "--expression",
            "a",
            "--depth",
            "10",
            "--search-one-step",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        stdout.contains("VarResult:SortGeneratedTopCell{}"),
        "{stdout}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn search_bound_truncation_is_reported_to_the_user() {
    let (root, definition) = branching_search_fixture();
    // Both bounds search one compiled definition.
    let compiled = root.join("compiled");
    kcompile_for_krun(&definition, &["--main-module", "MAIN"], &compiled);
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["krun", "--definition"])
        .arg(&compiled)
        .args([
            "--sort",
            "State",
            "--expression",
            "a",
            "--depth",
            "10",
            "--search-all",
            "--search-bound",
            "1",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        stderr.contains("search stopped at the requested result bound"),
        "{stderr}"
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(!stdout.contains("\\or{"), "{stdout}");

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["krun", "--definition"])
        .arg(&compiled)
        .args([
            "--sort",
            "State",
            "--expression",
            "a",
            "--depth",
            "10",
            "--search-final",
            "--search-bound",
            "2",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(!stderr.contains("result bound"), "{stderr}");
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\\or{"), "{stdout}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn search_bound_stops_a_catch_all_over_an_infinite_result_stream() {
    fn flatten_disjuncts<'a>(pattern: &'a Pattern, disjuncts: &mut Vec<&'a Pattern>) {
        match pattern {
            Pattern::Or { arguments, .. } => {
                for argument in arguments {
                    flatten_disjuncts(argument, disjuncts);
                }
            }
            pattern => disjuncts.push(pattern),
        }
    }

    let definition = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/search-pattern/infinite-result.k");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "INFINITE-RESULT",
            "--syntax-module",
            "INFINITE-RESULT-SYNTAX",
            "--sort",
            "State",
            "--expression",
            "loop(z)",
            "--search-final",
            "--search-bound",
            "5",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        stderr.contains("search stopped at the requested result bound"),
        "{stderr}"
    );
    let result = parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap();
    let mut disjuncts = Vec::new();
    flatten_disjuncts(&result, &mut disjuncts);
    assert_eq!(disjuncts.len(), 5);
    let mut successor_counts = disjuncts
        .iter()
        .map(|disjunct| disjunct.to_string().matches("Lbls{}(").count())
        .collect::<Vec<_>>();
    successor_counts.sort_unstable();
    assert_eq!(successor_counts, [0, 1, 2, 3, 4]);
}

#[test]
fn krun_search_all_prints_disjuncts_in_a_deterministic_order() {
    let definition = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/search/branching-order.k");
    // Both search types search one compiled definition.
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    kcompile_for_krun(
        &definition,
        &["--main-module", "BR", "--syntax-module", "BR-SYNTAX"],
        &compiled,
    );
    let run = |search_type: &str| {
        Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["krun", "--definition"])
            .arg(&compiled)
            .args([
                "--sort",
                "Pgm",
                "--expression",
                "a",
                "--depth",
                "10",
                search_type,
            ])
            .output()
            .unwrap()
    };
    let assert_order = |stdout: &str, labels: &[&str]| {
        let positions = labels
            .iter()
            .map(|label| {
                stdout
                    .find(&format!("Lbl{label}'Unds'BR-SYNTAX'Unds'Pgm"))
                    .unwrap_or_else(|| panic!("missing {label:?} in {stdout}"))
            })
            .collect::<Vec<_>>();
        assert!(
            positions.windows(2).all(|pair| pair[0] < pair[1]),
            "labels {labels:?} were not ordered in {stdout}"
        );
    };

    let all = run("--search-all");
    assert!(
        all.status.success(),
        "{}",
        String::from_utf8_lossy(&all.stderr)
    );
    assert_order(
        &String::from_utf8(all.stdout).unwrap(),
        &["a", "b", "c", "d", "zz"],
    );

    let final_states = run("--search-final");
    assert!(
        final_states.status.success(),
        "{}",
        String::from_utf8_lossy(&final_states.stderr)
    );
    assert_order(
        &String::from_utf8(final_states.stdout).unwrap(),
        &["c", "d", "zz"],
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_search_final_decides_result_predicates_for_ground_overloaded_lists() {
    fn collect_result_bindings(pattern: &Pattern, bindings: &mut Vec<Pattern>) {
        match pattern {
            Pattern::And { arguments, .. } => {
                for argument in arguments {
                    collect_result_bindings(argument, bindings);
                }
            }
            Pattern::Equals { left, right, .. } => {
                let variable = match (left.as_ref(), right.as_ref()) {
                    (Pattern::Variable(variable), _) | (_, Pattern::Variable(variable)) => variable,
                    _ => panic!("unexpected residual constraint in search result: {pattern:#?}"),
                };
                if variable.name == "VarS" {
                    bindings.push(pattern.clone());
                } else {
                    assert!(
                        variable.name.starts_with("Var'Unds'Gen"),
                        "unexpected binding in search result: {pattern:#?}"
                    );
                }
            }
            _ => panic!("unexpected residual constraint in search result: {pattern:#?}"),
        }
    }

    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/search/simple-print");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("test.k").to_str().unwrap(),
            fixtures.join("nondeterministic.pgm").to_str().unwrap(),
            "--main-module",
            "SIMPLE-PRINT",
            "--syntax-module",
            "SIMPLE-PRINT-SYNTAX",
            "--sort",
            "Stmt",
            "--search-final",
            "--pattern",
            r#"<output> ListItem(#ostream(1)) ListItem("off") ListItem(#buffer(S:String)) </output>"#,
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let mut result = parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap();
    let disjuncts = match &mut result {
        Pattern::Or { arguments, .. } => std::mem::take(arguments),
        _ => vec![result],
    };
    let mut actual = Vec::new();
    for disjunct in &disjuncts {
        let before = actual.len();
        collect_result_bindings(disjunct, &mut actual);
        assert_eq!(
            actual.len(),
            before + 1,
            "each disjunct must contain exactly one S binding: {disjunct:#?}"
        );
    }
    actual.sort();

    let mut expected = ["1\\n", "2\\n"]
        .map(|value| {
            parse_pattern(&format!(
                r#"\equals{{SortString{{}}, SortGeneratedTopCell{{}}}}(VarS:SortString{{}}, \dv{{SortString{{}}}}("{value}"))"#
            ))
            .unwrap()
        })
        .to_vec();
    expected.sort();
    assert_eq!(actual, expected);
}

#[test]
fn krun_owise_decides_distinct_ground_overloaded_list_shapes() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/execution/overloaded-list-owise");
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "OVERLOADED-LIST-OWISE",
            "--output-directory",
        ])
        .arg(&compiled)
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );

    for (expression, expected) in [("nil-cons", "2"), ("one-cons", "2"), ("cons-nil", "1")] {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                "--definition",
                compiled.to_str().unwrap(),
                "--sort",
                "Pgm",
                "--expression",
                expression,
                "--depth",
                "20",
                "--strategy",
                "all",
                "--io",
                "off",
                "--pattern",
                "<k> V:Int </k>",
            ])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{expression}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let output = String::from_utf8(output.stdout).unwrap();
        assert!(
            matches!(parse_pattern(&output).unwrap(), Pattern::Equals { .. }),
            "{expression}: {output}"
        );
        assert!(
            output.contains(&format!(r#"\dv{{SortInt{{}}}}("{expected}")"#)),
            "{expression}: {output}"
        );
        assert!(!output.contains(r"\or{"), "{expression}: {output}");
    }

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_search_bound_returns_a_subset_of_the_unbounded_solutions() {
    let definition = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/search/branching-order.k");
    // The bounded and the unbounded search search one compiled definition.
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    kcompile_for_krun(
        &definition,
        &["--main-module", "BR", "--syntax-module", "BR-SYNTAX"],
        &compiled,
    );
    let run = |bound: Option<&str>| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args(["krun", "--definition"]).arg(&compiled).args([
            "--sort",
            "Pgm",
            "--expression",
            "a",
            "--depth",
            "10",
            "--search-all",
        ]);
        if let Some(bound) = bound {
            command.args(["--search-bound", bound]);
        }
        command.output().unwrap()
    };
    let labels = ["a", "b", "c", "d", "zz"];
    let members = |stdout: &str| {
        labels
            .iter()
            .copied()
            .filter(|label| stdout.contains(&format!("Lbl{label}'Unds'BR-SYNTAX'Unds'Pgm")))
            .collect::<BTreeSet<_>>()
    };

    let unbounded = run(None);
    assert!(
        unbounded.status.success(),
        "{}",
        String::from_utf8_lossy(&unbounded.stderr)
    );
    let unbounded = members(&String::from_utf8(unbounded.stdout).unwrap());
    assert_eq!(unbounded, labels.into_iter().collect());

    let bounded = run(Some("2"));
    assert!(
        bounded.status.success(),
        "{}",
        String::from_utf8_lossy(&bounded.stderr)
    );
    let stderr = String::from_utf8(bounded.stderr).unwrap();
    assert!(
        stderr.contains("search stopped at the requested result bound"),
        "{stderr}"
    );
    let bounded = members(&String::from_utf8(bounded.stdout).unwrap());
    assert_eq!(bounded.len(), 2);
    assert!(bounded.is_subset(&unbounded));
    fs::remove_dir_all(root).unwrap();
}

/// Each step of `go(M, L, N)` adds a new variable `?K` to the map and the list, by any of three
/// equal rules, so the states at one depth are renamings of each other: their map entries
/// differ only in the names of their keys, which store in different orders once the
/// request's counter reaches two digits (`!10` before `!3`), while the list fixes which entry
/// is which. Each depth is one state, so the search reports five states, the final one once,
/// and no renaming takes a `--search-bound` slot from another state. A few small states; the
/// debug run takes a few seconds.
#[test]
fn krun_search_reports_renamings_of_one_state_once() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module T
  imports INT
  imports MAP
  imports LIST
  configuration <k> $PGM:KItem </k>
  syntax KItem ::= go(Map, List, Int)
  rule [ra]: <k> go(M, L, N) => go(M (?K:Int |-> 0), L ListItem(?K), N -Int 1) </k> requires N >Int 0
  rule [rb]: <k> go(M, L, N) => go(M (?K:Int |-> 0), L ListItem(?K), N -Int 1) </k> requires N >Int 0
  rule [rc]: <k> go(M, L, N) => go(M (?K:Int |-> 0), L ListItem(?K), N -Int 1) </k> requires N >Int 0
endmodule
"#,
    )
    .unwrap();
    // Both search modes search one compiled definition.
    let compiled = root.join("compiled");
    kcompile_for_krun(
        &definition,
        &["--main-module", "T", "--syntax-module", "T"],
        &compiled,
    );
    let run = |search: &[&str]| {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["krun", "--definition"])
            .arg(&compiled)
            .args(["--sort", "KItem", "--expression", "go(.Map, .List, 4)"])
            .args(search)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8(output.stdout).unwrap();
        // Each result's `<k>` cell is `go(_, _, N) ~> .K`: the counter is the literal before the
        // `go` application closes ahead of `dotk`.
        stdout
            .match_indices("dotk{}()")
            .map(|(end, _)| {
                let before = stdout[..end].trim_end();
                let before = before.strip_suffix(',').unwrap().trim_end();
                let before = before.strip_suffix(')').unwrap().trim_end();
                let before = before.strip_suffix("\")").unwrap();
                before[before.rfind('"').unwrap() + 1..].to_owned()
            })
            .collect::<Vec<_>>()
    };

    assert_eq!(run(&["--search-final"]), ["0"]);
    let mut all = run(&["--search-all"]);
    all.sort();
    assert_eq!(all, ["0", "1", "2", "3", "4"]);

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn undeclared_config_variables_are_rejected_by_name() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  syntax State ::= "a" [symbol(a)]
  configuration <k> $PGM:State </k>
endmodule
"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "State",
            "--expression",
            "a",
            "-cNOPE=1",
        ])
        .output()
        .unwrap();

    assert!(!output.status.success());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("NOPE"), "{stderr}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn search_flag_combinations_are_validated() {
    let (root, definition) = fixture();
    let target = root.join("target.kore");
    fs::write(&target, "Result:SortExp{}").unwrap();
    let cases = [
        (
            "exclusive search modes",
            vec!["--search-all", "--search-one-step"],
            "--search-one-step",
        ),
        (
            "bound requires a mode",
            vec!["--search-bound", "3"],
            "--search-bound",
        ),
        (
            "pattern requires a mode",
            vec!["--search-pattern", target.to_str().unwrap()],
            "--search-pattern",
        ),
    ];

    for (name, extra, expected) in cases {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "krun",
                definition.to_str().unwrap(),
                "--main-module",
                "MAIN",
                "--sort",
                "Exp",
                "--expression",
                "1",
            ])
            .args(extra)
            .output()
            .unwrap();
        assert!(!output.status.success(), "{name} unexpectedly succeeded");
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(stderr.contains(expected), "{name}: {stderr}");
    }

    fs::remove_dir_all(root).unwrap();
}

/// Kore/Parser/Lexer.x:57-58: `@ident = [a-zA-Z][a-zA-Z0-9'\-]*`, set variables prefixed by `@`.
fn is_kore_identifier(name: &str) -> bool {
    let name = name.strip_prefix('@').unwrap_or(name);
    let mut characters = name.chars();
    characters
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic())
        && characters.all(|character| character.is_ascii_alphanumeric() || "'-".contains(character))
}

fn variable_names(pattern: &Pattern, names: &mut Vec<String>) {
    match pattern {
        Pattern::Variable(variable) => names.push(variable.name.clone()),
        Pattern::Exists { variable, body, .. } | Pattern::Forall { variable, body, .. } => {
            names.push(variable.name.clone());
            variable_names(body, names);
        }
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. } => {
            for argument in arguments {
                variable_names(argument, names);
            }
        }
        Pattern::Not { argument, .. } | Pattern::Ceil { argument, .. } => {
            variable_names(argument, names);
        }
        Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. }
        | Pattern::Implies { left, right, .. } => {
            variable_names(left, names);
            variable_names(right, names);
        }
        _ => {}
    }
}

/// Symbolic collection frame narrowing mints `Ex#Frame!0`; the reference prints its own remainder as
/// `VarAC1'Unds'1:SortMap{}` (kore-exec on the same fixture), a plain KORE identifier.
#[test]
fn kore_exec_prints_fresh_remainder_names_as_kore_identifiers() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/matching/map");
    let (root, _) = fixture();
    let compiled = root.join("map-kompiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "TEST",
            "--syntax-module",
            "TEST",
            "--backend",
            "rust",
            "--output-directory",
            compiled.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    let execute = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            compiled.join("definition.kore").to_str().unwrap(),
            "--module",
            "TEST",
            "--pattern",
            fixtures.join("pgm-map.kore").to_str().unwrap(),
            "--depth",
            "1",
        ])
        .output()
        .unwrap();
    assert!(
        execute.status.success(),
        "{}",
        String::from_utf8_lossy(&execute.stderr)
    );
    let output = String::from_utf8(execute.stdout).unwrap();
    let parsed = parse_pattern(&output).unwrap_or_else(|error| panic!("{output}\n{error:?}"));
    let mut names = Vec::new();
    variable_names(&parsed, &mut names);
    names.sort();
    names.dedup();
    assert!(
        names.iter().all(|name| is_kore_identifier(name)),
        "{names:?}"
    );
    assert!(names.contains(&"Ex-hFrame-b0".to_owned()), "{names:?}");
    assert!(names.contains(&"VarM".to_owned()), "{names:?}");
    assert_eq!(parse_pattern(&parsed.to_string()).unwrap(), parsed);

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_exec_runs_a_compiled_definition_and_searches_it() {
    let (root, _) = fixture();
    let definition = root.join("definition.kore");
    let program = root.join("program.kore");
    let target = root.join("target.kore");
    fs::write(
        &definition,
        r#"[]
module MAIN
  sort SortS{} []
  symbol a{}() : SortS{} [constructor{}()]
  symbol b{}() : SortS{} [constructor{}()]
  symbol c{}() : SortS{} [constructor{}()]
  symbol d{}() : SortS{} [constructor{}()]
  symbol e{}() : SortS{} [constructor{}()]
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(a{}(), \top{SortS{}}()),
    b{}()
  ) [label{}("a-to-b")]
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(a{}(), \top{SortS{}}()),
    c{}()
  ) [label{}("a-to-c")]
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(b{}(), \top{SortS{}}()),
    d{}()
  ) [label{}("b-to-d")]
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(c{}(), \top{SortS{}}()),
    e{}()
  ) [label{}("c-to-e")]
endmodule []
"#,
    )
    .unwrap();
    fs::write(&program, "a{}()").unwrap();
    fs::write(&target, "Result:SortS{}").unwrap();

    let execute = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            program.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        execute.status.success(),
        "{}",
        String::from_utf8_lossy(&execute.stderr)
    );
    let execute = String::from_utf8(execute.stdout).unwrap();
    assert!(execute.starts_with(r#"\or{SortS{}}("#), "{execute}");
    assert!(execute.contains("d{}()"), "{execute}");
    assert!(execute.contains("e{}()"), "{execute}");

    let stop_leaves = root.join("stop-leaves.kore");
    let bounded = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            program.to_str().unwrap(),
            "--depth",
            "1",
            "--stop-leaves",
            stop_leaves.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        bounded.status.success(),
        "{}",
        String::from_utf8_lossy(&bounded.stderr)
    );
    let stop_leaves = fs::read_to_string(stop_leaves).unwrap();
    assert!(stop_leaves.contains("b{}()"), "{stop_leaves}");
    assert!(stop_leaves.contains("c{}()"), "{stop_leaves}");
    assert!(!stop_leaves.contains("d{}()"), "{stop_leaves}");
    assert!(!stop_leaves.contains("e{}()"), "{stop_leaves}");

    let result_file = root.join("result.kore");
    let file_output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            program.to_str().unwrap(),
            "--output",
            result_file.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        file_output.status.success(),
        "{}",
        String::from_utf8_lossy(&file_output.stderr)
    );
    assert!(file_output.stdout.is_empty());
    let file_output = fs::read_to_string(result_file).unwrap();
    assert!(file_output.contains("d{}()"), "{file_output}");
    assert!(file_output.contains("e{}()"), "{file_output}");

    let branch = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            program.to_str().unwrap(),
            "--execute-to-branch",
        ])
        .output()
        .unwrap();
    assert!(
        branch.status.success(),
        "{}",
        String::from_utf8_lossy(&branch.stderr)
    );
    assert_eq!(String::from_utf8(branch.stdout).unwrap(), "a{}()\n");

    let any = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            program.to_str().unwrap(),
            "--strategy",
            "any",
        ])
        .output()
        .unwrap();
    assert!(
        any.status.success(),
        "{}",
        String::from_utf8_lossy(&any.stderr)
    );
    // Equal priority: any follows the first applicable rule in definition.kore declaration
    // order, a-to-b before a-to-c, so the single successor chain ends at d.
    assert_eq!(String::from_utf8(any.stdout).unwrap(), "d{}()\n");

    let breadth = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            program.to_str().unwrap(),
            "--breadth",
            "1",
        ])
        .output()
        .unwrap();
    assert!(
        breadth.status.success(),
        "{}",
        String::from_utf8_lossy(&breadth.stderr)
    );
    let breadth = String::from_utf8(breadth.stdout).unwrap();
    assert!(breadth.contains("b{}()"), "{breadth}");
    assert!(breadth.contains("c{}()"), "{breadth}");
    assert!(!breadth.contains("d{}()"), "{breadth}");
    assert!(!breadth.contains("e{}()"), "{breadth}");

    let search = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            program.to_str().unwrap(),
            "--search-final",
            "--search-pattern",
            target.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        search.status.success(),
        "{}",
        String::from_utf8_lossy(&search.stderr)
    );
    let search = String::from_utf8(search.stdout).unwrap();
    assert!(search.contains("Result:SortS{}"), "{search}");
    assert!(search.contains("d{}()"), "{search}");
    assert!(search.contains("e{}()"), "{search}");

    let bounded_search = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            program.to_str().unwrap(),
            "--search-final",
            "--breadth",
            "1",
        ])
        .output()
        .unwrap();
    assert!(!bounded_search.status.success());
    assert!(
        String::from_utf8_lossy(&bounded_search.stderr)
            .contains("the breadth bound was exceeded with 2 states at the frontier"),
        "{}",
        String::from_utf8_lossy(&bounded_search.stderr)
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_exec_executes_every_disjunct_of_the_initial_pattern() {
    let (root, _) = fixture();
    let definition = root.join("disjunctive-definition.kore");
    let program = root.join("disjunctive-program.kore");
    fs::write(
        &definition,
        r#"[]
module MAIN
  sort SortS{} []
  symbol a{}() : SortS{} [constructor{}()]
  symbol b{}() : SortS{} [constructor{}()]
  symbol left{}() : SortS{} [constructor{}()]
  symbol right{}() : SortS{} [constructor{}()]
  axiom{} \rewrites{SortS{}}(\and{SortS{}}(a{}(),\top{SortS{}}()), left{}()) [label{}("left-step")]
  axiom{} \rewrites{SortS{}}(\and{SortS{}}(b{}(),\top{SortS{}}()), right{}()) [label{}("right-step")]
endmodule []
"#,
    )
    .unwrap();
    fs::write(&program, r#"\or{SortS{}}(a{}(), b{}())"#).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            program.to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("left{}()"), "{stdout}");
    assert!(stdout.contains("right{}()"), "{stdout}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_exec_adds_a_rule_module_before_execution() {
    let (root, _) = fixture();
    let definition = root.join("definition.kore");
    let added_module = root.join("new-module.kore");
    let program = root.join("program.kore");
    fs::write(
        &definition,
        r#"[]
module MAIN
  sort SortState{} [hasDomainValues{}()]
  symbol state{}(SortState{}) : SortState{} [function{}(), injective{}(), total{}()]
  axiom{} \rewrites{SortState{}}(
    \and{SortState{}}(state{}(\dv{SortState{}}("a")), \top{SortState{}}()),
    \and{SortState{}}(state{}(\dv{SortState{}}("d")), \top{SortState{}}())
  ) [label{}("MAIN.AD")]
endmodule []
"#,
    )
    .unwrap();
    fs::write(
        &added_module,
        r#"module NEW
  import MAIN []
  axiom{} \rewrites{SortState{}}(
    \and{SortState{}}(state{}(\dv{SortState{}}("d")), \top{SortState{}}()),
    \and{SortState{}}(state{}(\dv{SortState{}}("e")), \top{SortState{}}())
  ) [label{}("NEW.DE")]
  axiom{} \rewrites{SortState{}}(
    \and{SortState{}}(state{}(\dv{SortState{}}("e")), \top{SortState{}}()),
    \and{SortState{}}(state{}(\dv{SortState{}}("f")), \top{SortState{}}())
  ) [label{}("NEW.EF")]
endmodule []"#,
    )
    .unwrap();
    fs::write(&program, r#"state{}(\dv{SortState{}}("a"))"#).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            definition.to_str().unwrap(),
            "--module",
            "NEW",
            "--add-module",
            added_module.to_str().unwrap(),
            "--pattern",
            program.to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "state{}(\\dv{SortState{}}(\"f\"))\n"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_pattern_files_are_verified_before_internalization() {
    // reference: k/result/bin/kore-parser ok.kore --module M --pattern dv.kore --verify
    let root =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/definition");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-exec",
            root.join("ok.kore").to_str().unwrap(),
            "--module",
            "M",
            "--pattern",
            root.join("dv.kore").to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("hasDomainValues"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn kore_get_model_returns_a_typed_substitution() {
    let (root, _) = fixture();
    let definition = root.join("definition.kore");
    let predicate = root.join("predicate.kore");
    fs::write(
        &definition,
        r#"[]
module MAIN
  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
  symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
    [function{}(), total{}(), smt-hook{}("<")]
endmodule []
"#,
    )
    .unwrap();
    fs::write(
        &predicate,
        r#"\equals{SortBool{}, SortBool{}}(
  \dv{SortBool{}}("true"),
  lt{}(X:SortInt{}, \dv{SortInt{}}("5"))
)"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-get-model",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--pattern",
            predicate.to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(output["satisfiable"], "Sat");
    assert_eq!(output["substitution"]["format"], "KORE");
    assert_eq!(output["substitution"]["term"]["tag"], "Equals");
    assert_eq!(output["substitution"]["term"]["first"]["name"], "X");
    assert_eq!(
        output["substitution"]["term"]["second"]["sort"]["name"],
        "SortInt"
    );

    fs::remove_dir_all(root).unwrap();
}

#[cfg(feature = "z3-inference")]
#[test]
fn kore_get_model_reports_unknown_for_approximate_smt_models() {
    let (root, _) = fixture();
    let source = root.join("nat.k");
    fs::write(&source, include_str!("fixtures/kink/model/nat.k")).unwrap();
    let compiled = root.join("nat-kompiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kcompile", source.to_str().unwrap(), "-m", "NATP", "-o"])
        .arg(&compiled)
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );

    for (name, pattern) in [
        ("m1", include_str!("fixtures/kink/model/m1.kore")),
        ("m2", include_str!("fixtures/kink/model/m2.kore")),
    ] {
        let pattern_path = root.join(format!("{name}.kore"));
        fs::write(&pattern_path, pattern).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kore-get-model",
                compiled.join("definition.kore").to_str().unwrap(),
                "--module",
                "NATP",
                "--pattern",
                pattern_path.to_str().unwrap(),
            ])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let answer: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(answer["satisfiable"], "Unknown", "{name}: {answer}");
        assert!(answer.get("substitution").is_none(), "{name}: {answer}");
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_implies_returns_the_matching_condition() {
    let (root, _) = fixture();
    let definition = root.join("definition.kore");
    let antecedent = root.join("antecedent.kore");
    let consequent = root.join("consequent.kore");
    fs::write(
        &definition,
        "[]\nmodule MAIN\n  sort SortK{} []\nendmodule []\n",
    )
    .unwrap();
    fs::write(&antecedent, "X:SortK{}").unwrap();
    fs::write(&consequent, r"\exists{SortK{}}(Z:SortK{}, Z:SortK{})").unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-implies",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--antecedent",
            antecedent.to_str().unwrap(),
            "--consequent",
            consequent.to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(output["status"], "valid");
    assert_eq!(
        output["condition"]["substitution"]["term"]["first"]["name"],
        "X"
    );
    assert_eq!(
        output["condition"]["substitution"]["term"]["second"]["name"],
        "Z"
    );
    assert_eq!(output["condition"]["predicate"]["term"]["tag"], "Top");
    assert_eq!(output["condition"]["witnesses"]["term"]["tag"], "Top");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_implies_decides_bottom_and_top_operands_and_refuses_a_top_antecedent() {
    let (root, _) = fixture();
    let definition = root.join("definition.kore");
    fs::write(
        &definition,
        r#"[]
module MAIN
  sort SortS{} []
  symbol a{}() : SortS{} [constructor{}()]
endmodule []
"#,
    )
    .unwrap();
    let bottom = root.join("bottom.kore");
    let top = root.join("top.kore");
    let regular = root.join("regular.kore");
    fs::write(&bottom, r#"\bottom{SortS{}}()"#).unwrap();
    fs::write(&top, r#"\top{SortS{}}()"#).unwrap();
    fs::write(&regular, "a{}()").unwrap();

    let cases = [
        (&bottom, &bottom, "valid", "Bottom"),
        (&bottom, &top, "valid", "Bottom"),
        (&bottom, &regular, "valid", "Bottom"),
        (&regular, &bottom, "invalid", "Bottom"),
        (&regular, &top, "valid", "Top"),
        (&regular, &regular, "valid", "Top"),
    ];
    for (antecedent, consequent, status, predicate) in cases {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kore-implies",
                definition.to_str().unwrap(),
                "--module",
                "MAIN",
                "--antecedent",
                antecedent.to_str().unwrap(),
                "--consequent",
                consequent.to_str().unwrap(),
            ])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{} => {}: {}",
            antecedent.display(),
            consequent.display(),
            String::from_utf8_lossy(&output.stderr)
        );
        let output: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(output["status"], status, "{output:#}");
        assert_eq!(
            output["condition"]["predicate"]["term"]["tag"], predicate,
            "{output:#}"
        );
        assert_eq!(
            output["condition"]["substitution"]["term"]["tag"], "Top",
            "{output:#}"
        );
        assert_eq!(
            output["condition"]["witnesses"]["term"]["tag"], "Top",
            "{output:#}"
        );
    }

    for consequent in [&bottom, &top, &regular] {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kore-implies",
                definition.to_str().unwrap(),
                "--module",
                "MAIN",
                "--antecedent",
                top.to_str().unwrap(),
                "--consequent",
                consequent.to_str().unwrap(),
            ])
            .output()
            .unwrap();
        assert!(!output.status.success());
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("function-like"),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    fs::remove_dir_all(root).unwrap();
}

/// Disjoint collection collisions make both strict wrappers bottom, whose equality is top.
/// The defined `ok` value therefore cannot imply the different constructor `c(empty)`.
#[test]
fn kore_implies_does_not_refute_equal_bottom_collection_wrappers() {
    let (root, _) = fixture();
    let definition = root.join("definition.kore");
    let antecedent = root.join("antecedent.kore");
    let consequent = root.join("consequent.kore");
    fs::write(
        &definition,
        r#"[]
module MAIN
  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
  hooked-sort SortMap{} [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
  hooked-sort SortSet{} [hook{}("SET.Set"), unit{}(setUnit{}()), element{}(setItem{}()), concat{}(setConcat{}())]
  sort SortR{} []
  hooked-symbol mapUnit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
  hooked-symbol mapItem{}(SortInt{}, SortInt{}) : SortMap{} [function{}(), total{}(), hook{}("MAP.element")]
  hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{} [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}(), unit{}(mapUnit{}())]
  hooked-symbol setUnit{}() : SortSet{} [function{}(), total{}(), hook{}("SET.unit")]
  hooked-symbol setItem{}(SortInt{}) : SortSet{} [function{}(), total{}(), hook{}("SET.element")]
  hooked-symbol setConcat{}(SortSet{}, SortSet{}) : SortSet{} [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), unit{}(setUnit{}())]
  symbol cMap{}(SortMap{}) : SortR{} [constructor{}(), functional{}(), injective{}()]
  symbol dMap{}(SortMap{}) : SortR{} [constructor{}(), functional{}(), injective{}()]
  symbol cSet{}(SortSet{}) : SortR{} [constructor{}(), functional{}(), injective{}()]
  symbol dSet{}(SortSet{}) : SortR{} [constructor{}(), functional{}(), injective{}()]
  symbol ok{}() : SortR{} [constructor{}(), functional{}(), injective{}()]
endmodule []"#,
    )
    .unwrap();
    let check = |left: &str, right: &str| {
        fs::write(&antecedent, left).unwrap();
        fs::write(&consequent, right).unwrap();
        let output = watchdog::output(watchdog::Request::KoreImplies {
            definition: &definition,
            module: "MAIN",
            antecedent: &antecedent,
            consequent: &consequent,
        });
        assert!(
            output.status.success(),
            "{left} => {right}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        serde_json::from_slice::<serde_json::Value>(&output.stdout).unwrap()
    };
    let mut raw_results = Vec::new();
    for (name, kind, collision, singleton) in [
        (
            "map equal values",
            "Map",
            r#"mapConcat{}(mapItem{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("1")), mapItem{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("1")))"#,
            r#"mapItem{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("1"))"#,
        ),
        (
            "map different values",
            "Map",
            r#"mapConcat{}(mapItem{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("1")), mapItem{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("2")))"#,
            r#"mapItem{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("1"))"#,
        ),
        (
            "disjoint set without idem",
            "Set",
            r#"setConcat{}(setItem{}(\dv{SortInt{}}("1")), setItem{}(\dv{SortInt{}}("1")))"#,
            r#"setItem{}(\dv{SortInt{}}("1"))"#,
        ),
    ] {
        let empty = format!("c{kind}{{}}({}Unit{{}}())", kind.to_lowercase());
        let constrained = |collection: &str| {
            format!(
                r"\and{{SortR{{}}}}(ok{{}}(), \equals{{SortR{{}}, SortR{{}}}}(c{kind}{{}}({collection}), d{kind}{{}}({collection})))"
            )
        };
        let raw = check(&constrained(collision), &empty);
        raw_results.push((name, raw["status"].clone()));
        let normalized = check(r"\and{SortR{}}(ok{}(), \top{SortR{}}())", &empty);
        assert_eq!(normalized["status"], "invalid", "{name}: {normalized:#}");
        let vacuous = check(&constrained(singleton), &empty);
        assert_eq!(vacuous["status"], "valid", "{name}: {vacuous:#}");
        let value = format!("c{kind}{{}}({singleton})");
        let reflexive = check(&value, &value);
        assert_eq!(reflexive["status"], "valid", "{name}: {reflexive:#}");
    }
    assert!(
        raw_results
            .iter()
            .all(|(_, status)| status == "unknown" || status == "invalid"),
        "raw collision implications must never be valid: {raw_results:?}"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_implies_rejects_a_syntactic_sort_mismatch_before_internalization() {
    let (root, _) = fixture();
    let definition = root.join("definition.kore");
    let antecedent = root.join("antecedent.kore");
    let consequent = root.join("consequent.kore");
    fs::write(
        &definition,
        "[]\nmodule MAIN\n  sort SortA{} []\n  sort SortB{} []\nendmodule []\n",
    )
    .unwrap();
    fs::write(&antecedent, r#"\bottom{SortA{}}()"#).unwrap();
    fs::write(&consequent, r#"\top{SortB{}}()"#).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-implies",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--antecedent",
            antecedent.to_str().unwrap(),
            "--consequent",
            consequent.to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("antecedent and consequent sorts differ: SortA{} and SortB{}"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_match_disjunction_matches_each_configuration_and_writes_its_result() {
    let (root, _) = fixture();
    let definition = root.join("definition.kore");
    let disjunction = root.join("disjunction.kore");
    let pattern = root.join("pattern.kore");
    let result = root.join("result.kore");
    fs::write(
        &definition,
        r#"[]
module MAIN
  sort SortS{} []
  symbol a{}() : SortS{} [constructor{}()]
  symbol b{}() : SortS{} [constructor{}()]
endmodule []
"#,
    )
    .unwrap();
    fs::write(&disjunction, r#"\or{SortS{}}(a{}(), b{}())"#).unwrap();
    fs::write(&pattern, "Result:SortS{}").unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-match-disjunction",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--disjunction",
            disjunction.to_str().unwrap(),
            "--match",
            pattern.to_str().unwrap(),
            "--output",
            result.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stdout.is_empty());
    let result = fs::read_to_string(result).unwrap();
    assert!(result.starts_with(r#"\or{SortS{}}("#), "{result}");
    assert!(result.contains("Result:SortS{}"), "{result}");
    assert!(result.contains("a{}()"), "{result}");
    assert!(result.contains("b{}()"), "{result}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kore_match_disjunction_verifies_its_disjunction_file() {
    let (root, _) = fixture();
    let definition = root.join("definition.kore");
    let disjunction = root.join("disjunction.kore");
    let pattern = root.join("pattern.kore");
    fs::write(
        &definition,
        r#"[]
module MAIN
  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
  sort SortS{} []
  symbol a{}() : SortS{} [constructor{}()]
  symbol wrap{}(SortInt{}) : SortS{} [constructor{}()]
endmodule []
"#,
    )
    .unwrap();
    // One variable name at two sorts denotes one ill-formed variable, not two variables.
    fs::write(
        &disjunction,
        r#"\or{SortS{}}(a{}(), \and{SortS{}}(wrap{}(X:SortInt{}),
            \equals{SortBool{}, SortS{}}(X:SortBool{}, \dv{SortBool{}}("true"))))"#,
    )
    .unwrap();
    fs::write(&pattern, "a{}()").unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-match-disjunction",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--disjunction",
            disjunction.to_str().unwrap(),
            "--match",
            pattern.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Inconsistent free variable usage: X:SortInt{} and X:SortBool{}."),
        "{stderr}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// A match the backend cannot decide is reported by its reason, stated in words: here the
/// remainder equation between a function application in the target and a constructor in the
/// configuration, printed as KORE.
#[test]
fn kore_match_disjunction_states_an_undecided_match_in_words() {
    let (root, _) = fixture();
    let definition = root.join("definition.kore");
    let disjunction = root.join("disjunction.kore");
    let pattern = root.join("pattern.kore");
    fs::write(
        &definition,
        r#"[]
module MAIN
  sort SortS{} []
  symbol a{}() : SortS{} [constructor{}()]
  symbol f{}(SortS{}) : SortS{} [function{}()]
endmodule []
"#,
    )
    .unwrap();
    fs::write(&disjunction, "a{}()").unwrap();
    fs::write(&pattern, "f{}(X:SortS{})").unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kore-match-disjunction",
            definition.to_str().unwrap(),
            "--module",
            "MAIN",
            "--disjunction",
            disjunction.to_str().unwrap(),
            "--match",
            pattern.to_str().unwrap(),
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.ends_with(
            "KORE pattern match was indeterminate: the match left an undecided remainder:\n\
             f{}(X:SortS{}) = a{}()\n"
        ),
        "{stderr}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// The levels of the configuration [`run_on_a_deep_pattern`] gives the `kore-*` commands.
const DEEP_PATTERN_LEVELS: usize = 100_000;

/// Run `command` (`kore-exec` or `kore-match-disjunction`) with `arguments` naming
/// `{definition}`, `{pattern}` and `{output}`: a definition of `z` and `s`, the configuration
/// `s(...100,000...(z))` and the file the command writes; the command must succeed, and its
/// output file is returned.
fn run_on_a_deep_pattern(command: &str, arguments: &[&str]) -> String {
    let (root, _) = fixture();
    let definition = root.join("definition.kore");
    let pattern = root.join("pattern.kore");
    let result = root.join("result.kore");
    fs::write(
        &definition,
        r#"[]
module MAIN
  sort SortN{} []
  symbol z{}() : SortN{} [constructor{}()]
  symbol s{}(SortN{}) : SortN{} [constructor{}()]
endmodule []
"#,
    )
    .unwrap();
    fs::write(
        &pattern,
        format!(
            "{}z{{}}(){}",
            "s{}(".repeat(DEEP_PATTERN_LEVELS),
            ")".repeat(DEEP_PATTERN_LEVELS)
        ),
    )
    .unwrap();
    let arguments = arguments
        .iter()
        .map(|argument| match *argument {
            "{definition}" => definition.to_str().unwrap(),
            "{pattern}" => pattern.to_str().unwrap(),
            "{output}" => result.to_str().unwrap(),
            argument => argument,
        })
        .collect::<Vec<_>>();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg(command)
        .args(&arguments)
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{command}: {}: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    let result = fs::read_to_string(&result).unwrap();
    fs::remove_dir_all(root).unwrap();
    result
}

/// `kore-exec` reads a KORE pattern file of any depth, and verifies, internalizes, executes and
/// prints it on a stack the backend measures from the pattern: a configuration 100,000 levels
/// deep runs, and `--depth 0` returns it. Its backend passes once ran on a stack sized for the
/// definition alone and overflowed the main thread.
#[test]
fn kore_exec_takes_a_pattern_of_any_depth() {
    let executed = run_on_a_deep_pattern(
        "kore-exec",
        &[
            "{definition}",
            "--module",
            "MAIN",
            "--pattern",
            "{pattern}",
            "--depth",
            "0",
            "--output",
            "{output}",
        ],
    );
    assert_eq!(executed.matches("s{}(").count(), DEEP_PATTERN_LEVELS);
    assert!(executed.contains("z{}()"));
}

/// `kore-match-disjunction` matches a configuration 100,000 levels deep against itself, both read
/// from files, on a stack the backend measures from the two patterns.
#[test]
fn kore_match_disjunction_takes_patterns_of_any_depth() {
    let matched = run_on_a_deep_pattern(
        "kore-match-disjunction",
        &[
            "{definition}",
            "--module",
            "MAIN",
            "--match",
            "{pattern}",
            "--disjunction",
            "{pattern}",
            "--output",
            "{output}",
        ],
    );
    assert_eq!(matched, r"\top{SortN{}}()");
}

/// A hand-written KORE definition for the `kore-*` servers: `a => f(a)`, `b => c`, and the
/// function equation `f(a) = b`, so `a` executes to `c` in two steps through the equation.
fn kore_rpc_definition() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/kore-rpc/definition.kore")
}

#[test]
fn kore_simplify_applies_the_function_equations_of_the_definition() {
    let (root, _) = fixture();
    let simplify = |pattern: &str| {
        let path = root.join("pattern.kore");
        fs::write(&path, pattern).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .arg("kore-simplify")
            .arg(kore_rpc_definition())
            .args(["--module", "MAIN", "--pattern"])
            .arg(&path)
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{pattern}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).unwrap()
    };

    // The equation `f(a) = b` applies; no equation defines `f(c)`, which stays as it is.
    assert_eq!(simplify("f{}(a{}())\n"), "b{}()\n");
    assert_eq!(simplify("f{}(c{}())\n"), "f{}(c{}())\n");
    fs::remove_dir_all(root).unwrap();
}

/// A `kore-rpc` server stopped when the test ends, whether it passes or not.
struct KoreRpcServer(std::process::Child);

impl Drop for KoreRpcServer {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

#[test]
fn kore_rpc_serves_execute_and_simplify_on_an_ephemeral_port() {
    use std::{
        io::{BufRead, BufReader},
        net::TcpStream,
        time::Duration,
    };

    let mut server = KoreRpcServer(
        Command::new(env!("CARGO_BIN_EXE_krust"))
            .arg("kore-rpc")
            .arg(kore_rpc_definition())
            .args(["--module", "MAIN", "--server-port", "0"])
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap(),
    );
    // Port 0 asks the system for a free port; the server announces the address it bound.
    let mut announcement = String::new();
    BufReader::new(server.0.stderr.take().unwrap())
        .read_line(&mut announcement)
        .unwrap();
    let address = announcement
        .strip_prefix("KORE JSON-RPC listening on ")
        .unwrap_or_else(|| panic!("no listening address in {announcement:?}"))
        .trim();
    let port = address.rsplit_once(':').unwrap().1.parse::<u16>().unwrap();
    assert_ne!(port, 0, "{announcement}");

    let stream = TcpStream::connect(address).unwrap();
    stream
        .set_read_timeout(Some(Duration::from_secs(60)))
        .unwrap();
    let mut writer = stream.try_clone().unwrap();
    let mut reader = BufReader::new(stream);
    let mut request = |request: serde_json::Value| {
        writeln!(writer, "{request}").unwrap();
        let mut response = String::new();
        reader.read_line(&mut response).unwrap();
        serde_json::from_str::<serde_json::Value>(&response)
            .unwrap_or_else(|error| panic!("{error}: {response:?}"))
    };
    let constant =
        |name: &str| serde_json::json!({ "tag": "App", "name": name, "sorts": [], "args": [] });
    let state = |term: serde_json::Value| serde_json::json!({ "format": "KORE", "version": 1, "term": term });

    // `a` rewrites to `f(a)`, which the equation simplifies to `b`, which rewrites to `c`.
    let executed = request(serde_json::json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "execute",
        "params": { "state": state(constant("a")) },
    }));
    assert_eq!(executed["id"], 1, "{executed}");
    assert_eq!(executed["result"]["reason"], "stuck", "{executed}");
    assert_eq!(executed["result"]["depth"], 2, "{executed}");
    assert_eq!(
        executed["result"]["state"]["term"]["term"],
        constant("c"),
        "{executed}"
    );

    // A second request on the same connection: the equation `f(a) = b`.
    let simplified = request(serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "simplify",
        "params": {
            "state": state(serde_json::json!({
                "tag": "App", "name": "f", "sorts": [], "args": [constant("a")]
            })),
        },
    }));
    assert_eq!(simplified["id"], 2, "{simplified}");
    assert_eq!(
        simplified["result"]["state"]["term"],
        constant("b"),
        "{simplified}"
    );
    drop(server);
}

/// `pos(X, Y) => yes(X /Int Y) requires X /Int Y >Int 0`, and a specification module `DISJ-SPEC`
/// with one claim `disj` whose left-hand side is the disjunction `left`, under `requires`.
fn disjunctive_claim_source(left: &str, requires: &str) -> String {
    format!(
        r#"
module DEFPROBE
  imports INT
  imports BOOL
  imports BASIC-K
  syntax Res ::= yes(Int) [symbol(yes)] | pos(Int, Int) [symbol(pos)]
  configuration <k> $PGM:Res </k>
  rule [pos]: pos(X, Y) => yes(X /Int Y) requires X /Int Y >Int 0
endmodule
module DISJ-SPEC
  imports DEFPROBE
  claim [disj]: <k> ({left}) => yes(?_) </k> requires {requires}
endmodule
"#
    )
}

/// A claim whose left-hand side is a disjunction holds only if it holds for every disjunct, so
/// `kprove` reports each disjunct and counts, and saves, the claim as proven only when every
/// disjunct is proven in the run. Here `pos(X, 0)` is stuck: its rule's condition `X /Int 0 >Int 0`
/// is undefined. The claim is selected whole by its label.
#[test]
fn kprove_proves_a_disjunctive_claim_only_when_every_disjunct_is_proven() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        disjunctive_claim_source("pos(X, 1) #Or pos(X, 0)", "X >Int 0"),
    )
    .unwrap();
    let compiled = root.join("compiled");
    kcompile_for_proving(&definition, "DISJ-SPEC", "DEFPROBE", &compiled);
    let saved = root.join("proofs.kore");
    for selection in [&[][..], &["--claim", "disj"][..]] {
        let _ = fs::remove_file(&saved);
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["kprove", "--compiled-definition"])
            .arg(&compiled)
            .args(["--main-module", "DISJ-SPEC", "--save-proofs"])
            .arg(&saved)
            .args(selection)
            .output()
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !output.status.success(),
            "{selection:?}: {stdout}\n{stderr}"
        );
        let claims = stdout
            .lines()
            .filter(|line| line.starts_with("claim "))
            .collect::<Vec<_>>();
        assert!(
            matches!(claims.as_slice(), [first, second]
                if first.starts_with("claim DISJ-SPEC.disj (disjunct 1 of 2): proven (")
                    && second.starts_with("claim DISJ-SPEC.disj (disjunct 2 of 2): ")
                    && !second.contains("proven")),
            "{selection:?}: {stdout}\n{stderr}"
        );
        let file = parse_definition(&fs::read_to_string(&saved).unwrap()).unwrap();
        assert!(
            !file.modules[0]
                .sentences
                .iter()
                .any(|sentence| matches!(sentence, k_rust::kore::ast::Sentence::Claim { .. })),
            "{selection:?}: the unproven claim was saved"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

/// A disjunctive claim whose disjuncts are all proven is saved, and a rerun reports each
/// disjunct from the saved proof. A file in an earlier saved-proof format, which may record such
/// a claim after only its first disjunct was proven, is rejected.
#[test]
fn kprove_saves_a_disjunctive_claim_once_every_disjunct_is_proven() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        disjunctive_claim_source("pos(X, 1) #Or pos(X, 2)", "X >Int 3"),
    )
    .unwrap();
    let compiled = root.join("compiled");
    kcompile_for_proving(&definition, "DISJ-SPEC", "DEFPROBE", &compiled);
    let saved = root.join("proofs.kore");
    let kprove = || {
        Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["kprove", "--compiled-definition"])
            .arg(&compiled)
            .args(["--main-module", "DISJ-SPEC", "--save-proofs"])
            .arg(&saved)
            .output()
            .unwrap()
    };
    let first = kprove();
    let stdout = String::from_utf8(first.stdout).unwrap();
    assert!(first.status.success(), "{stdout}");
    let claims = stdout
        .lines()
        .filter(|line| line.starts_with("claim "))
        .collect::<Vec<_>>();
    assert!(
        matches!(claims.as_slice(), [first, second]
            if first.starts_with("claim DISJ-SPEC.disj (disjunct 1 of 2): proven (")
                && second.starts_with("claim DISJ-SPEC.disj (disjunct 2 of 2): proven (")),
        "{stdout}"
    );
    let rerun = kprove();
    let stdout = String::from_utf8(rerun.stdout).unwrap();
    assert!(rerun.status.success(), "{stdout}");
    assert_eq!(
        stdout,
        "claim DISJ-SPEC.disj (disjunct 1 of 2): proven (saved)\n\
         claim DISJ-SPEC.disj (disjunct 2 of 2): proven (saved)\n"
    );

    let mut earlier = parse_definition(&fs::read_to_string(&saved).unwrap()).unwrap();
    earlier.modules[0].attributes =
        k_rust::kore::ast::Attributes(vec![k_rust::kore::ast::Pattern::Application {
            symbol: k_rust::kore::ast::Symbol {
                name: "kRustModalitySafeProofsV1".into(),
                sort_parameters: Vec::new(),
            },
            arguments: Vec::new(),
        }]);
    fs::write(
        &saved,
        k_rust::kore::printer::Printer::pretty(100).print_definition(&earlier),
    )
    .unwrap();
    let rejected = kprove();
    assert!(!rejected.status.success(), "{rejected:?}");
    assert!(
        String::from_utf8_lossy(&rejected.stderr)
            .contains("is in the earlier saved-proof format kRustModalitySafeProofsV1"),
        "{rejected:?}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// The specification `UK-SPEC`: `go(1) => done()` (true), `[mid] s(1) => done()` (true,
/// one-path), in that order or `mid` first, and `go(0) => done()` (false: `go(0)` steps to
/// `s(0)`, which is stuck), compiled for proving, then rewritten as a client writing KORE could:
/// `edit` receives the three claim sentences' attributes in order. Returns the fixture root and
/// the compiled directory.
fn hand_written_claims(
    mid_first: bool,
    edit: impl FnOnce(&mut [&mut k_rust::kore::ast::Attributes]),
) -> (PathBuf, PathBuf) {
    let go_one = "  claim <k> go(1) => done() </k>\n";
    let mid = "  claim [mid]: <k> s(1) => done() </k> [one-path]\n";
    let claims = if mid_first {
        format!("{mid}{go_one}")
    } else {
        format!("{go_one}{mid}")
    };
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module UK
  imports INT
  imports BOOL
  imports BASIC-K
  syntax Res ::= go(Int) [symbol(go)] | s(Int) [symbol(s)] | done() [symbol(done)]
  configuration <k> $PGM:Res </k>
  rule <k> go(X) => s(X) </k>
  rule <k> s(1) => done() </k>
endmodule
module UK-SPEC
  imports UK
CLAIMS  claim <k> go(0) => done() </k>
endmodule
"#
        .replace("CLAIMS", &claims),
    )
    .unwrap();
    let compiled = root.join("compiled");
    kcompile_for_proving(&definition, "UK-SPEC", "UK", &compiled);
    let path = compiled.join("definition.kore");
    let mut kore = parse_definition(&fs::read_to_string(&path).unwrap()).unwrap();
    let mut attributes = kore
        .modules
        .iter_mut()
        .flat_map(|module| module.sentences.iter_mut())
        .filter_map(|sentence| match sentence {
            k_rust::kore::ast::Sentence::Claim { attributes, .. } => Some(attributes),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(attributes.len(), 3);
    edit(&mut attributes);
    fs::write(
        &path,
        k_rust::kore::printer::Printer::pretty(100).print_definition(&kore),
    )
    .unwrap();
    (root, compiled)
}

fn label_attribute(label: &str) -> Pattern {
    parse_pattern(&format!("label{{}}(\"{label}\")")).unwrap()
}

fn kprove_compiled(compiled: &Path, module: &str, extra: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kprove", "--compiled-definition"])
        .arg(compiled)
        .args(["--main-module", module])
        .args(extra)
        .output()
        .unwrap()
}

fn claim_lines(output: &std::process::Output) -> Vec<String> {
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter(|line| line.starts_with("claim "))
        .map(str::to_owned)
        .collect()
}

/// A claim written in KORE may carry no unique id (every such claim then has the backend's id
/// `UNKNOWN`) or another claim's label (the label is the id then), and no origin. Such an id
/// names no single claim, so a proof under it is neither reused nor saved, and two such claims
/// are two claims, never the disjuncts of one: `go(0) => done()` is proven or failed on its own.
#[test]
fn kprove_reuses_and_saves_a_proof_only_under_an_id_that_names_one_claim() {
    let strip = |attributes: &mut [&mut k_rust::kore::ast::Attributes]| {
        attributes[0].0.clear();
        attributes[2].0.clear();
    };
    // Two claims without an id, separated by another claim.
    let (root, compiled) = hand_written_claims(false, strip);
    let saved = root.join("proofs.kore");
    let separated = kprove_compiled(
        &compiled,
        "UK-SPEC",
        &["--save-proofs", saved.to_str().unwrap()],
    );
    let lines = claim_lines(&separated);
    assert!(!separated.status.success(), "{lines:?}");
    assert!(
        lines.len() == 3
            && lines[0].starts_with("claim #1: proven (")
            && lines[1].starts_with("claim UK-SPEC.mid: proven (")
            && lines[2].starts_with("claim #3: ")
            && !lines[2].contains("proven"),
        "{lines:?}"
    );
    fs::remove_dir_all(root).unwrap();

    // The same two claims next to each other are still two claims.
    let (root, compiled) = hand_written_claims(true, |attributes| {
        attributes[1].0.clear();
        attributes[2].0.clear();
    });
    let consecutive = kprove_compiled(&compiled, "UK-SPEC", &[]);
    let lines = claim_lines(&consecutive);
    assert!(
        lines.iter().all(|line| !line.contains("disjunct")),
        "{lines:?}"
    );
    fs::remove_dir_all(root).unwrap();

    // Two claims under one label: the false one is neither reported from the true one's proof
    // nor saved, whatever claims are selected.
    let (root, compiled) = hand_written_claims(false, |attributes| {
        strip(attributes);
        attributes[0].0.push(label_attribute("UK-SPEC.dup"));
        attributes[2].0.push(label_attribute("UK-SPEC.dup"));
    });
    let saved = root.join("proofs.kore");
    for selection in [&[][..], &["--claim", "dup"][..]] {
        let mut arguments = vec!["--save-proofs", saved.to_str().unwrap()];
        arguments.extend(selection);
        let output = kprove_compiled(&compiled, "UK-SPEC", &arguments);
        let lines = claim_lines(&output);
        assert!(!output.status.success(), "{selection:?}: {lines:?}");
        assert!(
            lines
                .iter()
                .all(|line| !line.contains("(saved)") && !line.contains("disjunct")),
            "{selection:?}: {lines:?}"
        );
        let file = parse_definition(&fs::read_to_string(&saved).unwrap()).unwrap();
        assert!(
            !file.modules[0]
                .sentences
                .iter()
                .any(|sentence| matches!(sentence, k_rust::kore::ast::Sentence::Claim { .. })),
            "{selection:?}: a claim was saved"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

/// The claims of one run are proven together, each available to the others' proofs as a
/// circularity. `a: go(0) => done()` is false, but its proof closes by applying the unproven
/// second disjunct `s(0) => done()` of `disj`. A run in which not every claim is proven therefore
/// saves none of its proofs, and says so, so `a` is not reported `proven (saved)` later.
#[test]
fn kprove_saves_no_proof_of_a_run_whose_circularities_are_not_all_proven() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module CIRC
  imports INT
  imports BOOL
  imports BASIC-K
  syntax Res ::= go(Int) [symbol(go)] | s(Int) [symbol(s)] | done() [symbol(done)]
  configuration <k> $PGM:Res </k>
  rule <k> go(X) => s(X) </k>
  rule <k> s(1) => done() </k>
endmodule
module CIRC-SPEC
  imports CIRC
  claim [disj]: <k> (s(1) #Or s(0)) => done() </k>
  claim [a]: <k> go(0) => done() </k>
endmodule
"#,
    )
    .unwrap();
    let compiled = root.join("compiled");
    kcompile_for_proving(&definition, "CIRC-SPEC", "CIRC", &compiled);
    let saved = root.join("proofs.kore");
    let run = kprove_compiled(
        &compiled,
        "CIRC-SPEC",
        &["--save-proofs", saved.to_str().unwrap()],
    );
    assert!(!run.status.success(), "{:?}", claim_lines(&run));
    assert!(
        String::from_utf8_lossy(&run.stderr).contains("are not saved"),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    let file = parse_definition(&fs::read_to_string(&saved).unwrap()).unwrap();
    assert!(
        !file.modules[0]
            .sentences
            .iter()
            .any(|sentence| matches!(sentence, k_rust::kore::ast::Sentence::Claim { .. })),
        "a proof of the run was saved"
    );
    let alone = kprove_compiled(
        &compiled,
        "CIRC-SPEC",
        &["--claim", "a", "--save-proofs", saved.to_str().unwrap()],
    );
    let lines = claim_lines(&alone);
    assert!(!alone.status.success(), "{lines:?}");
    assert!(
        matches!(lines.as_slice(), [line] if line.starts_with("claim CIRC-SPEC.a: ")
            && !line.contains("proven")),
        "{lines:?}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// A saved-proof file is bound to the compiled definition its proofs were made under: changing
/// the semantics so that the claim is false makes the file's proof unused, with a warning, and
/// the claim is proven again (here, disproved).
#[test]
fn kprove_reuses_saved_proofs_only_under_the_definition_they_were_made_under() {
    let source = |rule: &str| {
        format!(
            r#"
module D
  imports INT
  imports BOOL
  imports BASIC-K
  syntax Res ::= go(Int) [symbol(go)] | s(Int) [symbol(s)] | done() [symbol(done)]
  configuration <k> $PGM:Res </k>
  rule <k> {rule} </k>
endmodule
module D-SPEC
  imports D
  claim [p]: <k> go(0) => done() </k>
endmodule
"#
        )
    };
    let (root, definition) = fixture();
    let saved = root.join("proofs.kore");
    fs::write(&definition, source("go(X) => done()")).unwrap();
    let first = root.join("first");
    kcompile_for_proving(&definition, "D-SPEC", "D", &first);
    let proven = kprove_compiled(
        &first,
        "D-SPEC",
        &["--save-proofs", saved.to_str().unwrap()],
    );
    assert!(proven.status.success(), "{:?}", claim_lines(&proven));
    fs::write(&definition, source("go(X) => s(X)")).unwrap();
    let second = root.join("second");
    kcompile_for_proving(&definition, "D-SPEC", "D", &second);
    let changed = kprove_compiled(
        &second,
        "D-SPEC",
        &["--save-proofs", saved.to_str().unwrap()],
    );
    let lines = claim_lines(&changed);
    assert!(!changed.status.success(), "{lines:?}");
    assert!(
        matches!(lines.as_slice(), [line] if !line.contains("proven")),
        "{lines:?}"
    );
    assert!(
        String::from_utf8_lossy(&changed.stderr)
            .contains("written for another compiled definition"),
        "{}",
        String::from_utf8_lossy(&changed.stderr)
    );
    fs::remove_dir_all(root).unwrap();
}

/// Compile `source` (specification module `spec` over `module`) into `root/<name>` and run
/// `kprove` on it with `--save-proofs <root>/proofs.kore` and `arguments`.
fn kprove_saving(
    root: &Path,
    definition: &Path,
    source: &str,
    (spec, module): (&str, &str),
    name: &str,
    arguments: &[&str],
) -> std::process::Output {
    fs::write(definition, source).unwrap();
    let compiled = root.join(name);
    kcompile_for_proving(definition, spec, module, &compiled);
    let saved = root.join("proofs.kore");
    let mut all = vec!["--save-proofs", saved.to_str().unwrap()];
    all.extend_from_slice(arguments);
    kprove_compiled(&compiled, spec, &all)
}

/// A trusted claim is an assumption of every proof of its run, so a saved proof is bound to the
/// claims its run trusted. `t: s(0) => done()` is false, and `a: go(0) => done()` is proven by
/// applying it. Once `t` is no longer trusted (its attribute removed, the claim deleted, or the
/// `--trusted` option dropped), the saved proof of `a` is not reused, and `a` is not proven.
#[test]
fn kprove_reuses_a_saved_proof_only_under_the_claims_its_run_trusted() {
    let source = |t: &str| {
        format!(
            r#"
module T
  imports INT
  imports BOOL
  imports BASIC-K
  syntax Res ::= go(Int) [symbol(go)] | s(Int) [symbol(s)] | done() [symbol(done)]
  configuration <k> $PGM:Res </k>
  rule <k> go(X) => s(X) </k>
  rule <k> s(1) => done() </k>
endmodule
module T-SPEC
  imports T
  {t}
  claim [a]: <k> go(0) => done() </k>
endmodule
"#
        )
    };
    let trusted = source("claim [t]: <k> s(0) => done() </k> [trusted]");
    let untrusted = source("claim [t]: <k> s(0) => done() </k>");
    let deleted = source("");
    let modules = ("T-SPEC", "T");
    for (case, first, first_arguments, second, second_arguments) in [
        (
            "untrusted in source",
            &trusted,
            &[][..],
            &untrusted,
            &["--claim", "a"][..],
        ),
        ("deleted", &trusted, &[][..], &deleted, &[][..]),
        (
            "--trusted dropped",
            &untrusted,
            &["--trusted", "t"][..],
            &untrusted,
            &["--claim", "a"][..],
        ),
    ] {
        let (root, definition) = fixture();
        let run = kprove_saving(&root, &definition, first, modules, "first", first_arguments);
        let lines = claim_lines(&run);
        assert!(run.status.success(), "{case}: {lines:?}");
        assert!(
            lines
                .iter()
                .any(|line| line.starts_with("claim T-SPEC.a: proven (")),
            "{case}: {lines:?}"
        );
        let run = kprove_saving(
            &root,
            &definition,
            second,
            modules,
            "second",
            second_arguments,
        );
        let lines = claim_lines(&run);
        assert!(!run.status.success(), "{case}: {lines:?}");
        assert!(
            lines
                .iter()
                .any(|line| line.starts_with("claim T-SPEC.a: ") && !line.contains("proven")),
            "{case}: {lines:?}"
        );
        assert!(
            String::from_utf8_lossy(&run.stderr).contains("under other assumptions"),
            "{case}: {}",
            String::from_utf8_lossy(&run.stderr)
        );
        fs::remove_dir_all(root).unwrap();
    }
}

/// The SMT prelude's assertions are axioms of the proofs made with it, and `--allow-vacuous`
/// accepts branches that reach no configuration, so a saved proof is bound to both. `p` holds
/// only by the prelude's axiom on `ff`; `c` only by accepting its undefined step (`half(0)`). A
/// rerun without the prelude, or without the option, does not reuse the saved proof.
#[test]
fn kprove_reuses_a_saved_proof_only_under_its_smt_prelude_and_vacuity_policy() {
    let prelude_source = r#"
module PR
  imports INT
  imports BOOL
  imports BASIC-K
  syntax Int ::= f(Int) [function, total, smtlib(ff), no-evaluators, symbol(f)]
  syntax Res ::= go(Int) [symbol(go)] | done() [symbol(done)]
  configuration <k> $PGM:Res </k>
  rule <k> go(X) => done() </k> requires f(X) >Int 0
endmodule
module PR-SPEC
  imports PR
  claim [p]: <k> go(X) => done() </k>
endmodule
"#;
    let (root, definition) = fixture();
    let prelude = root.join("pre.smt2");
    fs::write(&prelude, "(assert (forall ((x Int)) (> (ff x) 0)))\n").unwrap();
    let modules = ("PR-SPEC", "PR");
    let with = kprove_saving(
        &root,
        &definition,
        prelude_source,
        modules,
        "with",
        &["--smt-prelude", prelude.to_str().unwrap()],
    );
    assert!(with.status.success(), "{:?}", claim_lines(&with));
    let without = kprove_saving(&root, &definition, prelude_source, modules, "without", &[]);
    let lines = claim_lines(&without);
    assert!(!without.status.success(), "{lines:?}");
    assert!(
        matches!(lines.as_slice(), [line] if !line.contains("proven")),
        "{lines:?}"
    );
    fs::remove_dir_all(root).unwrap();

    let vacuous_source = r#"
module AV
  imports INT
  imports BOOL
  imports BASIC-K
  syntax Int ::= half(Int) [function, symbol(half)]
  syntax Res ::= h(Int) [symbol(h)] | yes(Int) [symbol(yes)]
  configuration <k> $PGM:Res </k>
  rule half(X) => X /Int 2 requires X >Int 0
  rule <k> h(X) => yes(half(X)) </k>
endmodule
module AV-SPEC
  imports AV
  claim [c]: <k> h(0) => yes(?_) </k>
endmodule
"#;
    let (root, definition) = fixture();
    let modules = ("AV-SPEC", "AV");
    let with = kprove_saving(
        &root,
        &definition,
        vacuous_source,
        modules,
        "with",
        &["--allow-vacuous"],
    );
    assert!(with.status.success(), "{:?}", claim_lines(&with));
    let without = kprove_saving(&root, &definition, vacuous_source, modules, "without", &[]);
    let lines = claim_lines(&without);
    assert!(!without.status.success(), "{lines:?}");
    assert!(
        matches!(lines.as_slice(), [line] if !line.contains("proven")),
        "{lines:?}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// The verdict word of each `claim <spec>.<label>: <word> ...` line of `output`, by label.
fn claim_verdicts(output: &std::process::Output, spec: &str) -> BTreeMap<String, String> {
    claim_lines(output)
        .iter()
        .filter_map(|line| {
            let rest = line.strip_prefix(&format!("claim {spec}."))?;
            let (label, verdict) = rest.split_once(": ")?;
            Some((
                label.to_owned(),
                verdict.split_whitespace().next()?.to_owned(),
            ))
        })
        .collect()
}

/// `kprove` reads a claim's own constraints with their matching-logic meaning
/// (`support/proof_sources.rs`, `DEFPROBE`): `cpos` and `cposctl` exclude their undefined
/// instances and are proven; `cnoteq`, `cnegml` and `cmeq` hold exactly on the stuck `pos(X, 0)`
/// and fail; `crhs`'s destination equality fails where exactly one quotient is undefined.
#[test]
fn kprove_reads_a_claim_condition_with_its_definedness() {
    let (root, definition) = fixture();
    fs::write(&definition, format!("{DEFPROBE}{DEFPROBE_SPEC}")).unwrap();
    let compiled = root.join("compiled");
    kcompile_for_proving(&definition, "DEFPROBE-SPEC", "DEFPROBE", &compiled);
    let run = kprove_compiled(&compiled, "DEFPROBE-SPEC", &["--depth", "8"]);
    assert!(!run.status.success(), "{:?}", claim_lines(&run));
    let verdicts = claim_verdicts(&run, "DEFPROBE-SPEC");
    let expected = [
        ("cdiv", "proven"),
        ("cens", "proven"),
        ("cmeq", "failed"),
        ("cneg", "proven"),
        ("cnegml", "failed"),
        ("cnoteq", "failed"),
        ("cpos", "proven"),
        ("cposctl", "proven"),
        ("crhs", "failed"),
        ("crhsatom", "disproved"),
    ]
    .map(|(label, verdict)| (label.to_owned(), verdict.to_owned()));
    assert_eq!(
        verdicts,
        BTreeMap::from(expected),
        "{:?}",
        claim_lines(&run)
    );
    fs::remove_dir_all(root).unwrap();
}

/// A claim whose constraint has no definedness-explicit form (its definedness depends on the
/// impure `imp()` under an `#if`) is reported `refused` and the run goes on: the claim after it
/// is proven, the exit is nonzero, and the saved-proof file is written. Since the run's claims
/// are circularities of each other's proofs, the file keeps no proof of it.
#[test]
fn kprove_reports_a_refused_claim_and_proves_the_rest() {
    let (root, definition) = fixture();
    fs::write(&definition, format!("{DEFPROBE}{DEFPROBE_REFUSED_SPEC}")).unwrap();
    let compiled = root.join("compiled");
    kcompile_for_proving(&definition, "DEFPROBE-REFUSED-SPEC", "DEFPROBE", &compiled);
    let saved = root.join("proofs.kore");
    let run = kprove_compiled(
        &compiled,
        "DEFPROBE-REFUSED-SPEC",
        &["--save-proofs", saved.to_str().unwrap()],
    );
    let lines = claim_lines(&run);
    assert!(!run.status.success(), "{lines:?}");
    assert!(
        matches!(lines.as_slice(), [refused, proven]
            if refused.starts_with("claim DEFPROBE-REFUSED-SPEC.crefused: refused (")
                && refused.contains("impure")
                && proven.starts_with("claim DEFPROBE-REFUSED-SPEC.cposctl: proven (")),
        "{lines:?}"
    );
    let file = parse_definition(&fs::read_to_string(&saved).unwrap()).unwrap();
    assert!(
        !file.modules[0]
            .sentences
            .iter()
            .any(|sentence| matches!(sentence, k_rust::kore::ast::Sentence::Claim { .. })),
        "a proof of the run was saved"
    );
    assert!(
        String::from_utf8_lossy(&run.stderr).contains("not saved (DEFPROBE-REFUSED-SPEC.cposctl)"),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    // A claim whose meaning cannot be stated is not trusted either.
    let trusted = kprove_compiled(
        &compiled,
        "DEFPROBE-REFUSED-SPEC",
        &["--trusted", "DEFPROBE-REFUSED-SPEC.crefused"],
    );
    let lines = claim_lines(&trusted);
    assert!(!trusted.status.success(), "{lines:?}");
    assert!(
        lines
            .iter()
            .any(|line| line.starts_with("claim DEFPROBE-REFUSED-SPEC.crefused: refused (")),
        "{lines:?}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// Claims written in KORE with an `\equals` that reads a term as a predicate, added to a compiled
/// specification, are each reported `refused`, never proven or disproved; a trusted refused claim
/// is not trusted either, so the run fails.
#[test]
fn kprove_refuses_a_claim_whose_equality_reads_a_term_as_a_predicate() {
    let (root, definition) = fixture();
    fs::write(&definition, format!("{DEFPROBE}{DEFPROBE_SPEC}")).unwrap();
    let compiled = root.join("compiled");
    kcompile_for_proving(&definition, "DEFPROBE-SPEC", "DEFPROBE", &compiled);
    let kore = compiled.join("definition.kore");
    let text = fs::read_to_string(&kore).unwrap();
    let end = text.rfind("endmodule").unwrap();
    fs::write(
        &kore,
        format!(
            "{}{TERM_READ_AS_PREDICATE_CLAIMS}\n{}",
            &text[..end],
            &text[end..]
        ),
    )
    .unwrap();
    for claim in ["HAND.eqtop", "HAND.andterm", "HAND.lhseqtop"] {
        let run = kprove_compiled(&compiled, "DEFPROBE-SPEC", &["--claim", claim]);
        let lines = claim_lines(&run);
        assert!(!run.status.success(), "{claim}: {lines:?}");
        assert!(
            matches!(lines.as_slice(), [line]
                if line.starts_with(&format!("claim {claim}: refused ("))
                    && line.contains("where a predicate is read")),
            "{claim}: {lines:?}"
        );
        let trusted = kprove_compiled(
            &compiled,
            "DEFPROBE-SPEC",
            &["--claim", claim, "--trusted", claim],
        );
        let lines = claim_lines(&trusted);
        assert!(!trusted.status.success(), "{claim} trusted: {lines:?}");
        assert!(
            matches!(lines.as_slice(), [line] if line.starts_with(&format!("claim {claim}: refused ("))),
            "{claim} trusted: {lines:?}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

/// A saved proof certifies its claim under the meaning k-rust gave the claim's KORE when it was
/// made. A file written by a k-rust that decided a claim's constraints as written, which proved
/// `cnoteq` vacuously, carries that k-rust's digest: it is not reused, with the warning, and
/// `cnoteq` is proven again (here, failed) and never `proven (saved)`.
#[test]
fn kprove_does_not_reuse_a_proof_saved_under_the_earlier_claim_reading() {
    use k_rust::backend::proving::{
        ProofAssumptions, SAVED_PROOFS_DEFINITION, saved_proofs_digest_under_reading,
    };
    use k_rust::kore::ast::{KoreString, Sentence};
    let (root, definition) = fixture();
    fs::write(&definition, format!("{DEFPROBE}{DEFPROBE_SPEC}")).unwrap();
    let compiled = root.join("compiled");
    kcompile_for_proving(&definition, "DEFPROBE-SPEC", "DEFPROBE", &compiled);
    let saved = root.join("proofs.kore");
    let first = kprove_compiled(
        &compiled,
        "DEFPROBE-SPEC",
        &["--claim", "cneg", "--save-proofs", saved.to_str().unwrap()],
    );
    assert!(first.status.success(), "{:?}", claim_lines(&first));
    // The file as the earlier k-rust wrote it after proving `cnoteq`: its digest names no claim
    // reading, and it records `cnoteq`.
    let syntax =
        parse_definition(&fs::read_to_string(compiled.join("definition.kore")).unwrap()).unwrap();
    let earlier = saved_proofs_digest_under_reading(
        &syntax,
        "DEFPROBE-SPEC",
        &ProofAssumptions {
            trusted: &BTreeSet::new(),
            smt_prelude: None,
            allow_vacuous: false,
        },
        None,
    );
    let cnoteq = syntax
        .modules
        .iter()
        .find(|module| module.name == "DEFPROBE-SPEC")
        .unwrap()
        .sentences
        .iter()
        .find(|sentence| {
            matches!(sentence, Sentence::Claim { .. })
                && k_rust::kore::printer::Printer::compact()
                    .print_sentence(sentence)
                    .contains("\"DEFPROBE-SPEC.cnoteq\"")
        })
        .unwrap()
        .clone();
    let mut file = parse_definition(&fs::read_to_string(&saved).unwrap()).unwrap();
    let module = &mut file.modules[0];
    module.sentences.push(cnoteq);
    for attribute in &mut module.attributes.0 {
        if let Pattern::Application { symbol, arguments } = attribute
            && symbol.name == SAVED_PROOFS_DEFINITION
        {
            *arguments = vec![Pattern::String(KoreString::from_bytes(earlier.as_bytes()))];
        }
    }
    fs::write(
        &saved,
        k_rust::kore::printer::Printer::pretty(100).print_definition(&file),
    )
    .unwrap();
    let rerun = kprove_compiled(
        &compiled,
        "DEFPROBE-SPEC",
        &[
            "--claim",
            "cnoteq",
            "--save-proofs",
            saved.to_str().unwrap(),
        ],
    );
    let lines = claim_lines(&rerun);
    assert!(!rerun.status.success(), "{lines:?}");
    assert!(
        matches!(lines.as_slice(), [line] if line.starts_with("claim DEFPROBE-SPEC.cnoteq: failed")),
        "{lines:?}"
    );
    assert!(
        String::from_utf8_lossy(&rerun.stderr).contains("read claims otherwise"),
        "{}",
        String::from_utf8_lossy(&rerun.stderr)
    );
    fs::remove_dir_all(root).unwrap();
}

fn modal_claim_fixture() -> (PathBuf, PathBuf, PathBuf) {
    let (root, definition) = fixture();
    let saved_proofs = root.join("proofs.kore");
    fs::write(
        &definition,
        r#"
module MAIN
  syntax State ::= "a" [symbol(a)]
                 | "b" [symbol(b)]
                 | "c" [symbol(c)]
  configuration <k> $PGM:State </k>
  rule <k> a => b </k>
  claim <k> a => b #Or c </k> [label(reaches-b-or-c)]
endmodule
"#,
    )
    .unwrap();
    (root, definition, saved_proofs)
}

#[test]
fn kprove_proves_a_modal_claim_in_process() {
    // Both runs start from source: this test keeps `kprove` of a definition that is its own
    // specification module, and the saved-proof round trip, on the source path.
    let (root, definition, saved_proofs) = modal_claim_fixture();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--claim",
            "reaches-b-or-c",
            "--depth",
            "10",
            "--save-proofs",
            saved_proofs.to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "claim reaches-b-or-c: proven (2 states, 0 unexplored)\n"
    );
    let saved = parse_definition(&fs::read_to_string(&saved_proofs).unwrap()).unwrap();
    assert_eq!(
        saved.modules[0].name,
        "haskell-backend-saved-claims-43943e50-f723-47cd-99fd-07104d664c6d"
    );
    assert_eq!(
        saved.modules[0]
            .sentences
            .iter()
            .filter(|sentence| matches!(sentence, k_rust::kore::ast::Sentence::Claim { .. }))
            .count(),
        1
    );

    let resumed = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--claim",
            "reaches-b-or-c",
            "--save-proofs",
            saved_proofs.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        resumed.status.success(),
        "{}",
        String::from_utf8_lossy(&resumed.stderr)
    );
    assert_eq!(
        String::from_utf8(resumed.stdout).unwrap(),
        "claim reaches-b-or-c: proven (saved)\n"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_reuses_proofs_only_toward_weaker_claim_modality() {
    let source = include_str!("fixtures/claim-modality/dup.k");
    let (root, definition) = fixture();
    let swap_claims = |spec: &str| {
        spec.replace(
            "  claim [one]: <k> a => b </k> [one-path]\n  claim [all]: <k> a => b </k>",
            "  claim [all]: <k> a => b </k>\n  claim [one]: <k> a => b </k> [one-path]",
        )
    };
    let deterministic = |spec: &str| spec.replace("  rule <k> a => c </k>\n", "");
    // Each variant of the specification is compiled once; every proof of it below reads that
    // compilation.
    let compile = |name: &str, spec: String| {
        fs::write(&definition, spec).unwrap();
        let compiled = root.join(name);
        kcompile_for_proving(&definition, "DUP-SPEC", "DUP-SPEC", &compiled);
        compiled
    };
    let nondeterministic_one_first = compile("one-first", source.to_owned());
    let nondeterministic_all_first = compile("all-first", swap_claims(source));
    let deterministic_one_first = compile("deterministic", deterministic(source));
    let deterministic_all_first = compile(
        "deterministic-all-first",
        swap_claims(&deterministic(source)),
    );
    let kprove = |compiled: &Path| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command
            .args(["kprove", "--compiled-definition"])
            .arg(compiled)
            .args(["--main-module", "DUP-SPEC"]);
        command
    };

    for (case, compiled, expected) in [
        (
            "one-first",
            &nondeterministic_one_first,
            [("one", "proven ("), ("all", "disproved (")],
        ),
        (
            "all-first",
            &nondeterministic_all_first,
            [("all", "disproved ("), ("one", "proven (")],
        ),
    ] {
        let output = kprove(compiled).output().unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(!output.status.success(), "{case}: {stdout}");
        let claims = stdout
            .lines()
            .filter(|line| line.starts_with("claim "))
            .collect::<Vec<_>>();
        assert_eq!(claims.len(), 2, "{case}: {stdout}");
        for ((label, verdict), line) in expected.into_iter().zip(claims) {
            assert!(
                line.starts_with(&format!("claim DUP-SPEC.{label}: {verdict}")),
                "{case}: {stdout}"
            );
        }
    }

    // On a deterministic definition the all-path proof can discharge the same one-path body.
    let output = kprove(&deterministic_one_first).output().unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        output.status.success(),
        "{stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(stdout.contains("claim DUP-SPEC.one: proven ("), "{stdout}");
    assert!(stdout.contains("claim DUP-SPEC.all: proven ("), "{stdout}");

    let saved = root.join("proofs.kore");
    let output = kprove(&deterministic_all_first)
        .arg("--save-proofs")
        .arg(&saved)
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        output.status.success(),
        "{stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(stdout.contains("claim DUP-SPEC.all: proven ("), "{stdout}");
    assert!(
        stdout.contains("claim DUP-SPEC.one: proven (saved)"),
        "{stdout}"
    );

    fs::remove_file(&saved).unwrap();
    let selected = |compiled: &Path, label: &str| {
        kprove(compiled)
            .args(["--claim", label, "--save-proofs"])
            .arg(&saved)
            .output()
            .unwrap()
    };
    let one = selected(&nondeterministic_one_first, "one");
    assert!(one.status.success(), "{one:?}");
    let all = selected(&nondeterministic_one_first, "all");
    let stdout = String::from_utf8(all.stdout).unwrap();
    assert!(!all.status.success(), "{stdout}");
    assert!(
        stdout.contains("claim DUP-SPEC.all: disproved ("),
        "{stdout}"
    );

    fs::remove_file(&saved).unwrap();
    let all = selected(&deterministic_one_first, "all");
    assert!(all.status.success(), "{all:?}");
    let one = selected(&deterministic_one_first, "one");
    let stdout = String::from_utf8(one.stdout).unwrap();
    assert!(one.status.success(), "{stdout}");
    assert!(
        stdout.contains("claim DUP-SPEC.one: proven (saved)"),
        "{stdout}"
    );

    let mut legacy = parse_definition(&fs::read_to_string(&saved).unwrap()).unwrap();
    legacy.modules[0].attributes = Default::default();
    fs::write(
        &saved,
        k_rust::kore::printer::Printer::pretty(100).print_definition(&legacy),
    )
    .unwrap();
    let old_file = selected(&deterministic_one_first, "one");
    assert!(!old_file.status.success(), "{old_file:?}");
    assert!(
        String::from_utf8_lossy(&old_file.stderr).contains("carries no saved-proof format marker"),
        "{old_file:?}"
    );

    fs::remove_dir_all(root).unwrap();
}

/// A lower-priority rule is applied to the remainder as simplified, not to the step's subject:
/// the `c` rule does not match `app(N, 0)` but matches the remainder's `c(N)`. The condition
/// comes from another cell, since `app(N, 0)`, which the anywhere equation rewrites for `N > 0`,
/// is not compared by its arguments.
#[test]
fn kprove_selects_lower_priority_rules_for_the_simplified_remainder() {
    for next in ["", "mark() ~>"] {
        let (root, definition) = fixture();
        fs::write(
            &definition,
            ANYWHERE_OVERLOAD_REMAINDER.replace("$NEXT", next),
        )
        .unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kprove",
                definition.to_str().unwrap(),
                "--main-module",
                "OVL-SPEC",
                "--definition-module",
                "OVL",
            ])
            .stdin(std::process::Stdio::null())
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "next item {next:?}: {}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            "claim #1: proven (3 states, 0 unexplored)\n",
            "next item {next:?}"
        );
        fs::remove_dir_all(root).unwrap();
    }
}

/// An anywhere rule identifies `wrap(s(z))` with `wrap(z)`; the rule for `wrap(z)` reaches
/// `bad`, and the `owise` rule `done` (probe `aw.k`).
const ANYWHERE_OWISE_RULE: &str = r#"
module AW-SYNTAX
  syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
  syntax Address ::= wrap(Nat) [symbol(wrap)]
  syntax KItem ::= go(Address) [symbol(go)] | "bad" [symbol(bad)] | "done" [symbol(done)]
endmodule

module AW
  imports AW-SYNTAX
  configuration <k> $PGM:KItem </k>
  rule [collapse]: wrap(s(z)) => wrap(z) [anywhere]
  rule [hit]: <k> go(wrap(z)) => bad </k>
  rule [miss]: <k> go(_) => done </k> [owise]
endmodule

module AW-SPEC
  imports AW
  claim [symbolic]: <k> go(wrap(s(_X:Nat))) => done </k>
  claim [ground]: <k> go(wrap(s(z))) => done </k>
endmodule
"#;

/// The function counterpart of [`ANYWHERE_OWISE_RULE`]: `f(wrap(z)) = 1`, `f(_) = 2` [owise]
/// (probe `awf.k`).
const ANYWHERE_OWISE_EQUATION: &str = r#"
module AWF-SYNTAX
  imports INT-SYNTAX
  syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
  syntax Address ::= wrap(Nat) [symbol(wrap)]
  syntax KItem ::= val(Int) [symbol(val)]
endmodule

module AWF
  imports AWF-SYNTAX
  imports INT
  configuration <k> $PGM:KItem </k>
  syntax Int ::= f(Address) [function, total, symbol(f)]
  rule [collapse]: wrap(s(z)) => wrap(z) [anywhere]
  rule [fhit]: f(wrap(z)) => 1
  rule [fmiss]: f(_) => 2 [owise]
endmodule

module AWF-SPEC
  imports AWF
  claim [symbolic]: <k> val(f(wrap(s(_X:Nat)))) => val(2) </k>
  claim [ground]: <k> val(f(wrap(s(z)))) => val(2) </k>
endmodule
"#;

/// `wrap(s(X))` equals `wrap(z)` at `X = z`, so neither the `owise` rule nor the `owise`
/// equation may fire on it for every `X`: the symbolic claims, false at `X = z`, are not proven.
/// `wrap(s(z)) = wrap(z)` reapplies its own head, so the least fixed point cannot establish
/// totality for `wrap` (Unshown(Cycle)), and `wrap` is a `value-production`. No equation reduces
/// `wrap(z)`, so it is a value and its definedness is that of `z`: the ground counterexample's
/// stuck state carries no `ceil(wrap(z))` obligation, is certified, and the claim is `disproved`.
#[test]
fn kprove_does_not_prove_an_owise_fallback_on_a_symbolic_anywhere_redex() {
    for (source, module) in [
        (ANYWHERE_OWISE_RULE, "AW"),
        (ANYWHERE_OWISE_EQUATION, "AWF"),
    ] {
        let (root, definition) = fixture();
        fs::write(&definition, source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kprove",
                definition.to_str().unwrap(),
                "--main-module",
                &format!("{module}-SPEC"),
                "--definition-module",
                module,
            ])
            .stdin(std::process::Stdio::null())
            .output()
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(!output.status.success(), "{module}: {stdout}");
        let verdict = |claim: &str| {
            let prefix = format!("claim {module}-SPEC.{claim}: ");
            stdout
                .lines()
                .find_map(|line| line.strip_prefix(&prefix))
                .unwrap_or_else(|| panic!("{module}: no {claim} verdict in {stdout}"))
                .split_whitespace()
                .next()
                .unwrap()
                .to_owned()
        };
        assert_ne!(verdict("symbolic"), "proven", "{module}: {stdout}");
        assert_eq!(verdict("ground"), "disproved", "{module}: {stdout}");
        let ground_output = stdout
            .split_once(&format!("claim {module}-SPEC.ground: "))
            .unwrap()
            .1
            .split("\nclaim ")
            .next()
            .unwrap();
        assert!(
            ground_output.contains("stuck (certified) at depth ")
                && !ground_output.contains(r"\ceil{SortAddress{}"),
            "{module}: the ground stuck state is not a certified, obligation-free counterexample \
             in {ground_output}"
        );
        fs::remove_dir_all(root).unwrap();
    }
}

#[test]
fn kprove_claim_condition_over_a_later_binding_is_stated_under_it() {
    for (source, module) in [
        (LATER_BINDING_KEPT, "LEMMAKEPT"),
        (LATER_BINDING_RECOVERED, "LEMMADEF"),
    ] {
        let (root, definition) = fixture();
        fs::write(&definition, source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kprove",
                definition.to_str().unwrap(),
                "--main-module",
                &format!("{module}-SPEC"),
                "--definition-module",
                module,
            ])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        fs::remove_dir_all(root).unwrap();
        assert!(!output.status.success(), "{module}: {stdout}");
        assert!(
            stdout.contains(&format!("claim {module}-SPEC.lemma: proven")),
            "{module}: {stdout}"
        );
        // Apart elements need no disequality, so the false main claim's stuck instance
        // is certifiable without an opaque equality between the constructor applications.
        assert!(
            stdout.contains(&format!("claim {module}-SPEC.main: disproved")),
            "{module}: {stdout}"
        );
        assert!(stdout.contains("stuck (certified)"), "{module}: {stdout}");
    }
}

#[test]
fn kprove_rule_condition_over_a_later_binding_is_stated_under_it() {
    let (root, definition) = fixture();
    fs::write(&definition, LATER_BINDING_RULE).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            definition.to_str().unwrap(),
            "--main-module",
            "RULESOLVED-SPEC",
            "--definition-module",
            "RULESOLVED",
            "--max-counterexamples",
            "5",
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    fs::remove_dir_all(root).unwrap();
    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("RULESOLVED-SPEC.main: failed"), "{stdout}");
    assert!(stdout.contains("Lblbar"), "{stdout}");
    assert!(!stdout.contains("RuleVar"), "{stdout}");
    assert!(!stdout.contains(r"\exists"), "{stdout}");
}

/// `10 /Int A` is undefined at `A = 0`, where the ground claim is disproved, so the symbolic
/// claim is false and must not be proven, whether the division is bound by `#let` or not.
#[test]
fn kprove_keeps_the_definedness_of_a_let_bound_partial_condition() {
    for (case, condition) in [
        ("plain", "10 /Int A <=Int 10 /Int A"),
        (
            "let",
            "(#let Y = A #in 10 /Int Y) <=Int (#let Y = A #in 10 /Int Y)",
        ),
    ] {
        let (root, definition) = fixture();
        fs::write(
            &definition,
            LET_PARTIAL_CONDITION.replace("$CONDITION", condition),
        )
        .unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kprove",
                definition.to_str().unwrap(),
                "--main-module",
                "LETDIV-SPEC",
                "--definition-module",
                "LETDIV",
            ])
            .stdin(std::process::Stdio::null())
            .output()
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(!output.status.success(), "{case}: {stdout}");
        let verdict = |claim: &str| {
            let prefix = format!("claim LETDIV-SPEC.{claim}: ");
            stdout
                .lines()
                .find_map(|line| line.strip_prefix(&prefix))
                .unwrap_or_else(|| panic!("{case}: no {claim} verdict in {stdout}"))
                .split_whitespace()
                .next()
                .unwrap()
                .to_owned()
        };
        assert_ne!(verdict("symbolic"), "proven", "{case}: {stdout}");
        assert_eq!(verdict("ground"), "disproved", "{case}: {stdout}");
        fs::remove_dir_all(root).unwrap();
    }
}

/// `3 ^%Int B 7` is undefined for every negative `B` (no integer is `3 ^Int B`), so `gm(B)` takes
/// the `owise` rule there, and the claim that it reaches `yes` for every negative `B` is false:
/// its instance at `-1` reaches `no`. The solver's own power is a fraction there, whose integer
/// part modulo 7 is 0; the claim must not be proven from that value.
#[test]
fn kprove_proves_nothing_from_a_power_where_no_integer_is_its_value() {
    let (root, definition) = fixture();
    fs::write(&definition, NEGATIVE_POWER).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            definition.to_str().unwrap(),
            "--main-module",
            "NEGPOW-SPEC",
            "--definition-module",
            "NEGPOW",
        ])
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(!output.status.success(), "{stdout}");
    let verdict = |claim: &str| {
        let prefix = format!("claim NEGPOW-SPEC.{claim}: ");
        stdout
            .lines()
            .find_map(|line| line.strip_prefix(&prefix))
            .unwrap_or_else(|| panic!("no {claim} verdict in {stdout}"))
            .split_whitespace()
            .next()
            .unwrap()
            .to_owned()
    };
    assert_ne!(verdict("negative"), "proven", "{stdout}");
    assert_eq!(verdict("minus-one"), "proven", "{stdout}");
    fs::remove_dir_all(root).unwrap();
}

const PARTIAL_HALF: &str = r#"
module HALF
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k>
  syntax Pgm ::= go(Int) | go2(Int)
  syntax KItem ::= "yes" | "no"
  syntax Int ::= half(Int) [function, smt-hook((div #1 2)), symbol(half)]
  rule half(X) => X /Int 2 requires X %Int 2 ==Int 0
  rule <k> go(X) => yes </k> requires half(X) ==Int 0
  rule <k> go(_) => no </k> [owise]
  rule <k> go2(X) => yes </k> requires half(half(X)) ==Int 0
  rule <k> go2(_) => no </k> [owise]
endmodule
module HALF-SPEC
  imports HALF
  claim [symbolic-yes]: <k> go(X) => yes </k> requires 0 <Int X andBool X <Int 2
  claim [concrete-yes]: <k> go(1) => yes </k>
  claim [even-yes]: <k> go(X) => yes </k> requires X ==Int 0
  claim [range-yes]: <k> go(X) => yes </k> requires half(X) <=Int 0 andBool half(X) >=Int 0
  claim [nested-yes]: <k> go2(X) => yes </k> requires 1 <Int X andBool X <Int 3
  claim [nested-range-yes]: <k> go2(X) => yes </k> requires half(half(X)) <=Int 0 andBool half(half(X)) >=Int 0
endmodule
"#;

/// `half` is partial and its equations give it a value only at even arguments, so the
/// definition leaves open whether `half(1)` is defined: `go(1)` reaches `yes` if it is (with
/// value 0) and `no` if it is not. Its `smt-hook` is SMT-LIB's `div`, which has a value at every
/// argument, so the solver reads `half(1) = 0` as true; the claims that `go` reaches `yes` at 1
/// must not be proven from that reading. The definedness of `half(X)` is stated next to the
/// condition `half(X) = 0` and not discharged through it, so the solver decides the condition
/// only under it. At an even argument the equations give the value, and the claim is proven.
/// A claim whose `requires` holds of `half(X)` (`range-yes`) states that `half(X)` is defined,
/// since every symbol is strict, so the claim is proven; at any depth too (`nested-range-yes`,
/// with `half(X)` under the partial `half`), while `go2(2)` (`half(2)` is 1, `half(1)` has no
/// value the definition gives) is not.
#[test]
fn kprove_decides_a_partial_smt_hook_only_under_its_definedness() {
    let (root, definition) = fixture();
    fs::write(&definition, PARTIAL_HALF).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            definition.to_str().unwrap(),
            "--main-module",
            "HALF-SPEC",
            "--definition-module",
            "HALF",
        ])
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(!output.status.success(), "{stdout}");
    let verdict = |claim: &str| {
        let prefix = format!("claim HALF-SPEC.{claim}: ");
        stdout
            .lines()
            .find_map(|line| line.strip_prefix(&prefix))
            .unwrap_or_else(|| panic!("no {claim} verdict in {stdout}"))
            .split_whitespace()
            .next()
            .unwrap()
            .to_owned()
    };
    assert_ne!(verdict("symbolic-yes"), "proven", "{stdout}");
    assert_ne!(verdict("concrete-yes"), "proven", "{stdout}");
    assert_eq!(verdict("even-yes"), "proven", "{stdout}");
    assert_eq!(verdict("range-yes"), "proven", "{stdout}");
    assert_ne!(verdict("nested-yes"), "proven", "{stdout}");
    assert_eq!(verdict("nested-range-yes"), "proven", "{stdout}");
    fs::remove_dir_all(root).unwrap();
}

const APART_COLLECTIONS: &str = r#"
module APART
  imports INT
  imports SET
  imports MAP
  imports K-EQUAL
  syntax Elem ::= a(Int) | b(Int) | p(Int, Int)
  syntax KItem ::= start(Int, Int) | startm(Int, Int) | startp(Int, Int) | same(Int, Int) | chk(Int, Int) | run(Set) | runm(Map) | done()
  configuration <k> $PGM:K </k>
  rule <k> start(A, B) => run(SetItem(a(A)) SetItem(b(B))) ... </k>
  rule <k> startm(A, B) => runm(a(A) |-> 1 b(B) |-> 2) ... </k>
  rule <k> startp(A, B) => run(SetItem(p(A, 1)) SetItem(p(B, 2))) ... </k>
  rule <k> same(A, B) => run(SetItem(a(A)) SetItem(a(B))) ... </k>
  rule <k> chk(A, B) => done() ... </k> requires p(A, 1) =/=K p(B, 2)
  rule <k> run(_) => done() ... </k>
  rule <k> runm(_) => done() ... </k>
endmodule
module APART-SPEC
  imports APART
  claim [set]: <k> start(_A, _B) => done() ... </k>
  claim [map]: <k> startm(_A, _B) => done() ... </k>
  claim [args]: <k> startp(_A, _B) => done() ... </k>
  claim [keq]: <k> chk(_A, _B) => done() ... </k>
  claim [same]: <k> same(_A, _B) => done() ... </k>
endmodule
"#;

#[test]
fn kprove_proves_collections_of_apart_symbolic_elements() {
    let (root, definition) = fixture();
    fs::write(&definition, APART_COLLECTIONS).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            definition.to_str().unwrap(),
            "--main-module",
            "APART-SPEC",
            "--definition-module",
            "APART",
        ])
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    fs::remove_dir_all(root).unwrap();
    let verdict = |claim: &str| {
        let prefix = format!("claim APART-SPEC.{claim}: ");
        stdout
            .lines()
            .find_map(|line| line.strip_prefix(&prefix))
            .unwrap_or_else(|| panic!("no {claim} verdict in {stdout}\n{stderr}"))
            .split_whitespace()
            .next()
            .unwrap()
            .to_owned()
    };
    assert_eq!(
        ["set", "map", "args", "keq"].map(verdict),
        ["proven"; 4],
        "{stdout}\n{stderr}"
    );
    // At equal arguments `same` builds a repeated element, so its set is undefined.
    assert_ne!(verdict("same"), "proven", "{stdout}\n{stderr}");
}

/// `keys_list` of a map whose keys are 10, 2 and the program: domains.md fixes no order of the
/// listing, so a claim about the order is true in some models of the definition and false in
/// others.
const KEYS_LIST_ORDER: &str = r#"
module ORD
  imports DOMAINS
  imports COLLECTIONS
  configuration <k> $PGM:Int </k>
  rule I:Int => keys_list(10 |-> 1 2 |-> 2 I |-> 3)
endmodule
"#;

/// The order `keys_list` lists keys in, reached through a rule `requires` (on 1) and through a
/// function equation's `requires` (on 2); on 0 the listing is the result.
const KEYS_LIST_ORDER_IN_CONDITIONS: &str = r#"
module ORDREQ
  imports DOMAINS
  imports COLLECTIONS
  syntax KItem ::= res(List) | cond(Bool) | fres(Int)
  syntax Int ::= f(Map) [function]
  rule f(M) => 1 requires keys_list(M) ==K ListItem(-1) ListItem(10) ListItem(2)
  rule f(_) => 0 [owise]
  configuration <k> $PGM:Int </k>
  rule 0 => res(keys_list(10 |-> 1 2 |-> 2 -1 |-> 3))
  rule 1 => cond(true) requires keys_list(10 |-> 1 2 |-> 2 -1 |-> 3) ==K ListItem(-1) ListItem(10) ListItem(2)
  rule 2 => fres(f(10 |-> 1 2 |-> 2 -1 |-> 3))
endmodule
"#;

/// `kprove` of `source` with `spec` as the main module and `definition_module` as the definition
/// module: the verdict word of each named claim, by claim name, and the output.
fn order_claim_verdicts(
    source: &str,
    definition_module: &str,
    spec: &str,
) -> (BTreeMap<String, String>, String) {
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            definition.to_str().unwrap(),
            "--main-module",
            spec,
            "--definition-module",
            definition_module,
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    fs::remove_dir_all(root).unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    let prefix = format!("claim {spec}.");
    let verdicts = stdout
        .lines()
        .filter_map(|line| line.strip_prefix(&prefix))
        .filter_map(|line| {
            let (name, rest) = line.split_once(": ")?;
            Some((name.to_owned(), rest.split_whitespace().next()?.to_owned()))
        })
        .collect();
    (verdicts, format!("{stdout}\n{stderr}"))
}

/// The verdict of `claim` among `verdicts`, which must have one.
fn claim_verdict<'a>(verdicts: &'a BTreeMap<String, String>, claim: &str, output: &str) -> &'a str {
    verdicts
        .get(claim)
        .unwrap_or_else(|| panic!("no {claim} verdict in {output}"))
}

/// Neither `proven` nor `disproved`: the definition entails neither the claim nor its failure.
fn assert_undecided(verdicts: &BTreeMap<String, String>, claim: &str, output: &str) {
    let verdict = claim_verdict(verdicts, claim, output);
    assert!(
        verdict != "proven" && verdict != "disproved",
        "{claim} is {verdict}: {output}"
    );
}

/// domains.md leaves the order of `keys_list` open, so neither order of the three keys is a
/// consequence of the definition: no claim about it is proven, and none is disproved.
#[test]
fn kprove_proves_no_claim_that_depends_on_the_order_of_keys_list() {
    let source = format!(
        "{KEYS_LIST_ORDER}
module ORD-SPEC
  imports ORD
  claim [text-order]: <k> -1 => ListItem(-1) ListItem(10) ListItem(2) </k>
  claim [numeric-order]: <k> -1 => ListItem(-1) ListItem(2) ListItem(10) </k>
endmodule
"
    );
    let (verdicts, output) = order_claim_verdicts(&source, "ORD", "ORD-SPEC");
    assert_undecided(&verdicts, "text-order", &output);
    assert_undecided(&verdicts, "numeric-order", &output);
}

/// The order of `keys_list` reached through a rule `requires` (`cond`) and a function equation's
/// `requires` (`fres`) is no more a consequence of the definition than on a right-hand side,
/// while a claim that holds whatever the order (`res`) is proven.
#[test]
fn kprove_proves_no_claim_that_depends_on_the_order_in_conditions() {
    let source = format!(
        "{KEYS_LIST_ORDER_IN_CONDITIONS}
module ORDREQ-SPEC
  imports ORDREQ
  claim [rule-requires]: <k> 1 => cond(true) </k>
  claim [equation-requires]: <k> 2 => fres(1) </k>
  claim [order-free]: <k> 0 => res(?_L:List) </k>
endmodule
"
    );
    let (verdicts, output) = order_claim_verdicts(&source, "ORDREQ", "ORDREQ-SPEC");
    assert_undecided(&verdicts, "rule-requires", &output);
    assert_undecided(&verdicts, "equation-requires", &output);
    assert_eq!(
        claim_verdict(&verdicts, "order-free", &output),
        "proven",
        "{output}"
    );
}

/// `Set2List` fixes no order either: the claim about one order is neither proven nor disproved,
/// and the claim that some list is reached is proven.
#[test]
fn kprove_proves_no_claim_that_depends_on_the_order_of_set2list() {
    let source = r#"
module ORD-SET
  imports DOMAINS
  imports COLLECTIONS
  configuration <k> $PGM:Int </k>
  rule I:Int => Set2List(SetItem(3) SetItem(1) SetItem(I) SetItem(7))
endmodule
module ORD-SET-SPEC
  imports ORD-SET
  claim [one-order]: <k> 0 => ListItem(0) ListItem(1) ListItem(3) ListItem(7) </k>
  claim [order-free]: <k> 0 => ?_L:List </k>
endmodule
"#;
    let (verdicts, output) = order_claim_verdicts(source, "ORD-SET", "ORD-SET-SPEC");
    assert_undecided(&verdicts, "one-order", &output);
    assert_eq!(
        claim_verdict(&verdicts, "order-free", &output),
        "proven",
        "{output}"
    );
}

/// A listing left unevaluated outside an execution is a defined value: `keys_list` of a map with
/// distinct keys is defined, so the step that writes it has a successor, and the claim that some
/// list is reached is proven, with no undefined step.
#[test]
fn kprove_proves_an_order_free_claim_over_keys_list() {
    let source = format!(
        "{KEYS_LIST_ORDER}
module ORD-FREE-SPEC
  imports ORD
  claim [some-list]: <k> -1 => ?_L:List </k>
endmodule
"
    );
    let (verdicts, output) = order_claim_verdicts(&source, "ORD", "ORD-FREE-SPEC");
    assert_eq!(
        claim_verdict(&verdicts, "some-list", &output),
        "proven",
        "{output}"
    );
    assert!(!output.contains("undefined step"), "{output}");
}

/// A listing left unevaluated over a map whose keys are constructor-like but whose values are
/// symbolic is defined exactly when the map is: the map binds distinct keys, so it is defined
/// when its values are, and then it has a listing. A claim that some list is reached is proven
/// over such a map (`k-free`, `v-free`), a claim about one order is not (`k-order`, `v-order`),
/// and a map holding a value undefined at some instance (`10 /Int X` at `X = 0`) still leaves
/// its step undefined there (`z-free`): that value's obligation is what remains, so the claim
/// that excludes the instance is proven (`z-guarded`).
#[test]
fn kprove_takes_a_listing_of_a_map_with_symbolic_values_as_defined_as_the_map() {
    let source = r#"
module SYMV
  imports DOMAINS
  imports COLLECTIONS
  syntax KItem ::= run(Int) | runv(Int) | runz(Int) | done(List)
  configuration <k> $PGM:K </k>
  rule run(X) => done(keys_list(1 |-> X 2 |-> 3))
  rule runv(X) => done(values(1 |-> X 2 |-> 3))
  rule runz(X) => done(keys_list(1 |-> 10 /Int X 2 |-> 3))
endmodule
module SYMV-SPEC
  imports SYMV
  claim [k-order]: <k> run(_X:Int) => done(ListItem(1) ListItem(2)) </k>
  claim [k-free]: <k> run(_X:Int) => done(?_L:List) </k>
  claim [v-order]: <k> runv(X:Int) => done(ListItem(X) ListItem(3)) </k>
  claim [v-free]: <k> runv(_X:Int) => done(?_L:List) </k>
  claim [z-free]: <k> runz(_X:Int) => done(?_L:List) </k>
  claim [z-guarded]: <k> runz(X:Int) => done(?_L:List) </k> requires X =/=Int 0
endmodule
"#;
    let (verdicts, output) = order_claim_verdicts(source, "SYMV", "SYMV-SPEC");
    for claim in ["k-free", "v-free", "z-guarded"] {
        assert_eq!(
            claim_verdict(&verdicts, claim, &output),
            "proven",
            "{claim}: {output}"
        );
    }
    for claim in ["k-order", "v-order"] {
        assert_undecided(&verdicts, claim, &output);
    }
    assert_ne!(
        claim_verdict(&verdicts, "z-free", &output),
        "proven",
        "{output}"
    );
}

/// The expected loss of leaving a listing unevaluated: its size is 3 in every model, but `size`
/// of the unevaluated listing is not computed, so the claim that states it is not proven. A
/// change that decides `LIST.size` of such a listing flips the second verdict to `proven`.
#[test]
fn kprove_loses_the_size_of_a_gated_listing() {
    let source = format!(
        "{KEYS_LIST_ORDER}
module ORD-FREE-SPEC
  imports ORD
  claim [some-list]: <k> -1 => ?_L:List </k>
  claim [three-keys]: <k> -1 => ?L:List </k> ensures size(?L) ==Int 3
endmodule
"
    );
    let (verdicts, output) = order_claim_verdicts(&source, "ORD", "ORD-FREE-SPEC");
    assert_eq!(
        claim_verdict(&verdicts, "some-list", &output),
        "proven",
        "{output}"
    );
    assert_ne!(
        claim_verdict(&verdicts, "three-keys", &output),
        "proven",
        "{output}"
    );
}

/// `krun` of `source` (main and syntax module `main`, `$PGM` of sort Int) on `program`, with the
/// `extra` arguments: the printed result.
fn krun_int_program(source: &str, main: &str, program: &str, extra: &[&str]) -> String {
    krun_sorted_program(source, main, "Int", program, extra)
}

/// `krun` of `source` (main and syntax module `main`, `$PGM` of sort `sort`) on `program`, with
/// the `extra` arguments: the printed result.
fn krun_sorted_program(
    source: &str,
    main: &str,
    sort: &str,
    program: &str,
    extra: &[&str],
) -> String {
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["krun", definition.to_str().unwrap()])
        .args(["--main-module", main, "--syntax-module", main])
        .args(["--sort", sort, "--expression", program, "--io", "off"])
        .args(extra)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    fs::remove_dir_all(root).unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        output.status.success(),
        "{stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    stdout
}

/// The Int domain values of `output`, in the order they are printed.
fn printed_ints(output: &str) -> Vec<String> {
    Regex::new(r#"\\dv\{SortInt\{\}\}\("(-?[0-9]+)"\)"#)
        .unwrap()
        .captures_iter(output)
        .map(|found| found[1].to_owned())
        .collect()
}

/// An execution lists the keys of a map in k-rust's documented order, the decimal text order
/// for Int keys: -1, 10, 2.
#[test]
fn krun_lists_keys_in_the_documented_order() {
    let output = krun_int_program(KEYS_LIST_ORDER, "ORD", "-1", &[]);
    assert!(
        printed_ints(&output).starts_with(&["-1".into(), "10".into(), "2".into()]),
        "{output}"
    );
}

/// An execution evaluates every listing in its documented order, also in the conditions it
/// decides: a rule `requires` (on 1) and a function equation's `requires` (on 2), with `krun` and
/// with `krun --search-final`.
#[test]
fn krun_keeps_the_order_in_rule_and_equation_conditions() {
    let cond = Regex::new(r#"Lblcond[^(]*\(\\dv\{SortBool\{\}\}\("true"\)\)"#).unwrap();
    let fres = Regex::new(r#"Lblfres[^(]*\(\\dv\{SortInt\{\}\}\("1"\)\)"#).unwrap();
    let source = KEYS_LIST_ORDER_IN_CONDITIONS;
    let listed = krun_int_program(source, "ORDREQ", "0", &[]);
    assert!(
        listed.contains("Lblres")
            && printed_ints(&listed).starts_with(&["-1".into(), "10".into(), "2".into()]),
        "{listed}"
    );
    for extra in [&[][..], &["--search-final"][..]] {
        // The condition is decided, not carried as a constraint on the result.
        let output = krun_int_program(source, "ORDREQ", "1", extra);
        assert!(
            cond.is_match(&output) && !output.contains("Lblkeys"),
            "{extra:?}: {output}"
        );
        let output = krun_int_program(source, "ORDREQ", "2", extra);
        assert!(
            fres.is_match(&output) && !output.contains("Lblkeys"),
            "{extra:?}: {output}"
        );
    }
}

/// Float operations over a binary32 and a binary64 operand, whose result format domains.md does
/// not name: as a result (`div`), under `precisionFloat` (`fmt`), and in complementary rule
/// conditions (`pick`).
const MIXED_FLOAT_FORMATS: &str = r#"
module MIXED
  imports DOMAINS
  imports FLOAT
  syntax Pgm ::= div(Float, Float) | fmt(Float, Float) | pick(Float, Float)
  configuration <k> $PGM:Pgm </k>
  rule div(X, Y) => X /Float Y
  rule fmt(X, Y) => precisionFloat(X +Float Y)
  rule pick(X, Y) => true requires X /Float Y >Float 0.0
  rule pick(X, Y) => false requires notBool (X /Float Y >Float 0.0)
endmodule
"#;

/// An execution rounds a Float operation over a binary32 and a binary64 operand to binary64, the
/// operand format that contains the other, also where a rule condition reads it, with `krun` and
/// with `krun --search-final`.
#[test]
fn krun_rounds_float_arithmetic_over_two_formats_to_the_wider_format() {
    let source = MIXED_FLOAT_FORMATS;
    let output = krun_sorted_program(source, "MIXED", "Pgm", "div(0.1f, 2.0)", &[]);
    assert!(
        output.contains(r#"\dv{SortFloat{}}("5.0000000745058060e-02p53x11")"#),
        "{output}"
    );
    for extra in [&[][..], &["--search-final"][..]] {
        let output = krun_sorted_program(source, "MIXED", "Pgm", "pick(1.0f, 2.0)", extra);
        assert!(
            output.contains(r#"\dv{SortBool{}}("true")"#)
                && !output.contains(r#"\dv{SortBool{}}("false")"#)
                && !output.contains("Lblpick"),
            "{extra:?}: {output}"
        );
    }
}

/// The definition does not fix the format of a Float operation's result over a binary32 and a
/// binary64 operand: a model of it may round to either, so a claim about the result's value or
/// format is neither proven nor disproved.
#[test]
fn kprove_proves_no_claim_that_depends_on_the_format_of_a_mixed_result() {
    let source = format!(
        "{MIXED_FLOAT_FORMATS}
module MIXED-SPEC
  imports MIXED
  claim [value]: <k> div(0.1f, 2.0) => 5.0000000745058060e-02p53x11 </k>
  claim [format]: <k> fmt(0.1f, 0.2) => 53 </k>
endmodule
"
    );
    let (verdicts, output) = order_claim_verdicts(&source, "MIXED", "MIXED-SPEC");
    assert_undecided(&verdicts, "value", &output);
    assert_undecided(&verdicts, "format", &output);
}

/// `signFloat` of a value read from the program (`sg`) and of a NaN constant the frontend would
/// fold (`nanc`).
const NAN_SIGN: &str = r#"
module NANSIGN
  imports DOMAINS
  imports FLOAT
  syntax Pgm ::= sg(Float) | nanc() | r(Bool)
  configuration <k> $PGM:Pgm </k>
  rule sg(X) => r(signFloat(X))
  rule nanc() => r(signFloat(NaN))
endmodule
"#;

/// domains.md gives the `NaN` literal no sign bit, so a model of the definition may give
/// `signFloat` of a NaN either value: no claim about it is proven or disproved, in binary64, in a
/// format the backend does not compute, or as a constant in a rule; that it is some Bool is
/// proven, and the sign of `-0.0` is still proven. An execution answers `false`.
#[test]
fn kprove_proves_no_claim_that_depends_on_the_sign_of_a_nan() {
    let source = format!(
        "{NAN_SIGN}
module NANSIGN-SPEC
  imports NANSIGN
  claim [nan-false]: <k> sg(NaN) => r(false) </k>
  claim [nan-true]: <k> sg(NaN) => r(true) </k>
  claim [wide-nan-false]: <k> sg(NaNp113x15) => r(false) </k>
  claim [constant-nan-false]: <k> nanc() => r(false) </k>
  claim [nan-some]: <k> sg(NaN) => r(?_B:Bool) </k>
  claim [negative-zero]: <k> sg(-0.0) => r(true) </k>
endmodule
"
    );
    let (verdicts, output) = order_claim_verdicts(&source, "NANSIGN", "NANSIGN-SPEC");
    for claim in [
        "nan-false",
        "nan-true",
        "wide-nan-false",
        "constant-nan-false",
    ] {
        assert_undecided(&verdicts, claim, &output);
    }
    for claim in ["nan-some", "negative-zero"] {
        assert_eq!(
            claim_verdict(&verdicts, claim, &output),
            "proven",
            "{claim}: {output}"
        );
    }
    for program in ["sg(NaN)", "sg(NaNp113x15)", "nanc()"] {
        let output = krun_sorted_program(NAN_SIGN, "NANSIGN", "Pgm", program, &[]);
        assert!(
            output.contains(r#"\dv{SortBool{}}("false")"#) && !output.contains("LblsignFloat"),
            "{program}: {output}"
        );
    }
}

/// A Float operation over a binary32 and a binary64 operand is defined whatever format its result
/// takes, so the claim that some Float is reached is proven, with no undefined step; an operation
/// over one format is evaluated in a proof as in an execution.
#[test]
fn kprove_proves_a_format_free_claim_over_a_mixed_result() {
    let source = format!(
        "{MIXED_FLOAT_FORMATS}
module MIXED-SPEC
  imports MIXED
  claim [some-float]: <k> div(0.1f, 2.0) => ?_F:Float </k>
  claim [one-format]: <k> div(0.1f, 2.0f) => 5.00000007e-02p24x8 </k>
endmodule
"
    );
    let (verdicts, output) = order_claim_verdicts(&source, "MIXED", "MIXED-SPEC");
    for claim in ["some-float", "one-format"] {
        assert_eq!(
            claim_verdict(&verdicts, claim, &output),
            "proven",
            "{claim}: {output}"
        );
    }
    assert!(!output.contains("undefined step"), "{output}");
}

/// The modal claim fixture prepared once with `kcompile --for-proving`, so that a `kprove`
/// child loads the compiled KORE instead of compiling the definition and its prelude.
/// Functions hooked `MINT.integer` at `MInt{Foo}`, a machine-integer sort that names no width:
/// a user function declared without `total` (`partial`), one declared `total` (`declared`), and
/// the prelude's `Int2MInt`, which is `total` (`prelude`).
const WIDTHLESS_MINT: &str = r#"
module WIDTHLESS
  imports INT
  imports MINT
  syntax Foo
  syntax MInt{Foo} ::= partialWord(Int) [function, hook(MINT.integer)]
                     | totalWord(Int) [function, total, hook(MINT.integer)]
  syntax Pgm ::= partial(Int) | declared(Int) | prelude(Int) | word(MInt{Foo})
  configuration <k> $PGM:Pgm </k>
  rule partial(I) => word(partialWord(I))
  rule declared(I) => word(totalWord(I))
  rule prelude(I) => word(Int2MInt(I))
endmodule
"#;

/// `MInt{Foo}` names no width, so the description of `MINT.integer` gives a conversion into it
/// no value, and only a `total` declaration says that it has one. A step that writes the
/// application of the function declared without `total` therefore has a successor in no model the
/// definition is known to have, on a literal as on a variable, and no claim through it is
/// proven; the same claims through a function declared `total` are proven, the value being some
/// machine integer the definition does not determine.
#[test]
fn kprove_takes_a_widthless_mint_conversion_as_defined_only_where_it_is_declared_total() {
    let source = format!(
        "{WIDTHLESS_MINT}
module WIDTHLESS-SPEC
  imports WIDTHLESS
  claim [partial-literal]: <k> partial(5) => word(?_W:MInt{{Foo}}) </k>
  claim [partial-variable]: <k> partial(_I:Int) => word(?_W:MInt{{Foo}}) </k>
  claim [declared-literal]: <k> declared(5) => word(?_W:MInt{{Foo}}) </k>
  claim [declared-variable]: <k> declared(_I:Int) => word(?_W:MInt{{Foo}}) </k>
  claim [prelude-literal]: <k> prelude(5) => word(?_W:MInt{{Foo}}) </k>
  claim [prelude-variable]: <k> prelude(_I:Int) => word(?_W:MInt{{Foo}}) </k>
endmodule
"
    );
    let (verdicts, output) = order_claim_verdicts(&source, "WIDTHLESS", "WIDTHLESS-SPEC");
    for claim in ["partial-literal", "partial-variable"] {
        assert_undecided(&verdicts, claim, &output);
    }
    for claim in [
        "declared-literal",
        "declared-variable",
        "prelude-literal",
        "prelude-variable",
    ] {
        assert_eq!(
            claim_verdict(&verdicts, claim, &output),
            "proven",
            "{claim}: {output}"
        );
    }
}

fn compiled_modal_claim_fixture() -> (PathBuf, PathBuf) {
    let (root, definition, _) = modal_claim_fixture();
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--output-directory",
            compiled.to_str().unwrap(),
            "--for-proving",
        ])
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    (root, compiled)
}

#[test]
fn kprove_reports_closed_stdout_as_io_error() {
    let (root, compiled) = compiled_modal_claim_fixture();
    // Exercise trusted reporting, an executed proof, and an unproven result. Each child reaches
    // its first report line, where the closed pipe surfaces, after loading the compiled
    // definition; nothing is compiled behind the dead stdout.
    //
    // The child's stdout is a pipe whose read end is closed before the child starts, so every
    // write to it fails, the first one included. Closing the read end after the spawn instead
    // would race: a first report line written into the pipe's buffer before the close succeeds,
    // and a child that writes nothing else exits 0.
    for options in [
        ["--trusted", "reaches-b-or-c"],
        ["--depth", "10"],
        ["--depth", "0"],
    ] {
        let (reader, writer) = std::io::pipe().unwrap();
        drop(reader);
        let child = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kprove",
                "--compiled-definition",
                compiled.to_str().unwrap(),
            ])
            .args(["--main-module", "MAIN", "--claim", "reaches-b-or-c"])
            .args(options)
            .stdout(Stdio::from(writer))
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();

        // The child holds no pipe it could block on: stdout has no reader and stderr is drained
        // here, so the wait has no deadline.
        let output = child.wait_with_output().unwrap();
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert_eq!(output.status.code(), Some(1), "{options:?}: {stderr}");
        assert!(stderr.contains("error:"), "{options:?}: {stderr}");
        assert!(
            stderr.to_lowercase().contains("pipe"),
            "{options:?}: {stderr}"
        );
        assert!(!stderr.contains("panicked"), "{options:?}: {stderr}");
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_compiles_only_a_specification_against_prepared_semantics() {
    let (root, _) = fixture();
    let timings = root.join("timings.json");
    let semantics = root.join("semantics.k");
    let specification = root.join("spec.k");
    let compiled = root.join("compiled");
    fs::write(
        &semantics,
        r#"
module SEMANTICS
  syntax State ::= "a" [symbol(a)] | "b" [symbol(b)]
  configuration <k> $PGM:State </k>
  rule <k> a => b </k>
endmodule
"#,
    )
    .unwrap();
    fs::write(
        &specification,
        r#"
requires "semantics.k"
module SPEC
  imports SEMANTICS
  claim <k> a => b </k> [label(reaches-b)]
endmodule
"#,
    )
    .unwrap();

    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            semantics.to_str().unwrap(),
            "--main-module",
            "SEMANTICS",
            "--output-directory",
            compiled.to_str().unwrap(),
            "--for-proving",
        ])
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    assert!(!compiled.join("runtime.json").exists());
    fs::remove_file(&semantics).unwrap();

    let load = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "--main-module",
            "SEMANTICS",
            "--load-only",
            "--timings",
            timings.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        load.status.success(),
        "{}",
        String::from_utf8_lossy(&load.stderr)
    );
    assert!(load.stdout.is_empty());
    let load_timings: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&timings).unwrap()).unwrap();
    assert_eq!(
        load_timings["version"],
        k_rust::timings::TIMINGS_SCHEMA_VERSION
    );
    assert!(load_timings["input_seconds"].as_f64().unwrap() > 0.0);
    assert!(load_timings["internalize_seconds"].as_f64().unwrap() > 0.0);
    assert_eq!(load_timings["proof_seconds"], 0.0);
    assert_eq!(load_timings["proof_setup_seconds"], 0.0);
    assert_eq!(load_timings["claims"], serde_json::json!([]));

    let proof = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            specification.to_str().unwrap(),
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "--main-module",
            "SPEC",
            "--definition-module",
            "SEMANTICS",
            "--claim",
            "reaches-b",
        ])
        .output()
        .unwrap();
    assert!(
        proof.status.success(),
        "{}",
        String::from_utf8_lossy(&proof.stderr)
    );
    assert_eq!(
        String::from_utf8(proof.stdout).unwrap(),
        "claim reaches-b: proven (2 states, 0 unexplored)\n"
    );

    let prepared_spec = root.join("prepared-spec");
    let compile_spec = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            specification.to_str().unwrap(),
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "--main-module",
            "SPEC",
            "--definition-module",
            "SEMANTICS",
            "--for-proving",
            "--output-directory",
            prepared_spec.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        compile_spec.status.success(),
        "{}",
        String::from_utf8_lossy(&compile_spec.stderr)
    );
    assert!(!prepared_spec.join("runtime.json").exists());
    fs::remove_file(&specification).unwrap();
    let prepared_proof = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            "--compiled-definition",
            prepared_spec.to_str().unwrap(),
            "--main-module",
            "SPEC",
            "--claim",
            "reaches-b",
            "--timings",
            timings.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        prepared_proof.status.success(),
        "{}",
        String::from_utf8_lossy(&prepared_proof.stderr)
    );
    assert_eq!(
        String::from_utf8(prepared_proof.stdout).unwrap(),
        "claim reaches-b: proven (2 states, 0 unexplored)\n"
    );
    let proof_timings: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&timings).unwrap()).unwrap();
    assert_eq!(
        proof_timings["version"],
        k_rust::timings::TIMINGS_SCHEMA_VERSION
    );
    assert!(proof_timings["proof_setup_seconds"].as_f64().unwrap() > 0.0);
    assert!(proof_timings["proof_seconds"].as_f64().unwrap() > 0.0);
    assert_eq!(proof_timings["claims"][0]["label"], "reaches-b");
    assert_eq!(proof_timings["claims"][0]["status"], "proven");
    assert_eq!(
        proof_timings["claims"][0]["seconds"],
        proof_timings["proof_seconds"]
    );

    let bounded = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            "--compiled-definition",
            prepared_spec.join("definition.kore").to_str().unwrap(),
            "--main-module",
            "SPEC",
            "--depth",
            "0",
            "--timings",
            timings.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(!bounded.status.success());
    let bounded_timings: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&timings).unwrap()).unwrap();
    assert_ne!(bounded_timings["claims"][0]["status"], "proven");
    assert_eq!(bounded_timings["claims"][0]["label"], "reaches-b");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_keeps_definition_and_spec_markdown_selectors_distinct() {
    let (root, _) = fixture();
    let semantics = root.join("semantics.md");
    let specification = root.join("spec.md");
    let reread_specification = root.join("reread-spec.md");
    let compiled = root.join("compiled");
    let definition_selector = "(k|keep) & !discard";
    fs::write(
        &semantics,
        r#"
```k
requires "domains.md"
module SEMANTICS
  imports INT
  syntax State ::= "a" [symbol(a)] | "b" [symbol(b)]
  configuration <k> $PGM:State </k>
```
```keep
  rule <k> a => b </k>
```
```discard
  rule <k> b => a </k>
```
```k
endmodule
```
"#,
    )
    .unwrap();
    fs::write(
        &specification,
        r#"
```keep
module SPEC
  imports SEMANTICS
  claim <k> a => b </k> [label(reaches-b)]
  claim <k> b => b </k> [label(stays-b)]
endmodule
```
```discard
module DISCARDED imports MISSING-DISCARDED endmodule
```
```k
module WRONG-SELECTOR imports MISSING-K endmodule
```
"#,
    )
    .unwrap();
    fs::write(
        &reread_specification,
        r#"
```k
requires "semantics.md"
module REREAD-SPEC
  imports SEMANTICS
  claim <k> b => b </k> [label(reloads-identical-semantics)]
endmodule
```
"#,
    )
    .unwrap();

    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            semantics.to_str().unwrap(),
            "--main-module",
            "SEMANTICS",
            "--md-selector",
            definition_selector,
            "--for-proving",
            "--output-directory",
            compiled.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );

    let proof = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            specification.to_str().unwrap(),
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "--main-module",
            "SPEC",
            "--definition-module",
            "SEMANTICS",
            "--md-selector",
            "keep&!(discard|k)",
        ])
        .output()
        .unwrap();
    assert!(
        proof.status.success(),
        "{}",
        String::from_utf8_lossy(&proof.stderr)
    );
    let stdout = String::from_utf8(proof.stdout).unwrap();
    assert!(stdout.contains("claim reaches-b: proven"), "{stdout}");
    assert!(stdout.contains("claim stays-b: proven"), "{stdout}");

    let without_prepared = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            specification.to_str().unwrap(),
            "--main-module",
            "SPEC",
            "--definition-module",
            "SEMANTICS",
            "--md-selector",
            "keep&!(discard|k)",
        ])
        .output()
        .unwrap();
    assert!(!without_prepared.status.success());
    assert!(
        String::from_utf8_lossy(&without_prepared.stderr)
            .contains("imports missing module \"SEMANTICS\"")
    );

    let same_selector = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            reread_specification.to_str().unwrap(),
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "--main-module",
            "REREAD-SPEC",
            "--definition-module",
            "SEMANTICS",
            "--md-selector",
            definition_selector,
        ])
        .output()
        .unwrap();
    assert!(
        same_selector.status.success(),
        "{}",
        String::from_utf8_lossy(&same_selector.stderr)
    );

    let changed_selector = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            reread_specification.to_str().unwrap(),
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "--main-module",
            "REREAD-SPEC",
            "--definition-module",
            "SEMANTICS",
            "--md-selector",
            "k",
        ])
        .output()
        .unwrap();
    assert!(!changed_selector.status.success());
    let stderr = String::from_utf8_lossy(&changed_selector.stderr);
    assert!(
        stderr.contains("differs from previous declaration"),
        "{stderr}"
    );
    assert!(
        stderr.contains("This can happen if --md-selector differs for kompile and kprove"),
        "{stderr}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_rejects_unsupported_prepared_manifest_versions() {
    let (root, definition) = fixture();
    let compiled = root.join("compiled");
    fs::create_dir_all(&compiled).unwrap();
    fs::write(
        compiled.join("krust.json"),
        r#"{"format":"krust-prepared-definition","version":999,"sources":[]}"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            definition.to_str().unwrap(),
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "-m",
            "MAIN",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("unsupported prepared definition manifest")
    );
    fs::remove_dir_all(root).unwrap();
}

/// Proof preparation for a semantics whose strictness names a context alias.
fn prepared_context_alias_semantics() -> (PathBuf, PathBuf, PathBuf) {
    let (root, _) = fixture();
    let semantics = root.join("semantics.k");
    let specification = root.join("spec.k");
    let compiled = root.join("compiled");
    fs::write(
        &semantics,
        r#"
module SEMANTICS
  imports INT
  syntax KResult ::= Int
  syntax Exp ::= Int | foo(Exp) [strict(c), symbol(foo)] | a() [symbol(a)]
  context alias [c]: HERE
  configuration <k> $PGM:Exp </k>
  rule <k> a() => 1 ... </k>
  rule <k> foo(I:Int) => I +Int 1 ... </k>
endmodule
"#,
    )
    .unwrap();
    fs::write(
        &specification,
        r#"
requires "semantics.k"
module SPEC
  imports SEMANTICS
  claim <k> foo(a()) => 2 </k> [label(heats-a)]
endmodule
"#,
    )
    .unwrap();
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            semantics.to_str().unwrap(),
            "--main-module",
            "SEMANTICS",
            "--for-proving",
            "--output-directory",
            compiled.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    (root, specification, compiled)
}

fn kprove_spec_against(specification: &Path, compiled: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            specification.to_str().unwrap(),
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "--main-module",
            "SPEC",
            "--definition-module",
            "SEMANTICS",
        ])
        .output()
        .unwrap()
}

#[test]
fn kprove_against_prepared_semantics_keeps_context_aliases_named_by_strictness() {
    let (root, specification, compiled) = prepared_context_alias_semantics();
    // The claim holds only through the heating and cooling rules that `strict(c)` generates from
    // the context alias, so the alias must reach the specification's compilation.
    let proof = kprove_spec_against(&specification, &compiled);
    assert!(
        proof.status.success(),
        "{}",
        String::from_utf8_lossy(&proof.stderr)
    );
    assert!(
        String::from_utf8_lossy(&proof.stdout).contains("claim heats-a: proven"),
        "{}",
        String::from_utf8_lossy(&proof.stdout)
    );

    // A specification prepared against the semantics is itself a base for later specifications.
    let prepared_spec = root.join("prepared-spec");
    let compile_spec = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            specification.to_str().unwrap(),
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "--main-module",
            "SPEC",
            "--definition-module",
            "SEMANTICS",
            "--for-proving",
            "--output-directory",
            prepared_spec.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        compile_spec.status.success(),
        "{}",
        String::from_utf8_lossy(&compile_spec.stderr)
    );
    let later = root.join("later-spec.k");
    fs::write(
        &later,
        r#"
requires "spec.k"
module LATER
  imports SPEC
  claim <k> foo(foo(a())) => 3 </k> [label(heats-twice)]
endmodule
"#,
    )
    .unwrap();
    let later_proof = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            later.to_str().unwrap(),
            "--compiled-definition",
            prepared_spec.to_str().unwrap(),
            "--main-module",
            "LATER",
            "--definition-module",
            "SEMANTICS",
            "--claim",
            "heats-twice",
        ])
        .output()
        .unwrap();
    assert!(
        later_proof.status.success(),
        "{}",
        String::from_utf8_lossy(&later_proof.stderr)
    );
    assert!(
        String::from_utf8_lossy(&later_proof.stdout).contains("claim heats-twice: proven"),
        "{}",
        String::from_utf8_lossy(&later_proof.stdout)
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_rejects_a_prepared_directory_without_its_lossless_definition() {
    let (root, specification, compiled) = prepared_context_alias_semantics();
    let manifest_path = compiled.join("krust.json");
    let manifest: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&manifest_path).unwrap()).unwrap();
    let definition = compiled.join(manifest["definition"].as_str().unwrap());
    assert!(definition.is_file(), "{manifest}");

    // A definition written in an earlier provenance version (here by the version 7 writer) is
    // refused by its version, with the remedy, not as a malformed document.
    let current = fs::read(&definition).unwrap();
    fs::write(&definition, PROVENANCE_VERSION_7).unwrap();
    let earlier = kprove_spec_against(&specification, &compiled);
    assert!(!earlier.status.success());
    let stderr = String::from_utf8_lossy(&earlier.stderr);
    assert!(
        stderr.contains(&format!(
            "could not decode {}: KRUST-PROVENANCE version 7 is not supported; this build reads \
             version 8; prepare the semantics again with `kcompile --for-proving`",
            definition.display()
        )),
        "{stderr}"
    );
    fs::write(&definition, current).unwrap();

    // The named file is a symbolic link to a definition outside the bundle.
    let outside = root.join("outside.provenance.json");
    fs::rename(&definition, &outside).unwrap();
    std::os::unix::fs::symlink(&outside, &definition).unwrap();
    let escaped = kprove_spec_against(&specification, &compiled);
    assert!(!escaped.status.success());
    let stderr = String::from_utf8_lossy(&escaped.stderr);
    assert!(
        stderr.contains("outside the prepared directory")
            && stderr.contains(definition.to_str().unwrap()),
        "{stderr}"
    );

    fs::remove_file(&definition).unwrap();
    let missing = kprove_spec_against(&specification, &compiled);
    assert!(!missing.status.success());
    let stderr = String::from_utf8_lossy(&missing.stderr);
    assert!(
        stderr.contains("lacks its lossless parsed definition")
            && stderr.contains(definition.to_str().unwrap()),
        "{stderr}"
    );

    // A directory prepared before the manifest named the lossless definition holds only the
    // interchange `parsed.json`, which cannot denote every definition; it is not read.
    let mut older = manifest.clone();
    older["version"] = 1.into();
    older.as_object_mut().unwrap().remove("definition");
    fs::write(&manifest_path, older.to_string()).unwrap();
    let older_output = kprove_spec_against(&specification, &compiled);
    assert!(!older_output.status.success());
    let stderr = String::from_utf8_lossy(&older_output.stderr);
    assert!(
        stderr.contains("lacks its lossless parsed definition")
            && stderr.contains(definition.to_str().unwrap()),
        "{stderr}"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_loads_a_new_spec_module_from_the_semantics_entry_file() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module SEMANTICS
  syntax State ::= "a" | "b"
  configuration <k> $PGM:State </k>
  rule <k> a => b </k>
endmodule
module SPEC
  imports SEMANTICS
  claim <k> a => b </k> [label(reaches-b)]
endmodule
"#,
    )
    .unwrap();
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "-m",
            "SEMANTICS",
            "--for-proving",
            "-o",
            compiled.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    let parsed = fs::read_to_string(compiled.join("parsed.json")).unwrap();
    let base = k_rust::definition::json::from_str(&parsed).unwrap();
    assert!(!base.modules.iter().any(|module| module.name == "SPEC"));
    let proof = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            definition.to_str().unwrap(),
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "-m",
            "SPEC",
            "--definition-module",
            "SEMANTICS",
        ])
        .output()
        .unwrap();
    assert!(
        proof.status.success(),
        "{}",
        String::from_utf8_lossy(&proof.stderr)
    );
    assert!(String::from_utf8_lossy(&proof.stdout).contains("claim reaches-b: proven"));
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_claim_selection_does_not_use_unselected_lemmas() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/proof/split");
    let specification = fixtures.join("lemma-spec.k");
    // The isolated claim and the batch read one compiled specification.
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    kcompile_for_proving(&specification, "LEMMA-SPEC", "SPLIT", &compiled);

    let isolated = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kprove", "--compiled-definition"])
        .arg(&compiled)
        .args([
            "--main-module",
            "LEMMA-SPEC",
            "--definition-module",
            "SPLIT",
            "--claim",
            "ca",
            "--depth",
            "10",
        ])
        .output()
        .unwrap();
    let isolated_stdout = String::from_utf8(isolated.stdout).unwrap();
    assert!(!isolated.status.success(), "{isolated_stdout}");
    assert!(
        isolated_stdout.contains("claim LEMMA-SPEC.ca: disproved"),
        "{isolated_stdout}"
    );

    let batch = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kprove", "--compiled-definition"])
        .arg(&compiled)
        .args([
            "--main-module",
            "LEMMA-SPEC",
            "--definition-module",
            "SPLIT",
            "--depth",
            "10",
        ])
        .output()
        .unwrap();
    let batch_stdout = String::from_utf8(batch.stdout).unwrap();
    assert!(!batch.status.success(), "{batch_stdout}");
    assert!(
        batch_stdout.contains("claim LEMMA-SPEC.ca: proven"),
        "{batch_stdout}"
    );
    assert!(
        batch_stdout.contains("claim LEMMA-SPEC.cb: disproved"),
        "{batch_stdout}"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_filters_claims_imported_into_the_specification_module() {
    // reference (k/result/bin, split.k kompiled with --backend haskell, imported-spec.k with
    // --depth 10): --exclude SPLIT-LEMMAS.fail1 --exclude SPLIT-LEMMAS.fail2 exits 0 (#Top);
    // --trusted SPLIT-LEMMAS.fail1 --trusted SPLIT-LEMMAS.fail2 exits 0 (#Top); no flags exits 1
    // stuck on fail1 (imported-spec.k:5); excluding all three claims exits 113 with
    // "Unexpected empty set of claims.". Recorded in split/reference.toml.
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/proof/split");
    let specification = fixtures.join("imported-spec.k");
    let (root, _) = fixture();
    let compiled_semantics = root.join("semantics");
    let compiled_spec = root.join("specification");
    let timings = root.join("timings.json");
    for (source, module, destination) in [
        (fixtures.join("split.k"), "SPLIT", &compiled_semantics),
        (specification.clone(), "IMPORTED-SPEC", &compiled_spec),
    ] {
        let compiled = Command::new(env!("CARGO_BIN_EXE_krust"))
            .arg("kcompile")
            .arg(source)
            .args([
                "--main-module",
                module,
                "--definition-module",
                "SPLIT",
                "--for-proving",
            ])
            .arg("--output-directory")
            .arg(destination)
            .output()
            .unwrap();
        assert!(
            compiled.status.success(),
            "{}",
            String::from_utf8_lossy(&compiled.stderr)
        );
    }
    for input in [
        vec![specification.to_str().unwrap()],
        vec![
            specification.to_str().unwrap(),
            "--compiled-definition",
            compiled_semantics.to_str().unwrap(),
        ],
        vec!["--compiled-definition", compiled_spec.to_str().unwrap()],
    ] {
        let mut common = vec!["kprove"];
        common.extend(input);
        common.extend([
            "--main-module",
            "IMPORTED-SPEC",
            "--definition-module",
            "SPLIT",
            "--depth",
            "10",
        ]);

        let excluded = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(&common)
            .args(["--exclude", "fail1", "--exclude", "SPLIT-LEMMAS.fail2"])
            .output()
            .unwrap();
        assert!(
            excluded.status.success(),
            "{}{}",
            String::from_utf8_lossy(&excluded.stdout),
            String::from_utf8_lossy(&excluded.stderr)
        );
        assert_eq!(
            String::from_utf8(excluded.stdout).unwrap(),
            "claim SPLIT-LEMMAS.pass: proven (3 states, 0 unexplored)\n"
        );

        let trusted = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(&common)
            .args(["--trusted", "fail1", "--trusted", "fail2"])
            .arg("--timings")
            .arg(&timings)
            .output()
            .unwrap();
        assert!(
            trusted.status.success(),
            "{}{}",
            String::from_utf8_lossy(&trusted.stdout),
            String::from_utf8_lossy(&trusted.stderr)
        );
        // Claims are reported in declaration order (imported-spec.k: pass, fail1, fail2).
        assert_eq!(
            String::from_utf8(trusted.stdout).unwrap(),
            "claim SPLIT-LEMMAS.pass: proven (3 states, 0 unexplored)\n\
         claim SPLIT-LEMMAS.fail1: proven (trusted)\n\
         claim SPLIT-LEMMAS.fail2: proven (trusted)\n"
        );

        let recorded: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(&timings).unwrap()).unwrap();
        let claims = recorded["claims"].as_array().unwrap();
        assert_eq!(claims.len(), 3, "{recorded}");
        for claim in &claims[1..] {
            assert_eq!(claim["status"], "trusted");
            assert_eq!(claim["seconds"], 0.0);
        }
        assert_eq!(recorded["proof_seconds"], claims[0]["seconds"]);

        // Control: without filtering every imported claim is attempted.
        let batch = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(&common)
            .output()
            .unwrap();
        let batch_stdout = String::from_utf8(batch.stdout).unwrap();
        assert!(!batch.status.success(), "{batch_stdout}");
        assert!(
            batch_stdout.contains("claim SPLIT-LEMMAS.pass: proven"),
            "{batch_stdout}"
        );
        for claim in ["SPLIT-LEMMAS.fail1", "SPLIT-LEMMAS.fail2"] {
            assert!(
                batch_stdout.contains(&format!("claim {claim}: disproved")),
                "{batch_stdout}"
            );
        }

        // Excluding every claim leaves nothing to prove: no claim's validity could be reported,
        // so an empty claim set is an error rather than a vacuous success.
        let emptied = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(&common)
            .args([
                "--exclude",
                "pass",
                "--exclude",
                "fail1",
                "--exclude",
                "fail2",
            ])
            .output()
            .unwrap();
        assert!(!emptied.status.success());
        assert_eq!(String::from_utf8(emptied.stdout).unwrap(), "");
        assert!(
            String::from_utf8_lossy(&emptied.stderr)
                .contains("the selected module contains no modal reachability claims"),
            "{}",
            String::from_utf8_lossy(&emptied.stderr)
        );
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_one_path_claim_fails_on_the_uncovered_case() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/proof/split");
    let specification = fixtures.join("onepath-spec.k");

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            specification.to_str().unwrap(),
            "--main-module",
            "ONEPATH-SPEC",
            "--definition-module",
            "SPLIT",
            "--depth",
            "10",
        ])
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();

    assert!(!output.status.success(), "{stdout}");
    // `start(I)` with `I <=Int 0` has the one successor `bad` (the two rules' conditions are
    // disjoint), which has none: no path reaches `good`, a certified refutation.
    assert!(
        stdout.contains("claim ONEPATH-SPEC.c1: disproved"),
        "{stdout}"
    );
    assert!(stdout.contains("stuck (certified) at depth 1"), "{stdout}");
}

#[test]
fn reference_ite_bug_splits_implication_obligations_without_branching_functions() {
    // reference: kprove fixture captured under reference/implication/ite-bug/reference.log
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/implication/ite-bug");
    let (root, _) = fixture();
    fs::copy(fixtures.join("ite-bug.k"), root.join("ite-bug.k")).unwrap();
    let cases = [
        ("passing-spec.k", "PASSING-SPEC", true),
        ("failing-1-spec.k", "FAILING-1-SPEC", false),
        ("failing-2-spec.k", "FAILING-2-SPEC", false),
    ];

    for (specification, module, should_prove) in cases {
        let source = format!(
            "requires \"ite-bug.k\"\n{}",
            fs::read_to_string(fixtures.join(specification)).unwrap()
        );
        let specification_path = root.join(specification);
        fs::write(&specification_path, source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kprove",
                specification_path.to_str().unwrap(),
                "--main-module",
                module,
                "--definition-module",
                "ITE-BUG",
                "--depth",
                "10",
            ])
            .output()
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();

        assert_eq!(
            output.status.success(),
            should_prove,
            "{specification}: {stdout}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        // The failing leaves are constrained through `bool2Word`, which has no SMT translation:
        // they are non-empty only modulo abstraction, so the claims fail without a certified
        // refutation.
        assert!(
            stdout.contains(if should_prove { "proven" } else { "failed" }),
            "{specification}: {stdout}"
        );
    }

    let nolemma = fixtures.join("nolemma");
    fs::copy(nolemma.join("ite-bug.k"), root.join("ite-bug.k")).unwrap();
    let specification = root.join("passing-nolemma-spec.k");
    fs::write(
        &specification,
        format!(
            "requires \"ite-bug.k\"\n{}",
            fs::read_to_string(nolemma.join("passing-spec.k")).unwrap()
        ),
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            specification.to_str().unwrap(),
            "--main-module",
            "PASSING-SPEC",
            "--definition-module",
            "ITE-BUG",
            "--depth",
            "10",
        ])
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        output.status.success(),
        "nolemma/passing-spec.k: {stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(stdout.contains("proven"), "{stdout}");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_rejects_claims_reached_only_through_bottom() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/proof/split");
    let specification = fixtures.join("trivial-spec.k");
    // Both vacuity policies read one compiled specification.
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    kcompile_for_proving(&specification, "TRIVIAL-SPEC", "SPLIT", &compiled);
    let common = [
        "kprove",
        "--compiled-definition",
        compiled.to_str().unwrap(),
        "--main-module",
        "TRIVIAL-SPEC",
        "--definition-module",
        "SPLIT",
        "--depth",
        "10",
    ];

    let rejected = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(common)
        .output()
        .unwrap();
    let rejected_stdout = String::from_utf8(rejected.stdout).unwrap();
    assert!(!rejected.status.success(), "{rejected_stdout}");
    // A trivial leaf is an empty set of configurations: the vacuity policy rejects it, so the
    // claim fails, but no configuration refutes it.
    for claim in ["TRIVIAL-SPEC.ct1", "TRIVIAL-SPEC.ct2"] {
        assert!(
            rejected_stdout.contains(&format!("claim {claim}: failed")),
            "{rejected_stdout}"
        );
    }
    assert!(
        rejected_stdout.contains("trivial at depth 1"),
        "{rejected_stdout}"
    );
    assert!(
        rejected_stdout.contains(
            "undefined step: a rule applies to these configurations but its result is empty \
             for them, so they have no successor (--allow-vacuous accepts such branches)"
        ),
        "{rejected_stdout}"
    );

    let allowed = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(common)
        .arg("--allow-vacuous")
        .output()
        .unwrap();
    let allowed_stdout = String::from_utf8(allowed.stdout).unwrap();
    assert!(allowed.status.success(), "{allowed_stdout}");
    for claim in ["TRIVIAL-SPEC.ct1", "TRIVIAL-SPEC.ct2"] {
        assert!(
            allowed_stdout.contains(&format!("claim {claim}: proven")),
            "{allowed_stdout}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

/// A claim holds for every instance of its left-hand side, so a symbolic claim is not proven
/// while one of its instances ends in an undefined step. `apart(X, Y)` has the undefined step
/// `apart(0, 0)` because the rule's `ensures` fails there: the symbolic claims, one-path and
/// all-path, fail exactly like the ground one, and `--allow-vacuous` accepts all of them. An
/// instance that a sibling takes to a defined result (`cover`) and an `ensures` that always has a
/// witness (`fresh`) leave no undefined step. A one-path step offers the instances where a rule
/// applies but its result is undefined to the later rules of its priority, so `cover` and `skip`
/// are proven one-path as they are all-path; it never offers them to a lower priority (`low`), and
/// where no rule of the priority gives a defined result (`pick`) the one-path claim fails too.
#[test]
fn kprove_fails_a_claim_on_the_instances_a_rule_leaves_undefined() {
    let (root, definition) = fixture();
    fs::write(&definition, UNDEFINED_STEP).unwrap();
    // The three proof runs read one compiled specification.
    let compiled = root.join("compiled");
    kcompile_for_proving(&definition, "UNDEF-SPEC", "UNDEF", &compiled);
    let prove = |extra: &[&str]| {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["kprove", "--compiled-definition"])
            .arg(&compiled)
            .args([
                "--main-module",
                "UNDEF-SPEC",
                "--definition-module",
                "UNDEF",
            ])
            .args(extra)
            .stdin(Stdio::null())
            .output()
            .unwrap();
        (
            output.status.success(),
            String::from_utf8(output.stdout).unwrap(),
        )
    };
    let verdict = |stdout: &str, claim: &str| {
        let prefix = format!("claim UNDEF-SPEC.{claim}: ");
        stdout
            .lines()
            .find_map(|line| line.strip_prefix(&prefix))
            .unwrap_or_else(|| panic!("no {claim} verdict in {stdout}"))
            .split_whitespace()
            .next()
            .unwrap()
            .to_owned()
    };

    let (success, stdout) = prove(&[]);
    assert!(!success, "{stdout}");
    for claim in [
        "sym", "gnd", "sym-one", "pick", "pick-one", "low-one", "low",
    ] {
        assert_eq!(verdict(&stdout, claim), "failed", "{claim}: {stdout}");
    }
    for claim in [
        "defined",
        "cover",
        "fresh",
        "fresh-one",
        "cover-one",
        "skip-one",
        "skip",
    ] {
        assert_eq!(verdict(&stdout, claim), "proven", "{claim}: {stdout}");
    }
    assert!(stdout.contains("trivial at depth 1"), "{stdout}");
    assert!(stdout.contains("  undefined step: "), "{stdout}");

    // The one-path claims alone, so that no all-path claim with the same body is proven first
    // in the same run and none is reported from a saved proof.
    let one_path = ["cover-one", "skip-one", "pick-one", "low-one"];
    let (success, stdout) = prove(&one_path.map(|claim| ["--claim", claim]).concat());
    assert!(!success, "{stdout}");
    assert!(!stdout.contains("(saved)"), "{stdout}");
    for claim in ["pick-one", "low-one"] {
        assert_eq!(verdict(&stdout, claim), "failed", "{claim}: {stdout}");
    }
    for claim in ["cover-one", "skip-one"] {
        assert_eq!(verdict(&stdout, claim), "proven", "{claim}: {stdout}");
    }

    let (success, stdout) = prove(&["--allow-vacuous"]);
    assert!(success, "{stdout}");
    fs::remove_dir_all(root).unwrap();
}

/// Set concatenation is nilpotent: `SetItem(X) SetItem(X)` is `\bottom`, and `|Set` is the union.
/// `ovl` concatenates a set with an element it already holds, `lit` writes a repeated element,
/// `size` evaluates a hook on such a set, `dis` concatenates disjoint sets and `uni` takes the
/// union. `NILPOTENT_SET_SPEC` claims the ground and the symbolic instance of one step that
/// concatenates, and the symbolic one restricted to the instances where the sets are disjoint.
const NILPOTENT_SET: &str = r#"
module NSET
  imports DOMAINS
  configuration <k> $PGM:Pgm </k> <s> SetItem(1) </s>
  syntax Pgm ::= "ovl" | "dis" | "uni" | "lit" | "sz" | "keep" | add(Int)
  rule <k> ovl => .K ...</k> <s> S => S SetItem(1) </s>
  rule <k> dis => .K ...</k> <s> S => S SetItem(2) </s>
  rule <k> uni => .K ...</k> <s> S => S |Set SetItem(1) </s>
  rule <k> lit => .K ...</k> <s> _ => SetItem(3) SetItem(3) </s>
  rule <k> sz => size(SetItem(1) SetItem(1)) ...</k>
  rule <k> keep => .K ...</k> <s> SetItem(X) S => SetItem(X) S </s>
  rule <k> add(I) => .K ...</k> <s> S => S SetItem(I) </s>
endmodule
"#;

const NILPOTENT_SET_SPEC: &str = r#"
requires "definition.k"
module NSET-SPEC
  imports NSET
  claim [gnd]: <k> add(1) => .K </k> <s> SetItem(1) => ?_ </s>
  claim [sym]: <k> add(_I) => .K </k> <s> SetItem(1) => ?_ </s>
  claim [fresh]: <k> add(I) => .K </k> <s> SetItem(1) => ?_ </s> requires I =/=Int 1
endmodule
"#;

/// A concrete run and a proof agree on one theory of `_Set_`: concatenating sets that share an
/// element is an undefined step (the rule applies and its result is empty), in `krun` as in
/// `kprove`; concatenating disjoint sets and `|Set` are unchanged.
#[test]
fn set_concatenation_is_nilpotent_in_krun_and_kprove() {
    let (root, definition) = fixture();
    fs::write(&definition, NILPOTENT_SET).unwrap();
    let compiled = root.join("compiled");
    kcompile_for_krun(
        &definition,
        &["--main-module", "NSET", "--syntax-module", "NSET"],
        &compiled,
    );
    let run = |program: &str| {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["krun", "--definition"])
            .arg(&compiled)
            .args(["-s", "Pgm", "--io", "off", "-e", program])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert!(output.status.success(), "{program}: {output:?}");
        (
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap(),
        )
    };
    let item = |value: u32| {
        format!(
            "LblSetItem{{}}(inj{{SortInt{{}}, SortKItem{{}}}}(\\dv{{SortInt{{}}}}(\"{value}\")))"
        )
    };
    for program in ["ovl", "lit", "sz"] {
        let (stdout, stderr) = run(program);
        assert!(
            stderr.contains("execution ended with no successor at depth 1")
                && stderr.contains("applied with an undefined result"),
            "{program}: {stderr}"
        );
        assert!(
            stdout.contains("\\bottom{SortGeneratedTopCell{}}()"),
            "{program}: {stdout}"
        );
    }
    let (stdout, stderr) = run("dis");
    assert!(!stderr.contains("no successor"), "{stderr}");
    assert!(
        stdout.contains(&item(1)) && stdout.contains(&item(2)),
        "{stdout}"
    );
    for program in ["uni", "keep"] {
        let (stdout, stderr) = run(program);
        assert!(!stderr.contains("no successor"), "{program}: {stderr}");
        assert!(
            stdout.contains(&format!("Lbl'-LT-'s'-GT-'{{}}({})", item(1))),
            "{program}: {stdout}"
        );
    }

    let spec = root.join("nset-spec.k");
    fs::write(&spec, NILPOTENT_SET_SPEC).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            spec.to_str().unwrap(),
            "--main-module",
            "NSET-SPEC",
            "--definition-module",
            "NSET",
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(!output.status.success(), "{stdout}");
    let verdict = |claim: &str| {
        let prefix = format!("claim NSET-SPEC.{claim}: ");
        stdout
            .lines()
            .find_map(|line| line.strip_prefix(&prefix))
            .unwrap_or_else(|| panic!("no {claim} verdict in {stdout}"))
            .split_whitespace()
            .next()
            .unwrap()
            .to_owned()
    };
    assert_eq!(verdict("gnd"), "failed", "{stdout}");
    assert_eq!(verdict("sym"), "failed", "{stdout}");
    assert_eq!(verdict("fresh"), "proven", "{stdout}");
    assert!(stdout.contains("  undefined step: "), "{stdout}");
    fs::remove_dir_all(root).unwrap();
}

const REPEATED_COLLECTION: &str = r#"
module RCOL
  imports DOMAINS
  configuration <k> $PGM:Pgm </k> <s> .Set </s> <m> .Map </m>
  syntax Pgm ::= "tset" | "tsetok" | "tmapsame" | "tmapdiff" | "tmapok" | "pmapsame"
               | "rmapsame" | "done" | tsetS(Int) | dupS(Int)
  syntax Set ::= tAdd(Set, Int) [function, total]
               | tDup(Int) [function, total]
  rule tAdd(S, I) => S SetItem(I)
  rule tDup(I) => SetItem(I) SetItem(I)
  syntax Map ::= tPut(Map, Int, Int) [function, total]
               | pPut(Map, Int, Int) [function]
  rule tPut(M, K, V) => M (K |-> V)
  rule pPut(M, K, V) => M (K |-> V)
  rule <k> tset => done </k> <s> _ => tAdd(SetItem(1), 1) </s>
  rule <k> tsetok => done </k> <s> _ => tAdd(SetItem(1), 2) </s>
  rule <k> tmapsame => done </k> <m> _ => tPut(1 |-> 2, 1, 2) </m>
  rule <k> tmapdiff => done </k> <m> _ => tPut(1 |-> 2, 1, 3) </m>
  rule <k> tmapok => done </k> <m> _ => tPut(1 |-> 2, 2, 2) </m>
  rule <k> pmapsame => done </k> <m> _ => pPut(1 |-> 2, 1, 2) </m>
  rule <k> rmapsame => done </k> <m> _ => (1 |-> 2) (1 |-> 2) </m>
  rule <k> tsetS(I) => done </k> <s> _ => tAdd(SetItem(1), I) </s>
  rule <k> dupS(I) => done </k> <s> _ => tDup(I) </s>
endmodule
"#;

const REPEATED_COLLECTION_SPEC: &str = r#"
requires "definition.k"
module RCOL-SPEC
  imports RCOL
  claim [gnd]: <k> tsetS(1) => done </k> <s> _ => ?_ </s> <m> _ </m>
  claim [gndok]: <k> tsetS(2) => done </k> <s> _ => ?_ </s> <m> _ </m>
  claim [dup]: <k> dupS(_I) => done </k> <s> _ => ?_ </s> <m> _ </m>
endmodule
"#;

/// A set that holds an element twice and a map that binds a key twice, with the same value or
/// not, are `\bottom` where they are built: a rule's right-hand side, or the result of a function
/// equation, `total` or not, as a builtin's undefined result is. `krun` ends in an undefined
/// step and `kprove` fails the claim, on a ground repeat and on a symbolic one (`I` and `I`);
/// disjoint collections are unchanged.
#[test]
fn a_repeated_set_element_or_map_key_is_bottom_where_it_is_built() {
    let (root, definition) = fixture();
    fs::write(&definition, REPEATED_COLLECTION).unwrap();
    let compiled = root.join("compiled");
    kcompile_for_krun(
        &definition,
        &["--main-module", "RCOL", "--syntax-module", "RCOL"],
        &compiled,
    );
    let run = |program: &str| {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["krun", "--definition"])
            .arg(&compiled)
            .args(["-s", "Pgm", "--io", "off", "-e", program])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert!(output.status.success(), "{program}: {output:?}");
        (
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap(),
        )
    };
    for program in ["tset", "tmapsame", "tmapdiff", "pmapsame", "rmapsame"] {
        let (stdout, stderr) = run(program);
        assert!(
            stderr.contains("execution ended with no successor at depth 1")
                && stderr.contains("applied with an undefined result"),
            "{program}: {stderr}"
        );
        assert!(
            stdout.contains("\\bottom{SortGeneratedTopCell{}}()"),
            "{program}: {stdout}"
        );
    }
    let int =
        |value: u32| format!("inj{{SortInt{{}}, SortKItem{{}}}}(\\dv{{SortInt{{}}}}(\"{value}\"))");
    let (stdout, stderr) = run("tsetok");
    assert!(!stderr.contains("no successor"), "{stderr}");
    assert!(
        stdout.contains(&format!("LblSetItem{{}}({})", int(1)))
            && stdout.contains(&format!("LblSetItem{{}}({})", int(2))),
        "{stdout}"
    );
    let (stdout, stderr) = run("tmapok");
    assert!(!stderr.contains("no successor"), "{stderr}");
    assert!(
        stdout.contains(&int(1)) && stdout.contains(&int(2)) && !stdout.contains("\\bottom"),
        "{stdout}"
    );

    let spec = root.join("rcol-spec.k");
    fs::write(&spec, REPEATED_COLLECTION_SPEC).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            spec.to_str().unwrap(),
            "--main-module",
            "RCOL-SPEC",
            "--definition-module",
            "RCOL",
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(!output.status.success(), "{stdout}");
    let verdict = |claim: &str| {
        let prefix = format!("claim RCOL-SPEC.{claim}: ");
        stdout
            .lines()
            .find_map(|line| line.strip_prefix(&prefix))
            .unwrap_or_else(|| panic!("no {claim} verdict in {stdout}"))
            .split_whitespace()
            .next()
            .unwrap()
            .to_owned()
    };
    assert_eq!(verdict("gnd"), "failed", "{stdout}");
    assert_eq!(verdict("dup"), "failed", "{stdout}");
    assert_eq!(verdict("gndok"), "proven", "{stdout}");
    fs::remove_dir_all(root).unwrap();
}

const CONTRADICTED_TOTAL: &str = r#"
module CTOT
  imports DOMAINS
  configuration <k> $PGM:Pgm </k> <i> 0 </i> <s> .Set </s> <m> .Map </m>
  syntax Pgm ::= "tdiv" | "pdiv" | "tset" | "pset" | "tmapdiff" | "tnest" | "tvia" | "targ"
               | "done" | tsetS(Int) | psetS(Int)
  syntax Int ::= tDiv(Int) [function, total]
               | pDiv(Int) [function]
               | tNest(Int) [function, total]
               | tVia(Int) [function, total]
               | tId(Int) [function, total]
  rule [tdiv-eq]: tDiv(I) => 10 /Int I
  rule [pdiv-eq]: pDiv(I) => 10 /Int I
  rule [tnest-eq]: tNest(I) => tDiv(I) +Int 1
  rule [tvia-eq]: tVia(I) => pDiv(I)
  rule [tid-eq]: tId(I) => I
  syntax Set ::= tAdd(Set, Int) [function, total]
               | pAdd(Set, Int) [function]
  rule [tadd-eq]: tAdd(S, I) => S SetItem(I)
  rule [padd-eq]: pAdd(S, I) => S SetItem(I)
  syntax Map ::= tPut(Map, Int, Int) [function, total]
  rule [tput-eq]: tPut(M, K, V) => M (K |-> V)
  rule <k> tdiv => done </k> <i> _ => tDiv(0) </i>
  rule <k> pdiv => done </k> <i> _ => pDiv(0) </i>
  rule <k> tnest => done </k> <i> _ => tNest(0) </i>
  rule <k> tvia => done </k> <i> _ => tVia(0) </i>
  rule <k> targ => done </k> <i> _ => tId(pDiv(0)) </i>
  rule <k> tset => done </k> <s> _ => tAdd(SetItem(1), 1) </s>
  rule <k> pset => done </k> <s> _ => pAdd(SetItem(1), 1) </s>
  rule <k> tmapdiff => done </k> <m> _ => tPut(1 |-> 2, 1, 3) </m>
  rule <k> tsetS(I) => done </k> <s> _ => tAdd(SetItem(1), I) </s>
  rule <k> psetS(I) => done </k> <s> _ => pAdd(SetItem(1), I) </s>
endmodule
"#;

const CONTRADICTED_TOTAL_SPEC: &str = r#"
requires "definition.k"
module CTOT-SPEC
  imports CTOT
  claim [sym]: <k> tsetS(_I) => done </k> <i> _ </i> <s> _ => ?_ </s> <m> _ </m>
  claim [psym]: <k> psetS(_I) => done </k> <i> _ </i> <s> _ => ?_ </s> <m> _ </m>
  claim [gnd]: <k> tsetS(1) => done </k> <i> _ </i> <s> _ => ?_ </s> <m> _ </m>
  claim [pgnd]: <k> psetS(1) => done </k> <i> _ </i> <s> _ => ?_ </s> <m> _ </m>
  claim [div]: <k> tdiv => done </k> <i> _ => ?_ </i> <s> _ </s> <m> _ </m>
  claim [pdiv]: <k> pdiv => done </k> <i> _ => ?_ </i> <s> _ </s> <m> _ </m>
endmodule
"#;

const NON_JOINING_ANYWHERE: &str = r#"
module NJ
  imports DOMAINS
  configuration <k> $PGM:Pgm </k>
  syntax Pgm ::= w(Int) | m(Int) | v(Int)
  rule [w-one]: w(1) => m(1) [anywhere]
  rule [w-any]: w(_) => m(2) [anywhere]
  rule [v-one]: v(1) => m(1) [anywhere]
  rule [v-two]: v(2) => m(2) [anywhere]
endmodule
"#;

/// Two `anywhere` rules of `w` overlap at `w(1)` and give `m(1)` and `m(2)`: the critical pair
/// does not join, so `krun` names both rules with their written positions, the overlapped term
/// and the head that gets no value claim, before running. The rules of `v` do not overlap, and
/// nothing is said about them.
#[test]
fn a_pair_of_anywhere_rules_that_does_not_join_is_named_when_the_definition_is_loaded() {
    let (root, definition) = fixture();
    fs::write(&definition, NON_JOINING_ANYWHERE).unwrap();
    let compiled = root.join("compiled");
    kcompile_for_krun(
        &definition,
        &["--main-module", "NJ", "--syntax-module", "NJ"],
        &compiled,
    );
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["krun", "--definition"])
        .arg(&compiled)
        .args(["-s", "Pgm", "--io", "off", "-e", "v(1)"])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let stderr = String::from_utf8(output.stderr).unwrap();
    let warnings = stderr
        .lines()
        .filter(|line| line.contains("not shown to join"))
        .collect::<Vec<_>>();
    let position = |line: usize| format!("{}:{line}:3", definition.display());
    assert_eq!(warnings.len(), 1, "{stderr}");
    let warning = warnings[0];
    assert!(
        warning.starts_with("warning: the equations ")
            && warning.contains(&format!("NJ.w-one at {}", position(6)))
            && warning.contains(&format!("NJ.w-any at {}", position(7)))
            && warning.contains("the two reducts reach different terms")
            && warning.ends_with("no value claims are made for w(_)_NJ_Pgm_Int"),
        "{warning}"
    );
    assert!(!stderr.contains("v(_)_NJ_Pgm_Int"), "{stderr}");
}

/// `kcompile` reports the same pair when it compiles the definition, located at the first rule,
/// under the `ValueClaims` warning category: shown by default, and an error with
/// `--warnings-to-errors`. The rules of `v` get nothing.
#[test]
fn kcompile_names_a_pair_of_anywhere_rules_that_does_not_join_at_its_first_rule() {
    let (root, definition) = fixture();
    fs::write(&definition, NON_JOINING_ANYWHERE).unwrap();
    let options = ["--main-module", "NJ", "--syntax-module", "NJ"];
    let compiled = kcompile_for_krun(&definition, &options, &root.join("compiled"));
    let stderr = String::from_utf8(compiled.stderr).unwrap();
    let warnings = stderr
        .lines()
        .filter(|line| line.contains("[UnjoinedCriticalPair]"))
        .collect::<Vec<_>>();
    assert_eq!(warnings.len(), 1, "{stderr}");
    let warning = warnings[0];
    assert!(
        warning.starts_with(&format!(
            "{}:6:3: Warning[UnjoinedCriticalPair]: the equations NJ.w-one at ",
            definition.display()
        )) && warning.contains("the two reducts reach different terms")
            && warning.ends_with("no value claims are made for w(_)_NJ_Pgm_Int"),
        "{warning}"
    );
    assert!(!stderr.contains("v(_)_NJ_Pgm_Int"), "{stderr}");

    let promoted = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("kcompile")
        .arg(&definition)
        .args(options)
        .arg("--warnings-to-errors")
        .arg("--output-directory")
        .arg(root.join("promoted"))
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let promoted_stderr = String::from_utf8_lossy(&promoted.stderr);
    assert!(!promoted.status.success(), "{promoted_stderr}");
    assert_eq!(
        promoted_stderr
            .matches("Error[UnjoinedCriticalPair]")
            .count(),
        1,
        "{promoted_stderr}"
    );
}

const OVERLOADED_TEST: &str = r#"
module TEST
  imports DOMAINS
  syntax Foo ::= "foo"
  syntax Bar ::= Foo | "bar"
  syntax Bool ::= test(Foo) [function, overload(test)]
                | test(Bar) [function, overload(test)]
  rule test(foo) => true
  rule test(_)   => false
endmodule
"#;

/// The compiler makes the overload axiom `test(inj(X:Foo)) = inj(test(X))` of the two `test`
/// productions; it has no label, no unique id and no written position. Applied at `test(foo)` it
/// reaches `true` and the written `test(_) => false` reaches `false`, so the pair does not join.
/// The warning names the generated equation by the overloaded pair, and the diagnostic is
/// located at the written equation, the one of the two that has a position.
#[test]
fn kcompile_names_a_generated_overload_axiom_by_its_pair_and_locates_it_at_the_written_equation() {
    let (root, definition) = fixture();
    fs::write(&definition, OVERLOADED_TEST).unwrap();
    let options = ["--main-module", "TEST", "--syntax-module", "TEST"];
    let compiled = kcompile_for_krun(&definition, &options, &root.join("compiled"));
    let stderr = String::from_utf8(compiled.stderr).unwrap();
    let warnings = stderr
        .lines()
        .filter(|line| line.contains("[UnjoinedCriticalPair]"))
        .collect::<Vec<_>>();
    assert_eq!(warnings.len(), 1, "{stderr}");
    let warning = warnings[0];
    let written = format!("{}:9:3", definition.display());
    assert!(
        warning.starts_with(&format!(
            "{written}: Warning[UnjoinedCriticalPair]: the equations overload axiom of test(_)_TEST_Bool_Bar over test(_)_TEST_Bool_Foo and "
        )) && warning.contains(&format!(" at {written} overlap at ")),
        "{warning}"
    );
    assert!(!warning.contains("UNKNOWN"), "{warning}");
}

const ANYWHERE_ARGUMENTS: &str = r#"
module AA
  imports DOMAINS
  configuration <k> $PGM:Pgm </k>
  syntax Zero ::= "z"
  syntax Nat ::= Zero | s(Nat)
  syntax Wrap ::= h(Nat)
  syntax Pgm ::= Nat | f(Wrap) [function] | g(Wrap) [function] | k(Wrap) [function]
  rule [h-drop]: h(s(Y)) => h(Y) [anywhere]
  rule [f-any]: f(h(X)) => X
  rule [g-zero]: g(h(z)) => z
  rule [k-zero]: k(h(X:Zero)) => X
endmodule
"#;

/// An equation whose argument holds an anywhere head is consistent with the anywhere equations
/// when no instance of its argument pattern is rewritten by them (or each such rewrite gives the
/// same result). `f(h(X)) => X` is not: at `X = s(Y)` the axiom `h(s(Y)) = h(Y)` makes
/// `f(h(s(Y)))` equal both `s(Y)` and `f(h(Y))`, that is `Y`. `kcompile` names it at its rule,
/// as not shown consistent with `h-drop`. `g(h(z))` (ground, and `h(z)` is no instance of
/// `h(s(Y))`) and `k(h(X:Zero))` (an injected `Zero` is never an `s(_)` application) are normal on
/// every instance and get nothing.
#[test]
fn kcompile_names_an_equation_whose_argument_an_anywhere_rule_rewrites() {
    let (root, definition) = fixture();
    fs::write(&definition, ANYWHERE_ARGUMENTS).unwrap();
    let options = ["--main-module", "AA", "--syntax-module", "AA"];
    let compiled = kcompile_for_krun(&definition, &options, &root.join("compiled"));
    let stderr = String::from_utf8(compiled.stderr).unwrap();
    let warnings = stderr
        .lines()
        .filter(|line| line.contains("[UnjoinedCriticalPair]"))
        .collect::<Vec<_>>();
    assert_eq!(warnings.len(), 1, "{stderr}");
    let warning = warnings[0];
    let position = |line: usize| format!("{}:{line}:3", definition.display());
    assert!(
        warning.starts_with(&format!(
            "{}: Warning[UnjoinedCriticalPair]: the equation AA.f-any at {} is not shown consistent with the equation AA.h-drop at {}, which rewrites some instances of an argument of the first's left-hand side (at ",
            position(10),
            position(10),
            position(9)
        )) && warning.contains(
            "): the two results are not shown equal (the two reducts reach different terms)"
        ),
        "{warning}"
    );
    assert!(
        !stderr.contains("AA.g-zero") && !stderr.contains("AA.k-zero"),
        "{stderr}"
    );
}

/// The sequences of `ABSORB`: `seq` is an anywhere head whose one rule nests its own head on its
/// left-hand side, `(S1 ; a) ; S3 => S1 ; S3`. The rule's pair with itself and its in-argument
/// pairs join, so `seq` keeps its value claims.
const ABSORB: &str = r#"
module ABSORB
  syntax Stmt ::= "a" [symbol(a)] | "b" [symbol(b)] | "c" [symbol(c)] | "d" [symbol(d)]
                | "wrap" "(" Stmt ")" [symbol(wrap)]
                > Stmt ";" Stmt [symbol(seq), right]
  syntax Stmt ::= "(" Stmt ")" [bracket]
  configuration <k> $PGM:Stmt </k>
  rule (S1:Stmt ; a) ; S3:Stmt => S1 ; S3 [anywhere]
endmodule
"#;

/// `ABSORB` with a rewrite rule that builds `(b ; a) ; d` from `go`.
const ABSORB_GO: &str = r#"
module ABSORB-GO
  syntax Stmt ::= "a" [symbol(a)] | "b" [symbol(b)] | "c" [symbol(c)] | "d" [symbol(d)] | "go" [symbol(go)]
                > Stmt ";" Stmt [symbol(seq), right]
  syntax Stmt ::= "(" Stmt ")" [bracket]
  configuration <k> $PGM:Stmt </k>
  rule (S1:Stmt ; a) ; S3:Stmt => S1 ; S3 [anywhere]
  rule <k> go => (b ; a) ; d </k>
endmodule
"#;

/// `ABSORB` with a function whose first equation's argument is the ground `b ; a` and whose
/// second is `owise`.
const ABSORB_OWISE: &str = r#"
module ABSORB-OWISE
  imports INT
  syntax Stmt ::= "a" [symbol(a)] | "b" [symbol(b)] | "c" [symbol(c)] | "d" [symbol(d)]
                > Stmt ";" Stmt [symbol(seq), right]
  syntax Stmt ::= "(" Stmt ")" [bracket]
  syntax Exp ::= Int | "run" "(" Stmt ")" [symbol(run)]
  syntax Int ::= f(Stmt) [symbol(f), function]
  configuration <k> $PGM:Exp </k>
  rule (S1:Stmt ; a) ; S3:Stmt => S1 ; S3 [anywhere]
  rule f(b ; a) => 1
  rule f(_) => 2 [owise]
  rule run(S) => f(S)
endmodule
"#;

/// A reassociation whose first leaf is an `Atom`, beside the unit rule `a ; S => S`.
const ATOM_REASSOCIATION: &str = r#"
module ATOM
  syntax Atom ::= "a" [symbol(a)] | "b" [symbol(b)] | "c" [symbol(c)] | "d" [symbol(d)] | "e" [symbol(e)]
  syntax Stmt ::= Atom
                | "wrap" "(" Stmt ")" [symbol(wrap)]
                > Stmt ";" Stmt [symbol(seq), right]
  syntax Stmt ::= "(" Stmt ")" [bracket]
  configuration <k> $PGM:Stmt </k>
  rule a ; S:Stmt => S [anywhere]
  rule (A:Atom ; S2:Stmt) ; S3:Stmt => A ; S2 ; S3 [anywhere]
endmodule
"#;

/// The unrestricted reassociation beside the unit rule `a ; S => S`.
const REASSOCIATION: &str = r#"
module ANYWHERE
  syntax Stmt ::= "a" [symbol(a)] | "b" [symbol(b)] | "c" [symbol(c)] | "d" [symbol(d)]
                | "wrap" "(" Stmt ")" [symbol(wrap)]
                > Stmt ";" Stmt [symbol(seq), right]
  syntax Stmt ::= "(" Stmt ")" [bracket]
  configuration <k> $PGM:Stmt </k>
  rule a ; S:Stmt => S [anywhere]
  rule (S1:Stmt ; S2:Stmt) ; S3:Stmt => S1 ; S2 ; S3 [anywhere]
endmodule
"#;

/// `krust krun` of `source`, whose main and syntax module is `module`, on the program
/// `expression` of sort `sort`, with `extra` arguments: the standard output with every space and
/// line end removed, and the standard error.
fn krun_compact(
    source: &str,
    module: &str,
    sort: &str,
    expression: &str,
    extra: &[&str],
) -> (String, String) {
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("krun")
        .arg(&definition)
        .args(["--main-module", module, "--syntax-module", module])
        .args(["--sort", sort, "-e", expression])
        .args(extra)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(output.status.success(), "{expression}: {stderr}");
    fs::remove_dir_all(root).unwrap();
    (
        String::from_utf8(output.stdout)
            .unwrap()
            .split_whitespace()
            .collect(),
        stderr,
    )
}

/// The compact final configuration of a run with no constraint whose `<k>` cell holds the one
/// item `item`.
fn unconstrained_final(item: &str) -> String {
    format!(
        r#"Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}({item},dotk{{}}())),Lbl'-LT-'generatedCounter'-GT-'{{}}(\dv{{SortInt{{}}}}("0")))"#
    )
}

/// `(S1 ; a) ; S3 => S1 ; S3` nests `seq` on its own left-hand side, and every pair it makes
/// joins, so `seq` keeps its claims. In the normal-form model a step matches the inner `S1 ; a`
/// by its root, so `seq(b, a)` is a normal form there and `(b ; a) ; d` rewrites to `b ; d`,
/// also under `wrap`, with no definedness condition left and nothing warned.
#[test]
fn an_anywhere_rule_that_nests_its_own_head_rewrites_where_its_pairs_join() {
    for (expression, item) in [
        ("(b ; a) ; d", "Lblseq{}(Lblb{}(),Lbld{}())"),
        (
            "wrap((b ; a) ; d)",
            "Lblwrap{}(Lblseq{}(Lblb{}(),Lbld{}()))",
        ),
    ] {
        let (stdout, stderr) = krun_compact(ABSORB, "ABSORB", "Stmt", expression, &[]);
        assert_eq!(
            stdout,
            unconstrained_final(&format!("inj{{SortStmt{{}},SortKItem{{}}}}({item})")),
            "{expression}: {stderr}"
        );
        assert!(!stderr.contains("warning"), "{expression}: {stderr}");
    }
}

/// `(A:Atom ; S2) ; S3 => A ; S2 ; S3` has no overlap with itself (an `Atom` is never a
/// sequence) and joins with `a ; S => S`, so `seq` keeps its claims. Innermost evaluation
/// right-nests an inner sequence before the outer one is tried, so every nesting of `Atom`
/// leaves reaches the right-nested sequence, with no definedness condition left.
#[test]
fn a_reassociation_restricted_to_an_atom_first_leaf_reaches_the_right_nested_sequence() {
    let atom = |name: &str| format!("inj{{SortAtom{{}},SortStmt{{}}}}(Lbl{name}{{}}())");
    let right_nested = format!(
        "Lblseq{{}}({},Lblseq{{}}({},Lblseq{{}}({},{})))",
        atom("b"),
        atom("c"),
        atom("d"),
        atom("e")
    );
    for expression in ["((b ; c) ; d) ; e", "((a ; b) ; (c ; d)) ; e"] {
        let (stdout, stderr) = krun_compact(ATOM_REASSOCIATION, "ATOM", "Stmt", expression, &[]);
        assert_eq!(
            stdout,
            unconstrained_final(&format!(
                "inj{{SortStmt{{}},SortKItem{{}}}}({right_nested})"
            )),
            "{expression}: {stderr}"
        );
        assert!(!stderr.contains("warning"), "{expression}: {stderr}");
    }
}

/// Under `ABSORB`'s rule, `b ; a` is a normal form and `(b ; a) ; d` is `b ; d`, so `go`
/// rewrites once and ends at `b ; d`, and `b ; a`, which is not `go`, is final as it stands. A
/// rewrite rule is not applied under an equality between `go` and a sequence: each run has one
/// final leaf with no constraint, well within the depth bound.
#[test]
fn a_rewrite_rule_is_not_applied_under_an_equality_with_a_scanned_normal_form() {
    for (expression, item) in [
        ("go", "Lblseq{}(Lblb{}(),Lbld{}())"),
        ("b ; a", "Lblseq{}(Lblb{}(),Lbla{}())"),
    ] {
        let (stdout, stderr) = krun_compact(
            ABSORB_GO,
            "ABSORB-GO",
            "Stmt",
            expression,
            &["--depth", "5"],
        );
        assert_eq!(
            stdout,
            unconstrained_final(&format!("inj{{SortStmt{{}},SortKItem{{}}}}({item})")),
            "{expression}: {stderr}"
        );
    }
}

/// `b ; a` written in `f(b ; a) => 1` is a normal form of `ABSORB`'s rule, so it denotes one
/// value, distinct from `c` (another root) and from the normal form `b ; c`: `f` of those takes
/// the `owise` equation, and `f(b ; a)` the first, each with no definedness condition left.
#[test]
fn an_owise_equation_applies_past_a_ground_nested_anywhere_pattern() {
    for (expression, value) in [("run(c)", "2"), ("run(b ; c)", "2"), ("run(b ; a)", "1")] {
        let (stdout, stderr) = krun_compact(ABSORB_OWISE, "ABSORB-OWISE", "Exp", expression, &[]);
        assert_eq!(
            stdout,
            unconstrained_final(&format!(
                r#"inj{{SortInt{{}},SortKItem{{}}}}(\dv{{SortInt{{}}}}("{value}"))"#
            )),
            "{expression}: {stderr}"
        );
    }
}

/// The negative control of the root reading: the load does not show that the unrestricted
/// reassociation's pair with itself joins, so `seq` loses its claims, its applications keep
/// their open reading, and `(b ; c) ; d` stays as written under `\ceil(seq(b, c))`.
#[test]
fn a_reassociation_whose_head_is_withdrawn_keeps_the_nested_application_open() {
    let (stdout, stderr) = krun_compact(REASSOCIATION, "ANYWHERE", "Stmt", "(b ; c) ; d", &[]);
    assert!(
        stdout.contains(
            r"kseq{}(inj{SortStmt{},SortKItem{}}(Lblseq{}(Lblseq{}(Lblb{}(),Lblc{}()),Lbld{}())),dotk{}())"
        ) && stdout
            .contains(r"\ceil{SortStmt{},SortGeneratedTopCell{}}(Lblseq{}(Lblb{}(),Lblc{}()))"),
        "{stdout}"
    );
    assert!(
        stderr.contains("is not shown consistent with the equation")
            && stderr.contains("no value claims are made for seq"),
        "{stderr}"
    );
}

/// The unrestricted reassociation beside the unit rule, with a rewrite rule that rebuilds a
/// nested `seq` application from the constructor `go`.
const REASSOCIATION_GO: &str = r#"
module REASSOC-GO
  syntax Stmt ::= "a" [symbol(a)] | "b" [symbol(b)] | "c" [symbol(c)] | "d" [symbol(d)] | "go" [symbol(go)]
                > Stmt ";" Stmt [symbol(seq), right]
  syntax Stmt ::= "(" Stmt ")" [bracket]
  configuration <k> $PGM:Stmt </k>
  rule a ; S:Stmt => S [anywhere]
  rule (S1:Stmt ; S2:Stmt) ; S3:Stmt => S1 ; S2 ; S3 [anywhere]
  rule <k> go => (b ; c) ; d </k>
endmodule
"#;

/// While `seq` is withdrawn no application of it is a normal form, so the rule for the
/// constructor `go`, whose left-hand side is ground and binds no variable, applies to `b ; c`
/// under the undecided equality `go = b ; c`, beside the branch under its negation; its result
/// `(b ; c) ; d` is again an uncertified application, so the rule applies on every state it
/// builds. The run revisits the same states: three leaves at depth 2 and the same three at depth
/// 6, no minted existential. A rule that leaves a left-hand-side variable unbound halts on the
/// variable-free configuration instead.
#[test]
fn a_withdrawn_anywhere_head_makes_a_rebuilding_rule_branch_on_equalities() {
    let seq_bc = "Lblseq{}(Lblb{}(),Lblc{}())";
    let seq_bcd = format!("Lblseq{{}}({seq_bc},Lbld{{}}())");
    let leaf = |item: &str| {
        format!(
            r#"Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortStmt{{}},SortKItem{{}}}}({item}),dotk{{}}())),Lbl'-LT-'generatedCounter'-GT-'{{}}(\dv{{SortInt{{}}}}("0")))"#
        )
    };
    let equals = |right: &str| {
        format!(r"\equals{{SortStmt{{}},SortGeneratedTopCell{{}}}}(Lblgo{{}}(),{right})")
    };
    let not = |predicate: &str| format!(r"\not{{SortGeneratedTopCell{{}}}}({predicate})");
    let ceil = format!(r"\ceil{{SortStmt{{}},SortGeneratedTopCell{{}}}}({seq_bc})");
    let expected = format!(
        r"\or{{SortGeneratedTopCell{{}}}}(\and{{SortGeneratedTopCell{{}}}}({},{}),\and{{SortGeneratedTopCell{{}}}}({},\and{{SortGeneratedTopCell{{}}}}({ceil},{},{})),\and{{SortGeneratedTopCell{{}}}}({},\and{{SortGeneratedTopCell{{}}}}({ceil},{},{})))",
        leaf(seq_bc),
        not(&equals(seq_bc)),
        leaf(&seq_bcd),
        equals(seq_bc),
        not(&equals(&seq_bcd)),
        leaf(&seq_bcd),
        equals(seq_bc),
        equals(&seq_bcd),
    );
    let (depth_two, stderr) = krun_compact(
        REASSOCIATION_GO,
        "REASSOC-GO",
        "Stmt",
        "b ; c",
        &["--depth", "2"],
    );
    assert_eq!(depth_two, expected, "{stderr}");
    assert_eq!(
        depth_two.matches("Lbl'-LT-'generatedTop'-GT-'{}(").count(),
        3
    );
    assert!(!depth_two.contains("Ex-"), "{depth_two}");
    assert!(
        stderr.contains("no value claims are made for seq"),
        "{stderr}"
    );
    let (depth_six, stderr) = krun_compact(
        REASSOCIATION_GO,
        "REASSOC-GO",
        "Stmt",
        "b ; c",
        &["--depth", "6"],
    );
    assert_eq!(depth_six, depth_two, "{stderr}");

    let (root, _) = fixture();
    let unbound = compiled_for_execution(
        &root,
        "unbound",
        &REASSOCIATION_GO
            .replace("REASSOC-GO", "REASSOC-GO2")
            .replace(r#""go" [symbol(go)]"#, r#""go" "(" Stmt ")" [symbol(go)]"#)
            .replace(
                "rule <k> go => (b ; c) ; d </k>",
                "rule <k> go(X) => (X ; c) ; d </k>",
            ),
        "REASSOC-GO2",
        "REASSOC-GO2",
    );
    let output = bounded_krun(&unbound, "Stmt", "b ; c", &[]);
    assert_halts_uninstantiated(&output, 0, Some("Rule-hVarX"));
    fs::remove_dir_all(root).unwrap();
}

const SEVERAL_MATCHES: &str = r#"
module SM
  imports DOMAINS
  configuration <k> $PGM:Pgm </k>
  syntax Pgm ::= pick(Map) [function] | m(Int) | w(Int)
  rule [pick-any]: pick((K |-> _) _) => m(K)
  rule [w-one]: w(1) => m(1) [anywhere]
endmodule
"#;

/// `pick((K |-> _) _) => m(K)` matches `(1 |-> a) (2 |-> b)` with `K = 1` and with `K = 2`, so
/// the one equation gives two steps from one term, `m(1)` and `m(2)`: its pair with itself does
/// not join, and it withdraws the claims of the equation head `w`, whose values the map's values
/// can be. The equation was checked, so `krun` and `kcompile` name it as paired with itself and
/// say why, not as an equation the check skipped.
#[test]
fn an_equation_whose_map_pattern_matches_in_several_ways_is_named_as_paired_with_itself() {
    let (root, definition) = fixture();
    fs::write(&definition, SEVERAL_MATCHES).unwrap();
    let options = ["--main-module", "SM", "--syntax-module", "SM"];
    let compiled = root.join("compiled");
    let compilation = kcompile_for_krun(&definition, &options, &compiled);
    let expected = format!(
        "the equation SM.pick-any at {}:6:3 paired with itself is not shown to join: its map or set pattern can match one collection in several ways, and its right-hand side and `ensures` are not shown to read only variables that every matching binds alike; no value claims are made for w(_)_SM_Pgm_Int",
        definition.display()
    );

    let compile_stderr = String::from_utf8(compilation.stderr).unwrap();
    let diagnostics = compile_stderr
        .lines()
        .filter(|line| line.contains("[UnjoinedCriticalPair]"))
        .collect::<Vec<_>>();
    assert_eq!(
        diagnostics,
        [format!(
            "{}:6:3: Warning[UnjoinedCriticalPair]: {expected}",
            definition.display()
        )],
        "{compile_stderr}"
    );

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["krun", "--definition"])
        .arg(&compiled)
        .args(["-s", "Pgm", "--io", "off", "-e", "w(2)"])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let stderr = String::from_utf8(output.stderr).unwrap();
    let warnings = stderr
        .lines()
        .filter(|line| line.contains("SM.pick-any"))
        .collect::<Vec<_>>();
    assert_eq!(warnings, [format!("warning: {expected}")], "{stderr}");
    assert!(!stderr.contains("is not checked"), "{stderr}");
}

const REQUIRES_ON_A_MATCHING: &str = r#"
module RM
  imports DOMAINS
  configuration <k> $PGM:Pgm </k>
  syntax Pgm ::= f(Map) [function] | g(Map) [function] | mk(Int)
  rule f((K |-> _) _) => mk(1) requires K ==Int 2
  rule f(_) => mk(2) [owise]
  rule g((K |-> _) _) => mk(1) requires K ==Int 1
  rule g(_) => mk(2) [owise]
endmodule
"#;

/// `f((K |-> _) _) => mk(1) requires K ==Int 2` matches `1 |-> 0 2 |-> 0` with `K = 1` and with
/// `K = 2`; the instance `K = 2` applies, so `f` of that map is `mk(1)` in every model and the
/// `owise` rule does not apply there. `krun` tries each matching until one satisfies the
/// `requires`, whichever comes first (`g` asks for the other key); it used to decide the
/// `requires` on the first matching only and print `mk(2)` for one of them. A map neither
/// matching satisfies still reaches the `owise` rule.
#[test]
fn a_function_rule_applies_when_any_matching_of_its_map_pattern_satisfies_its_requires() {
    let (root, definition) = fixture();
    fs::write(&definition, REQUIRES_ON_A_MATCHING).unwrap();
    let compiled = root.join("compiled");
    kcompile_for_krun(
        &definition,
        &["--main-module", "RM", "--syntax-module", "RM"],
        &compiled,
    );
    for (program, result) in [
        ("f(1 |-> 0 2 |-> 0)", 1),
        ("g(1 |-> 0 2 |-> 0)", 1),
        ("f(1 |-> 0 3 |-> 0)", 2),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["krun", "--definition"])
            .arg(&compiled)
            .args(["-s", "Pgm", "--io", "off", "-e", program])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert!(output.status.success(), "{program}: {output:?}");
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(
            stdout.contains(&format!(
                r#"Lblmk'LParUndsRParUnds'RM'Unds'Pgm'Unds'Int{{}}(\dv{{SortInt{{}}}}("{result}"))"#
            )),
            "{program}: {stdout}"
        );
    }
}

/// An equation of a function declared `total` that reduces an application of it to bottom
/// contradicts the attribute on that input (KK-81 probe). `krun` and `kprove` keep their
/// outcomes (an undefined step; a failed claim with a `Vacuous` leaf, and a symbolic claim still
/// proven, since the attribute is trusted), and name the symbol by its K label, the equation and
/// its position.
/// A partial function, or an argument that is bottom before the equation fires, names nothing;
/// a nested total application names the innermost equation, and a total function whose equation
/// calls a partial one names its own.
#[test]
fn a_contradicted_total_attribute_is_named_without_changing_the_outcome() {
    let (root, definition) = fixture();
    fs::write(&definition, CONTRADICTED_TOTAL).unwrap();
    let compiled = root.join("compiled");
    kcompile_for_krun(
        &definition,
        &["--main-module", "CTOT", "--syntax-module", "CTOT"],
        &compiled,
    );
    let run = |program: &str| {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["krun", "--definition"])
            .arg(&compiled)
            .args(["-s", "Pgm", "--io", "off", "-e", program])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert!(output.status.success(), "{program}: {output:?}");
        let stdout = String::from_utf8(output.stdout).unwrap();
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(
            stderr.contains("execution ended with no successor at depth 1")
                && stdout.contains("\\bottom{SortGeneratedTopCell{}}()"),
            "{program}: {stdout}{stderr}"
        );
        stderr
    };
    let position = |line: usize| format!("{}:{line}:3", definition.display());
    for (program, symbol, equation, line) in [
        ("tdiv", "tDiv(_)_CTOT_Int_Int", "tdiv-eq", 12),
        ("tnest", "tDiv(_)_CTOT_Int_Int", "tdiv-eq", 12),
        ("tvia", "tVia(_)_CTOT_Int_Int", "tvia-eq", 15),
        ("tset", "tAdd(_,_)_CTOT_Set_Set_Int", "tadd-eq", 19),
        (
            "tmapdiff",
            "tPut(_,_,_)_CTOT_Map_Map_Int_Int",
            "tput-eq",
            22,
        ),
    ] {
        let stderr = run(program);
        let message = stderr
            .lines()
            .find(|line| line.contains("attribute of"))
            .unwrap_or_else(|| panic!("{program}: no contradicted-total warning in {stderr}"));
        assert!(
            message.starts_with(&format!(
                "warning: the `total` attribute of {symbol} is contradicted"
            )) && message.contains("is contradicted on this input")
                && message.contains(&format!("CTOT.{equation} at {}", position(line)))
                && message.contains("to bottom"),
            "{program}: {message}"
        );
    }
    for program in ["pdiv", "pset", "targ"] {
        let stderr = run(program);
        assert!(!stderr.contains("attribute of"), "{program}: {stderr}");
    }

    let spec = root.join("ctot-spec.k");
    fs::write(&spec, CONTRADICTED_TOTAL_SPEC).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            spec.to_str().unwrap(),
            "--main-module",
            "CTOT-SPEC",
            "--definition-module",
            "CTOT",
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(!output.status.success(), "{stdout}");
    // The report of one claim: its verdict line and the lines that follow up to the next claim.
    let report = |claim: &str| {
        let prefix = format!("claim CTOT-SPEC.{claim}: ");
        let start = stdout
            .find(&prefix)
            .unwrap_or_else(|| panic!("no {claim} verdict in {stdout}"));
        let rest = &stdout[start + prefix.len()..];
        rest[..rest.find("\nclaim ").unwrap_or(rest.len())].to_owned()
    };
    assert!(report("sym").starts_with("proven"), "{stdout}");
    for claim in ["gnd", "div"] {
        let report = report(claim);
        assert!(
            report.starts_with("failed")
                && report.contains("vacuous at depth 1")
                && report.contains("attribute of")
                && report.contains("is contradicted on this input"),
            "{claim}: {report}"
        );
    }
    assert!(report("gnd").contains("CTOT.tadd-eq"), "{stdout}");
    assert!(report("div").contains("CTOT.tdiv-eq"), "{stdout}");
    for claim in ["psym", "pgnd", "pdiv"] {
        let report = report(claim);
        assert!(
            report.starts_with("failed")
                && report.contains("trivial at depth 1")
                && !report.contains("attribute of"),
            "{claim}: {report}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

#[cfg(feature = "z3-inference")]
#[test]
fn kprove_does_not_certify_a_stuck_leaf_from_an_uninterpreted_smtlib_model() {
    let (root, _) = fixture();
    fs::write(
        root.join("andint.k"),
        include_str!("fixtures/kink/andint/andint.k"),
    )
    .unwrap();
    let specification = root.join("andint-spec.k");
    fs::write(
        &specification,
        include_str!("fixtures/kink/andint/andint-spec.k"),
    )
    .unwrap();

    // Both claims are proven by their own process on one compiled specification.
    let compiled = root.join("compiled");
    kcompile_for_proving(&specification, "ANDINT-SPEC", "ANDINT", &compiled);
    for (claim, verdict, certified) in
        [("vacuous", "failed", false), ("control", "disproved", true)]
    {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["kprove", "--compiled-definition"])
            .arg(&compiled)
            .args([
                "--main-module",
                "ANDINT-SPEC",
                "--definition-module",
                "ANDINT",
                "--claim",
                claim,
            ])
            .output()
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(!output.status.success(), "{stdout}");
        assert!(
            stdout.contains(&format!("claim ANDINT-SPEC.{claim}: {verdict}")),
            "{stdout}"
        );
        assert_eq!(stdout.contains("stuck (certified)"), certified, "{stdout}");
    }
    fs::remove_dir_all(root).unwrap();
}

/// `stay(X)` under `X &Int 1 ==Int 2` is empty, so it implies anything; `andInt` is an
/// uninterpreted `smtlib` function, so the solver's `Sat` for it is no instance and the answer is
/// `unknown`, never `invalid`. Under `X +Int 1 ==Int 2` the antecedent has the instance `X = 1`,
/// so the refutations stay `invalid`.
#[cfg(feature = "z3-inference")]
#[test]
fn kore_implies_reports_invalid_only_for_an_antecedent_shown_nonempty() {
    let (root, _) = fixture();
    let source = root.join("andint.k");
    fs::write(&source, include_str!("fixtures/kink/andint/andint.k")).unwrap();
    let compiled = root.join("compiled");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kcompile", source.to_str().unwrap(), "-m", "ANDINT", "-o"])
        .arg(&compiled)
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    let patterns = [
        ("ant", include_str!("fixtures/kink/andint/ant.kore")),
        ("con", include_str!("fixtures/kink/andint/con.kore")),
        ("ant0", include_str!("fixtures/kink/andint/ant0.kore")),
        ("con0", include_str!("fixtures/kink/andint/con0.kore")),
        ("bottom", r#"\bottom{SortKItem{}}()"#),
    ];
    for (name, pattern) in patterns {
        fs::write(root.join(format!("{name}.kore")), pattern).unwrap();
        fs::write(
            root.join(format!("not-{name}.kore")),
            format!(r#"\not{{SortKItem{{}}}}({})"#, pattern.trim()),
        )
        .unwrap();
    }

    for (antecedent, consequent, status, predicate) in [
        ("ant", "con", "unknown", Some("Bottom")),
        ("ant0", "con0", "invalid", Some("Bottom")),
        ("ant", "bottom", "unknown", Some("Bottom")),
        ("ant0", "bottom", "invalid", Some("Bottom")),
        // `A -> \not C` is invalid exactly when `A /\ C` is nonempty: `stay(1)` is common to
        // `ant0` and itself, `X +Int 1` is 2 and 3 on no shared `X`, and the solver's `Sat` for
        // the uninterpreted `X &Int 1 ==Int 2` shows no common value.
        ("ant0", "not-ant0", "invalid", None),
        ("ant0", "not-con0", "valid", Some("Top")),
        ("ant", "not-ant", "unknown", None),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["kore-implies"])
            .arg(compiled.join("definition.kore"))
            .args(["--module", "ANDINT", "--antecedent"])
            .arg(root.join(format!("{antecedent}.kore")))
            .arg("--consequent")
            .arg(root.join(format!("{consequent}.kore")))
            .env("KRUST_COUNTERS", root.join("implies-counters.json"))
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{antecedent} => {consequent}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let output: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(
            output["status"], status,
            "{antecedent} => {consequent}: {output:#}"
        );
        #[cfg(feature = "measure")]
        if antecedent == "ant0" && consequent == "con0" {
            let counters: serde_json::Value =
                serde_json::from_slice(&fs::read(root.join("implies-counters.json")).unwrap())
                    .unwrap();
            assert!(counters["counters"]["smt.queries"].as_u64().unwrap() > 0);
        }
        match predicate {
            Some(predicate) => assert_eq!(
                output["condition"]["predicate"]["term"]["tag"], predicate,
                "{antecedent} => {consequent}: {output:#}"
            ),
            None => assert!(
                output.get("condition").is_none(),
                "{antecedent} => {consequent}: {output:#}"
            ),
        }
    }
    fs::remove_dir_all(root).unwrap();
}

/// A pattern with a free variable of an empty sort denotes nothing: `hold(V:Void)`, with no
/// production building a `Void`, is a vacuous left-hand side, so its claim is never disproved.
/// The same claim over `Int` has a stuck instance and is.
#[cfg(feature = "z3-inference")]
#[test]
fn kprove_does_not_certify_a_stuck_leaf_over_an_empty_sort() {
    let (root, _) = fixture();
    fs::write(
        root.join("void.k"),
        include_str!("fixtures/kink/void/void.k"),
    )
    .unwrap();
    let specification = root.join("void-spec.k");
    fs::write(
        &specification,
        include_str!("fixtures/kink/void/void-spec.k"),
    )
    .unwrap();

    // Both claims are proven by their own process on one compiled specification.
    let compiled = root.join("compiled");
    kcompile_for_proving(&specification, "VOID-SPEC", "VOID", &compiled);
    for (claim, verdict, certified) in
        [("vacuous", "failed", false), ("control", "disproved", true)]
    {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["kprove", "--compiled-definition"])
            .arg(&compiled)
            .args([
                "--main-module",
                "VOID-SPEC",
                "--definition-module",
                "VOID",
                "--claim",
                claim,
            ])
            .output()
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(!output.status.success(), "{stdout}");
        assert!(
            stdout.contains(&format!("claim VOID-SPEC.{claim}: {verdict}")),
            "{stdout}"
        );
        assert_eq!(stdout.contains("stuck (certified)"), certified, "{stdout}");
    }
    fs::remove_dir_all(root).unwrap();
}

/// A destination whose condition is false on the reached state covers none of it, so the whole
/// state is a stuck leaf. It is never reported as a vacuous branch, so `--allow-vacuous` cannot
/// turn these false claims into proofs, and the leaf is the same with or without the stuck check
/// because no rule applies to it.
#[test]
fn kprove_reports_a_refuted_destination_condition_as_a_stuck_leaf() {
    let (root, _) = fixture();
    fs::write(
        root.join("exist-probe.k"),
        r#"
module EXIST-PROBE
  imports INT
  syntax State ::= "start" | st(Int, Int) | "done"
  configuration <k> $PGM:State </k>
  rule <k> start => st(!N:Int, 7) </k>
endmodule
"#,
    )
    .unwrap();
    fs::write(
        root.join("exist-spec.k"),
        r#"
requires "exist-probe.k"

module EXIST-SPEC
  imports EXIST-PROBE

  claim <k> start => st(?B:Int, ?A:Int) </k> ensures ?A ==Int 8 [label(ab-false)]
endmodule
"#,
    )
    .unwrap();
    fs::write(
        root.join("cell-probe.k"),
        r#"
module CELL-PROBE
  imports INT
  syntax State ::= "start" | "middle"
  configuration <k> $PGM:State </k> <n> 0 </n>
  rule <k> start => middle </k> <n> _ => 5 </n>
endmodule
"#,
    )
    .unwrap();
    fs::write(
        root.join("ex-spec.k"),
        r#"
requires "cell-probe.k"

module EX-SPEC
  imports CELL-PROBE

  claim <k> start => middle </k> <n> _ => ?N </n> ensures ?N ==Int 7 [label(existential-wrong)]
endmodule
"#,
    )
    .unwrap();

    // `ab-false` fails without a certified refutation: its leaf's generated counter holds the
    // unevaluated function application `Gen0 +Int 1`. The leaf of `existential-wrong` is a
    // term of constructors and integers with no constraint, a certified refutation.
    let cases = [
        (
            "exist-spec.k",
            "EXIST-SPEC",
            "EXIST-PROBE",
            "ab-false",
            "Lblst'LParUndsCommUndsRParUnds'EXIST-PROBE",
            ("failed", "stuck at depth 1"),
        ),
        (
            "ex-spec.k",
            "EX-SPEC",
            "CELL-PROBE",
            "existential-wrong",
            "Lbl'-LT-'n'-GT-'{}(\\dv{SortInt{}}(\"5\"))",
            ("disproved", "stuck (certified) at depth 1"),
        ),
    ];
    for (specification, module, definition_module, claim, leaf_term, (verdict, leaf)) in cases {
        // The four flag sets are proof options: one compilation serves them all.
        let compiled = root.join(format!("{module}-compiled"));
        kcompile_for_proving(
            &root.join(specification),
            module,
            definition_module,
            &compiled,
        );
        for flags in [
            &[][..],
            &["--allow-vacuous"][..],
            &["--disable-stuck-check"][..],
            &["--allow-vacuous", "--disable-stuck-check"][..],
        ] {
            let output = Command::new(env!("CARGO_BIN_EXE_krust"))
                .args(["kprove", "--compiled-definition"])
                .arg(&compiled)
                .args([
                    "--main-module",
                    module,
                    "--definition-module",
                    definition_module,
                    "--depth",
                    "10",
                    "--claim",
                    claim,
                ])
                .args(flags)
                .stdin(Stdio::null())
                .output()
                .unwrap();
            let stdout = String::from_utf8(output.stdout).unwrap();
            let context = format!(
                "{claim} {flags:?}: {stdout}\n{}",
                String::from_utf8_lossy(&output.stderr)
            );

            assert!(!output.status.success(), "{context}");
            assert!(
                stdout.contains(&format!("claim {claim}: {verdict}")),
                "{context}"
            );
            let leaves = stdout
                .lines()
                .filter(|line| line.contains(" at depth "))
                .map(str::trim)
                .collect::<Vec<_>>();
            assert_eq!(leaves, [leaf], "{context}");
            assert!(stdout.contains(leaf_term), "{context}");
            assert!(!stdout.contains("--allow-vacuous accepts"), "{context}");
        }
    }
    fs::remove_dir_all(root).unwrap();
}

/// An unproven leaf is printed by the name the host wire gives its outcome, and a leaf whose
/// outcome has a reason in words prints it, every line of it indented as the leaf's line, before
/// the configuration. Here the state's step reaches an application of a hook no evaluator or
/// equation reduces, so the leaf is indeterminate whatever the solver.
#[test]
fn kprove_names_a_leaf_outcome_and_states_its_detail() {
    let (root, _) = fixture();
    let definition = root.join("hooked.kore");
    fs::write(
        &definition,
        r#"[]
module MAIN
    sort SortS{} []
    symbol a{}() : SortS{} [constructor{}()]
    symbol c{}() : SortS{} [constructor{}()]
    hooked-symbol f{}(SortS{}) : SortS{} [function{}(), hook{}("NOSUCH.hook")]
    alias weakAlwaysFinally{S}(S) : S
        where weakAlwaysFinally{S}(@X:S) := @X:S []
    axiom{} \rewrites{SortS{}}(
        \and{SortS{}}(a{}(), \top{SortS{}}()),
        f{}(a{}())
    ) [label{}("to-hook")]
    claim{} \implies{SortS{}}(
        \and{SortS{}}(a{}(), \top{SortS{}}()),
        weakAlwaysFinally{SortS{}}(c{}())
    ) [label{}("hooked-claim")]
endmodule []
"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kprove", "--compiled-definition"])
        .arg(&definition)
        .args(["--main-module", "MAIN"])
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "claim hooked-claim: indeterminate (1 states, 0 unexplored)\n\
         \x20 indeterminate at depth 0\n\
         \x20 unsupported hook 'NOSUCH.hook' on constructor-like arguments: no evaluator in this \
         backend, and no equation of the definition applies\n\
         \x20 f{}(a{}())\n\
         \x20   a{}()\n"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_recalls_the_same_claim_from_another_spec_module() {
    let (root, _) = fixture();
    let saved_proofs = root.join("proofs.kore");
    let semantics = root.join("semantics.k");
    let first_spec = root.join("first-spec.k");
    let second_spec = root.join("second-spec.k");
    fs::write(
        &semantics,
        r#"
module SEMANTICS
  syntax State ::= "a" [symbol(a)]
                 | "b" [symbol(b)]
  configuration <k> $PGM:State </k>
  rule <k> a => b </k>
endmodule
"#,
    )
    .unwrap();
    fs::write(
        &first_spec,
        r#"
requires "semantics.k"
module FIRST-SPEC
  imports SEMANTICS
  claim <k> a => b </k>
endmodule
"#,
    )
    .unwrap();
    fs::write(
        &second_spec,
        r#"
requires "semantics.k"
module SECOND-SPEC
  imports SEMANTICS
  claim <k> a => b </k>
endmodule
"#,
    )
    .unwrap();

    let first = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            first_spec.to_str().unwrap(),
            "--main-module",
            "FIRST-SPEC",
            "--definition-module",
            "SEMANTICS",
            "--save-proofs",
            saved_proofs.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        first.status.success(),
        "{}",
        String::from_utf8_lossy(&first.stderr)
    );

    let second = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            second_spec.to_str().unwrap(),
            "--main-module",
            "SECOND-SPEC",
            "--definition-module",
            "SEMANTICS",
            "--save-proofs",
            saved_proofs.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        second.status.success(),
        "{}",
        String::from_utf8_lossy(&second.stderr)
    );
    assert_eq!(
        String::from_utf8(second.stdout).unwrap(),
        "claim #1: proven (saved)\n"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_handles_generated_concreteness_constraints() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax Int ::= abs(Int) [function, total]
               | "error" [function, total]
  rule abs(X:Int) => X:Int requires X >Int 0
  rule abs(X) => 0 -Int X [owise]
  rule abs(0) => error [simplification]
  configuration <k> $PGM:Int </k>
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "Int",
            "--expression",
            "abs(0)",
            "--depth",
            "20",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains(r#"\dv{SortInt{}}("0")"#), "{output}");
    assert!(!output.contains("Lblerror{}()"), "{output}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_simplifies_partial_rhs_functions_before_definedness() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax Pgm ::= run(Int)
  syntax Num ::= Int
               | inc(Num) [function]
               | foo(Num) [function]
  rule run(3) => foo(inc(333))
  rule inc(I:Int) => I +Int 1 [concrete]
  rule foo(I) => I
  configuration <k> $PGM:Pgm </k>
endmodule
"#,
    )
    .unwrap();

    // Both simplification budgets run one compiled definition.
    let compiled = root.join("compiled");
    kcompile_for_krun(&definition, &["--main-module", "MAIN"], &compiled);
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["krun", "--definition"])
        .arg(&compiled)
        .args(["--sort", "Pgm", "--expression", "run(3)", "--depth", "20"])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains(r#"\dv{SortInt{}}("334")"#), "{output}");
    assert!(!output.contains("Lblinc"), "{output}");
    assert!(!output.contains("Lblfoo"), "{output}");

    let limited = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["krun", "--definition"])
        .arg(&compiled)
        .args([
            "--sort",
            "Pgm",
            "--expression",
            "run(3)",
            "--depth",
            "20",
            "--max-simplification-iterations",
            "1",
        ])
        .output()
        .unwrap();
    assert!(
        limited.status.success(),
        "{}",
        String::from_utf8_lossy(&limited.stderr)
    );
    let output = String::from_utf8(limited.stdout).unwrap();
    assert!(output.contains(r#"\dv{SortInt{}}("334")"#), "{output}");
    assert!(!output.contains("Lblinc"), "{output}");
    assert!(!output.contains("Lblfoo"), "{output}");

    fs::remove_dir_all(root).unwrap();
}

/// `run(I) => stuck(I)` rewrites although `stuck(1)` cannot be evaluated: the rewrite carries
/// `\ceil(stuck(1))` as an obligation instead of blocking. The leaf is printed in the
/// simplifier's normal form, where that conjunct is entailed by the term (`stuck(1)` sits under
/// total symbols only, and application is strict), so the output shows the unevaluated
/// application and no `\ceil` conjunct.
#[test]
fn krun_rewrites_to_an_unevaluated_partial_application_in_normal_form() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax Pgm ::= run(Int)
  syntax Num ::= Int | stuck(Num) [function]
  rule run(I) => stuck(I)
  configuration <k> $PGM:Pgm </k>
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "Pgm",
            "--expression",
            "run(1)",
            "--depth",
            "20",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains("Lblstuck"), "{output}");
    assert!(!output.contains("Lblrun"), "{output}");
    assert!(!output.contains(r"\ceil"), "{output}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_recovers_evaluable_collection_function_patterns() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports LIST
  imports INT
  configuration <k> $PGM:K </k>
                <list> ListItem(0) ListItem(1) ListItem(2) </list>
  syntax KItem ::= l(Int, Int)
  rule <k> l(I, J) => .K ...</k>
       <list> _ [ I <- J ] </list>
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "KItem",
            "--expression",
            "l(1, 1)",
            "--depth",
            "20",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains("Lbl'-LT-'k'-GT-'{}(dotk{}())"), "{output}");
    assert!(output.contains(r#"\dv{SortInt{}}("2")"#), "{output}");
    assert!(!output.contains("Lbll'LPar"), "{output}");

    fs::remove_dir_all(root).unwrap();
}

/// A list update whose list argument the rule reads elsewhere would bind it to one of the many
/// lists that differ from the subject at the index, so the definition checks reject it.
#[test]
fn krun_rejects_a_list_update_whose_updated_list_the_rule_reads() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports LIST
  imports INT
  configuration <k> $PGM:K </k>
                <list> ListItem(0) ListItem(1) ListItem(2) </list>
  syntax KItem ::= l(Int, Int) | wrapped(List)
  rule <k> l(I, J) => wrapped(L) ...</k>
       <list> L [ I <- J ] </list>
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "KItem",
            "--expression",
            "l(1, 1)",
            "--depth",
            "20",
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Error[IllegalFunctionOnLhs]: Illegal function symbol List:set"),
        "{stderr}"
    );
    assert!(output.stdout.is_empty());

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_emits_k_user_logs_on_standard_error() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports K-IO
  imports STRING
  configuration <k> $PGM:K </k>
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--syntax-module",
            "MAIN",
            "--sort",
            "K",
            "--expression",
            r#"#log("hello from K")"#,
            "--depth",
            "20",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8(output.stderr).unwrap(), "hello from K\n");
    let stdout = String::from_utf8(output.stdout).unwrap();
    let compact: String = stdout
        .chars()
        .filter(|character| !character.is_whitespace())
        .collect();
    assert!(compact.contains("Lbl'-LT-'k'-GT-'{}(dotk{}())"), "{stdout}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kcompile_writes_parseable_kore_outputs() {
    let (root, definition) = fixture();
    let output_directory = root.join("compiled");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--output-directory",
            output_directory.to_str().unwrap(),
            "--no-prelude",
            "--emit-json",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    for name in ["definition.kore", "syntaxDefinition.kore"] {
        let source = fs::read_to_string(output_directory.join(name)).unwrap();
        let parsed = parse_definition(&source).unwrap_or_else(|error| panic!("{name}: {error}"));
        assert_eq!(
            parsed
                .modules
                .iter()
                .map(|module| module.name.as_str())
                .collect::<Vec<_>>(),
            ["BASIC-K", "KSEQ", "INJ", "K", "MAIN"],
        );
        assert!(source.contains("Source("));
        if name == "definition.kore" {
            assert_eq!(source.matches("simplification{}()").count(), 3);
        }
    }
    assert!(
        fs::read_to_string(output_directory.join("macros.kore"))
            .unwrap()
            .trim()
            .is_empty()
    );
    let parsed = k_rust::definition::json::from_str(
        &fs::read_to_string(output_directory.join("parsed.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(parsed.main_module, "MAIN");
    assert_eq!(parsed.attributes.get_str("syntaxModule"), Some("MAIN"));
    assert_eq!(
        parsed
            .modules
            .iter()
            .map(|module| module.name.as_str())
            .collect::<Vec<_>>(),
        ["BASE", "MAIN"],
    );

    fs::remove_dir_all(root).unwrap();
}

#[cfg(unix)]
#[test]
fn kcompile_generates_a_relocatable_glr_program_parser() {
    use std::os::unix::ffi::OsStringExt;
    use std::os::unix::fs::PermissionsExt;

    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module BISON
  syntax Number ::= r"[A-Z]+" [token]
  syntax Pgm ::= Number
               | Pgm "+" Pgm [symbol(add), group(add)]
               | Pgm "*" Pgm [symbol(mul), group(mul)]
  syntax priority mul > add
  syntax left add
  syntax left mul
  configuration <k> $PGM:Pgm </k>
endmodule
"#,
    )
    .unwrap();
    let output_name = std::ffi::OsString::from_vec(b"bison-\xff-kompiled".to_vec());
    let output_directory = root.join(&output_name);
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .current_dir(&root)
        .args([
            "kcompile",
            definition.file_name().unwrap().to_str().unwrap(),
            "--main-module",
            "BISON",
            "--syntax-module",
            "BISON",
            "--output-directory",
        ])
        .arg(&output_name)
        .arg("--gen-glr-bison-parser")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let primary = output_directory.join("parser_Pgm_BISON");
    let link = output_directory.join("parser_PGM");
    assert!(primary.is_file());
    assert_eq!(fs::read_link(&link).unwrap(), Path::new("parser_Pgm_BISON"));

    let input = root.join("input.pgm");
    fs::write(&input, "A+B*C\n").unwrap();
    let parsed = Command::new(&link).arg(&input).output().unwrap();
    assert!(
        parsed.status.success(),
        "{}",
        String::from_utf8_lossy(&parsed.stderr)
    );
    assert_eq!(
        String::from_utf8(parsed.stdout).unwrap(),
        "Lbladd{}(inj{SortNumber{}, SortPgm{}}(\\dv{SortNumber{}}(\"A\")),Lblmul{}(inj{SortNumber{}, SortPgm{}}(\\dv{SortNumber{}}(\"B\")),inj{SortNumber{}, SortPgm{}}(\\dv{SortNumber{}}(\"C\"))))\n"
    );

    let original_primary = fs::read(&primary).unwrap();
    let failing_cc = root.join("failing-cc");
    fs::write(
        &failing_cc,
        "#!/bin/sh\necho controlled-cc-failure >&2\nexit 23\n",
    )
    .unwrap();
    fs::set_permissions(&failing_cc, fs::Permissions::from_mode(0o755)).unwrap();
    let failed_replacement = Command::new(env!("CARGO_BIN_EXE_krust"))
        .current_dir(&root)
        .args([
            "kcompile",
            definition.file_name().unwrap().to_str().unwrap(),
            "--main-module",
            "BISON",
            "--syntax-module",
            "BISON",
            "--output-directory",
        ])
        .arg(&output_name)
        .arg("--gen-glr-bison-parser")
        .env("KRUST_CC", &failing_cc)
        .output()
        .unwrap();
    assert!(!failed_replacement.status.success());
    assert!(
        String::from_utf8_lossy(&failed_replacement.stderr)
            .contains("C compiler failed with exit code 23: controlled-cc-failure")
    );
    assert_eq!(fs::read(&primary).unwrap(), original_primary);
    assert_eq!(fs::read_link(&link).unwrap(), Path::new("parser_Pgm_BISON"));
    assert!(fs::read_dir(&output_directory).unwrap().all(|entry| {
        !entry
            .unwrap()
            .file_name()
            .to_string_lossy()
            .starts_with(".krust-bison")
    }));

    let replacement = Command::new(env!("CARGO_BIN_EXE_krust"))
        .current_dir(&root)
        .args([
            "kcompile",
            definition.file_name().unwrap().to_str().unwrap(),
            "--main-module",
            "BISON",
            "--syntax-module",
            "BISON",
            "--output-directory",
        ])
        .arg(&output_name)
        .args(["--gen-bison-parser", "--bison-stack-max-depth", "4321"])
        .output()
        .unwrap();
    assert!(
        replacement.status.success(),
        "{}",
        String::from_utf8_lossy(&replacement.stderr)
    );
    assert_eq!(fs::read_link(&link).unwrap(), Path::new("parser_Pgm_BISON"));
    let parsed = Command::new(&link).arg(&input).output().unwrap();
    assert!(
        parsed.status.success(),
        "{}",
        String::from_utf8_lossy(&parsed.stderr)
    );
    assert_eq!(
        String::from_utf8(parsed.stdout).unwrap(),
        "Lbladd{}(inj{SortNumber{}, SortPgm{}}(\\dv{SortNumber{}}(\"A\")),Lblmul{}(inj{SortNumber{}, SortPgm{}}(\\dv{SortNumber{}}(\"B\")),inj{SortNumber{}, SortPgm{}}(\\dv{SortNumber{}}(\"C\"))))\n"
    );

    let relocated = root.join("relocated");
    fs::rename(&output_directory, &relocated).unwrap();
    let parsed = Command::new(relocated.join("parser_PGM"))
        .arg(&input)
        .output()
        .unwrap();
    assert!(
        parsed.status.success(),
        "{}",
        String::from_utf8_lossy(&parsed.stderr)
    );

    fs::remove_dir_all(root).unwrap();
}

#[cfg(unix)]
#[test]
fn kcompile_generates_a_glr_parser_shared_library() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module BISON
  syntax Number ::= r"[A-Z]+" [token]
  syntax Pgm ::= Number
  configuration <k> $PGM:Pgm </k>
endmodule
"#,
    )
    .unwrap();
    let library_directory = root.join("library-kompiled");
    let executable_directory = root.join("executable-kompiled");
    let run = |directory: &Path, extra: &[&str]| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "BISON",
            "--syntax-module",
            "BISON",
            "--output-directory",
            directory.to_str().unwrap(),
            "--gen-glr-bison-parser",
        ]);
        command.args(extra);
        let output = command.output().unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    };
    run(&library_directory, &["--bison-parser-library"]);
    run(&executable_directory, &[]);

    let library_name = format!("libparser_Pgm_BISON{}", std::env::consts::DLL_SUFFIX);
    let library = library_directory.join(&library_name);
    assert!(library.is_file());
    assert!(!library_directory.join("parser_Pgm_BISON").exists());
    assert_eq!(
        fs::read_link(library_directory.join("parser_PGM")).unwrap(),
        Path::new(&library_name)
    );

    let consumer_source = root.join("consumer.c");
    let consumer = root.join("consumer");
    fs::write(
        &consumer_source,
        "#include <stdio.h>\nchar *parse_Pgm(char *, char *);\nint main(int argc, char **argv) { printf(\"%s\\n\", parse_Pgm(argv[1], NULL)); }\n",
    )
    .unwrap();
    let compiled = Command::new("cc")
        .arg(&consumer_source)
        .arg(format!("-L{}", library_directory.display()))
        .arg("-lparser_Pgm_BISON")
        .args(["-o"])
        .arg(&consumer)
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );

    let input = root.join("input.pgm");
    fs::write(&input, "ABC\n").unwrap();
    let library_path_variable = if cfg!(target_os = "macos") {
        "DYLD_LIBRARY_PATH"
    } else {
        "LD_LIBRARY_PATH"
    };
    let from_library = Command::new(&consumer)
        .arg(&input)
        .env(library_path_variable, &library_directory)
        .output()
        .unwrap();
    assert!(
        from_library.status.success(),
        "{}",
        String::from_utf8_lossy(&from_library.stderr)
    );
    let from_executable = Command::new(executable_directory.join("parser_PGM"))
        .arg(&input)
        .output()
        .unwrap();
    assert!(from_executable.status.success());
    assert_eq!(from_library.stdout, from_executable.stdout);

    let rejected = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "BISON",
            "--output-directory",
            root.join("rejected").to_str().unwrap(),
            "--bison-parser-library",
        ])
        .output()
        .unwrap();
    assert!(!rejected.status.success());
    assert!(
        String::from_utf8_lossy(&rejected.stderr).contains(
            "--bison-parser-library requires --gen-bison-parser or --gen-glr-bison-parser"
        )
    );

    fs::remove_dir_all(root).unwrap();
}

#[cfg(unix)]
#[test]
fn kast_gen_parser_writes_a_standalone_lr_parser() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN-SYNTAX
  syntax Int [hook(INT.Int)]
  syntax Int ::= r"[0-9]+" [token]
  syntax Pgm ::= Int
endmodule

module MAIN
  imports MAIN-SYNTAX
  configuration <k> $PGM:Pgm </k>
endmodule
"#,
    )
    .unwrap();
    let parser = root.join("standalone-parser");
    let generated = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kast",
            definition.to_str().unwrap(),
            "--module",
            "MAIN-SYNTAX",
            "--sort",
            "Pgm",
            "--gen-parser",
        ])
        .arg(&parser)
        .output()
        .unwrap();
    assert!(
        generated.status.success(),
        "{}",
        String::from_utf8_lossy(&generated.stderr)
    );
    let input = root.join("input.pgm");
    fs::write(&input, "1\n").unwrap();
    let parsed = Command::new(&parser).arg(&input).output().unwrap();
    assert!(
        parsed.status.success(),
        "{}",
        String::from_utf8_lossy(&parsed.stderr)
    );
    assert_eq!(
        String::from_utf8(parsed.stdout).unwrap(),
        "inj{SortInt{}, SortPgm{}}(\\dv{SortInt{}}(\"1\"))\n"
    );
    let kompiled = root.join("main-kompiled");
    let compiled = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--syntax-module",
            "MAIN-SYNTAX",
            "--output-directory",
            kompiled.to_str().unwrap(),
            "--gen-bison-parser",
        ])
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let compiled_parse = Command::new(kompiled.join("parser_PGM"))
        .arg(&input)
        .output()
        .unwrap();
    let standalone_parse = Command::new(&parser).arg(&input).output().unwrap();
    assert_eq!(standalone_parse.stdout, compiled_parse.stdout);

    for invalid in [
        vec!["--gen-parser", "out", "--expression", "1"],
        vec!["--gen-parser", "--gen-glr-parser", "out"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kast",
                definition.to_str().unwrap(),
                "--module",
                "MAIN-SYNTAX",
                "--sort",
                "Pgm",
            ])
            .args(invalid)
            .output()
            .unwrap();
        assert!(!output.status.success());
    }

    fs::remove_dir_all(root).unwrap();
}

/// The differential of the two parsers krust builds for one grammar: the generated Flex/Bison
/// parser (`kast --gen-parser` for `syntax_module` and start sort `Pgm`) and the in-process parser
/// (`krun --depth 0` of the definition compiled with `main_module` and `syntax_module`, whose `<k>`
/// cell holds the parsed program). Both are builds of one function from program text to a term,
/// so on every program they must agree: both accept it and give it the same term once injections
/// are removed (an injection places a term at a sort, it is not part of what was written), or
/// both reject it, the in-process parser with a parse error. Each program must also be accepted
/// exactly when it is marked accepted, and what the generated parser prints is KORE, whose
/// string literals are printable ASCII.
#[cfg(unix)]
fn assert_parsers_give_each_program_one_term(
    definition_source: &str,
    main_module: &str,
    syntax_module: &str,
    programs: &[(String, bool)],
) {
    let (root, parser) = generate_parser(definition_source, syntax_module, &[]);
    let definition = root.join("definition.k");
    let kompiled = root.join("kompiled");
    let compiled = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kcompile", definition.to_str().unwrap()])
        .args([
            "--main-module",
            main_module,
            "--syntax-module",
            syntax_module,
        ])
        .arg("--output-directory")
        .arg(&kompiled)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let mut failures = Vec::new();
    for (index, (program, accepted)) in programs.iter().enumerate() {
        let shown = if program.chars().count() > 64 {
            let prefix = program.chars().take(32).collect::<String>();
            format!("{prefix:?}... ({} bytes)", program.len())
        } else {
            format!("{program:?}")
        };
        let input = root.join(format!("program-{index}.pgm"));
        fs::write(&input, program).unwrap();

        let generated = Command::new(&parser)
            .arg(&input)
            .stdin(Stdio::null())
            .output()
            .unwrap();
        let generated = if generated.status.success() {
            if let Some(byte) = generated
                .stdout
                .iter()
                .find(|byte| !(byte.is_ascii_graphic() || b" \n".contains(byte)))
            {
                failures.push(format!(
                    "{shown}: the generated parser printed byte {byte:#04x}, outside KORE's printable ASCII"
                ));
            }
            match parse_pattern(&String::from_utf8_lossy(&generated.stdout)) {
                Ok(pattern) => Ok(program_term(&pattern)),
                Err(error) => {
                    failures.push(format!(
                        "{shown}: the generated parser printed no KORE pattern: {error}"
                    ));
                    continue;
                }
            }
        } else {
            Err(String::from_utf8_lossy(&generated.stderr).into_owned())
        };

        let in_process = Command::new(env!("CARGO_BIN_EXE_krust"))
            .arg("krun")
            .arg("--definition")
            .arg(&kompiled)
            .args(["--sort", "Pgm", "--depth", "0", "--output", "kore"])
            .arg(&input)
            .stdin(Stdio::null())
            .output()
            .unwrap();
        let in_process = if in_process.status.success() {
            let configuration =
                parse_pattern(&String::from_utf8_lossy(&in_process.stdout)).unwrap();
            Ok(program_term(
                k_cell_program(&configuration).expect("a <k> cell"),
            ))
        } else {
            let stderr = String::from_utf8_lossy(&in_process.stderr).into_owned();
            if !stderr.contains("could not parse program") {
                failures.push(format!(
                    "{shown}: the in-process run failed other than by rejecting the program: {stderr}"
                ));
                continue;
            }
            Err(stderr)
        };

        let decision = |result: &Result<String, String>| match result {
            Ok(term) => format!("accepted as {term}"),
            Err(error) => format!("rejected: {}", error.trim_end()),
        };
        if generated.as_ref().ok() != in_process.as_ref().ok() {
            failures.push(format!(
                "{shown}:\n  generated  {}\n  in-process {}",
                decision(&generated),
                decision(&in_process),
            ));
        } else if generated.is_ok() != *accepted {
            failures.push(format!(
                "{shown}: expected {}, both {}",
                if *accepted { "accepted" } else { "rejected" },
                decision(&generated),
            ));
        }
    }
    fs::remove_dir_all(root).unwrap();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[cfg(unix)]
fn owned_programs(programs: &[(&str, bool)]) -> Vec<(String, bool)> {
    programs
        .iter()
        .map(|(program, accepted)| ((*program).to_owned(), *accepted))
        .collect()
}

#[cfg(unix)]
#[test]
fn kast_gen_parser_scanner_gives_regex_line_anchors_the_in_process_meaning() {
    assert_parsers_give_each_program_one_term(
        line_anchors::DEFINITION,
        "ANCHOR",
        "ANCHOR-SYNTAX",
        &owned_programs(&line_anchors::PROGRAMS),
    );
}

/// Flex's own `$` is trailing context, which Flex counts in its longest-match comparison; the
/// exported scanner must compare token lengths, as the in-process scanner does.
#[cfg(unix)]
#[test]
fn kast_gen_parser_scanner_compares_anchored_candidates_by_token_length() {
    assert_parsers_give_each_program_one_term(
        line_anchors::TIE_DEFINITION,
        "TIE",
        "TIE-SYNTAX",
        &owned_programs(&line_anchors::TIE_PROGRAMS),
    );
}

/// A token is a sequence of characters, and a generated scanner reads the UTF-8 bytes of its
/// input: a negated class and `.` must each match one whole character there, as they do in the
/// in-process scanner, so a character of several bytes is one token, and `{2}` counts characters.
/// Layout comments, whose classes are negated too, may hold any character.
#[cfg(unix)]
#[test]
fn kast_gen_parser_scanner_matches_classes_and_dot_against_whole_characters() {
    let definition = r#"
module CHARS-SYNTAX
  syntax Other ::= r"~[^a-z\\n\\ ]" [token]
  syntax Any ::= r"@.@" [token]
  syntax Pair ::= r"\\|[^|]{2}\\|" [token]
  syntax Pgm ::= "n" Other "z" | "d" Any | "p" Pair
endmodule

module CHARS
  imports CHARS-SYNTAX
  configuration <k> $PGM:Pgm </k>
endmodule
"#;
    let programs = [
        ("n ~% z", true),
        ("n ~\u{e9} z", true),
        ("n ~\u{2028} z", true),
        ("n ~\u{1F642} z", true),
        ("n ~\u{e9}\u{e9} z", false),
        ("d @\u{e9}@", true),
        ("d @\u{10FFFF}@", true),
        ("d @\n@", false),
        ("d @\u{e9}a@", false),
        ("p |\u{e9}a|", true),
        ("p |\u{e9}\u{fc}|", true),
        ("p |\u{1F642}\u{1F642}|", true),
        ("p |\u{e9}|", false),
        ("p |\u{1F642}|", false),
        ("p |a\u{e9}\u{fc}|", false),
        ("n ~\u{e9} /* \u{1F642} \u{2028} */ z // \u{fc}", true),
    ];
    assert_parsers_give_each_program_one_term(
        definition,
        "CHARS",
        "CHARS-SYNTAX",
        &owned_programs(&programs),
    );
}

/// A class range denotes the characters from its start to its end, whatever their encoded length:
/// both parsers accept exactly those characters, and a range across the surrogate gap holds the
/// characters on either side of it and nothing else; a range in a negated class removes its
/// characters from the class.
#[cfg(unix)]
#[test]
fn kast_gen_parser_scanner_matches_a_class_range_of_non_ascii_characters() {
    let definition = "
module RANGES-SYNTAX
  syntax Accented ::= r\"~[\u{E0}-\u{FF}]+\" [token]
  syntax Gap ::= r\"@[\u{D7FF}-\u{E000}]\" [token]
  syntax Outside ::= r\"%[^a-z\u{80}-\u{10FFFF}]\" [token]
  syntax Pgm ::= \"a\" Accented | \"g\" Gap | \"o\" Outside
endmodule

module RANGES
  imports RANGES-SYNTAX
  configuration <k> $PGM:Pgm </k>
endmodule
";
    let programs = [
        ("a ~\u{E0}\u{E9}\u{FF}", true),
        ("a ~\u{E9}", true),
        ("a ~\u{DF}", false),
        ("a ~\u{100}", false),
        ("a ~\u{E9}a", false),
        ("g @\u{D7FF}", true),
        ("g @\u{E000}", true),
        ("g @\u{D7FE}", false),
        ("g @\u{E001}", false),
        ("o %A", true),
        ("o %%", true),
        ("o %a", false),
        ("o %\u{80}", false),
        ("o %\u{E9}", false),
        ("o %\u{10FFFF}", false),
    ];
    assert_parsers_give_each_program_one_term(
        definition,
        "RANGES",
        "RANGES-SYNTAX",
        &owned_programs(&programs),
    );
}

/// A K class is a set of characters with no set operations, so a class that holds `&` or `~`
/// twice, or a range and its endpoint beside it, holds each of those characters, in the generated
/// scanner as in the in-process one.
#[cfg(unix)]
#[test]
fn kast_gen_parser_scanner_reads_a_repeated_class_character_as_that_character() {
    let definition = r#"
module REPEATED-SYNTAX
  syntax Doubled ::= r"q[&&~~]+q" [token]
  syntax Ranged ::= r"r[%-&&]+r" [token]
  syntax Pgm ::= "d" Doubled | "g" Ranged
endmodule

module REPEATED
  imports REPEATED-SYNTAX
  configuration <k> $PGM:Pgm </k>
endmodule
"#;
    let programs = [
        ("d q&q", true),
        ("d q~q", true),
        ("d q&~&~q", true),
        ("d qaq", false),
        ("d q%q", false),
        ("g r%r", true),
        ("g r&%&r", true),
        ("g r$r", false),
        ("g r'r", false),
    ];
    assert_parsers_give_each_program_one_term(
        definition,
        "REPEATED",
        "REPEATED-SYNTAX",
        &owned_programs(&programs),
    );
}

/// U+0000 is a character like any other: a token whose text holds it is that whole text, in
/// every kind of literal and in a token subsort's phrase, and its literal holds the character.
/// A generated scanner keeps such a text whole whether it reads its input in chunks or, for an
/// anchored rule, all at once.
#[cfg(unix)]
#[test]
fn kast_gen_parser_reads_a_token_holding_u0000_as_the_in_process_parser_does() {
    for anchored in [false, true] {
        let mark = if anchored {
            "  syntax Mark ::= r\"^%[^ \\\\n]+\" [token]\n  syntax Pgm ::= \"k\" Mark\n"
        } else {
            ""
        };
        let definition = format!(
            r#"
module NUL-SYNTAX
  syntax String [hook(STRING.String)]
  syntax String ::= r"[\\\"](([^\\\"\\\\])|([\\\\][^\\n]))*[\\\"]" [token]
  syntax Bytes [hook(BYTES.Bytes)]
  syntax Bytes ::= r"b[\\\"](([^\\\"\\\\])|([\\\\][^\\n]))*[\\\"]" [token]
  syntax Name ::= r"~[^ \\n]+" [token]
  syntax MyName ::= Name [token]
  syntax Pgm ::= "s" String | "y" Bytes | "n" Name | "m" MyName
{mark}endmodule

module NUL
  imports NUL-SYNTAX
  configuration <k> $PGM:Pgm </k>
endmodule
"#
        );
        let mut programs = vec![
            ("s \"a\0b\"", true),
            ("s \"\0\"", true),
            ("y b\"a\0b\"", true),
            ("n ~a\0b", true),
            ("n ~\0", true),
            ("m ~a\0b", true),
            ("n ~a\0 b", false),
        ];
        if anchored {
            programs.push(("k\n%a\0b", true));
        }
        assert_parsers_give_each_program_one_term(
            &definition,
            "NUL",
            "NUL-SYNTAX",
            &owned_programs(&programs),
        );
    }
}

/// A `[token]` production of several items denotes one token whose text is the whole phrase it
/// spans, from its first token to its last with the layout between them, not the text of its
/// first item.
#[cfg(unix)]
#[test]
fn kast_gen_parser_reads_a_token_production_of_several_items_as_its_whole_phrase() {
    let definition = r#"
module PHRASE-SYNTAX
  syntax Name ::= r"[a-z]+" [token]
  syntax Paren ::= "(" Name ")" [token]
  syntax Dotted ::= Name "." Name [token]
  syntax Pgm ::= "p" Paren | "d" Dotted
endmodule

module PHRASE
  imports PHRASE-SYNTAX
  configuration <k> $PGM:Pgm </k>
endmodule
"#;
    let programs = [
        ("p ( ab )", true),
        ("p (ab)", true),
        ("p (\n ab  )", true),
        ("d ab . cd", true),
        ("d ab.cd", true),
        ("p ( ab", false),
    ];
    assert_parsers_give_each_program_one_term(
        definition,
        "PHRASE",
        "PHRASE-SYNTAX",
        &owned_programs(&programs),
    );
}

/// An anchored token that ends where a scanner reading its input in 8 KiB chunks would end a
/// chunk must still see the newline after it.
#[cfg(unix)]
#[test]
fn kast_gen_parser_scanner_sees_the_newline_after_an_anchored_token_across_a_read_boundary() {
    let programs = line_anchors::programs_with_a_token_at_a_buffer_boundary()
        .into_iter()
        .map(|program| (program, true))
        .collect::<Vec<_>>();
    assert_parsers_give_each_program_one_term(
        line_anchors::DEFINITION,
        "ANCHOR",
        "ANCHOR-SYNTAX",
        &programs,
    );
}

/// Class test for the two-parser ticket, line ends: `^` holds where a line starts and `$` where
/// one ends, and a location says where lines start (column 1 of the next line follows every line
/// end it counts). So both scanners must accept a `^b` token, and an `a$` token, at every line
/// end the location code counts, not only after `\n`.
#[cfg(unix)]
#[test]
fn regex_line_anchors_hold_at_every_line_end_a_location_counts() {
    const LINE_ENDS: [&str; 8] = [
        "\n", "\r", "\r\n", "\u{b}", "\u{c}", "\u{85}", "\u{2028}", "\u{2029}",
    ];
    // The layout holds every line end, so a scanner rejects a program only for its anchors.
    let definition = "module LINE-END-SYNTAX\n  syntax #Layout ::= r\"[\\\\ \\\\n\\\\r\\\\t\u{b}\u{c}\u{85}\u{2028}\u{2029}]\" [token]\n  syntax Bar ::= r\"^b\" [token]\n  syntax Foo ::= r\"a$\" [token]\n  syntax Pgm ::= Bar Bar | Foo Bar\nendmodule\n";
    let programs = LINE_ENDS
        .iter()
        .flat_map(|line_end| {
            [
                (format!("b{line_end}b"), true),
                (format!("a{line_end}b"), true),
            ]
        })
        .collect::<Vec<_>>();
    assert_parsers_give_each_program_one_term(
        definition,
        "LINE-END-SYNTAX",
        "LINE-END-SYNTAX",
        &programs,
    );
}

/// The default layout's line comment ends at a line end, and a line end is any line terminator a
/// location counts: after each of them both scanners read the next token, which a comment that
/// ran to the next `\n` would swallow. Every line end is also whitespace, so it separates two
/// tokens. Without a line end, the comment runs to the end of the text.
#[cfg(unix)]
#[test]
fn the_default_line_comment_ends_at_every_line_end_a_location_counts() {
    const LINE_ENDS: [&str; 8] = [
        "\n", "\r", "\r\n", "\u{b}", "\u{c}", "\u{85}", "\u{2028}", "\u{2029}",
    ];
    let definition = "module COMMENT-SYNTAX\n  syntax Pgm ::= \"a\" \"b\"\nendmodule\n";
    let mut programs = LINE_ENDS
        .iter()
        .flat_map(|line_end| {
            [
                (format!("a // c\u{2027}é{line_end}b"), true),
                (format!("a{line_end}b"), true),
            ]
        })
        .collect::<Vec<_>>();
    programs.push(("a // c\u{2027}é b".to_owned(), false));
    assert_parsers_give_each_program_one_term(
        definition,
        "COMMENT-SYNTAX",
        "COMMENT-SYNTAX",
        &programs,
    );
}

/// A `$`-anchored candidate the generated scanner rejects, here one whose text spans a newline,
/// must not move the line or column of the tokens scanned after it: the locations are those of
/// the same definition without the anchored lexeme.
#[cfg(unix)]
#[test]
fn kast_gen_parser_locations_ignore_rejected_anchored_candidates() {
    let parse = |anchored: bool| {
        let (root, definition) = fixture();
        let foo = if anchored {
            "syntax Foo ::= r\"a(\\\\n[a-z])*$\" [token]\n  syntax Pgm ::= Foo \"!\"\n"
        } else {
            ""
        };
        fs::write(
            &definition,
            format!(
                r#"
module LOC-SYNTAX
  syntax Bar [locations]
  syntax Bar ::= r"[a-z]+" [token]
  syntax Pgm ::= Bar Bar Bar
  {foo}
endmodule
"#
            ),
        )
        .unwrap();
        let parser = root.join("locations-parser");
        let generated = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kast",
                definition.to_str().unwrap(),
                "--module",
                "LOC-SYNTAX",
                "--sort",
                "Pgm",
                "--gen-parser",
            ])
            .arg(&parser)
            .output()
            .unwrap();
        assert!(
            generated.status.success(),
            "{}",
            String::from_utf8_lossy(&generated.stderr)
        );
        // At `a`, `Foo`'s body matches `a\nb`, which a space follows, then `a`, which a newline
        // follows; the second ties with `Bar` and loses on the lexeme order.
        let input = root.join("input.pgm");
        fs::write(&input, "a\nb c").unwrap();
        let parsed = Command::new(&parser).arg(&input).output().unwrap();
        assert!(
            parsed.status.success(),
            "{}",
            String::from_utf8_lossy(&parsed.stderr)
        );
        let output = String::from_utf8(parsed.stdout)
            .unwrap()
            .replace(input.to_str().unwrap(), "input.pgm");
        fs::remove_dir_all(root).unwrap();
        output
    };

    let plain = parse(false);
    assert!(plain.contains("\\dv{SortInt{}}(\"2\")"), "{plain}");
    assert_eq!(parse(true), plain);
}

/// Two regex lexemes of equal precedence that match equal-length text are tried in the order of
/// their canonical forms by both scanners, and regexes with the same canonical form are one
/// lexeme in both: `(a)` (canonical `a`) and `[a-z]` tie on `a`, and `[a-z]` comes first
/// although `(a)` comes first by source text; `(1)` and `1` are one lexeme, so both of its
/// productions are reachable.
#[cfg(unix)]
#[test]
fn kast_gen_parser_scanner_orders_and_identifies_regex_lexemes_by_canonical_form() {
    let definition = r##"
module ORDER-SYNTAX
  syntax A ::= r"(a)" [token]
  syntax B ::= r"[a-z]" [token]
  syntax X ::= r"(1)" [token]
  syntax Y ::= r"1" [token]
  syntax Pgm ::= A "!" | B "?" | X "#" | Y "%"
endmodule
"##;
    let programs = [("a?", true), ("a!", false), ("1#", true), ("1%", true)];
    assert_parsers_give_each_program_one_term(
        definition,
        "ORDER-SYNTAX",
        "ORDER-SYNTAX",
        &owned_programs(&programs),
    );
}

/// A scanner with a `$`-anchored rule uses Flex's `REJECT`; it must still accept a program
/// whose scan for one match runs far ahead of the token that wins (here an unclosed `<`
/// candidate over 20000 spaces before the literal `<` wins), and a single token longer than
/// Flex's default 16 KiB input buffer.
#[cfg(unix)]
#[test]
fn kast_gen_parser_anchored_scanner_accepts_long_lookahead_and_long_tokens() {
    let definition = r#"
module LOOKAHEAD-SYNTAX
  syntax Q ::= r"<[a-z ]*>" [token]
  syntax Foo ::= r"a$" [token]
  syntax Pgm ::= "<" "z" | Q | Foo
endmodule
"#;
    let programs = [
        (format!("<{}z", " ".repeat(20_000)), true),
        (format!("<{}>", "a".repeat(20_000)), true),
        (format!("<{}", "a".repeat(20_000)), false),
        ("a\n".to_owned(), true),
        ("a".to_owned(), false),
    ];
    assert_parsers_give_each_program_one_term(
        definition,
        "LOOKAHEAD-SYNTAX",
        "LOOKAHEAD-SYNTAX",
        &programs,
    );
}

/// Write `definition_source` and generate its Flex/Bison parser for `module` and start sort `Pgm`
/// (`kast --gen-parser`) with `environment` added to `kast`'s, which reaches the C compiler it
/// runs; returns the fixture root and the parser.
#[cfg(unix)]
fn generate_parser(
    definition_source: &str,
    module: &str,
    environment: &[(&str, &std::ffi::OsStr)],
) -> (PathBuf, PathBuf) {
    let (root, definition) = fixture();
    fs::write(&definition, definition_source).unwrap();
    let parser = root.join("generated-parser");
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command
        .args([
            "kast",
            definition.to_str().unwrap(),
            "--module",
            module,
            "--sort",
            "Pgm",
            "--gen-parser",
        ])
        .arg(&parser)
        .envs(environment.iter().copied());
    let generated = command.output().unwrap();
    assert!(
        generated.status.success(),
        "{}",
        String::from_utf8_lossy(&generated.stderr)
    );
    (root, parser)
}

/// A literal token production's `prec` orders it against regex tokens in both scanners: with
/// `prec(-1)` the regex `[a-z]+` wins `ab`, and without `prec` the literal does.
#[cfg(unix)]
#[test]
fn kast_gen_parser_scanner_gives_a_literal_token_its_declared_precedence() {
    for (precedence, regex_wins) in [(", prec(-1)", true), ("", false)] {
        let definition = format!(
            r#"
module PREC-SYNTAX
  syntax Foo ::= "ab" [token{precedence}]
  syntax Bar ::= r"[a-z]+" [token]
  syntax Pgm ::= Foo "!" | Bar "?"
endmodule
"#
        );
        let programs = [("ab?", regex_wins), ("ab!", !regex_wins), ("abc?", true)];
        assert_parsers_give_each_program_one_term(
            &definition,
            "PREC-SYNTAX",
            "PREC-SYNTAX",
            &owned_programs(&programs),
        );
    }
}

/// Generated parsers locate tokens as the in-process parser does (`inner::location`): lines and
/// columns from 1 on every line, a column per Unicode scalar value, the end column after the last
/// character, and `\n`, `\r`, `\r\n`, vertical tab, U+0085 and U+2028 each ending one line, also
/// when two tokens split a `\r\n`.
#[cfg(unix)]
#[test]
fn kast_gen_parser_locations_number_lines_and_columns_as_the_in_process_parser() {
    let definition = r#"
module LOC-SYNTAX
  syntax Bar [locations]
  syntax Bar ::= r"[a-z]+" [token] | r"<[^>]*>" [token]
  syntax Pgm ::= Bar ";" Bar ";" Bar ";" Bar ";" Bar
endmodule
"#;
    let (root, parser) = generate_parser(definition, "LOC-SYNTAX", &[]);
    let input = root.join("input.pgm");
    fs::write(
        &input,
        "a;\r\n<\u{e9}>;\rbb;<x\ny\u{85}z\u{b}w>;<p\u{2028}q>",
    )
    .unwrap();
    let parsed = Command::new(&parser).arg(&input).output().unwrap();
    assert!(
        parsed.status.success(),
        "{}",
        String::from_utf8_lossy(&parsed.stderr)
    );
    let output = String::from_utf8(parsed.stdout).unwrap();
    let int = r#"\\dv\{SortInt\{\}\}\("([0-9]+)"\)"#;
    let locations = Regex::new(&format!(r"{int}, {int}, {int}, {int}\)"))
        .unwrap()
        .captures_iter(&output)
        .map(|captures| {
            (1..=4)
                .map(|group| captures[group].parse::<u32>().unwrap())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    assert_eq!(
        locations,
        [
            [1, 1, 1, 2],
            [2, 1, 2, 4],
            [3, 1, 3, 3],
            [3, 4, 6, 3],
            [6, 4, 7, 3],
        ],
        "{output}"
    );

    let error = root.join("error.pgm");
    fs::write(&error, "a;\n  b c").unwrap();
    let rejected = Command::new(&parser).arg(&error).output().unwrap();
    assert!(!rejected.status.success());
    assert!(
        String::from_utf8_lossy(&rejected.stderr).contains(":2:5:2:6:syntax error"),
        "{}",
        String::from_utf8_lossy(&rejected.stderr)
    );
    fs::remove_dir_all(root).unwrap();
}

/// A generated parser's scanner error for text no rule matches names the whole character in the
/// column it locates: the unmatched byte and the UTF-8 continuation bytes after it, byte for byte,
/// so U+0000 is a NUL byte and a multi-byte character all of its bytes; a lead byte that nothing
/// continues is that byte alone. This holds in the middle and at the end of the input, for a
/// character the scanner's input buffer splits (the scanner without anchors reads a file in chunks
/// of 8192 bytes, so a run of spaces around that length puts the lead byte at the end of a chunk),
/// and in the scanner that reads its whole input at once (with an anchored rule).
#[cfg(unix)]
#[test]
fn kast_gen_parser_scanner_errors_name_the_whole_unexpected_character() {
    let characters: [&[u8]; 5] = [
        b"\0",
        "\u{e9}".as_bytes(),
        "\u{20ac}".as_bytes(),
        "\u{1f600}".as_bytes(),
        b"\xc3",
    ];
    for anchored in [false, true] {
        let mark = if anchored {
            "  syntax Mark ::= r\"^%[a-z]+\" [token]\n  syntax Pgm ::= \"k\" Mark\n"
        } else {
            ""
        };
        let definition = format!(
            "module UNEXPECTED-SYNTAX\n  syntax Id ::= r\"[a-z]+\" [token]\n  syntax Pgm ::= Id \";\" Pgm | \".Pgm\"\n{mark}endmodule\n"
        );
        let (root, parser) = generate_parser(&definition, "UNEXPECTED-SYNTAX", &[]);
        let program = root.join("program.pgm");
        let mut cases = Vec::new();
        for character in characters {
            for rest in [&b";.Pgm"[..], b""] {
                cases.push(([b"ab;", character, rest].concat(), 4, character));
            }
            if character.len() > 1 {
                for spaces in 8180..8200 {
                    cases.push((
                        [&vec![b' '; spaces][..], character].concat(),
                        spaces + 1,
                        character,
                    ));
                }
            }
        }
        for (text, column, character) in cases {
            fs::write(&program, &text).unwrap();
            let rejected = Command::new(&parser).arg(&program).output().unwrap();
            let expected = [
                format!("1:{column}:1:{}:syntax error: unexpected ", column + 1).as_bytes(),
                character,
                b"\n",
            ]
            .concat();
            assert!(
                !rejected.status.success() && rejected.stderr == expected,
                "anchored {anchored}, {:?}: {:?}",
                String::from_utf8_lossy(&text[text.len().saturating_sub(12)..]),
                String::from_utf8_lossy(&rejected.stderr)
            );
        }
        fs::remove_dir_all(root).unwrap();
    }
}

/// In-process program parsing locates the terms of `[locations]` sorts as a generated parser
/// does: a term is wrapped in `#location` at its own sort and at the sort of its position when
/// either declares `[locations]` (`Val` inside `Exp`, through its injection, when both do), a
/// term from its first token to its last, without the layout after it even when its last part is
/// empty (`f(1, 2 )` locates `1, 2` and its empty end at the end of `2`), an empty list at the end
/// of the token before it (`f( )` locates it after `(`), a term whose first part is empty from its
/// first token, line and column as offset (`(  # v )` locates `# v` from `#`, not after `(`), and
/// the file name is the program path as given, `-` for standard input and `--expression`.
/// `krun --depth 0` and the generated parser give each program one term once the injection into
/// the start position is removed.
#[cfg(unix)]
#[test]
fn in_process_parsing_locates_located_sorts_as_the_generated_parser() {
    const DEFINITION: &str = r##"
module L-SYNTAX
  imports INT-SYNTAX
  syntax Exp [locations]
  syntax Val [locations]
  syntax Exps [locations]
  syntax Val ::= Int | "v" [symbol(v)]
  syntax Exp ::= Val | Exp "+" Exp [left, symbol(plus)] | "f" "(" Exps ")" [symbol(f)]
               | "(" Exp ")" [bracket] | Opt "#" Val [symbol(hash)]
  syntax Opt ::= "" [symbol(none)] | "o" [symbol(some)]
  syntax Exps ::= List{Exp, ","}
  syntax Pgm ::= Exp
endmodule
module L
  imports L-SYNTAX
  imports K-LOCATIONS
  configuration <k> $PGM:Pgm </k>
endmodule
"##;
    /// `pattern` without the injection at its root.
    fn uninjected(pattern: &Pattern) -> Pattern {
        match pattern {
            Pattern::Application { symbol, arguments } if symbol.name == "inj" => {
                let [argument] = arguments.as_slice() else {
                    panic!("an injection has one argument")
                };
                argument.clone()
            }
            pattern => pattern.clone(),
        }
    }
    let (root, parser) = generate_parser(DEFINITION, "L-SYNTAX", &[]);
    let definition = root.join("definition.k");
    let kompiled = root.join("kompiled");
    let compiled = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kcompile", definition.to_str().unwrap()])
        .args(["--main-module", "L", "--syntax-module", "L-SYNTAX"])
        .arg("--output-directory")
        .arg(&kompiled)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let generated = |input: &Path, file: Option<&str>| {
        let output = Command::new(&parser)
            .arg(input)
            .args(file)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        uninjected(&parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap())
    };
    let in_process = |arguments: &[&std::ffi::OsStr], stdin: Option<&str>| {
        let mut child = Command::new(env!("CARGO_BIN_EXE_krust"))
            .arg("krun")
            .arg("--definition")
            .arg(&kompiled)
            .args(["--sort", "Pgm", "--depth", "0", "--output", "kore"])
            .args(arguments)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child
            .stdin
            .take()
            .unwrap()
            .write_all(stdin.unwrap_or_default().as_bytes())
            .unwrap();
        let output = child.wait_with_output().unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let configuration = parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap();
        let Some([Pattern::Application { symbol, arguments }]) = k_cell(&configuration) else {
            panic!("no <k> cell in {configuration:?}")
        };
        assert_eq!(symbol.name, "kseq");
        uninjected(&arguments[0])
    };
    let programs = [
        "v + 1",
        "f(1, 2)",
        "f()",
        "1",
        "(1 +\r\nv)\r+ f(3)\n",
        "f(1, 2 )",
        "f( )",
        "f( 1 ,\n 2  \n )\n",
        "f(f( ), (v) ) + f(\n)",
        "(  # v )",
        "  # 1",
        "f(\n  # v ,o # 1, #\n2)",
    ];
    for (index, program) in programs.into_iter().enumerate() {
        let input = root.join(format!("program-{index}.pgm"));
        fs::write(&input, program).unwrap();
        assert_eq!(
            in_process(&[input.as_os_str()], None),
            generated(&input, None),
            "{program:?} read from {}",
            input.display()
        );
        let unnamed = generated(&input, Some("-"));
        assert_eq!(
            in_process(&[], Some(program)),
            unnamed,
            "{program:?} on stdin"
        );
        assert_eq!(
            in_process(&["-".as_ref()], Some(program)),
            unnamed,
            "{program:?} read from -"
        );
        assert_eq!(
            in_process(&["--expression".as_ref(), program.as_ref()], None),
            unnamed,
            "{program:?} given by --expression"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

/// The program grammar renders only its useful rules. Here `KItem ::= KConfigVar` is one that is
/// not: `KConfigVar` has no program syntax. Rendered, Bison dropped it as useless, and its IELR
/// pass then aborted on this grammar (`AnnotationList__compute_from_inadequacies`). Without it
/// the parser is generated and reads a `Toks` phrase, empty or not, as its text.
#[cfg(unix)]
#[test]
fn kast_gen_parser_builds_a_located_token_phrase_over_a_list_without_useless_rules() {
    const DEFINITION: &str = r#"
module L-SYNTAX
  imports INT-SYNTAX
  syntax Exp [locations]
  syntax Val [locations]
  syntax Exps [locations]
  syntax Toks [locations]
  syntax Val ::= Int | "v" [symbol(v)]
  syntax Exp ::= Val | Exp "+" Exp [left, symbol(plus)] | "f" "(" Exps ")" [symbol(f)]
               | "(" Exp ")" [bracket]
               | "g" "(" Toks ")" [symbol(g)]
  syntax Exps ::= List{Exp, ","}
  syntax Vals ::= List{Val, ","}
  syntax Toks ::= Vals [token]
  syntax Pgm ::= Exp
endmodule
"#;
    let (root, parser) = generate_parser(DEFINITION, "L-SYNTAX", &[]);
    let located = |term: &str, columns: (u32, u32)| {
        format!(
            "Lbl'Hash'location{{{sort}}}({term}, \\dv{{SortString{{}}}}(\"p\"), \\dv{{SortInt{{}}}}(\"1\"), \\dv{{SortInt{{}}}}(\"{}\"), \\dv{{SortInt{{}}}}(\"1\"), \\dv{{SortInt{{}}}}(\"{}\"))",
            columns.0,
            columns.1,
            sort = if term.starts_with("\\dv") {
                "SortToks{}"
            } else {
                "SortExp{}"
            },
        )
    };
    for (program, text) in [("g(v, 1)", "v, 1"), ("g()", "")] {
        let input = root.join("program.pgm");
        fs::write(&input, program).unwrap();
        let output = Command::new(&parser).arg(&input).arg("p").output().unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let end = u32::try_from(program.len()).unwrap();
        let phrase = located(&format!("\\dv{{SortToks{{}}}}(\"{text}\")"), (3, end));
        assert_eq!(
            String::from_utf8(output.stdout).unwrap().trim_end(),
            format!(
                "inj{{SortExp{{}}, SortPgm{{}}}}({})",
                located(&format!("Lblg{{}}({phrase})"), (1, end + 1))
            ),
            "{program:?}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

/// Class test for the two-parser ticket: the generated parser and the in-process parser are two
/// builds of one function from program text to a term, so each program must get the same term
/// from both, modulo injections, or be rejected by both, and what the generated parser prints is
/// KORE, whose string literals are printable ASCII. Programs: `[locations]` (both wrap, or
/// neither), a two-byte and a three-byte character matched by a negated class (a token is a
/// sequence of characters), a line separator between tokens (a line end, which the default
/// layout skips), a `String` token holding non-ASCII and a control character, and
/// operators whose nesting priority and associativity decide, among them a labelled production
/// with one nonterminal and no terminal (`wrap`), below which neither parser judges an edge.
#[cfg(unix)]
#[test]
fn generated_and_in_process_parsers_give_each_program_one_term() {
    const TOKENS: &str = r#"
module TOKENS-SYNTAX
  imports STRING-SYNTAX
  syntax Tok ::= r"[^a-z\\n\\ \"+]" [token]
  syntax Exp ::= Tok | String | Exp "+" Exp [left, symbol(plus)] | "x" [symbol(x)]
  syntax Pgm ::= Exp
endmodule
module TOKENS
  imports TOKENS-SYNTAX
  configuration <k> $PGM:Pgm </k>
endmodule
"#;
    const LOCATIONS: &str = r#"
module LOC-SYNTAX
  syntax Exp [locations]
  syntax Exp ::= Exp "+" Exp [left, symbol(plus)] | "x" [symbol(x)]
  syntax Pgm ::= Exp
endmodule
module LOC
  imports LOC-SYNTAX
  imports K-LOCATIONS
  configuration <k> $PGM:Pgm </k>
endmodule
"#;
    assert_parsers_give_each_program_one_term(
        TOKENS,
        "TOKENS",
        "TOKENS-SYNTAX",
        &owned_programs(&[
            ("x + x", true),
            ("\"a\" + x", true),
            ("x + \u{e9}", true),
            ("\u{2027}", true),
            ("x +\u{2028}x", true),
            ("\"\u{e9}\u{1}\"", true),
            ("x + a", false),
        ]),
    );
    assert_parsers_give_each_program_one_term(
        LOCATIONS,
        "LOC",
        "LOC-SYNTAX",
        &owned_programs(&[("x + x", true), ("x +\nx", true), ("x +", false)]),
    );
    const RELATIONS: &str = r#"
module REL-SYNTAX
  syntax Exp ::= "x" [symbol(x)]
               | "-" Exp [symbol(neg)]
               | Exp "*" Exp [left, symbol(mul)]
               | Exp "+" Exp [left, symbol(plus)]
  syntax Top ::= Exp [symbol(wrap)]
  syntax Pgm ::= Top
  syntax priority neg > mul > plus
  syntax priority wrap > plus
endmodule
module REL
  imports REL-SYNTAX
  configuration <k> $PGM:Pgm </k>
endmodule
"#;
    assert_parsers_give_each_program_one_term(
        RELATIONS,
        "REL",
        "REL-SYNTAX",
        &owned_programs(&[
            ("x + x * x", true),
            ("x * x + x", true),
            ("- x + x * x", true),
            ("x + x + x", true),
            ("x * - x * x", true),
            ("x", true),
            ("x + ", false),
        ]),
    );
}

/// A sort that declares `[locations]` asks that each term of it a program denotes be wrapped in
/// `#location`, the symbol `K-LOCATIONS` declares. Without that module in the main module's view
/// only `krun` needs the symbol, to build its configuration, and only for a program holding a
/// located term: `kcompile` warns at the declaration and compiles, with or without a generated
/// parser, which prints the located term; `kast` prints it too; `krun` runs a program with no
/// located term and refuses one with a located term at that term's place in the program. The
/// import anywhere in the main module's view, also through the syntax module, silences the
/// warning, and `krun` then reads the program into located terms.
#[cfg(unix)]
#[test]
fn a_located_sort_without_k_locations_warns_at_kcompile_and_krun_refuses_only_located_programs() {
    let source = |syntax_imports: &str, main_imports: &str| {
        format!(
            r#"
module LOC-SYNTAX
  imports INT-SYNTAX{syntax_imports}
  syntax Exp [locations]
  syntax Exp ::= Int | Exp "+" Exp [left, symbol(plus)]
  syntax Pgm ::= Exp | "skip" [symbol(skip)]
endmodule

module LOC
  imports LOC-SYNTAX{main_imports}
  configuration <k> $PGM:Pgm </k>
endmodule
"#
        )
    };
    let kcompile = |definition: &Path, output: &Path, extra: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_krust"))
            .arg("kcompile")
            .arg(definition)
            .args(["--main-module", "LOC", "--syntax-module", "LOC-SYNTAX"])
            .arg("--output-directory")
            .arg(output)
            .args(extra)
            .stdin(Stdio::null())
            .output()
            .unwrap()
    };
    let krun = |kompiled: &Path, program: &Path| {
        Command::new(env!("CARGO_BIN_EXE_krust"))
            .arg("krun")
            .arg("--definition")
            .arg(kompiled)
            .args(["--sort", "Pgm", "--depth", "0"])
            .arg(program)
            .stdin(Stdio::null())
            .output()
            .unwrap()
    };
    let warning = "definition.k:4:3: Warning[MissingLocationsImport]: Sort Exp ";

    let (root, definition) = fixture();
    fs::write(&definition, source("", "")).unwrap();
    let located = root.join("located.loc");
    fs::write(&located, "1 + 2").unwrap();
    let unlocated = root.join("unlocated.loc");
    fs::write(&unlocated, "skip").unwrap();
    for extra in [&[][..], &["--gen-bison-parser"][..]] {
        let kompiled = root.join(format!("kompiled{}", extra.len()));
        let output = kcompile(&definition, &kompiled, extra);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success()
                && stderr.contains(warning)
                && stderr.contains("Add `imports K-LOCATIONS` to LOC to run such programs."),
            "{extra:?}: not compiled with the warning at the declaration: {stderr}"
        );
        if !extra.is_empty() {
            let parsed = Command::new(kompiled.join("parser_PGM"))
                .arg(&located)
                .stdin(Stdio::null())
                .output()
                .unwrap();
            assert!(
                parsed.status.success()
                    && String::from_utf8_lossy(&parsed.stdout)
                        .contains("Lbl'Hash'location{SortExp{}}("),
                "{}",
                String::from_utf8_lossy(&parsed.stderr)
            );
        }
        let run = krun(&kompiled, &unlocated);
        assert!(
            run.status.success() && String::from_utf8_lossy(&run.stdout).contains("Lblskip{}()"),
            "{extra:?}: a program without a located term does not run: {}",
            String::from_utf8_lossy(&run.stderr)
        );
        let run = krun(&kompiled, &located);
        let stderr = String::from_utf8_lossy(&run.stderr);
        assert!(
            !run.status.success()
                && stderr.contains(&format!(
                    "{}:1:1-1:6: the value of `$PGM` holds a term of sort Exp, which declares 'locations'",
                    located.display()
                ))
                && stderr.contains("Add `imports K-LOCATIONS` to LOC to run it."),
            "{extra:?}: a located program is not refused at its located term: {stderr}"
        );
    }
    let parsed = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("kast")
        .arg(&definition)
        .args(["--module", "LOC", "--sort", "Pgm"])
        .args(["--expression", "1 + 2"])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        parsed.status.success()
            && String::from_utf8_lossy(&parsed.stdout).contains("#location{Exp}"),
        "{}",
        String::from_utf8_lossy(&parsed.stderr)
    );
    fs::remove_dir_all(root).unwrap();

    for (case, syntax_imports, main_imports) in [
        ("main", "", "\n  imports K-LOCATIONS"),
        ("syntax", "\n  imports K-LOCATIONS", ""),
    ] {
        let (root, definition) = fixture();
        fs::write(&definition, source(syntax_imports, main_imports)).unwrap();
        let kompiled = root.join("kompiled");
        let output = kcompile(&definition, &kompiled, &[]);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success() && !stderr.contains("MissingLocationsImport"),
            "{case}: {stderr}"
        );
        let program = root.join("program.loc");
        fs::write(&program, "1 + 2").unwrap();
        let run = krun(&kompiled, &program);
        let stdout = String::from_utf8_lossy(&run.stdout);
        assert!(
            run.status.success() && stdout.matches("Lbl'Hash'location{SortExp{}}(").count() == 3,
            "{case}: {stdout}{}",
            String::from_utf8_lossy(&run.stderr)
        );
        fs::remove_dir_all(root).unwrap();
    }
}

/// A `#LineMarker` production says which text is a marker but not what the marker sets for the
/// text after it, so krust gives it no meaning and refuses the definition at load, alike on every
/// parser route: in-process parsing, the generated parser of `kast --gen-parser`, and the parser
/// `kcompile --gen-bison-parser` builds. Each refusal is krust's own diagnostic, located at the
/// production, whether the production is in the parsed module or in a module it imports, and no
/// parser is written. Declaring the same text as `#Layout`, the suggested replacement, skips it
/// alike in both parsers.
#[cfg(unix)]
#[test]
fn a_line_marker_production_means_one_thing_to_both_parsers() {
    const MARKER: &str = r##"syntax #LineMarker ::= r"#line [0-9]+\\n" [token]"##;
    for (case, source, location) in [
        (
            "main",
            format!(
                "module LM-SYNTAX\n  {MARKER}\n  syntax Pgm ::= \"a\" [symbol(a)]\nendmodule\n"
            ),
            "definition.k:2:",
        ),
        (
            "imported",
            format!(
                "module LM\n  {MARKER}\nendmodule\n\nmodule LM-SYNTAX\n  imports LM\n  syntax Pgm ::= \"a\" [symbol(a)]\nendmodule\n"
            ),
            "definition.k:2:",
        ),
    ] {
        let (root, definition) = fixture();
        fs::write(&definition, &source).unwrap();
        let parser = root.join("line-marker-parser");
        let kompiled = root.join("lm-kompiled");
        let routes = [
            (
                "in-process",
                vec!["kast", "--expression", "a", "--sort", "Pgm"],
            ),
            (
                "kast --gen-parser",
                vec![
                    "kast",
                    "--sort",
                    "Pgm",
                    "--gen-parser",
                    parser.to_str().unwrap(),
                ],
            ),
            (
                "kcompile --gen-bison-parser",
                vec![
                    "kcompile",
                    "--main-module",
                    "LM-SYNTAX",
                    "--syntax-module",
                    "LM-SYNTAX",
                    "--output-directory",
                    kompiled.to_str().unwrap(),
                    "--gen-bison-parser",
                ],
            ),
        ];
        for (route, arguments) in routes {
            let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
            command.arg(arguments[0]).arg(&definition);
            if arguments[0] == "kast" {
                command.args(["--module", "LM-SYNTAX"]);
            }
            let output = command
                .args(&arguments[1..])
                .stdin(Stdio::null())
                .output()
                .unwrap();
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(!output.status.success(), "{case}, {route}: accepted");
            assert!(
                stderr.contains(location) && stderr.contains("Error[UnsupportedLineMarker]"),
                "{case}, {route}: not refused at the production: {stderr}"
            );
            assert!(
                !stderr.contains("undefined reference"),
                "{case}, {route}: refused by the linker: {stderr}"
            );
        }
        assert!(!parser.exists() && !kompiled.join("parser_PGM").exists());
        fs::remove_dir_all(root).unwrap();
    }

    let (root, definition) = fixture();
    fs::write(
        &definition,
        "module LM-SYNTAX\n  syntax #Layout ::= r\"(#line [0-9]+\\\\n|[ \\\\t\\\\n])+\"\n  syntax Pgm ::= \"a\" [symbol(a)]\nendmodule\n",
    )
    .unwrap();
    let parser = root.join("layout-parser");
    let generated = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("kast")
        .arg(&definition)
        .args(["--module", "LM-SYNTAX", "--sort", "Pgm", "--gen-parser"])
        .arg(&parser)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        generated.status.success(),
        "{}",
        String::from_utf8_lossy(&generated.stderr)
    );
    let input = root.join("marked.pgm");
    fs::write(&input, "#line 7\na").unwrap();
    let standalone = Command::new(&parser).arg(&input).output().unwrap();
    let in_process = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("kast")
        .arg(&definition)
        .args(["--module", "LM-SYNTAX", "--sort", "Pgm"])
        .arg(&input)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        standalone.status.success() && in_process.status.success(),
        "generated: {}\nin-process: {}",
        String::from_utf8_lossy(&standalone.stderr),
        String::from_utf8_lossy(&in_process.stderr)
    );
    assert_eq!(
        parse_pattern(String::from_utf8_lossy(&standalone.stdout).trim()).unwrap(),
        parse_pattern("Lbla{}()").unwrap()
    );
    assert_eq!(
        String::from_utf8_lossy(&in_process.stdout).trim(),
        "a(.KList)"
    );
    fs::remove_dir_all(root).unwrap();
}

/// The term a successful parser run printed, as the KORE of the program with every injection
/// removed (an injection places a term at a sort; it is not part of what was written), or why
/// there is none.
#[cfg(unix)]
fn program_term(pattern: &Pattern) -> String {
    match pattern {
        Pattern::Application { symbol, arguments } if symbol.name == "inj" => {
            program_term(&arguments[0])
        }
        Pattern::Application { symbol, arguments } => format!(
            "{}({})",
            symbol.name,
            arguments
                .iter()
                .map(program_term)
                .collect::<Vec<_>>()
                .join(",")
        ),
        other => other.to_string(),
    }
}

/// The program inside the `<k>` cell of an initial configuration: `kseq{}(T, dotk{}())`'s `T`.
#[cfg(unix)]
fn k_cell_program(pattern: &Pattern) -> Option<&Pattern> {
    let Pattern::Application { symbol, arguments } = pattern else {
        return None;
    };
    if symbol.name == "Lbl'-LT-'k'-GT-'" {
        let [Pattern::Application { symbol, arguments }] = arguments.as_slice() else {
            return None;
        };
        return (symbol.name == "kseq").then(|| &arguments[0]);
    }
    arguments.iter().find_map(k_cell_program)
}

/// A user list is read by the generated parser element after element (left recursion), while
/// its constructor takes an element and the list after it: each program must still get the
/// term the in-process parser gives it, for a `NeList` and a `List`, of `[locations]` sorts,
/// with layout between the elements, and for a list whose separator is empty; the lists that
/// are not programs must be rejected by both. No program has layout after an empty term (a
/// `nil`), which the two parsers locate apart (`docs/compatibility.md`, "In-process program
/// locations").
#[cfg(unix)]
#[test]
fn generated_and_in_process_parsers_give_each_list_one_term() {
    const LISTS: &str = r#"
module LISTS-SYNTAX
  syntax Tok ::= "x" [symbol(x)] | "y" [symbol(y)]
  syntax Toks [locations]
  syntax Opt [locations]
  syntax Toks ::= NeList{Tok, ","} [symbol(toks)]
  syntax Opt ::= List{Tok, ";"} [symbol(opt)]
  syntax Adj ::= NeList{Tok, ""} [symbol(adj)]
  syntax Pgm ::= "n" Toks [symbol(n)] | "m" Opt "." [symbol(m)] | "s" Adj "." [symbol(s)]
endmodule
module LISTS
  imports LISTS-SYNTAX
  imports K-LOCATIONS
  configuration <k> $PGM:Pgm </k>
endmodule
"#;
    let programs = [
        ("n x", true),
        ("n x, y, y", true),
        ("n x ,\n y", true),
        ("m.", true),
        ("m x.", true),
        ("m x; y ;x.", true),
        ("m x;\n y.", true),
        ("n", false),
        ("n x,", false),
        ("n x y", false),
        ("m x; .", false),
        ("m ; .", false),
        ("s x.", true),
        ("s x y\n x.", true),
        ("s .", false),
        ("s x, y .", false),
    ]
    .map(|(program, accepted)| (program.to_owned(), accepted));
    assert_parsers_give_each_program_one_term(LISTS, "LISTS", "LISTS-SYNTAX", &programs);
}

/// A generated parser reads a list in a bounded stack: reading the next element reduces the list
/// read so far, so a list far longer than `--bison-stack-max-depth` is read, by the LR and the
/// GLR parser, with the term the in-process parser gives it, while nesting as deep as the list
/// is long exceeds the bound. When the list is ambiguous, the GLR parser prints every reading
/// merged (`Lblamb`): for `n x, ..., x` each way to group the elements into consecutive pairs
/// trees, as list elements.
#[cfg(unix)]
#[test]
fn generated_parsers_read_long_lists_in_a_bounded_stack_and_every_reading_of_an_ambiguous_list() {
    const LISTS: &str = r#"
module LISTS-SYNTAX
  syntax Tok ::= "x" [symbol(x)] | "(" Tok ")" [bracket]
  syntax Toks ::= NeList{Tok, ","} [symbol(toks)]
  syntax Pgm ::= "n" Toks [symbol(n)]
endmodule
module LISTS
  imports LISTS-SYNTAX
  configuration <k> $PGM:Pgm </k>
endmodule
"#;
    const AMBIGUOUS: &str = r#"
module LISTS-SYNTAX
  syntax Tok ::= "x" [symbol(x)] | Tok "," Tok [symbol(pair)]
  syntax Toks ::= NeList{Tok, ","} [symbol(toks)]
  syntax Pgm ::= "n" Toks [symbol(n)]
endmodule
module LISTS
  imports LISTS-SYNTAX
  configuration <k> $PGM:Pgm </k>
endmodule
"#;
    /// The terms a printed term with merged readings stands for.
    fn readings(pattern: &Pattern) -> BTreeSet<String> {
        let Pattern::Application { symbol, arguments } = pattern else {
            return BTreeSet::from([pattern.to_string()]);
        };
        if symbol.name == "Lblamb" {
            return arguments.iter().flat_map(readings).collect();
        }
        arguments
            .iter()
            .fold(BTreeSet::from([Vec::new()]), |prefixes, argument| {
                let readings = readings(argument);
                prefixes
                    .iter()
                    .flat_map(|prefix| {
                        readings.iter().map(move |reading| {
                            let mut arguments: Vec<String> = prefix.clone();
                            arguments.push(reading.clone());
                            arguments
                        })
                    })
                    .collect()
            })
            .into_iter()
            .map(|arguments| format!("{}({})", symbol.name, arguments.join(",")))
            .collect()
    }
    /// Every pair tree over `count` consecutive `x`.
    fn pairs(count: usize, x: &str) -> Vec<String> {
        if count == 1 {
            return vec![x.to_owned()];
        }
        (1..count)
            .flat_map(|left| {
                let rights = pairs(count - left, x);
                pairs(left, x).into_iter().flat_map(move |l| {
                    rights
                        .clone()
                        .into_iter()
                        .map(move |r| format!("Lblpair({l},{r})"))
                })
            })
            .collect()
    }
    /// Every list of pair trees over `count` consecutive `x`, ending in `nil`.
    fn lists(count: usize, x: &str, nil: &str) -> Vec<String> {
        if count == 0 {
            return vec![nil.to_owned()];
        }
        (1..=count)
            .flat_map(|first| {
                let rests = lists(count - first, x, nil);
                pairs(first, x).into_iter().flat_map(move |element| {
                    rests
                        .clone()
                        .into_iter()
                        .map(move |rest| format!("Lbltoks({element},{rest})"))
                })
            })
            .collect()
    }
    let (root, definition) = fixture();
    let compile = |source: &str, name: &str, flags: &[&str]| {
        fs::write(&definition, source).unwrap();
        let kompiled = root.join(format!("{name}-kompiled"));
        let compiled = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["kcompile", definition.to_str().unwrap()])
            .args(["--main-module", "LISTS", "--syntax-module", "LISTS-SYNTAX"])
            .arg("--output-directory")
            .arg(&kompiled)
            .args(flags)
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert!(
            compiled.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&compiled.stderr)
        );
        kompiled
    };
    let input = root.join("program.pgm");
    let parse = |kompiled: &Path, program: &str| {
        fs::write(&input, program).unwrap();
        let parsed = Command::new(kompiled.join("parser_PGM"))
            .arg(&input)
            .stdin(Stdio::null())
            .output()
            .unwrap();
        parsed
            .status
            .success()
            .then(|| parse_pattern(&String::from_utf8_lossy(&parsed.stdout)).unwrap())
    };
    let in_process = |kompiled: &Path, program: &str| {
        fs::write(&input, program).unwrap();
        let run = Command::new(env!("CARGO_BIN_EXE_krust"))
            .arg("krun")
            .arg("--definition")
            .arg(kompiled)
            .args(["--sort", "Pgm", "--depth", "0", "--output", "kore"])
            .arg(&input)
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert!(
            run.status.success(),
            "{}",
            String::from_utf8_lossy(&run.stderr)
        );
        let configuration = parse_pattern(&String::from_utf8_lossy(&run.stdout)).unwrap();
        program_term(k_cell_program(&configuration).expect("a <k> cell"))
    };
    let long = format!("n {}x", "x, ".repeat(200));
    let deep = format!("n {}x{}", "(".repeat(200), ")".repeat(200));
    for mode in ["--gen-bison-parser", "--gen-glr-bison-parser"] {
        let bounded = compile(LISTS, "bounded", &[mode, "--bison-stack-max-depth", "64"]);
        let term = parse(&bounded, &long).map(|pattern| program_term(&pattern));
        assert_eq!(term, Some(in_process(&bounded, &long)), "{mode}: long list");
        assert_eq!(
            parse(&bounded, &deep),
            None,
            "{mode}: the stack bound holds"
        );
        let unbounded = compile(LISTS, "unbounded", &[mode]);
        assert!(parse(&unbounded, &deep).is_some(), "{mode}: deep nesting");
    }

    let glr = compile(AMBIGUOUS, "ambiguous", &["--gen-glr-bison-parser"]);
    let single = parse(&glr, "n x").expect("n x");
    let Pattern::Application { arguments, .. } = &single else {
        panic!("{single}")
    };
    let Pattern::Application { symbol, arguments } = &arguments[0] else {
        panic!("{single}")
    };
    assert_eq!(symbol.name, "Lbltoks", "{single}");
    let [x, nil] = [&arguments[0], &arguments[1]].map(|argument| {
        let reading = readings(argument);
        assert_eq!(reading.len(), 1, "{single}");
        reading.into_iter().next().unwrap()
    });
    for (count, expected) in [(1, 1), (2, 2), (3, 5), (4, 14)] {
        let program = format!("n {}", vec!["x"; count].join(", "));
        let printed = readings(&parse(&glr, &program).expect(&program));
        let all = lists(count, &x, &nil)
            .into_iter()
            .map(|list| format!("Lbln({list})"))
            .collect::<BTreeSet<_>>();
        assert_eq!(all.len(), expected, "{program:?}");
        assert_eq!(printed, all, "{program:?}");
    }
    fs::remove_dir_all(root).unwrap();
}

/// The arguments of the `<k>` cell of a configuration.
fn k_cell(pattern: &Pattern) -> Option<&[Pattern]> {
    let Pattern::Application { symbol, arguments } = pattern else {
        return None;
    };
    if symbol.name == "Lbl'-LT-'k'-GT-'" {
        return Some(arguments);
    }
    arguments.iter().find_map(k_cell)
}

/// A scanner with an anchored rule scans its whole input with a state buffer of its own
/// (`bison::scanner::SCAN_WHOLE_INPUT`); a buffer one state too small is written past its end,
/// which an uninstrumented parser survives. Its anchor checks read the bytes around a match
/// (`bison::scanner::LINE_ANCHORS`), up to three after it and before it. Built with
/// AddressSanitizer, the parser must run the empty input, short programs, long candidates and
/// anchors at both ends of the input, beside multi-byte and truncated line terminators, and
/// unexpected characters up to the end of the input, without a report. Without a C compiler that
/// can build and run an AddressSanitizer program the test checks nothing.
#[cfg(unix)]
#[test]
fn kast_gen_parser_anchored_scanner_stays_in_its_buffers_under_address_sanitizer() {
    use std::os::unix::fs::PermissionsExt;

    // Leaks are not checked: the parser frees no node before it exits.
    const ASAN_OPTIONS: &str = "detect_leaks=0:exitcode=86";
    let compiler = std::env::var_os("KRUST_CC").unwrap_or_else(|| "cc".into());
    let (probe_root, _) = fixture();
    let probe_source = probe_root.join("probe.c");
    let probe = probe_root.join("probe");
    fs::write(&probe_source, "int main(void) { return 0; }\n").unwrap();
    let supported = Command::new(&compiler)
        .arg("-fsanitize=address")
        .arg(&probe_source)
        .arg("-o")
        .arg(&probe)
        .output()
        .is_ok_and(|output| output.status.success())
        && Command::new(&probe)
            .env("ASAN_OPTIONS", ASAN_OPTIONS)
            .output()
            .is_ok_and(|output| output.status.success());
    if !supported {
        eprintln!("skipped: the C compiler cannot build and run an AddressSanitizer program");
        fs::remove_dir_all(probe_root).unwrap();
        return;
    }
    let wrapper = probe_root.join("asan-cc");
    fs::write(
        &wrapper,
        "#!/bin/sh\nexec \"$KRUST_ASAN_CC\" -fsanitize=address -fno-omit-frame-pointer \"$@\"\n",
    )
    .unwrap();
    fs::set_permissions(&wrapper, fs::Permissions::from_mode(0o755)).unwrap();

    let definition = r#"
module LOOKAHEAD-SYNTAX
  syntax Q ::= r"<[a-z ]*>" [token]
  syntax Foo ::= r"a$" [token]
  syntax Bar ::= r"^b" [token]
  syntax Pgm ::= "<" "z" | Q | Foo | Bar
endmodule
"#;
    let (root, parser) = generate_parser(
        definition,
        "LOOKAHEAD-SYNTAX",
        &[
            ("KRUST_CC", wrapper.as_os_str()),
            ("KRUST_ASAN_CC", compiler.as_os_str()),
        ],
    );
    let programs = [
        (Vec::new(), false),
        (b"a\n".to_vec(), true),
        (b"a".to_vec(), false),
        (format!("<{}z", " ".repeat(20_000)).into_bytes(), true),
        (format!("<{}", "a".repeat(20_000)).into_bytes(), false),
        (b"a\r".to_vec(), true),
        (b"b".to_vec(), true),
        (b"\rb".to_vec(), true),
        // A line separator is a line end the default layout skips.
        ("\u{2028}b".as_bytes().to_vec(), true),
        ("a\u{2028}".as_bytes().to_vec(), true),
        (b"a\xE2\x80".to_vec(), false),
        (b"\xE2\x80b".to_vec(), false),
        // An unexpected character is written with the continuation bytes after it
        // (`bison::scanner::UNEXPECTED`), which may run to the end of the input.
        ("b\u{1f600}".as_bytes().to_vec(), false),
        ("\u{e9}\u{e9}".as_bytes().to_vec(), false),
        (b"\xC3".to_vec(), false),
    ];
    for (index, (program, accepted)) in programs.iter().enumerate() {
        let input = root.join(format!("program-{index}.pgm"));
        fs::write(&input, program).unwrap();
        let parsed = Command::new(&parser)
            .arg(&input)
            .env("ASAN_OPTIONS", ASAN_OPTIONS)
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&parsed.stderr);
        assert!(
            parsed.status.code() != Some(86) && !stderr.contains("AddressSanitizer"),
            "program {index}: {stderr}"
        );
        assert_eq!(
            parsed.status.success(),
            *accepted,
            "program {index}: {stderr}"
        );
    }
    fs::remove_dir_all(probe_root).unwrap();
    fs::remove_dir_all(root).unwrap();
}

#[cfg(unix)]
#[test]
fn kast_gen_parser_keeps_byte_string_tokens() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r##"
module TOKENS
  syntax Bytes [hook(BYTES.Bytes)]
  syntax Bytes ::= r"b[\\\"](([ !#-\\[\\]-~])|([\\\\][tnfr\"\\\\])|([\\\\][x][0-9a-fA-F]{2}))*[\\\"]" [token]
  syntax String [hook(STRING.String)]
  syntax String ::= r"[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2}))*[\\\"]" [token]
  syntax Pgm ::= Bytes | String
endmodule
"##,
    )
    .unwrap();
    let parser = root.join("tokens-parser");
    let generated = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kast",
            definition.to_str().unwrap(),
            "--module",
            "TOKENS",
            "--sort",
            "Pgm",
            "--gen-parser",
        ])
        .arg(&parser)
        .output()
        .unwrap();
    assert!(
        generated.status.success(),
        "{}",
        String::from_utf8_lossy(&generated.stderr)
    );
    for (name, source, expected) in [
        (
            "bytes.pgm",
            "b\"\\x00\\x0f\"\n",
            "inj{SortBytes{}, SortPgm{}}(\\dv{SortBytes{}}(\"\\x00\\x0f\"))\n",
        ),
        (
            "string.pgm",
            "\"text\"\n",
            "inj{SortString{}, SortPgm{}}(\\dv{SortString{}}(\"text\"))\n",
        ),
    ] {
        let input = root.join(name);
        fs::write(&input, source).unwrap();
        let parsed = Command::new(&parser).arg(&input).output().unwrap();
        assert!(
            parsed.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&parsed.stderr)
        );
        assert_eq!(
            String::from_utf8(parsed.stdout).unwrap(),
            expected,
            "{name}"
        );
    }

    fs::remove_dir_all(root).unwrap();
}

/// A generated parser writes each token as the KORE literal of the code points the in-process
/// frontend reads from it: a `String` token's characters after its K escapes, a `Bytes` token's
/// bytes as the code points of their values, any other token's characters; so the term it prints
/// is the in-process conversion of the token, and its text is KORE's printable ASCII. A token
/// text that is no literal of its hook is a located syntax error, as it is no term in-process.
#[cfg(unix)]
#[test]
fn kast_gen_parser_writes_each_token_as_the_kore_literal_of_its_code_points() {
    let source = r##"
module LITERALS
  syntax String [hook(STRING.String)]
  syntax String ::= r"[\\\"](([^\\\"\\\\])|([\\\\][^\\n]))*[\\\"]" [token]
  syntax Bytes [hook(BYTES.Bytes)]
  syntax Bytes ::= r"b[\\\"](([^\\\"\\\\])|([\\\\][^\\n]))*[\\\"]" [token]
  syntax Name ::= r"~[^ \\n]+" [token]
  syntax Pgm ::= String | Bytes | Name
endmodule
"##;
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();
    let parser = root.join("literals-parser");
    let generated = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kast", definition.to_str().unwrap()])
        .args(["--module", "LITERALS", "--sort", "Pgm", "--gen-parser"])
        .arg(&parser)
        .output()
        .unwrap();
    assert!(
        generated.status.success(),
        "{}",
        String::from_utf8_lossy(&generated.stderr)
    );
    let parsed = k_rust::outer::parse("literals.k", source).unwrap();
    let lowered = k_rust::outer::lower(&parsed, "LITERALS").unwrap();
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&lowered).unwrap();
    let converter = k_rust::kompile::TermConverter::new(&resolved, "LITERALS").unwrap();
    let in_process = |sort: &str, token: &str| {
        converter
            .convert(&k_rust::kast::Term::Token {
                token: token.into(),
                sort: k_rust::kast::Sort::new(sort),
            })
            .map(|pattern| k_rust::kore::printer::Printer::compact().print_pattern(&pattern))
    };
    let run = |index: usize, token: &str| {
        let input = root.join(format!("token-{index}.pgm"));
        fs::write(&input, token).unwrap();
        Command::new(&parser).arg(&input).output().unwrap()
    };

    let accepted = [
        ("String", "\"plain\"", Some(r#""plain""#)),
        ("String", "\"q\\\"b\\\\n\\n t\\t f\\f r\\r\"", None),
        (
            "String",
            "\"\u{e9}\u{2603}\u{1F642}\"",
            Some(r#""\xe9\u2603\U0001f642""#),
        ),
        (
            "String",
            "\"a\tb\u{85}c\u{2028}d\ne\"",
            Some(r#""a\tb\x85c\u2028d\ne""#),
        ),
        (
            "String",
            "\"\\x41\\xe9\\xE9\\u00e9\\u2603\\U0001F642\"",
            Some(r#""A\xe9\xe9\xe9\u2603\U0001f642""#),
        ),
        (
            "String",
            "\"\\101\\351\\777\\000\"",
            Some(r#""A\xe9\u01ff\x00""#),
        ),
        ("Bytes", "b\"\\x00\\x0f\\xff\"", Some(r#""\x00\x0f\xff""#)),
        ("Bytes", "b\"\u{e9}\"", Some(r#""\xc3\xa9""#)),
        (
            "Bytes",
            "b\"\\u00e9\\U0001f642\"",
            Some(r#""\xc3\xa9\xf0\x9f\x99\x82""#),
        ),
        (
            "Bytes",
            "b\"\\101\\377 q\\\"\\\\\\n\"",
            Some(r#""A\xff q\"\\\n""#),
        ),
        (
            "Name",
            "~\u{e9}\"\\\u{1F642}",
            Some(r#""~\xe9\"\\\U0001f642""#),
        ),
    ];
    for (index, (sort, token, literal)) in accepted.into_iter().enumerate() {
        let output = run(index, token);
        assert!(
            output.status.success(),
            "{token:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let printed = String::from_utf8(output.stdout).unwrap();
        assert!(
            printed
                .bytes()
                .all(|byte| byte == b'\n' || (b' '..=b'~').contains(&byte)),
            "{token:?}: {printed:?}"
        );
        let term = in_process(sort, token).unwrap_or_else(|error| panic!("{token:?}: {error}"));
        assert_eq!(
            printed,
            format!("inj{{Sort{sort}{{}}, SortPgm{{}}}}({term})\n"),
            "{token:?}"
        );
        if let Some(literal) = literal {
            assert_eq!(
                term,
                format!("\\dv{{Sort{sort}{{}}}}({literal})"),
                "{token:?}"
            );
        }
    }

    let rejected = [
        ("String", "\"\\q\""),
        ("String", "\"\\x4g\""),
        ("String", "\"\\x+1\""),
        ("String", "\"\\u12\""),
        ("String", "\"\\uD800\""),
        ("String", "\"\\U00110000\""),
        ("String", "\"\\8aa\""),
        ("Bytes", "b\"\\777\""),
        ("Bytes", "b\"\\uDFFF\""),
    ];
    for (index, (sort, token)) in rejected.into_iter().enumerate() {
        assert!(in_process(sort, token).is_err(), "{token:?}");
        let output = run(accepted.len() + index, token);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(!output.status.success(), "{token:?}: {stderr}");
        assert!(
            stderr.contains(&format!(
                ":1:1:1:{}:invalid {sort} token: ",
                token.chars().count() + 1
            )),
            "{token:?}: {stderr}"
        );
    }

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn a_token_subsort_reads_its_text_as_a_token_of_its_own_sort() {
    // `MyStr` has no hook, so a `MyStr` token's literal is its text as written, although the
    // phrase it covers is a `String` token whose literal decodes the escapes; `Wrapped` reads
    // the same text through a second token subsort.
    let source = r##"
module TOKSUB
  syntax String [hook(STRING.String)]
  syntax String ::= r"[\\\"](([^\\\"\\\\])|([\\\\][^\\n]))*[\\\"]" [token]
  syntax MyStr ::= String [token]
  syntax Wrapped ::= MyStr [token]
endmodule
"##;
    let program = "\"a\\nb\\x41\"";
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();
    let input = root.join("program.txt");
    fs::write(&input, program).unwrap();
    let parsed = k_rust::outer::parse("toksub.k", source).unwrap();
    let lowered = k_rust::outer::lower(&parsed, "TOKSUB").unwrap();
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&lowered).unwrap();
    let converter = k_rust::kompile::TermConverter::new(&resolved, "TOKSUB").unwrap();

    for (sort, literal) in [
        ("String", r#""a\nbA""#),
        ("MyStr", r#""\"a\\nb\\x41\"""#),
        ("Wrapped", r#""\"a\\nb\\x41\"""#),
    ] {
        let in_process = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["kast", definition.to_str().unwrap()])
            .args(["--module", "TOKSUB", "--sort", sort])
            .arg(&input)
            .output()
            .unwrap();
        assert!(
            in_process.status.success(),
            "{sort}: {}",
            String::from_utf8_lossy(&in_process.stderr)
        );
        assert_eq!(
            String::from_utf8(in_process.stdout).unwrap().trim_end(),
            format!(r#"#token("\"a\\nb\\x41\"","{sort}")"#),
            "{sort}"
        );
        let term = converter
            .convert(&k_rust::kast::Term::Token {
                token: program.into(),
                sort: k_rust::kast::Sort::new(sort),
            })
            .map(|pattern| k_rust::kore::printer::Printer::compact().print_pattern(&pattern))
            .unwrap();
        assert_eq!(term, format!("\\dv{{Sort{sort}{{}}}}({literal})"), "{sort}");

        let parser = root.join(format!("{sort}-parser"));
        let generated = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["kast", definition.to_str().unwrap()])
            .args(["--module", "TOKSUB", "--sort", sort, "--gen-parser"])
            .arg(&parser)
            .output()
            .unwrap();
        assert!(
            generated.status.success(),
            "{sort}: {}",
            String::from_utf8_lossy(&generated.stderr)
        );
        let output = Command::new(&parser).arg(&input).output().unwrap();
        assert!(
            output.status.success(),
            "{sort}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            format!("{term}\n"),
            "{sort}"
        );
    }

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn a_token_subsort_over_a_phrase_reads_the_phrase_text_as_its_token() {
    // `Pair` is no token, so a `MyTok` token's text is the input its phrase spans: from its
    // first token to its last, with the layout between them and without the layout around them.
    // `Wrapped` reads that text through a second token subsort. `Pairs` puts several such
    // phrases in one input, after a line-anchored token (whose scanner rejects matches), so
    // each phrase is reduced once the scanner has read past it. A phrase that starts with an
    // empty `Names` starts at its first token all the same, not at the layout before it, and one
    // that ends with an empty `Names` (as every `Names` phrase does) ends at its last token, not
    // at the layout after it, wherever the next token or the end of the input comes.
    let source = r##"
module TOKPHRASE
  syntax Name ::= r"[a-z]+" [token]
  syntax Mark ::= r"^#[a-z]+" [token]
  syntax Names ::= List{Name, ","}
  syntax Pair ::= Name "." Name | Mark Name | Names "!" Name | Name "?" Names
  syntax MyTok ::= Pair [token]
  syntax Wrapped ::= MyTok [token]
  syntax Pairs ::= MyTok ";" Pairs | MyTok
  syntax MyToks ::= Names [token]
  syntax Group ::= "(" MyToks ")"
endmodule
"##;
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();
    let parsed = k_rust::outer::parse("tokphrase.k", source).unwrap();
    let lowered = k_rust::outer::lower(&parsed, "TOKPHRASE").unwrap();
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&lowered).unwrap();
    let converter = k_rust::kompile::TermConverter::new(&resolved, "TOKPHRASE").unwrap();
    let token = |text: &str, sort: &str| {
        converter
            .convert(&k_rust::kast::Term::Token {
                token: text.into(),
                sort: k_rust::kast::Sort::new(sort),
            })
            .map(|pattern| k_rust::kore::printer::Printer::compact().print_pattern(&pattern))
            .unwrap()
    };

    let cases = [
        (
            "MyTok",
            "  ab .\n cd // c\n /* x */ ",
            r#"#token("ab .\n cd","MyTok")"#.to_owned(),
            token("ab .\n cd", "MyTok"),
        ),
        (
            "Wrapped",
            "  ab .\n cd // c\n /* x */ ",
            r#"#token("ab .\n cd","Wrapped")"#.to_owned(),
            token("ab .\n cd", "Wrapped"),
        ),
        (
            "MyTok",
            "  ! ab ",
            r#"#token("! ab","MyTok")"#.to_owned(),
            token("! ab", "MyTok"),
        ),
        (
            "Pairs",
            "ab.cd ;  ! ef",
            r##"`_;__TOKPHRASE_Pairs_MyTok_Pairs`(#token("ab.cd","MyTok"),#token("! ef","MyTok"))"##.to_owned(),
            format!(
                "Lbl'UndsSClnUndsUnds'TOKPHRASE'Unds'Pairs'Unds'MyTok'Unds'Pairs{{}}({},inj{{SortMyTok{{}}, SortPairs{{}}}}({}))",
                token("ab.cd", "MyTok"),
                token("! ef", "MyTok"),
            ),
        ),
        (
            "Group",
            "( a , b  )",
            r#"`(_)_TOKPHRASE_Group_MyToks`(#token("a , b","MyToks"))"#.to_owned(),
            format!(
                "Lbl'LParUndsRParUnds'TOKPHRASE'Unds'Group'Unds'MyToks{{}}({})",
                token("a , b", "MyToks"),
            ),
        ),
        (
            "Group",
            "(  )",
            r#"`(_)_TOKPHRASE_Group_MyToks`(#token("","MyToks"))"#.to_owned(),
            format!(
                "Lbl'LParUndsRParUnds'TOKPHRASE'Unds'Group'Unds'MyToks{{}}({})",
                token("", "MyToks"),
            ),
        ),
        (
            "MyToks",
            " a ,\n b // c\n /* x */ ",
            r#"#token("a ,\n b","MyToks")"#.to_owned(),
            token("a ,\n b", "MyToks"),
        ),
        (
            "Pairs",
            "ab ? cd , ef  ;  gh ?  ; ij ? ",
            r##"`_;__TOKPHRASE_Pairs_MyTok_Pairs`(#token("ab ? cd , ef","MyTok"),`_;__TOKPHRASE_Pairs_MyTok_Pairs`(#token("gh ?","MyTok"),#token("ij ?","MyTok")))"##.to_owned(),
            format!(
                "Lbl'UndsSClnUndsUnds'TOKPHRASE'Unds'Pairs'Unds'MyTok'Unds'Pairs{{}}({},Lbl'UndsSClnUndsUnds'TOKPHRASE'Unds'Pairs'Unds'MyTok'Unds'Pairs{{}}({},inj{{SortMyTok{{}}, SortPairs{{}}}}({})))",
                token("ab ? cd , ef", "MyTok"),
                token("gh ?", "MyTok"),
                token("ij ?", "MyTok"),
            ),
        ),
        (
            "Pairs",
            "ab.cd ;\n#m  x; ef . gh",
            r##"`_;__TOKPHRASE_Pairs_MyTok_Pairs`(#token("ab.cd","MyTok"),`_;__TOKPHRASE_Pairs_MyTok_Pairs`(#token("#m  x","MyTok"),#token("ef . gh","MyTok")))"##.to_owned(),
            format!(
                "Lbl'UndsSClnUndsUnds'TOKPHRASE'Unds'Pairs'Unds'MyTok'Unds'Pairs{{}}({},Lbl'UndsSClnUndsUnds'TOKPHRASE'Unds'Pairs'Unds'MyTok'Unds'Pairs{{}}({},inj{{SortMyTok{{}}, SortPairs{{}}}}({})))",
                token("ab.cd", "MyTok"),
                token("#m  x", "MyTok"),
                token("ef . gh", "MyTok"),
            ),
        ),
    ];
    for (index, (sort, program, kast, kore)) in cases.into_iter().enumerate() {
        let input = root.join(format!("program-{index}.txt"));
        fs::write(&input, program).unwrap();
        let in_process = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["kast", definition.to_str().unwrap()])
            .args(["--module", "TOKPHRASE", "--sort", sort])
            .arg(&input)
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert!(
            in_process.status.success(),
            "{sort}: {}",
            String::from_utf8_lossy(&in_process.stderr)
        );
        assert_eq!(
            String::from_utf8(in_process.stdout).unwrap().trim_end(),
            kast,
            "{sort}"
        );

        let parser = root.join(format!("{sort}-parser"));
        let generated = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["kast", definition.to_str().unwrap()])
            .args(["--module", "TOKPHRASE", "--sort", sort, "--gen-parser"])
            .arg(&parser)
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert!(
            generated.status.success(),
            "{sort}: {}",
            String::from_utf8_lossy(&generated.stderr)
        );
        let output = Command::new(&parser).arg(&input).output().unwrap();
        assert!(
            output.status.success(),
            "{sort}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            format!("{kore}\n"),
            "{sort}"
        );
    }

    fs::remove_dir_all(root).unwrap();
}

/// A located token subsort is located where its text is: from the first character of its
/// phrase's first token to the last character of its last, on both routes, whatever layout
/// follows the phrase's empty last part.
#[test]
fn a_located_token_subsort_is_located_from_its_first_token_to_its_last() {
    let source = r##"
module TOKLOC
  syntax Name ::= r"[a-z]+" [token]
  syntax Names ::= List{Name, ","}
  syntax MyToks ::= Names [token]
  syntax MyToks [locations]
  syntax Group ::= "(" MyToks ")"
endmodule
"##;
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();
    let input = root.join("program.txt");
    fs::write(&input, "( a ,\n b  \n )").unwrap();
    // The token's text and its start and end lines and columns, as KAST or KORE writes them.
    let located = |output: &[u8], text: &str, int: &str| {
        let output = String::from_utf8(output.to_vec()).unwrap();
        let captures = Regex::new(&format!(r#"{text}.*{int}, ?{int}, ?{int}, ?{int}\)"#))
            .unwrap()
            .captures(&output)
            .unwrap_or_else(|| panic!("no located token in {output}"));
        (
            captures[1].to_owned(),
            (2..=5)
                .map(|group| captures[group].parse::<u32>().unwrap())
                .collect::<Vec<_>>(),
        )
    };

    let in_process = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kast", definition.to_str().unwrap()])
        .args(["--module", "TOKLOC", "--sort", "Group"])
        .arg(&input)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        in_process.status.success(),
        "{}",
        String::from_utf8_lossy(&in_process.stderr)
    );
    assert_eq!(
        located(
            &in_process.stdout,
            r#"#token\("([^"]*)","MyToks"\)"#,
            r#"#token\("([0-9]+)","Int"\)"#,
        ),
        (r"a ,\n b".to_owned(), vec![1, 3, 2, 3])
    );

    let parser = root.join("parser");
    let generated = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kast", definition.to_str().unwrap()])
        .args(["--module", "TOKLOC", "--sort", "Group", "--gen-parser"])
        .arg(&parser)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        generated.status.success(),
        "{}",
        String::from_utf8_lossy(&generated.stderr)
    );
    let output = Command::new(&parser).arg(&input).output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        located(
            &output.stdout,
            r#"\\dv\{SortMyToks\{\}\}\("([^"]*)"\)"#,
            r#"\\dv\{SortInt\{\}\}\("([0-9]+)"\)"#,
        ),
        (r"a ,\n b".to_owned(), vec![1, 3, 2, 3])
    );

    fs::remove_dir_all(root).unwrap();
}

/// A token subsort's sort holds tokens, not values of the subsort it reads its text from: `Toks`
/// spells each `Names` phrase as a `Toks` domain value, and no `Names` list is a `Toks` value. So
/// the compiled definition states no subsort from `Names` to `Toks` (a sort of domain values has
/// no injected values), and a program that holds such a token compiles and runs.
#[test]
fn a_token_subsort_over_a_list_compiles_without_a_subsort_and_runs() {
    let source = r##"
module TOKRUN-SYNTAX
  syntax Name ::= r"[a-z]+" [token]
  syntax Names ::= List{Name, ","}
  syntax Toks ::= Names [token]
  syntax Pgm ::= "run" Toks
endmodule
module TOKRUN
  imports TOKRUN-SYNTAX
  syntax KItem ::= done(Pgm)
  configuration <k> $PGM:Pgm </k>
  rule <k> P:Pgm => done(P) </k>
endmodule
"##;
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();
    let compiled = root.join("compiled");
    kcompile_for_krun(&definition, &["--main-module", "TOKRUN"], &compiled);
    let kore = fs::read_to_string(compiled.join("definition.kore")).unwrap();
    assert!(
        kore.contains("sort SortToks{} [hasDomainValues{}()]"),
        "{kore}"
    );
    assert!(!kore.contains("inj{SortNames{}, SortToks{}}"), "{kore}");

    let program = root.join("program.txt");
    fs::write(&program, "run ab ,\n cd ").unwrap();
    let krun = |depth: Option<&str>| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command
            .args(["krun", "--definition"])
            .arg(&compiled)
            .arg(&program)
            .args(["--sort", "Pgm"]);
        if let Some(depth) = depth {
            command.args(["--depth", depth]);
        }
        let output = command.stdin(Stdio::null()).output().unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let pattern = parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap();
        k_rust::kore::printer::Printer::compact().print_pattern(&pattern)
    };
    let program =
        r#"Lblrun'UndsUnds'TOKRUN-SYNTAX'Unds'Pgm'Unds'Toks{}(\dv{SortToks{}}("ab ,\n cd"))"#;
    let initial = krun(Some("0"));
    assert!(
        initial.contains(&format!(
            "kseq{{}}(inj{{SortPgm{{}}, SortKItem{{}}}}({program}), dotk{{}}())"
        )),
        "{initial}"
    );
    let last = krun(None);
    assert!(
        last.contains(&format!(
            "kseq{{}}(Lbldone'LParUndsRParUnds'TOKRUN'Unds'KItem'Unds'Pgm{{}}({program}), dotk{{}}())"
        )),
        "{last}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn a_configuration_variable_whose_sort_reaches_a_phrase_token_places_the_program() {
    // `$PGM:Pgm` reaches the token sort `Toks` by the subsort `Pgm ::= Toks` alone; its text
    // is no program text of `Names`, so it is the configuration variable, and the rule's `T` is
    // a variable rather than the token `T`.
    let source = r##"
module T-SYNTAX
  syntax Name ::= r"[a-z]+" [token]
  syntax Names ::= List{Name, ","}
  syntax Toks ::= Names [token]
  syntax Pgm ::= Toks | done(Toks)
endmodule
module T
  imports T-SYNTAX
  configuration <k> $PGM:Pgm </k>
  rule <k> T:Toks => done(T) </k>
endmodule
"##;
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();
    let compiled = root.join("compiled");
    kcompile_for_krun(&definition, &["--main-module", "T"], &compiled);
    let kore = fs::read_to_string(compiled.join("definition.kore")).unwrap();
    assert!(!kore.contains(r#"\dv{SortToks{}}("$PGM")"#), "{kore}");
    assert!(!kore.contains(r#"\dv{SortToks{}}("T")"#), "{kore}");

    let program = root.join("program.txt");
    fs::write(&program, "ab , cd").unwrap();
    let krun = |depth: Option<&str>| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command
            .args(["krun", "--definition"])
            .arg(&compiled)
            .arg(&program)
            .args(["--sort", "Pgm"]);
        if let Some(depth) = depth {
            command.args(["--depth", depth]);
        }
        let output = command.stdin(Stdio::null()).output().unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let pattern = parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap();
        k_rust::kore::printer::Printer::compact().print_pattern(&pattern)
    };
    let program = r#"\dv{SortToks{}}("ab , cd")"#;
    let initial = krun(Some("0"));
    assert!(
        initial.contains(&format!(
            "kseq{{}}(inj{{SortToks{{}}, SortKItem{{}}}}({program}), dotk{{}}())"
        )),
        "{initial}"
    );
    let last = krun(None);
    assert!(
        last.contains(&format!(
            "kseq{{}}(inj{{SortPgm{{}}, SortKItem{{}}}}(Lbldone'LParUndsRParUnds'T-SYNTAX'Unds'Pgm'Unds'Toks{{}}({program})), dotk{{}}())"
        )),
        "{last}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kcompile_skips_bison_tools_when_the_configuration_has_no_pgm() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module NO-PGM
  syntax Value ::= "value"
  configuration <k> value </k>
endmodule
"#,
    )
    .unwrap();
    let output_directory = root.join("no-pgm-kompiled");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "NO-PGM",
            "--syntax-module",
            "NO-PGM",
            "--output-directory",
            output_directory.to_str().unwrap(),
            "--gen-glr-bison-parser",
        ])
        .env("KRUST_FLEX", root.join("must-not-run-flex"))
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!output_directory.join("parser_PGM").exists());
    assert!(fs::read_dir(&output_directory).unwrap().all(|entry| {
        !entry
            .unwrap()
            .file_name()
            .to_string_lossy()
            .starts_with("parser_")
    }));

    fs::remove_dir_all(root).unwrap();
}

#[cfg(unix)]
#[test]
fn kcompile_generates_a_nonempty_list_parser() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module NELISTS-SYNTAX
  syntax E ::= "e" [token]
  syntax Es ::= NeList{E, ","} [symbol(es)]
  syntax Pgm ::= Es
endmodule

module NELISTS
  imports NELISTS-SYNTAX
  configuration <k> $PGM:Pgm </k>
endmodule
"#,
    )
    .unwrap();
    let output_directory = root.join("nelists-kompiled");
    let kcompile = |flags: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kcompile",
                definition.to_str().unwrap(),
                "--main-module",
                "NELISTS",
                "--syntax-module",
                "NELISTS-SYNTAX",
                "--output-directory",
                output_directory.to_str().unwrap(),
                "--gen-glr-bison-parser",
            ])
            .args(flags)
            .stdin(Stdio::null())
            .output()
            .unwrap()
    };
    // Every generated parser reads lists in a bounded stack; there is no option to ask for it.
    let refused = kcompile(&["--bison-lists"]);
    assert!(!refused.status.success());
    assert!(
        String::from_utf8_lossy(&refused.stderr).contains("--bison-lists"),
        "{}",
        String::from_utf8_lossy(&refused.stderr)
    );
    let output = kcompile(&[]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let input = root.join("input.pgm");
    fs::write(&input, "e,e\n").unwrap();
    let parsed = Command::new(output_directory.join("parser_PGM"))
        .arg(&input)
        .output()
        .unwrap();
    assert!(
        parsed.status.success(),
        "{}",
        String::from_utf8_lossy(&parsed.stderr)
    );
    assert_eq!(
        String::from_utf8(parsed.stdout).unwrap(),
        "inj{SortEs{}, SortPgm{}}(Lbles{}(\\dv{SortE{}}(\"e\"),Lbles{}(\\dv{SortE{}}(\"e\"),Lbl'Stop'List'LBraQuot'es'QuotRBra'{}())))\n"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kcompile_rejects_missing_user_syntax_module_and_warns_on_missing_default() {
    let (root, definition) = fixture();
    let run = |name: &str, arguments: &[&str]| {
        let output_directory = root.join(name);
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--output-directory",
            output_directory.to_str().unwrap(),
            "--no-prelude",
        ]);
        command.args(arguments);
        command.output().unwrap()
    };

    let explicit = run("explicit", &["--syntax-module", "FOO"]);
    assert!(!explicit.status.success());
    assert!(
        String::from_utf8_lossy(&explicit.stderr)
            .contains("Could not find main syntax module with name FOO in definition."),
        "{}",
        String::from_utf8_lossy(&explicit.stderr)
    );

    let default = run("default", &["--warnings-to-errors"]);
    assert!(!default.status.success());
    assert!(
        String::from_utf8_lossy(&default.stderr).contains(
            "Could not find main syntax module with name MAIN-SYNTAX in definition.  Use --syntax-module to specify one. Using MAIN as default."
        ),
        "{}",
        String::from_utf8_lossy(&default.stderr)
    );

    let warning = "Could not find main syntax module with name MAIN-SYNTAX";
    let default_stderr = String::from_utf8_lossy(&default.stderr);
    assert_eq!(
        default_stderr.matches(warning).count(),
        1,
        "{default_stderr}"
    );
    assert!(
        default_stderr.contains("Error[MissingSyntaxModule]"),
        "{default_stderr}"
    );

    let normal = run("normal", &[]);
    let normal_stderr = String::from_utf8_lossy(&normal.stderr);
    assert!(normal.status.success(), "{normal_stderr}");
    assert_eq!(normal_stderr.matches(warning).count(), 1, "{normal_stderr}");
    assert!(
        normal_stderr.contains("Warning[MissingSyntaxModule]"),
        "{normal_stderr}"
    );

    let suppressed = run(
        "suppressed",
        &["--warnings", "none", "--warnings-to-errors"],
    );
    let suppressed_stderr = String::from_utf8_lossy(&suppressed.stderr);
    assert!(suppressed.status.success(), "{suppressed_stderr}");
    assert!(
        !suppressed_stderr.contains("MissingSyntaxModule"),
        "{suppressed_stderr}"
    );
    assert!(!suppressed_stderr.contains(warning), "{suppressed_stderr}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn warning_flags_are_exposed_by_every_diagnostic_subcommand() {
    for command in ["kcompile", "kast", "krun", "kprove"] {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([command, "--help"])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{command}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let help = String::from_utf8(output.stdout).unwrap();
        assert!(help.contains("-w, --warnings <LEVEL>"), "{command}: {help}");
        assert!(help.contains("--warnings-to-errors"), "{command}: {help}");
    }
}

#[test]
fn singleton_overload_warnings_follow_the_disambiguation_grammar_and_policy() {
    // The check and the diagnostic policy are tested in process by `definition_checks.rs`
    // (`singleton_overloads_are_warned_at_the_production_under_the_diagnostic_policy`), with
    // warnings off as well; here the warning flags reach the policy, and the warnings and
    // promoted errors are rendered with the matching exit status.
    let (root, _) = fixture();
    let definition = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/checks/singletonOverload.k");
    let run = |name: &str, warning_args: &[&str]| {
        let output_directory = root.join(name);
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "SINGLETONOVERLOAD",
            "--syntax-module",
            "SINGLETONOVERLOAD-SYNTAX",
            "--backend",
            "rust",
            "--output-directory",
            output_directory.to_str().unwrap(),
        ]);
        command.args(warning_args);
        command.output().unwrap()
    };

    let normal = run("normal", &[]);
    let normal_stderr = String::from_utf8_lossy(&normal.stderr);
    assert!(normal.status.success(), "{normal_stderr}");
    assert_eq!(
        normal_stderr.matches("Warning[SingletonOverload]").count(),
        2,
        "{normal_stderr}"
    );

    let promoted = run("promoted", &["--warnings", "all", "--warnings-to-errors"]);
    let promoted_stderr = String::from_utf8_lossy(&promoted.stderr);
    assert!(!promoted.status.success(), "{promoted_stderr}");
    assert_eq!(
        promoted_stderr.matches("Error[SingletonOverload]").count(),
        2,
        "{promoted_stderr}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn warnings_to_errors_fails_kcompile_on_an_unused_variable() {
    let (root, _) = fixture();
    let definition = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/checks/checkUnusedVar.k");
    let run = |name: &str, warning_args: &[&str]| {
        let output_directory = root.join(name);
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "CHECKUNUSEDVAR",
            "--output-directory",
            output_directory.to_str().unwrap(),
        ]);
        command.args(warning_args);
        command.output().unwrap()
    };

    let normal = run("normal", &[]);
    assert!(
        normal.status.success(),
        "{}",
        String::from_utf8_lossy(&normal.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&normal.stderr)
            .matches("Warning[UnusedVariable]")
            .count(),
        3
    );

    let error = run("error", &["--warnings-to-errors"]);
    assert!(!error.status.success());
    let stderr = String::from_utf8_lossy(&error.stderr);
    assert_eq!(
        stderr.matches("Error[UnusedVariable]").count(),
        3,
        "{stderr}"
    );
    assert!(!stderr.contains("Warning[UnusedVariable]"), "{stderr}");

    let none = run("none", &["--warnings", "none"]);
    assert!(
        none.status.success(),
        "{}",
        String::from_utf8_lossy(&none.stderr)
    );
    assert!(
        !String::from_utf8_lossy(&none.stderr).contains("UnusedVariable"),
        "{}",
        String::from_utf8_lossy(&none.stderr)
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn configured_builtin_paths_are_exempt_after_canonicalization() {
    let (root, definition) = fixture();
    let builtin_directory = root.join("builtin");
    let noncanonical_directory = root.join("alias").join("..").join("builtin");
    fs::create_dir_all(root.join("alias")).unwrap();
    fs::create_dir_all(&builtin_directory).unwrap();
    fs::write(
        builtin_directory.join("builtin.k"),
        r#"
module BUILTIN
  syntax Builtin ::= "builtin"
endmodule
"#,
    )
    .unwrap();
    fs::write(
        &definition,
        r#"
requires "builtin.k"

module MAIN
  imports BUILTIN
  syntax User ::= "user"
endmodule
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--syntax-module",
            "MAIN",
            "--output-directory",
            root.join("compiled").to_str().unwrap(),
            "--builtin-directory",
            noncanonical_directory.to_str().unwrap(),
            "--no-prelude",
            "--warnings",
            "all",
            "--warnings-to-errors",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(stderr.matches("Error[UnusedSymbol]").count(), 1, "{stderr}");
    assert!(
        stderr.contains("Symbol 'user_MAIN_User' defined but not used."),
        "{stderr}"
    );
    assert!(
        !stderr.contains("Symbol 'builtin_BUILTIN_Builtin' defined but not used."),
        "{stderr}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_deprecated_configuration_reports_every_occurrence() {
    let (root, _) = fixture();
    let definition = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/checks/deprecated.k");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "DEPRECATED",
            "--syntax-module",
            "DEPRECATED-SYNTAX",
            "--output-directory",
            root.join("compiled").to_str().unwrap(),
            "--warnings",
            "all",
            "--warnings-to-errors",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        stderr.matches("Error[DeprecatedProduction]").count(),
        11,
        "{stderr}"
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_configuration_dependent_sort_predicate_is_rejected() {
    let (root, _) = fixture();
    let definition = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/checks/invalidSortPredicate.k");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "INVALIDSORTPREDICATE",
            "--syntax-module",
            "INVALIDSORTPREDICATE",
            "--output-directory",
            root.join("compiled").to_str().unwrap(),
            "--warnings",
            "none",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(
            "Invalid sort predicate isExp that depends directly or indirectly on the current configuration. Is it possible to replace the sort predicate with a regular function?"
        ),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_proof_modules_reject_rules_and_new_syntax() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/checks");
    let semantics = fs::read_to_string(fixtures.join("errorClaim.k")).unwrap();
    let cases = [
        (
            "rule-spec.k",
            "RULE-SPEC",
            "Only claims and simplification rules are allowed in proof modules.",
        ),
        (
            "syntax-spec.k",
            "SYNTAX-SPEC",
            "Found syntax declaration in proof module. Only tokens for existing sorts are allowed.",
        ),
    ];
    for (file, module, message) in cases {
        let (root, definition) = fixture();
        let specification = fs::read_to_string(fixtures.join(file)).unwrap();
        fs::write(&definition, format!("{semantics}\n{specification}")).unwrap();
        for command in ["kprove", "kcompile"] {
            let mut invocation = Command::new(env!("CARGO_BIN_EXE_krust"));
            invocation.args([
                command,
                definition.to_str().unwrap(),
                "--main-module",
                module,
                "--definition-module",
                "ERRORCLAIM",
            ]);
            if command == "kcompile" {
                invocation
                    .arg("--for-proving")
                    .arg("--output-directory")
                    .arg(root.join("compiled"));
            }
            let output = invocation.output().unwrap();
            assert!(!output.status.success(), "{file}");
            assert!(
                String::from_utf8_lossy(&output.stderr).contains(message),
                "{file}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
        fs::remove_dir_all(root).unwrap();
    }
}

fn kcompile_checks_fixture(root: &Path, file: &str, module: &str, backend: &str) -> Output {
    let definition = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/checks")
        .join(file);
    Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            module,
            "--syntax-module",
            module,
            "--backend",
            backend,
            "--output-directory",
            root.join(file).with_extension("").to_str().unwrap(),
            "--warnings",
            "none",
        ])
        .output()
        .unwrap()
}

#[test]
fn reference_is_sort_predicates_outside_the_parsed_definition_are_accepted() {
    // reference: k/result/bin/kompile --backend haskell isSortPredicateOutsideClosure.k (exit 0)
    // reference: k/result/bin/kompile --backend haskell isSortPredicateBubbleModule.k (exit 0)
    let (root, _) = fixture();
    for (file, module) in [
        (
            "isSortPredicateOutsideClosure.k",
            "ISSORTPREDICATEOUTSIDECLOSURE",
        ),
        (
            "isSortPredicateBubbleModule.k",
            "ISSORTPREDICATEBUBBLEMODULE",
        ),
    ] {
        let output = kcompile_checks_fixture(&root, file, module, "haskell");
        assert!(
            output.status.success(),
            "{file}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_is_sort_predicate_conflicts_in_the_parsed_definition_are_rejected() {
    // reference: k/result/bin/kompile -w none --backend llvm checkIsSort.k (exit 113)
    // reference: k/result/bin/kompile --backend haskell isSortPredicateEntryModule.k (exit 113)
    let (root, _) = fixture();
    for (file, module, backend, predicates) in [
        (
            "checkIsSort.k",
            "CHECKISSORT",
            "llvm",
            &["isNonAddr", "isFoo"][..],
        ),
        (
            "isSortPredicateEntryModule.k",
            "ISSORTPREDICATEENTRYMODULE",
            "haskell",
            &["isRange"][..],
        ),
    ] {
        let output = kcompile_checks_fixture(&root, file, module, backend);
        assert!(!output.status.success(), "{file}");
        let stderr = String::from_utf8_lossy(&output.stderr);
        for predicate in predicates {
            assert!(
                stderr.contains(&format!(
                    "Error[IsSortPredicateConflict]: Syntax declaration conflicts with automatically generated {predicate} predicate."
                )),
                "{file}: {stderr}"
            );
        }
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kcompile_hook_namespaces_default_per_backend() {
    let source = r#"
module MAIN
  syntax Bytes
  syntax String
  syntax String ::= "keccak(" Bytes ")" [function, hook(KRYPTO.keccak256), symbol(keccak)]
endmodule
"#;
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();

    let kompile = |name: &str, extra: &[&str]| {
        let output_directory = root.join(name);
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--output-directory",
            output_directory.to_str().unwrap(),
            "--no-prelude",
        ]);
        command.args(extra);
        let output = command.output().unwrap();
        assert!(
            output.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        fs::read_to_string(output_directory.join("definition.kore")).unwrap()
    };
    let hooked = |kore: &str| kore.contains("hooked-symbol Lblkeccak{}");

    // The Rust backend implements KRYPTO natively, so it is admitted without a flag.
    assert!(hooked(&kompile("rust", &[])));
    // Other backends implement only the builtin hook namespaces themselves, so a plugin
    // namespace is hooked only when --hook-namespaces says its implementation is supplied.
    assert!(!hooked(&kompile("llvm", &["--backend", "llvm"])));
    assert!(hooked(&kompile(
        "llvm-admitted",
        &["--backend", "llvm", "--hook-namespaces", "HASH,KRYPTO"]
    )));

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_kcompile_accepts_hook_namespace_list_spellings() {
    // reference: k/result/bin/kompile test.k --backend haskell --hook-namespaces "A B"
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/hooks");
    let expected = fs::read_to_string(fixtures.join("hook-attributes.txt")).unwrap();
    let (root, _) = fixture();

    for (name, namespaces) in [
        ("space", &["A B"][..]),
        ("comma", &["A,B"][..]),
        ("repeated", &["A", "B"][..]),
    ] {
        let output_directory = root.join(name);
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args([
            "kcompile",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "HOOKS",
            "--syntax-module",
            "HOOKS",
            "--backend",
            "llvm",
            "--output-directory",
            output_directory.to_str().unwrap(),
        ]);
        for namespace in namespaces {
            command.args(["--hook-namespaces", namespace]);
        }
        let output = command.output().unwrap();
        assert!(
            output.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let kore = fs::read_to_string(output_directory.join("definition.kore")).unwrap();
        for hook in expected.lines() {
            assert!(kore.contains(hook), "{name} did not emit {hook}:\n{kore}");
        }
    }

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kcompile_warns_when_a_plugin_hook_namespace_is_not_selected() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/cli/hooks");
    let (root, _) = fixture();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "HOOKS",
            "--syntax-module",
            "HOOKS",
            "--backend",
            "llvm",
            "--output-directory",
            root.to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert_eq!(
        stderr.matches("UnadmittedHookNamespace").count(),
        2,
        "{stderr}"
    );
    assert!(stderr.contains("hook(A.f)"), "{stderr}");
    assert!(stderr.contains("hook(B.g)"), "{stderr}");

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kcompile_backend_selects_symbolic_or_concrete_modules() {
    let source = r#"
module SYMBOLIC [symbolic]
  syntax Exp ::= "symbolic" [symbol(symbolicOnly)]
endmodule

module CONCRETE [concrete]
  syntax Exp ::= "concrete" [symbol(concreteOnly)]
endmodule

module MAIN
  imports SYMBOLIC
  imports CONCRETE
  syntax Exp ::= "main" [symbol(main)]
endmodule
"#;
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();

    for (backend, present, absent) in [
        ("llvm", "concreteOnly", "symbolicOnly"),
        ("rust", "symbolicOnly", "concreteOnly"),
    ] {
        let output_directory = root.join(backend);
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kcompile",
                definition.to_str().unwrap(),
                "--main-module",
                "MAIN",
                "--backend",
                backend,
                "--output-directory",
                output_directory.to_str().unwrap(),
                "--no-prelude",
            ])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{backend}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let kore = fs::read_to_string(output_directory.join("definition.kore")).unwrap();
        assert!(kore.contains(present), "{backend} should retain {present}");
        assert!(!kore.contains(absent), "{backend} should exclude {absent}");
    }

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_executes_bn128_fixture_to_pinned_kore_results() {
    fn g1_result(x: &str, y: &str) -> String {
        format!(
            r#"Lbl'-LT-'generatedTop'-GT-'{{}}(
  Lbl'-LT-'k'-GT-'{{}}(
    kseq{{}}(
      inj{{SortG1Point{{}}, SortKItem{{}}}}(
        Lbl'LParUndsCommUndsRParUnds'BN128-EXECUTION'Unds'G1Point'Unds'Int'Unds'Int{{}}(
          \dv{{SortInt{{}}}}("{x}"),
          \dv{{SortInt{{}}}}("{y}")
        )
      ),
      dotk{{}}()
    )
  ),
  Lbl'-LT-'generatedCounter'-GT-'{{}}(\dv{{SortInt{{}}}}("0"))
)
"#,
        )
    }

    let bool_result = concat!(
        "Lbl'-LT-'generatedTop'-GT-'{}(\n",
        "  Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortBool{}, SortKItem{}}(\\dv{SortBool{}}(\"true\")), dotk{}())),\n",
        "  Lbl'-LT-'generatedCounter'-GT-'{}(\\dv{SortInt{}}(\"0\"))\n",
        ")\n",
    );
    let doubled = g1_result(
        "1368015179489954701390400359078579693043519447331113978918064868415326638035",
        "9918110051302171585080402603319702774565515993150576347155970296011118125764",
    );
    let cases = [
        (
            "bn128-ecadd.crypto",
            g1_result(
                "15497584038690294240042153688304417339506091937513459124271972833238779664131",
                "21762456842531143558012592863461237297422391564814111359902381816272400009493",
            ),
        ),
        ("bn128-ecmul.crypto", doubled.clone()),
        ("bn128-ecmul-reduce.crypto", doubled),
        ("bn128-pairing.crypto", bool_result.to_owned()),
        ("bn128-valid-infinity.crypto", bool_result.to_owned()),
    ];
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference");
    let definition = fixtures.join("bn128-execution.k");
    // Every program runs on one compiled definition.
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    kcompile_for_krun(
        &definition,
        &["--main-module", "BN128-EXECUTION"],
        &compiled,
    );

    for (program, expected) in cases {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["krun", "--definition"])
            .arg(&compiled)
            .args(["--sort", "Input"])
            .arg(fixtures.join(program))
            .args(["--depth", "10"])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{program}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            expected,
            "{program}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_evaluates_bn128_hooks_on_the_pinned_plugin_point_productions() {
    let (root, definition) = fixture();
    fs::write(&definition, PINNED_PLUGIN_BN128).unwrap();
    // Every check runs on one compiled definition.
    let compiled = root.join("compiled");
    kcompile_for_krun(&definition, &["--main-module", "MAIN"], &compiled);
    let boolean = |value: &str| format!(r#"\dv{{SortBool{{}}}}("{value}")"#);
    let doubled = concat!(
        "Lbl'LParUndsCommUndsRParUnds'KRYPTO'Unds'G1Point'Unds'Int'Unds'Int{}(\n",
        "              \\dv{SortInt{}}(\"1368015179489954701390400359078579693043519447331113978918064868415326638035\"),\n",
        "              \\dv{SortInt{}}(\"9918110051302171585080402603319702774565515993150576347155970296011118125764\")\n",
    )
    .to_owned();
    for (check, expected) in [
        ("valid", boolean("true")),
        ("off-curve", boolean("false")),
        ("other-constructor", boolean("false")),
        ("g2-valid", boolean("true")),
        ("add", doubled.clone()),
        ("mul", doubled),
        ("pairing", boolean("true")),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["krun", "--definition"])
            .arg(&compiled)
            .args(["--sort", "Check", "--expression", check, "--depth", "10"])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{check}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let output = String::from_utf8(output.stdout).unwrap();
        assert!(output.contains("Lblresult"), "{check}: {output}");
        assert!(output.contains(&expected), "{check}: {output}");
        assert!(!output.contains("BN128"), "{check}: {output}");
        assert!(!output.contains("isValid"), "{check}: {output}");
    }

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_completes_star_cell_heating_with_one_or_two_cells() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/execution/star-cell-heating");
    let definition = fixtures.join("test.k");
    // The three programs of the List-cell variant run on one compiled definition; the single run
    // of the Set-cell variant below compiles from source.
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    kcompile_for_krun(
        &definition,
        &[
            "--main-module",
            "STAR-CELL-HEATING",
            "--syntax-module",
            "STAR-CELL-HEATING-SYNTAX",
        ],
        &compiled,
    );
    for (program, thread_cells, next) in [
        ("one.pgm", 1, "1"),
        ("two.pgm", 2, "2"),
        ("two-late.pgm", 2, "2"),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["krun", "--definition"])
            .arg(&compiled)
            .arg(fixtures.join(program))
            .args(["--sort", "Stmt"])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{program}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert_eq!(
            stdout.matches("Lbl'-LT-'thread'-GT-'{}").count(),
            thread_cells,
            "{program}: {stdout}"
        );
        assert_eq!(
            stdout.matches("Lbl'-LT-'k'-GT-'{}(dotk{}())").count(),
            thread_cells,
            "{program}: {stdout}"
        );
        assert!(
            stdout.contains(&format!(
                "Lbl'-LT-'next'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"{next}\"))"
            )),
            "{program}: {stdout}"
        );
    }

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            fixtures.join("two.pgm").to_str().unwrap(),
            "--main-module",
            "STAR-CELL-HEATING-SET",
            "--syntax-module",
            "STAR-CELL-HEATING-SYNTAX",
            "--sort",
            "Stmt",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "Set-cell variant: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    // Set concatenation is nilpotent: when the spawned task completes it equals the first one,
    // and a cell set that holds one cell twice is `\bottom`. The step that completes it applies
    // with an undefined result (docs/compatibility.md#set-concatenation-is-nilpotent).
    assert!(
        stderr.contains("execution ended with no successor at depth 10")
            && stderr.contains("applied with an undefined result"),
        "{stderr}"
    );
    assert_eq!(
        stdout.trim(),
        "\\bottom{SortGeneratedTopCell{}}()",
        "{stdout}"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_surface_pattern_projects_set_typed_star_cell() {
    // The reference krun additionally prints _DotVar0/_DotVar1 bindings that krust projects away.
    // At depth zero, the reference binds KK to the injected Stmt program. `two.pgm` has no final
    // state: its two tasks complete to one cell, twice, which is `\bottom` (set concatenation is
    // nilpotent; `krun_completes_star_cell_heating_with_one_or_two_cells`), so only its initial
    // state is projected.
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/execution/star-cell-heating");
    let definition = fixtures.join("test.k");
    // Every run uses one compiled definition of the Set-cell variant.
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    kcompile_for_krun(
        &definition,
        &[
            "--main-module",
            "STAR-CELL-HEATING-SET",
            "--syntax-module",
            "STAR-CELL-HEATING-SYNTAX",
        ],
        &compiled,
    );
    for program in ["one.pgm"] {
        for (surface_pattern, expected_binding) in [
            ("<k> .K </k>", None),
            ("<k> KK:K </k>", Some(parse_pattern("dotk{}()").unwrap())),
        ] {
            let output = Command::new(env!("CARGO_BIN_EXE_krust"))
                .args(["krun", "--definition"])
                .arg(&compiled)
                .arg(fixtures.join(program))
                .args([
                    "--sort",
                    "Stmt",
                    "--io",
                    "off",
                    "--pattern",
                    surface_pattern,
                ])
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{program}, {surface_pattern}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            let actual = parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap();
            if let Some(expected_binding) = expected_binding {
                assert_eq!(
                    pattern_binding(&actual, "VarKK"),
                    Some(&expected_binding),
                    "{program}: {actual:?}"
                );
            } else {
                assert!(
                    matches!(actual, Pattern::Top { .. }),
                    "{program}: {actual:?}"
                );
            }
        }
    }

    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["krun", "--definition"])
        .arg(&compiled)
        .arg(fixtures.join("two.pgm"))
        .args([
            "--sort",
            "Stmt",
            "--io",
            "off",
            "--depth",
            "0",
            "--pattern",
            "<k> KK:K </k>",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let actual = parse_pattern(&String::from_utf8(output.stdout).unwrap()).unwrap();
    let binding = pattern_binding(&actual, "VarKK").expect("KK binding");
    let Pattern::Application { symbol, arguments } = binding else {
        panic!("expected K sequence, got {binding:?}");
    };
    assert_eq!(symbol.name, "kseq", "{binding:?}");
    let Some(Pattern::Application {
        symbol: injection, ..
    }) = arguments.first()
    else {
        panic!("expected injected Stmt at the head of {binding:?}");
    };
    assert_eq!(injection.name, "inj", "{binding:?}");
    assert_eq!(
        injection
            .sort_parameters
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        ["SortStmt{}", "SortKItem{}"],
        "{binding:?}"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_solves_map_keys_bound_by_a_star_set_cell_before_nested_sets() {
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/execution/star-cell-map-nested-set");
    let definition = fixtures.join("test.k");
    // Every program runs on one compiled definition.
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    kcompile_for_krun(
        &definition,
        &[
            "--main-module",
            "STAR-CELL-MAP-NESTED-SET",
            "--syntax-module",
            "STAR-CELL-MAP-NESTED-SET-SYNTAX",
        ],
        &compiled,
    );
    for (program, cast_remains) in [
        ("neg-two.pgm", true),
        ("pos-two.pgm", false),
        ("pos2-two.pgm", false),
        ("two.pgm", false),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["krun", "--definition"])
            .arg(&compiled)
            .arg(fixtures.join(program))
            .args(["--sort", "Stmt"])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{program}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert_eq!(
            stdout.contains("Lblcast"),
            cast_remains,
            "{program}: {stdout}"
        );
        assert!(!stdout.contains("\\or{"), "{program}: {stdout}");
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_executes_evm_optimized_add_fixture_to_pinned_kore_result() {
    let expected = concat!(
        "Lbl'-LT-'generatedTop'-GT-'{}(\n",
        "  Lbl'-LT-'kevm'-GT-'{}(\n",
        "    Lbl'-LT-'k'-GT-'{}(dotk{}()),\n",
        "    Lbl'-LT-'schedule'-GT-'{}(LblCANCUN'Unds'EVM-OPTIMIZED-ADD'Unds'Schedule{}()),\n",
        "    Lbl'-LT-'useGas'-GT-'{}(\\dv{SortBool{}}(\"false\")),\n",
        "    Lbl'-LT-'ethereum'-GT-'{}(\n",
        "      Lbl'-LT-'evm'-GT-'{}(\n",
        "        Lbl'-LT-'callState'-GT-'{}(\n",
        "          Lbl'-LT-'wordStack'-GT-'{}(\n",
        "            Lbl'UndsColnUndsUnds'EVM-OPTIMIZED-ADD'Unds'WordStack'Unds'Int'Unds'WordStack{}(\n",
        "              \\dv{SortInt{}}(\"11\"),\n",
        "              Lbl'Stop'WordStack'Unds'EVM-OPTIMIZED-ADD'Unds'WordStack{}()\n",
        "            )\n",
        "          ),\n",
        "          Lbl'-LT-'pc'-GT-'{}(\\dv{SortInt{}}(\"1\")),\n",
        "          Lbl'-LT-'gas'-GT-'{}(\\dv{SortInt{}}(\"99\"))\n",
        "        )\n",
        "      )\n",
        "    )\n",
        "  ),\n",
        "  Lbl'-LT-'generatedCounter'-GT-'{}(\\dv{SortInt{}}(\"0\"))\n",
        ")\n",
    );
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference");
    let definition = fixtures.join("evm-optimized-add.k");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "EVM-OPTIMIZED-ADD",
            "--sort",
            "Input",
            "--expression",
            "optimized-add",
            "--depth",
            "10",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
}

#[test]
fn krun_executes_invalid_ecdsa_recovery_to_empty_bytes() {
    let expected = concat!(
        "Lbl'-LT-'generatedTop'-GT-'{}(\n",
        "  Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortBytes{}, SortKItem{}}(\\dv{SortBytes{}}(\"\")), dotk{}())),\n",
        "  Lbl'-LT-'generatedCounter'-GT-'{}(\\dv{SortInt{}}(\"0\"))\n",
        ")\n",
    );
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference");
    let definition = fixtures.join("crypto-execution.k");
    let program = fixtures.join("ecdsa-invalid.crypto");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "CRYPTO-EXECUTION",
            "--sort",
            "Input",
            program.to_str().unwrap(),
            "--depth",
            "10",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
}

#[test]
fn krun_executes_fresh_constant_fixture_to_pinned_kore_result() {
    let expected = concat!(
        "Lbl'-LT-'generatedTop'-GT-'{}(\n",
        "  Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortInt{}, SortKItem{}}(\\dv{SortInt{}}(\"0\")), dotk{}())),\n",
        "  Lbl'-LT-'generatedCounter'-GT-'{}(\\dv{SortInt{}}(\"1\"))\n",
        ")\n",
    );
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference");
    let definition = fixtures.join("fresh-constants.k");
    let program = fixtures.join("fresh.input");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "FRESH-CONSTANTS",
            "--sort",
            "Input",
            program.to_str().unwrap(),
            "--depth",
            "10",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
}

#[test]
fn krun_executes_float_fixture_to_pinned_kore_results() {
    fn scalar_result(sort: &str, value: &str) -> String {
        if sort == "Float" {
            return format!(
                concat!(
                    "Lbl'-LT-'generatedTop'-GT-'{{}}(\n",
                    "  Lbl'-LT-'k'-GT-'{{}}(\n",
                    "    kseq{{}}(inj{{SortFloat{{}}, SortKItem{{}}}}(\\dv{{SortFloat{{}}}}(\"{value}\")), dotk{{}}())\n",
                    "  ),\n",
                    "  Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\"))\n",
                    ")\n",
                ),
                value = value,
            );
        }
        format!(
            concat!(
                "Lbl'-LT-'generatedTop'-GT-'{{}}(\n",
                "  Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{Sort{sort}{{}}, SortKItem{{}}}}(\\dv{{Sort{sort}{{}}}}(\"{value}\")), dotk{{}}())),\n",
                "  Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\"))\n",
                ")\n",
            ),
            sort = sort,
            value = value,
        )
    }

    let cases = [
        (
            "float-add.float",
            scalar_result("Float", "3.75000000e+00p24x8"),
        ),
        (
            "float-round-tie.float",
            scalar_result("Float", "1.00000000e+00p24x8"),
        ),
        (
            "float-sqrt.float",
            scalar_result("Float", "2.00000000e+00p24x8"),
        ),
        (
            "float-min-zero.float",
            scalar_result("Float", "-0e+00p24x8"),
        ),
        ("float-nan-eq.float", scalar_result("Bool", "false")),
        ("float2int-tie.float", scalar_result("Int", "12")),
        (
            "float-max-value.float",
            scalar_result("Float", "3.40282347e+38p24x8"),
        ),
    ];
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference");
    let definition = fixtures.join("float-execution.k");
    // Every program runs on one compiled definition.
    let (root, _) = fixture();
    let compiled = root.join("compiled");
    kcompile_for_krun(
        &definition,
        &["--main-module", "FLOAT-EXECUTION"],
        &compiled,
    );

    for (program, expected) in cases {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["krun", "--definition"])
            .arg(&compiled)
            .args(["--sort", "Input"])
            .arg(fixtures.join(program))
            .args(["--depth", "10"])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{program}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            expected,
            "{program}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn reference_krun_evaluates_a_named_field_projection_program() {
    // reference: k/result/bin/kompile --backend llvm test.k && k/result/bin/krun 3.test (regression-new/record-llvm: `foo(test(5, 10, 15))` prints `10`)
    let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/inner/record-projection");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            fixtures.join("test.k").to_str().unwrap(),
            "--main-module",
            "TEST",
            "--syntax-module",
            "TEST",
            "--sort",
            "KItem",
            "--expression",
            "foo(test(5, 10, 15))",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains(r#"\dv{SortInt{}}("10")"#), "{output}");
    assert!(!output.contains("project"), "{output}");
}

#[test]
fn kcompile_writes_phase_timings_json() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax Input ::= Int | "twice" "(" Int ")" [macro]
  rule twice(I) => I +Int I
  configuration <k> $PGM:Input </k>
endmodule
"#,
    )
    .unwrap();
    let timings_path = root.join("kcompile-timings.json");
    let trace_path = root.join("kcompile-trace.json");
    let output_directory = root.join("compiled");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--output-directory",
            output_directory.to_str().unwrap(),
            "--timings",
            timings_path.to_str().unwrap(),
            "--trace",
            trace_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stdout.is_empty());
    assert!(output_directory.join("definition.kore").is_file());
    let trace: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&trace_path).unwrap()).unwrap();
    let events = trace.as_array().unwrap();
    assert!(events.iter().any(|event| event["name"] == "phase"));
    assert!(
        events
            .iter()
            .any(|event| event["args"]["aggregation_rule"].is_string())
    );
    let timings: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&timings_path).unwrap()).unwrap();
    assert_eq!(timings["version"], k_rust::timings::TIMINGS_SCHEMA_VERSION);
    for key in [
        "load_seconds",
        "compile_seconds",
        "write_seconds",
        "load_wall_seconds",
        "compile_wall_seconds",
        "write_wall_seconds",
        "load_unattributed_seconds",
        "compile_unattributed_seconds",
        "write_unattributed_seconds",
        "total_wall_seconds",
    ] {
        assert!(timings[key].as_f64().unwrap() >= 0.0, "{key}: {timings}");
    }
    let phases = timings["phases"].as_array().unwrap();
    let names = phases
        .iter()
        .map(|phase| phase["name"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(names[0], "resolve entry source", "{names:?}");
    assert_eq!(names[1], "parse sources", "{names:?}");
    assert!(names.contains(&"lower files"), "{names:?}");
    assert!(names.contains(&"print definition.kore"), "{names:?}");
    assert_eq!(names.last(), Some(&"write artifacts"), "{names:?}");
    assert!(
        phases
            .iter()
            .all(|phase| phase["seconds"].as_f64().unwrap() >= 0.0),
        "{timings}"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn krun_writes_phase_timings_json() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax Input ::= Int | "twice" "(" Int ")" [macro]
  rule twice(I) => I +Int I
  configuration <k> $PGM:Input </k>
endmodule
"#,
    )
    .unwrap();
    let timings_path = root.join("krun-timings.json");
    let krun = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "Input",
            "--expression",
            "twice(21)",
            "--depth",
            "1",
            "--timings",
            timings_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        krun.status.success(),
        "{}",
        String::from_utf8_lossy(&krun.stderr)
    );
    let stdout = String::from_utf8(krun.stdout).unwrap();
    assert!(stdout.contains(r#"\dv{SortInt{}}("42")"#), "{stdout}");
    let timings: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&timings_path).unwrap()).unwrap();
    for key in [
        "program_parse_seconds",
        "config_vars_parse_seconds",
        "internalize_seconds",
        "execute_seconds",
        "output_seconds",
    ] {
        assert!(timings[key].as_f64().unwrap() >= 0.0, "{key}: {timings}");
    }
    let compile = &timings["compile"];
    assert_eq!(compile["version"], k_rust::timings::TIMINGS_SCHEMA_VERSION);
    assert!(
        compile["load_seconds"].as_f64().unwrap() >= 0.0,
        "{timings}"
    );
    assert!(
        compile["compile_seconds"].as_f64().unwrap() >= 0.0,
        "{timings}"
    );
    assert_eq!(compile["write_seconds"], 0.0, "{timings}");
    for key in [
        "load_wall_seconds",
        "compile_wall_seconds",
        "write_wall_seconds",
        "load_unattributed_seconds",
        "compile_unattributed_seconds",
        "write_unattributed_seconds",
        "total_wall_seconds",
    ] {
        assert!(compile[key].as_f64().unwrap() >= 0.0, "{key}: {timings}");
    }
    let names = compile["phases"]
        .as_array()
        .unwrap()
        .iter()
        .map(|phase| phase["name"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(names[0], "resolve entry source", "{names:?}");
    assert!(names.contains(&"lower files"), "{names:?}");
    assert_eq!(names.last(), Some(&"print macros.kore"), "{names:?}");
    fs::remove_dir_all(root).unwrap();
}

/// A definition that loads and passes every transformation stage, and whose compile fails late,
/// at the hook namespace check, once its unadmitted hook namespace is promoted to an error.
const LATE_FAILURE: &str = r#"
module LATE-SYNTAX
endmodule
module LATE
  imports INT
  syntax Int ::= nope(Int) [function, hook(NOPE.nope)]
  rule nope(_) => 0
endmodule
"#;

/// The compile phases of a timings file, in order: every phase from the compile's first phase on.
/// Panics when the file records no compile phase.
fn compile_phase_names(timings: &serde_json::Value) -> Vec<&str> {
    let names = timings["phases"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|phase| phase["depth"] == 0)
        .map(|phase| phase["name"].as_str().unwrap())
        .collect::<Vec<_>>();
    let first_compile_phase = k_rust::kompile::pipeline::prologue_descriptions()[0].name;
    let start = names
        .iter()
        .position(|name| *name == first_compile_phase)
        .unwrap_or_else(|| panic!("no compile phase was recorded: {names:?}"));
    assert_eq!(names[0], "resolve entry source", "{names:?}");
    names[start..].to_vec()
}

/// The compile phases a successful compile records, in order, through the first phase named
/// `last`: the prologue, the transformation stages and the emission phases before the Bison and
/// artifact-write phases.
fn expected_compile_phases_through(last: &str) -> Vec<&'static str> {
    use k_rust::kompile::pipeline::{EMISSION_PHASES, prologue_descriptions, stage_descriptions};
    let expected = prologue_descriptions()
        .into_iter()
        .chain(stage_descriptions())
        .map(|description| description.name)
        .chain(EMISSION_PHASES[..EMISSION_PHASES.len() - 2].iter().copied())
        .collect::<Vec<_>>();
    let end = expected
        .iter()
        .position(|name| *name == last)
        .unwrap_or_else(|| panic!("{last:?} should be a compile phase: {expected:?}"));
    expected[..=end].to_vec()
}

/// A kcompile timings file that records no artifact-write phase, and whose total is the sum of
/// its three groups' wall spans.
fn assert_no_write_phases(timings: &serde_json::Value) {
    assert_eq!(timings["version"], k_rust::timings::TIMINGS_SCHEMA_VERSION);
    assert_eq!(timings["write_seconds"], 0.0, "{timings}");
    let names = timings["phases"]
        .as_array()
        .unwrap()
        .iter()
        .map(|phase| phase["name"].as_str().unwrap())
        .collect::<Vec<_>>();
    for write_phase in ["generate bison parser", "write artifacts"] {
        assert!(!names.contains(&write_phase), "{names:?}");
    }
    assert_total_is_the_sum_of_the_group_spans(timings);
}

/// A kcompile timings file's `total_wall_seconds` is the sum of its three groups' wall spans.
fn assert_total_is_the_sum_of_the_group_spans(timings: &serde_json::Value) {
    let wall = |key: &str| timings[key].as_f64().unwrap();
    let groups =
        wall("load_wall_seconds") + wall("compile_wall_seconds") + wall("write_wall_seconds");
    // The file holds the exact sum; the tolerance absorbs serde_json's float parsing, which is
    // not correctly rounding without its `float_roundtrip` feature and can read a value one ulp
    // away from the one written.
    assert!(
        (wall("total_wall_seconds") - groups).abs() < 1e-9,
        "{groups}: {timings}"
    );
}

/// A run whose `--timings` file cannot be written still fails with its own error and exit
/// status; the failed timings write is reported before it.
#[test]
fn kcompile_keeps_its_error_when_the_timings_of_a_failed_run_cannot_be_written() {
    let (root, definition) = fixture();
    fs::write(&definition, LATE_FAILURE).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("kcompile")
        .arg(&definition)
        .args(["--main-module", "LATE", "--warnings-to-errors"])
        .arg("--output-directory")
        .arg(root.join("compiled"))
        .arg("--timings")
        .arg(root.join("missing-directory").join("timings.json"))
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stderr}");
    let warning = stderr
        .find("warning: the timings of the failed run were not written: ")
        .unwrap_or_else(|| panic!("{stderr}"));
    let error = stderr
        .find(
            "error: kcompile stage \"hook namespace checks\" failed: hook namespace checks failed",
        )
        .unwrap_or_else(|| panic!("{stderr}"));
    assert!(warning < error, "{stderr}");
    assert!(!root.join("missing-directory").exists());
    fs::remove_dir_all(root).unwrap();
}

/// A compile whose artifact write fails records the write group up to the failed write, with
/// the group's measured span, and exits with the write's own error.
#[test]
fn kcompile_timings_measure_a_failed_artifact_write() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax Input ::= Int
  configuration <k> $PGM:Input </k>
endmodule
"#,
    )
    .unwrap();
    let output_directory = root.join("compiled");
    // A directory where the first artifact file goes makes that write fail.
    fs::create_dir_all(output_directory.join("definition.kore")).unwrap();
    let timings_path = root.join("kcompile-timings.json");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("kcompile")
        .arg(&definition)
        .args(["--main-module", "MAIN"])
        .arg("--output-directory")
        .arg(&output_directory)
        .arg("--timings")
        .arg(&timings_path)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stderr}");
    assert!(stderr.contains("error: Is a directory"), "{stderr}");
    let timings: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&timings_path).unwrap()).unwrap();
    let mut expected = expected_compile_phases_through("print macros.kore");
    expected.push("write artifacts");
    assert_eq!(compile_phase_names(&timings), expected);
    assert!(
        timings["write_seconds"].as_f64().unwrap() > 0.0,
        "{timings}"
    );
    assert!(
        timings["write_wall_seconds"].as_f64().unwrap()
            >= timings["write_seconds"].as_f64().unwrap(),
        "{timings}"
    );
    assert_total_is_the_sum_of_the_group_spans(&timings);
    fs::remove_dir_all(root).unwrap();
}

/// A compile that fails at its hook namespace check still writes the load phases and every
/// compile phase that ran, through the failed one, and exits with the compile's own error.
#[test]
fn kcompile_timings_are_written_when_compilation_fails() {
    let (root, definition) = fixture();
    fs::write(&definition, LATE_FAILURE).unwrap();
    let timings_path = root.join("kcompile-timings.json");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("kcompile")
        .arg(&definition)
        .args(["--main-module", "LATE", "--warnings-to-errors"])
        .arg("--output-directory")
        .arg(root.join("compiled"))
        .arg("--timings")
        .arg(&timings_path)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "{stderr}");
    assert!(
        stderr.contains(
            "error: kcompile stage \"hook namespace checks\" failed: hook namespace checks failed"
        ),
        "{stderr}"
    );
    let timings: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&timings_path).unwrap()).unwrap();
    assert!(timings["load_seconds"].as_f64().unwrap() > 0.0, "{timings}");
    assert_eq!(
        compile_phase_names(&timings),
        expected_compile_phases_through("hook namespace checks")
    );
    assert_no_write_phases(&timings);
    fs::remove_dir_all(root).unwrap();
}

/// A compile that succeeds and then fails the critical-pair check promoted by
/// `--warnings-to-errors` writes every compile phase and no write phase.
#[test]
fn kcompile_timings_are_written_when_a_post_compile_check_fails() {
    let (root, definition) = fixture();
    fs::write(&definition, NON_JOINING_ANYWHERE).unwrap();
    let timings_path = root.join("kcompile-timings.json");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("kcompile")
        .arg(&definition)
        .args([
            "--main-module",
            "NJ",
            "--syntax-module",
            "NJ",
            "--warnings-to-errors",
        ])
        .arg("--output-directory")
        .arg(root.join("compiled"))
        .arg("--timings")
        .arg(&timings_path)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "{stderr}");
    assert!(
        stderr.contains(
            "error: the load-time critical-pair check of the compiled definition reported \
             warnings promoted to errors"
        ),
        "{stderr}"
    );
    let timings: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&timings_path).unwrap()).unwrap();
    assert_eq!(
        compile_phase_names(&timings),
        expected_compile_phases_through("print macros.kore")
    );
    assert_no_write_phases(&timings);
    fs::remove_dir_all(root).unwrap();
}

/// A krun whose compile fails writes its timings document with the compile phases that ran and
/// zero execution fields.
#[test]
fn krun_timings_are_written_when_compilation_fails() {
    let (root, definition) = fixture();
    fs::write(&definition, LATE_FAILURE).unwrap();
    let timings_path = root.join("krun-timings.json");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("krun")
        .args([
            "-m",
            "LATE",
            "--warnings-to-errors",
            "-s",
            "Int",
            "-e",
            "1",
            "--io",
            "off",
        ])
        .arg("--timings")
        .arg(&timings_path)
        .arg(&definition)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stderr}");
    assert!(
        stderr.contains("error: kcompile stage \"hook namespace checks\" failed"),
        "{stderr}"
    );
    let timings: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&timings_path).unwrap()).unwrap();
    for key in [
        "program_parse_seconds",
        "config_vars_parse_seconds",
        "internalize_seconds",
        "execute_seconds",
        "output_seconds",
    ] {
        assert_eq!(timings[key], 0.0, "{key}: {timings}");
    }
    let compile = &timings["compile"];
    assert_eq!(
        compile_phase_names(compile),
        expected_compile_phases_through("hook namespace checks")
    );
    assert_no_write_phases(compile);
    fs::remove_dir_all(root).unwrap();
}

fn rewrite_example() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/rewrite.k")
}

fn kcompile_rewrite_example(root: &Path, counters: Option<&Path>) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
    command
        .arg("kcompile")
        .arg(rewrite_example())
        .args(["--main-module", "REWRITE", "--output-directory"])
        .arg(root.join("compiled"))
        .env_remove("KRUST_COUNTERS");
    if let Some(counters) = counters {
        command.env("KRUST_COUNTERS", counters);
    }
    command.output().unwrap()
}

// Test builds enable the `measure` feature through the crate's own dev-dependency, so the dump is
// available here; a feature-off `krust` never reads `KRUST_COUNTERS`.
#[test]
fn krust_counters_writes_every_counter_in_schema_order_on_success_and_failure() {
    let (root, _) = fixture();
    let counters = root.join("counters.json");
    let output = kcompile_rewrite_example(&root, Some(&counters));
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = fs::read_to_string(&counters).unwrap();
    let document: serde_json::Value = serde_json::from_str(&text).unwrap();
    assert_eq!(document["format"], "krust-counters");
    assert_eq!(
        document["version"],
        k_rust_kore::measure::COUNTER_SCHEMA_VERSION
    );
    let written = document["counters"].as_object().unwrap();
    let expected = k_rust_kore::measure::Counter::ALL.map(k_rust_kore::measure::Counter::name);
    assert_eq!(written.len(), expected.len());
    // Keys appear in `Counter::ALL` order so that diffs between runs are line-stable.
    let positions = expected
        .iter()
        .map(|name| text.find(&format!("\"{name}\":")).unwrap())
        .collect::<Vec<_>>();
    assert!(positions.windows(2).all(|pair| pair[0] < pair[1]));
    assert!(written["kompile.resolve_calls"].as_u64().unwrap() > 0);
    // The prelude modules reachable from REWRITE carry rule bubbles too.
    assert!(written["kompile.rule_bubbles_parsed"].as_u64().unwrap() > 0);
    assert!(written["parser.parse_attempts"].as_u64().unwrap() > 0);
    assert_eq!(written["rewrite.steps"], 0);

    let failed_counters = root.join("failed-counters.json");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("kcompile")
        .arg(root.join("missing.k"))
        .args(["--main-module", "REWRITE", "--output-directory"])
        .arg(root.join("failed"))
        .env("KRUST_COUNTERS", &failed_counters)
        .output()
        .unwrap();
    assert!(!output.status.success());
    let document: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&failed_counters).unwrap()).unwrap();
    assert_eq!(
        document["counters"].as_object().unwrap().len(),
        k_rust_kore::measure::Counter::COUNT
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kcompile_writes_no_counter_file_without_krust_counters() {
    let (root, _) = fixture();
    let output = kcompile_rewrite_example(&root, None);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut entries = fs::read_dir(&root)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .collect::<Vec<_>>();
    entries.sort();
    assert_eq!(entries, ["base.k", "compiled", "definition.k"]);
    fs::remove_dir_all(root).unwrap();
}

/// The repository's `examples/` definition named `name`.
fn example(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples")
        .join(name)
}

/// The standard output of a `krust` run that must succeed, as `scripts/backend-smoke.sh` reads
/// it (`set -e` and a command substitution of standard output).
fn successful_stdout(command: &mut Command) -> String {
    let output = command.stdin(Stdio::null()).output().unwrap();
    assert!(
        output.status.success(),
        "{command:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

/// The number of lines of `text` that contain `needle`, which is what `grep -c` counts.
fn lines_containing(text: &str, needle: &str) -> usize {
    text.lines().filter(|line| line.contains(needle)).count()
}

/// The first two flows of `scripts/backend-smoke.sh`: `kcompile` of `examples/rewrite.k` writes
/// the three non-empty backend KORE files, and the in-process backend rewrites `a` to `b`. The
/// run reads that compilation rather than compiling the example again.
#[test]
fn backend_smoke_kcompile_writes_kore_artifacts_that_krun_rewrites() {
    let (root, _) = fixture();
    let compiled = root.join("rust");
    kcompile_for_krun(
        &example("rewrite.k"),
        &["--main-module", "REWRITE"],
        &compiled,
    );
    for artifact in ["definition.kore", "syntaxDefinition.kore", "macros.kore"] {
        let length = fs::metadata(compiled.join(artifact))
            .map(|metadata| metadata.len())
            .unwrap_or(0);
        assert!(length > 0, "{artifact} is missing or empty");
    }

    let execution = successful_stdout(
        Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["krun", "--definition"])
            .arg(&compiled)
            .args(["--sort", "State", "--expression", "a", "--depth", "10"]),
    );
    assert!(execution.contains("Lblb{}()"), "{execution}");
    fs::remove_dir_all(root).unwrap();
}

/// `scripts/backend-smoke.sh`: two equal builtin Lists built by one rule unify through the full
/// frontend and backend path, so the second rule fires and both cells keep their three items.
#[test]
fn backend_smoke_krun_matches_equal_builtin_lists() {
    let execution = successful_stdout(
        Command::new(env!("CARGO_BIN_EXE_krust"))
            .arg("krun")
            .arg(example("list-unification.k"))
            .args([
                "--main-module",
                "LIST-UNIFICATION",
                "--sort",
                "Val",
                "--expression",
                "test1",
                "--depth",
                "10",
            ]),
    );
    assert!(
        execution.contains("Lblsuccess'Unds'LIST-UNIFICATION'Unds'Val{}()"),
        "{execution}"
    );
    assert_eq!(
        lines_containing(&execution, "LblListItem{}"),
        6,
        "{execution}"
    );
}

/// `scripts/backend-smoke.sh`: a rule selects the concrete Map entry keyed by the `<k>` value
/// and removes it through AC framing, leaving the two other entries.
#[test]
fn backend_smoke_krun_removes_a_concrete_map_entry_through_ac_framing() {
    let execution = successful_stdout(
        Command::new(env!("CARGO_BIN_EXE_krust"))
            .arg("krun")
            .arg(example("map-framing.k"))
            .args([
                "--main-module",
                "MAP-FRAMING",
                "--sort",
                "Val",
                "--expression",
                "a",
                "--depth",
                "10",
            ]),
    );
    assert!(
        execution.contains("Lblb'Unds'MAP-FRAMING'Unds'Val{}()"),
        "{execution}"
    );
    assert!(
        execution.contains("Lblc'Unds'MAP-FRAMING'Unds'Val{}()"),
        "{execution}"
    );
    assert_eq!(
        lines_containing(&execution, "Lbl'UndsPipe'-'-GT-Unds'{}("),
        2,
        "{execution}"
    );
}

/// `scripts/backend-smoke.sh`: the one-path reachability claim of `examples/reachability.k` is
/// proven with the in-process solver.
#[test]
fn backend_smoke_kprove_proves_a_reachability_claim() {
    let proof = successful_stdout(
        Command::new(env!("CARGO_BIN_EXE_krust"))
            .arg("kprove")
            .arg(example("reachability.k"))
            .args([
                "--main-module",
                "REACHABILITY",
                "--claim",
                "reaches-b",
                "--depth",
                "10",
            ]),
    );
    assert!(proof.contains("claim reaches-b: proven"), "{proof}");
}

/// Prove each named claim of an inlined specification on its own and return the verdict word
/// `krust kprove` reports for it (`proven`, `disproved`, `indeterminate`, ...), or `error` with
/// its diagnostic on standard error when the prover rejects the claim.
fn kprove_claim_verdicts(
    definition: (&str, &str),
    specification: (&str, &str),
    main_module: &str,
    definition_module: &str,
    claims: &[&str],
) -> Vec<(String, String)> {
    kprove_claim_leaves(
        definition,
        specification,
        main_module,
        definition_module,
        claims,
        &[],
    )
    .into_iter()
    .map(|(claim, verdict, _)| (claim, verdict))
    .collect()
}

/// Each claim's verdict word and the outcome word of each of its reported leaves
/// (`Stuck`, `Vacuous`, ...), in output order. Each claim is proven by its own `kprove` process;
/// when there is more than one, they share one `kcompile --for-proving` of the specification.
fn kprove_claim_leaves(
    definition: (&str, &str),
    specification: (&str, &str),
    main_module: &str,
    definition_module: &str,
    claims: &[&str],
    extra_args: &[&str],
) -> Vec<(String, String, Vec<String>)> {
    let fixture = ProofFixture::new(definition, specification, main_module, definition_module);
    let fixture = if claims.len() > 1 {
        fixture.compiled()
    } else {
        fixture
    };
    fixture.claim_leaves(claims, extra_args)
}

/// The definition and specification of a claims test, written into the test's own temporary
/// directory. [`ProofFixture::compiled`] compiles the specification once, so that every later
/// `kprove` of the test reads that one compilation instead of compiling the same sources again.
/// Each claim is still proven by its own process, so no claim sees another as a circularity.
struct ProofFixture {
    root: PathBuf,
    specification: PathBuf,
    main_module: String,
    definition_module: String,
    compiled: Option<PathBuf>,
}

impl ProofFixture {
    fn new(
        definition: (&str, &str),
        specification: (&str, &str),
        main_module: &str,
        definition_module: &str,
    ) -> Self {
        let (root, _) = fixture();
        fs::write(root.join(definition.0), definition.1).unwrap();
        let specification_path = root.join(specification.0);
        fs::write(&specification_path, specification.1).unwrap();
        Self {
            root,
            specification: specification_path,
            main_module: main_module.to_owned(),
            definition_module: definition_module.to_owned(),
            compiled: None,
        }
    }

    /// Compile the specification once; later proofs read the compiled definition.
    fn compiled(mut self) -> Self {
        let compiled = self.root.join("compiled-specification");
        kcompile_for_proving(
            &self.specification,
            &self.main_module,
            &self.definition_module,
            &compiled,
        );
        self.compiled = Some(compiled);
        self
    }

    /// `kprove` of this specification, from its compilation when there is one and otherwise from
    /// source, without the claim selection and proof options.
    fn kprove(&self) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.arg("kprove");
        match &self.compiled {
            Some(compiled) => command.arg("--compiled-definition").arg(compiled),
            None => command.arg(&self.specification),
        };
        command.args([
            "--main-module",
            &self.main_module,
            "--definition-module",
            &self.definition_module,
        ]);
        command
    }

    fn claim_leaves(
        &self,
        claims: &[&str],
        extra_args: &[&str],
    ) -> Vec<(String, String, Vec<String>)> {
        claims
            .iter()
            .map(|claim| {
                let output = self
                    .kprove()
                    .args(["--depth", "10", "--claim", claim])
                    .args(extra_args)
                    .output()
                    .unwrap();
                let stdout = String::from_utf8(output.stdout).unwrap();
                let stderr = String::from_utf8_lossy(&output.stderr);
                let leaves = stdout
                    .lines()
                    .filter_map(|line| line.strip_prefix("  "))
                    .filter_map(|line| line.split_once(" at depth "))
                    .map(|(outcome, _)| outcome.to_owned())
                    .collect::<Vec<_>>();
                let prefix = format!("claim {claim}: ");
                let verdict = stdout
                    .lines()
                    .find_map(|line| line.strip_prefix(&prefix))
                    .and_then(|rest| rest.split_whitespace().next())
                    .map(str::to_owned)
                    .unwrap_or_else(|| {
                        eprintln!("{claim}: {}", stderr.trim());
                        "error".to_owned()
                    });
                assert_eq!(
                    output.status.success(),
                    verdict == "proven",
                    "{claim}: {stdout}\n{stderr}"
                );
                ((*claim).to_owned(), verdict, leaves)
            })
            .collect()
    }
}

impl Drop for ProofFixture {
    fn drop(&mut self) {
        // A failing test keeps its sources for inspection, as the tests that remove their
        // fixture after the last assertion do.
        if !std::thread::panicking() {
            fs::remove_dir_all(&self.root).unwrap();
        }
    }
}

/// `kcompile --for-proving` of `specification` into `output`, asserting that it succeeds. A test
/// that proves several claims of one specification compiles it once with this and passes
/// `output` to `kprove --compiled-definition`.
fn kcompile_for_proving(
    specification: &Path,
    main_module: &str,
    definition_module: &str,
    output: &Path,
) -> Output {
    let compiled = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("kcompile")
        .arg(specification)
        .args([
            "--main-module",
            main_module,
            "--definition-module",
            definition_module,
            "--for-proving",
            "--output-directory",
        ])
        .arg(output)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    compiled
}

/// domains.md makes a map concatenation undefined exactly when its operands share a key (and a
/// set concatenation when they share an element). A configuration map or set of pairwise
/// distinct literal keys is therefore defined, and so is the initializer that builds it
/// (`issue-946`); a repeated key, a key that differs only in spelling (`1`, `+1`), keys of
/// different sorts, or a key computed by a function leaves the initializer without the claim.
#[test]
fn kcompile_claims_initializers_of_disjoint_literal_collections_total() {
    for (content, total) in [
        (
            "<env> 1 |-> ListItem(2) ListItem(3) 5 |-> ListItem(6) 8 |-> .List </env>",
            true,
        ),
        ("<env> 1 |-> 2 1 |-> 3 </env>", false),
        ("<env> 1 |-> 2 +1 |-> 3 </env>", false),
        (r#"<env> 1 |-> 2 "1" |-> 3 </env>"#, false),
        ("<env> f(1) |-> 2 5 |-> 3 </env>", false),
        (
            r#"<env> SetItem(true) SetItem(false) SetItem("a") </env>"#,
            false,
        ),
        (r#"<env> SetItem("a") SetItem("b") </env>"#, true),
        ("<env> SetItem(2) SetItem(2) </env>", false),
    ] {
        let (root, definition) = fixture();
        fs::write(
            &definition,
            format!(
                "module MAIN\n  imports INT\n  imports STRING\n  imports MAP\n  imports SET\n  imports LIST\n  syntax Int ::= f(Int) [function, symbol(f)]\n  syntax KItem ::= \"start\"\n  configuration <k> start </k> {content}\nendmodule\n"
            ),
        )
        .unwrap();
        let compiled = root.join("compiled");
        kcompile_for_krun(&definition, &["--main-module", "MAIN"], &compiled);
        let kore = fs::read_to_string(compiled.join("definition.kore")).unwrap();
        for initializer in ["LblinitEnvCell", "LblinitGeneratedTopCell"] {
            let declaration = kore
                .split("\n  symbol ")
                .find(|declaration| declaration.starts_with(&format!("{initializer}{{}}()")))
                .unwrap_or_else(|| panic!("{content}: no {initializer} declaration"));
            // The declaration ends with its attribute list, which may span several lines.
            let open = declaration.find('[').expect("attribute list");
            let mut depth = 0;
            let end = declaration[open..]
                .char_indices()
                .find_map(|(index, character)| {
                    match character {
                        '[' => depth += 1,
                        ']' => depth -= 1,
                        _ => {}
                    }
                    (depth == 0).then_some(open + index + 1)
                })
                .expect("closed attribute list");
            let declaration = &declaration[..end];
            assert_eq!(
                declaration.contains("total{}()"),
                total,
                "{content}: {initializer} {declaration}"
            );
        }
        fs::remove_dir_all(root).unwrap();
    }
}

/// A token production conflicts with `Int`'s identical lexeme only in a view that contains
/// both: the upstream `checks/invalidPrec.k` module, which imports nothing, compiles, and the
/// same production beside `imports INT-SYNTAX` is rejected (docs/compatibility.md, "Grammar
/// scope of token precedence").
#[test]
fn kcompile_judges_token_precedence_in_the_module_s_own_view() {
    for (imports, accepted) in [("", true), ("  imports INT-SYNTAX\n", false)] {
        let (root, definition) = fixture();
        fs::write(
            &definition,
            format!(
                "module INVALIDPREC\n{imports}  syntax Foo ::= r\"[0-9]+\" [token]\nendmodule\n"
            ),
        )
        .unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .arg("kcompile")
            .arg(&definition)
            .args(["--main-module", "INVALIDPREC", "--output-directory"])
            .arg(root.join("compiled"))
            .stdin(Stdio::null())
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.success(), accepted, "{imports:?}: {stderr}");
        assert_eq!(
            stderr.contains("Inconsistent token precedence detected."),
            !accepted,
            "{imports:?}: {stderr}"
        );
        fs::remove_dir_all(root).unwrap();
    }
}

/// `kcompile` of `source` with the compile options `options` (modules, include directories) into
/// `output`, asserting that it succeeds. A test that runs one definition several times compiles it
/// once with this and passes `output` to `krun --definition`.
fn kcompile_for_krun(source: &Path, options: &[&str], output: &Path) -> Output {
    let compiled = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("kcompile")
        .arg(source)
        .args(options)
        .arg("--output-directory")
        .arg(output)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    compiled
}

fn verdicts_of(leaves: &[(String, String, Vec<String>)]) -> Vec<(String, String)> {
    leaves
        .iter()
        .map(|(claim, verdict, _)| (claim.clone(), verdict.clone()))
        .collect()
}

/// A claim that ends `disproved` at exactly one leaf, a certified stuck leaf.
fn refuted_leaf(claim: &str) -> (String, String, Vec<String>) {
    (
        claim.to_owned(),
        "disproved".to_owned(),
        vec!["stuck (certified)".to_owned()],
    )
}

/// A claim that ends `failed` at exactly one leaf, a stuck leaf that is not certified.
fn failed_stuck_leaf(claim: &str) -> (String, String, Vec<String>) {
    (
        claim.to_owned(),
        "failed".to_owned(),
        vec!["stuck".to_owned()],
    )
}

fn expected_verdicts(expected: &[(&str, &str)]) -> Vec<(String, String)> {
    expected
        .iter()
        .map(|(claim, verdict)| ((*claim).to_owned(), (*verdict).to_owned()))
        .collect()
}

const EXIST_PROBE: &str = r#"
module EXIST-PROBE
  imports INT
  syntax State ::= "start" | st(Int, Int) | "done"
  configuration <k> $PGM:State </k>
  rule <k> start => st(!N:Int, 7) </k>
endmodule
"#;

/// A claim that does not name the generated counter says nothing about it, so a path that
/// instantiates a `!` variable (and so advances the counter) can prove it.
#[test]
fn kprove_claims_leave_the_generated_counter_to_the_path() {
    let specification = r#"
requires "exist-probe.k"

module EXIST-SPEC
  imports EXIST-PROBE

  claim <k> start => st(?B:Int, ?A:Int) </k> ensures ?A ==Int 7 [label(ab)]
  claim <k> start => st(?Z:Int, ?A:Int) </k> ensures ?A ==Int 7 [label(za)]
  claim <k> start => st(?B:Int, ?A:Int) </k> ensures ?A ==Int 8 [label(ab-false)]
endmodule
"#;
    assert_eq!(
        kprove_claim_verdicts(
            ("exist-probe.k", EXIST_PROBE),
            ("exist-spec.k", specification),
            "EXIST-SPEC",
            "EXIST-PROBE",
            &["ab", "za", "ab-false"],
        ),
        expected_verdicts(&[("ab", "proven"), ("za", "proven"), ("ab-false", "failed")]),
    );
}

/// A claim that names the generated counter states what it says about it.
#[test]
fn kprove_claims_naming_the_generated_counter_keep_their_statement() {
    let specification = r#"
requires "exist-probe.k"

module EXIST-SPEC2
  imports EXIST-PROBE

  claim <k> start => st(?B:Int, ?A:Int) </k> <generatedCounter> C:Int => C </generatedCounter> ensures ?A ==Int 7 [label(same-counter)]
  claim <k> start => st(?B:Int, ?A:Int) </k> <generatedCounter> C:Int => ?C2:Int </generatedCounter> ensures ?A ==Int 7 [label(exists-counter)]
  claim <k> start => st(?B:Int, ?A:Int) </k> <generatedCounter> C:Int => C +Int 1 </generatedCounter> ensures ?A ==Int 7 [label(incremented-counter)]
  claim <k> start => st(?B:Int, ?A:Int) </k> <generatedCounter> C:Int => C +Int 2 </generatedCounter> ensures ?A ==Int 7 [label(wrong-counter)]
endmodule
"#;
    assert_eq!(
        kprove_claim_verdicts(
            ("exist-probe.k", EXIST_PROBE),
            ("exist-spec2.k", specification),
            "EXIST-SPEC2",
            "EXIST-PROBE",
            &[
                "same-counter",
                "exists-counter",
                "incremented-counter",
                "wrong-counter"
            ],
        ),
        expected_verdicts(&[
            ("same-counter", "failed"),
            ("exists-counter", "proven"),
            ("incremented-counter", "proven"),
            ("wrong-counter", "failed"),
        ]),
    );
}

/// Both ways of writing a claim across a rule that allocates a fresh value prove: naming the
/// counter's advance, or leaving the counter out.
#[test]
fn kprove_fresh_value_claims_prove_with_and_without_the_counter() {
    let definition = r#"
module TEST
  imports INT
  syntax Pgm ::= "quux"
  configuration <k> $PGM:Pgm </k> <c1> .K </c1> <c2> .K </c2>
  rule <k> quux => .K </k> <c1> .K => !C:Int </c1> <c2> .K => !C:Int </c2>
endmodule
"#;
    let specification = r#"
requires "test.k"

module FRESH-SPEC
  imports TEST

  claim <k> quux => .K </k> <c1> .K => ?C </c1> <c2> .K => ?C </c2>
    <generatedCounter> GC => GC +Int 1 </generatedCounter> [label(explicit)]
  claim <k> quux => .K </k> <c1> .K => ?C </c1> <c2> .K => ?C </c2> [label(implicit)]
endmodule
"#;
    assert_eq!(
        kprove_claim_verdicts(
            ("test.k", definition),
            ("fresh-spec.k", specification),
            "FRESH-SPEC",
            "TEST",
            &["explicit", "implicit"],
        ),
        expected_verdicts(&[("explicit", "proven"), ("implicit", "proven")]),
    );
}

const CELL_PROBE: &str = r#"
module CELL-PROBE
  imports INT
  syntax State ::= "start" | "middle" | "done"
  configuration <k> $PGM:State </k> <n> 0 </n>
  rule <k> start => middle </k> <n> X => X +Int 1 </n>
endmodule
"#;

/// A universal variable of a claim, including the frame variable of a cell the claim leaves out,
/// denotes the same value in the reached state as in the initial one.
#[test]
fn kprove_universal_claim_variables_keep_their_initial_value() {
    let specification = r#"
requires "cell-probe.k"

module CELL-SPEC
  imports CELL-PROBE

  claim <k> start => middle </k> [label(unmentioned)]
  claim <k> start => middle </k> <n> X => X +Int 1 </n> [label(incremented)]
  claim <k> start => middle </k> <n> X => X </n> [label(unchanged)]
  claim <k> start => middle </k> <n> 3 </n> [label(constant)]
  claim <k> start => done </k> [label(unreachable)]
endmodule
"#;
    let leaves = kprove_claim_leaves(
        ("cell-probe.k", CELL_PROBE),
        ("cell-spec.k", specification),
        "CELL-SPEC",
        "CELL-PROBE",
        &[
            "unmentioned",
            "incremented",
            "unchanged",
            "constant",
            "unreachable",
        ],
        &[],
    );
    // The increment of an unmentioned cell falsifies the claim. The frame equation holds on part
    // of the reached state as far as the solver can tell (the two `<n>` values are opaque to it),
    // so the part where it fails continues and ends as a stuck leaf. That part is non-empty only
    // modulo the abstraction of the two cells, so the leaf is not certified: the claim fails.
    assert_eq!(leaves[0], failed_stuck_leaf("unmentioned"), "{leaves:?}");
    assert_eq!(
        verdicts_of(&leaves[1..]),
        expected_verdicts(&[
            ("incremented", "proven"),
            // The leaves of `unchanged` and `unreachable` hold `X +Int 1`, an unevaluated
            // function application; `constant`'s holds the value `4` of the matched `X = 3`.
            ("unchanged", "failed"),
            ("constant", "disproved"),
            ("unreachable", "failed"),
        ]),
    );
}

const CELL_PROBE2: &str = r#"
module CELL-PROBE2
  imports INT
  syntax State ::= "start" | "middle"
  configuration <k> $PGM:State </k> <n> 0 </n>
  rule <k> start => middle </k> <n> _ => 5 </n>
endmodule
"#;

const CELL_SPEC2: &str = r#"
requires "cell-probe2.k"

module CELL-SPEC2
  imports CELL-PROBE2

  claim <k> start => middle </k> <n> X => X </n> [label(free-unchanged)]
  claim <k> start => middle </k> <n> X => X </n> requires X ==Int 0 [label(constrained-unchanged)]
  claim <k> start => middle </k> <n> X => 5 </n> requires X ==Int 0 [label(constrained-set)]
  claim <k> start => middle </k> <n> 0 => 0 </n> [label(concrete-unchanged)]
endmodule
"#;

/// A universal claim variable denotes its initial value in the reached state, so the value the path
/// writes into its cell falsifies the claim whether or not the precondition constrains the variable.
#[test]
fn kprove_constrained_universal_claim_variables_are_checked() {
    let leaves = kprove_claim_leaves(
        ("cell-probe2.k", CELL_PROBE2),
        ("cell-spec2.k", CELL_SPEC2),
        "CELL-SPEC2",
        "CELL-PROBE2",
        &[
            "free-unchanged",
            "constrained-unchanged",
            "constrained-set",
            "concrete-unchanged",
        ],
        &[],
    );
    // `X = 5` holds on part of the reached state for an unconstrained `X`: that part is in the
    // destination, and the part where `X` differs from 5 has no successor. Its constraint
    // `¬(X = 5)` is over the integers only, so the leaf is a certified refutation.
    assert_eq!(leaves[0], refuted_leaf("free-unchanged"), "{leaves:?}");
    assert_eq!(
        verdicts_of(&leaves[1..]),
        expected_verdicts(&[
            ("constrained-unchanged", "disproved"),
            ("constrained-set", "proven"),
            ("concrete-unchanged", "disproved"),
        ]),
    );
}

/// A rule that only reads a cell the claim leaves out keeps the claim's frame; a rule that writes
/// one does not.
#[test]
fn kprove_unmentioned_cells_read_by_the_path_keep_the_frame() {
    let definition = r#"
module CELL-PROBE3
  imports INT
  syntax State ::= "start" | "middle" | "done"
  configuration <k> $PGM:State </k> <n> 0 </n> <m> 0 </m>
  rule <k> start => middle </k> <n> _ </n>
  rule <k> middle => done </k> <n> X </n> <m> _ => X </m>
endmodule
"#;
    let specification = r#"
requires "cell-probe3.k"

module CELL-SPEC3
  imports CELL-PROBE3

  claim <k> start => middle </k> [label(read-only)]
  claim <k> middle => done </k> <m> _ => ?M </m> [label(copied-exists)]
  claim <k> middle => done </k> <n> X </n> <m> _ => X </m> [label(copied-universal)]
  claim <k> middle => done </k> [label(copied-unmentioned)]
endmodule
"#;
    let leaves = kprove_claim_leaves(
        ("cell-probe3.k", definition),
        ("cell-spec3.k", specification),
        "CELL-SPEC3",
        "CELL-PROBE3",
        &[
            "read-only",
            "copied-exists",
            "copied-universal",
            "copied-unmentioned",
        ],
        &[],
    );
    assert_eq!(
        verdicts_of(&leaves[..3]),
        expected_verdicts(&[
            ("read-only", "proven"),
            ("copied-exists", "proven"),
            ("copied-universal", "proven"),
        ]),
    );
    // Copying `<n>` into `<m>` changes the unmentioned `<m>` wherever the two differ; that part
    // of the reached state has no successor, a stuck leaf. It is non-empty only modulo the
    // abstraction of the cells the frame equation compares, so the claim fails.
    assert_eq!(
        leaves[3],
        failed_stuck_leaf("copied-unmentioned"),
        "{leaves:?}"
    );
}

/// A destination that holds on part of a state closes that part; only the rest continues. The
/// covered part of `covered-then-stuck` (`X = 0`, already in the destination) would reach a state
/// outside it if it were rewritten further.
#[test]
fn kprove_a_contingent_destination_closes_the_covered_part() {
    let definition = r#"
module SPLIT-PROBE
  imports INT
  imports BOOL
  syntax State ::= s(Int, Int)
  configuration <k> $PGM:State </k>
  rule <k> s(0, X) => s(1, 5) </k> requires X =/=Int 0
  rule <k> s(0, X) => s(2, 5) </k> requires X ==Int 0
endmodule
"#;
    let specification = r#"
requires "split-probe.k"

module SPLIT-SPEC
  imports SPLIT-PROBE

  claim <k> s(0, _X) => s(?P:Int, ?V:Int) </k> ensures ?P *Int ?P ==Int ?P andBool (1 -Int ?P) *Int ?V ==Int 0 [label(covered-then-stuck)]
  claim <k> s(0, _X) => s(?P:Int, ?V:Int) </k> ensures ?P *Int ?P ==Int ?P andBool (1 -Int ?P) *Int (?V -Int 7) ==Int 0 [label(contingent-false)]
endmodule
"#;
    let fixture = ProofFixture::new(
        ("split-probe.k", definition),
        ("split-spec.k", specification),
        "SPLIT-SPEC",
        "SPLIT-PROBE",
    )
    .compiled();
    for extra in [&[][..], &["--disable-stuck-check"][..]] {
        let leaves = fixture.claim_leaves(&["covered-then-stuck", "contingent-false"], extra);
        assert_eq!(
            verdicts_of(&leaves),
            expected_verdicts(&[
                ("covered-then-stuck", "proven"),
                ("contingent-false", "disproved"),
            ]),
            "{extra:?}: {leaves:?}"
        );
    }
}

/// A destination reached through a match remainder (`st(X)` against `st(0)`) is classified like
/// any other obligation: the part where `X = 0` is at the destination and closes, and the rest
/// can still rewrite, so it continues whatever the stuck check says. `remainder-rewritable` is
/// true (the rest takes the rule to `st(0)`). In `remainder-false` the rest reaches `st(0)`,
/// which is outside the destination `st(1)` and has no successor: a certified stuck leaf
/// (disproved).
#[test]
fn kprove_a_remainder_destination_continues_the_uncovered_part() {
    let definition = r#"
module REMAINDER-PROBE
  imports INT
  imports BOOL
  syntax State ::= st(Int)
  configuration <k> $PGM:State </k>
  rule <k> st(X) => st(0) </k> requires X =/=Int 0
endmodule
"#;
    let specification = r#"
requires "remainder-probe.k"

module REMAINDER-SPEC
  imports REMAINDER-PROBE

  claim <k> st(_X) => st(0) </k> [label(remainder-rewritable)]
  claim <k> st(_X) => st(1) </k> [label(remainder-false)]
endmodule
"#;
    let fixture = ProofFixture::new(
        ("remainder-probe.k", definition),
        ("remainder-spec.k", specification),
        "REMAINDER-SPEC",
        "REMAINDER-PROBE",
    )
    .compiled();
    for extra in [&[][..], &["--disable-stuck-check"][..]] {
        let leaves = fixture.claim_leaves(&["remainder-rewritable", "remainder-false"], extra);
        assert_eq!(
            leaves[0],
            (
                "remainder-rewritable".to_owned(),
                "proven".to_owned(),
                Vec::new()
            ),
            "{extra:?}: {leaves:?}"
        );
        let (claim, verdict, outcomes) = &leaves[1];
        assert_eq!(
            (claim.as_str(), verdict.as_str()),
            ("remainder-false", "disproved"),
            "{extra:?}: {leaves:?}"
        );
        assert!(
            !outcomes.is_empty()
                && outcomes
                    .iter()
                    .all(|outcome| outcome == "stuck (certified)"),
            "{extra:?}: {leaves:?}"
        );
    }
}

/// A remainder obligation (`0 = X` from `st(X)` against `st(0)`) that the simplifier refutes,
/// because together with the destination constraint it is false (`0 = X` with `X >Int 5`, or
/// `false`), is graded exactly as one the solver refutes: the stuck check stops the state at
/// depth 0, and without it the rule rewrites the state onward. `solver-refuted` and `simplifier-refuted` are
/// true; `solver-refuted-false` and `simplifier-refuted-false` are false (their destination
/// constraint fails on every state). Their reached `st(0)` refutes the obligation and has no
/// successor, so it is a stuck leaf in both modes.
#[test]
fn kprove_a_refuted_remainder_is_graded_alike_by_simplifier_and_solver() {
    let definition = r#"
module REMAINDER-PROBE
  imports INT
  imports BOOL
  syntax State ::= st(Int)
  configuration <k> $PGM:State </k>
  rule <k> st(X) => st(0) </k> requires X =/=Int 0
endmodule
"#;
    let specification = r#"
requires "remainder-probe.k"

module REMAINDER-SPEC
  imports REMAINDER-PROBE

  claim <k> st(X) => st(0) </k> requires X >Int 5 [label(solver-refuted)]
  claim <k> st(X) => st(0) </k> requires X >Int 5 ensures X >Int 5 [label(simplifier-refuted)]
  claim <k> st(X) => st(0) </k> requires X >Int 5 ensures X <Int 5 [label(solver-refuted-false)]
  claim <k> st(X) => st(0) </k> requires X >Int 5 ensures false [label(simplifier-refuted-false)]
endmodule
"#;
    let claims = [
        "solver-refuted",
        "simplifier-refuted",
        "solver-refuted-false",
        "simplifier-refuted-false",
    ];
    // The stuck check stops `st(X)` with `X >Int 5`, which still rewrites: a failed claim, not a
    // refutation. The reached `st(0)` of the false claims has no successor: a certified one.
    let stopped = || ("failed".to_owned(), vec!["stuck".to_owned()]);
    let refuted = || ("disproved".to_owned(), vec!["stuck (certified)".to_owned()]);
    let fixture = ProofFixture::new(
        ("remainder-probe.k", definition),
        ("remainder-spec.k", specification),
        "REMAINDER-SPEC",
        "REMAINDER-PROBE",
    )
    .compiled();
    for (extra, expected) in [
        (&[][..], [stopped(), stopped(), stopped(), stopped()]),
        (
            &["--disable-stuck-check"][..],
            [
                ("proven".to_owned(), Vec::new()),
                ("proven".to_owned(), Vec::new()),
                refuted(),
                refuted(),
            ],
        ),
    ] {
        let leaves = fixture.claim_leaves(&claims, extra);
        let expected = claims
            .iter()
            .zip(expected)
            .map(|(claim, (verdict, outcomes))| ((*claim).to_owned(), verdict, outcomes))
            .collect::<Vec<_>>();
        assert_eq!(leaves, expected, "{extra:?}");
    }
}

#[test]
fn kprove_reports_an_inconsistent_external_prelude_when_a_claim_queries_smt() {
    let (root, _) = fixture();
    fs::write(
        root.join("probe.k"),
        r#"
module PROBE
  imports INT
  imports BOOL
  syntax State ::= st(Int)
  configuration <k> $PGM:State </k>
  rule <k> st(X) => st(0) </k> requires X =/=Int 0
endmodule
"#,
    )
    .unwrap();
    let specification = root.join("probe-spec.k");
    fs::write(
        &specification,
        r#"
requires "probe.k"
module PROBE-SPEC
  imports PROBE
  claim <k> st(X) => st(0) </k> requires X >Int 5 [label(solver-refuted)]
  claim <k> st(X) => st(X) </k> [label(trusted), trusted]
endmodule
"#,
    )
    .unwrap();
    let prelude = root.join("inconsistent.smt2");
    fs::write(&prelude, "(assert false)\n").unwrap();
    // Both claims are proven by their own process on one compiled specification.
    let compiled = root.join("compiled");
    kcompile_for_proving(&specification, "PROBE-SPEC", "PROBE", &compiled);
    let no_query = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kprove", "--compiled-definition"])
        .arg(&compiled)
        .args([
            "--main-module",
            "PROBE-SPEC",
            "--definition-module",
            "PROBE",
            "--claim",
            "trusted",
            "--smt-prelude",
            prelude.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(no_query.status.success(), "{no_query:?}");
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kprove", "--compiled-definition"])
        .arg(&compiled)
        .args([
            "--main-module",
            "PROBE-SPEC",
            "--definition-module",
            "PROBE",
            "--claim",
            "solver-refuted",
            "--smt-prelude",
            prelude.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(!output.status.success(), "{output:?}");
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("the definitions sent to the solver are inconsistent"),
        "{output:?}"
    );
    assert!(
        !String::from_utf8_lossy(&output.stdout).contains("claim solver-refuted:"),
        "a prelude failure must not become a proof verdict: {output:?}"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_stops_an_unbounded_proof_after_a_prelude_failure() {
    let (root, _) = fixture();
    fs::write(
        root.join("probe.k"),
        r#"
module PROBE
  imports INT
  imports BOOL
  syntax State ::= st(Int)
  configuration <k> $PGM:State </k>
  rule <k> st(X) => st(X +Int 1) </k>
endmodule
"#,
    )
    .unwrap();
    let specification = root.join("probe-spec.k");
    fs::write(
        &specification,
        r#"
requires "probe.k"
module PROBE-SPEC
  imports PROBE
  claim <k> st(X) => st(0) </k> requires X >Int 5 [label(probe)]
endmodule
"#,
    )
    .unwrap();
    let prelude = root.join("inconsistent.smt2");
    fs::write(&prelude, "(assert false)\n").unwrap();
    let compiled = root.join("compiled");
    let preparation = watchdog::output(watchdog::Request::Compile {
        source: &specification,
        main_module: "PROBE-SPEC",
        output: &compiled,
        kind: watchdog::Compilation::Proof {
            definition_module: "PROBE",
        },
    });
    assert!(
        preparation.status.success(),
        "proof preparation failed: {}",
        String::from_utf8_lossy(&preparation.stderr)
    );
    for (context, input) in [
        ("compiled kprove", watchdog::Input::Compiled(&compiled)),
        ("source kprove", watchdog::Input::Source(&specification)),
    ] {
        let output = watchdog::output(watchdog::Request::Kprove {
            input,
            main_module: "PROBE-SPEC",
            definition_module: "PROBE",
            claim: "probe",
            smt_prelude: &prelude,
        });
        assert_eq!(output.status.code(), Some(1), "{context}: {output:?}");
        assert_eq!(output.stdout, b"", "{context}: {output:?}");
        assert_eq!(
            output.stderr, b"error: the definitions sent to the solver are inconsistent\n",
            "{context}: {output:?}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

/// Where `X =/=Int Y`, `q(X, Y)` rewrites to `q(Y, Y)`, which is stuck. The only witness for `?Z`
/// there is `Y`, so `?Z ==Int X` is refuted. The first state is split on the remainder of the
/// destination match (`X = Y` is covered). The rewritten part then refutes its obligation, and a
/// refuted obligation covers nothing: the whole of `q(Y, Y)` under `X =/=Int Y` is a stuck leaf.
/// That leaf is not an empty state, so accepting vacuous leaves cannot prove the claim.
#[test]
fn kprove_a_refuted_obligation_after_a_remainder_split_stays_stuck() {
    let definition = r#"
module SPLIT-PROBE
  imports INT
  imports BOOL
  syntax State ::= q(Int, Int)
  configuration <k> $PGM:State </k>
  rule <k> q(X, Y) => q(Y, Y) </k> requires X =/=Int Y
endmodule
"#;
    let specification = r#"
requires "split-probe.k"

module SPLIT-SPEC
  imports SPLIT-PROBE

  claim <k> q(X, Y) => q(?Z, ?Z) </k> ensures ?Z ==Int X [label(q-ens-false)]
endmodule
"#;
    let fixture = ProofFixture::new(
        ("split-probe.k", definition),
        ("split-spec.k", specification),
        "SPLIT-SPEC",
        "SPLIT-PROBE",
    )
    .compiled();
    for extra in [&[][..], &["--allow-vacuous"][..]] {
        let leaves = fixture.claim_leaves(&["q-ens-false"], extra);
        assert_eq!(leaves, [refuted_leaf("q-ens-false")], "{extra:?}");
    }
}

/// A claim universal that the path overwrote still names its initial value, so the part of the
/// reached state where the destination fails on it is a certified stuck leaf (disproved),
/// whether or not vacuous leaves are accepted.
#[test]
fn kprove_an_overwritten_universal_keeps_the_uncovered_part() {
    let specification = r#"
requires "cell-probe2.k"

module REM-SPEC
  imports CELL-PROBE2

  claim <k> start => middle </k> <n> X => X +Int 1 </n> [label(free-remainder)]
endmodule
"#;
    let fixture = ProofFixture::new(
        ("cell-probe2.k", CELL_PROBE2),
        ("rem-spec.k", specification),
        "REM-SPEC",
        "CELL-PROBE2",
    )
    .compiled();
    for extra in [&[][..], &["--allow-vacuous"][..]] {
        let leaves = fixture.claim_leaves(&["free-remainder"], extra);
        assert_eq!(leaves, [refuted_leaf("free-remainder")], "{extra:?}");
    }
}

/// `disproved` is reserved for a certified refutation. The ground all-path claim `start => stuck`
/// of the reference proof corpus reaches `done`, which has no successor, is outside the
/// destination, and has no constraint: its leaf is certified. A claim whose leaf is reached
/// through a circularity is not: the claim step summarises paths it does not follow, so the
/// leaf only fails the claim. Without the circularity the same leaf is certified.
#[test]
fn kprove_certifies_only_a_refutation_the_search_followed_step_by_step() {
    let definition = fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/mini-proof.k"),
    )
    .unwrap();
    let specification = r#"
requires "mini-proof.k"

module MINI-PROOF-SPEC
  imports MINI-PROOF

  claim <k> start => stuck </k> [label(claim-refuted)]
endmodule
"#;
    let leaves = kprove_claim_leaves(
        ("mini-proof.k", &definition),
        ("mini-proof-spec.k", specification),
        "MINI-PROOF-SPEC",
        "MINI-PROOF",
        &["claim-refuted"],
        &[],
    );
    assert_eq!(leaves, [refuted_leaf("claim-refuted")]);

    let definition = r#"
module CIRCULARITY-PROBE
  imports INT
  syntax State ::= a(Int) | b(Int) | c(Int) | d(Int)
  configuration <k> $PGM:State </k>
  rule <k> a(X) => b(X) </k>
  rule <k> b(X) => c(X) </k>
endmodule
"#;
    let specification = r#"
requires "circularity-probe.k"

module CIRCULARITY-SPEC
  imports CIRCULARITY-PROBE

  claim <k> b(X) => c(X) </k> [label(b-to-c), trusted]
  claim <k> a(X) => d(X) </k> [label(through-circularity)]
endmodule
"#;
    let leaves = kprove_claim_leaves(
        ("circularity-probe.k", definition),
        ("circularity-spec.k", specification),
        "CIRCULARITY-SPEC",
        "CIRCULARITY-PROBE",
        &["through-circularity"],
        // A claim selection keeps only the selected claims as circularities.
        &["--claim", "b-to-c"],
    );
    assert_eq!(leaves, [failed_stuck_leaf("through-circularity")]);

    let specification = r#"
requires "circularity-probe.k"

module DIRECT-SPEC
  imports CIRCULARITY-PROBE

  claim <k> a(X) => d(X) </k> [label(direct)]
endmodule
"#;
    let leaves = kprove_claim_leaves(
        ("circularity-probe.k", definition),
        ("direct-spec.k", specification),
        "DIRECT-SPEC",
        "CIRCULARITY-PROBE",
        &["direct"],
        &[],
    );
    assert_eq!(leaves, [refuted_leaf("direct")]);
}

/// A one-path claim is refuted by a leaf only when the trace kept every successor of every
/// configuration it followed; then that path is the only one. `start(I)` with `I <=Int 0` has the
/// one successor `bad`, since the two rules' conditions are disjoint, and `bad` has none: the
/// one-path claim `start(I) => good` is false there. When the rule tried first overlaps a later
/// one, the sequential step drops the later successor where both apply, and a rule whose
/// right-hand side chooses a value stands for many successors; the leaves those steps reach
/// only fail true claims.
#[test]
fn kprove_certifies_a_one_path_refutation_only_on_a_trace_that_kept_every_successor() {
    let definition = r#"
module ONE-PATH-PROBE
  imports INT
  syntax Pgm ::= start(Int) | "good" | "bad" | "pick" | val(Int)
  configuration <k> $PGM:Pgm </k>
  rule <k> start(I) => good </k> requires I >Int 0
  rule <k> start(I) => bad </k> requires I <=Int 0
  rule <k> pick => val(?X:Int) </k>
endmodule
"#;
    let specification = r#"
requires "one-path-probe.k"

module ONE-PATH-SPEC
  imports ONE-PATH-PROBE

  claim <k> start(I) => good </k> [label(disjoint), one-path]
  claim <k> pick => val(5) </k> [label(chosen-value), one-path]
endmodule
"#;
    let leaves = kprove_claim_leaves(
        ("one-path-probe.k", definition),
        ("one-path-spec.k", specification),
        "ONE-PATH-SPEC",
        "ONE-PATH-PROBE",
        &["disjoint", "chosen-value"],
        &[],
    );
    assert_eq!(
        verdicts_of(&leaves),
        expected_verdicts(&[("disjoint", "disproved"), ("chosen-value", "failed")]),
        "{leaves:?}"
    );
    assert!(
        leaves[0].2.iter().any(|leaf| leaf == "stuck (certified)"),
        "{leaves:?}"
    );

    // `bad` is tried first and covers `I ==Int 3`, where `good` also applies: the claim holds
    // there through `good`, which the sequential step drops.
    let definition = r#"
module OVERLAP-PROBE
  imports INT
  syntax Pgm ::= start(Int) | "good" | "bad"
  configuration <k> $PGM:Pgm </k>
  rule <k> start(I) => bad </k> requires I <Int 5
  rule <k> start(I) => good </k> requires I >Int 0
endmodule
"#;
    let specification = r#"
requires "overlap-probe.k"

module OVERLAP-SPEC
  imports OVERLAP-PROBE

  claim <k> start(3) => good </k> [label(overlap), one-path]
endmodule
"#;
    let leaves = kprove_claim_leaves(
        ("overlap-probe.k", definition),
        ("overlap-spec.k", specification),
        "OVERLAP-SPEC",
        "OVERLAP-PROBE",
        &["overlap"],
        &[],
    );
    assert_eq!(leaves, [failed_stuck_leaf("overlap")]);
}

/// A leaf certifies a refutation through one of its configurations. A claim written with `...`
/// leaves its frame variable in the `<k>` cell once its code has run, so the leaf still rewrites
/// when the frame holds more code; its configuration with the empty frame `.K` has no successor
/// and the counter `1` fails `?M >Int 1`, which refutes the claim. When `.K` itself rewrites, that
/// configuration certifies nothing.
#[test]
fn kprove_certifies_a_leaf_through_its_empty_computation_instance() {
    let definition = r#"
module FRAME-PROBE
  imports INT
  syntax Pgm ::= count(Int)
  configuration <k> $PGM:Pgm </k> <n> 0 </n>
  rule <k> count(I) => count(I -Int 1) ... </k> <n> N => N +Int 1 </n> requires I >Int 0
  rule <k> count(0) => .K ... </k>
endmodule
"#;
    let specification = r#"
requires "frame-probe.k"

module FRAME-SPEC
  imports FRAME-PROBE

  claim <k> count(1) => .K ... </k> <n> 0 => ?M:Int </n> ensures ?M >Int 0 [label(frame-proven)]
  claim <k> count(1) => .K ... </k> <n> 0 => ?M:Int </n> ensures ?M >Int 1 [label(frame-refuted)]
endmodule
"#;
    let leaves = kprove_claim_leaves(
        ("frame-probe.k", definition),
        ("frame-spec.k", specification),
        "FRAME-SPEC",
        "FRAME-PROBE",
        &["frame-proven", "frame-refuted"],
        &[],
    );
    assert_eq!(
        verdicts_of(&leaves),
        expected_verdicts(&[("frame-proven", "proven"), ("frame-refuted", "disproved")]),
        "{leaves:?}"
    );
    assert_eq!(leaves[1], refuted_leaf("frame-refuted"));

    let definition = r#"
module RESTART-PROBE
  imports INT
  syntax Pgm ::= count(Int) | "halt"
  configuration <k> $PGM:Pgm </k> <n> 0 </n>
  rule <k> count(I) => count(I -Int 1) ... </k> <n> N => N +Int 1 </n> requires I >Int 0
  rule <k> count(0) => .K ... </k>
  rule <k> .K => halt </k>
endmodule
"#;
    let specification = r#"
requires "restart-probe.k"

module RESTART-SPEC
  imports RESTART-PROBE

  claim <k> count(1) => .K ... </k> <n> 0 => ?M:Int </n> ensures ?M >Int 1 [label(frame-restarts)]
endmodule
"#;
    let leaves = kprove_claim_leaves(
        ("restart-probe.k", definition),
        ("restart-spec.k", specification),
        "RESTART-SPEC",
        "RESTART-PROBE",
        &["frame-restarts"],
        &[],
    );
    assert_eq!(leaves, [failed_stuck_leaf("frame-restarts")]);
}

/// The `[[proof]]` cases of `scripts/reference-differential.toml` whose sources are committed
/// in this repository and that need no `semantics-support`, as
/// `scripts/reference-proof-differential.sh` selects them, by name.
fn local_proof_corpus() -> Vec<(String, toml::Value)> {
    let manifest: toml::Value =
        toml::from_str(include_str!("../../../scripts/reference-differential.toml")).unwrap();
    manifest["proof"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|case| {
            let local = |key: &str| case[key].as_str().unwrap().starts_with("${workspace}/");
            local("source")
                && local("specification")
                && !case["requires"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|requirement| requirement.as_str() == Some("semantics-support"))
        })
        .map(|case| (case["name"].as_str().unwrap().to_owned(), case.clone()))
        .collect()
}

/// The krust half of `scripts/reference-proof-differential.sh` for one local proof case: the
/// case's `claims` are proven together in one `kprove`, which succeeds and reports each of them
/// `proven`; its `failure-claim` alone makes `kprove` fail with the `failure-verdict` (by
/// default `disproved`), and a `failed` verdict must carry a `failure-verdict-reason`. The
/// script also runs the reference prover on the same claims; that comparison stays there.
fn assert_local_proof_case_verdicts(name: &str) {
    let (_, case) = local_proof_corpus()
        .into_iter()
        .find(|(case, _)| case == name)
        .unwrap_or_else(|| panic!("no local proof case {name}"));
    let workspace = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let path = |key: &str| {
        let value = case[key].as_str().unwrap();
        workspace.join(value.strip_prefix("${workspace}/").unwrap())
    };
    let text = |key: &str| case[key].as_str().unwrap().to_owned();
    let specification = path("specification");
    let semantics_directory = path("source").parent().unwrap().to_owned();
    let spec_module = text("spec-module");
    let definition_module = text("definition-module");
    let depth = case["depth"].as_integer().unwrap().to_string();
    let proven_claims = case
        .get("claims")
        .and_then(toml::Value::as_array)
        .map(|claims| {
            claims
                .iter()
                .map(|claim| claim.as_str().unwrap().to_owned())
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let failure_claim = text("failure-claim");
    let failure_verdict = case
        .get("failure-verdict")
        .map_or("disproved", |verdict| verdict.as_str().unwrap());
    match failure_verdict {
        "disproved" => {}
        "failed" => assert!(
            case.get("failure-verdict-reason")
                .and_then(toml::Value::as_str)
                .is_some_and(|reason| !reason.is_empty()),
            "{name}:{failure_claim} expects failed without a failure-verdict-reason"
        ),
        verdict => panic!("unknown failure-verdict {verdict} for {name}:{failure_claim}"),
    }

    // A case with both a proven batch and a failure claim compiles its specification once.
    let (root, _) = fixture();
    let include = semantics_directory.to_str().unwrap();
    let compiled = (!proven_claims.is_empty()).then(|| {
        let compiled = root.join("compiled");
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .arg("kcompile")
            .arg(&specification)
            .args([
                "--main-module",
                &spec_module,
                "--definition-module",
                &definition_module,
                "--for-proving",
                "-I",
                include,
                "--output-directory",
            ])
            .arg(&compiled)
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        compiled
    });
    let kprove = |claims: &[String]| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.arg("kprove");
        match &compiled {
            Some(compiled) => command.arg("--compiled-definition").arg(compiled),
            None => command.arg(&specification).args(["-I", include]),
        };
        command.args([
            "--main-module",
            &spec_module,
            "--definition-module",
            &definition_module,
        ]);
        for claim in claims {
            command.args(["--claim", claim]);
        }
        let output = command
            .args(["--depth", &depth])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        // The script greps standard output and standard error together.
        let log = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        (output.status.success(), log)
    };

    if !proven_claims.is_empty() {
        let (success, log) = kprove(&proven_claims);
        assert!(
            success,
            "{name}: k-rust did not prove every selected claim\n{log}"
        );
        for claim in &proven_claims {
            assert!(
                log.contains(&format!("claim {claim}: proven")),
                "{name}:{claim}: no proven verdict\n{log}"
            );
        }
    }
    let (success, log) = kprove(std::slice::from_ref(&failure_claim));
    assert!(
        !success,
        "{name}: k-rust unexpectedly proved {failure_claim}\n{log}"
    );
    assert!(
        log.contains(&format!("claim {failure_claim}: {failure_verdict} ")),
        "{name}:{failure_claim}: no {failure_verdict} verdict\n{log}"
    );
    fs::remove_dir_all(root).unwrap();
}

/// Each local proof case of the manifest has a test below, so a new case is not silently left
/// to the reference gate alone.
#[test]
fn reference_proof_corpus_local_cases_each_have_a_verdict_test() {
    let names = local_proof_corpus()
        .into_iter()
        .map(|(name, _)| name)
        .collect::<Vec<_>>();
    assert_eq!(
        names,
        [
            "mini-proof",
            "split-proof",
            "trusted-lemma-proof",
            "trivial-proof"
        ]
    );
}

#[test]
fn reference_proof_corpus_mini_proof_verdicts() {
    assert_local_proof_case_verdicts("mini-proof");
}

#[test]
fn reference_proof_corpus_split_proof_verdicts() {
    assert_local_proof_case_verdicts("split-proof");
}

#[test]
fn reference_proof_corpus_trusted_lemma_proof_verdicts() {
    assert_local_proof_case_verdicts("trusted-lemma-proof");
}

#[test]
fn reference_proof_corpus_trivial_proof_verdicts() {
    assert_local_proof_case_verdicts("trivial-proof");
}

#[cfg(feature = "z3-inference")]
#[test]
fn kore_exec_search_final_keeps_symbolic_anywhere_remainder_constrained() {
    // wrap(s(z)) denotes wrap(z), so X = z gives the symbolic state a successor.
    // A final remainder may contain wrap(s(X)) only under a constraint excluding that instance.
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"[]
module MAIN
  sort SortNat{} []
  sort SortW{} []
  symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
  symbol s{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
  symbol done{}() : SortW{} [constructor{}(), functional{}(), injective{}()]
  symbol wrap{}(SortNat{}) : SortW{} [anywhere{}(), functional{}(), injective{}()]
  axiom{R} \implies{R}(
    \and{R}(
      \top{R}(),
      \and{R}(\in{SortNat{}, R}(X0:SortNat{}, s{}(z{}())), \top{R}())
    ),
    \equals{SortW{}, R}(
      wrap{}(X0:SortNat{}),
      \and{SortW{}}(wrap{}(z{}()), \top{SortW{}}())
    )
  ) [label{}("collapse"), anywhere{}()]
  axiom{} \rewrites{SortW{}}(
    \and{SortW{}}(wrap{}(z{}()), \top{SortW{}}()),
    done{}()
  ) [label{}("finish")]
endmodule []
"#,
    )
    .unwrap();
    let initial = root.join("initial.kore");
    for state in [
        "wrap{}(s{}(X:SortNat{}))",
        "wrap{}(X:SortNat{})",
        "W:SortW{}",
    ] {
        fs::write(&initial, state).unwrap();
        let output = watchdog::output(watchdog::Request::KoreExec {
            definition: &definition,
            module: "MAIN",
            pattern: &initial,
            search_final: true,
        });
        assert!(output.status.success(), "{state}: {output:?}");
        let final_states = String::from_utf8(output.stdout).unwrap();
        assert!(final_states.contains("done{}()"), "{state}: {final_states}");
        assert!(final_states.contains("\\not{"), "{state}: {final_states}");
    }
    fs::remove_dir_all(root).unwrap();
}

/// Run `krust krun` on `source`, written as the definition of a fresh fixture, with `arguments`
/// after the definition path; standard input is closed so a definition that reads it never waits.
fn krun_source(source: &str, arguments: &[&str]) -> Output {
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("krun")
        .arg(&definition)
        .args(arguments)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    fs::remove_dir_all(root).unwrap();
    output
}

/// The final `<k>` cell content of a successful `krun`.
fn krun_success(source: &str, arguments: &[&str]) -> String {
    let output = krun_source(source, arguments);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

#[test]
fn generated_bool_side_conditions_need_no_bool_import() {
    // Heating, cooling, and `:/=K` are lowered to conditions built from `BOOL`'s connectives;
    // the module states them without importing `BOOL`.
    let stdout = krun_success(
        r#"
module MAIN
  syntax KResult ::= Val
  syntax Val ::= "v" | "w"
  syntax Exp ::= Val | "e" | wrap(Exp) | "frozen" | "done"
  rule wrap(HOLE:Exp) => HOLE ~> frozen [heat]
  rule HOLE:Exp ~> frozen => wrap(HOLE) [cool]
  rule e => v
  rule wrap(V:Val) => done requires w :/=K V
endmodule
"#,
        &[
            "--main-module",
            "MAIN",
            "--sort",
            "Exp",
            "--expression",
            "wrap(e)",
        ],
    );
    assert!(
        stdout.contains("Lbldone'Unds'MAIN'Unds'Exp{}()"),
        "{stdout}"
    );

    // A module whose only lowered sentence is a heat rule, without `BOOL`, compiles. (A heat
    // rule that matches no HOLE is rejected: `heat_and_cool_sentences_without_a_matched_hole_are_rejected`.)
    let output = krun_source(
        r#"
module MAIN
  syntax KResult ::= Op
  syntax Op ::= "a" | "b" | wrap(Op)
  rule wrap(HOLE:Op) => HOLE ~> wrap(b) [heat]
endmodule
"#,
        &["--main-module", "MAIN", "--sort", "Op", "--expression", "b"],
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn cell_fragment_sort_tests_need_no_bool_import() {
    const SOURCE: &str = r#"
module MAIN
  syntax Foo ::= "a" | "b"
  configuration <t> <k> $PGM:Foo </k> <mem> a </mem> <x> a </x> </t>
  rule <t> <k> a => b ... </k> R </t> requires isTCellFragment(R)
endmodule
"#;
    // The run and the two pattern searches use one compiled definition.
    let (root, definition) = fixture();
    fs::write(&definition, SOURCE).unwrap();
    let compiled = root.join("compiled");
    kcompile_for_krun(&definition, &["--main-module", "MAIN"], &compiled);
    let krun = |arguments: &[&str]| {
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["krun", "--definition"])
            .arg(&compiled)
            .args(["--sort", "Foo", "--expression", "a"])
            .args(arguments)
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).unwrap()
    };
    // The fragment test of `R` becomes the conjunction of the sort tests of `<mem>` and `<x>`.
    let stdout = krun(&[]);
    assert!(
        stdout.contains(
            "Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortFoo{}, SortKItem{}}(Lblb'Unds'MAIN'Unds'Foo{}())"
        ),
        "{stdout}"
    );

    // A search pattern's cast and fragment tests are conjoined too; the compiled definition
    // has no `BOOL`, so the pattern states each conjunct as its own equation.
    for pattern in [
        "<t> <k> X:Foo </k> <mem> Y:Foo </mem> <x> _ </x> </t>",
        "<t> <k> X:Foo </k> R </t> requires isTCellFragment(R)",
    ] {
        let stdout = krun(&["--pattern", pattern]);
        assert!(
            stdout.contains("VarX:SortFoo{}, Lblb'Unds'MAIN'Unds'Foo{}()"),
            "{pattern}: {stdout}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

/// Run `krust kcompile` on `source`, written as the definition of a fresh fixture, into a
/// scratch output directory.
fn kcompile_source(source: &str) -> Output {
    let (root, definition) = fixture();
    fs::write(&definition, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .arg("kcompile")
        .arg(&definition)
        .args(["--main-module", "MAIN", "--output-directory"])
        .arg(&root)
        .output()
        .unwrap();
    fs::remove_dir_all(root).unwrap();
    output
}

/// `kcompile` compiles and writes out a rule body 5,000 levels deep, an operator chain inside
/// an application: every compile stage and the writing of the artifacts (the definition's KORE,
/// JSON and provenance) run on a stack measured from the deepest term. The first compile pass
/// that recursed per level overflowed the 8 MiB main thread at 4,000 levels.
#[test]
fn kcompile_compiles_a_rule_body_thousands_of_levels_deep() {
    let chain = (0..5_000)
        .map(|operand| (operand % 10).to_string())
        .collect::<Vec<_>>()
        .join(" + ");
    let source = format!(
        "module MAIN\n  imports INT\n  syntax E ::= Int | E \"+\" E [left, symbol(plus)]\n  \
         syntax KItem ::= foo(E) [symbol(foo)]\n  rule foo({chain}) => .K\nendmodule\n"
    );
    let output = kcompile_source(&source);
    assert!(
        output.status.success(),
        "{}: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn anywhere_rules_needing_the_configuration_are_rejected_at_the_rule() {
    // An anywhere rule applies to its left-hand side wherever that term occurs, with no
    // configuration around it: no parent cell to hold several sibling cells. (Its fresh
    // variables are covered by `fresh_variables_outside_rewrite_steps_are_rejected_at_the_sentence`.)
    let source = r#"
module MAIN
  syntax Foo ::= "a" | "b"
  configuration <k> .K </k> <mem> a </mem>
  rule <k> .K </k> <mem> a => b </mem> [anywhere]
endmodule
"#;
    let output = kcompile_source(source);
    assert!(!output.status.success(), "{source}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(
            "definition.k:5:3: Error[InvalidAttribute]: An anywhere rule must rewrite a single term"
        ),
        "{stderr}"
    );
    assert!(!stderr.contains("cannot find a production"), "{stderr}");

    // The parent cell written around the same cells is a term, and the rule compiles and runs.
    let stdout = krun_success(
        r#"
module MAIN
  syntax Foo ::= "a" | "b"
  configuration <t> <k> .K </k> <mem> a </mem> </t>
  rule <t> <k> .K </k> <mem> a => b </mem> </t> [anywhere]
endmodule
"#,
        &["--main-module", "MAIN", "--sort", "Foo"],
    );
    assert!(
        stdout.contains("Lbl'-LT-'mem'-GT-'{}(Lblb'Unds'MAIN'Unds'Foo{}())"),
        "{stdout}"
    );
}

#[test]
fn fresh_variables_outside_rewrite_steps_are_rejected_at_the_sentence() {
    // A fresh value is drawn from the configuration's counter cell by the rewrite step that
    // introduces it, so a `!X` in an equation or a claim would be a variable nothing binds.
    // Every kind of sentence is checked in process by `definition_checks.rs` (same test name);
    // here the rejection is rendered at the sentence with a failing exit status.
    // The generated-input reproducer: a function equation whose result is a fresh value.
    let source = "module MAIN\n  imports INT\n  syntax Int ::= g() [function]\n  rule g() => !X:Int\nendmodule\n";
    let output = kcompile_source(source);
    assert!(!output.status.success(), "{source}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(
            "definition.k:4:3: Error[InvalidFreshConstant]: Fresh variable !X is not supported in a function rule:"
        ),
        "{source}\n{stderr}"
    );
    assert!(!stderr.contains("panicked"), "{stderr}");

    // A rewrite step draws the value, also for a local function inside it, whose equation
    // receives the fresh value from the enclosing rule as an argument.
    let stdout = krun_success(
        r#"
module MAIN
  imports INT
  syntax KItem ::= "go"
  rule <k> go => #fun(Y => Y +Int !X:Int)(1) ...</k>
endmodule
"#,
        &[
            "--main-module",
            "MAIN",
            "--sort",
            "KItem",
            "--expression",
            "go",
        ],
    );
    assert!(
        stdout.contains(r#"kseq{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1")), dotk{}())"#)
            && stdout.contains(r#"Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("1"))"#),
        "{stdout}"
    );
}

#[test]
fn fresh_variables_occur_only_where_a_rewrite_rule_builds_its_result() {
    // The value of `!X` is allocated by the step that applies the rule, so it exists only in the
    // configuration after the step: the right-hand side of a rewrite and `ensures`. Every place
    // it cannot occur, contexts included, is checked in process by `definition_checks.rs` (same
    // test name); here the rejection is rendered at the rule with a failing exit status.
    // The generated-input reproducer: a fresh variable as the pattern of a left-hand side.
    let source = "module MAIN\n  imports INT\n  syntax KItem ::= foo(Int)\n  rule foo(!X:Int) => 1\nendmodule\n";
    let output = kcompile_source(source);
    assert!(!output.status.success(), "{source}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(
            "definition.k:4:3: Error[InvalidFreshConstant]: Fresh variable !X cannot occur where a rule matches"
        ),
        "{source}\n{stderr}"
    );

    // The right-hand side and `ensures` see the allocated values.
    let stdout = krun_success(
        r#"
module MAIN
  imports INT
  syntax KItem ::= start(Int) | done(Int, Int)
  rule start(I) => done(!X:Int, !Y:Int) ensures !X:Int >=Int I
endmodule
"#,
        &[
            "--main-module",
            "MAIN",
            "--sort",
            "KItem",
            "--expression",
            "start(0)",
        ],
    );
    let compact = stdout.split_whitespace().collect::<String>();
    assert!(
        compact.contains(r#"KItem'Unds'Int'Unds'Int{}(\dv{SortInt{}}("0"),\dv{SortInt{}}("1"))"#)
            && compact.contains(r#"Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("2"))"#),
        "{stdout}"
    );
}

#[test]
fn a_rule_with_an_operator_out_of_scope_fails_at_the_operator() {
    // The generated-input reproducer: `==K` is declared in `K-EQUAL`, which the module does not
    // import, so the rule has no parse and the error names the place it stops. A `=>` that
    // recognition tried and associativity ruled out on the way is not the reason.
    let source = r#"module MAIN
  imports INT
  syntax KItem ::= foo(Int) | "bar"
  rule foo(B) => bar requires B ==K B
endmodule
"#;
    let output = kcompile_source(source);
    assert!(!output.status.success(), "{source}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(
            "definition.k:4:33: could not parse rule in module \"MAIN\": Parse error: unexpected token '=' following token 'B'."
        ),
        "{stderr}"
    );
    assert!(!stderr.contains("#KRewrite"), "{stderr}");
}

#[test]
fn heat_and_cool_sentences_without_a_matched_hole_are_rejected() {
    // Heating and cooling apply only when the subterm the sentence matches as HOLE is not yet,
    // or is, a result. A rule that matches no HOLE would test a variable nothing binds. The
    // stages that reject such rules, and a context whose HOLE is rewritten to a term without
    // HOLE, are tested on their pipeline input by
    // `resolve_heat_cool::stage_tests::heat_and_cool_rules_without_a_matched_hole_are_rejected_at_the_rule`
    // and `resolve_contexts::stage_tests::a_context_rewriting_hole_away_is_rejected_at_the_context`;
    // here the rejection is rendered at the rule with a failing exit status.
    // The generated-input reproducer.
    let source = "module MAIN\n  imports K-EQUAL\n  syntax KResult ::= Op\n  syntax Op ::= \"a\" | \"b\" | wrap(Op)\n  rule a => b [heat]\nendmodule\n";
    let output = kcompile_source(source);
    assert!(!output.status.success(), "{source}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(
            "definition.k:5:3: Error[InvalidHeatCool]: A heat rule must match HOLE on its left-hand side"
        ),
        "{source}\n{stderr}"
    );
    assert!(!stderr.contains("panicked"), "{stderr}");
}

#[test]
fn stream_cells_initialize_without_a_configuration_variable() {
    // A stream cell's initial contents are its stream's builtin configuration, which reads
    // `$STDIN` and `$IO` even when the user's configuration reads no variable.
    for (source, expected) in [
        (
            r#"
module MAIN
  imports INT
  imports LIST
  configuration <k> .K </k> <in stream="stdin"> .List </in>
endmodule
"#,
            "Lbl'Hash'istream'LParUndsRParUnds'K-IO'Unds'Stream'Unds'Int{}(\\dv{SortInt{}}(\"0\"))",
        ),
        (
            r#"
module MAIN
  imports LIST
  imports STRING
  configuration <t> <k> .K </k> <out stream="stdout"> .List </out> </t>
endmodule
"#,
            "Lbl'Hash'ostream'LParUndsRParUnds'K-IO'Unds'Stream'Unds'Int{}(\\dv{SortInt{}}(\"1\"))",
        ),
    ] {
        let stdout = krun_success(source, &["--main-module", "MAIN", "--sort", "KItem"]);
        assert!(stdout.contains(expected), "{source}: {stdout}");
    }
}

#[test]
fn fresh_variables_need_no_int_import() {
    // The counter cell that supplies fresh values is advanced with `INT`'s `_+Int_`; a module
    // that only sees `INT-SYNTAX` still states the rule.
    let stdout = krun_success(
        r#"
module MAIN
  imports INT-SYNTAX
  syntax Foo ::= foo(Int) | "a"
  syntax Foo ::= freshFoo(Int) [freshGenerator, function, total]
  rule freshFoo(I) => foo(I)
  configuration <k> $PGM:Foo </k>
  rule <k> a => !X:Foo ... </k>
endmodule
"#,
        &[
            "--main-module",
            "MAIN",
            "--sort",
            "Foo",
            "--expression",
            "a",
        ],
    );
    assert!(
        stdout.contains("Lblfoo'LParUndsRParUnds'MAIN'Unds'Foo'Unds'Int{}(\\dv{SortInt{}}(\"0\"))"),
        "{stdout}"
    );
}

/// Class test for the module-view ticket: a module's rule grammar is what its imports declare
/// plus what compilation adds to that module, and a rule that parses in a module is typed in it.
/// `OTHER` imports nothing and is not the main module, so the configuration is not in its view:
/// neither `<k>` nor the cell compilation adds to the configuration, `<generatedCounter>`, parses
/// there. Were the counter cell in `OTHER`'s view, its rule would parse and then fail to type, on
/// the internal label `#SemanticCastToInt`, as `Int` is not in that view.
#[cfg(unix)]
#[test]
fn a_compiler_added_cell_is_in_the_view_of_the_modules_that_see_the_configuration() {
    let outcome = |cell_rule: &str| {
        let source = format!(
            "module OTHER\n  syntax Foo ::= \"foo\"\n  syntax KItem ::= Foo\n  {cell_rule}\nendmodule\nmodule MAIN\n  imports OTHER\n  imports INT\n  configuration <k> $PGM:Foo </k>\nendmodule\n"
        );
        let (root, definition) = fixture();
        fs::write(&definition, source).unwrap();
        let compiled = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["kcompile", definition.to_str().unwrap()])
            .args(["--main-module", "MAIN", "--syntax-module", "MAIN"])
            .arg("--output-directory")
            .arg(root.join("kompiled"))
            .stdin(Stdio::null())
            .output()
            .unwrap();
        fs::remove_dir_all(root).unwrap();
        let stderr = String::from_utf8_lossy(&compiled.stderr).into_owned();
        assert!(
            !stderr.contains("#SemanticCastTo"),
            "{cell_rule}: a rule that parsed failed on an internal label: {stderr}"
        );
        (
            compiled.status.success(),
            stderr.contains("could not parse rule"),
        )
    };
    let counter = outcome("rule <generatedCounter> C => C </generatedCounter>");
    assert_eq!(counter, outcome("rule <k> foo => .K </k>"));
    assert_eq!(counter, (false, true));
}

/// The counter cell compilation adds to the configuration is a cell of every view that holds the
/// configuration's cells, also outside the main module: `RULES` sees `CONF`'s configuration and
/// names `<generatedCounter>` (docs/compatibility.md, "Compiler-resolved fresh constants").
#[cfg(unix)]
#[test]
fn a_module_that_sees_the_configuration_names_the_compiler_added_cell() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        "module CONF\n  syntax Foo ::= \"foo\"\n  configuration <k> $PGM:Foo </k>\nendmodule\nmodule RULES\n  imports CONF\n  rule <generatedCounter> C => C </generatedCounter>\nendmodule\nmodule MAIN\n  imports RULES\n  imports INT\nendmodule\n",
    )
    .unwrap();
    let compiled = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args(["kcompile", definition.to_str().unwrap()])
        .args(["--main-module", "MAIN", "--syntax-module", "MAIN"])
        .arg("--output-directory")
        .arg(root.join("kompiled"))
        .stdin(Stdio::null())
        .output()
        .unwrap();
    fs::remove_dir_all(root).unwrap();
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
}
