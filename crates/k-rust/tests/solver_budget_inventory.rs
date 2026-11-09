//! The inventory of every place in the workspace that builds a backend or a solver, or makes the
//! solver options one is built with, and the proof that each one's default bounds the solver by
//! Z3 resource units, never by the clock (CF-33: a solver answer is a function of its query).
//!
//! How the list is found. A `Z3Solver` is built only by its constructors, and outside tests only
//! k-rust's `Backend` calls them, with the `BackendOptions` it was built with; every `Backend` is
//! built by a constructor that takes `BackendOptions`. So the mode of every solver answer is
//! chosen where a `Backend` or a `Z3Solver` is built (the options expression at the call), and
//! where solver options are made: a function returning them, a `Default` impl, or a constant.
//! [`scan`] finds all of these in the non-test sources of the workspace (`crates/`,
//! `kink/crates/`, `krs/crates/`), by the call or the signature, and the test fails on any site
//! that is not listed here, on any listed site that is gone, and on any build site whose options
//! expression is not the one listed. A new entry point therefore cannot appear without being
//! listed and audited. A clock is built only through `SmtBudget::clock` or `SmtBudget::requested`,
//! which clippy's `disallowed-methods` makes each caller justify in an `#[expect]`, so the
//! entries below that may yield a clock name the flag or field that asks for it.
//!
//! Each producer names the test that asserts its default is units; the test checks that the
//! named test exists. The producers k-rust reaches are asserted here.

use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
};

use k_rust::backend::{Backend, BackendOptions, DEFAULT_SMT_RESOURCE_LIMIT, SmtBudget};

/// A place that builds a `Backend` or a `Z3Solver`: its file, its enclosing function, and the
/// options expression it builds with, which the scan finds at the call.
struct Build {
    file: &'static str,
    function: &'static str,
    options: &'static str,
}

/// A place that makes solver options, and what its default is.
struct Producer {
    file: &'static str,
    item: &'static str,
    default: Mode,
}

/// What a producer's default is.
enum Mode {
    /// Units, which the named test (file, function) asserts.
    Units(&'static str, &'static str),
    /// Still the clock, through the door, until the named CF-33 unit makes it units.
    Clock(&'static str),
}

const THIS: &str = "crates/k-rust/tests/solver_budget_inventory.rs";

const BUILDS: &[Build] = &[
    // The one caller of the solver's constructors: the options the backend was built with.
    Build {
        file: "crates/k-rust/src/backend/mod.rs",
        function: "run_with_solver",
        options: "options",
    },
    // Library constructors that are handed their options.
    Build {
        file: "crates/k-rust/src/krun.rs",
        function: "backend",
        options: "options",
    },
    // krust's commands: their `SmtArgs` (`--smt-timeout` asks for the clock).
    Build {
        file: "crates/k-rust/src/main.rs",
        function: "krun",
        options: "options.smt",
    },
    Build {
        file: "crates/k-rust/src/main.rs",
        function: "kore_exec",
        options: "backend_options",
    },
    Build {
        file: "crates/k-rust/src/main.rs",
        function: "kore_rpc",
        options: "options.smt.options()",
    },
    Build {
        file: "crates/k-rust/src/main.rs",
        function: "kore_simplify",
        options: "options.smt.options()",
    },
    Build {
        file: "crates/k-rust/src/main.rs",
        function: "kore_get_model",
        options: "options.smt.options()",
    },
    Build {
        file: "crates/k-rust/src/main.rs",
        function: "kore_implies_inner",
        options: "options.smt.options()",
    },
    Build {
        file: "crates/k-rust/src/main.rs",
        function: "kore_match_disjunction_command",
        options: "options.smt.options()",
    },
    // The bindings.
    Build {
        file: "crates/k-rust-napi/src/lib.rs",
        function: "create_backend_native",
        options: "smt_budget,",
    },
    Build {
        file: "crates/k-rust-wasm/src/lib.rs",
        function: "create_backend_wasm",
        options: "smt_budget,",
    },
    Build {
        file: "crates/k-rust-wasm/src/lib.rs",
        function: "compile_backend_wasm",
        options: "BackendOptions::default()",
    },
    // The fuzzer: its campaign's `BackendSettings::options`, or the solve proposer's units.
    Build {
        file: "crates/k-rust-fuzz/src/assemble.rs",
        function: "build_backend",
        options: "options",
    },
    Build {
        file: "crates/k-rust-fuzz/src/engine/live.rs",
        function: "build",
        options: "options",
    },
    Build {
        file: "crates/k-rust-fuzz/src/proposers/solve.rs",
        function: "backend",
        options: "options",
    },
    // kink: kink-native's BACKEND_OPTIONS, or a corpus's `[budget] smt_resource_limit` units.
    Build {
        file: "kink/crates/kink-campaign/src/runner.rs",
        function: "load",
        options: "solver",
    },
    Build {
        file: "kink/crates/kink-corpus/src/admission.rs",
        function: "input_backend",
        options: "kink_native::BACKEND_OPTIONS",
    },
    Build {
        file: "kink/crates/kink-flow/src/admit.rs",
        function: "admit_definition",
        options: "manifest.budget.backend_options()",
    },
    Build {
        file: "kink/crates/kink-flow/src/pattern.rs",
        function: "new",
        options: "budget.backend_options()",
    },
    Build {
        file: "kink/crates/kink-flow/src/results.rs",
        function: "diagnose",
        options: "kink_native::backend_options(self.smt_resource_limit)",
    },
    Build {
        file: "kink/crates/kink-native/src/consistency.rs",
        function: "loaded_definition",
        options: "crate::BACKEND_OPTIONS",
    },
    Build {
        file: "kink/crates/kink-native/src/exclusion.rs",
        function: "load_validated",
        options: "solver",
    },
    // krs: the semantics' solver options (`--smt-clock-ms` asks for the clock).
    Build {
        file: "krs/crates/krs-exec/src/lib.rs",
        function: "backend_in_item_order",
        options: "solver",
    },
];

const PRODUCERS: &[Producer] = &[
    Producer {
        file: "crates/k-rust-backend/src/smt/budget.rs",
        item: "impl Default for SmtBudget",
        default: Mode::Units(THIS, "library_defaults_are_units"),
    },
    Producer {
        file: "crates/k-rust-backend/src/smt/z3.rs",
        item: "impl Default for Z3Options",
        default: Mode::Units(THIS, "library_defaults_are_units"),
    },
    Producer {
        file: "crates/k-rust-backend/src/smt/z3/trace.rs",
        item: "fn parse_budget",
        default: Mode::Units(
            "crates/k-rust-backend/src/smt/z3/trace/tests.rs",
            "a_headers_budget_is_units_unless_it_states_a_clock",
        ),
    },
    Producer {
        file: "crates/k-rust-backend/src/smt/z3/trace.rs",
        item: "fn legacy_budget",
        default: Mode::Units(
            "crates/k-rust-backend/src/smt/z3/trace/tests.rs",
            "a_headers_budget_is_units_unless_it_states_a_clock",
        ),
    },
    Producer {
        file: "crates/k-rust/src/backend/mod.rs",
        item: "impl Default for BackendOptions",
        default: Mode::Units(THIS, "library_defaults_are_units"),
    },
    Producer {
        file: "crates/k-rust/src/main.rs",
        item: "fn options",
        default: Mode::Units(
            "crates/k-rust/src/main.rs",
            "smt_flags_give_units_unless_a_clock_is_asked_for",
        ),
    },
    Producer {
        file: "crates/k-rust-fuzz/src/spec.rs",
        item: "fn options",
        default: Mode::Clock("unit 4, the fuzz campaign's smt-timeout-ms"),
    },
    Producer {
        file: "crates/k-rust-fuzz/src/spec.rs",
        item: "impl Default for BackendSettings",
        default: Mode::Clock("unit 4, the fuzz campaign's smt-timeout-ms"),
    },
    Producer {
        file: "kink/crates/kink-native/src/lib.rs",
        item: "const BACKEND_OPTIONS",
        default: Mode::Units(
            "kink/crates/kink-native/src/lib.rs",
            "answers_are_keyed_under_resource_bounds_or_without_z3",
        ),
    },
    Producer {
        file: "kink/crates/kink-native/src/lib.rs",
        item: "fn backend_options",
        default: Mode::Units(
            "kink/crates/kink-native/src/lib.rs",
            "answers_are_keyed_under_resource_bounds_or_without_z3",
        ),
    },
    Producer {
        file: "kink/crates/kink-campaign/src/runner.rs",
        item: "fn backend_options",
        default: Mode::Units(
            "kink/crates/kink-campaign/tests/manifest.rs",
            "kink_tier::counter_manifest_is_deterministic_and_declaration_changes_are_local",
        ),
    },
    Producer {
        file: "kink/crates/kink-flow/src/manifest.rs",
        item: "fn backend_options",
        default: Mode::Units(
            "kink/crates/kink-flow/tests/manifest.rs",
            "a_minimal_manifest_takes_every_default",
        ),
    },
    Producer {
        file: "krs/crates/krs-exec/src/lib.rs",
        item: "fn solver",
        default: Mode::Units(
            "krs/crates/krs-cli/src/main.rs",
            "solver_options_select_one_mode_and_claim_timeout_is_prove_only",
        ),
    },
    Producer {
        file: "krs/crates/krs-cli/src/command.rs",
        item: "fn solver",
        default: Mode::Units(
            "krs/crates/krs-cli/src/main.rs",
            "solver_options_select_one_mode_and_claim_timeout_is_prove_only",
        ),
    },
    Producer {
        file: "krs/crates/krs-cli/src/main.rs",
        item: "fn solver",
        default: Mode::Units(
            "krs/crates/krs-cli/src/main.rs",
            "solver_options_select_one_mode_and_claim_timeout_is_prove_only",
        ),
    },
];

/// The types that carry a solver budget.
const BUDGET_TYPES: &[&str] = &[
    "BackendOptions",
    "Z3Options",
    "SmtBudget",
    "BackendSettings",
];

fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The non-test Rust sources under `directory`: no `tests`, `benches`, `examples` or `testdata`
/// directory, no `tests.rs` or `*_tests.rs` file.
fn sources(directory: &Path, found: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(directory) else {
        return;
    };
    let mut entries = entries
        .map(|entry| entry.unwrap().path())
        .collect::<Vec<_>>();
    entries.sort();
    for path in entries {
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        if path.is_dir() {
            if !matches!(
                name.as_str(),
                "target" | "tests" | "benches" | "examples" | "testdata" | "node_modules"
            ) {
                sources(&path, found);
            }
        } else if name.ends_with(".rs") && name != "tests.rs" && !name.ends_with("_tests.rs") {
            found.push(path);
        }
    }
}

/// Whether the attributes above line `index` include a `cfg` that holds only in tests
/// (`#[cfg(test)]`, `#[cfg(all(test, ...))]`).
fn under_cfg_test(lines: &[&str], index: usize) -> bool {
    lines[..index]
        .iter()
        .rev()
        .take_while(|line| {
            let line = line.trim_start();
            line.starts_with("#[") || line.starts_with("///") || line.starts_with(')')
        })
        .any(|line| {
            let line = line.trim_start();
            line.starts_with("#[cfg(")
                && (line.starts_with("#[cfg(test)]") || line.starts_with("#[cfg(all(test,"))
        })
}

/// The lines of a source before its first top-level test module.
fn non_test_lines(text: &str) -> Vec<&str> {
    let lines = text.lines().collect::<Vec<_>>();
    let module = regex::Regex::new(r"^(pub(\([^)]*\))? )?mod \w+ \{").unwrap();
    let end = (0..lines.len())
        .find(|&index| module.is_match(lines[index]) && under_cfg_test(&lines, index))
        .unwrap_or(lines.len());
    lines[..end].to_vec()
}

/// What [`scan`] finds: the build sites as `(file, function, the call's text)`, and the
/// producers as `(file, item)`.
type Found = (Vec<(String, String, String)>, BTreeSet<(String, String)>);

/// Every build site and every producer of solver options in the workspace's non-test sources.
fn scan() -> Found {
    let root = workspace();
    let mut files = Vec::new();
    for directory in ["crates", "kink/crates", "krs/crates"] {
        sources(&root.join(directory), &mut files);
    }
    let build =
        regex::Regex::new(r"\b(Backend::(new|from_\w+)|Z3Solver::(new|with_\w+))\(").unwrap();
    let function =
        regex::Regex::new(r"^\s*(pub(\([^)]*\))?\s+)?(const\s+)?(async\s+)?(unsafe\s+)?fn\s+(\w+)")
            .unwrap();
    let types = BUDGET_TYPES.join("|");
    let returns =
        regex::Regex::new(&format!(r"(?s)\bfn\s+(\w+)[^;{{]*?->[^;{{]*\b({types})\b")).unwrap();
    let default = regex::Regex::new(&format!(r"\bimpl Default for ({types})\b")).unwrap();
    let constant = regex::Regex::new(&format!(
        r"\bconst ([A-Z_]+): (k_rust::backend::)?({types})\b"
    ))
    .unwrap();
    let mut builds = Vec::new();
    let mut producers = BTreeSet::new();
    for path in files {
        let file = path
            .strip_prefix(&root)
            .unwrap()
            .to_string_lossy()
            .into_owned();
        let text = fs::read_to_string(&path).unwrap();
        let lines = non_test_lines(&text);
        let mut current: Option<(String, bool)> = None;
        for (index, line) in lines.iter().enumerate() {
            if let Some(found) = function.captures(line) {
                current = Some((found[6].to_owned(), under_cfg_test(&lines, index)));
            }
            if line.trim_start().starts_with("//") || !build.is_match(line) {
                continue;
            }
            match &current {
                Some((_, true)) => {}
                Some((name, false)) => {
                    let call = lines[index..(index + 6).min(lines.len())].join("\n");
                    builds.push((file.clone(), name.clone(), call));
                }
                None => panic!("{file}:{}: a build outside a function", index + 1),
            }
        }
        let text = lines.join("\n");
        for found in returns.captures_iter(&text) {
            let line = text[..found.get(0).unwrap().start()].matches('\n').count();
            if !under_cfg_test(&lines, line) {
                producers.insert((file.clone(), format!("fn {}", &found[1])));
            }
        }
        for found in default.captures_iter(&text) {
            producers.insert((file.clone(), format!("impl Default for {}", &found[1])));
        }
        for found in constant.captures_iter(&text) {
            let line = text[..found.get(0).unwrap().start()].matches('\n').count();
            if !under_cfg_test(&lines, line) && !text.contains(&format!("impl {}", &found[3])) {
                producers.insert((file.clone(), format!("const {}", &found[1])));
            }
        }
    }
    (builds, producers)
}

/// Every place that builds a backend or a solver, or makes solver options, is listed, and each
/// listed build uses the listed options; every producer names an existing test of its default.
#[test]
fn every_backend_and_solver_entry_point_is_inventoried() {
    let (builds, producers) = scan();
    let listed = BUILDS
        .iter()
        .map(|build| (build.file.to_owned(), build.function.to_owned()))
        .collect::<BTreeSet<_>>();
    let found = builds
        .iter()
        .map(|(file, function, _)| (file.clone(), function.clone()))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        found.difference(&listed).collect::<Vec<_>>(),
        Vec::<&(String, String)>::new(),
        "unlisted places that build a backend or a solver: add them to BUILDS with the options \
         they use, after checking that those options default to units"
    );
    assert_eq!(
        listed.difference(&found).collect::<Vec<_>>(),
        Vec::<&(String, String)>::new(),
        "listed builds that are gone"
    );
    for build in BUILDS {
        assert!(
            builds
                .iter()
                .any(|(file, function, call)| file == build.file
                    && function == build.function
                    && call.contains(build.options)),
            "{} `{}` no longer builds with `{}`: audit its options and update BUILDS",
            build.file,
            build.function,
            build.options
        );
    }
    let listed = PRODUCERS
        .iter()
        .map(|producer| (producer.file.to_owned(), producer.item.to_owned()))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        producers.difference(&listed).collect::<Vec<_>>(),
        Vec::<&(String, String)>::new(),
        "unlisted makers of solver options: add them to PRODUCERS with the test that asserts \
         their default is units"
    );
    assert_eq!(
        listed.difference(&producers).collect::<Vec<_>>(),
        Vec::<&(String, String)>::new(),
        "listed makers of solver options that are gone"
    );
    for producer in PRODUCERS {
        let (test_file, test) = match producer.default {
            Mode::Units(test_file, test) => (test_file, test),
            Mode::Clock(until) => {
                assert!(until.starts_with("unit "), "{until}");
                continue;
            }
        };
        let text = fs::read_to_string(workspace().join(test_file)).unwrap();
        let name = test.rsplit("::").next().unwrap();
        assert!(
            text.contains(&format!("fn {name}(")),
            "{} names the test {test} of {test_file}, which does not exist",
            producer.item,
        );
    }
}

/// The library's defaults, its wire's, and the solvers and backends built from them are bounded
/// by units.
#[test]
fn library_defaults_are_units() {
    let units = SmtBudget::Units(DEFAULT_SMT_RESOURCE_LIMIT);
    assert_eq!(SmtBudget::default(), units);
    assert_eq!(SmtBudget::DEFAULT, units);
    assert_eq!(BackendOptions::default().smt_budget, units);
    assert_eq!(BackendOptions::DEFAULT.smt_budget, units);
    assert_eq!(
        serde_json::from_str::<BackendOptions>("{}")
            .unwrap()
            .smt_budget,
        units
    );
    #[cfg(feature = "z3-inference")]
    {
        use k_rust::k_rust_backend::smt::{SmtSolver, Z3Options, Z3Solver};
        assert_eq!(Z3Options::default().budget, units);
        assert_eq!(Z3Options::DEFAULT.budget, units);
        let definition = k_rust::k_rust_backend::definition::BackendDefinition::internalize(
            &k_rust::kore::parser::parse_definition(DEFINITION).unwrap(),
            "MAIN",
        )
        .unwrap();
        assert!(
            Z3Solver::new(&definition)
                .unwrap()
                .undecided_answers_reproducible()
        );
        assert!(
            Z3Solver::with_prelude(&definition, "(declare-const a Int)")
                .unwrap()
                .undecided_answers_reproducible()
        );
        let mut backend = Backend::new(DEFINITION, "MAIN", BackendOptions::default()).unwrap();
        let reproducible = backend
            .with_solver(None, |_, solver| {
                Ok::<_, k_rust::backend::BackendError>(solver.undecided_answers_reproducible())
            })
            .unwrap();
        assert!(reproducible);
    }
    #[cfg(not(feature = "z3-inference"))]
    drop(Backend::new(DEFINITION, "MAIN", BackendOptions::default()).unwrap());
}

const DEFINITION: &str = r#"[]
module MAIN
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
endmodule []"#;
