//! Re-pin R0b (`draft/tasks/repin-501f18b9`): the exclusions of kink-native's `exclusion` module
//! on real k-rust runs and loads, the implementation-chosen hook list pinned against k-rust's
//! source, and the testdata definitions each definition-level exclusion affects.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::time::Duration;

use k_rust::backend::{Backend, BackendOptions};
use k_rust::kompile::CompileOptions;
use k_rust::kore::{ast::Pattern, parser::parse_definition, parser::parse_pattern};
use k_rust_backend::nesting::with_simplification_stack_budget;
use kink_native::exclusion::{
    DOMAINS_OPEN_HOOKS, DefinitionExclusions, Exclusion, IMPLEMENTATION_CHOSEN_HOOKS,
    K_RUST_IMPLEMENTATION_CHOSEN_HOOKS, state_references_implementation_chosen,
};
use kink_native::execution::{
    AdaptedExecution, ExecutionAdapter, ExecutionBudget, HaltClass, SolverProfile,
};
use kink_native::feasibility::TestInitialState;
use kink_native::step_events::ObservationDecider;
use kink_native::{NativeValidator, ValidatedDefinition};

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn on_a_big_stack(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(work)
        .unwrap()
        .join()
        .unwrap();
}

/// The R0b fixture `testdata/k/r0b/<name>.k`, compiled, and its encoded main module (the
/// upper-cased name).
fn r0b(name: &str) -> (ValidatedDefinition, String) {
    fixture("r0b", name)
}

/// The fixture `testdata/k/<dir>/<name>.k`, compiled, and its encoded main module (the
/// upper-cased name).
fn fixture(dir: &str, name: &str) -> (ValidatedDefinition, String) {
    let module = name.to_ascii_uppercase();
    let loaded = support::load_path(
        &Path::new(support::DIR).join(format!("{dir}/{name}.k")),
        &module,
    );
    let side = NativeValidator::bind(loaded, CompileOptions::default())
        .compile_baseline()
        .unwrap_or_else(|e| panic!("{name}: {e}"));
    (side, k_rust::kast::identifier::encode(&module))
}

fn budget() -> ExecutionBudget {
    ExecutionBudget {
        time: Duration::from_secs(60),
        max_simplification_iterations: 10_000,
        max_depth: Some(100),
        max_breadth: None,
    }
}

fn backend(side: &ValidatedDefinition, module: &str) -> Backend {
    Backend::new(
        &side.artifacts().definition_kore,
        module,
        BackendOptions::default(),
    )
    .unwrap()
}

fn run(side: &ValidatedDefinition, module: &str, program: Pattern) -> AdaptedExecution {
    ExecutionAdapter::with_profile(SolverProfile::BUILD)
        .execute(
            &mut backend(side, module),
            &support::initial_state(program, "SortProg"),
            budget(),
        )
        .unwrap()
}

/// Every string literal naming a hook (`"NAMESPACE.name"`) written before a `=>` in `text`.
fn arm_hooks(text: &str) -> BTreeSet<String> {
    text.lines()
        .filter(|line| line.contains("=>"))
        .flat_map(|line| {
            let head = &line[..line.find("=>").unwrap()];
            head.split('"')
                .skip(1)
                .step_by(2)
                .filter(|literal| literal.contains('.'))
                .map(str::to_owned)
                .collect::<Vec<_>>()
        })
        .collect()
}

/// The text of the function `name` in `source`, from its signature to its closing brace at the
/// signature's indentation.
fn function<'s>(source: &'s str, name: &str) -> &'s str {
    let start = source
        .find(&format!("fn {name}("))
        .unwrap_or_else(|| panic!("k-rust has no fn {name}"));
    let line_start = source[..start].rfind('\n').map_or(0, |at| at + 1);
    let indent = source[line_start..start]
        .chars()
        .take_while(|c| *c == ' ')
        .count();
    let close = format!("\n{}}}\n", " ".repeat(indent));
    let end = source[start..].find(&close).expect("the function ends") + start;
    &source[start..end]
}

/// The k-rust-backend source directory the workspace builds against (its path dependency).
fn k_rust_backend() -> PathBuf {
    let manifest: toml::Value =
        toml::from_str(&std::fs::read_to_string(root().join("Cargo.toml")).unwrap()).unwrap();
    root().join(
        manifest["workspace"]["dependencies"]["k-rust-backend"]["path"]
            .as_str()
            .expect("k-rust-backend is a path dependency"),
    )
}

/// `K_RUST_IMPLEMENTATION_CHOSEN_HOOKS` is exactly the set of hooks for which k-rust's
/// `implementation_chosen_in` (k-rust-backend `builtin.rs`) can return `Some`, read from the
/// k-rust source the workspace builds against: its match arms, the hooks of the binary Float
/// operations `float::mixed_destination` accepts (`BinaryOperation::of`) and the one hook
/// `float::nan_sign` reads. `IMPLEMENTATION_CHOSEN_HOOKS` is that list and the kink-side
/// `DOMAINS_OPEN_HOOKS`, each once. A change of any of them in k-rust fails this test, so a
/// re-pin re-derives the list.
///
/// Re-pin R0c deliverable 5 (R0b review 1 minor): reading arms and two helper calls misses a
/// third fallthrough helper or a widened `nan_sign` condition, so the source text of the four
/// functions is pinned by digest as well.
#[test]
fn implementation_chosen_hooks_are_k_rusts() {
    let backend = k_rust_backend();
    let builtin = std::fs::read_to_string(backend.join("src/builtin.rs")).unwrap();
    let float = std::fs::read_to_string(backend.join("src/builtin/float.rs")).unwrap();
    let chosen = function(&builtin, "implementation_chosen_in");
    let mixed = function(&float, "mixed_destination");
    let of = function(
        &float[float
            .find("impl BinaryOperation {")
            .expect("BinaryOperation")..],
        "of",
    );
    let nan = function(&float, "nan_sign");
    // The exact texts at k-rust 501f18b9; a changed text needs the hook list re-derived from it.
    let digests = [
        ("implementation_chosen_in", chosen),
        ("float::mixed_destination", mixed),
        ("BinaryOperation::of", of),
        ("float::nan_sign", nan),
    ]
    .map(|(name, text)| (name, kink_patch::sha256(text.as_bytes()).to_string()));
    assert_eq!(
        digests,
        [
            (
                "implementation_chosen_in",
                "4c51bafff2346bfd456986f7165a3b4a76e7b93449d4dc035da4a9cd17191a8b".to_owned()
            ),
            (
                "float::mixed_destination",
                "c219eec25b1ad8899f7af425aed682f2edcb72010065a62f60a019324354d623".to_owned()
            ),
            (
                "BinaryOperation::of",
                "7d79eac8ebb73ef293b15f4a731b339f576b74f29b3b93de85080b52d0b20eca".to_owned()
            ),
            (
                "float::nan_sign",
                "c17041cfd7ea611ad2def7d98277f9204f00e410c066beb4ac6d7bc93c2f285a".to_owned()
            ),
        ]
    );
    // The fallthrough arm is exactly the two Float helpers.
    assert!(
        chosen.contains("float::mixed_destination(hook, arguments)")
            && chosen.contains(".or_else(|| float::nan_sign(hook, arguments))"),
        "{chosen}"
    );
    let mut hooks = arm_hooks(chosen);
    assert_eq!(hooks.len(), 5, "{chosen}");
    assert!(mixed.contains("BinaryOperation::of(hook)?"), "{mixed}");
    let operations = arm_hooks(of);
    assert_eq!(operations.len(), 6, "{operations:?}");
    hooks.extend(operations);
    assert!(nan.contains(r#"if hook != "FLOAT.sign" {"#), "{nan}");
    hooks.insert("FLOAT.sign".to_owned());
    let k_rust = K_RUST_IMPLEMENTATION_CHOSEN_HOOKS
        .iter()
        .map(|hook| (*hook).to_owned())
        .collect::<BTreeSet<_>>();
    assert_eq!(hooks, k_rust);
    assert_eq!(hooks.len(), K_RUST_IMPLEMENTATION_CHOSEN_HOOKS.len());
    let all = K_RUST_IMPLEMENTATION_CHOSEN_HOOKS
        .iter()
        .copied()
        .chain(DOMAINS_OPEN_HOOKS.iter().map(|(hook, _, _)| *hook))
        .collect::<Vec<_>>();
    assert_eq!(IMPLEMENTATION_CHOSEN_HOOKS, all.as_slice());
    assert_eq!(
        all.iter().collect::<BTreeSet<_>>().len(),
        all.len(),
        "each hook once"
    );
}

/// Re-pin R0c deliverable 2 (R0b review 1 major 2): every kink-side census hook is one whose
/// value `k-rust/builtin/domains.md` leaves to the backend, the implementation or the
/// environment. For each, the cited lines of domains.md at the pinned k-rust say so (the phrase
/// is in them), and domains.md declares the hook. The file's digest is pinned: a re-pin that
/// changes the prelude text sweeps it again (README "What a kill trusts"; handoff R0c lists each
/// hook with its lines).
#[test]
fn domains_md_leaves_these_hook_values_open() {
    let path = k_rust_backend().join("../k-rust/builtin/domains.md");
    let text = std::fs::read_to_string(&path).unwrap();
    assert_eq!(
        kink_patch::sha256(text.as_bytes()).to_string(),
        "eb5b7c3cd001d5fe3cbd481598bb53c3abfd417c409135276008d50edf79aa0d",
        "domains.md changed: sweep it again for hook values it leaves open"
    );
    let lines = text.lines().collect::<Vec<_>>();
    for (hook, range, phrase) in DOMAINS_OPEN_HOOKS {
        let (first, last) = range.split_once('-').unwrap();
        let (first, last) = (
            first.parse::<usize>().unwrap(),
            last.parse::<usize>().unwrap(),
        );
        let cited = lines[first - 1..last].join(" ");
        assert!(
            cited.contains(phrase),
            "{hook}: domains.md:{range} does not say {phrase:?}"
        );
        assert!(
            text.contains(&format!("hook({hook})")) || text.contains(&format!("hook({hook}),")),
            "{hook} is not a domains.md hook"
        );
    }
    // Each kink-side hook, once, and none of k-rust's own.
    let kink = DOMAINS_OPEN_HOOKS
        .iter()
        .map(|(hook, _, _)| *hook)
        .collect::<BTreeSet<_>>();
    assert_eq!(kink.len(), DOMAINS_OPEN_HOOKS.len());
    assert!(
        kink.iter()
            .all(|hook| !K_RUST_IMPLEMENTATION_CHOSEN_HOOKS.contains(hook))
    );
    // Deliverable 8 rests on `encodeBytes` with a named encoding: domains.md names its
    // encodings (line 2012), so it is not on the list.
    assert!(lines[2011].contains("using `UTF-8`"), "{}", lines[2011]);
    assert!(!IMPLEMENTATION_CHOSEN_HOOKS.contains(&"BYTES.encodeBytes"));
}

/// Every testdata and example definition that compiles, by its definition-level exclusions
/// (decision 1's census, the load's stack stops, C-10's role-rooted axioms). The census flags
/// exactly the definitions whose own rules use an implementation-chosen hook: Float arithmetic
/// (`rulecondfail`, `t12hook`, `t12probe`, `t12unev`) and `String2Bytes` (`t12probe`). Every
/// comparison on them is unknown. No load counts a stack stop on this thread, and no definition
/// has an axiom rooted at a collection role symbol.
///
/// Re-pin R0c: deliverable 8 rewrote the Bytes keys of `bytes-map` and both copies of
/// `collstore` with `encodeBytes("UTF-8", ..)`, so R0b's three `String2Bytes` flags are gone;
/// deliverable 2's domains.md additions flag no testdata or example definition.
#[test]
fn definition_exclusions_over_testdata() {
    on_a_big_stack(|| {
        let mut files = Vec::new();
        let mut pending = vec![
            root().join("testdata/k"),
            root().join("testdata/flow"),
            root().join("examples/imp"),
        ];
        while let Some(dir) = pending.pop() {
            for entry in std::fs::read_dir(&dir).unwrap() {
                let path = entry.unwrap().path();
                if path.is_dir() {
                    // The Z3 fixtures and R0b's and R0c's own fixtures are pinned by their own
                    // tests.
                    if !path.ends_with("testdata/k/z3")
                        && !path.ends_with("testdata/k/r0b")
                        && !path.ends_with("testdata/k/r0c")
                    {
                        pending.push(path);
                    }
                } else if path.extension().is_some_and(|e| e == "k") {
                    files.push(path);
                }
            }
        }
        files.sort();
        let mut flagged = BTreeSet::new();
        let mut compiled = 0;
        for path in files {
            let name = path.strip_prefix(root()).unwrap().display().to_string();
            let text = std::fs::read_to_string(&path).unwrap();
            let module = text
                .lines()
                .filter_map(|l| l.trim().strip_prefix("module "))
                .next_back()
                .unwrap()
                .split_whitespace()
                .next()
                .unwrap()
                .to_owned();
            let validator = NativeValidator::bind(
                support::load_path(&path, &module),
                CompileOptions::default(),
            );
            let Ok(side) = validator.compile_baseline() else {
                continue;
            };
            compiled += 1;
            let exclusions = DefinitionExclusions::of_validated(
                &side,
                &k_rust::kast::identifier::encode(&module),
            )
            .unwrap();
            assert_eq!(exclusions.load_stack_stops, 0, "{name}");
            assert!(exclusions.collections_trusted(), "{name}: {exclusions:?}");
            if !exclusions.implementation_chosen.is_empty() {
                assert_eq!(
                    exclusions.definition_exclusion(),
                    Some(Exclusion::ImplementationChosenHook)
                );
                eprintln!(
                    "IMPLEMENTATION_CHOSEN {name} {:?}",
                    exclusions
                        .implementation_chosen
                        .iter()
                        .map(|reference| (&reference.sentence, &reference.hook))
                        .collect::<Vec<_>>()
                );
                flagged.insert(name);
            }
        }
        assert!(compiled > 70, "{compiled}");
        assert_eq!(
            flagged,
            [
                "testdata/k/rulecondfail.k",
                "testdata/k/t12hook.k",
                "testdata/k/t12probe.k",
                "testdata/k/t12unev.k",
            ]
            .map(str::to_owned)
            .into_iter()
            .collect::<BTreeSet<_>>()
        );
    });
}

/// Re-pin R0c deliverable 2 (the R0b reviewer's probe): a rule that applies `Base2String`, whose
/// letter case domains.md leaves to the backend, flags its definition, so every run on it is
/// excluded; before R0c the census flagged nothing and the run of `start(255)` was one complete
/// Stuck leaf `str("ff")`.
#[test]
fn a_base2string_rule_flags_the_definition() {
    on_a_big_stack(|| {
        let (side, module) = fixture("r0c", "base16");
        let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
        let [reference] = exclusions.implementation_chosen.as_slice() else {
            panic!("{exclusions:?}")
        };
        assert_eq!(reference.hook, "STRING.base2string");
        assert_eq!(reference.module, "BASE16");
        let execution = run(
            &side,
            &module,
            support::app("Lblstart", vec![support::int(255)]),
        );
        assert_eq!(
            execution
                .leaves()
                .iter()
                .map(|leaf| leaf.halt)
                .collect::<Vec<_>>(),
            [HaltClass::Stuck]
        );
        assert_eq!(
            exclusions.run_exclusion(&execution),
            Some(Exclusion::ImplementationChosenHook)
        );
    });
}

/// Decision 1: a rule that lists a map's keys flags its definition, so every run on it is
/// excluded, one that never lists keys included; a test's initial state that applies such a hook
/// flags its run; a definition that only imports MAP is not flagged.
#[test]
fn an_implementation_chosen_hook_flags_the_definition_or_the_state() {
    on_a_big_stack(|| {
        let (side, module) = r0b("implchosen");
        let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
        let [reference] = exclusions.implementation_chosen.as_slice() else {
            panic!("{exclusions:?}")
        };
        assert_eq!(reference.hook, "MAP.keys_list");
        assert_eq!(reference.module, "IMPLCHOSEN");
        assert_eq!(
            exclusions.definition_exclusion(),
            Some(Exclusion::ImplementationChosenHook)
        );
        let execution = run(
            &side,
            &module,
            support::app("Lblcount", vec![support::int(3)]),
        );
        assert_eq!(
            exclusions.run_exclusion(&execution),
            Some(Exclusion::ImplementationChosenHook)
        );

        let (free, free_module) = r0b("keysfree");
        let exclusions = DefinitionExclusions::of_validated(&free, &free_module).unwrap();
        assert!(
            exclusions.implementation_chosen.is_empty(),
            "{exclusions:?}"
        );
        assert_eq!(exclusions.definition_exclusion(), None);
        let execution = run(
            &free,
            &free_module,
            support::app("Lblstart", vec![support::int(3)]),
        );
        assert_eq!(exclusions.run_exclusion(&execution), None);
        let keys = parse_pattern(
            r#"Lblkeys{}(Lblkeys'Unds'list'LParUndsRParUnds'MAP'Unds'List'Unds'Map{}(Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1")), inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1")))))"#,
        )
        .unwrap();
        let plain = support::app("Lblstart", vec![support::int(3)]);
        let (listed, unlisted) = backend(&free, &free_module)
            .with_solver(None, |definition, _| {
                Ok::<_, k_rust::backend::BackendError>((
                    state_references_implementation_chosen(
                        definition,
                        &support::initial_state(keys.clone(), "SortProg"),
                    ),
                    state_references_implementation_chosen(
                        definition,
                        &support::initial_state(plain.clone(), "SortProg"),
                    ),
                ))
            })
            .unwrap();
        assert!(listed && !unlisted);
    });
}

/// Decision 2 (finding A-13), k-rust's tdiv/td shape: an undefined step through a `total`
/// function whose equation is undefined there names the contradicted claim, and an undefined step
/// of a `preserves-definedness` rule names that rule; both runs are excluded. An undefined step of
/// a rule that makes no claim is a complete terminal and is not excluded, nor is a defined run.
#[test]
fn an_undefined_step_that_contradicts_a_claim_excludes_the_run() {
    on_a_big_stack(|| {
        let (side, module) = r0b("tdiv");
        let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
        let catalog = backend(&side, &module).rule_catalog(None).unwrap();
        let id = |label: &str| {
            catalog
                .iter()
                .find(|rule| rule.label.as_deref() == Some(label))
                .unwrap_or_else(|| panic!("{label}"))
                .id
                .clone()
        };
        assert!(exclusions.preserves_definedness.contains(&id("TDIV.pd")));
        assert!(!exclusions.preserves_definedness.contains(&id("TDIV.half")));
        let leaf = |symbol: &str, argument: i64| {
            let execution = run(
                &side,
                &module,
                support::app(symbol, vec![support::int(argument)]),
            );
            let [leaf] = execution.leaves() else {
                panic!("{symbol}({argument}): {execution:?}")
            };
            (leaf.clone(), exclusions.run_exclusion(&execution))
        };
        let (td, excluded) = leaf("Lbltdiv", -1);
        assert_eq!(td.halt, HaltClass::Trivial);
        let contradicted = td.contradicted_total.as_ref().expect("names the claim");
        assert_eq!(contradicted.symbol, "Lbltd");
        assert_eq!(contradicted.rule_id, id("TDIV.tdeq"));
        assert_eq!(excluded, Some(Exclusion::ContradictedClaim));
        let (pd, excluded) = leaf("Lblpd", -1);
        assert_eq!(pd.halt, HaltClass::Trivial);
        assert_eq!(pd.contradicted_total, None);
        assert_eq!(
            pd.undefined_rule.as_ref().map(|rule| &rule.id),
            Some(&id("TDIV.pd"))
        );
        assert_eq!(excluded, Some(Exclusion::ContradictedClaim));
        let (half, excluded) = leaf("Lblhalf", 0);
        assert_eq!(half.halt, HaltClass::Trivial);
        assert_eq!(
            half.undefined_rule.as_ref().map(|rule| &rule.id),
            Some(&id("TDIV.half"))
        );
        assert_eq!(excluded, None);
        for (symbol, argument) in [("Lbltdiv", 0), ("Lblpd", 0)] {
            let (defined, excluded) = leaf(symbol, argument);
            assert_eq!(defined.halt, HaltClass::Stuck, "{symbol}");
            assert_eq!(excluded, None, "{symbol}");
        }
    });
}

/// Finding C-10: an equation rooted at a collection role symbol (reported by the load as
/// `IndexedAt(List)`) or a simplification rooted at one (which the load does not report) makes no
/// collection term of the definition a terminal value; without the flag the same decider gives
/// the canonical value.
#[test]
fn an_axiom_rooted_at_a_role_symbol_distrusts_collection_terminals() {
    on_a_big_stack(|| {
        for (name, element) in [("rolerooted", "LblListItem"), ("rolesimp", "LblSetItem")] {
            let (side, module) = r0b(name);
            let exclusions = DefinitionExclusions::of_validated(&side, &module).unwrap();
            assert!(!exclusions.collections_trusted(), "{name}: {exclusions:?}");
            assert_eq!(exclusions.definition_exclusion(), None, "{name}");
            let execution = run(
                &side,
                &module,
                support::app("Lblstart", vec![support::int(5)]),
            );
            assert_eq!(exclusions.run_exclusion(&execution), None, "{name}");
            let [leaf] = execution.leaves() else {
                panic!("{name}: {execution:?}")
            };
            let state = k_rust::kore::codec::from_value(&leaf.branch.state).unwrap();
            let term = match &state {
                Pattern::And { arguments, .. } => arguments[0].clone(),
                term => term.clone(),
            };
            assert!(format!("{term:?}").contains(element), "{name}: {term:?}");
            let initial =
                support::initial_state(support::app("Lblstart", vec![support::int(5)]), "SortProg");
            backend(&side, &module)
                .with_solver(None, |definition, solver| {
                    let trusted = ObservationDecider::new(
                        definition,
                        solver,
                        TestInitialState::of_test(&initial),
                    );
                    assert!(trusted.terminal_value(&term).is_some(), "{name}");
                    let distrusted = ObservationDecider::new(
                        definition,
                        solver,
                        TestInitialState::of_test(&initial),
                    )
                    .trusting_collections(exclusions.collections_trusted());
                    assert_eq!(distrusted.terminal_value(&term), None, "{name}");
                    Ok::<_, k_rust::backend::BackendError>(())
                })
                .unwrap();
        }
    });
}

/// `deep(N)` recurses `N` levels, not in tail position (k-rust tests/execution_stack_stops.rs).
const DEEP: &str = r#"[] module MAIN
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    hooked-symbol subInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.sub"), smt-hook{}("-")]
    hooked-symbol addInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
    hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
    symbol deep{}(SortInt{}) : SortInt{} [function{}(), total{}()]
    sort SortS{} []
    symbol done{}(SortInt{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
    axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, \dv{SortInt{}}("0")), \top{R}())), \equals{SortInt{}, R}(deep{}(X0:SortInt{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))) []
    axiom{R} \implies{R}(\and{R}(\equals{SortBool{}, R}(gtInt{}(VarN:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarN:SortInt{}), \top{R}())), \equals{SortInt{}, R}(deep{}(X0:SortInt{}), \and{SortInt{}}(addInt{}(deep{}(subInt{}(VarN:SortInt{}, \dv{SortInt{}}("1"))), \dv{SortInt{}}("1")), \top{SortInt{}}()))) []
endmodule []"#;

/// Finding A-06: a run that met a stop for lack of native stack reports it (`stackStops`), both
/// adapter entry points keep the count, and the run is excluded; the same run with the default
/// stack budget reports none and is not excluded.
#[test]
fn a_run_with_a_stack_stop_is_excluded() {
    let result = |stack_budget: Option<usize>| {
        std::thread::Builder::new()
            .stack_size(8 << 20)
            .spawn(move || {
                let mut backend = Backend::new(DEEP, "MAIN", BackendOptions::default()).unwrap();
                if let Some(stack_budget) = stack_budget {
                    backend.set_simplification_stack_budget(stack_budget);
                }
                let state = parse_pattern(r#"done{}(deep{}(\dv{SortInt{}}("30000")))"#).unwrap();
                let bounds = ExecutionBudget {
                    max_depth: Some(0),
                    ..budget()
                };
                let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
                let unobserved = adapter
                    .execute_unobserved(&mut backend, &state, bounds)
                    .unwrap();
                let adapted = adapter.execute(&mut backend, &state, bounds).unwrap();
                (unobserved.stack_stops, adapted)
            })
            .unwrap()
            .join()
            .unwrap()
    };
    let (unobserved, stopped) = result(Some(0));
    assert!(unobserved >= 1 && stopped.stack_stops() >= 1, "{stopped:?}");
    assert_eq!(
        DefinitionExclusions::default().run_exclusion(&stopped),
        Some(Exclusion::StackStop)
    );
    let (unobserved, clean) = result(None);
    assert_eq!((unobserved, clean.stack_stops()), (0, 0));
    assert_eq!(DefinitionExclusions::default().run_exclusion(&clean), None);
}

/// k-rust's confluence_budget fixture (k-rust-backend tests/backend/confluence_budget.rs): a
/// partial `p` with the ceil equation `\ceil(p(X)) = (hk(n) == n)` and the rewrite rule
/// `state => done(p(0))`, whose definedness the load discharges by simplifying `hk(n) == n`, which
/// recurses `n` levels.
fn partial_definition(n: u64) -> String {
    let int = |value: u64| format!(r#"\dv{{SortInt{{}}}}("{value}")"#);
    let equation = |pattern: &str, right: &str, requires: &str| {
        format!(
            r"axiom{{R}} \implies{{R}}(\and{{R}}({requires}, \and{{R}}(\in{{SortInt{{}}, R}}(X0:SortInt{{}}, {pattern}), \top{{R}}())), \equals{{SortInt{{}}, R}}(hk{{}}(X0:SortInt{{}}), \and{{SortInt{{}}}}({right}, \top{{SortInt{{}}}}()))) []"
        )
    };
    let axioms = [
        equation(&int(0), &int(0), r"\top{R}()"),
        equation(
            "VarN:SortInt{}",
            &format!(
                "addInt{{}}(hk{{}}(subInt{{}}(VarN:SortInt{{}}, {})), {})",
                int(1),
                int(1)
            ),
            &format!(
                r#"\equals{{SortBool{{}}, R}}(gtInt{{}}(VarN:SortInt{{}}, {}), \dv{{SortBool{{}}}}("true"))"#,
                int(0)
            ),
        ),
        format!(
            r"axiom{{R}} \implies{{R}}(\top{{R}}(), \equals{{R, R}}(\ceil{{SortInt{{}}, R}}(p{{}}(X:SortInt{{}})), \equals{{SortInt{{}}, R}}(hk{{}}({}), {}))) []",
            int(n),
            int(n)
        ),
        r#"axiom{} \rewrites{SortS{}}(\and{SortS{}}(state{}(), \top{SortS{}}()), done{}(p{}(\dv{SortInt{}}("0")))) [label{}("advance")]"#.to_owned(),
    ];
    format!(
        r#"[] module MAIN
    hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
    hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
    hooked-symbol subInt{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
        [function{{}}(), total{{}}(), hook{{}}("INT.sub"), smt-hook{{}}("-")]
    hooked-symbol addInt{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
        [function{{}}(), total{{}}(), hook{{}}("INT.add"), smt-hook{{}}("+")]
    hooked-symbol gtInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
        [function{{}}(), total{{}}(), hook{{}}("INT.gt"), smt-hook{{}}(">")]
    hooked-symbol eqInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
        [function{{}}(), total{{}}(), hook{{}}("INT.eq"), smt-hook{{}}("=")]
    hooked-symbol hk{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), hook{{}}("MYHOOK.hk")]
    symbol p{{}}(SortInt{{}}) : SortInt{{}} [function{{}}()]
    sort SortS{{}} []
    symbol state{{}}() : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
    symbol done{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
    {}
endmodule []"#,
        axioms.join("\n    ")
    )
}

/// Finding A-08: a load whose discharge of rewrite-rule definedness runs out of stack counts the
/// stop, read through `select_definition` on the backend, and excludes every run on it; a shallow
/// discharge on the same thread counts nothing.
#[test]
fn a_load_with_a_stack_stop_excludes_every_run() {
    let exclusions = |n: u64| {
        std::thread::Builder::new()
            .stack_size(8 << 20)
            .spawn(move || {
                let kore = parse_definition(&partial_definition(n)).unwrap();
                with_simplification_stack_budget(0, || {
                    let mut backend =
                        Backend::from_definition(kore.clone(), "MAIN", BackendOptions::default())
                            .unwrap();
                    let selected = backend.select_definition(None).unwrap();
                    DefinitionExclusions::of(&kore, &selected, &[])
                })
            })
            .unwrap()
            .join()
            .unwrap()
    };
    let deep = exclusions(100_000);
    assert!(deep.load_stack_stops >= 1, "{deep:?}");
    assert_eq!(deep.definition_exclusion(), Some(Exclusion::LoadStackStop));
    let shallow = exclusions(100);
    assert_eq!(shallow.load_stack_stops, 0);
    assert_eq!(shallow.definition_exclusion(), None);
}

/// Decision 4 / finding C-09: census rule C stays exercised by a definition k-rust 501f18b9
/// compiles: a well-sorted List whose role symbols carry no role hook is flagged under rule C for
/// each of its three roles, so kink-corpus admission refuses it (`vi-t13`).
#[test]
fn a_compiling_hookless_role_is_refused_by_census_rule_c() {
    on_a_big_stack(|| {
        let (side, _) = r0b("hooklessrole");
        let census = kink_native::declaration_census(&side).unwrap();
        assert_eq!(census.verdict(), kink_native::CensusVerdict::Flagged);
        let findings = census
            .findings()
            .iter()
            .map(|finding| (finding.class, finding.symbol.clone()))
            .collect::<Vec<_>>();
        eprintln!("HOOKLESS {}", census.text());
        assert_eq!(findings.len(), 3, "{}", census.text());
        assert!(
            findings
                .iter()
                .all(|(class, _)| *class == kink_native::CensusClass::C),
            "{}",
            census.text()
        );
    });
}

/// A hooked division: partial with the ceil equation `\ceil(mydiv(X, Y)) = (Y =/= 0)`, or
/// declared `total`.
fn division(total: bool) -> String {
    format!(
        r#"[] module MAIN
    hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
    hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
    hooked-symbol mydiv{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}} [function{{}}(), {}hook{{}}("INT.tdiv"), smt-hook{{}}("div")]
    sort SortS{{}} []
    symbol done{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
    {}
endmodule []"#,
        if total { "total{}(), " } else { "" },
        if total {
            ""
        } else {
            r#"axiom{R} \implies{R}(\top{R}(), \equals{R, R}(\ceil{SortInt{}, R}(mydiv{}(X:SortInt{}, Y:SortInt{})), \not{R}(\equals{SortInt{}, R}(Y:SortInt{}, \dv{SortInt{}}("0"))))) []"#
        }
    )
}

/// Re-pin R0b deliverable 5 (finding A-12): since 501f18b9 k-rust's admission restates a
/// pattern's definedness from the admitting definition. A mutant that declares a partial hooked
/// division `total` can leave a leaf `done(X) /\ mydiv(X, 0) = 1`. Admitted under the baseline,
/// whose ceil equation makes `mydiv(X, 0)` undefined, the leaf gains the conjunct `false`, and
/// with Z3 it is refuted (`Unsat`, so the mutant leaf would be discarded) although the mutant has
/// instances of it. The decider for a mutant's leaves decides their feasibility on the mutant's
/// own definition, where the leaf is not refuted; the baseline's own leaves are still decided on
/// the baseline. Without a solver neither is decided.
#[test]
fn a_mutant_leaf_is_admitted_under_the_mutant_definition() {
    use kink_native::feasibility::LeafFeasibility;
    let state = k_rust::kore::codec::to_value(
        &parse_pattern(
            r#"\and{SortS{}}(done{}(VarX:SortInt{}), \equals{SortInt{}, SortS{}}(mydiv{}(VarX:SortInt{}, \dv{SortInt{}}("0")), \dv{SortInt{}}("1")))"#,
        )
        .unwrap(),
    )
    .unwrap();
    let mut baseline = Backend::new(&division(false), "MAIN", BackendOptions::default()).unwrap();
    let mut mutant = Backend::new(&division(true), "MAIN", BackendOptions::default()).unwrap();
    let initial = parse_pattern("done{}(VarX:SortInt{})").unwrap();
    let (own, shared) = baseline
        .with_solver(None, |definition, solver| {
            let own =
                ObservationDecider::new(definition, solver, TestInitialState::of_test(&initial))
                    .shared_leaf_feasibility(&state);
            let shared = mutant.with_solver(None, |leaf_definition, leaf_solver| {
                Ok::<_, k_rust::backend::BackendError>(
                    ObservationDecider::for_leaves_of(
                        definition,
                        leaf_definition,
                        leaf_solver,
                        TestInitialState::of_test(&initial),
                    )
                    .shared_leaf_feasibility(&state),
                )
            })?;
            Ok::<_, k_rust::backend::BackendError>((own, shared))
        })
        .unwrap();
    if SolverProfile::BUILD == SolverProfile::Z3 {
        assert_eq!(own, LeafFeasibility::Unsat);
        assert_ne!(shared, LeafFeasibility::Unsat, "{shared:?}");
    } else {
        assert_eq!(
            (own, shared),
            (LeafFeasibility::Unknown, LeafFeasibility::Unknown)
        );
    }
}
