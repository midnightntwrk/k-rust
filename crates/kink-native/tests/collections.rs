//! CS-16 N1-N12: terminal collection values; the boolean bridge and feasibility stay unchanged.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::{collections::BTreeMap, path::Path, time::Duration};

use k_rust::{
    backend::{Backend, BackendError, BackendOptions},
    kast::Sort,
    kompile::{
        CompileOptions,
        initial_configuration::{
            ConfigurationAssembler, ConfigurationError, ProgramGrammar, kore_application,
            kore_sort, program_start_position,
        },
    },
    kore::{ast::Pattern, codec::from_value, parser::parse_definition},
};
use k_rust_backend::{definition::BackendDefinition, term::CollectionMetadata};
use kink_native::{
    CensusClass, CensusVerdict, NativeValidator, ValidatedDefinition,
    bridge::{BridgeContext, paths_from_execution, paths_from_execution_values},
    declaration_census,
    execution::{ExecutionAdapter, ExecutionBudget, HaltClass, SolverProfile},
    feasibility::{LeafFeasibility, TestInitialState},
    step_events::ObservationDecider,
};
use kink_pattern::{ExecutionTerminalKind, PathStop, SymbolSorts};

const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(120),
    max_simplification_iterations: 10_000,
    max_depth: Some(200),
    max_breadth: None,
};

struct Fixture {
    validator: NativeValidator,
    compiled: ValidatedDefinition,
    syntax: String,
    depth: u64,
}

impl Fixture {
    fn new(file: &str, main: &str, syntax: &str) -> Self {
        let validator = NativeValidator::bind(
            support::load_path(&Path::new(support::DIR).join(file), main),
            CompileOptions::default(),
        );
        let compiled = validator.compile_baseline().expect("fixture compiles");
        Self {
            validator,
            compiled,
            syntax: syntax.to_owned(),
            depth: 200,
        }
    }

    fn backend(&self) -> Backend {
        Backend::new(
            &self.compiled.artifacts().definition_kore,
            k_rust::kast::identifier::encode(&self.compiled.definition().main_module),
            BackendOptions::default(),
        )
        .expect("backend")
    }

    /// The same ProgramGrammar/ConfigurationAssembler route as kink-corpus input.rs.
    fn input(&self, text: &str, sort: Option<&str>) -> Pattern {
        let grammar = ProgramGrammar::new(self.validator.baseline().definition()).expect("grammar");
        let variables = &self.compiled.artifacts().configuration_variables;
        let start = sort.map_or_else(
            || program_start_position(variables.get("PGM").unwrap_or(&Sort::new("KItem"))),
            Sort::new,
        );
        let mut assembler = ConfigurationAssembler::new(
            &grammar,
            &self.validator.baseline().definition().main_module,
            &self.syntax,
            variables,
        );
        assembler.program(&start, text).expect("program parses");
        assembler
            .bind_stream_defaults::<ConfigurationError>(false, false, || Ok(Vec::new()))
            .expect("streams");
        assembler.finish().expect("input assembled")
    }
}

fn normal(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Normal
}

/// N1, N2, N4, N5, N7 (executed repeats), N10, N11 and N12.
fn execute_rows(
    fixture: &Fixture,
    rows: &[(&str, &str, bool, PathStop)],
) -> BTreeMap<String, Pattern> {
    let sorts = SymbolSorts::from_definition(
        &parse_definition(&fixture.compiled.artifacts().definition_kore).expect("KORE"),
    );
    let mut backend = fixture.backend();
    let mut terminals = BTreeMap::new();
    for &(id, program, accepted, stop) in rows {
        let initial = fixture.input(program, None);
        kink_native::bridge::validate_test_initial_state(&mut backend, &initial)
            .expect("concrete input admitted");
        let execution = ExecutionAdapter::with_profile(SolverProfile::BUILD)
            .execute(
                &mut backend,
                &initial,
                ExecutionBudget {
                    max_depth: Some(fixture.depth),
                    ..BUDGET
                },
            )
            .expect("execution");
        assert!(!execution.timed_out(), "STOP {id}: timeout");
        let context = BridgeContext {
            test_id: id,
            classify: &normal,
            sorts: &sorts,
        };
        backend
            .with_solver(None, |definition, solver| {
                let decider = ObservationDecider::new(
                    definition,
                    solver,
                    TestInitialState::of_test(&initial),
                );
                let old = paths_from_execution(&execution, &context, &|term| {
                    decider.definition_independent(term)
                })
                .expect("boolean bridge");
                let identity = paths_from_execution_values(&execution, &context, &|term| {
                    decider.definition_independent(term).then(|| term.clone())
                })
                .expect("identity bridge");
                assert_eq!(old, identity, "N12 {id}: boolean closure keeps its results");
                assert!(
                    old.paths
                        .iter()
                        .all(|path| !path.complete && path.stop == PathStop::SolverUnknown),
                    "{id}: old collection paths"
                );
                let new = paths_from_execution_values(&execution, &context, &|term| {
                    decider.terminal_value(term)
                })
                .expect("value bridge");
                assert!(!new.paths.is_empty(), "{id}: no path");
                if id == "sum3" {
                    assert_eq!(new.paths.len(), 64, "N1 IMP sum n=3 path count");
                    assert_eq!(
                        new.paths
                            .iter()
                            .filter_map(|path| path
                                .execution_terminal
                                .as_ref()
                                .map(|terminal| &terminal.state))
                            .collect::<std::collections::BTreeSet<_>>()
                            .len(),
                        1,
                        "N1 IMP distinct terminals"
                    );
                }
                assert!(
                    new.paths.iter().all(|path| path.complete == accepted
                        && path.stop == stop
                        && path.execution_terminal.is_some() == accepted),
                    "STOP {id}: {new:?}"
                );
                for leaf in execution.leaves() {
                    let raw = from_value(&leaf.branch.state).expect("leaf KORE");
                    assert!(
                        !decider.definition_independent(&raw),
                        "{id}: collection independent before"
                    );
                    assert_eq!(
                        leaf.feasibility,
                        LeafFeasibility::Unknown,
                        "N10 {id}: feasibility changed"
                    );
                    let value = decider.terminal_value(&raw);
                    assert_eq!(
                        value,
                        accepted.then(|| raw.clone()),
                        "STOP N1/N4/N5 {id}: canonical bytes or acceptance changed"
                    );
                    if leaf.halt == HaltClass::Stuck {
                        terminals.insert(id.to_owned(), raw);
                    }
                }
                if matches!(id, "fkey1" | "fval1") {
                    assert_eq!(execution.leaves().len(), 2, "N4 residue leaves");
                    assert!(
                        execution
                            .leaves()
                            .iter()
                            .any(|leaf| leaf.halt == HaltClass::Trivial)
                    );
                    assert!(
                        execution
                            .leaves()
                            .iter()
                            .any(|leaf| leaf.halt == HaltClass::Stuck)
                    );
                }
                if stop == PathStop::UndefinedStep {
                    assert!(
                        execution
                            .leaves()
                            .iter()
                            .all(|leaf| leaf.halt == HaltClass::Trivial),
                        "N7 {id}: repeated construction is an undefined step"
                    );
                }
                Ok::<_, BackendError>(())
            })
            .expect("solver");
    }
    terminals
}

#[test]
fn natural_collection_terminals_and_bridge_rows() {
    let store = Fixture::new("collstore.k", "COLLSTORE", "COLLSTORE-SYNTAX");
    let t = PathStop::Terminal;
    let u = PathStop::UndefinedStep;
    let s = PathStop::SolverUnknown;
    let terms = execute_rows(
        &store,
        &[
            ("put1", "put(1, 10)", true, t),
            ("put21", "seq(put(2, 20), put(1, 10))", true, t),
            ("put12", "seq(put(1, 10), put(2, 20))", true, t),
            ("two", "putTwo(1, 10, 2, 20)", true, t),
            ("tworev", "putTwoRev(1, 10, 2, 20)", true, t),
            ("put10", "seq(put(10, 1), put(9, 1))", true, t),
            ("set21", "seq(addSet(2), addSet(1))", true, t),
            ("set12", "seq(addSet(1), addSet(2))", true, t),
            ("list21", "seq(logList(2), logList(1))", true, t),
            ("list12", "seq(logList(1), logList(2))", true, t),
            ("fkey0", "fKey(0)", true, t),
            ("nest", "nest(3)", true, t),
            ("halt", "halt()", true, t),
            ("clear", "seq(put(1, 10), clear())", true, t),
            ("fkey1", "fKey(1)", false, s),
            ("fval1", "fVal(1)", false, s),
            ("byteskey", "bytesKey(\"a\")", false, s),
            ("dupkey", "seq(put(1, 10), dupKey(1))", true, u),
            ("dupkeysame", "seq(put(1, 1), dupKey(1))", true, u),
            ("dupelem", "seq(addSet(1), dupElem(1))", true, u),
        ],
    );
    for id in ["put12", "two", "tworev"] {
        assert_eq!(terms["put21"], terms[id], "N2 {id}");
    }
    assert_eq!(terms["set21"], terms["set12"], "N2 Set order");
    assert_ne!(terms["list21"], terms["list12"], "N2 List order");
    let cell = Fixture::new("cellmap.k", "CELLMAP", "CELLMAP-SYNTAX");
    assert_eq!(
        declaration_census(&cell.compiled)
            .expect("census")
            .verdict(),
        CensusVerdict::Natural
    );
    let terms = execute_rows(
        &cell,
        &[
            ("open21", "seq(open(2, 20), open(1, 10))", true, t),
            ("open12", "seq(open(1, 10), open(2, 20))", true, t),
            ("opendup", "seq(open(1, 10), open(1, 11))", true, u),
        ],
    );
    assert_eq!(terms["open21"], terms["open12"], "N2 cell map order");
    let imp = Fixture::new("collimp.k", "COLLIMP", "COLLIMP-SYNTAX");
    execute_rows(
        &imp,
        &[("sum", "var x ; var y ; x = 1 + 2 ; y = x + x ;", true, t)],
    );
}

#[test]
fn b1_non_natural_role_is_not_a_terminal_value() {
    let fixture = Fixture::new("b1coll.k", "B1COLL", "B1COLL-SYNTAX");
    let census = declaration_census(&fixture.compiled).expect("census");
    assert_eq!(census.verdict(), CensusVerdict::Flagged, "N6");
    let roles: std::collections::BTreeSet<_> = census
        .findings()
        .iter()
        .filter(|finding| finding.class == CensusClass::C)
        .map(|finding| finding.symbol.as_str())
        .collect();
    let expected: std::collections::BTreeSet<_> = [".LI", "_LI_", "mkFoo"]
        .map(|name| format!("Lbl{}", k_rust::kast::identifier::encode(name)))
        .into_iter()
        .collect();
    assert_eq!(
        roles,
        expected.iter().map(String::as_str).collect(),
        "N6 B1 role census"
    );
    execute_rows(
        &fixture,
        &[("start1", "start(1)", false, PathStop::SolverUnknown)],
    );
}

fn at<'a>(term: &'a Pattern, path: &[usize]) -> &'a Pattern {
    path.iter().fold(term, |term, &index| match term {
        Pattern::Application { arguments, .. } => &arguments[index],
        _ => panic!("application path"),
    })
}

fn replaced(term: &Pattern, path: &[usize], value: Pattern) -> Pattern {
    if path.is_empty() {
        return value;
    }
    let Pattern::Application { symbol, arguments } = term else {
        panic!("application path")
    };
    let mut arguments = arguments.clone();
    arguments[path[0]] = replaced(&arguments[path[0]], &path[1..], value);
    Pattern::Application {
        symbol: symbol.clone(),
        arguments,
    }
}

fn find_collection(
    definition: &BackendDefinition,
    term: &Pattern,
    namespace: &str,
    path: &mut Vec<usize>,
) -> Option<Vec<usize>> {
    let Pattern::Application { symbol, arguments } = term else {
        return None;
    };
    if definition
        .symbols()
        .get(symbol.name.as_str())
        .is_some_and(|symbol| {
            symbol.attributes.collection.is_some()
                && symbol.attributes.hook.as_deref() == Some(namespace)
        })
    {
        return Some(path.clone());
    }
    for (index, argument) in arguments.iter().enumerate() {
        path.push(index);
        let found = find_collection(definition, argument, namespace, path);
        path.pop();
        if found.is_some() {
            return found;
        }
    }
    None
}

fn elements(term: &Pattern, unit: &str, concat: &str, out: &mut Vec<Pattern>) {
    let Pattern::Application { symbol, arguments } = term else {
        panic!("collection application")
    };
    if symbol.name == unit {
        assert!(arguments.is_empty());
    } else if symbol.name == concat {
        for argument in arguments {
            elements(argument, unit, concat, out);
        }
    } else {
        out.push(term.clone());
    }
}

#[test]
fn collection_permutations_repeats_and_position_rows() {
    let fixture = Fixture::new("collstore.k", "COLLSTORE", "COLLSTORE-SYNTAX");
    let mut backend = fixture.backend();
    // Three entries make the left-nested and right-nested shapes observably different.
    let initial = fixture.input("seq(put(1, 10), seq(put(2, 20), seq(put(3, 30), seq(addSet(1), seq(addSet(2), seq(addSet(3), seq(logList(1), logList(2))))))))", Some("Prog"));
    let execution = ExecutionAdapter::with_profile(SolverProfile::BUILD)
        .execute(&mut backend, &initial, BUDGET)
        .expect("execution");
    assert!(!execution.timed_out());
    assert_eq!(execution.leaves().len(), 1);
    let raw = from_value(&execution.leaves()[0].branch.state).expect("leaf KORE");
    backend
        .with_solver(None, |definition, solver| {
            let decider =
                ObservationDecider::new(definition, solver, TestInitialState::of_test(&initial));
            assert_eq!(decider.terminal_value(&raw), Some(raw.clone()));
            let mut map_element = None;
            for namespace in ["MAP.concat", "SET.concat", "LIST.concat"] {
                let path = find_collection(definition, &raw, namespace, &mut Vec::new())
                    .expect("collection");
                let collection = at(&raw, &path);
                let Pattern::Application { symbol, .. } = collection else {
                    unreachable!()
                };
                let metadata = definition
                    .symbols()
                    .get(symbol.name.as_str())
                    .unwrap()
                    .attributes
                    .collection
                    .as_ref()
                    .unwrap();
                let symbols = match metadata {
                    CollectionMetadata::Map(d) => &d.symbols,
                    CollectionMetadata::List(d) | CollectionMetadata::Set(d) => &d.symbols,
                };
                let cat = |a, b| support::app(&symbols.concat, vec![a, b]);
                let unit = || support::app(&symbols.unit, vec![]);
                let mut entries = Vec::new();
                elements(collection, &symbols.unit, &symbols.concat, &mut entries);
                let reversed = entries.iter().rev().cloned().reduce(&cat).unwrap();
                let reversed_term = replaced(&raw, &path, reversed);
                if namespace == "LIST.concat" {
                    assert_eq!(
                        decider.terminal_value(&reversed_term),
                        Some(reversed_term.clone()),
                        "N3 reversed List preserves its order"
                    );
                    assert_ne!(reversed_term, raw, "N3 List order matters");
                    continue;
                }
                assert_eq!(
                    decider.terminal_value(&reversed_term),
                    Some(raw.clone()),
                    "N3 reversed {namespace}"
                );
                let left_nested = entries.iter().cloned().reduce(&cat).unwrap();
                assert_eq!(
                    decider.terminal_value(&replaced(&raw, &path, left_nested)),
                    Some(raw.clone()),
                    "N3 left-nested {namespace}"
                );
                let interleaved = entries
                    .iter()
                    .cloned()
                    .map(|element| cat(unit(), cat(element, unit())))
                    .reduce(&cat)
                    .unwrap();
                assert_eq!(
                    decider.terminal_value(&replaced(&raw, &path, interleaved)),
                    Some(raw.clone()),
                    "N3 units {namespace}"
                );
                let one = replaced(&raw, &path, entries[0].clone());
                assert_eq!(
                    decider.terminal_value(&replaced(&raw, &path, cat(entries[0].clone(), unit()))),
                    Some(one),
                    "N3 single element with unit"
                );
                let repeat = cat(entries[0].clone(), entries[0].clone());
                assert_eq!(
                    decider.terminal_value(&replaced(&raw, &path, repeat)),
                    None,
                    "N7 equal repeat {namespace}"
                );
                assert_eq!(
                    decider.terminal_value(collection),
                    None,
                    "N8 top-level collection {namespace}"
                );
                if namespace == "MAP.concat" {
                    map_element = Some(entries[0].clone());
                    let Pattern::Application { symbol, arguments } = &entries[0] else {
                        unreachable!()
                    };
                    let mut changed = arguments.clone();
                    changed[1] = arguments[0].clone();
                    let different_value = Pattern::Application {
                        symbol: symbol.clone(),
                        arguments: changed,
                    };
                    assert_eq!(
                        decider.terminal_value(&replaced(
                            &raw,
                            &path,
                            cat(entries[0].clone(), different_value)
                        )),
                        None,
                        "N7 same key different value"
                    );
                    let mut variable_key = arguments.clone();
                    variable_key[0] = support::var("X", "SortKItem");
                    assert_eq!(
                        decider.terminal_value(&replaced(
                            &raw,
                            &path,
                            Pattern::Application {
                                symbol: symbol.clone(),
                                arguments: variable_key
                            }
                        )),
                        None,
                        "N8 variable key"
                    );
                    assert_eq!(
                        decider.terminal_value(&replaced(
                            &raw,
                            &path,
                            cat(entries[0].clone(), support::var("M", "SortMap"))
                        )),
                        None,
                        "N8 variable rest"
                    );
                }
            }
            let map_element = map_element.unwrap();
            let list_path =
                find_collection(definition, &raw, "LIST.concat", &mut Vec::new()).unwrap();
            assert_eq!(
                decider.terminal_value(&replaced(&raw, &list_path, map_element.clone())),
                None,
                "N8 Map under List cell"
            );
            let set_path =
                find_collection(definition, &raw, "SET.concat", &mut Vec::new()).unwrap();
            let Pattern::Application { symbol, arguments } = at(&raw, &set_path) else {
                unreachable!()
            };
            let mixed = Pattern::Application {
                symbol: symbol.clone(),
                arguments: vec![map_element, arguments[1].clone()],
            };
            assert_eq!(
                decider.terminal_value(&replaced(&raw, &set_path, mixed)),
                None,
                "N8 Set with Map component"
            );
            Ok::<_, BackendError>(())
        })
        .expect("solver");
}

fn inj(from: &str, to: &str, value: Pattern) -> Pattern {
    kore_application("inj", vec![kore_sort(from), kore_sort(to)], vec![value])
}

#[test]
fn collection_free_tv01_fix1_and_stuck_terminals_keep_exact_values() {
    let fixture = Fixture::new("unbound.k", "TV01TERMINAL", "TV01TERMINAL");
    let seven = || support::int(7);
    let done = |value| support::app("Lbldone", vec![value]);
    let check = |value| support::app("Lblcheck", vec![value]);
    let wrap = |value| support::app("Lblwrap", vec![value]);
    // Every TV01-FIX1 row, including the term checked separately beneath kseq.
    let nested = inj("SortVal", "SortKItem", inj("SortInt", "SortVal", seven()));
    let rows = [
        ("strict", done(inj("SortInt", "SortVal", seven()))),
        ("strict-ctor", done(wrap(seven()))),
        (
            "strict-var",
            done(inj("SortInt", "SortVal", support::var("X", "SortInt"))),
        ),
        ("canonical-check", check(seven())),
        ("identity", check(inj("SortInt", "SortInt", seven()))),
        (
            "identity-under-strict",
            done(inj(
                "SortInt",
                "SortVal",
                inj("SortInt", "SortInt", seven()),
            )),
        ),
        (
            "identity-val",
            done(inj("SortVal", "SortVal", wrap(seven()))),
        ),
        ("reversed", check(inj("SortVal", "SortInt", wrap(seven())))),
        (
            "ill-sorted-dv",
            done(inj(
                "SortInt",
                "SortVal",
                Pattern::DomainValue {
                    sort: kore_sort("SortBool"),
                    value: "true".into(),
                },
            )),
        ),
        (
            "ill-sorted-ctor",
            done(inj("SortInt", "SortVal", wrap(seven()))),
        ),
        (
            "ill-sorted-var",
            done(inj("SortInt", "SortVal", support::var("V", "SortVal"))),
        ),
        ("nested", nested.clone()),
        (
            "nested-state",
            support::initial_state(
                support::app("Lblhold", vec![support::app("LblListItem", vec![nested])]),
                "SortProg",
            ),
        ),
        (
            "bridge-identity",
            support::initial_state(check(inj("SortInt", "SortInt", seven())), "SortProg"),
        ),
        (
            "bridge-canonical",
            support::initial_state(check(support::int(3)), "SortProg"),
        ),
    ];
    let mut backend = fixture.backend();
    for (id, term) in rows {
        backend
            .with_solver(None, |definition, solver| {
                let decider =
                    ObservationDecider::new(definition, solver, TestInitialState::of_test(&term));
                assert_eq!(
                    decider.terminal_value(&term),
                    decider.definition_independent(&term).then(|| term.clone()),
                    "STOP N9 TV01-FIX1 {id}"
                );
                Ok::<_, BackendError>(())
            })
            .expect("solver");
    }
    let z = || support::app("Lblz", vec![]);
    let s = |p| support::app("Lbls", vec![p]);
    let rows = [
        (
            "counter.k",
            "COUNTER",
            support::initial_state(
                support::app("Lblcounter", vec![z(), s(s(s(z())))]),
                "SortCounter",
            ),
        ),
        (
            "guardeddiv.k",
            "GUARDEDDIV",
            support::initial_state(
                support::app("Lbldivide", vec![support::int(10), support::int(2)]),
                "SortProg",
            ),
        ),
    ];
    for (file, main, initial) in rows {
        let fixture = Fixture::new(file, main, main);
        let mut backend = fixture.backend();
        let execution = ExecutionAdapter::with_profile(SolverProfile::BUILD)
            .execute(&mut backend, &initial, BUDGET)
            .expect("execution");
        assert!(!execution.timed_out());
        assert_eq!(execution.leaves().len(), 1);
        assert_eq!(execution.leaves()[0].halt, HaltClass::Stuck);
        let raw = from_value(&execution.leaves()[0].branch.state).expect("leaf KORE");
        backend
            .with_solver(None, |definition, solver| {
                let decider = ObservationDecider::new(
                    definition,
                    solver,
                    TestInitialState::of_test(&initial),
                );
                assert!(decider.definition_independent(&raw));
                assert_eq!(
                    decider.terminal_value(&raw),
                    Some(raw.clone()),
                    "STOP N9 {main} terminal bytes"
                );
                Ok::<_, BackendError>(())
            })
            .expect("solver");
    }
}

/// N1 external rows use the same read-only opt-in convention as corpus external.rs.
#[test]
#[ignore = "external read-only collection rows; requires KINK_WORKSPACE"]
fn external_panopticon_and_imp_terminal_values() {
    let Some(workspace) = std::env::var_os("KINK_WORKSPACE") else {
        eprintln!("CS16 N1 external rows skipped: KINK_WORKSPACE unset");
        return;
    };
    std::thread::Builder::new().stack_size(256 << 20).spawn(move || {
        let workspace = std::path::PathBuf::from(workspace);
        for (directory, entry, main, syntax, depth, programs) in [
            ("panopticon/K/spec", "panopticon-semantics.md", "PANOPTICON-SEMANTICS", "PANOPTICON-SYNTAX", 100, vec![
                ("let1", "let x : int = 1 ; x", true, PathStop::Terminal),
                ("shadow", "let x : int = 1 ; let x : bool = true ; x", true, PathStop::Terminal),
                ("const", "42", true, PathStop::Terminal),
            ]),
            ("inspirations/runtimeverification/k/k-distribution/tests/regression-new/pl-tutorial/1_k/2_imp/lesson_4", "imp.k", "IMP", "IMP-SYNTAX", 1000, vec![
                ("sum3", "int n, sum; n = 3; sum = 0; while (!(n <= 0)) { sum = sum + n; n = n + -1; }", true, PathStop::Terminal),
            ]),
        ] {
            let root = workspace.join(directory);
            // Source names remain relative, and no external source is written.
            let mut resolver = |current: &str, required: &str| {
                let relative = Path::new(current).parent().unwrap_or(Path::new("")).join(required);
                match std::fs::read_to_string(root.join(&relative)) {
                    Ok(text) => Ok(k_rust::outer::ResolvedSource::new(relative.to_str().expect("relative source"), text)),
                    Err(_) => k_rust::builtin::embedded(required).ok_or_else(|| format!("cannot resolve {required}")),
                }
            };
            let baseline = kink_patch::Baseline::load(
                k_rust::outer::ResolvedSource::new(entry, std::fs::read_to_string(root.join(entry)).expect("external source")),
                main, Some(syntax), &mut resolver, &support::options(),
            ).expect("external definition loads");
            let validator = NativeValidator::bind(baseline, CompileOptions::default());
            let compiled = validator.compile_baseline().expect("external compiles");
            kink_native::representation::validate_representation(&compiled).expect("external representation admitted");
            assert_eq!(declaration_census(&compiled).expect("census").verdict(), CensusVerdict::Natural, "STOP N1 {main}: census");
            let fixture = Fixture { validator, compiled, syntax: syntax.to_owned(), depth };
            execute_rows(&fixture, &programs);
            eprintln!("CS16 N1 external {main}: every terminal canonical byte for byte");
        }
    }).expect("external measurement thread").join().unwrap_or_else(|panic| std::panic::resume_unwind(panic));
}
