//! A leaf as deep as a long run makes it, judged on the stack kink-flow and kink-corpus run a
//! definition on: the adapter's feasibility, the terminal value and the existence evidence of
//! the bridge, the bridge's reading of the run into paths, and a pattern slot's relation decision
//! over a subterm as deep as the leaf; and kink-native's walks of a
//! term, on deep chains and a thread far smaller than they are deep.
//!
//! A list a step appends to is one level deeper in KORE per step (a right-nested chain of
//! concatenations), so a long run ends at a leaf as deep as its number of steps, while the
//! definition thread has a fixed stack. The run here starts with the whole list in its `<log>`
//! cell, written as one associative application, which k-rust reads into its list without
//! nesting; one rewrite later the leaf comes back as the chain, and kink admits it to k-rust
//! with its collections associated again, so its length adds no level to the admission.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::{path::Path, time::Duration};

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
    kore::{
        ast::{Associativity, Pattern, Symbol},
        parser::parse_definition,
    },
};
use k_rust_backend::nesting;
use kink_native::{
    NativeValidator,
    bridge::{BridgeContext, paths_from_execution_existing},
    execution::{ExecutionAdapter, ExecutionBudget, HaltClass, SolverProfile},
    feasibility::{LeafFeasibility, TestInitialState},
    step_events::ObservationDecider,
};
use kink_pattern::{
    ExecutionTerminalKind, PathStop, RelationDecider, RelationDecision, SymbolSorts,
};

/// The entries of the list, the depth of a million-step run: as a right-nested chain, the form
/// k-rust's facade hands the leaf in, more levels than the definition thread's stack holds of
/// k-rust's recursive internalization of a pattern (about 230,000 at 1,152 bytes per level in a
/// release build, fewer in the test build) and more than the largest stack k-rust provides
/// holds in the test build (`nesting::max_depth`, 700,000 levels), so the leaf would be refused
/// for its depth if kink admitted it as it is handed. kink admits the leaf with its collections
/// associated, whose depth does not grow with the list's length, and holds it as a
/// `kore::Pattern`, whose clone, comparison and drop keep their work on the heap.
const ENTRIES: usize = 1_000_000;

/// The entries the list holds: [`ENTRIES`], or one more than `nesting::max_depth` where that is
/// more (a release build, whose largest stack holds about a million levels), so that in every
/// build the leaf as handed is deeper than the largest stack k-rust provides, and the test shows
/// what association admits rather than a leaf k-rust could admit as handed.
fn entries() -> usize {
    ENTRIES.max(nesting::max_depth() + 1)
}

/// The levels of the chains the walks are run on in [`deep_walks_keep_their_work_off_the_stack`]:
/// far more than an 8 MiB thread holds of any recursion that takes a frame per level.
const WALK_LEVELS: usize = 200_000;

/// The stack of the thread the walks are run on.
const WALK_STACK_BYTES: usize = 8 << 20;

/// The stack of the thread kink-flow and kink-corpus run a definition on
/// (`kink_corpus::cli::DEFINITION_STACK_BYTES`, which this crate cannot name).
const DEFINITION_STACK_BYTES: usize = 256 << 20;

const LOG_CELL: &str = "Lbl'-LT-'log'-GT-'";
const LIST_UNIT: &str = "Lbl'Stop'List";
const LIST_ELEMENT: &str = "LblListItem";
const LIST_CONCAT: &str = "Lbl'Unds'List'Unds'";

/// `inj{Int, KItem}(value)`.
fn item(value: usize) -> Pattern {
    kore_application(
        "inj",
        vec![kore_sort("SortInt"), kore_sort("SortKItem")],
        vec![Pattern::DomainValue {
            sort: kore_sort("SortInt"),
            value: (value % 256).to_string().into(),
        }],
    )
}

/// `ListItem(inj{Int, KItem}(value))`.
fn element(value: usize) -> Pattern {
    kore_application(LIST_ELEMENT, Vec::new(), vec![item(value)])
}

/// `pattern` with the content of its `<log>` cell, the empty list, replaced by `list`.
fn with_log(pattern: &mut Pattern, list: &mut Option<Pattern>) {
    let Pattern::Application { symbol, arguments } = pattern else {
        return;
    };
    if symbol.name == LOG_CELL {
        let [content] = arguments.as_mut_slice() else {
            panic!("the <log> cell has one argument");
        };
        assert!(
            matches!(content, Pattern::Application { symbol, arguments }
                if symbol.name == LIST_UNIT && arguments.is_empty()),
            "the <log> cell starts empty"
        );
        *content = list.take().expect("one <log> cell");
        return;
    }
    for argument in arguments {
        with_log(argument, list);
    }
}

/// The number of elements of the right-nested chain `list`, or `None` when it is not one.
fn chain_length(mut list: &Pattern) -> Option<usize> {
    let mut length = 0;
    // Invariant: `length` counts the elements left of `list`; each round moves one level down.
    loop {
        let Pattern::Application { symbol, arguments } = list else {
            return None;
        };
        match (symbol.name.as_str(), arguments.as_slice()) {
            (LIST_ELEMENT, [_]) => return Some(length + 1),
            (LIST_UNIT, []) => return Some(length),
            (LIST_CONCAT, [Pattern::Application { symbol, .. }, tail])
                if symbol.name == LIST_ELEMENT =>
            {
                length += 1;
                list = tail;
            }
            _ => return None,
        }
    }
}

/// The content of the `<log>` cell of `pattern`.
fn log_content(pattern: &Pattern) -> Option<&Pattern> {
    let mut pending = vec![pattern];
    while let Some(node) = pending.pop() {
        if let Pattern::Application { symbol, arguments } = node {
            if symbol.name == LOG_CELL {
                return arguments.first();
            }
            pending.extend(arguments);
        }
    }
    None
}

/// The content of the `<log>` cell of `pattern`, to replace.
fn log_content_mut(pattern: &mut Pattern) -> Option<&mut Pattern> {
    let mut pending = vec![pattern];
    while let Some(node) = pending.pop() {
        if let Pattern::Application { symbol, arguments } = node {
            if symbol.name == LOG_CELL {
                return arguments.first_mut();
            }
            pending.extend(arguments);
        }
    }
    None
}

fn judge_the_deep_leaf() {
    let entries = entries();
    let validator = NativeValidator::bind(
        support::load_path(&Path::new(support::DIR).join("collstore.k"), "COLLSTORE"),
        CompileOptions::default(),
    );
    let compiled = validator.compile_baseline().expect("fixture compiles");
    let mut backend = Backend::new(
        &compiled.artifacts().definition_kore,
        k_rust::kast::identifier::encode(&compiled.definition().main_module),
        BackendOptions::default(),
    )
    .expect("backend");
    let grammar = ProgramGrammar::new(validator.baseline().definition()).expect("grammar");
    let variables = &compiled.artifacts().configuration_variables;
    let mut assembler = ConfigurationAssembler::new(
        &grammar,
        &validator.baseline().definition().main_module,
        "COLLSTORE-SYNTAX",
        variables,
    );
    let start = program_start_position(variables.get("PGM").unwrap_or(&Sort::new("KItem")));
    assembler.program(&start, "halt()").expect("program parses");
    assembler
        .bind_stream_defaults::<ConfigurationError>(false, false, || Ok(Vec::new()))
        .expect("streams");
    let program = assembler.finish().expect("input assembled");
    // The input is `initGeneratedTopCell` of the program; the configuration with its cells is
    // the leaf of a run of no rewrite step.
    let budget = |max_depth| ExecutionBudget {
        time: Duration::from_secs(600),
        max_simplification_iterations: 1000,
        max_depth: Some(max_depth),
        max_breadth: None,
    };
    let configured = ExecutionAdapter::with_profile(SolverProfile::BUILD)
        .execute(&mut backend, &program, budget(0))
        .expect("initialization");
    let [configured] = configured.leaves() else {
        panic!("one initialized configuration");
    };
    let mut initial = configured.branch.state.clone();
    let mut list = Some(Pattern::AssociativeApplication {
        associativity: Associativity::Right,
        symbol: Symbol {
            name: LIST_CONCAT.into(),
            sort_parameters: Vec::new(),
        },
        arguments: (0..entries).map(element).collect(),
    });
    with_log(&mut initial, &mut list);
    assert!(list.is_none(), "the configuration has a <log> cell");

    kink_native::bridge::validate_test_initial_state(&mut backend, &initial)
        .expect("concrete input admitted");
    let execution = ExecutionAdapter::with_profile(SolverProfile::BUILD)
        .execute(&mut backend, &initial, budget(10))
        .expect("execution");
    assert!(!execution.timed_out(), "the run ends before its time bound");
    let [leaf] = execution.leaves() else {
        panic!("one leaf, not {}", execution.leaves().len());
    };
    assert_eq!(
        leaf.halt,
        HaltClass::Stuck,
        "halt() rewrites once and stops"
    );
    // The adapter admitted the leaf, associated, on a stack sized for that form, which is within
    // the depth k-rust provides a stack for, so the admission was not refused for its depth, and
    // a host's refusal would have failed the execution above. So `Unknown` is the admission's
    // own answer.
    assert_eq!(
        leaf.feasibility,
        LeafFeasibility::Unknown,
        "a collection is never a constructor term, and the leaf has no constraint"
    );

    let sorts = SymbolSorts::from_definition(
        &parse_definition(&compiled.artifacts().definition_kore).expect("KORE"),
    );
    let normal = |_: &Pattern| ExecutionTerminalKind::Normal;
    let context = BridgeContext {
        test_id: "deep-leaf",
        classify: &normal,
        sorts: &sorts,
    };
    backend
        .with_solver(None, |definition, solver| {
            let decider =
                ObservationDecider::new(definition, solver, TestInitialState::of_test(&initial));
            let raw = leaf.branch.state.clone();
            assert_eq!(
                log_content(&raw).and_then(chain_length),
                Some(entries),
                "the leaf's list is the right-nested chain of every entry"
            );
            let depth = definition.operation_depth(&[&raw]);
            assert!(
                entries < depth,
                "the leaf as k-rust hands it is deeper than its list: {depth}"
            );
            assert!(
                nesting::max_depth() < depth,
                "the leaf as k-rust hands it is deeper than the largest stack k-rust provides \
                 ({}), so admitting it as handed would be refused: {depth}",
                nesting::max_depth()
            );
            // The leaf with a three-entry list in place of its own: associated, the two are
            // equally deep, so the admitted form's depth does not depend on the list's length.
            let mut short = raw.clone();
            *log_content_mut(&mut short).expect("the leaf has a <log> cell") =
                (0..2).rev().fold(element(2), |rest, value| {
                    app(LIST_CONCAT, vec![element(value), rest])
                });
            let associated = definition.associated_collections(&raw);
            let associated_depth = definition.operation_depth(&[associated.as_ref()]);
            assert_eq!(
                associated_depth,
                definition.operation_depth(&[definition.associated_collections(&short).as_ref()]),
                "the associated leaf is as deep as with a three-entry list"
            );
            assert!(
                associated_depth <= nesting::max_depth(),
                "the associated leaf is within what k-rust provides a stack for: {associated_depth}"
            );
            drop((associated, short));
            assert_eq!(
                decider.terminal_value(&raw).as_ref(),
                Some(&raw),
                "the leaf is a terminal value in k-rust's externalized form"
            );
            assert_eq!(decider.first_non_value(&raw), None);
            let log = log_content(&raw).expect("the leaf has a <log> cell");
            let (exists, shared, bridged, related) = decider
                .host_refusal_during(|| {
                    let bridged = paths_from_execution_existing(
                        &execution,
                        &context,
                        &|term| decider.terminal_value(term),
                        &|term| decider.configuration_exists(term),
                    );
                    // A pattern slot binding the list and reading it as a payload: the relation
                    // decision admits both on a stack sized for them.
                    let related = bridged.as_ref().ok().map(|bridged| {
                        decider
                            .relations()
                            .relate(&bridged.paths[0], &[], log, &log.clone())
                    });
                    (
                        decider.configuration_exists(&raw),
                        decider.shared_leaf_feasibility(&leaf.branch.state),
                        bridged,
                        related,
                    )
                })
                .expect("the host maps the stacks the leaf needs");
            assert_eq!(
                related,
                Some(RelationDecision::Equal),
                "the list admits to one internal term, related to itself"
            );
            assert!(
                exists,
                "the leaf is shown to exist: its associated form is within what k-rust provides a \
                 stack for"
            );
            assert_eq!(
                shared,
                LeafFeasibility::Unknown,
                "the step-tracked bridge's feasibility admits the leaf as the adapter's does"
            );
            let bridged = bridged.expect("bridge");
            let [path] = bridged.paths.as_slice() else {
                panic!("one path, not {}", bridged.paths.len());
            };
            assert!(
                path.complete && path.stop == PathStop::Terminal,
                "the stuck leaf with a terminal value is a complete path: {:?} {:?}",
                path.complete,
                path.stop
            );
            assert_eq!(
                path.execution_terminal
                    .as_ref()
                    .map(|terminal| &terminal.state),
                Some(&raw),
                "the path ends at the leaf's value"
            );
            Ok::<_, BackendError>(())
        })
        .expect("solver");
}

/// `symbol(arguments)`, with no sort parameters.
fn app(symbol: &str, arguments: Vec<Pattern>) -> Pattern {
    kore_application(symbol, Vec::new(), arguments)
}

/// kink-native's walks of a term keep their work on the heap: the terminal value, the reason a
/// term has none and definition independence, on a configuration that holds a K sequence, a
/// right-nested list and lists nested in each other, each [`WALK_LEVELS`] deep, on a thread of
/// [`WALK_STACK_BYTES`]. Each would overflow that thread if it took a frame per level, and the
/// nested lists hold a collection below every level, which a walk that looked for one below each
/// level afresh would take quadratic time over.
#[test]
fn deep_walks_keep_their_work_off_the_stack() {
    let validator = NativeValidator::bind(
        support::load_path(&Path::new(support::DIR).join("collstore.k"), "COLLSTORE"),
        CompileOptions::default(),
    );
    let compiled = validator.compile_baseline().expect("fixture compiles");
    let mut backend = Backend::new(
        &compiled.artifacts().definition_kore,
        k_rust::kast::identifier::encode(&compiled.definition().main_module),
        BackendOptions::default(),
    )
    .expect("backend");
    let definition = backend.select_definition(None).expect("definition");
    // `kseq(inj(0), kseq(inj(1), ... dotk))`: free constructors all the way down.
    let sequence = (0..WALK_LEVELS)
        .rev()
        .fold(app("dotk", Vec::new()), |rest, value| {
            app("kseq", vec![item(value), rest])
        });
    // `<log>(ListItem(inj(0)) ListItem(inj(1)) ...)`, right-nested as k-rust externalizes it.
    let list = app(
        LOG_CELL,
        vec![
            (0..WALK_LEVELS - 1)
                .rev()
                .fold(element(WALK_LEVELS - 1), |rest, value| {
                    app(LIST_CONCAT, vec![element(value), rest])
                }),
        ],
    );
    // `<log>(ListItem(inj{List, KItem}(ListItem(inj{List, KItem}(... ListItem(inj(0)))))))`.
    let nested = app(
        LOG_CELL,
        vec![(0..WALK_LEVELS / 2).fold(element(0), |inner, _| {
            app(
                LIST_ELEMENT,
                vec![kore_application(
                    "inj",
                    vec![kore_sort("SortList"), kore_sort("SortKItem")],
                    vec![inner],
                )],
            )
        })],
    );
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("deep-walks".into())
            .stack_size(WALK_STACK_BYTES)
            .spawn_scoped(scope, || {
                let solver = k_rust_backend::smt::NoSolver;
                let initial = app("dotk", Vec::new());
                let decider = ObservationDecider::new(
                    &definition,
                    &solver,
                    TestInitialState::of_test(&initial),
                );
                for (name, term) in [
                    ("sequence", &sequence),
                    ("list", &list),
                    ("nested lists", &nested),
                ] {
                    assert_eq!(decider.first_non_value(term), None, "{name}");
                    assert_eq!(
                        decider.terminal_value(term).as_ref(),
                        Some(term),
                        "{name} is a terminal value in k-rust's externalized form"
                    );
                }
                assert!(decider.definition_independent(&sequence));
                assert!(
                    decider.first_dependent(&list).is_some(),
                    "a collection head is no free constructor"
                );
            })
            .expect("thread")
            .join()
            .expect("the deep terms are walked");
    });
}

mod kink_tier {
    /// The run, the adapter's feasibility and the bridge on a leaf with a million-entry list, on
    /// the definition thread's stack: every walk kink makes over the leaf either keeps its work
    /// on the heap or runs on a stack k-rust sizes for the leaf's associated form, so none
    /// overflows and none is refused for the leaf's depth.
    /// About 90 s and 8 GiB in the test build, which is why it is not a light test.
    #[test]
    #[ignore = "kink"]
    fn a_deep_list_leaf_is_judged_on_the_definition_stack() {
        std::thread::Builder::new()
            .name("deep-leaf".into())
            .stack_size(super::DEFINITION_STACK_BYTES)
            .spawn(super::judge_the_deep_leaf)
            .expect("thread")
            .join()
            .expect("the deep leaf is judged");
    }
}
