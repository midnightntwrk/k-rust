//! The state-set exploration merge (`backend.rewrite.execute`): a state-set execution expands
//! each distinct state of a depth once, and its result is the deduplicated path-set result.

use k_rust_backend::{
    builtin::BuiltinEffect,
    definition::BackendDefinition,
    diagnostic::BackendDiagnostic,
    rewrite::{
        ExecutionLeaf, ExecutionOptions, ExecutionResult, HaltReason, Pattern, TraceEntry, execute,
        execute_observed, execute_with_io_state,
    },
    rule::Predicate,
    search::{ResultModality, SearchOptions, SearchType, search_graph},
    transition::{ConsoleObservation, ExecutionIoState, ObservationOptions},
};
use k_rust_kore::{
    kore::parser::{parse_definition, parse_pattern},
    measure::{Counter, snapshot},
};

use crate::support::{rule, search_definition};

/// A definition whose states are `node(name)` and `seq(effect, state)`, with the console and
/// log hooks, `cond`, a condition no rule or solver decides, and the rewrite rules `rules`.
pub(crate) fn graph_definition(rules: &str) -> BackendDefinition {
    let source = format!(
        r#"[]
            module MAIN
                hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
                hooked-sort SortString{{}} [hook{{}}("STRING.String"), hasDomainValues{{}}()]
                hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
                sort SortK{{}} []
                symbol node{{}}(SortString{{}}) : SortK{{}} [constructor{{}}()]
                symbol seq{{}}(SortK{{}}, SortK{{}}, SortString{{}}) : SortK{{}} [constructor{{}}()]
                symbol dotk{{}}() : SortK{{}} [constructor{{}}(), total{{}}()]
                hooked-symbol log{{}}(SortString{{}}) : SortK{{}}
                    [function{{}}(), total{{}}(), hook{{}}("IO.logString")]
                hooked-symbol write{{}}(SortInt{{}}, SortString{{}}) : SortK{{}}
                    [function{{}}(), total{{}}(), hook{{}}("IO.write")]
                symbol cond{{}}(SortString{{}}) : SortBool{{}}
                    [function{{}}(), total{{}}(), no-evaluators{{}}()]
                {rules}
            endmodule []"#
    );
    let syntax = parse_definition(&source).expect("graph definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("graph definition should internalize")
}

/// The state `node(name)`.
pub(crate) fn node(name: &str) -> String {
    format!(r#"node{{}}(\dv{{SortString{{}}}}("{name}"))"#)
}

/// A rule `from => to` labelled `label`, where `from` names a node and `to` is a term.
pub(crate) fn edge(label: &str, from: &str, to: &str) -> String {
    format!(
        r#"
            axiom{{}} \rewrites{{SortK{{}}}}(
                \and{{SortK{{}}}}({}, \top{{SortK{{}}}}()),
                \and{{SortK{{}}}}({to}, \top{{SortK{{}}}}())
            ) [label{{}}("{label}")]"#,
        node(from)
    )
}

/// A rule `from => to requires cond(from) = true`, which no solver decides.
pub(crate) fn guarded_edge(label: &str, from: &str, to: &str) -> String {
    format!(
        r#"
            axiom{{}} \rewrites{{SortK{{}}}}(
                \and{{SortK{{}}}}(
                    {},
                    \equals{{SortBool{{}}, SortK{{}}}}(
                        cond{{}}(\dv{{SortString{{}}}}("{from}")),
                        \dv{{SortBool{{}}}}("true")
                    )
                ),
                \and{{SortK{{}}}}({to}, \top{{SortK{{}}}}())
            ) [label{{}}("{label}")]"#,
        node(from)
    )
}

/// The state `seq(log(text), write(1, bytes), name)`: the log and the write are evaluated when
/// the state is built, leaving `seq(dotk, dotk, name)`.
pub(crate) fn logging(text: &str, bytes: &str, name: &str) -> String {
    format!(
        r#"seq{{}}(log{{}}(\dv{{SortString{{}}}}("{text}")), write{{}}(\dv{{SortInt{{}}}}("1"), \dv{{SortString{{}}}}("{bytes}")), \dv{{SortString{{}}}}("{name}"))"#
    )
}

/// A rule `seq(K1, K2, name) => to`.
pub(crate) fn seq_edge(label: &str, name: &str, to: &str) -> String {
    format!(
        r#"
            axiom{{}} \rewrites{{SortK{{}}}}(
                \and{{SortK{{}}}}(
                    seq{{}}(K1:SortK{{}}, K2:SortK{{}}, \dv{{SortString{{}}}}("{name}")),
                    \top{{SortK{{}}}}()
                ),
                \and{{SortK{{}}}}({to}, \top{{SortK{{}}}}())
            ) [label{{}}("{label}")]"#
    )
}

/// A chain of `diamonds` diamonds: `s{i}` rewrites to `l{i}` and `r{i}`, both of which rewrite
/// to `s{i + 1}`.
pub(crate) fn diamond_chain(diamonds: usize) -> String {
    (0..diamonds)
        .map(|i| {
            let next = node(&format!("s{}", i + 1));
            [
                edge(
                    &format!("s{i}-l"),
                    &format!("s{i}"),
                    &node(&format!("l{i}")),
                ),
                edge(
                    &format!("s{i}-r"),
                    &format!("s{i}"),
                    &node(&format!("r{i}")),
                ),
                edge(&format!("l{i}-s"), &format!("l{i}"), &next),
                edge(&format!("r{i}-s"), &format!("r{i}"), &next),
            ]
            .concat()
        })
        .collect()
}

pub(crate) fn pattern(definition: &BackendDefinition, source: &str) -> Pattern {
    definition
        .admit_unverified(&parse_pattern(source).expect("pattern should parse"), &[])
        .internalize_pattern()
        .expect("pattern should internalize")
}

/// One modality's run: its result, the states it popped (`RewriteSteps`) and the arrivals it
/// merged.
pub(crate) struct Run {
    pub(crate) result: ExecutionResult,
    pub(crate) steps: u64,
    pub(crate) merged: u64,
}

pub(crate) fn run(
    definition: &BackendDefinition,
    initial: &Pattern,
    options: &ExecutionOptions,
    result_modality: ResultModality,
) -> Run {
    let before = snapshot();
    let result = execute_with_io_state(
        definition,
        initial.clone(),
        ExecutionOptions {
            result_modality,
            ..options.clone()
        },
        ExecutionIoState::default(),
    );
    let delta = snapshot().delta(&before);
    Run {
        result,
        steps: delta.get(Counter::RewriteSteps),
        merged: delta.get(Counter::ExecutionStatesMerged),
    }
}

/// Whether the run exceeded `max_breadth`: it then ends every pending state as a breadth-bound
/// leaf.
pub(crate) fn reaches_breadth_bound(result: &ExecutionResult) -> bool {
    result
        .leaves
        .iter()
        .any(|leaf| leaf.halt_reason == HaltReason::BreadthBound)
}

fn carries_configuration(leaf: &ExecutionLeaf) -> bool {
    !matches!(
        leaf.halt_reason,
        HaltReason::Trivial { .. } | HaltReason::Vacuous { .. }
    )
}

type Key = (Pattern, Vec<BuiltinEffect>, ConsoleObservation);

fn key(leaf: &ExecutionLeaf) -> Key {
    (
        leaf.pattern.clone(),
        leaf.effects.clone(),
        leaf.io.observable(),
    )
}

/// What a leaf without a configuration denotes: its depth, state, and obligation or false
/// constraint. The rule it names is witness metadata under merging.
fn bottom(leaf: &ExecutionLeaf) -> Option<(u64, Pattern, Predicate)> {
    match &leaf.halt_reason {
        HaltReason::Trivial {
            depth, obligation, ..
        } => Some((*depth, leaf.pattern.clone(), obligation.clone())),
        HaltReason::Vacuous {
            depth, constraint, ..
        } => Some((*depth, leaf.pattern.clone(), constraint.clone())),
        _ => None,
    }
}

/// Whether an earlier leaf of halt `retained` stands for a later leaf of halt `later` of the same
/// configuration, by the state-set contract (docs/compatibility.md): a stuck, branch or cut-point
/// leaf stands for any later leaf but a terminal-rule one; a leaf that leaves its configuration's
/// subtree unexplored or undecided only for another such leaf; a terminal-rule leaf only for, and
/// only by, a stuck or terminal-rule leaf. The fixtures have no run-ending stop.
fn stands_for(retained: &HaltReason, later: &HaltReason) -> bool {
    let decided = |halt: &HaltReason| {
        matches!(
            halt,
            HaltReason::Stuck | HaltReason::Branch { .. } | HaltReason::CutPointRule { .. }
        )
    };
    let terminal = |halt: &HaltReason| matches!(halt, HaltReason::TerminalRule { .. });
    if terminal(retained) || terminal(later) {
        let final_ = |halt: &HaltReason| matches!(halt, HaltReason::Stuck) || terminal(halt);
        return final_(retained) && final_(later);
    }
    decided(retained) || !decided(later)
}

fn witness(leaf: &ExecutionLeaf) -> (Pattern, u64, HaltReason, Vec<TraceEntry>) {
    (
        leaf.pattern.clone(),
        leaf.depth,
        leaf.halt_reason.clone(),
        leaf.trace.clone(),
    )
}

fn distinct<T: PartialEq>(items: impl IntoIterator<Item = T>) -> Vec<T> {
    let mut distinct = Vec::new();
    for item in items {
        if !distinct.contains(&item) {
            distinct.push(item);
        }
    }
    distinct
}

fn same_set<T: PartialEq + std::fmt::Debug>(left: &[T], right: &[T], what: &str, context: &str) {
    assert!(
        left.iter().all(|item| right.contains(item))
            && right.iter().all(|item| left.contains(item)),
        "{context}: {what} differ:\n{left:#?}\n{right:#?}"
    );
}

/// The state-set run of `initial` merges equal states during exploration, and its result is
/// the path-set result's, deduplicated:
/// - its leaves carrying a configuration, as a set of (state, effects, console), are the
///   path-set leaves', and each has the depth and halt reason of a path-set leaf of its key;
/// - in order, they are the path-set leaves the final merge keeps (each retained leaf the first of
///   the leaves it stands for, [`stands_for`]), with that leaf's depth, halt reason and trace;
/// - leaves without a configuration denote the same (depth, state, obligation) set;
/// - the union of the leaves' diagnostics is the same;
/// - the run's coverage (`ExecutionOptions::collect_coverage`) is the same;
/// - the state-set run pops no more states than the path-set run.
///
/// Under `max_breadth` this holds where the path-set run never exceeds the bound: the merged
/// run's pending states are then the path-set run's without the skipped subtrees, so it never
/// exceeds the bound either. Where the path-set run exceeds it, the merged run reaches the bound
/// later or not at all and its frontier may lie deeper, and only the path-set run's own
/// properties are checked.
pub(crate) fn assert_merged_state_set_agrees(
    definition: &BackendDefinition,
    initial: &Pattern,
    options: &ExecutionOptions,
    context: &str,
) -> (Run, Run) {
    let options = &ExecutionOptions {
        collect_coverage: true,
        ..options.clone()
    };
    let state_set = run(definition, initial, options, ResultModality::StateSet);
    let path_set = run(definition, initial, options, ResultModality::PathSet);
    assert_eq!(
        path_set.merged, 0,
        "{context}: a path-set run merges nothing"
    );
    for leaf in state_set
        .result
        .leaves
        .iter()
        .chain(&path_set.result.leaves)
    {
        assert!(
            !matches!(leaf.halt_reason, HaltReason::Stopped(_)),
            "{context}: the fixture has no stop: {leaf:#?}"
        );
    }
    if reaches_breadth_bound(&path_set.result) {
        return (state_set, path_set);
    }
    assert_eq!(
        state_set.result.coverage, path_set.result.coverage,
        "{context}: the coverage differs"
    );

    let configured = |result: &ExecutionResult| {
        result
            .leaves
            .iter()
            .filter(|leaf| carries_configuration(leaf))
            .cloned()
            .collect::<Vec<_>>()
    };
    let state_leaves = configured(&state_set.result);
    let path_leaves = configured(&path_set.result);
    let state_keys = state_leaves.iter().map(key).collect::<Vec<_>>();
    let path_keys = path_leaves.iter().map(key).collect::<Vec<_>>();
    same_set(&state_keys, &path_keys, "configurations", context);
    for leaf in &state_leaves {
        assert!(
            path_leaves.iter().any(|path| key(path) == key(leaf)
                && path.depth == leaf.depth
                && path.halt_reason == leaf.halt_reason),
            "{context}: no path-set leaf has the state-set leaf's depth and halt: {leaf:#?}"
        );
    }
    // The final merge of the path-set leaves, as the state-set contract states it: a leaf is
    // dropped when an earlier retained leaf of its key stands for it.
    let mut retained = Vec::<(Key, ExecutionLeaf)>::new();
    for leaf in &path_leaves {
        if !retained.iter().any(|(seen, kept)| {
            *seen == key(leaf) && stands_for(&kept.halt_reason, &leaf.halt_reason)
        }) {
            retained.push((key(leaf), leaf.clone()));
        }
    }
    assert_eq!(
        state_leaves.iter().map(witness).collect::<Vec<_>>(),
        retained
            .iter()
            .map(|(_, leaf)| witness(leaf))
            .collect::<Vec<_>>(),
        "{context}: the state-set leaves are the path-set leaves of the final merge, in order"
    );

    let bottoms = |result: &ExecutionResult| distinct(result.leaves.iter().filter_map(bottom));
    same_set(
        &bottoms(&state_set.result),
        &bottoms(&path_set.result),
        "leaves without a configuration",
        context,
    );
    let diagnostics = |result: &ExecutionResult| {
        distinct(
            result
                .leaves
                .iter()
                .flat_map(|leaf| leaf.diagnostics.iter().cloned()),
        )
    };
    let state_diagnostics: Vec<BackendDiagnostic> = diagnostics(&state_set.result);
    same_set(
        &state_diagnostics,
        &diagnostics(&path_set.result),
        "diagnostics",
        context,
    );
    assert!(
        state_set.steps <= path_set.steps,
        "{context}: {} state-set steps against {} path-set steps",
        state_set.steps,
        path_set.steps
    );
    (state_set, path_set)
}

/// Small ground rule graphs, each with and without a depth bound and under breadth bounds of 2
/// and 3 (checked where the path-set run stays within them): chains of converging
/// diamonds; diamonds of unequal lengths, which meet at different depths; distinct final
/// states; a cycle; an undefined step after a diamond; a remainder after a diamond; a diamond
/// whose branches log and write alike, and one whose branches log differently.
#[test]
fn a_merged_state_set_result_is_the_deduplicated_path_set_result() {
    let mut fixtures = Vec::<(String, String)>::new();
    for diamonds in 1..=4 {
        fixtures.push((format!("chain of {diamonds}"), diamond_chain(diamonds)));
    }
    fixtures.push((
        "unequal diamond".into(),
        [
            edge("a-b", "a", &node("b")),
            edge("b-c", "b", &node("c")),
            edge("c-d", "c", &node("d")),
            edge("a-e", "a", &node("e")),
            edge("e-d", "e", &node("d")),
            edge("d-f", "d", &node("f")),
        ]
        .concat(),
    ));
    fixtures.push((
        "distinct finals".into(),
        [edge("a-x", "a", &node("x")), edge("a-y", "a", &node("y"))].concat(),
    ));
    fixtures.push((
        "cycle".into(),
        [
            edge("a-l", "a", &node("l")),
            edge("a-r", "a", &node("r")),
            edge("l-a", "l", &node("a")),
            edge("r-a", "r", &node("a")),
            edge("l-z", "l", &node("z")),
        ]
        .concat(),
    ));
    fixtures.push((
        "undefined step after a diamond".into(),
        [
            edge("a-l", "a", &node("l")),
            edge("a-r", "a", &node("r")),
            edge("l-m", "l", &node("m")),
            edge("r-m", "r", &node("m")),
            edge("m-undefined", "m", r#"node{}(\bottom{SortString{}}())"#),
        ]
        .concat(),
    ));
    fixtures.push((
        "remainder after a diamond".into(),
        [
            edge("a-l", "a", &node("l")),
            edge("a-r", "a", &node("r")),
            edge("l-m", "l", &node("m")),
            edge("r-m", "r", &node("m")),
            guarded_edge("m-z", "m", &node("z")),
        ]
        .concat(),
    ));
    fixtures.push((
        "branches that log and write alike".into(),
        [
            edge("a-l", "a", &node("l")),
            edge("a-r", "a", &node("r")),
            edge("l-m", "l", &logging("line", "x", "m")),
            edge("r-m", "r", &logging("line", "x", "m")),
            seq_edge("m-z", "m", &node("z")),
        ]
        .concat(),
    ));
    fixtures.push((
        "branches that log differently".into(),
        [
            edge("a-l", "a", &node("l")),
            edge("a-r", "a", &node("r")),
            edge("l-m", "l", &logging("left", "x", "m")),
            edge("r-m", "r", &logging("right", "x", "m")),
            seq_edge("m-z", "m", &node("z")),
        ]
        .concat(),
    ));
    for (name, rules) in &fixtures {
        let definition = graph_definition(rules);
        let start = if name.starts_with("chain") { "s0" } else { "a" };
        let initial = pattern(&definition, &node(start));
        // The cycle never ends without a depth bound.
        let depths: &[u64] = if name == "cycle" {
            &[3, 6]
        } else {
            &[u64::MAX, 3]
        };
        for &max_depth in depths {
            for max_breadth in [None, Some(2), Some(3)] {
                let options = ExecutionOptions {
                    max_depth,
                    max_breadth,
                    ..ExecutionOptions::default()
                };
                assert_merged_state_set_agrees(
                    &definition,
                    &initial,
                    &options,
                    &format!("{name}, max_depth {max_depth}, max_breadth {max_breadth:?}"),
                );
            }
        }
    }

    // The budget exhaustion of one of two converging paths (KINK-01/1's fixture), in both rule
    // orders: the diagnosed arrival is not merged into the clean one, and the clean one is
    // merged into the diagnosed one.
    for rules in [["to-c", "to-norm"], ["to-norm", "to-c"]] {
        let definition = search_definition(
            &rules
                .map(|label| match label {
                    "to-c" => rule("to-c", "start{}()", "c{}()"),
                    _ => rule("to-norm", "start{}()", "norm{}(a{}())"),
                })
                .concat(),
        );
        let initial = pattern(&definition, "start{}()");
        for max_depth in [u64::MAX, 1] {
            let options = ExecutionOptions {
                max_depth,
                max_simplification_iterations: 3,
                ..ExecutionOptions::default()
            };
            assert_merged_state_set_agrees(
                &definition,
                &initial,
                &options,
                &format!("{rules:?}, max_depth {max_depth}"),
            );
        }
    }
}

/// Under state-set, `max_breadth` bounds the pending states of the merged exploration. A merged
/// arrival pushes no successors, so where the path-set run exceeds the bound inside a subtree the
/// merged run skips, the merged run reaches the bound later or not at all: its frontier can lie
/// deeper, and it can report configurations the path-set result does not. Here `a` reaches `m`
/// through `p` and through `q`, and `q` has three more successors: with `max_breadth` 4 the
/// path-set run exceeds the bound when it expands `m` the second time, while the merged run
/// skips that arrival and runs to the end. With 3 both runs exceed it at the same point, and with
/// 5 neither does.
#[test]
fn under_a_breadth_bound_a_merged_run_can_explore_past_the_path_set_frontier() {
    let rules = [
        edge("a-p", "a", &node("p")),
        edge("a-q", "a", &node("q")),
        edge("p-m", "p", &node("m")),
        edge("q-m", "q", &node("m")),
        edge("q-q1", "q", &node("q1")),
        edge("q-q2", "q", &node("q2")),
        edge("q-q3", "q", &node("q3")),
        edge("m-m1", "m", &node("m1")),
        edge("m-m2", "m", &node("m2")),
        edge("q1-z", "q1", &node("z")),
    ]
    .concat();
    let definition = graph_definition(&rules);
    let initial = pattern(&definition, &node("a"));
    let leaves = |run: &Run| {
        run.result
            .leaves
            .iter()
            .map(|leaf| {
                let name = (["m1", "m2", "m", "q1", "q2", "q3", "z"].into_iter())
                    .find(|name| leaf.pattern == pattern(&definition, &node(name)))
                    .unwrap_or("?");
                (name, leaf.depth, leaf.halt_reason.clone())
            })
            .collect::<Vec<_>>()
    };
    use HaltReason::{BreadthBound, Stuck};
    let options = |bound| ExecutionOptions {
        max_breadth: Some(bound),
        ..ExecutionOptions::default()
    };
    let (state_set, path_set) =
        assert_merged_state_set_agrees(&definition, &initial, &options(4), "max_breadth 4");
    assert!(reaches_breadth_bound(&path_set.result));
    assert_eq!(state_set.merged, 1);
    assert_eq!(
        leaves(&path_set),
        [
            ("m1", 3, Stuck),
            ("m2", 3, Stuck),
            ("m1", 3, BreadthBound),
            ("m2", 3, BreadthBound),
            ("q1", 2, BreadthBound),
            ("q2", 2, BreadthBound),
            ("q3", 2, BreadthBound),
        ]
    );
    assert_eq!(
        leaves(&state_set),
        [
            ("m1", 3, Stuck),
            ("m2", 3, Stuck),
            ("z", 3, Stuck),
            ("q2", 2, Stuck),
            ("q3", 2, Stuck),
        ]
    );
    for bound in [3, 5] {
        let (state_set, path_set) = assert_merged_state_set_agrees(
            &definition,
            &initial,
            &options(bound),
            &format!("max_breadth {bound}"),
        );
        assert_eq!(reaches_breadth_bound(&path_set.result), bound == 3);
        assert_eq!(
            reaches_breadth_bound(&state_set.result),
            bound == 3,
            "{:#?}",
            leaves(&state_set)
        );
    }
}

/// On a chain of converging diamonds the state-set run merges one arrival per diamond, and its
/// steps grow by a constant per diamond, where the path-set run's double.
#[test]
fn a_state_set_run_of_a_diamond_chain_pops_states_linearly() {
    let mut steps = Vec::new();
    for diamonds in 1..=6 {
        let definition = graph_definition(&diamond_chain(diamonds));
        let initial = pattern(&definition, &node("s0"));
        let (state_set, path_set) = assert_merged_state_set_agrees(
            &definition,
            &initial,
            &ExecutionOptions::default(),
            &format!("chain of {diamonds}"),
        );
        assert_eq!(state_set.merged, diamonds as u64);
        assert_eq!(path_set.result.leaves.len(), 1 << diamonds);
        steps.push(state_set.steps);
    }
    assert!(
        steps
            .windows(2)
            .all(|pair| pair[1] - pair[0] == steps[1] - steps[0]),
        "{steps:?}"
    );
}

/// The `Stuck` leaves of a merged state-set run carry exactly the states a final-state search
/// of the same initial state finds.
#[test]
fn a_merged_state_set_run_finds_the_final_states_a_search_finds() {
    for (name, rules) in [
        ("chain of 3", diamond_chain(3)),
        (
            "unequal diamond",
            [
                edge("a-b", "a", &node("b")),
                edge("b-c", "b", &node("c")),
                edge("c-d", "c", &node("d")),
                edge("a-e", "a", &node("e")),
                edge("e-d", "e", &node("d")),
            ]
            .concat(),
        ),
        (
            "distinct finals after a diamond",
            [
                edge("a-l", "a", &node("l")),
                edge("a-r", "a", &node("r")),
                edge("l-m", "l", &node("m")),
                edge("r-m", "r", &node("m")),
                edge("m-x", "m", &node("x")),
                edge("m-y", "m", &node("y")),
            ]
            .concat(),
        ),
    ] {
        let definition = graph_definition(&rules);
        let start = if name.starts_with("chain") { "s0" } else { "a" };
        let initial = pattern(&definition, &node(start));
        let state_set = run(
            &definition,
            &initial,
            &ExecutionOptions::default(),
            ResultModality::StateSet,
        );
        // The unequal diamond meets at two depths, so nothing merges there.
        assert_eq!(state_set.merged > 0, name != "unequal diamond", "{name}");
        let stuck = distinct(
            state_set
                .result
                .leaves
                .iter()
                .filter(|leaf| leaf.halt_reason == HaltReason::Stuck)
                .map(|leaf| leaf.pattern.clone()),
        );
        let searched = search_graph(
            &definition,
            initial.clone(),
            SearchOptions {
                search_type: SearchType::Final,
                ..SearchOptions::default()
            },
        );
        let found = distinct(searched.states.iter().map(|state| state.pattern.clone()));
        same_set(&stuck, &found, "final states", name);
    }
}

/// Converging paths that wrote the same bytes to a descriptor in different orders reach
/// different consoles and are not merged; paths that wrote the same bytes by different hooks
/// are, and both go on as one for two more steps.
#[test]
fn the_exploration_merge_compares_consoles_as_a_process_observes_them() {
    let writes = |left: &str, right: &str| {
        graph_definition(
            &[
                edge("a-l", "a", &node("l")),
                edge("a-r", "a", &node("r")),
                edge("l-m", "l", left),
                edge("r-m", "r", right),
                seq_edge("m-n", "m", &node("n")),
                edge("n-o", "n", &node("o")),
            ]
            .concat(),
        )
    };
    let two_writes = |first: &str, second: &str| {
        format!(
            r#"seq{{}}(write{{}}(\dv{{SortInt{{}}}}("1"), \dv{{SortString{{}}}}("{first}")), write{{}}(\dv{{SortInt{{}}}}("1"), \dv{{SortString{{}}}}("{second}")), \dv{{SortString{{}}}}("m"))"#
        )
    };
    let one_write = r#"seq{}(write{}(\dv{SortInt{}}("1"), \dv{SortString{}}("ab")), dotk{}(), \dv{SortString{}}("m"))"#;

    let interleaved = writes(&two_writes("a", "b"), &two_writes("b", "a"));
    let initial = pattern(&interleaved, &node("a"));
    let (state_set, _) = assert_merged_state_set_agrees(
        &interleaved,
        &initial,
        &ExecutionOptions::default(),
        "different orders",
    );
    assert_eq!(state_set.merged, 0);
    assert_eq!(state_set.result.leaves.len(), 2, "{:#?}", state_set.result);

    let split = writes(&two_writes("a", "b"), one_write);
    let initial = pattern(&split, &node("a"));
    let (state_set, path_set) = assert_merged_state_set_agrees(
        &split,
        &initial,
        &ExecutionOptions::default(),
        "same bytes, different calls",
    );
    assert_eq!(state_set.merged, 1);
    assert_eq!(state_set.result.leaves.len(), 1);
    assert_eq!(path_set.result.leaves.len(), 2);
    assert!(state_set.steps < path_set.steps);
}

/// An observed merged run returns the unobserved run's leaves, with the observations of each
/// leaf's own path.
#[test]
fn an_observed_merged_run_returns_the_unobserved_runs_leaves() {
    let definition = graph_definition(&diamond_chain(3));
    let initial = pattern(&definition, &node("s0"));
    let before = snapshot();
    let observed = execute_observed(
        &definition,
        initial.clone(),
        ExecutionOptions::default(),
        &ObservationOptions::all(),
    );
    let observed_merges = snapshot()
        .delta(&before)
        .get(Counter::ExecutionStatesMerged);
    let before = snapshot();
    let unobserved = execute(&definition, initial, ExecutionOptions::default());
    let unobserved_merges = snapshot()
        .delta(&before)
        .get(Counter::ExecutionStatesMerged);
    assert_eq!((observed_merges, unobserved_merges), (3, 3));
    let mut stripped = observed.clone();
    stripped.discarded.clear();
    for leaf in &mut stripped.leaves {
        assert_eq!(leaf.branch.len(), 6);
        leaf.branch.clear();
        leaf.observations.clear();
    }
    assert_eq!(stripped, unobserved);
}

/// Whether the trace is retained changes no leaf but its `trace`: merging never reads the trace,
/// and a halt that names the rule producing its state reads the path's latest rewrite, which a
/// path keeps when it keeps no other entry.
#[test]
fn a_merged_run_without_traces_reports_the_same_leaves() {
    let fixtures = [
        ("s0", diamond_chain(3)),
        (
            "a",
            [
                edge("a-l", "a", &node("l")),
                edge("a-r", "a", &node("r")),
                edge("l-m", "l", &node("m")),
                edge("r-m", "r", &node("m")),
                edge("m-undefined", "m", r#"node{}(\bottom{SortString{}}())"#),
            ]
            .concat(),
        ),
        (
            "a",
            [
                edge("a-l", "a", &node("l")),
                edge("a-r", "a", &node("r")),
                edge("l-m", "l", &logging("line", "x", "m")),
                edge("r-m", "r", &logging("line", "x", "m")),
                seq_edge("m-z", "m", &node("z")),
            ]
            .concat(),
        ),
    ];
    for (start, rules) in fixtures {
        let definition = graph_definition(&rules);
        let initial = pattern(&definition, &node(start));
        for result_modality in [ResultModality::StateSet, ResultModality::PathSet] {
            let traced = run(
                &definition,
                &initial,
                &ExecutionOptions::default(),
                result_modality,
            );
            let untraced = run(
                &definition,
                &initial,
                &ExecutionOptions {
                    retain_trace: false,
                    ..ExecutionOptions::default()
                },
                result_modality,
            );
            assert_eq!(
                (untraced.steps, untraced.merged),
                (traced.steps, traced.merged)
            );
            let mut stripped = traced.result.clone();
            for leaf in &mut stripped.leaves {
                leaf.trace.clear();
            }
            assert_eq!(untraced.result, stripped, "{start} {result_modality:?}");
        }
    }
}
