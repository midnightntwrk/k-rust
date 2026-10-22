//! Unit tests of the solve proposer: hole selection, the query's constraints, the mapping of a
//! model to hole values, and queries on the maze (FZ-13), whose cells `c7` (a nonlinear guard),
//! `u2` (a guard the path contradicts) and `u4` (a nonlinear guard without an integer solution)
//! are the stall benchmark's.

use std::sync::Arc;

use k_rust::{
    backend::{ConditionCollection, ExecuteRequest},
    kore::parser::parse_pattern,
};
use num_bigint::BigInt;

use super::*;
use crate::{
    holes::{HoleDecl, HoleLocation, SpanAddress},
    score::records,
    spec::{
        CallerIdentity, CampaignSpec, DEFAULT_REJECTION_CAP, Definitions, ProgramInput,
        ProgramSource, ProgramText, ProposerConfig,
    },
    target::{RuleMode, RuleRef, RuleTarget, Target, TargetKind},
    values::IntRange,
};

fn int(value: i64) -> Value {
    Value::Int(BigInt::from(value))
}

fn hole(sort: ValueSort, constraints: Constraints) -> SolveHole {
    SolveHole { sort, constraints }
}

fn free(sort: ValueSort) -> SolveHole {
    hole(sort, Constraints::default())
}

#[test]
fn only_int_and_bool_holes_whose_value_the_guard_read_are_symbolic() {
    let holes = vec![
        free(ValueSort::Int),
        free(ValueSort::Int),
        free(ValueSort::Bool),
        free(ValueSort::String),
        hole(
            ValueSort::Int,
            Constraints {
                choices: Some(vec![int(7)]),
                ..Constraints::default()
            },
        ),
        free(ValueSort::Int),
    ];
    let values = vec![
        int(8),
        int(3),
        Value::Bool(true),
        Value::String("8".into()),
        int(7),
        int(8),
    ];
    // The guard read 8, true and 7: both holes holding 8 are symbolic (the value does not say
    // which one reached the guard), the Bool hole too; the String hole is never symbolic, and
    // the hole fixed by a one-value choice set stays concrete.
    let read = vec![int(8), Value::Bool(true), int(7)];
    assert_eq!(symbolic_holes(&holes, &values, &read), vec![0, 2, 5]);
    // Nothing read, nothing symbolic.
    assert!(symbolic_holes(&holes, &values, &[]).is_empty());
    // A value of the other sort does not count: an `Int` hole is not read by `true`.
    assert!(symbolic_holes(&holes[..2], &values[..2], &[Value::Bool(true)]).is_empty());
}

#[test]
fn a_model_gives_the_values_of_the_query_variables_only() {
    let substitution = parse_pattern(concat!(
        r"\and{SortGeneratedTopCell{}}(",
        r#"\equals{SortInt{}, SortGeneratedTopCell{}}(VarKrustFuzzHole7:SortInt{}, \dv{SortInt{}}("1009")), "#,
        r"\and{SortGeneratedTopCell{}}(",
        r#"\equals{SortBool{}, SortGeneratedTopCell{}}(\dv{SortBool{}}("false"), VarKrustFuzzHole2:SortBool{}), "#,
        r"\and{SortGeneratedTopCell{}}(",
        r#"\equals{SortInt{}, SortGeneratedTopCell{}}(VarOther:SortInt{}, \dv{SortInt{}}("5")), "#,
        r#"\equals{SortKItem{}, SortGeneratedTopCell{}}(VarKrustFuzzHole3:SortKItem{}, inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("-12"))))))"#,
    ))
    .expect("the substitution parses");
    assert_eq!(
        model_values(&substitution),
        BTreeMap::from([(2, Value::Bool(false)), (3, int(-12)), (7, int(1009))])
    );
}

#[test]
fn declared_constraints_become_kore_predicates() {
    let range = Constraints {
        range: Some(IntRange {
            min: Some(BigInt::from(-5)),
            max: Some(BigInt::from(1000)),
        }),
        ..Constraints::default()
    };
    let predicates = constraint_predicates(4, Symbolic::Int, &range).expect("a KORE form");
    assert_eq!(predicates.len(), 2);
    let choices = Constraints {
        choices: Some(vec![Value::Bool(true), Value::Bool(false)]),
        ..Constraints::default()
    };
    let predicates = constraint_predicates(1, Symbolic::Bool, &choices).expect("a KORE form");
    assert_eq!(predicates.len(), 1);
    assert!(predicates[0].starts_with(r"\or"), "{predicates:?}");
    for predicate in constraint_predicates(4, Symbolic::Int, &range)
        .into_iter()
        .chain(constraint_predicates(1, Symbolic::Bool, &choices))
        .flatten()
    {
        parse_pattern(&predicate).unwrap_or_else(|error| panic!("{predicate}: {error}"));
    }
    assert_eq!(
        constraint_predicates(0, Symbolic::Int, &Constraints::default()),
        Some(Vec::new())
    );
}

/// The maze program `walk(1, 2, 7, 1050, 31337, 335002, 5005, h, i)`, which passes every guard
/// of the corridor before room `r6`, with the holes `A` (the first argument, which `c7` does
/// not read), `C` (the third), `D` (the fourth), `H` and `I` (the last two, at `h` and `i`), and
/// the rule target `target`.
fn maze_spec(h: i64, i: i64, target: &str) -> CampaignSpec {
    let name = "maze/solve.pgm";
    let text = format!("walk(1, 2, 7, 1050, 31337, 335002, 5005, {h}, {i})\n");
    let hole = |hole: &str, find: String, literal: String| HoleDecl {
        name: hole.into(),
        sort: "Int".into(),
        location: HoleLocation::Span(SpanAddress {
            program: name.into(),
            line: None,
            find,
            literal,
        }),
        constraints: Constraints::default(),
        allow_refused_sort: false,
    };
    CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(crate::support::MAZE.compiled().definition()),
            mutant: None,
        },
        program: ProgramInput::Source(ProgramSource {
            program: Some(ProgramText {
                name: name.into(),
                text,
                start_sort: "Pgm".into(),
            }),
            config_vars: Vec::new(),
        }),
        holes: vec![
            hole("A", "walk(1,".into(), "1".into()),
            hole("C", " 7,".into(), "7".into()),
            hole("D", " 1050,".into(), "1050".into()),
            hole("H", format!(" {h},"), h.to_string()),
            hole("I", format!(" {i})"), i.to_string()),
        ],
        target: Target {
            kind: TargetKind::Rule(RuleTarget {
                rule: RuleRef::Label(target.into()),
                mode: RuleMode::Fired,
            }),
            run_to_completion: false,
            negated_property: false,
        },
        options: CaseOptions::default(),
        proposers: ProposerConfig::default(),
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: 1,
        identity: CallerIdentity {
            k_rust_revision: "fz26-solve-unit".into(),
            thread_stack_size: None,
        },
    }
}

/// A solve proposer over `spec`'s holes, with `constraints` on hole `H`.
fn proposer(mut spec: CampaignSpec, constraints: Constraints) -> SolveProposer {
    spec.holes[3].constraints = constraints;
    let options = spec.options.clone();
    let bounds = spec.bounds;
    let builder = crate::engine::configuration_builder(spec).expect("the campaign builds");
    SolveProposer::new(builder, options, bounds, None, None)
}

/// The values of the holes `A`, `C`, `D`, `H` and `I`, in that order.
fn values(a_c_d: (i64, i64, i64), h: i64, i: i64) -> Vec<Value> {
    [a_c_d.0, a_c_d.1, a_c_d.2, h, i]
        .into_iter()
        .map(int)
        .collect()
}

/// The condition records of `c7` name the bindings of `H` and `I`: run the configuration of
/// `H = 8`, `I = 9` with `collectConditions` and select the symbolic holes from the record.
#[test]
fn the_records_of_c7_make_exactly_h_and_i_symbolic() {
    let spec = maze_spec(8, 9, "MAZE.c7");
    let builder = crate::engine::configuration_builder(spec).expect("the campaign builds");
    let case = values((1, 7, 1050), 8, 9);
    let configuration = builder
        .configuration(&case, &[])
        .expect("the case assembles");
    let mut request = ExecuteRequest::new(configuration);
    request.collect_coverage = true;
    request.collect_conditions = Some(ConditionCollection::new(["MAZE.c7"]));
    let result = crate::support::MAZE
        .compiled()
        .source_backend()
        .execute(request)
        .expect("the case runs");
    let conditions = result
        .coverage
        .and_then(|coverage| coverage.conditions)
        .expect("conditions were asked for");
    let guards = records::guards(&conditions);
    let entries: Vec<_> = guards.values().flatten().collect();
    assert_eq!(entries.len(), 1, "{guards:?}");
    assert!(entries[0].refuted);
    assert_eq!(entries[0].guard_values, vec![int(8), int(9)]);
    let holes: Vec<SolveHole> = builder
        .holes()
        .holes
        .iter()
        .map(|hole| free(hole.sort.clone()))
        .collect();
    assert_eq!(
        symbolic_holes(&holes, &case, &entries[0].guard_values),
        vec![3, 4]
    );
}

/// The catalog id of the maze rule labelled `label`.
fn rule_id(label: &str) -> String {
    crate::support::MAZE
        .compiled()
        .source_backend()
        .rule_catalog(None)
        .expect("the maze's catalog")
        .into_iter()
        .find(|entry| entry.label.as_deref() == Some(label))
        .unwrap_or_else(|| panic!("{label} in the catalog"))
        .id
}

fn query(rule: &str, case: Vec<Value>, symbolic: Vec<usize>) -> Query {
    Query {
        rule: rule_id(rule),
        values: case,
        symbolic,
        work: 9,
    }
}

/// The nonlinear `c7` (`H * I == 2021027`, `1 < H < I`; 2021027 is 1009 times 2003, both
/// prime): the model is the factorization, and the hole the guard does not read keeps its value.
#[test]
fn a_query_solves_the_nonlinear_guard_of_c7() {
    let mut solve = proposer(maze_spec(8, 9, "MAZE.c7"), Constraints::default());
    let candidate = solve
        .ask(&query("MAZE.c7", values((1, 7, 1050), 8, 9), vec![3, 4]))
        .unwrap_or_else(|| panic!("a candidate: {:?}", solve.totals));
    assert_eq!(candidate, values((1, 7, 1050), 1009, 2003));
    assert_eq!(solve.totals.candidates, 1);
    // The run's work and one model query are charged.
    let work = solve.take_extra_work();
    assert!(work > 1, "{work}");
    assert_eq!(work, solve.totals.work);
}

/// A declared range is conjoined: with `H <= 1000` no factorization is left, with `H` in
/// `1009 ..= 1009` the model keeps it.
#[test]
fn a_query_conjoins_the_holes_declared_constraints() {
    let range = |min: i64, max: i64| Constraints {
        range: Some(IntRange {
            min: Some(BigInt::from(min)),
            max: Some(BigInt::from(max)),
        }),
        ..Constraints::default()
    };
    let mut solve = proposer(maze_spec(8, 9, "MAZE.c7"), range(2, 1000));
    assert_eq!(
        solve.ask(&query("MAZE.c7", values((1, 7, 1050), 8, 9), vec![3, 4])),
        None
    );
    // No branch applies `c7` under `H <= 1000`: the run finds no path (no candidate either way;
    // the clock-free solver makes the answer the same on every run).
    assert_eq!(
        (solve.totals.no_path, solve.totals.candidates),
        (1, 0),
        "{:?}",
        solve.totals
    );
    let mut solve = proposer(maze_spec(8, 9, "MAZE.c7"), range(1009, 1009));
    assert_eq!(
        solve.ask(&query("MAZE.c7", values((1, 7, 1050), 1009, 9), vec![3, 4])),
        Some(values((1, 7, 1050), 1009, 2003))
    );
}

/// The negative controls give no candidate, deterministically: `u4`'s `C * C == 2` has no
/// integer solution, and
/// `u2`'s `D < 50` contradicts `c4`'s `1000 < D < 1100` on the path to its room.
#[test]
fn a_query_finds_no_candidate_for_the_unreachable_cells() {
    let mut solve = proposer(maze_spec(8, 9, "MAZE.u4"), Constraints::default());
    assert_eq!(
        solve.ask(&query("MAZE.u4", values((1, 3, 1050), 8, 9), vec![1])),
        None
    );
    // No path applies `u4` (`C * C == 2`) within the run's budget.
    assert_eq!(
        (solve.totals.no_path, solve.totals.candidates),
        (1, 0),
        "{:?}",
        solve.totals
    );
    let mut solve = proposer(maze_spec(8, 9, "MAZE.u2"), Constraints::default());
    assert_eq!(
        solve.ask(&query("MAZE.u2", values((1, 7, 1050), 8, 9), vec![2])),
        None
    );
    assert_eq!(solve.totals.no_path, 1, "{:?}", solve.totals);
}

/// The proposer is ready only after a stall on a blocked case, asks each query once, and moves
/// on to the next pending query when the best one is settled.
#[test]
fn the_proposer_asks_after_a_stall_never_twice_and_moves_on() {
    use crate::{
        exec::OutcomeClass,
        score::{Blocked, Distance, Guard, Level},
    };
    let mut solve = proposer(maze_spec(8, 9, "MAZE.c7"), Constraints::default());
    let blocked = Observation {
        case: 0,
        class: OutcomeClass::Miss,
        applied: Vec::new(),
        matched: Vec::new(),
        applied_counts: std::collections::BTreeMap::new(),
        work: 9,
        score: Some(Score {
            level: Level::At(0),
            guard: Guard::Defined(Distance::normalized(5u32.into())),
        }),
        reads: Vec::new(),
        blocked: Some(Blocked {
            rule: rule_id("MAZE.c7"),
            distance: 0,
            guard: Guard::Defined(Distance::normalized(5u32.into())),
            values: vec![int(8), int(9)],
        }),
        comparisons: Vec::new(),
    };
    let proposal = Proposal::plain(Origin::Explicit, values((1, 7, 1050), 8, 9));
    let unscored = Observation {
        score: None,
        blocked: None,
        class: OutcomeClass::Rejected,
        ..blocked.clone()
    };
    solve.observe_all(&proposal, &blocked);
    assert!(!solve.ready());
    for _ in 1..SOLVE_STALL_CASES {
        solve.observe_all(&proposal, &unscored);
        assert!(!solve.ready());
    }
    solve.observe_all(&proposal, &unscored);
    assert!(solve.ready());
    let mut rng = <rand_chacha::ChaCha20Rng as rand::SeedableRng>::from_seed([0; 32]);
    let candidate = solve
        .propose(&mut ProposalContext { rng: &mut rng })
        .expect("a candidate");
    assert_eq!(candidate.origin, Origin::Scheduled(ProposerKind::Solve));
    assert_eq!(candidate.values, values((1, 7, 1050), 1009, 2003));
    // The same blocked case asks the same question: not again.
    solve.observe_all(&proposal, &unscored);
    assert!(!solve.ready());
    // A worse-ranked blocked case with another value of a concrete hole asks another query, at
    // once while the stall runs: a settled query does not silence the proposer.
    let other = Proposal::plain(Origin::Explicit, values((2, 7, 1050), 8, 9));
    let worse = Observation {
        score: Some(Score {
            level: Level::At(0),
            guard: Guard::Defined(Distance::normalized(6u32.into())),
        }),
        blocked: Some(Blocked {
            guard: Guard::Defined(Distance::normalized(6u32.into())),
            ..blocked.blocked.clone().expect("blocked")
        }),
        ..blocked.clone()
    };
    solve.observe_all(&other, &worse);
    assert!(solve.ready());
    assert_eq!(
        solve.ready.as_ref().map(|query| query.values.clone()),
        Some(values((2, 7, 1050), 8, 9))
    );
    // A better score restarts the stall.
    let better = Observation {
        score: Some(Score {
            level: Level::At(0),
            guard: Guard::Defined(Distance::normalized(4u32.into())),
        }),
        ..worse.clone()
    };
    solve.observe_all(&other, &better);
    assert!(!solve.ready());
    for _ in 0..SOLVE_STALL_CASES {
        solve.observe_all(&proposal, &unscored);
    }
    assert!(solve.ready());
}

/// A model that binds no symbolic hole gives no candidate (it would only give the blocked case
/// back); one that binds some keeps the free ones' values.
#[test]
fn a_model_that_binds_no_symbolic_hole_gives_no_candidate() {
    let query = Query {
        rule: "r".into(),
        values: values((1, 7, 1050), 8, 9),
        symbolic: vec![3, 4],
        work: 9,
    };
    assert_eq!(apply_model(&query, &BTreeMap::new()), None);
    // A binding of a hole that is not symbolic is no binding.
    assert_eq!(apply_model(&query, &BTreeMap::from([(0, int(5))])), None);
    assert_eq!(
        apply_model(&query, &BTreeMap::from([(4, int(2003))])),
        Some(values((1, 7, 1050), 8, 2003))
    );
}

/// A sort hooked to `INT.Int` under its own name keeps its domain values at its own KORE sort,
/// so a hole of it is never given a `SortInt` variable.
#[test]
fn a_renamed_int_sort_is_not_symbolic() {
    let renamed = free(ValueSort::Renamed {
        sort: "MyInt".into(),
        kore_sort: "SortMyInt".into(),
        base: Box::new(ValueSort::Int),
    });
    assert_eq!(renamed.symbolic(), None);
    assert!(symbolic_holes(&[renamed], &[int(8)], &[int(8)]).is_empty());
}

/// A run the per-case safety limit stops is settled and charged: it is asked once, its query
/// does not come back at every draw, and its work (at least 1) counts in the share. The 1 ms limit
/// stops the `c7` query, which takes hundreds of milliseconds (building its backends alone takes
/// tens), before it answers.
#[test]
fn a_run_the_safety_limit_stops_is_settled_and_charged() {
    use crate::{
        exec::OutcomeClass,
        score::{Blocked, Distance, Guard, Level},
    };
    let mut spec = maze_spec(8, 9, "MAZE.c7");
    spec.options.safety_limit_ms = Some(1);
    let mut solve = proposer(spec, Constraints::default());
    let guard = Guard::Defined(Distance::normalized(5u32.into()));
    let blocked = Observation {
        case: 0,
        class: OutcomeClass::Miss,
        applied: Vec::new(),
        matched: Vec::new(),
        applied_counts: std::collections::BTreeMap::new(),
        work: 9,
        score: Some(Score {
            level: Level::At(0),
            guard: guard.clone(),
        }),
        reads: Vec::new(),
        blocked: Some(Blocked {
            rule: rule_id("MAZE.c7"),
            distance: 0,
            guard,
            values: vec![int(8), int(9)],
        }),
        comparisons: Vec::new(),
    };
    let proposal = Proposal::plain(Origin::Explicit, values((1, 7, 1050), 8, 9));
    let unscored = Observation {
        score: None,
        blocked: None,
        class: OutcomeClass::Rejected,
        ..blocked.clone()
    };
    solve.observe_all(&proposal, &blocked);
    for _ in 0..SOLVE_STALL_CASES {
        solve.observe_all(&proposal, &unscored);
    }
    let mut rng = <rand_chacha::ChaCha20Rng as rand::SeedableRng>::from_seed([0; 32]);
    for _ in 0..5 {
        if solve.ready() {
            assert!(
                solve
                    .propose(&mut ProposalContext { rng: &mut rng })
                    .is_none()
            );
        }
        // The same blocked case again: its query is settled, so it is not ready again.
        solve.observe_all(&proposal, &blocked);
        solve.observe_all(&proposal, &unscored);
    }
    assert_eq!(solve.totals.attempts, 1, "{:?}", solve.totals);
    assert_eq!(
        (solve.totals.failed, solve.totals.outside_determinism),
        (1, 1),
        "{:?}",
        solve.totals
    );
    assert!(solve.take_extra_work() >= 1, "{:?}", solve.totals);
    assert!(solve.totals.work >= 1, "{:?}", solve.totals);
}
