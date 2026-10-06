//! VI-06: the variable-identity audit attacks at the native level (README 12 as amended by
//! README 16, k-rust `927b9ce6`, `VARIABLE_IDENTITY == 3`). Names are read verbatim and
//! printed injectively, and one counter per request skips every request spelling, so a
//! test's initial variable is one variable whatever it is spelled. Each attack runs the
//! neutral naming and forged namings and asserts that the forged spellings change no leaf,
//! no feasibility, no discard and no certificate. The campaign-level attacks are the
//! `audit_vi_at*` tests of kink-campaign's `coupled.rs`.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::{
    collections::{BTreeMap, BTreeSet},
    time::Duration,
};

use k_rust::backend::{Backend, BackendError, BackendOptions};
use k_rust::definition::AttributeKey;
use k_rust::kast::{Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kore::{
    ast::{Pattern, Variable, VariableKind},
    codec,
};
use k_rust_backend::externalize;
use kink_native::execution::{ExecutionAdapter, ExecutionBudget, HaltClass, SolverProfile};
use kink_native::execution_difference::{
    DifferenceCertificate, NotProvedReason, certify_difference, definition_facts,
};
use kink_native::{
    NativeValidator, bridge,
    feasibility::{LeafFeasibility, TestInitialState},
};
use kink_patch::{Edit, Patch, TermRef};
use kink_pattern::RelationDecider;

const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(30),
    max_simplification_iterations: 1000,
    max_depth: None,
    max_breadth: None,
};

type Row = (HaltClass, LeafFeasibility, Option<bridge::DiscardReason>);

/// One leaf as a naming must leave it: its halt, feasibility and discard, and the number of
/// distinct free variables of its state (a merge of two variables would lower it).
type Summary = (Row, usize);

fn seq(head: Pattern, tail: Pattern) -> Pattern {
    support::app("Lblseq", vec![head, tail])
}

fn op(symbol: &str, arguments: Vec<Pattern>) -> Pattern {
    support::app(&format!("Lbl{symbol}"), arguments)
}

fn backend(validator: &NativeValidator, patch: Option<&Patch>, module: &str) -> Backend {
    let side = match patch {
        Some(patch) => validator.validate(patch).expect("mutant compiles"),
        None => validator.compile_baseline().expect("baseline compiles"),
    };
    Backend::new(
        &side.artifacts().definition_kore,
        module,
        BackendOptions::default(),
    )
    .expect("backend")
}

fn state_of(value: &serde_json::Value) -> Pattern {
    codec::from_value(value).expect("leaf KORE reads")
}

fn summaries(backend: &mut Backend, initial: &Pattern) -> Vec<Summary> {
    ExecutionAdapter::with_profile(SolverProfile::BUILD)
        .execute(backend, initial, BUDGET)
        .expect("event-free execution")
        .leaves()
        .iter()
        .map(|leaf| {
            (
                (leaf.halt, leaf.feasibility, bridge::discarded(leaf)),
                state_of(&leaf.branch.state).free_variables().len(),
            )
        })
        .collect()
}

/// Every state of every path of a stepped run of `initial`.
fn stepped_states(backend: &mut Backend, initial: &Pattern) -> Vec<Vec<Pattern>> {
    ExecutionAdapter::with_profile(SolverProfile::BUILD)
        .execute_steps(backend, initial, BUDGET)
        .expect("stepped execution")
        .expect("step states decode")
        .states
}

/// `pattern` with its free element variables renamed by `renaming` (KORE level: the
/// spelling reaches k-rust exactly as written).
fn renamed(pattern: &Pattern, renaming: &BTreeMap<String, String>) -> Pattern {
    fn walk(value: &mut serde_json::Value, renaming: &BTreeMap<String, String>) {
        match value {
            serde_json::Value::Object(map) => {
                if map.get("tag").and_then(serde_json::Value::as_str) == Some("EVar")
                    && let Some(serde_json::Value::String(name)) = map.get_mut("name")
                    && let Some(to) = renaming.get(name.as_str())
                {
                    name.clone_from(to);
                }
                map.values_mut().for_each(|value| walk(value, renaming));
            }
            serde_json::Value::Array(items) => {
                items.iter_mut().for_each(|value| walk(value, renaming));
            }
            _ => {}
        }
    }
    let mut value = codec::to_value(pattern).expect("pattern encodes");
    walk(&mut value, renaming);
    let renamed: Pattern = codec::from_value(&value).expect("pattern decodes");
    assert_eq!(
        renamed.free_variables().len(),
        pattern.free_variables().len(),
        "a renaming keeps the variables apart"
    );
    renamed
}

/// The namings of `initial` that spell its free variables with `spellings`, one per rotation.
fn rotations(initial: &Pattern, spellings: &[&str]) -> Vec<BTreeMap<String, String>> {
    let names = initial
        .free_variables()
        .into_iter()
        .map(|variable| variable.name)
        .collect::<BTreeSet<_>>();
    assert!(names.len() <= spellings.len(), "{names:?}");
    (0..spellings.len())
        .map(|rotation| {
            names
                .iter()
                .enumerate()
                .map(|(index, name)| {
                    (
                        name.clone(),
                        spellings[(index + rotation) % spellings.len()].to_owned(),
                    )
                })
                .collect()
        })
        .collect()
}

fn int(name: &str) -> Pattern {
    support::var(name, "SortInt")
}

/// The VI-AT2 and VI-AT3 programs: (fixture, module, initial state), each with free
/// variables next to rules that narrow, mint, or decide by a solver.
fn programs() -> Vec<(&'static str, &'static str, Pattern)> {
    let nat = |name: &str| support::var(name, "SortNat");
    let memory = |address: Pattern, value: Pattern, load: Pattern, loaded: Pattern| {
        seq(
            op("write", vec![op("addr", vec![address]), value]),
            seq(
                op("load", vec![op("addr", vec![load]), loaded]),
                op("halt", vec![]),
            ),
        )
    };
    vec![
        (
            "symmem.k",
            "SYMMEM",
            support::initial_state(memory(nat("X"), nat("V"), nat("Y"), nat("W")), "SortProg"),
        ),
        (
            "guardedmem.k",
            "GUARDEDMEM",
            support::initial_state(memory(int("X"), int("V"), int("Y"), int("W")), "SortProg"),
        ),
        (
            "conflate.k",
            "CONFLATE",
            support::initial_state(
                seq(
                    op("check", vec![int("A")]),
                    seq(
                        op("check2", vec![int("B")]),
                        seq(
                            op("go", vec![support::var("X", "SortBox")]),
                            op("done", vec![]),
                        ),
                    ),
                ),
                "SortProg",
            ),
        ),
        (
            "conflate2.k",
            "CONFLATE2",
            support::initial_state(
                seq(
                    op("check", vec![int("A")]),
                    seq(op("mk", vec![]), op("done", vec![])),
                ),
                "SortProg",
            ),
        ),
        (
            "conflate3.k",
            "CONFLATE3",
            support::initial_state(
                seq(
                    op("new1", vec![]),
                    seq(
                        op("go", vec![support::var("X", "SortBox")]),
                        op("done", vec![]),
                    ),
                ),
                "SortProg",
            ),
        ),
    ]
}

/// The neutral leaf rows of `programs()`, measured (both profiles).
fn neutral_rows(fixture: &str) -> Vec<Row> {
    use HaltClass::{Indeterminate, Stuck};
    use LeafFeasibility::{Solver, Syntactic, Unknown};
    let z3 = cfg!(feature = "z3");
    match fixture {
        "symmem.k" => vec![(Stuck, Syntactic, None)],
        "guardedmem.k" if z3 => vec![
            (Stuck, Solver, None),
            (Stuck, Solver, None),
            (Stuck, Solver, None),
        ],
        "conflate.k" if z3 => vec![
            (Stuck, Unknown, None),
            (Stuck, Unknown, None),
            (Stuck, Unknown, None),
            (Stuck, Solver, None),
            (Stuck, Solver, None),
        ],
        "conflate2.k" if z3 => vec![
            (Stuck, Unknown, None),
            (Stuck, Unknown, None),
            (Stuck, Solver, None),
        ],
        "conflate3.k" if z3 => vec![(Stuck, Unknown, None); 3],
        _ => vec![(Indeterminate, Syntactic, None)],
    }
}

fn assert_naming_invariant(spellings: &[&str], context: &str) {
    for (fixture, module, initial) in programs() {
        let validator = NativeValidator::bind(support::load(fixture), CompileOptions::default());
        let mut backend = backend(&validator, None, module);
        let neutral = summaries(&mut backend, &initial);
        eprintln!("{context} {fixture} neutral {neutral:?}");
        assert_eq!(
            neutral.iter().map(|(row, _)| *row).collect::<Vec<_>>(),
            neutral_rows(fixture),
            "{context} {fixture} neutral rows"
        );
        for naming in rotations(&initial, spellings) {
            let forged = renamed(&initial, &naming);
            assert_eq!(
                summaries(&mut backend, &forged),
                neutral,
                "{context} {fixture} naming {naming:?}"
            );
        }
    }
}

const OLD_MINT_SPELLINGS: [&str; 5] = [
    "ExVarI0",
    "ExVarI10",
    "RuleVarX",
    "X'Bang'apart1",
    "Var'Ques'X0",
];

const NEW_MINT_SPELLINGS: [&str; 5] = [
    "Ex-hVarI-b0",
    "Ex-hFrame-b0",
    "X-bapart0",
    "Ex-hVarI1-b0",
    "Ex-hVarI-b1",
];

/// VI-AT2: initial names spelled like pre-VI mints (`ExVarI0`, `ExVarI10`, `RuleVarX`,
/// `X'Bang'apart1`, `Var'Ques'X0`) on symmem, guardedmem, conflate, conflate2 and conflate3:
/// every leaf, Unsat, discard and free-variable count equals the neutral-name run, under
/// every rotation of the spellings. No leaf is Unsat or discarded in either profile.
#[test]
fn audit_vi_at2_old_mint_spellings_equal_the_neutral_run() {
    assert_naming_invariant(&OLD_MINT_SPELLINGS, "AT2");
}

/// VI-AT3 (leaves): initial names spelled like v3 printed mints (`Ex-hVarI-b0` is
/// `Ex#VarI!0` printed, the spelling of conflate's narrowing mint for `I`) next to that
/// narrowing: every leaf equals the neutral-name run.
#[test]
fn audit_vi_at3_new_mint_spellings_equal_the_neutral_run() {
    assert_naming_invariant(&NEW_MINT_SPELLINGS, "AT3");
}

/// Free variables of `pattern` by name: two entries under one name are two variables printed
/// alike.
fn variables_by_name(pattern: &Pattern) -> BTreeMap<String, BTreeSet<Variable>> {
    let mut names = BTreeMap::<String, BTreeSet<Variable>>::new();
    for variable in pattern.free_variables() {
        names
            .entry(variable.name.clone())
            .or_default()
            .insert(variable);
    }
    names
}

/// VI-AT3 (names and certificate): with conflate's initial variables spelled `Ex-hVarI-b0`
/// and `Ex-hVarI-b1` (the printed spellings of its first two narrowing mints) or
/// `Ex-hFrame-b0`/`X-bapart0`, no leaf or stepped state prints two variables alike, every
/// variable spelled like an initial variable is that variable, the mints are never minted
/// with a request spelling, and the certificate against conflatem (goPos and goNeg merged,
/// identical on every ground instance) stays `NotProved(NoWitness)` for every naming.
#[test]
fn audit_vi_at3_new_mint_spellings_are_never_reminted() {
    let validator = NativeValidator::bind(support::load("conflate.k"), CompileOptions::default());
    let merged = NativeValidator::bind(support::load("conflatem.k"), CompileOptions::default());
    let mut baseline = backend(&validator, None, "CONFLATE");
    let mut mutant = backend(&merged, None, "CONFLATEM");
    let facts = definition_facts(&mut baseline).expect("baseline facts");
    let mutant_facts = definition_facts(&mut mutant).expect("mutant facts");
    let program = |a: &str, b: &str, x: &str| {
        support::initial_state(
            seq(
                op("check", vec![int(a)]),
                seq(
                    op("check2", vec![int(b)]),
                    seq(
                        op("go", vec![support::var(x, "SortBox")]),
                        op("done", vec![]),
                    ),
                ),
            ),
            "SortProg",
        )
    };
    let mut minted = BTreeSet::new();
    for (a, b, x) in [
        ("A", "B", "X"),
        ("Ex-hVarI-b0", "Ex-hVarI-b1", "X"),
        ("Ex-hVarI-b0", "Ex-hVarI1-b0", "Ex-hVarI-b2"),
        ("Ex-hFrame-b0", "X-bapart0", "Ex-hVarI-b0"),
    ] {
        let initial = program(a, b, x);
        let initial_variables = initial.free_variables();
        let states = stepped_states(&mut baseline, &initial);
        assert_eq!(states.len(), if cfg!(feature = "z3") { 5 } else { 1 });
        for state in states.iter().flatten() {
            for (name, variables) in variables_by_name(state) {
                assert_eq!(variables.len(), 1, "{a} {b} {x}: {name} printed twice");
                let variable = variables.first().expect("one variable");
                if let Some(initial) = initial_variables.iter().find(|v| v.name == name) {
                    assert_eq!(
                        variable, initial,
                        "{a} {b} {x}: {name} is the initial variable"
                    );
                } else {
                    minted.insert(name);
                }
            }
        }
        let baseline_sequences = ExecutionAdapter::with_profile(SolverProfile::BUILD)
            .execute_steps(&mut baseline, &initial, BUDGET)
            .expect("baseline run")
            .expect("baseline steps")
            .certificate_sequences()
            .expect("baseline sequences");
        let mutant_sequences = ExecutionAdapter::with_profile(SolverProfile::BUILD)
            .execute_steps(&mut mutant, &initial, BUDGET)
            .expect("mutant run")
            .expect("mutant steps")
            .certificate_sequences()
            .expect("mutant sequences");
        assert_eq!(
            certify_difference(
                &mut baseline,
                TestInitialState::of_test(&initial),
                &facts,
                &mutant_facts,
                &baseline_sequences,
                &mutant_sequences,
            ),
            DifferenceCertificate::NotProved(NotProvedReason::NoWitness),
            "{a} {b} {x}"
        );
    }
    eprintln!("AT3 conflate mints: {minted:?}");
    if cfg!(feature = "z3") {
        assert!(
            minted.iter().any(|name| name.starts_with("Ex-hVarI-b")),
            "conflate narrows X with a minted I: {minted:?}"
        );
    }
}

/// freshgen's two writes, `write(addr(X), 5); write(addr(Y), 6); load(addr(X), 7); halt`.
fn two_writes(x: &str, y: &str) -> Pattern {
    support::initial_state(
        seq(
            op("write", vec![op("addr", vec![int(x)]), support::int(5)]),
            seq(
                op("write", vec![op("addr", vec![int(y)]), support::int(6)]),
                seq(
                    op("load", vec![op("addr", vec![int(x)]), support::int(7)]),
                    op("halt", vec![]),
                ),
            ),
        ),
        "SortProg",
    )
}

/// The free names of every state of `path` that are not initial names, and whether a name
/// that left the path's state came back later.
fn reappearing(path: &[Pattern], initial: &BTreeSet<String>) -> Vec<String> {
    let mut gone = BTreeSet::new();
    let mut previous = BTreeSet::new();
    let mut back = Vec::new();
    for state in path {
        let names = state
            .free_variables()
            .into_iter()
            .map(|variable| variable.name)
            .filter(|name| !initial.contains(name))
            .collect::<BTreeSet<_>>();
        back.extend(names.intersection(&gone).cloned());
        gone.extend(previous.difference(&names).cloned());
        previous = names;
    }
    back
}

/// The non-initial free names of every state of `paths`.
fn minted_names(paths: &[Vec<Pattern>], initial: &BTreeSet<String>) -> BTreeSet<String> {
    paths
        .iter()
        .flatten()
        .flat_map(Pattern::free_variables)
        .map(|variable| variable.name)
        .filter(|name| !initial.contains(name))
        .collect()
}

/// VI-AT5: freshgen mints `?T` once per write, and `stamp` drops it, so on one path the
/// existential leaves the state twice. With initial variables spelled like those mints
/// (`Ex-hVar'Ques'T-b0` is `Ex#Var'Ques'T!0` printed), every leaf equals the neutral-name
/// run, no minted name reappears after leaving the state, and no mint is spelled like an
/// initial variable: the counter skips the request's spellings.
#[test]
fn audit_vi_at5_reused_existential_is_never_a_request_name() {
    let validator = NativeValidator::bind(support::load("freshgen.k"), CompileOptions::default());
    let mut baseline = backend(&validator, None, "FRESHGEN");
    let neutral = summaries(&mut baseline, &two_writes("X", "Y"));
    eprintln!("AT5 neutral {neutral:?}");
    for (x, y) in [
        ("X", "Y"),
        ("X", "Ex-hVar'Ques'T-b0"),
        ("Ex-hVar'Ques'T-b0", "Ex-hVar'Ques'T-b1"),
        ("Ex-hVar'Ques'T-b1", "Ex-hVar'Ques'T-b2"),
    ] {
        let initial = two_writes(x, y);
        assert_eq!(summaries(&mut baseline, &initial), neutral, "{x} {y}");
        let names = [x.to_owned(), y.to_owned()].into_iter().collect();
        let paths = stepped_states(&mut baseline, &initial);
        for path in &paths {
            assert_eq!(reappearing(path, &names), Vec::<String>::new(), "{x} {y}");
        }
        let minted = minted_names(&paths, &names);
        eprintln!("AT5 {x} {y}: minted {minted:?}");
        assert!(minted.is_disjoint(&names));
        if cfg!(feature = "z3") {
            assert!(
                minted
                    .iter()
                    .any(|name| name.starts_with("Ex-hVar'Ques'T-b")),
                "{x} {y}: the writes mint ?T: {minted:?}"
            );
        }
    }
}

/// freshgen's guard split (AT1, without the rename): `write` keeps `A >Int 0` and an inserted
/// copy takes `A ==Int 0`, so a symbolic write has one more branch that mints `?T`.
fn freshgen_split(validator: &NativeValidator) -> Patch {
    let baseline = validator.baseline();
    let label = support::rule(baseline, "FRESHGEN.write");
    let requires = TermRef::new(label.clone(), [1]);
    let address = baseline
        .term(&TermRef::new(label.clone(), [0, 0, 0, 0, 0]))
        .expect("address")
        .clone();
    let token = Term::Token {
        token: "0".into(),
        sort: Sort::new("Int"),
    };
    let mut zero = baseline.sentence(&label).expect("write").clone();
    for key in [
        AttributeKey::Label,
        AttributeKey::UniqueId,
        AttributeKey::Origin,
        AttributeKey::Location,
        AttributeKey::Source,
        AttributeKey::SourceId,
        AttributeKey::SentenceStartOffset,
        AttributeKey::SentenceEndOffset,
        AttributeKey::ContentStartLine,
        AttributeKey::ContentStartColumn,
        AttributeKey::ContentStartOffset,
    ] {
        zero.attributes_mut().remove(key.as_str());
    }
    if let k_rust::definition::Sentence::Rule { requires, .. } = &mut zero {
        *requires = Term::apply("_==Int_", vec![address.clone(), token.clone()]);
    }
    Patch::new(vec![
        Edit::ReplaceTerm {
            expected: baseline.term(&requires).expect("requires").clone(),
            replacement: Term::apply("_>Int_", vec![address, token]),
            at: requires,
        },
        Edit::InsertSentence {
            position: kink_patch::InsertPosition::After(label),
            ordinal: 0,
            sentence: zero,
        },
    ])
    .expect("split")
}

/// VI-AT6: the guard split's extra branch also mints `?T` from the request's one counter, so
/// the split's paths carry other mint counters than the baseline's (the shift is live), and
/// the leaves keep their halts, feasibilities and discards in the same number per variable
/// count. The campaign-level half (`coupled.rs` `audit_vi_at6_counter_shift_is_not_a_kill`)
/// shows that the shift kills nothing.
#[test]
fn audit_vi_at6_counter_shift_is_live() {
    let validator = NativeValidator::bind(support::load("freshgen.k"), CompileOptions::default());
    let mut baseline = backend(&validator, None, "FRESHGEN");
    let mut split = backend(&validator, Some(&freshgen_split(&validator)), "FRESHGEN");
    let initial = two_writes("X", "Y");
    let names = ["X".to_owned(), "Y".to_owned()].into_iter().collect();
    let baseline_minted = minted_names(&stepped_states(&mut baseline, &initial), &names);
    let split_minted = minted_names(&stepped_states(&mut split, &initial), &names);
    eprintln!("AT6 baseline minted {baseline_minted:?}, split minted {split_minted:?}");
    let baseline_leaves = summaries(&mut baseline, &initial);
    let split_leaves = summaries(&mut split, &initial);
    eprintln!("AT6 baseline leaves {baseline_leaves:?}, split leaves {split_leaves:?}");
    if cfg!(feature = "z3") {
        assert_ne!(
            baseline_minted, split_minted,
            "the split shifts the counters"
        );
    }
}

/// VI-AT8: a set variable spelled like a printed marked set variable, `@Rule-hM` (v3 prints
/// `@Rule#M` so), reads back verbatim as a set variable of that name and prints unchanged.
/// A test may hold it: execution admits the state and stops at one Indeterminate leaf, so the
/// path is incomplete (kink-campaign `audit_vi_at8_set_variable_in_a_test_is_not_killed`).
#[test]
fn audit_vi_at8_set_variable_spelling_reads_back_verbatim() {
    let validator = NativeValidator::bind(support::load("guardedmem.k"), CompileOptions::default());
    let mut guarded = backend(&validator, None, "GUARDEDMEM");
    let set = Pattern::Variable(Variable {
        kind: VariableKind::Set,
        name: "@Rule-hM".to_owned(),
        sort: k_rust::kompile::initial_configuration::kore_sort("SortInt"),
    });
    let initial = support::initial_state(
        seq(
            op("write", vec![op("addr", vec![int("X")]), set.clone()]),
            op("halt", vec![]),
        ),
        "SortProg",
    );
    guarded
        .with_solver(None, |definition, _| {
            let internal = definition
                .admit_unverified(&initial, &[])
                .internalize_pattern()
                .expect("a set variable identifier is read");
            let variables = internal
                .term
                .attributes()
                .variables
                .iter()
                .map(|variable| (variable.name.to_string(), variable.kind))
                .collect::<BTreeSet<_>>();
            assert!(
                variables.contains(&(
                    "@Rule-hM".to_owned(),
                    k_rust_backend::term::VariableKind::Set
                )),
                "{variables:?}"
            );
            let printed = externalize::constrained_pattern(&internal);
            assert_eq!(printed.free_variables(), initial.free_variables());
            Ok::<_, BackendError>(())
        })
        .expect("set variable round trip");
    // Reachable as a test variable: the adapter admits it (only element variables are checked
    // for inhabitation), and the run is one Indeterminate leaf (the rule binds `V` to the set
    // variable but the step is undecided), so the path is incomplete in both profiles.
    let run = ExecutionAdapter::with_profile(SolverProfile::BUILD)
        .execute(&mut guarded, &initial, BUDGET)
        .expect("a set variable is admitted");
    assert_eq!(
        run.leaves()
            .iter()
            .map(|leaf| (leaf.halt, leaf.feasibility))
            .collect::<Vec<_>>(),
        [(HaltClass::Indeterminate, LeafFeasibility::Unknown)]
    );
}

/// conflate's `go` rules with their variable `I` renamed to `to`.
fn conflate_go_renamed(validator: &NativeValidator, to: &str) -> Patch {
    let baseline = validator.baseline();
    let mut edits = Vec::new();
    for rule in ["CONFLATE.goPos", "CONFLATE.goNeg"] {
        for path in [[0u32], [1]] {
            let at = TermRef::new(support::rule(baseline, rule), path);
            let expected = baseline.term(&at).expect("term").clone();
            let mut replacement = expected.clone();
            assert!(
                rename_variable(&mut replacement, "I", to) > 0,
                "{rule} {path:?}"
            );
            edits.push(Edit::ReplaceTerm {
                at,
                expected,
                replacement,
            });
        }
    }
    Patch::new(edits).expect("rename")
}

fn rename_variable(term: &mut Term, from: &str, to: &str) -> usize {
    match term {
        Term::Variable { name, .. } if name == from => {
            *name = to.into();
            1
        }
        Term::Rewrite { left, right } => {
            rename_variable(left, from, to) + rename_variable(right, from, to)
        }
        Term::Apply { arguments, .. } => arguments
            .iter_mut()
            .map(|argument| rename_variable(argument, from, to))
            .sum(),
        Term::Annotated { term, .. } => rename_variable(term, from, to),
        _ => 0,
    }
}

/// VI-AT10 (KK-82 review R1-1): a test whose path condition names `Rule-hVarI`, the printed
/// spelling of conflate's rule variable `Rule#VarI` that `go` narrows, has the same leaves as
/// the neutral naming, on the baseline and on the alpha-renamed mutant (`I` to `K`).
#[test]
fn audit_vi_at10_forged_rule_variable_keeps_the_leaves() {
    let validator = NativeValidator::bind(support::load("conflate.k"), CompileOptions::default());
    let mut baseline = backend(&validator, None, "CONFLATE");
    let mut mutant = backend(
        &validator,
        Some(&conflate_go_renamed(&validator, "K")),
        "CONFLATE",
    );
    let program = |n: &str| {
        support::initial_state(
            seq(
                op("check", vec![int(n)]),
                seq(
                    op("go", vec![support::var("X", "SortBox")]),
                    op("done", vec![]),
                ),
            ),
            "SortProg",
        )
    };
    let neutral = summaries(&mut baseline, &program("N"));
    eprintln!("AT10 neutral {neutral:?}");
    assert_eq!(neutral.len(), if cfg!(feature = "z3") { 4 } else { 1 });
    for n in ["N", "Rule-hVarI", "Rule-hI", "Rule-hVarK"] {
        assert_eq!(
            summaries(&mut baseline, &program(n)),
            neutral,
            "baseline {n}"
        );
        assert_eq!(summaries(&mut mutant, &program(n)), neutral, "mutant {n}");
    }
}

/// VI-AT11 (KK-82 review R1-2): conflate's `go` variable renamed to a forged spelling
/// (`Rule-hX`, `X-b0`, `Ex-hVarI-b0`) compiles and gives the alpha-rename's leaves (`K`): the
/// compiled KORE variable is read verbatim and marked like any other rule variable.
#[test]
fn audit_vi_at11_forged_rule_variables_load_as_ordinary_names() {
    let validator = NativeValidator::bind(support::load("conflate.k"), CompileOptions::default());
    let initial = support::initial_state(
        seq(
            op("check", vec![int("A")]),
            seq(
                op("go", vec![support::var("X", "SortBox")]),
                op("done", vec![]),
            ),
        ),
        "SortProg",
    );
    let mut alpha = backend(
        &validator,
        Some(&conflate_go_renamed(&validator, "K")),
        "CONFLATE",
    );
    let neutral = summaries(&mut alpha, &initial);
    for forged in ["Rule-hX", "X-b0", "Ex-hVarI-b0"] {
        let patch = conflate_go_renamed(&validator, forged);
        let side = validator.validate(&patch).expect("forged mutant compiles");
        let kore = &side.artifacts().definition_kore;
        let spelled = kore
            .split(|c: char| !(c.is_ascii_alphanumeric() || c == '\'' || c == '-'))
            .filter(|token| {
                token.contains(forged) || token.contains(&forged.replace('-', "'Hyph'"))
            })
            .collect::<BTreeSet<_>>();
        eprintln!("AT11 {forged}: KORE spellings {spelled:?}");
        let mut forged_backend = backend(&validator, Some(&patch), "CONFLATE");
        assert_eq!(
            summaries(&mut forged_backend, &initial),
            neutral,
            "{forged}"
        );
    }
}

/// VI-06 deliverable 6: since k-rust `4d80cea6`, `symwrap.k`'s `wrap` compiles as
/// `anywhere, function, value-production` (self-reference withholds `functional`), so its runs
/// stop before a relation is asked. `symwraptotal.k` keeps the non-injective head with a
/// functional claim (`[function, total]`; compiled `anywhere, function, functional, total`
/// with the functional axiom). Over it, `wrap(s(X))` against `wrap(z)` (equal at `X = z`) and
/// `wrap(s(z))` against `wrap(z)` (equal) are never Unequal and their equation is never Unsat,
/// in both profiles with the build's solver.
#[test]
fn audit_vi_symwrap_total_head_is_never_unequal() {
    let validator =
        NativeValidator::bind(support::load("symwraptotal.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("symwraptotal compiles");
    let kore = &side.artifacts().definition_kore;
    let declaration = kore
        .lines()
        .skip_while(|line| !line.contains("symbol Lblwrap{}"))
        .take_while(|line| !line.trim_start().starts_with(']'))
        .collect::<String>();
    for attribute in [
        "anywhere{}()",
        "function{}()",
        "functional{}()",
        "total{}()",
    ] {
        assert!(
            declaration.contains(attribute),
            "{attribute}: {declaration}"
        );
    }
    assert!(!declaration.contains("constructor{}()"), "{declaration}");
    assert!(!declaration.contains("injective{}()"), "{declaration}");
    let mut backend = backend(&validator, None, "SYMWRAPTOTAL");
    let nat = |name: &str| support::var(name, "SortNat");
    let z = || op("z", vec![]);
    let s = |value: Pattern| op("s", vec![value]);
    let wrap = |value: Pattern| op("wrap", vec![value]);
    let state = support::initial_state(
        seq(
            op("write", vec![wrap(s(nat("X"))), nat("V")]),
            seq(op("load", vec![wrap(z()), nat("W")]), op("halt", vec![])),
        ),
        "SortProg",
    );
    let real = kink_pattern::PathInput {
        test_id: "t".into(),
        path_ordinal: 0,
        path_key: None,
        complete: false,
        stop: kink_pattern::PathStop::Terminal,
        execution_stop: kink_pattern::ExecutionStop::DepthLimit,
        execution_terminal: None,
        events: Vec::new(),
        path_predicate: Pattern::Top {
            sort: k_rust::kompile::initial_configuration::kore_sort("SortGeneratedTopCell"),
        },
        equivalences: Vec::new(),
        inequalities: Vec::new(),
    };
    let (answers, queries) = backend
        .with_solver(None, |definition, solver| {
            let relations = kink_native::feasibility::BackendRelations::shared(
                definition,
                solver,
                TestInitialState::of_test(&state),
            );
            let pairs = [(wrap(s(nat("X"))), wrap(z())), (wrap(s(z())), wrap(z()))];
            let answers = pairs
                .clone()
                .map(|(left, right)| relations.relate(&real, &[], &left, &right));
            let queries = pairs.map(|(left, right)| {
                relations.feasible(&real, &[kink_pattern::TermRelation { left, right }])
            });
            Ok::<_, BackendError>((answers, queries))
        })
        .expect("relations");
    assert_eq!(
        answers,
        [
            kink_pattern::RelationDecision::Indeterminate,
            kink_pattern::RelationDecision::Indeterminate,
        ],
        "never Unequal"
    );
    assert_eq!(
        queries,
        [kink_pattern::Feasibility::Unknown; 2],
        "never Unsat"
    );
}
