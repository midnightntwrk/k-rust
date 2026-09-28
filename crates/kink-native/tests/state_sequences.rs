//! State-sequence runs preserve the primary observed run's leaves and rewrite positions.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::time::Duration;

use k_rust::backend::{Backend, BackendOptions};
use k_rust::kompile::CompileOptions;
use k_rust::kore::ast::Pattern;
use kink_native::execution::{ExecutionAdapter, ExecutionBudget, SolverProfile};
use kink_native::execution_difference::NotProvedReason;
use kink_native::observation::{DomainEventSpec, PayloadSource};
use kink_native::{NativeValidator, ObservedRule};

const PROFILE: SolverProfile = SolverProfile::BUILD;

const BACKEND_OPTIONS: BackendOptions = BackendOptions {
    smt_timeout_ms: 4000,
    smt_retry_limit: 2,
};
const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(30),
    max_simplification_iterations: 1000,
    max_depth: None,
    max_breadth: None,
};

fn backend(kore: &str, module: &str) -> Backend {
    Backend::new(kore, module, BACKEND_OPTIONS).expect("backend")
}

fn adapter(manifest: kink_native::observation::InstalledObservationManifest) -> ExecutionAdapter {
    ExecutionAdapter::with_profile(manifest, PROFILE)
}

// These are the named binding positions used by symbolic.rs for these two fixtures.
const SYM_WRITE_A: usize = 0;
const SYM_WRITE_V: usize = 3;
const SYM_LOAD_A: usize = 0;
const SYM_LOAD_V: usize = 3;
const SYM_FREE_A: usize = 0;
const GUARD_WRITE_A: usize = 1;
const GUARD_WRITE_V: usize = 2;
const GUARD_LOAD_A: usize = 1;
const GUARD_LOAD_V: usize = 2;
const GUARD_LOAD_NEG_A: usize = 1;
const GUARD_LOAD_NEG_V: usize = 2;

#[derive(Clone, Copy)]
enum Fixture {
    Sym,
    Guard,
}

impl Fixture {
    fn name(self) -> &'static str {
        match self {
            Self::Sym => "symmem.k",
            Self::Guard => "guardedmem.k",
        }
    }

    fn module(self) -> &'static str {
        match self {
            Self::Sym => "SYMMEM",
            Self::Guard => "GUARDEDMEM",
        }
    }
}

fn observed(
    validator: &NativeValidator,
    label: &str,
    constructor: &str,
    indices: &[usize],
) -> ObservedRule {
    ObservedRule {
        rule: support::rule(validator.baseline(), label),
        emit_rule_applied: false,
        domain_events: vec![DomainEventSpec {
            constructor: constructor.into(),
            payload: indices
                .iter()
                .copied()
                .map(PayloadSource::BindingValue)
                .collect(),
        }],
    }
}

fn observations(fixture: Fixture, validator: &NativeValidator) -> Vec<ObservedRule> {
    match fixture {
        Fixture::Sym => vec![
            observed(
                validator,
                "SYMMEM.write",
                "memoryWrite",
                &[SYM_WRITE_A, SYM_WRITE_V],
            ),
            observed(
                validator,
                "SYMMEM.load",
                "memoryLoad",
                &[SYM_LOAD_A, SYM_LOAD_V],
            ),
            observed(validator, "SYMMEM.free", "memoryFree", &[SYM_FREE_A]),
        ],
        Fixture::Guard => vec![
            observed(
                validator,
                "GUARDEDMEM.write",
                "memoryWrite",
                &[GUARD_WRITE_A, GUARD_WRITE_V],
            ),
            observed(
                validator,
                "GUARDEDMEM.load",
                "memoryLoad",
                &[GUARD_LOAD_A, GUARD_LOAD_V],
            ),
            observed(
                validator,
                "GUARDEDMEM.loadNeg",
                "memoryLoad",
                &[GUARD_LOAD_NEG_A, GUARD_LOAD_NEG_V],
            ),
        ],
    }
}

fn app(name: &str, args: Vec<Pattern>) -> Pattern {
    support::app(name, args)
}
fn nat(name: &str) -> Pattern {
    support::var(name, "SortNat")
}
fn integer(name: &str) -> Pattern {
    support::var(name, "SortInt")
}
fn z() -> Pattern {
    app("Lblz", vec![])
}
fn s(value: Pattern) -> Pattern {
    app("Lbls", vec![value])
}
fn addr(value: Pattern) -> Pattern {
    app("Lbladdr", vec![value])
}
fn write(address: Pattern, value: Pattern) -> Pattern {
    app("Lblwrite", vec![address, value])
}
fn load(address: Pattern, value: Pattern) -> Pattern {
    app("Lblload", vec![address, value])
}
fn load_neg(address: Pattern, value: Pattern) -> Pattern {
    app("LblloadNeg", vec![address, value])
}
fn free(address: Pattern) -> Pattern {
    app("Lblfree", vec![address])
}
fn halt() -> Pattern {
    app("Lblhalt", vec![])
}
fn seq(operation: Pattern, rest: Pattern) -> Pattern {
    app("Lblseq", vec![operation, rest])
}
fn fork(left: Pattern, right: Pattern) -> Pattern {
    app("Lblfork", vec![left, right])
}

fn p1() -> Pattern {
    seq(
        write(addr(nat("X")), nat("V")),
        seq(load(addr(nat("X")), nat("W")), halt()),
    )
}
fn p2() -> Pattern {
    seq(
        write(addr(nat("X")), nat("V")),
        seq(free(addr(z())), seq(load(addr(nat("X")), nat("W")), halt())),
    )
}
fn p3() -> Pattern {
    seq(
        load(addr(nat("X")), nat("W")),
        seq(write(addr(nat("X")), nat("V")), halt()),
    )
}
fn p4() -> Pattern {
    fork(
        seq(write(addr(nat("X")), nat("V")), halt()),
        seq(load(addr(nat("X")), nat("W")), halt()),
    )
}
fn p5() -> Pattern {
    fork(p1(), seq(load(addr(nat("X")), nat("W")), halt()))
}
fn p6() -> Pattern {
    seq(
        write(addr(nat("X")), nat("V")),
        seq(load(addr(nat("Y")), nat("W")), halt()),
    )
}
fn p7() -> Pattern {
    seq(
        write(addr(z()), nat("V")),
        seq(load(addr(s(nat("Y"))), nat("W")), halt()),
    )
}
fn p8() -> Pattern {
    p1()
}
fn p9() -> Pattern {
    fork(
        p1(),
        seq(
            write(addr(nat("Y")), nat("V")),
            seq(load(addr(nat("Y")), nat("W")), halt()),
        ),
    )
}
fn g1() -> Pattern {
    seq(
        write(addr(integer("X")), integer("V")),
        seq(load(addr(integer("Y")), integer("W")), halt()),
    )
}
fn g2() -> Pattern {
    seq(
        write(addr(integer("X")), integer("V")),
        seq(load_neg(addr(integer("Y")), integer("W")), halt()),
    )
}
fn g3() -> Pattern {
    seq(
        write(addr(support::int(1)), integer("V")),
        seq(load(addr(support::int(1)), integer("W")), halt()),
    )
}

type ProgramRow = (&'static str, Pattern);
type FixtureRow = (Fixture, Vec<ProgramRow>);

fn fixture_rows() -> Vec<FixtureRow> {
    vec![
        (
            Fixture::Sym,
            vec![
                ("p1", p1()),
                ("p2", p2()),
                ("p3", p3()),
                ("p4", p4()),
                ("p5", p5()),
                ("p6", p6()),
                ("p7", p7()),
                ("p8", p8()),
                ("p9", p9()),
            ],
        ),
        (
            Fixture::Guard,
            vec![("g1", g1()), ("g2", g2()), ("g3", g3())],
        ),
    ]
}

fn setup(fixture: Fixture) -> (ExecutionAdapter, Backend) {
    let validator = NativeValidator::bind(support::load(fixture.name()), CompileOptions::default());
    let side = validator.compile_baseline().expect("fixture compiles");
    let rules = observations(fixture, &validator);
    let manifest = validator
        .observation_manifest(&side, &rules)
        .expect("manifest");
    (
        adapter(manifest),
        backend(&side.artifacts().definition_kore, fixture.module()),
    )
}

#[test]
fn state_sequences_follow_the_observed_leaves() {
    let mut reached_three = false;
    for (fixture, programs) in fixture_rows() {
        let (adapter, mut backend) = setup(fixture);
        let fixture = fixture.name();
        for (row, program) in programs {
            let state = support::initial_state(program, "SortProg");
            let execution = adapter
                .execute(&mut backend, &state, BUDGET)
                .expect("primary run");
            let expected = execution
                .leaves()
                .iter()
                .map(|leaf| leaf.branch.identity.clone())
                .collect::<Vec<_>>();
            let sequences = adapter
                .state_sequences(&mut backend, &state, BUDGET, &expected)
                .unwrap_or_else(|reason| panic!("{fixture} {row}: {reason:?}"));
            assert_eq!(
                sequences.leaves.len(),
                execution.leaves().len(),
                "{fixture} {row}: leaves"
            );
            for (index, (sequence, leaf)) in
                sequences.leaves.iter().zip(execution.leaves()).enumerate()
            {
                assert_eq!(
                    sequence.halt, leaf.halt,
                    "{fixture} {row} leaf {index}: halt"
                );
                assert_eq!(
                    sequence.feasibility, leaf.feasibility,
                    "{fixture} {row} leaf {index}: feasibility"
                );
                // Without Z3, g1 and g2 are single Indeterminate leaves with empty branches;
                // the same position-count formula covers them.
                assert_eq!(
                    sequence.states.len(),
                    expected[index]
                        .iter()
                        .filter(|id| !id.rule.starts_with("remainder:"))
                        .count()
                        + 1,
                    "{fixture} {row} leaf {index}: positions"
                );
                reached_three |= sequence.states.len() >= 3;
            }
        }
    }
    assert!(reached_three, "no program reached three states");
}

#[test]
fn mismatched_branches_are_refused() {
    let (adapter, mut backend) = setup(Fixture::Sym);
    let programs = [p1(), p2(), p3(), p4(), p5(), p6(), p7(), p8(), p9()];
    let (state, expected) = programs
        .into_iter()
        .find_map(|program| {
            let state = support::initial_state(program, "SortProg");
            let execution = adapter
                .execute(&mut backend, &state, BUDGET)
                .expect("primary run");
            let expected = execution
                .leaves()
                .iter()
                .map(|leaf| leaf.branch.identity.clone())
                .collect::<Vec<_>>();
            if expected.first().is_some_and(|branch| !branch.is_empty()) {
                Some((state, expected))
            } else {
                None
            }
        })
        .expect("a program with a transition");
    let mut shortened = expected.clone();
    shortened[0].pop();
    assert_eq!(
        adapter.state_sequences(&mut backend, &state, BUDGET, &shortened),
        Err(NotProvedReason::BranchMismatch)
    );
    let mut extended = expected;
    extended.push(Vec::new());
    assert_eq!(
        adapter.state_sequences(&mut backend, &state, BUDGET, &extended),
        Err(NotProvedReason::BranchMismatch)
    );
}
