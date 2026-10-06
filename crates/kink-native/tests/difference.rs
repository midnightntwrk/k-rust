//! The execution-difference certificate (README section 6 of
//! `draft/tasks/execution-identity`): definition facts, generalization, the four exclusions,
//! covering and witness rules, on real runs of the campaign fixtures and on synthetic
//! sequences.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::time::Duration;

use k_rust::backend::{Backend, BackendOptions};
use k_rust::definition::AttributeKey;
use k_rust::kast::{Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kore::ast::Pattern;
use k_rust_backend::externalize::external_variable_name;
use kink_native::execution::{ExecutionAdapter, ExecutionBudget, HaltClass, SolverProfile};
use kink_native::execution_difference::{
    CertifiedSide, DefinitionFacts, DifferenceCertificate, Exclusion, NotProvedReason,
    StateSequence, StateSequences, certify_difference, definition_facts,
};
use kink_native::feasibility::{LeafFeasibility, TestInitialState};
use kink_native::{NativeValidator, ValidatedDefinition};
use kink_patch::{Baseline, Edit, InsertPosition, Patch, TermRef};

use DifferenceCertificate::{NotProved, Proved};
use Exclusion::{Clash, Disjoint, Length, Vacuous};
use NotProvedReason::{Internalization, NoWitness, NotCovering, SignatureDiffers};

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

// ------------------------------------------------------------------ fixtures and sides

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

    fn validator(self) -> NativeValidator {
        NativeValidator::bind(support::load(self.name()), CompileOptions::default())
    }
}

/// One compiled side: its event-free adapter and backend.
struct Side {
    adapter: ExecutionAdapter,
    backend: Backend,
}

impl Side {
    fn new(fixture: Fixture, side: &ValidatedDefinition) -> Self {
        Self {
            adapter: ExecutionAdapter::with_profile(PROFILE),
            backend: Backend::new(
                &side.artifacts().definition_kore,
                fixture.module(),
                BACKEND_OPTIONS,
            )
            .expect("backend"),
        }
    }

    fn baseline(fixture: Fixture, validator: &NativeValidator) -> Self {
        Self::new(
            fixture,
            &validator.compile_baseline().expect("baseline compiles"),
        )
    }

    fn mutant(fixture: Fixture, validator: &NativeValidator, patch: &Patch) -> Self {
        Self::new(
            fixture,
            &validator.validate(patch).expect("mutant compiles"),
        )
    }

    /// The baseline of `file` (module named after it) with no observed rule.
    fn unobserved(file: &str) -> Self {
        let validator = NativeValidator::bind(support::load(file), CompileOptions::default());
        let side = validator.compile_baseline().expect("baseline compiles");
        let module = file.strip_suffix(".k").expect("a .k file").to_uppercase();
        Self {
            adapter: ExecutionAdapter::with_profile(PROFILE),
            backend: Backend::new(&side.artifacts().definition_kore, &module, BACKEND_OPTIONS)
                .expect("backend"),
        }
    }

    fn facts(&mut self) -> DefinitionFacts {
        definition_facts(&mut self.backend).expect("facts")
    }

    /// The certificate sequences from one stepped run of `state`.
    fn sequences(&mut self, state: &Pattern) -> StateSequences {
        self.adapter
            .execute_steps(&mut self.backend, state, BUDGET)
            .expect("sequence run")
            .expect("step run")
            .certificate_sequences()
            .expect("certificate sequences")
    }
}

/// The certificate of `state` between two real sides.
fn certify(baseline: &mut Side, mutant: &mut Side, state: &Pattern) -> DifferenceCertificate {
    let baseline_sequences = baseline.sequences(state);
    let mutant_sequences = mutant.sequences(state);
    let (baseline_facts, mutant_facts) = (baseline.facts(), mutant.facts());
    certify_difference(
        &mut baseline.backend,
        TestInitialState::of_test(state),
        &baseline_facts,
        &mutant_facts,
        &baseline_sequences,
        &mutant_sequences,
    )
}

fn proved(witness_side: CertifiedSide, exclusions: &[Exclusion]) -> DifferenceCertificate {
    Proved {
        witness_side,
        witness_leaf: 0,
        exclusions: exclusions.to_vec(),
    }
}

// ------------------------------------------------------------------ mutants

fn term_at(baseline: &Baseline, label: &str, path: &[u32]) -> (TermRef, Term) {
    let at = TermRef::new(support::rule(baseline, label), path);
    let term = baseline.term(&at).expect("term").clone();
    (at, term)
}

fn replace(at: TermRef, expected: Term, replacement: Term) -> Edit {
    Edit::ReplaceTerm {
        at,
        expected,
        replacement,
    }
}

/// S1 (`release-after-write`) and K (`release-after-access`): `P` becomes `seq(free(A), P)`
/// on the right-hand side of the listed symmem rules (copied from tests/validator.rs).
fn release(baseline: &Baseline, labels: &[&str]) -> Patch {
    Patch::new(
        labels
            .iter()
            .map(|label| {
                let (_, address) = term_at(baseline, label, &[0, 0, 0, 0]);
                let (at, continuation) = term_at(baseline, label, &[0, 1]);
                replace(
                    at,
                    continuation.clone(),
                    Term::apply(
                        "seq",
                        vec![Term::apply("free", vec![address]), continuation],
                    ),
                )
            })
            .collect(),
    )
    .expect("patch")
}

/// G (`inverted-load-sign`): guardedmem's `load` and `loadFault` exchange their `requires`
/// (copied from tests/validator.rs).
fn inverted_load_sign(baseline: &Baseline) -> Patch {
    let (load_at, load) = term_at(baseline, "GUARDEDMEM.load", &[1]);
    let (fault_at, fault) = term_at(baseline, "GUARDEDMEM.loadFault", &[1]);
    Patch::new(vec![
        replace(load_at, load.clone(), fault.clone()),
        replace(fault_at, fault, load),
    ])
    .expect("patch")
}

fn int_token(value: i64) -> Term {
    Term::Token {
        token: value.to_string(),
        sort: Sort::new("Int"),
    }
}

/// An insertable copy of the rule `label`: no label, identity or source-position attributes
/// (as in crates/kink-campaign/tests/coupled.rs).
fn unlabelled_copy(baseline: &Baseline, label: &str) -> k_rust::definition::Sentence {
    let mut copy = baseline
        .sentence(&support::rule(baseline, label))
        .expect("rule")
        .clone();
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
        copy.attributes_mut().remove(key.as_str());
    }
    copy
}

/// AS5 (guard split, as in coupled.rs `audit_ks_as5_guard_split_*`): `GUARDEDMEM.write`'s
/// guard narrowed to `A >Int 0`, and an unobserved copy with `A ==Int 0` inserted after it.
fn guard_split(baseline: &Baseline) -> Patch {
    let write = support::rule(baseline, "GUARDEDMEM.write");
    let (_, a) = term_at(baseline, "GUARDEDMEM.write", &[0, 0, 0, 0, 0]);
    let mut zero = unlabelled_copy(baseline, "GUARDEDMEM.write");
    if let k_rust::definition::Sentence::Rule { requires, .. } = &mut zero {
        *requires = Term::apply("_==Int_", vec![a.clone(), int_token(0)]);
    }
    let (guard_at, guard) = term_at(baseline, "GUARDEDMEM.write", &[1]);
    Patch::new(vec![
        replace(
            guard_at,
            guard,
            Term::apply("_>Int_", vec![a, int_token(0)]),
        ),
        Edit::InsertSentence {
            position: InsertPosition::After(write),
            ordinal: 0,
            sentence: zero,
        },
    ])
    .expect("patch")
}

// ------------------------------------------------------------------ programs

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
fn halt() -> Pattern {
    app("Lblhalt", vec![])
}
fn seq(operation: Pattern, rest: Pattern) -> Pattern {
    app("Lblseq", vec![operation, rest])
}
fn state(program: Pattern) -> Pattern {
    support::initial_state(program, "SortProg")
}

/// `write(addr(wa), wv); load(addr(la), lv); halt` (coupled.rs `state`).
fn memory(wa: Pattern, wv: Pattern, la: Pattern, lv: Pattern) -> Pattern {
    state(seq(write(addr(wa), wv), seq(load(addr(la), lv), halt())))
}

/// ground-zero (coupled.rs `int_program(0, 5, int(0), 7)`).
fn ground_zero() -> Pattern {
    memory(
        support::int(0),
        support::int(5),
        support::int(0),
        support::int(7),
    )
}

/// ground-shared (coupled.rs `tests()`).
fn ground_shared() -> Pattern {
    memory(z(), s(z()), z(), s(z()))
}

/// sym-shared (coupled.rs `tests()`; symbolic.rs p1).
fn sym_shared() -> Pattern {
    memory(nat("X"), nat("V"), nat("X"), nat("W"))
}

/// ground-guarded (coupled.rs `Guarded::new`).
fn ground_guarded() -> Pattern {
    memory(support::int(1), integer("V"), support::int(1), integer("W"))
}

/// sym-guarded (coupled.rs `Guarded::new`; symbolic.rs g1).
fn sym_guarded() -> Pattern {
    memory(integer("X"), integer("V"), integer("Y"), integer("W"))
}

// ------------------------------------------------------------------ synthetic sequences

fn leaf(halt: HaltClass, states: &[Pattern]) -> StateSequence {
    StateSequence {
        halt,
        states: states.to_vec(),
        feasibility: LeafFeasibility::Syntactic,
    }
}

fn leaves(leaves: Vec<StateSequence>) -> StateSequences {
    StateSequences { leaves }
}

/// The states of a symmem program of `count` writes to `addr(z)`, one per position: the
/// state after `i` rewrites is `states[i]`.
fn chain(count: usize) -> Vec<Pattern> {
    (0..=count)
        .map(|done| (done..count).fold(halt(), |rest, _| seq(write(addr(z()), z()), rest)))
        .map(state)
        .collect()
}

/// A synthetic certificate over one backend's definition, whose facts both sides share.
fn synthetic(
    backend: &mut Backend,
    initial: &Pattern,
    baseline: &StateSequences,
    mutant: &StateSequences,
) -> DifferenceCertificate {
    let facts = definition_facts(backend).expect("facts");
    certify_difference(
        backend,
        TestInitialState::of_test(initial),
        &facts,
        &facts,
        baseline,
        mutant,
    )
}

fn symmem_backend() -> Backend {
    let side = Fixture::Sym
        .validator()
        .compile_baseline()
        .expect("baseline compiles");
    Backend::new(&side.artifacts().definition_kore, "SYMMEM", BACKEND_OPTIONS).expect("backend")
}

fn guardedmem_backend() -> Backend {
    let side = Fixture::Guard
        .validator()
        .compile_baseline()
        .expect("baseline compiles");
    Backend::new(
        &side.artifacts().definition_kore,
        "GUARDEDMEM",
        BACKEND_OPTIONS,
    )
    .expect("backend")
}

// ------------------------------------------------------------------ rows on real runs

/// d1: AS5 on ground-zero. The unobserved `A ==Int 0` copy handles the state `write` handled;
/// both runs pass through the same states to the same leaf, so no witness exists, in both
/// profiles.
#[test]
fn guard_split_has_no_witness() {
    let fixture = Fixture::Guard;
    let validator = fixture.validator();
    let mut baseline = Side::baseline(fixture, &validator);
    let mut mutant = Side::mutant(fixture, &validator, &guard_split(validator.baseline()));
    assert_eq!(
        certify(&mut baseline, &mut mutant, &ground_zero()),
        NotProved(NoWitness),
        "d1 ground-zero"
    );
}

/// d2: S1 (`release` of `SYMMEM.write`) takes one more rewrite before the Stuck `halt`: 3
/// against 2 positions, on ground-shared and on sym-shared, in both profiles.
#[test]
fn release_is_proved_by_length() {
    let fixture = Fixture::Sym;
    let validator = fixture.validator();
    let mut baseline = Side::baseline(fixture, &validator);
    let mut mutant = Side::mutant(
        fixture,
        &validator,
        &release(validator.baseline(), &["SYMMEM.write"]),
    );
    for (id, program) in [
        ("ground-shared", ground_shared()),
        ("sym-shared", sym_shared()),
    ] {
        assert_eq!(
            certify(&mut baseline, &mut mutant, &program),
            proved(CertifiedSide::Mutant, &[Length]),
            "d2 {id}"
        );
    }
}

/// d3 and d4: G (inverted load sign). On ground-guarded the mutant faults where the baseline
/// halts, after as many rewrites: `fault` against `halt` clashes in the last state (predicted
/// by the README; the campaign certifies this test through the state slot). On sym-guarded
/// with Z3, the mutant's first leaf is excluded from the baseline's three leaves by
/// `Disjoint`, `Clash` and `Length`; without Z3 both sides are one Indeterminate leaf at the
/// initial state, and nothing separates them.
#[test]
fn inverted_load_sign_is_proved_by_clash_and_by_disjoint_paths() {
    let fixture = Fixture::Guard;
    let validator = fixture.validator();
    let mut baseline = Side::baseline(fixture, &validator);
    let mut mutant = Side::mutant(
        fixture,
        &validator,
        &inverted_load_sign(validator.baseline()),
    );
    assert_eq!(
        certify(&mut baseline, &mut mutant, &ground_guarded()),
        proved(CertifiedSide::Mutant, &[Clash]),
        "d3 ground-guarded"
    );
    let expected = if cfg!(feature = "z3") {
        proved(CertifiedSide::Mutant, &[Disjoint, Clash, Length])
    } else {
        NotProved(NoWitness)
    };
    assert_eq!(
        certify(&mut baseline, &mut mutant, &sym_guarded()),
        expected,
        "d4 sym-guarded"
    );
}

/// d11: the signature projection of symmem equals that of its S1 mutant; symmem's and
/// guardedmem's differ, and the certificate refuses to compare them.
#[test]
fn signature_projections_compare_constructor_and_sort_structure() {
    let validator = Fixture::Sym.validator();
    let mut symmem = Side::baseline(Fixture::Sym, &validator);
    let mut released = Side::mutant(
        Fixture::Sym,
        &validator,
        &release(validator.baseline(), &["SYMMEM.write"]),
    );
    let mut guarded = guardedmem_backend();
    let symmem_facts = symmem.facts();
    assert_eq!(symmem_facts, released.facts(), "d11 symmem and S1");
    let guarded_facts = definition_facts(&mut guarded).expect("facts");
    assert_ne!(
        symmem_facts.signature, guarded_facts.signature,
        "d11 guardedmem"
    );
    let sequences = leaves(vec![leaf(HaltClass::Stuck, &chain(1))]);
    let other = leaves(vec![leaf(HaltClass::Stuck, &chain(2))]);
    assert_eq!(
        certify_difference(
            &mut symmem.backend,
            TestInitialState::of_test(&chain(2)[0]),
            &symmem_facts,
            &guarded_facts,
            &sequences,
            &other,
        ),
        NotProved(SignatureDiffers),
        "d11 a Length difference is not compared across signatures"
    );
}

// ------------------------------------------------------------------ synthetic rows

/// d5: a Stuck and a Trivial leaf at the same state have the same length (positions, never a
/// depth), so neither excludes the other.
#[test]
fn stuck_and_trivial_at_one_state_are_not_separated() {
    let mut backend = symmem_backend();
    let states = chain(2);
    let stuck = leaves(vec![leaf(HaltClass::Stuck, &states)]);
    let trivial = leaves(vec![leaf(HaltClass::Trivial, &states)]);
    for (baseline, mutant) in [(&stuck, &trivial), (&trivial, &stuck)] {
        assert_eq!(
            synthetic(&mut backend, &states[0], baseline, mutant),
            NotProved(NoWitness),
            "d5"
        );
    }
}

/// d6: a DepthBound leaf is a prefix. Against a longer Stuck path with the same prefix it is
/// excluded by nothing; a DepthBound witness longer than a Stuck path is excluded by
/// `Length`.
#[test]
fn depth_bound_prefixes_are_excluded_only_when_the_terminal_is_shorter() {
    let mut backend = symmem_backend();
    let three = chain(3);
    let bounded_2 = leaves(vec![leaf(HaltClass::DepthBound, &three[..3])]);
    let stuck_3 = leaves(vec![leaf(HaltClass::Stuck, &three)]);
    for (baseline, mutant) in [(&bounded_2, &stuck_3), (&stuck_3, &bounded_2)] {
        assert_eq!(
            synthetic(&mut backend, &three[0], baseline, mutant),
            NotProved(NoWitness),
            "d6 DepthBound 2 against Stuck 3"
        );
    }
    let states = chain(4);
    let initial = &states[0];
    let stuck_2 = leaves(vec![leaf(HaltClass::Stuck, &states[..3])]);
    let bounded_4 = leaves(vec![leaf(HaltClass::DepthBound, &states)]);
    assert_eq!(
        synthetic(&mut backend, initial, &stuck_2, &bounded_4),
        proved(CertifiedSide::Mutant, &[Length]),
        "d6 DepthBound 4 against Stuck 2"
    );
    assert_eq!(
        synthetic(&mut backend, initial, &bounded_4, &stuck_2),
        proved(CertifiedSide::Mutant, &[Length]),
        "d6 reversed sides: the shorter Stuck witness is tried first"
    );
}

/// d7: a BreadthBound leaf loses its side's coverage. With one on each side neither
/// direction is attempted; with one on one side only, the other direction is attempted and
/// finds no witness among equal sequences.
#[test]
fn breadth_bounds_lose_coverage() {
    let mut backend = symmem_backend();
    let states = chain(2);
    let both = leaves(vec![
        leaf(HaltClass::Stuck, &states),
        leaf(HaltClass::BreadthBound, &states[..2]),
    ]);
    assert_eq!(
        synthetic(&mut backend, &states[0], &both, &both),
        NotProved(NotCovering),
        "d7 both sides"
    );
    let stuck = leaves(vec![leaf(HaltClass::Stuck, &states)]);
    let bounded = leaves(vec![leaf(HaltClass::BreadthBound, &states)]);
    for (baseline, mutant) in [(&stuck, &bounded), (&bounded, &stuck)] {
        assert_eq!(
            synthetic(&mut backend, &states[0], baseline, mutant),
            NotProved(NoWitness),
            "d7 one side"
        );
    }
}

/// d8: distinct `Int` values at one position clash; a difference only inside a function
/// application is a wildcard on each side and proves nothing.
#[test]
fn values_clash_and_function_residues_do_not() {
    let mut backend = guardedmem_backend();
    let plus = backend
        .with_solver(None, |definition, _| {
            Ok::<_, k_rust::backend::BackendError>(
                definition
                    .symbols()
                    .values()
                    .find(|symbol| symbol.attributes.hook.as_deref() == Some("INT.add"))
                    .expect("+Int")
                    .name
                    .to_string(),
            )
        })
        .expect("definition");
    let int = support::int;
    let written = |value: Pattern| state(seq(write(addr(int(1)), value), halt()));
    let initial = state(seq(
        load(addr(int(1)), int(7)),
        seq(write(addr(int(1)), int(5)), halt()),
    ));
    let path = |last: Pattern| leaves(vec![leaf(HaltClass::Stuck, &[initial.clone(), last])]);
    assert_eq!(
        synthetic(
            &mut backend,
            &initial,
            &path(written(int(5))),
            &path(written(int(6))),
        ),
        proved(CertifiedSide::Mutant, &[Clash]),
        "d8 distinct Int values"
    );
    let sum = |right: i64| app(&plus, vec![int(1), int(right)]);
    assert_eq!(
        synthetic(
            &mut backend,
            &initial,
            &path(written(sum(1))),
            &path(written(sum(2))),
        ),
        NotProved(NoWitness),
        "d8 function residues"
    );
}

/// d9 and d10: a stable variable denotes one value along the path. `addr(X)` against
/// `addr(1)` is no clash; `X` against `1` at one position and against `2` at the next is,
/// because `X` is one of the test's initial variables, whatever its spelling. Before variable
/// identity the names that a backend mint could also print as (`ExVarX0`, `X0`, `RuleX`, `EqX`,
/// `X'Bang'apart1`) and every name under an existential rule were not stable, and the
/// difference was not proved. d10: a variable that is not initial, named alike at two
/// positions, is renamed in each position's own scope, so it links nothing across positions.
#[test]
fn stable_variables_carry_differences_across_positions() {
    let mut backend = guardedmem_backend();
    let int = support::int;
    let loaded = |address: Pattern| state(seq(load(addr(address), int(7)), halt()));
    for name in ["X", "ExVarX0", "X0", "RuleX", "EqX", "X'Bang'apart1"] {
        let x = || integer(name);
        let initial = state(seq(
            load(addr(x()), int(7)),
            seq(load(addr(x()), int(7)), halt()),
        ));
        let path = |states: Vec<Pattern>| leaves(vec![leaf(HaltClass::Stuck, &states)]);
        let symbolic = path(vec![initial.clone(), loaded(x()), loaded(x())]);
        let one = path(vec![initial.clone(), loaded(int(1)), loaded(int(1))]);
        let one_two = path(vec![initial.clone(), loaded(int(1)), loaded(int(2))]);
        assert_eq!(
            synthetic(&mut backend, &initial, &symbolic, &one),
            NotProved(NoWitness),
            "d9 {name}: addr(X) against addr(1)"
        );
        assert_eq!(
            synthetic(&mut backend, &initial, &symbolic, &one_two),
            proved(CertifiedSide::Mutant, &[Clash]),
            "d9 {name}: X against 1, then 2"
        );
    }
    let x = || integer("X");
    let initial = state(seq(
        load(addr(x()), int(7)),
        seq(load(addr(x()), int(7)), halt()),
    ));
    let path = |states: Vec<Pattern>| leaves(vec![leaf(HaltClass::Stuck, &states)]);
    // A narrowing mint of the rule variable `N`, as k-rust prints it.
    let minted = || integer(&external_variable_name("Ex#N!0"));
    let symbolic = path(vec![initial.clone(), loaded(minted()), loaded(minted())]);
    let one_two = path(vec![initial.clone(), loaded(int(1)), loaded(int(2))]);
    assert_eq!(
        synthetic(&mut backend, &initial, &symbolic, &one_two),
        NotProved(NoWitness),
        "d10 a minted N against 1, then 2"
    );
}

/// d12: a Vacuous leaf and an Unsat leaf of the covering side have no instance and are
/// excluded by `Vacuous`; neither is ever a witness.
#[test]
fn vacuous_and_unsat_leaves_are_excluded() {
    let mut backend = symmem_backend();
    let states = chain(2);
    let unsat = StateSequence {
        feasibility: LeafFeasibility::Unsat,
        ..leaf(HaltClass::Stuck, &states)
    };
    let covering = leaves(vec![leaf(HaltClass::Vacuous, &states), unsat.clone()]);
    let witness = leaves(vec![leaf(HaltClass::Stuck, &states)]);
    assert_eq!(
        synthetic(&mut backend, &states[0], &covering, &witness),
        proved(CertifiedSide::Mutant, &[Vacuous, Vacuous]),
        "d12 mutant witness"
    );
    assert_eq!(
        synthetic(&mut backend, &states[0], &witness, &covering),
        proved(CertifiedSide::Baseline, &[Vacuous, Vacuous]),
        "d12 baseline witness"
    );
    let unwitnessed = leaves(vec![leaf(HaltClass::Vacuous, &states), unsat]);
    assert_eq!(
        synthetic(&mut backend, &states[0], &unwitnessed, &unwitnessed),
        NotProved(NoWitness),
        "d12 no side has a witness"
    );
}

/// A state that does not internalize in the baseline definition leaves its leaf to
/// `Vacuous` and `Length` only; with no such exclusion the result is `Internalization`.
#[test]
fn uninternalizable_states_fail_closed() {
    let mut backend = symmem_backend();
    let states = chain(2);
    let foreign = state(app("LblnoSuchSymbol", vec![]));
    let broken = leaves(vec![leaf(
        HaltClass::Stuck,
        &[states[0].clone(), states[1].clone(), foreign],
    )]);
    let good = leaves(vec![leaf(HaltClass::Stuck, &states)]);
    assert_eq!(
        synthetic(&mut backend, &states[0], &good, &broken),
        NotProved(Internalization),
        "equal lengths, one state foreign"
    );
    let longer = leaves(vec![leaf(HaltClass::Stuck, &chain(3))]);
    assert_eq!(
        synthetic(&mut backend, &states[0], &broken, &longer),
        proved(CertifiedSide::Mutant, &[Length]),
        "Length needs no internalization"
    );
}

// ------------------------------------------------------------------ read names (variable identity)

/// `check(a); check2(b); go(X); done` over conflate.k: `check` continues when `a <=Int 0`,
/// `check2` when `b >Int 0`, and the baseline's `go` narrows `X:Box` to `c(I)` with a fresh
/// `I`, split on its sign.
fn conflate_program(a: &str, b: &str) -> Pattern {
    let op = |name: &str, argument: Pattern| app(name, vec![argument]);
    state(seq(
        op("Lblcheck", integer(a)),
        seq(
            op("Lblcheck2", integer(b)),
            seq(
                op("Lblgo", support::var("X", "SortBox")),
                app("Lbldone", vec![]),
            ),
        ),
    ))
}

/// EI-02b review regression. conflatem.k merges the baseline's guard-split `go` rules into
/// one unguarded rule, so the two definitions execute identically on every ground instance.
/// Before VI, the printer merged a fresh narrowing variable with initial variables named
/// `ExVarI0` and `ExVarI1`, making two feasible leaves Unsat under Z3.
/// The injective printer preserves their identities, so neither naming has an Unsat leaf.
/// The certificate remains NotProved(NoWitness) in both profiles.
#[test]
fn initial_names_are_distinct_from_minted_names() {
    let mut baseline = Side::unobserved("conflate.k");
    let mut mutant = Side::unobserved("conflatem.k");
    let (baseline_facts, mutant_facts) = (baseline.facts(), mutant.facts());
    assert_eq!(
        baseline_facts, mutant_facts,
        "the merge changes no signature"
    );
    for (a, b) in [("A", "B"), ("ExVarI0", "ExVarI1")] {
        let program = conflate_program(a, b);
        let baseline_sequences = baseline.sequences(&program);
        let mutant_sequences = mutant.sequences(&program);
        let unsat = baseline_sequences
            .leaves
            .iter()
            .map(|leaf| leaf.feasibility == LeafFeasibility::Unsat)
            .collect::<Vec<_>>();
        // Z3: the baseline narrows into five leaves and the mutant has three; the renamed
        // program's two `go` leaves are no longer conflated. No-Z3: one Indeterminate
        // leaf per side.
        let expected_unsat = match (cfg!(feature = "z3"), a) {
            (true, "A") => vec![false; 5],
            (true, _) => vec![false; 5],
            (false, _) => vec![false],
        };
        assert_eq!(
            unsat, expected_unsat,
            "baseline Unsat leaves, names {a}, {b}"
        );
        assert_eq!(
            mutant_sequences.leaves.len(),
            if cfg!(feature = "z3") { 3 } else { 1 },
            "mutant leaves, names {a}, {b}"
        );
        assert_eq!(
            certify_difference(
                &mut baseline.backend,
                TestInitialState::of_test(&program),
                &baseline_facts,
                &mutant_facts,
                &baseline_sequences,
                &mutant_sequences,
            ),
            NotProved(NoWitness),
            "initial names {a}, {b}"
        );
    }
}

/// Within one read state a name is one variable, whatever its spelling (names are read
/// verbatim and printed injectively), so it is renamed
/// consistently in its scope: `write(addr(N), N)` against `write(addr(z), s(z))` clashes for
/// every name. Before variable identity the names a mint could print as (`ExVarI10`, `N10`)
/// were renamed per occurrence, and the difference was not proved.
#[test]
fn every_name_is_renamed_consistently() {
    let mut backend = symmem_backend();
    let initial = state(seq(write(addr(z()), z()), halt()));
    let witness = leaves(vec![leaf(
        HaltClass::Stuck,
        &[
            initial.clone(),
            state(seq(write(addr(z()), s(z())), halt())),
        ],
    )]);
    for (name, expected) in [
        ("N", proved(CertifiedSide::Mutant, &[Clash])),
        ("ExVarI10", proved(CertifiedSide::Mutant, &[Clash])),
        ("N10", proved(CertifiedSide::Mutant, &[Clash])),
    ] {
        let covering = leaves(vec![leaf(
            HaltClass::Stuck,
            &[
                initial.clone(),
                state(seq(write(addr(nat(name)), nat(name)), halt())),
            ],
        )]);
        assert_eq!(
            synthetic(&mut backend, &initial, &covering, &witness),
            expected,
            "{name}"
        );
    }
}

/// A leaf's feasibility is decided on its read state, which under variable identity is the
/// real state up to a renaming that fixes the request's names, so an Unsat covering leaf has no instance and is `Vacuous` whatever its names.
/// Before variable identity only names that no mint could print as (`N`, not `ExVarI10` or
/// `N10`) made an Unsat leaf Vacuous.
#[test]
fn unsat_leaves_are_vacuous() {
    let mut backend = symmem_backend();
    let initial = state(seq(write(addr(z()), z()), halt()));
    let witness = leaves(vec![leaf(
        HaltClass::Stuck,
        &[initial.clone(), state(seq(write(addr(z()), z()), halt()))],
    )]);
    for (name, expected) in [
        ("N", proved(CertifiedSide::Mutant, &[Vacuous])),
        ("ExVarI10", proved(CertifiedSide::Mutant, &[Vacuous])),
        ("N10", proved(CertifiedSide::Mutant, &[Vacuous])),
    ] {
        let covering = leaves(vec![StateSequence {
            feasibility: LeafFeasibility::Unsat,
            ..leaf(
                HaltClass::Stuck,
                &[
                    initial.clone(),
                    state(seq(write(addr(nat(name)), z()), halt())),
                ],
            )
        }]);
        assert_eq!(
            synthetic(&mut backend, &initial, &covering, &witness),
            expected,
            "{name}"
        );
    }
}
