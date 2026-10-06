//! Trust-base premises that the k-rust 927b9ce6 pin changed (variable-identity TB-01).
//!
//! AT12 (README 16.3 item 13): a function call that k-rust keeps in a ground state, because no
//! equation instance is used for it, is a value only k-rust's equations could fix; kink must
//! never compare it syntactically against a mutant that evaluates it.
//!
//! T-UNSAT (README 16.4, decision D-B): a solver `Unsat` on a leaf's constraints, or on a
//! relation query over them, refutes the leaf only if every partial term of the predicate has
//! its definedness explicit in it. The rows below take every leaf of rules whose `requires` is
//! over the partial `/Int`, including the remainder k-rust builds, and check that no leaf with
//! a K instance is refuted.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::time::Duration;

use k_rust::backend::{Backend, BackendError, BackendOptions};
use k_rust::definition::{AttributeKey, Sentence};
use k_rust::kast::{Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::kore_sort;
use k_rust::kore::{ast::Pattern, codec};
use kink_native::bridge::{self, DiscardReason};
use kink_native::execution::{
    AdaptedLeaf, ExecutionAdapter, ExecutionBudget, HaltClass, SolverProfile,
};
use kink_native::feasibility::{BackendRelations, LeafFeasibility, TestInitialState};
use kink_native::{NativeValidator, ValidatedDefinition};
use kink_patch::{Edit, InsertPosition, Patch, TermRef};
use kink_pattern::{
    ExecutionStop, Feasibility, PathInput, PathStop, RelationDecider, TermRelation,
};

const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(30),
    max_simplification_iterations: 1000,
    max_depth: None,
    max_breadth: None,
};

fn int(name: &str) -> Pattern {
    support::var(name, "SortInt")
}

fn backend(side: &ValidatedDefinition, module: &str) -> Backend {
    Backend::new(
        &side.artifacts().definition_kore,
        module,
        BackendOptions::default(),
    )
    .expect("backend")
}

fn leaves(side: &ValidatedDefinition, module: &str, initial: &Pattern) -> Vec<AdaptedLeaf> {
    ExecutionAdapter::with_profile(SolverProfile::BUILD)
        .execute(&mut backend(side, module), initial, BUDGET)
        .expect("event-free execution")
        .leaves()
        .to_vec()
}

fn diagnosed(leaf: &AdaptedLeaf) -> bool {
    !leaf.diagnostics.is_empty()
        || leaf.candidate_diagnostics.iter().any(|d| !d.is_empty())
        || !leaf.remainder_diagnostics.is_empty()
}

fn state(leaf: &AdaptedLeaf) -> Pattern {
    codec::from_value(&leaf.branch.state).expect("leaf KORE reads")
}

fn contains_symbol(pattern: &Pattern, name: &str) -> bool {
    let mut found = false;
    k_rust::kore::walk::for_each_post_order(pattern, |node| {
        if let Pattern::Application { symbol, .. } = node {
            found |= symbol.name == name;
        }
    });
    found
}

// ---------------------------------------------------------------- AT12

/// A copy of `label` with `left` as its left-hand side and no identity or position attributes.
fn equation_copy(baseline: &kink_patch::Baseline, label: &str, left: Term) -> Sentence {
    let at = support::rule(baseline, label);
    let mut copy = baseline.sentence(&at).expect("rule").clone();
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
    let right = baseline
        .term(&TermRef::new(at, [0, 1]))
        .expect("right-hand side")
        .clone();
    if let Sentence::Rule { body, .. } = &mut copy {
        *body = Term::Rewrite {
            left: Box::new(left),
            right: Box::new(right),
        };
    }
    copy
}

/// `unbound.k`'s mutants that make a kept call evaluate: `freq` without its requires-only
/// condition (`freq(X) => 1`), and `part` with the equation `part(1) => 7` added.
fn unbound_mutants(validator: &NativeValidator) -> [(&'static str, Patch); 2] {
    let baseline = validator.baseline();
    let requires = TermRef::new(support::rule(baseline, "UNBOUND.freq"), [1]);
    let freq = Patch::new(vec![Edit::ReplaceTerm {
        expected: baseline.term(&requires).expect("requires").clone(),
        replacement: Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        },
        at: requires,
    }])
    .expect("freq patch");
    let one = Term::Token {
        token: "1".into(),
        sort: Sort::new("Int"),
    };
    let part = Patch::new(vec![Edit::InsertSentence {
        position: InsertPosition::After(support::rule(baseline, "UNBOUND.part")),
        ordinal: 0,
        sentence: equation_copy(baseline, "UNBOUND.part", Term::apply("part", vec![one])),
    }])
    .expect("part patch");
    [("Lblfreq", freq), ("Lblpart", part)]
}

/// AT12 at the leaf. A call written in a ground initial state that no rule rewrites, `done(c)`
/// for `c` in `freq(3)` and `part(1)`, is one `Stuck` leaf whose state is the ground term with
/// the call kept: no predicate, no diagnostic (`freq`'s requires-only variable has a contingent
/// condition, and `part` has no equation for 1), feasibility `Unknown` (the call is not a free
/// constructor). The mutant evaluates the call (`freq(3) = 1`, `part(1) = 7`) and its leaf is
/// the `Syntactic` `done(1)` or `done(7)`. Both definitions agree on every defined input, so the
/// two ground terminals denote the same value in a model of the baseline, but they are distinct
/// terms. Identical in both profiles. `fres(3)` (an unbound result variable) keeps the call with
/// an `UndecidedCondition` diagnostic instead, which the bridge maps to `BackendLimit`.
#[test]
fn kept_calls_in_ground_terminals_are_not_values() {
    let validator = NativeValidator::bind(support::load("unbound.k"), CompileOptions::default());
    let baseline = validator.compile_baseline().expect("unbound compiles");
    for ((call, patch), (argument, value)) in unbound_mutants(&validator)
        .into_iter()
        .zip([(3, 1), (1, 7)])
    {
        let initial = support::initial_state(
            support::app(
                "Lbldone",
                vec![support::app(call, vec![support::int(argument)])],
            ),
            "SortProg",
        );
        let kept = leaves(&baseline, "UNBOUND", &initial);
        let [leaf] = kept.as_slice() else {
            panic!("{call}: one baseline leaf, got {}", kept.len())
        };
        assert_eq!(
            (
                leaf.halt,
                leaf.feasibility,
                bridge::discarded(leaf),
                diagnosed(leaf)
            ),
            (HaltClass::Stuck, LeafFeasibility::Unknown, None, false),
            "{call}"
        );
        assert_eq!(
            state(leaf),
            initial,
            "{call}: the call is kept, unconstrained"
        );
        let mutant = validator.validate(&patch).expect("mutant compiles");
        let evaluated = leaves(&mutant, "UNBOUND", &initial);
        let [leaf] = evaluated.as_slice() else {
            panic!("{call}: one mutant leaf")
        };
        assert_eq!(
            (
                leaf.halt,
                leaf.feasibility,
                bridge::discarded(leaf),
                diagnosed(leaf)
            ),
            (HaltClass::Stuck, LeafFeasibility::Syntactic, None, false),
            "{call}"
        );
        assert_eq!(
            state(leaf),
            support::initial_state(
                support::app("Lbldone", vec![support::int(value)]),
                "SortProg"
            ),
            "{call}"
        );
    }
    let initial = support::initial_state(
        support::app(
            "Lbldone",
            vec![support::app("Lblfres", vec![support::int(3)])],
        ),
        "SortProg",
    );
    let kept = leaves(&baseline, "UNBOUND", &initial);
    let [leaf] = kept.as_slice() else {
        panic!("fres: one leaf")
    };
    assert_eq!((leaf.halt, diagnosed(leaf)), (HaltClass::Stuck, true));
    assert!(contains_symbol(&state(leaf), "Lblfres"));
}

// ---------------------------------------------------------------- T-UNSAT

/// One leaf with a K instance: its halt, feasibility and discard, and the relation query
/// answers at a K instance of it and at a valuation outside it.
#[derive(Debug, PartialEq, Eq)]
struct DefinednessRow {
    halt: HaltClass,
    feasibility: LeafFeasibility,
    discarded: Option<DiscardReason>,
    at_instance: Feasibility,
    outside: Feasibility,
}

/// The leaf's predicate conjuncts, below the generated top cell.
fn predicates(state: Pattern) -> Vec<Pattern> {
    state
        .into_conjuncts_at(&kore_sort("SortGeneratedTopCell"))
        .into_iter()
        .filter(|conjunct| {
            !matches!(
                conjunct,
                Pattern::Application { .. } | Pattern::DomainValue { .. } | Pattern::Variable(_)
            )
        })
        .collect()
}

/// A real-prefix path carrying `predicates`, so that `feasible` consults the solver.
fn real_path(predicates: &[Pattern]) -> PathInput {
    let sort = kore_sort("SortGeneratedTopCell");
    PathInput {
        test_id: "definedness".into(),
        path_ordinal: 0,
        path_key: None,
        complete: true,
        stop: PathStop::Terminal,
        execution_stop: ExecutionStop::Terminal,
        execution_terminal: None,
        events: Vec::new(),
        path_predicate: match predicates {
            [] => Pattern::Top { sort },
            [predicate] => predicate.clone(),
            more => Pattern::And {
                sort,
                arguments: more.to_vec(),
            },
        },
        equivalences: Vec::new(),
        inequalities: Vec::new(),
    }
}

fn flatten_and(pattern: &Pattern, out: &mut Vec<Pattern>) {
    match pattern {
        Pattern::And { arguments, .. } => {
            for argument in arguments {
                flatten_and(argument, out);
            }
        }
        other => out.push(other.clone()),
    }
}

/// The divisors of every `/Int` in `pattern` that is not under a `\not`.
fn divisors(pattern: &Pattern, out: &mut Vec<Pattern>) {
    match pattern {
        Pattern::Not { .. } => {}
        Pattern::Application { symbol, arguments } => {
            if symbol.name == "Lbl'UndsSlsh'Int'Unds'" {
                out.push(arguments[1].clone());
            }
            for argument in arguments {
                divisors(argument, out);
            }
        }
        Pattern::Equals { left, right, .. } => {
            divisors(left, out);
            divisors(right, out);
        }
        Pattern::And { arguments, .. } | Pattern::Or { arguments, .. } => {
            for argument in arguments {
                divisors(argument, out);
            }
        }
        _ => {}
    }
}

/// `\not(\equals(divisor, 0))`, k-rust's printed definedness of `_ /Int divisor`.
fn nonzero(divisor: &Pattern) -> Pattern {
    Pattern::Not {
        sort: kore_sort("SortGeneratedTopCell"),
        argument: Box::new(Pattern::Equals {
            operand_sort: Box::new(kore_sort("SortInt")),
            result_sort: kore_sort("SortGeneratedTopCell"),
            left: Box::new(divisor.clone()),
            right: Box::new(support::int(0)),
        }),
    }
}

/// An independent reading of a printed predicate (k-rust `condition.rs:168-182, 255-261`,
/// `rewrite/apply.rs:1245-1249`): every conjunction that applies `/Int` to a divisor `d`, at
/// the top or directly under a `\not`, also has the conjunct `d =/= 0` (or a `\ceil`), so a
/// remainder `\not(A)` keeps the definedness inside the negation next to its atom. Returns the
/// number of conjunctions that apply `/Int`.
fn definedness_beside_division(conjuncts: &[Pattern]) -> usize {
    let mut flat = Vec::new();
    for conjunct in conjuncts {
        flatten_and(conjunct, &mut flat);
    }
    let mut found = Vec::new();
    for conjunct in &flat {
        divisors(conjunct, &mut found);
    }
    for divisor in &found {
        assert!(
            flat.contains(&nonzero(divisor))
                || flat.iter().any(|c| matches!(c, Pattern::Ceil { .. })),
            "no definedness for /Int by {divisor:?} beside it in {flat:?}"
        );
    }
    let nested = flat
        .iter()
        .map(|conjunct| match conjunct {
            Pattern::Not { argument, .. } => definedness_beside_division(&[(**argument).clone()]),
            _ => 0,
        })
        .sum::<usize>();
    usize::from(!found.is_empty()) + nested
}

fn equal(name: &str, value: i64) -> TermRelation {
    TermRelation {
        left: int(name),
        right: support::int(value),
    }
}

/// The rows of `program`'s leaves, each with one K instance and one valuation outside it, and
/// the number of conjunctions over `/Int` that the independent reading checked.
fn definedness_rows(
    fixture: &str,
    module: &str,
    program: Pattern,
    valuations: &[(Vec<TermRelation>, Vec<TermRelation>)],
) -> (Vec<DefinednessRow>, usize) {
    let validator = NativeValidator::bind(support::load(fixture), CompileOptions::default());
    let side = validator.compile_baseline().expect("fixture compiles");
    let initial = support::initial_state(program, "SortProg");
    let leaves = leaves(&side, module, &initial);
    assert_eq!(
        leaves.len(),
        valuations.len(),
        "{fixture}: one valuation pair per leaf"
    );
    let mut checked = 0;
    let rows = backend(&side, module)
        .with_solver(None, |definition, solver| {
            let relations =
                BackendRelations::shared(definition, solver, TestInitialState::of_test(&initial));
            Ok::<_, BackendError>(
                leaves
                    .iter()
                    .zip(valuations)
                    .map(|(leaf, (instance, outside))| {
                        let predicates = predicates(state(leaf));
                        checked += definedness_beside_division(&predicates);
                        let path = real_path(&predicates);
                        DefinednessRow {
                            halt: leaf.halt,
                            feasibility: leaf.feasibility,
                            discarded: bridge::discarded(leaf),
                            at_instance: relations.feasible(&path, instance),
                            outside: relations.feasible(&path, outside),
                        }
                    })
                    .collect(),
            )
        })
        .expect("relations");
    (rows, checked)
}

fn row(
    halt: HaltClass,
    feasibility: LeafFeasibility,
    at_instance: Feasibility,
    outside: Feasibility,
) -> DefinednessRow {
    DefinednessRow {
        halt,
        feasibility,
        discarded: None,
        at_instance,
        outside,
    }
}

/// T-UNSAT regression (D-B). `partialreq.k`: `pos(X, Y) => yes(X /Int Y) requires X /Int Y >Int
/// 0` and `same(X, Y) => halt requires X /Int Y <=Int X /Int Y`; `guardeddiv.k`: `divide(I1,
/// I2) => done(I1 /Int I2) requires I2 =/=Int 0`. Each runs from a symbolic state with the
/// divisor free (PathSet, strategy all, through `ExecutionAdapter`), and every leaf has a K
/// instance: the applied leaf at divisor 1 (`X = Y = 1` for `pos`), the remainder at divisor 0,
/// where the division is undefined, so the `requires` does not hold and the state is stuck. For
/// each leaf: (i) its feasibility is not `Unsat` and the bridge does not discard it; (ii) the
/// relation query of a real-prefix path over its constraints, assuming the K instance, is not
/// `Unsat`; (iii) the independent reading finds the definedness `d =/= 0` beside every `/Int`,
/// inside the remainder's negation. `same`'s remainder is the discriminating row: its condition
/// holds wherever it is defined, so without the definedness in the negation a solver that treats
/// `/Int` as total would refute it, discarding the stuck instances `Y = 0`. The `outside`
/// column assumes a valuation outside the leaf (the other branch's divisor); with Z3 it is
/// `Unsat`, so the solver is consulted and the instance column is a real answer.
///
/// Measured with Z3: no violating leaf, so no guard (D-B default). The applied leaves of `same`
/// and `divide` and `divide`'s remainder (`I2 = 0`, no `/Int` left) are `Solver` with the
/// instance `Sat`; `pos`'s two leaves and `same`'s remainder keep an `/Int` atom, which does not
/// translate exactly, so they are `Unknown` and the instance query is `Unknown` (a solver `Sat`
/// is not evidence there), never `Unsat`. Every `outside` column is `Unsat`. Without Z3 each run is one
/// `Indeterminate` leaf at the initial state (the `requires` needs a solver), with no predicate:
/// the relation query is empty after eliminating the binding, so both columns are `Sat`, and no
/// `Unsat` occurs anywhere.
#[test]
fn partial_conditions_keep_their_definedness_in_remainders() {
    use Feasibility::{Sat, Unsat};
    use HaltClass::{Indeterminate, Stuck};
    use LeafFeasibility::{Solver, Syntactic, Unknown};
    let cases = [
        (
            "partialreq.k",
            "PARTIALREQ",
            support::app("Lblpos", vec![int("X"), int("Y")]),
            vec![
                (vec![equal("X", 1), equal("Y", 1)], vec![equal("Y", 0)]),
                (vec![equal("Y", 0)], vec![equal("X", 1), equal("Y", 1)]),
            ],
            vec![
                row(Stuck, Unknown, Feasibility::Unknown, Unsat),
                row(Stuck, Unknown, Feasibility::Unknown, Unsat),
            ],
            2,
        ),
        (
            "partialreq.k",
            "PARTIALREQ",
            support::app("Lblsame", vec![int("X"), int("Y")]),
            vec![
                (vec![equal("Y", 1)], vec![equal("Y", 0)]),
                (vec![equal("Y", 0)], vec![equal("Y", 1)]),
            ],
            vec![
                row(Stuck, Solver, Sat, Unsat),
                row(Stuck, Unknown, Feasibility::Unknown, Unsat),
            ],
            1,
        ),
        (
            "guardeddiv.k",
            "GUARDEDDIV",
            support::app("Lbldivide", vec![int("I1"), int("I2")]),
            vec![
                (vec![equal("I2", 1)], vec![equal("I2", 0)]),
                (vec![equal("I2", 0)], vec![equal("I2", 1)]),
            ],
            vec![
                row(Stuck, Solver, Sat, Unsat),
                row(Stuck, Solver, Sat, Unsat),
            ],
            0,
        ),
    ];
    for (fixture, module, program, valuations, z3_rows, z3_checked) in cases {
        let valuations = if cfg!(feature = "z3") {
            valuations
        } else {
            valuations[..1].to_vec()
        };
        let (rows, checked) = definedness_rows(fixture, module, program, &valuations);
        if cfg!(feature = "z3") {
            assert_eq!(rows, z3_rows, "{fixture} {module}");
            assert_eq!(checked, z3_checked, "{fixture} {module}");
        } else {
            assert_eq!(
                rows,
                [row(Indeterminate, Syntactic, Sat, Sat)],
                "{fixture} {module}"
            );
            assert_eq!(checked, 0);
        }
        assert!(
            rows.iter()
                .all(|row| row.feasibility != LeafFeasibility::Unsat
                    && row.discarded.is_none()
                    && row.at_instance != Unsat),
            "{fixture} {module}: a leaf with a K instance is refuted"
        );
    }
}

// ---------------------------------------------------------------- TV-01 review 2: T-UNSAT attacks

/// One leaf of a review attack: the head it reached (the first listed head whose symbol it
/// contains), its halt, feasibility and discard, and the relation answer at the K instance the
/// attack names for that head.
#[derive(Debug)]
struct ReviewLeaf {
    head: &'static str,
    halt: HaltClass,
    feasibility: LeafFeasibility,
    discarded: Option<DiscardReason>,
    at_instance: Option<Feasibility>,
}

fn review_leaves(
    fixture: &str,
    module: &str,
    initial: &Pattern,
    instances: &[(&'static str, Vec<TermRelation>)],
) -> Vec<ReviewLeaf> {
    let validator = NativeValidator::bind(
        support::load_path(&std::path::Path::new(support::DIR).join(fixture), module),
        CompileOptions::default(),
    );
    let side = validator.compile_baseline().expect("fixture compiles");
    let leaves = leaves(&side, module, initial);
    backend(&side, module)
        .with_solver(None, |definition, solver| {
            let relations =
                BackendRelations::shared(definition, solver, TestInitialState::of_test(initial));
            Ok::<_, BackendError>(
                leaves
                    .iter()
                    .map(|leaf| {
                        let leaf_state = state(leaf);
                        let named = instances
                            .iter()
                            .find(|(head, _)| contains_symbol(&leaf_state, &format!("Lbl{head}")));
                        let path = real_path(&predicates(leaf_state));
                        ReviewLeaf {
                            head: named.map_or("other", |(head, _)| head),
                            halt: leaf.halt,
                            feasibility: leaf.feasibility,
                            discarded: bridge::discarded(leaf),
                            at_instance: named
                                .map(|(_, instance)| relations.feasible(&path, instance)),
                        }
                    })
                    .collect(),
            )
        })
        .expect("relations")
}

/// A K instance per leaf head.
type Instances = Vec<(&'static str, Vec<TermRelation>)>;

/// Fails if any leaf with a named K instance is refuted: Unsat feasibility, a discard, or an
/// Unsat relation query at the instance.
fn assert_no_refuted_instance(label: &str, rows: &[ReviewLeaf]) {
    eprintln!("TV01-REVIEW {label}: {rows:?}");
    for row in rows {
        if row.at_instance.is_some() {
            assert!(
                row.feasibility != LeafFeasibility::Unsat
                    && row.halt != HaltClass::Vacuous
                    && row.discarded.is_none()
                    && row.at_instance != Some(Feasibility::Unsat),
                "{label}: a leaf with a K instance is refuted: {row:?}"
            );
        }
    }
}

/// TV-01 review 2, T-UNSAT attack 1: complementary conditions over a partial term
/// (`partialreq.k (TV01UNSAT)`). For `dv` (`/Int`) and `md` (`%Int`) at `Y = 0`, and for `cmp` (the user
/// partial function `part`) at `X = 1`, neither condition is defined, so the stuck remainder
/// has K instances; with both negations read as total it is `not P and not (not P)`, which a
/// solver refutes. `ow` pits `part`'s condition against an owise rule, whose leaf has the
/// instance `X = 1`. Every leaf with a named instance must stay unrefuted in both profiles;
/// with Z3, `dv` and `md` must also keep a leaf for the remainder (else instances are lost).
#[test]
fn review_complementary_partial_conditions_keep_their_stuck_instances() {
    let x = || int("X");
    let y = || int("Y");
    let cases: [(&str, Pattern, Instances); 4] = [
        (
            "dv",
            support::app("Lbldv", vec![x(), y()]),
            vec![
                ("dv", vec![equal("X", 1), equal("Y", 0)]),
                ("yes", vec![equal("X", 1), equal("Y", 1)]),
                ("no", vec![equal("X", 0), equal("Y", 1)]),
            ],
        ),
        (
            "md",
            support::app("Lblmd", vec![x(), y()]),
            vec![
                ("md", vec![equal("X", 1), equal("Y", 0)]),
                ("yes", vec![equal("X", 0), equal("Y", 1)]),
                ("no", vec![equal("X", 1), equal("Y", 2)]),
            ],
        ),
        (
            "cmp",
            support::app("Lblcmp", vec![x()]),
            vec![("cmp", vec![equal("X", 1)]), ("yes", vec![equal("X", 0)])],
        ),
        (
            "ow",
            support::app("Lblow", vec![x()]),
            vec![
                ("ow", vec![equal("X", 1)]),
                ("yes", vec![equal("X", 0)]),
                ("no", vec![equal("X", 1)]),
            ],
        ),
    ];
    for (label, program, instances) in cases {
        let initial = support::initial_state(program, "SortProg");
        let rows = review_leaves("partialreq.k", "TV01UNSAT", &initial, &instances);
        assert_no_refuted_instance(label, &rows);
        if cfg!(feature = "z3") && matches!(label, "dv" | "md") {
            assert!(
                rows.iter().any(|row| row.head == label),
                "{label}: no leaf keeps the undefined-divisor instances"
            );
        }
    }
}

/// TV-01 deliverable 5 (R2-F1): test-written conditions with partial applications beneath
/// `\not` must be REFUSED by the campaign's shared input boundary before execution.
/// `neither` has the instance X = 1, Y = 0 yet k-rust previously halted it Vacuous at depth 0.
/// `reflexive` and `reflexive-part` previously kept Stuck leaves; they match the same admission
/// rule. Measured in both profiles: all three are REFUSED (`InvalidState`) before execution;
/// campaign admission maps these to `BaselineOracleFailed`. This boundary does not inspect
/// k-rust-built leaves. R3-F1 adds implies/iff/predicate-equals negation notations:
/// before the polarity guard, each was admitted and produced (Vacuous, Unknown, depth 0,
/// discarded Vacuous) in both profiles; after it, each is REFUSED before execution.
#[test]
fn review_test_written_partial_conditions_are_not_refuted() {
    const DIV: &str = r"Lbl'UndsSlsh'Int'Unds'{}(X:SortInt{}, Y:SortInt{})";
    let not_equals = |atom: String, value: &str| {
        format!(
            r#"\not{{SortGeneratedTopCell{{}}}}(\equals{{SortBool{{}}, SortGeneratedTopCell{{}}}}({atom}, \dv{{SortBool{{}}}}("{value}")))"#
        )
    };
    let reflexive = not_equals(
        format!("Lbl'UndsEqlsEqls'Int'Unds'{{}}({DIV}, {DIV})"),
        "true",
    );
    let positive = format!(r#"Lbl'Unds-GT-'Int'Unds'{{}}({DIV}, \dv{{SortInt{{}}}}("0"))"#);
    let neither = format!(
        r"\and{{SortGeneratedTopCell{{}}}}({}, {})",
        not_equals(positive.clone(), "true"),
        not_equals(positive.clone(), "false")
    );
    // R3-F1: these notations express negation in matching logic without a literal Not.
    let negation_equivalent_pair = |connective: &str| {
        let negate = |value: &str| {
            format!(
                r#"\{connective}(\equals{{SortBool{{}},SortGeneratedTopCell{{}}}}({positive},\dv{{SortBool{{}}}}("{value}")),\bottom{{SortGeneratedTopCell{{}}}}())"#
            )
        };
        format!(
            r"\and{{SortGeneratedTopCell{{}}}}({},{})",
            negate("true"),
            negate("false")
        )
    };
    let mut measured = Vec::new();
    const PART: &str = r"Lblpart{}(X:SortInt{})";
    let reflexive_part = not_equals(
        format!("Lbl'UndsEqlsEqls'Int'Unds'{{}}({PART}, {PART})"),
        "true",
    );
    for (label, condition) in [
        ("reflexive", reflexive),
        ("neither", neither),
        ("reflexive-part", reflexive_part),
        (
            "implies",
            negation_equivalent_pair("implies{SortGeneratedTopCell{}}"),
        ),
        (
            "iff",
            negation_equivalent_pair("iff{SortGeneratedTopCell{}}"),
        ),
        (
            "pred-equals",
            negation_equivalent_pair("equals{SortGeneratedTopCell{},SortGeneratedTopCell{}}"),
        ),
    ] {
        let condition =
            k_rust::kore::parser::parse_pattern(&condition).expect("the condition parses");
        let validator = NativeValidator::bind(
            support::load_path(
                &std::path::Path::new(support::DIR).join("partialreq.k"),
                "TV01UNSAT",
            ),
            CompileOptions::default(),
        );
        let side = validator.compile_baseline().expect("fixture compiles");
        let initial = Pattern::And {
            sort: kore_sort("SortGeneratedTopCell"),
            arguments: vec![
                support::initial_state(
                    support::app("Lblpair", vec![int("X"), int("Y")]),
                    "SortProg",
                ),
                condition,
            ],
        };
        let mut backend = backend(&side, "TV01UNSAT");
        // The same input admission entry point run_campaign uses, before either adapter path.
        let admission = bridge::validate_test_initial_state(&mut backend, &initial);
        let mut executed = false;
        let result = admission.and_then(|()| {
            executed = true;
            ExecutionAdapter::with_profile(SolverProfile::BUILD).execute(
                &mut backend,
                &initial,
                BUDGET,
            )
        });
        eprintln!(
            "TV01-INPUT {label}: executed={executed}, leaves={:?}",
            result.as_ref().ok().map(|execution| execution
                .leaves()
                .iter()
                .map(|leaf| (
                    leaf.halt,
                    leaf.feasibility,
                    leaf.branch.depth,
                    bridge::discarded(leaf)
                ))
                .collect::<Vec<_>>())
        );
        measured.push((label, executed, result));
    }
    eprintln!("TV01-INPUT measured: {measured:?}");
    for (label, executed, result) in measured {
        assert!(!executed, "{label}: must be REFUSED before execution");
        assert!(
            matches!(
                result,
                Err(kink_native::execution::ExecutionAdapterFailure::InvalidState(_))
            ),
            "{label}: expected REFUSED invalid test input, got {result:?}"
        );
    }
}

/// Input-boundary coverage: negation at arbitrary depth (including double negation),
/// undeclared totality and missing symbols fail closed. Constructors, injections, domain
/// values and declared-total functions remain admitted; a partial call outside negation
/// does not match this guard (VI-T10 records that remaining premise question). Regression
/// (TV-01 fix 1, R1-F1): the identity-injection row moved from admitted to refused, because
/// only a normal-form injection is admitted (`injections_are_values_only_in_normal_form`).
#[test]
fn test_input_negations_require_declared_totality_at_any_depth() {
    let mut backend = Backend::new(
        r"[]
        module MAIN
            sort SortS{} []
            symbol Lbla{}() : SortS{} [constructor{}()]
            symbol Lblwrap{}(SortS{}) : SortS{} [constructor{}()]
            symbol Lbltotal{}(SortS{}) : SortS{} [function{}(), total{}()]
            symbol Lblpartial{}(SortS{}) : SortS{} [function{}()]
            symbol Lblundeclared{}(SortS{}) : SortS{} [function{}()]
            symbol Lblbinary{}(SortS{},SortS{}) : SortS{} [function{}()]
        endmodule []",
        "MAIN",
        BackendOptions::default(),
    )
    .expect("backend");
    for (source, refused) in [
        (
            r"\not{SortS{}}(\ceil{SortS{},SortS{}}(Lblpartial{}(Lbla{}())))",
            true,
        ),
        (
            r"\exists{SortS{}}(V:SortS{},\and{SortS{}}(\top{SortS{}}(),\not{SortS{}}(\not{SortS{}}(\ceil{SortS{},SortS{}}(Lblpartial{}(Lbla{}()))))))",
            true,
        ),
        (
            r"\not{SortS{}}(\ceil{SortS{},SortS{}}(Lblundeclared{}(Lbla{}())))",
            true,
        ),
        (
            r"\not{SortS{}}(\ceil{SortS{},SortS{}}(Lblmissing{}(Lbla{}())))",
            true,
        ),
        (
            r"\not{SortS{}}(\ceil{SortS{},SortS{}}(Lbltotal{}(Lblwrap{}(Lbla{}()))))",
            false,
        ),
        // Moved by TV-01 fix 1 (review R1-F1), toward refusal: an identity injection is not
        // k-rust normal form and is refused at any polarity (was admitted).
        (
            r"\not{SortS{}}(\ceil{SortS{},SortS{}}(inj{SortS{},SortS{}}(Lbla{}())))",
            true,
        ),
        (
            r#"\not{SortS{}}(\ceil{SortInt{},SortS{}}(\dv{SortInt{}}("0")))"#,
            false,
        ),
        (r"\ceil{SortS{},SortS{}}(Lblpartial{}(Lbla{}()))", false),
        // Positive whitelist: partial applications here remain VI-T10 (ii).
        (
            r"\and{SortS{}}(\ceil{SortS{},SortS{}}(Lblpartial{}(Lbla{}())),\top{SortS{}}())",
            false,
        ),
        (
            r"\or{SortS{}}(\ceil{SortS{},SortS{}}(Lblpartial{}(Lbla{}())),\bottom{SortS{}}())",
            false,
        ),
        (
            r"\forall{SortS{}}(V:SortS{},\exists{SortS{}}(W:SortS{},\ceil{SortS{},SortS{}}(Lblpartial{}(Lbla{}()))))",
            false,
        ),
        (
            r"\equals{SortS{},SortS{}}(Lblpartial{}(Lbla{}()),Lbla{}())",
            false,
        ),
        (
            r"\in{SortS{},SortS{}}(Lblpartial{}(Lbla{}()),Lbla{}())",
            false,
        ),
        // Logical negation notations and every non-whitelisted connective.
        (r"\floor{SortS{},SortS{}}(Lblpartial{}(Lbla{}()))", true),
        (
            r"\ceil{SortS{},SortS{}}(\floor{SortS{},SortS{}}(Lblpartial{}(Lbla{}())))",
            true,
        ),
        (
            r"\floor{SortS{},SortS{}}(\ceil{SortS{},SortS{}}(Lblpartial{}(Lbla{}())))",
            true,
        ),
        (
            r"\forall{SortS{}}(V:SortS{},\or{SortS{}}(\bottom{SortS{}}(),\exists{SortS{}}(W:SortS{},\implies{SortS{}}(\top{SortS{}}(),\ceil{SortS{},SortS{}}(Lblpartial{}(Lbla{}()))))))",
            true,
        ),
        (
            r"\implies{SortS{}}(\ceil{SortS{},SortS{}}(Lblpartial{}(Lbla{}())),\top{SortS{}}())",
            true,
        ),
        (
            r"\iff{SortS{}}(\top{SortS{}}(),\ceil{SortS{},SortS{}}(Lblpartial{}(Lbla{}())))",
            true,
        ),
        (
            r"\equals{SortS{},SortS{}}(\ceil{SortS{},SortS{}}(Lblpartial{}(Lbla{}())),\bottom{SortS{}}())",
            true,
        ),
        (
            r"\equals{SortS{},SortS{}}(\top{SortS{}}(),Lblpartial{}(Lbla{}()))",
            true,
        ),
        (
            r"\in{SortS{},SortS{}}(Lblpartial{}(Lbla{}()),\ceil{SortS{},SortS{}}(Lbla{}()))",
            true,
        ),
        (
            r"\in{SortS{},SortS{}}(\ceil{SortS{},SortS{}}(Lbla{}()),Lblpartial{}(Lbla{}()))",
            true,
        ),
        (r"\next{SortS{}}(Lblpartial{}(Lbla{}()))", true),
        (r"\rewrites{SortS{}}(Lbla{}(),Lblpartial{}(Lbla{}()))", true),
        (
            r"\not{SortS{}}(\ceil{SortS{},SortS{}}(\left-assoc{}(Lblbinary{}(Lbla{}(),Lbla{}(),Lbla{}()))))",
            true,
        ),
        (r"\floor{SortS{},SortS{}}(Lblmissing{}(Lbla{}()))", true),
        (
            r"\floor{SortS{},SortS{}}(Lbltotal{}(Lblpartial{}(Lbla{}())))",
            true,
        ),
        (
            r"\floor{SortS{},SortS{}}(Lbltotal{}(Lblwrap{}(Lbla{}())))",
            false,
        ),
    ] {
        let state = k_rust::kore::parser::parse_pattern(source)
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert_eq!(
            bridge::validate_test_initial_state(&mut backend, &state).is_err(),
            refused,
            "{source}"
        );
    }
}

// ---------------------------------------------------------------- TV-01 review 2: bridge counterfactual

/// One bridged path, reduced: complete, stop, and the terminal (kind and whether it holds a
/// `part` or `fsel` application).
type ReviewPath = (
    bool,
    PathStop,
    Option<(kink_pattern::ExecutionTerminalKind, bool)>,
);

fn review_paths(bridged: &bridge::BridgedPaths) -> Vec<ReviewPath> {
    bridged
        .paths
        .iter()
        .map(|path| {
            (
                path.complete,
                path.stop,
                path.execution_terminal.as_ref().map(|terminal| {
                    (
                        terminal.kind,
                        contains_symbol(&terminal.state, "Lblpart")
                            || contains_symbol(&terminal.state, "Lblfsel"),
                    )
                }),
            )
        })
        .collect()
}

/// TV-01 review 2: with `part(0) => 7` disabled, the mutant keeps a call in each ground state.
/// The side's own definition-independence check must leave every path incomplete with no terminal in both profiles.
/// The review report preserves the temporary counterfactual that bypassed this check; persisted callers meet the bridge contract.
#[test]
fn review_kept_calls_do_not_supply_terminals() {
    let validator = NativeValidator::bind(
        support::load_path(
            &std::path::Path::new(support::DIR).join("unbound.k"),
            "TV01TERMINAL",
        ),
        CompileOptions::default(),
    );
    let baseline = validator.baseline();
    let requires = TermRef::new(support::rule(baseline, "TV01TERMINAL.part"), [1]);
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        expected: baseline.term(&requires).expect("requires").clone(),
        replacement: Term::Token {
            token: "false".into(),
            sort: Sort::new("Bool"),
        },
        at: requires,
    }])
    .expect("patch");
    let mutant = validator.validate(&patch).expect("mutant compiles");
    let sorts = kink_pattern::SymbolSorts::from_definition(
        &k_rust::kore::parser::parse_definition(&mutant.artifacts().definition_kore)
            .expect("compiled KORE parses"),
    );
    let part0 = || support::app("Lblpart", vec![support::int(0)]);
    let int_val = |value: Pattern| {
        k_rust::kompile::initial_configuration::kore_application(
            "inj",
            vec![kore_sort("SortInt"), kore_sort("SortVal")],
            vec![value],
        )
    };
    let states = [
        ("inj", support::app("Lbldone", vec![int_val(part0())])),
        (
            "ctor",
            support::app("Lbldone", vec![support::app("Lblwrap", vec![part0()])]),
        ),
        ("class", support::app("Lblcheck", vec![part0()])),
        ("owise-rule", support::app("Lblsel", vec![part0()])),
        (
            "owise-fn",
            support::app(
                "Lbldone",
                vec![int_val(support::app("Lblfsel", vec![part0()]))],
            ),
        ),
    ];
    let normal = |_: &Pattern| kink_pattern::ExecutionTerminalKind::Normal;
    for (label, program) in states {
        let initial = support::initial_state(program, "SortProg");
        let mut side = backend(&mutant, "TV01TERMINAL");
        let execution = ExecutionAdapter::with_profile(SolverProfile::BUILD)
            .execute(&mut side, &initial, BUDGET)
            .expect("event-free execution");
        let context = bridge::BridgeContext {
            test_id: label,
            classify: &normal,
            sorts: &sorts,
        };
        let guarded = side
            .with_solver(None, |definition, solver| {
                let decider = kink_native::step_events::ObservationDecider::new(
                    definition,
                    solver,
                    TestInitialState::of_test(&initial),
                );
                Ok::<_, BackendError>(bridge::paths_from_execution(
                    &execution,
                    &context,
                    &|term| decider.definition_independent(term),
                ))
            })
            .expect("backend definition");
        let guarded = review_paths(&guarded.expect("guarded bridge"));
        eprintln!("TV01-REVIEW bridge {label}: guarded {guarded:?}");
        assert!(
            guarded
                .iter()
                .all(|(complete, _, terminal)| !complete && terminal.is_none()),
            "{label}: a guarded path is complete: {guarded:?}"
        );
    }
}

// ---------------------------------------------------------------- TV-01 fix 1: identity injections

/// `inj{From,To}(value)`.
fn inj(from: &str, to: &str, value: Pattern) -> Pattern {
    k_rust::kompile::initial_configuration::kore_application(
        "inj",
        vec![kore_sort(from), kore_sort(to)],
        vec![value],
    )
}

/// TV-01 fix 1 (review R1-F1): a sort injection is a value, and admissible test input, only in
/// k-rust's normal form: strict (a proper subsort source), one argument whose sort is the
/// source, and not nested. The identity `inj{SortInt,SortInt}(7)`, the reversed
/// `inj{SortVal,SortInt}`, the nested `inj{SortVal,SortKItem}(inj{SortInt,SortVal}(7))` and the
/// ill-sorted `inj{SortInt,SortVal}(true)` and `inj{SortInt,SortVal}(wrap(7))` are none. Each
/// row checks the decider's definition independence of the program and the input guard on the
/// initial state holding it (refused exactly when not independent here, since every other
/// application is a free constructor).
#[test]
fn injections_are_values_only_in_normal_form() {
    let validator = NativeValidator::bind(
        support::load_path(
            &std::path::Path::new(support::DIR).join("unbound.k"),
            "TV01TERMINAL",
        ),
        CompileOptions::default(),
    );
    let side = validator.compile_baseline().expect("fixture compiles");
    let seven = || support::int(7);
    let truth = || Pattern::DomainValue {
        sort: kore_sort("SortBool"),
        value: "true".into(),
    };
    let done = |value: Pattern| support::app("Lbldone", vec![value]);
    let check = |value: Pattern| support::app("Lblcheck", vec![value]);
    let wrap = |value: Pattern| support::app("Lblwrap", vec![value]);
    let rows = [
        ("strict", done(inj("SortInt", "SortVal", seven())), true),
        ("strict-ctor", done(wrap(seven())), true),
        (
            "strict-var",
            done(inj("SortInt", "SortVal", int("X"))),
            true,
        ),
        ("canonical-check", check(seven()), true),
        ("identity", check(inj("SortInt", "SortInt", seven())), false),
        (
            "identity-under-strict",
            done(inj(
                "SortInt",
                "SortVal",
                inj("SortInt", "SortInt", seven()),
            )),
            false,
        ),
        (
            "identity-val",
            done(inj("SortVal", "SortVal", wrap(seven()))),
            false,
        ),
        (
            "reversed",
            check(inj("SortVal", "SortInt", wrap(seven()))),
            false,
        ),
        (
            "ill-sorted-dv",
            done(inj("SortInt", "SortVal", truth())),
            false,
        ),
        (
            "ill-sorted-ctor",
            done(inj("SortInt", "SortVal", wrap(seven()))),
            false,
        ),
        (
            "ill-sorted-var",
            done(inj("SortInt", "SortVal", support::var("V", "SortVal"))),
            false,
        ),
    ];
    let mut backend = backend(&side, "TV01TERMINAL");
    for (label, program, expected) in rows {
        let initial = support::initial_state(program.clone(), "SortProg");
        let independent = backend
            .with_solver(None, |definition, solver| {
                let decider = kink_native::step_events::ObservationDecider::new(
                    definition,
                    solver,
                    TestInitialState::of_test(&initial),
                );
                Ok::<_, BackendError>(decider.definition_independent(&program))
            })
            .expect("backend definition");
        let admitted = bridge::validate_test_initial_state(&mut backend, &initial).is_ok();
        eprintln!("TV01-FIX1 {label}: independent={independent} admitted={admitted}");
        assert_eq!(independent, expected, "{label}: definition independence");
        assert_eq!(admitted, expected, "{label}: input admission");
    }
    // A nested pair: the program itself is well formed, the term under `kseq` is not normal.
    let nested = inj("SortVal", "SortKItem", inj("SortInt", "SortVal", seven()));
    let nested_independent = backend
        .with_solver(None, |definition, solver| {
            let decider = kink_native::step_events::ObservationDecider::new(
                definition,
                solver,
                TestInitialState::of_test(&nested),
            );
            Ok::<_, BackendError>(decider.definition_independent(&nested))
        })
        .expect("backend definition");
    assert!(!nested_independent, "a nested injection pair is not normal");
    let nested_state = support::initial_state(
        support::app("Lblhold", vec![support::app("LblListItem", vec![nested])]),
        "SortProg",
    );
    assert!(
        bridge::validate_test_initial_state(&mut backend, &nested_state).is_err(),
        "a nested injection pair is refused as test input"
    );
}

/// TV-01 fix 1 (review R1-F1), below the input guard: the baseline `check(7) => done(7)` leaves
/// a test-written `check(inj{SortInt,SortInt}(7))` stuck. Its stuck term is not a value, so the
/// guarded bridge gives an incomplete path with no terminal in both profiles (before the fix:
/// a complete `Normal` terminal, compared against the mutant's `done(7)`).
#[test]
fn identity_injections_do_not_supply_terminals() {
    let validator = NativeValidator::bind(
        support::load_path(
            &std::path::Path::new(support::DIR).join("unbound.k"),
            "TV01TERMINAL",
        ),
        CompileOptions::default(),
    );
    let side = validator.compile_baseline().expect("fixture compiles");
    let sorts = kink_pattern::SymbolSorts::from_definition(
        &k_rust::kore::parser::parse_definition(&side.artifacts().definition_kore)
            .expect("compiled KORE parses"),
    );
    let normal = |_: &Pattern| kink_pattern::ExecutionTerminalKind::Normal;
    for (label, program, complete) in [
        (
            "identity",
            support::app("Lblcheck", vec![inj("SortInt", "SortInt", support::int(7))]),
            false,
        ),
        (
            "canonical",
            support::app("Lblcheck", vec![support::int(3)]),
            true,
        ),
    ] {
        let initial = support::initial_state(program, "SortProg");
        let mut backend = backend(&side, "TV01TERMINAL");
        let execution = ExecutionAdapter::with_profile(SolverProfile::BUILD)
            .execute(&mut backend, &initial, BUDGET)
            .expect("event-free execution");
        let halts = execution
            .leaves()
            .iter()
            .map(|leaf| leaf.halt)
            .collect::<Vec<_>>();
        assert_eq!(halts, [HaltClass::Stuck], "{label}: the baseline is stuck");
        let context = bridge::BridgeContext {
            test_id: label,
            classify: &normal,
            sorts: &sorts,
        };
        let bridged = backend
            .with_solver(None, |definition, solver| {
                let decider = kink_native::step_events::ObservationDecider::new(
                    definition,
                    solver,
                    TestInitialState::of_test(&initial),
                );
                Ok::<_, BackendError>(bridge::paths_from_execution(
                    &execution,
                    &context,
                    &|term| decider.definition_independent(term),
                ))
            })
            .expect("backend definition")
            .expect("guarded bridge");
        let paths = bridged
            .paths
            .iter()
            .map(|path| (path.complete, path.stop, path.execution_terminal.is_some()))
            .collect::<Vec<_>>();
        eprintln!("TV01-FIX1 bridge {label}: {paths:?}");
        let expected = if complete {
            (true, PathStop::Terminal, true)
        } else {
            (false, PathStop::SolverUnknown, false)
        };
        assert_eq!(paths, [expected], "{label}");
    }
}

/// VI-T10 R4-D1: both equalities hold at Y = 0 in matching logic (bottom equals bottom).
/// Before the guard Z3 retained a Trivial leaf but refuted its X=1,Y=0 instance as Unsat;
/// refuse before execution so that no relation query can use that test predicate.
#[test]
fn audit_vi_t10_partial_equalities_require_input_refusal() {
    const DIV: &str = r"Lbl'UndsSlsh'Int'Unds'{}(X:SortInt{},Y:SortInt{})";
    let positive = format!(r#"Lbl'Unds-GT-'Int'Unds'{{}}({DIV},\dv{{SortInt{{}}}}("0"))"#);
    let conditions = [
        (
            "eq-succ",
            format!(
                r#"\equals{{SortInt{{}},SortGeneratedTopCell{{}}}}({DIV},Lbl'UndsPlus'Int'Unds'{{}}({DIV},\dv{{SortInt{{}}}}("1")))"#
            ),
        ),
        (
            "eq-notbool",
            format!(
                r"\equals{{SortBool{{}},SortGeneratedTopCell{{}}}}({positive},LblnotBool'Unds'{{}}({positive}))"
            ),
        ),
    ];
    let validator = NativeValidator::bind(
        support::load_path(
            &std::path::Path::new(support::DIR).join("partialreq.k"),
            "TV01UNSAT",
        ),
        CompileOptions::default(),
    );
    let side = validator.compile_baseline().expect("baseline");
    for (label, condition) in conditions {
        let initial = Pattern::And {
            sort: kore_sort("SortGeneratedTopCell"),
            arguments: vec![
                support::initial_state(
                    support::app("Lblpair", vec![int("X"), int("Y")]),
                    "SortProg",
                ),
                k_rust::kore::parser::parse_pattern(&condition).expect("condition"),
            ],
        };
        let mut backend = backend(&side, "TV01UNSAT");
        let admission = bridge::validate_test_initial_state(&mut backend, &initial);
        assert!(
            matches!(
                admission,
                Err(kink_native::execution::ExecutionAdapterFailure::InvalidState(_))
            ),
            "{label}: undefined instances must be protected before execution, got {admission:?}"
        );
        // Deliberately bypass admission: this is the T-UNSAT violation that justifies
        // refusing the input, adjudicated by the supervisor on 2026-10-07.
        let measured = audit_vi_t10_relation_rows(
            &side,
            "TV01UNSAT",
            &initial,
            &[equal("X", 1), equal("Y", 0)],
            &[equal("X", 1), equal("Y", 1)],
        );
        eprintln!("TB02-EQUALITY {label}: {measured:?}");
        assert_eq!(
            measured,
            [row(
                if cfg!(feature = "z3") {
                    HaltClass::Trivial
                } else {
                    HaltClass::Stuck
                },
                LeafFeasibility::Unknown,
                if cfg!(feature = "z3") {
                    Feasibility::Unsat
                } else {
                    Feasibility::Unknown
                },
                if cfg!(feature = "z3") {
                    Feasibility::Unsat
                } else {
                    Feasibility::Unknown
                },
            )],
            "{label}"
        );
    }
}

/// VI-T11: free set variables are refused explicitly before the backend's undecided step.
/// A set binder is local and is not a free test-state input.
#[test]
fn audit_vi_t11_free_set_variables_require_input_refusal() {
    let mut backend = Backend::new(
        r"[] module MAIN sort SortS{} [] symbol Lbla{}() : SortS{} [constructor{}()] endmodule []",
        "MAIN",
        BackendOptions::default(),
    )
    .expect("backend");
    for source in ["@Rule-hM:SortS{}", r"\and{SortS{}}(Lbla{}(),@M:SortS{})"] {
        let pattern = k_rust::kore::parser::parse_pattern(source).expect("set input");
        let admission = bridge::validate_test_initial_state(&mut backend, &pattern);
        assert!(
            matches!(
                admission,
                Err(kink_native::execution::ExecutionAdapterFailure::InvalidState(_))
            ),
            "{source}: must refuse a free set variable before execution, got {admission:?}"
        );
    }
    let local =
        k_rust::kore::parser::parse_pattern(r"\mu{}(@M:SortS{},@M:SortS{})").expect("local binder");
    assert!(bridge::validate_test_initial_state(&mut backend, &local).is_ok());
}

/// VI-T10: admitted monotone predicates, defined and undefined valuations, plus a genuinely
/// empty predicate. Report every depth-0 discard and require an actual-instance row to stay.
#[test]
fn audit_vi_t10_positive_predicates_do_not_discard_instances() {
    const PART: &str = r"Lblpart{}(X:SortInt{})";
    const TOP: &str = "SortGeneratedTopCell{}";
    let atom = format!(r#"\equals{{SortInt{{}},{TOP}}}({PART},\dv{{SortInt{{}}}}("7"))"#);
    let rows = [
        ("ceil", format!(r"\ceil{{SortInt{{}},{TOP}}}({PART})"), true),
        ("equals", atom.clone(), true),
        (
            "in",
            format!(r#"\in{{SortInt{{}},{TOP}}}({PART},\dv{{SortInt{{}}}}("7"))"#),
            true,
        ),
        (
            "and",
            format!(r"\and{{{TOP}}}({atom},\top{{{TOP}}}())"),
            true,
        ),
        ("or", format!(r"\or{{{TOP}}}({atom},\top{{{TOP}}}())"), true),
        (
            "exists",
            format!(r"\exists{{{TOP}}}(X:SortInt{{}},{atom})"),
            true,
        ),
        (
            "forall",
            format!(r"\forall{{{TOP}}}(X:SortInt{{}},{atom})"),
            false,
        ),
        (
            "empty",
            format!(
                r#"\equals{{SortInt{{}},{TOP}}}(\dv{{SortInt{{}}}}("1"),\dv{{SortInt{{}}}}("2"))"#
            ),
            false,
        ),
    ];
    let validator = NativeValidator::bind(
        support::load_path(
            &std::path::Path::new(support::DIR).join("partialreq.k"),
            "TV01UNSAT",
        ),
        CompileOptions::default(),
    );
    let side = validator.compile_baseline().expect("baseline");
    for (label, condition, inhabited) in rows {
        let initial = Pattern::And {
            sort: kore_sort("SortGeneratedTopCell"),
            arguments: vec![
                support::initial_state(
                    support::app("Lblpair", vec![int("X"), int("Y")]),
                    "SortProg",
                ),
                k_rust::kore::parser::parse_pattern(&condition).expect("predicate"),
            ],
        };
        let mut backend = backend(&side, "TV01UNSAT");
        bridge::validate_test_initial_state(&mut backend, &initial).expect("positive predicate");
        let execution = ExecutionAdapter::with_profile(SolverProfile::BUILD)
            .execute(&mut backend, &initial, BUDGET)
            .expect("execution");
        let rows = execution
            .leaves()
            .iter()
            .map(|leaf| {
                (
                    leaf.halt,
                    leaf.feasibility,
                    leaf.branch.depth,
                    bridge::discarded(leaf),
                )
            })
            .collect::<Vec<_>>();
        eprintln!("TB02-POSITIVE {label}: {rows:?}");
        assert_eq!(
            rows,
            [(
                if label == "empty" {
                    HaltClass::Vacuous
                } else {
                    HaltClass::Stuck
                },
                if label == "or" {
                    LeafFeasibility::Syntactic
                } else {
                    LeafFeasibility::Unknown
                },
                0,
                if label == "empty" {
                    Some(DiscardReason::Vacuous)
                } else {
                    None
                }
            )],
            "{label}"
        );
        if inhabited {
            assert!(
                rows.iter().all(
                    |(halt, feasibility, _, discard)| *halt != HaltClass::Vacuous
                        && *feasibility != LeafFeasibility::Unsat
                        && discard.is_none()
                ),
                "{label}: an X=0 instance was dropped"
            );
        }
    }
}

/// Executes directly so refusal regressions can retain the evidence behind the guard.
fn audit_vi_t10_relation_rows(
    side: &ValidatedDefinition,
    module: &str,
    initial: &Pattern,
    instance: &[TermRelation],
    outside: &[TermRelation],
) -> Vec<DefinednessRow> {
    let leaves = leaves(side, module, initial);
    assert!(leaves.iter().all(|leaf| leaf.branch.depth == 0));
    backend(side, module)
        .with_solver(None, |definition, solver| {
            let relations =
                BackendRelations::shared(definition, solver, TestInitialState::of_test(initial));
            Ok::<_, BackendError>(
                leaves
                    .iter()
                    .map(|leaf| {
                        let path = real_path(&predicates(state(leaf)));
                        DefinednessRow {
                            halt: leaf.halt,
                            feasibility: leaf.feasibility,
                            discarded: bridge::discarded(leaf),
                            at_instance: relations.feasible(&path, instance),
                            outside: relations.feasible(&path, outside),
                        }
                    })
                    .collect(),
            )
        })
        .expect("instance queries")
}

/// Review F5: Y=0 makes Y=1 outside every leaf, including the tautological or/exists rows.
#[test]
fn audit_vi_t10_positive_predicate_instance_queries_are_not_refuted() {
    const PART: &str = r"Lblpart{}(X:SortInt{})";
    const TOP: &str = "SortGeneratedTopCell{}";
    let atom = format!(r#"\equals{{SortInt{{}},{TOP}}}({PART},\dv{{SortInt{{}}}}("7"))"#);
    let validator = NativeValidator::bind(
        support::load_path(
            &std::path::Path::new(support::DIR).join("partialreq.k"),
            "TV01UNSAT",
        ),
        CompileOptions::default(),
    );
    let side = validator.compile_baseline().expect("baseline");
    for (label, source) in [
        ("ceil", format!(r"\ceil{{SortInt{{}},{TOP}}}({PART})")),
        ("equals", atom.clone()),
        (
            "in",
            format!(r#"\in{{SortInt{{}},{TOP}}}({PART},\dv{{SortInt{{}}}}("7"))"#),
        ),
        ("and", format!(r"\and{{{TOP}}}({atom},\top{{{TOP}}}())")),
        ("or", format!(r"\or{{{TOP}}}({atom},\top{{{TOP}}}())")),
        ("exists", format!(r"\exists{{{TOP}}}(X:SortInt{{}},{atom})")),
    ] {
        let initial = Pattern::And {
            sort: kore_sort("SortGeneratedTopCell"),
            arguments: vec![
                support::initial_state(
                    support::app("Lblpair", vec![int("X"), int("Y")]),
                    "SortProg",
                ),
                k_rust::kore::parser::parse_pattern(&source).expect("positive condition"),
                k_rust::kore::parser::parse_pattern(
                    r#"\equals{SortInt{},SortGeneratedTopCell{}}(Y:SortInt{},\dv{SortInt{}}("0"))"#,
                )
                .expect("Y=0"),
            ],
        };
        bridge::validate_test_initial_state(&mut backend(&side, "TV01UNSAT"), &initial)
            .expect("admitted");
        let rows = audit_vi_t10_relation_rows(
            &side,
            "TV01UNSAT",
            &initial,
            &[equal("X", 0), equal("Y", 0)],
            &[equal("X", 0), equal("Y", 1)],
        );
        eprintln!("TB02-POSITIVE-QUERY {label}: {rows:?}");
        let solved = cfg!(feature = "z3") && label == "or";
        assert_eq!(
            rows,
            [row(
                HaltClass::Stuck,
                if solved {
                    LeafFeasibility::Solver
                } else {
                    LeafFeasibility::Unknown
                },
                if solved {
                    Feasibility::Sat
                } else {
                    Feasibility::Unknown
                },
                if solved {
                    Feasibility::Unsat
                } else {
                    Feasibility::Unknown
                }
            )],
            "{label}"
        );
        assert!(
            rows.iter()
                .all(|row| row.at_instance != Feasibility::Unsat && row.discarded.is_none())
        );
    }
}

/// Review F6: measure the declared-total String2Bytes hook's Bottom residue; do not refuse it.
#[test]
fn audit_vi_t10_string2bytes_declared_totality_residue() {
    let validator = NativeValidator::bind(support::load("tb02input.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("baseline");
    let definition =
        k_rust::kore::parser::parse_definition(&side.artifacts().definition_kore).expect("KORE");
    let symbol = definition
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .find_map(|sentence| {
            if let k_rust::kore::ast::Sentence::SymbolDeclaration { symbol, .. } = sentence
                && symbol.name.contains("String2Bytes")
            {
                Some(symbol.clone())
            } else {
                None
            }
        })
        .expect("compiled String2Bytes symbol");
    eprintln!("TB02-STRING2BYTES symbol: {}", symbol.name);
    let initial = Pattern::And {
        sort: kore_sort("SortGeneratedTopCell"),
        arguments: vec![
            support::initial_state(support::app("Lbldone", vec![support::int(1)]), "SortProg"),
            Pattern::Ceil {
                operand_sort: Box::new(kore_sort("SortBytes")),
                result_sort: kore_sort("SortGeneratedTopCell"),
                argument: Box::new(Pattern::Application {
                    symbol,
                    arguments: vec![Pattern::DomainValue {
                        sort: kore_sort("SortString"),
                        value: "Ā".into(),
                    }],
                }),
            },
        ],
    };
    bridge::validate_test_initial_state(&mut backend(&side, "TB02INPUT"), &initial)
        .expect("not refused");
    let rows = leaves(&side, "TB02INPUT", &initial)
        .iter()
        .map(|leaf| {
            (
                leaf.halt,
                leaf.feasibility,
                leaf.branch.depth,
                bridge::discarded(leaf),
            )
        })
        .collect::<Vec<_>>();
    eprintln!("TB02-STRING2BYTES: {rows:?}");
    assert_eq!(
        rows,
        [(
            HaltClass::Vacuous,
            LeafFeasibility::Unknown,
            0,
            Some(DiscardReason::Vacuous)
        )]
    );
}

/// F1: a bare String pattern carries the same String value as its domain-value spelling.
#[test]
fn audit_vi_t11_invalid_utf8_string_guard_is_independent_of_polarity() {
    let validator = NativeValidator::bind(support::load("tb02string.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("baseline");
    let mut backend = backend(&side, "TB02STRING");
    for source in [r#"\dv{SortString{}}("\x80")"#, r#""\x80""#] {
        let value =
            k_rust::kore::parser::parse_pattern(source).expect("invalid UTF-8 parses as bytes");
        for input in [
            value.clone(),
            Pattern::Not {
                sort: kore_sort("SortString"),
                argument: Box::new(value),
            },
        ] {
            assert!(
                matches!(
                    bridge::validate_test_initial_state(&mut backend, &input),
                    Err(kink_native::execution::ExecutionAdapterFailure::InvalidState(_))
                ),
                "{source}: {input:?}"
            );
        }
    }
    for source in [
        r#"\dv{SortString{}}("A")"#,
        r#"\dv{SortString{}}("\u0080")"#,
        r#""\xc3\xa9""#,
    ] {
        let input = k_rust::kore::parser::parse_pattern(source).expect("valid UTF-8");
        assert!(bridge::validate_test_initial_state(&mut backend, &input).is_ok());
    }
}

/// TB02-R2-F1: every test-written Float token is refused at any polarity,
/// including the rule literal and k-rust's hook-produced canonical spelling.
#[test]
fn audit_vi_t11_review2_float_guard_is_independent_of_polarity() {
    let validator = NativeValidator::bind(support::load("tb02float.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("Float fixture");
    let mut backend = backend(&side, "TB02FLOAT");
    for spelling in [
        "1.0",
        "1.00",
        "1.0e0",
        "1.0d",
        "1.0p53x11",
        "10.0e-1",
        "1.0000000000000000e0",
        "1.0000000000000000e+00",
    ] {
        let value = Pattern::DomainValue {
            sort: kore_sort("SortFloat"),
            value: spelling.into(),
        };
        for input in [
            value.clone(),
            Pattern::Not {
                sort: kore_sort("SortFloat"),
                argument: Box::new(value),
            },
        ] {
            let admission = bridge::validate_test_initial_state(&mut backend, &input);
            assert!(
                matches!(
                    admission,
                    Err(kink_native::execution::ExecutionAdapterFailure::InvalidState(_))
                ),
                "{spelling}: {input:?}: {admission:?}"
            );
        }
    }
}
