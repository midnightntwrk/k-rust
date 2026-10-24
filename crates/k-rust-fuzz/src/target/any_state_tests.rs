//! Pattern targets `at: any-state` on real runs (ARCHITECTURE 4.1; FZ-ANYSTATE): FZ-FIX's
//! fixtures (`tests/support`) compiled in-process, each case run once through observed execution
//! by [`ResolvedTarget::run_and_judge`] and classed by [`crate::exec::classify`].
//!
//! - IMP `commute.imp` looks `x` (3) up for `x + y`, so `<k>` holds `3` at its head mid-run;
//!   `div.imp` with `y = 0` looks `x` (10) up, then stops abnormally at `10 / 0`.
//! - COIN `count(3)` steps through `count(2)`, `count(1)` and `count(0)` and ends at depth 5;
//!   `flip(3)` takes `heads` (`<out>` 3) or `tails` (`<out>` 4), two paths under all-paths.
//! - ANYSTATE `hold(N)` passes through `keep(f(N)) ~> drop`, where the partial `f` has an
//!   equation for `f(0)` only.
//! - [`ANY_STATE_HITS`]: the named hits a cross-test with kink reuses.
//!
//! The tests use only what the base already had (`resolve`, `run_and_judge`,
//! `Executor::run_observed`), so they ran at the base, and failed there on the refusal of
//! `at: any-state`.

use k_rust::{
    backend::{ExecutionLeaf, ObservationEventOutput, SearchPatternRequest, SearchTypeArg},
    kore::{ast::Pattern as KorePattern, codec, walk},
};

use crate::support::{ANY_STATE_HITS, ANYSTATE, AnyStateHit, COIN, Compiled, IMP};

use super::super::{HitSite, Judgement, PatternAt, PatternTarget, ResolvedTarget};
use crate::{
    Target, TargetKind,
    assemble::ProgramAssembly,
    exec::{CaseRequestShape, CaseResult, Executor, OutcomeClass, TargetNeeds, UnjudgedReason},
    spec::{CaseOptions, CompiledDefinition, PathMode},
};

fn any_state(pattern: &str, run_to_completion: bool) -> Target {
    Target {
        kind: TargetKind::Pattern(PatternTarget {
            pattern: pattern.to_owned(),
            at: PatternAt::AnyState,
        }),
        run_to_completion,
        negated_property: false,
        data_end: true,
    }
}

/// One fixture's definition, assembly and executor, as a campaign builds them.
struct Harness {
    compiled: &'static Compiled,
    definition: CompiledDefinition,
    assembly: ProgramAssembly,
    executor: Executor,
    options: CaseOptions,
}

/// A judged case: its result, judgement and hit step.
struct Judged {
    result: CaseResult,
    judgement: Judgement,
    hit_step: Option<u64>,
}

impl Harness {
    fn new(compiled: &'static Compiled, options: CaseOptions) -> Self {
        let definition = compiled.definition();
        let assembly = ProgramAssembly::new(&definition).expect("the definition assembles");
        let executor =
            Executor::new(&definition, &assembly, &options).expect("the executor builds");
        Self {
            compiled,
            definition,
            assembly,
            executor,
            options,
        }
    }

    fn resolve(&mut self, target: &Target) -> ResolvedTarget {
        ResolvedTarget::resolve(target, &mut self.executor, &self.definition, &self.assembly)
            .unwrap_or_else(|error| panic!("the target resolves: {error:?}"))
    }

    /// The initial configuration of the program `file`, with `edit`'s `(find, replace)` applied
    /// once when given.
    fn initial(&self, file: &str, edit: Option<(&str, &str)>) -> KorePattern {
        let program = self.compiled.fixture.program(file);
        let text = match edit {
            Some((find, replace)) => {
                assert_eq!(program.text.matches(find).count(), 1, "{find} in {file}");
                program.text.replacen(find, replace, 1)
            }
            None => program.text.to_owned(),
        };
        self.compiled
            .assemble(program.file, &text, program.bindings)
            .unwrap_or_else(|error| panic!("{text} does not assemble: {error}"))
    }

    /// Judge the case that starts from `initial`.
    fn judge_from(&mut self, target: &Target, initial: &KorePattern) -> Judged {
        let resolved = self.resolve(target);
        let shape = CaseRequestShape::new(&self.options, &resolved.needs(self.options.paths));
        let judged = resolved
            .run_and_judge(&mut self.executor, initial, &shape, None)
            .expect("no abort");
        let result = judged.result;
        let judgement = judged
            .judgement
            .unwrap_or_else(|defect| panic!("{defect:?}: {result:#?}"));
        Judged {
            result,
            judgement,
            hit_step: judged.hit_step,
        }
    }

    /// Judge the program `file` with `find` replaced by `replace`.
    fn judge(&mut self, target: &Target, file: &str, find: &str, replace: &str) -> Judged {
        let initial = self.initial(file, Some((find, replace)));
        self.judge_from(target, &initial)
    }

    /// The observed leaves of the case that starts from `initial`, with every event.
    fn observed(&mut self, initial: &KorePattern) -> Vec<ExecutionLeaf> {
        let shape = CaseRequestShape::new(&self.options, &TargetNeeds::default());
        let (_, leaves) = self
            .executor
            .run_observed(initial, &shape, &[], None, None)
            .expect("no abort");
        leaves
    }
}

fn one_path() -> CaseOptions {
    CaseOptions::default()
}

fn all_paths() -> CaseOptions {
    CaseOptions {
        paths: PathMode::AllPaths,
        ..CaseOptions::default()
    }
}

/// The configurations of a one-path run's only leaf, by step: the `before` of each committed
/// transition, then the leaf's state.
fn configurations(leaves: &[ExecutionLeaf]) -> Vec<KorePattern> {
    let [leaf] = leaves else {
        panic!("one leaf: {leaves:#?}");
    };
    let mut configurations: Vec<KorePattern> = leaf
        .observations
        .iter()
        .filter_map(|event| match event {
            ObservationEventOutput::Transition { before, .. } => {
                Some(codec::from_value(before).expect("a configuration decodes"))
            }
            ObservationEventOutput::Evaluation { .. }
            | ObservationEventOutput::Uncommitted { .. } => None,
        })
        .collect();
    assert_eq!(
        configurations.len(),
        leaf.branch.len(),
        "every step has its event"
    );
    configurations.push(codec::from_value(&leaf.state).expect("the state decodes"));
    configurations
}

/// The first application of the KORE symbol `name` in `pattern`, in pre-order.
fn application<'a>(pattern: &'a KorePattern, name: &str) -> Option<&'a [KorePattern]> {
    let mut work = vec![pattern];
    while let Some(next) = work.pop() {
        if let KorePattern::Application { symbol, arguments } = next
            && symbol.name == name
        {
            return Some(arguments);
        }
        work.extend(walk::children(next).into_iter().rev());
    }
    None
}

/// Whether the item at the head of the `<k>` cell of `configuration`, below its injection, is
/// the domain value `value`.
fn k_head_is(configuration: &KorePattern, value: &str) -> bool {
    let Some([sequence]) = application(configuration, "Lbl'-LT-'k'-GT-'") else {
        return false;
    };
    let Some([head, _]) = application(sequence, "kseq") else {
        return false;
    };
    let mut head = head;
    while let KorePattern::Application { symbol, arguments } = head
        && symbol.name == "inj"
        && let [inner] = arguments.as_slice()
    {
        head = inner;
    }
    matches!(head, KorePattern::DomainValue { value: found, .. } if found == value)
}

/// Whether the `<out>` cell of `configuration` holds the domain value `value`.
fn out_holds(configuration: &KorePattern, value: &str) -> bool {
    let Some(contents) = application(configuration, "Lbl'-LT-'out'-GT-'") else {
        return false;
    };
    let mut work: Vec<&KorePattern> = contents.iter().collect();
    while let Some(next) = work.pop() {
        if matches!(next, KorePattern::DomainValue { value: found, .. } if found == value) {
            return true;
        }
        work.extend(walk::children(next));
    }
    false
}

#[test]
fn an_imp_configuration_holding_3_mid_run_is_a_hit_at_its_step() {
    let mut imp = Harness::new(IMP.compiled(), one_path());
    let target = any_state("<k> 3 ~> _ </k>", false);
    let judged = imp.judge(&target, "imp/commute.imp", "x = 3;", "x = 3;");
    assert_eq!(
        judged.judgement.class,
        OutcomeClass::Hit,
        "{:#?}",
        judged.result
    );
    assert_eq!(judged.judgement.hit_site, Some(HitSite::Leaf(0)));
    let step = judged.hit_step.expect("an any-state hit names its step");
    // Read the step off the run itself: the first configuration whose `<k>` head is 3.
    let initial = imp.initial("imp/commute.imp", None);
    let configurations = configurations(&imp.observed(&initial));
    let first = configurations
        .iter()
        .position(|configuration| k_head_is(configuration, "3"))
        .expect("some configuration holds 3 at the head of <k>");
    assert_eq!(step, u64::try_from(first).expect("a small step"));
    assert!(step > 0 && step < judged.result.leaves[0].depth, "{step}");
    // The leaf runs on to its natural end, so the hit holds under run-to-completion too.
    let completed = imp.judge(
        &any_state("<k> 3 ~> _ </k>", true),
        "imp/commute.imp",
        "x = 3;",
        "x = 3;",
    );
    assert_eq!(
        completed.judgement.class,
        OutcomeClass::Hit,
        "{:#?}",
        completed.result
    );
    assert_eq!(completed.hit_step, Some(step));
    // With `x = 7` no configuration holds 3 at the head of `<k>`, and none holds 7 on the
    // anchor's run: misses.
    let other = imp.judge(&target, "imp/commute.imp", "x = 3;", "x = 7;");
    assert_eq!(
        other.judgement.class,
        OutcomeClass::Miss,
        "{:#?}",
        other.result
    );
    assert_eq!(other.hit_step, None);
    let none = imp.judge(
        &any_state("<k> 7 ~> _ </k>", false),
        "imp/commute.imp",
        "x = 3;",
        "x = 3;",
    );
    assert_eq!(
        none.judgement.class,
        OutcomeClass::Miss,
        "{:#?}",
        none.result
    );
}

#[test]
fn the_initial_configuration_matches_at_step_0() {
    for options in [one_path(), all_paths()] {
        let mut coin = Harness::new(COIN.compiled(), options);
        let judged = coin.judge(
            &any_state("<k> count(3) ~> _ </k>", false),
            "coin/count.pgm",
            "count(3)",
            "count(3)",
        );
        assert_eq!(
            judged.judgement.class,
            OutcomeClass::Hit,
            "{:#?}",
            judged.result
        );
        assert_eq!(judged.hit_step, Some(0));
    }
}

#[test]
fn a_configuration_holding_an_undefined_application_does_not_reach() {
    let target = any_state("<k> keep(_) ~> _ </k>", false);
    for options in [one_path(), all_paths()] {
        let mut anystate = Harness::new(ANYSTATE.compiled(), options);
        // `keep(f(3)) ~> drop` matches the pattern's configuration, but `f(3)` has no equation
        // and may denote nothing: never a hit, and never a miss. (k-rust keeps the step's
        // definedness obligation `#Ceil(f(3))` on that configuration, so it is not decided.)
        let judged = anystate.judge(&target, "anystate/hold.pgm", "hold(3)", "hold(3)");
        assert_eq!(
            judged.judgement.class,
            OutcomeClass::Unsupported,
            "{:#?}",
            judged.result
        );
        assert_eq!(judged.hit_step, None);
        // `f(0)` evaluates: `keep(1) ~> drop` reaches at step 1.
        let judged = anystate.judge(&target, "anystate/hold.pgm", "hold(3)", "hold(0)");
        assert_eq!(
            judged.judgement.class,
            OutcomeClass::Hit,
            "{:#?}",
            judged.result
        );
        assert_eq!(judged.hit_step, Some(1));
    }
}

#[test]
fn a_hit_under_all_paths_rests_on_the_reaching_leaf() {
    let mut coin = Harness::new(COIN.compiled(), all_paths());
    let judged = coin.judge(
        &any_state("<out> 4 </out>", true),
        "coin/flip.pgm",
        "flip(3)",
        "flip(3)",
    );
    assert_eq!(judged.result.leaves.len(), 2, "{:#?}", judged.result);
    assert_eq!(
        judged.judgement.class,
        OutcomeClass::Hit,
        "{:#?}",
        judged.result
    );
    let Some(HitSite::Leaf(leaf)) = judged.judgement.hit_site else {
        panic!("a leaf hit: {:?}", judged.judgement);
    };
    assert!(
        out_holds(&judged.result.leaves[leaf].state, "4"),
        "the hit rests on the `tails` leaf: {:#?}",
        judged.result
    );
    assert_eq!(judged.hit_step, Some(1));
    let none = coin.judge(
        &any_state("<out> 5 </out>", false),
        "coin/flip.pgm",
        "flip(3)",
        "flip(3)",
    );
    assert_eq!(
        none.judgement.class,
        OutcomeClass::Miss,
        "{:#?}",
        none.result
    );
}

#[test]
fn a_reaching_path_cut_by_a_bound_is_no_hit() {
    // `count(2)` is reached at step 1; the run is cut at depth 2, or by the work budget, before
    // its end.
    let reaching = |run_to_completion| any_state("<k> count(2) ~> _ </k>", run_to_completion);
    for options in [
        CaseOptions {
            max_depth: Some(2),
            ..CaseOptions::default()
        },
        CaseOptions {
            max_work: Some(3),
            ..CaseOptions::default()
        },
    ] {
        let mut coin = Harness::new(COIN.compiled(), options);
        let judged = coin.judge(&reaching(false), "coin/count.pgm", "count(3)", "count(3)");
        assert_eq!(
            judged.judgement.class,
            OutcomeClass::Unsupported,
            "{:#?}",
            judged.result
        );
        assert_eq!(
            judged.judgement.reason,
            Some(UnjudgedReason::ReachedCutPath),
            "{:#?}",
            judged.result
        );
        let judged = coin.judge(&reaching(true), "coin/count.pgm", "count(3)", "count(3)");
        assert_eq!(
            judged.judgement.class,
            OutcomeClass::ReachedUnfinished,
            "{:#?}",
            judged.result
        );
        // Nothing before the cut matches: the case takes its bound's class.
        let judged = coin.judge(
            &any_state("<k> count(0) ~> _ </k>", false),
            "coin/count.pgm",
            "count(3)",
            "count(3)",
        );
        assert!(
            matches!(
                judged.judgement.class,
                OutcomeClass::DepthBound | OutcomeClass::WorkBound
            ),
            "{:?}: {:#?}",
            judged.judgement,
            judged.result
        );
    }
}

#[test]
fn under_run_to_completion_the_reaching_leaf_must_end_naturally() {
    // `y = 0` leaves `10 / 0` on `<k>`: a clean abnormal stop after `x` (10) was looked up.
    let mut imp = Harness::new(IMP.compiled(), one_path());
    let ten = |run_to_completion| any_state("<k> 10 ~> _ </k>", run_to_completion);
    let judged = imp.judge(&ten(false), "imp/div.imp", "y = 2;", "y = 0;");
    assert_eq!(
        judged.judgement.class,
        OutcomeClass::Hit,
        "{:#?}",
        judged.result
    );
    let judged = imp.judge(&ten(true), "imp/div.imp", "y = 2;", "y = 0;");
    assert_eq!(
        judged.judgement.class,
        OutcomeClass::ReachedUnfinished,
        "{:#?}",
        judged.result
    );
    assert_eq!(judged.hit_step, None);
}

/// [`ANY_STATE_HITS`] as the fuzz judges them: a hit at the entry's step on its run's one clean
/// leaf, on one path and on all paths; and, for a unique entry, a miss from the configuration
/// after that step, so that no later configuration matches. Also the k-rust search that kink's
/// query sends (`search_pattern`, every state, the first match only) on the same compiled
/// pattern: its first match is at the same depth, with no constraint and no diagnostic. That
/// is the search, not kink's hit rule, which FZ-KINK-XTEST applies to these entries.
#[test]
fn every_named_any_state_hit_reaches_at_its_step() {
    for entry in &ANY_STATE_HITS {
        let AnyStateHit {
            fixture,
            program,
            pattern,
            step,
            unique,
        } = entry;
        let target = any_state(pattern, false);
        for options in [one_path(), all_paths()] {
            let mut harness = Harness::new(fixture.compiled(), options);
            let initial = harness.initial(program, None);
            let judged = harness.judge_from(&target, &initial);
            assert_eq!(
                judged.result.leaves.len(),
                1,
                "{entry:?}: {:#?}",
                judged.result
            );
            assert!(
                judged.result.leaves[0].is_clean(),
                "{entry:?}: {:#?}",
                judged.result
            );
            assert_eq!(
                judged.judgement.class,
                OutcomeClass::Hit,
                "{entry:?}: {:#?}",
                judged.result
            );
            assert_eq!(judged.hit_step, Some(*step), "{entry:?}");
            let compiled = harness.resolve(&target).compiled_patterns();
            let found = harness
                .executor
                .backend_mut()
                .search_pattern(SearchPatternRequest {
                    search_type: SearchTypeArg::All,
                    max_results: Some(1),
                    ..SearchPatternRequest::new(initial.clone(), compiled[0].kore().clone())
                })
                .expect("the search answers");
            let [first] = found.matches.as_slice() else {
                panic!("{entry:?}: one match: {found:#?}");
            };
            assert_eq!(first.state.depth, *step, "{entry:?}");
            assert!(
                first.constraints.is_empty()
                    && first.diagnostics.is_empty()
                    && first.state.diagnostics.is_empty(),
                "{entry:?}: {first:#?}"
            );
            if *unique {
                let configurations = configurations(&harness.observed(&initial));
                let next = usize::try_from(*step).expect("a small step") + 1;
                let after = configurations
                    .get(next)
                    .unwrap_or_else(|| panic!("{entry:?}: the run continues after the hit"));
                let rest = harness.judge_from(&target, after);
                assert_eq!(
                    rest.judgement.class,
                    OutcomeClass::Miss,
                    "{entry:?}: {:#?}",
                    rest.result
                );
            }
        }
    }
}
