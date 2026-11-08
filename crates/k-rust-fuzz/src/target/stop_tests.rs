//! The campaign's stop ([`crate::CaseStop`]) on real runs of STOP, a machine that never halts
//! (`tests/data/README.md`): every request carries the stop, a leaf at the stop is a natural end
//! of the truncated system and judged as one, a passed stop leaves the case unjudged, and
//! without a stop nothing changes.

use std::num::NonZeroU64;

use k_rust::backend::HaltReasonOutput;

use super::{
    Judgement, PatternAt, PatternTarget, ResolvedTarget, RuleMode, RuleRef, RuleTarget,
    differential,
};
use crate::{
    CaseStop, Target, TargetKind,
    assemble::ProgramAssembly,
    error::CampaignError,
    exec::{
        CaseRequestShape, CaseResult, Executor, OutcomeClass, UnjudgedReason,
        comparable::{ComparableCondition, end_conditions},
    },
    spec::{CaseOptions, PathMode},
    support::{Fixture, STOP, STOP_KILL, STOP_ONE},
};

/// A work bound far above every stopped run's work, which a run without a stop meets.
const MAX_WORK: u64 = 200;

/// The stop before `tick` and `late` (and the extra rules `also`, each by its whole label) at
/// its `count`th event.
fn stop_before(count: u64, also: &[&str]) -> CaseStop {
    CaseStop {
        before: ["STOP.tick", "STOP.late"]
            .iter()
            .chain(also)
            .map(|name| (*name).to_owned())
            .collect(),
        after: Vec::new(),
        count: NonZeroU64::new(count).expect("a positive count"),
    }
}

fn options(paths: PathMode, stop: Option<CaseStop>) -> CaseOptions {
    CaseOptions {
        paths,
        max_work: Some(MAX_WORK),
        stop,
        ..CaseOptions::default()
    }
}

fn final_pattern(pattern: &str) -> Target {
    pattern_at(pattern, PatternAt::Final)
}

fn pattern_at(pattern: &str, at: PatternAt) -> Target {
    Target {
        kind: TargetKind::Pattern(PatternTarget {
            pattern: pattern.to_owned(),
            at,
        }),
        run_to_completion: false,
        negated_property: false,
        data_end: true,
        comparable: false,
        query_confirmable: false,
    }
}

fn fired(label: &str, run_to_completion: bool) -> Target {
    Target {
        kind: TargetKind::Rule(RuleTarget {
            rule: RuleRef::Label(label.to_owned()),
            mode: RuleMode::Fired,
        }),
        run_to_completion,
        negated_property: false,
        data_end: true,
        comparable: false,
        query_confirmable: false,
    }
}

/// The program file `text` is a variant of.
fn file_of(text: &str) -> &'static str {
    if text.starts_with("fork") {
        "stop/fork.pgm"
    } else {
        "stop/tick.pgm"
    }
}

/// An executor of `fixture` under `options`, with the definition's assembly.
fn executor(fixture: &'static Fixture, options: &CaseOptions) -> (Executor, ProgramAssembly) {
    let definition = fixture.compiled().definition();
    let assembly = ProgramAssembly::new(&definition).expect("the definition assembles");
    let executor = Executor::new(&definition, &assembly, options).expect("the executor builds");
    (executor, assembly)
}

/// Run `text` on STOP against `target` under `options` and judge it, as a campaign's case is;
/// also the program's own run of every path, as comparability runs it.
fn judge(
    target: &Target,
    options: &CaseOptions,
    text: &str,
) -> (Judgement, CaseResult, CaseResult) {
    let compiled = STOP.compiled();
    let definition = compiled.definition();
    let (mut executor, assembly) = executor(&STOP, options);
    let resolved = ResolvedTarget::resolve(target, &mut executor, &definition, &assembly)
        .expect("the target resolves");
    let initial = compiled
        .assemble(file_of(text), text, &[])
        .expect("the program assembles");
    let shape = CaseRequestShape::new(options, &resolved.needs(options.paths));
    let judged = resolved
        .run_and_judge(&mut executor, &initial, &shape, None)
        .expect("no abort");
    let result = judged.result;
    let judgement = judged
        .judgement
        .unwrap_or_else(|defect| panic!("{defect:?}: {result:#?}"));
    let every_path = executor
        .run(&initial, &shape.every_path(), &[], None)
        .expect("no abort");
    (judgement, result, every_path)
}

const BOTH_MODES: [PathMode; 2] = [PathMode::OnePath, PathMode::AllPaths];

#[test]
fn a_run_that_never_ends_ends_at_the_stop_as_a_natural_end_and_is_judged() {
    for paths in BOTH_MODES {
        // Without a stop the machine runs to the work bound: no end, no judgement of `<n>`.
        let (unstopped, result, _) = judge(
            &final_pattern("<n> 1 </n>"),
            &options(paths, None),
            "tick(0)",
        );
        assert_eq!(
            unstopped.class,
            OutcomeClass::WorkBound,
            "{paths:?}: {result:#?}"
        );
        assert!(
            result
                .leaves
                .iter()
                .all(|leaf| leaf.halt == HaltReasonOutput::WorkBound && !leaf.stop_end),
            "{result:#?}"
        );
        // With the stop the run ends at its third step, `<k> tick(2) </k> <n> 1 </n>`, a clean
        // natural end of the truncated system whose configuration is data.
        let stopped = options(paths, Some(stop_before(3, &[])));
        let (hit, result, every_path) = judge(&final_pattern("<n> 1 </n>"), &stopped, "tick(0)");
        assert_eq!(hit.class, OutcomeClass::Hit, "{paths:?}: {result:#?}");
        let [leaf] = result.leaves.as_slice() else {
            panic!("one leaf: {result:#?}");
        };
        assert_eq!(leaf.halt, HaltReasonOutput::CutPoint);
        assert!(leaf.stop_end && leaf.is_end() && leaf.is_clean() && leaf.natural_end);
        assert_eq!(leaf.depth, 2);
        assert!(result.passed_stops.is_empty());
        // The program's own run of every path is the truncated system's, and comparable.
        assert_eq!(end_conditions(&every_path), [], "{every_path:#?}");
        // An end the stop does not reach is a miss, not a bound.
        let (miss, result, _) = judge(&final_pattern("<n> 7 </n>"), &stopped, "tick(0)");
        assert_eq!(miss.class, OutcomeClass::Miss, "{paths:?}: {result:#?}");
    }
}

#[test]
fn a_stop_after_a_rule_ends_at_its_successor_as_a_natural_end() {
    let after = CaseStop {
        before: Vec::new(),
        after: vec!["STOP.tick".to_owned(), "STOP.late".to_owned()],
        count: NonZeroU64::new(3).expect("a positive count"),
    };
    // After the third step: `<k> tick(3) </k> <n> 2 </n>`.
    let (hit, result, _) = judge(
        &final_pattern("<n> 2 </n>"),
        &options(PathMode::AllPaths, Some(after)),
        "tick(0)",
    );
    assert_eq!(hit.class, OutcomeClass::Hit, "{result:#?}");
    assert_eq!(result.leaves[0].halt, HaltReasonOutput::Terminal);
    assert!(result.leaves[0].stop_end && result.leaves[0].natural_end);
}

#[test]
fn a_rule_that_fires_only_past_the_stop_is_no_hit() {
    for paths in BOTH_MODES {
        for run_to_completion in [false, true] {
            let stopped = options(paths, Some(stop_before(3, &[])));
            // From `tick(0)` the stop comes before `late` can fire.
            let (miss, result, _) = judge(&fired("late", run_to_completion), &stopped, "tick(0)");
            assert_eq!(
                miss.class,
                OutcomeClass::Miss,
                "{paths:?} {run_to_completion}: {result:#?}"
            );
            // From `tick(4)` it fires at the second step, before the stop.
            let (hit, result, _) = judge(&fired("late", run_to_completion), &stopped, "tick(4)");
            assert_eq!(
                hit.class,
                OutcomeClass::Hit,
                "{paths:?} {run_to_completion}: {result:#?}"
            );
            // The target's own early stop is not used under the campaign's: the leaf is the
            // stop's, after the firing.
            assert!(
                result.leaves.iter().all(|leaf| leaf.stop_end),
                "{result:#?}"
            );
        }
    }
}

#[test]
fn a_passed_stop_leaves_the_case_unjudged() {
    for paths in BOTH_MODES {
        // `left` has the sibling successor `right` at `fork(0)`: no event, a passed stop. Both
        // paths then tick to the stop, and `<n> 0 </n>` holds at the end of the `left` one.
        let passed = options(paths, Some(stop_before(2, &["STOP.left"])));
        let (unjudged, result, every_path) =
            judge(&final_pattern("<n> 0 </n>"), &passed, "fork(0)");
        assert_eq!(result.passed_stops, ["STOP.left"], "{paths:?}: {result:#?}");
        assert_eq!(unjudged.class, OutcomeClass::Unsupported, "{result:#?}");
        assert_eq!(unjudged.reason, Some(UnjudgedReason::PassedStop));
        assert!(end_conditions(&every_path).contains(&ComparableCondition::PassedStop));
        for target in [fired("tick", false), fired("tick", true)] {
            let (unjudged, result, _) = judge(&target, &passed, "fork(0)");
            assert_eq!(unjudged.class, OutcomeClass::Unsupported, "{result:#?}");
            assert_eq!(unjudged.reason, Some(UnjudgedReason::PassedStop));
        }
        // Without `left` among the stop rules nothing is passed, and the `left` path is a hit.
        let (hit, result, _) = judge(
            &final_pattern("<n> 0 </n>"),
            &options(paths, Some(stop_before(2, &[]))),
            "fork(0)",
        );
        assert_eq!(hit.class, OutcomeClass::Hit, "{paths:?}: {result:#?}");
    }
}

/// Run `text` on the STOP baseline and `mutant` as a differential case is run, and judge it.
fn differential_case(
    mutant: &'static Fixture,
    options: &CaseOptions,
    text: &str,
) -> (differential::DifferentialJudgement, Option<UnjudgedReason>) {
    differential_pair(&STOP, mutant, options, text)
}

/// Run `text` on `baseline` and `mutant` as a differential case is run, and judge it.
fn differential_pair(
    baseline: &'static Fixture,
    mutant: &'static Fixture,
    options: &CaseOptions,
    text: &str,
) -> (differential::DifferentialJudgement, Option<UnjudgedReason>) {
    let plan = differential::plan(options);
    let side = |fixture: &'static Fixture, needs| {
        let (mut executor, _) = executor(fixture, options);
        let initial = fixture
            .compiled()
            .assemble(file_of(text), text, &[])
            .expect("the program assembles");
        executor
            .run(&initial, &CaseRequestShape::new(options, needs), &[], None)
            .expect("no abort")
    };
    let baseline = side(baseline, &plan.baseline);
    let mutated = side(mutant, &plan.mutant);
    differential::judge_pair_explained(&baseline, &mutated, options.paths, false)
        .expect("no engine defect")
}

#[test]
fn a_mutant_that_reaches_another_end_at_the_stop_is_killed() {
    for paths in BOTH_MODES {
        let stopped = options(paths, Some(stop_before(3, &[])));
        let (killed, _) = differential_case(&STOP_KILL, &stopped, "tick(0)");
        assert_eq!(killed.class, OutcomeClass::Hit, "{paths:?}");
        assert_eq!(killed.killing_leaf, Some(0));
        // The baseline against itself: equal ends at the stop.
        let (same, reason) = differential_case(&STOP, &stopped, "tick(0)");
        assert_eq!(
            (same.class, reason),
            (OutcomeClass::Miss, None),
            "{paths:?}"
        );
        // Without a stop neither side has an end: the baseline is incomplete.
        let (cut, reason) = differential_case(&STOP_KILL, &options(paths, None), "tick(0)");
        assert_eq!(
            (cut.class, reason),
            (
                OutcomeClass::BaselineIncomplete,
                Some(UnjudgedReason::WorkBound)
            ),
            "{paths:?}"
        );
        // A stop only the mutant passes leaves the pair unjudged: the mutant's ends at the stop
        // (`<n> 0 </n>` and `<n> 10 </n>`) differ from the baseline's one end there
        // (`<n> 0 </n>` after `tick(0)` alone), but they are no ends of the truncated system.
        let passed = options(paths, Some(stop_before(2, &["STOP.left"])));
        let (unjudged, reason) = differential_pair(&STOP_ONE, &STOP, &passed, "fork(0)");
        assert_eq!(
            (unjudged.class, reason),
            (OutcomeClass::Unsupported, Some(UnjudgedReason::PassedStop)),
            "{paths:?}"
        );
        assert_eq!((unjudged.killing_leaf, unjudged.removed_end), (None, None));
        // A passed stop leaves the baseline incomplete, whatever the mutant reaches.
        let passed = options(paths, Some(stop_before(2, &["STOP.left"])));
        let (unjudged, reason) = differential_case(&STOP_KILL, &passed, "fork(0)");
        assert_eq!(
            (unjudged.class, reason),
            (
                OutcomeClass::BaselineIncomplete,
                Some(UnjudgedReason::PassedStop)
            ),
            "{paths:?}"
        );
    }
}

#[test]
fn every_request_carries_the_stop_and_no_target_stop_beside_it() {
    let stopped = options(PathMode::OnePath, Some(stop_before(3, &[])));
    let needs = crate::exec::TargetNeeds {
        terminal_rules: vec!["late".to_owned()],
        ..crate::exec::TargetNeeds::default()
    };
    let state = STOP.compiled().initial("stop/tick.pgm");
    for shape in [
        CaseRequestShape::new(&stopped, &needs),
        CaseRequestShape::new(&stopped, &needs).every_path(),
    ] {
        let request = shape.request(state.clone());
        assert_eq!(request.cut_point_rules, ["STOP.tick", "STOP.late"]);
        assert!(request.terminal_rules.is_empty());
        assert_eq!(request.stop_count, NonZeroU64::new(3));
        assert!(!shape.has_terminal_rules());
    }
    // An `after` stop is the request's terminal rules, the program's run of every path too.
    let after = options(
        PathMode::OnePath,
        Some(CaseStop {
            before: Vec::new(),
            after: vec!["STOP.tick".to_owned()],
            count: NonZeroU64::MIN,
        }),
    );
    for shape in [
        CaseRequestShape::new(&after, &needs),
        CaseRequestShape::new(&after, &needs).every_path(),
    ] {
        let request = shape.request(state.clone());
        assert!(request.cut_point_rules.is_empty());
        assert_eq!(request.terminal_rules, ["STOP.tick"]);
        assert_eq!(request.stop_count, Some(NonZeroU64::MIN));
        assert!(!shape.has_terminal_rules() && shape.stopped());
    }
    // Without a stop the request is what it was: the target's terminal rule, no stop count,
    // and the program's run of every path without a stop rule.
    let unstopped = options(PathMode::OnePath, None);
    let shape = CaseRequestShape::new(&unstopped, &needs);
    let request = shape.request(state.clone());
    assert!(request.cut_point_rules.is_empty());
    assert_eq!(request.terminal_rules, ["late"]);
    assert_eq!(request.stop_count, None);
    assert!(shape.has_terminal_rules());
    let every_path = shape.every_path().request(state);
    assert!(every_path.cut_point_rules.is_empty() && every_path.terminal_rules.is_empty());
}

#[test]
fn a_stop_must_name_a_rewrite_rule_of_the_definition() {
    let (mut executor, _) = executor(&STOP, &CaseOptions::default());
    let catalog = executor
        .backend_mut()
        .rule_catalog(None)
        .expect("the catalog is available");
    assert!(stop_before(1, &[]).check(&catalog, "baseline").is_ok());
    let unknown = stop_before(1, &["nowhere"]);
    let Err(CampaignError::InvalidOptions { message }) = unknown.check(&catalog, "mutant") else {
        panic!("an unknown stop rule is refused");
    };
    assert!(
        message.contains("`nowhere`") && message.contains("mutant"),
        "{message}"
    );
    // A label without its module is not the whole label k-rust selects by.
    let Err(CampaignError::InvalidOptions { message }) =
        stop_before(1, &["left"]).check(&catalog, "baseline")
    else {
        panic!("an unqualified label is refused");
    };
    assert!(message.contains("`STOP.left`"), "{message}");
    let empty = CaseStop {
        before: Vec::new(),
        after: Vec::new(),
        count: NonZeroU64::MIN,
    };
    assert!(matches!(
        empty.check(&catalog, "baseline"),
        Err(CampaignError::InvalidOptions { .. })
    ));
}

#[test]
fn an_any_state_target_reads_the_truncated_system() {
    for paths in BOTH_MODES {
        let stopped = options(paths, Some(stop_before(3, &[])));
        // `<n> 1 </n>` is reached at the stop's state; `<n> 3 </n>` only past the stop.
        let (hit, result, _) = judge(
            &pattern_at("<n> 1 </n>", PatternAt::AnyState),
            &stopped,
            "tick(0)",
        );
        assert_eq!(hit.class, OutcomeClass::Hit, "{paths:?}: {result:#?}");
        let (miss, result, _) = judge(
            &pattern_at("<n> 3 </n>", PatternAt::AnyState),
            &stopped,
            "tick(0)",
        );
        assert_eq!(miss.class, OutcomeClass::Miss, "{paths:?}: {result:#?}");
        // Past a passed stop a reached state is no evidence about the truncated system.
        let passed = options(paths, Some(stop_before(2, &["STOP.left"])));
        let (unjudged, result, _) = judge(
            &pattern_at("<n> 0 </n>", PatternAt::AnyState),
            &passed,
            "fork(0)",
        );
        assert_eq!(
            (unjudged.class, unjudged.reason),
            (OutcomeClass::Unsupported, Some(UnjudgedReason::PassedStop)),
            "{paths:?}: {result:#?}"
        );
    }
}

/// A campaign on STOP's `tick(N)` (the hole `N` at `0`) against the final pattern `pattern`,
/// under `stop`, against `mutant` when given.
fn campaign(
    pattern: &str,
    stop: CaseStop,
    mutant: Option<&'static Fixture>,
) -> crate::CampaignSpec {
    campaign_on("tick", pattern, stop, mutant)
}

/// [`campaign`] on the program `stop/{program}.pgm`, `{program}(N)`.
fn campaign_on(
    program: &str,
    pattern: &str,
    stop: CaseStop,
    mutant: Option<&'static Fixture>,
) -> crate::CampaignSpec {
    use crate::{
        CallerIdentity, CampaignSpec, Definitions, ProgramInput, ProposerConfig,
        holes::{HoleDecl, HoleLocation, SpanAddress},
        values::{Constraints, GenerationBounds},
    };
    let file = format!("stop/{program}.pgm");
    let definition =
        |fixture: &'static Fixture| std::sync::Arc::new(fixture.compiled().definition());
    let target = match mutant {
        Some(_) => Target {
            kind: TargetKind::Differential(super::DifferentialTarget::default()),
            ..final_pattern(pattern)
        },
        None => final_pattern(pattern),
    };
    CampaignSpec {
        definitions: Definitions {
            baseline: definition(&STOP),
            mutant: mutant.map(definition),
        },
        program: ProgramInput::Source(STOP.compiled().program_source(&file)),
        holes: vec![HoleDecl {
            name: "N".into(),
            sort: "Int".into(),
            location: HoleLocation::Span(SpanAddress {
                program: file.clone(),
                line: None,
                column: None,
                find: format!("{program}(0)"),
                literal: "0".into(),
            }),
            constraints: Constraints::default(),
            allow_refused_sort: false,
        }],
        target,
        options: CaseOptions {
            stop: Some(stop),
            ..options(PathMode::OnePath, None)
        },
        proposers: ProposerConfig::default(),
        bounds: GenerationBounds::default(),
        rejection_cap: crate::spec::DEFAULT_REJECTION_CAP,
        seed: 1,
        identity: CallerIdentity::default(),
    }
}

fn report_json(spec: crate::CampaignSpec) -> serde_json::Value {
    let report = match crate::Campaign::new(spec) {
        Ok(mut campaign) => campaign.run(crate::Budget::Cases(1), None),
        Err(error) => panic!("the campaign is valid: {error}"),
    };
    serde_json::from_str(&report.to_canonical_json()).expect("a report is JSON")
}

#[test]
fn a_campaign_under_a_stop_records_it_and_reproduces_its_witness_only_where_krun_can() {
    // Count 1: the anchor `tick(0)` stops before its first step, at `<n> 0 </n>`; krun takes the
    // stop's rule as a cut-point rule.
    let report = report_json(campaign("<n> 0 </n>", stop_before(1, &[]), None));
    assert_eq!(
        report["identity"]["options"]["stop"],
        serde_json::json!({"before": ["STOP.tick", "STOP.late"], "count": 1}),
        "{report}"
    );
    assert_eq!(report["outcome"]["status"], "witness-found", "{report}");
    let witness = &report["outcome"]["witness"];
    let line = witness["krun-command"].as_str().expect("a krun line");
    assert!(
        line.contains(" --cut-point-rule STOP.tick --cut-point-rule STOP.late ")
            && !line.contains("--terminal-rule"),
        "{line}"
    );
    // Count 3: krun takes no stop count, so no line reproduces the case.
    let report = report_json(campaign("<n> 1 </n>", stop_before(3, &[]), None));
    assert_eq!(
        report["identity"]["options"]["stop"]["count"], 3,
        "{report}"
    );
    assert_eq!(report["outcome"]["status"], "witness-found", "{report}");
    let witness = &report["outcome"]["witness"];
    assert!(witness["krun-command"].is_null(), "{witness}");
}

#[test]
fn a_campaign_refuses_a_stop_rule_its_mutant_lacks() {
    // STOP_ONE has no `right`: the baseline resolves the stop, the mutant does not.
    let spec = campaign(
        "<n> 0 </n>",
        stop_before(1, &["STOP.right"]),
        Some(&STOP_ONE),
    );
    match crate::Campaign::new(spec) {
        Err(CampaignError::InvalidOptions { message }) => {
            assert!(
                message.contains("`STOP.right`") && message.contains("of the mutant"),
                "{message}"
            );
        }
        Err(error) => panic!("refused for another reason: {error}"),
        Ok(_) => panic!("a stop rule the mutant lacks is refused"),
    }
}

#[test]
fn a_case_that_passed_a_stop_adds_nothing_to_the_coverage_totals() {
    // `fork(0)` passes the stop on `left`: its run fires `left`, `right` and `tick`, outside the
    // truncated system's run, so the totals name no rule.
    let report = report_json(campaign_on(
        "fork",
        "<n> 0 </n>",
        stop_before(2, &["STOP.left"]),
        None,
    ));
    let totals = &report["totals"];
    assert_eq!(totals["unsupported-reasons"]["passed-stop"], 1, "{totals}");
    assert_eq!(
        totals["coverage"]["applied"],
        serde_json::json!([]),
        "{totals}"
    );
    assert_eq!(
        totals["coverage"]["matched"],
        serde_json::json!([]),
        "{totals}"
    );
    // Without `left` among the stop rules the same case covers what it ran.
    let report = report_json(campaign_on("fork", "<n> 7 </n>", stop_before(2, &[]), None));
    let applied = report["totals"]["coverage"]["applied"]
        .as_array()
        .expect("a list");
    assert!(!applied.is_empty(), "{report}");
}
