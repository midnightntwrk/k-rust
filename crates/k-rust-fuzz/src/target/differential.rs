//! The differential target: does the mutant reach a final configuration that the baseline cannot
//! reach on the same input, or lose one the baseline reaches (ARCHITECTURE 4.3, amended by
//! FZ-DIFFEND)? Owner: FZ-08; ends and state sets: FZ-DIFFEND.
//!
//! A case runs the baseline on all paths and the mutant on the campaign's path mode, both as
//! state sets, each on its own backend, with hole values generated from the baseline's signature
//! and internalized per side. [`judge_pair`] then decides the case from the two [`CaseResult`]s
//! alone. In the one-path mode a case whose one mutant path could kill only by a removed end is
//! decided by a second, all-paths run of the mutant ([`needs_all_paths`]).
//!
//! # What an end is
//!
//! A run's outcome on a path is either a final configuration or undefinedness. A side's *set of
//! ends* on an input is the set of final configurations its paths from the initial configuration
//! reach. A clean, decided `stuck` leaf is one: a reached configuration to which no rule applies
//! (`docs/compatibility.md`, "Work budget" in "Execution results"), whether the program finished
//! there (a natural end) or stopped mid-way (an abnormal stop). The natural-end label decides
//! `miss` against `stuck` for one run's class, not membership in the set. An undefined step
//! (`trivial`) is no end: its configuration is reached and exists, and the path to it is real,
//! but it is not stuck, since a rule applies to it and shuts out the lower priorities, and it has
//! no successor ("Undefined steps in proofs"); the run's outcome there is undefinedness, which is
//! no configuration (`krun` prints `\bottom`, "Trivial rule results"). A clean undefined step is
//! a decided fact (this path's outcome is undefined) and keeps a side complete, but contributes
//! no configuration to its set: a mutant whose every path takes an undefined step has the empty
//! set of ends. Leaving undefinedness out of the compared sets only gives kills up (a mutant that
//! removes an undefined path and keeps every end is not killed); it never invents one, since an
//! end outside the other side's set of configurations is outside its set of outcomes too.
//!
//! # Why the hit rule is sound
//!
//! An *added end* claims that the mutant reaches, on this input, a final configuration that the
//! baseline does not reach on any path. The baseline's set of ends is known only when its
//! all-paths run is complete: every leaf is a clean `stuck` leaf or a clean undefined step. A
//! bound, a stop, an undecided or unsupported leaf leaves paths unexplored, and an end outside a
//! partial set proves nothing; such a case is `baseline-incomplete`, never a miss. The mutant's
//! end must be a clean, decided `stuck` leaf whose internalized term is built from free
//! constructors, injections, domain values and well-formed collections only, so that it denotes
//! itself and syntactic inequality is inequality of values (condition 4); the baseline's ends
//! must pass the same test, or one of them may denote the mutant's end (D15). An
//! implementation-chosen value on either side would make the comparison depend on a choice
//! k-rust made, not on the definitions; a contradicted claim (a `total` or
//! `preserves-definedness` attribute the run refuted) makes that side's theory inconsistent on
//! this input, so neither its ends nor its undefined steps are facts of the definition. Either
//! mark anywhere on a side's result (a leaf, or the result's lists, which hold the marks of
//! arrivals a state-set merge absorbed) makes it no evidence: an incomplete baseline, or an
//! `unsupported` case for the mutant.
//!
//! A *removed end* is the same claim with the roles exchanged, so it needs the same facts the
//! other way round: the mutant's all-paths run is complete (its set may be empty), every mutant
//! end is data, and a baseline end that is data is not in the mutant's set. One mutant path
//! does not establish the mutant's set, so the one-path mode re-runs the mutant on all paths
//! where only a removed end could kill.
//!
//! # State sets
//!
//! Both sides run with `result_modality: state-set`. k-rust's contract
//! (`docs/compatibility.md`, "Search results") is that a state-set execution reports the same
//! configurations as the path-set one without exploring the paths that converge on them, where
//! the path-set run stays within `maxBreadth` (the fuzz sets none); the leaf it reports for
//! merged paths carries the diagnostics of every path merged into it, and the marks of arrivals
//! merged during exploration are on the result's `implementationChosenValues` and
//! `contradictedClaims` lists, which [`CaseResult::run_facts_off_leaves`] reads. A `work-bound`
//! or `cancelled` leaf is never merged; a bound or undecided leaf is absorbed only by an earlier
//! `stuck` leaf of its configuration (which loses no configuration, the stuck halt being decided
//! by the configuration) or merges with another bound or undecided leaf of it (both stay
//! incomplete), so incompleteness stays visible. The leaf that
//! stands for merged paths carries the trace and depth of the first path, so a witness's reaching
//! leaf may differ from a path-set run's.
//!
//! # Comparison
//!
//! Each side's ends are held as a set of KORE patterns ordered by [`KorePattern`]'s `Ord`, whose
//! equality is structural, so two patterns are equal exactly when their printed KORE is equal.
//! Leaves are compared after k-rust's normalization, under which map and set entries are already
//! ordered.
//!
//! The whole configuration is compared, the `<generatedCounter>` cell included: an end that
//! differs from every end of the other side only in that cell is a kill. The compiled
//! definition's `<generatedCounter>` cell and its `freshGenerator` rules are part of each
//! definition's rewrite theory and fix the fresh constants a run mints, so the counter is a
//! component of the final configuration like any other cell. kink's whole-term oracle compares
//! the same complete terms, so the two agree on this point.

use std::collections::BTreeSet;

use k_rust::{backend::HaltReasonOutput, kore::ast::Pattern as KorePattern};

use crate::{
    error::CampaignError,
    exec::{
        self, CaseResult, LeafReport, OutcomeClass, TargetNeeds, UncleanReason, UnjudgedReason,
        reasons,
    },
    report::{EngineDefect, KillKind},
    spec::{BackendRoute, CaseOptions, CompiledDefinition, PathMode},
};

/// The request needs of the two sides of a differential case (ARCHITECTURE 4.3, 5.1).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DifferentialPlan {
    /// The baseline runs all paths, so that its set of ends can be complete, and reports
    /// [`crate::exec::LeafReport::constructor_only`]: its ends must be data to be compared.
    pub(crate) baseline: TargetNeeds,
    /// The mutant runs on the campaign's path mode and reports
    /// [`crate::exec::LeafReport::constructor_only`].
    pub(crate) mutant: TargetNeeds,
    /// In the one-path mode, the mutant on all paths, for the cases [`needs_all_paths`] selects;
    /// `None` in the all-paths mode, whose mutant run already explores every path.
    pub(crate) mutant_all_paths: Option<TargetNeeds>,
}

/// The judgement of one baseline/mutant pair.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DifferentialJudgement {
    /// The case's class: `rejected` when the baseline refuses the initial state,
    /// `baseline-incomplete` when the baseline's ends are incomplete; otherwise `hit` for an
    /// added or a removed end, else the mutant's class or `unsupported`.
    pub(crate) class: OutcomeClass,
    /// For a hit by an added end, the index of the mutant leaf whose configuration (the added
    /// end) the baseline cannot reach.
    pub(crate) killing_leaf: Option<usize>,
    /// For a hit by a removed end (judged against an all-paths mutant result: the all-paths
    /// mode's, or the one-path mode's re-run), the index of the baseline leaf whose
    /// configuration (the removed end) the mutant cannot reach. A hit has at least one of the
    /// two indices, and may have both.
    pub(crate) removed_end: Option<usize>,
}

impl DifferentialJudgement {
    /// The witness of a hit: its kind and the index of its end, a mutant leaf for
    /// [`KillKind::AddedEnd`] and a baseline leaf for [`KillKind::RemovedEnd`]. When a hit has
    /// both, the added end is the witness, as in the one-path mode. `None` for any other class.
    pub(crate) fn witness(&self) -> Option<(KillKind, usize)> {
        if self.class != OutcomeClass::Hit {
            return None;
        }
        self.killing_leaf
            .map(|index| (KillKind::AddedEnd, index))
            .or_else(|| self.removed_end.map(|index| (KillKind::RemovedEnd, index)))
    }

    const fn class(class: OutcomeClass) -> Self {
        Self {
            class,
            killing_leaf: None,
            removed_end: None,
        }
    }
}

/// The needs of each side for `options`: the baseline on all paths, whatever the campaign's
/// path mode; the mutant on the campaign's path mode (and, in the one-path mode, on all paths for
/// the re-run), with the constructor-only judgement of condition 4. The baseline's leaves carry
/// that judgement too: an end outside the baseline's set is a kill only when every baseline end
/// is data, and a baseline end can be the witness of a removed end. Both sides run as state
/// sets, whose set of final configurations is the path set's (the module documentation, "State
/// sets"). Neither side needs traces or terminal rules: the differential target names no rule.
pub(crate) fn plan(options: &CaseOptions) -> DifferentialPlan {
    let side = |paths| TargetNeeds {
        paths: Some(paths),
        constructor_only: true,
        state_set: true,
        ..TargetNeeds::default()
    };
    DifferentialPlan {
        baseline: side(PathMode::AllPaths),
        mutant: side(options.paths),
        mutant_all_paths: (options.paths == PathMode::OnePath).then(|| side(PathMode::AllPaths)),
    }
}

/// Whether the campaign ends before any case with the result `equivalent`
/// (ARCHITECTURE 4.3 as amended by D22, T-16): the two definitions run every case alike, so no
/// case can kill the mutant.
///
/// A case's result is a function of its initial configuration, assembled from the program text
/// by each side's frontend, and of the definition that executes it. Both parts must be equal.
///
/// Execution. Equal digests promise equal results for an equal module, options and initial
/// state through the routes that take no rewrite order (`docs/compatibility.md`, "Execution
/// digest"). On [`BackendRoute::SourceExecution`] the rewrite order reorders the rules of each
/// priority, which selects the one path `strategy: any` follows and, under `max_work`, what a
/// bounded run reaches, so the orders must be equal as well. The two sides must also use one
/// route and one main module (the module the backend executes).
///
/// Assembly. The execution digest covers only `definition.kore`, and the map from program text
/// to initial configuration is not in it: macro rules are emitted into `macros.kore`, so a
/// mutant that edits only a macro has an equal digest and assembles `inc(3)` into another
/// state (phase-1 review B1). The map is equal when everything it reads is:
/// - the syntax module (the grammar the program and the hole values are parsed with) and the
///   configuration variables with their sorts (which variables are bound, and the sort each
///   value is parsed at and injected from);
/// - `macros.kore` and `syntaxDefinition.kore`, the compiled macro rules and the program
///   productions with their formats and priorities, compared without their `Source` and
///   `Location` attributes ([`same_kore_without_origins`]);
/// - the frontend definition the assembler parses and expands macros with, compared without
///   the attributes that record where its text was read and how the compiler derived it
///   ([`same_frontend_without_positions`]). `syntaxDefinition.kore` declares only the
///   productions that are symbols, so token and lexical regular expressions, layout and the
///   attributes of subsort productions, which the parser also reads, are compared here.
///
/// Source positions in the definitions' own text are left out on purpose: a layout-only mutant
/// moves every `Location` and assembles and executes every program alike. They never reach a
/// configuration: a definition that records locations in its terms records those of the
/// program text, which both sides read alike, and whether it records them is a production
/// attribute that the comparisons keep.
///
/// Every comparison that cannot be made (a text that does not parse, a definition without a
/// digest or a JSON form) counts as unequal: the campaign then runs its cases, which can only
/// miss a kill that `equivalent` would also have missed, never claim one.
///
/// # Errors
///
/// [`CampaignError::Definition`] when an execution definition has no digest.
pub(crate) fn equivalent(
    baseline: &CompiledDefinition,
    mutant: &CompiledDefinition,
) -> Result<bool, CampaignError> {
    let digests_equal = baseline.execution_digest()? == mutant.execution_digest()?;
    let routes_equal = match (&baseline.route, &mutant.route) {
        (BackendRoute::FromDefinition, BackendRoute::FromDefinition) => true,
        (
            BackendRoute::SourceExecution {
                execution_rewrite_order: baseline_order,
            },
            BackendRoute::SourceExecution {
                execution_rewrite_order: mutant_order,
            },
        ) => baseline_order == mutant_order,
        (BackendRoute::FromDefinition, BackendRoute::SourceExecution { .. })
        | (BackendRoute::SourceExecution { .. }, BackendRoute::FromDefinition) => false,
    };
    // The cheap comparisons first; the frontend's JSON form is built only when every other
    // component is equal.
    Ok(digests_equal
        && routes_equal
        && baseline.main_module == mutant.main_module
        && baseline.syntax_module == mutant.syntax_module
        && baseline.configuration_variables == mutant.configuration_variables
        && same_kore_without_origins(
            &baseline.syntax_definition_kore,
            &mutant.syntax_definition_kore,
            KoreText::Definition,
        )
        && same_kore_without_origins(
            &baseline.macros_kore,
            &mutant.macros_kore,
            KoreText::Sentences,
        )
        && same_frontend_without_positions(
            &baseline.frontend_definition,
            &mutant.frontend_definition,
        ))
}

/// The form of a KORE artifact's text.
#[derive(Clone, Copy)]
enum KoreText {
    /// A whole definition (`syntaxDefinition.kore`).
    Definition,
    /// A bare list of sentences without an enclosing module (`macros.kore`).
    Sentences,
}

/// Whether two KORE artifact texts are equal once every `Source` and `Location` attribute is
/// removed: equal texts, or texts that parse and have equal execution digests, which hash the
/// definition printed without exactly those attributes (`k_rust::backend::execution_digest`).
/// A bare sentence list is compared inside one enclosing module, the same for both. A text that
/// does not parse or has no digest is unequal to every other text.
fn same_kore_without_origins(left: &str, right: &str, form: KoreText) -> bool {
    if left == right {
        return true;
    }
    let digest = |text: &str| {
        let definition = match form {
            KoreText::Definition => k_rust::kore::parser::parse_definition(text),
            KoreText::Sentences => k_rust::kore::parser::parse_definition(&format!(
                "[]\nmodule FUZZMACROS\n{text}\nendmodule\n[]\n"
            )),
        }
        .ok()?;
        k_rust::backend::execution_digest(&definition).ok()
    };
    matches!((digest(left), digest(right)), (Some(left), Some(right)) if left == right)
}

/// Whether two frontend definitions are equal once every attribute that records a source
/// position (`Source`, `Location`, the sentence and content offsets) or the compiler's own
/// provenance (`k_rust::definition::AttributeKey::is_source_position`, `is_provenance_only`)
/// is removed, compared through their KAST JSON forms. A definition without a JSON form is
/// unequal to every other definition.
fn same_frontend_without_positions(
    left: &k_rust::definition::Definition,
    right: &k_rust::definition::Definition,
) -> bool {
    let normal = |definition| {
        let text = k_rust::definition::json::to_string(definition).ok()?;
        let mut value = serde_json::from_str::<serde_json::Value>(&text).ok()?;
        strip_positions(&mut value);
        Some(value)
    };
    matches!((normal(left), normal(right)), (Some(left), Some(right)) if left == right)
}

/// Remove, from every KAST attribute map (`{"node": "KAtt", "att": {...}}`) in `value`, the
/// keys that name a source-position or provenance attribute.
fn strip_positions(value: &mut serde_json::Value) {
    match value {
        serde_json::Value::Object(map) => {
            if map.get("node").and_then(serde_json::Value::as_str) == Some("KAtt")
                && let Some(serde_json::Value::Object(att)) = map.get_mut("att")
            {
                att.retain(|key, _| {
                    !k_rust::definition::AttributeKey::from_name(key)
                        .is_some_and(|key| key.is_source_position() || key.is_provenance_only())
                });
            }
            for child in map.values_mut() {
                strip_positions(child);
            }
        }
        serde_json::Value::Array(items) => {
            for item in items {
                strip_positions(item);
            }
        }
        serde_json::Value::Null
        | serde_json::Value::Bool(_)
        | serde_json::Value::Number(_)
        | serde_json::Value::String(_) => {}
    }
}

/// Judge one pair (ARCHITECTURE 4.3 as amended by FZ-DIFFEND); `paths` is the path mode the
/// mutant's result was run in. A case is a hit by an *added end* if and only if:
/// 1. the baseline run with all paths is complete: every leaf is a clean `stuck` leaf or a clean
///    undefined step, with no bound, stop, timeout, unknown or unsupported leaf; its set of ends
///    holds the `stuck` leaves' configurations only (an undefined step's outcome is no
///    configuration);
/// 2. the mutant leaf is a clean, decided `stuck` leaf: a final configuration of the mutant,
///    natural end or abnormal stop alike (under `run_to_completion`, a natural end only);
/// 3. neither side is no evidence: no implementation-chosen value mark and no contradicted
///    claim on a leaf or off every leaf;
/// 4. the mutant leaf's internalized configuration is constructor-only (internal term kinds,
///    not KORE symbols);
/// 5. that configuration is not in the baseline's set of ends, compared as printed KORE after
///    k-rust's normalization, and every end in that set passes condition 4 too (decision D15):
///    a baseline end such as an unevaluated application of a total function may denote the
///    mutant's configuration, so a syntactic difference from it proves nothing.
///
/// With `paths` all-paths a case is also a hit by a *removed end* if conditions 1 and 3 hold, the
/// mutant's run is complete in the sense of condition 1 (its set of ends may be empty, when every
/// path takes an undefined step) with every end constructor-only, and some baseline end (a
/// clean `stuck` leaf, a natural end under `run_to_completion`) with a constructor-only
/// configuration is not in the mutant's set. The mutant's ends must be data too: a mutant end
/// such as an unevaluated application of a total function may denote the baseline's end, so its
/// syntactic difference proves nothing.
///
/// A baseline that refuses the initial state (an `Err` with a refused state, or only `vacuous`
/// leaves at depth 0) makes the case `rejected`, as [`exec::classify`] classes it: the input is
/// not a state of the baseline, so there is nothing to compare. An incomplete baseline makes the
/// case `baseline-incomplete`, whatever the mutant did.
/// Otherwise the mutant's leaves are classed by [`exec::classify`], a leaf "reaching the target"
/// when it is an added end. Two outcomes are neither a hit nor a pass, and are `unsupported`,
/// as a target-reaching leaf that is not clean is (ARCHITECTURE 5.3):
/// - an added or removed end exists, but the mutant's result is no evidence
///   ([`no_evidence`]): an implementation-chosen value or a contradicted claim on some leaf, or
///   one the run noted on no leaf ([`CaseResult::run_facts_off_leaves`]); condition 3 is a fact
///   of the whole result;
/// - no kill exists, but some end outside the other side's set could not be judged: a clean
///   end that is not constructor-only, a `stuck` leaf that is not clean (or, under
///   `run_to_completion`, whose natural end is undecided), or a would-be kill against a
///   complete set that holds an end that is not data (the set is complete, so the case is not
///   `baseline-incomplete`, but its ends cannot be compared).
///
/// # Errors
///
/// [`EngineDefect`] from classification, or when a clean natural end outside the other side's
/// set carries no constructor-only judgement although [`plan`] asked for it.
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "the campaign calls `judge_pair_explained`; the tests compare judgements alone"
    )
)]
pub(crate) fn judge_pair(
    baseline: &CaseResult,
    mutant: &CaseResult,
    paths: PathMode,
    run_to_completion: bool,
) -> Result<DifferentialJudgement, EngineDefect> {
    judge_pair_explained(baseline, mutant, paths, run_to_completion).map(|(judgement, _)| judgement)
}

/// [`judge_pair`], with the reason of an `unsupported` or `baseline-incomplete` class
/// ([`crate::exec::reasons`]): `Some` exactly for those two classes.
///
/// # Errors
///
/// As [`judge_pair`].
pub(crate) fn judge_pair_explained(
    baseline: &CaseResult,
    mutant: &CaseResult,
    paths: PathMode,
    run_to_completion: bool,
) -> Result<(DifferentialJudgement, Option<UnjudgedReason>), EngineDefect> {
    if exec::classify(baseline, &vec![false; baseline.leaves.len()], false)?
        == OutcomeClass::Rejected
    {
        return Ok((DifferentialJudgement::class(OutcomeClass::Rejected), None));
    }
    let Some(baseline_set) = complete_ends(baseline) else {
        let reason = reasons::incomplete(baseline).unwrap_or(UnjudgedReason::EngineDefect);
        return Ok((
            DifferentialJudgement::class(OutcomeClass::BaselineIncomplete),
            Some(reason),
        ));
    };
    let added = Verdicts::outside(mutant, baseline, &baseline_set, "mutant", run_to_completion)?;
    let removed = match (paths, complete_ends(mutant)) {
        (PathMode::AllPaths, Some(mutant_set)) => {
            Verdicts::outside(baseline, mutant, &mutant_set, "baseline", run_to_completion)?
        }
        (PathMode::OnePath, _) | (PathMode::AllPaths, None) => Verdicts::none(baseline),
    };
    let killing_leaf = added.kills.iter().position(|&kills| kills);
    let removed_end = removed.kills.iter().position(|&kills| kills);
    let (class, reason) = exec::classify_explained(mutant, &added.kills, run_to_completion)?;
    if (killing_leaf.is_some() || removed_end.is_some()) && no_evidence(mutant) {
        // Not `kill-on-chosen-value` alone: `no_evidence` also holds for a contradicted claim,
        // whose remedy is not about map or set order.
        return Ok((
            DifferentialJudgement::class(OutcomeClass::Unsupported),
            Some(UnjudgedReason::KillWithoutEvidence),
        ));
    }
    if class == OutcomeClass::Hit && killing_leaf.is_none() {
        return Err(EngineDefect {
            case: None,
            description: "classification reported a differential hit without a killing leaf"
                .to_owned(),
        });
    }
    if class == OutcomeClass::Hit || removed_end.is_some() {
        return Ok((
            DifferentialJudgement {
                class: OutcomeClass::Hit,
                killing_leaf: killing_leaf.filter(|_| class == OutcomeClass::Hit),
                removed_end,
            },
            None,
        ));
    }
    if let Some(undecided) = added.undecided.or(removed.undecided) {
        // The mutant's own classification, when it is `unsupported`, names the fact nearer the
        // backend (an unclean leaf); otherwise the comparison's refusal is the reason.
        let reason = reason.map_or(undecided, |reason| reason.min(undecided));
        return Ok((
            DifferentialJudgement::class(OutcomeClass::Unsupported),
            Some(reason),
        ));
    }
    Ok((DifferentialJudgement::class(class), reason))
}

/// Whether the mutant's result is no evidence of a kill (condition 3): some leaf carries an
/// implementation-chosen value or a contradicted claim, or the run noted one on no leaf (which,
/// under state sets, includes the marks of an arrival a merge absorbed). A chosen value makes
/// the result depend on a choice k-rust made; a contradicted claim (`total`, or
/// `preserves-definedness`) makes the definition inconsistent on this input, so no end and no
/// undefined step of it is a fact of the definition. Either one anywhere on the result is
/// enough: the leaves of a result are judged together, as one set.
fn no_evidence(result: &CaseResult) -> bool {
    result.run_facts_off_leaves
        || result.leaves.iter().any(|leaf| {
            leaf.unclean.iter().any(|reason| {
                matches!(
                    reason,
                    UncleanReason::ImplementationChosenValue | UncleanReason::ContradictedClaim
                )
            })
        })
}

/// Whether a one-path case must be decided by an all-paths run of the mutant: one path cannot
/// establish the mutant's set of ends, so it can show no removed end, and this is the only case
/// in which a removed end may still kill. That is when the baseline is complete, the mutant's one
/// path is complete in the same sense (a clean end or a clean undefined step, no mark, no claim:
/// otherwise its all-paths run, which contains that path, cannot be complete either) and adds no
/// end, and some baseline end that could be a removed end (data, and a natural end under
/// `run_to_completion`) is not among the ends the one path reached. The case of TRIAL2's B-T1 is
/// one: the baseline stops where the mutant's one path takes an undefined step, whose outcome is
/// no end. A deterministic definition reaches its one end on its one path, so the re-run happens
/// only where the one path ends in an undefined step or at another end than the baseline's.
pub(crate) fn needs_all_paths(
    baseline: &CaseResult,
    one_path: &CaseResult,
    run_to_completion: bool,
) -> bool {
    let (Some(baseline_set), Some(reached)) = (complete_ends(baseline), complete_ends(one_path))
    else {
        return false;
    };
    let adds_none = one_path
        .leaves
        .iter()
        .all(|leaf| leaf.halt != HaltReasonOutput::Stuck || baseline_set.contains(&leaf.state));
    adds_none
        && baseline.leaves.iter().any(|leaf| {
            leaf.halt == HaltReasonOutput::Stuck
                && leaf.constructor_only == Some(true)
                && (!run_to_completion || leaf.natural_end)
                && !reached.contains(&leaf.state)
        })
}

/// A side's set of ends when its all-paths run is complete (condition 1, with condition 3 for
/// that side: a marked leaf is not clean), or `None`.
///
/// A complete run returned leaves, was not stopped by the safety limit, counted no stack stop,
/// SMT unknown or run allowance refusal, is inside the determinism contract (no stack stop in
/// its definition's load either, [`CaseResult::determinism_breaks`]), noted no
/// implementation-chosen value or contradicted claim that no leaf carries
/// ([`CaseResult::run_facts_off_leaves`]), and every leaf is a clean `stuck` leaf or an
/// undefined step (`trivial`) whose only unclean reason is its halt (a decided, ceil-free
/// configuration with no diagnostic, so that the step's undefinedness is decided, not resting
/// on a mark or a refuted claim). The set holds the `stuck` leaves' configurations only: an
/// undefined step's leaf holds a configuration that is not stuck and has no successor, and the
/// path's outcome there is undefinedness, no configuration (the module documentation, "What an
/// end is"). Load records are facts
/// about the definition and do not make a run incomplete (T-5).
///
/// Why the off-leaf facts matter (review B1): an unmarked leaf exists in every model of the
/// definition, but work that read an open value and vanished (an undefined candidate beside a
/// defined sibling) may give another leaf in another model, so the leaves are not every end. The
/// flag matches a run-listed value to leaf marks by hook and class, so it may miss an off-leaf
/// value whose twin is on some leaf; that leaf's mark already makes the side incomplete.
///
/// Run-observed unsupported hooks need no check here: since D21, `exec` marks every leaf of a
/// run that observed one ([`UncleanReason::UnsupportedHook`]), so [`complete_end`] already
/// refuses such a side.
fn complete_ends(result: &CaseResult) -> Option<BTreeSet<&KorePattern>> {
    let run_clean = result.failure.is_none()
        && !result.run_facts_off_leaves
        && !result.safety_limit_hit
        && result.stack_stops == 0
        && result.smt_unknowns == 0
        && result.run_allowance_refusals == 0
        && result.determinism_breaks().is_empty()
        && !result.leaves.is_empty();
    if !run_clean || !result.leaves.iter().all(complete_leaf) {
        return None;
    }
    Some(
        result
            .leaves
            .iter()
            .filter(|leaf| leaf.halt == HaltReasonOutput::Stuck)
            .map(|leaf| &leaf.state)
            .collect(),
    )
}

/// Whether a leaf may be part of a complete run (condition 1): a clean `stuck` leaf (an end) or
/// a clean undefined step (no end).
fn complete_leaf(leaf: &LeafReport) -> bool {
    match leaf.halt {
        HaltReasonOutput::Stuck => leaf.is_clean(),
        HaltReasonOutput::Trivial => leaf
            .unclean
            .iter()
            .all(|reason| *reason == UncleanReason::Halt),
        _ => false,
    }
}

/// What one side's leaves show against the other side's complete set of ends.
#[derive(Debug, Eq, PartialEq)]
struct Verdicts {
    /// `kills[i]`: leaf `i` is a clean `stuck` leaf (condition 2) whose configuration is
    /// constructor-only (condition 4) and not in the other side's set (condition 5).
    kills: Vec<bool>,
    /// Some end outside the other side's set could not be judged: a clean end that is not
    /// constructor-only, a `stuck` leaf that is not clean, or, under `run_to_completion`, a
    /// clean `stuck` leaf whose natural end is undecided. The reason of the first such end
    /// found, or that the other side's set holds an end that is not data.
    undecided: Option<UnjudgedReason>,
}

impl Verdicts {
    /// No judgement of `side`'s leaves.
    fn none(side: &CaseResult) -> Self {
        Self {
            kills: vec![false; side.leaves.len()],
            undecided: None,
        }
    }

    /// The leaves of `side` whose configuration the other side's complete set of ends,
    /// `others_set` (the ends of `others`), lacks: the mutant's added ends against the baseline,
    /// or the baseline's removed ends against the mutant.
    ///
    /// A kill needs data on both sides (conditions 4 and 5, decision D15): when some end of
    /// `others` is not constructor-only, an end that `others_set` lacks syntactically may still
    /// be one the other side reaches, so every would-be kill is undecided instead. Only the
    /// ends of `others` count: the outcome of its undefined steps is no configuration.
    ///
    /// Every clean, decided `stuck` leaf is an end, a natural end or an abnormal stop alike: in
    /// both, no rule applies, so the configuration is final in that definition's transition
    /// system, and set exclusion is about final configurations. Under `run_to_completion` the
    /// author asked that a kill also end the program, so only a natural end kills, and a leaf
    /// whose natural end is undecided is undecided.
    fn outside(
        side: &CaseResult,
        others: &CaseResult,
        others_set: &BTreeSet<&KorePattern>,
        role: &str,
        run_to_completion: bool,
    ) -> Result<Self, EngineDefect> {
        let mut verdicts = Self::none(side);
        for (index, leaf) in side.leaves.iter().enumerate() {
            // Only a stuck leaf is an end that may be a kill; an undefined step's outcome is no end,
            // and a bound or a stop is classed by `exec::classify`.
            if leaf.halt != HaltReasonOutput::Stuck || others_set.contains(&leaf.state) {
                continue;
            }
            if !leaf.is_clean() {
                let reason = reasons::beyond_halt(leaf).unwrap_or(UnjudgedReason::EngineDefect);
                verdicts.undecided.get_or_insert(reason);
                continue;
            }
            // Set membership does not depend on the natural end; only `run_to_completion` asks
            // for one, and only then does an undecided natural end leave the leaf undecided. A
            // decided abnormal stop under `run_to_completion` is simply no kill, with no reason.
            if run_to_completion && !leaf.natural_end {
                if leaf.natural_end_undecided() {
                    verdicts
                        .undecided
                        .get_or_insert(UnjudgedReason::NaturalEndUndecided);
                }
                continue;
            }
            match leaf.constructor_only {
                Some(true) => verdicts.kills[index] = true,
                Some(false) => {
                    verdicts.undecided.get_or_insert(not_data(role));
                }
                None => {
                    return Err(EngineDefect {
                        case: None,
                        description: format!(
                            "{role} leaf {index} is an end without the constructor-only \
                             judgement the differential plan requests"
                        ),
                    });
                }
            }
        }
        let others_are_data = others
            .leaves
            .iter()
            .filter(|leaf| leaf.halt == HaltReasonOutput::Stuck)
            .all(|leaf| leaf.constructor_only == Some(true));
        if !others_are_data && verdicts.kills.contains(&true) {
            verdicts.kills.fill(false);
            verdicts
                .undecided
                .get_or_insert(not_data(if role == "mutant" {
                    "baseline"
                } else {
                    "mutant"
                }));
        }
        Ok(verdicts)
    }
}

/// The reason for an end of the side `role` (`"mutant"` or `"baseline"`) that is not data.
fn not_data(role: &str) -> UnjudgedReason {
    if role == "mutant" {
        UnjudgedReason::MutantEndNotData
    } else {
        UnjudgedReason::BaselineEndNotData
    }
}

#[cfg(test)]
mod tests {
    use k_rust::kore::parser::parse_pattern;

    use super::*;
    use crate::{
        exec::{CaseFailure, FailureCause},
        report::LoadRecord,
    };

    /// A final configuration `<generatedTop>(<k>(.K), <out>(N), <generatedCounter>(C))`.
    fn config(out: i64, counter: i64) -> KorePattern {
        parse_pattern(&format!(
            "Lbl'-LT-'generatedTop'-GT-'{{}}(\
               Lbl'-LT-'k'-GT-'{{}}(dotk{{}}()), \
               Lbl'-LT-'out'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"{out}\")), \
               Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"{counter}\")))"
        ))
        .expect("the test configuration parses")
    }

    /// A clean natural end with the given constructor-only judgement.
    fn natural(state: KorePattern, constructor_only: Option<bool>) -> LeafReport {
        LeafReport {
            halt: HaltReasonOutput::Stuck,
            depth: 3,
            state,
            unclean: Vec::new(),
            natural_end: true,
            matches: Vec::new(),
            rewrites: Vec::new(),
            constructor_only,
        }
    }

    /// A leaf with `halt` and `unclean` that is not a natural end.
    fn leaf(halt: HaltReasonOutput, state: KorePattern, unclean: Vec<UncleanReason>) -> LeafReport {
        LeafReport {
            halt,
            depth: 3,
            state,
            unclean,
            natural_end: false,
            matches: Vec::new(),
            rewrites: Vec::new(),
            constructor_only: None,
        }
    }

    fn result(leaves: Vec<LeafReport>) -> CaseResult {
        CaseResult {
            leaves,
            work: 10,
            coverage: None,
            stack_stops: 0,
            smt_unknowns: 0,
            run_allowance_refusals: 0,
            run_facts_off_leaves: false,
            load_records: Vec::new(),
            safety_limit_hit: false,
            failure: None,
        }
    }

    /// A complete baseline with the two ends 3 and 4 (the COIN baseline on `flip(3)`), both
    /// judged constructor-only.
    fn coin_baseline() -> CaseResult {
        result(vec![
            natural(config(3, 0), Some(true)),
            natural(config(4, 0), Some(true)),
        ])
    }

    fn judge(baseline: &CaseResult, mutant: &CaseResult, paths: PathMode) -> DifferentialJudgement {
        judge_pair(baseline, mutant, paths, false).expect("no engine defect")
    }

    fn added(baseline: &CaseResult, mutant: &CaseResult) -> Verdicts {
        let ends = complete_ends(baseline).expect("the baseline is complete");
        Verdicts::outside(mutant, baseline, &ends, "mutant", false).expect("no engine defect")
    }

    fn hit(killing_leaf: Option<usize>, removed_end: Option<usize>) -> DifferentialJudgement {
        DifferentialJudgement {
            class: OutcomeClass::Hit,
            killing_leaf,
            removed_end,
        }
    }

    const BOTH_MODES: [PathMode; 2] = [PathMode::OnePath, PathMode::AllPaths];

    // ---- plan

    #[test]
    fn baseline_runs_all_paths_and_mutant_the_campaign_mode_both_as_state_sets() {
        for paths in BOTH_MODES {
            let plan = plan(&CaseOptions {
                paths,
                ..CaseOptions::default()
            });
            assert_eq!(plan.baseline.paths, Some(PathMode::AllPaths));
            assert_eq!(plan.mutant.paths, Some(paths));
            let rerun = plan.mutant_all_paths.as_ref();
            assert_eq!(rerun.is_some(), paths == PathMode::OnePath);
            if let Some(rerun) = rerun {
                assert_eq!(rerun.paths, Some(PathMode::AllPaths));
            }
            for needs in [&plan.baseline, &plan.mutant].into_iter().chain(rerun) {
                assert!(needs.constructor_only);
                assert!(needs.state_set);
                assert!(!needs.trace);
                assert!(needs.terminal_rules.is_empty());
            }
        }
    }

    // ---- condition 1: completeness

    #[test]
    fn complete_baseline_holds_its_stuck_ends_and_not_its_undefined_steps() {
        let undefined = config(7, 0);
        let baseline = result(vec![
            natural(config(3, 0), None),
            leaf(
                HaltReasonOutput::Trivial,
                undefined.clone(),
                vec![UncleanReason::Halt],
            ),
            // A clean abnormal stop is a final configuration too.
            leaf(HaltReasonOutput::Stuck, config(9, 0), Vec::new()),
        ]);
        let ends = complete_ends(&baseline).expect("complete");
        assert_eq!(ends.len(), 2);
        // An undefined step's configuration is not stuck, and its outcome is no configuration.
        assert!(!ends.contains(&undefined));
        // Every path an undefined step: complete, with no end.
        let all_undefined = result(vec![leaf(
            HaltReasonOutput::Trivial,
            undefined,
            vec![UncleanReason::Halt],
        )]);
        assert_eq!(
            complete_ends(&all_undefined).map(|ends| ends.len()),
            Some(0)
        );
    }

    #[test]
    fn every_unclean_or_unfinished_leaf_makes_a_side_incomplete() {
        use HaltReasonOutput as H;
        let unfinished = [
            H::DepthBound,
            H::BreadthBound,
            H::WorkBound,
            H::Timeout,
            H::Cancelled,
            H::Vacuous,
            H::Terminal,
            H::Branch,
            H::CutPoint,
        ];
        for halt in unfinished {
            let baseline = result(vec![
                natural(config(3, 0), None),
                leaf(halt, config(4, 0), vec![UncleanReason::Halt]),
            ]);
            assert!(complete_ends(&baseline).is_none(), "{halt:?}");
        }
        let unclean = [
            UncleanReason::Undecided,
            UncleanReason::NotCeilFree(None),
            UncleanReason::ImplementationChosenValue,
            UncleanReason::ContradictedClaim,
            UncleanReason::IterationExhaustion,
            UncleanReason::Internalization("no".to_owned()),
        ];
        for reason in unclean {
            for (halt, mut reasons) in [(H::Stuck, vec![]), (H::Trivial, vec![UncleanReason::Halt])]
            {
                reasons.push(reason.clone());
                let baseline = result(vec![
                    natural(config(3, 0), None),
                    leaf(halt, config(4, 0), reasons),
                ]);
                assert!(complete_ends(&baseline).is_none(), "{halt:?} {reason:?}");
            }
        }
    }

    #[test]
    fn run_level_facts_make_a_side_incomplete() {
        let cases: [fn(&mut CaseResult); 9] = [
            |r| r.stack_stops = 1,
            |r| r.smt_unknowns = 1,
            |r| r.run_allowance_refusals = 1,
            |r| r.safety_limit_hit = true,
            |r| {
                r.failure = Some(CaseFailure::other("err"));
                r.leaves.clear();
            },
            |r| r.leaves.clear(),
            // The failure check alone, with the leaves kept.
            |r| r.failure = Some(CaseFailure::other("err")),
            // A chosen value or claim the run noted on no leaf (review B1).
            |r| r.run_facts_off_leaves = true,
            // A stack stop in the definition's load puts the case outside the determinism
            // contract.
            |r| {
                r.load_records.push(LoadRecord {
                    kind: crate::exec::LOAD_STACK_STOP.to_owned(),
                    detail: "load".to_owned(),
                });
            },
        ];
        for (index, edit) in cases.into_iter().enumerate() {
            let mut baseline = coin_baseline();
            edit(&mut baseline);
            assert!(complete_ends(&baseline).is_none(), "case {index}");
        }
    }

    #[test]
    fn a_contradicted_claim_of_the_load_does_not_make_a_side_incomplete() {
        let mut baseline = coin_baseline();
        baseline.load_records.push(LoadRecord {
            kind: "contradicted-claim".to_owned(),
            detail: "td(0)".to_owned(),
        });
        assert!(complete_ends(&baseline).is_some());
    }

    #[test]
    fn incomplete_baseline_is_baseline_incomplete_whatever_the_mutant() {
        let baseline = result(vec![
            natural(config(3, 0), None),
            leaf(
                HaltReasonOutput::DepthBound,
                config(4, 0),
                vec![UncleanReason::Halt],
            ),
        ]);
        // The mutant's end 5 would kill against a complete set {3, 4}.
        let mutant = result(vec![natural(config(5, 0), Some(true))]);
        for paths in BOTH_MODES {
            assert_eq!(
                judge(&baseline, &mutant, paths),
                DifferentialJudgement::class(OutcomeClass::BaselineIncomplete)
            );
        }
    }

    // ---- reasons (FZ-UNSUPPORTED)

    fn explained(
        baseline: &CaseResult,
        mutant: &CaseResult,
        paths: PathMode,
    ) -> (OutcomeClass, Option<UnjudgedReason>) {
        let (judgement, reason) =
            judge_pair_explained(baseline, mutant, paths, false).expect("no engine defect");
        (judgement.class, reason)
    }

    #[test]
    fn an_end_that_is_not_data_names_its_side() {
        // TRIAL2's SIMPLE shape: the mutant's end outside the baseline's set holds a function
        // application, so the two ends cannot be compared.
        let mutant = result(vec![natural(config(5, 0), Some(false))]);
        for paths in BOTH_MODES {
            assert_eq!(
                explained(&coin_baseline(), &mutant, paths),
                (
                    OutcomeClass::Unsupported,
                    Some(UnjudgedReason::MutantEndNotData)
                )
            );
        }
        // A would-be kill against a complete baseline set that holds an end that is not data.
        let baseline = result(vec![
            natural(config(3, 0), Some(false)),
            natural(config(4, 0), Some(true)),
        ]);
        let killing = result(vec![natural(config(5, 0), Some(true))]);
        assert_eq!(
            explained(&baseline, &killing, PathMode::OnePath),
            (
                OutcomeClass::Unsupported,
                Some(UnjudgedReason::BaselineEndNotData)
            )
        );
    }

    #[test]
    fn an_incomplete_baseline_names_what_cut_it() {
        let mutant = result(vec![natural(config(5, 0), Some(true))]);
        for (cut, expected) in [
            (
                leaf(
                    HaltReasonOutput::DepthBound,
                    config(9, 0),
                    vec![UncleanReason::Halt],
                ),
                UnjudgedReason::DepthBound,
            ),
            (
                leaf(
                    HaltReasonOutput::WorkBound,
                    config(9, 0),
                    vec![UncleanReason::Halt],
                ),
                UnjudgedReason::WorkBound,
            ),
            (
                leaf(
                    HaltReasonOutput::Stuck,
                    config(9, 0),
                    vec![UncleanReason::NotCeilFree(None)],
                ),
                UnjudgedReason::NotCeilFree,
            ),
        ] {
            let baseline = result(vec![natural(config(3, 0), Some(true)), cut]);
            assert_eq!(
                explained(&baseline, &mutant, PathMode::OnePath),
                (OutcomeClass::BaselineIncomplete, Some(expected))
            );
        }
    }

    #[test]
    fn a_kill_resting_on_a_chosen_value_is_named() {
        let mut mutant = result(vec![natural(config(5, 0), Some(true))]);
        mutant.run_facts_off_leaves = true;
        assert_eq!(
            explained(&coin_baseline(), &mutant, PathMode::OnePath),
            (
                OutcomeClass::Unsupported,
                Some(UnjudgedReason::KillWithoutEvidence)
            )
        );
    }

    // ---- reasons of FZ-DIFFEND's judgements (INT7, the merge of FZ-DIFFEND and FZ-UNSUPPORTED)

    fn explained_rtc(
        baseline: &CaseResult,
        mutant: &CaseResult,
        paths: PathMode,
        run_to_completion: bool,
    ) -> (OutcomeClass, Option<UnjudgedReason>) {
        let (judgement, reason) = judge_pair_explained(baseline, mutant, paths, run_to_completion)
            .expect("no engine defect");
        (judgement.class, reason)
    }

    #[test]
    fn a_kill_beside_a_contradicted_claim_is_a_kill_without_evidence() {
        // `no_evidence` also holds for a contradicted claim, on another leaf than the killing
        // one or on the result's lists; its reason is not the chosen-value one, whose remedy is
        // about map or set order.
        let on_leaf = result(vec![
            natural(config(5, 0), Some(true)),
            leaf(
                HaltReasonOutput::Trivial,
                config(3, 0),
                vec![UncleanReason::Halt, UncleanReason::ContradictedClaim],
            ),
        ]);
        let mut off_leaf = result(vec![natural(config(5, 0), Some(true))]);
        off_leaf.run_facts_off_leaves = true;
        for mutant in [&on_leaf, &off_leaf] {
            for paths in BOTH_MODES {
                assert_eq!(
                    explained(&coin_baseline(), mutant, paths),
                    (
                        OutcomeClass::Unsupported,
                        Some(UnjudgedReason::KillWithoutEvidence)
                    )
                );
            }
        }
        // A removed end on an empty set that carries the claim on its undefined step: no kill
        // either, and the claim's own reason, since the mutant's set is not complete.
        let claimed = result(vec![leaf(
            HaltReasonOutput::Trivial,
            config(3, 0),
            vec![UncleanReason::Halt, UncleanReason::ContradictedClaim],
        )]);
        assert_eq!(
            explained(&coin_baseline(), &claimed, PathMode::AllPaths),
            (
                OutcomeClass::Unsupported,
                Some(UnjudgedReason::ContradictedClaim)
            )
        );
        assert!(
            UnjudgedReason::KillWithoutEvidence
                .remedy()
                .is_some_and(|remedy| !remedy.contains("total"))
        );
    }

    #[test]
    fn an_undecided_natural_end_has_a_reason_only_under_run_to_completion() {
        let mut end = abnormal(config(5, 0), Some(true));
        end.unclean = vec![UncleanReason::NaturalEndUndecided];
        let mutant = result(vec![end]);
        // Without run-to-completion the end is an end: an added end, a kill, no reason.
        assert_eq!(
            explained_rtc(&coin_baseline(), &mutant, PathMode::OnePath, false),
            (OutcomeClass::Hit, None)
        );
        // Under run-to-completion it is neither a kill nor a proof of none.
        assert_eq!(
            explained_rtc(&coin_baseline(), &mutant, PathMode::OnePath, true),
            (
                OutcomeClass::Unsupported,
                Some(UnjudgedReason::NaturalEndUndecided)
            )
        );
        // A decided abnormal stop under run-to-completion is `stuck`, with no reason.
        let stop = result(vec![abnormal(config(5, 0), Some(true))]);
        assert_eq!(
            explained_rtc(&coin_baseline(), &stop, PathMode::OnePath, true),
            (OutcomeClass::Stuck, None)
        );
        // Without run-to-completion a decided abnormal stop outside the set kills.
        assert_eq!(
            explained_rtc(&coin_baseline(), &stop, PathMode::OnePath, false),
            (OutcomeClass::Hit, None)
        );
    }

    #[test]
    fn a_removed_end_that_is_not_data_names_the_baseline() {
        // The all-paths mutant's complete set {3} lacks the baseline's end 4, which is not
        // data: it may denote 3, so it is not shown removed.
        let baseline = result(vec![
            natural(config(3, 0), Some(true)),
            natural(config(4, 0), Some(false)),
        ]);
        let mutant = result(vec![natural(config(3, 0), Some(true))]);
        assert_eq!(
            explained(&baseline, &mutant, PathMode::AllPaths),
            (
                OutcomeClass::Unsupported,
                Some(UnjudgedReason::BaselineEndNotData)
            )
        );
        // The one-path mode shows no set, so nothing is compared beyond the added ends.
        assert_eq!(
            explained(&baseline, &mutant, PathMode::OnePath),
            (OutcomeClass::Miss, None)
        );
        // A removed data end against a mutant set holding an end that is not data.
        let baseline = coin_baseline();
        let mutant = result(vec![natural(config(3, 0), Some(false))]);
        assert_eq!(
            explained(&baseline, &mutant, PathMode::AllPaths),
            (
                OutcomeClass::Unsupported,
                Some(UnjudgedReason::MutantEndNotData)
            )
        );
    }

    #[test]
    fn a_clean_undefined_step_keeps_a_side_complete_and_the_reasons_agree() {
        // `reasons::incomplete` names a reason exactly when `complete_ends` refuses the side.
        let trivial = |unclean| leaf(HaltReasonOutput::Trivial, config(6, 0), unclean);
        let sides = [
            result(vec![trivial(vec![UncleanReason::Halt])]),
            result(vec![
                natural(config(3, 0), Some(true)),
                trivial(vec![UncleanReason::Halt]),
            ]),
            result(vec![trivial(vec![
                UncleanReason::Halt,
                UncleanReason::ContradictedClaim,
            ])]),
            result(vec![trivial(vec![
                UncleanReason::Halt,
                UncleanReason::ImplementationChosenValue,
            ])]),
            result(vec![
                natural(config(3, 0), Some(true)),
                leaf(
                    HaltReasonOutput::WorkBound,
                    config(7, 0),
                    vec![UncleanReason::Halt],
                ),
            ]),
            result(vec![leaf(
                HaltReasonOutput::Stuck,
                config(3, 0),
                vec![UncleanReason::NaturalEndUndecided],
            )]),
            result(vec![leaf(
                HaltReasonOutput::Stuck,
                config(3, 0),
                vec![UncleanReason::NotCeilFree(None)],
            )]),
            result(Vec::new()),
        ];
        for side in &sides {
            assert_eq!(
                complete_ends(side).is_some(),
                reasons::incomplete(side).is_none(),
                "{side:?}"
            );
        }
        // A baseline whose one path is a clean undefined step is complete with the empty set:
        // any mutant end is added.
        let baseline = &sides[0];
        let mutant = result(vec![natural(config(5, 0), Some(true))]);
        assert_eq!(
            explained(baseline, &mutant, PathMode::OnePath),
            (OutcomeClass::Hit, None)
        );
        // A baseline with a work-bound path names the bound.
        assert_eq!(
            explained(&sides[4], &mutant, PathMode::OnePath),
            (
                OutcomeClass::BaselineIncomplete,
                Some(UnjudgedReason::WorkBound)
            )
        );
        // An all-paths mutant whose every path takes a clean undefined step removes every
        // baseline end: a kill, with no reason.
        assert_eq!(
            explained(&coin_baseline(), &sides[0], PathMode::AllPaths),
            (OutcomeClass::Hit, None)
        );
    }

    // ---- conditions 2, 4, 5 per mutant leaf

    #[test]
    fn a_mutant_end_outside_the_set_kills() {
        let mutant = result(vec![natural(config(5, 0), Some(true))]);
        assert_eq!(
            added(&coin_baseline(), &mutant),
            Verdicts {
                kills: vec![true],
                undecided: None,
            }
        );
    }

    #[test]
    fn a_mutant_end_inside_the_set_does_not_kill() {
        // A mutant whose single path differs from the baseline's but stays in its set.
        for out in [3, 4] {
            let mutant = result(vec![natural(config(out, 0), Some(true))]);
            assert_eq!(
                added(&coin_baseline(), &mutant),
                Verdicts {
                    kills: vec![false],
                    undecided: None,
                }
            );
        }
    }

    #[test]
    fn a_difference_only_in_the_generated_counter_kills() {
        let mutant = result(vec![natural(config(3, 1), Some(true))]);
        assert_eq!(added(&coin_baseline(), &mutant).kills, vec![true]);
    }

    /// A clean abnormal stop (a `stuck` leaf that is not a natural end) with the given
    /// constructor-only judgement.
    fn abnormal(state: KorePattern, constructor_only: Option<bool>) -> LeafReport {
        LeafReport {
            constructor_only,
            ..leaf(HaltReasonOutput::Stuck, state, Vec::new())
        }
    }

    /// A clean undefined step from `state`.
    fn undefined(state: KorePattern) -> LeafReport {
        leaf(HaltReasonOutput::Trivial, state, vec![UncleanReason::Halt])
    }

    #[test]
    fn an_abnormal_stop_outside_the_set_kills() {
        // FZ-DIFFEND: condition 2 asks for a final configuration, which an abnormal stop is.
        let mutant = result(vec![abnormal(config(5, 0), Some(true))]);
        assert_eq!(added(&coin_baseline(), &mutant).kills, vec![true]);
        // Under run-to-completion only a natural end kills.
        let baseline = coin_baseline();
        let ends = complete_ends(&baseline).expect("complete");
        let verdicts =
            Verdicts::outside(&mutant, &baseline, &ends, "mutant", true).expect("no engine defect");
        assert_eq!(verdicts.kills, vec![false]);
        assert_eq!(verdicts.undecided, None, "a decided abnormal stop has no reason");
        assert_eq!(
            judge_pair(&coin_baseline(), &mutant, PathMode::OnePath, true)
                .expect("no engine defect"),
            DifferentialJudgement::class(OutcomeClass::Stuck)
        );
    }

    #[test]
    fn an_end_whose_natural_end_is_undecided_is_still_an_end() {
        // Set membership does not depend on the natural end (FZ-08 review 2, S4).
        let mut end = abnormal(config(5, 0), Some(true));
        end.unclean = vec![UncleanReason::NaturalEndUndecided];
        let mutant = result(vec![end]);
        assert_eq!(added(&coin_baseline(), &mutant).kills, vec![true]);
        // Under run-to-completion it is neither a kill nor a proof of none.
        let baseline = coin_baseline();
        let ends = complete_ends(&baseline).expect("complete");
        let verdicts =
            Verdicts::outside(&mutant, &baseline, &ends, "mutant", true).expect("no engine defect");
        assert_eq!(verdicts.kills, vec![false]);
        assert_eq!(
            verdicts.undecided,
            Some(UnjudgedReason::NaturalEndUndecided)
        );
    }

    #[test]
    fn an_undefined_step_or_a_bound_outside_the_set_does_not_kill() {
        let mutant = result(vec![
            leaf(
                HaltReasonOutput::Trivial,
                config(6, 0),
                vec![UncleanReason::Halt],
            ),
            leaf(
                HaltReasonOutput::DepthBound,
                config(7, 0),
                vec![UncleanReason::Halt],
            ),
        ]);
        assert_eq!(
            added(&coin_baseline(), &mutant),
            Verdicts {
                kills: vec![false, false],
                undecided: None,
            }
        );
    }

    #[test]
    fn a_natural_end_that_is_not_constructor_only_is_undecided() {
        let mutant = result(vec![natural(config(5, 0), Some(false))]);
        assert_eq!(
            added(&coin_baseline(), &mutant),
            Verdicts {
                kills: vec![false],
                undecided: Some(UnjudgedReason::MutantEndNotData),
            }
        );
    }

    #[test]
    fn an_unclean_stuck_leaf_outside_the_set_is_undecided() {
        let mutant = result(vec![leaf(
            HaltReasonOutput::Stuck,
            config(5, 0),
            vec![UncleanReason::SmtUnknowns],
        )]);
        assert_eq!(
            added(&coin_baseline(), &mutant),
            Verdicts {
                kills: vec![false],
                undecided: Some(UnjudgedReason::SmtUnknowns),
            }
        );
    }

    #[test]
    fn a_missing_constructor_only_judgement_is_an_engine_defect() {
        let mutant = result(vec![natural(config(5, 0), None)]);
        let baseline = coin_baseline();
        let ends = complete_ends(&baseline).expect("complete");
        assert!(Verdicts::outside(&mutant, &baseline, &ends, "mutant", false).is_err());
        // Inside the set the judgement is not read.
        let agreeing = result(vec![natural(config(3, 0), None)]);
        assert!(Verdicts::outside(&agreeing, &baseline, &ends, "mutant", false).is_ok());
    }

    // ---- classes

    #[test]
    fn a_kill_is_a_hit_on_its_leaf() {
        let mutant = result(vec![
            natural(config(3, 0), Some(true)),
            natural(config(5, 0), Some(true)),
        ]);
        // In the all-paths mode the mutant also lacks the baseline's end 4.
        assert_eq!(
            judge(&coin_baseline(), &mutant, PathMode::OnePath),
            hit(Some(1), None)
        );
        assert_eq!(
            judge(&coin_baseline(), &mutant, PathMode::AllPaths),
            hit(Some(1), Some(1))
        );
    }

    #[test]
    fn agreeing_natural_ends_are_a_miss() {
        let mutant = result(vec![
            natural(config(3, 0), Some(true)),
            natural(config(4, 0), Some(true)),
        ]);
        for paths in BOTH_MODES {
            assert_eq!(
                judge(&coin_baseline(), &mutant, paths),
                DifferentialJudgement::class(OutcomeClass::Miss)
            );
        }
    }

    #[test]
    fn a_kill_beside_a_chosen_value_mark_is_unsupported() {
        let mutant = result(vec![
            natural(config(5, 0), Some(true)),
            leaf(
                HaltReasonOutput::Stuck,
                config(3, 0),
                vec![UncleanReason::ImplementationChosenValue],
            ),
        ]);
        for paths in BOTH_MODES {
            assert_eq!(
                judge(&coin_baseline(), &mutant, paths),
                DifferentialJudgement::class(OutcomeClass::Unsupported)
            );
        }
    }

    #[test]
    fn an_undecided_end_without_a_kill_is_unsupported() {
        let mutant = result(vec![natural(config(5, 0), Some(false))]);
        assert_eq!(
            judge(&coin_baseline(), &mutant, PathMode::OnePath),
            DifferentialJudgement::class(OutcomeClass::Unsupported)
        );
    }

    #[test]
    fn a_kill_beside_an_undecided_end_is_still_a_hit() {
        let mutant = result(vec![
            natural(config(6, 0), Some(false)),
            natural(config(5, 0), Some(true)),
        ]);
        assert_eq!(
            judge(&coin_baseline(), &mutant, PathMode::OnePath),
            hit(Some(1), None)
        );
    }

    #[test]
    fn a_bounded_mutant_without_a_kill_keeps_its_class() {
        let mutant = result(vec![leaf(
            HaltReasonOutput::DepthBound,
            config(5, 0),
            vec![UncleanReason::Halt],
        )]);
        for paths in BOTH_MODES {
            assert_eq!(
                judge(&coin_baseline(), &mutant, paths).class,
                OutcomeClass::DepthBound
            );
        }
    }

    #[test]
    fn a_kill_against_a_baseline_end_that_is_not_data_is_unsupported() {
        // The baseline's end 4 is not data (say an unevaluated total function): it may denote
        // the mutant's 5, so 5 is not shown absent. The baseline is complete, so the case is
        // not baseline-incomplete (decision D15).
        let baseline = result(vec![
            natural(config(3, 0), Some(true)),
            natural(config(4, 0), Some(false)),
        ]);
        let killing = result(vec![natural(config(5, 0), Some(true))]);
        let agreeing = result(vec![
            natural(config(3, 0), Some(true)),
            natural(config(4, 0), Some(true)),
        ]);
        assert_eq!(
            judge(&baseline, &killing, PathMode::OnePath),
            DifferentialJudgement::class(OutcomeClass::Unsupported)
        );
        // On all paths the mutant's complete set {5} is data and lacks the baseline's data end
        // 3: a removed end, which the baseline's other end does not affect.
        assert_eq!(
            judge(&baseline, &killing, PathMode::AllPaths),
            hit(None, Some(0))
        );
        for paths in BOTH_MODES {
            assert_eq!(
                judge(&baseline, &agreeing, paths),
                DifferentialJudgement::class(OutcomeClass::Miss),
                "{paths:?}"
            );
        }
    }

    #[test]
    fn a_baseline_that_refuses_the_initial_state_is_rejected() {
        let mutant = result(vec![natural(config(5, 0), Some(true))]);
        let mut refused = result(Vec::new());
        refused.failure = Some(CaseFailure {
            message: "refused".to_owned(),
            cause: FailureCause::StateRefused,
        });
        let mut vacuous = leaf(
            HaltReasonOutput::Vacuous,
            config(0, 0),
            vec![UncleanReason::Halt],
        );
        vacuous.depth = 0;
        let vacuous = result(vec![vacuous]);
        for baseline in [&refused, &vacuous] {
            for paths in BOTH_MODES {
                assert_eq!(
                    judge(baseline, &mutant, paths),
                    DifferentialJudgement::class(OutcomeClass::Rejected),
                    "{paths:?}"
                );
            }
        }
    }

    #[test]
    fn a_kill_beside_mutant_facts_off_its_leaves_is_unsupported() {
        // The mutant noted a chosen value on no leaf: condition 3 is a fact of the whole result.
        let mut mutant = result(vec![natural(config(5, 0), Some(true))]);
        mutant.run_facts_off_leaves = true;
        for paths in BOTH_MODES {
            assert_eq!(
                judge(&coin_baseline(), &mutant, paths),
                DifferentialJudgement::class(OutcomeClass::Unsupported),
                "{paths:?}"
            );
        }
    }

    #[test]
    fn the_witness_is_the_added_end_first_then_the_removed_end() {
        assert_eq!(hit(Some(1), None).witness(), Some((KillKind::AddedEnd, 1)));
        assert_eq!(
            hit(None, Some(0)).witness(),
            Some((KillKind::RemovedEnd, 0))
        );
        assert_eq!(
            hit(Some(1), Some(0)).witness(),
            Some((KillKind::AddedEnd, 1))
        );
        assert_eq!(
            DifferentialJudgement::class(OutcomeClass::Miss).witness(),
            None
        );
    }

    // ---- removed ends (all-paths mode)

    #[test]
    fn a_removed_end_is_a_hit_on_all_paths_only() {
        // The mutant reaches 4 only: it adds nothing and removes 3.
        let mutant = result(vec![natural(config(4, 0), Some(true))]);
        assert_eq!(
            judge(&coin_baseline(), &mutant, PathMode::AllPaths),
            hit(None, Some(0))
        );
        assert_eq!(
            judge(&coin_baseline(), &mutant, PathMode::OnePath),
            DifferentialJudgement::class(OutcomeClass::Miss)
        );
    }

    #[test]
    fn an_incomplete_mutant_removes_no_end() {
        let mutant = result(vec![
            natural(config(4, 0), Some(true)),
            leaf(
                HaltReasonOutput::DepthBound,
                config(4, 0),
                vec![UncleanReason::Halt],
            ),
        ]);
        assert_eq!(
            judge(&coin_baseline(), &mutant, PathMode::AllPaths).class,
            OutcomeClass::DepthBound
        );
    }

    #[test]
    fn a_removed_end_that_is_not_constructor_only_is_unsupported() {
        let baseline = result(vec![
            natural(config(3, 0), Some(false)),
            natural(config(4, 0), Some(true)),
        ]);
        let mutant = result(vec![natural(config(4, 0), Some(true))]);
        assert_eq!(
            judge(&baseline, &mutant, PathMode::AllPaths),
            DifferentialJudgement::class(OutcomeClass::Unsupported)
        );
    }

    #[test]
    fn a_removed_end_beside_a_mutant_end_that_is_not_data_is_unsupported() {
        // The mutant's end 4 is not constructor-only (say an unevaluated total function that
        // happens to print apart from 3 and 4): it may denote 3, so 3 is not shown removed.
        let mutant = result(vec![
            natural(config(4, 0), Some(true)),
            natural(config(6, 0), Some(false)),
        ]);
        assert_eq!(
            judge(&coin_baseline(), &mutant, PathMode::AllPaths),
            DifferentialJudgement::class(OutcomeClass::Unsupported)
        );
    }

    #[test]
    fn a_baseline_end_whose_natural_end_is_undecided_can_be_removed() {
        // The baseline's 3 is clean and final; whether it is a natural end is undecided (review
        // S4), which decides no set membership: outside the mutant's complete set it is a
        // removed end. Under run-to-completion it is neither a removed end nor a proof of none.
        let mut undecided = abnormal(config(3, 0), Some(true));
        undecided.unclean = vec![UncleanReason::NaturalEndUndecided];
        let baseline = result(vec![undecided, natural(config(4, 0), Some(true))]);
        let mutant = result(vec![natural(config(4, 0), Some(true))]);
        assert_eq!(
            judge(&baseline, &mutant, PathMode::AllPaths),
            hit(None, Some(0))
        );
        assert_eq!(
            judge_pair(&baseline, &mutant, PathMode::AllPaths, true).expect("no engine defect"),
            DifferentialJudgement::class(OutcomeClass::Unsupported)
        );
        assert_eq!(
            judge(&baseline, &mutant, PathMode::OnePath),
            DifferentialJudgement::class(OutcomeClass::Miss)
        );
    }

    #[test]
    fn a_removed_abnormal_stop_is_a_hit_and_a_baseline_undefined_step_is_no_end() {
        let baseline = result(vec![
            abnormal(config(3, 0), Some(true)),
            undefined(config(5, 0)),
            natural(config(4, 0), Some(true)),
        ]);
        let mutant = result(vec![natural(config(4, 0), Some(true))]);
        assert_eq!(
            judge(&baseline, &mutant, PathMode::AllPaths),
            hit(None, Some(0))
        );
        // Without the abnormal stop nothing is removed: the undefined step reached no end.
        let baseline = result(vec![
            undefined(config(5, 0)),
            natural(config(4, 0), Some(true)),
        ]);
        assert_eq!(
            judge(&baseline, &mutant, PathMode::AllPaths),
            DifferentialJudgement::class(OutcomeClass::Miss)
        );
    }

    // ---- undefined steps (FZ-DIFFEND, TRIAL2 B-T1)

    #[test]
    fn a_mutant_whose_every_path_is_undefined_removes_every_baseline_end() {
        // B-T1: the baseline stops at S (here the end 3); the mutant's only path takes an
        // undefined step, from S itself or elsewhere. Its complete set of ends is empty.
        let baseline = result(vec![abnormal(config(3, 0), Some(true))]);
        for from in [config(3, 0), config(8, 0)] {
            let mutant = result(vec![undefined(from)]);
            assert_eq!(
                judge(&baseline, &mutant, PathMode::AllPaths),
                hit(None, Some(0))
            );
            // One path establishes no set: the one-path judgement is the mutant's class, and
            // the engine re-runs the mutant on all paths (`needs_all_paths`).
            assert_eq!(
                judge(&baseline, &mutant, PathMode::OnePath),
                DifferentialJudgement::class(OutcomeClass::Undefined)
            );
            assert!(needs_all_paths(&baseline, &mutant, false));
        }
    }

    #[test]
    fn a_baseline_whose_every_path_is_undefined_has_no_end_a_mutant_end_can_be_in() {
        let baseline = result(vec![undefined(config(3, 0))]);
        let mutant = result(vec![natural(config(3, 0), Some(true))]);
        for paths in BOTH_MODES {
            assert_eq!(judge(&baseline, &mutant, paths), hit(Some(0), None));
        }
        // Both sides undefined on every path: two empty sets agree.
        let mutant = result(vec![undefined(config(4, 0))]);
        assert_eq!(
            judge(&baseline, &mutant, PathMode::AllPaths),
            DifferentialJudgement::class(OutcomeClass::Undefined)
        );
        assert!(!needs_all_paths(&baseline, &mutant, false));
    }

    #[test]
    fn a_contradicted_claim_anywhere_on_the_mutant_makes_it_no_evidence() {
        // An undefined step that refutes a `total` or `preserves-definedness` claim: the
        // mutant's theory is inconsistent on this input, so neither its empty set nor its other
        // ends kill.
        let claimed = || {
            leaf(
                HaltReasonOutput::Trivial,
                config(8, 0),
                vec![UncleanReason::ContradictedClaim, UncleanReason::Halt],
            )
        };
        let baseline = result(vec![abnormal(config(3, 0), Some(true))]);
        let only_claimed = result(vec![claimed()]);
        assert!(complete_ends(&only_claimed).is_none());
        assert!(!needs_all_paths(&baseline, &only_claimed, false));
        let beside_an_added_end = result(vec![natural(config(5, 0), Some(true)), claimed()]);
        let mut off_leaves = result(vec![natural(config(5, 0), Some(true))]);
        off_leaves.run_facts_off_leaves = true;
        for paths in BOTH_MODES {
            assert_eq!(
                judge(&baseline, &only_claimed, paths),
                DifferentialJudgement::class(OutcomeClass::Unsupported),
                "{paths:?}"
            );
            for mutant in [&beside_an_added_end, &off_leaves] {
                assert_eq!(
                    judge(&baseline, mutant, paths),
                    DifferentialJudgement::class(OutcomeClass::Unsupported),
                    "{paths:?}"
                );
            }
        }
    }

    #[test]
    fn the_one_path_re_run_happens_only_where_a_removed_end_could_kill() {
        let single = result(vec![natural(config(3, 0), Some(true))]);
        // The one path reaches the baseline's only end, or adds an end: nothing to re-run.
        assert!(!needs_all_paths(&single, &single, false));
        let adds = result(vec![natural(config(5, 0), Some(true))]);
        assert!(!needs_all_paths(&single, &adds, false));
        // The one path misses one of two baseline ends (COIN): only all paths can tell.
        let three = result(vec![natural(config(3, 0), Some(true))]);
        assert!(needs_all_paths(&coin_baseline(), &three, false));
        // An incomplete one path or baseline: its all-paths run cannot be complete either.
        let bounded = result(vec![leaf(
            HaltReasonOutput::WorkBound,
            config(3, 0),
            vec![UncleanReason::Halt],
        )]);
        assert!(!needs_all_paths(&single, &bounded, false));
        assert!(!needs_all_paths(&bounded, &undefined_only(), false));
        // A baseline end that could not be removed (not data; or, under run-to-completion, not
        // a natural end).
        let not_data = result(vec![natural(config(3, 0), Some(false))]);
        assert!(!needs_all_paths(&not_data, &undefined_only(), false));
        let stop = result(vec![abnormal(config(3, 0), Some(true))]);
        assert!(needs_all_paths(&stop, &undefined_only(), false));
        assert!(!needs_all_paths(&stop, &undefined_only(), true));
    }

    fn undefined_only() -> CaseResult {
        result(vec![undefined(config(8, 0))])
    }

    #[test]
    fn a_removed_end_without_a_constructor_only_judgement_is_an_engine_defect() {
        let baseline = result(vec![
            natural(config(3, 0), None),
            natural(config(4, 0), None),
        ]);
        let mutant = result(vec![natural(config(4, 0), Some(true))]);
        assert!(judge_pair(&baseline, &mutant, PathMode::AllPaths, false).is_err());
        // The one-path mode never reads it.
        assert!(judge_pair(&baseline, &mutant, PathMode::OnePath, false).is_ok());
    }
}

/// The differential judge on FZ-FIX's baselines and mutants (`tests/data/README.md`), each side
/// run through its own executor as a campaign case runs it.
#[cfg(test)]
mod fixture_tests {
    use super::*;
    use crate::support::{self, Compiled, Fixture};
    use crate::{
        assemble::ProgramAssembly,
        exec::{CaseRequestShape, Executor},
    };

    /// One side of a differential case: its definition's executor and request shape.
    struct Side {
        compiled: &'static Compiled,
        executor: Executor,
        shape: CaseRequestShape,
    }

    impl Side {
        fn new(fixture: &'static Fixture, needs: &TargetNeeds, options: &CaseOptions) -> Self {
            let compiled = fixture.compiled();
            let definition = compiled.definition();
            let assembly = ProgramAssembly::new(&definition).expect("the fixture assembles");
            let executor =
                Executor::new(&definition, &assembly, options).expect("the executor builds");
            Self {
                compiled,
                executor,
                shape: CaseRequestShape::new(options, needs),
            }
        }

        /// Run the program `text`, named `file`, on this side.
        fn run(&mut self, file: &str, text: &str) -> CaseResult {
            let initial = self
                .compiled
                .assemble(file, text, &[])
                .expect("the program assembles");
            self.executor
                .run(&initial, &self.shape, &[], None)
                .expect("no solver prelude failure")
        }
    }

    /// Judge `text` on `baseline` and `mutant` under `options`, each side planned by [`plan`].
    fn judge_on(
        baseline: &'static Fixture,
        mutant: &'static Fixture,
        file: &str,
        text: &str,
        options: &CaseOptions,
    ) -> DifferentialJudgement {
        let plan = plan(options);
        let baseline = Side::new(baseline, &plan.baseline, options).run(file, text);
        let mutant = Side::new(mutant, &plan.mutant, options).run(file, text);
        judge_pair(&baseline, &mutant, options.paths, false).expect("no engine defect")
    }

    fn options(paths: PathMode) -> CaseOptions {
        CaseOptions {
            paths,
            ..CaseOptions::default()
        }
    }

    /// `flip(n)` on the COIN baseline and `mutant`.
    fn flip(mutant: &'static Fixture, n: i64, paths: PathMode) -> DifferentialJudgement {
        judge_on(
            &support::COIN,
            mutant,
            "coin/flip.pgm",
            &format!("flip({n})"),
            &options(paths),
        )
    }

    const BOTH_MODES: [PathMode; 2] = [PathMode::OnePath, PathMode::AllPaths];
    const MISS: DifferentialJudgement = DifferentialJudgement::class(OutcomeClass::Miss);

    #[test]
    fn single_paths_that_differ_inside_the_baseline_set_are_no_hit() {
        // The swapped mutant's one path ends elsewhere than the baseline's one path, ...
        let options = options(PathMode::OnePath);
        let one_path = TargetNeeds {
            paths: Some(PathMode::OnePath),
            ..TargetNeeds::default()
        };
        let baseline =
            Side::new(&support::COIN, &one_path, &options).run("coin/flip.pgm", "flip(3)");
        let mutant =
            Side::new(&support::COIN_SWAPPED, &one_path, &options).run("coin/flip.pgm", "flip(3)");
        assert_eq!(baseline.leaves.len(), 1);
        assert_eq!(mutant.leaves.len(), 1);
        assert_ne!(baseline.leaves[0].state, mutant.leaves[0].state);
        // ... but inside the baseline's set of ends {3, 4}: no hit in either mode.
        for paths in BOTH_MODES {
            assert_eq!(flip(&support::COIN_SWAPPED, 3, paths), MISS, "{paths:?}");
        }
    }

    #[test]
    fn a_mutant_that_adds_an_end_is_a_hit() {
        for paths in BOTH_MODES {
            let judgement = flip(&support::COIN_KILL, 11, paths);
            assert_eq!(judgement.class, OutcomeClass::Hit, "{paths:?}");
            assert_eq!(judgement.killing_leaf, Some(0), "{paths:?}");
            // On the anchor the mutant is the baseline.
            assert_eq!(flip(&support::COIN_KILL, 3, paths), MISS, "{paths:?}");
        }
        // On all paths the mutant's single end 13 also lacks both baseline ends 11 and 12.
        assert!(
            flip(&support::COIN_KILL, 11, PathMode::AllPaths)
                .removed_end
                .is_some()
        );
    }

    #[test]
    fn a_mutant_that_removes_an_end_is_a_hit_on_all_paths_only() {
        assert_eq!(flip(&support::COIN_PRIO, 3, PathMode::OnePath), MISS);
        let judgement = flip(&support::COIN_PRIO, 3, PathMode::AllPaths);
        assert_eq!(judgement.class, OutcomeClass::Hit);
        assert_eq!(judgement.killing_leaf, None);
        assert!(judgement.removed_end.is_some());
    }

    #[test]
    fn an_added_end_holding_a_function_application_is_no_hit() {
        // flip(11) ends with opaque(11) on the mutant: clean, ceil-free, not data.
        for paths in BOTH_MODES {
            assert_eq!(
                flip(&support::COIN_FUNC, 11, paths),
                DifferentialJudgement::class(OutcomeClass::Unsupported),
                "{paths:?}"
            );
            assert_eq!(flip(&support::COIN_FUNC, 3, paths), MISS, "{paths:?}");
        }
    }

    #[test]
    fn a_depth_bound_below_the_run_makes_the_baseline_incomplete() {
        // count(3) ends only under max_depth 5; the mutant does the same as the baseline.
        let count = |max_depth| {
            judge_on(
                &support::COIN,
                &support::COIN_KILL,
                "coin/count.pgm",
                "count(3)",
                &CaseOptions {
                    max_depth: Some(max_depth),
                    ..CaseOptions::default()
                },
            )
        };
        for max_depth in [3, 4] {
            assert_eq!(
                count(max_depth),
                DifferentialJudgement::class(OutcomeClass::BaselineIncomplete),
                "max_depth {max_depth}"
            );
        }
        assert_eq!(count(5), MISS);
    }

    #[test]
    fn a_marked_baseline_end_makes_it_incomplete_and_an_unmarked_pair_kills() {
        // listKeys(1, 2): both sides read keys_list of a two-key map and carry the mark, and the
        // ends differ; the marked baseline end makes its set incomplete.
        for paths in BOTH_MODES {
            let program = support::CHOSEN.program("chosen/keys.pgm");
            assert_eq!(
                judge_on(
                    &support::CHOSEN,
                    &support::CHOSEN_KILL,
                    program.file,
                    program.text,
                    &options(paths)
                ),
                DifferentialJudgement::class(OutcomeClass::BaselineIncomplete),
                "{paths:?}"
            );
            // listKeys(1, 1): one key, no mark; the mutant ends with [1, 1], the baseline [1].
            let judgement = judge_on(
                &support::CHOSEN,
                &support::CHOSEN_KILL,
                program.file,
                "listKeys(1, 1)",
                &options(paths),
            );
            assert_eq!(judgement.class, OutcomeClass::Hit, "{paths:?}");
            assert_eq!(judgement.killing_leaf, Some(0), "{paths:?}");
        }
    }

    #[test]
    fn equal_digests_and_orders_are_equivalent() {
        let coin = support::COIN.compiled();
        let layout = support::COIN_LAYOUT.compiled();
        assert_eq!(coin.digest(), layout.digest());
        assert!(equivalent(&coin.definition(), &layout.definition()).expect("digests"));
        assert!(
            equivalent(
                &coin.definition_on(BackendRoute::FromDefinition),
                &layout.definition_on(BackendRoute::FromDefinition),
            )
            .expect("digests")
        );
    }

    #[test]
    fn unequal_digests_are_not_equivalent() {
        let coin = support::COIN.compiled().definition();
        for mutant in [
            &support::COIN_SWAPPED,
            &support::COIN_PRIO,
            &support::COIN_KILL,
            &support::COIN_FUNC,
        ] {
            assert!(
                !equivalent(&coin, &mutant.compiled().definition()).expect("digests"),
                "{}",
                mutant.file
            );
        }
    }

    #[test]
    fn equal_digests_with_another_rewrite_order_route_or_module_are_not_equivalent() {
        // FZ-FIX has no source pair with one digest and two orders (compiled KORE keeps the
        // sentence order), so the pair is the baseline and itself with a permuted order.
        let coin = support::COIN.compiled();
        let mut order = coin.artifacts.execution_rewrite_order.clone();
        assert!(order.len() >= 2, "COIN orders several rules: {order:?}");
        order.reverse();
        let permuted = coin.definition_on(BackendRoute::SourceExecution {
            execution_rewrite_order: order,
        });
        assert!(!equivalent(&coin.definition(), &permuted).expect("digests"));
        let kore_route = coin.definition_on(BackendRoute::FromDefinition);
        assert!(!equivalent(&coin.definition(), &kore_route).expect("digests"));
        assert!(!equivalent(&kore_route, &coin.definition()).expect("digests"));
        let mut other_main = coin.definition();
        other_main.main_module = "COIN-SYNTAX".to_owned();
        assert!(!equivalent(&coin.definition(), &other_main).expect("digests"));
    }

    #[test]
    fn a_macro_only_mutant_is_not_equivalent_on_either_route() {
        // Phase-1 review B1: the macro rule lives in macros.kore, so the execution digests (of
        // definition.kore without its origins) are equal. The source route's rewrite orders
        // happen to differ; the from-definition route has none, so there only the assembly
        // comparisons tell the two apart.
        let (mac, kill) = (support::MAC.compiled(), support::MAC_KILL.compiled());
        assert_eq!(mac.digest(), kill.digest());
        assert_ne!(mac.artifacts.macros_kore, kill.artifacts.macros_kore);
        assert!(!equivalent(&mac.definition(), &kill.definition()).expect("digests"));
        assert!(
            !equivalent(
                &mac.definition_on(BackendRoute::FromDefinition),
                &kill.definition_on(BackendRoute::FromDefinition),
            )
            .expect("digests")
        );
        // Each component on its own: the mutant's macros.kore alone, then its frontend alone.
        let mut macros_only = mac.definition();
        macros_only
            .macros_kore
            .clone_from(&kill.artifacts.macros_kore);
        assert!(!equivalent(&mac.definition(), &macros_only).expect("digests"));
        let mut frontend_only = mac.definition();
        frontend_only.frontend_definition = kill.definition().frontend_definition;
        assert!(!equivalent(&mac.definition(), &frontend_only).expect("digests"));
    }

    /// `text` with the first `Location(` attribute's start line moved by 1000.
    fn moved_location(text: &str) -> String {
        let at = text.find("\"Location(").expect("a Location attribute") + "\"Location(".len();
        format!("{}1000{}", &text[..at], &text[at..])
    }

    #[test]
    fn assembly_artifacts_are_compared_without_locations() {
        let mac = support::MAC.compiled().definition();
        let mut moved = mac.clone();
        moved.syntax_definition_kore = moved_location(&moved.syntax_definition_kore);
        moved.macros_kore = moved_location(&moved.macros_kore);
        assert_ne!(moved.syntax_definition_kore, mac.syntax_definition_kore);
        assert_ne!(moved.macros_kore, mac.macros_kore);
        assert!(equivalent(&mac, &moved).expect("digests"));
        // A production attribute other than a location is a difference.
        let mut formatted = mac.clone();
        formatted.syntax_definition_kore = formatted.syntax_definition_kore.replacen(
            "format{}(",
            "format{}(\"%c\"),\nformerly{}(",
            1,
        );
        assert_ne!(formatted.syntax_definition_kore, mac.syntax_definition_kore);
        assert!(!equivalent(&mac, &formatted).expect("digests"));
        // A text that does not parse is unequal to every other text, itself excepted.
        let mut broken = mac.clone();
        broken.macros_kore = "axiom".to_owned();
        assert!(!equivalent(&mac, &broken).expect("digests"));
        assert!(equivalent(&broken, &broken.clone()).expect("digests"));
    }

    #[test]
    fn configuration_variable_sorts_and_the_frontend_grammar_are_compared() {
        let coin = support::COIN.compiled().definition();
        let mut resorted = coin.clone();
        let pgm = resorted
            .configuration_variables
            .get_mut("PGM")
            .expect("COIN declares $PGM");
        *pgm = k_rust::kast::Sort::new("KItem");
        assert!(!equivalent(&coin, &resorted).expect("digests"));
        // COIN_PRIO's frontend differs from COIN's in a priority attribute; every compiled
        // artifact of `regrammared` is still COIN's.
        let mut regrammared = coin.clone();
        regrammared.frontend_definition = support::COIN_PRIO
            .compiled()
            .definition()
            .frontend_definition;
        assert!(!equivalent(&coin, &regrammared).expect("digests"));
        // COIN_LAYOUT's frontend differs from COIN's only in positions.
        let mut relaid = coin.clone();
        relaid.frontend_definition = support::COIN_LAYOUT
            .compiled()
            .definition()
            .frontend_definition;
        assert!(equivalent(&coin, &relaid).expect("digests"));
    }

    #[test]
    fn a_kill_against_a_baseline_end_that_is_not_data_is_unsupported() {
        // The roles of COIN_FUNC and COIN exchanged: on flip(11) the baseline ends with
        // opaque(11), an unevaluated total function, and the mutant with 11 and 12 (D15).
        for paths in BOTH_MODES {
            assert_eq!(
                judge_on(
                    &support::COIN_FUNC,
                    &support::COIN,
                    "coin/flip.pgm",
                    "flip(11)",
                    &options(paths)
                ),
                DifferentialJudgement::class(OutcomeClass::Unsupported),
                "{paths:?}"
            );
        }
    }

    /// Options without a work bound: a depth bound only (`effective_max_work` is `None`), under
    /// which the backend does not copy run facts onto every leaf.
    fn unbudgeted(paths: PathMode) -> CaseOptions {
        CaseOptions {
            paths,
            max_depth: Some(10),
            ..CaseOptions::default()
        }
    }

    /// Run `pick(1, 2)` on `fixture` as `side`'s plan asks under `options`.
    #[test]
    fn a_state_set_merge_moves_an_arrival_mark_to_the_result_list_which_the_judge_reads() {
        // DIAMOND: `go(5)` reaches `d(5)` through `b` and through `c`, and only `c` reads a
        // chosen value. Under path-set the `c` leaf carries the mark; under state-set the
        // arrivals merge into one unmarked `d(5)` leaf, and the mark is on the result's list,
        // which `run_facts_off_leaves` reads (docs/compatibility.md, "Marks in executions").
        let program = support::DIAMOND.program("diamond/go.pgm");
        // A depth bound instead of the default work bound: under `max_work` every leaf carries
        // every mark of the run (`docs/compatibility.md`, "Marks in executions").
        let options = CaseOptions {
            max_depth: Some(50),
            ..options(PathMode::AllPaths)
        };
        let needs = |state_set| TargetNeeds {
            paths: Some(PathMode::AllPaths),
            constructor_only: true,
            state_set,
            ..TargetNeeds::default()
        };
        let path_set =
            Side::new(&support::DIAMOND, &needs(false), &options).run(program.file, program.text);
        assert_eq!(path_set.leaves.len(), 2);
        assert_eq!(
            path_set
                .leaves
                .iter()
                .filter(|leaf| leaf
                    .unclean
                    .contains(&UncleanReason::ImplementationChosenValue))
                .count(),
            1
        );
        let state_set =
            Side::new(&support::DIAMOND, &needs(true), &options).run(program.file, program.text);
        assert_eq!(state_set.leaves.len(), 1);
        assert!(
            state_set.leaves[0].is_clean(),
            "{:?}",
            state_set.leaves[0].unclean
        );
        assert!(state_set.run_facts_off_leaves);
        assert!(state_set.work <= path_set.work);
        // As a baseline the merged result is incomplete; as a mutant it is no evidence.
        assert!(complete_ends(&state_set).is_none());
        assert!(no_evidence(&state_set));
    }

    fn pick(fixture: &'static Fixture, needs: &TargetNeeds, options: &CaseOptions) -> CaseResult {
        let program = support::VANISH.program("vanish/pick.pgm");
        Side::new(fixture, needs, options).run(program.file, program.text)
    }

    #[test]
    fn a_baseline_end_that_vanished_in_another_model_makes_the_baseline_incomplete() {
        // VANISH's `split` reads keys_list, divides by zero in k-rust's listing and vanishes
        // beside `plain` (end 0); the mutant ends with 10, which `split` gives in the other
        // listing (review B1, D16).
        for paths in BOTH_MODES {
            let options = unbudgeted(paths);
            assert_eq!(options.effective_max_work(), None);
            let plan = plan(&options);
            let baseline = pick(&support::VANISH, &plan.baseline, &options);
            assert!(
                baseline.run_facts_off_leaves,
                "{paths:?}: FZ-04 B3 end to end"
            );
            assert_eq!(baseline.leaves.len(), 1, "{paths:?}");
            assert!(
                baseline.leaves[0].is_clean(),
                "{paths:?}: no leaf carries the mark"
            );
            let mutant = pick(&support::VANISH_KILL, &plan.mutant, &options);
            assert_eq!(
                judge_pair(&baseline, &mutant, paths, false).expect("no engine defect"),
                DifferentialJudgement::class(OutcomeClass::BaselineIncomplete),
                "{paths:?}"
            );
        }
        // Under the default work bound the mark is on the leaf, with the same class.
        let program = support::VANISH.program("vanish/pick.pgm");
        for paths in BOTH_MODES {
            assert_eq!(
                judge_on(
                    &support::VANISH,
                    &support::VANISH_KILL,
                    program.file,
                    program.text,
                    &options(paths)
                ),
                DifferentialJudgement::class(OutcomeClass::BaselineIncomplete),
                "{paths:?}"
            );
        }
    }

    #[test]
    fn a_mutant_that_read_an_open_value_on_no_leaf_does_not_kill() {
        // The roles exchanged: the mutant's end 0 is outside the baseline's {10}, but the
        // mutant noted a chosen value on no leaf (condition 3).
        for paths in BOTH_MODES {
            let options = unbudgeted(paths);
            let plan = plan(&options);
            let baseline = pick(&support::VANISH_KILL, &plan.baseline, &options);
            let mutant = pick(&support::VANISH, &plan.mutant, &options);
            // One path carries the value on its leaf; all paths note it on no leaf.
            let marked = mutant.leaves.iter().any(|leaf| {
                leaf.unclean
                    .contains(&UncleanReason::ImplementationChosenValue)
            });
            assert_eq!(
                (marked, mutant.run_facts_off_leaves),
                (paths == PathMode::OnePath, paths == PathMode::AllPaths),
                "{paths:?}"
            );
            assert_eq!(
                judge_pair(&baseline, &mutant, paths, false).expect("no engine defect"),
                DifferentialJudgement::class(OutcomeClass::Unsupported),
                "{paths:?}"
            );
        }
    }

    #[test]
    fn unbudgeted_all_paths_runs_find_added_and_removed_ends() {
        let options = unbudgeted(PathMode::AllPaths);
        let flip = |mutant, n: i64| {
            judge_on(
                &support::COIN,
                mutant,
                "coin/flip.pgm",
                &format!("flip({n})"),
                &options,
            )
        };
        let added = flip(&support::COIN_KILL, 11);
        assert_eq!(
            added.witness().map(|(kind, _)| kind),
            Some(KillKind::AddedEnd)
        );
        let removed = flip(&support::COIN_PRIO, 3);
        assert_eq!(
            removed.witness().map(|(kind, _)| kind),
            Some(KillKind::RemovedEnd)
        );
        assert_eq!(flip(&support::COIN_SWAPPED, 3), MISS);
        assert_eq!(
            flip(&support::COIN_FUNC, 11),
            DifferentialJudgement::class(OutcomeClass::Unsupported)
        );
    }
}
