//! The representative campaign set of flow packet F-01 (deliverable 3).
//!
//! `dedup.rs` runs every case through the evidence-sharing comparison (sharing on and
//! off, Full and FirstKill, complete runs and canonical report bytes), and
//! `selection.rs` runs every case through the CS-07 Prioritize theorem check. Each case
//! rebuilds, from the same fixtures, the campaign of the original test it names. That
//! original still runs in the per-commit gate with all of its assertions. The expected
//! statuses and killing test ids here are copied from it, except where a case says
//! otherwise (the Error case, which no original produces, the multi-generation
//! statuses and the Z3 column of G's ground campaign, all measured at 47e9285), so the
//! set also shows that it holds what it claims to hold. [`Coverage`] asserts that the
//! set contains every protected kill's campaign, every mutant status, a coupled mutant,
//! an admitted symbolic test in the running profile and a multi-generation campaign.
//!
//! The fixture builders are copies of the ones in `coupled.rs`, `end_to_end.rs` and
//! `multi_operator.rs`; they are copied rather than shared so that the fixtures and
//! assertions of those files stay as they were at 47e9285.
#![allow(dead_code)]

use std::collections::BTreeSet;
use std::time::Duration;

use k_rust::definition::AttributeKey;
use k_rust::kast::{Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::kore_sort;
use k_rust::kore::ast::Pattern;
use kink_campaign::{
    Campaign, CampaignFailure, CampaignFailureKind, CampaignRun, CrashPolicy, MutantStatus,
    OracleDeclaration, Projection, StateProjection, TestCase,
};
use kink_native::NativeValidator;
use kink_native::execution::ExecutionBudget;
use kink_native::step_events::{StepEventSpec, StepObservation};
use kink_patch::{
    Baseline, CandidateGeneration, Discovery, Edit, InsertPosition, Patch, SelectionPolicy,
    SiteSelector, TermRef, Universe, catalogue_v1, derive_sites, generate, resolve_universe,
    select,
};
use kink_pattern::{
    Atom, EventVocabulary, ExecutionTerminalKind, MatchMode, PatternArm, PatternPlan,
    PayloadClause, Relation,
};
use serde_json::Value;

use crate::{step_support, support};

/// The protected kills of the flow package (`work-package.toml` `protected_kills`).
pub const PROTECTED: [&str; 7] = [
    "K",
    "S1",
    "G",
    "C row 1b",
    "EI-D2=b",
    "AS7(a)",
    "digit audit",
];

/// Every mutant status the replaced copy suites could produce.
pub const STATUSES: [MutantStatus; 7] = [
    MutantStatus::Killed,
    MutantStatus::Survived,
    MutantStatus::Equivalent,
    MutantStatus::Invalid,
    MutantStatus::Timeout,
    MutantStatus::Unknown,
    MutantStatus::Error,
];

/// What the original test pins for a case, in the running profile.
pub enum Expected {
    /// The campaign is refused before any mutant runs, in both schedules.
    Refused(CampaignFailureKind),
    Run {
        /// Per mutant in id order: the Full status and killing test ids.
        full: Vec<(MutantStatus, Vec<&'static str>)>,
        /// Per mutant: the FirstKill status and killing test ids, where the original pins
        /// them.
        first_kill: Option<Vec<(MutantStatus, Vec<&'static str>)>>,
    },
    /// Per mutant in id order: the status in both schedules, where the original pins
    /// statuses only through other runs.
    Statuses(Vec<MutantStatus>),
}

/// One campaign of the representative set.
pub struct Case<'a> {
    /// Unique within the set.
    pub name: String,
    /// The original test whose campaign this is (`file.rs::test`).
    pub origin: &'static str,
    /// The protected kill this campaign belongs to, if any.
    pub protected: Option<&'static str>,
    pub campaign: Campaign<'a>,
    pub generations: Vec<CandidateGeneration<'a>>,
    pub expected: Expected,
    /// Fires a wall-clock bound by design. CS-07 excluded such fixtures from its theorem
    /// check (`selection.rs`), and so does the selection differential.
    pub wall_clock_bound: bool,
}

/// Checks the runs of one case (Full and FirstKill, the request's own runs) against
/// what its original test pins.
pub fn check_expected(
    case: &Case<'_>,
    full: &Result<CampaignRun, CampaignFailure>,
    first_kill: &Result<CampaignRun, CampaignFailure>,
) {
    let name = &case.name;
    match &case.expected {
        Expected::Refused(kind) => {
            for run in [full, first_kill] {
                assert_eq!(
                    run.as_ref().map(|_| ()).map_err(CampaignFailure::kind),
                    Err(*kind),
                    "{name}: refused campaign"
                );
            }
        }
        Expected::Run {
            full: expected_full,
            first_kill: expected_first,
        } => {
            let full = full.as_ref().unwrap_or_else(|f| panic!("{name}: {f:?}"));
            let first = first_kill
                .as_ref()
                .unwrap_or_else(|f| panic!("{name}: {f:?}"));
            assert_eq!(&observed(full), expected_full, "{name}: Full");
            if let Some(expected_first) = expected_first {
                assert_eq!(&observed(first), expected_first, "{name}: FirstKill");
            }
            assert_eq!(full.mutants.len(), first.mutants.len(), "{name}");
        }
        Expected::Statuses(expected) => {
            for (schedule, run) in [("Full", full), ("FirstKill", first_kill)] {
                let run = run.as_ref().unwrap_or_else(|f| panic!("{name}: {f:?}"));
                let statuses = run
                    .mutants
                    .iter()
                    .map(|mutant| mutant.report.status)
                    .collect::<Vec<_>>();
                assert_eq!(&statuses, expected, "{name}: {schedule}");
            }
        }
    }
}

/// Each mutant's status and killing test ids, in id order.
fn observed(run: &CampaignRun) -> Vec<(MutantStatus, Vec<&str>)> {
    run.mutants
        .iter()
        .map(|mutant| {
            (
                mutant.report.status,
                mutant
                    .report
                    .killing_test_ids
                    .iter()
                    .map(String::as_str)
                    .collect(),
            )
        })
        .collect()
}

/// What the set has been shown to contain, accumulated over its cases' Full runs.
#[derive(Default)]
pub struct Coverage {
    names: BTreeSet<String>,
    protected: BTreeSet<&'static str>,
    statuses: BTreeSet<String>,
    coupled: bool,
    symbolic: bool,
    multi_generation: bool,
}

impl Coverage {
    pub fn record(&mut self, case: &Case<'_>, full: &Result<CampaignRun, CampaignFailure>) {
        assert!(
            self.names.insert(case.name.clone()),
            "duplicate case {}",
            case.name
        );
        if let Some(protected) = case.protected {
            self.protected.insert(protected);
        }
        let Ok(run) = full else {
            return;
        };
        self.multi_generation |= case.generations.len() > 1 && !run.mutants.is_empty();
        for mutant in &run.mutants {
            self.statuses.insert(format!("{:?}", mutant.report.status));
            self.coupled |= mutant.written_sentences.len() > 1;
        }
        self.symbolic |= !run.mutants.is_empty()
            && case
                .campaign
                .tests
                .iter()
                .any(|test| !test.initial_state.variable_occurrences().is_empty());
    }

    /// Fails unless the set contains every element F-01 deliverable 3 lists.
    pub fn assert_complete(&self) {
        assert_eq!(
            self.protected,
            PROTECTED.into_iter().collect::<BTreeSet<_>>(),
            "every protected kill's campaign"
        );
        assert_eq!(
            self.statuses,
            STATUSES
                .iter()
                .map(|status| format!("{status:?}"))
                .collect::<BTreeSet<_>>(),
            "every mutant status"
        );
        assert!(self.coupled, "a coupled mutant");
        assert!(self.symbolic, "an admitted symbolic test in this profile");
        assert!(self.multi_generation, "a multi-generation campaign");
    }
}

/// Builds every case of the representative set in a fixed order and hands each to
/// `visit`. This is the one place that names the set.
pub fn representative_set(visit: &mut dyn FnMut(&Case<'_>)) {
    symmem_cases(visit);
    guarded_cases(visit);
    counter_cases(visit);
    timeout_case(visit);
}

// ---------------------------------------------------------------- shared builders

const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(30),
    max_simplification_iterations: 1000,
    max_depth: None,
    max_breadth: None,
};

fn normal(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Normal
}

fn app(symbol: &str, args: Vec<Pattern>) -> Pattern {
    support::app(&format!("Lbl{symbol}"), args)
}

fn nat(name: &str) -> Pattern {
    support::var(name, "SortNat")
}

fn z() -> Pattern {
    app("z", vec![])
}

fn s(pattern: Pattern) -> Pattern {
    app("s", vec![pattern])
}

fn addr(n: Pattern) -> Pattern {
    app("addr", vec![n])
}

fn whole_term() -> OracleDeclaration {
    OracleDeclaration::new(
        CrashPolicy::CompareIdentity,
        Projection::State(StateProjection::WholeTerm),
    )
    .expect("final")
}

fn case(id: &str, initial_state: Pattern, oracles: &[OracleDeclaration]) -> TestCase {
    TestCase {
        id: id.into(),
        initial_state,
        oracles: oracles.to_vec(),
    }
}

fn run(full: Vec<(MutantStatus, Vec<&'static str>)>) -> Expected {
    Expected::Run {
        full,
        first_kill: None,
    }
}

fn run_both(full: Vec<(MutantStatus, Vec<&'static str>)>) -> Expected {
    Expected::Run {
        first_kill: Some(full.clone()),
        full,
    }
}

fn term(baseline: &Baseline, rule: &str, path: &[u32]) -> Term {
    baseline
        .term(&TermRef::new(support::rule(baseline, rule), path))
        .expect("term")
        .clone()
}

fn exact(count: usize, arity: usize) -> SelectionPolicy {
    SelectionPolicy::Exact {
        expected_tuple_count: count,
        expected_tuple_arity: arity,
    }
}

/// The edit that replaces the term at `path` of `rule` by `replacement` (coupled.rs).
fn replaced(baseline: &Baseline, rule: &str, path: &[u32], replacement: Term) -> Edit {
    let at = TermRef::new(support::rule(baseline, rule), path);
    Edit::ReplaceTerm {
        expected: baseline.term(&at).expect("term").clone(),
        replacement,
        at,
    }
}

/// A one-candidate generation whose patch is `patch`, selected as one tuple of the exact
/// `sites` (coupled.rs `fixed`).
fn fixed<'b>(
    baseline: &'b Baseline,
    sites: &[(&str, &[u32])],
    operator: &str,
    patch: &Patch,
) -> CandidateGeneration<'b> {
    let discovery = sites
        .iter()
        .map(|(rule, path)| {
            derive_sites(
                baseline,
                operator,
                &[
                    SiteSelector::RuleLabel((*rule).into()),
                    SiteSelector::Path(path.to_vec()),
                ],
            )
            .expect("site")
        })
        .reduce(|left, right| left.join(&right, false).expect("join"))
        .expect("at least one site");
    assert!(discovery.exhaustive());
    let generation = select(&discovery, exact(1, sites.len()), 1)
        .expect("selection")
        .fold(operator, |_| patch.clone())
        .expect("generation");
    assert!(generation.scored());
    assert_eq!(generation.candidates().len(), 1);
    generation
}

/// The generation whose candidates are exactly `mutants`' patches, each at its own site
/// (end_to_end.rs `generation`).
fn generation<'b>(baseline: &'b Baseline, mutants: &[(TermRef, Patch)]) -> CandidateGeneration<'b> {
    let derive = |clauses: &[SiteSelector]| derive_sites(baseline, "site", clauses);
    let nothing = Discovery::empty(baseline, false, false);
    let discovery = mutants
        .iter()
        .map(|(site, _)| {
            let label = baseline
                .sentence(&site.sentence)
                .and_then(|rule| rule.attributes().string(AttributeKey::Label))
                .expect("a labelled rule");
            derive(&[
                SiteSelector::RuleLabel(label.to_owned()),
                SiteSelector::Path(site.path.0.clone()),
            ])
        })
        .try_fold(nothing, |all, next| all.union(&next.expect("no bindings")))
        .expect("one baseline and shape");
    assert!(discovery.exhaustive(), "declared by clauses");
    assert_eq!(discovery.tuples().len(), mutants.len());
    select(&discovery, SelectionPolicy::Each, mutants.len().max(1))
        .expect("selection")
        .fold("test", |origin| {
            let (_, patch) = mutants
                .iter()
                .find(|(site, _)| origin.site_tuple == [site.clone()])
                .expect("a mutant's site");
            patch.clone()
        })
        .expect("every patch edits its site's rule")
}

/// The mutant that replaces the term at `path` of `label` with `replacement`
/// (end_to_end.rs `replace`).
fn replace(baseline: &Baseline, label: &str, path: &[u32], replacement: Term) -> (TermRef, Patch) {
    let at = TermRef::new(support::rule(baseline, label), path);
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        expected: baseline.term(&at).expect("baseline term").clone(),
        at: at.clone(),
        replacement,
    }])
    .expect("one edit");
    (at, patch)
}

fn bool_token(value: &str) -> Term {
    Term::Token {
        token: value.to_owned(),
        sort: Sort::new("Bool"),
    }
}

fn pattern_with_sort(
    vocabulary: &EventVocabulary,
    first: &str,
    second: &str,
    relation: Relation,
    sort: &str,
) -> OracleDeclaration {
    let plan = PatternPlan::new(
        vocabulary,
        vec![("A".into(), kore_sort(sort))],
        vec![PatternArm {
            atoms: vec![first, second]
                .into_iter()
                .map(|constructor| Atom {
                    constructor: constructor.into(),
                    payload: vec![PayloadClause {
                        position: 0,
                        mode: if constructor == first {
                            MatchMode::Bind
                        } else {
                            MatchMode::Use
                        },
                        variable: "A".into(),
                    }],
                })
                .collect(),
            relations: vec![relation],
        }],
        None,
    )
    .expect("plan");
    OracleDeclaration::new(
        CrashPolicy::CompareIdentity,
        Projection::Pattern {
            plan,
            with_bindings: false,
        },
    )
    .expect("oracle")
}

/// One atom of `constructor` binding `variable` at payload `position` (coupled.rs `binds`).
fn binds(
    vocabulary: &EventVocabulary,
    constructor: &str,
    position: usize,
    variable: &str,
    sort: &str,
    with_bindings: bool,
) -> OracleDeclaration {
    let plan = PatternPlan::new(
        vocabulary,
        vec![(variable.into(), kore_sort(sort))],
        vec![PatternArm {
            atoms: vec![Atom {
                constructor: constructor.into(),
                payload: vec![PayloadClause {
                    position,
                    mode: MatchMode::Bind,
                    variable: variable.into(),
                }],
            }],
            relations: vec![],
        }],
        None,
    )
    .expect("plan");
    OracleDeclaration::new(
        CrashPolicy::CompareIdentity,
        Projection::Pattern {
            plan,
            with_bindings,
        },
    )
    .expect("oracle")
}

/// A pattern oracle whose one atom is `constructor` (end_to_end.rs `occurs`).
fn occurs(vocabulary: &EventVocabulary, constructor: &str) -> OracleDeclaration {
    let plan = PatternPlan::new(
        vocabulary,
        Vec::new(),
        vec![PatternArm {
            atoms: vec![Atom {
                constructor: constructor.to_owned(),
                payload: Vec::new(),
            }],
            relations: Vec::new(),
        }],
        None,
    )
    .expect("plan");
    OracleDeclaration::new(
        CrashPolicy::CompareIdentity,
        Projection::Pattern {
            plan,
            with_bindings: false,
        },
    )
    .expect("pattern declaration")
}

/// Swaps the variables `from` and `to` (coupled.rs `swap_names`).
fn swap_names(term: &mut Term, from: &str, to: &str) -> usize {
    match term {
        Term::Variable { name, .. } if name == from => {
            *name = to.into();
            1
        }
        Term::Variable { name, .. } if name == to => {
            *name = from.into();
            1
        }
        Term::Rewrite { left, right } => swap_names(left, from, to) + swap_names(right, from, to),
        Term::As { pattern, alias } => swap_names(pattern, from, to) + swap_names(alias, from, to),
        Term::Sequence(items) => items
            .iter_mut()
            .map(|item| swap_names(item, from, to))
            .sum(),
        Term::Apply { arguments, .. } => arguments
            .iter_mut()
            .map(|argument| swap_names(argument, from, to))
            .sum(),
        Term::Annotated { term, .. } => swap_names(term, from, to),
        _ => 0,
    }
}

/// The edit that applies `swap_names(from, to)` to the term at `path` of `rule`.
fn renamed(baseline: &Baseline, rule: &str, path: &[u32], from: &str, to: &str) -> Edit {
    let at = TermRef::new(support::rule(baseline, rule), path);
    let expected = baseline.term(&at).expect("term").clone();
    let mut replacement = expected.clone();
    assert!(
        swap_names(&mut replacement, from, to) > 0,
        "{rule} {path:?}"
    );
    Edit::ReplaceTerm {
        at,
        expected,
        replacement,
    }
}

// ---------------------------------------------------------------- symmem.k (coupled.rs)

/// `write(write_address, write_value); load(load_address, load_value); halt`.
fn state(
    write_address: Pattern,
    write_value: Pattern,
    load_address: Pattern,
    load_value: Pattern,
) -> Pattern {
    support::initial_state(
        app(
            "seq",
            vec![
                app("write", vec![write_address, write_value]),
                app(
                    "seq",
                    vec![
                        app("load", vec![load_address, load_value]),
                        app("halt", vec![]),
                    ],
                ),
            ],
        ),
        "SortProg",
    )
}

/// coupled.rs `tests`: ground-shared, sym-shared, sym-distinct, sym-clash.
fn symmem_tests(vocabulary: &EventVocabulary) -> Vec<TestCase> {
    let oracles = vec![
        whole_term(),
        pattern_with_sort(
            vocabulary,
            "memoryWrite",
            "memoryLoad",
            Relation::NextEvent,
            "SortAddress",
        ),
        pattern_with_sort(
            vocabulary,
            "memoryWrite",
            "memoryLoad",
            Relation::EventuallyAfter,
            "SortAddress",
        ),
        pattern_with_sort(
            vocabulary,
            "memoryLoad",
            "memoryFree",
            Relation::NextEvent,
            "SortAddress",
        ),
    ];
    [
        ("ground-shared", state(addr(z()), s(z()), addr(z()), s(z()))),
        (
            "sym-shared",
            state(addr(nat("X")), nat("V"), addr(nat("X")), nat("W")),
        ),
        (
            "sym-distinct",
            state(addr(nat("X")), nat("V"), addr(nat("Y")), nat("W")),
        ),
        (
            "sym-clash",
            state(addr(z()), nat("V"), addr(s(nat("Y"))), nat("W")),
        ),
    ]
    .into_iter()
    .map(|(id, program)| case(id, program, &oracles))
    .collect()
}

struct Symmem {
    validator: NativeValidator,
    vocabulary: EventVocabulary,
    observation: Vec<StepEventSpec>,
    tests: Vec<TestCase>,
}

impl Symmem {
    fn new(whole: bool) -> Self {
        let validator = NativeValidator::bind(support::load("symmem.k"), CompileOptions::default());
        let observation = step_support::symmem(whole);
        let vocabulary = StepObservation::vocabulary_of(&observation).expect("vocabulary");
        let tests = symmem_tests(&vocabulary);
        Self {
            validator,
            vocabulary,
            observation,
            tests,
        }
    }

    fn campaign<'a>(&'a self, tests: &'a [TestCase]) -> Campaign<'a> {
        Campaign {
            validator: &self.validator,
            module: "SYMMEM",
            observation: &self.observation,
            classify: &normal,
            tests,
            budget: BUDGET,
        }
    }
}

/// coupled.rs `release_after_write`.
fn release_after_write(baseline: &Baseline) -> CandidateGeneration<'_> {
    let discovery = derive_sites(
        baseline,
        "write-continuation",
        &[
            SiteSelector::RuleLabel("SYMMEM.write".into()),
            SiteSelector::Path(vec![0, 1]),
        ],
    )
    .expect("site");
    assert!(discovery.exhaustive());
    let generation = select(&discovery, exact(1, 1), 1)
        .expect("selection")
        .fold("release-after-write", |origin| {
            let at = origin.discovery_tuples[0].sites[0].at.clone();
            let address = term(baseline, "SYMMEM.write", &[0, 0, 0, 0]);
            let continuation = baseline.term(&at).expect("continuation").clone();
            Patch::new(vec![Edit::ReplaceTerm {
                at,
                expected: continuation.clone(),
                replacement: Term::apply(
                    "seq",
                    vec![Term::apply("free", vec![address]), continuation],
                ),
            }])
            .expect("patch")
        })
        .expect("generation");
    assert!(generation.scored());
    assert_eq!(generation.candidates().len(), 1);
    generation
}

/// coupled.rs `coupled` (`coupled_with_stale_load(.., false)`): `value` false is the
/// release-after-access mutant of K, true the coherent value representation.
fn coupled(baseline: &Baseline, value: bool) -> CandidateGeneration<'_> {
    let path = if value {
        vec![0, 0, 0, 1]
    } else {
        vec![0, 0, 0, 0]
    };
    let binding = if value { "V" } else { "A" };
    let sort = if value { "Nat" } else { "Address" };
    let derive = |role: &str, rule: &str| {
        derive_sites(
            baseline,
            role,
            &[
                SiteSelector::RuleLabel(rule.into()),
                SiteSelector::Path(path.clone()),
                SiteSelector::Sort(Sort::new(sort)),
                SiteSelector::Bind(binding.into()),
            ],
        )
        .expect("site")
    };
    let discovery = derive("write", "SYMMEM.write")
        .join(&derive("load", "SYMMEM.load"), false)
        .expect("join");
    assert!(discovery.exhaustive());
    let operator = if value {
        "coupled-value-representation"
    } else {
        "release-after-access"
    };
    let generation = select(&discovery, exact(1, 2), 1)
        .expect("selection")
        .fold(operator, |origin| {
            let tuple = &origin.discovery_tuples[0];
            let bound = tuple.bindings.get(binding).expect("binding").clone();
            Patch::new(
                tuple
                    .sites
                    .iter()
                    .map(|site| {
                        let at = if value {
                            site.at.clone()
                        } else {
                            TermRef::new(site.at.sentence.clone(), [0, 1])
                        };
                        let expected = baseline.term(&at).expect("term").clone();
                        let replacement = if value {
                            Term::apply("s", vec![bound.clone()])
                        } else {
                            Term::apply(
                                "seq",
                                vec![Term::apply("free", vec![bound.clone()]), expected.clone()],
                            )
                        };
                        Edit::ReplaceTerm {
                            at,
                            expected,
                            replacement,
                        }
                    })
                    .collect(),
            )
            .expect("patch")
        })
        .expect("generation");
    assert!(generation.scored());
    assert_eq!(generation.candidates().len(), 1);
    generation
}

fn symmem_cases(visit: &mut dyn FnMut(&Case<'_>)) {
    use MutantStatus::{Killed, Survived, Unknown};
    for whole in [true, false] {
        let fixture = Symmem::new(whole);
        let baseline = fixture.validator.baseline();
        visit(&Case {
            name: format!("S1 whole={whole}"),
            origin: "coupled.rs::single_site_release_is_killed_by_its_trace",
            protected: Some("S1"),
            campaign: fixture.campaign(&fixture.tests),
            generations: vec![release_after_write(baseline)],
            expected: run(vec![(
                Killed,
                vec!["ground-shared", "sym-shared", "sym-distinct"],
            )]),
            wall_clock_bound: false,
        });
        visit(&Case {
            name: format!("K whole={whole}"),
            origin: "coupled.rs::coupled_release_is_one_mutant_killed_by_its_trace",
            protected: Some("K"),
            campaign: fixture.campaign(&fixture.tests),
            generations: vec![coupled(baseline, false)],
            expected: run(vec![(
                Killed,
                if whole {
                    vec!["ground-shared", "sym-shared", "sym-distinct"]
                } else {
                    vec!["ground-shared", "sym-shared", "sym-distinct", "sym-clash"]
                },
            )]),
            wall_clock_bound: false,
        });
    }

    let fixture = Symmem::new(true);
    let baseline = fixture.validator.baseline();
    visit(&Case {
        name: "Unknown: coherent value representation".into(),
        origin: "coupled.rs::coherent_value_representation_is_not_killed",
        protected: None,
        campaign: fixture.campaign(&fixture.tests),
        generations: vec![coupled(baseline, true)],
        expected: run(vec![(Unknown, vec![])]),
        wall_clock_bound: false,
    });
    visit(&Case {
        name: "Unknown: coherent value representation, ground test".into(),
        origin: "coupled.rs::coherent_value_representation_is_not_killed",
        protected: None,
        campaign: fixture.campaign(&fixture.tests[..1]),
        generations: vec![coupled(baseline, true)],
        expected: run(vec![(Survived, vec![])]),
        wall_clock_bound: false,
    });

    // C row 1b: audit A6, all three of its campaigns.
    let valued = [case(
        "ground-shared-value",
        fixture.tests[0].initial_state.clone(),
        &[binds(
            &fixture.vocabulary,
            "memoryWrite",
            1,
            "V",
            "SortNat",
            true,
        )],
    )];
    visit(&Case {
        name: "C row 1b: valued".into(),
        origin: "coupled.rs::audit_a6_name_kept_meaning_change_is_not_killed",
        protected: Some("C row 1b"),
        campaign: fixture.campaign(&valued),
        generations: vec![coupled(baseline, true)],
        expected: run(vec![(Survived, vec![])]),
        wall_clock_bound: false,
    });
    let zero_valued = [case(
        "ground-zero-value",
        state(addr(z()), z(), addr(z()), z()),
        &[
            fixture.tests[0].oracles[0].clone(),
            binds(&fixture.vocabulary, "memoryWrite", 1, "V", "SortNat", true),
        ],
    )];
    visit(&Case {
        name: "C row 1b: zero valued".into(),
        origin: "coupled.rs::audit_a6_name_kept_meaning_change_is_not_killed",
        protected: Some("C row 1b"),
        campaign: fixture.campaign(&zero_valued),
        generations: vec![coupled(baseline, true)],
        expected: run(vec![(Killed, vec!["ground-zero-value"])]),
        wall_clock_bound: false,
    });
    let guarded = Guarded::new();
    let guarded_baseline = guarded.validator.baseline();
    let swap = Patch::new(vec![
        renamed(guarded_baseline, "GUARDEDMEM.write", &[0], "A", "V"),
        renamed(guarded_baseline, "GUARDEDMEM.write", &[1], "A", "V"),
    ])
    .expect("patch");
    let distinct_values = [case(
        "ground-distinct-values",
        state(
            addr(support::int(1)),
            support::int(5),
            addr(support::int(1)),
            support::int(7),
        ),
        &guarded.tests[1].oracles,
    )];
    visit(&Case {
        name: "C row 1b: guarded name swap".into(),
        origin: "coupled.rs::audit_a6_name_kept_meaning_change_is_not_killed",
        protected: Some("C row 1b"),
        campaign: guarded.campaign(&distinct_values),
        generations: vec![fixed(
            guarded_baseline,
            &[("GUARDEDMEM.write", &[0])],
            "swap-names",
            &swap,
        )],
        expected: run(vec![(Survived, vec![])]),
        wall_clock_bound: false,
    });

    // AS7(a): the load operation replaced by the write operation.
    let load_as_write = Patch::new(vec![replaced(
        baseline,
        "SYMMEM.load",
        &[0, 0, 0],
        term(baseline, "SYMMEM.write", &[0, 0, 0]),
    )])
    .expect("patch");
    visit(&Case {
        name: "AS7(a): load as write".into(),
        origin: "coupled.rs::audit_ks_as7_anchoring_fails_closed",
        protected: Some("AS7(a)"),
        campaign: fixture.campaign(&fixture.tests),
        generations: vec![fixed(
            baseline,
            &[("SYMMEM.load", &[0, 0, 0])],
            "load-as-write",
            &load_as_write,
        )],
        expected: run(vec![(Killed, vec!["ground-shared"])]),
        wall_clock_bound: false,
    });
}

// ---------------------------------------------------------------- guardedmem.k (coupled.rs)

struct Guarded {
    validator: NativeValidator,
    observation: Vec<StepEventSpec>,
    tests: Vec<TestCase>,
}

impl Guarded {
    fn new() -> Self {
        let validator =
            NativeValidator::bind(support::load("guardedmem.k"), CompileOptions::default());
        let observation = step_support::guardedmem(true);
        let vocabulary = StepObservation::vocabulary_of(&observation).expect("vocabulary");
        let oracles = vec![
            whole_term(),
            pattern_with_sort(
                &vocabulary,
                "memoryWrite",
                "memoryLoad",
                Relation::EventuallyAfter,
                "SortInt",
            ),
        ];
        let guarded_state = |write_address: Pattern, load_address: Pattern| {
            state(
                addr(write_address),
                support::var("V", "SortInt"),
                addr(load_address),
                support::var("W", "SortInt"),
            )
        };
        let tests = vec![
            case(
                "sym-guarded",
                guarded_state(support::var("X", "SortInt"), support::var("Y", "SortInt")),
                &oracles,
            ),
            case(
                "ground-guarded",
                guarded_state(support::int(1), support::int(1)),
                &oracles,
            ),
        ];
        Self {
            validator,
            observation,
            tests,
        }
    }

    fn campaign<'a>(&'a self, tests: &'a [TestCase]) -> Campaign<'a> {
        Campaign {
            validator: &self.validator,
            module: "GUARDEDMEM",
            observation: &self.observation,
            classify: &normal,
            tests,
            budget: BUDGET,
        }
    }
}

/// coupled.rs `inverted_load_sign`: the guards of `load` and `loadFault` exchanged.
fn inverted_load_sign(baseline: &Baseline) -> CandidateGeneration<'_> {
    let derive = |role: &str, rule: &str| {
        derive_sites(
            baseline,
            role,
            &[
                SiteSelector::RuleLabel(rule.into()),
                SiteSelector::Path(vec![0, 0, 0, 0, 0]),
                SiteSelector::Sort(Sort::new("Int")),
                SiteSelector::Bind("A".into()),
            ],
        )
        .expect("site")
    };
    let discovery = derive("load", "GUARDEDMEM.load")
        .join(&derive("load-fault", "GUARDEDMEM.loadFault"), false)
        .expect("join");
    assert!(discovery.exhaustive());
    let generation = select(&discovery, exact(1, 2), 1)
        .expect("selection")
        .fold("inverted-load-sign", |origin| {
            Patch::new(
                origin.discovery_tuples[0]
                    .sites
                    .iter()
                    .map(|site| {
                        let other =
                            if site.at.sentence == support::rule(baseline, "GUARDEDMEM.load") {
                                "GUARDEDMEM.loadFault"
                            } else {
                                "GUARDEDMEM.load"
                            };
                        let at = TermRef::new(site.at.sentence.clone(), [1]);
                        Edit::ReplaceTerm {
                            expected: baseline.term(&at).expect("requires").clone(),
                            replacement: term(baseline, other, &[1]),
                            at,
                        }
                    })
                    .collect(),
            )
            .expect("patch")
        })
        .expect("generation");
    assert!(generation.scored());
    assert_eq!(generation.candidates().len(), 1);
    generation
}

fn guarded_cases(visit: &mut dyn FnMut(&Case<'_>)) {
    use MutantStatus::Killed;
    let fixture = Guarded::new();
    let baseline = fixture.validator.baseline();
    let refused = Expected::Refused(CampaignFailureKind::BaselineOracleFailed);
    visit(&Case {
        name: "G".into(),
        origin: "coupled.rs::inverted_load_sign_is_killed_by_a_solver_unsat",
        protected: Some("G"),
        campaign: fixture.campaign(&fixture.tests),
        generations: vec![inverted_load_sign(baseline)],
        expected: if cfg!(feature = "z3") {
            Expected::Run {
                full: vec![(Killed, vec!["sym-guarded", "ground-guarded"])],
                first_kill: Some(vec![(Killed, vec!["sym-guarded"])]),
            }
        } else {
            Expected::Refused(CampaignFailureKind::BaselineOracleFailed)
        },
        wall_clock_bound: false,
    });
    // The original runs the ground campaign without Z3 only (Full); the Z3 column and
    // FirstKill of this one-test campaign are measured.
    visit(&Case {
        name: "G: ground test".into(),
        origin: "coupled.rs::inverted_load_sign_is_killed_by_a_solver_unsat",
        protected: Some("G"),
        campaign: fixture.campaign(&fixture.tests[1..]),
        generations: vec![inverted_load_sign(baseline)],
        expected: run_both(vec![(Killed, vec!["ground-guarded"])]),
        wall_clock_bound: false,
    });
    let int = |name: &str| support::var(name, "SortInt");
    let digit_tests = [
        case(
            "sym-guarded-1",
            state(addr(int("X1")), int("V1"), addr(int("Y1")), int("W1")),
            &fixture.tests[0].oracles,
        ),
        fixture.tests[1].clone(),
    ];
    visit(&Case {
        name: "digit audit".into(),
        origin: "coupled.rs::audit_vi_digit_suffixed_initial_names_are_stable",
        protected: Some("digit audit"),
        campaign: fixture.campaign(&digit_tests),
        generations: vec![inverted_load_sign(baseline)],
        expected: if cfg!(feature = "z3") {
            Expected::Run {
                full: vec![(Killed, vec!["sym-guarded-1", "ground-guarded"])],
                first_kill: Some(vec![(Killed, vec!["sym-guarded-1"])]),
            }
        } else {
            refused
        },
        wall_clock_bound: false,
    });
}

// ---------------------------------------------------------------- counter.k (end_to_end.rs, multi_operator.rs)

/// `counter(z, s(s(s(z))))`.
fn counter_state() -> Pattern {
    support::initial_state(app("counter", vec![z(), s(s(s(z())))]), "SortCounter")
}

fn bool_value(value: &str) -> Pattern {
    Pattern::DomainValue {
        sort: kore_sort("SortBool"),
        value: value.into(),
    }
}

/// `choose(true)`.
fn choose_state() -> Pattern {
    support::initial_state(app("choose", vec![bool_value("true")]), "SortControl")
}

fn counter_campaign<'a>(
    validator: &'a NativeValidator,
    observation: &'a [StepEventSpec],
    classify: &'a dyn Fn(&Pattern) -> ExecutionTerminalKind,
    tests: &'a [TestCase],
) -> Campaign<'a> {
    Campaign {
        validator,
        module: "COUNTER",
        observation,
        classify,
        tests,
        budget: BUDGET,
    }
}

/// Whether `term` contains `selected(false)`.
fn selects_false(term: &Pattern) -> bool {
    match term {
        Pattern::Application { symbol, arguments } if symbol.name == "Lblselected" => {
            arguments == &[bool_value("false")]
        }
        _ => k_rust::kore::walk::children(term)
            .into_iter()
            .any(selects_false),
    }
}

/// Ends in `selected(false)` count as semantic crashes; everything else is normal.
fn false_selection_is_a_crash(term: &Pattern) -> ExecutionTerminalKind {
    if selects_false(term) {
        ExecutionTerminalKind::SemanticCrash
    } else {
        ExecutionTerminalKind::Normal
    }
}

/// multi_operator.rs `code`: an unknown attribute on `increment` (rejected by k-rust).
fn attribute_code(b: &Baseline) -> CandidateGeneration<'_> {
    let discovery = derive_sites(
        b,
        "site",
        &[
            SiteSelector::RuleLabel("COUNTER.increment".into()),
            SiteSelector::Path(vec![0]),
        ],
    )
    .expect("site");
    select(&discovery, SelectionPolicy::Each, 1)
        .expect("selection")
        .fold("code", |_| {
            Patch::new(vec![Edit::AddAttribute {
                at: support::rule(b, "COUNTER.increment"),
                key: "foo".into(),
                value: Value::String(String::new()),
            }])
            .expect("patch")
        })
        .expect("generation")
}

fn counter_cases(visit: &mut dyn FnMut(&Case<'_>)) {
    use MutantStatus::{Equivalent, Error, Invalid, Killed, Survived};
    let validator = NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
    let baseline = validator.baseline();
    let specs = step_support::counter(true);
    let vocabulary = StepObservation::vocabulary_of(&specs).expect("vocabulary");

    // EI-D2=b: increment by two keeps the final result and is killed by its pattern.
    let increment = || Atom {
        constructor: "increment".to_owned(),
        payload: Vec::new(),
    };
    let twice = OracleDeclaration::new(
        CrashPolicy::CompareIdentity,
        Projection::Pattern {
            plan: PatternPlan::new(
                &vocabulary,
                Vec::new(),
                vec![PatternArm {
                    atoms: vec![increment(), increment()],
                    relations: vec![Relation::NextEvent],
                }],
                None,
            )
            .expect("plan"),
            with_bindings: false,
        },
    )
    .expect("pattern declaration");
    let two = [case(
        "two",
        support::initial_state(app("counter", vec![z(), s(s(z()))]), "SortCounter"),
        &[whole_term(), occurs(&vocabulary, "increment"), twice],
    )];
    let doubled = |path: &[u32]| {
        let at = TermRef::new(support::rule(baseline, "COUNTER.increment"), path);
        let expected = baseline.term(&at).expect("baseline term").clone();
        Edit::ReplaceTerm {
            replacement: Term::apply("s", vec![expected.clone()]),
            expected,
            at,
        }
    };
    let by_two = (
        TermRef::new(support::rule(baseline, "COUNTER.increment"), [0]),
        Patch::new(vec![doubled(&[0, 0, 1]), doubled(&[0, 1, 0])]).expect("two edits"),
    );
    visit(&Case {
        name: "EI-D2=b".into(),
        origin: "end_to_end.rs::counter_campaign_kills_by_pattern_with_unchanged_final_result_over_a_proved_difference",
        protected: Some("EI-D2=b"),
        campaign: counter_campaign(&validator, &specs, &normal, &two),
        generations: vec![generation(baseline, &[by_two])],
        expected: run_both(vec![(Killed, vec!["two"])]),
        wall_clock_bound: false,
    });

    // Invalid, Killed and Survived in one campaign.
    let t1_t2 = [
        case(
            "t1",
            counter_state(),
            &[whole_term(), occurs(&vocabulary, "increment")],
        ),
        case(
            "t2",
            choose_state(),
            &[whole_term(), occurs(&vocabulary, "branchTaken")],
        ),
    ];
    let mutants = [
        (
            TermRef::new(support::rule(baseline, "COUNTER.increment"), [0]),
            Patch::new(vec![Edit::AddAttribute {
                at: support::rule(baseline, "COUNTER.increment"),
                key: "foo".to_owned(),
                value: Value::String(String::new()),
            }])
            .expect("one edit"),
        ),
        replace(
            baseline,
            "COUNTER.increment",
            &[0, 1, 0],
            term(baseline, "COUNTER.increment", &[0, 1, 0, 0]),
        ),
        replace(baseline, "COUNTER.branch", &[1], bool_token("false")),
        replace(baseline, "COUNTER.fallback", &[0, 1, 0], bool_token("true")),
    ];
    visit(&Case {
        name: "Invalid, Killed, Survived: counter final result".into(),
        origin: "end_to_end.rs::counter_campaign_kills_by_final_result_and_not_by_rule_identity",
        protected: None,
        campaign: counter_campaign(&validator, &specs, &normal, &t1_t2),
        generations: vec![generation(baseline, &mutants)],
        expected: Expected::Run {
            full: vec![
                (Invalid, vec![]),
                (Killed, vec!["t1"]),
                (Survived, vec![]),
                (Survived, vec![]),
            ],
            first_kill: Some(vec![
                (Invalid, vec![]),
                (Killed, vec!["t1"]),
                (Survived, vec![]),
                (Survived, vec![]),
            ]),
        },
        wall_clock_bound: false,
    });

    // Equivalent: an anonymous clone of `increment`.
    let rule = support::rule(baseline, "COUNTER.increment");
    let mut clone = baseline.sentence(&rule).expect("rule").clone();
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
        clone.attributes_mut().remove(key.as_str());
    }
    let insert = Patch::new(vec![Edit::InsertSentence {
        position: InsertPosition::After(rule.clone()),
        ordinal: 0,
        sentence: clone,
    }])
    .expect("patch");
    let increment_test = [case("increment", counter_state(), &[whole_term()])];
    visit(&Case {
        name: "Equivalent: anonymous clone".into(),
        origin: "end_to_end.rs::anonymous_clone_of_observed_rule_is_equivalent",
        protected: None,
        campaign: counter_campaign(&validator, &specs, &normal, &increment_test),
        generations: vec![generation(baseline, &[(TermRef::new(rule, [0]), insert)])],
        expected: run(vec![(Equivalent, vec![])]),
        wall_clock_bound: false,
    });

    // Error: no replaced copy produced it (handoff F-01), so the set adds this campaign.
    // The baseline ends normally in `selected(true)`; the mutant ends in `selected(false)`,
    // which the classifier calls a semantic crash. Under CompareIdentity a crash against a
    // normal value is Incomparable, which folds to Error, never to a kill.
    let choose = [case("choose", choose_state(), &[whole_term()])];
    let select_false = replace(baseline, "COUNTER.branch", &[0, 1, 0], bool_token("false"));
    visit(&Case {
        name: "Error: crash against a normal result".into(),
        origin: "representative/mod.rs (constructed for F-01; status rule of campaign.rs)",
        protected: None,
        campaign: counter_campaign(&validator, &[], &false_selection_is_a_crash, &choose),
        generations: vec![generation(baseline, &[select_false])],
        expected: run_both(vec![(Error, vec![])]),
        wall_clock_bound: false,
    });

    // Multi-generation: three catalogue specs and a code operator over one campaign.
    let universe = resolve_universe(baseline, &Universe::v1());
    let mut generations = catalogue_v1()
        .into_iter()
        .filter(|spec| matches!(spec.id(), "cond-true" | "cond-false" | "delete-rule"))
        .map(|spec| generate(baseline, &universe, &spec, usize::MAX).expect("generation"))
        .collect::<Vec<_>>();
    assert_eq!(generations.len(), 3);
    generations.push(attribute_code(baseline));
    let multi_specs = step_support::counter(true);
    let multi_vocabulary = StepObservation::vocabulary_of(&multi_specs).expect("vocabulary");
    let multi_tests = [
        case(
            "counter",
            counter_state(),
            &[occurs(&multi_vocabulary, "increment")],
        ),
        case(
            "choose",
            choose_state(),
            &[occurs(&multi_vocabulary, "branchTaken")],
        ),
    ];
    let mut multi_budget = counter_campaign(&validator, &multi_specs, &normal, &multi_tests);
    multi_budget.budget.max_depth = Some(32);
    visit(&Case {
        name: "multi-generation: counter catalogue and code".into(),
        origin: "multi_operator.rs::mixed_generations_equal_single_runs_and_replay_manifest_specs",
        protected: None,
        campaign: multi_budget,
        generations,
        // Measured at 47e9285 in both profiles (THROWAWAY_STATUS census, handoff F-01):
        // cond-true, cond-false and delete-rule over counter.k, then the rejected attribute.
        expected: Expected::Statuses(vec![
            Survived, Killed, Survived, Survived, Killed, Survived, Survived, Invalid,
        ]),
        wall_clock_bound: false,
    });
}

// ---------------------------------------------------------------- nd.k (end_to_end.rs)

fn timeout_case(visit: &mut dyn FnMut(&Case<'_>)) {
    let validator = NativeValidator::bind(support::load("nd.k"), CompileOptions::default());
    let baseline = validator.baseline();
    let tests = [case(
        "mid1",
        support::initial_state(support::app("Lblmid1", vec![]), "SortS"),
        &[whole_term()],
    )];
    // l2: mid1 => spin, and spin => spin forever.
    let spin = replace(
        baseline,
        "ND.l2",
        &[0, 1],
        term(baseline, "ND.spin", &[0, 1]),
    );
    visit(&Case {
        name: "Timeout: nonterminating mutant".into(),
        origin: "end_to_end.rs::nonterminating_mutant_is_a_timeout",
        protected: None,
        campaign: Campaign {
            validator: &validator,
            module: "ND",
            observation: &[],
            classify: &normal,
            tests: &tests,
            budget: ExecutionBudget {
                time: Duration::from_secs(2),
                ..BUDGET
            },
        },
        generations: vec![generation(baseline, &[spin])],
        expected: run(vec![(MutantStatus::Timeout, vec![])]),
        wall_clock_bound: true,
    });
}
