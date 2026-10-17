//! Rule coverage of a test's run and the map from compiled rule identities to the sentences
//! that wrote them (semantic-input ticket SI-T04).
//!
//! [`RuleAuthors`] reads k-rust's typed sentence provenance
//! (`CompiledKoreArtifacts::sentence_provenance`): each emitted rule or claim `UNIQUE_ID` lists
//! the `InputSpace::Compile` addresses of the input sentences behind it, which index the very
//! loaded definition a [`ValidatedDefinition`] compiled, so they are kink's [`SentenceRef`]s.
//! On a mutant side each address is mapped back to the baseline sentence it came from through
//! the mutant's sentence origins; an inserted sentence has no baseline author.
//!
//! [`TestCoverage`] is the coverage of one run, read from k-rust's run coverage
//! (`collect_coverage`, [`crate::execution::RunCoverage`]), which every adapter run collects. Since
//! re-pin lane 2 (L2-1, [`COVERAGE_DOMAIN`] `kink/coverage/v2`; v3 since L2-1-tail) it holds
//! every compiled id k-rust records, rewrite rules and equations alike:
//! - `rule_ids` (reached) are k-rust's `matched` ids, which include `applied`: every rule and
//!   equation whose condition the run began to decide for an instance whose left-hand side
//!   matched, whatever the verdict, and every one the run applied;
//! - `applied_ids` (fired) are k-rust's `applied` ids: every rule for which a step built a
//!   successor or found the step undefined, and every equation whose instance gave a result.
//!
//! Both cover every state the run explored, the states a state-set result merges away included.
//! Before L2-1 (`kink/coverage/v1`) the rule ids were the rewrite rules among `applied` only, so
//! an equation edit was never covered (ticket CS-T09), and an execution without run coverage was
//! read from its leaves' branch identities and traces. Such an execution (only a hand-built
//! result has one) now has no coverage signal: it is incomplete and lists nothing.
//!
//! Some compiled ids have no recording site in k-rust, so no run ever names them: `smt-lemma`
//! axioms, `non-executable` axioms (k-rust internalizes executable axioms only; re-pin
//! L2-1-tail), macro and alias rules (`macros_kore`), and claims; builtin hooks are not axioms at
//! all (k-rust `coverage::RunCoverage`). [`coverage_domain`] is the set of ids that do have one. A
//! rule none of whose ids is in it has no coverage signal and is never reported as uncovered.
//!
//! The sets are no over-approximation of what can affect a result: a higher-priority rule or
//! equation whose left-hand side did not match is absent, though its failure is what lets a lower
//! one fire, and an equation behind one that applies is never scanned (findings D-03). Coverage is
//! a scheduling and report input only. No oracle, fold, status or score reads it: rule identity
//! enters scheduling, never an observation (SO-D1 = a). Scheduling only orders tests; it never
//! leaves one out (kink-campaign `selection`).

use std::collections::{BTreeMap, BTreeSet};

use k_rust::backend::BackendDiagnosticOutput;
use k_rust::kore::{
    ast::{Pattern, Sentence},
    parser::parse_definition,
};
use k_rust::names::KoreAttribute;
use k_rust::provenance::InputSpace;
use kink_patch::{SentenceOrigin, SentenceRef, Sha256Digest};
use serde_json::{Value, json};

use crate::ValidatedDefinition;
use crate::execution::{
    AdaptedExecution, AdaptedLeaf, BaselineLeaf, HaltClass, RunCoverage, UnobservedExecution,
};

/// Domain of the canonical coverage list and its payload digest, and the version of how coverage
/// is read. Coverage orders the schedule, so under `FirstKill` it can decide which test kills;
/// kink's semantics identity names it (kink-campaign `identity`). v2 (re-pin L2-1): `rule_ids`
/// are k-rust's `matched` ids, equations included, and `applied_ids` its `applied` ids; v1's
/// `rule_ids` were the rewrite rules among `applied`. v3 (re-pin L2-1-tail): kink-campaign's
/// `selection` witnesses a rewrite rule edit of its `requires` and its right-hand side by
/// `matched` (v2: by `applied`), so under `FirstKill` such a mutant's first killing test can
/// differ from v2's; [`coverage_domain`] leaves out `non-executable` axioms; kink-flow orders its
/// programs by the edit's witness.
pub const COVERAGE_DOMAIN: &str = "kink/coverage/v3";

/// Unmapped reason of an id whose every author is a sentence the mutant's patch inserted.
pub const UNMAPPED_INSERTED: &str = "inserted";
/// Unmapped reason of an id the side's sentence provenance does not list.
pub const UNMAPPED_NO_PROVENANCE: &str = "no-provenance";
/// Unmapped reason of an id one of whose Compile addresses names no sentence of the compiled
/// definition, or (on a mutant side) a sentence without an origin. Never expected; tests pin
/// that no testdata definition or campaign mutant has one.
pub const UNMAPPED_UNRESOLVED: &str = "unresolved-address";
/// Unmapped reason of an id with neither an input address nor a generating pass.
pub const UNMAPPED_UNATTRIBUTED: &str = "unattributed";

/// Who wrote one compiled rule identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Authorship {
    /// The baseline sentences behind the id: every Compile address of the id, mapped back to
    /// the baseline on a mutant side. Equal-content sentences share one id, so a set.
    Sentences(BTreeSet<SentenceRef>),
    /// No baseline sentence: the generating pass (`generate-sort-predicate-rules`, ...) or one
    /// of the `UNMAPPED_*` reasons of this module.
    Unmapped(String),
}

/// One unresolvable Compile address of an id.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct UnresolvedAddress {
    pub id: String,
    pub module: String,
    pub index: u32,
}

/// The authors of every emitted rule identity of one compiled side.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuleAuthors {
    authors: BTreeMap<String, Authorship>,
    unresolved: BTreeSet<UnresolvedAddress>,
}

impl RuleAuthors {
    /// Maps every id of the side's sentence provenance to its authors. A baseline's addresses
    /// are its own sentences; a mutant's are mapped back through its origins, and an address
    /// of an inserted sentence contributes no author.
    #[must_use]
    pub fn of(validated: &ValidatedDefinition) -> Self {
        let definition = validated.definition();
        let exists = |module: &str, index: u32| {
            definition
                .modules
                .iter()
                .find(|candidate| candidate.name == module)
                .and_then(|module| module.local_sentences.get(usize::try_from(index).ok()?))
                .is_some()
        };
        let mut authors = BTreeMap::new();
        let mut unresolved = BTreeSet::new();
        for (id, provenance) in &validated.artifacts().sentence_provenance {
            let mut sentences = BTreeSet::new();
            let mut inserted = false;
            let mut missing = false;
            for address in provenance
                .input_addresses
                .iter()
                .filter(|address| address.input == InputSpace::Compile)
            {
                let at = SentenceRef::new(address.module.clone(), address.index);
                let origin = if exists(&address.module, address.index) {
                    match validated.origins() {
                        None => Some(at.clone()),
                        Some(origins) => match origins.get(&at) {
                            Some(SentenceOrigin::Baseline(baseline)) => Some(baseline.clone()),
                            Some(SentenceOrigin::Inserted { .. }) => {
                                inserted = true;
                                None
                            }
                            None => {
                                missing = true;
                                None
                            }
                        },
                    }
                } else {
                    missing = true;
                    None
                };
                if let Some(baseline) = origin {
                    sentences.insert(baseline);
                } else if missing {
                    unresolved.insert(UnresolvedAddress {
                        id: id.clone(),
                        module: at.module,
                        index: at.index,
                    });
                }
            }
            let authorship = if missing {
                Authorship::Unmapped(UNMAPPED_UNRESOLVED.to_owned())
            } else if !sentences.is_empty() {
                Authorship::Sentences(sentences)
            } else if inserted {
                Authorship::Unmapped(UNMAPPED_INSERTED.to_owned())
            } else if let Some(pass) = provenance.generated_by {
                Authorship::Unmapped(pass.as_str().to_owned())
            } else {
                Authorship::Unmapped(UNMAPPED_UNATTRIBUTED.to_owned())
            };
            authors.insert(id.clone(), authorship);
        }
        Self {
            authors,
            unresolved,
        }
    }

    /// The authors of `id`, or `None` when the side's provenance does not list it.
    #[must_use]
    pub fn get(&self, id: &str) -> Option<&Authorship> {
        self.authors.get(id)
    }

    /// Every id with its authors, in id order.
    pub fn iter(&self) -> impl Iterator<Item = (&str, &Authorship)> {
        self.authors
            .iter()
            .map(|(id, authors)| (id.as_str(), authors))
    }

    /// The ids whose authors include `at`, in id order.
    pub fn ids_of<'a>(&'a self, at: &'a SentenceRef) -> impl Iterator<Item = &'a str> + 'a {
        self.iter().filter_map(move |(id, authors)| match authors {
            Authorship::Sentences(sentences) if sentences.contains(at) => Some(id),
            Authorship::Sentences(_) | Authorship::Unmapped(_) => None,
        })
    }

    /// Compile addresses that name no sentence of the compiled definition or, on a mutant
    /// side, a sentence without an origin. Their ids are `unresolved-address`.
    #[must_use]
    pub const fn unresolved(&self) -> &BTreeSet<UnresolvedAddress> {
        &self.unresolved
    }
}

/// The rule coverage of one test's run.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TestCoverage {
    pub test_id: String,
    /// The run did not time out and every leaf is `Stuck`, `Trivial` or `Vacuous` with no
    /// diagnostic (leaf, candidate or remainder). A run that is not complete (a work-bound,
    /// depth-bound or undecided leaf, a diagnostic) covers only what it explored before it
    /// stopped, which depends on where it stopped.
    pub complete: bool,
    /// The reached compiled ids (README corpus-scale 4.5): k-rust's `matched`, which includes
    /// `applied`.
    pub rule_ids: BTreeSet<String>,
    /// The fired compiled ids: k-rust's `applied`, a subset of `rule_ids`.
    pub applied_ids: BTreeSet<String>,
    /// The baseline sentences behind `rule_ids`.
    pub sentences: BTreeSet<SentenceRef>,
    /// The baseline sentences behind `applied_ids`.
    pub applied_sentences: BTreeSet<SentenceRef>,
    /// The ids of `rule_ids` with no baseline sentence, with the reason (generating pass or an
    /// `UNMAPPED_*` value).
    pub unmapped: BTreeMap<String, String>,
}

/// Whether one leaf leaves its run complete, for observed and unobserved leaves alike.
fn leaf_complete(
    halt: HaltClass,
    diagnostics: [&[BackendDiagnosticOutput]; 2],
    candidate_diagnostics: &[Vec<BackendDiagnosticOutput>],
) -> bool {
    matches!(
        halt,
        HaltClass::Stuck | HaltClass::Trivial | HaltClass::Vacuous
    ) && diagnostics.iter().all(|list| list.is_empty())
        && candidate_diagnostics.iter().all(Vec::is_empty)
}

fn adapted_complete(leaf: &AdaptedLeaf) -> bool {
    leaf_complete(
        leaf.halt,
        [&leaf.diagnostics, &leaf.remainder_diagnostics],
        &leaf.candidate_diagnostics,
    )
}

fn unobserved_complete(leaf: &BaselineLeaf) -> bool {
    leaf_complete(
        leaf.halt,
        [&leaf.diagnostics, &leaf.remainder_diagnostics],
        &leaf.candidate_diagnostics,
    )
}

impl TestCoverage {
    /// The coverage of a result or stepped run (for a stepped run, its `adapted` leaves), from
    /// k-rust's run coverage, which every adapter run carries. An execution without it has no
    /// coverage signal ([`Self::failed`]).
    #[must_use]
    pub fn of_execution(
        test_id: &str,
        execution: &AdaptedExecution,
        authors: &RuleAuthors,
    ) -> Self {
        Self::of_run(
            test_id,
            execution.timed_out(),
            execution.leaves().iter().all(adapted_complete),
            execution.coverage(),
            authors,
        )
    }

    /// The coverage of an unobserved run, as [`Self::of_execution`].
    #[must_use]
    pub fn of_unobserved(
        test_id: &str,
        execution: &UnobservedExecution,
        authors: &RuleAuthors,
    ) -> Self {
        Self::of_run(
            test_id,
            execution.timed_out,
            execution.leaves.iter().all(unobserved_complete),
            execution.coverage.as_ref(),
            authors,
        )
    }

    /// A timed-out run is incomplete and lists nothing: k-rust answers its cancellation with an
    /// error, so it carries no coverage, and where the watchdog stopped it depends on the host.
    /// A run without run coverage lists nothing either.
    fn of_run(
        test_id: &str,
        timed_out: bool,
        complete: bool,
        coverage: Option<&RunCoverage>,
        authors: &RuleAuthors,
    ) -> Self {
        let Some(coverage) = coverage.filter(|_| !timed_out) else {
            return Self::failed(test_id);
        };
        let mut sentences = BTreeSet::new();
        let mut applied_sentences = BTreeSet::new();
        let mut unmapped = BTreeMap::new();
        for id in &coverage.matched {
            match authors.get(id) {
                Some(Authorship::Sentences(authors)) => {
                    sentences.extend(authors.iter().cloned());
                    if coverage.applied.contains(id) {
                        applied_sentences.extend(authors.iter().cloned());
                    }
                }
                Some(Authorship::Unmapped(reason)) => {
                    unmapped.insert(id.clone(), reason.clone());
                }
                None => {
                    unmapped.insert(id.clone(), UNMAPPED_NO_PROVENANCE.to_owned());
                }
            }
        }
        Self {
            test_id: test_id.to_owned(),
            complete,
            rule_ids: coverage.matched.clone(),
            applied_ids: coverage.applied.clone(),
            sentences,
            applied_sentences,
            unmapped,
        }
    }

    /// A run that produced no execution (an adapter failure), or no coverage signal: incomplete,
    /// nothing covered.
    #[must_use]
    pub fn failed(test_id: &str) -> Self {
        Self {
            test_id: test_id.to_owned(),
            complete: false,
            rule_ids: BTreeSet::new(),
            applied_ids: BTreeSet::new(),
            sentences: BTreeSet::new(),
            applied_sentences: BTreeSet::new(),
            unmapped: BTreeMap::new(),
        }
    }

    /// The canonical value: `{"test_id","complete","rule_ids","applied_ids","sentences",
    /// "applied_sentences","unmapped"}`, every list sorted.
    #[must_use]
    pub fn value(&self) -> Value {
        let sentences = |sentences: &BTreeSet<SentenceRef>| {
            sentences
                .iter()
                .map(|at| json!({"module": at.module, "index": at.index}))
                .collect::<Vec<_>>()
        };
        json!({
            "test_id": self.test_id,
            "complete": self.complete,
            "rule_ids": self.rule_ids,
            "applied_ids": self.applied_ids,
            "sentences": sentences(&self.sentences),
            "applied_sentences": sentences(&self.applied_sentences),
            "unmapped": self
                .unmapped
                .iter()
                .map(|(id, generated_by)| json!({"id": id, "generated_by": generated_by}))
                .collect::<Vec<_>>(),
        })
    }
}

/// The coverage domain of a compiled side: the ids of its axioms that k-rust's run coverage can
/// name, which are every `UNIQUE_ID` axiom of `definition_kore` except `smt-lemma` and
/// `non-executable` axioms. A claim, a macro or alias rule (`macros_kore`), an `smt-lemma` axiom
/// and a `non-executable` axiom have no recording site (k-rust `coverage::RunCoverage`; k-rust
/// internalizes only executable axioms, so no run matches or applies a `non-executable` one;
/// re-pin L2-1-tail). Unparsable KORE gives the empty set, so every rule then has no coverage
/// signal rather than being uncovered.
#[must_use]
pub fn coverage_domain(validated: &ValidatedDefinition) -> BTreeSet<String> {
    axiom_ids(validated, |attributes| {
        !attributes.iter().any(|attribute| {
            named(attribute, KoreAttribute::SmtLemma)
                || named(attribute, KoreAttribute::NonExecutable)
        })
    })
}

/// The ids of the `non-executable` axioms of a compiled side's `definition_kore`: k-rust never
/// runs them, so they are outside [`coverage_domain`] (re-pin L2-1-tail). Unparsable KORE gives
/// the empty set.
#[must_use]
pub fn non_executable_ids(validated: &ValidatedDefinition) -> BTreeSet<String> {
    axiom_ids(validated, |attributes| {
        attributes
            .iter()
            .any(|attribute| named(attribute, KoreAttribute::NonExecutable))
    })
}

fn named(pattern: &Pattern, attribute: KoreAttribute) -> bool {
    matches!(pattern, Pattern::Application { symbol, .. } if symbol.name == attribute.as_str())
}

/// The `UNIQUE_ID` of every axiom of `definition_kore` whose attributes `keep` accepts.
fn axiom_ids(
    validated: &ValidatedDefinition,
    keep: impl Fn(&[Pattern]) -> bool,
) -> BTreeSet<String> {
    let Ok(definition) = parse_definition(&validated.artifacts().definition_kore) else {
        return BTreeSet::new();
    };
    definition
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| match sentence {
            Sentence::Axiom { attributes, .. } if keep(&attributes.0) => {
                attributes.0.iter().find_map(|attribute| match attribute {
                    Pattern::Application { symbol, arguments }
                        if symbol.name == KoreAttribute::UniqueId.as_str() =>
                    {
                        match arguments.as_slice() {
                            [Pattern::String(id)] => id.as_utf8().ok().map(str::to_owned),
                            _ => None,
                        }
                    }
                    _ => None,
                })
            }
            _ => None,
        })
        .collect()
}

/// Canonical JSON of a coverage list, in the given (manifest) order.
#[must_use]
pub fn coverage_text(coverage: &[TestCoverage]) -> String {
    kink_patch::canonical_json(&Value::Array(
        coverage.iter().map(TestCoverage::value).collect(),
    ))
}

/// `payload_digest(COVERAGE_DOMAIN, coverage_text(coverage))`.
#[must_use]
pub fn coverage_digest(coverage: &[TestCoverage]) -> Sha256Digest {
    kink_patch::payload_digest(COVERAGE_DOMAIN, coverage_text(coverage).as_bytes())
}
