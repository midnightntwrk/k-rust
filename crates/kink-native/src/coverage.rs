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
//! [`TestCoverage`] collects the rewrite rules one run applied. Since re-pin lane 1 (L1-1) every
//! run collects k-rust's run coverage (`collect_coverage`) and carries no trace, so the rule ids
//! are the rewrite rules among the coverage's `applied` ids
//! ([`crate::execution::RunCoverage::applied_rewrites`]): every rewrite rule for which a step
//! built a successor or found the step undefined, over every state the run explored, the states
//! a state-set result merges away included. That is what the leaves' branch identities, their
//! `rewrite` and `remainder` trace entries and the rule of an undefined step gave before, which
//! is still the reading of an execution that carries no coverage ([`TestCoverage::of_execution`]
//! of a hand-built result). Equations (coverage's other `applied` ids) are left out, as before,
//! so an equation edit is still never covered by any test (ticket CS-T09; lane 2's L2-1 changes
//! that, with a new [`COVERAGE_DOMAIN`]).
//!
//! Coverage is a scheduling input only. No oracle, fold, status or score reads it: rule
//! identity enters scheduling, never an observation (SO-D1 = a).

use std::collections::{BTreeMap, BTreeSet};

use k_rust::backend::{BackendDiagnosticOutput, TraceEntry, TransitionIdOutput};
use k_rust::provenance::InputSpace;
use kink_patch::{SentenceOrigin, SentenceRef, Sha256Digest};
use serde_json::{Value, json};

use crate::ValidatedDefinition;
use crate::execution::{
    AdaptedExecution, AdaptedLeaf, BaselineLeaf, HaltClass, UndefinedStepRule, UnobservedExecution,
};

/// Domain of the canonical coverage list and its payload digest.
pub const COVERAGE_DOMAIN: &str = "kink/coverage/v1";

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
    /// diagnostic (leaf, candidate or remainder) and, for a run read from its trace, no trace
    /// entry of an unknown kind. A run that is not complete covers only what it explored.
    pub complete: bool,
    /// The committed rule identities (README corpus-scale 4.5).
    pub rule_ids: BTreeSet<String>,
    /// The baseline sentences behind `rule_ids`.
    pub sentences: BTreeSet<SentenceRef>,
    /// The ids of `rule_ids` with no baseline sentence, with the reason (generating pass or an
    /// `UNMAPPED_*` value).
    pub unmapped: BTreeMap<String, String>,
}

/// The fields of one leaf that coverage reads, for observed and unobserved leaves alike.
struct LeafView<'a> {
    halt: HaltClass,
    branch: &'a [TransitionIdOutput],
    trace: &'a [TraceEntry],
    undefined_rule: Option<&'a UndefinedStepRule>,
    diagnostics: [&'a [BackendDiagnosticOutput]; 2],
    candidate_diagnostics: &'a [Vec<BackendDiagnosticOutput>],
}

impl<'a> LeafView<'a> {
    fn adapted(leaf: &'a AdaptedLeaf) -> Self {
        Self {
            halt: leaf.halt,
            branch: &leaf.branch.identity,
            trace: &leaf.branch.trace,
            undefined_rule: leaf.undefined_rule.as_ref(),
            diagnostics: [&leaf.diagnostics, &leaf.remainder_diagnostics],
            candidate_diagnostics: &leaf.candidate_diagnostics,
        }
    }

    fn unobserved(leaf: &'a BaselineLeaf) -> Self {
        Self {
            halt: leaf.halt,
            branch: &leaf.branch,
            trace: &leaf.trace,
            undefined_rule: leaf.undefined_rule.as_ref(),
            diagnostics: [&leaf.diagnostics, &leaf.remainder_diagnostics],
            candidate_diagnostics: &leaf.candidate_diagnostics,
        }
    }

    fn complete(&self) -> bool {
        matches!(
            self.halt,
            HaltClass::Stuck | HaltClass::Trivial | HaltClass::Vacuous
        ) && self.diagnostics.iter().all(|list| list.is_empty())
            && self.candidate_diagnostics.iter().all(Vec::is_empty)
    }
}

/// Inserts the ids of one branch or trace entry: a `remainder:` entry lists the rules whose
/// negated conditions define the branch, joined by `,`.
fn insert_ids(ids: &mut BTreeSet<String>, entry: &str) {
    let entry = entry.strip_prefix("remainder:").unwrap_or(entry);
    ids.extend(
        entry
            .split(',')
            .filter(|id| !id.is_empty())
            .map(str::to_owned),
    );
}

impl TestCoverage {
    /// The coverage of a result or stepped run (for a stepped run, its `adapted` leaves): the
    /// rewrite rules of k-rust's run coverage when the run carries it, as every adapter run does;
    /// otherwise what its leaves' branches and traces name.
    #[must_use]
    pub fn of_execution(
        test_id: &str,
        execution: &AdaptedExecution,
        authors: &RuleAuthors,
    ) -> Self {
        let leaves = execution.leaves().iter().map(LeafView::adapted);
        match execution.coverage() {
            Some(coverage) => Self::of_run(
                test_id,
                execution.timed_out(),
                leaves,
                &coverage.applied_rewrites,
                authors,
            ),
            None => Self::of_leaves(test_id, execution.timed_out(), leaves, authors),
        }
    }

    /// The coverage an execution's leaves name, ignoring its run coverage: branch identities
    /// (a stepped run's), `rewrite` and `remainder` trace entries, and the rule of an undefined
    /// step. This is the reading before re-pin L1-1; it is kept for the coverage differential
    /// (equal rule ids from a stepped path set's branches and from a run's coverage) until lane
    /// 2's L2-1 retires it.
    #[must_use]
    pub fn of_branches(test_id: &str, execution: &AdaptedExecution, authors: &RuleAuthors) -> Self {
        Self::of_leaves(
            test_id,
            execution.timed_out(),
            execution.leaves().iter().map(LeafView::adapted),
            authors,
        )
    }

    /// The coverage of an unobserved run, as [`Self::of_execution`]; without run coverage its
    /// leaves carry no branch identity, so it reads the trace alone, which lists the same
    /// rewrite and remainder ids (M-C4).
    #[must_use]
    pub fn of_unobserved(
        test_id: &str,
        execution: &UnobservedExecution,
        authors: &RuleAuthors,
    ) -> Self {
        let leaves = execution.leaves.iter().map(LeafView::unobserved);
        match &execution.coverage {
            Some(coverage) => Self::of_run(
                test_id,
                execution.timed_out,
                leaves,
                &coverage.applied_rewrites,
                authors,
            ),
            None => Self::of_leaves(test_id, execution.timed_out, leaves, authors),
        }
    }

    /// The coverage of a run that collected k-rust's run coverage: `rule_ids` are the rewrite
    /// rules it applied, and the run is complete as [`Self::of_leaves`] reads it from its halts
    /// and diagnostics (it has no trace to read).
    fn of_run<'a>(
        test_id: &str,
        timed_out: bool,
        leaves: impl Iterator<Item = LeafView<'a>>,
        rule_ids: &BTreeSet<String>,
        authors: &RuleAuthors,
    ) -> Self {
        if timed_out {
            return Self::failed(test_id);
        }
        let mut complete = true;
        for leaf in leaves {
            complete &= leaf.complete();
        }
        Self::mapped(test_id, complete, rule_ids.clone(), authors)
    }

    /// A run that produced no execution (an adapter failure): incomplete, nothing covered.
    #[must_use]
    pub fn failed(test_id: &str) -> Self {
        Self {
            test_id: test_id.to_owned(),
            complete: false,
            rule_ids: BTreeSet::new(),
            sentences: BTreeSet::new(),
            unmapped: BTreeMap::new(),
        }
    }

    /// A timed-out run is incomplete and lists nothing: its leaves are not its path set, and
    /// where the watchdog stopped it depends on the host, so no id of it is recorded.
    fn of_leaves<'a>(
        test_id: &str,
        timed_out: bool,
        leaves: impl Iterator<Item = LeafView<'a>>,
        authors: &RuleAuthors,
    ) -> Self {
        if timed_out {
            return Self::failed(test_id);
        }
        let mut complete = true;
        let mut rule_ids = BTreeSet::new();
        for leaf in leaves {
            complete &= leaf.complete();
            for transition in leaf.branch {
                insert_ids(&mut rule_ids, &transition.rule);
            }
            for entry in leaf.trace {
                match entry.kind.as_str() {
                    "rewrite" | "remainder" => insert_ids(&mut rule_ids, &entry.unique_id),
                    // Simplifications and claims are not rule coverage; equations deciding a
                    // condition are not traced at all (CS-T09).
                    "simplification" | "claim" => {}
                    _ => complete = false,
                }
            }
            if let Some(rule) = leaf.undefined_rule {
                insert_ids(&mut rule_ids, &rule.id);
            }
        }
        Self::mapped(test_id, complete, rule_ids, authors)
    }

    /// `rule_ids` with the baseline sentences behind them.
    fn mapped(
        test_id: &str,
        complete: bool,
        rule_ids: BTreeSet<String>,
        authors: &RuleAuthors,
    ) -> Self {
        let mut sentences = BTreeSet::new();
        let mut unmapped = BTreeMap::new();
        for id in &rule_ids {
            match authors.get(id) {
                Some(Authorship::Sentences(authors)) => sentences.extend(authors.iter().cloned()),
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
            rule_ids,
            sentences,
            unmapped,
        }
    }

    /// The canonical value: `{"test_id","complete","rule_ids","sentences","unmapped"}`, every
    /// list sorted.
    #[must_use]
    pub fn value(&self) -> Value {
        json!({
            "test_id": self.test_id,
            "complete": self.complete,
            "rule_ids": self.rule_ids,
            "sentences": self
                .sentences
                .iter()
                .map(|at| json!({"module": at.module, "index": at.index}))
                .collect::<Vec<_>>(),
            "unmapped": self
                .unmapped
                .iter()
                .map(|(id, generated_by)| json!({"id": id, "generated_by": generated_by}))
                .collect::<Vec<_>>(),
        })
    }
}

/// Canonical JSON of a coverage list, in the given (manifest) order.
#[must_use]
pub fn coverage_text(coverage: &[TestCoverage]) -> String {
    kink_patch::canonical_json(&Value::Array(
        coverage.iter().map(TestCoverage::value).collect(),
    ))
}

/// `payload_digest("kink/coverage/v1", coverage_text(coverage))`.
#[must_use]
pub fn coverage_digest(coverage: &[TestCoverage]) -> Sha256Digest {
    kink_patch::payload_digest(COVERAGE_DOMAIN, coverage_text(coverage).as_bytes())
}
