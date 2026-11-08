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
//! re-pin lane 2 (L2-1, [`COVERAGE_DOMAIN`] `kink/coverage/v2`; v3 since L2-1-tail, v4 since
//! a rewrite rule edit is witnessed by `applied` only when it is confined to its right-hand side
//! or `ensures`) it holds every compiled id k-rust records, rewrite rules and equations alike.
//! Each set is named by the predicate it holds, as in k-rust, kink-flow and krs (kink-flow
//! README, "Coverage predicates"):
//! - `rule_ids` are k-rust's `matched` ids, which include `applied`: every rule and equation
//!   whose condition the run began to decide for an instance whose left-hand side matched,
//!   whatever the verdict, and every one the run applied; `sentences` are the baseline sentences
//!   behind them, which kink-flow's `matched_by` lists;
//! - `applied_ids` are k-rust's `applied` ids: every rule for which a step built a successor or
//!   found the step undefined, and every equation whose instance gave a result;
//!   `applied_sentences` are the baseline sentences behind them.
//!
//! `fired_sentences` (KINK-R4) are the baseline sentences the run fired, kink-flow's derived
//! predicate: a rewrite rule among k-rust's `committed` ids, whose step some explored path takes
//! (a successor the step's own normalization showed defined), and an equation among `applied`,
//! whose instance gave a result. A rewrite candidate rolled back because its successor was
//! undefined, and an undefined step's rule, are applied but not committed: no path takes them,
//! so they are not fired. Nor is the step a `cut-point` leaf proposes (a run that stops before a
//! rule, [`crate::execution::StopRules`]): the step built its successor, so its rule is applied,
//! but the run stopped before taking it, so k-rust does not commit it and no path of the run
//! takes it ([`crate::execution::StopProposal`]); a run whose count of stop events is past that
//! arrival takes the step and commits it. kink-flow's `fired_by` reads them; they are not part of
//! the canonical value ([`TestCoverage::value`]), which schedules read, so [`COVERAGE_DOMAIN`] did
//! not move.
//!
//! Both cover every state the run explored, the states a state-set result merges away included.
//!
//! [`TestCoverage::bindings`] are what the run's fired instances bound (k-rust
//! `coverage.bindings`, which a baseline result run that records coverage asks for,
//! [`crate::execution::ResultRun::bindings`]), by the baseline sentence behind each axiom: the
//! requested symbols that were the head of an operand the axiom reads, the values of the
//! selected template binders, and the alternatives of an axiom with several that a fired
//! instance took. [`syntax_facts`] gives, from the definition alone, the symbols each sentence's
//! axioms, and each alternative of an axiom with several, inspect (a non-variable position of a
//! left-hand side) and build (one of a right-hand side), and the constructors of the
//! definition. Together they say which productions a fired
//! instance touched, which kink-flow's syntax family reads. Neither is part of the canonical
//! value ([`TestCoverage::value`]), which schedules read, so [`COVERAGE_DOMAIN`] did not move.
//!
//! [`TestCoverage::windows`] are the rule windows the run took (k-rust `coverage.windows`, which
//! a baseline result run whose tables hold a depth above 1 asks for,
//! [`crate::execution::DefinitionTables::with_depth`]), by the baseline sentence behind each
//! step's rule, and [`TestCoverage::depth`] the depth asked for; [`may_follow`] gives, from the
//! definition alone, the graph of which authored rewrite rule may take the step after which,
//! whose walks are the windows a run can take. At the same depth the bindings hold the syntax
//! paths the fired instances touched ([`SentenceBindings::paths`], k-rust `bindings.paths`), and
//! [`grammar_graph`] gives, from the definition alone, which named symbol may stand at which
//! argument of which, whose walks are the paths a run can record. None of these is part of the
//! canonical value, so [`COVERAGE_DOMAIN`] did not move.
//!
//! A run is complete ([`TestCoverage::complete`]) when it explored every state its system reaches
//! from its initial state, so its coverage is a fact of the run and not of where it was cut
//! short. A run with stop rules computes the truncated system of its rules, the system that ends
//! a path at every step of a selected rule (see [`crate::bridge`]): a clean `cut-point` or
//! `terminal` leaf has no successor there, as a stuck leaf has none in the definition's own
//! system, so it leaves its run complete as a stuck leaf does, and the coverage of such a run is
//! the coverage of that truncated system. A run to a later arrival at a stop than the first is a
//! run of the system truncated at that arrival, whose earlier arrivals are steps of its paths that
//! the run commits, so its coverage is that system's. Before stop rules every stop leaf was
//! refused by the adapter, so no coverage value computed under [`COVERAGE_DOMAIN`]
//! `kink/coverage/v4` held one, and admitting them changes none of those values: the domain did
//! not move, and a stopped run is told from an unstopped one by its request
//! (`kink-native/execution-request/v3`).
//! Before L2-1 (`kink/coverage/v1`) the rule ids were the rewrite rules among `applied` only, so
//! an equation edit was never in a run's coverage (ticket CS-T09), and an execution without run coverage was
//! read from its leaves' branch identities and traces. Such an execution (only a hand-built
//! result has one) now has no coverage signal: it is incomplete and lists nothing.
//!
//! Some compiled ids have no recording site in k-rust, so no run ever names them: `smt-lemma`
//! axioms, `non-executable` axioms (k-rust internalizes executable axioms only; re-pin
//! L2-1-tail), macro and alias rules (`macros_kore`), and claims; builtin hooks are not axioms at
//! all (k-rust `coverage::RunCoverage`). [`coverage_domain`] is the set of ids that do have one. A
//! rule none of whose ids is in it has no coverage signal and is never reported as unmatched.
//!
//! The sets are no over-approximation of what can affect a result: a higher-priority rule or
//! equation whose left-hand side did not match is absent, though its failure is what lets a lower
//! one fire, and an equation behind one that applies is never scanned (findings D-03). Coverage is
//! a scheduling and report input only. No oracle, fold, status or score reads it: rule identity
//! enters scheduling, never an observation (SO-D1 = a). Scheduling only orders tests; it never
//! leaves one out (kink-campaign `selection`).

use std::collections::{BTreeMap, BTreeSet};

mod grammar;
mod may_follow;

pub use grammar::{GrammarGraph, grammar_graph};
pub(crate) use may_follow::unifies;
pub use may_follow::{MayFollow, may_follow};

use k_rust::backend::{AxiomGuardOutput, BackendDiagnosticOutput, BindingsOutput};
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
/// programs by the edit's witness. v4: kink-campaign's `selection` witnesses every rewrite rule
/// edit that is not confined to its right-hand side or `ensures` (its left-hand side, an
/// attribute, a deletion, one it cannot pair) by `matched` (v3: by `applied`), so under
/// `FirstKill` such a mutant's first killing test can differ from v3's.
pub const COVERAGE_DOMAIN: &str = "kink/coverage/v4";

/// Every earlier [`COVERAGE_DOMAIN`], oldest first: a declaration naming one is refused as
/// retired rather than malformed (kink-corpus manifests). A bump moves the old domain here; a
/// unit test requires `v1` up to the version before the current one (review L2-1-tail-1 D4).
pub const RETIRED_COVERAGE_DOMAINS: [&str; 3] =
    ["kink/coverage/v1", "kink/coverage/v2", "kink/coverage/v3"];

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
    /// The ids one of whose input sentences is a `context` or a `strict` or `seqstrict`
    /// production: the heating and cooling rules the compile generates from them (and a
    /// `hybrid` production's result equations), which [`TestCoverage::strictness`] records by id.
    strictness: BTreeSet<String>,
}

/// The skeleton of every guarded sentence's condition, without a run: for each baseline
/// sentence behind a rewrite rule or function equation of `definition` whose `requires` is not
/// empty (the axioms a run that collects guard outcomes names, [`crate::execution::ResultRun::guards`]),
/// each such axiom's nodes as a run that entered it would report them, none reached (k-rust
/// `guard_skeletons`), by the sentence `authors` names. A run reports a guard only once it
/// entered it; this gives the nodes of every guard, so that what a guard can show is read from
/// the definition alone. A sentence one of whose axioms has an atom that cannot be encoded is
/// listed in [`GuardSkeletons::unreadable`] with the reason instead, and has no skeletons: a
/// part of its condition would be missing, and a run that entered that axiom could not report
/// it either.
#[must_use]
pub fn guard_skeletons(
    definition: &k_rust_backend::definition::BackendDefinition,
    authors: &RuleAuthors,
) -> GuardSkeletons {
    let axioms = crate::execution::guarded_unique_ids(definition);
    let mut skeletons = GuardSkeletons::default();
    let sentences_of = |axiom: &str| match authors.get(axiom) {
        Some(Authorship::Sentences(sentences)) => sentences.iter().cloned().collect::<Vec<_>>(),
        _ => Vec::new(),
    };
    // One call reads every axiom; only when it fails is each axiom read alone, to tell the
    // axioms whose atoms cannot be encoded from the others.
    let guards = match k_rust::backend::guard_skeletons(definition, &axioms) {
        Ok(guards) => guards,
        Err(_) => {
            let mut guards = Vec::new();
            for axiom in &axioms {
                let one = BTreeSet::from([axiom.clone()]);
                match k_rust::backend::guard_skeletons(definition, &one) {
                    Ok(read) => guards.extend(read),
                    Err(error) => {
                        for sentence in sentences_of(axiom) {
                            skeletons.unreadable.entry(sentence).or_insert_with(|| {
                                format!(
                                    "the skeleton of the condition of axiom {axiom} cannot be \
                                     read: {error}"
                                )
                            });
                        }
                    }
                }
            }
            guards
        }
    };
    for guard in guards {
        for sentence in sentences_of(&guard.axiom) {
            if !skeletons.unreadable.contains_key(&sentence) {
                skeletons
                    .by_sentence
                    .entry(sentence)
                    .or_default()
                    .push(guard.clone());
            }
        }
    }
    let unreadable = skeletons.unreadable.keys().cloned().collect::<Vec<_>>();
    for sentence in unreadable {
        skeletons.by_sentence.remove(&sentence);
    }
    skeletons
}

/// The skeletons of the guarded sentences' conditions ([`guard_skeletons`]).
#[derive(Clone, Debug, Default)]
pub struct GuardSkeletons {
    /// Each guarded sentence's skeletons, one per axiom behind it.
    pub by_sentence: BTreeMap<SentenceRef, Vec<AxiomGuardOutput<Pattern>>>,
    /// The guarded sentences with an axiom whose skeleton cannot be read, each with why.
    pub unreadable: BTreeMap<SentenceRef, String>,
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
        let mut strictness = BTreeSet::new();
        for (id, provenance) in &validated.artifacts().sentence_provenance {
            let mut sentences = BTreeSet::new();
            let mut inserted = false;
            let mut missing = false;
            for address in provenance
                .input_addresses
                .iter()
                .filter(|address| address.input == InputSpace::Compile)
            {
                if strictness_sentence(definition, &address.module, address.index) {
                    strictness.insert(id.clone());
                }
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
            strictness,
        }
    }

    /// The ids one of whose input sentences is a `context` or a `strict` or `seqstrict`
    /// production ([`strictness_rules`] reads the heating and cooling rules among them).
    #[must_use]
    pub const fn strictness_ids(&self) -> &BTreeSet<String> {
        &self.strictness
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
    /// The run did not time out and every leaf is `Stuck`, `Trivial`, `Vacuous`, `CutPoint` or
    /// `TerminalRule` with no diagnostic (leaf, candidate or remainder; a cut point's proposed
    /// step is a candidate). A run that is not complete (a work-bound, depth-bound or undecided
    /// leaf, a diagnostic) covers only what it explored before it stopped, which depends on where
    /// it stopped. A stop leaf is final in its run's truncated system, so it does not make the
    /// run incomplete (module documentation).
    pub complete: bool,
    /// The matched compiled ids (README corpus-scale 4.5): k-rust's `matched`, which includes
    /// `applied`.
    pub rule_ids: BTreeSet<String>,
    /// The applied compiled ids: k-rust's `applied`, a subset of `rule_ids`.
    pub applied_ids: BTreeSet<String>,
    /// The baseline sentences behind `rule_ids`, the matched ones.
    pub sentences: BTreeSet<SentenceRef>,
    /// The baseline sentences behind `applied_ids`.
    pub applied_sentences: BTreeSet<SentenceRef>,
    /// The fired baseline sentences, a subset of `applied_sentences`: the rewrite rules whose
    /// step some explored path takes (k-rust `committed`) and the equations behind `applied_ids`
    /// (module docs). Not in [`Self::value`].
    pub fired_sentences: BTreeSet<SentenceRef>,
    /// The ids of `rule_ids` with no baseline sentence, with the reason (generating pass or an
    /// `UNMAPPED_*` value).
    pub unmapped: BTreeMap<String, String>,
    /// The guard outcomes the run collected (k-rust `coverage.guards`, asked for by a baseline
    /// result run, `ResultRun::guards`), by the baseline sentence behind each axiom; an axiom
    /// with no baseline sentence is left out. Not in [`Self::value`]: no schedule reads them.
    pub guards: BTreeMap<SentenceRef, Vec<AxiomGuardOutput<Pattern>>>,
    /// What the run's fired instances bound (k-rust `coverage.bindings`, asked for by a baseline
    /// result run, `ResultRun::bindings`), by the baseline sentence behind each axiom; `None`
    /// when the run collected none. Not in [`Self::value`]: no schedule reads them.
    pub bindings: Option<SentenceBindings>,
    /// The heating and cooling rules the run matched and fired, by compiled id
    /// ([`RuleAuthors::strictness_ids`]): every such rule of one production or `context` has the
    /// same author, so `sentences` cannot tell which argument position a run heated, and the
    /// ids can ([`strictness_rules`]). Not in [`Self::value`]: no schedule reads them.
    pub strictness: StrictnessCoverage,
    /// The depth the run's request asked for (`crate::execution::DefinitionTables::with_depth`):
    /// the longest rule window ([`Self::windows`]) and syntax path ([`SentenceBindings::paths`])
    /// it collected; 1 when it asked for none, its windows of length 1 being its fired rules and
    /// its paths of length 1 its operand heads and its axioms' own symbols. Not in
    /// [`Self::value`].
    pub depth: usize,
    /// The rule windows the run took (k-rust `coverage.windows`, asked for by a baseline result
    /// run whose tables hold a depth above 1), by the baseline sentences behind each step's rule;
    /// `None` when the run asked for none. Not in [`Self::value`]: no schedule reads them.
    pub windows: Option<SentenceWindows>,
}

/// The rule windows of a run by the baseline sentences behind their rules
/// ([`TestCoverage::windows`]).
///
/// A window is a sequence of rewrite rules some path of the run took as consecutive committed
/// steps (k-rust `coverage.windows`). Each step's rule is read as the baseline sentences behind
/// it, so a window of rule ids is the windows of every choice of one sentence per step. A window
/// with a step whose rule has no baseline sentence, or is a heating or cooling rule (whose
/// sentence is the production or `context` it was generated from, not a rule), is left out:
/// no sequence of authored rules was taken as those consecutive steps, since a generated step
/// stands between them.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SentenceWindows {
    /// The windows, each a list of sentences in step order: every window of length up to the
    /// run's depth ([`TestCoverage::depth`]) it took, so the record answers a question about any
    /// length up to it.
    pub sequences: BTreeSet<Vec<SentenceRef>>,
}

impl SentenceWindows {
    fn of(windows: &[Vec<String>], authors: &RuleAuthors) -> Self {
        let strictness = authors.strictness_ids();
        let mut sequences = BTreeSet::new();
        'window: for window in windows {
            let mut steps = Vec::with_capacity(window.len());
            for id in window {
                match authors.get(id) {
                    Some(Authorship::Sentences(sentences)) if !strictness.contains(id) => {
                        steps.push(sentences);
                    }
                    _ => continue 'window,
                }
            }
            // Every choice of one sentence per step.
            let mut choices = vec![Vec::with_capacity(steps.len())];
            for sentences in steps {
                choices = choices
                    .into_iter()
                    .flat_map(|prefix: Vec<SentenceRef>| {
                        sentences.iter().map(move |sentence| {
                            let mut next = prefix.clone();
                            next.push(sentence.clone());
                            next
                        })
                    })
                    .collect();
            }
            sequences.extend(choices);
        }
        Self { sequences }
    }
}

/// The heating and cooling rules a run matched and fired ([`TestCoverage::strictness`]), by
/// compiled id, under the predicates of `rule_ids` and `fired_sentences`.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct StrictnessCoverage {
    /// The ids among [`RuleAuthors::strictness_ids`] the run matched (k-rust `matched`).
    pub matched: BTreeSet<String>,
    /// The ids of `matched` the run fired: a rewrite rule some explored path takes (k-rust
    /// `committed`), an equation whose instance gave a result (`applied`).
    pub fired: BTreeSet<String>,
}

/// What a run's fired instances bound, by the baseline sentences behind their axioms
/// ([`TestCoverage::bindings`]). An axiom with no baseline sentence is left out: no authored
/// sentence stands for its instance.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SentenceBindings {
    /// Per sentence, the requested symbols that were the head, through injections, of a value a
    /// fired instance of an axiom behind it bound to a left-hand-side variable.
    pub operands: BTreeMap<SentenceRef, BTreeSet<String>>,
    /// Per selected binder bound at some fired instance, its values, with the sentences behind
    /// its axiom; in k-rust's order (axiom `UNIQUE_ID`, then variable).
    pub binders: Vec<SentenceBinder>,
    /// The alternatives of an axiom with several that a fired instance took (k-rust
    /// `bindings.alternatives`), with the sentences behind the axiom; in k-rust's order.
    pub alternatives: Vec<SentenceAlternative>,
    /// Per sentence, the syntax paths of length `2..=depth` a fired instance of an axiom behind
    /// it touched (k-rust `bindings.paths`, collected at a depth above 1,
    /// [`TestCoverage::depth`]): sequences of the requested symbols along consecutive argument
    /// positions that start at a position the instance inspected, built or took as an operand.
    /// `None` when the run collected none.
    pub paths: Option<BTreeMap<SentenceRef, BTreeSet<SyntaxPath>>>,
}

/// A syntax path `(P1, i1, P2, ..., Pn)` ([`SentenceBindings::paths`], [`GrammarGraph`]): the
/// symbols `P1, ..., Pn` by KORE name, and the 0-based argument positions `i1, ..., i(n-1)`,
/// `symbols[j + 1]` being the head, through injections, of argument `positions[j]` of
/// `symbols[j]`'s application.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SyntaxPath {
    /// The symbols, outermost first.
    pub symbols: Vec<String>,
    /// The argument positions between them.
    pub positions: Vec<usize>,
}

/// An alternative of an axiom with several that a fired instance took
/// ([`SentenceBindings::alternatives`], [`AlternativeKey`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SentenceAlternative {
    /// The alternative.
    pub key: AlternativeKey,
    /// The baseline sentences behind its axiom.
    pub sentences: BTreeSet<SentenceRef>,
}

/// One alternative of an axiom with several: the axiom's `UNIQUE_ID`, its left-hand side
/// alternative (a rewrite rule's disjunct or a function equation's reading, `None` when it has
/// one), and a rewrite rule's right-hand side alternative (its position in the disjunction,
/// `None` when it is none, and for an equation, whose instance gives its whole right-hand side).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct AlternativeKey {
    /// The axiom's `UNIQUE_ID`.
    pub axiom: String,
    /// The left-hand side alternative.
    pub lhs: Option<usize>,
    /// The right-hand side alternative.
    pub rhs: Option<usize>,
}

/// The values one selected template binder took ([`SentenceBindings::binders`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SentenceBinder {
    /// The axiom, by `UNIQUE_ID`.
    pub axiom: String,
    /// The baseline sentences behind the axiom.
    pub sentences: BTreeSet<SentenceRef>,
    /// The variable, as the definition writes it.
    pub variable: String,
    /// The `Int` literals bound, in decimal, the least ones k-rust kept, ascending.
    pub values: Vec<String>,
    /// Whether a further literal was bound that the cap left out.
    pub truncated: bool,
    /// Whether some fired instance bound a value that is no `Int` literal.
    pub nonliteral: bool,
}

impl SentenceBindings {
    /// k-rust's bindings `output`, by the baseline sentences `authors` names for each axiom.
    fn of(output: &BindingsOutput, authors: &RuleAuthors) -> Self {
        let sentences = |axiom: &str| match authors.get(axiom) {
            Some(Authorship::Sentences(sentences)) => sentences.clone(),
            _ => BTreeSet::new(),
        };
        let mut operands = BTreeMap::<SentenceRef, BTreeSet<String>>::new();
        for axiom in &output.operands {
            for sentence in sentences(&axiom.axiom) {
                operands
                    .entry(sentence)
                    .or_default()
                    .extend(axiom.symbols.iter().cloned());
            }
        }
        let binders = output
            .binders
            .iter()
            .filter_map(|binder| {
                let sentences = sentences(&binder.axiom);
                (!sentences.is_empty()).then(|| SentenceBinder {
                    axiom: binder.axiom.clone(),
                    sentences,
                    variable: binder.variable.clone(),
                    values: binder.values.clone(),
                    truncated: binder.truncated,
                    nonliteral: binder.nonliteral,
                })
            })
            .collect();
        let alternatives = output
            .alternatives
            .iter()
            .filter_map(|alternative| {
                let sentences = sentences(&alternative.axiom);
                (!sentences.is_empty()).then(|| SentenceAlternative {
                    key: AlternativeKey {
                        axiom: alternative.axiom.clone(),
                        lhs: alternative.lhs,
                        rhs: alternative.rhs,
                    },
                    sentences,
                })
            })
            .collect();
        let paths = output.paths.as_ref().map(|paths| {
            let mut by_sentence = BTreeMap::<SentenceRef, BTreeSet<SyntaxPath>>::new();
            for axiom in paths {
                for sentence in sentences(&axiom.axiom) {
                    by_sentence
                        .entry(sentence)
                        .or_default()
                        .extend(axiom.paths.iter().map(|path| SyntaxPath {
                            symbols: path.symbols.clone(),
                            positions: path.positions.clone(),
                        }));
                }
            }
            by_sentence
        });
        Self {
            operands,
            binders,
            alternatives,
            paths,
        }
    }
}

/// Whether one leaf leaves its run complete, for observed and unobserved leaves alike.
fn leaf_complete(
    halt: HaltClass,
    diagnostics: [&[BackendDiagnosticOutput<Pattern>]; 2],
    candidate_diagnostics: &[Vec<BackendDiagnosticOutput<Pattern>>],
) -> bool {
    matches!(
        halt,
        HaltClass::Stuck
            | HaltClass::Trivial
            | HaltClass::Vacuous
            | HaltClass::CutPoint
            | HaltClass::TerminalRule
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
        let mut fired_sentences = BTreeSet::new();
        let mut strictness = StrictnessCoverage::default();
        let mut unmapped = BTreeMap::new();
        let mut guards = BTreeMap::<SentenceRef, Vec<AxiomGuardOutput<Pattern>>>::new();
        for guard in &coverage.guards {
            if let Some(Authorship::Sentences(authors)) = authors.get(&guard.axiom) {
                for author in authors {
                    guards
                        .entry(author.clone())
                        .or_default()
                        .push(guard.clone());
                }
            }
        }
        let strictness_ids = authors.strictness_ids();
        for id in &coverage.matched {
            match authors.get(id) {
                Some(Authorship::Sentences(authors)) => {
                    sentences.extend(authors.iter().cloned());
                    if coverage.applied.contains(id) {
                        applied_sentences.extend(authors.iter().cloned());
                    }
                    // A rewrite rule fires when a path takes its step; an equation when its
                    // instance gave a result (it takes no step, so it is never committed).
                    let fired = if coverage.applied_rewrites.contains(id) {
                        coverage.committed.contains(id)
                    } else {
                        coverage.applied.contains(id)
                    };
                    if fired {
                        fired_sentences.extend(authors.iter().cloned());
                    }
                    if strictness_ids.contains(id) {
                        strictness.matched.insert(id.clone());
                        if fired {
                            strictness.fired.insert(id.clone());
                        }
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
            fired_sentences,
            unmapped,
            guards,
            bindings: coverage
                .bindings
                .as_ref()
                .map(|bindings| SentenceBindings::of(bindings, authors)),
            strictness,
            depth: coverage.depth.get(),
            windows: coverage
                .windows
                .as_ref()
                .map(|windows| SentenceWindows::of(windows, authors)),
        }
    }

    /// A run that produced no execution (an adapter failure), or no coverage signal: incomplete,
    /// no sentence listed.
    #[must_use]
    pub fn failed(test_id: &str) -> Self {
        Self {
            test_id: test_id.to_owned(),
            complete: false,
            rule_ids: BTreeSet::new(),
            applied_ids: BTreeSet::new(),
            sentences: BTreeSet::new(),
            applied_sentences: BTreeSet::new(),
            fired_sentences: BTreeSet::new(),
            unmapped: BTreeMap::new(),
            guards: BTreeMap::new(),
            bindings: None,
            strictness: StrictnessCoverage::default(),
            depth: 1,
            windows: None,
        }
    }

    /// The canonical value: `{"test_id","complete","rule_ids","applied_ids","sentences",
    /// "applied_sentences","unmapped"}`, every list sorted; `fired_sentences` is left out
    /// (module docs).
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
/// signal rather than being unmatched.
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

/// Whether the sentence at `index` of `module` in `definition` is one the compile generates
/// heating and cooling rules from: a `context`, or a production with a `strict` or `seqstrict`
/// attribute.
fn strictness_sentence(
    definition: &k_rust::definition::Definition,
    module: &str,
    index: u32,
) -> bool {
    use k_rust::definition::{AttributeKey, Sentence as Input};
    let Some(sentence) = definition
        .modules
        .iter()
        .find(|candidate| candidate.name == module)
        .and_then(|module| module.local_sentences.get(usize::try_from(index).ok()?))
    else {
        return false;
    };
    match &**sentence {
        Input::Context { .. } => true,
        Input::Production { attributes, .. } => {
            attributes.has(AttributeKey::Strict) || attributes.has(AttributeKey::Seqstrict)
        }
        _ => false,
    }
}

/// One heating rule of the compiled definition, with the cooling rule that undoes it, attributed
/// to the authored sentence it was generated from ([`strictness_rules`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StrictnessRule {
    /// The heating rule's `UNIQUE_ID`.
    pub heat: String,
    /// The heating rule's label, where the compile gave it one.
    pub heat_label: Option<String>,
    /// The cooling rule's `UNIQUE_ID`, `None` where none pairs with the heating rule.
    pub cool: Option<String>,
    /// The cooling rule's label.
    pub cool_label: Option<String>,
    /// Whether k-rust's run coverage can name the heating rule ([`coverage_domain`]).
    pub signal: bool,
    /// The authored sentence and, for a production, the argument position.
    pub source: StrictnessSource,
}

/// The authored sentence a heating rule was generated from ([`StrictnessRule::source`]).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum StrictnessSource {
    /// A `strict` (`sequential` false) or `seqstrict` production.
    Production {
        /// The production sentence.
        at: SentenceRef,
        /// Whether the attribute is `seqstrict`.
        sequential: bool,
        /// The 1-based argument position the rule heats, `None` where its label does not name
        /// one of the production's positions.
        position: Option<usize>,
        /// The context alias the rule instantiates (`strict(alias; ...)`), `None` for the
        /// default one.
        alias: Option<SentenceRef>,
    },
    /// A `context` sentence.
    Context {
        /// The context sentence.
        at: SentenceRef,
    },
}

impl StrictnessSource {
    /// The authored sentence.
    #[must_use]
    pub const fn at(&self) -> &SentenceRef {
        match self {
            Self::Production { at, .. } | Self::Context { at } => at,
        }
    }
}

/// The heating rules of a baseline side, each with its cooling rule and the authored sentence
/// and argument position it was generated from, in the order of that sentence, then position,
/// then alias, then id.
///
/// A `strict` or `seqstrict` production has, per argument position it names and context alias
/// it uses, one context, and a `context` sentence is one; the compile lowers each context to a
/// heating rule, which moves the subterm at the hole to the front of the computation while it is
/// not a result, and a cooling rule, which plugs it back once it is. Both are rewrite rules whose
/// input sentences ([`RuleAuthors`]) are the production (with the alias) or the context, so they
/// are the rewrite axioms among [`RuleAuthors::strictness_ids`]; the cooling rule is the one the
/// compile marks `cool`, and the heating rule is the other. The two rules of one context share
/// their input sentences and their label but for its suffix (`-heat`, `-cool`), the label the
/// compile gives a production's context, `MODULE.label` and the position, naming the position;
/// a context without a label has one heating and one cooling rule, so the input sentences alone
/// pair them. The sentences are read from the side's own definition, so a mutant side's ids are
/// read against the baseline only where its authors are; this is a reader of the baseline.
/// Unparsable KORE gives no rule.
#[must_use]
pub fn strictness_rules(
    validated: &ValidatedDefinition,
    authors: &RuleAuthors,
) -> Vec<StrictnessRule> {
    use k_rust::definition::{AttributeKey, Sentence as Input};
    let ids = authors.strictness_ids();
    if ids.is_empty() {
        return Vec::new();
    }
    let Ok(kore) = parse_definition(&validated.artifacts().definition_kore) else {
        return Vec::new();
    };
    let definition = validated.definition();
    let sentence = |at: &SentenceRef| {
        definition
            .modules
            .iter()
            .find(|module| module.name == at.module)
            .and_then(|module| module.local_sentences.get(usize::try_from(at.index).ok()?))
    };
    let string_of = |attribute: &Pattern, key: KoreAttribute| match attribute {
        Pattern::Application { symbol, arguments } if symbol.name == key.as_str() => {
            match arguments.as_slice() {
                [Pattern::String(text)] => text.as_utf8().ok().map(str::to_owned),
                _ => None,
            }
        }
        _ => None,
    };
    // (id, label, cool, signal) of every rewrite axiom among the strictness ids.
    let mut rules = Vec::new();
    for axiom in kore.modules.iter().flat_map(|module| &module.sentences) {
        let Sentence::Axiom {
            pattern,
            attributes,
            ..
        } = axiom
        else {
            continue;
        };
        if !matches!(**pattern, Pattern::Rewrites { .. }) {
            continue;
        }
        let Some(id) = attributes
            .0
            .iter()
            .find_map(|attribute| string_of(attribute, KoreAttribute::UniqueId))
            .filter(|id| ids.contains(id))
        else {
            continue;
        };
        let label = attributes
            .0
            .iter()
            .find_map(|attribute| string_of(attribute, KoreAttribute::Label));
        let cool = attributes
            .0
            .iter()
            .any(|attribute| named(attribute, KoreAttribute::Cool));
        let signal = !attributes.0.iter().any(|attribute| {
            named(attribute, KoreAttribute::SmtLemma)
                || named(attribute, KoreAttribute::NonExecutable)
        });
        rules.push((id, label, cool, signal));
    }
    // The cooling rules by their input sentences and their label's stem.
    let stem = |label: &Option<String>, suffix: &str| {
        label
            .as_deref()
            .map(|label| label.strip_suffix(suffix).unwrap_or(label).to_owned())
    };
    let inputs = |id: &str| match authors.get(id) {
        Some(Authorship::Sentences(sentences)) => Some(sentences.clone()),
        _ => None,
    };
    let mut cooling =
        BTreeMap::<(BTreeSet<SentenceRef>, Option<String>), Vec<(String, Option<String>)>>::new();
    for (id, label, cool, _) in &rules {
        if *cool && let Some(sentences) = inputs(id) {
            cooling
                .entry((sentences, stem(label, "-cool")))
                .or_default()
                .push((id.clone(), label.clone()));
        }
    }
    let mut heating = BTreeMap::<(BTreeSet<SentenceRef>, Option<String>), usize>::new();
    for (id, label, cool, _) in &rules {
        if !*cool && let Some(sentences) = inputs(id) {
            *heating
                .entry((sentences, stem(label, "-heat")))
                .or_default() += 1;
        }
    }
    let mut found = Vec::new();
    for (id, label, cool, signal) in rules {
        if cool {
            continue;
        }
        let Some(sentences) = inputs(&id) else {
            continue;
        };
        let mut context = None;
        let mut production = None;
        let mut alias = None;
        for at in &sentences {
            match sentence(at).map(|sentence| &**sentence) {
                Some(Input::Context { .. }) => context = Some(at.clone()),
                Some(Input::Production { attributes, .. })
                    if attributes.has(AttributeKey::Strict)
                        || attributes.has(AttributeKey::Seqstrict) =>
                {
                    production = Some(at.clone());
                }
                Some(Input::ContextAlias { .. }) => alias = Some(at.clone()),
                _ => {}
            }
        }
        let source = match (context, production) {
            (Some(at), _) => StrictnessSource::Context { at },
            (None, Some(at)) => {
                let Some(Input::Production {
                    label: Some(production_label),
                    items,
                    attributes,
                    ..
                }) = sentence(&at).map(|sentence| &**sentence)
                else {
                    continue;
                };
                // The compile labels a production's context `MODULE.label` and the position, the
                // label written without backquotes or whitespace (its `klabel` where it has one).
                let written = attributes
                    .string(AttributeKey::Klabel)
                    .unwrap_or(production_label.name.as_str())
                    .chars()
                    .filter(|character| *character != '`' && !character.is_whitespace())
                    .collect::<String>();
                let arity = items
                    .iter()
                    .filter(|item| {
                        matches!(item, k_rust::definition::ProductionItem::NonTerminal { .. })
                    })
                    .count();
                let position = label
                    .as_deref()
                    .and_then(|label| label.strip_suffix("-heat"))
                    .and_then(|label| label.strip_prefix(&format!("{}.{written}", at.module)))
                    .filter(|digits| {
                        !digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit())
                    })
                    .and_then(|digits| digits.parse::<usize>().ok())
                    .filter(|position| (1..=arity).contains(position));
                StrictnessSource::Production {
                    at,
                    sequential: !attributes.has(AttributeKey::Strict),
                    position,
                    alias,
                }
            }
            (None, None) => continue,
        };
        // A cooling rule pairs with the one heating rule of its sentences and stem.
        let key = (sentences, stem(&label, "-heat"));
        let (cool, cool_label) = match (cooling.get(&key).map(Vec::as_slice), heating.get(&key)) {
            (Some([(cool, cool_label)]), Some(1)) => (Some(cool.clone()), cool_label.clone()),
            _ => (None, None),
        };
        found.push(StrictnessRule {
            heat: id,
            heat_label: label,
            cool,
            cool_label,
            signal,
            source,
        });
    }
    found.sort_by(|left, right| {
        let order = |rule: &StrictnessRule| match &rule.source {
            StrictnessSource::Production {
                at,
                position,
                alias,
                ..
            } => (at.clone(), *position, alias.clone()),
            StrictnessSource::Context { at } => (at.clone(), None, None),
        };
        order(left)
            .cmp(&order(right))
            .then_with(|| left.heat.cmp(&right.heat))
    });
    found
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

/// The symbols the axioms behind one sentence inspect and build ([`syntax_facts`]).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SentenceSymbols {
    /// The symbols at a non-variable position of a left-hand side (through injections and
    /// inside collections), by KORE name.
    pub inspected: BTreeSet<String>,
    /// The symbols at a non-variable position of a right-hand side, by KORE name.
    pub built: BTreeSet<String>,
}

/// What a definition says of its syntax, without a run ([`syntax_facts`]).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SyntaxFacts {
    /// The constructors of the definition, by KORE name: the symbols k-rust reads as free
    /// constructors, without a hook, that are neither injections nor a collection's symbols.
    pub constructors: BTreeSet<String>,
    /// Per baseline sentence behind a rewrite rule or a function equation of the definition (an
    /// `anywhere` or overload equation included, a simplification not), the symbols its axioms
    /// inspect and build: what the sentence can touch, whichever alternative fires.
    pub by_sentence: BTreeMap<SentenceRef, SentenceSymbols>,
    /// Per such sentence, the symbols its axioms with one alternative of each side inspect and
    /// build: what a fired instance of the sentence touched, since its axiom's one alternative
    /// is the one it took. Empty for a sentence all of whose axioms have several.
    pub single: BTreeMap<SentenceRef, SentenceSymbols>,
    /// Per alternative of an axiom with several behind such a sentence, the symbols it inspects
    /// (its left-hand side alternative's) and builds (its right-hand side alternative's, or the
    /// whole right-hand side): what a fired instance that took it touched, which a run's
    /// bindings name ([`SentenceBindings::alternatives`]).
    pub by_alternative: BTreeMap<AlternativeKey, SentenceSymbols>,
}

/// The syntax facts of `definition` ([`SyntaxFacts`]), each axiom by the baseline sentences
/// `authors` names for it. The axioms are the internalized ones a run applies: a function
/// equation's left-hand side has its argument binders' patterns in place, so the symbols an
/// equation inspects are those its instances match. A sentence's sets are the union over its
/// axioms. An axiom with several alternatives (k-rust loads one rule per disjunct of a
/// rewrite rule's left-hand side, or reading of a function equation, under one `UNIQUE_ID`, and
/// a rewrite rule with a disjunctive right-hand side builds one successor per alternative) has
/// its alternatives listed apart, as k-rust names the one a fired instance took. A simplification states a fact of the definition's functions that the definition
/// means the same without, so it is no step of the definition's meaning and is not listed.
#[must_use]
pub fn syntax_facts(
    definition: &k_rust_backend::definition::BackendDefinition,
    authors: &RuleAuthors,
) -> SyntaxFacts {
    use k_rust_backend::rule::{RewriteRule, RuleRhs};
    use k_rust_backend::term::{SymbolType, Term};
    let constructors = definition
        .symbols()
        .values()
        .filter(|symbol| {
            matches!(symbol.attributes.symbol_type, SymbolType::Constructor)
                && symbol.attributes.hook.is_none()
                && symbol.attributes.collection.is_none()
                && symbol.name.as_ref() != "inj"
        })
        .map(|symbol| symbol.name.to_string())
        .collect();
    let names = |term: &Term, into: &mut BTreeSet<String>| {
        term.visit_symbols(&mut |symbol| {
            if !into.contains(symbol.name.as_ref()) {
                into.insert(symbol.name.to_string());
            }
        });
    };
    let mut by_sentence = BTreeMap::<SentenceRef, SentenceSymbols>::new();
    let mut single = BTreeMap::<SentenceRef, SentenceSymbols>::new();
    let mut by_alternative = BTreeMap::<AlternativeKey, SentenceSymbols>::new();
    let extend = |into: &mut SentenceSymbols, symbols: &SentenceSymbols| {
        into.inspected.extend(symbols.inspected.iter().cloned());
        into.built.extend(symbols.built.iter().cloned());
    };
    // `rewrite`: whether the rule is a rewrite rule, whose disjunctive right-hand side builds one
    // successor per alternative; an equation's instance gives its whole right-hand side.
    let mut add = |rule: &RewriteRule, rewrite: bool| {
        let Some(Authorship::Sentences(sentences)) = authors.get(&rule.attributes.unique_id) else {
            return;
        };
        let mut inspected = BTreeSet::new();
        names(&rule.lhs, &mut inspected);
        // Each right-hand side alternative's built symbols, by its position when a rewrite
        // rule's disjunction gives it one.
        let mut built = Vec::<(Option<usize>, BTreeSet<String>)>::new();
        match &rule.rhs {
            RuleRhs::Term(term) => {
                let mut symbols = BTreeSet::new();
                names(term, &mut symbols);
                built.push((None, symbols));
            }
            RuleRhs::Disjunction(alternatives) => {
                let mut whole = BTreeSet::new();
                for (index, alternative) in alternatives.iter().enumerate() {
                    let mut symbols = BTreeSet::new();
                    names(&alternative.term, &mut symbols);
                    if rewrite {
                        built.push((Some(index), symbols));
                    } else {
                        whole.extend(symbols);
                    }
                }
                if !rewrite {
                    built.push((None, whole));
                }
            }
            RuleRhs::Top | RuleRhs::Bottom | RuleRhs::Predicates(_) => {
                built.push((None, BTreeSet::new()));
            }
        }
        for (rhs, built) in built {
            let symbols = SentenceSymbols {
                inspected: inspected.clone(),
                built,
            };
            for sentence in sentences {
                extend(by_sentence.entry(sentence.clone()).or_default(), &symbols);
            }
            if rule.lhs_alternative.is_none() && rhs.is_none() {
                for sentence in sentences {
                    extend(single.entry(sentence.clone()).or_default(), &symbols);
                }
            } else {
                let key = AlternativeKey {
                    axiom: rule.attributes.unique_id.clone(),
                    lhs: rule.lhs_alternative,
                    rhs,
                };
                extend(by_alternative.entry(key).or_default(), &symbols);
            }
        }
    };
    for rule in definition
        .rewrite_theory()
        .values()
        .flat_map(|priorities| priorities.values())
        .flatten()
    {
        add(&rule.rule, true);
    }
    for rule in definition
        .function_theory()
        .values()
        .flat_map(|priorities| priorities.values())
        .flatten()
    {
        add(rule, false);
    }
    SyntaxFacts {
        constructors,
        by_sentence,
        single,
        by_alternative,
    }
}

#[cfg(test)]
mod retired_tests {
    use super::{COVERAGE_DOMAIN, RETIRED_COVERAGE_DOMAINS};

    /// Review L2-1-tail-1 D4: the retired coverage domains are `v1` up to the version before
    /// [`COVERAGE_DOMAIN`], so a bump that forgets to retire the old domain fails here.
    #[test]
    fn every_earlier_coverage_domain_is_retired() {
        let current = COVERAGE_DOMAIN
            .strip_prefix("kink/coverage/v")
            .and_then(|n| n.parse::<usize>().ok())
            .expect("kink/coverage/v<N>");
        let earlier = (1..current)
            .map(|n| format!("kink/coverage/v{n}"))
            .collect::<Vec<_>>();
        assert_eq!(RETIRED_COVERAGE_DOMAINS.as_slice(), earlier.as_slice());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A leaf leaves its run complete exactly when it is final in the system the run computes
    /// and carries no diagnostic: a stuck, trivial or vacuous leaf, and a stop leaf of a run with
    /// stop rules, which is final in its truncated system. Every bound, undecided or refused halt
    /// leaves the run incomplete.
    #[test]
    fn stop_leaves_leave_their_run_complete() {
        let diagnostic = BackendDiagnosticOutput::UnsupportedHookUnevaluated {
            hook: "TEST.hook".into(),
            reason: "unavailable".into(),
        };
        for halt in HaltClass::ALL {
            let final_leaf = matches!(
                halt,
                HaltClass::Stuck
                    | HaltClass::Trivial
                    | HaltClass::Vacuous
                    | HaltClass::CutPoint
                    | HaltClass::TerminalRule
            );
            assert_eq!(leaf_complete(halt, [&[], &[]], &[]), final_leaf, "{halt:?}");
            let diagnosed = std::slice::from_ref(&diagnostic);
            assert!(!leaf_complete(halt, [diagnosed, &[]], &[]), "{halt:?}");
            assert!(!leaf_complete(halt, [&[], diagnosed], &[]), "{halt:?}");
            assert!(
                !leaf_complete(halt, [&[], &[]], &[vec![diagnostic.clone()]]),
                "{halt:?}: a diagnosed candidate, such as a cut point's proposed step"
            );
        }
    }
}
