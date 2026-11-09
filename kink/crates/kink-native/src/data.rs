//! What a definition's full critical-pair check says about the ends of runs on it (fz26
//! KINK-BASELINE-FINDINGS, finding KINK-BASELINE-TRUST).
//!
//! kink's kill is "relative to the definition, not to k-rust's model of it" (`trust.md`, "What a
//! kill trusts"): a compared end is the value of a term in the definition's initial model, and two
//! ends differ only if no model of the definition identifies them. k-rust's full check reads a
//! definition by the model `M+` (its normal forms, with a fresh constant in each sort that does
//! not have an element in every model and the witness equations the check adopts), which is a
//! model of the definition when the executable and witness equations terminate over the added
//! constants (A1+, a premise k-rust states and does not check) and their critical pairs join
//! (k-rust-backend `data_term`, "What a data term denotes"); `M+` agrees with the normal-form
//! model `M_NF` on every term free of the constants, which every end kink compares is. The
//! baseline's pairs were a trusted premise ("which the backend checks",
//! `consistency`), but nothing checked them. A pair that does not join can identify two ends kink
//! compares: in `q(_) => a` with `q(_) => bb`, every model has `a = bb`, so a mutant that writes
//! `bb` where the baseline writes `a` is equal to it in every model, and a "kill" through the
//! whole-term slot would be false. An identification reaches other terms through congruence, so
//! no local reading of the compared terms rules it out: the whole definition must be shown
//! confluent (`data_term`, "A local check cannot replace the global one").
//!
//! So each definition's [`DataFacts`] are computed once per load, on the backend kink runs it on
//! (`Backend::from_definition`, the selected definition), through
//! [`BackendDefinition::data_heads`] (the full check, [`CheckScope::All`]) and
//! [`BackendDefinition::data_heads_assuming`] with the author's named premises (kink-flow's
//! `[spec] assume_joined`). [`data_ends`] is the one function that says which ends of runs on a
//! definition are data under it, from its own facts: while a finding is left none is, and kink
//! counts no kill on it. A finding is assumed only by its name, as k-rust-fuzz assumes one,
//! through k-rust-backend's one renderer (`data_term::names`, with the K label decoder
//! [`label`]), so a name the fuzz prints is a name kink reads. A name is the finding's kind, its
//! sentences and a digest of the compiled sentences it is about (`kind:SENTENCES#DIGEST`), so it
//! survives every edit that leaves those sentences alone and names nothing once they change; a
//! premise assumes the findings whose name is byte-equal to it. Only an undecided finding can be
//! assumed: [`DataFacts::refused_names`] refuses every other premise with its reason
//! (`malformed`, `position-name`, `unnamed-sentence`, `no-digest`, `changed`, `no-finding`,
//! `decided`, `ambiguous`).
//!
//! The premises [`DataFacts::of`] takes are in the K spelling, each sentence by its K label. A
//! front end that spells sentences its own way (KRS by the item that wrote it) gives its spelling
//! ([`SentenceNames`]): the facts then print names in it, and the front end's premises are mapped
//! to the K spelling before they are read ([`SentenceNames::to_k`]).
//!
//! The mutant's facts are compared with the baseline's ([`DataFacts::differs_outside`]): a finding
//! of the claim-free mutant outside the heads its edit can change should be the baseline's
//! (`consistency`: such a pair is normalized with the baseline's equations alone), and kink checks
//! that, by name, instead of arguing it. A name holds no position, so a patch that only moves
//! lines changes none.
//!
//! [`CheckScope::All`]: k_rust_backend::confluence::CheckScope::All

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use k_rust::kore::ast::Pattern;
use k_rust_backend::{
    confluence::{ViolationKind, WitnessPass},
    data_term::{
        DataHeads, Finding,
        names::{self, FindingName, Spelling},
    },
    definition::BackendDefinition,
    rule::{Concreteness, ConstraintKind, RewriteRule, TermIndex},
};
use serde_json::{Value, json};

/// The version of the data facts kink reads from each definition's full critical-pair check and
/// what it refuses on them: a mutation is unknown while the baseline has a finding no
/// `assume_joined` name assumes (`baseline-findings`), or when the claim-free mutant's findings
/// outside the heads its edit can change differ from the baseline's (`mutant-findings`). A
/// component of kink's semantics identity (kink-campaign `identity`, key `data_facts`), so no
/// store made before kink read these facts (a tier-1 outcome, a pattern answer, a result) is
/// honoured. Bump it whenever what these facts refuse changes. v1 (fz26 KINK-BASELINE-FINDINGS).
/// v2 (KINK-FINDING-NAMES): a finding is named by its kind, sentences and a digest of its compiled
/// sentences, not by its generated-K positions; a premise assumes the findings whose name is
/// byte-equal to it, a genuine finding is never assumed, and the baseline and a mutant are
/// compared by these names, so a patch that only moves lines no longer changes them.
pub const DATA_FACTS_VERSION: &str = "kink-native/data-facts/v2";

/// The K label a KORE symbol name encodes (the name itself when it does not decode): how every
/// finding name writes a symbol (k-rust-backend `data_term::names`). It is k-rust's
/// `kast::identifier::label_or_name`, which k-rust-fuzz passes too.
#[must_use]
pub fn label(name: &str) -> String {
    k_rust::kast::identifier::label_or_name(name)
}

/// A front end's spelling of the sentences finding names name (k-rust-backend
/// `data_term::names`, "The grammar"): its own name for each K label it emitted. KRS spells a
/// sentence by the item that wrote it (`crate::plus_zero` for the label `nat--plus_zero`). A
/// spelling given to several labels is dropped for each of them, so the map is one to one and a
/// name maps back to the K spelling ([`Self::to_k`]). Empty: the K spelling.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SentenceNames {
    spelled: BTreeMap<String, String>,
    labels: BTreeMap<String, String>,
}

impl SentenceNames {
    /// The spelling `pairs` gives, `(K label, spelling)`, a spelling of several labels dropped.
    #[must_use]
    pub fn new(pairs: impl IntoIterator<Item = (String, String)>) -> Self {
        let mut by_spelling = BTreeMap::<String, BTreeSet<String>>::new();
        for (label, spelling) in pairs {
            if label != spelling {
                by_spelling.entry(spelling).or_default().insert(label);
            }
        }
        let mut names = Self::default();
        for (spelling, labels) in by_spelling {
            if let [label] = labels.into_iter().collect::<Vec<_>>().as_slice() {
                names.spelled.insert(label.clone(), spelling.clone());
                names.labels.insert(spelling, label.clone());
            }
        }
        names
    }

    /// Whether it is the K spelling.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.spelled.is_empty()
    }

    /// The front end's spelling of the K label `label`, if it has one.
    #[must_use]
    pub fn spell(&self, label: &str) -> Option<String> {
        self.spelled.get(label).cloned()
    }

    /// The K label the front end spells `spelling`, if any.
    #[must_use]
    pub fn label(&self, spelling: &str) -> Option<String> {
        self.labels.get(spelling).cloned()
    }

    /// `name`, written in the front end's spelling, in the K spelling (unchanged when it is no
    /// name of the grammar, which is then refused as it stands).
    #[must_use]
    pub fn to_k(&self, name: &str) -> String {
        if self.is_empty() {
            return name.to_owned();
        }
        names::respell(name, &|spelling| self.label(spelling)).unwrap_or_else(|| name.to_owned())
    }

    /// `name`, written in the K spelling, in the front end's.
    #[must_use]
    pub fn spelled(&self, name: &str) -> String {
        if self.is_empty() {
            return name.to_owned();
        }
        names::respell(name, &|label| self.spell(label)).unwrap_or_else(|| name.to_owned())
    }
}

/// What a finding is about the definition (k-rust-backend `data_term`, "Findings: genuine or
/// undecided").
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum FindingVerdict {
    /// A pair with a ground input that has two normal forms.
    Genuine,
    /// Not shown to join or to apply as written, which may be a limit of the checker.
    Undecided,
    /// A fact about the definition as written that no premise removes; it cannot be assumed.
    Decided,
}

impl FindingVerdict {
    /// The name documents print.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Genuine => "genuine",
            Self::Undecided => "undecided",
            Self::Decided => "decided",
        }
    }

    fn of(finding: &Finding) -> Self {
        if finding.is_decided() {
            Self::Decided
        } else if finding.is_genuine() {
            Self::Genuine
        } else {
            Self::Undecided
        }
    }
}

/// One sentence of a finding as a document shows it: its part of the name, in the front end's
/// spelling, and where the generated K writes it (information only: a name holds no position).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FindingSentence {
    pub part: String,
    pub at: Option<String>,
}

/// One finding of a definition's full check as kink states it.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct NamedFinding {
    /// Its name (k-rust-backend `data_term::names`) in the front end's spelling, which
    /// `assume_joined` takes; `None` for a finding about a sentence with no label, no id and no
    /// generated part.
    pub name: Option<String>,
    pub verdict: FindingVerdict,
    /// Whether an `assume_joined` name assumes it.
    pub assumed: bool,
    /// One line naming it (k-rust-backend `Finding::describe`).
    pub description: String,
    /// What identifies it across the baseline and a mutant and in the execution digest: its
    /// name in the K spelling, or, for a finding with no name, `unnamed:` and its description.
    pub identity: String,
    /// Its sentences, in its name's order.
    pub sentences: Vec<FindingSentence>,
}

impl NamedFinding {
    fn of(
        finding: &Finding,
        name: Option<&FindingName>,
        assumed: bool,
        spelling: &SentenceNames,
    ) -> Self {
        let spell = |label: &str| spelling.spell(label);
        let spelled = Spelling {
            symbol: &label,
            sentence: &spell,
        };
        Self {
            name: name.map(|name| spelled.text(name)),
            verdict: FindingVerdict::of(finding),
            assumed,
            description: finding.describe(label),
            identity: identity(finding, name),
            sentences: name
                .map(|name| {
                    name.sentences
                        .iter()
                        .map(|sentence| FindingSentence {
                            part: names::Sentence {
                                base: match &sentence.sentence.base {
                                    names::SentenceBase::Overload(greater, lesser) => {
                                        names::SentenceBase::Overload(label(greater), label(lesser))
                                    }
                                    other => other.clone(),
                                },
                                alternative: sentence.sentence.alternative,
                            }
                            .text(&spell),
                            at: sentence.at.clone(),
                        })
                        .collect()
                })
                .unwrap_or_default(),
        }
    }

    /// `{name, verdict, assumed, description, sentences: [{part, at}]}`.
    #[must_use]
    pub fn value(&self) -> Value {
        json!({
            "name": self.name,
            "verdict": self.verdict.name(),
            "assumed": self.assumed,
            "description": self.description,
            "sentences": self
                .sentences
                .iter()
                .map(|sentence| json!({"part": sentence.part, "at": sentence.at}))
                .collect::<Vec<_>>(),
        })
    }
}

/// The K-spelled name of a finding, or `unnamed:` and its description for one with no name.
fn identity(finding: &Finding, name: Option<&FindingName>) -> String {
    name.map_or_else(
        || format!("unnamed:{}", finding.describe(label)),
        |name| Spelling::k(&label).text(name),
    )
}

/// Why an `assume_joined` name is refused ([`DataFacts::refused_names`]): the name in the front
/// end's spelling, the refusal's code and why.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NameRefusal {
    pub name: String,
    /// `malformed`, `position-name`, `unnamed-sentence`, `no-digest`, `changed`, `no-finding`,
    /// `decided` or `ambiguous` (k-rust-backend `data_term::names::Refusal`).
    pub reason: String,
    pub detail: String,
}

/// One definition's full critical-pair check as kink reads it: k-rust's [`DataHeads`] with the
/// author's assumed names applied, and what kink's consistency gate guards the check with (the
/// executable equations and root pairs of the definition the check ran on, and the index of each
/// equation).
#[derive(Clone, Debug)]
pub struct DataFacts {
    heads: DataHeads,
    /// The premises, in the K spelling.
    assume_joined: Vec<String>,
    spelling: SentenceNames,
    /// Each premise the definition refuses, in the order of `assume_joined`.
    refused: Vec<NameRefusal>,
    /// The unique id of each equation of the function theory, with its index.
    index_of: BTreeMap<String, TermIndex>,
    /// The executable equations of the function theory (the check skips `[symbolic]` ones).
    executable_equations: usize,
    /// The root pairs: two executable equations of one index and priority group.
    root_pairs: usize,
}

impl DataFacts {
    /// The facts of `definition` (the definition a backend selected for the main module, the one
    /// its runs execute on), every finding whose name one of `assume_joined` (in the K spelling)
    /// is assumed (`data_heads_assuming`; only an undecided finding ever is). The full check
    /// costs about as much as the definition's load, so a caller computes this once per load.
    #[must_use]
    pub fn of(definition: &BackendDefinition, assume_joined: &[String]) -> Self {
        Self::spelled(definition, assume_joined, SentenceNames::default())
    }

    /// [`Self::of`], printing names in the front end's spelling `spelling` (the premises are still
    /// in the K spelling: [`SentenceNames::to_k`]).
    #[must_use]
    pub fn spelled(
        definition: &BackendDefinition,
        assume_joined: &[String],
        spelling: SentenceNames,
    ) -> Self {
        let mut heads = definition.data_heads();
        let mut refused = Vec::new();
        if !assume_joined.is_empty() {
            let premises = assume_joined
                .iter()
                .filter_map(|given| names::canonical(given))
                .collect::<BTreeSet<_>>();
            let k = Spelling::k(&label);
            heads = definition.data_heads_assuming(&heads, |_, name| {
                name.is_some_and(|name| premises.contains(&k.text(name)))
            });
            let candidates = heads
                .named()
                .map(|(finding, name, _)| names::Candidate { finding, name })
                .collect::<Vec<_>>();
            let spell = |label: &str| spelling.spell(label);
            let spelled = Spelling {
                symbol: &label,
                sentence: &spell,
            };
            for given in assume_joined {
                let reason = if given.starts_with("baseline:") || given.starts_with("mutant:") {
                    Some((
                        "no-finding",
                        "kink names the baseline's findings without a side prefix (`baseline:` \
                         and `mutant:` are k-rust-fuzz's): the claim-free mutant's are checked \
                         equal to the baseline's, and every name applies to both"
                            .to_owned(),
                    ))
                } else {
                    names::classify(given, &candidates, definition, &spelled)
                        .err()
                        .map(|refusal| (refusal.reason(), refusal.detail(given)))
                };
                if let Some((reason, detail)) = reason {
                    refused.push(NameRefusal {
                        name: spelling.spelled(given),
                        reason: reason.to_owned(),
                        detail,
                    });
                }
            }
        }
        let mut index_of = BTreeMap::new();
        let (mut executable_equations, mut root_pairs) = (0, 0);
        for (index, priorities) in definition.function_theory() {
            for rules in priorities.values() {
                for rule in rules {
                    index_of.insert(rule.attributes.unique_id.clone(), index.clone());
                }
                let executable = rules.iter().filter(|rule| !symbolic(rule)).count();
                executable_equations += executable;
                root_pairs += executable * executable.saturating_sub(1) / 2;
            }
        }
        Self {
            heads,
            assume_joined: assume_joined.to_vec(),
            spelling,
            refused,
            index_of,
            executable_equations,
            root_pairs,
        }
    }

    /// k-rust's data heads and findings, the assumed ones moved to [`DataHeads::assumed`].
    #[must_use]
    pub const fn heads(&self) -> &DataHeads {
        &self.heads
    }

    /// The names the facts were computed with, in the K spelling.
    #[must_use]
    pub fn assume_joined(&self) -> &[String] {
        &self.assume_joined
    }

    /// The front end's spelling the facts print names in.
    #[must_use]
    pub const fn spelling(&self) -> &SentenceNames {
        &self.spelling
    }

    /// The witness equations the full check adopted (k-rust-backend
    /// `ValueClaims::witnesses`; empty unless [`Self::witness_pass_adopted`]): the findings are
    /// those of the check on the executable equations and these, in the model `M+`. The
    /// consistency gate diffs them between the baseline and a claim-free mutant (fz26
    /// KINK-WITNESS), so the witnesses it compares are those of the check it reads.
    #[must_use]
    pub fn witnesses(&self) -> &[Arc<RewriteRule>] {
        self.heads.witnesses()
    }

    /// Whether the full check adopted its pass with witness equations (k-rust-backend
    /// `CheckCounts::witness_pass`): `false` when it proposed none or kept its first pass.
    #[must_use]
    pub fn witness_pass_adopted(&self) -> bool {
        self.heads.check_counts().witness_pass == WitnessPass::Adopted
    }

    /// Whether no finding is left and the check is complete ([`Self::incomplete`]): [`data_ends`]
    /// admits ends only then.
    #[must_use]
    pub fn has_data(&self) -> bool {
        self.heads.confluent() && self.incomplete().is_none()
    }

    /// Whether a simplification of the full check ran out of native stack: the check's verdict,
    /// and so [`Self::has_data`], then depends on the thread, not only on the definition.
    #[must_use]
    pub fn stack_stopped(&self) -> bool {
        self.heads.check_counts().condition_stack_stops > 0
    }

    /// Why the full check is not shown to have read the whole definition, if it is not: a
    /// simplification of the check ran out of native stack (its verdict then depends on the
    /// thread), or the check did not read every executable equation, skipped a candidate pair,
    /// or classified fewer pairs than the definition has root pairs (two executable equations of
    /// one index and priority group). k-rust reports these counts for the whole definition only,
    /// so the guard shows that no early return fired, not that every group was classified. The
    /// consistency gate refuses an incomplete mutant check on the same guard, and an incomplete
    /// check has no data (fz26 KINK-BASELINE-FINDINGS review N2): one place, both sides.
    #[must_use]
    pub fn incomplete(&self) -> Option<String> {
        let counts = self.heads.check_counts();
        if counts.condition_stack_stops > 0 {
            return Some(format!(
                "{} simplifications of the check ran out of native stack",
                counts.condition_stack_stops
            ));
        }
        (counts.equations != self.executable_equations
            || counts.skipped > 0
            || counts.pairs < self.root_pairs)
            .then(|| {
                format!(
                    "k-rust read {} of the {} executable equations, skipped {} candidate pairs \
                     and classified {} pairs of the {} root pairs",
                    counts.equations,
                    self.executable_equations,
                    counts.skipped,
                    counts.pairs,
                    self.root_pairs
                )
            })
    }

    /// Every finding with its name and whether it is assumed, the unassumed first.
    fn named(&self) -> impl Iterator<Item = (&Finding, Option<&FindingName>, bool)> {
        self.heads.named()
    }

    fn stated(&self, finding: &Finding, name: Option<&FindingName>, assumed: bool) -> NamedFinding {
        NamedFinding::of(finding, name, assumed, &self.spelling)
    }

    /// The findings no name assumes.
    #[must_use]
    pub fn unnamed(&self) -> Vec<NamedFinding> {
        self.named()
            .filter(|(_, _, assumed)| !assumed)
            .map(|(finding, name, assumed)| self.stated(finding, name, assumed))
            .collect()
    }

    /// Every finding, the assumed ones marked, in k-rust's order (the unassumed first).
    #[must_use]
    pub fn findings(&self) -> Vec<NamedFinding> {
        self.named()
            .map(|(finding, name, assumed)| self.stated(finding, name, assumed))
            .collect()
    }

    /// Every finding that involves an equation of one of `heads` (KORE symbol names), the assumed
    /// ones marked, the unassumed first: those kink's consistency gate reads for those heads
    /// ([`Self::reads`]: a pair or an equation report with an equation of one of them, an
    /// equation indexed at no symbol counting as every head's, and every precondition row that
    /// names one or none). What a function's equations state rests on exactly these: a finding
    /// outside them is about equations no evaluation of an application of `heads` uses, when
    /// `heads` is closed under the equations' reach (`consistency::EquationReach`).
    #[must_use]
    pub fn findings_at(&self, heads: &BTreeSet<String>) -> Vec<NamedFinding> {
        self.named()
            .filter(|(finding, _, _)| self.reads(finding, Some(heads)))
            .map(|(finding, name, assumed)| self.stated(finding, name, assumed))
            .collect()
    }

    /// The names of [`Self::assume_joined`] this definition refuses, each with its reason
    /// (k-rust-backend `data_term::names::classify`): a name must be byte-equal to the name of
    /// an undecided finding of the definition's full critical-pair check.
    #[must_use]
    pub fn refused_names(&self) -> Vec<NameRefusal> {
        self.refused.clone()
    }

    /// Whether the findings outside `checked` (KORE symbol names; `None` for every head, so
    /// every finding is inside) differ between these facts (a claim-free mutant's) and
    /// `baseline`'s, by name, assumed or not. A finding is inside when kink's consistency gate
    /// reads it for those heads (`consistency`), with each side's own index of its equations.
    /// Only for a gate that ran: when it read nothing (it returns early on no checked head),
    /// compare with [`Self::differs`], since some findings (an equation not indexed at a
    /// symbol, an `IndexedAt` row, a constructor row without a rule) are read for every set of
    /// heads, the empty one included.
    #[must_use]
    pub fn differs_outside(&self, baseline: &Self, checked: Option<&BTreeSet<String>>) -> bool {
        self.outside(checked) != baseline.outside(checked)
    }

    /// Whether any finding differs between these facts (a claim-free mutant's) and `baseline`'s,
    /// by name, assumed or not: the comparison when the consistency gate read nothing (fz26
    /// KINK-BASELINE-FINDINGS review S1).
    #[must_use]
    pub fn differs(&self, baseline: &Self) -> bool {
        self.every() != baseline.every()
    }

    /// The identity ([`NamedFinding::identity`]) of every finding, sorted, repeats kept.
    fn every(&self) -> Vec<String> {
        let mut every = self
            .named()
            .map(|(finding, name, _)| identity(finding, name))
            .collect::<Vec<_>>();
        every.sort();
        every
    }

    /// The identity of every finding outside `checked`, sorted, repeats kept.
    fn outside(&self, checked: Option<&BTreeSet<String>>) -> Vec<String> {
        let mut outside = self
            .named()
            .filter(|(finding, _, _)| !self.reads(finding, checked))
            .map(|(finding, name, _)| identity(finding, name))
            .collect::<Vec<_>>();
        outside.sort();
        outside
    }

    /// Whether kink's consistency gate reads `finding` for the heads `checked`: a pair or an
    /// equation report with an equation of a checked head (a hook pair by its first equation
    /// alone, its second being the hook's written meaning), an equation not indexed at a symbol
    /// counting as every head's; an `IndexedAt` row always; an overload row of a checked symbol;
    /// a constructor-headed or injection-headed row whose equation is checked or that names none.
    pub(crate) fn reads(&self, finding: &Finding, checked: Option<&BTreeSet<String>>) -> bool {
        let checked_symbol = |name: &str| checked.is_none_or(|heads| heads.contains(name));
        let checked_rule = |rule: &RewriteRule| match self.index_of.get(&rule.attributes.unique_id)
        {
            Some(TermIndex::Symbol(name)) => checked_symbol(name),
            // An equation not indexed at a symbol (at a conjunction, a domain value, a collection
            // or a bare variable) could be offered at a head's application: every head's.
            _ => true,
        };
        match finding {
            Finding::Pair { pair, .. } | Finding::Equation(pair) => {
                checked_rule(&pair.first) || (pair.hook.is_none() && checked_rule(&pair.second))
            }
            Finding::Precondition(violation) => match &violation.kind {
                ViolationKind::IndexedAt(_) => true,
                ViolationKind::OverloadShape(symbol)
                | ViolationKind::PinnedByInjectiveTotal(symbol) => checked_symbol(symbol),
                ViolationKind::NoLeastCommonOverload(left, right) => {
                    checked_symbol(left) || checked_symbol(right)
                }
                ViolationKind::ConstructorHeaded(_) | ViolationKind::InjectionHeaded => {
                    violation.rule.as_deref().is_none_or(checked_rule)
                }
            },
        }
    }

    /// `{assume_joined, has_data, incomplete, findings}`: what a document prints, names in the
    /// front end's spelling.
    #[must_use]
    pub fn value(&self) -> Value {
        json!({
            "assume_joined": self
                .assume_joined
                .iter()
                .map(|name| self.spelling.spelled(name))
                .collect::<Vec<_>>(),
            "has_data": self.has_data(),
            "incomplete": self.incomplete(),
            "findings": self.findings().iter().map(NamedFinding::value).collect::<Vec<_>>(),
        })
    }
}

/// Whether k-rust's check skips `rule`: restricted to symbolic instances, it is never a step on
/// a ground term (`confluence.rs` `symbolic`).
pub(crate) fn symbolic(rule: &RewriteRule) -> bool {
    match &rule.attributes.concreteness {
        Concreteness::Unconstrained => false,
        Concreteness::All(kind) => *kind == ConstraintKind::Symbolic,
        Concreteness::Some(constraints) => constraints
            .values()
            .any(|kind| *kind == ConstraintKind::Symbolic),
    }
}

/// The version of what kink admits as a compared end (TV-01), [`data_ends`] and the
/// terminal-value walk it parameterizes (`step_events::ObservationDecider::terminal_value`): v1
/// (fz26 KINK-OVERLOAD-VALUE) admits an instance-normal application of an overload data head
/// where k-rust's [`BackendDefinition::is_data`] holds, and judges every compared end of a pair
/// under the other side's definition too, so an end that is not data there makes its slot
/// unknown for that pair. v2 (fz26 KRUST-ANYWHERE-HEAD) reads k-rust's wider data heads: also an
/// `anywhere` production whose equations are plain `anywhere` equations (SIMPLE's `_[_]`), when
/// it is declared total or `value-production` and has no hook, lemma or ceil equation, so an
/// end holding an instance-normal `a[4]` is now compared; and it drops an overload head declared
/// neither total nor `value-production` (hand-written KORE only), whose irreducible applications
/// need not be elements. The walk itself is unchanged; the heads it delegates to moved. A
/// component of kink's semantics identity (kink-campaign `identity`, key `terminal_value`): it
/// changes which slots compare, so a verdict. Bump it whenever what the walk admits changes.
/// v3 (kink27 R5-BYTES-ENDS): a domain value of a sort hooked `BYTES.Bytes` has a trusted
/// injective codec, its payload in its sort's stored form, so an end holding one (a cell, a Map
/// key or value, a List or Set element) is compared. The same codec admits it in step-event
/// patterns, configuration existence and shared feasibility.
pub const TERMINAL_VALUE_VERSION: &str = "kink-native/terminal-value/v3";

/// Which ends of runs on a definition are data under it ([`data_ends`]).
#[derive(Clone, Copy, Debug)]
pub enum DataEnds<'f> {
    /// Every end kink's terminal-value walk admits (TV-01: free constructors, normal-form
    /// injections, identity-safe domain values and trusted natural collections, and the
    /// applications of these data heads where k-rust's data judgement holds,
    /// [`Self::overload_application_is_data`]): such a term is a normal form free of `M+`'s
    /// constants, and distinct such normal forms differ in `M+`, a model of the definition under
    /// A1+.
    Admitted(&'f DataHeads),
    /// None: a finding is left (or the check is incomplete), so `M+` is not shown to be a model
    /// and the definition may identify any two ends.
    None,
}

impl DataEnds<'_> {
    /// Whether `symbol` (a KORE symbol name) is one of the definition's data heads
    /// (k-rust-backend `data_term`, "The class"). None is when no end is data.
    #[must_use]
    pub fn overload_head(&self, symbol: &str) -> bool {
        match self {
            Self::Admitted(heads) => heads.names().any(|name| &**name == symbol),
            Self::None => false,
        }
    }

    /// Whether `application`, a ground application of a data head
    /// ([`Self::overload_head`]) on a definition `definition` whose facts gave `self`, is data
    /// there: it internalizes in `definition` and k-rust's [`BackendDefinition::is_data`] holds
    /// with the definition's own heads, which reads instance-normality from the evaluator's own
    /// matcher, subsort order and overload axioms (no second matcher in kink). It judges the whole
    /// subterm, so the walk calls it once, at the outermost such application, and walks its
    /// arguments for the rest of TV-01 (identity-safe domain values, normal-form injections). A
    /// term with a variable, a symbol `definition` lacks, or any failure is not data.
    ///
    /// The internalization and `is_data` descend once per level of `application` on the caller's
    /// stack; a caller judging a term as deep as a leaf gives it the stack k-rust sizes for an
    /// operation over it, as `step_events::ObservationDecider` does.
    #[must_use]
    pub fn overload_application_is_data(
        &self,
        definition: &BackendDefinition,
        application: &Pattern,
    ) -> bool {
        let Self::Admitted(heads) = self else {
            return false;
        };
        application.free_variables().is_empty()
            && definition
                .admit_unverified(application, &[])
                .internalize_term()
                .is_ok_and(|term| definition.is_data(&term, heads))
    }
}

/// Two judgements are equal when they admit the same ends of one definition: both none, or the
/// same data heads.
impl PartialEq for DataEnds<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::None, Self::None) => true,
            (Self::Admitted(left), Self::Admitted(right)) => left.names().eq(right.names()),
            _ => false,
        }
    }
}

impl Eq for DataEnds<'_> {}

/// Which ends of runs on a definition are data under it, from that definition's own facts `own`
/// (fz26 KINK-BASELINE-FINDINGS part 2, extended by KINK-OVERLOAD-VALUE): none while a finding is
/// left or the check is incomplete ([`DataFacts::has_data`]); otherwise every end the terminal-value walk admits, with the instance-normal
/// applications of the definition's data heads where k-rust's data judgement holds
/// (`step_events::ObservationDecider::judging_data` takes the result). This is the one place that
/// says it.
///
/// A kill counts only when both sides' compared ends are data under *both* definitions (k-rust-
/// backend `data_term`, "Two definitions"): each definition reads the ends with its own theory,
/// and the two may differ on any symbol (a mutant can make a baseline constructor an `anywhere`
/// head, or add an overload member that lowers a baseline normal form). Each side's ends are
/// judged under its own definition with this function's result for its own facts when the run is
/// judged (a baseline's facts, a claim-free mutant's facts), and under the other side's
/// definition with the result for the other side's facts before the pair's slots are compared
/// (kink-campaign `runner`): for a constructor-only end that is a head-role and injection check.
/// So two different compared ends differ in each definition's initial model, under premises A1+
/// (evaluation by the executable and witness equations terminates over `M+`'s constants, which
/// implies A1, evaluation terminates) and A2 (lemmas and `[symbolic]` equations are theorems of the
/// executable equations; the baseline's claims are trusted, a mutant's that its edit unbacks are
/// removed).
#[must_use]
pub fn data_ends(own: &DataFacts) -> DataEnds<'_> {
    if own.has_data() {
        DataEnds::Admitted(own.heads())
    } else {
        DataEnds::None
    }
}
