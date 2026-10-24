//! What a definition's full critical-pair check says about the ends of runs on it (fz26
//! KINK-BASELINE-FINDINGS, finding KINK-BASELINE-TRUST).
//!
//! kink's kill is "relative to the definition, not to k-rust's model of it" (README, "What a
//! kill trusts"): a compared end is the value of a term in the definition's initial model, and two
//! ends differ only if no model of the definition identifies them. k-rust reads a definition by
//! its normal-form model `M_NF`, which is a model of the definition when evaluation terminates and
//! the critical pairs of its executable equations join (k-rust-backend `data_term`, "What a data
//! term denotes"). The baseline's pairs were a trusted premise ("which the backend checks",
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
//! counts no kill on it. A finding is assumed only by name, as k-rust-fuzz assumes one, through
//! k-rust-backend's one renderer (`data_term::names`, with the K label decoder [`label`]), so a
//! name the fuzz prints is a name kink reads. A decided finding ([`Finding::is_decided`]) cannot be
//! assumed: [`DataFacts::refused_names`] says so, as it says when a name matches no finding or
//! more than one.
//!
//! The mutant's facts are compared with the baseline's ([`DataFacts::differs_outside`]): a finding
//! of the claim-free mutant outside the heads its edit can change should be the baseline's
//! (`consistency`: such a pair is normalized with the baseline's equations alone), and kink checks
//! that, by name and by the unique ids of its equations, instead of arguing it.
//!
//! [`CheckScope::All`]: k_rust_backend::confluence::CheckScope::All

use std::collections::{BTreeMap, BTreeSet};

use k_rust_backend::{
    confluence::ViolationKind,
    data_term::{DataHeads, Finding, names},
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
pub const DATA_FACTS_VERSION: &str = "kink-native/data-facts/v1";

/// The K label a KORE symbol name encodes (the name itself when it does not decode): how every
/// finding name writes a symbol (k-rust-backend `data_term::names`). It is k-rust's
/// `kast::identifier::label_or_name`, which k-rust-fuzz passes too.
#[must_use]
pub fn label(name: &str) -> String {
    k_rust::kast::identifier::label_or_name(name)
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

/// One finding of a definition's full check as kink states it.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct NamedFinding {
    /// Its name (k-rust-backend `data_term::names::finding_name`), which `assume_joined` takes;
    /// `None` for an equation with neither a position, an overloaded pair, a label nor an id.
    pub name: Option<String>,
    pub verdict: FindingVerdict,
    /// Whether an `assume_joined` name assumes it.
    pub assumed: bool,
    /// One line naming it (k-rust-backend `Finding::describe`).
    pub description: String,
    /// What identifies it across the baseline and a mutant: its kind, the unique ids of its
    /// equations (a root pair's sorted) and its position.
    pub identity: String,
}

impl NamedFinding {
    fn of(finding: &Finding, assumed: bool) -> Self {
        Self {
            name: names::finding_name(finding, label),
            verdict: FindingVerdict::of(finding),
            assumed,
            description: finding.describe(label),
            identity: identity(finding),
        }
    }

    /// `{name, verdict, assumed, description}`.
    #[must_use]
    pub fn value(&self) -> Value {
        json!({
            "name": self.name,
            "verdict": self.verdict.name(),
            "assumed": self.assumed,
            "description": self.description,
        })
    }
}

/// An equation as a finding's identity names it: its unique id, else its name.
fn equation_id(rule: &RewriteRule) -> String {
    rule.attributes
        .identifier()
        .map(str::to_owned)
        .or_else(|| names::rule_part(rule, label))
        .unwrap_or_else(|| rule.attributes.diagnostic_name(label))
}

fn identity(finding: &Finding) -> String {
    match finding {
        Finding::Pair { pair, .. } => {
            let mut ids = [equation_id(&pair.first), equation_id(&pair.second)];
            if pair.position.is_empty() {
                ids.sort();
            }
            format!(
                "pair:{},{}@{}",
                ids[0],
                ids[1],
                names::position_text(&pair.position)
            )
        }
        Finding::Equation(pair) => {
            format!(
                "{}:{}",
                names::equation_prefix(pair),
                equation_id(&pair.first)
            )
        }
        Finding::Precondition(violation) => format!(
            "precondition:{}:{}",
            names::precondition_kind(&violation.kind, label),
            violation
                .rule
                .as_deref()
                .map(equation_id)
                .unwrap_or_default()
        ),
    }
}

/// Why an `assume_joined` name is refused ([`DataFacts::refused_names`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NameRefusal {
    pub name: String,
    pub reason: String,
}

/// One definition's full critical-pair check as kink reads it: k-rust's [`DataHeads`] with the
/// author's assumed names applied, and what kink's consistency gate guards the check with (the
/// executable equations and root pairs of the definition the check ran on, and the index of each
/// equation).
#[derive(Clone, Debug)]
pub struct DataFacts {
    heads: DataHeads,
    assume_joined: Vec<String>,
    /// The unique id of each equation of the function theory, with its index.
    index_of: BTreeMap<String, TermIndex>,
    /// The executable equations of the function theory (the check skips `[symbolic]` ones).
    executable_equations: usize,
    /// The root pairs: two executable equations of one index and priority group.
    root_pairs: usize,
}

impl DataFacts {
    /// The facts of `definition` (the definition a backend selected for the main module, the one
    /// its runs execute on), every finding that one of `assume_joined` names assumed
    /// (`data_heads_assuming`; a decided finding never is). The full check costs about as much as
    /// the definition's load, so a caller computes this once per load.
    #[must_use]
    pub fn of(definition: &BackendDefinition, assume_joined: &[String]) -> Self {
        let mut heads = definition.data_heads();
        if !assume_joined.is_empty() {
            heads = definition.data_heads_assuming(&heads, |finding| {
                assume_joined
                    .iter()
                    .any(|given| names::names_finding(given, finding, label))
            });
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

    /// The names the facts were computed with.
    #[must_use]
    pub fn assume_joined(&self) -> &[String] {
        &self.assume_joined
    }

    /// Whether no finding is left and the check is complete ([`Self::incomplete`]): [`data_ends`]
    /// admits ends only then.
    #[must_use]
    pub fn has_data(&self) -> bool {
        self.heads.confluent() && self.incomplete().is_none()
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

    /// The findings no name assumes.
    #[must_use]
    pub fn unnamed(&self) -> Vec<NamedFinding> {
        self.heads
            .findings()
            .iter()
            .map(|finding| NamedFinding::of(finding, false))
            .collect()
    }

    /// Every finding, the assumed ones marked, in k-rust's order (the unassumed first).
    #[must_use]
    pub fn findings(&self) -> Vec<NamedFinding> {
        self.unnamed()
            .into_iter()
            .chain(
                self.heads
                    .assumed()
                    .iter()
                    .map(|finding| NamedFinding::of(finding, true)),
            )
            .collect()
    }

    /// The names of [`Self::assume_joined`] this definition refuses: a name that matches no
    /// finding, more than one finding (the hook pairs of one equation are one finding), or a
    /// decided finding, which is a fact about the definition as written.
    #[must_use]
    pub fn refused_names(&self) -> Vec<NameRefusal> {
        let all = self
            .heads
            .findings()
            .iter()
            .chain(self.heads.assumed())
            .collect::<Vec<_>>();
        let mut refused = Vec::new();
        for given in &self.assume_joined {
            let matched = all
                .iter()
                .filter(|finding| names::names_finding(given, finding, label))
                .collect::<Vec<_>>();
            let identities = matched
                .iter()
                .map(|finding| identity(finding))
                .collect::<BTreeSet<_>>();
            let reason = if matched.is_empty()
                && (given.starts_with("baseline:") || given.starts_with("mutant:"))
            {
                Some(
                    "kink names the baseline's findings without a side prefix (`baseline:` and \
                     `mutant:` are k-rust-fuzz's): the claim-free mutant's are checked equal to \
                     the baseline's, and every name applies to both"
                        .to_owned(),
                )
            } else if matched.is_empty() {
                Some("it names no finding of the definition's full critical-pair check".to_owned())
            } else if let Some(decided) = matched.iter().find(|finding| finding.is_decided()) {
                Some(format!(
                    "it names a decided finding ({}), a fact about the definition as written that \
                     no premise removes",
                    decided.describe(label)
                ))
            } else if identities.len() > 1 {
                Some(format!(
                    "it names {} findings; name one: {}",
                    identities.len(),
                    matched
                        .iter()
                        .filter_map(|finding| names::finding_name(finding, label))
                        .collect::<BTreeSet<_>>()
                        .into_iter()
                        .collect::<Vec<_>>()
                        .join(", ")
                ))
            } else {
                None
            };
            if let Some(reason) = reason {
                refused.push(NameRefusal {
                    name: given.clone(),
                    reason,
                });
            }
        }
        refused
    }

    /// Whether the findings outside `checked` (KORE symbol names; `None` for every head, so
    /// every finding is inside) differ between these facts (a claim-free mutant's) and
    /// `baseline`'s, by identity and name, assumed or not. A finding is inside when kink's
    /// consistency gate reads it for those heads (`consistency`), with each side's own index of
    /// its equations. Only for a gate that ran: when it read nothing (it returns early on no
    /// checked head), compare with [`Self::differs`], since some findings (an equation not indexed
    /// at a symbol, an `IndexedAt` row, a constructor row without a rule) are read for every set
    /// of heads, the empty one included.
    #[must_use]
    pub fn differs_outside(&self, baseline: &Self, checked: Option<&BTreeSet<String>>) -> bool {
        self.outside(checked) != baseline.outside(checked)
    }

    /// Whether any finding differs between these facts (a claim-free mutant's) and `baseline`'s,
    /// by identity and name, assumed or not: the comparison when the consistency gate read
    /// nothing (fz26 KINK-BASELINE-FINDINGS review S1).
    #[must_use]
    pub fn differs(&self, baseline: &Self) -> bool {
        self.every() != baseline.every()
    }

    /// `(identity, name)` of every finding, sorted, repeats kept.
    fn every(&self) -> Vec<(String, Option<String>)> {
        let mut every = self
            .heads
            .findings()
            .iter()
            .chain(self.heads.assumed())
            .map(|finding| (identity(finding), names::finding_name(finding, label)))
            .collect::<Vec<_>>();
        every.sort();
        every
    }

    /// `(identity, name)` of every finding outside `checked`, sorted, repeats kept.
    fn outside(&self, checked: Option<&BTreeSet<String>>) -> Vec<(String, Option<String>)> {
        let mut outside = self
            .heads
            .findings()
            .iter()
            .chain(self.heads.assumed())
            .filter(|finding| !self.reads(finding, checked))
            .map(|finding| (identity(finding), names::finding_name(finding, label)))
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

    /// `{assume_joined, has_data, incomplete, findings}`: what a document prints.
    #[must_use]
    pub fn value(&self) -> Value {
        json!({
            "assume_joined": self.assume_joined,
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

/// Which ends of runs on a definition are data under it ([`data_ends`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DataEnds {
    /// Every end kink's terminal-value walk admits (TV-01: free constructors, normal-form
    /// injections, identity-safe domain values and trusted natural collections): such a term is
    /// a normal form, and distinct normal forms differ in `M_NF`, a model of the definition.
    Admitted,
    /// None: a finding is left (or the check is incomplete), so `M_NF` is not shown to be a model
    /// and the definition may identify any two ends.
    None,
}

/// Which ends of runs on a definition are data under it, from that definition's own facts `own`
/// (fz26 KINK-BASELINE-FINDINGS part 2): every end the terminal-value walk admits when no finding
/// is left and the check is complete ([`DataFacts::has_data`]), and none otherwise. A kill counts
/// only when both sides' compared ends are data, each under its own side's definition. This is the one place that says it: KINK-OVERLOAD-VALUE
/// extends this function (instance-normal overload applications, `BackendDefinition::is_data`,
/// and each end judged under the other side's definition too) rather than adding another.
#[must_use]
pub fn data_ends(own: &DataFacts) -> DataEnds {
    if own.has_data() {
        DataEnds::Admitted
    } else {
        DataEnds::None
    }
}
