//! Coverage chooses test order only; it does not supply an oracle outcome.
//!
//! A mutant's tests run in two groups: first the tests whose baseline run's coverage witnesses an
//! edited site ([`coverage_selected`]), then the rest, each group in manifest order. No test is
//! ever left out (`deselected` is always empty), so, while no wall-clock bound fires, the order
//! decides only which killing test is found first under `FirstKill` and what the run costs, never
//! a status (a run near its time bound can time out in one order and finish in another: review
//! L2-1-tail-1 D2), in the no-Z3 profile and under Z3 with a solver bounded by resource units.
//! That premise is that each test's outcome does not depend on the tests run before it, which
//! k-rust's Execute promise gives without Z3, and under Z3 for a backend whose queries are
//! bounded by Z3 resource units (kink-native `BACKEND_OPTIONS`, the runner's default), whose
//! answers are functions of the query, the units and the Z3 build. Under a solver that the clock
//! bounds, an SMT query can time out, and the mutant's backend and the baseline's are reused for
//! every test in schedule order and keep a cache of satisfiability answers across requests
//! (k-rust `docs/compatibility.md`, Execute), so a test may get an answer after another test
//! warmed the cache where it times out when run first: the order can move a status between
//! `Killed`, `Unknown` and `Survived` (the warmed answer can make the test kill or agree, and
//! with no kill the fold reads `Survived` where the timeout reads `Unknown`; review L2-1-tail-1
//! D1). It never makes a false kill, since a kill is still a proved `Distinguish` (re-pin
//! L2-1-tail, review L2-1-1 D4; `tests/selection.rs`'s Theorem 2 assumes that no wall-clock
//! bound fires, and a Z3 query timeout is one).
//!
//! A run witnesses an edit when it could observe a difference the edit makes. What witnesses an
//! edit ([`CompiledEdit::between`], re-pin L2-1, findings D-01 and D-03):
//! - a rewrite rule edit confined to its right-hand side or `ensures`: a run that applied the
//!   rule (k-rust `applied`). The rule keeps its left-hand side, `requires` and attributes, so it
//!   is tried, matched and decided at every state as before, and only what it builds differs,
//!   which a run sees only where the step built a candidate of it;
//! - every other site-local rewrite rule edit (its `requires`, its left-hand side, an attribute,
//!   a deletion, or one whose edited form cannot be paired with it): a run that began to decide
//!   its condition (`matched`, which contains `applied`). Each changes whether the rule takes a
//!   step from a state its left-hand side matches, not only what the step builds:
//!   - an edit of the `requires` or the left-hand side changes the guard or the bindings it is
//!     decided under, so a run that matched the rule and refuted its old guard can take the
//!     edited rule's step;
//!   - an attribute edit keeps the left-hand side and the guard, and a deletion only takes the
//!     rule away. At a state where the guard was refuted, the rule takes no step and
//!     blocks no lower priority group wherever it is placed, or whether it exists, so the run is
//!     the same there; the runs that can observe the edit at a state the rule matched are those
//!     that applied it and those that left its guard undecided (which blocks the lower priority
//!     groups). k-rust's `matched` holds the rule whatever its guard's verdict, so it cannot
//!     tell an undecided guard from a refuted one, and `matched` is the smallest recorded
//!     superset of those runs;
//!   - an edit that pairs no one removed axiom with one added axiom is not shown to keep the
//!     left-hand side, so it is read as a left-hand side edit.
//!
//!   A widened left-hand side, or an attribute edit that raises the rule in its site's trial
//!   order (a higher priority, a removed `owise`), can also observe a state where the old rule
//!   was not tried or its match was left undecided, and a deletion, or an attribute edit that
//!   lowers the rule (a lower priority, an added `owise`), a state where its match was left
//!   undecided, since such a match blocks the lower priority groups of its site: k-rust's lists
//!   reach no left-hand side edit there, and an attribute edit or a deletion only through
//!   `offered`, which kink does not collect. Such a run is no witness, and runs after the
//!   witnesses;
//! - an equation edit confined to its `requires`, or to its `requires` and its right-hand side
//!   or `ensures`: a run that matched the equation; confined to its right-hand side or
//!   `ensures`: a run that applied it;
//! - every other edit selects every test (`global`, the fallback order): an equation edit of its
//!   left-hand side, of an attribute (priority, owise, concrete/symbolic, simplification, ...),
//!   of an `smt-lemma` axiom or of an equation that carries `owise`, `concrete` or `symbolic`
//!   (findings D-03: a set-aside instance with an empty `requires` is not counted); a removed or
//!   inserted equation; a changed declaration, claim, macro, syntax or rewrite order.
//!
//! kink-flow's kill search reads the same classification ([`CompiledEdit::witness`]) over the
//! coverage its result records keep by baseline sentence, ordering each mutant's programs once it
//! compiles (`run_campaign_multi_ordered`). Its programs are ground, and it reads the edit as a
//! ground test witnesses it ([`CompiledEdit::for_ground_tests`]): the definedness claims kink
//! withdraws from the mutant (`total`, `functional`, `preserves-definedness`) are a change of
//! the declarations, which the claim-free side's edit reads as `global`, but no ground test can
//! tell the two definitions apart through them alone, so that edit is the author's patch, the
//! mutant as written against the baseline.
//!
//! k-rust's sets are no over-approximation of what can affect a result (a higher-priority rule
//! that failed to match is absent, though its failure lets the owise rule fire), so a test that
//! does not witness an edit may still kill it; it only runs later.

use std::collections::{BTreeMap, BTreeSet};

use k_rust::{
    backend::{ExecutionRole, execution_role},
    definition::AttributeKey,
    kore::{
        ast::{Attributes, Definition, Pattern, Sentence},
        parser::parse_definition,
    },
    names::KoreAttribute,
};
use kink_native::{
    ValidatedDefinition,
    coverage::{Authorship, RuleAuthors, TestCoverage},
};
use kink_patch::{SentenceRef, Withdrawal};
use serde_json::{Value, json};

/// The campaign's test scheduling policy.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum SelectionPolicy {
    #[default]
    None,
    Prioritize(Sel),
}

/// Coverage key and domain are fixed in this version.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Sel {
    pub coupled: Coupled,
}

/// Whether coverage of any edited site or every edited site comes first.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Coupled {
    #[default]
    Union,
    AllSites,
}

impl SelectionPolicy {
    /// The exact manifest declaration; replay rebuilds scheduling from this input.
    #[must_use]
    pub fn value(self) -> Value {
        match self {
            Self::None => json!("none"),
            Self::Prioritize(selection) => json!({"prioritize": {
                "key": "compiled-rule-ids",
                "coupled": match selection.coupled {
                    Coupled::Union => "union",
                    Coupled::AllSites => "all-sites",
                },
                "coverage": kink_native::coverage::COVERAGE_DOMAIN,
            }}),
        }
    }
}

/// A compiled-side diff, computed for the actual side a test runs on.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompiledEdit {
    pub removed_rule_ids: BTreeSet<String>,
    pub global: bool,
    /// The removed ids a run witnesses by `matched` ([`TestCoverage::rule_ids`]): every removed
    /// rewrite rule id whose edit is not confined to its right-hand side or `ensures`, and every
    /// removed equation id whose edit changed its condition, alone or with its right-hand side or
    /// `ensures` (module doc). A run witnesses every other removed id by `applied`
    /// ([`TestCoverage::applied_ids`]). Empty when `global`.
    pub matched_ids: BTreeSet<String>,
}

impl CompiledEdit {
    /// Compares the baseline with a patched or claim-withdrawn side.
    ///
    /// Only removed and added axioms may differ, each changed equation paired one to one with
    /// its edited form by the baseline sentence behind it and changed only in its `requires`,
    /// right-hand side or `ensures` (module doc). Unparseable KORE, any other change, and
    /// additions without any removed identity select every test.
    #[must_use]
    pub fn between(baseline: &ValidatedDefinition, side: &ValidatedDefinition) -> Self {
        let left = baseline.artifacts();
        let right = side.artifacts();
        let baseline_ids = left
            .sentence_provenance
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>();
        let side_ids = right
            .sentence_provenance
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>();
        let removed_rule_ids = baseline_ids
            .difference(&side_ids)
            .cloned()
            .collect::<BTreeSet<_>>();
        let added = side_ids
            .difference(&baseline_ids)
            .cloned()
            .collect::<BTreeSet<_>>();
        let unchanged_order = left
            .execution_rewrite_order
            .iter()
            .filter(|id| !removed_rule_ids.contains(*id))
            .eq(right
                .execution_rewrite_order
                .iter()
                .filter(|id| !added.contains(*id)));
        let local = (baseline.compile_options() == side.compile_options()
            && left.configuration_variables == right.configuration_variables
            && left.syntax_definition_kore == right.syntax_definition_kore
            && left.macros_kore == right.macros_kore
            && unchanged_order
            && !(removed_rule_ids.is_empty() && !added.is_empty()))
        .then(|| {
            site_local(
                &left.definition_kore,
                &right.definition_kore,
                &removed_rule_ids,
                &added,
                &sentences_of(&RuleAuthors::of(baseline)),
                &sentences_of(&RuleAuthors::of(side)),
            )
        })
        .flatten();
        Self {
            removed_rule_ids,
            global: local.is_none(),
            matched_ids: local.unwrap_or_default(),
        }
    }

    /// Which coverage predicate witnesses the removed id `id` (module doc): `matched` for an id of
    /// [`Self::matched_ids`] (a rewrite rule edit that is not confined to its right-hand side or
    /// `ensures`, an equation edit that changed its condition), `applied` for every other removed
    /// id (an edit confined to its right-hand side or `ensures`). Meaningful only when the edit is
    /// not [`Self::global`], which every run witnesses.
    #[must_use]
    pub fn witness(&self, id: &str) -> Witness {
        if self.matched_ids.contains(id) {
            Witness::Matched
        } else {
            Witness::Applied
        }
    }

    /// Whether `coverage` witnesses the removed id `id` (module doc).
    fn witnessed(&self, coverage: &TestCoverage, id: &str) -> bool {
        match self.witness(id) {
            Witness::Matched => coverage.rule_ids.contains(id),
            Witness::Applied => coverage.applied_ids.contains(id),
        }
    }
}

/// The trusted claims that state only that terms are defined: a symbol's `total` and
/// `functional` (each of its applications to defined arguments is defined) and a rule's
/// `preserves-definedness` (its right-hand side is defined wherever its left-hand side is).
/// Their withdrawal from a mutant ([`kink_patch::ClaimSupport::withdraw`]) adds no ground
/// witness of its edit through coverage ([`CompiledEdit::for_ground_tests`]).
pub const DEFINEDNESS_CLAIMS: [AttributeKey; 3] = [
    AttributeKey::Total,
    AttributeKey::Functional,
    AttributeKey::PreservesDefinedness,
];

/// Whether a ground test witnesses a mutant's edit as the mutant as written gives it, given the
/// keys of the claims kink withdrew from it (`withdrawn_keys`, [`kink_patch::Claim::key`]):
/// when every withdrawn claim is one of [`DEFINEDNESS_CLAIMS`]
/// ([`CompiledEdit::for_ground_tests`]). With no claim withdrawn the two sides are one
/// definition, and both readings are the same edit.
#[must_use]
pub fn ground_reading_is_as_written<'k>(withdrawn_keys: impl IntoIterator<Item = &'k str>) -> bool {
    withdrawn_keys
        .into_iter()
        .all(|key| DEFINEDNESS_CLAIMS.iter().any(|claim| claim.as_str() == key))
}

impl CompiledEdit {
    /// The edit as a ground test witnesses it, given the mutant as written (`as_written`, the
    /// author's patch applied) and the claims kink withdrew from it (`claims`) to build the
    /// claim-free side every test runs on: the edit of `as_written` against `baseline` when
    /// every withdrawn claim is one of [`DEFINEDNESS_CLAIMS`] ([`ground_reading_is_as_written`]),
    /// else `None`, and the claim-free side's own edit ([`Self::between`]) is read instead.
    ///
    /// A ground test witnesses an edit when its run under the baseline uses a sentence the
    /// mutant changes, so that its run can tell the two apart. Withdrawing a definedness claim
    /// changes no sentence a run uses; it only takes away an answer k-rust reads when it asks
    /// whether a term is defined. Take a ground test whose baseline coverage is complete and
    /// reaches no sentence the patch changes. Its run under the claim-free mutant applies the
    /// baseline's sentences to the same terms and decides the same ground conditions, since
    /// nothing it uses differs. Each application its equations evaluate is defined because it
    /// equals the value they compute, which needs no claim. An application they leave
    /// unevaluated in a step's result contradicts a `total` or `functional` claim, a
    /// contradicted claim, or leaves a function application in an end, which is no data, on
    /// either side.
    ///
    /// One case escapes coverage: an application in an operand that a short-circuit operator
    /// skipped in the baseline run (the right operand of `orElseBool` after `true`, say) was
    /// trusted defined by the claim and never evaluated, so the test's coverage holds none of
    /// its equations. Without the claim, k-rust's strict reading must establish its definedness,
    /// and can do so through an equation the patch edited: where that equation now leaves the
    /// application undefined, the claim-free mutant's step is undefined where the baseline's
    /// was not. That run is judged as any run is (the withdrawal makes the symbol partial, so
    /// where the mutant's short-circuit analysis flags the rule that read the operand, the run
    /// is excluded as `short-circuit-reading`), but its coverage reaches no edited sentence, and
    /// it is no witness. So the withdrawal adds no witness through coverage, and a test it lets
    /// reach an edit in this way runs after the witnesses. Witnesses only order the tests and
    /// name a cached killer; every test still runs, so no status depends on the reading.
    ///
    /// The other withdrawn claims are not read so: an `injective`, `smt-hook`, `smtlib` or
    /// `smt-lemma` withdrawal changes how a step or a solver query is decided. A deleted
    /// `simplification` lemma removes a sentence, and a run that used the lemma then evaluates the
    /// terms it rewrote by their equations, which can reach an edited one. For these the
    /// claim-free side's edit stays the reading, as for a symbolic test, whose run can hold an
    /// application no equation evaluates wherever a claimed symbol is applied.
    #[must_use]
    pub fn for_ground_tests(
        baseline: &ValidatedDefinition,
        as_written: &ValidatedDefinition,
        claims: &Withdrawal,
    ) -> Option<Self> {
        ground_reading_is_as_written(claims.withdrawn.iter().map(|claim| claim.key.as_str()))
            .then(|| Self::between(baseline, as_written))
    }
}

/// The k-rust coverage predicate by which a run witnesses one removed id of a [`CompiledEdit`]
/// ([`CompiledEdit::witness`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Witness {
    /// The run began to decide a matched instance's condition (k-rust `matched`,
    /// [`TestCoverage::rule_ids`]).
    Matched,
    /// The run built a candidate of the axiom, defined or rolled back (k-rust `applied`,
    /// [`TestCoverage::applied_ids`]).
    Applied,
}

/// The regenerated per-mutant schedule. Prioritize has no deselected tests.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MutantSelection {
    pub policy: SelectionPolicy,
    pub order: Vec<String>,
    pub deselected: Vec<String>,
    pub global: bool,
    pub removed_rule_ids: BTreeSet<String>,
}

impl MutantSelection {
    /// The exact report value, with no policy duplicate.
    #[must_use]
    pub fn value(&self) -> Value {
        if self.policy == SelectionPolicy::None {
            return Value::Null;
        }
        json!({
            "order": self.order,
            "deselected": self.deselected,
            "global": self.global,
            "removed_rule_ids": self.removed_rule_ids,
        })
    }
}

/// Whether one test comes first. `site_groups` contains the baseline identities
/// authored by each edited site, intersected with this actual side's removed ids.
/// The caller handles the campaign-wide empty-selection fallback.
#[must_use]
pub fn coverage_selected(
    coverage: &TestCoverage,
    edit: &CompiledEdit,
    coupled: Coupled,
    site_groups: &[BTreeSet<String>],
) -> bool {
    if !coverage.complete || edit.global {
        return true;
    }
    match coupled {
        Coupled::Union => edit
            .removed_rule_ids
            .iter()
            .any(|id| edit.witnessed(coverage, id)),
        Coupled::AllSites => {
            !site_groups.is_empty()
                && site_groups
                    .iter()
                    .all(|ids| ids.iter().any(|id| edit.witnessed(coverage, id)))
        }
    }
}

/// One changed `UNIQUE_ID` axiom of `definition_kore`.
struct Changed {
    parameters: Vec<String>,
    pattern: Pattern,
    /// Its attributes without `UNIQUE_ID` and the origin attributes.
    attributes: Vec<Pattern>,
    rewrite: bool,
}

/// What changed between a removed axiom and its edited form.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Change {
    /// Only the `requires`.
    Condition,
    /// Only the right-hand side and `ensures`.
    Result,
    /// The `requires` and the right-hand side or `ensures`.
    Both,
    /// Anything else: a left-hand side, an attribute, a sort, the axiom's shape.
    Other,
}

/// The baseline sentences behind an id of one side, for pairing a removed axiom with its edited
/// form; `None` for an id with no baseline sentence.
fn sentences_of(authors: &RuleAuthors) -> impl Fn(&str) -> Option<BTreeSet<SentenceRef>> + '_ {
    move |id| match authors.get(id) {
        Some(Authorship::Sentences(sentences)) => Some(sentences.clone()),
        Some(Authorship::Unmapped(_)) | None => None,
    }
}

/// The removed ids a run witnesses by `matched` ([`CompiledEdit::matched_ids`]), when every
/// change between the two definitions is site-local (module doc); `None` when the edit must
/// select every test.
/// `baseline_author` and `side_author` give the baseline sentences behind a removed and an added
/// id, which pair each changed equation with its edited form.
fn site_local(
    left: &str,
    right: &str,
    removed: &BTreeSet<String>,
    added: &BTreeSet<String>,
    baseline_author: &dyn Fn(&str) -> Option<BTreeSet<SentenceRef>>,
    side_author: &dyn Fn(&str) -> Option<BTreeSet<SentenceRef>>,
) -> Option<BTreeSet<String>> {
    let (Ok(mut left), Ok(mut right)) = (parse_definition(left), parse_definition(right)) else {
        return None;
    };
    let removed_axioms = take_changed(&mut left, removed)?;
    let added_axioms = take_changed(&mut right, added)?;
    if left != right {
        return None;
    }
    let mut matched = BTreeSet::new();
    // The changed axioms of each baseline sentence set: (removed, added).
    let mut groups = BTreeMap::<BTreeSet<SentenceRef>, (Vec<&str>, Vec<&str>)>::new();
    for id in removed {
        if let Some(sentences) = baseline_author(id) {
            groups.entry(sentences).or_default().0.push(id);
        } else if removed_axioms[id.as_str()].rewrite {
            // A rewrite rule with no baseline sentence has no edited form to pair it with, so
            // its edit is not shown to be confined to its result.
            matched.insert(id.clone());
        } else {
            return None;
        }
    }
    for id in added {
        if let Some(sentences) = side_author(id) {
            groups.entry(sentences).or_default().1.push(id);
        } else if !added_axioms[id.as_str()].rewrite {
            return None;
        }
    }
    for (old, new) in groups.values() {
        let pair = match (old.as_slice(), new.as_slice()) {
            ([old], [new]) => Some((&removed_axioms[*old], &added_axioms[*new])),
            _ => None,
        };
        let equation = old
            .iter()
            .map(|id| &removed_axioms[*id])
            .chain(new.iter().map(|id| &added_axioms[*id]))
            .any(|axiom| !axiom.rewrite);
        if !equation {
            // A rewrite rule edit stays site-local whatever it changed. Only one paired with its
            // edited form and confined to its right-hand side or `ensures` is witnessed by
            // `applied`; every other (its `requires`, left-hand side or attributes, a deletion, an
            // edit that pairs no one removed axiom with one added axiom) changes whether the rule
            // takes a step from a state it matches, so it is witnessed by `matched` (module doc).
            let result_only = pair.is_some_and(|(old_axiom, new_axiom)| {
                change(old_axiom, new_axiom) == Change::Result
            });
            if !result_only {
                matched.extend(old.iter().map(|id| (*id).to_owned()));
            }
            continue;
        }
        let (old_axiom, new_axiom) = pair?;
        if !old_axiom.recorded_equation() || !new_axiom.recorded_equation() {
            return None;
        }
        match change(old_axiom, new_axiom) {
            Change::Result => {}
            Change::Condition | Change::Both if !old_axiom.sets_aside() => {
                matched.insert(old[0].to_owned());
            }
            Change::Condition | Change::Both | Change::Other => return None,
        }
    }
    Some(matched)
}

impl Changed {
    /// An equation that k-rust's coverage records and whose instances it decides like any other:
    /// not an `smt-lemma` axiom (no recording site) and not an `owise` equation (its condition
    /// is the negation of its competitors').
    fn recorded_equation(&self) -> bool {
        !self.rewrite
            && !self.attributes.iter().any(|attribute| {
                named(attribute, KoreAttribute::SmtLemma) || named(attribute, KoreAttribute::Owise)
            })
    }

    /// The equation carries `concrete` or `symbolic`: an instance it sets aside with an empty
    /// `requires` is neither decided nor counted (findings D-03).
    fn sets_aside(&self) -> bool {
        self.attributes.iter().any(|attribute| {
            named(attribute, KoreAttribute::Concrete) || named(attribute, KoreAttribute::Symbolic)
        })
    }
}

fn named(pattern: &Pattern, attribute: KoreAttribute) -> bool {
    matches!(pattern, Pattern::Application { symbol, .. } if symbol.name == attribute.as_str())
}

/// The condition, the result and the rest of an axiom: a rewrite rule
/// `\rewrites(\and(lhs, requires), right)`, a function equation
/// `\implies(\and(requires, matches), \equals(f(X...), \and(rhs, ensures)))`, and a direct
/// equation `\implies(requires, \equals(lhs, \and(rhs, ensures)))` (k-rust's emitter;
/// `requires` is `\top` or `\equals(.., true)`). `None` for any other shape.
fn parts(axiom: &Changed) -> Option<(&Pattern, &Pattern, Pattern)> {
    let placeholder = || Pattern::String("".into());
    match &axiom.pattern {
        Pattern::Rewrites { sort, left, right } if axiom.rewrite => match left.as_ref() {
            Pattern::And {
                sort: and_sort,
                arguments,
            } if arguments.len() == 2 => Some((
                &arguments[1],
                right.as_ref(),
                Pattern::Rewrites {
                    sort: sort.clone(),
                    left: Box::new(Pattern::And {
                        sort: and_sort.clone(),
                        arguments: vec![arguments[0].clone(), placeholder()],
                    }),
                    right: Box::new(placeholder()),
                },
            )),
            _ => None,
        },
        Pattern::Implies { sort, left, right } if !axiom.rewrite => {
            let Pattern::Equals {
                operand_sort,
                result_sort,
                left: head,
                right: result,
            } = right.as_ref()
            else {
                return None;
            };
            let (condition, condition_rest) = match left.as_ref() {
                Pattern::And {
                    sort: and_sort,
                    arguments,
                } if arguments.len() == 2 => (
                    &arguments[0],
                    Pattern::And {
                        sort: and_sort.clone(),
                        arguments: vec![placeholder(), arguments[1].clone()],
                    },
                ),
                condition @ (Pattern::Top { .. } | Pattern::Equals { .. }) => {
                    (condition, placeholder())
                }
                _ => return None,
            };
            Some((
                condition,
                result.as_ref(),
                Pattern::Implies {
                    sort: sort.clone(),
                    left: Box::new(condition_rest),
                    right: Box::new(Pattern::Equals {
                        operand_sort: operand_sort.clone(),
                        result_sort: result_sort.clone(),
                        left: head.clone(),
                        right: Box::new(placeholder()),
                    }),
                },
            ))
        }
        _ => None,
    }
}

fn change(old: &Changed, new: &Changed) -> Change {
    if old.rewrite != new.rewrite
        || old.parameters != new.parameters
        || old.attributes != new.attributes
    {
        return Change::Other;
    }
    let (Some((old_condition, old_result, old_rest)), Some((new_condition, new_result, new_rest))) =
        (parts(old), parts(new))
    else {
        return Change::Other;
    };
    if old_rest != new_rest {
        return Change::Other;
    }
    match (old_condition != new_condition, old_result != new_result) {
        (true, false) => Change::Condition,
        (false, true) => Change::Result,
        (true, true) => Change::Both,
        (false, false) => Change::Other,
    }
}

fn rule_identity(attributes: &Attributes) -> Option<&str> {
    attributes.0.iter().find_map(|attribute| match attribute {
        Pattern::Application { symbol, arguments }
            if symbol.name == KoreAttribute::UniqueId.as_str() =>
        {
            let [Pattern::String(id)] = arguments.as_slice() else {
                return None;
            };
            id.as_utf8().ok()
        }
        _ => None,
    })
}

/// Removes every axiom whose id is in `changed` from `definition` and returns them by id; `None`
/// when a changed id names a claim or no axiom of `definition_kore` (a macro, alias or claim
/// id), or two axioms.
fn take_changed(
    definition: &mut Definition,
    changed: &BTreeSet<String>,
) -> Option<BTreeMap<String, Changed>> {
    let mut taken = BTreeMap::new();
    let mut claims = false;
    let mut twice = false;
    for module in &mut definition.modules {
        module.sentences.retain(|sentence| {
            let (attributes, axiom) = match sentence {
                Sentence::Axiom {
                    parameters,
                    pattern,
                    attributes,
                } => (attributes, Some((parameters, pattern))),
                Sentence::Claim { attributes, .. } => (attributes, None),
                _ => return true,
            };
            let Some(id) = rule_identity(attributes).filter(|id| changed.contains(*id)) else {
                return true;
            };
            let Some((parameters, pattern)) = axiom else {
                claims = true;
                return true;
            };
            let entry = Changed {
                parameters: parameters.clone(),
                pattern: pattern.as_ref().clone(),
                attributes: attributes
                    .0
                    .iter()
                    .filter(|attribute| {
                        !named(attribute, KoreAttribute::UniqueId)
                            && !KoreAttribute::ALL.iter().any(|origin| {
                                execution_role(*origin) == ExecutionRole::Origin
                                    && named(attribute, *origin)
                            })
                    })
                    .cloned()
                    .collect(),
                rewrite: matches!(pattern.as_ref(), Pattern::Rewrites { .. }),
            };
            twice |= taken.insert(id.to_owned(), entry).is_some();
            false
        });
    }
    (!claims && !twice && taken.len() == changed.len()).then_some(taken)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kore(body: &str) -> String {
        format!("[]\nmodule M\n{body}\nendmodule []")
    }

    const ID: &str = "UNIQUE'Unds'ID";

    /// A rewrite `a => <right> requires <requires>`.
    fn rewrite(id: &str, right: &str, requires: &str) -> String {
        format!(
            r#"axiom{{}} \rewrites{{S{{}}}}(\and{{S{{}}}}(a{{}}(), {requires}), {right}) [{ID}{{}}("{id}")]"#
        )
    }

    /// A function equation `f(X) = <right> requires <requires>` with the given attributes.
    fn equation(id: &str, right: &str, requires: &str, attributes: &str) -> String {
        format!(
            r#"axiom{{R}} \implies{{R}}(\and{{R}}({requires}, \in{{S{{}},R}}(X0:S{{}}, a{{}}())), \equals{{S{{}},R}}(f{{}}(X0:S{{}}), \and{{S{{}}}}({right}, \top{{S{{}}}}()))) [{ID}{{}}("{id}"){attributes}]"#
        )
    }

    fn ids(ids: &[&str]) -> BTreeSet<String> {
        ids.iter().map(|id| (*id).to_owned()).collect()
    }

    /// The removed axioms' condition ids for one removed and one added axiom of one sentence,
    /// or `None` when the edit is global.
    fn local(old: &str, new: &str) -> Option<BTreeSet<String>> {
        let one = |_: &str| Some(BTreeSet::from([SentenceRef::new("M", 0)]));
        site_local(
            &kore(old),
            &kore(new),
            &ids(&["old"]),
            &ids(&["new"]),
            &one,
            &one,
        )
    }

    const TOP: &str = r"\top{S{}}()";
    const COND: &str = r#"\equals{SortBool{},S{}}(c{}(), \dv{SortBool{}}("true"))"#;
    const ECOND: &str = r#"\equals{SortBool{},R}(c{}(), \dv{SortBool{}}("true"))"#;

    /// A ground test reads the mutant as written's edit exactly when every withdrawn claim is a
    /// definedness claim; any other withdrawn claim, alone or beside one, keeps the claim-free
    /// side's edit, since its withdrawal changes how a run is decided.
    #[test]
    fn only_definedness_withdrawals_read_the_mutant_as_written() {
        let definedness = ["total", "functional", "preserves-definedness"];
        for key in definedness {
            assert!(ground_reading_is_as_written([key]), "{key}");
        }
        assert!(ground_reading_is_as_written(definedness));
        assert!(ground_reading_is_as_written([]), "no claim withdrawn");
        for key in [
            "injective",
            "smt-hook",
            "smtlib",
            "smt-lemma",
            "simplification",
        ] {
            assert!(!ground_reading_is_as_written([key]), "{key}");
            assert!(
                !ground_reading_is_as_written(["total", key]),
                "total and {key}"
            );
            assert!(
                !ground_reading_is_as_written([key, "preserves-definedness"]),
                "{key} and preserves-definedness"
            );
        }
    }

    #[test]
    fn a_changed_rewrite_is_site_local_and_only_a_result_only_change_is_witnessed_by_applied() {
        assert_eq!(
            local(&rewrite("old", "b{}()", TOP), &rewrite("new", "c{}()", TOP)),
            Some(BTreeSet::new()),
            "right-hand side: applied"
        );
        assert_eq!(
            local(
                &rewrite("old", "b{}()", COND),
                &rewrite("new", &format!(r"\and{{S{{}}}}(b{{}}(), {COND})"), COND)
            ),
            Some(BTreeSet::new()),
            "ensures: applied"
        );
        // A left-hand side edit changes the bindings the guard is decided under, so a run that
        // matched the rule and refuted its guard can take the edited rule's step; an attribute
        // edit is observed where the guard was left undecided, which `matched` holds and
        // `applied` does not. Either is witnessed by `matched`, not `applied` alone.
        let lhs = rewrite("new", "b{}()", COND).replace(r"(a{}(), ", r"(d{}(), ");
        assert_eq!(
            local(&rewrite("old", "b{}()", COND), &lhs),
            Some(ids(&["old"])),
            "left-hand side: matched"
        );
        let lhs_and_requires = rewrite("new", "b{}()", TOP).replace(r"(a{}(), ", r"(d{}(), ");
        assert_eq!(
            local(&rewrite("old", "b{}()", COND), &lhs_and_requires),
            Some(ids(&["old"])),
            "left-hand side and requires: matched"
        );
        let attribute =
            rewrite("new", "b{}()", TOP).replace(r#"("new")]"#, r#"("new"), priority{}("40")]"#);
        assert_eq!(
            local(&rewrite("old", "b{}()", TOP), &attribute),
            Some(ids(&["old"])),
            "attribute: matched"
        );
        assert_eq!(
            local(
                &rewrite("old", "b{}()", TOP),
                &rewrite("new", "b{}()", COND)
            ),
            Some(ids(&["old"])),
            "requires: matched"
        );
        // Re-pin L2-1-tail (review L2-1-1, D3): the requires and the right-hand side both
        // changed is witnessed by matched, as for an equation.
        assert_eq!(
            local(
                &rewrite("old", "b{}()", TOP),
                &rewrite("new", "c{}()", COND)
            ),
            Some(ids(&["old"])),
            "both: matched"
        );
        let declaration = kore(&rewrite("new", "c{}()", TOP))
            .replace("module M", "module M\nsymbol z{}(): S{} []");
        let one = |_: &str| Some(BTreeSet::from([SentenceRef::new("M", 0)]));
        let none = |_: &str| None;
        let old = kore(&rewrite("old", "b{}()", TOP));
        let (removed, added) = (ids(&["old"]), ids(&["new"]));
        assert_eq!(
            site_local(&old, &declaration, &removed, &added, &one, &one),
            None
        );
        assert_eq!(
            site_local("malformed", &old, &removed, &added, &one, &one),
            None
        );
        // An inserted rewrite rule beside a removed one stays site-local, as before L2-1; the
        // removed one has no edited form to pair it with, so `matched` witnesses it.
        assert_eq!(
            site_local(
                &old,
                &kore(&rewrite("new", "c{}()", TOP)),
                &removed,
                &added,
                &one,
                &none
            ),
            Some(ids(&["old"]))
        );
        // A deleted rewrite rule: a run that left its guard undecided loses the group that
        // blocked the lower ones, so `matched` witnesses it too.
        assert_eq!(
            site_local(&old, &kore(""), &removed, &BTreeSet::new(), &one, &one),
            Some(ids(&["old"])),
            "deletion: matched"
        );
        // A removed rewrite rule with no baseline sentence is not paired, so `matched`.
        assert_eq!(
            site_local(
                &old,
                &kore(&rewrite("new", "c{}()", TOP)),
                &removed,
                &added,
                &none,
                &none
            ),
            Some(ids(&["old"])),
            "no baseline sentence: matched"
        );
    }

    #[test]
    fn an_equation_edit_is_site_local_only_in_its_requires_right_hand_side_or_ensures() {
        let top = r"\top{R}()";
        assert_eq!(
            local(
                &equation("old", "b{}()", top, ""),
                &equation("new", "c{}()", top, "")
            ),
            Some(BTreeSet::new()),
            "right-hand side: applied"
        );
        assert_eq!(
            local(
                &equation("old", "b{}()", top, ""),
                &equation("new", "b{}()", ECOND, "")
            ),
            Some(ids(&["old"])),
            "requires: matched"
        );
        assert_eq!(
            local(
                &equation("old", "b{}()", top, ""),
                &equation("new", "c{}()", ECOND, "")
            ),
            Some(ids(&["old"])),
            "both: matched"
        );
        let lhs = equation("new", "b{}()", top, "").replace(r"a{}()), \equals", r"d{}()), \equals");
        assert_eq!(
            local(&equation("old", "b{}()", top, ""), &lhs),
            None,
            "left-hand side"
        );
        assert_eq!(
            local(
                &equation("old", "b{}()", top, ""),
                &equation("new", "b{}()", top, r#", priority{}("40")"#)
            ),
            None,
            "attribute"
        );
        for attribute in [r#", concrete{}()"#, r#", symbolic{}()"#] {
            assert_eq!(
                local(
                    &equation("old", "b{}()", top, attribute),
                    &equation("new", "b{}()", ECOND, attribute)
                ),
                None,
                "requires of a set-aside equation"
            );
            assert_eq!(
                local(
                    &equation("old", "b{}()", top, attribute),
                    &equation("new", "c{}()", top, attribute)
                ),
                Some(BTreeSet::new()),
                "right-hand side of a set-aside equation"
            );
        }
        let one = |_: &str| Some(BTreeSet::from([SentenceRef::new("M", 0)]));
        let none = |_: &str| None;
        assert_eq!(
            site_local(
                &kore(&equation("old", "b{}()", top, "")),
                &kore(&equation("new", "c{}()", top, "")),
                &ids(&["old"]),
                &ids(&["new"]),
                &one,
                &none
            ),
            None,
            "an equation without a baseline author (inserted)"
        );
        for attribute in [r#", smt-lemma{}()"#, r#", owise{}()"#] {
            assert_eq!(
                local(
                    &equation("old", "b{}()", top, attribute),
                    &equation("new", "c{}()", top, attribute)
                ),
                None,
                "{attribute}"
            );
        }
    }
}
