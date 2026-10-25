//! kink's judgement of a candidate witness, as a k-rust-fuzz witness filter (fz26
//! FZ-COMPARABLE-B).
//!
//! kink refuses some fuzz witnesses for reasons that depend on the input: its end check (TV-01)
//! gives a `String` domain value a terminal value only when its bytes are ASCII, so a String-hole
//! kill whose generated text is not ASCII is no kill for kink (TRIAL3 ASCII-STRINGS). Refusing
//! such a witness only after the campaign ends loses the search, so `kink-flow fuzz` runs its
//! campaign with [`KinkJudgement`] ([`k_rust_fuzz::WitnessFilter`]): each candidate hit and shrink
//! candidate is judged by the rules kink's runner judges a run by, on the same sides, and a
//! refused hit is repaired from the client's candidates ([`repair_candidates`]).
//!
//! **What is judged.** The filter reads the witness case the campaign built: each side's initial
//! configuration, the configuration and halt of every leaf, the rule of every undefined step and
//! each side's work. It composes kink's own deciders, in the order kink's runner applies them to a
//! run (`kink-campaign` `Runtime::judge_with`, `judge_across`):
//! 1. the state exclusion (`DefinitionExclusions::state_exclusion`) of the baseline side's initial
//!    configuration, under each side's facts and definition: kink assembles every test's input
//!    from the baseline's grammar for both sides (cause `initial-state:<exclusion>`);
//! 2. the undefined-step exclusions of each side's run, under that side's facts: a `trivial` leaf
//!    of a `preserves-definedness` rule contradicts a claim (`preserves-definedness`), one of a
//!    rule whose result depends on the short-circuit reading is no evidence
//!    (`short-circuit-step`);
//! 3. TV-01 on every `stuck` or `trivial` leaf's term under its own side's definition, with that
//!    side's collection trust and data facts (`ObservationDecider::terminal_value`; the cause is
//!    the first failing node's test, [`cause_of`]);
//! 4. for a kill, every such end's value judged under the other side's definition too, as
//!    `judge_ends` judges each side's ends (cause `cross-<test>`);
//! 5. for a kill by a removed end under the flow's `[budget] work_factor`, the mutant's run must
//!    complete within kink's budget for it, `work_factor × W + WORK_FLOOR` with `W` the baseline
//!    run's work: a run bounded by at least its unbounded work completes, and a removed end needs
//!    the mutant's complete set of ends (`work-factor`). An added end is left to kink's own run,
//!    which may still kill it through one-sided evidence of a work-bound mutant.
//!
//! A reach job judges the baseline alone (1 to 3, own definition); a pattern job judges only the
//! state exclusion (1): a query's stepped run stops at its first match, so the leaves the case
//! holds are not the run kink judges, and kink's own query decides about them.
//!
//! **Laxer and stricter than kink.** The filter only removes candidates, and kink's own run of
//! the fragment stays the verdict (KF-T4). A difference costs a witness or leaves kink's refusal
//! to its confirmation, never a claim kink does not make:
//! - stricter: without the adapter's feasibility, a leaf the solver refutes (kink drops it,
//!   `Unsat`) is judged ([`kink_native::bridge::leaf_term`]); the work-factor check reads the
//!   fuzz's work, which is kink's unit of the same request shape;
//! - laxer: a leaf whose state is not one decided term, a halt outside the bridge's contract, a
//!   configuration that does not parse, and a decider kink-native could not build are left to
//!   kink (a backend that cannot reach its definition is a fact of the environment, so refusing on
//!   it could make the filter's verdict depend on more than the case).
//!
//! **Identity.** [`KinkJudgement::id`] names [`FILTER_VERSION`] (this composition: the deciders,
//! the leaves, the cause tokens, the repair), the `KINK_IDENTITY` components it composes
//! (`terminal_value`, `data_facts`, `definition_exclusion`, `k_rust_revision`) and the flow's work
//! budget. It never names `kink_build`, which changes with every rebuild of an identical filter.

use k_rust::kore::{
    ast::{Definition as KoreDefinition, Pattern, Sort as KoreSort},
    parser::parse_pattern,
};
use k_rust_fuzz::{
    FilterRefusal, Value, WitnessFilter,
    report::{KillKind, WitnessCase, WitnessSide},
};
use kink_campaign::{KINK_IDENTITY, WorkBudget};
use kink_native::{
    bridge::{LeafTerm, leaf_term},
    data::{DataFacts, data_ends},
    exclusion::{DefinitionExclusions, ValidatedLoad},
    execution::HaltClass,
    feasibility::TestInitialState,
    step_events::{LocalTest, NonValue, ObservationDecider},
};
use kink_pattern::SymbolSorts;
use std::collections::BTreeSet;

use crate::results::non_value_text;

/// The version of the filter's composition: which deciders it applies to which leaves, in which
/// order, its cause tokens and its repair. Bumped when any of them changes.
pub const FILTER_VERSION: &str = "kink-flow/witness-filter/v1";

/// The repair candidates a refused hit gets at most ([`repair_candidates`]).
const REPAIR_CANDIDATES: usize = 2;

/// The job a filter judges for.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FilterJob {
    /// A kill: both sides.
    Kill,
    /// A reach: the baseline alone.
    Reach,
    /// A pattern: the baseline's state exclusion alone.
    Pattern,
}

/// One side as the filter judges it: kink's load of it and the exclusions read from it, its
/// symbol sorts, and its data facts under the campaign's assumed names.
pub struct FilterSide {
    load: ValidatedLoad,
    sorts: SymbolSorts,
    data: DataFacts,
}

impl FilterSide {
    /// The side of `load` with the data facts `data`.
    #[must_use]
    pub fn new(load: ValidatedLoad, data: DataFacts) -> Self {
        let sorts = SymbolSorts::from_definition(&load.kore);
        Self { load, sorts, data }
    }

    /// The side's data facts recomputed under `assume_joined` on its own load (the campaign's
    /// names, when the command line adds names the flow lacks).
    ///
    /// # Errors
    ///
    /// The backend's refusal to select the side's definition.
    pub fn recompute_data(&mut self, assume_joined: &[String]) -> Result<(), String> {
        let selected = self
            .load
            .backend
            .select_definition(None)
            .map_err(|error| error.to_string())?;
        self.data = DataFacts::of(&selected, assume_joined);
        Ok(())
    }

    /// The exclusions read from the side's load.
    #[must_use]
    pub const fn exclusions(&self) -> &DefinitionExclusions {
        &self.load.exclusions
    }

    /// The parsed KORE of the side.
    #[must_use]
    pub const fn kore(&self) -> &KoreDefinition {
        &self.load.kore
    }

    /// The state exclusion of `initial` on this side, by name, if any.
    fn state_exclusion(&mut self, initial: &Pattern) -> Option<&'static str> {
        let exclusions = &self.load.exclusions;
        let selected = self.load.backend.select_definition(None).ok()?;
        exclusions
            .state_exclusion(&selected, initial)
            .map(kink_native::exclusion::Exclusion::name)
    }

    /// The terminal value of each of `terms` under this side's definition, or why it has none
    /// (with whether the failing node is a String-like domain value that is not ASCII, which a
    /// repair of the holes can avoid); `None` when no decider can be built.
    fn values(&mut self, initial: &Pattern, terms: &[Pattern]) -> Option<Vec<Judged>> {
        let trusted = self.load.exclusions.collections_trusted();
        let own = data_ends(&self.data);
        self.load
            .backend
            .with_solver(None, |definition, solver| {
                let decider =
                    ObservationDecider::new(definition, solver, TestInitialState::of_test(initial))
                        .trusting_collections(trusted)
                        .judging_data(own, own);
                Ok::<_, k_rust::backend::BackendError>(
                    terms
                        .iter()
                        .map(|term| match decider.terminal_value(term) {
                            Some(value) => Judged::Value(value),
                            None => {
                                decider
                                    .first_non_value(term)
                                    .map_or(Judged::Changed, |failure| {
                                        let hook = |name: &str| {
                                            definition.sorts().get(name).map(|info| {
                                                info.hook.as_ref().map(ToString::to_string)
                                            })
                                        };
                                        let repairable = repairable(&failure, &hook);
                                        Judged::NoValue(Box::new(failure), repairable)
                                    })
                            }
                        })
                        .collect(),
                )
            })
            .ok()
    }
}

/// What one side's decider says of one term ([`FilterSide::values`]).
enum Judged {
    /// Its terminal value.
    Value(Pattern),
    /// It has none: the first failing node, and whether a repair of the holes can avoid it.
    NoValue(Box<NonValue>, bool),
    /// It has a value, but not itself (the cross judgement asks for the term itself): no node
    /// fails, the canonical value differs.
    Changed,
}

/// Whether `failure` is a domain value that fails only because its bytes are not ASCII: of a
/// sort whose hook (`hook`, which reads the definition's sort table) is `STRING.String` or none,
/// whose ASCII values have a trusted injective codec (kink-native's TV-01). Generated `String`
/// hole values reach ends this way, and replacing their non-ASCII characters can give a value; a
/// `Bytes`, `Float` or `MInt` domain value is refused for every value, and no repair helps.
fn repairable(failure: &NonValue, hook: &dyn Fn(&str) -> Option<Option<String>>) -> bool {
    let Pattern::DomainValue {
        sort: KoreSort::Application { name, arguments },
        value,
    } = &failure.node
    else {
        return false;
    };
    arguments.is_empty()
        && !value.as_bytes().is_ascii()
        && hook(name).is_some_and(|hook| matches!(hook.as_deref(), Some("STRING.String") | None))
}

/// The cause token of a term that has no terminal value, by the test its first failing node
/// fails.
const fn cause_of(test: LocalTest) -> &'static str {
    match test {
        LocalTest::TermKind => "term-kind",
        LocalTest::IdentitySafeDomainValue => "domain-value",
        LocalTest::CanonicalInjection => "injection",
        LocalTest::DeclaredSymbol => "undeclared-symbol",
        LocalTest::FreeConstructor => "not-constructor",
        LocalTest::OverloadData => "overload-not-data",
        LocalTest::Arity => "arity",
        LocalTest::TrustedCollections => "collection-untrusted",
        LocalTest::CollectionSort
        | LocalTest::Ground
        | LocalTest::NaturalCollection
        | LocalTest::DistinctEntries => "collection-shape",
    }
}

/// A refusal, with whether [`repair_candidates`] can avoid it.
struct Refused {
    refusal: FilterRefusal,
    repairable: bool,
}

impl Refused {
    fn new(cause: impl Into<String>, detail: String, remedy: &str) -> Self {
        Self {
            refusal: FilterRefusal {
                cause: cause.into(),
                detail,
                remedy: Some(remedy.to_owned()),
            },
            repairable: false,
        }
    }
}

/// The remedy of a refusal by kink's end check.
const VALUE_REMEDY: &str = "kink compares only ends whose every node has a definition-independent \
                            value (TV-01): constructors, normal-form injections, canonical Int and \
                            Bool values, ASCII strings and trusted collections; choose a template \
                            or hole range whose runs end on such values (an ASCII String hole \
                            needs `choices`, or the repair the filter tries)";

/// The remedy of a refusal by an exclusion.
const EXCLUSION_REMEDY: &str = "kink excludes such a run from every comparison (kink-flow run \
                                gives the program the exclusion as its cause); choose a template \
                                whose runs avoid it";

/// The remedy of a refusal by the work budget.
const WORK_REMEDY: &str = "kink's run of the mutant stops at its work budget before it shows that \
                           the baseline's end is missing; raise [budget] work_factor in FLOW.toml, \
                           or choose a template or hole range on which the mutant ends sooner";

/// kink's judgement of a candidate witness (module documentation).
pub struct KinkJudgement {
    job: FilterJob,
    baseline: FilterSide,
    mutant: Option<FilterSide>,
    work: WorkBudget,
    id: String,
}

impl KinkJudgement {
    /// The filter of `job` on `baseline` (and `mutant` for a kill), with the flow's work budget.
    #[must_use]
    pub fn new(
        job: FilterJob,
        baseline: FilterSide,
        mutant: Option<FilterSide>,
        work: WorkBudget,
    ) -> Self {
        let component = |key: &str| {
            KINK_IDENTITY
                .iter()
                .find(|component| component.key == key)
                .map_or("", |component| component.value)
        };
        let budget = match work {
            WorkBudget::Unbounded => "unbounded".to_owned(),
            WorkBudget::Calibrated { factor, floor } => format!("{factor}*W+{floor}"),
        };
        let id = format!(
            "{FILTER_VERSION};terminal_value={};data_facts={};definition_exclusion={};\
             k_rust_revision={};work={budget}",
            component("terminal_value"),
            component("data_facts"),
            component("definition_exclusion"),
            component("k_rust_revision"),
        );
        Self {
            job,
            baseline,
            mutant,
            work,
            id,
        }
    }

    /// The baseline side.
    #[must_use]
    pub const fn baseline(&self) -> &FilterSide {
        &self.baseline
    }

    /// The state exclusion of `initial` on any side the job reads, as `(side, exclusion)`, for
    /// the job's setup check of the anchors.
    pub fn initial_exclusion(&mut self, initial: &Pattern) -> Option<(&'static str, &'static str)> {
        if let Some(exclusion) = self.baseline.state_exclusion(initial) {
            return Some(("baseline", exclusion));
        }
        let mutant = self
            .mutant
            .as_mut()
            .filter(|_| self.job == FilterJob::Kill)?;
        mutant
            .state_exclusion(initial)
            .map(|exclusion| ("mutant", exclusion))
    }

    /// The verdict on `case` (module documentation): `None` when kink's rules accept it.
    fn verdict(&mut self, case: &WitnessCase) -> Option<Refused> {
        let initial = parse_pattern(&case.sides.first()?.initial_configuration).ok()?;
        // 1. The state exclusion of the baseline's initial configuration, under each side's facts.
        if let Some((role, exclusion)) = self.initial_exclusion(&initial) {
            return Some(Refused::new(
                format!("initial-state:{exclusion}"),
                format!(
                    "the initial configuration has kink's exclusion {exclusion} on the {role}'s \
                     definition"
                ),
                EXCLUSION_REMEDY,
            ));
        }
        if self.job == FilterJob::Pattern {
            return None;
        }
        // 2 and 3, each side under its own facts and definition.
        let baseline = match judge_side(
            "baseline",
            case.sides.first()?,
            &mut self.baseline,
            &initial,
        ) {
            Ok(values) => values,
            Err(refused) => return Some(refused),
        };
        let pair = match (self.job, self.mutant.as_mut(), case.sides.get(1)) {
            (FilterJob::Kill, Some(mutant), Some(side)) => Some((mutant, side)),
            _ => None,
        };
        let (mutant, mutant_case) = pair?;
        let mutant_values = match judge_side("mutant", mutant_case, mutant, &initial) {
            Ok(values) => values,
            Err(refused) => return Some(refused),
        };
        // 4. Each side's values under the other side's definition.
        if let Some(values) = &baseline
            && let Some(refused) = cross("baseline", values, "mutant", mutant, &initial)
        {
            return Some(refused);
        }
        if let Some(values) = &mutant_values
            && let Some(refused) = cross("mutant", values, "baseline", &mut self.baseline, &initial)
        {
            return Some(refused);
        }
        // 5. A removed end needs the mutant's run complete within kink's work budget.
        if case.kill == Some(KillKind::RemovedEnd) {
            return self.work_refusal(case);
        }
        None
    }

    /// The `work-factor` refusal of a removed-end kill whose mutant run visited more states than
    /// kink's budget for it ([`WorkBudget::limit`] of the baseline's work).
    fn work_refusal(&self, case: &WitnessCase) -> Option<Refused> {
        let (baseline, mutant) = (case.sides.first()?.work?, case.sides.get(1)?.work?);
        let limit = self.work.limit(baseline)?;
        (mutant > limit).then(|| {
            let WorkBudget::Calibrated { factor, floor } = self.work else {
                unreachable!("an unbounded budget has no limit")
            };
            Refused::new(
                "work-factor",
                format!(
                    "the mutant's run visited {mutant} states, more than kink's budget for it \
                     (work_factor {factor} x the baseline's {baseline} + {floor} = {limit}), so \
                     kink's run of the mutant stops work-bound and cannot show the baseline's end \
                     missing"
                ),
                WORK_REMEDY,
            )
        })
    }
}

/// The refusal of `side`'s run, the `role` side's, by its undefined steps and by TV-01 under its
/// own `facts`, or the values of its ends (`None` when no decider could be built, which leaves
/// the side to kink).
fn judge_side(
    role: &str,
    side: &WitnessSide,
    facts: &mut FilterSide,
    initial: &Pattern,
) -> Result<Option<Vec<Pattern>>, Refused> {
    if let Some(refused) = undefined_step(role, side, facts.exclusions()) {
        return Err(refused);
    }
    let ends = ends(side, &facts.sorts);
    let terms: Vec<Pattern> = ends.iter().map(|(_, term)| term.clone()).collect();
    let Some(judged) = facts.values(initial, &terms) else {
        return Ok(None);
    };
    let mut values = Vec::new();
    for ((leaf, _), judged) in ends.iter().zip(judged) {
        match judged {
            Judged::Value(value) => values.push(value),
            Judged::NoValue(failure, repairable) => {
                return Err(Refused {
                    repairable,
                    ..Refused::new(
                        cause_of(failure.test),
                        format!(
                            "the {role}'s leaf {leaf} has no value kink can compare: {}",
                            non_value_text(&failure)
                        ),
                        VALUE_REMEDY,
                    )
                });
            }
            Judged::Changed => {}
        }
    }
    Ok(Some(values))
}

/// The `stuck` and `trivial` leaves of `side` whose state is one decided term, with their index.
fn ends(side: &WitnessSide, sorts: &SymbolSorts) -> Vec<(usize, Pattern)> {
    side.final_configurations
        .iter()
        .zip(&side.halts)
        .enumerate()
        .filter_map(|(index, (state, halt))| {
            let halt = HaltClass::from_output(*halt);
            if !matches!(halt, HaltClass::Stuck | HaltClass::Trivial) {
                return None;
            }
            let state = parse_pattern(state).ok()?;
            match leaf_term(&state, halt, sorts) {
                Ok(LeafTerm::Term(term)) => Some((index, term)),
                _ => None,
            }
        })
        .collect()
}

/// The refusal of `side`'s run by its undefined steps, under its own `exclusions`.
fn undefined_step(
    role: &str,
    side: &WitnessSide,
    exclusions: &DefinitionExclusions,
) -> Option<Refused> {
    let steps = side
        .halts
        .iter()
        .zip(&side.undefined_rules)
        .enumerate()
        .filter(|(_, (halt, _))| HaltClass::from_output(**halt) == HaltClass::Trivial)
        .filter_map(|(index, (_, rule))| Some((index, rule.as_ref()?)));
    for (index, rule) in steps {
        if exclusions.preserves_definedness.contains(rule) {
            return Some(Refused::new(
                "preserves-definedness",
                format!(
                    "the {role}'s leaf {index} is an undefined step of rule {rule}, written \
                     preserves-definedness: the run contradicts the claim, so kink takes no \
                     evidence from it"
                ),
                EXCLUSION_REMEDY,
            ));
        }
        if exclusions.short_circuit_rules.contains(rule) {
            return Some(Refused::new(
                "short-circuit-step",
                format!(
                    "the {role}'s leaf {index} is an undefined step of rule {rule}, whose result \
                     depends on whether a short-circuit operator skips an undefined operand"
                ),
                EXCLUSION_REMEDY,
            ));
        }
    }
    None
}

/// The refusal of `values`, the `role` side's end values, under `other`'s definition: each must
/// be its own terminal value there.
fn cross(
    role: &str,
    values: &[Pattern],
    other_role: &str,
    other: &mut FilterSide,
    initial: &Pattern,
) -> Option<Refused> {
    let judged = other.values(initial, values)?;
    for (value, judged) in values.iter().zip(judged) {
        let failure = match judged {
            Judged::Value(own) if own == *value => continue,
            Judged::Value(_) | Judged::Changed => None,
            Judged::NoValue(failure, repairable) => Some((failure, repairable)),
        };
        let (cause, detail, repairable) = match failure {
            Some((failure, repairable)) => (
                format!("cross-{}", cause_of(failure.test)),
                non_value_text(&failure),
                repairable,
            ),
            None => (
                "cross-value-differs".to_owned(),
                "its value there is another term".to_owned(),
                false,
            ),
        };
        return Some(Refused {
            repairable,
            ..Refused::new(
                cause,
                format!(
                    "an end of the {role} is not a value under the {other_role}'s definition: {detail}"
                ),
                VALUE_REMEDY,
            )
        });
    }
    None
}

impl WitnessFilter for KinkJudgement {
    fn id(&self) -> String {
        self.id.clone()
    }

    fn judge(&mut self, case: &WitnessCase) -> Result<(), FilterRefusal> {
        self.verdict(case)
            .map_or(Ok(()), |refused| Err(refused.refusal))
    }

    /// Candidates only for a refusal a repair of the holes can avoid: a String-like domain value
    /// that is not ASCII ([`repairable`]); none for a value refused whatever it holds.
    fn repair(
        &mut self,
        case: &WitnessCase,
        values: &[Value],
        _refusal: &FilterRefusal,
    ) -> Vec<Vec<Value>> {
        match self.verdict(case) {
            Some(refused) if refused.repairable => repair_candidates(values),
            _ => Vec::new(),
        }
    }
}

/// Repair candidates for hole values whose String text kink refuses: each candidate replaces only
/// the non-ASCII characters of the `String` values in `values` (nested in `List`, `Set`, `Map` and
/// constructor values too) by ASCII letters or digits, so every length, every ASCII character and
/// the equality of equal characters is kept, and distinct strings stay distinct (a candidate that
/// would merge two is dropped, as is one under which a `Set` or a `Map`'s keys would collapse).
///
/// In order: each distinct non-ASCII character, in order of first appearance, becomes the next
/// letter or digit that no string of the values holds (so the replaced characters stay distinct
/// from each other and from every kept character while there are enough), then each non-ASCII
/// character becomes the letter its code point selects modulo 26. At most [`REPAIR_CANDIDATES`];
/// none when no String value holds a non-ASCII character.
#[must_use]
pub fn repair_candidates(values: &[Value]) -> Vec<Vec<Value>> {
    let mut texts = Vec::new();
    for value in values {
        collect_strings(value, &mut texts);
    }
    if texts.iter().all(|text| text.is_ascii()) {
        return Vec::new();
    }
    let kept: BTreeSet<char> = texts
        .iter()
        .flat_map(|text| text.chars())
        .filter(char::is_ascii)
        .collect();
    let mut free: Vec<char> = ('a'..='z')
        .chain('A'..='Z')
        .chain('0'..='9')
        .filter(|c| !kept.contains(c))
        .collect();
    if free.is_empty() {
        free = ('a'..='z').collect();
    }
    let mut order: Vec<char> = Vec::new();
    for c in texts.iter().flat_map(|text| text.chars()) {
        if !c.is_ascii() && !order.contains(&c) {
            order.push(c);
        }
    }
    let by_appearance = |c: char| {
        let index = order.iter().position(|seen| *seen == c).unwrap_or(0);
        free[index % free.len()]
    };
    let by_code_point = |c: char| {
        let offset = u8::try_from(u32::from(c) % 26).unwrap_or(0);
        char::from(b'a' + offset)
    };
    let mappings: [&dyn Fn(char) -> char; 2] = [&by_appearance, &by_code_point];
    let distinct: BTreeSet<&String> = texts.iter().collect();
    let mut candidates: Vec<Vec<Value>> = Vec::new();
    for mapping in mappings {
        if candidates.len() == REPAIR_CANDIDATES {
            break;
        }
        let replace = |text: &str| -> String {
            text.chars()
                .map(|c| if c.is_ascii() { c } else { mapping(c) })
                .collect()
        };
        let repaired: BTreeSet<String> = distinct.iter().map(|text| replace(text)).collect();
        if repaired.len() != distinct.len() {
            continue;
        }
        let Some(candidate) = values
            .iter()
            .map(|value| replace_strings(value, &replace))
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };
        if candidate != values && !candidates.contains(&candidate) {
            candidates.push(candidate);
        }
    }
    candidates
}

/// Every `String` text in `value`, in order.
fn collect_strings(value: &Value, out: &mut Vec<String>) {
    match value {
        Value::String(text) => out.push(text.clone()),
        Value::List(items) | Value::Set(items) => {
            for item in items {
                collect_strings(item, out);
            }
        }
        Value::Map(entries) => {
            for (key, value) in entries {
                collect_strings(key, out);
                collect_strings(value, out);
            }
        }
        Value::Apply { arguments, .. } => {
            for argument in arguments {
                collect_strings(argument, out);
            }
        }
        Value::Int(_)
        | Value::Bool(_)
        | Value::Bytes(_)
        | Value::MInt { .. }
        | Value::Token { .. } => {}
    }
}

/// `value` with every `String` text replaced by `replace`; a `Set` stays sorted and a `Map`
/// sorted by key, and `None` when either would lose an element or a key.
fn replace_strings(value: &Value, replace: &dyn Fn(&str) -> String) -> Option<Value> {
    Some(match value {
        Value::String(text) => Value::String(replace(text)),
        Value::List(items) => Value::List(
            items
                .iter()
                .map(|item| replace_strings(item, replace))
                .collect::<Option<_>>()?,
        ),
        Value::Set(items) => {
            let replaced: BTreeSet<Value> = items
                .iter()
                .map(|item| replace_strings(item, replace))
                .collect::<Option<_>>()?;
            if replaced.len() != items.len() {
                return None;
            }
            Value::Set(replaced.into_iter().collect())
        }
        Value::Map(entries) => {
            let replaced: std::collections::BTreeMap<Value, Value> = entries
                .iter()
                .map(|(key, value)| {
                    Some((
                        replace_strings(key, replace)?,
                        replace_strings(value, replace)?,
                    ))
                })
                .collect::<Option<_>>()?;
            if replaced.len() != entries.len() {
                return None;
            }
            Value::Map(replaced.into_iter().collect())
        }
        Value::Apply { symbol, arguments } => Value::Apply {
            symbol: symbol.clone(),
            arguments: arguments
                .iter()
                .map(|argument| replace_strings(argument, replace))
                .collect::<Option<_>>()?,
        },
        other => other.clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use k_rust::{
        backend::{Backend, BackendOptions, HaltReasonOutput},
        kore::parser::parse_definition,
    };
    use k_rust_fuzz::{
        OutcomeClass,
        report::{DefinitionRole, Reaching},
    };

    /// Two constructors of one sort, `a` and `b`, and a hooked String sort.
    const DEFINITION: &str = r#"[]
        module MAIN
            sort SortS{} []
            hooked-sort SortString{} [hook{}("STRING.String"), hasDomainValues{}()]
            symbol Lbla{}() : SortS{} [constructor{}(), functional{}()]
            symbol Lblb{}() : SortS{} [constructor{}(), functional{}()]
        endmodule []"#;

    /// [`DEFINITION`] without `b`.
    const WITHOUT_B: &str = r#"[]
        module MAIN
            sort SortS{} []
            hooked-sort SortString{} [hook{}("STRING.String"), hasDomainValues{}()]
            symbol Lbla{}() : SortS{} [constructor{}(), functional{}()]
        endmodule []"#;

    /// A side of [`DEFINITION`] whose facts name `preserves` as `preserves-definedness` rules.
    fn side(preserves: &[&str]) -> FilterSide {
        side_of(DEFINITION, preserves)
    }

    /// A side of `definition` whose facts name `preserves` as `preserves-definedness` rules.
    fn side_of(definition: &str, preserves: &[&str]) -> FilterSide {
        let kore = parse_definition(definition).expect("the test definition parses");
        let mut backend = Backend::from_definition(kore.clone(), "MAIN", BackendOptions::default())
            .expect("the test definition loads");
        let selected = backend.select_definition(None).expect("a definition");
        let data = DataFacts::of(&selected, &[]);
        let exclusions = DefinitionExclusions {
            preserves_definedness: preserves.iter().map(|id| (*id).to_owned()).collect(),
            ..DefinitionExclusions::default()
        };
        FilterSide::new(
            ValidatedLoad {
                exclusions,
                backend,
                kore,
            },
            data,
        )
    }

    fn witness_side(
        role: DefinitionRole,
        leaves: &[(&str, HaltReasonOutput, Option<&str>)],
        work: u64,
    ) -> WitnessSide {
        let rules: Vec<Option<String>> = leaves
            .iter()
            .map(|(_, _, rule)| rule.map(str::to_owned))
            .collect();
        WitnessSide {
            role,
            initial_configuration: "Lbla{}()".into(),
            final_configurations: leaves
                .iter()
                .map(|(state, ..)| (*state).to_owned())
                .collect(),
            halts: leaves.iter().map(|(_, halt, _)| *halt).collect(),
            undefined_rules: if rules.iter().any(Option::is_some) {
                rules
            } else {
                Vec::new()
            },
            work: Some(work),
        }
    }

    fn kill(baseline: WitnessSide, mutant: WitnessSide, kind: KillKind) -> WitnessCase {
        WitnessCase {
            holes: Vec::new(),
            program: None,
            config_vars: std::collections::BTreeMap::new(),
            class: OutcomeClass::Hit,
            sides: vec![baseline, mutant],
            reaching: Reaching {
                role: DefinitionRole::Mutant,
                leaf: Some(0),
                step: None,
                configuration: None,
            },
            kill: Some(kind),
            steps: Some(1),
            comparable: None,
        }
    }

    const STUCK: HaltReasonOutput = HaltReasonOutput::Stuck;
    const TRIVIAL: HaltReasonOutput = HaltReasonOutput::Trivial;

    /// S1: each side's undefined steps are judged under that side's own facts, as kink's runner
    /// judges each run under its own side's exclusions. A rule whose `preserves-definedness`
    /// claim the claim-free mutant withdrew is in the baseline's facts alone: the mutant's
    /// undefined step of it is evidence for kink, and the baseline's is not.
    #[test]
    fn each_sides_undefined_steps_are_judged_under_its_own_facts() {
        let case = |baseline_rule, mutant_rule| {
            kill(
                witness_side(
                    DefinitionRole::Baseline,
                    &[("Lblb{}()", TRIVIAL, baseline_rule)],
                    1,
                ),
                witness_side(
                    DefinitionRole::Mutant,
                    &[("Lbla{}()", TRIVIAL, mutant_rule)],
                    1,
                ),
                KillKind::AddedEnd,
            )
        };
        let mut judgement = KinkJudgement::new(
            FilterJob::Kill,
            side(&["claimed"]),
            Some(side(&[])),
            WorkBudget::Unbounded,
        );
        assert_eq!(judgement.judge(&case(None, Some("claimed"))), Ok(()));
        let refused = judgement
            .judge(&case(Some("claimed"), None))
            .expect_err("the baseline's claim is contradicted");
        assert_eq!(refused.cause, "preserves-definedness");
        assert!(refused.detail.contains("baseline"), "{}", refused.detail);
        // And the other way round: a rule in the mutant's facts alone.
        let mut judgement = KinkJudgement::new(
            FilterJob::Kill,
            side(&[]),
            Some(side(&["claimed"])),
            WorkBudget::Unbounded,
        );
        assert_eq!(judgement.judge(&case(Some("claimed"), None)), Ok(()));
        assert_eq!(
            judgement
                .judge(&case(None, Some("claimed")))
                .map_err(|refusal| refusal.cause),
            Err("preserves-definedness".to_owned())
        );
    }

    /// S5: under `[budget] work_factor`, a removed-end kill whose mutant run visited more states
    /// than `factor × W + floor` (kink's budget, `W` the baseline's work) is refused, since kink's
    /// run of the mutant stops at its budget; one within the budget, an added end, and an
    /// unbounded flow are accepted.
    #[test]
    fn a_removed_end_beyond_kinks_work_budget_is_refused() {
        let case = |kind, baseline_work, mutant_work| {
            kill(
                witness_side(
                    DefinitionRole::Baseline,
                    &[("Lbla{}()", STUCK, None)],
                    baseline_work,
                ),
                witness_side(
                    DefinitionRole::Mutant,
                    &[("Lblb{}()", STUCK, None)],
                    mutant_work,
                ),
                kind,
            )
        };
        let budget = WorkBudget::Calibrated {
            factor: 2,
            floor: 10_000,
        };
        let mut judgement = KinkJudgement::new(FilterJob::Kill, side(&[]), Some(side(&[])), budget);
        let refused = judgement
            .judge(&case(KillKind::RemovedEnd, 100, 10_201))
            .expect_err("beyond 2 x 100 + 10000");
        assert_eq!(refused.cause, "work-factor");
        assert!(refused.detail.contains("10200"), "{}", refused.detail);
        assert_eq!(
            judgement.judge(&case(KillKind::RemovedEnd, 100, 10_200)),
            Ok(())
        );
        assert_eq!(
            judgement.judge(&case(KillKind::AddedEnd, 100, 99_999)),
            Ok(())
        );
        let mut unbounded = KinkJudgement::new(
            FilterJob::Kill,
            side(&[]),
            Some(side(&[])),
            WorkBudget::Unbounded,
        );
        assert_eq!(
            unbounded.judge(&case(KillKind::RemovedEnd, 1, 99_999)),
            Ok(())
        );
        assert!(
            judgement.id().ends_with(";work=2*W+10000"),
            "{}",
            judgement.id()
        );
        assert!(
            unbounded.id().ends_with(";work=unbounded"),
            "{}",
            unbounded.id()
        );
        assert!(!judgement.id().contains("kink_build"));
    }

    /// The identity names the filter's composition and the kink components it composes.
    #[test]
    fn the_identity_names_the_composition_and_kinks_components() {
        let judgement =
            KinkJudgement::new(FilterJob::Reach, side(&[]), None, WorkBudget::Unbounded);
        let id = judgement.id();
        assert!(id.starts_with(&format!("{FILTER_VERSION};")), "{id}");
        for key in [
            "terminal_value",
            "data_facts",
            "definition_exclusion",
            "k_rust_revision",
        ] {
            let value = KINK_IDENTITY
                .iter()
                .find(|component| component.key == key)
                .expect("a component")
                .value;
            assert!(id.contains(&format!("{key}={value};")), "{id}");
        }
    }

    /// TV-01 runs on each side's ends under its own definition (a String end that is not ASCII
    /// is refused, repairably), and each kill end's value under the other side's too (`b` is no
    /// symbol of the mutant).
    #[test]
    fn ends_are_judged_under_their_own_and_the_other_sides_definition() {
        let mut judgement = KinkJudgement::new(
            FilterJob::Kill,
            side(&[]),
            Some(side_of(WITHOUT_B, &[])),
            WorkBudget::Unbounded,
        );
        let case = |baseline: &str, mutant: &str| {
            kill(
                witness_side(DefinitionRole::Baseline, &[(baseline, STUCK, None)], 1),
                witness_side(DefinitionRole::Mutant, &[(mutant, STUCK, None)], 1),
                KillKind::AddedEnd,
            )
        };
        let ascii = r#"\dv{SortString{}}("x")"#;
        let accented = r#"\dv{SortString{}}("\u00e9")"#;
        assert_eq!(judgement.judge(&case(ascii, "Lbla{}()")), Ok(()));
        let accented_case = case(accented, "Lbla{}()");
        let refused = judgement
            .judge(&accented_case)
            .expect_err("a non-ASCII String end");
        assert_eq!(refused.cause, "domain-value");
        assert!(
            refused.detail.contains("baseline's leaf 0"),
            "{}",
            refused.detail
        );
        assert!(
            judgement
                .verdict(&accented_case)
                .is_some_and(|r| r.repairable)
        );
        let refused = judgement
            .judge(&case("Lblb{}()", "Lbla{}()"))
            .expect_err("b is no symbol of the mutant");
        assert_eq!(refused.cause, "cross-undeclared-symbol");
        // A reach judges the baseline alone, under its own definition.
        let mut reach =
            KinkJudgement::new(FilterJob::Reach, side(&[]), None, WorkBudget::Unbounded);
        let mut alone = case("Lblb{}()", "Lbla{}()");
        alone.sides.truncate(1);
        assert_eq!(reach.judge(&alone), Ok(()));
    }

    fn string(text: &str) -> Value {
        Value::String(text.into())
    }

    /// The repair replaces only the non-ASCII characters of String values, nested ones too,
    /// keeps every length and ASCII character, keeps distinct strings distinct, re-sorts a set,
    /// and proposes nothing for values it cannot change.
    #[test]
    fn a_repair_replaces_only_non_ascii_characters() {
        let values = vec![
            string("ab\u{e9}\u{e9}"),
            Value::List(vec![string("\u{e9}x"), string("\u{e8}x")]),
            Value::Int(7.into()),
        ];
        let candidates = repair_candidates(&values);
        assert!(!candidates.is_empty() && candidates.len() <= REPAIR_CANDIDATES);
        for candidate in &candidates {
            let mut texts = Vec::new();
            for value in candidate {
                collect_strings(value, &mut texts);
            }
            assert!(texts.iter().all(|text| text.is_ascii()), "{texts:?}");
            assert_eq!(
                texts
                    .iter()
                    .map(|text| text.chars().count())
                    .collect::<Vec<_>>(),
                [4, 2, 2]
            );
            assert!(texts[0].starts_with("ab"), "{texts:?}");
            assert_ne!(texts[1], texts[2], "distinct strings stay distinct");
            assert_eq!(candidate[2], Value::Int(7.into()));
        }
        // The first candidate maps each distinct character to a letter no string holds.
        assert_eq!(
            candidates[0],
            vec![
                string("abcc"),
                Value::List(vec![string("cx"), string("dx")]),
                Value::Int(7.into()),
            ]
        );
        // A set is re-sorted; one whose elements would collapse gives no candidate of that
        // mapping.
        let set = vec![Value::Set(vec![string("z"), string("\u{e9}")])];
        for candidate in repair_candidates(&set) {
            let Value::Set(items) = &candidate[0] else {
                panic!("a set");
            };
            assert!(items.windows(2).all(|pair| pair[0] < pair[1]), "{items:?}");
        }
        assert!(repair_candidates(&[string("ascii"), Value::Bytes(vec![0xff])]).is_empty());
        assert!(repair_candidates(&[Value::Int(1.into())]).is_empty());
    }
}
