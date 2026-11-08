//! A stop condition of a campaign's stop ([`crate::Stop::with_when`]): a question asked at each
//! arrival at a stop of a result run, so that a path ends at its `N`th arrival where the answer
//! is yes.
//!
//! # Meaning
//!
//! An arrival is a step by a stop rule that is its state's one successor, whose successor is
//! defined (kink-native `ExecutionAdapter::execute_result_counted`). Its stop state is the state
//! the path would end at there: the state before a stop-before rule's step, the successor of a
//! stop-after rule's. A stop event is an arrival whose stop state the condition holds of, and the
//! stop's count counts events. Every other arrival is taken as any other step. Without a
//! condition every arrival is an event, which is the stop as it was before conditions existed.
//!
//! The condition is a function of named cells of the stop state, evaluated in one fixed observer
//! definition, which the front end that states the condition chooses ([`StopOracle`]): never the
//! definition being run. The baseline's runs and every mutant's are asked the same question, so a
//! mutation changes the states the condition is asked at, never the condition, and a kill is
//! relative to (definition, stop rules, count, condition).
//!
//! # Reading a mutant's cells
//!
//! The front end reads a run's cells with the baseline's declarations of their values: a term
//! whose symbols and literal sorts the baseline declares is read as that term, an injection as
//! its argument, and a term with a part the baseline does not declare is refused. A refused
//! reading leaves the arrival without an answer, which is sound (the run is no evidence). What
//! is unsound is a reading as another term than the mutant's state holds, which needs a part both
//! definitions declare, declared otherwise. [`ReadSignature`] is the part of a definition's
//! signature a run's read cells can hold: the sorts reached from each read cell's content sort
//! through the argument sorts of their constructors and hooked symbols and through their
//! subsorts, and those symbols. A mutant is not admitted (`stop-condition-incompatible`), never
//! run under another reading of its states, when a sort or symbol of its read signature or of
//! the baseline's is declared by both with different declarations, or when its read signature
//! has a subsort between two sorts the baseline declares that the baseline does not have
//! ([`KoreSignature::incompatibility`]). A constructor the mutant adds under a new name, or one
//! it lacks, is admitted: the first is refused where a state holds it, and the second is never
//! held.
//!
//! # Answers
//!
//! A condition answers each arrival with k-rust's [`StopDecision`]: it holds, it fails, it is
//! undecided (the path ends there, `stop-undecided`) or it refuses (the observation has no value
//! at that state, and the run has no result). A run with an undecided or refused answer is no
//! evidence on either side: the program is `unknown` for the mutant, cause `stop-condition`, and
//! on the baseline the program is not judged ([`crate::ExecutionFailureKind::StopCondition`]).

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use k_rust::kore::ast::{Definition, Sentence, Sort};
use k_rust::names::KoreAttribute;
use kink_native::execution::{StopArrival, StopCondition, StopDecision};
use serde_json::Value;

/// The source of a campaign's stop condition: a front end that reads a run's cells as values of
/// its own level and evaluates the condition in its observer definition.
pub trait StopOracle: Send + Sync {
    /// Each cell the condition reads, as the KORE cell symbols from the configuration's top down
    /// to the cell (k-rust `StopArrival::cell`'s path). A mutant is admitted only where it
    /// declares no sort or symbol these cells' sorts reach otherwise than the baseline (module
    /// documentation, "Reading a mutant's cells").
    fn cells(&self) -> &[Vec<String>];

    /// Run `body` once with the condition of one request, on the calling thread. The condition
    /// must be a function of the arrival's stop state's configuration, evaluated in the observer
    /// whatever definition the request runs.
    ///
    /// # Errors
    ///
    /// Why no condition can be given here (its observer does not load, for example); `body` is
    /// then not run, and the run is no evidence (`stop-condition`).
    fn with_condition(&self, body: &mut dyn FnMut(&mut dyn StopCondition)) -> Result<(), String>;
}

/// A campaign's stop condition: its identity, which every key of a run with the stop names, and
/// the oracle that asks it. Two conditions are equal when their identities are: the identity
/// names the observer, the function and the cells, which decide every answer.
#[derive(Clone)]
pub struct StopWhen {
    identity: Value,
    canonical: String,
    oracle: Arc<dyn StopOracle>,
}

impl StopWhen {
    /// The condition `oracle` asks, whose identity is `identity` (a JSON value that names what
    /// decides its answers: for the krs front end, the observer's Definition IR digest, the
    /// function and the cells).
    #[must_use]
    pub fn new(identity: Value, oracle: Arc<dyn StopOracle>) -> Self {
        Self {
            canonical: kink_patch::canonical_json(&identity),
            identity,
            oracle,
        }
    }

    /// The identity, as documents and keys name the condition.
    #[must_use]
    pub const fn identity(&self) -> &Value {
        &self.identity
    }

    /// The cells the condition reads ([`StopOracle::cells`]).
    #[must_use]
    pub fn cells(&self) -> &[Vec<String>] {
        self.oracle.cells()
    }

    /// `body` with the condition of one request, and the reason of the last arrival the
    /// condition was left undecided at, when one was.
    ///
    /// # Errors
    ///
    /// The oracle's refusal to give a condition ([`StopOracle::with_condition`]).
    pub(crate) fn asking<T>(
        &self,
        body: impl FnOnce(&mut dyn StopCondition) -> T,
    ) -> Result<(T, Option<String>), String> {
        let mut body = Some(body);
        let mut answer = None;
        let mut undecided = None;
        self.oracle.with_condition(&mut |condition| {
            if let Some(body) = body.take() {
                let mut recording = Recording {
                    inner: condition,
                    undecided: None,
                };
                answer = Some(body(&mut recording));
                undecided = recording.undecided;
            }
        })?;
        answer
            .map(|answer| (answer, undecided))
            .ok_or_else(|| "the stop condition's oracle gave the run no condition".to_owned())
    }
}

impl PartialEq for StopWhen {
    fn eq(&self, other: &Self) -> bool {
        self.canonical == other.canonical
    }
}

impl Eq for StopWhen {}

impl PartialOrd for StopWhen {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for StopWhen {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.canonical.cmp(&other.canonical)
    }
}

impl std::hash::Hash for StopWhen {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.canonical.hash(state);
    }
}

impl fmt::Debug for StopWhen {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_tuple("StopWhen")
            .field(&self.canonical)
            .finish()
    }
}

/// A condition that records the reason of the last arrival it left undecided.
struct Recording<'c> {
    inner: &'c mut dyn StopCondition,
    undecided: Option<String>,
}

impl StopCondition for Recording<'_> {
    fn decide(&mut self, arrival: &StopArrival<'_>) -> StopDecision {
        let decision = self.inner.decide(arrival);
        if let StopDecision::Undecided(reason) = &decision {
            self.undecided = Some(format!(
                "undecided at the arrival at `{}` at depth {}: {reason}",
                arrival.rule(),
                arrival.depth()
            ));
        }
        decision
    }
}

/// One symbol's declaration: its argument and result sorts, whether it is hooked, a
/// constructor or a function, and its hook. These decide how a term the symbol heads is read; a
/// symbol's other attributes (its source position, its `UNIQUE_ID`) do not.
#[derive(Clone, Debug, Eq, PartialEq)]
struct SymbolEntry {
    arguments: Vec<String>,
    result: String,
    hooked: bool,
    constructor: bool,
    function: bool,
    hook: Option<String>,
}

impl SymbolEntry {
    /// Whether a term this symbol heads can be a value of its result sort in a state: a
    /// constructor's or a hooked symbol's (a collection's, a builtin's).
    const fn heads_values(&self) -> bool {
        self.hooked || self.constructor
    }
}

/// The hook a declaration's attributes name, when they name one (as written, a malformed one
/// included, so that two declarations differ wherever their hooks do).
fn hook(attributes: &k_rust::kore::ast::Attributes) -> Option<String> {
    attributes
        .arguments(KoreAttribute::Hook)
        .map(|arguments| format!("{arguments:?}"))
}

/// The declarations of a definition a [`ReadSignature`] is read from: every sort with its
/// declaration, every non-parametric symbol with its declaration, the constructors and hooked
/// symbols by result sort, and every subsort, by its supersort. Built once per loaded side, and
/// only for a campaign with a stop condition.
#[derive(Clone, Debug, Default)]
pub(crate) struct KoreSignature {
    sorts: BTreeMap<String, String>,
    symbols: BTreeMap<String, SymbolEntry>,
    by_result: BTreeMap<String, BTreeSet<String>>,
    subsorts: BTreeMap<String, BTreeSet<String>>,
}

impl KoreSignature {
    /// The declarations of `definition`.
    pub(crate) fn of(definition: &Definition) -> Self {
        let mut signature = Self::default();
        for sentence in definition
            .modules
            .iter()
            .flat_map(|module| &module.sentences)
        {
            match sentence {
                Sentence::SortDeclaration {
                    hooked,
                    name,
                    parameters,
                    attributes,
                } => {
                    signature.sorts.insert(
                        name.clone(),
                        format!("{hooked} {parameters:?} {:?}", hook(attributes)),
                    );
                }
                Sentence::SymbolDeclaration {
                    hooked,
                    symbol,
                    argument_sorts,
                    result_sort,
                    attributes,
                } if symbol.sort_parameters.is_empty() => {
                    let entry = SymbolEntry {
                        arguments: argument_sorts.iter().map(sort_text).collect(),
                        result: sort_text(result_sort),
                        hooked: *hooked,
                        constructor: attributes.has(KoreAttribute::Constructor),
                        function: attributes.has(KoreAttribute::Function),
                        hook: hook(attributes),
                    };
                    if entry.heads_values() {
                        signature
                            .by_result
                            .entry(entry.result.clone())
                            .or_default()
                            .insert(symbol.name.clone());
                    }
                    signature.symbols.insert(symbol.name.clone(), entry);
                }
                Sentence::Axiom { attributes, .. } => {
                    if let Some((symbol, _)) = attributes.application(KoreAttribute::Subsort)
                        && let [sub, sup] = symbol.sort_parameters.as_slice()
                    {
                        signature
                            .subsorts
                            .entry(sort_text(sup))
                            .or_default()
                            .insert(sort_text(sub));
                    }
                }
                _ => {}
            }
        }
        signature
    }

    /// The part of this signature the cells `cells` reach ([`ReadSignature`]), or why a cell's
    /// sort cannot be read: a path that names no cell symbol of one argument.
    pub(crate) fn reads(&self, cells: &[Vec<String>]) -> Result<ReadSignature, String> {
        let mut pending = Vec::new();
        for path in cells {
            let Some(symbol) = path.last() else {
                return Err("a read cell names no cell symbol".to_owned());
            };
            // Every symbol may head a cell, whatever else it is.
            match self
                .symbols
                .get(symbol)
                .map(|entry| entry.arguments.as_slice())
            {
                Some([content]) => pending.push(content.clone()),
                Some(_) => return Err(format!("the read cell `{symbol}` is not a leaf cell")),
                None => return Err(format!("no symbol `{symbol}` heads a read cell")),
            }
        }
        let mut sorts = BTreeSet::new();
        let mut symbols = BTreeSet::new();
        while let Some(sort) = pending.pop() {
            if !sorts.insert(sort.clone()) {
                continue;
            }
            pending.extend(self.subsorts.get(&sort).into_iter().flatten().cloned());
            for name in self.by_result.get(&sort).into_iter().flatten() {
                pending.extend(self.symbols[name].arguments.iter().cloned());
                symbols.insert(name.clone());
            }
        }
        Ok(ReadSignature { sorts, symbols })
    }

    /// The symbols the cells `cells` reach in this signature ([`ReadSignature`]).
    pub(crate) fn read_symbols(&self, cells: &[Vec<String>]) -> Result<BTreeSet<String>, String> {
        self.reads(cells).map(|read| read.symbols)
    }

    /// Why the front end, which reads every side's cells with the declarations of `baseline`,
    /// cannot read the cells `cells` of a run of the definition whose declarations are `self`
    /// (module documentation, "Reading a mutant's cells"); `None` when it can; `Err` when either
    /// side's cells name no leaf cell.
    ///
    /// The cells of a run of `self` hold only terms of the sorts and symbols `self`'s read
    /// signature reaches, and the injections of its subsorts. Such a term is read as the term it
    /// is wherever each of its parts is declared alike on both sides, and refused wherever the
    /// baseline does not declare a part (its symbol, the sort of its literal): a refused reading
    /// leaves the arrival without an answer, and the run is no evidence (`stop-condition`). What
    /// can be read as another term is therefore exactly a part both sides declare otherwise: a
    /// sort or a symbol that one side's read cells reach and the two sides declare differently,
    /// or a subsort the mutant's read cells reach between two sorts the baseline declares, which
    /// the baseline does not have (the front end reads an injection as its argument, so the
    /// observer would be given a value of a sort its parameter does not admit). A part only one
    /// side declares (a constructor the mutant adds, or one it lacks) is never read otherwise.
    pub(crate) fn incompatibility(
        &self,
        baseline: &Self,
        cells: &[Vec<String>],
    ) -> Result<Option<String>, String> {
        let own = self.reads(cells)?;
        let theirs = baseline.reads(cells)?;
        for sort in own.sorts.union(&theirs.sorts) {
            let name = sort_name(sort);
            if let (Some(mine), Some(declared)) = (self.sorts.get(name), baseline.sorts.get(name))
                && mine != declared
            {
                return Ok(Some(format!("the sort `{sort}` is declared otherwise")));
            }
        }
        for name in own.symbols.union(&theirs.symbols) {
            if let (Some(mine), Some(declared)) =
                (self.symbols.get(name), baseline.symbols.get(name))
                && mine != declared
            {
                return Ok(Some(format!(
                    "the symbol `{name}` of the sort `{}` is declared otherwise",
                    declared.result
                )));
            }
        }
        for sup in &own.sorts {
            for sub in self.subsorts.get(sup).into_iter().flatten() {
                let declared = |sort: &str| baseline.sorts.contains_key(sort_name(sort));
                if declared(sub)
                    && declared(sup)
                    && !baseline
                        .subsorts
                        .get(sup)
                        .is_some_and(|subs| subs.contains(sub))
                {
                    return Ok(Some(format!(
                        "the sort `{sub}` is a subsort of `{sup}`, which it is not in the baseline"
                    )));
                }
            }
        }
        Ok(None)
    }
}

/// The part of a definition's signature a stop condition's cells reach (module documentation,
/// "Reading a mutant's cells"): the sorts reached from each read cell's content sort through the
/// argument sorts of their constructors and hooked symbols and through their subsorts, and those
/// symbols.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ReadSignature {
    sorts: BTreeSet<String>,
    symbols: BTreeSet<String>,
}

/// A sort as KORE text (`SortInt{}`, `SortMap{}`).
fn sort_text(sort: &Sort) -> String {
    sort.to_string()
}

/// The name of a sort given as KORE text: the text up to its first `{`.
fn sort_name(text: &str) -> &str {
    text.split('{').next().unwrap_or(text)
}

#[cfg(test)]
mod tests {
    use super::*;
    use k_rust::kore::parser::parse_definition;

    /// A definition with a configuration `<k>` of `SortK`, a sort `SortClock` with the
    /// constructors `extra`, and `constructors`, and a hooked `SortInt`.
    fn definition(constructors: &str) -> Definition {
        parse_definition(&format!(
            r#"[]
            module MAIN
                sort SortK{{}} []
                sort SortKItem{{}} []
                sort SortClock{{}} []
                sort SortOther{{}} []
                hooked-sort SortInt{{}} [hook{{}}("INT.Int")]
                symbol Lbl'-LT-'generatedTop'-GT-'{{}}(SortKCell{{}}) : SortGeneratedTopCell{{}} [constructor{{}}()]
                symbol Lbl'-LT-'k'-GT-'{{}}(SortK{{}}) : SortKCell{{}} [constructor{{}}()]
                symbol kseq{{}}(SortKItem{{}}, SortK{{}}) : SortK{{}} [constructor{{}}()]
                symbol dotk{{}}() : SortK{{}} [constructor{{}}()]
                symbol Lblclock{{}}(SortInt{{}}, SortInt{{}}) : SortClock{{}} [constructor{{}}()]
                symbol Lblother{{}}() : SortOther{{}} [constructor{{}}()]
                {constructors}
                axiom{{R}} \exists{{R}}(Val:SortKItem{{}}, \equals{{SortKItem{{}}, R}}(Val:SortKItem{{}}, inj{{SortClock{{}}, SortKItem{{}}}}(From:SortClock{{}}))) [subsort{{SortClock{{}}, SortKItem{{}}}}()]
            endmodule []"#
        ))
        .expect("a KORE definition")
    }

    fn cells() -> Vec<Vec<String>> {
        vec![vec![
            "Lbl'-LT-'generatedTop'-GT-'".to_owned(),
            "Lbl'-LT-'k'-GT-'".to_owned(),
        ]]
    }

    fn signature(constructors: &str) -> KoreSignature {
        KoreSignature::of(&definition(constructors))
    }

    fn reads(constructors: &str) -> ReadSignature {
        signature(constructors)
            .reads(&cells())
            .expect("the cell is a leaf cell")
    }

    /// Why a mutant declaring `mutant` cannot be read as a baseline declaring `baseline` reads.
    fn incompatibility(mutant: &str, baseline: &str) -> Option<String> {
        signature(mutant)
            .incompatibility(&signature(baseline), &cells())
            .expect("the cell is a leaf cell")
    }

    /// The read signature reaches a cell's content sort, its constructors' argument sorts and
    /// its subsorts: through `SortK` and the subsort `SortClock < SortKItem` to `clock` and the
    /// hooked `SortInt`, but not to `SortOther`, which no read cell reaches.
    #[test]
    fn the_read_signature_is_what_the_cells_reach() {
        let read = reads("");
        assert!(read.symbols.contains("Lblclock"));
        assert!(read.sorts.contains("SortInt{}"));
        assert!(!read.symbols.contains("Lblother"));
        // A mutant that declares an unreached sort's constructors otherwise reads alike.
        assert_eq!(
            incompatibility(
                "symbol Lblother{}(SortInt{}) : SortOther{} [constructor{}()]",
                ""
            ),
            None
        );
        assert_eq!(incompatibility("", ""), None);
    }

    /// A symbol both sides declare, which either side's read cells reach, declared with another
    /// signature, as a function, or as a constructor where the baseline has a function, makes the
    /// mutant unreadable, naming the symbol; so does a subsort of a reached sort that the
    /// baseline does not have: such a mutant is not admitted under a condition
    /// (`stop-condition-incompatible`).
    #[test]
    fn a_symbol_both_declare_otherwise_is_incompatible() {
        let halted = "symbol Lblhalted{}(SortInt{}) : SortClock{} [constructor{}()]";
        let function = "symbol Lblhalted{}(SortInt{}) : SortClock{} [function{}()]";
        for (mutant, baseline, named) in [
            (
                "symbol Lblhalted{}(SortInt{}, SortInt{}) : SortClock{} [constructor{}()]",
                halted,
                "Lblhalted",
            ),
            (function, halted, "Lblhalted"),
            (halted, function, "Lblhalted"),
            (
                r"axiom{R} \exists{R}(Val:SortKItem{}, \equals{SortKItem{}, R}(Val:SortKItem{}, inj{SortOther{}, SortKItem{}}(From:SortOther{}))) [subsort{SortOther{}, SortKItem{}}()]",
                "",
                "SortOther",
            ),
        ] {
            let difference = incompatibility(mutant, baseline)
                .unwrap_or_else(|| panic!("{mutant}: no incompatibility"));
            assert!(difference.contains(named), "{mutant}: {difference}");
        }
    }

    /// A constructor of a reached sort that only one side declares is never read otherwise: the
    /// front end refuses a symbol the baseline does not declare, and a symbol the mutant lacks
    /// is in none of its states.
    #[test]
    fn a_symbol_only_one_side_declares_is_compatible() {
        let halted = "symbol Lblhalted{}(SortInt{}) : SortClock{} [constructor{}()]";
        assert_eq!(incompatibility("", halted), None);
        assert_eq!(incompatibility(halted, ""), None);
    }

    /// A read cell must be a leaf cell the definition declares.
    #[test]
    fn a_cell_without_a_leaf_symbol_is_refused() {
        let signature = KoreSignature::of(&definition(""));
        assert!(
            signature
                .reads(&[vec!["Lbl'-LT-'nothing'-GT-'".to_owned()]])
                .is_err()
        );
        assert!(signature.reads(&[Vec::new()]).is_err());
    }
}
