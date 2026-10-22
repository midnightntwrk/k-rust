//! The one place that reads the backend's condition records (`collectConditions`, G-7) into
//! the algebra's [`Cond`]. A change of the record shape is absorbed here.
//!
//! - Only complete entries count: a record whose verdict is `reentered` is followed by the
//!   complete entry of the same attempt and is skipped; a record whose attempt stopped, left the
//!   condition undecided or ended without a verdict gives no distance, and neither does a
//!   `chosen` record (its terms may be one model's of a value the definition leaves open). A
//!   `held` record is at distance 0. A `refuted` record is measured, and gives no distance when
//!   the measure finds every atom satisfied (it was refuted by the path, which the record does
//!   not show).
//! - Every node carries the truth the record's evaluation decided. The measure uses it where it
//!   is decided ([`Cond::Decided`]): a node that holds is at distance 0 without measuring its
//!   children, and a node that is `undefined` or `undecided` gives no distance.
//! - The K Boolean connectives are strict functions on `Bool`: `notBool`, `andBool` and
//!   `andThenBool`, `orBool` and `orElseBool`, `impliesBool`, and `xorBool` as
//!   `(a andBool notBool b) orBool (notBool a andBool b)`; an undefined operand makes them
//!   undefined, which the decided truth already says. This holds for the operand `andThenBool`
//!   or `orElseBool` does not evaluate too, and no bound such as `d(a) + 1` (the first
//!   operand's distance plus one) is given for it: a symbol applied to an undefined argument is
//!   undefined, and the variable of `false andThenBool _ => false` ranges over defined values,
//!   so `false andThenBool ⊥` is `⊥`. The guard then has no truth value to be near, and a
//!   distance for it would be invented; it would also rank such an input above a defined miss
//!   farther than `d(a) + 1`, pulling the climb toward the undefined point. The matching-logic
//!   connectives `\not`, `\and`, `\or`, `\implies`, `\iff` combine two-valued predicates the
//!   same way. An `equals`
//!   node `\equals(b, literal)` is `b` for `true` and `notBool b` for `false`.
//! - An atom is measured by its operands only when they are ground values (`kind: value`);
//!   `unevaluated`, `symbolic`, `undefined`, `stopped` and `omitted` operands leave it to its
//!   decided truth (`super::distance`).

use k_rust::backend::{
    ConditionAtomOutput, ConditionNodeOutput, ConditionRecordOutput, ConnectiveOutput,
    RecordedValueOutput, RuleConditionsOutput, TruthOutput, VerdictOutput,
};
use num_bigint::BigInt;
use serde_json::Value as Json;

use crate::values::Value;

use super::{
    GuardEntry, Guards,
    distance::{Comparison, Cond, Distance, Operand, Truth, distance},
};

/// Each complete record of each rule in `conditions`, by rule id, in the records' order: its
/// guard distance (`None` when it gives none), the ground `Int` and `String` values it binds, and
/// the ground `Int` and `Bool` values its condition's atoms read.
pub(crate) fn guards(conditions: &[RuleConditionsOutput]) -> Guards {
    conditions
        .iter()
        .map(|rule| {
            let entries = rule
                .records
                .iter()
                .filter(|record| record.verdict != Some(VerdictOutput::Reentered))
                .map(|record| GuardEntry {
                    distance: record_distance(record),
                    refuted: record.verdict == Some(VerdictOutput::Refuted) && !record.chosen,
                    reads: record
                        .bindings
                        .iter()
                        .filter_map(|binding| match &binding.value {
                            RecordedValueOutput::Value { term } => operand(term),
                            _ => None,
                        })
                        .collect(),
                    guard_values: guard_values(record),
                })
                .collect();
            (rule.rule.clone(), entries)
        })
        .collect()
}

/// The ground `Int` and `Bool` values of the bindings that some atom of `record`'s condition
/// reads (each atom's `reads` names positions in the record's bindings), in binding order, each
/// once: the values the condition depends on.
fn guard_values(record: &ConditionRecordOutput) -> Vec<Value> {
    let mut read = std::collections::BTreeSet::new();
    let mut work: Vec<&ConditionNodeOutput> = record.condition.iter().collect();
    while let Some(node) = work.pop() {
        match node {
            ConditionNodeOutput::Connective { children, .. } => work.extend(children),
            ConditionNodeOutput::Equals { child, .. } => work.push(child),
            ConditionNodeOutput::Atom(atom) => read.extend(atom.reads.iter().copied()),
        }
    }
    read.into_iter()
        .filter_map(|index| match &record.bindings.get(index)?.value {
            RecordedValueOutput::Value { term } => int_or_bool(term),
            _ => None,
        })
        .collect()
}

/// A comparison a refuted condition record holds with the wrong truth for its guard, and its two
/// ground operands, as the run compared them: had the comparison held, that atom would not have
/// refuted the guard (the run-time dictionary, `crate::proposers::runtime`).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Compared {
    /// The catalog id of the rule whose condition holds the atom.
    pub(crate) rule: String,
    /// The comparison the guard needs to hold: the atom's own, or its negation where the atom
    /// is under a negation.
    pub(crate) comparison: Comparison,
    /// The left operand's value.
    pub(crate) left: Operand,
    /// The right operand's value.
    pub(crate) right: Operand,
}

/// The comparisons of the last refuted complete record of each rule of `conditions` that its
/// guard needed the other way round ([`Compared`]), in the rules' order, each once, at most
/// `limit` of them.
///
/// Only each guard's last refuted entry is read: a run went on after the earlier ones (another
/// rule took the step, or the next attempt came), so the last is where the guard last stopped
/// the run, which on a run over a list is the element where it ended.
///
/// An atom is taken when it is a comparison over two ground `Int` or two ground `String` values
/// (the comparisons the distance measures, [`atom`]), its truth is decided, and the truth is the
/// one that refutes the guard at the atom's polarity: false under an even number of negations,
/// true under an odd number. A `notBool`, `\not` or `\equals(b, false)` flips the polarity, the
/// premise of an implication is under a negation, and the operands of `xorBool` and `\iff`,
/// which a guard needs either way, are not read. `chosen` records, whose operands may be one
/// model's values of something the definition leaves open, are not read either.
pub(crate) fn comparisons(conditions: &[RuleConditionsOutput], limit: usize) -> Vec<Compared> {
    let mut found = Vec::new();
    for rule in conditions {
        let last = rule
            .records
            .iter()
            .rev()
            .find(|record| record.verdict == Some(VerdictOutput::Refuted) && !record.chosen);
        for conjunct in last.into_iter().flat_map(|record| &record.condition) {
            wrong_atoms(conjunct, true, &rule.rule, limit, &mut found);
        }
    }
    found
}

/// Push onto `found` the comparisons below `node` whose truth refutes it at `positive` polarity
/// ([`comparisons`]), up to `limit`.
fn wrong_atoms(
    node: &ConditionNodeOutput,
    positive: bool,
    rule: &str,
    limit: usize,
    found: &mut Vec<Compared>,
) {
    use ConnectiveOutput as C;
    if found.len() >= limit {
        return;
    }
    match node {
        ConditionNodeOutput::Connective {
            connective,
            children,
            ..
        } => match (connective, &children[..]) {
            (C::NotBool | C::Not, [child]) => wrong_atoms(child, !positive, rule, limit, found),
            (C::AndBool | C::AndThenBool | C::And | C::OrBool | C::OrElseBool | C::Or, _) => {
                for child in children {
                    wrong_atoms(child, positive, rule, limit, found);
                }
            }
            (C::ImpliesBool | C::Implies, [premise, consequent]) => {
                wrong_atoms(premise, !positive, rule, limit, found);
                wrong_atoms(consequent, positive, rule, limit, found);
            }
            _ => {}
        },
        ConditionNodeOutput::Equals { literal, child, .. } => {
            wrong_atoms(child, positive == *literal, rule, limit, found);
        }
        ConditionNodeOutput::Atom(atom) => {
            let refuting = if positive {
                TruthOutput::False
            } else {
                TruthOutput::True
            };
            if atom.value != refuting {
                return;
            }
            let Cond::Compare(comparison, Some((left, right))) = self::atom(atom) else {
                return;
            };
            let compared = Compared {
                rule: rule.to_owned(),
                comparison: if positive {
                    comparison
                } else {
                    comparison.negated()
                },
                left,
                right,
            };
            if !found.contains(&compared) {
                found.push(compared);
            }
        }
    }
}

/// An `Int` or `Bool` domain value in KORE JSON (in its envelope or not, under injections).
fn int_or_bool(term: &Json) -> Option<Value> {
    let term = term.get("term").unwrap_or(term);
    match term.get("tag")?.as_str()? {
        "DV" => {
            let value = term.get("value")?.as_str()?;
            match term.get("sort")?.get("name")?.as_str()? {
                "SortInt" => value.parse::<BigInt>().ok().map(Value::Int),
                "SortBool" => match value {
                    "true" => Some(Value::Bool(true)),
                    "false" => Some(Value::Bool(false)),
                    _ => None,
                },
                _ => None,
            }
        }
        "App" if term.get("name")?.as_str()? == "inj" => match term.get("args")?.as_array()?[..] {
            [ref inner] => int_or_bool(inner),
            _ => None,
        },
        _ => None,
    }
}

/// The guard distance of one complete record (module documentation).
fn record_distance(record: &ConditionRecordOutput) -> Option<Distance> {
    if record.chosen {
        return None;
    }
    match record.verdict? {
        VerdictOutput::Held => Some(Distance::zero()),
        VerdictOutput::Refuted => distance(&Cond::And(
            record
                .condition
                .iter()
                .map(|conjunct| node(conjunct).0)
                .collect(),
        ))
        .filter(|distance| !distance.is_zero()),
        VerdictOutput::Undecided | VerdictOutput::Stopped | VerdictOutput::Reentered => None,
    }
}

fn truth(value: TruthOutput) -> Truth {
    match value {
        TruthOutput::True => Truth::True,
        TruthOutput::False => Truth::False,
        TruthOutput::Undefined | TruthOutput::Undecided => Truth::Unknown,
    }
}

/// The algebra's form of `node`, and whether its subtree meets an undefined value (a node or
/// an operand). A node whose subtree meets one is read as undecided whatever truth it carries:
/// a matching-logic predicate is two-valued, so `\not \equals(b, true)` over an undefined `b`
/// is true, and a distance of 0 from it would reward a move that made `b` undefined.
fn node(node: &ConditionNodeOutput) -> (Cond, bool) {
    let decided = |value: TruthOutput, undefined: bool, cond: Cond| {
        let undefined = undefined || value == TruthOutput::Undefined;
        let truth = if undefined {
            Truth::Unknown
        } else {
            truth(value)
        };
        (Cond::Decided(truth, Box::new(cond)), undefined)
    };
    match node {
        ConditionNodeOutput::Connective {
            connective,
            children,
            value,
        } => {
            let (children, undefined): (Vec<Cond>, Vec<bool>) =
                children.iter().map(self::node).unzip();
            decided(
                *value,
                undefined.contains(&true),
                connect(*connective, children),
            )
        }
        ConditionNodeOutput::Equals {
            literal,
            child,
            value,
        } => {
            let (child, undefined) = self::node(child);
            let cond = if *literal {
                child
            } else {
                Cond::Not(Box::new(child))
            };
            decided(*value, undefined, cond)
        }
        ConditionNodeOutput::Atom(atom) => {
            let undefined = atom
                .operands
                .iter()
                .any(|operand| matches!(operand, RecordedValueOutput::Undefined));
            decided(atom.value, undefined, self::atom(atom))
        }
    }
}

/// The algebra's form of `connective` over `children` (a malformed arity gives an unknown
/// atom, no signal).
fn connect(connective: ConnectiveOutput, mut children: Vec<Cond>) -> Cond {
    use ConnectiveOutput as C;
    let not = |cond: Cond| Cond::Not(Box::new(cond));
    match (connective, children.len()) {
        (C::NotBool | C::Not, 1) => not(children.remove(0)),
        (C::AndBool | C::AndThenBool | C::And, _) => Cond::And(children),
        (C::OrBool | C::OrElseBool | C::Or, _) => Cond::Or(children),
        (C::ImpliesBool | C::Implies, 2) => {
            let consequent = children.remove(1);
            Cond::Implies(Box::new(children.remove(0)), Box::new(consequent))
        }
        (C::XorBool, 2) => {
            let (a, b) = (children[0].clone(), children[1].clone());
            Cond::Or(vec![
                Cond::And(vec![a.clone(), not(b.clone())]),
                Cond::And(vec![not(a), b]),
            ])
        }
        (C::Iff, 2) => {
            let (a, b) = (children[0].clone(), children[1].clone());
            Cond::Or(vec![
                Cond::And(vec![a.clone(), b.clone()]),
                Cond::And(vec![not(a), not(b)]),
            ])
        }
        _ => Cond::Atom(Truth::Unknown),
    }
}

/// An atom measured by its operands when it is a comparison over two ground `Int` or `String`
/// values; otherwise counted by its truth (the caller wraps it in that truth).
fn atom(atom: &ConditionAtomOutput) -> Cond {
    let ground: Option<Vec<&Json>> = atom
        .operands
        .iter()
        .map(|operand| match operand {
            RecordedValueOutput::Value { term } => Some(term),
            _ => None,
        })
        .collect();
    if let Some(ground) = ground
        && let Some((comparison, family)) = comparison(atom.head.as_deref(), atom.hook.as_deref())
        && let [left, right] = ground[..]
    {
        match (operand(left), operand(right), family) {
            (Some(Operand::Int(a)), Some(Operand::Int(b)), Family::Int | Family::Any) => {
                return Cond::Compare(comparison, Some((Operand::Int(a), Operand::Int(b))));
            }
            (Some(Operand::Str(a)), Some(Operand::Str(b)), Family::Str | Family::Any) => {
                let comparison = match comparison {
                    Comparison::IntEq | Comparison::StrEq => Comparison::StrEq,
                    _ => Comparison::StrNe,
                };
                return Cond::Compare(comparison, Some((Operand::Str(a), Operand::Str(b))));
            }
            // Operands of another sort are counted by the atom's truth.
            _ => {}
        }
    }
    Cond::Atom(truth(atom.value))
}

/// Which operands a comparison measures.
#[derive(Clone, Copy)]
enum Family {
    /// Integers (`INT` hooks).
    Int,
    /// Strings (`STRING` hooks).
    Str,
    /// Terms of any sort (`==K`, `=/=K`, `\equals`): measured when both operands are integers
    /// or both are strings, and counted by truth otherwise.
    Any,
}

/// The comparison an atom's hook (or, without one, its matching-logic head) names, with the
/// operands it measures. An equality of the `Any` family is given as `IntEq`/`IntNe` and read
/// as `StrEq`/`StrNe` over strings.
fn comparison(head: Option<&str>, hook: Option<&str>) -> Option<(Comparison, Family)> {
    Some(match hook {
        Some("INT.eq") => (Comparison::IntEq, Family::Int),
        Some("INT.ne") => (Comparison::IntNe, Family::Int),
        Some("INT.lt") => (Comparison::IntLt, Family::Int),
        Some("INT.le") => (Comparison::IntLe, Family::Int),
        Some("INT.gt") => (Comparison::IntGt, Family::Int),
        Some("INT.ge") => (Comparison::IntGe, Family::Int),
        Some("STRING.eq") => (Comparison::StrEq, Family::Str),
        Some("STRING.ne") => (Comparison::StrNe, Family::Str),
        Some("KEQUAL.eq") => (Comparison::IntEq, Family::Any),
        Some("KEQUAL.ne") => (Comparison::IntNe, Family::Any),
        None if head == Some("\\equals") => (Comparison::IntEq, Family::Any),
        _ => return None,
    })
}

/// An `Int` or `String` domain value in KORE JSON (in its envelope or not, under injections).
fn operand(term: &Json) -> Option<Operand> {
    let term = term.get("term").unwrap_or(term);
    match term.get("tag")?.as_str()? {
        "DV" => {
            let sort = term.get("sort")?.get("name")?.as_str()?;
            let value = term.get("value")?.as_str()?;
            match sort {
                "SortInt" => value.parse::<BigInt>().ok().map(Operand::Int),
                "SortString" => Some(Operand::Str(value.to_owned())),
                _ => None,
            }
        }
        "App" if term.get("name")?.as_str()? == "inj" => match term.get("args")?.as_array()?[..] {
            [ref inner] => operand(inner),
            _ => None,
        },
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use k_rust::backend::RecordedBindingOutput;
    use serde_json::json;

    use super::*;

    fn int(value: i64) -> RecordedValueOutput {
        RecordedValueOutput::Value {
            term: json!({"format": "KORE", "version": 1, "term": {
                "tag": "DV",
                "sort": {"tag": "SortApp", "name": "SortInt", "args": []},
                "value": value.to_string(),
            }}),
        }
    }

    /// A Boolean application atom with `hook`.
    fn atom(
        hook: &str,
        operands: Vec<RecordedValueOutput>,
        value: TruthOutput,
    ) -> ConditionNodeOutput {
        ConditionNodeOutput::Atom(ConditionAtomOutput {
            head: Some("Lbl".into()),
            hook: Some(hook.into()),
            operands,
            reads: Vec::new(),
            value,
        })
    }

    /// The conjunct `requires b`: `\equals(b, true)`, true exactly when `b` is.
    fn requires(child: ConditionNodeOutput) -> ConditionNodeOutput {
        let value = match node_truth(&child) {
            TruthOutput::True => TruthOutput::True,
            TruthOutput::False | TruthOutput::Undefined => TruthOutput::False,
            TruthOutput::Undecided => TruthOutput::Undecided,
        };
        ConditionNodeOutput::Equals {
            literal: true,
            child: Box::new(child),
            value,
        }
    }

    fn node_truth(node: &ConditionNodeOutput) -> TruthOutput {
        match node {
            ConditionNodeOutput::Connective { value, .. }
            | ConditionNodeOutput::Equals { value, .. } => *value,
            ConditionNodeOutput::Atom(atom) => atom.value,
        }
    }

    fn connective(
        connective: ConnectiveOutput,
        children: Vec<ConditionNodeOutput>,
        value: TruthOutput,
    ) -> ConditionNodeOutput {
        ConditionNodeOutput::Connective {
            connective,
            children,
            value,
        }
    }

    fn entry(
        condition: Vec<ConditionNodeOutput>,
        verdict: Option<VerdictOutput>,
    ) -> ConditionRecordOutput {
        ConditionRecordOutput {
            bindings: Vec::new(),
            condition,
            verdict,
            chosen: false,
        }
    }

    fn rule(records: Vec<ConditionRecordOutput>) -> RuleConditionsOutput {
        RuleConditionsOutput {
            rule: "r".into(),
            records,
            truncated: false,
        }
    }

    fn distances(records: Vec<ConditionRecordOutput>) -> Vec<Option<Distance>> {
        guards(&[rule(records)])["r"]
            .iter()
            .map(|entry| entry.distance.clone())
            .collect()
    }

    fn one(condition: Vec<ConditionNodeOutput>, verdict: VerdictOutput) -> Option<Distance> {
        distances(vec![entry(condition, Some(verdict))])[0].clone()
    }

    use TruthOutput::{False, True, Undecided, Undefined};
    use VerdictOutput::{Held, Reentered, Refuted, Stopped};

    #[test]
    fn integer_atoms_are_measured_by_their_operands() {
        // 1000 < D < 1100 at D = -3.
        let window = vec![
            requires(atom("INT.gt", vec![int(-3), int(1000)], False)),
            requires(atom("INT.lt", vec![int(-3), int(1100)], True)),
        ];
        assert_eq!(
            one(window, Refuted),
            Some(Distance::normalized(1004u32.into()))
        );
        // Under a K connective: `notBool (D <=Int 1000)` at D = -3 is D > 1000.
        let negated = vec![requires(connective(
            ConnectiveOutput::NotBool,
            vec![atom("INT.le", vec![int(-3), int(1000)], True)],
            False,
        ))];
        assert_eq!(
            one(negated, Refuted),
            Some(Distance::normalized(1004u32.into()))
        );
    }

    #[test]
    fn only_complete_decided_records_count() {
        let far = || vec![requires(atom("INT.eq", vec![int(1), int(9)], False))];
        // A held record is at distance 0; a refuted one is measured.
        let held = vec![requires(atom("INT.eq", vec![int(9), int(9)], True))];
        assert_eq!(one(held, Held), Some(Distance::zero()));
        // A reentered record is followed by the complete entry: only that one is an entry.
        let records = vec![entry(far(), Some(Reentered)), entry(far(), Some(Refuted))];
        assert_eq!(
            distances(records),
            vec![Some(Distance::normalized(8u32.into()))]
        );
        // Undecided, stopped and verdict-less attempts and chosen records give no distance.
        for verdict in [Some(VerdictOutput::Undecided), Some(Stopped), None] {
            assert_eq!(distances(vec![entry(far(), verdict)]), vec![None]);
        }
        let mut chosen = entry(far(), Some(Refuted));
        chosen.chosen = true;
        assert_eq!(distances(vec![chosen]), vec![None]);
        // A refuted record whose atoms all hold was refuted by the path: no distance, never 0.
        let path = vec![requires(atom("INT.eq", vec![int(9), int(9)], True))];
        assert_eq!(one(path, Refuted), None);
    }

    #[test]
    fn undefined_and_undecided_nodes_give_no_distance() {
        // `notBool (X /Int Y >Int 3)` at Y = 0: the comparison and the notBool are undefined,
        // the conjunct false, the verdict refuted: no gradient.
        let undefined = vec![requires(connective(
            ConnectiveOutput::NotBool,
            vec![atom(
                "INT.gt",
                vec![RecordedValueOutput::Undefined, int(3)],
                Undefined,
            )],
            Undefined,
        ))];
        assert_eq!(one(undefined, Refuted), None);
        // A strict `andThenBool` over an undefined operand is undefined.
        let strict = vec![requires(connective(
            ConnectiveOutput::AndThenBool,
            vec![
                atom("INT.eq", vec![int(1), int(2)], False),
                atom(
                    "INT.gt",
                    vec![RecordedValueOutput::Undefined, int(3)],
                    Undefined,
                ),
            ],
            Undefined,
        ))];
        assert_eq!(one(strict, Refuted), None);
        for operand in [
            RecordedValueOutput::Symbolic { term: json!({}) },
            RecordedValueOutput::Unevaluated { term: json!({}) },
            RecordedValueOutput::Stopped,
            RecordedValueOutput::Omitted,
        ] {
            // An undecided atom over such an operand is no signal.
            let undecided = vec![requires(atom(
                "INT.eq",
                vec![int(1), operand.clone()],
                Undecided,
            ))];
            assert_eq!(one(undecided, Refuted), None);
            // A decided one counts by its truth only: its operands are not measured.
            let decided = vec![requires(atom("INT.eq", vec![int(1), operand], False))];
            assert_eq!(
                one(decided, Refuted),
                Some(Distance::normalized(1u32.into()))
            );
        }
    }

    #[test]
    fn an_undefined_value_never_gives_a_distance_of_zero() {
        // `notBool pb(X)` with every operand a value, and `pb(X)` undefined: no distance under
        // the K negation.
        let undefined_bool = || atom("LblPb", vec![int(0)], Undefined);
        let not_bool = vec![requires(connective(
            ConnectiveOutput::NotBool,
            vec![undefined_bool()],
            Undefined,
        ))];
        assert_eq!(one(not_bool, Refuted), None);
        // Under the matching-logic negation, `\not \equals(pb(X), true)` is true where `pb(X)`
        // is undefined, and the record says so; the measure still gives no distance, and a
        // record whose other conjunct fails gives none either.
        let ml_not = || {
            connective(
                ConnectiveOutput::Not,
                vec![requires(undefined_bool())],
                True,
            )
        };
        assert_eq!(one(vec![ml_not()], Held), Some(Distance::zero()));
        let failing = vec![
            ml_not(),
            requires(atom("INT.eq", vec![int(1), int(2)], False)),
        ];
        assert_eq!(one(failing, Refuted), None);
        // A predicate over an undefined operand (`\ceil(⊥)`, two-valued false) under `\not`.
        let ceil = ConditionNodeOutput::Atom(ConditionAtomOutput {
            head: Some("\\ceil".into()),
            hook: None,
            operands: vec![RecordedValueOutput::Undefined],
            reads: Vec::new(),
            value: False,
        });
        let not_ceil = vec![
            connective(ConnectiveOutput::Not, vec![ceil], True),
            requires(atom("INT.eq", vec![int(1), int(2)], False)),
        ];
        assert_eq!(one(not_ceil, Refuted), None);
    }

    #[test]
    fn a_decided_true_node_is_not_measured_below() {
        // `D >Int 1000 orBool <undecided>` decided true by its first operand: distance 0
        // contributes nothing to the conjunction; the second conjunct is measured.
        let condition = vec![
            requires(connective(
                ConnectiveOutput::OrBool,
                vec![
                    atom("INT.gt", vec![int(2000), int(1000)], True),
                    atom("SET.in", vec![int(1)], Undecided),
                ],
                True,
            )),
            requires(atom("INT.eq", vec![int(5), int(7)], False)),
        ];
        assert_eq!(
            one(condition, Refuted),
            Some(Distance::normalized(2u32.into()))
        );
    }

    #[test]
    fn xor_and_iff_are_read_by_their_definitions() {
        // `(A ==Int 1) xorBool (B ==Int 1)` at A = B = 3: either equality, 2 steps.
        let xor = vec![requires(connective(
            ConnectiveOutput::XorBool,
            vec![
                atom("INT.eq", vec![int(3), int(1)], False),
                atom("INT.eq", vec![int(3), int(1)], False),
            ],
            False,
        ))];
        assert_eq!(one(xor, Refuted), Some(Distance::normalized(2u32.into())));
        // `\iff(A ==Int 1, B ==Int 1)` at A = 1, B = 3: B to 1 (2 steps) or A off 1 (1).
        let iff = vec![connective(
            ConnectiveOutput::Iff,
            vec![
                requires(atom("INT.eq", vec![int(1), int(1)], True)),
                requires(atom("INT.eq", vec![int(3), int(1)], False)),
            ],
            False,
        )];
        assert_eq!(one(iff, Refuted), Some(Distance::normalized(1u32.into())));
    }

    #[test]
    fn the_ground_integer_and_string_bindings_are_read() {
        let string = RecordedValueOutput::Value {
            term: json!({
                "tag": "DV",
                "sort": {"tag": "SortApp", "name": "SortString", "args": []},
                "value": "open",
            }),
        };
        let binding = |name: &str, value| RecordedBindingOutput {
            variable: json!(name),
            value,
        };
        let mut record = entry(
            vec![requires(atom("INT.eq", vec![int(1), int(2)], False))],
            Some(Refuted),
        );
        record.bindings = vec![
            binding("A", int(5)),
            binding("B", RecordedValueOutput::Symbolic { term: json!({}) }),
            binding("S", string),
            binding("U", RecordedValueOutput::Undefined),
        ];
        let entry = &guards(&[rule(vec![record])])["r"][0];
        assert_eq!(
            entry.reads,
            vec![Operand::Int(5.into()), Operand::Str("open".into())]
        );
    }

    #[test]
    fn the_comparisons_are_the_atoms_that_refuted_the_last_refuted_entry() {
        use Comparison::{IntEq, IntLe};
        let compared = |comparison, left: i64, right: i64| Compared {
            rule: "r".into(),
            comparison,
            left: Operand::Int(left.into()),
            right: Operand::Int(right.into()),
        };
        // `N ==Int M andBool A <=Int B andBool notBool (A ==Int 0)`: the first atom refutes it
        // (false), the second holds, and the negated third refutes it by holding.
        let entry_at = |nonce: i64, amount: i64| {
            entry(
                vec![requires(connective(
                    ConnectiveOutput::AndBool,
                    vec![
                        atom(
                            "INT.eq",
                            vec![int(nonce), int(2)],
                            if nonce == 2 { True } else { False },
                        ),
                        atom("INT.le", vec![int(amount), int(400)], True),
                        connective(
                            ConnectiveOutput::NotBool,
                            vec![atom(
                                "INT.eq",
                                vec![int(amount), int(0)],
                                if amount == 0 { True } else { False },
                            )],
                            if amount == 0 { False } else { True },
                        ),
                    ],
                    False,
                ))],
                Some(Refuted),
            )
        };
        let records = vec![
            entry_at(1, 0),
            entry_at(1, 0),
            entry_at(5, 0),
            entry(
                vec![requires(atom("INT.eq", vec![int(9), int(9)], True))],
                Some(Held),
            ),
        ];
        // Only the last refuted entry is read; the held entry after it has nothing to change.
        assert_eq!(
            comparisons(&[rule(records.clone())], 64),
            vec![compared(IntEq, 5, 2), compared(Comparison::IntNe, 0, 0)]
        );
        assert_eq!(
            comparisons(&[rule(records)], 1),
            vec![compared(IntEq, 5, 2)]
        );
        // The premise of an implication is under a negation: `A >Int 3 impliesBool B ==Int 1`
        // refuted at A = 5, B = 4 needs B ==Int 1, or A >Int 3 false, which is A <=Int 3.
        let implication = entry(
            vec![requires(connective(
                ConnectiveOutput::ImpliesBool,
                vec![
                    atom("INT.gt", vec![int(5), int(3)], True),
                    atom("INT.eq", vec![int(4), int(1)], False),
                ],
                False,
            ))],
            Some(Refuted),
        );
        assert_eq!(
            comparisons(&[rule(vec![implication])], 64),
            vec![compared(IntLe, 5, 3), compared(IntEq, 4, 1)]
        );
    }

    #[test]
    fn negations_flip_the_comparison_and_unread_atoms_give_none() {
        use Comparison::{IntGt, IntLe};
        let compared = |comparison, left: i64, right: i64| Compared {
            rule: "r".into(),
            comparison,
            left: Operand::Int(left.into()),
            right: Operand::Int(right.into()),
        };
        // `\equals(b, false)` flips the polarity, `xorBool` is not read, nor a chosen record,
        // nor operands that are not values, nor an undefined atom.
        let flipped = entry(
            vec![ConditionNodeOutput::Equals {
                literal: false,
                child: Box::new(atom("INT.gt", vec![int(8), int(1)], True)),
                value: False,
            }],
            Some(Refuted),
        );
        assert_eq!(
            comparisons(&[rule(vec![flipped])], 64),
            vec![compared(IntLe, 8, 1)]
        );
        let xor = entry(
            vec![requires(connective(
                ConnectiveOutput::XorBool,
                vec![
                    atom("INT.eq", vec![int(3), int(1)], False),
                    atom("INT.eq", vec![int(3), int(1)], False),
                ],
                False,
            ))],
            Some(Refuted),
        );
        let mut chosen = entry(
            vec![requires(atom("INT.eq", vec![int(3), int(1)], False))],
            Some(Refuted),
        );
        chosen.chosen = true;
        let symbolic = entry(
            vec![requires(atom(
                "INT.eq",
                vec![int(3), RecordedValueOutput::Symbolic { term: json!({}) }],
                False,
            ))],
            Some(Refuted),
        );
        let undefined = entry(
            vec![requires(atom(
                "INT.eq",
                vec![int(3), RecordedValueOutput::Undefined],
                Undefined,
            ))],
            Some(Refuted),
        );
        for record in [xor, chosen, symbolic, undefined] {
            assert_eq!(comparisons(&[rule(vec![record])], 64), Vec::new());
        }
        // `IntGt` keeps its direction: `X >Int 4096` refuted at X = 7.
        let window = entry(
            vec![requires(atom("INT.gt", vec![int(7), int(4096)], False))],
            Some(Refuted),
        );
        assert_eq!(
            comparisons(&[rule(vec![window])], 64),
            vec![compared(IntGt, 7, 4096)]
        );
    }

    #[test]
    fn other_atoms_count_by_their_truth() {
        let fails = vec![requires(atom("SET.in", vec![int(1)], False))];
        assert_eq!(one(fails, Refuted), Some(Distance::normalized(1u32.into())));
    }
}
