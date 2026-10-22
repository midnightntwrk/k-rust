//! The one place that reads the backend's condition records (`collectConditions`, G-7) into
//! the algebra's [`Cond`]. A change of the record shape is absorbed here.
//!
//! A record gives no distance when it is marked `chosen` (its terms may be one model's of a
//! value the definition leaves open), and an atom gives none when its truth is not decided or
//! one of its operands is not a ground value (`symbolic`, `undefined`, `omitted`, or variable-free
//! but holding an unevaluated application): no signal, never a distance of 0
//! (`super::distance`).

use k_rust::backend::{
    ConditionAtomOutput, ConditionNodeOutput, ConditionRecordOutput, RecordedValueOutput,
    RuleConditionsOutput,
};
use num_bigint::BigInt;
use serde_json::Value as Json;

use super::{
    GuardEntry, Guards,
    distance::{Comparison, Cond, Distance, Operand, Truth, distance},
};

/// Each record of each rule in `conditions`, by rule id, in the records' order: its guard
/// distance (`None` when it gives none) and the ground `Int` and `String` values it binds.
pub(crate) fn guards(conditions: &[RuleConditionsOutput]) -> Guards {
    conditions
        .iter()
        .map(|rule| {
            let entries = rule
                .records
                .iter()
                .map(|record| GuardEntry {
                    distance: record_distance(record),
                    reads: record
                        .bindings
                        .iter()
                        .filter_map(|binding| match &binding.value {
                            RecordedValueOutput::Value { term } => operand(term),
                            _ => None,
                        })
                        .collect(),
                })
                .collect();
            (rule.rule.clone(), entries)
        })
        .collect()
}

/// The guard distance of one record: the distance of the conjunction of its conjuncts.
fn record_distance(record: &ConditionRecordOutput) -> Option<Distance> {
    if record.chosen {
        return None;
    }
    distance(&Cond::And(record.condition.iter().map(node).collect()))
}

fn node(node: &ConditionNodeOutput) -> Cond {
    match node {
        ConditionNodeOutput::And(children) => Cond::And(children.iter().map(self::node).collect()),
        ConditionNodeOutput::Or(children) => Cond::Or(children.iter().map(self::node).collect()),
        ConditionNodeOutput::Not(child) => Cond::Not(Box::new(self::node(child))),
        ConditionNodeOutput::Implies(antecedent, consequent) => Cond::Implies(
            Box::new(self::node(antecedent)),
            Box::new(self::node(consequent)),
        ),
        ConditionNodeOutput::Atom(atom) => self::atom(atom),
    }
}

fn atom(atom: &ConditionAtomOutput) -> Cond {
    let ground: Option<Vec<&Json>> = atom
        .operands
        .iter()
        .map(|operand| match operand {
            RecordedValueOutput::Value { term } => Some(term),
            _ => None,
        })
        .collect();
    let Some(ground) = ground else {
        return Cond::Atom(Truth::Unknown);
    };
    if let Some((comparison, family)) = comparison(atom.head.as_deref(), atom.hook.as_deref())
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
    Cond::Atom(match atom.value {
        Some(true) => Truth::True,
        Some(false) => Truth::False,
        None => Truth::Unknown,
    })
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

    fn atom(
        hook: &str,
        operands: Vec<RecordedValueOutput>,
        value: Option<bool>,
    ) -> ConditionNodeOutput {
        ConditionNodeOutput::Atom(ConditionAtomOutput {
            head: Some("Lbl".into()),
            hook: Some(hook.into()),
            operands,
            reads: Vec::new(),
            value,
        })
    }

    fn record(condition: Vec<ConditionNodeOutput>, chosen: bool) -> RuleConditionsOutput {
        RuleConditionsOutput {
            rule: "r".into(),
            records: vec![ConditionRecordOutput {
                bindings: Vec::new(),
                condition,
                chosen,
            }],
            truncated: false,
        }
    }

    fn only(conditions: &RuleConditionsOutput) -> Option<Distance> {
        guards(std::slice::from_ref(conditions))["r"][0]
            .distance
            .clone()
    }

    #[test]
    fn integer_atoms_are_measured_by_their_operands() {
        let window = record(
            vec![
                atom("INT.gt", vec![int(-3), int(1000)], Some(false)),
                atom("INT.lt", vec![int(-3), int(1100)], Some(true)),
            ],
            false,
        );
        assert_eq!(only(&window), Some(Distance::normalized(1004u32.into())));
    }

    #[test]
    fn chosen_records_and_non_ground_operands_give_no_distance() {
        let chosen = record(
            vec![atom("INT.eq", vec![int(1), int(2)], Some(false))],
            true,
        );
        assert_eq!(only(&chosen), None);
        for operand in [
            RecordedValueOutput::Symbolic { term: json!({}) },
            RecordedValueOutput::Ground { term: json!({}) },
            RecordedValueOutput::Undefined,
            RecordedValueOutput::Omitted,
        ] {
            // The truth a record gives such an atom is not used: no signal, never 0.
            let record = record(
                vec![atom("INT.eq", vec![int(1), operand], Some(true))],
                false,
            );
            assert_eq!(only(&record), None);
        }
        let undecided = record(vec![atom("SET.in", vec![int(1)], None)], false);
        assert_eq!(only(&undecided), None);
    }

    #[test]
    fn the_ground_integer_and_string_bindings_are_read() {
        use k_rust::backend::RecordedBindingOutput;
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
        let mut conditions = record(
            vec![atom("INT.eq", vec![int(1), int(2)], Some(false))],
            false,
        );
        conditions.records[0].bindings = vec![
            binding("A", int(5)),
            binding("B", RecordedValueOutput::Symbolic { term: json!({}) }),
            binding("S", string),
            binding("U", RecordedValueOutput::Undefined),
        ];
        let entry = &guards(std::slice::from_ref(&conditions))["r"][0];
        assert_eq!(
            entry.reads,
            vec![Operand::Int(5.into()), Operand::Str("open".into())]
        );
    }

    #[test]
    fn other_atoms_count_by_their_truth() {
        let holds = record(vec![atom("SET.in", vec![int(1)], Some(true))], false);
        assert_eq!(only(&holds), Some(Distance::zero()));
        let fails = record(vec![atom("SET.in", vec![int(1)], Some(false))], false);
        assert_eq!(only(&fails), Some(Distance::normalized(1u32.into())));
    }
}
