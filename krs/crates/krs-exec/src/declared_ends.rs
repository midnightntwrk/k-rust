//! The ends a definition declares (`#[k::end(finished)]`, `#[k::end(refused)]`), and the class
//! of a state no rule applies to.
//!
//! A declared end is a set of states at which the definition says the run is over, in one of two
//! classes.
//! The definition holds it as a total `Bool` function of the whole configuration, true exactly on
//! the end, and a `refused` end also as a partial function of the configuration that gives the
//! reason where the end holds.
//! [`DeclaredEnds::of`] reads both from the Definition IR, as [`crate::console::ConsoleCells`]
//! reads the console cells: the function productions marked as an end's, paired by their module
//! and item.
//!
//! # The class of an end
//!
//! A run evaluates the declared ends only at a state no rule applies to ([`crate::Halt::Stuck`]).
//! A state a step bound or a stop ended the run at is not known to be one, since the definition
//! may go on from it, so it has no class; and a declaration promises only that its function is
//! true where no rule applies, so its value elsewhere says nothing of the run.
//!
//! At such a state every declared end's function is applied to the state and simplified:
//!
//! - where none is true the state is a *gap* ([`DeclaredClass::None`]): no rule applies and the
//!   definition does not call the state an end;
//! - where the true ones are of one class, the state is of that class, at the first of them in
//!   the order of declaring package, module and item name, the order of `ends.json`;
//! - where ends of both classes are true the definition contradicts itself
//!   ([`crate::ExecError::EndClassesOverlap`]): an end is finished or refused, never both;
//! - where one's value is not decided (the evaluation spent the run's budget of polls, another
//!   stop of the backend ended it, or it ended short of `true` or `false`) the class is not
//!   known ([`crate::Halt::EndUndecided`]), whatever the others answer: an end left undecided
//!   may be of the other class, or the first in order.
//!
//! The functions are applied to the configuration alone.
//! A state that carries a constraint denotes the configurations that satisfy it, and a function
//! that simplifies to `true` or `false` on the configuration has that value at each of them, so
//! the answer holds under the constraint; an evaluation that would need the constraint to reach a
//! value ends short of one and leaves the class undecided.

use k_rust::kore::ast::{Pattern, Sort, Symbol};
use krs_ir::{EndClass, EndRole, ProductionAttribute};
use krs_ir_levels::{DefinitionIr, DefinitionSentence};
use serde::Serialize;
use serde_json::Value as Json;

use crate::inputs::{InputType, input_type};
use crate::values::{Value, ValueIndex, kore_symbol_name, strip_injections};

/// The declared class of a state no rule applies to
/// ([module documentation](crate::declared_ends#the-class-of-an-end)).
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum DeclaredClass {
    /// A declared `finished` end holds: the computation completed.
    Finished,
    /// A declared `refused` end holds: the definition refuses to continue, for a stated reason.
    Refused,
    /// No declared end holds: the definition has no rule for the state and does not call it an
    /// end.
    None,
}

impl DeclaredClass {
    /// The word a report and an end document write.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Finished => "finished",
            Self::Refused => "refused",
            Self::None => "none",
        }
    }

    pub(crate) const fn of(class: EndClass) -> Self {
        match class {
            EndClass::Finished => Self::Finished,
            EndClass::Refused => Self::Refused,
        }
    }

    /// The class `word` names.
    pub(crate) fn named(word: &str) -> Option<Self> {
        [Self::Finished, Self::Refused, Self::None]
            .into_iter()
            .find(|class| class.as_str() == word)
    }
}

/// The reason of a `refused` end: the value its reason function gives at the end's state.
///
/// Two reasons are equal when their values are.
#[derive(Clone, Debug, Serialize)]
pub struct EndReason {
    /// The value.
    #[serde(skip)]
    pub value: Value,
    /// The value's canonical document at the reason function's declared result type; `None`
    /// (omitted) for a value with a part that has no document there.
    #[serde(rename = "reason", skip_serializing_if = "Option::is_none")]
    pub document: Option<Json>,
    /// The value as K text, or as KORE where the printer warns.
    #[serde(rename = "reason_text")]
    pub text: String,
}

impl PartialEq for EndReason {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl Eq for EndReason {}

/// The declared class of a run's end ([`crate::RunReport::end`]).
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct RunEnd {
    /// The class.
    pub class: DeclaredClass,
    /// The declared end that holds, by its item as `ends.json` names it (`crate::machine::halt`
    /// for an item of the definition's main package, `core::trap` for a dependency's): the first
    /// in the order of declaring package, module and item name. `None` (omitted) for a gap.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub item: Option<String>,
    /// A `refused` end's reason; `None` (omitted) for the other classes.
    #[serde(flatten)]
    pub reason: Option<EndReason>,
}

/// Where and why a run's class was left undecided ([`crate::Halt::EndUndecided`]).
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct EndUndecided {
    /// The declared end whose function, or whose reason function, was not decided, by its item.
    pub item: String,
    /// Why.
    pub reason: String,
    /// Whether the evaluation spent its budget of polls, which a larger budget can decide.
    pub budget_spent: bool,
}

/// One declared end, as a run evaluates it.
#[derive(Clone, Debug)]
pub(crate) struct Declared {
    pub(crate) class: EndClass,
    /// The item, as `ends.json` names it.
    pub(crate) item: String,
    /// The KORE symbol of the total `Bool` function that is true exactly on the end.
    pub(crate) holds: String,
    /// A refused end's reason function: its KORE symbol, and its declared result type where KRS
    /// names the sort.
    pub(crate) reason: Option<(String, Option<InputType>)>,
}

/// The ends a definition declares, in the order of declaring package, module and item name.
#[derive(Clone, Debug, Default)]
pub(crate) struct DeclaredEnds(Vec<Declared>);

impl DeclaredEnds {
    pub(crate) fn of(definition: &DefinitionIr, values: &ValueIndex) -> Self {
        type Key = (String, Vec<String>, String);
        let mut holds = std::collections::BTreeMap::<Key, (EndClass, String, String)>::new();
        let mut reasons = std::collections::BTreeMap::<Key, (String, Option<InputType>)>::new();
        for sentence in definition
            .modules()
            .iter()
            .flat_map(krs_ir_levels::DefinitionModule::sentences)
        {
            let DefinitionSentence::Production(production) = sentence else {
                continue;
            };
            let Some((class, role, name)) =
                production
                    .attributes()
                    .iter()
                    .find_map(|attribute| match attribute {
                        ProductionAttribute::End {
                            class, role, item, ..
                        } => Some((*class, *role, item)),
                        _ => None,
                    })
            else {
                continue;
            };
            let Some(item) = sentence.item() else {
                continue;
            };
            let key = (
                item.package().cargo_name().to_owned(),
                item.module_path().to_vec(),
                name.clone(),
            );
            let symbol = kore_symbol_name(production.symbol().emitted_name());
            match role {
                EndRole::Holds => {
                    let root = if item.package().k_namespace() == definition.main_module().as_str()
                    {
                        "crate".to_owned()
                    } else {
                        definition.crate_name(item.package())
                    };
                    let path = std::iter::once(root)
                        .chain(item.module_path().iter().cloned())
                        .chain([name.clone()])
                        .collect::<Vec<_>>()
                        .join("::");
                    holds.insert(key, (class, path, symbol));
                }
                EndRole::Reason => {
                    let ty = input_type(
                        values,
                        production.result_sort(),
                        production.result_arguments(),
                    );
                    reasons.insert(key, (symbol, ty));
                }
            }
        }
        Self(
            holds
                .into_iter()
                .map(|(key, (class, item, holds))| Declared {
                    class,
                    item,
                    holds,
                    reason: reasons.remove(&key),
                })
                .collect(),
        )
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &Declared> {
        self.0.iter()
    }

    /// The declared end whose item is `item`.
    pub(crate) fn get(&self, item: &str) -> Option<&Declared> {
        self.0.iter().find(|declared| declared.item == item)
    }

    /// The items, each quoted, for a refusal that lists them.
    pub(crate) fn listed(&self) -> String {
        self.0
            .iter()
            .map(|declared| format!("`{}`", declared.item))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

/// Whether `definition` declares an end: whether [`crate::Semantics::declares_ends`] holds of
/// it once loaded, read from the Definition IR alone, for a caller that decides the format of
/// what it writes before it loads the definition.
#[must_use]
pub fn declares_ends(definition: &DefinitionIr) -> bool {
    definition
        .modules()
        .iter()
        .flat_map(krs_ir_levels::DefinitionModule::sentences)
        .any(|sentence| {
            let DefinitionSentence::Production(production) = sentence else {
                return false;
            };
            sentence.item().is_some()
                && production.attributes().iter().any(|attribute| {
                    matches!(
                        attribute,
                        ProductionAttribute::End {
                            role: EndRole::Holds,
                            ..
                        }
                    )
                })
        })
}

/// The KORE symbols of the functions of `definition`'s declared ends: each end's function of
/// the configuration, and a refused end's reason function, in the definition's order of
/// sentences. A tool that reads a run's states without applying these functions (kink's
/// coverage) tells by them which equations only a declared end applies.
#[must_use]
pub fn end_functions(definition: &DefinitionIr) -> Vec<String> {
    definition
        .modules()
        .iter()
        .flat_map(krs_ir_levels::DefinitionModule::sentences)
        .filter_map(|sentence| {
            let DefinitionSentence::Production(production) = sentence else {
                return None;
            };
            (sentence.item().is_some()
                && production
                    .attributes()
                    .iter()
                    .any(|attribute| matches!(attribute, ProductionAttribute::End { .. })))
            .then(|| kore_symbol_name(production.symbol().emitted_name()))
        })
        .collect()
}

/// `symbol` applied to the configuration of `state`, a state's pattern: the pattern itself, or
/// its one configuration conjunct where it carries constraints; `None` for any other pattern.
pub(crate) fn application(symbol: &str, state: &Pattern) -> Option<Pattern> {
    let configuration = match state {
        Pattern::And { arguments, .. } => arguments.iter().find(|argument| {
            matches!(argument, Pattern::Application { symbol, .. } if symbol.name.starts_with("Lbl'-LT-'"))
        })?,
        Pattern::Application { .. } => state,
        _ => return None,
    };
    Some(Pattern::Application {
        symbol: Symbol {
            name: symbol.to_owned(),
            sort_parameters: Vec::new(),
        },
        arguments: vec![configuration.clone()],
    })
}

/// The Bool `pattern` is, where it is a Bool literal.
pub(crate) fn bool_value(pattern: &Pattern) -> Option<bool> {
    match strip_injections(pattern) {
        Pattern::DomainValue {
            sort: Sort::Application { name, arguments },
            value,
        } if name == "SortBool" && arguments.is_empty() => match value.as_bytes() {
            b"true" => Some(true),
            b"false" => Some(false),
            _ => None,
        },
        _ => None,
    }
}

/// Whether `pattern` is an application of `symbol`: a function's application that no equation
/// rewrote.
pub(crate) fn applies(pattern: &Pattern, symbol: &str) -> bool {
    matches!(
        strip_injections(pattern),
        Pattern::Application { symbol: head, .. } if head.name == symbol
    )
}

#[cfg(test)]
mod tests {
    use k_rust::kore::ast::{Pattern, Sort, Symbol};

    use super::{application, applies, bool_value};

    fn sort(name: &str) -> Sort {
        Sort::Application {
            name: name.to_owned(),
            arguments: Vec::new(),
        }
    }

    fn apply(name: &str, arguments: Vec<Pattern>) -> Pattern {
        Pattern::Application {
            symbol: Symbol {
                name: name.to_owned(),
                sort_parameters: Vec::new(),
            },
            arguments,
        }
    }

    fn truth(value: &str) -> Pattern {
        Pattern::DomainValue {
            sort: sort("SortBool"),
            value: value.into(),
        }
    }

    /// Only a Bool literal decides whether an end holds: an application left unevaluated, or a
    /// literal of another sort, decides nothing.
    #[test]
    fn only_a_bool_literal_is_a_decided_answer() {
        assert_eq!(bool_value(&truth("true")), Some(true));
        assert_eq!(bool_value(&truth("false")), Some(false));
        let unevaluated = apply(
            "LblendHalt",
            vec![apply("Lbl'-LT-'generatedTop'-GT-'", vec![])],
        );
        assert_eq!(bool_value(&unevaluated), None);
        assert!(applies(&unevaluated, "LblendHalt"));
        assert!(!applies(&truth("true"), "LblendHalt"));
        let number = Pattern::DomainValue {
            sort: sort("SortInt"),
            value: "true".into(),
        };
        assert_eq!(bool_value(&number), None);
    }

    /// An end's function is applied to the configuration: the whole pattern of a state without
    /// constraints, and the configuration conjunct of one with them.
    #[test]
    fn a_function_is_applied_to_the_configuration() {
        let configuration = apply("Lbl'-LT-'generatedTop'-GT-'", vec![]);
        let expected = apply("LblendHalt", vec![configuration.clone()]);
        assert_eq!(
            application("LblendHalt", &configuration),
            Some(expected.clone())
        );
        let constrained = Pattern::And {
            sort: sort("SortGeneratedTopCell"),
            arguments: vec![
                configuration,
                Pattern::Top {
                    sort: sort("SortGeneratedTopCell"),
                },
            ],
        };
        assert_eq!(application("LblendHalt", &constrained), Some(expected));
        let bottom = Pattern::Bottom {
            sort: sort("SortGeneratedTopCell"),
        };
        assert_eq!(application("LblendHalt", &bottom), None);
    }
}
