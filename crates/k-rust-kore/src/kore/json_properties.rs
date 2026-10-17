//! Generated patterns against an independent reference encoding of the KORE JSON format.
//!
//! The reference below is written field by field from the format's own declaration
//! (`KorePattern` and `KoreSort` in `crates/k-rust-wasm/typescript/index.ts`): one object per
//! pattern or sort, a `tag` naming its constructor, and named fields for its sorts, scalars and
//! sub-patterns. A string or domain value carries the KORE bytes of its literal, one JSON code
//! point per byte. The reference shares no code with `pattern_fields`, so a wrong tag, field
//! name or byte mapping in either encoder makes the two disagree.
//!
//! The domain is every pattern the KORE JSON format can carry: quantifiers bind element
//! variables, fixpoints bind set variables, and an associative application has at least one
//! argument. The crate's generator stays inside it.

use std::{borrow::Cow, cell::RefCell, collections::BTreeMap};

use proptest::{
    prelude::*,
    test_runner::{Config, RngAlgorithm, TestRng, TestRunner},
};
use serde_json::{Value, json};

use super::{
    from_str, source_to_string, to_node_source, to_string, to_string_pretty, to_value,
    to_value_source,
};
use crate::json_tree;
use crate::kore::{
    ast::{Associativity, KoreString, Pattern, Sort, Symbol, Variable, VariableKind},
    node::{PatternNode, PatternSource},
    printer::tests::streaming::pattern,
    string::LiteralEncoding,
};

fn reference_sort(sort: &Sort) -> Value {
    match sort {
        Sort::Variable(name) => json!({ "tag": "SortVar", "name": name }),
        Sort::Application { name, arguments } => json!({
            "tag": "SortApp",
            "name": name,
            "args": reference_sorts(arguments),
        }),
    }
}

fn reference_sorts(sorts: &[Sort]) -> Value {
    Value::Array(sorts.iter().map(reference_sort).collect())
}

fn reference_patterns(patterns: &[Pattern]) -> Value {
    Value::Array(patterns.iter().map(reference_term).collect())
}

/// The JSON string of a payload's code points: one per byte of a `Bytes` payload, the UTF-8 of
/// any other (`string::LiteralEncoding`).
fn reference_code_points(value: &KoreString, encoding: LiteralEncoding) -> String {
    match encoding {
        LiteralEncoding::Bytes => value
            .as_bytes()
            .iter()
            .map(|&byte| char::from(byte))
            .collect(),
        LiteralEncoding::Utf8 => value.as_utf8().unwrap().to_owned(),
    }
}

/// The term object of `pattern`, recursing once per level of the generator's bounded depth.
fn reference_term(pattern: &Pattern) -> Value {
    let unary = |tag: &str, sort: &Sort, field: &str, argument: &Pattern| {
        json!({
            "tag": tag,
            "sort": reference_sort(sort),
            field: reference_term(argument),
        })
    };
    let binary = |tag: &str, sort: &Sort, names: [&str; 2], left: &Pattern, right: &Pattern| {
        json!({
            "tag": tag,
            "sort": reference_sort(sort),
            names[0]: reference_term(left),
            names[1]: reference_term(right),
        })
    };
    let binder = |tag: &str, sort: Option<&Sort>, variable: &Variable, body: &Pattern| {
        let mut object = json!({
            "tag": tag,
            "var": variable.name,
            "varSort": reference_sort(&variable.sort),
            "arg": reference_term(body),
        });
        if let Some(sort) = sort {
            object["sort"] = reference_sort(sort);
        }
        object
    };
    let predicate = |tag: &str, operand: &Sort, result: &Sort| {
        json!({
            "tag": tag,
            "argSort": reference_sort(operand),
            "sort": reference_sort(result),
        })
    };
    match pattern {
        Pattern::String(value) => json!({
            "tag": "String",
            "value": reference_code_points(value, LiteralEncoding::Utf8),
        }),
        Pattern::Variable(variable) => json!({
            "tag": match variable.kind {
                VariableKind::Element => "EVar",
                VariableKind::Set => "SVar",
            },
            "name": variable.name,
            "sort": reference_sort(&variable.sort),
        }),
        Pattern::Application { symbol, arguments } => json!({
            "tag": "App",
            "name": symbol.name,
            "sorts": reference_sorts(&symbol.sort_parameters),
            "args": reference_patterns(arguments),
        }),
        Pattern::Top { sort } => json!({ "tag": "Top", "sort": reference_sort(sort) }),
        Pattern::Bottom { sort } => json!({ "tag": "Bottom", "sort": reference_sort(sort) }),
        Pattern::And { sort, arguments } => json!({
            "tag": "And",
            "sort": reference_sort(sort),
            "patterns": reference_patterns(arguments),
        }),
        Pattern::Or { sort, arguments } => json!({
            "tag": "Or",
            "sort": reference_sort(sort),
            "patterns": reference_patterns(arguments),
        }),
        Pattern::Not { sort, argument } => unary("Not", sort, "arg", argument),
        Pattern::Next { sort, argument } => unary("Next", sort, "dest", argument),
        Pattern::Implies { sort, left, right } => {
            binary("Implies", sort, ["first", "second"], left, right)
        }
        Pattern::Iff { sort, left, right } => binary("Iff", sort, ["first", "second"], left, right),
        Pattern::Rewrites { sort, left, right } => {
            binary("Rewrites", sort, ["source", "dest"], left, right)
        }
        Pattern::Exists {
            sort,
            variable,
            body,
        } => binder("Exists", Some(sort), variable, body),
        Pattern::Forall {
            sort,
            variable,
            body,
        } => binder("Forall", Some(sort), variable, body),
        Pattern::Mu { variable, body } => binder("Mu", None, variable, body),
        Pattern::Nu { variable, body } => binder("Nu", None, variable, body),
        Pattern::Ceil {
            operand_sort,
            result_sort,
            argument,
        }
        | Pattern::Floor {
            operand_sort,
            result_sort,
            argument,
        } => {
            let tag = if matches!(pattern, Pattern::Ceil { .. }) {
                "Ceil"
            } else {
                "Floor"
            };
            let mut object = predicate(tag, operand_sort, result_sort);
            object["arg"] = reference_term(argument);
            object
        }
        Pattern::Equals {
            operand_sort,
            result_sort,
            left,
            right,
        }
        | Pattern::In {
            operand_sort,
            result_sort,
            left,
            right,
        } => {
            let tag = if matches!(pattern, Pattern::Equals { .. }) {
                "Equals"
            } else {
                "In"
            };
            let mut object = predicate(tag, operand_sort, result_sort);
            object["first"] = reference_term(left);
            object["second"] = reference_term(right);
            object
        }
        Pattern::DomainValue { sort, value } => json!({
            "tag": "DV",
            "sort": reference_sort(sort),
            "value": reference_code_points(value, LiteralEncoding::of_domain_value(sort)),
        }),
        Pattern::AssociativeApplication {
            associativity,
            symbol,
            arguments,
        } => json!({
            "tag": match associativity {
                Associativity::Left => "LeftAssoc",
                Associativity::Right => "RightAssoc",
            },
            "symbol": symbol.name,
            "sorts": reference_sorts(&symbol.sort_parameters),
            "argss": reference_patterns(arguments),
        }),
    }
}

fn reference_document(pattern: &Pattern) -> Value {
    json!({ "format": "KORE", "version": 1, "term": reference_term(pattern) })
}

/// The format also admits a two-argument `And` or `Or` written with `first` and `second`
/// instead of `patterns`; it denotes the same pattern. Returns how many it rewrote.
fn with_binary_connectives(value: &mut Value) -> usize {
    match value {
        Value::Object(object) => {
            let binary = matches!(object.get("tag"), Some(Value::String(tag)) if tag == "And" || tag == "Or")
                && matches!(object.get("patterns"), Some(Value::Array(patterns)) if patterns.len() == 2);
            if binary {
                let Some(Value::Array(mut patterns)) = object.remove("patterns") else {
                    unreachable!("checked above")
                };
                let second = patterns.pop().expect("two patterns");
                let first = patterns.pop().expect("two patterns");
                object.insert("first".into(), first);
                object.insert("second".into(), second);
            }
            usize::from(binary)
                + object
                    .values_mut()
                    .map(with_binary_connectives)
                    .sum::<usize>()
        }
        Value::Array(values) => values.iter_mut().map(with_binary_connectives).sum(),
        _ => 0,
    }
}

/// A source whose nodes own their scalars, as a source that builds nodes on demand does,
/// so the encoders take their `Cow::Owned` paths.
#[derive(Clone, Copy)]
struct Owned<'p>(&'p Pattern);

impl<'a, 'p> PatternSource<'a> for Owned<'p> {
    fn node(self) -> PatternNode<'a, Self> {
        use PatternNode as N;
        let sort = |sort: &Sort| Cow::Owned(sort.clone());
        let list = |patterns: &'p [Pattern]| patterns.iter().map(Owned).collect();
        let variable = |variable: &Variable| Cow::Owned(variable.clone());
        let symbol = |symbol: &Symbol| Cow::Owned(symbol.clone());
        match self.0 {
            Pattern::String(value) => N::String(Cow::Owned(value.clone())),
            Pattern::Variable(value) => N::Variable(variable(value)),
            Pattern::Application {
                symbol: head,
                arguments,
            } => N::Application {
                symbol: symbol(head),
                arguments: list(arguments),
            },
            Pattern::Top { sort: s } => N::Top { sort: sort(s) },
            Pattern::Bottom { sort: s } => N::Bottom { sort: sort(s) },
            Pattern::And { sort: s, arguments } => N::And {
                sort: sort(s),
                arguments: list(arguments),
            },
            Pattern::Or { sort: s, arguments } => N::Or {
                sort: sort(s),
                arguments: list(arguments),
            },
            Pattern::Not { sort: s, argument } => N::Not {
                sort: sort(s),
                argument: Owned(argument),
            },
            Pattern::Next { sort: s, argument } => N::Next {
                sort: sort(s),
                argument: Owned(argument),
            },
            Pattern::Implies {
                sort: s,
                left,
                right,
            } => N::Implies {
                sort: sort(s),
                left: Owned(left),
                right: Owned(right),
            },
            Pattern::Iff {
                sort: s,
                left,
                right,
            } => N::Iff {
                sort: sort(s),
                left: Owned(left),
                right: Owned(right),
            },
            Pattern::Rewrites {
                sort: s,
                left,
                right,
            } => N::Rewrites {
                sort: sort(s),
                left: Owned(left),
                right: Owned(right),
            },
            Pattern::Exists {
                sort: s,
                variable: bound,
                body,
            } => N::Exists {
                sort: sort(s),
                variable: variable(bound),
                body: Owned(body),
            },
            Pattern::Forall {
                sort: s,
                variable: bound,
                body,
            } => N::Forall {
                sort: sort(s),
                variable: variable(bound),
                body: Owned(body),
            },
            Pattern::Mu {
                variable: bound,
                body,
            } => N::Mu {
                variable: variable(bound),
                body: Owned(body),
            },
            Pattern::Nu {
                variable: bound,
                body,
            } => N::Nu {
                variable: variable(bound),
                body: Owned(body),
            },
            Pattern::Ceil {
                operand_sort,
                result_sort,
                argument,
            } => N::Ceil {
                operand_sort: sort(operand_sort),
                result_sort: sort(result_sort),
                argument: Owned(argument),
            },
            Pattern::Floor {
                operand_sort,
                result_sort,
                argument,
            } => N::Floor {
                operand_sort: sort(operand_sort),
                result_sort: sort(result_sort),
                argument: Owned(argument),
            },
            Pattern::Equals {
                operand_sort,
                result_sort,
                left,
                right,
            } => N::Equals {
                operand_sort: sort(operand_sort),
                result_sort: sort(result_sort),
                left: Owned(left),
                right: Owned(right),
            },
            Pattern::In {
                operand_sort,
                result_sort,
                left,
                right,
            } => N::In {
                operand_sort: sort(operand_sort),
                result_sort: sort(result_sort),
                left: Owned(left),
                right: Owned(right),
            },
            Pattern::DomainValue { sort: s, value } => N::DomainValue {
                sort: sort(s),
                value: Cow::Owned(value.clone()),
            },
            Pattern::AssociativeApplication {
                associativity,
                symbol: head,
                arguments,
            } => N::AssociativeApplication {
                associativity: *associativity,
                symbol: symbol(head),
                arguments: list(arguments),
            },
        }
    }
}

/// A generated pattern beside a string and a domain value of arbitrary code points, a `Bytes`
/// domain value holding arbitrary bytes, so every byte value and code point reaches the encoders
/// (the generator's own texts are ASCII), and a set variable outside a fixpoint binder, which the
/// generator does not build.
fn generated() -> impl Strategy<Value = Pattern> {
    (
        pattern(),
        prop::collection::vec(any::<char>(), 0..8),
        prop::collection::vec(any::<char>(), 0..8),
        prop::collection::vec(any::<u8>(), 0..8),
        "@[A-C][a-c0-9']{0,3}",
    )
        .prop_map(
            |(pattern, string, value, bytes, set)| Pattern::Application {
                symbol: Symbol {
                    name: "Root".into(),
                    sort_parameters: Vec::new(),
                },
                arguments: vec![
                    pattern,
                    Pattern::String(string.into_iter().collect::<String>().into()),
                    Pattern::DomainValue {
                        sort: Sort::Variable("S".into()),
                        value: value.into_iter().collect::<String>().into(),
                    },
                    Pattern::DomainValue {
                        sort: Sort::Application {
                            name: "SortBytes".into(),
                            arguments: Vec::new(),
                        },
                        value: bytes.into(),
                    },
                    Pattern::Variable(Variable {
                        kind: VariableKind::Set,
                        name: set,
                        sort: Sort::Variable("S".into()),
                    }),
                ],
            },
        )
}

/// The tags of every object in `value`, counted.
fn count_tags(value: &Value, tally: &mut BTreeMap<String, usize>) {
    match value {
        Value::Object(object) => {
            if let Some(Value::String(tag)) = object.get("tag") {
                *tally.entry(tag.clone()).or_default() += 1;
            }
            object.values().for_each(|child| count_tags(child, tally));
        }
        Value::Array(values) => values.iter().for_each(|child| count_tags(child, tally)),
        _ => {}
    }
}

fn check(pattern: &Pattern, tally: &RefCell<BTreeMap<String, usize>>) -> Result<(), TestCaseError> {
    let reference = reference_document(pattern);
    count_tags(&reference, &mut tally.borrow_mut());
    let compact = serde_json::to_string(&reference).unwrap();
    let parse = |text: &str| serde_json::from_str::<Value>(text).unwrap();

    // Both encoders, from a borrowing and from an owning source, write the reference.
    prop_assert_eq!(&to_value(pattern).unwrap(), &reference);
    prop_assert_eq!(&to_value_source(Owned(pattern)).unwrap(), &reference);
    prop_assert_eq!(&parse(&to_string(pattern).unwrap()), &reference);
    prop_assert_eq!(&parse(&to_string_pretty(pattern).unwrap()), &reference);
    // The streaming writer emits the compact text with sorted keys, byte for byte.
    prop_assert_eq!(&source_to_string(pattern), &compact);
    prop_assert_eq!(&source_to_string(Owned(pattern)), &compact);
    // The key-ordered tree writes the text of the reference value, compact and pretty.
    prop_assert_eq!(
        &json_tree::to_string(&to_node_source(pattern), false),
        &compact
    );
    prop_assert_eq!(
        &json_tree::to_string(&to_node_source(Owned(pattern)), true),
        &json_tree::to_string_pretty(&reference).unwrap()
    );

    // The decoder reads the reference and every encoder's text back to the pattern.
    prop_assert_eq!(&from_str(&compact).unwrap(), pattern);
    prop_assert_eq!(&from_str(&to_string(pattern).unwrap()).unwrap(), pattern);
    prop_assert_eq!(
        &from_str(&to_string_pretty(pattern).unwrap()).unwrap(),
        pattern
    );
    let mut binary = reference;
    *tally
        .borrow_mut()
        .entry("binary And or Or".into())
        .or_default() += with_binary_connectives(&mut binary);
    prop_assert_eq!(&from_str(&binary.to_string()).unwrap(), pattern);
    Ok(())
}

/// Every encoder agrees with the reference encoding and the decoder inverts it, over generated
/// patterns of every constructor.
#[test]
fn encoders_agree_with_the_format_and_the_decoder_inverts_them() {
    let config = Config {
        cases: 256,
        failure_persistence: None,
        ..Config::default()
    };
    let mut runner =
        TestRunner::new_with_rng(config, TestRng::deterministic_rng(RngAlgorithm::ChaCha));
    let tally = RefCell::new(BTreeMap::new());
    runner
        .run(&generated(), |pattern| check(&pattern, &tally))
        .unwrap();

    // Guard against a vacuous pass: each tag of the format, and the binary connective form, is
    // reached at least ten times.
    let tally = tally.into_inner();
    for tag in [
        "String",
        "EVar",
        "SVar",
        "App",
        "Top",
        "Bottom",
        "And",
        "Or",
        "Not",
        "Next",
        "Implies",
        "Iff",
        "Rewrites",
        "Exists",
        "Forall",
        "Mu",
        "Nu",
        "Ceil",
        "Floor",
        "Equals",
        "In",
        "DV",
        "LeftAssoc",
        "RightAssoc",
        "SortVar",
        "SortApp",
        "binary And or Or",
    ] {
        assert!(
            tally.get(tag).copied().unwrap_or(0) >= 10,
            "tag {tag} was reached only {:?} times: {tally:?}",
            tally.get(tag)
        );
    }
}
