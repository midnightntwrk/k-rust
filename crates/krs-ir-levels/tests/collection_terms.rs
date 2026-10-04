//! Collection terms keep their JSON shape and reject a wrong operand count when decoding.

use krs_ir::{NonEmpty, testing};
use krs_ir_levels::{
    DefinitionSortRef, DefinitionTerm, ListOperands, MapEntry, MapOperands, SetOperands,
};
use serde_json::{Value, json};

fn int(key: &str, value: &str) -> DefinitionTerm {
    DefinitionTerm::token(testing::origin(key), DefinitionSortRef::int(), value).unwrap()
}

fn argument_tokens(json: &Value) -> Vec<&str> {
    json["arguments"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|argument| argument["value"].as_str())
        .collect()
}

#[test]
fn collection_operands_serialize_in_wire_order_and_round_trip() {
    let items = DefinitionTerm::map(
        testing::origin("items"),
        MapOperands::Items(NonEmpty::new(
            MapEntry {
                key: int("items.first.key", "1"),
                value: int("items.first.value", "2"),
            },
            vec![MapEntry {
                key: int("items.second.key", "3"),
                value: int("items.second.value", "4"),
            }],
        )),
    );
    let range = DefinitionTerm::list(
        testing::origin("range"),
        DefinitionSortRef::list(),
        ListOperands::Range {
            list: DefinitionTerm::list(
                testing::origin("range.list"),
                DefinitionSortRef::list(),
                ListOperands::Empty,
            ),
            from_front: int("range.front", "5"),
            from_back: int("range.back", "6"),
        },
    );
    let contains = DefinitionTerm::set(
        testing::origin("contains"),
        DefinitionSortRef::bool(),
        SetOperands::Contains {
            element: int("contains.element", "7"),
            set: DefinitionTerm::set(
                testing::origin("contains.set"),
                DefinitionSortRef::set(),
                SetOperands::Empty,
            ),
        },
    );
    for (term, kind, operation, tokens) in [
        (items, "map", "item", vec!["1", "2", "3", "4"]),
        (range, "list", "range", vec!["5", "6"]),
        (contains, "set", "contains", vec!["7"]),
    ] {
        let json = serde_json::to_value(&term).unwrap();
        assert_eq!(json["term_kind"], kind);
        assert_eq!(json["operation"], operation);
        assert_eq!(argument_tokens(&json), tokens);
        let decoded: DefinitionTerm = serde_json::from_value(json.clone()).unwrap();
        assert_eq!(decoded, term);
        assert_eq!(serde_json::to_value(&decoded).unwrap(), json);
    }
}

#[test]
fn wrong_collection_arity_is_rejected_when_decoding() {
    let extra = serde_json::to_value(int("extra", "1")).unwrap();
    let mut empty = serde_json::to_value(DefinitionTerm::map(
        testing::origin("empty"),
        MapOperands::Empty,
    ))
    .unwrap();
    empty["arguments"] = json!([extra]);
    let error = serde_json::from_value::<DefinitionTerm>(empty)
        .unwrap_err()
        .to_string();
    assert!(
        error.contains("the empty Map operation has invalid arity 1"),
        "{error}"
    );

    let mut odd_items = serde_json::to_value(DefinitionTerm::map(
        testing::origin("odd"),
        MapOperands::entry(int("odd.key", "1"), int("odd.value", "2")),
    ))
    .unwrap();
    odd_items["arguments"]
        .as_array_mut()
        .unwrap()
        .push(extra.clone());
    assert!(serde_json::from_value::<DefinitionTerm>(odd_items).is_err());

    let mut short_get = serde_json::to_value(DefinitionTerm::list(
        testing::origin("get"),
        DefinitionSortRef::int(),
        ListOperands::Get {
            list: DefinitionTerm::list(
                testing::origin("get.list"),
                DefinitionSortRef::list(),
                ListOperands::Empty,
            ),
            index: int("get.index", "0"),
        },
    ))
    .unwrap();
    short_get["arguments"].as_array_mut().unwrap().pop();
    let error = serde_json::from_value::<DefinitionTerm>(short_get)
        .unwrap_err()
        .to_string();
    assert!(
        error.contains("the List lookup operation has invalid arity 1"),
        "{error}"
    );
}
