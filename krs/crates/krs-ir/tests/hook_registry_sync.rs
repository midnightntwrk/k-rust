//! The hook registry must equal k-rust's `hook-capabilities.toml` at the pin.

use std::collections::BTreeMap;
use std::path::Path;

use krs_ir::hook_registry::{
    HOOK_REGISTRY, NativeHookCapability, catalogued_hook, registered_hook,
};

fn names(item: &toml_edit::Item) -> Vec<String> {
    item.as_array()
        .expect("a hook list is an array")
        .iter()
        .map(|value| value.as_str().expect("a hook name is a string").to_owned())
        .collect()
}

fn grouped(item: Option<&toml_edit::Item>) -> Vec<String> {
    item.and_then(toml_edit::Item::as_array_of_tables)
        .map(|tables| {
            tables
                .iter()
                .flat_map(|table| names(table.get("hooks").expect("a hook group lists hooks")))
                .collect()
        })
        .unwrap_or_default()
}

#[test]
fn registry_matches_k_rust_hook_capabilities() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../crates/k-rust/tests/fixtures/hook-capabilities.toml");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    let document: toml_edit::Document<String> =
        toml_edit::Document::parse(text).expect("hook-capabilities.toml parses");
    let root = document.as_table();
    assert_eq!(
        root.get("version").and_then(toml_edit::Item::as_integer),
        Some(2),
        "the registry mirrors manifest version 2"
    );
    let crypto = root
        .get("crypto")
        .and_then(toml_edit::Item::as_table)
        .expect("the pin classifies crypto hooks");
    let arities = crypto
        .get("arities")
        .and_then(toml_edit::Item::as_table)
        .expect("the pin lists crypto arities");
    let mut expected = BTreeMap::new();
    let mut add = |name: String, capability, arity: Option<u8>| {
        assert!(
            expected.insert(name.clone(), (capability, arity)).is_none(),
            "{name} is classified twice"
        );
    };
    for name in names(&root["implemented"]) {
        add(name, NativeHookCapability::Implemented, None);
    }
    for name in names(&root["execution_only"]) {
        add(name, NativeHookCapability::ExecutionOnly, None);
    }
    for name in grouped(root.get("equation_defined")) {
        add(name, NativeHookCapability::EquationDefined, None);
    }
    for name in grouped(root.get("unsupported")) {
        add(name, NativeHookCapability::Unsupported, None);
    }
    let arity = |name: &str| {
        let value = arities
            .get(name)
            .and_then(toml_edit::Item::as_integer)
            .unwrap_or_else(|| panic!("{name} has a crypto arity"));
        Some(u8::try_from(value).expect("crypto arities are small"))
    };
    for name in names(&crypto["implemented"]) {
        let arity = arity(&name);
        add(name, NativeHookCapability::Implemented, arity);
    }
    for name in grouped(crypto.get("unsupported")) {
        let arity = arity(&name);
        add(name, NativeHookCapability::Unsupported, arity);
    }
    let actual = HOOK_REGISTRY
        .iter()
        .map(|hook| (hook.name.to_owned(), (hook.capability, hook.crypto_arity)))
        .collect::<BTreeMap<_, _>>();
    assert_eq!(
        actual.len(),
        HOOK_REGISTRY.len(),
        "the registry names each hook once"
    );
    assert_eq!(
        actual, expected,
        "crates/krs-ir/src/hook_registry.rs differs from the pinned hook-capabilities.toml"
    );
    assert!(
        HOOK_REGISTRY
            .windows(2)
            .all(|pair| pair[0].name < pair[1].name),
        "the registry is sorted by name for binary search"
    );
}

#[test]
fn every_catalogued_hook_is_registered() {
    for operation in krs_ir::HookOperation::ALL {
        let name = operation.spec().k_hook;
        assert!(
            registered_hook(name).is_some(),
            "{name} is not in the registry"
        );
        assert_eq!(catalogued_hook(name), Some(operation));
    }
}

#[test]
fn lookups_find_registered_names_only() {
    let keccak = registered_hook("KRYPTO.keccak256").expect("KRYPTO.keccak256 is pinned");
    assert_eq!(keccak.capability, NativeHookCapability::Implemented);
    assert_eq!(keccak.crypto_arity, Some(1));
    assert_eq!(keccak.namespace(), "KRYPTO");
    assert_eq!(catalogued_hook("KRYPTO.keccak256"), None);
    assert_eq!(
        registered_hook("IO.write").map(|hook| hook.capability),
        Some(NativeHookCapability::ExecutionOnly)
    );
    assert!(registered_hook("KRYPTO.keccak").is_none());
    assert!(
        registered_hook("INT.Int").is_none(),
        "sort hooks are not function hooks"
    );
}
