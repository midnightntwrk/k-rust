use std::collections::BTreeSet;

use toml::Value;

const MANIFEST: &str = include_str!("../../../scripts/reference-differential.toml");

#[test]
fn differential_manifest_is_complete_and_unambiguous() {
    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    assert_eq!(manifest["version"].as_integer(), Some(1));

    let reference = manifest["reference"].as_table().expect("reference pins");
    for pin in [
        "k",
        "imp",
        "wasm",
        "evm-equivalence",
        "kevm",
        "kevm-plugin",
        "mir",
    ] {
        let revision = reference[pin]["revision"]
            .as_str()
            .expect("revision string");
        assert_eq!(revision.len(), 40, "{pin} must use a full Git revision");
        assert!(revision.bytes().all(|byte| byte.is_ascii_hexdigit()));
    }
    assert!(reference["k"]["version"].as_str().is_some());

    for section in ["compile", "kast", "execution", "proof", "rpc"] {
        let entries = manifest[section].as_array().expect("coverage array");
        assert!(!entries.is_empty(), "{section} coverage must not be empty");
        let mut names = BTreeSet::new();
        for entry in entries {
            let name = entry["name"].as_str().expect("coverage name");
            assert!(names.insert(name), "duplicate {section} case {name}");
        }
    }

    let compile = manifest["compile"].as_array().unwrap();
    let compiled_names = compile
        .iter()
        .map(|entry| entry["name"].as_str().unwrap())
        .collect::<BTreeSet<_>>();
    for semantics in ["imp", "wasm", "evm-equivalence", "mir"] {
        assert!(
            compiled_names.contains(semantics),
            "missing {semantics} compile differential"
        );
    }
    let evm = compile
        .iter()
        .find(|entry| entry["name"].as_str() == Some("evm-equivalence"))
        .unwrap();
    assert_eq!(
        evm["hook-namespaces"].as_array().unwrap(),
        &[Value::String("JSON".into()), Value::String("KRYPTO".into())],
        "production hook namespace flags must be pinned"
    );
    for entry in compile {
        assert!(
            !entry["comparisons"].as_array().unwrap().is_empty(),
            "every compile case must declare compared artifacts"
        );
    }
}
