//! kink's semantics identity (packet CACHE-ID): every versioned constant of every kink crate is
//! either a component of the identity or listed outside it with a reason, and the identity is
//! the object every store keys on.

use kink_campaign::identity::{
    KINK_IDENTITY, OUTSIDE_IDENTITY, identity_difference, kink_identity,
};
use serde_json::json;
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

/// A `const NAME: TYPE = VALUE;` item of one crate's sources: `(crate, NAME) -> (TYPE, VALUE)`,
/// with `VALUE` as written (a string literal keeps its quotes).
type Constants = BTreeMap<(String, String), (String, String)>;

fn rust_files(directory: &Path, files: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            rust_files(&path, files);
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            files.push(path);
        }
    }
}

/// Every `const` item of every `crates/*/src` file. An item may span lines (rustfmt breaks a
/// long one after `=`); a `const` of a block or an `impl` counts like a top-level one.
fn constants() -> Constants {
    let crates = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut constants = Constants::new();
    for entry in fs::read_dir(&crates).unwrap() {
        let root = entry.unwrap().path();
        let source = root.join("src");
        if !source.is_dir() {
            continue;
        }
        let krate = root.file_name().unwrap().to_str().unwrap().to_owned();
        let mut files = Vec::new();
        rust_files(&source, &mut files);
        for file in files {
            let text = fs::read_to_string(&file).unwrap();
            let mut rest = text.as_str();
            while let Some(at) = rest.find("const ") {
                let before = &rest[..at];
                rest = &rest[at + "const ".len()..];
                // `const` as a keyword starting an item, not inside an identifier or `const fn`.
                if before
                    .chars()
                    .last()
                    .is_some_and(|c| c.is_alphanumeric() || c == '_')
                {
                    continue;
                }
                let Some(colon) = rest.find(':') else { break };
                let name = rest[..colon].trim();
                if name.is_empty()
                    || !name
                        .chars()
                        .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
                {
                    continue;
                }
                let Some(end) = rest.find(';') else { break };
                let item = &rest[colon + 1..end];
                let Some((kind, value)) = item.split_once('=') else {
                    continue;
                };
                constants.insert(
                    (krate.clone(), name.to_owned()),
                    (kind.trim().to_owned(), value.trim().to_owned()),
                );
            }
        }
    }
    constants
}

/// A constant is versioned when its name ends in `_VERSION` or its value is a string literal
/// ending in `/v<N>`.
fn versioned(name: &str, value: &str) -> bool {
    if name.ends_with("_VERSION") {
        return true;
    }
    let Some(literal) = value.strip_prefix('"').and_then(|v| v.strip_suffix('"')) else {
        return false;
    };
    literal
        .rsplit_once("/v")
        .is_some_and(|(_, n)| !n.is_empty() && n.chars().all(|c| c.is_ascii_digit()))
}

#[test]
fn every_versioned_constant_is_in_the_identity_or_listed_outside_it() {
    let constants = constants();
    let inside = KINK_IDENTITY
        .iter()
        .map(|c| (c.krate.to_owned(), c.constant.to_owned()))
        .collect::<BTreeSet<_>>();
    let outside = OUTSIDE_IDENTITY
        .iter()
        .map(|c| (c.krate.to_owned(), c.constant.to_owned()))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        inside.len(),
        KINK_IDENTITY.len(),
        "a component is named twice"
    );
    assert_eq!(
        outside.len(),
        OUTSIDE_IDENTITY.len(),
        "an exemption is listed twice"
    );
    assert!(inside.is_disjoint(&outside));
    let keys = KINK_IDENTITY.iter().map(|c| c.key).collect::<BTreeSet<_>>();
    assert_eq!(keys.len(), KINK_IDENTITY.len(), "a key is used twice");
    // Every versioned constant is classified. A failure here is a new version constant: add it
    // to KINK_IDENTITY when its change can change a verdict, else to OUTSIDE_IDENTITY with the
    // reason it cannot.
    let unclassified = constants
        .iter()
        .filter(|((_, name), (_, value))| versioned(name, value))
        .map(|(id, _)| id.clone())
        .filter(|id| !inside.contains(id) && !outside.contains(id))
        .collect::<Vec<_>>();
    assert_eq!(unclassified, Vec::<(String, String)>::new());
    // Every listed constant exists, so neither list keeps a stale entry, and every component's
    // value is its constant's literal.
    for component in KINK_IDENTITY {
        let id = (component.krate.to_owned(), component.constant.to_owned());
        let (kind, value) = constants
            .get(&id)
            .unwrap_or_else(|| panic!("{id:?} is not a constant of its crate"));
        assert_eq!(kind, "&str", "{id:?}");
        assert_eq!(*value, format!("{:?}", component.value), "{id:?}");
    }
    for exemption in OUTSIDE_IDENTITY {
        let id = (exemption.krate.to_owned(), exemption.constant.to_owned());
        assert!(
            constants.contains_key(&id),
            "{id:?} is not a constant of its crate"
        );
        assert!(!exemption.reason.is_empty(), "{id:?}");
    }
    // The scan sees the constants it must: the components and the version constants at the
    // time of CACHE-ID, so a broken scan cannot pass by finding nothing.
    for id in [
        ("kink-patch", "CLAIM_REMOVAL_VERSION"),
        ("kink-native", "DEFINITION_EXCLUSION_VERSION"),
        ("kink-native", "EXECUTION_REQUEST_VERSION"),
        ("kink-campaign", "CAMPAIGN_REPORT_VERSION"),
        ("kink-flow", "RUN_VERSION"),
        ("kink-flow", "OUTCOME_SCHEMA_VERSION"),
    ] {
        let id = (id.0.to_owned(), id.1.to_owned());
        let (_, value) = constants.get(&id).unwrap();
        assert!(versioned(&id.1, value), "{id:?}");
    }
}

#[test]
fn the_identity_is_an_object_of_its_components() {
    let identity = kink_identity();
    let object = identity.as_object().unwrap();
    assert_eq!(object.len(), KINK_IDENTITY.len());
    for component in KINK_IDENTITY {
        assert_eq!(
            object[component.key],
            json!(component.value),
            "{}",
            component.key
        );
    }
    assert_eq!(identity["k_rust_revision"], kink_native::K_RUST_REVISION);
    assert_eq!(
        identity["definition_exclusion"],
        kink_native::exclusion::DEFINITION_EXCLUSION_VERSION
    );
    assert_eq!(identity_difference(&identity), None);
    for component in KINK_IDENTITY {
        let mut changed = identity.clone();
        changed[component.key] = json!(format!("{}-other", component.value));
        assert_eq!(
            identity_difference(&changed).as_deref(),
            Some(component.key)
        );
        let mut missing = identity.clone();
        missing.as_object_mut().unwrap().remove(component.key);
        assert_eq!(
            identity_difference(&missing).as_deref(),
            Some(component.key)
        );
    }
    let mut extra = identity.clone();
    extra["later_algorithm"] = json!("kink/later/v1");
    assert_eq!(
        identity_difference(&extra).as_deref(),
        Some("later_algorithm")
    );
    assert_eq!(identity_difference(&json!(null)).as_deref(), Some(""));
}
