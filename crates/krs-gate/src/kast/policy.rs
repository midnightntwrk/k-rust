//! Deserialize closed policy data once at the request boundary.

use std::collections::{BTreeMap, BTreeSet};

use serde::Deserialize;
use serde_json::Value;

#[derive(Default)]
pub(crate) struct NamePolicy {
    pub(crate) label_map: BTreeMap<String, String>,
    pub(crate) identity_labels: BTreeSet<String>,
    pub(crate) sort_map: BTreeMap<String, String>,
    pub(crate) identity_sorts: BTreeSet<String>,
    pub(crate) name_map: BTreeMap<String, String>,
    pub(crate) identity_names: BTreeSet<String>,
}

impl NamePolicy {
    pub(crate) fn name(&self, raw: &str) -> Result<String, String> {
        self.mapped(raw, "name")
    }

    pub(crate) fn mapped(&self, raw: &str, kind: &str) -> Result<String, String> {
        let (map, identities) = match kind {
            "label" => (&self.label_map, &self.identity_labels),
            "sort" => (&self.sort_map, &self.identity_sorts),
            "name" => (&self.name_map, &self.identity_names),
            _ => return Err(format!("unknown name category {kind:?}")),
        };
        map.get(raw)
            .cloned()
            .or_else(|| identities.contains(raw).then(|| raw.to_owned()))
            .ok_or_else(|| format!("unknown {kind} {raw:?}"))
    }
}

pub(crate) fn metadata_attributes() -> BTreeSet<String> {
    [
        "org.kframework.attributes.Source",
        "org.kframework.attributes.Location",
        "org.kframework.definition.Production",
        "contentStartLine",
        "contentStartColumn",
        "digest",
        "productionID",
        "UNIQUE_ID",
        "syntaxModule",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect()
}

pub(crate) struct AttributePolicy {
    pub(crate) known_attributes: BTreeSet<String>,
    pub(crate) metadata_attributes: BTreeSet<String>,
    pub(crate) attribute_value_map: BTreeMap<String, BTreeMap<String, String>>,
}

impl Default for AttributePolicy {
    fn default() -> Self {
        Self {
            known_attributes: metadata_attributes(),
            metadata_attributes: metadata_attributes(),
            attribute_value_map: BTreeMap::new(),
        }
    }
}

impl AttributePolicy {
    pub(crate) fn validate(&self) -> Result<(), String> {
        if self.metadata_attributes.is_subset(&self.known_attributes) {
            Ok(())
        } else {
            Err("every removable metadata attribute must be known".into())
        }
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct BehaviorPolicy {
    label_map: BTreeMap<String, String>,
    identity_labels: BTreeSet<String>,
    sort_map: BTreeMap<String, String>,
    identity_sorts: BTreeSet<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofPolicy {
    #[serde(default)]
    label_map: BTreeMap<String, String>,
    #[serde(default)]
    identity_labels: BTreeSet<String>,
    #[serde(default)]
    sort_map: BTreeMap<String, String>,
    #[serde(default)]
    identity_sorts: BTreeSet<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct EmptyPolicy {}

pub(crate) fn read(raw: &Value, variant: &str) -> Result<(NamePolicy, AttributePolicy), String> {
    let (names, attributes) = match variant {
        "behavior" => {
            let policy: BehaviorPolicy =
                serde_json::from_value(raw.clone()).map_err(|e| e.to_string())?;
            (
                NamePolicy {
                    label_map: policy.label_map,
                    identity_labels: policy.identity_labels,
                    sort_map: policy.sort_map,
                    identity_sorts: policy.identity_sorts,
                    ..NamePolicy::default()
                },
                AttributePolicy::default(),
            )
        }
        "proof_result" | "proof_claim" => {
            let policy: ProofPolicy =
                serde_json::from_value(raw.clone()).map_err(|e| e.to_string())?;
            (
                NamePolicy {
                    label_map: policy.label_map,
                    identity_labels: policy.identity_labels,
                    sort_map: policy.sort_map,
                    identity_sorts: policy.identity_sorts,
                    ..NamePolicy::default()
                },
                AttributePolicy {
                    known_attributes: metadata_attributes()
                        .into_iter()
                        .chain(["label", "circularity", "all-path", "one-path"].map(str::to_owned))
                        .collect(),
                    metadata_attributes: metadata_attributes(),
                    attribute_value_map: BTreeMap::new(),
                },
            )
        }
        _ => {
            let _: EmptyPolicy = serde_json::from_value(raw.clone()).map_err(|e| e.to_string())?;
            let mut attributes = AttributePolicy::default();
            attributes.metadata_attributes.remove("syntaxModule");
            (NamePolicy::default(), attributes)
        }
    };
    attributes.validate()?;
    Ok((names, attributes))
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    #[test]
    fn closed_typed_policies_reject_unknown_fields_and_values() {
        let value =
            json!({"label_map":{},"sort_map":{},"identity_labels":["f","f"],"identity_sorts":[]});
        let (names, _) = read(&value, "behavior").unwrap();
        assert_eq!(names.identity_labels.len(), 1);
        assert!(names.mapped("other", "label").is_err());
        assert!(read(&json!({}), "behavior").is_err());
        let mut extra = value;
        extra["unknown"] = true.into();
        assert!(read(&extra, "behavior").is_err());
        for (field, invalid) in [
            ("label_map", json!({"f":0})),
            ("sort_map", json!({"Int":true})),
            ("identity_labels", json!([0])),
            ("identity_sorts", json!("Int")),
        ] {
            let mut policy =
                json!({"label_map":{},"sort_map":{},"identity_labels":[],"identity_sorts":[]});
            policy[field] = invalid;
            for variant in ["behavior", "proof_result", "proof_claim"] {
                assert!(read(&policy, variant).is_err());
            }
        }
        for field in [
            "known_attributes",
            "metadata_attributes",
            "constraint_labels",
        ] {
            assert!(read(&json!({field:[]}), "proof_claim").is_err());
        }
        let (_, attributes) = read(&json!({}), "proof_claim").unwrap();
        assert_eq!(attributes.metadata_attributes, metadata_attributes());
        for name in ["label", "circularity", "all-path", "one-path"] {
            assert!(attributes.known_attributes.contains(name));
        }
    }
}
