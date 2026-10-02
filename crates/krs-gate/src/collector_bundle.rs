//! Typed comparison of collector stdout and the emitted descriptor bundle.

use krs_ir::DescriptorBundle;
use serde_json::{Value, json};
use std::{collections::BTreeMap, error::Error, fs, path::Path};

/// Compare both bundle representations and return oracle metadata.
///
/// # Errors
///
/// Returns an error when either input cannot be read or decoded, or the bundles differ.
pub fn run(collector: &Path, descriptor_bundle: &Path) -> Result<Value, Box<dyn Error>> {
    let wire = fs::read(collector)
        .map_err(|error| format!("could not read `{}`: {error}", collector.display()))?;
    let restored = DescriptorBundle::from_collector_protocol(&wire).map_err(|error| {
        format!(
            "invalid collector stdout `{}`: {error}",
            collector.display()
        )
    })?;
    let pretty: DescriptorBundle = krs_ir::json::from_slice(&fs::read(descriptor_bundle)?)
        .map_err(|error| {
            format!(
                "invalid descriptor bundle `{}`: {error}",
                descriptor_bundle.display()
            )
        })?;
    if restored != pretty {
        return Err("decoded collector stdout differs from the emitted descriptor bundle".into());
    }
    let mut kinds = BTreeMap::<String, usize>::new();
    for descriptor in restored.descriptors() {
        let payload = serde_json::to_value(descriptor.payload())?;
        let kind = payload["descriptor_kind"]
            .as_str()
            .ok_or("serialized descriptor payload lacks its canonical descriptor_kind")?;
        *kinds.entry(kind.to_owned()).or_default() += 1;
    }
    Ok(json!({
        "protocol_version": krs_ir::transport::collector::VERSION,
        "descriptors": restored.descriptors().len(),
        "descriptor_kinds": kinds,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn inputs() -> (
        krs_test_support::TempDir,
        std::path::PathBuf,
        std::path::PathBuf,
    ) {
        let directory = krs_test_support::temp_dir();
        let collector = directory.path().join("collector-stdout.json");
        let pretty = directory.path().join("descriptor-bundle.json");
        fs::write(
            &collector,
            include_bytes!("../../krs-ir/tests/golden/collector_sort_constructors.json"),
        )
        .unwrap();
        fs::write(
            &pretty,
            include_bytes!("../../krs-ir/tests/golden/sort_constructors.json"),
        )
        .unwrap();
        (directory, collector, pretty)
    }

    #[test]
    fn accepts_equal_pair_and_reports_wire_version_and_canonical_kinds() {
        let (_directory, collector, pretty) = inputs();
        assert_eq!(
            run(&collector, &pretty).unwrap(),
            json!({
                "protocol_version": krs_ir::transport::collector::VERSION,
                "descriptors": 3,
                "descriptor_kinds": { "constructor": 2, "sort": 1 },
            })
        );
    }

    #[test]
    fn rejects_mismatched_pair() {
        let (_directory, collector, pretty) = inputs();
        fs::write(
            &pretty,
            DescriptorBundle::new(Vec::new())
                .unwrap()
                .to_canonical_json()
                .unwrap(),
        )
        .unwrap();
        assert!(
            run(&collector, &pretty)
                .unwrap_err()
                .to_string()
                .contains("decoded collector stdout differs")
        );
    }
}
