//! Descriptor and collector documents accept only the current schema version, and the version constants agree with the repository lock.

use krs_ir::{DescriptorBundle, SchemaVersion, transport::collector};

#[test]
fn every_noncurrent_schema_version_is_rejected() {
    let expected_schema = format!("expected {}", SchemaVersion::CURRENT.0);
    let expected_collector = format!("expected {}", collector::VERSION);
    let bundle = serde_json::to_value(DescriptorBundle::empty()).unwrap();
    let collector_bytes = DescriptorBundle::empty()
        .to_collector_protocol_measured()
        .unwrap()
        .0;
    let collector_wire: serde_json::Value = serde_json::from_slice(&collector_bytes).unwrap();

    for version in (0..=SchemaVersion::CURRENT.0 + 5).chain([u32::MAX]) {
        if version != SchemaVersion::CURRENT.0 {
            let mut wire = bundle.clone();
            wire["protocol_version"] = version.into();
            let error = serde_json::from_value::<DescriptorBundle>(wire).unwrap_err();
            assert!(error.to_string().contains(&expected_schema), "{error}");

            let mut wire = collector_wire.clone();
            wire["schema"] = version.into();
            let error =
                DescriptorBundle::from_collector_protocol(&serde_json::to_vec(&wire).unwrap())
                    .unwrap_err();
            assert!(error.to_string().contains(&expected_schema), "{error}");
        }
    }

    for version in (0..=collector::VERSION + 5).chain([u32::MAX]) {
        if version != collector::VERSION {
            let mut wire = collector_wire.clone();
            wire["protocol_version"] = version.into();
            let error =
                DescriptorBundle::from_collector_protocol(&serde_json::to_vec(&wire).unwrap())
                    .unwrap_err();
            assert!(error.to_string().contains(&expected_collector), "{error}");
        }
    }
}

#[test]
fn schema_version_equals_the_krs_lock_pin() {
    let lock: toml_edit::Document<String> = toml_edit::Document::parse(
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../Krs.lock")).to_owned(),
    )
    .expect("Krs.lock parses as TOML");
    let pinned = lock["schemas"]["krs_ir"]
        .as_integer()
        .expect("Krs.lock [schemas] krs_ir is an integer");
    assert_eq!(
        u32::try_from(pinned).expect("the pinned schema fits in u32"),
        SchemaVersion::CURRENT.0,
        "SchemaVersion::CURRENT and Krs.lock [schemas] krs_ir must change together"
    );
    let collector_pin = lock["schemas"]["collector"]
        .as_integer()
        .expect("Krs.lock [schemas] collector is an integer");
    assert_eq!(
        u32::try_from(collector_pin).expect("the collector version fits in u32"),
        collector::VERSION,
        "collector::VERSION and Krs.lock [schemas] collector must change together"
    );
}
