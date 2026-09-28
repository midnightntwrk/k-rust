//! The schema version constant and the repository lock agree.

use krs_ir::{SchemaVersion, transport::collector};

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
