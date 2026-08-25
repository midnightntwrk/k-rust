//! Frozen acceptance snapshot for the parser-owned provenance protocol seam.

const SOURCE: &str = include_str!("../src/provenance.rs");
const GOLDEN: &str = include_str!("golden/provenance_roles.txt");

fn frozen_catalog(source: &str) -> String {
    let mut catalog = String::new();
    for line in source.lines() {
        let Some(mapping) = line.trim().strip_prefix("Self::") else {
            continue;
        };
        let (variant, spelling) = mapping
            .split_once(" => ")
            .expect("every ProvenanceRole mapping has an explicit spelling");
        let spelling = spelling
            .strip_suffix(',')
            .and_then(|value| value.strip_prefix('"'))
            .and_then(|value| value.strip_suffix('"'))
            .expect("every ProvenanceRole spelling is one string literal");
        catalog.push_str(variant);
        catalog.push('=');
        catalog.push_str(spelling);
        catalog.push('\n');
    }
    catalog
}

#[test]
fn provenance_role_protocol_catalog_is_frozen() {
    let actual = frozen_catalog(SOURCE);
    assert_eq!(actual, GOLDEN);
    assert_eq!(actual.lines().count(), 151);
}
