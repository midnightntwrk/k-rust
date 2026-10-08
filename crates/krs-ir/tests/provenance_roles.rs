//! Frozen acceptance snapshot for the provenance role protocol seam.

use std::fmt::Write as _;

use krs_ir::ProvenanceRole;

#[test]
fn provenance_role_protocol_catalog_is_frozen() {
    let mut actual = String::new();
    for role in ProvenanceRole::ALL {
        writeln!(actual, "{}={}", role.variant_ident(), role.as_str())
            .expect("writing to a String succeeds");
    }
    expect_test::expect_file!["golden/provenance_roles.txt"].assert_eq(&actual);
    assert_eq!(ProvenanceRole::ALL.len(), 191);
}
