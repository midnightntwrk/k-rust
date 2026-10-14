//! Validates the facade provenance decoder used by generated descriptors.

use krs::*;

const fn raw(file: usize) -> __KrsRawAnchor {
    __KrsRawAnchor::new(file, false, (1, 1), (1, 2), true)
}

const fn absolute(file: usize) -> __KrsRawAnchor {
    __KrsRawAnchor::new(file, true, (1, 1), (1, 2), true)
}

#[test]
fn compact_provenance_preserves_files_order_and_precision() {
    let provenance = __krs_host_provenance(
        "/package",
        const {
            &__KrsRawProvenance::new(
                &[
                    "src/lib.rs",
                    "/package/src/other.rs",
                    "/package/src\\third.rs",
                ],
                raw(0),
                const {
                    &[
                        (ProvenanceRole::SortDeclaration, 0, absolute(1)),
                        (
                            ProvenanceRole::SortParent,
                            1,
                            __KrsRawAnchor::new(2, true, (1, 1), (1, 2), false),
                        ),
                        (ProvenanceRole::ConstructorDeclaration, 0, absolute(1)),
                    ]
                },
            )
        },
    )
    .unwrap();
    assert_eq!(provenance.invocation().display_file(), "src/lib.rs");
    let anchors = provenance.authored();
    assert_eq!(anchors[0].anchor().display_file(), "src/other.rs");
    assert_eq!(anchors[0].key().role(), ProvenanceRole::SortDeclaration);
    assert_eq!(anchors[1].anchor().display_file(), "src/third.rs");
    assert_eq!(
        anchors[1].anchor().precision(),
        AnchorPrecision::InvocationFallback
    );
    assert_eq!(anchors[2].anchor().display_file(), "src/other.rs");
    assert_eq!(
        anchors[2].key().role(),
        ProvenanceRole::ConstructorDeclaration
    );
}

#[test]
fn compact_provenance_rejects_outside_manifest() {
    const INVOCATION: __KrsRawAnchor = __KrsRawAnchor::new(0, true, (3, 7), (3, 8), true);
    for (display_file, provenance) in [
        (
            "/target/debug/build/package/out/generated.rs",
            const {
                &__KrsRawProvenance::new(
                    &["/target/debug/build/package/out/generated.rs"],
                    INVOCATION,
                    &[(ProvenanceRole::SortDeclaration, 0, INVOCATION)],
                )
            },
        ),
        (
            "/elsewhere/lib.rs",
            const {
                &__KrsRawProvenance::new(
                    &["/elsewhere/lib.rs"],
                    INVOCATION,
                    &[(ProvenanceRole::SortDeclaration, 0, INVOCATION)],
                )
            },
        ),
    ] {
        let error = __krs_host_provenance("/package", provenance).unwrap_err();
        assert_eq!(
            error,
            HostProvenanceError {
                invocation_file: display_file.to_owned(),
                invocation_start: HostSourcePosition::new(3, 7).unwrap(),
                display_file: display_file.to_owned(),
                manifest_dir: "/package".to_owned(),
                path_error: None,
            }
        );
        assert_eq!(
            error.to_string(),
            format!(
                "display file `{display_file}` is outside Cargo package `/package` (invocation at {display_file}:3:7)"
            )
        );
    }
}

#[test]
fn compact_provenance_reports_outside_authored_file_and_containing_invocation() {
    let error = __krs_host_provenance(
        "/package",
        const {
            &__KrsRawProvenance::new(
                &["src/lib.rs", "/target/out/generated.rs"],
                raw(0),
                const { &[(ProvenanceRole::SortDeclaration, 0, absolute(1))] },
            )
        },
    )
    .unwrap_err();
    assert_eq!(
        error.to_string(),
        "display file `/target/out/generated.rs` is outside Cargo package `/package` (invocation at src/lib.rs:1:1)"
    );
}

#[test]
fn compact_provenance_rejects_non_normalized_package_relative_path() {
    let error = __krs_host_provenance(
        "/package",
        const {
            &__KrsRawProvenance::new(
                &["/package/src/../lib.rs"],
                absolute(0),
                const { &[(ProvenanceRole::SortDeclaration, 0, absolute(0))] },
            )
        },
    )
    .unwrap_err();
    assert!(std::matches!(
        error,
        HostProvenanceError {
            path_error: Some(ref error),
            ..
        } if **error == krs_ir::DisplayPathError::NotNormalized("src/../lib.rs".to_owned())
    ));
    assert_eq!(
        error.to_string(),
        "display file `/package/src/../lib.rs` is not a normalized path inside Cargo package `/package` (invocation at /package/src/../lib.rs:1:1): display path `src/../lib.rs` is not normalized"
    );
}

#[test]
fn compact_provenance_rejects_blank_package_relative_path() {
    let error = __krs_host_provenance(
        "/package",
        const {
            &__KrsRawProvenance::new(
                &["src/lib.rs", "/package/ "],
                raw(0),
                const { &[(ProvenanceRole::SortDeclaration, 0, absolute(1))] },
            )
        },
    )
    .unwrap_err();
    assert_eq!(
        error.path_error.as_deref(),
        Some(&krs_ir::DisplayPathError::Empty(" ".to_owned()))
    );
}

#[test]
#[should_panic(expected = "KRS source positions are one-based")]
fn raw_anchor_rejects_zero_position() {
    let _ = __KrsRawAnchor::new(0, false, (0, 1), (1, 2), true);
}

#[test]
#[should_panic(expected = "a KRS source anchor must end after it starts")]
fn raw_anchor_rejects_reversed_anchor() {
    let _ = __KrsRawAnchor::new(0, false, (1, 2), (1, 1), true);
}

#[test]
#[should_panic(expected = "a KRS source anchor must end after it starts")]
fn raw_anchor_rejects_empty_anchor() {
    let _ = __KrsRawAnchor::new(0, false, (1, 1), (1, 1), true);
}

#[test]
#[should_panic(expected = "host provenance requires at least one authored anchor")]
fn raw_provenance_rejects_empty_authored() {
    let _ = __KrsRawProvenance::new(&["src/lib.rs"], raw(0), &[]);
}

#[test]
#[should_panic(expected = "two authored anchors share a provenance key")]
fn raw_provenance_rejects_duplicate_key() {
    const DUPLICATE: &[(ProvenanceRole, u32, __KrsRawAnchor)] = &[
        (ProvenanceRole::SortDeclaration, 0, raw(0)),
        (ProvenanceRole::SortDeclaration, 0, raw(0)),
    ];
    let _ = __KrsRawProvenance::new(&["src/lib.rs"], raw(0), DUPLICATE);
}

#[test]
#[should_panic(expected = "a KRS source anchor names a missing display file")]
fn raw_provenance_rejects_missing_file() {
    const MISSING: &[(ProvenanceRole, u32, __KrsRawAnchor)] =
        &[(ProvenanceRole::SortDeclaration, 0, raw(1))];
    let _ = __KrsRawProvenance::new(&["src/lib.rs"], raw(0), MISSING);
}

#[test]
#[should_panic(expected = "a relative KRS display filename is blank or absolute")]
fn raw_provenance_rejects_blank_relative_file() {
    const AUTHORED: &[(ProvenanceRole, u32, __KrsRawAnchor)] =
        &[(ProvenanceRole::SortDeclaration, 0, raw(0))];
    let _ = __KrsRawProvenance::new(&[" "], raw(0), AUTHORED);
}

#[test]
fn provenance_shape_errors_are_nameable_through_the_facade() {
    assert_eq!(
        HostSourcePosition::new(0, 1),
        Err(krs::HostProvenanceShapeError::ZeroLine)
    );
}
