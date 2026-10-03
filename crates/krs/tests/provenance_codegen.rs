//! Validates the facade provenance decoder used by generated descriptors.

use krs::*;

fn raw(file: usize) -> __KrsRawAnchor {
    __KrsRawAnchor {
        file,
        absolute: false,
        start: (1, 1),
        end: (1, 2),
        exact: true,
    }
}

#[test]
fn compact_provenance_preserves_files_order_and_precision() {
    let absolute = __KrsRawAnchor {
        absolute: true,
        ..raw(1)
    };
    let fallback = __KrsRawAnchor {
        file: 2,
        absolute: true,
        exact: false,
        ..raw(2)
    };
    let provenance = __krs_host_provenance(
        "/package",
        &[
            "src/lib.rs",
            "/package/src/other.rs",
            "/package/src\\third.rs",
        ],
        raw(0),
        &[
            (ProvenanceRole::SortDeclaration, 0, absolute),
            (ProvenanceRole::SortParent, 1, fallback),
            (ProvenanceRole::ConstructorDeclaration, 0, absolute),
        ],
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
    for display_file in [
        "/target/debug/build/package/out/generated.rs",
        "/elsewhere/lib.rs",
    ] {
        let error = __krs_host_provenance(
            "/package",
            &[display_file],
            __KrsRawAnchor {
                absolute: true,
                start: (3, 7),
                end: (3, 8),
                ..raw(0)
            },
            &[],
        )
        .unwrap_err();
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
        &["src/lib.rs", "/target/out/generated.rs"],
        raw(0),
        &[(
            ProvenanceRole::SortDeclaration,
            0,
            __KrsRawAnchor {
                absolute: true,
                ..raw(1)
            },
        )],
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
        &["/package/src/../lib.rs"],
        __KrsRawAnchor {
            absolute: true,
            ..raw(0)
        },
        &[],
    )
    .unwrap_err();
    assert!(matches!(
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
#[should_panic(expected = "stable proc-macro positions are one-based")]
fn compact_provenance_rejects_zero_position() {
    let _ = __krs_host_provenance(
        "/package",
        &["src/lib.rs"],
        __KrsRawAnchor {
            start: (0, 1),
            ..raw(0)
        },
        &[],
    );
}

#[test]
#[should_panic(expected = "KRS emits ordered, non-absolute display anchors")]
fn compact_provenance_rejects_reversed_anchor() {
    let _ = __krs_host_provenance(
        "/package",
        &["src/lib.rs"],
        __KrsRawAnchor {
            end: (1, 1),
            ..raw(0)
        },
        &[],
    );
}

#[test]
#[should_panic(expected = "KRS shared parsers emit nonempty, uniquely keyed provenance")]
fn compact_provenance_rejects_empty_authored() {
    let _ = __krs_host_provenance("/package", &["src/lib.rs"], raw(0), &[]);
}

#[test]
#[should_panic(expected = "KRS shared parsers emit nonempty, uniquely keyed provenance")]
fn compact_provenance_rejects_duplicate_key() {
    let _ = __krs_host_provenance(
        "/package",
        &["src/lib.rs"],
        raw(0),
        &[
            (ProvenanceRole::SortDeclaration, 0, raw(0)),
            (ProvenanceRole::SortDeclaration, 0, raw(0)),
        ],
    );
}
