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
            ("first", 0, absolute),
            ("second", 1, fallback),
            ("third", 0, absolute),
        ],
    );
    assert_eq!(provenance.invocation().display_file(), "src/lib.rs");
    let anchors = provenance.authored();
    assert_eq!(anchors[0].anchor().display_file(), "src/other.rs");
    assert_eq!(anchors[0].key().role(), "first");
    assert_eq!(anchors[1].anchor().display_file(), "src/third.rs");
    assert_eq!(
        anchors[1].anchor().precision(),
        AnchorPrecision::InvocationFallback
    );
    assert_eq!(anchors[2].anchor().display_file(), "src/other.rs");
    assert_eq!(anchors[2].key().role(), "third");
}

#[test]
#[should_panic(expected = "rustc's absolute display path must remain inside the Cargo package")]
fn compact_provenance_rejects_outside_manifest() {
    let _ = __krs_host_provenance(
        "/package",
        &["/elsewhere/lib.rs"],
        __KrsRawAnchor {
            absolute: true,
            ..raw(0)
        },
        &[],
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
#[should_panic(expected = "KRS parser roles are nonempty")]
fn compact_provenance_rejects_empty_role() {
    let _ = __krs_host_provenance("/package", &["src/lib.rs"], raw(0), &[("", 0, raw(0))]);
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
        &[("same", 0, raw(0)), ("same", 0, raw(0))],
    );
}
