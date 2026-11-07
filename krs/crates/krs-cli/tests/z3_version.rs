//! krs links the Z3 release `Krs.lock` `[solver] linked` names.
//!
//! Whether a query bounded by Z3's resources is decided is a function of the query, the budget
//! and the Z3 build, so KRS's tests, k-rust's tests and the solve budgets they were measured with
//! hold for one release only. The default features link that release statically (k-rust's
//! release download); a build on `z3-inference` alone links whatever the build environment
//! provides, and this test fails it when that is another release.

/// The `[solver] linked` release of `Krs.lock`.
fn pinned() -> String {
    let lock = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../Krs.lock"))
        .parse::<toml_edit::DocumentMut>()
        .expect("Krs.lock parses as TOML");
    lock["solver"]["linked"]
        .as_str()
        .expect("Krs.lock [solver] linked is a string")
        .to_owned()
}

/// Whether `reported`, a `Z3_get_full_version` text, names the release `version`.
///
/// Builds spell the full version differently (`Z3 4.16.0.0`, `4.12.5.0`, and `5.3.3.0` followed by
/// the commit from the `CMake` build of Z3), so the text is compared without the `Z3 ` prefix and with
/// anything after the patch number's `.`.
fn names_release(reported: &str, version: &str) -> bool {
    let reported = reported.strip_prefix("Z3 ").unwrap_or(reported);
    reported == version || reported.starts_with(&format!("{version}."))
}

#[test]
fn krs_links_the_pinned_z3() {
    let pinned = pinned();
    match k_rust::backend::z3_version() {
        Some(linked) => assert!(
            names_release(linked, &pinned),
            "this build links {linked}, but krs supports Z3 {pinned} (Krs.lock [solver] linked): \
             build with the default features, which download and link that release, or provide \
             that release to a `z3-inference` build"
        ),
        // A portable build links no Z3, so there is none to mislink.
        None => {
            #[cfg(feature = "z3-inference")]
            panic!("a `z3-inference` build reports no linked Z3");
        }
    }
}

#[test]
fn a_release_is_named_with_or_without_its_prefix_and_tweak() {
    assert!(names_release("Z3 4.16.0.0", "4.16.0"));
    assert!(names_release("4.16.0", "4.16.0"));
    assert!(!names_release("Z3 4.12.5.0", "4.16.0"));
    assert!(!names_release("Z3 4.16.01.0", "4.16.0"));
    assert!(names_release(
        "5.3.3.0 430d19e697e2ec9bad79ff210d41b4a7a5fcfa3e 430d19e",
        "5.3.3"
    ));
    assert!(!names_release("5.3.30.0 430d19e", "5.3.3"));
}
