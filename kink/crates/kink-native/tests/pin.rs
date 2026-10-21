/// Merge packet M-1: kink builds against the k-rust beside it, so the ledger's reference pin no
/// longer names what the workspace builds against (that is `K_RUST_REVISION`, the in-repo
/// k-rust's version, which kink-campaign `tests/identity.rs` checks). It records the full k-rust
/// commit at which kink's premises on the in-repo k-rust were last judged.
#[test]
fn the_reference_pin_is_a_judged_commit_of_the_in_repo_k_rust() {
    let pin: toml::Value = toml::from_str(include_str!("../../../upstream/k-rust.toml")).unwrap();
    let commit = pin["reference_pin"]["k_rust_commit"].as_str().unwrap();
    assert!(
        commit.len() == 40 && commit.chars().all(|c| c.is_ascii_hexdigit()),
        "{commit}"
    );
    assert_eq!(pin["reference_pin"]["checkout"].as_str(), Some(".."));
}
