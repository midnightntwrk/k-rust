#[test]
fn revision_matches_reference_pin() {
    let pin: toml::Value = toml::from_str(include_str!("../../../upstream/k-rust.toml")).unwrap();
    assert_eq!(
        pin["reference_pin"]["k_rust_commit"].as_str(),
        Some(kink_native::K_RUST_REVISION)
    );
}
