//! Root semantics fixture.

#[cfg(not(krs_test))]
compile_error!("generated collector did not apply the selected KRS cfg inputs");

/// A symbol which makes both same-named dependencies part of ordinary Rust.
pub fn dependency_markers() -> (&'static str, &'static str) {
    (same_a::MARKER, same_b::MARKER)
}

