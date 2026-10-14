//! Compile check for the reviewed `krs expand` reference surface.

#[rustfmt::skip]
#[path = "../../goldens/imp.expanded.rs"]
#[allow(dead_code)]
mod imp;

#[test]
fn expanded_reference_surface_compiles() {
    let _ = std::any::TypeId::of::<imp::Machine>();
}
