//! Exposes the optimization level this crate is compiled at as `cfg(k_rust_opt_level = "N")`.
//!
//! The native stack a recursion takes per level is a property of the generated code: the
//! optimization level decides how large each frame is and how many frames a level takes, and
//! debug assertions add checks and the data they read. The stack the compile passes are given
//! per level of a term (`stack::STACK_PER_LEVEL`) needs that level, and Cargo tells it only to
//! build scripts.

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    println!(
        "cargo::rustc-check-cfg=cfg(k_rust_opt_level, values(\"0\", \"1\", \"2\", \"3\", \"s\", \"z\"))"
    );
    let level = std::env::var("OPT_LEVEL").expect("Cargo sets OPT_LEVEL for build scripts");
    println!("cargo::rustc-cfg=k_rust_opt_level=\"{level}\"");
}
