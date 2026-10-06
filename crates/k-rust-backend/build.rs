//! Exposes the optimization level this crate is compiled at as `cfg(k_rust_opt_level = "N")`.
//!
//! The native stack a recursion takes per level is a property of the generated code: the
//! optimization level decides how large each frame is and how many frames a level takes, while
//! debug assertions only add checks. The stack the backend provides per level of a pattern
//! (`nesting::STACK_PER_LEVEL`) and the tests that bound the stack of a recursion per level,
//! tight enough that a regression in frame size fails, need that level, and Cargo tells it only
//! to build scripts.

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    println!(
        "cargo::rustc-check-cfg=cfg(k_rust_opt_level, values(\"0\", \"1\", \"2\", \"3\", \"s\", \"z\"))"
    );
    let level = std::env::var("OPT_LEVEL").expect("Cargo sets OPT_LEVEL for build scripts");
    println!("cargo::rustc-cfg=k_rust_opt_level=\"{level}\"");
}
