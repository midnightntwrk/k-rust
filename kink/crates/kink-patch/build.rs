//! Exposes the optimization level kink-patch is compiled at as `cfg(kink_opt_level = "N")`, as
//! k-rust's build scripts expose theirs (`k_rust_opt_level`).
//!
//! The native stack a recursion takes per level is a property of the generated code, and the
//! stack kink-patch provides per level of a JSON document (`digest::JSON_STACK_PER_LEVEL`) and the
//! deepest document it reads (`MAX_JSON_DEPTH`) follow it; Cargo tells the level only to build
//! scripts. Every workspace crate is built at the same level within one profile, so the level is
//! also that of the crates that drop the documents kink-patch parses.

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    println!(
        "cargo::rustc-check-cfg=cfg(kink_opt_level, values(\"0\", \"1\", \"2\", \"3\", \"s\", \"z\"))"
    );
    let level = std::env::var("OPT_LEVEL").expect("Cargo sets OPT_LEVEL for build scripts");
    println!("cargo::rustc-cfg=kink_opt_level=\"{level}\"");
}
