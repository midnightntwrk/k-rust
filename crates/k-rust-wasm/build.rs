//! Links the WebAssembly module with an 8 MiB stack, the size of a native main thread.
//!
//! Rust's wasm32 default is 1 MiB, on which a program nesting one level per statement traps
//! from about 960 levels when it is parsed, and a nested function application from about 480
//! when it is simplified. The stack is the module's own linear memory below its data and heap:
//! the size is reserved at instantiation and its pages become resident only as the recursion
//! touches them. On wasm32 the engine's call stack is a second bound that the module cannot
//! see or switch (docs/backend-port.md, "Stack bounds").

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    if std::env::var("CARGO_CFG_TARGET_ARCH").as_deref() == Ok("wasm32") {
        println!("cargo:rustc-link-arg-cdylib=-zstack-size=8388608");
    }
}
