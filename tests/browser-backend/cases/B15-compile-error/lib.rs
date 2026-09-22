// Control for the error path that works: rustc.wasm prints the diagnostics
// and then traps (IR-03, IR-06); the twin exits 1. The suite classifies both as
// a compile error and compares the error codes and messages.
pub fn f() -> u32 {
    missing::g()
}

pub fn g(_: Missing) {}
