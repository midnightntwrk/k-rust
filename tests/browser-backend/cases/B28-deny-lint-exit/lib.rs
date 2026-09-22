// Error exit from a denied lint (the lesson compile passes -D warnings, IR-15):
// the deny-level warning becomes an error, rustc prints the summary line, and
// exits with status 1.
pub fn f() -> u32 {
    let unused = 3;
    4
}
