//! Integration tests of the public API of `k_rust_backend`: one target, so that shared support
//! is never dead code in another target. The modules live under `tests/backend/`.

#[path = "backend/matching.rs"]
mod matching;
