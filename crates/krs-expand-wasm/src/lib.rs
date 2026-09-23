//! Browser-lesson KRS expander module.
//!
//! This crate is the `wasm32-unknown-unknown` module that the browser
//! worker (IR-15) calls to turn one editable lesson file into Rust that its
//! rustc compiles without KRS procedural macros. It holds only the JSON
//! protocol ([`protocol`]) and the Wasm ABI; expansion, source maps, and the
//! registration table are `krs_expand::whole_file`, and the lesson policy
//! pre-pass is `krs_lesson_policy`.
//!
//! ```text
//! krs_expand_alloc(len: u32) -> ptr: u32
//! krs_expand_run(request_ptr: u32, request_len: u32) -> u64      // (response_len << 32) | response_ptr
//! krs_expand_lookup(request_ptr: u32, request_len: u32) -> u64   // (response_len << 32) | response_ptr
//! krs_expand_dealloc(ptr: u32, len: u32)
//! memory
//! ```
//!
//! The module has no imports.

mod abi;
pub mod protocol;

pub use protocol::{lookup_json, run_json};
