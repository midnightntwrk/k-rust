//! Native KRS gate compiler and session protocol.
//!
//! `krs-gate compile [--timings FILE] DEFINITION-IR OUTPUT-KORE` writes the
//! compiled KORE definition and, when requested, a `krs-timings/1` document.
//!
//! `krs-gate session` reads one JSON request per line from stdin and writes one
//! JSON response per line to stdout, flushing after every response.
//! Every request must be an object with string `id` and `operation` fields.
//! Every response carries the same `id` and either `result` or an `error`
//! object with a string `message` field.
//!
//! The first request must be `definition.load` with string `kore` (a path to
//! a compiled definition) and `module` (its main module).
//! Its result is an object containing the loaded `module`.
//! `definition.load` may be requested only once per session, including when
//! loading fails.
//! `execute` requires a KORE text `pattern` and accepts optional `max_depth`
//! (unsigned integer or null), `max_simplification_iterations` (unsigned
//! integer), and `trace` (boolean).
//! Its result is the backend's serialized `ExecuteResult`; leaf traces are
//! empty unless `trace` is true.
//! `prove` requires a string `claim` and returns the backend's serialized
//! `ProveResult`.
//!
//! A failure while handling a valid operation, including a pattern parse or
//! backend error, produces an error response and leaves the session open.
//! After a failed load, no further operation can succeed in that session.
//! A malformed JSON line, missing `id` or `operation`, unknown operation,
//! operation before a successful load, or second load terminates the session
//! with a nonzero exit status and a message on stderr.

/// Compile Definition IR into native KORE.
pub mod compile;
/// Serve requests against one loaded native definition.
pub mod session;
