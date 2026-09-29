//! Native KRS gate compiler and session protocol.
//!
//! `krs-gate compile [--timings FILE] DEFINITION-IR OUTPUT-KORE` writes the compiled KORE definition and, when requested, a `krs-timings/1` document.
//!
//! `krs-gate session` reads one JSON request per line from stdin and writes one JSON response per line to stdout, flushing after every response.
//! Every request must be an object with string `id` and `operation` fields.
//! Every response carries the same `id` and either `result` or an `error` object with a string `message` field.
//!
//! The first request must be `definition.load` with string `module` (the main module) and `definition_ir` (a path to emitted Definition IR).
//! Loading compiles with the Haskell backend in process using the same options as `compile` and retains its frontend definition and variable sorts.
//! Its result is an object containing the loaded `module`.
//! `definition.load` may be requested only once per session, including when loading fails.
//! `configure` requires a `variables` object mapping names without `$` to surface K text and returns `pattern` (KORE text of `initGeneratedTopCell`) and `variables` (an object mapping each name to `sort` and `kore` text).
//! Every declared variable must be supplied once, except declared `$IO` and `$STDIN` may be omitted; those receive krun stream defaults with IO off and empty stdin.
//! Unknown variable names are errors.
//! Bindings are assembled with `$PGM` first and other supplied names in lexical order, followed by synthesized stream defaults.
//! `execute` requires a KORE text `pattern` and accepts optional `max_depth` (unsigned integer or null), `max_simplification_iterations` (unsigned integer), `trace` (boolean), and `keep` (a state name).
//! Without `keep`, its result is the backend's serialized `ExecuteResult`; leaf traces are empty unless `trace` is true.
//! With `keep`, execution must have exactly one leaf, its final state replaces any previously retained state of that name, and the result contains only the modality and the leaf's reason, depth, optional detail, and trace.
//! `kore.read` requires KORE pattern `text` and a `keep` name; it parses and retains the pattern, replacing a previous state of that name.
//! Its result contains the retained `state` name.
//! `observe` requires a retained `state` name and an array of `cells` names.
//! Its result maps each name to `kore`, the canonical content KORE text, and `size`, the element count for collection content or null otherwise.
//! Each named cell must occur exactly once in the state.
//! `expect` requires `state`, `cell`, and exactly one of `text` (surface K text), `size` (an unsigned collection element count), or `head` (surface text for the first item of a K sequence).
//! Surface text is parsed at the declared frontend cell content sort, macro expanded, sort injected, and lowered through the same pipeline as `configure`.
//! For the `K` sort, a single item parses at `KItem`; `.K` and sequences parse at `K`.
//! A `head` expectation parses at `KItem` and injects the parsed item's declared sort into `KItem`, matching the stored K sequence head.
//! Its result contains `met`, `expected`, and `actual`; the latter two are canonical KORE text for text and head checks, or decimal counts for size.
//! Comparisons normalize nested builtin List association and unit, and Map and Set association, commutation, and unit using the compiled definition's hooks.
//! No other difference is normalized.
//! `prove` requires a string `claim` and returns the backend's serialized `ProveResult`.
//!
//! A failure while handling a valid operation, including a pattern parse or backend error, produces an error response and leaves the session open.
//! After a failed load, no further operation can succeed in that session.
//! A malformed JSON line, missing `id` or `operation`, unknown operation, operation before a successful load, or second load terminates the session with a nonzero exit status and a message on stderr.

/// Compile Definition IR into native KORE.
pub mod compile;
/// Assemble surface configuration variables through the native frontend.
pub mod configuration;
mod kore_attributes;
/// Compare parsed reference and native KORE definitions.
pub mod kore_compare;
/// Normalize and inspect retained KORE states.
pub mod pattern;
/// Split and classify parsed proof artifacts.
pub mod proof;
/// Serve requests against one loaded native definition.
pub mod session;
