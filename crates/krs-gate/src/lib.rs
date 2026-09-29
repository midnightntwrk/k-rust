//! Native KRS gate commands and session protocol.
//!
//! # Commands and Rust APIs
//!
//! `krs-gate compile [--timings FILE] DEFINITION-IR OUTPUT-KORE` writes the compiled KORE definition and, when requested, a `krs-timings/1` document.
//! It reads [`krs_ir::DefinitionIr`] through [`krs_ir::json::from_slice`] and calls [`krs_k_rust::compile_definition_with_context_timed`] with [`krs_k_rust::CompileOptions`] selecting the Haskell backend.
//! The timing document is written on success and failure, uses the document name `native-compile`, and includes `native.input` and `native.write` spans.
//! `krs-gate kore-compare REFERENCE NATIVE MODULE [--label FROM=CANONICAL]... [--reference-claims PATH MODULE]` invokes [`kore_compare::compare_kore`] or [`kore_compare::compare_kore_with_reference_claims`].
//! These compare definitions parsed by [`k_rust::kore::parser::parse_definition`] under the closed normalization and projector policy documented in [`kore_compare`].
//! `krs-gate proof split DEFINITION OUTPUT-DIR MODULE SPEC-MODULE LABEL...` extracts one-claim specifications and a claim-free definition through [`proof`].
//! `krs-gate proof classify RESULT` parses and classifies a proof result through [`proof`].
//! `krs-gate proof assert-spec SPEC SPEC-MODULE MODULE LABEL` validates a specification's module, import, and claim through [`proof`].
//! `krs-gate proof compare-patterns LEFT RIGHT` compares normalized proof residuals through [`proof`] and [`kore_compare::normalize_standalone_pattern`].
//! The proof commands use [`k_rust::kore::parser::parse_definition`], [`k_rust::kore::parser::parse_pattern`], and [`k_rust::kore::printer::Printer`] to read and write their artifacts.
//!
//! # Session protocol
//!
//! `krs-gate session` reads one JSON request per line from stdin and writes one JSON response per line to stdout, flushing after every response.
//! Every request must be an object with string `id` and `operation` fields.
//! Every response carries the same `id` and either `result` or an `error` object with a string `message` field.
//!
//! `definition.load` requires string `module` (the main module) and `definition_ir` (a path to emitted Definition IR) before definition-dependent operations.
//! `kore.digest` may precede it.
//! Loading uses the same Definition IR reader and compilation API as `compile`, then constructs [`k_rust::backend::Backend`] from the compiled KORE and retains its frontend definition and variable sorts.
//! Its result is an object containing the loaded `module`.
//! `definition.load` may be requested only once per session, including when loading fails.
//! `configure` requires a `variables` object mapping names without `$` to surface K text and returns `pattern` (KORE text of `initGeneratedTopCell`) and `variables` (an object mapping each name to `sort` and `kore` text).
//! Every declared variable must be supplied once, except declared `$IO` and `$STDIN` may be omitted; those receive krun stream defaults with IO off and empty stdin.
//! Unknown variable names are errors.
//! Bindings are assembled with `$PGM` first and other supplied names in lexical order, followed by synthesized stream defaults.
//! The shared surface pipeline prepares [`k_rust::inner::definition_with_named_projections`], [`k_rust::definition::ResolvedDefinition`], and [`k_rust::kompile::MacroExpansionDefinition`], then caches [`k_rust::inner::ProgramParser::from_resolved`] per parser module chosen with [`k_rust::kompile::initial_configuration::parser_modules`].
//! It parses at the declared sort, expands macros, uses [`k_rust::kompile::SortInjector`] to determine and inject sorts, and lowers with [`k_rust::kompile::term_to_kore_from_resolved_with_token_module`].
//! Configuration assembly calls [`k_rust::kompile::initial_configuration::top_cell_initializer`] and uses [`k_rust::kompile::initial_configuration::stream_defaults`] for omitted declared stream variables.
//! `execute` requires a KORE text `pattern` and accepts optional `max_depth` (unsigned integer or null), `max_simplification_iterations` (unsigned integer), `trace` (boolean), and `keep` (a state name).
//! It parses the input with [`k_rust::kore::parser::parse_pattern`] and calls [`k_rust::backend::Backend::execute`].
//! Without `keep`, its result is the backend's serialized `ExecuteResult`; leaf traces are empty unless `trace` is true.
//! With `keep`, execution must have exactly one leaf, its final state replaces any previously retained state of that name, and the result contains only the modality and the leaf's reason, depth, optional detail, and trace.
//! `kore.read` requires KORE pattern `text` and a `keep` name; it parses and retains the pattern, replacing a previous state of that name.
//! It wraps [`k_rust::kore::parser::parse_pattern`]; its result contains the retained `state` name.
//! `kore.digest` is available before `definition.load` and requires `kore` (a kompiled definition.kore path) and `semantics` (the absolute source path passed to kompile).
//! It wraps [`k_rust::kore::parser::parse_definition`], shared generated-variable alpha normalization in [`kore_compare`], and [`k_rust::kore::printer::Printer`] through [`kore_digest`].
//! It canonicalizes source paths and compiler-generated variable names and returns `sha256` of the pretty-printed KORE definition.
//! `observe` requires a retained `state` name and an array of `cells` names.
//! Its result maps each name to `kore`, the canonical content KORE text, and `size`, the element count for collection content or null otherwise.
//! Each named cell must occur exactly once in the state.
//! It uses definition-derived structural cell lookup and collection normalization in [`pattern`] and canonical text from [`k_rust::kore::printer::Printer`].
//! `expect` requires `state`, `cell`, and exactly one of `text` (surface K text), `size` (an unsigned collection element count), or `head` (surface text for the first item of a K sequence).
//! Surface text is parsed at the declared frontend cell content sort, macro expanded, sort injected, and lowered through the same Rust API pipeline as `configure`; [`pattern`] compares the resulting KORE structures.
//! For the `K` sort, items parse at `KItem` and `.K` and sequences are assembled with [`k_rust::kast::Term::sequence`] because the program grammar does not supply implicit `KSEQ` productions.
//! A `head` expectation parses at `KItem` and injects the parsed item's declared sort into `KItem`, matching the stored K sequence head.
//! Its result contains `met`, `expected`, and `actual`; the latter two are canonical KORE text for text and head checks, or decimal counts for size.
//! Comparisons normalize nested builtin List association and unit, and Map and Set association, commutation, and unit using the compiled definition's hooks.
//! No other difference is normalized.
//! `prove` requires a string `claim` selector, calls [`k_rust::backend::Backend::prove`] to select and prove a claim in the loaded definition, and returns the backend's serialized [`k_rust::backend::ProofResultOutput`].
//!
//! A failure while handling a valid operation, including a pattern parse or backend error, produces an error response and leaves the session open.
//! After a failed load, only `kore.digest` can succeed in that session.
//! A malformed JSON line, missing `id` or `operation`, unknown operation, definition-dependent operation before a successful load, or second load terminates the session with a nonzero exit status and a message on stderr.

/// Compile Definition IR into native KORE.
pub mod compile;
/// Assemble surface configuration variables through the native frontend.
pub mod configuration;
mod kore_attributes;
/// Compare parsed reference and native KORE definitions.
pub mod kore_compare;
/// Digest parsed reference KORE independently of source locations and generated names.
pub mod kore_digest;
/// Normalize and inspect retained KORE states.
pub mod pattern;
/// Split and classify parsed proof artifacts.
pub mod proof;
/// Serve requests against one loaded native definition.
pub mod session;
