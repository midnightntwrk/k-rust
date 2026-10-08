//! Native KRS gate commands and session protocol.
//!
//! # Commands and Rust APIs
//!
//! `krs-gate compile [--timings FILE] DEFINITION-IR OUTPUT-KORE` writes the compiled KORE definition and, when requested, a `krs-timings/1` document.
//! It reads [`krs_ir_levels::DefinitionIr`] through [`krs_ir::json::from_slice`] and calls [`krs_k_rust::compile_definition_with_context_timed`] with [`krs_k_rust::CompileOptions`] selecting the Haskell backend.
//! The timing document is written on success and failure, uses the document name `native-compile`, and includes `native.input` and `native.write` spans.
//! `krs-gate collector-bundle COLLECTOR-STDOUT DESCRIPTOR-BUNDLE` requires equality between the collector wire decoded by [`krs_ir::DescriptorBundle::from_collector_protocol`] and the typed emitted [`krs_ir::DescriptorBundle`].
//! It returns a JSON summary with the collector wire `protocol_version`, `descriptors` count, and `descriptor_kinds` counts using canonical serialized names.
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
//! `kore.digest`, `kore.attributes`, `ir.query`, `registration.table`, and the `kast.*` operations may precede it.
//! Loading uses the same Definition IR reader and compilation API as `compile`, then constructs [`k_rust::backend::Backend`] from the compiled KORE and retains its frontend definition and variable sorts.
//! Its result contains the loaded `module` and `definition_kore_sha256`, the lowercase SHA-256 hex digest of the compiled KORE text bytes, identical to the bytes written by `compile`.
//! `definition.load` may be requested only once per session, including when loading fails.
//! `configure` requires a `variables` object mapping names without `$` to surface K text and returns `pattern` (KORE text of `initGeneratedTopCell`) and `variables` (an object mapping each supplied name to `sort` and `kore` text).
//! Every declared variable must be supplied once, except declared `$IO` and `$STDIN` may be omitted; those receive krun stream defaults with IO off and empty stdin.
//! Unknown variable names are errors.
//! [`k_rust::kompile::ConfigurationAssembler`] builds `pattern` over one [`k_rust::kompile::ProgramGrammar`] per session, binding `$PGM` first, other supplied names in lexical order, and then the stream defaults.
//! The per-variable `variables` rendering and cell expectations share a surface pipeline over the same grammar: it caches [`k_rust::inner::ProgramParser::from_resolved`] per parser module chosen with [`k_rust::kompile::initial_configuration::parser_modules`], parses at the declared sort, expands macros with [`k_rust::kompile::MacroExpansionDefinition::expand_program`], uses [`k_rust::kompile::SortInjector`] to determine and inject sorts at the expansion position, and lowers with [`k_rust::kompile::term_to_kore_from_resolved_with_token_module`].
//! `execute` requires a KORE text `pattern` and accepts optional `max_depth` (unsigned integer or null), `max_simplification_iterations` (unsigned integer), `trace` (boolean), and `keep` (a state name).
//! It parses the input with [`k_rust::kore::parser::parse_pattern`] and calls [`k_rust::backend::Backend::execute`].
//! Without `keep`, its result is the backend's serialized `ExecuteResult`; leaf traces are empty unless `trace` is true.
//! With `keep`, execution must have exactly one leaf, its final state replaces any previously retained state of that name, and the result contains only the modality and the leaf's reason, depth, optional detail, and trace.
//! `search` requires a KORE text `pattern` and accepts optional `max_depth` and `max_results` (unsigned integers or null) and `keep` (a state name).
//! It parses the input with [`k_rust::kore::parser::parse_pattern`] and calls [`k_rust::backend::Backend::search`] with [`k_rust::backend::SearchRequest`] selecting final states.
//! Without `keep`, its result is the backend's serialized [`k_rust::backend::SearchResponse`].
//! With `keep`, search must return exactly one state, that state replaces any previously retained state of that name, and the result contains `modality` and `states` (the result state count).
//! `kore.read` requires KORE pattern `text` and a `keep` name; it parses and retains the pattern, replacing a previous state of that name.
//! It wraps [`k_rust::kore::parser::parse_pattern`]; its result contains the retained `state` name.
//! `kore.digest` is available before `definition.load` and requires `kore` (a kompiled definition.kore path) and `semantics` (the absolute source path passed to kompile).
//! It wraps [`k_rust::kore::parser::parse_definition`], shared generated-variable alpha normalization in [`kore_compare`], and [`k_rust::kore::printer::Printer`] through [`kore_digest`].
//! It canonicalizes source paths and compiler-generated variable names and returns `sha256` of the pretty-printed KORE definition.
//! `kore.attributes` is available before `definition.load` and requires `kore` (a KORE definition path), `labels` (K label names, encoded to KORE symbol names with [`k_rust::kast::identifier::encode_label`]), and `attributes` (attribute names).
//! It parses the definition with [`k_rust::kore::parser::parse_definition`] and returns `symbols`, an object mapping each label to an object of the named string attributes its unique symbol declaration carries.
//! A label without exactly one declaration, or a named attribute that is not one UTF-8 string, is an error.
//! `registration.table` operates independently of a loaded definition and requires string `source`, `display_file`, `crate_name`, and `facade_alias` fields.
//! Unknown request fields are errors.
//! `source` names an authored crate-root file that must be readable as UTF-8; `display_file` must equal the file spelling rustc reports through `Span::file()`, which determines factory names.
//! `crate_name` is the library crate name at the start of `module_path!()`, and `facade_alias` is the dependency name through which authored code names the KRS facade.
//! It calls [`krs_expand::whole_file::expand_file`] with whole-file selection, module path `[crate_name]`, facade path `::<facade_alias>`, and `display_file` as the generated-file map label.
//! Expansion failures return an error message listing every diagnostic's code and message.
//! Its result contains `table`, the exact text [`krs_expand::whole_file::registration_table`] appends to that expansion, `requests_framework` (boolean), and `registrations` in expansion order.
//! Each registration contains `module_path` (string array starting with the crate name), `factory` (string), and `cfg` (array of Rust attribute strings).
//! The table preserves cfg attributes and uses the expansion's facade path rendered as tokens with spaces removed.
//! The operation fails unless the generated file ends with exactly that table.
//! `ir.query` requires `artifacts` (an `emit-k` output directory) and a closed `query` object with `kind` and the parameters documented below.
//! It operates independently of a loaded definition and reads only the artifacts required by the selected query.
//! Descriptor, Semantic IR, and Definition IR inputs use [`krs_ir::json::from_slice`] with [`krs_ir::DescriptorBundle`], [`krs_ir_levels::SemanticTheory`], and [`krs_ir_levels::DefinitionIr`].
//! Symbol and source inputs use the version-checked [`krs_compiler::SymbolMap`] and [`krs_compiler::SourceMap`] readers.
//! Unknown query kinds and fields are errors.
//! All filters are optional exact matches; omitted filters select all rows.
//! `kind: "absolute_strings"` returns `{rows}` with `{artifact,value}` for every absolute string in each present emitted JSON artifact.
//! It scans descriptor-bundle.json, semantic-ir.json, definition-ir.json, symbols.json, and sources.json as generic JSON, including object keys, object values, and array elements.
//! A string is absolute when [`krs_ir::DisplayPath::is_absolute_spelling`] returns true or it starts with `/`; missing artifacts are skipped and malformed JSON is an error.
//! This lexical hygiene query does not interpret modeled artifact data.
//! `kind: "files"` returns `{expected,actual,owned,has_claims}`.
//! `expected` is the lexical file set from [`krs_compiler::emitted_artifact_names`], including `spec.k` exactly when Definition IR contains claims.
//! `actual` lists directory entries in lexical order and `owned` requires the exact compiler-owned marker bytes.
//! `kind: "modules"` returns `{main_module,rows}`; each row contains `name` and the exact authored and compiler-inferred emitted `imports`.
//! `kind: "semantic_modules"` reads only Semantic IR and returns `{rows}` with `name`, `production_count`, `rule_count`, and `has_configuration`.
//! `kind: "sentences"` accepts `module`, `sentence_kind`, and `label` filters and returns `{rows}` in generated artifact and byte order.
//! Sentence rows contain `module`, `kind`, optional `label` and `rule_kind`, `source_map_key`, optional `generated`, `body`, `initializers`, and optional `associativity`.
//! The sentence kinds are `syntax_sort`, `subsort`, `production`, `precedence`, `associativity`, `configuration`, `context_alias`, `rule`, and `claim`.
//! Generated ranges contain `artifact`, inclusive `start_byte`, exclusive `end_byte`, and scalar line and column coordinates; clients may slice the artifact's UTF-8 bytes at these ranges.
//! Ordinary rule bodies are provenance-free typed term facts; simultaneous bodies contain `kind: "configuration_rewrite"` and ordered `clauses` with `cell`, `from`, `to`, and `frame`.
//! Configuration initializers contain ordered `{cell,term}` facts.
//! Term facts contain `kind` and emitted `sort`, with `symbol` or closed `operation` for applications, `variable` for variables, `token` for tokens, `cell` for cells, ordered `arguments` for composites, and `from` and `to` for rewrites.
//! `kind: "productions"` accepts `module`, `sort`, and `symbol` filters and returns `{rows}` sorted by module and symbol.
//! Each production contains `module`, result `sort`, emitted `symbol`, literal `terminals`, typed `items` with emitted nonterminal sort names, and IR `attributes`.
//! `kind: "vocabulary"` returns sorted sets `sorts`, `production_symbols`, `terminals`, `rule_labels`, and `imports`, plus `cells`, direct `subsorts`, and `applied_operations`.
//! Cell rows contain `name`, leaf `sort` or null, and directly initializing `configuration_variable` or null.
//! Subsort rows contain `sort` (the supersort) and `subsort`.
//! Applied operation rows contain `module`, `label`, optional `symbol`, optional `operation`, optional `hook`, `result_sort`, and ordered `argument_sorts` from rule bodies, requirements, and claim ensures.
//! Builtin and hook identities use their closed IR snake-case names; collection operations use `map.`, `list.`, and `set.` prefixes.
//! `kind: "applications"` accepts `operation`, `symbol`, `result_sort`, `argument_sorts`, and `arguments` filters and returns `{rows}` with the operation fields above and ordered term-fact `arguments`.
//! An argument pattern is a closed object with optional `kind`, `sort`, `symbol`, `operation`, `token`, `variable`, and recursive `arguments`.
//! Every supplied field must match; omitted fields are wildcards, and supplied argument arrays must match exact arity and order.
//! `kind: "descriptors"` accepts `descriptor_kind` and `item_kind` filters and returns `{counts,rows}`.
//! Counts map the selected descriptor and item kinds to their multiplicities; rows contain typed `id`, `descriptor_kind`, `item_kind`, and `cargo_name`.
//! `kind: "descriptor_details"` accepts exact `module_path` and `item_name` filters and `public_only` (default false).
//! It returns `{rows}` with `module_path`, `item_name`, `item_kind`, exact `visibility`, optional `explicit_symbol`, and opaque `normalized` descriptors.
//! Normalized descriptors remove provenance recursively and reduce every package to its `k_namespace`; all other descriptor fields remain exact.
//! `kind: "head_rule_walkthrough"` requires `item_name` and selects exactly one head rule with a declared named-argument subject and builtin positional-variable replacement.
//! It returns `{id,kind,sentence_kind,label,configuration,cell,bindings,subject,result}`.
//! `subject` and `result` each contain `application` and ordered `arguments`; builtin application names carry the `builtin:` prefix.
//! Unsupported walkthrough shapes and ambiguous identities are errors.
//! `kind: "symbol_projection"` requires `emitted_names` and returns `{rows,source_keys}`.
//! Rows retain exactly `identity`, `emitted_name`, and optional `symbol_kind`, sorted by canonical JSON; source-map keys are sorted independently with multiplicity retained.
//! `kind: "source_token"` requires an `authored` source path, `package_relative_path`, `token`, and `artifact` (`definition.k` or `spec.k`).
//! It returns exactly one `{authored_range,generated}` whose authored file digest, relative path, and nonempty UTF-8 token match and whose generated interval is nonempty and in bounds.
//! Exact authored content selects a typed source-map view before generated-to-authored lookup uses [`krs_cli::translate_k_frontend_diagnostic`].
//! A surrounding condition may share the generated interval but cannot match the narrower authored token; multiple exact-token matches are errors.
//! `kind: "replacement_parity"` requires `reference` (an artifact directory), emitted `module`, descriptor `module_path`, package `k_namespace`, `replaced_k_tail_cells`, and `preserved_map_remainder_cells`.
//! The queried directory is the configuration-rule replacement and the reference directory is the head-rule authority.
//! Non-rule descriptors and declarations must agree after removing descriptor provenance, normalizing the `k_namespace` package's Cargo identity, and naming subsorts by sorted typed relations.
//! `k_namespace` is independent of the emitted K `module` whose sentences are compared.
//! It normalizes bindings of replaced K-sequence tails in `replaced_k_tail_cells` and bindings of preserved Map remainders in `preserved_map_remainder_cells` to unbound frames; the rebuilt Definition IR must validate.
//! All other rules, terms, attributes, and grammar remain exact through the canonical compiler printer.
//! Every replacement import and non-claim sentence must occur in the reference multiset with at least the same multiplicity.
//! It returns `{non_rule_counts,non_rule_count,subsort_count,reference_rules,replacement_rules,sentence_count}`; rule maps retain exact Rust-item-to-K-label transport for transitions.
//! Counts and transport expectations remain caller-owned data.
//! `kind: "symbols"` accepts `emitted_name`, `identity_kind`, and `symbol_kind` filters and returns `{rows}` of typed symbol sidecar entries in their stored order.
//! `kind: "sources"` accepts `key`, `node_kind`, and generated `artifact` filters and returns `{rows}` of typed source sidecar entries in their stored order.
//! Source rows add `authored`, a flat array of `{k_namespace,cargo_name,package_relative_path,content_sha256}` for authored provenance frames.
//! `ranged` projects every ranged provenance frame with the same file fields and its `frame_kind`, retaining stored frame order and multiplicity.
//! `kind: "definition_shape"` returns the typed Definition IR serialization with provenance omitted and each rule reduced to its kind and label identity.
//! It preserves module, import, grammar, configuration, initializer, context-alias, sentence-kind, and label structure for readable-versus-expanded parity comparisons.
//! Rule variables, bodies, conditions, and metadata do not participate because independently compiled expansion may introduce explicit tail bindings.
//! `kast.normalize`, `kast.project`, `kast.frontier`, and `kast.inspect` operate independently of a loaded definition.
//! Each KAST input must supply exactly one of `text` (inline KAST JSON), `path` (a UTF-8 KAST JSON file), or `value` (an inline node or envelope).
//! Text and path inputs must carry exactly the `format`, `version`, and `term` envelope fields, with format `KAST` and version [`k_rust::kast::json::VERSION`].
//! `allow_prefix: true` permits text preceding the first `{`; callers must enable this only for tool output that permits leading statistics.
//! Terms use [`k_rust::kast::json::from_str`], definitions use [`k_rust::definition::json::from_str_omitting_unrepresentable`], and module lists use [`k_rust::definition::json::module_list_from_str`].
//! Every read must equal the corresponding writer output as a JSON value; unknown or changed fields are errors.
//! Each omitted sentence is retained outside the typed definition at its original sentence position and written back as the exact `badsentence` sentinel.
//! A `KFlatModuleList` must name one of its modules as `mainModule`, and its modules are written back one by one inside the wrapper.
//! Normalization transforms typed terms, sentences, modules, definitions, and rebuilt attributes before serialization.
//! Attribute payloads remain JSON values; modeled nodes in payloads pass through the typed reader and normalizer.
//! Canonical list sorting and projection grouping occur after serialization.
//! `kast.normalize` requires `variant` and accepts a closed `policy` object.
//! `behavior` requires exactly `label_map`, `sort_map`, `identity_labels`, and `identity_sorts` in its policy and returns a normalized bare term.
//! `proof_result` accepts the same name tables with empty defaults and returns a normalized KAST term envelope.
//! Proof normalization removes location metadata and permits only metadata, `label`, `circularity`, `all-path`, and `one-path` attributes.
//! `proof_claim` accepts that proof policy and requires `label`; it selects exactly one matching claim, rejects priority, and returns a `KRS-IMP-CLAIM` version 1 envelope.
//! `static_proof` requires an empty policy, concrete variable sorts, and a term without rewrites; it returns a normalized KAST term envelope.
//! `static_claim` requires an empty policy and `label`; it requires exactly one claim in a `KFlatModuleList` and requires that claim's label to match.
//! It returns the normalized module-list envelope with sorted imports and sentences.
//! `normalized_definition` requires an empty policy and a definition; it preserves variable names, removes location metadata, sorts modules and their imports and sentences, and returns a KAST definition envelope.
//! Name policies must map each name or include it in the corresponding identity set.
//! Removable metadata attributes must be known wherever attribute validation applies.
//! `kast.project` requires `reference` and `actual` input descriptors, `reference_policy`, and `actual_policy`, and accepts `compatible_sentence_pairs`.
//! Projection policies accept the source pin's module and sentence origins, name tables, attribute tables, import tables, closed prefixes, redundant declarations, joined terminals, and exact ignored and supplemental sentence digest counts.
//! Policy objects must not contain unknown fields; compared and supplemental modules must be disjoint.
//! Each compatibility pair must provide `origin`, `reference_sha256`, `actual_sha256`, and a positive `count`, with an exact witness on each side.
//! Comparison returns `{baseline_sha256,actual_sha256,sentence_count}`; mismatched layouts or sentence multisets are errors.
//! `kast.frontier` requires one normalized term input and `action`.
//! `proof` requires `returncode`, `stderr`, and `constraint_labels`, and returns `{status,frontier}`.
//! It flattens `#Or`, flattens each branch's `#And`, separates constraints from states, and returns sorted canonical branch strings.
//! `constraint_labels` declares the labels classified as constraints.
//! Branch multiplicity is retained; `#Top` and `#Bottom` have empty frontiers.
//! Status is `proved` only for exit 0 with `#Top`, `failed` only for exit 1 with `#Bottom`, and `incomplete` only for exit 1 with another root and the stalled-configuration diagnostic.
//! Other terminations are errors.
//! `action: "search_set"` flattens `#Or` and returns sorted distinct canonical term strings.
//! `kast.inspect` requires `action` and one KAST input.
//! `term` returns the losslessly read bare term; the input envelope is validated by the reader.
//! An optional closed validation `policy` with `labels`, `label_prefixes`, `label_contains`, `parameterized_sorts`, and `variables` restricts term inputs to the configured vocabulary.
//! `abstract_term` requires a `label_map` and returns a nested label/token array.
//! `module_facts` requires a definition and a module `name`.
//! It requires exactly one matching module and returns `{counts,sentences}`.
//! It uses `syntax_sort`, `sort_synonym`, `syntax_lexical`, `production`, `syntax_associativity`, `syntax_priority`, `context_alias`, `context`, `rule`, `claim`, `configuration`, `bubble`, and `bad_sentence` for count keys and sentence `node` values.
//! Each sentence fact contains `node`, `label`, `klabel`, and sorted `attribute_keys` for structure comparisons.
//! `final_environment` returns concrete Id-to-Int/Bool token strings from a generated top configuration with an empty K cell and an environment Map, rejecting duplicate keys.
//! `if_complete: true` returns null when a concrete final environment cannot be extracted.
//! `search_frontier` unwraps exactly `#Equals(Result, frontier)` and returns the frontier term.
//! `search_solution` unwraps `#Equals(variable, state)` for any variable and returns any other term unchanged.
//! `collections` returns the term with builtin Map, Set, and List concatenations flattened, unit-free, left-associated, and (for Map and Set) sorted, so terms from backends that associate collections differently compare equal.
//! `root_label` returns the label name of the term's root application, or null.
//! `k_head` requires `head` and returns whether the first item of the configuration's K sequence is an application with that label.
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
//! The loaded definition is a [`krs_exec::Semantics`], compiled exactly as `krs run` compiles it; `execute`, `search`, and `prove` issue raw k-rust requests to its backend.
//! `exec.run`, `exec.search`, and `exec.prove` run the `krs run`, `krs search`, and `krs prove` code paths of [`krs_exec`] and return their `krs-exec/1` reports.
//! `exec.run` and `exec.search` accept `program` (surface text bound to `$PGM`) with an optional `program_name`, `variables` (an object of `-c` bindings by K name, `$`-prefixed name, or init parameter), and `depth` (unsigned integer or null); `exec.run` also accepts `trace` (boolean), and `exec.search` accepts `mode` (`final`, `all`, `one-step`, or `one-or-more-steps`) and `max_solutions`.
//! `exec.prove` accepts `claims` (labels resolved by exact match or unique suffix; empty proves every claim) and `depth`.
//!
//! A failure while handling a valid operation, including a pattern parse or backend error, produces an error response and leaves the session open.
//! After a failed load, `kore.digest`, `ir.query`, `registration.table`, and the `kast.*` operations can still succeed in that session.
//! A malformed JSON line, missing `id` or `operation`, unknown operation, definition-dependent operation before a successful load, or second load terminates the session with a nonzero exit status and a message on stderr.

/// Compare collector stdout with a typed emitted descriptor bundle.
pub mod collector_bundle;
/// Compile Definition IR into native KORE.
pub mod compile;
/// Assemble surface configuration variables through the native frontend (owned by `krs-exec`).
pub mod configuration;
/// Query version-checked emitted artifact models.
pub mod ir_query;
/// Read and normalize KAST oracle evidence.
pub mod kast;
mod kore_attributes;
/// Compare parsed reference and native KORE definitions.
pub mod kore_compare;
/// Digest parsed reference KORE independently of source locations and generated names.
pub mod kore_digest;
/// Normalize and inspect retained KORE states.
pub mod pattern;
/// Split and classify parsed proof artifacts.
pub mod proof;
/// Render explicit registration tables through whole-file expansion.
pub mod registration;
/// Serve requests against one loaded native definition.
pub mod session;
