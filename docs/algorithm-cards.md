# Algorithm cards

Algorithm cards are the source declarations from which the workspace algorithm graph is generated.
They live beside the implementation they describe; this document defines their syntax and validation contract.

## Fences and primary cards

A primary card is a TOML fence tagged `algorithm` in the `//!` head of the algorithm's home module.
The prose around the fence remains the human explanation and is not parsed.
More than one primary card may appear in one module head when the module implements more than one algorithm.

```toml
id = "backend.matching.syntactic"
name = "sort-aware one-way first-order matching by pair decomposition"
sites = ["match_terms", "match_terms_with_context", "Matcher::run", "Matcher::match_one"]
variable = "p = pairs popped, bounded by |pattern| plus one re-enqueue per deferred pair; a = pair arity"
counters = ["MatchingProblems", "MatchingPairs"]

[[cost]]
mode = "one matching problem"
bound = "O(p x a)"
```

Every primary card must contain:

- `id`, equal to one `Algorithm::as_str()` value;
- `name`, a human-readable algorithm name;
- `sites`, a non-empty list of implementation symbols in the same file as the card; and
- one or more `[[cost]]` entries, each with a `mode` and `bound`.

The `mode` distinguishes costs of the same algorithm, including fast and slow paths, collection kinds, and retry modes.
When a bound names a variable, the card must define it in `variable`.
A card with measurement counters uses `counters = ["CounterVariant", ...]`, with variant names from `Counter::ALL`.
A card without a dedicated counter must use `counters = []` and state the reason in `no_counter`.

The optional primary-card keys are:

- `invariant`, for the loop invariant stated by the module head; the corresponding `// Invariant:` comment remains at the loop;
- `consumes` and `produces`, for representation boundaries;
- `constrains = [{ id, site, via }]`, for a contract or ordering dependency without a call;
- `variant_of = "algorithm.id"` and `falls_back_to = ["algorithm.id", ...]`, for declared relationships to another algorithm; fallback order is list order;
- `span`, for the runtime instrumentation policy; and
- `tests`, for repository-relative test paths.

Every `tests` entry must be a relative path, without `..`, to a file under the workspace root.

`span` is either `"per problem"`, `"per call"`, or `"none"`.
The key may be absent until the ticket responsible for instrumentation chooses the policy.

## Sites and site cards

Every `sites` entry names a Rust symbol in the same file as its fence.
Accepted forms include `function_name`, `TypeName`, `TypeName::method`, and `impl TypeName`.
A site is never a line number, path-and-line anchor, prose description, or symbol in another file.
Site order is significant: the first entry is an operational entry point suitable for the algorithm's span when one callable site covers the algorithm; later entries locate supporting implementation.

An implementation site outside the home module uses a TOML fence tagged `algorithm-site` in the `///` documentation of the item that contains it:

```toml
id = "backend.fresh.variables"
role = "part"
sites = ["freshen_claim"]
```

A site card must contain `id`, `role`, and `sites`.
The role is one of `"part"`, `"variant"`, or `"fallback"`.
A variant site may add a scalar `variant_of`; a fallback site may add an ordered `falls_back_to` list.
The referenced algorithm identity must exist; a card must not create an identity that is absent from `Algorithm::ALL`.

## Representations and constraints

An entry in `consumes` or `produces` is either a workspace type path or `{ type = "workspace::Type", role = "meaning" }`.
The type must resolve in the workspace.
The optional role distinguishes different meanings of one Rust type and participates in representation identity.
A card declares a representation only where the Rust type or its role changes; ordinary `Term`-to-`Term` backend steps do not declare representation edges.

A `constrains` entry names the producer node, names one consumer `site` from the declaring card, and explains the non-call carrier in `via`.
For example, backend internalization depends on the sentence numbering performed before KORE emission:

```toml
constrains = [
  { id = "kompile.sentences.number", site = "BackendDefinition::internalize_for_source_execution", via = "the UNIQUE_ID attribute set by number_sentences" },
]
```

The generator resolves the referenced identity and the consumer site.
It does not infer a constraint from prose or from a call graph.

## Reading the gate report

The freshness gate is `crates/algo-graph/tests/freshness.rs`; it runs under `cargo test` and fails on any card-contract violation.
Its advisory findings (uncovered phases, unclaimed counters, runtime-invisible algorithms, and worklists without a card) never fail it.
The gate writes them, one per line, to `target/algo/report.txt` below the workspace root and prints `algo-graph report: <n> lines written to <path>` in a plain `cargo test` run, without `--nocapture`.
`cargo run -p algo-graph -- graph` prints each finding and the same summary line to standard error and rewrites the same file.

## Reviewing card drift

Before asking an agent to re-read cards after an implementation change, run:

```sh
cargo run -p algo-graph -- drift --since <revision>
```

Use `--until <revision>` to inspect a closed revision range instead of the index and working tree.
The command reports a card when a changed Git hunk intersects one of its named Rust items but does not intersect the card fence.
It compares the `syn` token stream of the item at both ends of the range, so comment-only and formatting-only edits are omitted.
Each finding names the card, the item, and the relevant zero-context hunks.
The report is advisory and always exits successfully when findings are present; it is not part of the workspace freshness test.

When a real constraint endpoint is not an algorithm, an `algorithm-contract` fence declares an anchored contract node instead of inventing an `Algorithm` identity.
The fence must contain an id beginning with `contract.`, a name, exactly one site, and exactly one `constrains` entry.
The counter writer is such a contract because `Counter::ALL` and `write_counters_if_requested` are a registry and an output site, not algorithms:

```toml algorithm-contract
id = "contract.counters.krust_writer_order"
name = "stable KRUST_COUNTERS key order"
sites = ["write_counters_if_requested"]
constrains = [
  { id = "Counter::ALL", site = "write_counters_if_requested", via = "Snapshot::iter preserves Counter::ALL declaration order" },
]
```

## Worked cases

### One function hosts several algorithms

`rewrite/apply.rs` declares `backend.rewrite.apply` with `sites = ["apply_rule_with_match"]`.
Its `initial_match` and `simplify_conditions` functions also carry site cards for `backend.matching.syntactic` and `backend.simplify.predicates`, respectively.
The remaining P1-to-P13 labels stay prose: phases are not algorithm identities.
In particular, the SAT-narrowing phase does not receive a separate card unless `Algorithm::ALL` first gains an identity that describes it.

```toml algorithm
id = "backend.rewrite.apply"
name = "one-rule conditional rewriting"
sites = ["apply_rule_with_match"]
variable = "r = unmatched remainder pairs"
counters = ["RewriteRuleAttempts", "RewriteMatchFailures", "SmtQueries"]

[[cost]]
mode = "indeterminate recovery"
bound = "up to eleven recovery strategies with recursion depth at most |r| + 1"
```

```toml algorithm-site
id = "backend.matching.syntactic"
role = "part"
sites = ["initial_match"]
```

### One algorithm spans files

`fresh.rs` is the home of `backend.fresh.variables` and names only symbols in `fresh.rs`.
The `freshen_claim` item in `proof.rs`, `freshen_existentials` in `implication.rs`, and the alias-local fresh-name item in `alias.rs` each use an `algorithm-site` card with `role = "part"`.
The object-language substitution in `builtin/substitution.rs` has its own primary identity, `backend.fresh.object_language`, because it operates in a different name domain.

In `fresh.rs`:

```toml algorithm
id = "backend.fresh.variables"
name = "counter-suffixed backend variable naming with collision retry"
sites = ["fresh_name", "fresh_variable", "freshen_existential"]
variable = "c = colliding candidate names"
counters = []
no_counter = "fresh backend variable naming has no dedicated counter"

[[cost]]
mode = "shared counter"
bound = "O(c) per name, amortized O(1)"
```

In `proof.rs`:

```toml algorithm-site
id = "backend.fresh.variables"
role = "part"
sites = ["freshen_claim"]
```

### Composition without a call

The primary `backend.definition.internalize` card in `definition.rs` has a `constrains` entry for `kompile.sentences.number`.
The `via` text names the `UNIQUE_ID` attribute set by `number_sentences`, which survives KORE emission and determines rewrite order during internalization.

```toml algorithm
id = "backend.definition.internalize"
name = "KORE definition validation and internalization"
sites = ["BackendDefinition::internalize_for_source_execution"]
variable = "d = definition sentences and pattern nodes"
counters = []
no_counter = "the internalize phase of kprove timings measures the whole boundary"
constrains = [
  { id = "kompile.sentences.number", site = "BackendDefinition::internalize_for_source_execution", via = "the UNIQUE_ID attribute set by number_sentences" },
]

[[cost]]
mode = "one definition load"
bound = "O(d)"
```

## Backend modules without primary cards

The backend module map includes files that define shared representations or responsibilities rather than algorithms.
They intentionally have no primary card:

```toml
[[without_primary_card]]
files = ["crates/k-rust-backend/src/term.rs", "crates/k-rust-backend/src/term/names.rs"]
classification = "responsibility-only"
reason = "shared immutable term representation and naming vocabulary"

[[without_primary_card]]
files = ["crates/k-rust-backend/src/smt.rs"]
classification = "responsibility-only"
reason = "portable SMT-LIB translation responsibility; the bounded result-cache algorithm is in smt/z3.rs"

[[without_primary_card]]
files = ["crates/k-rust-backend/src/rewrite/mod.rs"]
classification = "responsibility-only"
reason = "shared rewrite types, public entry points, and re-exports; algorithms are declared in the rewrite submodules"

[[without_primary_card]]
files = ["crates/k-rust-backend/src/rewrite/predicates.rs"]
classification = "responsibility-only"
reason = "predicate vocabulary and shared operations, not one algorithm"

[[without_primary_card]]
files = ["crates/k-rust-backend/src/builtin.rs"]
classification = "responsibility-only"
reason = "hook dispatch responsibility; the object-language substitution algorithm is in builtin/substitution.rs"

[[without_primary_card]]
files = [
  "crates/k-rust-backend/src/builtin/bytes.rs",
  "crates/k-rust-backend/src/builtin/float.rs",
  "crates/k-rust-backend/src/builtin/krypto.rs",
  "crates/k-rust-backend/src/builtin/list.rs",
  "crates/k-rust-backend/src/builtin/map.rs",
  "crates/k-rust-backend/src/builtin/set.rs",
  "crates/k-rust-backend/src/builtin/string.rs",
]
classification = "responsibility-only"
reason = "bounded namespace hook implementations dispatched by builtin.rs; they do not share one algorithm identity"

[[without_primary_card]]
files = ["crates/k-rust-backend/src/externalize.rs", "crates/k-rust-backend/src/verify.rs"]
classification = "responsibility-only"
reason = "boundary conversion and sentence verification responsibilities"
```

No reference-set module is classified as data-only.
A future data-only module must be listed with `classification = "data-only"` and a reason instead of receiving an algorithm identity.

## Frontend modules without primary cards

The parser, definition, and kompile conversions keep family and data modules card-less when a concrete algorithm has another home or the file is a stage-table phase rather than an algorithm identity:

```toml
[[without_primary_card]]
files = ["crates/k-rust/src/inner/mod.rs"]
classification = "responsibility-only"
reason = "pipeline index and re-exports; each parser layer declares its algorithms in its implementation module"

[[without_primary_card]]
files = [
  "crates/k-rust/src/definition/ast.rs",
  "crates/k-rust/src/definition/attribute_keys.rs",
  "crates/k-rust/src/definition/synonyms.rs",
  "crates/k-rust/src/outer/ast.rs",
]
classification = "data-only"
reason = "definition and outer-syntax data, vocabulary, and local codecs; traversal algorithms declare their cards at parser, resolver, catalog, check, lowering, or emission homes"

[[without_primary_card]]
files = [
  "crates/k-rust/src/definition/checks/attributes.rs",
  "crates/k-rust/src/definition/checks/deprecated.rs",
  "crates/k-rust/src/definition/checks/functions.rs",
  "crates/k-rust/src/definition/checks/kompile_checks.rs",
  "crates/k-rust/src/definition/checks/labels.rs",
  "crates/k-rust/src/definition/checks/production_shapes.rs",
  "crates/k-rust/src/definition/checks/regexes.rs",
  "crates/k-rust/src/definition/checks/rhs_variables.rs",
  "crates/k-rust/src/definition/checks/smt_lemmas.rs",
  "crates/k-rust/src/definition/checks/sorts.rs",
  "crates/k-rust/src/definition/checks/term_position.rs",
]
classification = "responsibility-only"
reason = "Java-compatible checks composed by definition.checks.run; no submodule states a distinct asymptotic bound"

[[without_primary_card]]
files = ["crates/k-rust/src/kompile/passes.rs"]
classification = "responsibility-only"
reason = "shared pass scaffolding and re-exports; it does not define one transformation algorithm"

[[without_primary_card]]
files = [
  "crates/k-rust/src/kompile/passes/add_implicit_computation_cell.rs",
  "crates/k-rust/src/kompile/passes/check_simplification.rs",
  "crates/k-rust/src/kompile/passes/finalize.rs",
  "crates/k-rust/src/kompile/passes/guard_or_patterns.rs",
  "crates/k-rust/src/kompile/passes/propagate_macro.rs",
  "crates/k-rust/src/kompile/passes/remove_unit.rs",
  "crates/k-rust/src/kompile/passes/resolve_anon_vars.rs",
  "crates/k-rust/src/kompile/passes/resolve_fresh_config_constants.rs",
  "crates/k-rust/src/kompile/passes/resolve_function_with_config.rs",
  "crates/k-rust/src/kompile/passes/resolve_heat_cool.rs",
  "crates/k-rust/src/kompile/passes/resolve_semantic_casts.rs",
]
classification = "phase-only"
reason = "stage-table transformations with no independent algorithm identity or distinct cost claim"

[[without_primary_card]]
files = ["crates/k-rust/src/kompile/passes/constant_folding_float.rs"]
classification = "responsibility-only"
reason = "floating-point support for kompile.constant_folding.evaluate, whose primary card is in constant_folding.rs"
```
