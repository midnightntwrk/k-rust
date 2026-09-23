# Algorithm cards

Algorithm cards are the source declarations from which the workspace algorithm graph is generated.
They live beside the implementation they describe; this document defines their syntax and validation contract.
The generated [algorithm map](algorithm-map.md) renders the whole graph in one document and is the starting point for work that spans algorithms.

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
- `span`, for the runtime instrumentation policy;
- `tests`, for repository-relative test paths; and
- `lean`, for the Lean theorems whose models mirror the card's sites.

Every `tests` entry must be a relative path, without `..`, to a file under the workspace root.

## Lean proofs on cards

A card whose sites a Lean model mirrors names the model's theorems:

```toml
lean = ["KRust.MaximalModels.maximal_models_spec", "KRust.SubsortEncoding.new_equiv"]
```

Every `lean` entry must be a line of `lean/theorems.txt`, at most once per card.
That file is the sorted list of the theorems written in the `KRust` modules; `scripts/lean-check.sh` fails when it differs from what the Lean project proves (`lean/README.md`, "Checking"), so the freshness gate checks the names without running Lean.
Primary, site, contract, and representation cards may carry the key; put it on the card whose `sites` include the Rust items the model's anchors name, and add those items to `sites` when they are missing, because `algo-graph drift` only watches named sites.
A drift finding for such a card ends with `re-check the Lean models of: …`: the model must be compared with the changed Rust, and its anchors updated (`lean/README.md`, "Conventions").
The generated map lists every card with a `lean` key under "Lean proofs".

## Representation cards

A representation card records what every value of one workspace type satisfies, and names the sites that establish it.
It is a TOML fence tagged `algorithm-representation` in the `//!` head of the type's home module:

```toml
id = "representation.backend.term"
name = "immutable backend term with a cached structural hash"
type = "k_rust_backend::term::Term"
sites = ["Term::new", "Term::map", "Term::set"]
invariant = "…"
tests = ["crates/k-rust-backend/tests/backend/term_order.rs"]
lean = ["KRust.TermAttributes.ceilFree_sound"]
```

A representation card must contain:

- `id`, beginning with `representation.`, declared once;
- `name`;
- `type`, a workspace type path that resolves to one item;
- `sites`, a non-empty list of symbols in the same file, the items that establish or could break the invariant; and
- `invariant`, the statement itself.

`tests` and `lean` are optional; cost, counters, span policy, and relations are not allowed, because a representation card is not an algorithm and needs no `Algorithm` identity.
The generator adds one `invariant` node per card; the map lists them under "Representation invariants", and `algo-graph drift` reports a changed site as it does for algorithm cards.
A module with a representation card and no primary card stays listed under the modules without primary cards below.

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
A site card carries `consumes`, `produces`, or `constrains` only when its site is the process boundary where a representation enters or leaves the program, as the command-line entry points in `main.rs` do; every other representation and constraint is declared on a primary card.
The role is one of `"part"`, `"variant"`, or `"fallback"`.
A variant site may add a scalar `variant_of`; a fallback site may add an ordered `falls_back_to` list.
The referenced algorithm identity must exist; a card must not create an identity that is absent from `Algorithm::ALL`.

## Representations and constraints

An entry in `consumes` or `produces` is either a workspace type path or `{ type = "workspace::Type", role = "meaning" }`.
The type must resolve in the workspace.
The optional role distinguishes different meanings of one Rust type and participates in representation identity.
A card declares a representation only where the Rust type or its role changes; ordinary `Term`-to-`Term` backend steps do not declare representation edges.
A representation whose producer or consumer has no card, because it is an input file, a host, or another process, is declared on the one side that has a card.

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
Its advisory findings (uncovered phases, unclaimed counters, runtime-invisible algorithms, worklists without a card, and undeclared representation uses) never fail it.
The gate writes them, one per line, to `target/algo/report.txt` below the workspace root and prints `algo-graph report: <n> lines written to <path>` in a plain `cargo test` run, without `--nocapture`.
`cargo run -p algo-graph -- graph` prints each finding to standard error; without `-o` it also rewrites the same file and prints the same summary line, and with `-o` it writes only the requested output.

An `undeclared representation use` line names an algorithm that branches on a declared representation returned by a producer of that representation while none of the algorithm's cards consumes or produces it.
It is a syntactic heuristic, not type resolution, and its absence proves nothing:

- a pattern path is resolved through the `use` declarations in scope: explicit `use a::b::Name` and `use a::b::X as Name` in the file, a type the file defines, and, for a glob such as `use super::*`, the explicit `use` declarations and types of the workspace module file the glob names (one level); `crate::`, `self::`, and `super::` are made absolute, and a crate root's own `use` re-export, such as `pub use k_rust_kore::kore` in `k-rust`, is followed;
- a resolved path names a representation when it equals the declared type without generic arguments, so an alias such as `KoreSentence` names `k_rust_kore::kore::ast::Sentence` and a bare `Sentence` resolved to `k_rust::definition::Sentence` does not;
- a path that cannot be resolved names every representation whose simple name, the last segment of a `consumes` or `produces` type without generic arguments, equals the pattern segment, so two types with one simple name are not distinguished there;
- a use is a pattern path naming the representation inside a `match` arm, `let`, `let`-`else`, `if let`, `while let`, or `matches!` pattern outside `#[cfg(test)]` modules, whose scrutinee is a call to a function named like the last `::` segment of a site of an algorithm that produces the representation, directly or through a `let name = function(..);` binding earlier in the same item;
- a use belongs to the algorithms whose cards in the same file name the enclosing item as a site, or, when no card in the file names it, to every algorithm whose primary card is in the file.

A type annotation, a constructor, a method-call scrutinee, and a match on a value obtained another way are not uses: the finding targets an algorithm that decides on another algorithm's outcome, not one that traverses a structure it already holds.

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

## Comparing runs by algorithm

`algo-graph join` projects one run's trace and receipt onto the graph as a `join.toml` of schema 2, and `algo-graph query hot --join` reads one join.
To compare two builds on one workload, run:

```sh
cargo run -p algo-graph -- diff --before <join.toml>... --after <join.toml>... [--format text|toml]
```

Each flag is repeatable, and the joins of one side must be repeats of one workload and claim; a side that mixes workloads is refused, and a join of another schema is refused with its path.
For every quantity, a side's value is the median over its repeats, the mean of the two middle values for an even number, with the min..max range.
An algorithm without a row in a join counts as zero spans, zero seconds, and zero counters in that join.

- Span counts and counters are deterministic: the delta is the after median minus the before median, and it is exact when every repeat of each side agrees; otherwise it is marked `varies`.
- A self or total time delta is `unreplicated` when either side has fewer than two joins, `within noise` when the before and after ranges overlap, and `faster` or `slower` otherwise.
- An algorithm's counters are the counters its card declares, measured inside its spans including nested spans (`trace_total`); receipt counters are the process-wide totals of `counters.json`.
- An algorithm is added when some after join declares it and no before join does, and removed conversely.

The output lists the added and removed algorithms, every changed span count, algorithm counter, and receipt counter, every changed verdict, then the algorithms with a span on either side by decreasing absolute self-time delta, then the receipt counters that are nonzero on either side.

## Summarizing receipts into a cost atlas

An `atlas.toml` index (schema 1) names the receipts of one commit: per receipt its `workload`, `command`, optional ladder `param_name` and numeric `param`, `repeat`, `join` path relative to the index, and the measured (untraced) run's `wall_seconds`, `peak_rss_kib`, and `stdout_bytes`; each measurement is optional, and `scripts/algo-receipt.sh --atlas` writes all three.

```sh
cargo run -p algo-graph -- atlas --index <atlas.toml> [-o atlas.md] [--toml atlas.toml] [--check]
```

The Markdown is written for agents: a header with the rules and the command that regenerates it, then compact tables.
A workload is its receipts without a parameter, or, for a ladder, its receipts at the largest parameter.

- Share: an algorithm's share of a run is its self seconds divided by the run's span seconds, the sum of self seconds over every algorithm of the join.
  Because self time subtracts the directly nested algorithm spans, that sum is the time inside outermost algorithm spans.
  The denominator is span time rather than wall time: both numerator and denominator come from the same spans on the same clock, while wall time also holds process start, unspanned work, and trace writing that no algorithm row can claim.
  A workload's share is the median of its per-run shares, and each workload table prints its span-to-wall ratio.
- Ceiling: the Amdahl ceiling is `1 / (1 - share)`, the factor by which span time would shrink if the algorithm's self time were zero; on one thread it also bounds the wall-time speedup `1 / (1 - share x span/wall)`.
- Cut: a workload lists algorithms by decreasing share until the listed shares reach 90 % of span time, then every further algorithm above 1 %.
  Each listed algorithm shows its span count and the counters that moved in its spans outside nested algorithm spans, with `?` on a counter its card does not declare.
- Matrix: every listed algorithm's median share in every workload, ordered by the number of workloads in which it exceeds 1 %.
- Slope: along a ladder, an algorithm whose median span count is positive at two or more parameter values is fitted by least squares of ln(value) on ln(param) for its span count, self seconds, and each counter its card declares (measured inside its spans including nested spans), over the parameter values where the median value is positive.
  Each fit prints its slope, its number of points, and R²; a fit from fewer than three points is marked `*`.
  The card's `[[cost]]` bounds and `variable` are printed beside the fit, not parsed.
- Run growth: each ladder section opens with a table of the whole run at each parameter value (median wall seconds, peak RSS, and stdout size over the repeats that record them) and two slope rows for each of the three: the least-squares fit over every parameter value, with the same points and marks, and the top slope between the two largest parameter values.
  They measure the whole process, so no algorithm row carries a space bound.
  A fixed baseline (the binary, the loaded definition) lowers every slope below the exponent of the growing part, most at the smallest parameter values, so the top slope is the least lowered: `fun-build-list-length` at n = 10 to 300 fits peak RSS at 0.80 over the ladder and 2.03 between 100 and 300.
  A ladder is marked when the peak-RSS fit or top slope exceeds 1.5: the ladders' parameters grow the input at most linearly, so a marked ladder's memory grows superlinearly in its input.
  A stdout slope close to the peak-RSS slope points at output-driven memory; one well below it points at the algorithms.
  The TOML output carries the table as `[[ladder.step]]`, each measurement as `ladder.wall_seconds`, `ladder.peak_rss_kib`, and `ladder.stdout_bytes` with its `fit`, `top_slope`, and `top_params`, and the mark as `ladder.memory_marked`.
- Staleness: every row records the index commit.
  `--check` takes the site files of each listed algorithm (its anchor and sites) from the `graph.toml` beside a receipt's join, which is the graph at the receipt commit, runs `git diff --name-only <commit> -- <files>` in the checkout named by `--root`, prints the algorithms with a changed file, and exits 1 when there is one.
  A change outside the site files, such as in a callee or in a representation the algorithm reads, is not detected.
- Nesting: each workload table is followed by an indented outline of the nesting observed on that run, built from the join's `observed_nest` edges.
  It is not a declared relation: a child under a parent means the child's span opened while the parent's span was open on the same thread, and algorithms without spans do not appear.
  With repeats, the outline uses the first repeat's edges and states whether every repeat has the same edges.
  Roots are algorithms with a positive span count and no observed parent other than themselves; an algorithm reachable only through a cycle is added as a root.
  Children are ordered by decreasing median total-seconds share of span time, and each line reads `id — nested N× — total X % — self Y %`, with the span count for a root.
  Nesting of an algorithm inside itself is a `(recursive, N×)` note, not a child.
  An algorithm with several parents appears in full under the parent with the largest nest count and as `= id` under the others; `^ id (cycle)` marks a child that is already an ancestor on the path.
  Children and roots below 0.5 % total share are folded into a `+k more (Z %)` line.
  The TOML output carries the same outline as `[[workload.nesting.line]]` entries with their depth.

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
files = ["crates/k-rust-backend/src/term/names.rs"]
classification = "responsibility-only"
reason = "naming vocabulary of the shared term representation; term.rs has the primary card backend.term.macro_or_alias, and its constructor invariants are on its representation card, representation.backend.term"

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
files = ["crates/k-rust/src/native.rs"]
classification = "responsibility-only"
reason = "runnable-artifact write and load; the JSON encoding it calls is a site of definition.json.encode"

[[without_primary_card]]
files = ["crates/k-rust/src/definition/synonyms.rs"]
classification = "responsibility-only"
reason = "the apply-sort-synonyms load phase: a resolve, one pass over local productions, and an update, each carried by definition.resolve.imports"

[[without_primary_card]]
files = ["crates/k-rust/src/outer/mod.rs"]
classification = "responsibility-only"
reason = "outer-syntax module index and re-exports; each outer algorithm declares its card in its implementation module"

[[without_primary_card]]
files = [
  "crates/k-rust/src/bison/mod.rs",
  "crates/k-rust/src/bison/scanner.rs",
  "crates/k-rust/src/bison/toolchain.rs",
]
classification = "responsibility-only"
reason = "Bison export driver, scanner rendering and toolchain invocation; the two exporter algorithms are declared in bison/grammar.rs"

[[without_primary_card]]
files = [
  "crates/k-rust/src/definition/ast.rs",
  "crates/k-rust/src/definition/attribute_keys.rs",
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

Stage-table phases whose transformation is a linear rewrite with no worklist and no counter of its own are phase-only; the pipeline phase node is their only graph presence:

```toml
[[phase_only_stage]]
stage = "resolve commutative rules"
call = "resolve_comm"
file = "crates/k-rust/src/kompile/passes.rs"
reason = "duplicates each comm-attributed rule with its arguments swapped; one clone per rule"

[[phase_only_stage]]
stage = "resolve function configuration"
call = "resolve_function_with_config"
file = "crates/k-rust/src/kompile/passes/resolve_function_with_config.rs"
reason = "threads the generated top-cell configuration through functions that inspect it; one pass over rules"

[[phase_only_stage]]
stage = "resolve anonymous variables"
call = "resolve_anon_vars"
file = "crates/k-rust/src/kompile/passes/resolve_anon_vars.rs"
reason = "gives every anonymous variable a sentence-local name; one pass over terms with kompile.fresh_names.mint"

[[phase_only_stage]]
stage = "resolve heat/cool attributes"
call = "resolve_heat_cool_attributes"
file = "crates/k-rust/src/kompile/passes/resolve_heat_cool.rs"
reason = "lowers heat and cool attributes into side conditions; one pass over rules"

[[phase_only_stage]]
stage = "resolve semantic casts"
call = "resolve_semantic_casts"
file = "crates/k-rust/src/kompile/passes/resolve_semantic_casts.rs"
reason = "removes semantic-cast applications keeping their sorts; one pass over terms"

[[phase_only_stage]]
stage = "propagate macro attributes"
call = "propagate_macro_attributes"
file = "crates/k-rust/src/kompile/passes/propagate_macro.rs"
reason = "copies production macro kinds onto their rules; one pass over sentences"

[[phase_only_stage]]
stage = "guard or-patterns"
call = "guard_or_patterns"
file = "crates/k-rust/src/kompile/passes/guard_or_patterns.rs"
reason = "gives matching-logic disjunctions explicit aliases; one pass over rules"

[[phase_only_stage]]
stage = "resolve fresh configuration constants"
call = "resolve_fresh_config_constants"
file = "crates/k-rust/src/kompile/passes/resolve_fresh_config_constants.rs"
reason = "allocates integer constants for fresh configuration variables; one pass over configuration terms"

[[phase_only_stage]]
stage = "add implicit computation cell"
call = "add_implicit_computation_cell"
file = "crates/k-rust/src/kompile/passes/add_implicit_computation_cell.rs"
reason = "wraps cell-free sentences in the declared computation cell; one pass over sentences"

[[phase_only_stage]]
stage = "check simplification rules"
call = "check_simplification_rules"
file = "crates/k-rust/src/kompile/passes/check_simplification.rs"
reason = "validates simplification-rule heads; one pass over rules"

[[phase_only_stage]]
stage = "add semantics module"
call = "add_semantics_module"
file = "crates/k-rust/src/kompile/passes/finalize.rs"
reason = "module bookkeeping; no traversal of note"

[[phase_only_stage]]
stage = "resolve configuration variables"
call = "resolve_config_var"
file = "crates/k-rust/src/kompile/passes/resolve_function_with_config.rs"
reason = "one pass over configuration variables"

[[phase_only_stage]]
stage = "add cool-like attributes"
call = "add_cool_like_attributes"
file = "crates/k-rust/src/kompile/passes/finalize.rs"
reason = "attribute rewrite; one pass over rules"

[[phase_only_stage]]
stage = "remove units"
call = "remove_unit"
file = "crates/k-rust/src/kompile/passes/remove_unit.rs"
reason = "removes unit applications from associative collections; one pass over sentences"
```
