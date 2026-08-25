# R13: Stable proc-macro source provenance

## Question and result

Can the Rust-hosted architecture recover precise provenance for an attribute
argument path, refutable rule parameter pattern/type, nested body path, and a
function-like macro payload while remaining on stable rustc 1.97.1?

**Yes, with a required distinction between expansion-time anchors and final
serialized byte ranges.** Stable `proc_macro` exposes enough file and endpoint
information to anchor every requested authored token. It does not expose a
stable byte-range API, multi-span join, or expansion-parent/source traversal.
Raw spans also cannot leave the proc-macro process. The production design
should snapshot stable line/column anchors in `HostDescriptor`, then use a
shared-parser provenance pass over the exact package source to create
content-addressed, package-relative byte `SourceRange`s and explicit origin
stacks.

The source-provenance portion of the M0 gate is therefore **PASS**, provided
that the provenance materialization pass described below is part of M0. It is
**FAIL** if production attempts to serialize `proc_macro2::Span::byte_range()`
or treats `file!()/line!()/column!()` on a generated descriptor as the authored
nested range.

The executable spike is in
[`spikes/span-provenance/`](../../spikes/span-provenance/).

## Stable API boundary on rustc 1.97.1

The following is the observed and compiled API boundary. The stability
attributes in the installed 1.97.1 `proc_macro` source agree with the probe.

| API | Stable behavior at expansion time |
|---|---|
| `Span::start`, `end`, `line`, `column` | Available since 1.88. Endpoints are usable. Direct `proc_macro` lines and columns are one-based. Columns count Unicode scalar values, not bytes. |
| `Span::file` | Stable display/remapped filename. It need not be a filesystem path. |
| `Span::local_file` | Stable actual local path when available. It is deliberately unsuitable for serialized/reproducible output. |
| `Span::source_text` | Stable, best-effort source text for a real source span. Its documentation limits it to diagnostics and says macro output must not depend on it. |
| `TokenTree::span`, `Group::span_open`, `span_close` | Stable leaf and delimiter anchors. First/last leaf endpoints recover multi-token parsed-node bounds without `join`. |
| `Span::call_site`, `mixed_site`, `resolved_at`, `located_at` | Stable hygiene/location construction. These do not reveal an expansion origin chain. |
| `Span::byte_range`, `join`, `parent`, `source` | Unstable `proc_macro_span` APIs. The rejected fixture produces four E0658 diagnostics on stable 1.97.1. |

For `proc_macro2` 1.0.107 with `span-locations` enabled:

- `start`, `end`, `file`, and `local_file` forward the stable compiler data on
  rustc 1.88 and newer;
- its `LineColumn` uses one-based lines and zero-based Unicode-scalar columns,
  unlike direct `proc_macro::Span::column`;
- `source_text` forwards the same best-effort facility;
- `byte_range()` returned `0..0` for every probed endpoint; and
- `join()` returned `None` for every probed multi-token range because the
  underlying compiler APIs remain unstable.

The safest macro implementation is to parse with `syn`/`krs-syntax`, retain
leaf spans, and unwrap only the selected endpoint spans to the direct stable
`proc_macro` API when taking the anchor snapshot. `syn::spanned::Spanned` on a
large node must not be assumed to produce a full range on stable: its attempted
joins can degrade to a first-token span.

## What the spike proves

The accepted fixture deliberately consumes a Rust-invalid refutable function
parameter before rustc's irrefutability check, as the R12 prototype does. Its
generated runtime-safe descriptor contains scalar snapshots for:

| Probe target | Recovered source slice |
|---|---|
| Attribute argument path | `model::Expr` |
| Refutable parameter pattern | `model::Foo(value)` |
| Parameter type | `model::Term<dyn model::Expr>` |
| Nested body path | `model::nested::Bar` |
| Function-like macro payload path | `model::nested::Bar` |

All five ranges are reconstructed exactly from first-token start and last-token
end anchors. The nested-body line places the non-ASCII identifier `日本` before
the selected path. A naïve byte-column conversion selected the wrong slice;
Unicode-scalar-to-byte indexing selected the exact path. This makes dependence
on the exact source snapshot observable rather than theoretical.

The macro embeds only ordinary descriptor values: display filename, a boolean
recording whether a local file existed, endpoint numbers, and best-effort leaf
text. These survive into a `static` and runtime. The `proc_macro::Span` itself,
its hygiene context, its local absolute path, and any implicit expansion chain
do not survive. KRS must construct the origin stack explicitly as descriptors
are transformed.

The rejected syntax fixture produces an invocation-local primary range exactly
covering the invalid string literal in:

```rust
#[probe(path = "not a Rust path")]
```

Cargo's JSON diagnostic reports byte range `123..140`, line 6, columns 16..33.
This confirms that authored spans remain the right mechanism for immediate
macro syntax/type-shape diagnostics even though final provenance is later
materialized independently.

## rust-analyzer span mapping

The LSP probe asks go-to-definition on the same payload path under three macro
expansions:

1. one authored-spanned expansion use;
2. two expansion uses carrying the duplicated authored spans; and
3. one authored-spanned use plus one duplicate reparsed with call-site spans.

On rust-analyzer 1.97.1 all three returned exactly one definition target and
the authored document had no diagnostics. Thus a small same-symbol duplicate
does **not** deterministically break go-to-definition in this version. This
does not invalidate R12's broader observation that repeating authored spans
across a descriptor, hidden check, and `stringify!` made navigation ambiguous
or intermittent; it narrows the claim. Duplicate authored-span behavior is an
implementation detail, not something KRS can use as an ABI guarantee.

Production should retain the R12 rule:

- emit each authored token at exactly one meaningful, type-checking expansion
  position;
- give generated spelling/type-check duplicates call-site locations; and
- golden-test diagnostics, definition, hover, and rename on the representative
  production expansions, not only this minimal path macro.

The call-site-duplicate strategy preserved the same successful navigation in
this probe and gives rust-analyzer an unambiguous source-to-expansion mapping.

## Production capture and materialization strategy

### Expansion-time anchor

`HostDescriptor` should carry a non-final anchor for every parsed semantic
node, resembling:

```text
SourceAnchor {
  stable_item_id,
  origin_kind,             // attribute, rule pattern/type/body, macro payload
  display_file,
  start_line, start_scalar_column,
  end_line, end_scalar_column,
  invocation_ordinal,
  token_fingerprint,       // validation hint, never semantic input
}
```

Use the first and last authored leaf/delimiter spans selected by the shared
parser. Capture the macro invocation as a separate origin frame. Never embed
`local_file()`, depend semantically on `source_text()`, or place a raw Span in a
registration. A synthesized node without a direct authored token inherits an
explicit invocation or parent-node frame rather than a fabricated authored
range.

### Shared-parser provenance pass

Before `DescriptorBundle` serialization, the host collector/compiler should:

1. resolve the source through Cargo package identity and normalized
   package-relative paths, not through the embedded local absolute path;
2. read and content-hash the exact source, producing `SourceFileId`;
3. reparse the relevant attribute/rule/macro payload with `krs-syntax` (and the
   Rust outer item parser used by the macro), keyed by `StableItemId`, origin
   kind, and invocation ordinal;
4. take byte offsets from that parse and validate them against the captured
   line/scalar-column anchor and token fingerprint; and
5. emit final `SourceRange { file_id, byte_start, byte_end }` values.

Line-index conversion alone recovered this controlled fixture, so reparsing is
not mathematically necessary for a direct-source token if the exact source is
already trusted. It is nevertheless required for the production contract: it
supplies deterministic content identity, multi-token semantic-node matching,
payload-parser agreement, and a failure mode for stale/remapped/generated
anchors. This remains a provenance pass, not a second semantic frontend.

### Explicit origin stack

Every later transform appends a typed frame instead of trying to recover rustc's
unstable macro parent chain:

```text
Authored(SourceRange)
  -> Invocation(SourceRange, macro kind)
  -> Descriptor(StableItemId, field)
  -> SemanticIr(node id)
  -> DefinitionIr(sentence/term id)
  -> GeneratedArtifact or FrontendDiagnostic(range/code)
```

Generated `.k`, KORE/frontend source maps, and diagnostics should point at the
most specific authored frame and retain the remaining frames as trace/context.

## Reproduction and results

From `spikes/span-provenance`:

```sh
python3 tools/verify.py
```

The verifier checks the compiler version before running:

```text
rustc 1.97.1 (8bab26f4f 2026-07-14)
cargo fmt --all -- --check                         PASS
cargo clippy --workspace --all-targets -D warnings PASS
cargo test --workspace                            PASS (5 exact ranges)
cargo check fixtures/rejected                     expected failure; diagnostic PASS
cargo check fixtures/unstable-api                 expected failure; 4 x E0658 PASS
rust-analyzer 1.97.1 LSP probe                    3/3 definition probes PASS
```

The machine's version-named rustup alias was incomplete, while its `stable`
channel is exactly 1.97.1. `rust-toolchain.toml` selects `stable`, and the
verifier refuses to proceed unless the resolved compiler starts with
`rustc 1.97.1`.

## Remaining risks and gates

- `file()` may be remapped or artificial; `local_file()` may be absent and
  must never leak into reproducible artifacts.
- `source_text()` is explicitly best-effort. It is suitable for validating a
  diagnostic anchor, not for descriptor meaning or stable identity.
- A source change between expansion and collection must fail content/anchor
  validation and cause a rebuild, never silently shift a byte range.
- Stable Rust cannot traverse `parent()`/`source()` for input originating in
  another macro expansion. Such cases need an invocation-level fallback and an
  explicit diagnostic until the provenance pass can match authored source.
- Endpoint composition is valid only when both leaves resolve to the same
  source file and ordered range; the materialization pass must validate this.
- rust-analyzer mappings are not a language guarantee. The production macro
  shapes and each supported rust-analyzer upgrade need golden LSP tests.
- The captured columns are Unicode-scalar columns, whereas LSP positions use
  negotiated encodings (commonly UTF-16). Source-map and editor adapters must
  convert from byte ranges using the exact file text rather than reuse compiler
  column numbers.
