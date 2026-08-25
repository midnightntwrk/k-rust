# R2-G-02 accepted evidence

Status: pass on 19 August 2026 against K v7.1.337 at
`4a46d1231473b599c699160132fd6e76a5c46406`.

## Acceptance

Run from a checkout without a pre-existing patch replay output:

```sh
bun run r2:g:patch
```

The replay preserves the full R2-G-01 identity/rejection suite, compiles a
fresh W1-D in-process reference edit, applies the K-proposed input-relative
patch, and checks official Haskell lowering and execution. Three complete
oracle cycles passed; the last cycle binds the committed evidence to the final
transport, driver, runner, replay, normalizers, and W1-D oracle source hashes.

## Result

- K structurally selected `start => add(read(), bump())` and returned one
  `KDefinitionPatch-v1` edit. Its target path is rewrite-right; its replacement
  source is rewrite-right/application-argument 1.
- The trusted-small host validated the exact typed result, resolved both paths
  against the original official rule body, reused the original `bump` node,
  and rebuilt only official ancestors while preserving attributes.
- Exactly one rule was replaced and one source lineage changed content. The
  output is a new official `Definition`; lineage, sentence attributes,
  `requires`, `ensures`, module count, and sentence count were preserved.
- Focused normalized Kore equals the freshly generated W1-D reference, differs
  from baseline, contains `Lblbump`, and contains no `Lbladd`, `Lblread`, or
  stale `#Configuration` binder. Runtime is `<k> 0` and `<state> 2`.
- Stale target content and the recognized-but-unsupported `dSequenceItem(0)`
  path step were rejected at `post-k-patch-pre-apply`, with zero applications
  and no backend artifacts.

## Boundary retained

The only new shared contract is `KDefinitionPatch-v1`. It supports one
input-relative term replacement in one existing rule, with rewrite and
application-argument navigation. It does not define synthetic terms,
multi-edit atomicity, overlap behavior, insertion, deletion, condition or
attribute edits, general `SemanticInput`, pre-CF augmentation, or C1/C2 work.

The packet's only interpretation choice was that application-argument indices
are zero-based, so index `1` denotes the second `add` argument. The compact,
source-bound machine result is `results.json`; generated compiler trees,
records, projections, checksums, and logs remain under the ignored build path.
