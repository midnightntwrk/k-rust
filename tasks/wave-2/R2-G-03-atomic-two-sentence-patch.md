# R2-G-03: atomic two-sentence input-relative patch

Status: accepted and integrated as `daca204` on 19 August 2026. The activation
commit `21b05ed` was the worker's exact starting revision.

## Objective

Introduce exactly one shared contract, `KDefinitionPatch-v2`, and use it for
one K-authored P3 transaction containing two input-relative term edits rooted
in two distinct source rules. The trusted-small host must validate every edit
against the same original in-memory official `Definition` before constructing
an output, then apply both immutably as one all-or-none transaction before
official lowering.

This packet proves coupled atomicity. It does not add synthetic replacement
terms, new patch operation kinds, general overlap semantics, mutation
enumeration, observation instrumentation, or independent compilation.

## Starting inputs

- the activation commit containing this packet, descended from `c1605d2`;
- `tasks/wave-2/R2-G-02-single-sentence-patch.md` and its accepted evidence;
- `draft/k-in-k-r2-g-product-checkpoint-2026-08-19.md`;
- `draft/decisions/official-definition-adapter-v1.md`;
- `spine/definition-transport/**`;
- the P3 definition and ordinary `start` program; and
- K v7.1.337 at
  `4a46d1231473b599c699160132fd6e76a5c46406`, using the pinned Haskell-backend
  profile.

Record the exact activation revision in task-specific evidence.

## Contract fixed by this packet

`KDefinitionPatch-v2` retains the v1 input-relative
`replaceTermFromInput` operation and typed path vocabulary. Its envelope
contains:

- schema ID `KDefinitionPatch-v2`;
- transformation ID/version `p3-start-and-add-values@1`;
- expected input-definition fingerprint;
- exactly one transaction candidate;
- exactly two ordered edits; and
- for each edit, target lineage, expected target content/body fingerprints,
  typed target path, and typed replacement-source path.

Both edits resolve their replacement source from their own unmodified target
rule. Application-argument indices remain zero-based. The canonical edit order
is the lexicographic order of the complete canonical edit values beginning
with target lineage. K must emit that order and the host must verify it rather
than silently reorder K's result.

The host computes the canonical transaction fingerprint from the parsed v2
constructors and fields, independent of pretty-output whitespace. It accepts
one exact top-level typed result and rejects multiple or residual results.

## Positive transaction

K must structurally discover both edits without a Java label-specific
mutation:

1. In P3 `start => read() + bump`, replace the rewrite-right term with its
   rewrite-right/application-argument 1 subterm (`bump`).
2. In P3's variable-addition rule, replace the rewrite-right term with the
   rewrite-left/application-argument 1 subterm (the second input variable).

K may use sentence provenance to distinguish operator roles after structural
matching, but label equality alone is not a structural match. Java may
implement generic lookup, path validation/navigation, immutable replacement,
and transaction validation; it may not search for `start`, `add`, `read`,
`bump`, `+Int`, or choose either replacement.

Add one task-owned P3 program fixture below the spine that evaluates `1 + 2`.
The ordinary existing `start` program exercises the first edit; the new
program exercises the second.

## Required atomic behavior

1. Preserve the complete R2-G-01 and R2-G-02 acceptance suites, including v1
   patch behavior and all prior negative classifications.
2. Project through unchanged `KDefinitionTransport-v1` and invoke K to produce
   one exact `KDefinitionPatch-v2` result.
3. Validate schema, transformation, input definition fingerprint, transaction
   cardinality, edit cardinality, canonical order, distinct target lineages,
   supported path steps, non-negative/bounded indices, and both per-edit
   lineage/content/body preconditions against the original definition.
4. Resolve every target and replacement path against the original definition
   and prepare both replacements before constructing an output definition.
5. Reject duplicate targets. Because this packet requires distinct rules and
   one edit per rule, no general within-rule overlap algorithm is needed.
6. Only after all validation succeeds, build one new official `Definition`
   that applies both edits. Reuse the original official replacement nodes and
   preserve all ancestor, rule, condition, and sentence attributes.
7. Validate after application that:
   - application count is exactly two;
   - changed source-lineage count is exactly two;
   - both lineages, sentence attributes, `requires`, and `ensures` are
     preserved;
   - both target content/body fingerprints and the definition fingerprint
     change;
   - module and local-sentence counts remain equal; and
   - the output is a different official `Definition` reference.
8. Emit a record containing the canonical transaction/fingerprint, ordered
   per-edit values, validated-edit count, application count, changed-lineage
   count, `outputConstructed`, before/after fingerprints, and closest
   validation boundary.
9. Continue the positive transaction through official lowering, Haskell
   compilation, and both programs.

The host must never expose or retain a partially edited definition.

## Required negative transactions

K-authored modes or fixtures must return otherwise well-shaped v2 values for:

- stale content on the first edit;
- stale content on the second edit; and
- two edits that resolve to the same target lineage.

Each must fail at `post-k-transaction-pre-apply`, report application count
zero and `outputConstructed: false`, and emit none of `definition.kore`,
`syntaxDefinition.kore`, `macros.kore`, `backend.txt`, `compiled.bin`, or
`haskellDefinition.bin`.

The two stale cases are the atomicity oracle: failure of either member leaves
no output transaction. Do not implement rollback by applying one edit first;
validate all edits against the original before calling the transformer.

## Required positive oracles

The one deterministic acceptance command must first replay R2-G-02 into a
fresh nested output, then compile the v2 transaction. Require:

- the transaction's focused normalized `start-program` Kore equals the v1
  positive patch projection;
- the transaction's focused normalized `add-values` Kore differs from the
  official baseline and reflects replacement by the second input variable;
- syntax Kore and macros are byte-identical to the official baseline;
- ordinary `start` execution ends with `<k>` value `0` and `<state>` value
  `2`;
- the task-owned `1 + 2` program ends with `<k>` value `2`;
- baseline execution of that same program ends with `<k>` value `3`;
- the structured record satisfies every atomic/provenance invariant above;
  and
- repeated transaction proposal produces the same canonical transaction
  fingerprint.

The focused projection helper may be generalized to select a declared label,
but compiler output and source fixtures outside the owned spine remain
read-only.

## Owned paths

The worker may create or modify only:

- `spine/definition-transport/**`, including one small program fixture;
- `evidence/r2-g-03-atomic-two-sentence-patch/**`; and
- the single `r2:g:transaction` script entry in `package.json`.

The worker may inspect but not modify task packets, roadmap/checkpoint/loop
records, goals, existing R2-G-01/R2-G-02 evidence, investigations, existing
P1/P3 fixtures, official K, unrelated package entries, or other paths. Raw
compiler outputs remain below the already ignored spine build directory.

## Required outputs

- v2 K semantics plus generic Java validation/application under the owned
  spine;
- the task-owned `1 + 2` P3 program;
- one deterministic transaction replay;
- compact source-bound `report.md` and `results.json` under
  `evidence/r2-g-03-atomic-two-sentence-patch/`; and
- one clean worker commit containing task-owned changes only.

The worker return must state its commit, verdict, full-oracle cycle count,
tests, packet ambiguity, new contract, limitations, and the recommended
pre-CF observation-seam investigation.

## Acceptance command

The worker must add and pass:

```sh
bun run r2:g:transaction
```

The command must fail closed on missing tools, wrong K pin, pre-existing
output, or any mismatch. Also run:

```sh
bun run check
git diff --check
```

## Stop/split rule

Stop with preserved evidence rather than expanding if acceptance requires:

- another shared contract beyond `KDefinitionPatch-v2`;
- changing `KDefinitionTransport-v1` or breaking v1 patch compatibility;
- synthetic terms or a patch operation other than input-relative term
  replacement;
- more or fewer than two edits, same-rule multi-edit overlap semantics,
  insertion, deletion, condition edits, or attribute edits;
- Java structural recognition of the P3 mutation;
- source/KAST JSON round-tripping or official emitted `parsed.json` as input;
- fixture changes outside the owned spine;
- modifying official K, investigations, goals, task packets, or roadmaps;
- observation/configuration augmentation; or
- C1/C2 lowering, Kore emission, or parsing work.

After three substantive full-oracle cycles without acceptance, return the
smallest replayable blocker or split recommendation instead of a fourth cycle.
