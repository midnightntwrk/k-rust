# R2-G-03 accepted evidence

Status: pass on 19 August 2026 against K v7.1.337 at
`4a46d1231473b599c699160132fd6e76a5c46406`.

## Acceptance

Run from a checkout without a pre-existing transaction replay output:

```sh
bun run r2:g:transaction
```

The replay first runs the complete R2-G-02 suite into fresh nested output,
which itself preserves R2-G-01. It then compiles the positive transaction
twice, exercises both P3 programs, and checks all three negative transactions.
One complete oracle cycle passed.

## Result

- K structurally discovers the `start => read() + bump` and variable-addition
  rules, authors two provenance-bearing `replaceTermFromInput` edits, and emits
  their complete canonical values in lexicographic order under
  `KDefinitionPatch-v2` / `p3-start-and-add-values@1`.
- The host verifies the order without reordering, validates both edits against
  the same original official `Definition`, resolves both replacement nodes,
  and only then invokes one immutable definition transformer. Exactly two
  applications and two changed source lineages result.
- Both rule lineages, sentence attributes, `requires`, and `ensures` remain
  unchanged while both content/body fingerprints and the definition
  fingerprint change. Module and sentence counts are unchanged, and the
  output is a new official `Definition` reference.
- The focused `start-program` Kore equals the R2-G-02 v1 patch projection. The
  focused `add-values` Kore differs from baseline and returns the second input
  variable. Ordinary `start` ends at `<k> 0` / `<state> 2`; the task-owned
  `1 + 2` fixture changes from baseline `<k> 3` to transaction `<k> 2`.
- Stale-first, stale-second, and duplicate-target transactions all reject at
  `post-k-transaction-pre-apply`, with zero applications,
  `outputConstructed: false`, and no backend artifacts. Stale-second records
  one validated edit, demonstrating that validation progress does not expose
  a partial output.
- Repeated proposals have the same canonical transaction fingerprint.

## Boundary retained

The only new shared contract is `KDefinitionPatch-v2`. It supports exactly two
input-relative replacements in two distinct existing rules using rewrite and
application-argument paths. It adds no same-rule overlap semantics, synthetic
terms, insertion, deletion, condition edits, attribute edits, observation
state, or C1/C2 work.

There was no packet ambiguity requiring a split. At the pre-backend seam,
typed source variables are represented under `#SemanticCastToInt`; the fixed
replacement path therefore reuses the original cast-wrapped second input term,
which lowers to that variable as required.

The recommended next work is the pre-CF observation/configuration-seam
investigation: determine whether the accepted post-CF adapter can be paired
with one narrow earlier augmentation seam, or whether the observation design
must change. General event or matcher implementation should wait for that
classification.
