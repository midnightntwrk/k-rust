# K-in-k2 recovery provenance

This directory is an extraction-ready forensic reconstruction assembled without
mounting or modifying the source VHDX.

## Recovered contents

- 618 files total (about 4.9 MiB on the recovery host).
- The 473-file `investigations/backend-agnostic-goal-closure/` subtree is an
  exact reconstruction of the final state captured by the original agent
  session on 2026-08-22.
- The remaining 145 files are the previously verified transcript and
  user-artifact reconstruction: task packets, root package and probes, drafts,
  and definition-transport/spine evidence.

## Exact investigation reconstruction

Two deleted live `/tmp` copies of the investigation were recovered directly
from ext4 inodes. At `2026-08-22T18:32:38.705Z`, the original session recorded
that `/tmp/tmp.F0VytmbktF` was byte-identical to the live investigation after
excluding interpreter caches. That checkpoint supplied all file baselines.

The 47 later successful structured FileChange events were replayed in timestamp
order with exact unified-diff application. The investigation's deterministic
`refresh_fixture_ids.py` was then run. All 473 resulting files match the final
per-file SHA-256 ledger captured by the original session at
`2026-08-22T19:43:06.666Z`.

Reproducible replay inputs, script, mutation ledger, and both SHA-256 ledgers
are under `../evidence/k-in-k2-final-replay/`. The earlier 83-file reconstruction
was retained under `../evidence/k-in-k2-replaced-investigation/`.

## Verification

- 473 / 473 investigation files match the captured final-session SHA-256
  ledger byte-for-byte.
- 438 / 438 JSON and JSONL files parse.
- 4 / 4 Python files compile without writing bytecode.
- 2 / 2 shell files pass `bash -n`.
- `bun test oracle/test p1/test p2/test p3/test`: 10 pass, 0 fail when run from
  the extraction-ready tree with the recovered sibling `k-framework-ts`
  checkout available.
- An isolated copy without that external sibling gives the expected 9 passes
  and one module-resolution error in P3.
- The original session recorded successful `verify.py` and
  `verify.py --official-only` runs after the final hash checkpoint. On the
  recovery Mac, rerunning those two commands requires the unavailable official
  Draft 2020-12 `jsonschema` Python dependency; this is an environment gap, not
  a recovered-content failure.

The complete extraction identity ledger is
`../evidence/k-in-k2-extract-ready-identities.tsv` (SHA-256
`9693ed43ee372165b38f927a4e16e867be0c526b8438bc42c222015e9616bd9d`).

## Remaining uncertainty

The exact-final proof applies to the 473-file backend investigation. Outside
that subtree, three spine paths still lack captured baselines and two shared
draft histories remain divergent. Those unresolved variants were not guessed
or promoted.
