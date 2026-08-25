# M4 upstream reference-proof pins

This independent investigation freezes the ten upstream IMP claims not already
covered by M3D. It hash-checks the pinned K and IMP checkouts, proves the exact
set difference, builds a fresh Haskell IMP definition, runs every pending
claim separately, and delegates KAST-v4 normalization to the hash-pinned
`tests/m3d/verify.py` implementation.

Every proof is semantically bounded by the exact `depth` and
`branching_allowed` values in `cases.json`; `pins.json` independently freezes
the same policy and evidence-schema version. The wall-clock `--timeout` is
only an operational watchdog: a timeout is a failed run and is never a
pinnable proof status. Every external command starts in its own process
session. On a watchdog timeout the verifier terminates the whole session and
reaps its launcher, killing `kore-exec` and solver descendants with it. The
corpus stops immediately, preserving earlier evidence for an exact-identity
resume; it never continues past a watchdog failure or changes semantic bounds.

Verify the checked-in ledger:

```bash
PYTHONDONTWRITEBYTECODE=1 \
  python3 draft/investigations/m4-reference-proof-pins/verify.py
```

To independently regenerate a proposal and retain normalized JSON evidence:

```bash
PYTHONDONTWRITEBYTECODE=1 \
  python3 draft/investigations/m4-reference-proof-pins/verify.py \
    --write-proposal /tmp/m4-reference-pins.json \
    --artifacts /tmp/m4-reference-proof-artifacts
```

If a run stops, resume without repeating completed proofs:

```bash
PYTHONDONTWRITEBYTECODE=1 \
  python3 draft/investigations/m4-reference-proof-pins/verify.py \
    --write-proposal /tmp/m4-reference-pins.json \
    --artifacts /tmp/m4-reference-proof-artifacts \
    --reuse-artifacts
```

For a deliberately short investigation, advance one or more named cases and
retain a partial ledger without pretending it is a complete proposal:

```bash
PYTHONDONTWRITEBYTECODE=1 \
  python3 draft/investigations/m4-reference-proof-pins/verify.py \
    --artifacts /tmp/m4-reference-proof-artifacts \
    --reuse-artifacts \
    --case addition-2
```

Omit `--reuse-artifacts` only when creating a new/empty artifact directory.
Once all ten evidence entries exist, rerun without `--case` and with
`--write-proposal` to assemble the complete proposal.

Reuse is fail-closed. Each per-case evidence file embeds and hashes the exact K
and IMP revisions, source and normalizer hashes, selected claim, invocation
contract, and semantic bounds. The verifier re-normalizes the stored proof and
claim, recomputes its status, frontier count/hash, and hashes, and rejects any
stale or inconsistent cache entry. A missing entry is run normally; a
mismatched entry is not silently replaced.

The default verifier never edits pins. A proposal is only written when the
destination is explicitly supplied. Checked-in pins record proof status,
semantic bounds, normalized frontier count/hash, applied user labels when the
reference route exposes them, and normalized result/claim hashes. The pinned
KAST-v4 route does not expose applied-rule traces, so its reviewed
`user_labels` evidence is empty rather than inferred from terms. Pins never
record elapsed time or a watchdog timeout. Tool workspaces are
fresh and live under the system temporary directory. This investigation avoids
`/dev/shm`, which is shared with the Rust build lanes and may fill or empty
while a proof corpus is running.
