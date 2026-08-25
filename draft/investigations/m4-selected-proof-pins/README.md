# M4 selected reference-proof pins

This investigation upgrades the six proof invocations selected by M3D to the
expanded M4 `ProofEvidence.pin()` contract. It proves the exact upstream IMP
claims from the exact upstream definition: `addition-1`, `addition-var`,
`branching`, `sum-loop`, and `sum-spec` at depth 100, plus a distinct
`addition-depth-zero` invocation of the same `addition-1` claim at depth 0.
Every invocation uses `branching_allowed = 64`.

The verifier hash-checks the K and IMP revisions, all used upstream sources,
the frozen M3D normalizer and pin ledger, and every legacy M3D result/claim hash. Legacy
`frontier` maps only to M4's `incomplete` status. The depth-zero result must
retain a non-empty normalized residual frontier and its complete normalized
result must retain the legacy result hash. The five ordinary proofs must have
empty frontiers and retain their legacy `proved` statuses and hashes.

Every external command starts in a fresh process session. The wall-clock
timeout is only a watchdog: on expiry the verifier terminates and reaps the
whole session, including Java, `kore-exec`, and solver descendants, then fails.
A timeout can never become proof status or pin data. Semantic termination is
controlled only by the explicit depth and branch bounds in `cases.json`.

Verify all six checked-in pins from fresh `/tmp` artifacts:

```bash
PYTHONDONTWRITEBYTECODE=1 \
  python3 draft/investigations/m4-selected-proof-pins/verify.py
```

Independently regenerate a reviewable proposal and retain the normalized
claim/results:

```bash
PYTHONDONTWRITEBYTECODE=1 \
  python3 draft/investigations/m4-selected-proof-pins/verify.py \
  --write-proposal /tmp/m4-selected-proof-pins.json \
  --artifacts /tmp/m4-selected-proof-artifacts
```

The default command never writes project files. `pins.json` proof outcomes
have exactly the fields emitted by `tests/m4/oracle/proofs.py`'s
`ProofEvidence.pin()`: status, bounds, frontier count/hash, user labels, and
normalized result/claim hashes. The reference JSON route has no reviewed
applied-rule trace, so `user_labels` is intentionally empty rather than
inferred.
