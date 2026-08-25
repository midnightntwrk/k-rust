# M4 static-adjunct reference-proof pins

This investigation closes the M3D aggregate-proof ambiguity by freezing the
five claims in `tests/m3d/claims/static-spec.k` as five independent reference
invocations:

- `total-equation`
- `partial-equation`
- `explicit-priority`
- `static-alias`
- `context-alias`

It compiles a fresh Haskell definition from the exact M3D
`static-adjunct.k`, selects exactly one fully qualified claim with `--claims`
per `kprove` invocation, and requires the emitted JSON spec to contain exactly
that one `KClaim`. Every invocation is semantically bounded at `depth=100` and
`branching_allowed=64`.

The verifier imports the exact hash-pinned `tests/m3d/verify.py` normalizer. It
also checks the exact M3D pin ledger, K and IMP Git revisions, the fixture and
claim-spec hashes, and the four transitive upstream IMP definition hashes used
by the fixture. This makes these new per-claim pins a refinement of the M3D
reference evidence rather than a second normalization contract.

Run the checked-in ledger with:

```bash
PYTHONDONTWRITEBYTECODE=1 \
  python3 draft/investigations/m4-adjunct-proof-pins/verify.py
```

Regenerate a review proposal and retain full normalized evidence outside the
repository with:

```bash
PYTHONDONTWRITEBYTECODE=1 \
  python3 draft/investigations/m4-adjunct-proof-pins/verify.py \
    --write-proposal /tmp/m4-adjunct-proof-pins.json \
    --artifacts /tmp/m4-adjunct-proof-evidence
```

`pins.json` uses the same semantic fields as
`tests/m4/oracle/proofs.py::ProofEvidence.pin`: status, explicit bounds,
frontier count/hash, user labels, and normalized result/claim hashes. The
normalization itself remains the exact frozen M3D normalization as required by
this reference investigation.

The reference `kprove --output json` route exposes a KAST-v4 proved/residual
term on stdout and the selected KAST-v4 claim module through
`--emit-json-spec`. Its stderr channel contains diagnostics; this invocation
does not request or expose an applied-rule trace. Consequently `user_labels`
is reviewed as empty for these pins. The verifier does not guess labels from
the claim, result terms, or diagnostic text.

The wall-clock timeout is only a safety watchdog. It is never converted into a
proof status or written to a pin. Every `kompile`, `kprove`, version, and Git
command owns a new process session. On timeout or interruption the verifier
terminates and reaps that whole session, including Java, `kore-exec`, solver,
and other descendants. All compilation and proof work lives in a fresh `/tmp`
directory.

Normalized evidence is intentionally not checked in: these five proofs are
fast and reproducible, while the reviewed hashes and exact regeneration
contract are compact. Passing `--artifacts` retains one self-describing JSON
evidence file per claim when an audit needs the normalized terms.
