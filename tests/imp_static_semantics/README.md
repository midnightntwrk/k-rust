# IMP static semantics independent static and proof oracle

This package is a functional reconstruction of the independent IMP static semantics oracle
lost with the failed disk. The original file hashes are retained in the
`reconstruction` table of `pins.json`; none of the reconstructed files claims
byte identity.

The oracle reads the KAST JSON output of the pinned K command-line tools through k-rust's reader in krs-gate.
Its independence rests on Java K having produced that output independently of KRS-generated artifacts:
by default the verifier replays the Java K results of the reference snapshot `oracle` from the per-user reference cache,
and runs the pinned K tools live when the cache does not hold them or under `--refresh-reference`.
It layers a small static-form stress surface over the pinned upstream IMP definition and checks:

- total and partial functions and guarded equations;
- explicit equation priority;
- a static alias;
- a named context alias selected by `seqstrict`;
- concrete execution ending in `x = 6, y = 0`;
- the six upstream proof invocations inherited by the IMP gate; and
- five independently selected static-adjunct claims.

Run:

```bash
TMPDIR=/var/tmp PYTHONDONTWRITEBYTECODE=1 python3 tests/imp_static_semantics/verify.py
```

With a warm reference cache the verifier needs no K tool.
`pins.json` `reference_sha256.oracle` pins the manifest digest of the snapshot of its `kompile`, `krun`, and `kprove` invocations,
including each proof's `--emit-json-spec` output, and the verifier replays the cache entry stored under it
(`tests/support/reference.py`; `${XDG_CACHE_HOME:-~/.cache}/krs/reference-outputs/v1` by default).
The manifest holds the snapshot key
(the `Krs.lock` K version, the K tools, the upstream IMP commit, and the digest of every corpus and fixture file)
and the digest of every stored file.
A cached entry whose key or argument vectors differ from the current ones fails closed;
the verifier never falls back from a cached entry to running Java K.
The upstream IMP checkout must still be clean at its pinned commit.

When the cache does not hold the pinned entry, and under `--refresh-reference`, the verifier runs the pinned K 7.1.337 tools live,
from `KRS_K_BIN` or `PATH`; a live run also requires the K source checkout at the `Krs.lock` commit and fails closed naming a missing tool.
The live result must reproduce the pinned digest, and it is stored only when every check passes.
After an intended change to an input, the K version, or the upstream commit, run the verifier with `--refresh-reference --record`:
`--record` rewrites the output pins in `pins.json`, including `reference_sha256`.

The verifier must own fresh disposable compilation/proof workspaces and treat a timeout, unknown KAST node, unclassified proof exit, or pin difference as a failure.
