# IMP static semantics independent static and proof oracle

This package is a functional reconstruction of the independent IMP static semantics oracle
lost with the failed disk. The original file hashes are retained in the
`reconstruction` table of `pins.json`; none of the reconstructed files claims
byte identity.

The oracle reads the KAST JSON output of the pinned K command-line tools through k-rust's reader in krs-gate.
Its independence rests on Java K having produced that output independently of KRS-generated artifacts:
by default the verifier replays the Java K results recorded in `reference/oracle/`,
and `--refresh-reference` runs the pinned K tools live and re-records them.
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

By default the verifier needs no K tool.
It replays the recorded `kompile`, `krun`, and `kprove` invocations in `reference/oracle/`,
including each proof's `--emit-json-spec` output.
Their `manifest.toml` holds the snapshot key
(the `Krs.lock` K version, the K tools, the upstream IMP commit, and the digest of every corpus and fixture file)
and the digest of every stored file.
A changed input, K version, upstream commit, or argument vector fails closed and names `--refresh-reference`;
the verifier never falls back to running Java K.
The upstream IMP checkout must still be clean at its pinned commit.

To re-record the snapshot, put the pinned K 7.1.337 `bin` directory on `PATH` and run the verifier with `--refresh-reference`.
The refresh also requires the K source checkout at the `Krs.lock` commit,
reruns every recorded invocation live, and rewrites `reference/oracle/` only when every check passes.
`--record` rewrites output pins in `pins.json`; it is independent of `--refresh-reference`, and the two may be combined.

The verifier must own fresh disposable compilation/proof workspaces and treat a timeout, unknown KAST node, unclassified proof exit, or pin difference as a failure.
