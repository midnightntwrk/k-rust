# IMP static semantics independent static and proof oracle

This package is a functional reconstruction of the independent IMP static semantics oracle
lost with the failed disk. The original file hashes are retained in the
`reconstruction` table of `pins.json`; none of the reconstructed files claims
byte identity.

The oracle remains independent of KRS-generated artifacts. It layers a small
static-form stress surface over the pinned upstream IMP definition and checks:

- total and partial functions and guarded equations;
- explicit equation priority;
- a static alias;
- a named context alias selected by `seqstrict`;
- concrete execution ending in `x = 6, y = 0`;
- the six upstream proof invocations inherited by the IMP gate; and
- five independently selected static-adjunct claims.

Run under K 7.1.337:

```bash
TMPDIR=/var/tmp PYTHONDONTWRITEBYTECODE=1 python3 tests/imp_static_semantics/verify.py
```

The verifier owns fresh disposable compilation/proof workspaces and treats a
timeout, unknown KAST node, unclassified proof exit, or pin difference as a
failure.
