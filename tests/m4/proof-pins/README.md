# Reference-proof ledgers

These three ledgers record where M4's 21 reference-proof outcomes came from.
Each was produced by a separate investigation against the pinned K and IMP
checkouts:

- `selected/pins.json`: the six invocations M3D had selected (`addition-1`,
  `addition-var`, `branching`, `sum-loop`, `sum-spec`, and a depth-0
  `addition-depth-zero`), upgraded to the M4 proof-evidence contract;
- `reference/pins.json`: the ten upstream IMP claims M3D did not cover;
- `adjunct/pins.json`: the five M3D static-adjunct claims
  (`tests/m3d/claims/static-spec.k`), each proved on its own.

The ledgers are frozen provenance. `tests/m4/verify.py` checks each one against
its `proof_ledgers` hash in `../pins.json` and requires it to be non-empty. The
M4 proof phase then proves all 21 invocations again from `../pins.json`
`proof_outcomes`, so the gate does not rely on the ledgers' own evidence.

The scripts that generated the ledgers are retired, because they pinned the
M3D pin ledger and normalizer as they were before the M3D reconstruction.
To change a proof outcome, update `../pins.json` `proof_outcomes` and rerun M4.
