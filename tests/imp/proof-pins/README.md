# Reference-proof ledgers

These three ledgers record where IMP's 21 reference-proof outcomes came from.
Each was produced by a separate investigation against the pinned K and IMP
checkouts:

- `selected/pins.json`: the six invocations IMP static semantics had selected (`addition-1`,
  `addition-var`, `branching`, `sum-loop`, `sum-spec`, and a depth-0
  `addition-depth-zero`), upgraded to the IMP proof-evidence contract;
- `reference/pins.json`: the ten upstream IMP claims IMP static semantics did not cover;
- `adjunct/pins.json`: the five IMP static semantics static-adjunct claims
  (`tests/imp_static_semantics/claims/static-spec.k`), each proved on its own.

The ledgers are frozen provenance; `tests/imp/verify.py` does not read them.
Their pre-reconstruction hashes identify historical blobs, not the files at the current paths.
The IMP proof phase proves all 21 invocations from `../pins.json`
`proof_outcomes`, so the gate does not rely on the ledgers' own evidence.

The scripts that generated the ledgers are retired, because they pinned the
IMP static semantics pin ledger and normalizer as they were before the IMP static semantics reconstruction.
To change a proof outcome, update `../pins.json` `proof_outcomes` and rerun IMP.
