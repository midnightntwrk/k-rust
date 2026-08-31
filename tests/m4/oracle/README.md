# M4 source, behavior, and proof oracle library

This directory is Lane B of the M4 complete-IMP gate.  It is deliberately a
library: the root-owned `tests/m4/verify.py`, `corpus.json`, and `pins.json`
must supply the generated artifacts and the reviewed normalization tables.
Missing evidence is an error; none of these modules falls back to an earlier
fixture or another frontend route.

## Root integration API

Import the three modules from `tests.m4.oracle` (or put this directory on
`sys.path` for a directly loaded runner).

1. Call `behavior.load_frozen_helpers(ROOT)` before compiling M4.  It checks
   the exact reviewed hashes of all four M3 verifier modules.  The optional
   `run_frozen_behavior_gates(ROOT)` entry point runs only bounded M3A--M3C;
   it intentionally refuses M3D because that script launches proofs.
2. Compile upstream IMP and KRS-emitted K with the same pinned K frontend.
   Call `source_definition.compare_definitions` independently for
   `parsed.json` and `compiled.json`, because the reviewed exact-count
   omissions and exact reference/actual sentence pairs differ at those two
   frontend boundaries. Each
   `ProjectionPolicy` must enumerate selected modules, every label/sort/name
   identity or mapping, every known attribute, any explicit structured
   attribute-value mapping (for example a renamed `seqstrict` alias), and
   sentence origins for a flattened module.  Unknown structure fails before
   behavior.
3. Construct `behavior.Route` values for the two compiled source definitions
   and one `BehaviorPlan` from the checked corpus manifest.  Call
   `behavior.compare_behavior(kast=..., krun=..., reference=..., actual=...,
   plan=...)`.
4. Construct one `proofs.ProofCase` per invocation.  Every case requires an
   explicit `ProofBounds(depth, branching_allowed)`; there is no unbounded
   constructor.  `run_bounded_source_proof` owns and terminates a complete
   process group on timeout.  A timeout is an error, never a pinned status.
   Native/external proof consumers can instead construct evidence with
   `evidence_from_values`.
5. Call `proofs.compare_proof_evidence(reference, actual,
   pins["proof_outcomes"])`.  It compares the normalized claim, full result,
   proved/failed/incomplete status, frontier states and constraints, semantic
   bounds, and representative applied user labels before checking pins.

`proofs.verify_m3d_selected_pins` additionally requires exact legacy outcomes
computed with the hash-checked M3D normalizer.  It covers the six individually
frozen invocations.  The old `static-adjunct` hash represents five claims in
one module, so root must add five per-claim M4 pins; this library does not
pretend that the aggregate pin selects them independently.

## Required root-owned corpus wiring

`corpus.json` should construct these cases without copying source files:

- 22 accepted parse cases: M3A 9, M3B 5, M3C 8;
- all accepted concrete executions plus M3A's two parsed-but-stuck cases,
  M3B's two stuck cases, M3C's three stuck cases, and M3D static evaluation;
- 238 existing M3B/M3C depth states plus the eight bounded infinite-loop
  states (`run_to_completion=False` for the loop);
- the eight finite M3C search frontiers and eight bounded infinite-loop search
  frontiers (each search depth must also have a direct depth state);
- all eight syntax rejections with exact class and four-coordinate range; and
- division by zero as a `FailureCase` with the exact frozen
  `[hook_INT_tdiv]: Division by zero: 1 / 0` fragment.

The LLVM failure routes require `prlimit`.
They restore an unlimited soft address-space limit only for the LLVM interpreter because its collector reserves a sparse 2 TiB virtual region; the root gate may keep every resident-memory-heavy route under a soft `RLIMIT_AS` ceiling.

Each case needs both its upstream module and KRS module.  `TermPolicy` must map
every KRS-generated label/sort to the upstream identity; identities are also
explicit. Unparse differences are permitted only as complete, case-named
reference/actual strings. This includes the existing M3A unary-binding
round-trip exception and the exact `m3dZero` spelling differences; no generic
whitespace or token rewrite is allowed.

## Required root-owned proof wiring

`pins.json` needs one expanded pin in the exact shape returned by
`ProofEvidence.pin()` for all 20 unique claims (15 upstream plus five adjunct
claims).  `addition-depth-zero` is an additional invocation of `addition-1`,
not another claim.  The root proof harness must provide applied user labels;
empty labels are valid only when the reviewed reference evidence also has
none.

All 20 unique claim outcomes (15 upstream plus five split adjunct claims) are
now pinned from exact-identity evidence produced under deterministic
depth/branch bounds.  The harness compares all 21 invocations independently
across the reference source, projected source, dry-run specification, and
native Haskell routes.  The five expected incomplete outcomes are accepted
only after their parsed residual patterns match structurally; exit status or
wall-clock timeout is never proof evidence.  Process-session cleanup remains
mandatory, and every timeout is an error.

## Fast validation

```bash
PYTHONDONTWRITEBYTECODE=1 \
python3 -m unittest discover -s tests/m4/oracle -p 'test_*.py' -v
```

The tests are tool-independent and do not launch any proof.
