# IMP source, behavior, and proof oracle library

This directory holds the source, behavior, and proof comparison libraries of
the complete IMP gate.
It is deliberately a library: the root-owned `tests/imp/verify.py`,
`corpus.json`, and `pins.json` supply the generated artifacts and the reviewed
normalization tables.
Missing evidence is an error; none of these modules falls back to an earlier
fixture or another frontend route.

## Root integration API

Put `tests/` on `sys.path` (the modules import the shared `support`
package and `imp_static_semantics.normalize`), then import the three modules from
`tests.imp.oracle` or with this directory on `sys.path` for a directly loaded
runner.

1. Compile upstream IMP and KRS-emitted K with the same pinned K frontend.
   Call `source_definition.compare_definitions` independently for
   `parsed.json` and `compiled.json`, because the reviewed exact-count
   omissions and exact reference/actual sentence pairs differ at those two
   frontend boundaries. Each
   `ProjectionPolicy` must enumerate selected modules, every label/sort/name
   identity or mapping, every known attribute, any explicit structured
   attribute-value mapping (for example a renamed `seqstrict` alias), and
   sentence origins for a flattened module.  Unknown structure fails before
   behavior.
2. Construct `behavior.Route` values for the two compiled source definitions
   and one `BehaviorPlan` from the checked corpus manifest.  Call
   `behavior.compare_behavior(kast=..., krun=..., reference=..., actual=...,
   plan=...)`.
3. Construct one `proofs.ProofCase` per invocation.  Every case requires an
   explicit `ProofBounds(depth, branching_allowed)`; there is no unbounded
   constructor.  `run_bounded_source_proof` owns and terminates a complete
   process group on timeout.  A timeout is an error, never a pinned status.
   Native/external proof consumers can instead construct evidence with
   `evidence_from_values`.
4. Call `proofs.compare_proof_evidence(reference, actual,
   pins["proof_outcomes"])`.  It compares the normalized claim, full result,
   proved/failed/incomplete status, frontier states and constraints, semantic
   bounds, and representative applied user labels before checking pins.

## Corpus wiring

`behavior.plan_from_manifest` constructs these cases from `corpus.json`
without copying source files, and IMP.6 pins their counts in
`behavior.expected` of `pins.json`:

- 23 accepted parse cases: expression 9 plus the IMP-owned expression case,
  IMP state 5, and IMP control flow 8;
- all accepted concrete executions plus the expression corpus's two
  parsed-but-stuck cases, IMP state's two stuck cases, IMP control flow's
  three stuck cases, and IMP static semantics static evaluation;
- 238 IMP state and IMP control flow depth states plus the eight bounded
  infinite-loop states (`run_to_completion=False` for the loop);
- the eight finite IMP control flow search frontiers and eight bounded
  infinite-loop search frontiers (each search depth also has a direct depth
  state);
- all eight syntax rejections with exact class and four-coordinate range; and
- division by zero as a `FailureCase` with the exact frozen
  `[hook_INT_tdiv]: Division by zero: 1 / 0` fragment.

The LLVM failure routes require `prlimit`.
They restore an unlimited soft address-space limit only for the LLVM interpreter because its collector reserves a sparse 2 TiB virtual region; the root gate may keep every resident-memory-heavy route under a soft `RLIMIT_AS` ceiling.

Each case has both its upstream module and KRS module.
`TermPolicy` maps every KRS-generated label/sort to the upstream identity;
identities are also explicit.
Unparse differences are permitted only as complete, case-named
reference/actual strings.
This includes the expression unary-binding round-trip exception and the exact
`zeroAlias` spelling differences; no generic whitespace or token rewrite is
allowed.

## Proof wiring

`proof_outcomes` in `pins.json` holds one expanded pin in the exact shape
returned by `ProofEvidence.pin()` for each of the 21 invocations: the 20
unique claims (15 upstream plus five split adjunct claims) and
`addition-depth-zero`, an additional invocation of `addition-1`.
The pins come from exact-identity evidence produced under deterministic
depth/branch bounds.
IMP.7 compares all 21 invocations independently across the reference source,
projected source, dry-run specification, and native Haskell routes.
The root proof harness provides applied user labels; empty labels are valid
only when the reviewed reference evidence also has none.
The five expected incomplete outcomes are accepted only after their parsed
residual patterns match structurally; exit status or wall-clock timeout is
never proof evidence.
Process-session cleanup is mandatory, and every timeout is an error.

## Fast validation

```bash
PYTHONDONTWRITEBYTECODE=1 \
python3 -m unittest discover -s tests/imp/oracle -p 'test_*.py' -v
```

The tests are tool-independent and do not launch any proof.
