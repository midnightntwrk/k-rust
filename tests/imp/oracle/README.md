# IMP source, behavior, and proof oracle library

This directory holds the behavior and proof orchestration libraries of the complete IMP gate.
The root runner `tests/imp/verify.py`, `corpus.json`, and `pins.json` must supply the generated artifacts and the reviewed normalization tables.
Missing evidence must be an error; these modules must not fall back to an earlier fixture or another frontend route.

## Root integration API

The root runner must put `tests/` and this directory on `sys.path` and build krs-gate before comparing evidence.
Python must orchestrate tool execution, assemble policies from the pins, compare native observations, hash returned JSON, and report results.
KAST output must be read and normalized through k-rust's readers in krs-gate.

1. Compile upstream IMP and KRS-emitted K with the same pinned K frontend.
   Send one `kast.project` request for each of `parsed.json` and `compiled.json`, using file paths, the two pin policy tables, and the file's exact ignored and supplemental sentence multisets and compatible sentence pairs.
   These boundaries have different reviewed omissions and compatibility witnesses.
   The policies must enumerate selected modules, name maps and identities, known attributes, structured attribute-value mappings, and flattened sentence origins.
   Unknown structure must fail before behavior comparison.
2. Construct `behavior.Route` values from the compiled source definitions and the pin's term-policy side tables.
   Construct a `BehaviorPlan` from the checked corpus manifest and call `behavior.compare_behavior(k=..., workspace=..., gate=..., reference=..., actual=..., plan=...)`.
   `k` is the reference snapshot (`support.reference.Snapshot`) that replays or refreshes every `kast` and `krun` invocation; `workspace` must be a new directory inside the snapshot's workspace.
   The comparison must use one session for `kast.normalize` with the `behavior` variant and `kast.frontier` with the `search_set` action.
3. Construct one `proofs.ProofCase` per invocation with explicit `ProofBounds(depth, branching_allowed)`.
   The proof runner must own and terminate each complete process group on timeout.
   A timeout must be an error, never a pinned status.
   Pass kprove stdout and the emitted-spec path to `proofs.evidence_from_inputs` with the shared session and the assembled proof policy.
   It must call `kast.normalize` with `proof_result` and `proof_claim`, select the claim by label, and obtain status and frontier through `kast.frontier` with the `proof` action.
   The legacy pin must use the `static_proof` and `static_claim` variants through the same session.
4. Compare normalized claims and results, proved/failed/incomplete status, frontier states and constraints, semantic bounds, and applied user labels before checking pins.
   `ProofEvidence.pin()` must assemble the established pin shape from native observations.

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

A live (refresh) run of the LLVM failure routes requires `prlimit`.
They restore an unlimited soft address-space limit only for the LLVM interpreter because its collector reserves a sparse 2 TiB virtual region; the root gate may keep every resident-memory-heavy route under a soft `RLIMIT_AS` ceiling.

Each case has both its upstream module and KRS module.
The `behavior.term_policy` tables must map every KRS-generated label and sort to the upstream identity or list it as an explicit identity.
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

The Python orchestration tests must be tool-independent and must not launch a proof.
KAST reader, normalization, projection, and frontier tests must run in krs-gate.
