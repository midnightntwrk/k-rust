# R3-G-05J: driver compilation and idempotent failure-recovery repair

Status: seventh R3-G-05 acceptance repair. The accepted zero-backend I
implementation is clean commit `014d77690977805d06b9d4a1c3a334afb0fd5678`
over activation `9bcb273863027af51a9381ecb02edace9a896adf`. Root's first
authorized substantive full-oracle cycle used the fresh ignored output
`build/cycle-1-r3-g-05i`, passed the resource/session gates and overlay
compilation, then failed during task-driver `javac` at `frontend-setup`. Preserve
that directory as failed cycle-1 provenance and never reuse or finalize it.

## Observed cycle-1 boundary

The failed output contains no K definition, Haskell backend, `compiled.bin`,
`definition.kore`, or `backend.txt`. Its authoritative terminal record is:

```json
{"schema":"R3-G-05-raw-failure-v1","stage":"frontend-setup","exitStatus":1}
```

`driver-javac.stderr` reports three unresolved calls to
`productionStructure(Production)`, from `Projection.encodeMeta`,
`ProductionDescriptor.capture`, and `GeneratedCellDescriptor.capture`. The
method exists, but is private inside sibling `TraceAdapter`, so it is not in
scope at those call sites. Because this compiler result drives the repair, the
substantive full-oracle count is one. At most two further substantive cycles
remain under the original cap.

Failure unwinding also attempted to publish the already committed
`raw-failure.json` from the raw-inner wrapper and outer launcher. The absent-only
publisher correctly preserved the first bytes, but both best-effort recovery
paths emitted `SecureIOError: marker already exists` tracebacks. Failure
recovery must recognize one already valid first-writer failure record without
overwriting, unlinking, or weakening malformed/symlink refusal.

## Compilation repair

Move the one canonical `productionStructure(Production)` helper to the outer
`RuleAppliedTraceDriver` scope, shared by `TraceAdapter`, `Projection`,
`ProductionDescriptor`, and `GeneratedCellDescriptor`. Do not duplicate the
helper or change its encoding. Add a zero-backend static witness that fails the
I layout: exactly one helper declaration must occur in outer scope before the
first nested `TraceAdapter` declaration, and the three consumers must remain.

Do not otherwise change K/Java semantic authority, mutation construction,
selection, ordering, term encoding, exact-existing validation, or the accepted
I process/session behavior.

## Idempotent failure recovery

Make repeated recovery publication idempotent only for an existing regular,
non-symlink, valid `R3-G-05-raw-failure-v1` object with a nonempty string stage
and integer exit status. The first writer remains authoritative. A second
recovery attempt may return successfully without changing bytes; it must not
replace, unlink, reinterpret as success, or emit a traceback.

An absent marker must still be committed through the existing kernel
no-replace publisher. A malformed record, symlink, directory, or other
non-regular target must still fail closed and remain byte-for-byte unchanged.
Retain success-only watchdog disarm, raw-success exclusion, two-phase outer
completion, and every secure first-writer adversary.

Extend bounded zero-backend tests to prove:

- two sequential recovery attempts leave one identical valid failure marker;
- inherited-option, resource-floor, and hard-kill wrapper failures do not print
  duplicate-marker tracebacks;
- malformed and symlink first writers remain refused and unchanged; and
- the existing concurrent absent-only publication adversaries still pass.

## Binding, audit, and next oracle

Bind this packet and its activation into semantic inputs, accepted pins, exact
raw authorization, raw success, final evidence, and verification. Retain every
R3-G-05 zero-backend suite and all I witnesses. Do not run Bun, K, Java,
`javac`, `kompile`, `krun`, a compiler/backend, or a raw oracle in the worker
repair. Do not edit K semantic source or external K.

Return one clean repair commit and the newly bound guarded command for a fresh
`build/cycle-2-r3-g-05j` output with cycle count 2. Root will review the full
diff, commission fresh read-only audits, recheck live resources and unrelated
K/Lean activity, and alone decide whether to authorize cycle 2.

## Ownership and stop rule

Ownership remains only `spine/rule-applied-allowlist/**`, owned R3-G-05
evidence, and the existing package entry. Do not edit this packet,
checkpoints/roadmaps/loop/decisions, accepted artifacts, lockfiles, or external
K. Stop rather than broaden beyond the compilation scope and failure-recovery
boundary, weaken exact first-writer publication, reuse cycle-1 output, exceed
three substantive cycles, or activate R3-G-06 before accepted R3-G-05 evidence.
