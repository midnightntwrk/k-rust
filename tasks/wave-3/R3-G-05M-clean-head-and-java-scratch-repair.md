# R3-G-05M: exact implementation head and Java nested scratch repair

Status: pre-cycle R3-G-05L audit repair. Clean implementation
`b2b78b4a07190fc3e387b5fcd24b933b2232e419` over L activation
`dfadc62bb090580a32f2b0f2a95e74eaefdd7e4d` passes the complete bounded
zero-backend suite. No total cycle 4 output exists and no substantive cycle was
consumed. Two fresh read-only audits rejected cycle-4 launch for the two narrow
gaps below. Preserve cycles 1 through 3 unchanged; total cycle 4 remains the
only authorized next raw attempt after this repair is accepted.

## Exact implementation-head authorization

L binds its activation and semantic input digest but does not bind the clean
implementation commit that root actually reviews and authorizes. Activation
ancestry alone permits a different descendant, and before/after repository
snapshot equality permits a checkout that began and ended dirty.

Add one required `R3_G_05_IMPLEMENTATION_HEAD` input for a non-test raw launch.
It must be an exact full commit object ID, must equal `git rev-parse HEAD`, and
must enter exact authorization material alongside the existing semantic digest,
output, resources, and total cycle count. Before reserving the fresh output,
refuse any staged change, tracked worktree change, or untracked non-ignored
path. Ignored failed/build outputs remain provenance and are not source dirt.

Carry the exact implementation head through raw success, accepted pins,
finalized JSON/Markdown evidence, and the verifier. Bind it to the before/after
repository snapshot head, prove the M activation is its ancestor, and require
the referenced commit object to exist. Verification from a later integrated
checkout must validate the recorded implementation revision without requiring
the current reporting checkout to remain at that revision.

Add zero-backend refusal cases for a mismatched requested head, a tracked
change, a staged change, and an untracked non-ignored file. Each must fail
before output reservation or raw execution and leave no cycle-4 directory.

## Separate stable Java scratch path

L correctly changes shell-visible compiler/backend outputs to the stable owner
path, but both unchanged Java `runK` helpers still create temporary K programs
under `recordPath.getParent()` and pass that immediate
`/proc/self/fd/<fd>/records/<temp>` spelling to nested `krun`:

- `RuleAppliedTraceDriver.java` around its `Files.createTempFile`/`runK` helper;
- `TraceConfigurationAugmentation.java` around the equivalent helper.

This is the same disappearing-self-FD class as cycle 3. Keep
`R3_G_05_RECORD` and all final record publication on the immediate inherited
descriptor path. Introduce a separately named, required task-local environment
binding for a stable owner-qualified scratch directory below the descriptor-
bound output, create that directory through the immediate secure path, and pass
the stable spelling into both Java helpers. Each helper must create, pass, and
delete its temporary `krun` input through only that stable scratch binding.
Do not derive nested arguments from the record path or fall back to a canonical
pathname.

The existing shell `run_nested_guarded` call around each driver invocation must
span the complete Java process and its internal synchronous `krun` calls, so
the same owner generation/device/inode pre/post checks reject every provisional
result on owner loss. Bind this production mapping in static acceptance: exact
stable scratch environment source, both Java consumers, both temp-file uses,
immediate-only record publication, and absence of `recordPath.getParent()` as a
nested scratch authority. Extend the zero-backend descriptor adversary ledger
or an equivalent bounded check to prove stable scratch and immediate record
spellings resolve to the same descriptor-bound tree while the final record path
never becomes owner-qualified.

## Binding, acceptance, and ownership

Bind this packet and its distinct activation everywhere L is bound: semantic
inputs, accepted pins, authorization material, ancestry/hash preflight, raw
success, final evidence, and verification. Retain exact total cycle count 4,
fresh `spine/rule-applied-allowlist/build/cycle-4-r3-g-05l`, all prior cycle
history, resource/session gates, and the complete zero-backend suite.

Worker write ownership is only `spine/rule-applied-allowlist/**` excluding
ignored raw build outputs. This packet, delivery-loop/checkpoint/roadmap/decision
records, package entries, evidence outside the task directory, lockfiles,
accepted artifacts, and external K are read-only. The worker may run Python,
shell syntax/static checks, and zero-backend tests only. Do not run Java,
`javac`, K, `kompile`, `krun`, `kore-exec`, any compiler/backend command, or the
raw oracle.

Return one clean repair commit and a newly recomputed semantic digest plus exact
cycle-4 authorization command. Stop rather than broaden semantics, weaken
publication, consume cycle 4, reuse a prior output, authorize total cycle 5, or
activate R3-G-06. Root will review the complete diff, commission fresh audits,
replay zero-backend acceptance, and alone decide whether the heavy-work and
live-resource gates permit cycle 4.
