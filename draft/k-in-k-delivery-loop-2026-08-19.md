# K-in-K packet delivery loop — 19 August 2026

Status: active execution protocol. This records the loop being used after
accepted `R2-G-01` so it survives conversation compaction. It is not a live
substitute for task packets, evidence, or the execution roadmap.

## Loop

For each bounded capability leaf:

1. The root selects the next dependency-unblocked leaf and writes an
   executable task packet.
2. The root commits the packet before delegation. The packet fixes the base
   revision, owned/read-only paths, one shared contract at most, fixtures,
   negative cases, acceptance command, and stop/split rule.
3. A fresh Sol worker implements the packet in an isolated Git worktree and
   returns one worker commit plus compact evidence.
4. The root reviews the complete diff, independently replays acceptance from
   the recorded base, and classifies the result as accepted, small repair,
   split/redesign, or blocked.
5. Only the root integrates the worker commit, updates roadmap/checkpoint
   state, and activates the next leaf.

The worker's completion report is not itself an integration decision.

“Independently replays” means the smallest fresh oracle that proves the new
leaf. It does not require recursively rebuilding every accepted ancestor.
Accepted ancestor evidence and source hashes are verified directly; only the
new or materially changed compiler/backend boundary is rerun.

## Context and ownership rules

Durable repository artifacts, rather than conversation history, carry the
contract. A worker receives the task path, activation commit, required ADRs,
and evidence references. Full historical context is unnecessary unless the
packet proves incomplete.

The worker exclusively owns its implementation directory and task-specific
evidence directory. The root retains the execution roadmap, this loop record,
shared orchestration records, integration status, and unrelated package
entries. A task may grant one narrow root-manifest entry when needed for its
acceptance command.

Only one implementation worker may change a shared schema at a time. After a
schema stabilizes, independent audit, replay, fixtures, or downstream oracles
may run concurrently because those workstreams do not redesign it.

## Integration and stop policy

Every accepted worker commit must pass its task command and the accumulated
repository checks from the integrated tree. After two or three accepted
leaves, the root performs an explicit product-goal check before selecting more
infrastructure work.

Routine task commands must be safe on the development workstation and should
invoke zero compiler/backend processes. A packet's explicit full-oracle path
must be serialized, run at lowered priority, cap each Java child at 2 GiB and
two active processors by default, and refuse configuration above 4 GiB or four
processors. Do not start backend work while swap is exhausted or unrelated
heavy work is active. Reporting-only changes reuse and reproject the last
successful raw output instead of repeating compilation.

After three substantive full-oracle cycles without acceptance, preserve the
evidence and split or redesign the packet. Do not broaden ownership, add a
second shared contract, or silently enter C1/C2 merely to make a leaf pass.

## Current cycle

- Accepted loop result: R2-G-07 integrated as `71379e4` after three substantive
  oracle cycles. The root replayed the full acceptance and two read-only audits
  found parser-canonicality and evidence-binding gaps before integration; the
  final single commit closes both.
- Accepted loop result: R3-G-01A integrated as prototype `249c540` plus repair
  `1ac7bc1`. Root's first detached replay rejected path-derived ordering and
  opaque metadata hashes; the second repair cycle and two fresh detached
  replays closed both before integration.
- Accepted loop result: R3-G-02A integrated as prototype `8d657e5`, semantic
  repair `daf4d60`, and projection repair `e5b5234`. The stopped prototype's
  three cycles remain frozen; the repair used its separate two-cycle cap.
  Root's first different-checkout replay found run-local raw clone digests in
  committed evidence. Cycle 2 retained their transient equality/repeat checks,
  omitted the checkout-local values explicitly, and a third fresh checkout
  passed the full replay, 10/10 checks, and `git diff --check`.
- Accepted composition checkpoint:
  `draft/k-in-k-r3-g-02a-acceptance-checkpoint-2026-08-20.md`.
- Accepted loop result: R3-G-03 integrated as prototype `0a1a945` plus
  acceptance-boundary repair `6c88e2c`. The worker used one substantive
  full-oracle cycle. Its first audit closed an unsafe replay-reuse path,
  generated-completion validation, and exact KAST-version typing before the
  worker commit. Root's fresh audit then rejected an unpinned bare `krun` call
  and shallow completion-cell validation. The repair pins and invokes the
  resolved tool, validates full generated completion shapes, and expands the
  fail-closed suite to 22 cases. A fresh different-path replay passed, followed
  by 10/10 repository checks and `git diff --check`.
- Accepted head-match checkpoint:
  `draft/k-in-k-r3-g-03-acceptance-checkpoint-2026-08-20.md`.
- Accepted loop result: R3-G-04 integrated as prototype `f4a64c1` plus root
  repair `5ce645d`. K owns exact two-event adjacency, shared typed origin
  variables, literal trace exhaustion, and three exact `#Bottom` negatives.
  Root repair closes loose runtime-event projection and separates the
  zero-backend routine verifier from explicit resource-capped replay.
- Accepted next-event checkpoint:
  `draft/k-in-k-r3-g-04-acceptance-checkpoint-2026-08-21.md`.
- Authorized split repair: `R3-G-05L` addresses the live inherited-descriptor
  owner versus nested-compiler-child working-directory boundary exposed after
  the original three-cycle stop. See
  `tasks/wave-3/R3-G-05L-nested-child-descriptor-path-repair.md`. The split
  permits at most two further substantive cycles, activates only total cycle 4
  initially, and does not silently authorize total cycle 5.
- Pre-cycle audit repair: `R3-G-05M` binds the exact clean implementation HEAD
  and routes Java-internal nested `krun` scratch arguments through the stable
  descriptor-owner path. Total cycle 4 remains unspent and is still the only
  authorized next raw attempt after acceptance. See
  `tasks/wave-3/R3-G-05M-clean-head-and-java-scratch-repair.md`.
- Final split-cycle authorization: `R3-G-05N` preserves cycle 4's nested Java
  heap failure and authorizes one fresh total cycle 5 at exactly the existing
  2048 MiB hard maximum. No sixth cycle is authorized. See
  `tasks/wave-3/R3-G-05N-final-2048-heap-cycle.md`.
- Pre-launch timeout repair: `R3-G-05O` closes the fresh audit finding that N's
  7200-second timeout was a default and authorization input rather than an
  exact non-test and evidence invariant. It spends no cycle and leaves the
  single N-authorized cycle 5 unstarted. See
  `tasks/wave-3/R3-G-05O-exact-final-timeout-binding.md`.
- Pre-launch report-verification repair: `R3-G-05P` requires the final verifier
  to reject a Markdown report whose exact 7200-second witness was weakened even
  when its recorded report hash was recomputed. It spends no cycle. See
  `tasks/wave-3/R3-G-05P-exact-timeout-report-verification.md`.
- Terminal split result: exact clean cycle 5 at implementation `c8f939d`, 2048
  MiB heap, two processors, and 7200 seconds failed at
  `positive-pair-transactions`, status 113. Nested configuration
  `krun`/`kparse` again exhausted Java heap after the stable owner-qualified
  path repair succeeded. The watchdog did not fire, peak session RSS was
  2,423,740 KiB, and teardown left the target session empty.
- Final stop checkpoint:
  `draft/k-in-k-r3-g-05-final-five-cycle-stop-checkpoint-2026-08-22.md`.
- Active packet: none. R3-G-05 is stopped and unaccepted; R3-G-06 through
  R4-G-05 and D1 remain dependency-blocked. No sixth cycle or further repair
  is authorized.
- New shared contract allowed: one task-owned exact-two producer contract.
- Root hold points: domain event constructors, temporal matching, gaps,
  symbolic exploration, mutation work, monitors, persistent official-K
  modification, general `SemanticInput`, and C1/C2.
