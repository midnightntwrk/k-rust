# R3-G-04 K-native exact `RuleApplied` next-event pair

Verdict: pass in three substantive full-oracle cycles.

Activation `68c95e7` was followed by packet repair `84ec8a9`, which replaced an
ambiguous three-bump input discovered in cycle one with the pinned unambiguous
`hold(bump + bump) + bump` input. Cycle two validated the repaired fixture and
all oracles. Cycle three regenerated worker evidence after tightening the
committed invocation history and exact 26-case assertion. Root acceptance
repair then made clean replay reproduce that three-cycle history and replaced
loose runtime token counting with exact event-structure validation. The final
root replay regenerated this evidence without adding a substantive worker
cycle; no ambiguity remains that requires a split.

The accepted R3-G-03 replay ran unchanged from a temporary detached checkout at
integration `6c88e2c`. It preserved that checkout's historical package pin,
regenerated and byte-compared accepted evidence, and produced two fresh
composition definitions under this task's ignored output. No accepted build
directory or external-K source was changed.

Pinned absolute `krun --pattern --output json` applied the committed exact-pair
pattern to `hold(bump) + bump` on both definitions. K returned each of the five
typed shared variables exactly once and no `REST` binding. The raw substitution
origin equaled the independent driver target and both concrete runtime event
origins before projection. The ordered portable result is indices `[0,1]`, two
`RuleApplied` constructors, and two equal origins: ID
`54a064c17f3eca9ce1b5619a3534d7898d572a42b209f9f17bb552dd266756e0`,
label `bump-state`, module `R3-G-01-P3-TRACE`, source
`repo://spine/trace-configuration-composition/fixtures/p3-trace.k`, and location
`Location(36,8,39,28)`. Raw source and source-derived ID stay in ignored output.

K returned exact zero-argument `#Bottom{GeneratedTopCell}` for all three
negative classes: the accepted one-bump program was too short, the three-bump
program left a residual event against literal `.List`, and the two-bump program
failed the unequal second-label pattern. All eight pattern invocations exited
normally and repeated byte-for-byte across the independently regenerated
definitions. The positive instrumented and baseline executions also had equal
`k`/`state` projections after trace erasure. These conservativity checks were
four separate absolute-`krun` executions: instrumented and baseline for each
of the two fresh-definition repeats, in addition to the eight matcher queries.

The host validated only the official KAST v4 envelope, exact substitution and
completion shapes, canonical tokens, raw equality, and portable projection. It
did not search a trace, infer adjacency or exhaustion, parse pretty matcher
output, or classify malformed KAST as no-match. An independent trusted-small
walker confirmed the five witness terms occur once and that no synthetic
`REST` exists. Twenty-six focused malformed-envelope cases failed with zero
compiler/backend invocations. Four additional zero-backend runtime-projector
cases rejected detached event/origin terms, malformed wrappers, residual trace
syntax, and the wrong exact event count.

This establishes only two adjacent same-origin observations on the
observed-event clock. It does not establish distinct-event order, gaps,
arbitrary subsequences, eventually-after, a temporal API, symbolic claims,
search, a monitor, corpus aggregation, or domain events. No ambiguity required
a split. The separate atomic multi-rule producer/allowlist leaf is now
dependency-unblocked.

Routine `bun run r3:g:rule-applied-next-event` verification is deliberately
zero-backend: it checks all committed pins, evidence invariants, Python source,
and adversarial runtime projection. The already completed root full replay is
the backend provenance for this evidence; finalization reprojected its raw
outputs after the reporting-only repair. The routine entry point cannot launch
a full replay. A deliberate direct `replay.sh` command caps every Java child at
2 GiB and two active processors by default, with hard override ceilings of 4
GiB and four CPUs. The installed JDK was probed to confirm `_JAVA_OPTIONS`
wins over the inherited launchers' explicit 8 GiB heap arguments. Do not run
that direct command while the workstation is under memory or swap pressure.
