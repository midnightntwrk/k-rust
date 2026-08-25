# R3-G-04 acceptance checkpoint — 21 August 2026

Status: accepted and integrated. This checkpoint fixes the exact same-origin
`next-event` boundary and the workstation-safe verification policy before an
atomic two-rule producer is activated.

## Accepted composition

R3-G-04 is integrated as prototype `f4a64c1` and root acceptance repair
`5ce645d`. The worker lineage is `c432504`; root packet repair `84ec8a9`
replaced the cycle-one ambiguous `bump + bump + bump` fixture with exact
`hold(bump + bump) + bump` before final evidence.

Pinned ordinary `krun --pattern --output json` matched the exact two-event
trace produced by `hold(bump) + bump`. K owned both adjacent
`ListItem(ruleApplied(ruleOrigin(...)))` graphs, five shared typed origin
variables, and literal `.List` exhaustion. The portable witness is ordered
indices `[0,1]`, two `RuleApplied` constructors, and two equal origins.

K returned exact zero-argument `#Bottom{GeneratedTopCell}` for the one-event
too-short input, the three-event non-exhausted input, and the unequal second
label. Eight matcher queries repeated byte-for-byte across two fresh accepted
definitions. Four separate instrumented/baseline runtime invocations retained
equal `k`/`state` after trace erasure.

The host validated official KAST v4, exact substitution/completion shapes,
canonical strings, and raw driver/runtime equality before portable projection.
It did not scan a trace or infer adjacency, shared payloads, or exhaustion.

## Root acceptance repair

The worker used three substantive cycles: parser ambiguity discovery, repaired
fixture validation, and final worker evidence generation. Its fresh
adversarial audit then found two acceptance-boundary defects. Root repair
`5ce645d`:

- makes the recorded three-cycle history reproducible instead of defaulting to
  one;
- structurally parses exact `ListItem(ruleApplied(ruleOrigin(five strings)))`
  runtime events instead of counting detached constructor names and strings;
- adds four zero-backend failures for detached terms, missing wrappers,
  residual syntax, and the wrong exact event count; and
- separates routine evidence verification from explicit full backend replay.

The root full replay completed successfully from
`spine/rule-applied-next-event/build/root-repair` before the reporting-only
finalization change. Final evidence was regenerated from those raw matcher and
runtime outputs with zero new compiler/backend invocations. A read-only audit
accepted the routine zero-backend boundary; its concern about JVM option
precedence was independently reproduced on the installed JDK, where
`_JAVA_OPTIONS=-Xmx128m java -Xmx256m` reports a 128 MiB effective heap.

Routine verification now invokes no K compiler or backend:

```sh
bun run r3:g:rule-applied-next-event
bun run check
git diff --check
```

All passed; repository checks were 10/10. The routine entry point refuses its
former full-replay environment switch. A deliberate direct full replay, if
ever authorized while the workstation has sufficient headroom, constrains
Java children to 2 GiB and two active processors by default, with hard
configuration ceilings of 4 GiB and four processors. External K remained
exactly ` M pyk/uv.lock`.

Accepted evidence hashes are:

- results: `99a2ec547665bf5c66ac148c03c196b0dd271045bff9b17fde3d09465f95cbb4`;
- report: `d009434285a2c7a21c939fef1e114aa00d2e61040d569f7b7e1016f3ee2d0e5f`.

## Product-goal checkpoint and next leaf

The accepted result is deliberately narrow: exact concrete adjacency of two
observations from one rule on the observed-event clock. It does not establish
distinct-event ordering, gaps, arbitrary subsequences, `eventually-after`, a
temporal API, domain events, symbolic paths, or a monitor.

The next dependency is an atomic explicit two-rule generic `RuleApplied`
allowlist. It must instrument exactly two independently selected safe-shape
rules in one all-or-none definition transaction and produce distinct origins.
It must not add domain constructors or temporal matching.

The resource boundary is now part of every later packet: no recursive replay
of the complete accepted ancestor chain; routine checks are zero-backend;
compiler/backend work is serialized and capped; one successful raw-output run
may be reused for projection/report-only repairs with explicit provenance.
