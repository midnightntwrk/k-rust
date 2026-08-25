# R3-G-03 K-native `RuleApplied` head match

Verdict: pass in one substantive full-oracle cycle.

The unchanged accepted R3-G-02A replay regenerated two fresh composed Haskell
definitions in this task's ignored build tree and byte-compared its accepted
evidence. It ran from the accepted worker revision because activation contains
the corresponding byte-identical cherry-picks; no accepted source was vendored,
modified, or consumed from an accepted build directory.

Pinned `krun --pattern --output json` applied the committed head pattern to
both definitions. K returned the six exact typed bindings `ID:String`,
`LABEL:String`, `MODULE:String`, `SOURCE:String`, `LOCATION:String`, and
`REST:List`. The five raw run-local origin fields equaled both the independently
captured composition driver target and runtime event before projection.
`REST` was exact `.List`, so the portable witness is event index zero,
constructor `RuleApplied`, origin ID
`54a064c17f3eca9ce1b5619a3534d7898d572a42b209f9f17bb552dd266756e0`,
label `bump-state`, module `R3-G-01-P3-TRACE`, source
`repo://spine/trace-configuration-composition/fixtures/p3-trace.k`, and location
`Location(36,8,39,28)`. Raw values remain only in ignored output.

The accepted non-firing input returned exact zero-argument
`#Bottom{GeneratedTopCell}`. A second K-authored pattern constraining the label
to `known-unequal-label` returned the same exact bottom for the firing input.
All six backend invocations terminated normally, and all three raw KAST results
were byte-identical across the two independently compiled repeats.

The host consumed only official KAST v4 JSON. It validated the envelope and
node algebra, flattened official `#And`/`#Equals`, enforced exact binding
cardinality and sorts, decoded canonical K string tokens, required exact empty
List, and projected only after raw validation. An independent trusted-small
walker confirmed the five actual substitution terms and empty tail. Seventeen
focused malformed-envelope cases were classified as errors with zero compiler
or backend invocations; none became semantic no-match.

This is one concrete head match and two exhaustive terminating concrete
no-matches. It does not establish a general absence result, ordered
subsequence, temporal operator, symbolic path, solver claim, monitor, corpus,
or domain event. No packet ambiguity required a split. The dependency for a
separate bounded two-event ordered-subsequence leaf is unblocked, but that
future leaf must define its intervening-event semantics explicitly.