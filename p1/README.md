# P1 minimal-lowering probe

This is the executable P1 calibration probe from
`draft/k-in-k-complexity-plan.md`. It is a deliberately small semantics of a
parsed definition to a canonical Kore projection, not a frontend or backend.

The TypeScript adapter selects only user syntax/rules from official
`parsed.json`. The K semantics in `src/p1.k` stages sorts, productions, and
rules through cells, generating constructor axioms and classifying function
equations versus semantic rewrites. The comparator independently projects the
corresponding official `definition.kore` with the built
`K_TS/packages/kore` reader.

Run the complete probe:

```sh
bun run p1
```

It recompiles the fixture and P1 semantics, compares both projections, checks
that feeding the P1 result back to P1 is a fixed point, and executes the fixture
with official K. Machine-readable evidence is written to
`p1/build/probe-result.json`; the build directory is ignored.

The ordinary `tick` rewrite is compared at parsed KAST. Official final Kore has
already wrapped such a rule in generated configuration cells, which is P3's
scope. Consequently this probe does not claim that its compact projection is a
standalone backend definition.
