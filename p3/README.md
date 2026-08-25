# P3 configuration/context probe

P3 contains an executable K model of the minimum configuration metadata and
generated facts needed by its coupled fixture.

```sh
bun run p3
```

The runner checks the context prefix, the prefix through `concretizeCells`, the
full compiled definition, final Kore labels/classes, a fixed point, and concrete
execution. Evidence is written to `p3/build/probe-result.json`.

For a replayable normalized official-K bundle with all three boundaries:

```sh
bun run oracle capture oracle/manifests/p3-coupled.json \
  --out oracle/results/p3-coupled-new
```

Prefix runs intentionally exit nonzero after writing their declared artifacts;
the manifest pins the accepted diagnostic contracts. See
`draft/k-in-k-probe-p3.md`.
