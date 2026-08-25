# R2-G-05 commands

The executable source of truth is `replay.sh`. It performs all pin/status/hash
checks, copies and patches exact official sources, compiles and inspects the
overlay, runs the official baseline, all positive and negative driver modes,
Haskell execution, projections, comparisons, artifact checks, and checked
result regeneration.

Final acceptance:

```sh
bun run r2:g:pre-cf-hook
bun run check
git diff --check
```

The two development full-oracle invocations used distinct ignored output
roots; the first completed the probes and stopped at a diagnostic-text check,
and the second passed:

```sh
R2_G_05_FULL_CYCLE_COUNT=3 bash \
  investigations/r2-g-05-pre-cf-hook-prototype/replay.sh \
  investigations/r2-g-05-pre-cf-hook-prototype/build/cycle-1b

R2_G_05_FULL_CYCLE_COUNT=3 bash \
  investigations/r2-g-05-pre-cf-hook-prototype/replay.sh \
  investigations/r2-g-05-pre-cf-hook-prototype/build/cycle-2
```

Bounded pre-cycle compilation and lifecycle probes used `patch --dry-run`,
`patch`, `javac`, `javap`, the task `run-driver.sh`, `krun`, `rg`, `jq`,
`sha256sum`, and read-only Git inspection. No command edited the external K
checkout or installed K distribution.
