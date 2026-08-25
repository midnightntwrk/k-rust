# Official-K differential oracle

This harness captures replayable artifacts from a pinned K frontend, applies a
small explicit normalization allowlist, and compares normalized boundaries. It
is the Gate B oracle described in `draft/k-in-k-complexity-plan.md`; it is not a
K-in-K implementation.

The checked smoke manifests require K v7.1.337 and require the pinned commit to
appear in the resolved `kompile` executable path. Captures refuse to overwrite
an existing directory.

## Commands

```sh
bun install

# Full determinism and semantic-mutation check. This compiles the baseline
# twice and the deliberate mutation once.
bun run oracle smoke oracle/suites/smoke.json --out oracle/results/smoke

# One manifest capture.
bun run oracle capture oracle/manifests/smoke-baseline.json \
  --out oracle/results/baseline

# Compare all normalized boundaries.
bun run oracle compare oracle/results/baseline-a oracle/results/baseline-b \
  --expect equal

# Compare one boundary and emit a structured report.
bun run oracle compare LEFT RIGHT \
  --only full:definition-kore --report oracle/results/comparison.json
```

Each capture contains:

- snapshots of the manifest, definition, and normalization policy;
- the resolved executable, version output, pin evidence, environment, and
  exact argv;
- raw `kompile` directories plus stdout/stderr;
- normalized comparison artifacts and both raw/normalized SHA-256 values;
- `bundle.json`, the machine-readable boundary index.

## Prefix-stage caveat

K's hidden `--kore-backend-steps` option selects the frontend stages but does
not stop before backend emission. An intentionally incomplete prefix can write
`compiled.json` and then fail while `ModuleToKORE` looks for state produced by
later stages. The smoke manifest records the exact accepted exit code and
diagnostic substrings for this case, and only accepts `parsed.json` and
`compiled.json` as artifacts. This is classified as an artifact-complete
nonzero run, not as a successful compilation.

If K gains a supported "stop after frontend pipeline" boundary, the manifest
should require exit zero instead.

## Normalization policy

`normalization.json` is an allowlist. Every rule has an ID, reason, and evidence.
The initial policy only:

- replaces the exact definition path;
- replaces the exact pinned K installation root in source attributes;
- canonicalizes JSON object keys while preserving array order; and
- canonicalizes line endings.

It does not reorder K sentences, Kore declarations, attributes, priorities,
injections, or axioms. Adding a rule requires a focused test showing that a
nearby semantic mutation remains visible.
