# W1-D commands and replay

All material commands ran from
`/home/sebdev20/Documents/git/workspaces/starstream-fv/k-in-k2-wt-inprocess`.
Generated output directories are ignored.

## Revision and pin checks

```sh
git status --short --branch
git rev-parse HEAD
git -C /home/sebdev20/Documents/git/workspaces/starstream-fv/inspirations/runtimeverification/k rev-parse HEAD
command -v kompile
readlink -f "$(command -v kompile)"
kompile --version
```

The starting revision was
`57c02599ab970a4d95b7155cf9801adca9bc179c`; K resolved to v7.1.337 at
`4a46d1231473b599c699160132fd6e76a5c46406`.

## Focused classpath/lifecycle proof

The installed wrapper, jar inventory, source signatures, and Guice modules
were inspected with `sed`, `find`, `jar tf`, `javap`, and `rg`. The first
executable proof compiled the driver and resolved the official frontend:

```sh
chmod +x investigations/w1-inprocess-adapter/run-driver.sh
investigations/w1-inprocess-adapter/run-driver.sh --version
```

The first real parse exposed that direct Java lacked the Nix wrapper's pinned
`flex` PATH and exited 113 before the adapter. `run-driver.sh` was then bounded
to project the exact generated wrapper PATH entries plus K's native-library
path. The retry compiled and ran Peano identity. No official source or
installed file was changed.

Focused driver forms used during development were:

```sh
W1_ADAPTER_MODE=identity \
W1_ADAPTER_RECORD=<output>/records/peano.json \
  investigations/w1-inprocess-adapter/run-driver.sh \
  p1/fixtures/peano.k --backend haskell --emit-json \
  --main-module P1-PEANO --syntax-module P1-PEANO-SYNTAX \
  --output-definition <output>/peano-identity

W1_ADAPTER_MODE=p3-start-to-bump \
W1_ADAPTER_RECORD=<output>/records/p3-edit.json \
  investigations/w1-inprocess-adapter/run-driver.sh \
  p3/fixtures/coupled.k --backend haskell --emit-json \
  --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
  --output-definition <output>/p3-edit

W1_ADAPTER_MODE=malformed-null \
W1_ADAPTER_RECORD=<output>/records/p3-null.json \
  investigations/w1-inprocess-adapter/run-driver.sh \
  p3/fixtures/coupled.k --backend haskell \
  --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
  --output-definition <output>/p3-malformed
```

The malformed command exited 113 with
`W1 adapter validation failed: transformation returned null Definition` and
produced no `definition.kore`.

## Deterministic acceptance replay

The complete exact command sequence is executable source in `replay.sh`. It
builds official Peano/P3 baselines, in-process identities, the W1-A late-edit
oracle, the in-process early edit, and the malformed case; runs representative
programs; checks Kore projections and provenance; and emits digests/results.

```sh
investigations/w1-inprocess-adapter/replay.sh \
  investigations/w1-inprocess-adapter/replay-pass
```

The accepted clean replay exited 0 and printed:

```text
W1-D replay: pass
```

The default reproducible form requires a nonexistent output path and is:

```sh
investigations/w1-inprocess-adapter/replay.sh \
  investigations/w1-inprocess-adapter/replay
```
