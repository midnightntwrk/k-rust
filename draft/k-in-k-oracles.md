# Modern K-in-K oracle harness

Status: Gate B initial harness implemented and exercised on 18 August 2026.

This document records the executable oracle used by the complexity
reconnaissance. The implementation is under `oracle/`; usage details are in
`oracle/README.md`.

## Purpose and boundary

The harness runs the official K frontend pinned by the reconnaissance plan,
captures intermediate and final artifacts, normalizes only documented
deployment metadata, and compares named boundaries.

It is an oracle and experiment control plane. It is not an implementation of
the K-in-K semantics and does not receive reuse credit for implementing a
frontend pass.

## Pinned toolchain

The smoke manifests require:

- K release `v7.1.337`;
- commit `4a46d1231473b599c699160132fd6e76a5c46406`;
- Haskell-backend frontend profile;
- `LC_ALL=C`, `LANG=C`, and `TZ=UTC`.

The release is parsed from `kompile --version`. For the initial environment,
the commit is verified from the resolved Nix executable path:

```text
/nix/store/18pfm4wc0m4b8phf1x7nwla65iv2s44r-k-7.1.337-4a46d1231473b599c699160132fd6e76a5c46406/bin/kompile
```

A capture refuses to proceed when either check fails. The bundle records the
invoked and resolved executable paths, complete version output, and evidence
kind.

## Bundle schema

Each capture directory contains:

```text
bundle.json
inputs/
  manifest.json
  definition.k
  normalization.json
raw/<run-id>/
  invocation.json
  stdout.txt
  stderr.txt
  definition/             # the complete --output-definition directory
normalized/<run-id>/
  <artifact-id>
```

`bundle.json` records:

- input and policy SHA-256 values;
- exact argv, working directory, and controlled environment;
- K release and commit evidence;
- stage list, exit status, and duration for each run;
- raw and normalized artifact paths, sizes, and SHA-256 values.

Capture and smoke commands refuse to overwrite an existing directory. A
failed capture retains its partial directory, invocation, stdout, and stderr
for diagnosis.

## Current boundaries

The smoke corpus captures:

| boundary | source | success contract |
| --- | --- | --- |
| `contexts-prefix:parsed-json` | `parsed.json` while selecting the pipeline through `resolveContexts` | Required artifact after exact accepted prefix diagnostic |
| `contexts-prefix:compiled-json` | `compiled.json` after the same prefix | Required artifact after exact accepted prefix diagnostic |
| `full:parsed-json` | Full successful compilation | Exit zero |
| `full:compiled-json` | Full successful compilation | Exit zero |
| `full:definition-kore` | Main backend definition | Exit zero |
| `full:syntax-kore` | Syntax definition | Exit zero |
| `full:macros-kore` | Macro definition | Exit zero |

### Prefix-stage limitation

`--kore-backend-steps` selects stages but does not stop after the selected
frontend pipeline. With the prefix through `resolveContexts`, K writes valid
`parsed.json` and prefix `compiled.json`, then `ModuleToKORE` fails because
later passes have not created `GeneratedTopCell` state.

The manifest therefore requires all of:

- exit code `1`;
- stderr containing `Uncaught exception`;
- stderr containing `GeneratedTopCell`;
- both declared JSON artifacts.

The bundle marks this `acceptedNonzeroExit: true`. It is artifact-complete for
the declared prefix boundary, not a successful compilation. Unexpected errors
or missing artifacts fail capture.

This workaround should be removed if K gains a supported stop-after-pipeline
option.

## Normalization allowlist

The checked policy is `oracle/normalization.json`. Rules have a stable ID,
operation, reason, and evidence.

The initial policy permits only:

1. replacing the exact resolved input definition path with `<DEFINITION>`;
2. replacing the exact verified K installation root with `<K_INSTALL>`;
3. recursively sorting JSON object keys while preserving array order; and
4. converting CRLF/CR line endings to LF in text artifacts.

It does not remove digests, unique IDs, locations, labels, attributes,
declaration order, priorities, injections, conditions, or axioms. In
particular, the deliberate source mutation first appears in the JSON comparison
through K's changed digest; the later semantic changes remain independently
visible in Kore declarations and rules.

## Smoke corpus and mutation

`oracle/corpus/smoke/baseline.k` defines a small expression language with:

- syntax and semantic modules;
- constructors;
- a function symbol and two equations;
- a generated configuration and `<k>` cell.

`mutation.k` deliberately changes the identity constructor from `zero` to
`unit` and changes the base equation from returning its argument to returning
`unit`. The files retain the same line structure so the comparison is not
merely detecting shifted locations.

The suite contract expects the mutation to change:

- prefix parsed and compiled JSON;
- full parsed and compiled JSON;
- main Kore; and
- syntax Kore.

It expects `macros.kore` to remain equal because neither definition declares a
macro.

## Observed Gate B result

The initial run compiled the baseline twice and the mutation once. All seven
normalized boundaries were identical between repeated baseline runs.

The semantic mutation produced the expected result:

| boundary | verdict |
| --- | --- |
| `contexts-prefix:parsed-json` | different |
| `contexts-prefix:compiled-json` | different |
| `full:parsed-json` | different |
| `full:compiled-json` | different |
| `full:definition-kore` | different |
| `full:syntax-kore` | different |
| `full:macros-kore` | equal |

Representative normalized baseline hashes from that run were:

| boundary | SHA-256 |
| --- | --- |
| `contexts-prefix:parsed-json` | `00b5708bca2d027963df7b9d2ff84cb9a1b9d1bfa68e22635c3c2a1aa993731f` |
| `contexts-prefix:compiled-json` | `62f1dd1f6a7640e4379ea3aa9bc56224a442ad2ab1f432b0326af8a50f3a0821` |
| `full:parsed-json` | `00b5708bca2d027963df7b9d2ff84cb9a1b9d1bfa68e22635c3c2a1aa993731f` |
| `full:compiled-json` | `fe95fafc255750b29dfd099d8003e0dc5a24d767a47c41e6e4df4a55af343243` |
| `full:definition-kore` | `b55f21dc5528ae35c57facd5b2043cf07f57805f6b69860712466969596c70ee` |
| `full:syntax-kore` | `76c5ed0ad88033bc61fc6bc1141425a08589ce5f4f5771ba13ae5f6838c730a1` |
| `full:macros-kore` | `3585c084b81281ec26971b2e42c56b9968a802c5d645a81062296350493491cf` |

These hashes are evidence for this exact fixture and policy, not a promise that
all future compatible harness versions retain the same pretty-printed JSON.
The smoke suite's primary assertion is repeated determinism plus mutation
sensitivity.

## Reproduction

```sh
bun install
bun run check
bun run oracle smoke oracle/suites/smoke.json \
  --out oracle/results/smoke-gate-b
```

The smoke command deliberately requires a new output directory. Choose a new
name for a later run.

Focused comparator checks:

```sh
bun run oracle compare \
  oracle/results/smoke-gate-b/baseline-a \
  oracle/results/smoke-gate-b/baseline-b \
  --expect equal

bun run oracle compare \
  oracle/results/smoke-gate-b/baseline-a \
  oracle/results/smoke-gate-b/mutation \
  --only full:definition-kore \
  --expect different
```

## Gate B status and remaining work

The initial Gate B requirements are satisfied for the smoke corpus:

- manifests reproduce the same input and toolchain;
- full and selected prefix artifacts are captured;
- normalization is explicit and mutation-tested;
- failures and exact invocations are replayable from bundles;
- repeated official-K captures compare equal;
- a deliberate source-level semantic mutation is detected at every boundary
  where the suite says it should be observable.

P1 added a feature-isolated Peano fixture and a structural projection over the
official parsed-KAST and Kore artifacts. Its first differential run exposed two
real normalization/semantics errors, demonstrating that the focused oracle is
sensitive beyond whole-file mutation checks. See `draft/k-in-k-probe-p1.md`.

P2 will need an additional observation seam or focused final-AST fixtures for
intermediate disambiguation filters; the current public compiler artifacts
cannot expose raw parse forests.
