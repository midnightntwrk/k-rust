# W1-C independent P1/P2/P3 replay

## Verdict

`pass`

All three probes reproduce their material declared checks from the starting
revision. The P3 oracle capture also reproduces its accepted-nonzero prefix
contracts and successful full boundary. No tracked source, manifest, report,
or shared configuration was modified.

## Starting revision

`9f30221d08de4b0f710061ce599b3c7f9f860273` on branch
`agent/w1-replay`, in
`/home/sebdev20/Documents/git/workspaces/starstream-fv/k-in-k2-wt-replay`.

The resolved K executable is
`/nix/store/18pfm4wc0m4b8phf1x7nwla65iv2s44r-k-7.1.337-4a46d1231473b599c699160132fd6e76a5c46406/bin/kompile`:
K release `v7.1.337`, commit evidence
`4a46d1231473b599c699160132fd6e76a5c46406`. Bun is `1.3.14`; the
installed project-local TypeScript is `5.9.3`.

## Commands executed

All commands used the worktree above as their working directory. The exact
nested `kompile`, `kast`, and `krun` argv, exit codes, and durations are in the
per-probe structured records.

```sh
git rev-parse HEAD
git status --short --branch
bun --version
node --version
npm --version
tsc --version
kompile --version
which bun
which kompile
readlink -f "$(which kompile)"
locale
sha256sum package.json bun.lock draft/k-in-k-probe-p1.md draft/k-in-k-probe-p2.md draft/k-in-k-probe-p3.md draft/k-in-k-oracles.md p1/README.md p2/README.md p3/README.md oracle/manifests/p3-coupled.json oracle/normalization.json
bun install
bunx tsc --version
bun run check
bun run p1
bun run p2
bun run p3
bun run oracle capture oracle/manifests/p3-coupled.json --out oracle/results/p3-coupled-w1-replay
sha256sum p1/build/probe-result.json p2/build/probe-result.json p3/build/probe-result.json
sha256sum oracle/results/p3-coupled-w1-replay/bundle.json
find oracle/results/p3-coupled-w1-replay/normalized -type f -print0 | sort -z | xargs -0 sha256sum
jq empty investigations/w1-replay/environment.json investigations/w1-replay/p1-replay.json investigations/w1-replay/p2-replay.json investigations/w1-replay/p3-replay.json
```

`tsc --version` before installation exited `127` because no global `tsc` was
present. This is not a prerequisite failure: `bun install` exited `0`, did not
change `bun.lock` or `package.json`, and installed the project-local compiler
used by `bun run check`. `bun run check` exited `0` with 10 tests passing and 0
failing.

## Evidence paths and digests

Committed replay evidence:

| path | SHA-256 |
| --- | --- |
| `investigations/w1-replay/environment.json` | `005fbd85767c53ad67dfe297e8262eed64540d729602e8be570cac6f9763a1cc` |
| `investigations/w1-replay/p1-replay.json` | `f3ccc481aee11092ca12879b026dc38700cf86d3364a923cf74c061822e35a1e` |
| `investigations/w1-replay/p2-replay.json` | `ba7837f416abffd28257881af7403fc54af469da8f4e7626e05b4e23280164b9` |
| `investigations/w1-replay/p3-replay.json` | `7a34d36b8d25ffa751670b33973d1c3c90fbde646d9417ae0a53def5b48a85c2` |

Ignored generated results retained in this worktree:

| path | bytes | SHA-256 |
| --- | ---: | --- |
| `p1/build/probe-result.json` | 18,487 | `1030332e1819b5b8b89de60290235d179b2e41bc9d1b483ca506661f8cddd174` |
| `p2/build/probe-result.json` | 14,967 | `2238c4b9a44c66855753c7d15dadbbdb1010e77377b67baa151d7b6c60bd45b7` |
| `p3/build/probe-result.json` | 17,844 | `12142728ca24656cfa2bdd41f2ef46ca04555d565ff0d2d58132d434ebb79d27` |
| `oracle/results/p3-coupled-w1-replay/bundle.json` | 14,848 | `ef76a6ba609d12dbef172eca79557964e801172cb504d66ee8379156d2190f4d` |

The nine normalized P3 capture artifact digests are preserved in
`p3-replay.json`. Notably, all three normalized parsed JSON boundaries are
identical (`c1696426...`), while context-prefix, cells-prefix, and full compiled
JSON have distinct hashes as expected.

## Acceptance checks passed and failed

### P1: pass

`bun run p1` exited `0` in 28.51 seconds. All six runner checks passed:

- structural Kore projection equals the independent official projection;
- ordinary semantic rewrite equals the official parsed-KAST rewrite;
- canonical input is a fixed point;
- Peano official Kore executes to `succ(succ(zero))`;
- Foobar structural projection equals official Kore;
- Foobar representative execution passes.

Observed counts match the report: one sort, four symbols, eleven structural
axioms, two function equations, and one semantic rewrite. All eight nested
external commands exited `0`.

### P2: pass

`bun run p2` exited `0` in 31.00 seconds. All seven canonical cases matched:
priority, left associativity, `avoid`, `prefer`, user-list completion,
overload selection, and checked sort inference. The overload/inference fixture
was compiled with `--type-inference-mode checked`. All eleven nested external
commands exited `0`. The declared lack of an independent raw-forest oracle is
also reproduced as `false` for `independentRawForestOracleAvailable`; it is a
known scope limit, not a failed acceptance check.

### P3: pass

`bun run p3` exited `0` in 26.26 seconds. All seven runner checks passed. The
observed projection has three cell edges, six generated context rules, five
concretized source rules, one function injection, and eleven selected final
Kore axioms. The fixed point passes and execution returns `<k> 1` and
`<state> 2`.

The context-prefix nested compile exited `1` with `GeneratedTopCell`; the
cells-prefix nested compile exited `1` with `None.get`. Both produced their
required artifacts and match the exact accepted harness contracts. The other
five nested commands exited `0`.

The independent documented oracle capture exited `0` in 13.12 seconds. Its
context and cell prefix runs were marked `acceptedNonzeroExit: true`, and the
full run exited `0`; all nine declared normalized artifacts were present.

No acceptance check failed.

## Discrepancies

There is no substantive semantic mismatch, nondeterministic result, or
installation/documentation blocker.

One non-material harness-observability discrepancy was found. The normalized
oracle capture explicitly forces and records `LC_ALL=C`, `LANG=C`, and
`TZ=UTC`. The direct P1/P2/P3 runners inherit the caller environment and their
generated `probe-result.json` files do not record that environment. This replay
ran the direct probes under ambient `LANG=C.UTF-8`, unset `LC_ALL`, and unset
`TZ`; all checks nevertheless passed. `kompile --version` rendered its build
date in JST under the ambient environment and in UTC inside the oracle bundle,
confirming that at least version text is timezone-sensitive. Classification:
`harness behavior / documentation`, non-material in this replay.

## Newly discovered contracts

1. A fresh-replay result needs a command envelope that records the effective
   locale/timezone for direct P1/P2/P3 runs, not only for oracle capture.
2. If direct-probe output is intended to be cross-host digest-comparable, the
   runner must either force the oracle environment or state which fields are
   allowed to vary. The current checks are semantic and passed, but raw result
   digests include timings and absolute worktree paths and therefore are
   evidence-instance hashes, not stable golden hashes.

## Requested shared-contract changes

Request one small shared harness packet:

- run P1/P2/P3 child processes under the same `LC_ALL=C`, `LANG=C`, `TZ=UTC`
  envelope as oracle capture;
- add effective environment and resolved tool identities to each probe result;
- document that whole `probe-result.json` SHA-256 values are run-specific due
  to durations and absolute paths, while normalized semantic projections are
  the comparable contract.

This request does not affect the current `pass` verdict and was not implemented
in this diagnostic task.

## Remaining unknowns

- Whether direct probe outputs remain semantically identical under materially
  different locales/timezones or on a non-WSL host.
- Whether a second independent machine reproduces normalized projection hashes;
  this packet supplies one fresh-agent replay, not a cross-host replay.
- P2 still has no intermediate raw parse-forest/filter snapshot oracle, as the
  originating report already states.
- P1 and P3 remain separate probe models; replay does not establish their
  production integration.

## Recommended next packet

First, take the focused shared harness-contract packet above, bounded to
environment control and result metadata. Then proceed to the planned P1/P3
integration/vertical-slice packet while retaining the official parsed-KAST
adapter and P3 boundary oracle. No semantic repair packet is warranted from
this replay.
