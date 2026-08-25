# W1-A exact material commands

All commands ran from
`/home/sebdev20/Documents/git/workspaces/starstream-fv/k-in-k2-wt-egress`.
Shell redirections are part of the evidence capture. Read-only `rg`, `sed`,
`jq`, `diff`, `cmp`, `sha256sum`, and source-inspection commands are omitted
below only when their complete product is already stored in
`evidence/source-audit`, a diff, a projection, or `evidence/SHA256SUMS`.

## Revision and toolchain

```sh
git status --short --branch
git rev-parse HEAD
git -C /home/sebdev20/Documents/git/workspaces/starstream-fv/inspirations/runtimeverification/k rev-parse HEAD
git -C /home/sebdev20/Documents/git/workspaces/starstream-fv/inspirations/runtimeverification/k status --short --branch
command -v kompile
readlink -f "$(command -v kompile)"
kompile --version
```

## Cycle 1: baseline and post-process identity

The first Peano post-process invocation used the same command as the retry
below and failed because the initial adapter expected KAST v3. Its stderr is
`evidence/cycle-1/logs/peano-identity.stderr`. After pinning the actual KAST v4
envelope, the retry was:

```sh
kompile p1/fixtures/peano.k --backend haskell --emit-json --main-module P1-PEANO --syntax-module P1-PEANO-SYNTAX --output-definition investigations/w1-egress/evidence/cycle-1/peano-baseline > investigations/w1-egress/evidence/cycle-1/logs/peano-baseline.stdout 2> investigations/w1-egress/evidence/cycle-1/logs/peano-baseline.stderr
kompile p1/fixtures/peano.k --backend haskell --emit-json --main-module P1-PEANO --syntax-module P1-PEANO-SYNTAX --post-process "python3 investigations/w1-egress/postprocess.py identity" --output-definition investigations/w1-egress/evidence/cycle-1/peano-identity > investigations/w1-egress/evidence/cycle-1/logs/peano-identity-retry.stdout 2> investigations/w1-egress/evidence/cycle-1/logs/peano-identity-retry.stderr
krun p1/fixtures/program.peano --definition investigations/w1-egress/evidence/cycle-1/peano-baseline > investigations/w1-egress/evidence/cycle-1/runtime/peano-baseline.out 2> investigations/w1-egress/evidence/cycle-1/runtime/peano-baseline.err
krun p1/fixtures/program.peano --definition investigations/w1-egress/evidence/cycle-1/peano-identity > investigations/w1-egress/evidence/cycle-1/runtime/peano-identity.out 2> investigations/w1-egress/evidence/cycle-1/runtime/peano-identity.err

kompile p3/fixtures/coupled.k --backend haskell --emit-json --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX --output-definition investigations/w1-egress/evidence/cycle-1/p3-baseline > investigations/w1-egress/evidence/cycle-1/logs/p3-baseline.stdout 2> investigations/w1-egress/evidence/cycle-1/logs/p3-baseline.stderr
kompile p3/fixtures/coupled.k --backend haskell --emit-json --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX --post-process "python3 investigations/w1-egress/postprocess.py identity" --output-definition investigations/w1-egress/evidence/cycle-1/p3-identity > investigations/w1-egress/evidence/cycle-1/logs/p3-identity.stdout 2> investigations/w1-egress/evidence/cycle-1/logs/p3-identity.stderr
krun p3/fixtures/program.exp --definition investigations/w1-egress/evidence/cycle-1/p3-baseline > investigations/w1-egress/evidence/cycle-1/runtime/p3-baseline.out 2> investigations/w1-egress/evidence/cycle-1/runtime/p3-baseline.err
krun p3/fixtures/program.exp --definition investigations/w1-egress/evidence/cycle-1/p3-identity > investigations/w1-egress/evidence/cycle-1/runtime/p3-identity.out 2> investigations/w1-egress/evidence/cycle-1/runtime/p3-identity.err
```

For both fixtures, `cmp` was run over `definition.kore`,
`syntaxDefinition.kore`, `macros.kore`, and runtime stdout. All passed.

## Cycle 2: typed compiled-sentence edit

```sh
kompile p3/fixtures/coupled.k --backend haskell --emit-json --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX --post-process "python3 investigations/w1-egress/postprocess.py p3-start-to-bump" --output-definition investigations/w1-egress/evidence/cycle-2/p3-sentence-edit > investigations/w1-egress/evidence/cycle-2/logs/p3-sentence-edit.stdout 2> investigations/w1-egress/evidence/cycle-2/logs/p3-sentence-edit.stderr
krun p3/fixtures/program.exp --definition investigations/w1-egress/evidence/cycle-2/p3-sentence-edit > investigations/w1-egress/evidence/cycle-2/runtime/p3-sentence-edit.out 2> investigations/w1-egress/evidence/cycle-2/runtime/p3-sentence-edit.err
diff -u investigations/w1-egress/evidence/cycle-1/p3-baseline/definition.kore investigations/w1-egress/evidence/cycle-2/p3-sentence-edit/definition.kore > investigations/w1-egress/evidence/cycle-2/definition-kore.diff
```

## Cycle 3: attempted typed parsed-KAST replay

Direct replay (both Peano and P3 failed with `None.get` because emitted
`parsed.json` omits `DEFAULT-CONFIGURATION`):

```sh
kompile investigations/w1-egress/evidence/cycle-1/peano-baseline/parsed.json --outer-parsed-json --backend haskell --emit-json --main-module P1-PEANO --syntax-module P1-PEANO-SYNTAX --output-definition investigations/w1-egress/evidence/cycle-3/peano-parsed-reentry > investigations/w1-egress/evidence/cycle-3/logs/peano-parsed-reentry.stdout 2> investigations/w1-egress/evidence/cycle-3/logs/peano-parsed-reentry.stderr
kompile investigations/w1-egress/evidence/cycle-1/p3-baseline/parsed.json --outer-parsed-json --backend haskell --emit-json --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX --output-definition investigations/w1-egress/evidence/cycle-3/p3-parsed-reentry > investigations/w1-egress/evidence/cycle-3/logs/p3-parsed-reentry.stdout 2> investigations/w1-egress/evidence/cycle-3/logs/p3-parsed-reentry.stderr
kompile investigations/w1-egress/evidence/cycle-1/p3-baseline/parsed.json --outer-parsed-json --backend haskell --emit-json --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX --debug --output-definition investigations/w1-egress/evidence/cycle-3/p3-parsed-reentry-debug > investigations/w1-egress/evidence/cycle-3/logs/p3-parsed-reentry-debug.stdout 2> investigations/w1-egress/evidence/cycle-3/logs/p3-parsed-reentry-debug.stderr
```

The temporary adapter then added an empty `DEFAULT-CONFIGURATION`. An
unreachable module still failed at the same lookup; importing it reached the
next precise failure, missing inner-term `Production` attributes:

```sh
python3 investigations/w1-egress/postprocess.py parsed-reentry-identity investigations/w1-egress/evidence/cycle-1/p3-baseline/parsed.json > investigations/w1-egress/evidence/cycle-3/p3-parsed-adapted-imported.json
kompile investigations/w1-egress/evidence/cycle-3/p3-parsed-adapted-imported.json --outer-parsed-json --backend haskell --emit-json --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX --debug --output-definition investigations/w1-egress/evidence/cycle-3/p3-parsed-reentry-imported-debug > investigations/w1-egress/evidence/cycle-3/logs/p3-parsed-reentry-imported-debug.stdout 2> investigations/w1-egress/evidence/cycle-3/logs/p3-parsed-reentry-imported-debug.stderr
```

The official pyk outer artifact producer also failed before producing an
artifact for P3:

```sh
PYTHONPATH=/home/sebdev20/Documents/git/workspaces/starstream-fv/inspirations/runtimeverification/k/pyk/src pyk parse-outer p3/fixtures/coupled.k --main-module P3-COUPLED --output-file investigations/w1-egress/evidence/outer-route/p3.outer-term.json > investigations/w1-egress/evidence/outer-route/logs/pyk-parse-outer.stdout 2> investigations/w1-egress/evidence/outer-route/logs/pyk-parse-outer.stderr
```

## Cycle 4: source fallback for observation configuration

```sh
kompile investigations/w1-egress/fixtures/p3-observation.k --backend haskell --emit-json --main-module W1-P3-OBSERVATION --syntax-module W1-P3-OBSERVATION-SYNTAX --output-definition investigations/w1-egress/evidence/cycle-4/p3-observation-a > investigations/w1-egress/evidence/cycle-4/logs/p3-observation-a.stdout 2> investigations/w1-egress/evidence/cycle-4/logs/p3-observation-a.stderr
kompile investigations/w1-egress/fixtures/p3-observation.k --backend haskell --emit-json --main-module W1-P3-OBSERVATION --syntax-module W1-P3-OBSERVATION-SYNTAX --output-definition investigations/w1-egress/evidence/cycle-4/p3-observation-b > investigations/w1-egress/evidence/cycle-4/logs/p3-observation-b.stdout 2> investigations/w1-egress/evidence/cycle-4/logs/p3-observation-b.stderr
krun investigations/w1-egress/fixtures/program.exp --definition investigations/w1-egress/evidence/cycle-4/p3-observation-a > investigations/w1-egress/evidence/cycle-4/runtime/p3-observation-a.out 2> investigations/w1-egress/evidence/cycle-4/runtime/p3-observation-a.err
krun investigations/w1-egress/fixtures/program.exp --definition investigations/w1-egress/evidence/cycle-4/p3-observation-b > investigations/w1-egress/evidence/cycle-4/runtime/p3-observation-b.out 2> investigations/w1-egress/evidence/cycle-4/runtime/p3-observation-b.err
```

`cmp` passed for the two repeats over parsed JSON, compiled JSON, all three
Kore files, and runtime stdout.

## Identity/provenance projection and acceptance replay

```sh
python3 investigations/w1-egress/project_identity.py investigations/w1-egress/evidence/cycle-1/peano-baseline/compiled.json /p1/fixtures/peano.k investigations/w1-egress/evidence/projections/peano-baseline.json
python3 investigations/w1-egress/project_identity.py investigations/w1-egress/evidence/cycle-1/peano-identity/compiled.json /p1/fixtures/peano.k investigations/w1-egress/evidence/projections/peano-identity.json
python3 investigations/w1-egress/project_identity.py investigations/w1-egress/evidence/cycle-1/p3-baseline/compiled.json /p3/fixtures/coupled.k investigations/w1-egress/evidence/projections/p3-baseline.json
python3 investigations/w1-egress/project_identity.py investigations/w1-egress/evidence/cycle-1/p3-identity/compiled.json /p3/fixtures/coupled.k investigations/w1-egress/evidence/projections/p3-identity.json
jq -e --slurp '.[0].sentences == .[1].sentences' investigations/w1-egress/evidence/projections/peano-{baseline,identity}.json
jq -e --slurp '.[0].sentences == .[1].sentences' investigations/w1-egress/evidence/projections/p3-{baseline,identity}.json
investigations/w1-egress/replay.sh investigations/w1-egress/replay-check
```

The last command exited 0 and printed `W1-A replay: pass`. Generated compiler
directories, KAST/Kore dumps, the duplicate replay bundle, and backend/cache
binaries are omitted from the compact commit. Their digests remain in
`evidence/SHA256SUMS`; the replay script reconstructs the accepted artifacts.
