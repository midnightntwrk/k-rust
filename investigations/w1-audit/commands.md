# Commands executed

Working directory for workspace commands:
`/home/sebdev20/Documents/git/workspaces/starstream-fv/k-in-k2-wt-audit`.

## Revision and input inspection

```sh
git status --short --branch
git rev-parse HEAD
wc -l tasks/wave-1/README.md tasks/wave-1/W1-B-audit.md
sed -n '1,240p' tasks/wave-1/README.md
sed -n '1,260p' tasks/wave-1/W1-B-audit.md
```

The starting revision was
`9f30221d08de4b0f710061ce599b3c7f9f860273` on `agent/w1-audit` with a clean
worktree.

All named plans, oracle/probe reports, and goal contracts were read in full via
range-bounded `sed`. Pinned source inspection used `rg`, `find`, `wc`, and
line-numbered `sed` over the files named in complexity-plan section 15,
including `Kompile.java`, `DefinitionParsing.java`, `ParseInModule.java`,
`RuleGrammarGenerator.java`, `KoreBackend.java`, `ModuleToKORE.java`, the
compiler checks directory, K_TS docs/k-parser README/version source, and the
old K-in-K revision.

Pinned revisions:

```text
K        4a46d1231473b599c699160132fd6e76a5c46406
K_TS     120e1dba90adb04f4730f90d8c0c516b30822811
OLD_KINK c72d76d16cf0987253a60f1954c40c79c84ba465
```

The parser subtree census reproduced 31 Java files and 7,429 total lines.

## Checks and replay

```sh
bun run check
```

Result: **failed before tests**, exit 127, because `tsc` is unavailable and no
dependency installation was allowed outside the packet-owned directory.

```sh
bun test oracle/test p1/test p2/test p3/test
```

Result: **pass**, 10 tests, 0 failures, 16 expectations.

```sh
bun run oracle smoke oracle/suites/smoke.json \
  --out investigations/w1-audit/evidence/smoke
```

Result: **pass** in 25.9 seconds at the exact output path above. The generated
43 MiB tree had sorted SHA-256-of-SHA-256 manifest digest
`dfe90860b80e7c1c6f89cab602c2cff0cc2b94e665ba71184d2522e5d003806e`.
The compact structured comparison report is preserved under `evidence/smoke/`;
reproducible raw compiler outputs, caches/binaries/scanners, and duplicated
normalized artifacts were omitted from the commit.

Audit-only check that the JSON mutation is not detected solely by `digest`:

```sh
bun -e '/* load each normalized JSON pair, recursively delete every key named
digest, compare canonical JSON, and print SHA-256 */'
```

Result: all four JSON boundary pairs remain different. Exact hashes are
captured in the terminal evidence summarized by `hash-drift.json`; this command
did not alter oracle policy or artifacts.

## Candidate-matrix acceptance

```sh
bun investigations/w1-audit/verify.mjs
jq empty investigations/w1-audit/capabilities.json
```

Result: **pass**. The verifier reports 69 candidate rows, all 42 census groups
represented, tracks `G1=21`, `C1=31`, `C2=8`, `optional=9`, and all 21 G1 rows
explicitly missing deterministic acceptance commands.
