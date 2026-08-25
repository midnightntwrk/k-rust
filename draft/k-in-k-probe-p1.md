# P1 report: simple lowering and Kore projection

Status: bounded probe completed on 19 August 2026 against K v7.1.337,
commit `4a46d1231473b599c699160132fd6e76a5c46406`.

## Result

P1 is a passing feasibility slice for local, strongly-oracled lowering. A K
semantics accepted an adapter-produced parsed definition, staged its lowering,
and produced a canonical Kore projection. Against the independent official-K
projection, all of the following were equal:

- one user sort;
- four user symbols: three constructors and one function;
- three constructor functional axioms;
- two nontrivial same-constructor no-confusion axioms;
- three pairwise different-constructor no-confusion axioms;
- one no-junk axiom;
- function equations from Peano- and Foobar-class fixtures, including typed
  variables, default conditions, and explicit nontrivial `requires`/`ensures`;
- one ordinary semantic rewrite at the parsed-KAST boundary.

Feeding the produced canonical module back into P1 returned the same normalized
module. The official Kore definition executed the sample addition program and
returned `succ(succ(zero))` in its `<k>` cell.

The machine-readable result is `p1/build/probe-result.json` after reproduction.
Build products are ignored, while all source, fixtures, adapters, and tests are
under `p1/`.

## Exact boundary

The Peano fixture defines `zero`, `succ`, the function `plus` with two
equations, explicit `requires`/`ensures`, and the non-function rewrite
`tick(X) => X`. A second Foobar fixture exercises two nullary constructors and
a separate function equation.

Official final Kore independently validates the user declarations, structural
constructor axioms, and function equations. It cannot serve as a direct
source-term oracle for `tick`: by final emission, K has expanded the
configuration and wrapped that rewrite in generated cells. P1 therefore checks
`tick` against official `parsed.json` and does not import configuration
concretization into this probe.

This means P1's canonical module is not a complete textual
`definition.kore`, and the program execution check uses official Kore. Making a
P1-produced semantic rewrite backend-executable depends on P3's configuration,
context, and cell-concretization slice. This is a deliberate scope boundary,
not evidence that end-to-end K-in-K execution is already solved.

## Implementation and reproduction

The executable pieces are:

- `p1/src/p1.k`: staged executable lowering semantics;
- `p1/src/adapter.ts`: official parsed-KAST to explicit P1 input;
- `p1/src/official.ts`: independent official-Kore projection using the built
  `K_TS/packages/kore` package;
- `p1/src/decode.ts`: P1 result decoder and fixed-point serializer;
- `p1/src/probe.ts`: compilation, comparison, fixed-point, execution, and
  evidence runner;
- `p1/fixtures/peano.k`: feature-isolated source fixture.

From the repository root:

```sh
bun install
bun run check
bun run p1
```

The accepted run reported:

| check | result |
| --- | --- |
| P1 structural projection = official Kore projection | pass |
| P1 semantic rewrite = official parsed-KAST rewrite | pass |
| second application at the canonical boundary = first result | pass |
| representative official Kore execution | pass |
| Foobar structural projection = official Kore projection | pass |
| Foobar representative execution | pass |

The accepted runner performs eight external compile/run commands. Their timing
is recorded in `probe-result.json`; it is validation latency, not an effort
estimate.

## What the oracle found

The first full differential cycle failed for two substantive reasons:

1. Source-location filtering alone admitted configuration-generated `<k>`
   syntax as though it were user syntax. The adapter now selects productions
   from the declared user syntax module and rules from the semantic module.
2. P1 initially emitted a same-constructor no-confusion axiom for nullary
   `zero`. Official K omits that tautological axiom. The K semantics now emits
   same-constructor no-confusion only for constructors with arguments.

The second full cycle passed. These failures are useful calibration evidence:
even this small transformation required module-provenance awareness and exact
knowledge of structural-axiom edge cases. A whole-file or count-only oracle
would have localized both poorly.

A separate integration issue appeared when consuming `K_TS`: installing its
Kore package with `file:` exposed a monorepo-only `workspace:*` development
dependency. The probe imports the already-built package by repository-relative
path instead. This is packaging friction, not semantic difficulty, but a
production harness should publish or pack the package rather than rely on the
workspace layout.

## Agent-complexity telemetry

The work remained inside the fixed P1 task packet and used one lead-agent
episode with two complete oracle cycles:

| field | observation |
| --- | --- |
| accepted episode candidates | 1 |
| abandoned/failed episode candidates | 0 |
| full oracle cycles before acceptance | 2 |
| regressions in the existing harness | 0 |
| contract omissions exposed | module provenance; nullary no-confusion rule |
| fresh-agent replay | not yet performed |

Under the plan's definition this is one successful VAE candidate, but it is
only one sample and lacks fresh-agent replay. It cannot support a P50/P90 VAE
distribution. P1 therefore calibrates task shape and oracle-cycle behavior, not
a project total.

## Complexity implication

P1 supports three narrow conclusions:

1. Modern K can express and execute a staged metacircular transformation over
   an explicit parsed-definition adapter boundary.
2. For local declarations and equations, normalized structural Kore gives a
   strong and fast enough oracle for agent iteration.
3. Complexity is already driven more by boundary contracts and edge cases than
   by transformation size; dependency depth, coupling, and oracle quality
   remain the right primary metrics.

It does not reduce the provisional risk of inner parsing (P2) or the
configuration/context cluster (P3). In particular, the inability to execute
the P1-produced ordinary rewrite without configuration concretization confirms
that P3 sits on the serial path to an F1 vertical slice.

The orchestration recommendation is unchanged: do not fan out implementation.
Run P2 and P3 as bounded probes, then use an independent review before deriving
F1/F2/F3 VAE ranges or deciding safe concurrency.
