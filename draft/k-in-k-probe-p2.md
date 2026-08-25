# P2 report: inner parsing and disambiguation

Status: bounded probe completed on 19 August 2026 against K v7.1.337,
commit `4a46d1231473b599c699160132fd6e76a5c46406`.

## Decision

Use a replaceable official-K parsed-KAST adapter for the first lowering
delivery. Do not describe that delivery as an independent feature-complete K
frontend. Treat replacement with a specified parser as its own critical-path
project, with a new observation seam as the first prerequisite.

This is not a conclusion that parsing is unimportant. It is the opposite: the
probe found the cluster too coupled and too weakly observable to hide inside
the initial lowering build.

## Executable evidence

The probe compiled five feature-isolated definitions and asserted exact
canonical trees for seven cases:

| case | asserted result |
| --- | --- |
| priority | `n + n * n` resolves as `plus(n, times(n,n))` |
| associativity | `n + n + n` resolves left |
| `avoid` | dangling `else` attaches to the inner conditional |
| `prefer` | the independent preferred-production fixture makes the same selection |
| user list | three elements become nested `atoms` ending in `.atoms` |
| overload | `L().field` selects the more specific `lvalDot` production |
| sort inference | the labelled wildcard is assigned `LVal` |

The inference definition was compiled with `--type-inference-mode checked`, so
official K ran both SimpleSub and Z3 inference and would have rejected a
disagreement. All seven cases passed.

Reproduce with:

```sh
bun run p2
```

The implementation is under `p2/`; machine-readable command timing, expected
trees, and actual trees are written to `p2/build/probe-result.json`.

## Architecture comparison

### Replaceable adapter — selected for first delivery

The adapter has a strong final-output oracle and passed every selected case.
It lets P1/P3 lowering consume typed, disambiguated KAST now. Its trust boundary
must remain explicit: grammar generation, scanning, parsing, all ambiguity
filters, and inference still come from official K.

### Direct TypeScript transcription — plausible separate project

The pinned inner-parser subtree contains 31 Java files and about 7,429 lines,
but line count is only surface telemetry. The more important facts are its
ordered twelve-stage filter pipeline, two inference implementations, shared
grammar/module state, and overload/list passes after inference. `K_TS` already
provides compatible outer AST and KAST representations, which reduces adapter
work but does not implement this cluster.

This option has the best conventional implementation path if independence is
required. It should be decomposed around scanner/forest, structural filters,
and inference only after intermediate snapshots exist.

### Declarative parser in K — research track, not first delivery

A generalized parser and ambiguity forest can be represented in K, but this
probe found no evidence that doing so would reduce the hard parts: grammar
generation, forest sharing, ordered ambiguity movement, overload resolution,
and constraint-based sort inference. It would also place the largest state
space behind the weakest oracle. A precedence-only executable demo would not
calibrate this architecture honestly, so P2 did not substitute one for the
required feature set.

## Oracle limitation

Official `parsed.json` exposes the final resolved KAST, not the raw Earley
forest or snapshots after individual filters. Thus final cases have an O4
oracle, while failures inside the ordered filter cluster remain O1/O2. Before
implementing an independent parser, add a debug/export seam after parsing,
priority filtering, prefer/avoid, inference, overload removal, list completion,
and bracket removal.

## Agent-complexity telemetry

One lead-agent episode produced the accepted slice. One fixture-construction
diagnostic caught incorrect priority-block syntax before the full suite; the
first complete seven-case oracle cycle passed. There is no fresh-agent replay,
so this is one VAE candidate rather than a P50/P90 distribution.

The accepted external K commands took roughly 26.8 seconds in aggregate. That
is evaluation latency, not project effort.

## Complexity implication

P2 confirms that parser independence is a scope multiplier, not a parallel
leaf. With the adapter, lowering can proceed while the parser cluster remains a
declared dependency. Without the adapter, IP-01 through IP-07 stay on the serial
path and retain `X` risk. Maximum useful fan-out inside that cluster should
remain one coherent implementation owner plus oracle work until stable
intermediate contracts exist.
