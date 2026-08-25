# M3B independent configuration/state oracle

This directory freezes the external acceptance contract for the second IMP
vertical slice. It is production-independent: the verifier invokes only the
pinned K command-line tools, and neither the handwritten definition nor the
corpus imports a KRS crate or KRS-generated artifact.

`fixtures/expr.k` carries forward the M3A expression theory.
`fixtures/calc.k` is a module-renamed transcription of modern IMP `calc.k`,
layered on that expression file with an ordinary `requires`. Together they
retain the state surface that KRS must eventually emit:

- `Id` syntax and the after-the-fact `Expr ::= Id` injection;
- strict assignment and right-associative statement sequencing;
- the `stmt > seq-stmt` production priority;
- a two-cell configuration with `$PGM:Stmt` and `$ENV:Map` variables;
- computation sequencing via `~>` and `.K`;
- map lookup, insertion, and replacement; and
- the labeled `step`, `var`, and `assign` multi-cell rules with cell frames.

The reference toolchain is K 7.1.337 at commit
`4a46d1231473b599c699160132fd6e76a5c46406`. The upstream sources are modern
IMP commit `683a773418add3bcae8ded47c2b24e94494e1988`; their exact `expr.k` and
`calc.k` hashes, every handwritten input hash, and every derived oracle hash
are recorded in `pins.json`.

## Accepted corpus

The five accepted programs distinguish behaviors that a final-state-only
test would conflate:

| Program | Initial environment | Exact LLVM rewrites | Final environment | Observable contract |
| --- | --- | ---: | --- | --- |
| `single-assignment.calc` | `.Map` | 1 | `x |-> 1` | empty initialization and insertion |
| `initial-environment.calc` | `x |-> 41` | 7 | `x |-> 41, y |-> 42` | nonempty initialization and lookup |
| `lookup-evaluation-order.calc` | `.Map` | 15 | `x |-> 2, y |-> 8` | lookup, multiplication-before-addition, strict assignment |
| `update-existing.calc` | `.Map` | 9 | `x |-> 5` | same-key replacement rather than duplicate insertion |
| `right-associated-sequence.calc` | `.Map` | 14 | `x |-> 1, y |-> 2, z |-> 3` | priority, right association, sequencing, later lookup |

For each program, `kast` must produce the expected semantic tree, `kparse`
must accept it, and the program unparser must reparse to the identical full
KAST v4 tree. The verifier then checks the exact rewrite count and concrete
final configuration. It also executes every depth from zero through the
normal form: 51 full configurations are retained and hashed, including the
generated heat/cool freezer frames. This makes evaluation order and cell
updates observable rather than inferred from the final map.

## Rejected and diagnostic corpus

The rejected cases preserve three distinct outcomes:

- missing syntax fails at the exact authored source range;
- an undefined identifier and a cross-sort addition parse successfully but
  remain stuck at exact depth-indexed configurations; and
- integer division by zero reaches the concrete LLVM
  `[hook_INT_tdiv]` error instead of becoming a normal state.

The induced outer-parser error separately proves that K selects the authored
`@` at `fixtures/induced-definition-error.k:2:19-2:20`.

## Definition evidence and determinism

The emitted `parsed.json` must contain exactly three local calculation
productions, one right-associativity sentence, one priority sentence, the 18
inherited expression rules, and the calculation module's expected generated
configuration sentences. The compiled definition must contain exactly one
assignment strictness context and 25 heat/cool pairs: 24 inherited from the
expression layer and one from assignment.

The verifier rejects unknown KAST envelope versions, node shapes, project
labels, arities, sort shapes, map shapes, and tree-changing unparse results.
After removing only enumerated compiler metadata and ordering unordered
definition members canonically, `parsed.json` and `compiled.json` must match
their pinned hashes. Full parse trees, unparse output, final configurations,
all 51 trace states, stuck states, and the division diagnostic are independently
hash-pinned.

## KRS implementation requirements exposed by this oracle

M3B needs the following complete paths beyond the M3A expression slice:

1. `Id` and `Map` builtin imports, including stable sort and operation
   identities for map unit, item, lookup matching, and update.
2. A post-hoc subsort/injection declaration from `Id` to an already-declared
   `Expr` sort.
3. Multiple fixed configuration cells, multiple typed configuration
   variables, and a root initializer that composes both cells.
4. Configuration-aware rules that can rewrite one or several cells, retain
   `...` frames, read a map cell without rewriting it, and rewrite the map cell
   in the same rule as the computation cell.
5. `KSequence`, `~>`, and `.K` term forms in rule patterns/results.
6. Map pattern and update terms, typed `Value` variables, rule labels, and
   source-local provenance for every nested cell/map/computation term.
7. `strict(2)`, right associativity, production groups, and priority lowering
   that reproduce the pinned generated contexts and parse trees.

## Verification

Run exactly:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tests/m3b/verify.py
```

The frozen verifier SHA-256 is
`08401de91efba5c39456e094295643b36504a123801c6db5d421667b5762ea05`.

The verifier recompiles the handwritten definition with the LLVM backend and
fails closed on source drift, revision drift, structural drift, changed parse
or unparse trees, changed rewrite counts, changed intermediate configurations,
changed final environments, changed stuck/error behavior, or relocated
diagnostics.
