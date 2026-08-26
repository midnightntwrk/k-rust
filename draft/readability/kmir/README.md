# Readable KMIR qualification

Status: first operational slice qualified; KEVM, KWasm, and IMP regressions green, 2026-08-26 JST

## Pinned authority

The external acceptance corpus is the clean checkout at `../../../../inspirations/runtimeverification/mir-semantics`:

- commit `4d793252bcd77091ee759ca6cd1629db41ed5496`;
- K release `7.1.337` from `deps/k_release`, exactly matching KRS;
- core semantics in `kmir/src/kmir/kdist/mir-semantics/`;
- parser fixtures and representative Rust programs under `kmir/src/tests/integration/data/`.

The KMIR checkout and the recovery evidence remain read-only.
KRS owns this fixture, its structured-body adapter, and every generated acceptance artifact.

## Corpus inventory

The selected production roots have the following principal size and rule shapes:

| file | lines | syntax declarations | rules | `requires` | `owise` |
|---|---:|---:|---:|---:|---:|
| `kmir.md` | 742 | 31 | 99 | 28 | 11 |
| `mono.md` | 76 | 10 | 0 | 0 | 0 |
| `body.md` | 518 | 77 | 0 | 0 | 0 |
| `rt/configuration.md` | 78 | 2 | 0 | 0 | 0 |
| `rt/data.md` | 2,488 | 77 | 316 | 121 | 23 |
| `ty.md` | 821 | 159 | 0 | 0 | 0 |

KMIR contains no checked-in K `claim` sentence.
Its proving corpus is generated through the Python tooling from Rust and Stable MIR inputs.
Full KMIR additionally uses generic K lists, nested configuration, call stacks, function and type tables, projections, references, allocations, bytes, strictness-generated evaluation, priorities, `owise`, and extensive guarded rules.
This milestone does not claim those features.

## Representative operational slice

The first slice follows KMIR's `#execBlockIdx` / `#execBlock` / `#execStmts` / `#execStmt` / `#execTerminator` pipeline:

1. a basic-block graph and ordered recursive statement lists;
2. a block-lookup map and a distinct locals map;
3. constant and copied-local operands;
4. local assignment through a staged `#setLocalValue` analogue;
5. integer addition through a staged binary-operation analogue;
6. `Goto` and Boolean `SwitchInt` terminators;
7. top-level `Return` of local `_0` into the return-value cell;
8. one all-path native claim spanning installation, sequencing, local reads and updates, a graph edge, a conditional branch, and return.

KMIR receives Stable MIR bodies through generated JSON and converts `BasicBlocks` to K's builtin `List` before execution.
The fixture deliberately replaces only that front-end boundary with a right-recursive `BlockProgram` installer.
Installation checks each constructor as a basic block and persistently builds `Map<Int, BasicBlock>`; operational lookup and execution then follow the source pipeline.

The fixture represents locals directly as `Map<Int, MirValue>` rather than KMIR's typed `List` entries.
This second narrowing omits type metadata and projections while retaining the selected semantics of indexed reads, persistent updates, read-before-write staging, and local `_0` as the program result.

## Source mapping

- `kmir.md`: block-index lookup, block expansion, ordered statement execution, assignment dispatch, `Goto`, Boolean `SwitchInt`, and top-level `Return`;
- `body.md`: `BasicBlock`, `StatementKind::Assign`, `Rvalue`, `Operand`, `Goto`, `SwitchInt`, and `Return` syntax families;
- `rt/configuration.md`: computation, current body, locals, and return-value state;
- `rt/data.md`: copied-local reads, `#setLocalValue`, `rvalueUse`, `rvalueBinaryOp`, and integer addition;
- `schema-parse/basicblock1`, `statementassign1`, `terminatorgoto`, and `terminatorreturn`: concrete serialized constructor shapes;
- `prove-rs/if.rs`, `else.rs`, and `const-arithm-simple.rs`: representative Boolean branch and local-arithmetic programs exercised by KMIR's integration suite.

## Unsupported shapes recorded before implementation

Protocol-16 ordinary fixed-cell rewrites already scale to the selected state, and the IMP milestone already qualifies finite-map matching and persistent update.
Constructor-pattern branch rules avoid rule-table guards.
Explicit evaluation commands preserve read-before-write staging without claiming K's full strictness protocol.

Implementation exposed one independent-expansion gap, K1.
A source module that both authored `map!` in a claim and used readable map extras required an explicit `use k::map`, while reference expansion unconditionally inserted the same import for the readable rules.
The resulting duplicate macro import made the independently expanded crate fail to compile.
KRS now detects an existing equivalent use tree before inserting its generated map-macro import.
The focused compiler regression proves that attributes do not hide an existing import and that unrelated imports do not suppress insertion.
This is an import-hygiene fix only; descriptor protocol 16 and Definition IR schema 9 remain unchanged.

Deferred corpus shapes include generic builtin-list matching and indexing, typed locals, projections, moves and invalidation, references, memory and allocation stores, nested and multiplicity cells, call-stack frames, function calls, unwind and panic paths, integer truncation, checked overflow aggregates, arbitrary `SwitchInt` branch lists, priorities, `owise`, symbolic generated lookup functions, and KMIR's Python-generated proof workflow.
A later slice may extend KRS only when one of these shapes is selected as acceptance evidence.

## Acceptance contract

The checked-in gate must establish deterministic collection and expansion, formatting, warnings-denied Clippy, focused rust-analyzer probes, emitted-K compilation under K 7.1.337, native behavior for the selected graph and local-state paths, a closed native all-path proof, and unchanged complete IMP, KWasm, and KEVM regressions.
Pins may be updated only after reviewing emitted K and structured behavior.

The canonical KRS port is `semantics/kmir`, the corpus is `tests/kmir/corpus.toml`, and the fail-closed entry point is `python3 tests/kmir/verify.py`.

## Qualification result

The complete fixture gate passes with the K1 import-hygiene fix and no syntax, protocol, semantic IR, Definition IR, or runtime extension:

```text
PASS readable KMIR operational slice: 103 descriptors; 11 executions; 1 native proof; protocol 16; K 7.1.337
```

The behavior matrix covers direct top-level return, constant assignment, ordered copied-local assignment, integer addition, nonadjacent `Goto`, both Boolean `SwitchInt` outcomes, read-before-overwrite staging, insertion-order-independent block lookup, and both outcomes of the combined four-block specimen.
Every execution consumes the recursive body, installs the expected number of blocks, halts with an empty computation, and matches its locals and return value.
The structured behavior SHA-256 is `e150e7a86c513ec5966185fe079d8f58c34c57a66e73991ff8ac9b1f9aaee5c5`.

The concrete all-path claim spans body installation, four map-backed block lookups, ordered statements, constant and copied operands, integer addition, `Goto`, true `SwitchInt`, local `_0`, and top-level return.
It closes with `#Top` through native `kprove`.

The normalized native `definition.kore` SHA-256 is `5b05ecb38c803c8ae95d517e46f10e2725ac74f45f3cb7867cf85e600c818f7c`.
Normalization is limited to the temporary semantics path and K-generated sort-membership binder names under the previously qualified policy.
Six focused definition and hover probes pass with zero rust-analyzer diagnostics.

The unchanged KEVM and KWasm gates pass with 14 and 32 executions respectively and one native proof each.
The complete IMP M4 gate passes with 124 descriptors, 98 parsed and 244 compiled sentences, native KORE parity at 1,206/1,206 sentences, unchanged behavior evidence `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`, all 21 proof specifications, and unchanged compatibility evidence `13ddab23139f1c64cc4bebf2402b4aa16c96c142f15310b9451113a7d4cc7fa6`.
