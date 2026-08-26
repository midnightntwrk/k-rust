# Readable KMIR qualification

Status: builtin-List block adapter removed; KEVM, KWasm, and IMP regressions green, 2026-08-26 JST

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

1. a basic-block graph stored in K's builtin `List` and ordered recursive statement lists;
2. direct indexed block lookup and a distinct locals map;
3. constant and copied-local operands;
4. local assignment through a staged `#setLocalValue` analogue;
5. integer addition through a staged binary-operation analogue;
6. `Goto` and Boolean `SwitchInt` terminators;
7. top-level `Return` of local `_0` into the return-value cell;
8. one all-path native claim spanning builtin-list lookup, sequencing, local reads and updates, graph edges, a conditional branch, and return.

KMIR receives Stable MIR bodies through generated JSON and converts `BasicBlocks` to K's builtin `List` before execution.
The fixture now preserves that boundary directly as `List<BasicBlock>`.
Execution begins at index zero, retains the program list in state, and projects `PROGRAM [ INDEX ]` to `BasicBlock` before entering the source pipeline.

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

The initial milestone exposed one independent-expansion gap, K1.
A source module that both authored `map!` in a claim and used readable map extras required an explicit `use k::map`, while reference expansion unconditionally inserted the same import for the readable rules.
The resulting duplicate macro import made the independently expanded crate fail to compile.
KRS detects an existing equivalent use tree before inserting its generated map-macro import.
The focused compiler regression proves that attributes do not hide an existing import and that unrelated imports do not suppress insertion.
K1 is an import-hygiene fix only.

The current milestone adds K's associative builtin `List` as a shared KRS surface in descriptor protocol 18 and Definition IR schema 11.
The closed operation catalog is `.List`, `ListItem`, associative concatenation, indexed lookup, persistent indexed update, and `size`.
Element sorts remain explicit in Semantic and Definition IR so indexed lookup emits the required typed projection, such as `{PROGRAM:List [ INDEX:Int ]}:>BasicBlock`.
The source emitter and native `k-rust` adapter use the pinned `LIST` labels, and focused tests cover registry identity, descriptor arity, IR validation, exact K source, reference expansion, and native adaptation.

Deferred corpus shapes include typed local-list entries, projections, moves and invalidation, references, memory and allocation stores, nested and multiplicity cells, call-stack frames, function calls, unwind and panic paths, integer truncation, checked overflow aggregates, arbitrary `SwitchInt` branch lists, priorities, `owise`, symbolic generated lookup functions, and KMIR's Python-generated proof workflow.
A later slice may extend KRS only when one of these shapes is selected as acceptance evidence.

## Acceptance contract

The checked-in gate must establish deterministic collection and expansion, formatting, warnings-denied Clippy, focused rust-analyzer probes, emitted-K compilation under K 7.1.337, native behavior for the selected graph and local-state paths, a closed native all-path proof, and unchanged complete IMP, KWasm, and KEVM regressions.
Pins may be updated only after reviewing emitted K and structured behavior.

The canonical KRS port is `semantics/kmir`, the corpus is `tests/kmir/corpus.toml`, and the fail-closed entry point is `python3 tests/kmir/verify.py`.

## Qualification result

The complete fixture gate passes with native builtin-list program storage and lookup:

```text
PASS readable KMIR operational slice: 94 descriptors; 11 executions; 1 native proof; protocol 19; K 7.1.337
```

The behavior matrix covers direct top-level return, constant assignment, ordered copied-local assignment, integer addition, sequential and nonadjacent indexed `Goto`, both Boolean `SwitchInt` outcomes, read-before-overwrite staging, third-block lookup in a three-element list, and both outcomes of the combined four-block specimen.
Every execution preserves the expected builtin program list, observes its exact block count, halts with an empty computation, and matches its locals and return value.
The structured behavior SHA-256 is `dd173192fa881b744030cef7b57aca8f646e2788b21397d00c826db0d41b4abf`.

The concrete all-path claim spans four builtin-list block lookups, ordered statements, constant and copied operands, integer addition, `Goto`, true `SwitchInt`, local `_0`, and top-level return.
It closes with `#Top` through native `kprove`.

The normalized native `definition.kore` SHA-256 is `d71738e52d51bba416ee52391bf71a7ba9bf9a017b839c3493547f0b1f3c8d34`.
Normalization is limited to the temporary semantics path and K-generated sort-membership binder names under the previously qualified policy.
Six focused definition and hover probes pass with zero rust-analyzer diagnostics.

Descriptor protocol 19 and Definition IR schema 12 add K's selected `INT.mod` identity for the source-faithful KEVM arithmetic tranche.
KMIR behavior, emitted K, and native proof evidence remain unchanged because this baseline does not consume that shared operation.
The KEVM and unchanged KWasm gates pass at protocol 19 and Definition IR schema 12 with 25 and 32 executions respectively; KEVM closes two native proofs and KWasm closes one.
The complete IMP M4 gate passes at the same versions with 124 descriptors, 98 parsed and 244 compiled sentences, native KORE parity at 1,206/1,206 sentences, unchanged behavior evidence `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`, all 21 proof specifications, and unchanged compatibility evidence `13ddab23139f1c64cc4bebf2402b4aa16c96c142f15310b9451113a7d4cc7fa6`.
