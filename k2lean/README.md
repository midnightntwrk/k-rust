# k2lean

k2lean generates a Lean 4 library from a K definition compiled by krust: one Lean type per sort, the definition's functions as Lean definitions, its rewrite rules as an inductive `Step` relation with an executable `step`, its K equations as proved theorems, and proofs that tie them together.
On top of a generated library it proves preserved invariants (a property kept by every rule, for every program), written either as a K function or as a Lean predicate.
It is part of k-rust's repository: the generator is a member of k-rust's workspace and reads KORE through `k-rust-kore`, at whatever commit the checkout is.

## Layout

| path | content |
|---|---|
| `crates/k2lean` | the generator (`k2lean gen`, and the commands of `docs/design.md`, §4), with its unit and snapshot tests |
| `lean/prelude` | `KPrelude`: the hooks, matching combinators and tactics every generated library uses, and the invariant core (`Preserved`, `k2l_preserve`) |
| `lean/claims` | `KClaims`: K reachability claims over a transition relation, and the claim tactic |
| `demos` | K inputs, hand-written Lean projects over generated libraries, and `regen.sh`, which regenerates and builds them |
| `generated` | where the libraries are generated; git tracks only each library's open lists and hand-written invariant module |
| `tests` | the gate (`gate.sh`, `gate-check.py`, `libs.sh`, and each area's registrations in `areas/`), its baseline and recorded outputs (one file and directory per area), kimp's golden cases, and the generator's fixtures |
| `pipelines` | human-run scripts that generate and build KEVM (`kevm.sh`, with KEVM's termination file) and KMIR (`kmir.sh`) in the arity-indexed term universe; not gate tiers |
| `docs` | `design.md` (what is generated and why it is sound, the encodings, measured costs, and what is open) and `invariants.md` (the user guide to preserved invariants) |

## Quick start

From the root of a k-rust checkout with the reference checkouts of `README.md`, "Compatibility evidence" (`k`, `imp-semantics`), krust built (`cargo build --release -p k-rust --bin krust`) and Lean's `elan` on `PATH`:

```sh
cargo build --release --locked -p k2lean      # target/release/k2lean
k2lean/demos/regen.sh                         # generate kimp, KRS IMP and two more, build the four IMP demos
k2lean/tests/gate.sh light                    # the regression gate's light tier
```

Each generated project pins Lean v4.34.0, which elan installs on first use.
A clean light gate builds several Lean libraries: about 1,550 s of CPU and 4 GB of peak memory (1,100 s wall on a shared 32-CPU host under a load of about 30, 2026-10-24, Lean v4.34.0); a rerun builds only what changed.
To generate a library of your own definition:

```sh
target/release/krust kcompile my.k --main-module MY --syntax-module MY-SYNTAX --output-directory out/my
mkdir -p out/lean && cp -a k2lean/lean/prelude out/lean/
target/release/k2lean gen --kore out/my/definition.kore --runtime out/my/runtime.json \
  --out out/generated/my --name My --prelude ../../lean/prelude
(cd out/generated/my && lake build My.Equations > build.log 2>&1)
```

An equation whose generated proof fails (here, a `Set` equation of `domains.md`) is turned into a named open obligation, and the library is generated again:

```sh
touch out/generated/my/open-obligations.txt
target/release/k2lean open-from-log out/generated/my/My/Equations.lean out/generated/my/build.log \
  out/generated/my/open-obligations.txt
target/release/k2lean gen --kore out/my/definition.kore --runtime out/my/runtime.json \
  --out out/generated/my --name My --prelude ../../lean/prelude \
  --open-obligations out/generated/my/open-obligations.txt
(cd out/generated/my && lake build My My.Equations MyTest.Axioms)
```

`docs/invariants.md`, §2, explains the flags and the work-tree layout.

## Demos

| demo | shows |
|---|---|
| `demos/ImpRel` | the KRS IMP port (`demos/k/krs-imp`) and kimp are bisimilar: `k2lean relate` pairs their rules and generates the proof |
| `demos/SimpleRel` | SIMPLE and a variant of it (`tests/simple-variant.py`: constructors with other symbols, rules in another order) are bisimilar (priorities, free-key matches on the thread cell map, typed cell maps): `k2lean relate --split true` generates the proof, one module per simulation; human-run (`pipelines/simple-rel.sh`, per-sort), 7 minutes and 9 GB on top of the two libraries (`docs/design.md`, §9) |
| `demos/PeanoRel`, `demos/CellMapRel`, `demos/PickRel` | the fixtures `tests/fixtures/peano` (an `owise` priority, recursive and mutual functions), `tests/fixtures/cellmap` (a free-key rule over the typed cell map of `<worker>`s) and `tests/fixtures/pick` (functions with free-key map patterns) are each bisimilar to themselves under two namespaces: the light gate's cheap pins of `relate` |
| `demos/ImpTypes` | kimp is type-sound for a K type checker (`demos/k/imp-typing.k`): `k2lean soundness` generates the runtime typing, preservation, progress and `soundness`; `Store.lean` holds the store typing and the cases of the three rules that read or write the store |
| `demos/ImpMut` | a mutant of kimp (`demos/k/kimp-mutant`) diverges from kimp, proved on a concrete configuration |
| `demos/ImpUnroll` | kimp and a variant whose `while` unrolls in one step less (`tests/kimp-unroll.py`) are stuttering bisimilar: `k2lean refine` generates all 316 case parts and the non-local part of the relation, from the split of `while` (`--hand-module none`) |
| `demos/RaceConf` | every schedule of the fixture `tests/fixtures/race` (workers adding to a shared accumulator) ends in one configuration: `k2lean confluence` generates and proves all 9 joins of pairs of rules |
| `demos/SimpleConf` | SIMPLE's steps of two threads join (`k2lean confluence --threads threads`, one view per rule, nothing per pair), so every schedule ends in one configuration given the joins it leaves as hypotheses: those of one thread and those involving a rule that inserts or removes threads, races on a cell, or enables a rule of a rank before (heavy tier) |
| `demos/ImpNI` | kimp's termination-insensitive noninterference for a two-level security checker in K (`demos/k/imp-sec.k`), stated by `k2lean noninterference` with its 240 obligations, all discharged by the relation it generates from the checker (`ImpNI/Levels.lean`, `Stack.lean`, `Proof.lean`; the store lemmas and 5 cases by hand in `ImpNI/Store.lean`); `ImpNI/Examples.lean` shows the hypotheses hold of a secure program and the checker rejects explicit and implicit flows |
| `demos/KrsImpTyping` | every KRS IMP rule preserves the declared cell type `env: Map<Id, Value>`, from the KRS sidecar |
| `demos/ImpWrites` | a kind 2 invariant of kimp that walks the `<k>` cell |
| `demos/k/kimp-inv`, `demos/k/kimp-keys`, `demos/k/simple-inv` | kind 1 invariants written as K functions |
| `demos/claims` | K claims of kimp proved in Lean, generically or by hand; claims under an invariant; the termination of kimp's expressions |
| `demos/ImpRelClaims` | a K claim proved on kimp holds for the KRS IMP port, through `relate`'s bisimulation |
| `demos/ImpUnrollClaims` | kimp's claims hold for its unrolling variant, through `refine`'s stuttering bisimulation |

## Claims

`k2lean claims` states the `claim` sentences of specifications compiled with `krust kcompile --for-proving` as Lean propositions over a generated library, and proves them with the claim tactic of `lean/claims` (`KClaims`); the gate runs it on kimp's specs (`tests/gate.sh`, heavy tier):

```sh
target/release/k2lean claims --kore out/my/definition.kore --spec out/my-spec/definition.kore \
  --out out/generated/my-claims --name MyClaims --semantics My --semantics-path ../my \
  --kclaims-path ../../lean/claims [--open OPEN.txt] [--hand MODULE]…
```

| option | does |
|---|---|
| `--open FILE` | claims (and induction obligations) that get no generic proof: false ones, or ones proved by hand in a `--hand` module |
| `--assume-invariant NAME` | every claim is stated for the configurations satisfying the preserved invariant `NAME` (`NAME.preserved : Preserved Step NAME`; `--invariant-preserved`, `--invariant-module`), which its proof carries along every step; `--invariant-unfold FILE` gives the unfolding set, one Lean name per line (default: the `invariant-unfold.txt` that `gen --invariant` writes in the semantics' library, `--semantics-path`) |
| `--induction FILE` | the termination of a sublanguage of a syntax sort (TOML: classes and constructor typings), by structural induction, one obligation per typing |
| `--transfer REL` | every proved claim carried to the definition `--transfer-target B` along `REL.bisim`, one theorem per claim, into the module `--transfer-out FILE` (namespace `--transfer-ns`); repeatable, the other `--transfer-…` options apply to the last one |
| `--transfer-kind stutter` | `REL.bisim` is `refine`'s stuttering bisimulation, not `relate`'s: one-path claims carry, and all-path ones only as one-path claims unless `--transfer-det MODULE` names `B`'s determinism module (`B.Step.deterministic`), on which every claim keeps its modality |

A claim proved on one definition holds on another that `k2lean relate` proves bisimilar: `KClaims.AF.of_bisim` and its `EF` and `Reach` forms (`demos/ImpRelClaims`); along `refine`'s stuttering bisimulations, `KClaims.EF.of_stutter` (`demos/ImpUnrollClaims`).
`docs/design.md`, §3.8, says what each statement means and how it is proved.

## Type soundness

`k2lean soundness` generates the type soundness of a semantics for a type checker written as a second K definition over its syntax, except what is specific to the language's store: the hand module types the store and proves the cases of the rules that read or write it (`demos/ImpTypes`, `tests/areas/soundness.sh`, `libs_soundness`):

```sh
target/release/k2lean soundness --kore-a out/my/definition.kore --name-a My \
  --kore-b out/my-typing/definition.kore --name-b MyTypes --ns MySound \
  --typing typeOf,wt --store-cell env --store-typing envTy \
  --out-typing MySound/Typing.lean --out-soundness MySound/Soundness.lean
```

It needs the two libraries and the translation of programs that `k2lean relate --roots` writes (`MySound/Tr.lean`; `--tr-module`), and writes `Typing.lean`, which the hand module `MySound/Store.lean` (`--hand-module`) imports, and `Soundness.lean`, which imports it; `docs/design.md`, §3.3, says what each part states and what is supported.

## Scaffolds

Three commands state a theorem whose proof needs an argument no generator has, and reduce it to named obligations: they prove the reduction (`KPrelude.Scaffold`) and the obligations a generic argument closes, and take the rest from a hand module; `docs/design.md`, §3.4 to §3.7, says what each generates and what it leaves (the calls are in `tests/areas/relational.sh`, `confluence.sh` and `noninterference.sh`):

```sh
# a stuttering bisimulation between A and B, from relate's per-rule simulations
target/release/k2lean relate --kore-a A/definition.kore --name-a A --kore-b B/definition.kore --name-b B \
  --ns AB --per-rule true --out AB/Tr.lean --report AB/correspondence.toml
target/release/k2lean refine --kore-a A/definition.kore --name-a A --kore-b B/definition.kore --name-b B \
  --ns AB --correspondence AB/correspondence.toml --open AB/open-cases.txt --out AB/Refine.lean
# confluence modulo scheduling, observing the cells --obs names (--report-only: the classification of the pairs)
target/release/k2lean confluence --kore A/definition.kore --name A --ns AConf --obs out \
  [--join local] [--open OPEN.txt] --out AConf/Confluence.lean --report AConf/confluence.toml
# noninterference, reduced to a relation on pairs of runs (with --checker-kore: the relation generated)
target/release/k2lean noninterference --kore A/definition.kore --name A --ns ANI --store-cell env \
  --program-sort SortStmt --params "(G : Sec.SortMap)" --secure "secure G" --low-eq "lowEq G" --out ANI/NI.lean \
  [--checker-kore Sec/definition.kore --checker-name Sec --lev lev --sec sec --conf conf --open ANI/open.txt --out-dir ANI]
```

| option | does |
|---|---|
| `relate --per-sort-terms true` | the two libraries are in the per-sort universe (`gen --per-sort-terms`); by default they are in the arity-indexed one and the translation is one function over `A`'s term family (`docs/design.md`, §3.2); `--arity-terms true`, the former opt-in, changes nothing |
| `soundness --per-sort-terms true` | the two libraries are in the per-sort universe (`gen --per-sort-terms`); by default `Typing.lean` and `Soundness.lean` are written for the arity-indexed one (`docs/design.md`, §3.3) |
| `relate --per-rule true` | when not every rule pairs: one simulation lemma per pair of corresponding rules (`fwd.r`, `bwd.r`) instead of the bisimulation |
| `relate --split true` | the bisimulation in one module per simulation (`OUT/Base.lean`, `AppFwd`, `AppBwd`, `Forward`, `Backward`, imported by `OUT.lean`), so that Lean builds them in separate processes: for definitions of SIMPLE's size |
| `refine --open FILE` | the case parts the hand module proves (`KIND RULE`, `KIND` one of `fwd_tr`, `fwd_x`, `bwd_tr`, `bwd_x`); `--hand-module` (default `NS.Relation`), `--extra`, `--measure-a`, `--measure-b` name what it supplies (default `X`, `μ`, `ν`); `--hand-module none`: no hand module, `X` and the measures generated from one step of `B` that `A` takes in two (`--tr-module`, default `NS.Tr`) |
| `confluence --threads CELL` | the views of the rules by the binding of the cell map in `CELL` they update (`--ns`, `--obs`, `--out`; `docs/design.md`, §3.6): two steps of different bindings, or of a binding and the other cells, join generically, the same-thread joins and the other pairs are the hypotheses `SameThreadJoins` and `OpenJoins` of `terminal_unique_of`; the report adds what is left open (`[threads]`) |
| `confluence --open FILE` | the pairs of rules the hand module joins (`RULE \| RULE`); `--hand-module` (default `NS.Hand`) and `--hyp` (default `H`) name the program hypothesis, `--join local` asks for `μ` and `μ_dec` |
| `noninterference --params`, `--secure`, `--low-eq` | the hand module's parameters and predicates the statement uses; `--hand-module` (default `NS.Hand`) |
| `noninterference --checker-kore` | the relation from a two-level checker (`--lev`, `--sec`, `--conf` name its functions): `Levels.lean`, `Stack.lean`, `Proof.lean` in `--out-dir`, around the hand module `NS.Store` (`--store-module`), which proves the per-rule cases `--open` lists (`KIND RULE`, `KIND` one of `cq`, `sq`, `same`) |
| `noninterference --per-sort-terms true` | with `--checker-kore`, the libraries are in the per-sort universe (`gen --per-sort-terms`); by default the relation's modules are written for the arity-indexed one (`docs/design.md`, §3.7) |

## Large definitions

The default term universe is one inductive family indexed by the sorts, which Lean builds at KEVM's size; `gen --per-sort-terms` writes one Lean type per sort instead, in one `mutual` block, the default until 2026-10-25, which some of the gate's libraries and demos still use (`docs/design.md`, §2.1, lists them and why); `gen --arity-terms`, the former opt-in, changes nothing.
Determinism is proved along the rule index rather than over all pairs of rules, on both encodings (`gen --det-pairs` keeps the proof by pairs for the per-sort one); `docs/design.md`, §2.1 and §3.1, describes both and what they cost.
`pipelines/kevm.sh` and `pipelines/kmir.sh` run KEVM and KMIR through the generator and Lean, step by step, `pipelines/simple-rel.sh` relates SIMPLE to its variant (`demos/SimpleRel`), and `pipelines/kevm-inv.sh` proves an invariant of KEVM's semantics, every account stored under its own `<acctID>`, for all 358 rules (`docs/invariants.md`, §5.3); `docs/design.md`, §9, lists what is open.
`pipelines/kevm.sh` builds KEVM's test driver (`driver.md`) by default and the semantics alone (`evm.md`, main module `EVM`) with `TARGET=evm`; its `equations` step builds KEVM's `Equations` part by part, and its `det` step builds the determinism modules and then `KEvmTest.DetAxioms`, the axiom guard of determinism alone, which does not need KEVM's `Equations`.
A definition whose rules overlap gets `Step.deterministic_of` (no listed pair applies) instead of `Step.deterministic`, and each listed pair a witness, a configuration where both rules step to different results; a witness holding a `String` or token literal longer than `--det2-long-literal N` characters (default 256), or a `Bytes` literal longer than `--det2-long-bytes N` bytes (default 131,072), is reported and not checked, and its pair stays listed.

## Testing

`cargo test -p k2lean` runs the generator's tests, which the workspace suite includes.
`tests/gate.sh light|heavy` is the regression gate; `docs/testing.md` of the repository describes the tiers and when they are owed (`k2lean-light`, `k2lean-heavy` in `scripts/gates.toml`).

## Third-party material

Some test data and demo inputs derive from K's sources and from kimp (runtimeverification/imp-semantics):

- `demos/k/kimp-mutant` is kimp's `imp.k`, `calc.k` and `expr.k` at the pin of `scripts/reference-differential.toml`, with one rule changed;
- `demos/claims/specs/imp-ifs-uint64-spec.k` is kimp's `examples/specs/imp-ifs-spec.k` with one predicate written out;
- `tests/goldens` records krust and K results on kimp's example programs and on ports of programs of K's tutorial tests, whose texts the cases carry;
- the compiled fixtures and `demos/k/krs-imp/*.kore` contain the K builtin modules that krust compiles into every definition.

This material, from K and from kimp alike, keeps the K Framework's BSD 3-Clause license (`licenses/K-FRAMEWORK-BSD-3-Clause.txt`), and [NOTICE](../NOTICE) lists it; the rest of k2lean is licensed as k-rust is.
