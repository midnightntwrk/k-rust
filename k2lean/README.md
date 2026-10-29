# k2lean

k2lean generates a Lean 4 library from a K definition compiled by krust: its sorts as one term family indexed by sort, the definition's functions as Lean definitions, its rewrite rules as an inductive `Step` relation with an executable `step`, its K equations as theorems (proved by generic tactics where they reach, and listed as open obligations where they do not), and proofs that tie them together.
On top of a generated library it proves preserved invariants (a property kept by every rule, for every program), written either as a K function or as a Lean predicate.
It is part of k-rust's repository: the generator is a member of k-rust's workspace and reads KORE through `k-rust-kore`, at whatever commit the checkout is.

## Layout

| path | content |
|---|---|
| `crates/k2lean` | the generator (`k2lean gen`, and the commands of `docs/design.md`, §4), with its unit and snapshot tests |
| `lean` | the Lake package `k2lean`, which every generated library requires: `KPrelude` (`lean/prelude`), the hooks, matching combinators and tactics every generated library uses, and the invariant core (`Preserved`, `k2l_preserve`); `KClaims` (`lean/claims`), K reachability claims over a transition relation, and the claim tactic |
| `demos` | K inputs, hand-written Lean projects over generated libraries, and `regen.sh`, which regenerates and builds them |
| `generated` | where the libraries are generated; git tracks only each library's open lists and hand-written invariant module |
| `tests` | the gate (`gate.sh`, `gate-check.py`, `libs.sh`, and each area's registrations in `areas/`), its baseline and recorded outputs (one file and directory per area), kimp's golden cases, and the generator's fixtures |
| `pipelines` | human-run scripts that generate and build KEVM (`kevm.sh`, with KEVM's termination file) and KMIR (`kmir.sh`) in the arity-indexed term universe; not gate tiers |
| `docs` | `product.md` (what k2lean is for, and where work belongs: k2lean, example material, or a project of its own), `contract.md` (what a generated library promises: the specification an optimization loop must leave frozen, and the proofs and derived definitions it may change), `design.md` (what is generated and why it is sound, the encodings, measured costs, and what is open) and `invariants.md` (the user guide to preserved invariants) |

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
K2LEAN=https://github.com/midnightntwrk/k-rust@$(git rev-parse HEAD)   # a commit the URL serves
target/release/k2lean gen --kore out/my/definition.kore --runtime out/my/runtime.json \
  --out out/generated/my --name My --prelude-git "$K2LEAN"
(cd out/generated/my && lake update && lake build My.Equations > build.log 2>&1)
```

The library requires the Lake package `k2lean` (`lean/`: `KPrelude`, `KClaims`) by git at that commit, the revision whose hook models its statements are about; `--prelude PATH` requires a local copy of `lean/` instead, by a path relative to `--out` (the gate and the demos do).

An equation whose generated proof fails (here, a `Set` equation of `domains.md`) is turned into a named open obligation, and the library is generated again:

```sh
touch out/generated/my/open-obligations.txt
target/release/k2lean open-from-log out/generated/my/My/Equations.lean out/generated/my/build.log \
  out/generated/my/open-obligations.txt
target/release/k2lean gen --kore out/my/definition.kore --runtime out/my/runtime.json \
  --out out/generated/my --name My --prelude-git "$K2LEAN" \
  --open-obligations out/generated/my/open-obligations.txt
(cd out/generated/my && lake build My My.Equations MyTest.Axioms)
```

`docs/invariants.md`, §2, explains the flags and the work-tree layout.

A release (`pipelines/release.sh VERSION`) is one commit of k-rust and its tag `k2lean-vVERSION-leanTOOLCHAIN`: the generator and the package at the same version; the release binary is built with `K2LEAN_PACKAGE_GIT=URL@COMMIT`, so that `gen` without `--prelude` requires the package at that commit.

A project of your own uses the generated library through Lake alone (`demos/PkgDemo`, built by the gate): its lakefile requires `k2lean` at the same commit (Lake resolves a package by name, the root's requirement first; the library's root module checks the release, `#k2l_check_prelude`), the generated library by path or git, and any other Lean library. A library with parameters (`class Hooks`: hooks the hook library does not implement, functions without equations) is stated for every implementation of them; the project supplies one, an `@[instance_reducible] def` made a local instance where it is used, possibly from another library (`demos/PkgDemo/Consumer/Consumer/Hooks.lean`), and declares the executables, `def main` applying the generated `{NS}Test.testMain` or `{NS}Bench.benchMain` to its instance. Its lean-toolchain must be the library's (every generated lakefile sets `fixedToolchain`).

## Demos

| demo | shows |
|---|---|
| `demos/ImpRel` | the KRS IMP port (`demos/k/krs-imp`) and kimp are bisimilar: `k2lean relate` pairs their rules and generates the proof |
| `demos/SimpleRel` | SIMPLE and a variant of it (`tests/simple-variant.py`: constructors with other symbols, rules in another order) are bisimilar (priorities, free-key matches on the thread cell map, typed cell maps): `k2lean relate --split true` generates the proof, one module per simulation; a targeted check, not a gate tier (`pipelines/simple-rel.sh`, run when `relate`'s emitters or the family's case and split tactics change), about 17 minutes with `Base` at 771 s and 10.7 GB on top of the two libraries (`docs/design.md`, §9) |
| `demos/PeanoRel`, `demos/CellMapRel`, `demos/PickRel` | the fixtures `tests/fixtures/peano` (an `owise` priority, recursive and mutual functions), `tests/fixtures/cellmap` (a free-key rule over the typed cell map of `<worker>`s) and `tests/fixtures/pick` (functions with free-key map patterns) are each bisimilar to themselves under two namespaces: the light gate's cheap pins of `relate` |
| `demos/ImpTypes` | kimp is type-sound for a K type checker (`demos/k/imp-typing.k`): `k2lean soundness` generates the runtime typing, preservation and `soundness`, from kimp's progress under the typing (`gen --progress`, `var`'s case by hand in `ProgressHand.lean`); `Store.lean` holds the store typing and the preservation cases of the three rules that read or write the store |
| `demos/ImpPlusTypes` | IMP++ of K's tutorial (threads in a cell map, `spawn`/`join`, blocks, K's I/O streams) is type-sound for a K type checker of its programs without variables (`demos/k/impplus-typing.k`): all generated, no hand module (`docs/design.md`, §3.3, "A semantics with threads") |
| `demos/ImpMut` | a mutant of kimp (`demos/k/kimp-mutant`) diverges from kimp, proved on a concrete configuration |
| `demos/ImpUnroll` | kimp and a variant whose `while` unrolls in one step less (`tests/kimp-unroll.py`) are stuttering bisimilar: `k2lean refine` generates all 316 case parts and the non-local part of the relation, from the split of `while` (`--hand-module none`) |
| `demos/RaceConf` | every schedule of the fixture `tests/fixtures/race` (workers adding to a shared accumulator) ends in one configuration, proved twice with no premise: by worker (`k2lean confluence --threads workers --slots`, workers without `<k>`; 8 slots, all generic) and with every pair of rules a slot (`k2lean confluence --slots`, `RaceConf.Pairs`; 9 of 9 generic) |
| `demos/UtxoConf` | the fixture `tests/fixtures/utxo` (coroutines in a cell map over a UTXO ledger, ids derived from content, outputs spent by their owner: create, spend, spawn, yield, a one-shot resume of a child): steps of two processes join generically (`k2lean confluence --threads procs`), the joins left open as slots (`--slots`): one process against itself, matched at one or two bindings, and the overlaps at one ledger binding generically (12), two spawns by the hand module `UtxoConf/Hand.lean` (1): confluent with no premise, `UtxoConf.terminal_unique` (light tier) |
| `demos/HandoffConf` | the fixture `tests/fixtures/handoff` (the coroutine handoff shape: a coordination script's tasks run when their inputs are ready, and a resume runs a process's whole segment as one step, its next state and output the functions `next` and `out`, parameters of the definition (`class Hooks`), so the theorem holds whatever the lower layer computes; ids derived from content): steps of two tasks join generically, including two that read one input (`k2lean confluence --threads tasks`), the joins left open as slots (`--slots`): the root's two forks, one task against itself, and a creation against a resume generically (13), two tasks claiming one creation or one resume by the hand module `HandoffConf/Hand.lean` (5) under the script's well-formedness `wf`, a K function of the fixture (no step of a process named twice by the pending tasks), whose preservation `gen --invariant wf@T` proves with no hand case (`Handoff.Invariant`; `--assume-invariant`; read order-free by `HandoffConf/Claims.lean`): `HandoffConf.terminal_unique`, with `wf` the only hypothesis (light tier) |
| `demos/HandoffSeqRel` | the fixture `tests/fixtures/handoffseq` (the same coordination script run in its order: one instruction after the other, with the same readiness and the same lower layer) into `handoff` (any ready task runs): a run of the script to its end is a run of `handoff` (each instruction a fork, its step and `done`), so through `HandoffConf.terminal_unique` every run of `handoff` from the script to a terminal configuration ends with the same processes and values, `HandoffSeqRel.result_unique`; the script's well-formedness is not assumed but follows from the run in order. The simulation is by hand (the two configurations differ, so `relate` does not apply); the composition is the prelude's `KPrelude.Forward.result_unique_of`, and the map lemmas `KPrelude.MapRep` (light tier) |
| `demos/DrfConf` | the fixture `tests/fixtures/drf` (`race` with each worker writing its count to the accumulator once, the last write winning): by worker (`k2lean confluence --threads workers --slots`), 7 slots generic and the slot of two writes listed `\| refuted two-workers`: two runs of the program `spawn(1); spawn(2); done` (`tests/fixtures/drf/witnesses`) end with different `<acc>`, found in the elaborator and checked by the kernel (`witness.«two-workers».refutes`), so the definition is not confluent and the slot, the only one not proved, is refuted (`DrfConf.join.open.put.put.refuted`; no hand Lean) (light tier) |
| `demos/SimpleConf` | SIMPLE's steps of two threads join (`k2lean confluence --threads threads --slots`, one view per rule, nothing per pair), so every schedule ends in one configuration given the joins it leaves: of its 1,128 slots, 266 of one thread are proved generically, and 862 are open (442 of one thread, 92 races on a cell, 328 where a step enables a rule of a rank before; `open-joins.txt`). They are false together: two runs of SIMPLE's `div-nondet` print different results (`--witnesses`, found in the elaborator and checked by the kernel), so `Open.refuted` (generated), and the theorem holds of no program until it is stated under a program hypothesis (heavy tier) |
| `demos/ImpNI` | kimp's termination-insensitive noninterference for a two-level security checker in K (`demos/k/imp-sec.k`), stated by `k2lean noninterference` with its 240 obligations, all discharged by the relation it generates from the checker (`ImpNI/Levels.lean`, `Stack.lean`, `Proof.lean`; the store lemmas and 5 cases by hand in `ImpNI/Store.lean`); `ImpNI/Examples.lean` shows the hypotheses hold of a secure program and the checker rejects explicit and implicit flows |
| `demos/ContractNI` | noninterference up to disclosure for the fixture `tests/fixtures/contract`, a contract with private state (private answers from `witness()`, a public ledger whose every operation, reads included, goes to a public transcript with each `emit`, `disclose(E)`), with its checker in K, the fixture `tests/fixtures/contractsec`: two runs of an accepted program from one ledger and two private inputs, that both end and disclosed the same values, end with the same ledger and transcript (`k2lean noninterference --inputs --observe --disclosed`; 105 obligations, 199 of 204 per-rule cases generic, the store lemmas and 5 cases by hand in `ContractNI/Store.lean`); `ContractNI/Examples.lean` shows the hypotheses hold of a contract that branches on a disclosed private condition, and refutes the explicit flow, which the checker rejects, by two runs (light tier) |
| `demos/KrsImpTyping` | every KRS IMP rule preserves the declared cell type `env: Map<Id, Value>`, from the KRS sidecar |
| `demos/ImpWrites` | a kind 2 invariant of kimp that walks the `<k>` cell |
| `demos/ImpPlusFresh` | a kind 2 invariant of IMP++ that K cannot state: every store location is below K's generated counter and every thread id at most it, so the location `int` allocates and the id `spawn` gives are not keys yet (`store_fresh`, `thread_fresh`); 60 of 62 rules by `k2l_preserve`, `int` and `spawn` by hand |
| `demos/k/kimp-inv`, `demos/k/kimp-keys`, `demos/k/simple-inv` | kind 1 invariants written as K functions |
| `demos/claims` | K claims of kimp proved in Lean, generically or by hand; claims under an invariant; the termination of kimp's expressions |
| `demos/ImpRelClaims` | a K claim proved on kimp holds for the KRS IMP port, through `relate`'s bisimulation |
| `demos/ImpUnrollClaims` | kimp's claims hold for its unrolling variant, through `refine`'s stuttering bisimulation |
| `demos/PkgDemo` | a user's project through Lake alone: a generated library (the `params` fixture) required with `k2lean` by git, its hooks implemented by another library (`HexLib`), a generated theorem at that instance, a run, and the generated run driver as the project's executable |

## Claims

`k2lean claims` states the `claim` sentences of specifications compiled with `krust kcompile --for-proving` as Lean propositions over a generated library, and proves them with the claim tactic of `lean/claims` (`KClaims`); the gate runs it on kimp's specs (`tests/gate.sh`, heavy tier):

```sh
target/release/k2lean claims --kore out/my/definition.kore --spec out/my-spec/definition.kore \
  --out out/generated/my-claims --name MyClaims --semantics My --semantics-path ../my \
  --kclaims-path ../../lean [--open OPEN.txt] [--hand MODULE]…
```

| option | does |
|---|---|
| `--open FILE` | claims (and induction obligations) that get no generic proof: false ones, or ones proved by hand in a `--hand` module; `NAME \| refuted R` and `NAME \| proved R` name the hand theorem, which `NSTest/Hand.lean` checks (`#k2l_refuted`) |
| `--assume-invariant NAME` | every claim is stated for the configurations satisfying the preserved invariant `NAME` (`NAME.preserved : Preserved Step NAME`; `--invariant-preserved`, `--invariant-module`), which its proof carries along every step; `--invariant-unfold FILE` gives the unfolding set, one Lean name per line (default: the `invariant-unfold.txt` that `gen --invariant` writes in the semantics' library, `--semantics-path`) |
| `--induction FILE` | the termination of a sublanguage of a syntax sort (TOML: classes and constructor typings), by structural induction, one obligation per typing |
| `--transfer REL` | every proved claim carried to the definition `--transfer-target B` along `REL.bisim`, one theorem per claim, into the module `--transfer-out FILE` (namespace `--transfer-ns`); repeatable, the other `--transfer-…` options apply to the last one |
| `--transfer-kind stutter` | `REL.bisim` is `refine`'s stuttering bisimulation, not `relate`'s: one-path claims carry, and all-path ones only as one-path claims unless `--transfer-det MODULE` names `B`'s determinism module (`B.Step.deterministic`), on which every claim keeps its modality |

A semantics whose `Step` is not a function (overlapping rules, strictness in two positions, matches of several cell-collection elements) is explored by every successor, and where those do not reduce on a symbolic part, by the cases of `Step` (`design.md` §3.8; the gate's IMP++ and kstrict claims).
A claim may apply a function that no rule of the definition applies (KEVM's `MerkleUpdate`, `#padRightToWidth`): it is part of the definition, so the library defines it too when generated with `gen --spec FILE` (repeatable, the spec's compiled `definition.kore`).
`gen --spec` lists the library's functions in `functions.txt`, which `claims` reads beside the library (`--semantics-path`); a claim that needs a function the library does not define is not stated, and `claims` names the functions in a note.

A claim proved on one definition holds on another that `k2lean relate` proves bisimilar: `KClaims.AF.of_bisim` and its `EF` and `Reach` forms (`demos/ImpRelClaims`); along `refine`'s stuttering bisimulations, `KClaims.EF.of_stutter` (`demos/ImpUnrollClaims`).
`docs/design.md`, §3.8, says what each statement means and how it is proved.

## Type soundness

`k2lean soundness` generates the type soundness of a semantics for a type checker written as a second K definition over its syntax, except, for a language with a store, what is specific to it: a hand module types the store and proves the cases of the rules that read or write it (`demos/ImpTypes`; `demos/ExprTypes` and `demos/ImpPlusTypes` need none; `tests/areas/soundness.sh`, `libs_soundness` and `gen_typed_prog`). Its progress is no stuck states under the typing (`gen --progress`, `docs/design.md` §3.9):

```sh
target/release/k2lean soundness --kore-a out/my/definition.kore --name-a My \
  --kore-b out/my-typing/definition.kore --name-b MyTypes --ns MySound \
  --typing typeOf,wt --store-cell env --store-typing envTy \
  --out-typing MySound/Typing.lean --out-typed MySound/Typed.lean \
  --out-soundness MySound/Soundness.lean --out-unfold typed-unfold.txt
target/release/k2lean gen --kore out/my/definition.kore --runtime out/my/runtime.json --out gen/my --name My \
  --progress --assume-invariant MySound.Typed --invariant-module MySound.Typed \
  --invariant-preserved MySound.Typed.preserved --invariant-unfold typed-unfold.txt \
  --ending-lean MySound.kDone@k --progress-out . --progress-prefix MySound
```

It needs the two libraries and the translation of programs that `k2lean relate --roots` writes (`MySound/Tr.lean`; `--tr-module`), and writes `Typing.lean`, which the hand module `MySound/Store.lean` (`--hand-module`) imports; `Typed.lean`, preservation and the typing as an invariant, which `gen --progress` assumes; and `Soundness.lean`, `soundness` from the progress modules' `no_stuck`, with a case `gen --progress` leaves open proved in `MySound/ProgressHand.lean`; `docs/design.md`, §3.3, says what each part states and what is supported.

## Scaffolds

Three commands state a theorem whose proof needs an argument no generator has, and reduce it to named obligations: they prove the reduction (`KPrelude.Scaffold`) and the obligations a generic argument closes, and take the rest from a hand module; `docs/design.md`, §3.4 to §3.7, says what each generates and what it leaves (the calls are in `tests/areas/relational.sh`, `confluence.sh` and `noninterference.sh`):

```sh
# a stuttering bisimulation between A and B, from relate's per-rule simulations
target/release/k2lean relate --kore-a A/definition.kore --name-a A --kore-b B/definition.kore --name-b B \
  --ns AB --per-rule true --out AB/Tr.lean --report AB/correspondence.toml
target/release/k2lean refine --kore-a A/definition.kore --name-a A --kore-b B/definition.kore --name-b B \
  --ns AB --correspondence AB/correspondence.toml --open AB/open-cases.txt --out AB/Refine.lean
# confluence modulo scheduling, observing the cells --obs names (--report-only: the classification of the pairs);
# --threads CELL: one view per rule for the threads in CELL; the joins left are slots, proved generically,
# by the hand module (NAME | hand in --open-joins) or open (NAME alone)
target/release/k2lean confluence --kore A/definition.kore --name A --ns AConf --obs out [--threads CELL] \
  [--assume-invariant NAME --invariant-module M] --slots AConf/Slots.lean [--hand-module AConf.Hand \
  --open-joins AConf/open-joins.txt] --out AConf/Views.lean --report AConf/confluence.toml
# noninterference, reduced to a relation on pairs of runs (with --checker-kore: the relation generated)
target/release/k2lean noninterference --kore A/definition.kore --name A --ns ANI --store-cell env \
  --program-sort SortStmt --params "(G : Sec.SortMap)" --secure "secure G" --low-eq "lowEq G" --out ANI/NI.lean \
  [--checker-kore Sec/definition.kore --checker-name Sec --lev lev --sec sec --conf conf --open ANI/open.txt --out-dir ANI]
```

| option | does |
|---|---|
| `relate --per-rule true` | when not every rule pairs: one simulation lemma per pair of corresponding rules (`fwd.r`, `bwd.r`) instead of the bisimulation |
| `relate --split true` | the bisimulation in one module per simulation (`OUT/Base.lean`, `AppFwd`, `AppBwd`, `Forward`, `Backward`, imported by `OUT.lean`), so that Lean builds them in separate processes: for definitions of SIMPLE's size |
| `refine --open FILE` | the case parts the hand module proves (`KIND RULE`, `KIND` one of `fwd_tr`, `fwd_x`, `bwd_tr`, `bwd_x`); `--hand-module` (default `NS.Relation`), `--extra`, `--measure-a`, `--measure-b` name what it supplies (default `X`, `μ`, `ν`); `--hand-module none`: no hand module, `X` and the measures generated from one step of `B` that `A` takes in two (`--tr-module`, default `NS.Tr`) |
| `confluence --threads CELL` | the views of the rules by the bindings of the cell map in `CELL` they replace (a thread's step, its end, a spawn, two threads matched together; `--ns`, `--obs`, `--out`; `docs/design.md`, §3.6): two steps at bindings with no key in common, or at bindings and the other cells, join generically, the same-thread joins and the other pairs are the hypotheses `SameThreadJoins` and `OpenJoins` of `terminal_unique_of`, and `--obs` adds its corollary `obs_confluent_of`; `--assume-invariant NAME` (with `--invariant-module`, `--invariant-preserved`, as `claims`) states the premises and the theorem under a preserved program hypothesis; `--slots PATH` splits the premises into one obligation per pair of rules (a slot, `join.K.r₁.r₂`), attempted generically in the module `PATH`, proved by name in `--hand-module M` (`hand.join.K.r₁.r₂`) when the open-joins list (`--open-joins FILE`, filled by `open-from-log`) marks it `| hand`, or left open as a field of `Open`, the premise of `terminal_unique`; `NAME \| refuted` marks a slot the hand module refutes (`hand.join.K.r₁.r₂.refuted`, checked by `#k2l_refuted`), which refutes its premise (`openJoins_refuted`) and drops `terminal_unique`; `--hyp`, `--join` and `--open` are refused; the report gives the views' shape (`[threads]`) and, per premise and class of pairs, the slots proved generically, by hand, open or refuted (`[premises.*]`; all open without `--slots`), the pair classifier's reading kept as `[diagnostic.*]`, untrusted |
| `noninterference --params`, `--secure`, `--low-eq` | the hand module's parameters and predicates the statement uses; `--hand-module` (default `NS.Hand`) |
| `noninterference --checker-kore` | the relation from a two-level checker (`--lev`, `--sec`, `--conf` name its functions): `Levels.lean`, `Stack.lean`, `Proof.lean` in `--out-dir`, around the hand module `NS.Store` (`--store-module`), which proves the per-rule cases `--open` lists (`KIND RULE`, `KIND` one of `cq`, `sq`, `same`) |
| `noninterference --inputs`, `--observe`, `--disclosed`, `--quiet` | noninterference up to disclosure: each configuration variable but `$PGM` `public`, `private` or related by a named relation; the observed cells (the store by its relation, the others by equality); the disclosure cell, appended to by one strict construct; the checker's function on the expressions a confined stack may evaluate (`docs/design.md` §3.7) |

## Large definitions

The term universe is one inductive family indexed by the sorts, which Lean builds at KEVM's size; the former encoding, one Lean type per sort in one `mutual` block, was retired on 2026-10-28 (`docs/design.md`, §2.1); `gen --arity-terms`, the former opt-in, changes nothing.
Determinism is proved along the rule index rather than over all pairs of rules; `docs/design.md`, §2.1 and §3.1, describes both and what they cost.
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
