# Preserved invariants of a k2lean semantics: user guide

This guide shows how to prove, in Lean, that a property of configurations is kept by every step of a K semantics that k2lean generated.
It walks through two new invariants of kimp (the IMP of `imp-semantics`), one of each kind, with every command and file.
The commands run from a k-rust checkout; the outputs shown are those of a run on 2026-10-24.
A path without a variable in front of it is relative to `k2lean/`.

## 1. What a preserved invariant is

### 1.1 The statement

k2lean generates, for a K definition, a Lean inductive relation `Step : C → C → Prop` on the configuration type `C` (`SortGeneratedTopCell`), with one constructor per K rule.
A preserved invariant is a predicate `P : C → Prop` with

```lean
def Preserved (S : α → α → Prop) (P : α → Prop) : Prop :=
  ∀ c c', P c → S c c' → P c'
```

(`KPrelude.Preserved`, `lean/prelude/KPrelude/Invariant.lean`).
`Preserved Step P` says: every rule, applied to any configuration that satisfies `P`, gives a configuration that satisfies `P`, whatever the program.
With a theorem `init_holds : P (init pgm env)` about the generated initial configuration, it gives `star : Star Step (init pgm env) c → P c`: every configuration reachable from a program's start satisfies `P`.

### 1.2 What it says and what it does not

- It is a statement about every program and every step: one theorem covers all inputs.
- It is proved rule by rule, so it holds only for *inductive* invariants: `P` must be kept by each rule from *every* configuration that satisfies `P`, reachable or not.
  A property that is true of reachable configurations but not inductive must be strengthened first (§8).
- `Step` relates a configuration to its defined successors.
  A rule whose right-hand side is undefined (`⊥`, for example a division by zero in a function) gives no `Step`, so `Preserved` says nothing about it; undefinedness is stated by the generated `App` relation and the adequacy theorems, not by an invariant.
- At the initial configuration, every configuration variable (`$PGM`, `$ENV`) is a parameter of `init`.
  krust accepts any value of the variable's sort, so `init_holds` usually needs a hypothesis on them (§3.3, §4.5).

### 1.3 A preserved invariant or a K claim

| you want to show | use |
|---|---|
| one program's loop keeps a property, possibly with symbolic inputs | a K claim with the property in a circularity's `requires` (`krust kprove`, or the Lean claims of `lean/claims/`) |
| a property holds at every step of every program | a preserved invariant |
| a fact about sorts (`<env>` holds a `Map`) | nothing: the generated Lean types already say it |

A K claim `φ ⇒ ψ` is a reachability statement about the paths from `φ`; "`P` holds at every reachable configuration" is a safety property, which a claim does not express.
A preserved invariant can be assumed inside a claim proof: `lean/claims/KClaims/Invariant.lean` has `AF.step_inv`, `AF.coind_inv`, `AF.circularity_inv` and their `EF` forms, which carry `P` to every state of the proof.
`k2lean claims --assume-invariant Invariant`, over a library generated with `gen --invariant` (whose `invariant-unfold.txt` lists the invariant's unfolding set for it), states every claim for the configurations satisfying the kind 1 invariant and proves it with `P` carried along (`README.md`, "Claims"; `docs/design.md`, §3.8).
A claim false in general can then hold: `demos/claims/specs/imp-inv-spec.k` copies a store value `V` of any sort, which kimp evaluates when it is not a value, and under kimpinv's invariant, whose part `envOk` says that every store value is a `Value`, both of its claims are proved generically (`generated/kimpinv-claims`, heavy gate).

### 1.4 The two kinds

| | kind 1 | kind 2 |
|---|---|---|
| you write | a K function `f(…) -> Bool`, in the K definition or in KRS | a Lean predicate `P`, in your own Lake project |
| you run | `k2lean gen --invariant f@CELL` | `k2lean new-invariant`, then `lake build` |
| the statement | generated with the library: `Invariant.preserved`, `init_holds`, `star`, `stepsN` | yours, in a skeleton the command writes |
| per-rule proofs | generated; the rules the tactic does not close are proved in a hand module | the tactic `k2l_preserve … hand NS`, and your hand cases |
| choose it when | the property belongs to the language: K authors read it, it changes with the spec, every regenerated definition gets its own theorem | the property needs what a K function cannot express (a quantifier, a parameter, another Lean library), relates several cells, or is a proof device |

A KRS definition with typed cells (`env: Map<Id, Value>`) gets its typing invariant from a sidecar file, without any function (§3.5).

## 2. Setup

### 2.1 Paths

The commands use these variables; set them in the shell you run the guide in.

| variable | value |
|---|---|
| `R` | the k-rust checkout |
| `K` | `$R/k2lean` |
| `W` | your work directory, outside the checkout |
| `KRUST` | `$R/target/release/krust`, a release build of krust (`cargo build --release -p k-rust --bin krust`) |
| `BUILTIN` | `$R/k/k-distribution/include/kframework/builtin`, K's builtin modules, from the K sources at the pin of `scripts/reference-differential.toml` (`README.md`, "Compatibility evidence") |
| `KIMP` | `$R/imp-semantics/src/kimp/kdist/imp-semantics`, kimp's K sources (the imp-semantics checkout at its pin: never edit it) |
| `G` | `$R/target/release/k2lean`, the k2lean binary |
| `GEN` | `$W/k2lean/generated`, your generated libraries |

`elan`, `lean` and `lake` must be on `PATH`; each project's `lean-toolchain` selects Lean v4.34.0, which elan installs on first use.

```sh
R=$(git rev-parse --show-toplevel)
K=$R/k2lean
W=${TMPDIR:-/tmp}/k2lean-guide
KRUST=$R/target/release/krust
BUILTIN=$R/k/k-distribution/include/kframework/builtin
KIMP=$R/imp-semantics/src/kimp/kdist/imp-semantics
G=$R/target/release/k2lean
GEN=$W/k2lean/generated
mkdir -p $W
```

Run the first line inside the checkout; with `CARGO_TARGET_DIR` set, `KRUST` and `G` are under that directory instead.

### 2.2 Build k2lean

```sh
cargo build --release --locked -p k2lean --manifest-path $R/Cargo.toml
```

The binary is `$G`; it is self-contained.

### 2.3 A work tree

Work outside the checkout: `lake build` writes into the `.lake/` directory of every package it builds, including the dependencies.
A generated library requires the prelude as `../../lean/prelude`, so the work tree keeps the layout of `k2lean/`.
The generated libraries are not in git: `demos/regen.sh` and the gate (§10) regenerate them, and git keeps only each library's open-obligation lists and hand-written invariant module, which are inputs of the generation.

```sh
mkdir -p $GEN/kimp $W/k2lean/lean
cp -a $K/lean/prelude $W/k2lean/lean/
cp $K/generated/kimp/open-obligations.txt $GEN/kimp/
```

### 2.4 Generating a library

A library is generated in two steps: krust compiles the K definition to KORE, and `k2lean gen` writes a Lake project from the KORE.
`$K/tests/libs.sh` gives the exact calls for every library of the gate (each area's are in `$K/tests/areas/AREA.sh`, which it sources); source it, set the variables it reads, and define `kore_dir NAME` to say where the compiled KORE goes.
This generates kimp in your work tree; the gate checks that these files do not change without a reviewed baseline (`tests/baseline/core.toml`, `[sources]`):

```sh
. $K/tests/libs.sh
kore_dir() { echo "$W/kore/$1"; }
libs_kcompile kimp && libs_kcompile kimp-verif && libs_gen kimp
```

`libs_gen kimp` is this call:

```text
$G gen --kore $W/kore/kimp/definition.kore --runtime $W/kore/kimp/runtime.json \
  --out $GEN/kimp --name KImp --prelude ../../lean/prelude \
  --lemmas-kore $W/kore/kimp-verif/definition.kore --open-obligations $GEN/kimp/open-obligations.txt
```

- `--name` is the Lean namespace; `--prelude` is the prelude's path relative to `--out`.
- `--open-obligations FILE` lists the K equations whose generated proofs fail; they are emitted as statements only.
  A library generated with an empty list whose `Equations.lean` then fails to build is fixed by `$G open-from-log NS/Equations.lean BUILD.log open-obligations.txt` and a second `gen`; starting from an existing library's list (kimp has 1) avoids the round.
- The files an invariant uses are `NS/Rules.lean` (`Step`), `NS/Preserves.lean` (one `Step.Case.r P` per rule and `Step.preserves_of`) and `NS/Init.lean` (`init`, one parameter per configuration variable).

## 3. Kind 1: an invariant written in K

The walkthrough proves: **every key of kimp's store `<env>` is an `Id`**.

### 3.1 Write the K function

An invariant is a K function with one argument and result `Bool`, in a module that imports the definition.
Write it in its own file, so the reference sources stay untouched:

```sh
mkdir -p $W/k
cat > $W/k/imp-keys.k <<'EOF'
requires "imp.k"

// Every key of the store <env> is an Id.
module IMP-KEYS
  imports IMP
  imports MAP
  imports LIST
  imports BOOL

  syntax Bool ::= envKeysOk(Map) [function, total]
                | allIds(List) [function, total]
  rule envKeysOk(M) => allIds(keys_list(M))
  rule allIds(.List) => true
  rule allIds(ListItem(X) L) => isId(X) andBool allIds(L)
endmodule
EOF
```

The shapes the generator and the tactic support:

| shape | how to write it | what the generator does |
|---|---|---|
| cell form (the default) | `f(S)` where `S` is the content sort of the cell (`envKeysOk(Map)` for `<env>`), and `--invariant f@env` | the part `f (content_env (cell_env c)) = true`, read through one projection per level of the configuration |
| cell-map lift | `f(S)` over a cell inside a cell collection (`--invariant holdsOk@holds` on SIMPLE, where `<holds>` is inside the `<thread>` cell map) | "for every element": `MapHook.EntriesOn` over the collection's bindings, so the closers read the invariant of the matched element |
| nested collections | `f(S)` over a cell inside a cell collection of an element of another (`--invariant even@v` on `tests/fixtures/nested`: `<v>` in every `<member>` of every `<group>`) | lifted once per collection: the predicate of a `<group>` binding (`Invariant.even_in_group`) is `EntriesOn` of the member predicate (`Invariant.even_elem`) over the group's `<members>` |
| list fold | `f(.List, P…) => true` and `f(ListItem(X) L, P…) => φ(X, P…) andBool f(L, P…)` (or `f(L, P…) andBool φ(X, P…)`): the list at any argument, the other arguments variables the recursive call passes unchanged (`allIs(L, B)` in `demos/k/kimp-inv`), no `requires`, `φ` total | the theorem `f l p = true ↔ every element satisfies φ(·, p)` (`Invariant.f_iff`), which the collection lemmas read |
| structural recursion | a recursive function each of whose recursive calls is on a variable inside a constructor pattern of the same argument (`even(s(s(N))) => even(N)`), not mutually recursive with another, with proved equations | its K equations (`Eqn.*`) join the unfolding set, as a non-recursive function's do |
| a fold over `K` | `f(.K, P…) => true` and `f(I ~> K, P…) => g(I, P…) andBool f(K, P…)`, the test of one item a call of a function `g` that may be partial (a function of the same mutual group, which the generator makes well-founded and `Option`-valued), both equations proved; `kOk` in `tests/fixtures/kfold`, SIMPLE's `kIn` | `Invariant.kAll P k` (every item of `k` satisfies `P`) and `Invariant.f_iff : f k p = some true ↔ kAll (g · p = some true) k`, by structural recursion on `k` from the two equations: a rule that pushes or pops items of `<k>` reads the fold item by item |
| a function of a fold's group | a recursive function that does not call itself, only other functions of its mutual group (SIMPLE's `itemIn`, through `kIn` and `listIn`; `itemOk` in `tests/fixtures/kfold`, through `kOk`), with proved equations | its equations join the unfolding set: they rewrite a call on a constructor term into calls whose element-wise forms the others have, which are theorems, so the rewriting ends |
| an `owise` equation at injections | a function (of the unfolding set) with a `Bool` argument of sort `KItem` that every equation but an `owise` one matches with a constructor of `KItem`'s own (`setEnv(E)`, a stack frame, `use(L)`), the `owise` value a constant | `Invariant.f_owise_S : f (inj x) … = c` for every subsort `S` of `KItem`: a value injected from `S` is no constructor of `KItem`'s own, so only the `owise` equation applies, which `simp` cannot see on a variable under an injection (`inj_Exp_KItem e` is a `match` on `e`); proved by casing on `x` |
| a map built on an `Int` range | `f(A, B, P…) => .Map requires A >Int B` and `f(A, B, P…) => K(A) \|-> V f(A +Int 1, B, P…) requires A <=Int B` (SIMPLE's `N ... M \|-> K`, `tests/fixtures/range`'s `fill`), the other arguments patterns the recursive call passes unchanged (an alias `P #as X` passed as `X` too), `V` mentioning neither `A` nor `f`, `K(A)` no variable but `A`, both equations proved; a rule calls it, the invariant need not | the `@[k2l_coll]` theorem `Invariant.range_f`: a result of `f` binds `V` at each of its keys, so it satisfies every `Q` that holds of `(K(a), V)` for all `a` (`MapHook.entriesOn_of_range`, from the two equations, by induction on the number of keys); closer 3 applies it to the map a rule binds |
| non-recursive helpers | ordinary equations, `owise` ones included | their K equations (`Eqn.*`) join the unfolding set; an `owise` equation is a rewrite conditional on its side condition (no other equation matches), which simp discharges when the argument's constructors differ from the other equations' patterns |
| a map walked by pattern | `f(.Map, P…) => true` and `f((K \|-> V) REST, P…) => φ(K, V, P…) andBool f(REST, P…)`, in that order (the binding first in the pattern, the test first in the conjunction: the shape the generated proof is checked on; write a walk in another order this way): the map at one argument, or the content of a cell there (`<threads> <thread> … </thread> Ts </threads>`, SIMPLE's thread cell map), the other arguments variables the recursive call passes unchanged, no `requires`, `K` and `V` variables or trees of cells with variables at the leaves (a variable read twice, a cell map's key and the element's own id, means the two are equal); `allIn` and `workersIn` in `tests/fixtures/walk` | the test of one binding `Invariant.f_test k v p` (the reads of `K`'s and `V`'s variables through projections, so it reduces on a rule's rebuilt element whose cells are variables, and `φ`), and the theorem `Invariant.f_walk : f m p = true ↔ WF m ∧ every binding passes the test` (`MapHook.all_iff_of_walk`, from the function's instances, `F.eq_instances`, and its unit equation), which the collection lemmas read; for a cell's map, also `Invariant.f_walk_cell` at any cell, through the cell's map `Invariant.f_map`, which rewrites a cell that a rule leaves as a variable |
| a tree of cells | `f(C)` for a cell sort `C` with one equation whose argument is a tree of cells with variables at the leaves: `topEnvOk(<generatedTop> <k> _ </k> <env> E </env> _ </generatedTop>)` with `--invariant topEnvOk` (the top-cell form), or `tStoreOk(<T> <store> S </store> ... </T>)` with `--invariant tStoreOk@T` | the theorem `Invariant.f_cells : ∀ x, f x = rhs(projections of x)`, proved by cases on `x` (each cell sort has one constructor), joins the unfolding set, so the function reads its cells as the cell form does; a right-hand side that conjoins partial calls (`topBoth(…) => allValues(values(E)) andBool noIds(values(E))`, `demos/k/kimp-inv/imp-both.k`) is a chain of `Option.bind`s, which `KPrelude.bind_bool_eq_some_true` splits into one fact per call; at `init` the right-hand side gets a hypothesis on the configuration variables its cells hold, or is computed |

Several `--invariant` flags (and `--sidecar`) are conjoined into one `Invariant`.

### 3.2 Compile and generate

```sh
$KRUST kcompile $W/k/imp-keys.k --main-module IMP-KEYS --syntax-module IMP-SYNTAX \
  --output-directory $W/kore/kimp-keys --builtin-directory $BUILTIN -I $KIMP
mkdir -p $GEN/kimpkeys
cp $K/generated/kimp/open-obligations.txt $GEN/kimpkeys/
$G gen --kore $W/kore/kimp-keys/definition.kore --runtime $W/kore/kimp-keys/runtime.json \
  --out $GEN/kimpkeys --name KImpKeys --prelude ../../lean/prelude \
  --open-obligations $GEN/kimpkeys/open-obligations.txt --invariant envKeysOk@env
```

- `NAME` in `--invariant NAME@CELL` is the K label up to `(`; `CELL` is the cell name without brackets.
- The output ends with `invariant: 0 open cases` and writes `KImpKeys/InvariantDefs.lean`, `KImpKeys/Invariants.lean` and `open-invariant-cases.txt`.
- The library root (`KImpKeys.lean`) does not import the invariant modules; build them by name.

### 3.3 Build, and the generated theorems

```sh
(cd $GEN/kimpkeys && lake build KImpKeys.Invariants > $W/kimpkeys-1.log 2>&1)
grep -E "k2l_preserve|depends on|^error|Build completed" $W/kimpkeys-1.log
```

The first build compiles the whole library (132 s wall and 93 s of CPU in the gate, under a load of 21 to 57), and succeeds: `k2l_preserve` closes the case of every rule, and the four guarded theorems depend on `propext`, `Classical.choice` and `Quot.sound` only.

```text
info: KImpKeys/Invariants.lean:362:0: KImpKeys.Invariant.preserved depends on axioms: [propext, Classical.choice, Quot.sound]
…
Build completed successfully
```

What `InvariantDefs.lean` defines (`K.envKeysOk` abbreviates `K.«envKeysOk(_)_IMP-KEYS_Bool_Map»`):

```lean
def Invariant.cell_env : SortGeneratedTopCell → SortEnvCell
def Invariant.content_env : SortEnvCell → SortMap
def Invariant.envKeysOk (c : SortGeneratedTopCell) : Prop :=
  K.envKeysOk (Invariant.content_env (Invariant.cell_env c)) = some true
def Invariant (c : SortGeneratedTopCell) : Prop := Invariant.envKeysOk c
theorem Invariant.allIds_iff (l : SortList) :
    K.allIds l = some true ↔ ListHook.ElemsOn (fun x => K.isId (SortK.kseq x SortK.dotk) = true) l
```

What `Invariants.lean` proves:

```lean
theorem Invariant.case.«CALC.assign» : Step.Case.«CALC.assign» Invariant     -- one per rule
theorem Invariant.preserved : Preserved Step Invariant
theorem Invariant.init_holds (pgm : SortStmt) (env : SortMap)
    (h_env : K.envKeysOk env = some true) : Invariant (init pgm env)
theorem Invariant.star {pgm env} (h_env : …) {c} (h : Star Step (init pgm env) c) : Invariant c
theorem Invariant.stepsN {pgm env} (h_env : …) {n c} (h : StepsN Step n (init pgm env) c) : Invariant c
#k2l_assert_axioms Invariant.preserved Invariant.init_holds Invariant.star Invariant.stepsN
```

- Each case is `by k2l_inv`, a local macro for `k2l_preserve` with the invariant's unfolding set (the parts, the projections, the K equations, the fold's `_iff`).
- The case of `CALC.assign`, which updates the store, closes because `ListHook.elemsOn_keysList_iff` (`@[k2l_pres]`) turns the fold over `keys_list(E)` into a predicate on `E`'s bindings, which `MapHook.entriesOn_update` carries to the updated store; the new key `X` is an `Id` by `isId`'s equation.
- `init_holds` follows the configuration declaration: a cell that holds a configuration variable (`<env> $ENV:Map </env>`) gives a hypothesis on that parameter; a cell with a closed term is proved by computation; anything else makes `init` an open case (`Invariant.hand.init`).
- `#k2l_assert_axioms` fails the build when a theorem depends on `sorryAx` or on an axiom other than `propext`, `Classical.choice`, `Quot.sound`.
- `Invariant` is named so, not `Inv`, because core Lean declares a class `Inv`.

### 3.4 Open cases and the hand module

A case the tactic does not close fails the build at its theorem: the log has `k2l_preserve: rule r not closed; …` and an `unsolved goals` error that shows the case, with the rule's variables and side conditions in context.
`$G open-from-log NS/Invariants.lean BUILD.log open-invariant-cases.txt` lists the failed cases in `open-invariant-cases.txt`, and the next `gen` takes each listed case from the hand module `NS/InvariantsHand.lean`, as the theorem `Invariant.hand.r` with the same statement.

Every case of `envKeysOk` closes, so to see the hand path, list `CALC.assign` yourself (the gate's fixture `generated/kimpkeys-hand` is this library with this list and the hand proof below):

```sh
cd $GEN/kimpkeys
echo '«CALC.assign» | Step.Case.«CALC.assign» Invariant | calc.k:32:3' >> open-invariant-cases.txt
$G gen --kore $W/kore/kimp-keys/definition.kore --runtime $W/kore/kimp-keys/runtime.json \
  --out $GEN/kimpkeys --name KImpKeys --prelude ../../lean/prelude \
  --open-obligations $GEN/kimpkeys/open-obligations.txt --invariant envKeysOk@env
grep -v '^#' open-invariant-cases.txt
```

A line of the list is the case, its statement and the rule's position; `gen` prints `invariant: 1 open cases`.
The generator wrote `KImpKeys/InvariantsHand.lean` once, with the statement in a comment and the generated unfolding set in its header; it never overwrites that file.
Until the theorem exists, the build fails at `Invariant.case.«CALC.assign»` with ``Unknown constant `KImpKeys.Invariant.hand.«CALC.assign»` ``, which names the rule.

To prove the case, read its statement in `KImpKeys/Preserves.lean` (or in the `unsolved goals` error of a case the tactic left open):

```lean
def Step.Case.«CALC.assign» (P : SortGeneratedTopCell → Prop) : Prop :=
  ∀ (X : SortId) (y : SortExpr) (DotVar1 : SortK) (E : SortMap) (DotVar0 : SortGeneratedCounterCell)
    (V : SortValue) (hp : proj_Expr_Value y = some V),
    P (… (SortEnvCell.«<env>» E) DotVar0) →
    P (… (SortEnvCell.«<env>» (KPrelude.MapHook.update E (SortKItem.inj_Id X) (inj_Value_KItem V))) DotVar0)
```

The hand proof takes the steps the closers take (§3.3):

```sh
cat > $GEN/kimpkeys/KImpKeys/InvariantsHand.lean <<'EOF'
import KImpKeys.InvariantDefs

/-! Hand-written proofs of the cases of `Invariant` listed in `open-invariant-cases.txt`. -/

namespace KImpKeys

open KPrelude

/-- Rule `CALC.assign` (calc.k:32:3): the updated store's keys are the old keys and `X`, an `Id`. -/
theorem Invariant.hand.«CALC.assign» : Step.Case.«CALC.assign» Invariant := by
  intro X y DotVar1 E DotVar0 V hp h
  simp only [Invariant, Invariant.envKeysOk, Invariant.cell_env, Invariant.content_env,
    Eqn.«envKeysOk(_)_IMP-KEYS_Bool_Map_1», Invariant.allIds_iff, Option.bind_fun_some,
    ListHook.elemsOn_keysList_iff] at h ⊢
  exact MapHook.entriesOn_update h (Eqn.isId_1 X)

end KImpKeys
EOF
(cd $GEN/kimpkeys && lake build KImpKeys.Invariants 2>&1 | grep -E "depends on|^error|Build completed")
```

The build completes; the four theorems depend on `propext`, `Classical.choice` and `Quot.sound` only.

- The `simp only` list is the generated unfolding set (from the header of the skeleton), with the fold's rewrite `ListHook.elemsOn_keysList_iff`.
- `MapHook.entriesOn_update` is a collection lemma of `KPrelude.InvColl` (§6.3).
- `Eqn.isId_1 X : K.isId (kseq (inj_Id X) dotk) = true` is the generated K equation of `isId`.
- The hand module is yours: regeneration never touches it, and `k2lean diff` names it when its rule changes (§7).

### 3.5 KRS: the sidecar of declared cell types

A KRS configuration declares element sorts (`env: Map<Id, Value>`) that KORE does not carry.
A sidecar file gives them to the generator, keyed by KORE names; `--sidecar FILE` makes each declared cell a part of `Invariant`, with no K function:

```json
{
  "format": "k2lean-krs-sidecar",
  "version": 1,
  "cells": [
    { "cell": "Lbl'-LT-'env'-GT-'", "krs": "env: Map<Id, Value>",
      "collection": "Map", "key": "SortId", "value": "SortValue" }
  ]
}
```

| key | value |
|---|---|
| `cell` | the cell's KORE symbol, as in `definition.kore` |
| `collection` | `Map`, `List` or `Set` |
| `key`, `value` | for a `Map`, the KORE sorts of keys and values |
| `element` | for a `List` or a `Set`, the KORE sort of elements |
| `krs`, `producer`, `definition` | free text (optional) |

The generated part is "every binding has the declared sorts", where "a `KItem` `t` has sort `S`" is `∃ y, proj_KItem_S t = some y`:

```lean
def Invariant.entry_env (p : SortKItem × SortKItem) : Prop :=
  (∃ y, proj_KItem_Id p.1 = some y) ∧ (∃ y, proj_KItem_Value p.2 = some y)
def Invariant.declared_env (c : SortGeneratedTopCell) : Prop :=
  KPrelude.MapHook.EntriesOn Invariant.entry_env (Invariant.content_env (Invariant.cell_env c))
```

The recorded KRS IMP definition and its sidecar are in `$K/demos/k/krs-imp/`; this regenerates and builds it (82 of 82 rules automatic):

```sh
mkdir -p $GEN/krsimp && cp $K/generated/krsimp/open-*.txt $GEN/krsimp/
mkdir -p $W/k2lean/demos/k && cp -a $K/demos/k/krs-imp $W/k2lean/demos/k/
KRS=$W/k2lean/demos/k/krs-imp
$G gen --kore $KRS/definition.kore --out $GEN/krsimp --name KrsImp --prelude ../../lean/prelude \
  --open-obligations $GEN/krsimp/open-obligations.txt --sidecar $KRS/k2lean-sidecar.json
(cd $GEN/krsimp && lake build KrsImp.Invariants 2>&1 | grep -E "depends on|^error|Build completed")
```

- `krs build` writes the sidecar as `k2lean-sidecar.json` beside `definition.kore`: one entry per configuration cell whose content is a `Map`, `List` or `Set` with declared element sorts, outside every repeated or optional cell; the recorded `$K/demos/k/krs-imp/k2lean-sidecar.json` is its output for KRS IMP (`krs/tests/imp/rust-definition`), whose KORE names it uses are those of the recorded `definition.kore`.
- The generator refuses a sidecar cell that is not in the definition, whose content is not the named collection, whose sorts are unknown or not subsorts of the collection's element sort, or that lies inside a cell collection.
- Nested arguments (`Map<Int, Set<Int>>`) have no field.

## 4. Kind 2: an invariant written in Lean

The walkthrough proves: **for every list `D` of identifiers, if every identifier of `D` is a key of `<env>`, it stays one**: an assigned variable is never unbound.
The parameter `D` and the quantifier make it a Lean statement rather than a K function.

### 4.1 Create the project

```sh
$G new-invariant --lib $GEN/kimp --out $W/EnvBound
(cd $W/EnvBound && lake build 2>&1 | grep -E "k2l_preserve|Build completed")
```

The command writes a Lake project; nothing in it is ever regenerated, and the command never overwrites a file:

| file | content |
|---|---|
| `lakefile.lean` | requires `KPrelude` and `KImp` by relative path |
| `EnvBound/Invariant.lean` | `def Invariant : KImp.SortGeneratedTopCell → Prop := fun _ => True`, a placeholder |
| `EnvBound/Cases.lean` | `namespace hand` with a marker line, then `theorem preserved : Preserved KImp.Step Invariant := by k2l_preserve hand EnvBound.hand` |
| `EnvBound/Run.lean` | `init_holds`, `star`, `stepsN`, and `#k2l_assert_axioms` |

The skeleton builds at once: `k2l_preserve: 79 of 79 rules closed`.
Every command and module of this section was run as written on 2026-10-25 (Lean v4.34.0, kimp in the default arity-indexed encoding), with the results shown.
`--name NAME` sets the project and namespace name (default: the last component of `--out`); `--prelude DIR` overrides the prelude the library names.

### 4.2 Write `P` and how it computes

Read cells through one projection per level of the configuration, each a separate definition matching one constructor.
On a rule that does not touch `<env>`, both sides then reduce to the same `envMap Gen2`, and the first closer proves the case by `exact`; a single projection with a nested pattern would be stuck on a variable cell.
The constructors and argument orders are in `KImp/Terms.lean` and in the `Step.Case` statements of `KImp/Preserves.lean`.
The collection predicates (`MapHook.EntriesOn`, `ListHook.ElemsOn`) and their lemmas come from `KPrelude.InvColl`; import it whenever `P` uses them.

```sh
cat > $W/EnvBound/EnvBound/Invariant.lean <<'EOF'
import KImp.Rules
import KPrelude.InvColl

/-! Every identifier of `D` stays a key of kimp's store `<env>`. -/

namespace EnvBound

open KPrelude

/-- The `<env>` cell of a configuration. -/
def envCell : KImp.SortGeneratedTopCell → KImp.SortEnvCell
  | .«<generatedTop>» _ e _ => e

/-- The map that an `<env>` cell holds. -/
def envMap : KImp.SortEnvCell → KImp.SortMap
  | .«<env>» m => m

/-- The identifier `x` is a key of the map `m`. -/
def BoundIn (m : KImp.SortMap) (x : KImp.SortId) : Prop :=
  ∃ w, (KImp.SortKItem.inj_Id x, w) ∈ ListIso.toList m

/-- Every identifier of `D` is a key of `<env>`. -/
def Invariant (D : List KImp.SortId) (c : KImp.SortGeneratedTopCell) : Prop :=
  ∀ x ∈ D, BoundIn (envMap (envCell c)) x

end EnvBound
EOF
cat > $W/EnvBound/EnvBound/Cases.lean <<'EOF'
import EnvBound.Invariant
import KImp.Preserves
import KPrelude.InvTactic
import KPrelude.InvColl

/-! Every rule of kimp keeps `Invariant D`. -/

namespace EnvBound

open KPrelude

namespace hand

-- k2lean new-invariant --from-log: new hand cases go above this line
end hand

/-- Every rule of kimp keeps `Invariant D`. -/
theorem preserved (D : List KImp.SortId) : Preserved KImp.Step (Invariant D) := by
  k2l_preserve [envCell, envMap, BoundIn] hand EnvBound.hand

end EnvBound
EOF
```

- The lemma list of `k2l_preserve` is the unfolding set: the definitions and lemmas that say how `P` computes (§5.2).
  `Invariant` itself is unfolded without being named.
- Keep the marker line in `Cases.lean`: `--from-log` inserts stubs above it.
- Hand cases and `preserved` share one module on purpose: Lake does not build the modules that import a module with an error (§9), so a broken hand case still leaves `preserved` elaborated.

### 4.3 Build and read the residual goals

`Run.lean` still has the placeholder's signatures, so build `Cases` alone:

```sh
(cd $W/EnvBound && lake build EnvBound.Cases > $W/cases-1.log 2>&1)
grep -A 22 "k2l_preserve" $W/cases-1.log
```

```text
info: EnvBound/Cases.lean:19:2: k2l_preserve: 78 of 79 rules closed; open: [«CALC.assign»]
error: EnvBound/Cases.lean:18:80: unsolved goals
case «CALC.assign»
D : List KImp.SortId
X : KImp.SortId
y : KImp.SortExpr
DotVar1 : KImp.SortK
E : KImp.SortMap
DotVar0 : KImp.SortGeneratedCounterCell
V : KImp.SortValue
hp : KImp.proj_Expr_Value y = some V
⊢ Invariant D (… (KImp.SortEnvCell.«<env>» E) DotVar0) →
    Invariant D (… (KImp.SortEnvCell.«<env>» (MapHook.update E (KImp.SortKItem.inj_Id X) (KImp.inj_Value_KItem V))) DotVar0)
```

- The log line is `k2l_preserve: N of M rules closed; hand: [...]; open: [...]`: `N` rules closed by the closers, the rules taken from `hand`, the rules left open.
- Each open rule is an `unsolved goals` error tagged with the rule's name, showing `P lhs → P rhs` with the rule's variables and side conditions in context.
- Before writing a hand case, try giving the closers more lemmas (§5.2); here no closer reasons about a membership under `update`, so the case needs a hand proof.

### 4.4 Stubs, and a hand case

```sh
$G new-invariant --lib $GEN/kimp --out $W/EnvBound --from-log $W/cases-1.log \
  --params '(D : List KImp.SortId)' --pred 'Invariant D'
sed -n '/namespace hand/,/end hand/p' $W/EnvBound/EnvBound/Cases.lean
```

`--from-log` adds one stub per open rule that has no hand case yet; `--params` and `--pred` give the stub the invariant's parameters.

```lean
theorem «CALC.assign» (D : List KImp.SortId) : KImp.Step.Case.«CALC.assign» (Invariant D) := by
  intro X y DotVar1 E DotVar0 V hp
  intro h
  done
```

The stub introduces the rule's variables and side conditions under their generated names and ends in `done`, which fails with the goal still to prove (no `sorry`).
Replace `done` by the proof; here it needs one lemma about `update`, which goes above `namespace hand`.
`Cases.lean` then reads:

```sh
cat > $W/EnvBound/EnvBound/Cases.lean <<'EOF'
import EnvBound.Invariant
import KImp.Preserves
import KPrelude.InvTactic
import KPrelude.InvColl

/-! Every rule of kimp keeps `Invariant D`. -/

namespace EnvBound

open KPrelude

/-- Updating a map keeps every key it had. -/
theorem boundIn_update {m : KImp.SortMap} {k v : KImp.SortKItem} {x : KImp.SortId}
    (h : BoundIn m x) : BoundIn (MapHook.update m k v) x := by
  obtain ⟨w, hw⟩ := h
  rw [BoundIn, MapHook.update_def, ListIso.toList_ofList]
  by_cases hk : KImp.SortKItem.inj_Id x = k
  · subst hk
    exact ⟨v, SAL.mem_insert_self _ _ _⟩
  · exact ⟨w, SAL.mem_insert_of_mem_ne hw hk⟩

namespace hand

/-! ## HAND CASE `CALC.assign` (calc.k:32:3): the store is updated at `X`. -/

theorem «CALC.assign» (D : List KImp.SortId) : KImp.Step.Case.«CALC.assign» (Invariant D) := by
  intro X y DotVar1 E DotVar0 V hp
  intro h x hx
  exact boundIn_update (h x hx)

-- k2lean new-invariant --from-log: new hand cases go above this line
end hand

/-- Every rule of kimp keeps `Invariant D`. -/
theorem preserved (D : List KImp.SortId) : Preserved KImp.Step (Invariant D) := by
  k2l_preserve [envCell, envMap, BoundIn] hand EnvBound.hand

end EnvBound
EOF
(cd $W/EnvBound && lake build EnvBound.Cases 2>&1 | grep -E "k2l_preserve|^error|Build completed")
```

The log line is now `k2l_preserve: 78 of 79 rules closed; hand: [«CALC.assign»]`.
`hand EnvBound.hand` finds `EnvBound.hand.«CALC.assign»` by name and closes the rule's case with it; a hand case whose statement does not match its rule's case is an error naming it.

### 4.5 The initial configuration

`Run.lean` states `P` at the generated `init` and extends it to every reachable configuration.
`init pgm env` puts `env` in `<env>`, so `Invariant D (init pgm env)` holds exactly when every identifier of `D` is a key of `env`: that is the hypothesis.

```sh
cat > $W/EnvBound/EnvBound/Run.lean <<'EOF'
import EnvBound.Cases
import KImp.Init
import KPrelude.InvSteps
import KPrelude.Tactic

/-! Every run of a kimp program keeps the identifiers of `D` bound. -/

namespace EnvBound

open KPrelude

/-- The initial configuration satisfies `Invariant D` when every identifier of `D` is a key of
the initial store `env`. -/
theorem init_holds (D : List KImp.SortId) (pgm : KImp.SortStmt) (env : KImp.SortMap)
    (h_env : ∀ x ∈ D, BoundIn env x) : Invariant D (KImp.init pgm env) :=
  h_env

/-- Every configuration reachable from the initial configuration satisfies `Invariant D`. -/
theorem star {D : List KImp.SortId} {pgm : KImp.SortStmt} {env : KImp.SortMap}
    (h_env : ∀ x ∈ D, BoundIn env x) {c : KImp.SortGeneratedTopCell}
    (h : Star KImp.Step (KImp.init pgm env) c) : Invariant D c :=
  (preserved D).star h (init_holds D pgm env h_env)

/-- Every configuration reached in `n` steps from the initial configuration satisfies `Invariant D`. -/
theorem stepsN {D : List KImp.SortId} {pgm : KImp.SortStmt} {env : KImp.SortMap}
    (h_env : ∀ x ∈ D, BoundIn env x) {n : Nat} {c : KImp.SortGeneratedTopCell}
    (h : StepsN KImp.Step n (KImp.init pgm env) c) : Invariant D c :=
  (preserved D).stepsN h (init_holds D pgm env h_env)

#k2l_assert_axioms preserved hand.«CALC.assign» init_holds star stepsN

end EnvBound
EOF
(cd $W/EnvBound && lake build 2>&1 | grep -E "k2l_preserve|depends on|^error|Build completed")
```

- `init` has one parameter per configuration variable (kimp: `pgm` for `$PGM`, `env` for `$ENV`); every other cell is at its declared default.
- The proof of `init_holds` is the hypothesis itself, because `Invariant D (init pgm env)` unfolds to it.
- `Star` and `StepsN` are the prelude's closures (`KPrelude.Star`, `KPrelude.StepsN`); `Preserved.star` and `Preserved.stepsN` do the induction.

## 5. What is automatic

### 5.1 The closers

`k2l_preserve` runs on each rule's goal `P lhs → P rhs` these closers in order, and stops at the first that closes the goal completely:

| # | closer | closes |
|---|---|---|
| 1 | untouched | rules that do not change what `P` reads: unfold `P`, then `exact` the hypothesis |
| 2 | compute (only with `split [f, …]`) | goals decided by computing `P`: simp with the unfolding set and the rule's hypotheses, then case on applications of `f` and on enumeration-typed fields of the result, at most `fuel` deep (default 5) |
| 3 | collections | predicates on the keys, values or entries of maps, sets and lists: substitute the rule's equations, split conjunctions, add the facts read off the rule's matched collections (for `EntriesOn Q m` and a match `concat a b = some m`: `Q (k, v)` for an element, `EntriesOn Q x` for the rest), and, from the store terms of both sides, that every key of a map stays a key of the map a rule leaves (`MapHook.KeysIncl`: an operand of a defined `concat` and its result, a map rebound at one key and the original, and the new key of a `concat` with an element); then close each conjunct by a hypothesis, by `apply` of a `@[k2l_coll]` lemma (update, remove, concat, element, unit, `values`, `keys_list`, `entriesOn_inKeys_mono`, …), or, for `EntriesOn Q' m` with a hypothesis `EntriesOn Q m` on the same map, by `entriesOn_mono` and the closer on `Q' p` from `Q p` (a relational invariant whose other map changes: every environment's values stay keys of a store that grows), normalizing a goal no lemma fits by the unfolding set and trying again, with the depth renewed |
| 4 | simp | `simp_all` with the unfolding set |
| 5 | arithmetic | linear arithmetic over `Int`: rewrite the hypotheses and the goal with the unfolding set and the `@[k2l_arith]` lemmas, which state the `Int` and `Bool` hooks in Lean's arithmetic (`IntHook.add a b` is `a + b`, `IntHook.ge a b = true` is `a ≥ b`, `BoolHook.not`, `&&`, `\|\|`), then `omega`; the same step ends the discharger of closer 3's leaves, so the count test `0 ≤ N + 1` of a rebuilt map entry closes from the matched entry's `0 ≤ N` (SIMPLE's `acquire`, `release`) |
| 6 | injections | a variable `x` of the rule that is the argument of a generated injection `inj_S_T x` in the goal (`inj_Expr_KItem HOLE` in a heating rule, `inj_Value_KItem V` in `CALC.assign`): `cases x`, reduce the injection on each constructor, and run closers 1–6 on each case, at most two such splits along one path; an injection is defined by cases on its argument, so a function that matches on its result is stuck until the argument is a constructor |

- Before closers 2–6, the hypotheses that were in context before the tactic and are not named in its lemma list are hidden, and a rule's sort projections `proj_A_B y = some x` are turned into `y = inj_B_A x` and substituted.
- The unfolding set also drops the trivial parts of a proposition (`p ∧ True`, `p ∨ True`, `∀ x, True`, `@[k2l_pres]`), and closer 5 runs `omega` only on what its rewriting leaves, so a leaf that the rewriting alone proves (a test of a constant, as `undefined` in SIMPLE's store test) closes there.
- The unfolding set normalizes `Bool` conjunctions: `(a && b) = true` is `a = true ∧ b = true` and `(a || b) = false` is `a = false ∧ b = false` (`@[k2l_pres]`), so closer 3 splits them as it splits `∧`.
- A goal no closer closes is restored to its state after the case split, so the residual goal is exactly the rule's case.
- Each rule gets a fresh heartbeat budget, `maxHeartbeats`, or `k2l.preserve.maxHeartbeats` when that option is set (in the `Preserved` and hand modes), so it bounds the work on one rule. A rule whose closers reach it is left open with the log line `k2l_preserve: rule r reached the heartbeat limit in its closers; it is left open`, and the other rules are still attempted: the limit is a runtime exception, which `try … catch` rethrows, so the tactic catches it around each rule (before 2026-10-25 it ended the whole tactic). `demos/InvBudget` pins this with `#guard_msgs`.
- The recursion-depth limit (`maxRecDepth`) is the other runtime exception: a closer step that reaches it (a unification or a simp call on a large term) fails like any other step, and the steps after it are tried (before 2026-10-25 it ended the tactic with an error). Unlike the heartbeat limit it does not end the rule, since another step can still succeed within the depth. `demos/InvBudget/InvBudget/RecDepth.lean` pins it on `k2l_coll_close`.

### 5.2 The arguments

```text
k2l_preserve [lemmas]? (split [f, …])? (fuel n)? (hand NS)?
```

| argument | effect |
|---|---|
| `[l₁, …]` | added to the unfolding set (the head of `P`, the `@[k2l_pres]` simp set, `↓reduceIte`); a name that is not a hypothesis, a constant or a simp set is an error that names it |
| `split [f, …]` | enables closer 2, casing on applications of the functions `f` (a typing function `tyOf`, a K function the invariant computes) |
| `fuel n` | the depth of closer 2's case splits |
| `hand NS` | on `Preserved S P` with `S` a generated `Step`: apply `S.preserves_of`, close the case of rule `r` by `NS.r` when that constant exists, and run the closers on the other cases |

The goal may be `Preserved S P`, or one rule's case `Step.Case.r P` (the per-case mode the generated kind 1 cases use: it logs `k2l_preserve: rule r not closed; …` when it fails and nothing when it succeeds).
Lemmas of your own can join the closers through the three attributes the tactic reads (`lean/prelude/KPrelude/InvAttr.lean`): `@[k2l_pres]` adds a simp lemma to every unfolding set, `@[k2l_coll]` adds a lemma that closer 3 tries by `apply`, and `@[k2l_arith]` adds a rewrite that closer 5 applies before `omega`, in a module the cases import.
No demo tags a lemma of its own; the tested routes are naming a simp lemma in `[…]` and proving the case by hand.

### 5.3 Cost

Measured 2026-10-25 on Lean v4.34.0, a shared 32-CPU host at a load of 34 to 43, in the encoding each library has in the gate (the arity-indexed default; per-sort where the row says so), two runs each of `lake env lean FILE`, after the commits of that day up to `main` 173e8d9dc; the SIMPLE rows are older (before the default changed), as they say.

| invariant | kind | rules | automatic | hand | elaboration of the case module |
|---|---|---|---|---|---|
| kimp, `envKeysOk@env` (§3, library `kimpkeys`) | 1 | 79 | 79 | 0 | 1.1–1.2 s wall, 3.4–3.7 s CPU, 1.7 GB |
| kimp, `Invariant D` (§4, `EnvBound/Cases.lean`) | 2 | 79 | 78 | 1 | 1.7–2.0 s, 1.7–2.0 s CPU, 1.6 GB |
| kimp, `envOk@env` and `storeNoIds@env`: every store value is a `Value` and none is an `Id` (`demos/k/kimp-inv`, library `kimpinv`) | 1 | 79 | 79 | 0 | 2.5–4.3 s, 5.9–6.0 s CPU, 1.7 GB |
| kimp, `envAll@env`: the same, by a fold with a parameter (`kimpfold`) | 1 | 79 | 79 | 0 | 1.7–2.5 s, 3.6–3.9 s CPU, 1.6 GB |
| kimp, `topEnvOk`: the same, by a function of the whole configuration (`kimptop`) | 1 | 79 | 79 | 0 | 1.2 s, 3.5–3.7 s CPU, 1.6 GB |
| kimp, `topBoth`: `envOk` and `storeNoIds` conjoined in one function of the whole configuration (`demos/k/kimp-inv/imp-both.k`, `kimpboth`) | 1 | 79 | 79 | 0 | 2.7–5.3 s, 7.4–7.7 s CPU, 1.7 GB |
| `even@v`: counters in two nested cell maps are even (`tests/fixtures/nested`) | 1 | 6 | 6 | 0 | 5.5–5.7 s, 7.8–8.3 s CPU, 1.6 GB (per-sort, 2026-10-24, Lean v4.30.0: 2.7–3.6 s) |
| `storeNat@store`: store values stay non-negative when `alloc` adds an `Int`-range map (`tests/fixtures/range`) | 1 | 3 | 3 | 0 | 2.4–2.6 s, 2.1–2.2 s CPU, 1.6 GB |
| `envsOk`: every value of every worker's `<env>` is a key of `<store>`, two map walks (`tests/fixtures/walk`, per-sort, §9) | 1 | 5 | 5 | 0 | 1.3–2.3 s, 1.8–2.6 s CPU, 1.6 GB |
| KRS IMP, sidecar `Map<Id, Value>` (`demos/k/krs-imp`, `krsimp`) | 1 | 82 | 82 | 0 | 1.4–1.5 s, 2.4–2.6 s CPU, 1.6 GB |
| kimp, ImpTypes runtime typing `WTc envTy G`, generated by `k2lean soundness` (`demos/ImpTypes/ImpTypes/Preserve.lean`, per-sort) | 2 | 79 | 77 | 2 | 11.4–12.4 s, 11.0–11.8 s CPU, 1.8 GB (the hand-written typing it replaced: 5.4–10.3 s at load 12–22, 2026-10-25) |
| kimp, no pending statement assigns `x` (`demos/ImpWrites`) | 2 | 79 | 79 | 0 | 37.6–39.9 s, 34.7–37.1 s CPU, 1.9 GB (per-sort, 2026-10-24, Lean v4.30.0: 7.7–10.8 s); 50 of 79 without closer 6 |
| SIMPLE, `holdsOk@holds`, lock counts ≥ 0 (`demos/k/simple-inv`; per-sort, 2026-10-24, Lean v4.30.0, load 20 to 29) | 1 | 169 | 169 | 0 | 3.4–4.0 s, 2.0 GB |
| SIMPLE, `storeOk@store`: every store value is a `Val` or `undefined` (`demos/k/simple-inv`; per-sort, 2026-10-25, load 15–16) | 1 | 169 | 169 | 0 | 2.4–3.9 s, 1.8 GB |
| SIMPLE, `tStoreOk@T`: the same, by a function of the top cell `<T>` (per-sort, 2026-10-25, load 15–16) | 1 | 169 | 169 | 0 | 2.4–2.6 s, 1.8 GB |
| SIMPLE, environments map into the store (`demos/SimpleEnv`, per-sort; 2026-10-24, Lean v4.30.0, load 20 to 29) | 2 | 169 | 164 | 5 | 26.7–27.3 s, 3.5 GB (main 33.2 s) |

- The module's imports alone take 0.6–1.0 s of each time.
- The per-sort times of 2026-10-24 (Lean v4.30.0, load 12 to 22) compare only roughly with these, at about twice the load: most rows are within a factor of two of them; ImpWrites is the outlier, four times as long and CPU-bound (35–37 s of CPU), since on the arity-indexed encoding it walks `<k>` by one function over the term family (`writesT`).
- `var X[N];`, which binds `N` locations through SIMPLE's recursive function `N ... M |-> K`, was a hand case of `storeOk@store` and `tStoreOk@T` (the hand proof was an induction on the number of keys) until the generator recognized maps built on an `Int` range (§3.1, 2026-10-25): closer 3 applies `Invariant.range_…` to the map the rule binds, and the test of `undefined` closes by rewriting.
- `Preserves.lean` itself takes 0.5 s on kimp and 1.2 s on SIMPLE (per-sort, 2026-10-24).
- A new library is a full build: kimp-based up to `Invariants`, 46 s wall at load 31; SIMPLE-based, 242 s wall and 3.4 GB at load 1–3 (per-sort, 2026-10-24).

## 6. Proving a residual case

A residual case is `Step.Case.r P` with the rule's variables and side conditions in context.
The proofs below are in the tree; each shows one kind of reasoning the closers do not do.

### 6.1 Store typing: `CALC.var`, `CALC.assign` (`demos/ImpTypes/ImpTypes/Store.lean`)

The invariant `WTc envTy G` says the `<k>` computation is well typed under `G` and the store holds a value of `G`'s type at every typed identifier; `k2lean soundness` generates it from the K type checker, all but the store typing `envTy` (`design.md`, §3.3).
`CALC.var` reads the store, so its case needs the store's typing at `X`: the proof rewrites the matched lookup by `MapHook.lookup_of_concat_element hm`, takes the stored value's type from the hypothesis, and cases on the value.

```lean
theorem «CALC.var» (G : TEnv) : KImp.Step.Case.«CALC.var» (WTc envTy G) := by
  intro X K g m v D hm
  rintro ⟨hk, he⟩
  simp only [WTc, kOf, envOf, envCellTy] at hk he ⊢
  refine ⟨?_, he⟩
  simp only [kty_kseq, item_none, item0_inj_Id] at hk ⊢
  cases ht : typeOf G (.inj_Id X) with
  | none => simp [ht] at hk
  | some t =>
    simp only [ht, Option.map_some] at hk
    obtain ⟨v', hl, hv⟩ := he.2 X t ht
    rw [MapHook.lookup_of_concat_element hm] at hl
    obtain rfl := Option.some.inj hl
    cases v <;> simp_all [valTy, item0_inj_Int, item0_inj_Bool, typeOf.inj_Int, typeOf.inj_Bool]
```

`CALC.assign` writes the store: the proof splits on whether a typed identifier `x` is `X` (`MapHook.lookup_update_self`) or another key (`MapHook.lookup_update_ne`, from `SAL.lookup_insert_ne`), the same split as `boundIn_update` in §4.4.

### 6.2 Monotonicity: SIMPLE's store-growing rules (`demos/SimpleEnv/SimpleEnv/Cases.lean`)

The kind 2 invariant says every environment value is a location of `<store>`.
Five rules add or overwrite a store binding (`var X;`, `var X[N];`, `function F(Xs) S`, `++ loc(L)`, `loc(L) = V`): before the step `P` speaks of the store `S`, after it of a larger `S'`, and no closer carries a predicate from `S` to `S'`.
Each hand case proves that the store grows (`grow_right` for a new binding, `grow_overwrite` for an overwritten one, from `MapHook.mem_toList_of_concat`), lifts the invariant along it (`threadOk_mono`, `envIn_mono`), and hands the rest to the collections closer through a local macro:

```lean
theorem «var X;» : KSimple.Step.Case.«var X;» (Invariant) := by
  intro m Gen7 DotVar2 Gen6 Gen10 Gen8 Gen9 L DotVar0 k DotVar3 X DotVar5 Gen11 Env Gen12 r r_2 hm hr hr_3 hpri
  intro h
  have hg := grow_right hr_3
  have hL := inStore_left_element hr_3
  grow_close hm hg h
```

`grow_close` ends with `k2l_coll_close [lemmas]`, the collections closer on its own, which is the usual way to finish a hand case once the step the closers miss is done.

### 6.3 Useful lemmas

| lemma (namespace `KPrelude`) | says |
|---|---|
| `MapHook.update_def`, `MapHook.lookup_def` | `update` and `lookup` through the sorted association list `SAL` |
| `SAL.mem_insert`, `SAL.mem_insert_self`, `SAL.mem_insert_of_mem_ne`, `SAL.lookup_insert_self`, `SAL.lookup_insert_ne` | membership and lookup after an insert, at the inserted key and at another key |
| `MapHook.lookup_update_self`, `MapHook.lookup_update_ne` | `M[K <- V][K]` is `V`, and `M[K <- V][K']` is `M[K']` when `K' ≠ K` |
| `MapHook.mem_toList_of_concat` | a binding of a defined `concat a b` is a binding of `a` or of `b`, and conversely |
| `MapHook.entry_of_concat_element`, `MapHook.entriesOn_of_concat_right` | the matched binding of `K |-> V REST`, and the rest |
| `MapHook.entriesOn_update`, `_concat`, `_element`, `_unit`, `_remove` | `EntriesOn Q` kept by each map operation |
| `MapHook.lookup_of_concat_element` | the lookup of the matched key |
| `MapHook.entriesOn_of_range` | a map built by recursion on an `Int` range, from its two equations, binds its value at each of its keys (the lemma behind `Invariant.range_f`) |
| `MapHook.all_iff_of_walk` | a function with the equations of a map walk is `true` exactly on the well-formed maps whose every binding passes its test (the lemma behind `Invariant.f_walk`) |
| `MapHook.wf_of_concat`, `wf_rest_of_concat_element`, `wf_update`, `wf_remove`, `wf_unit`, `wf_element` | a rule's rebuilt map is well formed (`@[k2l_coll]`, for the `WF m` that a walk's element-wise form states) |
| `ListHook.elemsOn_keysList`, `ListHook.elemsOn_values`, `ListHook.elemsOn_keysList_iff`, `ListHook.elemsOn_values_iff` | list predicates over `keys_list(M)` and `values(M)`; the two `_iff` (`@[k2l_pres]`) state them on `M`'s bindings |

They are in `lean/prelude/KPrelude/{InvColl,Coll,SAL,InvFold}.lean`.

## 7. Regeneration and hand proofs

### 7.1 Stable rule names

A rule's name, which names its `Step` constructor, its `Step.Case`, its kind 1 case and its hand case, is:

1. its K label, when it has one (`CALC.assign`, `IMP.while`);
2. otherwise the focus of its left-hand side in K syntax: the first item of the first `<k>` cell, or the first non-cell term (`«X + Y»`, `«if(true) S else _»`); variables keep their source names, and a variable at the root of the focus gets its sort (`«X:Id»`);
3. when several rules share a focus, each with its variables' sorts (`«X:Int * Y:Int»`);
4. when that still collides, ` #` and 6 hex digits of a digest of the whole rule (`«acquire V:Val; #59f263»`).

The source position is a doc comment, not part of the name, so inserting lines, comments or unrelated rules renames nothing.
These edits rename a rule:

- adding, removing or changing its label;
- changing the focus of an unlabelled rule: its head, its arguments, a variable name in it, a sort cast at its root;
- adding a rule with the same focus (both gain sorts or a digest), or removing the other rule of such a pair (the survivor loses them);
- for a rule with a digest: any change to its left-hand side, `requires` or right-hand side, and any change to the configuration declaration.

kimp has no digest names; SIMPLE has 10.
Prefer labels (`rule [name]: …`) for rules that have hand cases.

### 7.2 `k2lean diff`

```text
$G diff OLD NEW [--hand PATH]… [--toml FILE]
```

`OLD` and `NEW` are two generated library directories.
It compares their `Step.Case` statements by rule name, after renaming bound variables, and reports the rules changed (and which parts: variables, side conditions, sides), renamed with an equal statement, renamed and changed (suggested), added, removed, and those whose priority context changed.
`--hand PATH` scans the `.lean` and `.txt` files under `PATH` for references to rules (`Step.Case.r`, `Step.r`, `App.r`, `case r` tags, `open-invariant-cases.txt` lines) and lists the ones to revisit with file and line.
It also compares the generated functions (`NS/Functions.lean`, written from their K equations): each function whose definition changed, was added or was removed is listed with the rules whose cases call it, directly or through other generated functions, and with the kind 1 invariant when it calls it (`NS/InvariantDefs.lean`), since then every case's meaning changed.
With `--hand`, a reference to a rule that calls a changed or removed function is a case to revisit, and so is each mention of such a function (`K.f`, `Eqn.f_N`) in a hand-written file.
A function is compared as the text of its definitions, so renaming a variable of one of its equations also reports it as changed.
Exit status: 0 when nothing differs, 1 when something does, 2 on an error.

### 7.3 An edit, step by step

Try it on a copy of the work directory, with an edited copy of kimp's sources: a comment line at the top of every file, `CALC.var` matching only `Value`s, and `CALC.assign` allowed only on bound variables.

```sh
W2=$W-edit
rm -rf $W2 && cp -a $W $W2
cp -r $KIMP $W2/kimp
for f in $W2/kimp/*.k; do sed -i '1i // edited copy' $f; done
sed -i 's/<env> X |-> V \.\.\. <\/env>/<env> X |-> V:Value ... <\/env>/' $W2/kimp/calc.k
sed -i 's/^    <env> E => E \[ X <- V \] <\/env>$/&\n    requires X in_keys(E)/' $W2/kimp/calc.k
diff $KIMP/calc.k $W2/kimp/calc.k
```

Regenerate both libraries in the copy, then compare:

```sh
(
  KIMP=$W2/kimp GEN=$W2/k2lean/generated
  kore_dir() { echo "$W2/kore/$1"; }
  libs_kcompile kimp && libs_kcompile kimp-verif && libs_gen kimp
  $KRUST kcompile $W2/k/imp-keys.k --main-module IMP-KEYS --syntax-module IMP-SYNTAX \
    --output-directory $W2/kore/kimp-keys --builtin-directory $BUILTIN -I $KIMP
  $G gen --kore $W2/kore/kimp-keys/definition.kore --runtime $W2/kore/kimp-keys/runtime.json \
    --out $GEN/kimpkeys --name KImpKeys --prelude ../../lean/prelude \
    --open-obligations $GEN/kimpkeys/open-obligations.txt --invariant envKeysOk@env
)
$G diff $GEN/kimp $W2/k2lean/generated/kimp --hand $W2/EnvBound
$G diff $GEN/kimpkeys $W2/k2lean/generated/kimpkeys --hand $W2/k2lean/generated/kimpkeys | sed -n '/^hand-written/,$p'
```

```text
changed 2, added 0, removed 0, renamed 0 (same statement), renamed and changed 0 (suggested), context changed 0; unchanged 77 (77 moved)
functions: changed 0, added 0, removed 0; unchanged 1
…
  «CALC.assign»  calc.k:32:3 -> calc.k:33:3: side conditions differs
      side conditions:
        - hp : proj_Expr_Value y = some V
        + hp : proj_Expr_Value y = some V, hreq : KPrelude.MapHook.inKeys (SortKItem.inj_Id X) E = true

hand-written references (files read: 5):
  revisit 1 rule(s):
  «CALC.assign»: changed (side conditions differs)
      …/EnvBound/EnvBound/Cases.lean:26 (case)
```

`CALC.var` changed too, but nothing refers to it, so it is not listed; 77 rules moved and are unchanged, and so is kimp's one generated function (`isKResult`).
Build both invariants:

```sh
(cd $W2/EnvBound && lake build 2>&1 | grep -E "k2l_preserve|^error|Build completed")
(cd $W2/k2lean/generated/kimpkeys && lake build KImpKeys.Invariants 2>&1 | grep -E "^error|Build completed")
```

Each fails at its hand case of `CALC.assign` only: the rule gained the side condition `hreq`, so the introductions in the hand proofs bind the wrong hypotheses.
`preserved` still elaborates (`78 of 79 rules closed; hand: [«CALC.assign»]`), and `CALC.var`'s case is closed automatically in both.
Add the new name to both introductions and rebuild:

```sh
sed -i 's/^  intro X y DotVar1 E DotVar0 V hp$/  intro X y DotVar1 E DotVar0 V hp hreq/' $W2/EnvBound/EnvBound/Cases.lean
sed -i 's/^  intro X y DotVar1 E DotVar0 V hp h$/  intro X y DotVar1 E DotVar0 V hp hreq h/' \
  $W2/k2lean/generated/kimpkeys/KImpKeys/InvariantsHand.lean
(cd $W2/EnvBound && lake build 2>&1 | grep -E "^error|Build completed")
(cd $W2/k2lean/generated/kimpkeys && lake build KImpKeys.Invariants 2>&1 | grep -E "^error|Build completed")
rm -rf $W2
```

### 7.4 What breaks and what does not

| after a K edit | effect on your proofs |
|---|---|
| lines, comments or unrelated rules inserted | nothing: names do not depend on positions |
| a rule changed that has no hand case | its case is re-proved by the closers; it fails only if they no longer close it, and then it is reported as open |
| a rule changed that has a hand case | that hand case may fail to build, and no other; `diff --hand` names it |
| a rule renamed (§7.1) | its hand case fails at its own statement (`unknown constant Step.Case.r`); `diff` reports the rename |
| a rule added | nothing unless the closers fail on it (kind 1: build, then `open-from-log`; kind 2: it appears in `open`) |
| a rule removed | its hand case fails at its statement; delete it |
| a function's equations changed | the rule statements may be equal, but the case's meaning changed: `diff` reports the function with the rules that call it, and `--hand` the hand cases of those rules; rebuild and read the results |
| a side condition added or removed | the hand case's introductions shift (§7.3) |

## 8. Strengthening a non-inductive invariant

A property can hold at every reachable configuration and still not be inductive: some rule breaks it from a configuration that satisfies it but is not reachable.
The rule-by-rule proof then fails at that rule, and the fix is to strengthen `P` so that the unreachable configurations are excluded.

SIMPLE's "every value of every thread's `<env>`, and of `<genv>`, is a location of `<store>`" is not inductive:

- The block rule `{ S } => S ~> setEnv(Env)` saves the environment in the computation, and the rule `setEnv(Env)` installs whatever map it carries.
- A configuration with `<k> setEnv(x |-> 7) ~> K </k>`, `<env> .Map </env>` and `<store> .Map </store>` satisfies the plain statement and steps to `<env> x |-> 7 </env>`, which does not.
- The same holds for the environments saved in stack frames (`return`, `throw`) and for `<genv>` (a function call).

The strengthened invariant (`demos/SimpleEnv/SimpleEnv/Invariant.lean`) also says it of every environment a thread holds: the `setEnv(E)` items of its `<k>`, and every stack frame's environment, saved computation and saved control, recursively.

```lean
def ThreadOk (S : SortMap) (p : SortIdCell × SortThreadCell) : Prop :=
  EnvIn S (envOf (thEnv p.2)) ∧ AllIn S (envsK (kOf (thK p.2))) ∧
    AllIn S (envsL (fsOf (ctlF (thCtl p.2)))) ∧ AllIn S (envsL (xsOf (ctlX (thCtl p.2))))

def Invariant (c : SortGeneratedTopCell) : Prop :=
  MapHook.EntriesOn (ThreadOk (storeOf (tStore (topT c)))) (threadsOf (tThreads (topT c))) ∧
    EnvIn (storeOf (tStore (topT c))) (genvOf (tGenv (topT c)))
```

It implies the plain statement (its first conjunct), and it is inductive: 164 of 169 rules close automatically and the 5 store rules by hand (§6.2).
How to find the strengthening: read the open goal of the failing rule, find where the value the rule installs comes from (here, a `setEnv` item or a stack frame), and add the property of that source to `P`.
`Preserved.and_under` (`lean/prelude/KPrelude/Invariant.lean`) proves a conjunction in stages: `Preserved S P` and `PreservedUnder S P Q` (`Q` kept by the steps from configurations satisfying `P`) give `Preserved S (P ∧ Q)`.

## 9. Limitations

| limitation | consequence | workaround |
|---|---|---|
| inductive invariants only | a non-inductive property fails at a rule | strengthen it (§8) |
| nothing about undefined steps | a rule with an undefined result has no `Step` | state undefinedness through `App` and the adequacy theorems |
| configuration variables are arbitrary at `init` | `init_holds` needs hypotheses on `pgm`, `env` | state them; they are what a caller must establish |
| relational invariants over a map that rules extend | a map walk (§3.1) whose test reads another cell, such as SIMPLE's "every value of every thread's `<env>` is a key of `<store>`" (`envsIn@T`, `demos/k/simple-inv/simple-envs.k`), needs that a key of the store stays a key where a rule changes the store; the collections closer derives it from the rule's store terms (§5.1, 2026-10-25): on SIMPLE, 164 of 169 cases at the default budget (161 before, 8 before the walks; per-sort, Lean v4.34.0), and 166 at `maxHeartbeats` 400,000 (`++ loc(L)` and `loc(L) = V` need more than the default). The 3 left, `setEnv(Env)`, `return V;`, `throw V;`, are where the statement is false (it is not inductive, §8). Its strengthening over computations and stack frames, `envsOk@T` (the statement of `demos/SimpleEnv`), tests each thread with a mutual recursion over `K`, lists and frames (`kIn`, `listIn`, `itemIn`, `ctlIn`), which is neither a walk, a fold nor structural recursion: 8 of 169, and 9 GB for its case module. None of these is in the gate (the fixture `walk` is: its store rules close only through the monotonicity) | write the invariant in Lean (`demos/SimpleEnv`, 164 of 169), or raise `maxHeartbeats` for the two update rules |
| arithmetic is linear | closer 5 is `omega` on the total `Int` hooks: a case that needs a product of variables, or `/Int`, `%Int`, `^Int` (partial hooks, `Option`-valued, not unfolded), stays open | a hand case, or a lemma of the step it needs passed to `k2l_preserve` |
| injection splits: of variables, two along a path | closer 6 cases only on a variable under an injection (not on `inj_S_T (f x)`), at most twice on one path | a lemma `f (inj_S_T e) = …` by `cases e <;> rfl`, passed to `k2l_preserve` |
| `owise` side conditions by simp | an `owise` equation rewrites only where simp proves that no other equation matches, from the argument's constructors; on `isId(kseq(inj_Value_KItem V, .K))` it applies only in closer 6's cases of `V`; the generator states it at injections when every other pattern is a constructor of `KItem`'s own (§3.1), not otherwise | a lemma of the injection, or a hand case |
| recursive functions of a few shapes only | a recursive function that the invariant calls and that is none of the shapes of §3.1 (a map walk, a list or `K` fold, structural recursion with proved equations, a function of a fold's group) gets a note (`… is neither a map walk, a list fold nor structurally recursive with proved equations; its cases may need hand proofs`), and its cases usually become hand cases: a fold through `orBool`, a list fold whose test is partial, a fold whose recursive call changes a parameter, a recursion on an `Int` bounded by a `requires` other than a map built on a range (§3.1). SIMPLE's `envsOk@T` (`kIn`, `listIn`, `itemIn`, `ctlIn`): 158 of 169 cases with the `K` fold, `itemIn` and `ctlIn` unfolded and `itemIn`'s `owise` equation at injections (8 before; per-sort, 2026-10-25, 62 s wall, 353 s CPU, 3.4 GB); open: the five rules that change the store (they need `itemIn`'s monotonicity in it), the four that push or pop a stack frame (`listIn`'s list equation does not prove yet, core's EQ-11), `spawn S`, and `popx` (which closes at `maxHeartbeats` 400,000) | rewrite it in one of the two shapes, or write the invariant in Lean |
| a variable as the whole content of a cell collection's parent, annotated | until 2026-10-25 krust compiled `<T> <threads> Ts </threads> … </T>` (`<threads>` holds the `<thread>` cell map) as `<threads>` holding one `<thread>` cell `Ts`; since `main` 8255e8d03 a bare `Ts` there, used elsewhere at the cell map's sort, is the whole cell map; only the annotation written inside the cell (`<threads> Ts:ThreadCellMap </threads>`) does not parse, while the sort written at another occurrence (`f(Ts:ThreadCellMap)`) parses and means the same | write the variable bare in the cell, with its sort elsewhere if needed, or take the parent cell (`TS:ThreadsCell`) and walk it as `<threads> <thread> … </thread> Ts </threads>`, as `simple-envs.k` does; there `Ts` is the rest of the cell map |
| no `<generatedTop>` through krust for a configuration with one top cell | for SIMPLE (whose configuration is the one cell `<T>`), krust declares the sort `GeneratedTopCell` and the production `<generatedTop>` only after parsing, in the compilation pass that adds the counter cell (`resolve_fresh_constants.rs`), whereas a configuration of several top cells (kimp's `<k> <env>`) gets them when the configuration declaration is expanded (`definition/configuration.rs`, `Generator::generate`, the `Cells` case): `f(GeneratedTopCell)` fails with ``Could not find sorts: [GeneratedTopCell]``, and with `syntax GeneratedTopCell` declared, the rule fails with ``unexpected token '<'`` | a function of the user's top cell (`tStoreOk@T`, §3.1), which reads every cell but the counter; decided 2026-10-25: krust keeps a single top cell unwrapped, so this is the form to use, not a stopgap |
| map walks on the arity-indexed encoding | the generated proof of a walk's element-wise form (`Invariant.f_walk`, §3.1) leaves open the fallback arm of a projection's match on a cell sort with one constructor, which the arity encoding's family adds (found by K6, 2026-10-25), so the library fails to build | generate the library with `--per-sort-terms`, as the gate's `walk` is |
| a tree of cells, one equation | a function of a cell sort gets `Invariant.f_cells` only when it is not recursive and its one equation, without `requires` or `owise`, matches a tree of cells with distinct variables at the leaves; with any other pattern (a constructor inside a cell, two equations, a `requires`) it is unfolded by its K equations only, which rewrite a constructor term and not a rule's cell variables (on kimp, before `f_cells`: 2 of 79 cases and `init` open, measured) | state the invariant over the cell, or split it into cell functions |
| Lake does not build the dependents of a module with an error | a broken hand case leaves `Run.lean` (kind 2) or `Invariants.lean` (kind 1) unchecked; Lake names only the module that failed, the gate prints the others (`gate:   failed: M; not built because they import it: …`, after the step's FAIL line) | keep hand cases in `Cases.lean` with `preserved`, as the skeleton does; fix the hand case first |
| heartbeats | in the `Preserved` and hand modes the elaboration of the proof after the tactic counts every rule's heartbeats, so a definition with many rules can reach `maxHeartbeats` at `preserved` though each rule is within it (measured on SIMPLE) | `set_option maxHeartbeats 0` on the proof, with `set_option k2l.preserve.maxHeartbeats N` to keep each rule bounded (without it, `maxHeartbeats 0` leaves the rules unbounded too); ImpTypes' `Cases.lean` has the first |
| introductions are positional | an added or removed side condition shifts the names a hand case introduces | fix the `intro` line (§7.3) |
| digest names | a rule named with a digest is renamed by any change to it or to the configuration declaration | label the rule |

## 10. Checking with the gate

`$K/tests/gate.sh light|heavy` regenerates every library and demo of `k2lean/` from the K sources, builds them in a work tree of its own, and compares what it measures with its baseline (`$K/tests/baseline/AREA.toml`, one file per area): open sets may only shrink, `k2l_preserve` counts may not drop, axiom guards may not lose theorems, no `sorry`, and regenerated sources must equal the last accepted generation.
`docs/testing.md` of the repository says when it is owed and how it runs in CI (`k2lean-light`, `k2lean-heavy`).
To have it ratchet a new invariant, register it in the two files of the invariants area, put its inputs in the tree, run a tier, and accept.
The library `kimpkeys` of §3 is registered so (with `kimpkeys-hand`, the same library with `CALC.assign` listed as a hand case, §3.4); the kind 2 project `EnvBound` of §4 is not, and the steps below add it.

1. The inputs, in the k2lean directory `T` the gate checks (`T=$K` for real; git tracks exactly these files):

   ```text
   T/demos/k/kimp-keys/imp-keys.k                    the K module of §3.1 (in the tree)
   T/generated/kimpkeys/open-obligations.txt         a library's open lists and hand module (in the tree): the
   T/generated/kimpkeys/open-invariant-cases.txt     rest of generated/ is regenerated by every run, and git
   T/generated/kimpkeys-hand/KImpKeys/InvariantsHand.lean   ignores it
   T/demos/EnvBound/EnvBound/{Invariant,Cases,Run}.lean   the three modules of §4 (to add)
   T/demos/EnvBound/{lakefile.lean,lean-toolchain}
   ```

   A kind 2 project under `demos/` must require `../../lean/prelude` and `../../generated/kimp`; copy the three modules first and then run `$G new-invariant --lib $T/generated/kimp --out $T/demos/EnvBound` with a generated kimp in `$T/generated/kimp` (from `demos/regen.sh`), which writes the lakefile with those paths and keeps the modules.
2. The registrations, in the two files of the gate's invariants area (`docs/testing.md` of the repository lists the areas): `tests/areas/invariants.sh` (how to compile and generate, and the phase that builds the entry) and `tests/areas/invariants.py` (what is measured, and the entry's tier).
   The `kimpkeys` lines show the shape of a kind 1 library's registration (the tree has them, with `kimpkeys-hand` beside them); the `EnvBound` lines are the ones to add:

   ```diff
   --- a/k2lean/tests/areas/invariants.sh
   +++ b/k2lean/tests/areas/invariants.sh
   @@ kore_invariants
        kimp-inv) f=$DEMOS/k/kimp-inv/imp-inv.k m=IMP-INV s=IMP-SYNTAX inc=$KIMP ;;
   +    kimp-keys) f=$DEMOS/k/kimp-keys/imp-keys.k m=IMP-KEYS s=IMP-SYNTAX inc=$KIMP ;;
   @@ name_invariants
   +    kimpkeys|kimpkeys-hand) echo KImpKeys ;;
   @@ gen_invariants
   +    kimpkeys|kimpkeys-hand) GEN_ARGS=(--kore "$(kore_dir kimp-keys)/definition.kore" --runtime "$(kore_dir kimp-keys)/runtime.json"
   +            --out "$o" --name KImpKeys --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt"
   +            --invariant envKeysOk@env) ;;
   @@ gate_invariants
   +  runs lib kimpkeys && kc kimp-keys && inv_lib kimpkeys KImpKeys
   …
   -  diffs kimpinv kimpfold kimptop kimpboth nested …
   +  diffs kimpinv kimpkeys kimpfold kimptop kimpboth nested …
   …
   -  for d in ImpWrites KrsImpTyping SimpleEnv InvBudget; do
   +  for d in ImpWrites KrsImpTyping SimpleEnv InvBudget EnvBound; do
        runs demo "$d" || continue
   --- a/k2lean/tests/areas/invariants.py
   +++ b/k2lean/tests/areas/invariants.py
    LIBS = {
   +    "kimpkeys": {"ns": "KImpKeys", "tier": "light", "guard": False},
    INVS = {
   +    "kimpkeys": {"ns": "KImpKeys", "tier": "light"},
    DEMOS = {
   +    "EnvBound": {"tier": "light"},
   ```

   - `guard: False`: the library is built only as far as its invariant needs, so it has no `…Test.Axioms` guard; the invariant's own `#k2l_assert_axioms` is checked through `INVS`.
   - `inv_lib` (in `invariants.sh`) generates the library, builds its `Equations` and its `Invariants`, and turns a case that `k2l_preserve` does not close into an open case; `runs KIND NAME` holds when the tier being run includes the entry's tier.
   - A heavy invariant (SIMPLE-based) gets `"tier": "heavy"`; nothing else changes.
   - Libraries are generated in the arity-indexed encoding by default (since 2026-10-25); an entry that must stay on the per-sort encoding gets `"encoding": "per-sort"` and `--per-sort-terms` in its generator call (`walk` has both, §9), and a demo on per-sort libraries `"encoding": "per-sort"` (SimpleEnv). EnvBound builds on the default kimp (checked 2026-10-25), so it needs neither.
   - `tests/gate.sh list` prints the registered entries, which checks the new ones.
3. Run a tier, read its `FAIL` and `NOTE` lines, accept, and run again:

   ```text
   $T/tests/gate.sh light
   $T/tests/gate.sh accept --area invariants
   $T/tests/gate.sh light
   ```

   The first run passes with a `NOTE` line for what the baseline does not have yet (a new kind 1 library adds `lib.NAME`, `inv.NAME` and `sources` notes):

   ```text
   gate: NOTE demo.EnvBound: not in the baseline
   gate: light passed
   ```

   `accept --area invariants` (which refuses a run with failed steps, banned items or failing unit tests, and a run in which another area's measured entries differ from that area's baseline) writes the new entries to `T/tests/baseline/invariants.toml`: for EnvBound, 78 of 79 closed with hand `[«CALC.assign»]`, 5 guarded (for kimpkeys the baseline has 79 cases, 79 automatic, open `[]`, 4 guarded).
   The second run passes with no `NOTE`.
   From then on the gate fails if a hand case breaks (`FAIL step build EnvBound`, `FAIL demo.EnvBound: not built`), an open set grows, or a `k2l_preserve` count drops.
   A kind 1 hand module (`generated/kimpkeys-hand/KImpKeys/InvariantsHand.lean`) is, like the open lists, an input that a person writes: the sources check does not hash it, and the build of the invariant checks it, so an edit that still proves its cases passes and one that does not fails (`FAIL step invariant kimpkeys-hand`).

To rehearse without touching your checkout, make a worktree of it (`git worktree add`), edit there, and run the worktree's gate with `GATE_KRUST_REPO=$R` (the checkout with krust and the K and kimp sources) and your own `GATE_WORK` and `GATE_CACHE`; `GATE_SEED=DIR` copies the `.lake/` directories of an existing work tree first, which makes the run incremental (`tests/gate.sh` with no argument prints every variable).

## 11. Further reading

| demo | kind | what it shows |
|---|---|---|
| `demos/k/kimp-inv/imp-inv.k` (libraries `kimpinv`, `kimpfold`, `kimptop`, light gate) | 1 | `kimpinv`: two `values` folds conjoined (`envOk`, and `storeNoIds`, whose test `notBool isId(X)` on the value `CALC.assign` stores closes by the injection split); `kimpfold` and `kimptop`: `envOk`'s property by a fold with a parameter and in the top-cell form; each 79 of 79 automatic, `init_holds` from hypotheses |
| `demos/k/kimp-inv/imp-both.k` (library `kimpboth`, light gate) | 1 | `kimpinv`'s two parts as one function of the whole configuration, a conjunction of two partial calls, 79 of 79 automatic |
| `demos/k/kimp-keys/imp-keys.k` (libraries `kimpkeys` and `kimpkeys-hand`, light gate) | 1 | the `keys_list` fold of §3, 79 of 79 automatic; `kimpkeys-hand` takes `CALC.assign` from its hand module (§3.4) |
| `tests/fixtures/nested/nested.k` (library `nested`, light gate) | 1 | a cell inside two nested cell maps and a structurally recursive invariant, 6 of 6 automatic, `init_holds` by computation |
| `tests/fixtures/range/range.k` (library `range`, light gate) | 1 | a store extended by a map built on an `Int` range (`fill`), 3 of 3 automatic through `Invariant.range_fill…` |
| `demos/k/simple-inv/simple-inv.k` (library `simpleinv`, heavy gate) | 1 | the cell-map lift over SIMPLE's threads, 169 of 169 automatic, the lock counts by linear arithmetic |
| `demos/k/simple-inv/simple-inv.k`, `generated/simplestore/`, `generated/simplet/` (libraries `simplestore`, `simplet`, heavy gate) | 1 | one property of `<store>` as a cell function and as a function of `<T>`, 169 of 169 each (`var X[N];` through the `Int`-range lemma of `N ... M \|-> K`) |
| `demos/k/krs-imp/k2lean-sidecar.json`, `demos/KrsImpTyping/` | 1 | the KRS sidecar, proved equivalent to a hand-written typing predicate |
| `demos/ImpTypes/ImpTypes/Store.lean` (with `Typing.lean` and `Soundness.lean`, generated by `k2lean soundness`) | 2 | a runtime typing generated from a K type checker, parametrized by a hand-written store typing, with `split [typeOf, wt]`; two store hand cases |
| `demos/ImpWrites/ImpWrites/{Invariant,Cases,Run}.lean` | 2 | a predicate that walks `<k>` (no pending statement assigns `x`), 79 of 79 automatic, 29 of them through the injection split |
| `demos/InvBudget/` (light gate) | 2 | `k2l_preserve`'s per-rule heartbeat budget: on `range`, `alloc` reaches a budget of 2,000 and is left open while `seq` and `set` close, checked by `#guard_msgs`; and a collections-closer step at the recursion-depth limit fails like any other (`RecDepth.lean`) |
| `demos/SimpleEnv/` | 2 | a relational, strengthened invariant over SIMPLE, five monotonicity hand cases |
| `demos/k/simple-inv/simple-envs.k` (not in the gate) | 1 | the same statement, plain and strengthened, as K functions over `<T>` that walk the thread cell map: 161 of 169 automatic for the plain one, 8 for the strengthened one (§9) |
| `tests/fixtures/walk/walk.k` (library `walk`, light gate) | 1 | a relational invariant written as two map walks, over the `<workers>` cell map and over each worker's `<env>`: 5 of 5 automatic, the post-state maps' well-formedness by the `@[k2l_coll]` lemmas `MapHook.wf_of_concat` and the others |
| `lean/prelude/KPrelude/InvTactic.lean` | — | the tactic's documentation |
| `lean/prelude/KPrelude/Invariant.lean`, `InvSteps.lean` | — | `Preserved`, `PreservedUnder`, `Star`, `StepsN`, the typed view `TConfig` and `OnCell` |
