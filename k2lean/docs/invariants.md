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

`elan`, `lean` and `lake` must be on `PATH`; each project's `lean-toolchain` selects Lean v4.30.0, which elan installs on first use.

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
`$K/tests/libs.sh` holds the exact calls for every library of the gate; source it, set the variables it reads, and define `kore_dir NAME` to say where the compiled KORE goes.
This generates kimp in your work tree; the gate checks that these files do not change without a reviewed baseline (`tests/baseline.toml`, `[sources]`):

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
  A library generated with an empty list whose `Equations.lean` then fails to build is fixed by `$G open-from-log NS/Equations.lean BUILD.log open-obligations.txt` and a second `gen`; starting from an existing library's list (kimp has 5) avoids the round.
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
| cell-map lift | `f(S)` over a cell inside a cell collection (`--invariant holdsOk@holds` on SIMPLE, where `<holds>` is inside the `<thread>` cell map) | "for every element": `MapHook.EntriesOn` over the collection's bindings, so the closers read the invariant of the matched element; one level of collection only |
| list fold | `f(.List) => true` and `f(ListItem(X) L) => φ(X) andBool f(L)` (or `f(L) andBool φ(X)`), no `requires`, `φ` total, `f` with one argument | the theorem `f l = true ↔ every element satisfies φ` (`Invariant.f_iff`), which the collection lemmas read |
| non-recursive helpers | ordinary equations | their K equations (`Eqn.*`) join the unfolding set |
| a map walked by pattern (`f(K |-> V M)`) | not supported: the generator panics (§9); fold over `values(M)` or `keys_list(M)` instead | — |
| top-cell form | `f(GeneratedTopCell)` and `--invariant f` without a cell | supported by the generator, but closes almost nothing (§9); use the cell form or kind 2 |

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
grep -E "k2l_preserve|^error" $W/kimpkeys-1.log
```

The first build compiles the whole library (46 s here, 40 s of it `Terms.lean`), and fails:

```text
info: KImpKeys/Invariants.lean:88:64: k2l_preserve: rule «CALC.assign» not closed; the goal is its case, with the rule's variables and side conditions introduced
error: KImpKeys/Invariants.lean:88:61: unsolved goals
error: KImpKeys/Invariants.lean:362:0: KImpKeys.Invariant.preserved depends on disallowed axioms [sorryAx]
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
- `init_holds` follows the configuration declaration: a cell that holds a configuration variable (`<env> $ENV:Map </env>`) gives a hypothesis on that parameter; a cell with a closed term is proved by computation; anything else makes `init` an open case (`Invariant.hand.init`).
- `#k2l_assert_axioms` fails the build when a theorem depends on `sorryAx` or on an axiom other than `propext`, `Classical.choice`, `Quot.sound`.
- `Invariant` is named so, not `Inv`, because core Lean declares a class `Inv`.

### 3.4 Open cases and the hand module

A case the tactic does not close becomes an open case: it is listed in `open-invariant-cases.txt`, and `Invariants.lean` takes it from the hand module `KImpKeys/InvariantsHand.lean` as the theorem `Invariant.hand.r` with the same statement.

```sh
cd $GEN/kimpkeys
$G open-from-log KImpKeys/Invariants.lean $W/kimpkeys-1.log open-invariant-cases.txt
$G gen --kore $W/kore/kimp-keys/definition.kore --runtime $W/kore/kimp-keys/runtime.json \
  --out $GEN/kimpkeys --name KImpKeys --prelude ../../lean/prelude \
  --open-obligations $GEN/kimpkeys/open-obligations.txt --invariant envKeysOk@env
grep -v '^#' open-invariant-cases.txt
```

The list now reads `«CALC.assign» | Step.Case.«CALC.assign» Invariant | calc.k:32:3`: the case, its statement, the rule's position.
The generator wrote `KImpKeys/InvariantsHand.lean` once, with the statement in a comment and the generated unfolding set in its header; it never overwrites that file.
Until the theorem exists, the build fails at `Invariant.case.«CALC.assign»` with ``Unknown constant `KImpKeys.Invariant.hand.«CALC.assign»` ``, which names the rule.

To prove the case, read its statement in `KImpKeys/Preserves.lean` (or in the `unsolved goals` error):

```lean
def Step.Case.«CALC.assign» (P : SortGeneratedTopCell → Prop) : Prop :=
  ∀ (X : SortId) (y : SortExpr) (DotVar1 : SortK) (E : SortMap) (DotVar0 : SortGeneratedCounterCell)
    (V : SortValue) (hp : proj_Expr_Value y = some V),
    P (… (SortEnvCell.«<env>» E) DotVar0) →
    P (… (SortEnvCell.«<env>» (KPrelude.MapHook.update E (SortKItem.inj_Id X) (inj_Value_KItem V))) DotVar0)
```

The tactic leaves it because the hypothesis is a fact about `keys_list(E)`, and no lemma turns it into a fact about `E`'s bindings, which the update lemma needs.
The hand proof does that step:

```sh
cat > $GEN/kimpkeys/KImpKeys/InvariantsHand.lean <<'EOF'
import KImpKeys.InvariantDefs

/-! Hand-written proofs of the cases of `Invariant` listed in `open-invariant-cases.txt`. -/

namespace KImpKeys

open KPrelude

/-- Rule `CALC.assign` (calc.k:32:3): the updated store's keys are the old keys and `X`. -/
theorem Invariant.hand.«CALC.assign» : Step.Case.«CALC.assign» Invariant := by
  intro X y DotVar1 E DotVar0 V hp h
  simp only [Invariant, Invariant.envKeysOk, Invariant.cell_env, Invariant.content_env,
    Eqn.«envKeysOk(_)_IMP-KEYS_Bool_Map_1», Invariant.allIds_iff, Option.bind_fun_some] at h ⊢
  apply ListHook.elemsOn_keysList
  apply MapHook.entriesOn_update
  · intro p hp
    apply h p.1
    unfold MapHook.keysList
    rw [ListIso.toList_ofList]
    exact List.mem_map_of_mem hp
  · exact Eqn.isId_1 X

end KImpKeys
EOF
(cd $GEN/kimpkeys && lake build KImpKeys.Invariants 2>&1 | grep -E "depends on|^error|Build completed")
```

The build completes; the four theorems depend on `propext`, `Classical.choice` and `Quot.sound` only.

- The `simp only` list is the generated unfolding set (copied from the header of the skeleton).
- `ListHook.elemsOn_keysList` and `MapHook.entriesOn_update` are collection lemmas of `KPrelude.InvColl` (§6.4).
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

- `krs build` does not write the sidecar yet; write it by hand from the configuration declaration.
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
| 3 | collections | predicates on the keys, values or entries of maps, sets and lists: substitute the rule's equations, split conjunctions, add the facts read off the rule's matched collections (for `EntriesOn Q m` and a match `concat a b = some m`: `Q (k, v)` for an element, `EntriesOn Q x` for the rest), then close each conjunct by a hypothesis or by `apply` of a `@[k2l_coll]` lemma (update, remove, concat, element, unit, `values`, `keys_list`, …), normalizing a goal no lemma fits by the unfolding set and trying again |
| 4 | simp | `simp_all` with the unfolding set |

- Before closers 2–4, the hypotheses that were in context before the tactic and are not named in its lemma list are hidden, and a rule's sort projections `proj_A_B y = some x` are turned into `y = inj_B_A x` and substituted.
- A goal no closer closes is restored to its state after the case split, so the residual goal is exactly the rule's case.
- Each rule gets a fresh heartbeat budget, so `maxHeartbeats` bounds the work on one rule.

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
Lemmas of your own can join the closers through the two attributes the tactic reads (`lean/prelude/KPrelude/InvAttr.lean`): `@[k2l_pres]` adds a simp lemma to every unfolding set, and `@[k2l_coll]` adds a lemma that closer 3 tries by `apply`, in a module the cases import.
No demo tags a lemma of its own; the tested routes are naming a simp lemma in `[…]` and proving the case by hand.

### 5.3 Cost (measured 2026-10-23, Lean v4.30.0, shared 32-CPU host)

| invariant | kind | rules | automatic | hand | elaboration of the case module |
|---|---|---|---|---|---|
| kimp, `envKeysOk@env` (§3) | 1 | 79 | 78 | 1 | 1.1–1.6 s (load 25) |
| kimp, `Invariant D` (§4) | 2 | 79 | 78 | 1 | 1.1–1.4 s (load 25) |
| kimp, `envOk@env`: every store value is a `Value` (`demos/k/kimp-inv`) | 1 | 79 | 79 | 0 | 1.0–1.1 s, 1.6 GB |
| KRS IMP, sidecar `Map<Id, Value>` (`demos/k/krs-imp`) | 1 | 82 | 82 | 0 | 0.7–0.9 s, 1.5 GB |
| kimp, ImpTypes runtime typing `WTc G` (`demos/ImpTypes`) | 2 | 79 | 77 | 2 | 6.0–8.8 s, 1.7 GB |
| SIMPLE, `holdsOk@holds`, lock counts ≥ 0 (`demos/k/simple-inv`) | 1 | 169 | 167 | 2 | 2.5–2.7 s, 1.9 GB |
| SIMPLE, environments map into the store (`demos/SimpleEnv`) | 2 | 169 | 164 | 5 | 26–27 s, 3.5 GB |

- Times are `lake env lean FILE`, two runs each; the module's imports alone take 0.6–1.0 s of it.
- `Preserves.lean` itself takes 0.5 s on kimp and 1.2 s on SIMPLE.
- A new library is a full build: kimp-based up to `Invariants`, 46 s wall at load 31; SIMPLE-based, 242 s wall and 3.4 GB at load 1–3.

## 6. Proving a residual case

A residual case is `Step.Case.r P` with the rule's variables and side conditions in context.
The proofs below are in the tree; each shows one kind of reasoning the closers do not do.

### 6.1 Store typing: `CALC.var`, `CALC.assign` (`demos/ImpTypes/ImpTypes/Cases.lean`)

The invariant `WTc G` says the `<k>` computation is well typed under `G` and the store holds a value of `G`'s type at every typed identifier.
`CALC.var` reads the store, so its case needs the store's typing at `X`: the proof rewrites the matched lookup by `MapHook.lookup_of_concat_element hm`, takes the stored value's type from the hypothesis, and cases on the value.

```lean
theorem «CALC.var» (G : TEnv) : KImp.Step.Case.«CALC.var» (WTc G) := by
  intro X K g m v D hm
  rintro ⟨hk, he⟩
  simp only [WTc, kOf, envOf, envTyC] at hk he ⊢
  refine ⟨?_, he⟩
  simp only [kty_kseq, item_none, item0_id] at hk ⊢
  cases ht : tyOf G (.inj_Id X) with
  | none => simp [ht] at hk
  | some t =>
    simp only [ht, Option.map_some] at hk
    obtain ⟨v', hl, hv⟩ := he.2 X t ht
    rw [MapHook.lookup_of_concat_element hm] at hl
    obtain rfl := Option.some.inj hl
    cases v <;> simp_all [valTy, item_none, item0_int, item0_bool]
```

`CALC.assign` writes the store: the proof splits on whether a typed identifier `x` is `X` (`SAL.lookup_insert_self`) or another key (a lookup under `insert` at another key: the prelude has no lemma for it yet, so copy `SAL_lookup_insert_ne` from `demos/ImpTypes/ImpTypes/Invariant.lean`), the same split as `boundIn_update` in §4.4.

### 6.2 Arithmetic: SIMPLE's `acquire` and `release` (`generated/simpleinv/KSimpleInv/InvariantsHand.lean`)

The kind 1 invariant `holdsOk@holds` says every lock count is an `Int` at least 0.
Re-acquiring increments a count and releasing decrements it under `N >Int 0`; the closers reduce each case to `0 ≤ N + 1` from `0 ≤ N`, or `0 ≤ N - 1` from `0 < N`, and stop there.
The hand proofs take the collection steps by hand (`MapHook.entry_of_concat_element` on the matched thread and lock, `MapHook.entriesOn_concat` on the rebuilt ones), then restate the goal at `Int` and call `omega`:

```lean
  have hN := MapHook.entry_of_concat_element hm_6 ht
  simp only [Invariant.isCount_int, IntHook.add] at hN ⊢
  -- `SortInt` is `Int`; `omega` reads `Int` syntactically
  have hN' : (0 : Int) ≤ (N : Int) := hN
  show (0 : Int) ≤ (N : Int) + 1
  omega
```

`SortInt` is an abbreviation of `Int`, and `omega` does not see through it; the `have … : (0 : Int) ≤ …` and `show` lines are what make it apply.

### 6.3 Monotonicity: SIMPLE's store-growing rules (`demos/SimpleEnv/SimpleEnv/Cases.lean`)

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

### 6.4 Useful lemmas

| lemma (namespace `KPrelude`) | says |
|---|---|
| `MapHook.update_def`, `MapHook.lookup_def` | `update` and `lookup` through the sorted association list `SAL` |
| `SAL.mem_insert`, `SAL.mem_insert_self`, `SAL.mem_insert_of_mem_ne`, `SAL.lookup_insert_self` | membership and lookup after an insert |
| `MapHook.mem_toList_of_concat` | a binding of a defined `concat a b` is a binding of `a` or of `b`, and conversely |
| `MapHook.entry_of_concat_element`, `MapHook.entriesOn_of_concat_right` | the matched binding of `K |-> V REST`, and the rest |
| `MapHook.entriesOn_update`, `_concat`, `_element`, `_unit`, `_remove` | `EntriesOn Q` kept by each map operation |
| `MapHook.lookup_of_concat_element` | the lookup of the matched key |
| `SAL_lookup_insert_ne` (not in the prelude: `demos/ImpTypes/ImpTypes/Invariant.lean`) | a lookup after an insert at another key is unchanged |
| `ListHook.elemsOn_keysList`, `ListHook.elemsOn_values`, `ListHook.elemsOn_values_iff` | list predicates over `keys_list(M)` and `values(M)` |

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
Exit status: 0 when nothing differs, 1 when something does, 2 on an error.
It compares rule statements only, not the equations of the functions a rule calls (§9).

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

`CALC.var` changed too, but nothing refers to it, so it is not listed; 77 rules moved and are unchanged.
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
| a function's equations changed | the rule statements may be equal, so `diff` reports nothing, but the case's meaning changed: rebuild and read the results |
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

It implies the plain statement (its first conjunct), and it is inductive: 164 of 169 rules close automatically and the 5 store rules by hand (§6.3).
How to find the strengthening: read the open goal of the failing rule, find where the value the rule installs comes from (here, a `setEnv` item or a stack frame), and add the property of that source to `P`.
`Preserved.and_under` (`lean/prelude/KPrelude/Invariant.lean`) proves a conjunction in stages: `Preserved S P` and `PreservedUnder S P Q` (`Q` kept by the steps from configurations satisfying `P`) give `Preserved S (P ∧ Q)`.

## 9. Limitations

| limitation | consequence | workaround |
|---|---|---|
| inductive invariants only | a non-inductive property fails at a rule | strengthen it (§8) |
| nothing about undefined steps | a rule with an undefined result has no `Step` | state undefinedness through `App` and the adequacy theorems |
| configuration variables are arbitrary at `init` | `init_holds` needs hypotheses on `pgm`, `env` | state them; they are what a caller must establish |
| no linear-arithmetic closer | a case that needs `0 ≤ N + 1` from `0 ≤ N` stays open (SIMPLE's `acquire`, `release`) | a hand case: restate at `Int` with `have`/`show`, then `omega` (§6.2) |
| no free-key map patterns in invariant functions | `gen` panics: ``functions: f(…) equation …: a map pattern with a free key in a function equation (several matches)`` | fold over `values(M)` or `keys_list(M)` (§3.1), or write the invariant in Lean |
| owise equations are not in the unfolding set | only a function's non-`owise` equations are unfolded, so a test such as `notBool isId(X)` that needs `isId`'s `owise` equation leaves the update rule open | add the `owise` equation from `NS/Equations.lean` (for example `Eqn.isId_2`) to the hand proof, discharging its side condition by `cases` |
| injections are defined by cases | a predicate that walks `<k>` is stuck on `inj_Expr_KItem HOLE` or `inj_Value_KItem V` in the heating rules and `&&`/`||` (measured on one such predicate: 49 of 79 rules automatic without the lemmas) | prove one lemma per injection, `f (inj_Expr_KItem e) = …` by `cases e <;> rfl`, and pass them to `k2l_preserve` |
| list folds of one shape only | a recursive function other than `φ(X) andBool f(L)` with one argument gets a note (`… is not a list fold; its cases may need hand proofs`), and its cases usually become hand cases | rewrite it as such a fold, or write the invariant in Lean |
| `keys_list` has no rewrite into map bindings | with a `keys_list` fold, every rule that updates the map is a hand case (measured: `CALC.assign`, §3.4) | the hand proof of §3.4; a `values` fold has the rewrite (`ListHook.elemsOn_values_iff`) |
| no top-cell K function | through krust, a function over `GeneratedTopCell` does not parse on SIMPLE; on kimp it compiles, but a function that is `true` on every configuration closed 2 of 79 cases and left `init` open (measured), because its equation needs every cell to be a constructor and the rules' cells are variables | the cell form `@CELL` (SIMPLE: `@T`, a function over `<T>`), or a kind 2 predicate with one projection per level |
| cell collections: one level | a cell inside two nested collections is refused | state the invariant over the enclosing cell, or in Lean |
| `diff` does not compare functions | a change to a function's equations is not reported, though it changes what the cases mean | rebuild after every regeneration; compare `NS/Functions.lean` of the two generations with `diff -u` |
| Lake does not build the dependents of a module with an error | a broken hand case leaves `Run.lean` (kind 2) or `Invariants.lean` (kind 1) unchecked | keep hand cases in `Cases.lean` with `preserved`, as the skeleton does; fix the hand case first |
| heartbeats | when the hand mode leaves goals open, elaboration after the tactic counts every rule's heartbeats and can add a timeout error at `preserved` (measured on SIMPLE) | `set_option maxHeartbeats 0` in `Cases.lean` (ImpTypes has it); successful proofs are not affected |
| introductions are positional | an added or removed side condition shifts the names a hand case introduces | fix the `intro` line (§7.3) |
| digest names | a rule named with a digest is renamed by any change to it or to the configuration declaration | label the rule |
| the KRS sidecar is written by hand | `krs build` does not emit it | write it from the configuration declaration (§3.5) |

## 10. Checking with the gate

`$K/tests/gate.sh light|heavy` regenerates every library and demo of `k2lean/` from the K sources, builds them in a work tree of its own, and compares what it measures with `$K/tests/baseline.toml`: open sets may only shrink, `k2l_preserve` counts may not drop, axiom guards may not lose theorems, no `sorry`, and regenerated sources must equal the last accepted generation.
`docs/testing.md` of the repository says when it is owed and how it runs in CI (`k2lean-light`, `k2lean-heavy`).
To have it ratchet a new invariant, register it in three scripts, put its inputs in the tree, run a tier, and accept.

1. The inputs, in the k2lean directory `T` the gate checks (`T=$K` for real; git tracks exactly these files):

   ```text
   T/demos/k/kimp-keys/imp-keys.k                    the K module of §3.1
   T/generated/kimpkeys/open-obligations.txt         the library's open lists and hand module: the rest of
   T/generated/kimpkeys/open-invariant-cases.txt     generated/ is regenerated by every run, and git ignores it
   T/generated/kimpkeys/KImpKeys/InvariantsHand.lean
   T/demos/EnvBound/EnvBound/{Invariant,Cases,Run}.lean   the three modules of §4
   T/demos/EnvBound/{lakefile.lean,lean-toolchain}
   ```

   A kind 2 project under `demos/` must require `../../lean/prelude` and `../../generated/kimp`; copy the three modules first and then run `$G new-invariant --lib $T/generated/kimp --out $T/demos/EnvBound` with a generated kimp in `$T/generated/kimp` (from `demos/regen.sh`), which writes the lakefile with those paths and keeps the modules.
2. The registrations: `tests/libs.sh` (how to compile and generate), `tests/gate.sh` (the phases), `tests/gate-check.py` (what is measured):

   ```diff
   --- a/k2lean/tests/libs.sh
   +++ b/k2lean/tests/libs.sh
   @@ libs_kcompile
        kimp-inv) f=$DEMOS/k/kimp-inv/imp-inv.k m=IMP-INV s=IMP-SYNTAX inc=$KIMP ;;
   +    kimp-keys) f=$DEMOS/k/kimp-keys/imp-keys.k m=IMP-KEYS s=IMP-SYNTAX inc=$KIMP ;;
   @@ libs_name
   -    kimp) echo KImp ;; kimpinv) echo KImpInv ;; krsimp) …
   +    kimp) echo KImp ;; kimpinv) echo KImpInv ;; kimpkeys) echo KImpKeys ;; krsimp) …
   @@ libs_gen
   +    kimpkeys) "$G" gen --kore "$(kore_dir kimp-keys)/definition.kore" --runtime "$(kore_dir kimp-keys)/runtime.json" \
   +            --out "$o" --name KImpKeys --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt" \
   +            --invariant envKeysOk@env ;;
        krsimp) "$G" gen --kore "$KRS/definition.kore" …
   --- a/k2lean/tests/gate.sh
   +++ b/k2lean/tests/gate.sh
    kc kimp-inv
   +kc kimp-keys
   …
   +phase "lib kimpkeys"
   +if [ -f "$KO/kimp-keys/definition.kore" ]; then
   +  mkdir -p "$GEN/kimpkeys"; touch "$GEN/kimpkeys/open-obligations.txt"
   +  inv_reset kimpkeys
   +  if genlib kimpkeys; then
   +    eqns kimpkeys KImpKeys && invcases kimpkeys KImpKeys
   +  else bad "gen kimpkeys" "$L/gen-kimpkeys.log"; fi
   +fi
    phase "negative"
   …
   -diffs kimp krsimp kmut imptypes kimpinv
   +diffs kimp krsimp kmut imptypes kimpinv kimpkeys
   …
   -for p in ImpRel ImpTypes ImpMut KrsImpTyping; do
   +for p in ImpRel ImpTypes ImpMut KrsImpTyping EnvBound; do
   --- a/k2lean/tests/gate-check.py
   +++ b/k2lean/tests/gate-check.py
   -LIBS = {… "simpleinv": ("KSimpleInv", "heavy")}
   +LIBS = {… "simpleinv": ("KSimpleInv", "heavy"), "kimpkeys": ("KImpKeys", "light")}
   -NO_GUARD = {"kimpinv", "simpleinv"}
   +NO_GUARD = {"kimpinv", "simpleinv", "kimpkeys"}
   -INVS = {… "simpleinv": ("KSimpleInv", "heavy")}
   +INVS = {… "simpleinv": ("KSimpleInv", "heavy"), "kimpkeys": ("KImpKeys", "light")}
   -DEMOS = {… "Kind2Template": "light", "SimpleEnv": "heavy"}
   +DEMOS = {… "Kind2Template": "light", "SimpleEnv": "heavy", "EnvBound": "light"}
   -SOURCE_DIRS = {"light": [… "generated/kimpinv"],
   +SOURCE_DIRS = {"light": [… "generated/kimpinv", "generated/kimpkeys"],
   ```

   - `NO_GUARD`: the library is built only as far as its invariant needs, so it has no `…Test.Axioms` guard; the invariant's own `#k2l_assert_axioms` is checked through `INVS`.
   - A heavy invariant (SIMPLE-based) goes in the `heavy` branch of `gate.sh` and gets `"heavy"` in `gate-check.py`.
3. Run a tier, read its `FAIL` and `NOTE` lines, accept, and run again:

   ```text
   $T/tests/gate.sh light
   $T/tests/gate.sh accept
   $T/tests/gate.sh light
   ```

   The first run passes with `NOTE` lines for what the baseline does not have yet:

   ```text
   gate: NOTE lib.kimpkeys: not in the baseline
   gate: NOTE demo.EnvBound: not in the baseline
   gate: NOTE inv.kimpkeys: not in the baseline
   gate: NOTE sources: 17 new generated files: generated/kimpkeys/KImpKeys.lean, …
   gate: light passed
   ```

   `accept` (which refuses a run with failed steps, banned items or failing unit tests) writes the new entries to `T/tests/baseline.toml`: for kimpkeys, 79 cases, 78 automatic, open `[«CALC.assign»]`, 4 guarded; for EnvBound, 78 of 79 closed with hand `[«CALC.assign»]`, 5 guarded.
   The second run passes with no `NOTE`.
   From then on the gate fails if a hand case breaks (`FAIL step build EnvBound`, `FAIL demo.EnvBound: not built`), an open set grows, or a `k2l_preserve` count drops.
   The hand module `generated/kimpkeys/KImpKeys/InvariantsHand.lean` is among the hashed sources, so an edit to it is a `FAIL sources` until accepted.

To rehearse without touching your checkout, make a worktree of it (`git worktree add`), edit there, and run the worktree's gate with `GATE_KRUST_REPO=$R` (the checkout with krust and the K and kimp sources) and your own `GATE_WORK` and `GATE_CACHE`; `GATE_SEED=DIR` copies the `.lake/` directories of an existing work tree first, which makes the run incremental (`tests/gate.sh` with no argument prints every variable).

## 11. Further reading

| demo | kind | what it shows |
|---|---|---|
| `demos/k/kimp-inv/imp-inv.k` (library `kimpinv`, light gate) | 1 | a `values` fold, 79 of 79 automatic, `init_holds` from a hypothesis |
| `demos/k/simple-inv/simple-inv.k`, `generated/simpleinv/KSimpleInv/InvariantsHand.lean` (library `simpleinv`, heavy gate) | 1 | the cell-map lift over SIMPLE's threads, two arithmetic hand cases |
| `demos/k/krs-imp/k2lean-sidecar.json`, `demos/KrsImpTyping/` | 1 | the KRS sidecar, proved equivalent to a hand-written typing predicate |
| `demos/ImpTypes/ImpTypes/{Invariant,Cases,Run}.lean` | 2 | a parametrized runtime typing with `split [tyOf, wtS]`, two store hand cases |
| `demos/SimpleEnv/` | 2 | a relational, strengthened invariant over SIMPLE, five monotonicity hand cases |
| `lean/prelude/KPrelude/InvTactic.lean` | — | the tactic's documentation |
| `lean/prelude/KPrelude/Invariant.lean`, `InvSteps.lean` | — | `Preserved`, `PreservedUnder`, `Star`, `StepsN`, the typed view `TConfig` and `OnCell` |
