/-
  Three conjuncts of `faithCoreOK` (rows faithCoreOK.1-3 of test/witnesses.toml) for which no
  witness was found in the no-model form (a semantics meeting every other leaf condition of
  `coreOK` and `FnHyp`, failing the conjunct, whose `Γ` has no model).
  Run from the package root: `lake env lean -j1 test/WitRestFaithA.lean`.

  Kernel-checked here, for each conjunct: a semantics meeting every other leaf condition of `coreOK`
  (`sortedOK`, the other eleven conjuncts of `faithCoreOK`, `predsApart`, `idsOK`,
  `overloadsOK`) and `FnHyp`, with the conjunct false. So none of the three is implied by the others.
  - `namesNumbered`: `CtorIte.c` has a constructor named `Lblite{KCell}` (its first part fails).
    `FnIte.c` has a function so named, without clauses, that no symbol overloads: `namesNumbered`
    holds of it (`FnIte.namesNumbered_holds`), a function's equations and applications being written
    at one head. Its second part (no symbol that an overloading symbol overloads is so named) has no
    semantics here that fails it alone. Its third part (the sorts of every function are numbered) is
    implied by `sortsNumbered`, which says it of every symbol of `kernelSyms`, the functions among
    them (`fnSorts_of_sortsNumbered`, every semantics).
  - `genWf`: `CtorInt.c` has a constructor `k : → Int` (Int is no constructor sort: genWf's first
    part fails). `LibInt.c` has a library constructor `#KConfigValue : → Int` (Int a library sort
    with a generator, so a constructor sort, `int_cons`: genWf's third part fails), and `Γ` holds a
    no-junk item for Int (`nojunk_int`).
  - `collSortsOK`: `CollInt.c` has a list collection of the sort Int, its unit, element and
    concatenation parameters implemented by the library list's.

  `Γ` of `LibInt.c` has no model: kernel-checked in KcoreSpec/ModelLibIntWitness.lean (the same
  semantics), the witness module of the row faithCoreOK.2.

  Argued, not kernel-checked: `Γ` of each other semantics has a model.
  - `CtorIte.c`: as for `overloadsOK`'s conjunct on overloading symbols
    (test/OvlIteName.lean, whose `pattern_head`, `value_head` and `heads_differ` hold of every
    symbol named like `ite` at a sort): a value and the constructor items write the symbol under its
    own name `Lblite{KCell}`, a pattern or right-hand side (`Term.kore`) as the head `Lblite`
    applied to `SortKCell`; reading both heads as the symbol, as the canonical model's `resolve` reads
    the second once `itesApart` holds, meets each item as for a plainly named symbol, and nothing
    else in `Γ` names `Lblite` at `SortKCell` (`itesApart` leaves no other symbol there; the
    registry's `Lblite` is applied to a Bool's element first). Where a rule's right-hand side
    applies the constructor, `Γ` equates the two heads nowhere, so the conjunct is asked for
    soundness, as test/OvlIteSoundC.lean kernel-checks for the overloading symbol, not for a model.
  - `CtorInt.c`: `Γ` reads Int as a sort of domain values: distinct literals are distinct elements,
    and the hooks' graphs speak of literals. `consItemsK` states its items per constructor sort
    (`consSorts`), which Int is not, so `k` has no function, injectivity, distinctness or no-junk
    item: of `k()` `Γ` states its arity (`sigItems`: it lies in Int), and nothing else names `k`. A
    model is the value model of `CtorInt.c0` (`c` without `k` and its name, which `coreOK` accepts:
    `c0_core`) with `k()` read as nothing, or as any element of Int.
    `genWf` is asked for the constructor items to describe a constructor sort's values, which
    `HypModelCore` reads.
  - `CollInt.c`: Int's carrier extended by the lists of KItem: the list axioms (`listCollAxioms`)
    quantify over every element of Int, and are met with the concatenation and element read as on
    the lists and as nothing at a literal (their premises are definedness conditions), the
    literals staying distinct and apart from the lists.

  Not examined: the other ways each conjunct can fail alone: among `genWf`'s, a subsort into a
  collection sort and a raw parameter of a sort that is no constructor sort (a reflexive subsort is
  `subsortsOK`'s as well; `apartSort` of a constructor sort looks vacuous, every constructor sort
  being K, KItem or a sort below KItem: argued); among `collSortsOK`'s, a collection of a sort
  hooked to a library carrier.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.Faithful.WitRestFaithA

open ML Faithful.Model
open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

/-- Every function's sorts are numbered where every symbol's are (`sortsNumbered`). -/
theorem fnSorts_of_sortsNumbered (c : Semantics) (h : sortsNumbered c = true) :
    (c.allFns.all fun fn => (fn.result :: fn.args).all fun s => decide (s < nRegSorts + c.sortNames.length)) = true := by
  unfold sortsNumbered at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, -⟩, -⟩, -⟩ := h
  rw [List.all_eq_true] at h1 ⊢
  intro fn hfn
  exact h1 fn.sig (by simp only [kernelSyms, List.mem_append, List.mem_map]; exact .inl (.inl (.inl (.inr ⟨fn, hfn, rfl⟩))))

/-- The cells of `FnSolvesWitness.c` and one more symbol, numbered `nRegSyms + 4`, named `name`. -/
def base (name : String) : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", name]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

def g : Sym := nRegSyms + 4

/-- A semantics without functions meets `FnHyp` once it reads no confined sort and has no raw parameter. -/
theorem fnHyp_of_nil {c : Semantics} (hf : c.fns = []) (hp : ∀ k ∈ c.params, k.raw = false)
    (hr : c.readsConfined = false) : FnHyp c :=
  ⟨fun _ h => absurd (hf ▸ h) List.not_mem_nil, fun _ h => absurd (hf ▸ h) List.not_mem_nil,
    fun _ h => absurd (hf ▸ h) List.not_mem_nil, fun _ h => absurd (hf ▸ h) List.not_mem_nil,
    openDecided_of_readsConfined hr, openLaws_of_plain hp⟩

/-- Every leaf condition of `coreOK` outside `faithCoreOK`. -/
def outside (c : Semantics) : Prop :=
  c.sortedOK = true ∧ c.predsApart = true ∧ c.idsOK = true ∧ c.overloadsOK = true

/-! ## `namesNumbered`: a constructor named like `ite` at a sort -/

namespace CtorIte

/-- The constant `Lblite{KCell} : → KCell`. -/
def c : Semantics := { base "Lblite{KCell}" with ctors := cellCtors ++ [⟨g, [], nRegSorts⟩] }

theorem fnHyp : FnHyp c := fnHyp_of_nil rfl (fun _ h => absurd h List.not_mem_nil) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem meets_others : outside c ∧
    genWf c = true ∧ collSortsOK c = true ∧ collsOK c = true ∧ patHeadsOK c = true ∧
    namesApartK c = true ∧ LitsApart c = true ∧ sortsNumbered c = true ∧ itesApart c = true ∧
    kindsApart c = true ∧ ctorsOnce c = true ∧ fnsApart c = true ∧ FnHyp c :=
  ⟨⟨by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap⟩,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, fnHyp⟩

theorem not_namesNumbered : namesNumbered c = false := by decide +kernel
theorem ite_named : instDecode? (c.symName g) = some ("Lblite", ["KCell"]) := by decide +kernel

end CtorIte

/-! ## `namesNumbered` holds of a function named like `ite` at a sort that no symbol overloads -/

namespace FnIte

/-- `Lblite{KCell} : → KCell`, without clauses. -/
def fn : Fn := ⟨g, [], nRegSorts, [], false⟩

def c : Semantics := { base "Lblite{KCell}" with fns := [fn] }

theorem fnHyp : FnHyp c := by
  refine ⟨fun f hf vs hvs => ?_, fun f hf ht => ?_, fun f hf => ?_, fun f hf cl hcl => ?_,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain fun _ h => absurd h List.not_mem_nil⟩
  · obtain rfl := List.mem_singleton.mp hf
    exact ⟨_, .rest (f := g) rfl fun cl hcl => absurd hcl List.not_mem_nil⟩
  · obtain rfl := List.mem_singleton.mp hf; cases ht
  · obtain rfl := List.mem_singleton.mp hf
    intro cl cl' h; exact absurd h List.not_mem_nil
  · obtain rfl := List.mem_singleton.mp hf; exact absurd hcl List.not_mem_nil

set_option maxHeartbeats 1000000 in
theorem meets_others : outside c ∧
    genWf c = true ∧ collSortsOK c = true ∧ collsOK c = true ∧ patHeadsOK c = true ∧
    namesApartK c = true ∧ LitsApart c = true ∧ sortsNumbered c = true ∧ itesApart c = true ∧
    kindsApart c = true ∧ ctorsOnce c = true ∧ fnsApart c = true ∧ FnHyp c :=
  ⟨⟨by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap⟩,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, fnHyp⟩

theorem namesNumbered_holds : namesNumbered c = true := by decide +kernel

end FnIte

/-! ## `genWf`: a constructor of the sort Int -/

namespace CtorInt

/-- The constant `k : → Int`. -/
def c : Semantics := { base "Lblk" with ctors := cellCtors ++ [⟨g, [], Srt.int⟩] }

theorem fnHyp : FnHyp c := fnHyp_of_nil rfl (fun _ h => absurd h List.not_mem_nil) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem meets_others : outside c ∧
    namesNumbered c = true ∧ collSortsOK c = true ∧ collsOK c = true ∧ patHeadsOK c = true ∧
    namesApartK c = true ∧ LitsApart c = true ∧ sortsNumbered c = true ∧ itesApart c = true ∧
    kindsApart c = true ∧ ctorsOnce c = true ∧ fnsApart c = true ∧ FnHyp c :=
  ⟨⟨by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap⟩,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, fnHyp⟩

theorem not_genWf : genWf c = false := by decide +kernel
theorem int_not_cons : (consSorts c).contains Srt.int = false := by decide +kernel

/-- `c` without `k` and its name. -/
def c0 : Semantics := { base "Lblk" with symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"] }

theorem c0_core : c0.coreOK = true := by decide_cheap

end CtorInt

/-! ## `genWf`: a library constructor of the sort Int -/

namespace LibInt

/-- The library's sorts below KItem are Int, with the constant `#KConfigValue : → Int`. -/
def c : Semantics :=
  { base "" with
    lib := { sortsBelowKItem := [Srt.int], ctors := [⟨kconfigValue, [], Srt.int⟩] }
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"] }

theorem fnHyp : FnHyp c := fnHyp_of_nil rfl (fun _ h => absurd h List.not_mem_nil) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem meets_others : outside c ∧
    namesNumbered c = true ∧ collSortsOK c = true ∧ collsOK c = true ∧ patHeadsOK c = true ∧
    namesApartK c = true ∧ LitsApart c = true ∧ sortsNumbered c = true ∧ itesApart c = true ∧
    kindsApart c = true ∧ ctorsOnce c = true ∧ fnsApart c = true ∧ FnHyp c :=
  ⟨⟨by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap⟩,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, fnHyp⟩

theorem not_genWf : genWf c = false := by decide +kernel
theorem int_cons : (consSorts c).contains Srt.int = true := by decide +kernel
theorem nojunk_int : (consItemsK c).any (·.label == "cons-nojunk SortInt") = true := by decide +kernel

end LibInt

/-! ## `collSortsOK`: a collection of the sort Int -/

namespace CollInt

def uS : Sym := nRegSyms + 4
def eS : Sym := nRegSyms + 5
def cS : Sym := nRegSyms + 6

/-- A list collection of the sort Int, of KItem, built by three parameters implemented by the
library list's unit, element and concatenation. -/
def c : Semantics :=
  { base "LblunitI" with
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "LblunitI", "LblelemI", "LblconcatI"]
    params := [{ sig := ⟨uS, [], Srt.int⟩, impl := some (builtinColl .list).unit },
      { sig := ⟨eS, [Srt.kitem], Srt.int⟩, impl := some (builtinColl .list).elem },
      { sig := ⟨cS, [Srt.int, Srt.int], Srt.int⟩, impl := some (builtinColl .list).concat }]
    colls := [⟨Srt.int, .list, Srt.kitem, none, uS, eS, cS⟩] }

theorem fnHyp : FnHyp c := fnHyp_of_nil rfl (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem meets_others : outside c ∧
    namesNumbered c = true ∧ genWf c = true ∧ collsOK c = true ∧ patHeadsOK c = true ∧
    namesApartK c = true ∧ LitsApart c = true ∧ sortsNumbered c = true ∧ itesApart c = true ∧
    kindsApart c = true ∧ ctorsOnce c = true ∧ fnsApart c = true ∧ FnHyp c :=
  ⟨⟨by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap⟩,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, fnHyp⟩

theorem not_collSortsOK : collSortsOK c = false := by decide +kernel

end CollInt

/-- info: 'KCore.Faithful.WitRestFaithA.CtorIte.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CtorIte.meets_others

/-- info: 'KCore.Faithful.WitRestFaithA.FnIte.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FnIte.meets_others

/-- info: 'KCore.Faithful.WitRestFaithA.CtorInt.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CtorInt.meets_others

/-- info: 'KCore.Faithful.WitRestFaithA.LibInt.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LibInt.meets_others

/-- info: 'KCore.Faithful.WitRestFaithA.CollInt.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CollInt.meets_others

/-- info: 'KCore.Faithful.WitRestFaithA.fnSorts_of_sortsNumbered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fnSorts_of_sortsNumbered

end KCore.Faithful.WitRestFaithA
