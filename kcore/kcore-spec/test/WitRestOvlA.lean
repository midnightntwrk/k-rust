/-
  The rows overloadsOK.1, overloadsOK.2 and overloadsOK.4 of test/witnesses.toml (an overloading
  symbol is of no other kind, is looked up as itself, has a constructor sort). Run from the package
  root: `lake env lean -j1 test/WitRestOvlA.lean`.

  overloadsOK.1 has a witness module, KcoreSpec/ModelOvlLibCtorWitness.lean (an overloading symbol
  that is also a constructor of the library: `Γ` has no model). Its leaves `ov1` to `ov9` are used
  here. Its semantics meets overloadsOK.10 as well (`libCtor_ovlPatsOK`), which the module does not
  list.

  Kernel-checked here:
  - overloadsOK.2: implied by idsOK.2, for every semantics (`ov2_of_ids2`): idsOK.2 numbers the
    overloading symbols once each (`ownSyms` lists their names, without repetition), so the first
    overloading symbol of an overloading symbol's name is that symbol (`find_self`).
  - overloadsOK.4, `Res.c`: the overloading symbol `f : Int → Int`, overloading nothing, meets every
    other leaf condition of `coreOK` (`sortedOK`, `faithCoreOK`, `hooksApart`, `predsApart`,
    `idsOK`, the other nine leaves of `overloadsOK`) and `FnHyp`, with overloadsOK.4 false;
    `Res.c0`, the same with `f : Int → K`, meets `coreOK`. `f(0)` is a value of Int (`Res.f_value`).

  Argued, not kernel-checked: `Γ` of `Res.c` has a model. Int is no constructor sort, so `f` is
  the generator of no sort and `consItemsK` states nothing of it (`Res.cons_f`: no item names it), and
  it overloads nothing, so no overload equation; `Γ` speaks of `f` through its arity item (its
  applications to Int lie in Int) and through `ΓDomains`, which makes each value `f(n)` one element of
  Int, apart from every other value of Int, and gives the graphs of the interpreted hooks at the
  values `f(n)`, the interpretation's values or ⊥. Nothing states that Int holds its literals only
  (no no-junk item for Int), so the value model, Int holding the literals and the values `f(n)`,
  meets these. Not examined: the fallback graphs (`ΓFallback`) at the values `f(n)` one by one.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.Faithful.WitRestOvlA

open ML Faithful.Model
open Faithful.OvlLibCtorWitness (ov1 ov2 ov3 ov4 ov5 ov6 ov7 ov8 ov9)
open Faithful.OvlTwiceWitness (cellSorts cellCtors cellSubsorts fSig)

/-- idsOK.2, as test/witnesses.toml lists it. -/
def ids2 (c : Semantics) : Bool := c.ownSyms == List.range' c.symBase (c.symNames.length - c.sortNames.length)

/-! ## overloadsOK.2: implied by idsOK.2 -/

/-- In a list of overloading symbols named apart, the first of a member's name is the member. -/
theorem find_self : ∀ (l : List OvlSig) (o : OvlSig), (l.map (·.sig.name)).Nodup → o ∈ l →
    l.find? (·.sig.name == o.sig.name) = some o
  | [], _, _, h => absurd h List.not_mem_nil
  | a :: l, o, hn, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have hne : a.sig.name ≠ o.sig.name := fun he => hn.1 (he ▸ List.mem_map_of_mem h)
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact find_self l o hn.2 h

/-- **overloadsOK.2 is implied by idsOK.2**, for every semantics. -/
theorem ov2_of_ids2 (c : Semantics) (h : ids2 c = true) : ov2 c = true := by
  have hnd : c.ownSyms.Nodup := by
    unfold ids2 at h
    rw [beq_iff_eq.mp h]
    exact List.nodup_range' ..
  unfold Semantics.ownSyms at hnd
  have hov := (List.nodup_append.mp hnd).2.1
  unfold ov2
  rw [List.all_eq_true]
  intro o ho
  simp only [Semantics.lookupOvl, beq_iff_eq]
  exact find_self _ _ hov ho

/-! ## overloadsOK.4: an overloading symbol of a sort of domain values -/

namespace Res

def c0 : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := []
    ovls := [⟨fSig, []⟩] }

def fInt : CtorSig := ⟨nRegSyms + 4, [Srt.int], Srt.int⟩
def c : Semantics := { c0 with ovls := [⟨fInt, []⟩] }

theorem c0_coreOK : c0.coreOK = true := by decide_cheap

theorem sortedOK : c.sortedOK = true := by decide_cheap

theorem fnHyp : FnHyp c :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩

set_option maxHeartbeats 1000000 in
theorem meets_others : c.sortedOK = true ∧ c.faithCoreOK = true ∧ c.hooksApart = true ∧
    c.predsApart = true ∧ c.idsOK = true ∧ ov1 c = true ∧ ov2 c = true ∧ ov3 c = true ∧ ov5 c = true ∧
    ov6 c = true ∧ ov7 c = true ∧ ov8 c = true ∧ c.ovlPatsOK = true ∧ FnHyp c :=
  ⟨sortedOK, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, fnHyp⟩

/-- It lists every function it reaches along the overloads: it overloads nothing. -/
theorem meets_ov9 : ov9 c = true := by decide +kernel

theorem not_ov4 : ov4 c = false := by decide +kernel

theorem f_value : c.sortOf (.ctor fInt.name [int 0]) = some Srt.int := by decide +kernel

/-- No constructor item of `c` is about `f`: the overloading symbols are generators of their result
sort only (`Semantics.gens`), f's is Int, and Int is no constructor sort. -/
theorem cons_f : (consSorts c).contains Srt.int = false ∧ c.ovlSigs.all (·.result == Srt.int) = true ∧
    c.ctorSigs.all (·.name != fInt.name) = true := by
  decide +kernel

end Res

/-- The witness module's semantics of overloadsOK.1 meets overloadsOK.10 as well: it has no
function, so no symbol is function-overloaded. -/
theorem libCtor_ovlPatsOK : Faithful.OvlLibCtorWitness.c.ovlPatsOK = true := by decide +kernel

/-- info: 'KCore.Faithful.WitRestOvlA.ov2_of_ids2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ov2_of_ids2

/-- info: 'KCore.Faithful.WitRestOvlA.Res.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Res.meets_others

end KCore.Faithful.WitRestOvlA
