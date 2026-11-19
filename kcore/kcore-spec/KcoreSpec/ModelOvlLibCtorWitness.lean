/-
  KCore. A semantics that meets every condition of `coreOK` but the first part of `overloadsOK`
  (an overloading symbol is of no other kind, `isOvl`), and `FnHyp`, whose `Γ` has no model because
  its overloading symbol is also a constructor of the library: so `SoundC` fails of it
  (`not_sound`), and that part cannot be left out of `coreOK`.

  The overloading symbol `f : Int → K`, numbered as the definition's own symbol after the cell's,
  overloads nothing; the library's constructors are `f : Int → K` as well. `idsOK` numbers the
  definition's constructors, functions, parameters and overloading symbols, not the library's
  constructors, so it holds; `ctorsOnce` reads the constructors only, and `f` is one. The
  generators of K then hold `f` twice, once as a constructor and once as an overloading symbol;
  `f` is not `isOvl`, so `distGuarded` does not name the pair and `consItemsK` states Cons-Dist for
  it with no guard: `f(x) ≠ f(y)` for Int x and y. At x = y = the element of `0` this is false. The
  decidable facts are kernel decisions.
-/
import KcoreSpec.CoreDecide
import KcoreSpec.Sound
import KcoreSpec.ModelOvlTwiceWitness

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace Faithful

namespace OvlLibCtorWitness

open ML
open Faithful.OvlTwiceWitness (cellSorts cellCtors cellSubsorts fSig)

def o : OvlSig := ⟨fSig, []⟩

def c : Semantics :=
  { lib := { ctors := [fSig] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := []
    ovls := [o] }

/-- Without the library's constructor `coreOK` holds. -/
def c0 : Semantics := { c with lib := {} }

set_option maxHeartbeats 4000000 in
theorem c0_coreOK : c0.coreOK = true := by decide_coreOK

/-- The leaves of `overloadsOK`, each over every overloading symbol (test/witnesses.toml's
overloadsOK.1 to overloadsOK.9). -/
def ov1 (c : Semantics) : Bool := c.ovls.all fun o => c.isOvl o.sig.name
def ov2 (c : Semantics) : Bool := c.ovls.all fun o => c.lookupOvl o.sig.name == some o
def ov3 (c : Semantics) : Bool := c.ovls.all fun o => (instDecode? (c.symName o.sig.name)).isNone
def ov4 (c : Semantics) : Bool := c.ovls.all fun o => (consSorts c).contains o.sig.result
def ov5 (c : Semantics) : Bool := c.ovls.zipIdx.all fun (o, i) =>
  o.over.all fun g => (lookupSig c.ctorSigs g).isSome || (c.ovls.take i).any (·.sig.name == g) ||
    c.fns.any (·.label == g)
def ov6 (c : Semantics) : Bool := c.ovls.all fun o => (c.ovlOver o).length == o.over.length
def ov7 (c : Semantics) : Bool := c.ovls.all fun o => (c.ovlOver o).all (c.ovlPairOK o)
def ov8 (c : Semantics) : Bool := c.ovls.all fun o => (c.ovlOver o).all fun k1 => (c.ovlOver o).all fun k2 =>
  c.ovlCoherent k1 k2
def ov9 (c : Semantics) : Bool := c.ovls.all fun o =>
  (c.ovlClosure o.sig.name).all fun g => !c.fns.any (·.label == g) || o.over.contains g

theorem sortedOK : c.sortedOK = true := by decide +kernel

/-- `c` has no function: `FnHyp` holds. -/
theorem fnHyp : FnHyp c :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩

set_option maxHeartbeats 1000000 in
/-- Every condition of `coreOK` but `overloadsOK`'s first part holds, and `FnHyp`. -/
theorem meets_others : c.sortedOK = true ∧ c.faithCoreOK = true ∧ c.hooksApart = true ∧
    c.predsApart = true ∧ c.idsOK = true ∧ ov2 c = true ∧ ov3 c = true ∧ ov4 c = true ∧ ov5 c = true ∧
    ov6 c = true ∧ ov7 c = true ∧ ov8 c = true ∧ FnHyp c :=
  ⟨sortedOK, by decide_faithCoreOK, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, fnHyp⟩

/-- It lists every function it reaches along the overloads: it reaches none. -/
theorem meets_ov9 : ov9 c = true := by decide +kernel

theorem not_ov1 : ov1 c = false := by decide +kernel
theorem not_overloadsOK : c.overloadsOK = false := by decide +kernel

theorem k_cons : Srt.k ∈ consSorts c := by decide +kernel

/-- f is a generator of K twice: as the library's constructor and as the overloading symbol. -/
theorem gens_k : c.gens Srt.k = (fixedCtors.filter (·.result == Srt.k)).map Gen.ctor ++ [Gen.ctor fSig, Gen.ctor fSig] := by
  unfold Semantics.gens; rfl

theorem f_pair : (Gen.ctor fSig, Gen.ctor fSig) ∈ pairs (c.gens Srt.k) := by
  rw [gens_k]; exact Faithful.OvlTwiceWitness.pairs_twice _ []

theorem f_unguarded : c.distGuarded (.ctor fSig) (.ctor fSig) = false := by decide +kernel

/-- **`Γ c` has no model.** -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M _ I hI
  have hit := sat_cons hI (Or.inl ⟨_, distItem_mem k_cons f_pair (fun _ _ h _ => by cases h) f_unguarded, rfl⟩)
  have hx : InS I (c.sortName Srt.int) (elemOf c I (int 0)) :=
    (inS_iff _).mp (elemOf_spec hI (sortOf_int 0) KoreAML.val0).2
  exact dist_at (defOK hI) hit (xs := [elemOf c I (int 0)]) (ys := [elemOf c I (int 0)]) rfl rfl
    (single_sorts hx) (single_sorts hx) (fun _ => Iff.rfl)

/-- **Soundness fails** of `c`, which meets every condition of `coreOK` but `overloadsOK`'s first
part, and `FnHyp`. -/
theorem not_sound : ¬ SoundC c := fun h => by
  obtain ⟨⟨M, hM, I, hI⟩, -⟩ := h
  exact no_model M hM I (fun φ hφ => hI φ (Or.inl (Or.inl hφ)))

end OvlLibCtorWitness

end Faithful

end KCore
