/-
  KCore. A semantics that meets every condition of `coreOK` but the agreement of two overloads in `overloadsOK`
  (any two overloads of one symbol agree, `ovlCoherent`), and `FnHyp`, whose `Γ` has no model
  because two overloads of one symbol meet at a value no overload covers: so `SoundC` fails of it
  (`not_sound`), and that part cannot be left out of `coreOK`.

  The constructors `g, h : Int → KCell` and the overloading symbol `f : Int → KCell` overloading
  both. At every position some sort lies below both argument sorts (Int), and no symbol among
  `g` and those it overloads is among `h` and those it overloads, so `ovlCoherent g h` is false.
  `consItemsK` states the overload equations `f(x) = g(x)` and `f(x) = h(x)` for Int x
  (`ovlEq_at`, the sorts being equal) and, `g` and `h` being constructors, Cons-Dist for the pair
  with no guard: `g(x) ≠ h(y)`. At x = y = the element of `0`, `g(x) = f(x) = h(x)`. With `f`
  overloading `g` alone, `coreOK` holds (`c0_coreOK`). The decidable facts are kernel decisions.
-/
import KcoreSpec.CoreDecide
import KcoreSpec.Sound
import KcoreSpec.ModelOvlLibCtorWitness

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace Faithful

namespace OvlIncohWitness

open ML
open Faithful.OvlTwiceWitness (cellSorts cellCtors cellSubsorts)
open Faithful.OvlLibCtorWitness (ov1 ov2 ov3 ov4 ov5 ov6 ov7 ov8 ov9)

/-- The `k` cell's sort. -/
def KCell : Srt := nRegSorts

def gSig : CtorSig := ⟨nRegSyms + 4, [Srt.int], KCell⟩
def hSig : CtorSig := ⟨nRegSyms + 5, [Srt.int], KCell⟩
def fSig : CtorSig := ⟨nRegSyms + 6, [Srt.int], KCell⟩
def o : OvlSig := ⟨fSig, [gSig.name, hSig.name]⟩

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblg", "Lblh", "Lblf"]
    userSorts := cellSorts
    ctors := cellCtors ++ [gSig, hSig]
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := []
    ovls := [o] }

/-- With `f` overloading `g` alone `coreOK` holds. -/
def c0 : Semantics := { c with ovls := [⟨fSig, [gSig.name]⟩] }

set_option maxHeartbeats 4000000 in
theorem c0_coreOK : c0.coreOK = true := by decide_coreOK

theorem sortedOK : c.sortedOK = true := by decide +kernel

/-- `c` has no function: `FnHyp` holds. -/
theorem fnHyp : FnHyp c :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩

set_option maxHeartbeats 1000000 in
/-- Every condition of `coreOK` but `overloadsOK`'s agreement of two overloads holds, and `FnHyp`. -/
theorem meets_others : c.sortedOK = true ∧ c.faithCoreOK = true ∧
    c.predsApart = true ∧ c.idsOK = true ∧ ov1 c = true ∧ ov2 c = true ∧ ov3 c = true ∧ ov4 c = true ∧
    ov5 c = true ∧ ov7 c = true ∧ FnHyp c :=
  ⟨sortedOK, by decide_faithCoreOK, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, fnHyp⟩

/-- It lists every function it reaches along the overloads: it reaches none. -/
theorem meets_ov9 : ov9 c = true := by decide +kernel

theorem not_ov8 : ov8 c = false := by decide +kernel
theorem not_overloadsOK : c.overloadsOK = false := by decide +kernel

theorem kcell_cons : KCell ∈ consSorts c := by decide +kernel
theorem gens_kcell : c.gens KCell = [Gen.ctor ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, .ctor gSig, .ctor hSig, .ctor fSig] := by
  unfold Semantics.gens; rfl

theorem gh_pair : (Gen.ctor gSig, Gen.ctor hSig) ∈ pairs (c.gens KCell) := by
  rw [gens_kcell]; exact List.mem_append_right _ (List.mem_append_left _ (List.mem_cons_self ..))
theorem gh_unguarded : c.distGuarded (.ctor gSig) (.ctor hSig) = false := by decide +kernel
theorem g_over : gSig ∈ c.ovlOver o := by decide +kernel
theorem h_over : hSig ∈ c.ovlOver o := by decide +kernel

/-- The overload equation at one Int argument, the sorts being equal. -/
theorem ovl_single {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {x : M} {s : String} :
    ∀ (i : Nat) (A B : String) (z y : M), [s][i]? = some A → [s][i]? = some B → [x][i]? = some z →
      [x][i]? = some y → ∀ m, (if A == B then m = z else GS I B (.inj A) [z] m) ↔ m = y
  | 0, A, B, z, y, hA, hB, hz, hy, m => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hA hB hz hy
    subst hA hB hz hy
    simp
  | _ + 1, _, _, _, _, _, _, hz, _, _ => by simp at hz

/-- **`Γ c` has no model.** -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M _ I hI
  have hD := defOK hI
  have hx : InS I (c.sortName Srt.int) (elemOf c I (int 0)) :=
    (inS_iff _).mp (elemOf_spec hI (sortOf_int 0) KoreAML.val0).2
  have ho : o ∈ c.ovls := List.mem_singleton_self _
  have eq_at : ∀ kg ∈ c.ovlOver o, ((toK c kg).result == (toK c o.sig).result) = true →
      (toK c kg).args = [c.sortName Srt.int] → ∀ m,
      (GS I (c.sortName KCell) (.ctor (toK c o.sig)) [elemOf c I (int 0)] m ↔
        GS I (c.sortName KCell) (.ctor (toK c kg)) [elemOf c I (int 0)] m) := by
    intro kg hkg hres hargs m
    have hax := sat_cons hI (Or.inl ⟨_, ovlEqItem_mem ho hkg, rfl⟩)
    have key := ovlEq_at hD (N := c.sortName KCell) (N' := c.sortName KCell) hax
      (zs := [elemOf c I (int 0)]) (ys := [elemOf c I (int 0)]) (by rw [hargs]; rfl) (by rw [hargs]; rfl)
      (by rw [hargs]; rfl) (by rw [hargs]; exact single_sorts hx) (by rw [hargs]; exact ovl_single) m
    rw [if_pos hres] at key
    exact key
  have hg := eq_at gSig g_over (beq_self_eq_true _) rfl
  have hh := eq_at hSig h_over (beq_self_eq_true _) rfl
  have hit := sat_cons hI (Or.inl ⟨_, distItem_mem kcell_cons gh_pair (fun _ _ h _ => by cases h) gh_unguarded, rfl⟩)
  exact dist_at hD hit (xs := [elemOf c I (int 0)]) (ys := [elemOf c I (int 0)]) rfl rfl
    (single_sorts hx) (single_sorts hx) (fun m => (hg m).symm.trans (hh m))

/-- **Soundness fails** of `c`, which meets every condition of `coreOK` but `overloadsOK`'s agreement of two overloads
part, and `FnHyp`. -/
theorem not_sound : ¬ SoundC c := fun h => by
  obtain ⟨⟨M, hM, I, hI⟩, -⟩ := h
  exact no_model M hM I (fun φ hφ => hI φ (Or.inl (Or.inl hφ)))

end OvlIncohWitness

end Faithful

end KCore
