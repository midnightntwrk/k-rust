/-
  KCore. A semantics that meets every condition of `coreOK` but `idsOK` and the empty list of
  overloading symbols, and `FnHyp`, whose `Γ` has no model because one overloading symbol is
  listed twice: so `SoundC` fails of it (`not_sound`), and without the empty list `coreOK` needs
  `idsOK`'s numbering of the overloading symbols, which lists each once
  (`ovlsOnce_of_ids`).

  The overloading symbol `f : Int → K` overloads nothing and is listed twice in `ovls`; its
  declarations are well formed (`overloadsOK`). The generators of K then hold `f` twice, and
  `consItemsK` states Cons-Dist at uncovered arguments for the pair (f, f): `f(x) ≠ f(y)` for Int
  x and y, under no guard on the arguments since f has no overload. At x = y = the element of `0`
  this is false. `idsOK` refuses the semantics: `ownSyms` lists f twice. The decidable facts are
  kernel decisions.
-/
import KcoreSpec.Sound
import KcoreSpec.CoreDecide

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace Faithful

namespace OvlTwiceWitness

open ML

/-- The configuration `<k> K </k>` with the generated counter, as ordinary sorts, constructors
and subsorts: the top cell's, its fragment's, the `k` cell's and the counter's. -/
def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

/-- The overloading symbol `f : Int → K`, numbered after the cell's symbols, overloading nothing. -/
def fSig : CtorSig := ⟨nRegSyms + 4, [Srt.int], Srt.k⟩
def o : OvlSig := ⟨fSig, []⟩

def c : Semantics :=
  { lib := { ctors := [⟨kconfigValue, [Srt.k], Srt.kitem⟩] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := []
    ovls := [o, o] }

theorem sortedOK : c.sortedOK = true := by decide +kernel

/-- `c` has no function: `FnHyp` holds. -/
theorem fnHyp : FnHyp c :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩

set_option maxHeartbeats 1000000 in
/-- Every condition of `coreOK` but `idsOK` and the empty list of overloading symbols holds, and
`FnHyp`. -/
theorem meets_others : c.sortedOK = true ∧ c.faithCoreOK = true ∧ c.hooksApart = true ∧
    c.predsApart = true ∧ c.overloadsOK = true ∧ FnHyp c :=
  ⟨sortedOK, by decide_faithCoreOK, by decide +kernel, by decide +kernel, by decide +kernel, fnHyp⟩

/-- `idsOK` refuses `c`: its own symbols list f twice. -/
theorem not_idsOK : c.idsOK = false := by decide +kernel

theorem k_cons : Srt.k ∈ consSorts c := by decide +kernel
theorem pairs_twice {α : Type} {x : α} : ∀ (l1 l2 : List α), (x, x) ∈ pairs (l1 ++ x :: x :: l2)
  | [], l2 => List.mem_append_left _ (List.mem_cons_self ..)
  | a :: l1, l2 => List.mem_append_right _ (pairs_twice l1 l2)

/-- f is a generator of K twice. -/
theorem f_pair : (Gen.ctor fSig, Gen.ctor fSig) ∈ pairs (c.gens Srt.k) := by
  have : c.gens Srt.k = (c.ctorSigs.filter (·.result == Srt.k)).map .ctor ++ (Gen.ctor fSig :: Gen.ctor fSig ::
      (sortBy id ((c.subsorts.filter (·.2 == Srt.k)).map (·.1))).map .inj) := by
    unfold Semantics.gens; rw [List.append_assoc, List.append_assoc]; rfl
  rw [this]; exact pairs_twice _ _
theorem f_guarded : c.distGuarded (.ctor fSig) (.ctor fSig) = true := by decide +kernel
theorem f_args : ovlArgsOf c (.ctor fSig) = some [] := by decide +kernel

/-- **`Γ c` has no model.** -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M _ I hI
  have hF : (c.gens Srt.k).filter (!c.isOpenGen ·) = c.gens Srt.k := List.filter_eq_self.mpr fun g _ => by
    cases g with
    | ctor k => simp [Semantics.isOpenGen, Semantics.lookupOpen_of_noRaw c (by decide +kernel) k.name]
    | inj _ => rfl
  have hit := sat_cons hI (Or.inl ⟨_, distUncItem_mem k_cons (by rw [hF]; exact f_pair) (fun _ _ h _ => by cases h)
    f_guarded, rfl⟩)
  have hx : InS I (c.sortName Srt.int) (elemOf c I (int 0)) :=
    (inS_iff _).mp (elemOf_spec hI (sortOf_int 0) KoreAML.val0).2
  have hu : ∀ covs, ovlArgsOf c (.ctor fSig) = some covs → ∀ bs xv z (e : Valuation M) m,
      (KoreAML.Cons.uncoveredP bs covs xv z).interpret I e m := by
    intro covs hcov bs xv z e m
    rw [f_args] at hcov
    cases hcov
    exact KoreAML.interp_conjList fun w hw => absurd hw List.not_mem_nil
  exact distUnc_at (defOK hI) hit (xs := [elemOf c I (int 0)]) (ys := [elemOf c I (int 0)]) rfl rfl
    (single_sorts hx) (single_sorts hx) (fun covs h => hu covs h _ _ _ _) (fun covs h => hu covs h _ _ _ _)
    (fun _ => Iff.rfl)

/-- **Soundness fails** of `c`, which meets every condition of `coreOK` but `idsOK` and the empty
list of overloading symbols, and `FnHyp`. -/
theorem not_sound : ¬ SoundC c := fun h => by
  obtain ⟨⟨M, hM, I, hI⟩, -⟩ := h
  exact no_model M hM I (fun φ hφ => hI φ (Or.inl (Or.inl hφ)))

end OvlTwiceWitness

end Faithful

end KCore
