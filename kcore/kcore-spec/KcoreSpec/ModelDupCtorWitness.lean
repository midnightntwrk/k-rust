/-
  KCore. A semantics that satisfies `Hyp` and `HypSound` and meets every condition of `HypModel`
  but `ctorsOnce`, whose `Γ` has no model because one constructor is listed twice: the regression
  test for `ctorsOnce`.

  `Semantics.gens` reads the constructors of a sort from `ctorSigs`, and `ΓCons` states the
  distinctness of every pair of generators. A signature listed twice gives the pair `(g, g)`, and
  its distinctness axiom (Cons-Dist) is `¬(g = g)` at every argument list of g's sorts, which no
  inhabited model satisfies when those sorts have elements. Here the library lists `.K` (`dotk`,
  no arguments) among its constructors, which the fixed text already has: `NamesApartK` holds (the
  two are one signature), and neither `okAll` nor `idsOK` reads the library's constructors' names.
  The decidable facts are kernel decisions.
-/
import KcoreSpec.ModelNamesWitness
import KcoreSpec.ModelCarrier

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace Faithful

namespace DupCtorWitness

open ML

def kIds : CellIds := { sort := nRegSorts, opt := some (nRegSorts + 1), label := nRegSyms + 2, no := some (nRegSyms + 3) }

/-- The configuration `<k> K </k>` with the generated counter, as ordinary sorts, constructors
and subsorts: the top cell's, its fragment's, the `k` cell's and the counter's. -/
def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

/-- `.K`, the empty K sequence, as the fixed text declares it. -/
def dotkSig : CtorSig := ⟨dotk, [], Srt.k⟩

def c : Semantics :=
  { lib := { ctors := [dotkSig] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

instance : OvlOK c := .of_nil rfl (by decide +kernel)

theorem okAll : c.okAll = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem idsOK : c.idsOK = true := by decide +kernel
theorem names_plain : c.ctorSigs.all (fun k => (iteSort? (c.symName k.name)).isNone) = true := by decide +kernel
theorem names_fns : c.allFns.all (fun fn => (iteSort? (c.symName fn.label)).isNone &&
    (fn.result :: fn.args).all (· < nRegSorts + c.sortNames.length)) = true := by decide +kernel

theorem namesNumbered : NamesNumbered c := by
  refine ⟨fun k hk => ?_, fun o ho g hg => ?_, fun fn hfn s hs => ?_⟩
  · exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp names_plain k hk)
  · have h : c.ovls.all (fun o => o.over.all fun g => (iteSort? (c.symName g)).isNone) = true := by
      decide +kernel
    exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp (List.all_eq_true.mp h o ho) g hg)
  · have := List.all_eq_true.mp names_fns fn hfn
    simp only [Bool.and_eq_true] at this
    exact of_decide_eq_true (List.all_eq_true.mp this.2 s hs)

theorem hyp : Hyp c :=
  ⟨okAll, srReady, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil, namesNumbered⟩

theorem hypSound : HypSound c :=
  ⟨okAll, srReady, namesNumbered, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, inferInstance⟩

/-- `.K` is listed twice among the constructors. -/
theorem ctorSigs_dup : (c.ctorSigs.filter (·.name == dotk)).length = 2 := by decide +kernel

/-- `.K` as a generator of K. -/
def gk : KoreAML.Gen := Gen.toK c (.ctor dotkSig)

/-- Cons-Dist of `.K` with itself: `¬(.K = .K)`. -/
def distAx : KoreAML.P := (KoreAML.Cons.distItem (c.sortName Srt.k) gk gk).pat

theorem distAx_mem_any : (consItemsK c).any (fun it => decide (it.pat = distAx)) = true := by decide +kernel

theorem distAx_mem : distAx ∈ ΓCons c := by
  obtain ⟨it, hit, h⟩ := List.any_eq_true.mp distAx_mem_any
  exact Or.inl ⟨it, hit, of_decide_eq_true h⟩

/-- **`Γ c` has no model**, though `c` satisfies `Hyp`. -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M _ I hI
  have h := hI distAx (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr distAx_mem)))))) ⟨fun _ => default, fun _ _ => False⟩ default
  exact NamesWitness.not_equal_self I _ _ _ h

theorem not_hasModel : ¬ HasModel c := fun h => by
  obtain ⟨M, hM, I, hI⟩ := h hyp
  exact no_model M hM I (fun φ hφ => hI φ (Or.inl hφ))

set_option maxHeartbeats 1000000 in
/-- Every condition of `HypModel` but `ctorsOnce` holds. -/
theorem meets_others : Hyp c ∧ HypSound c ∧ Model.namesApartK c = true ∧ Model.LitsApart c = true ∧
    c.idsOK = true ∧ Model.sortsNumbered c = true ∧ Model.collsNotCtors c = true ∧
    Model.itesApart c = true ∧ Model.kindsApart c = true ∧ Model.fnsApart c = true :=
  ⟨hyp, hypSound, by decide +kernel, by decide +kernel, idsOK, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem not_ctorsOnce : Model.ctorsOnce c = false := by decide +kernel

/-- The core with a constructor listed twice is outside `HypModel`. -/
theorem not_hypModel : ¬ Model.HypModel c := fun h => by
  have := h.ctors
  rw [not_ctorsOnce] at this
  cases this

end DupCtorWitness

end Faithful

end KCore
