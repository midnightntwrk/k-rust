/-
  KCore. A semantics that satisfies `Hyp` and `HypSound` and meets every condition of `HypModel`
  but `fnsApart`, whose `Γ` has no model because a function is named like a constructor: the
  regression test for `fnsApart`.

  `idsOK` numbers the user's functions apart from the user's constructors, but no check numbers the
  library's constructors. Here the library has a constructor `f : KItem` and the user's function
  `f : KItem` (one signature, so `NamesApartK` holds) has the one clause `f() = #KConfigValue(.K)`.
  `Γ` says of the symbol `f` both that its application is the constructor term `f()` and, by the
  function's equation, that it is `#KConfigValue(.K)`; these are two distinct values of KItem, and
  `Γ` makes distinct values of KItem distinct elements (`values_apart`). Evaluation reads `f` as a
  constructor and never calls the function. The decidable facts are kernel decisions.
-/
import KcoreSpec.ModelDupCtorWitness

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace Faithful

namespace FnCtorWitness

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

/-- The function `f`, numbered after the cell's symbols. -/
def fl : Sym := nRegSyms + 4

/-- `#KConfigValue(.K)`. -/
def rhsT : Term := .app kconfigValue [.app dotk []]

/-- `f() = #KConfigValue(.K)`. -/
def cl : Clause := { vars := [], pats := [], req := none, rhs := rhsT, ens := none }

def fn : Fn := { label := fl, args := [], result := Srt.kitem, clauses := [cl] }

def c : Semantics :=
  { lib := { ctors := [⟨kconfigValue, [Srt.k], Srt.kitem⟩, ⟨fl, [], Srt.kitem⟩] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [fn]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

instance : OvlOK c := .of_nil rfl (by decide +kernel)

theorem okAll : c.okAll = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem idsOK : c.idsOK = true := by decide +kernel
theorem namesNumbered : NamesNumbered c := namesNumbered_spec (by decide +kernel)

theorem lookup_f : c.lookupFn fl = some fn := rfl

theorem rhs_eval : EvalTerm c [] rhsT (some (.ctor kconfigValue [.ctor dotk []])) := by
  have h1 : EvalTerm c [] (.app dotk []) (some (.ctor dotk [])) :=
    EvalTerm.ctor (rs := []) (by decide +kernel) .nil
  exact EvalTerm.ctor (rs := [some (.ctor dotk [])]) (by decide +kernel) (.cons h1 .nil)

/-- The function is `#KConfigValue(.K)` at its one argument list: its clause applies. -/
theorem eval_f : Eval c fl [] (some (.ctor kconfigValue [.ctor dotk []])) :=
  .clause lookup_f (List.mem_singleton_self _) (fun _ _ h => by simp [cl] at h) .nil (fun _ h => by cases h) .top
    (fun _ h _ hlt => by rw [List.mem_singleton.mp h] at hlt; exact absurd hlt (Nat.lt_irrefl _)) rfl rhs_eval
    (fun _ h => by simp [cl] at h) .top

theorem hyp : Hyp c := by
  refine ⟨okAll, srReady, fun g hg vs hvs => ?_, fun g hg ht => ?_, fun g hg => ?_, fun g hg cl' hcl' => ?_,
    namesNumbered⟩
  · rw [List.mem_singleton.mp hg] at hvs ⊢
    have : vs = [] := by
      cases vs with
      | nil => rfl
      | cons v vs => obtain ⟨_, _, _, _, h⟩ := sortsOf_cons.mp hvs; cases h
    subst this
    exact ⟨_, eval_f⟩
  · rw [List.mem_singleton.mp hg] at ht; cases ht
  · rw [List.mem_singleton.mp hg]
    intro cl1 cl2 hp
    have h0 : pairs fn.clauses = [] := rfl
    rw [h0] at hp
    cases hp
  · rw [List.mem_singleton.mp hg] at hcl'
    rw [List.mem_singleton.mp hcl']
    refine (matchIndependent_iff_noExs rfl).mpr ?_
    intro vs σ σ' _ _ _ _ _ _ _
    exact Or.inl ⟨rfl, rfl, rfl, rfl, fun i hi => (by simp [cl, rhsT, varOccs, varOccsList] at hi),
      fun t ht => (by simp [cl] at ht)⟩

theorem hypSound : HypSound c :=
  ⟨okAll, srReady, namesNumbered, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, inferInstance⟩

set_option maxHeartbeats 1000000 in
/-- Every condition of `HypModel` but `fnsApart` holds. -/
theorem meets_others : Hyp c ∧ HypSound c ∧ Model.namesApartK c = true ∧ Model.LitsApart c = true ∧
    c.idsOK = true ∧ Model.sortsNumbered c = true ∧ Model.collsNotCtors c = true ∧
    Model.itesApart c = true ∧ Model.kindsApart c = true ∧ Model.ctorsOnce c = true :=
  ⟨hyp, hypSound, by decide +kernel, by decide +kernel, idsOK, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem not_fnsApart : Model.fnsApart c = false := by decide +kernel

/-- The core with a function named like a constructor is outside `HypModel`. -/
theorem not_hypModel : ¬ Model.HypModel c := fun h => by
  have := h.fns
  rw [not_fnsApart] at this
  cases this

/-- The value `f()` of the library's constructor. -/
def vf : GroundTerm := .ctor fl []
/-- The value `#KConfigValue(.K)`. -/
def vk : GroundTerm := .ctor kconfigValue [.ctor dotk []]

theorem vf_sort : c.sortOf vf = some Srt.kitem := by decide +kernel
theorem vk_sort : c.sortOf vk = some Srt.kitem := by decide +kernel
theorem genWf_ok : genWf c = true := by decide +kernel
theorem kitem_apart : apartSort c Srt.kitem = true := by decide +kernel
theorem f_plain : instDecode? (c.symName fl) = none := by decide +kernel

/-- **`Γ c` has no model**, though `c` satisfies `Hyp`. -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M _ I hI
  have htr := (sortCtx_of_all (Semantics.sortedOK_of_okAll okAll (Semantics.ovlPatsOK_of_ovlCase (OvlOK.ovlCase inferInstance))) srReady (OvlOK.ovlCase inferInstance)).trans
  -- the function's equation: `f()` is what `#KConfigValue(.K)` denotes
  have heq := clause_eq hI namesNumbered htr lookup_f (cl := cl) (List.mem_singleton_self _) rfl rfl rfl (ws := [])
    (by decide +kernel) (σ' := []) (fun _ _ h => by simp [cl] at h) .nil rfl (by decide +kernel)
    (fun _ h => by simp [cl] at h) (fun _ h => by cases h) (fun _ h => by simp [cl, rhsT, varOccs, varOccsList] at h)
    (fun _ h => by simp [cl] at h)
    (r := some vk) (fun v hv => by cases hv; exact vk_sort) (fun _ _ _ _ h => by cases h)
    (fun tbl e _ => right_iff hI namesNumbered (lookupFn_spec lookup_f).1 (fun v hv => by cases hv; exact vk_sort)
      (fun m => by
        show (KoreAML.tr ⟨tbl, []⟩ (GroundTerm.kore c vk)).interpret I e m ↔ (den c vk).interpret I e m
        rfl)
      (fun t ht => by simp [cl] at ht))
  -- `f()` as the library's constructor's value
  have hfd : ∀ e m, (KoreAML.den (symApp c fl (GroundTerm.koreList c []))).interpret I e m ↔
      (den c vf).interpret I e m := fun e m => by
    rw [symApp_noInst f_plain] <;> rfl
  have he : elemOf c I vf = elemOf c I vk := by
    have h1 := (elemOf_spec hI vf_sort KoreAML.val0).1
    have h2 := (elemOf_spec hI vk_sort KoreAML.val0).1
    have := (heq KoreAML.val0 (elemOf c I vf)).mp ((hfd _ _).mpr ((h1 _).mpr rfl))
    exact (h2 _).mp this
  have := values_apart hI genWf_ok htr kitem_apart vf_sort vk_sort he
  simp only [vf, vk, GroundTerm.ctor.injEq] at this
  exact absurd this.1 (by decide +kernel)

theorem not_hasModel : ¬ HasModel c := fun h => by
  obtain ⟨M, hM, I, hI⟩ := h hyp
  exact no_model M hM I (fun φ hφ => hI φ (Or.inl hφ))

end FnCtorWitness

end Faithful

end KCore
