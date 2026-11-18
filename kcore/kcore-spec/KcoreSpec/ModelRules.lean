/-
  KCore. Parts of the reading of the rules' axioms (`SatRulesGoal`, proved in OpenModel.lean by
  `satRulesGoal_open`).

  A rule's axiom is `lhs ∧ ⌈req = true⌉ ∧ ¬ ⋁ competitors ∧ ⌈rhs⌉ → •(rhs ∧ ⊤)` at the
  configuration sort, its variables free and guarded by their sorts. At a valuation giving each
  variable a value of its sort, read as a substitution σ, a configuration in the premise is one the
  rule's left-hand side matches under σ (`tr_pat`), where its `requires` evaluates to `true`
  (`reqPat_iff`), no rule of a smaller priority applies (`applies_iff_open`), and its right-hand side
  evaluates to a value (`tr_term`): that is a step of `StepM` to the right-hand side's value, which
  the right-hand side denotes, and the model's next relation is `StepM` (ModelCarrier.lean).
-/
import KcoreSpec.ModelPat

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

mutual
  theorem kore_freeOf (c : Semantics) (vs : List KoreAML.Var) : ∀ (t : Term) {i : Nat}, i ∈ varOccs t →
      KoreAML.evarKey (vs.getD i default).kore ∈ KoreAML.freeOf [] (Term.kore c vs t)
    | .var j, i, h => by
      rw [varOccs] at h
      rw [mem_one h, Term.kore]; unfold KoreAML.varAt; rw [KoreAML.freeOf]
      simp
    | .app f ts, i, h => by
      rw [varOccs] at h
      rw [kore_app]
      obtain ⟨hd, ss, he, _⟩ := symApp_cases c f (Term.koreList c vs ts)
      rw [he, KoreAML.freeOf]
      exact kore_freeOfList c vs ts h
    | .inj a b t, i, h => by
      rw [varOccs] at h
      rw [Term.kore]; unfold KoreAML.injP; rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList]
      simp only [List.append_nil]
      exact kore_freeOf c vs t h
    | .as t j, i, h => by
      rw [varOccs] at h
      rw [Term.kore, KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList]
      simp only [List.append_nil, List.mem_append]
      rcases List.mem_append.mp h with h | h
      · exact Or.inl (kore_freeOf c vs t h)
      · right
        rw [mem_one h]; unfold KoreAML.varAt; rw [KoreAML.freeOf]
        simp
    | .dv s lit, i, h => by rw [varOccs] at h; cases h
  theorem kore_freeOfList (c : Semantics) (vs : List KoreAML.Var) : ∀ (ts : List Term) {i : Nat},
      i ∈ varOccsList ts → KoreAML.evarKey (vs.getD i default).kore ∈ KoreAML.freeOfList [] (Term.koreList c vs ts)
    | [], i, h => by rw [varOccsList] at h; cases h
    | t :: ts, i, h => by
      rw [varOccsList] at h
      rw [Term.koreList, KoreAML.freeOfList]
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ (kore_freeOf c vs t h)
      · exact List.mem_append_right _ (kore_freeOfList c vs ts h)
end

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sNext_iff (φ : KoreAML.P) (e : Valuation Elem) (x : GroundTerm) :
    (KoreAML.sNext φ).interpret (stdI_T c T) e (.val x) ↔ ∃ y, φ.interpret (stdI_T c T) e (.val y) ∧ StepE_T c T (.val x) (.val y) := by
  unfold KoreAML.sNext
  rw [KoreAML.interp_app]
  constructor
  · rintro ⟨a0, b0, ha0, hb, hab⟩
    have ha0' : a0 = .app .next [] := ha0
    subst ha0'
    have hst : StepE_T c T (.val x) b0 := hab
    cases b0 with
    | val y => exact ⟨y, hb, hst⟩
    | srt _ => exact hst.elim
    | app _ _ => exact hst.elim
  · rintro ⟨y, hy, hst⟩
    exact ⟨.app .next [], .val y, rfl, hy, hst⟩

end AtT

theorem sNext_iff (φ : KoreAML.P) (e : Valuation Elem) (x : GroundTerm) :
    (KoreAML.sNext φ).interpret (stdI c) e (.val x) ↔ ∃ y, φ.interpret (stdI c) e (.val y) ∧ StepE c (.val x) (.val y) :=
  AtT.sNext_iff (c := c) (T := StepM c) (φ := φ) (e := e) (x := x)

/-- The right-hand side of a rule, at the configuration sort, and its value. -/
theorem rhs_next (h : HypModelCore c) {r : Rule} (hr : r ∈ c.rules) (hpre : r.pre = .top) (hpost : r.post = .top) {tbl : KoreAML.VarTable} {e : Valuation Elem}
    {σ : Subst} (hσ : c.WellSorted r.vars σ)
    (hvar : ∀ i, i < r.vars.length → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c r.vars) i)).interpret
      (stdI c) e m ↔ ∃ v, σ.lookup i = some v ∧ m = .val v)
    (hrhs : ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.rhs)).interpret (stdI c) e m ↔
      ∃ v, EvalTerm c σ r.rhs (some v) ∧ m = .val v)
    {x : GroundTerm} (hx : c.sortOf x = some topCellSort) (hmatch : PatVal c σ r.lhs x)
    (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x) {y : GroundTerm}
    (hy : EvalTerm c σ r.rhs (some y)) (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) :
    (KoreAML.sNext (KoreAML.tr ⟨tbl, []⟩ (.and (srtOf c topCellSort)
      [Term.kore c (canonVars c r.vars) r.rhs,
        reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))]))).interpret (stdI c) e (.val x) := by
  have hys := rhs_sorted_coreClEx h.hyp.1 h.hyp.2.1 h.ovlCase hr hσ hy
  have hensS := rule_ctx_ensClEx h.hyp.1 hr
  rw [sNext_iff]
  refine ⟨y, ?_, hx, hys, r, hr, σ, hσ, hmatch, hreq, hpre ▸ .top, hy, hens, hpost ▸ .top, hprio⟩
  rw [tr_and2, KoreAML.interp_sAnd]
  refine ⟨(hrhs _).mpr ⟨y, hy, rfl⟩, ?_⟩
  cases hq : r.ens with
  | none =>
    simp only [Option.map_none, reqPat]
    rw [KoreAML.tr, KoreAML.interp_sTop defOK_std (by unfold srtOf; rw [trSort_srt]; rfl),
      KoreAML.interp_inhOf_of (srtOf_top_den h e), inh_srt]
    exact hys
  | some t =>
    simp only [Option.map_some]
    exact (reqPat_iff h hvar (termOK_of_sorted h fns_headsOK (hensS t hq)) (srtOf_top_den h e) top_isSort _).mpr
      ⟨(inh_srt _ _).mpr hys, hens t hq⟩

theorem freeOf_and_lhs {S : Kore.KSort} {p : Kore.Pattern} {ps : List Kore.Pattern} {k : KoreAML.VarKey}
    (hk : k ∈ KoreAML.freeOf [] p) : k ∈ KoreAML.freeOf [] (.and S (p :: ps)) := by
  simp only [KoreAML.freeOf, KoreAML.freeOfList]
  exact List.mem_append_left _ hk

theorem varsOf_and_mem {S : Kore.KSort} {p : Kore.Pattern} {ps : List Kore.Pattern} {k : KoreAML.VarKey}
    (hp : p ∈ ps) (hk : k ∈ KoreAML.varsOf p) : k ∈ KoreAML.varsOf (.and S ps) := by
  simp only [KoreAML.varsOf]
  refine List.mem_append_right _ ?_
  induction ps with
  | nil => exact absurd hp List.not_mem_nil
  | cons q qs ih =>
    rw [KoreAML.varsOfList]
    rcases List.mem_cons.mp hp with rfl | hp
    · exact List.mem_append_left _ hk
    · exact List.mem_append_right _ (ih hp)

end Model

end Faithful

end KCore
