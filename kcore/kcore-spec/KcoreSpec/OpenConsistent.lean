/-
  KCore. `Γc` with the step's closure has a model, for a definition whose rules' left sides need
  not bind every variable: the value model.

  - `freeOf_prioOpen`: the free variables of a rule's axiom are its own.
  - `satStepGoal_open`: the value model satisfies the step's closure. A `StepM` step by a rule
    gives every variable of the rule a value (`WellSorted r.vars`), and under it the configuration
    is in the left part of the rule's axiom (`rule_premise_open`) and the successor in its right
    side.
  - `stdI_modelOpen`: the value model satisfies `Γc c ∪ Γstep c`: `Γ` with the rules' axioms by
    `satRulesGoal_open`, the step's closure by `satStepGoal_open`, and the closure axiom
    `boolClosed`, which `Γcl` holds where Bool holds only its literals, by `boolClosed_model`.
    Of the rules it reads `ruleSorted` and `rulePlainOpen`, given as a hypothesis
    (`consistent_open`, Sound.lean, is its statement over `Consistent`).
-/
import KcoreSpec.OpenModel
import KcoreSpec.ModelFnsCl
import KcoreSpec.FaithfulFamilies
import KcoreSpec.StepOld

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-- The free variables of the axiom of a rule with `ruleSorted` and `rulePlainOpen` are its own. -/
theorem freeOf_prioOpen (h : HypModelCore c) {r : Rule} (hs : c.ruleSorted r = true)
    (hp : c.rulePlainOpen r = true) (hrules : ∀ r' ∈ c.rules, c.ruleSorted r' = true ∧ c.rulePlainEx r' = true) {k : KoreAML.VarKey} (hk : k ∈ KoreAML.freeOf [] (prioRuleK c r)) :
    ∃ i < r.vars.length, k = canonKey c r.vars i := by
  obtain ⟨hlhs, -, hreqs, hens, hrhss⟩ := ruleSorted_partsOpen hs hp
  obtain ⟨hex₀, hpre₀, hpost₀⟩ := Semantics.rulePlainOpen_top hp
  -- a key of the left side, the `requires`, the right side or the `ensures`
  have hparts : ∀ {k : KoreAML.VarKey},
      (k ∈ KoreAML.freeOf [] (Term.kore c (canonVars c r.vars) r.lhs) ∨
        k ∈ KoreAML.freeOf [] (reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars)))) ∨
        k ∈ KoreAML.freeOf [] (Term.kore c (canonVars c r.vars) r.rhs) ∨
        k ∈ KoreAML.freeOf [] (reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars))))) →
      ∃ i < r.vars.length, k = canonKey c r.vars i := by
    intro k hk
    have hq : ∀ (q : Option Term), (∀ t, q = some t →
        sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool) →
        k ∈ KoreAML.freeOf [] (reqPat (srtOf c topCellSort) (q.map (Term.kore c (canonVars c r.vars)))) →
        ∃ i < r.vars.length, k = canonKey c r.vars i := by
      intro q hqs hk
      cases hq : q with
      | none => rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
      | some t =>
        rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
        rw [KoreAML.freeOf] at hk
        rcases List.mem_append.mp hk with hk | hk
        · obtain ⟨i, hi, rfl⟩ := freeOf_kore c _ t hk
          exact ⟨i, varOccs_lt t (hqs t hq) i hi, rfl⟩
        · rw [KoreAML.freeOf] at hk; cases hk
    rcases hk with hk | hk | hk | hk
    · obtain ⟨i, hi, rfl⟩ := freeOf_kore c _ r.lhs hk
      exact ⟨i, varOccs_lt r.lhs hlhs i hi, rfl⟩
    · exact hq r.req hreqs hk
    · obtain ⟨i, hi, rfl⟩ := freeOf_kore c _ r.rhs hk
      exact ⟨i, varOccs_lt r.rhs hrhss i hi, rfl⟩
    · exact hq r.ens hens hk
  rw [prioRuleK_top hex₀ hpre₀ hpost₀] at hk
  dsimp only at hk
  split at hk
  · rw [KoreAML.freeOf] at hk
    simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append] at hk
    rcases hk with (hk | hk | hk) | hk
    · exact hparts (Or.inl hk)
    · exact hparts (Or.inr (Or.inl hk))
    · exact hparts (Or.inr (Or.inr hk))
    · exact hparts (Or.inr (Or.inr hk))
  · rw [KoreAML.freeOf] at hk
    simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append] at hk
    rcases hk with (hk | hk | hk | hk) | hk
    · exact hparts (Or.inl hk)
    · exact hparts (Or.inr (Or.inl hk))
    · exfalso
      obtain ⟨φ, hφ, hk⟩ := mem_freeOf_anyOfC hk
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hφ
      obtain ⟨hs', hp'⟩ := hrules r' (List.mem_filter.mp hr').1
      obtain ⟨hlhs', -, hreqs', -, -, -⟩ := ruleSorted_partsEx hs' hp'
      exact freeOf_appliesOpen hlhs' (fun t ht i hi => varOccs_lt t (hreqs' t ht) i hi)
        (Semantics.rulePlainEx_top hp').1 hk
    · exact hparts (Or.inr (Or.inr hk))
    · exact hparts (Or.inr (Or.inr hk))

/-- **`SatStepGoal`**, for a definition whose rules have `ruleSorted` and `rulePlainOpen`: the value
model satisfies the step's closure axiom. -/
theorem satStepGoal_open (h : HypModelCore c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true) : SatStepGoal c := by
  have hn := h.namesK
  have hrulesEx : ∀ r' ∈ c.rules, c.ruleSorted r' = true ∧ c.rulePlainEx r' = true :=
    fun r' hr' => ⟨(hrules r' hr').1, (Semantics.rulePlainOpen_iff_ex.mp (hrules r' hr').2).1⟩
  rintro φ rfl
  rw [stepClosure_pat]
  dsimp only
  intro e m
  generalize hy : (⟨tablesLen (c.rules.map (prioRuleK c)) 0 + 1⟩ : EVar) = y
  have hall : ∀ (x : EVar) (φ : KoreAML.P) (e : Valuation Elem) (m : Elem),
      (∀ a, φ.interpret (stdI c) ⟨Function.update e.evalEvar x a, e.evalSvar⟩ m) → (∀∀ x φ).interpret (stdI c) e m := by
    intro x φ e m h'
    unfold Pattern.universal
    rw [interpret_neg, interpret_exists]
    rintro ⟨a, ha⟩
    rw [interpret_neg] at ha
    exact ha (h' a)
  refine hall y _ e m fun a => ?_
  -- the valuation inside the universal
  let e1 : Valuation Elem := ⟨Function.update e.evalEvar y a, e.evalSvar⟩
  show (KoreAML.sNext (.evar y) ⊆⊆ _ : KoreAML.P).interpret (stdI c) e1 m
  rw [KoreAML.interp_included defOK_std]
  intro x0 hx0
  -- a successor of `a` by a rule
  unfold KoreAML.sNext at hx0
  rw [KoreAML.interp_app] at hx0
  obtain ⟨a0, b0, ha0, hb0, hab⟩ := hx0
  have ha0' : a0 = .app .next [] := ha0
  subst ha0'
  have hb0a : b0 = e1.evalEvar y := hb0
  have hst : StepE c x0 b0 := hab
  cases x0 with
  | srt _ => exact hst.elim
  | app _ _ => exact hst.elim
  | val x =>
  cases b0 with
  | srt _ => exact hst.elim
  | app _ _ => exact hst.elim
  | val yv =>
  obtain ⟨hx, hyv, hstep⟩ := hst
  obtain ⟨r, hr, σ, hσ, hmatch, hreq, -, heval, hens, -, hprio⟩ := hstep
  obtain ⟨hs, hp⟩ := hrules r hr
  obtain ⟨-, -, -, hensS, hrhss⟩ := ruleSorted_partsOpen hs hp
  have hnum := rule_vars_numOpen h hs hp
  obtain ⟨L, hPL, hLk, hLread⟩ := rule_premise_open h hs hp hrulesEx
  -- its disjunct
  obtain ⟨off, hoff, hmem⟩ := stepF_mem y (c.rules.map (prioRuleK c)) ([], [], 0) (prioRuleK c r)
    (List.mem_map.mpr ⟨r, hr, rfl⟩)
  refine disjList_intro hmem ?_
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let P := prioRuleK c r
  let tbl : KoreAML.VarTable := List.replicate off (.sortVar "#pad") ++ KoreAML.tableOf [] P
  have hin_tbl : ∀ k ∈ KoreAML.varsOf P, k ∈ tbl := fun k hk =>
    List.mem_append_right _ (List.mem_eraseDups.mpr (List.mem_append_right _ hk))
  have hinL : ∀ k ∈ KoreAML.varsOf L, k ∈ tbl := fun k hk => hin_tbl k (by
    show _ ∈ KoreAML.varsOf (prioRuleK c r)
    rw [hPL, KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ hk))
  have hy_ne : ∀ k ∈ tbl, y ≠ tbl.ev k := by
    intro k hk he
    have h1 := index_le hk
    have hoff' : off + (KoreAML.tableOf [] P).length ≤ tablesLen (c.rules.map (prioRuleK c)) 0 := hoff
    rw [← he, ← hy] at h1
    have h2 : tbl.length = off + (KoreAML.tableOf [] P).length := by simp [tbl]
    simp only at h1
    omega
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => hinL _ (hLk i hi).2
  -- the valuation of the rule's variables
  let e' := overE c tbl r.vars σ e1
  have hvar := overE_ok (e := e1) hkeys hσ
  have he'y : e'.evalEvar y = .val yv := by
    rw [overE_off (fun i hi => hy_ne _ (hkeys i hi))]
    exact hb0a.symm
  have hensR : ∀ yy, c.sortOf yy = some topCellSort →
      (KoreAML.tr ⟨tbl, []⟩ (reqPat C (r.ens.map (Term.kore c vs)))).interpret (stdI c) e' (.val yy) := by
    intro yy hyy
    cases hq : r.ens with
    | none =>
      simp only [Option.map_none, reqPat]
      rw [KoreAML.tr, KoreAML.interp_sTop defOK_std (top_free _),
        KoreAML.interp_inhOf_of (srtOf_top_den h e'), inh_srt]
      exact hyy
    | some t =>
      simp only [Option.map_some]
      exact (reqPat_iff h hvar (termOK_of_sorted h fns_headsOK (hensS t hq)) (srtOf_top_den h e') top_isSort _).mpr
        ⟨(inh_srt topCellSort (.val yy)).mpr hyy, hens t hq⟩
  have hLx : (KoreAML.tr ⟨tbl, []⟩ L).interpret (stdI c) e' (.val x) :=
    (hLread tbl e' σ x hinL hσ hx hvar).mpr ⟨hmatch, hreq, hprio, yv, heval, hens⟩
  -- the disjunct's existentials
  have hdisj : (KoreAML.closureDisjunct [] off y P).2 =
      ((evarsOf (KoreAML.freeOf [] P).eraseDups).foldr (fun (k, s) φ => KoreAML.sExists (tbl.ev k) (KoreAML.trSort tbl s) φ)
        (KoreAML.tr ⟨tbl, []⟩ L ⋀ (y ∈∈ KoreAML.tr ⟨tbl, []⟩
          (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))])))) := by
    unfold KoreAML.closureDisjunct
    simp only [tbl]
    simp only [P, hPL]
    rfl
  rw [hdisj]
  have hfree : ∀ ks ∈ evarsOf (KoreAML.freeOf [] P).eraseDups, ∃ i < r.vars.length, ks.1 = canonKey c r.vars i ∧
      ks.2 = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
    intro ks hks
    obtain ⟨hk1, n, hn⟩ := mem_filterMap_evar hks
    obtain ⟨i, hi, he⟩ := freeOf_prioOpen h hs hp hrulesEx (List.mem_eraseDups.mp hk1)
    refine ⟨i, hi, he, ?_⟩
    rw [he, canonKey_eq c hi] at hn
    injection hn with _ h2
    exact h2.symm
  refine sExists_foldr_intro _ e1 e' _ (fun z hz => overE_off fun i hi he => ?_) rfl ?_ ?_
  · -- off the binders the valuation is unchanged
    have hk : canonKey c r.vars i ∈ KoreAML.freeOf [] P := by
      show _ ∈ KoreAML.freeOf [] (prioRuleK c r)
      rw [hPL, KoreAML.freeOf]
      exact List.mem_append_left _ (hLk i hi).1
    have hks := evar_mem_filterMap (List.mem_eraseDups.mpr (by rw [canonKey_eq c hi] at hk; exact hk))
    exact hz _ hks (by rw [he, canonKey_eq c hi])
  · intro ks hks
    obtain ⟨i, hi, h1, h2⟩ := hfree ks hks
    refine ⟨_, h2, ?_⟩
    rw [h1, overE_at hkeys hi]
    obtain ⟨v, hv, hsv⟩ := hσ i (r.vars.getD i 0) (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
    rw [hv]
    exact (inhOf_sort hn (hnum i hi) KoreAML.val0 _).mpr hsv
  · rw [interpret_conj]
    refine ⟨hLx, ?_⟩
    rw [KoreAML.interp_member defOK_std, he'y, tr_and2, KoreAML.interp_sAnd]
    have hrd := tr_term h hvar (termOK_of_sorted h fns_headsOK hrhss)
    exact ⟨(hrd _).mpr ⟨yv, heval, rfl⟩, hensR yv hyv⟩

end Model

end Faithful

open Faithful Faithful.Model

/-- **The value model is a model of `Γc` with the step's closure**, for a semantics that `coreOK`
accepts with `HypModelCore`, whose rules have `ruleSorted` and `rulePlainOpen`: `Γ` with the rules'
axioms by `satRulesGoal_open`, the step's closure by `satStepGoal_open`, and `boolClosed`, which
`Γcl` holds where Bool holds only its literals, by `boolClosed_model`. -/
theorem stdI_modelOpen (c : Semantics) (h : c.coreOK = true) (hm : HypModelCore c) (hl : OpenLaws c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true) (hFns : SatFnsGoal c) :
    stdI c ⊧ᴵP (Γc c ∪ Γstep c) := by
  intro φ hφ
  rcases hφ with (hφ | hφ) | hφ
  · rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
    · exact satSigGoal hm φ hφ
    · exact satConsGoal hm hl φ hφ
    · exact satDomainsGoal hm φ hφ
    · exact satCollsGoal hm φ hφ
    · exact hFns φ hφ
    · exact satRulesGoal_open hm hrules φ hφ
    · exact satFallbackGoal hm φ hφ
  · obtain ⟨-, hl, rfl⟩ := hφ
    exact boolClosed_model hm h hl
  · exact satStepGoal_open hm hrules φ hφ

end KCore
