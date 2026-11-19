/-
  KCore, outside the cone: a rule sentence of the text whose right side holds nothing is refuted by
  Γ where a configuration matches its left side. Beside `TieRuleRhs` (the direction from the text
  to Γ's item).

  A model of Γ holds an element for each configuration (`elemOf`), and the left side's term of a
  rule holds that element at the valuation of a match (`left_at_match`: `patVal_den4` at `overV`).
  A sentence `\rewrites{C}(T ∧ ⊤, R)` with T that term states that each element of its left side
  has a successor among the elements of R. So where R holds nothing at the match's valuation, no
  model of Γ is a model of the sentence (`rhs_empty_refuted`). `ens_at_match`: a rule's `ensures`
  at the match's valuation holds the elements of the value it evaluates to, which is how a right
  side that conjoins a predicate is shown to hold nothing where the predicate is false.
-/
import KcoreSpec.TieRuleRhs
import KcoreSpec.TieRuleGuard

set_option autoImplicit false

namespace KCore

namespace TieRuleRhs

open ML Faithful KoreAML

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The left side's term of a rule holds the element of a configuration it matches**, in a model
of Γ, at the valuation that gives the rule's variables the elements of the match σ. -/
theorem left_at_match (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {r : Rule} (hs : c.ruleSorted r = true)
    {σ : Subst} {x : Config c} (hσ : c.WellSorted r.vars σ) (hmatch : PatVal c σ r.lhs x.val)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) (e : Valuation M) :
    (tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I (overV c I tbl r.vars σ e)
      (elemOf c I x.val) := by
  obtain ⟨hok, hsr, hnn, -, hph, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  exact ((patVal_den4 hI hnn.1 hph hsc.trans hσ (canonVars_length c r.vars) (overV_agrees hI hkeys hσ) hmatch
    (Semantics.ruleSorted_lhs_nf c hs)).2 _).mpr (((elemOf_spec hI x.property _).1 _).mpr rfl)

/-- **Γ refutes a rule sentence whose right side holds nothing where a configuration matches.**
`r` is a rule of `c` with `ruleSorted`, σ a well-sorted match of its left side at the configuration
`x`. The sentence is the item of `\rewrites{C}(T ∧ ⊤, R)` at a table `t` that holds the rule's
variables, T the left side's term and C the sort of configurations, with guards on variables of
the rule (`fT`). At the valuation of the match `R` holds nothing. Then a model of Γ is no model of
the sentence: `x`'s element is one of the left side, and the sentence gives it a successor among
the elements of `R`. -/
theorem rhs_empty_refuted (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {r : Rule} (hs : c.ruleSorted r = true)
    {σ : Subst} {x : Config c} (hσ : c.WellSorted r.vars σ) (hmatch : PatVal c σ r.lhs x.val)
    {t : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ t) {fT : List VarKey}
    (hfT : ∀ k ∈ fT, ∃ i < r.vars.length, k = canonKey c r.vars i) {R : Kore.Pattern} (e : Valuation M)
    (hR : ∀ b, ¬ (tr ⟨t, []⟩ R).interpret I (overV c I t r.vars σ e) b)
    (hsen : I ⊧ᴵ TieRuleLhs.itemAt t fT (srtOf c topCellSort)
      (.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.lhs, .top (srtOf c topCellSort)]) R) : False := by
  obtain ⟨-, -, -, -, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hD := defOK hI
  have hx := elemOf_top hI x t (overV c I t r.vars σ e)
  have hg : ∀ k ∈ fT, (guardOf t k).interpret I (overV c I t r.vars σ e) (elemOf c I x.val) := fun k hk => by
    obtain ⟨i, hi, rfl⟩ := hfT k hk
    obtain ⟨w, hw, hsw⟩ := hσ i (r.vars.getD i 0) (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
    have hkk := canonKey_eq c hi
    rw [hkk, interp_guard_evar hD, trSort_srt, ← hkk, overV_at hkeys hi, hw]
    exact (elemOf_spec hI hsw _).2
  refine left_empty_of_right_empty hD hsen _ _ hg hR (fun a ha => ?_) (elemOf c I x.val) ?_
  · rw [tr_and2, interp_sAnd] at ha
    have hT : tr ⟨t, []⟩ (.top (srtOf c topCellSort)) = sTop (trSort t (srtOf c topCellSort)) := by rw [tr]
    rw [hT, interp_sTop hD (by unfold srtOf; rw [trSort_srt]; rfl)] at ha
    exact ha.2
  · rw [tr_and2, interp_sAnd]
    refine ⟨left_at_match h hI hs hσ hmatch hkeys e, ?_⟩
    have hT : tr ⟨t, []⟩ (.top (srtOf c topCellSort)) = sTop (trSort t (srtOf c topCellSort)) := by rw [tr]
    rw [hT, interp_sTop hD (by unfold srtOf; rw [trSort_srt]; rfl)]
    exact hx

/-- **A rule's `ensures` at a match denotes its value**, in a model of Γ of a semantics whose
conditions read no confined sort: where the `ensures` evaluates to `v` under the match σ, its term
holds the elements of `v` at the valuation of the match. -/
theorem ens_at_match (h : c.coreOK = true) (hrc : c.readsConfined = false) (hI : I ⊧ᴵP Γ c) {r : Rule}
    (hs : c.ruleSorted r = true) {σ : Subst} (hσ : c.WellSorted r.vars σ) {t : Term} {v : GroundTerm}
    (ht : r.ens = some t) (hev : EvalTerm c σ t (some v))
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) (e : Valuation M) (m : M) :
    (tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) t)).interpret I (overV c I tbl r.vars σ e) m ↔
      (den c v).interpret I (overV c I tbl r.vars σ e) m := by
  have hx := Semantics.coreOK_iff_ex.mp h
  have hIc : I ⊧ᴵP Γc c := by rw [Γc_plain hrc]; exact hI
  have hcw := (openDecided_of_readsConfined hrc).2
  obtain ⟨hok, hsr, hnn, -, hph, -, -, -, hno⟩ := hypSoundEx_of_coreEx hx
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have hneg := neg_of_coreClEx hIc (Semantics.sortedOKClEx_of_sortedOKEx hok) hsr (Semantics.coreOKEx_parts hx).2.1 hph hcw
    (HoldsShape.preReadAll_of_coreEx hx hIc)
  obtain ⟨-, -, -, hensS, -⟩ := Model.ruleSorted_partsPP hs
  exact evalTerm_den4ClQ hI hnn hsc hph (clauseOpenFactsQ_of_sortedOKEx hok) hneg
    (HoldsShape.preReadAll_of_coreEx hx hIc) (clauseExRead_all_of_coreEx hx hIc) hev fns_headsOK hσ
    (canonVars_length c r.vars) (overV_agrees hI hkeys hσ) (hensS t ht) m

/-- **A rule's `ensures` that evaluates to `false` at a match holds nothing there**, in a model of
Γ of a semantics whose conditions read no confined sort: the equality of the `ensures` with `true`
would give the value `true` the element of `false`, and the two values of Bool are apart. -/
theorem ens_false_empty (h : c.coreOK = true) (hrc : c.readsConfined = false) (hI : I ⊧ᴵP Γ c) {r : Rule}
    (hs : c.ruleSorted r = true) {σ : Subst} (hσ : c.WellSorted r.vars σ) {t : Term}
    (ht : r.ens = some t) (hev : EvalTerm c σ t (some (KCore.bool false)))
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) (e : Valuation M) (b : M) :
    ¬ (tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (some (Term.kore c (canonVars c r.vars) t)))).interpret I
      (overV c I tbl r.vars σ e) b := by
  obtain ⟨hok, hsr, -, hg, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have htr := (sortCtx_of_all hok hsr (OvlOK.ovlCase hno)).trans
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hI (top_numbered (c := c))
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  generalize hev' : overV c I tbl r.vars σ e = e'
  have hSC : ∀ a, (trSort tbl (srtOf c topCellSort)).interpret I e' a ↔ a = σC := by
    unfold srtOf; rw [trSort_srt]; exact hσC1
  simp only [reqPat]
  rw [tr, interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) hSC hσB2 hσC2]
  rintro ⟨-, hall⟩
  have hF := elemOf_spec hI (sortOf_bool (c := c) false) e'
  have hT := elemOf_spec hI (sortOf_bool (c := c) true) e'
  have hFin : Inh I σB (elemOf c I (KCore.bool false)) := by
    have := hF.2
    rw [sortName_bool] at this
    exact (interp_inhOf_of (S := KoreAML.sym _) hσB1).mp this
  have h1 := (hall _ hFin).mp (by
    rw [← hev']; exact (ens_at_match h hrc hI hs hσ ht hev hkeys e _).mpr (by rw [hev']; exact (hF.1 _).mpr rfl))
  have h2 : (den c (KCore.bool true)).interpret I e' (elemOf c I (KCore.bool false)) := by
    unfold den KoreAML.den KCore.bool
    rw [GroundTerm.kore, sortName_bool]
    exact h1
  exact absurd (values_apart hI hg htr (apart_of_distinct bool_distinct) (sortOf_bool (c := c) false) (sortOf_bool (c := c) true)
    ((hT.1 _).mp h2)) (by decide)

end

/-! ## The parts of a rule's axiom under an interpretation of the parameters -/

kernel_rfl kore_withHooks_rr : ∀ (c : Semantics) (H : HookParams) (vs : List KoreAML.Var) (p : Term),
  Term.kore (c.withHooks H) vs p = Term.kore c vs p
kernel_rfl canonVars_withHooks_rr : ∀ (c : Semantics) (H : HookParams) (vars : List Srt),
  canonVars (c.withHooks H) vars = canonVars c vars
kernel_rfl canonKey_withHooks_rr : ∀ (c : Semantics) (H : HookParams) (vars : List Srt) (i : Nat),
  canonKey (c.withHooks H) vars i = canonKey c vars i
kernel_rfl srtOf_withHooks_rr : ∀ (c : Semantics) (H : HookParams) (s : Srt),
  srtOf (c.withHooks H) s = srtOf c s
kernel_rfl ruleSorted_withHooks_rr : ∀ (c : Semantics) (H : HookParams) (r : Rule),
  (c.withHooks H).ruleSorted r = c.ruleSorted r

/-! ## On a text, for every interpretation of the parameters -/

section
open Exec Cert
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **`rhs_empty_refuted` from facts decided on the data, for every interpretation H of the
parameters.** `c` meets `coreOK` and has no raw parameter; the matcher lists a well-sorted match
of the rule `r` at the configuration `x`; the table `t` holds the rule's variables and the guards
`fT` are on variables of the rule. In a model of `Γ (c.withHooks H)`, if the sentence's right side
`R` holds nothing at the valuation of each listed match, the sentence does not hold. -/
theorem rhs_empty_refuted_everyH (hcore : c.coreOK = true) (hraw : ∀ k ∈ c.params, k.raw = false) {r : Rule}
    (hs : c.ruleSorted r = true) (x : Config c) {n : Nat}
    (hm : ((matchP c n [] r.lhs x.val).filter (wellSorted c r.vars)).isEmpty = false)
    {t : VarTable} (hkeys : (List.range r.vars.length).all (fun i => t.contains (canonKey c r.vars i)) = true)
    {fT : List VarKey}
    (hfT : fT.all (fun k => (List.range r.vars.length).any (fun i => k == canonKey c r.vars i)) = true)
    {R : Kore.Pattern} (H : HookParams) (hI : I ⊧ᴵP Γ (c.withHooks H))
    (hR : ∀ σ ∈ (matchP c n [] r.lhs x.val).filter (wellSorted c r.vars), (c.withHooks H).WellSorted r.vars σ →
      ∀ b, ¬ (tr ⟨t, []⟩ R).interpret I (overV (c.withHooks H) I t r.vars σ (val0 : Valuation M)) b)
    (hsen : I ⊧ᴵ TieRuleLhs.itemAt t fT (srtOf c topCellSort)
      (.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.lhs, .top (srtOf c topCellSort)]) R) : False := by
  obtain ⟨σ, hσm⟩ := List.exists_mem_of_ne_nil _ (List.isEmpty_eq_false_iff.mp hm)
  have hσm' : σ ∈ (matchP (c.withHooks H) n [] r.lhs (TieRuleLhs.cfgH hraw x H).val).filter
      (wellSorted (c.withHooks H) r.vars) := by
    rw [matchP_withHooksC, wellSorted_withHooks_hr c H hraw]; exact hσm
  obtain ⟨hmm, hws⟩ := List.mem_filter.mp hσm'
  have hσ := wellSorted_iff.mp hws
  obtain ⟨-, hpv⟩ := matchP_sound _ (canonV_of_sortOf (TieRuleLhs.cfgH hraw x H).property) hmm
  have hk : ∀ i < r.vars.length, canonKey (c.withHooks H) r.vars i ∈ t := fun i hi => by
    rw [canonKey_withHooks_rr]
    exact List.contains_iff_mem.mp (List.all_eq_true.mp hkeys i (List.mem_range.mpr hi))
  have hf : ∀ k ∈ fT, ∃ i < r.vars.length, k = canonKey (c.withHooks H) r.vars i := fun k hk' => by
    obtain ⟨i, hi, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hfT k hk')
    exact ⟨i, List.mem_range.mp hi, by rw [canonKey_withHooks_rr]; exact beq_iff_eq.mp he⟩
  rw [← srtOf_withHooks_rr c H, ← canonVars_withHooks_rr c H, ← kore_withHooks_rr c H] at hsen
  exact rhs_empty_refuted ((Semantics.coreOK_withHooks c H).trans hcore) hI
    ((ruleSorted_withHooks_rr c H r).trans hs) hσ hpv hk hf val0 (hR σ hσm hσ) hsen

/-- **An `ensures` the check evaluates to `false` at each listed match holds nothing there, for
every interpretation H of the parameters**: `ens_false_empty` from facts decided on the data. -/
theorem ens_false_empty_everyH (hcore : c.coreOK = true) (hraw : ∀ k ∈ c.params, k.raw = false)
    (hrc : c.readsConfined = false) (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    {r : Rule} (hr : r ∈ c.rules) (hs : c.ruleSorted r = true) {t : Term} (ht : r.ens = some t) {n : Nat} {σ : Subst}
    (hev : evalTC c n σ t = some (some (KCore.bool false)))
    {tbl : VarTable} (hkeys : (List.range r.vars.length).all (fun i => tbl.contains (canonKey c r.vars i)) = true)
    (H : HookParams) (hI : I ⊧ᴵP Γ (c.withHooks H)) (hσ : (c.withHooks H).WellSorted r.vars σ) (b : M) :
    ¬ (tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (some (Term.kore c (canonVars c r.vars) t)))).interpret I
      (overV (c.withHooks H) I tbl r.vars σ (val0 : Valuation M)) b := by
  have hokH := (Semantics.ok_withHooks c H).trans hok
  have hsrH := (Semantics.srReady_withHooks c H).trans hsr
  have hmrH := (Semantics.matchReady_withHooks c H).trans hmr
  have hsc := sortCtx_of hokH hsrH (Exec.ovlCase_of hmrH)
  have hen := ruleOK_ens_of hokH (r := r) hr
  rw [ht] at hen
  have he : EvalTerm (c.withHooks H) σ t (some (KCore.bool false)) :=
    evalT_sound hsc (clauseCtx_of hokH) (matchCtx_of hmrH) n
      (evalTC_sound n (by rw [evalTC_withHooks c H hraw]; exact hev)) (headsOK_fns _) hσ (reqOK_some hen)
  have hk : ∀ i < r.vars.length, canonKey (c.withHooks H) r.vars i ∈ tbl := fun i hi => by
    rw [canonKey_withHooks_rr]
    exact List.contains_iff_mem.mp (List.all_eq_true.mp hkeys i (List.mem_range.mpr hi))
  have h := ens_false_empty ((Semantics.coreOK_withHooks c H).trans hcore)
    ((Semantics.readsConfined_withHooks c H).trans hrc) hI ((ruleSorted_withHooks_rr c H r).trans hs) hσ ht he hk
    (val0 : Valuation M) b
  rw [srtOf_withHooks_rr, canonVars_withHooks_rr, kore_withHooks_rr] at h
  exact h

end

end TieRuleRhs

end KCore
