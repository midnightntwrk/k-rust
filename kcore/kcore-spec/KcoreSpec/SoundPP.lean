/-
  KCore. Soundness at a step by a rule with a `pre` and a `post`: the lemmas that read no clause.

  The rule's axiom is `\rewrites(lhs ∧ ⌈req⌉ ∧ pre ∧ ¬ ⋁ applies ∧ ⌈right⌉, right)`, `right` the
  pattern `∃ē. (rhs ∧ ⌈ens⌉ ∧ post)`.

  - `famEx_of_right_pp`: an element of a rule's right side, at a valuation that gives the variables
    other than the existential ones the elements of their values under σ, is among the instances
    of the application.
  - `ruleRight_sort_pp`, `ceil_right_pp`: an element of a rule's right side is in the configuration
    sort, and the right side is defined where an element is in it, whatever its `post`.
  - `applies_match_pp`: x's element in a rule's `applies` gives a match of its left side at x,
    whatever its `pre`.

  The step's soundness (`step_sound_heldCEx`, `famEx_mem_ppCEx`) is SoundCEx.lean's.
-/
import KcoreSpec.FamExValuesPP
import KcoreSpec.CompletePP
import KcoreSpec.ExSound
import KcoreSpec.OpenSound

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK VarTable)
open HoldsShape (hasBinder Reads reads_of_agrees)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **An element of a rule's right side is among the instances**, for a rule with any `post`: an
element in `ruleRight` through a table that holds the rule's variables and the keys of `post`'s
pattern (`hkQ`), at a valuation that gives the variables other than the existential ones the
elements of their values under σ, is in `famEx c r σ`; `post` is read under the two tables alike
(`tr_condKore_twoT`). -/
theorem famEx_of_right_pp (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c) {r : Rule} (hs : c.ruleSorted r = true)
    {σ : Subst} (hσ : c.WellSorted r.vars σ) {tbl : VarTable}
    (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl)
    (hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl)
    {e' : Valuation M}
    (hval : ∀ i < r.vars.length, i ∉ r.exs →
      e'.evalEvar (tbl.ev (canonKey c r.vars i)) = elemOf c I ((σ.lookup i).getD default))
    {b : M} (hb : (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret I e' b) (e : Valuation M) :
    (famEx c r σ).interpret I e b := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have hs0 := hypSound_of_core h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := id hs0
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  obtain ⟨-, -, -, hensS, hrhss, hexnd, hexs, -, hokQ, -, -⟩ := Model.ruleSorted_partsPP hs
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  have hsorts := sortsNumbered_of_core h
  have hov := Semantics.coreOK_ovls h
  let fixed := (List.range r.vars.length).filter fun i => !r.exs.contains i
  have hfixed : ∀ i, i ∈ fixed ↔ i < r.vars.length ∧ i ∉ r.exs := fun i => by simp [fixed]
  have hfl : ∀ i ∈ fixed, i < r.vars.length := fun i hi => ((hfixed i).mp hi).1
  have hsortB : ∀ i < r.vars.length,
      ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := fun i hi => by
    rw [canonVars_getD c hi]; rfl
  have hinσ : ∀ i < r.vars.length,
      InS I (c.sortName (r.vars.getD i 0)) (elemOf c I ((σ.lookup i).getD default)) := by
    intro i hi
    obtain ⟨w, hw, hsw⟩ := hσ i (r.vars.getD i 0)
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
    rw [hw]
    exact (inS_iff e).mp (elemOf_spec hI hsw e).2
  -- inside `∃ē` on the right side's table
  rw [Model.ruleRight_eqPP hlt] at hb
  obtain ⟨e'', hoff, hguard, hbody⟩ := existsAll_elim hD (Model.ruleExBinders c r) e' _
    (binders_nodupEx hkeys hlt hexnd) (binders_sortEx hlt) hb
  unfold Model.ruleRightBodyPP at hbody
  rw [interp_and (by simp)] at hbody
  have hyR := hbody (Term.kore c (canonVars c r.vars) r.rhs) (List.mem_append_left _ (List.mem_cons_self ..))
  have hensR := hbody (reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars))))
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hpostR : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.post,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e'' b := fun φ hφ => hbody φ (List.mem_append_right _ hφ)
  have hoffE : ∀ i < r.vars.length, i ∉ r.exs →
      e''.evalEvar (tbl.ev (canonKey c r.vars i)) = e'.evalEvar (tbl.ev (canonKey c r.vars i)) := by
    intro i hi hx
    refine hoff _ fun b hb he => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    exact hx ((canonKey_inj hi (hlt j hj) (ev_inj (hkeys i hi) (hkeys j (hlt j hj)) he)) ▸ hj)
  have hin'' : ∀ i < r.vars.length,
      InS I (c.sortName (r.vars.getD i 0)) (e''.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))) := by
    intro i hi
    by_cases hx : i ∈ r.exs
    · exact hguard _ (List.mem_map_of_mem (f := fun i => ((canonVars c r.vars).getD i default).kore) hx) _
        (hsortB i hi)
    · show InS I _ (e''.evalEvar (tbl.ev (canonKey c r.vars i)))
      rw [hoffE i hi hx, hval i hi hx]; exact hinσ i hi
  have hbC : InS I (c.sortName topCellSort) b :=
    rhsSort hI hg hsc.trans hnn.1 (canonVars_length c r.vars) hin'' fns_headsOK hrhss b hyR
  have hinC : ∀ (tb : VarTable) (e₀ : Valuation M),
      (KoreAML.inhOf (KoreAML.trSort tb (srtOf c topCellSort))).interpret I e₀ b := fun tb e₀ => by
    unfold srtOf; rw [trSort_srt]; exact (inS_iff e₀).mpr hbC
  -- `famEx`'s pattern
  rw [famEx_eqPPx hlt]
  unfold KoreAML.denB
  generalize htf : KoreAML.tableOf [] _ = tf
  have hkf : ∀ i < r.vars.length, canonKey c r.vars i ∈ tf := by
    intro i hi
    rw [← htf]
    unfold KoreAML.tableOf
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    by_cases hx : i ∈ r.exs
    · refine Model.varsOf_existsAll_bodyEx ?_ _
      refine Model.varsOf_and_mem (List.mem_append_right _ (List.mem_singleton_self _)) ?_
      exact varsOf_existsAll_binder _
        (List.mem_map_of_mem (f := fun i => ((canonVars c r.vars).getD i default).kore) hx)
    · exact varsOf_existsAll_binder _
        (List.mem_map_of_mem (f := fun i => ((canonVars c r.vars).getD i default).kore) ((hfixed i).mpr ⟨hi, hx⟩))
  have hkfQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tf :=
    fun k hk => by
      rw [← htf]
      unfold KoreAML.tableOf
      refine List.mem_eraseDups.mpr (List.mem_append_right _ (Model.varsOf_existsAll_bodyEx ?_ _))
      refine Model.varsOf_and_mem (List.mem_append_right _ (List.mem_singleton_self _)) ?_
      unfold Model.ruleRightBodyPP
      exact Model.varsOf_existsAll_bodyEx (Model.varsOf_condConj (fun φ hφ => List.mem_append_right _ hφ) hk) _
  let e₁ := overVEx c I tf r.vars fixed σ e
  let e₂ := copyVSplit c tbl tf r.vars e'' e₁
  have hne : ∀ (l : List Kore.Pattern) (p : Kore.Pattern), l ++ [p] ≠ [] := fun l p => by simp
  refine existsAll_intro_at hD _ e e₁ _ (binders_nodupEx hkf hfl (List.nodup_range.filter _)) (binders_sortEx hfl)
    (fun z hz => overVEx_off fun i hi hif he => hz _ (List.mem_map_of_mem hif) he) rfl
    (fun b' hb' n hn => ?_) ?_
  · obtain ⟨i, hif, rfl⟩ := List.mem_map.mp hb'
    have hi := hfl i hif
    rw [hsortB i hi] at hn
    rw [← srt_inj hn]
    show InS I _ (e₁.evalEvar (tf.ev (canonKey c r.vars i)))
    rw [overVEx_at hkf hi hif]
    exact hinσ i hi
  · rw [interp_and (hne _ _)]
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · unfold fixK at hp
      obtain ⟨i, hif, hpi⟩ := List.mem_filterMap.mp hp
      split at hpi
      · rename_i v s g hv hsi hg'
        cases hpi
        have hi : i < r.vars.length := (List.getElem?_eq_some_iff.mp hsi).1
        obtain ⟨w, hw, hsw⟩ := hσ i s hsi
        rw [hg'] at hw; cases hw
        refine (fixEq_iff hI (sortOf_numbered_of hs0 hsorts hov hsw) hsw _).mpr ⟨hinC tf e₁, ?_⟩
        have hvk : KoreAML.evarKey v.kore = canonKey c r.vars i := by
          unfold canonKey
          rw [List.getD_eq_getElem?_getD, hv, Option.getD_some]
        rw [hvk, overVEx_at hkf hi hif, hg', Option.getD_some]
      · cases hpi
    · rw [List.mem_singleton.mp hp]
      have hcp : ∀ i < r.vars.length,
          e''.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i)) = e₂.evalEvar (tf.ev (keyAt (canonVars c r.vars) i)) :=
        fun i hi => (copyVSplit_at hkf hi).symm
      refine existsAll_intro_at hD _ e₁ e₂ _ (binders_nodupEx hkf hlt hexnd) (binders_sortEx hlt) (fun z hz => ?_) rfl
        (fun b' hb' n hn => ?_) ?_
      · by_cases hk : ∃ i < r.vars.length, z = tf.ev (canonKey c r.vars i)
        · obtain ⟨i, hi, rfl⟩ := hk
          have hx : i ∉ r.exs := fun hx => hz _ (List.mem_map_of_mem hx) rfl
          rw [copyVSplit_at hkf hi, hoffE i hi hx, hval i hi hx,
            overVEx_at hkf hi ((hfixed i).mpr ⟨hi, hx⟩)]
        · exact copyVSplit_off fun i hi he => hk ⟨i, hi, he⟩
      · obtain ⟨i, hix, rfl⟩ := List.mem_map.mp hb'
        have hi := hlt i hix
        rw [hsortB i hi] at hn
        rw [← srt_inj hn]
        have := hin'' i hi
        rw [hcp i hi] at this
        exact this
      · have hAB : (KoreAML.tr ⟨tf, []⟩ (Model.ruleRightBody c r)).interpret I e₂ b := by
          unfold Model.ruleRightBody
          rw [tr_and2, KoreAML.interp_sAnd]
          refine ⟨(tr_kore_congr r.rhs (fun i hi => hcp i (varOccs_lt r.rhs hrhss i hi)) b).mp hyR, ?_⟩
          cases hq : r.ens with
          | none =>
            exact reqPat_holds hI (q := none) (vs := canonVars c r.vars) (fun t ht => by cases ht) (hinC tf e₂)
          | some t =>
            have h2 := hensR
            rw [hq] at h2
            exact (tr_reqPat_congr hI (fun i hi => hcp i (varOccs_lt t (hensS t hq) i hi)) b).mp h2
        unfold Model.ruleRightBody at hAB
        rw [tr_and2, KoreAML.interp_sAnd] at hAB
        unfold Model.ruleRightBodyPP
        rw [interp_and (by simp)]
        intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl
          · exact hAB.1
          · exact hAB.2
        · have hqm := hpostR q hq
          have hq' := Model.mem_condConj hq
          subst hq'
          exact (tr_condKore_twoT hD r.post hokQ (fun k hk => ⟨hkQ k hk, hkfQ k hk⟩)
            (fun i hi => ⟨hkeys i (varOccsCond_lt_twoT r.post hokQ i hi), hkf i (varOccsCond_lt_twoT r.post hokQ i hi),
              hcp i (varOccsCond_lt_twoT r.post hokQ i hi)⟩) b).mp hqm

/-- An element of a rule's right side is in the configuration sort, whatever its `post` (the `rhs`
conjunct only is read). -/
theorem ruleRight_sort_pp (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {r : Rule} (hs : c.ruleSorted r = true)
    {σ : Subst} (hσ : c.WellSorted r.vars σ) {tbl : VarTable}
    (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) {e' : Valuation M}
    (hval : ∀ i < r.vars.length, i ∉ r.exs →
      e'.evalEvar (tbl.ev (canonKey c r.vars i)) = elemOf c I ((σ.lookup i).getD default))
    {b : M} (hb : (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret I e' b) :
    InS I (c.sortName topCellSort) b := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  obtain ⟨-, -, -, -, hrhss, hexnd, hexs, -, -, -, -⟩ := Model.ruleSorted_partsPP hs
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  rw [Model.ruleRight_eqPP hlt] at hb
  obtain ⟨e'', hoff, hguard, hbody⟩ := existsAll_elim hD (Model.ruleExBinders c r) e' _
    (binders_nodupEx hkeys hlt hexnd) (binders_sortEx hlt) hb
  unfold Model.ruleRightBodyPP at hbody
  rw [interp_and (by simp)] at hbody
  have hyR := hbody (Term.kore c (canonVars c r.vars) r.rhs) (List.mem_append_left _ (List.mem_cons_self ..))
  have hin'' : ∀ i < r.vars.length,
      InS I (c.sortName (r.vars.getD i 0)) (e''.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))) := by
    intro i hi
    by_cases hx : i ∈ r.exs
    · exact hguard _ (List.mem_map_of_mem (f := fun i => ((canonVars c r.vars).getD i default).kore) hx) _
        (by rw [canonVars_getD c hi]; rfl)
    · show InS I _ (e''.evalEvar (tbl.ev (canonKey c r.vars i)))
      rw [hoff _ fun b hb he => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
        exact hx ((canonKey_inj hi (hlt j hj) (ev_inj (hkeys i hi) (hkeys j (hlt j hj)) he)) ▸ hj), hval i hi hx]
      obtain ⟨w, hw, hsw⟩ := hσ i (r.vars.getD i 0)
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
      rw [hw]
      exact (inS_iff e'').mp (elemOf_spec hI hsw e'').2
  exact rhsSort hI hg hsc.trans hnn.1 (canonVars_length c r.vars) hin'' fns_headsOK hrhss b hyR

/-- The right side of a rule is defined where an element is in it, whatever its `post`
(`ruleRight_sort_pp`). -/
theorem ceil_right_pp (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {r : Rule} (hs : c.ruleSorted r = true)
    {σ : Subst} (hσ : c.WellSorted r.vars σ) {tbl : VarTable}
    (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) {e' : Valuation M}
    (hval : ∀ i < r.vars.length, i ∉ r.exs →
      e'.evalEvar (tbl.ev (canonKey c r.vars i)) = elemOf c I ((σ.lookup i).getD default))
    {b : M} (hb : (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret I e' b)
    {a : M} (ha : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e' a) :
    (KoreAML.tr ⟨tbl, []⟩ (.ceil (srtOf c topCellSort) (srtOf c topCellSort) (ruleRight c r))).interpret I e' a := by
  haveI : OvlOK c := (hypSound_of_core h).2.2.2.2.2.2.2.2
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hI (top_numbered (c := c))
  have hSC : ∀ b, (KoreAML.trSort tbl (srtOf c topCellSort)).interpret I e' b ↔ b = σC := by
    unfold srtOf; rw [trSort_srt]; exact hσC1
  have hφs : ∀ b', (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret I e' b' → KoreAML.Inh I σC b' := fun b' hb' =>
    (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσC1).mp
      ((inS_iff e').mpr (ruleRight_sort_pp h hI hs hσ hkeys hval hb'))
  rw [KoreAML.tr, KoreAML.interp_sCeil hD hc hSC hSC hσC2 hσC2 hφs]
  exact ⟨⟨b, hb⟩, (KoreAML.interp_inhOf_of hSC).mp ha⟩

/-- **x's element in a rule's `applies` gives a match of its left side at x**, for a rule with
`ruleSorted`, whatever its `pre` (the left side's conjunct only is read). -/
theorem applies_match_pp (h : c.coreOK = true) (hIΓ : I ⊧ᴵP Γ c) {r : Rule}
    (hs : c.ruleSorted r = true) {x : Config c}
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl) (e : Valuation M)
    (hm : (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x.val)) :
    ∃ σ', PatVal c σ' r.lhs x.val := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hIΓ
  obtain ⟨hlhs, -, -, -⟩ := Semantics.ruleSorted_parts c hs
  let vs := canonVars c r.vars
  let n := r.vars.length
  let C := srtOf c topCellSort
  let l := (List.range n).filter r.leftVars.contains
  have hl : ∀ i ∈ l, i < n := fun i hi => List.mem_range.mp (List.mem_filter.mp hi).1
  have hlm : ∀ i ∈ l, i ∈ r.leftVars := fun i hi => by simpa using (List.mem_filter.mp hi).2
  have hml : ∀ i < n, i ∈ r.leftVars → i ∈ l := fun i hi hil =>
    List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hil⟩
  rw [Model.applies_eqPP r] at hm
  have hnd : (((l.map (vs.getD · default)).map KoreAML.Var.kore).map fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
    rw [List.map_map, List.map_map]
    refine Model.nodup_map_of_injOn _ (fun i hi j hj he => ?_) (List.nodup_range.filter _)
    exact canonKey_inj (hl i hi) (hl j hj) (ev_inj (hkeys i (hl i hi) (hlm i hi)) (hkeys j (hl j hj) (hlm j hj)) he)
  have hsrt : ∀ b ∈ (l.map (vs.getD · default)).map KoreAML.Var.kore, ∃ n, b.sort = KoreAML.srt n := fun b hb => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    show ∃ n, ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt n
    rw [canonVars_getD c (hl i hi)]; exact ⟨_, rfl⟩
  obtain ⟨e', -, hguard, hbody⟩ := existsAll_elim hD _ e _ hnd hsrt hm
  obtain ⟨hlx, -, -⟩ := (interp_bodyPPI _ _ _ _ _ _).mp hbody
  have hinL : ∀ i < n, i ∈ r.leftVars → InS I (c.sortName (r.vars.getD i 0)) (e'.evalEvar (tbl.ev (keyAt vs i))) :=
    fun i hi hil => hguard _ (List.mem_map_of_mem (List.mem_map_of_mem (hml i hi hil))) _
      (by show (vs.getD i default).kore.sort = _; rw [canonVars_getD c hi]; rfl)
  let e1 := fillV c tbl r.vars r.leftVars (elemOf c I x.val) e'
  have hoff1 : ∀ i < n, i ∈ r.leftVars → e1.evalEvar (tbl.ev (keyAt vs i)) = e'.evalEvar (tbl.ev (keyAt vs i)) :=
    fun i hi hil => fillV_off hkeys hi hil
  have hvsl : vs.length = r.leftSorts.length := by rw [canonVars_length, Rule.leftSorts_length]
  have hin1 : ∀ i < r.leftSorts.length, InS I (c.sortName (r.leftSorts.getD i 0)) (e1.evalEvar (tbl.ev (keyAt vs i))) :=
    fun i hi => by
      rw [Rule.leftSorts_length] at hi
      by_cases hil : i ∈ r.leftVars
      · rw [Rule.leftSorts_getD hi hil, hoff1 i hi hil]; exact hinL i hi hil
      · have hw : Witnessed c I tbl vs r.leftSorts e1 i :=
          ⟨x.val, by rw [Rule.leftSorts_getD_off hi hil]; exact x.property, (fillV_on hi hil).symm⟩
        obtain ⟨v, hv, he⟩ := hw
        rw [← he]; exact (inS_iff e1).mp (elemOf_spec hIΓ hv e1).2
  have hlhsL : ∀ i ∈ varOccs r.lhs, i ∈ r.leftVars := fun i hi => List.mem_append_left _ hi
  have hltL : ∀ i ∈ varOccs r.lhs, i < n := Exec.sortOfTerm_vars hlhs
  have hlx1 := (tr_kore_congr r.lhs (fun i hi => (hoff1 i (hltL i hi) (hlhsL i hi)).symm) _).mp hlx
  have hlhs' : sortOfTerm c.patCtxAll r.leftSorts r.lhs = some topCellSort := by
    rw [sortOfTerm_congr r.lhs fun i hi => Rule.leftSorts_getElem? (hltL i hi) (hlhsL i hi)]; exact hlhs
  have hlhsN' : sortOfTerm c.patCtxNF r.leftSorts r.lhs = some topCellSort := by
    rw [sortOfTerm_congr r.lhs fun i hi => Rule.leftSorts_getElem? (hltL i hi) (hlhsL i hi)]; exact Semantics.ruleSorted_lhs_nf c hs
  obtain ⟨hpv, -⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 hvsl hin1 (collPat_of_sorted hph' hlhs')
    hlhsN' x.property hlx1
  exact ⟨_, hpv⟩

end

end Faithful

open ML Faithful Faithful.Model

end KCore
