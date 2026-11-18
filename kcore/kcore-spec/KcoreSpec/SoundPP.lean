/-
  KCore. Soundness at a step by a rule with a `pre` and a `post`.

  `sound_at_pp` is `sound_at`'s statement from the per-rule facts `ruleSorted` and `rulePlainPP`
  (not `rulePlainEx`, so not from `\top` predicates): in every model of `Γc`, x has a successor among
  the instances of the application (`step_sound_pp`) and y is one of them (`famEx_mem_pp`).

  The rule's axiom is `\rewrites(lhs ∧ ⌈req⌉ ∧ pre ∧ ¬ ⋁ applies ∧ ⌈right⌉, right)`, `right` the
  pattern `∃ē. (rhs ∧ ⌈ens⌉ ∧ post)`. `StepBy` gives `Holds … pre true` and `Holds … post true` at
  σ, and in a model of `Γc` a condition's patterns hold at an element of the configuration sort
  where its truth value is `true` (`holds_entails`). A competitor that does not apply holds x's
  element in no `applies` (`not_applies_of_notApplies_pp`); its conditions are asked decided only
  where its left side matches x, and x's element in `applies` gives such a match
  (`applies_match_pp`, `not_applies_guarded_pp`). No hypothesis that a predicate or a `requires` is
  decided, and no `FnTerminates`.
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

/-- **The successor of a step is among its instances**, in a model of `Γc`, for a rule with
`ruleSorted` and any `post`: y's element is in `famEx c r σ` where the right side evaluates to y,
the `ensures` to `true` and `Holds … post true` at σ (`post` by `holds_entails`). -/
theorem famEx_mem_pp (h : c.coreOK = true) {r : Rule} (hs : c.ruleSorted r = true)
    (hrcQ : hasBinder r.post = true → c.readsConfined = true) {σ : Subst} (hσ : c.WellSorted r.vars σ) {y : Config c}
    (heval : EvalTerm c σ r.rhs (some y.val)) (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hpost : Holds c r.vars.length σ r.post true)
    (hIc : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) (e : Valuation M) :
    (famEx c r σ).interpret I e (elemOf c I y.val) := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have hs0 := hypSound_of_core h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := id hs0
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  have hneg := (neg_of_coreCl hIc (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw)
  obtain ⟨-, -, -, hensS, hrhss, hexnd, hexs, -, hokQ, -, hbdQ⟩ := Model.ruleSorted_partsPP hs
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  have hsorts := sortsNumbered_of_core h
  have hov := Semantics.coreOK_ovls h
  let vs := canonVars c r.vars
  let fixed := (List.range r.vars.length).filter fun i => !r.exs.contains i
  have hfixed : ∀ i, i ∈ fixed ↔ i < r.vars.length ∧ i ∉ r.exs := fun i => by simp [fixed]
  rw [famEx_eqPPx hlt]
  unfold KoreAML.denB
  generalize htbl : KoreAML.tableOf [] _ = tbl
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := by
    intro i hi
    rw [← htbl]
    unfold KoreAML.tableOf
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    by_cases hx : i ∈ r.exs
    · refine Model.varsOf_existsAll_bodyEx ?_ _
      refine Model.varsOf_and_mem (List.mem_append_right _ (List.mem_singleton_self _)) ?_
      exact varsOf_existsAll_binder _ (List.mem_map_of_mem (f := fun i => (vs.getD i default).kore) hx)
    · exact varsOf_existsAll_binder _
        (List.mem_map_of_mem (f := fun i => (vs.getD i default).kore) ((hfixed i).mpr ⟨hi, hx⟩))
  have hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl :=
    fun k hk => by
      rw [← htbl]
      unfold KoreAML.tableOf
      refine List.mem_eraseDups.mpr (List.mem_append_right _ (Model.varsOf_existsAll_bodyEx ?_ _))
      refine Model.varsOf_and_mem (List.mem_append_right _ (List.mem_singleton_self _)) ?_
      unfold Model.ruleRightBodyPP
      exact Model.varsOf_existsAll_bodyEx (Model.varsOf_condConj (fun φ hφ => List.mem_append_right _ hφ) hk) _
  have hsortB : ∀ i < r.vars.length,
      (vs.getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := fun i hi => by
    show ((canonVars c r.vars).getD i default).kore.sort = _
    rw [canonVars_getD c hi]; rfl
  have hinjB : ∀ {l : List Nat}, (∀ i ∈ l, i < r.vars.length) → l.Nodup →
      ((l.map fun i => (vs.getD i default).kore).map fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
    intro l hl hnd
    rw [List.map_map]
    refine List.pairwise_map.mpr (hnd.imp_of_mem fun {i j} hi hj hne he => hne ?_)
    exact canonKey_inj (hl i hi) (hl j hj) (ev_inj (hkeys i (hl i hi)) (hkeys j (hl j hj)) he)
  have hbinders : ∀ {l : List Nat}, (∀ i ∈ l, i < r.vars.length) →
      ∀ b ∈ l.map (fun i => (vs.getD i default).kore), ∃ n, b.sort = KoreAML.srt n := fun hl b hb => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb; exact ⟨_, hsortB i (hl i hi)⟩
  -- the element of a variable's value is in its sort
  have hinσ : ∀ i < r.vars.length, ∀ e₁ : Valuation M,
      InS I (c.sortName (r.vars.getD i 0)) (elemOf c I ((σ.lookup i).getD default)) := by
    intro i hi e₁
    obtain ⟨w, hw, hsw⟩ := hσ i (r.vars.getD i 0)
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
    rw [hw]
    exact (inS_iff e₁).mp (elemOf_spec hI hsw e₁).2
  have hne : ∀ (l : List Kore.Pattern) (p : Kore.Pattern), l ++ [p] ≠ [] := fun l p => by simp
  have hfl : ∀ i ∈ fixed, i < r.vars.length := fun i hi => ((hfixed i).mp hi).1
  let e₁ := overVEx c I tbl r.vars fixed σ e
  let e₂ := overV c I tbl r.vars σ e₁
  have hag₂ := overV_agrees hI hkeys hσ (e := e₁)
  refine existsAll_intro_at hD _ e e₁ _ (hinjB hfl (List.nodup_range.filter _)) (hbinders hfl)
    (fun z hz => overVEx_off fun i hi hif he => hz _ (List.mem_map_of_mem hif) he) rfl
    (fun b hb n hn => ?_) ?_
  · obtain ⟨i, hif, rfl⟩ := List.mem_map.mp hb
    have hi := hfl i hif
    rw [hsortB i hi] at hn
    rw [← srt_inj hn]
    show InS I _ (e₁.evalEvar (tbl.ev (canonKey c r.vars i)))
    rw [overVEx_at hkeys hi hif]
    exact hinσ i hi e₁
  · have hinC : ∀ e' : Valuation M, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e'
        (elemOf c I y.val) := fun e' => elemOf_top hI y tbl e'
    rw [interp_and (hne _ _)]
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · -- the variables other than the existential ones are fixed to their values
      unfold fixK at hp
      obtain ⟨i, hif, hpi⟩ := List.mem_filterMap.mp hp
      split at hpi
      · rename_i v s g hv hsi hg'
        cases hpi
        have hi : i < r.vars.length := (List.getElem?_eq_some_iff.mp hsi).1
        obtain ⟨w, hw, hsw⟩ := hσ i s hsi
        rw [hg'] at hw; cases hw
        refine (fixEq_iff hI (sortOf_numbered_of hs0 hsorts hov hsw) hsw _).mpr ⟨hinC e₁, ?_⟩
        have hvk : KoreAML.evarKey v.kore = canonKey c r.vars i := by
          unfold canonKey
          rw [List.getD_eq_getElem?_getD, hv, Option.getD_some]
        rw [hvk, overVEx_at hkeys hi hif, hg', Option.getD_some]
      · cases hpi
    · -- inside `∃ē`, the existential variables at their values
      rw [List.mem_singleton.mp hp]
      refine existsAll_intro_at hD _ e₁ e₂ _ (hinjB hlt hexnd) (hbinders hlt) (fun z hz => ?_) rfl
        (fun b hb n hn => ?_) ?_
      · by_cases hk : ∃ i < r.vars.length, z = tbl.ev (canonKey c r.vars i)
        · obtain ⟨i, hi, rfl⟩ := hk
          have hx : i ∉ r.exs := fun hx => hz _ (List.mem_map_of_mem hx) rfl
          show (overV c I tbl r.vars σ e₁).evalEvar (tbl.ev (canonKey c r.vars i)) = _
          rw [overV_at hkeys hi, overVEx_at hkeys hi ((hfixed i).mpr ⟨hi, hx⟩)]
        · exact overV_off fun i hi he => hk ⟨i, hi, he⟩
      · obtain ⟨i, hix, rfl⟩ := List.mem_map.mp hb
        have hi := hlt i hix
        rw [hsortB i hi] at hn
        rw [← srt_inj hn]
        show InS I _ (e₂.evalEvar (tbl.ev (canonKey c r.vars i)))
        rw [overV_at hkeys hi]
        exact hinσ i hi e₂
      · have hAB : (KoreAML.tr ⟨tbl, []⟩ (Model.ruleRightBody c r)).interpret I e₂ (elemOf c I y.val) := by
          unfold Model.ruleRightBody
          rw [tr_and2, KoreAML.interp_sAnd]
          refine ⟨(evalTerm_den4Cl hI hnn hsc hph (clauseOpenFacts_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok))
            hneg heval fns_headsOK hσ (canonVars_length c r.vars) hag₂ hrhss _).mpr
              ((elemOf_spec hI y.property e₂).1 _ |>.mpr rfl), reqPat_holds hI (fun t ht b =>
              evalTerm_den4Cl hI hnn hsc hph (clauseOpenFacts_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok))
                hneg (hens t ht) fns_headsOK hσ (canonVars_length c r.vars) hag₂ (hensS t ht) b) (hinC e₂)⟩
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
        · have hq' := Model.mem_condConj hq
          subst hq'
          have hr := reads_of_agrees hσ hag₂ (P := fun i => i ∈ varOccsCond r.vars.length r.post)
            fun i hi => ⟨varOccsCond_lt_twoT r.post hokQ i hi, hkeys i (varOccsCond_lt_twoT r.post hokQ i hi)⟩
          exact (HoldsShape.holds_entails h hIc hcw r.post hrcQ hokQ hbdQ (fun i hi _ => hi) hr hkQ top_numbered
            hpost _ (hinC e₂)).mpr rfl

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

/-- **The successor's element is in the rule's right side**, for a rule with any `post`: at a
valuation that agrees with σ, where the right side evaluates to y, the `ensures` to `true` and
`Holds … post true` (`post` by `holds_entails`; a binder in it asks `readsConfined`, and the table
holds its keys). -/
theorem ruleRight_at_pp (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hrcQ : hasBinder r.post = true → c.readsConfined = true) {σ : Subst} (hσ : c.WellSorted r.vars σ)
    {y : Config c} (heval : EvalTerm c σ r.rhs (some y.val))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hpost : Holds c r.vars.length σ r.post true) {tbl : VarTable}
    (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl)
    (hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl)
    {e' : Valuation M}
    (hval : ∀ i < r.vars.length, e'.evalEvar (tbl.ev (canonKey c r.vars i)) = elemOf c I ((σ.lookup i).getD default))
    (hag : Agrees c I tbl (canonVars c r.vars) σ e') :
    (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret I e' (elemOf c I y.val) := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  have hneg := (neg_of_coreCl hIc (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw)
  obtain ⟨-, -, -, hensS, hrhss, hexnd, hexs, -, hokQ, -, hbdQ⟩ := Model.ruleSorted_partsPP hs
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  rw [Model.ruleRight_eqPP hlt]
  refine existsAll_intro_at hD _ e' e' _ (binders_nodupEx hkeys hlt hexnd) (binders_sortEx hlt)
    (fun _ _ => rfl) rfl (fun b hb n hn => ?_) ?_
  · obtain ⟨i, hix, rfl⟩ := List.mem_map.mp hb
    have hi := hlt i hix
    have hs' : ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
      rw [canonVars_getD c hi]; rfl
    rw [hs'] at hn
    rw [← srt_inj hn]
    show InS I _ (e'.evalEvar (tbl.ev (canonKey c r.vars i)))
    rw [hval i hi]
    obtain ⟨w, hw, hsw⟩ := hσ i (r.vars.getD i 0)
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
    rw [hw]
    exact (inS_iff e').mp (elemOf_spec hI hsw e').2
  · have hAB : (KoreAML.tr ⟨tbl, []⟩ (Model.ruleRightBody c r)).interpret I e' (elemOf c I y.val) := by
      unfold Model.ruleRightBody
      rw [tr_and2, KoreAML.interp_sAnd]
      exact ⟨(evalTerm_den4Cl hI hnn hsc hph (clauseOpenFacts_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok))
        hneg heval fns_headsOK hσ (canonVars_length c r.vars) hag hrhss _).mpr
          ((elemOf_spec hI y.property e').1 _ |>.mpr rfl), reqPat_holds hI (fun t ht b =>
          evalTerm_den4Cl hI hnn hsc hph (clauseOpenFacts_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok))
            hneg (hens t ht) fns_headsOK hσ (canonVars_length c r.vars) hag (hensS t ht) b) (elemOf_top hI y tbl e')⟩
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
    · have hq' := Model.mem_condConj hq
      subst hq'
      have hr := reads_of_agrees hσ hag (P := fun i => i ∈ varOccsCond r.vars.length r.post)
        fun i hi => ⟨varOccsCond_lt_twoT r.post hokQ i hi, hkeys i (varOccsCond_lt_twoT r.post hokQ i hi)⟩
      exact (HoldsShape.holds_entails h hIc hcw r.post hrcQ hokQ hbdQ (fun i hi _ => hi) hr hkQ top_numbered
        hpost _ (elemOf_top hI y tbl e')).mpr rfl

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
  obtain ⟨hpv, -⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 hvsl hin1 (collPat_of_sorted hph' hlhs')
    (Semantics.lhs_nf OvlOK.ok hr hlhs') x.property hlx1
  exact ⟨_, hpv⟩

/-- **A competitor that does not apply at x holds x's element in no `applies`**, for a competitor
with a `pre`: `not_applies_of_notApplies_pp` with `hw` asking decided conditions only where the
left side matches x (`applies_match_pp`), as `sound_at`'s `hw` gives them. -/
theorem not_applies_guarded_pp (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainPP r = true)
    (hlarger : c.rules.any (fun r'' => r.prio < r''.prio) = true)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true)
    {x : Config c} (hw : r.needsWitness c = true → (∃ σ', PatVal c σ' r.lhs x.val) → r.CondDecided c)
    (hna : NotApplies c r x.val)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (e : Valuation M) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x.val) := fun hm =>
  not_applies_of_notApplies_pp h hI hcw hs hp hlarger hrc hrcP
    (fun hn => hw hn (applies_match_pp h (fun φ hφ => hI φ (Or.inl hφ)) hs hkeys e hm)) hna hkeys hkP e hm

/-- **A step has a successor among its instances**, in a model of `Γc` that holds the rule's axiom,
for a rule with a `pre` and a `post`: x's element is in the axiom's left part (the left side,
`⌈req = true⌉`, `pre` by `holds_entails` at `hpre`, no competitor's `applies` by
`not_applies_guarded_pp`, the right side defined by `ruleRight_at_pp` and `ceil_right_pp`), so an
element after it is in the right side, and in `famEx c r σ` (`famEx_of_right_pp`). A binder in
`pre` or `post` asks `readsConfined`. The rule's own `rulePlainPP` is not read; the competitors'
is, through `hrules`. -/
theorem step_sound_pp (h : c.coreOK = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainPP r = true)
    (hIc : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (_hp : c.rulePlainPP r = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true)
    (hrcQ : hasBinder r.post = true → c.readsConfined = true)
    (hax : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", { sortVars := [], pattern := prioRuleK c r, attributes := [] }⟩).pat)
    (hlarger : ∀ r' ∈ c.rules, r'.prio < r.prio → c.rules.any (fun r'' => r'.prio < r''.prio) = true)
    {σ : Subst} {x y : Config c} (hσ : c.WellSorted r.vars σ) (hmatch : PatVal c σ r.lhs x.val)
    (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c r.vars.length σ r.pre true)
    (heval : EvalTerm c σ r.rhs (some y.val))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hpost : Holds c r.vars.length σ r.post true)
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val)
    (hw : ∀ r' ∈ c.rules, r'.prio < r.prio → r'.needsWitness c = true →
      (∃ σ', PatVal c σ' r'.lhs x.val) → r'.CondDecided c)
    (e : Valuation M) (m : M) (hm : (den c x.val).interpret I e m) :
    (KoreAML.sNext (famEx c r σ)).interpret I e m := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hneg := (neg_of_coreCl hIc (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw)
  have hD := defOK hIΓ
  obtain ⟨hlhs, hocc, hreqs, -, -, -, -, hokP, hokQ, hbdP, hbdQ⟩ := Model.ruleSorted_partsPP hs
  obtain ⟨-, hRv⟩ := Model.ruleRight_keysPP hs
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  let left : List Kore.Pattern := [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs))] ++
    Cond.conj c vs C r.pre
  have hcomp : ∀ r' ∈ c.rules, r'.prio < r.prio → applies c r' (canonRulePres r') ∈ comps := fun r' hr' hlt =>
    List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', by simpa using hlt⟩, rfl⟩
  -- the left side and the `requires` at x's element, under a valuation that agrees with σ
  have hlr : ∀ (tbl : VarTable) (e' : Valuation M), Agrees c I tbl vs σ e' →
      (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs r.lhs)).interpret I e' (elemOf c I x.val) ∧
      (KoreAML.tr ⟨tbl, []⟩ (reqPat C (r.req.map (Term.kore c vs)))).interpret I e' (elemOf c I x.val) :=
    fun tbl e' hag =>
      ⟨(patVal_den4 hIΓ hnn.1 hph hsc.trans hσ (canonVars_length c r.vars) hag hmatch (Semantics.lhs_nf OvlOK.ok hr hlhs)).2 _ |>.mpr
        ((elemOf_spec hIΓ x.property e').1 _ |>.mpr rfl),
       reqPat_holds hIΓ (fun t ht b => evalTerm_den4Cl hIΓ hnn hsc hph
        (clauseOpenFacts_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) hneg (hreq t ht) fns_headsOK hσ
        (canonVars_length c r.vars) hag (hreqs t ht) b) (elemOf_top hIΓ x tbl e')⟩
  -- `pre` at x's element: it holds at σ (`holds_entails`)
  have hpreL : ∀ (tbl : VarTable) (e' : Valuation M), (∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) →
      (∀ k ∈ KoreAML.varsOf (Cond.kore c vs C r.pre), k ∈ tbl) → Agrees c I tbl vs σ e' →
      ∀ φ ∈ Cond.conj c vs C r.pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e' (elemOf c I x.val) := by
    intro tbl e' hkeys hkP hag φ hφ
    have hφ' := Model.mem_condConj hφ
    subst hφ'
    have hr := reads_of_agrees hσ hag (P := fun i => i ∈ varOccsCond r.vars.length r.pre)
      fun i hi => ⟨varOccsCond_lt_twoT r.pre hokP i hi, hkeys i (varOccsCond_lt_twoT r.pre hokP i hi)⟩
    exact (HoldsShape.holds_entails h hIc hcw r.pre hrcP hokP hbdP (fun i hi _ => hi) hr hkP top_numbered
      hpre _ (elemOf_top hIΓ x tbl e')).mpr rfl
  have hceilK : ∀ {k : KoreAML.VarKey}, k ∈ KoreAML.varsOf (ruleRight c r) →
      k ∈ KoreAML.varsOf (.ceil C C (ruleRight c r)) := fun hk => by
    rw [KoreAML.varsOf]; exact List.mem_append_right _ hk
  -- every variable of the rule, and every key of `pre`, is a variable of the left part
  have hkeysL : ∀ {ps : List Kore.Pattern}, (∀ q ∈ left, q ∈ ps) → .ceil C C (ruleRight c r) ∈ ps →
      (∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.varsOf (.and C ps)) ∧
      (∀ k ∈ KoreAML.varsOf (Cond.kore c vs C r.pre), k ∈ KoreAML.varsOf (.and C ps)) := by
    intro ps hsub h3
    have h1 : Term.kore c vs r.lhs ∈ ps := hsub _ (by simp [left])
    have h2 : reqPat C (r.req.map (Term.kore c vs)) ∈ ps := hsub _ (by simp [left])
    have hP : ∀ φ ∈ Cond.conj c vs C r.pre, φ ∈ ps := fun φ hφ => hsub _ (List.mem_append_right _ hφ)
    refine ⟨fun i hi => ?_, fun k hk => Model.varsOf_condConj hP hk⟩
    rcases hocc i hi with hL | ⟨t, ht, hit⟩ | hPr | hR | ⟨t, ht, hit⟩ | hPo
    · exact Model.varsOf_and_mem h1 (varsOf_kore c vs r.lhs hL)
    · rw [ht] at h2
      refine Model.varsOf_and_mem h2 ?_
      simp only [Option.map_some, reqPat]
      rw [KoreAML.varsOf]
      exact List.mem_append_left _ (List.mem_append_right _ (varsOf_kore c vs t hit))
    · exact Model.varsOf_condConj hP (Model.condKore_keys C r.pre (bound := []) hi hPr (by simp)).2
    · exact Model.varsOf_and_mem h3 (hceilK (hRv i hi (Or.inr (Or.inl hR))))
    · exact Model.varsOf_and_mem h3 (hceilK (hRv i hi (Or.inr (Or.inr (Or.inl ⟨t, ht, hit⟩)))))
    · exact Model.varsOf_and_mem h3 (hceilK (hRv i hi (Or.inr (Or.inr (Or.inr hPo)))))
  -- the axiom: `\rewrites(L, ∃ē. (rhs ∧ ens ∧ post))`, L read at x's element
  obtain ⟨L, hpat, hLv, hLP, hLread⟩ : ∃ L, prioRuleK c r = .rewrites C L (ruleRight c r) ∧
      (∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.varsOf L) ∧
      (∀ k ∈ KoreAML.varsOf (Cond.kore c vs C r.pre), k ∈ KoreAML.varsOf L) ∧
      ∀ (tbl : VarTable) (e' : Valuation M), (∀ k ∈ KoreAML.varsOf L, k ∈ tbl) → Agrees c I tbl vs σ e' →
        (∀ φ ∈ Cond.conj c vs C r.pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e' (elemOf c I x.val)) →
        (KoreAML.tr ⟨tbl, []⟩ (.ceil C C (ruleRight c r))).interpret I e' (elemOf c I x.val) →
        (KoreAML.tr ⟨tbl, []⟩ L).interpret I e' (elemOf c I x.val) := by
    by_cases hce : comps.isEmpty
    · obtain ⟨hk1, hk3⟩ := hkeysL (ps := left ++ [.ceil C C (ruleRight c r)])
        (fun q hq => List.mem_append_left _ hq) (by simp)
      refine ⟨_, by unfold prioRuleK; dsimp only; rw [if_pos hce], hk1, hk3, fun tbl e' _ hag hpm hceil => ?_⟩
      rw [interp_and (by simp)]
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · rcases List.mem_append.mp hp with hp | hp
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · exact (hlr tbl e' hag).1
          · exact (hlr tbl e' hag).2
        · exact hpm p hp
      · rw [List.mem_singleton.mp hp]; exact hceil
    · have hnot : Kore.Pattern.not C (anyOfC C comps) ∈
          left ++ [.not C (anyOfC C comps), .ceil C C (ruleRight c r)] := by simp
      obtain ⟨hk1, hk3⟩ := hkeysL (ps := left ++ [.not C (anyOfC C comps), .ceil C C (ruleRight c r)])
        (fun q hq => List.mem_append_left _ hq) (by simp)
      refine ⟨_, by unfold prioRuleK; dsimp only; rw [if_neg hce], hk1, hk3, fun tbl e' hkL hag hpm hceil => ?_⟩
      rw [interp_and (List.ne_nil_of_mem hnot)]
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · rcases List.mem_append.mp hp with hp | hp
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · exact (hlr tbl e' hag).1
          · exact (hlr tbl e' hag).2
        · exact hpm p hp
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · rw [KoreAML.tr, KoreAML.interp_sNot]
          refine ⟨anyOfC_empty hD (by
            show (KoreAML.trSort tbl (KoreAML.srt (c.sortName topCellSort))).isFreeEvar KoreAML.topVar = false
            rw [trSort_srt]; rfl) comps (fun φ hφ => ?_), ?_⟩
          · -- a competitor with a `pre`: it does not apply in the model (`not_applies_guarded_pp`)
            obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hφ
            obtain ⟨hr'm, hlt⟩ := List.mem_filter.mp hr'
            have hlt' : r'.prio < r.prio := by simpa using hlt
            have hrc' : r'.opens.any (fun i => (r'.vars[i]?.map c.confined).getD false) = true →
                c.readsConfined = true := fun hany => by
              obtain ⟨i, hi, -⟩ := List.any_eq_true.mp hany
              simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
              exact Or.inl ⟨r', hr'm, by simp [List.ne_nil_of_mem hi]⟩
            have hvC : ∀ {k}, k ∈ KoreAML.varsOf (applies c r' (canonRulePres r')) → k ∈ tbl := fun hk =>
              hkL _ (Model.varsOf_and_mem hnot (by
                simp only [KoreAML.varsOf]
                exact List.mem_append_right _ (mem_varsOf_anyOfC (hcomp r' hr'm hlt') hk)))
            exact not_applies_guarded_pp h hIc hcw (hrules r' hr'm).1 (hrules r' hr'm).2 (hlarger r' hr'm hlt') hrc'
              (readsConfined_of_pre hr'm) (hw r' hr'm hlt') (hprio r' hr'm hlt')
              (fun i hi hil => hvC ((Model.varsOf_applies_pp r').1 i hi hil))
              (fun k hk => hvC ((Model.varsOf_applies_pp r').2 k hk)) e'
          · have hxs := elemOf_spec hIΓ x.property e'
            show (KoreAML.inhOf (KoreAML.trSort tbl (KoreAML.srt (c.sortName topCellSort)))).interpret I e' _
            rw [trSort_srt]
            exact hxs.2
        · exact hceil
  rw [hpat] at hax
  let ax : Kore.Axiom := { sortVars := [], pattern := .rewrites C L (ruleRight c r), attributes := [] }
  let tbl : VarTable := KoreAML.tableOf ax.sortVars ax.pattern
  have hvarsL : ∀ k ∈ KoreAML.varsOf L, k ∈ tbl := fun k hk => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    show k ∈ KoreAML.varsOf (.rewrites C L _)
    rw [KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ hk)
  have hvarsR : ∀ k ∈ KoreAML.varsOf (ruleRight c r), k ∈ tbl := fun k hk => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    show k ∈ KoreAML.varsOf (.rewrites C L _)
    rw [KoreAML.varsOf]
    exact List.mem_append_right _ hk
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => hvarsL _ (hLv i hi)
  have hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c vs C r.pre), k ∈ tbl := fun k hk => hvarsL _ (hLP k hk)
  have hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c vs C r.post), k ∈ tbl := fun k hk =>
    hvarsR _ (Model.varsOf_post_ruleRight hs hk)
  let e' := overV c I tbl r.vars σ (KoreAML.val0 : Valuation M)
  have hval : ∀ i < r.vars.length, e'.evalEvar (tbl.ev (canonKey c r.vars i)) =
      elemOf c I ((σ.lookup i).getD default) := fun i hi => overV_at hkeys hi
  have hag : Agrees c I tbl vs σ e' := overV_agrees hIΓ hkeys hσ
  -- the guards of the axiom's free variables hold at e'
  have hgd : ∀ k ∈ (ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] ax.pattern).eraseDups, ∀ m,
      (KoreAML.guardOf tbl k).interpret I e' m := by
    intro k hk m'
    have hk' : k ∈ KoreAML.freeOf [] ax.pattern := by simpa [ax] using List.mem_eraseDups.mp hk
    obtain ⟨i, hi, -, rfl⟩ := Model.freeOf_prio_pp (fun r' hr' => (hrules r' hr').1) hs (by rw [hpat]; exact hk')
    obtain ⟨w, hw, hsw⟩ := hσ i (r.vars.getD i 0)
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
    have hkk := canonKey_eq c hi
    rw [hkk, KoreAML.interp_guard_evar hD, trSort_srt, ← hkk, hval i hi, hw, Option.getD_some]
    exact (elemOf_spec hIΓ hsw e').2
  obtain ⟨a, ha, has⟩ := den_single hIΓ x.property e'
  have hxa : elemOf c I x.val = a := (ha _).mp ((elemOf_spec hIΓ x.property e').1 _ |>.mpr rfl)
  have hP := (KoreAML.trAxiom_at hD hax e' hgd a).mpr (by
    show (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e' a
    unfold srtOf; rw [trSort_srt]; exact has)
  have hP' : (KoreAML.tr ⟨tbl, []⟩ ax.pattern).interpret I e' a := hP
  change (KoreAML.tr ⟨tbl, []⟩ (.rewrites C L _)).interpret I e' a at hP'
  rw [KoreAML.tr] at hP'
  unfold KoreAML.sRewrites at hP'
  rw [KoreAML.interp_sImp] at hP'
  obtain ⟨-, himp⟩ := hP'
  have hyR := ruleRight_at_pp h hIc hcw hs hrcQ hσ heval hens hpost hkeys hkQ hval hag
  have hceil := ceil_right_pp h hIΓ hs hσ hkeys (fun i hi _ => hval i hi) hyR (elemOf_top hIΓ x tbl e')
  have hL' := himp (by rw [← hxa]; exact hLread tbl e' hvarsL hag (hpreL tbl e' hkeys hkP hag) hceil)
  obtain ⟨n, b, hn, hb, happ⟩ := KoreAML.interp_app.mp hL'
  have hbF := famEx_of_right_pp h hIc hs hσ hkeys hkQ (fun i hi _ => hval i hi) hb e
  have hma : m = a := (ha m).mp (((den_closed c x.val).interp e e' m).mp hm)
  rw [hma]
  exact KoreAML.interp_app.mpr ⟨n, b, hn, hbF, happ⟩

end

end Faithful

open ML Faithful Faithful.Model

/-- **Soundness at a step by a rule with a `pre` and a `post`**: `sound_at`'s statement from the
per-rule facts `ruleSorted` and `rulePlainPP`. The competitors of r whose left side matches x have
decided closed conditions. -/
theorem sound_at_pp (c : Semantics) (h : c.coreOK = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainPP r = true)
    (x y : Config c) (r : Rule) (σ : Subst) (hs : StepBy c r σ x y)
    (hw : ∀ r' ∈ c.rules, r'.prio < r.prio → r'.needsWitness c = true →
      (∃ σ', PatVal c σ' r'.lhs x.val) → r'.CondDecided c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    (Γc c ⊧ (den c x.val ⇒ KoreAML.sNext (famEx c r σ))) ∧ (Γc c ⊧ (den c y.val ⇒ famEx c r σ)) := by
  obtain ⟨hsr, hpr⟩ := hrules r hs.mem
  refine ⟨?_, ?_⟩
  · intro M _ I hI e m
    have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
    rw [interpret_impl]
    exact step_sound_pp h hrules hI hcw hsr hpr (readsConfined_of_pre hs.mem) (readsConfined_of_post hs.mem)
      (sat_rules hIΓ (Or.inl ⟨_, List.mem_map.mpr ⟨r, hs.mem, rfl⟩, rfl⟩))
      (fun r' _ hlt => List.any_eq_true.mpr ⟨r, hs.mem, by simpa using hlt⟩) hs.hσ hs.hmatch hs.hreq hs.hpre
      hs.heval hs.hens hs.hpost hs.hprio hw e m
  · intro M _ I hI e m
    have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
    rw [interpret_impl]
    intro hm
    rw [((elemOf_spec hIΓ y.property e).1 m).mp hm]
    exact famEx_mem_pp h hsr (readsConfined_of_post hs.mem) hs.hσ hs.heval hs.hens hs.hpost hI hcw e

end KCore
