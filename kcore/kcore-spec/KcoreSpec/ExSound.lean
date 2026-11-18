/-
  KCore. Soundness at a step by a rule with existential variables, in any model of `Γc c`.

  - `famEx_mem_ex`: a step's successor y is among the instances of its application: at the
    valuation that gives the variables other than the existential ones their values under σ, and
    inside `∃ē` the existential ones theirs, y's element is in `rhs ∧ ens`.
-/
import KcoreSpec.ExFamValues
import KcoreSpec.OpenSound

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (VarTable Inh)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

open Classical in
/-- The valuation that gives the canonical variables of `vars` listed in `is` the elements of
their values under σ, through `tbl`, and agrees with `e` elsewhere. -/
noncomputable def overVEx (c : Semantics) (I : Interpretation KoreAML.Sym M) (tbl : VarTable) (vars : List Srt)
    (is : List Nat) (σ : Subst) (e : Valuation M) : Valuation M :=
  ⟨fun x => if h : ∃ i < vars.length, i ∈ is ∧ x = tbl.ev (canonKey c vars i)
    then elemOf c I ((σ.lookup (Classical.choose h)).getD default) else e.evalEvar x, e.evalSvar⟩

theorem overVEx_at {tbl : VarTable} {vars : List Srt} {is : List Nat} {σ : Subst} {e : Valuation M}
    (hkeys : ∀ i < vars.length, canonKey c vars i ∈ tbl) {i : Nat} (hi : i < vars.length) (his : i ∈ is) :
    (overVEx c I tbl vars is σ e).evalEvar (tbl.ev (canonKey c vars i)) = elemOf c I ((σ.lookup i).getD default) := by
  have hex : ∃ j < vars.length, j ∈ is ∧ tbl.ev (canonKey c vars i) = tbl.ev (canonKey c vars j) :=
    ⟨i, hi, his, rfl⟩
  show (if h : _ then _ else _) = _
  rw [dif_pos hex]
  obtain ⟨hj, -, hje⟩ := Classical.choose_spec hex
  have e1 : Classical.choose hex = i := (canonKey_inj hi hj (ev_inj (hkeys i hi) (hkeys _ hj) hje)).symm
  rw [e1]

theorem overVEx_off {tbl : VarTable} {vars : List Srt} {is : List Nat} {σ : Subst} {e : Valuation M} {x : EVar}
    (hx : ∀ i < vars.length, i ∈ is → x ≠ tbl.ev (canonKey c vars i)) :
    (overVEx c I tbl vars is σ e).evalEvar x = e.evalEvar x := by
  show (if h : _ then _ else _) = _
  rw [dif_neg (fun ⟨i, hi, his, he⟩ => hx i hi his he)]

/-- **A step's successor is among the instances of its application**, in every model of `Γc`, for
a rule with `ruleSorted` and `rulePlainEx` (not asked to be one of the definition's), at a σ that
gives every variable a value, under which the right side evaluates to y and the `ensures` to
`true`. -/
theorem famEx_mem_ex (h : c.coreOK = true) {r : Rule} (hs : c.ruleSorted r = true)
    (hp : c.rulePlainEx r = true) {σ : Subst} (hσ : c.WellSorted r.vars σ) {y : Config c}
    (heval : EvalTerm c σ r.rhs (some y.val)) (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
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
  obtain ⟨-, -, -, hensS, hrhss, hexnd, hexs⟩ := Model.ruleSorted_partsEx hs hp
  obtain ⟨-, hpost₀⟩ := Semantics.rulePlainEx_top hp
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  have hsorts := sortsNumbered_of_core h
  have hov := Semantics.coreOK_ovls h
  let vs := canonVars c r.vars
  let fixed := (List.range r.vars.length).filter fun i => !r.exs.contains i
  have hfixed : ∀ i, i ∈ fixed ↔ i < r.vars.length ∧ i ∉ r.exs := fun i => by simp [fixed]
  rw [famEx_eqEx hpost₀ hlt]
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
      · unfold Model.ruleRightBody
        rw [tr_and2, KoreAML.interp_sAnd]
        refine ⟨(evalTerm_den4Cl hI hnn hsc hph (clauseOpenFacts_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok))
          hneg heval fns_headsOK hσ (canonVars_length c r.vars) hag₂ hrhss _).mpr
            ((elemOf_spec hI y.property e₂).1 _ |>.mpr rfl), reqPat_holds hI (fun t ht b =>
            evalTerm_den4Cl hI hnn hsc hph (clauseOpenFacts_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok))
              hneg (hens t ht) fns_headsOK hσ (canonVars_length c r.vars) hag₂ (hensS t ht) b) (hinC e₂)⟩


/-- The binders of the canonical variables listed in l, at their indices in a table holding their
keys: one index each. -/
theorem binders_nodupEx {vars : List Srt} {tbl : VarTable} (hkeys : ∀ i < vars.length, canonKey c vars i ∈ tbl)
    {l : List Nat} (hl : ∀ i ∈ l, i < vars.length) (hnd : l.Nodup) :
    ((l.map fun i => ((canonVars c vars).getD i default).kore).map fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
  rw [List.map_map]
  refine List.pairwise_map.mpr (hnd.imp_of_mem fun {i j} hi hj hne he => hne ?_)
  exact canonKey_inj (hl i hi) (hl j hj) (ev_inj (hkeys i (hl i hi)) (hkeys j (hl j hj)) he)

theorem binders_sortEx {vars : List Srt} {l : List Nat} (hl : ∀ i ∈ l, i < vars.length) :
    ∀ b ∈ l.map (fun i => ((canonVars c vars).getD i default).kore), ∃ n, b.sort = KoreAML.srt n := fun b hb => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  rw [canonVars_getD c (hl i hi)]; exact ⟨_, rfl⟩

/-- Every variable of a rule has its key in the table of `famEx`'s pattern. -/
theorem famEx_keysEx {r : Rule} {σ : Subst} :
    ∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.tableOf [] (KoreAML.existsAll (srtOf c topCellSort)
      (((List.range r.vars.length).filter fun i => !r.exs.contains i).map
        fun i => ((canonVars c r.vars).getD i default).kore)
      (.and (srtOf c topCellSort) (fixK c r σ ((List.range r.vars.length).filter fun i => !r.exs.contains i) ++
        [KoreAML.existsAll (srtOf c topCellSort) (Model.ruleExBinders c r) (Model.ruleRightBody c r)]))) := by
  intro i hi
  unfold KoreAML.tableOf
  refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
  by_cases hx : i ∈ r.exs
  · refine Model.varsOf_existsAll_bodyEx ?_ _
    refine Model.varsOf_and_mem (List.mem_append_right _ (List.mem_singleton_self _)) ?_
    exact varsOf_existsAll_binder _ (List.mem_map_of_mem (f := fun i => ((canonVars c r.vars).getD i default).kore) hx)
  · exact varsOf_existsAll_binder _ (List.mem_map_of_mem (f := fun i => ((canonVars c r.vars).getD i default).kore)
      (List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hx⟩))

/-- **An element of a rule's right side, at a valuation that gives the variables other than the
existential ones their values under σ, is among the instances of the application**, in a model of
`Γc`, for a rule with `ruleSorted` and `rulePlainEx` (not asked to be one of the definition's): the
right side read through any table holding the rule's keys. -/
theorem famEx_of_right_ex (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c) {r : Rule} (hs : c.ruleSorted r = true)
    (hp : c.rulePlainEx r = true) {σ : Subst} (hσ : c.WellSorted r.vars σ) {tbl : VarTable}
    (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) {e' : Valuation M}
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
  obtain ⟨-, -, -, hensS, hrhss, hexnd, hexs⟩ := Model.ruleSorted_partsEx hs hp
  obtain ⟨-, hpost₀⟩ := Semantics.rulePlainEx_top hp
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
  rw [Model.ruleRight_eqEx hpost₀ hlt] at hb
  obtain ⟨e'', hoff, hguard, hbody⟩ := existsAll_elim hD (Model.ruleExBinders c r) e' _
    (binders_nodupEx hkeys hlt hexnd) (binders_sortEx hlt) hb
  unfold Model.ruleRightBody at hbody
  rw [tr_and2, KoreAML.interp_sAnd] at hbody
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
    rhsSort hI hg hsc.trans hnn.1 (canonVars_length c r.vars) hin'' fns_headsOK hrhss b hbody.1
  have hinC : ∀ (tb : VarTable) (e₀ : Valuation M),
      (KoreAML.inhOf (KoreAML.trSort tb (srtOf c topCellSort))).interpret I e₀ b := fun tb e₀ => by
    unfold srtOf; rw [trSort_srt]; exact (inS_iff e₀).mpr hbC
  -- `famEx`'s pattern
  rw [famEx_eqEx hpost₀ hlt]
  unfold KoreAML.denB
  have hkf := famEx_keysEx (c := c) (r := r) (σ := σ)
  generalize KoreAML.tableOf [] _ = tf at hkf ⊢
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
      · unfold Model.ruleRightBody
        rw [tr_and2, KoreAML.interp_sAnd]
        refine ⟨(tr_kore_congr r.rhs (fun i hi => hcp i (varOccs_lt r.rhs hrhss i hi)) b).mp hbody.1, ?_⟩
        cases hq : r.ens with
        | none =>
          exact reqPat_holds hI (q := none) (vs := canonVars c r.vars) (fun t ht => by cases ht) (hinC tf e₂)
        | some t =>
          have h2 := hbody.2
          rw [hq] at h2
          exact (tr_reqPat_congr hI (fun i hi => hcp i (varOccs_lt t (hensS t hq) i hi)) b).mp h2

/-- **The elements of a rule's right side are in the configuration sort**, at a valuation that
gives the variables other than the existential ones their values under σ, in a model of `Γ`. -/
theorem ruleRight_sort_ex (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {r : Rule} (hs : c.ruleSorted r = true)
    (hp : c.rulePlainEx r = true) {σ : Subst} (hσ : c.WellSorted r.vars σ) {tbl : VarTable}
    (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) {e' : Valuation M}
    (hval : ∀ i < r.vars.length, i ∉ r.exs →
      e'.evalEvar (tbl.ev (canonKey c r.vars i)) = elemOf c I ((σ.lookup i).getD default))
    {b : M} (hb : (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret I e' b) :
    InS I (c.sortName topCellSort) b := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  obtain ⟨-, -, -, -, hrhss, hexnd, hexs⟩ := Model.ruleSorted_partsEx hs hp
  obtain ⟨-, hpost₀⟩ := Semantics.rulePlainEx_top hp
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  rw [Model.ruleRight_eqEx hpost₀ hlt] at hb
  obtain ⟨e'', hoff, hguard, hbody⟩ := existsAll_elim hD (Model.ruleExBinders c r) e' _
    (binders_nodupEx hkeys hlt hexnd) (binders_sortEx hlt) hb
  unfold Model.ruleRightBody at hbody
  rw [tr_and2, KoreAML.interp_sAnd] at hbody
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
  exact rhsSort hI hg hsc.trans hnn.1 (canonVars_length c r.vars) hin'' fns_headsOK hrhss b hbody.1

/-- **A step's successor is in the rule's right side**, at a valuation that agrees with σ on every
variable of the rule, in a model of `Γc`. -/
theorem ruleRight_at_ex (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainEx r = true) {σ : Subst} (hσ : c.WellSorted r.vars σ)
    {y : Config c} (heval : EvalTerm c σ r.rhs (some y.val))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) {tbl : VarTable}
    (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) {e' : Valuation M}
    (hval : ∀ i < r.vars.length, e'.evalEvar (tbl.ev (canonKey c r.vars i)) = elemOf c I ((σ.lookup i).getD default))
    (hag : Agrees c I tbl (canonVars c r.vars) σ e') :
    (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret I e' (elemOf c I y.val) := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  have hneg := (neg_of_coreCl hIc (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw)
  obtain ⟨-, -, -, hensS, hrhss, hexnd, hexs⟩ := Model.ruleSorted_partsEx hs hp
  obtain ⟨-, hpost₀⟩ := Semantics.rulePlainEx_top hp
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  rw [Model.ruleRight_eqEx hpost₀ hlt]
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
  · unfold Model.ruleRightBody
    rw [tr_and2, KoreAML.interp_sAnd]
    exact ⟨(evalTerm_den4Cl hI hnn hsc hph (clauseOpenFacts_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok))
      hneg heval fns_headsOK hσ (canonVars_length c r.vars) hag hrhss _).mpr
        ((elemOf_spec hI y.property e').1 _ |>.mpr rfl), reqPat_holds hI (fun t ht b =>
        evalTerm_den4Cl hI hnn hsc hph (clauseOpenFacts_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok))
          hneg (hens t ht) fns_headsOK hσ (canonVars_length c r.vars) hag (hensS t ht) b) (elemOf_top hI y tbl e')⟩

/-- **`⌈∃ē. (rhs ∧ ens)⌉` holds of every configuration's element** where the right side has an
element, at a valuation that gives the variables other than the existential ones their values. -/
theorem ceil_right_ex (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {r : Rule} (hs : c.ruleSorted r = true)
    (hp : c.rulePlainEx r = true) {σ : Subst} (hσ : c.WellSorted r.vars σ) {tbl : VarTable}
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
  have hφs : ∀ b', (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret I e' b' → Inh I σC b' := fun b' hb' =>
    (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσC1).mp
      ((inS_iff e').mpr (ruleRight_sort_ex h hI hs hp hσ hkeys hval hb'))
  rw [KoreAML.tr, KoreAML.interp_sCeil hD hc hSC hSC hσC2 hσC2 hφs]
  exact ⟨⟨b, hb⟩, (KoreAML.interp_inhOf_of hSC).mp ha⟩

/-- A rule with its existential variables read as ordinary ones. -/
def ruleDropExs (r : Rule) : Rule := { r with exs := [] }

/-- A well-sorted rule is well sorted with its existential variables read as ordinary ones. -/
theorem ruleSorted_dropExs {r : Rule} (hs : c.ruleSorted r = true) : c.ruleSorted (ruleDropExs r) = true := by
  simp only [Semantics.ruleSorted, Bool.and_eq_true] at hs ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := hs
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, rfl⟩, rfl⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩

/-- A rule that does not apply does not apply with its existential variables read as ordinary
ones: `NotApplies` reads the left side and the conditions only. -/
theorem notApplies_dropExs {r : Rule} {x : GroundTerm} (hna : NotApplies c r x) :
    NotApplies c (ruleDropExs r) x := fun σ hσ hm => by
  cases hna σ hσ hm with
  | intro ht he hv => exact .intro ht he hv
  | pre hb => exact .pre hb

/-- With its existential variables read as ordinary ones, a rule with `rulePlainEx` has
`rulePlainOpen`. -/
theorem rulePlainOpen_dropExs {r : Rule} (hp : c.rulePlainEx r = true) : c.rulePlainOpen (ruleDropExs r) = true :=
  Semantics.rulePlainOpen_iff_ex.mpr ⟨hp, rfl⟩


/-- **Step soundness at values, for a rule with existential variables.** For a rule r with
`ruleSorted` and `rulePlainEx` whose axiom a model of `Γc` satisfies (not asked to be one of the
definition's), in a definition whose rules have both, where each competitor of r has a rule of a
larger priority: at a σ with every premise of `StepBy c r σ x y` but the rule's membership, where
each competitor that matches x and needs a witness has decided conditions, x has a successor among
the instances of the application. The axiom gives one in `∃ē. (rhs ∧ ens)` at the valuation of σ,
and that is in `famEx c r σ` (`famEx_of_right_ex`). -/
theorem step_sound_ex (h : c.coreOK = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true)
    (hIc : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainEx r = true)
    (hax : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", { sortVars := [], pattern := prioRuleK c r, attributes := [] }⟩).pat)
    (hlarger : ∀ r' ∈ c.rules, r'.prio < r.prio → c.rules.any (fun r'' => r'.prio < r''.prio) = true)
    {σ : Subst} {x y : Config c} (hσ : c.WellSorted r.vars σ) (hmatch : PatVal c σ r.lhs x.val)
    (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) (heval : EvalTerm c σ r.rhs (some y.val))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
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
  obtain ⟨hlhs, hocc, hreqs, -, -, -, -⟩ := Model.ruleSorted_partsEx hs hp
  obtain ⟨hpre₀, -⟩ := Semantics.rulePlainEx_top hp
  obtain ⟨-, hRv⟩ := Model.ruleRight_keysEx hs hp
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  have hcomp : ∀ r' ∈ c.rules, r'.prio < r.prio → applies c r' (canonRulePres r') ∈ comps := fun r' hr' hlt =>
    List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', by simpa using hlt⟩, rfl⟩
  -- the left side and the `requires` at x's element, under a valuation that agrees with σ
  have hlr : ∀ (tbl : VarTable) (e' : Valuation M), Agrees c I tbl vs σ e' →
      (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs r.lhs)).interpret I e' (elemOf c I x.val) ∧
      (KoreAML.tr ⟨tbl, []⟩ (reqPat C (r.req.map (Term.kore c vs)))).interpret I e' (elemOf c I x.val) :=
    fun tbl e' hag =>
      ⟨(patVal_den4 hIΓ hnn.1 hph hsc.trans hσ (canonVars_length c r.vars) hag hmatch (OvlOK.nf_bridge inferInstance hlhs)).2 _ |>.mpr
        ((elemOf_spec hIΓ x.property e').1 _ |>.mpr rfl),
       reqPat_holds hIΓ (fun t ht b => evalTerm_den4Cl hIΓ hnn hsc hph
        (clauseOpenFacts_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) hneg (hreq t ht) fns_headsOK hσ
        (canonVars_length c r.vars) hag (hreqs t ht) b) (elemOf_top hIΓ x tbl e')⟩
  -- every variable of the rule is a variable of the left part
  have hkeysL : ∀ {ps : List Kore.Pattern}, Term.kore c vs r.lhs ∈ ps → reqPat C (r.req.map (Term.kore c vs)) ∈ ps →
      .ceil C C (ruleRight c r) ∈ ps → ∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.varsOf (.and C ps) := by
    intro ps h1 h2 h3 i hi
    have hceilK : ∀ {k : KoreAML.VarKey}, k ∈ KoreAML.varsOf (ruleRight c r) →
        k ∈ KoreAML.varsOf (.ceil C C (ruleRight c r)) := fun hk => by
      rw [KoreAML.varsOf]; exact List.mem_append_right _ hk
    rcases hocc i hi with hL | ⟨t, ht, hit⟩ | hR | ⟨t, ht, hit⟩
    · exact Model.varsOf_and_mem h1 (varsOf_kore c vs r.lhs hL)
    · rw [ht] at h2
      refine Model.varsOf_and_mem h2 ?_
      simp only [Option.map_some, reqPat]
      rw [KoreAML.varsOf]
      exact List.mem_append_left _ (List.mem_append_right _ (varsOf_kore c vs t hit))
    · exact Model.varsOf_and_mem h3 (hceilK (hRv i hi (Or.inr (Or.inl hR))))
    · exact Model.varsOf_and_mem h3 (hceilK (hRv i hi (Or.inr (Or.inr ⟨t, ht, hit⟩))))
  -- the axiom: `\rewrites(L, ∃ē. (rhs ∧ ens))`, L read at x's element
  obtain ⟨L, hpat, hLv, hLread⟩ : ∃ L, prioRuleK c r = .rewrites C L (ruleRight c r) ∧
      (∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.varsOf L) ∧
      ∀ (tbl : VarTable) (e' : Valuation M), (∀ k ∈ KoreAML.varsOf L, k ∈ tbl) → Agrees c I tbl vs σ e' →
        (KoreAML.tr ⟨tbl, []⟩ (.ceil C C (ruleRight c r))).interpret I e' (elemOf c I x.val) →
        (KoreAML.tr ⟨tbl, []⟩ L).interpret I e' (elemOf c I x.val) := by
    by_cases hce : comps.isEmpty
    · refine ⟨_, by rw [Model.prioRuleK_preTop hpre₀]; dsimp only; rw [if_pos hce],
        hkeysL (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
        fun tbl e' _ hag hceil => ?_⟩
      rw [tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd]
      exact ⟨(hlr tbl e' hag).1, (hlr tbl e' hag).2, hceil⟩
    · refine ⟨_, by rw [Model.prioRuleK_preTop hpre₀]; dsimp only; rw [if_neg hce],
        hkeysL (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))),
        fun tbl e' hkL hag hceil => ?_⟩
      rw [tr_and4, KoreAML.interp_sAnd, KoreAML.interp_sAnd, KoreAML.interp_sAnd]
      refine ⟨(hlr tbl e' hag).1, (hlr tbl e' hag).2, ?_, hceil⟩
      rw [KoreAML.tr, KoreAML.interp_sNot]
      refine ⟨anyOfC_empty hD (by
        show (KoreAML.trSort tbl (KoreAML.srt (c.sortName topCellSort))).isFreeEvar KoreAML.topVar = false
        rw [trSort_srt]; rfl) comps (fun φ hφ => ?_), ?_⟩
      · -- a competitor, its existential variables read as ordinary ones: its `applies` is the same
        obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hφ
        obtain ⟨hr'm, hlt⟩ := List.mem_filter.mp hr'
        have hlt' : r'.prio < r.prio := by simpa using hlt
        have hrc' : (ruleDropExs r').opens.any (fun i => ((ruleDropExs r').vars[i]?.map c.confined).getD false) = true →
            c.readsConfined = true := fun hany => by
          obtain ⟨i, hi, -⟩ := List.any_eq_true.mp hany
          have hi' : i ∈ r'.opens := hi
          simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
          exact Or.inl ⟨r', hr'm, by simp [List.ne_nil_of_mem hi']⟩
        refine not_applies_guardedOpen (r := ruleDropExs r') h hIc hcw (ruleSorted_dropExs (hrules r' hr'm).1)
          (rulePlainOpen_dropExs (hrules r' hr'm).2) (hlarger r' hr'm hlt') hrc' (hw r' hr'm hlt')
          (notApplies_dropExs (hprio r' hr'm hlt')) (fun i hi hil => hkL _ ?_) e'
        refine Model.varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) ?_
        simp only [KoreAML.varsOf]
        exact List.mem_append_right _ (mem_varsOf_anyOfC (hcomp r' hr'm hlt')
          (Model.varsOf_appliesOpen (Semantics.rulePlainEx_top (hrules r' hr'm).2).1 hi hil))
      · have hxs := elemOf_spec hIΓ x.property e'
        show (KoreAML.inhOf (KoreAML.trSort tbl (KoreAML.srt (c.sortName topCellSort)))).interpret I e' _
        rw [trSort_srt]
        exact hxs.2
  rw [hpat] at hax
  let ax : Kore.Axiom := { sortVars := [], pattern := .rewrites C L (ruleRight c r), attributes := [] }
  let tbl : VarTable := KoreAML.tableOf ax.sortVars ax.pattern
  have hvarsL : ∀ k ∈ KoreAML.varsOf L, k ∈ tbl := fun k hk => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    show k ∈ KoreAML.varsOf (.rewrites C L _)
    rw [KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ hk)
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => hvarsL _ (hLv i hi)
  let e' := overV c I tbl r.vars σ (KoreAML.val0 : Valuation M)
  have hval : ∀ i < r.vars.length, e'.evalEvar (tbl.ev (canonKey c r.vars i)) =
      elemOf c I ((σ.lookup i).getD default) := fun i hi => overV_at hkeys hi
  have hag : Agrees c I tbl vs σ e' := overV_agrees hIΓ hkeys hσ
  -- the guards of the axiom's free variables hold at e'
  have hgd : ∀ k ∈ (ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] ax.pattern).eraseDups, ∀ m,
      (KoreAML.guardOf tbl k).interpret I e' m := by
    intro k hk m'
    have hk' : k ∈ KoreAML.freeOf [] ax.pattern := by simpa [ax] using List.mem_eraseDups.mp hk
    obtain ⟨i, hi, -, rfl⟩ := Model.freeOf_prio_T hrules hs hp (by rw [hpat]; exact hk')
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
  have hyR := ruleRight_at_ex h hIc hcw hs hp hσ heval hens hkeys hval hag
  have hceil := ceil_right_ex h hIΓ hs hp hσ hkeys (fun i hi _ => hval i hi) hyR (elemOf_top hIΓ x tbl e')
  have hL' := himp (by rw [← hxa]; exact hLread tbl e' hvarsL hag hceil)
  obtain ⟨n, b, hn, hb, happ⟩ := KoreAML.interp_app.mp hL'
  have hbF := famEx_of_right_ex h hIc hs hp hσ hkeys (fun i hi _ => hval i hi) hb e
  have hma : m = a := (ha m).mp (((den_closed c x.val).interp e e' m).mp hm)
  rw [hma]
  exact KoreAML.interp_app.mpr ⟨n, b, hn, hbF, happ⟩

end

end Faithful

open ML Faithful

/-- **Soundness at a step by a rule with existential variables**: `sound_at`'s conclusion, for a
semantics that `coreOK` accepts whose rules have `ruleSorted` and `rulePlainEx`: in every model of
`Γc`, x has a successor among the instances of the application (`step_sound_ex`), and y is one of
them (`famEx_mem_ex`). The competitors of r whose left side matches x have decided closed
conditions. -/
theorem sound_at_ex (c : Semantics) (h : c.coreOK = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true)
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
    exact step_sound_ex h hrules hI hcw hsr hpr (sat_rules hIΓ (Or.inl ⟨_, List.mem_map.mpr ⟨r, hs.mem, rfl⟩, rfl⟩))
      (fun r' _ hlt => List.any_eq_true.mpr ⟨r, hs.mem, by simpa using hlt⟩) hs.hσ hs.hmatch hs.hreq hs.heval
      hs.hens hs.hprio hw e m
  · intro M _ I hI e m
    have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
    rw [interpret_impl]
    intro hm
    rw [((elemOf_spec hIΓ y.property e).1 m).mp hm]
    exact famEx_mem_ex h hsr hpr hs.hσ hs.heval hs.hens hI hcw e

end KCore
