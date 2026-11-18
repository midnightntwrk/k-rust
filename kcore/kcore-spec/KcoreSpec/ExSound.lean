/-
  KCore. Soundness at a step by a rule with existential variables, in any model of `Γc c`: the
  lemmas that read no clause.

  - `overVEx_at`, `overVEx_off`, `binders_nodupEx`, `famEx_keysEx`: the valuation that gives the
    variables other than the existential ones their values under σ, and the table of `famEx`.
  - `famEx_of_right_ex`, `ruleRight_sort_ex`, `ceil_right_ex`: an element of the rule's right side
    is among the instances of the application and in the configuration sort, and the right side
    is defined where an element is in it.
  - `ruleDropExs` with `ruleSorted_dropExs`, `notApplies_dropExs`, `rulePlainOpen_dropExs`: a rule
    read with its existential variables as ordinary ones.
-/
import KcoreSpec.ExFamValues
import KcoreSpec.CondPredAt
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

/-- The binders of the canonical variables listed in l, at their indices in a table holding their
keys: one index each. -/
theorem binders_nodupEx {vars : List Srt} {tbl : VarTable} (hkeys : ∀ i < vars.length, canonKey c vars i ∈ tbl)
    {l : List Nat} (hl : ∀ i ∈ l, i < vars.length) (hnd : l.Nodup) :
    ((l.map fun i => ((canonVars c vars).getD i default).kore).map fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
  rw [List.map_map]
  refine List.pairwise_map.mpr (hnd.imp_of_mem fun {i j} hi hj hne he => hne ?_)
  exact canonKey_inj (hl i hi) (hl j hj) (ev_inj (hkeys i (hl i hi)) (hkeys j (hl j hj)) he)

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

end

end Faithful

open ML Faithful

end KCore
