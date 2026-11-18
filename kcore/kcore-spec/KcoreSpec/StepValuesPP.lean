/-
  KCore. A successor's valuation at values, for a rule with predicates: the lemmas that read no
  clause.

  - `inh_top_PP`: an element of a configuration is in the configuration sort, under every table.
  - `cond_not_refuted_pp`: a refuted condition contradicts the valuation: x's element is in
    `∃ō. (⌈req = true⌉ ∧ pre)` under the table of that sentence (`tr_condKore_twoT`).

  The successor's substitution of values (`rule_step_values_heldCEx`) is ExactHeldCEx.lean's.
-/
import KcoreSpec.OpenCompete
import KcoreSpec.OpenClauseFn
import KcoreSpec.CondTwoTables
import KcoreSpec.ClausePreCore
import KcoreSpec.HoldsDecided
import KcoreSpec.OpenSplit
import KcoreSpec.PredPlain

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (VarTable)
open HoldsShape (hasBinder Reads reads_of_agrees)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- An element of a configuration is in the configuration sort, under every table. -/
theorem inh_top_PP (hIΓ : I ⊧ᴵP Γ c) (x : Config c) (tbl : VarTable) (e : Valuation M) :
    (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e (elemOf c I x.val) := by
  rw [trSort_srtOf_twoT]
  exact (elemOf_spec hIΓ x.property e).2

/-- **A refuted condition contradicts a valuation**, for a rule with predicates: where x's element
is in `⌈req = true⌉` and `pre` at a valuation that gives the condition variables elements of their
sorts, through a table holding their keys, the conditions are not refuted. -/
theorem cond_not_refuted_pp (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c) {r : Rule} (hs : c.ruleSorted r = true)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, i ∈ r.condVars → canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    {e : Valuation M}
    (hin : ∀ i < r.vars.length, i ∈ r.condVars → InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i)))) {m : M}
    (hreqm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e m)
    (hprem : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e m) :
    ¬ r.Refuted c := by
  intro href
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  haveI : OvlOK c := (hypSound_of_core h).2.2.2.2.2.2.2.2
  have hD := defOK hIΓ
  have hs' := hs
  simp only [Semantics.ruleSorted, Bool.and_eq_true] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hokP⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hs'
  obtain ⟨-, hreqK, -, -⟩ := Semantics.ruleSorted_parts c hs
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let l := (List.range r.vars.length).filter r.condVars.contains
  have hl : ∀ i ∈ l, i < r.vars.length := fun i hi => List.mem_range.mp (List.mem_filter.mp hi).1
  have hml : ∀ i < r.vars.length, i ∈ r.condVars → i ∈ l := fun i hi hc =>
    List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hc⟩
  have hbs : l.filterMap (vs[·]?) = l.map (vs.getD · default) :=
    filterMap_getElem?_of_lt vs l (fun i hi => by rw [canonVars_length]; exact hl i hi)
  have hK : r.condK c = KoreAML.existsAll C ((l.map (vs.getD · default)).map KoreAML.Var.kore)
      (.and C ([reqPat C (r.req.map (Term.kore c vs))] ++ Cond.conj c vs C r.pre)) := by
    unfold Rule.condK
    rw [← hbs]
  unfold Rule.Refuted at href
  rw [hK] at href
  unfold KoreAML.denB at href
  generalize htbl : KoreAML.tableOf [] _ = tbl2 at href
  have hkeys2 : ∀ i < r.vars.length, i ∈ l → canonKey c r.vars i ∈ tbl2 := fun i _ hil => by
    rw [← htbl]; unfold KoreAML.tableOf canonKey
    exact List.mem_eraseDups.mpr (List.mem_append_right _
      (mem_varsOf_existsAll (List.mem_map_of_mem (List.mem_map_of_mem hil))))
  let e' := moveV c tbl tbl2 r.vars l e
  have hneg := href hI e' m
  rw [interpret_neg] at hneg
  apply hneg
  have hnd : (((l.map (vs.getD · default)).map KoreAML.Var.kore).map fun b => tbl2.ev (KoreAML.evarKey b)).Nodup := by
    rw [List.map_map, List.map_map]
    refine Model.nodup_map_of_injOn _ (fun i hi j hj he => ?_) (List.nodup_range.filter _)
    exact canonKey_inj (hl i hi) (hl j hj) (ev_inj (hkeys2 i (hl i hi) hi) (hkeys2 j (hl j hj) hj) he)
  have hsrt : ∀ b ∈ (l.map (vs.getD · default)).map KoreAML.Var.kore, ∃ n, b.sort = KoreAML.srt n := fun b hb => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    show ∃ n, ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt n
    rw [canonVars_getD c (hl i hi)]; exact ⟨_, rfl⟩
  refine existsAll_intro_at hD _ e' e' m hnd hsrt (fun _ _ => rfl) rfl (fun b hb n hn => ?_) ?_
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hil, rfl⟩ := List.mem_map.mp hv
    have hs' : ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
      rw [canonVars_getD c (hl i hil)]; rfl
    change ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt n at hn
    rw [hs'] at hn
    rw [← srt_inj hn]
    show InS I _ (e'.evalEvar (tbl2.ev (canonKey c r.vars i)))
    rw [moveV_at hkeys2 (hl i hil) hil]
    exact hin i (hl i hil) (by simpa using (List.mem_filter.mp hil).2)
  · refine (interp_and (by simp)).mpr fun φ hφ => ?_
    rcases List.mem_append.mp hφ with hφ | hφ
    · rw [List.mem_singleton.mp hφ]
      cases hq : r.req with
      | none =>
        show (KoreAML.tr ⟨tbl2, []⟩ (.top C)).interpret I e' m
        rw [KoreAML.tr, KoreAML.interp_sTop hD Model.srtOf_free_stdI]
        exact reqPat_inhSplit hIΓ hreqm tbl2 e'
      | some t =>
        have htS : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool := by
          rw [hq] at hreqK; simpa [reqOK] using hreqK
        have hlt : ∀ i ∈ varOccs t, i < r.vars.length := Exec.sortOfTerm_vars htS
        have hcv : ∀ i ∈ varOccs t, i ∈ r.condVars := fun i hi => by
          simp only [Rule.condVars, hq, Option.map_some, Option.getD_some]; exact List.mem_append_left _ hi
        rw [hq] at hreqm
        exact (tr_reqPat_congr hIΓ (fun i hi => moveV_at hkeys2 (hlt i hi) (hml i (hlt i hi) (hcv i hi))) m).mpr
          hreqm
    · by_cases hT : r.pre.isTop = true
      · simp [Cond.conj, hT] at hφ
      · obtain rfl : φ = Cond.kore c vs C r.pre := by simpa [Cond.conj, hT] using hφ
        refine (tr_condKore_twoT hD r.pre hokP (fun k hk0 => ⟨hkP k hk0, ?_⟩) (fun i hi => ?_) m).mp
          (hprem _ (by simp [Cond.conj, hT]))
        · rw [← htbl]; unfold KoreAML.tableOf
          exact List.mem_eraseDups.mpr (List.mem_append_right _ (HoldsShape.varsOf_existsAll_bodyHF
            (Model.varsOf_and_mem (List.mem_append_right _ (by simp [Cond.conj, hT, vs, C])) hk0) _))
        · have hlt := varOccsCond_lt_twoT r.pre hokP i hi
          have hc : i ∈ r.condVars := List.mem_append_right _ hi
          exact ⟨hkeys i hlt hc, hkeys2 i hlt (hml i hlt hc), (moveV_at hkeys2 hlt (hml i hlt hc)).symm⟩

end

end Faithful

end KCore
