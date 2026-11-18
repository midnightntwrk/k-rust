/-
  KCore. Soundness at a step by a rule whose left side need not bind every variable, in any model
  of `Γc c`: the lemmas that read no clause.

  - `famEx_eqOpen`: the pattern `famEx` reads, for a rule with `rulePlainOpen`: every variable is
    fixed to its value under σ.
  - `applies_matchOpen`: a rule whose `applies` holds at x's element has a left side that matches
    x, so a condition on a competitor is asked only of one that matches x.
  - `sNext_congr`: `•φ` depends only on the set φ denotes.
-/
import KcoreSpec.OpenSplit

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

/-! ## The instances of a step -/

section
variable {c : Semantics}

/-- The pattern `famEx` reads, for a rule with `rulePlainOpen` (not asked to be one of the
definition's): every variable is fixed to its value under σ. -/
theorem famEx_eqOpen {r : Rule} (hp : c.rulePlainOpen r = true) (σ : Subst) :
    famEx c r σ = KoreAML.denB (KoreAML.existsAll (srtOf c topCellSort)
      ((canonVars c r.vars).map KoreAML.Var.kore)
      (.and (srtOf c topCellSort) (fixK c r σ (List.range r.vars.length) ++
        [.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.rhs,
          reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))]]))) := by
  obtain ⟨hex, -, hpost⟩ := Semantics.rulePlainOpen_top hp
  have hv := filterMap_range_getElem? (canonVars c r.vars)
  rw [canonVars_length] at hv
  have hf : (List.range r.vars.length).filter (fun _ => true) = List.range r.vars.length :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  simp only [famEx, ruleRight, hex, hpost, List.contains_nil, Bool.not_false, Cond.conj, Cond.isTop, ite_true,
    List.filterMap_nil, List.foldr_nil, List.append_nil]
  rw [hf, hv]

variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

end

/-! ## A competitor whose `applies` holds matches -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A rule whose `applies` holds at x's element has a left side that matches x**, in a model of
`Γ`, for a rule with `ruleSorted` and `rulePlainOpen`. -/
theorem applies_matchOpen (h : c.coreOK = true) (hIΓ : I ⊧ᴵP Γ c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainOpen r = true) {x : Config c}
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl) (e : Valuation M)
    (hm : (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x.val)) :
    ∃ σ', PatVal c σ' r.lhs x.val := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hIΓ
  obtain ⟨hlhs, -, -, -⟩ := Semantics.ruleSorted_parts c hs
  obtain ⟨-, hpre, -⟩ := Semantics.rulePlainOpen_top hp
  let vs := canonVars c r.vars
  let n := r.vars.length
  let C := srtOf c topCellSort
  let l := (List.range n).filter r.leftVars.contains
  have hl : ∀ i ∈ l, i < n := fun i hi => List.mem_range.mp (List.mem_filter.mp hi).1
  have hlm : ∀ i ∈ l, i ∈ r.leftVars := fun i hi => by simpa using (List.mem_filter.mp hi).2
  have hml : ∀ i < n, i ∈ r.leftVars → i ∈ l := fun i hi hil =>
    List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hil⟩
  have hbs : l.filterMap (vs[·]?) = l.map (vs.getD · default) :=
    filterMap_getElem?_of_lt vs l (fun i hi => by rw [canonVars_length]; exact hl i hi)
  rw [applies_eq hpre] at hm
  change (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll C ((l.filterMap (vs[·]?)).map KoreAML.Var.kore)
    (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs))]))).interpret I e (elemOf c I x.val) at hm
  rw [hbs] at hm
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
  rw [tr_and2, KoreAML.interp_sAnd] at hbody
  have hinL : ∀ i < n, i ∈ r.leftVars → InS I (c.sortName (r.vars.getD i 0)) (e'.evalEvar (tbl.ev (keyAt vs i))) :=
    fun i hi hil => hguard _ (List.mem_map_of_mem (List.mem_map_of_mem (hml i hi hil))) _
      (by show (vs.getD i default).kore.sort = _; rw [canonVars_getD c hi]; rfl)
  -- the other variables: the configuration sort and x's element
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
  have hlx1 := (tr_kore_congr r.lhs (fun i hi => (hoff1 i (hltL i hi) (hlhsL i hi)).symm) _).mp hbody.1
  have hlhs' : sortOfTerm c.patCtxAll r.leftSorts r.lhs = some topCellSort := by
    rw [sortOfTerm_congr r.lhs fun i hi => Rule.leftSorts_getElem? (hltL i hi) (hlhsL i hi)]; exact hlhs
  have hlhsN' : sortOfTerm c.patCtxNF r.leftSorts r.lhs = some topCellSort := by
    rw [sortOfTerm_congr r.lhs fun i hi => Rule.leftSorts_getElem? (hltL i hi) (hlhsL i hi)]; exact Semantics.ruleSorted_lhs_nf c hs
  obtain ⟨hpv, -⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 hvsl hin1 (collPat_of_sorted hph' hlhs')
    hlhsN' x.property hlx1
  exact ⟨_, hpv⟩

end

end Faithful

open ML Faithful

/-- `•φ` depends only on the set φ denotes. -/
theorem sNext_congr {M : Type} {I : Interpretation KoreAML.Sym M} {e : Valuation M} {φ ψ : KoreAML.P}
    (h : ∀ a, φ.interpret I e a ↔ ψ.interpret I e a) {m : M}
    (hm : (KoreAML.sNext φ).interpret I e m) : (KoreAML.sNext ψ).interpret I e m := by
  unfold KoreAML.sNext at hm ⊢
  rw [KoreAML.interp_app] at hm ⊢
  obtain ⟨n, b, hn, hb, happ⟩ := hm
  exact ⟨n, b, hn, (h b).mp hb, happ⟩

end KCore
