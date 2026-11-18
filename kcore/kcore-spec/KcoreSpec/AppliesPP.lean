/-
  KCore. A competitor with a `pre`, read in the value model at T.

  `applies` of a rule is `∃x̄'. (lhs ∧ ⌈req = true⌉ ∧ pre)`, x̄' the variables of its left side and
  its conditions, the conjunct `pre` absent where it is `\top` (`Cond.conj`). In the value model at
  any transition T, at a configuration's element:

  - `applies_eqPP`: `applies` with the binders as `canonVars` names them, for any `pre`.
  - `preConj_iffPP`: the conjuncts `pre` adds hold at a configuration's element exactly where
    `TrueV … pre`, under a valuation that reads `pre`'s free variables as their values under σ
    (`ReadsT`), with the keys of `pre`'s pattern in the table: the value model's truth of a
    condition (`trueV_stdI`), and nothing for `\top`. No truth value of `pre` is asked for.
  - `applies_iff_T_pp`: **a configuration is in a well-sorted rule's `applies` pattern exactly where
    the rule applies to it in the value model** (`RuleAppliesV`: `RuleApplies` with `TrueV … pre`),
    the rule not asked to be one of the definition's, its `pre` arbitrary. Read are `ruleSorted`,
    the keys of the left side's and the conditions' variables and of `pre`'s pattern in the table
    (the table hypothesis), and that x is a configuration. The binders' sorts are numbered by
    `rule_vars_numCN` (`condOK`).
  - `ruleAppliesV_iff`: where `pre` has a truth value at each σ the left side and `requires` give
    at x, under `FnDet`, `RuleAppliesV` is `RuleApplies` (`holds_trueV`); `applies_iff_T_dec` is
    `applies_iff_T_pp` in that form.
  - `applies_iff_T_of_pp`: `applies_iff_T`'s statement (`ruleSorted`, `rulePlainEx`) as the instance
    at `pre = \top`, where the table hypothesis and the truth value hold of themselves.
-/
import KcoreSpec.TrueV
import KcoreSpec.CondNumbered

set_option autoImplicit false

namespace KCore

/-- **`RuleApplies` with the value model's truth of `pre`**: some σ well sorted on the left side's
and the conditions' variables matches x by the left side, makes `requires` true and `pre` true in
the value model (`TrueV`). -/
def RuleAppliesV (c : Semantics) (r : Rule) (x : GroundTerm) : Prop :=
  ∃ σ, c.WellSortedAt r.vars r.leftVars σ ∧ PatVal c σ r.lhs x ∧
    (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧ TrueV c r.vars.length σ r.pre

/-- Where `pre` has a truth value at each σ the left side and `requires` give at x, under `FnDet`,
`RuleAppliesV` is `RuleApplies`. -/
theorem ruleAppliesV_iff {c : Semantics} (hd : FnDet c) {r : Rule} {x : GroundTerm}
    (hdec : ∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x →
      (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) → ∃ b, Holds c r.vars.length σ r.pre b) :
    RuleAppliesV c r x ↔ RuleApplies c r x := by
  constructor
  · rintro ⟨σ, hσ, hp, hq, hv⟩
    obtain ⟨b, hb⟩ := hdec σ hσ hp hq
    have hbt := (holds_trueV hd hb).mp hv
    subst hbt
    exact ⟨σ, hσ, hp, hq, hb⟩
  · rintro ⟨σ, hσ, hp, hq, hh⟩
    exact ⟨σ, hσ, hp, hq, (holds_trueV hd hh).mpr rfl⟩

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-- `applies` of a rule, its binders the canonical variables of its left side and conditions, for
any `pre`. -/
theorem applies_eqPP (r : Rule) :
    applies c r (canonRulePres r) = KoreAML.existsAll (srtOf c topCellSort)
      ((((List.range r.vars.length).filter r.leftVars.contains).map ((canonVars c r.vars).getD · default)).map
        KoreAML.Var.kore)
      (.and (srtOf c topCellSort) ([Term.kore c (canonVars c r.vars) r.lhs,
        reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars)))] ++
        Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre)) := by
  have he : applies c r (canonRulePres r) = KoreAML.existsAll (srtOf c topCellSort)
      ((((List.range r.vars.length).filter r.leftVars.contains).filterMap ((canonVars c r.vars)[·]?)).map
        KoreAML.Var.kore)
      (.and (srtOf c topCellSort) ([Term.kore c (canonVars c r.vars) r.lhs,
        reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars)))] ++
        Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre)) := rfl
  rw [he, filterMap_getElem?_of_lt]
  intro i hi
  rw [canonVars_length]; exact List.mem_range.mp (List.mem_filter.mp hi).1

/-- The body of `applies`: its left side, its `requires` and the conjuncts of its `pre`. -/
theorem interp_bodyPP {T : GroundTerm → GroundTerm → Prop} {tbl : KoreAML.VarTable} {e : Valuation Elem}
    {m : Elem} (S : Kore.KSort) (p q : Kore.Pattern) (vs : List KoreAML.Var) (C : Kore.KSort) (pre : Cond) :
    (KoreAML.tr ⟨tbl, []⟩ (.and S ([p, q] ++ Cond.conj c vs C pre))).interpret (stdI_T c T) e m ↔
      (KoreAML.tr ⟨tbl, []⟩ p).interpret (stdI_T c T) e m ∧ (KoreAML.tr ⟨tbl, []⟩ q).interpret (stdI_T c T) e m ∧
        ∀ φ ∈ Cond.conj c vs C pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret (stdI_T c T) e m := by
  by_cases hT : pre.isTop = true
  · simp only [Cond.conj, hT, if_true, List.append_nil]
    rw [tr_and2, KoreAML.interp_sAnd]
    simp
  · have hc : Cond.conj c vs C pre = [Cond.kore c vs C pre] := by simp [Cond.conj, hT]
    rw [hc, List.cons_append, List.cons_append, List.nil_append, tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd]
    simp

/-- **The conjuncts of a `pre` in the value model at T**: at a configuration's element they hold
exactly where `TrueV … pre`, under a valuation that reads `pre`'s free variables as their values
under σ, with the keys of `pre`'s pattern in the table. -/
theorem preConj_iffPP (h : HypModelCore c) {T : GroundTerm → GroundTerm → Prop} {vars : List Srt} {pre : Cond}
    (hok : c.condOK vars pre = true) (hbd : Cond.bound c vars.length pre = true) {P : Nat → Prop} {σ : Subst}
    {tbl : KoreAML.VarTable} {e : Valuation Elem}
    (hP : ∀ i ∈ varOccsCond vars.length pre, i < vars.length → P i) (hr : ReadsT c vars P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c topCellSort) pre), k ∈ tbl)
    {x : GroundTerm} (hx : c.sortOf x = some topCellSort) :
    (∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c topCellSort) pre,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret (stdI_T c T) e (.val x)) ↔ TrueV c vars.length σ pre := by
  by_cases hT : pre.isTop = true
  · have hp : pre = .top := Cond.eq_top_of_isTop hT
    subst hp
    simp only [Cond.conj, Cond.isTop, if_true]
    exact ⟨fun _ => trivial, fun _ φ hφ => absurd hφ List.not_mem_nil⟩
  · have hc : Cond.conj c (canonVars c vars) (srtOf c topCellSort) pre =
        [Cond.kore c (canonVars c vars) (srtOf c topCellSort) pre] := by simp [Cond.conj, hT]
    rw [hc, ← trueV_stdI h T pre hok hbd hP hr hk top_numbered (.val x) (show InSort c topCellSort (.val x) from hx)]
    simp

/-- **A competitor with a `pre`, read at T**: a configuration is in a well-sorted rule's `applies`
pattern exactly where the rule applies to it in the value model (`RuleAppliesV`, `TrueV … pre`
included), the rule not asked to be one of the definition's. The keys of the variables of the left
side and the conditions and those of `pre`'s pattern are in the table. No truth value of `pre` is
asked for. -/
theorem applies_iff_T_pp (h : HypModelCore c) {T : GroundTerm → GroundTerm → Prop} {r : Rule}
    (hs : c.ruleSorted r = true) {tbl : KoreAML.VarTable}
    (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (e : Valuation Elem) {x : GroundTerm} (hx : c.sortOf x = some topCellSort) :
    (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret (stdI_T c T) e (.val x) ↔
      RuleAppliesV c r x := by
  have hn := h.namesK
  obtain ⟨hlhs, hreqK, -, -⟩ := Semantics.ruleSorted_parts c hs
  have hreqS : ∀ t, r.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool :=
    fun t ht => by rw [ht] at hreqK; simpa [reqOK] using hreqK
  have hs' := hs
  simp only [Semantics.ruleSorted, Bool.and_eq_true] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hokP⟩, -⟩, -⟩, hbdP⟩, -⟩, -⟩ := hs'
  have hnum := rule_vars_numCN h hs
  let vs := canonVars c r.vars
  let n := r.vars.length
  let l := (List.range n).filter r.leftVars.contains
  have hl : ∀ i ∈ l, i < n := fun i hi => List.mem_range.mp (List.mem_filter.mp hi).1
  have hlm : ∀ i ∈ l, i ∈ r.leftVars := fun i hi => by simpa using (List.mem_filter.mp hi).2
  have hml : ∀ i < n, i ∈ r.leftVars → i ∈ l := fun i hi hil =>
    List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hil⟩
  have hnd : (((l.map (vs.getD · default)).map KoreAML.Var.kore).map fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
    rw [List.map_map, List.map_map]
    refine nodup_map_of_injOn _ (fun i hi j hj he => ?_) (List.nodup_range.filter _)
    exact canonKey_inj (hl i hi) (hl j hj) (ev_inj (hkeys i (hl i hi) (hlm i hi)) (hkeys j (hl j hj) (hlm j hj)) he)
  have hsrt : ∀ b ∈ (l.map (vs.getD · default)).map KoreAML.Var.kore, ∃ n, b.sort = KoreAML.srt n := fun b hb => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    show ∃ n, ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt n
    rw [canonVars_getD c (hl i hi)]; exact ⟨_, rfl⟩
  have hltL : ∀ i ∈ varOccs r.lhs, i < n := fun i hi => varOccs_lt r.lhs hlhs i hi
  have hreqLt : ∀ t, r.req = some t → ∀ i ∈ varOccs t, i < n ∧ i ∈ r.leftVars := fun t ht i hi =>
    ⟨varOccs_lt t (hreqS t ht) i hi, Rule.req_leftVars ht i hi⟩
  let P : Nat → Prop := fun i => i < n ∧ i ∈ r.leftVars
  have hPpre : ∀ i ∈ varOccsCond r.vars.length r.pre, i < r.vars.length → P i := fun i hi hlt =>
    ⟨hlt, List.mem_append_right _ (List.mem_append_right _ hi)⟩
  have hPk : ∀ i, P i → i < r.vars.length ∧ canonKey c r.vars i ∈ tbl := fun i hi =>
    ⟨hi.1, hkeys i hi.1 hi.2⟩
  have hpat : PatOK c P r.lhs :=
    (patOK_of_sorted h (h.lhs_nf hr hlhs)).monoOpen fun i hi => ⟨hltL i hi, List.mem_append_left _ hi⟩
  have hreqT : ∀ t, r.req = some t → TermOK c P t := fun t ht =>
    (termOK_of_sorted h fns_headsOK (hreqS t ht)).monoOpen (hreqLt t ht)
  rw [applies_eqPP r]
  constructor
  · intro hm
    obtain ⟨e', -, hguard, hbody⟩ := existsAll_elim AtT.defOK_std _ e _ hnd hsrt hm
    obtain ⟨hl', hreq, hpreM⟩ := (interp_bodyPP _ _ _ _ _ _).mp hbody
    have hin : ∀ i < n, i ∈ r.leftVars → InSort c (r.vars.getD i 0) (e'.evalEvar (tbl.ev (canonKey c r.vars i))) :=
      fun i hi hil => (AtT.inhOf_sort (T := T) hn (hnum i hi) KoreAML.val0 _).mp
        (hguard _ (List.mem_map_of_mem (List.mem_map_of_mem (hml i hi hil))) _
          (by show (vs.getD i default).kore.sort = _; rw [canonVars_getD c hi]; rfl))
    let σ := substE c tbl r.vars e'
    have hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e' m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v := by
      rintro i ⟨hi, hil⟩ m
      obtain ⟨v, he, -⟩ := inSort_val (hin i hi hil)
      rw [AtT.var_read, substE_lookup hi]
      show m = e'.evalEvar (tbl.ev (canonKey c r.vars i)) ↔ _
      rw [he]
      simp [toVal]
    have hσs : ∀ i, P i → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (r.vars.getD i 0) := by
      rintro i ⟨hi, hil⟩
      obtain ⟨v, he, hsv⟩ := inSort_val (hin i hi hil)
      exact ⟨v, by rw [substE_lookup hi, he]; rfl, hsv⟩
    have hσ : c.WellSortedAt r.vars r.leftVars σ := fun i hil s hs' => by
      have hi : i < n := (List.getElem?_eq_some_iff.mp hs').1
      obtain ⟨v, hv, hsv⟩ := hσs i ⟨hi, hil⟩
      refine ⟨v, hv, ?_⟩
      rwa [List.getD_eq_getElem?_getD, hs', Option.getD_some] at hsv
    obtain ⟨x', hx', he⟩ := (AtT.tr_pat h hvar hpat _).mp hl'
    cases he
    have hq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)) := fun t ht => by
      rw [ht] at hreq
      simp only [Option.map_some] at hreq
      exact ((AtT.reqPat_iff h hvar (hreqT t ht) (srtOf_top_den_T h e') top_isSort_T _).mp hreq).2
    have hr : ReadsT c r.vars P σ tbl e' := readsT_of_hvar hPk hσs hvar
    exact ⟨σ, hσ, hx', hq,
      (preConj_iffPP h hokP hbdP hPpre hr hkP hx).mp hpreM⟩
  · rintro ⟨σ, hσ, hp', hq, hpre⟩
    have hσv : ∀ i < n, i ∈ r.leftVars → ∃ w, σ.lookup i = some w ∧ c.sortOf w = some (r.vars.getD i 0) :=
      fun i hi hil => hσ i hil _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
    let f : Nat → Elem := fun j => .val ((σ.lookup j).getD default)
    let e' := setV c tbl r.vars r.leftVars f e
    have hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e' m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v := by
      rintro i ⟨hi, hil⟩ m
      rw [AtT.var_read]
      show m = (setV c tbl r.vars r.leftVars f e).evalEvar (tbl.ev (canonKey c r.vars i)) ↔ _
      rw [setV_on hkeys hi hil]
      obtain ⟨w, hw, -⟩ := hσv i hi hil
      simp [f, hw]
    have hr : ReadsT c r.vars P σ tbl e' := readsT_of_hvar hPk (fun i hi => hσv i hi.1 hi.2) hvar
    refine AtT.existsAll_intro _ e e' _ hnd hsrt (fun z hz => ?_) rfl (fun b hb k hk => ?_) ?_
    · show (if h : _ then _ else _) = _
      rw [dif_neg]
      rintro ⟨i, hi, hil, rfl⟩
      exact hz _ (List.mem_map_of_mem (List.mem_map_of_mem (hml i hi hil))) rfl
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
      obtain ⟨i, hil, rfl⟩ := List.mem_map.mp hv
      have hs' : ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
        rw [canonVars_getD c (hl i hil)]; rfl
      change ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt k at hk
      rw [hs'] at hk
      rw [← srt_inj hk]
      show InS (stdI_T c T) _ ((setV c tbl r.vars r.leftVars f e).evalEvar (tbl.ev (canonKey c r.vars i)))
      rw [setV_on hkeys (hl i hil) (hlm i hil)]
      obtain ⟨w, hw, hws⟩ := hσv i (hl i hil) (hlm i hil)
      show InS (stdI_T c T) _ (Elem.val ((σ.lookup i).getD default))
      rw [hw, Option.getD_some]
      exact (AtT.inhOf_sort (T := T) hn (hnum i (hl i hil)) KoreAML.val0 _).mpr hws
    · refine (interp_bodyPP _ _ _ _ _ _).mpr ⟨(AtT.tr_pat h hvar hpat _).mpr ⟨x, hp', rfl⟩, ?_,
        (preConj_iffPP h hokP hbdP hPpre hr hkP hx).mpr hpre⟩
      cases hrq : r.req with
      | none =>
        simp only [Option.map_none, reqPat]
        rw [KoreAML.tr, KoreAML.interp_sTop AtT.defOK_std (by unfold srtOf; rw [trSort_srt]; rfl),
          KoreAML.interp_inhOf_of (srtOf_top_den_T h e'), AtT.inh_srt]
        exact hx
      | some t =>
        simp only [Option.map_some]
        exact (AtT.reqPat_iff h hvar (hreqT t hrq) (srtOf_top_den_T h e') top_isSort_T _).mpr
          ⟨(AtT.inh_srt _ _).mpr hx, hq t hrq⟩

/-- `applies_iff_T_pp` with `RuleApplies` on the right, where `pre` has a truth value at each σ the
left side and `requires` give at x (`ruleAppliesV_iff`, `FnDet` from `HypModelCore`). -/
theorem applies_iff_T_dec (h : HypModelCore c) {T : GroundTerm → GroundTerm → Prop} {r : Rule}
    (hs : c.ruleSorted r = true) {tbl : KoreAML.VarTable}
    (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (e : Valuation Elem) {x : GroundTerm} (hx : c.sortOf x = some topCellSort)
    (hdec : ∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x →
      (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) → ∃ b, Holds c r.vars.length σ r.pre b) :
    (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret (stdI_T c T) e (.val x) ↔
      RuleApplies c r x :=
  (applies_iff_T_pp h hs hkeys hkP e hx).trans (ruleAppliesV_iff h.det hdec)

/-- **`applies_iff_T` as the instance of `applies_iff_T_pp` at `pre = \top`**: its statement, for a
rule with `ruleSorted` and `rulePlainEx`; `\top` has a truth value at every σ and its pattern no
variable. -/
theorem applies_iff_T_of_pp (h : HypModelCore c) {T : GroundTerm → GroundTerm → Prop} {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainEx r = true) {tbl : KoreAML.VarTable}
    (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl) (e : Valuation Elem)
    {x : GroundTerm} (hx : c.sortOf x = some topCellSort) :
    (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret (stdI_T c T) e (.val x) ↔
      RuleApplies c r x := by
  obtain ⟨hpre, -⟩ := Semantics.rulePlainEx_top hp
  refine applies_iff_T_dec h hs hkeys (fun k hk => ?_) e hx (fun _ _ _ _ => ⟨true, hpre ▸ .top⟩)
  rw [hpre] at hk
  simp [Cond.kore, KoreAML.varsOf, srtOf, KoreAML.srt, KoreAML.sortVarsOf, KoreAML.sortVarsOfList] at hk

end Model

end Faithful

end KCore
