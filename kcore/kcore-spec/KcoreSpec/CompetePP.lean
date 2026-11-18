/-
  KCore. A competitor with a `pre`, in a model of `Γc`.

  `applies` of a rule is `∃x̄'. (lhs ∧ ⌈req = true⌉ ∧ pre)` (`Model.applies_eqPP`), the conjunct
  `pre` the condition's pattern `Cond.kore` where it is not `\top`. In any model I of `Γc`, at the
  element of a configuration x, for a well-sorted rule whose `pre` need not be `\top`:

  - `applies_of_values_pp`: a σ that gives the left side's and the conditions' variables values of
    their sorts, matches x, makes the `requires` `true` and `pre` `true` (`Holds … pre true`) puts
    x's element in `applies`. `pre`'s conjunct is read by the Holds lemma (`holds_entails`), at the
    valuation that gives those variables σ's elements.
  - `notApplies_of_not_applies_pp`: where the `requires` has a result and `pre` a truth value at
    each match (the first conjunct of `StepDecided` for the rule), x's element outside `applies`
    gives `NotApplies`: at a match, a `requires` without the result `true` fails it, and otherwise
    `pre` is `false`, for `true` would put x's element in `applies`.
  - `not_applies_of_notApplies_pp`: `NotApplies` puts x's element outside `applies`, for a rule with
    `rulePlainPP` (its competition conjunct) and a rule of a larger priority, its conditions decided
    when `needsWitness` holds. A valuation in `applies` gives, at values, a match at which the
    `requires` evaluates to `true` (as in `not_applies_of_notApplies`) and at which `pre` cannot be
    `false`: x's element is in `pre`'s pattern, and where `Holds … pre false` no element of the
    configuration sort is (`holds_entails`). Where a witness σw of the conditions replaces the
    conditions' variables, `pre` holds at σw (`Rule.Witnessed`), so x's element is in its pattern
    there; a refuted condition contradicts the valuation (`cond_not_refuted_pp`).
  - `applies_iff_pp`: the two directions together.

  No truth value of `pre` is asked for by the first and third, and `FnTerminates` by none. The
  hypotheses beyond the `pre = \top` lemmas of `OpenRuleStepCl` are that the keys of `pre`'s
  pattern are in the table (the table hypothesis) and that a `pre` with a binder is read where the
  definition reads a confined sort (`holds_entails`). `condOK` is read at the rule's own variable
  sorts: the Holds lemma reads a σ at the condition's free variables only (`Reads`), all of which
  are among the left side's and the conditions' variables, so no other list of sorts is needed.
-/
import KcoreSpec.StepValuesPP
import KcoreSpec.AppliesPP

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK VarTable)
open HoldsShape (hasBinder Reads)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

omit [Inhabited M] in
/-- The body of `applies` in any interpretation: its left side, its `requires` and the conjuncts of
its `pre`. -/
theorem interp_bodyPPI {tbl : VarTable} {e : Valuation M} {m : M} (S : Kore.KSort) (p q : Kore.Pattern)
    (vs : List KoreAML.Var) (C : Kore.KSort) (pre : Cond) :
    (KoreAML.tr ⟨tbl, []⟩ (.and S ([p, q] ++ Cond.conj c vs C pre))).interpret I e m ↔
      (KoreAML.tr ⟨tbl, []⟩ p).interpret I e m ∧ (KoreAML.tr ⟨tbl, []⟩ q).interpret I e m ∧
        ∀ φ ∈ Cond.conj c vs C pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e m := by
  by_cases hT : pre.isTop = true
  · simp only [Cond.conj, hT, if_true, List.append_nil]
    rw [tr_and2, KoreAML.interp_sAnd]
    simp
  · have hc : Cond.conj c vs C pre = [Cond.kore c vs C pre] := by simp [Cond.conj, hT]
    rw [hc, List.cons_append, List.cons_append, List.nil_append, tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd]
    simp

omit [Inhabited M] in
/-- A σ that agrees with a valuation is read at the variables where it gives values of their
sorts, their keys in the table. -/
theorem reads_of_agreesAt {vars : List Srt} {P : Nat → Prop} {σ : Subst} {tbl : VarTable} {e : Valuation M}
    (hag : Agrees c I tbl (canonVars c vars) σ e)
    (hP : ∀ i, P i → i < vars.length ∧ canonKey c vars i ∈ tbl ∧
      ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (vars.getD i 0)) : Reads c I vars P σ tbl e := by
  intro i hi
  obtain ⟨hl, hk, v, hv, hsv⟩ := hP i hi
  exact ⟨hl, hk, v, hv, hsv, hag i v (by rw [canonVars_length]; exact hl) hv⟩

/-- **The conjuncts a predicate adds to a sentence, in a model of `Γc`** (none for `\top`): at an
element of the configuration sort they hold exactly where its truth value is `true`, at a σ the
valuation reads at the predicate's free variables, the keys of its pattern in the table. -/
theorem conj_iff_holdsPP (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    {vars : List Srt} {p : Cond} (hok : c.condOK vars p = true) (hbd : Cond.bound c vars.length p = true)
    (hrc : hasBinder p = true → c.readsConfined = true) {σ : Subst} {tbl : VarTable} {e : Valuation M}
    (hr : Reads c I vars (fun i => i ∈ varOccsCond vars.length p) σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c topCellSort) p), k ∈ tbl)
    {a : M} (ha : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e a)
    {b : Bool} (hh : Holds c vars.length σ p b) :
    (∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c topCellSort) p, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a) ↔
      b = true := by
  by_cases hT : p.isTop = true
  · obtain rfl := Cond.eq_top_of_isTop hT
    cases hh
    simp [Cond.conj, Cond.isTop]
  · have hc : Cond.conj c (canonVars c vars) (srtOf c topCellSort) p =
        [Cond.kore c (canonVars c vars) (srtOf c topCellSort) p] := by simp [Cond.conj, hT]
    rw [hc]
    simp only [List.mem_singleton, forall_eq]
    exact HoldsShape.holds_entails h hI hcw p hrc hok hbd (fun i hi _ => hi) hr hk top_numbered hh a ha

omit [Inhabited M] in
/-- The conjuncts a predicate adds to a sentence read two valuations alike where they agree at its
free variables. -/
theorem conj_congrPP (hD : DefOK I) {vars : List Srt} {p : Cond} (hok : c.condOK vars p = true)
    {tbl : VarTable} {e e' : Valuation M}
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c topCellSort) p), k ∈ tbl)
    (hkeys : ∀ i ∈ varOccsCond vars.length p, canonKey c vars i ∈ tbl)
    (hag : ∀ i ∈ varOccsCond vars.length p,
      e.evalEvar (tbl.ev (canonKey c vars i)) = e'.evalEvar (tbl.ev (canonKey c vars i))) {a : M}
    (hm : ∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c topCellSort) p, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a) :
    ∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c topCellSort) p, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e' a := by
  intro φ hφ
  by_cases hT : p.isTop = true
  · simp [Cond.conj, hT] at hφ
  · obtain rfl : φ = Cond.kore c (canonVars c vars) (srtOf c topCellSort) p := by simpa [Cond.conj, hT] using hφ
    exact (tr_condKore_twoT hD p hok (fun k hk0 => ⟨hk k hk0, hk k hk0⟩)
      (fun i hi => ⟨hkeys i hi, hkeys i hi, hag i hi⟩) a).mp (hm _ (by simp [Cond.conj, hT]))

end


/-! ## A competitor that applies at values applies in a model -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A rule with a `pre` that applies at values applies in a model of `Γc`.** For a rule with
`ruleSorted`, a σ that gives the variables of its left side and conditions values, matches x, makes
the `requires` `true` and `pre` `true`: x's element is in the rule's `applies` pattern. The keys of
the left side's and the conditions' variables and of `pre`'s pattern are in the table. -/
theorem applies_of_values_pp (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hrcP : hasBinder r.pre = true → c.readsConfined = true)
    {x : Config c} {σ : Subst}
    (hσ : c.WellSortedAt r.vars r.leftVars σ) (hpv : PatVal c σ r.lhs x.val)
    (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c r.vars.length σ r.pre true)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (e : Valuation M) :
    (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x.val) := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hIΓ
  obtain ⟨hlhs, hreqK, -, -⟩ := Semantics.ruleSorted_parts c hs
  have hs' := hs
  simp only [Semantics.ruleSorted, Bool.and_eq_true] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hokP⟩, -⟩, -⟩, hbdP⟩, -⟩, -⟩ := hs'
  have hreqS : ∀ t, r.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool :=
    fun t ht => by rw [ht] at hreqK; simpa [reqOK] using hreqK
  let vs := canonVars c r.vars
  let n := r.vars.length
  let C := srtOf c topCellSort
  let l := (List.range n).filter r.leftVars.contains
  have hl : ∀ i ∈ l, i < n := fun i hi => List.mem_range.mp (List.mem_filter.mp hi).1
  have hlm : ∀ i ∈ l, i ∈ r.leftVars := fun i hi => by simpa using (List.mem_filter.mp hi).2
  have hml : ∀ i < n, i ∈ r.leftVars → i ∈ l := fun i hi hil =>
    List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hil⟩
  rw [Model.applies_eqPP r]
  have hnd : (((l.map (vs.getD · default)).map KoreAML.Var.kore).map fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
    rw [List.map_map, List.map_map]
    refine Model.nodup_map_of_injOn _ (fun i hi j hj he => ?_) (List.nodup_range.filter _)
    exact canonKey_inj (hl i hi) (hl j hj) (ev_inj (hkeys i (hl i hi) (hlm i hi)) (hkeys j (hl j hj) (hlm j hj)) he)
  have hsrt : ∀ b ∈ (l.map (vs.getD · default)).map KoreAML.Var.kore, ∃ n, b.sort = KoreAML.srt n := fun b hb => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    show ∃ n, ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt n
    rw [canonVars_getD c (hl i hi)]; exact ⟨_, rfl⟩
  -- σ on the left side's and conditions' variables, x's value elsewhere
  let σ' : Subst := (List.range n).map fun i => (i, if r.leftVars.contains i then (σ.lookup i).getD default else x.val)
  have hσ'l : ∀ i < n, σ'.lookup i = some (if r.leftVars.contains i then (σ.lookup i).getD default else x.val) :=
    fun i hi => by
      simp only [σ']
      rw [List.range_eq_range', lookup_range', if_pos ⟨Nat.zero_le _, by omega⟩]
  have hσv : ∀ i < n, i ∈ r.leftVars → ∃ w, σ.lookup i = some w ∧ c.sortOf w = some (r.vars.getD i 0) :=
    fun i hi hil => hσ i hil _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
  have hσ'L : ∀ i < n, i ∈ r.leftVars → σ'.lookup i = σ.lookup i := fun i hi hil => by
    obtain ⟨w, hw, -⟩ := hσv i hi hil
    rw [hσ'l i hi, if_pos (by simpa using hil), hw, Option.getD_some]
  have hσ'O : ∀ i < n, i ∉ r.leftVars → σ'.lookup i = some x.val := fun i hi hil => by
    rw [hσ'l i hi, if_neg (by simpa using hil)]
  have hvsl : vs.length = r.leftSorts.length := by rw [canonVars_length, Rule.leftSorts_length]
  have hσ' : c.WellSorted r.leftSorts σ' := fun i s hs' => by
    have hlt : i < n := by have := (List.getElem?_eq_some_iff.mp hs').1; rwa [Rule.leftSorts_length] at this
    by_cases hil : i ∈ r.leftVars
    · obtain ⟨w, hw, hws⟩ := hσv i hlt hil
      refine ⟨w, by rw [hσ'L i hlt hil, hw], ?_⟩
      rw [Rule.leftSorts_getElem? hlt hil] at hs'
      rw [hws, List.getD_eq_getElem?_getD, hs', Option.getD_some]
    · refine ⟨x.val, hσ'O i hlt hil, ?_⟩
      have := Rule.leftSorts_getD_off hlt hil
      rw [List.getD_eq_getElem?_getD, hs', Option.getD_some] at this
      rw [this]; exact x.property
  have hltL : ∀ i ∈ varOccs r.lhs, i < n := Exec.sortOfTerm_vars hlhs
  have hlhsL : ∀ i ∈ varOccs r.lhs, i ∈ r.leftVars := fun i hi => List.mem_append_left _ hi
  have hpv' : PatVal c σ' r.lhs x.val := PatVal.congr_lookup hpv fun j hj => hσ'L j (hltL j hj) (hlhsL j hj)
  have hreqLt : ∀ t, r.req = some t → ∀ i ∈ varOccs t, i < n ∧ i ∈ r.leftVars := fun t ht i hi =>
    ⟨Exec.sortOfTerm_vars (hreqS t ht) i hi, Rule.req_leftVars ht i hi⟩
  have hreq' : ∀ t, r.req = some t → EvalTerm c σ' t (some (bool true)) := fun t ht =>
    Exec.EvalTerm.congr (hreq t ht) fun i hi => (hσ'L i (hreqLt t ht i hi).1 (hreqLt t ht i hi).2).symm
  have hlhs' : sortOfTerm c.patCtxAll r.leftSorts r.lhs = some topCellSort := by
    rw [sortOfTerm_congr r.lhs fun i hi => Rule.leftSorts_getElem? (hltL i hi) (hlhsL i hi)]; exact hlhs
  have hreqS' : ∀ t, r.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.leftSorts t = some Srt.bool :=
    fun t ht => by
      rw [sortOfTerm_congr t fun i hi => Rule.leftSorts_getElem? (hreqLt t ht i hi).1 (hreqLt t ht i hi).2]
      exact hreqS t ht
  -- the valuation: σ''s elements at the binders, and x's element at the other variables
  let f : Nat → M := fun j => elemOf c I ((σ'.lookup j).getD default)
  let e3 := setV c tbl r.vars r.leftVars f e
  let e4 := fillV c tbl r.vars r.leftVars (elemOf c I x.val) e3
  have h4 : ∀ i < n, e4.evalEvar (tbl.ev (keyAt vs i)) = f i := fun i hi => by
    by_cases hil : i ∈ r.leftVars
    · show (fillV c tbl r.vars r.leftVars _ e3).evalEvar (tbl.ev (canonKey c r.vars i)) = _
      rw [fillV_off hkeys hi hil]; exact setV_on hkeys hi hil
    · show (fillV c tbl r.vars r.leftVars _ e3).evalEvar (tbl.ev (canonKey c r.vars i)) = _
      rw [fillV_on hi hil]; show _ = elemOf c I ((σ'.lookup i).getD default)
      rw [hσ'O i hi hil, Option.getD_some]
  have hag : Agrees c I tbl vs σ' e4 := fun i v hi hv m => by
    rw [canonVars_length] at hi
    have hvs' := hσ' i (r.leftSorts.getD i 0)
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [Rule.leftSorts_length]; exact hi)]; rfl)
    obtain ⟨w, hw, hws⟩ := hvs'
    rw [hv] at hw; cases hw
    show m = e4.evalEvar (tbl.ev (keyAt vs i)) ↔ _
    rw [h4 i hi]; show m = elemOf c I ((σ'.lookup i).getD default) ↔ _
    rw [hv, Option.getD_some]
    exact ((elemOf_spec hIΓ hws e4).1 m).symm
  have hxs := elemOf_spec hIΓ x.property e4
  have hlx4 := ((patVal_den4 hIΓ hnn.1 hph hsc.trans hσ' hvsl hag hpv' (Semantics.lhs_nf OvlOK.ok hr hlhs')).2 _).mpr ((hxs.1 _).mpr rfl)
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hIΓ (top_numbered (c := c))
  have hreq4 := reqPat_holds hIΓ (vs := vs) (q := r.req) (fun t ht b =>
    evalTerm_den4Cl hIΓ hnn hsc hph (clauseOpenFacts_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) (neg_of_coreCl hI (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw) (hreq' t ht) fns_headsOK hσ' hvsl hag (hreqS' t ht) b)
    (by have := hxs.2; unfold srtOf; rw [trSort_srt]; exact this)
  -- e3 agrees with e4 at the left side's and conditions' variables, and with e off the binders
  have h34 : ∀ i < n, i ∈ r.leftVars → e4.evalEvar (tbl.ev (keyAt vs i)) = e3.evalEvar (tbl.ev (keyAt vs i)) :=
    fun i hi hil => fillV_off hkeys hi hil
  -- `pre` is `true` at σ, which e3 reads at `pre`'s variables
  have hpre3 : ∀ φ ∈ Cond.conj c vs C r.pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e3 (elemOf c I x.val) := by
    have hreads : Reads c I r.vars (fun i => i ∈ varOccsCond r.vars.length r.pre) σ tbl e3 := fun i hi => by
      have hlt := varOccsCond_lt_twoT r.pre hokP i hi
      have hil : i ∈ r.leftVars := List.mem_append_right _ (List.mem_append_right _ hi)
      obtain ⟨w, hw, hws⟩ := hσv i hlt hil
      refine ⟨hlt, hkeys i hlt hil, w, hw, hws, fun m => ?_⟩
      have hon : e3.evalEvar (tbl.ev (canonKey c r.vars i)) = elemOf c I w := by
        show (setV c tbl r.vars r.leftVars f e).evalEvar (tbl.ev (canonKey c r.vars i)) = _
        rw [setV_on hkeys hlt hil]
        show elemOf c I ((σ'.lookup i).getD default) = _
        rw [hσ'L i hlt hil, hw, Option.getD_some]
      rw [hon]
      exact ((elemOf_spec hIΓ hws e3).1 m).symm
    exact (conj_iff_holdsPP h hI hcw hokP hbdP hrcP hreads hkP (inh_top_PP hIΓ x tbl e3) hpre).mpr rfl
  refine existsAll_intro_at hD _ e e3 _ hnd hsrt (fun z hz => ?_) rfl (fun b hb k hk => ?_) ?_
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
    show InS I _ (e3.evalEvar (tbl.ev (canonKey c r.vars i)))
    rw [setV_on hkeys (hl i hil) (hlm i hil)]
    obtain ⟨w, hw, hws⟩ := hσv i (hl i hil) (hlm i hil)
    show InS I _ (elemOf c I ((σ'.lookup i).getD default))
    rw [hσ'L i (hl i hil) (hlm i hil), hw, Option.getD_some]
    exact (inS_iff e3).mp (elemOf_spec hIΓ hws e3).2
  · refine (interp_bodyPPI _ _ _ _ _ _).mpr
      ⟨(tr_kore_congr r.lhs (fun i hi => h34 i (hltL i hi) (hlhsL i hi)) _).mp hlx4, ?_, hpre3⟩
    cases hq : r.req with
    | none =>
      rw [hq] at hreq4
      have hT : ∀ (tb : VarTable) (ev : Valuation M),
          (KoreAML.tr ⟨tb, []⟩ (reqPat C none)).interpret I ev (elemOf c I x.val) ↔
          (KoreAML.inhOf (KoreAML.sym (.sort ("Sort" ++ c.sortName topCellSort)))).interpret I ev (elemOf c I x.val) :=
        fun tb ev => by
          simp only [reqPat]
          rw [KoreAML.tr, KoreAML.interp_sTop hD (by unfold C srtOf; rw [trSort_srt]; rfl)]
          unfold C srtOf; rw [trSort_srt]
      exact (hT tbl e3).mpr (((KoreAML.Closed.sym _).app (KoreAML.Closed.sym _)).interp e4 e3 _ |>.mp ((hT tbl e4).mp hreq4))
    | some t =>
      rw [hq] at hreq4
      exact (tr_reqPat_congr hIΓ (fun i hi => h34 i (hreqLt t hq i hi).1 (hreqLt t hq i hi).2) _).mp hreq4

/-- **A competitor with a `pre` that does not apply in a model does not apply at values**, where its
`requires` has a result and its `pre` a truth value at each match (the first conjunct of
`StepDecided` for the rule): for a rule with `ruleSorted`, if x's element is not in its `applies`
pattern at a valuation, then `NotApplies`. -/
theorem notApplies_of_not_applies_pp (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hrcP : hasBinder r.pre = true → c.readsConfined = true) {x : Config c}
    (hd : ∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x.val →
      (∀ t, r.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c r.vars.length σ r.pre b)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (e : Valuation M)
    (hna : ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x.val)) :
    NotApplies c r x.val := by
  intro σ hσ hpv
  obtain ⟨hdq, b, hb⟩ := hd σ hσ hpv
  have key : (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) → RuleReqFails c σ r := fun hq => by
    cases b with
    | true => exact absurd (applies_of_values_pp h hI hcw hs hrcP hσ hpv hq hb hkeys hkP e) hna
    | false => exact .pre hb
  cases ht : r.req with
  | none => exact key fun t h' => by rw [ht] at h'; cases h'
  | some t =>
    obtain ⟨v, hv⟩ := hdq t ht
    by_cases hvt : v = some (bool true)
    · refine key fun t' h' => ?_
      rw [ht] at h'; cases h'; rw [hvt] at hv; exact hv
    · exact RuleReqFails.intro ht hv hvt

end


/-! ## A competitor that does not apply does not apply in a model -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A competitor with a `pre` that does not apply does not apply in a model of `Γc`.** For a rule
with `ruleSorted` and `rulePlainPP` and a rule of a larger priority, where its conditions are
decided when `needsWitness` holds: if it does not apply to x at values, x's element is not in its
`applies` pattern. The keys of the left side's and the conditions' variables and of `pre`'s pattern
are in the table; a `pre` with a binder is read where the definition reads a confined sort. -/
theorem not_applies_of_notApplies_pp (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainPP r = true)
    (hlarger : c.rules.any (fun r'' => r.prio < r''.prio) = true)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true)
    (hw : r.needsWitness c = true → r.CondDecided c)
    {x : Config c} (hna : NotApplies c r x.val)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (e : Valuation M) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x.val) := by
  intro hm
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hIΓ
  obtain ⟨hlhs, hreqK, -, -⟩ := Semantics.ruleSorted_parts c hs
  have hs' := hs
  simp only [Semantics.ruleSorted, Bool.and_eq_true] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hokP⟩, -⟩, -⟩, hbdP⟩, -⟩, -⟩ := hs'
  have hreqS : ∀ t, r.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool :=
    fun t ht => by rw [ht] at hreqK; simpa [reqOK] using hreqK
  let vs := canonVars c r.vars
  let n := r.vars.length
  let C := srtOf c topCellSort
  let l := (List.range n).filter r.leftVars.contains
  have hl : ∀ i ∈ l, i < n := fun i hi => List.mem_range.mp (List.mem_filter.mp hi).1
  have hlm : ∀ i ∈ l, i ∈ r.leftVars := fun i hi => by simpa using (List.mem_filter.mp hi).2
  have hml : ∀ i < n, i ∈ r.leftVars → i ∈ l := fun i hi hil =>
    List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hil⟩
  have hpreL : ∀ i ∈ varOccsCond n r.pre, i < n ∧ i ∈ r.leftVars := fun i hi =>
    ⟨varOccsCond_lt_twoT r.pre hokP i hi, List.mem_append_right _ (List.mem_append_right _ hi)⟩
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
  obtain ⟨hlx, hreqx, hprex⟩ := (interp_bodyPPI _ _ _ _ _ _).mp hbody
  -- the binders are in their sorts
  have hinL : ∀ i < n, i ∈ r.leftVars → InS I (c.sortName (r.vars.getD i 0)) (e'.evalEvar (tbl.ev (keyAt vs i))) :=
    fun i hi hil => hguard _ (List.mem_map_of_mem (List.mem_map_of_mem (hml i hi hil))) _
      (by show (vs.getD i default).kore.sort = _; rw [canonVars_getD c hi]; rfl)
  -- the other variables: the configuration sort and x's element
  let a := elemOf c I x.val
  let e1 := fillV c tbl r.vars r.leftVars a e'
  have hoff1 : ∀ i < n, i ∈ r.leftVars → e1.evalEvar (tbl.ev (keyAt vs i)) = e'.evalEvar (tbl.ev (keyAt vs i)) :=
    fun i hi hil => fillV_off hkeys hi hil
  have hvsl : vs.length = r.leftSorts.length := by rw [canonVars_length, Rule.leftSorts_length]
  have hwitF : ∀ i < n, i ∉ r.leftVars → Witnessed c I tbl vs r.leftSorts e1 i := fun i hi hil =>
    ⟨x.val, by rw [Rule.leftSorts_getD_off hi hil]; exact x.property, (fillV_on hi hil).symm⟩
  have hin1 : ∀ i < r.leftSorts.length, InS I (c.sortName (r.leftSorts.getD i 0)) (e1.evalEvar (tbl.ev (keyAt vs i))) :=
    fun i hi => by
      rw [Rule.leftSorts_length] at hi
      by_cases hil : i ∈ r.leftVars
      · rw [Rule.leftSorts_getD hi hil, hoff1 i hi hil]; exact hinL i hi hil
      · obtain ⟨v, hv, he⟩ := hwitF i hi hil
        rw [← he]; exact (inS_iff e1).mp (elemOf_spec hIΓ hv e1).2
  have hlhsL : ∀ i ∈ varOccs r.lhs, i ∈ r.leftVars := fun i hi => List.mem_append_left _ hi
  have hltL : ∀ i ∈ varOccs r.lhs, i < n := Exec.sortOfTerm_vars hlhs
  have hlx1 := (tr_kore_congr r.lhs (fun i hi => (hoff1 i (hltL i hi) (hlhsL i hi)).symm) _).mp hlx
  have hreq1 : ∀ t, r.req = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat C (some (Term.kore c vs t)))).interpret I e1
      (elemOf c I x.val) := fun t ht => by
    rw [ht] at hreqx
    exact (tr_reqPat_congr hIΓ (fun i hi => (hoff1 i (Exec.sortOfTerm_vars (hreqS t ht) i hi)
      (Rule.req_leftVars ht i hi)).symm) _).mp hreqx
  -- `pre`'s conjuncts read e1 as e'
  have hpre1 : ∀ φ ∈ Cond.conj c vs C r.pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e1 (elemOf c I x.val) :=
    conj_congrPP hD hokP hkP (fun i hi => hkeys i (hpreL i hi).1 (hpreL i hi).2)
      (fun i hi => (hoff1 i (hpreL i hi).1 (hpreL i hi).2).symm) hprex
  have hsortsL : ∀ (t : Term), (∀ i ∈ varOccs t, i < n ∧ i ∈ r.leftVars) → ∀ (x' : TermCtx),
      sortOfTerm x' r.leftSorts t = sortOfTerm x' r.vars t := fun t ht x' =>
    sortOfTerm_congr t fun i hi => Rule.leftSorts_getElem? (ht i hi).1 (ht i hi).2
  have hlhs' : sortOfTerm c.patCtxAll r.leftSorts r.lhs = some topCellSort := by
    rw [hsortsL r.lhs (fun i hi => ⟨hltL i hi, hlhsL i hi⟩)]; exact hlhs
  have hreqS' : ∀ t, r.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.leftSorts t = some Srt.bool :=
    fun t ht => by
      rw [hsortsL t (fun i hi => ⟨Exec.sortOfTerm_vars (hreqS t ht) i hi, Rule.req_leftVars ht i hi⟩)]
      exact hreqS t ht
  -- a valuation of the left side's variables in their sorts where every variable is a value's,
  -- x's element in `pre`'s conjuncts, contradicts `NotApplies`
  have hwsAt : ∀ σ, c.WellSorted r.leftSorts σ → c.WellSortedAt r.vars r.leftVars σ := fun σ hσ i hi s hs => by
    have hlt : i < n := (List.getElem?_eq_some_iff.mp hs).1
    exact hσ i s (by rw [Rule.leftSorts_getElem? hlt hi]; exact hs)
  have hfin : ∀ (e2 : Valuation M), (∀ i < r.leftSorts.length, Witnessed c I tbl vs r.leftSorts e2 i) →
      (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs r.lhs)).interpret I e2 (elemOf c I x.val) →
      (∀ t, r.req = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat C (some (Term.kore c vs t)))).interpret I e2
        (elemOf c I x.val) ∨ EvalTerm c (substOf c I tbl vs r.leftSorts e2) t (some (bool true))) →
      (∀ φ ∈ Cond.conj c vs C r.pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e2 (elemOf c I x.val)) → False := by
    intro e2 hwit2 hl2 hr2 hpre2
    have hin2 : ∀ i < r.leftSorts.length, InS I (c.sortName (r.leftSorts.getD i 0)) (e2.evalEvar (tbl.ev (keyAt vs i))) :=
      fun i hi => by obtain ⟨v, hv, he⟩ := hwit2 i hi; rw [← he]; exact (inS_iff e2).mp (elemOf_spec hIΓ hv e2).2
    obtain ⟨hpv, -⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 hvsl hin2 (collPat_of_sorted hph' hlhs')
      (Semantics.lhs_nf OvlOK.ok hr hlhs') x.property hl2
    obtain ⟨hσ2, hag2⟩ := substOf_ok hIΓ hg hsc.trans hvsl hwit2
    obtain ⟨t, v, ht, he, hv⟩ : ∃ t v, r.req = some t ∧ EvalTerm c (substOf c I tbl vs r.leftSorts e2) t v ∧
        v ≠ some (bool true) := by
      cases hna _ (hwsAt _ hσ2) hpv with
      | intro ht he hv => exact ⟨_, _, ht, he, hv⟩
      | pre hf =>
        -- `pre` false: x's element is not in its pattern
        have hreads : Reads c I r.vars (fun i => i ∈ varOccsCond r.vars.length r.pre)
            (substOf c I tbl vs r.leftSorts e2) tbl e2 := reads_of_agreesAt hag2 fun i hi => by
          obtain ⟨hlt, hil⟩ := hpreL i hi
          obtain ⟨v, hv, hsv⟩ := hσ2 i (r.vars.getD i 0) (by
            rw [Rule.leftSorts_getElem? hlt hil, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl)
          exact ⟨hlt, hkeys i hlt hil, v, hv, hsv⟩
        exact Bool.noConfusion ((conj_iff_holdsPP h hI hcw hokP hbdP hrcP hreads hkP (inh_top_PP hIΓ x tbl e2) hf).mp
          hpre2)
    have hden := evalTerm_den4Cl hIΓ hnn hsc hph (clauseOpenFacts_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) (neg_of_coreCl hI (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw) he fns_headsOK hσ2 hvsl hag2 (hreqS' t ht)
    rcases hr2 t ht with hm2 | htrue
    · obtain ⟨σC, hσC1, hσC2⟩ := sortSing hIΓ (top_numbered (c := c))
      exact reqFalse_empty hIΓ (S' := C) (fun a => by unfold C srtOf; rw [trSort_srt]; exact hσC1 a) hσC2 hv
        (fun u hu => EvalTerm.sorted hsc he fns_headsOK hσ2 (hreqS' t ht) hu) hden _ hm2
    · have hdenT := evalTerm_den4Cl hIΓ hnn hsc hph (clauseOpenFacts_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) (neg_of_coreCl hI (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw) htrue fns_headsOK hσ2 hvsl hag2
        (hreqS' t ht)
      have hTm : Res c I e2 (some (bool true)) (elemOf c I (bool true)) :=
        ((elemOf_spec hIΓ (sortOf_bool true) e2).1 _).mpr rfl
      have hVm := (hden _).mp ((hdenT _).mpr hTm)
      cases v with
      | none => exact hVm
      | some u =>
        have hu := EvalTerm.sorted hsc he fns_headsOK hσ2 (hreqS' t ht) rfl
        have heq : elemOf c I (bool true) = elemOf c I u := ((elemOf_spec hIΓ hu e2).1 _).mp hVm
        exact hv (congrArg some (values_apart hIΓ hg hsc.trans (apartSort_of_sorted hg hu) hu (sortOf_bool true)
          heq.symm))
  -- the open condition variables, by the competition conjunct
  have hp' := hp
  simp only [Semantics.rulePlainPP, Bool.and_eq_true, Bool.or_eq_true] at hp'
  obtain ⟨-, hcomp⟩ := hp'
  have hlarger' : (!c.rules.any fun r'' => r.prio < r''.prio) = false := by rw [hlarger]; rfl
  rw [hlarger'] at hcomp
  -- a variable of the left side's conditions that the left side does not hold is open
  have hopen : ∀ i < n, i ∈ r.leftVars → i ∉ varOccs r.lhs → i ∈ r.openCondVars := fun i hi hil hnl => by
    have hcv : i ∈ r.condVars := by
      rcases List.mem_append.mp hil with h' | h'
      · exact absurd h' hnl
      · exact h'
    refine List.mem_filter.mpr ⟨?_, by simpa using hcv⟩
    simp only [Rule.opens, List.mem_filter, List.mem_range]; exact ⟨hi, by simpa using hnl⟩
  obtain ⟨-, hwitL⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 hvsl hin1 (collPat_of_sorted hph' hlhs')
    (Semantics.lhs_nf OvlOK.ok hr hlhs') x.property hlx1
  by_cases hconf : r.openCondVars.all (fun i => (r.vars[i]?.map c.confined).getD false) = true
  · -- every open condition variable is of a confined sort: it is a value's
    refine hfin e1 (fun i hi => ?_) hlx1 (fun t ht => Or.inl (hreq1 t ht)) hpre1
    rw [Rule.leftSorts_length] at hi
    by_cases hil : i ∈ r.leftVars
    · by_cases hL : i ∈ varOccs r.lhs
      · exact hwitL i hL
      · have hoc := hopen i hi hil hL
        obtain ⟨s, hvs⟩ : ∃ s, r.vars[i]? = some s := ⟨_, List.getElem?_eq_getElem hi⟩
        have hcs' : c.confined s = true := by
          have := List.all_eq_true.mp hconf i hoc; rw [hvs] at this; exact this
        have hin' := hin1 i (by rw [Rule.leftSorts_length]; exact hi)
        rw [Rule.leftSorts_getD hi hil, List.getD_eq_getElem?_getD, hvs, Option.getD_some] at hin'
        obtain ⟨v, hv, hden⟩ := confined_value h
          (hrc (List.any_eq_true.mpr ⟨i, (List.mem_filter.mp hoc).1, by rw [hvs]; exact hcs'⟩)) hI hcs' e1 _
          ((inS_iff e1).mpr hin')
        have hel := ((elemOf_spec hIΓ hv e1).1 _).mpr rfl
        exact witnessed_of (by rw [Rule.leftSorts_getElem? hi hil]; exact hvs) hv ((hden _).mp hel)
    · exact hwitF i hi hil
  -- otherwise the conditions are closed, and `needsWitness` holds
  have hconf' : r.openCondVars.all (fun i => (r.vars[i]?.map c.confined).getD false) = false := by
    cases hb : r.openCondVars.all (fun i => (r.vars[i]?.map c.confined).getD false) with
    | false => rfl
    | true => exact absurd hb hconf
  obtain ⟨i0, hi0, -⟩ := List.all_eq_false.mp hconf'
  have hro : r.reqOpen = true := by
    unfold Rule.reqOpen
    cases h' : r.openCondVars with
    | nil => rw [h'] at hi0; cases hi0
    | cons _ _ => rfl
  have hrcl : r.reqClosed = true := by
    rw [hro, hconf'] at hcomp; simpa using hcomp
  have hnw : r.needsWitness c = true := by
    unfold Rule.needsWitness; rw [hro, hrcl, hconf']; rfl
  have hcvl : ∀ j ∈ r.condVars, j ∉ varOccs r.lhs := fun j hj hjl => by
    have hc2 := hrcl
    unfold Rule.reqClosed at hc2
    have := List.all_eq_true.mp hc2 j hj
    rw [List.contains_iff_mem.mpr hjl] at this
    exact absurd this (by decide)
  have hcvn : ∀ j ∈ r.condVars, j < n := fun j hj => by
    rcases List.mem_append.mp hj with hj | hj
    · cases ht : r.req with
      | none => simp [ht] at hj
      | some t =>
        simp only [ht, Option.map_some, Option.getD_some] at hj
        exact Exec.sortOfTerm_vars (hreqS t ht) j hj
    · exact varOccsCond_lt_twoT r.pre hokP j hj
  rcases hw hnw with hW | href
  · -- witnessed: the witness's values at the conditions' variables, x's match elsewhere
    obtain ⟨σw, hσw, hreqw, hprew⟩ := hW
    have hkeysC : ∀ i < r.vars.length, i ∈ r.condVars → canonKey c r.vars i ∈ tbl :=
      fun i hi hc => hkeys i hi (List.mem_append_right _ hc)
    let e2 := setV c tbl r.vars r.condVars (fun j => elemOf c I ((σw.lookup j).getD default)) e1
    have hσwv : ∀ i < n, i ∈ r.condVars → ∃ w, σw.lookup i = some w ∧ c.sortOf w = some (r.vars.getD i 0) :=
      fun i hi hc => hσw i hc _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
    have hon2 : ∀ i < n, i ∈ r.condVars → ∀ w, σw.lookup i = some w →
        e2.evalEvar (tbl.ev (canonKey c r.vars i)) = elemOf c I w := fun i hi hc w hw' => by
      show (setV c tbl r.vars r.condVars _ e1).evalEvar (tbl.ev (canonKey c r.vars i)) = _
      rw [setV_on hkeysC hi hc, hw', Option.getD_some]
    have hwit2 : ∀ i < r.leftSorts.length, Witnessed c I tbl vs r.leftSorts e2 i := fun i hi => by
      rw [Rule.leftSorts_length] at hi
      by_cases hc : i ∈ r.condVars
      · obtain ⟨w, hw', hws⟩ := hσwv i hi hc
        refine ⟨w, by rw [Rule.leftSorts_getD hi (List.mem_append_right _ hc)]; exact hws, ?_⟩
        exact (hon2 i hi hc w hw').symm
      · obtain ⟨v, hv, he⟩ : Witnessed c I tbl vs r.leftSorts e1 i := by
          by_cases hil : i ∈ r.leftVars
          · rcases List.mem_append.mp hil with hL | hL
            · exact hwitL i hL
            · exact absurd hL hc
          · exact hwitF i hi hil
        refine ⟨v, hv, ?_⟩
        show _ = (setV c tbl r.vars r.condVars _ e1).evalEvar (tbl.ev (canonKey c r.vars i))
        rw [setV_off hkeysC hi hc]; exact he
    have hl2 : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs r.lhs)).interpret I e2 (elemOf c I x.val) :=
      (tr_kore_congr r.lhs (fun i hi => (setV_off (f := fun j => elemOf c I ((σw.lookup j).getD default)) hkeysC
        (hltL i hi) (fun hc => hcvl i hc hi)).symm) _).mp hlx1
    -- `pre` holds at σw, which e2 reads at `pre`'s variables
    have hpre2 : ∀ φ ∈ Cond.conj c vs C r.pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e2 (elemOf c I x.val) := by
      have hreads : Reads c I r.vars (fun i => i ∈ varOccsCond r.vars.length r.pre) σw tbl e2 := fun i hi => by
        have hlt := varOccsCond_lt_twoT r.pre hokP i hi
        have hc : i ∈ r.condVars := List.mem_append_right _ hi
        obtain ⟨w, hw', hws⟩ := hσwv i hlt hc
        refine ⟨hlt, hkeysC i hlt hc, w, hw', hws, fun m => ?_⟩
        rw [hon2 i hlt hc w hw']
        exact ((elemOf_spec hIΓ hws e2).1 m).symm
      exact (conj_iff_holdsPP h hI hcw hokP hbdP hrcP hreads hkP (inh_top_PP hIΓ x tbl e2) hprew).mpr rfl
    refine hfin e2 hwit2 hl2 (fun t ht => Or.inr (Exec.EvalTerm.congr (hreqw t ht) fun i hi => ?_)) hpre2
    have hc : i ∈ r.condVars := by
      simp only [Rule.condVars, ht, Option.map_some, Option.getD_some]; exact List.mem_append_left _ hi
    have hi' := hcvn i hc
    obtain ⟨w, hw', hws⟩ := hσwv i hi' hc
    have hin2 : ∀ i < r.leftSorts.length, InS I (c.sortName (r.leftSorts.getD i 0)) (e2.evalEvar (tbl.ev (keyAt vs i))) :=
      fun i hi => by obtain ⟨v, hv, he⟩ := hwit2 i hi; rw [← he]; exact (inS_iff e2).mp (elemOf_spec hIΓ hv e2).2
    have hvi : r.leftSorts[i]? = some (r.vars.getD i 0) := by
      rw [Rule.leftSorts_getElem? hi' (List.mem_append_right _ hc), List.getElem?_eq_getElem hi',
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    rw [hw', substOf_var hIΓ hg hsc.trans hnn.1 hvsl hin2 hvi hws (hon2 i hi' hc w hw').symm]
  · -- refuted: but the conditions hold at the binders
    exact cond_not_refuted_pp h hI hs (fun i hi hc => hkeys i hi (List.mem_append_right _ hc)) hkP
      (fun i hi hc => hinL i hi (List.mem_append_right _ hc)) hreqx hprex href

/-- **A competitor with a `pre`, in a model of `Γc`**: for a rule with `ruleSorted` and
`rulePlainPP` and a rule of a larger priority, its conditions decided when `needsWitness` holds,
where its `requires` has a result and its `pre` a truth value at each match (the first conjunct of
`StepDecided` for the rule), x's element is outside its `applies` pattern (whose body holds
`Cond.kore` of `pre`) exactly where it does not apply to x. -/
theorem applies_iff_pp (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainPP r = true)
    (hlarger : c.rules.any (fun r'' => r.prio < r''.prio) = true)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true)
    (hw : r.needsWitness c = true → r.CondDecided c) {x : Config c}
    (hd : ∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x.val →
      (∀ t, r.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c r.vars.length σ r.pre b)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (e : Valuation M) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x.val) ↔
      NotApplies c r x.val :=
  ⟨notApplies_of_not_applies_pp h hI hcw hs hrcP hd hkeys hkP e,
   fun hna => not_applies_of_notApplies_pp h hI hcw hs hp hlarger hrc hrcP hw hna hkeys hkP e⟩

end

end Faithful

end KCore
