/-
  KCore. The value model satisfies the axiom of a rule whose left side need not bind every
  variable.

  In the value model every element of a sort is a value (`InSort`), so at a valuation that the
  axiom's guards keep in the sorts every variable of the rule is a value, held by the left side or
  not. What is read of the rule is that it is well sorted (`ruleSorted`: each variable occurs in the
  left side, the `requires`, the right side or the `ensures`, and these are sorted) and its
  predicates are `\top` (`rulePlainOpen`); no arm of `rulePlainOpen` is read.

  - `applies_iff_open`: a configuration is in a rule's `applies` pattern exactly where the rule
    applies to it (`RuleApplies`). `applies` binds the variables of the left side and the
    conditions only, which are those `RuleApplies` gives values; the other variables occur nowhere
    in it.
  - `rule_premise_open`: the left part of the rule's axiom holds at a configuration, under a
    valuation reading as a substitution of values, exactly where the left side matches it, the
    `requires` and `ensures` evaluate to `true`, no rule of a smaller priority applies and the right
    side has a value: `StepM`'s premises for the rule. Every variable of the rule is free in it.
  - `sat_rule_open`: the axiom of a rule of the definition holds in the value model.

  These are read at the value model (`stdI`) through its own readers (`tr_pat`, `tr_term`,
  `reqPat_iff`); the lemmas of OpenSuccessor.lean and OpenCompete.lean that take a model of `Γ c`
  are not used here, since the value model is shown to be one from these.
-/
import KcoreSpec.OpenCompete
import KcoreSpec.ExPlain
import KcoreSpec.PredPlain
import KcoreSpec.ModelFns
import KcoreSpec.ModelUndefRhsWitness
import KcoreSpec.ModelJunkWitness
import KcoreSpec.ModelNamesWitness
import KcoreSpec.ModelDupCtorWitness
import KcoreSpec.ModelFnCtorWitness

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-! ## What a well-sorted rule with `rulePlainOpen` says -/

theorem varOccsList_of_memOpen : ∀ {ts : List Term} {t : Term}, t ∈ ts → ∀ {i : Nat}, i ∈ varOccs t →
    i ∈ varOccsList ts
  | [], _, h, _, _ => absurd h List.not_mem_nil
  | _ :: ts, _, h, _, hi => by
    rw [varOccsList]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_append_left _ hi
    · exact List.mem_append_right _ (varOccsList_of_memOpen h hi)

/-- `PatOK` reads its predicate at the pattern's variables only. -/
theorem PatOK.monoOpen {P Q : Nat → Prop} {p : Term} (h : PatOK c P p) (hq : ∀ i ∈ varOccs p, Q i) :
    PatOK c Q p := by
  induction h with
  | var _ => exact .var (hq _ (by simp [varOccs]))
  | dv h' => exact .dv h'
  | inj ha hb _ ih => exact .inj ha hb (ih fun i hi => hq i (by rw [varOccs]; exact hi))
  | as _ _ ih =>
    exact .as (ih fun j hj => hq j (by rw [varOccs]; exact List.mem_append_left _ hj)) (hq _ (by simp [varOccs]))
  | app hk hkn hl hkind hnf _ ih =>
    exact .app hk hkn hl hkind hnf fun t ht => ih t ht fun i hi => hq i (by rw [varOccs]; exact varOccsList_of_memOpen ht hi)

/-- `TermOK` reads its predicate at the term's variables only. -/
theorem TermOK.monoOpen {P Q : Nat → Prop} {t : Term} (h : TermOK c P t) (hq : ∀ i ∈ varOccs t, Q i) :
    TermOK c Q t := by
  induction h with
  | var _ => exact .var (hq _ (by simp [varOccs]))
  | dv h' => exact .dv h'
  | inj ha hb _ ih => exact .inj ha hb (ih fun i hi => hq i (by rw [varOccs]; exact hi))
  | app hk hkn hl _ ih =>
    exact .app hk hkn hl fun t ht => ih t ht fun i hi => hq i (by rw [varOccs]; exact varOccsList_of_memOpen ht hi)

/-- What `ruleSorted` says of a rule with `\top` predicates: its left side, `requires`, `ensures`
and right side are sorted, and each variable occurs in one of them. -/
theorem ruleSorted_partsOpen {r : Rule} (hs : c.ruleSorted r = true) (hp : c.rulePlainOpen r = true) :
    sortOfTerm c.patCtxAll r.vars r.lhs = some topCellSort ∧
      (∀ i < r.vars.length, i ∈ varOccs r.lhs ∨ (∃ t, r.req = some t ∧ i ∈ varOccs t) ∨ i ∈ varOccs r.rhs ∨
        ∃ t, r.ens = some t ∧ i ∈ varOccs t) ∧
      (∀ t, r.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool) ∧
      (∀ t, r.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool) ∧
      sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.rhs = some topCellSort := by
  obtain ⟨-, hpre, hpost⟩ := Semantics.rulePlainOpen_top hp
  have hs' := hs
  simp only [Semantics.ruleSorted, Bool.and_eq_true, beq_iff_eq] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hb⟩, -⟩, -⟩, hreq⟩, -⟩, hens⟩, -⟩, -⟩, -⟩, hrhs⟩ := hs'
  replace hl := sortOfTerm_all_of_nf hl
  refine ⟨hl, fun i hi => ?_, fun t ht => ?_, fun t ht => ?_, hrhs⟩
  · have := List.all_eq_true.mp hb i (List.mem_range.mpr hi)
    simp only [Rule.condVars, hpre, hpost, varOccsCond, List.append_nil, List.contains_iff_mem,
      List.mem_append] at this
    rcases this with ((h1 | h2) | h3) | h4
    · exact Or.inl h1
    · cases hq : r.req with
      | none => rw [hq] at h2; cases h2
      | some t => rw [hq] at h2; exact Or.inr (Or.inl ⟨t, rfl, h2⟩)
    · exact Or.inr (Or.inr (Or.inl h3))
    · cases hq : r.ens with
      | none => rw [hq] at h4; cases h4
      | some t => rw [hq] at h4; exact Or.inr (Or.inr (Or.inr ⟨t, rfl, h4⟩))
  · rw [ht] at hreq; simpa [reqOK] using hreq
  · rw [ht] at hens; simpa [reqOK] using hens

/-- The facts on a rule of a definition that `HypModelCore`'s `sortedOKCl` gives, its predicates
left aside: `ruleSorted` and `rulePlainHO1`. -/
theorem HypModelCore.ruleFactsHO1 (h : HypModelCore c) {r : Rule} (hr : r ∈ c.rules) :
    c.ruleSorted r = true ∧ c.rulePlainHO1 r = true := by
  obtain ⟨-, -, hrs, hrp, -⟩ := Semantics.sortedOKCl_parts h.hyp.1
  exact ⟨List.all_eq_true.mp hrs r hr, Semantics.rulesPlain_iff_held.mp hrp r hr⟩

/-- Where every rule has `rulePlainEx` (a decidable fact of the rules), `HypModelCore` gives
`ruleSorted` and `rulePlainEx` of each rule. -/
theorem HypModelCore.ruleFactsEx_of_all (h : HypModelCore c)
    (hex : c.rules.all c.rulePlainEx = true) :
    ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true := fun _ hr =>
  ⟨(h.ruleFactsHO1 hr).1, List.all_eq_true.mp hex _ hr⟩

mutual
  /-- The variables of a sorted term of a numbered sort have numbered sorts, in a context whose
  heads are kernel symbols and whose subsorts are the definition's. -/
  theorem varOccs_numOpen (h : HypModelCore c) {x : TermCtx} (hx : ∀ k ∈ x.heads, k ∈ kernelSyms c)
      (hsub : ∀ a b, (a, b) ∈ x.subs → (a, b) ∈ c.subsorts) {vars : List Srt} : ∀ (t : Term) {s : Srt},
      sortOfTerm x vars t = some s → s < nRegSorts + c.sortNames.length →
      ∀ i ∈ varOccs t, ∀ s', vars[i]? = some s' → s' < nRegSorts + c.sortNames.length
    | .var j, s, ht, hs, i, hi, s', hs' => by
      rw [varOccs] at hi
      rw [mem_one hi, sortOfTerm_var.mp ht] at hs'
      cases hs'; exact hs
    | .app f ts, s, ht, hs, i, hi, s', hs' => by
      rw [varOccs] at hi
      obtain ⟨k, hk, hargs, _⟩ := sortOfTerm_app.mp ht
      exact varOccsList_numOpen h hx hsub ts hargs
        (fun s0 h0 => h.symSorts (hx _ (lookupSig_spec hk).1) s0 (List.mem_cons_of_mem _ h0)) i hi s' hs'
    | .inj a b t, s, ht, hs, i, hi, s', hs' => by
      rw [varOccs] at hi
      obtain ⟨hab, h', _⟩ := sortOfTerm_inj.mp ht
      exact varOccs_numOpen h hx hsub t h' (h.subSorts (hsub _ _ hab)).1 i hi s' hs'
    | .as t j, s, ht, hs, i, hi, s', hs' => by
      rw [varOccs] at hi
      obtain ⟨hv, h'⟩ := Exec.sortOfTerm_as ht
      rcases List.mem_append.mp hi with hi | hi
      · exact varOccs_numOpen h hx hsub t h' hs i hi s' hs'
      · rw [mem_one hi, hv] at hs'; cases hs'; exact hs
    | .dv _ _, _, _, _, i, hi, _, _ => by rw [varOccs] at hi; cases hi
  theorem varOccsList_numOpen (h : HypModelCore c) {x : TermCtx} (hx : ∀ k ∈ x.heads, k ∈ kernelSyms c)
      (hsub : ∀ a b, (a, b) ∈ x.subs → (a, b) ∈ c.subsorts) {vars : List Srt} : ∀ (ts : List Term) {ss : List Srt},
      sortsOfTerms x vars ts = some ss → (∀ s ∈ ss, s < nRegSorts + c.sortNames.length) →
      ∀ i ∈ varOccsList ts, ∀ s', vars[i]? = some s' → s' < nRegSorts + c.sortNames.length
    | [], _, _, _, i, hi, _, _ => by rw [varOccsList] at hi; cases hi
    | t :: ts, ss, ht, hs, i, hi, s', hs' => by
      rw [varOccsList] at hi
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
      rcases List.mem_append.mp hi with hi | hi
      · exact varOccs_numOpen h hx hsub t h1 (hs s (List.mem_cons_self ..)) i hi s' hs'
      · exact varOccsList_numOpen h hx hsub ts h2 (fun s0 h0 => hs s0 (List.mem_cons_of_mem _ h0)) i hi s' hs'
end

/-- A well-sorted rule's variables with `\top` predicates have numbered sorts: each occurs in its
left side, `requires`, right side or `ensures`. -/
theorem rule_vars_numOpen (h : HypModelCore c) {r : Rule} (hs : c.ruleSorted r = true)
    (hp : c.rulePlainOpen r = true) : ∀ i < r.vars.length, r.vars.getD i 0 < nRegSorts + c.sortNames.length := by
  obtain ⟨hlhs, hocc, hreqs, hens, hrhs⟩ := ruleSorted_partsOpen hs hp
  intro i hi
  have hg : r.vars[i]? = some (r.vars.getD i 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have hx : ∀ k ∈ (c.rhsCtx (c.fns.map Fn.sig)).heads, k ∈ kernelSyms c := fun k hk => rhsHead_kernel fns_headsOK hk
  have hsub : ∀ a b, (a, b) ∈ (c.rhsCtx (c.fns.map Fn.sig)).subs → (a, b) ∈ c.subsorts := fun _ _ h' => h'
  rcases hocc i hi with hL | ⟨t, ht, hit⟩ | hR | ⟨t, ht, hit⟩
  · exact varOccs_num h r.lhs hlhs top_numbered i hL _ hg
  · exact varOccs_numOpen h hx hsub t (hreqs t ht) bool_numbered i hit _ hg
  · exact varOccs_numOpen h hx hsub r.rhs hrhs top_numbered i hR _ hg
  · exact varOccs_numOpen h hx hsub t (hens t ht) bool_numbered i hit _ hg

/-- Subject reduction for a rule with the two facts: its right-hand side evaluated under a
well-sorted σ is, when defined, a configuration. -/
theorem rhs_sorted_open (h : HypModelCore c) {r : Rule} (hs : c.ruleSorted r = true) {σ : Subst}
    (hσ : c.WellSorted r.vars σ) {v : GroundTerm} (he : EvalTerm c σ r.rhs (some v)) :
    c.sortOf v = some topCellSort :=
  EvalTerm.sorted (sortCtx_of_allCl h.hyp.1 h.hyp.2.1 h.ovlCase) he
    (fun k hk => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk; exact ⟨g, List.mem_append_left _ hg, rfl⟩) hσ
    (Semantics.ruleSorted_parts c hs).2.2.2 rfl

/-! ## The configurations a rule applies to -/

/-- The binders of `applies` of a rule with a `\top` premise: the canonical variables of the left
side and the conditions. -/
theorem applies_eqOpen {r : Rule} (hpre : r.pre = .top) :
    applies c r (canonRulePres r) = KoreAML.existsAll (srtOf c topCellSort)
      ((((List.range r.vars.length).filter r.leftVars.contains).map ((canonVars c r.vars).getD · default)).map
        KoreAML.Var.kore)
      (.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.lhs,
        reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars)))]) := by
  rw [applies_eq hpre, filterMap_getElem?_of_lt]
  intro i hi
  rw [canonVars_length]; exact List.mem_range.mp (List.mem_filter.mp hi).1

/-- The key of a variable of a rule's left side or conditions is a variable of its `applies`. -/
theorem varsOf_appliesOpen {r : Rule} (hpre : r.pre = .top) {i : Nat} (hi : i < r.vars.length)
    (hil : i ∈ r.leftVars) : canonKey c r.vars i ∈ KoreAML.varsOf (applies c r (canonRulePres r)) := by
  rw [applies_eqOpen hpre]
  refine varsOf_existsAll_binder _ (List.mem_map_of_mem (List.mem_map_of_mem ?_))
  exact List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hil⟩

/-- A rule's `applies` pattern has no free variable: it binds the variables of its left side and
conditions, the only ones it holds. -/
theorem freeOf_appliesOpen {r : Rule} (hlhs : sortOfTerm c.patCtxAll r.vars r.lhs = some topCellSort)
    (hreqv : ∀ t, r.req = some t → ∀ i ∈ varOccs t, i < r.vars.length) (hpre : r.pre = .top)
    {bound : List KoreAML.VarKey} {k : KoreAML.VarKey}
    (hk : k ∈ KoreAML.freeOf bound (applies c r (canonRulePres r))) : False := by
  rw [applies_eqOpen hpre] at hk
  let vs := canonVars c r.vars
  let l := (List.range r.vars.length).filter r.leftVars.contains
  obtain ⟨bound', hb', hk⟩ := freeOf_existsAll (S := srtOf c topCellSort)
    (body := .and (srtOf c topCellSort) [Term.kore c vs r.lhs, reqPat (srtOf c topCellSort) (r.req.map (Term.kore c vs))])
    ((l.map (vs.getD · default)).map KoreAML.Var.kore) hk
  have hbound : ∀ i < r.vars.length, i ∈ r.leftVars → bound'.contains (canonKey c r.vars i) = true := fun i hi hil =>
    (hb' _).mpr (Or.inl (List.mem_map_of_mem (List.mem_map_of_mem (List.mem_map_of_mem
      (List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hil⟩)))))
  rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList] at hk
  simp only [List.append_nil, List.mem_append] at hk
  rcases hk with hk | hk
  · obtain ⟨hb, i, hi, rfl⟩ := freeOf_kore_bound c vs r.lhs hk
    have h2 : bound'.contains (KoreAML.evarKey (vs.getD i default).kore) = true :=
      hbound i (varOccs_lt r.lhs hlhs i hi) (List.mem_append_left _ hi)
    rw [hb] at h2; cases h2
  · cases hq : r.req with
    | none =>
      rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
    | some t =>
      rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
      rw [KoreAML.freeOf] at hk
      rcases List.mem_append.mp hk with hk | hk
      · obtain ⟨hb, i, hi, rfl⟩ := freeOf_kore_bound c vs t hk
        have h2 : bound'.contains (KoreAML.evarKey (vs.getD i default).kore) = true :=
          hbound i (hreqv t hq i hi) (Rule.req_leftVars hq i hi)
        rw [hb] at h2; cases h2
      · rw [KoreAML.freeOf] at hk; cases hk

/-! ## What a well-sorted rule with `rulePlainEx` says -/

/-- The parts of a well-sorted rule with `\top` predicates, and its existential variables: distinct
variables of the rule that neither the left side nor a condition holds. -/
theorem ruleSorted_partsEx {r : Rule} (hs : c.ruleSorted r = true) (hp : c.rulePlainEx r = true) :
    sortOfTerm c.patCtxAll r.vars r.lhs = some topCellSort ∧
      (∀ i < r.vars.length, i ∈ varOccs r.lhs ∨ (∃ t, r.req = some t ∧ i ∈ varOccs t) ∨ i ∈ varOccs r.rhs ∨
        ∃ t, r.ens = some t ∧ i ∈ varOccs t) ∧
      (∀ t, r.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool) ∧
      (∀ t, r.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool) ∧
      sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.rhs = some topCellSort ∧
      r.exs.Nodup ∧ ∀ i ∈ r.exs, i < r.vars.length ∧ i ∉ varOccs r.lhs ∧ i ∉ r.condVars := by
  obtain ⟨hpre, hpost⟩ := Semantics.rulePlainEx_top hp
  have hs' := hs
  simp only [Semantics.ruleSorted, Bool.and_eq_true, beq_iff_eq] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hb⟩, hnd⟩, hex⟩, hreq⟩, -⟩, hens⟩, -⟩, -⟩, -⟩, hrhs⟩ := hs'
  replace hl := sortOfTerm_all_of_nf hl
  refine ⟨hl, fun i hi => ?_, fun t ht => ?_, fun t ht => ?_, hrhs, (NamesApart.nodupB_iff _).mp hnd,
    fun i hi => ?_⟩
  · have := List.all_eq_true.mp hb i (List.mem_range.mpr hi)
    simp only [Rule.condVars, hpre, hpost, varOccsCond, List.append_nil, List.contains_iff_mem,
      List.mem_append] at this
    rcases this with ((h1 | h2) | h3) | h4
    · exact Or.inl h1
    · cases hq : r.req with
      | none => rw [hq] at h2; cases h2
      | some t => rw [hq] at h2; exact Or.inr (Or.inl ⟨t, rfl, h2⟩)
    · exact Or.inr (Or.inr (Or.inl h3))
    · cases hq : r.ens with
      | none => rw [hq] at h4; cases h4
      | some t => rw [hq] at h4; exact Or.inr (Or.inr (Or.inr ⟨t, rfl, h4⟩))
  · rw [ht] at hreq; simpa [reqOK] using hreq
  · rw [ht] at hens; simpa [reqOK] using hens
  · have := List.all_eq_true.mp hex i hi
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem, Rule.opens, List.mem_filter,
      List.mem_range] at this
    obtain ⟨⟨hlt, hnl⟩, hnc⟩ := this
    refine ⟨hlt, fun h' => ?_, fun h' => ?_⟩
    · simp [h'] at hnl
    · simp [h'] at hnc

/-- A well-sorted rule's variables with `\top` predicates have numbered sorts. -/
theorem rule_vars_numEx (h : HypModelCore c) {r : Rule} (hs : c.ruleSorted r = true)
    (hp : c.rulePlainEx r = true) : ∀ i < r.vars.length, r.vars.getD i 0 < nRegSorts + c.sortNames.length := by
  obtain ⟨hlhs, hocc, hreqs, hens, hrhs, -⟩ := ruleSorted_partsEx hs hp
  intro i hi
  have hg : r.vars[i]? = some (r.vars.getD i 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have hx : ∀ k ∈ (c.rhsCtx (c.fns.map Fn.sig)).heads, k ∈ kernelSyms c := fun k hk => rhsHead_kernel fns_headsOK hk
  have hsub : ∀ a b, (a, b) ∈ (c.rhsCtx (c.fns.map Fn.sig)).subs → (a, b) ∈ c.subsorts := fun _ _ h' => h'
  rcases hocc i hi with hL | ⟨t, ht, hit⟩ | hR | ⟨t, ht, hit⟩
  · exact varOccs_num h r.lhs hlhs top_numbered i hL _ hg
  · exact varOccs_numOpen h hx hsub t (hreqs t ht) bool_numbered i hit _ hg
  · exact varOccs_numOpen h hx hsub r.rhs hrhs top_numbered i hR _ hg
  · exact varOccs_numOpen h hx hsub t (hens t ht) bool_numbered i hit _ hg

/-! ## Readers at T -/

/-- A `requires` or `ensures` at a configuration, read at T: where it is a term, its value under σ
is `true`. -/
theorem reqRead_T (h : HypModelCore c) {T : GroundTerm → GroundTerm → Prop} {P : Nat → Prop}
    {vs : List KoreAML.Var} {tbl : KoreAML.VarTable} {e : Valuation Elem} {σ : Subst}
    (hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v)
    (q : Option Term) (hq : ∀ t, q = some t → TermOK c P t) {x : GroundTerm} (hx : c.sortOf x = some topCellSort) :
    (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (q.map (Term.kore c vs)))).interpret (stdI_T c T) e (.val x) ↔
      ∀ t, q = some t → EvalTerm c σ t (some (bool true)) := by
  cases hq' : q with
  | none =>
    simp only [Option.map_none, reqPat]
    rw [KoreAML.tr, KoreAML.interp_sTop AtT.defOK_std (top_free _), KoreAML.interp_inhOf_of (srtOf_top_den_T h e),
      AtT.inh_srt]
    exact ⟨fun _ _ ht => (by cases ht), fun _ => hx⟩
  | some t =>
    simp only [Option.map_some]
    rw [AtT.reqPat_iff h hvar (hq t hq') (srtOf_top_den_T h e) top_isSort_T]
    constructor
    · rintro ⟨-, hv⟩ t' ht'; cases ht'; exact hv
    · intro hv; exact ⟨(AtT.inh_srt _ _).mpr hx, hv t rfl⟩

/-- **A competitor read at T**: a configuration is in a rule's `applies` pattern exactly where the
rule applies to it, for a rule with `ruleSorted` and `rulePlainEx`, not asked to be one of the
definition's. -/
theorem applies_iff_T (h : HypModelCore c) {T : GroundTerm → GroundTerm → Prop} {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainEx r = true) {tbl : KoreAML.VarTable}
    (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl) (e : Valuation Elem)
    {x : GroundTerm} (hx : c.sortOf x = some topCellSort) :
    (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret (stdI_T c T) e (.val x) ↔
      RuleApplies c r x := by
  have hn := h.namesK
  obtain ⟨hlhs, -, hreqS, -, -⟩ := ruleSorted_partsEx hs hp
  obtain ⟨hpre, -⟩ := Semantics.rulePlainEx_top hp
  have hnum := rule_vars_numEx h hs hp
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
  have hpat : PatOK c P r.lhs :=
    (patOK_of_sorted h (h.ovlOKI.nf_bridge hlhs)).monoOpen fun i hi => ⟨hltL i hi, List.mem_append_left _ hi⟩
  have hreqT : ∀ t, r.req = some t → TermOK c P t := fun t ht =>
    (termOK_of_sorted h fns_headsOK (hreqS t ht)).monoOpen (hreqLt t ht)
  rw [applies_eqOpen hpre]
  constructor
  · intro hm
    obtain ⟨e', -, hguard, hbody⟩ := existsAll_elim AtT.defOK_std _ e _ hnd hsrt hm
    rw [tr_and2, KoreAML.interp_sAnd] at hbody
    obtain ⟨hl', hreq⟩ := hbody
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
    have hσ : c.WellSortedAt r.vars r.leftVars σ := fun i hil s hs' => by
      have hi : i < n := (List.getElem?_eq_some_iff.mp hs').1
      obtain ⟨v, he, hsv⟩ := inSort_val (hin i hi hil)
      refine ⟨v, by rw [substE_lookup hi, he]; rfl, ?_⟩
      rwa [List.getD_eq_getElem?_getD, hs', Option.getD_some] at hsv
    obtain ⟨x', hx', he⟩ := (AtT.tr_pat h hvar hpat _).mp hl'
    cases he
    refine ⟨σ, hσ, hx', fun t ht => ?_, hpre ▸ .top⟩
    rw [ht] at hreq
    simp only [Option.map_some] at hreq
    exact ((AtT.reqPat_iff h hvar (hreqT t ht) (srtOf_top_den_T h e') top_isSort_T _).mp hreq).2
  · rintro ⟨σ, hσ, hp', hq, -⟩
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
    · rw [tr_and2, KoreAML.interp_sAnd]
      refine ⟨(AtT.tr_pat h hvar hpat _).mpr ⟨x, hp', rfl⟩, ?_⟩
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

/-! ## A rule's right side under its binders -/

/-- The binders of a rule's right side: its existential variables, named canonically. -/
def ruleExBinders (c : Semantics) (r : Rule) : List Kore.EVar :=
  r.exs.map fun i => ((canonVars c r.vars).getD i default).kore

/-- The body of a rule's right side whose `post` is `\top`: `rhs ∧ ens`. -/
def ruleRightBody (c : Semantics) (r : Rule) : Kore.Pattern :=
  .and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.rhs,
    reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))]

/-- **The reading of a competitor whose left side need not bind every variable**: a configuration
is in a rule's `applies` pattern exactly when the rule applies to it (`RuleApplies`), for a rule
with `ruleSorted` and `rulePlainOpen`. The rule need not be one of the definition's. -/
theorem applies_iff_open (h : HypModelCore c) {r : Rule} (hs : c.ruleSorted r = true)
    (hp : c.rulePlainOpen r = true) {tbl : KoreAML.VarTable}
    (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl) (e : Valuation Elem)
    {x : GroundTerm} (hx : c.sortOf x = some topCellSort) :
    (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret (stdI c) e (.val x) ↔ RuleApplies c r x :=
  applies_iff_T (T := StepM c) h hs (Semantics.rulePlainOpen_iff_ex.mp hp).1 hkeys e hx

/-! ## A rule's axiom -/

theorem freeOf_and_memOpen {S : Kore.KSort} {p : Kore.Pattern} {ps : List Kore.Pattern} {k : KoreAML.VarKey}
    (hp : p ∈ ps) (hk : k ∈ KoreAML.freeOf [] p) : k ∈ KoreAML.freeOf [] (.and S ps) := by
  rw [KoreAML.freeOf]
  induction ps with
  | nil => exact absurd hp List.not_mem_nil
  | cons q qs ih =>
    rw [KoreAML.freeOfList]
    rcases List.mem_cons.mp hp with rfl | hp
    · exact List.mem_append_left _ hk
    · exact List.mem_append_right _ (ih hp)

/-- The keys of a rule's variables are free in, and variables of, a conjunction holding its left
side, its `requires` and the definedness of its right side. -/
theorem rule_keys_open {r : Rule} (hs : c.ruleSorted r = true) (hp : c.rulePlainOpen r = true)
    {ps : List Kore.Pattern}
    (h1 : Term.kore c (canonVars c r.vars) r.lhs ∈ ps)
    (h2 : reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars))) ∈ ps)
    (h3 : .ceil (srtOf c topCellSort) (srtOf c topCellSort) (.and (srtOf c topCellSort)
      [Term.kore c (canonVars c r.vars) r.rhs,
        reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))]) ∈ ps) :
    ∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.freeOf [] (.and (srtOf c topCellSort) ps) ∧
      canonKey c r.vars i ∈ KoreAML.varsOf (.and (srtOf c topCellSort) ps) := by
  obtain ⟨-, hocc, -, -, -⟩ := ruleSorted_partsOpen hs hp
  let vs := canonVars c r.vars
  let C := srtOf c topCellSort
  -- a variable of the right side or the `ensures`, under the definedness
  have hceil : ∀ {k : KoreAML.VarKey} {q : Kore.Pattern},
      q ∈ [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))] →
      k ∈ KoreAML.freeOf [] q → k ∈ KoreAML.varsOf q →
      k ∈ KoreAML.freeOf [] (.and C ps) ∧ k ∈ KoreAML.varsOf (.and C ps) := fun hq hf hv => by
    refine ⟨freeOf_and_memOpen h3 ?_, varsOf_and_mem h3 ?_⟩
    · rw [KoreAML.freeOf]; exact freeOf_and_memOpen hq hf
    · rw [KoreAML.varsOf]; exact List.mem_append_right _ (varsOf_and_mem hq hv)
  have hreqK : ∀ {k : KoreAML.VarKey} {p : Kore.Pattern}, k ∈ KoreAML.freeOf [] p → k ∈ KoreAML.varsOf p →
      k ∈ KoreAML.freeOf [] (reqPat C (some p)) ∧ k ∈ KoreAML.varsOf (reqPat C (some p)) := fun hf hv => by
    simp only [reqPat]
    rw [KoreAML.freeOf, KoreAML.varsOf]
    exact ⟨List.mem_append_left _ hf, List.mem_append_left _ (List.mem_append_right _ hv)⟩
  intro i hi
  rcases hocc i hi with hL | ⟨t, ht, hit⟩ | hR | ⟨t, ht, hit⟩
  · exact ⟨freeOf_and_memOpen h1 (kore_freeOf c vs r.lhs hL), varsOf_and_mem h1 (varsOf_kore c vs r.lhs hL)⟩
  · rw [ht] at h2
    obtain ⟨hf, hv⟩ := hreqK (kore_freeOf c vs t hit) (varsOf_kore c vs t hit)
    exact ⟨freeOf_and_memOpen h2 hf, varsOf_and_mem h2 hv⟩
  · exact hceil (List.mem_cons_self ..) (kore_freeOf c vs r.rhs hR) (varsOf_kore c vs r.rhs hR)
  · have hq : reqPat C (r.ens.map (Term.kore c vs)) = reqPat C (some (Term.kore c vs t)) := by rw [ht]; rfl
    obtain ⟨hf, hv⟩ := hreqK (kore_freeOf c vs t hit) (varsOf_kore c vs t hit)
    rw [← hq] at hf hv
    exact hceil (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hf hv

/-- **The left part of a rule's axiom, read in the value model.** For a rule with `ruleSorted` and
`rulePlainOpen` (not asked to be one of the definition's), the axiom is `\rewrites(L, R)` with R its
right side and `ensures`, and every variable of the rule free in L. Under a valuation that reads as
a substitution σ of values at every variable, a configuration x is in L exactly where `StepM`'s
premises hold of the rule at x under σ: the left side matches x, the `requires` and `ensures`
evaluate to `true`, no rule of a smaller priority applies, and the right side has a value. -/
theorem rule_premise_open (h : HypModelCore c) {r : Rule} (hs : c.ruleSorted r = true)
    (hp : c.rulePlainOpen r = true)
    (hrules : ∀ r' ∈ c.rules, c.ruleSorted r' = true ∧ c.rulePlainEx r' = true) :
    ∃ L, prioRuleK c r = .rewrites (srtOf c topCellSort) L (.and (srtOf c topCellSort)
        [Term.kore c (canonVars c r.vars) r.rhs,
          reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))]) ∧
      (∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.freeOf [] L ∧ canonKey c r.vars i ∈ KoreAML.varsOf L) ∧
      ∀ (tbl : KoreAML.VarTable) (e : Valuation Elem) (σ : Subst) (x : GroundTerm), (∀ k ∈ KoreAML.varsOf L, k ∈ tbl) →
        c.WellSorted r.vars σ → c.sortOf x = some topCellSort →
        (∀ i, i < r.vars.length → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c r.vars) i)).interpret
          (stdI c) e m ↔ ∃ v, σ.lookup i = some v ∧ m = .val v) →
        ((KoreAML.tr ⟨tbl, []⟩ L).interpret (stdI c) e (.val x) ↔
          PatVal c σ r.lhs x ∧ (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
          (∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x) ∧
          ∃ y, EvalTerm c σ r.rhs (some y) ∧ ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) := by
  obtain ⟨hlhs, -, hreqs, hensS, hrhss⟩ := ruleSorted_partsOpen hs hp
  obtain ⟨hex₀, hpre₀, hpost₀⟩ := Semantics.rulePlainOpen_top hp
  have hpat := patOK_of_sorted h (h.ovlOKI.nf_bridge hlhs)
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  let R : Kore.Pattern := .and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]
  -- the parts of the left side, each read
  have hreadL : ∀ (tbl : KoreAML.VarTable) (e : Valuation Elem) (σ : Subst) (x : GroundTerm),
      (∀ i, i < r.vars.length → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI c) e m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v) →
      ((KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs r.lhs)).interpret (stdI c) e (.val x) ↔ PatVal c σ r.lhs x) := by
    intro tbl e σ x hvar
    rw [tr_pat h hvar hpat]
    constructor
    · rintro ⟨v, hv, he⟩; cases he; exact hv
    · intro hv; exact ⟨x, hv, rfl⟩
  have hreadQ : ∀ (tbl : KoreAML.VarTable) (e : Valuation Elem) (σ : Subst) (x : GroundTerm),
      c.sortOf x = some topCellSort → ∀ (q : Option Term), (∀ t, q = some t →
        sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool) →
      (∀ i, i < r.vars.length → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI c) e m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v) →
      ((KoreAML.tr ⟨tbl, []⟩ (reqPat C (q.map (Term.kore c vs)))).interpret (stdI c) e (.val x) ↔
        ∀ t, q = some t → EvalTerm c σ t (some (bool true))) :=
    fun tbl e σ x hx q hqs hvar =>
      reqRead_T (T := StepM c) h hvar q (fun t ht => termOK_of_sorted h fns_headsOK (hqs t ht)) hx
  have hreadCeil : ∀ (tbl : KoreAML.VarTable) (e : Valuation Elem) (σ : Subst) (x : GroundTerm),
      c.WellSorted r.vars σ → c.sortOf x = some topCellSort →
      (∀ i, i < r.vars.length → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI c) e m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v) →
      ((KoreAML.tr ⟨tbl, []⟩ (.ceil C C R)).interpret (stdI c) e (.val x) ↔
        ∃ y, EvalTerm c σ r.rhs (some y) ∧ ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) := by
    intro tbl e σ x hσ hx hvar
    have hrd := tr_term h hvar (termOK_of_sorted h fns_headsOK hrhss)
    rw [KoreAML.tr, KoreAML.interp_sCeil defOK_std sat_ceilDef (srtOf_top_den h e) (srtOf_top_den h e)
      top_isSort top_isSort (fun a ha => by
        rw [tr_and2, KoreAML.interp_sAnd] at ha
        obtain ⟨v, hv, rfl⟩ := (hrd a).mp ha.1
        exact (inh_srt _ _).mpr (rhs_sorted_open h hs hσ hv))]
    constructor
    · rintro ⟨⟨a, ha⟩, -⟩
      rw [tr_and2, KoreAML.interp_sAnd] at ha
      obtain ⟨v, hv, rfl⟩ := (hrd a).mp ha.1
      exact ⟨v, hv, (hreadQ tbl e σ v (rhs_sorted_open h hs hσ hv) r.ens hensS hvar).mp ha.2⟩
    · rintro ⟨v, hv, hens⟩
      refine ⟨⟨.val v, ?_⟩, (inh_srt topCellSort (.val x)).mpr hx⟩
      rw [tr_and2, KoreAML.interp_sAnd]
      exact ⟨(hrd _).mpr ⟨v, hv, rfl⟩, (hreadQ tbl e σ v (rhs_sorted_open h hs hσ hv) r.ens hensS hvar).mpr hens⟩
  have hreadN : ∀ (tbl : KoreAML.VarTable) (e : Valuation Elem) (x : GroundTerm),
      (∀ k ∈ KoreAML.varsOf (.not C (anyOfC C comps)), k ∈ tbl) → c.sortOf x = some topCellSort →
      ((KoreAML.tr ⟨tbl, []⟩ (.not C (anyOfC C comps))).interpret (stdI c) e (.val x) ↔
        ∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x) := by
    intro tbl e x hk hx
    have happ : ∀ r' ∈ c.rules, r'.prio < r.prio →
        ((KoreAML.tr ⟨tbl, []⟩ (applies c r' (canonRulePres r'))).interpret (stdI c) e (.val x) ↔
          RuleApplies c r' x) := by
      intro r' hr' hp'
      obtain ⟨hs', hpo'⟩ := hrules r' hr'
      have hφ : applies c r' (canonRulePres r') ∈ comps :=
        List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', by simpa using hp'⟩, rfl⟩
      refine applies_iff_T (T := StepM c) h hs' hpo' (fun i hi hil => hk _ ?_) e hx
      rw [KoreAML.varsOf]
      exact List.mem_append_right _ (mem_varsOf_anyOfC hφ
        (varsOf_appliesOpen (Semantics.rulePlainEx_top hpo').1 hi hil))
    rw [KoreAML.tr, KoreAML.interp_sNot]
    constructor
    · rintro ⟨hnc, -⟩ r' hr' hp' hna
      have hφ : applies c r' (canonRulePres r') ∈ comps :=
        List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', by simpa using hp'⟩, rfl⟩
      refine hnc ?_
      -- the disjunction of the competitors holds where one of them does
      have key : ∀ (cs : List Kore.Pattern), applies c r' (canonRulePres r') ∈ cs →
          (KoreAML.tr ⟨tbl, []⟩ (anyOfC C cs)).interpret (stdI c) e (.val x) := by
        intro cs hcs
        induction cs with
        | nil => exact absurd hcs List.not_mem_nil
        | cons φ cs ih =>
          rw [anyOfC, KoreAML.tr]
          simp only [KoreAML.trOrList]
          rw [KoreAML.interp_sOr]
          refine ⟨KoreAML.interp_inhOf_of (srtOf_top_den h e) |>.mpr ((inh_srt topCellSort (.val x)).mpr hx), ?_⟩
          rcases List.mem_cons.mp hcs with rfl | hcs
          · exact Or.inl ((happ r' hr' hp').mpr hna)
          · exact Or.inr (ih hcs)
      exact key comps hφ
    · intro hprio
      refine ⟨anyOfC_empty defOK_std (top_free _) _ (fun φ hφ hφm => ?_),
        KoreAML.interp_inhOf_of (srtOf_top_den h e) |>.mpr ((inh_srt topCellSort (.val x)).mpr hx)⟩
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hφ
      obtain ⟨hr'm, hp'⟩ := List.mem_filter.mp hr'
      exact hprio r' hr'm (by simpa using hp') ((happ r' hr'm (by simpa using hp')).mp hφm)
  by_cases hce : comps.isEmpty
  · refine ⟨.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)), .ceil C C R],
      by rw [prioRuleK_top hex₀ hpre₀ hpost₀]; dsimp only; rw [if_pos hce],
      rule_keys_open hs hp (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))), ?_⟩
    intro tbl e σ x _ hσ hx hvar
    have hnone : ∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x := fun r' hr' hp' => by
      have hne := List.isEmpty_iff.mp hce
      rw [List.map_eq_nil_iff, List.filter_eq_nil_iff] at hne
      exact absurd (by simpa using hp') (hne r' hr')
    rw [tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd, hreadL tbl e σ x hvar,
      hreadQ tbl e σ x hx r.req hreqs hvar, hreadCeil tbl e σ x hσ hx hvar]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun r' hr' hp' => hnone r' hr' hp', h3⟩
    · rintro ⟨h1, h2, -, h3⟩; exact ⟨h1, h2, h3⟩
  · refine ⟨.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)), .not C (anyOfC C comps),
      .ceil C C R], by rw [prioRuleK_top hex₀ hpre₀ hpost₀]; dsimp only; rw [if_neg hce],
      rule_keys_open hs hp (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))), ?_⟩
    intro tbl e σ x hkeysL hσ hx hvar
    have hkN : ∀ k ∈ KoreAML.varsOf (.not C (anyOfC C comps)), k ∈ tbl := fun k hk =>
      hkeysL k (varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) hk)
    rw [tr_and4, KoreAML.interp_sAnd, KoreAML.interp_sAnd, KoreAML.interp_sAnd, hreadL tbl e σ x hvar,
      hreadQ tbl e σ x hx r.req hreqs hvar, hreadN tbl e x hkN hx, hreadCeil tbl e σ x hσ hx hvar]

/-- **A rule's axiom holds in the value model**, for a rule of the definition with `ruleSorted` and
`rulePlainOpen`: its guards give every variable of the rule, held by the left side or not, a value
of its sort, and where the left part holds `StepM` steps by the rule to the right side's value. -/
theorem sat_rule_open (h : HypModelCore c) {r : Rule} (hr : r ∈ c.rules) (hs : c.ruleSorted r = true)
    (hp : c.rulePlainOpen r = true)
    (hrules : ∀ r' ∈ c.rules, c.ruleSorted r' = true ∧ c.rulePlainEx r' = true) :
    stdI c ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", { sortVars := [], pattern := prioRuleK c r, attributes := [] }⟩).pat := by
  have hn := h.namesK
  obtain ⟨-, -, -, -, hrhss⟩ := ruleSorted_partsOpen hs hp
  have hnum := rule_vars_numOpen h hs hp
  obtain ⟨L, hP, hLk, hLread⟩ := rule_premise_open h hs hp hrules
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let R : Kore.Pattern := .and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]
  intro e m
  unfold KoreAML.trAxiom
  dsimp only
  have hsortP : KoreAML.sortOf [] (prioRuleK c r) = some C := by rw [hP]; rfl
  simp only [hsortP]
  rw [interpret_impl]
  intro hgs
  let tbl : KoreAML.VarTable := KoreAML.tableOf [] (prioRuleK c r)
  have hvarsL : ∀ k ∈ KoreAML.varsOf L, k ∈ tbl := fun k hk => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    rw [hP, KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ hk)
  -- the guards give each variable a value of its sort
  have hin : ∀ i < r.vars.length, InSort c (r.vars.getD i 0) (e.evalEvar (tbl.ev (canonKey c r.vars i))) := by
    intro i hi
    have hk : canonKey c r.vars i ∈ ((([] : List Kore.SortVar).map KoreAML.sortVarKey) ++
        KoreAML.freeOf [] (prioRuleK c r)).eraseDups := by
      refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
      rw [hP, KoreAML.freeOf]
      exact List.mem_append_left _ (hLk i hi).1
    have hg := conjList_elim hgs _ (List.mem_map.mpr ⟨_, hk, rfl⟩)
    have hkk := canonKey_eq c hi
    rw [hkk, KoreAML.interp_guard_evar defOK_std, trSort_srt, ← hkk] at hg
    exact (inhOf_sort hn (hnum i hi) e _).mp hg
  obtain ⟨hσ, hvar⟩ := substE_ok hin
  have hPtr : ∀ tb, KoreAML.tr ⟨tb, []⟩ (prioRuleK c r) =
      KoreAML.sRewrites (KoreAML.trSort tb C) (KoreAML.tr ⟨tb, []⟩ L) (KoreAML.tr ⟨tb, []⟩ R) := fun tb => by
    rw [hP, KoreAML.tr]; rfl
  rw [KoreAML.interp_equal defOK_std]
  intro a
  rw [hPtr]
  unfold KoreAML.sRewrites
  rw [KoreAML.interp_sImp]
  constructor
  · exact fun h' => h'.1
  · intro ha
    refine ⟨ha, fun hL => ?_⟩
    rw [KoreAML.interp_inhOf_of (srtOf_top_den h e), inh_srt] at ha
    obtain ⟨x, rfl, hx⟩ := inSort_val ha
    obtain ⟨hmatch, hreq, hprio, y, hy, hens⟩ := (hLread tbl e _ x hvarsL hσ hx hvar).mp hL
    exact rhs_next h hr (Semantics.rulePlainOpen_top hp).2.1 (Semantics.rulePlainOpen_top hp).2.2 hσ hvar (tr_term h hvar (termOK_of_sorted h fns_headsOK hrhss)) hx hmatch hreq hprio hy hens

/-- **`SatRulesGoal`** for a definition whose rules have `ruleSorted` and `rulePlainOpen`. -/
theorem satRulesGoal_open (h : HypModelCore c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true) : SatRulesGoal c := by
  refine sat_itemsPremises c fun it hit => ?_
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hit
  exact sat_rule_open h hr (hrules r hr).1 (hrules r hr).2
    fun r' hr' => ⟨(hrules r' hr').1, (Semantics.rulePlainOpen_iff_ex.mp (hrules r' hr').2).1⟩

end Model

end Faithful

end KCore
