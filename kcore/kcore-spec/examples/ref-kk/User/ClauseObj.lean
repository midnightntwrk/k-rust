/-
  The object side of kore.k's walk of a clause: what `encodable d` and `execReady d` give of a
  clause of `d₀ d` and of what kore.k's `eval` returns at the instances of its terms.

  - The clause's shape (C12, `shapesOK`): no existential variable, `\top` predicates, not `aside`,
    and its patterns bind every variable (`clauseShape_ksc`).
  - Its terms are sorted over function signatures (`clauseTerms_ksc`), their forms are those
    `encDef` writes and hold no alias outside the patterns (`clauseEnc_ksc`), and a substitution
    well sorted on its variables gives them values whose literals have a kore.k form
    (`clauseLits_ksc`).
  - `inst` has a value at the form of an alias-free term where the binding has an entry for each
    of its variables (`instF_isSome_ksc`): the forms `encTerm` writes are `vr`, literals, `ap`,
    `hk`, `ij`, `cb` with `el` and `kv` parts, none of which `inst` leaves without a value
    (`InstOK_ksc`).
  - `eval` at the instance of the `requires` (`reqEval_spec_ksc`) and of the right side with its
    ensures (`rhsEval_spec_ksc`) under a binding that agrees with a well-sorted substitution: the
    encoding of what the object semantics gives the term, under every well-sorted substitution
    the binding agrees with. `Spec` at `eval` gives the value per substitution; one substitution
    (`σ₀`) is needed to have it at all.
  - `lookup` at the encoded definition is `lookupFn` (`lookFn_encDef_ksc`).
-/
import User.WalkInv

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KCore.KK

/-! ## The clause -/

section Clause
variable {d : Semantics}

theorem allFns_d₀_ksc (d : Semantics) : (d₀ d).allFns = d.allFns := rfl

theorem encodable_d₀_ksc (hc : encodable d = true) : encodable (d₀ d) = true := by
  rw [← encDef_isSome, encDef_withHooks, encDef_isSome]; exact hc

theorem encodable_of_encDef_ksc {E : D} (hE : encDef d = some E) : encodable d = true := by
  rw [← encDef_isSome, hE]; rfl

/-- **C12 at a clause**: no existential variable, `\top` predicates, not `aside`, and the patterns
bind every variable. -/
theorem clauseShape_ksc (hc : encodable d = true) {fn : Fn} (hfn : fn ∈ (d₀ d).allFns)
    {cl : Clause} (hcl : cl ∈ fn.clauses) :
    cl.exs = [] ∧ cl.pre = .top ∧ cl.post = .top ∧ cl.aside = false ∧
      binds cl.vars.length (varOccsList cl.pats) = true := by
  have h12 : shapesOK d = true := by
    simp only [encodable, Bool.and_eq_true] at hc
    exact hc.1.2
  simp only [shapesOK, Bool.and_eq_true, List.all_eq_true] at h12
  have h := h12.2 fn hfn cl hcl
  simp only [clauseShapeOK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨⟨ho, he⟩, hpre⟩, hpost⟩, ha⟩ := h
  refine ⟨List.isEmpty_iff.mp he, Cond.eq_top_of_isTop hpre, Cond.eq_top_of_isTop hpost, ha, ?_⟩
  rw [← opens_isEmpty_iff_binds]
  exact ho

/-- **The terms of a clause, sorted over function signatures.** -/
theorem clauseTerms_ksc (hr : CExec.execReady d = true) (hc : encodable d = true) {fn : Fn}
    (hfn : fn ∈ (d₀ d).allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) :
    ∃ L, HeadsOK (d₀ d) L ∧ sortOfTerm ((d₀ d).rhsCtx L) cl.vars cl.rhs = some fn.result ∧
      (∀ t, cl.req = some t → sortOfTerm ((d₀ d).rhsCtx L) cl.vars t = some Srt.bool) ∧
      (∀ e, cl.ens = some e → sortOfTerm ((d₀ d).rhsCtx L) cl.vars e = some Srt.bool) := by
  obtain ⟨hok, -, -, -⟩ := d₀_facts_kkv hr hc
  obtain ⟨L, hL, hreq, hrhs, hens⟩ : ∃ L, HeadsOK (d₀ d) L ∧
      reqOK ((d₀ d).rhsCtx L) cl.vars cl.req = true ∧
      sortOfTerm ((d₀ d).rhsCtx L) cl.vars cl.rhs = some fn.result ∧
      reqOK ((d₀ d).rhsCtx L) cl.vars cl.ens = true := by
    rcases List.mem_append.mp hfn with hfn | hfn
    · have h' := Semantics.sortedOK_sorted hok
      simp only [Bool.and_eq_true, List.all_eq_true] at h'
      have := h'.1.2 fn hfn cl hcl
      simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at this
      exact ⟨_, headsOK_fns_kkv _, this.1.1.1.1.2, this.1.1.1.2, this.1.1.2⟩
    · obtain ⟨-, -, -, h1, h2, h3⟩ := sortPreds_ctx hfn cl hcl
      exact ⟨[], (fun k hk => nomatch hk : HeadsOK (d₀ d) []), h1, h2, h3⟩
  exact ⟨L, hL, hrhs, fun t ht => reqOK_some_kkv hreq ht, fun e he => reqOK_some_kkv hens he⟩

/-- **The forms of a clause's terms** are those `encDef` writes, the `requires`, right side and
ensures without an alias, and the patterns' `Map` and `Set` patterns of C8's shape. -/
theorem clauseEnc_ksc (hc : encodable d = true) {fn : Fn} (hfn : fn ∈ (d₀ d).allFns) {cl : Clause}
    (hcl : cl ∈ fn.clauses) :
    encTermsWith d encLit cl.pats = some (encCl d cl).pats ∧ colPatsOKL (encCl d cl).pats = true ∧
      (∀ t, cl.req = some t → encTerm d t = some (encCl d cl).req ∧ asFree t = true) ∧
      (cl.req = none → (encCl d cl).req = .bv true) ∧ encTerm d cl.rhs = some (encT d cl.rhs) ∧
      asFree cl.rhs = true ∧ (∀ e, cl.ens = some e → encTerm d e = some (encT d e) ∧ asFree e = true) := by
  have hl : ∀ t ∈ cl.pats, t ∈ lhsTerms d := fun t ht => by
    simp only [lhsTerms, List.mem_append, List.mem_flatMap]
    exact .inr ⟨fn, hfn, cl, hcl, ht⟩
  have hreqm : ∀ t, cl.req = some t → t ∈ rhsTerms d := fun t ht => by
    simp only [rhsTerms, List.mem_append, List.mem_flatMap]
    exact .inr ⟨fn, hfn, cl, hcl, by simp [ht]⟩
  have hrhsm : cl.rhs ∈ rhsTerms d := by
    simp only [rhsTerms, List.mem_append, List.mem_flatMap]
    exact .inr ⟨fn, hfn, cl, hcl, by simp⟩
  have hensm : ∀ e, cl.ens = some e → e ∈ ensTerms d := fun e he => by
    simp only [ensTerms, List.mem_append, List.mem_flatMap]
    exact .inr ⟨fn, hfn, List.mem_filterMap.mpr ⟨cl, hcl, he⟩⟩
  have hc' := hc
  simp only [encodable, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, h8⟩, h10⟩, h11⟩, -⟩, -⟩ := hc'
  simp only [colPatsOK, List.all_eq_true] at h8
  simp only [asOK, List.all_eq_true] at h10
  simp only [ensOK, List.all_eq_true, Bool.and_eq_true] at h11
  have hpats := encTerms_of_encodable hc (ts := cl.pats) fun t ht => by
    simp only [List.mem_append]; exact .inl (.inl (hl t ht))
  refine ⟨hpats, colPatsOKL_iff_cpv.mpr fun p hp => ?_, fun t ht => ⟨?_, h10 t (hreqm t ht)⟩,
    fun ht => by simp [encCl, encReq, ht], encTerm_of_encodable hc (by simp [hrhsm]), h10 _ hrhsm,
    fun e he => ⟨encTerm_of_encodable hc (by simp [hensm e he]), (h11 e (hensm e he)).2⟩⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
    have := h8 t (hl t ht)
    rw [encTerm_of_encodable hc (by simp [hl t ht])] at this
    exact this
  · simp only [encCl, encReq, ht]
    exact encTerm_of_encodable hc (by simp [hreqm t ht])

/-- **What a well-sorted substitution gives a clause's variables has kore.k literals**: every
variable is a pattern variable (C12), of a sort other than `Float`. -/
theorem clauseLits_ksc (hr : CExec.execReady d = true) (hc : encodable d = true) {fn : Fn}
    (hfn : fn ∈ (d₀ d).allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) {σ : Subst}
    (hσ : (d₀ d).WellSorted cl.vars σ) :
    ∀ i < cl.vars.length, ∀ v, σ.lookup i = some v → litsV v = true := fun i hi v hv =>
  litsV_wellSortedAt_kpv (encodable_d₀_ksc hc) (hσ.at (List.range cl.vars.length))
    (List.mem_range.mpr hi)
    (clause_patVar_sort_kpv hr hc hfn hcl (Exec.binds_all (clauseShape_ksc hc hfn hcl).2.2.2.2 i hi)) hv

/-- A term of a clause sorted over its variables is one `σ` gives a meaning, at a well-sorted
`σ`. -/
theorem clauseTermOK_ksc (hr : CExec.execReady d = true) (hc : encodable d = true) {fn : Fn}
    (hfn : fn ∈ (d₀ d).allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) {σ : Subst}
    (hσ : (d₀ d).WellSorted cl.vars σ) {L : List CtorSig} (hL : HeadsOK (d₀ d) L) {t : Term}
    {s : Srt} (hs : sortOfTerm ((d₀ d).rhsCtx L) cl.vars t = some s) : TermOK_ksm d σ t :=
  termOK_of_kst hL hs (is := List.range cl.vars.length)
    (fun i hi => List.mem_range.mpr (Faithful.varOccs_lt t hs i hi)) (hσ.at _)
    (fun i hi v hv => clauseLits_ksc hr hc hfn hcl hσ i (List.mem_range.mp hi) v hv)

/-- The variables of a context have sorts other than `Float`. -/
def VarsNF_ksc (vars : List Srt) : Prop := ∀ i < vars.length, ∃ s, vars[i]? = some s ∧ s ≠ Srt.float

/-- A well-sorted substitution at variables of sorts other than `Float` gives them values whose
literals have kore.k forms. -/
theorem litsV_subst_ksc (hc : encodable d = true) {vars : List Srt} (hv : VarsNF_ksc vars)
    {σ : Subst} (hσ : (d₀ d).WellSorted vars σ) :
    ∀ i < vars.length, ∀ v, σ.lookup i = some v → litsV v = true := fun i hi v hvi =>
  litsV_wellSortedAt_kpv (encodable_d₀_ksc hc) (hσ.at (List.range vars.length))
    (List.mem_range.mpr hi) (hv i hi) hvi

/-- A term sorted over the variables of a context is one a well-sorted `σ` gives a meaning. -/
theorem termOK_ctx_ksc (hc : encodable d = true) {vars : List Srt} (hv : VarsNF_ksc vars)
    {σ : Subst} (hσ : (d₀ d).WellSorted vars σ) {L : List CtorSig} (hL : HeadsOK (d₀ d) L)
    {t : Term} {s : Srt} (hs : sortOfTerm ((d₀ d).rhsCtx L) vars t = some s) : TermOK_ksm d σ t :=
  termOK_of_kst hL hs (is := List.range vars.length)
    (fun i hi => List.mem_range.mpr (Faithful.varOccs_lt t hs i hi)) (hσ.at _)
    (fun i hi v hvi => litsV_subst_ksc hc hv hσ i (List.mem_range.mp hi) v hvi)

/-- The patterns of a clause bind every variable (C12). -/
theorem clauseBinds_ksc (hc : encodable d = true) {fn : Fn} (hfn : fn ∈ (d₀ d).allFns)
    {cl : Clause} (hcl : cl ∈ fn.clauses) : binds cl.vars.length (varOccsList cl.pats) = true :=
  (clauseShape_ksc hc hfn hcl).2.2.2.2

/-- A clause's variables have sorts other than `Float`: each is a pattern variable. -/
theorem clauseVarsNF_ksc (hr : CExec.execReady d = true) (hc : encodable d = true) {fn : Fn}
    (hfn : fn ∈ (d₀ d).allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) : VarsNF_ksc cl.vars :=
  fun i hi => clause_patVar_sort_kpv hr hc hfn hcl (Exec.binds_all (clauseBinds_ksc hc hfn hcl) i hi)

end Clause

/-! ## `inst` has a value -/

section Inst

mutual
/-- A form `inst` gives a value where every variable has an entry: no alias, `bot` or collection
value. -/
def InstOK_ksc : T → Prop
  | .vr _ | .iv _ | .bv _ | .tk _ _ => True
  | .ap _ ts | .hk _ ts | .cb _ _ ts => InstOKL_ksc ts
  | .ij _ _ t | .el t => InstOK_ksc t
  | .kv a b | .en a b => InstOK_ksc a ∧ InstOK_ksc b
  | .as _ _ | .bot | .co _ _ _ => False
  termination_by structural t => t
/-- `InstOK_ksc` of each. -/
def InstOKL_ksc : List T → Prop
  | [] => True
  | t :: ts => InstOK_ksc t ∧ InstOKL_ksc ts
  termination_by structural ts => ts
end

theorem instOKL_iff_ksc : ∀ {ts : List T}, InstOKL_ksc ts ↔ ∀ t ∈ ts, InstOK_ksc t
  | [] => by simp [InstOKL_ksc]
  | t :: ts => by simp [InstOKL_ksc, instOKL_iff_ksc (ts := ts)]

mutual
theorem instF_isSome_of_ksc : ∀ (p : T) (B : Bind), InstOK_ksc p →
    (∀ x ∈ tvarsF p, (lookF x B).isSome = true) → (instF p B).isSome = true
  | .vr x, B, _, hB => by rw [instF]; exact hB x (by simp [tvarsF])
  | .iv _, _, _, _ => rfl
  | .bv _, _, _, _ => rfl
  | .tk _ _, _, _, _ => rfl
  | .ap f ts, B, h, hB => by
    rw [instF]
    have := instTsF_isSome_of_ksc ts B (by rw [InstOK_ksc] at h; exact instOKL_iff_ksc.mp h) (by rw [tvarsF] at hB; exact hB)
    obtain ⟨us, hus⟩ := Option.isSome_iff_exists.mp this
    rw [hus]; rfl
  | .hk o ts, B, h, hB => by
    rw [instF]
    have := instTsF_isSome_of_ksc ts B (by rw [InstOK_ksc] at h; exact instOKL_iff_ksc.mp h) (by rw [tvarsF] at hB; exact hB)
    obtain ⟨us, hus⟩ := Option.isSome_iff_exists.mp this
    rw [hus]; rfl
  | .cb k c ts, B, h, hB => by
    rw [instF]
    have := instTsF_isSome_of_ksc ts B (by rw [InstOK_ksc] at h; exact instOKL_iff_ksc.mp h) (by rw [tvarsF] at hB; exact hB)
    obtain ⟨us, hus⟩ := Option.isSome_iff_exists.mp this
    rw [hus]; rfl
  | .ij a c t, B, h, hB => by
    rw [instF]
    have := instF_isSome_of_ksc t B (by rw [InstOK_ksc] at h; exact h) (by rw [tvarsF] at hB; exact hB)
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp this
    rw [hu]; rfl
  | .el t, B, h, hB => by
    rw [instF]
    have := instF_isSome_of_ksc t B (by rw [InstOK_ksc] at h; exact h) (by rw [tvarsF] at hB; exact hB)
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp this
    rw [hu]; rfl
  | .kv a b, B, h, hB => by
    rw [InstOK_ksc] at h
    rw [tvarsF] at hB
    rw [instF]
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp
      (instF_isSome_of_ksc a B h.1 fun x hx => hB x (List.mem_append_left _ hx))
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp
      (instF_isSome_of_ksc b B h.2 fun x hx => hB x (List.mem_append_right _ hx))
    rw [hu, hw]; rfl
  | .en a b, B, h, hB => by
    rw [InstOK_ksc] at h
    rw [tvarsF] at hB
    rw [instF]
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp
      (instF_isSome_of_ksc a B h.1 fun x hx => hB x (List.mem_append_left _ hx))
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp
      (instF_isSome_of_ksc b B h.2 fun x hx => hB x (List.mem_append_right _ hx))
    rw [hu, hw]; rfl
  | .as _ _, _, h, _ => by rw [InstOK_ksc] at h; exact h.elim
  | .bot, _, h, _ => by rw [InstOK_ksc] at h; exact h.elim
  | .co _ _ _, _, h, _ => by rw [InstOK_ksc] at h; exact h.elim
theorem instTsF_isSome_of_ksc : ∀ (ts : List T) (B : Bind), (∀ t ∈ ts, InstOK_ksc t) →
    (∀ x ∈ tvarsLF ts, (lookF x B).isSome = true) → (instTsF ts B).isSome = true
  | [], _, _, _ => rfl
  | t :: ts, B, h, hB => by
    rw [tvarsLF] at hB
    rw [instTsF]
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp
      (instF_isSome_of_ksc t B (h t (List.mem_cons_self ..)) fun x hx => hB x (List.mem_append_left _ hx))
    obtain ⟨us, hus⟩ := Option.isSome_iff_exists.mp
      (instTsF_isSome_of_ksc ts B (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
        fun x hx => hB x (List.mem_append_right _ hx))
    rw [hu, hus]; rfl
end

section
variable {c : Semantics}

theorem readApp_instOK_ksc {f : Sym} {args parts : Option (List T)} {q : T}
    (hargs : ∀ qs, args = some qs → ∀ t ∈ qs, InstOK_ksc t)
    (hparts : ∀ ps, parts = some ps → ∀ t ∈ ps, InstOK_ksc t)
    (h : readApp c f args parts = some q) : InstOK_ksc q := by
  unfold readApp at h
  split at h
  · obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [InstOK_ksc]; exact instOKL_iff_ksc.mpr (hargs qs hqs)
  · split at h
    · obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [InstOK_ksc]
      exact instOKL_iff_ksc.mpr fun t ht => hparts ps hps t (mem_orderParts_kin ht)
    · split at h
      · split at h
        · obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
          rw [InstOK_ksc]; exact instOKL_iff_ksc.mpr (hargs qs hqs)
        · obtain ⟨qs, hqs, h'⟩ := Option.bind_eq_some_iff.mp h
          unfold derivedHook at h'
          split at h'
          · cases h'
            rw [InstOK_ksc, InstOKL_ksc, InstOKL_ksc, InstOK_ksc]
            exact ⟨instOKL_iff_ksc.mpr (hargs qs hqs), trivial⟩
          · cases h'
      · split at h
        · cases h
        · split at h
          · obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
            rw [InstOK_ksc]; exact instOKL_iff_ksc.mpr (hargs qs hqs)
          · cases h

/-- What the induction gives of an alias-free term: its form, and its parts as a concatenation's
argument, are forms `inst` gives a value. -/
def InstOf_ksc (c : Semantics) (t : Term) : Prop :=
  asFree t = true → (∀ q, encTerm c t = some q → InstOK_ksc q) ∧
    ∀ k s qs, encPartWith c encLit k s t = some qs → ∀ q ∈ qs, InstOK_ksc q

theorem asFreeL_iff_ksc : ∀ {ts : List Term}, asFree.asFreeL ts = true ↔ ∀ t ∈ ts, asFree t = true
  | [] => by simp [asFree.asFreeL]
  | t :: ts => by simp [asFree.asFreeL, asFreeL_iff_ksc (ts := ts)]

theorem encTermsWith_instOK_ksc : ∀ {ts : List Term}, (∀ t ∈ ts, InstOf_ksc c t) →
    (∀ t ∈ ts, asFree t = true) → ∀ {qs : List T}, encTermsWith c encLit ts = some qs →
    ∀ q ∈ qs, InstOK_ksc q
  | [], _, _, qs, h => by rw [encTerms_nil_kmf c h]; exact fun _ h => nomatch h
  | t :: ts, ih, ha, qs, h => by
    obtain ⟨q, qs', h1, h2, rfl⟩ := encTerms_cons_kmf c h
    intro q' hq'
    rcases List.mem_cons.mp hq' with rfl | hq'
    · exact ((ih t (by simp)) (ha t (by simp))).1 _ h1
    · exact encTermsWith_instOK_ksc (fun x hx => ih x (by simp [hx]))
        (fun x hx => ha x (by simp [hx])) h2 q' hq'

theorem encCollWith_instOK_ksc {ts : List Term} (ih : ∀ t ∈ ts, InstOf_ksc c t)
    (ha : ∀ t ∈ ts, asFree t = true) (k : Kind) (s : Srt) (r : CRole) {ps : List T}
    (h : encCollWith c encLit k s r ts = some ps) : ∀ q ∈ ps, InstOK_ksc q := by
  rcases ts with _ | ⟨x, _ | ⟨v, _ | ⟨w, rest⟩⟩⟩
  · simp only [encCollWith] at h
    split at h
    · cases h; exact fun _ h => nomatch h
    · cases h
  · simp only [encCollWith] at h
    split at h
    · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
      intro q hq
      simp only [List.mem_singleton] at hq
      subst hq
      rw [InstOK_ksc]
      exact ((ih x (by simp)) (ha x (by simp))).1 p hp
    · cases h
  · have hx := (ih x (by simp)) (ha x (by simp))
    have hv := (ih v (by simp)) (ha v (by simp))
    simp only [encCollWith] at h
    split at h
    · split at h
      · rename_i p q' hp hq
        cases h
        intro q hq
        simp only [List.mem_singleton] at hq
        subst hq
        rw [InstOK_ksc]
        exact ⟨hx.1 p hp, hv.1 q' hq⟩
      · cases h
    · split at h
      · split at h
        · rename_i p q' hp hq
          cases h
          intro y hy
          rcases List.mem_append.mp hy with hy | hy
          · exact hx.2 k s p hp y hy
          · exact hv.2 k s q' hq y hy
        · cases h
      · cases h
  · simp only [encCollWith] at h; cases h

/-- **The form of an alias-free term is one `inst` gives a value.** -/
theorem instOf_ksc (t : Term) : InstOf_ksc c t := by
  induction t using termInd_kel with
  | hvar i =>
    intro _
    refine ⟨fun q hq => ?_, fun k s qs hq => ?_⟩
    · rw [encTerm_var_kmf] at hq; cases hq; rw [InstOK_ksc]; trivial
    · simp only [encPartWith, Option.some.injEq] at hq
      subst hq
      intro q hq
      simp only [List.mem_singleton] at hq
      subst hq; rw [InstOK_ksc]; trivial
  | hdv s l =>
    intro _
    have hl : ∀ q, encLit s l = some q → InstOK_ksc q := by
      intro q hq
      unfold encLit encLitWith at hq
      split at hq <;> first | (cases hq; rw [InstOK_ksc]; trivial) | cases hq
    refine ⟨fun q hq => ?_, fun k s' qs hq => ?_⟩
    · rw [encTerm_dv_kmf] at hq; exact hl q hq
    · simp only [encPartWith] at hq
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
      intro q hq
      simp only [List.mem_singleton] at hq
      subst hq; exact hl _ hp
  | hinj a b t ih =>
    intro hf
    have hf' : asFree t = true := by simpa [asFree] using hf
    refine ⟨fun q hq => ?_, fun k s' qs hq => ?_⟩
    · rw [encTerm_inj_kmf] at hq
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
      rw [InstOK_ksc]; exact (ih hf').1 p hp
    · simp only [encPartWith] at hq
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
      intro q hq
      simp only [List.mem_singleton] at hq
      subst hq
      rw [InstOK_ksc]; exact (ih hf').1 p hp
  | has t i _ =>
    intro hf
    simp [asFree] at hf
  | happ f ts ih =>
    intro hf
    have ha : ∀ t ∈ ts, asFree t = true := by
      have : asFree.asFreeL ts = true := by simpa [asFree] using hf
      exact asFreeL_iff_ksc.mp this
    have hargs : ∀ qs, encTermsWith c encLit ts = some qs → ∀ q ∈ qs, InstOK_ksc q :=
      fun qs h => encTermsWith_instOK_ksc ih ha h
    have hcoll : ∀ k' s' r ps, encCollWith c encLit k' s' r ts = some ps → ∀ q ∈ ps, InstOK_ksc q :=
      fun k' s' r ps h => encCollWith_instOK_ksc ih ha k' s' r h
    have hparts : ∀ ps, ((collSymOf c f).bind fun (k', s', r) => encCollWith c encLit k' s' r ts) =
        some ps → ∀ q ∈ ps, InstOK_ksc q := by
      intro ps h
      obtain ⟨⟨k', s', r⟩, -, h'⟩ := Option.bind_eq_some_iff.mp h
      exact hcoll k' s' r ps h'
    refine ⟨fun q hq => ?_, fun k₀ s₀ qs hq => ?_⟩
    · rw [encTerm_app_kmf] at hq
      exact readApp_instOK_ksc hargs hparts hq
    · simp only [encPartWith] at hq
      split at hq
      · split at hq
        · exact hcoll _ _ _ _ hq
        · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
          intro q hq
          simp only [List.mem_singleton] at hq
          subst hq
          exact readApp_instOK_ksc hargs (fun ps h => hcoll _ _ _ ps h) hp
      · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
        intro q hq
        simp only [List.mem_singleton] at hq
        subst hq
        exact readApp_instOK_ksc hargs hparts hp

end

/-- **`inst` has a value** at the form of an alias-free term, where the binding has an entry for
every variable of the term. -/
theorem instF_isSome_ksc {d : Semantics} {t : Term} {p : T} {B : Bind} (h : encTerm d t = some p)
    (ha : asFree t = true) (hB : ∀ i ∈ varOccs t, (lookF (i : Int) B).isSome = true) :
    (instF p B).isSome = true :=
  instF_isSome_of_ksc p B (((instOf_ksc (c := d) t) ha).1 p h) fun x hx => by
    obtain ⟨i, hi, rfl⟩ := encTerm_among_kin h x hx
    exact hB i hi

end Inst

/-! ## What `eval` gives at a clause's terms -/

section Eval
variable {d : Semantics} {E : D}

/-- The encoding of a value is `bv(b)` only at the Bool `b`. -/
theorem enc_eq_bv_ksc {v : GroundTerm} {b : Bool} (h : enc v = .bv b) : v = bool b := by
  cases v with
  | dv s l =>
    unfold enc at h
    split at h <;> (try (cases h; done)) <;> (cases h; rename_i heq; rw [heq]; rfl)
  | _ => unfold enc at h; cases h

theorem encR_eq_bv_ksc {o : Option GroundTerm} {b : Bool} (h : encR o = .bv b) : o = some (bool b) := by
  cases o with
  | none => cases h
  | some v => rw [enc_eq_bv_ksc h]

/-- The instance of a clause's `requires` has a value where the binding has an entry for every
variable of the clause. -/
theorem reqInst_ksc (hr : CExec.execReady d = true) (hc : encodable d = true) {fn : Fn}
    (hfn : fn ∈ (d₀ d).allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) {B : Bind}
    (hB : Covers_ksm B (List.range cl.vars.length)) : ∃ t, instF (encCl d cl).req B = some t := by
  obtain ⟨L, -, -, hreq, -⟩ := clauseTerms_ksc hr hc hfn hcl
  obtain ⟨-, -, he, hn, -⟩ := clauseEnc_ksc hc hfn hcl
  cases hq : cl.req with
  | none => rw [hn hq]; exact ⟨_, rfl⟩
  | some tq =>
    obtain ⟨h1, h2⟩ := he tq hq
    exact Option.isSome_iff_exists.mp (instF_isSome_ksc h1 h2 fun i hi =>
      hB i (List.mem_range.mpr (Faithful.varOccs_lt tq (hreq tq hq) i hi)))

/-- The instance of a clause's right side with its ensures has a value where the binding has an
entry for every variable of the clause. -/
theorem rhsInst_ksc (hr : CExec.execReady d = true) (hc : encodable d = true) {fn : Fn}
    (hfn : fn ∈ (d₀ d).allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) {B : Bind}
    (hB : Covers_ksm B (List.range cl.vars.length)) : ∃ t, instF (encCl d cl).rhs B = some t := by
  obtain ⟨L, -, hrhs, -, hens⟩ := clauseTerms_ksc hr hc hfn hcl
  obtain ⟨-, -, -, -, h1, h2, he⟩ := clauseEnc_ksc hc hfn hcl
  have hr' := instF_isSome_ksc h1 h2 fun i hi =>
    hB i (List.mem_range.mpr (Faithful.varOccs_lt cl.rhs hrhs i hi))
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hr'
  cases hq : cl.ens with
  | none =>
    refine ⟨u, ?_⟩
    show instF (encRhs d cl.rhs cl.ens) B = some u
    rw [hq]; exact hu
  | some e =>
    obtain ⟨g1, g2⟩ := he e hq
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (instF_isSome_ksc g1 g2 fun i hi =>
      hB i (List.mem_range.mpr (Faithful.varOccs_lt e (hens e hq) i hi)))
    refine ⟨.en u w, ?_⟩
    show instF (encRhs d cl.rhs cl.ens) B = some (.en u w)
    rw [hq, encRhs, instF, hu, hw]; rfl

/-- **`eval` at the instance of a `requires`** of a context (`vars`, `req`: a clause's or a
rule's): a value `u`, `bv(true)` where there is no `requires`, and the encoding of the `requires`'
result under every well-sorted substitution the binding agrees with. -/
theorem reqEval_spec_ksc (hc : encodable d = true) {vars : List Srt} {req : Option Term}
    {L : List CtorSig} (hL : HeadsOK (d₀ d) L)
    (hs : ∀ t, req = some t → sortOfTerm ((d₀ d).rhsCtx L) vars t = some Srt.bool)
    (he : ∀ t, req = some t → encTerm d t = some (encReq d req)) (hv : VarsNF_ksc vars)
    {B : Bind} {t : T} (ht : instF (encReq d req) B = some t) {σ₀ : Subst} (hB₀ : BindAgree B σ₀)
    (hσ₀ : (d₀ d).WellSorted vars σ₀) {q : Option GroundTerm}
    (hq : Called d E 464 [embD E, emb t] q) :
    ∃ u, q = some (emb u) ∧ (req = none → u = .bv true) ∧
      ∀ tq, req = some tq → ∀ σ, BindAgree B σ → (d₀ d).WellSorted vars σ →
        ∃ o, u = encR o ∧ EvalTerm (d₀ d) σ tq o := by
  cases hrq : req with
  | none =>
    rw [hrq] at ht
    cases ht
    have := (evalF_iff (eval_bv_kev E true)).mp hq.1
    exact ⟨.bv true, this, fun _ => rfl, fun tq h => (nomatch h)⟩
  | some tq =>
    subst hrq
    have hspec : ∀ σ, BindAgree B σ → (d₀ d).WellSorted vars σ →
        ∃ o, q = some (emb (encR o)) ∧ EvalTerm (d₀ d) σ tq o := fun σ hB hσ =>
      Spec.eval_term hq.2 (termOK_ctx_ksc hc hv hσ hL (hs tq rfl)) (inst_Inst_agree_kin (he tq rfl) hB ht)
    obtain ⟨o₀, hq₀, -⟩ := hspec σ₀ hB₀ hσ₀
    refine ⟨encR o₀, hq₀, fun h => (nomatch h), fun tq' htq σ hB hσ => ?_⟩
    cases htq
    obtain ⟨o, hqo, ho⟩ := hspec σ hB hσ
    rw [hq₀] at hqo
    exact ⟨o, emb_injective (Option.some.inj hqo), ho⟩

/-- **`eval` at the instance of a right side with its ensures** of a context (`vars`, `rhs`,
`ens`: a clause's or a rule's): a value `u`, under every well-sorted substitution the binding
agrees with the encoding of the right side's result (no ensures), or `ensure` of the ensures'
result and the right side's. -/
theorem rhsEval_spec_ksc (hc : encodable d = true) {vars : List Srt} {rhs : Term}
    {ens : Option Term} {s : Srt} {L : List CtorSig} (hL : HeadsOK (d₀ d) L)
    (hs : sortOfTerm ((d₀ d).rhsCtx L) vars rhs = some s)
    (hse : ∀ e, ens = some e → sortOfTerm ((d₀ d).rhsCtx L) vars e = some Srt.bool)
    (he : encTerm d rhs = some (encT d rhs)) (hee : ∀ e, ens = some e → encTerm d e = some (encT d e))
    (hv : VarsNF_ksc vars) {B : Bind} {t : T} (ht : instF (encRhs d rhs ens) B = some t)
    {σ₀ : Subst} (hB₀ : BindAgree B σ₀) (hσ₀ : (d₀ d).WellSorted vars σ₀) {q : Option GroundTerm}
    (hq : Called d E 464 [embD E, emb t] q) :
    ∃ u, q = some (emb u) ∧ ∀ σ, BindAgree B σ → (d₀ d).WellSorted vars σ →
      ∃ o, EvalTerm (d₀ d) σ rhs o ∧
        ((ens = none ∧ u = encR o) ∨
          ∃ e w, ens = some e ∧ EvalTerm (d₀ d) σ e w ∧ u = ensureF (encR w) (encR o)) := by
  cases hen : ens with
  | none =>
    rw [hen, encRhs] at ht
    have hspec : ∀ σ, BindAgree B σ → (d₀ d).WellSorted vars σ →
        ∃ o, q = some (emb (encR o)) ∧ EvalTerm (d₀ d) σ rhs o := fun σ hB hσ =>
      Spec.eval_term hq.2 (termOK_ctx_ksc hc hv hσ hL hs) (inst_Inst_agree_kin he hB ht)
    obtain ⟨o₀, hq₀, -⟩ := hspec σ₀ hB₀ hσ₀
    refine ⟨encR o₀, hq₀, fun σ hB hσ => ?_⟩
    obtain ⟨o, hqo, ho⟩ := hspec σ hB hσ
    rw [hq₀] at hqo
    exact ⟨o, ho, .inl ⟨rfl, emb_injective (Option.some.inj hqo)⟩⟩
  | some e =>
    rw [hen, encRhs] at ht
    simp only [instF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ht
    obtain ⟨p', hp', q', hq', rfl⟩ := ht
    have hspec : ∀ σ, BindAgree B σ → (d₀ d).WellSorted vars σ →
        ∃ o w, q = some (emb (ensureF (encR w) (encR o))) ∧ EvalTerm (d₀ d) σ rhs o ∧
          EvalTerm (d₀ d) σ e w := fun σ hB hσ =>
      Spec.eval_en hq.2 (termOK_ctx_ksc hc hv hσ hL hs) (termOK_ctx_ksc hc hv hσ hL (hse e hen))
        (inst_Inst_agree_kin he hB hp') (inst_Inst_agree_kin (hee e hen) hB hq')
    obtain ⟨o₀, w₀, hq₀, -, -⟩ := hspec σ₀ hB₀ hσ₀
    refine ⟨_, hq₀, fun σ hB hσ => ?_⟩
    obtain ⟨o, w, hqo, ho, hw⟩ := hspec σ hB hσ
    rw [hq₀] at hqo
    exact ⟨o, ho, .inr ⟨e, w, rfl, hw, emb_injective (Option.some.inj hqo)⟩⟩

/-- `reqEval_spec_ksc` at a clause of `d₀ d`. -/
theorem clauseReqEval_ksc (hr : CExec.execReady d = true) (hc : encodable d = true) {fn : Fn}
    (hfn : fn ∈ (d₀ d).allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) {B : Bind} {t : T}
    (ht : instF (encCl d cl).req B = some t) {σ₀ : Subst} (hB₀ : BindAgree B σ₀)
    (hσ₀ : (d₀ d).WellSorted cl.vars σ₀) {q : Option GroundTerm}
    (hq : Called d E 464 [embD E, emb t] q) :
    ∃ u, q = some (emb u) ∧ (cl.req = none → u = .bv true) ∧
      ∀ tq, cl.req = some tq → ∀ σ, BindAgree B σ → (d₀ d).WellSorted cl.vars σ →
        ∃ o, u = encR o ∧ EvalTerm (d₀ d) σ tq o := by
  obtain ⟨L, hL, -, hreq, -⟩ := clauseTerms_ksc hr hc hfn hcl
  obtain ⟨-, -, he, -⟩ := clauseEnc_ksc hc hfn hcl
  exact reqEval_spec_ksc hc hL hreq (fun t h => (he t h).1) (clauseVarsNF_ksc hr hc hfn hcl) ht hB₀ hσ₀ hq

/-- `rhsEval_spec_ksc` at a clause of `d₀ d`. -/
theorem clauseRhsEval_ksc (hr : CExec.execReady d = true) (hc : encodable d = true) {fn : Fn}
    (hfn : fn ∈ (d₀ d).allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) {B : Bind} {t : T}
    (ht : instF (encCl d cl).rhs B = some t) {σ₀ : Subst} (hB₀ : BindAgree B σ₀)
    (hσ₀ : (d₀ d).WellSorted cl.vars σ₀) {q : Option GroundTerm}
    (hq : Called d E 464 [embD E, emb t] q) :
    ∃ u, q = some (emb u) ∧ ∀ σ, BindAgree B σ → (d₀ d).WellSorted cl.vars σ →
      ∃ o, EvalTerm (d₀ d) σ cl.rhs o ∧
        ((cl.ens = none ∧ u = encR o) ∨
          ∃ e w, cl.ens = some e ∧ EvalTerm (d₀ d) σ e w ∧ u = ensureF (encR w) (encR o)) := by
  obtain ⟨L, hL, hrhs, -, hens⟩ := clauseTerms_ksc hr hc hfn hcl
  obtain ⟨-, -, -, -, h1, -, he⟩ := clauseEnc_ksc hc hfn hcl
  exact rhsEval_spec_ksc hc hL hrhs hens h1 (fun e h => (he e h).1) (clauseVarsNF_ksc hr hc hfn hcl)
    ht hB₀ hσ₀ hq

/-- A binding `σ` reads agrees with `σ`. -/
theorem bindAgree_of_rep_ksc {c : Semantics} {vars : List Srt} {B : Bind} {σ : Subst}
    (h : BindRep c vars B σ) : BindAgree B σ := fun x t hx => by
  obtain ⟨i, w, s, hi, hw, ht, -⟩ := h x t hx
  exact ⟨i, w, hi, hw, ht⟩

/-- `hasBot` at the encodings of values whose literals have kore.k forms is false. -/
theorem hasBotF_encTs_ksc : ∀ {ws : List GroundTerm}, (∀ v ∈ ws, litsV v = true) →
    hasBotF (encTs ws) = false
  | [], _ => rfl
  | v :: ws, h => by
    have hv : enc v ≠ .bot := fun e => by
      have := enc_ne_bot (h v (List.mem_cons_self ..))
      rw [e] at this
      exact this
    rw [encTs_eq_map, List.map_cons, hasBotF, ← encTs_eq_map,
      hasBotF_encTs_ksc fun u hu => h u (List.mem_cons_of_mem _ hu)]
    simp [hv]

end Eval

/-! ## `lookup` at the encoded definition -/

section Look

theorem encDef_fns_ksc {d : Semantics} {E : D} (hE : encDef d = some E) :
    E.fns = d.allFns.map fun fn => ((fn.label : Int), fn.clauses.map (encCl d)) := by
  unfold encDef at hE
  split at hE
  · cases hE; rfl
  · cases hE

theorem lookFn_map_ksc (d : Semantics) (f : Sym) : ∀ l : List Fn,
    lookFnF_ksc (f : Int) (l.map fun fn => ((fn.label : Int), fn.clauses.map (encCl d))) =
      (l.find? (·.label == f)).map fun fn => fn.clauses.map (encCl d)
  | [] => rfl
  | fn :: l => by
    simp only [List.map_cons, lookFnF_ksc, List.find?_cons]
    by_cases h : fn.label = f
    · subst h; simp
    · have h' : ¬ ((f : Int) = (fn.label : Int)) := fun e => h (Int.natCast_inj.mp e).symm
      have hb : (fn.label == f) = false := by simpa using h
      simp [h', hb, lookFn_map_ksc d f l]

/-- **`lookup` at the encoded definition is `lookupFn`.** -/
theorem lookFn_encDef_ksc {d : Semantics} {E : D} (hE : encDef d = some E) (f : Sym) :
    lookFnF_ksc (f : Int) E.fns = ((d₀ d).lookupFn f).map fun fn => fn.clauses.map (encCl d) := by
  rw [encDef_fns_ksc hE, lookFn_map_ksc, Semantics.lookupFn_eq]
  rfl

/-- `lookup` at the encoded definition, as User.KkGenEmb's mirror function gives it. -/
theorem lookupF_encDef_ksc {d : Semantics} {E : D} (hE : encDef d = some E) (f : Sym) :
    Gen.lookupF (f : Int) E.fns = some (((d₀ d).lookupFn f).map fun fn => fn.clauses.map (encCl d)) := by
  rw [lookupF_lookFn_ksc, lookFn_encDef_ksc hE]

end Look

/-! ## Instances -/

section Instances

/-- `instF_isSome_of_ksc` at `ap(5, vr(0) ; iv(1))` and a binding with an entry for `0`. -/
example : (instF (.ap 5 [.vr 0, .iv 1]) [(0, .bv true)]).isSome = true :=
  instF_isSome_of_ksc _ _ (by simp [InstOK_ksc, InstOKL_ksc]) fun x hx => by
    simp [tvarsF, tvarsLF] at hx
    subst hx; rfl

/-- `inst` has no value at `vr(0)` under `.Bind`: `instF_isSome_of_ksc` needs the entry. -/
example : instF (.vr 0) [] = none := rfl

/-- `hasBotF_encTs_ksc` at the encoding of an Int. -/
example : hasBotF (encTs [.dv 3 (.int 1)]) = false :=
  hasBotF_encTs_ksc fun v hv => by simp at hv; subst hv; rfl

/-- `lookFnF_ksc` finds the first function of the number. -/
example : lookFnF_ksc 3 [(2, []), (3, [⟨50, false, [], .bv true, .bot⟩])] =
    some [⟨50, false, [], .bv true, .bot⟩] := rfl

/-- `enc_eq_bv_ksc` at the Bool `true`. -/
example : bool true = bool true := enc_eq_bv_ksc (v := bool true) rfl

end Instances

/-! ## Checks -/

open Lean in
#eval show CoreM Unit from do
  for n in [``clauseShape_ksc, ``clauseTerms_ksc, ``clauseEnc_ksc, ``clauseLits_ksc,
      ``clauseTermOK_ksc, ``instF_isSome_ksc, ``enc_eq_bv_ksc, ``encR_eq_bv_ksc, ``reqInst_ksc,
      ``rhsInst_ksc, ``reqEval_spec_ksc, ``rhsEval_spec_ksc, ``clauseReqEval_ksc,
      ``clauseRhsEval_ksc, ``litsV_subst_ksc, ``termOK_ctx_ksc, ``clauseVarsNF_ksc, ``bindAgree_of_rep_ksc,
      ``hasBotF_encTs_ksc, ``lookFn_encDef_ksc, ``lookupF_encDef_ksc, ``clauseBinds_ksc] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
