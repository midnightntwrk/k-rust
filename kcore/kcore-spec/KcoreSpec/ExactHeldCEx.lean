/-
  KCore. The choice among instances and exactness, for a semantics `coreOKEx` accepts (a function's
  clauses may bind variables by `\exists`) whose rules have `rulePlainHeldH`, the per-rule fact
  `coreOKEx` gives at `Semantics.holds` (`Semantics.ruleFactsHeld_of_coreEx`).

  - `rule_step_of_witnessed_ppCEx`, `rule_step_C_witCEx`, `memHeld_valuesBCEx`,
    `rule_step_values_heldCEx`: a successor's valuation can be taken at values. The terms and
    predicates are read through `HoldsShape.termSoundEx` and `HoldsShape.holds_entailsCEx`, which
    read a clause with existential variables in every model of `Γc`.
  - `stepVals_of_right_heldCEx`, `step_of_successor_heldCEx`: a successor in a model of `Γc` with
    the step's closure is a step.
  - `stepBy_of_stepVByCEx`, `stdI_T_model_heldCEx`, `has_model_choice_heldCEx`: the value model at a
    transition T; the functions' equations are `AtT.satFnsGoalEx`.
  - `exact_heldCEx`: `ExactC` from the two.
  - `has_model_choice_ce`, `step_of_successor_ce`, `exact_ce`: `has_model_choice`'s and
    `exact_hyp`'s statements with `coreOKEx` for `coreOK`, the rules' facts and `HeldBackAll` read
    from `coreOKEx`.
-/
import KcoreSpec.SoundCE
import KcoreSpec.StepSuccessorExCEx
import KcoreSpec.ExactHeld
import KcoreSpec.FnModelCEx
import KcoreSpec.HypModelCoreEx

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace KCore

namespace Faithful

open ML
open KoreAML (VarTable)
open HoldsShape (hasBinder Reads reads_of_agrees)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A predicate that holds at an element is `true`**, in a model of `Γc`, at a σ that gives its
free variables values whose elements the valuation gives them. -/
theorem holdsTrue_of_memPPCEx (h : c.coreOKEx = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    {vars : List Srt} {p : Cond} (hok : c.condOK vars p = true) (hbd : Cond.bound c vars.length p = true)
    (hrc : hasBinder p = true → c.readsConfined = true) {σ : Subst}
    (hσ : c.WellSortedAt vars (varOccsCond vars.length p) σ) {tbl : VarTable} {e : Valuation M}
    (hr : Reads c I vars (fun i => i ∈ varOccsCond vars.length p) σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c topCellSort) p), k ∈ tbl)
    {a : M} (ha : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e a)
    (hm : (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c topCellSort) p)).interpret I e a) :
    Holds c vars.length σ p true := by
  obtain ⟨b, hb⟩ := holds_decidedCEx (hypSoundEx_of_coreEx h) hft p hok hσ
  have hiff := HoldsShape.holds_entailsCEx h hI hcw p hrc hok hbd (fun i hi _ => hi) hr hk top_numbered hb a ha
  rw [hiff.mp hm] at hb
  exact hb

/-- `holdsTrue_of_memPPCEx` over the conjuncts a predicate adds to a sentence (none for `\top`), at a
σ well sorted on every variable that agrees with the valuation. -/
theorem holds_of_conjPPCEx (h : c.coreOKEx = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    {vars : List Srt} {p : Cond} (hok : c.condOK vars p = true) (hbd : Cond.bound c vars.length p = true)
    (hrc : hasBinder p = true → c.readsConfined = true) {σ : Subst} (hσ : c.WellSorted vars σ)
    {tbl : VarTable} {e : Valuation M} (hag : Agrees c I tbl (canonVars c vars) σ e)
    (hkeys : ∀ i < vars.length, canonKey c vars i ∈ tbl)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c topCellSort) p), k ∈ tbl)
    {a : M} (ha : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e a)
    (hm : ∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c topCellSort) p, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a) :
    Holds c vars.length σ p true := by
  by_cases hT : p.isTop = true
  · rw [Cond.eq_top_of_isTop hT]; exact .top
  · refine holdsTrue_of_memPPCEx h hft hI hcw hok hbd hrc (hσ.at _)
      (reads_of_agrees hσ hag fun i hi => ⟨varOccsCond_lt_twoT p hok i hi, hkeys i (varOccsCond_lt_twoT p hok i hi)⟩)
      hk ha (hm _ ?_)
    simp [Cond.conj, hT]

/-- **The step a valuation gives, where it gives every variable a value**, for a rule with
predicates: `rule_step_of_witnessed`'s conclusion, x's element in `pre` and y's in `post` read by
the Holds lemma. -/
theorem rule_step_of_witnessed_ppCEx (h : c.coreOKEx = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true) (hrcQ : hasBinder r.post = true → c.readsConfined = true)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl)
    {e : Valuation M}
    (hwit : ∀ i < r.vars.length, Witnessed c I tbl (canonVars c r.vars) r.vars e i) (x y : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hprem : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e (elemOf c I x.val))
    (hy : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.rhs)).interpret I e (elemOf c I y.val))
    (hens : ∀ t, r.ens = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (some (Term.kore c (canonVars c r.vars) t)))).interpret I e (elemOf c I y.val))
    (hpostm : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.post,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e (elemOf c I y.val))
    (hreq : ∀ t, r.req = some t →
      EvalTerm c (substOf c I tbl (canonVars c r.vars) r.vars e) t (some (bool true))) :
    let σ := substOf c I tbl (canonVars c r.vars) r.vars e
    c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x.val ∧ (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
      Holds c r.vars.length σ r.pre true ∧ EvalTerm c σ r.rhs (some y.val) ∧
      (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.post true := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hs0 := hypSoundEx_of_coreEx h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hs0
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  obtain ⟨hlhs, -, hensK, hrhs⟩ := Semantics.ruleSorted_parts c hs
  have hs' := hs
  simp only [Semantics.ruleSorted, Bool.and_eq_true] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hokP⟩, -⟩, hokQ⟩, hbdP⟩, hbdQ⟩, -⟩ := hs'
  have hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))) := fun i hi => by
    obtain ⟨v, hv, he⟩ := hwit i hi
    rw [← he]; exact (inS_iff e).mp (elemOf_spec hIΓ hv e).2
  obtain ⟨hmatch, -⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
    (collPat_of_sorted hph' hlhs) (Semantics.ruleSorted_lhs_nf c hs) x.property hl
  obtain ⟨hσ, hag⟩ := substOf_ok hIΓ hg hsc.trans (canonVars_length c r.vars) hwit
  have hensS : ∀ t, r.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool :=
    fun t ht => by rw [ht] at hensK; simpa [reqOK] using hensK
  refine ⟨hσ, hmatch, hreq,
    holds_of_conjPPCEx h hft hI hcw hokP hbdP hrcP hσ hag hkeys hkP (inh_top_PP hIΓ x tbl e) hprem, ?_,
    fun t ht => evalTrue_of_modelSSx h hft hI hcw hσ hag (hensS t ht) (hens t ht),
    holds_of_conjPPCEx h hft hI hcw hokQ hbdQ hrcQ hσ hag hkeys hkQ (inh_top_PP hIΓ y tbl e) hpostm⟩
  obtain ⟨v, hv⟩ := Model.evalTerm_totalCl hsc hno hft fns_headsOK hσ hrhs
  have hbR := (HoldsShape.termSoundEx h hI hcw hv hσ (canonVars_length c r.vars) hag hrhs _).mp hy
  cases v with
  | none => exact hbR.elim
  | some yv =>
    have hyv := EvalTerm.sorted hsc hv fns_headsOK hσ hrhs rfl
    have he : elemOf c I yv = elemOf c I y.val := (((elemOf_spec hIΓ hyv e).1 _).mp hbR).symm
    rw [values_apart hIΓ hg hsc.trans (apartSort_of_sorted hg hyv) hyv y.property he] at hv
    exact hv

/-- **The conditions' variables at a witness's values.** Where the conditions are witnessed by
values σw (their `requires` `true`, their `pre` holding), none of their variables is held by the
left side, the right side, the `ensures` or `post`, and the valuation gives every other variable
the element of a value: the valuation that gives the conditions' variables σw's values and keeps
the others has a substitution with every premise of `StepBy` but the rule's membership and
`hprio`. -/
theorem rule_step_C_witCEx (h : c.coreOKEx = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true)
    (hcl : ∀ j ∈ r.condVars, j ∉ varOccs r.lhs) (hcr : ∀ j ∈ r.condVars, j ∉ varOccs r.rhs)
    (hce : ∀ j ∈ r.condVars, ∀ t, r.ens = some t → j ∉ varOccs t)
    (hcq : ∀ j ∈ r.condVars, j ∉ varOccsCond r.vars.length r.post)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true) (hrcQ : hasBinder r.post = true → c.readsConfined = true)
    {σw : Subst} (hσw : c.WellSortedAt r.vars r.condVars σw)
    (hreqw : ∀ t, r.req = some t → EvalTerm c σw t (some (bool true)))
    (hprew : Holds c r.vars.length σw r.pre true)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl)
    {e : Valuation M}
    (hwe : ∀ i < r.vars.length, i ∉ r.condVars → Witnessed c I tbl (canonVars c r.vars) r.vars e i)
    (x y : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hy : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.rhs)).interpret I e (elemOf c I y.val))
    (hens : ∀ t, r.ens = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (some (Term.kore c (canonVars c r.vars) t)))).interpret I e (elemOf c I y.val))
    (hpostm : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.post,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e (elemOf c I y.val)) :
    ∃ σ, c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x.val ∧ (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
      Holds c r.vars.length σ r.pre true ∧ EvalTerm c σ r.rhs (some y.val) ∧
      (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.post true := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hIΓ
  obtain ⟨hlhs, -, hensK, hrhs⟩ := Semantics.ruleSorted_parts c hs
  have hs' := hs
  simp only [Semantics.ruleSorted, Bool.and_eq_true] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hokP⟩, -⟩, hokQ⟩, hbdP⟩, -⟩, -⟩ := hs'
  let vs := canonVars c r.vars
  let n := r.vars.length
  let σmix : Subst := (List.range n).map fun i => (i, if r.condVars.contains i then (σw.lookup i).getD default
    else pick c I (r.vars.getD i 0) (e.evalEvar (tbl.ev (keyAt vs i))))
  have hmix : ∀ i < n, σmix.lookup i = some (if r.condVars.contains i then (σw.lookup i).getD default
      else pick c I (r.vars.getD i 0) (e.evalEvar (tbl.ev (keyAt vs i)))) := fun i hi => by
    simp only [σmix]
    rw [List.range_eq_range', lookup_range', if_pos ⟨Nat.zero_le _, by omega⟩]
  let e'' := overV c I tbl r.vars σmix e
  have hoff : ∀ i < n, i ∉ r.condVars →
      e''.evalEvar (tbl.ev (keyAt vs i)) = e.evalEvar (tbl.ev (keyAt vs i)) := fun i hi hc => by
    show (overV c I tbl r.vars σmix e).evalEvar (tbl.ev (canonKey c r.vars i)) = _
    rw [overV_at hkeys hi, hmix i hi, if_neg (by simpa using hc), Option.getD_some]
    exact (pick_spec (hwe i hi hc)).2
  have hon : ∀ i < n, i ∈ r.condVars → ∀ w, σw.lookup i = some w →
      e''.evalEvar (tbl.ev (keyAt vs i)) = elemOf c I w := fun i hi hc w hw => by
    show (overV c I tbl r.vars σmix e).evalEvar (tbl.ev (canonKey c r.vars i)) = _
    rw [overV_at hkeys hi, hmix i hi, if_pos (by simpa using hc), hw, Option.getD_some, Option.getD_some]
  have hσwv : ∀ i < n, i ∈ r.condVars → ∃ w, σw.lookup i = some w ∧ c.sortOf w = some (r.vars.getD i 0) :=
    fun i hi hc => hσw i hc _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
  have hwit : ∀ i < n, Witnessed c I tbl vs r.vars e'' i := fun i hi => by
    by_cases hc : i ∈ r.condVars
    · obtain ⟨w, hw, hws⟩ := hσwv i hi hc
      exact ⟨w, hws, (hon i hi hc w hw).symm⟩
    · obtain ⟨v, hv, he⟩ := hwe i hi hc
      exact ⟨v, hv, by rw [hoff i hi hc]; exact he⟩
  have hin'' : ∀ i < n, InS I (c.sortName (r.vars.getD i 0)) (e''.evalEvar (tbl.ev (keyAt vs i))) := fun i hi => by
    obtain ⟨v, hv, he⟩ := hwit i hi
    rw [← he]; exact (inS_iff e'').mp (elemOf_spec hIΓ hv e'').2
  have hag : ∀ (T : Term), (∀ i ∈ varOccs T, i < n) → (∀ j ∈ r.condVars, j ∉ varOccs T) →
      ∀ i ∈ varOccs T, e.evalEvar (tbl.ev (keyAt vs i)) = e''.evalEvar (tbl.ev (keyAt vs i)) :=
    fun T hlt hT i hi => (hoff i (hlt i hi) (fun hc => hT i hc hi)).symm
  have hl'' := (tr_kore_congr r.lhs (hag r.lhs (Exec.sortOfTerm_vars hlhs) hcl) _).mp hl
  have hy'' := (tr_kore_congr r.rhs (hag r.rhs (Exec.sortOfTerm_vars hrhs) hcr) _).mp hy
  have hens'' : ∀ t, r.ens = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (some (Term.kore c vs t)))).interpret I e'' (elemOf c I y.val) := fun t ht => by
    have htS : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool := by
      rw [ht] at hensK; simpa [reqOK] using hensK
    exact (tr_reqPat_congr hIΓ (hag t (Exec.sortOfTerm_vars htS) (fun j hj => hce j hj t ht)) _).mp (hens t ht)
  -- `post` holds no condition variable: it reads e'' as e
  have hpost'' : ∀ φ ∈ Cond.conj c vs (srtOf c topCellSort) r.post,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e'' (elemOf c I y.val) := fun φ hφ => by
    by_cases hT : r.post.isTop = true
    · simp [Cond.conj, hT] at hφ
    · obtain rfl : φ = Cond.kore c vs (srtOf c topCellSort) r.post := by simpa [Cond.conj, hT] using hφ
      refine (tr_condKore_twoT hD r.post hokQ (fun k hk0 => ⟨hkQ k hk0, hkQ k hk0⟩) (fun i hi => ?_) _).mp
        (hpostm _ (by simp [Cond.conj, hT]))
      have hlt := varOccsCond_lt_twoT r.post hokQ i hi
      exact ⟨hkeys i hlt, hkeys i hlt, (hoff i hlt (fun hc => hcq i hc hi)).symm⟩
  -- `pre` holds at σw, which e'' reads at `pre`'s variables
  have hpre'' : ∀ φ ∈ Cond.conj c vs (srtOf c topCellSort) r.pre,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e'' (elemOf c I x.val) := fun φ hφ => by
    by_cases hT : r.pre.isTop = true
    · simp [Cond.conj, hT] at hφ
    · obtain rfl : φ = Cond.kore c vs (srtOf c topCellSort) r.pre := by simpa [Cond.conj, hT] using hφ
      have hreads : Reads c I r.vars (fun i => i ∈ varOccsCond r.vars.length r.pre) σw tbl e'' := fun i hi => by
        have hlt := varOccsCond_lt_twoT r.pre hokP i hi
        have hc : i ∈ r.condVars := List.mem_append_right _ hi
        obtain ⟨w, hw, hws⟩ := hσwv i hlt hc
        refine ⟨hlt, hkeys i hlt, w, hw, hws, fun m => ?_⟩
        have hon' : e''.evalEvar (tbl.ev (canonKey c r.vars i)) = elemOf c I w := hon i hlt hc w hw
        rw [hon']
        exact ((elemOf_spec hIΓ hws e'').1 m).symm
      exact (HoldsShape.holds_entailsCEx h hI hcw r.pre hrcP hokP hbdP (fun i hi _ => hi) hreads hkP top_numbered
        hprew _ (inh_top_PP hIΓ x tbl e'')).mpr rfl
  have hreq'' : ∀ t, r.req = some t → EvalTerm c (substOf c I tbl vs r.vars e'') t (some (bool true)) :=
    fun t ht => Exec.EvalTerm.congr (hreqw t ht) fun i hi => by
      have hc : i ∈ r.condVars := by
        simp only [Rule.condVars, ht, Option.map_some, Option.getD_some]; exact List.mem_append_left _ hi
      obtain ⟨-, hreqK, -, -⟩ := Semantics.ruleSorted_parts c hs
      have htS : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool := by
        rw [ht] at hreqK; simpa [reqOK] using hreqK
      have hi' := Exec.sortOfTerm_vars htS i hi
      obtain ⟨w, hw, hws⟩ := hσwv i hi' hc
      rw [hw, substOf_var hIΓ hg hsc.trans hnn.1 (canonVars_length c r.vars) hin''
        (List.getElem?_eq_getElem hi') (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi'] at hws; exact hws)
        (hon i hi' hc w hw).symm]
  exact ⟨_, rule_step_of_witnessed_ppCEx h hft hI hcw hs hrcP hrcQ hkeys hkP hkQ hwit x y hl'' hpre'' hy'' hens''
    hpost'' hreq''⟩

end

end Faithful

open ML Faithful
open KoreAML (VarTable)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A variable held by a cut of a rule, at a value**: in a model of `Γc`, a valuation of a
well-sorted rule's variables in their sorts under which the left side holds at a value's element
and `pre` holds there gives every variable that is `memHeldH` over the left side's variables the
element of a value of its sort, for every H whose symbols that are no constructor have `HeldBack`
in the model. -/
theorem memHeld_valuesBCEx (h : c.coreOKEx = true) (hI : I ⊧ᴵP Γc c) {H : Sym → Bool}
    (hback : ∀ f k, c.isCtor f = false → H f = true →
      lookupSig (c.rhsCtx (c.fns.map Fn.sig)).heads f = some k → HeldBack c I f k)
    {r : Rule} (hs : c.ruleSorted r = true) {tbl : VarTable} {e : Valuation M}
    (hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (x : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hpre : (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre)).interpret I e
      (elemOf c I x.val))
    (i : Nat) (hi : memHeldH c H (varOccs r.lhs) r.pre i = true) :
    Witnessed c I tbl (canonVars c r.vars) r.vars e i := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨hlhs, -, -, -⟩ := Semantics.ruleSorted_parts c hs
  obtain ⟨-, hwitL⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
    (collPat_of_sorted hph' hlhs) (Semantics.ruleSorted_lhs_nf c hs) x.property hl
  have hokP : c.condOK r.vars r.pre = true := by
    simp only [Semantics.ruleSorted, Bool.and_eq_true] at hs
    exact hs.1.1.1.1.1.2
  exact memHeldH_witnessedAt hIΓ hg hsc.trans hnn.1 (canonVars_length c r.vars) hin fns_headsOK hback hwitL
    (fun s v t hq => conjuncts_memOK hokP hq) top_numbered hpre i hi

end

namespace Faithful

open ML
open KoreAML (VarTable)
open HoldsShape (hasBinder Reads reads_of_agrees)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
variable {H : Sym → Bool}

/-- **A successor's valuation can be taken at values, for a rule with `rulePlainHeldH`** (a model
of `Γc` in which each symbol of H that is no constructor has `HeldBack`). For a well-sorted rule
with `rulePlainHeldH c H`, at a valuation of its variables in their sorts where x's element lies in
the left side, `⌈req = true⌉` and `pre`, and y's element in the right side, `⌈ens = true⌉` and
`post`: a σ of values with every premise of `StepBy` but the rule's membership and `hprio`. An open
variable the right side holds under H is a value's by `occsUnder_witnessed`, one of a confined sort
by `confined_value`, one a cut of `pre` holds by `memHeld_valuesBCEx`; a variable that passes only
the third arm makes the conditions closed and `needsWitness` hold, so they are decided: `Refuted`
fails at the valuation, and `Witnessed` gives values to all of `condVars`. -/
theorem rule_step_values_heldCEx (h : c.coreOKEx = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    {H : Sym → Bool}
    (hback : ∀ f k, c.isCtor f = false → H f = true →
      lookupSig (c.rhsCtx (c.fns.map Fn.sig)).heads f = some k → HeldBack c I f k)
    {r : Rule} (hs : c.ruleSorted r = true) (hp : c.rulePlainHeldH H r = true)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true) (hrcQ : hasBinder r.post = true → c.readsConfined = true)
    (hw : r.needsWitness c = true → r.CondDecided c)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl)
    {e : Valuation M}
    (hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (x y : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hreqm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e (elemOf c I x.val))
    (hprem : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e (elemOf c I x.val))
    (hy : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.rhs)).interpret I e (elemOf c I y.val))
    (hensm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.ens.map (Term.kore c (canonVars c r.vars))))).interpret I e (elemOf c I y.val))
    (hpostm : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.post,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e (elemOf c I y.val)) :
    ∃ σ, c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x.val ∧ (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
      Holds c r.vars.length σ r.pre true ∧ EvalTerm c σ r.rhs (some y.val) ∧
      (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.post true := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  obtain ⟨hlhs, hreqK, -, hrhs⟩ := Semantics.ruleSorted_parts c hs
  have hreq' : ∀ t, r.req = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (some (Term.kore c (canonVars c r.vars) t)))).interpret I e (elemOf c I x.val) := fun t ht => by
    rw [ht] at hreqm; exact hreqm
  have hens' : ∀ t, r.ens = some t → (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (some (Term.kore c (canonVars c r.vars) t)))).interpret I e (elemOf c I y.val) := fun t ht => by
    rw [ht] at hensm; exact hensm
  have hopens := Semantics.rulePlainHeldH_opens hp
  -- a variable the right side holds, of a confined sort, or held by a cut is a value's
  have hgood : ∀ i ∈ r.opens, ((occsUnder c H r.rhs).contains i = true ∨
      (r.vars[i]?.map c.confined).getD false = true ∨ memHeldH c H (varOccs r.lhs) r.pre i = true) →
      Witnessed c I tbl (canonVars c r.vars) r.vars e i := by
    intro i hop harm
    have hi : i < r.vars.length := by
      simp only [Rule.opens, List.mem_filter, List.mem_range] at hop; exact hop.1
    rcases harm with hA | hB | hM
    · exact occsUnder_witnessed hIΓ hg hsc.trans hnn.1 (canonVars_length c r.vars) hin fns_headsOK hback hrhs
        y.property hy i (List.contains_iff_mem.mp hA)
    · exact rule_witnessedSSx h hI hs hin x y hl hy i hi
        (Or.inr (by simp only [Rule.armAB, Bool.or_eq_true]; exact Or.inr hB))
        (fun _ => hrc (List.any_eq_true.mpr ⟨i, hop, hB⟩))
    · exact memHeld_valuesBCEx h hI hback hs hin x hl (hprem _ (by simp [Cond.conj, memHeldH_not_top hM])) i hM
  by_cases hall : ∀ i ∈ r.opens, ((occsUnder c H r.rhs).contains i = true ∨
      (r.vars[i]?.map c.confined).getD false = true ∨ memHeldH c H (varOccs r.lhs) r.pre i = true)
  · have hwit := rule_witnessed_allSSx h hIΓ hs hin x hl fun i hop => hgood i hop (hall i hop)
    obtain ⟨hσ, hag⟩ := substOf_ok hIΓ hg hsc.trans (canonVars_length c r.vars) hwit
    exact ⟨_, rule_step_of_witnessed_ppCEx h hft hI hcw hs hrcP hrcQ hkeys hkP hkQ hwit x y hl hprem hy hens' hpostm
      fun t ht => evalTrue_of_modelSSx h hft hI hcw hσ hag (by rw [ht] at hreqK; simpa [reqOK] using hreqK)
        (hreq' t ht)⟩
  -- an open variable passes the third arm only
  obtain ⟨i, hio, hiG⟩ : ∃ i ∈ r.opens, ¬ ((occsUnder c H r.rhs).contains i = true ∨
      (r.vars[i]?.map c.confined).getD false = true ∨ memHeldH c H (varOccs r.lhs) r.pre i = true) :=
    Classical.byContradiction fun hne => hall fun i hi => Classical.byContradiction fun hg' => hne ⟨i, hi, hg'⟩
  rcases hopens i hio with hG | ⟨hic, hclosed, hapart⟩
  · exact absurd hG hiG
  -- so the conditions are closed and `needsWitness` holds
  have hnw : r.needsWitness c = true := by
    have hoc : i ∈ r.openCondVars := List.mem_filter.mpr ⟨hio, List.contains_iff_mem.mpr hic⟩
    have h1 : r.reqOpen = true := by
      unfold Rule.reqOpen
      cases h' : r.openCondVars with
      | nil => rw [h'] at hoc; cases hoc
      | cons _ _ => rfl
    have h3 : (r.openCondVars.all fun i => (r.vars[i]?.map c.confined).getD false) = false :=
      List.all_eq_false.mpr ⟨i, hoc, fun hc => hiG (Or.inr (Or.inl hc))⟩
    unfold Rule.needsWitness
    rw [h1, hclosed, h3]; rfl
  rcases hw hnw with hW | href
  · obtain ⟨σw, hσw, hreqw, hprew⟩ := hW
    have hcl : ∀ j ∈ r.condVars, j ∉ varOccs r.lhs := fun j hj hjl => by
      have hc2 := hclosed
      unfold Rule.reqClosed at hc2
      have := List.all_eq_true.mp hc2 j hj
      rw [List.contains_iff_mem.mpr hjl] at this
      exact absurd this (by decide)
    obtain ⟨-, hwitL⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
      (collPat_of_sorted hph' hlhs) (Semantics.ruleSorted_lhs_nf c hs) x.property hl
    refine rule_step_C_witCEx h hft hI hcw hs hcl
      (fun j hj hjr => hapart j hj (List.mem_append_left _ (List.mem_append_left _ hjr)))
      (fun j hj t' ht' hjt => hapart j hj (List.mem_append_left _ (List.mem_append_right _ (by rw [ht']; exact hjt))))
      (fun j hj hjq => hapart j hj (List.mem_append_right _ hjq))
      hrcP hrcQ hσw hreqw hprew hkeys hkP hkQ (fun j hj hjc => ?_) x y hl hy hens' hpostm
    by_cases hL : (varOccs r.lhs).contains j = true
    · exact hwitL j (List.contains_iff_mem.mp hL)
    · have hop : j ∈ r.opens := by
        simp only [Rule.opens, List.mem_filter, List.mem_range]; exact ⟨hj, by simpa using hL⟩
      rcases hopens j hop with hG | ⟨hjc', -, -⟩
      · exact hgood j hop hG
      · exact absurd hjc' hjc
  · exact (cond_not_refuted_ppCEx h hI hs (fun i hi _ => hkeys i hi) hkP (fun i hi _ => hin i hi) hreqm hprem href).elim

/-- **The values of a successor in a rule's right side, for a rule with predicates.** For a rule r
with `ruleSorted` and `rulePlainHeldH` (not asked to be one of the definition's), in a model of `Γc`,
through a table that holds r's variables and the keys of its predicates' patterns, at a valuation
that gives each of r's variables other than the existential ones an element of its sort, where x's
element is in r's left side, in `⌈req = true⌉` and in `pre`'s patterns, and y's element is in r's
right side `∃ē. (rhs ∧ ens ∧ post)`: a σ of values with every premise of `StepBy c r σ x y` but the
rule's membership and the competitors'. A confined open variable or a binder in a predicate asks
`readsConfined`; conditions that need a witness are decided. -/
theorem stepVals_of_right_heldCEx (h : c.coreOKEx = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hback : ∀ f k, c.isCtor f = false → H f = true →
      lookupSig (c.rhsCtx (c.fns.map Fn.sig)).heads f = some k → HeldBack c I f k)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainHeldH H r = true)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true) (hrcQ : hasBinder r.post = true → c.readsConfined = true)
    (hw : r.needsWitness c = true → r.CondDecided c)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl)
    {e : Valuation M}
    (hin : ∀ i < r.vars.length, i ∉ r.exs → InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (x y : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hreqm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e (elemOf c I x.val))
    (hprem : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e (elemOf c I x.val))
    (hy : (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret I e (elemOf c I y.val)) :
    ∃ σ, c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x.val ∧ (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
      Holds c r.vars.length σ r.pre true ∧ EvalTerm c σ r.rhs (some y.val) ∧
      (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.post true := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hD := defOK hIΓ
  obtain ⟨-, -, -, -, -, -, -, -, hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  obtain ⟨hlhs, -, hreqs, -, -, hexnd, hexs, hokP, -, -, -⟩ := Model.ruleSorted_partsPP hs
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  -- the left side's, the `requires`' and `pre`'s variables are not existential
  have hnxL : ∀ i ∈ varOccs r.lhs, i < r.vars.length ∧ i ∉ r.exs := fun i hi =>
    ⟨varOccs_lt r.lhs hlhs i hi, fun hx => (hexs i hx).2.1 hi⟩
  have hnxQ : ∀ t, r.req = some t → ∀ i ∈ varOccs t, i < r.vars.length ∧ i ∉ r.exs := fun t ht i hi =>
    ⟨varOccs_lt t (hreqs t ht) i hi, fun hx => (hexs i hx).2.2 (List.mem_append_left _ (by rw [ht]; exact hi))⟩
  have hnxP : ∀ i ∈ varOccsCond r.vars.length r.pre, i < r.vars.length ∧ i ∉ r.exs := fun i hi =>
    ⟨varOccsCond_lt_twoT r.pre hokP i hi, fun hx => (hexs i hx).2.2 (List.mem_append_right _ hi)⟩
  -- inside `∃ē`: a valuation that agrees with e off ē and gives ē elements of their sorts
  rw [Model.ruleRight_eqPP hlt] at hy
  obtain ⟨eR, hoff, hguard, hbody⟩ := existsAll_elim hD (Model.ruleExBinders c r) e _
    (binders_nodupEx hkeys hlt hexnd) (binders_sortEx hlt) hy
  unfold Model.ruleRightBodyPP at hbody
  rw [interp_and (by simp)] at hbody
  have hyR := hbody (Term.kore c (canonVars c r.vars) r.rhs) (List.mem_append_left _ (List.mem_cons_self ..))
  have hensR := hbody (reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars))))
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hpostR : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.post,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I eR (elemOf c I y.val) :=
    fun φ hφ => hbody φ (List.mem_append_right _ hφ)
  have hoffE : ∀ i < r.vars.length, i ∉ r.exs →
      eR.evalEvar (tbl.ev (canonKey c r.vars i)) = e.evalEvar (tbl.ev (canonKey c r.vars i)) := by
    intro i hi hx
    refine hoff _ fun b hb he => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    exact hx ((canonKey_inj hi (hlt j hj) (ev_inj (hkeys i hi) (hkeys j (hlt j hj)) he)) ▸ hj)
  -- there every variable of r, existential or not, is in its sort
  have hinR : ∀ i < r.vars.length,
      InS I (c.sortName (r.vars.getD i 0)) (eR.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))) := by
    intro i hi
    by_cases hx : i ∈ r.exs
    · exact hguard _ (List.mem_map_of_mem (f := fun i => ((canonVars c r.vars).getD i default).kore) hx) _
        (by rw [canonVars_getD c hi]; rfl)
    · show InS I _ (eR.evalEvar (tbl.ev (canonKey c r.vars i)))
      rw [hoffE i hi hx]; exact hin i hi hx
  have hlR : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I eR (elemOf c I x.val) :=
    (tr_kore_congr r.lhs (fun i hi => (hoffE i (hnxL i hi).1 (hnxL i hi).2).symm) _).mp hl
  have hreqR : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I eR (elemOf c I x.val) :=
    reqPat_transferSplit hIΓ (fun t ht i hi => (hoffE i (hnxQ t ht i hi).1 (hnxQ t ht i hi).2).symm) hreqm
      (reqPat_inhSplit hIΓ hreqm tbl eR)
  have hpreR : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I eR (elemOf c I x.val) :=
    conj_congrPP hD hokP hkP (fun i hi => hkeys i (hnxP i hi).1)
      (fun i hi => (hoffE i (hnxP i hi).1 (hnxP i hi).2).symm) hprem
  -- the step's values, the existential variables read as the others
  exact rule_step_values_heldCEx h hft hI hcw hback hs hp hrc hrcP hrcQ hw hkeys hkP hkQ hinR x y hlR hreqR hpreR hyR hensR
    hpostR

end

end Faithful

open ML Faithful Faithful.Model

/-- **A successor in a model is a step**, for a semantics that `coreOKEx` accepts whose functions meet
`FnHyp` and whose rules have `ruleSorted` and `rulePlainHeldH` (a `pre` and a `post` allowed): in a
model of `Γc` with the step's closure, where x's element has a successor in y's element,
`Step c x y`. -/
theorem step_of_successor_heldCEx (c : Semantics) {H : Sym → Bool} (h : c.coreOKEx = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true) (hbk : HeldBackAll c H)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP (Γc c ∪ Γstep c))
    (x y : Config c) (e : Valuation M)
    (hs : (KoreAML.sNext (den c y.val)).interpret I e (elemOf c I x.val)) : Step c x y := by
  have hIc : I ⊧ᴵP Γc c := fun φ hφ => hI φ (Or.inl hφ)
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  have hrs : ∀ r ∈ c.rules, c.ruleSorted r = true := fun r hr => (hrules r hr).1
  have hd := stepDecided_ppCEx (hypSoundEx_of_coreEx h) hf.1 hrs x.val
  obtain ⟨b, hb, r, hr, tbl, e2, hkeys, hkP, hkQ, hkeysC, hin, hl, hreq, hprem, hcomp, hy⟩ :=
    step_successor_axiomPP hrs x hI e _ hs
  have hbe : b = elemOf c I y.val := ((elemOf_spec hIΓ y.property e).1 b).mp hb
  subst hbe
  obtain ⟨hsr, hpr⟩ := hrules r hr
  have hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val := by
    rcases successor_split_ppCEx h hrs x hd hIc hf.2.2.2.2.1.2 hsr (readsConfined_of_pre hr)
        (readsConfined_of_post hr) (hd r hr) hkeys hkP hkQ hkeysC hin hl hreq hprem hcomp hy with
      ⟨-, y', σ, hst, -⟩ | ⟨-, σ, hu, -⟩
    · exact (hst hr).hprio
    · exact hu.2.2
  have hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true :=
      fun hany => by
    obtain ⟨i, hi, -⟩ := List.any_eq_true.mp hany
    simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
    exact Or.inl ⟨r, hr, by simp [List.ne_nil_of_mem hi]⟩
  obtain ⟨σ, hσ, hm, hrq, hpre, hev, hen, hpo⟩ := stepVals_of_right_heldCEx h hf.1 hIc (hbk I hIc) hf.2.2.2.2.1.2 hsr hpr hrc
    (readsConfined_of_pre hr) (readsConfined_of_post hr) (hf.2.2.2.2.1.1 r hr) hkeys hkP hkQ hin x y hl hreq
    hprem hy
  exact step_iff_by.mpr ⟨r, σ, ⟨hr, hσ, hm, hrq, hpre, hev, hen, hpo, hprio⟩⟩

/-- **A `StepVBy` step between configurations is a `StepBy` step**, for a semantics that `coreOKEx`
accepts where a term has at most one result and every function terminates, whose rules are well
sorted: `pre`, `post` and each competitor's `pre` have truth values (`holds_decidedCEx`), which the
value model's truth gives (`holds_trueV`); a competitor's `requires` has a result at each of its
matches (`Rule.decided_ppCEx`). -/
theorem stepBy_of_stepVByCEx {c : Semantics} (h : c.coreOKEx = true) (hfd : FnDet c) (hft : FnTerminates c)
    (hsr : ∀ r' ∈ c.rules, c.ruleSorted r' = true)
    {r : Rule} {σ : Subst} {x y : Config c} (hb : StepVBy c r σ x.val y.val) : StepBy c r σ x y := by
  obtain ⟨hr, hσ, hm, hreq, hpre, hev, hens, hpost, hprio⟩ := hb
  have hsc := hypSoundEx_of_coreEx h
  obtain ⟨-, -, -, -, -, -, -, hokP, hokQ, -⟩ := ruleSorted_partsPP (hsr r hr)
  have htrue : ∀ {p : Cond}, c.condOK r.vars p = true → TrueV c r.vars.length σ p →
      Holds c r.vars.length σ p true := fun {p} hok ht => by
    obtain ⟨b, hb⟩ := holds_decidedCEx hsc hft p hok (hσ.at _)
    rw [(holds_trueV hfd hb).mp ht] at hb
    exact hb
  refine ⟨hr, hσ, hm, hreq, htrue hokP hpre, hev, hens, htrue hokQ hpost, fun r' hr' hlt σ' hσ' hm' => ?_⟩
  obtain ⟨hdq, b, hb⟩ := (Faithful.Rule.decided_ppCEx hsc hft (hsr r' hr') x.val).1 σ' hσ' hm'
  by_cases hq : ∀ t, r'.req = some t → EvalTerm c σ' t (some (bool true))
  · cases b with
    | false => exact .pre hb
    | true => exact (hprio r' hr' hlt ⟨σ', hσ', hm', hq, (holds_trueV hfd hb).mpr rfl⟩).elim
  · obtain ⟨t, ht, hne⟩ : ∃ t, r'.req = some t ∧ ¬ EvalTerm c σ' t (some (bool true)) := by
      exact Classical.byContradiction fun hc =>
        hq fun t ht => Classical.byContradiction fun hn => hc ⟨t, ht, hn⟩
    obtain ⟨v, hv⟩ := hdq t ht
    exact .intro ht hv fun he => hne (he ▸ hv)

/-- **The value model at a transition T is a model of `Γc` with the step's closure, where a clause
may bind variables by `\exists`**, for rules with `ruleSorted` and `rulePlainHeldH`: under
`HypModelCore`, with each clause's two predicates decided, where every T step between configurations
is a `StepV` step (`hsub`), every `StepVBy` instance of a rule without existential variables is in T
(`hall`), and for a rule with existential variables some instance that differs from a given one at ē
only is (`hsome`). The functions' equations are `AtT.satFnsGoalEx`. -/
theorem stdI_T_model_heldCEx (c : Semantics) {H : Sym → Bool} (hm : HypModelCore c) (hp : ClausePreDecided c)
    (hq : ClausePostDecided c) (hl : OpenLaws c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true)
    (T : GroundTerm → GroundTerm → Prop)
    (hsub : ∀ x y, c.sortOf x = some topCellSort → c.sortOf y = some topCellSort → T x y → StepV c x y)
    (hall : ∀ r σ x y, StepVBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ r σ x y, StepVBy c r σ x y → r.exs ≠ [] → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepVBy c r σ' x y' ∧ T x y') :
    stdI_T c T ⊧ᴵP (Γc c ∪ Γstep c) := by
  intro φ hφ
  rcases hφ with (hφ | hφ) | hφ
  · rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
    · exact AtT.satSigGoal hm φ hφ
    · exact AtT.satConsGoal hm hl φ hφ
    · exact AtT.satDomainsGoal hm φ hφ
    · exact AtT.satCollsGoal hm φ hφ
    · exact AtT.satFnsGoalEx hm (hypModelCore_clsFactsCe hm) hp hq φ hφ
    · exact satRulesGoal_held hm hrules T hall hsome φ hφ
    · exact AtT.satFallbackGoal hm φ hφ
  · obtain ⟨-, hlit, rfl⟩ := hφ
    exact boolClosed_modelClT hm hlit
  · exact satStepGoal_held hm hrules T hsub φ hφ

/-- **The choice among instances is free, for rules with `pre` and `post`**: `has_model_choice_ex`'s
statement with `rulePlainHeldH` for `rulePlainEx`, under `coreOKEx` and `FnHyp`, so a function's clauses
may bind variables by `\exists`. The model is the value model at
`liftT_ex c T`; `hsub` gives its closure through `stepVBy_of_stepBy`, `hall` and `hsome` its rules'
axioms through `stepBy_of_stepVByCEx`. -/
theorem has_model_choice_heldCEx (c : Semantics) {H : Sym → Bool} (h : c.coreOKEx = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true)
    (T : Config c → Config c → Prop)
    (hsub : ∀ x y, T x y → Step c x y)
    (hall : ∀ x y r σ, StepBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ x y r σ, StepBy c r σ x y → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y' ∧ T x y') :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      ∀ x y : Config c, T x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  have hfm := fnModel_of_fnHypCEx h hf
  have hfd := hfm.1
  have hm := hypModelCore_of_coreEx h hfm.1 hfm.2
  have hsr : ∀ r ∈ c.rules, c.ruleSorted r = true := fun r hr => (hrules r hr).1
  refine ⟨Elem, inferInstance, stdI_T c (liftT_ex c T), stdI_T_model_heldCEx c hm (clausePreDecided_of_fnHypCEx h hf) (clausePostDecided_of_fnHypCEx h hf)
      hf.2.2.2.2.2 hrules (liftT_ex c T) ?_ ?_ ?_,
    fun x y => (liftT_ex_iff T x y).symm.trans (step_iff_stdI_T c hm _ x y)⟩
  · intro x y hx hy hT
    obtain ⟨r, σ, hb⟩ := step_iff_by.mp (hsub ⟨x, hx⟩ ⟨y, hy⟩ (hT hx hy))
    exact ⟨r, σ, stepVBy_of_stepBy hfd hb⟩
  · intro r σ x y hb hex hx hy
    exact hall ⟨x, hx⟩ ⟨y, hy⟩ r σ (stepBy_of_stepVByCEx (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h hfd hf.1 hsr hb) hex
  · intro r σ x y hb _
    by_cases hx : c.sortOf x = some topCellSort
    · have hy := rhs_sorted_open hm (hrules r hb.1).1 hb.2.1 hb.2.2.2.2.2.1
      obtain ⟨y', σ', hag, hb', hT⟩ :=
        hsome ⟨x, hx⟩ ⟨y, hy⟩ r σ (stepBy_of_stepVByCEx (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h hfd hf.1 hsr hb)
      exact ⟨y'.val, σ', hag, stepVBy_of_stepBy hfd hb', fun _ _ => hT⟩
    · exact ⟨y, σ, fun _ _ => rfl, hb, fun hx' => absurd hx' hx⟩

/-- **Exactness of a definition whose rules may have a `pre` and a `post`**: `ExactC`, for a
semantics that `coreOKEx` accepts whose functions meet `FnHyp` and whose rules have `ruleSorted` and
`rulePlainHeldH`. Left to right in the model of `has_model_choice_heldCEx` at `T := Step`, right to left in
any model (`step_of_successor_heldCEx`). -/
theorem exact_heldCEx (c : Semantics) {H : Sym → Bool} (h : c.coreOKEx = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true) (hbk : HeldBackAll c H) :
    ExactC c := by
  intro x y
  constructor
  · intro hs
    obtain ⟨M, hM, I, hI, hT⟩ := has_model_choice_heldCEx c h hf hrules (Step c) (fun _ _ hst => hst)
      (fun _ _ r σ hb _ => step_iff_by.mpr ⟨r, σ, hb⟩)
      (fun _ y r σ hb => ⟨y, σ, fun _ _ => rfl, hb, step_iff_by.mpr ⟨r, σ, hb⟩⟩)
    exact ⟨M, hM, I, hI, (hT x y).mp hs⟩
  · rintro ⟨M, hM, I, hI, hn⟩
    have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
    simp only [Interpretation.satisfies, Valuation.satifies] at hn
    obtain ⟨e, hn⟩ := Classical.not_forall.mp hn
    obtain ⟨m, hn⟩ := Classical.not_forall.mp hn
    rw [interpret_impl] at hn
    have h1 : (den c x.val).interpret I e m := Classical.byContradiction fun hc => hn fun h => absurd h hc
    have h2 : (KoreAML.sNext (den c y.val)).interpret I e m :=
      Classical.byContradiction fun hc => hn fun _ => interpret_neg.mpr hc
    rw [((elemOf_spec hIΓ x.property e).1 m).mp h1] at h2
    exact step_of_successor_heldCEx c h hf hrules hbk hI x y e h2

/-! ## The statements over `coreOKEx` -/

/-- **The choice among instances is free**, for a semantics that `coreOKEx` accepts whose functions
meet `FnHyp`: `has_model_choice`'s statement with `coreOKEx` for `coreOK`. -/
theorem has_model_choice_ce (c : Semantics) (h : c.coreOKEx = true) (hf : FnHyp c)
    (T : Config c → Config c → Prop)
    (hsub : ∀ x y, T x y → Step c x y)
    (hall : ∀ x y r σ, StepBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ x y r σ, StepBy c r σ x y → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y' ∧ T x y') :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      ∀ x y : Config c, T x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) :=
  has_model_choice_heldCEx c h hf (Semantics.ruleFactsHeld_of_coreEx h) T hsub hall hsome

/-- **A successor in a model is a step**, for a semantics that `coreOKEx` accepts whose functions
meet `FnHyp`: in a model of `Γc` with the step's closure, where x's element has a successor in y's
element, `Step c x y`. -/
theorem step_of_successor_ce (c : Semantics) (h : c.coreOKEx = true) (hf : FnHyp c)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP (Γc c ∪ Γstep c))
    (x y : Config c) (e : Valuation M)
    (hs : (KoreAML.sNext (den c y.val)).interpret I e (elemOf c I x.val)) : Step c x y :=
  step_of_successor_heldCEx c h hf (Semantics.ruleFactsHeld_of_coreEx h) (heldBackAll_holdsCEx h) hI x y e hs

/-- **Exactness of a semantics** that `coreOKEx` accepts and whose functions meet `FnHyp`:
`exact_hyp`'s statement with `coreOKEx` for `coreOK`. -/
theorem exact_ce (c : Semantics) (h : c.coreOKEx = true) (hf : FnHyp c) : ExactC c :=
  exact_heldCEx c h hf (Semantics.ruleFactsHeld_of_coreEx h) (heldBackAll_holdsCEx h)

end KCore
