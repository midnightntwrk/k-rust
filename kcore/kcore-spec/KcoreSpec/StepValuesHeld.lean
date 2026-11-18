/-
  KCore. A successor's valuation can be taken at values, for a rule whose open variables the right
  side or a cut holds under a set of symbols.

  `Semantics.rulePlainHeldH c H r` is `rulePlainPP` with two readings widened over a set H of held
  symbols: the first arm reads the variables the right side holds under constructors, injections
  and the symbols of H (`occsUnder c H`), and a variable counts as decided, where `rulePlainPP`
  asks a confined sort, also if a cut of `pre` holds it (`memHeldH c H` over the left side's
  variables). `Semantics.rulePlainHO1` (PredPlain.lean), what `rulesPlain` asks of one rule, gives
  `rulePlainHeldH` at `Semantics.holds`, so `coreOK` and `HypModelCore` give it of each rule
  (`Semantics.ruleFactsHeld_of_core`, `HypModelCore.ruleFactsHeld`); `rulePlainHeldH` is monotone
  in H.

  `rule_step_values_held` is `rule_step_values_pp`'s statement for a rule with `rulePlainHeldH`, in
  a model where each symbol of H that is no constructor has `HeldBack`: an open variable the right
  side holds is a value's by `occsUnder_witnessed`, one a cut holds by `memHeld_valuesB`, one of a
  confined sort by `confined_value`; under the third arm the conditions are closed, `needsWitness`
  holds and the conditions' variables take the witness's values (`rule_step_C_wit`).
-/
import KcoreSpec.StepValuesPP
import KcoreSpec.MemHeldValues

set_option autoImplicit false

namespace KCore

/-- **The conjunct of the plain shapes for one rule, over a set H of held symbols**: `rulePlainPP`
with the first arm reading the variables the right side holds under constructors, injections and
the symbols of H, and `conf` reading "of a confined sort, or held by a cut of `pre`". -/
def Semantics.rulePlainHeldH (c : Semantics) (H : Sym → Bool) (r : Rule) : Bool :=
  let conf := fun i => (r.vars[i]?.map c.confined).getD false || memHeldH c H (varOccs r.lhs) r.pre i
  let rest := varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post
  let condApart := r.reqClosed && r.condVars.all fun j => !rest.contains j
  r.opens.all (fun i => (occsUnder c H r.rhs).contains i || conf i || (r.condVars.contains i && condApart)) &&
  (!r.reqOpen || !c.rules.any (fun r' => r.prio < r'.prio) || r.openCondVars.all conf || r.reqClosed)

/-- **What `rulePlainHeldH` says of an open variable**: the right side holds it, or its sort is
confined, or a cut holds it; or it is a condition variable, the conditions are closed and none of
their variables is held by the right side, the `ensures` or `post`. -/
theorem Semantics.rulePlainHeldH_opens {c : Semantics} {H : Sym → Bool} {r : Rule}
    (hp : c.rulePlainHeldH H r = true) : ∀ i ∈ r.opens,
      ((occsUnder c H r.rhs).contains i = true ∨ (r.vars[i]?.map c.confined).getD false = true ∨
        memHeldH c H (varOccs r.lhs) r.pre i = true) ∨
      (i ∈ r.condVars ∧ r.reqClosed = true ∧ ∀ j ∈ r.condVars,
        j ∉ varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post) := by
  simp only [Semantics.rulePlainHeldH, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hp
  intro i hi
  rcases hp.1 i hi with (hA | hB | hM) | ⟨hC, hcl, hap⟩
  · exact Or.inl (Or.inl hA)
  · exact Or.inl (Or.inr (Or.inl hB))
  · exact Or.inl (Or.inr (Or.inr hM))
  · refine Or.inr ⟨List.contains_iff_mem.mp hC, hcl, fun j hj hjr => ?_⟩
    have := hap j hj
    rw [List.contains_iff_mem.mpr hjr] at this
    exact absurd this (by decide)

/-- **What `rulePlainHeldH` says of a rule that competes with a larger one**: no condition
variable is open, or each open condition variable is of a confined sort or held by a cut, or the
conditions are closed. -/
theorem Semantics.rulePlainHeldH_compete {c : Semantics} {H : Sym → Bool} {r : Rule}
    (hp : c.rulePlainHeldH H r = true) (hlarger : c.rules.any (fun r'' => r.prio < r''.prio) = true) :
    r.reqOpen = false ∨
      (∀ i ∈ r.openCondVars, (r.vars[i]?.map c.confined).getD false = true ∨
        memHeldH c H (varOccs r.lhs) r.pre i = true) ∨ r.reqClosed = true := by
  simp only [Semantics.rulePlainHeldH, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hp
  rcases hp.2 with ((h1 | h2) | h3) | h4
  · exact Or.inl (by simpa using h1)
  · rw [hlarger] at h2; exact absurd h2 (by decide)
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr h4)

/-- `rulePlainHeldH` is monotone in the set of held symbols. -/
theorem Semantics.rulePlainHeldH_mono {c : Semantics} {H H' : Sym → Bool} (hH : ∀ f, H f = true → H' f = true)
    {r : Rule} (hp : c.rulePlainHeldH H r = true) : c.rulePlainHeldH H' r = true := by
  simp only [Semantics.rulePlainHeldH, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hp ⊢
  have hm : ∀ i, memHeldH c H (varOccs r.lhs) r.pre i = true → memHeldH c H' (varOccs r.lhs) r.pre i = true :=
    fun i hi => by
      obtain ⟨s, v, t, hq, hv, hti⟩ := memHeldH_parts hi
      exact memHeldH_of_parts hq hv (occsUnder_mono c hH t i hti)
  refine ⟨fun i hi => ?_, ?_⟩
  · rcases hp.1 i hi with (hA | hB | hM) | hC
    · exact Or.inl (Or.inl (List.contains_iff_mem.mpr (occsUnder_mono c hH _ i (List.contains_iff_mem.mp hA))))
    · exact Or.inl (Or.inr (Or.inl hB))
    · exact Or.inl (Or.inr (Or.inr (hm i hM)))
    · exact Or.inr hC
  · rcases hp.2 with ((h1 | h2) | h3) | h4
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inl (Or.inl (Or.inr h2))
    · exact Or.inl (Or.inr fun i hi => (h3 i hi).imp id (hm i))
    · exact Or.inr h4

/-- A rule with `rulePlainHO1` has `rulePlainHeldH` at `Semantics.holds`. -/
theorem Semantics.rulePlainHeldH_of_HO1 {c : Semantics} {r : Rule} (hp : c.rulePlainHO1 r = true) :
    c.rulePlainHeldH c.holds r = true := by
  simp only [Semantics.rulePlainHO1, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hp
  simp only [Semantics.rulePlainHeldH, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true]
  refine ⟨fun i hi => ?_, ?_⟩
  · rcases hp.1 i hi with (hA | hB) | hC
    · rw [heldOccs_eq] at hA; exact Or.inl (Or.inl hA)
    · exact Or.inl (Or.inr (Or.inl hB))
    · exact Or.inr hC
  · rcases hp.2 with ((h1 | h2) | h3) | h4
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inl (Or.inl (Or.inr h2))
    · exact Or.inl (Or.inr fun i hi => Or.inl (h3 i hi))
    · exact Or.inr h4

/-- What `coreOK` gives of each rule: `ruleSorted`, and `rulePlainHeldH` at the symbols
`Semantics.holds` names. -/
theorem Semantics.ruleFactsHeld_of_core {c : Semantics} (h : c.coreOK = true) :
    ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH c.holds r = true := fun r hr =>
  ⟨(Semantics.ruleFactsHO1_of_core h r hr).1,
    Semantics.rulePlainHeldH_of_HO1 (Semantics.ruleFactsHO1_of_core h r hr).2⟩

/-- What `HypModelCore` gives of each rule: `ruleSorted`, and `rulePlainHeldH` at the symbols
`Semantics.holds` names. -/
theorem Faithful.Model.HypModelCore.ruleFactsHeld {c : Semantics} (h : Faithful.Model.HypModelCore c) :
    ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH c.holds r = true := fun _ hr =>
  ⟨(h.ruleFactsHO1 hr).1, Semantics.rulePlainHeldH_of_HO1 (h.ruleFactsHO1 hr).2⟩

namespace Faithful

open ML
open KoreAML (VarTable)
open HoldsShape (hasBinder Reads reads_of_agrees)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The conditions' variables at a witness's values.** Where the conditions are witnessed by
values σw (their `requires` `true`, their `pre` holding), none of their variables is held by the
left side, the right side, the `ensures` or `post`, and the valuation gives every other variable
the element of a value: the valuation that gives the conditions' variables σw's values and keeps
the others has a substitution with every premise of `StepBy` but the rule's membership and
`hprio`. -/
theorem rule_step_C_wit (h : c.coreOK = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
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
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
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
      exact (HoldsShape.holds_entails h hI hcw r.pre hrcP hokP hbdP (fun i hi _ => hi) hreads hkP top_numbered
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
  exact ⟨_, rule_step_of_witnessed_pp h hft hI hcw hs hrcP hrcQ hkeys hkP hkQ hwit x y hl'' hpre'' hy'' hens''
    hpost'' hreq''⟩

/-- **A successor's valuation can be taken at values, for a rule with `rulePlainHeldH`** (a model
of `Γc` in which each symbol of H that is no constructor has `HeldBack`). For a well-sorted rule
with `rulePlainHeldH c H`, at a valuation of its variables in their sorts where x's element lies in
the left side, `⌈req = true⌉` and `pre`, and y's element in the right side, `⌈ens = true⌉` and
`post`: a σ of values with every premise of `StepBy` but the rule's membership and `hprio`. An open
variable the right side holds under H is a value's by `occsUnder_witnessed`, one of a confined sort
by `confined_value`, one a cut of `pre` holds by `memHeld_valuesB`; a variable that passes only
the third arm makes the conditions closed and `needsWitness` hold, so they are decided: `Refuted`
fails at the valuation, and `Witnessed` gives values to all of `condVars`. -/
theorem rule_step_values_held (h : c.coreOK = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
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
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
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
    · exact rule_witnessed h hI hs hin x y hl hy i hi
        (Or.inr (by simp only [Rule.armAB, Bool.or_eq_true]; exact Or.inr hB))
        (fun _ => hrc (List.any_eq_true.mpr ⟨i, hop, hB⟩))
    · exact memHeld_valuesB h hI hback hs hin x hl (hprem _ (by simp [Cond.conj, memHeldH_not_top hM])) i hM
  by_cases hall : ∀ i ∈ r.opens, ((occsUnder c H r.rhs).contains i = true ∨
      (r.vars[i]?.map c.confined).getD false = true ∨ memHeldH c H (varOccs r.lhs) r.pre i = true)
  · have hwit := rule_witnessed_all h hIΓ hs hin x hl fun i hop => hgood i hop (hall i hop)
    obtain ⟨hσ, hag⟩ := substOf_ok hIΓ hg hsc.trans (canonVars_length c r.vars) hwit
    exact ⟨_, rule_step_of_witnessed_pp h hft hI hcw hs hrcP hrcQ hkeys hkP hkQ hwit x y hl hprem hy hens' hpostm
      fun t ht => evalTrue_of_model h hft hI hcw hσ hag (by rw [ht] at hreqK; simpa [reqOK] using hreqK)
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
      (collPat_of_sorted hph' hlhs) (Semantics.lhs_nf OvlOK.ok hr hlhs) x.property hl
    refine rule_step_C_wit h hft hI hcw hs hcl
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
  · exact (cond_not_refuted_pp h hI hs (fun i hi _ => hkeys i hi) hkP (fun i hi _ => hin i hi) hreqm hprem href).elim

end

end Faithful

end KCore
