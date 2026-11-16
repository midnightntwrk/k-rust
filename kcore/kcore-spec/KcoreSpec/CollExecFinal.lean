/-
  KCore, checked layer: what a configuration without a listed successor is, read off the
  executable step's own matches (CollExec.lean), on a core that `execReady` accepts.

  `CExec.ruleMatches c n r x` lists the matches of r's left-hand side at x (`cmatch`, which does not
  read the fuel) with the `requires` value at fuel n: `some true`, `some false` (false or
  undefined), `none` (out of fuel). Read off that list:

  - (N) no rule applies. `noRule_of_ruleMatches`: if at some fuel n every listed match of every rule
    has `some false`, then `∀ r ∈ c.rules, NotApplies c r x`; `execReady` alone, at every n, so at
    a harness's fixed fuel too. Conversely, given `FnDet` (`noRule_iff`): if no rule applies,
    every listed match has `some false` at every fuel from some fuel on; at any one fuel no listed
    match has `some true` (`ruleMatches_ne_true`), so where no listed match is out of fuel the list
    decides N exactly (`noRule_iff_at`).
  - (U) a rule applies. `applies_of_ruleMatches`: a listed match with `some true`, at any fuel, is a
    well-sorted match whose `requires` evaluates to `true` (`execReady` alone); with `FnDet`
    the rule does not satisfy `NotApplies` (`not_notApplies_of_ruleMatches`). Conversely, given
    `FnDet`, a rule that applies has such a listed match from some fuel on
    (`ruleMatches_of_applies`).
  - The successors at one fuel. `step_iff_at`: where `outOfFuel c n x` is false (no listed match
    out of fuel, and the right-hand side of each match with `some true` evaluated), the successors
    `successorsN c n x` are exactly the `Step` successors, given `FnDet`; so an empty list
    there means that x has no `Step` successor (`noStep_at`).

  What these leave to the caller: `FnDet` (a hypothesis of the converse, of
  `not_notApplies_of_ruleMatches` and of `step_iff_at`); and, at a fixed fuel, the configurations
  where `outOfFuel` holds: there the list may miss a successor and may leave N undecided, and only
  `successorsN_sound` holds.
-/
import KcoreSpec.CollExecStepIff
import KcoreSpec.EvalFunctional

set_option autoImplicit false

namespace KCore.CExec

open KCore Exec GroundTerm

variable {c : Semantics}

/-- What `execReady` gives the step's proofs. -/
theorem execReady_parts (hr : execReady c = true) :
    c.sortedOK = true ∧ SortCtx c ∧ CClauseCtx c ∧ ClauseComplete c ∧ RuleComplete c := by
  have hr' := hr
  simp only [execReady, Bool.and_eq_true] at hr'
  have hok := hr'.1.1.1.1.1
  exact ⟨hok, sortCtx_of_all hok hr'.1.1.1.1.2 (matchCtxO_of hr'.1.1.1.2).ovlCase, cclauseCtx_of hok,
    clauseComplete_of_ready hr, ruleComplete_of_ready hr⟩

/-! ## (N): no rule applies -/

/-- **A rule whose listed matches all have `requires` `some false` does not apply**, at any fuel:
every well-sorted σ under which its left-hand side denotes x agrees on the rule's variables with a
listed match (`RuleComplete`), whose `requires` value is its `EvalTerm` result (`evalT_sound`). -/
theorem notApplies_of_ruleMatches (hr : execReady c = true) {n : Nat} {x : Config c} {r : Rule}
    (hmem : r ∈ c.rules) (h : ∀ σb ∈ ruleMatches c n r x.val, σb.2 = some false) :
    NotApplies c r x.val := by
  obtain ⟨hok, hsc, hcc, hcm, hrc⟩ := execReady_parts hr
  intro τ hτ hpv
  obtain ⟨σ₀, hσ₀m, hag⟩ := hrc r hmem x.val τ x.property hτ hpv
  have hσ₀ := (cmatch_sound hσ₀m).1
  have hf := h (σ₀, reqVal c n r σ₀) (ruleMatches_mem.mpr ⟨hσ₀m, rfl⟩)
  simp only at hf
  unfold reqVal at hf
  obtain ⟨hreq', -⟩ := ruleSorted_of hok hmem
  cases ht : r.req with
  | none => simp [ht] at hf
  | some t =>
    rw [ht] at hf hreq'
    cases he' : CExec.evalT c n σ₀ t with
    | none => simp [he'] at hf
    | some v =>
      simp only [he', Option.map_some, Option.some.injEq] at hf
      have hts := reqOK_some hreq'
      have hev := evalT_sound hsc hcc hcm n he' Exec.headsOK_fns hσ₀ hts
      refine RuleReqFails.intro ht (EvalTerm.congr hev (fun i hi => hag i (sortOfTerm_vars hts i hi))) ?_
      intro hv
      rw [hv] at hf
      exact absurd (isTrue_iff.mpr rfl) (by rw [hf]; simp)

/-- **(N) read off the step's matches**: if at some fuel n every match `ruleMatches` lists, of every
rule, has the `requires` value `some false`, no rule applies to x. Holds at every n, so at the
harness's fixed fuel; no coherence is read. -/
theorem noRule_of_ruleMatches (hr : execReady c = true) {n : Nat} {x : Config c}
    (h : ∀ r ∈ c.rules, ∀ σb ∈ ruleMatches c n r x.val, σb.2 = some false) :
    ∀ r ∈ c.rules, NotApplies c r x.val :=
  fun r hm => notApplies_of_ruleMatches hr hm (h r hm)

/-! ## (U): a rule applies -/

/-- **A listed match with `requires` `some true` is an application**, at any fuel: a well-sorted σ
under which the left-hand side denotes x and the `requires` evaluates to `true` (Step's premises
`hσ`, `hmatch`, `hreq`). -/
theorem applies_of_ruleMatches (hr : execReady c = true) {n : Nat} {x : Config c} {r : Rule}
    (hmem : r ∈ c.rules) {σ : Subst} (h : (σ, some true) ∈ ruleMatches c n r x.val) :
    c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x.val ∧
      ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)) := by
  obtain ⟨hok, hsc, hcc, hcm, -⟩ := execReady_parts hr
  obtain ⟨hσm, hb⟩ := ruleMatches_mem.mp h
  obtain ⟨hσ, hpvs⟩ := cmatch_sound hσm
  obtain ⟨hreq, -⟩ := ruleSorted_of hok hmem
  refine ⟨hσ, patVal_of_patVals hpvs, fun t ht => ?_⟩
  rw [ht] at hreq
  unfold reqVal at hb
  rw [ht] at hb
  cases he' : CExec.evalT c n σ t with
  | none => simp [he'] at hb
  | some v =>
    simp only [he', Option.map_some, Option.some.injEq] at hb
    rw [isTrue_iff.mp hb.symm] at he'
    exact evalT_sound hsc hcc hcm n he' Exec.headsOK_fns hσ (reqOK_some hreq)

/-- **(U) read off the step's matches**: a rule with a listed match whose `requires` is `some true`,
at any fuel, does not satisfy `NotApplies`, given `FnDet` (a `requires` has one result,
`EvalTerm.functional_of_fnDet`). -/
theorem not_notApplies_of_ruleMatches (hr : execReady c = true) (hfd : FnDet c) {n : Nat}
    {x : Config c} {r : Rule} (hmem : r ∈ c.rules) {σ : Subst}
    (h : (σ, some true) ∈ ruleMatches c n r x.val) : ¬ NotApplies c r x.val := by
  obtain ⟨hσ, hpv, hreq⟩ := applies_of_ruleMatches hr hmem h
  intro hna
  obtain ⟨t, v, ht, he, hv⟩ := (hna σ (hσ.at _) hpv).req_of_top
    (rule_plain_of_execReady hr hmem).1
  exact hv (EvalTerm.functional_of_fnDet hfd he (hreq t ht))

/-- **The converse of (U), with fuel**: a rule that applies to x (a well-sorted match under which
its `requires` evaluates to `true`) has, from some fuel on, a listed match with `requires`
`some true`. Given `FnDet`. The applying is stated positively: `¬ NotApplies` does not give a
`requires` result, since a function's evaluation may have none (no termination is assumed). -/
theorem ruleMatches_of_applies (hr : execReady c = true) (hfd : FnDet c) {x : Config c}
    {r : Rule} (hmem : r ∈ c.rules) {σ : Subst} (hσ : c.WellSorted r.vars σ)
    (hpv : PatVal c σ r.lhs x.val) (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) :
    ∃ N, ∀ m, N ≤ m → ∃ σ₀, (σ₀, some true) ∈ ruleMatches c m r x.val := by
  obtain ⟨hok, hsc, hcc, hcm, hrc⟩ := execReady_parts hr
  have hnaF : c.AsideFree := asideFree_of_ready hr
  obtain ⟨hrq, -⟩ := ruleSorted_of hok hmem
  obtain ⟨σ₀, hσ₀m, hag⟩ := hrc r hmem x.val σ x.property (hσ.at _) hpv
  cases hreqc : r.req with
  | none =>
    refine ⟨0, fun m _ => ⟨σ₀, ruleMatches_mem.mpr ⟨hσ₀m, ?_⟩⟩⟩
    simp [reqVal, hreqc]
  | some t =>
    rw [hreqc] at hrq
    have hts := reqOK_some hrq
    obtain ⟨n, hn⟩ := EvalTerm.exec hsc hcc hcm hfd hnaF (hreq t hreqc) r.vars _ Srt.bool Exec.headsOK_fns hσ hts
    refine ⟨n, fun m hm => ⟨σ₀, ruleMatches_mem.mpr ⟨hσ₀m, ?_⟩⟩⟩
    have hq : CExec.evalT c m σ₀ t = some (some (bool true)) := by
      rw [evalT_congr m (fun i hi => hag i (sortOfTerm_vars hts i hi))]
      exact evalT_mono_le hsc hcc hcm hfd hm hn Exec.headsOK_fns hσ hts
    simp [reqVal, hreqc, hq, isTrue_iff]

/-! ## The converse of (N) -/

/-- Where a rule does not apply, no listed match has `requires` `some true`, at any fuel. -/
theorem ruleMatches_ne_true (hr : execReady c = true) (hfd : FnDet c) {n : Nat}
    {x : Config c} {r : Rule} (hmem : r ∈ c.rules) (h : NotApplies c r x.val) :
    ∀ σb ∈ ruleMatches c n r x.val, σb.2 ≠ some true := by
  rintro ⟨σ, b⟩ hσb (hb : b = some true)
  subst hb
  exact not_notApplies_of_ruleMatches hr hfd hmem hσb h

/-- **The converse of (N), with fuel as in `step_iff`**: where no rule applies, from some fuel on
every listed match of every rule has `requires` `some false` (each `requires` result is computed
with some fuel, `EvalTerm.exec`, and kept with more, `evalT_mono`; `cmatch` lists finitely many
matches and does not read the fuel). Given `FnDet`. -/
theorem ruleMatches_of_noRule (hr : execReady c = true) (hfd : FnDet c) {x : Config c}
    (h : ∀ r ∈ c.rules, NotApplies c r x.val) :
    ∃ N, ∀ m, N ≤ m → ∀ r ∈ c.rules, ∀ σb ∈ ruleMatches c m r x.val, σb.2 = some false := by
  obtain ⟨hok, hsc, hcc, hcm, -⟩ := execReady_parts hr
  have hnaF : c.AsideFree := asideFree_of_ready hr
  let all := c.rules.flatMap fun r' => (cmatch c r'.vars [r'.lhs] [x.val]).map (r', ·)
  obtain ⟨N, hN⟩ := fuel_list
    (P := fun n (a : Rule × Subst) => a.1 ∈ c.rules ∧ c.WellSorted a.1.vars a.2 ∧
      ∃ t v, a.1.req = some t ∧ CExec.evalT c n a.2 t = some v ∧ v ≠ some (bool true))
    (fun n a ⟨har, haw, t, v, ht, he, hv⟩ => by
      obtain ⟨hrq', -⟩ := ruleSorted_of hok har
      rw [ht] at hrq'
      exact ⟨har, haw, t, v, ht, evalT_mono hsc hcc hcm hfd n he Exec.headsOK_fns haw (reqOK_some hrq'), hv⟩)
    (l := all) (fun a ha => by
      obtain ⟨r', hr', ha⟩ := List.mem_flatMap.mp ha
      obtain ⟨σ', hσ', rfl⟩ := List.mem_map.mp ha
      obtain ⟨hσw, hpvs⟩ := cmatch_sound hσ'
      obtain ⟨t, v, ht, he, hv⟩ := (h r' hr' σ' (hσw.at _) (patVal_of_patVals hpvs)).req_of_top
        (rule_plain_of_execReady hr hr').1
      obtain ⟨hrq', -⟩ := ruleSorted_of hok hr'
      rw [ht] at hrq'
      obtain ⟨n, hn⟩ := EvalTerm.exec hsc hcc hcm hfd hnaF he r'.vars _ Srt.bool Exec.headsOK_fns hσw
        (reqOK_some hrq')
      exact ⟨n, hr', hσw, t, v, ht, hn, hv⟩)
  refine ⟨N, fun m hm r' hr' σb hσb => ?_⟩
  obtain ⟨σ', b⟩ := σb
  obtain ⟨hσ', rfl⟩ := ruleMatches_mem.mp hσb
  have hmem : (r', σ') ∈ all :=
    List.mem_flatMap.mpr ⟨r', hr', List.mem_map.mpr ⟨σ', hσ', rfl⟩⟩
  obtain ⟨t, v, ht, he, hv⟩ := (hN _ hmem m hm).2.2
  show reqVal c m r' σ' = some false
  unfold reqVal
  rw [ht]
  simp only [he, Option.map_some, Option.some.injEq]
  cases hb : isTrue v
  · rfl
  · exact absurd (isTrue_iff.mp hb) hv

/-- **(N) and the step's matches, both ways**: no rule applies to x exactly when, at some fuel,
every match `ruleMatches` lists of every rule has `requires` `some false` (`←` at every fuel,
`noRule_of_ruleMatches`; `→` from some fuel on, `ruleMatches_of_noRule`). Given `FnDet`. -/
theorem noRule_iff (hr : execReady c = true) (hfd : FnDet c) (x : Config c) :
    (∀ r ∈ c.rules, NotApplies c r x.val) ↔
      ∃ n, ∀ r ∈ c.rules, ∀ σb ∈ ruleMatches c n r x.val, σb.2 = some false := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := ruleMatches_of_noRule hr hfd h
    exact ⟨N, hN N (Nat.le_refl _)⟩
  · rintro ⟨n, hn⟩
    exact noRule_of_ruleMatches hr hn

/-- **(N) decided at one fuel**: where no listed match is out of fuel, no rule applies to x exactly
when every listed match of every rule has `requires` `some false`. Given `FnDet`. -/
theorem noRule_iff_at (hr : execReady c = true) (hfd : FnDet c) {n : Nat} (x : Config c)
    (hf : ∀ r ∈ c.rules, ∀ σb ∈ ruleMatches c n r x.val, σb.2 ≠ none) :
    (∀ r ∈ c.rules, NotApplies c r x.val) ↔
      ∀ r ∈ c.rules, ∀ σb ∈ ruleMatches c n r x.val, σb.2 = some false := by
  constructor
  · intro h r hm σb hσb
    have h1 := hf r hm σb hσb
    have h2 := ruleMatches_ne_true hr hfd hm (h r hm) σb hσb
    match σb.2, h1, h2 with
    | some false, _, _ => rfl
    | none, h1, _ => exact absurd rfl h1
    | some true, _, h2 => exact absurd rfl h2
  · exact noRule_of_ruleMatches hr

/-! ## The successors at one fuel -/

/-- What `outOfFuel c n x = false` says of each listed match. -/
theorem of_outOfFuel_false {n : Nat} {x : GroundTerm} (hf : outOfFuel c n x = false) {r : Rule}
    (hmem : r ∈ c.rules) {σ : Subst} {b : Option Bool} (hm : (σ, b) ∈ ruleMatches c n r x) :
    b ≠ none ∧ (b = some true → (CExec.evalT c n σ r.rhs).isSome = true ∧ ensVal c n r σ ≠ none) := by
  unfold outOfFuel at hf
  have h1 := List.any_eq_false.mp hf r hmem
  rw [Bool.not_eq_true, List.any_eq_false] at h1
  have h2 := h1 (σ, b) hm
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, not_or, not_and] at h2
  refine ⟨h2.1, fun hb => ?_⟩
  have := h2.2 hb
  refine ⟨?_, this.2⟩
  cases he : CExec.evalT c n σ r.rhs with
  | none => have := this.1; rw [he] at this; simp at this
  | some _ => rfl

/-- **The step at one fuel is exact where nothing ran out of fuel**: if `outOfFuel c n x` is false,
the configurations `successorsN c n x` lists are exactly x's `Step` successors. Given `FnDet`
(a `requires` and a right-hand side have one result). `step_iff` gives the same for some fuel;
this one is for the fuel the caller ran, with the condition it can check. -/
theorem step_iff_at (hr : execReady c = true) (hfd : FnDet c) {n : Nat} {x y : Config c}
    (hf : outOfFuel c n x.val = false) : Step c x y ↔ y.val ∈ successorsN c n x.val := by
  obtain ⟨hok, hsc, hcc, hcm, hrc⟩ := execReady_parts hr
  constructor
  · rintro ⟨r, hmem, σ, hσ, hmatch, hreq, -, heval, hens, -, hprio⟩
    obtain ⟨hrq, hrt⟩ := ruleSorted_of hok hmem
    have hen := ruleSorted_ens_of hok hmem
    obtain ⟨σ₀, hσ₀m, hag⟩ := hrc r hmem x.val σ x.property (hσ.at _) hmatch
    have hσ₀ := (cmatch_sound hσ₀m).1
    have hb : reqVal c n r σ₀ = some true := by
      have hne := (of_outOfFuel_false hf hmem (ruleMatches_mem.mpr ⟨hσ₀m, rfl⟩)).1
      unfold reqVal at hne ⊢
      cases hreqc : r.req with
      | none => rfl
      | some t =>
        rw [hreqc] at hne hrq
        cases he : CExec.evalT c n σ₀ t with
        | none => simp [he] at hne
        | some v =>
          have hts := reqOK_some hrq
          have hev := evalT_sound hsc hcc hcm n he Exec.headsOK_fns hσ₀ hts
          have hev' := EvalTerm.congr hev (fun i hi => hag i (sortOfTerm_vars hts i hi))
          have := EvalTerm.functional_of_fnDet hfd hev' (hreq t hreqc)
          subst this
          simp [he, isTrue_iff]
    have hm₀ : (σ₀, some true) ∈ ruleMatches c n r x.val := ruleMatches_mem.mpr ⟨hσ₀m, hb.symm⟩
    have hrhs : CExec.evalT c n σ₀ r.rhs = some (some y.val) := by
      have hs := ((of_outOfFuel_false hf hmem hm₀).2 rfl).1
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hs
      have hev := evalT_sound hsc hcc hcm n ho Exec.headsOK_fns hσ₀ hrt
      have hev' := EvalTerm.congr hev (fun i hi => hag i (sortOfTerm_vars hrt i hi))
      rw [ho, EvalTerm.functional_of_fnDet hfd hev' heval]
    have hensV : ensVal c n r σ₀ = some true := by
      have hne := ((of_outOfFuel_false hf hmem hm₀).2 rfl).2
      unfold ensVal at hne ⊢
      cases hensc : r.ens with
      | none => rfl
      | some t =>
        rw [hensc] at hne hen
        cases he : CExec.evalT c n σ₀ t with
        | none => simp [he] at hne
        | some v =>
          have hts := reqOK_some hen
          have hev := evalT_sound hsc hcc hcm n he Exec.headsOK_fns hσ₀ hts
          have hev' := EvalTerm.congr hev (fun i hi => hag i (sortOfTerm_vars hts i hi))
          have := EvalTerm.functional_of_fnDet hfd hev' (hens t hensc)
          subst this
          simp [he, isTrue_iff]
    refine successorsN_of hmem (fun r' hr' hlt σb hσb => ?_) hm₀ hrhs y.property hensV
    obtain ⟨σ', b⟩ := σb
    have hne := (of_outOfFuel_false hf hr' hσb).1
    have hnt : b ≠ some true := by
      rintro rfl
      obtain ⟨hσ', hpv', hreq'⟩ := applies_of_ruleMatches hr hr' hσb
      obtain ⟨t, v, ht, he, hv⟩ := (hprio r' hr' hlt σ' (hσ'.at _) hpv').req_of_top
        (rule_plain_of_execReady hr hr').1
      exact hv (EvalTerm.functional_of_fnDet hfd he (hreq' t ht))
    show b = some false
    match b, hne, hnt with
    | some false, _, _ => rfl
    | none, h, _ => exact absurd rfl h
    | some true, _, h => exact absurd rfl h
  · intro hy
    obtain ⟨_, hst⟩ := successorsN_step_ready hr hy
    exact hst

/-- **A configuration where nothing ran out of fuel is `StepDecided`**: each match of a rule's
left-hand side agrees on the rule's variables with a listed match (`RuleComplete`), whose
`requires` has a value at fuel n, and, where that value is `true`, whose right-hand side and
`ensures` have values (`outOfFuel c n x = false`); each value is an `EvalTerm` result
(`evalT_sound`). Given `FnDet`: a `requires` that evaluates to `true` under the match is the
listed match's value (one result). -/
theorem stepDecided_of_fuel (hr : execReady c = true) (hfd : FnDet c) {n : Nat} {x : Config c}
    (hf : outOfFuel c n x.val = false) : StepDecided c x.val := by
  obtain ⟨hok, hsc, hcc, hcm, hrc⟩ := execReady_parts hr
  intro r hmem _
  obtain ⟨hpre₀, hpost₀, hb₀⟩ := rule_plain_of_execReady hr hmem
  suffices H : ∀ σ, c.WellSorted r.vars σ → PatVal c σ r.lhs x.val →
      (∀ t, r.req = some t → ∃ v, EvalTerm c σ t v) ∧
      ((∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) →
        (∃ v, EvalTerm c σ r.rhs v) ∧ ∀ e, r.ens = some e → ∃ w, EvalTerm c σ e w) from
    ⟨fun σ hσ hm => ⟨(H σ (Rule.wellSorted_of_at hb₀ hσ) hm).1, true, hpre₀ ▸ .top⟩,
     fun σ hσ hm hq _ => ⟨((H σ hσ hm).2 hq).1, ((H σ hσ hm).2 hq).2, true, hpost₀ ▸ .top⟩⟩
  intro σ hσ hmatch
  obtain ⟨hrq, hrt⟩ := ruleSorted_of hok hmem
  have hen := ruleSorted_ens_of hok hmem
  obtain ⟨σ₀, hσ₀m, hag⟩ := hrc r hmem x.val σ x.property (hσ.at _) hmatch
  have hσ₀ := (cmatch_sound hσ₀m).1
  obtain ⟨hne, hb⟩ := of_outOfFuel_false hf hmem (ruleMatches_mem.mpr ⟨hσ₀m, rfl⟩)
  refine ⟨fun t ht => ?_, fun hreq => ?_⟩
  · unfold reqVal at hne
    rw [ht] at hne hrq
    cases he : CExec.evalT c n σ₀ t with
    | none => simp [he] at hne
    | some v =>
      have hts := reqOK_some hrq
      exact ⟨v, EvalTerm.congr (evalT_sound hsc hcc hcm n he Exec.headsOK_fns hσ₀ hts)
        (fun i hi => hag i (sortOfTerm_vars hts i hi))⟩
  have hbt : reqVal c n r σ₀ = some true := by
    unfold reqVal at hne ⊢
    cases hreqc : r.req with
    | none => rfl
    | some t =>
      rw [hreqc] at hne hrq
      cases he : CExec.evalT c n σ₀ t with
      | none => simp [he] at hne
      | some v =>
        have hts := reqOK_some hrq
        have hev := evalT_sound hsc hcc hcm n he Exec.headsOK_fns hσ₀ hts
        have hev' := EvalTerm.congr hev (fun i hi => hag i (sortOfTerm_vars hts i hi))
        have := EvalTerm.functional_of_fnDet hfd hev' (hreq t hreqc)
        subst this
        simp [he, isTrue_iff]
  obtain ⟨hrhs, hens⟩ := hb hbt
  refine ⟨?_, fun t ht => ?_⟩
  · obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hrhs
    exact ⟨o, EvalTerm.congr (evalT_sound hsc hcc hcm n ho Exec.headsOK_fns hσ₀ hrt)
      (fun i hi => hag i (sortOfTerm_vars hrt i hi))⟩
  · unfold ensVal at hens
    rw [ht] at hens hen
    cases he : CExec.evalT c n σ₀ t with
    | none => simp [he] at hens
    | some v =>
      have hts := reqOK_some hen
      exact ⟨v, EvalTerm.congr (evalT_sound hsc hcc hcm n he Exec.headsOK_fns hσ₀ hts)
        (fun i hi => hag i (sortOfTerm_vars hts i hi))⟩

/-- **No listed successor at a fuel where nothing ran out means no successor**: if `outOfFuel c n x`
is false and `successorsN c n x` is empty, x has no `Step` successor. Given `FnDet`. -/
theorem noStep_at (hr : execReady c = true) (hfd : FnDet c) {n : Nat} {x : Config c}
    (hf : outOfFuel c n x.val = false) (he : successorsN c n x.val = []) (y : Config c) :
    ¬ Step c x y := by
  intro hst
  have := (step_iff_at hr hfd hf).mp hst
  rw [he] at this
  nomatch this

end KCore.CExec
