/-
  KCore, checked layer: what a configuration without a listed successor is, read off the
  executable step's own matches (CollExec.lean), on a core that `execReady` accepts.

  `CExec.ruleMatches c n r x` lists the matches of r's left-hand side at x (`cmatch`, which does not
  read the fuel) with their value at fuel n (`matchVal`, of the `requires` and the `pre`): `some
  true` (the `requires` true and the `pre` true), `some false` (the `requires` false or undefined,
  or the `pre` false), `none` (out of fuel). A `pre` and a `post` are conjunctions of `\in` and
  `\equals` atoms (`predAtoms`, which `execReady` asks), evaluated by `predVal`. Read off that list:

  - (N) no rule applies. `noRule_of_ruleMatches`: if at some fuel n every listed match of every rule
    has `some false`, then `∀ r ∈ c.rules, NotApplies c r x`; `execReady` alone, at every n, so at
    a harness's fixed fuel too. Conversely, given `FnDet` (`noRule_iff`): if no rule applies,
    every listed match has `some false` at every fuel from some fuel on; at any one fuel no listed
    match has `some true` (`ruleMatches_ne_true`), so where no listed match is out of fuel the list
    decides N exactly (`noRule_iff_at`).
  - (U) a rule applies. `applies_of_ruleMatches`: a listed match with `some true`, at any fuel, is a
    well-sorted match whose `requires` evaluates to `true` and whose `pre` holds (`execReady`
    alone); with `FnDet`
    the rule does not satisfy `NotApplies` (`not_notApplies_of_ruleMatches`). Conversely, given
    `FnDet`, a rule that applies has such a listed match from some fuel on
    (`ruleMatches_of_applies`).
  - The successors at one fuel. `step_iff_at`: where `outOfFuel c n x` is false (the `requires` and
    the `pre` of each listed match evaluated, and the right-hand side, the `ensures` and the `post`
    of each match with `some true`), the successors
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
  replace hr' := hr'.1
  have hok := hr'.1.1.1.1.1
  exact ⟨hok, sortCtx_of_all hok hr'.1.1.1.1.2 (matchCtxO_of hr'.1.1.1.2).ovlCase, cclauseCtx_of hok,
    clauseComplete_of_ready hr, ruleComplete_of_ready hr⟩

/-! ## (N): no rule applies -/

/-- **Two values of a predicate `predVal` evaluates are one**, given `FnDet` (each term has one
result, `EvalTerm.functional_of_fnDet`). -/
theorem holds_atoms_functional (hfd : FnDet c) : ∀ {p : Cond}, predAtoms p = true →
    ∀ {k : Nat} {σ : Subst} {b b' : Bool}, Holds c k σ p b → Holds c k σ p b' → b = b'
  | .top, _, _, _, _, _, h, h' => by cases h; cases h'; rfl
  | .equals _ _ _, _, _, _, _, _, h, h' => by
    cases h with
    | equals h₁ h₂ =>
      cases h' with
      | equals h₁' h₂' =>
        rw [EvalTerm.functional_of_fnDet hfd h₁ h₁', EvalTerm.functional_of_fnDet hfd h₂ h₂']
  | .mem _ _ _, _, _, _, _, _, h, h' => by
    cases h with
    | mem h₁ h₂ =>
      cases h' with
      | mem h₁' h₂' =>
        rw [EvalTerm.functional_of_fnDet hfd h₁ h₁', EvalTerm.functional_of_fnDet hfd h₂ h₂']
  | .and p q, ha, _, _, _, _, h, h' => by
    simp only [predAtoms, Bool.and_eq_true] at ha
    cases h with
    | and h₁ h₂ =>
      cases h' with
      | and h₁' h₂' =>
        rw [holds_atoms_functional hfd ha.1 h₁ h₁', holds_atoms_functional hfd ha.2 h₂ h₂']
  | .bot, ha, _, _, _, _, _, _ | .not _, ha, _, _, _, _, _, _ | .or _ _, ha, _, _, _, _, _, _
  | .implies _ _, ha, _, _, _, _, _, _ | .ceil _ _, ha, _, _, _, _, _, _
  | .exMatch _ _ _ _ _, ha, _, _, _, _, _, _ | .ex _ _, ha, _, _, _, _, _, _
  | .all _ _, ha, _, _, _, _, _, _ => by simp [predAtoms] at ha

/-- **A rule whose listed matches all have the value `some false` does not apply**, at any fuel:
every well-sorted σ under which its left-hand side denotes x agrees on the rule's variables with a
listed match (`RuleComplete`), whose `requires` value is its `EvalTerm` result (`evalT_sound`) and
whose `pre` value its `Holds` value (`predVal_sound`). -/
theorem notApplies_of_ruleMatches (hr : execReady c = true) {n : Nat} {x : Config c} {r : Rule}
    (hmem : r ∈ c.rules) (h : ∀ σb ∈ ruleMatches c n r x.val, σb.2 = some false) :
    NotApplies c r x.val := by
  obtain ⟨hok, hsc, hcc, hcm, hrc⟩ := execReady_parts hr
  intro τ hτ hpv
  obtain ⟨σ₀, hσ₀m, hag⟩ := hrc r hmem x.val τ x.property hτ hpv
  exact ruleReqFails_of_matchVal hsc hcc hcm hok hmem (cmatch_sound hσ₀m).1 hag
    (h (σ₀, matchVal c n r σ₀) (ruleMatches_mem.mpr ⟨hσ₀m, rfl⟩))

/-- **(N) read off the step's matches**: if at some fuel n every match `ruleMatches` lists, of every
rule, has the value `some false`, no rule applies to x. Holds at every n, so at the harness's fixed
fuel; no coherence is read. -/
theorem noRule_of_ruleMatches (hr : execReady c = true) {n : Nat} {x : Config c}
    (h : ∀ r ∈ c.rules, ∀ σb ∈ ruleMatches c n r x.val, σb.2 = some false) :
    ∀ r ∈ c.rules, NotApplies c r x.val :=
  fun r hm => notApplies_of_ruleMatches hr hm (h r hm)

/-! ## (U): a rule applies -/

/-- **A listed match with value `some true` is an application**, at any fuel: a well-sorted σ under
which the left-hand side denotes x, the `requires` evaluates to `true` and the `pre` holds (Step's
premises `hσ`, `hmatch`, `hreq`, `hpre`). -/
theorem applies_of_ruleMatches (hr : execReady c = true) {n : Nat} {x : Config c} {r : Rule}
    (hmem : r ∈ c.rules) {σ : Subst} (h : (σ, some true) ∈ ruleMatches c n r x.val) :
    c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x.val ∧
      (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
      Holds c r.vars.length σ r.pre true := by
  obtain ⟨hok, hsc, hcc, hcm, -⟩ := execReady_parts hr
  obtain ⟨hσm, hb⟩ := ruleMatches_mem.mp h
  obtain ⟨hσ, hpvs⟩ := cmatch_sound hσm
  obtain ⟨hreq, hpre⟩ := req_pre_of_matchVal hsc hcc hcm hok hmem hσ hb.symm
  exact ⟨hσ, patVal_of_patVals hpvs, hreq, hpre⟩

/-- **(U) read off the step's matches**: a rule with a listed match whose value is `some true`, at
any fuel, does not satisfy `NotApplies`, given `FnDet` (a `requires` has one result,
`EvalTerm.functional_of_fnDet`, and a `pre` one value, `holds_atoms_functional`). -/
theorem not_notApplies_of_ruleMatches (hr : execReady c = true) (hfd : FnDet c) {n : Nat}
    {x : Config c} {r : Rule} (hmem : r ∈ c.rules) {σ : Subst}
    (h : (σ, some true) ∈ ruleMatches c n r x.val) : ¬ NotApplies c r x.val := by
  obtain ⟨hσ, hpv, hreq, hpre⟩ := applies_of_ruleMatches hr hmem h
  intro hna
  cases hna σ (hσ.at _) hpv with
  | intro ht he hv => exact hv (EvalTerm.functional_of_fnDet hfd he (hreq _ ht))
  | pre hf =>
    exact absurd (holds_atoms_functional hfd (rule_atoms_of_execReady hr hmem).1 hpre hf) (by simp)

/-- **The converse of (U), with fuel**: a rule that applies to x (a well-sorted match under which
its `requires` evaluates to `true` and its `pre` holds) has, from some fuel on, a listed match with
value `some true`. Given `FnDet`. The applying is stated positively: `¬ NotApplies` does not give a
`requires` result, since a function's evaluation may have none (no termination is assumed). -/
theorem ruleMatches_of_applies (hr : execReady c = true) (hfd : FnDet c) {x : Config c}
    {r : Rule} (hmem : r ∈ c.rules) {σ : Subst} (hσ : c.WellSorted r.vars σ)
    (hpv : PatVal c σ r.lhs x.val) (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c r.vars.length σ r.pre true) :
    ∃ N, ∀ m, N ≤ m → ∃ σ₀, (σ₀, some true) ∈ ruleMatches c m r x.val := by
  obtain ⟨hok, hsc, hcc, hcm, hrc⟩ := execReady_parts hr
  have hnaF : c.AsideFree := asideFree_of_ready hr
  obtain ⟨hrq, -⟩ := ruleSorted_of hok hmem
  have hpc := (ruleSorted_preds_of hok hmem).1
  obtain ⟨σ₀, hσ₀m, hag⟩ := hrc r hmem x.val σ x.property (hσ.at _) hpv
  obtain ⟨np, hnp⟩ := predVal_exec hsc hcc hcm hfd hnaF hσ (rule_atoms_of_execReady hr hmem).1 hpc hpre
  obtain ⟨nq, hnq⟩ : ∃ nq, ∀ m, nq ≤ m → reqVal c m r σ₀ = some true := by
    cases hreqc : r.req with
    | none => exact ⟨0, fun m _ => by simp [reqVal, hreqc]⟩
    | some t =>
      rw [hreqc] at hrq
      have hts := reqOK_some hrq
      obtain ⟨n, hn⟩ := EvalTerm.exec hsc hcc hcm hfd hnaF (hreq t hreqc) r.vars _ Srt.bool Exec.headsOK_fns hσ hts
      refine ⟨n, fun m hm => ?_⟩
      have hq : CExec.evalT c m σ₀ t = some (some (bool true)) := by
        rw [evalT_congr m (fun i hi => hag i (sortOfTerm_vars hts i hi))]
        exact evalT_mono_le hsc hcc hcm hfd hm hn Exec.headsOK_fns hσ hts
      simp [reqVal, hreqc, hq, isTrue_iff]
  refine ⟨max np nq, fun m hm => ⟨σ₀, ruleMatches_mem.mpr ⟨hσ₀m, ?_⟩⟩⟩
  show some true = appVal (reqVal c m r σ₀) (predVal c m σ₀ r.pre)
  rw [hnq m (by omega), predVal_congr hag hpc, hnp m (by omega)]
  rfl

/-! ## The converse of (N) -/

/-- Where a rule does not apply, no listed match has `requires` `some true`, at any fuel. -/
theorem ruleMatches_ne_true (hr : execReady c = true) (hfd : FnDet c) {n : Nat}
    {x : Config c} {r : Rule} (hmem : r ∈ c.rules) (h : NotApplies c r x.val) :
    ∀ σb ∈ ruleMatches c n r x.val, σb.2 ≠ some true := by
  rintro ⟨σ, b⟩ hσb (hb : b = some true)
  subst hb
  exact not_notApplies_of_ruleMatches hr hfd hmem hσb h

/-- **The converse of (N), with fuel as in `step_iff`**: where no rule applies, from some fuel on
every listed match of every rule has the value `some false` (each failing `requires` result and
each false `pre` is computed with some fuel, `EvalTerm.exec`, `predVal_exec`, and kept with more,
`evalT_mono`, `predVal_mono_le`; `cmatch` lists finitely many matches and does not read the fuel).
Given `FnDet`. -/
theorem ruleMatches_of_noRule (hr : execReady c = true) (hfd : FnDet c) {x : Config c}
    (h : ∀ r ∈ c.rules, NotApplies c r x.val) :
    ∃ N, ∀ m, N ≤ m → ∀ r ∈ c.rules, ∀ σb ∈ ruleMatches c m r x.val, σb.2 = some false := by
  obtain ⟨hok, hsc, hcc, hcm, -⟩ := execReady_parts hr
  have hnaF : c.AsideFree := asideFree_of_ready hr
  let all := c.rules.flatMap fun r' => (cmatch c r'.vars [r'.lhs] [x.val]).map (r', ·)
  obtain ⟨N, hN⟩ := fuel_list
    (P := fun n (a : Rule × Subst) => a.1 ∈ c.rules ∧ c.WellSorted a.1.vars a.2 ∧
      ((∃ t v, a.1.req = some t ∧ CExec.evalT c n a.2 t = some v ∧ v ≠ some (bool true)) ∨
        predVal c n a.2 a.1.pre = some false))
    (fun n a ⟨har, haw, hor⟩ => by
      refine ⟨har, haw, ?_⟩
      rcases hor with ⟨t, v, ht, he, hv⟩ | hp
      · obtain ⟨hrq', -⟩ := ruleSorted_of hok har
        rw [ht] at hrq'
        exact Or.inl ⟨t, v, ht, evalT_mono hsc hcc hcm hfd n he Exec.headsOK_fns haw (reqOK_some hrq'), hv⟩
      · exact Or.inr (predVal_mono_le hsc hcc hcm hfd haw (Nat.le_succ n) (ruleSorted_preds_of hok har).1 hp))
    (l := all) (fun a ha => by
      obtain ⟨r', hr', ha⟩ := List.mem_flatMap.mp ha
      obtain ⟨σ', hσ', rfl⟩ := List.mem_map.mp ha
      obtain ⟨hσw, hpvs⟩ := cmatch_sound hσ'
      cases h r' hr' σ' (hσw.at _) (patVal_of_patVals hpvs) with
      | intro ht he hv =>
        obtain ⟨hrq', -⟩ := ruleSorted_of hok hr'
        rw [ht] at hrq'
        obtain ⟨n, hn⟩ := EvalTerm.exec hsc hcc hcm hfd hnaF he r'.vars _ Srt.bool Exec.headsOK_fns hσw
          (reqOK_some hrq')
        exact ⟨n, hr', hσw, Or.inl ⟨_, _, ht, hn, hv⟩⟩
      | pre hf =>
        obtain ⟨n, hn⟩ := predVal_exec hsc hcc hcm hfd hnaF hσw (rule_atoms_of_execReady hr hr').1
          (ruleSorted_preds_of hok hr').1 hf
        exact ⟨n, hr', hσw, Or.inr (hn n (Nat.le_refl _))⟩)
  refine ⟨N, fun m hm r' hr' σb hσb => ?_⟩
  obtain ⟨σ', b⟩ := σb
  obtain ⟨hσ', rfl⟩ := ruleMatches_mem.mp hσb
  have hmem : (r', σ') ∈ all :=
    List.mem_flatMap.mpr ⟨r', hr', List.mem_map.mpr ⟨σ', hσ', rfl⟩⟩
  show matchVal c m r' σ' = some false
  rcases (hN _ hmem m hm).2.2 with ⟨t, v, ht, he, hv⟩ | hp
  · refine appVal_false.mpr (Or.inl ?_)
    unfold reqVal
    rw [ht]
    simp only [he, Option.map_some, Option.some.injEq]
    cases hb : isTrue v
    · rfl
    · exact absurd (isTrue_iff.mp hb) hv
  · exact appVal_false.mpr (Or.inr hp)

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
    reqVal c n r σ ≠ none ∧ predVal c n σ r.pre ≠ none ∧
      (b = some true → (CExec.evalT c n σ r.rhs).isSome = true ∧ ensVal c n r σ ≠ none ∧
        predVal c n σ r.post ≠ none) := by
  unfold outOfFuel at hf
  have h1 := List.any_eq_false.mp hf r hmem
  rw [Bool.not_eq_true, List.any_eq_false] at h1
  have h2 := h1 (σ, b) hm
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, not_or, not_and] at h2
  obtain ⟨⟨hq, hp⟩, hrest⟩ := h2
  refine ⟨hq, hp, fun hb => ?_⟩
  obtain ⟨⟨hr1, hr2⟩, hr3⟩ := hrest hb
  refine ⟨?_, hr2, hr3⟩
  cases he : CExec.evalT c n σ r.rhs with
  | none => rw [he] at hr1; simp at hr1
  | some _ => rfl

/-- A listed match whose `requires` and `pre` have values, under which a rule applies (its
`requires` evaluates to `true` and its `pre` holds under a σ that agrees with the match on the
variables), has the value `some true`. Given `FnDet`. -/
theorem matchVal_true_of (hr : execReady c = true) (hfd : FnDet c) {n : Nat} {r : Rule}
    (hmem : r ∈ c.rules) {σ₀ σ : Subst} (hσ₀ : c.WellSorted r.vars σ₀)
    (hag : ∀ i < r.vars.length, σ₀.lookup i = σ.lookup i)
    (hqne : reqVal c n r σ₀ ≠ none) (hpne : predVal c n σ₀ r.pre ≠ none)
    (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c r.vars.length σ r.pre true) : matchVal c n r σ₀ = some true := by
  obtain ⟨hok, hsc, hcc, hcm, -⟩ := execReady_parts hr
  have hpc := (ruleSorted_preds_of hok hmem).1
  have hp : predVal c n σ₀ r.pre = some true := by
    cases hpv : predVal c n σ₀ r.pre with
    | none => exact absurd hpv hpne
    | some b =>
      rw [holds_atoms_functional hfd (rule_atoms_of_execReady hr hmem).1
        (predVal_sound hsc hcc hcm hσ₀ hag hpc hpv) hpre]
  have hq : reqVal c n r σ₀ = some true := by
    obtain ⟨hrq, -⟩ := ruleSorted_of hok hmem
    unfold reqVal at hqne ⊢
    cases hreqc : r.req with
    | none => rfl
    | some t =>
      rw [hreqc] at hqne hrq
      cases he : CExec.evalT c n σ₀ t with
      | none => simp [he] at hqne
      | some v =>
        have hts := reqOK_some hrq
        have hev := evalT_sound hsc hcc hcm n he Exec.headsOK_fns hσ₀ hts
        have hev' := EvalTerm.congr hev (fun i hi => hag i (sortOfTerm_vars hts i hi))
        have := EvalTerm.functional_of_fnDet hfd hev' (hreq t hreqc)
        subst this
        simp [he, isTrue_iff]
  show appVal (reqVal c n r σ₀) (predVal c n σ₀ r.pre) = some true
  rw [hq, hp]
  rfl

/-- A `post` with a value under a listed match, where the rule's `post` holds under a σ that
agrees with the match on the variables, has the value `some true`. Given `FnDet`. -/
theorem postVal_true_of (hr : execReady c = true) (hfd : FnDet c) {n : Nat} {r : Rule}
    (hmem : r ∈ c.rules) {σ₀ σ : Subst} (hσ₀ : c.WellSorted r.vars σ₀)
    (hag : ∀ i < r.vars.length, σ₀.lookup i = σ.lookup i) (hne : predVal c n σ₀ r.post ≠ none)
    (hpost : Holds c r.vars.length σ r.post true) : predVal c n σ₀ r.post = some true := by
  obtain ⟨hok, hsc, hcc, hcm, -⟩ := execReady_parts hr
  cases hpv : predVal c n σ₀ r.post with
  | none => exact absurd hpv hne
  | some b =>
    rw [holds_atoms_functional hfd (rule_atoms_of_execReady hr hmem).2.1
      (predVal_sound hsc hcc hcm hσ₀ hag (ruleSorted_preds_of hok hmem).2 hpv) hpost]

/-- **The step at one fuel is exact where nothing ran out of fuel**: if `outOfFuel c n x` is false,
the configurations `successorsN c n x` lists are exactly x's `Step` successors. Given `FnDet`
(a `requires`, a predicate and a right-hand side have one result). `step_iff` gives the same for
some fuel; this one is for the fuel the caller ran, with the condition it can check. -/
theorem step_iff_at (hr : execReady c = true) (hfd : FnDet c) {n : Nat} {x y : Config c}
    (hf : outOfFuel c n x.val = false) : Step c x y ↔ y.val ∈ successorsN c n x.val := by
  obtain ⟨hok, hsc, hcc, hcm, hrc⟩ := execReady_parts hr
  constructor
  · rintro ⟨r, hmem, σ, hσ, hmatch, hreq, hpre, heval, hens, hpost, hprio⟩
    obtain ⟨-, hrt⟩ := ruleSorted_of hok hmem
    have hen := ruleSorted_ens_of hok hmem
    obtain ⟨σ₀, hσ₀m, hag⟩ := hrc r hmem x.val σ x.property (hσ.at _) hmatch
    have hσ₀ := (cmatch_sound hσ₀m).1
    obtain ⟨hqne, hpne, -⟩ := of_outOfFuel_false hf hmem (ruleMatches_mem.mpr ⟨hσ₀m, rfl⟩)
    have hm₀ : (σ₀, some true) ∈ ruleMatches c n r x.val :=
      ruleMatches_mem.mpr ⟨hσ₀m, (matchVal_true_of hr hfd hmem hσ₀ hag hqne hpne hreq hpre).symm⟩
    obtain ⟨hrs, hensne, hpostne⟩ := (of_outOfFuel_false hf hmem hm₀).2.2 rfl
    have hrhs : CExec.evalT c n σ₀ r.rhs = some (some y.val) := by
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hrs
      have hev := evalT_sound hsc hcc hcm n ho Exec.headsOK_fns hσ₀ hrt
      have hev' := EvalTerm.congr hev (fun i hi => hag i (sortOfTerm_vars hrt i hi))
      rw [ho, EvalTerm.functional_of_fnDet hfd hev' heval]
    have hensV : ensVal c n r σ₀ = some true := by
      unfold ensVal at hensne ⊢
      cases hensc : r.ens with
      | none => rfl
      | some t =>
        rw [hensc] at hensne hen
        cases he : CExec.evalT c n σ₀ t with
        | none => simp [he] at hensne
        | some v =>
          have hts := reqOK_some hen
          have hev := evalT_sound hsc hcc hcm n he Exec.headsOK_fns hσ₀ hts
          have hev' := EvalTerm.congr hev (fun i hi => hag i (sortOfTerm_vars hts i hi))
          have := EvalTerm.functional_of_fnDet hfd hev' (hens t hensc)
          subst this
          simp [he, isTrue_iff]
    refine successorsN_of hmem (fun r' hr' hlt σb hσb => ?_) hm₀ hrhs y.property hensV
      (postVal_true_of hr hfd hmem hσ₀ hag hpostne hpost)
    obtain ⟨σ', b⟩ := σb
    obtain ⟨hσ'm, rfl⟩ := ruleMatches_mem.mp hσb
    obtain ⟨hqne', hpne', -⟩ := of_outOfFuel_false hf hr' hσb
    refine eq_false_of_ne (appVal_ne_none hqne' hpne') fun ht => ?_
    have hσb' : (σ', some true) ∈ ruleMatches c n r' x.val := ruleMatches_mem.mpr ⟨hσ'm, ht.symm⟩
    exact not_notApplies_of_ruleMatches hr hfd hr' hσb' (hprio r' hr' hlt)
  · intro hy
    obtain ⟨_, hst⟩ := successorsN_step_ready hr hy
    exact hst

/-- **A configuration where nothing ran out of fuel is `StepDecided`**: each match of a rule's
left-hand side agrees on the rule's variables with a listed match (`RuleComplete`), whose
`requires` and `pre` have values at fuel n, and, where both are `true`, whose right-hand side,
`ensures` and `post` have values (`outOfFuel c n x = false`); each value is an `EvalTerm` result
(`evalT_sound`) or a `Holds` value (`predVal_sound`). Given `FnDet`: a `requires` that evaluates to
`true` and a `pre` that holds under the match are the listed match's values (one result). -/
theorem stepDecided_of_fuel (hr : execReady c = true) (hfd : FnDet c) {n : Nat} {x : Config c}
    (hf : outOfFuel c n x.val = false) : StepDecided c x.val := by
  obtain ⟨hok, hsc, hcc, hcm, hrc⟩ := execReady_parts hr
  intro r hmem _
  have hpc := ruleSorted_preds_of hok hmem
  obtain ⟨hrq, hrt⟩ := ruleSorted_of hok hmem
  have hen := ruleSorted_ens_of hok hmem
  refine ⟨fun τ hτ hmatch => ?_, fun σ hσ hmatch hreq hpre => ?_⟩
  · obtain ⟨σ₀, hσ₀m, hag⟩ := hrc r hmem x.val τ x.property hτ hmatch
    have hσ₀ := (cmatch_sound hσ₀m).1
    obtain ⟨hqne, hpne, -⟩ := of_outOfFuel_false hf hmem (ruleMatches_mem.mpr ⟨hσ₀m, rfl⟩)
    refine ⟨fun t ht => ?_, ?_⟩
    · unfold reqVal at hqne
      rw [ht] at hqne hrq
      cases he : CExec.evalT c n σ₀ t with
      | none => simp [he] at hqne
      | some v =>
        have hts := reqOK_some hrq
        exact ⟨v, EvalTerm.congr (evalT_sound hsc hcc hcm n he Exec.headsOK_fns hσ₀ hts)
          (fun i hi => hag i (sortOfTerm_vars hts i hi))⟩
    · cases hpv : predVal c n σ₀ r.pre with
      | none => exact absurd hpv hpne
      | some b => exact ⟨b, predVal_sound hsc hcc hcm hσ₀ hag hpc.1 hpv⟩
  obtain ⟨σ₀, hσ₀m, hag⟩ := hrc r hmem x.val σ x.property (hσ.at _) hmatch
  have hσ₀ := (cmatch_sound hσ₀m).1
  obtain ⟨hqne, hpne, -⟩ := of_outOfFuel_false hf hmem (ruleMatches_mem.mpr ⟨hσ₀m, rfl⟩)
  have hm₀ : (σ₀, some true) ∈ ruleMatches c n r x.val :=
    ruleMatches_mem.mpr ⟨hσ₀m, (matchVal_true_of hr hfd hmem hσ₀ hag hqne hpne hreq hpre).symm⟩
  obtain ⟨hrhs, hens, hpostne⟩ := (of_outOfFuel_false hf hmem hm₀).2.2 rfl
  refine ⟨?_, fun t ht => ?_, ?_⟩
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
  · cases hpv : predVal c n σ₀ r.post with
    | none => exact absurd hpv hpostne
    | some b => exact ⟨b, predVal_sound hsc hcc hcm hσ₀ hag hpc.2 hpv⟩

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
