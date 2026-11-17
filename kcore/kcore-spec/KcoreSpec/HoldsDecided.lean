/-
  KCore. A well-sorted condition has a truth value, and the evaluations a step reads have results,
  for rules with any predicates.

  - `holds_decided`: a condition with `condOK` has a truth value (`∃ b, Holds … p b`) at every σ that
    gives its free variables (`varOccsCond`) values of their sorts, where every function has a result
    at arguments of its sorts (`HypSoundCore`, `FnTerminates`). A binder's truth value is read by
    classical choice of the truth value of its body at each extension of σ; no list of a sort's
    values is read.
  - `Rule.decided_pp`, `stepDecided_pp`: `Rule.decided_of_total` and `stepDecided_of_rules` for a
    well-sorted rule with any `pre` and `post`, without `rulePlainOpen`: every configuration is
    `StepDecided` where every rule is well sorted.
-/
import KcoreSpec.OpenStep

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML

section
variable {c : Semantics}

/-- An extension of a σ that gives the listed variables values gives the variables of a body under
the binder values: those below n by σ, the bound ones by the extension. -/
theorem extends_wellSortedAt_hd {n : Nat} {vars ys : List Srt} {σ σ' : Subst} {is js : List Nat}
    (hn : n = vars.length) (he : Extends c n ys σ σ') (hσ : c.WellSortedAt vars is σ)
    (hjs : ∀ i ∈ js, i < n → i ∈ is) : c.WellSortedAt (vars ++ ys) js σ' := by
  intro i hi s hs
  by_cases hlt : i < n
  · rw [List.getElem?_append_left (hn ▸ hlt)] at hs
    obtain ⟨v, hv, hvs⟩ := hσ i (hjs i hi hlt) s hs
    exact ⟨v, by rw [he.1 i hlt]; exact hv, hvs⟩
  · have hge : vars.length ≤ i := hn ▸ Nat.le_of_not_lt hlt
    rw [List.getElem?_append_right hge] at hs
    obtain ⟨v, hv, hvs⟩ := he.2 (i - vars.length) s hs
    refine ⟨v, ?_, hvs⟩
    have : n + (i - vars.length) = i := by omega
    rw [this] at hv; exact hv

open Classical in
/-- **A well-sorted condition has a truth value** at every σ that gives its free variables values
of their sorts, where every function has a result at arguments of its sorts. -/
theorem holds_decided (h : HypSoundCore c) (hft : FnTerminates c) :
    ∀ (p : Cond) {vars : List Srt} {σ : Subst}, c.condOK vars p = true →
      c.WellSortedAt vars (varOccsCond vars.length p) σ → ∃ b, Holds c vars.length σ p b
  | .top, _, _, _, _ => ⟨true, .top⟩
  | .bot, _, _, _, _ => ⟨false, .bot⟩
  | .not p, vars, σ, hok, hσ => by
    rw [Semantics.condOK] at hok
    rw [varOccsCond] at hσ
    obtain ⟨b, hb⟩ := holds_decided h hft p hok hσ
    exact ⟨!b, .not hb⟩
  | .and p q, vars, σ, hok, hσ => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    rw [varOccsCond] at hσ
    obtain ⟨b, hb⟩ := holds_decided h hft p hok.1 (hσ.mono fun i hi => List.mem_append_left _ hi)
    obtain ⟨b', hb'⟩ := holds_decided h hft q hok.2 (hσ.mono fun i hi => List.mem_append_right _ hi)
    exact ⟨b && b', .and hb hb'⟩
  | .or p q, vars, σ, hok, hσ => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    rw [varOccsCond] at hσ
    obtain ⟨b, hb⟩ := holds_decided h hft p hok.1 (hσ.mono fun i hi => List.mem_append_left _ hi)
    obtain ⟨b', hb'⟩ := holds_decided h hft q hok.2 (hσ.mono fun i hi => List.mem_append_right _ hi)
    exact ⟨b || b', .or hb hb'⟩
  | .implies p q, vars, σ, hok, hσ => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    rw [varOccsCond] at hσ
    obtain ⟨b, hb⟩ := holds_decided h hft p hok.1 (hσ.mono fun i hi => List.mem_append_left _ hi)
    obtain ⟨b', hb'⟩ := holds_decided h hft q hok.2 (hσ.mono fun i hi => List.mem_append_right _ hi)
    exact ⟨!b || b', .implies hb hb'⟩
  | .ceil s t, vars, σ, hok, hσ => by
    rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1; rw [beq_iff_eq] at hok
    rw [varOccsCond] at hσ
    obtain ⟨r, hr⟩ := evalTerm_total_at h hft fns_headsOK hσ hok
    exact ⟨r.isSome, .ceil hr⟩
  | .equals s t u, vars, σ, hok, hσ => by
    rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1; rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
    rw [varOccsCond] at hσ
    obtain ⟨r, hr⟩ := evalTerm_total_at h hft fns_headsOK (hσ.mono fun i hi => List.mem_append_left _ hi) hok.1
    obtain ⟨r', hr'⟩ := evalTerm_total_at h hft fns_headsOK (hσ.mono fun i hi => List.mem_append_right _ hi) hok.2
    exact ⟨sameResult r r', .equals hr hr'⟩
  | .mem s t u, vars, σ, hok, hσ => by
    rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1; rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
    rw [varOccsCond] at hσ
    obtain ⟨r, hr⟩ := evalTerm_total_at h hft fns_headsOK (hσ.mono fun i hi => List.mem_append_left _ hi) hok.1
    obtain ⟨r', hr'⟩ := evalTerm_total_at h hft fns_headsOK (hσ.mono fun i hi => List.mem_append_right _ hi) hok.2
    exact ⟨r.isSome && sameResult r r', .mem hr hr'⟩
  | .exMatch ys s p t body, vars, σ, hok, hσ => by
    rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1; rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
    rw [varOccsCond] at hσ
    obtain ⟨r, hr⟩ := evalTerm_total_at h hft fns_headsOK (hσ.mono fun i hi => List.mem_append_left _ hi) hok.1.2
    cases r with
    | none => exact ⟨false, .exNone hr⟩
    | some v =>
      let g : Subst → Bool := fun σ' => decide (Holds c (vars.length + ys.length) σ' body true)
      have hb : ∀ σ', Extends c vars.length ys σ σ' → PatVal c σ' p v →
          Holds c (vars.length + ys.length) σ' body (g σ') := by
        intro σ' he _
        have hσ' : c.WellSortedAt (vars ++ ys) (varOccsCond (vars ++ ys).length body) σ' :=
          extends_wellSortedAt_hd rfl he hσ fun i hi hlt => List.mem_append_right _ (List.mem_filter.mpr
            ⟨List.mem_append_right _ (by rw [List.length_append] at hi; exact hi), by simpa using hlt⟩)
        obtain ⟨b, hb⟩ := holds_decided h hft body hok.2 hσ'
        rw [List.length_append] at hb
        by_cases hT : Holds c (vars.length + ys.length) σ' body true
        · have : g σ' = true := decide_eq_true hT
          rw [this]; exact hT
        · have : g σ' = false := decide_eq_false hT
          rw [this]
          cases b with
          | true => exact absurd hb hT
          | false => exact hb
      exact ⟨decide (∃ σ', Extends c vars.length ys σ σ' ∧ PatVal c σ' p v ∧ g σ' = true),
        .exSome g hr hb decide_eq_true_iff⟩
  | .ex s body, vars, σ, hok, hσ => by
    rw [Semantics.condOK] at hok
    rw [varOccsCond] at hσ
    let g : Subst → Bool := fun σ' => decide (Holds c (vars.length + 1) σ' body true)
    have hb : ∀ σ', Extends c vars.length [s] σ σ' → Holds c (vars.length + 1) σ' body (g σ') := by
      intro σ' he
      have hσ' : c.WellSortedAt (vars ++ [s]) (varOccsCond (vars ++ [s]).length body) σ' :=
        extends_wellSortedAt_hd rfl he hσ fun i hi hlt => List.mem_filter.mpr
          ⟨by rw [List.length_append] at hi; exact hi, by simpa using hlt⟩
      obtain ⟨b, hb⟩ := holds_decided h hft body hok hσ'
      rw [List.length_append] at hb
      by_cases hT : Holds c (vars.length + 1) σ' body true
      · have : g σ' = true := decide_eq_true hT
        rw [this]; exact hT
      · have : g σ' = false := decide_eq_false hT
        rw [this]
        cases b with
        | true => exact absurd hb hT
        | false => exact hb
    exact ⟨decide (∃ σ', Extends c vars.length [s] σ σ' ∧ g σ' = true), .ex g hb decide_eq_true_iff⟩
  | .all s body, vars, σ, hok, hσ => by
    rw [Semantics.condOK] at hok
    rw [varOccsCond] at hσ
    let g : Subst → Bool := fun σ' => decide (Holds c (vars.length + 1) σ' body true)
    have hb : ∀ σ', Extends c vars.length [s] σ σ' → Holds c (vars.length + 1) σ' body (g σ') := by
      intro σ' he
      have hσ' : c.WellSortedAt (vars ++ [s]) (varOccsCond (vars ++ [s]).length body) σ' :=
        extends_wellSortedAt_hd rfl he hσ fun i hi hlt => List.mem_filter.mpr
          ⟨by rw [List.length_append] at hi; exact hi, by simpa using hlt⟩
      obtain ⟨b, hb⟩ := holds_decided h hft body hok hσ'
      rw [List.length_append] at hb
      by_cases hT : Holds c (vars.length + 1) σ' body true
      · have : g σ' = true := decide_eq_true hT
        rw [this]; exact hT
      · have : g σ' = false := decide_eq_false hT
        rw [this]
        cases b with
        | true => exact absurd hb hT
        | false => exact hb
    exact ⟨decide (∀ σ', Extends c vars.length [s] σ σ' → g σ' = true), .all g hb decide_eq_true_iff⟩

/-- A well-sorted condition is true or false at such a σ. -/
theorem holds_true_or_false (h : HypSoundCore c) (hft : FnTerminates c) (p : Cond) {vars : List Srt}
    {σ : Subst} (hok : c.condOK vars p = true) (hσ : c.WellSortedAt vars (varOccsCond vars.length p) σ) :
    Holds c vars.length σ p true ∨ Holds c vars.length σ p false := by
  obtain ⟨b, hb⟩ := holds_decided h hft p hok hσ
  cases b with
  | true => exact .inl hb
  | false => exact .inr hb

/-- **The evaluations a step by a rule reads have results**, for a well-sorted rule with any
predicates: `Rule.decided_of_total` without `rulePlainOpen`. -/
theorem Rule.decided_pp (h : HypSoundCore c) (hft : FnTerminates c) {r : Rule}
    (hs : c.ruleSorted r = true) (x : GroundTerm) :
    (∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x →
      (∀ t, r.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c r.vars.length σ r.pre b) ∧
    (∀ σ, c.WellSorted r.vars σ → PatVal c σ r.lhs x →
      (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) → Holds c r.vars.length σ r.pre true →
        (∃ v, EvalTerm c σ r.rhs v) ∧ (∀ e, r.ens = some e → ∃ w, EvalTerm c σ e w) ∧
        ∃ b, Holds c r.vars.length σ r.post b) := by
  obtain ⟨-, hreq, hens, hrhs⟩ := Semantics.ruleSorted_parts c hs
  have hs' := hs
  simp only [Semantics.ruleSorted, Bool.and_eq_true] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hpre⟩, -⟩, hpost⟩, -⟩, -⟩, -⟩ := hs'
  have hreqs : ∀ t, r.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool :=
    fun t ht => by rw [ht] at hreq; simpa [reqOK] using hreq
  have hensS : ∀ t, r.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool :=
    fun t ht => by rw [ht] at hens; simpa [reqOK] using hens
  refine ⟨fun σ hσ _ => ⟨fun t ht => evalTerm_total_at h hft fns_headsOK
      (hσ.mono (Rule.req_leftVars ht)) (hreqs t ht),
      holds_decided h hft r.pre hpre (hσ.mono fun i hi =>
        List.mem_append_right _ (List.mem_append_right _ hi))⟩,
    fun σ hσ _ _ _ => ⟨Model.evalTerm_total h hft fns_headsOK hσ hrhs,
      fun e he => Model.evalTerm_total h hft fns_headsOK hσ (hensS e he),
      holds_decided h hft r.post hpost (hσ.at _)⟩⟩

/-- Every configuration is `StepDecided` where every function has a result at arguments of its
sorts and every rule is well sorted: `stepDecided_of_rules` without `rulePlainOpen`. -/
theorem stepDecided_pp (h : HypSoundCore c) (hft : FnTerminates c)
    (hr : ∀ r ∈ c.rules, c.ruleSorted r = true) (x : GroundTerm) : StepDecided c x :=
  fun r hmem _ => Rule.decided_pp h hft (hr r hmem) x

end

end Faithful

open Faithful

/-- Every configuration of a semantics that `coreOK` accepts and whose functions meet `FnHyp` is
`StepDecided`: `stepDecided_pp` with the rules' `ruleSorted`, which `coreOK` gives. -/
theorem stepDecided_of_fnHyp {c : Semantics} (h : c.coreOK = true) (hf : FnHyp c) (x : Config c) :
    StepDecided c x.val :=
  stepDecided_pp (hypSound_of_core h) hf.1
    (fun r hr => List.all_eq_true.mp (by
      have hs := Semantics.sortedOK_sorted (Semantics.coreOK_parts h).1
      simp only [Bool.and_eq_true] at hs
      exact hs.2) r hr) x.val

end KCore
