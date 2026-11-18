/-
  KCore. `FnHyp` gives `FnDet` and `FnSolves`, a well-sorted condition has a truth value, and the
  evaluations a step reads have results, for a semantics `coreOKEx` accepts: its clauses may bind
  variables by `\exists`.

  - `holds_decidedCl`: `holds_decided` from `SortCtx` and `OvlOK`. What the proof reads of the
    semantics is that a well-sorted term has a result (`evalTerm_total_atCl`), which reads the sort
    context and no condition on the shape of the clauses. `holds_decidedCEx` is its instance at
    `HypSoundCoreEx`.
  - `prioDecided_of_totalCEx`, `instRes_of_totalCEx`, `fnSolves_of_totalCEx`: the inputs of
    `fnSolves_of_res`. A clause without existential variables has a result where it decides by the
    termination of the functions, its right-side predicate being `\top` (`sortedOKEx_post_of_nil`);
    a clause with existential variables has one by hypothesis.
  - `fnModel_of_fnHypCEx`: `FnDet` is `fnDet_of_agree`, and the result of a clause with existential
    variables where it decides is `MatchIndependent`'s second conjunct.
  - `clausePreDecided_of_fnHypCEx`, `clausePostDecided_of_fnHypCEx`: each clause's two predicates
    have truth values, both being well sorted (`clauseSorted`, `clauseExOK`).
  - `Rule.decided_ppCEx`, `stepDecided_ppCEx`, `stepDecided_of_fnHypCEx`: every configuration is
    `StepDecided`.
-/
import KcoreSpec.ClauseExDenCEx
import KcoreSpec.OpenClauseModel
import KcoreSpec.ModelFnsExGoal
import KcoreSpec.HoldsDecided
import KcoreSpec.HypWf

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML

section
variable {c : Semantics}

open Model in
open Classical in
/-- **A well-sorted condition has a truth value** at every σ that gives its free variables values
of their sorts, where every function has a result at arguments of its sorts: `holds_decided` from
the sort context. -/
theorem holds_decidedCl (hsc : SortCtx c) (hov : OvlOK c) (hft : FnTerminates c) :
    ∀ (p : Cond) {vars : List Srt} {σ : Subst}, c.condOK vars p = true →
      c.WellSortedAt vars (varOccsCond vars.length p) σ → ∃ b, Holds c vars.length σ p b
  | .top, _, _, _, _ => ⟨true, .top⟩
  | .bot, _, _, _, _ => ⟨false, .bot⟩
  | .not p, vars, σ, hok, hσ => by
    rw [Semantics.condOK] at hok
    rw [varOccsCond] at hσ
    obtain ⟨b, hb⟩ := holds_decidedCl hsc hov hft p hok hσ
    exact ⟨!b, .not hb⟩
  | .and p q, vars, σ, hok, hσ => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    rw [varOccsCond] at hσ
    obtain ⟨b, hb⟩ := holds_decidedCl hsc hov hft p hok.1 (hσ.mono fun i hi => List.mem_append_left _ hi)
    obtain ⟨b', hb'⟩ := holds_decidedCl hsc hov hft q hok.2 (hσ.mono fun i hi => List.mem_append_right _ hi)
    exact ⟨b && b', .and hb hb'⟩
  | .or p q, vars, σ, hok, hσ => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    rw [varOccsCond] at hσ
    obtain ⟨b, hb⟩ := holds_decidedCl hsc hov hft p hok.1 (hσ.mono fun i hi => List.mem_append_left _ hi)
    obtain ⟨b', hb'⟩ := holds_decidedCl hsc hov hft q hok.2 (hσ.mono fun i hi => List.mem_append_right _ hi)
    exact ⟨b || b', .or hb hb'⟩
  | .implies p q, vars, σ, hok, hσ => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    rw [varOccsCond] at hσ
    obtain ⟨b, hb⟩ := holds_decidedCl hsc hov hft p hok.1 (hσ.mono fun i hi => List.mem_append_left _ hi)
    obtain ⟨b', hb'⟩ := holds_decidedCl hsc hov hft q hok.2 (hσ.mono fun i hi => List.mem_append_right _ hi)
    exact ⟨!b || b', .implies hb hb'⟩
  | .ceil s t, vars, σ, hok, hσ => by
    rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1; rw [beq_iff_eq] at hok
    rw [varOccsCond] at hσ
    obtain ⟨r, hr⟩ := evalTerm_total_atCl hsc hov hft fns_headsOK hσ (fun _ hi => hi) hok
    exact ⟨r.isSome, .ceil hr⟩
  | .equals s t u, vars, σ, hok, hσ => by
    rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1; rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
    rw [varOccsCond] at hσ
    obtain ⟨r, hr⟩ := evalTerm_total_atCl hsc hov hft fns_headsOK hσ (fun i hi => List.mem_append_left _ hi) hok.1
    obtain ⟨r', hr'⟩ := evalTerm_total_atCl hsc hov hft fns_headsOK hσ (fun i hi => List.mem_append_right _ hi) hok.2
    exact ⟨sameResult r r', .equals hr hr'⟩
  | .mem s t u, vars, σ, hok, hσ => by
    rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1; rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
    rw [varOccsCond] at hσ
    obtain ⟨r, hr⟩ := evalTerm_total_atCl hsc hov hft fns_headsOK hσ (fun i hi => List.mem_append_left _ hi) hok.1
    obtain ⟨r', hr'⟩ := evalTerm_total_atCl hsc hov hft fns_headsOK hσ (fun i hi => List.mem_append_right _ hi) hok.2
    exact ⟨r.isSome && sameResult r r', .mem hr hr'⟩
  | .exMatch ys s p t body, vars, σ, hok, hσ => by
    rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1; rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
    rw [varOccsCond] at hσ
    obtain ⟨r, hr⟩ := evalTerm_total_atCl hsc hov hft fns_headsOK hσ (fun i hi => List.mem_append_left _ hi) hok.1.2
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
        obtain ⟨b, hb⟩ := holds_decidedCl hsc hov hft body hok.2 hσ'
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
      obtain ⟨b, hb⟩ := holds_decidedCl hsc hov hft body hok hσ'
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
      obtain ⟨b, hb⟩ := holds_decidedCl hsc hov hft body hok hσ'
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

/-- The sort context of a semantics with `HypSoundCoreEx`. -/
theorem HypSoundCoreEx.sortCtx (hs : HypSoundCoreEx c) : SortCtx c :=
  sortCtx_of_allCEx hs.1 hs.2.1 (OvlOK.ovlCase hs.2.2.2.2.2.2.2.2)

/-- `holds_decided` for a semantics with `HypSoundCoreEx`. -/
theorem holds_decidedCEx (hs : HypSoundCoreEx c) (hft : FnTerminates c) (p : Cond) {vars : List Srt}
    {σ : Subst} (hok : c.condOK vars p = true) (hσ : c.WellSortedAt vars (varOccsCond vars.length p) σ) :
    ∃ b, Holds c vars.length σ p b :=
  holds_decidedCl hs.sortCtx hs.2.2.2.2.2.2.2.2 hft p hok hσ

/-- **The evaluations a step by a rule reads have results**, for a well-sorted rule with any
predicates: `Rule.decided_pp` for a semantics with `HypSoundCoreEx`. -/
theorem Rule.decided_ppCEx (h : HypSoundCoreEx c) (hft : FnTerminates c) {r : Rule}
    (hs : c.ruleSorted r = true) (x : GroundTerm) :
    (∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x →
      (∀ t, r.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c r.vars.length σ r.pre b) ∧
    (∀ σ, c.WellSorted r.vars σ → PatVal c σ r.lhs x →
      (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) → Holds c r.vars.length σ r.pre true →
        (∃ v, EvalTerm c σ r.rhs v) ∧ (∀ e, r.ens = some e → ∃ w, EvalTerm c σ e w) ∧
        ∃ b, Holds c r.vars.length σ r.post b) := by
  have hsc := h.sortCtx
  have hov : OvlOK c := h.2.2.2.2.2.2.2.2
  obtain ⟨-, hreq, hens, hrhs⟩ := Semantics.ruleSorted_parts c hs
  have hs' := hs
  simp only [Semantics.ruleSorted, Bool.and_eq_true] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hpre⟩, -⟩, hpost⟩, -⟩, -⟩, -⟩ := hs'
  have hreqs : ∀ t, r.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool :=
    fun t ht => by rw [ht] at hreq; simpa [reqOK] using hreq
  have hensS : ∀ t, r.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool :=
    fun t ht => by rw [ht] at hens; simpa [reqOK] using hens
  refine ⟨fun σ hσ _ => ⟨fun t ht => evalTerm_total_atCl hsc hov hft fns_headsOK hσ
      (Rule.req_leftVars ht) (hreqs t ht),
      holds_decidedCl hsc hov hft r.pre hpre (hσ.mono fun i hi =>
        List.mem_append_right _ (List.mem_append_right _ hi))⟩,
    fun σ hσ _ _ _ => ⟨Model.evalTerm_totalCl hsc hov hft fns_headsOK hσ hrhs,
      fun e he => Model.evalTerm_totalCl hsc hov hft fns_headsOK hσ (hensS e he),
      holds_decidedCl hsc hov hft r.post hpost (hσ.at _)⟩⟩

end

namespace Model

variable {c : Semantics}

/-- A function of the semantics is the one `lookupFn` finds under its label
(`lookupFn_of_sound`), for a semantics with `HypSoundCoreEx`. -/
theorem lookupFn_of_soundCEx (hs : HypSoundCoreEx c) {fn : Fn} (hfn : fn ∈ c.allFns) :
    c.lookupFn fn.label = some fn := by
  rw [Semantics.lookupFn_eq]
  exact find?_label hs.sortCtx.nodupFns hfn

/-- **`PrioDecided` where every function has a result** at arguments of its sorts
(`prioDecided_of_total`), for a semantics with `HypSoundCoreEx`: each `requires` of a clause has a
result at each match well sorted on its patterns and conditions, and the clause's predicate, well
sorted, a truth value there. -/
theorem prioDecided_of_totalCEx (hs : HypSoundCoreEx c) (ht : FnTerminates c) : PrioDecided c := by
  intro fn hfn vs cl σ _ _ cl' hcl' _ _ σ' hσ' _
  refine ⟨fun t hq => ?_,
    holds_decidedCEx hs ht cl'.pre (Semantics.sortedOKEx_clausePre hs.1 hfn hcl').1 (hσ'.mono Clause.pre_leftVarsRH)⟩
  obtain ⟨-, -, L, hL, hreqs, -⟩ := clause_ctxOccECEx hs.1 (List.mem_append_left _ hfn) hcl'
  exact evalTerm_total_atCl hs.sortCtx hs.2.2.2.2.2.2.2.2 ht hL hσ' (Clause.req_leftVarsRH hq) (hreqs t hq)

/-- **Each clause instance has a result under each well-sorted substitution** where every function
has a result at arguments of its sorts (`instRes_of_total`), for a semantics with
`HypSoundCoreEx`: its `ensures` has one, and where that is `true`, its right-hand side. -/
theorem instRes_of_totalCEx (hs : HypSoundCoreEx c) (ht : FnTerminates c) {fn : Fn} (hfn : fn ∈ c.fns)
    {cl' : Clause} (hcl' : cl' ∈ fn.clauses) {σ' : Subst} (hσ' : c.WellSorted cl'.vars σ') :
    ∃ r, cl'.InstRes c σ' r := by
  have hsc := hs.sortCtx
  have hov : OvlOK c := hs.2.2.2.2.2.2.2.2
  obtain ⟨-, -, L, hL, -, hrhs, hens⟩ := clause_ctxOccECEx hs.1 (List.mem_append_left _ hfn) hcl'
  obtain ⟨r, hr⟩ := evalTerm_totalCl hsc hov ht hL hσ' hrhs
  cases he : cl'.ens with
  | none => exact ⟨r, .inl ⟨fun t ht => (by rw [he] at ht; cases ht), hr⟩⟩
  | some t =>
    obtain ⟨w, hw⟩ := evalTerm_totalCl hsc hov ht hL hσ' (hens t he)
    by_cases hb : w = some (bool true)
    · subst hb
      exact ⟨r, .inl ⟨fun t' ht' => (by rw [he] at ht'; cases ht'; exact hw), hr⟩⟩
    · exact ⟨none, .inr ⟨t, w, he, hw, hb, rfl⟩⟩

/-- **Evaluation solves the equations** (`fnSolves_of_total`), for a semantics with
`HypSoundCoreEx`, where every function has at most one result and a result at arguments of its
sorts, and each clause with existential variables has a result (`Clause.Res`) at each match under
which it decides (`hex`). A clause without existential variables has one by the termination, its
right side's predicate being `\top`. -/
theorem fnSolves_of_totalCEx (hs : HypSoundCoreEx c) (hd : FnDet c) (ht : FnTerminates c)
    (hex : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.exs ≠ [] → ∀ vs σ, cl.Decides c fn σ vs → ∃ r, cl.Res c σ r) :
    FnSolves c :=
  fnSolves_of_res (fun _ hfn => lookupFn_of_soundCEx hs (List.mem_append_left _ hfn)) hd
    (prioDecided_of_totalCEx hs ht) fun fn hfn cl hcl vs _ σ hdec => by
      by_cases hx : cl.exs = []
      · obtain ⟨r, hr⟩ := instRes_of_totalCEx hs ht hfn hcl ((wellSortedAt_univ hx).mp hdec.1.1)
        exact ⟨r, Clause.res_of_instRes hx (Semantics.sortedOKEx_post_of_nil hs.1 hfn hcl hx) hr⟩
      · exact hex fn hfn cl hcl hx vs σ hdec

/-- Each clause's right-side predicate, in a semantics `sortedOKEx` accepts, is well sorted over
the clause's variables (`clauseExOK`). -/
theorem _root_.KCore.Semantics.sortedOKEx_postOK (h : c.sortedOKEx = true) :
    ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, c.condOK cl.vars cl.post = true := by
  intro fn hfn cl hcl
  have := (Semantics.clausesPlainEx_spec (Semantics.sortedOKEx_parts h).2.2.2.2.1 hfn hcl).2.1
  simp only [Semantics.clauseExOK, Bool.and_eq_true] at this
  exact this.2

/-- **`ClausePreDecided` where every function has a result** at arguments of its sorts
(`clausePreDecided_of_terminates`), for a semantics with `HypSoundCoreEx`. -/
theorem clausePreDecided_of_totalCEx (hs : HypSoundCoreEx c) (ht : FnTerminates c) : ClausePreDecided c :=
  fun _ hfn cl hcl _ _ hσ _ =>
    holds_decidedCEx hs ht cl.pre (Semantics.sortedOKEx_clausePre hs.1 hfn hcl).1 (hσ.mono Clause.pre_leftVarsRH)

/-- **`ClausePostDecided` where every function has a result** at arguments of its sorts
(`clausePostDecided_of_total`), for a semantics with `HypSoundCoreEx`: each clause's right-side
predicate is well sorted over the clause's variables. -/
theorem clausePostDecided_of_totalCEx (hs : HypSoundCoreEx c) (ht : FnTerminates c) : ClausePostDecided c :=
  fun fn hfn cl hcl _ hσ =>
    holds_decidedCEx hs ht cl.post (Semantics.sortedOKEx_postOK hs.1 fn hfn cl hcl) (hσ.at _)

end Model

end Faithful

open Faithful Faithful.Model

variable {c : Semantics}

/-- **`FnHyp` gives `FnDet` and `FnSolves`**, for a semantics `coreOKEx` accepts: the agreement of
the equations and the match independence of the clauses give one result (`fnDet_of_agree`); with
termination every `requires` and right-hand side read has a result, and match independence holds a
result of each clause with existential variables where it decides. `FnHyp`'s totality conjunct and
its two last are not read. -/
theorem fnModel_of_fnHypCEx (h : c.coreOKEx = true) (hf : FnHyp c) : FnDet c ∧ FnSolves c :=
  have hs := hypSoundEx_of_coreEx h
  have hd := fnDet_of_agree hf.2.2.1 hf.2.2.2.1
  ⟨hd, fnSolves_of_totalCEx hs hd hf.1 fun fn hfn cl hcl hne vs σ hdec =>
    (hf.2.2.2.1 fn hfn cl hcl).2 hne fn.label fn vs σ
      (lookupFn_of_soundCEx hs (List.mem_append_left _ hfn)) hcl hdec⟩

/-- **`ClausePreDecided` under `FnHyp`**, for a semantics `coreOKEx` accepts. -/
theorem clausePreDecided_of_fnHypCEx (h : c.coreOKEx = true) (hf : FnHyp c) : ClausePreDecided c :=
  clausePreDecided_of_totalCEx (hypSoundEx_of_coreEx h) hf.1

/-- **`ClausePostDecided` under `FnHyp`**, for a semantics `coreOKEx` accepts. -/
theorem clausePostDecided_of_fnHypCEx (h : c.coreOKEx = true) (hf : FnHyp c) : ClausePostDecided c :=
  clausePostDecided_of_totalCEx (hypSoundEx_of_coreEx h) hf.1

/-- Every configuration is `StepDecided` where every function has a result at arguments of its
sorts and every rule is well sorted: `stepDecided_pp` for a semantics with `HypSoundCoreEx`. -/
theorem stepDecided_ppCEx (h : HypSoundCoreEx c) (hft : FnTerminates c)
    (hr : ∀ r ∈ c.rules, c.ruleSorted r = true) (x : GroundTerm) : StepDecided c x :=
  fun r hmem _ => Rule.decided_ppCEx h hft (hr r hmem) x

/-- Every configuration of a semantics that `coreOKEx` accepts and whose functions meet `FnHyp` is
`StepDecided`. -/
theorem stepDecided_of_fnHypCEx (h : c.coreOKEx = true) (hf : FnHyp c) (x : Config c) :
    StepDecided c x.val :=
  stepDecided_ppCEx (hypSoundEx_of_coreEx h) hf.1
    (fun r hr => List.all_eq_true.mp (Semantics.sortedOKEx_parts (Semantics.coreOKEx_parts h).1).2.2.1 r hr) x.val

end KCore
