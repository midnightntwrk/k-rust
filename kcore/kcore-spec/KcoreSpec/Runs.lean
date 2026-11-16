/-
  Runs of a definition's step relation, and the means to prove one step at a time.

  - `StepsTo c u v`: every configuration whose term is `u` has a step to a configuration whose term
    is `v`; `Runs c u v`: the same with a finite sequence of steps (`Star`). Stated on terms, so a
    run is written with the terms of its configurations, and subject reduction supplies that each
    term met is a configuration.
  - `stepsTo_of_rule`: one step by a rule whose left-hand side is a constructor pattern, from a
    substitution written as the list of its variables' values (`sub`): the values have the rule's
    sorts (`SortsAre`), the left-hand side's instance is `u` and its aliases hold (`Term.aliasCheck`),
    the `requires` evaluates to `true` and the right-hand side to `v` in the executable evaluation.
    Each of these is an equation the kernel decides by evaluation (`kernel_defeq`), also when the
    terms hold variables the evaluation does not inspect (an Int under a constructor, the rest of a
    cell).
  - `allPath_of_runs`: in a deterministic relation, a run from x to z puts z on every complete path
    from x, so a one-path run is an all-path claim (`Reachability.AllPath`).
-/
import KcoreSpec.SymbolicLemmas
import KcoreSpec.StepIff
import KcoreSpec.Reachability

set_option autoImplicit false

open Lean Elab Tactic Meta in
/-- `kernel_defeq`: close an equation `a = b` by `Eq.refl a`, checked by the kernel's definitional
equality alone, after abstracting the local variables the goal mentions (each of a closed type):
the kernel checks `∀ xs, a = b` by `fun xs => Eq.refl a`. As `kernel_rfl`, but the goal may hold
variables, which the evaluation must leave in place. -/
elab "kernel_defeq" : tactic => liftMetaFinishingTactic fun g => do
  let t ← instantiateMVars (← g.getType)
  if t.hasMVar then throwError "kernel_defeq: the goal has metavariables"
  let fvs := (collectFVars {} t).fvarIds
  let xs := fvs.map mkFVar
  let t' ← mkForallFVars xs t
  if t'.hasFVar then throwError "kernel_defeq: a variable of the goal has a type with variables"
  let pf ← forallTelescope t' fun ys body => do
    let some (α, a, _) := body.eq? | throwError "kernel_defeq: the goal is not an equation"
    let u ← getLevel α
    mkLambdaFVars ys (mkApp2 (mkConst ``Eq.refl [u]) α a)
  let lvls := (collectLevelParams {} t').params.toList
  let name ← mkAuxLemma lvls t' pf
  g.assign (mkAppN (mkConst name (lvls.map mkLevelParam)) xs)

namespace KCore

/-! ## Paths of a relation -/

/-- `Star r x y`: a finite sequence of `r` steps leads from x to y. -/
inductive Star {α : Type} (r : α → α → Prop) : α → α → Prop where
  | refl {x : α} : Star r x x
  | cons {x y z : α} (h : r x y) (t : Star r y z) : Star r x z

theorem Star.trans {α : Type} {r : α → α → Prop} {x y z : α} (h : Star r x y) (h' : Star r y z) :
    Star r x z := by
  induction h with
  | refl => exact h'
  | cons hs _ ih => exact .cons hs (ih h')

namespace Reachability

/-- In a deterministic relation, the end of a finite path from x lies on every complete path from
x. -/
theorem mem_of_star {α : Type} {r : α → α → Prop} (hdet : ∀ x y y', r x y → r x y' → y = y')
    {x z : α} (h : Star r x z) : ∀ l, CPath r x l → z ∈ l := by
  induction h with
  | refl => exact fun _ hl => hl.head_mem
  | @cons x y z hxy _ ih =>
    intro l hl
    cases hl with
    | stuck hs => exact absurd ⟨y, hxy⟩ hs
    | cons hxy' hl' =>
      obtain rfl := hdet _ _ _ hxy hxy'
      exact List.mem_cons_of_mem _ (ih _ hl')

/-- In a deterministic relation, a claim whose every state of `P` has a finite path to a state of
`Q` holds on all paths. -/
theorem allPath_of_star {α : Type} {r : α → α → Prop} (hdet : ∀ x y y', r x y → r x y' → y = y')
    {P Q : α → Prop} (h : ∀ x, P x → ∃ z, Q z ∧ Star r x z) : AllPath r P Q := fun x hx l hl =>
  let ⟨z, hq, hs⟩ := h x hx
  ⟨z, mem_of_star hdet hs l hl, hq⟩

end Reachability

variable {c : Semantics}

/-! ## Steps and runs on terms -/

/-- Every configuration whose term is `u` has a step to a configuration whose term is `v`. -/
def StepsTo (c : Semantics) (u v : GroundTerm) : Prop :=
  ∀ x : Config c, x.val = u → ∃ y : Config c, y.val = v ∧ Step c x y

/-- Every configuration whose term is `u` has a run to a configuration whose term is `v`. -/
def Runs (c : Semantics) (u v : GroundTerm) : Prop :=
  ∀ x : Config c, x.val = u → ∃ y : Config c, y.val = v ∧ Star (Step c) x y

theorem Runs.refl (u : GroundTerm) : Runs c u u := fun x hx => ⟨x, hx, .refl⟩

theorem Runs.trans {u v w : GroundTerm} (h : Runs c u v) (h' : Runs c v w) : Runs c u w :=
  fun x hx =>
    let ⟨y, hy, hs⟩ := h x hx
    let ⟨z, hz, hs'⟩ := h' y hy
    ⟨z, hz, hs.trans hs'⟩

theorem Runs.cons {u v w : GroundTerm} (h : StepsTo c u v) (h' : Runs c v w) : Runs c u w :=
  fun x hx =>
    let ⟨y, hy, hs⟩ := h x hx
    let ⟨z, hz, hs'⟩ := h' y hy
    ⟨z, hz, .cons hs hs'⟩

theorem Runs.of_eq {u v w : GroundTerm} (h : Runs c u v) (he : v = w) : Runs c u w := he ▸ h

/-! ## A substitution as the list of its variables' values -/

/-- The substitution giving variable `k + i` the `i`-th value. -/
def subFrom : Nat → List GroundTerm → Subst
  | _, [] => []
  | k, v :: vs => (k, v) :: subFrom (k + 1) vs

/-- The substitution giving variable `i` the `i`-th value. -/
def sub (vs : List GroundTerm) : Subst := subFrom 0 vs

theorem lookup_subFrom : ∀ (k : Nat) (vs : List GroundTerm) (i : Nat),
    (subFrom k vs).lookup (k + i) = vs[i]?
  | _, [], _ => rfl
  | k, v :: vs, i => by
    simp only [subFrom, List.lookup]
    cases i with
    | zero => simp
    | succ i =>
      have hne : (k + (i + 1) == k) = false := by simp
      rw [hne]
      simp only [List.getElem?_cons_succ]
      rw [show k + (i + 1) = (k + 1) + i by omega]
      exact lookup_subFrom (k + 1) vs i

theorem lookup_sub (vs : List GroundTerm) (i : Nat) : (sub vs).lookup i = vs[i]? := by
  have h := lookup_subFrom 0 vs i
  rwa [Nat.zero_add] at h

/-- Each value has the sort at its position. -/
def SortsAre (c : Semantics) : List Srt → List GroundTerm → Prop
  | [], [] => True
  | s :: ss, v :: vs => c.sortOf v = some s ∧ SortsAre c ss vs
  | _, _ => False

theorem SortsAre.get : ∀ {ss : List Srt} {vs : List GroundTerm}, SortsAre c ss vs →
    ∀ {i : Nat} {s : Srt}, ss[i]? = some s → ∃ v, vs[i]? = some v ∧ c.sortOf v = some s
  | [], [], _, _, _, h => nomatch h
  | _ :: _, _ :: _, h, 0, _, hs => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨_, rfl, h.1⟩
  | _ :: _, _ :: _, h, i + 1, _, hs => by
    simp only [List.getElem?_cons_succ] at hs ⊢
    exact SortsAre.get h.2 hs
  | [], _ :: _, h, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _ => nomatch h

theorem wellSorted_sub {ss : List Srt} {vs : List GroundTerm} (h : SortsAre c ss vs) :
    c.WellSorted ss (sub vs) := fun _ _ hs =>
  let ⟨v, hv, hsv⟩ := h.get hs
  ⟨v, (lookup_sub vs _).trans hv, hsv⟩

/-! ## Aliases as one equation -/

mutual
  /-- For each alias `p #as i` of the pattern, the value σ gives `i` and `p`'s instance. -/
  def Term.aliasPairs (σ : Subst) : Term → List (Option GroundTerm × Option GroundTerm)
    | .var _ => []
    | .dv _ _ => []
    | .app _ ps => Term.aliasPairsList σ ps
    | .inj _ _ p => Term.aliasPairs σ p
    | .as p i => (σ.lookup i, Term.inst σ p) :: Term.aliasPairs σ p
  def Term.aliasPairsList (σ : Subst) : List Term → List (Option GroundTerm × Option GroundTerm)
    | [] => []
    | p :: ps => Term.aliasPairs σ p ++ Term.aliasPairsList σ ps
end

/-- The aliases' values equal their subpatterns' instances, as one equation of lists. -/
def Term.aliasCheck (σ : Subst) (p : Term) : Prop :=
  (Term.aliasPairs σ p).map Prod.fst = (Term.aliasPairs σ p).map Prod.snd

theorem pairs_eq_append {l l' : List (Option GroundTerm × Option GroundTerm)}
    (h : (l ++ l').map Prod.fst = (l ++ l').map Prod.snd) :
    l.map Prod.fst = l.map Prod.snd ∧ l'.map Prod.fst = l'.map Prod.snd := by
  simp only [List.map_append] at h
  exact List.append_inj h (by simp)

mutual
  theorem Term.aliases_of_check (σ : Subst) : ∀ (p : Term), Term.aliasCheck σ p → Term.Aliases σ p
    | .var _, _ => trivial
    | .dv _ _, _ => trivial
    | .app _ ps, h => Term.aliasesList_of_check σ ps h
    | .inj _ _ p, h => Term.aliases_of_check σ p h
    | .as p i, h => by
      simp only [Term.aliasCheck, Term.aliasPairs, List.map_cons, List.cons.injEq] at h
      exact ⟨h.1, Term.aliases_of_check σ p h.2⟩
  theorem Term.aliasesList_of_check (σ : Subst) : ∀ (ps : List Term),
      (Term.aliasPairsList σ ps).map Prod.fst = (Term.aliasPairsList σ ps).map Prod.snd →
      Term.AliasesList σ ps
    | [], _ => trivial
    | p :: ps, h => by
      simp only [Term.aliasPairsList] at h
      obtain ⟨h1, h2⟩ := pairs_eq_append h
      exact ⟨Term.aliases_of_check σ p h1, Term.aliasesList_of_check σ ps h2⟩
end

/-! ## One step by a rule -/

/-- One step by the `i`-th rule under the substitution `sub vs`, from a match the caller proves,
the `requires`, the right-hand side and the `ensures` evaluated by the executable evaluation. -/
theorem stepsTo_of_match (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    {i : Nat} {r : Rule} (hr : c.rules[i]? = some r) {vs : List GroundTerm} {u v : GroundTerm}
    (hσ : SortsAre c r.vars vs) (hm : PatVal c (sub vs) r.lhs u) (n : Nat)
    (hq : ∀ t, r.req = some t → Exec.evalT c n (sub vs) t = some (some (bool true)))
    (he : Exec.evalT c n (sub vs) r.rhs = some (some v))
    (hens : ∀ t, r.ens = some t → Exec.evalT c n (sub vs) t = some (some (bool true)))
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → ∀ x, NotApplies c r' x) : StepsTo c u v := by
  intro x hx
  subst hx
  have hσ' := wellSorted_sub hσ
  have hsc := sortCtx_of hok hsr (Exec.ovlCase_of hmr)
  have hcc := Exec.clauseCtx_of hok
  have hmc := Exec.matchCtx_of hmr
  obtain ⟨_, _, _, hreq, hrhs⟩ := Exec.ruleOK_of hok (List.mem_of_getElem? hr)
  have hen := Exec.ruleOK_ens_of hok (List.mem_of_getElem? hr)
  refine Step.exists_of_rule hok hsr hr hσ' hm (fun t ht => ?_) (fun r' h1 h2 => hprio r' h1 h2 _)
    (Exec.evalT_sound hsc hcc hmc n he Exec.headsOK_fns hσ' hrhs) (fun t ht => ?_) (Exec.ovlCase_of hmr)
  · rw [ht] at hreq
    exact Exec.evalT_sound hsc hcc hmc n (hq t ht) Exec.headsOK_fns hσ' (Exec.reqOK_some hreq)
  · rw [ht] at hen
    exact Exec.evalT_sound hsc hcc hmc n (hens t ht) Exec.headsOK_fns hσ' (Exec.reqOK_some hen)

/-- One step by the `i`-th rule, whose left-hand side is a constructor pattern, under the
substitution `sub vs`: the instance of the left-hand side is `u`, its aliases hold, and the
`requires`, the right-hand side and the `ensures` evaluate. -/
theorem stepsTo_of_rule (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    {i : Nat} {r : Rule} (hr : c.rules[i]? = some r) {vs : List GroundTerm} {u v : GroundTerm}
    (hσ : SortsAre c r.vars vs) (hp : r.lhs.ctorPat c = true) (hu : r.lhs.inst (sub vs) = some u)
    (ha : (Term.aliasPairs (sub vs) r.lhs).map Prod.fst = (Term.aliasPairs (sub vs) r.lhs).map Prod.snd)
    (n : Nat)
    (hq : ∀ t, r.req = some t → Exec.evalT c n (sub vs) t = some (some (bool true)))
    (he : Exec.evalT c n (sub vs) r.rhs = some (some v))
    (hens : ∀ t, r.ens = some t → Exec.evalT c n (sub vs) t = some (some (bool true)))
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → ∀ x, NotApplies c r' x) : StepsTo c u v :=
  stepsTo_of_match hok hsr hmr hr hσ ((PatVal.iff_inst hp).mpr ⟨hu, Term.aliases_of_check _ _ ha⟩)
    n hq he hens hprio

/-- Where every rule has one priority, no rule waits on another. -/
theorem no_prio_of {p : Nat} (h : c.rules.all (·.prio == p) = true) {r : Rule} (hr : r ∈ c.rules) :
    ∀ r' ∈ c.rules, r'.prio < r.prio → ∀ x, NotApplies c r' x := by
  intro r' hr' hlt
  have h1 := List.all_eq_true.mp h r hr
  have h2 := List.all_eq_true.mp h r' hr'
  simp only [beq_iff_eq] at h1 h2
  omega

end KCore
