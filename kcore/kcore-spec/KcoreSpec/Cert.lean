/-
  KCore, checked layer: run certificates.

  A certificate of a run is its start configuration and, for each step, the rule the step applies
  (its index among the core's rules) and the configuration it reaches. `checkRun` checks one by
  evaluating, for each step, the named rule alone (`ruleSuccs`, one rule's part of `successorsN`)
  and asking whether the recorded configuration is among its results. Every configuration is in
  the certificate, so nothing is replayed: one rule can have several matches (map patterns,
  non-linear keys), and the certificate says which result the run took. Certificates are not read
  by `Step` (the `Certificates` part of a `Definition` stays apart from `Semantics`).

  `Step` has rule priorities, so a named rule's result is a step only if
  no rule of a smaller priority applies. `lowerBlocked` decides that executably: every rule of a
  smaller priority has only matches whose `requires` evaluates to `false` or undefined within the
  fuel. Rules of the same or a larger priority are not evaluated, so for a definition whose rules
  share one priority (kimp, peano) a step costs one rule's evaluation.

  The index only chooses which rule to evaluate: soundness uses nothing about it beyond "the rule
  at this index is a rule of the core", so a wrong index can make a check fail but never succeed
  wrongly. Mapping krust's rule ids to indices is the generator's job, not this file's.

  **Every interpretation of the parameters.** A parameter symbol that no registry hook implements
  (`impl = none`) has the value the interpretation `hooks` gives it (`Semantics.paramVal`). The
  checks evaluate with `evalTC`, the executable evaluation except that it has no result (`none`,
  as out of fuel) where it would consult the interpretation: a parameter of `impl = none` applied
  to defined arguments, a silent point, or a function where every clause fails (its rest). So a
  check succeeds only for a run none of whose evaluations reads `hooks`, and that is decided with
  the run. Where no parameter is raw the checks read no interpretation (`checkRun_withHooks`,
  `stuckCheck_withHooks`): they read it only through `sortOf`, and an open generator's (a raw
  parameter's) application has its sort from the interpretation. A result `evalTC` gives on the
  data is then the executable evaluation's under every interpretation (`evalTC_withHooks`,
  `evalTC_sound`). The soundness theorems take "no parameter is raw" as their last argument,
  decided where the semantics is closed; for a definition with a raw parameter they say nothing.

  `checkRun_sound`: under the core's three decided conditions (`ok`, `srReady`, `matchReady`, the
  ones determinism and `step_iff_of_ok` use), a certificate accepted on the data gives, for every
  interpretation H, a reflexive-transitive chain of `Step (c.withHooks H)`s over `Config`.
  `checkRun_sound_wf`: the same from `wf`. `stuckCheck_sound`: a configuration `stuckCheck`
  accepts has no successor under any interpretation whose clauses of one priority are coherent
  (`CoherentAll`, which the completeness of the executable step reads); the check states that every rule's every
  match evaluates to a result within the fuel that gives no successor, so no fuel lists one.
  `checkRunFull` (membership in the whole `successorsN`, which reads `hooks`) is kept for the cost
  comparison; its soundness is for the semantics it is decided on.
-/
import KcoreSpec.StepIffWf
import KcoreSpec.Params

set_option autoImplicit false

namespace KCore.Cert

open KCore KCore.Exec

/-- The reflexive-transitive closure of a relation, head-first. -/
inductive Reach {α : Type} (r : α → α → Prop) : α → α → Prop where
  | refl (x : α) : Reach r x x
  | head {x y z : α} (h : r x y) (t : Reach r y z) : Reach r x z

/-! ## Evaluation that consults no interpretation of the parameters -/

/-- An interpreted symbol's result where it does not depend on the interpretation: `hook`'s,
except at a silent point where `hook` gives no value, where there is no result (`none`; the value
is the interpretation's, `Semantics.hookRes`). -/
def hookResC (f : Sym) (vs : List GroundTerm) : Option (Option GroundTerm) :=
  if silent f vs then (hook f vs).bind fun r => r.map some else hook f vs

/-- A parameter symbol's value at defined arguments where it does not depend on the
interpretation: the registry hook's (`impl = some g`, as `Semantics.paramVal` gives it, where
`hookResC` has one), or undefined for a symbol that is not a parameter; no result (`none`) for a
parameter whose value is the interpretation's (`impl = none`, or g at a silent point). -/
def paramValC (c : Semantics) (f : Sym) (vs : List GroundTerm) : Option (Option GroundTerm) :=
  match c.lookupParam f with
  | none => some none
  | some k => match k.impl with
    | some g => (hookResC g (c.libArgs g vs)).map fun o => (o.map (GroundTerm.asSort c.lib k.sig.result)).filter
        fun v => c.sortOf v == some k.sig.result
    | none => none

/-- One priority's candidates, each as its `requires` and (where that is `true`) its right-hand
side's result, read in order: `none` where every `requires` is `false`; otherwise the first that is
not decides, `some none` (no result) where its `requires` or its right-hand side is out of fuel. -/
def scanSeq : List (Option Bool × Option (Option GroundTerm)) → Option (Option (Option GroundTerm))
  | [] => none
  | (some false, _) :: rest => scanSeq rest
  | (some true, r) :: _ => some r
  | (none, _) :: _ => some none

mutual
  /-- `evalT`, except that a parameter of `impl = none` applied to defined arguments, a silent
  point and a function's rest have no result (`none`): `some r` is a result no interpretation of the parameters takes part in. -/
  def evalTC (c : Semantics) : Nat → Subst → Term → Option (Option GroundTerm)
    | 0, _, _ => none
    | _ + 1, σ, .var i => some (σ.lookup i)
    | _ + 1, _, .dv s l => some (some (.dv s l))
    | n + 1, σ, .inj a b t => (evalTC c n σ t).map (·.map (injNormal a b))
    | _ + 1, _, .as _ _ => none
    | n + 1, σ, .app f ts => do
      let rs ← evalTsC c n σ ts
      if c.isCtor f then pure ((allSome rs).map (.ctor f))
      else if isHook f then match allSome rs with
        | none => pure none
        | some vs => hookResC f vs
      else if c.isParam f then match allSome rs with
        | none => pure none
        | some vs => paramValC c f vs
      else match allSome rs with
        | none => pure none
        | some vs => evalFC c n f vs
  def evalTsC (c : Semantics) : Nat → Subst → List Term → Option (List (Option GroundTerm))
    | 0, _, _ => none
    | _ + 1, _, [] => some []
    | n + 1, σ, t :: ts => do pure ((← evalTC c n σ t) :: (← evalTsC c n σ ts))
  def evalFC (c : Semantics) : Nat → Sym → List GroundTerm → Option (Option GroundTerm)
    | 0, _, _ => none
    | n + 1, f, vs => do
      let fn ← c.lookupFn f
      firstClauseC c n vs (byPrio fn.clauses)
  /-- `firstClause`'s priorities, each priority's candidates read in order (`scanSeq`): the first
  whose `requires` is not `false` decides, so a result is the one `firstClause` finds. Where every
  clause fails there is no result (`none`): the value there is the function's rest, the
  interpretation's (`Semantics.fnRest`). -/
  def firstClauseC (c : Semantics) : Nat → List GroundTerm → List Clause → Option (Option GroundTerm)
    | 0, _, _ => none
    | _ + 1, _, [] => none
    | n + 1, vs, cl :: rest =>
      match scanSeq (((cl :: rest).takeWhile (·.prio == cl.prio)).flatMap fun cl' =>
          (clauseMatches c cl' vs).map fun σ =>
            let b := match cl'.req with
              | none => some true
              | some t => (evalTC c n σ t).map isTrue
            (b, if b == some true then
              (match (match cl'.ens with
                | none => some true
                | some t => (evalTC c n σ t).map isTrue) with
              | some true => evalTC c n σ cl'.rhs
              | some false => some none
              | none => none)
            else none)) with
      | some r => r
      | none => firstClauseC c n vs ((cl :: rest).dropWhile (·.prio == cl.prio))
end

/-- A match's `requires` by `evalTC` (`reqVal`'s). -/
def reqValC (c : Semantics) (n : Nat) (r : Rule) (σ : Subst) : Option Bool :=
  match r.req with
  | none => some true
  | some t => (evalTC c n σ t).map isTrue

/-- A rule's matches at x, each with its `requires` by `evalTC` (`ruleMatches`'s). -/
def ruleMatchesC (c : Semantics) (n : Nat) (r : Rule) (x : GroundTerm) : List (Subst × Option Bool) :=
  ((matchP c (patFuel [r.lhs]) [] r.lhs x).filter (wellSorted c r.vars)).map fun σ => (σ, reqValC c n r σ)

/-! ## The checks -/

/-- A match's `ensures` by `evalTC` (`ensVal`'s). -/
def ensValC (c : Semantics) (n : Nat) (r : Rule) (σ : Subst) : Option Bool :=
  match r.ens with
  | none => some true
  | some t => (evalTC c n σ t).map isTrue

/-- One rule's results at x with `n` units of evaluation fuel: for each match whose `requires` is
`true`, the configuration the right-hand side evaluates to where the `ensures` is `true`
(`successorsN`'s inner `filterMap`, by `evalTC`). -/
def ruleSuccs (c : Semantics) (n : Nat) (r : Rule) (x : GroundTerm) : List GroundTerm :=
  (ruleMatchesC c n r x).filterMap fun (σ, b) =>
    if b == some true then match evalTC c n σ r.rhs with
      | some (some y) =>
        if c.sortOf y == some topCellSort && ensValC c n r σ == some true then some y else none
      | _ => none
    else none

/-- No rule of a smaller priority than r applies at x: each of their matches has a `requires` that
evaluates to `false` or undefined within the fuel. -/
def lowerBlocked (c : Semantics) (n : Nat) (r : Rule) (x : GroundTerm) : Bool :=
  c.rules.all fun r' => !decide (r'.prio < r.prio) || (ruleMatchesC c n r' x).all (·.2 == some false)

/-- Rule `r` rewrites `x` to `y` (with `n` units of evaluation fuel). -/
def checkStep (c : Semantics) (n : Nat) (r : Rule) (x y : GroundTerm) : Bool :=
  lowerBlocked c n r x && (ruleSuccs c n r x).any (same · y)

/-- The chain from `x` through the recorded steps ends at `z`, each step by the rule at its
index. -/
def checkSteps (c : Semantics) (n : Nat) : GroundTerm → List (Nat × GroundTerm) → GroundTerm → Bool
  | x, [], z => same x z
  | x, (i, y) :: rest, z =>
    (match c.rules[i]? with
      | some r => checkStep c n r x y
      | none => false) && checkSteps c n y rest z

/-- A run certificate: `start` is a configuration and the recorded steps lead from it to
`final`. -/
def checkRun (c : Semantics) (n : Nat) (start : GroundTerm) (steps : List (Nat × GroundTerm))
    (final : GroundTerm) : Bool :=
  decide (c.sortOf start = some topCellSort) && checkSteps c n start steps final

/-! ## The same check against every rule (the cost comparison) -/

def checkStepsFull (c : Semantics) (n : Nat) : GroundTerm → List GroundTerm → GroundTerm → Bool
  | x, [], z => same x z
  | x, y :: rest, z => (successorsN c n x).any (same · y) && checkStepsFull c n y rest z

def checkRunFull (c : Semantics) (n : Nat) (start : GroundTerm) (steps : List GroundTerm)
    (final : GroundTerm) : Bool :=
  decide (c.sortOf start = some topCellSort) && checkStepsFull c n start steps final

/-! ## Stuckness -/

/-- Rule `r` gives `x` no successor, decided within evaluation fuel `n`: each match's `requires`
is `false` or undefined, or it is `true` and the right-hand side is undefined, or not a
configuration, or its `ensures` is not `true` (false or undefined); every evaluation it reads has a
result within the fuel, by `evalTC`. -/
def ruleStuck (c : Semantics) (n : Nat) (r : Rule) (x : GroundTerm) : Bool :=
  ((matchP c (patFuel [r.lhs]) [] r.lhs x).filter (wellSorted c r.vars)).all fun σ =>
    match reqValC c n r σ with
    | some false => true
    | some true => match evalTC c n σ r.rhs with
      | some none => true
      | some (some y) => !(c.sortOf y == some topCellSort) || ensValC c n r σ == some false
      | none => false
    | none => false

/-- No rule gives `x` a successor, decided within evaluation fuel `n`. -/
def stuckCheck (c : Semantics) (n : Nat) (x : GroundTerm) : Bool :=
  c.rules.all fun r => ruleStuck c n r x

/-! ## The checks do not read the interpretation of the parameters, where no parameter is raw

The checks read the interpretation only through `sortOf` (`paramValC`'s filter, `wellSorted`, a
result's being a configuration), and with no raw parameter the sorts are the same under every
interpretation (`Semantics.sortOf_withHooks`). The matcher reads no sort. -/

kernel_rfl matchP_withHooksC : ∀ (c : Semantics) (H : HookParams) (n : Nat) (σ : Subst) (p : Term)
  (v : GroundTerm), matchP (c.withHooks H) n σ p v = matchP c n σ p v
kernel_rfl matchL_withHooksC : ∀ (c : Semantics) (H : HookParams) (n : Nat) (σ : Subst) (ps : List Term)
  (vs : List GroundTerm), matchL (c.withHooks H) n σ ps vs = matchL c n σ ps vs

section
-- The proofs below read `sortOf` only through `Semantics.sortOf_withHooks`: it is irreducible here,
-- so that they do not depend on what its body reads.
attribute [local irreducible] Semantics.sortOf Semantics.sortsOf

variable (c : Semantics) (H : HookParams) (hr : ∀ k ∈ c.params, k.raw = false)
include hr

theorem sortOf_withHooks_hrC (v : GroundTerm) : (c.withHooks H).sortOf v = c.sortOf v :=
  congrFun (Semantics.sortOf_withHooks c H hr) v

theorem wellSorted_withHooks_hr (vars : List Srt) : wellSorted (c.withHooks H) vars = wellSorted c vars := by
  funext σ; unfold wellSorted; simp only [sortOf_withHooks_hrC c H hr]

theorem clauseMatches_withHooks_hr (cl : Clause) (vs : List GroundTerm) :
    clauseMatches (c.withHooks H) cl vs = clauseMatches c cl vs := by
  unfold clauseMatches
  rw [matchL_withHooksC, wellSorted_withHooks_hr c H hr]

theorem paramValC_withHooks (f : Sym) (vs : List GroundTerm) :
    paramValC (c.withHooks H) f vs = paramValC c f vs := by
  unfold paramValC; simp only [sortOf_withHooks_hrC c H hr]; rfl

theorem evalC_withHooks_hr : ∀ n,
    (∀ σ t, evalTC (c.withHooks H) n σ t = evalTC c n σ t) ∧
    (∀ σ ts, evalTsC (c.withHooks H) n σ ts = evalTsC c n σ ts) ∧
    (∀ f vs, evalFC (c.withHooks H) n f vs = evalFC c n f vs) ∧
    (∀ vs cls, firstClauseC (c.withHooks H) n vs cls = firstClauseC c n vs cls)
  | 0 => ⟨fun _ _ => by simp only [evalTC], fun _ _ => by simp only [evalTsC],
      fun _ _ => by simp only [evalFC], fun _ _ => by simp only [firstClauseC]⟩
  | n + 1 => by
    obtain ⟨ih1, ih2, ih3, ih4⟩ := evalC_withHooks_hr n
    refine ⟨fun σ t => ?_, fun σ ts => ?_, fun f vs => ?_, fun vs cls => ?_⟩
    · cases t with
      | app f ts =>
        simp only [evalTC, ih2, ih3, paramValC_withHooks c H hr]
        rfl
      | inj a b t => simp only [evalTC, ih1]
      | _ => simp only [evalTC]
    · cases ts with
      | nil => simp only [evalTsC]
      | cons t ts => simp only [evalTsC, ih1, ih2]
    · simp only [evalFC, ih4]
      rfl
    · cases cls with
      | nil => simp only [firstClauseC]
      | cons cl rest => simp only [firstClauseC, ih1, ih4, clauseMatches_withHooks_hr c H hr]

theorem evalTC_withHooks (n : Nat) (σ : Subst) (t : Term) :
    evalTC (c.withHooks H) n σ t = evalTC c n σ t := (evalC_withHooks_hr c H hr n).1 σ t

theorem evalFC_withHooks (n : Nat) (f : Sym) (vs : List GroundTerm) :
    evalFC (c.withHooks H) n f vs = evalFC c n f vs := (evalC_withHooks_hr c H hr n).2.2.1 f vs

theorem reqValC_withHooks_hr (n : Nat) (r : Rule) (σ : Subst) :
    reqValC (c.withHooks H) n r σ = reqValC c n r σ := by
  unfold reqValC; simp only [evalTC_withHooks c H hr]

theorem ensValC_withHooks_hr (n : Nat) (r : Rule) (σ : Subst) :
    ensValC (c.withHooks H) n r σ = ensValC c n r σ := by
  unfold ensValC; simp only [evalTC_withHooks c H hr]

theorem ruleMatchesC_withHooks (n : Nat) (r : Rule) (x : GroundTerm) :
    ruleMatchesC (c.withHooks H) n r x = ruleMatchesC c n r x := by
  unfold ruleMatchesC
  rw [matchP_withHooksC, wellSorted_withHooks_hr c H hr]
  simp only [reqValC_withHooks_hr c H hr]

theorem ruleSuccs_withHooks (n : Nat) (r : Rule) (x : GroundTerm) :
    ruleSuccs (c.withHooks H) n r x = ruleSuccs c n r x := by
  unfold ruleSuccs
  simp only [ruleMatchesC_withHooks c H hr, evalTC_withHooks c H hr, sortOf_withHooks_hrC c H hr,
    ensValC_withHooks_hr c H hr]

theorem lowerBlocked_withHooks (n : Nat) (r : Rule) (x : GroundTerm) :
    lowerBlocked (c.withHooks H) n r x = lowerBlocked c n r x := by
  unfold lowerBlocked
  simp only [ruleMatchesC_withHooks c H hr]
  rfl

theorem checkStep_withHooks (n : Nat) (r : Rule) (x y : GroundTerm) :
    checkStep (c.withHooks H) n r x y = checkStep c n r x y := by
  unfold checkStep; rw [lowerBlocked_withHooks c H hr, ruleSuccs_withHooks c H hr]

theorem checkSteps_withHooks (n : Nat) : ∀ (x : GroundTerm) (steps : List (Nat × GroundTerm)) (z : GroundTerm),
    checkSteps (c.withHooks H) n x steps z = checkSteps c n x steps z
  | x, [], z => by simp only [checkSteps]
  | x, (i, y) :: rest, z => by
    simp only [checkSteps, checkStep_withHooks c H hr, checkSteps_withHooks n y rest z]
    rfl

theorem checkRun_withHooks (n : Nat) (start : GroundTerm) (steps : List (Nat × GroundTerm))
    (final : GroundTerm) : checkRun (c.withHooks H) n start steps final = checkRun c n start steps final := by
  unfold checkRun; rw [Semantics.sortOf_withHooks c H hr, checkSteps_withHooks c H hr]

theorem ruleStuck_withHooks (n : Nat) (r : Rule) (x : GroundTerm) :
    ruleStuck (c.withHooks H) n r x = ruleStuck c n r x := by
  unfold ruleStuck
  rw [matchP_withHooksC, wellSorted_withHooks_hr c H hr]
  simp only [reqValC_withHooks_hr c H hr, evalTC_withHooks c H hr, sortOf_withHooks_hrC c H hr,
    ensValC_withHooks_hr c H hr]

theorem stuckCheck_withHooks (n : Nat) (x : GroundTerm) :
    stuckCheck (c.withHooks H) n x = stuckCheck c n x := by
  unfold stuckCheck
  simp only [ruleStuck_withHooks c H hr]
  rfl
end

/-! ## Soundness -/

section

variable {c : Semantics}

theorem hookResC_sound {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm}
    (h : hookResC f vs = some r) : c.hookRes f vs = some r := by
  unfold hookResC at h
  unfold Semantics.hookRes
  cases hs : silent f vs
  · rw [hs] at h; simpa using h
  · rw [hs] at h
    simp only [if_true] at h ⊢
    cases hh : hook f vs with
    | none => rw [hh] at h; cases h
    | some o =>
      rw [hh] at h
      cases o with
      | none => cases h
      | some v => simp at h; subst h; rfl

theorem paramValC_sound {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm}
    (h : paramValC c f vs = some r) : c.paramVal f vs = r := by
  unfold paramValC at h
  unfold Semantics.paramVal
  split at h
  · next hk => rw [hk]; cases h; rfl
  · next k hk =>
    rw [hk]
    split at h
    · next g hg =>
      obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [hg, hookResC_sound ho, Option.join_some]
    · cases h

/-- A candidate read by `evalTC`, as `firstClauseC` reads it. -/
def candC (c : Semantics) (n : Nat) (a : Clause × Subst × Option Bool) :
    Option Bool × Option (Option GroundTerm) :=
  let b := match a.1.req with
    | none => some true
    | some t => (evalTC c n a.2.1 t).map isTrue
  (b, if b == some true then
    (match (match a.1.ens with
      | none => some true
      | some t => (evalTC c n a.2.1 t).map isTrue) with
    | some true => evalTC c n a.2.1 a.1.rhs
    | some false => some none
    | none => none)
  else none)

theorem candidates_map (n : Nat) (vs : List GroundTerm) (cls : List Clause) :
    (candidates c n vs cls).map (candC c n) = cls.flatMap fun cl' => (clauseMatches c cl' vs).map fun σ =>
      let b := match cl'.req with
        | none => some true
        | some t => (evalTC c n σ t).map isTrue
      (b, if b == some true then
        (match (match cl'.ens with
          | none => some true
          | some t => (evalTC c n σ t).map isTrue) with
        | some true => evalTC c n σ cl'.rhs
        | some false => some none
        | none => none)
      else none) := by
  simp only [candidates, List.map_flatMap, List.map_map]
  rfl

/-- Reading the candidates in order finds what `firstClause` finds, where every value read is the
evaluation's. -/
theorem scanSeq_sound {n : Nat} {g : Clause × Subst × Option Bool → Option Bool × Option (Option GroundTerm)} :
    ∀ {l : List (Clause × Subst × Option Bool)},
    (∀ a ∈ l, (∀ x, (g a).1 = some x → a.2.2 = some x) ∧
      (∀ r, (g a).1 = some true → (g a).2 = some r → candBody c n a.1 a.2.1 = some r)) →
    (∀ {r}, scanSeq (l.map g) = some (some r) → l.findSome? (candResult c n) = some r) ∧
    (scanSeq (l.map g) = none → l.findSome? (candResult c n) = none ∧ l.all (·.2.2 == some false) = true)
  | [], _ => ⟨fun h => by simp [scanSeq] at h, fun _ => ⟨rfl, rfl⟩⟩
  | a :: l, hg => by
    obtain ⟨h1, h2⟩ := hg a (List.mem_cons_self ..)
    have ih := scanSeq_sound (l := l) (fun a' h' => hg a' (List.mem_cons_of_mem _ h'))
    simp only [List.map_cons]
    cases hb : (g a).1 with
    | none =>
      have : scanSeq ((g a) :: l.map g) = some none := by
        rw [show g a = ((g a).1, (g a).2) from rfl, hb]; rfl
      rw [this]
      exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
    | some b =>
      cases b with
      | false =>
        have : scanSeq ((g a) :: l.map g) = scanSeq (l.map g) := by
          rw [show g a = ((g a).1, (g a).2) from rfl, hb]; rfl
        rw [this]
        have ha : a.2.2 = some false := h1 false hb
        have hres : candResult c n a = none := by unfold candResult; simp [ha]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rw [List.findSome?_cons, hres]; exact ih.1 h
        · obtain ⟨h3, h4⟩ := ih.2 h
          refine ⟨by rw [List.findSome?_cons, hres]; exact h3, ?_⟩
          simp only [List.all_cons, ha, h4]; rfl
      | true =>
        have : scanSeq ((g a) :: l.map g) = some (g a).2 := by
          rw [show g a = ((g a).1, (g a).2) from rfl, hb]; rfl
        rw [this]
        refine ⟨fun {r} h => ?_, fun h => (by cases h)⟩
        have ha : a.2.2 = some true := h1 true hb
        have hr := h2 r hb (Option.some.inj h)
        rw [List.findSome?_cons]
        have hres : candResult c n a = some r := by unfold candResult; simp [ha, hr]
        rw [hres]

/-- A candidate read by `evalTC`, where `evalTC`'s results are `evalT`'s: its `requires`, when
computed, is the one `evalT` computes, and so is its result (`candBody`). -/
theorem cand_sound {n : Nat} (hev : ∀ σ t r, evalTC c n σ t = some r → evalT c n σ t = some r)
    (a : Clause × Subst × Option Bool) :
    (∀ x, (candC c n a).1 = some x → clauseReq c n a.1 a.2.1 = some x) ∧
    (∀ r, (candC c n a).1 = some true → (candC c n a).2 = some r → candBody c n a.1 a.2.1 = some r) := by
  obtain ⟨cl, σ, _⟩ := a
  refine ⟨fun x hx => ?_, fun r hb hr => ?_⟩
  · unfold candC at hx
    unfold clauseReq
    simp only at hx ⊢
    split at hx
    · next hq => simp only [hq]; exact hx
    · next t hq =>
      simp only [hq]
      simp only [Option.map_eq_some_iff] at hx ⊢
      obtain ⟨r₀, h₀, rfl⟩ := hx
      exact ⟨r₀, hev _ _ _ h₀, rfl⟩
  · unfold candC at hb hr
    simp only at hb hr
    rw [hb] at hr
    simp only [beq_self_eq_true, ↓reduceIte] at hr
    unfold candBody clauseEns
    cases he : cl.ens with
    | none => simp only [he] at hr ⊢; exact hev _ _ _ hr
    | some t =>
      simp only [he] at hr ⊢
      cases hq : evalTC c n σ t with
      | none => simp [hq] at hr
      | some w =>
        rw [hev _ _ _ hq]
        simp only [hq, Option.map_some] at hr ⊢
        cases hw : isTrue w with
        | true => simp only [hw] at hr ⊢; exact hev _ _ _ hr
        | false => simp only [hw] at hr ⊢; exact hr

theorem cands_sound {n : Nat} {vs : List GroundTerm} {cls : List Clause}
    (hev : ∀ σ t r, evalTC c n σ t = some r → evalT c n σ t = some r) :
    ∀ a ∈ candidates c n vs cls, (∀ x, (candC c n a).1 = some x → a.2.2 = some x) ∧
      (∀ r, (candC c n a).1 = some true → (candC c n a).2 = some r → candBody c n a.1 a.2.1 = some r) := by
  intro ⟨cl, σ, b⟩ ha
  obtain ⟨_, _, rfl⟩ := mem_candidates.mp ha
  exact cand_sound hev _

mutual
  /-- **A result of `evalTC` is the executable evaluation's.** -/
  theorem evalTC_sound : ∀ (n : Nat) {σ : Subst} {t : Term} {r : Option GroundTerm},
      evalTC c n σ t = some r → evalT c n σ t = some r
    | 0, _, _, _, h => by simp [evalTC] at h
    | n + 1, σ, .var i, r, h => by simpa [evalTC, evalT] using h
    | n + 1, σ, .dv s l, r, h => by simpa [evalTC, evalT] using h
    | n + 1, σ, .as t i, r, h => by simp [evalTC] at h
    | n + 1, σ, .inj a b t, r, h => by
      simp only [evalTC, Option.map_eq_some_iff] at h
      simp only [evalT, Option.map_eq_some_iff]
      obtain ⟨r₀, h₀, rfl⟩ := h
      exact ⟨r₀, evalTC_sound n h₀, rfl⟩
    | n + 1, σ, .app f ts, r, h => by
      simp only [evalTC, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      simp only [evalT, Option.bind_eq_bind, Option.bind_eq_some_iff]
      obtain ⟨rs, hrs, hk⟩ := h
      refine ⟨rs, evalTsC_sound n hrs, ?_⟩
      by_cases hc : c.isCtor f = true
      · simp only [hc, ↓reduceIte] at hk ⊢; exact hk
      · simp only [hc, ↓reduceIte, Bool.false_eq_true] at hk ⊢
        by_cases hh : isHook f = true
        · simp only [hh, ↓reduceIte] at hk ⊢
          cases hall : allSome rs with
          | none => simp only [hall] at hk ⊢; exact hk
          | some vs => simp only [hall] at hk ⊢; exact hookResC_sound hk
        · simp only [hh, ↓reduceIte, Bool.false_eq_true] at hk ⊢
          by_cases hp : c.isParam f = true
          · simp only [hp, ↓reduceIte] at hk ⊢
            cases hall : allSome rs with
            | none => simp only [hall] at hk ⊢; exact hk
            | some vs =>
              simp only [hall] at hk
              simp only [Option.bind_some, paramValC_sound hk]
              rfl
          · simp only [hp, ↓reduceIte, Bool.false_eq_true] at hk ⊢
            cases hall : allSome rs with
            | none => simp only [hall] at hk ⊢; exact hk
            | some vs => simp only [hall] at hk ⊢; exact evalFC_sound n hk
  theorem evalTsC_sound : ∀ (n : Nat) {σ : Subst} {ts : List Term} {rs : List (Option GroundTerm)},
      evalTsC c n σ ts = some rs → evalTs c n σ ts = some rs
    | 0, _, _, _, h => by simp [evalTsC] at h
    | n + 1, σ, [], rs, h => by simpa [evalTsC, evalTs] using h
    | n + 1, σ, t :: ts, rs, h => by
      simp only [evalTsC, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      simp only [evalTs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq]
      obtain ⟨r, hr, rs', hrs', rfl⟩ := h
      exact ⟨r, evalTC_sound n hr, rs', evalTsC_sound n hrs', rfl⟩
  theorem evalFC_sound : ∀ (n : Nat) {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm},
      evalFC c n f vs = some r → evalF c n f vs = some r
    | 0, _, _, _, h => by simp [evalFC] at h
    | n + 1, f, vs, r, h => by
      simp only [evalFC, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      simp only [evalF, Option.bind_eq_bind, Option.bind_eq_some_iff]
      obtain ⟨fn, hfn, hr⟩ := h
      exact ⟨fn, hfn, firstClauseC_sound n hr⟩
  theorem firstClauseC_sound : ∀ (n : Nat) {vs : List GroundTerm} {fr : Option GroundTerm} {cls : List Clause}
      {r : Option GroundTerm}, firstClauseC c n vs cls = some r → firstClause c n vs fr cls = some r
    | 0, _, _, _, _, h => by simp [firstClauseC] at h
    | n + 1, vs, _, [], r, h => by simp [firstClauseC] at h
    | n + 1, vs, fr, cl :: rest, r, h => by
      simp only [firstClauseC] at h
      rw [firstClause_cons]
      rw [← candidates_map] at h
      split at h
      · rename_i r' hs
        cases h
        rw [(scanSeq_sound (cands_sound (fun σ t r h => evalTC_sound n h))).1 hs]
      · rename_i hs
        obtain ⟨h1, h2⟩ := (scanSeq_sound (cands_sound (fun σ t r h => evalTC_sound n h))).2 hs
        rw [h1]
        simp only [h2, ↓reduceIte]
        exact firstClauseC_sound n h
end

theorem reqValC_sound {n : Nat} {r : Rule} {σ : Subst} {b : Bool} (h : reqValC c n r σ = some b) :
    reqVal c n r σ = some b := by
  unfold reqValC at h
  unfold reqVal
  split at h
  · next hq => rw [hq]; exact h
  · next t hq =>
    rw [hq]
    simp only [Option.map_eq_some_iff] at h ⊢
    obtain ⟨r₀, h₀, rfl⟩ := h
    exact ⟨r₀, evalTC_sound n h₀, rfl⟩

theorem ensValC_sound {n : Nat} {r : Rule} {σ : Subst} {b : Bool} (h : ensValC c n r σ = some b) :
    ensVal c n r σ = some b := by
  unfold ensValC at h
  unfold ensVal
  split at h
  · next hq => rw [hq]; exact h
  · next t hq =>
    rw [hq]
    simp only [Option.map_eq_some_iff] at h ⊢
    obtain ⟨r₀, h₀, rfl⟩ := h
    exact ⟨r₀, evalTC_sound n h₀, rfl⟩

theorem ruleMatchesC_mem {n : Nat} {r : Rule} {x : GroundTerm} {σ : Subst} {b : Option Bool} :
    (σ, b) ∈ ruleMatchesC c n r x ↔
      σ ∈ (matchP c (patFuel [r.lhs]) [] r.lhs x).filter (wellSorted c r.vars) ∧ b = reqValC c n r σ := by
  unfold ruleMatchesC
  rw [List.mem_map]
  constructor
  · rintro ⟨σ', hσ', he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨hσ', rfl⟩
  · rintro ⟨hσ, rfl⟩
    exact ⟨σ, hσ, rfl⟩

/-- A match whose `requires` `evalTC` decides is one of the executable step's, with that value. -/
theorem ruleMatches_of_C {n : Nat} {r : Rule} {x : GroundTerm} {σ : Subst} {b : Bool}
    (h : (σ, some b) ∈ ruleMatchesC c n r x) : (σ, some b) ∈ ruleMatches c n r x := by
  obtain ⟨hσ, hb⟩ := ruleMatchesC_mem.mp h
  exact ruleMatches_mem.mpr ⟨hσ, (reqValC_sound hb.symm).symm⟩

theorem ruleSuccs_mem {n : Nat} {r : Rule} {x y : GroundTerm} (hy : y ∈ ruleSuccs c n r x) :
    ∃ σ, (σ, some true) ∈ ruleMatches c n r x ∧ evalT c n σ r.rhs = some (some y) ∧
      c.sortOf y = some topCellSort ∧ ensVal c n r σ = some true := by
  rw [ruleSuccs, List.mem_filterMap] at hy
  obtain ⟨⟨σ, b⟩, hσb, hk⟩ := hy
  simp only at hk
  by_cases hb : b = some true
  · subst hb
    refine ⟨σ, ruleMatches_of_C hσb, ?_⟩
    simp only [beq_self_eq_true, ↓reduceIte] at hk
    cases he : evalTC c n σ r.rhs with
    | none => rw [he] at hk; cases hk
    | some o =>
      cases o with
      | none => rw [he] at hk; cases hk
      | some y' =>
        rw [he] at hk
        dsimp only at hk
        split at hk
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          cases hk; exact ⟨evalTC_sound n he, hc.1, ensValC_sound hc.2⟩
        · cases hk
  · have : (b == some true) = false := by simpa using hb
    simp [this] at hk

/-- A step the named rule checks is listed by the executable step. -/
theorem listed_of_checkStep {n : Nat} {r : Rule} {x y : GroundTerm} (hr : r ∈ c.rules)
    (h : checkStep c n r x y = true) : (successorsN c n x).any (same · y) = true := by
  simp only [checkStep, Bool.and_eq_true] at h
  obtain ⟨hlow, hy⟩ := h
  rw [List.any_eq_true] at hy ⊢
  obtain ⟨y', hmem, hs⟩ := hy
  obtain ⟨σ, hσ, he, hsort, hens⟩ := ruleSuccs_mem hmem
  refine ⟨y', successorsN_of hr (fun r' hr' hlt σb hσb => ?_) hσ he hsort hens, hs⟩
  have h' := List.all_eq_true.mp hlow r' hr'
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h'
  rcases h' with h' | h'
  · exact absurd hlt h'
  · obtain ⟨σ', b⟩ := σb
    obtain ⟨hσ', rfl⟩ := ruleMatches_mem.mp hσb
    have hc : (σ', reqValC c n r' σ') ∈ ruleMatchesC c n r' x := ruleMatchesC_mem.mpr ⟨hσ', rfl⟩
    have hf : reqValC c n r' σ' = some false := by simpa using List.all_eq_true.mp h' _ hc
    exact reqValC_sound hf

variable (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)

include hok hsr hmr in
/-- One listed successor, at any fuel, is a `Step` to a configuration. -/
theorem step_of_listed {n : Nat} {x : Config c} {y : GroundTerm}
    (hy : (successorsN c n x.val).any (same · y) = true) :
    ∃ hy' : c.sortOf y = some topCellSort, Step c x ⟨y, hy'⟩ := by
  rw [List.any_eq_true] at hy
  obtain ⟨y', hmem, hs⟩ := hy
  rw [same_iff] at hs
  subst hs
  obtain ⟨r, hr, σ, hσ, hpv, hreq, heval, hens, hsort, hprio⟩ := successorsN_sound hok hsr hmr hmem
  exact ⟨hsort, Step.rule_top r hr σ (Semantics.ok_rule hok hr).2.1 (Semantics.ok_rule hok hr).2.2.1 hσ hpv hreq heval hens hprio⟩

include hok hsr hmr in
theorem checkSteps_sound {n : Nat} :
    ∀ (steps : List (Nat × GroundTerm)) (x : Config c) (z : GroundTerm),
      checkSteps c n x.val steps z = true →
      ∃ hz : c.sortOf z = some topCellSort, Reach (Step c) x ⟨z, hz⟩
  | [], x, z, h => by
    unfold checkSteps at h
    rw [same_iff] at h
    subst h
    exact ⟨x.property, .refl x⟩
  | (i, y) :: rest, x, z, h => by
    unfold checkSteps at h
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases hr : c.rules[i]? with
    | none => rw [hr] at h1; cases h1
    | some r =>
      rw [hr] at h1
      obtain ⟨hy, hstep⟩ := step_of_listed hok hsr hmr (listed_of_checkStep (List.mem_of_getElem? hr) h1)
      obtain ⟨hz, hreach⟩ := checkSteps_sound rest ⟨y, hy⟩ z h2
      exact ⟨hz, .head hstep hreach⟩

include hok hsr hmr in
/-- **Soundness of run certificates, for every interpretation of the parameters.** A certificate
that `checkRun` accepts on the data (at any evaluation fuel `n`) shows, for every H, that `final`
is a configuration reachable from the configuration `start` by `Step (c.withHooks H)`s: none of the
check's evaluations consults the interpretation, and where no parameter is raw (`hr`) neither does
a sort. -/
theorem checkRun_sound {n : Nat} {start final : GroundTerm} {steps : List (Nat × GroundTerm)}
    (h : checkRun c n start steps final = true) (H : HookParams)
    (hr : ∀ k ∈ c.params, k.raw = false := by decide +kernel) :
    ∃ (hs : (c.withHooks H).sortOf start = some topCellSort)
      (hf : (c.withHooks H).sortOf final = some topCellSort),
      Reach (Step (c.withHooks H)) ⟨start, hs⟩ ⟨final, hf⟩ := by
  rw [← checkRun_withHooks c H hr] at h
  unfold checkRun at h
  rw [Bool.and_eq_true, decide_eq_true_iff] at h
  obtain ⟨hs, h⟩ := h
  obtain ⟨hf, hreach⟩ := checkSteps_sound ((Semantics.ok_withHooks c H).trans hok)
    ((Semantics.srReady_withHooks c H).trans hsr) ((Semantics.matchReady_withHooks c H).trans hmr)
    steps ⟨start, hs⟩ final h
  exact ⟨hs, hf, hreach⟩

include hok hsr hmr in
theorem checkStepsFull_sound {n : Nat} :
    ∀ (steps : List GroundTerm) (x : Config c) (z : GroundTerm),
      checkStepsFull c n x.val steps z = true →
      ∃ hz : c.sortOf z = some topCellSort, Reach (Step c) x ⟨z, hz⟩
  | [], x, z, h => by
    unfold checkStepsFull at h
    rw [same_iff] at h
    subst h
    exact ⟨x.property, .refl x⟩
  | y :: rest, x, z, h => by
    unfold checkStepsFull at h
    rw [Bool.and_eq_true] at h
    obtain ⟨hy, hstep⟩ := step_of_listed hok hsr hmr h.1
    obtain ⟨hz, hreach⟩ := checkStepsFull_sound rest ⟨y, hy⟩ z h.2
    exact ⟨hz, .head hstep hreach⟩

include hok hsr hmr in
theorem checkRunFull_sound {n : Nat} {start final : GroundTerm} {steps : List GroundTerm}
    (h : checkRunFull c n start steps final = true) :
    ∃ (hs : c.sortOf start = some topCellSort) (hf : c.sortOf final = some topCellSort),
      Reach (Step c) ⟨start, hs⟩ ⟨final, hf⟩ := by
  unfold checkRunFull at h
  rw [Bool.and_eq_true, decide_eq_true_iff] at h
  obtain ⟨hs, h⟩ := h
  obtain ⟨hf, hreach⟩ := checkStepsFull_sound hok hsr hmr steps ⟨start, hs⟩ final h
  exact ⟨hs, hf, hreach⟩

omit hok hsr hmr in
/-- What `ruleStuck` gives at a match, read with the executable evaluation. -/
theorem ruleStuck_at {n : Nat} {r : Rule} {σ : Subst}
    (h : (match reqValC c n r σ with
      | some false => true
      | some true => match evalTC c n σ r.rhs with
        | some none => true
        | some (some y) => !(c.sortOf y == some topCellSort) || ensValC c n r σ == some false
        | none => false
      | none => false) = true) :
    reqVal c n r σ = some false ∨ (reqVal c n r σ = some true ∧
      (evalT c n σ r.rhs = some none ∨
        ∃ y, evalT c n σ r.rhs = some (some y) ∧
          (c.sortOf y ≠ some topCellSort ∨ ensVal c n r σ = some false))) := by
  cases hq : reqValC c n r σ with
  | none => rw [hq] at h; cases h
  | some b =>
    cases b with
    | false => exact Or.inl (reqValC_sound hq)
    | true =>
      rw [hq] at h
      refine Or.inr ⟨reqValC_sound hq, ?_⟩
      cases he : evalTC c n σ r.rhs with
      | none => rw [he] at h; cases h
      | some o =>
        rw [he] at h
        cases o with
        | none => exact Or.inl (evalTC_sound n he)
        | some y =>
          refine Or.inr ⟨y, evalTC_sound n he, ?_⟩
          by_cases hs : c.sortOf y = some topCellSort
          · simp only [hs, beq_self_eq_true, Bool.not_true, Bool.false_or, beq_iff_eq] at h
            exact Or.inr (ensValC_sound h)
          · exact Or.inl hs

include hok hsr hmr in
/-- A match's `ensures` is not `false` at one fuel and `true` at another: it is a sorted term
(`ok`), which has one result where clauses of one priority are coherent. -/
theorem ensVal_not_false_true (hco : CoherentAll c) {r : Rule} (hr : r ∈ c.rules) {σ : Subst}
    (hσw : c.WellSorted r.vars σ) {n m : Nat} (hn : ensVal c n r σ = some false)
    (hm : ensVal c m r σ = some true) : False := by
  have hsc := sortCtx_of hok hsr (Exec.ovlCase_of hmr)
  have hcc := clauseCtx_of hok
  have hmc := matchCtx_of hmr
  have hens := ruleOK_ens_of hok hr
  unfold ensVal at hn hm
  cases hre : r.ens with
  | none => rw [hre] at hn; cases hn
  | some t =>
    rw [hre] at hn hm hens
    cases hv : evalT c n σ t with
    | none => simp [hv] at hn
    | some v =>
      cases hw : evalT c m σ t with
      | none => simp [hw] at hm
      | some w =>
        cases EvalTerm.functional hco (evalT_sound hsc hcc hmc n hv headsOK_fns hσw (reqOK_some hens))
          (evalT_sound hsc hcc hmc m hw headsOK_fns hσw (reqOK_some hens))
        simp only [hv, hw, Option.map_some, Option.some.injEq] at hn hm
        rw [hn] at hm; cases hm

include hok hsr hmr in
/-- A configuration `stuckCheck` accepts at fuel n has no listed successor at any fuel: a listed
successor comes from a match whose `requires` is `true`, whose right-hand side is a
configuration and whose `ensures` is `true` at that fuel, and the results at fuel n, being defined, are the same (both are the
relation's, which has one result where clauses of one priority are coherent). -/
theorem successorsN_nil_of_stuckCheck (hco : CoherentAll c) {n : Nat} {x : GroundTerm}
    (h : stuckCheck c n x = true) (m : Nat) : successorsN c m x = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro y hy
  obtain ⟨r, hr, -, σ, hσb, he, hs, hens⟩ := successorsN_mem_ens hy
  obtain ⟨hσm, hb⟩ := ruleMatches_mem.mp hσb
  have h2 := ruleStuck_at (List.all_eq_true.mp (List.all_eq_true.mp h r hr) σ hσm)
  -- the results at fuel n, when defined, are those at fuel m
  have hσw : c.WellSorted r.vars σ := wellSorted_iff.mp (List.mem_filter.mp hσm).2
  obtain ⟨-, -, -, hrqOK, hrtOK⟩ := ruleOK_of hok hr
  have hsc := sortCtx_of hok hsr (Exec.ovlCase_of hmr)
  have hcc := clauseCtx_of hok
  have hmc := matchCtx_of hmr
  -- the rule's `requires` and right-hand side are well sorted
  have hagree : ∀ {t : Term} {v w : Option GroundTerm} {s : Srt},
      sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some s → evalT c n σ t = some v →
      evalT c m σ t = some w → v = w := fun ht hv hw =>
    EvalTerm.functional hco (evalT_sound hsc hcc hmc n hv headsOK_fns hσw ht)
      (evalT_sound hsc hcc hmc m hw headsOK_fns hσw ht)
  have hreq : reqVal c n r σ = some true ∨ reqVal c n r σ = none := by
    unfold reqVal at hb ⊢
    cases hrq : r.req with
    | none => left; rfl
    | some t =>
      rw [hrq] at hb
      cases hm : evalT c m σ t with
      | none => simp [hm] at hb
      | some w =>
        cases hn : evalT c n σ t with
        | none => right; simp only [hn, Option.map_none]
        | some v =>
          left
          rw [hrq] at hrqOK
          cases hagree (reqOK_some hrqOK) hn hm
          simp only [hm, Option.map_some, Option.some.injEq] at hb
          simp [hn, hb]
  rcases h2 with h2 | ⟨h2, h3⟩
  · rcases hreq with hreq | hreq <;> rw [hreq] at h2 <;> cases h2
  · rcases h3 with h3 | ⟨y', h3, hs'⟩
    · cases hagree hrtOK h3 he
    · cases hagree hrtOK h3 he
      rcases hs' with hs' | hs'
      · exact hs' hs
      · exact ensVal_not_false_true hok hsr hmr hco hr hσw hs' hens

include hok hsr hmr in
/-- **Stuckness, for every interpretation of the parameters.** A configuration that `stuckCheck`
accepts on the data at some fuel has no `Step (c.withHooks H)` successor, for every H whose clauses
of one priority are coherent (a step is then listed by the executable step, `Exec.step_iff_all`),
where no clause is `aside` and no parameter is raw. -/
theorem stuckCheck_sound (H : HookParams) (hco : CoherentAll (c.withHooks H)) {n : Nat}
    {x : Config (c.withHooks H)} (h : stuckCheck c n x.val = true)
    (hna : c.asideFree = true := by decide +kernel)
    (hr : ∀ k ∈ c.params, k.raw = false := by decide +kernel) : ∀ y, ¬ Step (c.withHooks H) x y := by
  intro y hstep
  obtain ⟨m, hm⟩ := (Exec.step_iff_all hok hsr hmr H hco x y hna).mp hstep
  rw [successorsN_nil_of_stuckCheck ((Semantics.ok_withHooks c H).trans hok)
    ((Semantics.srReady_withHooks c H).trans hsr) ((Semantics.matchReady_withHooks c H).trans hmr) hco
    ((stuckCheck_withHooks c H hr n x.val).trans h) m] at hm
  cases hm

end

/-- `checkRun_sound` from `wf` and `ok`, without overloading symbols. -/
theorem checkRun_sound_wf {d : Definition} (hwf : wf d = true) (hok : d.sem.ok = true) (hno : d.sem.ovls = []) {n : Nat} {start final : GroundTerm}
    {steps : List (Nat × GroundTerm)} (h : checkRun d.sem n start steps final = true) (H : HookParams)
    (hr : ∀ k ∈ d.sem.params, k.raw = false := by decide +kernel) :
    ∃ (hs : (d.sem.withHooks H).sortOf start = some topCellSort)
      (hf : (d.sem.withHooks H).sortOf final = some topCellSort),
      Reach (Step (d.sem.withHooks H)) ⟨start, hs⟩ ⟨final, hf⟩ :=
  checkRun_sound hok (NamesApart.srReady_of_wf hwf) (NamesApart.matchReady_of_wf hwf hno) h H hr

/-- `stuckCheck_sound` from `wf` and `ok`, without overloading symbols. -/
theorem stuckCheck_sound_wf {d : Definition} (hwf : wf d = true) (hok : d.sem.ok = true) (hno : d.sem.ovls = [])
    (H : HookParams) (hco : CoherentAll (d.sem.withHooks H)) {n : Nat} {x : Config (d.sem.withHooks H)}
    (h : stuckCheck d.sem n x.val = true) (hna : d.sem.asideFree = true := by decide +kernel)
    (hr : ∀ k ∈ d.sem.params, k.raw = false := by decide +kernel) :
    ∀ y, ¬ Step (d.sem.withHooks H) x y :=
  stuckCheck_sound hok (NamesApart.srReady_of_wf hwf) (NamesApart.matchReady_of_wf hwf hno) H hco h hna hr

end KCore.Cert
