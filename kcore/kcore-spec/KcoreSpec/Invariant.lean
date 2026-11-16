/-
  KCore. The invariant theorem kind (ARCHITECTURE.md §3.7). Checked layer, generic in the semantics;
  the statements `RuleSteps`, `Frame`, `Guard.Holds` and `steps_of` are the kind's frozen part.

  The kind's shape:
  1. **statement**: every step `Step c x y` relates x and y by a property `P x.val y.val`;
  2. **decided condition** per rule: `frameOK c p r` or `guardOK c g r`, read off the rule's
     syntax (no evaluation, no search);
  3. **one generic theorem**, `steps_of`: the rules whose index is not listed satisfy the
     condition (one kernel decision, `allExcept`), and the condition gives P for each step of the
     rule (`frame_sound`, `guard_sound`);
  4. **named obligations**: each listed rule's steps (`RuleSteps c r P`), proved by hand or left as a
     premise.
  As a `Kind` (Kind.lean): `stepsKind c P`, indexed by the rules, the obligation at a rule
  `RuleSteps c r P`, the goal every step's P (`steps_of_rules`); a condition on rules is its decider
  (`Kind.listDecider`), and `steps_of` is `Kind.of_decided` with the decision `allExcept` read as the
  kind's (`decides_of_allExcept`). `stepsKindAll c H P` is the same for an interpretation H of the
  parameters, indexed by the data's rules, with `stepsDecider` the decider of a condition that does
  not read `hooks`.

  An invariant of executions (`Invariant c Init Inv`) is a property of configurations that holds at
  every initial one and that every step keeps; `Invariant.reach` gives it at every configuration
  reachable from an initial one (`Cert.Reach (Step c)`). `invariant_of_steps` gives the step half
  from `steps_of` at the property `P x y := Inv' x → Inv' y`, so a rule the decided condition does
  not close is the obligation `RuleSteps c r (fun x y => Inv' x → Inv' y)`. `frame_inv_sound` and
  `guard_inv_sound` are the two conditions in that form.

  `steps_of_all` and `invariant_of_steps_all` are the same for every interpretation H of the
  parameters (`c.withHooks H`): the conditions read the rules' syntax and the definition's
  constructors, never `hooks` (`frameOK_withHooks`, `guardOK_withHooks`), so one decision on the
  data covers every interpretation, and the obligations are stated under H.

  Two conditions, each a property of positions in the configuration (`Path`: an argument of a
  constructor of known arity, or the inside of an injection):
  - **frame** (`Frame p`): the subterm at p is the same before and after. The condition: along p,
    both sides of the rule are constructor applications (or injections of constructor or literal
    terms) of the path's shape, and at p the left-hand side binds a variable that the right-hand
    side is (`<top> P, X </top> => <top> Q, X </top>`);
  - **guard** (`Guard.Holds g`): after the step, if the subterm at `g.path` has the constructor
    `g.head`, its subterm at `g.sub` is `g.val`. The condition: the right-hand side at `g.path`
    is a constructor term of another head, an injection or a literal; or it has the head and its
    subterm at `g.sub` is pinned to `g.val`: built from constructors, literals, injections, and
    variables that the left-hand side binds by an alias of a closed pattern (`z #as V`).
  Matching and evaluation are relations (`PatVal`, `EvalTerm`), so neither
  condition needs a linearity check: a variable bound twice is bound to one value.
-/
import KcoreSpec.Cert
import KcoreSpec.Kind
import KcoreSpec.EvalLemmas
import KcoreSpec.OrderLaws

set_option autoImplicit false

namespace KCore

/-! ## Positions -/

/-- One step down a term: argument `i` of the constructor `f` applied to `n` arguments, or the
inside of an injection into the sort `b`. -/
inductive Pos where
  | arg (f : Sym) (n i : Nat)
  | inj (b : Srt)
  deriving Repr

abbrev Path := List Pos

/-- The subterm of a value at a path; `none` where the value does not have the path's shape. -/
def GroundTerm.atPath : Path → GroundTerm → Option GroundTerm
  | [], v => some v
  | .arg f n i :: p, .ctor g vs =>
    if g == f && vs.length == n then (vs[i]?).bind (GroundTerm.atPath p) else none
  | .inj b :: p, .inj _ b' w => if b' == b then GroundTerm.atPath p w else none
  | _ :: _, _ => none

theorem GroundTerm.atPath_arg {f : Sym} {n i : Nat} {p : Path} {v w : GroundTerm}
    (h : v.atPath (.arg f n i :: p) = some w) :
    ∃ vs u, v = .ctor f vs ∧ vs.length = n ∧ vs[i]? = some u ∧ u.atPath p = some w := by
  cases v with
  | ctor g vs =>
    simp only [GroundTerm.atPath] at h
    split at h
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, hl⟩ := hc
      obtain ⟨u, hu, hw⟩ := Option.bind_eq_some_iff.mp h
      exact ⟨vs, u, rfl, hl, hu, hw⟩
    · cases h
  | _ => simp [GroundTerm.atPath] at h

/-- The constructor at the root of a value. -/
def GroundTerm.headSym : GroundTerm → Option Sym
  | .ctor f _ => some f
  | _ => none

/-- A term whose value is a constructor term of its own head, or the literal itself: a
constructor application (not a pattern hook), or a domain value. -/
def ctorHeaded (c : Semantics) : Term → Bool
  | .app f _ => c.isCtor f && !patternHooks.contains f
  | .dv .. => true
  | _ => false

/-- The subterm of a rule's side at a path, when every node along it is a constructor
application of the path's head and arity (not a pattern hook), or an injection into the path's
sort of a `ctorHeaded` term. -/
def Term.atPath (c : Semantics) : Path → Term → Option Term
  | [], t => some t
  | .arg f n i :: p, .app g ts =>
    if g == f && ts.length == n && c.isCtor f && !patternHooks.contains f then
      (ts[i]?).bind (Term.atPath c p) else none
  | .inj b :: p, .inj _ b' t => if b' == b && ctorHeaded c t then Term.atPath c p t else none
  | _ :: _, _ => none

/-! ## Values a rule's right-hand side pins -/

mutual
  /-- The value of a closed pattern (constructors, injections, literals). -/
  def closedVal (c : Semantics) : Term → Option GroundTerm
    | .dv s l => some (.dv s l)
    | .app f ps =>
      if c.isCtor f && !patternHooks.contains f then (closedVals c ps).map (.ctor f) else none
    | .inj a b p => (closedVal c p).map (injNormal a b)
    | .var _ => none
    | .as .. => none
    termination_by structural t => t
  def closedVals (c : Semantics) : List Term → Option (List GroundTerm)
    | [] => some []
    | p :: ps => match closedVal c p, closedVals c ps with
      | some v, some vs => some (v :: vs)
      | _, _ => none
    termination_by structural ps => ps
end

mutual
  /-- The value a pattern forces on its variable i: the first alias `p #as i` of a closed p. -/
  def asPin (c : Semantics) (i : Nat) : Term → Option GroundTerm
    | .as p j => if j == i then
        (match closedVal c p with
          | some g => some g
          | none => asPin c i p)
      else asPin c i p
    | .app _ ps => asPins c i ps
    | .inj _ _ p => asPin c i p
    | .var _ => none
    | .dv .. => none
    termination_by structural t => t
  def asPins (c : Semantics) (i : Nat) : List Term → Option GroundTerm
    | [] => none
    | p :: ps => match asPin c i p with
      | some g => some g
      | none => asPins c i ps
    termination_by structural ps => ps
end

mutual
  /-- The value a right-hand-side term has under every σ under which `lhs` matches: built from
  constructors, literals, injections and variables `asPin` pins. -/
  def pin (c : Semantics) (lhs : Term) : Term → Option GroundTerm
    | .var i => asPin c i lhs
    | .dv s l => some (.dv s l)
    | .app f ts => if c.isCtor f then (pins c lhs ts).map (.ctor f) else none
    | .inj a b t => (pin c lhs t).map (injNormal a b)
    | .as .. => none
    termination_by structural t => t
  def pins (c : Semantics) (lhs : Term) : List Term → Option (List GroundTerm)
    | [] => some []
    | t :: ts => match pin c lhs t, pins c lhs ts with
      | some v, some vs => some (v :: vs)
      | _, _ => none
    termination_by structural ts => ts
end

/-! ## The kind -/

/-- `RuleSteps c r P`: every step by rule r has the property P: under every well-sorted σ under
which its left-hand side denotes x, its `requires` holds and its right-hand side evaluates to y,
`P x y`. The form of a named obligation. -/
def RuleSteps (c : Semantics) (r : Rule) (P : GroundTerm → GroundTerm → Prop) : Prop :=
  ∀ σ x y, c.WellSorted r.vars σ → PatVal c σ r.lhs x →
    (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) → EvalTerm c σ r.rhs (some y) → P x y

/-- The rules from index `i` on satisfy `cond`, except those whose index is in `obl`. -/
def allExcept (cond : Rule → Bool) (obl : List Nat) : Nat → List Rule → Bool
  | _, [] => true
  | i, r :: rs => (obl.contains i || cond r) && allExcept cond obl (i + 1) rs

theorem allExcept_get {cond : Rule → Bool} {obl : List Nat} :
    ∀ (rs : List Rule) (i j : Nat) (r : Rule), allExcept cond obl i rs = true → rs[j]? = some r →
      obl.contains (i + j) = true ∨ cond r = true
  | [], _, _, _, _, h => nomatch h
  | r' :: rs, i, j, r, h, hj => by
    simp only [allExcept, Bool.and_eq_true, Bool.or_eq_true] at h
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simpa using h.1
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      have := allExcept_get rs (i + 1) j r h.2 hj
      rwa [Nat.add_assoc, Nat.add_comm 1 j] at this

/-- `allExcept` is the decision of a kind indexed by the rules (`Kind.ofList`): every index is
confirmed by the condition at its rule or listed. -/
theorem decides_of_allExcept {cond : Rule → Bool} {obl : List Nat} {rs : List Rule}
    (h : allExcept cond obl 0 rs = true) : Kind.decides (Kind.listCond rs cond) obl (List.range rs.length) = true := by
  refine List.all_eq_true.mpr fun i hi => ?_
  have hi := List.mem_range.mp hi
  have := allExcept_get rs 0 i rs[i] h (List.getElem?_eq_getElem hi)
  simp only [Kind.listCond, List.getElem?_eq_getElem hi, Nat.zero_add, Bool.or_eq_true] at this ⊢
  exact this.symm

/-- Every rule's steps have P: so every step has P. -/
theorem steps_of_rules {c : Semantics} {P : GroundTerm → GroundTerm → Prop}
    (h : ∀ r ∈ c.rules, RuleSteps c r P) : ∀ x y : Config c, Step c x y → P x.val y.val := by
  intro x y hs
  cases hs with
  | rule r mem σ hσ hmatch hreq _ heval _ _ _ => exact h r mem σ _ _ hσ hmatch hreq heval

/-- **The invariant kind**: indexed by the rules, the obligation at a rule its steps' having P
(`RuleSteps c r P`), the goal every step's having P. -/
@[reducible] def stepsKind (c : Semantics) (P : GroundTerm → GroundTerm → Prop) : Kind :=
  Kind.ofList c.rules (fun r => RuleSteps c r P) (∀ x y : Config c, Step c x y → P x.val y.val) steps_of_rules

/-- **The generic theorem.** If `cond` gives P for each step of a rule (`sound`), every rule not
listed in `obl` satisfies `cond` (one decision), and every listed rule is an obligation proved,
then every step has P. -/
theorem steps_of {c : Semantics} {P : GroundTerm → GroundTerm → Prop} {cond : Rule → Bool}
    (sound : ∀ r, cond r = true → RuleSteps c r P) {obl : List Nat}
    (h : allExcept cond obl 0 c.rules = true)
    (ho : ∀ i ∈ obl, ∀ r, c.rules[i]? = some r → RuleSteps c r P) :
    ∀ x y : Config c, Step c x y → P x.val y.val :=
  Kind.of_decided (stepsKind c P) (Kind.listDecider cond fun r _ h => sound r h) obl (decides_of_allExcept h) ho

theorem RuleSteps.mono {c : Semantics} {r : Rule} {P Q : GroundTerm → GroundTerm → Prop}
    (hPQ : ∀ x y, P x y → Q x y) (h : RuleSteps c r P) : RuleSteps c r Q :=
  fun σ x y hσ hm hreq he => hPQ x y (h σ x y hσ hm hreq he)

/-! ## Invariants of executions -/

/-- `Invariant c Init Inv`: Inv holds at every configuration where Init holds, and every step from
a configuration where Inv holds reaches one where Inv holds. -/
def Invariant (c : Semantics) (Init Inv : Config c → Prop) : Prop :=
  (∀ x, Init x → Inv x) ∧ ∀ x y, Inv x → Step c x y → Inv y

/-- **An invariant holds at every configuration reachable from an initial one.** -/
theorem Invariant.reach {c : Semantics} {Init Inv : Config c → Prop} (h : Invariant c Init Inv)
    {x y : Config c} (hx : Init x) (hr : Cert.Reach (Step c) x y) : Inv y := by
  have kept : ∀ {a b : Config c}, Cert.Reach (Step c) a b → Inv a → Inv b := by
    intro a b hab
    induction hab with
    | refl => exact id
    | head hs _ ih => exact fun ha => ih (h.2 _ _ ha hs)
  exact kept hr (h.1 x hx)

/-- **The step half of an invariant from the generic theorem**: a property of values that each rule
not listed keeps by `cond`, and each listed rule keeps by its obligation, is kept by every step. -/
theorem invariant_of_steps {c : Semantics} {Inv' : GroundTerm → Prop} {cond : Rule → Bool}
    (sound : ∀ r, cond r = true → RuleSteps c r (fun x y => Inv' x → Inv' y)) {obl : List Nat}
    (h : allExcept cond obl 0 c.rules = true)
    (ho : ∀ i ∈ obl, ∀ r, c.rules[i]? = some r → RuleSteps c r (fun x y => Inv' x → Inv' y)) :
    ∀ x y : Config c, Inv' x.val → Step c x y → Inv' y.val :=
  fun x y hx hs => steps_of sound h ho x y hs hx

/-! ## Every interpretation of the parameters

A condition decided on the data that does not read `hooks` (`cond (c.withHooks H) = cond c`, `rfl`
for `frameOK` and `guardOK`: `frameOK_withHooks`, `guardOK_withHooks`) gives the kind for every
interpretation H of the parameters: one decision, `allExcept (cond c)`, covers every
`c.withHooks H`, whose rules are c's. -/

/-- `allExcept` of a condition that does not read `hooks` is the same decision for every
interpretation. -/
theorem allExcept_withHooks {c : Semantics} {cond : Semantics → Rule → Bool} {H : HookParams}
    (hc : ∀ r, cond (c.withHooks H) r = cond c r) (obl : List Nat) (i : Nat) :
    allExcept (cond (c.withHooks H)) obl i (c.withHooks H).rules = allExcept (cond c) obl i c.rules := by
  rw [funext hc]; rfl

/-- **The invariant kind, for an interpretation H of the parameters**: `stepsKind (c.withHooks H) P`
indexed by the data's rules (the same list). -/
@[reducible] def stepsKindAll (c : Semantics) (H : HookParams) (P : GroundTerm → GroundTerm → Prop) : Kind :=
  Kind.ofList c.rules (fun r => RuleSteps (c.withHooks H) r P)
    (∀ x y : Config (c.withHooks H), Step (c.withHooks H) x y → P x.val y.val) (steps_of_rules (c := c.withHooks H))

/-- The decider of `stepsKindAll c H P` from a condition decided on the data that does not read
`hooks` (`hcond`) and gives P for each step of a rule under every interpretation (`sound`). -/
def stepsDecider {c : Semantics} {P : GroundTerm → GroundTerm → Prop} {cond : Semantics → Rule → Bool}
    (hcond : ∀ H r, cond (c.withHooks H) r = cond c r)
    (sound : ∀ H r, cond (c.withHooks H) r = true → RuleSteps (c.withHooks H) r P) (H : HookParams) :
    (stepsKindAll c H P).Decider :=
  Kind.listDecider (cond c) fun r _ h => sound H r ((hcond H r).trans h)

/-- **The generic theorem, for every interpretation of the parameters.** A condition that does not
read `hooks` (`hcond`) and gives P for each step of a rule under every interpretation (`sound`),
decided once on the data except at the rules listed in `obl`, gives P for every step of
`c.withHooks H` whose listed rules are obligations proved under H. -/
theorem steps_of_all {c : Semantics} {P : GroundTerm → GroundTerm → Prop} {cond : Semantics → Rule → Bool}
    (hcond : ∀ H r, cond (c.withHooks H) r = cond c r)
    (sound : ∀ H r, cond (c.withHooks H) r = true → RuleSteps (c.withHooks H) r P) {obl : List Nat}
    (h : allExcept (cond c) obl 0 c.rules = true) (H : HookParams)
    (ho : ∀ i ∈ obl, ∀ r, c.rules[i]? = some r → RuleSteps (c.withHooks H) r P) :
    ∀ x y : Config (c.withHooks H), Step (c.withHooks H) x y → P x.val y.val :=
  Kind.of_decided (stepsKindAll c H P) (stepsDecider hcond sound H) obl (decides_of_allExcept h) ho

/-- **The step half of an invariant, for every interpretation of the parameters** (`steps_of_all`
at `P x y := Inv' x → Inv' y`). -/
theorem invariant_of_steps_all {c : Semantics} {Inv' : GroundTerm → Prop} {cond : Semantics → Rule → Bool}
    (hcond : ∀ H r, cond (c.withHooks H) r = cond c r)
    (sound : ∀ H r, cond (c.withHooks H) r = true → RuleSteps (c.withHooks H) r (fun x y => Inv' x → Inv' y))
    {obl : List Nat} (h : allExcept (cond c) obl 0 c.rules = true) (H : HookParams)
    (ho : ∀ i ∈ obl, ∀ r, c.rules[i]? = some r → RuleSteps (c.withHooks H) r (fun x y => Inv' x → Inv' y)) :
    ∀ x y : Config (c.withHooks H), Inv' x.val → Step (c.withHooks H) x y → Inv' y.val :=
  fun x y hx hs => steps_of_all hcond sound h H ho x y hs hx

/-! ## Following a path through a match and an evaluation -/

variable {c : Semantics} {σ : Subst}

theorem PatVal.dv_inv {s : Srt} {l : Lit} {v : GroundTerm} (h : PatVal c σ (.dv s l) v) :
    v = .dv s l := by
  generalize ht : Term.dv s l = t at h
  cases h with
  | dv => cases ht; rfl
  | _ => cases ht

theorem PatVal.args_inv {f : Sym} {ps : List Term} {v : GroundTerm} (h : PatVal c σ (.app f ps) v) :
    ∃ vs, PatVals c σ ps vs := by
  generalize ht : Term.app f ps = t at h
  cases h with
  | ctor _ hs => cases ht; exact ⟨_, hs⟩
  | hook _ hs _ => cases ht; exact ⟨_, hs⟩
  | coll _ _ hs _ => cases ht; exact ⟨_, hs⟩
  | ovl _ _ hs _ => cases ht; exact ⟨_, hs⟩
  | _ => cases ht

theorem EvalTerm.dv_inv {s : Srt} {l : Lit} {r : Option GroundTerm} (h : EvalTerm c σ (.dv s l) r) :
    r = some (.dv s l) := by
  generalize ht : Term.dv s l = t at h
  cases h with
  | dv => cases ht; rfl
  | _ => cases ht

theorem PatVals.get : ∀ {ps : List Term} {vs : List GroundTerm}, PatVals c σ ps vs →
    vs.length = ps.length ∧ ∀ (i : Nat) (p : Term), ps[i]? = some p → ∃ v, vs[i]? = some v ∧ PatVal c σ p v
  | [], _, h => by cases h; exact ⟨rfl, fun _ _ h => nomatch h⟩
  | _ :: _, _, h => by
    cases h with
    | cons h hs =>
      obtain ⟨hl, hg⟩ := PatVals.get hs
      refine ⟨by simp [hl], fun i p hp => ?_⟩
      cases i with
      | zero => cases hp; exact ⟨_, rfl, h⟩
      | succ i => exact hg i p hp

theorem EvalTerms.get : ∀ {ts : List Term} {rs : List (Option GroundTerm)}, EvalTerms c σ ts rs →
    rs.length = ts.length ∧ ∀ (i : Nat) (t : Term), ts[i]? = some t → ∃ r, rs[i]? = some r ∧ EvalTerm c σ t r
  | [], _, h => by cases h; exact ⟨rfl, fun _ _ h => nomatch h⟩
  | _ :: _, _, h => by
    cases h with
    | cons h hs =>
      obtain ⟨hl, hg⟩ := EvalTerms.get hs
      refine ⟨by simp [hl], fun i t ht => ?_⟩
      cases i with
      | zero => cases ht; exact ⟨_, rfl, h⟩
      | succ i => exact hg i t ht

theorem allSome_get : ∀ {rs : List (Option GroundTerm)} {ws : List GroundTerm}, allSome rs = some ws →
    ws.length = rs.length ∧ ∀ (i : Nat) (r : Option GroundTerm), rs[i]? = some r → ∃ w, r = some w ∧ ws[i]? = some w
  | [], ws, h => by
    simp only [allSome, Option.some.injEq] at h
    subst h; exact ⟨rfl, fun _ _ h => nomatch h⟩
  | r :: rs, ws, h => by
    cases r with
    | none => simp [allSome] at h
    | some w =>
      simp only [allSome, Option.bind_some] at h
      cases hr : allSome rs with
      | none => rw [hr] at h; cases h
      | some ws' =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨hl, hg⟩ := allSome_get hr
        refine ⟨by simp [hl], fun i r' hr' => ?_⟩
        cases i with
        | zero => cases hr'; exact ⟨w, rfl, rfl⟩
        | succ i => exact hg i r' hr'

/-- A `ctorHeaded` pattern's value is not an injection, so an injection of it is not normalized. -/
theorem PatVal.injNormal_of {a b : Srt} {t : Term} {w : GroundTerm} (ht : ctorHeaded c t = true)
    (h : PatVal c σ t w) : injNormal a b w = .inj a b w := by
  cases t with
  | app f ps =>
    simp only [ctorHeaded, Bool.and_eq_true, Bool.not_eq_true'] at ht
    obtain ⟨_, vs, rfl, _⟩ := PatVal.app_inv ht.2 h ht.1
    rfl
  | dv s l => rw [PatVal.dv_inv h]; rfl
  | _ => simp [ctorHeaded] at ht

theorem EvalTerm.injNormal_of {a b : Srt} {t : Term} {w : GroundTerm} (ht : ctorHeaded c t = true)
    (h : EvalTerm c σ t (some w)) : injNormal a b w = .inj a b w := by
  cases t with
  | app f ts =>
    simp only [ctorHeaded, Bool.and_eq_true, Bool.not_eq_true'] at ht
    obtain ⟨rs, _, hr⟩ := EvalTerm.ctor_inv ht.1 h
    cases ha : allSome rs with
    | none => rw [ha] at hr; cases hr
    | some ws => rw [ha] at hr; cases hr; rfl
  | dv s l => cases EvalTerm.dv_inv h; rfl
  | _ => simp [ctorHeaded] at ht

/-- The subterm of a left-hand side at a path denotes the matched value's subterm there. -/
theorem PatVal.atPath : ∀ (p : Path) {t t' : Term} {x : GroundTerm}, PatVal c σ t x →
    Term.atPath c p t = some t' → ∃ x', x.atPath p = some x' ∧ PatVal c σ t' x'
  | [], _, _, x, h, ht => by cases ht; exact ⟨x, rfl, h⟩
  | .arg f n i :: p, t, t', x, h, ht => by
    cases t with
    | app g ts =>
      simp only [Term.atPath] at ht
      split at ht
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
        obtain ⟨⟨⟨rfl, hn⟩, hct⟩, hph⟩ := hc
        obtain ⟨_, vs, rfl, hs⟩ := PatVal.app_inv hph h hct
        obtain ⟨ti, hti, ht'⟩ := Option.bind_eq_some_iff.mp ht
        obtain ⟨hl, hg⟩ := PatVals.get hs
        obtain ⟨vi, hvi, hpi⟩ := hg i ti hti
        obtain ⟨x', hx', hp'⟩ := PatVal.atPath p hpi ht'
        refine ⟨x', ?_, hp'⟩
        simp only [GroundTerm.atPath, beq_self_eq_true, hl, hn, Bool.and_self, ↓reduceIte, hvi,
          Option.bind_some, hx']
      · cases ht
    | _ => simp [Term.atPath] at ht
  | .inj b :: p, t, t', x, h, ht => by
    cases t with
    | inj a b' t₁ =>
      simp only [Term.atPath] at ht
      split at ht
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨rfl, hch⟩ := hc
        obtain ⟨w, hw, rfl⟩ := PatVal.inj_inv h
        rw [PatVal.injNormal_of hch hw]
        obtain ⟨x', hx', hp'⟩ := PatVal.atPath p hw ht
        exact ⟨x', by simp [GroundTerm.atPath, hx'], hp'⟩
      · cases ht
    | _ => simp [Term.atPath] at ht

/-- The subterm of a right-hand side at a path evaluates to the result's subterm there. -/
theorem EvalTerm.atPath : ∀ (p : Path) {t t' : Term} {y : GroundTerm}, EvalTerm c σ t (some y) →
    Term.atPath c p t = some t' → ∃ y', y.atPath p = some y' ∧ EvalTerm c σ t' (some y')
  | [], _, _, y, h, ht => by cases ht; exact ⟨y, rfl, h⟩
  | .arg f n i :: p, t, t', y, h, ht => by
    cases t with
    | app g ts =>
      simp only [Term.atPath] at ht
      split at ht
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
        obtain ⟨⟨⟨rfl, hn⟩, hct⟩, _⟩ := hc
        obtain ⟨rs, hts, hr⟩ := EvalTerm.ctor_inv hct h
        cases ha : allSome rs with
        | none => rw [ha] at hr; cases hr
        | some ws =>
          rw [ha] at hr
          cases hr
          obtain ⟨ti, hti, ht'⟩ := Option.bind_eq_some_iff.mp ht
          obtain ⟨hl, hg⟩ := EvalTerms.get hts
          obtain ⟨hl', hg'⟩ := allSome_get ha
          obtain ⟨ri, hri, hei⟩ := hg i ti hti
          obtain ⟨wi, rfl, hwi⟩ := hg' i ri hri
          obtain ⟨y', hy', he'⟩ := EvalTerm.atPath p hei ht'
          refine ⟨y', ?_, he'⟩
          simp only [GroundTerm.atPath, beq_self_eq_true, hl', hl, hn, Bool.and_self, ↓reduceIte,
            hwi, Option.bind_some, hy']
      · cases ht
    | _ => simp [Term.atPath] at ht
  | .inj b :: p, t, t', y, h, ht => by
    cases t with
    | inj a b' t₁ =>
      simp only [Term.atPath] at ht
      split at ht
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨rfl, hch⟩ := hc
        obtain ⟨r', hr', hy⟩ := EvalTerm.inj_inv h
        cases r' with
        | none => cases hy
        | some w =>
          cases hy
          rw [EvalTerm.injNormal_of hch hr']
          obtain ⟨y', hy', he'⟩ := EvalTerm.atPath p hr' ht
          exact ⟨y', by simp [GroundTerm.atPath, hy'], he'⟩
      · cases ht
    | _ => simp [Term.atPath] at ht

/-! ## Pinned values are the values -/

mutual
  theorem closedVal_pat : ∀ (p : Term) {v g : GroundTerm}, PatVal c σ p v → closedVal c p = some g → v = g
    | .dv s l, v, g, h, hg => by
      rw [PatVal.dv_inv h]; simp only [closedVal, Option.some.injEq] at hg; exact hg
    | .app f ps, v, g, h, hg => by
      simp only [closedVal] at hg
      split at hg
      · next hc =>
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        obtain ⟨_, vs, rfl, hs⟩ := PatVal.app_inv hc.2 h hc.1
        obtain ⟨gs, hgs, rfl⟩ := Option.map_eq_some_iff.mp hg
        rw [closedVals_pat ps hs hgs]
      · cases hg
    | .inj a b p, v, g, h, hg => by
      obtain ⟨w, hw, rfl⟩ := PatVal.inj_inv h
      obtain ⟨g', hg', rfl⟩ := Option.map_eq_some_iff.mp hg
      rw [closedVal_pat p hw hg']
    | .var _, _, _, _, hg => by simp [closedVal] at hg
    | .as .., _, _, _, hg => by simp [closedVal] at hg
    termination_by structural p => p
  theorem closedVals_pat : ∀ (ps : List Term) {vs gs : List GroundTerm}, PatVals c σ ps vs →
      closedVals c ps = some gs → vs = gs
    | [], vs, gs, h, hg => by
      rw [PatVals.nil_inv h]; simp only [closedVals, Option.some.injEq] at hg; exact hg
    | p :: ps, vs, gs, h, hg => by
      obtain ⟨v, vs', rfl, hp, hps⟩ := PatVals.cons_inv h
      simp only [closedVals] at hg
      split at hg
      · next g gs' h₁ h₂ =>
        cases hg
        rw [closedVal_pat p hp h₁, closedVals_pat ps hps h₂]
      · cases hg
    termination_by structural ps => ps
end

mutual
  theorem asPin_pat (i : Nat) : ∀ (t : Term) {x g : GroundTerm}, PatVal c σ t x → asPin c i t = some g →
      σ.lookup i = some g
    | .as p j, x, g, h, hg => by
      obtain ⟨hp, hj⟩ := PatVal.as_inv h
      simp only [asPin] at hg
      split at hg
      · next hji =>
        split at hg
        · next g' hcv =>
          cases hg
          rw [beq_iff_eq] at hji
          subst hji
          rw [hj, closedVal_pat p hp hcv]
        · exact asPin_pat i p hp hg
      · exact asPin_pat i p hp hg
    | .app f ps, x, g, h, hg => by
      obtain ⟨vs, hs⟩ := PatVal.args_inv h
      exact asPins_pat i ps hs hg
    | .inj a b p, x, g, h, hg => by
      obtain ⟨w, hw, -⟩ := PatVal.inj_inv h
      exact asPin_pat i p hw hg
    | .var _, _, _, _, hg => by simp [asPin] at hg
    | .dv .., _, _, _, hg => by simp [asPin] at hg
    termination_by structural t => t
  theorem asPins_pat (i : Nat) : ∀ (ps : List Term) {vs : List GroundTerm} {g : GroundTerm},
      PatVals c σ ps vs → asPins c i ps = some g → σ.lookup i = some g
    | [], _, _, _, hg => by simp [asPins] at hg
    | p :: ps, vs, g, h, hg => by
      obtain ⟨v, vs', rfl, hp, hps⟩ := PatVals.cons_inv h
      simp only [asPins] at hg
      split at hg
      · next g' h₁ => cases hg; exact asPin_pat i p hp h₁
      · exact asPins_pat i ps hps hg
    termination_by structural ps => ps
end

mutual
  theorem pin_eval {lhs : Term} {x : GroundTerm} (hm : PatVal c σ lhs x) :
      ∀ (t : Term) {y g : GroundTerm}, EvalTerm c σ t (some y) → pin c lhs t = some g → y = g
    | .var i, y, g, h, hg => by
      have h' := EvalTerm.var_inv h
      simp only [pin] at hg
      rw [asPin_pat i lhs hm hg] at h'
      exact Option.some.inj h'
    | .dv s l, y, g, h, hg => by
      have h' := EvalTerm.dv_inv h
      simp only [pin, Option.some.injEq] at hg
      rw [← hg]; exact Option.some.inj h'
    | .app f ts, y, g, h, hg => by
      simp only [pin] at hg
      split at hg
      · next hc =>
        obtain ⟨rs, hts, hr⟩ := EvalTerm.ctor_inv hc h
        obtain ⟨gs, hgs, rfl⟩ := Option.map_eq_some_iff.mp hg
        cases ha : allSome rs with
        | none => rw [ha] at hr; cases hr
        | some ws =>
          rw [ha] at hr
          cases hr
          rw [pins_eval hm ts hts ha hgs]
      · cases hg
    | .inj a b t, y, g, h, hg => by
      obtain ⟨r', hr', hy⟩ := EvalTerm.inj_inv h
      obtain ⟨g', hg', rfl⟩ := Option.map_eq_some_iff.mp hg
      cases r' with
      | none => cases hy
      | some w =>
        cases hy
        rw [pin_eval hm t hr' hg']
    | .as .., _, _, _, hg => by simp [pin] at hg
    termination_by structural t => t
  theorem pins_eval {lhs : Term} {x : GroundTerm} (hm : PatVal c σ lhs x) :
      ∀ (ts : List Term) {rs : List (Option GroundTerm)} {ws gs : List GroundTerm},
      EvalTerms c σ ts rs → allSome rs = some ws → pins c lhs ts = some gs → ws = gs
    | [], rs, ws, gs, h, ha, hg => by
      rw [EvalTerms.nil_inv h] at ha
      simp only [allSome, Option.some.injEq] at ha
      simp only [pins, Option.some.injEq] at hg
      rw [← ha, ← hg]
    | t :: ts, rs, ws, gs, h, ha, hg => by
      obtain ⟨r, rs', rfl, ht, hts⟩ := EvalTerms.cons_inv h
      simp only [pins] at hg
      split at hg
      · next g gs' h₁ h₂ =>
        cases hg
        cases r with
        | none => simp [allSome] at ha
        | some w =>
          simp only [allSome, Option.bind_some] at ha
          cases ha' : allSome rs' with
          | none => rw [ha'] at ha; cases ha
          | some ws' =>
            rw [ha'] at ha
            simp only [Option.map_some, Option.some.injEq] at ha
            subst ha
            rw [pin_eval hm t ht h₁, pins_eval hm ts hts ha' h₂]
      · cases hg
    termination_by structural ts => ts
end

/-! ## Frame: a position every step keeps -/

/-- The subterm at p is the same before and after the step. -/
def Frame (p : Path) (x y : GroundTerm) : Prop := y.atPath p = x.atPath p

/-- Rule r keeps the subterm at p: the left-hand side binds a variable there that the right-hand
side has there. -/
def frameOK (c : Semantics) (p : Path) (r : Rule) : Bool :=
  match Term.atPath c p r.lhs, Term.atPath c p r.rhs with
  | some (.var j), some (.var j') => j == j'
  | some (.as _ j), some (.var j') => j == j'
  | _, _ => false

theorem frame_sound (p : Path) (r : Rule) (h : frameOK c p r = true) : RuleSteps c r (Frame p) := by
  intro σ x y _ hm _ he
  unfold frameOK at h
  split at h
  · next j j' hl hr =>
    obtain ⟨x', hx, hx'⟩ := PatVal.atPath p hm hl
    obtain ⟨y', hy, hy'⟩ := EvalTerm.atPath p he hr
    rw [beq_iff_eq] at h; subst h
    have e₁ := PatVal.var_inv hx'
    have e₂ := EvalTerm.var_inv hy'
    rw [e₁] at e₂
    unfold Frame
    rw [hx, hy, e₂]
  · next q j j' hl hr =>
    obtain ⟨x', hx, hx'⟩ := PatVal.atPath p hm hl
    obtain ⟨y', hy, hy'⟩ := EvalTerm.atPath p he hr
    rw [beq_iff_eq] at h; subst h
    have e₁ := (PatVal.as_inv hx').2
    have e₂ := EvalTerm.var_inv hy'
    rw [e₁] at e₂
    unfold Frame
    rw [hx, hy, e₂]
  · cases h

/-- A rule that keeps the subterm at p keeps every property of that subterm. -/
theorem frame_inv_sound (p : Path) (Q : Option GroundTerm → Prop) (r : Rule) (h : frameOK c p r = true) :
    RuleSteps c r (fun x y => Q (x.atPath p) → Q (y.atPath p)) :=
  (frame_sound p r h).mono fun _ _ hf hq => by unfold Frame at hf; rw [hf]; exact hq

/-! ## Guard: what a step leaves at a position -/

/-- After the step, if the subterm at `path` has the constructor `head`, its subterm at `sub` is
`val`. -/
structure Guard where
  path : Path
  head : Sym
  sub : Path
  val : GroundTerm

def Guard.Holds (g : Guard) (y : GroundTerm) : Prop :=
  ∀ w, y.atPath g.path = some w → w.headSym = some g.head → w.atPath g.sub = some g.val

/-- Rule r leaves `g` holding: its right-hand side at `g.path` is a constructor term of another
head, an injection or a literal; or of the head, with its subterm at `g.sub` pinned to `g.val`. -/
def guardOK (c : Semantics) (g : Guard) (r : Rule) : Bool :=
  match Term.atPath c g.path r.rhs with
  | some (.app f ts) =>
    c.isCtor f && (f != g.head ||
      match Term.atPath c g.sub (.app f ts) with
      | some t => match pin c r.lhs t with
        | some v => GroundTerm.cmp v g.val == .eq
        | none => false
      | none => false)
  | some (.inj ..) => true
  | some (.dv ..) => true
  | _ => false

theorem guard_sound (g : Guard) (r : Rule) (h : guardOK c g r = true) :
    RuleSteps c r (fun _ y => g.Holds y) := by
  intro σ x y _ hm _ he w hw hhead
  unfold guardOK at h
  split at h
  · next f ts hp =>
    obtain ⟨y', hy, hy'⟩ := EvalTerm.atPath g.path he hp
    rw [hw] at hy; cases hy
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨hc, h⟩ := h
    obtain ⟨rs, hts, hr⟩ := EvalTerm.ctor_inv hc hy'
    cases ha : allSome rs with
    | none => rw [ha] at hr; cases hr
    | some ws =>
      rw [ha] at hr
      cases hr
      simp only [GroundTerm.headSym, Option.some.injEq] at hhead
      rcases h with hne | h
      · exact absurd hhead hne
      · split at h
        · next t hsub =>
          split at h
          · next v hv =>
            have hv' := GroundTerm.cmp_eq v g.val (by simpa using h)
            obtain ⟨y'', hy'', he''⟩ := EvalTerm.atPath g.sub hy' hsub
            rw [hy'', pin_eval hm t he'' hv, hv']
          · cases h
        · cases h
  · next a b t hp =>
    obtain ⟨y', hy, hy'⟩ := EvalTerm.atPath g.path he hp
    rw [hw] at hy; cases hy
    obtain ⟨r', _, hr⟩ := EvalTerm.inj_inv hy'
    cases r' with
    | none => cases hr
    | some u =>
      cases hr
      cases u <;> simp [injNormal, GroundTerm.headSym] at hhead
  · next s l hp =>
    obtain ⟨y', hy, hy'⟩ := EvalTerm.atPath g.path he hp
    rw [hw] at hy; cases hy
    cases EvalTerm.dv_inv hy'
    simp [GroundTerm.headSym] at hhead
  · cases h

/-- A rule that leaves `g` holding after each of its steps keeps `g.Holds`. -/
theorem guard_inv_sound (g : Guard) (r : Rule) (h : guardOK c g r = true) :
    RuleSteps c r (fun x y => g.Holds x → g.Holds y) :=
  (guard_sound g r h).mono fun _ _ hy _ => hy

/-! ## The conditions do not read the interpretation of the parameters

Each equation is `rfl` for a variable `c`, checked by the kernel (`kernel_rfl`, Params.lean). -/

kernel_rfl Term.atPath_withHooks : ∀ (c : Semantics) (H : HookParams) (p : Path) (t : Term),
  Term.atPath (c.withHooks H) p t = Term.atPath c p t
kernel_rfl pin_withHooks : ∀ (c : Semantics) (H : HookParams) (lhs t : Term),
  pin (c.withHooks H) lhs t = pin c lhs t
kernel_rfl frameOK_withHooks : ∀ (c : Semantics) (H : HookParams) (p : Path) (r : Rule),
  frameOK (c.withHooks H) p r = frameOK c p r
kernel_rfl guardOK_withHooks : ∀ (c : Semantics) (H : HookParams) (g : Guard) (r : Rule),
  guardOK (c.withHooks H) g r = guardOK c g r

end KCore
