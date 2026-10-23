import KPrelude.RelAttr
import KPrelude.Coll
import KPrelude.InvColl
import KPrelude.Tactic
import KPrelude.Run

/-!
# Relating two generated libraries

Generic parts of `k2lean relate`, which translates the terms of one generated library `A` into
another `B` (`tr`, a symbol renaming) and states that the two `Step` relations are bisimilar.

- `Bisimulation`: a strong bisimulation between two relations, and what it transfers
  (reachability, terminal states).
- Maps translated pointwise: a pointwise translation of a sorted association list is the
  translation of the map when it preserves the order of the keys involved. Canonical maps are
  sorted by each library's own order on keys, and two independently generated libraries order
  constructors differently, so order preservation is a real hypothesis (`PresOn`).
- `k2l_inv`: inverts hypotheses `tr x = e` by case analysis on `x`.
-/

namespace KPrelude

/-! ## Bisimulation -/

/-- `R` is a strong bisimulation between `S₁` and `S₂`. -/
structure Bisimulation {α β : Type} (S₁ : α → α → Prop) (S₂ : β → β → Prop) (R : α → β → Prop) : Prop where
  fwd : ∀ {a b a'}, R a b → S₁ a a' → ∃ b', S₂ b b' ∧ R a' b'
  bwd : ∀ {a b b'}, R a b → S₂ b b' → ∃ a', S₁ a a' ∧ R a' b'

namespace Bisimulation

variable {α β : Type} {S₁ : α → α → Prop} {S₂ : β → β → Prop} {R : α → β → Prop}

theorem stepsN_fwd (h : Bisimulation S₁ S₂ R) :
    ∀ {n a b a'}, R a b → StepsN S₁ n a a' → ∃ b', StepsN S₂ n b b' ∧ R a' b'
  | _, _, b, _, hr, .refl _ => ⟨b, .refl _, hr⟩
  | _, _, _, _, hr, .step hs rest => by
    obtain ⟨b₁, hb₁, hr₁⟩ := h.fwd hr hs
    obtain ⟨b', hb', hr'⟩ := h.stepsN_fwd hr₁ rest
    exact ⟨b', .step hb₁ hb', hr'⟩

theorem stepsN_bwd (h : Bisimulation S₁ S₂ R) :
    ∀ {n a b b'}, R a b → StepsN S₂ n b b' → ∃ a', StepsN S₁ n a a' ∧ R a' b'
  | _, a, _, _, hr, .refl _ => ⟨a, .refl _, hr⟩
  | _, _, _, _, hr, .step hs rest => by
    obtain ⟨a₁, ha₁, hr₁⟩ := h.bwd hr hs
    obtain ⟨a', ha', hr'⟩ := h.stepsN_bwd hr₁ rest
    exact ⟨a', .step ha₁ ha', hr'⟩

/-- Related states are terminal (have no successor) together. -/
theorem terminal_iff (h : Bisimulation S₁ S₂ R) {a b} (hr : R a b) :
    (∀ a', ¬ S₁ a a') ↔ (∀ b', ¬ S₂ b b') := by
  constructor
  · intro ha b' hb
    obtain ⟨a', ha', _⟩ := h.bwd hr hb
    exact ha a' ha'
  · intro hb a' ha
    obtain ⟨b', hb', _⟩ := h.fwd hr ha
    exact hb b' hb'

end Bisimulation

/-! ## Sorted association lists under a pointwise translation -/

namespace SAL

set_option linter.unusedSectionVars false

variable {α α' β β' : Type} [Ord α] [Ord α']

/-- The pointwise translation of an association list. -/
def mapPairs (f : α → α') (g : β → β') (l : List (α × β)) : List (α' × β') :=
  l.map (fun p => (f p.1, g p.2))

@[simp] theorem mapPairs_nil (f : α → α') (g : β → β') : mapPairs f g [] = [] := rfl
@[simp] theorem mapPairs_cons (f : α → α') (g : β → β') (k : α) (v : β) (t : List (α × β)) :
    mapPairs f g ((k, v) :: t) = (f k, g v) :: mapPairs f g t := rfl

/-- `f` preserves the order on the keys that satisfy `P`. -/
def PresOn (P : α → Prop) (f : α → α') : Prop :=
  ∀ a b, P a → P b → compare (f a) (f b) = compare a b

variable {P : α → Prop} {f : α → α'} {g : β → β'}

theorem insert_mapPairs (hf : PresOn P f) {k : α} (hk : P k) (v : β) :
    ∀ {l : List (α × β)}, (∀ p ∈ l, P p.1) →
      insert (f k) (g v) (mapPairs f g l) = mapPairs f g (insert k v l)
  | [], _ => rfl
  | (k', v') :: t, hl => by
    have hk' : P k' := hl (k', v') (by simp)
    have ht : ∀ p ∈ t, P p.1 := fun p hp => hl p (by simp [hp])
    simp only [mapPairs_cons, insert, hf k k' hk hk']
    split <;> simp [insert_mapPairs hf hk v ht]

theorem lookup_mapPairs (hf : PresOn P f) {k : α} (hk : P k) :
    ∀ {l : List (α × β)}, (∀ p ∈ l, P p.1) → lookup (f k) (mapPairs f g l) = (lookup k l).map g
  | [], _ => rfl
  | (k', v') :: t, hl => by
    have hk' : P k' := hl (k', v') (by simp)
    have ht : ∀ p ∈ t, P p.1 := fun p hp => hl p (by simp [hp])
    simp only [mapPairs_cons, lookup, hf k k' hk hk']
    split <;> simp [lookup_mapPairs hf hk ht]

theorem erase_mapPairs (hf : PresOn P f) {k : α} (hk : P k) :
    ∀ {l : List (α × β)}, (∀ p ∈ l, P p.1) → erase (f k) (mapPairs f g l) = mapPairs f g (erase k l)
  | [], _ => rfl
  | (k', v') :: t, hl => by
    have hk' : P k' := hl (k', v') (by simp)
    have ht : ∀ p ∈ t, P p.1 := fun p hp => hl p (by simp [hp])
    simp only [mapPairs_cons, erase, hf k k' hk hk']
    split <;> simp [erase_mapPairs hf hk ht]

theorem mem_mapPairs {p : α' × β'} {l : List (α × β)} :
    p ∈ mapPairs f g l ↔ ∃ q ∈ l, p = (f q.1, g q.2) := by
  simp only [mapPairs, List.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩

theorem sorted_mapPairs_iff (hf : PresOn P f) :
    ∀ {l : List (α × β)}, (∀ p ∈ l, P p.1) → (Sorted (mapPairs f g l) ↔ Sorted l)
  | [], _ => by simp [Sorted.nil]
  | (k, v) :: t, hl => by
    have hk : P k := hl (k, v) (by simp)
    have ht : ∀ p ∈ t, P p.1 := fun p hp => hl p (by simp [hp])
    simp only [mapPairs_cons]
    constructor
    · intro h
      cases h with
      | cons hlt hs =>
        refine Sorted.cons (fun q hq => ?_) ((sorted_mapPairs_iff hf ht).1 hs)
        have := hlt (f q.1, g q.2) (mem_mapPairs.2 ⟨q, hq, rfl⟩)
        rwa [hf k q.1 hk (ht q hq)] at this
    · intro h
      cases h with
      | cons hlt hs =>
        refine Sorted.cons (fun q hq => ?_) ((sorted_mapPairs_iff hf ht).2 hs)
        obtain ⟨q', hq', rfl⟩ := mem_mapPairs.1 hq
        show compare (f k) (f q'.1) = .lt
        rw [hf k q'.1 hk (ht q' hq')]; exact hlt q' hq'

section Laws

variable [Std.TransOrd α] [Std.LawfulEqOrd α] [Std.TransOrd α'] [Std.LawfulEqOrd α']

/-- The map pattern `k |-> v REST` is preserved by an order-preserving translation. -/
theorem concat_singleton_mapPairs (hf : PresOn P f) {k : α} {v : β} {r m : List (α × β)}
    (hk : P k) (hm : ∀ p ∈ m, P p.1) (h : concat [(k, v)] r = some m) :
    concat [(f k, g v)] (mapPairs f g r) = some (mapPairs f g m) := by
  obtain ⟨hs, hn, rfl⟩ := concat_singleton_iff.1 h
  have hr : ∀ p ∈ r, P p.1 := by
    intro p hp
    apply hm
    rw [← erase_insert_of_lookup_none hs hn (v := v)] at hp
    exact mem_erase hp
  refine concat_singleton_iff.2 ⟨(sorted_mapPairs_iff hf hr).2 hs, ?_, (insert_mapPairs hf hk v hr).symm⟩
  rw [lookup_mapPairs hf hk hr, hn]; rfl

/-- The inverse direction: a match of `f k |-> v' REST'` on a translated map comes from a match
on the map. -/
theorem concat_singleton_mapPairs_inv (hf : PresOn P f) {k : α} {v' : β'} {r' : List (α' × β')}
    {m : List (α × β)} (hk : P k) (hm : ∀ p ∈ m, P p.1)
    (h : concat [(f k, v')] r' = some (mapPairs f g m)) :
    ∃ v r, v' = g v ∧ r' = mapPairs f g r ∧ concat [(k, v)] r = some m := by
  have hl := lookup_of_concat_singleton h
  rw [lookup_mapPairs hf hk hm] at hl
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 hl
  obtain ⟨hs', hn', he⟩ := concat_singleton_iff.1 h
  have hsm : Sorted m := (sorted_mapPairs_iff hf hm).1 (he ▸ sorted_insert hs')
  refine ⟨v, erase k m, rfl, ?_, concat_singleton_erase hsm hv⟩
  rw [← erase_mapPairs hf hk hm, he, erase_insert_of_lookup_none hs' hn']

end Laws

end SAL

/-! ## Maps of two libraries related by a pointwise translation `T` -/

namespace MapHook

open ListIso

set_option linter.unusedSectionVars false

variable {M K V M' K' V' : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V]
  [Ord K'] [ListIso M' (K' × V')] [MapRepr M' K' V']
  {P : K → Prop} {f : K → K'} {g : V → V'} {T : M → M'}

/-- `T` translates a map pointwise, with `f` on keys and `g` on values. -/
def Pointwise (f : K → K') (g : V → V') (T : M → M') : Prop :=
  ∀ m, toList (T m) = SAL.mapPairs f g (toList m)

theorem pointwise_ofList (hT : Pointwise f g T) (l : List (K × V)) :
    T (ofList l) = ofList (SAL.mapPairs f g l) := by
  have := hT (ofList l)
  rw [toList_ofList] at this
  rw [← this, ofList_toList]

theorem update_pointwise (hT : Pointwise f g T) (hf : SAL.PresOn P f) {m : M} {k : K} (v : V)
    (hm : KeysOn P m) (hk : P k) : update (T m) (f k) (g v) = T (update m k v) := by
  rw [update_def, update_def, hT, SAL.insert_mapPairs hf hk v hm, pointwise_ofList hT]

variable [Std.TransOrd K] [Std.LawfulEqOrd K] [Std.TransOrd K'] [Std.LawfulEqOrd K']


theorem concat_element_pointwise (hT : Pointwise f g T) (hf : SAL.PresOn P f) {k : K} {v : V} {r m : M}
    (hk : P k) (hm : KeysOn P m) (h : concat (element k v) r = some m) :
    concat (element (f k) (g v)) (T r) = some (T m) := by
  unfold concat element at *
  rw [toList_ofList] at *
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨l, hl, hlm⟩ := h
  have hl' : l = toList m := by rw [← hlm, toList_ofList]
  subst hl'
  rw [hT, SAL.concat_singleton_mapPairs hf hk hm hl]
  simp only [Option.map_some]
  rw [← hT m, ofList_toList]

theorem concat_element_pointwise_inv (hT : Pointwise f g T) (hf : SAL.PresOn P f) {k : K} {v' : V'}
    {r' : M'} {m : M} (hk : P k) (hm : KeysOn P m)
    (h : concat (element (f k) v') r' = some (T m)) :
    ∃ v r, v' = g v ∧ r' = T r ∧ concat (element k v) r = some m := by
  unfold concat element at h
  rw [toList_ofList] at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨l, hl, hlm⟩ := h
  have hl' : l = toList (T m) := by rw [← hlm, toList_ofList]
  subst hl'
  rw [hT] at hl
  obtain ⟨v, r, rfl, hr, hc⟩ := SAL.concat_singleton_mapPairs_inv hf hk hm hl
  refine ⟨v, ofList r, rfl, ?_, ?_⟩
  · rw [pointwise_ofList hT, ← hr, ofList_toList]
  · unfold concat element; rw [toList_ofList, toList_ofList, hc]; simp [ofList_toList]

end MapHook

/-! ## Inverting a translation -/

open Lean Meta Elab Tactic in
/-- `k2l_inv`: repeatedly (1) substitute variables, (2) split conjunctions, (3) for a hypothesis
`h : e = f x` (or `f x = e`) where `f` is a translation function (its name has a component
starting with `tr_`), `x` a local variable and `e` not a variable, case on `x` and simplify `h`
with `f`'s equations: constructor clashes close the goal, matching constructors give equations
between the arguments. Terminates because `e` gets smaller. -/
partial def k2lInvLoop (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| try subst_vars))
  k2lAndsLoop 64
  evalTactic (← `(tactic| try subst_vars))
  if (← getGoals).isEmpty then return
  let isTr (e : Expr) : Option (Name × Expr) :=
    match e.getAppFn with
    | .const n _ =>
      if (n.components.getLast?.map (fun c => c.toString.startsWith "tr_")).getD false then
        (e.getAppArgs.back?).map (fun x => (n, x))
      else none
    | _ => none
  let found ← withMainContext do
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let some (_, l, r) := ty.eq? | continue
      let cand := match isTr r, isTr l with
        | some t, _ => if l.isFVar then none else some t
        | none, some t => if r.isFVar then none else some t
        | none, none => none
      let some (fn, x) := cand | continue
      unless x.isFVar do continue
      let s ← saveState
      try
        let hx ← Term.exprToSyntax x
        let hid := mkIdent ldecl.userName
        let fid := mkIdent fn
        evalTactic (← `(tactic| cases $hx:term <;> simp [$fid:ident] at $hid:ident))
        return true
      catch _ => s.restore
    return false
  if found then
    let gs ← getGoals
    let mut out := #[]
    for g in gs do
      setGoals [g]
      k2lInvLoop (fuel - 1)
      out := out ++ (← getGoals)
    setGoals out.toList

elab "k2l_inv" : tactic => k2lInvLoop 64

end KPrelude

attribute [k2l_rel] Option.map_some Option.map_none

namespace KPrelude

open Lean Meta Elab Tactic in
/-- `k2l_comm_fn`: close `B.f (tr x) = tr? (A.f x)` after unfolding both definitions: case on
the variables (up to depth 3) until both sides reduce to the same value. -/
partial def k2lCommLoop (fuel : Nat) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let s ← saveState
  try
    evalTactic (← `(tactic| first | rfl | (simp only [k2l_rel]; done) | (simp only [k2l_rel]; rfl)))
    return
  catch _ => s.restore
  if fuel = 0 then throwError "k2l_comm_fn: no proof found"
  -- case on the first local of an inductive type that the goal mentions
  let g ← getMainGoal
  let target ← instantiateMVars (← g.getType)
  let cand ← g.withContext do
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let ty ← whnf ldecl.type
      if ty.isProp then continue
      unless (target.find? (· == ldecl.toExpr)).isSome do continue
      let .const tn _ := ty.getAppFn | continue
      if let some (.inductInfo _) := (← getEnv).find? tn then
        if tn == ``Int || tn == ``Nat || tn == ``String then continue
        return some ldecl.toExpr
    return none
  let some x := cand | throwError "k2l_comm_fn: nothing to case on"
  let hx ← g.withContext (Term.exprToSyntax x)
  evalTactic (← `(tactic| cases $hx:term))
  let gs ← getGoals
  let mut out := #[]
  for g in gs do
    setGoals [g]
    k2lCommLoop (fuel - 1)
    out := out ++ (← getGoals)
  setGoals out.toList

elab "k2l_comm_fn" : tactic => k2lCommLoop 3

end KPrelude

namespace KPrelude

open Lean Meta Elab Tactic in
/-- `k2l_ctor_search I tac`: try each constructor of the inductive proposition `I` in turn:
`apply` it and run `tac` on every new goal; keep the first constructor for which every goal
closes. Used to prove `App c` (some rule applies) without naming the rule. -/
elab "k2l_ctor_search " i:ident " => " tac:tacticSeq : tactic => do
  let n ← realizeGlobalConstNoOverloadWithInfo i
  let some (.inductInfo info) := (← getEnv).find? n | throwError "{n} is not an inductive"
  for c in info.ctors do
    let s ← saveState
    try
      let cid := mkIdent c
      evalTactic (← `(tactic| apply $cid:ident))
      evalTactic (← `(tactic| all_goals ($tac)))
      if (← getGoals).isEmpty then return
      s.restore
    catch _ => s.restore
  throwError "k2l_ctor_search: no constructor of {n} applies"

end KPrelude
