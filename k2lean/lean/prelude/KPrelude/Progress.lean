import Lean
import KPrelude.Soundness
import KPrelude.Hooks
import KPrelude.InvColl

/-!
# Progress: some rule applies (`gen --progress`, SND-13)

The tactic of a generated progress case (`k2lean/docs/design.md`, §3.9): at a configuration whose
head of `<k>` is fixed, prove `App c` from the rules whose left-hand side has that head, given in
order.

`k2l_progress [r₁, …] => close` loops over the goals:
1. *search*: `apply` each rule's `App` constructor in turn and run `close` on what is left (its
   `requires`, its collection facts); the first rule for which everything closes proves the goal.
   When none does, it cases on the first `Bool`-valued application in a rule's remaining goals that
   no hypothesis decides (a side condition such as `isKResult(HOLE)` or `B =/=Int 0`), and searches
   again in both branches;
2. *split*: on a goal no rule closes (and, with `else stuck`, that `stuck` does not close), it cases
   on a variable of the configuration at a position
   where some rule's left-hand side has a constructor (an operand that a rule needs to be an `Int`, a
   stack that a rule needs to be non-empty), and loops on each case.
A goal where neither step makes progress is left as it is: there, no rule of the head applies, so
the generated proof closes it from the invariant or the ending, or the case is open.
Every step is `apply`, `by_cases` or `cases`, so the tactic cannot prove a false goal.

With `<k>` in a cell map (SND-14), a case is about one element `e`, matched as
`concat (element k e) rest = some m`, the same shape as a rule's premise, so the rule's own match
closes by assumption. Two more steps then apply to a rule's remaining premise
`concat (element K' E') D = some rest` that matches a second element (a partner):
3. *split on a hypothesis*: when a hypothesis matches the same key in the same map,
   `concat (element K' w) r = some rest`, a variable of `w` where `E'` has a constructor is split, as
   step 2 does for the goal's configuration;
4. *partner*: when none does and `K'` is known, `by_cases` on `inKeys K' rest`; where it is bound, the
   case's partner lemma (`partner p`, generated with the library) gives the partner's match in
   `rest`, at its own key cell, and, where `rank` proves that it ranks above the case's element,
   that it is an ending. The search then continues with the partner's state.
`MapHook.exists_maximal` is how `progress` picks the element of a case: one that is not an ending
and above which every element is (`k2lean/docs/design.md`, §3.9).

`set_option trace.k2l.progress true` shows each rule's attempt: the goals it leaves, or why it
failed.
-/

namespace KPrelude.MapHook

open ListIso

variable {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V]
  [Std.TransOrd K] [Std.LawfulEqOrd K]

theorem le_foldr_max {α : Type} (f : α → Nat) :
    ∀ {l : List α} {x : α}, x ∈ l → f x ≤ l.foldr (fun a b => max (f a) b) 0
  | _ :: _, _, .head _ => Nat.le_max_left _ _
  | _ :: _, _, .tail _ h => Nat.le_trans (le_foldr_max f h) (Nat.le_max_right _ _)

theorem mem_toList_of_concat_element {k : K} {v : V} {r m : M}
    (h : concat (element k v) r = some m) : (k, v) ∈ toList m := by
  refine (mem_toList_of_concat h).2 (Or.inl ?_)
  unfold element; rw [toList_ofList]; exact List.mem_singleton.2 rfl

/-- Among the bindings of `m` that fail `P`, given one, there is one of maximal `rank`: every
binding of a higher rank satisfies `P` (the bindings are finitely many). With `P` "is an ending",
this is the element whose case `progress` uses: if it waits on an element of a higher rank, that
element is an ending. -/
theorem exists_maximal {m : M} {P : K → V → Prop} (rank : K → V → Nat)
    (h : ∃ k v r, concat (element k v) r = some m ∧ ¬ P k v) :
    ∃ k v r, concat (element k v) r = some m ∧ ¬ P k v ∧
      ∀ k' v' r', concat (element k' v') r' = some m → rank k v < rank k' v' → P k' v' := by
  let B := (toList m).foldr (fun p b => max (rank p.1 p.2) b) 0
  have hB : ∀ k v r, concat (element k v) r = some m → rank k v ≤ B := fun k v r h =>
    le_foldr_max (fun p : K × V => rank p.1 p.2) (mem_toList_of_concat_element h)
  suffices H : ∀ n k v r, B - rank k v = n → concat (element k v) r = some m → ¬ P k v →
      ∃ k v r, concat (element k v) r = some m ∧ ¬ P k v ∧
        ∀ k' v' r', concat (element k' v') r' = some m → rank k v < rank k' v' → P k' v' by
    obtain ⟨k, v, r, h, hp⟩ := h
    exact H _ k v r rfl h hp
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k v r hn h hp
    by_cases hall : ∀ k' v' r', concat (element k' v') r' = some m → rank k v < rank k' v' → P k' v'
    · exact ⟨k, v, r, h, hp, hall⟩
    · simp only [Classical.not_forall] at hall
      obtain ⟨k', v', r', h', hlt, hp'⟩ := hall
      have := hB k' v' r' h'
      exact ih (B - rank k' v') (by omega) k' v' r' rfl h' hp'

/-- A key bound in the rest of a match `K |-> V REST` has a match of its own in the rest and in
the map. -/
theorem concat_element_of_inKeys_rest {k x : K} {v : V} {r m : M}
    (h : concat (element k v) r = some m) (hx : inKeys x r = true) :
    ∃ w r₁ r₂, concat (element x w) r₁ = some r ∧ concat (element x w) r₂ = some m := by
  obtain ⟨w, hw⟩ := inKeys_iff_lookup.1 hx
  have h1 := concat_element_remove (wf_rest_of_concat_element h) hw
  have hm : lookup m x = some w := by
    obtain ⟨_, hk, rfl⟩ := concat_element_iff.1 h
    have hne : x ≠ k := by
      intro e; subst e; rw [hk] at hw; cases hw
    rw [lookup_update_ne _ _ hne]; exact hw
  exact ⟨w, _, _, h1, concat_element_remove (wf_of_concat_element h) hm⟩

end KPrelude.MapHook

namespace KPrelude.Progress

open Lean Meta Elab Tactic

initialize registerTraceClass `k2l.progress

/-- The Boolean connectives a side condition is built from; any other `Bool`-valued application is
an atom of the condition. -/
def connectives : List Name :=
  [``KPrelude.BoolHook.not, ``KPrelude.BoolHook.and, ``KPrelude.BoolHook.or, ``KPrelude.BoolHook.xor,
   ``KPrelude.BoolHook.implies, ``KPrelude.BoolHook.eq, ``KPrelude.BoolHook.ne, ``and, ``or, ``not,
   ``Eq, ``Not, ``And, ``Or]

/-- The atoms of `e`, outermost first: its `Bool`-valued applications that are not built by a
connective and have no loose bound variable or metavariable. -/
partial def atoms (e : Expr) : MetaM (Array Expr) := do
  let e ← instantiateMVars e
  if !e.isApp then return #[]
  if let .const n _ := e.getAppFn then
    if !connectives.contains n && !e.hasLooseBVars && !e.hasMVar then
      if (← whnfR (← inferType e)).isConstOf ``Bool then return #[e]
  let mut out := #[]
  for a in e.getAppArgs do
    out := out ++ (← atoms a)
  return out

/-- Whether a hypothesis already decides `a`: `a = b` or `¬ a = b`. -/
def decided (a : Expr) : MetaM Bool := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let t := if t.isAppOfArity ``Not 1 then t.appArg! else t
    if t.isAppOfArity ``Eq 3 then
      if ← withNewMCtxDepth (isDefEq (t.getArg! 1) a) then return true
  return false

/-- The first atom of `e` that no hypothesis decides. -/
def undecided (e : Expr) : MetaM (Option Expr) := do
  for a in ← atoms e do
    if !(← decided a) then return some a
  return none

/-- A variable of `e` at a position where the pattern `p` has a constructor: what to case on for `p`
to match. Both sides are unfolded reducibly (a K constructor is a reducible definition over the
family); a variable of `p` matches anything, and a clash of constructors means `p` cannot match. -/
partial def mismatch (p e : Expr) : MetaM (Option Expr) := do
  let p ← whnfR (← instantiateMVars p)
  if p.isMVar then return none
  let e ← whnfR e
  if e.isFVar then
    return if p.isApp || p.isConst then some e else none
  match p.getAppFn, e.getAppFn with
  | .const n _, .const n' _ =>
    if n != n' || p.getAppNumArgs != e.getAppNumArgs then return none
    for (a, b) in p.getAppArgs.zip e.getAppArgs do
      if let some x ← mismatch a b then return some x
    return none
  | _, _ => return none

/-- `concat (element k v) d = some x`: `(k, v, x)`. -/
def matchOf? (t : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let t := (← instantiateMVars t).consumeMData
  unless t.isAppOfArity ``Eq 3 do return none
  let lhs := t.getArg! 1
  let rhs := t.getArg! 2
  unless lhs.getAppFn.isConstOf ``KPrelude.MapHook.concat && rhs.isAppOfArity ``Option.some 2 do
    return none
  let la := lhs.getAppArgs
  let some el := la[la.size - 2]? | return none
  unless el.getAppFn.isConstOf ``KPrelude.MapHook.element do return none
  let ea := el.getAppArgs
  let (some k, some v) := (ea[ea.size - 2]?, ea[ea.size - 1]?) | return none
  return some (k, v, rhs.appArg!)

/-- What a rule's remaining goals ask of a second element: a variable to split (a hypothesis
matches the goal's key in the goal's map, and the rule's pattern has a constructor where it has a
variable), or a partner to look up (no hypothesis matches that key there; the key and the map). -/
structure Cand where
  split : Option Expr := none
  partners : Array (Expr × Expr) := #[]

def Cand.merge (a b : Cand) : Cand :=
  { split := a.split <|> b.split, partners := a.partners ++ b.partners }

/-- The candidates of a remaining goal `g` of a rule (in the attempt's state). -/
def candOf (g : MVarId) : MetaM Cand := g.withContext do
  let some (k', e', x') ← matchOf? (← g.getType) | return {}
  let k' ← instantiateMVars k'
  let x' ← instantiateMVars x'
  let mut found := false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (k, w, x) ← matchOf? d.type | continue
    unless ← withNewMCtxDepth (isDefEq x x') do continue
    -- the same element: its key needs splitting, or it unifies with the rule's
    if let some v ← mismatch k' k then
      if v.isFVar then return { split := some v }
    let s ← saveState
    let same ← isDefEq k' k
    s.restore
    if same then
      found := true
      if let some v ← mismatch e' w then
        if v.isFVar then return { split := some v }
  if !found && !k'.hasMVar && !x'.hasMVar && x'.isFVar then
    return { partners := #[(k', x')] }
  return {}

/-- Search among the constructors `cs` (see the module documentation), at most `fuel` atoms deep;
returns the goals where no rule applies. -/
partial def search (cs : Array Name) (close : TSyntax ``Lean.Parser.Tactic.tacticSeq) (fuel : Nat) :
    TacticM (List (MVarId × Cand)) := do
  let mut atom : Option Expr := none
  let mut cand : Cand := {}
  for c in cs do
    let s ← saveState
    let r ← tryCatchRuntimeEx (do
      evalTactic (← `(tactic| apply $(mkIdent c):ident))
      -- `close` runs on the rule's premises only, not on the goals of its variables that
      -- unification has not fixed yet
      let mut rem := #[]
      for g in ← getGoals do
        if ← g.isAssigned then continue
        if ← g.withContext do isProp (← g.getType) then
          setGoals [g]
          let sg ← saveState
          try evalTactic close catch _ => sg.restore
          rem := rem ++ (← getGoals)
        else rem := rem.push g
      setGoals rem.toList
      let gs ← getGoals
      if gs.isEmpty then return some none
      let mut atom' := atom
      if atom'.isNone then
        for g in gs do
          if atom'.isNone then
            atom' ← g.withContext do undecided (← g.getType)
      let mut cand' := cand
      for g in gs do
        cand' := cand'.merge (← candOf g)
      s.restore
      pure (some (some (atom', cand'))))
      (fun ex => do s.restore; trace[k2l.progress] "{c}: failed: {ex.toMessageData}"; pure none)
    trace[k2l.progress] "{c}: {r.map fun o => o.map fun p => (p.1, p.2.split, p.2.partners.map (·.1))}"
    match r with
    | some none => return []
    | some (some (a', c')) => atom := a'; cand := c'
    | none => pure ()
  match atom, fuel with
  | some a, fuel + 1 =>
    let g ← getMainGoal
    let (gt, gf) ← g.withContext do
      let hyp ← mkEq a (mkConst ``Bool.true)
      let (gt, gf) ← g.byCases hyp (← mkFreshUserName `hb)
      pure (gt.mvarId, gf.mvarId)
    let mut out := []
    for g' in [gt, gf] do
      setGoals [g']
      out := out ++ (← search cs close fuel)
    return out
  | _, _ => return [(← getMainGoal, cand)]

/-- A variable of the main goal's configuration that one of the constructors `cs` needs to be a
constructor. -/
def splitVar (cs : Array Name) (g : MVarId) : MetaM (Option Expr) := g.withContext do
  -- a goal left by `cases` or `subst` can carry an annotation around its type
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isApp do return none
  for c in cs do
    let k ← mkConstWithFreshMVarLevels c
    let (_, _, concl) ← forallMetaTelescope (← inferType k)
    unless concl.isApp do continue
    if let some x ← mismatch concl.appArg! t.appArg! then
      if x.isFVar then return some x
  return none

/-- Whether `stuck` closes the goal `g` (a configuration the invariant or the ending excludes). -/
def closes (stuck : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) (g : MVarId) : TacticM Bool := do
  let some t := stuck | return false
  let s ← saveState
  tryCatchRuntimeEx (do
    setGoals [g]
    evalTactic t
    if (← getGoals).isEmpty then return true
    s.restore; return false)
    fun _ => do s.restore; return false

/-- `f h` when `f`'s argument type unifies with `h`'s type (at the current depth, so that the
implicit arguments `f` was elaborated with are fixed by `h`). -/
def applyTo (f h : Expr) : MetaM (Option Expr) := do
  let .forallE _ d _ _ ← whnf (← inferType f) | return none
  if ← isDefEq d (← inferType h) then return some (mkApp f h) else return none

/-- The partner step (module documentation, step 4) for the first partner of `cand`: the goals it
leaves, or `none` when it does not apply. -/
def partnerStep (p : Term) (rank : TSyntax ``Lean.Parser.Tactic.tacticSeq) (cand : Cand) (g : MVarId) :
    TacticM (Option (List MVarId)) := do
  for (k', x) in cand.partners do
    let r? ← g.withContext do
      let hin ← mkEq (← mkAppM ``KPrelude.MapHook.inKeys #[k', x]) (mkConst ``Bool.true)
      -- the case's partner lemma must apply to this map
      let f ← try Term.elabTermAndSynthesize p none
        catch ex => trace[k2l.progress] "partner: {p} does not elaborate: {ex.toMessageData}"; return none
      let s ← saveState
      let ok ← (do let h ← mkFreshExprMVar hin; pure (← applyTo f h).isSome) <|> pure false
      s.restore
      unless ok do trace[k2l.progress] "partner: {f} does not apply to {hin}"; return none
      -- a hypothesis that decides it
      let mut known : Option Expr := none
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let t ← instantiateMVars d.type
        if ← withNewMCtxDepth (isDefEq t hin) then known := some d.toExpr
        else
          let t' := if t.isAppOfArity ``Not 1 then t.appArg! else t
          if ← withNewMCtxDepth (isDefEq t' hin) then return some none
      pure (some (some (hin, known)))
    let some (some (hin, known)) := r? | continue
    let (gpos, gneg?) ← match known with
      | some _ => pure (g, none)
      | none => do
        let (gt, gf) ← g.byCases hin `k2l_hin
        pure (gt.mvarId, some gf.mvarId)
    let gpos ← gpos.withContext do
      let mut hyp := none
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        if ← withNewMCtxDepth (isDefEq (← instantiateMVars d.type) hin) then hyp := some d.toExpr
      let some h := hyp | throwError "k2l_progress: partner: the hypothesis is gone"
      let f ← Term.elabTermAndSynthesize p none
      let some pf ← applyTo f h | throwError "k2l_progress: partner: {p} does not apply"
      let pf ← instantiateMVars pf
      let (_, g') ← (← gpos.assert `k2l_hp (← inferType pf) pf).intro1P
      pure g'
    setGoals [gpos]
    let hp := mkIdent `k2l_hp
    evalTactic (← `(tactic| repeat (obtain ⟨_, $hp:ident⟩ := $hp:ident)))
    -- the partner's ending, where `rank` proves that it ranks higher: `rank` runs on a goal of its
    -- own and is used only when it closes it (it may fail in any way, a runtime limit included)
    let g ← getMainGoal
    let g ← g.withContext do
      let some d := (← getLCtx).findFromUserName? `k2l_hp | return g
      let .forallE _ a b _ ← whnfR (← instantiateMVars d.type) | return g
      if b.hasLooseBVars then return g
      let mv ← mkFreshExprSyntheticOpaqueMVar a
      let s ← saveState
      let ok ← tryCatchRuntimeEx (do
          let gs ← Tactic.run mv.mvarId! (evalTactic rank)
          pure (gs.isEmpty && !(← instantiateMVars mv).hasSorry))
        fun _ => pure false
      if !ok then
        s.restore
        return g
      let (_, g') ← (← g.assert `k2l_hp b (mkApp d.toExpr mv)).intro1P
      return g'
    replaceMainGoal [g]
    let gs ← getGoals
    return some (gs ++ gneg?.toList)
  return none

/-- See the module documentation; `fuel` bounds the splits along one branch. A goal that `stuck`
closes is not split further. -/
partial def loop (cs : Array Name) (close : TSyntax ``Lean.Parser.Tactic.tacticSeq)
    (stuck : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq))
    (partner : Option (Term × TSyntax ``Lean.Parser.Tactic.tacticSeq)) (fuel : Nat) : TacticM Unit := do
  let gs ← getGoals
  let mut out := #[]
  for g in gs do
    setGoals [g]
    for (r, cand) in ← search cs close 4 do
      if ← closes stuck r then continue
      let x? := (← splitVar cs r) <|> cand.split
      match x?, fuel with
      | some x, fuel + 1 =>
        setGoals [r]
        Soundness.casesVar x
        evalTactic (← `(tactic| all_goals k2l_norm_idx))
        loop cs close stuck partner fuel
        out := out ++ (← getGoals)
      | none, fuel + 1 =>
        let step? ← match partner with
          | some (p, rank) => partnerStep p rank cand r
          | none => pure none
        match step? with
        | some gs' =>
          setGoals gs'
          loop cs close stuck partner fuel
          out := out ++ (← getGoals)
        | none => out := out.push r
      | _, _ => out := out.push r
  setGoals out.toList

elab "k2l_progress " "[" cs:ident,* "]" " => " close:tacticSeq : tactic => do
  let cs ← cs.getElems.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
  loop cs close none none 6

/-- `k2l_progress [r₁, …] => close else stuck`: the same, and a goal no rule closes is first given
to `stuck`, which closes it when the invariant or the ending excludes the configuration, before it
is split further. -/
elab "k2l_progress " "[" cs:ident,* "]" " => " close:tacticSeq " else " stuck:tacticSeq : tactic => do
  let cs ← cs.getElems.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
  loop cs close (some stuck) none 6

/-- `k2l_progress [r₁, …] => close else stuck partner p rank t`: the same, at a case of an element of
a cell map, with the partner step (module documentation, step 4): `p` is the case's partner lemma
applied to its match, invariant and ranks, and `t` proves that a partner ranks higher. -/
elab "k2l_progress " "[" cs:ident,* "]" " => " close:tacticSeq " else " stuck:tacticSeq
    " partner " p:term " rank " rank:tacticSeq : tactic => do
  let cs ← cs.getElems.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
  -- two more splits along a branch than at one `<k>`: the partner step, and the partner's element
  loop cs close (some stuck) (some (p, rank)) 9

/-- `k2l_has_ctor_at h [C, …]`: fails unless the type of `h` has an application of one of the
constructors (`k2l_has_ctor` reads the goal; at a cell map, an element's head is in its match). -/
elab "k2l_has_ctor_at " h:ident " [" cs:ident,* "]" : tactic => withMainContext do
  let cs ← Soundness.names cs.getElems
  let t ← inferType (← Term.elabTerm h none)
  if (← Soundness.findCtorArg cs (← instantiateMVars t)).isNone then
    throwError "k2l_has_ctor_at: no application of {cs} in {h}"

/-- `k2l_ground`: fails when the goal has a metavariable (a rule's premise whose variables an
earlier premise has not fixed yet), so that a closer does not compute on it. -/
elab "k2l_ground" : tactic => withMainContext do
  if (← instantiateMVars (← getMainTarget)).hasMVar then throwError "k2l_ground: the goal has metavariables"

/-- The leaves `EntriesOn` of a proof `p : t` of a conjunction (its definitions unfolded). -/
partial def entriesLeaves (p t : Expr) (depth : Nat := 8) : MetaM (Array Expr) := do
  let t ← instantiateMVars t
  if t.isAppOf ``KPrelude.MapHook.EntriesOn then return #[p]
  if t.isAppOfArity ``And 2 then
    return (← entriesLeaves (← mkAppM ``And.left #[p]) (t.getArg! 0) depth) ++
      (← entriesLeaves (← mkAppM ``And.right #[p]) (t.getArg! 1) depth)
  match depth with
  | 0 => return #[]
  | depth + 1 =>
    match ← unfoldDefinition? t with
    | some t' => entriesLeaves p t' depth
    | none => return #[]

/-- `k2l_entries h [h₁, …]` with `h : concat (element k v) r = some m`: for each `hᵢ` whose
conjuncts include `EntriesOn Q m` (an invariant lifted over the cell map), the fact `Q (k, v)`
about the matched element. -/
elab "k2l_entries " h:ident " [" hs:ident,* "]" : tactic => withMainContext do
  let hm ← Term.elabTerm h none
  let mut facts := #[]
  for hi in hs.getElems do
    let p ← Term.elabTerm hi none
    for leaf in ← entriesLeaves p (← inferType p) do
      try facts := facts.push (← mkAppM ``KPrelude.MapHook.entry_of_concat_element #[hm, leaf])
      catch _ => pure ()
  let mut g ← getMainGoal
  for f in facts do
    let (_, g') ← (← g.assert `k2l_he (← inferType f) f).intro1P
    g := g'
  replaceMainGoal [g]

end KPrelude.Progress
