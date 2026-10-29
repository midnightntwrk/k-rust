import Lean
import KPrelude.Soundness
import KPrelude.Hooks
import KPrelude.InvColl

/-!
# Progress: some rule applies (`gen --progress`, SND-13)

The tactic of a generated progress case (`k2lean/docs/design.md`, §3.9): at a configuration whose
head of `<k>` is fixed, prove `App c` from the rules whose left-hand side has that head, given in
order. With priorities the goal is `∃ i, App i c` (some rule of some rank applies; `exists_least`
gives the least such rank, the one `Step` takes), and each attempt leaves the rank to the rule's
constructor, so one case can close by rules of different ranks on different branches (SND-15).

`k2l_progress [r₁, …] => close` loops over the goals:
1. *search*: `apply` each rule's `App` constructor in turn and run `close` on what is left (its
   `requires`, its collection facts); the first rule for which everything closes proves the goal.
   When none does, it cases on the first `Bool`-valued application in a rule's remaining goals that
   no hypothesis decides (a side condition such as `isKResult(HOLE)` or `B =/=Int 0`), or on the
   outcome of a sort projection that does not compute (`proj_Expr_Value y = some V`, the premise of
   a sorted variable `V:Value`), and searches again in each branch. A rule with a premise that cannot
   hold (its sides reduce to different constructors, `none = some _`, or a hypothesis decides it the
   other way) is skipped: it does not apply there, and asks for no split;
2. *split*: on a goal no rule closes (and, with `else stuck`, that `stuck` does not close), it cases
   on a variable of the configuration at a position
   where some rule's left-hand side has a constructor (an operand that a rule needs to be an `Int`, a
   stack that a rule needs to be non-empty), and loops on each case. A rule whose premises cannot
   hold with that variable left open asks for no split (a cooling rule, whose head is any item of
   the hole's sort, at a head of another sort). Each such split goes one position further into a
   finite pattern, so these splits end by themselves; `fuel` bounds the others: where a projection
   was assumed `none` and the goal stays open, the projected variable's constructors, and the
   partner steps below. A rule whose pattern has a different constructor than the configuration at
   some position (`clashes`) cannot match there, so it asks for no split; a proof argument (an
   injection's `leafOK`) is never split, since any two proofs of a proposition are equal.
A goal where neither step makes progress is left as it is: there, no rule of the head applies, so
the generated proof closes it from the invariant or the ending, or the case is open.
Every step is `apply`, `by_cases` or `cases`, so the tactic cannot prove a false goal.

*Closing* a goal from the invariant may need splits of its own: the invariant's computation is
blocked on a call of an opaque function (`typeOf G e`) or on a variable that a `match` reads below
a constructor (a freezer's `K` argument). `k2l_case_stuck` splits the innermost such variable (by
`reduceMatcher?`, then the stuck term's major premise, as `getStuckMVar?` finds a metavariable) or
the call (`cases h : call`); the generated stuck closer alternates it with `simp`, after
`k2l_refute_computed` (a `Bool` side condition that computes to the other literal).

With `<k>` in a cell map (SND-14), a case is about one element `e`, matched as
`concat (element k e) rest = some m`, the same shape as a rule's premise, so the rule's own match
closes by assumption. Two more steps then apply to a rule's remaining premise
`concat (element K' E') D = some rest` that matches a second element (a partner):
3. *split on a hypothesis*: when a hypothesis matches the same key in the same map,
   `concat (element K' w) r = some rest`, a variable of `w` where `E'` has a constructor is split, as
   step 2 does for the goal's configuration, and as it does, without `fuel`. A rule's match closes
   only by assumption, so a rule whose element clashes with that of every match hypothesis is not
   attempted (`elementClash`): its `apply` would unify the match with each hypothesis at default
   transparency, unfolding `concat`, only to fail;
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

/-- Given a rank where `A` holds, there is a least one. With `A i` "a rule of rank `i` applies",
that rank's rules are the ones `Step` takes: a rule of rank `i` steps only when no rule of a rank
`j < i` applies (its constructor's `hpri`). -/
theorem exists_least {A : Nat → Prop} (h : ∃ i, A i) : ∃ i, A i ∧ ∀ j, j < i → ¬ A j := by
  obtain ⟨i, hi⟩ := h
  induction i using Nat.strongRecOn with
  | ind i ih =>
    by_cases hm : ∃ j, j < i ∧ A j
    · obtain ⟨j, hj, hj'⟩ := hm
      exact ih j hj hj'
    · exact ⟨i, hi, fun j hj hj' => hm ⟨j, hj, hj'⟩⟩

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
      -- a proof argument (an injection's `hasLeaves`, `leafOK`) unifies with any other proof
      if ← isProof b then continue
      if let some x ← mismatch a b then return some x
    return none
  | _, _ => return none

/-- Whether the pattern `p` cannot match `e`: at some position both are constructors, and
different ones. No split of `e` makes `p` match then. -/
partial def clashes (p e : Expr) : MetaM Bool := do
  let p ← whnfR (← instantiateMVars p)
  if p.isMVar then return false
  let e ← whnfR e
  match p.getAppFn, e.getAppFn with
  | .const n _, .const n' _ =>
    let env ← getEnv
    if n != n' then return env.isConstructor n && env.isConstructor n'
    if p.getAppNumArgs != e.getAppNumArgs then return false
    for (a, b) in p.getAppArgs.zip e.getAppArgs do
      if ← isProof b then continue
      if ← clashes a b then return true
    return false
  | _, _ => return false

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
      if ← clashes e' w then return {}
      if let some v ← mismatch e' w then
        if v.isFVar then return { split := some v }
  if !found && !k'.hasMVar && !x'.hasMVar && x'.isFVar then
    return { partners := #[(k', x')] }
  return {}

/-- The constructor at the head of `e`, if any. -/
def ctorOf? (e : Expr) : MetaM (Option Name) := do
  let .const n _ := e.getAppFn | return none
  if (← getEnv).isConstructor n then return some n else return none

/-- Whether a premise `a = b` of a rule cannot hold: both sides reduce to different constructors
(`none = some _`, `false = true`), or a hypothesis gives `a` a value of another constructor. -/
def premiseDead (t : Expr) : MetaM Bool := do
  let t := (← instantiateMVars t).consumeMData
  unless t.isAppOfArity ``Eq 3 do return false
  -- a match of an element is decided by the hypotheses (`candOf`), not by computing the map
  if (← matchOf? t).isSome then return false
  let a := t.getArg! 1
  let some cb ← ctorOf? (← whnfD (t.getArg! 2)) | return false
  if let some ca ← ctorOf? (← whnfD a) then return ca != cb
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let u := (← instantiateMVars d.type).consumeMData
    if u.isAppOfArity ``Eq 3 then
      if ← withNewMCtxDepth (isDefEq (u.getArg! 1) a) then
        if let some cu ← ctorOf? (← whnfD (u.getArg! 2)) then
          if cu != cb then return true
  return false

/-- `proj_A_B x`: a sort projection (the premise of a sorted variable `V:B` of a rule). -/
def isProj (a : Expr) : Bool :=
  match a.consumeMData.getAppFn with
  | .const (.str _ str) _ => str.startsWith "proj_" && a.getAppNumArgs > 0
  | _ => false

/-- A premise `proj_A_B x = some V` whose projection does not compute (`x` is not a constructor)
and that no hypothesis decides: the projection to case on. -/
def projAtom? (t : Expr) : MetaM (Option Expr) := do
  let t := (← instantiateMVars t).consumeMData
  unless t.isAppOfArity ``Eq 3 && (t.getArg! 2).isAppOfArity ``Option.some 2 do return none
  let a := (t.getArg! 1).consumeMData
  unless isProj a && !a.hasMVar && !a.hasLooseBVars do return none
  if (← ctorOf? (← whnfD a)).isSome then return none
  if ← decided a then return none
  return some a

/-- Whether rule constructor `c` cannot apply at goal `g` because its first match of an element,
`concat (element K E) D = some M`, can only close by assumption, and `E` clashes with the element
of every such hypothesis. -/
def elementClash (c : Name) (g : MVarId) : MetaM Bool := g.withContext do
  let s ← saveState
  let r ← (do
    let (hs, _, _) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels c))
    let mut pat := none
    for h in hs do
      if let some (_, e', _) ← matchOf? (← inferType h) then pat := some e'; break
    let some e' := pat | return false
    let mut any := false
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let some (_, w, _) ← matchOf? d.type | continue
      any := true
      unless ← clashes e' w do return false
    return any)
  s.restore
  return r

/-- Search among the constructors `cs` (see the module documentation), at most `fuel` atoms deep;
returns the goals where no rule applies. -/
partial def search (cs : Array Name) (close : TSyntax ``Lean.Parser.Tactic.tacticSeq) (fuel : Nat) :
    TacticM (List (MVarId × Cand)) := do
  let mut atom : Option Expr := none
  let mut cand : Cand := {}
  for c in cs do
    if ← elementClash c (← getMainGoal) then
      trace[k2l.progress] "{c}: its element clashes"; continue
    let s ← saveState
    let r ← tryCatchRuntimeEx (do
      -- with priorities the goal is `∃ i, App i c`, and the constructor fixes the rank
      if (← whnfD (← getMainTarget)).isAppOf ``Exists then
        evalTactic (← `(tactic| (apply Exists.intro; apply $(mkIdent c):ident)))
      else evalTactic (← `(tactic| apply $(mkIdent c):ident))
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
      -- a rule with a premise that cannot hold here neither applies nor asks for a split
      if ← gs.anyM fun g => g.withContext do premiseDead (← g.getType) then
        s.restore; trace[k2l.progress] "{c}: a premise cannot hold"; return none
      let mut atom' := atom
      if atom'.isNone then
        for g in gs do
          if atom'.isNone then
            atom' ← g.withContext do
              let t ← g.getType
              match ← undecided t with
              | some a => pure (some a)
              | none => projAtom? t
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
    let gs ← g.withContext do
      if isProj a then
        -- the projection's two outcomes: `some v` (the rule's premise, by assumption) or `none`
        let ta ← Term.exprToSyntax a
        let hp := mkIdent (← mkFreshUserName `hp)
        setGoals [g]
        evalTactic (← `(tactic| cases $hp:ident : $ta:term))
        getGoals
      else
        let hyp ← mkEq a (mkConst ``Bool.true)
        let (gt, gf) ← g.byCases hyp (← mkFreshUserName `hb)
        pure [gt.mvarId, gf.mvarId]
    let mut out := []
    for g' in gs do
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
    let (hs, _, concl) ← forallMetaTelescope (← inferType k)
    unless concl.isApp do continue
    if ← clashes concl.appArg! t.appArg! then continue
    if let some x ← mismatch concl.appArg! t.appArg! then
      if x.isFVar then
        -- the rule with `x` left open: when one of its premises already cannot hold, splitting
        -- `x` cannot make it apply
        let s ← saveState
        let mx ← mkFreshExprMVar (← inferType x)
        let t' := (t.appArg!.abstract #[x]).instantiate1 mx
        let refuted ← tryCatchRuntimeEx (do
          if ← isDefEq concl.appArg! t' then
            hs.anyM fun h => do premiseDead (← inferType h)
          else pure false) fun _ => pure false
        s.restore
        if refuted then trace[k2l.progress] "{c}: needs {x} split, but a premise cannot hold"
        else return some x
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

/-- A hypothesis `proj_A_B x = none` with `x` a variable: `x`. -/
def projNoneVar? (g : MVarId) : MetaM (Option Expr) := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t := (← instantiateMVars d.type).consumeMData
    if t.isAppOfArity ``Eq 3 && (t.getArg! 2).isAppOfArity ``Option.none 1 then
      let a := (t.getArg! 1).consumeMData
      if isProj a && a.appArg!.isFVar then return some a.appArg!
  return none

/-- See the module documentation; `fuel` bounds the splits along one branch. A goal that `stuck`
closes is not split further. -/
partial def loop (cs : Array Name) (close : TSyntax ``Lean.Parser.Tactic.tacticSeq)
    (stuck : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq))
    (partner : Option (Term × TSyntax ``Lean.Parser.Tactic.tacticSeq)) (fuel : Nat)
    (depth : Nat := 32) : TacticM Unit := do
  let gs ← getGoals
  let mut out := #[]
  for g in gs do
    setGoals [g]
    for (r, cand) in ← search cs close 4 do
      if ← closes stuck r then continue
      -- a variable where a rule's pattern has a constructor: each such split goes one position
      -- further into a finite pattern, so these splits end by themselves (`depth` is a guard)
      if let (some x, depth + 1) := ((← splitVar cs r) <|> cand.split, depth) then
        setGoals [r]
        Soundness.casesVar x
        evalTactic (← `(tactic| all_goals k2l_norm_idx))
        loop cs close stuck partner fuel depth
        out := out ++ (← getGoals)
        continue
      -- the other splits use `fuel`
      let x? ← projNoneVar? r
      match x?, fuel with
      | some x, fuel + 1 =>
        setGoals [r]
        Soundness.casesVar x
        evalTactic (← `(tactic| all_goals k2l_norm_idx))
        loop cs close stuck partner fuel depth
        out := out ++ (← getGoals)
      | none, fuel + 1 =>
        let step? ← match partner with
          | some (p, rank) => partnerStep p rank cand r
          | none => pure none
        match step? with
        | some gs' =>
          setGoals gs'
          loop cs close stuck partner fuel depth
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

/-- The variable that the reduction of `e` is stuck on: the major premise of a recursor, or what
a `match` is stuck on (as `getStuckMVar?` finds a metavariable). -/
partial def stuckFVar? (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData
  if e.isFVar then return some e
  let .const n _ := e.getAppFn | return none
  match (← getEnv).find? n with
  | some (.recInfo r) =>
    let args := e.getAppArgs
    if h : r.getMajorIdx < args.size then stuckFVar? (← whnf args[r.getMajorIdx]) else return none
  | _ =>
    if (← getMatcherInfo? n).isSome then
      match ← reduceMatcher? e with
      | .stuck s => stuckFVar? s
      | _ => return none
    else return none

/-- A call `f a…` that is a `match` stuck on a variable once `f` is unfolded: that variable. -/
def callStuckVar? (d : Expr) : MetaM (Option Expr) := do
  let some d' ← unfoldDefinition? d | return none
  let d' ← whnfCore d'
  match d'.getAppFn with
  | .const n _ =>
    if (← getMatcherInfo? n).isSome then
      match ← reduceMatcher? d' with
      | .stuck s => stuckFVar? s
      | _ => return none
    else stuckFVar? d'
  | _ => return none

/-- The innermost blocked discriminant of `e`: a discriminant of a `match`, or the option that
`Option.bind`/`Option.map` reads, that is not a constructor application and has no bound variable. -/
partial def blocked? (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData
  match e with
  | .app .. =>
    for a in e.getAppArgs do
      if let some d ← blocked? a then return some d
    -- a `match` stuck inside its discriminants (a pattern below a constructor): that variable
    if (← matchMatcherApp? e).isSome && !e.hasLooseBVars && !e.hasMVar then
      if let .stuck st ← tryCatchRuntimeEx (reduceMatcher? e) (fun _ => pure .notMatcher) then
        if let some v ← stuckFVar? st then return some v
    let ds ← (do
      if let some m ← matchMatcherApp? e then pure m.discrs
      else if e.isAppOfArity ``Option.bind 4 then pure #[e.getArg! 2]
      else if e.isAppOfArity ``Option.map 4 then pure #[e.getArg! 3]
      else pure #[])
    for d in ds do
      let d := d.consumeMData
      if d.hasLooseBVars || d.hasMVar then continue
      -- a variable, or a call that does not compute (`typeOf G e`, `proj_A_B x`) and that no
      -- hypothesis decides yet
      if d.isFVar then return some d
      unless d.isApp && d.getAppFn.isConst do continue
      if (← ctorOf? (← whnfR d)).isNone && !(← decided d) then return some d
    return none
  | .lam _ _ b _ => blocked? b
  | _ => return none

/-- The closer's split (the module documentation, *closing*): on the innermost blocked computation
of a hypothesis, the variable it is stuck on (`cases`, substituted), or the call that blocks it
(`cases h : call`, rewritten everywhere). Each step removes a variable or decides a call, so a
loop of this step and `simp` ends. -/
elab "k2l_case_stuck" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some x ← blocked? (← instantiateMVars d.type) then
      -- a `match` behind the call, stuck on a variable: the variable (not a projection, whose two
      -- outcomes are split instead)
      let x ← if x.isFVar || isProj x then pure x else
        match ← tryCatchRuntimeEx (callStuckVar? x) (fun _ => pure none) with
        | some v => pure v
        | none => pure x
      if x.isFVar then
        -- a value of a K sort, split into its constructors and substituted (a variable of any
        -- other type is left alone: a `match` on a `Nat` would be split without end)
        unless ← Soundness.isFamily (← inferType x) do continue
        Soundness.casesVar x
        evalTactic (← `(tactic| all_goals k2l_norm_idx))
        return
      let tx ← Term.exprToSyntax x
      let h := mkIdent (← mkFreshUserName `hs)
      evalTactic (← `(tactic| cases $h:ident : $tx:term))
      -- the call's value everywhere, so that it is no longer blocked, but not in `h` itself,
      -- which `simp only [h] at *` makes `True`: the value is needed again once the call's
      -- arguments are split
      let mut out := []
      for g in ← getGoals do
        let g' ← g.withContext do
          let some hd := (← getLCtx).findFromUserName? h.getId | return some g
          let thms ← ({} : SimpTheorems).add (.fvar hd.fvarId) #[] hd.toExpr
          let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
          let mut fs := #[]
          for d in ← getLCtx do
            if d.isImplementationDetail || d.fvarId == hd.fvarId then continue
            if ← isProp d.type then fs := fs.push d.fvarId
          let (r, _) ← simpGoal g ctx (fvarIdsToSimp := fs)
          pure (r.map (·.2))
        if let some g' := g' then out := out ++ [g']
      setGoals out
      return
  throwError "k2l_case_stuck: no blocked discriminant"

/-- `k2l_dispatch hm [c₁, …]`: close the main goal by the case `cᵢ` (a lemma whose statement is
`∀ …, concat (element k e) r = some m → … → goal`) whose match premise is `hm`'s type up to
reducible unfolding, its other premises by assumption. Each goal of `progress`'s split is one head,
so the case is determined; a K constructor is a reducible definition over the arity-indexed family,
so a wrong case fails at the first different constructor of the element, without unfolding `concat`
(which `exact` at default transparency does, at every wrong case). -/
elab "k2l_dispatch " h:ident " [" cs:ident,* "]" : tactic => withMainContext do
  let g ← getMainGoal
  let hd ← getLocalDeclFromUserName h.getId
  let ht ← instantiateMVars hd.type
  let tgt ← instantiateMVars (← g.getType)
  for c in cs.getElems do
    let n ← realizeGlobalConstNoOverloadWithInfo c
    let s ← saveState
    let k ← mkConstWithFreshMVarLevels n
    -- reducing at each binder: a case is `∀ [Hooks], X.statement` in a library with hooks
    let (xs, _, concl) ← forallMetaTelescopeReducing (← inferType k)
    let mut idx := none
    for i in [0:xs.size] do
      let xt ← instantiateMVars (← inferType xs[i]!)
      if xt.isAppOfArity ``Eq 3 && (xt.getArg! 1).getAppFn.isConstOf ``KPrelude.MapHook.concat then
        idx := some i; break
    let some i := idx | continue
    if !(← withReducible (isDefEq (← inferType xs[i]!) ht)) then s.restore; continue
    xs[i]!.mvarId!.assign hd.toExpr
    let mut ok := true
    for j in [0:xs.size] do
      let mv := xs[j]!.mvarId!
      if j < i && !(← isProp (← mv.getType)) && !(← isClass? (← mv.getType)).isSome then continue
      if ← mv.isAssigned then continue
      try mv.assumption catch _ => ok := false; break
    if ok && (← isDefEq concl tgt) && (← xs.allM fun x => x.mvarId!.isAssigned) then
      g.assign (mkAppN k xs)
      replaceMainGoal []
      return
    s.restore
  throwError "k2l_dispatch: no case of {cs.getElems.size} has the match {ht}"

/-- `k2l_refute_computed`: close the goal by a hypothesis `a = b` at a sort whose carrier is `Bool`,
`b` a literal and `a` definitionally the other one, as `isKResult(I ~> .) = true` is with `I` an
identifier: the computation is definitional, and `simp` does not do it where it would need an
`owise` equation, whose side condition is not syntactic. -/
elab "k2l_refute_computed" : tactic => withMainContext do
  let g ← getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t := (← instantiateMVars d.type).consumeMData
    -- a `Bool` side condition (a function of K whose value computes)
    unless t.isAppOfArity ``Eq 3 do continue
    -- (a sort whose carrier is `Bool`, as `SortBool`, unfolds to it reducibly)
    unless (← whnfR (t.getArg! 0)).isConstOf ``Bool do continue
    -- `a = true` where `a` is definitionally `false` (or the converse): `isDefEq` unfolds both
    -- sides lazily, where `whnf` alone can stop short
    let b ← whnfD (t.getArg! 2)
    let other ← if b.isConstOf ``Bool.true then pure (mkConst ``Bool.false)
      else if b.isConstOf ``Bool.false then pure (mkConst ``Bool.true) else continue
    let s ← saveState
    unless ← withDefault (isDefEq (t.getArg! 1) other) do s.restore; continue
    let h ← mkExpectedTypeHint d.toExpr (← mkEq other b)
    g.assign (← mkNoConfusion (← g.getType) h)
    replaceMainGoal []
    return
  throwError "k2l_refute_computed: no hypothesis computes to a contradiction"

end KPrelude.Progress
