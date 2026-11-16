/-
  Tactics for runs of a definition's step relation. Each produces a proof the kernel checks; what
  they compute is only a candidate the kernel confirms.

  - `fire i j …` on a goal `Runs c u w`: one step by rule i (then j, …): the substitution is found
    by matching the rule's left-hand side against u (constructors, injections, aliases, and the
    map pattern `K |-> V M` against a map of concrete keys, K bound elsewhere in the pattern), the
    successor v is the right-hand side built with the substitution's values, function calls
    evaluated by the kernel; the proof is `stepsTo_fire`, its equations decided by the kernel
    (`kernel_defeq`), the sorts of the values proved from the hypotheses `c.sortOf X = some s` on
    the free terms they hold (`ksort`), and the new goal is `Runs c v w`. A `requires` whose
    value the kernel leaves as a Boolean `b` is the new goal `b = true`; a rule above the smallest
    priority leaves the goal that no rule of a smaller priority applies. `fire i with σ` starts
    the match from the bindings σ (a list of (variable, value) pairs), for a match the left-hand
    side does not determine.
  - `fire?`: a search for writing a proof: steps by the one rule that applies, while there is one,
    and suggests the `fire` line of the steps taken.
  - `run_end`: closes `Runs c u w` where the kernel finds u and w equal.
  - `run_by h`: with `h : Runs c u' w'` where the kernel finds u and u' equal, leaves `Runs c w' w`.
  - `ksort`: proves `c.sortOf t = some s` from the constructors' signatures, down to hypotheses on
    the free terms t holds.
  - `config_sorts hx`: from `hx : x.val = t`, x a configuration, adds the sorts of the free terms t
    holds below constructors and injections (`hK : c.sortOf K = some s`).
-/
import KcoreSpec.Fire

set_option autoImplicit false

open Lean Meta Elab Tactic

register_option fire.fuel : Nat := {
  defValue := 200
  descr := "the fuel of the executable evaluation `fire` checks the right-hand side and the `requires` with"
}

namespace KCore.FireTac

/-! ## The kernel's reduction -/

/-- Weak head normal form by the kernel, in the current local context. -/
def kwhnf (e : Expr) : MetaM Expr := do
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok r => pure r
  | .error _ => throwError "the kernel does not reduce{indentExpr e}"

/-- The number a closed `Nat` term reduces to. -/
def natOf (e : Expr) : MetaM Nat := do
  match ← kwhnf e with
  | .lit (.natVal n) => pure n
  | _ => throwError "not a number:{indentExpr e}"

/-- The constructor at the head of `e`, with its numbers of parameters and fields. -/
def ctorHead? (e : Expr) : MetaM (Option (Name × Nat × Nat)) := do
  match e.getAppFn with
  | .const n _ =>
    match (← getEnv).find? n with
    | some (.ctorInfo ci) => pure (some (n, ci.numParams, ci.numFields))
    | _ => pure none
  | _ => pure none

mutual
  /-- The normal form of a data term (ground terms, literals, lists, options, pairs, rules), as far
  as the kernel reduces it: below each constructor, its fields' normal forms; a literal's Int,
  Bool or text as written when it holds a variable; a term the kernel leaves stuck (a variable,
  or a function of one) as written. -/
  partial def kdeep (e : Expr) : MetaM Expr := do
    let e := e.headBeta
    if e.isFVar then return e
    if let .lit _ := e then return e
    let w ← kwhnf e
    match w with
    | .lit _ => return w
    | .fvar _ => return w
    | _ =>
      match ← ctorHead? w with
      | some (n, np, nf) =>
        let args := w.getAppArgs
        if args.size != np + nf then return e
        let leaf := n == ``Lit.int || n == ``Lit.bool || n == ``Lit.tok || n == ``Lit.float
        let mut out := args
        for i in [np:args.size] do
          out := out.set! i (← if leaf then kleaf args[i]! else kdeep args[i]!)
        return mkAppN w.getAppFn out
      | none => return e
  /-- A literal's content: its normal form when it is closed, as written otherwise. -/
  partial def kleaf (e : Expr) : MetaM Expr := do
    let e := e.headBeta
    if e.hasFVar then return e
    kdeep e
end

/-- The elements of a list term. -/
partial def listElems (e : Expr) : MetaM (Array Expr) := do
  let rec go (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    let w ← kwhnf e
    if w.isAppOfArity ``List.cons 3 then go w.appArg! (acc.push w.appFn!.appArg!)
    else if w.isAppOfArity ``List.nil 1 then pure acc
    else throwError "not a list:{indentExpr e}"
  go e #[]

/-- A proof of the equation `a = b` (in type α) by `Eq.refl`, checked by the kernel's definitional
equality alone, the local variables it mentions abstracted (as `kernel_defeq`). -/
def kdefeq (α a b : Expr) : MetaM Expr := do
  let t := mkApp3 (mkConst ``Eq [Level.one]) α a b
  let t ← instantiateMVars t
  if t.hasMVar then throwError "kernel_defeq: the equation has metavariables{indentExpr t}"
  let fvs := (collectFVars {} t).fvarIds
  let xs := fvs.map mkFVar
  let t' ← mkForallFVars xs t
  if t'.hasFVar then throwError "kernel_defeq: a variable of the equation has a type with variables"
  let pf ← forallTelescope t' fun ys body => do
    let some (α, a, _) := body.eq? | throwError "not an equation"
    mkLambdaFVars ys (mkApp2 (mkConst ``Eq.refl [Level.one]) α a)
  let name ← mkAuxLemma [] t' pf
  return mkAppN (mkConst name) xs

/-! ## Names of the library's terms -/

def gtTy : Expr := mkConst ``GroundTerm
def srtTy : Expr := mkConst ``Srt
def optGt : Expr := mkApp (mkConst ``Option [Level.zero]) gtTy
def optOptGt : Expr := mkApp (mkConst ``Option [Level.zero]) optGt
def someE (α a : Expr) : Expr := mkApp2 (mkConst ``Option.some [Level.zero]) α a
def entryTy : Expr := mkApp2 (mkConst ``_root_.Prod [Level.zero, Level.zero]) gtTy gtTy
def natE (n : Nat) : Expr := mkRawNatLit n

/-- `c.sortOf t = some s`. -/
def sortEq (c t s : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.one]) (mkApp (mkConst ``Option [Level.zero]) srtTy)
    (mkApp2 (mkConst ``Semantics.sortOf) c t) (someE srtTy s)

/-- `SortsAre c ss ts`. -/
def sortsAreE (c ss ts : Expr) : Expr := mkApp3 (mkConst ``SortsAre) c ss ts

/-! ## Exposing a term's head -/

/-- One step at a time (`whnfCore` and unfolding), stopping at `injNormal a b w`, whose `w` the
kernel's reduction would otherwise inspect. -/
partial def exposeSlow (e : Expr) : MetaM Expr := do
  let e ← whnfCore e
  if e.isAppOfArity ``injNormal 3 || e.isFVar then return e
  if (← ctorHead? e).isSome then return e
  if let .proj _ i s := e then
    let s' ← exposeSlow s
    if let some (_, np, _) ← ctorHead? s' then
      return ← exposeSlow (s'.getAppArgs[np + i]!)
    return e
  match ← unfoldDefinition? e with
  | some e' => exposeSlow e'
  | none => return e

/-- The head of a ground term: a constructor of `GroundTerm`, a variable, or `injNormal a b w`
with `w` stuck. -/
def expose (e : Expr) : MetaM Expr := do
  if e.isAppOfArity ``injNormal 3 then return e
  let w ← kwhnf e
  if w.isFVar then return w
  if let some (n, _, _) ← ctorHead? w then
    if n.getPrefix == ``GroundTerm then return w
  -- stuck: only an injection of a stuck term is worth unfolding step by step
  if (e.find? (·.isConstOf ``injNormal)).isSome || (e.find? (·.isConstOf ``Tm.inj)).isSome then
    exposeSlow e
  else return w

/-- `Tm.val (Tm.mk x)` is x. -/
def clean (e : Expr) : Expr :=
  if e.isAppOfArity ``Tm.val 2 then
    let a := e.appArg!
    if a.isAppOfArity ``Tm.mk 2 then a.appArg! else e
  else e

/-! ## Matching a left-hand side -/

structure St where
  c : Expr
  σ : Array (Option Expr)
  deferred : Array (Expr × Expr) := #[]
  ctorCache : Std.HashMap Nat Bool := {}
  exposeCache : Std.HashMap Expr Expr := {}
  natCache : Std.HashMap Expr Nat := {}
  listCache : Std.HashMap Expr (Array Expr) := {}

abbrev MM := StateRefT St MetaM

/-- `listElems`, remembered. -/
def listElemsM (e : Expr) : MM (Array Expr) := do
  if let some l := (← get).listCache[e]? then return l
  let l ← listElems e
  modify fun s => { s with listCache := s.listCache.insert e l }
  return l

/-- `expose`, remembered across the rules tried on one term. -/
def exposeM (e : Expr) : MM Expr := do
  if let some w := (← get).exposeCache[e]? then return w
  let w ← expose e
  modify fun s => { s with exposeCache := s.exposeCache.insert e w }
  return w

/-- `natOf`, remembered. -/
def natOfM (e : Expr) : MM Nat := do
  if let .lit (.natVal n) := e then return n
  if let some n := (← get).natCache[e]? then return n
  let n ← natOf e
  modify fun s => { s with natCache := s.natCache.insert e n }
  return n

def isCtorN (f : Expr) (n : Nat) : MM Bool := do
  if let some b := (← get).ctorCache[n]? then return b
  let b ← kwhnf (mkApp2 (mkConst ``Semantics.isCtor) (← get).c f)
  let r := b.isConstOf ``Bool.true
  modify fun s => { s with ctorCache := s.ctorCache.insert n r }
  return r

def bindVar (i : Nat) (u : Expr) : MM Unit := do
  let s ← get
  if h : i < s.σ.size then
    match s.σ[i] with
    | none => set { s with σ := s.σ.set i (some (clean u)) }
    | some e =>
      match Kernel.isDefEq (← getEnv) (← getLCtx) e u with
      | .ok true => pure ()
      | _ => throwError "variable {i} is bound to two different terms:{indentExpr e}\nand{indentExpr u}"
  else throwError "variable {i} is beyond the rule's variables"

def mapSyms : MetaM (Nat × Nat × Nat) := do
  return (← natOf (mkConst ``mapUnit), ← natOf (mkConst ``mapElem), ← natOf (mkConst ``mapConcat))

partial def mt (p u : Expr) : MM Unit := do
  let p ← kwhnf p
  let args := p.getAppArgs
  match p.getAppFn.constName? with
  | some ``Term.var => bindVar (← natOfM args[0]!) u
  | some ``Term.as => bindVar (← natOfM args[1]!) u; mt args[0]! u
  | some ``Term.dv =>
    let w ← exposeM u
    unless w.isAppOfArity ``GroundTerm.dv 2 do
      throwError "the literal pattern{indentExpr p}\ndoes not meet{indentExpr u}"
    unless (← natOfM args[0]!) == (← natOfM w.getAppArgs[0]!) do
      throwError "the literal pattern{indentExpr p}\ndoes not meet{indentExpr w}"
    match Kernel.isDefEq (← getEnv) (← getLCtx) args[1]! w.getAppArgs[1]! with
    | .ok true => pure ()
    | _ => throwError "the literal pattern{indentExpr args[1]!}\ndoes not meet{indentExpr w.getAppArgs[1]!}\n(rewrite it to its value first)"
  | some ``Term.inj =>
    let a ← natOfM args[0]!
    let b ← natOfM args[1]!
    if u.isAppOfArity ``injNormal 3 then
      let ua := u.getAppArgs
      unless (← natOfM ua[0]!) == a && (← natOfM ua[1]!) == b do
        throwError "the injection pattern{indentExpr p}\ndoes not meet{indentExpr u}"
      mt args[2]! ua[2]!
    else
      let w ← exposeM u
      if w.isAppOfArity ``injNormal 3 then return ← mt p w
      unless w.isAppOfArity ``GroundTerm.inj 3 do
        throwError "the injection pattern{indentExpr p}\ndoes not meet{indentExpr u}"
      let wa := w.getAppArgs
      unless (← natOfM wa[1]!) == b do
        throwError "the injection pattern{indentExpr p}\ndoes not meet{indentExpr w}"
      if (← natOfM wa[0]!) == a then mt args[2]! wa[2]!
      else
        -- `inj{a', b}(t)` is `injNormal a b (inj{a', a}(t))`, a value of sort a only where a' < a
        let sub ← kwhnf (mkApp3 (mkConst ``subsortB) (← get).c wa[0]! args[0]!)
        unless sub.isConstOf ``Bool.true do
          throwError "the injection pattern{indentExpr p}\ndoes not meet{indentExpr w}"
        mt args[2]! (mkApp3 (mkConst ``GroundTerm.inj) wa[0]! args[0]! wa[2]!)
  | some ``Term.app =>
    let f ← natOfM args[0]!
    let (mu, me, mc) := (← natOfM (mkConst ``mapUnit), ← natOfM (mkConst ``mapElem), ← natOfM (mkConst ``mapConcat))
    if f == mu || f == me || f == mc then
      modify fun s => { s with deferred := s.deferred.push (p, u) }
    else if ← isCtorN args[0]! f then
      let w ← exposeM u
      unless w.isAppOfArity ``GroundTerm.ctor 2 do
        throwError "the constructor pattern{indentExpr p}\ndoes not meet{indentExpr u}"
      unless (← natOfM w.getAppArgs[0]!) == f do
        throwError "the constructor pattern{indentExpr p}\ndoes not meet{indentExpr u}"
      let ps ← listElems args[1]!
      let us ← listElemsM w.getAppArgs[1]!
      unless ps.size == us.size do throwError "arity mismatch at{indentExpr p}"
      for (q, v) in ps.zip us do mt q v
    else throwError "fire matches constructors, injections and map patterns; not{indentExpr p}"
  | _ => throwError "not a pattern:{indentExpr p}"

/-- The value of a pattern whose variables are bound (a map key). -/
partial def instSyn (p : Expr) : MM (Option Expr) := do
  let p ← kwhnf p
  let args := p.getAppArgs
  match p.getAppFn.constName? with
  | some ``Term.var => return (← get).σ[← natOf args[0]!]?.join
  | some ``Term.as => instSyn args[0]!
  | some ``Term.dv => return some (mkApp2 (mkConst ``GroundTerm.dv) args[0]! args[1]!)
  | some ``Term.inj => return (← instSyn args[2]!).map (mkApp3 (mkConst ``injNormal) args[0]! args[1]!)
  | some ``Term.app =>
    let mut vs := #[]
    for q in ← listElems args[1]! do
      match ← instSyn q with
      | some v => vs := vs.push v
      | none => return none
    return some (mkApp2 (mkConst ``GroundTerm.ctor) args[0]! (← mkListLit gtTy vs.toList))
  | _ => return none

/-- The elements `(K, V)`, the rests and the units of a flattened map pattern. -/
partial def flatten (p : Expr) : MM (Array (Expr × Expr) × Array Expr) := do
  let p ← kwhnf p
  let (mu, me, mc) ← mapSyms
  if p.isAppOfArity ``Term.app 2 then
    let f ← natOf p.getAppArgs[0]!
    let qs ← listElems p.getAppArgs[1]!
    if f == mc && qs.size == 2 then
      let (e1, r1) ← flatten qs[0]!
      let (e2, r2) ← flatten qs[1]!
      return (e1 ++ e2, r1 ++ r2)
    if f == me && qs.size == 2 then return (#[(qs[0]!, qs[1]!)], #[])
    if f == mu then return (#[], #[])
  return (#[], #[p])

/-- `K |-> V M` (any arrangement of elements and at most one rest) against a map: each element's
key is the value of a bound pattern; its entry is found by `GroundTerm.cmp`, evaluated by the
kernel (closed keys), the rest takes the other entries. -/
def mapMatch (p u : Expr) : MM Unit := do
  let (elems, rests) ← flatten p
  let w ← expose u
  unless w.isAppOfArity ``GroundTerm.map 2 do
    throwError "the map pattern{indentExpr p}\nmeets a term that is not a map literal{indentExpr u}"
  let s := w.getAppArgs[0]!
  let mut rem : Array (Expr × Expr) := #[]
  for e in ← listElems w.getAppArgs[1]! do
    let e' ← kwhnf e
    unless e'.isAppOfArity ``_root_.Prod.mk 4 do throwError "not an entry:{indentExpr e}"
    rem := rem.push (e'.getAppArgs[2]!, e'.getAppArgs[3]!)
  for (kp, vp) in elems do
    let some k ← instSyn kp
      | throwError "the key of{indentExpr kp}\nis not determined by the rest of the pattern: give it with `fire i with [(var, value)]`"
    let mut found : Option Nat := none
    for h : j in [0:rem.size] do
      let b ← kwhnf (mkApp2 (mkConst ``keyEq) k rem[j].1)
      if b.isConstOf ``Bool.true then found := some j
    let some j := found | throwError "no entry of the map has the key{indentExpr k}"
    mt vp rem[j]!.2
    rem := rem.eraseIdx! j
  let entries ← rem.toList.mapM fun (k, v) => pure (mkApp4 (mkConst ``_root_.Prod.mk [Level.zero, Level.zero]) gtTy gtTy k v)
  match rests.toList with
  | [] => unless rem.isEmpty do throwError "the map has entries the pattern does not take"
  | [r] => mt r (mkApp2 (mkConst ``GroundTerm.map) s (← mkListLit entryTy entries))
  | _ => throwError "a map pattern with two rests is not matched by `fire`"

def matchLhs (lhs u : Expr) : MM Unit := do
  mt lhs u
  let mut todo := (← get).deferred
  modify fun s => { s with deferred := #[] }
  while !todo.isEmpty do
    let mut next := #[]
    let mut progress := false
    for (p, v) in todo do
      try mapMatch p v; progress := true
      catch e =>
        if todo.size == 1 then throw e
        next := next.push (p, v)
    todo := next ++ (← get).deferred
    modify fun s => { s with deferred := #[] }
    if !progress && !todo.isEmpty then
      for (p, v) in todo do mapMatch p v

/-! ## The successor -/

/-- The right-hand side's value under the substitution: constructors built, injections normalized
where the injected term's head is known, function calls evaluated by the kernel. -/
partial def ev (n : Expr) (sub : Expr) (t : Expr) : MM Expr := do
  let t ← kwhnf t
  let args := t.getAppArgs
  match t.getAppFn.constName? with
  | some ``Term.var =>
    let some v := (← get).σ[← natOf args[0]!]?.join
      | throwError "variable {args[0]!} of the right-hand side is not bound by the match"
    return v
  | some ``Term.dv => return mkApp2 (mkConst ``GroundTerm.dv) args[0]! args[1]!
  | some ``Term.inj =>
    let w ← ev n sub args[2]!
    let x ← expose w
    if x.isAppOfArity ``GroundTerm.inj 3 then
      return mkApp3 (mkConst ``GroundTerm.inj) x.getAppArgs[0]! args[1]! x.getAppArgs[2]!
    if let some (nm, _, _) ← ctorHead? x then
      if nm.getPrefix == ``GroundTerm then
        return mkApp3 (mkConst ``GroundTerm.inj) args[0]! args[1]! w
    return mkApp3 (mkConst ``injNormal) args[0]! args[1]! w
  | some ``Term.app =>
    let f ← natOf args[0]!
    if ← isCtorN args[0]! f then
      let mut vs := #[]
      for q in ← listElems args[1]! do vs := vs.push (← ev n sub q)
      return mkApp2 (mkConst ``GroundTerm.ctor) args[0]! (← mkListLit gtTy vs.toList)
    let r ← kdeep (mkApp4 (mkConst ``Exec.evalT) (← get).c n sub t)
    if r.isAppOfArity ``Option.some 2 then
      let r' := r.appArg!
      if r'.isAppOfArity ``Option.some 2 then return r'.appArg!
      throwError "the call{indentExpr t}\nis undefined at the substitution"
    throwError "the call{indentExpr t}\nhas no value within the fuel (set_option fire.fuel)"
  | _ => throwError "fire does not evaluate{indentExpr t}"

/-! ## Sorts -/

/-- Every variable of `t` is of a type the evaluation of a sort does not inspect (Int, Nat, Bool,
String). -/
def closedEnough (t : Expr) : MetaM Bool := do
  for fv in (collectFVars {} t).fvarIds do
    let ty ← whnfR (← instantiateMVars (← fv.getType))
    unless ty.isConstOf ``Int || ty.isConstOf ``Nat || ty.isConstOf ``Bool || ty.isConstOf ``String do
      return false
  return true

/-- A hypothesis `c.sortOf x = some s'` with s' the number s. -/
def findSortHyp (x : Expr) (s : Nat) : MetaM (Option Expr) := do
  (← getLCtx).findDeclM? fun d => do
    if d.isImplementationDetail then return none
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.eq? | return none
    unless l.isAppOfArity ``Semantics.sortOf 2 && l.appArg! == x do return none
    unless r.isAppOfArity ``Option.some 2 do return none
    try
      if (← natOf r.appArg!) == s then return some d.toExpr else return none
    catch _ => return none

mutual
  /-- A proof of `c.sortOf t = some s`. -/
  partial def sortProof (c t s : Expr) : MetaM Expr := do
    let t := clean t
    if ← closedEnough t then
      return ← kdefeq (mkApp (mkConst ``Option [Level.zero]) srtTy) (mkApp2 (mkConst ``Semantics.sortOf) c t)
        (someE srtTy s)
    let sn ← natOf s
    if t.isFVar then
      let some h ← findSortHyp t sn | throwError "fire: no hypothesis `c.sortOf {t} = some {sn}`"
      return h
    let w ← expose t
    if w.isFVar then
      let some h ← findSortHyp w sn | throwError "fire: no hypothesis `c.sortOf {w} = some {sn}`"
      return h
    if w.isAppOfArity ``GroundTerm.ctor 2 then
      let f := w.getAppArgs[0]!
      let tsL := w.getAppArgs[1]!
      let look := mkApp2 (mkConst ``lookupSig) (mkApp (mkConst ``Semantics.ctorSigs) c) f
      let sig ← kdeep look
      unless sig.isAppOfArity ``Option.some 2 do throwError "fire: no constructor{indentExpr f}"
      let k := sig.appArg!
      let ka := k.getAppArgs
      unless (← natOf ka[2]!) == sn do
        throwError "fire: the constructor{indentExpr f}\nhas sort {← natOf ka[2]!}, not {sn}"
      let hk ← kdefeq (mkApp (mkConst ``Option [Level.zero]) (mkConst ``CtorSig)) look sig
      let hts ← sortsAreProof c (← listElems ka[1]!) (← listElems tsL)
      return mkAppN (mkConst ``sortOf_ctor_of) #[c, f, tsL, k, hk, hts]
    if w.isAppOfArity ``GroundTerm.inj 3 then
      let wa := w.getAppArgs
      let hab ← kdefeq (mkConst ``Bool) (mkApp3 (mkConst ``subsortB) c wa[0]! wa[1]!) (mkConst ``Bool.true)
      let hn ← kdefeq (mkConst ``Bool) (mkApp (mkConst ``GroundTerm.isInj) wa[2]!) (mkConst ``Bool.false)
      let ht ← sortProof c wa[2]! wa[0]!
      return mkAppN (mkConst ``sortOf_inj_of) #[c, wa[0]!, wa[1]!, wa[2]!, hab, hn, ht]
    throwError "fire: no sort for{indentExpr t}"
  /-- A proof of `SortsAre c ss ts`. -/
  partial def sortsAreProof (c : Expr) (ss ts : Array Expr) : MetaM Expr := do
    unless ss.size == ts.size do throwError "fire: arity mismatch in a sort check"
    let mut pf := mkConst ``True.intro
    let mut ssL ← mkListLit srtTy []
    let mut tsL ← mkListLit gtTy []
    for j in (List.range ss.size).reverse do
      let s := ss[j]!
      let t := ts[j]!
      let h ← sortProof c t s
      pf := mkApp4 (mkConst ``And.intro) (sortEq c t s) (sortsAreE c ssL tsL) h pf
      ssL := mkApp3 (mkConst ``List.cons [Level.zero]) srtTy s ssL
      tsL := mkApp3 (mkConst ``List.cons [Level.zero]) gtTy t tsL
    return pf
end

/-! ## One step -/

/-- The package namespace of a semantics `NS.c`. -/
def nsOf (c : Expr) : Option Name :=
  match c.getAppFn.constName? with
  | some n => if n.isStr && n.getString! == "c" then some n.getPrefix else none
  | none => none

/-- The rule lemma `c.rules[i]? = some r` and the rule r, as a term. -/
def ruleOf (c : Expr) (i : Nat) : MetaM (Expr × Expr) := do
  if let some ns := nsOf c then
    let nm := ns ++ Name.mkSimple s!"rule{i}"
    if let some ci := (← getEnv).find? nm then
      let some (_, _, r) := ci.type.eq? | throwError "{nm} is not an equation"
      unless r.isAppOfArity ``Option.some 2 do throwError "{nm} is not `= some r`"
      return (mkConst nm, r.appArg!)
  let rulesI := mkApp2 (mkConst ``ruleAt) c (natE i)
  let r ← kdeep rulesI
  unless r.isAppOfArity ``Option.some 2 do throwError "the definition has no rule {i}"
  let h ← kdefeq (mkApp (mkConst ``Option [Level.zero]) (mkConst ``Rule)) rulesI r
  return (h, r.appArg!)

/-- Fire rule i at the main goal `Runs c u w`; the new goals: `Runs c v w`, then any left by the
`requires`, the `ensures` or the priority. -/
def fireOne (i : Nat) (init : Array (Nat × Expr)) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let ty ← whnfR (← instantiateMVars (← g.getType))
    unless ty.isAppOfArity ``Runs 3 do throwError "fire: the goal is not `Runs c u w`{indentExpr ty}"
    let #[c, u, w] := ty.getAppArgs | unreachable!
    let (hr, r) ← ruleOf c i
    let r ← if r.isAppOfArity ``Rule.mk 9 then pure r else kdeep r
    let #[vars, lhs, req, rhs, ens, prio, _, _, _] := r.getAppArgs | throwError "fire: rule {i} is not a literal"
    let F ← synthInstance (mkApp (mkConst ``FireFacts) c)
    let varsA ← listElems vars
    let mut σ : Array (Option Expr) := Array.replicate varsA.size none
    for (j, t) in init do
      if j < σ.size then σ := σ.set! j (some t)
    let (_, st) ← (matchLhs lhs u).run { c, σ }
    let mut vs := #[]
    for j in [0:varsA.size] do
      match st.σ[j]! with
      | some v => vs := vs.push v
      | none => throwError "fire: rule {i}'s variable {j} is not determined by the match: give it with `fire {i} with [({j}, value)]`"
    let vsL ← mkListLit gtTy vs.toList
    let sub := mkApp (mkConst ``sub) vsL
    let fuel := natE (fire.fuel.get (← getOptions))
    let (v, _) ← (ev fuel sub rhs).run st
    -- the proofs
    let hσ ← sortsAreProof c varsA vs
    let hu ← kdefeq optGt (mkApp3 (mkConst ``Term.instP) c sub lhs) (someE gtTy u)
    let pairs := mkApp3 (mkConst ``Term.aliasPairsP) c sub lhs
    let pTy := mkApp2 (mkConst ``_root_.Prod [Level.zero, Level.zero]) optGt optGt
    let lTy := mkApp (mkConst ``List [Level.zero]) optGt
    let fstE := mkApp2 (mkConst ``_root_.Prod.fst [Level.zero, Level.zero]) optGt optGt
    let sndE := mkApp2 (mkConst ``_root_.Prod.snd [Level.zero, Level.zero]) optGt optGt
    let ha ← kdefeq lTy (mkApp4 (mkConst ``List.map [Level.zero, Level.zero]) pTy optGt fstE pairs)
      (mkApp4 (mkConst ``List.map [Level.zero, Level.zero]) pTy optGt sndE pairs)
    let mut newGoals : Array MVarId := #[]
    let req' ← kwhnf req
    let hq ← if req'.isAppOfArity ``Option.none 1 then pure (mkConst ``True.intro) else
      let t := req'.appArg!
      let ev := mkApp4 (mkConst ``Exec.evalT) c fuel sub t
      let trueV := someE optGt (someE gtTy (mkApp (mkConst ``bool) (mkConst ``Bool.true)))
      let r ← kdeep ev
      let bOf : Option Expr :=
        if r.isAppOfArity ``Option.some 2 && r.appArg!.isAppOfArity ``Option.some 2 then
          let x := r.appArg!.appArg!
          if x.isAppOfArity ``GroundTerm.dv 2 && x.appArg!.isAppOfArity ``Lit.bool 1 then
            some x.appArg!.appArg! else none
        else none
      match bOf with
      | none => throwError "fire: rule {i}'s `requires` has no Boolean value:{indentExpr r}"
      | some b =>
        if b.isConstOf ``Bool.true then kdefeq optOptGt ev trueV
        else
          let hb ← mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) b (mkConst ``Bool.true)) `requires
          newGoals := newGoals.push hb.mvarId!
          let bV := someE optGt (someE gtTy (mkApp (mkConst ``bool) b))
          let h1 ← kdefeq optOptGt ev bV
          pure (mkAppN (mkConst ``req_of_bool) #[ev, b, h1, hb])
    let he ← kdefeq optOptGt (mkApp4 (mkConst ``Exec.evalT) c fuel sub rhs) (someE optGt (someE gtTy v))
    let ens' ← kwhnf ens
    let hens ← if ens'.isAppOfArity ``Option.none 1 then pure (mkConst ``True.intro) else
      let t := ens'.appArg!
      let ev := mkApp4 (mkConst ``Exec.evalT) c fuel sub t
      let trueV := someE optGt (someE gtTy (mkApp (mkConst ``bool) (mkConst ``Bool.true)))
      let r ← kdeep ev
      let bOf : Option Expr :=
        if r.isAppOfArity ``Option.some 2 && r.appArg!.isAppOfArity ``Option.some 2 then
          let x := r.appArg!.appArg!
          if x.isAppOfArity ``GroundTerm.dv 2 && x.appArg!.isAppOfArity ``Lit.bool 1 then
            some x.appArg!.appArg! else none
        else none
      match bOf with
      | none => throwError "fire: rule {i}'s `ensures` has no Boolean value:{indentExpr r}"
      | some b =>
        if b.isConstOf ``Bool.true then kdefeq optOptGt ev trueV
        else
          let hb ← mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) b (mkConst ``Bool.true)) `ensures
          newGoals := newGoals.push hb.mvarId!
          let bV := someE optGt (someE gtTy (mkApp (mkConst ``bool) b))
          let h1 ← kdefeq optOptGt ev bV
          pure (mkAppN (mkConst ``req_of_bool) #[ev, b, h1, hb])
    let prioN ← natOf prio
    let minN ← natOf (mkApp2 (mkConst ``FireFacts.minPrio) c F)
    let hprio ← if prioN ≤ minN then
        let hle ← kdefeq (mkConst ``Bool) (mkApp2 (mkConst ``Nat.ble) (mkApp (mkConst ``Rule.prio) r)
          (mkApp2 (mkConst ``FireFacts.minPrio) c F)) (mkConst ``Bool.true)
        pure (mkAppN (mkConst ``FireFacts.noPrio) #[c, F, r, hle, u])
      else
        let hp ← mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``PrioOK) c r u) `priority
        newGoals := newGoals.push hp.mvarId!
        pure hp
    let step := mkAppN (mkConst ``stepsTo_fire) #[c, F, natE i, r, hr, vsL, u, v, hσ, hu, ha, fuel, hq, he, hens, hprio]
    let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``Runs) c v w) (← g.getTag)
    g.assign (mkAppN (mkConst ``Runs.cons) #[c, u, v, w, step, g'])
    replaceMainGoal (g'.mvarId! :: newGoals.toList)

syntax fireRule := num <|> ident

/-- `fire i j …`: steps by the rules i, j, … (numbers, or rule lemmas `c.rules[i]? = some r`) from
the goal `Runs c u w`, each leaving `Runs c v w` for its successor v; `with σ`, a list of
(variable, value) pairs the match starts from. -/
syntax (name := fireTac) "fire" (ppSpace colGt fireRule)+ (" with " term)? : tactic

def ruleIndex (stx : Syntax) : TacticM Nat := do
  match stx[0] with
  | `($n:num) => return n.getNat
  | `($id:ident) =>
    let nm ← realizeGlobalConstNoOverloadWithInfo id
    let ci ← getConstInfo nm
    let some (_, l, _) := ci.type.eq? | throwError "{nm} is not a rule lemma"
    natOf l.appArg!
  | _ => throwUnsupportedSyntax

elab_rules : tactic
  | `(tactic| fire $rs:fireRule* $[with $σ?]?) => do
    let init ← match σ? with
      | none => pure #[]
      | some σ => withMainContext do
        let ty := mkApp (mkConst ``List [Level.zero]) (mkApp2 (mkConst ``_root_.Prod [Level.zero, Level.zero]) (mkConst ``Nat) gtTy)
        let e ← instantiateMVars (← elabTermEnsuringType σ ty)
        let mut out := #[]
        for p in ← listElems e do
          let p ← kwhnf p
          out := out.push (← natOf p.getAppArgs[2]!, p.getAppArgs[3]!)
        pure out
    for r in rs do
      fireOne (← ruleIndex r) init

/-- The rule term of rule i (the package's rule lemma's, or the kernel's normal form). -/
def ruleTerm (c : Expr) (i : Nat) : MetaM Expr := do
  if let some ns := nsOf c then
    if let some ci := (← getEnv).find? (ns ++ Name.mkSimple s!"rule{i}") then
      if let some (_, _, r) := ci.type.eq? then
        if r.isAppOfArity ``Option.some 2 then return r.appArg!
  let r ← kdeep (mkApp2 (mkConst ``ruleAt) c (natE i))
  unless r.isAppOfArity ``Option.some 2 do throwError "the definition has no rule {i}"
  return r.appArg!

/-- Whether rule i applies to u: its left-hand side matches and its `requires` evaluates to true
(`some false`/`some true`); `none` where the `requires`' value is a Boolean the kernel leaves open. -/
def applies (c u : Expr) (i : Nat) : MM (Option Bool) := do
  let r ← ruleTerm c i
  let #[vars, lhs, req, _, _, _, _, _, _] := r.getAppArgs | return some false
  let n := (← listElems vars).size
  let st0 ← get
  set { st0 with σ := Array.replicate n none, deferred := #[] }
  let ok ← try matchLhs lhs u; pure true
    catch _ => pure false
  let st ← get
  unless ok do return some false
  let mut vs := #[]
  for j in [0:n] do
    match st.σ[j]! with
    | some v => vs := vs.push v
    | none => return none
  -- the values' sorts, where the kernel decides them
  for (v, s) in vs.zip (← listElems vars) do
    if ← closedEnough v then
      let b ← kwhnf (mkApp2 (mkConst ``sortIs) (mkApp2 (mkConst ``Semantics.sortOf) c v) s)
      unless b.isConstOf ``Bool.true do return some false
  let req' ← kwhnf req
  if req'.isAppOfArity ``Option.none 1 then return some true
  let sub := mkApp (mkConst ``sub) (← mkListLit gtTy vs.toList)
  let r ← kdeep (mkApp4 (mkConst ``Exec.evalT) c (natE (fire.fuel.get (← getOptions))) sub req'.appArg!)
  if r.isAppOfArity ``Option.some 2 && r.appArg!.isAppOfArity ``Option.some 2 then
    let x := r.appArg!.appArg!
    if x.isAppOfArity ``GroundTerm.dv 2 && x.appArg!.isAppOfArity ``Lit.bool 1 then
      let b := x.appArg!.appArg!
      if b.isConstOf ``Bool.true then return some true
      if b.isConstOf ``Bool.false then return some false
      return none
  return some false

/-- `fire? n`: up to n steps (default 1000), each by the one rule that applies (its left-hand side
matches and its `requires` is true); stops where none or several apply, or where a `requires`'
value is open, and suggests the `fire` line of the steps taken. A search, for writing a proof (it
tries every rule at every step, so a long one wants `set_option maxHeartbeats 0`); the proof keeps
the `fire` line it suggests. -/
elab "fire?" n?:(ppSpace num)? : tactic => do
  let max := (n?.map (·.getNat)).getD 1000
  let mut taken : Array Nat := #[]
  let mut why := s!"after {max} steps"
  for _ in [0:max] do
    let g ← getMainGoal
    let found ← g.withContext do
      let ty ← whnfR (← instantiateMVars (← g.getType))
      unless ty.isAppOfArity ``Runs 3 do throwError "fire?: the goal is not `Runs c u w`"
      let #[c, u, _] := ty.getAppArgs | unreachable!
      let nr ← natOf (mkApp2 (mkConst ``List.length [Level.zero]) (mkConst ``Rule) (mkApp (mkConst ``Semantics.rules) c))
      let go : MM (Array Nat × Array Nat) := do
        let mut yes : Array Nat := #[]
        let mut open_ : Array Nat := #[]
        for i in [0:nr] do
          match ← applies c u i with
          | some true => yes := yes.push i
          | none => open_ := open_.push i
          | some false => pure ()
        pure (yes, open_)
      let (r, _) ← go.run { c, σ := #[] }
      pure r
    match found with
    | (#[i], #[]) => fireOne i #[]; taken := taken.push i
    | (yes, open_) =>
      why := if yes.isEmpty && open_.isEmpty then "no rule applies"
        else s!"rules {yes} apply, rules {open_} match with a `requires` left open"
      break
  logInfo m!"fire? ({why}): fire{String.join (taken.toList.map (s!" {·}"))}"

/-- `run_end`: closes `Runs c u w` where the kernel finds u and w equal. -/
elab "run_end" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let ty ← whnfR (← instantiateMVars (← g.getType))
    unless ty.isAppOfArity ``Runs 3 do throwError "run_end: the goal is not `Runs c u w`"
    let #[c, u, w] := ty.getAppArgs | unreachable!
    let h ← kdefeq gtTy u w
    g.assign (mkAppN (mkConst ``Runs.of_eq_refl) #[c, u, w, h])
    replaceMainGoal []

/-- `run_by h`: with `h : Runs c u' w'` where the kernel finds u and u' equal, leaves `Runs c w' w`. -/
elab "run_by " h:term : tactic => do
  let g ← getMainGoal
  g.withContext do
    let ty ← whnfR (← instantiateMVars (← g.getType))
    unless ty.isAppOfArity ``Runs 3 do throwError "run_by: the goal is not `Runs c u w`"
    let #[c, u, w] := ty.getAppArgs | unreachable!
    let hE ← instantiateMVars (← elabTerm h none)
    let hTy ← whnfR (← instantiateMVars (← inferType hE))
    unless hTy.isAppOfArity ``Runs 3 do throwError "run_by: the term is not `Runs c u' w'`"
    let #[_, u', w'] := hTy.getAppArgs | unreachable!
    let he ← kdefeq gtTy u u'
    let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``Runs) c w' w) (← g.getTag)
    g.assign (mkAppN (mkConst ``Runs.by_run) #[c, u, u', w', w, he, hE, g'])
    replaceMainGoal [g'.mvarId!]

/-- `ksort`: proves `c.sortOf t = some s`, down to hypotheses on the free terms t holds. -/
elab "ksort" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let some (_, l, r) := ty.eq? | throwError "ksort: not `c.sortOf t = some s`"
    unless l.isAppOfArity ``Semantics.sortOf 2 && r.isAppOfArity ``Option.some 2 do
      throwError "ksort: not `c.sortOf t = some s`"
    g.assign (← sortProof l.appFn!.appArg! l.appArg! r.appArg!)
    replaceMainGoal []

/-! ## Inverting a configuration's sort -/

def hasGroundFVar (t : Expr) : MetaM Bool := return !(← closedEnough t)

partial def invert (c t s pf : Expr) : StateT (Array (Expr × Expr × Expr)) MetaM Unit := do
  let t := clean t
  unless ← hasGroundFVar t do return
  if t.isFVar then modify (·.push (t, s, pf)); return
  let w ← expose t
  if w.isFVar then modify (·.push (w, s, pf)); return
  if w.isAppOfArity ``GroundTerm.ctor 2 then
    let f := w.getAppArgs[0]!
    let tsL := w.getAppArgs[1]!
    let look := mkApp2 (mkConst ``lookupSig) (mkApp (mkConst ``Semantics.ctorSigs) c) f
    let sig ← kdeep look
    unless sig.isAppOfArity ``Option.some 2 do return
    let k := sig.appArg!
    let hk ← kdefeq (mkApp (mkConst ``Option [Level.zero]) (mkConst ``CtorSig)) look sig
    let pts := mkAppN (mkConst ``sortsAre_of_ctor) #[c, f, tsL, s, k, pf, hk]
    let ss ← listElems k.getAppArgs[1]!
    let ts ← listElems tsL
    let mut rest := pts
    let mut ssL := k.getAppArgs[1]!
    let mut tsL' := tsL
    for j in [0:min ss.size ts.size] do
      let ssT ← mkListLit srtTy (ss.toList.drop (j + 1))
      let tsT ← mkListLit gtTy (ts.toList.drop (j + 1))
      let a := sortEq c ts[j]! ss[j]!
      let b := sortsAreE c ssT tsT
      invert c ts[j]! ss[j]! (mkApp3 (mkConst ``And.left) a b rest)
      rest := mkApp3 (mkConst ``And.right) a b rest
      ssL := ssT; tsL' := tsT
    return
  if w.isAppOfArity ``GroundTerm.inj 3 then
    let wa := w.getAppArgs
    invert c wa[2]! wa[0]! (mkAppN (mkConst ``sortOf_of_inj) #[c, wa[0]!, wa[1]!, wa[2]!, s, pf])

/-- `config_sorts hx`: from `hx : x.val = t`, x a configuration, the hypotheses
`hX : c.sortOf X = some s` for the free terms X that t holds below constructors and injections. -/
elab "config_sorts " h:ident : tactic => do
  let g ← getMainGoal
  g.withContext do
    let hE ← elabTerm h none
    let hTy ← instantiateMVars (← inferType hE)
    let some (_, l, t) := hTy.eq? | throwError "config_sorts: not `x.val = t`"
    let x := l.appArg!
    let xTy ← whnf (← inferType x)
    let c := xTy.appFn!.appArg!
    let _ := c
    let cE := (← whnfR (← inferType x)).getAppArgs
    let c ← match cE with
      | #[c, _] => pure c
      | _ => throwError "config_sorts: {x} is not a configuration"
    let top := mkConst ``topCellSort
    -- `c.sortOf t = some topCellSort` from `x.property`
    let prop := mkApp3 (mkConst ``Subtype.property [Level.one]) gtTy
      (mkLambda `t .default gtTy (sortEq c (mkBVar 0) top)) x
    let motive := mkLambda `z .default gtTy (sortEq c (mkBVar 0) top)
    let pf := mkApp4 (mkConst ``Eq.mp [Level.zero]) (sortEq c l top) (sortEq c t top)
      (mkApp6 (mkConst ``congrArg [Level.one, Level.one]) gtTy (mkSort Level.zero) l t motive hE) prop
    let (_, hyps) ← (invert c t top pf).run #[]
    let mut g := g
    for (fv, s, p) in hyps do
      let nm := Name.mkSimple ("h" ++ (← fv.fvarId!.getUserName).toString)
      g ← g.assert nm (sortEq c fv s) p
      let (_, g') ← g.intro1P
      g := g'
    replaceMainGoal [g]

end KCore.FireTac
