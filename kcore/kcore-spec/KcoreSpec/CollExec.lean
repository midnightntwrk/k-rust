/-
  KCore, checked layer: an executable step for definitions whose left-hand sides apply collection
  pattern symbols (`PatVal.coll`: lists, sets, cell maps, cell sets, cell lists) besides the map
  pattern symbols and constructors. `Exec.successorsN` (Exec.lean) lists no match for such a
  pattern; `CExec.successorsN` does.

  Matching is in two parts.
  1. **Candidates** (`cmatchP`, `cmatchL`, `pickAll`, `matchSeq`): substitutions extending σ,
     enumerated from the pattern and the value. A constructor pattern matches a constructor term of
     that constructor argument by argument; an injection pattern `inj{a,b}(p)` at `inj{x,b}(u)`
     tries p at `inj{x,a}(u)`, and, when x is a, at u too (so no sort argument is needed to
     know which one `injNormal` produced). A collection pattern (a symbol with a `role`: the unit,
     element or concatenation of a map, set or list, the library's or a parameter's implemented by
     one) is flattened (`flatten`) into its parts: the elements (each with its argument patterns),
     the frames (variables at the concatenation's argument positions) and anything else (`other`).
     The value's items (`content`: a map's entries `[k, v]`, a set's or a list's elements `[e]`)
     are then distributed: for a map or a set, each element chooses an item (`pickAll`, in order,
     each item at most once) and the one frame is bound to the rest (`build`, with the frame
     variable's declared sort as the collection's sort); for a list, the parts take the items in
     order, the one frame the stretch between the elements before and after it (`matchSeq`). A
     pattern with two frames, or with an `other` part, has no candidates. An overloading symbol's
     pattern `f(p̄)` at v (`PatVal.ovl`: v is f's normal form at the values of p̄) matches p̄ at the
     one argument list `ovlArgs c f v` read off v's head.
  2. **The check** (`cmatch`): a candidate is kept when it is well sorted and the patterns, read as
     values under it (`patEval`: a variable's binding, a constructor's term, a map pattern symbol's
     `hook`, a collection pattern symbol's `collVal`), are the arguments. Every substitution
     `cmatch` returns is therefore a match (`PatVals`) whatever the candidates were; which matches
     the candidates reach is the matcher's completeness.

  Evaluation (`evalT`, `evalTs`, `evalF`, `firstClause`) and the successors (`successorsN`) are
  `Exec`'s, with the clauses' and the rules' matches computed by `cmatch`.

  ## Proofs

  Soundness (CollExecSound.lean), completeness of the check (CollExecComplete.lean), of the
  candidates (CollExecMatch.lean), the matcher's completeness from `execReady` (CollExecStep.lean)
  and the step's characterization (CollExecStepIff.lean) are proved; no sorry, no axiom beyond
  `propext`, `Classical.choice`, `Quot.sound`.
  - `cmatch_sound : σ ∈ cmatch c vars ps vs → c.WellSorted vars σ ∧ PatVals c σ ps vs` (no
    hypothesis), from `patEval_sound`;
  - `patEval_complete (hc : MatchCtxO c) : PatVal c σ p v → patEval c σ p = some v`,
    `patEval_congr` (σ read on `varOccs p` only); the sorts of what patterns denote over
    `patCtxAll` are `Det.patVal_sortedAll` (Uniq.lean);
  - `roleVal` (a symbol with a role denotes what the library's symbol of that kind and role builds,
    `Builds`), `collDecomp` (a flattened collection pattern's value is what its parts take, a list's
    in order, a map's or a set's up to order, `Comb`);
  - `cmatchP_complete (hc : MatchCtxO c) (hτ : c.WellSorted vars τ) : ∀ n m σ p v s,
      8 * termSize p ≤ n → readyP c vars m p = true → PatVal c τ p v →
      sortOfTerm c.patCtxAll vars p = some s → Ext σ τ →
      ∃ σ' ∈ cmatchP c vars n σ p v, Ext σ' τ ∧ Ext σ σ' ∧ Binds σ' (varOccs p)`,
    with `cmatchL_complete`, `pickAll_complete`, `matchSeq_complete`;
  - `cmatch_complete (hc : MatchCtxO c) (hτ : c.WellSorted vars τ) (hpv : PatVals c τ ps vs)
      (hr : readyL c vars ps = true) (hb : binds vars.length (varOccsList ps) = true)
      (hss : sortsOfTerms c.patCtxAll vars ps = some ss) :
      ∃ σ₀ ∈ cmatch c vars ps vs, ∀ i < vars.length, σ₀.lookup i = τ.lookup i`;
  - `clauseComplete_of_ready (hr : execReady c = true) : ClauseComplete c`,
    `ruleComplete_of_ready (hr : execReady c = true) : RuleComplete c`;
  - `successors_step_ready (hr : execReady c = true) : y ∈ successors c x.val →
      ∃ h, Step c x ⟨y, h⟩` (and `successorsN_step_ready` at any fuel);
  - `evalT_congr`, `evalT_mono`, `evalT_mono_le`, `EvalTerm.exec`, `Eval.exec` for `CExec.evalT`
    (EvalComplete.lean's, with `CClauseCtx` and `ClauseComplete` for `ClauseCtx` and the matcher);
  - **`step_iff (hr : execReady c = true) (hco : CoherentAll c) (x y : Config c) :
      Step c x y ↔ ∃ n, (CExec.successorsN c n x.val).any (same · y.val) = true`**, the shape of
    `Exec.step_iff_of_ok` (StepIff.lean).

  Not stated: that `successors` at the fixed fuel `Exec.fuel` lists every `Step` successor (no
  fixed fuel suffices in general; `outOfFuel` tells when a listing may be partial). `execReady`
  accepts every one of the corpus's 343 coreOK texts, overloading symbols included; the proofs needed no
  strengthening.

  Notes for later work on these proofs:
  - The injection case reads the pattern's sort: the value p denotes at `inj{a,b}(p)` has sort a,
    so it is not an injection into a sort other than a, and one of the candidates' two tries is
    it. The frame's rest equals its value only because values of well-sorted patterns are
    canonical (`canonI_perm`); a defined `_Map_` or `_Set_` of canonical arguments holds their
    items each once (`union_perm`, `concatS_perm`).
  - Overloading symbols (`PatVal.ovl`, `EvalTerm.ovl`, `EvalTerm.ovlFn`): `patEval` and `evalT`
    compute `norm`, and `evalT` the covering function's value, lifted, where a function the symbol
    overloads covers the arguments (`fnCover`); the
    candidates of `f(p̄)` at v are the argument patterns matched at `ovlArgs c f v`, the one
    argument list at which f's normal form can be v (`ovlArgs_complete`, from
    `OvlLaws.norm_decomp`). The laws of `norm` read `overloadsOK`, which `execReady` holds through
    `matchReadyO` (`MatchCtxO`).
  - In the namespace `KCore.CExec` with `Exec` open, a name of the current namespace wins over
    `Exec`'s; still write `CExec.evalT` (and `evalTs`, `evalF`, `firstClause`) in `simp` sets.
    `simp [matchSeq]` times out: unfold it with `matchSeq_elem`, `matchSeq_frame`. `nomatch h, e`
    parses as `nomatch` on two discriminants: parenthesize `(nomatch h)` in an anonymous
    constructor.
-/
import KcoreSpec.MatchComplete

set_option autoImplicit false

namespace KCore.CExec

open KCore Exec

/-! ## The collection pattern symbols -/

/-- What a collection symbol builds: the empty collection, a one-item collection, or the
concatenation of two. -/
inductive Role where
  | unit
  | elem
  | concat
  deriving DecidableEq, Repr

/-- The library's collection pattern symbols: kind and role. -/
def hookRole (g : Sym) : Option (CollKind × Role) :=
  if g == mapUnit then some (.map, .unit) else if g == mapElem then some (.map, .elem)
  else if g == mapConcat then some (.map, .concat)
  else if g == setUnit then some (.set, .unit) else if g == setElem then some (.set, .elem)
  else if g == setConcat then some (.set, .concat)
  else if g == listUnit then some (.list, .unit) else if g == listElem then some (.list, .elem)
  else if g == listConcat then some (.list, .concat)
  else none

/-- The kind and role of a symbol applied in a pattern, read as `PatVal` reads it: none for a
constructor; a map pattern symbol's (`PatVal.hook`); a collection pattern symbol's (`PatVal.coll`):
the library symbol's, or the hook implementing the parameter. -/
def role (c : Semantics) (g : Sym) : Option (CollKind × Role) :=
  if c.isCtor g then none
  else if patternHooks.contains g then hookRole g
  else if c.isCollPat g then
    if isHook g then hookRole g
    else match c.lookupParam g with
      | some k => k.impl.bind hookRole
      | none => none
  else none

/-- A collection's kind, sort and items: a map's entries as `[k, v]`, a set's or a list's elements
as `[e]`. -/
def content : GroundTerm → Option (CollKind × Srt × List (List GroundTerm))
  | .map s es => some (.map, s, es.map fun e => [e.1, e.2])
  | .set s es => some (.set, s, es.map fun e => [e])
  | .list s es => some (.list, s, es.map fun e => [e])
  | _ => none

/-- The entry of a map item. -/
def pairOf : List GroundTerm → Option (GroundTerm × GroundTerm)
  | [k, v] => some (k, v)
  | _ => none

/-- The element of a set or list item. -/
def oneOf : List GroundTerm → Option GroundTerm
  | [e] => some e
  | _ => none

/-- The collection of kind K and sort s with these items (`content`'s inverse); a range map's, a
map's. -/
def build : CollKind → Srt → List (List GroundTerm) → GroundTerm
  | .map, s, its => .map s (its.filterMap pairOf)
  | .set, s, its => .set s (its.filterMap oneOf)
  | .list, s, its => .list s (its.filterMap oneOf)
  | .rangeMap, s, its => .map s (its.filterMap pairOf)

/-- A part of a flattened collection pattern. -/
inductive Part where
  /-- an element: its symbol's argument patterns -/
  | elem (qs : List Term)
  /-- a frame: a variable at a concatenation's argument -/
  | frame (j : Nat)
  /-- any other pattern at a concatenation's argument -/
  | other (q : Term)
  deriving Repr, Inhabited

/-- The parts of a collection pattern of kind K, in order: concatenations of kind K are opened,
units dropped. `none` for a symbol of kind K applied to the wrong number of arguments. -/
def flatten (c : Semantics) (K : CollKind) : Nat → Term → Option (List Part)
  | 0, _ => none
  | n + 1, .app g ps => match role c g with
    | some (K', r) =>
      if K' == K then match r, ps with
        | .unit, [] => some []
        | .elem, qs => some [.elem qs]
        | .concat, [a, b] => do
          let pa ← flatten c K n a
          let pb ← flatten c K n b
          pure (pa ++ pb)
        | _, _ => none
      else some [.other (.app g ps)]
    | none => some [.other (.app g ps)]
  | _ + 1, .var j => some [.frame j]
  | _ + 1, t => some [.other t]

def Part.elems : List Part → List (List Term)
  | [] => []
  | .elem qs :: ps => qs :: Part.elems ps
  | _ :: ps => Part.elems ps

def Part.frames : List Part → List Nat
  | [] => []
  | .frame j :: ps => j :: Part.frames ps
  | _ :: ps => Part.frames ps

def Part.hasOther : List Part → Bool
  | [] => false
  | .other _ :: _ => true
  | _ :: ps => Part.hasOther ps

/-- The number of elements among the parts. -/
def Part.countElems (ps : List Part) : Nat := (Part.elems ps).length

/-! ## Overloading symbols -/

/-- The symbol and the arguments of a raw application, or of one under an injection. -/
def rawHead : GroundTerm → Option (Sym × List GroundTerm)
  | .ctor h us => some (h, us)
  | .inj _ _ (.ctor h us) => some (h, us)
  | _ => none

/-- The arguments at which the overloading symbol f may denote v: a normal form is `h(ū)`, lifted
to f's result sort, for h f itself or a symbol below it along the overloads, at arguments ū whose
lifts to f's argument sorts are f's arguments (`OvlLaws.norm_decomp`); h and ū are read off v. -/
def ovlArgs (c : Semantics) (f : Sym) (v : GroundTerm) : Option (List GroundTerm) :=
  match c.lookupOvl f, rawHead v with
  | some o, some (h, us) => (lookupSig (c.ctorSigs ++ c.ovlSigs) h).map fun kh => liftAll kh.args o.sig.args us
  | _, _ => none

/-! ## Candidates -/

mutual
  /-- Candidate substitutions extending σ under which the pattern may denote the value (fuel bounds
  the depth). `vars`: the declared sorts of the variables (a frame's collection sort). -/
  def cmatchP (c : Semantics) (vars : List Srt) : Nat → Subst → Term → GroundTerm → List Subst
    | 0, _, _, _ => []
    | _ + 1, σ, .var i, v => (bindVar σ i v).toList
    | _ + 1, σ, .dv s l, v => match v with
      | .dv s' l' => if s == s' && l == l' then [σ] else []
      | _ => []
    | n + 1, σ, .inj a b p, v => match v with
      | .inj x b' u => if b == b' then
          (if x == a then cmatchP c vars n σ p u ++ cmatchP c vars n σ p (.inj x a u)
           else cmatchP c vars n σ p (.inj x a u))
        else []
      | _ => []
    | n + 1, σ, .as p i, v => (cmatchP c vars n σ p v).filterMap (bindVar · i v)
    | n + 1, σ, .app f ps, v =>
      if c.isCtor f then match v with
        | .ctor g vs => if f == g then cmatchL c vars n σ ps vs else []
        | _ => []
      else if c.isOvl f then match ovlArgs c f v with
        | some vs => cmatchL c vars n σ ps vs
        | none => []
      else match role c f, content v with
        | some (K, _), some (K', _, items) =>
          if K == K' then match flatten c K (termSize (.app f ps)) (.app f ps) with
            | some parts =>
              if Part.hasOther parts then [] else
              match K with
              | .list => matchSeq c vars n σ parts items
              | _ => match Part.frames parts with
                | [] => (pickAll c vars n σ (Part.elems parts) items).filterMap fun (σ', rest) =>
                    if rest.isEmpty then some σ' else none
                | [j] => match vars[j]? with
                  | some s => (pickAll c vars n σ (Part.elems parts) items).flatMap fun (σ', rest) =>
                      (bindVar σ' j (build K s rest)).toList
                  | none => []
                | _ => []
            | none => []
          else []
        | _, _ => []
  def cmatchL (c : Semantics) (vars : List Srt) : Nat → Subst → List Term → List GroundTerm → List Subst
    | 0, _, _, _ => []
    | _ + 1, σ, [], [] => [σ]
    | n + 1, σ, p :: ps, v :: vs => (cmatchP c vars n σ p v).flatMap fun σ' => cmatchL c vars n σ' ps vs
    | _ + 1, _, _, _ => []
  /-- Choose an item for each element, in order; each chosen item is removed. -/
  def pickAll (c : Semantics) (vars : List Srt) : Nat → Subst → List (List Term) → List (List GroundTerm) →
      List (Subst × List (List GroundTerm))
    | 0, _, _, _ => []
    | _ + 1, σ, [], its => [(σ, its)]
    | n + 1, σ, qs :: E, its =>
      (List.range its.length).flatMap fun j => match its[j]? with
        | some it => (cmatchL c vars n σ qs it).flatMap fun σ1 => pickAll c vars n σ1 E (its.eraseIdx j)
        | none => []
  /-- The parts of a list pattern take the items in order: an element one item, a frame the items
  up to those the elements after it take. -/
  def matchSeq (c : Semantics) (vars : List Srt) : Nat → Subst → List Part → List (List GroundTerm) → List Subst
    | 0, _, _, _ => []
    | _ + 1, σ, [], [] => [σ]
    | n + 1, σ, .elem qs :: ps, it :: its =>
      (cmatchL c vars n σ qs it).flatMap fun σ1 => matchSeq c vars n σ1 ps its
    | n + 1, σ, .frame j :: ps, its =>
      let k := its.length - Part.countElems ps
      match vars[j]? with
      | some s => (bindVar σ j (build .list s (its.take k))).toList.flatMap fun σ1 =>
          matchSeq c vars n σ1 ps (its.drop k)
      | none => []
    | _ + 1, _, _, _ => []
end

/-! ## The check -/

mutual
  /-- The value of a pattern read as a term under σ, where its variables are bound: a constructor's
  term, a map pattern symbol's hook, a collection pattern symbol's `collVal` (as `PatVal`). -/
  def patEval (c : Semantics) (σ : Subst) : Term → Option GroundTerm
    | .var i => σ.lookup i
    | .dv s l => some (.dv s l)
    | .inj a b p => (patEval c σ p).map (injNormal a b)
    | .as p i => match patEval c σ p, σ.lookup i with
      | some v, some w => if same w v then some v else none
      | _, _ => none
    | .app f ps => match patEvals c σ ps with
      | none => none
      | some vs =>
        if c.isCtor f then some (.ctor f vs)
        else if patternHooks.contains f then (hook f vs).join
        else if c.isCollPat f then c.collVal f vs
        else if c.isOvl f then some (c.norm f vs)
        else none
    termination_by structural t => t
  def patEvals (c : Semantics) (σ : Subst) : List Term → Option (List GroundTerm)
    | [] => some []
    | p :: ps => match patEval c σ p, patEvals c σ ps with
      | some v, some vs => some (v :: vs)
      | _, _ => none
    termination_by structural ts => ts
end

/-- Two lists of values are equal. -/
def sameL : List GroundTerm → List GroundTerm → Bool
  | [], [] => true
  | v :: vs, w :: ws => same v w && sameL vs ws
  | _, _ => false

/-- The candidates' fuel for a pattern list. -/
def cfuel (ps : List Term) : Nat := 8 * termSizeList ps + 8

/-- The matches of the patterns at the values: the candidates that are well sorted and under
which the patterns denote the values. -/
def cmatch (c : Semantics) (vars : List Srt) (ps : List Term) (vs : List GroundTerm) : List Subst :=
  (cmatchL c vars (cfuel ps) [] ps vs).filter fun σ =>
    wellSorted c vars σ && match patEvals c σ ps with
      | some ws => sameL ws vs
      | none => false

/-! ## Evaluation and successors (as `Exec`'s, with `cmatch`) -/

mutual
  /-- `some r`: the result (as `EvalTerm`); `none`: out of fuel or no result. -/
  def evalT (c : Semantics) : Nat → Subst → Term → Option (Option GroundTerm)
    | 0, _, _ => none
    | _ + 1, σ, .var i => some (σ.lookup i)
    | _ + 1, _, .dv s l => some (some (.dv s l))
    | n + 1, σ, .inj a b t => (evalT c n σ t).map (·.map (injNormal a b))
    | _ + 1, _, .as _ _ => none
    | n + 1, σ, .app f ts => do
      let rs ← evalTs c n σ ts
      if c.isCtor f then pure ((allSome rs).map (.ctor f))
      else if isHook f then match allSome rs with
        | none => pure none
        | some vs => c.hookRes f vs
      else if c.isParam f then pure ((allSome rs).bind (c.paramVal f))
      else if c.isOvl f then match allSome rs with
        | none => pure none
        | some vs => (match c.fnCover f vs, c.lookupOvl f with
          | some kg, some o =>
            (evalF c n kg.name (stripAll kg.args o.sig.args vs)).map (·.map (lift kg.result o.sig.result))
          | _, _ => pure (some (c.norm f vs)))
      else match allSome rs with
        | none => pure none
        | some vs => evalF c n f vs
  def evalTs (c : Semantics) : Nat → Subst → List Term → Option (List (Option GroundTerm))
    | 0, _, _ => none
    | _ + 1, _, [] => some []
    | n + 1, σ, t :: ts => do pure ((← evalT c n σ t) :: (← evalTs c n σ ts))
  def evalF (c : Semantics) : Nat → Sym → List GroundTerm → Option (Option GroundTerm)
    | 0, _, _ => none
    | n + 1, f, vs => do
      let fn ← c.lookupFn f
      firstClause c n vs (c.fnRest fn vs) (byPrio fn.clauses)
  /-- As `Exec.firstClause`: the clauses a priority at a time; a candidate whose `requires` is
  true and whose `ensures` and right-hand side have results gives the right-hand side's where the
  `ensures` is `true`, no value where it is something else; where every candidate's `requires` is
  false or undefined, the next priority is tried; otherwise (out of fuel) no result. Where every
  clause fails, the function's rest `fr`. -/
  def firstClause (c : Semantics) : Nat → List GroundTerm → Option GroundTerm → List Clause →
      Option (Option GroundTerm)
    | 0, _, _, _ => none
    | _ + 1, _, fr, [] => some fr
    | n + 1, vs, fr, cl :: rest =>
      let vals := ((cl :: rest).takeWhile (·.prio == cl.prio)).flatMap fun cl' =>
        (cmatch c cl'.vars cl'.pats vs).map fun σ =>
          (cl', σ, match cl'.req with
            | none => some true
            | some t => (evalT c n σ t).map isTrue)
      match vals.findSome? fun (cl', σ, b) => if b == some true then
          (match (match cl'.ens with
            | none => some true
            | some t => (evalT c n σ t).map isTrue) with
          | some true => evalT c n σ cl'.rhs
          | some false => some none
          | none => none)
        else none with
      | some r => some r
      | none =>
        if vals.all (·.2.2 == some false) then
          firstClause c n vs fr ((cl :: rest).dropWhile (·.prio == cl.prio))
        else none
end

/-- A clause's matches at the arguments. -/
def clauseMatches (c : Semantics) (cl : Clause) (vs : List GroundTerm) : List Subst :=
  cmatch c cl.vars cl.pats vs

/-- A rule's predicate the executable step evaluates: `\top`, an `\equals` or an `\in` atom, or a
conjunction of such. -/
def predAtoms : Cond → Bool
  | .top | .equals .. | .mem .. => true
  | .and p q => predAtoms p && predAtoms q
  | _ => false

/-- A predicate's truth value under σ with `n` units of evaluation fuel, as `Holds` states it:
`\top` is true, `\equals` compares its two terms' results (`sameResult`), `\in` asks that and a
value, a conjunction is the conjunction of its two values; `none` where a term ran out of fuel or
the predicate has another shape (`predAtoms`). -/
def predVal (c : Semantics) (n : Nat) (σ : Subst) : Cond → Option Bool
  | .top => some true
  | .equals _ t u => match evalT c n σ t, evalT c n σ u with
    | some r, some r' => some (sameResult r r')
    | _, _ => none
  | .mem _ t u => match evalT c n σ t, evalT c n σ u with
    | some r, some r' => some (r.isSome && sameResult r r')
    | _, _ => none
  | .and p q => match predVal c n σ p, predVal c n σ q with
    | some b, some b' => some (b && b')
    | _, _ => none
  | _ => none

/-- A match from its `requires` value and its `pre` value: `some false` where either is false
(`RuleReqFails` is either), `some true` where both are true, otherwise `none` (out of fuel). -/
def appVal : Option Bool → Option Bool → Option Bool
  | some false, _ => some false
  | _, some false => some false
  | some true, some true => some true
  | _, _ => none

/-- The `requires` value of a rule's match: `some true` where there is none, else its value read
as a Boolean (`none`: out of fuel). -/
def reqVal (c : Semantics) (n : Nat) (r : Rule) (σ : Subst) : Option Bool :=
  match r.req with
  | none => some true
  | some t => (evalT c n σ t).map isTrue

/-- The value of a rule's match: its `requires` and its `pre` (`appVal`). -/
def matchVal (c : Semantics) (n : Nat) (r : Rule) (σ : Subst) : Option Bool :=
  appVal (reqVal c n r σ) (predVal c n σ r.pre)

/-- A rule's matches at x, each with its `requires` and its `pre` (`matchVal`): `some true`
(applies), `some false` (does not), `none` (out of fuel). -/
def ruleMatches (c : Semantics) (n : Nat) (r : Rule) (x : GroundTerm) : List (Subst × Option Bool) :=
  (cmatch c r.vars [r.lhs] [x]).map fun σ => (σ, matchVal c n r σ)

/-- A match's `ensures` (as `Exec.ensVal`): `some true` where there is none, else its value read
as a Boolean (`none`: out of fuel). -/
def ensVal (c : Semantics) (n : Nat) (r : Rule) (σ : Subst) : Option Bool :=
  match r.ens with
  | none => some true
  | some t => (evalT c n σ t).map isTrue

/-- The successors of a configuration with `n` units of evaluation fuel (as `Exec.successorsN`):
among the rules that apply (or might, out of fuel), those of the smallest priority; for each of
their matches whose `requires` and `pre` are `true`, the configuration the right-hand side
evaluates to, where the `ensures` and the `post` are `true`. -/
def successorsN (c : Semantics) (n : Nat) (x : GroundTerm) : List GroundTerm :=
  let ms := c.rules.map fun r => (r, ruleMatches c n r x)
  let applying := ms.filter fun (_, l) => l.any fun (_, b) => b != some false
  match (applying.map (·.1.prio)).min? with
  | none => []
  | some p =>
    (applying.filter (·.1.prio == p)).flatMap fun (r, l) =>
      l.filterMap fun (σ, b) =>
        if b == some true then match evalT c n σ r.rhs with
          | some (some y) =>
            if c.sortOf y == some topCellSort && ensVal c n r σ == some true &&
              predVal c n σ r.post == some true then some y else none
          | _ => none
        else none

/-- The successors at `Exec.fuel`, each once. -/
def successors (c : Semantics) (x : GroundTerm) : List GroundTerm :=
  (successorsN c Exec.fuel x).foldl (fun acc y => if acc.any (same · y) then acc else acc ++ [y]) []

/-- Whether at some match of a rule its `requires` or its `pre` ran out of fuel, or, where both are
`true`, its right-hand side, its `ensures` or its `post`: then an empty or partial successor list
is not a verdict. -/
def outOfFuel (c : Semantics) (n : Nat) (x : GroundTerm) : Bool :=
  c.rules.any fun r => (ruleMatches c n r x).any fun (σ, b) =>
    reqVal c n r σ == none || predVal c n σ r.pre == none ||
      (b == some true && ((evalT c n σ r.rhs).isNone || ensVal c n r σ == none ||
        predVal c n σ r.post == none))

/-! ## Readiness: the patterns the candidates are meant to reach -/

/-- A pattern whose matches the candidates reach (fuel bounds the depth; `termSize` suffices):
constructors, literals, variables, injections, aliases, and collection patterns with at most one
frame, a variable of `vars`, and no other part at a concatenation's argument, their elements'
patterns again such. -/
def readyP (c : Semantics) (vars : List Srt) : Nat → Term → Bool
  | 0, _ => false
  | _ + 1, .var _ => true
  | _ + 1, .dv _ _ => true
  | n + 1, .inj _ _ p => readyP c vars n p
  | n + 1, .as p _ => readyP c vars n p
  | n + 1, .app f ps =>
    if c.isCtor f then ps.all (readyP c vars n)
    else match role c f with
      | some (K, _) => match flatten c K (termSize (.app f ps)) (.app f ps) with
        | some parts => !Part.hasOther parts && decide ((Part.frames parts).length ≤ 1) &&
            (Part.frames parts).all (fun j => (vars[j]?).isSome) &&
            (Part.elems parts).all (·.all (readyP c vars n))
        | none => false
      -- no role: an overloading symbol (`PatVal.ovl`), or a function
      | none => c.isOvl f && ps.all (readyP c vars n)

/-- Each pattern is ready. -/
def readyL (c : Semantics) (vars : List Srt) (ps : List Term) : Bool :=
  ps.all fun p => readyP c vars (termSize p) p

/-- **The readiness check**: the conditions the executable step's theorems read, decidable on the
core: well sorted (`sortedOK`, under `okAll`), `srReady`, `matchReadyO` (`matchReady` with
well-formed overloads, `overloadsOK`, in place of none), every clause's and rule's left-hand
side ready, binding all of its variables, every rule's predicates `\top` or conjunctions of
`\equals` and `\in` atoms (`predAtoms`, which `predVal` evaluates), and no clause `aside`
(`asideFree`: the executable evaluation stops at the first clause that applies, `aside` or not). -/
def execReady (c : Semantics) : Bool :=
  c.sortedOK && c.srReady && c.matchReadyO &&
  c.allFns.all (fun fn => fn.clauses.all fun cl =>
    readyL c cl.vars cl.pats && binds cl.vars.length (varOccsList cl.pats)) &&
  c.rules.all (fun r => readyL c r.vars [r.lhs] && binds r.vars.length (varOccs r.lhs) &&
    predAtoms r.pre && predAtoms r.post) &&
  c.asideFree

/-- A rule of a core `execReady` accepts has predicates `predVal` evaluates and a left side that
binds every variable. -/
theorem rule_atoms_of_execReady {c : Semantics} (hr : execReady c = true) {r : Rule} (hmem : r ∈ c.rules) :
    predAtoms r.pre = true ∧ predAtoms r.post = true ∧ binds r.vars.length (varOccs r.lhs) = true := by
  simp only [execReady, Bool.and_eq_true, List.all_eq_true] at hr
  obtain ⟨⟨⟨-, hb⟩, hpre⟩, hpost⟩ := hr.1.2 r hmem
  exact ⟨hpre, hpost, hb⟩

end KCore.CExec
