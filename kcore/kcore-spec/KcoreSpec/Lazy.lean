/-
  KCore. The arguments a short-circuiting evaluation may leave unevaluated (checked layer; the
  obligation is a conjunct of `Obligations`, Obligations.lean).

  Evaluation is strict (Evaluation.lean): a hook application, `ite{S}` among them, evaluates every
  argument, and an undefined argument makes it undefined, as in matching logic, where a symbol
  applied to ⊥ is ⊥. An evaluation that short-circuits reads `ite(C, A, B)` as A when C is true
  without evaluating B, and `false andBool B` as false without evaluating B. The two readings
  differ exactly where such a skipped argument has no value. This module lists the places where
  that can happen and decides, where it can, that it cannot:
  - `lazyOccs c`: every occurrence, in the `requires` and right-hand sides of rules, function
    clauses, of a symbol evaluated as one of `lazyHooks` (`_andBool_`,
    `_andThenBool_`, `_orBool_`, `_orElseBool_`, `_impliesBool_`, `ite`), each with its guard (the
    first argument), the guard's value under which the argument is not needed, and the argument;
  - `definedArg`: the argument is well sorted and built from variables, domain values,
    injections, constructors, the interpreted symbols defined at every argument list of their
    sorts (all but `partialHooks`), `ite{S}`, and the functions declared `[total]`; its soundness,
    under the totality of those functions (`TotalsDefined`), is `definedArg_sound` (LazySound.lean);
  - `lazyObligations c`: the occurrences `definedArg` does not confirm. Each is a named
    obligation (`LazyOcc.Holds`): where the occurrence is reached (`Semantics.Reached`) and its
    guard has the value under which the argument is skipped, the argument has a value. Under it,
    the strict result at the occurrence is the short-circuit one (LazySound.lean, `iteParam_true`,
    `andBool_false` and their companions).
-/
import KcoreSpec.DefinitionWf
import KcoreSpec.Step

set_option autoImplicit false

namespace KCore

/-- Where an occurrence lies: the `requires`, the right-hand side or the `ensures` of the rule of
index `i`, or the `requires` or the right-hand side of the clause of index `j` of the function
`f`. -/
inductive LazySite where
  | ruleReq (i : Nat)
  | ruleRhs (i : Nat)
  | ruleEns (i : Nat)
  | clauseReq (f : Sym) (j : Nat)
  | clauseRhs (f : Sym) (j : Nat)
  | clauseEns (f : Sym) (j : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- An occurrence of a symbol whose argument `skipped` a short-circuiting evaluation does not
evaluate when the first argument, `guard`, has the value `skipWhen`. `vars` are the variable
sorts of the rule or clause at `site`; `path` the argument positions leading from the root of the
`requires` or right-hand side to the occurrence (an injection's or alias's inner term is its
position 0); `pos` the position of `skipped` among the occurrence's arguments. -/
structure LazyOcc where
  site : LazySite
  vars : List Srt
  path : List Nat
  sym : Sym
  guard : Term
  skipWhen : Bool
  pos : Nat
  skipped : Term
  deriving Repr, Inhabited

/-- The interpreted symbols whose arguments a short-circuiting evaluation may skip. -/
def lazyHooks : List Sym := [boolAnd, boolAndThen, boolOr, boolOrElse, boolImplies, kIte]

/-- The arguments of the hook `g` applied to `ts` that a short-circuiting evaluation may skip, as
(guard, the guard's value under which the argument is skipped, position, argument):
`B₁ andBool B₂`, `B₁ andThenBool B₂`, `B₁ impliesBool B₂`: B₂ when B₁ is false;
`B₁ orBool B₂`, `B₁ orElseBool B₂`: B₂ when B₁ is true; `ite(C, A, B)`: A when C is false, B
when C is true. -/
def skippable (g : Sym) : List Term → List (Term × Bool × Nat × Term)
  | [a, b] =>
    if g == boolAnd || g == boolAndThen || g == boolImplies then [(a, false, 1, b)]
    else if g == boolOr || g == boolOrElse then [(a, true, 1, b)] else []
  | [c, a, b] => if g == kIte then [(c, false, 1, a), (c, true, 2, b)] else []
  | _ => []

namespace Semantics
variable (c : Semantics)

/-- The hook of `lazyHooks` evaluation reads `f` as: `f` itself when it is one and not a
constructor, or the registry hook a parameter symbol is implemented by (`ite{S}`, by `kIte`), when
`f` is neither a constructor nor an interpreted symbol (`EvalTerm.param`). -/
def lazyHookOf (f : Sym) : Option Sym :=
  if lazyHooks.contains f then (if c.isCtor f then none else some f)
  else match c.lookupParam f with
    | some k => if (k.impl.any lazyHooks.contains) && !c.isCtor f && !isHook f then k.impl else none
    | none => none

mutual
  /-- The occurrences in a term at `path` of the `requires` or right-hand side at `site`. -/
  def occsOf (site : LazySite) (vars : List Srt) (path : List Nat) : Term → List LazyOcc
    | .app f ts =>
      (match c.lazyHookOf f with
        | some g => (skippable g ts).map fun (gd, w, i, t) => ⟨site, vars, path, f, gd, w, i, t⟩
        | none => []) ++ occsOfList site vars path 0 ts
    | .inj _ _ t => occsOf site vars (path ++ [0]) t
    | .as t _ => occsOf site vars (path ++ [0]) t
    | _ => []
    termination_by structural t => t
  def occsOfList (site : LazySite) (vars : List Srt) (path : List Nat) : Nat → List Term → List LazyOcc
    | _, [] => []
    | i, t :: ts => occsOf site vars (path ++ [i]) t ++ occsOfList site vars path (i + 1) ts
    termination_by structural _ ts => ts
end

/-- The occurrences in a `requires`, if any. -/
def occsOfReq (site : LazySite) (vars : List Srt) : Option Term → List LazyOcc
  | some t => c.occsOf site vars [] t
  | none => []

/-- Every occurrence: in each rule's `requires`, right-hand side and `ensures` (by the rule's
index), and in each function clause's `requires`, right-hand side and `ensures` (by the function
and the clause's index). -/
def lazyOccs : List LazyOcc :=
  (c.rules.zipIdx.flatMap fun (r, i) =>
    c.occsOfReq (.ruleReq i) r.vars r.req ++
      (c.occsOf (.ruleRhs i) r.vars [] r.rhs ++ c.occsOfReq (.ruleEns i) r.vars r.ens)) ++
  c.fns.flatMap fun fn =>
    fn.clauses.zipIdx.flatMap fun (cl, j) =>
      c.occsOfReq (.clauseReq fn.label j) cl.vars cl.req ++
        (c.occsOf (.clauseRhs fn.label j) cl.vars [] cl.rhs ++ c.occsOfReq (.clauseEns fn.label j) cl.vars cl.ens)

end Semantics

/-! ## The decider -/

namespace Semantics
variable (c : Semantics)

/-- The signature of `ite{S}`: `Bool, S, S → S`. -/
def iteSig (k : CtorSig) : Bool := k.args == [Srt.bool, k.result, k.result]

/-- A head whose application is defined wherever its arguments are, at values of its argument
sorts: a constructor; an interpreted symbol other than `partialHooks`; a parameter symbol
implemented by `kIte` at the signature `Bool, S, S → S` (`ite{S}`); a function declared `[total]`
(a generated sort predicate among them). -/
def definedHead (f : Sym) : Bool :=
  c.isCtor f || (isHook f && !partialHooks.contains f) ||
  (!isHook f && match c.lookupParam f with
    | some k => k.impl == some kIte && iteSig k.sig
    | none => (c.lookupFn f).any (·.total))

mutual
  /-- A term over the heads `definedHead` admits, variables, domain values and injections. -/
  def definedTerm : Term → Bool
    | .var _ => true
    | .dv _ _ => true
    | .inj _ _ t => definedTerm t
    | .as _ _ => false
    | .app f ts => c.definedHead f && definedTerms ts
    termination_by structural t => t
  def definedTerms : List Term → Bool
    | [] => true
    | t :: ts => definedTerm t && definedTerms ts
    termination_by structural ts => ts
end

/-- The term `t` over the variables `vars` evaluates to a value under every well-sorted
substitution (`definedArg_sound`, given `TotalsDefined`): it is well sorted as a right-hand side
(`rhsCtx`), the values of the sorts the interpreted symbols read have their shapes (`shapesOK`),
and it is a `definedTerm`. -/
def definedArg (vars : List Srt) (t : Term) : Bool :=
  (sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t).isSome && c.shapesOK && c.definedTerm t

/-- The occurrences whose skipped argument `definedArg` does not show defined: the named lazy
obligations (`Obligations`, Obligations.lean). -/
def lazyObligations : List LazyOcc :=
  c.lazyOccs.filter fun o => !c.definedArg o.vars o.skipped

/-! ## The obligation -/

/-- What `definedArg_sound` reads of the functions declared `[total]` (a generated sort predicate
among them): each is defined at every argument list of its argument sorts. It has the form of the
second conjunct of `Obligations`, for every such function rather than those `totalOK` does not
confirm. -/
def TotalsDefined : Prop :=
  ∀ f fn, c.lookupFn f = some fn → fn.total = true →
    ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c f vs (some v)

/-- The substitutions under which the `requires` or right-hand side at a site is evaluated: σ
well sorted for the rule's or clause's variables and
- a rule's `requires`: its left-hand side denotes a configuration under σ (`Step` reads it there,
  and `NotApplies` there for the rules of larger priority);
- a rule's right-hand side and its `ensures`: moreover the `requires` is true and no rule of a
  smaller priority applies to the configuration (`Step`);
- a clause's `requires`: its patterns denote an argument list of the function's argument sorts
  (`Fails` reads it there, and `Eval.clause`);
- a clause's right-hand side and its `ensures`: moreover the `requires` is true and every clause of a smaller
  priority fails at the argument list (`Eval.clause`).
Argument lists of the function's argument sorts are those a call reads, the values of its
well-sorted arguments (subject reduction, `EvalTerm.sorted`). -/
def Reached : LazySite → Subst → Prop
  | .ruleReq i, σ => ∃ r, c.rules[i]? = some r ∧ c.WellSorted r.vars σ ∧
      ∃ x, c.sortOf x = some topCellSort ∧ PatVal c σ r.lhs x
  | .ruleRhs i, σ => ∃ r, c.rules[i]? = some r ∧ c.WellSorted r.vars σ ∧
      ∃ x, c.sortOf x = some topCellSort ∧ PatVal c σ r.lhs x ∧
        (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
        ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x
  | .ruleEns i, σ => ∃ r, c.rules[i]? = some r ∧ c.WellSorted r.vars σ ∧
      ∃ x, c.sortOf x = some topCellSort ∧ PatVal c σ r.lhs x ∧
        (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
        ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x
  | .clauseReq f j, σ => ∃ fn cl, c.lookupFn f = some fn ∧ fn.clauses[j]? = some cl ∧
      c.WellSorted cl.vars σ ∧ ∃ vs, c.sortsOf vs = some fn.args ∧ PatVals c σ cl.pats vs
  | .clauseRhs f j, σ => ∃ fn cl, c.lookupFn f = some fn ∧ fn.clauses[j]? = some cl ∧
      c.WellSorted cl.vars σ ∧ (∃ vs, c.sortsOf vs = some fn.args ∧ PatVals c σ cl.pats vs ∧
        ∀ cl' ∈ fn.clauses, cl'.prio < cl.prio → Fails c vs cl') ∧
        ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))
  | .clauseEns f j, σ => ∃ fn cl, c.lookupFn f = some fn ∧ fn.clauses[j]? = some cl ∧
      c.WellSorted cl.vars σ ∧ (∃ vs, c.sortsOf vs = some fn.args ∧ PatVals c σ cl.pats vs ∧
        ∀ cl' ∈ fn.clauses, cl'.prio < cl.prio → Fails c vs cl') ∧
        ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))

end Semantics

/-- The obligation of an occurrence: wherever it is reached and its guard evaluates to the value
under which the argument is skipped, the skipped argument evaluates to a value. Where the guard
has the other value the argument is used by both readings; where the occurrence is not reached
it is evaluated by neither. -/
def LazyOcc.Holds (c : Semantics) (o : LazyOcc) : Prop :=
  ∀ σ, c.Reached o.site σ → EvalTerm c σ o.guard (some (bool o.skipWhen)) →
    ∃ v, EvalTerm c σ o.skipped (some v)

end KCore
