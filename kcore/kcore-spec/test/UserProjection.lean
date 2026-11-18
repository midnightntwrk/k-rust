/-
  A user sort's projection applied by a rule, read from K 7.1.337 kompile's own KORE. Run from the
  package root: `lake env lean test/UserProjection.lean`.
  - `f2-examples/projuser.kompile.kore` (`projuser.k`): `<k> run(X) => done(project:Exp(X)) </k>`.
    kompile declares `project:Exp` a `function` and states its one equation
    `project:Exp(kseq(inj{Exp,KItem}(V), dotk)) = V`. The reader reads it as a function with that
    equation as its one clause, not as a parameter symbol: for every interpretation H, its value at
    `kseq(inj{Exp,KItem}(e), dotk)` is `e`, for every value e of sort Exp, as the text's equation
    states (`projExp_value`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace ProjUser

definition_of defn from "f2-examples/projuser.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

def projExp : Sym := 390

def exp : Srt := 33

theorem names : c.symName projExp = "Lblproject'Coln'Exp" ∧ c.sortName exp = "Exp" := by decide +kernel

/-- `project:Exp` is no parameter symbol of the semantics. -/
theorem not_param : (c.params.any (·.sig.name == projExp)) = false := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

/-- The text's equation, its one clause: the pattern `kseq(inj{Exp,KItem}(V), dotk)`, no `requires`,
the right side V, no `ensures`, priority 50. -/
def eqnCl : Clause := ⟨[exp], [.app kseq [.inj exp Srt.kitem (.var 0), .app dotk []]], none, .var 0, none, 50, false, [], .top, .top⟩

theorem fn_label : fn.label = projExp := by decide +kernel

theorem fn_clauses : fn.clauses = [eqnCl] := rfl

private theorem hfn : c.lookupFn projExp = some fn := rfl

kernel_rfl isCtor_withHooks : ∀ (c : Semantics) (H : HookParams), (c.withHooks H).isCtor = c.isCtor

theorem kseq_ctor : c.isCtor kseq = true := by decide +kernel
theorem dotk_ctor : c.isCtor dotk = true := by decide +kernel

/-- **The equation's value, for every H**: at `kseq(inj{Exp,KItem}(e), dotk)`, e a value of sort
Exp, `project:Exp` has the value e. -/
theorem projExp_value (H : HookParams) (e : GroundTerm) (he : c.sortOf e = some exp) :
    Eval (c.withHooks H) projExp [.ctor kseq [injNormal exp Srt.kitem e, .ctor dotk []]] (some e) := by
  have hfnH : (c.withHooks H).lookupFn projExp = some fn := by
    rw [Semantics.lookupFn_withHooks]; exact hfn
  have hk := kseq_ctor; have hd := dotk_ctor
  rw [← isCtor_withHooks c H] at hk hd
  refine Eval.clause (cl := eqnCl) (σ := [(0, e)]) hfnH (by rw [fn_clauses]; simp) ?_ ?_
    (fun t ht => nomatch ht) .top ?_ rfl .var (fun t ht => nomatch ht) .top
  · intro i s hs
    cases i with
    | zero => cases hs; exact ⟨e, rfl, by rw [Semantics.sortOf_withHooks _ _ noRaw]; exact he⟩
    | succ i => simp [eqnCl] at hs
  · exact .cons (.ctor hk (.cons (.inj (.var rfl)) (.cons (.ctor hd .nil) .nil))) .nil
  · intro cl' hcl' _ hlt
    rw [fn_clauses] at hcl'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl'
    subst hcl'
    exact absurd hlt (by decide)

end ProjUser

#print axioms ProjUser.projExp_value
#print axioms ProjUser.not_param
