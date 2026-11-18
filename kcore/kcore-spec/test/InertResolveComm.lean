/-
  The C2 evidence of the inert compile pass resolveComm (E7) on fixture e2-simplification: the
  simplification `rule g(X, Y) => g(Y, X) [simplification, comm]`, with `g(X, Y) => X +Int Y` the
  one equation of `g`, is written a second time by the pass with the arguments of its left side
  swapped, `g(Y, X) => g(Y, X)` (axiom 216).
  The text is `f2-examples/e2-simplification.kompile.kore`: the kompiled text that
  `test/constructs/fixtures/e2-simplification/kompile.txt` records, with its paths restored.
  Run from the package root: `lake env lean -j1 test/InertResolveComm.lean`. Every statement is on
  the literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  - `coreOK`; `simp_class`: the reader leaves the sentence inert, class `simplification`;
    `simp_text`: its pattern is `E`'s, `\equals(g(Y, X), \and(g(Y, X), \top))` under `\top`.
  - `eval_all`: `g(a, b) = a + b` at every pair of integers, for every H.
  - `simp_ev`: the sentence is entailed by Γ at values, for every H (`InertEvUser.EqnU.entailed`):
    its two sides are one term.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.InertResolveComm

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e2-simplification.kompile.kore"
definition_of defn from "f2-examples/e2-simplification.kompile.kore"
user_axioms U from "f2-examples/e2-simplification.kompile.kore" module "E2-SIMPLIFICATION"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem hok : c.ok = true := by decide_cheap
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok
theorem shapesOK_c : c.shapesOK = true := by decide_cheap

def g : Sym := 385

theorem names : c.symName g = "Lblg" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[1]'(by decide +kernel)

theorem hfn : c.lookupFn g = some fn := rfl
theorem hfnH (H : HookParams) : (cH H).lookupFn g = some fn := by rw [Semantics.lookupFn_withHooks]; exact hfn
theorem fn_args : fn.args = [Srt.int, Srt.int] := by decide +kernel
theorem hkg : lookupSig hookSigs g = none := by decide +kernel

/-! ## The sentence -/

/-- `g(Y, X) => g(Y, X)`: the simplification `g(X, Y) => g(Y, X)` with the arguments of its left
side swapped, as kompile writes it for `comm`. -/
def E : LibEv.Eqn :=
  ⟨[("VarY", Srt.int), ("VarX", Srt.int)], Srt.int, none, .app g [.var 0, .var 1], .app g [.var 0, .var 1]⟩

/-- The reader's class of the sentence. -/
theorem simp_class : Parse.classifyShape (.axiom U.ax216.ax) = .inert .simplification := by decide +kernel

/-- **The sentence is `E`'s pattern**, over the one sort variable `R`, `VarY` and `VarX` free. -/
theorem simp_text : U.ax216.ax.pattern = E.pattern c ∧ U.ax216.ax.sortVars = [Rv] ∧
    (trS U.ax216).pat = (trAxiom [] [] U.ax216).pat ∧
    LibEv.vkey c E.vars 0 ∈ freeOf [] U.ax216.ax.pattern ∧ LibEv.vkey c E.vars 1 ∈ freeOf [] U.ax216.ax.pattern := by
  decide +kernel

kernel_rfl pattern_wh : ∀ H : HookParams, E.pattern (cH H) = E.pattern c
kernel_rfl vkey_wh : ∀ (H : HookParams) (i : Nat), LibEv.vkey (cH H) E.vars i = LibEv.vkey c E.vars i

/-! ## `g`'s value at every pair of integers -/

/-- `g`'s one clause: `g(X, Y) => X +Int Y`. -/
noncomputable abbrev cl0 : Clause := fn.clauses[0]'(by decide +kernel)

theorem clauses_len : fn.clauses.length = 1 := by decide +kernel
theorem cl0_vars : cl0.vars = [Srt.int, Srt.int] := by decide +kernel
theorem cl0_pats : cl0.pats = [.var 0, .var 1] := rfl
theorem cl0_req : cl0.req = none := rfl
theorem cl0_rhs : cl0.rhs = .app intAdd [.var 0, .var 1] := rfl
theorem cl0_pre : cl0.pre = .top := rfl
theorem cl0_ens : cl0.ens = none := rfl
theorem cl0_least : fn.clauses.all (fun cl' => !decide (cl'.prio < cl0.prio)) = true := by decide +kernel
theorem isCtor_add : c.isCtor intAdd = false := by decide +kernel

theorem int2_at (x y : Int) (k : Int → Int → Option GroundTerm) : int2 [int x, int y] k = k x y := by
  simp [int2, asInt, int]

theorem hook_add (vs : List GroundTerm) : hook intAdd vs = some (int2 vs fun x y => some (int (x + y))) := rfl

/-- `X +Int Y` has the value `a + b` at the substitution giving the variables 0 and 1 the values a, b. -/
theorem add_at (H : HookParams) (a b : Int) :
    EvalTerm (cH H) [(0, int a), (1, int b)] (.app intAdd [.var 0, .var 1]) (some (int (a + b))) := by
  refine .hook (rs := [some (int a), some (int b)]) (show (cH H).isCtor intAdd = false from isCtor_add) rfl
    (.cons .var (.cons .var .nil)) (fun vs hvs => ?_) (fun h => by cases h)
  cases hvs
  exact Semantics.hookRes_of_value (by rw [hook_add, int2_at])

/-- **`g(a, b) = a + b` at every pair of integers, for every H.** -/
theorem eval_all (H : HookParams) (a b : Int) : Eval (cH H) g [int a, int b] (some (int (a + b))) := by
  have hσ : (cH H).WellSorted cl0.vars [(0, int a), (1, int b)] := by
    intro i s hi
    rw [cl0_vars] at hi
    match i, hi with
    | 0, hi => cases hi; exact ⟨int a, rfl, rfl⟩
    | 1, hi => cases hi; exact ⟨int b, rfl, rfl⟩
    | k + 2, hi => simp at hi
  have hm : PatVals (cH H) [(0, int a), (1, int b)] cl0.pats [int a, int b] := by
    rw [cl0_pats]; exact .cons (.var rfl) (.cons (.var rfl) .nil)
  exact .clause (cl := cl0) (σ := [(0, int a), (1, int b)]) (hfnH H) (List.getElem_mem _) hσ hm
    (fun t ht => by rw [cl0_req] at ht; cases ht) (by rw [cl0_pre]; exact .top)
    (fun cl' hcl' _ hlt => absurd hlt (by simpa using List.all_eq_true.mp cl0_least cl' hcl')) (by rfl)
    (by rw [cl0_rhs]; exact add_at H a b)
    (fun t ht => by rw [cl0_ens] at ht; cases ht) (Clause.holds_postTop (by rfl) _)

/-- The value table of `g`: `g(a, b) = a + b`. -/
def gTable : InertEvUser.ValTable := fun s =>
  if s = g then some fun ws => match ws with
    | [.dv _ (.int a), .dv _ (.int b)] => some (int (a + b))
    | _ => none
  else none

/-- **The table is `Eval`'s**, for every H. -/
theorem table_ok (H : HookParams) : InertEvUser.TableOK (cH H) gTable := by
  intro s k fn' ws hk _ hfn' hws
  by_cases hs : s = g
  · subst hs
    simp only [gTable, ite_true, Option.some.injEq] at hk
    subst hk
    have he : fn' = fn := Option.some.inj (hfn'.symm.trans (hfnH H))
    subst he
    rw [fn_args, Semantics.sortsOf_withHooks _ _ noRaw] at hws
    obtain ⟨w, ws', rfl, hw, hws'⟩ := sortsOf_inv_cons hws
    obtain ⟨w', ws'', rfl, hw', hws''⟩ := sortsOf_inv_cons hws'
    cases sortsOf_inv_nil hws''
    obtain ⟨a, rfl⟩ := shape_int shapesOK_c hw
    obtain ⟨b, rfl⟩ := shape_int shapesOK_c hw'
    exact eval_all H a b
  · simp [gTable, hs] at hk

theorem typed : InertEvUser.EqnU.typed c gTable E = true := by decide +kernel
kernel_rfl typed_wh : ∀ H : HookParams, InertEvUser.EqnU.typed (cH H) gTable E = InertEvUser.EqnU.typed c gTable E

/-- The two sides are one term, so they have one value under the table. -/
theorem holds (H : HookParams) : InertEvUser.EqnU.Holds (cH H) gTable E := fun _ _ _ => rfl

/-- **The sentence is entailed by Γ at values**, for every H. -/
theorem simp_ev (H : HookParams) : EntailsAtValues (cH H) U.ax216 (trS U.ax216).pat := by
  obtain ⟨hp, hsv, htr, hfv0, hfv1⟩ := simp_text
  rw [htr]
  refine InertEvUser.EqnU.entailed (coreOKH H) (hokH H) (table_ok H) E ((typed_wh H).trans typed) (holds H)
    U.ax216 (hp.trans (pattern_wh H).symm) hsv (fun i hi => ?_)
  have : i = 0 ∨ i = 1 := by simp [E] at hi; omega
  rcases this with rfl | rfl
  · rw [vkey_wh H]; exact hfv0
  · rw [vkey_wh H]; exact hfv1

end KCore.InertResolveComm

#check @KCore.InertResolveComm.simp_ev
#print axioms KCore.InertResolveComm.simp_class
#print axioms KCore.InertResolveComm.simp_text
#print axioms KCore.InertResolveComm.eval_all
#print axioms KCore.InertResolveComm.simp_ev
