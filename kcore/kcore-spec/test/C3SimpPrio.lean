/-
  The C2 evidence of the pair `simplification` x `priority` (status inert) on the fixture
  c3-simp-prio: `rule f(X) => X [priority(40)]` beside `rule f(f(X)) => f(X) [simplification]`.
  The text is `f2-examples/c3-simp-prio.kompile.kore`: the kompiled text that
  `test/constructs/fixtures/c3-simp-prio/kompile.txt` records, with its paths restored.
  Run from the package root: `lake env lean -j1 test/C3SimpPrio.lean`. Every statement is on the
  literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  - `coreOK`; `simp_class`: the reader leaves the `simplification` sentence (axiom 201, `//@ 336`
    of kore.txt) inert, class `simplification`; `simp_text`: its pattern is
    `\implies{R}(\top{R}(), \equals{SortInt{}, R}(f(f(X)), \and{SortInt{}}(f(X), \top{SortInt{}}())))`.
  - `eval_all`: `f(n) = n` at every integer n, for every H (the equation of priority 40 applies at
    every argument, with no `requires`).
  - `simp_ev`: the sentence is entailed by Γ at values, for every H (TIE-0 row 18, the direction
    `Ev` of its class): at an integer n, `f(f(n))` and `f(n)` are both n
    (`InertEvUser.EqnU.entailed`, with the table `f(n) = n` that `eval_all` gives).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.C3SimpPrio

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/c3-simp-prio.kompile.kore"
definition_of defn from "f2-examples/c3-simp-prio.kompile.kore"
user_axioms U from "f2-examples/c3-simp-prio.kompile.kore" module "C3-SIMP-PRIO"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem coreOK : c.coreOK = true := by decide +kernel
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem hok : c.ok = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok
theorem shapesOK_c : c.shapesOK = true := by decide +kernel

def f : Sym := 384

theorem names : c.symName f = "Lblf" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

theorem hfn : c.lookupFn f = some fn := rfl
theorem hfnH (H : HookParams) : (cH H).lookupFn f = some fn := by rw [Semantics.lookupFn_withHooks]; exact hfn
theorem fn_args : fn.args = [Srt.int] := by decide +kernel
theorem hkf : lookupSig hookSigs f = none := by decide +kernel

/-! ## The sentence -/

/-- The simplification sentence. -/
noncomputable abbrev simpAx : AxiomDecl := U.ax201

/-- The reader's class of the sentence. -/
theorem simp_class : Parse.classify (.axiom simpAx.ax) = .inert .simplification := by decide +kernel

/-- `f(f(X)) => f(X)` as an equation over `f`. -/
def E : LibEv.Eqn := ⟨[("VarX", Srt.int)], Srt.int, none, .app f [.app f [.var 0]], .app f [.var 0]⟩

/-- **The sentence is `E`'s pattern**, over the one sort variable `R`, `VarX` free in it. -/
theorem simp_text : simpAx.ax.pattern = E.pattern c ∧ simpAx.ax.sortVars = [Rv] ∧
    (trS simpAx).pat = (trAxiom [] [] simpAx).pat ∧
    LibEv.vkey c E.vars 0 ∈ freeOf [] simpAx.ax.pattern := by
  decide +kernel

kernel_rfl pattern_wh : ∀ H : HookParams, E.pattern (cH H) = E.pattern c
kernel_rfl vkey_wh : ∀ H : HookParams, LibEv.vkey (cH H) E.vars 0 = LibEv.vkey c E.vars 0

/-! ## `f`'s value at every integer -/

/-- `f`'s one clause: `f(X) => X [priority(40)]`. -/
noncomputable abbrev cl0 : Clause := fn.clauses[0]'(by decide +kernel)

theorem cl0_vars : cl0.vars = [Srt.int] := by decide +kernel
theorem cl0_pats : cl0.pats = [.var 0] := rfl
theorem cl0_req : cl0.req = none := rfl
theorem cl0_rhs : cl0.rhs = .var 0 := rfl
theorem cl0_pre : cl0.pre = .top := rfl
theorem cl0_ens : cl0.ens = none := rfl
theorem cl0_least : fn.clauses.all (fun cl' => !decide (cl'.prio < cl0.prio)) = true := by decide +kernel

/-- **`f(n) = n` at every integer n, for every H**: the clause matches and has no condition. -/
theorem eval_all (H : HookParams) (n : Int) : Eval (cH H) f [int n] (some (int n)) := by
  have hσ : (cH H).WellSorted cl0.vars [(0, int n)] := by
    intro i s hi
    rw [cl0_vars] at hi
    match i, hi with
    | 0, hi => cases hi; exact ⟨int n, rfl, rfl⟩
    | k + 1, hi => simp at hi
  have hm : PatVals (cH H) [(0, int n)] cl0.pats [int n] := by
    rw [cl0_pats]; exact .cons (.var rfl) .nil
  have hr : EvalTerm (cH H) [(0, int n)] cl0.rhs (some (int n)) := by
    rw [cl0_rhs]; exact .var
  exact .clause (cl := cl0) (σ := [(0, int n)]) (hfnH H) (List.getElem_mem _) hσ hm
    (fun t ht => by rw [cl0_req] at ht; cases ht) (by rw [cl0_pre]; exact .top)
    (fun cl' hcl' _ hlt => absurd hlt (by simpa using List.all_eq_true.mp cl0_least cl' hcl')) (by rfl) hr
    (fun t ht => by rw [cl0_ens] at ht; cases ht) (Clause.holds_postTop (by rfl) _)

/-- The value table of `f`: `f(n) = n`. -/
def fTable : InertEvUser.ValTable := fun s =>
  if s = f then some fun ws => match ws with
    | [.dv _ (.int n)] => some (int n)
    | _ => none
  else none

/-- **The table is `Eval`'s**, for every H. -/
theorem table_ok (H : HookParams) : InertEvUser.TableOK (cH H) fTable := by
  intro s g fn' ws hg _ hfn' hws
  by_cases hs : s = f
  · subst hs
    simp only [fTable, ite_true, Option.some.injEq] at hg
    subst hg
    have he : fn' = fn := Option.some.inj (hfn'.symm.trans (hfnH H))
    subst he
    rw [fn_args, Semantics.sortsOf_withHooks _ _ noRaw] at hws
    obtain ⟨w, ws', rfl, hw, hws'⟩ := sortsOf_inv_cons hws
    cases sortsOf_inv_nil hws'
    obtain ⟨n, rfl⟩ := shape_int shapesOK_c hw
    exact eval_all H n
  · simp [fTable, hs] at hg

theorem typed : InertEvUser.EqnU.typed c fTable E = true := by decide +kernel
kernel_rfl typed_wh : ∀ H : HookParams, InertEvUser.EqnU.typed (cH H) fTable E = InertEvUser.EqnU.typed c fTable E

/-- `f(f(n)) = f(n)` at every integer n, under the table. -/
theorem holds (H : HookParams) : InertEvUser.EqnU.Holds (cH H) fTable E := by
  intro σ hσ _
  obtain ⟨v, hv, hvs⟩ := hσ 0 _ rfl
  rw [Semantics.sortOf_withHooks _ _ noRaw] at hvs
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c hvs
  have ha : InertEvUser.appU (cH H) fTable f = fun ws => match ws with
      | [.dv _ (.int n)] => some (int n)
      | _ => none := InertEvUser.appU_fn hkf (by simp [fTable])
  simp only [E, InertEvUser.valU, InertEvUser.valUList, allSome, hv, ha, Option.bind_some, Option.map_some]
  rfl

/-- **The simplification sentence is entailed by Γ at values**, for every H. -/
theorem simp_ev (H : HookParams) : EntailsAtValues (cH H) simpAx (trS simpAx).pat := by
  obtain ⟨hp, hsv, htr, hfv⟩ := simp_text
  rw [htr]
  refine InertEvUser.EqnU.entailed (coreOKH H) (hokH H) (table_ok H) E ((typed_wh H).trans typed) (holds H)
    simpAx (hp.trans (pattern_wh H).symm) hsv (fun i hi => ?_)
  have : i = 0 := by simp [E] at hi; omega
  subst this
  rw [vkey_wh H]; exact hfv

end KCore.C3SimpPrio

#check @KCore.C3SimpPrio.simp_ev
#print axioms KCore.C3SimpPrio.simp_class
#print axioms KCore.C3SimpPrio.simp_text
#print axioms KCore.C3SimpPrio.eval_all
#print axioms KCore.C3SimpPrio.simp_ev
