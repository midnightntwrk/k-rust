/-
  The C2 evidence of the pair `[owise]` x `simplification` (status inert) on the fixture
  c3-owise-simp: `rule f(X) => X requires X >Int 0` and `rule f(_) => 0 [owise]` beside
  `rule f(f(X)) => f(X) [simplification]`.
  The text is `f2-examples/c3-owise-simp.kompile.kore`: the kompiled text that
  `test/constructs/fixtures/c3-owise-simp/kompile.txt` records, with its paths restored.
  Run from the package root: `lake env lean -j1 test/C3OwiseSimp.lean`. Every statement is on the
  literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  - `coreOK`; `simp_class`: the reader leaves the `simplification` sentence (axiom 202, `//@ 337`
    of kore.txt) inert, class `simplification`; `simp_text`: its pattern is
    `\implies{R}(\top{R}(), \equals{SortInt{}, R}(f(f(X)), \and{SortInt{}}(f(X), \top{SortInt{}}())))`.
  - `eval_all`: `f(n) = n` for n > 0 and `f(n) = 0` otherwise, for every H: at n > 0 the equation
    with the `requires` applies (`n >Int 0` is `true` by the hook's value); elsewhere it fails
    (`n >Int 0` is `false`) and the `[owise]` equation applies.
  - `simp_ev`: the sentence is entailed by Γ at values, for every H (TIE-0 row 18, the direction
    `Ev` of its class): at an integer n, `f(n)` is a non-negative m with `f(m) = m`
    (`InertEvUser.EqnU.entailed`, with the table that `eval_all` gives).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.C3OwiseSimp

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/c3-owise-simp.kompile.kore"
definition_of defn from "f2-examples/c3-owise-simp.kompile.kore"
user_axioms U from "f2-examples/c3-owise-simp.kompile.kore" module "C3-OWISE-SIMP"

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
noncomputable abbrev simpAx : AxiomDecl := U.ax202

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

/-- `f`'s value at n. -/
def g (n : Int) : Int := if 0 < n then n else 0

/-- The `[owise]` clause: `f(_) => 0`. -/
noncomputable abbrev cl0 : Clause := fn.clauses[1]'(by decide +kernel)
/-- The clause with the `requires`: `f(X) => X requires X >Int 0`. -/
noncomputable abbrev cl1 : Clause := fn.clauses[0]'(by decide +kernel)

theorem clauses_len : fn.clauses.length = 2 := by decide +kernel
theorem cl0_parts : cl0.vars = [Srt.int] ∧ cl0.pats = [.var 0] ∧ cl0.req = none ∧
    cl0.rhs = .dv Srt.int (.int 0) ∧ cl0.pre = .top ∧ cl0.ens = none ∧ cl0.prio = 200 :=
  ⟨by decide +kernel, rfl, rfl, rfl, rfl, rfl, by decide +kernel⟩
theorem cl1_parts : cl1.vars = [Srt.int] ∧ cl1.pats = [.var 0] ∧
    cl1.req = some (.app intGt [.var 0, .dv Srt.int (.int 0)]) ∧
    cl1.rhs = .var 0 ∧ cl1.pre = .top ∧ cl1.ens = none ∧ cl1.prio = 50 :=
  ⟨by decide +kernel, rfl, rfl, rfl, rfl, rfl, by decide +kernel⟩
theorem cl1_least : fn.clauses.all (fun cl' => !decide (cl'.prio < cl1.prio)) = true := by decide +kernel
theorem isCtor_gt : c.isCtor intGt = false := by decide +kernel

theorem int2_at (x y : Int) (g : Int → Int → Option GroundTerm) : int2 [int x, int y] g = g x y := by
  simp [int2, asInt, int]

/-- `n >Int 0` has the value `0 < n` at any σ giving the variable 0 the value n. -/
theorem gt_at (H : HookParams) {σ : Subst} {n : Int} (hl : σ.lookup 0 = some (int n)) :
    EvalTerm (cH H) σ (.app intGt [.var 0, .dv Srt.int (.int 0)]) (some (bool (decide (0 < n)))) := by
  refine .hook (rs := [some (int n), some (int 0)]) (show (cH H).isCtor intGt = false from isCtor_gt) rfl
    (.cons (by rw [← hl]; exact .var) (.cons .dv .nil)) (fun vs hvs => ?_) (fun h => by cases h)
  cases hvs
  exact Semantics.hookRes_of_value (by rw [Det.hook_intGt, int2_at])

theorem wellSorted_at (H : HookParams) (n : Int) {vars : List Srt} (hv : vars = [Srt.int]) :
    (cH H).WellSorted vars [(0, int n)] := by
  intro i s hi
  rw [hv] at hi
  match i, hi with
  | 0, hi => cases hi; exact ⟨int n, rfl, rfl⟩
  | k + 1, hi => simp at hi

/-- **`f(n) = g n` at every integer n, for every H.** -/
theorem eval_all (H : HookParams) (n : Int) : Eval (cH H) f [int n] (some (int (g n))) := by
  obtain ⟨v0, p0, q0, r0, e0, s0, o0⟩ := cl0_parts
  obtain ⟨v1, p1, q1, r1, e1, s1, o1⟩ := cl1_parts
  by_cases hn : 0 < n
  · rw [show g n = n by simp [g, hn]]
    have hm : PatVals (cH H) [(0, int n)] cl1.pats [int n] := by rw [p1]; exact .cons (.var rfl) .nil
    refine .clause (cl := cl1) (σ := [(0, int n)]) (hfnH H) (List.getElem_mem _) (wellSorted_at H n v1) hm
      (fun t ht => ?_) (by rw [e1]; exact .top)
      (fun cl' hcl' _ hlt => absurd hlt (by simpa using List.all_eq_true.mp cl1_least cl' hcl'))
      (by rfl) (by rw [r1]; exact .var) (fun t ht => by rw [s1] at ht; cases ht) (Clause.holds_postTop (by rfl) _)
    rw [q1] at ht; cases ht
    have := gt_at H (σ := [(0, int n)]) (n := n) rfl
    simpa [hn] using this
  · rw [show g n = 0 by simp [g, hn]]
    have hm : PatVals (cH H) [(0, int n)] cl0.pats [int n] := by rw [p0]; exact .cons (.var rfl) .nil
    refine .clause (cl := cl0) (σ := [(0, int n)]) (hfnH H) (List.getElem_mem _) (wellSorted_at H n v0) hm
      (fun t ht => by rw [q0] at ht; cases ht) (by rw [e0]; exact .top) (fun cl' hcl' _ hlt => ?_)
      (by rfl) (by rw [r0]; exact .dv) (fun t ht => by rw [s0] at ht; cases ht) (Clause.holds_postTop (by rfl) _)
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hcl'
    have hi2 : i = 0 ∨ i = 1 := by rw [clauses_len] at hi; omega
    rcases hi2 with rfl | rfl
    · change Fails (cH H) [int n] cl1
      refine .intro fun σ' _ hpv => ?_
      rw [p1] at hpv
      cases hpv with
      | cons h1 _ =>
        cases h1 with
        | var hl =>
          refine .intro q1 (gt_at H hl) ?_
          simp [hn, KCore.bool]
    · exact absurd hlt (Nat.lt_irrefl _)

/-- The value table of `f`: `f(n) = g n`. -/
def fTable : InertEvUser.ValTable := fun s =>
  if s = f then some fun ws => match ws with
    | [.dv _ (.int n)] => some (int (g n))
    | _ => none
  else none

/-- **The table is `Eval`'s**, for every H. -/
theorem table_ok (H : HookParams) : InertEvUser.TableOK (cH H) fTable := by
  intro s g' fn' ws hg _ hfn' hws
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

theorem g_g (n : Int) : g (g n) = g n := by
  unfold g; by_cases hn : 0 < n <;> simp [hn]

/-- `f(f(n)) = f(n)` at every integer n, under the table. -/
theorem holds (H : HookParams) : InertEvUser.EqnU.Holds (cH H) fTable E := by
  intro σ hσ _
  obtain ⟨v, hv, hvs⟩ := hσ 0 _ rfl
  rw [Semantics.sortOf_withHooks _ _ noRaw] at hvs
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c hvs
  have ha : InertEvUser.appU (cH H) fTable f = fun ws => match ws with
      | [.dv _ (.int n)] => some (int (g n))
      | _ => none := InertEvUser.appU_fn hkf (by simp [fTable])
  simp only [E, InertEvUser.valU, InertEvUser.valUList, allSome, hv, ha, Option.bind_some, Option.map_some]
  show some (int (g (g n))) = some (int (g n))
  rw [g_g]

/-- **The simplification sentence is entailed by Γ at values**, for every H. -/
theorem simp_ev (H : HookParams) : EntailsAtValues (cH H) simpAx (trS simpAx).pat := by
  obtain ⟨hp, hsv, htr, hfv⟩ := simp_text
  rw [htr]
  refine InertEvUser.EqnU.entailed (coreOKH H) (hokH H) (table_ok H) E ((typed_wh H).trans typed) (holds H)
    simpAx (hp.trans (pattern_wh H).symm) hsv (fun i hi => ?_)
  have : i = 0 := by simp [E] at hi; omega
  subst this
  rw [vkey_wh H]; exact hfv

end KCore.C3OwiseSimp

#check @KCore.C3OwiseSimp.simp_ev
#print axioms KCore.C3OwiseSimp.simp_class
#print axioms KCore.C3OwiseSimp.simp_text
#print axioms KCore.C3OwiseSimp.eval_all
#print axioms KCore.C3OwiseSimp.simp_ev
