/-
  The C2 evidence of the row E2 SIMPLIFICATION(simplification)@simplification (status inert) on the
  fixture e2-simp-true-prio: five functions `fi(X) => X` (i from 0 to 4), each beside a true
  simplification `fi(fi(X)) => fi(X)` carrying the key in one of its written forms: `[simplification]`
  (kompile writes `simplification{}("")`), and `[simplification(10)]`, `(50)`, `(200)`, `(300)`
  (below, at and above the defaults 50 and 200; kompile writes the number as given).
  The text is `f2-examples/e2-simp-true-prio.kompile.kore`: the kompiled text that
  `test/constructs/fixtures/e2-simp-true-prio/kompile.txt` records, with its paths restored.
  Run from the package root: `lake env lean -j1 test/InertE2SimpTruePrio.lean`. Every statement is
  on the literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  - `coreOK`; `simp_class`: the reader leaves each of the five simplification sentences inert, class
    `simplification`; `simp_arg`: their `simplification` attributes carry "", "10", "50", "200",
    "300"; `simp_text`: the sentence of fi is the pattern
    `\implies{R}(\top{R}(), \equals{SortInt{}, R}(fi(fi(X)), \and{SortInt{}}(fi(X), \top{SortInt{}}())))`.
  - `eval_f0` to `eval_f4`: `fi(n) = n` at every integer n, for every H.
  - `simp_ev`: each sentence is entailed by Γ at values, for every H: at an integer n both sides are
    n (`InertEvUser.EqnU.entailed`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.InertE2SimpTruePrio

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e2-simp-true-prio.kompile.kore"
definition_of defn from "f2-examples/e2-simp-true-prio.kompile.kore"
user_axioms U from "f2-examples/e2-simp-true-prio.kompile.kore" module "E2-SIMP-TRUE-PRIO"

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

/-- The five functions, in the order of `c.fns`. -/
def fs : List Sym := [384, 385, 386, 387, 388]

theorem names : fs.map c.symName = ["Lblf0", "Lblf1", "Lblf2", "Lblf3", "Lblf4"] := by decide +kernel
theorem fns_length : c.fns.length = 5 := by decide +kernel
theorem fns_labels : c.fns.map Fn.label = fs := by decide +kernel
theorem fns_args : c.fns.all (fun fn => fn.args == [Srt.int]) = true := by decide +kernel
theorem hk : fs.all (fun g => (lookupSig hookSigs g).isNone) = true := by decide +kernel

/-! ## The sentences -/

/-- The five simplification sentences, each with its function: f0 to f4 in that order. -/
noncomputable abbrev simpPairs : List (AxiomDecl × Sym) :=
  [(U.ax201, 384), (U.ax203, 385), (U.ax205, 386), (U.ax207, 387), (U.ax209, 388)]

/-- The five simplification sentences. -/
noncomputable abbrev simpAxs : List AxiomDecl := simpPairs.map (·.1)

/-- The reader's class of each sentence. -/
theorem simp_class : simpAxs.map (fun ad => Parse.classify (.axiom ad.ax)) =
    List.replicate 5 (.inert .simplification) := by decide +kernel

/-- **The written forms of the key**: the `simplification` attribute of each sentence carries no
number (the empty string), 10, 50, 200 and 300. -/
theorem simp_arg : simpAxs.map (fun ad => KoreAML.Parse.attrStr? ad.ax.attributes "simplification") =
    [some "", some "10", some "50", some "200", some "300"] := by decide +kernel

/-- `g(g(X)) => g(X)` as an equation over `g`. -/
def E (g : Sym) : LibEv.Eqn :=
  ⟨[("VarX", Srt.int)], Srt.int, none, .app g [.app g [.var 0]], .app g [.var 0]⟩

/-- **The sentences are `E`'s patterns**, the i-th of the i-th function, over the one sort variable
`R`, `VarX` free in each. -/
theorem simp_text : simpPairs.all (fun p =>
    decide (p.1.ax.pattern = (E p.2).pattern c) && decide (p.1.ax.sortVars = [Rv]) &&
    decide ((trS p.1).pat = (trAxiom [] [] p.1).pat) &&
    decide (LibEv.vkey c (E p.2).vars 0 ∈ freeOf [] p.1.ax.pattern) && decide (p.2 ∈ fs)) = true := by
  decide +kernel

kernel_rfl pattern_wh : ∀ (H : HookParams) (g : Sym), (E g).pattern (cH H) = (E g).pattern c
kernel_rfl vkey_wh : ∀ (H : HookParams) (g : Sym), LibEv.vkey (cH H) (E g).vars 0 = LibEv.vkey c (E g).vars 0

/-! ## The functions' values at every integer -/

/-- A function whose one clause is `g(X) => X`, of the least priority, has the value n at every
integer n, for every H. -/
theorem eval_id {g : Sym} {fn : Fn} (hfn : ∀ H : HookParams, (cH H).lookupFn g = some fn)
    (h0 : 0 < fn.clauses.length) (hv : (fn.clauses[0]'h0).vars = [Srt.int])
    (hp : (fn.clauses[0]'h0).pats = [.var 0]) (hq : (fn.clauses[0]'h0).req = none)
    (hr : (fn.clauses[0]'h0).rhs = .var 0) (hpre : (fn.clauses[0]'h0).pre = .top)
    (he : (fn.clauses[0]'h0).ens = none) (hx : (fn.clauses[0]'h0).exs = [])
    (hpost : (fn.clauses[0]'h0).post = .top)
    (hl : fn.clauses.all (fun cl' => !decide (cl'.prio < (fn.clauses[0]'h0).prio)) = true)
    (H : HookParams) (n : Int) : Eval (cH H) g [int n] (some (int n)) := by
  have hσ : (cH H).WellSorted (fn.clauses[0]'h0).vars [(0, int n)] := by
    intro i s hi
    rw [hv] at hi
    match i, hi with
    | 0, hi => cases hi; exact ⟨int n, rfl, rfl⟩
    | k + 1, hi => simp at hi
  have hm : PatVals (cH H) [(0, int n)] (fn.clauses[0]'h0).pats [int n] := by
    rw [hp]; exact .cons (.var rfl) .nil
  have hrv : EvalTerm (cH H) [(0, int n)] (fn.clauses[0]'h0).rhs (some (int n)) := by
    rw [hr]; exact .var
  exact .clause (cl := fn.clauses[0]'h0) (σ := [(0, int n)]) (hfn H) (List.getElem_mem _) hσ hm
    (fun t ht => by rw [hq] at ht; cases ht) (by rw [hpre]; exact .top)
    (fun cl' hcl' _ hlt => absurd hlt (by simpa using List.all_eq_true.mp hl cl' hcl')) hx hrv
    (fun t ht => by rw [he] at ht; cases ht) (Clause.holds_postTop hpost _)

noncomputable abbrev fn0 : Fn := c.fns[0]'(by decide +kernel)
noncomputable abbrev fn1 : Fn := c.fns[1]'(by decide +kernel)
noncomputable abbrev fn2 : Fn := c.fns[2]'(by decide +kernel)
noncomputable abbrev fn3 : Fn := c.fns[3]'(by decide +kernel)
noncomputable abbrev fn4 : Fn := c.fns[4]'(by decide +kernel)

theorem hfn0 (H : HookParams) : (cH H).lookupFn 384 = some fn0 := by rw [Semantics.lookupFn_withHooks]; rfl
theorem hfn1 (H : HookParams) : (cH H).lookupFn 385 = some fn1 := by rw [Semantics.lookupFn_withHooks]; rfl
theorem hfn2 (H : HookParams) : (cH H).lookupFn 386 = some fn2 := by rw [Semantics.lookupFn_withHooks]; rfl
theorem hfn3 (H : HookParams) : (cH H).lookupFn 387 = some fn3 := by rw [Semantics.lookupFn_withHooks]; rfl
theorem hfn4 (H : HookParams) : (cH H).lookupFn 388 = some fn4 := by rw [Semantics.lookupFn_withHooks]; rfl

theorem eval_f0 (H : HookParams) (n : Int) : Eval (cH H) 384 [int n] (some (int n)) :=
  eval_id hfn0 (by decide +kernel) (by decide +kernel) rfl rfl rfl rfl rfl rfl rfl (by decide +kernel) H n
theorem eval_f1 (H : HookParams) (n : Int) : Eval (cH H) 385 [int n] (some (int n)) :=
  eval_id hfn1 (by decide +kernel) (by decide +kernel) rfl rfl rfl rfl rfl rfl rfl (by decide +kernel) H n
theorem eval_f2 (H : HookParams) (n : Int) : Eval (cH H) 386 [int n] (some (int n)) :=
  eval_id hfn2 (by decide +kernel) (by decide +kernel) rfl rfl rfl rfl rfl rfl rfl (by decide +kernel) H n
theorem eval_f3 (H : HookParams) (n : Int) : Eval (cH H) 387 [int n] (some (int n)) :=
  eval_id hfn3 (by decide +kernel) (by decide +kernel) rfl rfl rfl rfl rfl rfl rfl (by decide +kernel) H n
theorem eval_f4 (H : HookParams) (n : Int) : Eval (cH H) 388 [int n] (some (int n)) :=
  eval_id hfn4 (by decide +kernel) (by decide +kernel) rfl rfl rfl rfl rfl rfl rfl (by decide +kernel) H n

/-- The identity on one integer argument. -/
def idVal : List GroundTerm → Option GroundTerm
  | [.dv _ (.int n)] => some (int n)
  | _ => none

/-- The value table of the five functions: the identity on integers. -/
def table : InertEvUser.ValTable := fun s => if s ∈ fs then some idVal else none

/-- One function of the table: where its clause gives `g(n) = n` and its one argument is an
integer, `Eval` gives the table's value. -/
theorem table_one {H : HookParams} {g : Sym} {fn fn' : Fn} {ws : List GroundTerm}
    (hfn : (cH H).lookupFn g = some fn) (hargs : fn.args = [Srt.int])
    (hall : ∀ n : Int, Eval (cH H) g [int n] (some (int n)))
    (hfn' : (cH H).lookupFn g = some fn') (hws : (cH H).sortsOf ws = some fn'.args) :
    Eval (cH H) g ws (idVal ws) := by
  have he : fn' = fn := Option.some.inj (hfn'.symm.trans hfn)
  subst he
  rw [hargs, Semantics.sortsOf_withHooks _ _ noRaw] at hws
  obtain ⟨w, ws', rfl, hw, hws'⟩ := sortsOf_inv_cons hws
  cases sortsOf_inv_nil hws'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c hw
  exact hall n

/-- **The table is `Eval`'s**, for every H. -/
theorem table_ok (H : HookParams) : InertEvUser.TableOK (cH H) table := by
  intro s g fn' ws hg _ hfn' hws
  by_cases hs : s ∈ fs
  · simp only [table, hs, ite_true, Option.some.injEq] at hg
    subst hg
    simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact table_one (hfn0 H) rfl (eval_f0 H) hfn' hws
    · exact table_one (hfn1 H) rfl (eval_f1 H) hfn' hws
    · exact table_one (hfn2 H) rfl (eval_f2 H) hfn' hws
    · exact table_one (hfn3 H) rfl (eval_f3 H) hfn' hws
    · exact table_one (hfn4 H) rfl (eval_f4 H) hfn' hws
  · simp [table, hs] at hg

theorem typed : fs.all (fun g => InertEvUser.EqnU.typed c table (E g)) = true := by
  decide +kernel
kernel_rfl typed_wh : ∀ (H : HookParams) (g : Sym),
  InertEvUser.EqnU.typed (cH H) table (E g) = InertEvUser.EqnU.typed c table (E g)

/-- `g(g(n)) = g(n)` at every integer n, under the table, for g any of the five functions. -/
theorem holds (H : HookParams) {g : Sym} (hg : g ∈ fs) (hk : lookupSig hookSigs g = none) :
    InertEvUser.EqnU.Holds (cH H) table (E g) := by
  intro σ hσ _
  obtain ⟨v, hv, hvs⟩ := hσ 0 _ rfl
  rw [Semantics.sortOf_withHooks _ _ noRaw] at hvs
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c hvs
  have ha : InertEvUser.appU (cH H) table g = idVal := InertEvUser.appU_fn hk (by simp [table, hg])
  simp only [E, InertEvUser.valU, InertEvUser.valUList, allSome, hv, ha, Option.bind_some, Option.map_some]
  rfl

/-- **Each of the five simplification sentences is entailed by Γ at values**, for every H. -/
theorem simp_ev (H : HookParams) : ∀ p ∈ simpPairs, EntailsAtValues (cH H) p.1 (trS p.1).pat := by
  intro p hm
  have h1 := List.all_eq_true.mp simp_text p hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨⟨⟨hp, hsv⟩, htr⟩, hfv⟩, hgf⟩ := h1
  rw [htr]
  refine InertEvUser.EqnU.entailed (coreOKH H) (hokH H) (table_ok H) (E p.2)
    ((typed_wh H p.2).trans (List.all_eq_true.mp typed _ hgf))
    (holds H hgf (Option.isNone_iff_eq_none.mp (List.all_eq_true.mp hk _ hgf))) p.1
    (hp.trans (pattern_wh H p.2).symm) hsv (fun j hj => ?_)
  have : j = 0 := by simp [E] at hj; omega
  subst this
  rw [vkey_wh H p.2]; exact hfv

end KCore.InertE2SimpTruePrio

#check @KCore.InertE2SimpTruePrio.simp_ev
#print axioms KCore.InertE2SimpTruePrio.simp_class
#print axioms KCore.InertE2SimpTruePrio.simp_arg
#print axioms KCore.InertE2SimpTruePrio.simp_text
#print axioms KCore.InertE2SimpTruePrio.eval_f0
#print axioms KCore.InertE2SimpTruePrio.simp_ev
