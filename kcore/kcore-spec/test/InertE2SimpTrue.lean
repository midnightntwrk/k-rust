/-
  The C2 evidence of the rows E2 NON_EXECUTABLE(non-executable)@simplification and
  SMT_LEMMA(smt-lemma)@simplification (status inert) on the fixture e2-simp-true:
  `rule f(X) => X` and `rule sl(X) => X` beside
  `rule f(f(X)) => f(X) [simplification, non-executable]` and
  `rule sl(sl(X)) => sl(X) [simplification, smt-lemma]` (`sl` declared `smtlib(sl)`).
  The text is `f2-examples/e2-simp-true.kompile.kore`: the kompiled text that
  `test/constructs/fixtures/e2-simp-true/kompile.txt` records, with its paths restored.
  Run from the package root: `lake env lean -j1 test/InertE2SimpTrue.lean`. Every statement is on
  the literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  - `coreOK`; `ne_class`, `sl_class`: the reader leaves each simplification sentence inert, class
    `simplification`, the key among its attributes (`ne_key`, `sl_key`); `ne_text`, `sl_text`: their
    patterns are `\implies{R}(\top{R}(), \equals{SortInt{}, R}(f(f(X)), \and{SortInt{}}(f(X), \top{SortInt{}}())))`
    and the same of `sl`.
  - `f_all`, `sl_all`: `f(n) = n` and `sl(n) = n` at every integer n, for every H.
  - `ne_ev`, `sl_ev`: each sentence is entailed by Γ at values, for every H: at an integer n both
    sides are n (`InertEvUser.EqnU.entailed`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.InertE2SimpTrue

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e2-simp-true.kompile.kore"
definition_of defn from "f2-examples/e2-simp-true.kompile.kore"
user_axioms U from "f2-examples/e2-simp-true.kompile.kore" module "E2-SIMP-TRUE"

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

def f : Sym := 384
def sl : Sym := 385

theorem names : c.symName f = "Lblf" ∧ c.symName sl = "Lblsl" := by decide +kernel

noncomputable abbrev fnF : Fn := c.fns[0]'(by decide +kernel)
noncomputable abbrev fnS : Fn := c.fns[1]'(by decide +kernel)

theorem hfnF : c.lookupFn f = some fnF := rfl
theorem hfnS : c.lookupFn sl = some fnS := rfl
theorem hfnFH (H : HookParams) : (cH H).lookupFn f = some fnF := by rw [Semantics.lookupFn_withHooks]; exact hfnF
theorem hfnSH (H : HookParams) : (cH H).lookupFn sl = some fnS := by rw [Semantics.lookupFn_withHooks]; exact hfnS
theorem fnF_args : fnF.args = [Srt.int] := by decide +kernel
theorem fnS_args : fnS.args = [Srt.int] := by decide +kernel
theorem hkf : lookupSig hookSigs f = none := by decide +kernel
theorem hks : lookupSig hookSigs sl = none := by decide +kernel

/-! ## The sentences -/

/-- The simplification carrying `non-executable`. -/
noncomputable abbrev neAx : AxiomDecl := U.ax201
/-- The simplification carrying `smt-lemma`. -/
noncomputable abbrev slAx : AxiomDecl := U.ax256

/-- The reader's class of each sentence. -/
theorem ne_class : Parse.classifyShape (.axiom neAx.ax) = .inert .simplification := by decide +kernel
theorem sl_class : Parse.classifyShape (.axiom slAx.ax) = .inert .simplification := by decide +kernel

/-- Each carries its key. -/
theorem ne_key : neAx.ax.attributes.any (fun ap => ap.head.ident.name == "non-executable") = true := by
  decide +kernel
theorem sl_key : slAx.ax.attributes.any (fun ap => ap.head.ident.name == "smt-lemma") = true := by
  decide +kernel

/-- `g(g(X)) => g(X)` as an equation over `g`. -/
def E (g : Sym) : LibEv.Eqn :=
  ⟨[("VarX", Srt.int)], Srt.int, none, .app g [.app g [.var 0]], .app g [.var 0]⟩

/-- **The sentences are `E`'s patterns**, over the one sort variable `R`, `VarX` free in each. -/
theorem ne_text : neAx.ax.pattern = (E f).pattern c ∧ neAx.ax.sortVars = [Rv] ∧
    (trS neAx).pat = (trAxiom [] [] neAx).pat ∧
    LibEv.vkey c (E f).vars 0 ∈ freeOf [] neAx.ax.pattern := by
  decide +kernel
theorem sl_text : slAx.ax.pattern = (E sl).pattern c ∧ slAx.ax.sortVars = [Rv] ∧
    (trS slAx).pat = (trAxiom [] [] slAx).pat ∧
    LibEv.vkey c (E sl).vars 0 ∈ freeOf [] slAx.ax.pattern := by
  decide +kernel

kernel_rfl pattern_wh : ∀ (H : HookParams) (g : Sym), (E g).pattern (cH H) = (E g).pattern c
kernel_rfl vkey_wh : ∀ (H : HookParams) (g : Sym), LibEv.vkey (cH H) (E g).vars 0 = LibEv.vkey c (E g).vars 0

/-! ## `f`'s and `sl`'s values at every integer -/

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

theorem f_all (H : HookParams) (n : Int) : Eval (cH H) f [int n] (some (int n)) :=
  eval_id hfnFH (by decide +kernel) (by decide +kernel) rfl rfl rfl rfl rfl rfl rfl (by decide +kernel) H n
theorem sl_all (H : HookParams) (n : Int) : Eval (cH H) sl [int n] (some (int n)) :=
  eval_id hfnSH (by decide +kernel) (by decide +kernel) rfl rfl rfl rfl rfl rfl rfl (by decide +kernel) H n

/-- The value table of `f` and `sl`: the identity on integers. -/
def table : InertEvUser.ValTable := fun s =>
  if s = f ∨ s = sl then some fun ws => match ws with
    | [.dv _ (.int n)] => some (int n)
    | _ => none
  else none

/-- **The table is `Eval`'s**, for every H. -/
theorem table_ok (H : HookParams) : InertEvUser.TableOK (cH H) table := by
  intro s g fn' ws hg _ hfn' hws
  by_cases hs : s = f ∨ s = sl
  · simp only [table, hs, ite_true, Option.some.injEq] at hg
    subst hg
    rcases hs with rfl | rfl
    · have he : fn' = fnF := Option.some.inj (hfn'.symm.trans (hfnFH H))
      subst he
      rw [fnF_args, Semantics.sortsOf_withHooks _ _ noRaw] at hws
      obtain ⟨w, ws', rfl, hw, hws'⟩ := sortsOf_inv_cons hws
      cases sortsOf_inv_nil hws'
      obtain ⟨n, rfl⟩ := shape_int shapesOK_c hw
      exact f_all H n
    · have he : fn' = fnS := Option.some.inj (hfn'.symm.trans (hfnSH H))
      subst he
      rw [fnS_args, Semantics.sortsOf_withHooks _ _ noRaw] at hws
      obtain ⟨w, ws', rfl, hw, hws'⟩ := sortsOf_inv_cons hws
      cases sortsOf_inv_nil hws'
      obtain ⟨n, rfl⟩ := shape_int shapesOK_c hw
      exact sl_all H n
  · simp [table, hs] at hg

theorem typed : InertEvUser.EqnU.typed c table (E f) = true ∧ InertEvUser.EqnU.typed c table (E sl) = true := by
  decide +kernel
kernel_rfl typed_wh : ∀ (H : HookParams) (g : Sym),
  InertEvUser.EqnU.typed (cH H) table (E g) = InertEvUser.EqnU.typed c table (E g)

/-- `g(g(n)) = g(n)` at every integer n, under the table, for g either function. -/
theorem holds (H : HookParams) {g : Sym} (hg : g = f ∨ g = sl) (hk : lookupSig hookSigs g = none) :
    InertEvUser.EqnU.Holds (cH H) table (E g) := by
  intro σ hσ _
  obtain ⟨v, hv, hvs⟩ := hσ 0 _ rfl
  rw [Semantics.sortOf_withHooks _ _ noRaw] at hvs
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c hvs
  have ha : InertEvUser.appU (cH H) table g = fun ws => match ws with
      | [.dv _ (.int n)] => some (int n)
      | _ => none := InertEvUser.appU_fn hk (by simp [table, hg])
  simp only [E, InertEvUser.valU, InertEvUser.valUList, allSome, hv, ha, Option.bind_some, Option.map_some]
  rfl

/-- **Each simplification sentence is entailed by Γ at values**, for every H. -/
theorem ne_ev (H : HookParams) : EntailsAtValues (cH H) neAx (trS neAx).pat := by
  obtain ⟨hp, hsv, htr, hfv⟩ := ne_text
  rw [htr]
  refine InertEvUser.EqnU.entailed (coreOKH H) (hokH H) (table_ok H) (E f) ((typed_wh H f).trans typed.1)
    (holds H (.inl rfl) hkf) neAx (hp.trans (pattern_wh H f).symm) hsv (fun i hi => ?_)
  have : i = 0 := by simp [E] at hi; omega
  subst this
  rw [vkey_wh H f]; exact hfv

theorem sl_ev (H : HookParams) : EntailsAtValues (cH H) slAx (trS slAx).pat := by
  obtain ⟨hp, hsv, htr, hfv⟩ := sl_text
  rw [htr]
  refine InertEvUser.EqnU.entailed (coreOKH H) (hokH H) (table_ok H) (E sl) ((typed_wh H sl).trans typed.2)
    (holds H (.inr rfl) hks) slAx (hp.trans (pattern_wh H sl).symm) hsv (fun i hi => ?_)
  have : i = 0 := by simp [E] at hi; omega
  subst this
  rw [vkey_wh H sl]; exact hfv

end KCore.InertE2SimpTrue

#check @KCore.InertE2SimpTrue.ne_ev
#check @KCore.InertE2SimpTrue.sl_ev
#print axioms KCore.InertE2SimpTrue.ne_class
#print axioms KCore.InertE2SimpTrue.sl_class
#print axioms KCore.InertE2SimpTrue.ne_key
#print axioms KCore.InertE2SimpTrue.sl_key
#print axioms KCore.InertE2SimpTrue.ne_text
#print axioms KCore.InertE2SimpTrue.sl_text
#print axioms KCore.InertE2SimpTrue.f_all
#print axioms KCore.InertE2SimpTrue.sl_all
#print axioms KCore.InertE2SimpTrue.ne_ev
#print axioms KCore.InertE2SimpTrue.sl_ev
