/-
  The C2 evidence of the rows E2 COMM(comm)@simplification, CONCRETE(concrete)@simplification,
  PRESERVES_DEFINEDNESS(preserves-definedness)@simplification, SYMBOLIC(symbolic)@simplification
  and SYNTACTIC(syntactic)@simplification (status inert, class simplification) on the fixture
  e2-simplification: with `f(X) => X` and `g(X, Y) => X +Int Y` the equations of `f` and `g`,
  - axiom 149, `rule f(X) *Int Y => Y *Int f(X) [simplification, concrete(Y), symbolic(X)]`;
  - axiom 150, `rule f(X) *Int 0 => 0 [simplification, concrete]`;
  - axiom 169, `rule f(X) -Int 0 => f(X) [simplification, preserves-definedness]`;
  - axiom 212, `rule f(g(X, Y)) => g(X, Y) [simplification, syntactic(1)]`;
  - axiom 215, `rule g(X, Y) => g(Y, X) [simplification, comm]`, as kompile writes it: `comm`
    removed, the sentence written a second time with the arguments of its left side swapped
    (axiom 216, `test/InertResolveComm.lean`).
  The text is `f2-examples/e2-simplification.kompile.kore`: the kompiled text that
  `test/constructs/fixtures/e2-simplification/kompile.txt` records, with its paths restored.
  Run from the package root: `lake env lean -j1 test/InertE2Simplification.lean`. Every statement
  is on the literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  The text holds two simplification sentences that fail in every model of Γ (axioms 170 and 178,
  `test/InertE2SimpRefuted.lean`). Γ does not hold them, so each sentence below is entailed by Γ
  whatever they state.

  - `coreOK`; `simp_class`: the reader leaves each of the five sentences inert, class
    `simplification`; `keys`: the attributes each carries (and 215 no `comm`); `text149` to
    `text215`: their patterns are the equations `E149` to `E215`.
  - `eval_f`, `eval_g`: `f(n) = n` and `g(a, b) = a + b` at all integers, for every H.
  - `s149_ev`, `s150_ev`, `s169_ev`, `s212_ev`, `s215_ev`: each sentence is entailed by Γ at values,
    for every H (`InertEvUser.EqnU.entailed`): at integers both sides have one value.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.InertE2Simplification

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
theorem hok : c.ok = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok
theorem shapesOK_c : c.shapesOK = true := by decide +kernel

def f : Sym := 384
def g : Sym := 385

theorem names : c.symName f = "Lblf" ∧ c.symName g = "Lblg" ∧ c.symName intMul = "Lbl'UndsStar'Int'Unds'" ∧
    c.symName intSub = "Lbl'Unds'-Int'Unds'" := by
  decide +kernel

noncomputable abbrev fnF : Fn := c.fns[0]'(by decide +kernel)
noncomputable abbrev fnG : Fn := c.fns[1]'(by decide +kernel)

theorem hfnF (H : HookParams) : (cH H).lookupFn f = some fnF := by rw [Semantics.lookupFn_withHooks]; rfl
theorem hfnG (H : HookParams) : (cH H).lookupFn g = some fnG := by rw [Semantics.lookupFn_withHooks]; rfl
theorem fnF_args : fnF.args = [Srt.int] := by decide +kernel
theorem fnG_args : fnG.args = [Srt.int, Srt.int] := by decide +kernel
theorem hkf : lookupSig hookSigs f = none := by decide +kernel
theorem hkg : lookupSig hookSigs g = none := by decide +kernel
theorem hkMul : lookupSig hookSigs intMul = some ⟨intMul, [Srt.int, Srt.int], Srt.int⟩ := by decide +kernel
theorem hkSub : lookupSig hookSigs intSub = some ⟨intSub, [Srt.int, Srt.int], Srt.int⟩ := by decide +kernel

/-! ## The sentences -/

/-- `f(X) *Int Y => Y *Int f(X)`. -/
def E149 : LibEv.Eqn :=
  ⟨[("VarX", Srt.int), ("VarY", Srt.int)], Srt.int, none,
    .app intMul [.app f [.var 0], .var 1], .app intMul [.var 1, .app f [.var 0]]⟩
/-- `f(X) *Int 0 => 0`. -/
def E150 : LibEv.Eqn :=
  ⟨[("VarX", Srt.int)], Srt.int, none, .app intMul [.app f [.var 0], .dv Srt.int (.int 0)], .dv Srt.int (.int 0)⟩
/-- `f(X) -Int 0 => f(X)`. -/
def E169 : LibEv.Eqn :=
  ⟨[("VarX", Srt.int)], Srt.int, none, .app intSub [.app f [.var 0], .dv Srt.int (.int 0)], .app f [.var 0]⟩
/-- `f(g(X, Y)) => g(X, Y)`. -/
def E212 : LibEv.Eqn :=
  ⟨[("VarX", Srt.int), ("VarY", Srt.int)], Srt.int, none, .app f [.app g [.var 0, .var 1]], .app g [.var 0, .var 1]⟩
/-- `g(X, Y) => g(Y, X)`. -/
def E215 : LibEv.Eqn :=
  ⟨[("VarX", Srt.int), ("VarY", Srt.int)], Srt.int, none, .app g [.var 0, .var 1], .app g [.var 1, .var 0]⟩

/-- The reader's class of each sentence. -/
theorem simp_class : [U.ax149, U.ax150, U.ax169, U.ax212, U.ax215].map
    (fun ad => Parse.classifyShape (.axiom ad.ax)) = List.replicate 5 (.inert .simplification) := by
  decide +kernel

/-- **The attributes of each sentence**: 149 `concrete` and `symbolic` (each over a variable), 150
`concrete`, 169 `preserves-definedness`, 212 `syntactic` with "1", 215 no `comm` (kompile removes
it); each `simplification` with no number. -/
theorem keys :
    (U.ax149.ax.attributes.any (fun ap => ap.head.ident.name == "concrete") &&
      U.ax149.ax.attributes.any (fun ap => ap.head.ident.name == "symbolic") &&
      U.ax150.ax.attributes.any (fun ap => ap.head.ident.name == "concrete") &&
      U.ax169.ax.attributes.any (fun ap => ap.head.ident.name == "preserves-definedness") &&
      !U.ax215.ax.attributes.any (fun ap => ap.head.ident.name == "comm")) = true ∧
    KoreAML.Parse.attrStr? U.ax212.ax.attributes "syntactic" = some "1" ∧
    [U.ax149, U.ax150, U.ax169, U.ax212, U.ax215].map
      (fun ad => KoreAML.Parse.attrStr? ad.ax.attributes "simplification") = List.replicate 5 (some "") := by
  decide +kernel

theorem text149 : U.ax149.ax.pattern = E149.pattern c ∧ U.ax149.ax.sortVars = [Rv] ∧
    (trS U.ax149).pat = (trAxiom [] [] U.ax149).pat ∧
    LibEv.vkey c E149.vars 0 ∈ freeOf [] U.ax149.ax.pattern ∧ LibEv.vkey c E149.vars 1 ∈ freeOf [] U.ax149.ax.pattern := by
  decide +kernel
theorem text150 : U.ax150.ax.pattern = E150.pattern c ∧ U.ax150.ax.sortVars = [Rv] ∧
    (trS U.ax150).pat = (trAxiom [] [] U.ax150).pat ∧ LibEv.vkey c E150.vars 0 ∈ freeOf [] U.ax150.ax.pattern := by
  decide +kernel
theorem text169 : U.ax169.ax.pattern = E169.pattern c ∧ U.ax169.ax.sortVars = [Rv] ∧
    (trS U.ax169).pat = (trAxiom [] [] U.ax169).pat ∧ LibEv.vkey c E169.vars 0 ∈ freeOf [] U.ax169.ax.pattern := by
  decide +kernel
theorem text212 : U.ax212.ax.pattern = E212.pattern c ∧ U.ax212.ax.sortVars = [Rv] ∧
    (trS U.ax212).pat = (trAxiom [] [] U.ax212).pat ∧
    LibEv.vkey c E212.vars 0 ∈ freeOf [] U.ax212.ax.pattern ∧ LibEv.vkey c E212.vars 1 ∈ freeOf [] U.ax212.ax.pattern := by
  decide +kernel
theorem text215 : U.ax215.ax.pattern = E215.pattern c ∧ U.ax215.ax.sortVars = [Rv] ∧
    (trS U.ax215).pat = (trAxiom [] [] U.ax215).pat ∧
    LibEv.vkey c E215.vars 0 ∈ freeOf [] U.ax215.ax.pattern ∧ LibEv.vkey c E215.vars 1 ∈ freeOf [] U.ax215.ax.pattern := by
  decide +kernel

/-! ## The values of `f` and `g` -/

/-- `f`'s one clause: `f(X) => X`. -/
noncomputable abbrev clF : Clause := fnF.clauses[0]'(by decide +kernel)
/-- `g`'s one clause: `g(X, Y) => X +Int Y`. -/
noncomputable abbrev clG : Clause := fnG.clauses[0]'(by decide +kernel)

theorem clF_vars : clF.vars = [Srt.int] := by decide +kernel
theorem clF_pats : clF.pats = [.var 0] := rfl
theorem clF_req : clF.req = none := rfl
theorem clF_rhs : clF.rhs = .var 0 := rfl
theorem clF_pre : clF.pre = .top := rfl
theorem clF_ens : clF.ens = none := rfl
theorem clF_least : fnF.clauses.all (fun cl' => !decide (cl'.prio < clF.prio)) = true := by decide +kernel
theorem clG_vars : clG.vars = [Srt.int, Srt.int] := by decide +kernel
theorem clG_pats : clG.pats = [.var 0, .var 1] := rfl
theorem clG_req : clG.req = none := rfl
theorem clG_rhs : clG.rhs = .app intAdd [.var 0, .var 1] := rfl
theorem clG_pre : clG.pre = .top := rfl
theorem clG_ens : clG.ens = none := rfl
theorem clG_least : fnG.clauses.all (fun cl' => !decide (cl'.prio < clG.prio)) = true := by decide +kernel
theorem isCtor_add : c.isCtor intAdd = false := by decide +kernel

theorem int2_at (x y : Int) (k : Int → Int → Option GroundTerm) : int2 [int x, int y] k = k x y := by
  simp [int2, asInt, int]

theorem hook_add (vs : List GroundTerm) : hook intAdd vs = some (int2 vs fun x y => some (int (x + y))) := rfl
theorem hook_mul (vs : List GroundTerm) : hook intMul vs = some (int2 vs fun x y => some (int (x * y))) := rfl
theorem hook_sub (vs : List GroundTerm) : hook intSub vs = some (int2 vs fun x y => some (int (x - y))) := rfl

/-- **`f(n) = n` at every integer n, for every H**: the clause matches and has no condition. -/
theorem eval_f (H : HookParams) (n : Int) : Eval (cH H) f [int n] (some (int n)) := by
  have hσ : (cH H).WellSorted clF.vars [(0, int n)] := by
    intro i s hi
    rw [clF_vars] at hi
    match i, hi with
    | 0, hi => cases hi; exact ⟨int n, rfl, rfl⟩
    | k + 1, hi => simp at hi
  have hm : PatVals (cH H) [(0, int n)] clF.pats [int n] := by
    rw [clF_pats]; exact .cons (.var rfl) .nil
  have hr : EvalTerm (cH H) [(0, int n)] clF.rhs (some (int n)) := by
    rw [clF_rhs]; exact .var
  exact .clause (cl := clF) (σ := [(0, int n)]) (hfnF H) (List.getElem_mem _) hσ hm
    (fun t ht => by rw [clF_req] at ht; cases ht) (by rw [clF_pre]; exact .top)
    (fun cl' hcl' _ hlt => absurd hlt (by simpa using List.all_eq_true.mp clF_least cl' hcl')) (by rfl) hr
    (fun t ht => by rw [clF_ens] at ht; cases ht) (Clause.holds_postTop (by rfl) _)

/-- `X +Int Y` has the value `a + b` at the substitution giving the variables 0 and 1 the values a, b. -/
theorem add_at (H : HookParams) (a b : Int) :
    EvalTerm (cH H) [(0, int a), (1, int b)] (.app intAdd [.var 0, .var 1]) (some (int (a + b))) := by
  refine .hook (rs := [some (int a), some (int b)]) (show (cH H).isCtor intAdd = false from isCtor_add) rfl
    (.cons .var (.cons .var .nil)) (fun vs hvs => ?_) (fun h => by cases h)
  cases hvs
  exact Semantics.hookRes_of_value (by rw [hook_add, int2_at])

/-- **`g(a, b) = a + b` at every pair of integers, for every H.** -/
theorem eval_g (H : HookParams) (a b : Int) : Eval (cH H) g [int a, int b] (some (int (a + b))) := by
  have hσ : (cH H).WellSorted clG.vars [(0, int a), (1, int b)] := by
    intro i s hi
    rw [clG_vars] at hi
    match i, hi with
    | 0, hi => cases hi; exact ⟨int a, rfl, rfl⟩
    | 1, hi => cases hi; exact ⟨int b, rfl, rfl⟩
    | k + 2, hi => simp at hi
  have hm : PatVals (cH H) [(0, int a), (1, int b)] clG.pats [int a, int b] := by
    rw [clG_pats]; exact .cons (.var rfl) (.cons (.var rfl) .nil)
  exact .clause (cl := clG) (σ := [(0, int a), (1, int b)]) (hfnG H) (List.getElem_mem _) hσ hm
    (fun t ht => by rw [clG_req] at ht; cases ht) (by rw [clG_pre]; exact .top)
    (fun cl' hcl' _ hlt => absurd hlt (by simpa using List.all_eq_true.mp clG_least cl' hcl')) (by rfl)
    (by rw [clG_rhs]; exact add_at H a b)
    (fun t ht => by rw [clG_ens] at ht; cases ht) (Clause.holds_postTop (by rfl) _)

/-- `f` on integers. -/
def fVal : List GroundTerm → Option GroundTerm
  | [.dv _ (.int n)] => some (int n)
  | _ => none

/-- `g` on integers. -/
def gVal : List GroundTerm → Option GroundTerm
  | [.dv _ (.int a), .dv _ (.int b)] => some (int (a + b))
  | _ => none

/-- The value table of `f` and `g`. -/
def tbl : InertEvUser.ValTable := fun s =>
  if s = f then some fVal else if s = g then some gVal else none

/-- **The table is `Eval`'s**, for every H. -/
theorem table_ok (H : HookParams) : InertEvUser.TableOK (cH H) tbl := by
  intro s k fn' ws hk _ hfn' hws
  by_cases hs : s = f
  · subst hs
    simp only [tbl, ite_true, Option.some.injEq] at hk
    subst hk
    have he : fn' = fnF := Option.some.inj (hfn'.symm.trans (hfnF H))
    subst he
    rw [fnF_args, Semantics.sortsOf_withHooks _ _ noRaw] at hws
    obtain ⟨w, ws', rfl, hw, hws'⟩ := sortsOf_inv_cons hws
    cases sortsOf_inv_nil hws'
    obtain ⟨n, rfl⟩ := shape_int shapesOK_c hw
    exact eval_f H n
  · by_cases hs' : s = g
    · subst hs'
      simp only [tbl, hs, ite_false, ite_true, Option.some.injEq] at hk
      subst hk
      have he : fn' = fnG := Option.some.inj (hfn'.symm.trans (hfnG H))
      subst he
      rw [fnG_args, Semantics.sortsOf_withHooks _ _ noRaw] at hws
      obtain ⟨w, ws', rfl, hw, hws'⟩ := sortsOf_inv_cons hws
      obtain ⟨w', ws'', rfl, hw', hws''⟩ := sortsOf_inv_cons hws'
      cases sortsOf_inv_nil hws''
      obtain ⟨a, rfl⟩ := shape_int shapesOK_c hw
      obtain ⟨b, rfl⟩ := shape_int shapesOK_c hw'
      exact eval_g H a b
    · simp [tbl, hs, hs'] at hk

theorem appU_f (H : HookParams) : InertEvUser.appU (cH H) tbl f = fVal :=
  InertEvUser.appU_fn hkf (by simp [tbl])
theorem appU_g (H : HookParams) : InertEvUser.appU (cH H) tbl g = gVal :=
  InertEvUser.appU_fn hkg (by simp [tbl, f, g])

theorem mul_at (H : HookParams) (x y : Int) : (cH H).hv intMul [int x, int y] = some (int (x * y)) :=
  hv_of_value (by rw [hook_mul, int2_at])
theorem sub_at (H : HookParams) (x y : Int) : (cH H).hv intSub [int x, int y] = some (int (x - y)) :=
  hv_of_value (by rw [hook_sub, int2_at])

/-! ## Each sentence is entailed at values -/

kernel_rfl pat149_wh : ∀ H : HookParams, E149.pattern (cH H) = E149.pattern c
kernel_rfl typed149_wh : ∀ H : HookParams, InertEvUser.EqnU.typed (cH H) tbl E149 = InertEvUser.EqnU.typed c tbl E149
kernel_rfl vkey149_wh : ∀ (H : HookParams) (i : Nat), LibEv.vkey (cH H) E149.vars i = LibEv.vkey c E149.vars i
kernel_rfl pat150_wh : ∀ H : HookParams, E150.pattern (cH H) = E150.pattern c
kernel_rfl typed150_wh : ∀ H : HookParams, InertEvUser.EqnU.typed (cH H) tbl E150 = InertEvUser.EqnU.typed c tbl E150
kernel_rfl vkey150_wh : ∀ (H : HookParams) (i : Nat), LibEv.vkey (cH H) E150.vars i = LibEv.vkey c E150.vars i
kernel_rfl pat169_wh : ∀ H : HookParams, E169.pattern (cH H) = E169.pattern c
kernel_rfl typed169_wh : ∀ H : HookParams, InertEvUser.EqnU.typed (cH H) tbl E169 = InertEvUser.EqnU.typed c tbl E169
kernel_rfl vkey169_wh : ∀ (H : HookParams) (i : Nat), LibEv.vkey (cH H) E169.vars i = LibEv.vkey c E169.vars i
kernel_rfl pat212_wh : ∀ H : HookParams, E212.pattern (cH H) = E212.pattern c
kernel_rfl typed212_wh : ∀ H : HookParams, InertEvUser.EqnU.typed (cH H) tbl E212 = InertEvUser.EqnU.typed c tbl E212
kernel_rfl vkey212_wh : ∀ (H : HookParams) (i : Nat), LibEv.vkey (cH H) E212.vars i = LibEv.vkey c E212.vars i
kernel_rfl pat215_wh : ∀ H : HookParams, E215.pattern (cH H) = E215.pattern c
kernel_rfl typed215_wh : ∀ H : HookParams, InertEvUser.EqnU.typed (cH H) tbl E215 = InertEvUser.EqnU.typed c tbl E215
kernel_rfl vkey215_wh : ∀ (H : HookParams) (i : Nat), LibEv.vkey (cH H) E215.vars i = LibEv.vkey c E215.vars i

/-- An equation of the table whose sides have one value is entailed at values by a sentence that
holds its pattern, for every H. -/
theorem ev_of (H : HookParams) (E : LibEv.Eqn) (ad : AxiomDecl)
    (hpw : E.pattern (cH H) = E.pattern c)
    (htw : InertEvUser.EqnU.typed (cH H) tbl E = InertEvUser.EqnU.typed c tbl E)
    (hvw : ∀ i : Nat, LibEv.vkey (cH H) E.vars i = LibEv.vkey c E.vars i)
    (ht : InertEvUser.EqnU.typed c tbl E = true)
    (hE : InertEvUser.EqnU.Holds (cH H) tbl E) (hp : ad.ax.pattern = E.pattern c) (hsv : ad.ax.sortVars = [Rv])
    (htr : (trS ad).pat = (trAxiom [] [] ad).pat)
    (hfv : ∀ i, i < E.vars.length → LibEv.vkey c E.vars i ∈ freeOf [] ad.ax.pattern) :
    EntailsAtValues (cH H) ad (trS ad).pat := by
  rw [htr]
  exact InertEvUser.EqnU.entailed (coreOKH H) (hokH H) (table_ok H) E (htw.trans ht) hE ad
    (hp.trans hpw.symm) hsv (fun i hi => (hvw i).symm ▸ hfv i hi)

theorem typed : [E149, E150, E169, E212, E215].all (InertEvUser.EqnU.typed c tbl) = true := by decide +kernel

theorem holds149 (H : HookParams) : InertEvUser.EqnU.Holds (cH H) tbl E149 := by
  intro σ hσ _
  obtain ⟨v, hv, hvs⟩ := hσ 0 _ rfl
  obtain ⟨w, hw, hws⟩ := hσ 1 _ rfl
  rw [Semantics.sortOf_withHooks _ _ noRaw] at hvs hws
  obtain ⟨x, rfl⟩ := shape_int shapesOK_c hvs
  obtain ⟨y, rfl⟩ := shape_int shapesOK_c hws
  simp only [E149, InertEvUser.valU, InertEvUser.valUList, allSome, hv, hw, appU_f, InertEvUser.appU_hook hkMul,
    Option.bind_some, Option.map_some, fVal, int]
  show (cH H).hv intMul [int x, int y] = (cH H).hv intMul [int y, int x]
  rw [mul_at, mul_at, Int.mul_comm]

theorem holds150 (H : HookParams) : InertEvUser.EqnU.Holds (cH H) tbl E150 := by
  intro σ hσ _
  obtain ⟨v, hv, hvs⟩ := hσ 0 _ rfl
  rw [Semantics.sortOf_withHooks _ _ noRaw] at hvs
  obtain ⟨x, rfl⟩ := shape_int shapesOK_c hvs
  simp only [E150, InertEvUser.valU, InertEvUser.valUList, allSome, hv, appU_f, InertEvUser.appU_hook hkMul,
    Option.bind_some, Option.map_some, fVal, int]
  rw [← int, ← int, mul_at, Int.mul_zero]

theorem holds169 (H : HookParams) : InertEvUser.EqnU.Holds (cH H) tbl E169 := by
  intro σ hσ _
  obtain ⟨v, hv, hvs⟩ := hσ 0 _ rfl
  rw [Semantics.sortOf_withHooks _ _ noRaw] at hvs
  obtain ⟨x, rfl⟩ := shape_int shapesOK_c hvs
  simp only [E169, InertEvUser.valU, InertEvUser.valUList, allSome, hv, appU_f, InertEvUser.appU_hook hkSub,
    Option.bind_some, Option.map_some, fVal, int]
  rw [← int, ← int, sub_at, Int.sub_zero]

theorem holds212 (H : HookParams) : InertEvUser.EqnU.Holds (cH H) tbl E212 := by
  intro σ hσ _
  obtain ⟨v, hv, hvs⟩ := hσ 0 _ rfl
  obtain ⟨w, hw, hws⟩ := hσ 1 _ rfl
  rw [Semantics.sortOf_withHooks _ _ noRaw] at hvs hws
  obtain ⟨x, rfl⟩ := shape_int shapesOK_c hvs
  obtain ⟨y, rfl⟩ := shape_int shapesOK_c hws
  simp only [E212, InertEvUser.valU, InertEvUser.valUList, allSome, hv, hw, appU_f, appU_g,
    Option.bind_some, Option.map_some, fVal, gVal, int]

theorem holds215 (H : HookParams) : InertEvUser.EqnU.Holds (cH H) tbl E215 := by
  intro σ hσ _
  obtain ⟨v, hv, hvs⟩ := hσ 0 _ rfl
  obtain ⟨w, hw, hws⟩ := hσ 1 _ rfl
  rw [Semantics.sortOf_withHooks _ _ noRaw] at hvs hws
  obtain ⟨x, rfl⟩ := shape_int shapesOK_c hvs
  obtain ⟨y, rfl⟩ := shape_int shapesOK_c hws
  simp only [E215, InertEvUser.valU, InertEvUser.valUList, allSome, hv, hw, appU_g,
    Option.bind_some, Option.map_some, gVal, int, Int.add_comm]

/-- **`f(X) *Int Y => Y *Int f(X)` (149) is entailed by Γ at values**, for every H. -/
theorem s149_ev (H : HookParams) : EntailsAtValues (cH H) U.ax149 (trS U.ax149).pat := by
  obtain ⟨hp, hsv, htr, h0, h1⟩ := text149
  refine ev_of H E149 U.ax149 (pat149_wh H) (typed149_wh H) (vkey149_wh H) (by simpa using (List.all_eq_true.mp typed) E149 (by simp)) (holds149 H)
    hp hsv htr (fun i hi => ?_)
  have : i = 0 ∨ i = 1 := by simp [E149] at hi; omega
  rcases this with rfl | rfl
  · exact h0
  · exact h1

/-- **`f(X) *Int 0 => 0` (150) is entailed by Γ at values**, for every H. -/
theorem s150_ev (H : HookParams) : EntailsAtValues (cH H) U.ax150 (trS U.ax150).pat := by
  obtain ⟨hp, hsv, htr, h0⟩ := text150
  refine ev_of H E150 U.ax150 (pat150_wh H) (typed150_wh H) (vkey150_wh H) (by simpa using (List.all_eq_true.mp typed) E150 (by simp)) (holds150 H)
    hp hsv htr (fun i hi => ?_)
  have : i = 0 := by simp [E150] at hi; omega
  subst this; exact h0

/-- **`f(X) -Int 0 => f(X)` (169) is entailed by Γ at values**, for every H. -/
theorem s169_ev (H : HookParams) : EntailsAtValues (cH H) U.ax169 (trS U.ax169).pat := by
  obtain ⟨hp, hsv, htr, h0⟩ := text169
  refine ev_of H E169 U.ax169 (pat169_wh H) (typed169_wh H) (vkey169_wh H) (by simpa using (List.all_eq_true.mp typed) E169 (by simp)) (holds169 H)
    hp hsv htr (fun i hi => ?_)
  have : i = 0 := by simp [E169] at hi; omega
  subst this; exact h0

/-- **`f(g(X, Y)) => g(X, Y)` (212) is entailed by Γ at values**, for every H. -/
theorem s212_ev (H : HookParams) : EntailsAtValues (cH H) U.ax212 (trS U.ax212).pat := by
  obtain ⟨hp, hsv, htr, h0, h1⟩ := text212
  refine ev_of H E212 U.ax212 (pat212_wh H) (typed212_wh H) (vkey212_wh H) (by simpa using (List.all_eq_true.mp typed) E212 (by simp)) (holds212 H)
    hp hsv htr (fun i hi => ?_)
  have : i = 0 ∨ i = 1 := by simp [E212] at hi; omega
  rcases this with rfl | rfl
  · exact h0
  · exact h1

/-- **`g(X, Y) => g(Y, X)` (215) is entailed by Γ at values**, for every H. -/
theorem s215_ev (H : HookParams) : EntailsAtValues (cH H) U.ax215 (trS U.ax215).pat := by
  obtain ⟨hp, hsv, htr, h0, h1⟩ := text215
  refine ev_of H E215 U.ax215 (pat215_wh H) (typed215_wh H) (vkey215_wh H) (by simpa using (List.all_eq_true.mp typed) E215 (by simp)) (holds215 H)
    hp hsv htr (fun i hi => ?_)
  have : i = 0 ∨ i = 1 := by simp [E215] at hi; omega
  rcases this with rfl | rfl
  · exact h0
  · exact h1

end KCore.InertE2Simplification

#check @KCore.InertE2Simplification.s149_ev
#check @KCore.InertE2Simplification.s150_ev
#check @KCore.InertE2Simplification.s169_ev
#check @KCore.InertE2Simplification.s212_ev
#check @KCore.InertE2Simplification.s215_ev
#print axioms KCore.InertE2Simplification.simp_class
#print axioms KCore.InertE2Simplification.keys
#print axioms KCore.InertE2Simplification.s149_ev
#print axioms KCore.InertE2Simplification.s150_ev
#print axioms KCore.InertE2Simplification.s169_ev
#print axioms KCore.InertE2Simplification.s212_ev
#print axioms KCore.InertE2Simplification.s215_ev
