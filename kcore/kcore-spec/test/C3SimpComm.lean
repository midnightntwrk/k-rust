/-
  The C2 evidence of the pair `simplification` `comm` x symbol `comm` (status inert) on the fixture
  c3-simp-comm: `syntax Int ::= g(Int, Int) [function, total, comm]`, `rule g(X, Y) => X +Int Y`
  and `rule g(X, 0) => X [simplification, comm]`, which kompile writes as two simplification
  sentences, `g(X, 0) = X` (axiom 203) and the same with the arguments of the left side swapped,
  `g(0, X) = X` (axiom 204).
  The text is `f2-examples/c3-simp-comm.kompile.kore`: the kompiled text that
  `test/constructs/fixtures/c3-simp-comm/kompile.txt` records, with its paths restored; its
  companion `f2-examples/c3-simp-comm-base.kompile.kore` (fixture c3-simp-comm-base) is the same text
  without `comm` on the simplification, which holds the first sentence alone.
  Run from the package root: `lake env lean -j1 test/C3SimpComm.lean`. Every statement is on the
  literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  - `coreOK`; `simp_class`: the reader leaves both sentences inert, class `simplification`;
    `simp_text`: their patterns are `E0`'s and `E1`'s.
  - `eval_all`: `g(a, b) = a + b` at every pair of integers, for every H (the one equation of `g`
    applies at every argument list, with no `requires`; `+Int`'s value is the hook's).
  - `simp_ev`: both sentences are entailed by Γ at values, for every H: `g(n, 0)` and `g(0, n)` are
    both n (`InertEvUser.EqnU.entailed`, with the table that `eval_all` gives).
  - `sem_eq`: the text's semantics is c3-simp-comm-base's, so at every H the two are one semantics
    (`withHooks_eq`), with one Γ (`gamma_eq`) and one `Step`: the second sentence, which `comm` adds,
    changes neither the theory nor the steps.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.C3SimpComm

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/c3-simp-comm.kompile.kore"
definition_of defn from "f2-examples/c3-simp-comm.kompile.kore"
user_axioms U from "f2-examples/c3-simp-comm.kompile.kore" module "C3-SIMP-COMM"

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

def g : Sym := 384

theorem names : c.symName g = "Lblg" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

theorem hfn : c.lookupFn g = some fn := rfl
theorem hfnH (H : HookParams) : (cH H).lookupFn g = some fn := by rw [Semantics.lookupFn_withHooks]; exact hfn
theorem fn_args : fn.args = [Srt.int, Srt.int] := by decide +kernel
theorem hkg : lookupSig hookSigs g = none := by decide +kernel

/-! ## The two sentences -/

/-- `g(X, 0) => X`, as kompile writes the simplification. -/
def E0 : LibEv.Eqn := ⟨[("VarX", Srt.int)], Srt.int, none, .app g [.var 0, .dv Srt.int (.int 0)], .var 0⟩
/-- `g(0, X) => X`, the same with the arguments of the left side swapped. -/
def E1 : LibEv.Eqn := ⟨[("VarX", Srt.int)], Srt.int, none, .app g [.dv Srt.int (.int 0), .var 0], .var 0⟩

/-- The reader's class of the two sentences. -/
theorem simp_class : [U.ax203, U.ax204].map (fun ad => Parse.classify (.axiom ad.ax)) =
    [.inert .simplification, .inert .simplification] := by decide +kernel

/-- **The sentences are `E0`'s and `E1`'s patterns**, over the one sort variable `R`, `VarX` free. -/
theorem simp_text :
    (U.ax203.ax.pattern = E0.pattern c ∧ U.ax203.ax.sortVars = [Rv] ∧
      (trS U.ax203).pat = (trAxiom [] [] U.ax203).pat ∧ LibEv.vkey c E0.vars 0 ∈ freeOf [] U.ax203.ax.pattern) ∧
    (U.ax204.ax.pattern = E1.pattern c ∧ U.ax204.ax.sortVars = [Rv] ∧
      (trS U.ax204).pat = (trAxiom [] [] U.ax204).pat ∧ LibEv.vkey c E1.vars 0 ∈ freeOf [] U.ax204.ax.pattern) := by
  decide +kernel

kernel_rfl pattern0_wh : ∀ H : HookParams, E0.pattern (cH H) = E0.pattern c
kernel_rfl pattern1_wh : ∀ H : HookParams, E1.pattern (cH H) = E1.pattern c
kernel_rfl vkey_wh : ∀ H : HookParams, LibEv.vkey (cH H) E0.vars 0 = LibEv.vkey c E0.vars 0

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

theorem typed : InertEvUser.EqnU.typed c gTable E0 = true ∧ InertEvUser.EqnU.typed c gTable E1 = true := by
  decide +kernel
kernel_rfl typed0_wh : ∀ H : HookParams, InertEvUser.EqnU.typed (cH H) gTable E0 = InertEvUser.EqnU.typed c gTable E0
kernel_rfl typed1_wh : ∀ H : HookParams, InertEvUser.EqnU.typed (cH H) gTable E1 = InertEvUser.EqnU.typed c gTable E1

theorem appU_g (H : HookParams) : InertEvUser.appU (cH H) gTable g = fun ws => match ws with
    | [.dv _ (.int a), .dv _ (.int b)] => some (int (a + b))
    | _ => none := InertEvUser.appU_fn hkg (by simp [gTable])

/-- `g(n, 0) = n` at every integer n, under the table. -/
theorem holds0 (H : HookParams) : InertEvUser.EqnU.Holds (cH H) gTable E0 := by
  intro σ hσ _
  obtain ⟨v, hv, hvs⟩ := hσ 0 _ rfl
  rw [Semantics.sortOf_withHooks _ _ noRaw] at hvs
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c hvs
  simp only [E0, InertEvUser.valU, InertEvUser.valUList, allSome, hv, appU_g, Option.bind_some, Option.map_some]
  simp [int]

/-- `g(0, n) = n` at every integer n, under the table. -/
theorem holds1 (H : HookParams) : InertEvUser.EqnU.Holds (cH H) gTable E1 := by
  intro σ hσ _
  obtain ⟨v, hv, hvs⟩ := hσ 0 _ rfl
  rw [Semantics.sortOf_withHooks _ _ noRaw] at hvs
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c hvs
  simp only [E1, InertEvUser.valU, InertEvUser.valUList, allSome, hv, appU_g, Option.bind_some, Option.map_some]
  simp [int]

/-- **Both simplification sentences are entailed by Γ at values**, for every H. -/
theorem simp_ev (H : HookParams) :
    EntailsAtValues (cH H) U.ax203 (trS U.ax203).pat ∧ EntailsAtValues (cH H) U.ax204 (trS U.ax204).pat := by
  obtain ⟨⟨hp0, hsv0, htr0, hfv0⟩, ⟨hp1, hsv1, htr1, hfv1⟩⟩ := simp_text
  constructor
  · rw [htr0]
    refine InertEvUser.EqnU.entailed (coreOKH H) (hokH H) (table_ok H) E0 ((typed0_wh H).trans typed.1) (holds0 H)
      U.ax203 (hp0.trans (pattern0_wh H).symm) hsv0 (fun i hi => ?_)
    have : i = 0 := by simp [E0] at hi; omega
    subst this
    rw [vkey_wh H]; exact hfv0
  · rw [htr1]
    refine InertEvUser.EqnU.entailed (coreOKH H) (hokH H) (table_ok H) E1 ((typed1_wh H).trans typed.2) (holds1 H)
      U.ax204 (hp1.trans (pattern1_wh H).symm) hsv1 (fun i hi => ?_)
    have : i = 0 := by simp [E1] at hi; omega
    subst this
    rw [show LibEv.vkey (cH H) E1.vars 0 = LibEv.vkey c E1.vars 0 from vkey_wh H]; exact hfv1

/-! ## The companion without `comm` on the simplification -/

namespace Base
definition_of defn from "f2-examples/c3-simp-comm-base.kompile.kore"
end Base

/-- **The two texts have one semantics**: the sentence `comm` adds is read as the same nothing. -/
theorem sem_eq : defn.sem = Base.defn.sem := rfl

/-- At every H the two semantics are one, so everything stated of one (its Γ, its `Step`) is stated
of the other. -/
theorem withHooks_eq (H : HookParams) : cH H = Base.defn.sem.withHooks H := congrArg (Semantics.withHooks · H) sem_eq

theorem gamma_eq (H : HookParams) : Γ (cH H) = Γ (Base.defn.sem.withHooks H) := by rw [withHooks_eq]

end KCore.C3SimpComm

#check @KCore.C3SimpComm.simp_ev
#check @KCore.C3SimpComm.sem_eq
#print axioms KCore.C3SimpComm.simp_class
#print axioms KCore.C3SimpComm.simp_text
#print axioms KCore.C3SimpComm.eval_all
#print axioms KCore.C3SimpComm.simp_ev
#print axioms KCore.C3SimpComm.sem_eq
#print axioms KCore.C3SimpComm.withHooks_eq
#print axioms KCore.C3SimpComm.gamma_eq
