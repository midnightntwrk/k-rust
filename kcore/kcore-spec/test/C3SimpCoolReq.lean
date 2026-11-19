/-
  The C2 evidence of the pair `cool` x `requires` on a simplification (status inert) on the fixture
  c3-simp-cool-req: `rule f(X) => X` beside
  `rule f(f(X)) => f(X) requires X >Int 0 [simplification, cool]`, with `syntax KResult ::= Int`.
  The text is `f2-examples/c3-simp-cool-req.kompile.kore`: the kompiled text that
  `test/constructs/fixtures/c3-simp-cool-req/kompile.txt` records, with its paths restored. kompile
  conjoins `isKResult(HOLE)` to the author's `requires`, HOLE of sort K in no side of the sentence.
  Run from the package root: `lake env lean -j1 test/C3SimpCoolReq.lean`. Every statement is on the
  literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  - `coreOK`; `simp_class`: the reader leaves the simplification sentence (axiom 205) inert, class
    `simplification`; `simp_text`: its pattern is
    `\implies{R}(\equals{SortBool{}, R}(X >Int 0 andBool isKResult(HOLE), true),
      \equals{SortInt{}, R}(f(f(X)), \and{SortInt{}}(f(X), \top{SortInt{}}())))`, X and HOLE free.
  - `eval_all`: `f(n) = n` at every integer n, for every H.
  - `isKResult_total`: the sort predicate `isKResult` has a value at every K, for every H (it has a
    clause over a variable of sort K and no `requires`); the value table takes that value.
  - `simp_ev`: the sentence is entailed by Γ at values, for every H: at an integer n and a K value
    for HOLE, `f(f(n))` and `f(n)` are both n, whatever the `requires` is
    (`InertEvUser.EqnU.entailed`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.C3SimpCoolReq

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/c3-simp-cool-req.kompile.kore"
definition_of defn from "f2-examples/c3-simp-cool-req.kompile.kore"
user_axioms U from "f2-examples/c3-simp-cool-req.kompile.kore" module "C3-SIMP-COOL-REQ"

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
theorem okAll_c : c.okAll = true := by decide_cheap
theorem srReady_c : c.srReady = true := by decide_cheap

def f : Sym := 385
def isKR : Sym := 382
def andBoolS : Sym := 4

theorem names : c.symName f = "Lblf" ∧ c.symName isKR = "LblisKResult" ∧
    c.symName andBoolS = "Lbl'Unds'andBool'Unds'" ∧ c.symName intGt = "Lbl'Unds-GT-'Int'Unds'" := by
  decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

theorem hfn : c.lookupFn f = some fn := rfl
theorem hfnH (H : HookParams) : (cH H).lookupFn f = some fn := by rw [Semantics.lookupFn_withHooks]; exact hfn
theorem fn_args : fn.args = [Srt.int] := by decide +kernel
theorem hkf : lookupSig hookSigs f = none := by decide +kernel
theorem hkK : lookupSig hookSigs isKR = none := by decide +kernel

/-! ## The sentence -/

/-- The simplification sentence. -/
noncomputable abbrev simpAx : AxiomDecl := U.ax205

/-- The reader's class of the sentence. -/
theorem simp_class : Parse.classifyShape (.axiom simpAx.ax) = .inert .simplification := by decide +kernel

/-- `f(f(X)) => f(X) requires X >Int 0 andBool isKResult(HOLE)` as an equation over `f`. -/
def E : LibEv.Eqn :=
  ⟨[("VarX", Srt.int), ("VarHOLE", Srt.k)], Srt.int,
    some (.app andBoolS [.app intGt [.var 0, .dv Srt.int (.int 0)], .app isKR [.var 1]]),
    .app f [.app f [.var 0]], .app f [.var 0]⟩

/-- **The sentence is `E`'s pattern**, over the one sort variable `R`, `VarX` and `VarHOLE` free in
it. -/
theorem simp_text : simpAx.ax.pattern = E.pattern c ∧ simpAx.ax.sortVars = [Rv] ∧
    (trS simpAx).pat = (trAxiom [] [] simpAx).pat ∧
    LibEv.vkey c E.vars 0 ∈ freeOf [] simpAx.ax.pattern ∧
    LibEv.vkey c E.vars 1 ∈ freeOf [] simpAx.ax.pattern := by
  decide +kernel

kernel_rfl pattern_wh : ∀ H : HookParams, E.pattern (cH H) = E.pattern c
kernel_rfl vkey_wh : ∀ H : HookParams, ∀ i : Nat, LibEv.vkey (cH H) E.vars i = LibEv.vkey c E.vars i

/-! ## `f`'s value at every integer -/

/-- `f`'s one clause: `f(X) => X`. -/
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

/-! ## `isKResult`'s value at every K -/

/-- The sort predicate `isKResult` of the reading. -/
noncomputable abbrev fnK : Fn := c.sortPreds[14]'(by decide +kernel)

theorem fnK_label : fnK.label = isKR := by decide +kernel
theorem fnK_mem : fnK ∈ c.sortPreds := List.getElem_mem _

theorem evalCtxN_H (H : HookParams) : EvalCtxN (cH H) := by
  have hokA : (cH H).okAll = true := (Semantics.okAll_withHooks c H).trans okAll_c
  exact evalCtxN_of_all (hpreTop := Semantics.preTop_of_okAll hokA) (Semantics.fnsNoExs_of_okAll hokA)
    (Semantics.sortedOK_of_okAll hokA
      (Semantics.ovlPatsOK_of_ovlCase (Semantics.ovlCase_of_core (coreOKH H))))
    ((Semantics.srReady_withHooks c H).trans srReady_c) (Semantics.ovlCase_of_core (coreOKH H))

/-- **`isKResult` has a value at every K, for every H.** -/
theorem isKResult_total (H : HookParams) : Total (cH H) isKR := by
  have h := sortPreds_totalN (evalCtxN_H H) (fn := fnK) fnK_mem
  rw [fnK_label] at h
  exact h

/-- `isKResult`'s value at an argument list, where it has one. -/
noncomputable def kresVal (H : HookParams) (ws : List GroundTerm) : Option GroundTerm :=
  open Classical in
  if h : ∃ v, Eval (cH H) isKR ws (some v) then some (Classical.choose h) else none

/-- The value table of `f` (`f(n) = n`) and of `isKResult` (its value, for H). -/
noncomputable def tbl (H : HookParams) : InertEvUser.ValTable := fun s =>
  if s = f then some fun ws => match ws with
    | [.dv _ (.int n)] => some (int n)
    | _ => none
  else if s = isKR then some (kresVal H)
  else none

theorem tbl_f (H : HookParams) : tbl H f = some fun ws => match ws with
    | [.dv _ (.int n)] => some (int n)
    | _ => none := by
  simp [tbl]

theorem tbl_isKR (H : HookParams) : tbl H isKR = some (kresVal H) := by
  simp [tbl, f, isKR]

/-- **The table is `Eval`'s**, for every H. -/
theorem table_ok (H : HookParams) : InertEvUser.TableOK (cH H) (tbl H) := by
  intro s g fn' ws hg _ hfn' hws
  by_cases hs : s = f
  · subst hs
    rw [tbl_f, Option.some.injEq] at hg
    subst hg
    have he : fn' = fn := Option.some.inj (hfn'.symm.trans (hfnH H))
    subst he
    rw [fn_args, Semantics.sortsOf_withHooks _ _ noRaw] at hws
    obtain ⟨w, ws', rfl, hw, hws'⟩ := sortsOf_inv_cons hws
    cases sortsOf_inv_nil hws'
    obtain ⟨n, rfl⟩ := shape_int shapesOK_c hw
    exact eval_all H n
  · by_cases hk : s = isKR
    · subst hk
      rw [tbl_isKR, Option.some.injEq] at hg
      subst hg
      obtain ⟨v, hv⟩ := isKResult_total H fn' hfn' ws hws
      have hex : ∃ v, Eval (cH H) isKR ws (some v) := ⟨v, hv⟩
      simp only [kresVal, hex, dite_true]
      exact Classical.choose_spec hex
    · simp [tbl, hs, hk] at hg

/-- The table with an `isKResult` entry that is not its value: the typing reads no entry's
results. -/
def tbl0 : InertEvUser.ValTable := fun s =>
  if s = f then some fun _ => none
  else if s = isKR then some fun _ => none
  else none

theorem typed0 : InertEvUser.EqnU.typed c tbl0 E = true := by decide +kernel
kernel_rfl typed_wh : ∀ H : HookParams, InertEvUser.EqnU.typed (cH H) (tbl H) E = InertEvUser.EqnU.typed c tbl0 E

/-- `f(f(n)) = f(n)` at every integer n and every K value of HOLE, under the table (where the
`requires` is true, and elsewhere). -/
theorem holds (H : HookParams) : InertEvUser.EqnU.Holds (cH H) (tbl H) E := by
  intro σ hσ _
  obtain ⟨v, hv, hvs⟩ := hσ 0 _ rfl
  rw [Semantics.sortOf_withHooks _ _ noRaw] at hvs
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c hvs
  have ha : InertEvUser.appU (cH H) (tbl H) f = fun ws => match ws with
      | [.dv _ (.int n)] => some (int n)
      | _ => none := InertEvUser.appU_fn hkf (tbl_f H)
  simp only [E, InertEvUser.valU, InertEvUser.valUList, allSome, hv, ha, Option.bind_some, Option.map_some]
  rfl

/-- **The simplification sentence is entailed by Γ at values**, for every H. -/
theorem simp_ev (H : HookParams) : EntailsAtValues (cH H) simpAx (trS simpAx).pat := by
  obtain ⟨hp, hsv, htr, hfv0, hfv1⟩ := simp_text
  rw [htr]
  refine InertEvUser.EqnU.entailed (coreOKH H) (hokH H) (table_ok H) E ((typed_wh H).trans typed0) (holds H)
    simpAx (hp.trans (pattern_wh H).symm) hsv (fun i hi => ?_)
  rw [vkey_wh H]
  have : i = 0 ∨ i = 1 := by simp [E] at hi; omega
  rcases this with rfl | rfl
  · exact hfv0
  · exact hfv1

end KCore.C3SimpCoolReq

#check @KCore.C3SimpCoolReq.simp_ev
#print axioms KCore.C3SimpCoolReq.simp_class
#print axioms KCore.C3SimpCoolReq.simp_text
#print axioms KCore.C3SimpCoolReq.eval_all
#print axioms KCore.C3SimpCoolReq.isKResult_total
#print axioms KCore.C3SimpCoolReq.simp_ev
