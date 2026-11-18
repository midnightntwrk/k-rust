/-
  An overload whose larger symbol is a function (CN-4b section 5, unit OVF), through the reader:
  the three fixtures e5-ovl-fn-fn, e5-ovl-fn-fn-owise and e5-ovl-fn-fn-ctor, each read from its
  kompiled text `f2-examples/NAME.kompile.kore` (the fixture's cached `definition.kore`, sha256 in
  its `kompile.txt`, with its `Source` paths restored). Every statement is on the literal `defn`
  and, where it reads an interpretation, for every H. Nothing here reads `emit`. Run from the
  package root: `lake env lean -j1 test/OvlFnFnRead.lean`. test/OvlFnFn.lean has the same facts on
  clauses built by hand.

  ## Fn: e5-ovl-fn-fn

  `Exp ::= Int | e`, `negExp : Exp → Exp` a function, `negInt : Int → Int` a total function with
  `negInt(I) = 0 -Int I`, the user equation `negExp(e #as G0) = G0`, and the symbol-overload
  sentence `negExp(inj{Int,Exp}(K0)) = inj{Int,Exp}(negInt(K0))`.
  - The reading (`reading`): `coreOK`; `negExp`'s clauses are the overload sentence, `aside` and of
    priority 0, its pattern the injected variable and its right side the injected application, then
    the user equation; `negExp` is no overloading symbol (`isOvl` false).
  - `negExp(inj 3)` is `inj -3`, by the `aside` clause (`eval_inj3`); `negExp(e)` is `e`, by the
    user clause (`eval_e`); for every H.
  - `FnHyp` (`fnHyp`: every obligation the deciders leave is empty; the two clauses of `negExp` meet
    at no argument), hence `ClausesAgree` of `negExp` (`agree`), and `Consistent` (`consistent`);
    for every H.

  ## Ow: e5-ovl-fn-fn-owise, a text whose reading has no model

  The same with `rule neg(_:Exp) => e [owise]`, whose premise in the text negates the user equation
  only (fixture.toml), so the clause is of priority 200 and the overload clause stays `aside`.
  - The reading (`reading`): `coreOK`; the three clauses; the agreement of `negExp` is the one named
    fact (`agree_named`: owed).
  - At `inj 3`: `inj -3` by the `aside` clause (`eval_ovl`) and `e` by the `[owise]` clause, the user
    clause failing there (`eval_owise`); hence not `FnDet` and not `ClausesAgree` of `negExp`
    (`not_fnDet`, `not_agree`: the owed fact is false); for every H.
  - **Γ has no model** (`no_model`): in a model of Γ, `negExp(inj 3)` denotes both results, which are
    distinct values of Exp. Hence not `Consistent` (`not_consistent`); for every H.

  ## Ct: e5-ovl-fn-fn-ctor

  `N ::= z`, `Exp ::= N | e`, `sExp : Exp → Exp` a function overloading the constructor
  `sN : N → N`, the user equation `sExp(e #as G0) = G0`.
  - The reading (`reading`): as Fn's, the right side of the `aside` clause the constructor term
    `inj{N,Exp}(sN(K0))`.
  - `sExp(inj z)` is `inj (sN z)` (`eval_inj_z`), `sExp(e)` is `e` (`eval_e`); `FnHyp`, `ClausesAgree`
    of `sExp`, `Consistent`; for every H.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.OvlFnFnRead

open KCore ML Faithful KoreAML

/-! ## Facts over any semantics -/

/-- **A defined result is a theorem of Γ**, for a semantics with `HypSoundCore`: where `f` has the
value `v` at `vs`, `Γ` entails `f(vs) = v` (`eval_den4`). -/
theorem eval_some_sound_core (c : Semantics) (h : HypSoundCore c)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) {f : Sym} {fn : Fn} {vs : List GroundTerm}
    {v : GroundTerm} (hE : Eval c f vs (some v)) (hfn : c.lookupFn f = some fn) (hvs : c.sortsOf vs = some fn.args) :
    Γ c ⊧ (KoreAML.den (symApp c f (GroundTerm.koreList c vs)) ≡ den c v) := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  intro M _ I hI e m
  have hex : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ExclEmpty c I fn cl := fun fn hfn cl hcl => by
    obtain ⟨hp', hb', -⟩ := clause_ctx hok hbc hfn hcl
    exact fun hws _ hkeys hXkeys hRkey _ hX _ hR hσR hfail m =>
      exclusion_emptyC hI hph hcs hcso hg hsc.trans hnn.1 (clause_preTop (hpreTop := by decide +kernel) hok hfn hcl) hp' hb' (collPats_of_sorted hph' hp') hws hkeys hXkeys
        hRkey hX hR hσR hfail m
  rw [KoreAML.interp_equal (defOK hI)]
  intro a
  rw [eval_den4 (hpreTop := by decide +kernel) hI hnn hsc hok hbc hph (fun fn hfn cl hcl _ => hex fn hfn cl hcl) hE hfn hvs e a]
  rfl

/-- **Two values of one sort that one pattern equals in a model of Γ are one value**: distinct
values are distinct elements. -/
theorem same_value_of_model (c : Semantics) (h : HypSoundCore c) {M : Type} [Inhabited M]
    {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) {X : P} {v w : GroundTerm} {s : Srt}
    (hv : c.sortOf v = some s) (hw : c.sortOf w = some s)
    (h1 : Γ c ⊧ (X ≡ den c v)) (h2 : Γ c ⊧ (X ≡ den c w)) : v = w := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have e : Valuation M := ⟨fun _ => default, fun _ _ => False⟩
  have k1 := h1 hI e default
  have k2 := h2 hI e default
  rw [KoreAML.interp_equal (defOK hI)] at k1 k2
  have hvv : (den c v).interpret I e (elemOf c I v) := ((elemOf_spec hI hv e).1 _).mpr rfl
  have hX : X.interpret I e (elemOf c I v) := (k1 _).mpr hvv
  have hwv : (den c w).interpret I e (elemOf c I v) := (k2 _).mp hX
  have he : elemOf c I v = elemOf c I w := ((elemOf_spec hI hw e).1 _).mp hwv
  exact values_apart hI hg hsc.trans (apartSort_of_sorted hg hv) hv hw he

theorem ws1 {c : Semantics} {s : Srt} {v : GroundTerm} (hv : c.sortOf v = some s) : c.WellSorted [s] [(0, v)] :=
  fun i s' h => by
    cases i with
    | zero => cases h; exact ⟨v, rfl, hv⟩
    | succ i => simp at h

/-- A clause without a `requires` and without a `pre` whose patterns match does not fail. -/
theorem not_fails_noReq {c : Semantics} {vs : List GroundTerm} {cl : Clause} {σ : Subst} (hq : cl.req = none)
    (hpre : cl.pre = .top)
    (hw : c.WellSortedAt cl.vars cl.leftVars σ) (hp : PatVals c σ cl.pats vs) (hf : Fails c vs cl) : False := by
  cases hf with
  | intro h =>
    cases h σ hw hp with
    | intro ht _ _ => rw [hq] at ht; cases ht
    | pre h => rw [hpre] at h; exact absurd (Holds.top_eq h) (by simp)

/-! ## Fn: e5-ovl-fn-fn -/

namespace Fn

definition_of defn from "f2-examples/e5-ovl-fn-fn.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def expS : Srt := 32
def eS : Sym := 385
def negExp : Sym := 386
def negInt : Sym := 387

theorem names : c.sortName expS = "Exp" ∧ c.symName eS = "Lble" ∧ c.symName negExp = "LblnegExp" ∧
    c.symName negInt = "LblnegInt" := by decide +kernel

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem wf_defn : wf defn = true := by decide_cheap
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The overload sentence, as a clause of `negExp`. -/
def ovlCl : Clause :=
  { vars := [Srt.int], pats := [.inj Srt.int expS (.var 0)], req := none,
    rhs := .inj Srt.int expS (.app negInt [.var 0]), ens := none, prio := 0, aside := true }
/-- `negExp(e #as G0) = G0`. -/
def userCl : Clause := { vars := [expS], pats := [.as (.app eS []) 0], req := none, rhs := .var 0, ens := none }

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

/-- **The reading**: `negExp`'s clauses are the overload sentence (`aside`, priority 0) and the user
equation; `negExp` is no overloading symbol. -/
theorem reading : (fn.label = negExp ∧ fn.args = [expS] ∧ fn.result = expS ∧ c.isOvl negExp = false) ∧
    fn.clauses = [ovlCl, userCl] := ⟨by decide +kernel, rfl⟩

theorem hfn : c.lookupFn negExp = some fn := rfl
theorem hfnH (H : HookParams) : (cH H).lookupFn negExp = some fn := by rw [Semantics.lookupFn_withHooks]; rfl
theorem fn_memH (H : HookParams) : fn ∈ (cH H).fns := by
  show fn ∈ c.fns
  exact List.getElem_mem _

theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel

def v3 : GroundTerm := .dv Srt.int (.int 3)
/-- `inj{Int,Exp}(3)` -/
def i3 : GroundTerm := .inj Srt.int expS v3
/-- `inj{Int,Exp}(-3)` -/
def im3 : GroundTerm := .inj Srt.int expS (.dv Srt.int (.int (-3)))
/-- `e` -/
def ve : GroundTerm := .ctor eS []

theorem sorts_i3 : c.sortsOf [i3] = some fn.args := by decide +kernel
theorem sorts_e : c.sortsOf [ve] = some fn.args := by decide +kernel

/-- **`negExp(inj 3)` is `inj -3`**, for every H: the `aside` clause of priority 0 decides. -/
theorem eval_inj3 (H : HookParams) : Eval (cH H) negExp [i3] (some im3) :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfn sorts_i3 (n := 10) (by decide +kernel)

/-- **`negExp(e)` is `e`**, for every H: the only clause below the user clause is `aside`. -/
theorem eval_e (H : HookParams) : Eval (cH H) negExp [ve] (some ve) :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfn sorts_e (n := 10) (by decide +kernel)

def callOrder : List Nat := [negInt, negExp]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel

theorem confined_named : c.readsConfined = false := by decide +kernel

/-- None named, for every H; `OpenDecided` as no rule or clause reads a confined sort, `OpenLaws` as
no parameter is an open generator (the definition is not `plain`: it has an `aside` clause). -/
theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  have h1 : (cH H).rankObligations callOrder ++ (cH H).decObligationsL = [] := by
    rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named
  have h2 : (cH H).totalObligationsRP callOrder [] = [] := (Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named
  have h3 : (cH H).agreeObligationsI = [] := (Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named
  have h4 : (cH H).matchObligationsL = [] := (Det.Semantics.matchObligationsL_withHooks _ H).trans match_named
  ⟨fun f hf => by rw [h1] at hf; exact absurd hf List.not_mem_nil,
   fun f hf => by rw [h2] at hf; exact absurd hf List.not_mem_nil,
   fun f hf => by rw [h3] at hf; exact absurd hf List.not_mem_nil,
   fun p hp => by rw [h4] at hp; exact absurd hp List.not_mem_nil,
   openDecided_of_readsConfined ((Semantics.readsConfined_withHooks c H).trans confined_named),
   openLaws_of_plain (c := cH H) noRaw⟩

/-- **`FnHyp`**, for every H. -/
theorem fnHyp (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- **`ClausesAgree` of `negExp`**, for every H: the `aside` clause and the user clause compete and
meet at no argument. -/
theorem agree (H : HookParams) : ClausesAgree (cH H) fn := (fnHyp H).2.2.1 fn (fn_memH H)

/-- **`Consistent`**, for every H. -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHyp H)

end Fn

/-! ## Ow: e5-ovl-fn-fn-owise -/

namespace Ow

definition_of defn from "f2-examples/e5-ovl-fn-fn-owise.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def expS : Srt := 32
def eS : Sym := 385
def negExp : Sym := 386
def negInt : Sym := 387

theorem names : c.sortName expS = "Exp" ∧ c.symName eS = "Lble" ∧ c.symName negExp = "LblnegExp" ∧
    c.symName negInt = "LblnegInt" := by decide +kernel

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem wf_defn : wf defn = true := by decide_cheap
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- `negExp(_) => e [owise]`. -/
def owiseCl : Clause := { vars := [expS], pats := [.var 0], req := none, rhs := .app eS [], ens := none, prio := 200 }

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)
noncomputable abbrev clV : Clause := fn.clauses[0]'(by decide +kernel)
noncomputable abbrev clU : Clause := fn.clauses[1]'(by decide +kernel)
noncomputable abbrev clO : Clause := fn.clauses[2]'(by decide +kernel)

/-- **The reading**: the overload clause (`aside`, priority 0), the user equation and the `[owise]`
clause (priority 200, not `aside`). -/
theorem reading : (fn.label = negExp ∧ fn.args = [expS] ∧ c.isOvl negExp = false) ∧
    fn.clauses = [Fn.ovlCl, Fn.userCl, owiseCl] := ⟨by decide +kernel, rfl⟩

theorem fn_clauses : fn.clauses = [clV, clU, clO] := rfl
theorem hfn : c.lookupFn negExp = some fn := rfl
theorem hfnH (H : HookParams) : (cH H).lookupFn negExp = some fn := by rw [Semantics.lookupFn_withHooks]; rfl
theorem fn_memH (H : HookParams) : fn ∈ (cH H).fns := by
  show fn ∈ c.fns
  exact List.getElem_mem _

/-- **The agreement of `negExp` is the one named fact** (owed), for every H. -/
theorem agree_named : c.agreeObligationsI = [negExp] := by decide +kernel
theorem agree_namedH (H : HookParams) : (cH H).agreeObligationsI = [negExp] :=
  (Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named

theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel

theorem rV : clV.rhs = .inj Srt.int expS (.app negInt [.var 0]) := rfl
theorem pV : clV.prio = 0 := rfl
theorem aV : clV.aside = true := rfl
theorem aU : clU.aside = false := rfl
theorem pU : clU.prio = 50 := rfl
theorem pO : clO.prio = 200 := rfl
theorem vO : clO.vars = [expS] := rfl
theorem ptO : clO.pats = [.var 0] := rfl
theorem qO : clO.req = none := rfl
theorem rO : clO.rhs = .app eS [] := rfl
theorem eO : clO.ens = none := rfl
theorem preO : clO.pre = .top := rfl
theorem exsO : clO.exs = [] := rfl
theorem exsV : clV.exs = [] := rfl
theorem exsU : clU.exs = [] := rfl
theorem postO : clO.post = .top := rfl
theorem postV : clV.post = .top := rfl
theorem ptU : clU.pats = [.as (.app eS []) 0] := rfl
theorem eV : clV.ens = none := rfl
theorem eU : clU.ens = none := rfl

def i3 : GroundTerm := .inj Srt.int expS (.dv Srt.int (.int 3))
def im3 : GroundTerm := .inj Srt.int expS (.dv Srt.int (.int (-3)))
def ve : GroundTerm := .ctor eS []

theorem i3_ne_ve : i3 ≠ ve := by simp [i3, ve]
theorem im3_ne_ve : im3 ≠ ve := by simp [im3, ve]

theorem sorts_i3 : c.sortsOf [i3] = some fn.args := by decide +kernel
theorem sorts_i3H (H : HookParams) : (cH H).sortsOf [i3] = some fn.args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact sorts_i3
theorem sort_i3H (H : HookParams) : (cH H).sortOf i3 = some expS := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem sort_im3H (H : HookParams) : (cH H).sortOf im3 = some expS := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem sort_veH (H : HookParams) : (cH H).sortOf ve = some expS := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem isCtor_eH (H : HookParams) : (cH H).isCtor eS = true := (by decide +kernel : c.isCtor eS = true)
theorem hook_e : patternHooks.contains eS = false := by decide

/-- At `inj 3`: `inj -3`, by the `aside` clause, for every H. -/
theorem eval_ovl (H : HookParams) : Eval (cH H) negExp [i3] (some im3) :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfn sorts_i3 (n := 10) (by decide +kernel)

/-- The pattern of `e` denotes `e` only. -/
theorem patVal_e {H : HookParams} {σ : Subst} {v : GroundTerm} (h : PatVal (cH H) σ (.app eS []) v) : v = ve := by
  cases h with
  | ctor _ hs => cases hs; rfl
  | hook hp _ _ => rw [hook_e] at hp; cases hp
  | coll hc _ _ _ => rw [isCtor_eH H] at hc; cases hc
  | ovl hc _ _ _ => rw [isCtor_eH H] at hc; cases hc

/-- The user clause fails at `inj 3`: its pattern `e #as G0` does not denote it. -/
theorem userCl_fails_i3 (H : HookParams) : Fails (cH H) [i3] clU := .intro fun σ _ hp => by
  rw [ptU] at hp
  cases hp with
  | cons h _ =>
    cases h with
    | as h' _ => exact absurd (patVal_e h') i3_ne_ve

theorem appliesO (H : HookParams) : clO.AppliesAt (cH H) [(0, i3)] [i3] :=
  ⟨by rw [vO]; exact (ws1 (sort_i3H H)).at _,
   by rw [ptO]; exact .cons (.var rfl) .nil,
   (fun t ht => by rw [qO] at ht; cases ht), Clause.holds_preTop preO _⟩

/-- The clauses below the `[owise]` one that are not `aside` (the user clause) fail at `inj 3`. -/
theorem lowerO (H : HookParams) :
    ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < clO.prio → Fails (cH H) [i3] cl' :=
  fun cl' h ha hlt => by
    rw [fn_clauses] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · rw [aV] at ha; cases ha
    · exact userCl_fails_i3 H
    · exact absurd hlt (Nat.lt_irrefl _)

/-- At `inj 3`: `e`, by the `[owise]` clause, for every H. -/
theorem eval_owise (H : HookParams) : Eval (cH H) negExp [i3] (some ve) :=
  .clause (cl := clO) (σ := [(0, i3)]) (hfnH H) (by rw [fn_clauses]; simp)
    ((wellSortedAt_univ exsO).mp (appliesO H).1) (appliesO H).2.1 (appliesO H).2.2.1 (appliesO H).2.2.2 (lowerO H)
    exsO (by rw [rO]; exact .ctor (isCtor_eH H) .nil) (fun t ht => by rw [eO] at ht; cases ht)
    (Clause.holds_postTop postO _)

/-- **Not `FnDet`**, for every H: two results at `inj 3`. -/
theorem not_fnDet (H : HookParams) : ¬ FnDet (cH H) :=
  fun h => im3_ne_ve (Option.some.inj (h _ _ _ _ (eval_ovl H) (eval_owise H)))

/-- The right side of the `[owise]` clause, `e`, has the one result `e`. -/
theorem evalTerm_e {H : HookParams} {σ : Subst} {r : Option GroundTerm} (h : EvalTerm (cH H) σ (.app eS []) r) :
    r = some ve := by
  cases h with
  | ctor _ hts => cases hts; rfl
  | hook hc _ _ _ _ => rw [isCtor_eH H] at hc; cases hc
  | param hc _ _ _ _ => rw [isCtor_eH H] at hc; cases hc
  | call hc _ _ _ _ _ => rw [isCtor_eH H] at hc; cases hc
  | callUndef hc _ _ _ _ => rw [isCtor_eH H] at hc; cases hc
  | ovl hc _ _ => rw [isCtor_eH H] at hc; cases hc
  | ovlFn hc _ => rw [isCtor_eH H] at hc; cases hc

/-- The `aside` clause applies at `inj 3` under a σ at which its right side is `inj -3`: the only
derivation of `eval_ovl`'s result is by that clause. -/
theorem rhsV (H : HookParams) : ∃ σ, clV.AppliesAt (cH H) σ [i3] ∧ EvalTerm (cH H) σ clV.rhs (some im3) := by
  have key : ∀ r, Eval (cH H) negExp [i3] r → r = some im3 →
      ∃ σ, clV.AppliesAt (cH H) σ [i3] ∧ EvalTerm (cH H) σ clV.rhs (some im3) := by
    intro r h hr
    cases h with
    | clause hfn' hmem hσ hmatch hreq hpre _ _ hrhs _ _ =>
      rw [hfnH H] at hfn'; cases hfn'
      subst hr
      rw [fn_clauses] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact ⟨_, ⟨hσ.at _, hmatch, hreq, hpre⟩, hrhs⟩
      · rw [ptU] at hmatch
        cases hmatch with
        | cons h1 _ =>
          cases h1 with
          | as h' _ => exact absurd (patVal_e h') i3_ne_ve
      · rw [rO] at hrhs
        exact absurd (evalTerm_e hrhs) (fun h => im3_ne_ve (Option.some.inj h))
    | rest hfn' hnone =>
      rw [hfnH H] at hfn'; cases hfn'
      exact (not_fails_noReq qO preO (by rw [vO]; exact (ws1 (sort_i3H H)).at _)
        (by rw [ptO]; exact .cons (.var rfl) .nil) (hnone clO (by rw [fn_clauses]; simp))).elim
    | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ =>
      rw [hfnH H] at hfn'; cases hfn'
      rw [fn_clauses] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · rw [eV] at ht; cases ht
      · rw [eU] at ht; cases ht
      · rw [eO] at ht; cases ht
    | clauseEx hfn' hmem _ _ _ _ _ hne =>
      rw [hfnH H] at hfn'; cases hfn'
      rw [fn_clauses] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact absurd exsV hne
      · exact absurd exsU hne
      · exact absurd exsO hne
    | exNone => cases hr
  exact key _ (eval_ovl H) rfl

/-- **Not `ClausesAgree` of `negExp`** (the owed fact is false), for every H: the `[owise]` clause
and the `aside` clause compete (the `aside` one has the smaller priority) and both decide at
`inj 3`, with `e` and `inj -3`. -/
theorem not_agree (H : HookParams) : ¬ ClausesAgree (cH H) fn := fun h => by
  have hp : (clV, clO) ∈ pairs fn.clauses := by rw [fn_clauses]; simp [pairs]
  have hcomp : clV.prio = clO.prio ∨ (clV.aside = true ∧ clV.prio < clO.prio) ∨
      (clO.aside = true ∧ clO.prio < clV.prio) := .inr (.inl ⟨aV, by rw [pV, pO]; decide⟩)
  have hco := (h clV clO hp hcomp).2
  obtain ⟨σV, hapV, hrV⟩ := rhsV H
  have hdet : HDet (cH H) [(0, i3)] clO.rhs := by
    rw [rO]
    intro u hu r r' h1 h2
    simp only [subterms, subtermsList, List.mem_cons, List.not_mem_nil, or_false] at hu
    subst hu
    rw [evalTerm_e h1, evalTerm_e h2]
  have hdecO : clO.Decides (cH H) fn [(0, i3)] [i3] := ⟨appliesO H, lowerO H⟩
  have hdecV : clV.Decides (cH H) fn σV [i3] :=
    ⟨hapV, fun _ _ _ hlt => absurd hlt (by rw [pV]; exact Nat.not_lt_zero _)⟩
  rcases hco [i3] [(0, i3)] σV (appliesO H) hapV (fun t ht => by rw [qO] at ht; cases ht)
      (fun _ _ => hdet) (fun _ t ht => by rw [eO] at ht; cases ht) (fun hne => absurd exsO hne)
      ⟨negExp, fn, hfnH H, by rw [fn_clauses]; simp, by rw [fn_clauses]; simp, hdecO, hdecV⟩ with
    ⟨-, -, hrhs, -⟩ | hr
  · rw [rO, rV] at hrhs; cases hrhs
  · exact im3_ne_ve (Option.some.inj (hr (some ve) (some im3)
      (.inl ⟨exsO, .inl ⟨(fun t ht => by rw [eO] at ht; cases ht), Clause.holds_postTop postO _,
        by rw [rO]; exact .ctor (isCtor_eH H) .nil⟩⟩)
      (.inl ⟨exsV, .inl ⟨(fun t ht => by rw [eV] at ht; cases ht), Clause.holds_postTop postV _, hrV⟩⟩))).symm

/-! ### Γ has no model, for every H -/

theorem okH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok

/-- `Γ` entails `negExp(inj 3) = v` for each result v, for every H. -/
theorem entails_i3 (H : HookParams) (v : GroundTerm) (hE : Eval (cH H) negExp [i3] (some v)) :
    Γ (cH H) ⊧ (KoreAML.den (symApp (cH H) negExp (GroundTerm.koreList (cH H) [i3])) ≡ den (cH H) v) :=
  eval_some_sound_core _ (hypSound_of_core (coreOKH H)) (Semantics.ok_clauseBinds (okH H)) hE (hfnH H) (sorts_i3H H)

/-- **Γ has no model**, for every H: in a model, `negExp(inj 3)` denotes `inj -3` and `e` (the two
`Eval` results), distinct values of Exp. -/
theorem no_model (H : HookParams) {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M) :
    ¬ (I ⊧ᴵP Γ (cH H)) := fun hI =>
  im3_ne_ve (same_value_of_model _ (hypSound_of_core (coreOKH H)) hI (sort_im3H H) (sort_veH H)
    (entails_i3 H im3 (eval_ovl H)) (entails_i3 H ve (eval_owise H)))

/-- **Not `Consistent`**, for every H: `Γc` holds Γ. -/
theorem not_consistent (H : HookParams) : ¬ Consistent (cH H) := fun ⟨_, _, I, hI⟩ =>
  no_model H I fun φ hφ => hI φ (Or.inl (Or.inl hφ))

end Ow

/-! ## Ct: e5-ovl-fn-fn-ctor -/

namespace Ct

definition_of defn from "f2-examples/e5-ovl-fn-fn-ctor.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def nS : Srt := 32
def expS : Srt := 33
def eS : Sym := 386
def sN : Sym := 387
def zS : Sym := 388
def sExp : Sym := 389

theorem names : c.sortName nS = "N" ∧ c.sortName expS = "Exp" ∧ c.symName eS = "Lble" ∧
    c.symName sN = "LblsN" ∧ c.symName zS = "Lblz" ∧ c.symName sExp = "LblsExp" := by decide +kernel

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem wf_defn : wf defn = true := by decide_cheap
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The overload sentence, as a clause of `sExp`: its right side a constructor term. -/
def ovlCl : Clause :=
  { vars := [nS], pats := [.inj nS expS (.var 0)], req := none,
    rhs := .inj nS expS (.app sN [.var 0]), ens := none, prio := 0, aside := true }
/-- `sExp(e #as G0) = G0`. -/
def userCl : Clause := { vars := [expS], pats := [.as (.app eS []) 0], req := none, rhs := .var 0, ens := none }

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

/-- **The reading**: as e5-ovl-fn-fn's, `sN` a constructor and `sExp` no overloading symbol. -/
theorem reading : (fn.label = sExp ∧ fn.args = [expS] ∧ fn.result = expS ∧ c.isCtor sN = true ∧
    c.isOvl sExp = false) ∧ fn.clauses = [ovlCl, userCl] := ⟨by decide +kernel, rfl⟩

theorem hfn : c.lookupFn sExp = some fn := rfl
theorem fn_memH (H : HookParams) : fn ∈ (cH H).fns := by
  show fn ∈ c.fns
  exact List.getElem_mem _

theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel

def vz : GroundTerm := .ctor zS []
/-- `inj{N,Exp}(z)` -/
def iz : GroundTerm := .inj nS expS vz
/-- `inj{N,Exp}(sN(z))` -/
def isz : GroundTerm := .inj nS expS (.ctor sN [vz])
def ve : GroundTerm := .ctor eS []

theorem sorts_iz : c.sortsOf [iz] = some fn.args := by decide +kernel
theorem sorts_e : c.sortsOf [ve] = some fn.args := by decide +kernel

/-- **`sExp(inj z)` is `inj (sN z)`**, for every H, by the `aside` clause. -/
theorem eval_inj_z (H : HookParams) : Eval (cH H) sExp [iz] (some isz) :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfn sorts_iz (n := 10) (by decide +kernel)

/-- **`sExp(e)` is `e`**, for every H, by the user clause. -/
theorem eval_e (H : HookParams) : Eval (cH H) sExp [ve] (some ve) :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfn sorts_e (n := 10) (by decide +kernel)

def callOrder : List Nat := [sExp]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel

theorem confined_named : c.readsConfined = false := by decide +kernel

/-- None named, for every H; `OpenDecided` as no rule or clause reads a confined sort, `OpenLaws` as
no parameter is an open generator (the definition is not `plain`: it has an `aside` clause). -/
theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  have h1 : (cH H).rankObligations callOrder ++ (cH H).decObligationsL = [] := by
    rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named
  have h2 : (cH H).totalObligationsRP callOrder [] = [] := (Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named
  have h3 : (cH H).agreeObligationsI = [] := (Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named
  have h4 : (cH H).matchObligationsL = [] := (Det.Semantics.matchObligationsL_withHooks _ H).trans match_named
  ⟨fun f hf => by rw [h1] at hf; exact absurd hf List.not_mem_nil,
   fun f hf => by rw [h2] at hf; exact absurd hf List.not_mem_nil,
   fun f hf => by rw [h3] at hf; exact absurd hf List.not_mem_nil,
   fun p hp => by rw [h4] at hp; exact absurd hp List.not_mem_nil,
   openDecided_of_readsConfined ((Semantics.readsConfined_withHooks c H).trans confined_named),
   openLaws_of_plain (c := cH H) noRaw⟩

/-- **`FnHyp`**, for every H. -/
theorem fnHyp (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- **`ClausesAgree` of `sExp`**, for every H. -/
theorem agree (H : HookParams) : ClausesAgree (cH H) fn := (fnHyp H).2.2.1 fn (fn_memH H)

/-- **`Consistent`**, for every H. -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHyp H)

end Ct

end KCore.OvlFnFnRead

/-! The headline declarations depend on no axiom but `propext`, `Classical.choice`, `Quot.sound`. -/
/-- info: 'KCore.OvlFnFnRead.Fn.reading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OvlFnFnRead.Fn.reading
/-- info: 'KCore.OvlFnFnRead.Fn.eval_inj3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OvlFnFnRead.Fn.eval_inj3
/-- info: 'KCore.OvlFnFnRead.Fn.eval_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OvlFnFnRead.Fn.eval_e
/-- info: 'KCore.OvlFnFnRead.Fn.agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OvlFnFnRead.Fn.agree
/-- info: 'KCore.OvlFnFnRead.Fn.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OvlFnFnRead.Fn.consistent
/-- info: 'KCore.OvlFnFnRead.Ow.reading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OvlFnFnRead.Ow.reading
/-- info: 'KCore.OvlFnFnRead.Ow.agree_namedH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OvlFnFnRead.Ow.agree_namedH
/-- info: 'KCore.OvlFnFnRead.Ow.not_fnDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OvlFnFnRead.Ow.not_fnDet
/-- info: 'KCore.OvlFnFnRead.Ow.not_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OvlFnFnRead.Ow.not_agree
/-- info: 'KCore.OvlFnFnRead.Ow.no_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OvlFnFnRead.Ow.no_model
/-- info: 'KCore.OvlFnFnRead.Ow.not_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OvlFnFnRead.Ow.not_consistent
/-- info: 'KCore.OvlFnFnRead.Ct.reading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OvlFnFnRead.Ct.reading
/-- info: 'KCore.OvlFnFnRead.Ct.eval_inj_z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OvlFnFnRead.Ct.eval_inj_z
/-- info: 'KCore.OvlFnFnRead.Ct.eval_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OvlFnFnRead.Ct.eval_e
/-- info: 'KCore.OvlFnFnRead.Ct.agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OvlFnFnRead.Ct.agree
/-- info: 'KCore.OvlFnFnRead.Ct.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OvlFnFnRead.Ct.consistent
