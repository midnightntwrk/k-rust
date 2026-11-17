/-
  Guards of the reading notes (findings/REVIEW-RN-reading-notes.md §3): for each note whose
  justification is about a value `Γ` gives, the statement of that justification for every
  interpretation H of the points the text leaves open, never only at the parsed semantics (whose
  interpretation, `HookParams.none`, gives nothing). Run from the package root:
  `lake env lean test/Guards.lean`.

  - G0, "where every clause fails, no value": false since the rest is the interpretation's
    (`Eval.rest`, `Semantics.fnRest`); `g0_refuted` is its refutation. No reading note rests on it:
    the one that did (`ensuresAsRequires`) is replaced by `Clause.ens`.
  - G1, a function equation's `ensures` (`Clause.ens`, in place of `ensuresAsRequires`): where a
    clause decides and its `ensures` has a result other than `true`, the function has no value
    (`eval_noValue_of_ens_fails`, every semantics). On `f2-examples/ens.kompile.kore`, for every H:
    `half(-4)` has no value and `Γ` entails `half(-4) = ⊥` (`Ens.half_neg4_gamma`).
  - G2, the same beside an `[owise]` equation (in place of the refusal `ensuresPriority`):
    `f2-examples/ens-owise.kompile.kore`, for every H (`EnsOwise.half_neg4_gamma`).
  - G3, `projectionDomainAsClause`: krust's texts hold, for every sort X, the selector-domain axiom
    of its projection, `⌈project:X(K)⌉ = ∃V. K = kseq(inj{X,KItem}(V), dotk)`; K 7.1.337's kompile
    writes none (`starinit.kompile.kore` names `project:Int` in its declaration, one use and its
    one equation only). On `f2-examples/projapp.kore`, krust's text of a rule applying
    `project:Int`, the axiom is read as a clause of `project:Int` with the `ensures` `false`: for every H, `project:Int(K)` has
    no value at every K of sort K that is not an injected Int (`ProjK.projInt_none_off`) and `Γ`
    entails `project:Int(K) = ⊥` there (`ProjK.projInt_off_gamma`), `.K` among them
    (`ProjK.dotk_off`). On `starinit.kompile.kore` the text is silent at `.K`: its value there is
    the interpretation's (`Proj.projInt_dotk_open`), as the text allows.
  - G4, the selector-inverse lemma `⌈project:Int(K)⌉ → kseq(inj(project:Int(K)), dotk) = K`, a
    `simplification` axiom of krust's text (kompile's has none): for every H, where `project:Int(K)`
    has a value v, K is `kseq(inj{Int,KItem}(v), dotk)` (`ProjK.inverse_holds`, at the values `Eval`
    gives; its statement in `Γ`'s models is not proved here).
  - G5, `total`: under `RestTotal`, a function declared total is total wherever, at each argument
    list, every clause fails or the function has a value (`total_of_restTotal`).
  - G6, a parameter symbol that is no open generator and a function with no clause have one value
    under every interpretation (`fnRest_nil_eq_paramVal`).
  - G7, `setIdempotence`: `_Set_` at a common member is no silent point, and `hook` gives it no value
    (`setIdem_bot`).
  - G8, `ruleRightDefined`: for every semantics and every rule with no existential variables and
    whose predicates `pre` and `post` are `\top`, so under every interpretation, the rule's axiom
    without the premise `⌈rhs ∧ ens⌉` (`UndefRhsWitness.textRuleK`, the text's rewrite with the
    competitors' negation of the priority reading), with the definedness axioms, entails the axiom
    `Γ` reads (`prioRuleK`): `ruleRightDefined_weaker`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.Guards

open KCore ML Faithful

def int (n : Int) : GroundTerm := .dv Srt.int (.int n)

kernel_rfl clausesFixed_withHooks : ∀ (c : Semantics) (H : HookParams),
  (c.withHooks H).clausesFixed = c.clausesFixed
/-- The matcher and `evalFC` read no interpretation where no parameter is raw. -/
theorem clauseMatches_withHooks (c : Semantics) (H : HookParams) (hr : ∀ k ∈ c.params, k.raw = false) (cl : Clause)
    (vs : List GroundTerm) : Exec.clauseMatches (c.withHooks H) cl vs = Exec.clauseMatches c cl vs :=
  Cert.clauseMatches_withHooks_hr c H hr cl vs
theorem evalFC_withHooks (c : Semantics) (H : HookParams) (hr : ∀ k ∈ c.params, k.raw = false) (n : Nat) (f : Sym)
    (vs : List GroundTerm) : Cert.evalFC (c.withHooks H) n f vs = Cert.evalFC c n f vs :=
  Cert.evalFC_withHooks c H hr n f vs

/-- A function's result that `evalFC` computes on the data, which reads no interpretation, is its
result under every interpretation. -/
theorem eval_everyH {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (hr : ∀ k ∈ c.params, k.raw = false)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {vs : List GroundTerm} (hvs : c.sortsOf vs = some fn.args)
    {n : Nat} {r : Option GroundTerm} (h : Cert.evalFC c n f vs = some r) (H : HookParams) :
    Eval (c.withHooks H) f vs r := by
  have hok' := (Semantics.ok_withHooks c H).trans hok
  have hsr' := (Semantics.srReady_withHooks c H).trans hsr
  have hmr' := (Semantics.matchReady_withHooks c H).trans hmr
  exact Exec.evalF_sound (sortCtx_of hok' hsr' (Exec.ovlCase_of hmr')) (Exec.clauseCtx_of hok') (Exec.matchCtx_of hmr') n
    (Cert.evalFC_sound n (by rw [evalFC_withHooks c H hr]; exact h)) (by rw [Semantics.lookupFn_withHooks]; exact hfn)
    (by rw [Semantics.sortsOf_withHooks c H hr]; exact hvs)

/-! ## G0: where every clause fails, the value is the interpretation's -/

namespace NoClause

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 50, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 51, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

def F : Sym := nRegSyms + 100
def fnF : Fn := ⟨F, [Srt.int], Srt.int, [], false⟩

def nc : Semantics where
  lib := { sortsBelowKItem := [Srt.map, Srt.list, Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts
  ctors := cellCtors
  fns := [fnF]
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

/-- The interpretation that gives `F` the value 0 everywhere. -/
def Hc : HookParams := ⟨fun f _ => if f = F then some (int 0) else none⟩

end NoClause

open NoClause in
/-- **G0 is false**: a function with no clause has the interpretation's value at every argument
list of its sorts. -/
theorem g0_refuted : ¬ ∀ (c : Semantics) (f : Sym) (fn : Fn) (vs : List GroundTerm), c.lookupFn f = some fn →
    (∀ cl ∈ fn.clauses, Fails c vs cl) → ¬ ∃ v, Eval c f vs (some v) := by
  intro h
  have hl : (nc.withHooks Hc).lookupFn F = some fnF := by rw [Semantics.lookupFn_withHooks]; rfl
  have hr : (nc.withHooks Hc).fnRest fnF [int 0] = some (int 0) := by decide +kernel
  have hE := Eval.rest (c := nc.withHooks Hc) (vs := [int 0]) hl (fun cl hcl => by simp [fnF] at hcl)
  rw [hr] at hE
  exact h _ F fnF [int 0] hl (fun cl hcl => by simp [fnF] at hcl) ⟨_, hE⟩

/-! ## G1: an `ensures` that is not `true` where its clause decides gives no value -/

/-- **G1**, in every semantics whose clauses of one priority are coherent: a clause that decides at
`vs` (it applies, every clause of a smaller priority fails) and whose `ensures` has a result other
than `true` leaves its function without a value there. -/
theorem eval_noValue_of_ens_fails {c : Semantics} {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause}
    {σ : Subst} {e : Term} {r : Option GroundTerm} (hco : CoherentAll c)
    (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses) (hσ : c.WellSorted cl.vars σ)
    (hmatch : PatVals c σ cl.pats vs) (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl')
    (he : cl.ens = some e) (hev : EvalTerm c σ e r) (hr : r ≠ some (bool true)) :
    ¬ ∃ v, Eval c f vs (some v) := fun ⟨_, h⟩ =>
  nomatch Eval.functional hco h (.ensFails hfn hmem hσ hmatch hreq hprio he hev hr)

/-- `Γ` entails `f(vs) = ⊥` where `f` has no value, for every interpretation, from `coreOK` on the
data (`coreOK` does not read the interpretation). -/
theorem gamma_bot_everyH {c : Semantics} (hcore : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) {f : Sym} {fn : Fn} {vs : List GroundTerm}
    (hfn : c.lookupFn f = some fn) (hvs : c.sortsOf vs = some fn.args) (H : HookParams)
    (hE : Eval (c.withHooks H) f vs none) :
    Γ (c.withHooks H) ⊧ (KoreAML.den (symApp (c.withHooks H) f (GroundTerm.koreList (c.withHooks H) vs)) ≡ ⊥) :=
  eval_none_sound_core _ (hypSound_of_core ((Semantics.coreOK_withHooks c H).trans hcore)) hbc hE
    (by rw [Semantics.lookupFn_withHooks]; exact hfn) (by rw [Semantics.sortsOf_withHooks _ _ hr]; exact hvs)

namespace Ens

definition_of defn from "f2-examples/ens.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

def half : Sym := 387

theorem half_named : c.symName half = "Lblhalf" := by decide +kernel

private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn half = some (c.fns[0]'(by decide +kernel)) := rfl
theorem coreOK : c.coreOK = true := by decide +kernel

theorem half_neg4_none (H : HookParams) : Eval (c.withHooks H) half [int (-4)] none :=
  eval_everyH hok hsr hmr noRaw hfn (by decide +kernel) (n := 10) (by decide +kernel) H

/-- **G1 on `ens`**: under every interpretation, `Γ` entails `half(-4) = ⊥`. -/
theorem half_neg4_gamma (H : HookParams) :
    Γ (c.withHooks H) ⊧
      (KoreAML.den (symApp (c.withHooks H) half (GroundTerm.koreList (c.withHooks H) [int (-4)])) ≡ ⊥) :=
  gamma_bot_everyH coreOK noRaw (by decide +kernel) hfn (by decide +kernel) H (half_neg4_none H)

end Ens

/-! ## G2: the same beside an `[owise]` equation -/

namespace EnsOwise

definition_of defn from "f2-examples/ens-owise.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

def half : Sym := 387

theorem half_named : c.symName half = "Lblhalf" := by decide +kernel

private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn half = some (c.fns[0]'(by decide +kernel)) := rfl
theorem coreOK : c.coreOK = true := by decide +kernel

theorem half_neg4_none (H : HookParams) : Eval (c.withHooks H) half [int (-4)] none :=
  eval_everyH hok hsr hmr noRaw hfn (by decide +kernel) (n := 10) (by decide +kernel) H

/-- **G2 on `ens-owise`**: under every interpretation, `Γ` entails `half(-4) = ⊥`; the `[owise]`
equation does not give it 0. -/
theorem half_neg4_gamma (H : HookParams) :
    Γ (c.withHooks H) ⊧
      (KoreAML.den (symApp (c.withHooks H) half (GroundTerm.koreList (c.withHooks H) [int (-4)])) ≡ ⊥) :=
  gamma_bot_everyH coreOK noRaw (by decide +kernel) hfn (by decide +kernel) H (half_neg4_none H)

end EnsOwise

/-! ## G3, G4: the projection's domain and its selector-inverse lemma -/

-- K 7.1.337's text: no selector-domain axiom, so `project:Int` is the one clause of its equation.
namespace Proj

definition_of defn from "f2-examples/starinit.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

def projInt : Sym := 416

theorem projInt_named : c.symName projInt = "Lblproject'Coln'Int" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[4]'(by decide +kernel)

theorem fn_label : fn.label = projInt := by decide +kernel

/-- `project:Int`'s one clause, its equation `project:Int(kseq(inj{Int,KItem}(V), dotk)) = V`. -/
theorem fn_clauses : fn.clauses =
    [⟨[Srt.int], [.app kseq [.inj Srt.int Srt.kitem (.var 0), .app dotk []]], none, .var 0, none, 50, false, [], .top, .top⟩] := rfl

private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn projInt = some fn := rfl

/-- The interpretation that gives `project:Int(.K)` the value 0 and nothing else. -/
def H0 : HookParams := ⟨fun f vs => if f = projInt ∧ vs = [.ctor dotk []] then some (int 0) else none⟩

/-- `project:Int`'s one clause, `project:Int(kseq(inj{Int,KItem}(V), dotk)) = V`, does not match `.K`. -/
theorem fails_dotk (H : HookParams) : ∀ cl ∈ fn.clauses, Fails (c.withHooks H) [.ctor dotk []] cl := by
  have hok' := (Semantics.ok_withHooks c H).trans hok
  have hsr' := (Semantics.srReady_withHooks c H).trans hsr
  have hmr' := (Semantics.matchReady_withHooks c H).trans hmr
  have hfnH : (c.withHooks H).lookupFn projInt = some fn := by rw [Semantics.lookupFn_withHooks]; exact hfn
  have hnil : ∀ cl ∈ fn.clauses, Exec.clauseMatches c cl [.ctor dotk []] = [] := by decide +kernel
  have hd : ∀ cl ∈ fn.clauses, ∀ σ ∈ Exec.clauseMatches (c.withHooks H) cl [.ctor dotk []],
      Exec.clauseReq (c.withHooks H) 10 cl σ = some false := by
    intro cl hcl σ hσ
    rw [clauseMatches_withHooks c H (by decide +kernel), hnil cl hcl] at hσ
    cases hσ
  intro cl hcl
  have hmem : fn ∈ (c.withHooks H).allFns := (lookupFn_spec hfnH).1
  obtain ⟨L, hL, hclk⟩ := Exec.clauseCtx_of hok' fn hmem
  obtain ⟨hpt, hmf, hlc, hreq, -⟩ := hclk cl hcl
  exact Exec.fails_of_false (Exec.matchCtx_of hmr') (n := 10) (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel)
    hpt hmf hlc hreq
    (fun σ t r h hσ ht => Exec.evalT_sound (sortCtx_of hok' hsr' (Exec.ovlCase_of hmr')) (Exec.clauseCtx_of hok')
      (Exec.matchCtx_of hmr') 10 h hL hσ ht)
    (hd cl hcl)

/-- **The text is silent at `.K`**: the one equation does not apply there and no sentence speaks of
`project:Int(.K)`, so its value is the interpretation's rest: 0 under `H0`, none under
`HookParams.none`. -/
theorem projInt_dotk_open : Eval (c.withHooks H0) projInt [.ctor dotk []] (some (int 0)) ∧
    Eval (c.withHooks HookParams.none) projInt [.ctor dotk []] none := by
  have hl : ∀ H, (c.withHooks H).lookupFn projInt = some fn := fun H => by
    rw [Semantics.lookupFn_withHooks]; exact hfn
  have h0 : (c.withHooks H0).fnRest fn [.ctor dotk []] = some (int 0) := by decide +kernel
  have h1 : (c.withHooks HookParams.none).fnRest fn [.ctor dotk []] = none := by decide +kernel
  have e0 := Eval.rest (hl H0) (fails_dotk H0)
  have e1 := Eval.rest (hl HookParams.none) (fails_dotk HookParams.none)
  rw [h0] at e0; rw [h1] at e1
  exact ⟨e0, e1⟩

end Proj

-- krust's text of `projapp.k`, whose rule applies `project:Int`: it holds `project:Int`'s
-- selector-domain axiom (`\implies{R}(
-- \top{R}(), \equals{R,R}(\ceil{SortInt{},R}(Lblproject'Coln'Int{}(SelectorInput:SortK{})),
-- \exists{R}(VarK:SortInt{}, \equals{SortK{},R}(SelectorInput:SortK{}, kseq{}(inj{SortInt{},
-- SortKItem{}}(VarK:SortInt{}), dotk{}())))))`) and its selector-inverse lemma.
namespace ProjK

definition_of defn from "f2-examples/projapp.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

def projInt : Sym := 387

theorem projInt_named : c.symName projInt = "Lblproject'Coln'Int" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

theorem fn_label : fn.label = projInt := by decide +kernel

/-- The equation's clause and the clause read from the selector-domain axiom. -/
def eqnCl : Clause := ⟨[Srt.int], [.app kseq [.inj Srt.int Srt.kitem (.var 0), .app dotk []]], none, .var 0, none, 50, false, [], .top, .top⟩
def domCl : Clause := ⟨[Srt.k], [.var 0], none, .app projInt [.var 0], some (.dv Srt.bool (.bool false)), 200, false, [], .top, .top⟩

theorem fn_clauses : fn.clauses = [eqnCl, domCl] := rfl

private theorem hfn : c.lookupFn projInt = some fn := rfl
theorem coreOK : c.coreOK = true := by decide +kernel

kernel_rfl isCtor_withHooks : ∀ (c : Semantics) (H : HookParams), (c.withHooks H).isCtor = c.isCtor

theorem kseq_ctor : c.isCtor kseq = true := by decide +kernel
theorem dotk_ctor : c.isCtor dotk = true := by decide +kernel

/-- A value the equation's pattern matches is an injected Int in `kseq(…, dotk)`. -/
theorem eqn_match {H : HookParams} {σ : Subst} {K : GroundTerm}
    (h : PatVals (c.withHooks H) σ [.app kseq [.inj Srt.int Srt.kitem (.var 0), .app dotk []]] [K]) :
    ∃ w, σ.lookup 0 = some w ∧ K = .ctor kseq [injNormal Srt.int Srt.kitem w, .ctor dotk []] := by
  have hk := kseq_ctor; have hd := dotk_ctor
  rw [← isCtor_withHooks c H] at hk hd
  cases h with
  | cons h _ =>
    cases h with
    | ctor _ hs =>
      cases hs with
      | cons h1 hs =>
        cases hs with
        | cons h2 hs =>
          cases hs
          cases h1 with
          | inj h1 =>
            cases h1 with
            | var hw =>
              cases h2 with
              | ctor _ hn => cases hn; exact ⟨_, hw, rfl⟩
              | hook hp => exact absurd hp (by decide)
              | coll hc => rw [hd] at hc; cases hc
              | ovl hc => rw [hd] at hc; cases hc
    | hook hp => exact absurd hp (by decide)
    | coll hc => rw [hk] at hc; cases hc
    | ovl hc => rw [hk] at hc; cases hc

/-- **G3 on krust's text**: for every H, `project:Int(K)` has no value at every K of sort K that is
not an injected Int in `kseq(…, dotk)`: the equation fails there, and the clause read from the
selector-domain axiom decides with its `ensures` false. -/
theorem projInt_none_off (H : HookParams) (K : GroundTerm) (hK : c.sortOf K = some Srt.k)
    (hoff : ∀ v, K ≠ .ctor kseq [injNormal Srt.int Srt.kitem v, .ctor dotk []]) :
    Eval (c.withHooks H) projInt [K] none := by
  have hfnH : (c.withHooks H).lookupFn projInt = some fn := by rw [Semantics.lookupFn_withHooks]; exact hfn
  refine Eval.ensFails (cl := domCl) (σ := [(0, K)]) hfnH (by rw [fn_clauses]; simp) ?_ ?_
    (fun t ht => nomatch ht) ?_ rfl .dv (by decide)
  · intro i s hs
    cases i with
    | zero => cases hs; exact ⟨K, rfl, by rw [Semantics.sortOf_withHooks _ _ noRaw]; exact hK⟩
    | succ i => simp [domCl] at hs
  · exact .cons (.var rfl) .nil
  · intro cl' hcl' _ hlt
    rw [fn_clauses] at hcl'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl'
    rcases hcl' with rfl | rfl
    · exact .intro fun σ _ hpv => by
        obtain ⟨w, -, rfl⟩ := eqn_match hpv
        exact absurd rfl (hoff w)
    · exact absurd hlt (by decide)

/-- `.K` is no injected Int. -/
theorem dotk_off : ∀ v, GroundTerm.ctor dotk [] ≠ .ctor kseq [injNormal Srt.int Srt.kitem v, .ctor dotk []] :=
  fun v h => by cases h

/-- **G3 in `Γ`**: for every H, `Γ` entails `project:Int(K) = ⊥` at every such K. -/
theorem projInt_off_gamma (H : HookParams) (K : GroundTerm) (hK : c.sortOf K = some Srt.k)
    (hoff : ∀ v, K ≠ .ctor kseq [injNormal Srt.int Srt.kitem v, .ctor dotk []]) :
    Γ (c.withHooks H) ⊧
      (KoreAML.den (symApp (c.withHooks H) projInt (GroundTerm.koreList (c.withHooks H) [K])) ≡ ⊥) :=
  gamma_bot_everyH coreOK noRaw (by decide +kernel) hfn (by
    have ha : fn.args = [Srt.k] := by decide +kernel
    rw [ha]; exact OvlLaws.sortsOf_cons_iff.mpr ⟨hK, sortsOf_nil⟩) H (projInt_none_off H K hK hoff)

/-- **G4 on krust's text**: for every H, where `project:Int(K)` has a value v, K is
`kseq(inj{Int,KItem}(v), dotk)`, the selector-inverse lemma's statement at `Eval`'s values. -/
theorem inverse_holds (H : HookParams) (K v : GroundTerm) (hK : c.sortOf K = some Srt.k)
    (hE : Eval (c.withHooks H) projInt [K] (some v)) :
    K = .ctor kseq [injNormal Srt.int Srt.kitem v, .ctor dotk []] := by
  have hfnH : (c.withHooks H).lookupFn projInt = some fn := by rw [Semantics.lookupFn_withHooks]; exact hfn
  generalize hr : (some v : Option GroundTerm) = r at hE
  cases hE with
  | clause hf hmem _ hmatch _ _ hrhs hens =>
    rw [hfnH] at hf; cases hf
    rw [fn_clauses] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · obtain ⟨w, hw, rfl⟩ := eqn_match hmatch
      change EvalTerm _ _ (.var 0) _ at hrhs
      cases hrhs
      rw [hw] at hr; cases hr; rfl
    · have := hens _ rfl
      cases this
  | rest hf hnone =>
    rw [hfnH] at hf; cases hf
    cases hnone domCl (by rw [fn_clauses]; simp) with
    | intro h =>
      cases h [(0, K)] (fun i _ s hs => by
          cases i with
          | zero => cases hs; exact ⟨K, rfl, by rw [Semantics.sortOf_withHooks _ _ noRaw]; exact hK⟩
          | succ i => simp [domCl] at hs)
        (.cons (.var rfl) .nil) with
      | intro ht => cases ht
  | ensFails => cases hr

end ProjK

/-! ## G5: a function declared total, under `RestTotal` -/

/-- **G5**: under an interpretation that gives every function declared total a value where its
clauses give none (`RestTotal`), a function declared total is total wherever, at each argument list
of its sorts, every clause fails or it has a value. -/
theorem total_of_restTotal {c : Semantics} {H : HookParams} (h : RestTotal c H) {fn : Fn} (hfn : fn ∈ c.fns)
    (ht : fn.total = true) (hlook : c.lookupFn fn.label = some fn)
    (hcl : ∀ vs, c.sortsOf vs = some fn.args → (∀ cl ∈ fn.clauses, Fails (c.withHooks H) vs cl) ∨
      ∃ v, Eval (c.withHooks H) fn.label vs (some v)) (hr : ∀ k ∈ c.params, k.raw = false) :
    Total (c.withHooks H) fn.label := by
  intro fn' hlook' vs hvs
  rw [Semantics.lookupFn_withHooks, hlook] at hlook'
  cases hlook'
  rw [Semantics.sortsOf_withHooks c H hr] at hvs
  rcases hcl vs hvs with hnone | hv
  · exact eval_rest_of_restTotal h hfn ht hlook hvs hnone hr
  · exact hv

/-! ## G6: a parameter symbol and a function with no clause -/

/-- **G6**: a function with no clause and a parameter symbol of its signature with no registry
hook, no open generator, have one value at every argument list of its sorts, under every
interpretation: both are the interpretation's, kept where it has the result sort. (An open
generator's value where the interpretation gives none is its raw application, `paramVal`.) -/
theorem fnRest_nil_eq_paramVal (c : Semantics) (fn : Fn) (k : ParamSig) (hn : k.sig.name = fn.label)
    (ha : k.sig.args = fn.args) (hr : k.sig.result = fn.result) (hi : k.impl = none) (hraw : k.raw = false)
    (hk : c.lookupParam fn.label = some k) (vs : List GroundTerm) (hvs : c.sortsOf vs = some fn.args) :
    c.fnRest fn vs = c.paramVal fn.label vs := by
  unfold Semantics.fnRest Semantics.paramVal
  rw [hk]
  simp only [hi, hraw, Bool.false_eq_true, ↓reduceIte]
  cases hH : c.hooks.app fn.label vs with
  | none => rfl
  | some v => simp [Option.filter, hvs, hr, hn]

/-! ## G7: `_Set_` at a common member -/

/-- **G7**: `_Set_` applied to two sets with a member in common is no silent point, and `hook` gives
it no value there, so `Γ` states ⊥ at it under every interpretation (`silentKey_fixed`). -/
theorem setIdem_bot :
    silent setConcat [.set Srt.set [int 1], .set Srt.set [int 1]] = false ∧
    hook setConcat [.set Srt.set [int 1], .set Srt.set [int 1]] = some none := by decide +kernel

/-! ## G8: `ruleRightDefined`, the text's rule axiom entails the read one -/

section RightDefined


theorem eraseDups_drop {α : Type} [DecidableEq α] {A X Y : List α} (hX : ∀ x ∈ X, x ∈ A) :
    (A ++ X ++ Y ++ Y).eraseDups = (A ++ Y).eraseDups := by
  have hsub : ∀ y ∈ Y, y ∈ A ++ X ++ Y := fun y hy => List.mem_append_right _ hy
  rw [List.eraseDups_append (as := A ++ X ++ Y), List.eraseDups_append (as := A ++ X),
    List.eraseDups_append (as := A)]
  rw [List.eraseDups_append (as := A)]
  have h1 : Y.removeAll (A ++ X ++ Y) = [] := by
    simp only [List.removeAll, List.filter_eq_nil_iff]
    intro y hy
    have h := hsub y hy
    simp only [List.mem_append] at h
    rcases h with (h | h) | h <;> simp [h]
  have h2 : X.removeAll A = [] := by
    simp only [List.removeAll, List.filter_eq_nil_iff]
    intro x hx
    simp [hX x hx]
  have h3 : Y.removeAll (A ++ X) = Y.removeAll A := by
    simp only [List.removeAll]
    refine List.filter_congr fun y _ => ?_
    by_cases hy : y ∈ A
    · simp [hy]
    · by_cases hy' : y ∈ X
      · exact absurd (hX y hy') hy
      · simp [hy, hy']
  rw [h1, h2, h3]
  simp

theorem varsOfList_append : ∀ (ps qs : List Kore.Pattern),
    KoreAML.varsOfList (ps ++ qs) = KoreAML.varsOfList ps ++ KoreAML.varsOfList qs
  | [], qs => by simp [KoreAML.varsOfList]
  | p :: ps, qs => by
    simp only [List.cons_append, KoreAML.varsOfList, varsOfList_append ps qs, List.append_assoc]

theorem freeOfList_append (b : List KoreAML.VarKey) : ∀ (ps qs : List Kore.Pattern),
    KoreAML.freeOfList b (ps ++ qs) = KoreAML.freeOfList b ps ++ KoreAML.freeOfList b qs
  | [], qs => by simp [KoreAML.freeOfList]
  | p :: ps, qs => by
    simp only [List.cons_append, KoreAML.freeOfList, freeOfList_append b ps qs, List.append_assoc]

/-- The premise `⌈R⌉` appended to a rewrite's left side changes neither the variable table nor the
guarded variables: its variables are the right side's, met later anyway. -/
theorem table_ceil (C : Kore.KSort) (ps : List Kore.Pattern) (R : Kore.Pattern) :
    KoreAML.tableOf [] (.rewrites C (.and C (ps ++ [.ceil C C R])) R) = KoreAML.tableOf [] (.rewrites C (.and C ps) R) := by
  simp only [KoreAML.tableOf, List.map_nil, List.nil_append, KoreAML.varsOf, varsOfList_append,
    KoreAML.varsOfList, List.append_nil]
  have := eraseDups_drop (A := KoreAML.sortVarsOf C ++ (KoreAML.sortVarsOf C ++ KoreAML.varsOfList ps))
    (X := KoreAML.sortVarsOf C ++ KoreAML.sortVarsOf C) (Y := KoreAML.varsOf R)
    (fun x hx => by simp only [List.mem_append] at hx ⊢; rcases hx with h | h <;> exact .inl h)
  simpa only [List.append_assoc] using this

theorem free_ceil (C : Kore.KSort) (ps : List Kore.Pattern) (R : Kore.Pattern) :
    (([] : List Kore.SortVar).map KoreAML.sortVarKey ++ KoreAML.freeOf [] (.rewrites C (.and C (ps ++ [.ceil C C R])) R)).eraseDups =
    (([] : List Kore.SortVar).map KoreAML.sortVarKey ++ KoreAML.freeOf [] (.rewrites C (.and C ps) R)).eraseDups := by
  simp only [List.map_nil, List.nil_append, KoreAML.freeOf, freeOfList_append, KoreAML.freeOfList, List.append_nil]
  have := eraseDups_drop (A := KoreAML.freeOfList [] ps) (X := []) (Y := KoreAML.freeOf [] R) (fun x hx => by cases hx)
  simpa only [List.append_nil, List.append_assoc] using this

/-- For a rule with no existential variables (`r.exs = []`) and whose predicates `pre` and `post` are
`\top`, in every semantics: `prioRuleK` is `UndefRhsWitness.textRuleK` with `⌈rhs ∧ ens⌉` appended to its
left side, whose conjuncts are the left side and the `requires`, and the competitors' negation where
there are competitors. -/
theorem prio_eq_text (c : Semantics) (r : Rule) (hex : r.exs = []) (hpre : r.pre = .top)
    (hpost : r.post = .top) : ∃ (C : Kore.KSort) (l q R : Kore.Pattern) (ps : List Kore.Pattern),
    (ps = [l, q] ∨ ∃ n, ps = [l, q, n]) ∧
    UndefRhsWitness.textRuleK c r = .rewrites C (.and C ps) R ∧ prioRuleK c r = .rewrites C (.and C (ps ++ [.ceil C C R])) R := by
  rw [prioRuleK_top hex hpre hpost]
  unfold UndefRhsWitness.textRuleK
  dsimp only
  by_cases hc : ((c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')).isEmpty = true
  · rw [if_pos hc, if_pos hc]; exact ⟨_, _, _, _, _, .inl rfl, rfl, rfl⟩
  · rw [if_neg hc, if_neg hc]; exact ⟨_, _, _, _, _, .inr ⟨_, rfl⟩, rfl, rfl⟩

/-- **G8** (`ReadingNote.ruleRightDefined`): for every semantics and every rule with no existential
variables (`r.exs = []`) and whose predicates `pre` and `post` are `\top`, so under every interpretation of
the points the text leaves open, the rule's axiom as the text writes it (`UndefRhsWitness.textRuleK`: no premise
`⌈rhs ∧ ens⌉`), with the definedness axioms, entails the axiom `Γ` reads (`prioRuleK`). The
competitors' negation, the priority reading, is in both. -/
theorem ruleRightDefined_weaker (c : Semantics) (r : Rule) (hex : r.exs = []) (hpre : r.pre = .top)
    (hpost : r.post = .top) :
    (fun φ => φ = (UndefRhsWitness.textRuleItem c r).pat ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ⊧
      (KoreAML.trAxiom [] [] ⟨0, "kernel", { sortVars := [], pattern := prioRuleK c r, attributes := [] }⟩).pat := by
  intro M _ I hI
  have hD : KoreAML.DefOK I := KoreAML.defOK_of fun x => hI _ (.inr ⟨x, rfl⟩)
  have h := hI _ (.inl rfl)
  obtain ⟨C, l, q, R, ps, hps, ht, hp⟩ := prio_eq_text c r hex hpre hpost
  intro e m
  have h1 := h e m
  unfold UndefRhsWitness.textRuleItem KoreAML.trAxiom at h1
  unfold KoreAML.trAxiom
  dsimp only at h1 ⊢
  rw [ht] at h1
  rw [hp, table_ceil, free_ceil]
  have hs : ∀ L, KoreAML.sortOf [] (.rewrites C L R) = some C := fun _ => rfl
  simp only [hs] at h1 ⊢
  rw [interpret_impl] at h1 ⊢
  intro hg
  have h2 := h1 hg
  rw [KoreAML.interp_equal hD] at h2 ⊢
  intro a
  have h3 := h2 a
  generalize KoreAML.tableOf [] (.rewrites C (.and C ps) R) = tb at h3 ⊢
  rw [KoreAML.tr] at h3 ⊢
  unfold KoreAML.sRewrites at h3 ⊢
  rw [KoreAML.interp_sImp] at h3 ⊢
  refine ⟨fun h' => h'.1, fun ha => ⟨ha, fun hL => (h3.mpr ha).2 ?_⟩⟩
  rcases hps with rfl | ⟨n, rfl⟩
  · simp only [List.cons_append, List.nil_append] at hL
    rw [tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd] at hL
    rw [tr_and2, KoreAML.interp_sAnd]
    exact ⟨hL.1, hL.2.1⟩
  · simp only [List.cons_append, List.nil_append] at hL
    rw [tr_and4, KoreAML.interp_sAnd, KoreAML.interp_sAnd, KoreAML.interp_sAnd] at hL
    rw [tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd]
    exact ⟨hL.1, hL.2.1, hL.2.2.1⟩

end RightDefined

end KCore.Guards

#print axioms KCore.Guards.g0_refuted
#print axioms KCore.Guards.eval_noValue_of_ens_fails
#print axioms KCore.Guards.Ens.half_neg4_gamma
#print axioms KCore.Guards.EnsOwise.half_neg4_gamma
#print axioms KCore.Guards.Proj.projInt_dotk_open
#print axioms KCore.Guards.ProjK.projInt_none_off
#print axioms KCore.Guards.ProjK.projInt_off_gamma
#print axioms KCore.Guards.ProjK.inverse_holds
#print axioms KCore.Guards.total_of_restTotal
#print axioms KCore.Guards.fnRest_nil_eq_paramVal
#print axioms KCore.Guards.setIdem_bot
#print axioms KCore.Guards.ruleRightDefined_weaker
