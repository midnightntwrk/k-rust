/-
  The tie (C14) of the fixture c3-eq-ens-total-holds (the pair equation `ensures` x `[total]`, the case in which the
  owed totality holds):
  `syntax Int ::= f(Int) [function, total]`, `rule f(X) => X ensures X ==Int X`.
  The text is `f2-examples/c3-eq-ens-total-holds.kompile.kore`: the kompiled text that
  `test/constructs/fixtures/c3-eq-ens-total-holds/kompile.txt` records (sha256 adadf6d7…), with its paths restored.
  Run from the package root: `lake env lean -j1 test/C3EqEnsTotalHolds.lean`. Every statement is on the literal
  `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  Layer 1. `wf_defn`, `coreOK` (kernel); `defs_attrsAgree`: the attributes of the text agree with
  `defn`; `account`: the function equations and the constructor sentences are sentences of the user
  module, apart, with the count of the rest.

  Layer 2.
  - Function equations (`fnText`: `f`'s and the sort predicates'): each of Γ's items is the
    translation of its sentence (`shape`), so Γ entails each sentence (`fns_entailed`) and each item
    is a consequence of its sentence (`fns_from_text`).
  - Constructor sentences (`consText`): entailed by Γ (`cons_entailed`).
  - The `functional` sentence of `f`: in no part of Γ; read into `Fn.total`, the owed fact
    `Total f`, proved here (`total_f`).

  For every H: `eval_all` (`f(n) = n` at every integer n: the `ensures` `n ==Int n` is true by the
  hook's value), `total_f` (`Total f`), `obl` (the facts the deciders leave hold; `total_named = [f]`),
  `consistent`, and `model_total`: the value model satisfies Γ, the step's closure and the
  functional axiom of `f` (`has_model_total`). Expectations (C7 form (a), from sentences): `f_5`,
  `f_neg1` (`f(-1) = -1`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.C3EqEnsTotalHolds

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/c3-eq-ens-total-holds.kompile.kore"
definition_of defn from "f2-examples/c3-eq-ens-total-holds.kompile.kore"
user_axioms U from "f2-examples/c3-eq-ens-total-holds.kompile.kore" module "C3-EQ-ENS-TOTAL-HOLDS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "C3-EQ-ENS-TOTAL-HOLDS")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

theorem wf_defn : wf defn = true := by decide_cheap
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The attributes of the text agree with `defn` (`attrsAgree`): constructors, functions, hooks,
collection symbols, priorities. -/
theorem defs_attrsAgree : attrsAgree kore defn = true := by decide +kernel

/-! ## The function equations -/

/-- The text sentences of Γ's equations, in `fnItems`'s order: found by head symbol and priority
(`TiePair.fnTextOf`); `shape` is what makes them the equations' sentences. -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

/-- Their axiom indices (`AxiomDecl.index`):  -/
theorem fnText_index : fnText.map (·.index) = [201, 219, 227, 226, 225, 224, 231, 230, 233, 232, 229, 228, 208, 207, 218, 217, 214, 213, 216, 215, 221, 220, 223, 222, 210, 209, 212, 211] := by decide +kernel

/-- The translations of the text's sentences, in that order. -/
noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence**, pattern for pattern or with
one variable renamed (`TiePair.sameB`; kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- **E for the function equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat :=
  fun ad had => TiePair.entailed (shapeH H) _ (List.mem_map_of_mem had)

/-- **The converse for `fnItems`**: each item is a consequence of a text sentence, the j-th of
`fnText[j]`. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj
  obtain ⟨t, ht, hent⟩ := TiePair.from_text (shapeH H) j it hj
  unfold textPats at ht
  rw [List.getElem?_map] at ht
  cases hf : fnText[j]? with
  | none => rw [hf] at ht; cases ht
  | some ad => rw [hf] at ht; cases ht; exact ⟨ad, rfl, hent⟩

/-! ## The constructor sentences -/

/-- The user module's sentences that are constructor sentences Γ's constructor items entail
(`tieConsB`): `functional` of a constructor, `subsort`, no confusion. -/
noncomputable def consText : List AxiomDecl := U.all.filter fun ad => tieConsB c ad.ax

/-- None of them reads a declaration or an alias: its translation with the text's declarations
is its translation with none. -/
theorem cons_trS : consText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **E for the constructor sentences**: Γ entails each, for every H. -/
theorem cons_entailed (H : HookParams) : ∀ ad ∈ consText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  rw [of_decide_eq_true (List.all_eq_true.mp cons_trS ad had)]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact tieCons_entailed (c := cH H) (a := ad.ax)
    ((tieConsB_withHooks c H ad.ax).trans (List.mem_filter.mp had).2) ad.index ad.module hI

/-! ## The account -/

/-- The indices of the sentences tied here: the function equations and the constructor
sentences. -/
noncomputable def tiedIdx : List Nat := fnText.map (·.index) ++ consText.map (·.index)

/-- **The account**: the function equations and the constructor sentences are sentences of the
user module, each once and none in both classes; the sizes of the two classes and of the rest
(library sentences, hooked symbols' `functional` sentences, collection laws, no junk, the
projections and initializers: not tied here). -/
theorem account : tiedIdx.Nodup ∧ tiedIdx.all (fun i => (U.all.map (·.index)).contains i) = true ∧
    (U.all.map (·.index)).Nodup ∧
    (fnText.length, consText.length, U.all.length - tiedIdx.length) = (28, 24, 200) := by decide +kernel

/-! ## The facts the deciders leave -/

def f : Sym := 384

theorem names : c.symName f = "Lblf" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

theorem hfn : c.lookupFn f = some fn := rfl
theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok
theorem hfnH (H : HookParams) : (cH H).lookupFn f = some fn := by rw [Semantics.lookupFn_withHooks]; exact hfn
theorem hvsH (H : HookParams) (n : Int) : (cH H).sortsOf [int n] = some fn.args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; rfl

/-- What `Cert.evalFC` computes for `f` is `Eval`'s under every H. -/
theorem eval_of {n : Int} {k : Nat} {r : Option GroundTerm} (h : Cert.evalFC c k f [int n] = some r)
    (H : HookParams) : Eval (cH H) f [int n] r :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfn rfl h

def callOrder : List Nat := [384]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel
/-- The totality decider does not confirm `f` (its equation has an `ensures`): its totality is the
named fact, proved below. -/
theorem total_named : c.totalObligationsRP callOrder [] = [f] := by decide +kernel

theorem plainH (H : HookParams) : (cH H).plain = true :=
  (Semantics.plain_withHooks c H).trans (by decide +kernel)

/-- `f`'s one clause: `f(X) => X ensures X ==Int X`. -/
noncomputable abbrev cl0 : Clause := fn.clauses[0]'(by decide +kernel)

theorem cl0_vars : cl0.vars = [Srt.int] := by decide +kernel
theorem cl0_pats : cl0.pats = [.var 0] := rfl
theorem cl0_req : cl0.req = none := rfl
theorem cl0_rhs : cl0.rhs = .var 0 := rfl
theorem cl0_pre : cl0.pre = .top := rfl
theorem cl0_ens : cl0.ens = some (.app intEq [.var 0, .var 0]) := rfl
theorem cl0_least : fn.clauses.all (fun cl' => !decide (cl'.prio < cl0.prio)) = true := by decide +kernel

theorem int2_at (x y : Int) (g : Int → Int → Option GroundTerm) : int2 [int x, int y] g = g x y := by
  simp [int2, asInt, int]

/-- **`f(n) = n` at every integer n, for every H**: the clause matches, and its `ensures`
`n ==Int n` evaluates to `true` by the hook's value. -/
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
  refine .clause (cl := cl0) (σ := [(0, int n)]) (hfnH H) (List.getElem_mem _) hσ hm
    (fun t ht => by rw [cl0_req] at ht; cases ht) (by rw [cl0_pre]; exact .top)
    (fun cl' hcl' _ hlt => absurd hlt (by simpa using List.all_eq_true.mp cl0_least cl' hcl')) (by rfl) hr
    (fun t ht => ?_) (Clause.holds_postTop (by rfl) _)
  rw [cl0_ens] at ht
  cases ht
  refine .hook (rs := [some (int n), some (int n)]) (show (cH H).isCtor intEq = false from (by decide +kernel : c.isCtor intEq = false)) rfl
    (.cons .var (.cons .var .nil))
    (fun vs hvs => ?_) (fun h => by cases h)
  cases hvs
  exact Semantics.hookRes_of_value (by rw [Det.hook_intEq, int2_at]; simp [KCore.bool])

theorem fn_args : fn.args = [Srt.int] := by decide +kernel
theorem shapesOK_c : c.shapesOK = true := by decide +kernel

/-- **`f` is `Total`, for every H.** -/
theorem total_f (H : HookParams) : Total (cH H) f := fun fn' hfn' vs hvs => by
  have he : fn' = fn := Option.some.inj (hfn'.symm.trans (hfnH H))
  subst he
  rw [fn_args, Semantics.sortsOf_withHooks _ _ noRaw] at hvs
  obtain ⟨w, ws', rfl, hw, hws⟩ := sortsOf_inv_cons hvs
  cases sortsOf_inv_nil hws
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c hw
  exact ⟨int n, eval_all H n⟩

/-- **The facts the deciders leave hold, for every H**: the one named is the totality of `f`. -/
theorem obl (H : HookParams) : FnObligations (cH H) callOrder [] :=
  ⟨fun g hg => by
      rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks, term_named] at hg
      exact absurd hg List.not_mem_nil,
   fun g hg => by
      rw [Semantics.totalObligationsRP_withHooks, total_named] at hg
      rw [List.mem_singleton.mp hg]; exact total_f H,
   fun g hg => by
      rw [Det.Semantics.agreeObligationsI_withHooks, agree_named] at hg; exact absurd hg List.not_mem_nil,
   fun p hp => by
      rw [Det.Semantics.matchObligationsL_withHooks, match_named] at hp; exact absurd hp List.not_mem_nil,
   openDecided_of_plain (fun r hr => needsWitness_of_binds ((Semantics.plain_parts (plainH H)).1 r hr))
     (fun fn hfn cl hcl => Clause.needsWitness_of_binds ((Semantics.plain_parts (plainH H)).2.1 fn hfn cl hcl)),
   openLaws_of_plain (Semantics.plain_parts (plainH H)).2.2⟩

theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl H)

/-- **Γ with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-- **The theory with the functional axiom of `f` has a model, for every H** (`has_model_total`):
the value model satisfies Γ, the step's closure and `∃y. f(x) = y`. -/
theorem model_total (H : HookParams) :
    Model.stdI (cH H) ⊧ᴵP (Γ (cH H) ∪ Γstep (cH H) ∪ Model.ΓTotal (cH H)) :=
  has_model_total (coreOKH H) (fnHypH H)

/-! ## The expectations (C7 form (a)) -/

/-- The premises of the derivations: the function sentences as written, Γ's rule items (none: the text has no rule), and the
families (the parts of Γ no sentence states, here the hooks' graphs and the values). -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- **`Pre` with the step's closure has a model, for every H.** -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) :=
  TiePair.pre_model (shapeH H) (consistent H)

/-- `⟦f(n)⟧`. -/
noncomputable abbrev fAt (H : HookParams) (n : Int) : P := TiePair.app (cH H) f [int n]


/-- **`f(5) = 5`, derived from `Pre`**, for every H: from `f`'s sentence as written, whose `ensures`
`5 ==Int 5` is `true` by the graph of `==Int`. -/
theorem f_5 (H : HookParams) : Pre H ⊧ (fAt H (5) ≡ den (cH H) (int (5))) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H) (eval_of (k := 10) (by decide +kernel) H) (hfnH H) (hvsH H (5))


/-- **`f(-1) = -1`, derived from `Pre`**, for every H: the `ensures` is true at every argument. -/
theorem f_neg1 (H : HookParams) : Pre H ⊧ (fAt H (-1) ≡ den (cH H) (int (-1))) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H) (eval_of (k := 10) (by decide +kernel) H) (hfnH H) (hvsH H (-1))


end KCore.C3EqEnsTotalHolds

#print axioms KCore.C3EqEnsTotalHolds.wf_defn
#print axioms KCore.C3EqEnsTotalHolds.defs_attrsAgree
#print axioms KCore.C3EqEnsTotalHolds.shape
#print axioms KCore.C3EqEnsTotalHolds.fns_entailed
#print axioms KCore.C3EqEnsTotalHolds.fns_from_text
#print axioms KCore.C3EqEnsTotalHolds.cons_entailed
#print axioms KCore.C3EqEnsTotalHolds.account
#print axioms KCore.C3EqEnsTotalHolds.consistent
#print axioms KCore.C3EqEnsTotalHolds.pre_model
#print axioms KCore.C3EqEnsTotalHolds.eval_all
#print axioms KCore.C3EqEnsTotalHolds.total_f
#print axioms KCore.C3EqEnsTotalHolds.obl
#print axioms KCore.C3EqEnsTotalHolds.model_total
#print axioms KCore.C3EqEnsTotalHolds.f_5
#print axioms KCore.C3EqEnsTotalHolds.f_neg1
