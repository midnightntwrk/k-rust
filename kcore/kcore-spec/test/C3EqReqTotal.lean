/-
  The tie (C14) of the fixture c3-eq-req-total (the pair equation `requires` x `[total]`):
  `syntax Int ::= f(Int) [function, total]`, `rule f(X) => X requires X >Int 0`.
  The text is `f2-examples/c3-eq-req-total.kompile.kore`: the kompiled text that
  `test/constructs/fixtures/c3-eq-req-total/kompile.txt` records (sha256 7c39428a…), with its paths restored.
  Run from the package root: `lake env lean -j1 test/C3EqReqTotal.lean`. Every statement is on the literal
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
    `Total f` (`total_named = [f]`). Where the `requires` is not true no equation applies, and the
    value that sentence states there is the interpretation's: whether `Total f` holds depends on H,
    and nothing here takes it.
  - `fnModelH`, `consistent`: `FnDet`, `FnSolves` and a model of Γc with the step's closure, for
    every H, with no totality fact.

  The expectation (C7 form (a), from sentences): `f_5`, `f(5) = 5`, from `Pre H`, which has a model
  (`pre_model`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.C3EqReqTotal

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/c3-eq-req-total.kompile.kore"
definition_of defn from "f2-examples/c3-eq-req-total.kompile.kore"
user_axioms U from "f2-examples/c3-eq-req-total.kompile.kore" module "C3-EQ-REQ-TOTAL"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "C3-EQ-REQ-TOTAL")

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
/-- The totality decider does not confirm `f`: where the `requires` is not true no equation
applies, and `f`'s value there is the interpretation's. Its totality is owed. -/
theorem total_named : c.totalObligationsRP callOrder [] = [f] := by decide +kernel

/-- **One result at each argument list and evaluation solves the equations, for every H**; `f`'s
`[total]` is not read. -/
theorem fnModelH (H : HookParams) : FnDet (cH H) ∧ FnSolves (cH H) :=
  TiePair.fnModel_noTotal_withHooks (hpreTop := by decide +kernel) (hnoEx := Semantics.fnsNoExs_of_all (by decide +kernel)) (ord := callOrder) coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) noRaw
    term_named agree_named match_named H

theorem plainH (H : HookParams) : (cH H).plain = true :=
  (Semantics.plain_withHooks c H).trans (by decide +kernel)

/-- **Γc with the step's closure has a model, for every H** (`consistent_of`); Γ holds no
functional axiom of a function, so the text's `functional` sentence of `f` is not read here. -/
theorem consistent (H : HookParams) : Consistent (cH H) :=
  consistent_of (cH H) (coreOKH H) (fnModelH H).1 (fnModelH H).2
    (clausePreDecided_of_isTop (c := cH H)
      (by decide +kernel : (c.fns.all fun f => f.clauses.all fun cl => cl.pre.isTop) = true))
    (clausePostDecided_of_isTop (c := cH H)
      (by decide +kernel : (c.fns.all fun f => f.clauses.all fun cl => cl.post.isTop) = true))
    (openLaws_of_plain (Semantics.plain_parts (plainH H)).2.2)

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


/-- **`f(5) = 5`, derived from `Pre`**, for every H: from `f`'s sentence as written, whose `requires`
is true at 5 by the graph of `>Int`. -/
theorem f_5 (H : HookParams) : Pre H ⊧ (fAt H (5) ≡ den (cH H) (int (5))) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H) (eval_of (k := 10) (by decide +kernel) H) (hfnH H) (hvsH H (5))


end KCore.C3EqReqTotal

#print axioms KCore.C3EqReqTotal.wf_defn
#print axioms KCore.C3EqReqTotal.defs_attrsAgree
#print axioms KCore.C3EqReqTotal.shape
#print axioms KCore.C3EqReqTotal.fns_entailed
#print axioms KCore.C3EqReqTotal.fns_from_text
#print axioms KCore.C3EqReqTotal.cons_entailed
#print axioms KCore.C3EqReqTotal.account
#print axioms KCore.C3EqReqTotal.consistent
#print axioms KCore.C3EqReqTotal.pre_model
#print axioms KCore.C3EqReqTotal.fnModelH
#print axioms KCore.C3EqReqTotal.f_5
