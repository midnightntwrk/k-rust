/-
  The tie (C14) of the fixture c3-eq-ens-prio-comp (the pair equation `ensures` x equation `priority`, with a
  competitor):
  `rule f(X) => X ensures X >=Int 0 [priority(40)]` beside `rule f(_) => 0` of the default
  priority: the two equations' own premises hold at every argument.
  The text is `f2-examples/c3-eq-ens-prio-comp.kompile.kore`: the kompiled text that
  `test/constructs/fixtures/c3-eq-ens-prio-comp/kompile.txt` records (sha256 5e5bf8bb…), with its paths restored.
  Run from the package root: `lake env lean -j1 test/C3EqEnsPrioComp.lean`. Every statement is on the literal
  `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  Layer 1. `wf_defn`, `coreOK` (kernel); `defs_attrsAgree`: the attributes of the text agree with
  `defn`; `account`: the function equations and the constructor sentences are sentences of the user
  module, apart, with the count of the rest.

  Layer 2.
  - Function equations (`fnText`): the equation of priority 40 and the sort predicates' are Γ's
    items, pattern for pattern (`shape`, `fns_entailed`). The equation without the attribute is in Γ
    under the negation of the clause of priority 40 (`prioEquation`): its sentence entails Γ's item
    (`w1`, W1) and is the item without that premise (`w_text`); it is not the item (`w_differs`).
    `fns_from_text`: each item is a consequence of its sentence.
  - Constructor sentences (`consText`): entailed by Γ (`cons_entailed`).
  - `consistent`: Γ with the step's closure has a model, for every H.

  The expectations (C7 form (a), through the reading, family the priority premise `prioEquation`;
  every point is one where both equations' own premises hold): `f_5`, `f(5) = 5`; `f_neg1`, `f(-1)`
  has no value (the equation of priority 40 applies and its `ensures` is not true, by the graph of
  `>=Int`; the other clause is under the premise, which negates the first clause's match and not
  its `ensures`). Both from `Pre H`: every equation of `f`, the one of priority 40 as written, the
  other as Γ's item; `Pre H` has a model (`pre_model`).
  The expectations check that the reader and the cone implement the manual's order (the equation
  of the smaller number first); they are not derived from the sentences as written, which with
  value distinctness have no model on this text (they give `f(5) = 5` and `f(5) = 0`): not proved
  here, a limit.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.C3EqEnsPrioComp

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/c3-eq-ens-prio-comp.kompile.kore"
definition_of defn from "f2-examples/c3-eq-ens-prio-comp.kompile.kore"
user_axioms U from "f2-examples/c3-eq-ens-prio-comp.kompile.kore" module "C3-EQ-ENS-PRIO-COMP"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "C3-EQ-ENS-PRIO-COMP")

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
theorem fnText_index : fnText.map (·.index) = [200, 201, 219, 227, 226, 225, 224, 231, 230, 233, 232, 229, 228, 208, 207, 218, 217, 214, 213, 216, 215, 221, 220, 223, 222, 210, 209, 212, 211] := by decide +kernel

/-! ### The equation read under the priority premise (W1)

`fnItems`'s item 1 is the equation of the clause of the larger priority: Γ holds it under the
negation of the clause of the smaller priority (`prioEquation`, `competingEquation`), a premise no
sentence of the text states. The text's sentence 201 entails it, and is the item without that
premise. -/

/-- Γ's axiom of the narrowed equation. -/
noncomputable def aW : Kore.Axiom := ((TiePair.fnAxioms c)[1]?).getD ⟨[], .top KoreAML.R, []⟩

theorem aW_at : (TiePair.fnAxioms c)[1]? = some aW := by decide +kernel

/-- Γ's item of it. -/
noncomputable def gW : P := (trAxiom [] [] ⟨0, "kernel", aW⟩).pat

theorem gW_at : (TiePair.gammaPats c)[1]? = some gW := TiePair.gammaPats_at aW_at

kernel_rfl fnText_W : fnText[1]? = some U.ax201

/-- Its premise has the negated conjunct. -/
theorem aW_narrowed : (TiePair.negParts aW.pattern).isSome = true := by decide +kernel

/-- **Γ's item without the priority premise is the text's sentence 201** (`TiePair.minusNeg`, up to
the indices of its variables: `TiePair.sameB`; kernel). -/
theorem w_text : TiePair.sameB (TiePair.minusNeg aW) (trS U.ax201).pat = true := by decide +kernel

/-- **Γ's item is not the sentence.** -/
theorem w_differs : gW ≠ (trS U.ax201).pat := by decide +kernel

/-- **W1**: the text's sentence 201 entails Γ's item, in every model of definedness. -/
theorem w1 : TiePair.Texts [(trS U.ax201).pat] ⊧ gW :=
  fun {M} _ {I} hI => TiePair.item_of_sentence (TiePair.defOK_texts hI) w_text
    (hI _ (Or.inl (List.mem_singleton_self _)))

/-- The premise set's equations, in `fnItems`'s order: each text sentence's translation, and for
sentence 201 Γ's item (C7 (ii)). -/
noncomputable def textPats : List P := (fnText.map (trS · |>.pat)).set 1 gW

/-- **Each of Γ's equations but item 1 is the translation of its text sentence** (kernel); item
1 is `gW`. -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- **E for the function equations other than sentence 201**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad → j ≠ 1 →
    Γ (cH H) ⊧ (trS ad).pat := by
  intro j ad hj hne
  refine TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (i := j) ?_)
  unfold textPats
  rw [List.getElem?_set_ne (Ne.symm hne), List.getElem?_map, hj]; rfl

/-- **The converse for `fnItems`**: each item is a consequence of a text sentence, the j-th of
`fnText[j]`; item 1 by W1, the others by their translation. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj
  by_cases hJ : j = 1
  · subst hJ
    refine ⟨U.ax201, fnText_W, ?_⟩
    have hg : (TiePair.gammaPats (cH H))[1]? = some it.pat := by
      unfold TiePair.gammaPats; rw [List.getElem?_map, hj]; rfl
    rw [TiePair.gammaPats_withHooks, gW_at] at hg
    rw [← Option.some.inj hg]
    intro M _ I hI
    exact w1 hI
  · obtain ⟨t, ht, hent⟩ := TiePair.from_text (shapeH H) j it hj
    unfold textPats at ht
    rw [List.getElem?_set_ne (Ne.symm hJ), List.getElem?_map] at ht
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
    (fnText.length, consText.length, U.all.length - tiedIdx.length) = (29, 24, 199) := by decide +kernel

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
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- **Γ with the step's closure has a model, for every H** (C14 closure (a)). -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)


/-! ## The expectations (C7 form (a)) -/

/-- The premises of the derivations: the function sentences as written but sentence 201, for which Γ's item
(`gW`, with `w1` and `w_text`), Γ's rule items (none: the text has no rule), and the families. -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- **`Pre` with the step's closure has a model, for every H.** -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) :=
  TiePair.pre_model (shapeH H) (consistent H)

/-- `⟦f(n)⟧`. -/
noncomputable abbrev fAt (H : HookParams) (n : Int) : P := TiePair.app (cH H) f [int n]


/-- **`f(5) = 5`, derived from `Pre`**, for every H, through the reading (the priority premise): at 5
both equations' own premises hold; the equation of priority 40 is in `Pre` as written and gives 5,
and the other one is in `Pre` as Γ's item, which is silent where the clause of priority 40 applies. -/
theorem f_5 (H : HookParams) : Pre H ⊧ (fAt H (5) ≡ den (cH H) (int (5))) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H) (eval_of (k := 10) (by decide +kernel) H) (hfnH H) (hvsH H (5))


/-- **`f(-1)` has no value, derived from `Pre`**, for every H, through the reading: the sentence of
priority 40 as written states `f(-1) = -1 ∧ (-1 >=Int 0 = true)`, `-1 >=Int 0` being `false` by the
graph of `>=Int`; the other equation, as Γ's item, is silent there: its premise negates the match
of the clause of priority 40, not its `ensures`. -/
theorem f_neg1 (H : HookParams) : Pre H ⊧ (fAt H (-1) ≡ ⊥) :=
  TiePair.noValue (shapeH H) (coreOKH H) (hokH H) (eval_of (k := 10) (by decide +kernel) H) (hfnH H) (hvsH H (-1))


end KCore.C3EqEnsPrioComp

#print axioms KCore.C3EqEnsPrioComp.wf_defn
#print axioms KCore.C3EqEnsPrioComp.defs_attrsAgree
#print axioms KCore.C3EqEnsPrioComp.shape
#print axioms KCore.C3EqEnsPrioComp.fns_entailed
#print axioms KCore.C3EqEnsPrioComp.fns_from_text
#print axioms KCore.C3EqEnsPrioComp.cons_entailed
#print axioms KCore.C3EqEnsPrioComp.account
#print axioms KCore.C3EqEnsPrioComp.consistent
#print axioms KCore.C3EqEnsPrioComp.pre_model
#print axioms KCore.C3EqEnsPrioComp.w1
#print axioms KCore.C3EqEnsPrioComp.w_text
#print axioms KCore.C3EqEnsPrioComp.f_5
#print axioms KCore.C3EqEnsPrioComp.f_neg1
