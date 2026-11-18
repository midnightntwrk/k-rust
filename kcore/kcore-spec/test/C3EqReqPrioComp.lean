/-
  The tie (C14) of the fixture c3-eq-req-prio-comp (the pair equation `requires` x equation `priority`, with a
  competitor):
  `rule f(X) => X requires X >Int 0 [priority(40)]` beside `rule f(_) => 0` of the default
  priority.
  The text is `f2-examples/c3-eq-req-prio-comp.kompile.kore`: the kompiled text that
  `test/constructs/fixtures/c3-eq-req-prio-comp/kompile.txt` records (sha256 5b21e93b…), with its paths restored.
  Run from the package root: `lake env lean -j1 test/C3EqReqPrioComp.lean`. Every statement is on the literal
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

  The expectations (C7 form (a)), from `Pre H`: every equation of `f`, the one of priority 40 as
  written, the other as Γ's item; `Pre H` has a model (`pre_model`).
  - `f_5`, `f(5) = 5`: through the reading, family the priority premise (`prioEquation`): at 5 both
    equations' own premises hold.
  - `f_neg1`, `f(-1) = 0`: from sentences: the `requires` of the equation of priority 40 is not
    true at -1, and the other sentence as written gives 0.
  The expectations at a point where both equations' own premises hold check that the reader and
  the cone implement the manual's order (the equation of the smaller number first); they are not
  derived from the sentences as written, which have no model on this text, for every H: at 5 they
  give `f(5) = 5` (with the graph of `>Int` at (5, 0)) and `f(5) = 0`, and 5 and 0 are distinct
  elements of Int. `no_model_written`: `Pre H` with sentence 201 as written in place of Γ's item has
  no model; `written_refuted`: Γ with sentence 201 has none. The proof goes through Γ, a
  consequence of the premise set (`TiePair.gamma_from`): Γ's value `f(5) = 5`, and from `ΓDomains`
  that the values 5 and 0 each denote one element of Int and denote distinct ones. `clauses_eq`: `f`'s clauses are the literals that
  test/C3EqPrioFlat.lean reads at one priority, where `ClausesAgree` is false.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.C3EqReqPrioComp

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/c3-eq-req-prio-comp.kompile.kore"
definition_of defn from "f2-examples/c3-eq-req-prio-comp.kompile.kore"
user_axioms U from "f2-examples/c3-eq-req-prio-comp.kompile.kore" module "C3-EQ-REQ-PRIO-COMP"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "C3-EQ-REQ-PRIO-COMP")

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
both equations' own premises hold (the `requires` of the first by the graph of `>Int`); the equation
of priority 40 is in `Pre` as written and gives 5, and the other one is in `Pre` as Γ's item, which
is silent where the clause of priority 40 applies. -/
theorem f_5 (H : HookParams) : Pre H ⊧ (fAt H (5) ≡ den (cH H) (int (5))) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H) (eval_of (k := 10) (by decide +kernel) H) (hfnH H) (hvsH H (5))


/-- **`f(-1) = 0`, derived from `Pre`**, for every H, from sentences: the `requires` of the equation
of priority 40 is not true at -1 (the graph of `>Int`), so that equation is silent and the
narrowed sentence, as written, applies: Γ's item for it has its premise true there. -/
theorem f_neg1 (H : HookParams) : Pre H ⊧ (fAt H (-1) ≡ den (cH H) (int (0))) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H) (eval_of (k := 10) (by decide +kernel) H) (hfnH H) (hvsH H (-1))


/-! ## The text side: the sentences as written have no model

At 5 the equation of priority 40 as written gives 5 (its `requires` true by the graph of `>Int` at
(5, 0)) and sentence 201 as written gives 0; 5 and 0 are distinct elements of Int. So the premise
set with sentence 201 as written in place of Γ's item has no model; neither does Γ with it. -/

/-- The clauses of `f`: `f(X) = X requires X >Int 0` of priority 40 and `f(_) = 0` of the default
priority (test/C3EqPrioFlat.lean has the same two at one priority). -/
def clA : Clause := ⟨[Srt.int], [.var 0], some (.app intGt [.var 0, .dv Srt.int (.int 0)]), .var 0, none, 40, false, [], .top, .top⟩
def clB : Clause := ⟨[Srt.int], [.var 0], none, .dv Srt.int (.int 0), none, 50, false, [], .top, .top⟩

kernel_rfl clauses_eq : fn.clauses = [clA, clB]

/-- **Sentence 201's translation is `clB`'s equation with no premise but its own** (`clauseAxiom`,
up to the indices of its variables; kernel). -/
theorem written_clB : TiePair.sameB (trAxiom [] [] ⟨0, "kernel", clauseAxiom c fn clB⟩).pat (trS U.ax201).pat = true := by
  decide +kernel

theorem clauseAxiom_withHooks (H : HookParams) : clauseAxiom (cH H) fn clB = clauseAxiom c fn clB := rfl
theorem int_sort (H : HookParams) (n : Int) : (cH H).sortOf (int n) = some Srt.int := rfl
theorem clB_plain : plainPats c clB.pats = true := by decide +kernel
theorem clB_sorts : sortsOfTerms c.patCtxAll clB.vars clB.pats = some fn.args := by decide +kernel
theorem int_apart : apartSort c Srt.int = true := by decide +kernel
theorem clB_binds : ∀ i < clB.vars.length, i ∈ varOccsList clB.pats := fun i hi => by
  have : i = 0 := by simpa [clB] using hi
  subst this; decide

/-- **Γ with sentence 201 as written has no model, for every H**: at 5, Γ gives `f(5) = 5`
(`Eval`'s value, through the graph of `>Int` at (5, 0)), the sentence gives `f(5) = 0`, and the
values 5 and 0 of Int denote distinct elements (`ΓDomains`). -/
theorem written_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax201).pat) := by
  intro M _ I hI hax
  obtain ⟨hsok, hsr', hnn, hg, -, -, -, -, hno⟩ := hypSound_of_core (coreOKH H)
  haveI : OvlOK (cH H) := hno
  have htr := (sortCtx_of_all hsok hsr' (OvlOK.ovlCase hno)).trans
  have hD := defOK hI
  have hax' : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", clauseAxiom (cH H) fn clB⟩).pat := by
    rw [clauseAxiom_withHooks]; exact (TiePair.sameB_iff written_clB).mp hax
  have h5 : Γ (cH H) ⊧ (TiePair.app (cH H) f [int 5] ≡ den (cH H) (int 5)) :=
    TiePair.eval_some_sound (hpreTop := by decide +kernel) (cH H) (hypSound_of_core (coreOKH H)) (Semantics.ok_clauseBinds (hokH H))
      (eval_of (k := 10) (by decide +kernel) H) (hfnH H) (hvsH H 5)
  have heq1 := (KoreAML.interp_equal hD).mp (h5 hI KoreAML.val0 default)
  have hws : (cH H).WellSorted clB.vars [(0, int 5)] := by
    intro i s hi
    match i, hi with
    | 0, hi => simp only [clB, List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
               exact ⟨int 5, rfl, int_sort H 5⟩
    | _ + 1, hi => simp [clB] at hi
  have heq2 := PrioTextWitness.clause_eq_ax hI hnn htr (hfnH H) (cl := clB) hax' (ws := [int 5]) (hvsH H 5)
    (σ' := [(0, int 5)]) hws (.cons (.var rfl) .nil) clB_plain clB_sorts clB_binds
    (fun _ h => by simp [clB] at h) (fun _ h => by simp [clB, varOccs] at h) (fun _ h => by simp [clB] at h)
    (r := some (int 0)) (fun v hv => by cases hv; exact int_sort H 0) (fun _ _ _ _ h => by cases h)
    (fun tbl e _ => right_iff hI hnn (lookupFn_spec (hfnH H)).1 (fun v hv => by cases hv; exact int_sort H 0)
      (fun m => by
        show (KoreAML.tr ⟨tbl, []⟩ (GroundTerm.kore (cH H) (int 0))).interpret I e m ↔ (den (cH H) (int 0)).interpret I e m
        rfl)
      (fun t ht => by simp [clB] at ht))
  have he : elemOf (cH H) I (int 5) = elemOf (cH H) I (int 0) := by
    have h1 := (elemOf_spec hI (int_sort H 5) KoreAML.val0).1
    have h2 := (elemOf_spec hI (int_sort H 0) KoreAML.val0).1
    exact (h2 _).mp ((heq2 KoreAML.val0 _).mp ((heq1 _).mpr ((h1 _).mpr rfl)))
  exact absurd (values_apart hI hg htr int_apart (int_sort H 5) (int_sort H 0) he) (by decide)

/-- The premise set's equations with sentence 201 as written in place of Γ's item. -/
noncomputable def writtenPats : List P := fnText.map (trS · |>.pat)

/-- **The premise set with sentence 201 as written has no model, for every H** (`Pre` with
`writtenPats`: every equation of `f` as written, Γ's rule items, the families). -/
theorem no_model_written (H : HookParams) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP TiePair.Pre (cH H) writtenPats) := by
  intro M hM I hI
  have h201 : I ⊧ᴵ (trS U.ax201).pat :=
    hI _ (Or.inl (Or.inl (Or.inl (by
      unfold writtenPats; exact List.mem_map.mpr ⟨U.ax201, List.mem_of_getElem? fnText_W, rfl⟩))))
  have hT : I ⊧ᴵP Pre H := fun φ hφ => by
    rcases hφ with ((hφ | ⟨x, rfl⟩) | hφ) | hφ
    · rcases List.mem_or_eq_of_mem_set hφ with hφ | rfl
      · exact hI _ (Or.inl (Or.inl (Or.inl hφ)))
      · exact w1 (fun ψ hψ => by
          rcases hψ with hψ | ⟨x, rfl⟩
          · rw [List.mem_singleton.mp hψ]; exact h201
          · exact hI _ (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩))))
    · exact hI _ (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩)))
    · exact hI _ (Or.inl (Or.inr hφ))
    · exact hI _ (Or.inr hφ)
  exact written_refuted H M hM I (fun φ hφ => TiePair.gamma_from (shapeH H) φ hφ hT) h201


end KCore.C3EqReqPrioComp

#print axioms KCore.C3EqReqPrioComp.wf_defn
#print axioms KCore.C3EqReqPrioComp.defs_attrsAgree
#print axioms KCore.C3EqReqPrioComp.shape
#print axioms KCore.C3EqReqPrioComp.fns_entailed
#print axioms KCore.C3EqReqPrioComp.fns_from_text
#print axioms KCore.C3EqReqPrioComp.cons_entailed
#print axioms KCore.C3EqReqPrioComp.account
#print axioms KCore.C3EqReqPrioComp.consistent
#print axioms KCore.C3EqReqPrioComp.pre_model
#print axioms KCore.C3EqReqPrioComp.w1
#print axioms KCore.C3EqReqPrioComp.w_text
#print axioms KCore.C3EqReqPrioComp.f_5
#print axioms KCore.C3EqReqPrioComp.f_neg1
#print axioms KCore.C3EqReqPrioComp.clauses_eq
#print axioms KCore.C3EqReqPrioComp.written_refuted
#print axioms KCore.C3EqReqPrioComp.no_model_written
