/-
  The tie (C14) of the readings `equationPriority` and `owiseAsPriority` on their construct fixture
  e2-equation: `f`'s equations `f(0) => 0`, `f(1) => 1 [priority(10)]`, `f(2) => 2 [priority(50)]`,
  `f(3) => 3 [priority(60)]`, `f(_) => 9 [owise]`, beside `gc`, `gs`, `h` (one equation
  `non-executable, priority(60)`) and `sl`. The text is `f2-examples/eqprio.kompile.kore`: the
  kompiled text that `test/constructs/fixtures/e2-equation/kompile.txt` records (sha256 703fd23f…),
  with its paths restored. Run from the package root: `lake env lean -j1 test/NoteEqPrio.lean`.
  Every statement is on the literal `defn`, for every interpretation H; nothing reads `Parse.parse`
  or `emit`.

  Layer 1. `wf_defn`, `coreOK` (kernel); `defs_attrsAgree_parts` (constructors, collections,
  priorities; `attrsAgree` itself is false here, `attrsAgree_p`: `p`, a function without equations,
  is read as a parameter symbol, which `attrsAgree` does not admit); `account`: the function equations and
  the constructor sentences are sentences of the user module, apart, with the count of the rest.

  Layer 2, the function equations (`fnText`, in `fnItems`'s order; written out, since `f`'s
  equations `f(0)` and `f(2)` have one priority, 50, and `TiePair.fnTextOf`, which finds a sentence by
  head and priority, finds 200 for both).
  - `equationPriority`, class *weaker*: the four equations with a sibling of a smaller priority,
    `f(0)` and `f(2)` (50, below `f(1)`'s 10), `f(3)` (60) and `h`'s aside equation (60, below `h`'s
    50), are in Γ under the negation of those siblings' clauses (`prioEquation`), a premise the text
    does not write: each sentence entails Γ's item (`w0`, `w2`, `w3`, `w8`, W1) and is the item
    without that premise (`w0_text`, …), and is not the item (`w0_differs`, …).
  - `owiseAsPriority`, class *equal*: the `[owise]` equation (204) is read as a clause of priority
    200, so Γ's item excludes the clauses of all four siblings; the text's sentence writes the same
    exclusion with its disjuncts in another order and other names of its bound variables
    (`ow_same`, `TieAlpha.acEqB`): the two are satisfied by the same interpretations.
  - The other equations are Γ's items pattern for pattern (`shape`). `fns_entailed` (E, all but the
    four narrowed ones), `fns_from_text` (each item a consequence of its sentence).
  Constructor sentences: `cons_entailed`. `consistent` for every H.

  The expectations (C7 form (a)), from `Pre H` (the function equations as written, the four
  narrowed ones as Γ's items, the families; it has a model, `pre_model`): `f_1`, `f(1) = 1`, from
  the sentence as written; `f_3`, `f(3) = 3`, through the reading (family the priority premise
  `prioEquation`); `f_5`, `f(5) = 9`, from the `[owise]` sentence, whose exclusion holds at 5;
  `h_4`, `h(4) = 4`, through the reading (the aside equation `h(X) => X +Int 1` is silent where the
  equation of priority 50 applies).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.NoteEqPrio

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/eqprio.kompile.kore"
definition_of defn from "f2-examples/eqprio.kompile.kore"
user_axioms U from "f2-examples/eqprio.kompile.kore" module "E2-EQUATION"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E2-EQUATION")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

theorem wf_defn : wf defn = true := by decide_cheap
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The attributes of the text agree with `defn` on constructors, collection symbols and
priorities (`AttrsAgree.ctors`, `colls`, `prios`: each equation's priority, `[owise]` as 200, is its
clause's). -/
theorem defs_attrsAgree_parts : AttrsAgree.ctors kore c = true ∧ AttrsAgree.colls kore c = true ∧
    AttrsAgree.prios kore defn = true := by decide +kernel

/-- `attrsAgree` is false on this text, by `p(Int, Int) [function]`, declared a function without
`hook` and with no equation: the reader reads it as a parameter symbol (its value the
interpretation's), and `AttrsAgree.fns` and `AttrsAgree.hooks` ask a function symbol without a hook to be
a function of the definition and no parameter. -/
theorem attrsAgree_p : attrsAgree kore defn = false ∧ c.params.any (c.symName ·.sig.name == "Lblp") = true ∧
    c.allFns.all (c.symName ·.label != "Lblp") = true := by decide +kernel

/-! ## The function equations -/

/-- The text sentences of Γ's 37 equations, in `fnItems`'s order: `f`'s five (200, 201, 202, 203,
and 204 its `[owise]` one), `gc`'s, `gs`'s, `h`'s two (209, and 210 the aside one), `sl`'s, then the
sort predicates'. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax200, U.ax201, U.ax202, U.ax203, U.ax204, U.ax206, U.ax208, U.ax209, U.ax210, U.ax262, U.ax226,
   U.ax234, U.ax233, U.ax232, U.ax231, U.ax238, U.ax237, U.ax240, U.ax239, U.ax236, U.ax235, U.ax215,
   U.ax214, U.ax225, U.ax224, U.ax221, U.ax220, U.ax223, U.ax222, U.ax228, U.ax227, U.ax230, U.ax229,
   U.ax217, U.ax216, U.ax219, U.ax218]

theorem fnText_length : fnText.length = 37 := rfl
theorem gammaPats_length : (TiePair.gammaPats c).length = 37 := by decide +kernel

/-! ### `equationPriority`: the four equations read under the priority premise (W1) -/

/-- Γ's axiom of item 0 (sentence 200). -/
noncomputable def a0 : Kore.Axiom := ((TiePair.fnAxioms c)[0]?).getD ⟨[], .top KoreAML.R, []⟩
theorem a0_at : (TiePair.fnAxioms c)[0]? = some a0 := by decide +kernel
noncomputable def g0 : P := (trAxiom [] [] ⟨0, "kernel", a0⟩).pat
theorem g0_at : (TiePair.gammaPats c)[0]? = some g0 := TiePair.gammaPats_at a0_at
/-- Its premise has the negated conjunct, the clauses of a smaller priority. -/
theorem a0_narrowed : (TiePair.negParts a0.pattern).isSome = true := by decide +kernel
/-- **Γ's item without the priority premise is the text's sentence 200** (up to the indices of its
variables; kernel), and it is not the sentence. -/
theorem w0_text : TiePair.sameB (TiePair.minusNeg a0) (trS U.ax200).pat = true := by decide +kernel
theorem w0_differs : g0 ≠ (trS U.ax200).pat := by decide +kernel
/-- **W1**: sentence 200 entails Γ's item 0. -/
theorem w0 : TiePair.Texts [(trS U.ax200).pat] ⊧ g0 :=
  fun {M} _ {I} hI => TiePair.item_of_sentence (TiePair.defOK_texts hI) w0_text
    (hI _ (Or.inl (List.mem_singleton_self _)))

/-- Γ's axiom of item 2 (sentence 202). -/
noncomputable def a2 : Kore.Axiom := ((TiePair.fnAxioms c)[2]?).getD ⟨[], .top KoreAML.R, []⟩
theorem a2_at : (TiePair.fnAxioms c)[2]? = some a2 := by decide +kernel
noncomputable def g2 : P := (trAxiom [] [] ⟨0, "kernel", a2⟩).pat
theorem g2_at : (TiePair.gammaPats c)[2]? = some g2 := TiePair.gammaPats_at a2_at
/-- Its premise has the negated conjunct, the clauses of a smaller priority. -/
theorem a2_narrowed : (TiePair.negParts a2.pattern).isSome = true := by decide +kernel
/-- **Γ's item without the priority premise is the text's sentence 202** (up to the indices of its
variables; kernel), and it is not the sentence. -/
theorem w2_text : TiePair.sameB (TiePair.minusNeg a2) (trS U.ax202).pat = true := by decide +kernel
theorem w2_differs : g2 ≠ (trS U.ax202).pat := by decide +kernel
/-- **W1**: sentence 202 entails Γ's item 2. -/
theorem w2 : TiePair.Texts [(trS U.ax202).pat] ⊧ g2 :=
  fun {M} _ {I} hI => TiePair.item_of_sentence (TiePair.defOK_texts hI) w2_text
    (hI _ (Or.inl (List.mem_singleton_self _)))

/-- Γ's axiom of item 3 (sentence 203). -/
noncomputable def a3 : Kore.Axiom := ((TiePair.fnAxioms c)[3]?).getD ⟨[], .top KoreAML.R, []⟩
theorem a3_at : (TiePair.fnAxioms c)[3]? = some a3 := by decide +kernel
noncomputable def g3 : P := (trAxiom [] [] ⟨0, "kernel", a3⟩).pat
theorem g3_at : (TiePair.gammaPats c)[3]? = some g3 := TiePair.gammaPats_at a3_at
/-- Its premise has the negated conjunct, the clauses of a smaller priority. -/
theorem a3_narrowed : (TiePair.negParts a3.pattern).isSome = true := by decide +kernel
/-- **Γ's item without the priority premise is the text's sentence 203** (up to the indices of its
variables; kernel), and it is not the sentence. -/
theorem w3_text : TiePair.sameB (TiePair.minusNeg a3) (trS U.ax203).pat = true := by decide +kernel
theorem w3_differs : g3 ≠ (trS U.ax203).pat := by decide +kernel
/-- **W1**: sentence 203 entails Γ's item 3. -/
theorem w3 : TiePair.Texts [(trS U.ax203).pat] ⊧ g3 :=
  fun {M} _ {I} hI => TiePair.item_of_sentence (TiePair.defOK_texts hI) w3_text
    (hI _ (Or.inl (List.mem_singleton_self _)))

/-- Γ's axiom of item 8 (sentence 210). -/
noncomputable def a8 : Kore.Axiom := ((TiePair.fnAxioms c)[8]?).getD ⟨[], .top KoreAML.R, []⟩
theorem a8_at : (TiePair.fnAxioms c)[8]? = some a8 := by decide +kernel
noncomputable def g8 : P := (trAxiom [] [] ⟨0, "kernel", a8⟩).pat
theorem g8_at : (TiePair.gammaPats c)[8]? = some g8 := TiePair.gammaPats_at a8_at
/-- Its premise has the negated conjunct, the clauses of a smaller priority. -/
theorem a8_narrowed : (TiePair.negParts a8.pattern).isSome = true := by decide +kernel
/-- **Γ's item without the priority premise is the text's sentence 210** (up to the indices of its
variables; kernel), and it is not the sentence. -/
theorem w8_text : TiePair.sameB (TiePair.minusNeg a8) (trS U.ax210).pat = true := by decide +kernel
theorem w8_differs : g8 ≠ (trS U.ax210).pat := by decide +kernel
/-- **W1**: sentence 210 entails Γ's item 8. -/
theorem w8 : TiePair.Texts [(trS U.ax210).pat] ⊧ g8 :=
  fun {M} _ {I} hI => TiePair.item_of_sentence (TiePair.defOK_texts hI) w8_text
    (hI _ (Or.inl (List.mem_singleton_self _)))

/-! ### `owiseAsPriority`: the `[owise]` equation -/

noncomputable def g4 : P := (TiePair.gammaPats c).getD 4 ⊥
theorem g4_at : (TiePair.gammaPats c)[4]? = some g4 := by decide +kernel

/-- **Γ's item of the `[owise]` equation and sentence 204 agree** up to the order of the
exclusion's disjuncts (the text lists the siblings 1, 3, 0, 2; Γ 0, 1, 2, 3) and the names of the
variables (`TieAlpha.acEqB`; kernel). -/
theorem ow_same : TieAlpha.acEqB g4 (trS U.ax204).pat = true := by decide +kernel

theorem ow_iff {M : Type} {I : Interpretation KoreAML.Sym M} : (I ⊧ᴵ (trS U.ax204).pat) ↔ (I ⊧ᴵ g4) :=
  (TieAlpha.acEqB_sat ow_same).symm

/-! ### The premise set's equations -/

/-- The premise set's equations, in `fnItems`'s order: each text sentence's translation, and Γ's
item in the place of the four narrowed sentences and of the `[owise]` one (C7 (ii)). -/
noncomputable def textPats : List P :=
  ((((fnText.map (trS · |>.pat)).set 0 g0).set 2 g2).set 3 g3 |>.set 4 g4).set 8 g8

/-- **Each of Γ's equations is the translation of its text sentence**, but the five set to Γ's
items (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- The positions set to Γ's items. -/
def setAt : List Nat := [0, 2, 3, 4, 8]

theorem textPats_of {j : Nat} {ad : AxiomDecl} (hj : fnText[j]? = some ad) (hn : j ∉ setAt) :
    textPats[j]? = some (trS ad).pat := by
  simp only [setAt, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨h0, h2, h3, h4, h8⟩ := hn
  unfold textPats
  rw [List.getElem?_set_ne (Ne.symm h8), List.getElem?_set_ne (Ne.symm h4), List.getElem?_set_ne (Ne.symm h3),
    List.getElem?_set_ne (Ne.symm h2), List.getElem?_set_ne (Ne.symm h0), List.getElem?_map, hj]
  rfl

/-- A model of Γ satisfies each of Γ's equations. -/
theorem gamma_sat {H : HookParams} {M : Type} {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    {j : Nat} {g : P} (hg : (TiePair.gammaPats c)[j]? = some g) : I ⊧ᴵ g := by
  obtain ⟨it, hit, rfl⟩ : ∃ it ∈ fnItems c, it.pat = g := by
    unfold TiePair.gammaPats at hg
    rw [List.getElem?_map] at hg
    cases h : (fnItems c)[j]? with
    | none => rw [h] at hg; cases hg
    | some it => rw [h] at hg; exact ⟨it, List.mem_of_getElem? h, Option.some.inj hg⟩
  exact hI _ (Or.inl (Or.inl (Or.inr (Or.inl ⟨it, by rw [TiePair.fnItems_withHooks]; exact hit, rfl⟩))))

/-- **E for the `[owise]` equation**: Γ entails sentence 204, for every H. -/
theorem ow_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax204).pat := by
  intro M _ I hI
  exact ow_iff.mpr (gamma_sat hI g4_at)

/-- **E for the function equations other than the four narrowed ones**: Γ entails each, for every
H; the `[owise]` one through `ow_iff`. -/
theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad →
    j ∉ [0, 2, 3, 8] → Γ (cH H) ⊧ (trS ad).pat := by
  intro j ad hj hn
  by_cases h4 : j = 4
  · subst h4
    have : ad = U.ax204 := by
      have h' : fnText[4]? = some U.ax204 := rfl
      rw [h'] at hj; exact (Option.some.inj hj).symm
    subst this
    exact ow_entailed H
  · have hn' : j ∉ setAt := by
      simp only [setAt, List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
      omega
    exact TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (textPats_of hj hn'))

/-- **The converse for `fnItems`**: each item is a consequence of its text sentence, the j-th of
`fnText`; the four narrowed ones by W1, the `[owise]` one by `ow_iff`, the others by their
translation. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj
  have hg : (TiePair.gammaPats c)[j]? = some it.pat := by
    rw [← TiePair.gammaPats_withHooks c H]
    unfold TiePair.gammaPats; rw [List.getElem?_map, hj]; rfl
  have pick : ∀ {i : Nat} {g : P} {ad : AxiomDecl}, (TiePair.gammaPats c)[i]? = some g → fnText[i]? = some ad →
      (TiePair.Texts [(trS ad).pat] ⊧ g) → j = i → ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
    intro i g ad hgi hti hent hji
    subst hji
    rw [hgi] at hg
    exact ⟨ad, hti, (Option.some.inj hg) ▸ hent⟩
  by_cases h0 : j = 0
  · exact pick g0_at rfl w0 h0
  by_cases h2 : j = 2
  · exact pick g2_at rfl w2 h2
  by_cases h3 : j = 3
  · exact pick g3_at rfl w3 h3
  by_cases h8 : j = 8
  · exact pick g8_at rfl w8 h8
  by_cases h4 : j = 4
  · exact pick g4_at rfl (fun {M} _ {I} hI => ow_iff.mp (hI _ (Or.inl (List.mem_singleton_self _)))) h4
  obtain ⟨t, ht, hent⟩ := TiePair.from_text (shapeH H) j it hj
  cases hf : fnText[j]? with
  | none =>
    have : j < 37 := by
      have := List.getElem?_eq_some_iff.mp hg
      obtain ⟨hlt, _⟩ := this
      rw [gammaPats_length] at hlt; exact hlt
    rw [List.getElem?_eq_none_iff, fnText_length] at hf; omega
  | some ad =>
    have hn : j ∉ setAt := by simp only [setAt, List.mem_cons, List.not_mem_nil, or_false]; omega
    rw [textPats_of hf hn] at ht
    cases ht
    exact ⟨ad, rfl, hent⟩

/-! ## The constructor sentences -/

noncomputable def consText : List AxiomDecl := U.all.filter fun ad => tieConsB c ad.ax

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

noncomputable def tiedIdx : List Nat := fnText.map (·.index) ++ consText.map (·.index)

/-- **The account**: the function equations and the constructor sentences are sentences of the
user module, each once and none in both classes, with the sizes of the two classes and of the
rest (not tied here). -/
theorem account : tiedIdx.Nodup ∧ tiedIdx.all (fun i => (U.all.map (·.index)).contains i) = true ∧
    (U.all.map (·.index)).Nodup ∧
    (fnText.length, consText.length, U.all.length - tiedIdx.length) = (37, 24, 199) := by decide +kernel

/-! ## The facts the deciders leave -/

def f : Sym := 384
def h : Sym := 387

theorem names : c.symName f = "Lblf" ∧ c.symName h = "Lblh" := by decide +kernel

noncomputable abbrev fnF : Fn := c.fns[0]'(by decide +kernel)
noncomputable abbrev fnH : Fn := c.fns[3]'(by decide +kernel)

theorem hfnF : c.lookupFn f = some fnF := rfl
theorem hfnHh : c.lookupFn h = some fnH := rfl
theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok
theorem hfnFH (H : HookParams) : (cH H).lookupFn f = some fnF := by rw [Semantics.lookupFn_withHooks]; exact hfnF
theorem hfnHH (H : HookParams) : (cH H).lookupFn h = some fnH := by rw [Semantics.lookupFn_withHooks]; exact hfnHh
theorem hvsFH (H : HookParams) (n : Int) : (cH H).sortsOf [int n] = some fnF.args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; rfl
theorem hvsHH (H : HookParams) (n : Int) : (cH H).sortsOf [int n] = some fnH.args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; rfl

def callOrder : List Nat := [384, 385, 386, 387, 388]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel

theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- None named. The definition is not `plain` (`h`'s aside clause), so `OpenDecided` comes from its
reading no confined sort and `OpenLaws` from its parameters' being no open generators. -/
theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] := by
  have h1 : (cH H).rankObligations callOrder ++ (cH H).decObligationsL = [] := by
    rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named
  have h2 := (Semantics.totalObligationsRP_withHooks _ H callOrder []).trans total_named
  have h3 := (Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named
  have h4 := (Det.Semantics.matchObligationsL_withHooks _ H).trans match_named
  exact ⟨fun f hf => by rw [h1] at hf; exact absurd hf List.not_mem_nil,
    fun f hf => by rw [h2] at hf; exact absurd hf List.not_mem_nil,
    fun f hf => by rw [h3] at hf; exact absurd hf List.not_mem_nil,
    fun p hp => by rw [h4] at hp; exact absurd hp List.not_mem_nil,
    openDecided_of_readsConfined ((Semantics.readsConfined_withHooks c H).trans readsConfined_c),
    openLaws_of_plain noRaw⟩

theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- **Γ with the step's closure has a model, for every H** (C14 closure (a)). -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## The expectations (C7 form (a)) -/

/-- The premises of the derivations: the function sentences as written, Γ's items in the place of
the four narrowed ones and of the `[owise]` one, and the families. -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- **`Pre` with the step's closure has a model, for every H.** -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) :=
  TiePair.pre_model (shapeH H) (consistent H)

/-- `⟦g(n)⟧`. -/
noncomputable abbrev at1 (H : HookParams) (g : Sym) (n : Int) : P := TiePair.app (cH H) g [int n]

/-- **`f(1) = 1`, derived from `Pre`**, for every H: from sentence 201 as written. -/
theorem f_1 (H : HookParams) : Pre H ⊧ (at1 H f 1 ≡ den (cH H) (int 1)) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H)
    (TiePair.eval_withHooks hok hsr hmr noRaw H hfnF rfl (n := 10) (by decide +kernel)) (hfnFH H) (hvsFH H 1)

/-- **`f(3) = 3`, derived from `Pre`**, for every H: through the reading (Γ's item of sentence
203, under the negation of the clauses of priority 10 and 50, which do not apply at 3). -/
theorem f_3 (H : HookParams) : Pre H ⊧ (at1 H f 3 ≡ den (cH H) (int 3)) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H)
    (TiePair.eval_withHooks hok hsr hmr noRaw H hfnF rfl (n := 10) (by decide +kernel)) (hfnFH H) (hvsFH H 3)

/-- **`f(5) = 9`, derived from `Pre`**, for every H: from the `[owise]` equation, whose exclusion
of the four siblings holds at 5. -/
theorem f_5 (H : HookParams) : Pre H ⊧ (at1 H f 5 ≡ den (cH H) (int 9)) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H)
    (TiePair.eval_withHooks hok hsr hmr noRaw H hfnF rfl (n := 10) (by decide +kernel)) (hfnFH H) (hvsFH H 5)

/-- **`h(4) = 4`, derived from `Pre`**, for every H: through the reading (the aside equation of
priority 60 is Γ's item under the negation of the clause of priority 50, which applies at 4). -/
theorem h_4 (H : HookParams) : Pre H ⊧ (at1 H h 4 ≡ den (cH H) (int 4)) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H)
    (TiePair.eval_withHooks hok hsr hmr noRaw H hfnHh rfl (n := 10) (by decide +kernel)) (hfnHH H) (hvsHH H 4)

end KCore.NoteEqPrio

#print axioms KCore.NoteEqPrio.wf_defn
#print axioms KCore.NoteEqPrio.defs_attrsAgree_parts
#print axioms KCore.NoteEqPrio.attrsAgree_p
#print axioms KCore.NoteEqPrio.account
#print axioms KCore.NoteEqPrio.shape
#print axioms KCore.NoteEqPrio.w0
#print axioms KCore.NoteEqPrio.w2
#print axioms KCore.NoteEqPrio.w3
#print axioms KCore.NoteEqPrio.w8
#print axioms KCore.NoteEqPrio.ow_iff
#print axioms KCore.NoteEqPrio.fns_entailed
#print axioms KCore.NoteEqPrio.fns_from_text
#print axioms KCore.NoteEqPrio.cons_entailed
#print axioms KCore.NoteEqPrio.consistent
#print axioms KCore.NoteEqPrio.pre_model
#print axioms KCore.NoteEqPrio.f_1
#print axioms KCore.NoteEqPrio.f_3
#print axioms KCore.NoteEqPrio.f_5
#print axioms KCore.NoteEqPrio.h_4
