/-
  The tie (C14) of the reading `keyFunctionAsMember` on its construct fixture e3-map-key-fn:
  `rule <k> get(X) => V ... </k> <m> key(X) |-> V ... </m>`, `key` a total function of the
  definition's own (`key(X) => X +Int 1`) applied as a map key in the rule's left side. The text is
  `f2-examples/mapkeyfn.kompile.kore`, the kompiled text that
  `test/constructs/fixtures/e3-map-key-fn/kompile.txt` records (sha256 0746c2bc…), with its paths
  restored. Run from the package root: `lake env lean -j1 test/NoteMapKeyFn.lean`. Every statement
  is on the literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  Layer 1. `wf_defn`, `coreOK` (kernel); `defs_attrsAgree` (`attrsAgree`). `account`: the function
  equations, the constructor sentences and the rule sentence (`U.ax159`, the account's sentence
  316) are sentences of the user module, apart, with the count of the rest.

  Layer 2. Function equations: Γ's items pattern for pattern (`shape`), entailed for every H
  (`fns_entailed`). Constructor sentences: `cons_entailed`.
  The rule, class *weaker*: Γ's axiom is the sentence with the key `inj(key(X))` written
  `inj(K)`, K a variable of Int, and the conjuncts `K ∈ key(X)` and `⌈r⌉` (`ruleRightDefined`)
  more on its left side. The sentence is the item of `\rewrites{C}(Ltext, r)` at the table of Γ's
  axiom, up to the indices of the variables after K (`rule_text`, kernel). Every element of Γ's left
  side is one of `Ltext` (`left_sub`): the conjunct `K ∈ key(X)` puts the value of K in `key(X)`,
  and an application context, a conjunction among them, is monotone. So the sentence with the
  signature (which gives `\in` its meaning: the sorts Int and GeneratedTopCell, `⌈_⌉`) entails Γ's
  item (`rule_from_text`, `TieRuleLhs.rule_w1`), for every H. `consistent` for every H.

  The expectation (C7 form (a), a step that exists), from `Pre H` (the function equations as
  written, Γ's rule item, the families; it has a model, `pre_model`): `get_steps`, with the map
  `2 |-> 7`, `get(1)` steps to 7: `key(1)` is 2 by its equation, a key of the map; `get_absent`,
  `get(0)` has no successor (with the step's closure): `key(0)` is 1, no key of the map.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.NoteMapKeyFn

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/mapkeyfn.kompile.kore"
definition_of defn from "f2-examples/mapkeyfn.kompile.kore"
user_axioms U from "f2-examples/mapkeyfn.kompile.kore" module "E3-MAP-KEY-FN"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-MAP-KEY-FN")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

theorem wf_defn : wf defn = true := by decide_cheap
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,
hooks, collections, priorities. -/
theorem defs_attrsAgree : attrsAgree kore defn = true := by decide +kernel

/-! ## The function equations -/

/-- The text sentences of Γ's equations, in `fnItems`'s order (`TiePair.fnTextOf`). -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

theorem fnText_index : fnText.map (·.index) = [252, 231, 239, 238, 237, 236, 247, 246, 249, 248, 241, 240, 220, 219,
    230, 229, 226, 225, 228, 227, 233, 232, 235, 234, 243, 242, 245, 244, 224, 223, 222, 221] := by
  decide +kernel

/-- The function equations as written. -/
noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence** (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- **E for every function equation**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat :=
  fun _ had => TiePair.entailed (shapeH H) _ (List.mem_map_of_mem had)

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

/-! ## The rule (sentence 159): W1 -/

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

/-- Γ's axiom of the rule. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩] := by kernel_rfl

/-- Its parts `\rewrites{C}(L', r)`. -/
noncomputable def q0 : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts p0).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

kernel_rfl q0_eq : TieRuleLhs.rwParts p0 = some q0
kernel_rfl q0_sort : q0.1 = srt "GeneratedTopCell"

/-- The context of the left side's term around the `<m>` cell's conjunction, and the conjunction. -/
noncomputable def cutA : KoreCutCtx × Kore.Pattern :=
  (TieRuleLhs.cutAt [1] (TieRuleLhs.andHead q0.2.1)).getD (.hole, .top KoreAML.R)

/-- The `<m>` cell, the first conjunct of that conjunction. -/
noncomputable def mCell : Kore.Pattern := TieRuleLhs.andHead cutA.2

/-- The context of the `<m>` cell around the map key's injected variable, and the variable. -/
noncomputable def cutB : KoreCutCtx × Kore.Pattern :=
  (TieRuleLhs.cutAt [0, 0, 0, 0] mCell).getD (.hole, .top KoreAML.R)

/-- The variable K of the key (index 2 of the table of Γ's axiom), and X. -/
def vK : Kore.EVar := KoreAML.evar "VarV6" (srt "Int")
def vX : Kore.EVar := KoreAML.evar "VarV0" (srt "Int")

/-- `key(X)`. -/
def keyX : Kore.Pattern := ap "Lblkey" [.var (.evar vX)]

kernel_rfl cutB_var : cutB.2 = .var (.evar vK)

-- Γ's left side: the term with K in the key, `\top`, `K ∈ key(X)`, and `⌈r⌉`.
kernel_rfl l0_eq : q0.2.1 = .and q0.1
  (cutA.1.fill (.and (srt "MCell") (cutB.1.fill (.var (.evar vK)) :: TieRuleLhs.andTail cutA.2)) :: .top q0.1 ::
    .in (srt "Int") q0.1 (.var (.evar vK)) keyX :: (TieRuleLhs.andTail q0.2.1).drop 2)

/-- The left side as the text writes it: `key(X)` in the key, and no conjunct after `\top`. -/
noncomputable def Ltext : Kore.Pattern :=
  .and q0.1 [cutA.1.fill (.and (srt "MCell") (cutB.1.fill keyX :: TieRuleLhs.andTail cutA.2)), .top q0.1]

/-- The free variables of the text's form. -/
noncomputable def fT : List VarKey := (freeOf [] (.rewrites q0.1 Ltext q0.2.2)).eraseDups

/-- **The text's sentence 159 is the item of `\rewrites{C}(Ltext, r)` at the table of Γ's axiom**,
the indices of the variables met after K moved down by one (kernel): Γ's axiom is the sentence with
K in the place of `key(X)` and the conjuncts `K ∈ key(X)` and `⌈r⌉` more. -/
theorem rule_text : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT q0.1 Ltext q0.2.2)
    [(4, 3), (5, 4), (6, 5), (7, 6)] = some (trS U.ax159).pat := by
  decide +kernel
theorem fT_free : fT.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel
theorem cutA_noAlias : cutA.1.noAlias ⟨tableOf [] p0, []⟩ = true := by decide +kernel
theorem cutB_noAlias : cutB.1.noAlias ⟨tableOf [] p0, []⟩ = true := by decide +kernel
theorem vK_free : evarKey vK ∈ (freeOf [] p0).eraseDups := by decide +kernel

theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- The top cell's sort. -/
def topSrt : Srt := 17

theorem top_numbered (H : HookParams) : topSrt < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : topSrt < nRegSorts + c.sortNames.length)
theorem top_name (H : HookParams) : (cH H).sortName topSrt = "GeneratedTopCell" :=
  (by decide +kernel : c.sortName topSrt = "GeneratedTopCell")

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

/-- **Every element of Γ's left side is an element of the text's left side**: the conjunct
`K ∈ key(X)` puts the value of K in `key(X)`, so the term with K in the key is in the term with
`key(X)` there (an application context and a conjunction are monotone), and `⌈r⌉` is not asked. -/
theorem left_sub (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (e : Valuation M) (m0 a : M)
    (hg : ∀ k ∈ (freeOf [] p0).eraseDups, (guardOf (tableOf [] p0) k).interpret I e m0)
    (h : (tr ⟨tableOf [] p0, []⟩ q0.2.1).interpret I e a) : (tr ⟨tableOf [] p0, []⟩ Ltext).interpret I e a := by
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σI, hσI1, hσI2⟩ := TieRhs.sortSing_sig hD hSig (int_numbered H)
  obtain ⟨σT, hσT1, hσT2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered H)
  rw [int_name] at hσI1
  rw [top_name] at hσT1
  have hInt : ∀ a, (sym (.sort ("Sort" ++ "Int")) : P).interpret I e a ↔ a = σI := fun a => hσI1 a
  have hTop : ∀ a, (sym (.sort ("Sort" ++ "GeneratedTopCell")) : P).interpret I e a ↔ a = σT := fun a => hσT1 a
  rw [l0_eq, interp_and (List.cons_ne_nil _ _)] at h
  -- the value of K is in `key(X)`
  have hin := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hgK := (TieRuleLhs.guard_evarKey hD).mp (hg _ vK_free)
  rw [show vK.sort = srt "Int" from rfl, trSort_srt] at hgK
  simp only [tr] at hin
  rw [q0_sort, trSort_srt, trSort_srt] at hin
  obtain ⟨⟨w, hw1, hw2⟩, -⟩ := (interp_sIn hD hc hInt hTop hσI2 hσT2 (fun b hb => by
      rw [interp_evar] at hb; rw [hb]; exact (interp_inhOf_of hInt).mp hgK) a).mp hin
  have hKey : ∀ b, (tr ⟨tableOf [] p0, []⟩ (.var (.evar vK))).interpret I e b →
      (tr ⟨tableOf [] p0, []⟩ keyX).interpret I e b := by
    intro b hb
    simp only [tr] at hb
    rw [interp_evar] at hb hw1
    rw [hb, ← hw1]; exact hw2
  unfold Ltext
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine TieRuleLhs.tr_fill_mono _ cutA.1 cutA_noAlias (fun b hb => ?_) a (h _ (List.mem_cons_self ..))
    rw [interp_and (List.cons_ne_nil _ _)] at hb ⊢
    intro p' hp'
    rcases List.mem_cons.mp hp' with rfl | hp'
    · exact TieRuleLhs.tr_fill_mono _ cutB.1 cutB_noAlias hKey b (hb _ (List.mem_cons_self ..))
    · exact hb _ (List.mem_cons_of_mem _ hp')
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- **W1 for the rule, and the converse for `ruleItems`**: Γ's rule item, with its premises
`K ∈ key(X)` and `⌈r⌉`, is a consequence of the text's sentence 159 with the signature, for
every H. -/
theorem rule_from_text (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), (TiePair.Texts [(trS U.ax159).pat] ∪ ΓSig (cH H)) ⊧ it.pat := by
  intro it hit M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hT : I ⊧ᴵ (trS U.ax159).pat := hI _ (Or.inl (Or.inl (List.mem_singleton_self _)))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  rw [List.mem_singleton.mp hit]
  exact TieRuleLhs.rule_w1 hD q0_eq rule_text fT_free hT fun e m0 hg a ha => left_sub H hD hSig e m0 a hg ha

/-! ## The account -/

noncomputable def tiedIdx : List Nat := fnText.map (·.index) ++ consText.map (·.index) ++ [159]

/-- **The account**: the function equations, the constructor sentences and the rule sentence are
sentences of the user module, each once and none in two classes, with the sizes of the three
classes and of the rest (not tied here). -/
theorem account : tiedIdx.Nodup ∧ tiedIdx.all (fun i => (U.all.map (·.index)).contains i) = true ∧
    (U.all.map (·.index)).Nodup ∧
    (fnText.length, consText.length, [159].length, U.all.length - tiedIdx.length) = (32, 30, 1, 208) := by
  decide +kernel

/-! ## The facts the deciders leave -/

def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel

/-- The rule's `pre` holds no binder: the semantics reads no confined sort. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel
theorem hrcH (H : HookParams) : (cH H).readsConfined = false := (Semantics.readsConfined_withHooks c H).trans readsConfined_c

/-- None named; `OpenDecided` as the semantics reads no confined sort (the rule has a `pre`, so the
semantics is not `plain`), `OpenLaws` as no parameter is raw. -/
theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] := by
  have h1 : (cH H).rankObligations callOrder ++ (cH H).decObligationsL = [] := by
    rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named
  have h2 := (Semantics.totalObligationsRP_withHooks _ H callOrder []).trans total_named
  have h3 := (Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named
  have h4 := (Det.Semantics.matchObligationsL_withHooks _ H).trans match_named
  refine ⟨fun f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun p hp => ?_,
    openDecided_of_readsConfined (hrcH H), openLaws_of_plain fun k hk => noRaw k hk⟩
  · rw [h1] at hf; exact absurd hf List.not_mem_nil
  · rw [h2] at hf; exact absurd hf List.not_mem_nil
  · rw [h3] at hf; exact absurd hf List.not_mem_nil
  · rw [h4] at hp; exact absurd hp List.not_mem_nil

theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- **Γ with the step's closure has a model, for every H** (C14 closure (a)). -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## The expectation (C7 form (a)) -/

/-- **The premises of the derivations**: every function equation as written, Γ's rule item (the
reading of the rule sentence 159, a consequence of it by `rule_from_text`), and the families. -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- **`Pre` with the step's closure has a model, for every H.** -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) :=
  TiePair.pre_model (shapeH H) (consistent H)

def kCell : Sym := 385
def mCellL : Sym := 387
def getL : Sym := 389
def keyL : Sym := 390
def exp : Srt := 34

theorem names : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName mCellL = "Lbl'-LT-'m'-GT-'" ∧
    c.symName getL = "Lblget" ∧ c.symName keyL = "Lblkey" ∧ c.sortName exp = "Exp" ∧
    c.sortName Srt.map = "Map" := by
  decide +kernel

private theorem hready : CExec.execReady c = true := by decide +kernel

/-- The map `2 |-> 7`. -/
def tab : GroundTerm := .map Srt.map [(.inj Srt.int Srt.kitem (int 2), .inj Srt.int Srt.kitem (int 7))]

/-- The configuration with the item `it` in the k cell and the map `2 |-> 7`. -/
def cfg (it : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [it, .ctor dotk []]], .ctor mCellL [tab], .ctor counterLabel [int 0]]

def Get1 : Config c := ⟨cfg (.inj exp Srt.kitem (.ctor getL [int 1])), by decide +kernel⟩
def Seven : Config c := ⟨cfg (.inj Srt.int Srt.kitem (int 7)), by decide +kernel⟩
def Get0 : Config c := ⟨cfg (.inj exp Srt.kitem (.ctor getL [int 0])), by decide +kernel⟩

theorem hreadyH (H : HookParams) : CExec.execReady (cH H) = true := (CExec.execReady_withHooks c H).trans hready
theorem fnDetH (H : HookParams) : FnDet (cH H) := fnDet_of_agree (fnHypH H).2.2.1 (fnHypH H).2.2.2.1

-- The executable step at `get(1)` reads no interpretation of the parameters (the definition has
-- none): `key(1)` is decided by `key`'s equation.
kernel_rfl get1_withHooks : ∀ H : HookParams,
  CExec.successorsN (c.withHooks H) 50 Get1.val = CExec.successorsN c 50 Get1.val
kernel_rfl get0_withHooks : ∀ H : HookParams,
  CExec.successorsN (c.withHooks H) 50 Get0.val = CExec.successorsN c 50 Get0.val
kernel_rfl get0_fuel_withHooks : ∀ H : HookParams,
  CExec.outOfFuel (c.withHooks H) 50 Get0.val = CExec.outOfFuel c 50 Get0.val

/-- The step, for every H: `key(1)` is 2 by its equation, a key of the map, so `get(1)` is 7. -/
theorem get_step (H : HookParams) :
    Step (cH H) (TieRuleLhs.cfgH noRaw Get1 H) (TieRuleLhs.cfgH noRaw Seven H) := by
  have hy : Seven.val ∈ CExec.successorsN (c.withHooks H) 50 Get1.val := by
    rw [get1_withHooks]; decide +kernel
  obtain ⟨_, h⟩ := CExec.successorsN_step_ready (hreadyH H) (x := TieRuleLhs.cfgH noRaw Get1 H) hy
  exact h

/-- **`get(1)` steps to 7 with the map `2 |-> 7`, derived from `Pre`**, for every H. -/
theorem get_steps (H : HookParams) : Pre H ⊧ (den (cH H) Get1.val ⇒ KoreAML.sNext (den (cH H) Seven.val)) :=
  TiePair.cut (shapeH H) (sound_at_step _ (coreOKH H) (hrcH H) _ _ (get_step H))

/-- **`get(0)` has no successor with the map `2 |-> 7`, derived from `Pre` with the step's
closure**, for every H: `key(0)` is 1, no key of the map. -/
theorem get_absent (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) Get0.val ⇒ KoreAML.allNext (KoreAML.disjList (([] : List GroundTerm).map (den (cH H))))) :=
  TiePair.cutStep (shapeH H) (complete_at_step _ (coreOKH H) (hrcH H) (TieRuleLhs.cfgH noRaw Get0 H)
    (stepDecided_of_fnHyp (coreOKH H) (fnHypH H) _) []
    fun y hy => absurd hy (CExec.noStep_at (hreadyH H) (fnDetH H) (n := 50) (x := TieRuleLhs.cfgH noRaw Get0 H)
      ((get0_fuel_withHooks H).trans (by decide +kernel)) ((get0_withHooks H).trans (by decide +kernel)) y))

end KCore.NoteMapKeyFn

#print axioms KCore.NoteMapKeyFn.wf_defn
#print axioms KCore.NoteMapKeyFn.defs_attrsAgree
#print axioms KCore.NoteMapKeyFn.account
#print axioms KCore.NoteMapKeyFn.shape
#print axioms KCore.NoteMapKeyFn.fns_entailed
#print axioms KCore.NoteMapKeyFn.cons_entailed
#print axioms KCore.NoteMapKeyFn.rule_text
#print axioms KCore.NoteMapKeyFn.left_sub
#print axioms KCore.NoteMapKeyFn.rule_from_text
#print axioms KCore.NoteMapKeyFn.consistent
#print axioms KCore.NoteMapKeyFn.pre_model
#print axioms KCore.NoteMapKeyFn.get_step
#print axioms KCore.NoteMapKeyFn.get_steps
#print axioms KCore.NoteMapKeyFn.get_absent
