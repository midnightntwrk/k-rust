/-
  The tie (C14) of the reading `existsAsVariable` on its construct fixture e3-ml-rule-lhs-exists:
  `rule <k> c(#Exists Y:Exp. d(Y, b())) => a() ... </k>`, a rule whose left side binds a variable,
  read with the variable free (a variable of the rule). The text is
  `f2-examples/mlex.kompile.kore` (as test/Guards.lean's `DevEx` reads it). Run from the package
  root: `lake env lean -j1 test/NoteExVar.lean`. Every statement is on the literal `defn`, for
  every interpretation H; nothing reads `Parse.parse` or `emit`.

  Layer 1. `wf_defn`, `coreOK` (kernel); `defs_attrsAgree`; `account`: the function equations,
  the constructor sentences and the rule sentence are sentences of the user module, apart, with
  the count of the rest.

  Layer 2. Function equations (the sort predicates'): Γ's items pattern for pattern (`shape`),
  entailed for every H (`fns_entailed`). Constructor sentences: `cons_entailed`.
  The rule (sentence 104), class *weaker*: Γ's item is the sentence with `d(V0, b())` in the
  place of `\exists{SortExp{}}(V0, d(V0, b()))`, V0 free, and the conjunct `⌈r⌉` more on its left
  side. The sentence is the item of `\rewrites{C}(Ltext, r)` at the table of Γ's axiom
  (`rule_text0`, kernel), and every element of Γ's left side is one of `Ltext` (`left0`: an
  application context is monotone, and `d(V0, b())` at the value of V0, an element of Exp by its
  guard, is in `\exists V0. d(V0, b())`). So the sentence entails the item (`rule_from_text`,
  `TieRuleLhs.rule_w1`, every H). `consistent` for every H.

  The expectations (C7 form (a)), from `Pre H` (the function equations as written, Γ's rule item,
  the families; it has a model with the step's closure, `pre_model`). From sentences (a step that
  exists): `ex_a`: `c(d(a, b))` steps to `a`; `ex_b`: `c(d(b, b))` steps to `a`. Through the
  reading (no successor; family `Γstep`): `ex_x`: `c(d(b, a))`, an instance of the left side at
  no value of the variable, has no successor.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.NoteExVar

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/mlex.kompile.kore"
definition_of defn from "f2-examples/mlex.kompile.kore"
user_axioms U from "f2-examples/mlex.kompile.kore" module "E3-ML-RULE-LHS-EXISTS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-ML-RULE-LHS-EXISTS")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

theorem wf_defn : wf defn = true := by decide +kernel
theorem coreOK : c.coreOK = true := by decide +kernel
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The attributes of the text agree with `defn` (`attrsAgree`). -/
theorem defs_attrsAgree : attrsAgree kore defn = true := by decide +kernel

/-! ## The function equations -/

/-- The text sentences of Γ's equations, in `fnItems`'s order (`TiePair.fnTextOf`). -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

theorem fnText_index : fnText.map (·.index) = [124, 132, 131, 130, 129, 136, 135, 138, 137, 134, 133, 111, 110, 123, 122, 119, 118, 121, 120, 126, 125, 128, 127, 115, 114, 117, 116, 113, 112] := by
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

/-! ## The rule (sentence 104): W1 -/

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

/-- Γ's axiom of rule 0. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0

/-- Its parts `\rewrites{C}(L', r)`. -/
noncomputable def q0 : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts p0).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

kernel_rfl q0_eq : TieRuleLhs.rwParts p0 = some q0

/-- The context of its left side's term around the argument of `c`, and the argument. -/
noncomputable def cut0 : KoreCutCtx × Kore.Pattern :=
  (TieRuleLhs.cutAt [0, 0, 0, 0, 0] (TieRuleLhs.andHead q0.2.1)).getD (.hole, .top KoreAML.R)

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩] := by kernel_rfl

noncomputable def K : KoreCutCtx := cut0.1

theorem names : c.symName 385 = "Lbla" ∧ c.symName 386 = "Lblb" ∧ c.symName 387 = "Lblc" ∧ c.symName 388 = "Lbld" ∧
    c.sortName 32 = "Exp" := by decide +kernel

/-- The variable Γ's axiom holds at the first argument of `d`. -/
noncomputable def x0 : Kore.EVar :=
  (((TieRuleLhs.cutAt [0, 0, 0, 0, 0, 0] (TieRuleLhs.andHead q0.2.1)).map (·.2)).bind TieRuleLhs.evarOf).getD
    (KoreAML.evar "X" KoreAML.R)

kernel_rfl l0_eq : q0.2.1 = .and q0.1 (K.fill cut0.2 :: .top q0.1 :: (TieRuleLhs.andTail q0.2.1).drop 1)

/-- The left side as the text writes it: the argument of `c` is `\exists{SortExp{}}(V0, d(V0, b()))`,
and no conjunct follows `\top`. -/
noncomputable def Ltext : Kore.Pattern := .and q0.1 [K.fill (.exist x0.sort x0 cut0.2), .top q0.1]

theorem x0_sort : x0.sort = KoreAML.srt "Exp" := by decide +kernel

/-- The free variables of the text's form. -/
noncomputable def fT : List VarKey := (freeOf [] (.rewrites q0.1 Ltext q0.2.2)).eraseDups

/-- **The text's sentence 104 is the item of `\rewrites{C}(Ltext, r)` at the table of Γ's axiom**
(kernel). -/
theorem rule_text0 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT q0.1 Ltext q0.2.2) [] = some (trS U.ax104).pat := by
  decide +kernel
theorem fT_free0 : fT.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel
theorem K_noAlias0 : K.noAlias ⟨tableOf [] p0, []⟩ = true := by decide +kernel

theorem x0_free : evarKey x0 ∈ (freeOf [] p0).eraseDups := by decide +kernel

/-- Every element of Γ's left side of rule 0 is an element of the text's left side. -/
theorem left0 {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I) (e : Valuation M) (m : M) (a : M)
    (hg : ∀ k ∈ (freeOf [] p0).eraseDups, (guardOf (tableOf [] p0) k).interpret I e m)
    (h : (tr ⟨tableOf [] p0, []⟩ q0.2.1).interpret I e a) : (tr ⟨tableOf [] p0, []⟩ Ltext).interpret I e a := by
  rw [l0_eq, interp_and (List.cons_ne_nil _ _)] at h
  unfold Ltext
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine TieRuleLhs.tr_fill_mono _ K K_noAlias0 (fun a' h' => TieRuleLhs.sub_exists hD ((TieRuleLhs.guard_evarKey hD).mp (hg _ x0_free)) a' h') a (h _ (List.mem_cons_self ..))
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- **W1 for the rule, and the converse for `ruleItems`**: Γ's rule item is a consequence of the
text's sentence 104, for every H. -/
theorem rule_from_text (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), TiePair.Texts [(trS U.ax104).pat] ⊧ it.pat := by
  intro it hit M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq, List.mem_singleton] at hit
  subst hit
  have hD : DefOK I := TiePair.defOK_texts hI
  exact TieRuleLhs.rule_w1 hD q0_eq rule_text0 fT_free0 (hI _ (Or.inl (List.mem_singleton_self _)))
    fun e m hg a ha => left0 hD e m a hg ha

/-! ## The account -/

noncomputable def tiedIdx : List Nat := fnText.map (·.index) ++ consText.map (·.index) ++ [104]

/-- **The account**: the function equations, the constructor sentences and the rule sentences are
sentences of the user module, each once and none in two classes, with the sizes of the three
classes and of the rest (not tied here). -/
theorem account : tiedIdx.Nodup ∧ tiedIdx.all (fun i => (U.all.map (·.index)).contains i) = true ∧
    (U.all.map (·.index)).Nodup ∧
    (fnText.length, consText.length, [104].length, U.all.length - tiedIdx.length) = (29, 37, 1, 84) := by decide +kernel

/-! ## The facts the deciders leave -/

theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok

def callOrder : List Nat := []

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

/-- **The premises of the derivations**: every function equation as written, Γ's rule items (the
reading of the rule sentence 104, each a consequence of it by `rule_from_text`), and the families. -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- **`Pre` with the step's closure has a model, for every H.** -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) :=
  TiePair.pre_model (shapeH H) (consistent H)

theorem readsConfined_c : c.readsConfined = false := by decide +kernel
theorem hrcH (H : HookParams) : (cH H).readsConfined = false := (Semantics.readsConfined_withHooks c H).trans readsConfined_c

/-- The configuration with `it` of sort Exp in the k cell and the counter at 0. -/
def cfg (it : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor 383 [.ctor kseq [.inj 32 Srt.kitem it, .ctor dotk []]], .ctor counterLabel [.dv Srt.int (.int 0)]]

/-- A step the rules' check accepts on the data, as a consequence of `Pre H`: `⟦x⟧ → •⟦y⟧`. -/
theorem step_from {x y : Config c} (h : c.rules.any (fun r => Cert.checkStep c 50 r x.val y.val) = true) (H : HookParams) :
    Pre H ⊧ (den (cH H) x.val ⇒ KoreAML.sNext (den (cH H) y.val)) :=
  TiePair.cut (shapeH H) (sound_at_step _ (coreOKH H) (hrcH H) _ _ (TieRuleLhs.step_everyH hok hsr hmr noRaw h H))

theorem clausesFixed_c : c.clausesFixed = true := by decide +kernel
theorem agreeObligations_c : c.agreeObligations = [] := by decide +kernel
theorem asideFree_c : c.asideFree = true := by decide +kernel

/-- A configuration `stuckCheck` accepts on the data has no successor, as a consequence of `Pre H`
with the step's closure: `⟦x⟧ → ◦⊥`. -/
theorem stuck_from {x : Config c} (h : Cert.stuckCheck c 50 x.val = true) (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) x.val ⇒ KoreAML.allNext (KoreAML.disjList (([] : List GroundTerm).map (den (cH H))))) :=
  TiePair.cutStep (shapeH H) (complete_at_step _ (coreOKH H) (hrcH H) (TieRuleLhs.cfgH noRaw x H)
    (stepDecided_of_fnHyp (coreOKH H) (fnHypH H) _) []
    fun y hy => absurd hy (TieRuleLhs.stuck_everyH hok hsr hmr noRaw clausesFixed_c agreeObligations_c asideFree_c h H y))

def CDA : Config c := ⟨cfg (.ctor 387 [.ctor 388 [.ctor 385 [], .ctor 386 []]]), by decide +kernel⟩
def CDB : Config c := ⟨cfg (.ctor 387 [.ctor 388 [.ctor 386 [], .ctor 386 []]]), by decide +kernel⟩
def CDX : Config c := ⟨cfg (.ctor 387 [.ctor 388 [.ctor 386 [], .ctor 385 []]]), by decide +kernel⟩
def A : Config c := ⟨cfg (.ctor 385 []), by decide +kernel⟩

/-- **`c(d(a, b))` steps to `a`, derived from `Pre`**, for every H. -/
theorem ex_a (H : HookParams) : Pre H ⊧ (den (cH H) CDA.val ⇒ KoreAML.sNext (den (cH H) A.val)) :=
  step_from (x := CDA) (y := A) (by decide +kernel) H

/-- **`c(d(b, b))` steps to `a`, derived from `Pre`**, for every H. -/
theorem ex_b (H : HookParams) : Pre H ⊧ (den (cH H) CDB.val ⇒ KoreAML.sNext (den (cH H) A.val)) :=
  step_from (x := CDB) (y := A) (by decide +kernel) H

/-- **`c(d(b, a))` has no successor, derived from `Pre` with the step's closure**, for every H. -/
theorem ex_x (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) CDX.val ⇒ KoreAML.allNext (KoreAML.disjList (([] : List GroundTerm).map (den (cH H))))) :=
  stuck_from (x := CDX) (by decide +kernel) H

end KCore.NoteExVar

#print axioms KCore.NoteExVar.wf_defn
#print axioms KCore.NoteExVar.defs_attrsAgree
#print axioms KCore.NoteExVar.account
#print axioms KCore.NoteExVar.shape
#print axioms KCore.NoteExVar.fns_entailed
#print axioms KCore.NoteExVar.cons_entailed
#print axioms KCore.NoteExVar.rule_text0
#print axioms KCore.NoteExVar.rule_from_text
#print axioms KCore.NoteExVar.consistent
#print axioms KCore.NoteExVar.pre_model
#print axioms KCore.NoteExVar.ex_a
#print axioms KCore.NoteExVar.ex_b
#print axioms KCore.NoteExVar.ex_x
