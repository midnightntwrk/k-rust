/-
  The tie (C14) of the reading `bottomAsEnsures` on its construct fixture e3-ml-eq-rhs-bottom:
  `rule f(X) => #Bottom requires X <Int 0` beside `rule f(X) => X [owise]`, an equation whose right
  side is `⊥`, read as the right side X with the `ensures` false.
  The text is `f2-examples/mleqbot.kompile.kore` (the kompiled text of
  `test/constructs/fixtures/e3-ml-eq-rhs-bottom`, as test/Guards.lean's `DevBot` reads it).
  Run from the package root: `lake env lean -j1 test/NoteBotEns.lean`. Every statement is on the
  literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  Layer 1. `wf_defn`, `coreOK` (kernel); `defs_attrsAgree`; `account`: the function equations and
  the constructor sentences are sentences of the user module, apart, with the count of the rest.

  Layer 2. The equation (sentence 201) is the one function equation whose translation is not Γ's
  item pattern for pattern: kompile writes the right side `\and{Int}(\bottom{Int}(), \top{Int}())`
  and Γ's item `\and{Int}(X, \equals{Bool, Int}(false, true))` (the clause's right side and its
  `ensures` false). The sentence is Γ's item with that right side written
  `\and{Int}(\bottom{Int}(), \top{Int}())` (`w_text`, up to the indices of its variables; kernel).
  The two right sides hold no element of Int where the values `false` and `true` of Bool are two
  elements, which the families state (`ΓDomains`: a value is one element of its sort, distinct
  values of Bool share none; `ΓSig` for the sorts and `\ceil`), not the sentence: in a model of
  definedness, of `ΓSig` and of `ΓDomains` the sentence and the item hold together (`w_iff`,
  `TieRhs.rhsMap_iff` with `TieRhs.botTop_agree` and `TieRhs.ensFalse_empty`). The class is
  *entailed*: Γ entails every function equation as written (`fns_entailed`, for every H), and the
  sentence with the two families entails the item (`w1`). The other function equations (the
  `[owise]` equation 200 and the sort predicates') are Γ's items (`shape`).
  Constructor sentences: `cons_entailed`. `consistent` for every H.

  The expectations (C7 form (a), from sentences): `PreW H` is every equation of `f` as written
  (sentences 201 and 200 among them), Γ's rule items and the families; it has a model
  (`preW_model`). `f_neg1`: `f(-1)` has no value: sentence 201 states `f(-1) = ⊥ ∧ ⊤` where
  `-1 <Int 0` is `true` (the graph of `<Int`, a family). `f_2`: `f(2) = 2`, by the `[owise]`
  sentence 200, whose pattern holds the negation of sentence 201's premise (`2 <Int 0` is `false`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.NoteBotEns

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/mleqbot.kompile.kore"
definition_of defn from "f2-examples/mleqbot.kompile.kore"
user_axioms U from "f2-examples/mleqbot.kompile.kore" module "E3-ML-EQ-RHS-BOTTOM"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-ML-EQ-RHS-BOTTOM")

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

theorem fnText_index : fnText.map (·.index) = [201, 200, 219, 227, 226, 225, 224, 231, 230, 233, 232, 229, 228, 208, 207, 218, 217, 214, 213, 216, 215, 221, 220, 223, 222, 210, 209, 212, 211] := by
  decide +kernel

kernel_rfl fnText_W : fnText[0]? = some U.ax201

/-! ### The equation whose right side is `⊥` -/

/-- Γ's axiom of `f`'s equation. -/
noncomputable def aW : Kore.Axiom := ((TiePair.fnAxioms c)[0]?).getD ⟨[], .top KoreAML.R, []⟩

theorem aW_at : (TiePair.fnAxioms c)[0]? = some aW := by decide +kernel

/-- Γ's item of it. -/
noncomputable def gW : P := (trAxiom [] [] ⟨0, "kernel", aW⟩).pat

theorem gW_at : (TiePair.gammaPats c)[0]? = some gW := TiePair.gammaPats_at aW_at

/-- Its parts `\implies{R}(prem, \equals{s, R'}(l, r))`. -/
noncomputable def pW : Kore.KSort × Kore.Pattern × Kore.KSort × Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRhs.eqParts aW.pattern).getD (KoreAML.R, .top KoreAML.R, KoreAML.R, KoreAML.R, .top KoreAML.R, .top KoreAML.R)

kernel_rfl pW_eq : TieRhs.eqParts aW.pattern = some pW
kernel_rfl pW_sort : pW.2.2.1 = KoreAML.srt "Int"

theorem aW_pattern : aW.pattern = .implies pW.1 pW.2.1 (.equals pW.2.2.1 pW.2.2.2.1 pW.2.2.2.2.1 pW.2.2.2.2.2) :=
  TieRhs.eqParts_eq pW_eq

/-- A conjunction of two, read as its first part. -/
def andFirst : Kore.Pattern → Kore.Pattern
  | .and _ [x, _] => x
  | p => p

-- Γ's right side is `\and{Int}(x, \equals{Bool, Int}(false, true))`: the clause's right side and
-- the `ensures` false.
kernel_rfl qW_eq : pW.2.2.2.2.2 = .and pW.2.2.1 [andFirst pW.2.2.2.2.2, TieRhs.ensFalse pW.2.2.1]

/-- Γ's axiom with its right side written `\and{Int}(\bottom{Int}(), \top{Int}())`. -/
noncomputable def aT : Kore.Axiom := TieRhs.rhsMap TieRhs.botTop aW

theorem aT_table : tableOf aT.sortVars aT.pattern = tableOf aW.sortVars aW.pattern := by decide +kernel
theorem aT_free : (aT.sortVars.map sortVarKey ++ freeOf [] aT.pattern).eraseDups =
    (aW.sortVars.map sortVarKey ++ freeOf [] aW.pattern).eraseDups := by decide +kernel
theorem aT_sort : sortOf [] aT.pattern = sortOf [] aW.pattern := by decide +kernel

/-- **The text's sentence 201 is Γ's item with its right side written
`\and{Int}(\bottom{Int}(), \top{Int}())`** (up to the indices of its variables; kernel). -/
theorem w_text : TiePair.sameB (trAxiom [] [] ⟨0, "kernel", aT⟩).pat (trS U.ax201).pat = true := by decide +kernel

/-- **The sentence is not Γ's item pattern for pattern.** -/
theorem w_differs : gW ≠ (trS U.ax201).pat := by decide +kernel

theorem sortOf_false (H : HookParams) : (cH H).sortOf (KCore.bool false) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem sortOf_true (H : HookParams) : (cH H).sortOf (KCore.bool true) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem den_false (H : HookParams) : den (cH H) (KCore.bool false) = KoreAML.sym (.dv "false") ⬝ KoreAML.sym (.sort "SortBool") := by
  show den c (KCore.bool false) = _; decide +kernel
theorem den_true (H : HookParams) : den (cH H) (KCore.bool true) = KoreAML.sym (.dv "true") ⬝ KoreAML.sym (.sort "SortBool") := by
  show den c (KCore.bool true) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 201 and Γ's item hold together in a model of definedness, of the signature and of
the domains**, for every H: the two right sides hold no element of Int there. -/
theorem w_iff (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (hDom : I ⊧ᴵP ΓDomains (cH H)) :
    (I ⊧ᴵ (trS U.ax201).pat) ↔ (I ⊧ᴵ gW) := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σ, hσ1, hσ2⟩ := TieRhs.sortSing_sig hD hSig (int_numbered H)
  rw [int_name] at hσ1
  exact (TiePair.sameB_iff w_text).trans
    (TieRhs.rhsMap_iff hD aW_pattern
      (fun e b _ => TieRhs.botTop_agree hD qW_eq (by rw [pW_sort, trSort_srt]; rfl) e
        (fun b' => TieRhs.ensFalse_empty hD hSig hDom (sortOf_false H) (sortOf_true H) (den_false H) (den_true H)
          (by rw [pW_sort, trSort_srt]; exact hσ1) hσ2 b') b)
      aT_table aT_free aT_sort)

/-- **W1**: the sentence, with the signature and the domains, entails Γ's item, for every H. -/
theorem w1 (H : HookParams) : (TiePair.Texts [(trS U.ax201).pat] ∪ ΓSig (cH H) ∪ ΓDomains (cH H)) ⊧ gW :=
  fun {M} _ {I} hI =>
    (w_iff H (TiePair.defOK_texts fun φ hφ => hI φ (Or.inl (Or.inl hφ))) (fun φ hφ => hI φ (Or.inl (Or.inr hφ)))
      (fun φ hφ => hI φ (Or.inr hφ))).mp (hI _ (Or.inl (Or.inl (Or.inl (List.mem_singleton_self _)))))

/-- The premise set's equations with Γ's item for sentence 201. -/
noncomputable def textPats : List P := (fnText.map (trS · |>.pat)).set 0 gW

/-- **Each of Γ's equations but item 0 is the translation of its text sentence** (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- **E for every function equation, sentence 201 among them**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp had
  by_cases hJ : j = 0
  · subst hJ
    rw [fnText_W] at hj; cases hj
    have hg : gW ∈ TiePair.gammaPats (cH H) := by
      rw [TiePair.gammaPats_withHooks]; exact List.mem_of_getElem? gW_at
    obtain ⟨it, hit, hit'⟩ := List.mem_map.mp hg
    exact (w_iff H (defOK hI) (fun φ hφ => sat_sig hI hφ) (fun φ hφ => sat_dom hI hφ)).mpr
      (hit' ▸ hI _ (TiePair.mem_Γ_fns (Or.inl ⟨it, hit, rfl⟩)))
  · refine TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (i := j) ?_) hI
    unfold textPats
    rw [List.getElem?_set_ne (Ne.symm hJ), List.getElem?_map, hj]; rfl

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

/-! ## The expectations (C7 form (a), from sentences) -/

noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- Every function equation as written. -/
noncomputable def writtenPats : List P := fnText.map (trS · |>.pat)

/-- **The premises of the derivations**: every equation of `f` as written (sentence 201 among
them), Γ's rule items (none: the text has no rule), and the families. -/
noncomputable abbrev PreW (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) writtenPats

/-- A model of `PreW H` is a model of `Pre H`: sentence 201 with the families gives Γ's item (`w1`). -/
theorem pre_of_written {H : HookParams} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP PreW H) : I ⊧ᴵP Pre H := fun φ hφ => by
  rcases hφ with ((hφ | ⟨x, rfl⟩) | hφ) | hφ
  · rcases List.mem_or_eq_of_mem_set hφ with hφ | rfl
    · exact hI _ (Or.inl (Or.inl (Or.inl hφ)))
    · refine w1 H (fun ψ hψ => ?_)
      rcases hψ with (hψ | hψ) | hψ
      · rcases hψ with hψ | ⟨x, rfl⟩
        · rw [List.mem_singleton.mp hψ]
          exact hI _ (Or.inl (Or.inl (Or.inl (by
            unfold writtenPats; exact List.mem_map.mpr ⟨U.ax201, List.mem_of_getElem? fnText_W, rfl⟩))))
        · exact hI _ (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩)))
      · exact hI _ (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl hψ)))))
      · exact hI _ (Or.inr (Or.inl (Or.inl (Or.inr hψ))))
  · exact hI _ (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩)))
  · exact hI _ (Or.inl (Or.inr hφ))
  · exact hI _ (Or.inr hφ)

/-- **`PreW` with the step's closure has a model, for every H**: Γ's model, which satisfies
sentence 201 (`fns_entailed`). -/
theorem preW_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (PreW H ∪ Γstep (cH H)) := by
  obtain ⟨M, hM, I, hI⟩ := consistent H
  have hΓ : I ⊧ᴵP Γ (cH H) := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  refine ⟨M, hM, I, fun φ hφ => ?_⟩
  rcases hφ with (((hφ | ⟨x, rfl⟩) | hφ) | hφ) | hφ
  · unfold writtenPats at hφ
    obtain ⟨ad, had, rfl⟩ := List.mem_map.mp hφ
    exact fns_entailed H ad had hΓ
  · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩))))))))
  · exact hΓ _ (Or.inl (Or.inr hφ))
  · rcases hφ with (((h1 | h1) | h1) | h1) | h1
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h1))))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1))))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1)))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inr h1))))
    · exact hΓ _ (Or.inr h1)
  · exact hI _ (Or.inr hφ)

/-- What `Pre H` entails, `PreW H` entails. -/
theorem written_cut {H : HookParams} {ψ : P} (h : Pre H ⊧ ψ) : PreW H ⊧ ψ :=
  fun hI => h (pre_of_written hI)

noncomputable abbrev fAt (H : HookParams) (n : Int) : P := TiePair.app (cH H) f [int n]

/-- **`f(-1)` has no value, derived from the sentences as written**, for every H: sentence 201
states `f(-1) = ⊥ ∧ ⊤` where `-1 <Int 0` is `true` (the graph of `<Int`, a family: `ΓDomains`). -/
theorem f_neg1 (H : HookParams) : PreW H ⊧ (fAt H (-1) ≡ ⊥) :=
  written_cut (TiePair.noValue (shapeH H) (coreOKH H) (hokH H) (eval_of (k := 10) (by decide +kernel) H) (hfnH H) (hvsH H (-1)))

/-- **`f(2) = 2`, derived from the sentences as written**, for every H: the `[owise]` sentence
200 holds the negation of sentence 201's premise, and `2 <Int 0` is `false` by the graph of `<Int`. -/
theorem f_2 (H : HookParams) : PreW H ⊧ (fAt H 2 ≡ den (cH H) (int 2)) :=
  written_cut (TiePair.value (shapeH H) (coreOKH H) (hokH H) (eval_of (k := 10) (by decide +kernel) H) (hfnH H) (hvsH H 2))

end KCore.NoteBotEns

#print axioms KCore.NoteBotEns.wf_defn
#print axioms KCore.NoteBotEns.defs_attrsAgree
#print axioms KCore.NoteBotEns.account
#print axioms KCore.NoteBotEns.w_text
#print axioms KCore.NoteBotEns.w_iff
#print axioms KCore.NoteBotEns.w1
#print axioms KCore.NoteBotEns.shape
#print axioms KCore.NoteBotEns.fns_entailed
#print axioms KCore.NoteBotEns.cons_entailed
#print axioms KCore.NoteBotEns.consistent
#print axioms KCore.NoteBotEns.preW_model
#print axioms KCore.NoteBotEns.f_neg1
#print axioms KCore.NoteBotEns.f_2
