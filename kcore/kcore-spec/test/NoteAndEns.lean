/-
  The tie (C14) of the reading `andAsEnsures` on its construct fixture e3-ml-eq-rhs-and-pred:
  `rule f(X) => X #And {(X >Int 0) #Equals true}`, an equation whose right side is
  `X ∧ (X >Int 0 = true)`, read as the right side X with the `ensures` `X >Int 0`.
  The text is `f2-examples/mleqand.kompile.kore` (the kompiled text of
  `test/constructs/fixtures/e3-ml-eq-rhs-and-pred`, as test/Guards.lean's `DevAndEns` reads it).
  Run from the package root: `lake env lean -j1 test/NoteAndEns.lean`. Every statement is on the
  literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  Layer 1. `wf_defn`, `coreOK` (kernel); `defs_attrsAgree`; `account`: the function equations and
  the constructor sentences are sentences of the user module, apart, with the count of the rest.

  Layer 2. The equation (sentence 200) is the one function equation whose translation is not Γ's
  item pattern for pattern: kompile writes the right side `\and{Int}(\and{Int}(X, ⌈B⌉), \top{Int}())`
  and Γ's item `\and{Int}(X, ⌈B⌉)` (the clause's right side and `ensures`). The sentence is Γ's
  item with that right side wrapped in `\and{Int}(_, \top{Int}())` (`w_text`, up to the indices of
  its variables; kernel), and the two hold in the same models of definedness (`w_iff`,
  `TieRhs.rhsMap_iff` with `TieRhs.andTop_agree`): the class is *entailed*, and the sentence is
  equivalent to the item, so Γ entails it (`fns_entailed`, every function equation, for every H)
  and it entails the item (`w1`). The other function equations (the sort predicates') are Γ's
  items (`shape`). Constructor sentences: `cons_entailed`. `consistent` for every H.

  The expectations (C7 form (a), from sentences): `PreW H` is every equation of `f` as written
  (sentence 200 among them), Γ's rule items and the families; it has a model (`preW_model`).
  `f_1`: `f(1) = 1`. `f_0`: `f(0)` has no value: the sentence states `f(0) = 0 ∧ (0 >Int 0 = true)`,
  and `0 >Int 0` is `false` by the graph of `>Int` (a family, `ΓDomains`), not `true` (the values
  of Bool are distinct).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.NoteAndEns

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/mleqand.kompile.kore"
definition_of defn from "f2-examples/mleqand.kompile.kore"
user_axioms U from "f2-examples/mleqand.kompile.kore" module "E3-ML-EQ-RHS-AND-PRED"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-ML-EQ-RHS-AND-PRED")

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

theorem fnText_index : fnText.map (·.index) = [200, 218, 226, 225, 224, 223, 230, 229, 232, 231, 228, 227, 207, 206, 217, 216, 213, 212, 215, 214, 220, 219, 222, 221, 209, 208, 211, 210] := by
  decide +kernel

kernel_rfl fnText_W : fnText[0]? = some U.ax200

/-! ### The equation whose right side is written as a conjunction -/

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

/-- Γ's axiom with its right side written `\and{Int}(r, \top{Int}())`. -/
noncomputable def aT : Kore.Axiom := TieRhs.rhsMap TieRhs.andTop aW

theorem aT_table : tableOf aT.sortVars aT.pattern = tableOf aW.sortVars aW.pattern := by decide +kernel
theorem aT_free : (aT.sortVars.map sortVarKey ++ freeOf [] aT.pattern).eraseDups =
    (aW.sortVars.map sortVarKey ++ freeOf [] aW.pattern).eraseDups := by decide +kernel
theorem aT_sort : sortOf [] aT.pattern = sortOf [] aW.pattern := by decide +kernel

/-- **The text's sentence 200 is Γ's item with its right side written `\and{Int}(r, \top{Int}())`**
(up to the indices of its variables; kernel). -/
theorem w_text : TiePair.sameB (trAxiom [] [] ⟨0, "kernel", aT⟩).pat (trS U.ax200).pat = true := by decide +kernel

/-- **The sentence is not Γ's item pattern for pattern.** -/
theorem w_differs : gW ≠ (trS U.ax200).pat := by decide +kernel

/-- **Sentence 200 and Γ's item hold in the same models of definedness.** -/
theorem w_iff {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I) :
    (I ⊧ᴵ (trS U.ax200).pat) ↔ (I ⊧ᴵ gW) :=
  (TiePair.sameB_iff w_text).trans
    (TieRhs.rhsMap_iff hD aW_pattern
      (fun e b hb => TieRhs.andTop_agree hD (by rw [pW_sort, trSort_srt]; rfl) e b hb)
      aT_table aT_free aT_sort)

/-- **W1**: the sentence entails Γ's item, in every model of definedness. -/
theorem w1 : TiePair.Texts [(trS U.ax200).pat] ⊧ gW :=
  fun {M} _ {I} hI => (w_iff (TiePair.defOK_texts hI)).mp (hI _ (Or.inl (List.mem_singleton_self _)))

/-- The premise set's equations with Γ's item for sentence 200. -/
noncomputable def textPats : List P := (fnText.map (trS · |>.pat)).set 0 gW

/-- **Each of Γ's equations but item 0 is the translation of its text sentence** (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- **E for every function equation, sentence 200 among them**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp had
  by_cases hJ : j = 0
  · subst hJ
    rw [fnText_W] at hj; cases hj
    have hg : gW ∈ TiePair.gammaPats (cH H) := by
      rw [TiePair.gammaPats_withHooks]; exact List.mem_of_getElem? gW_at
    obtain ⟨it, hit, hit'⟩ := List.mem_map.mp hg
    exact (w_iff (defOK hI)).mpr (hit' ▸ hI _ (TiePair.mem_Γ_fns (Or.inl ⟨it, hit, rfl⟩)))
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
    (fnText.length, consText.length, U.all.length - tiedIdx.length) = (28, 24, 199) := by decide +kernel

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

/-- **The premises of the derivations**: every equation of `f` as written (sentence 200 among
them), Γ's rule items (none: the text has no rule), and the families. -/
noncomputable abbrev PreW (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) writtenPats

/-- A model of `PreW H` is a model of `Pre H`: sentence 200 gives Γ's item (`w_iff`). -/
theorem pre_of_written {H : HookParams} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP PreW H) : I ⊧ᴵP Pre H := fun φ hφ => by
  rcases hφ with ((hφ | ⟨x, rfl⟩) | hφ) | hφ
  · rcases List.mem_or_eq_of_mem_set hφ with hφ | rfl
    · exact hI _ (Or.inl (Or.inl (Or.inl hφ)))
    · refine w1 (fun ψ hψ => ?_)
      rcases hψ with hψ | ⟨x, rfl⟩
      · rw [List.mem_singleton.mp hψ]
        exact hI _ (Or.inl (Or.inl (Or.inl (by
          unfold writtenPats; exact List.mem_map.mpr ⟨U.ax200, List.mem_of_getElem? fnText_W, rfl⟩))))
      · exact hI _ (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩)))
  · exact hI _ (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩)))
  · exact hI _ (Or.inl (Or.inr hφ))
  · exact hI _ (Or.inr hφ)

/-- **`PreW` with the step's closure has a model, for every H**: Γ's model, which satisfies
sentence 200 (`fns_entailed`). -/
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

/-- **`f(1) = 1`, derived from the sentences as written**, for every H: the sentence's conjunct
`1 >Int 0 = true` holds by the graph of `>Int`. -/
theorem f_1 (H : HookParams) : PreW H ⊧ (fAt H 1 ≡ den (cH H) (int 1)) :=
  written_cut (TiePair.value (shapeH H) (coreOKH H) (hokH H) (eval_of (k := 10) (by decide +kernel) H) (hfnH H) (hvsH H 1))

/-- **`f(0)` has no value, derived from the sentences as written**, for every H: the sentence
states `f(0) = 0 ∧ (0 >Int 0 = true)`, and `0 >Int 0` is `false` by the graph of `>Int` (INT.gt, a
family: `ΓDomains`), which is not `true` (the values of Bool are distinct). -/
theorem f_0 (H : HookParams) : PreW H ⊧ (fAt H 0 ≡ ⊥) :=
  written_cut (TiePair.noValue (shapeH H) (coreOKH H) (hokH H) (eval_of (k := 10) (by decide +kernel) H) (hfnH H) (hvsH H 0))

end KCore.NoteAndEns

#print axioms KCore.NoteAndEns.wf_defn
#print axioms KCore.NoteAndEns.defs_attrsAgree
#print axioms KCore.NoteAndEns.account
#print axioms KCore.NoteAndEns.w_text
#print axioms KCore.NoteAndEns.w_iff
#print axioms KCore.NoteAndEns.w1
#print axioms KCore.NoteAndEns.shape
#print axioms KCore.NoteAndEns.fns_entailed
#print axioms KCore.NoteAndEns.cons_entailed
#print axioms KCore.NoteAndEns.consistent
#print axioms KCore.NoteAndEns.preW_model
#print axioms KCore.NoteAndEns.f_1
#print axioms KCore.NoteAndEns.f_0
