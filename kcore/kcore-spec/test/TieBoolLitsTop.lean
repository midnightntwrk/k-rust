/-
  The Bool literals from the text's own sentences, on `f2-examples/e3-ml-req-top.kompile.kore`.
  Run from the package root: `lake env lean -j1 test/TieBoolLitsTop.lean`.

  The text writes no sentence about `\dv{SortBool{}}("true")` alone. It writes three sentences of
  module INT-KORE over element variables and the functional sentences of `_==Int_` and `_=/=Int_`:

  | sentence | index |
  |---|---|
  | INT-KORE.eq-int-true-left: `{K1 ==Int K2 #Equals true} => {K1 #Equals K2}` | 138 |
  | INT-KORE.neq-int-false-left: `{K1 =/=Int K2 #Equals false} => {K1 #Equals K2}` | 133 |
  | INT-KORE.eq-int-false-rigth: `{false #Equals K1 ==Int K2} => #Not({K1 #Equals K2})` | 147 |
  | functional sentence of `_==Int_` | 49 |
  | functional sentence of `_=/=Int_` | 46 |

  `sents`: each is the library's pattern of that sentence (kernel). `PreLits H`: the five, Int's
  G-nonempty item (an item of the text's signature, `intNonempty_text`; `ΓSig` does not hold it) and
  `ΓSig (cH H)`. From `PreLits H`, for every H:
  - `lits`: in a model, Bool is one sort and `false`, `true` denote two elements of it;
  - `true_value`, `false_value`: `ΓDomains`' value items of the two literals (`true_value_mem`,
    `false_value_mem`) are entailed;
  - `bool_dist`: `ΓDomains`' item that the two are apart (`bool_dist_mem`) is entailed.
  At an element n of Int, with both sort variables at Int: `n ==Int n` is one element of Bool among
  Bool's (49) and agrees with `true` on Bool (138); `n =/=Int n` likewise with `false` (46, 133);
  `false` does not agree with `n ==Int n` on Bool (147). A sentence equates its sides among the
  elements of its sort only; that a literal holds nothing outside Bool is its arity item in `ΓSig`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieBoolLitsTop

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-req-top.kompile.kore"
definition_of defn from "f2-examples/e3-ml-req-top.kompile.kore"
user_axioms U from "f2-examples/e3-ml-req-top.kompile.kore" module "E3-ML-REQ-TOP"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-- The five sentences are sentences of the user module, at these indices. -/
theorem idx : [U.ax138, U.ax133, U.ax147, U.ax49, U.ax46].map (·.index) = [138, 133, 147, 49, 46] ∧
    [138, 133, 147, 49, 46].all (fun i => (U.all.map (·.index)).contains i) = true := by
  constructor <;> decide +kernel

/-- **Each of the five is the library's pattern of its sentence** (kernel). -/
theorem sents :
    (trS U.ax138).pat = TieReqBool.sentPat TieReqBool.eqIntTrueLeftAx ∧
    (trS U.ax133).pat = TieReqBool.sentPat TieReqBool.neqIntFalseLeftAx ∧
    (trS U.ax147).pat = TieReqBool.sentPat TieReqBool.eqIntFalseRightAx ∧
    (trS U.ax49).pat = TieReqBool.sentPat (TieReqBool.fnlBoolAx TieReqBool.eqIntName) ∧
    (trS U.ax46).pat = TieReqBool.sentPat (TieReqBool.fnlBoolAx TieReqBool.neqIntName) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

noncomputable def litSents : List P :=
  [(trS U.ax138).pat, (trS U.ax133).pat, (trS U.ax147).pat, (trS U.ax49).pat, (trS U.ax46).pat]

/-- Int's G-nonempty item. -/
def intNonempty : P := (nonemptyItem ⟨"SortInt", [], true⟩).pat

/-- It is an item of the text's signature. -/
theorem intNonempty_text : ((Theory.ofDefinition kore).signature.map (·.pat)).contains intNonempty = true := by
  decide +kernel

/-- The five sentences, Int's G-nonempty item, and the signature. -/
noncomputable abbrev PreLits (H : HookParams) : Premises KoreAML.Sym :=
  TiePair.Texts litSents ∪ (fun φ => φ = intNonempty) ∪ ΓSig (cH H)

theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" :=
  (by decide +kernel : c.sortName Srt.int = "Int")
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)

theorem den_true (H : HookParams) : den (cH H) (KCore.bool true) = tr ⟨[], []⟩ (.dv (srt "Bool") "true") := by
  show den c (KCore.bool true) = _; decide +kernel
theorem den_false (H : HookParams) : den (cH H) (KCore.bool false) = tr ⟨[], []⟩ (.dv (srt "Bool") "false") := by
  show den c (KCore.bool false) = _; decide +kernel

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **Bool is one sort and `false`, `true` denote two elements of it**, in a model of the five
sentences, Int's G-nonempty item and the signature, for every H. -/
theorem lits (H : HookParams) (hI : I ⊧ᴵP PreLits H) (t : VarTable) (e : Valuation M) :
    ∃ σB aF aT, (∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB) ∧ IsSort I σB ∧
      (∀ m, (tr ⟨t, []⟩ (.dv (srt "Bool") "false")).interpret I e m ↔ m = aF) ∧
      (∀ m, (tr ⟨t, []⟩ (.dv (srt "Bool") "true")).interpret I e m ↔ m = aT) ∧
      aF ≠ aT ∧ Inh I σB aF ∧ Inh I σB aT := by
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨s1, s2, s3, s4, s5⟩ := sents
  have hT : ∀ φ ∈ litSents, I ⊧ᴵ φ := fun φ hφ => hI φ (Or.inl (Or.inl (Or.inl hφ)))
  exact TieReqBool.boolLits_of_text_sig hD hSig (int_numbered H) (int_name H)
    (hI _ (Or.inl (Or.inr rfl)))
    (s1 ▸ hT _ (.head _)) (s2 ▸ hT _ (.tail _ (.head _))) (s3 ▸ hT _ (.tail _ (.tail _ (.head _))))
    (s4 ▸ hT _ (.tail _ (.tail _ (.tail _ (.head _)))))
    (s5 ▸ hT _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) t e

end

/-- `ΓDomains`' item that the value `v` of Bool is one element of Bool. -/
noncomputable def valueItem (H : HookParams) (v : GroundTerm) : P :=
  sExists ⟨1⟩ (sortP ((cH H).sortName Srt.bool)) (den (cH H) v ≡ .evar ⟨1⟩)
/-- `ΓDomains`' item that `true` and `false` share no element. -/
noncomputable def boolDist (H : HookParams) : P :=
  ∼(den (cH H) (KCore.bool true) ⋀ den (cH H) (KCore.bool false))

theorem sortOf_bool (H : HookParams) (b : Bool) : (cH H).sortOf (KCore.bool b) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; cases b <;> decide +kernel

theorem true_value_mem (H : HookParams) : ΓDomains (cH H) (valueItem H (KCore.bool true)) :=
  Or.inr (Or.inr (Or.inl ⟨_, _, sortOf_bool H true, rfl⟩))
theorem false_value_mem (H : HookParams) : ΓDomains (cH H) (valueItem H (KCore.bool false)) :=
  Or.inr (Or.inr (Or.inl ⟨_, _, sortOf_bool H false, rfl⟩))
theorem bool_dist_mem (H : HookParams) : ΓDomains (cH H) (boolDist H) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨KCore.bool true, KCore.bool false, Srt.bool,
    (by decide +kernel : (distinctSorts c).contains Srt.bool = true), sortOf_bool H true, sortOf_bool H false,
    by decide, rfl⟩)))

/-- The value item of a literal, from the literal's element. -/
theorem value_of {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (H : HookParams) (hD : DefOK I)
    {v : GroundTerm} {σB a : M} {e : Valuation M}
    (hB : ∀ x, I.evalSymb (.sort "SortBool") x ↔ x = σB) (hv : ∀ m, (den (cH H) v).interpret I e m ↔ m = a)
    (ha : Inh I σB a) (m : M) : (valueItem H v).interpret I e m := by
  unfold valueItem
  rw [interp_sExists]
  refine ⟨a, ?_, ?_⟩
  · rw [interp_member hD, sortName_bool, interp_inhOf_of (S := sortP "Bool") (σ := σB) (fun x => hB x)]
    simp only [Function.update_same]
    exact ha
  · rw [interp_equal hD]
    intro x
    rw [← (den_closed (cH H) v).interp e _ x, hv x, interp_evar]
    simp only [Function.update_same]

/-- **The text entails that `true` is one element of Bool**, for every H. -/
theorem true_value (H : HookParams) : PreLits H ⊧ valueItem H (KCore.bool true) := by
  intro M _ I hI e m
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  obtain ⟨σB, aF, aT, hSB, -, haf, hat, -, hif, hit⟩ := lits H hI [] e
  rw [trSort_srt] at hSB
  exact value_of H hD hSB (by rw [den_true]; exact hat) hit m

/-- **The text entails that `false` is one element of Bool**, for every H. -/
theorem false_value (H : HookParams) : PreLits H ⊧ valueItem H (KCore.bool false) := by
  intro M _ I hI e m
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  obtain ⟨σB, aF, aT, hSB, -, haf, hat, -, hif, hit⟩ := lits H hI [] e
  rw [trSort_srt] at hSB
  exact value_of H hD hSB (by rw [den_false]; exact haf) hif m

/-- **The text entails that `true` and `false` share no element**, for every H. -/
theorem bool_dist (H : HookParams) : PreLits H ⊧ boolDist H := by
  intro M _ I hI e m
  obtain ⟨σB, aF, aT, -, -, haf, hat, hne, -, -⟩ := lits H hI [] e
  unfold boolDist
  rw [interpret_neg, interpret_conj, den_true, den_false]
  rintro ⟨h1, h2⟩
  exact hne (((haf m).mp h2).symm.trans ((hat m).mp h1))

end KCore.TieBoolLitsTop

#print axioms KCore.TieBoolLitsTop.idx
#print axioms KCore.TieBoolLitsTop.sents
#print axioms KCore.TieBoolLitsTop.intNonempty_text
#print axioms KCore.TieBoolLitsTop.lits
#print axioms KCore.TieBoolLitsTop.true_value
#print axioms KCore.TieBoolLitsTop.false_value
#print axioms KCore.TieBoolLitsTop.bool_dist
#print axioms KCore.TieBoolLitsTop.true_value_mem
#print axioms KCore.TieBoolLitsTop.false_value_mem
#print axioms KCore.TieBoolLitsTop.bool_dist_mem
#print axioms KCore.TieReqBool.boolLits_of_text
#print axioms KCore.TieReqBool.boolLits_of_text_sig
#print axioms KCore.TieReqBool.boolTrue_of_text_sig
#print axioms KCore.TieReqBool.boolFalse_of_text_sig
#print axioms KCore.TieReqBool.eqTrue_empty_lits
#print axioms KCore.TieReqBool.ensFalse_empty_lits
