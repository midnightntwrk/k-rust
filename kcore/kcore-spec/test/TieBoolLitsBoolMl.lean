/-
  The Bool literals from the text's own sentences, on a text that writes none of module INT-KORE's:
  `f2-examples/e3-eq-exists-bool-ml.kompile.kore`.
  Run from the package root: `lake env lean -j1 test/TieBoolLitsBoolMl.lean`.

  | sentence | index |
  |---|---|
  | `rule isK(K) => true` | 149 |
  | functional sentence of `isK` | 71 |
  | `rule notBool true => false` | 165 |
  | functional sentence of `notBool_` | 82 |

  `sents`: each is the library's pattern of that sentence (kernel). `PreLits H`: the four, K's
  G-nonempty item (an item of the text's signature, `kNonempty_text`; `ΓSig` does not hold it) and
  `ΓSig (cH H)`. `lit`: in a model of `PreLits H`, for every H, each of `true` and `false` denotes
  one element, an element of Bool. At an element k of K, the sort variable at K: `isK(k)` is one
  element v of Bool among Bool's (71) and agrees with `true` on Bool (149); `notBool(v)` is one
  element of Bool among Bool's (82) and agrees with `false` on Bool (165); a literal holds nothing
  outside Bool by its arity item in `ΓSig`. That the two elements differ is not stated here.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieBoolLitsBoolMl

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-eq-exists-bool-ml.kompile.kore"
definition_of defn from "f2-examples/e3-eq-exists-bool-ml.kompile.kore"
user_axioms U from "f2-examples/e3-eq-exists-bool-ml.kompile.kore" module "E3-EQ-EXISTS-BOOL-ML"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-- The four sentences are sentences of the user module, at these indices. -/
theorem idx : [U.ax149, U.ax71, U.ax165, U.ax82].map (·.index) = [149, 71, 165, 82] ∧
    [149, 71, 165, 82].all (fun i => (U.all.map (·.index)).contains i) = true := by
  constructor <;> decide +kernel

/-- **Each of the four is the library's pattern of its sentence** (kernel). -/
theorem sents :
    (trS U.ax149).pat = TieReqBool.sentPat TieReqBool.isKTrueAx ∧
    (trS U.ax71).pat = TieReqBool.sentPat (TieReqBool.fnl1Ax "LblisK" "K") ∧
    (trS U.ax165).pat = TieReqBool.sentPat TieReqBool.notTrueFalseAx ∧
    (trS U.ax82).pat = TieReqBool.sentPat (TieReqBool.fnl1Ax "LblnotBool'Unds'" "Bool") := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

noncomputable def litSents : List P :=
  [(trS U.ax149).pat, (trS U.ax71).pat, (trS U.ax165).pat, (trS U.ax82).pat]

/-- K's G-nonempty item. -/
def kNonempty : P := (nonemptyItem ⟨"SortK", [], false⟩).pat

/-- It is an item of the text's signature. -/
theorem kNonempty_text : ((Theory.ofDefinition kore).signature.map (·.pat)).contains kNonempty = true := by
  decide +kernel

/-- The four sentences, K's G-nonempty item, and the signature. -/
noncomputable abbrev PreLits (H : HookParams) : Premises KoreAML.Sym :=
  TiePair.Texts litSents ∪ (fun φ => φ = kNonempty) ∪ ΓSig (cH H)

theorem k_name (H : HookParams) : (cH H).sortName Srt.k = "K" :=
  (by decide +kernel : c.sortName Srt.k = "K")
theorem k_numbered (H : HookParams) : Srt.k < nRegSorts + (cH H).sortNames.length :=
  Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)

theorem den_lit (H : HookParams) (b : Bool) :
    den (cH H) (KCore.bool b) = TieReqBool.litP (if b then "true" else "false") := by
  show den c (KCore.bool b) = _; cases b <;> decide +kernel

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **Each of `true` and `false` denotes one element, an element of Bool**, in a model of the four
sentences, K's G-nonempty item and the signature, for every H. -/
theorem lit (H : HookParams) (hI : I ⊧ᴵP PreLits H) (b : Bool) (e : Valuation M) :
    ∃ y, (∀ m, (den (cH H) (KCore.bool b)).interpret I e m ↔ m = y) ∧ (inhOf TieFRRead.boolP).interpret I e y := by
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨s1, s2, s3, s4⟩ := sents
  have hT : ∀ φ ∈ litSents, I ⊧ᴵ φ := fun φ hφ => hI φ (Or.inl (Or.inl (Or.inl hφ)))
  obtain ⟨aF, aT, hF, hTr, hiF, hiT⟩ := TieReqBool.boolLits_of_bool_text_sig hD hSig (k_numbered H) (k_name H)
    (hI _ (Or.inl (Or.inr rfl)))
    (s1 ▸ hT _ (.head _)) (s2 ▸ hT _ (.tail _ (.head _))) (s3 ▸ hT _ (.tail _ (.tail _ (.head _))))
    (s4 ▸ hT _ (.tail _ (.tail _ (.tail _ (.head _))))) e
  rw [den_lit]
  cases b
  · exact ⟨aF, hF, hiF⟩
  · exact ⟨aT, hTr, hiT⟩

end

end KCore.TieBoolLitsBoolMl

#print axioms KCore.TieBoolLitsBoolMl.idx
#print axioms KCore.TieBoolLitsBoolMl.sents
#print axioms KCore.TieBoolLitsBoolMl.kNonempty_text
#print axioms KCore.TieBoolLitsBoolMl.lit
#print axioms KCore.TieReqBool.boolLits_of_bool_text_sig
