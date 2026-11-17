/-
  The constructor sentences of kore.k's text as kompile wrote it
  (`examples/ref-kk/RefKk/definition.kore`, user module `KORE`), layer 2 of the tie (C14), on
  the literals `kore` and `defn`. Nothing here reads `Parse.parse` or `emit`. Run from the package
  root: `lake env lean test/TieKkCons.lean`.

  - `consText`: the 234 sentences of the account's classes constructor functional (52), subsort
    (32), injectivity (35) and distinctness (115) (test/TieKk.lean, `classes`), in text order.
  - `cons_checked`: each is a constructor sentence `tieConsB` accepts; `cons_trS`: none reads a
    declaration or an alias. Both decided by ranges of 15 sentences, joined by `tieAll_range`.
  - `cons_entailed` (E): Γ entails each of them, for every H.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKk

open KCore ML Faithful KoreAML

kore_term kore from "examples/ref-kk/RefKk/definition.kore"
definition_of defn from "examples/ref-kk/RefKk/definition.kore"
user_axioms U from "examples/ref-kk/RefKk/definition.kore" module "KORE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The indices of the account's four constructor classes (functional, subsort, injectivity,
distinctness). -/
def consIdx : List Nat :=
  [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
    30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 44, 45, 46, 47, 49, 50, 51, 52, 53, 54, 55, 56, 57,
    58, 59, 60, 76, 77, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136,
    137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156,
    157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176,
    177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196,
    197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217,
    218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 234, 235, 236, 237, 238,
    239, 240, 241, 242, 243, 244, 245, 246, 282, 283, 284, 285, 286, 288, 289, 290, 291, 293, 294, 295,
    296, 297, 298, 299, 302, 303, 304, 305, 306, 307, 308, 309, 310, 312, 313, 314, 315, 316, 317, 318,
    323, 324, 325, 326, 327, 328, 329, 333, 334, 335, 336, 337, 338, 339, 340, 342, 343, 344, 346, 347,
    348, 349]

/-- The sentences of the four classes, in text order. -/
noncomputable def consText : List AxiomDecl := U.all.filter fun ad => consIdx.contains ad.index

/-- The sentence is a constructor sentence `tieConsB` accepts. -/
noncomputable def consP (ad : AxiomDecl) : Bool := tieConsB c ad.ax

/-- The sentence's translation reads no declaration and no alias. -/
noncomputable def consTP (ad : AxiomDecl) : Bool := decide ((trS ad).pat = (trAxiom [] [] ad).pat)

theorem consText_length : consText.length = 234 := by decide +kernel

theorem cons_0 : ((consText.drop 0).take 15).all consP = true := by decide +kernel
theorem consT_0 : ((consText.drop 0).take 15).all consTP = true := by decide +kernel
theorem cons_15 : ((consText.drop 15).take 15).all consP = true := by decide +kernel
theorem consT_15 : ((consText.drop 15).take 15).all consTP = true := by decide +kernel
theorem cons_30 : ((consText.drop 30).take 15).all consP = true := by decide +kernel
theorem consT_30 : ((consText.drop 30).take 15).all consTP = true := by decide +kernel
theorem cons_45 : ((consText.drop 45).take 15).all consP = true := by decide +kernel
theorem consT_45 : ((consText.drop 45).take 15).all consTP = true := by decide +kernel
theorem cons_60 : ((consText.drop 60).take 15).all consP = true := by decide +kernel
theorem consT_60 : ((consText.drop 60).take 15).all consTP = true := by decide +kernel
theorem cons_75 : ((consText.drop 75).take 15).all consP = true := by decide +kernel
theorem consT_75 : ((consText.drop 75).take 15).all consTP = true := by decide +kernel
theorem cons_90 : ((consText.drop 90).take 15).all consP = true := by decide +kernel
theorem consT_90 : ((consText.drop 90).take 15).all consTP = true := by decide +kernel
theorem cons_105 : ((consText.drop 105).take 15).all consP = true := by decide +kernel
theorem consT_105 : ((consText.drop 105).take 15).all consTP = true := by decide +kernel
theorem cons_120 : ((consText.drop 120).take 15).all consP = true := by decide +kernel
theorem consT_120 : ((consText.drop 120).take 15).all consTP = true := by decide +kernel
theorem cons_135 : ((consText.drop 135).take 15).all consP = true := by decide +kernel
theorem consT_135 : ((consText.drop 135).take 15).all consTP = true := by decide +kernel
theorem cons_150 : ((consText.drop 150).take 15).all consP = true := by decide +kernel
theorem consT_150 : ((consText.drop 150).take 15).all consTP = true := by decide +kernel
theorem cons_165 : ((consText.drop 165).take 15).all consP = true := by decide +kernel
theorem consT_165 : ((consText.drop 165).take 15).all consTP = true := by decide +kernel
theorem cons_180 : ((consText.drop 180).take 15).all consP = true := by decide +kernel
theorem consT_180 : ((consText.drop 180).take 15).all consTP = true := by decide +kernel
theorem cons_195 : ((consText.drop 195).take 15).all consP = true := by decide +kernel
theorem consT_195 : ((consText.drop 195).take 15).all consTP = true := by decide +kernel
theorem cons_210 : ((consText.drop 210).take 15).all consP = true := by decide +kernel
theorem consT_210 : ((consText.drop 210).take 15).all consTP = true := by decide +kernel
theorem cons_225 : (consText.drop 225).all consP = true := by decide +kernel
theorem consT_225 : (consText.drop 225).all consTP = true := by decide +kernel

/-- Each of the 234 is a constructor sentence Γ's constructor items entail (`tieConsB`). -/
theorem cons_checked : consText.all consP = true :=
  tieAll_whole (p := consP) <|
    tieAll_range (a := 0) (n := 15) cons_0 <|
    tieAll_range (a := 15) (n := 15) cons_15 <|
    tieAll_range (a := 30) (n := 15) cons_30 <|
    tieAll_range (a := 45) (n := 15) cons_45 <|
    tieAll_range (a := 60) (n := 15) cons_60 <|
    tieAll_range (a := 75) (n := 15) cons_75 <|
    tieAll_range (a := 90) (n := 15) cons_90 <|
    tieAll_range (a := 105) (n := 15) cons_105 <|
    tieAll_range (a := 120) (n := 15) cons_120 <|
    tieAll_range (a := 135) (n := 15) cons_135 <|
    tieAll_range (a := 150) (n := 15) cons_150 <|
    tieAll_range (a := 165) (n := 15) cons_165 <|
    tieAll_range (a := 180) (n := 15) cons_180 <|
    tieAll_range (a := 195) (n := 15) cons_195 <|
    tieAll_range (a := 210) (n := 15) cons_210 <|
    cons_225

/-- None of the 234 reads a declaration or an alias: its translation with the text's declarations
is its translation with none. -/
theorem cons_trS : consText.all consTP = true :=
  tieAll_whole (p := consTP) <|
    tieAll_range (a := 0) (n := 15) consT_0 <|
    tieAll_range (a := 15) (n := 15) consT_15 <|
    tieAll_range (a := 30) (n := 15) consT_30 <|
    tieAll_range (a := 45) (n := 15) consT_45 <|
    tieAll_range (a := 60) (n := 15) consT_60 <|
    tieAll_range (a := 75) (n := 15) consT_75 <|
    tieAll_range (a := 90) (n := 15) consT_90 <|
    tieAll_range (a := 105) (n := 15) consT_105 <|
    tieAll_range (a := 120) (n := 15) consT_120 <|
    tieAll_range (a := 135) (n := 15) consT_135 <|
    tieAll_range (a := 150) (n := 15) consT_150 <|
    tieAll_range (a := 165) (n := 15) consT_165 <|
    tieAll_range (a := 180) (n := 15) consT_180 <|
    tieAll_range (a := 195) (n := 15) consT_195 <|
    tieAll_range (a := 210) (n := 15) consT_210 <|
    consT_225

theorem ovls_nil : c.ovls = [] := by decide +kernel
theorem subsorts_irrefl : c.subsorts.all (fun p => p.1 != p.2) = true := by decide +kernel

/-- **E for the constructor sentences**: Γ entails each of the 234, for every H. -/
theorem cons_entailed (H : HookParams) : ∀ ad ∈ consText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  rw [of_decide_eq_true (List.all_eq_true.mp cons_trS ad had : consTP ad = true)]
  haveI : OvlOK (cH H) := .of_nil ovls_nil subsorts_irrefl
  exact tieCons_entailed (c := cH H) (a := ad.ax)
    ((tieConsB_withHooks c H ad.ax).trans (List.all_eq_true.mp cons_checked ad had : consP ad = true)) ad.index ad.module hI

end KCore.TieKk

#check @KCore.TieKk.cons_entailed
#print axioms KCore.TieKk.cons_entailed
