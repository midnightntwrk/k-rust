/-
  `kore.k`'s order `cmpF` on encoded values, and the canonical form `enc` writes
  (`KcoreSpec/KKEncCanon.lean`). The examples show why the order laws are stated on terms of one
  shape (`EncShape κ`) and on encodings of values sorted in one semantics, not on every term.
  Run from the package root: `lake env lean test/KKEncCanon.lean`.
-/
import KcoreSpec.KKEncCanon

set_option autoImplicit false

namespace KCore.KK.TestEncCanon

open KCore KCore.KK

#check @Canon
#check @enc_canonical
#check @cmpF_eq_zero_iff
#check @cmpF_trans
#check @cmpF_swap
#check @cmpF_range
#check @cmpF_self
#check @EncShape
#check @encKind
#check @enc_shape
#check @cmpF_eq_zero_iff_shape
#check @cmpF_trans_shape
#check @sortK_perm
#check @sortK_sorted

/-- A map entry and an element compare 0 and are different terms. -/
example : cmpF (.kv (.iv 1) (.iv 2)) (.el (.iv 1)) = 0 := by decide

/-- A set and a list of one sort number compare 0: `cmpF` ignores a collection's kind. -/
example : cmpF (.co .set 7 []) (.co .list 7 []) = 0 := by decide

/-- Two different terms of a form `tagF` ranks 6 compare 0. -/
example : cmpF (.vr 0) (.vr 1) = 0 := by decide

/-- Transitivity fails on terms that mix entries and elements in collections of one sort number:
`t < u < w` and `w < t`. -/
example :
    let t : T := .co .map 1 [.kv (.iv 1) (.iv 0)]
    let u : T := .co .set 1 [.el (.iv 0), .iv 0]
    let w : T := .co .map 1 [.kv (.iv 0) (.iv 0), .iv 0, .iv 0]
    cmpF t u = -1 ∧ cmpF u w = -1 ∧ cmpF t w = 1 := by decide

/-- A list keeps its order, which need not be `ckeyF`'s: `Canon` asks no order of a list. -/
example : ckeyF (.el (.bv true)) (.el (.iv 7)) = some 1 := by decide

/-- Two different Floats are written `bot` and compare 0: `cmpF_eq_zero_iff` needs `litsV`. -/
example : enc (.dv Srt.float (.float 53 11 0)) = enc (.dv Srt.float (.float 53 11 1)) := rfl

#print axioms Canon
#print axioms enc_canonical
#print axioms cmpF_eq_zero_iff
#print axioms cmpF_trans
#print axioms cmpF_swap
#print axioms cmpF_range
#print axioms cmpF_self
#print axioms enc_shape
#print axioms sortK_perm
#print axioms sortK_sorted

end KCore.KK.TestEncCanon
