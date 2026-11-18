/-
  The converse for Γ's signature (C14, layer 1) on kore.k's text as kompile wrote it
  (`examples/ref-kk/RefKk/definition.kore`), on the literals `kore` and `defn`. Nothing here reads
  `Parse.parse` or `emit`. Run from the package root: `lake env lean test/TieKkSig.lean`.

  - `sig_origin`: each of the 355 items of `sigItems c` is the item of a declaration of the text
    (`Theory.ofDefinition kore`'s signature, 420 items), or is about a registry name the text does
    not declare at that shape (`surplusItem`).

  Decided by ranges of the items (`sig_a`), each its own kernel decision, joined by
  `tieAll_range`; a surplus item is counted twice a declared one (`surplusItem` searches the
  registry), and a range holds at most 25 declared items or 12 surplus ones. Items
  9 to 10, 13 to 17, 22 to 30, 274 to 298, 323 to 351 are surplus; the other 285 are declared.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKk

open KCore ML Faithful KoreAML

kore_term kore from "examples/ref-kk/RefKk/definition.kore"
definition_of defn from "examples/ref-kk/RefKk/definition.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The item of Γ's signature is a declaration's item of the text, or a surplus one. -/
noncomputable def sigFrom (it : Item) : Bool :=
  (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it

theorem sig_0 : (((sigItems c).drop 0).take 18).all sigFrom = true := by decide +kernel
theorem sig_18 : (((sigItems c).drop 18).take 16).all sigFrom = true := by decide +kernel
theorem sig_34 : (((sigItems c).drop 34).take 25).all sigFrom = true := by decide +kernel
theorem sig_59 : (((sigItems c).drop 59).take 25).all sigFrom = true := by decide +kernel
theorem sig_84 : (((sigItems c).drop 84).take 25).all sigFrom = true := by decide +kernel
theorem sig_109 : (((sigItems c).drop 109).take 25).all sigFrom = true := by decide +kernel
theorem sig_134 : (((sigItems c).drop 134).take 25).all sigFrom = true := by decide +kernel
theorem sig_159 : (((sigItems c).drop 159).take 25).all sigFrom = true := by decide +kernel
theorem sig_184 : (((sigItems c).drop 184).take 25).all sigFrom = true := by decide +kernel
theorem sig_209 : (((sigItems c).drop 209).take 25).all sigFrom = true := by decide +kernel
theorem sig_234 : (((sigItems c).drop 234).take 25).all sigFrom = true := by decide +kernel
theorem sig_259 : (((sigItems c).drop 259).take 8).all sigFrom = true := by decide +kernel
theorem sig_267 : (((sigItems c).drop 267).take 16).all sigFrom = true := by decide +kernel
theorem sig_283 : (((sigItems c).drop 283).take 12).all sigFrom = true := by decide +kernel
theorem sig_295 : (((sigItems c).drop 295).take 21).all sigFrom = true := by decide +kernel
theorem sig_316 : (((sigItems c).drop 316).take 16).all sigFrom = true := by decide +kernel
theorem sig_332 : (((sigItems c).drop 332).take 12).all sigFrom = true := by decide +kernel
theorem sig_344 : ((sigItems c).drop 344).all sigFrom = true := by decide +kernel

/-- **Every item of Γ's signature has its origin**: it is the item of a declaration of the text,
or it states the sort constant of a registry sort or the arity of an interpreted hooked symbol
that the text does not declare at that shape. -/
theorem sig_origin : (sigItems c).all (fun it =>
    (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it) = true :=
  tieAll_whole (p := sigFrom) <|
    tieAll_range (a := 0) (n := 18) sig_0 <|
    tieAll_range (a := 18) (n := 16) sig_18 <|
    tieAll_range (a := 34) (n := 25) sig_34 <|
    tieAll_range (a := 59) (n := 25) sig_59 <|
    tieAll_range (a := 84) (n := 25) sig_84 <|
    tieAll_range (a := 109) (n := 25) sig_109 <|
    tieAll_range (a := 134) (n := 25) sig_134 <|
    tieAll_range (a := 159) (n := 25) sig_159 <|
    tieAll_range (a := 184) (n := 25) sig_184 <|
    tieAll_range (a := 209) (n := 25) sig_209 <|
    tieAll_range (a := 234) (n := 25) sig_234 <|
    tieAll_range (a := 259) (n := 8) sig_259 <|
    tieAll_range (a := 267) (n := 16) sig_267 <|
    tieAll_range (a := 283) (n := 12) sig_283 <|
    tieAll_range (a := 295) (n := 21) sig_295 <|
    tieAll_range (a := 316) (n := 16) sig_316 <|
    tieAll_range (a := 332) (n := 12) sig_332 <|
    sig_344

/-- The counts: Γ's signature has 355 items, the text's 420. -/
theorem sig_sizes : (sigItems c).length = 355 ∧ (Theory.ofDefinition kore).signature.length = 420 := by
  decide +kernel

end KCore.TieKk

#check @KCore.TieKk.sig_origin
#print axioms KCore.TieKk.sig_origin
