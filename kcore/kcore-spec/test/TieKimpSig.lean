/-
  The converse for Γ's signature (C14, layer 1) on kimp's text as kompile wrote it
  (`examples/ref-kimp/RefKimp/definition.kore`), on the literals `kore` and `defn`. Nothing here
  reads `Parse.parse` or `emit`. Run from the package root: `lake env lean test/TieKimpSig.lean`.

  - `sig_origin`: each of the 263 items of `sigItems c` is the item of a declaration of the text
    (`Theory.ofDefinition kore`'s signature, 240 items), or is about a registry name the text does
    not declare at that shape (`surplusItem`).

  One kernel decision of the statement exceeds 12 GiB. It is decided by ranges of the items
  (`sig_a`: the items from `a`, as many as the next range's start says), each its own decision, and
  joined by `tieAll_range`. The cost of an item is what the kernel evaluates for it: for a declared
  item, the text's signature up to the item's place in it; for a surplus item, `surplusItem`'s
  search through the registry's sorts and interpreted hooked symbols up to its own. So a range of
  surplus items is cut shorter than one of declared items. Items 9, 11 to 17, 21 to 30 (registry
  sorts) and 182 to 259 (interpreted hooked symbols) are surplus; the other 167 are declared.
  test/TieKimpHints.lean prints the places of the surplus items.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKimp

open KCore ML Faithful KoreAML

kore_term kore from "examples/ref-kimp/RefKimp/definition.kore"
definition_of defn from "examples/ref-kimp/RefKimp/definition.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The item of Γ's signature is a declaration's item of the text, or a surplus one. -/
noncomputable def sigFrom (it : Item) : Bool :=
  (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it

theorem sig_0 : (((sigItems c).drop 0).take 31).all sigFrom = true := by decide +kernel
theorem sig_31 : (((sigItems c).drop 31).take 35).all sigFrom = true := by decide +kernel
theorem sig_66 : (((sigItems c).drop 66).take 35).all sigFrom = true := by decide +kernel
theorem sig_101 : (((sigItems c).drop 101).take 35).all sigFrom = true := by decide +kernel
theorem sig_136 : (((sigItems c).drop 136).take 35).all sigFrom = true := by decide +kernel
theorem sig_171 : (((sigItems c).drop 171).take 11).all sigFrom = true := by decide +kernel
theorem sig_182 : (((sigItems c).drop 182).take 13).all sigFrom = true := by decide +kernel
theorem sig_195 : (((sigItems c).drop 195).take 13).all sigFrom = true := by decide +kernel
theorem sig_208 : (((sigItems c).drop 208).take 13).all sigFrom = true := by decide +kernel
theorem sig_221 : (((sigItems c).drop 221).take 13).all sigFrom = true := by decide +kernel
theorem sig_234 : (((sigItems c).drop 234).take 13).all sigFrom = true := by decide +kernel
theorem sig_247 : (((sigItems c).drop 247).take 13).all sigFrom = true := by decide +kernel
theorem sig_260 : ((sigItems c).drop 260).all sigFrom = true := by decide +kernel

/-- **Every item of Γ's signature has its origin**: it is the item of a declaration of the text,
or it states the sort constant of a registry sort or the arity of an interpreted hooked symbol
that the text does not declare at that shape. -/
theorem sig_origin : (sigItems c).all (fun it =>
    (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it) = true :=
  tieAll_whole (p := sigFrom) <|
    tieAll_range (a := 0) (n := 31) sig_0 <|
    tieAll_range (a := 31) (n := 35) sig_31 <|
    tieAll_range (a := 66) (n := 35) sig_66 <|
    tieAll_range (a := 101) (n := 35) sig_101 <|
    tieAll_range (a := 136) (n := 35) sig_136 <|
    tieAll_range (a := 171) (n := 11) sig_171 <|
    tieAll_range (a := 182) (n := 13) sig_182 <|
    tieAll_range (a := 195) (n := 13) sig_195 <|
    tieAll_range (a := 208) (n := 13) sig_208 <|
    tieAll_range (a := 221) (n := 13) sig_221 <|
    tieAll_range (a := 234) (n := 13) sig_234 <|
    tieAll_range (a := 247) (n := 13) sig_247 <|
    sig_260

/-- The counts: Γ's signature has 263 items, the text's 240. -/
theorem sig_sizes : (sigItems c).length = 263 ∧ (Theory.ofDefinition kore).signature.length = 240 := by
  decide +kernel

end KCore.TieKimp

#check @KCore.TieKimp.sig_origin
#print axioms KCore.TieKimp.sig_origin
