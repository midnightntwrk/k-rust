/-
  Part Sig of the tie (C14) on `f2-examples/e2-cells.kompile.kore`, test/TieE2Cells.lean: the sections
  `--split` puts here, in the tie's namespace. A test file imports no test file, so this one
  repeats the literals and the definitions and facts it reads. Written by
  `test/constructs/tiegen.py e2-cells --split`; run from the package root:
  `lake env lean -j1 test/TieE2CellsSig.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE2Cells

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e2-cells.kompile.kore"
definition_of defn from "f2-examples/e2-cells.kompile.kore"
user_axioms U from "f2-examples/e2-cells.kompile.kore" module "E2-CELLS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-! ## The declarations: `sig_origin` and `decls_entailed`, by ranges -/

/-- `p` holds from `a` on where it holds on the `n` members from `a` and from `a + n` on. -/
theorem tieAllE_range {α : Type} {l : List α} {p : α → Bool} {a n : Nat}
    (h : ((l.drop a).take n).all p = true) (ht : (l.drop (a + n)).all p = true) :
    (l.drop a).all p = true := by
  rw [← List.take_append_drop n (l.drop a), List.all_append, h, List.drop_drop, ht]; rfl

/-- `p` holds of the whole list where it holds from `0` on. -/
theorem tieAllE_whole {α : Type} {l : List α} {p : α → Bool} (h : (l.drop 0).all p = true) :
    l.all p = true := h

/-- The item of Γ's signature is a declaration's item of the text, or a surplus one. -/
noncomputable def sigFrom (it : Item) : Bool :=
  (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it

theorem sigE_0 : (((sigItems c).drop 0).take 34).all sigFrom = true := by decide +kernel
theorem sigE_34 : (((sigItems c).drop 34).take 13).all sigFrom = true := by decide +kernel
theorem sigE_47 : (((sigItems c).drop 47).take 13).all sigFrom = true := by decide +kernel
theorem sigE_60 : (((sigItems c).drop 60).take 13).all sigFrom = true := by decide +kernel
theorem sigE_73 : (((sigItems c).drop 73).take 13).all sigFrom = true := by decide +kernel
theorem sigE_86 : (((sigItems c).drop 86).take 13).all sigFrom = true := by decide +kernel
theorem sigE_99 : (((sigItems c).drop 99).take 13).all sigFrom = true := by decide +kernel
theorem sigE_112 : (((sigItems c).drop 112).take 13).all sigFrom = true := by decide +kernel
theorem sigE_125 : (((sigItems c).drop 125).take 13).all sigFrom = true := by decide +kernel
theorem sigE_138 : (((sigItems c).drop 138).take 13).all sigFrom = true := by decide +kernel
theorem sigE_151 : (((sigItems c).drop 151).take 13).all sigFrom = true := by decide +kernel
theorem sigE_164 : (((sigItems c).drop 164).take 13).all sigFrom = true := by decide +kernel
theorem sigE_177 : (((sigItems c).drop 177).take 13).all sigFrom = true := by decide +kernel
theorem sigE_190 : (((sigItems c).drop 190).take 13).all sigFrom = true := by decide +kernel
theorem sigE_203 : (((sigItems c).drop 203).take 13).all sigFrom = true := by decide +kernel
theorem sigE_216 : (((sigItems c).drop 216).take 13).all sigFrom = true := by decide +kernel
theorem sigE_229 : (((sigItems c).drop 229).take 13).all sigFrom = true := by decide +kernel
theorem sigE_242 : (((sigItems c).drop 242).take 13).all sigFrom = true := by decide +kernel
theorem sigE_255 : (((sigItems c).drop 255).take 13).all sigFrom = true := by decide +kernel
theorem sigE_268 : (((sigItems c).drop 268).take 13).all sigFrom = true := by decide +kernel
theorem sigE_281 : (((sigItems c).drop 281).take 13).all sigFrom = true := by decide +kernel
theorem sigE_294 : (((sigItems c).drop 294).take 13).all sigFrom = true := by decide +kernel
theorem sigE_307 : ((sigItems c).drop 307).all sigFrom = true := by decide +kernel

theorem sig_sizes : (sigItems c).length = 318 := by decide +kernel

/-- **Every item of Γ's signature has its origin**: the item of a declaration of the text, or the
sort constant of a registry sort or the arity of an interpreted hooked symbol that the text does not
declare at that shape. -/
theorem sig_origin : (sigItems c).all (fun it =>
    (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it) = true :=
  tieAllE_whole (p := sigFrom) <|
    tieAllE_range (a := 0) (n := 34) sigE_0 <|
    tieAllE_range (a := 34) (n := 13) sigE_34 <|
    tieAllE_range (a := 47) (n := 13) sigE_47 <|
    tieAllE_range (a := 60) (n := 13) sigE_60 <|
    tieAllE_range (a := 73) (n := 13) sigE_73 <|
    tieAllE_range (a := 86) (n := 13) sigE_86 <|
    tieAllE_range (a := 99) (n := 13) sigE_99 <|
    tieAllE_range (a := 112) (n := 13) sigE_112 <|
    tieAllE_range (a := 125) (n := 13) sigE_125 <|
    tieAllE_range (a := 138) (n := 13) sigE_138 <|
    tieAllE_range (a := 151) (n := 13) sigE_151 <|
    tieAllE_range (a := 164) (n := 13) sigE_164 <|
    tieAllE_range (a := 177) (n := 13) sigE_177 <|
    tieAllE_range (a := 190) (n := 13) sigE_190 <|
    tieAllE_range (a := 203) (n := 13) sigE_203 <|
    tieAllE_range (a := 216) (n := 13) sigE_216 <|
    tieAllE_range (a := 229) (n := 13) sigE_229 <|
    tieAllE_range (a := 242) (n := 13) sigE_242 <|
    tieAllE_range (a := 255) (n := 13) sigE_255 <|
    tieAllE_range (a := 268) (n := 13) sigE_268 <|
    tieAllE_range (a := 281) (n := 13) sigE_281 <|
    tieAllE_range (a := 294) (n := 13) sigE_294 <|
    sigE_307

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

end KCore.TieE2Cells

#check @KCore.TieE2Cells.sig_origin
#print axioms KCore.TieE2Cells.sig_origin
