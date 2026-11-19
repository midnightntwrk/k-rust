/-
  Part Sig of the tie (C14) on `f2-examples/rdr-config-deep.kompile.kore`, test/TieRdrConfigDeep.lean: the sections
  `--split` puts here, in the tie's namespace. A test file imports no test file, so this one
  repeats the literals and the definitions and facts it reads. Written by
  `test/constructs/tiegen.py rdr-config-deep --split`; run from the package root:
  `lake env lean -j1 test/TieRdrConfigDeepSig.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRdrConfigDeep

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/rdr-config-deep.kompile.kore"
definition_of defn from "f2-examples/rdr-config-deep.kompile.kore"
user_axioms U from "f2-examples/rdr-config-deep.kompile.kore" module "RDR-CONFIG-DEEP"

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

/-- Next's arity at the configuration sort, which Γ states whatever the text. -/
noncomputable def nextItem : Item := KoreAML.nextArityItem [] (srtOf c topCellSort)

/-- No sentence of the text has a `\rewrites` or a `\next`, so the text's signature states the
arity of next at no sort. -/
theorem text_nextless : kore.axiomDecls.all (fun ad => (nextSortsOf ad.ax.pattern).isEmpty) = true := by
  decide +kernel

/-- The item has an origin in the text, or is next's arity at the configuration sort. -/
noncomputable def sigFromN (it : Item) : Bool := sigFrom it || it.pat == nextItem.pat

theorem sigE_0 : (((sigItems c).drop 0).take 13).all sigFromN = true := by decide +kernel
theorem sigE_13 : (((sigItems c).drop 13).take 13).all sigFromN = true := by decide +kernel
theorem sigE_26 : (((sigItems c).drop 26).take 13).all sigFromN = true := by decide +kernel
theorem sigE_39 : (((sigItems c).drop 39).take 13).all sigFromN = true := by decide +kernel
theorem sigE_52 : (((sigItems c).drop 52).take 13).all sigFromN = true := by decide +kernel
theorem sigE_65 : (((sigItems c).drop 65).take 13).all sigFromN = true := by decide +kernel
theorem sigE_78 : (((sigItems c).drop 78).take 13).all sigFromN = true := by decide +kernel
theorem sigE_91 : (((sigItems c).drop 91).take 13).all sigFromN = true := by decide +kernel
theorem sigE_104 : (((sigItems c).drop 104).take 13).all sigFromN = true := by decide +kernel
theorem sigE_117 : (((sigItems c).drop 117).take 13).all sigFromN = true := by decide +kernel
theorem sigE_130 : (((sigItems c).drop 130).take 13).all sigFromN = true := by decide +kernel
theorem sigE_143 : (((sigItems c).drop 143).take 13).all sigFromN = true := by decide +kernel
theorem sigE_156 : (((sigItems c).drop 156).take 13).all sigFromN = true := by decide +kernel
theorem sigE_169 : (((sigItems c).drop 169).take 13).all sigFromN = true := by decide +kernel
theorem sigE_182 : (((sigItems c).drop 182).take 13).all sigFromN = true := by decide +kernel
theorem sigE_195 : (((sigItems c).drop 195).take 13).all sigFromN = true := by decide +kernel
theorem sigE_208 : (((sigItems c).drop 208).take 13).all sigFromN = true := by decide +kernel
theorem sigE_221 : (((sigItems c).drop 221).take 13).all sigFromN = true := by decide +kernel
theorem sigE_234 : (((sigItems c).drop 234).take 13).all sigFromN = true := by decide +kernel
theorem sigE_247 : (((sigItems c).drop 247).take 13).all sigFromN = true := by decide +kernel
theorem sigE_260 : (((sigItems c).drop 260).take 13).all sigFromN = true := by decide +kernel
theorem sigE_273 : (((sigItems c).drop 273).take 13).all sigFromN = true := by decide +kernel
theorem sigE_286 : (((sigItems c).drop 286).take 13).all sigFromN = true := by decide +kernel
theorem sigE_299 : (((sigItems c).drop 299).take 13).all sigFromN = true := by decide +kernel
theorem sigE_312 : (((sigItems c).drop 312).take 13).all sigFromN = true := by decide +kernel
theorem sigE_325 : (((sigItems c).drop 325).take 13).all sigFromN = true := by decide +kernel
theorem sigE_338 : (((sigItems c).drop 338).take 13).all sigFromN = true := by decide +kernel
theorem sigE_351 : (((sigItems c).drop 351).take 13).all sigFromN = true := by decide +kernel
theorem sigE_364 : (((sigItems c).drop 364).take 13).all sigFromN = true := by decide +kernel
theorem sigE_377 : (((sigItems c).drop 377).take 13).all sigFromN = true := by decide +kernel
theorem sigE_390 : (((sigItems c).drop 390).take 13).all sigFromN = true := by decide +kernel
theorem sigE_403 : (((sigItems c).drop 403).take 13).all sigFromN = true := by decide +kernel
theorem sigE_416 : (((sigItems c).drop 416).take 13).all sigFromN = true := by decide +kernel
theorem sigE_429 : (((sigItems c).drop 429).take 13).all sigFromN = true := by decide +kernel
theorem sigE_442 : (((sigItems c).drop 442).take 13).all sigFromN = true := by decide +kernel
theorem sigE_455 : (((sigItems c).drop 455).take 13).all sigFromN = true := by decide +kernel
theorem sigE_468 : (((sigItems c).drop 468).take 13).all sigFromN = true := by decide +kernel
theorem sigE_481 : (((sigItems c).drop 481).take 13).all sigFromN = true := by decide +kernel
theorem sigE_494 : (((sigItems c).drop 494).take 13).all sigFromN = true := by decide +kernel
theorem sigE_507 : (((sigItems c).drop 507).take 13).all sigFromN = true := by decide +kernel
theorem sigE_520 : (((sigItems c).drop 520).take 13).all sigFromN = true := by decide +kernel
theorem sigE_533 : (((sigItems c).drop 533).take 13).all sigFromN = true := by decide +kernel
theorem sigE_546 : (((sigItems c).drop 546).take 13).all sigFromN = true := by decide +kernel
theorem sigE_559 : (((sigItems c).drop 559).take 13).all sigFromN = true := by decide +kernel
theorem sigE_572 : (((sigItems c).drop 572).take 13).all sigFromN = true := by decide +kernel
theorem sigE_585 : (((sigItems c).drop 585).take 13).all sigFromN = true := by decide +kernel
theorem sigE_598 : (((sigItems c).drop 598).take 13).all sigFromN = true := by decide +kernel
theorem sigE_611 : (((sigItems c).drop 611).take 13).all sigFromN = true := by decide +kernel
theorem sigE_624 : (((sigItems c).drop 624).take 13).all sigFromN = true := by decide +kernel
theorem sigE_637 : (((sigItems c).drop 637).take 13).all sigFromN = true := by decide +kernel
theorem sigE_650 : (((sigItems c).drop 650).take 13).all sigFromN = true := by decide +kernel
theorem sigE_663 : (((sigItems c).drop 663).take 13).all sigFromN = true := by decide +kernel
theorem sigE_676 : (((sigItems c).drop 676).take 13).all sigFromN = true := by decide +kernel
theorem sigE_689 : (((sigItems c).drop 689).take 13).all sigFromN = true := by decide +kernel
theorem sigE_702 : (((sigItems c).drop 702).take 13).all sigFromN = true := by decide +kernel
theorem sigE_715 : (((sigItems c).drop 715).take 13).all sigFromN = true := by decide +kernel
theorem sigE_728 : (((sigItems c).drop 728).take 13).all sigFromN = true := by decide +kernel
theorem sigE_741 : (((sigItems c).drop 741).take 13).all sigFromN = true := by decide +kernel
theorem sigE_754 : (((sigItems c).drop 754).take 13).all sigFromN = true := by decide +kernel
theorem sigE_767 : ((sigItems c).drop 767).all sigFromN = true := by decide +kernel

theorem sig_sizes : (sigItems c).length = 770 := by decide +kernel

/-- **Every item of Γ's signature but next's arity has its origin**: the item of a declaration of
the text, or the sort constant of a registry sort or the arity of an interpreted hooked symbol that
the text does not declare at that shape. Next's arity at the configuration sort has none: the
text has no rule (`text_nextless`). -/
theorem sig_origin_but_next : (sigItems c).all (fun it =>
    (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it ||
      it.pat == nextItem.pat) = true :=
  tieAllE_whole (p := sigFromN) <|
    tieAllE_range (a := 0) (n := 13) sigE_0 <|
    tieAllE_range (a := 13) (n := 13) sigE_13 <|
    tieAllE_range (a := 26) (n := 13) sigE_26 <|
    tieAllE_range (a := 39) (n := 13) sigE_39 <|
    tieAllE_range (a := 52) (n := 13) sigE_52 <|
    tieAllE_range (a := 65) (n := 13) sigE_65 <|
    tieAllE_range (a := 78) (n := 13) sigE_78 <|
    tieAllE_range (a := 91) (n := 13) sigE_91 <|
    tieAllE_range (a := 104) (n := 13) sigE_104 <|
    tieAllE_range (a := 117) (n := 13) sigE_117 <|
    tieAllE_range (a := 130) (n := 13) sigE_130 <|
    tieAllE_range (a := 143) (n := 13) sigE_143 <|
    tieAllE_range (a := 156) (n := 13) sigE_156 <|
    tieAllE_range (a := 169) (n := 13) sigE_169 <|
    tieAllE_range (a := 182) (n := 13) sigE_182 <|
    tieAllE_range (a := 195) (n := 13) sigE_195 <|
    tieAllE_range (a := 208) (n := 13) sigE_208 <|
    tieAllE_range (a := 221) (n := 13) sigE_221 <|
    tieAllE_range (a := 234) (n := 13) sigE_234 <|
    tieAllE_range (a := 247) (n := 13) sigE_247 <|
    tieAllE_range (a := 260) (n := 13) sigE_260 <|
    tieAllE_range (a := 273) (n := 13) sigE_273 <|
    tieAllE_range (a := 286) (n := 13) sigE_286 <|
    tieAllE_range (a := 299) (n := 13) sigE_299 <|
    tieAllE_range (a := 312) (n := 13) sigE_312 <|
    tieAllE_range (a := 325) (n := 13) sigE_325 <|
    tieAllE_range (a := 338) (n := 13) sigE_338 <|
    tieAllE_range (a := 351) (n := 13) sigE_351 <|
    tieAllE_range (a := 364) (n := 13) sigE_364 <|
    tieAllE_range (a := 377) (n := 13) sigE_377 <|
    tieAllE_range (a := 390) (n := 13) sigE_390 <|
    tieAllE_range (a := 403) (n := 13) sigE_403 <|
    tieAllE_range (a := 416) (n := 13) sigE_416 <|
    tieAllE_range (a := 429) (n := 13) sigE_429 <|
    tieAllE_range (a := 442) (n := 13) sigE_442 <|
    tieAllE_range (a := 455) (n := 13) sigE_455 <|
    tieAllE_range (a := 468) (n := 13) sigE_468 <|
    tieAllE_range (a := 481) (n := 13) sigE_481 <|
    tieAllE_range (a := 494) (n := 13) sigE_494 <|
    tieAllE_range (a := 507) (n := 13) sigE_507 <|
    tieAllE_range (a := 520) (n := 13) sigE_520 <|
    tieAllE_range (a := 533) (n := 13) sigE_533 <|
    tieAllE_range (a := 546) (n := 13) sigE_546 <|
    tieAllE_range (a := 559) (n := 13) sigE_559 <|
    tieAllE_range (a := 572) (n := 13) sigE_572 <|
    tieAllE_range (a := 585) (n := 13) sigE_585 <|
    tieAllE_range (a := 598) (n := 13) sigE_598 <|
    tieAllE_range (a := 611) (n := 13) sigE_611 <|
    tieAllE_range (a := 624) (n := 13) sigE_624 <|
    tieAllE_range (a := 637) (n := 13) sigE_637 <|
    tieAllE_range (a := 650) (n := 13) sigE_650 <|
    tieAllE_range (a := 663) (n := 13) sigE_663 <|
    tieAllE_range (a := 676) (n := 13) sigE_676 <|
    tieAllE_range (a := 689) (n := 13) sigE_689 <|
    tieAllE_range (a := 702) (n := 13) sigE_702 <|
    tieAllE_range (a := 715) (n := 13) sigE_715 <|
    tieAllE_range (a := 728) (n := 13) sigE_728 <|
    tieAllE_range (a := 741) (n := 13) sigE_741 <|
    tieAllE_range (a := 754) (n := 13) sigE_754 <|
    sigE_767

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

end KCore.TieRdrConfigDeep

#check @KCore.TieRdrConfigDeep.sig_origin_but_next
#check @KCore.TieRdrConfigDeep.text_nextless
#print axioms KCore.TieRdrConfigDeep.sig_origin_but_next
#print axioms KCore.TieRdrConfigDeep.text_nextless
