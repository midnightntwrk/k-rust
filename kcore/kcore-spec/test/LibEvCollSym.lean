/-
  The lemmas of MAP-KORE-SYMBOLIC and SET-KORE-SYMBOLIC (domains.md, K 7.1.337) over element
  variables on `f2-examples/collsym.kompile.kore`, entailed at values (`EntailsAtValues`) for every
  interpretation H, each from the library's one statement of it (KcoreSpec/LibEvCollSym.lean):
  the text's axiom is compared with the statement's pattern over the registry's names.
  Run from the package root: `lake env lean test/LibEvCollSym.lean`.

  - Without an `ensures` (`LibEv.Eqn`): 417, 418, 419, 426, 434, 439, 441, 444, 445 of MAP;
    835, 836, 854 (both argument orders), 855, 864 (both), 865, 876 of SET.
  - With an `ensures` (`LibEv.EqnE`): 425, 432, 437 of MAP; 837, 839, 841, 843, 857 (both), 867
    (both), 871, 877, 886, 888 of SET.

  - Over a set variable (`LibEv.SvEqn`), entailed at set values (`EntailsAtSetValues`): 449, 450.

  Not here: the sentences whose `requires` applies `==K` or `=/=K` to two KItem variables (422,
  429, 433, 435, 438, 440, 446, 447: `kseq(K, dotk())`, which no library term form covers); 451
  and 452, whose right side has `#Not`, which `LibEv.SvPred` has not; 411 and 830, `#Ceil` of a
  partial symbol over set variables, which take the form of `LibEv.ceilMap_refuted_at`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvCollSym

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/collsym.kompile.kore"
definition_of defn from "f2-examples/collsym.kompile.kore"
user_axioms U from "f2-examples/collsym.kompile.kore" module "COLLSYM"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

/-- domains.md 417 (`LibEv.msUpdConcat`). -/
theorem ev179 (H : HookParams) : EntailsAtValues (cH H) U.ax179 (trS U.ax179).pat := by
  rw [(by decide +kernel : (trS U.ax179).pat = (trAxiom [] [] U.ax179).pat)]
  exact LibEv.msUpdConcat_ev (coreOKH H) (shapesOKH H) U.ax179 (by decide +kernel) (by decide +kernel)

/-- domains.md 418 (`LibEv.msUpdFresh`). -/
theorem ev177 (H : HookParams) : EntailsAtValues (cH H) U.ax177 (trS U.ax177).pat := by
  rw [(by decide +kernel : (trS U.ax177).pat = (trAxiom [] [] U.ax177).pat)]
  exact LibEv.msUpdFresh_ev (coreOKH H) (shapesOKH H) U.ax177 (by decide +kernel) (by decide +kernel)

/-- domains.md 419 (`LibEv.msUpdUpd`). -/
theorem ev178 (H : HookParams) : EntailsAtValues (cH H) U.ax178 (trS U.ax178).pat := by
  rw [(by decide +kernel : (trS U.ax178).pat = (trAxiom [] [] U.ax178).pat)]
  exact LibEv.msUpdUpd_ev (coreOKH H) (shapesOKH H) U.ax178 (by decide +kernel) (by decide +kernel)

/-- domains.md 426 (`LibEv.msRemFresh`). -/
theorem ev215 (H : HookParams) : EntailsAtValues (cH H) U.ax215 (trS U.ax215).pat := by
  rw [(by decide +kernel : (trS U.ax215).pat = (trAxiom [] [] U.ax215).pat)]
  exact LibEv.msRemFresh_ev (coreOKH H) (shapesOKH H) U.ax215 (by decide +kernel) (by decide +kernel)

/-- domains.md 434 (`LibEv.msLookupUpd`). -/
theorem ev169 (H : HookParams) : EntailsAtValues (cH H) U.ax169 (trS U.ax169).pat := by
  rw [(by decide +kernel : (trS U.ax169).pat = (trAxiom [] [] U.ax169).pat)]
  exact LibEv.msLookupUpd_ev (coreOKH H) (shapesOKH H) U.ax169 (by decide +kernel) (by decide +kernel)

/-- domains.md 439 (`LibEv.msLookupDefUpd`). -/
theorem ev174 (H : HookParams) : EntailsAtValues (cH H) U.ax174 (trS U.ax174).pat := by
  rw [(by decide +kernel : (trS U.ax174).pat = (trAxiom [] [] U.ax174).pat)]
  exact LibEv.msLookupDefUpd_ev (coreOKH H) (shapesOKH H) U.ax174 (by decide +kernel) (by decide +kernel)

/-- domains.md 441 (`LibEv.msLookupDefUnit`). -/
theorem ev172 (H : HookParams) : EntailsAtValues (cH H) U.ax172 (trS U.ax172).pat := by
  rw [(by decide +kernel : (trS U.ax172).pat = (trAxiom [] [] U.ax172).pat)]
  exact LibEv.msLookupDefUnit_ev (coreOKH H) U.ax172 (by decide +kernel) (by decide +kernel)

/-- domains.md 444 (`LibEv.msInKeysRem`). -/
theorem ev233 (H : HookParams) : EntailsAtValues (cH H) U.ax233 (trS U.ax233).pat := by
  rw [(by decide +kernel : (trS U.ax233).pat = (trAxiom [] [] U.ax233).pat)]
  exact LibEv.msInKeysRem_ev (coreOKH H) (shapesOKH H) U.ax233 (by decide +kernel) (by decide +kernel)

/-- domains.md 445 (`LibEv.msInKeysUpd`). -/
theorem ev232 (H : HookParams) : EntailsAtValues (cH H) U.ax232 (trS U.ax232).pat := by
  rw [(by decide +kernel : (trS U.ax232).pat = (trAxiom [] [] U.ax232).pat)]
  exact LibEv.msInKeysUpd_ev (coreOKH H) (shapesOKH H) U.ax232 (by decide +kernel) (by decide +kernel)

/-- domains.md 835 (`LibEv.ssDiffUnit`). -/
theorem ev181 (H : HookParams) : EntailsAtValues (cH H) U.ax181 (trS U.ax181).pat := by
  rw [(by decide +kernel : (trS U.ax181).pat = (trAxiom [] [] U.ax181).pat)]
  exact LibEv.ssDiffUnit_ev (coreOKH H) (shapesOKH H) U.ax181 (by decide +kernel) (by decide +kernel)

/-- domains.md 836 (`LibEv.ssUnitDiff`). -/
theorem ev183 (H : HookParams) : EntailsAtValues (cH H) U.ax183 (trS U.ax183).pat := by
  rw [(by decide +kernel : (trS U.ax183).pat = (trAxiom [] [] U.ax183).pat)]
  exact LibEv.ssUnitDiff_ev (coreOKH H) (shapesOKH H) U.ax183 (by decide +kernel) (by decide +kernel)

/-- domains.md 854 (`LibEv.ssUnionUnit`). -/
theorem ev250 (H : HookParams) : EntailsAtValues (cH H) U.ax250 (trS U.ax250).pat := by
  rw [(by decide +kernel : (trS U.ax250).pat = (trAxiom [] [] U.ax250).pat)]
  exact LibEv.ssUnionUnit_ev (coreOKH H) (shapesOKH H) U.ax250 (by decide +kernel) (by decide +kernel)

/-- domains.md 854 (`LibEv.ssUnitUnion`). -/
theorem ev252 (H : HookParams) : EntailsAtValues (cH H) U.ax252 (trS U.ax252).pat := by
  rw [(by decide +kernel : (trS U.ax252).pat = (trAxiom [] [] U.ax252).pat)]
  exact LibEv.ssUnitUnion_ev (coreOKH H) (shapesOKH H) U.ax252 (by decide +kernel) (by decide +kernel)

/-- domains.md 855 (`LibEv.ssUnionSelf`). -/
theorem ev249 (H : HookParams) : EntailsAtValues (cH H) U.ax249 (trS U.ax249).pat := by
  rw [(by decide +kernel : (trS U.ax249).pat = (trAxiom [] [] U.ax249).pat)]
  exact LibEv.ssUnionSelf_ev (coreOKH H) (shapesOKH H) U.ax249 (by decide +kernel) (by decide +kernel)

/-- domains.md 864 (`LibEv.ssInterUnit`). -/
theorem ev263 (H : HookParams) : EntailsAtValues (cH H) U.ax263 (trS U.ax263).pat := by
  rw [(by decide +kernel : (trS U.ax263).pat = (trAxiom [] [] U.ax263).pat)]
  exact LibEv.ssInterUnit_ev (coreOKH H) (shapesOKH H) U.ax263 (by decide +kernel) (by decide +kernel)

/-- domains.md 864 (`LibEv.ssUnitInter`). -/
theorem ev264 (H : HookParams) : EntailsAtValues (cH H) U.ax264 (trS U.ax264).pat := by
  rw [(by decide +kernel : (trS U.ax264).pat = (trAxiom [] [] U.ax264).pat)]
  exact LibEv.ssUnitInter_ev (coreOKH H) (shapesOKH H) U.ax264 (by decide +kernel) (by decide +kernel)

/-- domains.md 865 (`LibEv.ssInterSelf`). -/
theorem ev262 (H : HookParams) : EntailsAtValues (cH H) U.ax262 (trS U.ax262).pat := by
  rw [(by decide +kernel : (trS U.ax262).pat = (trAxiom [] [] U.ax262).pat)]
  exact LibEv.ssInterSelf_ev (coreOKH H) (shapesOKH H) U.ax262 (by decide +kernel) (by decide +kernel)

/-- domains.md 876 (`LibEv.ssInUnit`). -/
theorem ev190 (H : HookParams) : EntailsAtValues (cH H) U.ax190 (trS U.ax190).pat := by
  rw [(by decide +kernel : (trS U.ax190).pat = (trAxiom [] [] U.ax190).pat)]
  exact LibEv.ssInUnit_ev (coreOKH H) U.ax190 (by decide +kernel) (by decide +kernel)

/-- domains.md 425 (`LibEv.msRemConcat`). -/
theorem ev216 (H : HookParams) : EntailsAtValues (cH H) U.ax216 (trS U.ax216).pat := by
  rw [(by decide +kernel : (trS U.ax216).pat = (trAxiom [] [] U.ax216).pat)]
  exact LibEv.msRemConcat_ev (coreOKH H) (shapesOKH H) U.ax216 (by decide +kernel) (by decide +kernel)

/-- domains.md 432 (`LibEv.msLookupConcat`). -/
theorem ev170 (H : HookParams) : EntailsAtValues (cH H) U.ax170 (trS U.ax170).pat := by
  rw [(by decide +kernel : (trS U.ax170).pat = (trAxiom [] [] U.ax170).pat)]
  exact LibEv.msLookupConcat_ev (coreOKH H) (shapesOKH H) U.ax170 (by decide +kernel) (by decide +kernel)

/-- domains.md 437 (`LibEv.msLookupDefConcat`). -/
theorem ev175 (H : HookParams) : EntailsAtValues (cH H) U.ax175 (trS U.ax175).pat := by
  rw [(by decide +kernel : (trS U.ax175).pat = (trAxiom [] [] U.ax175).pat)]
  exact LibEv.msLookupDefConcat_ev (coreOKH H) (shapesOKH H) U.ax175 (by decide +kernel) (by decide +kernel)

/-- domains.md 837 (`LibEv.ssItemDiffConcat`). -/
theorem ev184 (H : HookParams) : EntailsAtValues (cH H) U.ax184 (trS U.ax184).pat := by
  rw [(by decide +kernel : (trS U.ax184).pat = (trAxiom [] [] U.ax184).pat)]
  exact LibEv.ssItemDiffConcat_ev (coreOKH H) (shapesOKH H) U.ax184 (by decide +kernel) (by decide +kernel)

/-- domains.md 839 (`LibEv.ssDiffConcat`). -/
theorem ev182 (H : HookParams) : EntailsAtValues (cH H) U.ax182 (trS U.ax182).pat := by
  rw [(by decide +kernel : (trS U.ax182).pat = (trAxiom [] [] U.ax182).pat)]
  exact LibEv.ssDiffConcat_ev (coreOKH H) (shapesOKH H) U.ax182 (by decide +kernel) (by decide +kernel)

/-- domains.md 841 (`LibEv.ssConcatDiff`). -/
theorem ev185 (H : HookParams) : EntailsAtValues (cH H) U.ax185 (trS U.ax185).pat := by
  rw [(by decide +kernel : (trS U.ax185).pat = (trAxiom [] [] U.ax185).pat)]
  exact LibEv.ssConcatDiff_ev (coreOKH H) (shapesOKH H) U.ax185 (by decide +kernel) (by decide +kernel)

/-- domains.md 843 (`LibEv.ssConcatDiffItem`). -/
theorem ev186 (H : HookParams) : EntailsAtValues (cH H) U.ax186 (trS U.ax186).pat := by
  rw [(by decide +kernel : (trS U.ax186).pat = (trAxiom [] [] U.ax186).pat)]
  exact LibEv.ssConcatDiffItem_ev (coreOKH H) (shapesOKH H) U.ax186 (by decide +kernel) (by decide +kernel)

/-- domains.md 857 (`LibEv.ssItemUnionConcat`). -/
theorem ev253 (H : HookParams) : EntailsAtValues (cH H) U.ax253 (trS U.ax253).pat := by
  rw [(by decide +kernel : (trS U.ax253).pat = (trAxiom [] [] U.ax253).pat)]
  exact LibEv.ssItemUnionConcat_ev (coreOKH H) (shapesOKH H) U.ax253 (by decide +kernel) (by decide +kernel)

/-- domains.md 857 (`LibEv.ssConcatUnionItem`). -/
theorem ev254 (H : HookParams) : EntailsAtValues (cH H) U.ax254 (trS U.ax254).pat := by
  rw [(by decide +kernel : (trS U.ax254).pat = (trAxiom [] [] U.ax254).pat)]
  exact LibEv.ssConcatUnionItem_ev (coreOKH H) (shapesOKH H) U.ax254 (by decide +kernel) (by decide +kernel)

/-- domains.md 867 (`LibEv.ssItemInterConcat`). -/
theorem ev265 (H : HookParams) : EntailsAtValues (cH H) U.ax265 (trS U.ax265).pat := by
  rw [(by decide +kernel : (trS U.ax265).pat = (trAxiom [] [] U.ax265).pat)]
  exact LibEv.ssItemInterConcat_ev (coreOKH H) (shapesOKH H) U.ax265 (by decide +kernel) (by decide +kernel)

/-- domains.md 867 (`LibEv.ssConcatInterItem`). -/
theorem ev266 (H : HookParams) : EntailsAtValues (cH H) U.ax266 (trS U.ax266).pat := by
  rw [(by decide +kernel : (trS U.ax266).pat = (trAxiom [] [] U.ax266).pat)]
  exact LibEv.ssConcatInterItem_ev (coreOKH H) (shapesOKH H) U.ax266 (by decide +kernel) (by decide +kernel)

/-- domains.md 871 (`LibEv.ssInterConcat2`). -/
theorem ev267 (H : HookParams) : EntailsAtValues (cH H) U.ax267 (trS U.ax267).pat := by
  rw [(by decide +kernel : (trS U.ax267).pat = (trAxiom [] [] U.ax267).pat)]
  exact LibEv.ssInterConcat2_ev (coreOKH H) (shapesOKH H) U.ax267 (by decide +kernel) (by decide +kernel)

/-- domains.md 877 (`LibEv.ssInConcat`). -/
theorem ev187 (H : HookParams) : EntailsAtValues (cH H) U.ax187 (trS U.ax187).pat := by
  rw [(by decide +kernel : (trS U.ax187).pat = (trAxiom [] [] U.ax187).pat)]
  exact LibEv.ssInConcat_ev (coreOKH H) (shapesOKH H) U.ax187 (by decide +kernel) (by decide +kernel)

/-- domains.md 886 (`LibEv.ssInUnionL`). -/
theorem ev189 (H : HookParams) : EntailsAtValues (cH H) U.ax189 (trS U.ax189).pat := by
  rw [(by decide +kernel : (trS U.ax189).pat = (trAxiom [] [] U.ax189).pat)]
  exact LibEv.ssInUnionL_ev (coreOKH H) (shapesOKH H) U.ax189 (by decide +kernel) (by decide +kernel)

/-- domains.md 888 (`LibEv.ssInUnionR`). -/
theorem ev188 (H : HookParams) : EntailsAtValues (cH H) U.ax188 (trS U.ax188).pat := by
  rw [(by decide +kernel : (trS U.ax188).pat = (trAxiom [] [] U.ax188).pat)]
  exact LibEv.ssInUnionR_ev (coreOKH H) (shapesOKH H) U.ax188 (by decide +kernel) (by decide +kernel)

/-- domains.md 449 (`LibEv.msInKeysUnitSv false`), over the set variable `@Key`: entailed at set values. -/
theorem ev157 (H : HookParams) : EntailsAtSetValues (cH H) U.ax157 (trS U.ax157).pat := by
  rw [(by decide +kernel : (trS U.ax157).pat = (trAxiom [] [] U.ax157).pat)]
  exact LibEv.msInKeysUnitSv_ev (coreOKH H) false U.ax157 (by decide +kernel) (by decide +kernel)

/-- domains.md 450 (`LibEv.msInKeysUnitSv true`). -/
theorem ev148 (H : HookParams) : EntailsAtSetValues (cH H) U.ax148 (trS U.ax148).pat := by
  rw [(by decide +kernel : (trS U.ax148).pat = (trAxiom [] [] U.ax148).pat)]
  exact LibEv.msInKeysUnitSv_ev (coreOKH H) true U.ax148 (by decide +kernel) (by decide +kernel)

end KCore.LibEvCollSym

/-- info: 'KCore.LibEvCollSym.ev179' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev179
/-- info: 'KCore.LibEvCollSym.ev177' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev177
/-- info: 'KCore.LibEvCollSym.ev178' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev178
/-- info: 'KCore.LibEvCollSym.ev215' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev215
/-- info: 'KCore.LibEvCollSym.ev169' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev169
/-- info: 'KCore.LibEvCollSym.ev174' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev174
/-- info: 'KCore.LibEvCollSym.ev172' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev172
/-- info: 'KCore.LibEvCollSym.ev233' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev233
/-- info: 'KCore.LibEvCollSym.ev232' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev232
/-- info: 'KCore.LibEvCollSym.ev181' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev181
/-- info: 'KCore.LibEvCollSym.ev183' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev183
/-- info: 'KCore.LibEvCollSym.ev250' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev250
/-- info: 'KCore.LibEvCollSym.ev252' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev252
/-- info: 'KCore.LibEvCollSym.ev249' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev249
/-- info: 'KCore.LibEvCollSym.ev263' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev263
/-- info: 'KCore.LibEvCollSym.ev264' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev264
/-- info: 'KCore.LibEvCollSym.ev262' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev262
/-- info: 'KCore.LibEvCollSym.ev190' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev190
/-- info: 'KCore.LibEvCollSym.ev216' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev216
/-- info: 'KCore.LibEvCollSym.ev170' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev170
/-- info: 'KCore.LibEvCollSym.ev175' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev175
/-- info: 'KCore.LibEvCollSym.ev184' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev184
/-- info: 'KCore.LibEvCollSym.ev182' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev182
/-- info: 'KCore.LibEvCollSym.ev185' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev185
/-- info: 'KCore.LibEvCollSym.ev186' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev186
/-- info: 'KCore.LibEvCollSym.ev253' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev253
/-- info: 'KCore.LibEvCollSym.ev254' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev254
/-- info: 'KCore.LibEvCollSym.ev265' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev265
/-- info: 'KCore.LibEvCollSym.ev266' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev266
/-- info: 'KCore.LibEvCollSym.ev267' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev267
/-- info: 'KCore.LibEvCollSym.ev187' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev187
/-- info: 'KCore.LibEvCollSym.ev189' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev189
/-- info: 'KCore.LibEvCollSym.ev188' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev188
/-- info: 'KCore.LibEvCollSym.ev157' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev157
/-- info: 'KCore.LibEvCollSym.ev148' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev148
