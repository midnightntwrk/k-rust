/-
  STRING's and BYTES' library sentences over Γ's symbols on `f2-examples/silentflt.kompile.kore`,
  entailed at values (`EntailsAtValues`, direction Ev) from the library's statements
  (`KcoreSpec/LibEvStr.lean`; 373, domains.md 1915, is test/LibEvFnOwiseFlt.lean's `ev373`).
  Run from the package root: `lake env lean test/LibEvStrFlt.lean`.

  For every H:
  - 227, 226 (`Bool2String`, domains.md 1787, 1788); 234, 233 (`String2Bool`, 1793, 1794);
  - 257 (`=/=String`, 1867); 252, 264, 261 (`<=String`, `>String`, `>=String`, 1887 to 1889);
  - 297, 378 (`findChar`, `rfindChar` at the empty set of characters, 1892, 1894);
  - 295 (`countAllOccurrences` where the needle does not occur, 1896);
  - 375, 376 (`replaceFirst`, 1901, 1904); 372 (`replace` where the count is positive and the needle
    occurs, 1911);
  - 260 (`S1 ==K S2 => S1 ==String S2`, 1925);
  - 195, 194 (`#Ceil(padRightBytes(_, LEN, VAL))`, `#Ceil(padLeftBytes(_, LEN, VAL))`, 2241, 2242).
  For every H meeting `Semantics.libAdmitted` (so for `HookParams.lib`, `_lib`):
  - 374 (`replaceAll`, 1917: `replaceAllEq`), 377 (`rfindChar`, 1893: `rfindCharEq`).

  The other sentences of these sections are not tied here: 294 (`countAllOccurrences`' second
  equation, 1898), which no interpretation meets at the empty needle (`LibProbe.unmet`); 296
  (`findChar`, 1891), whose right side applies `#if` at Int, which `LibEv`'s terms do not express
  (its condition is `findCharEq`); 228 to 232 (`Int2Bytes`, 2250 to 2258), which apply
  `Int2BytesNoLen`, no symbol of Γ.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvStrFlt

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/silentflt.kompile.kore"
definition_of defn from "f2-examples/silentflt.kompile.kore"
user_axioms U from "f2-examples/silentflt.kompile.kore" module "SILENTFLT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)
theorem stringBelowH (H : HookParams) : Srt.string ∈ (cH H).sortsBelowKItem :=
  List.contains_iff_mem.mp (by decide +kernel : c.sortsBelowKItem.contains Srt.string = true)

theorem ev226 (H : HookParams) : EntailsAtValues (cH H) U.ax226 (trS U.ax226).pat := by
  rw [(by decide +kernel : (trS U.ax226).pat = (trAxiom [] [] U.ax226).pat)]
  exact LibEv.fnB2S_ev (coreOKH H) false U.ax226 (by decide +kernel) (by decide +kernel)

theorem ev227 (H : HookParams) : EntailsAtValues (cH H) U.ax227 (trS U.ax227).pat := by
  rw [(by decide +kernel : (trS U.ax227).pat = (trAxiom [] [] U.ax227).pat)]
  exact LibEv.fnB2S_ev (coreOKH H) true U.ax227 (by decide +kernel) (by decide +kernel)

theorem ev233 (H : HookParams) : EntailsAtValues (cH H) U.ax233 (trS U.ax233).pat := by
  rw [(by decide +kernel : (trS U.ax233).pat = (trAxiom [] [] U.ax233).pat)]
  exact LibEv.fnS2B_ev (coreOKH H) false U.ax233 (by decide +kernel) (by decide +kernel)

theorem ev234 (H : HookParams) : EntailsAtValues (cH H) U.ax234 (trS U.ax234).pat := by
  rw [(by decide +kernel : (trS U.ax234).pat = (trAxiom [] [] U.ax234).pat)]
  exact LibEv.fnS2B_ev (coreOKH H) true U.ax234 (by decide +kernel) (by decide +kernel)

theorem ev252 (H : HookParams) : EntailsAtValues (cH H) U.ax252 (trS U.ax252).pat := by
  rw [(by decide +kernel : (trS U.ax252).pat = (trAxiom [] [] U.ax252).pat)]
  exact LibEv.fnLeStr_ev (coreOKH H) (shapesOKH H) U.ax252 (by decide +kernel) (by decide +kernel)

theorem ev257 (H : HookParams) : EntailsAtValues (cH H) U.ax257 (trS U.ax257).pat := by
  rw [(by decide +kernel : (trS U.ax257).pat = (trAxiom [] [] U.ax257).pat)]
  exact LibEv.fnNeStr_ev (coreOKH H) (shapesOKH H) U.ax257 (by decide +kernel) (by decide +kernel)

theorem ev261 (H : HookParams) : EntailsAtValues (cH H) U.ax261 (trS U.ax261).pat := by
  rw [(by decide +kernel : (trS U.ax261).pat = (trAxiom [] [] U.ax261).pat)]
  exact LibEv.fnGeStr_ev (coreOKH H) (shapesOKH H) U.ax261 (by decide +kernel) (by decide +kernel)

theorem ev264 (H : HookParams) : EntailsAtValues (cH H) U.ax264 (trS U.ax264).pat := by
  rw [(by decide +kernel : (trS U.ax264).pat = (trAxiom [] [] U.ax264).pat)]
  exact LibEv.fnGtStr_ev (coreOKH H) (shapesOKH H) U.ax264 (by decide +kernel) (by decide +kernel)

theorem ev295 (H : HookParams) : EntailsAtValues (cH H) U.ax295 (trS U.ax295).pat := by
  rw [(by decide +kernel : (trS U.ax295).pat = (trAxiom [] [] U.ax295).pat)]
  exact LibEv.fnCountNone_ev (coreOKH H) (shapesOKH H) U.ax295 (by decide +kernel) (by decide +kernel)

theorem ev297 (H : HookParams) : EntailsAtValues (cH H) U.ax297 (trS U.ax297).pat := by
  rw [(by decide +kernel : (trS U.ax297).pat = (trAxiom [] [] U.ax297).pat)]
  exact LibEv.fnCharNone_ev (coreOKH H) (shapesOKH H) false U.ax297 (by decide +kernel) (by decide +kernel)

theorem ev378 (H : HookParams) : EntailsAtValues (cH H) U.ax378 (trS U.ax378).pat := by
  rw [(by decide +kernel : (trS U.ax378).pat = (trAxiom [] [] U.ax378).pat)]
  exact LibEv.fnCharNone_ev (coreOKH H) (shapesOKH H) true U.ax378 (by decide +kernel) (by decide +kernel)

theorem ev372 (H : HookParams) : EntailsAtValues (cH H) U.ax372 (trS U.ax372).pat := by
  rw [(by decide +kernel : (trS U.ax372).pat = (trAxiom [] [] U.ax372).pat)]
  exact LibEv.fnReplace_ev (coreOKH H) (shapesOKH H) U.ax372 (by decide +kernel) (by decide +kernel)

theorem ev375 (H : HookParams) : EntailsAtValues (cH H) U.ax375 (trS U.ax375).pat := by
  rw [(by decide +kernel : (trS U.ax375).pat = (trAxiom [] [] U.ax375).pat)]
  exact LibEv.fnRepFirst_ev (coreOKH H) (shapesOKH H) U.ax375 (by decide +kernel) (by decide +kernel)

theorem ev376 (H : HookParams) : EntailsAtValues (cH H) U.ax376 (trS U.ax376).pat := by
  rw [(by decide +kernel : (trS U.ax376).pat = (trAxiom [] [] U.ax376).pat)]
  exact LibEv.fnRepFirstNone_ev (coreOKH H) (shapesOKH H) U.ax376 (by decide +kernel) (by decide +kernel)

theorem ev260 (H : HookParams) : EntailsAtValues (cH H) U.ax260 (trS U.ax260).pat := by
  rw [(by decide +kernel : (trS U.ax260).pat = (trAxiom [] [] U.ax260).pat)]
  exact LibEv.strKEq_ev (coreOKH H) (shapesOKH H) (stringBelowH H) U.ax260 (by decide +kernel) (by decide +kernel)

theorem ev194 (H : HookParams) : EntailsAtValues (cH H) U.ax194 (trS U.ax194).pat := by
  rw [(by decide +kernel : (trS U.ax194).pat = (trAxiom [] [] U.ax194).pat)]
  exact LibEv.ceilPad_ev (coreOKH H) (shapesOKH H) true U.ax194 (by decide +kernel) (by decide +kernel)

theorem ev195 (H : HookParams) : EntailsAtValues (cH H) U.ax195 (trS U.ax195).pat := by
  rw [(by decide +kernel : (trS U.ax195).pat = (trAxiom [] [] U.ax195).pat)]
  exact LibEv.ceilPad_ev (coreOKH H) (shapesOKH H) false U.ax195 (by decide +kernel) (by decide +kernel)

theorem ev374 (H : HookParams) (hA : (cH H).libAdmitted) : EntailsAtValues (cH H) U.ax374 (trS U.ax374).pat := by
  rw [(by decide +kernel : (trS U.ax374).pat = (trAxiom [] [] U.ax374).pat)]
  exact LibEv.fnReplaceAll_ev (coreOKH H) (shapesOKH H) hA.2.2.2.2.2.2 U.ax374 (by decide +kernel) (by decide +kernel)

theorem ev377 (H : HookParams) (hA : (cH H).libAdmitted) : EntailsAtValues (cH H) U.ax377 (trS U.ax377).pat := by
  rw [(by decide +kernel : (trS U.ax377).pat = (trAxiom [] [] U.ax377).pat)]
  exact LibEv.fnRfindChar_ev (coreOKH H) (shapesOKH H) hA.2.2.2.1 U.ax377 (by decide +kernel) (by decide +kernel)

theorem ev374_lib : EntailsAtValues (cH HookParams.lib) U.ax374 (trS U.ax374).pat :=
  ev374 HookParams.lib (libAdmitted_lib_of_coreOK coreOK)

theorem ev377_lib : EntailsAtValues (cH HookParams.lib) U.ax377 (trS U.ax377).pat :=
  ev377 HookParams.lib (libAdmitted_lib_of_coreOK coreOK)

end KCore.LibEvStrFlt

/-- info: 'KCore.LibEvStrFlt.ev226' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ev226
/-- info: 'KCore.LibEvStrFlt.ev227' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ev227
/-- info: 'KCore.LibEvStrFlt.ev233' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ev233
/-- info: 'KCore.LibEvStrFlt.ev234' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ev234
/-- info: 'KCore.LibEvStrFlt.ev252' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ev252
/-- info: 'KCore.LibEvStrFlt.ev257' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ev257
/-- info: 'KCore.LibEvStrFlt.ev261' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ev261
/-- info: 'KCore.LibEvStrFlt.ev264' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ev264
/-- info: 'KCore.LibEvStrFlt.ev295' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ev295
/-- info: 'KCore.LibEvStrFlt.ev297' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ev297
/-- info: 'KCore.LibEvStrFlt.ev378' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ev378
/-- info: 'KCore.LibEvStrFlt.ev372' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ev372
/-- info: 'KCore.LibEvStrFlt.ev375' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ev375
/-- info: 'KCore.LibEvStrFlt.ev376' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ev376
/-- info: 'KCore.LibEvStrFlt.ev260' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ev260
/-- info: 'KCore.LibEvStrFlt.ev194' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ev194
/-- info: 'KCore.LibEvStrFlt.ev195' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ev195
/-- info: 'KCore.LibEvStrFlt.ev374' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ev374
/-- info: 'KCore.LibEvStrFlt.ev377' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ev377
