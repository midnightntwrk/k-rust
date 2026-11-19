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

  The other sentences of these sections are not tied here:
  - 294 (`countAllOccurrences`' second equation, 1898): at the empty needle its two sides have the
    same value exactly where the interpretation gives the count no value (`cr0_iff`), so under
    `HookParams.none` (`count294_none`) and under no interpretation meeting `silentTotal`
    (`count294_not_holds`, the function form fails). These are statements about the values of the
    sides (`LibEv.val`), not about models of Γ: no refutation in models is stated. The argument
    that Γ refutes the sentence for every interpretation does not go through, since the sides
    agree at the empty needle under an interpretation giving the count no value there; so the
    sentence is put in no refuted class. In models of Γ, for every H meeting `silentTotal`, it is
    refuted: test/CountAllEmptyNeedleFlt.lean.
  - 296 (`findChar`, 1891): its right side applies `#if` at Int, `ite{SortInt}`, a symbol Γ does
    not have here: the reader numbers an instance of `ite` from its use in a sentence it reads, a
    parameter symbol of the text (`Parse.iteName`, implemented by `kIte`), and no such sentence of
    this text applies it; Γ's one `ite` is `kIte`, at KItem (LibProbe's run prints 296 as not
    probed, applying `ite{Int}`). A symbol with sort parameters is one symbol at each instance, and
    Γ applies `kIte` at no sort argument, so 296 applies a head Γ lacks (`ite296_absent`), though its
    names are all names of Γ's symbols. Where an instance is Γ's, it is a parameter symbol,
    which `LibEv`'s terms do not apply either (they apply interpreted symbols: `val` reads
    `Semantics.hv`, `srt?` reads `hookSigs`). Its condition on the interpretation is `findCharEq`.
  - 228 to 232 (`Int2Bytes` at three arguments, 2250 to 2258): each applies `Int2BytesNoLen`, a
    symbol Γ does not have, and 229 `~Int` too, their only such symbols (`int2BytesNoLen_absent`);
    this is the tie's account of them, no direction, and LibProbe's run prints each as not probed,
    applying symbols Γ does not have. `kcore account` counts them under `read [builtin]`, the
    reader's classification (consumed as the library's text), which agrees with it: Γ has no
    symbol `Int2BytesNoLen`.
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
  exact LibEv.fnReplaceAll_ev (coreOKH H) (shapesOKH H) hA.2.2.2.2.2.2.1 U.ax374 (by decide +kernel) (by decide +kernel)

theorem ev377 (H : HookParams) (hA : (cH H).libAdmitted) : EntailsAtValues (cH H) U.ax377 (trS U.ax377).pat := by
  rw [(by decide +kernel : (trS U.ax377).pat = (trAxiom [] [] U.ax377).pat)]
  exact LibEv.fnRfindChar_ev (coreOKH H) (shapesOKH H) hA.2.2.2.1 U.ax377 (by decide +kernel) (by decide +kernel)

theorem ev374_lib : EntailsAtValues (cH HookParams.lib) U.ax374 (trS U.ax374).pat :=
  ev374 HookParams.lib (libAdmitted_lib_of_coreOK coreOK)

theorem ev377_lib : EntailsAtValues (cH HookParams.lib) U.ax377 (trS U.ax377).pat :=
  ev377 HookParams.lib (libAdmitted_lib_of_coreOK coreOK)

/-! ## 294 (domains.md 1898) at the empty needle

The sentence is no condition `Semantics.libAdmitted` names. At the empty needle its `requires`
holds and it states that the count is its own successor (`cr0_parts`), so its two sides have one
value there exactly where the interpretation gives the count no value (`cr0_iff`): under
`HookParams.none` at every Source (`count294_none`); under no interpretation meeting `silentTotal`,
which gives the count a value there as the `functional` sentence of `countAllOccurrences` asks
(`count294_not_holds`). These are facts about the sides' values (`LibEv.val`); they relate to
models of Γ through `FnEqn.entailed` only in the direction of entailment, and no refutation in
models is stated. -/

section
open LibEv

/-- **domains.md 1898**, 294: `countAllOccurrences(Source, ToCount) => 1 +Int
countAllOccurrences(substrString(Source, findString(Source, ToCount, 0) +Int lengthString(ToCount),
lengthString(Source)), ToCount) requires findString(Source, ToCount, 0) >=Int 0`. -/
def fnCountRec : FnEqn :=
  ⟨[("VarSource", Srt.string), ("VarToCount", Srt.string)], stringCountAll,
    [(Srt.string, .var 0, none), (Srt.string, .var 1, none)], Srt.int,
    some (.app intGe [stFind 0 1, intT 0]),
    .app intAdd [intT 1, .app stringCountAll
      [.app stringSubstr [.var 0, .app intAdd [stFind 0 1, .app stringLength [.var 1]], .app stringLength [.var 0]],
       .var 1]]⟩

/-- The point at the empty needle: `Source` and `X0` the String `a`, `ToCount` and `X1` `""`. -/
def cr0 (a : String) : Subst := [(0, foS a), (1, foS ""), (2, foS a), (3, foS "")]

/-- At the empty needle the `requires` is `true` (`findString(a, "", 0)` is 0), the patterns
match, the left side is the count at `(a, "")` and the right side one more than it
(`substrString(a, 0, lengthString(a))` is `a`). -/
theorem cr0_parts (c : Semantics) (a : String) :
    val c (cr0 a) (.app intGe [stFind 0 1, intT 0]) = some (bool true) ∧
    FnEqn.Matches c (cr0 a) 2 fnCountRec.pats ∧
    val c (cr0 a) fnCountRec.lhs = c.hv stringCountAll [foS a, foS ""] ∧
    val c (cr0 a) fnCountRec.rhs =
      (c.hv stringCountAll [foS a, foS ""]).bind fun k => c.hv intAdd [int 1, k] := by
  have hfind : c.hv stringFind [foS a, foS "", int 0] = some (int 0) := by
    rw [st_hv_find0]
    simp [st_occ_nil, KStr.positions, List.range_succ_eq_map, KStr.firstOr]
  have hlen0 : c.hv stringLength [foS ""] = some (int 0) := st_hv_length ""
  have hsub : c.hv stringSubstr [foS a, int 0, int (a.toList.length : Int)] = some (foS a) := by
    rw [st_hv_substr a 0 _ (by omega) (by omega)]
    simp [st_foS_strV]
  have l0 : (cr0 a).lookup 0 = some (foS a) := rfl
  have l1 : (cr0 a).lookup 1 = some (foS "") := rfl
  have l2 : (cr0 a).lookup 2 = some (foS a) := rfl
  have l3 : (cr0 a).lookup 3 = some (foS "") := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [stFind, val, valList, allSome, l0, l1, intT, dv_int, hfind, fhv_intGe]
  · simp [FnEqn.Matches, fnCountRec, val, l0, l1, l2, l3]
  · simp [fnCountRec, FnEqn.lhs, FnEqn.xTerms, val, valList, allSome, l2, l3]
  · simp [fnCountRec, stFind, val, valList, allSome, l0, l1, intT, dv_int, hfind, hlen0, hv_intAdd,
      st_hv_length, hsub]
    cases c.hv stringCountAll [foS a, foS ""] <;> rfl

/-- Where the interpretation gives the count no value at the empty needle, both sides have none. -/
theorem cr0_none (c : Semantics) (a : String) (h : c.hv stringCountAll [foS a, foS ""] = none) :
    val c (cr0 a) fnCountRec.lhs = val c (cr0 a) fnCountRec.rhs := by
  obtain ⟨-, -, hl, hr⟩ := cr0_parts c a
  rw [hl, hr, h]; rfl

/-- Where it gives the count an Int value n, the right side is n + 1. -/
theorem cr0_int (c : Semantics) (a : String) (n : Int) (h : c.hv stringCountAll [foS a, foS ""] = some (int n)) :
    val c (cr0 a) fnCountRec.lhs ≠ val c (cr0 a) fnCountRec.rhs := by
  obtain ⟨-, -, hl, hr⟩ := cr0_parts c a
  rw [hl, hr, h, Option.bind_some, hv_intAdd]
  intro he
  have : n = 1 + n := by simpa [int] using he
  omega

/-- Under an interpretation meeting `silentTotal`, where Int values are literals, the count at the
empty needle is an Int value. -/
theorem cr0_total {c : Semantics} (hs : c.shapesOK = true) (ht : c.silentTotal) (a : String) :
    ∃ n, c.hv stringCountAll [foS a, foS ""] = some (int n) := by
  have hk : lookupSig hookSigs stringCountAll = some ⟨stringCountAll, [Srt.string, Srt.string], Srt.int⟩ := by
    decide +kernel
  have hmem := (lookupSig_spec hk).1
  have hvs : c.sortsOf [foS a, foS ""] = some [Srt.string, Srt.string] := by
    simp [Semantics.sortsOf, foS, Semantics.sortOf, dvOK]
  have hh : hook stringCountAll [foS a, foS ""] = some none := rfl
  have hsil : silent stringCountAll [foS a, foS ""] = true := rfl
  have hf := ht _ hmem (by decide) _ hvs hh hsil
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hf
  have hws : c.sortOf w = some Srt.int := by
    unfold Semantics.fallback at hw
    rw [hk] at hw
    simp only [Option.filter_eq_some_iff, beq_iff_eq] at hw
    exact hw.2
  obtain ⟨n, rfl⟩ := shape_int hs hws
  refine ⟨n, ?_⟩
  unfold Semantics.hv
  rw [Semantics.hookRes_of_silent hh hsil, hw]
  rfl

/-- A value of the count at the empty needle is the interpretation's, of sort Int. -/
theorem cr0_value_sort (c : Semantics) (a : String) {w : GroundTerm}
    (h : c.hv stringCountAll [foS a, foS ""] = some w) : c.sortOf w = some Srt.int := by
  have hh : hook stringCountAll [foS a, foS ""] = some none := rfl
  have hsil : silent stringCountAll [foS a, foS ""] = true := rfl
  unfold Semantics.hv at h
  rw [Semantics.hookRes_of_silent hh hsil] at h
  unfold Semantics.fallback at h
  rw [show lookupSig hookSigs stringCountAll = some ⟨stringCountAll, [Srt.string, Srt.string], Srt.int⟩ by
    decide +kernel] at h
  simp only [Option.join_some, Option.filter_eq_some_iff, beq_iff_eq] at h
  exact h.2

/-- **The instance at the empty needle holds exactly where the interpretation gives the count no
value there**, in every semantics whose Int values are literals. -/
theorem cr0_iff {c : Semantics} (hs : c.shapesOK = true) (a : String) :
    val c (cr0 a) fnCountRec.lhs = val c (cr0 a) fnCountRec.rhs ↔
      c.hv stringCountAll [foS a, foS ""] = none := by
  constructor
  · intro he
    cases hw : c.hv stringCountAll [foS a, foS ""] with
    | none => rfl
    | some w =>
      obtain ⟨n, rfl⟩ := shape_int hs (cr0_value_sort c a hw)
      exact absurd he (cr0_int c a n hw)
  · exact cr0_none c a

theorem pat294 : U.ax294.ax.pattern = fnCountRec.patR := by decide +kernel

/-- Under `HookParams.none` the instance at the empty needle holds at every Source. -/
theorem count294_none (a : String) :
    val (cH HookParams.none) (cr0 a) fnCountRec.lhs = val (cH HookParams.none) (cr0 a) fnCountRec.rhs :=
  cr0_none _ a (hv_none rfl rfl)

/-- Under every interpretation meeting `silentTotal`, the equation fails at the empty needle: the
function form does not hold. -/
theorem count294_not_holds (H : HookParams) (ht : (cH H).silentTotal) : ¬ fnCountRec.Holds (cH H) := by
  intro hH
  obtain ⟨n, hn⟩ := cr0_total (shapesOKH H) ht ""
  obtain ⟨hq, hm, -, -⟩ := cr0_parts (cH H) ""
  refine cr0_int (cH H) "" n hn (hH (cr0 "") ?_ (fun q hq' => by cases hq'; exact hq) hm)
  intro i p hp
  have hs : (cH H).sortOf (foS "") = some Srt.string := by simp [foS, Semantics.sortOf, dvOK]
  match i, hp with
  | 0, hp => cases hp; exact ⟨_, rfl, hs⟩
  | 1, hp => cases hp; exact ⟨_, rfl, hs⟩
  | 2, hp => cases hp; exact ⟨_, rfl, hs⟩
  | 3, hp => cases hp; exact ⟨_, rfl, hs⟩

end

/-! ## 228 to 232 (domains.md 2250 to 2258): no symbol of Γ

Each applies `Int2BytesNoLen` (the three-argument `Int2Bytes`, `symbol(Int2BytesNoLen)`, no
`hook`), which Γ does not have; it is the one symbol of each that Γ lacks, but for 229 (a negative
Int), which applies `~Int` too (`int2BytesNoLen_absent`). -/

/-- The names of the heads a sentence applies, each with its sort arguments (`appHeadsOf`), that are
not Γ's (`gammaHeads`). -/
noncomputable def absentOf (ad : AxiomDecl) : List String :=
  ((appHeadsOf ad.ax.pattern).filter fun h => !gammaHasHead c h).map (·.1)

theorem int2BytesNoLen_absent :
    [U.ax228, U.ax229, U.ax230, U.ax231, U.ax232].map absentOf =
      [["LblInt2BytesNoLen"], ["LblInt2BytesNoLen", "Lbl'Tild'Int'Unds'"], ["LblInt2BytesNoLen"],
       ["LblInt2BytesNoLen"], ["LblInt2BytesNoLen"]] := by decide +kernel

/-- 296 (domains.md 1891) applies `ite{SortInt}` twice, the one head of it Γ lacks: Γ's `ite`, the
registry's `kIte` at KItem, is applied at no sort argument. By the names alone (`symbolsOf`, `inj`
aside) it applies none Γ lacks: `Lblite` is the name of `kIte`. -/
theorem ite296_absent :
    (appHeadsOf U.ax296.ax.pattern).any (fun h => decide (h = ("Lblite", [KoreAML.srt "Int"]))) = true ∧
    absentOf U.ax296 = ["Lblite", "Lblite"] ∧
    (symbolsOf U.ax296.ax.pattern).all
      (fun n => n == "inj" || (kernelSyms c).any (fun k => c.symName k.name == n)) = true := by
  decide +kernel

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
/-- info: 'KCore.LibEvStrFlt.count294_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.count294_none
/-- info: 'KCore.LibEvStrFlt.count294_not_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.count294_not_holds
/-- info: 'KCore.LibEvStrFlt.cr0_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.cr0_iff
/-- info: 'KCore.LibEvStrFlt.int2BytesNoLen_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.int2BytesNoLen_absent
/-- info: 'KCore.LibEvStrFlt.ite296_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrFlt.ite296_absent
