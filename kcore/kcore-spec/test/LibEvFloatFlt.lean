/-
  FLOAT's sentences on `f2-examples/silentflt.kompile.kore` whose value reads no clause of an
  operation the text takes from IEEE 754 by name (findings/FLOAT-BYTES-rulings.md section 2: the
  same under the scoped and the incorporating reading), entailed at values (`EntailsAtValues`,
  direction Ev) from the library's statements, for every interpretation H meeting the condition
  each names.
  Run from the package root: `lake env lean test/LibEvFloatFlt.lean`.

  - 254 (`F1 =/=Float F2 => notBool (F1 ==Float F2)`, domains.md 1648): `ev254`, for every H
    meeting `neFloatEq` (`LibEv.fnNeFloat_ev`, KcoreSpec/LibEvFloat.lean); `ev254_lib` under
    `HookParams.lib`. The comparisons are stated at every pair of data.
  - The `functional` sentences of FLOAT's interpreted symbols (`LibEv.functional_ev`): a value
    exists at every Float, whatever the value is. `--Float` 25, `absFloat` 103, `ceilFloat` 108,
    `floorFloat` 119, `truncFloat` 173, `isInfinite` 134, `isNaN` 143, symbols of
    `totalSilentKeys`, for every H meeting `silentTotal`; `exponentBitsFloat` 117 and
    `precisionFloat` 159, of `floatResInt`, for every H (`floatShapeOK`, from `coreOK`).
  - 321 (`isInfinite(F) => F >Float maxValueFloat(precisionFloat(F), exponentBitsFloat(F)) orBool
    F <Float --Float maxValueFloat(precisionFloat(F), exponentBitsFloat(F))`, domains.md 1673):
    `ev321`, for every H meeting `isInfiniteEq` (`LibEv.fnIsInfinite_ev`); `ev321_lib` under
    `HookParams.lib`. Its value is the same under both readings of the naming of IEEE 754 (argued
    from section 2 of the rulings, not proved: it reads `precisionFloat`, `exponentBitsFloat`,
    `maxValueFloat`, `--Float` of a finite nonzero datum and the comparisons, each stated alike).
    At a Float of a format with a model, both sides are `hook`'s and agree for every format: a datum is infinite exactly when it is above the format's largest finite value or
    below its negation (`KFloat.isInf_unpack`, KcoreSpec/FloatUnpack.lean). At a format with a
    field of 1, which has no model, `isInfinite` is at a silent point and the condition is the
    sentence there.

  Not tied here: 380 (`sqrtFloat(F) => rootFloat(F, 2)`, 1671), whose right side is `rootFloat`, a
  parameter symbol no FLOAT sentence gives a value, and whose sides are the standard's square root
  and root only if the naming of IEEE 754 incorporates its operations (rulings section 7, G12),
  which the text leaves open.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvFloatFlt

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
theorem floatShapeOKH (H : HookParams) : (cH H).floatShapeOK = true := floatShapeOK_of_coreOK (coreOKH H)

theorem ev254 (H : HookParams) (hc : (cH H).neFloatEq) : EntailsAtValues (cH H) U.ax254 (trS U.ax254).pat := by
  rw [(by decide +kernel : (trS U.ax254).pat = (trAxiom [] [] U.ax254).pat)]
  exact LibEv.fnNeFloat_ev (coreOKH H) hc U.ax254 (by decide +kernel) (by decide +kernel)

theorem ev254_lib : EntailsAtValues (cH HookParams.lib) U.ax254 (trS U.ax254).pat :=
  ev254 HookParams.lib (neFloatEq_lib c)

theorem ev321 (H : HookParams) (hc : (cH H).isInfiniteEq) : EntailsAtValues (cH H) U.ax321 (trS U.ax321).pat := by
  rw [(by decide +kernel : (trS U.ax321).pat = (trAxiom [] [] U.ax321).pat)]
  exact LibEv.fnIsInfinite_ev (coreOKH H) hc U.ax321 (by decide +kernel) (by decide +kernel)

theorem ev321_lib : EntailsAtValues (cH HookParams.lib) U.ax321 (trS U.ax321).pat :=
  ev321 HookParams.lib (isInfiniteEq_lib c (floatShapeOK_of_coreOK coreOK))

theorem fun25 (H : HookParams) (hst : (cH H).silentTotal) : EntailsAtValues (cH H) U.ax25 (trS U.ax25).pat := by
  rw [(by decide +kernel : (trS U.ax25).pat = (trAxiom [] [] U.ax25).pat)]
  exact LibEv.functional_ev (coreOKH H) (shapesOKH H) (k := ⟨floatNeg, [Srt.float], Srt.float⟩) (by decide +kernel) (Or.inr (Or.inl ⟨by decide, hst⟩))
    (by decide +kernel) U.ax25 (by decide +kernel) (by decide +kernel)

theorem fun103 (H : HookParams) (hst : (cH H).silentTotal) : EntailsAtValues (cH H) U.ax103 (trS U.ax103).pat := by
  rw [(by decide +kernel : (trS U.ax103).pat = (trAxiom [] [] U.ax103).pat)]
  exact LibEv.functional_ev (coreOKH H) (shapesOKH H) (k := ⟨floatAbs, [Srt.float], Srt.float⟩) (by decide +kernel) (Or.inr (Or.inl ⟨by decide, hst⟩))
    (by decide +kernel) U.ax103 (by decide +kernel) (by decide +kernel)

theorem fun108 (H : HookParams) (hst : (cH H).silentTotal) : EntailsAtValues (cH H) U.ax108 (trS U.ax108).pat := by
  rw [(by decide +kernel : (trS U.ax108).pat = (trAxiom [] [] U.ax108).pat)]
  exact LibEv.functional_ev (coreOKH H) (shapesOKH H) (k := ⟨floatCeil, [Srt.float], Srt.float⟩) (by decide +kernel) (Or.inr (Or.inl ⟨by decide, hst⟩))
    (by decide +kernel) U.ax108 (by decide +kernel) (by decide +kernel)

theorem fun117 (H : HookParams) : EntailsAtValues (cH H) U.ax117 (trS U.ax117).pat := by
  rw [(by decide +kernel : (trS U.ax117).pat = (trAxiom [] [] U.ax117).pat)]
  exact LibEv.functional_ev (coreOKH H) (shapesOKH H) (k := ⟨floatExponentBits, [Srt.float], Srt.int⟩) (by decide +kernel) (Or.inr (Or.inr ⟨by decide, floatShapeOKH H⟩))
    (by decide +kernel) U.ax117 (by decide +kernel) (by decide +kernel)

theorem fun119 (H : HookParams) (hst : (cH H).silentTotal) : EntailsAtValues (cH H) U.ax119 (trS U.ax119).pat := by
  rw [(by decide +kernel : (trS U.ax119).pat = (trAxiom [] [] U.ax119).pat)]
  exact LibEv.functional_ev (coreOKH H) (shapesOKH H) (k := ⟨floatFloor, [Srt.float], Srt.float⟩) (by decide +kernel) (Or.inr (Or.inl ⟨by decide, hst⟩))
    (by decide +kernel) U.ax119 (by decide +kernel) (by decide +kernel)

theorem fun134 (H : HookParams) (hst : (cH H).silentTotal) : EntailsAtValues (cH H) U.ax134 (trS U.ax134).pat := by
  rw [(by decide +kernel : (trS U.ax134).pat = (trAxiom [] [] U.ax134).pat)]
  exact LibEv.functional_ev (coreOKH H) (shapesOKH H) (k := ⟨floatIsInfinite, [Srt.float], Srt.bool⟩) (by decide +kernel) (Or.inr (Or.inl ⟨by decide, hst⟩))
    (by decide +kernel) U.ax134 (by decide +kernel) (by decide +kernel)

theorem fun143 (H : HookParams) (hst : (cH H).silentTotal) : EntailsAtValues (cH H) U.ax143 (trS U.ax143).pat := by
  rw [(by decide +kernel : (trS U.ax143).pat = (trAxiom [] [] U.ax143).pat)]
  exact LibEv.functional_ev (coreOKH H) (shapesOKH H) (k := ⟨floatIsNaN, [Srt.float], Srt.bool⟩) (by decide +kernel) (Or.inr (Or.inl ⟨by decide, hst⟩))
    (by decide +kernel) U.ax143 (by decide +kernel) (by decide +kernel)

theorem fun159 (H : HookParams) : EntailsAtValues (cH H) U.ax159 (trS U.ax159).pat := by
  rw [(by decide +kernel : (trS U.ax159).pat = (trAxiom [] [] U.ax159).pat)]
  exact LibEv.functional_ev (coreOKH H) (shapesOKH H) (k := ⟨floatPrecision, [Srt.float], Srt.int⟩) (by decide +kernel) (Or.inr (Or.inr ⟨by decide, floatShapeOKH H⟩))
    (by decide +kernel) U.ax159 (by decide +kernel) (by decide +kernel)

theorem fun173 (H : HookParams) (hst : (cH H).silentTotal) : EntailsAtValues (cH H) U.ax173 (trS U.ax173).pat := by
  rw [(by decide +kernel : (trS U.ax173).pat = (trAxiom [] [] U.ax173).pat)]
  exact LibEv.functional_ev (coreOKH H) (shapesOKH H) (k := ⟨floatTrunc, [Srt.float], Srt.float⟩) (by decide +kernel) (Or.inr (Or.inl ⟨by decide, hst⟩))
    (by decide +kernel) U.ax173 (by decide +kernel) (by decide +kernel)

end KCore.LibEvFloatFlt

/-- info: 'KCore.LibEvFloatFlt.ev254' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFloatFlt.ev254
/-- info: 'KCore.LibEvFloatFlt.ev254_lib' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFloatFlt.ev254_lib
/-- info: 'KCore.LibEvFloatFlt.ev321' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFloatFlt.ev321
/-- info: 'KCore.LibEvFloatFlt.ev321_lib' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFloatFlt.ev321_lib
/-- info: 'KCore.LibEvFloatFlt.fun25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFloatFlt.fun25
/-- info: 'KCore.LibEvFloatFlt.fun103' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFloatFlt.fun103
/-- info: 'KCore.LibEvFloatFlt.fun108' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFloatFlt.fun108
/-- info: 'KCore.LibEvFloatFlt.fun117' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFloatFlt.fun117
/-- info: 'KCore.LibEvFloatFlt.fun119' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFloatFlt.fun119
/-- info: 'KCore.LibEvFloatFlt.fun134' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFloatFlt.fun134
/-- info: 'KCore.LibEvFloatFlt.fun143' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFloatFlt.fun143
/-- info: 'KCore.LibEvFloatFlt.fun159' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFloatFlt.fun159
/-- info: 'KCore.LibEvFloatFlt.fun173' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFloatFlt.fun173
