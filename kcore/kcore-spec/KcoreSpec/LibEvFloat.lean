/-
  KCore, checked layer: FLOAT's library sentence 1648 (domains.md, K 7.1.337),
  `F1 =/=Float F2 => notBool (F1 ==Float F2)`, entailed at values (`EntailsAtValues`) in every
  semantics meeting `coreOK`, for every interpretation meeting `Semantics.neFloatEq`.

  Both sides read the two Floats through `==Float` and `=/=Float`, whose values are stated at every
  pair of data (domains.md 1631-1638 and 1541: the comparison of the exact values, the zeros equal,
  a NaN unequal to every datum), so the sentence's value reads no clause of an operation that the
  text takes from IEEE 754 by name. Where `hook` gives `=/=Float` a value it gives `==Float` one
  too, and the first is the negation of the second (`flCmp` at complementary tests). Where it gives
  `=/=Float` none, the left side is at a silent point and `neFloatEq` is the sentence there.
-/
import KcoreSpec.LibEvStr

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-- 1648: `F1 =/=Float F2 => notBool (F1 ==Float F2)`. -/
def fnNeFloat : FnEqn :=
  ⟨[("VarF1", Srt.float), ("VarF2", Srt.float)], floatNe,
    [(Srt.float, .var 0, none), (Srt.float, .var 1, none)], Srt.bool, none,
    .app boolNot [.app floatEq [.var 0, .var 1]]⟩

/-- `=/=Float` and `==Float` at two values, by `hook`: complementary where `=/=Float` has a value. -/
theorem flt_ne_eq {c : Semantics} (a b : GroundTerm) (h : hook floatNe [a, b] ≠ some none) :
    c.hv floatNe [a, b] = (c.hv floatEq [a, b]).bind fun v => c.hv boolNot [v] := by
  have h1 : hook floatNe [a, b] = some (flCmp (fun o => o != some .eq) [a, b]) := rfl
  have h2 : hook floatEq [a, b] = some (flCmp (fun o => o == some .eq) [a, b]) := rfl
  cases ha : asDatum a with
  | none => exact absurd (by rw [h1]; simp [flCmp, ha]) h
  | some u =>
    cases hb : asDatum b with
    | none => exact absurd (by rw [h1]; simp [flCmp, ha, hb]) h
    | some w =>
      have e1 : hook floatNe [a, b] = some (some (bool (KFloat.cmpExact u w != some .eq))) := by
        rw [h1]; simp [flCmp, ha, hb]
      have e2 : hook floatEq [a, b] = some (some (bool (KFloat.cmpExact u w == some .eq))) := by
        rw [h2]; simp [flCmp, ha, hb]
      rw [hv_of_value e1, hv_of_value e2, Option.bind_some, fhv_boolNot]
      rfl

/-- **1648 holds of the values where the interpretation meets `neFloatEq`.** -/
theorem fnNeFloat_holds {c : Semantics} (hc : c.neFloatEq) : fnNeFloat.Holds c := by
  intro σ hσ _ hm
  obtain ⟨a, ha, sa⟩ := hσ 0 ("VarF1", Srt.float) rfl
  obtain ⟨b, hb, sb⟩ := hσ 1 ("VarF2", Srt.float) rfl
  obtain ⟨h2, -, h3, -⟩ := hm
  have h2' : σ.lookup 2 = some a := st_arg h2 ha
  have h3' : σ.lookup 3 = some b := st_arg h3 hb
  have hl : val c σ fnNeFloat.lhs = c.hv floatNe [a, b] := by fq_eval [fnNeFloat, h2', h3']
  have hr : val c σ fnNeFloat.rhs = (c.hv floatEq [a, b]).bind fun v => c.hv boolNot [v] := by
    show val c σ (.app boolNot [.app floatEq [.var 0, .var 1]]) = _
    simp only [val, valList, allSome, ha, hb, Option.bind_some, Option.map_some]
    cases c.hv floatEq [a, b] <;> rfl
  rw [hl, hr]
  by_cases hs : hook floatNe [a, b] = some none
  · exact hc a b (sortsOf_cons.mpr ⟨_, _, sa, sortsOf_cons.mpr ⟨_, _, sb, sortsOf_nil, rfl⟩, rfl⟩) hs
  · exact flt_ne_eq a b hs

/-- **domains.md 1648** is entailed at values, for an interpretation meeting `neFloatEq`. -/
theorem fnNeFloat_ev {c : Semantics} (h : c.coreOK = true) (hc : c.neFloatEq) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnNeFloat.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnNeFloat (by decide) (by rfl) (fnNeFloat_holds hc) ad hp hsv

end LibEv

end KCore
