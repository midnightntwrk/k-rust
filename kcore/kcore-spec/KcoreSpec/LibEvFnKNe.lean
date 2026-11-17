/-
  KCore, checked layer: domains.md 2355 (K 7.1.337), `K1 =/=K K2 => notBool (K1 ==K K2)`, a library
  equation in the function form (`LibEv.FnEqn`) over two variables of the sort K, entailed at values
  in every semantics meeting `coreOK`, for every interpretation.

  `=/=K` and `==K` are interpreted at every pair of values (`hook` gives each the Bool of the
  values' comparison), and `notBool` at every Bool, so neither side reaches a silent point and the
  equation holds of every pair of values; no shape of the values is read.
  - `fnNeK`: the equation; `fnNeK_holds`: it holds of the values; `fnNeK_ev`: entailed at values,
    for any axiom declaration of a text whose pattern is `fnNeK.patR`.
-/
import KcoreSpec.LibEvFnLib

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

section
variable {c : Semantics}

theorem fhv_kEq (v w : GroundTerm) : c.hv kEq [v, w] = some (bool (GroundTerm.cmp v w == .eq)) :=
  hv_of_value rfl
theorem fhv_kNe (v w : GroundTerm) : c.hv kNe [v, w] = some (bool (GroundTerm.cmp v w != .eq)) :=
  hv_of_value rfl

end

/-! ## 2355: `K1 =/=K K2 => notBool (K1 ==K K2)` -/

def fnNeK : FnEqn :=
  ⟨[("VarK1", Srt.k), ("VarK2", Srt.k)], kNe, [(Srt.k, .var 0, none), (Srt.k, .var 1, none)], Srt.bool,
    none, .app boolNot [.app kEq [.var 0, .var 1]]⟩

theorem fnNeK_holds (c : Semantics) : fnNeK.Holds c := by
  intro σ hσ _ hm
  obtain ⟨x, hx, -⟩ := hσ 0 ("VarK1", Srt.k) rfl
  obtain ⟨y, hy, -⟩ := hσ 1 ("VarK2", Srt.k) rfl
  obtain ⟨h2, -, h3, -⟩ := hm
  rw [fq_val_var] at h2 h3
  have h2' : σ.lookup 2 = some x := h2.symm.trans hx
  have h3' : σ.lookup 3 = some y := h3.symm.trans hy
  fq_eval [fnNeK, h2', h3', hx, hy, fhv_kNe, fhv_kEq, fhv_boolNot]
  rfl

theorem fnNeK_ev {c : Semantics} (h : c.coreOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnNeK.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnNeK (by decide) (by rfl) (fnNeK_holds c) ad hp hsv

end LibEv

end KCore
