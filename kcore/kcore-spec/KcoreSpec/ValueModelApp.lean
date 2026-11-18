/-
  KCore. A function's application to values, read in the value model.

  In the value model at any transition `T` (`stdI_T c T`; `consistent_ofCl`'s model is the one at
  `StepV c`), the application `f(vs)` of a function `f` of `c` to as many values `vs` as it has
  arguments, each of some sort, denotes the elements of the values `v` with `Eval c f vs (some v)`
  (`vmApp_fn_iff`): the symbol's application is `symAt`, which at all its arguments is `result`,
  and `result` at a function is the set of `Eval`'s values. The values need not be of the
  function's argument sorts; their sorts are read only for each to denote its own element, and
`HypModelCore` only for the names and that reading. On the elements themselves the statement
needs the names apart alone (`vmSymE_fn_iff`).

  With one result per argument list (`FnDet`) that set is one element where `Eval` has a value
  (`vmApp_fn_eq`) and empty where `Eval` is undefined (`vmApp_fn_empty`); it is empty as well where
  `Eval` has no result at all (`vmApp_fn_iff` directly).

  The model at `StepV c` satisfies `Γc c` with the step's closure under `consistent_ofCl`'s
  hypotheses (`vmModelCl`), so the theory does not entail that `f(vs)` is a value other than the
  one `Eval` gives (`vmApp_fn_not_entailed`), nor that it is empty where `Eval` gives a value
  (`vmApp_fn_not_bot`).
-/
import KcoreSpec.OpenClauseConsistent
import KcoreSpec.TiePairs

set_option autoImplicit false

namespace KCore

open ML Faithful Faithful.Model

variable {c : Semantics}

/-- **A function symbol applied to the elements of values, in the value model**: at any
transition `T`, the symbol named as `k`, for `k` a symbol of the semantics that is no constructor,
no interpreted hook, no parameter and no overloading symbol, applied to the elements of as many
values as `k` has arguments, is the set of the elements of the values `Eval` gives it there.
Nothing is read of the values' sorts, nor of the functions. -/
theorem vmSymE_fn_iff (hn : NamesApartK c) (T : GroundTerm → GroundTerm → Prop) {k : CtorSig} (hk : k ∈ kernelSyms c)
    (hc : c.isCtor k.name = false) (hh : isHook k.name = false) (hp : c.isParam k.name = false)
    (ho : c.isOvl k.name = false) {vs : List GroundTerm} (hl : vs.length = k.args.length) (m : Elem) :
    SymE (stdI_T c T) (c.symName k.name) (vs.map Elem.val) m ↔ ∃ v, m = .val v ∧ Eval c k.name vs (some v) := by
  rw [AtT.symE_vals hn hk hl, result_fn hc hh hp ho]

/-- **A function applied to values, in the value model**: at any transition `T`, `⟦f(vs)⟧` for a
function `f` of `c` and as many values as `f` has arguments, each of some sort, is the set of the
elements of the values `Eval` gives `f` at `vs`. -/
theorem vmApp_fn_iff (h : HypModelCore c) (T : GroundTerm → GroundTerm → Prop) {fn : Fn} (hfn : fn ∈ c.allFns)
    {vs : List GroundTerm} {ss : List Srt} (hvs : c.sortsOf vs = some ss) (hl : vs.length = fn.args.length)
    (e : Valuation Elem) (m : Elem) :
    (TiePair.app c fn.label vs).interpret (stdI_T c T) e m ↔ ∃ v, m = .val v ∧ Eval c fn.label vs (some v) := by
  obtain ⟨hc, hh, hp⟩ := h.fnApart hfn
  unfold TiePair.app
  rw [show fn.label = fn.sig.name from rfl, AtT.symApp_val h (fn_sig_mem hfn) hvs hl,
    result_fn (k := fn.sig) hc hh hp (c.isOvl_of_lookupFn (h.lookupFn hfn))]

/-- Where `Eval` gives `f` the value `v` at `vs`, `⟦f(vs)⟧` in the value model is the element of
`v` alone: `FnDet`, which `HypModelCore` holds, makes `v` the only result. -/
theorem vmApp_fn_eq (h : HypModelCore c) (T : GroundTerm → GroundTerm → Prop) {fn : Fn} (hfn : fn ∈ c.allFns)
    {vs : List GroundTerm} {ss : List Srt} (hvs : c.sortsOf vs = some ss) (hl : vs.length = fn.args.length)
    {v : GroundTerm} (hE : Eval c fn.label vs (some v)) (e : Valuation Elem) (m : Elem) :
    (TiePair.app c fn.label vs).interpret (stdI_T c T) e m ↔ m = .val v := by
  rw [vmApp_fn_iff h T hfn hvs hl]
  constructor
  · rintro ⟨w, rfl, hw⟩
    cases h.det _ _ _ _ hw hE
    rfl
  · intro hm
    exact ⟨v, hm, hE⟩

/-- Where `Eval` gives `f` no value at `vs` (it is undefined there), `⟦f(vs)⟧` in the value model
is empty: `FnDet`, which `HypModelCore` holds, leaves no other result. -/
theorem vmApp_fn_empty (h : HypModelCore c) (T : GroundTerm → GroundTerm → Prop) {fn : Fn} (hfn : fn ∈ c.allFns)
    {vs : List GroundTerm} {ss : List Srt} (hvs : c.sortsOf vs = some ss) (hl : vs.length = fn.args.length)
    (hE : Eval c fn.label vs none) (e : Valuation Elem) (m : Elem) :
    ¬ (TiePair.app c fn.label vs).interpret (stdI_T c T) e m := by
  rw [vmApp_fn_iff h T hfn hvs hl]
  rintro ⟨w, -, hw⟩
  cases h.det _ _ _ _ hw hE

/-- **The value model at its own step satisfies `Γc c` with the step's closure**, under
`consistent_ofCl`'s hypotheses: the model `consistent_ofCl` gives, named. -/
theorem vmModelCl (c : Semantics) (hok : c.sortedOKCl = true) (hsr : c.srReady = true) [hov : OvlOK c]
    (hfa : c.faithCoreOK = true) (hph : patHooksApart c = true) (hids : c.idsOK = true)
    (hd : FnDet c) (hs : FnSolves c) (hp : ClausePreDecided c) (hl : OpenLaws c) :
    stdI_T c (StepV c) ⊧ᴵP (Γc c ∪ Γstep c) := by
  have hm := hypModel_ofCl hok hsr hov hfa hph hids hd hs
  intro φ hφ
  rcases hφ with (hφ | hφ) | hφ
  · exact stdI_V_model_core hm hp hl φ (Or.inl hφ)
  · obtain ⟨-, hlit, rfl⟩ := hφ
    exact boolClosed_modelClT hm hlit
  · exact stdI_V_model_core hm hp hl φ (Or.inr hφ)

/-- **The theory does not entail another value of `f(vs)` than `Eval`'s**: under
`consistent_ofCl`'s hypotheses, where `Eval` gives `f` the value `v` at `vs` and `w` is another
value of some sort, `Γc c` with the step's closure does not entail `f(vs) = w`. The value model
at `StepV c` is a model in which `f(vs)` is `v`. -/
theorem vmApp_fn_not_entailed (c : Semantics) (hok : c.sortedOKCl = true) (hsr : c.srReady = true) [hov : OvlOK c]
    (hfa : c.faithCoreOK = true) (hph : patHooksApart c = true) (hids : c.idsOK = true)
    (hd : FnDet c) (hs : FnSolves c) (hp : ClausePreDecided c) (hl : OpenLaws c)
    {fn : Fn} (hfn : fn ∈ c.allFns) {vs : List GroundTerm} {ss : List Srt} (hvs : c.sortsOf vs = some ss)
    (hlen : vs.length = fn.args.length) {v w : GroundTerm} (hE : Eval c fn.label vs (some v))
    {s : Srt} (hw : c.sortOf w = some s) (hne : v ≠ w) :
    ¬ ((Γc c ∪ Γstep c) ⊧ (TiePair.app c fn.label vs ≡ den c w)) := by
  intro hent
  have hm := hypModel_ofCl hok hsr hov hfa hph hids hd hs
  have h1 := hent (vmModelCl c hok hsr hfa hph hids hd hs hp hl) KoreAML.val0 (.val v)
  rw [KoreAML.interp_equal AtT.defOK_std] at h1
  have h2 := (h1 (.val v)).mp ((vmApp_fn_eq hm _ hfn hvs hlen hE _ _).mpr rfl)
  rw [den_val_T hm _ w hw] at h2
  cases h2
  exact hne rfl

/-- **The theory does not entail that `f(vs)` is empty where `Eval` gives a value**: under
`consistent_ofCl`'s hypotheses, `Γc c` with the step's closure does not entail `f(vs) = ⊥`. -/
theorem vmApp_fn_not_bot (c : Semantics) (hok : c.sortedOKCl = true) (hsr : c.srReady = true) [hov : OvlOK c]
    (hfa : c.faithCoreOK = true) (hph : patHooksApart c = true) (hids : c.idsOK = true)
    (hd : FnDet c) (hs : FnSolves c) (hp : ClausePreDecided c) (hl : OpenLaws c)
    {fn : Fn} (hfn : fn ∈ c.allFns) {vs : List GroundTerm} {ss : List Srt} (hvs : c.sortsOf vs = some ss)
    (hlen : vs.length = fn.args.length) {v : GroundTerm} (hE : Eval c fn.label vs (some v)) :
    ¬ ((Γc c ∪ Γstep c) ⊧ (TiePair.app c fn.label vs ≡ ⊥)) := by
  intro hent
  have hm := hypModel_ofCl hok hsr hov hfa hph hids hd hs
  have h1 := hent (vmModelCl c hok hsr hfa hph hids hd hs hp hl) KoreAML.val0 (.val v)
  rw [KoreAML.interp_equal AtT.defOK_std] at h1
  have h2 := (h1 (.val v)).mp ((vmApp_fn_eq hm _ hfn hvs hlen hE _ _).mpr rfl)
  simp at h2

end KCore
