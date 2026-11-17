/-
  KCore. The values of an open generator, read off `sortOf` and `paramVal` for any semantics: the
  hypotheses are about the symbol itself and nothing is assumed of the other parameters.

  - `Semantics.sortOf_open_iff`: the application of an open generator (a `raw` parameter that
    `lookupOpen` answers for) whose symbol is no constructor and no overloading symbol is a value
    exactly where its arguments have the generator's argument sorts and the interpretation leaves it
    raw (`keepsRaw`); its sort is then the generator's result sort.
  - `paramVal_raw_sorted`: at a `raw` parameter with no registry hook, `paramVal` is the
    interpretation's answer, or the raw application where it gives none, kept only where that has
    the declared result sort: a value of the result sort, or nothing.
  - `paramVal_raw_keep`: where the interpretation gives no answer at arguments of the argument
    sorts, an open generator's value is its raw application.

  Subject reduction's case for a parameter (`EvalTerm.param`, SubjectReduction.lean) reads only
  `paramVal_sorted`, which holds of every parameter, raw or not.
-/
import KcoreSpec.Evaluation

set_option autoImplicit false

namespace KCore

namespace Semantics
variable {c : Semantics}

/-- **An open generator's application is a value exactly where its arguments are values of its
argument sorts and the interpretation leaves it raw**, and then of its result sort. -/
theorem sortOf_open_iff {f : Sym} {k : ParamSig} {ts : List GroundTerm} {s : Srt}
    (hk : c.lookupOpen f = some k) (hc : lookupSig c.ctorSigs f = none) (ho : c.lookupOvl f = none) :
    c.sortOf (.ctor f ts) = some s ↔
      c.sortsOf ts = some k.sig.args ∧ c.keepsRaw f ts = true ∧ s = k.sig.result := by
  rw [Semantics.sortOf_ctor_iff]
  constructor
  · rintro (⟨k', hk', -⟩ | ⟨-, o, ho', -⟩ | ⟨-, -, k', hk', h1, h2, h3⟩)
    · rw [hc] at hk'; cases hk'
    · rw [ho] at ho'; cases ho'
    · rw [hk] at hk'; cases hk'; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact .inr (.inr ⟨hc, ho, k, hk, h1, h2, h3⟩)

end Semantics

variable {c : Semantics}

/-- **`paramVal` at a `raw` parameter with no registry hook**: the interpretation's answer, or the
raw application where it gives none, and only where that has the parameter's result sort. So its
value is a value of the result sort, or there is none. -/
theorem paramVal_raw_sorted {f : Sym} {k : ParamSig} {vs : List GroundTerm} {v : GroundTerm}
    (hk : c.lookupParam f = some k) (hraw : k.raw = true) (hi : k.impl = none) :
    c.paramVal f vs = some v ↔
      v = (c.hooks.app f vs).getD (.ctor f vs) ∧ c.sortOf v = some k.sig.result := by
  unfold Semantics.paramVal
  rw [hk]
  simp only [hi, hraw, ↓reduceIte, Option.filter_some]
  constructor
  · intro h
    split at h
    · rename_i hp
      cases h
      exact ⟨rfl, by simpa using hp⟩
    · cases h
  · rintro ⟨rfl, hs⟩
    simp [hs]

/-- **Where the interpretation gives no answer, an open generator's value is its raw application**,
at arguments of its argument sorts. -/
theorem paramVal_raw_keep {f : Sym} {k : ParamSig} {vs : List GroundTerm}
    (hk : c.lookupParam f = some k) (hi : k.impl = none) (hko : c.lookupOpen f = some k)
    (hc : lookupSig c.ctorSigs f = none) (ho : c.lookupOvl f = none)
    (hn : c.hooks.app f vs = none) (hvs : c.sortsOf vs = some k.sig.args) :
    c.paramVal f vs = some (.ctor f vs) := by
  have hraw := (c.lookupOpen_spec hko).2.1
  refine (paramVal_raw_sorted hk hraw hi).mpr ⟨by rw [hn]; rfl, ?_⟩
  exact (Semantics.sortOf_open_iff hko hc ho).mpr ⟨hvs, by simp [Semantics.keepsRaw, hn], rfl⟩

end KCore
