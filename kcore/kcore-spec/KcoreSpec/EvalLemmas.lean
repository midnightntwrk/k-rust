/-
  Inversion lemmas for F2's matching and evaluation relations (checked layer, generic in the
  semantics). Each states what one constructor of `PatVal` or `EvalTerm` can have produced for a
  term of a given head, so that a proof about a definition reads its rules by cases.
-/
import KcoreSpec.Step

set_option autoImplicit false

namespace KCore

variable {c : Semantics} {σ : Subst}

/-- A constructor's pattern (not a pattern hook) denotes exactly the terms of its constructor whose
arguments its argument patterns denote. -/
theorem PatVal.app_inv {f : Sym} {ps : List Term} {v : GroundTerm}
    (hf : patternHooks.contains f = false) (h : PatVal c σ (.app f ps) v) (hct : c.isCtor f = true) :
    c.isCtor f = true ∧ ∃ vs, v = .ctor f vs ∧ PatVals c σ ps vs := by
  generalize ht : Term.app f ps = t at h
  cases h with
  | ctor hc hs => cases ht; exact ⟨hc, _, rfl, hs⟩
  | hook hp _ _ => cases ht; rw [hf] at hp; cases hp
  | coll hc _ _ _ => cases ht; rw [hct] at hc; cases hc
  | ovl hc _ _ _ => cases ht; rw [hct] at hc; cases hc
  | _ => cases ht

theorem PatVal.var_inv {i : Nat} {v : GroundTerm} (h : PatVal c σ (.var i) v) : σ.lookup i = some v := by
  generalize ht : Term.var i = t at h
  cases h with
  | var h => cases ht; exact h
  | _ => cases ht

theorem PatVal.inj_inv {a b : Srt} {p : Term} {v : GroundTerm} (h : PatVal c σ (.inj a b p) v) :
    ∃ w, PatVal c σ p w ∧ v = injNormal a b w := by
  generalize ht : Term.inj a b p = t at h
  cases h with
  | inj h => cases ht; exact ⟨_, h, rfl⟩
  | _ => cases ht

theorem PatVal.as_inv {p : Term} {i : Nat} {v : GroundTerm} (h : PatVal c σ (.as p i) v) :
    PatVal c σ p v ∧ σ.lookup i = some v := by
  generalize ht : Term.as p i = t at h
  cases h with
  | as h hi => cases ht; exact ⟨h, hi⟩
  | _ => cases ht

theorem PatVals.nil_inv {vs : List GroundTerm} (h : PatVals c σ [] vs) : vs = [] := by
  cases h; rfl

theorem PatVals.cons_inv {p : Term} {ps : List Term} {vs : List GroundTerm}
    (h : PatVals c σ (p :: ps) vs) : ∃ v vs', vs = v :: vs' ∧ PatVal c σ p v ∧ PatVals c σ ps vs' := by
  cases h with
  | cons h hs => exact ⟨_, _, rfl, h, hs⟩

/-- A constructor application evaluates to the constructor term of its arguments' results. -/
theorem EvalTerm.ctor_inv {f : Sym} {ts : List Term} {r : Option GroundTerm}
    (hc : c.isCtor f = true) (h : EvalTerm c σ (.app f ts) r) :
    ∃ rs, EvalTerms c σ ts rs ∧ r = (allSome rs).map (.ctor f) := by
  generalize ht : Term.app f ts = t at h
  cases h with
  | ctor _ hts => cases ht; exact ⟨_, hts, rfl⟩
  | hook h _ _ _ _ => cases ht; rw [hc] at h; cases h
  | param h _ _ _ _ => cases ht; rw [hc] at h; cases h
  | call h _ _ _ _ _ => cases ht; rw [hc] at h; cases h
  | callUndef h _ _ _ _ => cases ht; rw [hc] at h; cases h
  | ovl h _ _ => cases ht; rw [hc] at h; cases h
  | _ => cases ht

/-- An application of a function (neither a constructor nor a hook nor a parameter nor an
overloading symbol) on defined arguments is a call. -/
theorem EvalTerm.call_inv {f : Sym} {ts : List Term} {r : Option GroundTerm}
    (hc : c.isCtor f = false) (hh : isHook f = false) (hp : c.isParam f = false) (ho : c.isOvl f = false)
    (h : EvalTerm c σ (.app f ts) r) :
    ∃ rs, EvalTerms c σ ts rs ∧
      ((∃ vs, allSome rs = some vs ∧ Eval c f vs r) ∨ (allSome rs = none ∧ r = none)) := by
  generalize ht : Term.app f ts = t at h
  cases h with
  | ctor h _ => cases ht; rw [hc] at h; cases h
  | hook _ h _ _ _ => cases ht; rw [hh] at h; cases h
  | param _ _ h _ _ => cases ht; rw [hp] at h; cases h
  | call _ _ hts hvs hf _ => cases ht; exact ⟨_, hts, .inl ⟨_, hvs, hf⟩⟩
  | callUndef _ _ hts hvs _ => cases ht; exact ⟨_, hts, .inr ⟨hvs, rfl⟩⟩
  | ovl _ h _ => cases ht; rw [ho] at h; cases h
  | _ => cases ht

/-- A parameter symbol's application has the value `paramVal` gives its arguments' results. -/
theorem EvalTerm.param_inv {f : Sym} {ts : List Term} {r : Option GroundTerm}
    (hc : c.isCtor f = false) (hh : isHook f = false) (hp : c.isParam f = true)
    (h : EvalTerm c σ (.app f ts) r) :
    ∃ rs, EvalTerms c σ ts rs ∧ r = (allSome rs).bind (c.paramVal f) := by
  generalize ht : Term.app f ts = t at h
  cases h with
  | param _ _ _ hts hr => cases ht; exact ⟨_, hts, hr⟩
  | call _ _ _ _ _ h => cases ht; rw [hp] at h; cases h
  | callUndef _ _ _ _ h => cases ht; rw [hp] at h; cases h
  | ctor h _ => cases ht; rw [hc] at h; cases h
  | hook _ h _ _ _ => cases ht; rw [hh] at h; cases h
  | ovl _ ho _ => cases ht; rw [(c.isOvl_parts ho).2.2.1] at hp; cases hp
  | _ => cases ht

/-- An overloading symbol's application has the normal form of its arguments' results. -/
theorem EvalTerm.ovl_inv {f : Sym} {ts : List Term} {r : Option GroundTerm}
    (ho : c.isOvl f = true) (h : EvalTerm c σ (.app f ts) r) :
    ∃ rs, EvalTerms c σ ts rs ∧ r = (allSome rs).map (c.norm f) := by
  have hp := c.isOvl_parts ho
  generalize ht : Term.app f ts = t at h
  cases h with
  | ovl _ _ hts => cases ht; exact ⟨_, hts, rfl⟩
  | callUndef _ _ hts hvs _ => cases ht; exact ⟨_, hts, by rw [hvs]; rfl⟩
  | ctor h _ => cases ht; rw [hp.1] at h; cases h
  | hook _ h _ _ _ => cases ht; rw [hp.2.1] at h; cases h
  | param _ _ h _ _ => cases ht; rw [hp.2.2.1] at h; cases h
  | call _ _ _ _ hf _ => cases ht; rw [hf.isOvl_false] at ho; cases ho
  | _ => cases ht

theorem EvalTerm.var_inv {i : Nat} {r : Option GroundTerm} (h : EvalTerm c σ (.var i) r) :
    r = σ.lookup i := by
  generalize ht : Term.var i = t at h
  cases h with
  | var => cases ht; rfl
  | _ => cases ht

theorem EvalTerm.inj_inv {a b : Srt} {t : Term} {r : Option GroundTerm}
    (h : EvalTerm c σ (.inj a b t) r) : ∃ r', EvalTerm c σ t r' ∧ r = r'.map (injNormal a b) := by
  generalize ht : Term.inj a b t = u at h
  cases h with
  | inj h => cases ht; exact ⟨_, h, rfl⟩
  | _ => cases ht

theorem EvalTerms.nil_inv {rs : List (Option GroundTerm)} (h : EvalTerms c σ [] rs) : rs = [] := by
  cases h; rfl

theorem EvalTerms.cons_inv {t : Term} {ts : List Term} {rs : List (Option GroundTerm)}
    (h : EvalTerms c σ (t :: ts) rs) :
    ∃ r rs', rs = r :: rs' ∧ EvalTerm c σ t r ∧ EvalTerms c σ ts rs' := by
  cases h with
  | cons h hs => exact ⟨_, _, rfl, h, hs⟩

/-- The result of evaluating a term under σ does not depend on the derivation: `EvalTerm` is
functional for constructor and variable terms, which is all the lemmas below need. -/
theorem allSome_singleton {r : Option GroundTerm} {vs : List GroundTerm} (h : allSome [r] = some vs) :
    ∃ v, r = some v ∧ vs = [v] := by
  cases r with
  | none => cases h
  | some v => exact ⟨v, rfl, by simpa [allSome] using h.symm⟩

end KCore
