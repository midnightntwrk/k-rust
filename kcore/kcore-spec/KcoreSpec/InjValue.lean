/-
  Injections at values, in a model of `Γ` of a definition with `coreOK`. For a subsort pair (a, b)
  of the definition, `inj{a,b}` at an element of a is one element of b (`inj_defined`), and an
  element of a whose injection is the element of a value v of b is the element of a value w of a,
  with v the injection of w (`inj_value`); w is the only such value (`inj_value_unique`).
  `inj_value_at` and `inj_value_pat` state the same from an element that the pattern `inj{a,b}(x)`
  and `den v` share, and `inj_no_element` the consequence where no value of a injects to v: no
  element of a does. `sortOfTerm_inj_var` and `condOK_inj_equals` are what `condOK` decides of an
  injected variable equated with a term.

  Nothing is assumed beyond `coreOK`, the model and the pair among `c.subsorts`.
-/
import KcoreSpec.HypWf
import KcoreSpec.Confined

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace CE

/-- What `condOK` decides of an injected variable: the pair is a subsort pair of the context and
the variable has the lower sort. -/
theorem sortOfTerm_inj_var {x : TermCtx} {vs : List Srt} {a b s : Srt} {j : Nat}
    (h : sortOfTerm x vs (.inj a b (.var j)) = some s) :
    x.subs.contains (a, b) = true ∧ vs[j]? = some a ∧ s = b := by
  rw [sortOfTerm] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    have hv : vs[j]? = some a := by simpa [sortOfTerm] using hc.2
    exact ⟨hc.1, hv, (Option.some.inj h).symm⟩
  · cases h

/-- `condOK` of `inj{a,b}(Z) = u` gives the pair among `c.subsorts` and Z the sort a. -/
theorem condOK_inj_equals {c : Semantics} {vars : List Srt} {s a b : Srt} {j : Nat} {u : Term}
    (h : c.condOK vars (.equals s (.inj a b (.var j)) u) = true) :
    c.subsorts.contains (a, b) = true ∧ vars[j]? = some a ∧ s = b := by
  simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq] at h
  exact sortOfTerm_inj_var h.1.1

section InjValue
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

theorem injValue_subsorts_trans (h : c.coreOK = true) :
    ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts := by
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := hypSound_of_core h
  exact (sortCtx_of_all hok hsr (OvlOK.ovlCase hno)).trans

/-- **An injection is defined at every element of its source sort**: `inj{a,b}(e)` is one element
of b, never ⊥ (Cons-Fun of the generator `inj a` of b). -/
theorem inj_defined (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {a b : Srt} (hab : c.subsorts.contains (a, b) = true)
    {e : M} (he : InS I (c.sortName a) e) :
    ∃ y, InS I (c.sortName b) y ∧ ∀ m, GS I (c.sortName b) (.inj (c.sortName a)) [e] m ↔ m = y := by
  obtain ⟨-, -, -, hg, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hab' : (a, b) ∈ c.subsorts := by simpa using hab
  exact gen_fun hI (genWf_sub hg hab').1 (gensF_inj hab') rfl (xs := [e]) rfl (single_sorts he)

/-- **`inj_value`.** In a model of `Γ` of a definition with `coreOK`, for a subsort pair (a, b): an
element e of a whose injection is the element of a value v of b is the element of a value w of a,
and v is w's injection. -/
theorem inj_value (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {a b : Srt} (hab : c.subsorts.contains (a, b) = true)
    {v : GroundTerm} (hv : c.sortOf v = some b) {e : M} (he : InS I (c.sortName a) e)
    (hm : GS I (c.sortName b) (.inj (c.sortName a)) [e] (elemOf c I v)) :
    ∃ w, c.sortOf w = some a ∧ v = injNormal a b w ∧ e = elemOf c I w := by
  obtain ⟨-, -, -, hg, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  exact inj_back hI hg (injValue_subsorts_trans h) v (by simpa using hab) hv he hm

/-- The value of `inj_value` is the only one: `injNormal a b` is injective on the values of a. -/
theorem inj_value_unique (h : c.coreOK = true) {a b : Srt} {w w' : GroundTerm}
    (hw : c.sortOf w = some a) (hw' : c.sortOf w' = some a) (he : injNormal a b w = injNormal a b w') : w = w' := by
  obtain ⟨-, -, -, hg, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  exact injNormal_inj hg hw hw' he

/-- `inj_value` in `confined_value`'s shape, from an element the injection and the value share
(what `\equals` and `\in` both give, each side being one element). -/
theorem inj_value_at (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {a b : Srt} (hab : c.subsorts.contains (a, b) = true)
    {v : GroundTerm} (hv : c.sortOf v = some b) (ρ : Valuation M) (e : M)
    (he : (KoreAML.inhOf (sortP (c.sortName a))).interpret I ρ e)
    (hm : ∃ m, GS I (c.sortName b) (.inj (c.sortName a)) [e] m ∧ (den c v).interpret I ρ m) :
    ∃ w, c.sortOf w = some a ∧ v = injNormal a b w ∧ ∀ m, (den c w).interpret I ρ m ↔ m = e := by
  obtain ⟨m, hgs, hd⟩ := hm
  have hmv : m = elemOf c I v := ((elemOf_spec hI hv ρ).1 m).mp hd
  subst hmv
  obtain ⟨w, hw, hvw, rfl⟩ := inj_value h hI hab hv ((inS_iff ρ).mp he) hgs
  exact ⟨w, hw, hvw, (elemOf_spec hI hw ρ).1⟩

/-- The same over the pattern `inj{a,b}(x)`, x a pattern that is the one element e (a variable). -/
theorem inj_value_pat (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {a b : Srt} (hab : c.subsorts.contains (a, b) = true)
    {v : GroundTerm} (hv : c.sortOf v = some b) (ρ : Valuation M) (e : M) (x : KoreAML.P)
    (hx : ∀ m, x.interpret I ρ m ↔ m = e)
    (he : (KoreAML.inhOf (sortP (c.sortName a))).interpret I ρ e)
    (hm : ∃ m, (KoreAML.appList (KoreAML.sym (.symbol "inj"))
        [KoreAML.Cons.sortP (c.sortName a), KoreAML.Cons.sortP (c.sortName b), x]).interpret I ρ m ∧
      (den c v).interpret I ρ m) :
    ∃ w, c.sortOf w = some a ∧ v = injNormal a b w ∧ ∀ m, (den c w).interpret I ρ m ↔ m = e := by
  obtain ⟨m, hinj, hd⟩ := hm
  obtain ⟨x', hx', hgs⟩ := (interp_injApp _ _ x m).mp hinj
  have : x' = e := (hx x').mp hx'
  subst this
  exact inj_value_at h hI hab hv ρ x' he ⟨m, hgs, hd⟩

/-- **Where no value of a injects to v, no element of a does**: the union `∃Z:a. Z ∧ inj(Z) = v` is ⊥. -/
theorem inj_no_element (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {a b : Srt} (hab : c.subsorts.contains (a, b) = true)
    {v : GroundTerm} (hv : c.sortOf v = some b) (hno : ∀ w, c.sortOf w = some a → injNormal a b w ≠ v)
    {e : M} (he : InS I (c.sortName a) e) : ¬ GS I (c.sortName b) (.inj (c.sortName a)) [e] (elemOf c I v) := fun hm => by
  obtain ⟨w, hw, hvw, -⟩ := inj_value h hI hab hv he hm
  exact hno w hw hvw.symm

end InjValue

end CE

end KCore
