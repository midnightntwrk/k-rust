/-
  KCore. The value model with one unary function read as a set of values.

  `stdIOver c T n S` is the value model at `T` with the application of the head of the name `n`
  replaced: at a value `w` it gives the elements `S w`, and nothing at an element that is no value.
  It is `GenEqs.stdPatch` at the one name `n`. The head of a name is spare in the value model for
  any name (`GenEqs.spare_stdI`), a symbol of the semantics among them, so:

  - `interpret_over`: a rooted pattern that does not hold the symbol `n` (`AvoidsFn`) denotes in
    `stdIOver` what it denotes in the value model, at every valuation; `sat_over_iff` for its truth.
    Every premise of the theory is rooted (`GenEqs.rooted_of_decided`).
  - `over_call`: the symbol `n` applied to a pattern that avoids `n` denotes the elements `S w` at
    the values `w` the pattern denotes in the value model.
  - `over_defOK`: `⌈_⌉` is definedness in `stdIOver`.
  - `consistent_of_over`: the theory is consistent where the value model at its own step satisfies
    every item but the equations of the function `f` (`sat_off`), every premise that is not one of
    `f`'s own items (`FnOwn`: its equations and its arity item) avoids the name `n`
    (`AvoidsOff`), and `f`'s own items hold in `stdIOver`.

  The head alone is patched, so the function takes one argument: a partial application of a symbol
  of two or more arguments is an element that application gives, and is not spare.
-/
import KcoreSpec.ModelSatOff
import KcoreSpec.GenEqsWalk

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics} {T : GroundTerm → GroundTerm → Prop}

/-- The application of a head at a value `w`: the elements `S w`; nothing at an element that is no
value. -/
def overApp (S : GroundTerm → Set Elem) : Elem → Elem → Set Elem :=
  fun _ b m => ∃ w, b = .val w ∧ S w m

/-- **The value model at `T` with the symbol named `n` read as `S`**: the head of `n` applied to
the value `w` is the set `S w`. The other symbols, and application elsewhere, are the value
model's. -/
def stdIOver (c : Semantics) (T : GroundTerm → GroundTerm → Prop) (n : String)
    (S : GroundTerm → Set Elem) : Interpretation KoreAML.Sym Elem :=
  GenEqs.stdPatch c T (· = n) (overApp S)

/-- The pattern does not hold the symbol named `n`. -/
def AvoidsFn (n : String) (φ : KoreAML.P) : Prop := KoreAML.Sym.symbol n ∉ psyms φ

/-- **A rooted pattern that avoids `n` has one denotation in `stdIOver` and in the value model**, at
every valuation. -/
theorem interpret_over {n : String} {S : GroundTerm → Set Elem} {φ : KoreAML.P}
    (hr : GenEqs.rootedB φ = true) (hφ : AvoidsFn n φ) (ρ : Valuation Elem) :
    φ.interpret (stdIOver c T n S) ρ = φ.interpret (stdI_T c T) ρ :=
  GenEqs.stdPatch_interpret c T (· = n) (overApp S) hr (fun m hm => by subst hm; exact hφ) ρ

/-- A rooted pattern that avoids `n` holds in `stdIOver` exactly where it holds in the value
model. -/
theorem sat_over_iff {n : String} {S : GroundTerm → Set Elem} {φ : KoreAML.P}
    (hr : GenEqs.rootedB φ = true) (hφ : AvoidsFn n φ) :
    (stdIOver c T n S ⊧ᴵ φ) ↔ (stdI_T c T ⊧ᴵ φ) := by
  constructor
  · intro h ρ m
    have h' : φ.interpret (stdIOver c T n S) ρ m := h ρ m
    rwa [interpret_over hr hφ ρ] at h'
  · intro h ρ m
    show φ.interpret (stdIOver c T n S) ρ m
    rw [interpret_over hr hφ ρ]
    exact h ρ m

/-- **The symbol `n` applied to a pattern, in `stdIOver`**: the elements `S w` at the values `w`
the pattern denotes in the value model, where the symbol named `n` holds of its head only
(`spareSymB`: it is no constant) and the pattern is rooted and avoids `n`. -/
theorem over_call {n : String} {S : GroundTerm → Set Elem} (hsym : GenEqs.spareSymB c n = true)
    {ψ : KoreAML.P} (hr : GenEqs.rootedB ψ = true) (hψ : AvoidsFn n ψ) (ρ : Valuation Elem) (m : Elem) :
    (symP n ⬝ ψ).interpret (stdIOver c T n S) ρ m ↔
      ∃ w, ψ.interpret (stdI_T c T) ρ (.val w) ∧ S w m := by
  refine (GenEqs.stdPatch_app c T (· = n) (overApp S) rfl hsym hr
    (fun m hm => by subst hm; exact hψ) ρ m).trans ?_
  constructor
  · rintro ⟨b, hb, w, rfl, hS⟩
    exact ⟨w, hb, hS⟩
  · rintro ⟨w, hb, hS⟩
    exact ⟨_, hb, w, rfl, hS⟩

/-- `stdIOver` satisfies the definedness axiom. -/
theorem over_definedness (n : String) (S : GroundTerm → Set Elem) (x : EVar) :
    stdIOver c T n S ⊧ᴵ @definedness KoreAML.Sym _ x := by
  refine (sat_over_iff ?_ ?_).mpr (AtT.model_sat_definedness c x)
  · simp [definedness, Pattern.universal, Pattern.negation]
  · exact GenEqs.NameFree.cleanN_spec (ns := [n])
      (by simp [definedness, Pattern.universal, Pattern.negation]) (List.mem_singleton.mpr rfl)

/-- `⌈_⌉` is definedness in `stdIOver`. -/
theorem over_defOK (n : String) (S : GroundTerm → Set Elem) : KoreAML.DefOK (stdIOver c T n S) :=
  KoreAML.defOK_of fun x => over_definedness n S x

/-- **The own items of the function `f`**: the patterns of its equations and of its arity item. -/
def FnOwn (c : Semantics) (f : Sym) (φ : KoreAML.P) : Prop :=
  (∃ fn ∈ c.fns, fn.label = f ∧ ∃ it ∈ kernelItems (fnEquationsK c fn), φ = it.pat) ∨
  (∃ fn ∈ c.allFns, fn.label = f ∧ φ = (symArityItem c fn.sig).pat)

/-- **Every premise of the theory that is not one of `f`'s own items avoids the name `n`.** -/
def AvoidsOff (c : Semantics) (f : Sym) (n : String) : Prop :=
  ∀ φ, φ ∈ (Γc c ∪ Γstep c) → ¬ FnOwn c f φ → AvoidsFn n φ

/-- **The theory is consistent where the function `f` is read as a set of values**: for a
semantics `coreOKEx` accepts whose functions have one result (`FnDet`), where evaluation solves the
equations of every function of the definition but `f` (`FnSolvesAt`), the clauses' predicates have
truth values and the open generators meet their laws, every premise that is not one of `f`'s own
items avoids the name `n` (`AvoidsOff`), and `f`'s own items hold in the value model at its own
step with `n` read as `S`. That model satisfies the other premises because the value model does
(`sat_off`) and they denote the same in both (`sat_over_iff`). -/
theorem consistent_of_over {f : Sym} {n : String} {S : GroundTerm → Set Elem}
    (h : c.coreOKEx = true) (hd : FnDet c) (hs : ∀ g ∈ c.fns, g.label ≠ f → FnSolvesAt c g)
    (hp : ClausePreDecided c) (hq : ClausePostDecided c) (hl : OpenLaws c)
    (hav : AvoidsOff c f n)
    (hown : ∀ φ, φ ∈ (Γc c ∪ Γstep c) → FnOwn c f φ → stdIOver c (StepV c) n S ⊧ᴵ φ) :
    Consistent c :=
  ⟨Elem, inferInstance, stdIOver c (StepV c) n S, fun φ hφ => by
    by_cases ho : FnOwn c f φ
    · exact hown φ hφ ho
    · refine (sat_over_iff (GenEqs.rooted_of_decided c (GenEqs.rootedListsB_holds c) φ hφ)
        (hav φ hφ ho)).mpr ?_
      refine sat_off (D := [f]) h hd
        (fun fn hfn hD => hs fn hfn (fun he => hD (List.mem_singleton.mpr he))) hp hq hl φ hφ ?_
      intro fn hfn hD it hit he
      exact ho (.inl ⟨fn, hfn, List.mem_singleton.mp hD, it, hit, he⟩)⟩

end Model

end Faithful

end KCore
