/-
  The tie on the two texts of a `non-executable` equation beside an `[owise]` one, over their own
  kompiled texts: fixture e5-owise-nonexec (`f2-examples/owisenx.kompile.kore`) and fixture
  e5-owise-nonexec-agree (`f2-examples/owisenxagree.kompile.kore`), each the fixture's cached
  `definition.kore` (sha256 in its `kompile.txt`) with its `Source` paths restored. Stated on the
  literal `defn` for every interpretation H. Run from the package root:
  `lake env lean -j1 test/NonExecOwiseTie.lean`. The generated packages of the two texts are
  checked by `test/nonexec-owise-gen.sh`.

  Axiom numbers are `AxiomDecl.index` (the `U.axN` constants); the fixture's `kore.txt` numbers the
  sentences of the user module (`//@ N`) and its account the sentences of the text.

  ## NX: e5-owise-nonexec, a text with no model

  ```
  rule choose(a, Y) => Y                    // axiom 97  (kore.txt //@ 194)
  rule choose(b, Y) => Y [non-executable]   // axiom 98  (//@ 195; the account's sentence 208)
  rule choose(X, _) => X [owise]            // axiom 96  (//@ 193): its premise negates axiom 97 alone
  ```

  - The reading (`wf_defn`, `coreOK`, `agree_named`): the core is accepted; the agreement of `choose`
    is the one named fact. The second clause is `aside` (`aside_b`), the `[owise]` clause's smaller
    clauses are the first alone (`lower_owise`).
  - Γ's items for `choose` are the text's sentences: those of A and B are the translations of axioms
    97 and 98, pattern for pattern (`choose_AB`: the `non-executable` equation as written); the
    `[owise]` one is not literally axiom 96's translation (`owise_not_literal`) but is it up to a
    renaming of element variables, free and bound, both ways (`fn_align`, over all 32 of Γ's
    equations against their sentences `fnText`; `alphaB`, `satisfies_of_alphaB`), with the one
    exclusion disjunct the text writes. So Γ entails each sentence of `fnText` (`fns_entailed`).
  - `Eval` at (b, a) gives `a` (the `aside` clause) and `b` (the `[owise]` clause), for every H
    (`eval_ba_a`, `eval_ba_b`); hence not `FnDet`, not `ClausesAgree` of `choose`, not `FnSolves`
    (the `aside` clause decides at (b, a) under Y := a, and `b` is a result that is not its right
    side's value), for every H.
  - **Γ has no model** (`no_model`), for every H: in a model of Γ, `choose(b, a)` denotes each `Eval`
    result (`eval_den4`, through `eval_some_sound_core`), so the elements of `a` and `b` are one,
    and distinct values are distinct elements (`values_apart`). Hence **not `Consistent`**
    (`not_consistent`).
  - Facts about `Eval`, kind "not a value of the text": its one result at (b, b) is `b` (`eval_bb`),
    at (a, y) it is `y` (`eval_ay`). The text has no model, so no value of `choose` is an
    expectation of this fixture at any point; these two say what `Eval` gives and nothing of the
    text.

  ## AG: e5-owise-nonexec-agree, the text of the pair that has a model

  ```
  rule choose(b, Y) => b [non-executable]   // axiom 96, read choose((b as V0), V1) = V0
  rule choose(a, Y) => Y                    // axiom 98
  rule choose(X, _) => X [owise]            // axiom 97: its premise negates axiom 98 alone
  ```
  - The same equalities: the items of B and A are axioms 96 and 98 pattern for pattern
    (`choose_BA`), all 32 equations their sentences up to a renaming of element variables
    (`fn_align`); `agree_named = [choose]`.
  - **`ClausesAgree` of `choose`, for every H** (`agree`): the two clauses of priority 50 never both
    apply (their first patterns are the constructors `b` and `a`), and where the `aside` clause and
    the `[owise]` clause both apply, both right sides are the first argument.
  - Hence the facts the package names (`facts`: `FnFacts` at the package's `callOrder`), and
    **`Consistent`** for every H (`consistent`, the term of the package's `consistent_of`).
  - **The value `b` at (b, a) and at (b, b), in form (a)** (`choose_ba`, `choose_bb`): entailed by
    `Pre H`, the text's function sentences as written (axioms 96, 97, 98 and the sort predicates'
    equations), Γ's rule items (the text has no rule) and the families Γ defines by predicates.
    `Pre H` has a model with the step's closure (`pre_model`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.NonExecOwiseTie

open KCore ML Faithful KoreAML

/-! ## Patterns equal up to the names of their element variables -/

/-- Two element variables correspond under the binders `env` (innermost first): bound by the same
binder pair, or both free and equal. -/
def varRelB : List (EVar × EVar) → EVar → EVar → Bool
  | [], x, y => decide (x = y)
  | (a, b) :: env, x, y => if x = a then decide (y = b) else if y = b then false else varRelB env x y

/-- **Two patterns equal up to a renaming of their element variables** (`env`: corresponding
variables, innermost binder first; the free variables' pairs last). -/
def alphaB {𝕊 : Type} [DecidableEq 𝕊] : List (EVar × EVar) → Pattern 𝕊 → Pattern 𝕊 → Bool
  | env, .evar x, .evar y => varRelB env x y
  | _, .svar X, .svar Y => decide (X = Y)
  | _, .bottom, .bottom => true
  | _, .symbol s, .symbol t => decide (s = t)
  | env, .application p q, .application p' q' => alphaB env p p' && alphaB env q q'
  | env, .implication p q, .implication p' q' => alphaB env p p' && alphaB env q q'
  | env, .existential x p, .existential y q => alphaB ((x, y) :: env) p q
  | env, .mu X p, .mu Y q => decide (X = Y) && alphaB env p q
  | _, _, _ => false

/-- Two valuations agree under `env`: one value at corresponding element variables, the same set
variables. -/
def AgreeV {M : Type} (env : List (EVar × EVar)) (e e' : Valuation M) : Prop :=
  e.evalSvar = e'.evalSvar ∧ ∀ x y, varRelB env x y = true → e.evalEvar x = e'.evalEvar y

theorem agreeV_cons {M : Type} {env : List (EVar × EVar)} {e e' : Valuation M} (h : AgreeV env e e')
    (x y : EVar) (a : M) :
    AgreeV ((x, y) :: env) ⟨Function.update e.evalEvar x a, e.evalSvar⟩ ⟨Function.update e'.evalEvar y a, e'.evalSvar⟩ := by
  refine ⟨h.1, fun x' y' hr => ?_⟩
  simp only [varRelB] at hr
  split at hr
  · rename_i hx
    subst hx
    simp only [decide_eq_true_eq] at hr
    subst hr
    simp [Function.update]
  · rename_i hx
    split at hr
    · cases hr
    · rename_i hy
      simp only [Function.update, hx, hy, dite_false]
      exact h.2 x' y' hr

/-- A valuation that agrees with `e'` under `env`, `env`'s first variables read through `e'`'s
values at their partners. -/
def pullV {M : Type} : List (EVar × EVar) → Valuation M → Valuation M
  | [], e' => e'
  | (a, b) :: env, e' => ⟨Function.update (pullV env e').evalEvar a (e'.evalEvar b), e'.evalSvar⟩

theorem pullV_svar {M : Type} : ∀ (env : List (EVar × EVar)) (e' : Valuation M), (pullV env e').evalSvar = e'.evalSvar
  | [], _ => rfl
  | (_, _) :: _, _ => rfl

theorem agree_pullV {M : Type} : ∀ (env : List (EVar × EVar)) (e' : Valuation M), AgreeV env (pullV env e') e'
  | [], e' => ⟨rfl, fun x y h => by simp only [varRelB, decide_eq_true_eq] at h; subst h; rfl⟩
  | (a, b) :: env, e' => by
    refine ⟨rfl, fun x y hr => ?_⟩
    simp only [varRelB] at hr
    split at hr
    · rename_i hx
      subst hx
      simp only [decide_eq_true_eq] at hr
      subst hr
      simp [pullV, Function.update]
    · rename_i hx
      split at hr
      · cases hr
      · simp only [pullV, Function.update, hx, dite_false]
        exact (agree_pullV env e').2 x y hr

/-- **Patterns equal up to a renaming of element variables have one interpretation**, at valuations
that agree under the renaming. -/
theorem interpret_of_alphaB {𝕊 : Type} [DecidableEq 𝕊] {M : Type} (I : Interpretation 𝕊 M) :
    ∀ (φ ψ : Pattern 𝕊) (env : List (EVar × EVar)) (e e' : Valuation M), alphaB env φ ψ = true →
      AgreeV env e e' → ∀ m, φ.interpret I e m ↔ ψ.interpret I e' m
  | .evar x, .evar y, env, e, e', h, ha, m => by
    simp only [alphaB] at h
    simp only [Pattern.interpret]
    rw [ha.2 x y h]
  | .svar X, .svar Y, env, e, e', h, ha, m => by
    simp only [alphaB, decide_eq_true_eq] at h
    subst h
    simp only [Pattern.interpret]
    rw [ha.1]
  | .bottom, .bottom, _, _, _, _, _, _ => Iff.rfl
  | .symbol s, .symbol t, _, _, _, h, _, _ => by
    simp only [alphaB, decide_eq_true_eq] at h
    subst h; exact Iff.rfl
  | .application p q, .application p' q', env, e, e', h, ha, m => by
    simp only [alphaB, Bool.and_eq_true] at h
    simp only [Pattern.interpret]
    constructor
    · rintro ⟨a, b, h1, h2, h3⟩
      exact ⟨a, b, (interpret_of_alphaB I p p' env e e' h.1 ha a).mp h1,
        (interpret_of_alphaB I q q' env e e' h.2 ha b).mp h2, h3⟩
    · rintro ⟨a, b, h1, h2, h3⟩
      exact ⟨a, b, (interpret_of_alphaB I p p' env e e' h.1 ha a).mpr h1,
        (interpret_of_alphaB I q q' env e e' h.2 ha b).mpr h2, h3⟩
  | .implication p q, .implication p' q', env, e, e', h, ha, m => by
    simp only [alphaB, Bool.and_eq_true] at h
    simp only [Pattern.interpret]
    rw [interpret_of_alphaB I p p' env e e' h.1 ha m, interpret_of_alphaB I q q' env e e' h.2 ha m]
  | .existential x p, .existential y q, env, e, e', h, ha, m => by
    simp only [alphaB] at h
    simp only [Pattern.interpret]
    constructor
    · rintro ⟨a, h1⟩
      exact ⟨a, (interpret_of_alphaB I p q _ _ _ h (agreeV_cons ha x y a) m).mp h1⟩
    · rintro ⟨a, h1⟩
      exact ⟨a, (interpret_of_alphaB I p q _ _ _ h (agreeV_cons ha x y a) m).mpr h1⟩
  | .mu X p, .mu Y q, env, e, e', h, ha, m => by
    simp only [alphaB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [Pattern.interpret]
    have hag : ∀ B : Set M, AgreeV env ⟨e.evalEvar, Function.update e.evalSvar X B⟩
        ⟨e'.evalEvar, Function.update e'.evalSvar X B⟩ := fun B => ⟨by simp only; rw [ha.1], ha.2⟩
    constructor
    · intro h1 B hB
      exact h1 B fun m' hm' => hB m' ((interpret_of_alphaB I p q env _ _ h (hag B) m').mp hm')
    · intro h1 B hB
      exact h1 B fun m' hm' => hB m' ((interpret_of_alphaB I p q env _ _ h (hag B) m').mpr hm')
  | .evar _, .svar _, _, _, _, h, _, _ | .evar _, .bottom, _, _, _, h, _, _ | .evar _, .symbol _, _, _, _, h, _, _
  | .evar _, .application _ _, _, _, _, h, _, _ | .evar _, .implication _ _, _, _, _, h, _, _
  | .evar _, .existential _ _, _, _, _, h, _, _ | .evar _, .mu _ _, _, _, _, h, _, _
  | .svar _, .evar _, _, _, _, h, _, _ | .svar _, .bottom, _, _, _, h, _, _ | .svar _, .symbol _, _, _, _, h, _, _
  | .svar _, .application _ _, _, _, _, h, _, _ | .svar _, .implication _ _, _, _, _, h, _, _
  | .svar _, .existential _ _, _, _, _, h, _, _ | .svar _, .mu _ _, _, _, _, h, _, _
  | .bottom, .evar _, _, _, _, h, _, _ | .bottom, .svar _, _, _, _, h, _, _ | .bottom, .symbol _, _, _, _, h, _, _
  | .bottom, .application _ _, _, _, _, h, _, _ | .bottom, .implication _ _, _, _, _, h, _, _
  | .bottom, .existential _ _, _, _, _, h, _, _ | .bottom, .mu _ _, _, _, _, h, _, _
  | .symbol _, .evar _, _, _, _, h, _, _ | .symbol _, .svar _, _, _, _, h, _, _ | .symbol _, .bottom, _, _, _, h, _, _
  | .symbol _, .application _ _, _, _, _, h, _, _ | .symbol _, .implication _ _, _, _, _, h, _, _
  | .symbol _, .existential _ _, _, _, _, h, _, _ | .symbol _, .mu _ _, _, _, _, h, _, _
  | .application _ _, .evar _, _, _, _, h, _, _ | .application _ _, .svar _, _, _, _, h, _, _
  | .application _ _, .bottom, _, _, _, h, _, _ | .application _ _, .symbol _, _, _, _, h, _, _
  | .application _ _, .implication _ _, _, _, _, h, _, _ | .application _ _, .existential _ _, _, _, _, h, _, _
  | .application _ _, .mu _ _, _, _, _, h, _, _
  | .implication _ _, .evar _, _, _, _, h, _, _ | .implication _ _, .svar _, _, _, _, h, _, _
  | .implication _ _, .bottom, _, _, _, h, _, _ | .implication _ _, .symbol _, _, _, _, h, _, _
  | .implication _ _, .application _ _, _, _, _, h, _, _ | .implication _ _, .existential _ _, _, _, _, h, _, _
  | .implication _ _, .mu _ _, _, _, _, h, _, _
  | .existential _ _, .evar _, _, _, _, h, _, _ | .existential _ _, .svar _, _, _, _, h, _, _
  | .existential _ _, .bottom, _, _, _, h, _, _ | .existential _ _, .symbol _, _, _, _, h, _, _
  | .existential _ _, .application _ _, _, _, _, h, _, _ | .existential _ _, .implication _ _, _, _, _, h, _, _
  | .existential _ _, .mu _ _, _, _, _, h, _, _
  | .mu _ _, .evar _, _, _, _, h, _, _ | .mu _ _, .svar _, _, _, _, h, _, _ | .mu _ _, .bottom, _, _, _, h, _, _
  | .mu _ _, .symbol _, _, _, _, h, _, _ | .mu _ _, .application _ _, _, _, _, h, _, _
  | .mu _ _, .implication _ _, _, _, _, h, _, _ | .mu _ _, .existential _ _, _, _, _, h, _, _ => by
    simp [alphaB] at h

/-- **Patterns equal up to a renaming of their element variables hold in the same
interpretations**: `env` pairs the free variables (any list does: the valuation of the first pattern
is read off the second's, `pullV`) and, below binders, the bound ones. -/
theorem satisfies_of_alphaB {𝕊 : Type} [DecidableEq 𝕊] {M : Type} {I : Interpretation 𝕊 M} {φ ψ : Pattern 𝕊}
    {env : List (EVar × EVar)} (h : alphaB env φ ψ = true) (hφ : I ⊧ᴵ φ) : I ⊧ᴵ ψ :=
  fun e' m => (interpret_of_alphaB I φ ψ env (pullV env e') e' h (agree_pullV env e') m).mp (hφ _ m)

/-- The free element variables of a pattern, in order of occurrence (`bound`: the binders passed). -/
def freeEV {𝕊 : Type} : List EVar → Pattern 𝕊 → List EVar
  | bound, .evar x => if x ∈ bound then [] else [x]
  | _, .svar _ => []
  | _, .bottom => []
  | _, .symbol _ => []
  | bound, .application p q => freeEV bound p ++ freeEV bound q
  | bound, .implication p q => freeEV bound p ++ freeEV bound q
  | bound, .existential x p => freeEV (x :: bound) p
  | bound, .mu _ p => freeEV bound p

/-- The pairing of two patterns' free element variables in order of first occurrence. -/
def freeMap {𝕊 : Type} (φ ψ : Pattern 𝕊) : List (EVar × EVar) :=
  (freeEV [] φ).eraseDups.zip (freeEV [] ψ).eraseDups

/-! ## Shared -/

/-- The items `its` are the translations (by `tr`) of the sentences `ads`, one for one, up to a
renaming of element variables (`freeMap` pairs the free ones), both ways. -/
def alignB (tr : AxiomDecl → Item) (its : List Item) (ads : List AxiomDecl) : Bool :=
  its.length == ads.length &&
    (its.zip ads).all fun p => alphaB (freeMap p.1.pat (tr p.2).pat) p.1.pat (tr p.2).pat &&
      alphaB (freeMap (tr p.2).pat p.1.pat) (tr p.2).pat p.1.pat

theorem align_pair {tr : AxiomDecl → Item} {its : List Item} {ads : List AxiomDecl} (h : alignB tr its ads = true)
    (i : Nat) (hi : i < its.length) (hj : i < ads.length) :
    alphaB (freeMap its[i].pat (tr ads[i]).pat) its[i].pat (tr ads[i]).pat = true ∧
      alphaB (freeMap (tr ads[i]).pat its[i].pat) (tr ads[i]).pat its[i].pat = true := by
  simp only [alignB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  have hm : (its[i], ads[i]) ∈ its.zip ads :=
    List.mem_iff_getElem.mpr ⟨i, by rw [List.length_zip]; exact Nat.lt_min.mpr ⟨hi, hj⟩, by simp⟩
  simpa using h.2 _ hm

/-- Each sentence's translation is entailed by its item. -/
theorem align_text {tr : AxiomDecl → Item} {its : List Item} {ads : List AxiomDecl} (h : alignB tr its ads = true)
    {ad : AxiomDecl} (had : ad ∈ ads) : ∃ it ∈ its, ∃ env, alphaB env it.pat (tr ad).pat = true := by
  have hl : its.length = ads.length := by simp only [alignB, Bool.and_eq_true, beq_iff_eq] at h; exact h.1
  obtain ⟨i, hj, rfl⟩ := List.getElem_of_mem had
  exact ⟨its[i]'(hl ▸ hj), List.getElem_mem _, _, (align_pair h i (hl ▸ hj) hj).1⟩

/-- Each item is entailed by its sentence's translation. -/
theorem align_item {tr : AxiomDecl → Item} {its : List Item} {ads : List AxiomDecl} (h : alignB tr its ads = true)
    {it : Item} (hit : it ∈ its) : ∃ ad ∈ ads, ∃ env, alphaB env (tr ad).pat it.pat = true := by
  have hl : its.length = ads.length := by simp only [alignB, Bool.and_eq_true, beq_iff_eq] at h; exact h.1
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hit
  exact ⟨ads[i]'(hl ▸ hi), List.getElem_mem _, _, (align_pair h i hi (hl ▸ hi)).2⟩

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c
kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c

theorem mem_Γ_fns {c : Semantics} {φ : P} (h : ΓFns c φ) : Γ c φ := Or.inl (Or.inl (Or.inr h))

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

/-- **A defined result is a theorem of Γ**, for a semantics with `HypSoundCore`: where `f` has the
value `v` at `vs`, `Γ` entails `f(vs) = v` (`eval_den4`). -/
theorem eval_some_sound_core (c : Semantics) (h : HypSoundCore c)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) {f : Sym} {fn : Fn} {vs : List GroundTerm}
    {v : GroundTerm} (hE : Eval c f vs (some v)) (hfn : c.lookupFn f = some fn) (hvs : c.sortsOf vs = some fn.args) :
    Γ c ⊧ (KoreAML.den (symApp c f (GroundTerm.koreList c vs)) ≡ den c v) := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  intro M _ I hI e m
  have hex : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ExclEmpty c I fn cl := fun fn hfn cl hcl => by
    obtain ⟨hp', hb', -⟩ := clause_ctx hok hbc hfn hcl
    exact fun hws _ hkeys hXkeys hRkey _ hX _ hR hσR hfail m =>
      exclusion_emptyC hI hph hcs hcso hg hsc.trans hnn.1 (clause_preTop hok hfn hcl) hp' hb' (collPats_of_sorted hph' hp') hws hkeys hXkeys
        hRkey hX hR hσR hfail m
  rw [KoreAML.interp_equal (defOK hI)]
  intro a
  rw [eval_den4 hI hnn hsc hok hbc hph (fun fn hfn cl hcl _ => hex fn hfn cl hcl) hE hfn hvs e a]
  rfl

/-- **Two values of one sort that a function has at one argument list in a model of Γ are one
value**: Γ entails `f(vs) = v` and `f(vs) = w`, so `v` and `w` denote one element, and distinct
values are distinct elements. -/
theorem same_value_of_model (c : Semantics) (h : HypSoundCore c) {M : Type} [Inhabited M]
    {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) {X : P} {v w : GroundTerm} {s : Srt}
    (hv : c.sortOf v = some s) (hw : c.sortOf w = some s)
    (h1 : Γ c ⊧ (X ≡ den c v)) (h2 : Γ c ⊧ (X ≡ den c w)) : v = w := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have e : Valuation M := ⟨fun _ => default, fun _ _ => False⟩
  have k1 := h1 hI e default
  have k2 := h2 hI e default
  rw [KoreAML.interp_equal (defOK hI)] at k1 k2
  have hvv : (den c v).interpret I e (elemOf c I v) := ((elemOf_spec hI hv e).1 _).mpr rfl
  have hX : X.interpret I e (elemOf c I v) := (k1 _).mpr hvv
  have hwv : (den c w).interpret I e (elemOf c I v) := (k2 _).mp hX
  have he : elemOf c I v = elemOf c I w := ((elemOf_spec hI hw e).1 _).mp hwv
  exact values_apart hI hg hsc.trans (apartSort_of_sorted hg hv) hv hw he

/-- The pattern of a constructor without arguments denotes that constructor only. -/
theorem patVal_ctor0 {c : Semantics} {σ : Subst} {f : Sym} {v : GroundTerm} (hf : c.isCtor f = true)
    (hk : patternHooks.contains f = false) (h : PatVal c σ (.app f []) v) : v = .ctor f [] := by
  cases h with
  | ctor _ hs => cases hs; rfl
  | hook hp _ _ => rw [hk] at hp; cases hp
  | coll hc _ _ _ => rw [hf] at hc; cases hc
  | ovl hc _ _ _ => rw [hf] at hc; cases hc

/-- A clause without a `requires` and without a `pre` whose patterns match does not fail. -/
theorem not_fails_noReq {c : Semantics} {vs : List GroundTerm} {cl : Clause} {σ : Subst} (hq : cl.req = none)
    (hpre : cl.pre = .top)
    (hw : c.WellSortedAt cl.vars cl.leftVars σ) (hp : PatVals c σ cl.pats vs) (hf : Fails c vs cl) : False := by
  cases hf with
  | intro h =>
    cases h σ hw hp with
    | intro ht _ _ => rw [hq] at ht; cases ht
    | pre h => rw [hpre] at h; exact absurd (Holds.top_eq h) (by simp)

theorem ws1 {c : Semantics} {s : Srt} {v : GroundTerm} (hv : c.sortOf v = some s) : c.WellSorted [s] [(0, v)] :=
  fun i s' h => by
    cases i with
    | zero => cases h; exact ⟨v, rfl, hv⟩
    | succ i => simp at h

theorem ws2 {c : Semantics} {s : Srt} {v w : GroundTerm} (hv : c.sortOf v = some s) (hw : c.sortOf w = some s) :
    c.WellSorted [s, s] [(0, v), (1, w)] := fun i s' h => by
  match i, h with
  | 0, h => cases h; exact ⟨v, rfl, hv⟩
  | 1, h => cases h; exact ⟨w, rfl, hw⟩

/-- The cut: what Γ entails, a theory entailing each premise of Γ entails. -/
theorem cutΓ {G T : Premises KoreAML.Sym} {ψ : P} (h : ∀ φ, G φ → T ⊧ φ) (hψ : G ⊧ ψ) : T ⊧ ψ :=
  fun hT => hψ fun φ hφ => h φ hφ hT

/-! ## NX: e5-owise-nonexec -/

namespace NX

kore_term kore from "f2-examples/owisenx.kompile.kore"
definition_of defn from "f2-examples/owisenx.kompile.kore"
user_axioms U from "f2-examples/owisenx.kompile.kore" module "E5-OWISE-NONEXEC"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

def choose : Sym := 387
def a : Sym := 385
def b : Sym := 386
def foo : Srt := 32
def va : GroundTerm := .ctor a []
def vb : GroundTerm := .ctor b []

theorem names : c.symName choose = "Lblchoose" ∧ c.symName a = "Lbla" ∧ c.symName b = "Lblb" ∧
    c.sortName foo = "Foo" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)
noncomputable abbrev clA : Clause := fn.clauses[0]'(by decide +kernel)
noncomputable abbrev clB : Clause := fn.clauses[1]'(by decide +kernel)
noncomputable abbrev clO : Clause := fn.clauses[2]'(by decide +kernel)

theorem fn_label : fn.label = choose := by decide +kernel
theorem fn_args : fn.args = [foo, foo] := by decide +kernel
theorem fn_clauses : fn.clauses = [clA, clB, clO] := rfl
theorem hfnH (H : HookParams) : (cH H).lookupFn choose = some fn := by
  rw [Semantics.lookupFn_withHooks]; rfl
theorem fn_memH (H : HookParams) : fn ∈ (cH H).fns := by
  show fn ∈ c.fns
  exact List.getElem_mem _

/-- **The account**: `wf` and `coreOK` hold. -/
theorem wf_defn : wf defn = true := by decide_cheap
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- **The one named fact is the agreement of `choose`** (the package's `agree_named`), under every H. -/
theorem agree_named : c.agreeObligationsI = [choose] := by decide +kernel
theorem agree_namedH (H : HookParams) : (cH H).agreeObligationsI = [choose] :=
  (Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named

/-- The `non-executable` equation is read as an `aside` clause; the others are not. -/
theorem aside_b : clB.aside = true ∧ clA.aside = false ∧ clO.aside = false := by decide +kernel

theorem pA : clA.prio = 50 := rfl
theorem pB : clB.prio = 50 := rfl
theorem pO : clO.prio = 200 := rfl
theorem vA : clA.vars = [foo] := rfl
theorem ptA : clA.pats = [.app a [], .var 0] := rfl
theorem qA : clA.req = none := rfl
theorem rA : clA.rhs = .var 0 := rfl
theorem eA : clA.ens = none := rfl
theorem vB : clB.vars = [foo] := rfl
theorem ptB : clB.pats = [.app b [], .var 0] := rfl
theorem qB : clB.req = none := rfl
theorem rB : clB.rhs = .var 0 := rfl
theorem eB : clB.ens = none := rfl
theorem vO : clO.vars = [foo, foo] := rfl
theorem ptO : clO.pats = [.var 0, .var 1] := rfl
theorem qO : clO.req = none := rfl
theorem rO : clO.rhs = .var 0 := rfl
theorem eO : clO.ens = none := rfl
theorem preA : clA.pre = .top := rfl
theorem preB : clB.pre = .top := rfl
theorem preO : clO.pre = .top := rfl

/-- The `[owise]` clause's smaller clauses are the first alone, as axiom 96 writes. -/
theorem lower_owise : Faithful.lowerClauses fn clO = [clA] := rfl

/-! ### Γ's items for `choose` are the text's sentences -/

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's equations, in `fnItems`'s order: `choose`'s (axioms 97, 98, 96: the
clauses A, B and the `[owise]` O), then the sort predicates' (`isX`'s plain equation, then its
`[owise]` one). -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax97, U.ax98, U.ax96, U.ax117, U.ax125, U.ax124, U.ax123, U.ax122, U.ax129, U.ax128, U.ax131,
   U.ax130, U.ax127, U.ax126, U.ax104, U.ax103, U.ax116, U.ax115, U.ax112, U.ax111, U.ax114, U.ax113,
   U.ax119, U.ax118, U.ax121, U.ax120, U.ax108, U.ax107, U.ax110, U.ax109, U.ax106, U.ax105]

/-- **The items of the clauses A and B are the translations of axioms 97 and 98**, pattern for
pattern: the `non-executable` equation is in Γ as written. -/
theorem choose_AB : ((fnItems c).take 2).map (·.pat) = [U.ax97, U.ax98].map (trS · |>.pat) := by
  rw [fnItems_eq]; decide +kernel

/-- **Each of Γ's equations is the translation of its text sentence up to a renaming of element
variables, free and bound** (both ways; a kernel decision). The `[owise]` item is not literally
axiom 96's translation (`owise_not_literal`); its exclusion is the one disjunct the text writes, the
clause A's pattern. -/
theorem fn_align : alignB trS (fnItems c) fnText = true := by
  rw [fnItems_eq]; decide +kernel

theorem owise_not_literal : ((fnItems c).map (·.pat))[2]? ≠ some (trS U.ax96).pat := by
  rw [fnItems_eq]; decide +kernel

/-- Each sentence of `fnText` holds in every model of Γ, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, _, hα⟩ := align_text fn_align had
  exact satisfies_of_alphaB hα (hI _ (mem_Γ_fns (Or.inl ⟨it, by rw [fnItems_withHooks]; exact hit, rfl⟩)))

/-! ### `Eval` at (b, a): two results, for every H -/

theorem isCtor_a (H : HookParams) : (cH H).isCtor a = true := (by decide +kernel : c.isCtor a = true)
theorem isCtor_b (H : HookParams) : (cH H).isCtor b = true := (by decide +kernel : c.isCtor b = true)
theorem sort_a (H : HookParams) : (cH H).sortOf va = some foo := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem sort_b (H : HookParams) : (cH H).sortOf vb = some foo := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem sorts_ba (H : HookParams) : (cH H).sortsOf [vb, va] = some fn.args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel
theorem hook_a : patternHooks.contains a = false := by decide
theorem hook_b : patternHooks.contains b = false := by decide

/-- The first clause fails at `(b, w)`: its pattern `a` does not denote `b`. -/
theorem clA_fails_b (H : HookParams) (w : GroundTerm) : Fails (cH H) [vb, w] clA := .intro fun σ _ hp => by
  rw [ptA] at hp
  cases hp with
  | cons h _ => exact absurd (patVal_ctor0 (isCtor_a H) hook_a h) (by simp [vb, a, b])

theorem lowerB (H : HookParams) : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < clB.prio → Fails (cH H) [vb, va] cl' :=
  fun cl' h ha hlt => by
    rw [fn_clauses] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · rw [pA, pB] at hlt; exact absurd hlt (by decide)
    · rw [aside_b.1] at ha; cases ha
    · rw [pO, pB] at hlt; exact absurd hlt (by decide)

theorem lowerO (H : HookParams) (w : GroundTerm) :
    ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < clO.prio → Fails (cH H) [vb, w] cl' :=
  fun cl' h ha hlt => by
    rw [fn_clauses] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact clA_fails_b H w
    · rw [aside_b.1] at ha; cases ha
    · exact absurd hlt (Nat.lt_irrefl _)

theorem appliesB (H : HookParams) : clB.AppliesAt (cH H) [(0, va)] [vb, va] :=
  ⟨by rw [vB]; exact (ws1 (sort_a H)).at _,
   by rw [ptB]; exact .cons (.ctor (isCtor_b H) .nil) (.cons (.var rfl) .nil),
   (fun t ht => by rw [qB] at ht; cases ht), Clause.holds_preTop preB _⟩

theorem appliesO (H : HookParams) : clO.AppliesAt (cH H) [(0, vb), (1, va)] [vb, va] :=
  ⟨by rw [vO]; exact (ws2 (sort_b H) (sort_a H)).at _,
   by rw [ptO]; exact .cons (.var rfl) (.cons (.var rfl) .nil),
   (fun t ht => by rw [qO] at ht; cases ht), Clause.holds_preTop preO _⟩

/-- At (b, a): `a`, by the `aside` clause (no clause of a smaller priority is not `aside`). -/
theorem eval_ba_a (H : HookParams) : Eval (cH H) choose [vb, va] (some va) :=
  .clause (cl := clB) (σ := [(0, va)]) (hfnH H) (by rw [fn_clauses]; simp)
    ((wellSortedAt_univ rfl).mp (appliesB H).1) (appliesB H).2.1 (appliesB H).2.2.1 (appliesB H).2.2.2 (lowerB H)
    rfl (by rw [rB]; exact .var) (fun t ht => by rw [eB] at ht; cases ht) (Clause.holds_postTop rfl _)

/-- At (b, a): `b`, by the `[owise]` clause (its one smaller clause that is not `aside`, the first,
fails). -/
theorem eval_ba_b (H : HookParams) : Eval (cH H) choose [vb, va] (some vb) :=
  .clause (cl := clO) (σ := [(0, vb), (1, va)]) (hfnH H) (by rw [fn_clauses]; simp)
    ((wellSortedAt_univ rfl).mp (appliesO H).1) (appliesO H).2.1 (appliesO H).2.2.1 (appliesO H).2.2.2 (lowerO H va)
    rfl (by rw [rO]; exact .var) (fun t ht => by rw [eO] at ht; cases ht) (Clause.holds_postTop rfl _)

theorem va_ne_vb : va ≠ vb := by simp [va, vb, a, b]

/-- **Not `FnDet`**, for every H: two results at (b, a). -/
theorem not_fnDet (H : HookParams) : ¬ FnDet (cH H) :=
  fun h => va_ne_vb (Option.some.inj (h _ _ _ _ (eval_ba_a H) (eval_ba_b H)))

/-- **Not `ClausesAgree` of `choose`**, for every H: the `aside` clause and the `[owise]` clause
compete (the `aside` one has the smaller priority) and both decide at (b, a), with the results `a`
and `b`. -/
theorem not_agree (H : HookParams) : ¬ ClausesAgree (cH H) fn := fun h => by
  have hp : (clB, clO) ∈ pairs fn.clauses := by rw [fn_clauses]; simp [pairs]
  have hcomp : clB.prio = clO.prio ∨ (clB.aside = true ∧ clB.prio < clO.prio) ∨
      (clO.aside = true ∧ clO.prio < clB.prio) :=
    .inr (.inl ⟨aside_b.1, by rw [pB, pO]; decide⟩)
  have hco := (h clB clO hp hcomp).1
  have hdet : HDet (cH H) [(0, va)] clB.rhs := by
    rw [rB]
    intro u hu r r' h1 h2
    simp only [subterms, List.mem_singleton] at hu
    subst hu
    cases h1; cases h2; rfl
  rcases hco [vb, va] [(0, va)] [(0, vb), (1, va)] (appliesB H) (appliesO H)
      (fun t ht => by rw [qB] at ht; cases ht) (fun _ _ => hdet)
      (fun _ t ht => by rw [eB] at ht; cases ht) (fun hne => absurd rfl hne)
      ⟨choose, fn, hfnH H, by rw [fn_clauses]; simp, by rw [fn_clauses]; simp, ⟨appliesB H, lowerB H⟩,
        ⟨appliesO H, lowerO H va⟩⟩ with
    ⟨-, -, -, -, hv, -⟩ | hr
  · have := hv 0 (by rw [rB]; simp [varOccs])
    exact va_ne_vb (by simpa using this)
  · have := hr (some va) (some vb)
      ((Clause.res_noExs rfl).mpr (.inl ⟨(fun t ht => by rw [eB] at ht; cases ht),
        Clause.holds_postTop rfl _, (by rw [rB]; exact .var)⟩))
      ((Clause.res_noExs rfl).mpr (.inl ⟨(fun t ht => by rw [eO] at ht; cases ht),
        Clause.holds_postTop rfl _, (by rw [rO]; exact .var)⟩))
    exact va_ne_vb (Option.some.inj this)

/-- **Not `FnSolves`**, for every H: the `aside` clause decides at (b, a) under Y := a (no clause of
a smaller priority), and `b` is a result there (`eval_ba_b`) that is not the value of its right side
`Y`. -/
theorem not_fnSolves (H : HookParams) : ¬ FnSolves (cH H) := fun h => by
  have hdec : clB.DecidesAt (cH H) fn [(0, va)] [vb, va] := ⟨appliesB H, fun cl' h' ha hlt => by
    rw [fn_clauses] at h'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
    rcases h' with rfl | rfl | rfl
    · rw [pA, pB] at hlt; exact absurd hlt (by decide)
    · rw [aside_b.1] at ha; cases ha
    · rw [pO, pB] at hlt; exact absurd hlt (by decide)⟩
  have hiff := h fn (fn_memH H) [vb, va] (sorts_ba H) clB (by rw [fn_clauses]; simp) [(0, va)] hdec vb
  rw [fn_label] at hiff
  obtain ⟨hr, -⟩ := (Clause.gives_iff_noExs (cl := clB) rfl rfl ((wellSortedAt_univ rfl).mp hdec.1.1) vb).mp (hiff.mp (eval_ba_b H))
  rw [rB] at hr
  cases hr

/-! ### Γ has no model, for every H -/

theorem okH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans (by decide +kernel)

/-- `Γ` entails `choose(b, a) = a` and `choose(b, a) = b`, for every H. -/
theorem entails_ba (H : HookParams) (v : GroundTerm) (hE : Eval (cH H) choose [vb, va] (some v)) :
    Γ (cH H) ⊧ (KoreAML.den (symApp (cH H) choose (GroundTerm.koreList (cH H) [vb, va])) ≡ den (cH H) v) :=
  eval_some_sound_core _ (hypSound_of_core (coreOKH H)) (Semantics.ok_clauseBinds (okH H)) hE (hfnH H) (sorts_ba H)

/-- **Γ has no model**, for every H: in a model, `choose(b, a)` denotes `a` and `b` (the two `Eval`
results), so the two values are one; they are distinct. -/
theorem no_model (H : HookParams) {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M) :
    ¬ (I ⊧ᴵP Γ (cH H)) := fun hI =>
  va_ne_vb (same_value_of_model _ (hypSound_of_core (coreOKH H)) hI (sort_a H) (sort_b H)
    (entails_ba H va (eval_ba_a H)) (entails_ba H vb (eval_ba_b H)))

/-- **Not `Consistent`**, for every H: `Γc` holds Γ. -/
theorem not_consistent (H : HookParams) : ¬ Consistent (cH H) := fun ⟨_, _, I, hI⟩ =>
  no_model H I fun φ hφ => hI φ (Or.inl (Or.inl hφ))

/-! ### Facts about `Eval`, not values of the text -/

/-- **`Eval` at (b, b) gives `b` only**, for every H (a fact about `Eval`; the text has no model). -/
theorem eval_bb (H : HookParams) (r : Option GroundTerm) (h : Eval (cH H) choose [vb, vb] r) : r = some vb := by
  cases h with
  | clause hfn' hmem _ hmatch _ _ _ _ hrhs _ _ =>
    rw [hfnH H] at hfn'; cases hfn'
    rw [fn_clauses] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · rw [ptA] at hmatch
      cases hmatch with
      | cons h1 _ => exact absurd (patVal_ctor0 (isCtor_a H) hook_a h1) (by simp [vb, a, b])
    · rw [ptB] at hmatch; rw [rB] at hrhs
      cases hmatch with
      | cons _ h2 => cases h2 with
        | cons h2 _ => cases h2 with
          | var hl => cases hrhs; exact hl
    · rw [ptO] at hmatch; rw [rO] at hrhs
      cases hmatch with
      | cons h1 _ => cases h1 with
        | var hl => cases hrhs; exact hl
  | rest hfn' hnone =>
    rw [hfnH H] at hfn'; cases hfn'
    exact (not_fails_noReq qB preB (by rw [vB]; exact (ws1 (sort_b H)).at _)
      (by rw [ptB]; exact .cons (.ctor (isCtor_b H) .nil) (.cons (.var rfl) .nil))
      (hnone clB (by rw [fn_clauses]; simp))).elim
  | clauseEx hfn' hmem _ _ _ _ _ hne =>
    rw [hfnH H] at hfn'; cases hfn'
    rw [fn_clauses] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;> exact absurd rfl hne
  | exNone hfn' hmem hne =>
    rw [hfnH H] at hfn'; cases hfn'
    rw [fn_clauses] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;> exact absurd rfl hne
  | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ =>
    rw [hfnH H] at hfn'; cases hfn'
    rw [fn_clauses] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · rw [eA] at ht; cases ht
    · rw [eB] at ht; cases ht
    · rw [eO] at ht; cases ht

/-- **`Eval` at (a, y) gives `y` only**, for every value y of Foo and every H (a fact about `Eval`;
the text has no model). -/
theorem eval_ay (H : HookParams) {y : GroundTerm} (hy : (cH H).sortOf y = some foo) (r : Option GroundTerm)
    (h : Eval (cH H) choose [va, y] r) : r = some y := by
  have hAap : (cH H).WellSortedAt clA.vars clA.leftVars [(0, y)] ∧ PatVals (cH H) [(0, y)] clA.pats [va, y] :=
    ⟨by rw [vA]; exact (ws1 hy).at _, by rw [ptA]; exact .cons (.ctor (isCtor_a H) .nil) (.cons (.var rfl) .nil)⟩
  cases h with
  | clause hfn' hmem _ hmatch _ _ hprio _ hrhs _ _ =>
    rw [hfnH H] at hfn'; cases hfn'
    rw [fn_clauses] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · rw [ptA] at hmatch; rw [rA] at hrhs
      cases hmatch with
      | cons _ h2 => cases h2 with
        | cons h2 _ => cases h2 with
          | var hl => cases hrhs; exact hl
    · rw [ptB] at hmatch
      cases hmatch with
      | cons h1 _ => exact absurd (patVal_ctor0 (isCtor_b H) hook_b h1) (by simp [va, a, b])
    · exact (not_fails_noReq qA preA hAap.1 hAap.2
        (hprio clA (by rw [fn_clauses]; simp) aside_b.2.1 (by rw [pA, pO]; decide))).elim
  | rest hfn' hnone =>
    rw [hfnH H] at hfn'; cases hfn'
    exact (not_fails_noReq qA preA hAap.1 hAap.2 (hnone clA (by rw [fn_clauses]; simp))).elim
  | clauseEx hfn' hmem _ _ _ _ _ hne =>
    rw [hfnH H] at hfn'; cases hfn'
    rw [fn_clauses] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;> exact absurd rfl hne
  | exNone hfn' hmem hne =>
    rw [hfnH H] at hfn'; cases hfn'
    rw [fn_clauses] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;> exact absurd rfl hne
  | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ =>
    rw [hfnH H] at hfn'; cases hfn'
    rw [fn_clauses] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · rw [eA] at ht; cases ht
    · rw [eB] at ht; cases ht
    · rw [eO] at ht; cases ht

end NX

/-! ## AG: e5-owise-nonexec-agree -/

namespace AG

kore_term kore from "f2-examples/owisenxagree.kompile.kore"
definition_of defn from "f2-examples/owisenxagree.kompile.kore"
user_axioms U from "f2-examples/owisenxagree.kompile.kore" module "E5-OWISE-NONEXEC-AGREE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

def choose : Sym := 387
def a : Sym := 385
def b : Sym := 386
def foo : Srt := 32
def va : GroundTerm := .ctor a []
def vb : GroundTerm := .ctor b []

theorem names : c.symName choose = "Lblchoose" ∧ c.symName a = "Lbla" ∧ c.symName b = "Lblb" ∧
    c.sortName foo = "Foo" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)
noncomputable abbrev clB : Clause := fn.clauses[0]'(by decide +kernel)
noncomputable abbrev clA : Clause := fn.clauses[1]'(by decide +kernel)
noncomputable abbrev clO : Clause := fn.clauses[2]'(by decide +kernel)

theorem fn_label : fn.label = choose := by decide +kernel
theorem fn_clauses : fn.clauses = [clB, clA, clO] := rfl
theorem hfnH (H : HookParams) : (cH H).lookupFn choose = some fn := by
  rw [Semantics.lookupFn_withHooks]; rfl

theorem wf_defn : wf defn = true := by decide_cheap
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem okH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans (by decide +kernel)

/-- The agreement of `choose` is the one named fact (the package's `agree_named`), under every H:
no decider confirms it. -/
theorem agree_named : c.agreeObligationsI = [choose] := by decide +kernel
theorem agree_namedH (H : HookParams) : (cH H).agreeObligationsI = [choose] :=
  (Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named

/-- The `non-executable` equation is read as an `aside` clause, `choose((b as V0), V1) = V0`. -/
theorem aside_b : clB.aside = true ∧ clA.aside = false ∧ clO.aside = false := by decide +kernel

theorem pB : clB.prio = 50 := rfl
theorem pA : clA.prio = 50 := rfl
theorem pO : clO.prio = 200 := rfl
theorem vB : clB.vars = [foo, foo] := rfl
theorem ptB : clB.pats = [.as (.app b []) 0, .var 1] := rfl
theorem rB : clB.rhs = .var 0 := rfl
theorem eB : clB.ens = none := rfl
theorem vA : clA.vars = [foo] := rfl
theorem ptA : clA.pats = [.app a [], .var 0] := rfl
theorem qA : clA.req = none := rfl
theorem rA : clA.rhs = .var 0 := rfl
theorem eA : clA.ens = none := rfl
theorem preA : clA.pre = .top := rfl
theorem vO : clO.vars = [foo, foo] := rfl
theorem ptO : clO.pats = [.var 0, .var 1] := rfl
theorem qO : clO.req = none := rfl
theorem rO : clO.rhs = .var 0 := rfl
theorem eO : clO.ens = none := rfl
theorem preO : clO.pre = .top := rfl

/-- The `[owise]` clause's smaller clauses are the clause A alone, as axiom 97 writes. -/
theorem lower_owise : Faithful.lowerClauses fn clO = [clA] := rfl

/-! ### Γ's items are the text's sentences -/

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's equations, in `fnItems`'s order: `choose`'s (axioms 96, 98, 97: the
clauses B, A and the `[owise]` O), then the sort predicates'. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax96, U.ax98, U.ax97, U.ax117, U.ax125, U.ax124, U.ax123, U.ax122, U.ax129, U.ax128, U.ax131,
   U.ax130, U.ax127, U.ax126, U.ax104, U.ax103, U.ax116, U.ax115, U.ax112, U.ax111, U.ax114, U.ax113,
   U.ax119, U.ax118, U.ax121, U.ax120, U.ax108, U.ax107, U.ax110, U.ax109, U.ax106, U.ax105]

/-- **The items of the clauses B and A are the translations of axioms 96 and 98**, pattern for
pattern: the `non-executable` equation is in Γ as written. -/
theorem choose_BA : ((fnItems c).take 2).map (·.pat) = [U.ax96, U.ax98].map (trS · |>.pat) := by
  rw [fnItems_eq]; decide +kernel

/-- **Each of Γ's equations is the translation of its text sentence up to a renaming of element
variables, free and bound**, both ways (a kernel decision). -/
theorem fn_align : alignB trS (fnItems c) fnText = true := by
  rw [fnItems_eq]; decide +kernel

theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, _, hα⟩ := align_text fn_align had
  exact satisfies_of_alphaB hα (hI _ (mem_Γ_fns (Or.inl ⟨it, by rw [fnItems_withHooks]; exact hit, rfl⟩)))

/-! ### `ClausesAgree` of `choose`, for every H -/

theorem isCtor_a (H : HookParams) : (cH H).isCtor a = true := (by decide +kernel : c.isCtor a = true)
theorem isCtor_b (H : HookParams) : (cH H).isCtor b = true := (by decide +kernel : c.isCtor b = true)
theorem hook_a : patternHooks.contains a = false := by decide
theorem hook_b : patternHooks.contains b = false := by decide
theorem sort_a (H : HookParams) : (cH H).sortOf va = some foo := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem sort_b (H : HookParams) : (cH H).sortOf vb = some foo := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel

/-- Where the clause B applies, the first argument is `b`, and V0 is it. -/
theorem pats_B {H : HookParams} {σ : Subst} {vs : List GroundTerm} (h : PatVals (cH H) σ clB.pats vs) :
    ∃ y, vs = [vb, y] ∧ σ.lookup 0 = some vb := by
  rw [ptB] at h
  cases h with
  | cons h1 h2 =>
    cases h2 with
    | cons _ h4 =>
      cases h4
      cases h1 with
      | as hp hi =>
        have := patVal_ctor0 (isCtor_b H) hook_b hp
        subst this
        exact ⟨_, rfl, hi⟩

/-- Where the clause A applies, the first argument is `a`. -/
theorem pats_A {H : HookParams} {σ : Subst} {vs : List GroundTerm} (h : PatVals (cH H) σ clA.pats vs) :
    ∃ y, vs = [va, y] := by
  rw [ptA] at h
  cases h with
  | cons h1 h2 =>
    cases h2 with
    | cons _ h4 =>
      cases h4
      have := patVal_ctor0 (isCtor_a H) hook_a h1
      subst this
      exact ⟨_, rfl⟩

/-- Where the `[owise]` clause applies, X is the first argument. -/
theorem pats_O {H : HookParams} {σ : Subst} {vs : List GroundTerm} (h : PatVals (cH H) σ clO.pats vs) :
    ∃ x y, vs = [x, y] ∧ σ.lookup 0 = some x := by
  rw [ptO] at h
  cases h with
  | cons h1 h2 =>
    cases h2 with
    | cons _ h4 =>
      cases h4
      cases h1 with
      | var hl => exact ⟨_, _, rfl, hl⟩

theorem va_ne_vb : va ≠ vb := by simp [va, vb, a, b]

/-- B and A never both apply. -/
theorem coh_BA (H : HookParams) : Coherent (cH H) clB clA := by
  intro vs σ σ' h1 h2 _ _ _ _
  obtain ⟨y, rfl, -⟩ := pats_B h1.2.1
  obtain ⟨y', h⟩ := pats_A h2.2.1
  exact absurd (List.cons.inj h).1.symm va_ne_vb

theorem coh_AB (H : HookParams) : Coherent (cH H) clA clB := by
  intro vs σ σ' h1 h2 _ _ _ _
  obtain ⟨y, rfl⟩ := pats_A h1.2.1
  obtain ⟨y', h, -⟩ := pats_B h2.2.1
  exact absurd (List.cons.inj h).1 va_ne_vb

/-- Where B and the `[owise]` clause both apply, both right sides are the first argument. -/
theorem coh_BO (H : HookParams) : Coherent (cH H) clB clO := by
  intro vs σ σ' h1 h2 _ _ _ _ _
  obtain ⟨y, rfl, hσ⟩ := pats_B h1.2.1
  obtain ⟨x, y', hv, hσ'⟩ := pats_O h2.2.1
  have hx : x = vb := (List.cons.inj hv).1.symm
  subst hx
  refine .inl ⟨rfl, rfl, by rw [rB, rO], by rw [eB, eO], fun i hi => ?_, fun t ht => by rw [eB] at ht; cases ht⟩
  rw [rB] at hi
  simp only [varOccs, List.mem_singleton] at hi
  subst hi
  rw [hσ, hσ']

theorem coh_OB (H : HookParams) : Coherent (cH H) clO clB := by
  intro vs σ σ' h1 h2 _ _ _ _ _
  obtain ⟨x, y', hv, hσ'⟩ := pats_O h1.2.1
  obtain ⟨y, rfl, hσ⟩ := pats_B h2.2.1
  have hx : x = vb := (List.cons.inj hv).1.symm
  subst hx
  refine .inl ⟨rfl, rfl, by rw [rB, rO], by rw [eB, eO], fun i hi => ?_, fun t ht => by rw [eO] at ht; cases ht⟩
  rw [rO] at hi
  simp only [varOccs, List.mem_singleton] at hi
  subst hi
  rw [hσ, hσ']

theorem pairs_eq : pairs fn.clauses = [(clB, clA), (clB, clO), (clA, clO)] := rfl

/-- **`ClausesAgree` of `choose`, for every H**: the pairs that compete are (B, A), of one priority,
which never both apply, and (B, O), B `aside` of the smaller priority, whose right sides are the first
argument wherever both apply; A and O do not compete. -/
theorem agree (H : HookParams) : ClausesAgree (cH H) fn := by
  intro cl cl' hp hcomp
  rw [pairs_eq] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨coh_BA H, coh_AB H⟩
  · exact ⟨coh_BO H, coh_OB H⟩
  · exact absurd hcomp (not_compete (by decide +kernel))

/-! ### The package's facts and consistency, for every H -/

/-- The package's rank of the functions. -/
def callOrder : List Nat := [387]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

/-- **The facts the package names hold, for every H** (`FnFacts` at the package's `callOrder`: the
agreement of `choose`, nothing else). -/
theorem facts (H : HookParams) : FnFacts (cH H) callOrder [] :=
  ⟨fun f hf => by
    rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks, term_named] at hf
    exact absurd hf List.not_mem_nil,
   fun f hf => by
    rw [Semantics.totalObligationsRP_withHooks _ H _ _, total_named] at hf
    exact absurd hf List.not_mem_nil,
   fun f hf fn' hfn' => by
    rw [agree_namedH, List.mem_singleton] at hf
    subst hf
    rw [hfnH H] at hfn'
    cases hfn'
    exact agree H,
   fun p hp => by
    rw [Det.Semantics.matchObligationsL_withHooks _ H, match_named] at hp
    exact absurd hp List.not_mem_nil,
   openLaws_of_plain fun k hk => by
    simpa using List.all_eq_true.mp (by decide +kernel : c.params.all (fun k => !k.raw) = true) k hk⟩

/-- **`Consistent`, for every H** (the term of the package's `consistent_of`, at `facts`). -/
theorem consistent (H : HookParams) : Consistent (cH H) :=
  consistent_of_fnFacts (coreOKH H) (Semantics.rightHeld_withHooks_of_valued (by decide +kernel) H) (facts H)

/-! ### The value `b` at (b, a) and at (b, b), in form (a) -/

theorem mem_Γ_rules {c : Semantics} {φ : P} (h : ΓRules c φ) : Γ c φ := Or.inl (Or.inr h)

/-- The function sentences as written, with definedness. -/
def TextFns : Premises KoreAML.Sym := fun φ => (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x

/-- The parts of Γ that are no sentence's translation: the families. -/
def Families (H : HookParams) : Premises KoreAML.Sym :=
  ΓSig (cH H) ∪ ΓCons (cH H) ∪ ΓDomains (cH H) ∪ ΓColls (cH H) ∪ ΓFallback (cH H)

/-- The premises of the derivations: the function sentences as written (`choose`'s three, the
`non-executable` one and the `[owise]` one among them), Γ's rule items (the text has no rule), and
the families. -/
def Pre (H : HookParams) : Premises KoreAML.Sym := TextFns ∪ ΓRules (cH H) ∪ Families H

/-- Every premise of Γ is a consequence of `Pre`: a function equation by its sentence
(`fn_align`). -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → Pre H ⊧ φ := by
  intro φ h M _ I hI
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact hI _ (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl h)))))
  · exact hI _ (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact hI _ (Or.inr (Or.inl (Or.inl (Or.inr h))))
  · exact hI _ (Or.inr (Or.inl (Or.inr h)))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [fnItems_withHooks] at hit
      obtain ⟨ad, had, _, hα⟩ := align_item fn_align hit
      exact satisfies_of_alphaB hα (hI _ (Or.inl (Or.inl (Or.inl ⟨ad, had, rfl⟩))))
    · exact hI _ (Or.inl (Or.inl (Or.inr hx)))
  · exact hI _ (Or.inl (Or.inr h))
  · exact hI _ (Or.inr (Or.inr h))

/-- **`Pre` with the step's closure has a model, for every H**: every model of Γ with the step's
closure is one (`consistent`, `fns_entailed`). The derivations below are not vacuous. -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) := by
  obtain ⟨M, hM, I, hI⟩ := consistent H
  have hΓ : I ⊧ᴵP Γ (cH H) := fun φ h => hI φ (Or.inl (Or.inl h))
  refine ⟨M, hM, I, fun φ h => ?_⟩
  rcases h with ((h | h) | h) | h
  · rcases h with ⟨ad, had, rfl⟩ | ⟨x, rfl⟩
    · exact fns_entailed H ad had hΓ
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩))))))))
  · exact hΓ _ (mem_Γ_rules h)
  · rcases h with (((h | h) | h) | h) | h
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inr h))))
    · exact hΓ _ (Or.inr h)
  · exact hI _ (Or.inr h)

/-- The clause A fails at `(b, w)`: its pattern `a` does not denote `b`. -/
theorem clA_fails_b (H : HookParams) (w : GroundTerm) : Fails (cH H) [vb, w] clA := .intro fun σ _ hp => by
  rw [ptA] at hp
  cases hp with
  | cons h _ => exact absurd (patVal_ctor0 (isCtor_a H) hook_a h) (by simp [vb, a, b])

/-- At (b, w): `b`, by the `[owise]` clause (its one smaller clause that is not `aside`, A, fails). -/
theorem eval_bw (H : HookParams) {w : GroundTerm} (hw : (cH H).sortOf w = some foo) :
    Eval (cH H) choose [vb, w] (some vb) :=
  .clause (cl := clO) (σ := [(0, vb), (1, w)]) (hfnH H) (by rw [fn_clauses]; simp)
    (by rw [vO]; exact ws2 (sort_b H) hw)
    (by rw [ptO]; exact .cons (.var rfl) (.cons (.var rfl) .nil))
    (fun t ht => by rw [qO] at ht; cases ht) (Clause.holds_preTop preO _)
    (fun cl' h ha hlt => by
      rw [fn_clauses] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      · rw [aside_b.1] at ha; cases ha
      · exact clA_fails_b H w
      · exact absurd hlt (Nat.lt_irrefl _))
    rfl (by rw [rO]; exact .var) (fun t ht => by rw [eO] at ht; cases ht) (Clause.holds_postTop rfl _)

theorem sorts_bw (H : HookParams) {w : GroundTerm} (hw : (cH H).sortOf w = some foo) :
    (cH H).sortsOf [vb, w] = some fn.args := by
  have hargs : fn.args = [foo, foo] := by decide +kernel
  rw [hargs]
  exact sortsOf_cons.mpr ⟨_, _, sort_b H, sortsOf_cons.mpr ⟨_, _, hw, rfl, rfl⟩, rfl⟩

/-- `⟦choose(vs)⟧`. -/
noncomputable def chooseAt (H : HookParams) (vs : List GroundTerm) : P :=
  KoreAML.den (symApp (cH H) choose (GroundTerm.koreList (cH H) vs))

theorem choose_bw (H : HookParams) {w : GroundTerm} (hw : (cH H).sortOf w = some foo) :
    Pre H ⊧ (chooseAt H [vb, w] ≡ den (cH H) vb) :=
  cutΓ (gamma_from H) (eval_some_sound_core _ (hypSound_of_core (coreOKH H)) (Semantics.ok_clauseBinds (okH H))
    (eval_bw H hw) (hfnH H) (sorts_bw H hw))

/-- **`choose(b, a) = b`, derived from `Pre`** (the text's function sentences as written and the
families), for every H; `Pre` has a model (`pre_model`). -/
theorem choose_ba (H : HookParams) : Pre H ⊧ (chooseAt H [vb, va] ≡ den (cH H) vb) := choose_bw H (sort_a H)

/-- **`choose(b, b) = b`, derived from `Pre`**, for every H. -/
theorem choose_bb (H : HookParams) : Pre H ⊧ (chooseAt H [vb, vb] ≡ den (cH H) vb) := choose_bw H (sort_b H)

end AG

/-- info: 'KCore.NonExecOwiseTie.NX.no_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NX.no_model
/-- info: 'KCore.NonExecOwiseTie.NX.not_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NX.not_consistent
/-- info: 'KCore.NonExecOwiseTie.NX.not_fnSolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NX.not_fnSolves
/-- info: 'KCore.NonExecOwiseTie.NX.not_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NX.not_agree
/-- info: 'KCore.NonExecOwiseTie.NX.not_fnDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NX.not_fnDet
/-- info: 'KCore.NonExecOwiseTie.NX.fns_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NX.fns_entailed
/-- info: 'KCore.NonExecOwiseTie.NX.eval_bb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NX.eval_bb
/-- info: 'KCore.NonExecOwiseTie.NX.eval_ay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NX.eval_ay
/-- info: 'KCore.NonExecOwiseTie.AG.agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AG.agree
/-- info: 'KCore.NonExecOwiseTie.AG.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AG.consistent
/-- info: 'KCore.NonExecOwiseTie.AG.choose_ba' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AG.choose_ba
/-- info: 'KCore.NonExecOwiseTie.AG.choose_bb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AG.choose_bb
/-- info: 'KCore.NonExecOwiseTie.AG.pre_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AG.pre_model

end KCore.NonExecOwiseTie
