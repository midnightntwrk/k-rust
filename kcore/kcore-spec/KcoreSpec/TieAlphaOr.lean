/-
  KCore, outside the cone: two sentences that differ by the order of the operands of their sorted
  disjunctions and by the names of their variables are satisfied by the same interpretations.

  `sOr s φ ψ` (T-or) is, in every model, `(φ ∨ ψ) ∧ ⊤_s` (`orParts_interp`), so a right-nested chain
  of disjunctions at one sort is the union of its operands within `⊤_s` (`orChain_interp`), whatever
  their order. A variable's index is a name: renaming the bound variables of a pattern, and its free
  variables injectively, does not change which interpretations satisfy it.

  - `acEq n env g t`: the patterns agree up to these two freedoms. At a disjunction on both sides
    the operands of the two chains cover one another; elsewhere the patterns have the same shape,
    variables correspond by `env` (the binders around them first, then the free ones), set
    variables are the same. `n` bounds the depth.
  - `acEq_interp`: under valuations that agree along `env`, `g` and `t` have one interpretation.
  - `acEq_sat`: with `env` covering the free variables, `I ⊧ᴵ g ↔ I ⊧ᴵ t` for every `I`; `acEqB g t`
    takes for `env` the free variables of `g` and of `t` paired in order of first occurrence.
-/
import KcoreSpec.Kore.Signature

set_option autoImplicit false

namespace KCore

namespace TieAlpha

open ML KoreAML

/-! ## The shape of a sorted disjunction -/

/-- `a ⋀ b`. -/
def conjParts : P → Option (P × P)
  | .implication (.implication (.implication (.implication a .bottom) .bottom) (.implication b .bottom))
      .bottom => some (a, b)
  | _ => none

/-- `∼a`. -/
def negParts : P → Option P
  | .implication a .bottom => some a
  | _ => none

/-- `(∼φ) ⋀ i`, the shape of `sNot s φ` with `i = inhOf s`. -/
def notParts (p : P) : Option (P × P) :=
  match conjParts p with
  | some (a, i) => (negParts a).map fun φ => (φ, i)
  | none => none

/-- `sOr s φ ψ` with `i = inhOf s`: `(i, φ, ψ)`. -/
def orParts (p : P) : Option (P × P × P) :=
  match notParts p with
  | some (x, i) => match conjParts x with
    | some (l, r) => match notParts l, notParts r with
      | some (φ, i1), some (ψ, i2) => if i1 = i ∧ i2 = i then some (i, φ, ψ) else none
      | _, _ => none
    | none => none
  | none => none

/-- The operands of a right-nested chain of disjunctions within `i`; the last is not one. -/
def orChain (i : P) : Nat → P → List P
  | 0, p => [p]
  | n + 1, p => match orParts p with
    | some (i', φ, ψ) => if i' = i then φ :: orChain i n ψ else [p]
    | none => [p]

section Interp

variable {M : Type} {I : Interpretation Sym M} {e : Valuation M}

theorem conjParts_eq {p a b : P} (h : conjParts p = some (a, b)) : p = a ⋀ b := by
  unfold conjParts at h
  split at h
  · cases h; rfl
  · cases h

theorem negParts_eq {p a : P} (h : negParts p = some a) : p = ∼a := by
  unfold negParts at h
  split at h
  · cases h; rfl
  · cases h

theorem notParts_eq {p φ i : P} (h : notParts p = some (φ, i)) : p = (∼φ) ⋀ i := by
  unfold notParts at h
  split at h
  · rename_i a i' hc
    obtain ⟨φ', hn, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    rw [conjParts_eq hc, negParts_eq hn]
  · cases h

theorem orParts_eq {p i φ ψ : P} (h : orParts p = some (i, φ, ψ)) :
    p = (∼(((∼φ) ⋀ i) ⋀ ((∼ψ) ⋀ i))) ⋀ i := by
  unfold orParts at h
  split at h
  · rename_i x i0 hx
    split at h
    · rename_i l r hlr
      split at h
      · rename_i φ' i1 ψ' i2 hl hr
        split at h
        · rename_i hi
          cases h
          rw [notParts_eq hx, conjParts_eq hlr, notParts_eq hl, notParts_eq hr, hi.1, hi.2]
        · cases h
      · cases h
    · cases h
  · cases h

/-- A sorted disjunction is the union of its operands within `i`. -/
theorem orParts_interp {p i φ ψ : P} (h : orParts p = some (i, φ, ψ)) (m : M) :
    p.interpret I e m ↔ (φ.interpret I e m ∨ ψ.interpret I e m) ∧ i.interpret I e m := by
  rw [orParts_eq h]
  simp only [interpret_conj, interpret_neg]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    refine Classical.byContradiction fun hc => ?_
    exact h1 ⟨⟨fun h => hc (Or.inl h), h2⟩, ⟨fun h => hc (Or.inr h), h2⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun ⟨⟨a, _⟩, ⟨b, _⟩⟩ => h1.elim a b, h2⟩

/-- Within `i`, a chain is the union of its operands. -/
theorem orChain_interp (i : P) (m : M) : ∀ (n : Nat) (p : P),
    (p.interpret I e m ∧ i.interpret I e m) ↔ ((∃ a ∈ orChain i n p, a.interpret I e m) ∧ i.interpret I e m)
  | 0, p => by simp [orChain]
  | n + 1, p => by
    unfold orChain
    split
    · rename_i i' φ ψ hp
      split
      · rename_i hi
        subst hi
        rw [orParts_interp hp]
        have ih := orChain_interp i' m n ψ
        simp only [List.mem_cons, exists_eq_or_imp]
        constructor
        · rintro ⟨⟨h | h, hi⟩, -⟩
          · exact ⟨Or.inl h, hi⟩
          · exact ⟨Or.inr (ih.mp ⟨h, hi⟩).1, hi⟩
        · rintro ⟨h | h, hi⟩
          · exact ⟨⟨Or.inl h, hi⟩, hi⟩
          · exact ⟨⟨Or.inr (ih.mpr ⟨h, hi⟩).1, hi⟩, hi⟩
      · simp
    · simp

end Interp

/-! ## Agreement up to the order of disjuncts and the names of variables -/

/-- The variables `x` and `y` correspond in `env`: the first pair naming `x` on the left or `y` on
the right is `(x, y)`. -/
def envOK (env : List (EVar × EVar)) (x y : EVar) : Bool :=
  match env.find? (fun p => decide (p.1 = x) || decide (p.2 = y)) with
  | some p => decide (p.1 = x) && decide (p.2 = y)
  | none => false

/-- `g` and `t` agree up to the order of the operands of their disjunctions and the names of their
variables, `env` pairing the variables bound around them (innermost first) and the free ones. -/
def acEq : Nat → List (EVar × EVar) → P → P → Bool
  | 0, _, _, _ => false
  | n + 1, env, g, t =>
    match orParts g, orParts t with
    | some (i, _, _), some (j, _, _) =>
      acEq n env i j &&
        ((orChain i n g).all fun a => (orChain j n t).any fun b => acEq n env a b) &&
        ((orChain j n t).all fun b => (orChain i n g).any fun a => acEq n env a b)
    | _, _ => match g, t with
      | .evar x, .evar y => envOK env x y
      | .svar X, .svar Y => decide (X = Y)
      | .bottom, .bottom => true
      | .symbol a, .symbol b => decide (a = b)
      | .application a b, .application c d => acEq n env a c && acEq n env b d
      | .implication a b, .implication c d => acEq n env a c && acEq n env b d
      | .existential x a, .existential y b => acEq n ((x, y) :: env) a b
      | .mu X a, .mu Y b => decide (X = Y) && acEq n env a b
      | _, _ => false

/-- The valuations agree along `env`. -/
def EnvAgree {M : Type} (env : List (EVar × EVar)) (e e' : Valuation M) : Prop :=
  ∀ x y, envOK env x y = true → e.evalEvar x = e'.evalEvar y

theorem envAgree_cons {M : Type} {env : List (EVar × EVar)} {e e' : Valuation M} (h : EnvAgree env e e')
    (x y : EVar) (a : M) :
    EnvAgree ((x, y) :: env) ⟨Function.update e.evalEvar x a, e.evalSvar⟩
      ⟨Function.update e'.evalEvar y a, e'.evalSvar⟩ := by
  intro x' y' hxy
  unfold envOK at hxy
  rw [List.find?_cons] at hxy
  by_cases hc : (decide (x = x') || decide (y = y')) = true
  · rw [hc] at hxy
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    simp [Function.update_same]
  · rw [Bool.not_eq_true] at hc
    rw [hc] at hxy
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hc
    simp only [Function.update_noteq (Ne.symm hc.1), Function.update_noteq (Ne.symm hc.2)]
    exact h x' y' hxy

theorem acEq_interp {M : Type} {I : Interpretation Sym M} : ∀ (n : Nat) {env : List (EVar × EVar)}
    {g t : P} {e e' : Valuation M}, acEq n env g t = true → EnvAgree env e e' → e.evalSvar = e'.evalSvar →
    ∀ m, g.interpret I e m ↔ t.interpret I e' m
  | 0, _, _, _, _, _, h, _, _ => by simp [acEq] at h
  | n + 1, env, g, t, e, e', h, he, hs => by
    unfold acEq at h
    split at h
    · rename_i i φ ψ j φ' ψ' hg ht
      simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at h
      obtain ⟨⟨hij, hgt⟩, htg⟩ := h
      have hi := acEq_interp (I := I) n hij he hs
      intro m
      have lg : g.interpret I e m ↔ g.interpret I e m ∧ i.interpret I e m :=
        ⟨fun h => ⟨h, ((orParts_interp hg m).mp h).2⟩, fun h => h.1⟩
      have lt : t.interpret I e' m ↔ t.interpret I e' m ∧ j.interpret I e' m :=
        ⟨fun h => ⟨h, ((orParts_interp ht m).mp h).2⟩, fun h => h.1⟩
      rw [lg, lt, orChain_interp i m n g, orChain_interp j m n t, hi m]
      refine and_congr_left fun _ => ?_
      constructor
      · rintro ⟨a, ha, hm⟩
        obtain ⟨b, hb, hab⟩ := hgt a ha
        exact ⟨b, hb, (acEq_interp (I := I) n hab he hs m).mp hm⟩
      · rintro ⟨b, hb, hm⟩
        obtain ⟨a, ha, hab⟩ := htg b hb
        exact ⟨a, ha, (acEq_interp (I := I) n hab he hs m).mpr hm⟩
    · split at h
      · rename_i x y _
        intro m
        simp only [Pattern.interpret, he x y h]
      · rename_i X Y _
        intro m
        simp only [decide_eq_true_eq] at h
        subst h
        simp only [Pattern.interpret, hs]
      · intro m; exact Iff.rfl
      · rename_i a b _
        intro m
        simp only [decide_eq_true_eq] at h
        subst h
        exact Iff.rfl
      · rename_i a b c d _
        simp only [Bool.and_eq_true] at h
        intro m
        simp only [Pattern.interpret]
        have h1 := acEq_interp (I := I) n h.1 he hs
        have h2 := acEq_interp (I := I) n h.2 he hs
        constructor
        · rintro ⟨u, v, hu, hv, hm⟩; exact ⟨u, v, (h1 u).mp hu, (h2 v).mp hv, hm⟩
        · rintro ⟨u, v, hu, hv, hm⟩; exact ⟨u, v, (h1 u).mpr hu, (h2 v).mpr hv, hm⟩
      · rename_i a b c d _
        simp only [Bool.and_eq_true] at h
        intro m
        simp only [Pattern.interpret]
        rw [acEq_interp (I := I) n h.1 he hs m, acEq_interp (I := I) n h.2 he hs m]
      · rename_i x a y b _
        intro m
        simp only [Pattern.interpret]
        constructor
        · rintro ⟨u, hu⟩
          exact ⟨u, (acEq_interp (I := I) n h (envAgree_cons he x y u) hs m).mp hu⟩
        · rintro ⟨u, hu⟩
          exact ⟨u, (acEq_interp (I := I) n h (envAgree_cons he x y u) hs m).mpr hu⟩
      · rename_i X a Y b _
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨rfl, h⟩ := h
        intro m
        simp only [Pattern.interpret]
        have hB : ∀ B : Set M, ∀ m, a.interpret I ⟨e.evalEvar, Function.update e.evalSvar X B⟩ m ↔
            b.interpret I ⟨e'.evalEvar, Function.update e'.evalSvar X B⟩ m :=
          fun B => acEq_interp (I := I) n h he (by simp only [hs])
        constructor
        · intro hm B hc
          exact hm B fun m' hm' => hc m' ((hB B m').mp hm')
        · intro hm B hc
          exact hm B fun m' hm' => hc m' ((hB B m').mpr hm')
      · cases h

/-! ## Sentences -/

theorem find?_of_le {α : Type} {P Q : α → Bool} (hQP : ∀ a, Q a = true → P a = true) :
    ∀ {l : List α} {a : α}, l.find? P = some a → Q a = true → l.find? Q = some a
  | [], _, h, _ => by cases h
  | b :: l, a, h, hq => by
    rw [List.find?_cons] at h ⊢
    by_cases hb : P b = true
    · rw [hb] at h
      cases h
      rw [hq]
    · rw [Bool.not_eq_true] at hb
      rw [hb] at h
      have hqb : Q b = false := by
        cases hc : Q b with
        | false => rfl
        | true => rw [hQP b hc] at hb; cases hb
      rw [hqb]
      exact find?_of_le hQP h hq

/-- From a valuation of `t`'s variables, one of `g`'s that agrees with it along `env`. -/
def leftOf {M : Type} (env : List (EVar × EVar)) (e' : Valuation M) : Valuation M :=
  ⟨fun x => match env.find? (fun p => decide (p.1 = x)) with
    | some p => e'.evalEvar p.2
    | none => e'.evalEvar x, e'.evalSvar⟩

/-- From a valuation of `g`'s variables, one of `t`'s that agrees with it along `env`. -/
def rightOf {M : Type} (env : List (EVar × EVar)) (e : Valuation M) : Valuation M :=
  ⟨fun y => match env.find? (fun p => decide (p.2 = y)) with
    | some p => e.evalEvar p.1
    | none => e.evalEvar y, e.evalSvar⟩

theorem envOK_find {env : List (EVar × EVar)} {x y : EVar} (h : envOK env x y = true) :
    env.find? (fun p => decide (p.1 = x) || decide (p.2 = y)) = some (x, y) := by
  unfold envOK at h
  split at h
  · rename_i p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [hp, show p = (x, y) from Prod.ext h.1 h.2]
  · cases h

theorem leftOf_agree {M : Type} (env : List (EVar × EVar)) (e' : Valuation M) :
    EnvAgree env (leftOf env e') e' := by
  intro x y h
  have hf := find?_of_le (Q := fun p => decide (p.1 = x)) (fun p hp => by simp [hp]) (envOK_find h)
    (by simp)
  simp only [leftOf, hf]

theorem rightOf_agree {M : Type} (env : List (EVar × EVar)) (e : Valuation M) :
    EnvAgree env e (rightOf env e) := by
  intro x y h
  have hf := find?_of_le (Q := fun p => decide (p.2 = y)) (fun p hp => by simp [hp]) (envOK_find h)
    (by simp)
  simp only [rightOf, hf]

/-- **Sentences that agree up to the order of disjuncts and the names of variables are satisfied
by the same interpretations.** -/
theorem acEq_sat {M : Type} {I : Interpretation Sym M} {n : Nat} {env : List (EVar × EVar)} {g t : P}
    (h : acEq n env g t = true) : (I ⊧ᴵ g) ↔ (I ⊧ᴵ t) := by
  constructor
  · intro hg e' m
    exact (acEq_interp (I := I) n h (leftOf_agree env e') rfl m).mp (hg _ m)
  · intro ht e m
    exact (acEq_interp (I := I) n h (rightOf_agree env e) rfl m).mpr (ht _ m)

/-- The free element variables of a pattern in order of occurrence, `bound` the binders around it. -/
def freeOcc (bound : List EVar) : P → List EVar
  | .evar x => if bound.contains x then [] else [x]
  | .application a b | .implication a b => freeOcc bound a ++ freeOcc bound b
  | .existential x a => freeOcc (x :: bound) a
  | .mu _ a => freeOcc bound a
  | _ => []

/-- The free variables of `g` and of `t`, paired in order of first occurrence. -/
def freeEnv (g t : P) : List (EVar × EVar) :=
  ((freeOcc [] g).eraseDups).zip ((freeOcc [] t).eraseDups)

/-- The depth bound of `acEqB`. -/
def acFuel : Nat := 100000

/-- `acEq` with the free variables paired by `freeEnv`. -/
def acEqB (g t : P) : Bool := acEq acFuel (freeEnv g t) g t

theorem acEqB_sat {M : Type} {I : Interpretation Sym M} {g t : P} (h : acEqB g t = true) :
    (I ⊧ᴵ g) ↔ (I ⊧ᴵ t) :=
  acEq_sat h

end TieAlpha

end KCore
