/-
  KCore, outside the cone: a function equation whose right side the text writes with an empty
  alternative, `\or{s}(p, x)` or `\or{s}(x, p)` where Γ's item writes `x` (the reader's
  `Parse.dropEmptyAlts`, the reading `orBottom`). For a tie file, beside `TieRhs.orBotIn`.

  - `emptyB`: a pattern that is `\bottom{S}()` at a sort constant S, or an application (no alias
    applies under the translation's context with no alias) one of whose arguments is such a
    `\bottom`; `tr_empty`: its translation holds no element, in every model of definedness. An
    application holds the elements its function part gives at an element of each argument
    (`interp_app`), so an application with an argument that holds nothing holds nothing
    (`trArgs_empty_acc`, `trArgs_empty_arg`).
  - `orEmptyIn le p`: the right side `\and{s'}(x, y)` read as `\and{s'}(\or{s}(p, x), y)` (`le`) or
    `\and{s'}(\or{s}(x, p), y)`; `orEmptyIn_agree`: where p holds nothing, the two agree on the
    sort's inhabitants (`orEmptyIn false (.bottom s)` is `orBotIn`'s form).
  - `emptyAltOf`: of a text's equation, which alternative of its right side is empty, and the
    alternative; `orEmptyOK`: the decided conditions under which `orEmptyOK_iff` gives Γ's item and
    the text's form `rhsMap (orEmptyIn le p)` of it the same models of definedness.
-/
import KcoreSpec.TieRhs

set_option autoImplicit false

namespace KCore

namespace TieRhs

open ML Faithful KoreAML

/-- `\bottom{S}()` at a sort constant S. -/
def botConstB : Kore.Pattern → Bool
  | .bottom (.ctor _ []) => true
  | _ => false

/-- **A pattern that holds nothing**: `\bottom{S}()` at a sort constant, or an application one of
whose arguments is such a `\bottom`. -/
def emptyB : Kore.Pattern → Bool
  | .bottom (.ctor _ []) => true
  | .app _ _ ps => ps.any botConstB
  | _ => false

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- An application whose function part holds nothing holds nothing. -/
theorem app_empty_left {φ ψ : P} {e : Valuation M} (h : ∀ a, ¬ φ.interpret I e a) (m : M) :
    ¬ (φ ⬝ ψ).interpret I e m := by
  rw [interp_app]
  rintro ⟨a, -, ha, -, -⟩
  exact h a ha

/-- An application whose argument holds nothing holds nothing. -/
theorem app_empty_right {φ ψ : P} {e : Valuation M} (h : ∀ b, ¬ ψ.interpret I e b) (m : M) :
    ¬ (φ ⬝ ψ).interpret I e m := by
  rw [interp_app]
  rintro ⟨-, b, -, hb, -⟩
  exact h b hb

/-- The arguments applied to a function part that holds nothing hold nothing. -/
theorem trArgs_empty_acc (ctx : Ctx) {e : Valuation M} :
    ∀ (ps : List Kore.Pattern) (acc : P), (∀ a, ¬ acc.interpret I e a) →
      ∀ m, ¬ (trArgs ctx acc ps).interpret I e m
  | [], _, h, m => by unfold trArgs; exact h m
  | p :: ps, acc, h, m => by
    unfold trArgs
    exact trArgs_empty_acc ctx ps _ (fun a => app_empty_left h a) m

/-- **An application with an argument that holds nothing holds nothing**, whatever its other
arguments and its function part. -/
theorem trArgs_empty_arg (ctx : Ctx) {e : Valuation M} :
    ∀ (ps : List Kore.Pattern) (acc : P), (∃ p ∈ ps, ∀ b, ¬ (tr ctx p).interpret I e b) →
      ∀ m, ¬ (trArgs ctx acc ps).interpret I e m
  | [], _, ⟨_, hp, _⟩, _ => absurd hp List.not_mem_nil
  | p :: ps, acc, ⟨q, hq, hqe⟩, m => by
    unfold trArgs
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact trArgs_empty_acc ctx ps _ (fun a => app_empty_right hqe a) m
    · exact trArgs_empty_arg ctx ps _ ⟨q, hq', hqe⟩ m

/-- `\bottom{S}()` at a sort constant holds nothing, in every model of definedness. -/
theorem tr_botConst_empty (hD : DefOK I) {t : VarTable} {p : Kore.Pattern} (hp : botConstB p = true)
    (e : Valuation M) (b : M) : ¬ (tr ⟨t, []⟩ p).interpret I e b := by
  match p, hp with
  | .bottom (.ctor C []), _ =>
    simp only [tr]
    unfold sBot
    rw [interp_sNot, interp_sTop hD (by simp [trSort, trSortApp, KoreAML.sym, Pattern.isFreeEvar])]
    exact fun h => h.1 h.2

/-- **A pattern `emptyB` accepts holds nothing**, in every model of definedness: `\bottom{S}()`
at a sort constant, or an application with such an argument. -/
theorem tr_empty (hD : DefOK I) {t : VarTable} {p : Kore.Pattern} (hp : emptyB p = true)
    (e : Valuation M) (b : M) : ¬ (tr ⟨t, []⟩ p).interpret I e b := by
  match p, hp with
  | .bottom (.ctor C []), _ => exact tr_botConst_empty hD rfl e b
  | .app h ss ps, hp =>
    simp only [tr, List.contains_nil, Bool.false_eq_true, ↓reduceIte]
    simp only [emptyB, List.any_eq_true] at hp
    obtain ⟨q, hq, hqb⟩ := hp
    exact trArgs_empty_arg _ ps _ ⟨q, hq, fun b' => tr_botConst_empty hD hqb e b'⟩ b

end

/-- `\and{s'}(x, y)` as `\and{s'}(\or{s}(p, x), y)` (`le`) or `\and{s'}(\or{s}(x, p), y)`; another
pattern is unchanged. -/
def orEmptyIn (le : Bool) (p : Kore.Pattern) (s : Kore.KSort) : Kore.Pattern → Kore.Pattern
  | .and s' [x, y] => .and s' [.or s (if le then [p, x] else [x, p]), y]
  | r => r

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **`\and{s'}(\or{s}(p, x), y)` (or with p second) and `\and{s'}(x, y)` agree on the sort `s`**
where p holds nothing. -/
theorem orEmptyIn_agree {t : VarTable} {le : Bool} {p : Kore.Pattern} {s s' : Kore.KSort}
    {r x y : Kore.Pattern} (hr : r = .and s' [x, y]) (e : Valuation M) (hp : ∀ b, ¬ (tr ⟨t, []⟩ p).interpret I e b) (b : M)
    (hb : (inhOf (trSort t s)).interpret I e b) :
    (tr ⟨t, []⟩ (orEmptyIn le p s r)).interpret I e b ↔ (tr ⟨t, []⟩ r).interpret I e b := by
  subst hr
  unfold orEmptyIn
  rw [tr_and2, tr_and2, interp_sAnd, interp_sAnd]
  cases le
  · simp only [Bool.false_eq_true, ↓reduceIte, tr, trOrList]
    rw [interp_sOr]
    constructor
    · rintro ⟨⟨-, hx | hpx⟩, hy⟩
      · exact ⟨hx, hy⟩
      · exact absurd hpx (hp b)
    · rintro ⟨hx, hy⟩
      exact ⟨⟨hb, Or.inl hx⟩, hy⟩
  · simp only [↓reduceIte, tr, trOrList]
    rw [interp_sOr]
    constructor
    · rintro ⟨⟨-, hpx | hx⟩, hy⟩
      · exact absurd hpx (hp b)
      · exact ⟨hx, hy⟩
    · rintro ⟨hx, hy⟩
      exact ⟨⟨hb, Or.inr hx⟩, hy⟩

end

/-- Of a text's equation `\implies{R}(prem, \equals{s, R'}(l, \and{s'}(\or{s}(p, x), y)))`, the
alternative that holds nothing (`emptyB`): the first (`true`) or the second (`false`), with it. -/
def emptyAltOf : Kore.Pattern → Option (Bool × Kore.Pattern)
  | .implies _ _ (.equals _ _ _ (.and _ [.or _ [p, x], _])) =>
    if emptyB p then some (true, p) else if emptyB x then some (false, x) else none
  | _ => none

/-- The conditions of `orEmptyOK_iff`, decided: `a` is an equation axiom whose right side is a
conjunction of two, p holds nothing,
and the axiom with its right side's first conjunct written with p as an alternative has `a`'s
variable table, guards and sort. -/
def orEmptyOK (le : Bool) (p : Kore.Pattern) (a : Kore.Axiom) : Bool :=
  emptyB p &&
  (match a.pattern with
    | .implies _ _ (.equals _ _ _ (.and _ [_, _])) => true
    | _ => false) &&
  decide (tableOf (rhsMap (orEmptyIn le p) a).sortVars (rhsMap (orEmptyIn le p) a).pattern =
    tableOf a.sortVars a.pattern) &&
  decide (((rhsMap (orEmptyIn le p) a).sortVars.map sortVarKey ++ freeOf [] (rhsMap (orEmptyIn le p) a).pattern).eraseDups =
    (a.sortVars.map sortVarKey ++ freeOf [] a.pattern).eraseDups) &&
  decide (sortOf [] (rhsMap (orEmptyIn le p) a).pattern = sortOf [] a.pattern)

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **An equation axiom and its form with an empty alternative beside its right side's first
conjunct hold in the same models of definedness** (`rhsMap_iff` with `orEmptyIn_agree` and
`tr_empty`), where `orEmptyOK` holds. -/
theorem orEmptyOK_iff (hD : DefOK I) {le : Bool} {p : Kore.Pattern} {a : Kore.Axiom}
    (h : orEmptyOK le p a = true) :
    (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", rhsMap (orEmptyIn le p) a⟩).pat) ↔
      (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat) := by
  unfold orEmptyOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hp, hshape⟩, htbl⟩, hfr⟩, hsrt⟩ := h
  split at hshape
  · next R prem s R' l s' x y hpat =>
    exact rhsMap_iff hD hpat
      (fun e b hb => orEmptyIn_agree rfl e (tr_empty hD hp e) b hb)
      htbl hfr hsrt
  · cases hshape

end

end TieRhs

end KCore
