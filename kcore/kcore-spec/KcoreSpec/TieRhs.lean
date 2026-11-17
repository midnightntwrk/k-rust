/-
  KCore, outside the cone: a function equation whose right side the text writes in another form
  than Γ's item, with the same inhabitants of the result sort. For a tie file where a reading note
  rewrites a right side (`andAsEnsures`, `orBottom`): the item with its right side `r` replaced by
  `g s r` (`rhsMap g a`) holds in exactly the models of the item, wherever `g s r` and `r` denote
  the same elements of the sort `s` (`rhsMap_iff`), the two axioms having one variable table, one
  guard list and one sort (kernel decisions on the literal axiom).

  - `andTop`: `\and{s}(r, \top{s}())` (kompile's right side `rhs ∧ ens` with no `ensures`).
  - `orBotIn`: `\and{s'}(x, y)` read as `\and{s'}(\or{s}(x, \bottom{s}()), y)` (a disjunct `⊥`).
  Both agree with `r` on the sort's inhabitants in every model of definedness (`andTop_agree`,
  `orBotIn_agree`), where the sort is a constant (its translation binds no variable).
-/
import KcoreSpec.TiePairs

set_option autoImplicit false

namespace KCore

namespace TieRhs

open ML Faithful KoreAML

/-- An equation axiom `\implies{R}(prem, \equals{s, R'}(l, r))` with its right side `r` replaced by
`g s r`; an axiom of another form is unchanged. -/
def rhsMap (g : Kore.KSort → Kore.Pattern → Kore.Pattern) (a : Kore.Axiom) : Kore.Axiom :=
  match a.pattern with
  | .implies R prem (.equals s R' l r) => { a with pattern := .implies R prem (.equals s R' l (g s r)) }
  | _ => a

/-- `\and{s}(r, \top{s}())`. -/
def andTop (s : Kore.KSort) (r : Kore.Pattern) : Kore.Pattern := .and s [r, .top s]

/-- `\and{s'}(x, y)` as `\and{s'}(\or{s}(x, \bottom{s}()), y)`; another pattern is unchanged. -/
def orBotIn (s : Kore.KSort) : Kore.Pattern → Kore.Pattern
  | .and s' [x, y] => .and s' [.or s [x, .bottom s], y]
  | r => r

/-- An equation axiom, read as its parts. -/
def eqParts : Kore.Pattern → Option (Kore.KSort × Kore.Pattern × Kore.KSort × Kore.KSort × Kore.Pattern × Kore.Pattern)
  | .implies R prem (.equals s R' l r) => some (R, prem, s, R', l, r)
  | _ => none

theorem eqParts_eq {p : Kore.Pattern} {R s R' : Kore.KSort} {prem l r : Kore.Pattern}
    (h : eqParts p = some (R, prem, s, R', l, r)) : p = .implies R prem (.equals s R' l r) := by
  unfold eqParts at h
  split at h
  · cases h; rfl
  · cases h

theorem rhsMap_pattern {g : Kore.KSort → Kore.Pattern → Kore.Pattern} {a : Kore.Axiom} {R s R' : Kore.KSort}
    {prem l r : Kore.Pattern} (ha : a.pattern = .implies R prem (.equals s R' l r)) :
    (rhsMap g a).pattern = .implies R prem (.equals s R' l (g s r)) := by
  unfold rhsMap; rw [ha]

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- `φ = ψ` and `φ = ψ'` at the sort `S` agree where `ψ` and `ψ'` agree on `S`'s inhabitants. -/
theorem sEquals_congr {S S' φ ψ ψ' : P} {e : Valuation M}
    (h : ∀ a, (inhOf S).interpret I e a → (ψ.interpret I e a ↔ ψ'.interpret I e a)) (m : M) :
    (sEquals S S' φ ψ).interpret I e m ↔ (sEquals S S' φ ψ').interpret I e m := by
  have hin : ∀ a, (sNot S (sIff S φ ψ)).interpret I e a ↔ (sNot S (sIff S φ ψ')).interpret I e a := by
    intro a
    simp only [interp_sNot, interp_sIff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun ⟨h3, h4⟩ => h1 ⟨h3, h4.trans (h a h2).symm⟩, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun ⟨h3, h4⟩ => h1 ⟨h3, h4.trans (h a h2)⟩, h2⟩
  unfold sEquals sFloor sCeil
  simp only [interp_sNot, interp_app, hin]

/-- **An equation axiom and its form with the right side `g s r` hold in the same models of
definedness**, where `g s r` and `r` denote the same elements of the sort `s` under the axiom's
variable table, and the two axioms have one variable table, one guard list and one sort. -/
theorem rhsMap_iff (hD : DefOK I) {g : Kore.KSort → Kore.Pattern → Kore.Pattern} {a : Kore.Axiom}
    {R s R' : Kore.KSort} {prem l r : Kore.Pattern}
    (ha : a.pattern = .implies R prem (.equals s R' l r))
    (hg : ∀ (e : Valuation M) (b : M), (inhOf (trSort (tableOf a.sortVars a.pattern) s)).interpret I e b →
      ((tr ⟨tableOf a.sortVars a.pattern, []⟩ (g s r)).interpret I e b ↔
        (tr ⟨tableOf a.sortVars a.pattern, []⟩ r).interpret I e b))
    (htbl : tableOf (rhsMap g a).sortVars (rhsMap g a).pattern = tableOf a.sortVars a.pattern)
    (hfr : ((rhsMap g a).sortVars.map sortVarKey ++ freeOf [] (rhsMap g a).pattern).eraseDups =
      (a.sortVars.map sortVarKey ++ freeOf [] a.pattern).eraseDups)
    (hsrt : sortOf [] (rhsMap g a).pattern = sortOf [] a.pattern) :
    (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", rhsMap g a⟩).pat) ↔ (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat) := by
  have hbody : ∀ e m, (tr ⟨tableOf a.sortVars a.pattern, []⟩ (rhsMap g a).pattern).interpret I e m ↔
      (tr ⟨tableOf a.sortVars a.pattern, []⟩ a.pattern).interpret I e m := by
    intro e m
    generalize ht : tableOf a.sortVars a.pattern = t at hg ⊢
    rw [rhsMap_pattern ha, ha]
    simp only [tr, interp_sImp]
    rw [sEquals_congr (ψ' := tr ⟨t, []⟩ r) (fun b hb => hg e b hb) m]
  unfold trAxiom
  dsimp only
  rw [htbl, hfr, hsrt]
  constructor
  · intro h e m
    have h1 := h e m
    rw [interpret_impl] at h1 ⊢
    intro hgd
    have h2 := h1 hgd
    rw [interp_equal hD] at h2 ⊢
    intro b
    rw [← hbody]; exact h2 b
  · intro h e m
    have h1 := h e m
    rw [interpret_impl] at h1 ⊢
    intro hgd
    have h2 := h1 hgd
    rw [interp_equal hD] at h2 ⊢
    intro b
    rw [hbody]; exact h2 b

/-- `\and{s}(r, \top{s}())` and `r` agree on the sort `s`, a sort whose translation leaves the
variable of `⊤` unbound. -/
theorem andTop_agree (hD : DefOK I) {t : VarTable} {s : Kore.KSort} {r : Kore.Pattern}
    (hs : (trSort t s).isFreeEvar topVar = false) (e : Valuation M) (b : M)
    (hb : (inhOf (trSort t s)).interpret I e b) :
    (tr ⟨t, []⟩ (andTop s r)).interpret I e b ↔ (tr ⟨t, []⟩ r).interpret I e b := by
  unfold andTop
  rw [tr_and2, interp_sAnd]
  simp only [tr]
  rw [interp_sTop hD hs]
  exact ⟨fun h => h.1, fun h => ⟨h, hb⟩⟩

/-- `\and{s'}(\or{s}(x, \bottom{s}()), y)` and `\and{s'}(x, y)` agree on the sort `s`. -/
theorem orBotIn_agree (hD : DefOK I) {t : VarTable} {s s' : Kore.KSort} {r x y : Kore.Pattern}
    (hr : r = .and s' [x, y]) (hs : (trSort t s).isFreeEvar topVar = false) (e : Valuation M) (b : M)
    (hb : (inhOf (trSort t s)).interpret I e b) :
    (tr ⟨t, []⟩ (orBotIn s r)).interpret I e b ↔ (tr ⟨t, []⟩ r).interpret I e b := by
  subst hr
  unfold orBotIn
  rw [tr_and2, tr_and2, interp_sAnd, interp_sAnd]
  simp only [tr, trOrList]
  rw [interp_sOr]
  unfold sBot
  rw [interp_sNot, interp_sTop hD hs]
  constructor
  · rintro ⟨⟨-, hx | ⟨hn, hi⟩⟩, hy⟩
    · exact ⟨hx, hy⟩
    · exact absurd hi hn
  · rintro ⟨hx, hy⟩
    exact ⟨⟨hb, Or.inl hx⟩, hy⟩

end

end TieRhs

end KCore
