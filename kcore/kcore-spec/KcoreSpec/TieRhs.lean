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
  - `botTop`: `\and{s}(\bottom{s}(), \top{s}())` for a right side `\and{s}(x, y)` whose second
    conjunct holds nothing (`botTop_agree`); `ensFalse s`, the `ensures` false
    (`\equals{SortBool{}, s}(false, true)`), holds nothing in a model of the signature and the
    domains of a semantics, where the values `false` and `true` of Bool are two elements
    (`ensFalse_empty`).
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

/-- `\and{s}(\bottom{s}(), \top{s}())`, whatever the right side. -/
def botTop (s : Kore.KSort) (_ : Kore.Pattern) : Kore.Pattern := .and s [.bottom s, .top s]

/-- The `ensures` false at the sort `s`: `\equals{SortBool{}, s}(\dv{SortBool{}}("false"), \dv{SortBool{}}("true"))`. -/
def ensFalse (s : Kore.KSort) : Kore.Pattern :=
  .equals (srt "Bool") s (.dv (srt "Bool") "false") (.dv (srt "Bool") "true")

/-- `\and{s}(\bottom{s}(), \top{s}())` and `\and{s}(x, y)` agree where `y` holds nothing: both hold
nothing. -/
theorem botTop_agree (hD : DefOK I) {t : VarTable} {s : Kore.KSort} {r x y : Kore.Pattern}
    (hr : r = .and s [x, y]) (hs : (trSort t s).isFreeEvar topVar = false) (e : Valuation M)
    (hy : ∀ b, ¬ (tr ⟨t, []⟩ y).interpret I e b) (b : M) :
    (tr ⟨t, []⟩ (botTop s r)).interpret I e b ↔ (tr ⟨t, []⟩ r).interpret I e b := by
  subst hr
  unfold botTop
  rw [tr_and2, tr_and2, interp_sAnd, interp_sAnd]
  simp only [tr]
  unfold sBot
  rw [interp_sNot, interp_sTop hD hs]
  exact ⟨fun h => absurd h.1.2 h.1.1, fun h => absurd h.2 (hy b)⟩

/-- A numbered sort denotes one sort, in a model of the signature. -/
theorem sortSing_sig [Inhabited M] (hD : DefOK I) {c : Semantics} [OvlOK c] (hSig : I ⊧ᴵP ΓSig c) {s : Srt}
    (hs : s < nRegSorts + c.sortNames.length) :
    ∃ σ, (∀ a, I.evalSymb (.sort ("Sort" ++ c.sortName s)) a ↔ a = σ) ∧ IsSort I σ :=
  sortConst_of hD (hSig _ (Or.inl (Or.inl ⟨_, sig_sortConst hs, rfl⟩)))

/-- A value of the sort `s` denotes one element, an element of `s`, in a model of the domains. -/
theorem den_single_dom [Inhabited M] (hD : DefOK I) {c : Semantics} (hDom : I ⊧ᴵP ΓDomains c) {v : GroundTerm}
    {s : Srt} (h : c.sortOf v = some s) (e : Valuation M) :
    ∃ a, (∀ m, (den c v).interpret I e m ↔ m = a) ∧ (inhOf (sortP (c.sortName s))).interpret I e a := by
  have hax := hDom _ (Or.inr (Or.inr (Or.inl ⟨v, s, h, rfl⟩))) e default
  rw [interp_sExists] at hax
  obtain ⟨a, h1, h2⟩ := hax
  rw [interp_member hD] at h1
  simp only [Function.update_same] at h1
  rw [interp_equal hD] at h2
  refine ⟨a, fun m => ?_, ?_⟩
  · rw [(den_closed c v).interp e ⟨Function.update e.evalEvar ⟨1⟩ a, e.evalSvar⟩ m, h2 m, interp_evar]
    simp only [Function.update_same]
  · exact (((Closed.sym _).app (Closed.sym _)).interp _ e a).mp h1

/-- **The `ensures` false holds nothing** in a model of the signature and the domains of a
semantics `c`: the values `false` and `true` of Bool denote two elements of Bool (`ΓDomains`: each
value is one element of its sort, and distinct values of Bool share none), so the two sides of the
equality differ on Bool. -/
theorem ensFalse_empty [Inhabited M] (hD : DefOK I) {c : Semantics} [OvlOK c] (hSig : I ⊧ᴵP ΓSig c) (hDom : I ⊧ᴵP ΓDomains c)
    (hsf : c.sortOf (KCore.bool false) = some Srt.bool) (hst : c.sortOf (KCore.bool true) = some Srt.bool)
    (hdf : den c (KCore.bool false) = sym (.dv "false") ⬝ sym (.sort "SortBool"))
    (hdt : den c (KCore.bool true) = sym (.dv "true") ⬝ sym (.sort "SortBool"))
    {t : VarTable} {s : Kore.KSort} {σ : M} {e : Valuation M}
    (hs : ∀ a, (trSort t s).interpret I e a ↔ a = σ) (hσ : IsSort I σ) (b : M) :
    ¬ (tr ⟨t, []⟩ (ensFalse s)).interpret I e b := by
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing_sig hD hSig (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  have hSB : ∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB := by rw [trSort_srt]; exact hσB1
  unfold ensFalse
  simp only [tr]
  rw [interp_sEquals hD hc hSB hs hσB2 hσ]
  rintro ⟨-, h⟩
  obtain ⟨a, haf, hai⟩ := den_single_dom hD hDom hsf e
  have hne := hDom _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨KCore.bool false, KCore.bool true, Srt.bool,
    List.contains_iff_mem.mpr bool_distinct, hsf, hst,
    fun h => by have := GroundTerm.cmp_eq _ _ h; simp [KCore.bool] at this, rfl⟩)))) e a
  rw [interpret_neg, interpret_conj] at hne
  rw [sortName_bool] at hai
  have hia : Inh I σB a := (interp_inhOf_of (S := sortP "Bool") hσB1).mp hai
  have h3 := h a hia
  rw [trSort_srt] at h3
  rw [hdf, hdt] at hne
  rw [hdf] at haf
  exact hne ⟨(haf a).mpr rfl, h3.mp ((haf a).mpr rfl)⟩

end

end TieRhs

end KCore
