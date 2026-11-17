/-
  KCore, outside the cone: a rule axiom whose `requires` the text writes as a pattern at Bool
  equated with `true` where Γ's item writes a Bool term (`predicateAtBool`, `andAtBool`), in the
  direction from Γ to the text at values (`EntailsAtValues`).

  - `ruleItem_of_empty`: the item of `\rewrites{C}(L, r)` holds at a valuation where `L` holds
    nothing.
  - `boolTwo`: in a model of the signature and the domains, Bool is one sort, and the values
    `false` and `true` denote two elements of it.
  - `eqTrue_empty`: `\equals{SortBool{}, s}(p, \dv{SortBool{}}("true"))` holds nothing where `p`
    holds the same of every two elements of Bool: it would have to hold `true` and not `false`.
  - `ceil_const`: `\ceil{S, SortBool{}}(p)`, where `p`'s elements are in the sort `S`, holds all of
    Bool or none of it.
  - `substAt ρ p`: the pattern `p` with each element variable `x` for which `ρ x` is a pattern
    replaced by it, under applications only. `substAt_iff`: where each such `ρ x` denotes exactly
    the element the valuation gives `x`, the two patterns denote the same elements.
-/
import KcoreSpec.TieRuleLhs

set_option autoImplicit false

namespace KCore

namespace TieReqBool

open ML Faithful KoreAML

mutual
  /-- `p` with each element variable `x` for which `ρ x` is a pattern replaced by it, under
  applications; a pattern of another form is unchanged. -/
  def substAt (ρ : Kore.EVar → Option Kore.Pattern) : Kore.Pattern → Kore.Pattern
    | .var (.evar x) => (ρ x).getD (.var (.evar x))
    | .app h ss ps => .app h ss (substAtList ρ ps)
    | p => p
    termination_by structural p => p
  def substAtList (ρ : Kore.EVar → Option Kore.Pattern) : List Kore.Pattern → List Kore.Pattern
    | [] => []
    | p :: ps => substAt ρ p :: substAtList ρ ps
    termination_by structural ps => ps
end

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **A rule axiom holds where its left side holds nothing.** -/
theorem ruleItem_of_empty (hD : DefOK I) {t : VarTable} {free : List VarKey} {C : Kore.KSort}
    {L r : Kore.Pattern} {e : Valuation M} (h : ∀ a, ¬ (tr ⟨t, []⟩ L).interpret I e a) (m : M) :
    (TieRuleLhs.itemAt t free C L r).interpret I e m := by
  unfold TieRuleLhs.itemAt
  rw [interpret_impl]
  intro _
  rw [interp_equal hD]
  intro a
  have hT : tr ⟨t, []⟩ (.rewrites C L r) = sRewrites (trSort t C) (tr ⟨t, []⟩ L) (tr ⟨t, []⟩ r) := by rw [tr]
  rw [hT]
  unfold sRewrites
  rw [interp_sImp]
  exact ⟨fun h1 => h1.1, fun h1 => ⟨h1, fun hl => absurd hl (h a)⟩⟩

section subst
variable {t : VarTable} {e : Valuation M} {ρ : Kore.EVar → Option Kore.Pattern}

set_option linter.unusedSectionVars false in
mutual
  /-- **A substitution of patterns denoting the variables' elements keeps what a pattern
  denotes.** -/
  theorem substAt_iff
      (hρ : ∀ x q, ρ x = some q → ∀ m, (tr ⟨t, []⟩ q).interpret I e m ↔ m = e.evalEvar (t.ev (evarKey x))) :
      ∀ (p : Kore.Pattern) (m : M), (tr ⟨t, []⟩ (substAt ρ p)).interpret I e m ↔ (tr ⟨t, []⟩ p).interpret I e m
    | .var (.evar x), m => by
      rw [substAt]
      cases hx : ρ x with
      | none => exact Iff.rfl
      | some q =>
        rw [Option.getD_some, hρ x q hx m, tr, interp_evar]
    | .app h ss ps, m => by
      rw [substAt, tr, tr]
      split
      · exact Iff.rfl
      · exact substAtList_iff hρ ps _ _ (fun _ => Iff.rfl) m
    | .var (.svar _), _ => by rw [substAt] <;> simp
    | .string _, _ => by rw [substAt] <;> simp
    | .top _, _ => by rw [substAt] <;> simp
    | .bottom _, _ => by rw [substAt] <;> simp
    | .not _ _, _ => by rw [substAt] <;> simp
    | .and _ _, _ => by rw [substAt] <;> simp
    | .or _ _, _ => by rw [substAt] <;> simp
    | .implies _ _ _, _ => by rw [substAt] <;> simp
    | .iff _ _ _, _ => by rw [substAt] <;> simp
    | .exist _ _ _, _ => by rw [substAt] <;> simp
    | .forall _ _ _, _ => by rw [substAt] <;> simp
    | .mu _ _, _ => by rw [substAt] <;> simp
    | .nu _ _, _ => by rw [substAt] <;> simp
    | .ceil _ _ _, _ => by rw [substAt] <;> simp
    | .floor _ _ _, _ => by rw [substAt] <;> simp
    | .equals _ _ _ _, _ => by rw [substAt] <;> simp
    | .in _ _ _ _, _ => by rw [substAt] <;> simp
    | .next _ _, _ => by rw [substAt] <;> simp
    | .rewrites _ _ _, _ => by rw [substAt] <;> simp
    | .dv _ _, _ => by rw [substAt] <;> simp
    | .leftAssoc _ _ _, _ => by rw [substAt] <;> simp
    | .rightAssoc _ _ _, _ => by rw [substAt] <;> simp
  termination_by structural p => p
  theorem substAtList_iff
      (hρ : ∀ x q, ρ x = some q → ∀ m, (tr ⟨t, []⟩ q).interpret I e m ↔ m = e.evalEvar (t.ev (evarKey x))) :
      ∀ (ps : List Kore.Pattern) (acc acc' : P), (∀ m, acc.interpret I e m ↔ acc'.interpret I e m) →
        ∀ m, (trArgs ⟨t, []⟩ acc (substAtList ρ ps)).interpret I e m ↔ (trArgs ⟨t, []⟩ acc' ps).interpret I e m
    | [], acc, acc', hacc, m => by
      rw [substAtList, trArgs_nil, trArgs_nil]; exact hacc m
    | p :: ps, acc, acc', hacc, m => by
      rw [substAtList, trArgs_cons, trArgs_cons]
      exact substAtList_iff hρ ps _ _ (interp_app_congr hacc (substAt_iff hρ p)) m
  termination_by structural ps => ps
end

end subst

/-- **Bool is one sort with two elements `false` and `true`**, in a model of the signature and the
domains of a semantics `c`. -/
theorem boolTwo [Inhabited M] (hD : DefOK I) {c : Semantics} [OvlOK c] (hSig : I ⊧ᴵP ΓSig c) (hDom : I ⊧ᴵP ΓDomains c)
    (hsf : c.sortOf (KCore.bool false) = some Srt.bool) (hst : c.sortOf (KCore.bool true) = some Srt.bool)
    (hdf : den c (KCore.bool false) = sym (.dv "false") ⬝ sym (.sort "SortBool"))
    (hdt : den c (KCore.bool true) = sym (.dv "true") ⬝ sym (.sort "SortBool")) (t : VarTable) (e : Valuation M) :
    ∃ σB aF aT, (∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB) ∧ IsSort I σB ∧
      (∀ m, (tr ⟨t, []⟩ (.dv (srt "Bool") "false")).interpret I e m ↔ m = aF) ∧
      (∀ m, (tr ⟨t, []⟩ (.dv (srt "Bool") "true")).interpret I e m ↔ m = aT) ∧
      aF ≠ aT ∧ Inh I σB aF ∧ Inh I σB aT := by
  obtain ⟨σB, hσB1, hσB2⟩ := TieRhs.sortSing_sig hD hSig (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  have hSB : ∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB := by rw [trSort_srt]; exact hσB1
  obtain ⟨aF, haf, hif⟩ := TieRhs.den_single_dom hD hDom hsf e
  obtain ⟨aT, hat, hit⟩ := TieRhs.den_single_dom hD hDom hst e
  have htr : ∀ (n : String), tr ⟨t, []⟩ (.dv (srt "Bool") n) = sym (.dv n) ⬝ sym (.sort "SortBool") := by
    intro n; rw [tr, trSort_srt]; rfl
  rw [sortName_bool] at hif hit
  refine ⟨σB, aF, aT, hSB, hσB2, fun m => ?_, fun m => ?_, fun hfa => ?_,
    (interp_inhOf_of (S := sortP "Bool") hσB1).mp hif, (interp_inhOf_of (S := sortP "Bool") hσB1).mp hit⟩
  · rw [htr, ← hdf]; exact haf m
  · rw [htr, ← hdt]; exact hat m
  · have hne := hDom _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨KCore.bool false, KCore.bool true, Srt.bool,
      List.contains_iff_mem.mpr bool_distinct, hsf, hst,
      fun h => by have := GroundTerm.cmp_eq _ _ h; simp [KCore.bool] at this, rfl⟩)))) e aF
    rw [interpret_neg, interpret_conj] at hne
    exact hne ⟨(haf aF).mpr rfl, (hat aF).mpr hfa⟩

/-- **`p = true` at Bool holds nothing where `p` holds the same of every two elements of Bool**:
at `true` it must hold, at `false` it must not. -/
theorem eqTrue_empty [Inhabited M] (hD : DefOK I) {c : Semantics} [OvlOK c] (hSig : I ⊧ᴵP ΓSig c) (hDom : I ⊧ᴵP ΓDomains c)
    (hsf : c.sortOf (KCore.bool false) = some Srt.bool) (hst : c.sortOf (KCore.bool true) = some Srt.bool)
    (hdf : den c (KCore.bool false) = sym (.dv "false") ⬝ sym (.sort "SortBool"))
    (hdt : den c (KCore.bool true) = sym (.dv "true") ⬝ sym (.sort "SortBool"))
    {t : VarTable} {s : Kore.KSort} {σ : M} {e : Valuation M}
    (hs : ∀ a, (trSort t s).interpret I e a ↔ a = σ) (hσ : IsSort I σ) {p : Kore.Pattern}
    (hp : ∀ σB, (∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB) → IsSort I σB → ∀ x y, Inh I σB x → Inh I σB y →
      ((tr ⟨t, []⟩ p).interpret I e x ↔ (tr ⟨t, []⟩ p).interpret I e y)) (b : M) :
    ¬ (tr ⟨t, []⟩ (.equals (srt "Bool") s p (.dv (srt "Bool") "true"))).interpret I e b := by
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  obtain ⟨σB, aF, aT, hSB, hσB, haf, hat, hne, hif, hit⟩ := boolTwo hD hSig hDom hsf hst hdf hdt t e
  have hT : tr ⟨t, []⟩ (.equals (srt "Bool") s p (.dv (srt "Bool") "true")) =
      sEquals (trSort t (srt "Bool")) (trSort t s) (tr ⟨t, []⟩ p) (tr ⟨t, []⟩ (.dv (srt "Bool") "true")) := by rw [tr]
  rw [hT, interp_sEquals hD hc hSB hs hσB hσ]
  rintro ⟨-, h⟩
  have h1 := (h aT hit).mpr ((hat aT).mpr rfl)
  have h2 := (hp σB hSB hσB aF aT hif hit).mpr h1
  exact hne ((hat aF).mp ((h aF hif).mp h2))

/-- **`\ceil{S, SortBool{}}(p)` is all of Bool or none of it**, where `p`'s elements are in `S`. -/
theorem ceil_const [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {t : VarTable} {S : Kore.KSort} {σS σB : M}
    {e : Valuation M} (hS : ∀ a, (trSort t S).interpret I e a ↔ a = σS) (hσS : IsSort I σS)
    (hSB : ∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB) (hσB : IsSort I σB) {p : Kore.Pattern}
    (hp : ∀ a, (tr ⟨t, []⟩ p).interpret I e a → Inh I σS a) (x y : M) (hx : Inh I σB x) (hy : Inh I σB y) :
    (tr ⟨t, []⟩ (.ceil S (srt "Bool") p)).interpret I e x ↔ (tr ⟨t, []⟩ (.ceil S (srt "Bool") p)).interpret I e y := by
  have hT : tr ⟨t, []⟩ (.ceil S (srt "Bool") p) = sCeil (trSort t S) (trSort t (srt "Bool")) (tr ⟨t, []⟩ p) := by rw [tr]
  rw [hT, interp_sCeil hD hc hS hSB hσS hσB hp, interp_sCeil hD hc hS hSB hσS hσB hp]
  exact ⟨fun h => ⟨h.1, hy⟩, fun h => ⟨h.1, hx⟩⟩

end

end TieReqBool

end KCore
