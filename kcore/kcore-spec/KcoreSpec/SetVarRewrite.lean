/-
  A rewrite sentence whose set variable stands under applications only, as kompile writes
  `rule <k> c(@S, @S) => d(@S) </k>`: `L[@S, @S] → •R[@S]`. Read as an axiom the set variable is
  free, and the sentence holds for every set S inside the variable's sort.

  Under applications (and conjunctions with patterns that do not hold the variable) a pattern
  grows with S and is the union of its instances at elements: `L[S]` is the union of `L[ā]` over
  the choices ā of one element of S for each occurrence (`SvCtx.atSet_iff`, the cut identity
  `cut_sem` at several holes). So a point of `L[ā]` is covered by the instance of the sentence at
  every S that holds ā, and of those the one at `S = {ā}` states most, `R[{ā}]` being inside
  `R[S]`: the sentence at every S is "for all ā, `L[ā]` has a successor in `R[{ā}]`"
  (`setvar_rewrite_singleton`), and `R[{ā}]` is the union of `R[z̄]` over the z̄ each of which is
  one of the ā: `∃z̄. R[z̄] ∧ ⋀ⱼ ⋁ᵢ zⱼ ∈ aᵢ`, one variable per right occurrence.

  Stated on KoreAML patterns in every interpretation, at each point: nothing here is about K's
  semantics beyond `sNext`. `SvCtx.atVars_iff` reads the instance at elements as the pattern with
  one element variable per occurrence.
-/
import KcoreSpec.SetVarIn

set_option autoImplicit false

namespace KCore

open ML KoreAML

variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- A pattern in which a set variable stands under applications only: an occurrence of the
variable, a pattern that does not hold it, an application of two such, or one such in conjunction
with a pattern that does not hold it (a sentence's `\and(L, ⊤)`). -/
inductive SvCtx where
  | hole
  | side (ψ : P)
  | app (C D : SvCtx)
  | andSide (C : SvCtx) (ψ : P)

namespace SvCtx

/-- The number of occurrences. -/
def holes : SvCtx → Nat
  | .hole => 1
  | .side _ => 0
  | .app C D => C.holes + D.holes
  | .andSide C _ => C.holes

/-- The pattern with the set variable X at each occurrence. -/
def atSet (X : SVar) : SvCtx → P
  | .hole => .svar X
  | .side ψ => ψ
  | .app C D => C.atSet X ⬝ D.atSet X
  | .andSide C ψ => sAnd (C.atSet X) ψ

/-- The pattern with the element variable `xs k` at the occurrence k, the occurrences numbered
from n, left to right. -/
def atVars (xs : Nat → EVar) : SvCtx → Nat → P
  | .hole, n => .evar (xs n)
  | .side ψ, _ => ψ
  | .app C D, n => C.atVars xs n ⬝ D.atVars xs (n + C.holes)
  | .andSide C ψ, n => sAnd (C.atVars xs n) ψ

/-- No pattern beside the occurrences holds X. -/
def Sides (X : SVar) : SvCtx → Prop
  | .hole => True
  | .side ψ => ψ.isFreeSvar X = false
  | .app C D => C.Sides X ∧ D.Sides X
  | .andSide C ψ => C.Sides X ∧ ψ.isFreeSvar X = false

/-- The elements of the pattern with the element `a k` at the occurrence k (numbered from n). -/
def den (I : Interpretation KoreAML.Sym M) (e : Valuation M) (a : Nat → M) : SvCtx → Nat → M → Prop
  | .hole, n, m => m = a n
  | .side ψ, _, m => ψ.interpret I e m
  | .app C D, n, m => ∃ p b, C.den I e a n p ∧ D.den I e a (n + C.holes) b ∧ I.evalApp p b m
  | .andSide C ψ, n, m => C.den I e a n m ∧ ψ.interpret I e m

/-- `den` reads the elements at the pattern's own occurrences only. -/
theorem den_congr (e : Valuation M) {a a' : Nat → M} : ∀ (C : SvCtx) (n : Nat),
    (∀ i, i < C.holes → a (n + i) = a' (n + i)) → ∀ m, C.den I e a n m ↔ C.den I e a' n m
  | .hole, n, h, m => by
    have := h 0 (by simp [holes])
    simp only [Nat.add_zero] at this
    simp only [den, this]
  | .side _, _, _, _ => Iff.rfl
  | .app C D, n, h, m => by
    have hC := den_congr e C n (fun i hi => h i (by simp only [holes]; omega))
    have hD := den_congr e D (n + C.holes) (fun i hi => by
      have := h (C.holes + i) (by simp only [holes]; omega)
      simpa only [Nat.add_assoc] using this)
    simp only [den, hC, hD]
  | .andSide C _, n, h, m => by
    simp only [den, den_congr e C n (fun i hi => h i (by simpa only [holes] using hi)) m]

/-- **The pattern at a set is the union of its instances at elements of the set**, one element for
each occurrence: `C[S]` holds m exactly where some choice of elements of S, one per occurrence,
gives an instance that holds m. -/
theorem atSet_iff (X : SVar) (e : Valuation M) (A : Set M) : ∀ (C : SvCtx), C.Sides X → ∀ (n : Nat) (m : M),
    (C.atSet X).interpret I (svarAt_svin e X A) m ↔
      ∃ a : Nat → M, (∀ i, i < C.holes → A (a (n + i))) ∧ C.den I e a n m
  | .hole, _, n, m => by
    have hX : (Pattern.svar X : P).interpret I (svarAt_svin e X A) m ↔ A m := by
      show Function.update e.evalSvar X A X m ↔ A m
      simp
    show (Pattern.svar X : P).interpret I (svarAt_svin e X A) m ↔ _
    rw [hX]
    constructor
    · intro h
      exact ⟨fun _ => m, fun _ _ => h, rfl⟩
    · rintro ⟨a, ha, hm⟩
      have := ha 0 (by simp [holes])
      simp only [Nat.add_zero] at this
      rw [show m = a n from hm]; exact this
  | .side ψ, h, n, m => by
    show ψ.interpret I (svarAt_svin e X A) m ↔ _
    rw [interp_svarAt_svin h m]
    exact ⟨fun hm => ⟨fun _ => m, fun i hi => absurd hi (by simp [holes]), hm⟩, fun ⟨_, _, hm⟩ => hm⟩
  | .app C D, h, n, m => by
    show (C.atSet X ⬝ D.atSet X).interpret I (svarAt_svin e X A) m ↔ _
    rw [interp_app]
    constructor
    · rintro ⟨p, b, hp, hb, hpb⟩
      obtain ⟨a₁, ha₁, hC⟩ := (atSet_iff X e A C h.1 n p).mp hp
      obtain ⟨a₂, ha₂, hD⟩ := (atSet_iff X e A D h.2 (n + C.holes) b).mp hb
      refine ⟨fun k => if k < n + C.holes then a₁ k else a₂ k, ?_, p, b, ?_, ?_, hpb⟩
      · intro i hi
        simp only [holes] at hi
        by_cases hlt : n + i < n + C.holes
        · simp only [hlt, ite_true]; exact ha₁ i (by omega)
        · simp only [hlt, ite_false]
          have := ha₂ (i - C.holes) (by omega)
          rwa [show n + C.holes + (i - C.holes) = n + i by omega] at this
      · refine (den_congr e C n (fun i hi => ?_) p).mp hC
        simp only [show n + i < n + C.holes by omega, ite_true]
      · refine (den_congr e D (n + C.holes) (fun i _ => ?_) b).mp hD
        simp only [show ¬ n + C.holes + i < n + C.holes by omega, ite_false]
    · rintro ⟨a, ha, p, b, hC, hD, hpb⟩
      refine ⟨p, b, (atSet_iff X e A C h.1 n p).mpr ⟨a, fun i hi => ha i (by simp only [holes]; omega), hC⟩,
        (atSet_iff X e A D h.2 (n + C.holes) b).mpr ⟨a, fun i hi => ?_, hD⟩, hpb⟩
      have := ha (C.holes + i) (by simp only [holes]; omega)
      simpa only [Nat.add_assoc] using this
  | .andSide C ψ, h, n, m => by
    show (sAnd (C.atSet X) ψ).interpret I (svarAt_svin e X A) m ↔ _
    rw [interp_sAnd, interp_svarAt_svin h.2 m, atSet_iff X e A C h.1 n m]
    constructor
    · rintro ⟨⟨a, ha, hC⟩, hψ⟩; exact ⟨a, ha, hC, hψ⟩
    · rintro ⟨a, ha, hC, hψ⟩; exact ⟨⟨a, ha, hC⟩, hψ⟩

/-- No side pattern is read differently by the two valuations. -/
def SidesAgree (I : Interpretation KoreAML.Sym M) (e e' : Valuation M) : SvCtx → Prop
  | .hole => True
  | .side ψ => ∀ m, ψ.interpret I e' m ↔ ψ.interpret I e m
  | .app C D => C.SidesAgree I e e' ∧ D.SidesAgree I e e'
  | .andSide C ψ => C.SidesAgree I e e' ∧ ∀ m, ψ.interpret I e' m ↔ ψ.interpret I e m

/-- **The instance at elements is the pattern with one element variable per occurrence**, under a
valuation that gives the variable of the occurrence k the element `a k` and reads the side
patterns as e does. -/
theorem atVars_iff (xs : Nat → EVar) (e e' : Valuation M) (a : Nat → M) : ∀ (C : SvCtx) (n : Nat),
    C.SidesAgree I e e' → (∀ i, i < C.holes → e'.evalEvar (xs (n + i)) = a (n + i)) → ∀ m,
    (C.atVars xs n).interpret I e' m ↔ C.den I e a n m
  | .hole, n, _, h, m => by
    have := h 0 (by simp [holes])
    simp only [Nat.add_zero] at this
    show (Pattern.evar (xs n) : P).interpret I e' m ↔ m = a n
    rw [interp_evar, this]
  | .side _, _, h, _, m => h m
  | .app C D, n, h, hx, m => by
    show (C.atVars xs n ⬝ D.atVars xs (n + C.holes)).interpret I e' m ↔ _
    have hC := atVars_iff xs e e' a C n h.1 (fun i hi => hx i (by simp only [holes]; omega))
    have hD := atVars_iff xs e e' a D (n + C.holes) h.2 (fun i hi => by
      have := hx (C.holes + i) (by simp only [holes]; omega)
      simpa only [Nat.add_assoc] using this)
    simp only [interp_app, hC, hD, den]
  | .andSide C ψ, n, h, hx, m => by
    show (sAnd (C.atVars xs n) ψ).interpret I e' m ↔ _
    rw [interp_sAnd, atVars_iff xs e e' a C n h.1 (fun i hi => hx i (by simpa only [holes] using hi)) m, h.2 m]
    rfl

end SvCtx

/-- **A rewrite sentence over a set variable under applications only is its instances at
singletons of matches.** At a point m: the sentence `L[S] → •R[S]` holds at every set S inside U
(the variable's sort) exactly if, for every choice ā of elements of U, one per left occurrence,
with m in `L[ā]`, m has a successor (`sNext`) in `R[{ā}]`: an element of some `R[z̄]`, each `zⱼ`
(one per right occurrence) one of the ā. -/
theorem setvar_rewrite_singleton (X : SVar) (L R : SvCtx) (hL : L.Sides X) (hR : R.Sides X)
    (e : Valuation M) (U : Set M) (m : M) :
    (∀ A : Set M, (∀ x, A x → U x) →
        (L.atSet X).interpret I (svarAt_svin e X A) m →
        (sNext (R.atSet X)).interpret I (svarAt_svin e X A) m) ↔
      (∀ a : Nat → M, (∀ i, i < L.holes → U (a i)) → L.den I e a 0 m →
        ∃ nx b, I.evalSymb .next nx ∧
          (∃ z : Nat → M, (∀ j, j < R.holes → ∃ i, i < L.holes ∧ z j = a i) ∧ R.den I e z 0 b) ∧
          I.evalApp nx b m) := by
  constructor
  · intro h a ha hLa
    have hA : ∀ x, (fun x => ∃ i, i < L.holes ∧ x = a i : Set M) x → U x := by
      rintro x ⟨i, hi, rfl⟩; exact ha i hi
    have hs := h (fun x => ∃ i, i < L.holes ∧ x = a i) hA
      ((SvCtx.atSet_iff X e _ L hL 0 m).mpr ⟨a, fun i hi => ⟨i, hi, by rw [Nat.zero_add]⟩, hLa⟩)
    unfold sNext at hs
    obtain ⟨nx, b, hnx, hb, happ⟩ := interp_app.mp hs
    obtain ⟨z, hz, hRz⟩ := (SvCtx.atSet_iff X e _ R hR 0 b).mp hb
    refine ⟨nx, b, interp_sym.mp hnx, ⟨z, fun j hj => ?_, hRz⟩, happ⟩
    have := hz j hj
    rwa [Nat.zero_add] at this
  · intro h A hA hLA
    obtain ⟨a, ha, hLa⟩ := (SvCtx.atSet_iff X e A L hL 0 m).mp hLA
    have ha' : ∀ i, i < L.holes → A (a i) := fun i hi => by
      have := ha i hi; rwa [Nat.zero_add] at this
    obtain ⟨nx, b, hnx, ⟨z, hz, hRz⟩, happ⟩ := h a (fun i hi => hA _ (ha' i hi)) hLa
    unfold sNext
    refine interp_app.mpr ⟨nx, b, interp_sym.mpr hnx, (SvCtx.atSet_iff X e A R hR 0 b).mpr ⟨z, fun j hj => ?_, hRz⟩, happ⟩
    obtain ⟨i, hi, hzj⟩ := hz j hj
    rw [Nat.zero_add, hzj]; exact ha' i hi

end KCore
