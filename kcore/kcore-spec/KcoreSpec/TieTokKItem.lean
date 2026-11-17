/-
  A no-junk sentence that leaves out an injection (`Parse.ReadingNote.tokKItem`): where the sort the
  injection comes from has a value, the sentence has no model with `Γ`, for every interpretation of
  the parameters.
-/
import KcoreSpec.Confined
import KcoreSpec.HypWf
import KcoreSpec.FnObligations

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace Faithful

/-- **A no-junk sentence without an injection is refuted, for every interpretation.** Let N be a
constructor sort, `inj{a, N}` one of its generators that is not open, w a value of the sort a, and
`gs` generators of N each an injection `inj{b, N}` that is not open, from a sort b other than a,
incomparable with a and with no lower bound in common with it. Then no model of `Γ (c.withHooks H)`
satisfies the no-junk sentence of N over `gs`: `inj{a, N}(w)` is an element of N; the sentence
says it is one that some `inj{b, N}` builds from an element of b, which `inj{b, N}` builds alone
(Cons-Fun), so the two injections build one element, which their Cons-Dist item denies. -/
theorem noJunk_omitted_refuted {c : Semantics} (hcore : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    (H : HookParams) {N a : Srt} (hN : N ∈ consSorts c) (hno : c.fnOvlSyms = [])
    (ha : Gen.inj a ∈ (c.gens N).filter (!c.isOpenGen ·)) {w : GroundTerm} (hw : c.sortOf w = some a)
    (hv : c.sortOf (.inj a N w) = some N) {gs : List Gen}
    (hgs : ∀ g ∈ gs, ∃ b, g = .inj b ∧ Gen.inj b ∈ (c.gens N).filter (!c.isOpenGen ·) ∧ b ≠ a ∧
      (c.le a b || c.le b a) = false ∧ c.lowerBounds a b = [] ∧ c.lowerBounds b a = [])
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (c.withHooks H)) :
    ¬ (I ⊧ᴵ (KoreAML.Cons.noJunkItem (c.sortName N) (gs.map (Gen.toK c))).pat) := by
  intro hax
  haveI : OvlOK (c.withHooks H) := ovlOK_of_core ((Semantics.coreOK_withHooks c H).trans hcore)
  have hD := defOK hI
  have hw' : (c.withHooks H).sortOf w = some a := by rw [Semantics.sortOf_withHooks _ _ hr]; exact hw
  have hv' : (c.withHooks H).sortOf (.inj a N w) = some N := by rw [Semantics.sortOf_withHooks _ _ hr]; exact hv
  have hx : InS I (c.sortName N) (elemOf (c.withHooks H) I (.inj a N w)) :=
    (inS_iff _).mp (elemOf_spec hI hv' KoreAML.val0).2
  have hxw : InS I (c.sortName a) (elemOf (c.withHooks H) I w) :=
    (inS_iff _).mp (elemOf_spec hI hw' KoreAML.val0).2
  obtain ⟨g, hg, ys, hys, hgs'⟩ := noJunk_elim hD hax hx
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  obtain ⟨b, rfl, hbmem, hba, hle, hlb1, hlb2⟩ := hgs g0 hg0
  obtain ⟨y, hy, rfl⟩ : ∃ y, InS I (c.sortName b) y ∧ ys = [y] := by
    cases hys with
    | cons hy hr => cases hr; exact ⟨_, hy, rfl⟩
  have hN' : N ∈ consSorts (c.withHooks H) := hN
  have hno' : (c.withHooks H).fnOvlSyms = [] := hno
  have hbmem' : Gen.inj b ∈ ((c.withHooks H).gens N).filter (!(c.withHooks H).isOpenGen ·) := hbmem
  have hamem' : Gen.inj a ∈ ((c.withHooks H).gens N).filter (!(c.withHooks H).isOpenGen ·) := ha
  obtain ⟨y1, -, hy1⟩ := fun_at hD (sat_cons hI (Or.inl ⟨_, funItem_mem hno' hN' hbmem', rfl⟩)) (xs := [y]) rfl
    (single_sorts hy)
  have hy1 : ∀ m, GS I (c.sortName N) (Gen.toK c (.inj b)) [y] m ↔ m = y1 := hy1
  have hset_b : ∀ m, GS I (c.sortName N) (Gen.toK c (.inj b)) [y] m ↔
      m = elemOf (c.withHooks H) I (.inj a N w) := fun m => by
    rw [hy1 m, ← (hy1 _).mp hgs']
  have hset_a : ∀ m, GS I (c.sortName N) (Gen.toK c (.inj a)) [elemOf (c.withHooks H) I w] m ↔
      m = elemOf (c.withHooks H) I (.inj a N w) := fun m => by
    rw [← (elemOf_spec hI hv' KoreAML.val0).1 m]
    exact (den_inj_gs hI hw' KoreAML.val0 m).symm
  have hseq : ∀ m, GS I (c.sortName N) (Gen.toK c (.inj a)) [elemOf (c.withHooks H) I w] m ↔
      GS I (c.sortName N) (Gen.toK c (.inj b)) [y] m := fun m => by rw [hset_a, hset_b]
  have hne : Gen.inj a ≠ Gen.inj b := fun h => hba (by cases h; rfl)
  rcases mem_pairs_of hne hamem' hbmem' with hp | hp
  · rcases injPair_mem hno' hN' hp hle with ⟨-, hit⟩ | ⟨hl, -⟩
    · exact dist_at hD (sat_cons hI (Or.inl ⟨_, hit, rfl⟩)) (xs := [_]) (ys := [y]) rfl rfl
        (single_sorts hxw) (single_sorts hy) hseq
    · exact hl hlb1
  · rcases injPair_mem hno' hN' hp (by rw [Bool.or_comm]; exact hle) with ⟨-, hit⟩ | ⟨hl, -⟩
    · exact dist_at hD (sat_cons hI (Or.inl ⟨_, hit, rfl⟩)) (xs := [y]) (ys := [_]) rfl rfl
        (single_sorts hy) (single_sorts hxw) (fun m => (hseq m).symm)
    · exact hl hlb2

end Faithful

end KCore
