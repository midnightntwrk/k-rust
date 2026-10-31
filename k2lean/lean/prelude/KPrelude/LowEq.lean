import KPrelude.InvColl

/-! Agreement of two maps at the keys an observer sees: the part of low equivalence that is the
same for every language (`k2lean noninterference --good`, `docs/design.md` §3.7). Two stores are
low-equivalent when both are stores (the semantics' fact, a K function) and they agree at every
low key (`AgreeOn`): the keys `ι x` of the `x` that `Low` holds of (the checker's fact, its level
function). A lookup is compared as an `Option`, so a low key is bound in both stores to one value,
or in neither. A step confined to high keys changes a store only at keys that are not low
(`AgreeOn.update_high`), and both runs of one assignment at a low key keep the agreement
(`AgreeOn.update`). Not in the `KPrelude` root: the generated `Spec.lean` of a noninterference
demo imports it. -/

namespace KPrelude.MapHook

open ListIso

variable {M K V X : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V]

/-- `E₁` and `E₂` agree at the key `ι x` of every `x` that `Low` holds of. -/
def AgreeOn (Low : X → Prop) (ι : X → K) (E₁ E₂ : M) : Prop :=
  ∀ x, Low x → lookup E₁ (ι x) = lookup E₂ (ι x)

variable {Low : X → Prop} {ι : X → K} {E E₁ E₂ E₃ : M}

theorem AgreeOn.refl : AgreeOn Low ι E E := fun _ _ => rfl

theorem AgreeOn.symm (h : AgreeOn Low ι E₁ E₂) : AgreeOn Low ι E₂ E₁ := fun x hx => (h x hx).symm

theorem AgreeOn.trans (h₁ : AgreeOn Low ι E₁ E₂) (h₂ : AgreeOn Low ι E₂ E₃) : AgreeOn Low ι E₁ E₃ :=
  fun x hx => (h₁ x hx).trans (h₂ x hx)

variable [Std.TransOrd K] [Std.LawfulEqOrd K]

/-- Both maps updated at one key with one value. -/
theorem AgreeOn.update (hι : Function.Injective ι) (h : AgreeOn Low ι E₁ E₂) (x : X) (v : V) :
    AgreeOn Low ι (MapHook.update E₁ (ι x) v) (MapHook.update E₂ (ι x) v) := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx; rw [lookup_update_self, lookup_update_self]
  · have hne : ι y ≠ ι x := fun e => hyx (hι e)
    rw [lookup_update_ne _ _ hne, lookup_update_ne _ _ hne]
    exact h y hy

/-- A map updated at a key that is not low. -/
theorem AgreeOn.update_high (hι : Function.Injective ι) {x : X} (hx : ¬ Low x) (v : V) :
    AgreeOn Low ι E (MapHook.update E (ι x) v) := by
  intro y hy
  have hne : ι y ≠ ι x := fun e => hx (hι e ▸ hy)
  rw [lookup_update_ne _ _ hne]

end KPrelude.MapHook
