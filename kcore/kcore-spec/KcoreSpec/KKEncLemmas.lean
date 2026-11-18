import KcoreSpec.KKEncDef

/-!
# What `encDef` writes

The ensures of an encoded clause or rule is its ensures, encoded: `encTerm` writes `en` at the top
of no term, so `Cl.ens` and `Rl.ens` find exactly the `en` that `encRhs` writes for an ensures.
-/

set_option autoImplicit false

namespace KCore.KK
/-- `encTerm` writes no `en` at the top of a term. -/
theorem encTermWith_ne_en (d : Semantics) (lit : Srt → Lit → Option T)
    (hlit : ∀ s l a b, lit s l ≠ some (.en a b)) (t : Term) (a b : T) :
    encTermWith d lit t ≠ some (.en a b) := by
  cases t with
  | var i => simp [encTermWith]
  | dv s l => simpa [encTermWith] using hlit s l a b
  | inj x y t => simp only [encTermWith]; cases encTermWith d lit t <;> simp
  | as t i => simp only [encTermWith]; cases encTermWith d lit t <;> simp
  | app f ts =>
    simp only [encTermWith, readApp]
    split
    · cases encTermsWith d lit ts <;> simp
    · split
      · cases (collSymOf d f).bind _ <;> simp
      · split
        · split
          · cases encTermsWith d lit ts <;> simp
          · cases encTermsWith d lit ts <;> simp [derivedHook] <;> split <;> simp
        · split
          · simp
          · split
            · cases encTermsWith d lit ts <;> simp
            · simp

theorem encLit_ne_en (s : Srt) (l : Lit) (a b : T) : encLit s l ≠ some (.en a b) := by
  unfold encLit encLitWith; split <;> simp

theorem encT_ne_en (d : Semantics) (t : Term) (a b : T) : encT d t ≠ .en a b := by
  unfold encT encTerm
  cases h : encTermWith d encLit t with
  | none => simp
  | some p => simp only [Option.getD_some]; rintro rfl; exact encTermWith_ne_en d encLit encLit_ne_en t a b h

/-- The ensures of an encoded clause is its ensures, encoded. -/
theorem encCl_ens (d : Semantics) (cl : Clause) : (encCl d cl).ens = cl.ens.map (encT d) := by
  unfold encCl encRhs
  cases h : cl.ens with
  | some e => rfl
  | none =>
    simp only [Option.map_none]
    unfold Cl.ens
    split
    · rename_i r e' heq; simp at heq; exact absurd heq.2.2.2.2 (encT_ne_en d cl.rhs r e')
    · rfl

theorem encRl_ens (d : Semantics) (r : Rule) : (encRl d r).ens = r.ens.map (encT d) := by
  unfold encRl encRhs
  cases h : r.ens with
  | some e => rfl
  | none =>
    simp only [Option.map_none]
    unfold Rl.ens
    split
    · rename_i x e' heq; simp at heq; exact absurd heq.2.2.2.2 (encT_ne_en d r.rhs x e')
    · rfl

end KCore.KK
