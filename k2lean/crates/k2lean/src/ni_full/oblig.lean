theorem obligations : Obligations G (Rel G) (SyncR G) (Left G) (Right G) where
  init P@BINDERS@ hP := by
    refine Or.inr (Or.inl ⟨_, false, ⟨?_, by simp⟩, CK_base G _ false, CK_base G _ false,
      lowEq_refl (good_init P@ARGS1@), rfl, rfl⟩)
    simp only [@NA@.init, kOf, lk_kseq, litem_false, litem0_inj_@SS@]
    simp [show @SEC@ G P = some true from hP]
  final := by
    rintro f₁ f₂ (⟨i, a, b, h₁, h₂, hne⟩ | ⟨K, b₀, _, _, _, hlow, hpub, _⟩ |
      ⟨K, e₁, e₂, _, _, _, hk₁, _, _⟩) hf₁ hf₂ hd
    · rw [hd, h₂] at h₁; cases h₁; exact absurd rfl hne
    · exact @FINAL@
    · simp [Final, hk₁] at hf₁
  cover := by
    rintro c₁ c₂ (hd | ⟨K, b₀, hover, hc₁, hc₂, hsame⟩ | hp) hnf
    · by_cases h₁ : Final c₁
      · exact Or.inr (Or.inl ⟨Or.inl hd, fun h₂ => hnf ⟨h₁, h₂⟩⟩)
      · exact Or.inl ⟨Or.inl hd, h₁⟩
    · by_cases a₁ : AtBase K b₀ (kOf c₁)
      · by_cases a₂ : AtBase K b₀ (kOf c₂)
        · cases b₀
          · simp only [AtBase_false] at a₁ a₂
            refine Or.inr (Or.inr ⟨Or.inl ⟨a₁.trans a₂.symm, by rw [a₁]; exact hover.1, hsame⟩,
              fun hf => hnf ⟨hf, ?_⟩, fun hf => hnf ⟨?_, hf⟩⟩)
            · simp only [Final] at hf ⊢; rw [a₂, ← a₁, hf]
            · simp only [Final] at hf ⊢; rw [a₁, ← a₂, hf]
          · obtain ⟨K', rfl⟩ := hover.2 rfl
            obtain ⟨v₁, hv₁, hk₁⟩ := atBase_true a₁
            obtain ⟨v₂, hv₂, hk₂⟩ := atBase_true a₂
            refine Or.inr (Or.inr ⟨Or.inr (Or.inl ⟨K', v₁, v₂, ?_, hv₁, hv₂, hk₁, hk₂, hsame⟩),
              by simp [Final, hk₁], by simp [Final, hk₂]⟩)
            rw [← lk_frzD]; exact hover.1
        · exact Or.inr (Or.inl ⟨Or.inr ⟨K, b₀, hover, a₁, hc₂, a₂, hsame⟩, ne_dotk_of_notAtBase hc₂ a₂⟩)
      · exact Or.inl ⟨Or.inr ⟨K, b₀, hover, hc₁, a₁, hc₂, hsame⟩, ne_dotk_of_notAtBase hc₁ a₁⟩
    · obtain ⟨K, e₁, e₂, _, _, _, hk₁, hk₂, _⟩ := id hp
      exact Or.inr (Or.inr ⟨Or.inr (Or.inr hp), by simp [Final, hk₁], by simp [Final, hk₂]⟩)
