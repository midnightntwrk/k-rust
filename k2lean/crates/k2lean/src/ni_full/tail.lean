/-! ## The relation -/

variable (G : Lab)

/-- Two runs whose disclosed values differ at a common position. -/
def Div (c₁ c₂ : @TOP@) : Prop :=
  ∃ (i : Nat) (a b : @KIT@), (ListIso.toList (discOf c₁))[i]? = some a ∧ (ListIso.toList (discOf c₂))[i]? = some b ∧ a ≠ b

/-- What two related configurations share: low-equal stores, the observation, the disclosed values. -/
def Same (c₁ c₂ : @TOP@) : Prop :=
  @LOWEQ@ (storeOf c₁) (storeOf c₂) ∧ pubOf c₁ = pubOf c₂ ∧ discOf c₁ = discOf c₂

/-- Confined stacks over a common continuation. -/
def Conf (c₁ c₂ : @TOP@) : Prop :=
  ∃ K b₀, Over G K b₀ ∧ CK G K b₀ false (kOf c₁) ∧ CK G K b₀ false (kOf c₂) ∧ Same G c₁ c₂

/-- Both runs about to disclose a value, the two values possibly different. -/
def Pend (c₁ c₂ : @TOP@) : Prop :=
  ∃ K e₁ e₂, lk G true K = true ∧ isRes (@NA@.inj_@HS@_KItem e₁) = true ∧
    isRes (@NA@.inj_@HS@_KItem e₂) = true ∧
    kOf c₁ = .kseq (@DITEM@ (@DOWN@ e₁)) K ∧
    kOf c₂ = .kseq (@DITEM@ (@DOWN@ e₂)) K ∧
    Same G c₁ c₂

def Rel (c₁ c₂ : @TOP@) : Prop := Div c₁ c₂ ∨ Conf G c₁ c₂ ∨ Pend G c₁ c₂

/-- The left run steps alone: the runs have diverged, or it is inside its confined part. -/
def Left (c₁ c₂ : @TOP@) : Prop :=
  Div c₁ c₂ ∨ ∃ K b₀, Over G K b₀ ∧ CK G K b₀ false (kOf c₁) ∧ ¬ AtBase K b₀ (kOf c₁) ∧
    CK G K b₀ false (kOf c₂) ∧ Same G c₁ c₂

/-- The right run steps alone: the runs have diverged, or the left one has reached the continuation
and the right one has not. -/
def Right (c₁ c₂ : @TOP@) : Prop :=
  Div c₁ c₂ ∨ ∃ K b₀, Over G K b₀ ∧ AtBase K b₀ (kOf c₁) ∧ CK G K b₀ false (kOf c₂) ∧
    ¬ AtBase K b₀ (kOf c₂) ∧ Same G c₁ c₂

/-- Both runs step: at the same low stack, at a value each on the disclosure's freezer, or at the
disclosure of a value each. -/
def SyncR (c₁ c₂ : @TOP@) : Prop :=
  Sync G c₁ c₂ ∨
  (∃ K v₁ v₂, lk G true K = true ∧ isRes v₁ = true ∧ isRes v₂ = true ∧
    kOf c₁ = .kseq v₁ (.kseq frzD K) ∧ kOf c₂ = .kseq v₂ (.kseq frzD K) ∧ Same G c₁ c₂) ∨
  Pend G c₁ c₂

variable {G}

theorem prefix_getElem? {α : Type} {l l' : List α} (h : l <+: l') {i : Nat} {a : α}
    (hi : l[i]? = some a) : l'[i]? = some a := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hi).1]
  exact hi

theorem div_left {c₁ c₁' c₂ : @TOP@} (h : Div c₁ c₂) (ha : AppendQ c₁ c₁') : Div c₁' c₂ :=
  let ⟨i, a, b, h₁, h₂, hne⟩ := h
  ⟨i, a, b, prefix_getElem? ha h₁, h₂, hne⟩

theorem div_right {c₁ c₂ c₂' : @TOP@} (h : Div c₁ c₂) (ha : AppendQ c₂ c₂') : Div c₁ c₂' :=
  let ⟨i, a, b, h₁, h₂, hne⟩ := h
  ⟨i, a, b, h₁, prefix_getElem? ha h₂, hne⟩

theorem toList_inj {a b : @NA@.SortList} (h : ListIso.toList a = ListIso.toList b) : a = b := by
  have := congrArg (ListIso.ofList (M := @NA@.SortList)) h
  simpa [ListIso.ofList_toList] using this

theorem atBase_true {K k : @K@} (h : AtBase K true k) :
    ∃ v, isRes v = true ∧ k = .kseq v K := by
  k2l_cases k <;> simp_all

theorem ck_of_atBase {K k : @K@} {b₀ : Bool} (h : AtBase K b₀ k) : CK G K b₀ false k := by
  cases b₀
  · simp only [AtBase_false] at h; rw [h]; exact CK_base G K false
  · obtain ⟨v, hv, rfl⟩ := atBase_true h
    rw [CK_kseq, citem_false, citem0_of_res G hv]
    exact Or.inr (CK_base G K true)

theorem ne_dotk_of_notAtBase {K k : @K@} {b₀ : Bool} (h : CK G K b₀ false k)
    (hn : ¬ AtBase K b₀ k) : k ≠ .dotk := by
  rintro rfl
  rw [CK_dotk] at h
  obtain ⟨hb, hK⟩ := h
  subst hb
  exact hn (by simp [hK])

theorem lk_frzD (K : @K@) : lk G true (.kseq frzD K) = lk G true K := by
  simp [lk_kseq, plug, dflt, @LKFRZ@]

theorem inj_@HS@_KItem_inj {e₁ e₂ : @HOLE@}
    (h : @NA@.inj_@HS@_KItem e₁ = @NA@.inj_@HS@_KItem e₂) : e₁ = e₂ := by
  have := congrArg @NA@.proj_KItem_@HS@ h
  simpa using this

theorem sync_all {c₁ c₁' : @TOP@} (h : @NA@.Step c₁ c₁') :
    ∀ c₂ c₂', SyncR G c₁ c₂ → @NA@.Step c₂ c₂' → Rel G c₁' c₂' := by
  intro c₂ c₂' hs h₂
  rcases hs with hs | ⟨K, v₁, v₂, hlk, hv₁, hv₂, hk₁, hk₂, hlow, hpub, hdisc⟩ |
      ⟨K, e₁, e₂, hlk, he₁, he₂, hk₁, hk₂, hlow, hpub, hdisc⟩
  · obtain ⟨hk, hlow, hpub, hdisc⟩ := same_step G h c₂ c₂' hs h₂
    obtain ⟨K, b₀, hck, hover⟩ := sq_step G h hs.2.1 hs.2.2.1.1
    exact Or.inr (Or.inl ⟨K, b₀, hover, hck, hk ▸ hck, hlow, hpub, hdisc⟩)
  · obtain ⟨⟨e₁, he₁, hk₁'⟩, hs₁, hp₁, hd₁⟩ := cool_step h v₁ K hv₁ hk₁
    obtain ⟨⟨e₂, he₂, hk₂'⟩, hs₂, hp₂, hd₂⟩ := cool_step h₂ v₂ K hv₂ hk₂
    subst he₁ he₂
    exact Or.inr (Or.inr ⟨K, e₁, e₂, hlk, hv₁, hv₂, hk₁', hk₂',
      by rw [hs₁, hs₂]; exact hlow, by rw [hp₁, hp₂]; exact hpub, by rw [hd₁, hd₂]; exact hdisc⟩)
  · obtain ⟨hk₁', hs₁, hp₁, hd₁⟩ := disc_step h e₁ K he₁ hk₁
    obtain ⟨hk₂', hs₂, hp₂, hd₂⟩ := disc_step h₂ e₂ K he₂ hk₂
    by_cases he : e₁ = e₂
    · subst he
      refine Or.inr (Or.inl ⟨_, false, ⟨?_, by simp⟩, by rw [hk₁']; exact CK_base G _ false,
        by rw [hk₂']; exact CK_base G _ false, by rw [hs₁, hs₂]; exact hlow,
        by rw [hp₁, hp₂]; exact hpub, toList_inj (by rw [hd₁, hd₂, hdisc])⟩)
      simp [lk_kseq, litem_false, litem0_of_res G he₁, hlk]
    · refine Or.inl ⟨(ListIso.toList (discOf c₁)).length, _, _, ?_, ?_,
        fun h => he (inj_@HS@_KItem_inj h)⟩
      · simp [hd₁]
      · simp [hd₂, ← hdisc]

theorem left_all {c₁ c₁' : @TOP@} (h : @NA@.Step c₁ c₁') :
    ∀ c₂, Left G c₁ c₂ → Rel G c₁' c₂ := by
  rintro c₂ (hd | ⟨K, b₀, hover, hc₁, hne, hc₂, hlow, hpub, hdisc⟩)
  · exact Or.inl (div_left hd (append_step h))
  · obtain ⟨hc₁', hhi, hp, hd⟩ := cq_step G h K b₀ hc₁ hne hlow.1
    exact Or.inr (Or.inl ⟨K, b₀, hover, hc₁', hc₂, lowEq_hiOnly hlow hhi, hp.trans hpub,
      hd.trans hdisc⟩)

theorem right_all {c₂ c₂' : @TOP@} (h : @NA@.Step c₂ c₂') :
    ∀ c₁, Right G c₁ c₂ → Rel G c₁ c₂' := by
  rintro c₁ (hd | ⟨K, b₀, hover, hc₁, hc₂, hne, hlow, hpub, hdisc⟩)
  · exact Or.inl (div_right hd (append_step h))
  · obtain ⟨hc₂', hhi, hp, hd⟩ := cq_step G h K b₀ hc₂ hne hlow.2.1
    exact Or.inr (Or.inl ⟨K, b₀, hover, ck_of_atBase hc₁, hc₂',
      lowEq_symm (lowEq_hiOnly (lowEq_symm hlow) hhi), hpub.trans hp.symm, hdisc.trans hd.symm⟩)

