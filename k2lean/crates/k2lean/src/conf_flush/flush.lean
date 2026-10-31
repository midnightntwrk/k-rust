/-! ## Confluence up to the flush of the ranks before @R@

A rule of rank @R@ may enable the rules of the ranks before it (K's stream rules, after a `print`),
which step the shared cells alone; until they are done no rule of rank @R@ applies (`Calm`). Two
steps of rank @R@ then join only after the flush, so the steps are compressed (`KPrelude.FStep`): a
step from a calm configuration, then the flush to where it stops. The flush may stop where nothing
steps (an I/O hook the library leaves undefined), and two runs then end apart with one observation:
the theorem is the observation's (`obs_unique_of`, modulo `KPrelude.ObsEq`). -/

/-- No rule of a rank before @R@ applies. -/
def Calm (c : @TOP@) : Prop := ∀ j, j < @R@ → ¬ @NA@.App j c

@PREUNAPPLY@

/-- A step of the shared cells after a step of the thread map comes before it. -/
theorem sstep_back {a₁ b₁ ch₁ ch₂} {c c₁ c₁₂ : @TOP@}
    (h₁ : MStep a₁ b₁ ch₁ c c₁) (h₂ : SStep ch₂ c₁ c₁₂) (hc : ch₁.Compat ch₂)@HN_BIND@ :
    ∃ c₂, SStep ch₂ c c₂ ∧ MStep a₁ b₁ ch₁ c₂ c₁₂ := by
  obtain ⟨m, R₁, r₁, s, rfl, hm₁, hr₁, hp₁, rfl⟩ := h₁
  obtain ⟨tc₂, s₂, he, hp₂, rfl⟩ := h₂
  obtain ⟨rfl, rfl⟩ := mkc_inj he
  have hp₂' := Change.pre_unapply hc hp₁ hp₂@HN_ARG@
  refine ⟨mk m (ch₂.apply s), ⟨_, _, rfl, hp₂', rfl⟩,
    ⟨_, _, _, _, rfl, hm₁, hr₁, Change.pre_apply hc.symm hp₂' hp₁, ?_⟩⟩
  rw [Change.apply_comm hc hp₁ hp₂']

/-- A step of the shared cells after another comes before it. -/
theorem sstep_back_s {ch₁ ch₂} {c c₁ c₁₂ : @TOP@}
    (h₁ : SStep ch₁ c c₁) (h₂ : SStep ch₂ c₁ c₁₂) (hc : ch₁.Compat ch₂)@HN_BIND@ :
    ∃ c₂, SStep ch₂ c c₂ ∧ SStep ch₁ c₂ c₁₂ := by
  obtain ⟨tc, s, rfl, hp₁, rfl⟩ := h₁
  obtain ⟨tc₂, s₂, he, hp₂, rfl⟩ := h₂
  obtain ⟨rfl, rfl⟩ := mkc_inj he
  have hp₂' := Change.pre_unapply hc hp₁ hp₂@HN_ARG@
  refine ⟨mkc tc (ch₂.apply s), ⟨_, _, rfl, hp₂', rfl⟩,
    ⟨_, _, rfl, Change.pre_apply hc.symm hp₂' hp₁, ?_⟩⟩
  rw [Change.apply_comm hc hp₁ hp₂']

theorem calm_iff {a b ch cl} (hs : safe cl @R@ = true) (hi : InClass cl ch) {y y' : @TOP@}
    (h : MStep a b ch y y') : Calm y ↔ Calm y' :=
  ⟨fun hc j hj ha => hc j hj (app_back j cl (safe_spec hs hj) hi h ha),
   fun hc j hj ha => hc j hj (app_fwd j cl (safe_spec hs hj) hi h ha)⟩

theorem calm_iff_s {ch cl} (hs : safe cl @R@ = true) (hi : InClass cl ch) {y y' : @TOP@}
    (h : SStep ch y y') : Calm y ↔ Calm y' :=
  ⟨fun hc j hj ha => hc j hj (app_back_s j cl (safe_spec hs hj) hi h ha),
   fun hc j hj ha => hc j hj (app_fwd_s j cl (safe_spec hs hj) hi h ha)⟩

/-- The rules of the ranks before @R@ step the shared cells, compatibly with every class that leaves
alone what they read. -/
theorem high_shared : ∀ r : Rule, r.rank < @R@ → r.kind = .shared := by
  intro r h; cases r <;> simp_all [Rule.rank, Rule.kind]

theorem high_compat : ∀ r : Rule, r.rank < @R@ → ∀ cl, safe cl @R@ = true → compatTbl cl r.cls = true := by
  intro r h cl; cases r <;> simp [Rule.rank] at h <;> cases cl <;> decide
@HIGH_K@
/-- A step of the flush: by a rule of a rank before @R@, a step of the shared cells. -/
theorem flush_view {y z : @TOP@} (f : FlushStep @NA@.Step Calm y z) :
    ∃ (r : Rule) (ch : Change), r.rank < @R@ ∧ @NA@.App r.rank y ∧ (∀ j, j < r.rank → ¬ @NA@.App j y) ∧
      SStep ch y z ∧ LocalS r.rank ch ∧ InClass r.cls ch := by
  obtain ⟨hn, hs⟩ := f
  obtain ⟨r, ar, pr, -, w⟩ := view_of hs
  have hr : r.rank < @R@ := Nat.lt_of_not_le fun hge => hn fun j hj => pr j (by omega)
  unfold VPart at w
  rw [high_shared r hr] at w
  obtain ⟨ch, ss, l, i@SM@⟩ := w
  exact ⟨r, ch, hr, ar, pr, ss, l, i⟩

/-- The flush commutes with a step of the thread map whose class leaves alone what it reads, in
both directions. -/
theorem flush_fw {a b ch cl} (hs : safe cl @R@ = true) (hi : InClass cl ch) {y z y' : @TOP@}
    (f : FlushStep @NA@.Step Calm y z) (h : MStep a b ch y y') :
    ∃ z', FlushStep @NA@.Step Calm y' z' ∧ MStep a b ch z z' := by
  obtain ⟨r, ch₂, hr, ar, pr, ss, l, i₂⟩ := flush_view f
  obtain ⟨c₁₂, x, y2⟩ := mstep_sstep_comm h ss (compat_of _ _ (high_compat r hr cl hs) _ _ hi i₂@KC_HI@)
  refine ⟨c₁₂, ⟨fun hc => hc r.rank hr (app_fwd r.rank cl (safe_spec hs hr) hi h ar), l _ _ x ?_⟩, y2⟩
  intro j hj ha; exact pr j hj (app_back j cl (safe_spec hs (by omega)) hi h ha)

theorem flush_bw {a b ch cl} (hs : safe cl @R@ = true) (hi : InClass cl ch) {y y' z' : @TOP@}
    (f : FlushStep @NA@.Step Calm y' z') (h : MStep a b ch y y') :
    ∃ z, FlushStep @NA@.Step Calm y z ∧ MStep a b ch z z' := by
  obtain ⟨r, ch₂, hr, ar, pr, ss, l, i₂⟩ := flush_view f
  obtain ⟨z, x, y2⟩ := sstep_back h ss (compat_of _ _ (high_compat r hr cl hs) _ _ hi i₂@KC_HI@)@HN_HI@
  refine ⟨z, ⟨fun hc => hc r.rank hr (app_back r.rank cl (safe_spec hs hr) hi h ar), l _ _ x ?_⟩, y2⟩
  intro j hj ha; exact pr j hj (app_fwd j cl (safe_spec hs (by omega)) hi h ha)

/-- The same for a step of the shared cells. -/
theorem flush_fw_s {ch cl} (hs : safe cl @R@ = true) (hi : InClass cl ch) {y z y' : @TOP@}
    (f : FlushStep @NA@.Step Calm y z) (h : SStep ch y y') :
    ∃ z', FlushStep @NA@.Step Calm y' z' ∧ SStep ch z z' := by
  obtain ⟨r, ch₂, hr, ar, pr, ss, l, i₂⟩ := flush_view f
  obtain ⟨c₁₂, x, y2⟩ := sstep_comm h ss (compat_of _ _ (high_compat r hr cl hs) _ _ hi i₂@KC_HI@)
  refine ⟨c₁₂, ⟨fun hc => hc r.rank hr (app_fwd_s r.rank cl (safe_spec hs hr) hi h ar), l _ _ x ?_⟩, y2⟩
  intro j hj ha; exact pr j hj (app_back_s j cl (safe_spec hs (by omega)) hi h ha)

theorem flush_bw_s {ch cl} (hs : safe cl @R@ = true) (hi : InClass cl ch) {y y' z' : @TOP@}
    (f : FlushStep @NA@.Step Calm y' z') (h : SStep ch y y') :
    ∃ z, FlushStep @NA@.Step Calm y z ∧ SStep ch z z' := by
  obtain ⟨r, ch₂, hr, ar, pr, ss, l, i₂⟩ := flush_view f
  obtain ⟨z, x, y2⟩ := sstep_back_s h ss (compat_of _ _ (high_compat r hr cl hs) _ _ hi i₂@KC_HI@)@HN_HI@
  refine ⟨z, ⟨fun hc => hc r.rank hr (app_back_s r.rank cl (safe_spec hs hr) hi h ar), l _ _ x ?_⟩, y2⟩
  intro j hj ha; exact pr j hj (app_fwd_s j cl (safe_spec hs (by omega)) hi h ha)

@OBSFRAME@
/-- A step to `a` and a step of the thread map to `b`, of a class that leaves alone what the flush
reads, of rank @R@: they join compressed, modulo `ObsEq`, when after the second the first is a step
(`hab`) to where the second takes `a` (`ha`). -/
theorem fjoin_m (hdet : ∀ {c a b : @TOP@}, ¬ Calm c → @NA@.Step c a → @NA@.Step c b → a = b)
    {a₂ b₂ ch₂ cl₂} (hs₂ : safe cl₂ @R@ = true) (i₂ : InClass cl₂ ch₂) (l₂ : Local @R@ a₂ b₂ ch₂)
    {c a b c₁₂ n₁ n₂ : @TOP@} (hc : Calm c) (hb : MStep a₂ b₂ ch₂ c b)
    (ha : MStep a₂ b₂ ch₂ a c₁₂) (hab : @NA@.Step b c₁₂)
    (f₁ : FlushNF @NA@.Step Calm a n₁) (f₂ : FlushNF @NA@.Step Calm b n₂) :
    DiamondMod (FStep @NA@.Step Calm) (ObsEq @NA@.Step obs) n₁ n₂ :=
  fdiamond_of_frame (M := MStep a₂ b₂ ch₂) hdet (fun f h => flush_fw hs₂ i₂ f h)
    (fun f h => flush_bw hs₂ i₂ f h) (fun h => calm_iff hs₂ i₂ h)
    (fun h => obs_frame h (none_of_class_@JO@ _ _ (safe_spec hs₂ (by decide)) i₂)) (fun hy h => l₂ _ _ h hy)
    hc hb ha hab f₁ f₂

theorem fjoin_s (hdet : ∀ {c a b : @TOP@}, ¬ Calm c → @NA@.Step c a → @NA@.Step c b → a = b)
    {ch₂ cl₂} (hs₂ : safe cl₂ @R@ = true) (i₂ : InClass cl₂ ch₂) (l₂ : LocalS @R@ ch₂)
    {c a b c₁₂ n₁ n₂ : @TOP@} (hc : Calm c) (hb : SStep ch₂ c b)
    (ha : SStep ch₂ a c₁₂) (hab : @NA@.Step b c₁₂)
    (f₁ : FlushNF @NA@.Step Calm a n₁) (f₂ : FlushNF @NA@.Step Calm b n₂) :
    DiamondMod (FStep @NA@.Step Calm) (ObsEq @NA@.Step obs) n₁ n₂ :=
  fdiamond_of_frame (M := SStep ch₂) hdet (fun f h => flush_fw_s hs₂ i₂ f h)
    (fun f h => flush_bw_s hs₂ i₂ f h) (fun h => calm_iff_s hs₂ i₂ h)
    (fun h => obs_frame_s h (none_of_class_@JO@ _ _ (safe_spec hs₂ (by decide)) i₂)) (fun hy h => l₂ _ _ h hy)
    hc hb ha hab f₁ f₂

/-- Two rules of rank @R@ whose steps join compressed by the generic arguments: the first may enable
the flush, the second's class leaves alone what the flush reads, their classes are compatible, and
they do not both add bindings. -/
def flushOK (r₁ r₂ : Rule) : Bool :=
  r₁.rank == @R@ && r₂.rank == @R@ && !safe r₁.cls @R@ && safe r₂.cls @R@ && compatTbl r₁.cls r₂.cls@FOK_K@ &&
    (match r₁.kind, r₂.kind with
     | .thread, .thread => !(r₁.ins && r₂.ins)
     | .thread, .shared | .shared, .thread | .shared, .shared => true
     | _, _ => false)

/-- The flush is deterministic: two steps by rules of one rank before @R@ from one configuration
reach one configuration. -/
def FlushSlot (r₁ r₂ : Rule) : Prop :=
  ∀ {c c₁ c₂ : @TOP@}, StepBy r₁ c c₁ → StepBy r₂ c c₂ → c₁ = c₂

/-- The determinism of the flush: a slot per ordered pair of rules of one rank before @R@. -/
def FlushDet : Prop :=
  ∀ r₁ r₂, r₁.rank < @R@ → r₁.rank = r₂.rank → FlushSlot r₁ r₂

/-- The flush stops, from every configuration: the slot `flush.ends`. -/
def FlushEnds : Prop := ∀ c, ∃ n, FlushNF @NA@.Step Calm c n

theorem hdet_of (D : FlushDet) {c a b : @TOP@} (hc : ¬ Calm c) (h₁ : @NA@.Step c a)
    (h₂ : @NA@.Step c b) : a = b := by
  obtain ⟨r₁, a₁, p₁, s₁, -⟩ := view_of h₁
  obtain ⟨r₂, a₂, p₂, s₂, -⟩ := view_of h₂
  have hr₁ : r₁.rank < @R@ := Nat.lt_of_not_le fun hge => hc fun j hj => p₁ j (by omega)
  rcases Nat.lt_trichotomy r₁.rank r₂.rank with h | h | h
  · exact absurd a₁ (p₂ _ h)
  · exact D r₁ r₂ hr₁ h s₁ s₂
  · exact absurd a₂ (p₁ _ h)

/-- The join of two steps by `r₁` and `r₂` from one configuration: a slot of `OpenJoins`. -/
def OpenSlot (r₁ r₂ : Rule) : Prop :=
  ∀ {c c₁ c₂ : @TOP@}, StepBy r₁ c c₁ → StepBy r₂ c c₂ →
    DiamondMod @NA@.Step Eq c₁ c₂

/-- The joins the generic arguments leave from a calm configuration (so at rank @R@ and after): the
pairs neither `staticOK` nor `flushOK` decides. -/
def OpenJoins : Prop :=
  ∀ r₁ r₂, staticOK r₁ r₂ = false → flushOK r₁ r₂ = false → flushOK r₂ r₁ = false → @R@ ≤ r₁.rank →
    OpenSlot r₁ r₂

theorem join_flush (hdet : ∀ {c a b : @TOP@}, ¬ Calm c → @NA@.Step c a → @NA@.Step c b → a = b)
    (S : SameThreadJoins) (E : FlushEnds) {r₁ r₂ : Rule} (hf : flushOK r₁ r₂ = true)
    {c c₁ c₂ n₁ n₂ : @TOP@} (hc : Calm c) (v₁ : ViewOf r₁ c c₁) (v₂ : ViewOf r₂ c c₂)
    (f₁ : FlushNF @NA@.Step Calm c₁ n₁) (f₂ : FlushNF @NA@.Step Calm c₂ n₂) :
    DiamondMod (FStep @NA@.Step Calm) (ObsEq @NA@.Step obs) n₁ n₂ := by
  obtain ⟨a₁, p₁, b₁, w₁⟩ := v₁
  obtain ⟨a₂, p₂, b₂, w₂⟩ := v₂
  simp only [flushOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hf
  obtain ⟨@FOK_OPEN@⟨⟨⟨⟨hr₁, hr₂⟩, -⟩, hs₂⟩, hc₁₂⟩@FOK_PAT@, hk⟩ := hf
  have hr : r₁.rank = r₂.rank := hr₁.trans hr₂.symm
  unfold VPart at w₁ w₂
  revert w₁ w₂ hk
  rw [hr₁] at a₁ p₁ ⊢
  rw [hr₂] at a₂ p₂ ⊢
  cases hk₁ : r₁.kind <;> cases hk₂ : r₂.kind <;> intro w₁ w₂ hk <;> simp only [Bool.false_eq_true] at hk
  · obtain ⟨a₁, b₁', bs₁, ch₁, ts₁, d₁, n₁, l₁, i₁, m₁@SM@, at₁⟩ := w₁
    obtain ⟨a₂, b₂', bs₂, ch₂, ts₂, d₂, n₂, l₂, i₂, m₂@SM@, at₂⟩ := w₂
    by_cases hkk : ∃ p ∈ bs₁, ∃ q ∈ bs₂, p.1 = q.1
    · obtain ⟨p, hp, q, hq, e⟩ := hkk
      cases hd : KeyPat.pdisj r₁.pats r₂.pats
      · refine fdiamond_of_diamond (ObsEq.stepEquiv obs) hdet E f₁ f₂ (S r₁ r₂ hk₁ hk₂ hr hd at₁ at₂ (k := p.1) ?_ ?_)
        · rw [(d₁ p.1 p.2).2 hp]; simp
        · rw [e, (d₂ q.1 q.2).2 hq]; simp
      · exact (KeyPat.pdisj_sound hd m₁ m₂ hp hq (mstep_same ts₁ ts₂ d₁ d₂ hp hq e)).elim
    · obtain ⟨c₁₂, x, y⟩ := mstep_comm ts₁ ts₂ (MapHook.binds_disj d₁ d₂ hkk)
        (or_of_not_both n₁ n₂ hk) (compat_of _ _ hc₁₂ _ _ i₁ i₂@KC12@)
      exact fjoin_m hdet hs₂ i₂ l₂ hc ts₂ x (l₁ _ _ y ((calm_iff hs₂ i₂ ts₂).1 hc)) f₁ f₂
  · obtain ⟨a₁, b₁', bs₁, ch₁, ts₁, -, -, l₁, i₁, -@SM@, -⟩ := w₁
    obtain ⟨ch₂, ss₂, l₂, i₂@SM@⟩ := w₂
    obtain ⟨c₁₂, x, y⟩ := mstep_sstep_comm ts₁ ss₂ (compat_of _ _ hc₁₂ _ _ i₁ i₂@KC12@)
    exact fjoin_s hdet hs₂ i₂ l₂ hc ss₂ x (l₁ _ _ y ((calm_iff_s hs₂ i₂ ss₂).1 hc)) f₁ f₂
  · obtain ⟨ch₁, ss₁, l₁, i₁@SM@⟩ := w₁
    obtain ⟨a₂, b₂', bs₂, ch₂, ts₂, -, -, l₂, i₂, -@SM@, -⟩ := w₂
    obtain ⟨c₁₂, x, y⟩ := mstep_sstep_comm ts₂ ss₁ (compat_of _ _ ((compatTbl_symm _ _).trans hc₁₂) _ _ i₂ i₁@KC21@)
    exact fjoin_m hdet hs₂ i₂ l₂ hc ts₂ y (l₁ _ _ x ((calm_iff hs₂ i₂ ts₂).1 hc)) f₁ f₂
  · obtain ⟨ch₁, ss₁, l₁, i₁@SM@⟩ := w₁
    obtain ⟨ch₂, ss₂, l₂, i₂@SM@⟩ := w₂
    obtain ⟨c₁₂, x, y⟩ := sstep_comm ss₁ ss₂ (compat_of _ _ hc₁₂ _ _ i₁ i₂@KC12@)
    exact fjoin_s hdet hs₂ i₂ l₂ hc ss₂ x (l₁ _ _ y ((calm_iff_s hs₂ i₂ ss₂).1 hc)) f₁ f₂

/-- Two steps from a calm configuration, neither pair decided by `flushOK`: they join in one step
each, by `staticOK` or a slot. -/
theorem joins_at (O : OpenJoins) (S : SameThreadJoins)@K_BIND@ {r₁ r₂ : Rule} {c c₁ c₂ : @TOP@}
    (hc : Calm c) (v₁ : ViewOf r₁ c c₁) (v₂ : ViewOf r₂ c c₂) (hf : flushOK r₁ r₂ = false)
    (hf' : flushOK r₂ r₁ = false) : DiamondMod @NA@.Step Eq c₁ c₂ := by
  cases hs : staticOK r₁ r₂
  · exact O r₁ r₂ hs hf hf' (Nat.le_of_not_lt fun h => hc _ h v₁.1) v₁.2.2.1 v₂.2.2.1
  · exact join_static S@K_ARG@ hs v₁ v₂

theorem fjoins_of (O : OpenJoins) (S : SameThreadJoins)@K_BIND@ (D : FlushDet) (E : FlushEnds)
    {c c₁ c₂ n₁ n₂ : @TOP@} (hc : Calm c) (h₁ : @NA@.Step c c₁) (h₂ : @NA@.Step c c₂)
    (f₁ : FlushNF @NA@.Step Calm c₁ n₁) (f₂ : FlushNF @NA@.Step Calm c₂ n₂) :
    DiamondMod (FStep @NA@.Step Calm) (ObsEq @NA@.Step obs) n₁ n₂ := by
  obtain ⟨r₁, v₁⟩ := view_of h₁
  obtain ⟨r₂, v₂⟩ := view_of h₂
  cases hf : flushOK r₁ r₂
  · cases hf' : flushOK r₂ r₁
    · exact fdiamond_of_diamond (ObsEq.stepEquiv obs) (hdet_of D) E f₁ f₂ (joins_at O S@K_ARG@ hc v₁ v₂ hf hf')
    · exact (join_flush (hdet_of D) S E hf' hc v₂ v₁ f₂ f₁).symm (ObsEq.stepEquiv obs)
  · exact join_flush (hdet_of D) S E hf hc v₁ v₂ f₁ f₂

/-- Given the joins left open, the determinism of the flush and that it stops, two runs that end
in terminal configurations end with one observation. -/
theorem obs_unique_of (O : OpenJoins) (S : SameThreadJoins)@K_BIND@ (D : FlushDet) (E : FlushEnds)
    {c n₁ n₂ : @TOP@}
    (h₁ : Star @NA@.Step c n₁) (t₁ : Terminal @NA@.Step n₁) (h₂ : Star @NA@.Step c n₂)
    (t₂ : Terminal @NA@.Step n₂) : obs n₁ = obs n₂ :=
  (unique_of_flush (ObsEq.stepEquiv obs) (hdet_of D) (fun hc s₁ s₂ f₁ f₂ => fjoins_of O S@K_ARG@ D E hc s₁ s₂ f₁ f₂)
    h₁ t₁ h₂ t₂).obs

