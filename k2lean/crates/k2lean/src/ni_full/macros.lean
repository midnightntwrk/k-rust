/-- The generic case of `CQ`. -/
local macro "k2l_cq" : tactic => `(tactic| (
  intros
  k2l_cases_cells
  unfold CQ
  intro K b₀ hck hne hgood
  cases b₀ <;> simp only [AtBase_false, AtBase_true_kseq, kOf, storeOf, pubOf, discOf, CK_kseq, and_true_left, isKResult_eq, not_and] at hck hne hgood ⊢
  all_goals refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | rfl
    | with_reducible exact hiOnly_refl hgood
    | (try simp only [@NA@.proj_eq_some_KItem_@HS@, @NA@.proj_eq_some_@HS@_@VS@,
         @NA@.proj_eq_some_KItem_@VS@] at *
       try subst_vars
       try k2l_values
       try k2l_ni_comp)))

/-- The generic case of `SQ`. -/
local macro "k2l_sq" : tactic => `(tactic| (
  intros
  k2l_cases_cells
  unfold SQ
  intro hlk hgood
  simp only [kOf, storeOf] at hlk hgood ⊢
  try simp only [@NA@.proj_eq_some_KItem_@HS@, @NA@.proj_eq_some_@HS@_@VS@,
    @NA@.proj_eq_some_KItem_@VS@] at *
  try subst_vars
  try simp only [and_true_left, isKResult_eq] at *
  try k2l_values
  try k2l_ni_simp
  try k2l_ni_split
  all_goals (try k2l_ni_simp)
  all_goals first
    | (apply sq_base; k2l_ni_comp; done)
    | (apply sq_drop2 <;> simp only [dropK, CK_kseq] <;> k2l_ni_comp <;> done)
    | (apply sq_disclose <;> (try simp only [CK_kseq]) <;> k2l_ni_comp <;> done)
    | skip))

/-- The generic case of `SameQ` for the rule whose `Step` constructor is `c`: the other run, at the
same stack with the same observation, takes the same rule (`Step.deterministic`); or the stack is
not low. -/
local macro "k2l_same " c:ident : tactic => `(tactic| (
  intros
  unfold SameQ
  intro c₂ c₂' hS h₂
  obtain ⟨hk, hlk, hlow, hpub, hdisc⟩ := hS
  k2l_cases c₂ with ⟨⟨k₂⟩, x1₂, x2₂, x3₂, x4₂, x5₂, x6₂⟩
  k2l_cases_cells
  simp only [kOf, pubOf, discOf, Prod.mk.injEq] at hk hpub hdisc
  obtain ⟨hl, ht⟩ := hpub
  subst hk hl ht hdisc
  first
    | (have hd := @NA@.Step.deterministic h₂ (by apply $c <;> assumption)
       subst hd
       simp only [kOf, storeOf, pubOf, discOf, true_and, and_true] at hlow ⊢
       assumption)
    | (simp only [kOf, lk_kseq, litem_false] at hlk; k2l_ni_comp; done)))

/-- The generic case of `AppendQ`. -/
local macro "k2l_append" : tactic => `(tactic| (
  intros
  k2l_cases_cells
  unfold AppendQ
  simp only [discOf]
  first
    | exact List.prefix_refl _
    | (rw [toList_concat_element]; exact List.prefix_append _ _)))

/-- The generic case of `CoolQ` and `DiscQ`: the rule does not apply to that stack, or it is the
one that does. -/
local macro "k2l_bound " q:ident : tactic => `(tactic| (
  intros
  k2l_cases_cells
  unfold $q
  intro v K hv hk
  simp only [kOf, storeOf, pubOf, discOf] at hk ⊢
  try simp at hk
  try obtain ⟨rfl, hk⟩ := hk
  try subst_vars
  try simp only [@NA@.proj_eq_some_KItem_@HS@, @NA@.proj_eq_some_@HS@_@VS@] at *
  try subst_vars
  all_goals first
    | exact ⟨⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩
    | (simp_all [isRes, toList_concat_element, BoolHook.and, BoolHook.not]; done)))

/-- `CONTRACT.var`, by hand: the looked-up value is a value, since the store is one. -/
