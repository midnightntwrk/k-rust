/-! ## The per-rule properties -/

/-- The disclosure's freezer: the continuation of a confined part with a value pending. -/
abbrev frzD : @KIT@ :=
  @KIT@.inj_KItem @FRZ@

/-- A confined stack has reached its continuation `K`: `k` is `K` (nothing pending), or a value on
`K` (a value pending). -/
def AtBase (K : @K@) : Bool → @K@ → Prop
  | false, k => k = K
  | true, .kseq v k => isRes v = true ∧ k = K
  | true, .dotk => False

@[simp] theorem AtBase_false (K k : @K@) : AtBase K false k = (k = K) := by rw [AtBase]
@[simp] theorem AtBase_true_kseq (K : @K@) (v : @KIT@) (k : @K@) :
    AtBase K true (.kseq v k) = (isRes v = true ∧ k = K) := by rw [AtBase]
@[simp] theorem AtBase_true_dotk (K : @K@) : AtBase K true .dotk = False := by rw [AtBase]

/-- The continuation of a confined part: a low stack receiving `b₀`; with a value pending, the
disclosure's freezer on a low stack. -/
def Over (G : Lab) (K : @K@) (b₀ : Bool) : Prop :=
  lk G b₀ K = true ∧ (b₀ = true → ∃ K', K = .kseq frzD K')

/-- A step of a run inside a confined stack keeps it a confined stack over the same continuation,
changes the store only at high identifiers, and changes neither the observation nor the
disclosure cell. -/
def CQ (G : Lab) (c c' : @TOP@) : Prop :=
  ∀ K b₀, CK G K b₀ false (kOf c) → ¬ AtBase K b₀ (kOf c) → @GOOD@ (storeOf c) →
    CK G K b₀ false (kOf c') ∧ @HIONLY@ (storeOf c) (storeOf c') ∧ pubOf c' = pubOf c ∧
      discOf c' = discOf c

/-- The first `n` items of `<k>` dropped. -/
def dropK : Nat → @K@ → @K@
  | 0, k => k
  | _ + 1, .dotk => .dotk
  | n + 1, .kseq _ k => dropK n k

/-- `k` is a confined stack over a continuation. -/
def Lands (G : Lab) (k : @K@) : Prop := ∃ K b₀, CK G K b₀ false k ∧ Over G K b₀

/-- A step from a low stack leads to a confined stack over a continuation (the confined part is
empty unless the step enters a high assignment, a branch on a high condition, or the disclosure of
a high expression). -/
def SQ (G : Lab) (c c' : @TOP@) : Prop :=
  lk G false (kOf c) = true → @GOOD@ (storeOf c) → Lands G (kOf c')

theorem sq_base {G : Lab} {k : @K@} (h : lk G false k = true) : Lands G k :=
  ⟨k, false, CK_base G k false, h, by simp⟩

theorem sq_drop2 {G : Lab} {k : @K@} (h₁ : CK G (dropK 2 k) false false k)
    (h₂ : lk G false (dropK 2 k) = true) : Lands G k :=
  ⟨_, false, h₁, h₂, by simp⟩

theorem sq_disclose {G : Lab} {e : @KIT@} {K : @K@}
    (h₁ : CK G (.kseq frzD K) true false (.kseq e (.kseq frzD K)))
    (h₂ : lk G true (.kseq frzD K) = true) : Lands G (.kseq e (.kseq frzD K)) :=
  ⟨_, true, h₁, h₂, fun _ => ⟨K, rfl⟩⟩

/-- Both runs at the same low stack, with low-equal stores, the same observation and the same
disclosed values. -/
def Sync (G : Lab) (c₁ c₂ : @TOP@) : Prop :=
  kOf c₁ = kOf c₂ ∧ lk G false (kOf c₁) = true ∧ @LOWEQ@ (storeOf c₁) (storeOf c₂) ∧
    pubOf c₁ = pubOf c₂ ∧ discOf c₁ = discOf c₂

/-- From the same low stack, the other run steps to the same stack, with low-equal stores, the same
observation and the same disclosed values. -/
def SameQ (G : Lab) (c₁ c₁' : @TOP@) : Prop :=
  ∀ c₂ c₂', Sync G c₁ c₂ → @NA@.Step c₂ c₂' → kOf c₁' = kOf c₂' ∧
    @LOWEQ@ (storeOf c₁') (storeOf c₂') ∧ pubOf c₁' = pubOf c₂' ∧ discOf c₁' = discOf c₂'

/-- A step only appends to the disclosure cell. -/
def AppendQ (c c' : @TOP@) : Prop :=
  ListIso.toList (discOf c) <+: ListIso.toList (discOf c')

/-- From a value on the disclosure's freezer, a step cools it, and changes nothing else. -/
def CoolQ (c c' : @TOP@) : Prop :=
  ∀ v K, isRes v = true → kOf c = .kseq v (.kseq frzD K) →
    (∃ e, @NA@.inj_@HS@_KItem e = v ∧
      kOf c' = .kseq (@DITEM@ (@DOWN@ e)) K) ∧
    storeOf c' = storeOf c ∧ pubOf c' = pubOf c ∧ discOf c' = discOf c

/-- From the disclosure of a value, a step leaves the value, appends it to the disclosure cell, and
changes nothing else. -/
def DiscQ (c c' : @TOP@) : Prop :=
  ∀ e K, isRes (@NA@.inj_@HS@_KItem e) = true →
    kOf c = .kseq (@DITEM@ (@DOWN@ e)) K →
    kOf c' = .kseq (@NA@.inj_@HS@_KItem e) K ∧ storeOf c' = storeOf c ∧ pubOf c' = pubOf c ∧
      ListIso.toList (discOf c') = ListIso.toList (discOf c) ++ [@NA@.inj_@HS@_KItem e]

