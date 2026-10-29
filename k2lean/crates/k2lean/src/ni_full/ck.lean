/-- A confined stack over the continuation `K`, which receives `b₀` (a value pending, under a
disclosure; nothing, otherwise): `k` is `K` with `b₀` pending, or its first item consumes `b` and
the rest is a confined stack over `K`. -/
def CK (G : Lab) (K : @K@) (b₀ : Bool) : Bool → @K@ → Prop
  | b, .dotk => b = b₀ ∧ @K@.dotk = K
  | b, .kseq it k => (b = b₀ ∧ @K@.kseq it k = K) ∨
      (match citem G b it with
       | some o => CK G K b₀ o k
       | none => False)

theorem CK_kseq (G : Lab) (K : @K@) (b₀ b : Bool) (it : @KIT@) (k : @K@) :
    CK G K b₀ b (.kseq it k) = ((b = b₀ ∧ @K@.kseq it k = K) ∨
      (match citem G b it with
       | some o => CK G K b₀ o k
       | none => False)) := by rw [CK]

theorem CK_dotk (G : Lab) (K : @K@) (b₀ b : Bool) :
    CK G K b₀ b .dotk = (b = b₀ ∧ @K@.dotk = K) := by rw [CK]

theorem CK_base (G : Lab) (K : @K@) (b₀ : Bool) : CK G K b₀ b₀ K := by
  k2l_cases K <;> simp [CK]

