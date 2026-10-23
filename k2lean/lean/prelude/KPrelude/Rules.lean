import KPrelude.Run

/-!
# Certified rule matchers and the step function

A generated rule matcher returns a `RuleResult`: `none` (the left-hand side does not match or
the requires is not `true`), `undefined` with a proof that the rule applies (`A c`), or `next`
with a proof of the one-step relation. Soundness of the executable step is therefore by
construction; completeness is proved per definition.

`firstDefined` is `krun`'s choice for one priority group (k-rust `--strategy any`): the first
rule, in order, whose result is defined; if rules apply but none is defined, the step is
undefined (the first such rule is reported).
-/

namespace KPrelude

inductive RuleResult {α : Type} (A : α → Prop) (R : α → α → Prop) (c : α) : Type where
  | none
  | undefined (h : A c)
  | next (c' : α) (h : R c c')

namespace RuleResult

variable {α : Type} {A : α → Prop} {R : α → α → Prop} {c : α}

def next? : RuleResult A R c → Option α
  | .next c' _ => some c'
  | _ => Option.none

def applies : RuleResult A R c → Bool
  | .none => false
  | _ => true

@[simp] theorem next?_none : (RuleResult.none : RuleResult A R c).next? = Option.none := rfl
@[simp] theorem next?_undefined (h : A c) : (RuleResult.undefined h : RuleResult A R c).next? = Option.none := rfl
@[simp] theorem next?_next (c' : α) (h : R c c') : (RuleResult.next c' h : RuleResult A R c).next? = some c' := rfl
@[simp] theorem applies_none : (RuleResult.none : RuleResult A R c).applies = false := rfl
@[simp] theorem applies_undefined (h : A c) : (RuleResult.undefined h : RuleResult A R c).applies = true := rfl
@[simp] theorem applies_next (c' : α) (h : R c c') : (RuleResult.next c' h : RuleResult A R c).applies = true := rfl

theorem applies_of_next? {r : RuleResult A R c} {c' : α} (h : r.next? = some c') : r.applies = true := by
  cases r <;> simp_all

theorem sound_of_next? {r : RuleResult A R c} {c' : α} (h : r.next? = some c') : R c c' := by
  cases r with
  | none => simp at h
  | undefined => simp at h
  | next c'' hr => simp at h; subst h; exact hr

theorem app_of_applies (hA : ∀ c', R c c' → A c) {r : RuleResult A R c} (h : r.applies = true) : A c := by
  cases r with
  | none => simp at h
  | undefined ha => exact ha
  | next c' hr => exact hA c' hr

end RuleResult

structure Rule (α : Type) (A : α → Prop) (R : α → α → Prop) where
  name : String
  /-- Position in the definition's rule order. -/
  rank : Nat
  run : (c : α) → RuleResult A R c

variable {α : Type} {A : α → Prop} {R : α → α → Prop}

/-- Merge two rule lists sorted by rank, with fuel (structural recursion, so the kernel can
evaluate a step on a closed configuration with `decide`). Out of fuel it appends, which keeps
every rule; `mergeRank` gives enough fuel. -/
def mergeRankN : Nat → List (Rule α A R) → List (Rule α A R) → List (Rule α A R)
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | n + 1, x :: xs, y :: ys =>
    if x.rank ≤ y.rank then x :: mergeRankN n xs (y :: ys) else y :: mergeRankN n (x :: xs) ys

/-- Merge two rule lists sorted by rank (the buckets of a rule index). -/
def mergeRank (xs ys : List (Rule α A R)) : List (Rule α A R) := mergeRankN (xs.length + ys.length) xs ys

theorem mem_mergeRankN {r : Rule α A R} :
    ∀ (n : Nat) (xs ys : List (Rule α A R)), r ∈ mergeRankN n xs ys ↔ r ∈ xs ∨ r ∈ ys
  | 0, xs, ys => by simp [mergeRankN]
  | _ + 1, [], ys => by simp [mergeRankN]
  | _ + 1, x :: xs, [] => by simp [mergeRankN]
  | n + 1, x :: xs, y :: ys => by
    unfold mergeRankN
    split
    · simp only [List.mem_cons, mem_mergeRankN n xs (y :: ys), or_assoc]
    · simp only [List.mem_cons, mem_mergeRankN n (x :: xs) ys, or_assoc, or_left_comm]

@[simp] theorem mem_mergeRank {r : Rule α A R} (xs ys : List (Rule α A R)) :
    r ∈ mergeRank xs ys ↔ r ∈ xs ∨ r ∈ ys := mem_mergeRankN _ xs ys

/-- One priority group: the first defined result; `undefined` if rules apply but none is defined. -/
def firstDefined : List (Rule α A R) → α → Option String → Outcome α
  | [], _, Option.none => .stuck
  | [], _, some n => .undefined n
  | r :: rs, c, u =>
    match r.run c with
    | .next c' _ => .next c'
    | .undefined _ => firstDefined rs c (u <|> some r.name)
    | .none => firstDefined rs c u

theorem firstDefined_sound : ∀ (rs : List (Rule α A R)) (c : α) (u : Option String) (c' : α),
    firstDefined rs c u = .next c' → R c c'
  | [], c, u, c', h => by cases u <;> simp [firstDefined] at h
  | r :: rs, c, u, c', h => by
    unfold firstDefined at h
    split at h
    · next c'' hr _ => simp at h; subst h; exact hr
    · exact firstDefined_sound rs c _ c' h
    · exact firstDefined_sound rs c _ c' h

theorem firstDefined_next_of_mem : ∀ (rs : List (Rule α A R)) (c : α) (u : Option String) (r : Rule α A R) (c' : α),
    r ∈ rs → (r.run c).next? = some c' → ∃ c'', firstDefined rs c u = .next c''
  | [], _, _, _, _, hm, _ => by simp at hm
  | r₀ :: rs, c, u, r, c', hm, h => by
    unfold firstDefined
    split
    · next c'' _ _ => exact ⟨c'', rfl⟩
    · next _ hd =>
      rcases List.mem_cons.1 hm with rfl | hm
      · rw [hd] at h; simp at h
      · exact firstDefined_next_of_mem rs c _ r c' hm h
    · next hd =>
      rcases List.mem_cons.1 hm with rfl | hm
      · rw [hd] at h; simp at h
      · exact firstDefined_next_of_mem rs c _ r c' hm h

theorem firstDefined_stuck : ∀ (rs : List (Rule α A R)) (c : α),
    firstDefined rs c Option.none = .stuck → ∀ r ∈ rs, (r.run c).applies = false
  | [], _, _ => by simp
  | r₀ :: rs, c, h => by
    unfold firstDefined at h
    split at h
    · simp at h
    · next u _ =>
      exfalso
      have : ∀ (rs : List (Rule α A R)) (n : String), firstDefined rs c (some n) ≠ .stuck := by
        intro rs; induction rs with
        | nil => intro n; simp [firstDefined]
        | cons r rs ih =>
          intro n
          unfold firstDefined
          split
          · simp
          · simpa using ih n
          · exact ih n
      exact this rs _ (by simpa using h)
    · next hd =>
      intro r hm
      rcases List.mem_cons.1 hm with rfl | hm
      · rw [hd]; rfl
      · exact firstDefined_stuck rs c h r hm

theorem firstDefined_undefined : ∀ (rs : List (Rule α A R)) (c : α) (u : Option String) (n : String),
    firstDefined rs c u = .undefined n → ∀ r ∈ rs, (r.run c).next? = Option.none
  | [], _, _, _, _ => by simp
  | r₀ :: rs, c, u, n, h => by
    unfold firstDefined at h
    split at h
    · simp at h
    · next hd =>
      intro r hm
      rcases List.mem_cons.1 hm with rfl | hm
      · rw [hd]; rfl
      · exact firstDefined_undefined rs c _ n h r hm
    · next hd =>
      intro r hm
      rcases List.mem_cons.1 hm with rfl | hm
      · rw [hd]; rfl
      · exact firstDefined_undefined rs c _ n h r hm

theorem firstDefined_undefined_applies : ∀ (rs : List (Rule α A R)) (c : α) (n : String),
    firstDefined rs c Option.none = .undefined n → ∃ r ∈ rs, (r.run c).applies = true
  | [], _, _, h => by simp [firstDefined] at h
  | r₀ :: rs, c, n, h => by
    unfold firstDefined at h
    split at h
    · simp at h
    · next hd => exact ⟨r₀, List.mem_cons_self, by rw [hd]; rfl⟩
    · next hd =>
      obtain ⟨r, hm, hr⟩ := firstDefined_undefined_applies rs c n h
      exact ⟨r, List.mem_cons_of_mem _ hm, hr⟩

theorem mem_of_getElem? {β : Type} : ∀ {l : List β} {i : Nat} {a : β}, l[i]? = some a → a ∈ l
  | [], _, _, h => by simp at h
  | b :: l, 0, a, h => by simp at h; subst h; exact List.mem_cons_self
  | b :: l, i + 1, a, h => List.mem_cons_of_mem _ (mem_of_getElem? (l := l) (i := i) (by simpa using h))

theorem firstDefined_of_none : ∀ (rs : List (Rule α A R)) (c : α),
    (∀ r ∈ rs, (r.run c).applies = false) → firstDefined rs c Option.none = .stuck
  | [], _, _ => rfl
  | r₀ :: rs, c, h => by
    unfold firstDefined
    have h0 := h r₀ List.mem_cons_self
    split
    · next hd => rw [hd] at h0; simp at h0
    · next hd => rw [hd] at h0; simp at h0
    · exact firstDefined_of_none rs c (fun r hr => h r (List.mem_cons_of_mem _ hr))

/-! ## Priority ranks

With rewrite-rule priorities, a step uses the first rank (in priority order) at which some rule
applies; `orStuck` chains the ranks. -/

/-- `o`, or the next rank's outcome when no rule of this rank applies. -/
def orStuck {β : Type} (o : Outcome β) (k : Unit → Outcome β) : Outcome β :=
  match o with
  | .stuck => k ()
  | o => o

theorem orStuck_next {β : Type} {o : Outcome β} {k : Unit → Outcome β} {c : β} (h : orStuck o k = .next c) :
    o = .next c ∨ (o = .stuck ∧ k () = .next c) := by
  cases o <;> simp_all [orStuck]

theorem orStuck_stuck {β : Type} {o : Outcome β} {k : Unit → Outcome β} (h : orStuck o k = .stuck) :
    o = .stuck ∧ k () = .stuck := by
  cases o <;> simp_all [orStuck]

theorem orStuck_undefined {β : Type} {o : Outcome β} {k : Unit → Outcome β} {n : String}
    (h : orStuck o k = .undefined n) : o = .undefined n ∨ (o = .stuck ∧ k () = .undefined n) := by
  cases o <;> simp_all [orStuck]

@[simp] theorem orStuck_of_stuck {β : Type} (k : Unit → Outcome β) : orStuck .stuck k = k () := rfl

/-- Every successor by every rule (for search): sound by construction. -/
def successors (rs : List (Rule α A R)) (c : α) : List α := rs.filterMap fun r => (r.run c).next?

theorem mem_successors {rs : List (Rule α A R)} {c c' : α} :
    c' ∈ successors rs c ↔ ∃ r ∈ rs, (r.run c).next? = some c' := by
  simp [successors]

end KPrelude
