/-
  KCore: the interface of a theorem kind (ARCHITECTURE.md §3.7).

  A kind proves one goal about a definition from a property per index (`Kind`): the indices
  (`idxs`, a rule's number, a pair of rules' numbers), the obligation at an index (`Ob`), and the
  glue from every index's obligation to the goal. A decider (`Decider`) is a Boolean condition per
  index, read off the definition's data, whose truth gives the obligation there (`sound`).

  A kind's theorem (`of_decided`) is one decision and a list of obligations: every index the
  condition does not confirm is listed (`decides`, decided by the kernel), and each listed index's
  obligation is proved, by hand or as a premise. `of_blocks` is the same with the indices split into
  blocks, each decided on its own (a large definition's decision in separately checked parts).

  Two shapes of indices recur:
  - the elements of a list (`ofList`): index i is the list's element at i, its obligation a
    property of that element (`listCond` the condition read at each index);
  - rows of indices (`rows`): row i a list of indices, the rows lo, …, lo + len - 1 a block, the
    blocks of consecutive lengths together the rows 0, … (`rows_blocks_of`).
-/

set_option autoImplicit false

namespace KCore

/-- A theorem kind: indices, an obligation per index, and the goal every index's obligation
gives. -/
structure Kind where
  Idx : Type
  idxs : List Idx
  Ob : Idx → Prop
  Goal : Prop
  glue : (∀ i ∈ idxs, Ob i) → Goal

namespace Kind

/-- A decider for a kind: a condition per index whose truth gives the obligation there. -/
structure Decider (K : Kind) where
  cond : K.Idx → Bool
  sound : ∀ i, cond i = true → K.Ob i

/-- Every index of `is` is confirmed by `cond` or listed in `obl`. -/
def decides {ι : Type} [BEq ι] (cond : ι → Bool) (obl is : List ι) : Bool :=
  is.all fun i => cond i || obl.contains i

theorem decides_mem {ι : Type} [BEq ι] [LawfulBEq ι] {cond : ι → Bool} {obl is : List ι}
    (h : decides cond obl is = true) {i : ι} (hi : i ∈ is) : cond i = true ∨ i ∈ obl := by
  have := List.all_eq_true.mp h i hi
  simpa only [Bool.or_eq_true, List.contains_iff_mem] using this

theorem decides_append {ι : Type} [BEq ι] (cond : ι → Bool) (obl is₁ is₂ : List ι) :
    decides cond obl (is₁ ++ is₂) = (decides cond obl is₁ && decides cond obl is₂) := by
  simp only [decides, List.all_append]

theorem decides_flatten {ι : Type} [BEq ι] {cond : ι → Bool} {obl : List ι} :
    ∀ {bs : List (List ι)}, (∀ b ∈ bs, decides cond obl b = true) → decides cond obl bs.flatten = true
  | [], _ => rfl
  | b :: bs, h => by
    rw [List.flatten_cons, decides_append, h b (List.mem_cons_self ..),
      decides_flatten fun b' hb' => h b' (List.mem_cons_of_mem _ hb')]
    rfl

/-- **A kind's theorem from one decision**: every index is confirmed by the decider or listed in
`obl`, and every listed index's obligation is proved. -/
theorem of_decided (K : Kind) [BEq K.Idx] [LawfulBEq K.Idx] (d : K.Decider) (obl : List K.Idx)
    (h : decides d.cond obl K.idxs = true) (ho : ∀ i ∈ obl, K.Ob i) : K.Goal :=
  K.glue fun i hi => (decides_mem h hi).elim (d.sound i) (ho i)

/-- **A kind's theorem from decisions by blocks**: the indices split into blocks, each block
decided on its own. -/
theorem of_blocks (K : Kind) [BEq K.Idx] [LawfulBEq K.Idx] (d : K.Decider) (obl : List K.Idx)
    (bs : List (List K.Idx)) (hs : K.idxs = bs.flatten) (hb : ∀ b ∈ bs, decides d.cond obl b = true)
    (ho : ∀ i ∈ obl, K.Ob i) : K.Goal :=
  of_decided K d obl (hs ▸ decides_flatten hb) ho

/-! ## Indices: the elements of a list -/

/-- The kind whose index i is the element of `rs` at i, with obligation `Q` of it, and whose goal
follows from `Q` of every element. -/
@[reducible] def ofList {α : Type} (rs : List α) (Q : α → Prop) (Goal : Prop)
    (glue : (∀ a ∈ rs, Q a) → Goal) : Kind where
  Idx := Nat
  idxs := List.range rs.length
  Ob i := ∀ a, rs[i]? = some a → Q a
  Goal := Goal
  glue h := glue fun a ha => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    exact h i (List.mem_range.mpr hi) _ (List.getElem?_eq_getElem hi)

/-- A condition on the elements, read at an index (true past the end, where the obligation is
vacuous). -/
def listCond {α : Type} (rs : List α) (cond : α → Bool) (i : Nat) : Bool :=
  match rs[i]? with
  | some a => cond a
  | none => true

/-- The decider of `ofList` from a condition on the elements that gives `Q`. -/
def listDecider {α : Type} {rs : List α} {Q : α → Prop} {Goal : Prop} {glue : (∀ a ∈ rs, Q a) → Goal}
    (cond : α → Bool) (sound : ∀ a ∈ rs, cond a = true → Q a) : (ofList rs Q Goal glue).Decider where
  cond := listCond rs cond
  sound i h a ha := by
    simp only [listCond, ha] at h
    exact sound a (List.mem_of_getElem? ha) h

/-! ## Indices: rows -/

/-- The indices of the rows lo, …, lo + len - 1. -/
def rows {ι : Type} (row : Nat → List ι) (lo len : Nat) : List ι := (List.range' lo len).flatMap row

/-- The blocks of rows of the lengths `lens`, consecutive from lo. -/
def blocks {ι : Type} (row : Nat → List ι) : Nat → List Nat → List (List ι)
  | _, [] => []
  | lo, len :: lens => rows row lo len :: blocks row (lo + len) lens

theorem rows_add {ι : Type} (row : Nat → List ι) (lo a b : Nat) :
    rows row lo (a + b) = rows row lo a ++ rows row (lo + a) b := by
  simp only [rows, ← List.flatMap_append]
  congr 1
  rw [List.range'_append_1]

theorem rows_blocks {ι : Type} (row : Nat → List ι) :
    ∀ (lo : Nat) (lens : List Nat), rows row lo lens.sum = (blocks row lo lens).flatten
  | lo, [] => by simp [rows, blocks]
  | lo, len :: lens => by
    rw [List.sum_cons, rows_add, rows_blocks row (lo + len) lens]
    rfl

/-- The rows 0, …, n - 1 are the blocks of the lengths `lens`, where they sum to n. -/
theorem rows_blocks_of {ι : Type} {row : Nat → List ι} {n : Nat} {lens : List Nat} (hn : n = lens.sum) :
    rows row 0 n = (blocks row 0 lens).flatten := hn ▸ rows_blocks row 0 lens

end Kind

end KCore
