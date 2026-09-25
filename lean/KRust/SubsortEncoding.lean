/-
Case study 2 of `draft/lean-verification/README.md`: the Z3 subsort encoding.

Rust modelled here, with line anchors at bb256f2c:
  crates/k-rust/src/inner/parser/z3_inference.rs
    EncodingBase                  :76-92     (ground_values, closed_values, semantic_relation)
    OrderRelation                 :98-137    (pairs; up- and down-sets built once by `new`
                                              :105-115, read by `up` :117-119, `down` :121-123)
    OrderRelation::full_disjunction :125-136 (`old`)
    EncodingBase::build           :637-641   (closed_values = the cached ground values; the
                                              relation)
    EncodingBase::sort_value      :645-682   (ground values are cached constructor terms)
    EncodingBase::order_relation  :684-707   (R = pairs of real ground sorts with l = r or l < r)
    Encoding::less_than_eq        :1663-1717 (`new`: the dispatch on closed sides is :1678-1704)
    or_all                        :3275-3281 (the empty disjunction is `false`)
  crates/k-rust/src/definition/partial_order.rs (unchanged since 2aec72c7)
    PartialOrder::new closure     :119-137
    PartialOrder::less_than_eq    :179-181
  z3-0.20.2 src/ast/mod.rs
    PartialEq for ASTs            :487-492   (`Z3_is_eq_ast`)
    Hash for ASTs                 :526-533   (`Z3_get_ast_hash`)
`new` is `Encoding::less_than_eq` (ticket OT-03). `old` is `OrderRelation::full_disjunction`, the
encoding of every order constraint before OT-03, which `less_than_eq` still uses when neither side
is a closed value. The property test `ground_side_encoding_is_equivalent` in the `tests` module of
z3_inference.rs checks the two against each other with Z3. The bridge tests
`tests::lean_bridge::less_than_eq_agrees_with_new` and `full_disjunction_agrees_with_old` compare
the formulas the two Rust functions build with `new` and `old` (models `lessThanEq` and
`fullDisjunction` of `KRustBridge/Dispatch.lean`).
-/

namespace KRust.SubsortEncoding

/-! ## Model

`G` is the type of ground sort values that Rust recognises by AST identity.
The z3 crate's `PartialEq` and `Hash` on ASTs are `Z3_is_eq_ast` and the AST hash
(z3-0.20.2 src/ast/mod.rs:487-492, :526-533), so "recognised" means syntactic identity of
hash-consed terms.
The values in `closed_values` (the values of `ground_values`) are constructor applications of the
datatype `KRustInferenceSort` (z3_inference.rs:645-682).

`D` is the carrier of that datatype in a Z3 model, and `I : G → D` interprets a ground value.
The only semantic fact about Z3 used below is that `I` is injective: two syntactically distinct
constructor terms of a free (algebraic) datatype denote distinct elements.
That is the SMT-LIB datatype theory; it is a trusted assumption about Z3, stated as the hypothesis
`hI : Injective I`.
It would be false if a "ground value" could be a non-constructor closed term (an accessor
application, say), which is why the Rust test for a closed side must stay "is one of the cached
constructor terms" (`closed_values.contains`). -/

variable {G D : Type}

/-- Injectivity of the interpretation of ground values (core Lean has no `Function.Injective`
without Mathlib). -/
def Injective (I : G → D) : Prop := ∀ x y, I x = I y → x = y

/-- A Z3 expression of the inference datatype as `less_than_eq` receives it:
either one of the cached ground values, or anything else (a variable, a parametric sort applied to
variables, an uncached value). The `other` case is denoted by the environment. -/
inductive Tm (G : Type) where
  | val   : G → Tm G
  | other : Nat → Tm G

/-- The value of an expression in a model: `I` on cached ground values, `ρ` elsewhere. -/
def Tm.den (I : G → D) (ρ : Nat → D) : Tm G → D
  | .val g   => I g
  | .other n => ρ n

/-- `x.eq(y)` -/
structure Eqn (G : Type) where
  lhs : Tm G
  rhs : Tm G

/-- The shape `less_than_eq` builds: `Bool::or` of `Bool::and` of equalities.
`[]` is `or_all(&[]) = false` (z3_inference.rs:3275-3281); `[[]]` is `Bool::from_bool(true)`. -/
abbrev Dnf (G : Type) := List (List (Eqn G))

/-- An equality holds in a model when both sides denote the same element. -/
def Eqn.holds (I : G → D) (ρ : Nat → D) (e : Eqn G) : Prop :=
  e.lhs.den I ρ = e.rhs.den I ρ

/-- A disjunction of conjunctions holds when some conjunction has all its equalities hold. -/
def Dnf.holds (I : G → D) (ρ : Nat → D) (d : Dnf G) : Prop :=
  ∃ c ∈ d, ∀ e ∈ c, e.holds I ρ

/-! ## The full disjunction -/

/-- The full disjunction (`OrderRelation::full_disjunction`, z3_inference.rs:125-136):
`OR over (l, r) in R of (lesser = l ∧ greater = r)`, then `∨ lesser = greater`.
`R` is `semantic_relation`, whose pairs `order_relation` builds
(z3_inference.rs:684-707). -/
def old (R : List (G × G)) (a b : Tm G) : Dnf G :=
  R.map (fun p => [⟨a, .val p.1⟩, ⟨b, .val p.2⟩]) ++ [[⟨a, b⟩]]

/-! ## Lemmas about the formula shape -/

section
variable (I : G → D) (ρ : Nat → D)

/-- `holds` of an appended disjunction is the disjunction of `holds` (propositional equality of
truth values, as an `Iff`). -/
theorem holds_append (d e : Dnf G) :
    Dnf.holds I ρ (d ++ e) ↔ Dnf.holds I ρ d ∨ Dnf.holds I ρ e := by
  unfold Dnf.holds
  constructor
  · rintro ⟨c, hc, h⟩
    rcases List.mem_append.mp hc with hc | hc
    · exact Or.inl ⟨c, hc, h⟩
    · exact Or.inr ⟨c, hc, h⟩
  · rintro (⟨c, hc, h⟩ | ⟨c, hc, h⟩)
    · exact ⟨c, List.mem_append.mpr (Or.inl hc), h⟩
    · exact ⟨c, List.mem_append.mpr (Or.inr hc), h⟩

/-- A one-equality disjunction holds iff its equality holds. -/
theorem holds_unit (e : Eqn G) : Dnf.holds I ρ [[e]] ↔ e.holds I ρ := by
  unfold Dnf.holds
  constructor
  · rintro ⟨c, hc, h⟩
    rw [List.mem_singleton] at hc
    subst hc
    exact h e (List.mem_singleton.mpr rfl)
  · intro h
    refine ⟨[e], List.mem_singleton.mpr rfl, ?_⟩
    intro e' he'
    rw [List.mem_singleton] at he'
    subst he'
    exact h

/-- `[[]]` (`Bool::from_bool(true)`) holds in every model. -/
theorem holds_true : Dnf.holds I ρ ([[]] : Dnf G) :=
  ⟨[], List.mem_singleton.mpr rfl, fun _ he => by simp at he⟩

/-- `[]` (`or_all(&[])`, i.e. `false`) holds in no model. -/
theorem not_holds_false : ¬ Dnf.holds I ρ ([] : Dnf G) :=
  fun ⟨_, hc, _⟩ => by simp at hc

/-- The relational reading of the full disjunction: `old R a b` holds iff the values of `a` and `b`
are the interpretations of a pair in `R`, or are equal. -/
theorem old_holds (R : List (G × G)) (a b : Tm G) :
    Dnf.holds I ρ (old R a b) ↔
      (∃ p ∈ R, a.den I ρ = I p.1 ∧ b.den I ρ = I p.2) ∨ a.den I ρ = b.den I ρ := by
  unfold old
  rw [holds_append, holds_unit]
  refine or_congr ?_ Iff.rfl
  unfold Dnf.holds
  constructor
  · rintro ⟨c, hc, h⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    exact ⟨p, hp, h ⟨a, .val p.1⟩ (by simp), h ⟨b, .val p.2⟩ (by simp)⟩
  · rintro ⟨p, hp, h1, h2⟩
    refine ⟨_, List.mem_map.mpr ⟨p, hp, rfl⟩, ?_⟩
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact h1
    · exact h2

/-- A disjunction of single equalities `t = r`, `r ∈ xs`, holds iff `t` denotes one of the `r`. -/
theorem holds_map_single (xs : List G) (t : Tm G) :
    Dnf.holds I ρ (xs.map (fun r => [⟨t, .val r⟩])) ↔ ∃ r ∈ xs, t.den I ρ = I r := by
  unfold Dnf.holds
  constructor
  · rintro ⟨c, hc, h⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
    exact ⟨r, hr, h _ (List.mem_singleton.mpr rfl)⟩
  · rintro ⟨r, hr, h⟩
    refine ⟨[⟨t, .val r⟩], List.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
    intro e he
    rw [List.mem_singleton] at he
    subst he
    exact h

end

/-! ## The ground-side encoding

Deciding whether a side is a cached ground value, and computing up-sets and down-sets, compares
ground values; in Rust that is AST identity, here decidable equality on `G`. -/

variable [DecidableEq G]

/-- The up-set of a ground value in `R` (`OrderRelation::up`, z3_inference.rs:117-119; built once
per relation by `OrderRelation::new`, :101-111, in the order of the pairs). -/
def up (R : List (G × G)) (l : G) : List G :=
  (R.filter (fun p => decide (p.1 = l))).map Prod.snd

/-- The down-set of a ground value in `R` (`OrderRelation::down`, z3_inference.rs:121-123). -/
def down (R : List (G × G)) (r : G) : List G :=
  (R.filter (fun p => decide (p.2 = r))).map Prod.fst

/-- Lesser side ground: `OR over r in up(l) of (greater = r)`, then `∨ lesser = greater`
(z3_inference.rs:1685-1693). -/
def lesserGround (R : List (G × G)) (l : G) (b : Tm G) : Dnf G :=
  (up R l).map (fun r => [⟨b, .val r⟩]) ++ [[⟨.val l, b⟩]]

/-- Greater side ground: `OR over l in down(r) of (lesser = l)`, then `∨ lesser = greater`
(z3_inference.rs:1694-1702). -/
def greaterGround (R : List (G × G)) (a : Tm G) (r : G) : Dnf G :=
  (down R r).map (fun l => [⟨a, .val l⟩]) ++ [[⟨a, .val r⟩]]

/-- Both sides ground: decided in Rust (`Bool::from_bool(lesser == greater || up(lesser) contains
greater)`, z3_inference.rs:1682-1684). -/
def bothGround (R : List (G × G)) (l r : G) : Dnf G :=
  if l = r ∨ (l, r) ∈ R then [[]] else []

/-- `Encoding::less_than_eq` (z3_inference.rs:1678-1704): dispatch on which sides are cached
ground values (`closed_values.contains`); with neither, the full disjunction (:1651). -/
def new (R : List (G × G)) : Tm G → Tm G → Dnf G
  | .val l,   .val r   => bothGround R l r
  | .val l,   .other n => lesserGround R l (.other n)
  | .other m, .val r   => greaterGround R (.other m) r
  | .other m, .other n => old R (.other m) (.other n)

/-- Membership in the up-set is membership of the pair in `R`. -/
theorem mem_up (R : List (G × G)) (l r : G) : r ∈ up R l ↔ (l, r) ∈ R := by
  simp only [up, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨l', r'⟩, ⟨hp, hl⟩, rfl⟩
    simp only at hl
    subst hl
    exact hp
  · intro h
    exact ⟨(l, r), ⟨h, rfl⟩, rfl⟩

/-- Membership in the down-set is membership of the pair in `R`. -/
theorem mem_down (R : List (G × G)) (l r : G) : l ∈ down R r ↔ (l, r) ∈ R := by
  simp only [down, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨l', r'⟩, ⟨hp, hr⟩, rfl⟩
    simp only at hr
    subst hr
    exact hp
  · intro h
    exact ⟨(l, r), ⟨h, rfl⟩, rfl⟩

/-! ## Equivalence

No hypothesis on `R`: the rewrite is an equivalence for every relation, closed or not.
Transitive closure is what makes `R` mean "is a subsort of" (`order_relation` reads the closed
`PartialOrder`, definition/partial_order.rs:119-137, :179-181); it is not needed for old ⇔ new. -/

/-- Lesser side ground: `old` and `lesserGround` hold in exactly the same Z3 models
(logical equivalence, not syntactic equality of the formulas). -/
theorem lesserGround_equiv (I : G → D) (hI : Injective I) (ρ : Nat → D)
    (R : List (G × G)) (l : G) (b : Tm G) :
    Dnf.holds I ρ (old R (.val l) b) ↔ Dnf.holds I ρ (lesserGround R l b) := by
  rw [old_holds]
  unfold lesserGround
  rw [holds_append, holds_unit, holds_map_single]
  constructor
  · rintro (⟨⟨p1, p2⟩, hp, h1, h2⟩ | h)
    · have e : l = p1 := hI _ _ h1
      subst e
      exact Or.inl ⟨p2, (mem_up R l p2).mpr hp, h2⟩
    · exact Or.inr h
  · rintro (⟨r, hr, h⟩ | h)
    · exact Or.inl ⟨(l, r), (mem_up R l r).mp hr, rfl, h⟩
    · exact Or.inr h

/-- Greater side ground: `old` and `greaterGround` hold in exactly the same Z3 models
(logical equivalence). -/
theorem greaterGround_equiv (I : G → D) (hI : Injective I) (ρ : Nat → D)
    (R : List (G × G)) (a : Tm G) (r : G) :
    Dnf.holds I ρ (old R a (.val r)) ↔ Dnf.holds I ρ (greaterGround R a r) := by
  rw [old_holds]
  unfold greaterGround
  rw [holds_append, holds_unit, holds_map_single]
  constructor
  · rintro (⟨⟨p1, p2⟩, hp, h1, h2⟩ | h)
    · have e : r = p2 := hI _ _ h2
      subst e
      exact Or.inl ⟨p1, (mem_down R p1 r).mpr hp, h1⟩
    · exact Or.inr h
  · rintro (⟨l, hl, h⟩ | h)
    · exact Or.inl ⟨(l, r), (mem_down R l r).mp hl, h, rfl⟩
    · exact Or.inr h

/-- Both sides ground: `old` holds in a Z3 model iff the Rust-side decision `bothGround` is
`true` (logical equivalence; `bothGround` is a constant formula). -/
theorem bothGround_equiv (I : G → D) (hI : Injective I) (ρ : Nat → D)
    (R : List (G × G)) (l r : G) :
    Dnf.holds I ρ (old R (.val l) (.val r)) ↔ Dnf.holds I ρ (bothGround R l r) := by
  rw [old_holds]
  unfold bothGround
  split
  · rename_i h
    refine iff_of_true ?_ (holds_true I ρ)
    rcases h with rfl | h
    · exact Or.inr rfl
    · exact Or.inl ⟨(l, r), h, rfl, rfl⟩
  · rename_i h
    refine iff_of_false ?_ (not_holds_false I ρ)
    rintro (⟨⟨p1, p2⟩, hp, h1, h2⟩ | h3)
    · have e1 : l = p1 := hI _ _ h1
      have e2 : r = p2 := hI _ _ h2
      subst e1
      subst e2
      exact h (Or.inr hp)
    · exact h (Or.inl (hI _ _ h3))

/-- The ground-side `less_than_eq` is equivalent to the full disjunction in every Z3 model of a
free datatype:
for every relation `R` and every pair of sides, `old R a b` and `new R a b` hold in exactly the
same models `(I, ρ)` with `I` injective (logical equivalence of the formulas, not syntactic
equality; the formulas differ whenever a side is ground).
Rust sites: `OrderRelation::full_disjunction` (z3_inference.rs:125-136) for `old`;
`Encoding::less_than_eq` (z3_inference.rs:1663-1717) for `new`.
Hypothesis `hI` (Z3's datatype theory) is checked on the Rust side by the property test
`ground_side_encoding_is_equivalent`, which asks Z3 itself to refute `¬(old ⇔ new)`. -/
theorem new_equiv (I : G → D) (hI : Injective I) (ρ : Nat → D)
    (R : List (G × G)) (a b : Tm G) :
    Dnf.holds I ρ (old R a b) ↔ Dnf.holds I ρ (new R a b) := by
  cases a with
  | val l =>
    cases b with
    | val r   => exact bothGround_equiv I hI ρ R l r
    | other n => exact lesserGround_equiv I hI ρ R l (.other n)
  | other m =>
    cases b with
    | val r   => exact greaterGround_equiv I hI ρ R (.other m) r
    | other n => exact Iff.rfl

/-! ## The follow-up variable–variable encoding (statement for the next step)

The base arm proposes giving each real ground sort a bit-vector code of its up-set, so that
`x ≤ y ⇔ code(x) & code(y) = code(y)`, i.e. `up(y) ⊆ up(x)`.
Here, unlike above, the relation's properties matter: the equivalence needs reflexivity on the
real ground sorts (`order_relation` adds `left == right`, z3_inference.rs:700) and transitivity
(the closure, partial_order.rs:119-137). It also only speaks about values in `S`; the old
encoding lets a variable take a value outside `S` (a parametric instance, a scaffolding sort)
related only to itself, and the new encoding must say what such values get. That case is the
open design question, not the lemma. -/

/-- For a relation reflexive on `S` and transitive, `(x, y) ∈ R` iff `up R y ⊆ up R x`, for every
`y ∈ S` (propositional equivalence of relation membership and up-set inclusion). -/
theorem upset_code_iff (R : List (G × G)) (S : List G)
    (hrefl : ∀ x ∈ S, (x, x) ∈ R)
    (htrans : ∀ x y z, (x, y) ∈ R → (y, z) ∈ R → (x, z) ∈ R)
    (x y : G) (hy : y ∈ S) :
    (x, y) ∈ R ↔ (∀ z, z ∈ up R y → z ∈ up R x) := by
  constructor
  · intro hxy z hz
    exact (mem_up R x z).mpr (htrans x y z hxy ((mem_up R y z).mp hz))
  · intro hsub
    exact (mem_up R x y).mp (hsub y ((mem_up R y y).mpr (hrefl y hy)))

end KRust.SubsortEncoding
