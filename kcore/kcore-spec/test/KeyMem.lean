/-
  A rule's key read by `\in`: the cut `∃X. L[X] ∧ X ∈ f(t)` against the hooked equality
  `L[X] ∧ ((X ==Int f(t)) = true)`. Run from the package root: `lake env lean test/KeyMem.lean`.
  Kernel-checked.

  `KeyMemML`, in matching logic (sorts left out): a left side `L[f(t)]` whose key `f(t)` is
  replaced by a variable X with the condition `X ∈ f(t)` is the left side in every interpretation
  where each symbol denotes one element and definedness is total (`cut_exact`; the key under one
  application). The interpretation `D` shows the hooked reading is not: there `f(Y)` has the two
  elements 1 and 2, `==Int` is the equality at every element of Int (`D.eq_graph`), `L` is
  injective (`D.L_injective`); the text's left side is `{L[1], L[2]}` (`D.text_iff`), the cut is
  that set at every valuation (`D.mem_exact`), and `L[X] ∧ ((X ==Int f(Y)) = true)` is empty at
  every valuation, so its union over X is empty (`D.hook_empty`, `D.hook_exists_empty`).

  `KCore.KeyMemTest`, the kernel's definitions: six general lemmas on `Holds` and
  `RuleReqFails` (`holds_mem_true`, `holds_mem_false`, `holds_eqTrue`, `holds_and_true`,
  `holds_and_false`, `ruleReqFails_iff`); and on a hand-built semantics with the rule
  `<k> X:Int ~> Rest </k> <generatedCounter> N </generatedCounter> => <k> Rest </k>
  <generatedCounter> N </generatedCounter>`, X the key of `N +Int 1`, beside a rule of priority
  200 on every configuration: the step by the rule whose `pre` is `X ∈ N +Int 1` (`stepM_A`),
  the same step by the rule whose `requires` is `X ==Int N +Int 1` (`stepH_A`), `NotApplies`
  of the first at a key that is not the function's value (`notAppliesM_B`), and the step of the
  rule of larger priority there (`stepM_B`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KeyMemML
open ML ML.Pattern

section generic
variable {𝕊 M : Type} [HasDefined 𝕊] {I : Interpretation 𝕊 M} {c : 𝕊 → M}

/-- Every symbol denotes one element, and `defined` applied to anything is everything. -/
structure SymOK (I : Interpretation 𝕊 M) (c : 𝕊 → M) : Prop where
  sym : ∀ s a, I.evalSymb s a ↔ a = c s
  dfd : ∀ b m, I.evalApp (c HasDefined.defined) b m

theorem ceil_iff (h : SymOK I c) (ρ : Valuation M) (φ : Pattern 𝕊) (m : M) :
    (⌈φ⌉).interpret I ρ m ↔ ∃ b, φ.interpret I ρ b := by
  rw [interpret_app]
  constructor
  · rintro ⟨a, b, _, hb, _⟩; exact ⟨b, hb⟩
  · rintro ⟨b, hb⟩; exact ⟨c HasDefined.defined, b, (h.sym _ _).mpr rfl, hb, h.dfd b m⟩

theorem equal_iff (h : SymOK I c) (ρ : Valuation M) (φ ψ : Pattern 𝕊) (m : M) :
    (φ ≡ ψ).interpret I ρ m ↔ ∀ b, (φ.interpret I ρ b ↔ ψ.interpret I ρ b) := by
  show (∼⌈∼(φ ⇔ ψ)⌉).interpret I ρ m ↔ _
  rw [interpret_neg, ceil_iff h]
  constructor
  · intro hn b
    apply Classical.byContradiction
    intro hb
    exact hn ⟨b, interpret_neg.mpr (fun hq => hb (interpret_equiv.mp hq))⟩
  · rintro hall ⟨b, hb⟩
    exact (interpret_neg.mp hb) (interpret_equiv.mpr (hall b))

theorem ap1 (h : SymOK I c) (ρ : Valuation M) (s : 𝕊) (φ : Pattern 𝕊) (m : M) :
    (symbol s ⬝ φ).interpret I ρ m ↔ ∃ b, φ.interpret I ρ b ∧ I.evalApp (c s) b m := by
  rw [interpret_app]
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    have : a = c s := (h.sym s a).mp ha
    subst this; exact ⟨b, hb, hab⟩
  · rintro ⟨b, hb, hab⟩; exact ⟨c s, b, (h.sym _ _).mpr rfl, hb, hab⟩

theorem ap2 (h : SymOK I c) (ρ : Valuation M) (s : 𝕊) (φ ψ : Pattern 𝕊) (m : M) :
    (symbol s ⬝ φ ⬝ ψ).interpret I ρ m ↔
      ∃ a b p, φ.interpret I ρ a ∧ I.evalApp (c s) a p ∧ ψ.interpret I ρ b ∧ I.evalApp p b m := by
  rw [interpret_app]
  constructor
  · rintro ⟨p, b, hp, hb, hpb⟩
    obtain ⟨a, ha, hap⟩ := (ap1 h ρ s φ p).mp hp
    exact ⟨a, b, p, ha, hap, hb, hpb⟩
  · rintro ⟨a, b, p, ha, hap, hb, hpb⟩
    exact ⟨p, b, (ap1 h ρ s φ p).mpr ⟨a, ha, hap⟩, hb, hpb⟩

/-- `X ∈ φ`, as KORE's `\in`: `⌈X ∧ φ⌉`. -/
def memP (x : EVar) (φ : Pattern 𝕊) : Pattern 𝕊 := ⌈evar x ⋀ φ⌉

/-- **The cut at a position under one application**: `∃X. (s(X) ∧ X ∈ φ)` is `s(φ)`, in every
interpretation, whatever the number of elements of φ. φ does not hold X. -/
theorem cut_exact (h : SymOK I c) (ρ : Valuation M) (s : 𝕊) (x : EVar) (φ : Pattern 𝕊)
    (hφ : ∀ a b, φ.interpret I ⟨Function.update ρ.evalEvar x a, ρ.evalSvar⟩ b ↔ φ.interpret I ρ b)
    (m : M) :
    (∃∃ x ((symbol s ⬝ evar x) ⋀ memP x φ)).interpret I ρ m ↔ (symbol s ⬝ φ).interpret I ρ m := by
  rw [interpret_exists, ap1 h]
  constructor
  · rintro ⟨a, ha⟩
    rw [interpret_conj, ap1 h] at ha
    obtain ⟨⟨b, hb, hab⟩, hmem⟩ := ha
    unfold memP at hmem
    rw [ceil_iff h] at hmem
    obtain ⟨b', hb'⟩ := hmem
    rw [interpret_conj] at hb'
    have e1 : b = Function.update ρ.evalEvar x a x := hb
    have e2 : b' = Function.update ρ.evalEvar x a x := hb'.1
    have e3 : b' = b := e2.trans e1.symm
    refine ⟨b, ?_, hab⟩
    rw [← e3]
    exact (hφ a b').mp hb'.2
  · rintro ⟨b, hb, hab⟩
    refine ⟨b, ?_⟩
    have e : Function.update ρ.evalEvar x b x = b := by simp
    rw [interpret_conj, ap1 h]
    refine ⟨⟨b, e.symm, hab⟩, ?_⟩
    unfold memP
    rw [ceil_iff h]
    refine ⟨b, ?_⟩
    rw [interpret_conj]
    exact ⟨e.symm, (hφ b b).mpr hb⟩

end generic

/-! ## D. A key with two elements

`f(Y)` has the two elements 1 and 2 of Int. `==Int` is equality at every element of Int (one
element of Bool, `true` exactly where the two are the same), so its `functional` sentence and
`((K1 ==Int K2) = true) = (K1 = K2)` hold. `L` is injective. -/
namespace D

inductive Sg | defined | f | L | eq | tru
instance : HasDefined Sg := ⟨.defined⟩

inductive El | tt | ff | n1 | n2 | l1 | l2 | q1 | q2 | cdef | cf | cL | ceq
  deriving DecidableEq

def c : Sg → El
  | .defined => .cdef | .f => .cf | .L => .cL | .eq => .ceq | .tru => .tt

def IsInt (a : El) : Prop := a = .n1 ∨ a = .n2

def app : El → El → El → Prop
  | .cdef, _, _ => True
  | .cf, _, m => m = .n1 ∨ m = .n2
  | .cL, .n1, m => m = .l1
  | .cL, .n2, m => m = .l2
  | .ceq, .n1, m => m = .q1
  | .ceq, .n2, m => m = .q2
  | .q1, b, m => IsInt b ∧ m = (if b = .n1 then .tt else .ff)
  | .q2, b, m => IsInt b ∧ m = (if b = .n2 then .tt else .ff)
  | _, _, _ => False

def I : Interpretation Sg El := ⟨fun s m => m = c s, app⟩

theorem ok : SymOK I c := ⟨fun _ _ => Iff.rfl, fun _ _ => trivial⟩

def x : EVar := ⟨0⟩
def y : EVar := ⟨1⟩

/-- `f(Y)` -/
def F : Pattern Sg := symbol .f ⬝ evar y
/-- the text's left side: `L[f(Y)]` -/
def textL : Pattern Sg := symbol .L ⬝ F
/-- the cut with `\in`: `L[X] ∧ X ∈ f(Y)` -/
def memL : Pattern Sg := (symbol .L ⬝ evar x) ⋀ memP x F
/-- the cut with the hooked equality: `L[X] ∧ ((X ==Int f(Y)) = true)` -/
def hookL : Pattern Sg := (symbol .L ⬝ evar x) ⋀ ((symbol .eq ⬝ evar x ⬝ F) ≡ symbol .tru)

theorem F_iff (ρ : Valuation El) (m : El) : F.interpret I ρ m ↔ (m = .n1 ∨ m = .n2) := by
  unfold F; rw [ap1 ok]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨_, rfl, h⟩⟩

/-- The text's left side has the two elements `L[1]` and `L[2]`. -/
theorem text_iff (ρ : Valuation El) (m : El) : textL.interpret I ρ m ↔ (m = .l1 ∨ m = .l2) := by
  unfold textL; rw [ap1 ok]
  constructor
  · rintro ⟨b, hb, hab⟩
    rcases (F_iff ρ b).mp hb with rfl | rfl
    · exact .inl hab
    · exact .inr hab
  · rintro (rfl | rfl)
    · exact ⟨.n1, (F_iff ρ _).mpr (.inl rfl), rfl⟩
    · exact ⟨.n2, (F_iff ρ _).mpr (.inr rfl), rfl⟩

/-- **The `\in` cut is the text's left side**, at every valuation. -/
theorem mem_exact (ρ : Valuation El) (m : El) :
    (∃∃ x memL).interpret I ρ m ↔ textL.interpret I ρ m :=
  cut_exact ok ρ .L x F (fun a b => by rw [F_iff, F_iff]) m

/-- `==Int` is equality at every pair of elements of Int. -/
theorem eq_graph (a b : El) (ha : IsInt a) (hb : IsInt b) :
    ∃ p, app .ceq a p ∧ ∀ m, app p b m ↔ m = (if a = b then .tt else .ff) := by
  rcases ha with rfl | rfl
  · exact ⟨.q1, rfl, fun m => ⟨fun h => by rw [h.2]; rcases hb with rfl | rfl <;> rfl,
      fun h => ⟨hb, by rw [h]; rcases hb with rfl | rfl <;> rfl⟩⟩⟩
  · exact ⟨.q2, rfl, fun m => ⟨fun h => by rw [h.2]; rcases hb with rfl | rfl <;> rfl,
      fun h => ⟨hb, by rw [h]; rcases hb with rfl | rfl <;> rfl⟩⟩⟩

/-- `L` is injective on Int. -/
theorem L_injective (a b m : El) (ha : IsInt a) (hb : IsInt b) (h1 : app .cL a m) (h2 : app .cL b m) :
    a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    first | rfl | (have h1' : m = _ := h1; have h2' : m = _ := h2; exact absurd (h1'.symm.trans h2') (by decide))

/-- **The hooked cut is empty** at every valuation: whatever X is, `X ==Int f(Y)` is not `{true}`. -/
theorem hook_empty (ρ : Valuation El) (m : El) : ¬ hookL.interpret I ρ m := by
  unfold hookL; rw [interpret_conj]
  rintro ⟨-, heq⟩
  rw [equal_iff ok] at heq
  obtain ⟨a, b, p, ha, hap, -, -⟩ := (ap2 ok ρ .eq (evar x) F .tt).mp ((heq .tt).mpr rfl)
  have ha' : a = ρ.evalEvar x := ha
  have hff : (symbol .eq ⬝ evar x ⬝ F).interpret I ρ .ff := by
    rw [ap2 ok]
    cases a with
    | n1 => exact ⟨.n1, .n2, .q1, ha, rfl, (F_iff ρ .n2).mpr (.inr rfl), .inr rfl, rfl⟩
    | n2 => exact ⟨.n2, .n1, .q2, ha, rfl, (F_iff ρ .n1).mpr (.inl rfl), .inl rfl, rfl⟩
    | _ => exact absurd hap (fun h => h)
  have : El.ff = El.tt := (heq .ff).mp hff
  exact absurd this (by decide)

/-- So the union over X of the hooked cut is empty, and the text's left side is not. -/
theorem hook_exists_empty (ρ : Valuation El) (m : El) : ¬ (∃∃ x hookL).interpret I ρ m := by
  rw [interpret_exists]
  rintro ⟨a, ha⟩
  exact hook_empty _ m ha

theorem text_nonempty (ρ : Valuation El) : textL.interpret I ρ .l1 := (text_iff ρ .l1).mpr (.inl rfl)

end D

end KeyMemML

namespace KCore

namespace KeyMemTest

open GroundTerm
open Faithful.UndefRhsWitness (kIds cellSorts cellCtors cellSubsorts)

/-! ## What `Holds` says of `\in`, `\equals … true` and a conjunction -/

theorem holds_mem_inv {c : Semantics} {n : Nat} {σ : Subst} {s : Srt} {t u : Term} {b : Bool}
    (h : Holds c n σ (.mem s t u) b) :
    ∃ r r', EvalTerm c σ t r ∧ EvalTerm c σ u r' ∧ b = (r.isSome && sameResult r r') := by
  cases h with
  | mem h1 h2 => exact ⟨_, _, h1, h2, rfl⟩

theorem holds_equals_inv {c : Semantics} {n : Nat} {σ : Subst} {s : Srt} {t u : Term} {b : Bool}
    (h : Holds c n σ (.equals s t u) b) :
    ∃ r r', EvalTerm c σ t r ∧ EvalTerm c σ u r' ∧ b = sameResult r r' := by
  cases h with
  | equals h1 h2 => exact ⟨_, _, h1, h2, rfl⟩

theorem holds_and_inv {c : Semantics} {n : Nat} {σ : Subst} {p q : Cond} {b : Bool}
    (h : Holds c n σ (.and p q) b) :
    ∃ b1 b2, Holds c n σ p b1 ∧ Holds c n σ q b2 ∧ b = (b1 && b2) := by
  cases h with
  | and h1 h2 => exact ⟨_, _, h1, h2, rfl⟩

/-- **`t ∈ u` holds exactly where t and u evaluate to the same value.** -/
theorem holds_mem_true {c : Semantics} {n : Nat} {σ : Subst} {s : Srt} {t u : Term} :
    Holds c n σ (.mem s t u) true ↔ ∃ v, EvalTerm c σ t (some v) ∧ EvalTerm c σ u (some v) := by
  constructor
  · intro h
    obtain ⟨r, r', h1, h2, hb⟩ := holds_mem_inv h
    cases r with
    | none => simp at hb
    | some v =>
      cases r' with
      | none => simp [sameResult] at hb
      | some w =>
        have hc : cmp v w = .eq := by simpa [sameResult] using hb.symm
        have := cmp_eq_iff.mp hc
        subst this
        exact ⟨v, h1, h2⟩
  · rintro ⟨v, h1, h2⟩
    have h := Holds.mem (n := n) (s := s) h1 h2
    have e : ((some v).isSome && sameResult (some v) (some v)) = true := by
      simp [sameResult, cmp_eq_iff.mpr rfl]
    rw [e] at h
    exact h

/-- **`t ∈ u` is false exactly where both have a result and t has no value, u has none, or the two
values differ.** A term without a result gives the condition no truth value. -/
theorem holds_mem_false {c : Semantics} {n : Nat} {σ : Subst} {s : Srt} {t u : Term} :
    Holds c n σ (.mem s t u) false ↔
      ∃ r r', EvalTerm c σ t r ∧ EvalTerm c σ u r' ∧ (r = none ∨ r' = none ∨ r ≠ r') := by
  constructor
  · intro h
    obtain ⟨r, r', h1, h2, hb⟩ := holds_mem_inv h
    refine ⟨r, r', h1, h2, ?_⟩
    cases r with
    | none => exact .inl rfl
    | some v =>
      cases r' with
      | none => exact .inr (.inl rfl)
      | some w =>
        refine .inr (.inr fun e => ?_)
        cases e
        simp [sameResult, cmp_eq_iff.mpr rfl] at hb
  · rintro ⟨r, r', h1, h2, hd⟩
    have h := Holds.mem (n := n) (s := s) h1 h2
    have e : (r.isSome && sameResult r r') = false := by
      cases r with
      | none => rfl
      | some v =>
        cases r' with
        | none => rfl
        | some w =>
          rcases hd with hd | hd | hd
          · cases hd
          · cases hd
          · have hne : cmp v w ≠ .eq := fun hc => hd (by rw [cmp_eq_iff.mp hc])
            simp [sameResult, hne]
    rw [e] at h
    exact h

/-- **`\equals(B, true)` holds exactly where B evaluates to `true`**: what `Step.rule`'s `hreq`
asks of a `requires`. -/
theorem holds_eqTrue {c : Semantics} {n : Nat} {σ : Subst} {B : Term} :
    Holds c n σ (.equals Srt.bool B (.dv Srt.bool (.bool true))) true ↔
      EvalTerm c σ B (some (bool true)) := by
  constructor
  · intro h
    obtain ⟨r, r', h1, h2, hb⟩ := holds_equals_inv h
    cases h2
    cases r with
    | none => simp [sameResult] at hb
    | some v =>
      have hc : cmp v (.dv Srt.bool (.bool true)) = .eq := by simpa [sameResult] using hb.symm
      have := cmp_eq_iff.mp hc
      subst this
      exact h1
  · intro h1
    have h := Holds.equals (n := n) (s := Srt.bool) h1 (EvalTerm.dv (c := c) (σ := σ) (s := Srt.bool) (lit := .bool true))
    have e : sameResult (some (bool true)) (some (.dv Srt.bool (.bool true))) = true := by
      simp [sameResult, bool, cmp_eq_iff.mpr rfl]
    rw [e] at h
    exact h

/-- A conjunction holds exactly where both conjuncts hold. -/
theorem holds_and_true {c : Semantics} {n : Nat} {σ : Subst} {p q : Cond} :
    Holds c n σ (.and p q) true ↔ Holds c n σ p true ∧ Holds c n σ q true := by
  constructor
  · intro h
    obtain ⟨b1, b2, h1, h2, hb⟩ := holds_and_inv h
    cases b1 <;> cases b2 <;> simp at hb
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact Holds.and h1 h2

/-- A conjunction is false exactly where **both** conjuncts have a truth value and one is false:
a conjunct without a truth value leaves the conjunction without one. -/
theorem holds_and_false {c : Semantics} {n : Nat} {σ : Subst} {p q : Cond} :
    Holds c n σ (.and p q) false ↔
      ∃ b1 b2, Holds c n σ p b1 ∧ Holds c n σ q b2 ∧ (b1 = false ∨ b2 = false) := by
  constructor
  · intro h
    obtain ⟨b1, b2, h1, h2, hb⟩ := holds_and_inv h
    refine ⟨b1, b2, h1, h2, ?_⟩
    cases b1 <;> cases b2 <;> simp at hb <;> simp
  · rintro ⟨b1, b2, h1, h2, hd⟩
    have h := Holds.and h1 h2
    have e : (b1 && b2) = false := by rcases hd with rfl | rfl <;> simp
    rw [e] at h
    exact h

/-- For a rule without a `requires`: it fails under σ exactly where its `pre` is false. -/
theorem ruleReqFails_iff {c : Semantics} {σ : Subst} {r : Rule} (hq : r.req = none) :
    RuleReqFails c σ r ↔ Holds c r.vars.length σ r.pre false :=
  ⟨fun h => by
    cases h with
    | intro ht _ _ => rw [hq] at ht; cases ht
    | pre h => exact h, .pre⟩

/-! ## The instance

`<k> X:Int ~> Rest </k> <generatedCounter> N </generatedCounter> => <k> Rest </k> <generatedCounter> N </generatedCounter>`
where X is the key of `N +Int 1`, and a rule of priority 200 on every configuration. -/

def lhsK : Term :=
  .app topLabel [.app kIds.label [.app kseq [.inj Srt.int Srt.kitem (.var 2), .var 0]], .app counterLabel [.var 1]]
def rhsK : Term := .app topLabel [.app kIds.label [.var 0], .app counterLabel [.var 1]]
/-- `N +Int 1` -/
def fN : Term := .app intAdd [.var 1, .dv Srt.int (.int 1)]

/-- The key by `\in`: `pre := X ∈ N +Int 1`. -/
def kcMem : Rule :=
  { vars := [Srt.k, Srt.int, Srt.int], lhs := lhsK, req := none, rhs := rhsK, ens := none, prio := 50,
    pre := .mem Srt.int (.var 2) fN }

/-- The key by the hooked equality: `requires X ==Int N +Int 1`. -/
def kcHook : Rule :=
  { vars := [Srt.k, Srt.int, Srt.int], lhs := lhsK, req := some (.app intEq [.var 2, fN]), rhs := rhsK,
    ens := none, prio := 50 }

/-- `<k> K </k> <generatedCounter> N </generatedCounter> => <k> K </k> <generatedCounter> 7 </generatedCounter>` -/
def r200 : Rule :=
  { vars := [Srt.k, Srt.int], lhs := .app topLabel [.app kIds.label [.var 0], .app counterLabel [.var 1]],
    req := none, rhs := .app topLabel [.app kIds.label [.var 0], .app counterLabel [.dv Srt.int (.int 7)]],
    ens := none, prio := 200 }

def base : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

def cM : Semantics := { base with rules := [kcMem, r200] }
def cH : Semantics := { base with rules := [kcHook, r200] }

/-- The rules of both semantics are sorted (`condOK` and `Cond.bound` of `\in`). -/
theorem sortedM : cM.rules.all cM.ruleSorted = true := by decide +kernel
theorem sortedH : cH.rules.all cH.ruleSorted = true := by decide +kernel
theorem litBool : cM.litSort Srt.bool = true := by decide +kernel

/-- `<k> x ~> . </k> <generatedCounter> n </generatedCounter>`. -/
def cfgK (x n : Int) : GroundTerm :=
  .ctor topLabel [.ctor kIds.label [.ctor kseq [.inj Srt.int Srt.kitem (int x), .ctor dotk []]], .ctor counterLabel [int n]]
/-- `<k> . </k> <generatedCounter> n </generatedCounter>`. -/
def cfg0 (n : Int) : GroundTerm :=
  .ctor topLabel [.ctor kIds.label [.ctor dotk []], .ctor counterLabel [int n]]
/-- `<k> x ~> . </k> <generatedCounter> 7 </generatedCounter>`. -/
abbrev cfg7 (x : Int) : GroundTerm := cfgK x 7

def σA : Subst := [(0, .ctor dotk []), (1, int 0), (2, int 1)]

theorem hσA (d : Semantics) (hk : d.sortOf (.ctor dotk []) = some Srt.k)
    (hi : ∀ i, d.sortOf (int i) = some Srt.int) : d.WellSorted [Srt.k, Srt.int, Srt.int] σA := by
  intro i s h
  match i, h with
  | 0, h => cases h; exact ⟨_, rfl, hk⟩
  | 1, h => cases h; exact ⟨_, rfl, hi 0⟩
  | 2, h => cases h; exact ⟨_, rfl, hi 1⟩

theorem sortInt (d : Semantics) (i : Int) : d.sortOf (int i) = some Srt.int := sortOf_int i

theorem matchA (d : Semantics) (hc1 : d.isCtor topLabel = true) (hc2 : d.isCtor kIds.label = true)
    (hc3 : d.isCtor counterLabel = true) (hc4 : d.isCtor kseq = true) : PatVal d σA lhsK (cfgK 1 0) :=
  .ctor hc1 (.cons (.ctor hc2 (.cons (.ctor hc4 (.cons (show PatVal d σA (.inj Srt.int Srt.kitem (.var 2)) (injNormal Srt.int Srt.kitem (int 1)) from .inj (.var rfl)) (.cons (.var rfl) .nil))) .nil))
    (.cons (.ctor hc3 (.cons (.var rfl) .nil)) .nil))

/-- `N +Int 1` under a σ that gives N the value n. -/
theorem evalF (d : Semantics) (hc : d.isCtor intAdd = false) {σ : Subst} {n : Int}
    (h1 : σ.lookup 1 = some (int n)) : EvalTerm d σ fN (some (int (n + 1))) := by
  refine EvalTerm.hook hc (by decide +kernel) (.cons .var (.cons .dv .nil)) ?_ ?_
  · intro vs h; rw [h1] at h; cases h; rfl
  · intro h; rw [h1] at h; cases h

theorem evalRhsA (d : Semantics) (hc1 : d.isCtor topLabel = true) (hc2 : d.isCtor kIds.label = true)
    (hc3 : d.isCtor counterLabel = true) : EvalTerm d σA rhsK (some (cfg0 0)) :=
  .ctor hc1 (.cons (.ctor hc2 (.cons (.var (i := 0)) .nil)) (.cons (.ctor hc3 (.cons (.var (i := 1)) .nil)) .nil))

theorem sortA : cM.sortOf (cfgK 1 0) = some topCellSort := by decide +kernel
theorem sortA' : cM.sortOf (cfg0 0) = some topCellSort := by decide +kernel
theorem sortB : cM.sortOf (cfgK 5 0) = some topCellSort := by decide +kernel
theorem sortB7 : cM.sortOf (cfgK 5 7) = some topCellSort := by decide +kernel
theorem sortHA : cH.sortOf (cfgK 1 0) = some topCellSort := by decide +kernel
theorem sortHA' : cH.sortOf (cfg0 0) = some topCellSort := by decide +kernel

/-- **`<k> 1 ~> . </k> 0` steps by the `\in` rule**: 1 is the value of `0 +Int 1`. -/
theorem stepM_A : Step cM ⟨cfgK 1 0, sortA⟩ ⟨cfg0 0, sortA'⟩ :=
  .rule kcMem (by simp [cM]) σA (hσA cM (by decide +kernel) (sortInt cM))
    (matchA cM (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (fun t h => by cases h)
    (holds_mem_true.mpr ⟨int 1, .var (i := 2), evalF cM (by decide +kernel) (n := 0) rfl⟩)
    (evalRhsA cM (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (fun t h => by cases h) .top
    (fun r' h hlt => by
      simp only [cM, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> exact absurd hlt (by decide))

/-- **The same step by the hooked rule.** -/
theorem stepH_A : Step cH ⟨cfgK 1 0, sortHA⟩ ⟨cfg0 0, sortHA'⟩ :=
  .rule kcHook (by simp [cH]) σA (hσA cH (by decide +kernel) (sortInt cH))
    (matchA cH (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (fun t h => by
      cases h
      refine EvalTerm.hook (by decide +kernel) (by decide +kernel)
        (.cons (.var (i := 2)) (.cons (evalF cH (by decide +kernel) (n := 0) rfl) .nil)) ?_ ?_
      · intro vs h; cases h; rfl
      · intro h; cases h)
    .top
    (evalRhsA cH (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (fun t h => by cases h) .top
    (fun r' h hlt => by
      simp only [cH, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> exact absurd hlt (by decide))

theorem patVal_inj_inv {d : Semantics} {σ : Subst} {a b : Srt} {p : Term} {v : GroundTerm}
    (h : PatVal d σ (.inj a b p) v) : ∃ w, PatVal d σ p w ∧ v = injNormal a b w := by
  cases h with
  | inj h => exact ⟨_, h, rfl⟩

theorem patVal_var_inv {d : Semantics} {σ : Subst} {i : Nat} {v : GroundTerm}
    (h : PatVal d σ (.var i) v) : σ.lookup i = some v := by
  cases h with
  | var h => exact h

theorem patVal_ctor_inv {d : Semantics} {σ : Subst} {f : Sym} {ps : List Term} {v : GroundTerm}
    (hc : d.isCtor f = true) (hph : patternHooks.contains f = false) (h : PatVal d σ (.app f ps) v) :
    ∃ vs, v = .ctor f vs ∧ PatVals d σ ps vs := by
  cases h with
  | ctor _ hs => exact ⟨_, rfl, hs⟩
  | hook hp _ _ => rw [hph] at hp; cases hp
  | coll hc' _ _ _ => rw [hc] at hc'; cases hc'
  | ovl hc' _ _ _ => rw [hc] at hc'; cases hc'

theorem shapesM : cM.shapesOK = true := by decide +kernel

/-- What a match of the left side at `<k> x ~> . </k> n` gives X and N. -/
theorem match_inv {σ : Subst} {x n : Int} (hσ : cM.WellSortedAt kcMem.vars kcMem.leftVars σ)
    (hm : PatVal cM σ lhsK (cfgK x n)) : σ.lookup 2 = some (int x) ∧ σ.lookup 1 = some (int n) := by
  obtain ⟨vs, hv, hs⟩ := patVal_ctor_inv (by decide +kernel) (by decide +kernel) hm
  cases hv
  cases hs with
  | cons hk hs =>
    cases hs with
    | cons hcn _ =>
      obtain ⟨vs, hv, hs⟩ := patVal_ctor_inv (by decide +kernel) (by decide +kernel) hk
      cases hv
      cases hs with
      | cons hq _ =>
        obtain ⟨vs, hv, hs⟩ := patVal_ctor_inv (by decide +kernel) (by decide +kernel) hq
        cases hv
        cases hs with
        | cons hi _ =>
          obtain ⟨w, hw, hv⟩ := patVal_inj_inv hi
          have hl := patVal_var_inv hw
          obtain ⟨w', hl', hsw⟩ := hσ 2 (by decide +kernel) Srt.int rfl
          rw [hl] at hl'; cases hl'
          obtain ⟨i, rfl⟩ := shape_int shapesM hsw
          have hx : x = i := by simpa [injNormal, int] using hv
          subst hx
          obtain ⟨vs, hv, hs⟩ := patVal_ctor_inv (by decide +kernel) (by decide +kernel) hcn
          cases hv
          cases hs with
          | cons hn _ => exact ⟨hl, patVal_var_inv hn⟩

/-- **The `\in` rule does not apply at `<k> 5 ~> . </k> 0`**: under every match the key is 5 and
`0 +Int 1` evaluates to 1, so `pre` is false. -/
theorem notAppliesM_B : NotApplies cM kcMem (cfgK 5 0) := by
  intro σ hσ hm
  obtain ⟨h2, h1⟩ := match_inv hσ hm
  refine (ruleReqFails_iff rfl).mpr (holds_mem_false.mpr ⟨σ.lookup 2, some (int 1), .var, ?_, ?_⟩)
  · exact evalF cM (by decide +kernel) (n := 0) h1
  · rw [h2]; exact .inr (.inr (by decide))

/-- **So the rule of priority 200 is not blocked there**, and gives the step. -/
theorem stepM_B : Step cM ⟨cfgK 5 0, sortB⟩ ⟨cfgK 5 7, sortB7⟩ :=
  .rule r200 (by simp [cM]) [(0, .ctor kseq [.inj Srt.int Srt.kitem (int 5), .ctor dotk []]), (1, int 0)]
    (by
      intro i s h
      match i, h with
      | 0, h => cases h; exact ⟨_, rfl, by decide +kernel⟩
      | 1, h => cases h; exact ⟨_, rfl, sortInt cM 0⟩)
    (.ctor (by decide +kernel) (.cons (.ctor (by decide +kernel) (.cons (.var rfl) .nil))
      (.cons (.ctor (by decide +kernel) (.cons (.var rfl) .nil)) .nil)))
    (fun t h => by cases h) .top
    (.ctor (by decide +kernel) (.cons (.ctor (by decide +kernel) (.cons (.var (i := 0)) .nil))
      (.cons (.ctor (by decide +kernel) (.cons .dv .nil)) .nil)))
    (fun t h => by cases h) .top
    (fun r' h hlt => by
      simp only [cM, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact notAppliesM_B
      · exact absurd hlt (by decide))

end KeyMemTest

end KCore

#print axioms KeyMemML.cut_exact
#print axioms KeyMemML.D.mem_exact
#print axioms KeyMemML.D.text_iff
#print axioms KeyMemML.D.eq_graph
#print axioms KeyMemML.D.L_injective
#print axioms KeyMemML.D.hook_empty
#print axioms KeyMemML.D.hook_exists_empty
#print axioms KCore.KeyMemTest.holds_mem_true
#print axioms KCore.KeyMemTest.holds_mem_false
#print axioms KCore.KeyMemTest.holds_eqTrue
#print axioms KCore.KeyMemTest.holds_and_true
#print axioms KCore.KeyMemTest.holds_and_false
#print axioms KCore.KeyMemTest.ruleReqFails_iff
#print axioms KCore.KeyMemTest.sortedM
#print axioms KCore.KeyMemTest.sortedH
#print axioms KCore.KeyMemTest.stepM_A
#print axioms KCore.KeyMemTest.stepH_A
#print axioms KCore.KeyMemTest.notAppliesM_B
#print axioms KCore.KeyMemTest.stepM_B
