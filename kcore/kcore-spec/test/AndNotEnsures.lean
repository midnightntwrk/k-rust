/-
  On an equation's right side, `t #And u` of two terms is the intersection of the two sets, and the
  sentence `h(X) = t ∧ ((t ==Int u) = true)` (t with the `ensures` `t ==Int u`) is not what the text
  states. Run from the package root: `lake env lean -j1 test/AndNotEnsures.lean`.

  The fixture `test/constructs/fixtures/e3-ml-eq-rhs-and-term` (K 7.1.337 kompile) writes
  `rule h(X) => f(X) #And g(X)` (kore.txt `//@ 341`) as
  `\equals{SortInt{},R}(Lblh{}(X0:SortInt{}), \and{SortInt{}}(\and{SortInt{}}(Lblf{}(VarX:SortInt{}),
  Lblg{}(VarX:SortInt{})), \top{SortInt{}}()))`.

  Two interpretations of applicative matching logic (`ML.Interpretation`). Sorts are left out: a
  sorted variable is a hypothesis on the valuation (`IsInt`).
  - `A`, the text `f(X) => f(X)`, `g(X) => 1`, `h(X) => f(X) #And g(X)` (f open at every point): Int
    is `{0, 1, 2}`, `==Int` the equality at every pair of elements (`eq_graph`, so the text's
    sentences `((K1 ==Int K2) = true) = (K1 = K2)` and their `false` companions hold), `f(a) = {1, 2}`,
    `g(a) = {1}`, `h(a) = {1}`. The text's three sentences hold (`text_holds`); the sentence with the
    `ensures` is false at every valuation (`clause_fails`): its right side is
    `{1, 2} ∧ ({true, false} = {true})`, the empty set. `not_ensures` states both.
  - `B`, the fixture's own text, every conjunct with one element, and the hook's graph stated at the
    value `0` only: Int has the value `0` and one more element `e`, `0 -Int e = e` and
    `e ==Int e = false`. The sentences hold (`text_holds`, `eq_functional`) and give `h(e) = e`
    (`text_value`), and the sentence with the `ensures` is false at `e` (`clause_fails`). `B` is no
    model of the fixture's full text, whose sentence `((K1 ==Int K2) = true) = (K1 = K2)` it falsifies
    at `e`: the `ensures` reading also rests on that sentence (`needs_eq_int`).
-/
import MatchingLogic

set_option autoImplicit false

open ML ML.Pattern

namespace AndNotEnsures
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

end generic

def x : EVar := ⟨0⟩

/-! ## A. The hook is equality at every element of Int; a conjunct has two elements.

`rule f(X) => f(X)` (or any text that leaves `f` open at a point), `g(X) => 1`,
`h(X) => f(X) #And g(X)`. Int is `{0, 1, 2}`, every element a value's, `==Int` their equality.
`f(a) = {1, 2}`: no sentence says `f(a)` has at most one element. -/
namespace A

inductive Sg | defined | f | g | h | eq | zero | one | two | tru | fls
instance : HasDefined Sg := ⟨.defined⟩

inductive El | z | n1 | n2 | tt | ff | cdef | cf | cg | ch | ceq | eqz | eq1 | eq2
  deriving DecidableEq

def c : Sg → El
  | .defined => .cdef | .f => .cf | .g => .cg | .h => .ch | .eq => .ceq
  | .zero => .z | .one => .n1 | .two => .n2 | .tru => .tt | .fls => .ff

def IsInt (a : El) : Prop := a = .z ∨ a = .n1 ∨ a = .n2

def app : El → El → El → Prop
  | .cdef, _, _ => True
  | .cf, _, m => m = .n1 ∨ m = .n2
  | .cg, _, m => m = .n1
  | .ch, _, m => m = .n1
  | .ceq, .z, m => m = .eqz
  | .ceq, .n1, m => m = .eq1
  | .ceq, .n2, m => m = .eq2
  | .eqz, b, m => IsInt b ∧ m = (if b = .z then .tt else .ff)
  | .eq1, b, m => IsInt b ∧ m = (if b = .n1 then .tt else .ff)
  | .eq2, b, m => IsInt b ∧ m = (if b = .n2 then .tt else .ff)
  | _, _, _ => False

def I : Interpretation Sg El := ⟨fun s m => m = c s, app⟩

theorem ok : SymOK I c := ⟨fun _ _ => Iff.rfl, fun _ _ => trivial⟩

def F : Pattern Sg := symbol .f ⬝ evar x
def G : Pattern Sg := symbol .g ⬝ evar x
def H : Pattern Sg := symbol .h ⬝ evar x
def E : Pattern Sg := symbol .eq ⬝ F ⬝ G

/-- `f(X) = f(X)` -/
def tF : Pattern Sg := F ≡ F
/-- `g(X) = 1` -/
def tG : Pattern Sg := G ≡ symbol .one
/-- the text's `h(X) = f(X) ∧ g(X)` -/
def tH : Pattern Sg := H ≡ (F ⋀ G)
/-- the clause's sentence -/
def cH : Pattern Sg := H ≡ (F ⋀ (E ≡ symbol .tru))

theorem F_iff (ρ : Valuation El) (m : El) : F.interpret I ρ m ↔ (m = .n1 ∨ m = .n2) := by
  unfold F; rw [ap1 ok]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨_, rfl, h⟩⟩
theorem G_iff (ρ : Valuation El) (m : El) : G.interpret I ρ m ↔ m = .n1 := by
  unfold G; rw [ap1 ok]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨_, rfl, h⟩⟩
theorem H_iff (ρ : Valuation El) (m : El) : H.interpret I ρ m ↔ m = .n1 := by
  unfold H; rw [ap1 ok]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨_, rfl, h⟩⟩

/-- The text's sentences hold at every valuation. -/
theorem text_holds (ρ : Valuation El) (m : El) :
    tF.interpret I ρ m ∧ tG.interpret I ρ m ∧ tH.interpret I ρ m := by
  refine ⟨?_, ?_, ?_⟩
  · unfold tF; rw [equal_iff ok]; intro b; exact Iff.rfl
  · unfold tG; rw [equal_iff ok]; intro b; rw [G_iff]; exact Iff.rfl
  · unfold tH; rw [equal_iff ok]; intro b; rw [interpret_conj, H_iff, F_iff, G_iff]
    exact ⟨fun h => ⟨.inl h, h⟩, fun h => h.2⟩

/-- `==Int` is equality at every pair of elements of Int: one element of Bool, `true` exactly where
the two are the same. -/
theorem eq_graph (a b : El) (ha : IsInt a) (hb : IsInt b) :
    ∃ p, app .ceq a p ∧ ∀ m, app p b m ↔ m = (if a = b then .tt else .ff) := by
  rcases ha with rfl | rfl | rfl
  · exact ⟨.eqz, rfl, fun m => ⟨fun h => by rw [h.2]; rcases hb with rfl | rfl | rfl <;> rfl,
      fun h => ⟨hb, by rw [h]; rcases hb with rfl | rfl | rfl <;> rfl⟩⟩⟩
  · exact ⟨.eq1, rfl, fun m => ⟨fun h => by rw [h.2]; rcases hb with rfl | rfl | rfl <;> rfl,
      fun h => ⟨hb, by rw [h]; rcases hb with rfl | rfl | rfl <;> rfl⟩⟩⟩
  · exact ⟨.eq2, rfl, fun m => ⟨fun h => by rw [h.2]; rcases hb with rfl | rfl | rfl <;> rfl,
      fun h => ⟨hb, by rw [h]; rcases hb with rfl | rfl | rfl <;> rfl⟩⟩⟩

/-- The clause's sentence is false at every valuation: the text gives `h = 1`, the clause nothing. -/
theorem clause_fails (ρ : Valuation El) : ¬ cH.interpret I ρ .n1 := by
  unfold cH; rw [equal_iff ok]
  intro hall
  have h1 := (hall .n1).mp ((H_iff ρ .n1).mpr rfl)
  rw [interpret_conj, equal_iff ok] at h1
  have hE : E.interpret I ρ .ff := by
    unfold E; rw [ap2 ok]
    exact ⟨.n2, .n1, .eq2, (F_iff ρ .n2).mpr (.inr rfl), rfl, (G_iff ρ .n1).mpr rfl,
      .inr (.inl rfl), rfl⟩
  have : El.ff = El.tt := (h1.2 .ff).mp hE
  exact absurd this (by decide)

def atZ : Valuation El := ⟨fun _ => .z, fun _ _ => False⟩

/-- The text's sentences hold at every valuation, and the sentence with the `ensures` is false at a
valuation of `X` in Int. -/
theorem not_ensures :
    (∀ ρ m, tF.interpret I ρ m ∧ tG.interpret I ρ m ∧ tH.interpret I ρ m) ∧
    IsInt (atZ.evalEvar x) ∧ ¬ cH.interpret I atZ .n1 :=
  ⟨text_holds, .inl rfl, clause_fails atZ⟩

end A

/-! ## B. Every conjunct has one element; the hook's graph is stated at the values only.

NOT a model of the fixture's full text: that text also holds `((K1 ==Int K2) = true) = (K1 = K2)`
(`INT-KORE.eq-int-true-left`, a `[simplification]` sentence), which this interpretation falsifies at `e`.
It is a model of the sentences below, which are what `Γ` holds about the hook.
The fixture's three equations: `f(X) => X`, `g(X) => 0 -Int X`, `h(X) => f(X) #And g(X)`. Int has the value
`z` (0) and one more element `e`, no value's. `0 -Int e = e` and `e ==Int e = false`: one element each,
as the `functional` sentences ask; no sentence says what they are at `e`. -/
namespace B

inductive Sg | defined | f | g | h | eq | sub | zero | tru | fls
instance : HasDefined Sg := ⟨.defined⟩

inductive El | z | e | tt | ff | cdef | cf | cg | ch | ceq | csub | eqz | eqe | subz | sube
  deriving DecidableEq

def c : Sg → El
  | .defined => .cdef | .f => .cf | .g => .cg | .h => .ch | .eq => .ceq | .sub => .csub
  | .zero => .z | .tru => .tt | .fls => .ff

def app : El → El → El → Prop
  | .cdef, _, _ => True
  | .cf, a, m => m = a
  | .cg, a, m => m = a
  | .ch, a, m => m = a
  | .csub, .z, m => m = .subz
  | .csub, .e, m => m = .sube
  | .subz, a, m => m = a
  | .sube, a, m => m = a
  | .ceq, .z, m => m = .eqz
  | .ceq, .e, m => m = .eqe
  | .eqz, .z, m => m = .tt
  | .eqz, .e, m => m = .ff
  | .eqe, .z, m => m = .ff
  | .eqe, .e, m => m = .ff
  | _, _, _ => False

def I : Interpretation Sg El := ⟨fun s m => m = c s, app⟩

theorem ok : SymOK I c := ⟨fun _ _ => Iff.rfl, fun _ _ => trivial⟩

def IsInt (a : El) : Prop := a = .z ∨ a = .e
def IsBool (a : El) : Prop := a = .tt ∨ a = .ff

def F : Pattern Sg := symbol .f ⬝ evar x
def G : Pattern Sg := symbol .g ⬝ evar x
def H : Pattern Sg := symbol .h ⬝ evar x
/-- `f(X) ==Int g(X)` -/
def E : Pattern Sg := symbol .eq ⬝ F ⬝ G

/-- `f(X) = X` -/
def tF : Pattern Sg := F ≡ evar x
/-- `g(X) = 0 -Int X` -/
def tG : Pattern Sg := G ≡ (symbol .sub ⬝ symbol .zero ⬝ evar x)
/-- the text's `h(X) = f(X) ∧ g(X)` -/
def tH : Pattern Sg := H ≡ (F ⋀ G)
/-- the graphs at the value: `0 ==Int 0 = true`, `0 -Int 0 = 0` -/
def dEq : Pattern Sg := (symbol .eq ⬝ symbol .zero ⬝ symbol .zero) ≡ symbol .tru
def dSub : Pattern Sg := (symbol .sub ⬝ symbol .zero ⬝ symbol .zero) ≡ symbol .zero
/-- the clause's sentence: `h(X) = f(X) ∧ ((f(X) ==Int g(X)) = true)` -/
def cH : Pattern Sg := H ≡ (F ⋀ (E ≡ symbol .tru))

theorem F_iff (ρ : Valuation El) (m : El) : F.interpret I ρ m ↔ m = ρ.evalEvar x := by
  unfold F; rw [ap1 ok]
  constructor
  · rintro ⟨b, hb, hab⟩; have : b = ρ.evalEvar x := hb; subst this; exact hab
  · intro h; exact ⟨_, rfl, h⟩
theorem G_iff (ρ : Valuation El) (m : El) : G.interpret I ρ m ↔ m = ρ.evalEvar x := by
  unfold G; rw [ap1 ok]
  constructor
  · rintro ⟨b, hb, hab⟩; have : b = ρ.evalEvar x := hb; subst this; exact hab
  · intro h; exact ⟨_, rfl, h⟩
theorem H_iff (ρ : Valuation El) (m : El) : H.interpret I ρ m ↔ m = ρ.evalEvar x := by
  unfold H; rw [ap1 ok]
  constructor
  · rintro ⟨b, hb, hab⟩; have : b = ρ.evalEvar x := hb; subst this; exact hab
  · intro h; exact ⟨_, rfl, h⟩

/-- The text's sentences hold at every valuation. -/
theorem text_holds (ρ : Valuation El) (m : El) :
    tF.interpret I ρ m ∧ tG.interpret I ρ m ∧ tH.interpret I ρ m ∧
    dEq.interpret I ρ m ∧ dSub.interpret I ρ m := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold tF; rw [equal_iff ok]; intro b; rw [F_iff]; exact Iff.rfl
  · unfold tG; rw [equal_iff ok]; intro b; rw [G_iff, ap2 ok]
    constructor
    · intro h; exact ⟨.z, ρ.evalEvar x, .subz, rfl, rfl, rfl, h⟩
    · rintro ⟨a, b', p, ha, hap, hb, hpb⟩
      have ha : a = .z := ha
      have hb : b' = ρ.evalEvar x := hb
      subst ha; subst hb
      have hp : p = .subz := hap
      subst hp; exact hpb
  · unfold tH; rw [equal_iff ok]; intro b; rw [interpret_conj, H_iff, F_iff, G_iff]
    exact ⟨fun h => ⟨h, h⟩, fun h => h.1⟩
  · unfold dEq; rw [equal_iff ok]; intro b; rw [ap2 ok]
    constructor
    · rintro ⟨a, b', p, ha, hap, hb, hpb⟩
      have ha : a = .z := ha
      have hb : b' = .z := hb
      subst ha; subst hb
      have hp : p = .eqz := hap
      subst hp; exact hpb
    · intro h; exact ⟨.z, .z, .eqz, rfl, rfl, rfl, h⟩
  · unfold dSub; rw [equal_iff ok]; intro b; rw [ap2 ok]
    constructor
    · rintro ⟨a, b', p, ha, hap, hb, hpb⟩
      have ha : a = .z := ha
      have hb : b' = .z := hb
      subst ha; subst hb
      have hp : p = .subz := hap
      subst hp; exact hpb
    · intro h; exact ⟨.z, .z, .subz, rfl, rfl, rfl, h⟩

/-- `functional`: at elements of Int, `==Int` is one element of Bool and `0 -Int _`, f, g, h one of Int. -/
theorem eq_functional (a b : El) (ha : IsInt a) (hb : IsInt b) :
    ∃ v, IsBool v ∧ ∃ p, app .ceq a p ∧ ∀ m, app p b m ↔ m = v := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact ⟨.tt, .inl rfl, .eqz, rfl, fun _ => Iff.rfl⟩
  · exact ⟨.ff, .inr rfl, .eqz, rfl, fun _ => Iff.rfl⟩
  · exact ⟨.ff, .inr rfl, .eqe, rfl, fun _ => Iff.rfl⟩
  · exact ⟨.ff, .inr rfl, .eqe, rfl, fun _ => Iff.rfl⟩

def atE : Valuation El := ⟨fun _ => .e, fun _ _ => False⟩

/-- The clause's sentence is false at the element `e` of Int. -/
theorem clause_fails : IsInt (atE.evalEvar x) ∧ ¬ cH.interpret I atE .e := by
  refine ⟨.inr rfl, ?_⟩
  unfold cH; rw [equal_iff ok]
  intro hall
  have h1 := (hall .e).mp ((H_iff atE .e).mpr rfl)
  rw [interpret_conj, equal_iff ok] at h1
  have hE : E.interpret I atE .ff := by
    unfold E; rw [ap2 ok]
    exact ⟨.e, .e, .eqe, (F_iff atE .e).mpr rfl, rfl, (G_iff atE .e).mpr rfl, rfl⟩
  have : El.ff = El.tt := (h1.2 .ff).mp hE
  exact absurd this (by decide)

/-- The text's own sentence gives `h(e) = e` there. -/
theorem text_value : ∀ m, H.interpret I atE m ↔ m = .e := fun m => H_iff atE m

/-- The sentences modelled hold, `e ==Int e` is `false` although `e = e` (so the text's sentence
`((K1 ==Int K2) = true) = (K1 = K2)` is false at `e`), the text gives `h(e) = e`, and the sentence
with the `ensures` is false at `e`. -/
theorem needs_eq_int :
    (∀ ρ m, tF.interpret I ρ m ∧ tG.interpret I ρ m ∧ tH.interpret I ρ m ∧
      dEq.interpret I ρ m ∧ dSub.interpret I ρ m) ∧
    app .ceq .e .eqe ∧ (∀ m, app .eqe .e m ↔ m = .ff) ∧
    (∀ m, H.interpret I atE m ↔ m = .e) ∧ ¬ cH.interpret I atE .e :=
  ⟨text_holds, rfl, fun _ => Iff.rfl, text_value, clause_fails.2⟩

end B

end AndNotEnsures

#print axioms AndNotEnsures.B.text_holds
#print axioms AndNotEnsures.B.clause_fails
#print axioms AndNotEnsures.B.eq_functional
#print axioms AndNotEnsures.A.text_holds
#print axioms AndNotEnsures.A.clause_fails
#print axioms AndNotEnsures.A.eq_graph
#print axioms AndNotEnsures.A.not_ensures
#print axioms AndNotEnsures.B.needs_eq_int
