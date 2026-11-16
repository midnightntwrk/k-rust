/-
  `\and{SortBool{}}` in the `requires` of an equation that an `[owise]` equation negates is an
  intersection, not the strict conjunction. Run from the package root:
  `lake env lean -j1 test/AndBoolNotStrict.lean`.

  The text is the fixture `test/constructs/fixtures/e3-ml-req-and-owise` (K 7.1.337 kompile):
  `rule f(X) => 1 requires g(X) #And hh(X)`, `rule f(X) => 2 [owise]`,
  `rule g(X) => g(X) requires X >Int 0`, `rule hh(X) => true`, with no `functional` sentence of
  `f`, `g` or `hh`. Its kore.txt writes the first equation's premise (`//@ 337`) as
  `\equals{SortBool{},R}(\and{SortBool{}}(Lblg{}(VarX), Lblhh{}(VarX)), \dv{SortBool{}}("true"))`
  and the `[owise]` equation's (`//@ 338`) as that premise negated, under `\exists` of the argument.

  An interpretation of applicative matching logic (`ML.Interpretation`) in which `g(a)` has the two
  elements `true` and `false`, `hh(a) = {true}` and `f(a) = {1}`:
  - the text's sentences hold (`text_holds`): `{true, false} ∩ {true} = {true}`, so the first
    equation gives `f = 1` and the `[owise]` one states nothing;
  - `==K` is the equality of K at every element (`eq_graph`) and the pairing is injective
    (`pair_graph`, `pair_injective`), so the failure below is no missing hooked-equality sentence;
  - the `[owise]` sentence written with the strict conjunction,
    `¬((seq(g(X), hh(X)) ==K seq(true, true)) = true) → f(X) = 2`, is false at every valuation
    (`owise_fails`): the hooked equality has the elements `true` and `false`, so its negated premise
    holds, and `f(X)` is 1.
  So a reading of `\and{SortBool{}}` as `⋀ ⌈Bᵢ = true⌉` in a negated equation premise states what
  the text does not. `seq(a, b)` is modelled as one injective binary symbol `pair`, standing for
  `kseq(inj{Bool,KItem}(a), kseq(inj{Bool,KItem}(b), dotk))`. Sorts are left out and `f`, `g`, `hh`
  ignore their argument, so the `\exists` of the argument in the `[owise]` premise is the premise
  itself, and `g(X) = g(X)` (`tG`) gives the text's `X >Int 0 → g(X) = g(X)`.
-/
import MatchingLogic

set_option autoImplicit false

open ML ML.Pattern

namespace AndBoolNotStrict

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

inductive Sg | defined | f | g | hh | eq | pair | one | two | tru | fls
instance : HasDefined Sg := ⟨.defined⟩

inductive El | tt | ff | n1 | n2 | ptt | ptf | pft | pff | pT | pF | qtt | qtf | qft | qff
  | cdef | cf | cg | ch | ceq | cpair
  deriving DecidableEq

def c : Sg → El
  | .defined => .cdef | .f => .cf | .g => .cg | .hh => .ch | .eq => .ceq | .pair => .cpair
  | .one => .n1 | .two => .n2 | .tru => .tt | .fls => .ff

/-- The elements of K: the four pairs of elements of Bool. -/
def IsK (a : El) : Prop := a = .ptt ∨ a = .ptf ∨ a = .pft ∨ a = .pff

def app : El → El → El → Prop
  | .cdef, _, _ => True
  | .cf, _, m => m = .n1
  | .cg, _, m => m = .tt ∨ m = .ff
  | .ch, _, m => m = .tt
  | .cpair, .tt, m => m = .pT
  | .cpair, .ff, m => m = .pF
  | .pT, .tt, m => m = .ptt
  | .pT, .ff, m => m = .ptf
  | .pF, .tt, m => m = .pft
  | .pF, .ff, m => m = .pff
  | .ceq, .ptt, m => m = .qtt
  | .ceq, .ptf, m => m = .qtf
  | .ceq, .pft, m => m = .qft
  | .ceq, .pff, m => m = .qff
  | .qtt, b, m => IsK b ∧ m = (if b = .ptt then .tt else .ff)
  | .qtf, b, m => IsK b ∧ m = (if b = .ptf then .tt else .ff)
  | .qft, b, m => IsK b ∧ m = (if b = .pft then .tt else .ff)
  | .qff, b, m => IsK b ∧ m = (if b = .pff then .tt else .ff)
  | _, _, _ => False

def I : Interpretation Sg El := ⟨fun s m => m = c s, app⟩

theorem ok : SymOK I c := ⟨fun _ _ => Iff.rfl, fun _ _ => trivial⟩

def F : Pattern Sg := symbol .f ⬝ evar x
def G : Pattern Sg := symbol .g ⬝ evar x
def Hh : Pattern Sg := symbol .hh ⬝ evar x

/-- the text's premise: `(g(X) ∧ hh(X)) = true` -/
def T : Pattern Sg := (G ⋀ Hh) ≡ symbol .tru
/-- the strict reading's premise: `(pair(g(X), hh(X)) ==K pair(true, true)) = true` -/
def Gc : Pattern Sg :=
  (symbol .eq ⬝ (symbol .pair ⬝ G ⬝ Hh) ⬝ (symbol .pair ⬝ symbol .tru ⬝ symbol .tru)) ≡ symbol .tru

/-- `g(X) = g(X)` -/
def tG : Pattern Sg := G ≡ G
/-- `hh(X) = true` -/
def tH : Pattern Sg := Hh ≡ symbol .tru
/-- the text's first equation: `(g(X) ∧ hh(X)) = true → f(X) = 1` -/
def t1 : Pattern Sg := T ⇒ (F ≡ symbol .one)
/-- the text's `[owise]` equation: `¬((g(X) ∧ hh(X)) = true) → f(X) = 2` -/
def t2 : Pattern Sg := ∼T ⇒ (F ≡ symbol .two)
/-- the `[owise]` equation under the strict reading:
`¬((pair(g(X), hh(X)) ==K pair(true, true)) = true) → f(X) = 2` -/
def c2 : Pattern Sg := ∼Gc ⇒ (F ≡ symbol .two)

theorem F_iff (ρ : Valuation El) (m : El) : F.interpret I ρ m ↔ m = .n1 := by
  unfold F; rw [ap1 ok]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨_, rfl, h⟩⟩
theorem G_iff (ρ : Valuation El) (m : El) : G.interpret I ρ m ↔ (m = .tt ∨ m = .ff) := by
  unfold G; rw [ap1 ok]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨_, rfl, h⟩⟩
theorem Hh_iff (ρ : Valuation El) (m : El) : Hh.interpret I ρ m ↔ m = .tt := by
  unfold Hh; rw [ap1 ok]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨_, rfl, h⟩⟩

/-- The text's premise holds at every valuation: the two conjuncts meet in `true` alone. -/
theorem T_holds (ρ : Valuation El) (m : El) : T.interpret I ρ m := by
  unfold T; rw [equal_iff ok]; intro b; rw [interpret_conj, G_iff, Hh_iff]
  exact ⟨fun h => h.2, fun h => ⟨.inl h, h⟩⟩

/-- The text's sentences hold at every valuation. -/
theorem text_holds (ρ : Valuation El) (m : El) :
    tG.interpret I ρ m ∧ tH.interpret I ρ m ∧ t1.interpret I ρ m ∧ t2.interpret I ρ m := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold tG; rw [equal_iff ok]; intro b; exact Iff.rfl
  · unfold tH; rw [equal_iff ok]; intro b; rw [Hh_iff]; exact Iff.rfl
  · unfold t1; rw [interpret_impl]; intro _
    rw [equal_iff ok]; intro b; rw [F_iff]; exact Iff.rfl
  · unfold t2; rw [interpret_impl, interpret_neg]; intro h; exact absurd (T_holds ρ m) h

/-- `==K` is equality at every pair of elements of K: one element of Bool, `true` exactly where the
two are the same. So `((K1 ==K K2) = true) = (K1 = K2)` and its `false` companion hold. -/
theorem eq_graph (a b : El) (ha : IsK a) (hb : IsK b) :
    ∃ p, app .ceq a p ∧ ∀ m, app p b m ↔ m = (if a = b then .tt else .ff) := by
  rcases ha with rfl | rfl | rfl | rfl
  · exact ⟨.qtt, rfl, fun m => ⟨fun h => by rw [h.2]; rcases hb with rfl | rfl | rfl | rfl <;> rfl,
      fun h => ⟨hb, by rw [h]; rcases hb with rfl | rfl | rfl | rfl <;> rfl⟩⟩⟩
  · exact ⟨.qtf, rfl, fun m => ⟨fun h => by rw [h.2]; rcases hb with rfl | rfl | rfl | rfl <;> rfl,
      fun h => ⟨hb, by rw [h]; rcases hb with rfl | rfl | rfl | rfl <;> rfl⟩⟩⟩
  · exact ⟨.qft, rfl, fun m => ⟨fun h => by rw [h.2]; rcases hb with rfl | rfl | rfl | rfl <;> rfl,
      fun h => ⟨hb, by rw [h]; rcases hb with rfl | rfl | rfl | rfl <;> rfl⟩⟩⟩
  · exact ⟨.qff, rfl, fun m => ⟨fun h => by rw [h.2]; rcases hb with rfl | rfl | rfl | rfl <;> rfl,
      fun h => ⟨hb, by rw [h]; rcases hb with rfl | rfl | rfl | rfl <;> rfl⟩⟩⟩

/-- `pair` at two elements of Bool: one element of K, and a different one for different arguments. -/
def pairOf : El → El → El
  | .tt, .tt => .ptt | .tt, .ff => .ptf | .ff, .tt => .pft | _, _ => .pff
def IsBool (a : El) : Prop := a = .tt ∨ a = .ff
theorem pair_graph (a b : El) (ha : IsBool a) (hb : IsBool b) :
    ∃ p, app .cpair a p ∧ ∀ m, app p b m ↔ m = pairOf a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact ⟨.pT, rfl, fun _ => Iff.rfl⟩
  · exact ⟨.pT, rfl, fun _ => Iff.rfl⟩
  · exact ⟨.pF, rfl, fun _ => Iff.rfl⟩
  · exact ⟨.pF, rfl, fun _ => Iff.rfl⟩
theorem pair_injective (a b a' b' : El) (ha : IsBool a) (hb : IsBool b) (ha' : IsBool a') (hb' : IsBool b')
    (h : pairOf a b = pairOf a' b') : a = a' ∧ b = b' := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases ha' with rfl | rfl <;>
    rcases hb' with rfl | rfl <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

/-- The `[owise]` equation under the strict reading is false at every valuation: its premise holds
(the hooked equality gives `false` for the element `pair(false, true)`), and `f(X)` is 1, not 2. -/
theorem owise_fails (ρ : Valuation El) (m : El) : ¬ c2.interpret I ρ m := by
  unfold c2; rw [interpret_impl]
  intro h
  have hG : (∼Gc).interpret I ρ m := by
    rw [interpret_neg]; unfold Gc; rw [equal_iff ok]
    intro hall
    have hE : (symbol .eq ⬝ (symbol .pair ⬝ G ⬝ Hh) ⬝ (symbol .pair ⬝ symbol .tru ⬝ symbol .tru)).interpret I ρ .ff := by
      rw [ap2 ok]
      refine ⟨.pft, .ptt, .qft, ?_, rfl, ?_, .inl rfl, rfl⟩
      · rw [ap2 ok]; exact ⟨.ff, .tt, .pF, (G_iff ρ .ff).mpr (.inr rfl), rfl, (Hh_iff ρ .tt).mpr rfl, rfl⟩
      · rw [ap2 ok]; exact ⟨.tt, .tt, .pT, rfl, rfl, rfl, rfl⟩
    have : El.ff = El.tt := (hall .ff).mp hE
    exact absurd this (by decide)
  have h2 := h hG
  rw [equal_iff ok] at h2
  have : El.n1 = El.n2 := (h2 .n1).mp ((F_iff ρ .n1).mpr rfl)
  exact absurd this (by decide)

/-- The text holds and the strict reading's `[owise]` sentence fails, at one valuation together. -/
theorem not_strict (ρ : Valuation El) (m : El) :
    (tG.interpret I ρ m ∧ tH.interpret I ρ m ∧ t1.interpret I ρ m ∧ t2.interpret I ρ m) ∧
      ¬ c2.interpret I ρ m :=
  ⟨text_holds ρ m, owise_fails ρ m⟩

end AndBoolNotStrict

#print axioms AndBoolNotStrict.text_holds
#print axioms AndBoolNotStrict.eq_graph
#print axioms AndBoolNotStrict.pair_graph
#print axioms AndBoolNotStrict.pair_injective
#print axioms AndBoolNotStrict.owise_fails
#print axioms AndBoolNotStrict.not_strict
