/-
  The extension of a model of the theory without the registry family (`Γown c D`,
  RegistryOwn.lean) by the elements the family speaks of: the carrier `M ⊕ Added`, the
  interpretation `extModel` and the embedding `Sum.inl`, with the three embedding clauses of
  `RegistryConservative` (`ext_embeds`).

  The added elements are: a detached sort constant; for each literal, an element of its `dv`
  symbol (a literal's `dv` symbol may be empty in the smaller model, and a value of a detached
  sort is that symbol applied to the sort's name); a value of a detached sort; a detached hooked
  symbol applied to fewer values than it has arguments.

  `extModel` keeps every symbol outside `D` on the old elements (a detached symbol holds of an old
  element only as a hooked symbol without arguments whose result is that element) and application between old
  elements, gives a detached sort's name its one new element and the sort its values, and gives
  a detached hooked symbol its graph (`hook`, and at a silent point `Semantics.fallback`) at the
  arguments that are elements of values. An old element is the element of a value of a sort outside
  `D` where that value's pattern denotes exactly it in the smaller model.

  That `extModel` satisfies the theory is not proved here.
-/
import KcoreSpec.RegistryOwn

set_option autoImplicit false

namespace KCore.Cons

open ML Faithful

/-- The elements added to a model of the smaller theory. -/
inductive Added where
  /-- the detached sort constant `n` (a KORE sort name, `SortX`) -/
  | srt (n : String)
  /-- an element of the symbol `dv l` -/
  | lit (l : String)
  /-- a value of a detached sort -/
  | val (v : GroundTerm)
  /-- a detached hooked symbol applied to the values `vs`, fewer than its arguments -/
  | hk (f : Sym) (vs : List GroundTerm)

/-- The extended carrier. -/
abbrev Ext (M : Type) : Type := M ⊕ Added

section
variable (c : Semantics) (D : KoreAML.Sym → Prop) {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M)

/-- A sort whose name is detached. Under `Detached` it is a registry sort. -/
def DSort (s : Srt) : Prop := D (.sort ("Sort" ++ c.sortName s))

/-- An interpreted hooked symbol whose name is detached. -/
def DHook (k : CtorSig) : Prop := k ∈ hookSigs ∧ D (.symbol (c.symName k.name))

/-- `x` is the element of the value `v`: the added element `val v` for a value of a detached sort;
for a value of another sort, the old element its pattern denotes exactly in `I`. -/
def ElemOf (v : GroundTerm) (x : Ext M) : Prop :=
  (∃ s, c.sortOf v = some s ∧ DSort c D s ∧ x = .inr (.val v)) ∨
  (∃ s m, c.sortOf v = some s ∧ ¬ DSort c D s ∧ x = .inl m ∧
    ∀ m', (den c v).interpret I KoreAML.val0 m' ↔ m' = m)

/-- `x` is the element of the result of the hooked symbol `k` at the values `vs`: of `hook`'s
value, and at a silent point where `hook` gives none, of the interpretation's (`fallback`). Where
neither gives a value there is no such element. -/
def ResOf (k : CtorSig) (vs : List GroundTerm) (x : Ext M) : Prop :=
  ∃ v, (hook k.name vs = some (some v) ∨
      (hook k.name vs = some none ∧ silent k.name vs = true ∧ c.fallback k.name vs = some v)) ∧
    ElemOf c D I v x

/-- What the hooked symbol `k` applied to the values `vs` denotes: the added element `hk` while
arguments are missing, the result's element once all are given. -/
def PartOf (k : CtorSig) (vs : List GroundTerm) (x : Ext M) : Prop :=
  if vs.length < k.args.length then x = .inr (.hk k.name vs) else ResOf c D I k vs x

/-- **The extended interpretation.** -/
def extModel : Interpretation KoreAML.Sym (Ext M) where
  evalSymb σ x := match x with
    | .inl m => (¬ D σ ∧ I.evalSymb σ m) ∨
        -- a detached hooked symbol without arguments whose result is a value of a sort outside `D`
        ∃ k, DHook c D k ∧ σ = .symbol (c.symName k.name) ∧ PartOf c D I k [] (.inl m)
    | .inr (.srt n) => D (.sort n) ∧ σ = .sort n
    | .inr (.lit l) => σ = .dv l
    | .inr n => ∃ k, DHook c D k ∧ σ = .symbol (c.symName k.name) ∧ PartOf c D I k [] (.inr n)
  evalApp a b x := match a, b with
    | .inl a, .inl b =>
      (match x with
        | .inl m => I.evalApp a b m
        | .inr n =>
          -- definedness of an old element holds of every element; a detached sort's name is a sort
          I.evalSymb .defined a ∨
          (I.evalSymb .inh a ∧ I.evalSymb .sortSort b ∧ ∃ nm, D (.sort nm) ∧ n = .srt nm))
    | .inl a, .inr n =>
      -- definedness of a new element holds of every element; a detached sort's inhabitants are
      -- its values
      I.evalSymb .defined a ∨
      (I.evalSymb .inh a ∧ ∃ s v, n = .srt ("Sort" ++ c.sortName s) ∧ DSort c D s ∧ c.sortOf v = some s ∧
        x = .inr (.val v))
    | .inr (.lit l), .inr (.srt n) =>
      ∃ s lit, n = "Sort" ++ c.sortName s ∧ lit.text = l ∧ DSort c D s ∧ c.sortOf (.dv s lit) = some s ∧
        x = .inr (.val (.dv s lit))
    | .inr (.hk f vs), b =>
      ∃ k w, DHook c D k ∧ k.name = f ∧ ElemOf c D I w b ∧ PartOf c D I k (vs ++ [w]) x
    | _, _ => False

/-- **The embedding clauses of `RegistryConservative`**: `Sum.inl` is injective; a symbol outside
`D` holds of an old element in the extension what it held; application of old elements gives the
old elements it gave. -/
theorem ext_embeds :
    Function.Injective (Sum.inl : M → Ext M) ∧
    (∀ σ, ¬ D σ → ∀ m, (Sum.inl m : Ext M) ∈ (extModel c D I).evalSymb σ ↔ m ∈ I.evalSymb σ) ∧
    (∀ a b m, (Sum.inl m : Ext M) ∈ (extModel c D I).evalApp (.inl a) (.inl b) ↔ m ∈ I.evalApp a b) :=
  ⟨fun _ _ h => Sum.inl.inj h,
   fun _ hσ _ => ⟨fun h => h.elim (·.2) (fun ⟨_, hk, he, _⟩ => absurd (he ▸ hk.2) hσ), fun h => .inl ⟨hσ, h⟩⟩,
   fun _ _ _ => Iff.rfl⟩

/-- A detached sort constant is one element of the extension, the added one. -/
theorem ext_sortName {n : String} (hn : D (.sort n)) (x : Ext M) :
    x ∈ (extModel c D I).evalSymb (.sort n) ↔ x = .inr (.srt n) := by
  constructor
  · intro h
    match x, h with
    | .inl _, .inl h => exact absurd hn h.1
    | .inl _, .inr ⟨_, _, h, _⟩ => cases h
    | .inr (.srt n'), h => have := h.2; cases this; rfl
    | .inr (.lit _), h => cases h
    | .inr (.val _), ⟨_, _, h, _⟩ => cases h
    | .inr (.hk _ _), ⟨_, _, h, _⟩ => cases h
  · rintro rfl
    exact ⟨hn, rfl⟩

/-- A literal's `dv` symbol holds of its added element. -/
theorem ext_lit (l : String) : (.inr (.lit l) : Ext M) ∈ (extModel c D I).evalSymb (.dv l) := rfl

/-- A value of a detached sort that is a literal is its `dv` symbol's added element applied to the
sort's added name. -/
theorem ext_dv_app {s : Srt} (hs : DSort c D s) {lit : Lit} (hv : c.sortOf (.dv s lit) = some s) :
    (.inr (.val (.dv s lit)) : Ext M) ∈
      (extModel c D I).evalApp (.inr (.lit lit.text)) (.inr (.srt ("Sort" ++ c.sortName s))) :=
  ⟨s, lit, rfl, rfl, hs, hv, rfl⟩

end

end KCore.Cons
