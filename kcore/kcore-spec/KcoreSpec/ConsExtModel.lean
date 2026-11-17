/-
  The extension of a model of the theory without the registry family (`Γown c D`,
  RegistryOwn.lean) by the elements the family speaks of: the carrier `M ⊕ Added M`, the
  interpretation `extModel` and the embedding `Sum.inl`, with the three embedding clauses of
  `RegistryConservative` (`ext_embeds`).

  The extension is free: application of old elements gives the old elements it gave and no added
  one, an old element applied to an added one gives nothing, and every fact about an added element
  goes through an added element of the symbol that states it. So nothing is asked of the smaller
  model: an element of it may lie in several symbols at once (in `⌈_⌉` and in a constructor, say),
  and no application of such an element changes.

  The added elements are: a detached sort constant; for each literal, an element of its `dv`
  symbol (a literal's `dv` symbol may be empty in the smaller model, and a value of a detached
  sort is that symbol applied to the sort's name); a value of a detached sort; a detached hooked
  symbol applied to fewer values than it has arguments; an element of `⌈_⌉`, whose application to
  any element holds of every element; an element of `⊤_`, whose application to a detached sort's
  name holds of the sort's values; an element of `Sort` whose inhabitants (under the added element
  of `⊤_`) are the detached sort names; an element of the definedness symbols `⌈_⌉{s,s'}` with its
  applications to one and to two sorts, which give `⌈x⌉{s,s'}` at a detached sort `s` or `s'`.

  `extModel` keeps every symbol outside `D` on the old elements (a detached symbol holds of an old
  element only as a hooked symbol without arguments whose result is that element), and gives a
  detached hooked symbol its graph (`hook`, and at a silent point `Semantics.fallback`) at the
  arguments that are elements of values of its argument sorts. An old element is the element of a
  value of a sort outside `D` where that value's pattern denotes exactly it in the smaller model.

  That `extModel` satisfies the theory is not proved here.
-/
import KcoreSpec.RegistryOwn

set_option autoImplicit false

namespace KCore.Cons

open ML Faithful

/-- The elements added to a model of the smaller theory, with carrier `M`. -/
inductive Added (M : Type) where
  /-- the detached sort constant `n` (a KORE sort name, `SortX`) -/
  | srt (n : String)
  /-- an element of the symbol `dv l` -/
  | lit (l : String)
  /-- a value of a detached sort -/
  | val (v : GroundTerm)
  /-- a detached hooked symbol applied to the values `vs`, fewer than its arguments -/
  | hk (f : Sym) (vs : List GroundTerm)
  /-- an element of `⌈_⌉` -/
  | dfn
  /-- an element of `⊤_` -/
  | inh
  /-- an element of `Sort`: the sort of the detached sort names -/
  | sorts
  /-- an element of the definedness symbols `⌈_⌉{s,s'}` -/
  | ceil
  /-- `ceil` applied to the sort `s`: an old element, or a detached sort's name -/
  | ceil1 (s : M ⊕ String)
  /-- `ceil` applied to the sorts `s` and `s'`, one of them a detached sort's name -/
  | ceil2 (s s' : M ⊕ String)

/-- The extended carrier. -/
abbrev Ext (M : Type) : Type := M ⊕ Added M

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

/-- The inhabitants, in the extension, of the sort `t`: of an old element, its old inhabitants; of
a detached sort's name, the sort's values. -/
def InhX (t : M ⊕ String) (x : Ext M) : Prop :=
  match t with
  | .inl σ => ∃ m, x = .inl m ∧ KoreAML.Inh I σ m
  | .inr n => ∃ s v, n = "Sort" ++ c.sortName s ∧ DSort c D s ∧ c.sortOf v = some s ∧ x = .inr (.val v)

/-- **The extended interpretation.** -/
def extModel : Interpretation KoreAML.Sym (Ext M) where
  evalSymb σ x := match x with
    | .inl m => (¬ D σ ∧ I.evalSymb σ m) ∨
        -- a detached hooked symbol without arguments whose result is a value of a sort outside `D`
        ∃ k, DHook c D k ∧ σ = .symbol (c.symName k.name) ∧ PartOf c D I k [] (.inl m)
    | .inr (.srt n) => D (.sort n) ∧ σ = .sort n
    | .inr (.lit l) => σ = .dv l
    | .inr .dfn => σ = .defined
    | .inr .inh => σ = .inh
    | .inr .sorts => σ = .sortSort
    | .inr .ceil => σ = .ceil
    | .inr (.ceil1 _) => False
    | .inr (.ceil2 _ _) => False
    | .inr n => ∃ k, DHook c D k ∧ σ = .symbol (c.symName k.name) ∧ PartOf c D I k [] (.inr n)
  evalApp a b x := match a, b with
    | .inl a, .inl b =>
      (match x with
        | .inl m => I.evalApp a b m
        | .inr _ => False)
    -- definedness of any element holds of every element
    | .inr .dfn, _ => True
    -- the detached sort names are sorts; a detached sort's inhabitants are its values
    | .inr .inh, .inr .sorts => ∃ nm, D (.sort nm) ∧ x = .inr (.srt nm)
    | .inr .inh, .inr (.srt n) => InhX c D I (.inr n) x
    | .inr (.lit l), .inr (.srt n) =>
      ∃ s lit, n = "Sort" ++ c.sortName s ∧ lit.text = l ∧ DSort c D s ∧ c.sortOf (.dv s lit) = some s ∧
        x = .inr (.val (.dv s lit))
    -- a detached hooked symbol takes the element of a value of its next argument sort
    | .inr (.hk f vs), b =>
      ∃ k w s, DHook c D k ∧ k.name = f ∧ k.args[vs.length]? = some s ∧ c.sortOf w = some s ∧
        ElemOf c D I w b ∧ PartOf c D I k (vs ++ [w]) x
    -- `⌈x⌉{s,s'}` where `s` or `s'` is a detached sort's name: the sort `s'`, for `x` in `s`
    | .inr .ceil, .inl σ => x = .inr (.ceil1 (.inl σ))
    | .inr .ceil, .inr (.srt n) => x = .inr (.ceil1 (.inr n))
    | .inr (.ceil1 (.inr n)), .inl σ' => x = .inr (.ceil2 (.inr n) (.inl σ'))
    | .inr (.ceil1 s), .inr (.srt n') => x = .inr (.ceil2 s (.inr n'))
    | .inr (.ceil2 s s'), y => InhX c D I s y ∧ InhX c D I s' x
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
    | .inr .dfn, h => cases h
    | .inr .inh, h => cases h
    | .inr .sorts, h => cases h
    | .inr .ceil, h => cases h
    | .inr (.ceil1 _), h => cases h
    | .inr (.ceil2 _ _), h => cases h
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

/-- The extension interprets `⌈_⌉` as definedness. -/
theorem ext_defOK : KoreAML.DefOK (extModel c D I) := fun _ _ => ⟨.inr .dfn, rfl, trivial⟩

end

end KCore.Cons
