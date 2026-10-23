import KrsImp.Rules

/-! The typing invariant of KRS IMP, written by hand (the shape the generator now emits from KRS's
cell type `env: Map<Id, Value>`, through the sidecar; `Sidecar.lean` proves the two equivalent).

The compiled KORE types the `<env>` cell as K's untyped `Map` (`KItem ↦ KItem`).
KRS declares it `Map<Id, Value>`.
The declared type is a predicate on configurations, `WT`, and it is sound to read the cell as a
typed map exactly when every rule preserves `WT` (`Step.wt`).
`Step.wt` is the one new obligation of the refinement: with it, the configurations reachable from
a well-typed one are well typed (`Reach.wt`), and the typed view `TConfig` steps exactly as the
untyped semantics does (`TStep_iff`), so claims and invariants can be stated over typed maps. -/

namespace KrsImp.Typing

open KPrelude

/-- One binding of `Map<Id, Value>`: an `Id` key and a `Value` value. -/
def EntryOk (p : SortKItem × SortKItem) : Prop :=
  (∃ k, p.1 = SortKItem.inj_Id k) ∧ (∃ v, proj_KItem_Value p.2 = some v)

/-- The `<env>` cell holds a `Map<Id, Value>`. -/
def EnvOk : SortEnvCell → Prop
  | .«<env>» m => ∀ p ∈ ListIso.toList m, EntryOk p

/-- The configuration is well typed: every cell with a declared collection type holds it. -/
def WT : SortGeneratedTopCell → Prop
  | .«<generatedTop>» _ e _ => EnvOk e

theorem envOk_update {m : SortMap} {k v : SortKItem} (h : EnvOk (.«<env>» m)) (hk : EntryOk (k, v)) :
    EnvOk (.«<env>» (MapHook.update m k v)) := by
  intro p hp
  rw [MapHook.update_def, ListIso.toList_ofList] at hp
  rcases SAL.mem_insert hp with rfl | hp
  · exact hk
  · exact h p hp

/-- Every rule preserves the declared cell types (one case per `Step` constructor). -/
theorem Step.wt {c c' : SortGeneratedTopCell} (h : Step c c') (hw : WT c) : WT c' := by
  cases h <;> simp only [WT] at hw ⊢ <;>
    first
    | exact hw
    | exact envOk_update hw ⟨⟨_, rfl⟩, ⟨_, proj_inj_KItem_Value _⟩⟩

/-- Reflexive-transitive closure of `Step`. -/
inductive Reach : SortGeneratedTopCell → SortGeneratedTopCell → Prop where
  | refl (c) : Reach c c
  | step {c c' c''} : Step c c' → Reach c' c'' → Reach c c''

theorem Reach.wt {c c' : SortGeneratedTopCell} (h : Reach c c') (hw : WT c) : WT c' := by
  induction h with
  | refl => exact hw
  | step hs _ ih => exact ih (Step.wt hs hw)

/-- The typed view: configurations whose typed cells hold their declared types. -/
abbrev TConfig := { c : SortGeneratedTopCell // WT c }

/-- The typed step: the untyped step between typed configurations. -/
def TStep (t t' : TConfig) : Prop := Step t.1 t'.1

/-- The typed view loses no step: every untyped successor of a typed configuration is typed. -/
theorem TStep_iff (t : TConfig) (c' : SortGeneratedTopCell) :
    Step t.1 c' ↔ ∃ t' : TConfig, t'.1 = c' ∧ TStep t t' :=
  ⟨fun h => ⟨⟨c', Step.wt h t.2⟩, rfl, h⟩, fun ⟨_, he, h⟩ => he ▸ h⟩

/-- Typed lookup in the `<env>` cell of a typed configuration: the projection to `Value` always
succeeds on a typed map, so the result needs no cast at the use site. -/
def envLookup : (c : SortGeneratedTopCell) → SortId → Option SortValue
  | .«<generatedTop>» _ (.«<env>» m) _, x => (MapHook.lookup m (SortKItem.inj_Id x)).bind proj_KItem_Value

end KrsImp.Typing
