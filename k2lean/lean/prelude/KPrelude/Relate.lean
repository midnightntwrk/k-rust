import KPrelude.RelAttr
import KPrelude.Coll
import KPrelude.InvColl
import KPrelude.Tactic
import KPrelude.Run

/-!
# Relating two generated libraries

Generic parts of `k2lean relate`, which translates the terms of one generated library `A` into
another `B` (`tr`, a symbol renaming) and states that the two `Step` relations are bisimilar.

- `Bisimulation`: a strong bisimulation between two relations, and what it transfers
  (reachability, terminal states).
- Maps translated pointwise: a pointwise translation of a sorted association list is the
  translation of the map when it preserves the order of the keys involved. Canonical maps are
  sorted by each library's own order on keys, and two independently generated libraries order
  constructors differently, so order preservation is a real hypothesis (`PresOn`).
- `k2l_inv`: inverts hypotheses `tr x = e` by case analysis on `x`.
-/

namespace KPrelude

/-! ## Bisimulation -/

/-- `R` is a strong bisimulation between `S₁` and `S₂`. -/
structure Bisimulation {α β : Type} (S₁ : α → α → Prop) (S₂ : β → β → Prop) (R : α → β → Prop) : Prop where
  fwd : ∀ {a b a'}, R a b → S₁ a a' → ∃ b', S₂ b b' ∧ R a' b'
  bwd : ∀ {a b b'}, R a b → S₂ b b' → ∃ a', S₁ a a' ∧ R a' b'

namespace Bisimulation

variable {α β : Type} {S₁ : α → α → Prop} {S₂ : β → β → Prop} {R : α → β → Prop}

theorem stepsN_fwd (h : Bisimulation S₁ S₂ R) :
    ∀ {n a b a'}, R a b → StepsN S₁ n a a' → ∃ b', StepsN S₂ n b b' ∧ R a' b'
  | _, _, b, _, hr, .refl _ => ⟨b, .refl _, hr⟩
  | _, _, _, _, hr, .step hs rest => by
    obtain ⟨b₁, hb₁, hr₁⟩ := h.fwd hr hs
    obtain ⟨b', hb', hr'⟩ := h.stepsN_fwd hr₁ rest
    exact ⟨b', .step hb₁ hb', hr'⟩

theorem stepsN_bwd (h : Bisimulation S₁ S₂ R) :
    ∀ {n a b b'}, R a b → StepsN S₂ n b b' → ∃ a', StepsN S₁ n a a' ∧ R a' b'
  | _, a, _, _, hr, .refl _ => ⟨a, .refl _, hr⟩
  | _, _, _, _, hr, .step hs rest => by
    obtain ⟨a₁, ha₁, hr₁⟩ := h.bwd hr hs
    obtain ⟨a', ha', hr'⟩ := h.stepsN_bwd hr₁ rest
    exact ⟨a', .step ha₁ ha', hr'⟩

/-- Related states are terminal (have no successor) together. -/
theorem terminal_iff (h : Bisimulation S₁ S₂ R) {a b} (hr : R a b) :
    (∀ a', ¬ S₁ a a') ↔ (∀ b', ¬ S₂ b b') := by
  constructor
  · intro ha b' hb
    obtain ⟨a', ha', _⟩ := h.bwd hr hb
    exact ha a' ha'
  · intro hb a' ha
    obtain ⟨b', hb', _⟩ := h.fwd hr ha
    exact hb b' hb'

end Bisimulation

/-! ## Sorted association lists under a pointwise translation -/

namespace SAL

set_option linter.unusedSectionVars false

variable {α α' β β' : Type} [Ord α] [Ord α']

/-- The pointwise translation of an association list. -/
def mapPairs (f : α → α') (g : β → β') (l : List (α × β)) : List (α' × β') :=
  l.map (fun p => (f p.1, g p.2))

@[simp] theorem mapPairs_nil (f : α → α') (g : β → β') : mapPairs f g [] = [] := rfl
@[simp] theorem mapPairs_cons (f : α → α') (g : β → β') (k : α) (v : β) (t : List (α × β)) :
    mapPairs f g ((k, v) :: t) = (f k, g v) :: mapPairs f g t := rfl

/-- `f` preserves the order on the keys that satisfy `P`. -/
def PresOn (P : α → Prop) (f : α → α') : Prop :=
  ∀ a b, P a → P b → compare (f a) (f b) = compare a b

variable {P : α → Prop} {f : α → α'} {g : β → β'}

theorem insert_mapPairs (hf : PresOn P f) {k : α} (hk : P k) (v : β) :
    ∀ {l : List (α × β)}, (∀ p ∈ l, P p.1) →
      insert (f k) (g v) (mapPairs f g l) = mapPairs f g (insert k v l)
  | [], _ => rfl
  | (k', v') :: t, hl => by
    have hk' : P k' := hl (k', v') (by simp)
    have ht : ∀ p ∈ t, P p.1 := fun p hp => hl p (by simp [hp])
    simp only [mapPairs_cons, insert, hf k k' hk hk']
    split <;> simp [insert_mapPairs hf hk v ht]

theorem lookup_mapPairs (hf : PresOn P f) {k : α} (hk : P k) :
    ∀ {l : List (α × β)}, (∀ p ∈ l, P p.1) → lookup (f k) (mapPairs f g l) = (lookup k l).map g
  | [], _ => rfl
  | (k', v') :: t, hl => by
    have hk' : P k' := hl (k', v') (by simp)
    have ht : ∀ p ∈ t, P p.1 := fun p hp => hl p (by simp [hp])
    simp only [mapPairs_cons, lookup, hf k k' hk hk']
    split <;> simp [lookup_mapPairs hf hk ht]

theorem erase_mapPairs (hf : PresOn P f) {k : α} (hk : P k) :
    ∀ {l : List (α × β)}, (∀ p ∈ l, P p.1) → erase (f k) (mapPairs f g l) = mapPairs f g (erase k l)
  | [], _ => rfl
  | (k', v') :: t, hl => by
    have hk' : P k' := hl (k', v') (by simp)
    have ht : ∀ p ∈ t, P p.1 := fun p hp => hl p (by simp [hp])
    simp only [mapPairs_cons, erase, hf k k' hk hk']
    split <;> simp [erase_mapPairs hf hk ht]

theorem mem_mapPairs {p : α' × β'} {l : List (α × β)} :
    p ∈ mapPairs f g l ↔ ∃ q ∈ l, p = (f q.1, g q.2) := by
  simp only [mapPairs, List.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩

theorem sorted_mapPairs_iff (hf : PresOn P f) :
    ∀ {l : List (α × β)}, (∀ p ∈ l, P p.1) → (Sorted (mapPairs f g l) ↔ Sorted l)
  | [], _ => by simp [Sorted.nil]
  | (k, v) :: t, hl => by
    have hk : P k := hl (k, v) (by simp)
    have ht : ∀ p ∈ t, P p.1 := fun p hp => hl p (by simp [hp])
    simp only [mapPairs_cons]
    constructor
    · intro h
      cases h with
      | cons hlt hs =>
        refine Sorted.cons (fun q hq => ?_) ((sorted_mapPairs_iff hf ht).1 hs)
        have := hlt (f q.1, g q.2) (mem_mapPairs.2 ⟨q, hq, rfl⟩)
        rwa [hf k q.1 hk (ht q hq)] at this
    · intro h
      cases h with
      | cons hlt hs =>
        refine Sorted.cons (fun q hq => ?_) ((sorted_mapPairs_iff hf ht).2 hs)
        obtain ⟨q', hq', rfl⟩ := mem_mapPairs.1 hq
        show compare (f k) (f q'.1) = .lt
        rw [hf k q'.1 hk (ht q' hq')]; exact hlt q' hq'

section Laws

variable [Std.TransOrd α] [Std.LawfulEqOrd α] [Std.TransOrd α'] [Std.LawfulEqOrd α']

/-- The map pattern `k |-> v REST` is preserved by an order-preserving translation. -/
theorem concat_singleton_mapPairs (hf : PresOn P f) {k : α} {v : β} {r m : List (α × β)}
    (hk : P k) (hm : ∀ p ∈ m, P p.1) (h : concat [(k, v)] r = some m) :
    concat [(f k, g v)] (mapPairs f g r) = some (mapPairs f g m) := by
  obtain ⟨hs, hn, rfl⟩ := concat_singleton_iff.1 h
  have hr : ∀ p ∈ r, P p.1 := by
    intro p hp
    apply hm
    rw [← erase_insert_of_lookup_none hs hn (v := v)] at hp
    exact mem_erase hp
  refine concat_singleton_iff.2 ⟨(sorted_mapPairs_iff hf hr).2 hs, ?_, (insert_mapPairs hf hk v hr).symm⟩
  rw [lookup_mapPairs hf hk hr, hn]; rfl

/-- The inverse direction: a match of `f k |-> v' REST'` on a translated map comes from a match
on the map. -/
theorem concat_singleton_mapPairs_inv (hf : PresOn P f) {k : α} {v' : β'} {r' : List (α' × β')}
    {m : List (α × β)} (hk : P k) (hm : ∀ p ∈ m, P p.1)
    (h : concat [(f k, v')] r' = some (mapPairs f g m)) :
    ∃ v r, v' = g v ∧ r' = mapPairs f g r ∧ concat [(k, v)] r = some m := by
  have hl := lookup_of_concat_singleton h
  rw [lookup_mapPairs hf hk hm] at hl
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 hl
  obtain ⟨hs', hn', he⟩ := concat_singleton_iff.1 h
  have hsm : Sorted m := (sorted_mapPairs_iff hf hm).1 (he ▸ sorted_insert hs')
  refine ⟨v, erase k m, rfl, ?_, concat_singleton_erase hsm hv⟩
  rw [← erase_mapPairs hf hk hm, he, erase_insert_of_lookup_none hs' hn']

end Laws

end SAL

/-! ## Maps of two libraries related by a pointwise translation `T` -/

namespace MapHook

open ListIso

set_option linter.unusedSectionVars false

variable {M K V M' K' V' : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V]
  [Ord K'] [ListIso M' (K' × V')] [MapRepr M' K' V']
  {P : K → Prop} {f : K → K'} {g : V → V'} {T : M → M'}

/-- `T` translates a map pointwise, with `f` on keys and `g` on values. -/
def Pointwise (f : K → K') (g : V → V') (T : M → M') : Prop :=
  ∀ m, toList (T m) = SAL.mapPairs f g (toList m)

theorem pointwise_ofList (hT : Pointwise f g T) (l : List (K × V)) :
    T (ofList l) = ofList (SAL.mapPairs f g l) := by
  have := hT (ofList l)
  rw [toList_ofList] at this
  rw [← this, ofList_toList]

theorem update_pointwise (hT : Pointwise f g T) (hf : SAL.PresOn P f) {m : M} {k : K} (v : V)
    (hm : KeysOn P m) (hk : P k) : update (T m) (f k) (g v) = T (update m k v) := by
  rw [update_def, update_def, hT, SAL.insert_mapPairs hf hk v hm, pointwise_ofList hT]

variable [Std.TransOrd K] [Std.LawfulEqOrd K] [Std.TransOrd K'] [Std.LawfulEqOrd K']


theorem concat_element_pointwise (hT : Pointwise f g T) (hf : SAL.PresOn P f) {k : K} {v : V} {r m : M}
    (hk : P k) (hm : KeysOn P m) (h : concat (element k v) r = some m) :
    concat (element (f k) (g v)) (T r) = some (T m) := by
  unfold concat element at *
  rw [toList_ofList] at *
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨l, hl, hlm⟩ := h
  have hl' : l = toList m := by rw [← hlm, toList_ofList]
  subst hl'
  rw [hT, SAL.concat_singleton_mapPairs hf hk hm hl]
  simp only [Option.map_some]
  rw [← hT m, ofList_toList]

theorem concat_element_pointwise_inv (hT : Pointwise f g T) (hf : SAL.PresOn P f) {k : K} {v' : V'}
    {r' : M'} {m : M} (hk : P k) (hm : KeysOn P m)
    (h : concat (element (f k) v') r' = some (T m)) :
    ∃ v r, v' = g v ∧ r' = T r ∧ concat (element k v) r = some m := by
  unfold concat element at h
  rw [toList_ofList] at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨l, hl, hlm⟩ := h
  have hl' : l = toList (T m) := by rw [← hlm, toList_ofList]
  subst hl'
  rw [hT] at hl
  obtain ⟨v, r, rfl, hr, hc⟩ := SAL.concat_singleton_mapPairs_inv hf hk hm hl
  refine ⟨v, ofList r, rfl, ?_, ?_⟩
  · rw [pointwise_ofList hT, ← hr, ofList_toList]
  · unfold concat element; rw [toList_ofList, toList_ofList, hc]; simp [ofList_toList]

end MapHook

/-! ## Translations that preserve the order of every key

When the two libraries give every constructor the same position (a renaming that keeps each
sort's constructor order, `docs/design.md`, §3.2), the translation preserves the serialization
of every term, so it preserves the order of every key (`SAL.Pres`), and every collection
operation commutes with it, with no hypothesis on the operands: the lemmas below are what
`relate` states for each collection sort. -/

namespace SAL

set_option linter.unusedSectionVars false

variable {α α' β β' : Type} [Ord α] [Ord α'] {f : α → α'} {g : β → β'}

/-- `f` preserves the order of every key. -/
def Pres (f : α → α') : Prop := ∀ a b, compare (f a) (f b) = compare a b

theorem Pres.presOn (hf : Pres f) {P : α → Prop} : PresOn P f := fun a b _ _ => hf a b

theorem sortedb_mapPairs (hf : Pres f) : ∀ l : List (α × β), sortedb (mapPairs f g l) = sortedb l
  | [] => rfl
  | (k, v) :: t => by
    rw [mapPairs_cons]
    simp only [sortedb]
    rw [sortedb_mapPairs hf t]
    congr 1
    simp only [mapPairs, List.all_map]
    exact List.all_congr rfl (fun p => by show (compare (f k) (f p.1) == _) = _; rw [hf])

theorem lookup_mapPairs_of_pres (hf : Pres f) (k : α) (l : List (α × β)) :
    lookup (f k) (mapPairs f g l) = (lookup k l).map g :=
  lookup_mapPairs hf.presOn (P := fun _ => True) trivial (fun _ _ => trivial)

theorem insert_mapPairs_of_pres (hf : Pres f) (k : α) (v : β) (l : List (α × β)) :
    insert (f k) (g v) (mapPairs f g l) = mapPairs f g (insert k v l) :=
  insert_mapPairs hf.presOn (P := fun _ => True) trivial v (fun _ _ => trivial)

theorem erase_mapPairs_of_pres (hf : Pres f) (k : α) (l : List (α × β)) :
    erase (f k) (mapPairs f g l) = mapPairs f g (erase k l) :=
  erase_mapPairs hf.presOn (P := fun _ => True) trivial (fun _ _ => trivial)

theorem foldr_insert_mapPairs (hf : Pres f) (b : List (α × β)) : ∀ a : List (α × β),
    (mapPairs f g a).foldr (fun p acc => insert p.1 p.2 acc) (mapPairs f g b) =
      mapPairs f g (a.foldr (fun p acc => insert p.1 p.2 acc) b)
  | [] => rfl
  | (k, v) :: t => by
    simp only [mapPairs_cons, List.foldr_cons, foldr_insert_mapPairs hf b t]
    exact insert_mapPairs_of_pres hf k v _

theorem concat_mapPairs (hf : Pres f) (a b : List (α × β)) :
    concat (mapPairs f g a) (mapPairs f g b) = (concat a b).map (mapPairs f g) := by
  unfold concat
  have hall : (mapPairs f g a).all (fun p => (lookup p.1 (mapPairs f g b)).isNone) =
      a.all (fun p => (lookup p.1 b).isNone) := by
    simp only [mapPairs, List.all_map]
    exact List.all_congr rfl (fun p => by
      show (lookup (f p.1) (mapPairs f g b)).isNone = _
      rw [lookup_mapPairs_of_pres hf]; cases lookup p.1 b <;> rfl)
  rw [sortedb_mapPairs hf, sortedb_mapPairs hf, hall]
  split
  · rw [Option.map_some, foldr_insert_mapPairs hf]
  · rfl

end SAL

namespace MapHook

open ListIso

set_option linter.unusedSectionVars false

variable {M K V M' K' V' : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V]
  [Ord K'] [ListIso M' (K' × V')] [MapRepr M' K' V']
  {f : K → K'} {g : V → V'} {T : M → M'}

theorem unit_pointwise (hT : Pointwise f g T) : T unit = unit := by
  unfold unit; rw [pointwise_ofList hT]; rfl

theorem element_pointwise (hT : Pointwise f g T) (k : K) (v : V) :
    element (f k) (g v) = T (element k v) := by
  unfold element; rw [pointwise_ofList hT]; rfl

theorem concat_pointwise (hT : Pointwise f g T) (hf : SAL.Pres f) (a b : M) :
    concat (T a) (T b) = (concat a b).map T := by
  unfold concat
  rw [hT, hT, SAL.concat_mapPairs hf]
  cases SAL.concat (toList a) (toList b) with
  | none => rfl
  | some l => simp only [Option.map_some, pointwise_ofList hT]

theorem update_pointwise_of_pres (hT : Pointwise f g T) (hf : SAL.Pres f) (m : M) (k : K) (v : V) :
    update (T m) (f k) (g v) = T (update m k v) := by
  rw [update_def, update_def, hT, SAL.insert_mapPairs_of_pres hf, pointwise_ofList hT]

theorem remove_pointwise (hT : Pointwise f g T) (hf : SAL.Pres f) (m : M) (k : K) :
    remove (T m) (f k) = T (remove m k) := by
  rw [remove_def, remove_def, hT, SAL.erase_mapPairs_of_pres hf, pointwise_ofList hT]

theorem lookup_pointwise (hT : Pointwise f g T) (hf : SAL.Pres f) (m : M) (k : K) :
    lookup (T m) (f k) = (lookup m k).map g := by
  rw [lookup_def, lookup_def, hT, SAL.lookup_mapPairs_of_pres hf]

theorem lookupOrDefault_pointwise (hT : Pointwise f g T) (hf : SAL.Pres f) (m : M) (k : K) (d : V) :
    lookupOrDefault (T m) (f k) (g d) = g (lookupOrDefault m k d) := by
  unfold lookupOrDefault
  rw [MapRepr.lookupR_eq, MapRepr.lookupR_eq, hT, SAL.lookup_mapPairs_of_pres hf]
  cases SAL.lookup k (toList m) <;> rfl

theorem inKeys_pointwise (hT : Pointwise f g T) (hf : SAL.Pres f) (m : M) (k : K) :
    inKeys (f k) (T m) = inKeys k m := by
  unfold inKeys
  rw [MapRepr.lookupR_eq, MapRepr.lookupR_eq, hT, SAL.lookup_mapPairs_of_pres hf]
  cases SAL.lookup k (toList m) <;> rfl

theorem size_pointwise (hT : Pointwise f g T) (m : M) : size (T m) = size m := by
  unfold size; rw [hT]; simp [SAL.mapPairs]

theorem keys_pointwise {S S' : Type} [ListIso S (K × Unit)] [MapRepr S K Unit]
    [ListIso S' (K' × Unit)] [MapRepr S' K' Unit] {TS : S → S'}
    (hT : Pointwise f g T) (hS : Pointwise f (fun u => u) TS) (m : M) : keys (T m) = TS (keys m) := by
  unfold keys
  rw [pointwise_ofList hS, hT]
  simp only [SAL.mapPairs, List.map_map]
  rfl

theorem values_pointwise {L L' : Type} [ListIso L V] [ListIso L' V'] {TL : L → L'}
    (hT : Pointwise f g T) (hL : ∀ l, toList (TL l) = (toList l).map g) (m : M) :
    values (T m) = TL (values m) := by
  unfold values
  have := hL (ofList ((toList m).map (·.2)))
  rw [toList_ofList] at this
  rw [← ofList_toList (TL _), this, hT]
  simp only [SAL.mapPairs, List.map_map]
  rfl

theorem keysList_pointwise {L L' : Type} [ListIso L K] [ListIso L' K'] {TL : L → L'}
    (hT : Pointwise f g T) (hL : ∀ l, toList (TL l) = (toList l).map f) (m : M) :
    keysList (T m) = TL (keysList m) := by
  unfold keysList
  have := hL (ofList ((toList m).map (·.1)))
  rw [toList_ofList] at this
  rw [← ofList_toList (TL _), this, hT]
  simp only [SAL.mapPairs, List.map_map]
  rfl

theorem difference_pointwise [DecidableEq V] [DecidableEq V'] (hT : Pointwise f g T) (hf : SAL.Pres f)
    (hg : ∀ a b, g a = g b → a = b) (a b : M) : difference (T a) (T b) = T (difference a b) := by
  unfold difference
  rw [pointwise_ofList hT, hT]
  congr 1
  simp only [SAL.mapPairs, List.filter_map]
  congr 1
  apply List.filter_congr
  intro p _
  simp only [Function.comp, lookup_pointwise hT hf]
  cases lookup b p.1 with
  | none => rfl
  | some w =>
    show (some (g w) != some (g p.2)) = (some w != some p.2)
    by_cases h : w = p.2
    · subst h; rw [bne_self_eq_false, bne_self_eq_false]
    · have h' : g w ≠ g p.2 := fun e => h (hg _ _ e)
      rw [show (some (g w) != some (g p.2)) = true from bne_iff_ne.2 (by simpa using h'),
        show (some w != some p.2) = true from bne_iff_ne.2 (by simpa using h)]

variable [Std.TransOrd K] [Std.LawfulEqOrd K] [Std.TransOrd K'] [Std.LawfulEqOrd K']

theorem _root_.KPrelude.SAL.sortedAdj_mapPairs (hf : SAL.Pres f) :
    ∀ l : List (K × V), SAL.sortedAdj (SAL.mapPairs f g l) = SAL.sortedAdj l
  | [] => rfl
  | [_] => rfl
  | (k₁, v₁) :: (k₂, v₂) :: t => by
    have ih := SAL.sortedAdj_mapPairs hf ((k₂, v₂) :: t)
    simp only [SAL.mapPairs_cons] at ih ⊢
    simp only [SAL.sortedAdj, hf k₁ k₂, ih]

theorem wfb_pointwise (hT : Pointwise f g T) (hf : SAL.Pres f) (m : M) : wfb (T m) = wfb m := by
  unfold wfb
  rw [MapRepr.sortedR_eq, MapRepr.sortedR_eq, hT, SAL.sortedAdj_mapPairs hf]

/-- `chooseFirst` as a search over the bindings, without the membership proofs. -/
theorem chooseFirst_eq_findSome [DecidableEq M] {β : Type} {m : M} {hw : WF m}
    {F : (k : K) → (v : V) → concat (element k v) (remove m k) = some m → Option β} :
    chooseFirst m hw F = (toList m).findSome? fun p =>
      if hc : concat (element p.1 p.2) (remove m p.1) = some m then F p.1 p.2 hc else none := by
  unfold chooseFirst
  have h : (fun (p : {x // x ∈ toList m}) =>
      F p.1.1 p.1.2 (concat_element_remove hw (lookup_of_mem_toList hw p.2))) =
      (fun p : K × V => if hc : concat (element p.1 p.2) (remove m p.1) = some m then
        F p.1 p.2 hc else none) ∘ Subtype.val := by
    funext p
    simp only [Function.comp]
    rw [dif_pos (concat_element_remove hw (lookup_of_mem_toList hw p.2))]
  rw [h, ← List.findSome?_map, List.attach_map_subtype_val]

theorem _root_.List.findSome?_map_of_mem {α β β' : Type} {G : α → Option β} {H : α → Option β'}
    {φ : β → β'} : ∀ {l : List α}, (∀ x ∈ l, H x = (G x).map φ) →
      l.findSome? H = (l.findSome? G).map φ
  | [], _ => rfl
  | a :: t, h => by
    simp only [List.findSome?_cons, h a (List.mem_cons_self ..)]
    cases G a with
    | none => exact List.findSome?_map_of_mem (fun x hx => h x (List.mem_cons_of_mem _ hx))
    | some b => rfl

/-- `chooseFirst` on a translated map, with a continuation that agrees with the translation of
the original one at every binding. -/
theorem chooseFirst_pointwise [DecidableEq M] [DecidableEq M'] {β β' : Type}
    (hT : Pointwise f g T) (hf : SAL.Pres f) {m : M} {hw : WF m} {hw' : WF (T m)}
    {F : (k : K) → (v : V) → concat (element k v) (remove m k) = some m → Option β}
    {F' : (k : K') → (v : V') → concat (element k v) (remove (T m) k) = some (T m) → Option β'}
    {φ : β → β'} (h : ∀ k v hc hc', F' (f k) (g v) hc' = (F k v hc).map φ) :
    chooseFirst (T m) hw' F' = (chooseFirst m hw F).map φ := by
  rw [chooseFirst_eq_findSome, chooseFirst_eq_findSome, hT, SAL.mapPairs, List.findSome?_map]
  apply List.findSome?_map_of_mem
  intro p hp
  have hc := concat_element_remove hw (lookup_of_mem_toList hw hp)
  have hc' : concat (element (f p.1) (g p.2)) (remove (T m) (f p.1)) = some (T m) := by
    rw [element_pointwise hT, remove_pointwise hT hf, concat_pointwise hT hf, hc]; rfl
  simp only [Function.comp, dif_pos hc, dif_pos hc']
  exact h _ _ hc hc'

/-- A match `k' |-> v' r'` of a translated map, with a free key, is the translation of a match
of the map. -/
theorem concat_element_pointwise_inv_free (hT : Pointwise f g T) (hf : SAL.Pres f) {k' : K'} {v' : V'}
    {r' : M'} {m : M} (h : concat (element k' v') r' = some (T m)) :
    ∃ k v r, k' = f k ∧ v' = g v ∧ r' = T r ∧ concat (element k v) r = some m := by
  have hl := lookup_of_concat_element h
  rw [lookup_def, hT] at hl
  obtain ⟨q, _, hq⟩ := SAL.mem_mapPairs.1 (SAL.lookup_mem hl)
  simp only [Prod.mk.injEq] at hq
  obtain ⟨rfl, -⟩ := hq
  obtain ⟨v, r, hv, hr, hc⟩ := concat_element_pointwise_inv hT hf.presOn (P := fun _ => True)
    trivial (fun _ _ => trivial) h
  exact ⟨q.1, v, r, rfl, hv, hr, hc⟩

/-- The same with the key bound (`k' = f k` known). -/
theorem concat_element_pointwise_inv_of_pres (hT : Pointwise f g T) (hf : SAL.Pres f) {k : K} {v' : V'}
    {r' : M'} {m : M} (h : concat (element (f k) v') r' = some (T m)) :
    ∃ v r, v' = g v ∧ r' = T r ∧ concat (element k v) r = some m :=
  concat_element_pointwise_inv hT hf.presOn (P := fun _ => True) trivial (fun _ _ => trivial) h

end MapHook

namespace SetHook

open ListIso

set_option linter.unusedSectionVars false

variable {S K S' K' : Type} [Ord K] [ListIso S (K × Unit)] [MapRepr S K Unit]
  [Ord K'] [ListIso S' (K' × Unit)] [MapRepr S' K' Unit] {f : K → K'} {T : S → S'}

theorem unit_pointwise (hT : MapHook.Pointwise f (fun u => u) T) : T unit = unit :=
  MapHook.unit_pointwise hT

theorem element_pointwise (hT : MapHook.Pointwise f (fun u => u) T) (k : K) :
    element (f k) = T (element k) :=
  MapHook.element_pointwise hT k ()

theorem concat_pointwise (hT : MapHook.Pointwise f (fun u => u) T) (hf : SAL.Pres f) (a b : S) :
    concat (T a) (T b) = (concat a b).map T :=
  MapHook.concat_pointwise hT hf a b

theorem inSet_pointwise (hT : MapHook.Pointwise f (fun u => u) T) (hf : SAL.Pres f) (s : S) (k : K) :
    inSet (f k) (T s) = inSet k s :=
  MapHook.inKeys_pointwise hT hf s k

theorem difference_pointwise (hT : MapHook.Pointwise f (fun u => u) T) (hf : SAL.Pres f) (a b : S) :
    difference (T a) (T b) = T (difference a b) := by
  unfold difference
  rw [MapHook.pointwise_ofList hT, hT]
  congr 1
  simp only [SAL.mapPairs, List.filter_map]
  congr 1
  apply List.filter_congr
  intro p _
  simp only [Function.comp, MapHook.inKeys_pointwise hT hf]

theorem size_pointwise (hT : MapHook.Pointwise f (fun u => u) T) (s : S) : size (T s) = size s := by
  unfold size; rw [hT]; simp [SAL.mapPairs]

end SetHook

namespace ListHook

open ListIso

set_option linter.unusedSectionVars false

variable {L E L' E' : Type} [ListIso L E] [ListIso L' E'] {f : E → E'} {T : L → L'}

/-- `T` translates a list elementwise with `f`. -/
def Pointwise (f : E → E') (T : L → L') : Prop := ∀ l, toList (T l) = (toList l).map f

theorem pointwise_ofList (hT : Pointwise f T) (l : List E) : T (ofList l) = ofList (l.map f) := by
  have := hT (ofList l)
  rw [toList_ofList] at this
  rw [← this, ofList_toList]

theorem unit_pointwise (hT : Pointwise f T) : T unit = unit := by
  unfold unit; rw [pointwise_ofList hT]; rfl

theorem element_pointwise (hT : Pointwise f T) (x : E) : element (f x) = T (element x) := by
  unfold element; rw [pointwise_ofList hT]; rfl

theorem concat_pointwise (hT : Pointwise f T) (a b : L) : concat (T a) (T b) = T (concat a b) := by
  unfold concat; rw [pointwise_ofList hT, hT, hT, List.map_append]

theorem size_pointwise (hT : Pointwise f T) (l : L) : size (T l) = size l := by
  unfold size; rw [hT, List.length_map]

/-- `ListItem(X) REST` on a translated list is the translation of a match on the list. -/
theorem concat_element_pointwise_inv (hT : Pointwise f T) {x' : E'} {t' : L'} {l : L}
    (h : concat (element x') t' = T l) : ∃ x t, x' = f x ∧ t' = T t ∧ concat (element x) t = l := by
  have hl := congrArg toList h
  unfold concat element at hl
  rw [toList_ofList, toList_ofList, hT, List.singleton_append] at hl
  match hm : toList l, hl with
  | x :: t, hl =>
    simp only [List.map_cons, List.cons.injEq] at hl
    obtain ⟨rfl, ht⟩ := hl
    refine ⟨x, ofList t, rfl, ?_, ?_⟩
    · rw [pointwise_ofList hT, ← ht, ofList_toList]
    · unfold concat element; rw [toList_ofList, toList_ofList, List.singleton_append, ← hm, ofList_toList]

/-- `REST ListItem(X)` on a translated list is the translation of a match on the list. -/
theorem concat_element_pointwise_inv_back (hT : Pointwise f T) {x' : E'} {t' : L'} {l : L}
    (h : concat t' (element x') = T l) : ∃ x t, x' = f x ∧ t' = T t ∧ concat t (element x) = l := by
  have hl := congrArg toList h
  unfold concat element at hl
  rw [toList_ofList, toList_ofList, hT] at hl
  have hne : toList l ≠ [] := by intro e; rw [e] at hl; simp at hl
  obtain ⟨front, x, hfx⟩ := List.eq_nil_or_concat (toList l) |>.resolve_left hne
  rw [List.concat_eq_append] at hfx
  rw [hfx, List.map_append, List.map_singleton] at hl
  obtain ⟨ht, hx⟩ := List.append_inj' hl rfl
  simp only [List.cons.injEq, and_true] at hx
  refine ⟨x, ofList front, hx, ?_, ?_⟩
  · rw [pointwise_ofList hT, ← ht, ofList_toList]
  · unfold concat element; rw [toList_ofList, toList_ofList, ← hfx, ofList_toList]

end ListHook

namespace KEqHook

/-- `==K` commutes with an injective translation. -/
theorem eq_of_injective {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : ∀ a b, f a = f b → a = b) (a b : α) : eq (f a) (f b) = eq a b := by
  unfold eq
  exact decide_eq_decide.2 ⟨hf a b, congrArg f⟩

/-- `=/=K` commutes with an injective translation. -/
theorem ne_of_injective {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : ∀ a b, f a = f b → a = b) (a b : α) : ne (f a) (f b) = ne a b := by
  unfold ne
  rw [decide_eq_decide.2 ⟨hf a b, congrArg f⟩]

end KEqHook

/-! ## Inverting a translation -/

open Lean Meta Elab Tactic in
/-- `k2l_inv`: repeatedly (1) substitute variables, (2) split conjunctions, (3) for a hypothesis
`h : f a = f b` where `f` is a translation function (its name has a component starting with
`tr_`), rewrite it to `a = b` by `f`'s injectivity (`tr_eq_iff_S` beside `f`), or, for a token sort
(a structure over its string, with no such lemma), destructure both sides and inject, and (4) for a
hypothesis `h : e = f x` (or `f x = e`) where `x` is a local variable and `e` is not a variable nor
a translation, case on `x` (on the arity-indexed family, its sort's values by `familyCases`, then
`h` simplified by the `k2l_tr` equations) and simplify `h` with `f`'s equations, read off its folding lemmas
`fold_S_k : B.C (tr a) = tr (A.C a)` reversed (else `f`'s own equations): constructor clashes close
the goal, matching constructors give equations between the arguments. Terminates because `e`
gets smaller; when `e` is an application of a function (an injection between sorts, a
collection operation), fold it into a translation by the `k2l_rel` lemmas first, for (3), and
never case split against a collection operation of the prelude. (5) A list match `ListItem(x') t' = f l` (or `t' ListItem(x')`) becomes
`x' = f x`, `t' = f t` and the match on `l`, by the lemmas `list_bwd_S`/`list_bwd_back_S` beside
`f`: a rule's hypothesis `ListItem(X) T = L` is substituted by (1) wherever `L` was bound, so the
match is found where it lands rather than by its name. (6) Two hypotheses `e = a` and `e = b`
with one left-hand side (two hypotheses of a rule on one call, `f x = some r`, `f x = some r'`)
give `a = b` (by `Option.some.inj` between `some`s), and the second is dropped: a function has one
value, and a later step that reads one of the results then sees the other.
The folding lemmas are `rfl` lemmas of the relation's module; `f`'s own equations would be derived
on first use (`f.eq_def` of the mutual block of translations, seconds each on SIMPLE). -/
partial def k2lInvLoop (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| try subst_vars))
  k2lAndsLoop 64
  evalTactic (← `(tactic| try subst_vars))
  if (← getGoals).isEmpty then return
  let isTr (e : Expr) : Option (Name × Expr) :=
    match e.getAppFn with
    | .const n _ =>
      if (n.components.getLast?.map (fun c => c.toString.startsWith "tr_")).getD false then
        (e.getAppArgs.back?).map (fun x => (n, x))
      else none
    | _ => none
  let found ← withMainContext do
    -- injectivity: `f a = f b` gives `a = b`
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let some (_, l, r) := ty.eq? | continue
      let (some (f1, a), some (f2, b)) := (isTr l, isTr r) | continue
      unless f1 == f2 do continue
      let hid := mkIdent ldecl.userName
      let lem := f1.getPrefix ++ Name.mkSimple ("tr_eq_iff_" ++ (f1.components.getLast!.toString.drop 3))
      let s ← saveState
      try
        evalTactic (← `(tactic| rw [$(mkIdent lem):ident] at $hid:ident))
        return true
      catch _ => s.restore
      unless a.isFVar && b.isFVar do continue
      let s ← saveState
      try
        let ha ← Term.exprToSyntax a
        let hb ← Term.exprToSyntax b
        evalTactic (← `(tactic| (cases $ha:term; cases $hb:term; simp only [$(mkIdent f1):ident] at $hid:ident; injection $hid:ident)))
        return true
      catch _ => s.restore
    -- one call, two results: `e = a` and `e = b` (`some a`, `some b`) give `a = b`
    let eqs ← (← getLCtx).foldlM (init := #[]) fun acc ldecl => do
      if ldecl.isImplementationDetail then return acc
      let ty ← instantiateMVars ldecl.type
      let some (_, l, r) := ty.eq? | return acc
      if l.isFVar || l.hasMVar then return acc
      return acc.push (ldecl.userName, l, r)
    for i in [0:eqs.size] do
      for j in [i+1:eqs.size] do
        let (n₁, l₁, r₁) := eqs[i]!
        let (n₂, l₂, r₂) := eqs[j]!
        unless l₁ == l₂ && r₁ != r₂ do continue
        let s ← saveState
        try
          let (h₁, h₂) := (mkIdent n₁, mkIdent n₂)
          if r₁.isAppOfArity ``Option.some 2 && r₂.isAppOfArity ``Option.some 2 then
            evalTactic (← `(tactic| (have := Option.some.inj ((Eq.symm $h₁).trans $h₂); clear $h₂:ident)))
          else
            evalTactic (← `(tactic| (have := (Eq.symm $h₁).trans $h₂; clear $h₂:ident)))
          return true
        catch _ => s.restore
    -- a list match: `ListItem(x') t' = f l` (or `t' ListItem(x')`) by `list_bwd_S` beside `f`
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let some (_, l, r) := ty.eq? | continue
      let some (side, flip, fn) := (match isTr r, isTr l with
        | some (f, _), none => some (l, false, f)
        | none, some (f, _) => some (r, true, f)
        | _, _ => none) | continue
      unless side.getAppFn.constName? == some ``ListHook.concat do continue
      let sfx := fn.components.getLast!.toString.drop 3
      let hid := mkIdent ldecl.userName
      let h ← if flip then `(Eq.symm $hid) else `($hid)
      let mut done := false
      for nm in [s!"list_bwd_{sfx}", s!"list_bwd_back_{sfx}"] do
        let lem := mkIdent (fn.getPrefix ++ Name.mkSimple nm)
        let s ← saveState
        try
          evalTactic (← `(tactic| (obtain ⟨_, _, _, _, _⟩ := $lem $h; clear $hid:ident)))
          done := true
          break
        catch _ => s.restore
      if done then return true
    -- a case split where the other side is a constructor term
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let some (_, l, r) := ty.eq? | continue
      let cand := match isTr r, isTr l with
        | some t, none => if l.isFVar then none else some t
        | none, some t => if r.isFVar then none else some t
        | _, _ => none
      let some (fn, x) := cand | continue
      unless x.isFVar do continue
      let other := if (isTr r).isSome then l else r
      let hid := mkIdent ldecl.userName
      if (← whnfR (← inferType x)).getAppFn.constName?.any (isFamilyName (← getEnv)) then
        -- on the arity-indexed family: the cases of the sort's values only (`familyCases`)
        let s ← saveState
        try
          let gs ← familyCases (← getMainGoal) x.fvarId!
          let mut out := #[]
          for (g, _) in gs do
            setGoals [g]
            evalTactic (← `(tactic| simp [k2l_tr] at $hid:ident))
            out := out ++ (← getGoals)
          setGoals out.toList
          return true
        catch _ => s.restore
        continue
      unless other.isLit || (← isConstructorApp other) do
        -- a function (an injection between sorts, a collection operation, a constructor of the
        -- arity universe's term family): fold it into a translation (`fold_inj_*`, `comm_*`,
        -- `k2l_rel`), which injectivity then removes; else case split as against a constructor,
        -- except on a collection operation of the prelude, whose cases would not reduce it (a list
        -- match is inverted by (5), a map's by the relation's map lemmas)
        let s ← saveState
        try
          evalTactic (← `(tactic| simp only [k2l_rel] at $hid:ident))
          return true
        catch _ => s.restore
        if other.getAppFn.constName?.any (`KPrelude).isPrefixOf then continue
      let s ← saveState
      try
        let hx ← Term.exprToSyntax x
        let sfx := fn.components.getLast!.toString.drop 3
        let env ← getEnv
        let mut lems : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
        let mut k := 0
        while true do
          let n := fn.getPrefix ++ Name.mkSimple s!"fold_{sfx}_{k}"
          unless env.contains n do break
          lems := lems.push (← `(Lean.Parser.Tactic.simpLemma| ← $(mkIdent n):ident))
          k := k + 1
        if lems.isEmpty then
          evalTactic (← `(tactic| cases $hx:term <;> simp [$(mkIdent fn):ident] at $hid:ident))
        else
          evalTactic (← `(tactic| cases $hx:term <;> simp only [$lems,*, reduceCtorEq] at $hid:ident <;> (try injection $hid:ident)))
        return true
      catch _ => s.restore
    return false
  if found then
    let gs ← getGoals
    let mut out := #[]
    for g in gs do
      setGoals [g]
      k2lInvLoop (fuel - 1)
      out := out ++ (← getGoals)
    setGoals out.toList

elab "k2l_inv" : tactic => k2lInvLoop 64

open Lean Meta Elab Tactic in
/-- `k2l_assumption`: close the goal by a hypothesis, instantiating the goal's metavariables that
other goals stand for (`apply` makes them synthetic opaque, which `assumption` leaves alone): the
variables of a rule that occur only in a side hypothesis, such as the value matched in a map, are
read off the hypothesis that matches it. -/
elab "k2l_assumption" : tactic => liftMetaTactic fun g => g.withContext do
  let ty ← g.getType
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let s ← saveState
    if ← withAssignableSyntheticOpaque (isDefEq ldecl.type ty) then
      g.assign ldecl.toExpr
      return []
    s.restore
  throwError "k2l_assumption: no hypothesis matches the goal"




end KPrelude

attribute [k2l_rel] Option.map_some Option.map_none

namespace KPrelude

open Lean Meta Elab Tactic in
/-- `k2l_comm_fn`: close `B.f (tr x) = tr? (A.f x)` after unfolding both definitions: case on
the variables (up to depth 3) until both sides reduce to the same value. -/
partial def k2lCommLoop (fuel : Nat) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let s ← saveState
  try
    evalTactic (← `(tactic| first | rfl | (simp only [k2l_rel]; done) | (simp only [k2l_rel]; rfl)))
    return
  catch _ => s.restore
  if fuel = 0 then throwError "k2l_comm_fn: no proof found"
  -- case on the first local of an inductive type that the goal mentions
  let g ← getMainGoal
  let target ← instantiateMVars (← g.getType)
  let cand ← g.withContext do
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let ty ← whnf ldecl.type
      if ty.isProp then continue
      unless (target.find? (· == ldecl.toExpr)).isSome do continue
      let .const tn _ := ty.getAppFn | continue
      if let some (.inductInfo _) := (← getEnv).find? tn then
        if tn == ``Int || tn == ``Nat || tn == ``String then continue
        return some ldecl.toExpr
    return none
  let some x := cand | throwError "k2l_comm_fn: nothing to case on"
  if ← g.withContext do
      return (← whnfR (← inferType x)).getAppFn.constName?.any (isFamilyName (← getEnv)) then
    setGoals ((← familyCases g x.fvarId!).toList.map (·.1))
  else
    let hx ← g.withContext (Term.exprToSyntax x)
    evalTactic (← `(tactic| cases $hx:term))
  let gs ← getGoals
  let mut out := #[]
  for g in gs do
    setGoals [g]
    k2lCommLoop (fuel - 1)
    out := out ++ (← getGoals)
  setGoals out.toList

elab "k2l_comm_fn" : tactic => k2lCommLoop 3

end KPrelude

namespace KPrelude

open Lean Meta Elab Tactic in
/-- `k2l_ctor_search I tac`: try each constructor of the inductive proposition `I` in turn:
`apply` it and run `tac` on every new goal; keep the first constructor for which every goal
closes. Used to prove `App c` (some rule applies) without naming the rule. -/
elab "k2l_ctor_search " i:ident " => " tac:tacticSeq : tactic => do
  let n ← realizeGlobalConstNoOverloadWithInfo i
  let some (.inductInfo info) := (← getEnv).find? n | throwError "{n} is not an inductive"
  for c in info.ctors do
    let s ← saveState
    try
      let cid := mkIdent c
      evalTactic (← `(tactic| apply $cid:ident))
      evalTactic (← `(tactic| all_goals ($tac)))
      if (← getGoals).isEmpty then return
      s.restore
    catch _ => s.restore
  throwError "k2l_ctor_search: no constructor of {n} applies"

end KPrelude

namespace KPrelude.IOHook

/-! An undefined IO hook (`--io off`) is `none` in both definitions, so a rule that calls one has
no instance: the relation's closers read it off the hypothesis `undefN … = some r`. -/

@[k2l_rel] theorem undef0_eq {β : Type} : (undef0 : Option β) = none := rfl
@[k2l_rel] theorem undef1_eq {α β : Type} (a : α) : (undef1 a : Option β) = none := rfl
@[k2l_rel] theorem undef2_eq {α₁ α₂ β : Type} (a : α₁) (b : α₂) : (undef2 a b : Option β) = none := rfl
@[k2l_rel] theorem undef3_eq {α₁ α₂ α₃ β : Type} (a : α₁) (b : α₂) (c : α₃) :
    (undef3 a b c : Option β) = none := rfl
@[k2l_rel] theorem undef4_eq {α₁ α₂ α₃ α₄ β : Type} (a : α₁) (b : α₂) (c : α₃) (d : α₄) :
    (undef4 a b c d : Option β) = none := rfl

end KPrelude.IOHook
