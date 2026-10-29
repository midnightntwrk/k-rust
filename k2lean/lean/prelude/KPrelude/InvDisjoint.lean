import KPrelude.InvColl

/-!
# Claims disjoint across the bindings of a map

A legality condition that no two parts of a configuration claim one thing: each binding of a map
(a cell map's element) claims a list of values, `g k v`, and no value is claimed twice, within a
binding or across two (linearity: each resource owned by one process; a coordination script whose
tasks name each step once). In K it is written `noDup(F(M))`, where `F` concatenates the claims of
the bindings by a free-key walk: `F(.Map) => .List` and `F((K |-> V) R) => g(K, V) F(R)`.

`F` alone has no single meaning in K: `K |-> V R` matches modulo associativity and commutativity,
so `F`'s value depends on the order the walk takes the bindings in, which K does not fix. What `F`'s
result is, up to the order of its elements, does not depend on it, and `noDup` is invariant under
permutations, so `noDup(F(M))` has one meaning. That is why the model's choice (the canonical
order, `chooseFirst`) agrees with K here, and why every statement below is up to permutation
(`claimsOf`, whose order is the canonical one, appears only under `Nodup` or `Subperm`).

- `perm_toList_concat`, `perm_toList_remove`: a defined `M₁ M₂` lists the bindings of both, and a
  map lists a binding and the rest, up to order.
- `fold_claims`: from a fold's instances, its value is the claims of every binding (`claimsOf`), up
  to order, and each binding's claims are defined; `fold_isSome`: the fold is defined where every
  binding's claims are.
- `nodup_fn`: K's `noDup` is `List.Nodup`.
- `nodup_claimsOf_iff`: the order-free reading, each binding's claims without repetition and
  two distinct bindings' claims disjoint.
- `claimsOf_concat`, `claimsOf_element`, `nodup_of_subperm_claims`: what a rule's case needs: the
  claims a rule writes are among those it removes (as multisets), so no claim is duplicated.
-/

set_option linter.unusedSectionVars false

namespace KPrelude

namespace SAL

variable {α β : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]

/-- A sorted association list has no repeated binding. -/
theorem nodup_of_sorted : ∀ {m : List (α × β)}, Sorted m → m.Nodup
  | [], _ => List.nodup_nil
  | (k, v) :: t, Sorted.cons hlt ht => by
    refine List.nodup_cons.2 ⟨fun hm => ?_, nodup_of_sorted ht⟩
    have := hlt (k, v) hm
    rw [cmp_self] at this
    cases this

end SAL

namespace MapHook

open ListIso

variable {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V]
  [Std.TransOrd K] [Std.LawfulEqOrd K]

theorem nodup_toList {m : M} (hw : WF m) : (toList m).Nodup := SAL.nodup_of_sorted hw

/-- The operands of a defined `M₁ M₂` are well formed and share no key. -/
theorem concat_operands {a b m : M} (h : concat a b = some m) :
    WF a ∧ WF b ∧ ∀ p ∈ toList a, ∀ q ∈ toList b, p.1 ≠ q.1 := by
  unfold concat SAL.concat at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, List.all_eq_true, Option.isNone_iff_eq_none] at hc
    obtain ⟨⟨ha, hb⟩, hd⟩ := hc
    have hb' : SAL.Sorted (toList b) := (SAL.sortedb_iff _).1 hb
    refine ⟨(SAL.sortedb_iff _).1 ha, hb', fun p hp q hq he => ?_⟩
    have hl : SAL.lookup q.1 (toList b) = some q.2 := by
      rw [← lookup_def]; exact lookup_of_mem_toList hb' hq
    rw [← he, hd p hp] at hl
    cases hl
  · simp at h

/-- A defined `M₁ M₂` lists the bindings of both operands, up to order. -/
theorem perm_toList_concat {a b m : M} (h : concat a b = some m) :
    (toList m).Perm (toList a ++ toList b) := by
  obtain ⟨ha, hb, hd⟩ := concat_operands h
  have hn : (toList a ++ toList b).Nodup :=
    List.nodup_append.2 ⟨nodup_toList ha, nodup_toList hb,
      fun p hp q hq he => hd p hp q hq (he ▸ rfl)⟩
  refine (List.perm_ext_iff_of_nodup (nodup_toList (wf_of_concat h)) hn).2 fun p => ?_
  rw [mem_toList_of_concat h, List.mem_append]

/-- A map lists one of its bindings and the rest, up to order. -/
theorem perm_toList_remove {m : M} {k : K} {v : V} (hw : WF m) (hk : (k, v) ∈ toList m) :
    (toList m).Perm ((k, v) :: toList (remove m k)) := by
  have h := perm_toList_concat (concat_element_remove hw (lookup_of_mem_toList hw hk))
  unfold element at h
  rwa [toList_ofList, List.singleton_append] at h

section Claims

variable {L E : Type} [ListIso L E]

/-- The claims of a list of bindings (`g k v` at each, nothing where it is undefined). -/
def claimsL (g : K → V → Option L) (ps : List (K × V)) : List E :=
  ps.flatMap fun p => ((g p.1 p.2).map toList).getD []

/-- The claims of the bindings of `m`, in the canonical order of the bindings; read only up to
order. -/
def claimsOf (g : K → V → Option L) (m : M) : List E := claimsL g (toList m)

/-- Every binding of `m` matches the fold's patterns (`T`: what they read twice is equal) and has
its claims defined. -/
def ClaimsDef (T : K → V → Prop) (g : K → V → Option L) (m : M) : Prop :=
  ∀ p ∈ toList m, T p.1 p.2 ∧ (g p.1 p.2).isSome

theorem claimsL_perm {g : K → V → Option L} {ps qs : List (K × V)} (h : ps.Perm qs) :
    (claimsL g ps).Perm (claimsL g qs) :=
  List.Perm.flatMap_right _ h

/-- The claims of a defined `M₁ M₂` are those of both operands, up to order. -/
theorem claimsOf_concat {g : K → V → Option L} {a b m : M} (h : concat a b = some m) :
    (claimsOf g m).Perm (claimsOf g a ++ claimsOf g b) := by
  have := claimsL_perm (g := g) (perm_toList_concat h)
  unfold claimsOf
  unfold claimsL at this ⊢
  rwa [List.flatMap_append] at this

/-- The count of a claim in a defined `M₁ M₂` is its counts in the operands. -/
theorem count_claimsOf_concat [BEq E] [LawfulBEq E] {g : K → V → Option L} {a b m : M}
    (h : concat a b = some m) (x : E) :
    (claimsOf g m).count x = (claimsOf g a).count x + (claimsOf g b).count x := by
  rw [(claimsOf_concat h).count_eq, List.count_append]

theorem claimsOf_element (g : K → V → Option L) (k : K) (v : V) :
    claimsOf g (element k v : M) = ((g k v).map toList).getD [] := by
  unfold claimsOf claimsL element
  rw [toList_ofList, List.flatMap_singleton]

theorem claimsOf_unit (g : K → V → Option L) : claimsOf g (unit : M) = [] := by
  unfold claimsOf claimsL unit
  rw [toList_ofList, List.flatMap_nil]

theorem claimsDef_concat {T : K → V → Prop} {g : K → V → Option L} {a b m : M} (h : concat a b = some m) :
    ClaimsDef T g m ↔ ClaimsDef T g a ∧ ClaimsDef T g b := by
  unfold ClaimsDef
  simp only [mem_toList_of_concat h]
  exact ⟨fun hm => ⟨fun p hp => hm p (.inl hp), fun p hp => hm p (.inr hp)⟩,
    fun ⟨ha, hb⟩ p hp => hp.elim (ha p) (hb p)⟩

theorem claimsDef_element {T : K → V → Prop} {g : K → V → Option L} {k : K} {v : V} :
    ClaimsDef T g (element k v : M) ↔ T k v ∧ (g k v).isSome := by
  unfold ClaimsDef element
  simp [toList_ofList]

theorem claimsDef_unit {T : K → V → Prop} {g : K → V → Option L} : ClaimsDef T g (unit : M) := by
  unfold ClaimsDef unit
  simp [toList_ofList]

/-- A fold that concatenates the claims of each binding, from its instances (`F.eq_instances`):
`F(.Map) => .List` and, at a nonempty map, a binding whose claims `a` are defined, the rest's `r`,
and `F`'s value one of `a r` or `r a`. Its value is then the claims of every binding, up to the
order of the walk, and each binding's claims are defined. By induction on the number of bindings,
the rest at a binding having one fewer. -/
theorem fold_claims {F : M → Option L} {T : K → V → Prop} {g : K → V → Option L}
    (h1 : F unit = some (ListHook.unit : L))
    (h2 : ∀ m l, m ≠ unit → F m = some l → WF m ∧ ∃ k v a r, (k, v) ∈ toList m ∧ T k v ∧
      g k v = some a ∧ F (remove m k) = some r ∧ (toList l).Perm (toList a ++ toList r))
    (m : M) (l : L) (h : F m = some l) : ClaimsDef T g m ∧ (toList l).Perm (claimsOf g m) := by
  suffices H : ∀ n (m : M) (l : L), (toList m).length = n → F m = some l →
      ClaimsDef T g m ∧ (toList l).Perm (claimsOf g m) from H _ m l rfl h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m l hn h
    by_cases hu : m = unit
    · subst hu
      rw [h1] at h
      cases h
      refine ⟨claimsDef_unit, ?_⟩
      rw [claimsOf_unit]
      unfold ListHook.unit
      rw [toList_ofList]
    obtain ⟨hw, k, v, a, r, hk, ht, hg, hr, hp⟩ := h2 m l hu h
    have hlt : (toList (remove m k)).length < n := by
      rw [← hn, (perm_toList_remove hw hk).length_eq, List.length_cons]
      exact Nat.lt_succ_self _
    obtain ⟨hd, hrp⟩ := ih _ hlt (remove m k) r rfl hr
    have hm := claimsL_perm (g := g) (perm_toList_remove hw hk)
    unfold claimsL at hm
    rw [List.flatMap_cons] at hm
    refine ⟨fun p hp => ?_, ?_⟩
    · rcases List.mem_cons.1 ((perm_toList_remove hw hk).mem_iff.1 hp) with rfl | hp
      · rw [hg]; exact ⟨ht, rfl⟩
      · exact hd p hp
    · refine hp.trans (List.Perm.trans ?_ hm.symm)
      rw [hg]
      exact List.Perm.append_left _ hrp

/-- The fold is defined wherever every binding's claims are: from its instances, at a nonempty
well-formed map whose every binding has defined claims and a defined rest, the fold is defined. -/
theorem fold_isSome {F : M → Option L} {T : K → V → Prop} {g : K → V → Option L}
    (h1 : F unit = some (ListHook.unit : L))
    (h3 : ∀ m, m ≠ unit → WF m → (∀ k v, (k, v) ∈ toList m → (T k v ∧ (g k v).isSome) ∧
      (F (remove m k)).isSome) → (F m).isSome)
    (m : M) (hw : WF m) (hd : ClaimsDef T g m) : (F m).isSome := by
  suffices H : ∀ n (m : M), (toList m).length = n → WF m → ClaimsDef T g m → (F m).isSome from
    H _ m rfl hw hd
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m hn hw hd
    by_cases hu : m = unit
    · subst hu; rw [h1]; rfl
    refine h3 m hu hw fun k v hk => ⟨hd (k, v) hk, ?_⟩
    have hlt : (toList (remove m k)).length < n := by
      rw [← hn, (perm_toList_remove hw hk).length_eq, List.length_cons]
      exact Nat.lt_succ_self _
    refine ih _ hlt (remove m k) rfl (wf_remove hw) fun p hp => hd p ?_
    rw [remove_def, toList_ofList] at hp
    exact SAL.mem_erase hp

/-- A list without repetition, of a list of parts: each part without repetition and two
different positions' parts sharing nothing; for a list of distinct parts, two distinct parts. -/
theorem nodup_flatMap_iff {α β : Type} {f : α → List β} {l : List α} (hl : l.Nodup) :
    (l.flatMap f).Nodup ↔
      (∀ a ∈ l, (f a).Nodup) ∧ (∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ x ∈ f a, x ∉ f b) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.1 hl
    rw [List.flatMap_cons, List.nodup_append, ih ht]
    constructor
    · rintro ⟨hfa, ⟨hft, hd⟩, hx⟩
      refine ⟨fun b hb => ?_, fun b hb c hc hne x hxb hxc => ?_⟩
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact hfa
        · exact hft b hb
      rcases List.mem_cons.1 hb with hb' | hb' <;> rcases List.mem_cons.1 hc with hc' | hc'
      · exact hne (hb'.trans hc'.symm)
      · subst hb'; exact hx x hxb x (List.mem_flatMap.2 ⟨c, hc', hxc⟩) rfl
      · subst hc'; exact hx x hxc x (List.mem_flatMap.2 ⟨b, hb', hxb⟩) rfl
      · exact hd b hb' c hc' hne x hxb hxc
    · rintro ⟨hf, hd⟩
      refine ⟨hf a (List.mem_cons_self ..), ⟨fun b hb => hf b (List.mem_cons_of_mem _ hb),
        fun b hb c hc hne => hd b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc) hne⟩,
        fun x hx y hy hxy => ?_⟩
      obtain ⟨b, hb, hyb⟩ := List.mem_flatMap.1 hy
      exact hd a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb)
        (fun h => ha (h ▸ hb)) x hx (hxy ▸ hyb)

/-- The order-free reading of the claims of a well-formed map without repetition: each binding's
claims have none, and two distinct bindings claim nothing in common. -/
theorem nodup_claimsOf_iff {g : K → V → Option L} {m : M} (hw : WF m) :
    (claimsOf g m).Nodup ↔
      (∀ p ∈ toList m, (((g p.1 p.2).map toList).getD []).Nodup) ∧
      (∀ p ∈ toList m, ∀ q ∈ toList m, p ≠ q →
        ∀ x ∈ ((g p.1 p.2).map toList).getD [], x ∉ ((g q.1 q.2).map toList).getD []) :=
  nodup_flatMap_iff (nodup_toList hw)

/-- A rule's case: what it writes claims, counted as a multiset, no more than what it removes,
so the claims stay without repetition. `omega` decides the counts over the claims of opaque
parts, after `List.count_append`. -/
theorem nodup_of_count_le [BEq E] [LawfulBEq E] {l l' : List E}
    (hc : ∀ x, l'.count x ≤ l.count x) (h : l.Nodup) : l'.Nodup :=
  List.nodup_iff_count.2 fun x => Nat.le_trans (hc x) (List.nodup_iff_count.1 h x)

end Claims

end MapHook

namespace ListHook

open ListIso

variable {L E : Type} [ListIso L E] [DecidableEq E]

/-- K's `noDup`, from its two equations (`noDup(.List) => true`, `noDup(ListItem(X) L) =>
notBool (X in L) andBool noDup(L)`): whether the list repeats no element. By induction on its
length. -/
theorem nodup_fn {D : L → Option Bool} (h1 : D unit = some true)
    (h2 : ∀ r x, D (concat (element x) r) = (D r).bind fun b => some (BoolHook.and (BoolHook.not (inList x r)) b))
    (l : L) : D l = some (decide (toList l).Nodup) := by
  suffices H : ∀ n (l : L), (toList l).length = n → D l = some (decide (toList l).Nodup) from H _ l rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro l hn
    cases hl : uncons l with
    | none =>
      have h0 : toList l = [] := by
        unfold uncons at hl
        split at hl
        · assumption
        · cases hl
      have hu : l = unit := by rw [← ofList_toList l, h0]; rfl
      subst hu
      rw [h1, h0]
      rfl
    | some p =>
      obtain ⟨x, r⟩ := p
      have hc := concat_element_of_uncons hl
      have ht : toList l = x :: toList r := by
        rw [← hc]; unfold concat element; rw [toList_ofList, toList_ofList]; rfl
      rw [← hc, h2 r x, hc, ih _ (by rw [← hn, ht]; exact Nat.lt_succ_self _) r rfl, ht]
      simp [BoolHook.and, BoolHook.not, inList, List.nodup_cons]

end ListHook

end KPrelude

/-! ## The closer of a rule's case

The invariant's element-wise form states `WF m ∧ ClaimsOK g m`: every binding's claims defined, and
no claim twice. `k2l_claims [U]` proves `ClaimsOK g m'` for a rule's rebuilt map `m'` from
`ClaimsOK g m` on the matched map and the rule's map facts `concat a b = some x`:
- the facts of the matched map's parts (`entry_of_concat_element`, `entriesOn_of_concat_right`, …):
  the matched element's claims are defined, and so are the frame's;
- definedness on `m'` by `entriesOn_concat` and `entriesOn_element` along its map facts;
- no repetition by counting: the claims a rule writes, counted, are no more than those it removes
  (`nodup_of_count_le`), the counts rewritten through every map fact (`count_claimsOf_concat`);
- each element's claims unfolded by `U` (the invariant's unfolding set: `g` and the K functions it
  calls), and each value of a function call that is left (`K.f args : Option _`) cased on: a branch
  where the matched element's claims would be undefined contradicts its fact.
What is left is an inequality of sums of counts of opaque lists, for `omega`. A claim made from
nothing (in no removed part) leaves the inequality false, so the case stays open: such a rule
needs the claim absent everywhere else, which is not local. -/

namespace KPrelude

namespace MapHook

open ListIso

variable {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V]
  [Std.TransOrd K] [Std.LawfulEqOrd K] {L E : Type} [ListIso L E]

/-- Every binding matching the fold's patterns (`T`) with its claims defined, the claims `o` of the
configuration's other parts defined, and no claim twice among all of them. -/
def ClaimsOK (T : K → V → Prop) (g : K → V → Option L) (m : M) (o : Option L) : Prop :=
  EntriesOn (fun p => T p.1 p.2 ∧ (g p.1 p.2).isSome = true) m ∧ o.isSome = true ∧
    (claimsOf g m ++ (o.map toList).getD []).Nodup

section Bridge

variable [DecidableEq E] {T : K → V → Prop} {g : K → V → Option L} {F : M → Option L} {D : L → Option Bool}

/-- The bridge from K's `noDup` of the fold (and of the other parts' claims, either side) to the
order-free `ClaimsOK`, from the fold's value up to order (`fold`), its definedness (`isSome`), the
well-formedness of a map it is defined on (`wf`), and `noDup`'s meaning (`hD`). -/
theorem claimsOK_iff_of (hD : ∀ l, D l = some (decide (toList l).Nodup))
    (fold : ∀ m l, F m = some l → ClaimsDef T g m ∧ (toList l).Perm (claimsOf g m))
    (wf : ∀ m l, F m = some l → WF m)
    (isSome : ∀ m, WF m → ClaimsDef T g m → (F m).isSome) (m : M) (o : Option L) :
    ((F m).bind fun r => o.bind fun r₁ => D (ListHook.concat r r₁)) = some true ↔
      WF m ∧ ClaimsOK T g m o := by
  constructor
  · intro h
    obtain ⟨l, hl, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨l₁, ho, hn⟩ := Option.bind_eq_some_iff.1 h
    rw [hD] at hn
    simp only [Option.some.injEq, decide_eq_true_eq, ListHook.concat, toList_ofList] at hn
    obtain ⟨hd, hp⟩ := fold m l hl
    refine ⟨wf m l hl, hd, by rw [ho]; rfl, ?_⟩
    rw [ho]
    exact (hp.append_right _).nodup_iff.1 hn
  · rintro ⟨hw, hd, ho, hn⟩
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 (isSome m hw hd)
    obtain ⟨l₁, rfl⟩ := Option.isSome_iff_exists.1 ho
    rw [hl, Option.bind_some, Option.bind_some, hD]
    simp only [ListHook.concat, toList_ofList, Option.some.injEq, decide_eq_true_eq]
    exact ((fold m l hl).2.append_right _).nodup_iff.2 hn

/-- The bridge with the other parts' claims first: `noDup(h(…) F(M))`. -/
theorem claimsOK_iff_of' (hD : ∀ l, D l = some (decide (toList l).Nodup))
    (fold : ∀ m l, F m = some l → ClaimsDef T g m ∧ (toList l).Perm (claimsOf g m))
    (wf : ∀ m l, F m = some l → WF m)
    (isSome : ∀ m, WF m → ClaimsDef T g m → (F m).isSome) (m : M) (o : Option L) :
    (o.bind fun r => (F m).bind fun r₁ => D (ListHook.concat r r₁)) = some true ↔
      WF m ∧ ClaimsOK T g m o := by
  rw [← claimsOK_iff_of hD fold wf isSome m o]
  cases o with
  | none => cases F m <;> rfl
  | some l₁ =>
    cases hF : F m with
    | none => rfl
    | some l =>
      simp only [Option.bind_some, hD, ListHook.concat, toList_ofList, Option.some.injEq,
        decide_eq_true_eq]
      exact List.perm_append_comm.nodup_iff

/-- The bridge with no other part: `noDup(F(M))`. -/
theorem claimsOK_iff_of_unit (hD : ∀ l, D l = some (decide (toList l).Nodup))
    (fold : ∀ m l, F m = some l → ClaimsDef T g m ∧ (toList l).Perm (claimsOf g m))
    (wf : ∀ m l, F m = some l → WF m)
    (isSome : ∀ m, WF m → ClaimsDef T g m → (F m).isSome) (m : M) :
    (F m).bind D = some true ↔ WF m ∧ ClaimsOK T g m (some ListHook.unit) := by
  rw [← claimsOK_iff_of hD fold wf isSome m]
  cases F m with
  | none => rfl
  | some l =>
    simp only [Option.bind_some, hD, ListHook.concat, ListHook.unit, toList_ofList, List.append_nil]

end Bridge

end MapHook

namespace InvDisjoint

open Lean Elab Tactic Meta

/-- `MapHook.concat a b = some m`: `(a, b, m)`. -/
def concatEq? (ty : Expr) : Option (Expr × Expr × Expr) := do
  let some (_, l, r) := ty.eq? | none
  let n := l.getAppNumArgs
  unless l.isAppOf ``KPrelude.MapHook.concat && n ≥ 2 && r.isAppOfArity ``Option.some 2 do none
  some (l.getArg! (n - 2), l.getArg! (n - 1), r.appArg!)

/-- An `Option`-valued call that a simp normal form keeps (`Option.bind e _`, `Option.map _ e`,
`Option.getD e _`, `Option.isSome e`), `e` a call of a function other than `Option`'s own with
no bound variable. -/
partial def optionAtom? (e : Expr) : Option Expr :=
  let isAtom (o : Expr) : Bool :=
    !o.hasLooseBVars && match o.getAppFn.constName? with
      | some c => c.getPrefix != `Option && c != ``ite && c != ``dite
      | none => false
  let here : Option Expr :=
    if e.isAppOfArity ``Option.bind 4 && isAtom (e.getArg! 2) then some (e.getArg! 2)
    else if e.isAppOfArity ``Option.map 4 && isAtom (e.getArg! 3) then some (e.getArg! 3)
    else if e.isAppOfArity ``Option.getD 3 && isAtom (e.getArg! 1) then some (e.getArg! 1)
    else if e.isAppOfArity ``Option.isSome 2 && isAtom (e.getArg! 1) then some (e.getArg! 1)
    else none
  match here with
  | some a => some a
  | none =>
    match e with
    | .app f a => (optionAtom? f).orElse fun _ => optionAtom? a
    | .lam _ t b _ => (optionAtom? t).orElse fun _ => optionAtom? b
    | .mdata _ b => optionAtom? b
    | _ => none

/-- The local declarations of goal `g` whose types satisfy `p`. -/
def hypsWith (g : MVarId) (p : Expr → Bool) : MetaM (Array (FVarId × Expr)) := g.withContext do
  let mut acc := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if p ty then acc := acc.push (d.fvarId, ty)
  return acc

/-- The hypotheses `k2l_claims` asserted (`k2l_part_*`, `k2l_opt*`): its simp locations, so that the
rest of a rule's context (the collections closer's facts) is left alone. -/
def ownHyps (g : MVarId) : MetaM (Array Ident) := g.withContext do
  let mut acc := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let n := d.userName.eraseMacroScopes.toString
    if (n.startsWith "k2l_part_" || n.startsWith "k2l_opt") && !d.userName.hasMacroScopes then
      acc := acc.push (mkIdent d.userName)
  return acc

/-- `simp only [args] at` the goal and `ownHyps`, on every goal, failures ignored. -/
def simpOwn (args : Array (TSyntax [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma])) : TacticM Unit := do
  let mut out : List MVarId := []
  for g in ← getGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    let hs ← ownHyps g
    let s ← saveState
    try evalTactic (← `(tactic| simp only [$args,*] at $hs* ⊢))
    catch _ => s.restore
    out := out ++ (← getGoals)
  setGoals out

/-- Case on the `Option`-valued calls of the goal and the hypotheses (`optionAtom?`), at most `n`
deep, simplifying each branch everywhere: a branch where a defined value is `none` closes. -/
partial def optionCases (n : Nat) : TacticM Unit := do
  if n = 0 then return
  let mut out : List MVarId := []
  for g in ← getGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    let atom ← g.withContext do
      let mut found := optionAtom? (← instantiateMVars (← g.getType))
      if found.isNone then
        for (_, ty) in ← hypsWith g fun _ => true do
          if let some a := optionAtom? ty then
            found := some a
            break
      return found
    let some a := atom | out := out ++ [g]; continue
    let stx ← g.withContext (Term.exprToSyntax a)
    let h := mkIdent `k2l_opt
    evalTactic (← `(tactic| cases $h:ident : $stx))
    simpOwn #[← `(Lean.Parser.Tactic.simpLemma| $h:ident), ← `(Lean.Parser.Tactic.simpLemma| Option.bind_some), ← `(Lean.Parser.Tactic.simpLemma| Option.bind_none),
      ← `(Lean.Parser.Tactic.simpLemma| Option.map_some), ← `(Lean.Parser.Tactic.simpLemma| Option.map_none),
      ← `(Lean.Parser.Tactic.simpLemma| Option.getD_some), ← `(Lean.Parser.Tactic.simpLemma| Option.getD_none),
      ← `(Lean.Parser.Tactic.simpLemma| Option.isSome_some), ← `(Lean.Parser.Tactic.simpLemma| Option.isSome_none),
      ← `(Lean.Parser.Tactic.simpLemma| Bool.false_eq_true), ← `(Lean.Parser.Tactic.simpLemma| Option.some.injEq),
      ← `(Lean.Parser.Tactic.simpLemma| reduceCtorEq), ← `(Lean.Parser.Tactic.simpLemma| ite_true),
      ← `(Lean.Parser.Tactic.simpLemma| ite_false), ← `(Lean.Parser.Tactic.simpLemma| ↓reduceIte)]
    optionCases (n - 1)
    out := out ++ (← getGoals)
  setGoals out

/-- Rewrite every `count x (claimsOf g m)` of the goal through the hypotheses `concat a b = some m`
until none applies. -/
def countConcat : TacticM Unit := do
  let mut changed := true
  let mut fuel := 64
  while changed && fuel > 0 do
    changed := false
    fuel := fuel - 1
    let g ← getMainGoal
    for (h, _) in ← hypsWith g fun ty => (concatEq? ty).isSome do
      let s ← saveState
      try
        let n ← g.withContext h.getUserName
        evalTactic (← `(tactic| rw [KPrelude.MapHook.count_claimsOf_concat $(mkIdent n)]))
        changed := true
      catch _ => s.restore

/-- The facts of the matched map's parts: for `EntriesOn Q m` and each `concat a b = some m`, `Q (k, v)`
for an operand `element k v`, `EntriesOn Q x` for another operand `x`. -/
def partFacts (hd : FVarId) : TacticM Unit := do
  let g ← getMainGoal
  let new ← g.withContext do
    let mut out : Array (Expr × Expr) := #[]
    for (hc, ty) in ← hypsWith g fun ty => (concatEq? ty).isSome do
      let some (a, b, _) := concatEq? ty | continue
      for (left, x) in [(true, a), (false, b)] do
        let lem : Name :=
          if x.isAppOf ``KPrelude.MapHook.element then
            if left then ``KPrelude.MapHook.entry_of_concat_element
            else ``KPrelude.MapHook.entry_of_concat_element_right
          else if left then ``KPrelude.MapHook.entriesOn_of_concat_left
          else ``KPrelude.MapHook.entriesOn_of_concat_right
        try
          let pf ← mkAppM lem #[.fvar hc, .fvar hd]
          out := out.push (← instantiateMVars (← inferType pf), pf)
        catch _ => pure ()
    return out
  if new.isEmpty then return
  let hs : Array Hypothesis := new.mapIdx fun i (ty, pf) =>
    { userName := Name.mkSimple s!"k2l_part_{i}", type := ty, value := pf }
  let (_, g') ← g.assertHypotheses hs
  setGoals [g']

/-- `k2l_claims [U]`: `ClaimsOK g m'` of a rule's rebuilt map (above). -/
syntax (name := k2lClaims) "k2l_claims" " [" Lean.Parser.Tactic.simpArg,* "]" : tactic

/-- `k2l_claims_trace [U]`: `k2l_claims` up to the arithmetic, the goals left shown (debugging). -/
syntax (name := k2lClaimsTrace) "k2l_claims_trace" " [" Lean.Parser.Tactic.simpArg,* "]" : tactic

@[tactic k2lClaims, tactic k2lClaimsTrace] def evalK2lClaims : Tactic := fun stx => do
  let finish := stx.getKind == ``k2lClaims
  let U : Array (TSyntax [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma]) := stx[2].getSepArgs.map (⟨·⟩)
  let (cd, co, cn) := (mkIdent `k2l_cd, mkIdent `k2l_co, mkIdent `k2l_cn)
  -- the matched map's `ClaimsOK`, whole or already split into its parts
  let g ← getMainGoal
  if let some (h, _) := (← hypsWith g fun ty => ty.isAppOf ``KPrelude.MapHook.ClaimsOK).back? then
    let hn ← g.withContext h.getUserName
    evalTactic (← `(tactic| obtain ⟨$cd, $co, $cn⟩ := $(mkIdent hn)))
  else
    -- `(claimsOf g m ++ …).Nodup`
    let claimsArg? (ty : Expr) : Option Expr :=
      if ty.isAppOfArity ``List.Nodup 2 && (ty.getArg! 1).isAppOfArity ``HAppend.hAppend 6 then
        let c := (ty.getArg! 1).getArg! 4
        if c.isAppOf ``KPrelude.MapHook.claimsOf then some c else none
      else none
    let some (h, ty) := (← hypsWith g fun t => (claimsArg? t).isSome).back?
      | throwError "k2l_claims: no hypothesis `ClaimsOK g m o`"
    let some c := claimsArg? ty | throwError "k2l_claims: no claims"
    let m := c.appArg!
    let some (hd, _) := (← hypsWith g fun t => t.isAppOf ``KPrelude.MapHook.EntriesOn && t.appArg! == m).back?
      | throwError "k2l_claims: no definedness fact on the matched map"
    let (hn, hdn) ← g.withContext do return (← h.getUserName, ← hd.getUserName)
    evalTactic (← `(tactic| (have $cn := $(mkIdent hn); have $cd := $(mkIdent hdn))))
  let some (hd, _) := (← hypsWith (← getMainGoal) fun ty => ty.isAppOf ``KPrelude.MapHook.EntriesOn).back?
    | throwError "k2l_claims: no definedness fact"
  partFacts hd
  evalTactic (← `(tactic| refine ⟨?_, ?_, KPrelude.MapHook.nodup_of_count_le (fun _ => ?_) $cn⟩))
  let [gd, go, gc] ← getGoals | throwError "k2l_claims: unexpected goals"
  -- definedness on the rebuilt map, along its map facts
  setGoals [gd]
  evalTactic (← `(tactic| repeat' (first | assumption | apply KPrelude.MapHook.entriesOn_element | refine KPrelude.MapHook.entriesOn_concat ‹_› ?_ ?_)))
  let gds ← getGoals
  -- the counts, through every map fact
  setGoals [gc]
  evalTactic (← `(tactic| simp only [List.count_append]))
  countConcat
  setGoals (gds ++ [go] ++ (← getGoals))
  evalTactic (← `(tactic| all_goals (try dsimp only)))
  let lem (n : Name) : TacticM (TSyntax [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
      `Lean.Parser.Tactic.simpLemma]) := do
    return ⟨(← `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)).raw⟩
  let base ← [``KPrelude.MapHook.claimsOf_element, ``KPrelude.MapHook.claimsOf_unit,
    ``KPrelude.ListHook.concat, ``KPrelude.ListHook.element, ``KPrelude.ListHook.unit,
    ``KPrelude.ListIso.toList_ofList, ``List.count_append, ``List.count_nil, ``Option.bind_fun_some,
    ``eq_self_iff_true, ``ite_true, ``ite_false].toArray.mapM lem
  simpOwn (base ++ U ++ #[⟨(← `(Lean.Parser.Tactic.simpLemma| ↓reduceIte)).raw⟩])
  optionCases 6
  simpOwn (← [``KPrelude.ListHook.concat, ``KPrelude.ListIso.toList_ofList, ``List.count_append,
    ``List.count_nil, ``List.count_cons, ``Option.isSome_some, ``Option.getD_some, ``Option.map_some,
    ``Option.getD_none, ``Option.map_none].toArray.mapM lem)
  if finish then evalTactic (← `(tactic| all_goals first | rfl | omega))
  else evalTactic (← `(tactic| trace_state))

end InvDisjoint

end KPrelude
