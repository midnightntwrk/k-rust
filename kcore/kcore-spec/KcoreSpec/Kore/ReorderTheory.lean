/-
  Reordering a module's sentences keeps the models of the translated theory (checked layer,
  generic): `reordered_sameModels` below, for KORE definitions whose declared names are distinct
  and whose `\rewrites` and `\next` axioms have no sort variables. Kept from F0's ReorderTheory
  when F0 was removed (P1.4); F0's lemma that its `emit` meets the second condition was not kept,
  and the core's counterpart is not yet proved. F0's account follows.

  Where the translation reads the order, and why it does not matter:
  - the declarations, the aliases, the axioms and the literals are read as lists; reordering
    permutes them (`reordered_flatMap`), and every item but two is a `map` over one of them, so
    the set of patterns is the same;
  - a symbol's declaration is found by name, first match (`sortOfApp`); with the names declared
    once the match is unique, so it is the same in any order (`find?_perm`);
  - the aliases are read by membership (`tr_aliases`);
  - G-sorts is one pattern, a least fixpoint over the disjunction of the sort declarations in text
    order: the patterns differ, their interpretations do not (`disjList_perm`);
  - the G-next-arity items keep, for each sort of a `\rewrites` or `\next`, the sort variables of
    the first axiom that has it.
-/
import KcoreSpec.Kore.Reorder
import KcoreSpec.Kore.Translate
import KcoreSpec.Kore.Base

set_option autoImplicit false

namespace KoreAML.ReorderTheory

open ML KoreAML



/-! ## Reordering permutes what the translation reads -/

theorem reordered_flatMap {α : Type} {e k : Kore.Definition} (h : Reordered e k)
    (F : Kore.Module → List α)
    (hF : ∀ m m', m.name = m'.name → m.sentences.Perm m'.sentences → (F m).Perm (F m')) :
    (e.modules.flatMap F).Perm (k.modules.flatMap F) := by
  obtain ⟨-, hlen, hz⟩ := h
  revert hlen hz
  generalize e.modules = es
  generalize k.modules = ks
  intro hlen hz
  induction es generalizing ks with
  | nil =>
    cases ks with
    | nil => exact List.Perm.refl _
    | cons _ _ => simp at hlen
  | cons a as ih =>
    cases ks with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.zip_cons_cons, List.mem_cons, forall_eq_or_imp] at hz
      simp only [List.flatMap_cons]
      exact (hF a b hz.1.1 hz.1.2.2).append
        (ih bs (by simpa using hlen) hz.2)

theorem perm_filterMap_sentences {α : Type} {e k : Kore.Definition} (h : Reordered e k)
    (g : Kore.Sentence → Option α) :
    (e.modules.flatMap fun m => m.sentences.filterMap g).Perm
      (k.modules.flatMap fun m => m.sentences.filterMap g) :=
  reordered_flatMap h _ fun _ _ _ hp => hp.filterMap g

theorem sortDecls_perm {e k : Kore.Definition} (h : Reordered e k) :
    e.sortDecls.Perm k.sortDecls := perm_filterMap_sentences h _

theorem symbolDecls_perm {e k : Kore.Definition} (h : Reordered e k) :
    e.symbolDecls.Perm k.symbolDecls := perm_filterMap_sentences h _

theorem aliasNames_perm {e k : Kore.Definition} (h : Reordered e k) :
    e.aliasNames.Perm k.aliasNames := perm_filterMap_sentences h _

/-- The axioms of a definition, in text order. -/
def axiomsOf (d : Kore.Definition) : List Kore.Axiom :=
  d.modules.flatMap fun m => m.sentences.filterMap fun
    | .axiom a => some a
    | _ => none

theorem axiomDecls_ax (d : Kore.Definition) : d.axiomDecls.map (·.ax) = axiomsOf d := by
  unfold Kore.Definition.axiomDecls axiomsOf
  generalize hraw : (d.modules.flatMap fun m => m.sentences.filterMap fun
    | .axiom a => some (m.name.ident.name, a)
    | _ => none) = raw
  have hr : raw.map (·.2) = d.modules.flatMap fun m => m.sentences.filterMap fun
      | .axiom a => some a
      | _ => none := by
    rw [← hraw, List.map_flatMap]
    congr 1; funext m
    rw [List.map_filterMap]
    congr 1; funext s
    cases s <;> rfl
  rw [← hr, List.map_map]
  have : ((List.range raw.length).zip raw).map Prod.snd = raw :=
    List.map_snd_zip (by simp)
  conv => rhs; rw [← this]
  rw [List.map_map]
  rfl

theorem axioms_perm {e k : Kore.Definition} (h : Reordered e k) :
    (axiomsOf e).Perm (axiomsOf k) := perm_filterMap_sentences h _

theorem Reordered.symm' {e k : Kore.Definition} (h : Reordered e k) : Reordered k e := by
  obtain ⟨ha, hlen, hz⟩ := h
  refine ⟨ha.symm, hlen.symm, ?_⟩
  revert hlen hz
  generalize e.modules = es
  generalize k.modules = ks
  intro hlen hz
  induction es generalizing ks with
  | nil => cases ks <;> simp_all
  | cons a as ih =>
    cases ks with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.zip_cons_cons, List.mem_cons, forall_eq_or_imp] at hz ⊢
      exact ⟨⟨hz.1.1.symm, hz.1.2.1.symm, hz.1.2.2.symm⟩, ih bs (by simpa using hlen) hz.2⟩

/-! ## The order-free parts of the theory -/

/-- The patterns of a list of items. -/
abbrev pats (L : List Item) : List P := L.map (·.pat)

theorem pats_perm {α : Type} {f : α → Item} {l l' : List α} (hp : l.Perm l') {φ : P}
    (h : φ ∈ pats (l.map f)) : φ ∈ pats (l'.map f) :=
  ((hp.map f).map _).mem_iff.mp h

theorem axiomDecls_flatMap {β : Type} (D : Kore.Definition) (G : Kore.Axiom → List β) :
    D.axiomDecls.flatMap (fun ad => G ad.ax) = (axiomsOf D).flatMap G := by
  rw [← axiomDecls_ax, List.flatMap_map]

/-- Every axiom with a `\rewrites` or `\next` has no sort variables. -/
def NextOK (D : Kore.Definition) : Prop :=
  ∀ a ∈ axiomsOf D, a.sortVars = [] ∨ nextSortsOf a.pattern = []

theorem NextOK.perm {e k : Kore.Definition} (h : Reordered e k) (hx : NextOK e) : NextOK k :=
  fun a ha => hx a ((axioms_perm h).mem_iff.mpr ha)

/-- The pairs (sort variables, sort) G-next-arity reads, before removing repeated sorts. -/
def nextPairs (D : Kore.Definition) : List (List Kore.SortVar × Kore.KSort) :=
  (axiomsOf D).flatMap fun a => (nextSortsOf a.pattern).map (a.sortVars, ·)

theorem nextPairs_nil {D : Kore.Definition} (hx : NextOK D) : ∀ y ∈ nextPairs D, y.1 = [] := by
  intro y hy
  simp only [nextPairs, List.mem_flatMap, List.mem_map] at hy
  obtain ⟨a, ha, s, hs, rfl⟩ := hy
  rcases hx a ha with h | h
  · exact h
  · rw [h] at hs; cases hs

theorem foldl_dedup_mem {α β : Type} [DecidableEq β] (c : α) :
    ∀ (l acc : List (α × β)), (∀ y ∈ acc ++ l, y.1 = c) → ∀ x,
      x ∈ l.foldl (fun acc x => if acc.any (fun y => decide (y.2 = x.2)) then acc else acc ++ [x]) acc ↔
        x ∈ acc ∨ x ∈ l
  | [], acc, _, x => by simp
  | a :: l, acc, hc, x => by
    rw [List.foldl_cons]
    split
    · next hany =>
      rw [foldl_dedup_mem c l acc (fun y hy => hc y (by
        rcases List.mem_append.mp hy with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h))) x]
      obtain ⟨y, hy, hya⟩ := List.any_eq_true.mp hany
      have hyeq : y = a := Prod.ext ((hc y (List.mem_append_left _ hy)).trans
        (hc a (List.mem_append_right _ List.mem_cons_self)).symm) (of_decide_eq_true hya)
      subst hyeq
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · exact Or.inl h
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl hy
          · exact Or.inr h
    · rw [foldl_dedup_mem c l (acc ++ [a]) (fun y hy => hc y (by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
        rcases hy with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h))) x]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

theorem nextSorts_mem {D : Kore.Definition} (hx : NextOK D) (x) :
    x ∈ ((D.axiomDecls.flatMap fun ad => (nextSortsOf ad.ax.pattern).map (ad.ax.sortVars, ·))
      |>.foldl (fun acc x => if acc.any (fun y => decide (y.2 = x.2)) then acc else acc ++ [x]) [])
      ↔ x ∈ nextPairs D := by
  rw [axiomDecls_flatMap D (fun a => (nextSortsOf a.pattern).map (a.sortVars, ·))]
  rw [foldl_dedup_mem [] _ [] (fun y hy => by
    rw [List.nil_append] at hy; exact nextPairs_nil hx y hy) x]
  simp only [List.not_mem_nil, false_or]
  rfl

theorem nextPairs_perm {e k : Kore.Definition} (h : Reordered e k) :
    (nextPairs e).Perm (nextPairs k) := (axioms_perm h).flatMap_right _

/-! ## G-sorts: permuted disjunctions have the same interpretation -/

theorem disjList_interpret {M : Type} (I : Interpretation Sym M) (ev : Valuation M) (m : M) :
    ∀ l : List P, (disjList l).interpret I ev m ↔ ∃ φ ∈ l, φ.interpret I ev m
  | [] => by simp [disjList]
  | [φ] => by simp [disjList]
  | φ :: ψ :: l => by
    show (φ ⋁ disjList (ψ :: l)).interpret I ev m ↔ _
    rw [interpret_disj, disjList_interpret I ev m (ψ :: l)]
    simp only [List.mem_cons, exists_eq_or_imp]

theorem disjList_perm {M : Type} (I : Interpretation Sym M) {l l' : List P} (hp : l.Perm l')
    (ev : Valuation M) : (disjList l).interpret I ev = (disjList l').interpret I ev := by
  funext m
  apply propext
  rw [disjList_interpret, disjList_interpret]
  exact ⟨fun ⟨φ, h, h'⟩ => ⟨φ, hp.mem_iff.mp h, h'⟩, fun ⟨φ, h, h'⟩ => ⟨φ, hp.mem_iff.mpr h, h'⟩⟩

theorem sortsItem_perm {M : Type} (I : Interpretation Sym M) {l l' : List SortDecl}
    (hp : l.Perm l') (ev : Valuation M) :
    (sortsItem l).pat.interpret I ev = (sortsItem l').pat.interpret I ev := by
  have hd := fun ev => disjList_perm I (hp.map (fun sd => appList (sym (.sort sd.name))
    (sd.params.map fun _ => .svar (⟨1⟩ : SVar)))) ev
  simp only [sortsItem, equal, total, Pattern.equivalence, Pattern.conjunction,
    Pattern.disjunction, Pattern.negation, Pattern.interpret, hd]
  rfl

/-! ## The first declaration of a name is the only one -/

theorem nodup_true_iff : ∀ (l : List String), nodup l = true ↔ l.Nodup
  | [] => by simp [nodup]
  | a :: l => by
    simp only [nodup, Bool.and_eq_true, Bool.not_eq_true', List.nodup_cons, nodup_true_iff l]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun hm => ?_, h2⟩
      rw [List.contains_iff_mem.mpr hm] at h1
      cases h1
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      cases hc : l.contains a with
      | false => rfl
      | true => exact absurd (List.contains_iff_mem.mp hc) h1

theorem inj_of_nodup_map {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => absurd hx List.not_mem_nil
  | a :: l, h, x, y, hx, hy, hxy => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hx with hxa | hxl <;> rcases List.mem_cons.mp hy with hya | hyl
    · rw [hxa, hya]
    · subst hxa; exact absurd (hxy ▸ List.mem_map_of_mem hyl) h.1
    · subst hya; exact absurd (hxy.symm ▸ List.mem_map_of_mem hxl) h.1
    · exact inj_of_nodup_map h.2 hxl hyl hxy

theorem find?_perm {l l' : List SymbolDecl} (hp : l.Perm l') (hn : (l.map (·.name)).Nodup)
    (n : String) : l.find? (·.name == n) = l'.find? (·.name == n) := by
  have hn' : (l'.map (·.name)).Nodup := (hp.map _).nodup_iff.mp hn
  cases h1 : l.find? (·.name == n) with
  | none =>
    symm
    rw [List.find?_eq_none] at h1 ⊢
    intro x hx
    exact h1 x (hp.mem_iff.mpr hx)
  | some x =>
    have hx := List.mem_of_find?_eq_some h1
    have hpx := List.find?_some h1
    cases h2 : l'.find? (·.name == n) with
    | none =>
      rw [List.find?_eq_none] at h2
      exact absurd hpx (h2 x (hp.mem_iff.mp hx))
    | some y =>
      have hy := List.mem_of_find?_eq_some h2
      have hpy := List.find?_some h2
      simp only [beq_iff_eq] at hpx hpy
      congr 1
      exact inj_of_nodup_map hn' (hp.mem_iff.mp hx) hy (hpx.trans hpy.symm)

theorem sortOf_perm {l l' : List SymbolDecl} (hp : l.Perm l') (hn : (l.map (·.name)).Nodup)
    (p : Kore.Pattern) : sortOf l p = sortOf l' p := by
  cases p <;> simp only [sortOf, sortOfApp, find?_perm hp hn]

/-! ## The aliases are read by membership -/

mutual
  theorem tr_aliases (t : VarTable) {a a' : List String} (ha : ∀ n, a.contains n = a'.contains n) :
      ∀ p : Kore.Pattern, tr ⟨t, a⟩ p = tr ⟨t, a'⟩ p
    | .var (.evar _) | .var (.svar _) | .string _ | .top _ | .bottom _ | .dv _ _ => by simp only [tr]
    | .app h ss ps => by simp only [tr, ha, trArgs_aliases t ha]
    | .not _ p | .next _ p | .exist _ _ p | .forall _ _ p | .mu _ p | .nu _ p => by
      simp only [tr, tr_aliases t ha p]
    | .ceil _ _ p | .floor _ _ p => by simp only [tr, tr_aliases t ha p]
    | .and _ ps => by simp only [tr, trAndList_aliases t ha]
    | .or _ ps => by simp only [tr, trOrList_aliases t ha]
    | .implies _ p q | .iff _ p q | .rewrites _ p q | .equals _ _ p q | .in _ _ p q => by
      simp only [tr, tr_aliases t ha p, tr_aliases t ha q]
    | .leftAssoc _ _ ps => by simp only [tr, trLeftAssoc_aliases t ha]
    | .rightAssoc _ _ ps => by simp only [tr, trRightAssoc_aliases t ha]
    termination_by structural p => p
  theorem trArgs_aliases (t : VarTable) {a a' : List String} (ha : ∀ n, a.contains n = a'.contains n) :
      ∀ (acc : P) (ps : List Kore.Pattern), trArgs ⟨t, a⟩ acc ps = trArgs ⟨t, a'⟩ acc ps
    | _, [] => by simp only [trArgs]
    | acc, p :: ps => by simp only [trArgs, tr_aliases t ha p, trArgs_aliases t ha _ ps]
    termination_by structural _ ps => ps
  theorem trAndList_aliases (t : VarTable) {a a' : List String} (ha : ∀ n, a.contains n = a'.contains n) :
      ∀ (s : P) (ps : List Kore.Pattern), trAndList ⟨t, a⟩ s ps = trAndList ⟨t, a'⟩ s ps
    | _, [] => by simp only [trAndList]
    | s, p :: ps => by
      cases ps with
      | nil => simp only [trAndList, tr_aliases t ha p]
      | cons q qs =>
        show sAnd _ (trAndList _ s (q :: qs)) = sAnd _ (trAndList _ s (q :: qs))
        rw [tr_aliases t ha p, trAndList_aliases t ha s (q :: qs)]
    termination_by structural _ ps => ps
  theorem trOrList_aliases (t : VarTable) {a a' : List String} (ha : ∀ n, a.contains n = a'.contains n) :
      ∀ (s : P) (ps : List Kore.Pattern), trOrList ⟨t, a⟩ s ps = trOrList ⟨t, a'⟩ s ps
    | _, [] => by simp only [trOrList]
    | s, p :: ps => by
      cases ps with
      | nil => simp only [trOrList, tr_aliases t ha p]
      | cons q qs =>
        show sOr s _ (trOrList _ s (q :: qs)) = sOr s _ (trOrList _ s (q :: qs))
        rw [tr_aliases t ha p, trOrList_aliases t ha s (q :: qs)]
    termination_by structural _ ps => ps
  theorem trLeftAssoc_aliases (t : VarTable) {a a' : List String} (ha : ∀ n, a.contains n = a'.contains n) :
      ∀ (head : P) (ps : List Kore.Pattern), trLeftAssoc ⟨t, a⟩ head ps = trLeftAssoc ⟨t, a'⟩ head ps
    | _, [] => by simp only [trLeftAssoc]
    | head, p :: ps => by
      simp only [trLeftAssoc, tr_aliases t ha p, trLeftAssocRest_aliases t ha head _ ps]
    termination_by structural _ ps => ps
  theorem trLeftAssocRest_aliases (t : VarTable) {a a' : List String}
      (ha : ∀ n, a.contains n = a'.contains n) :
      ∀ (head acc : P) (ps : List Kore.Pattern),
        trLeftAssocRest ⟨t, a⟩ head acc ps = trLeftAssocRest ⟨t, a'⟩ head acc ps
    | _, _, [] => by simp only [trLeftAssocRest]
    | head, acc, p :: ps => by
      simp only [trLeftAssocRest, tr_aliases t ha p, trLeftAssocRest_aliases t ha head _ ps]
    termination_by structural _ _ ps => ps
  theorem trRightAssoc_aliases (t : VarTable) {a a' : List String} (ha : ∀ n, a.contains n = a'.contains n) :
      ∀ (head : P) (ps : List Kore.Pattern), trRightAssoc ⟨t, a⟩ head ps = trRightAssoc ⟨t, a'⟩ head ps
    | _, [] => by simp only [trRightAssoc]
    | head, p :: ps => by
      cases ps with
      | nil => simp only [trRightAssoc, tr_aliases t ha p]
      | cons q qs =>
        show head ⬝ _ ⬝ trRightAssoc _ head (q :: qs) = head ⬝ _ ⬝ trRightAssoc _ head (q :: qs)
        rw [tr_aliases t ha p, trRightAssoc_aliases t ha head (q :: qs)]
    termination_by structural _ ps => ps
end

/-- The pattern of a translated axiom: everything of `trAxiom` but its label. -/
theorem trAxiom_pat {l l' : List SymbolDecl} {a a' : List String} (hp : l.Perm l')
    (hn : (l.map (·.name)).Nodup) (ha : a.Perm a') (ad ad' : AxiomDecl) (hax : ad.ax = ad'.ax) :
    (trAxiom l a ad).pat = (trAxiom l' a' ad').pat := by
  have hc : ∀ n, a.contains n = a'.contains n := fun n => by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]; exact ha.mem_iff
  simp only [trAxiom, hax, sortOf_perm hp hn, tr_aliases _ hc]

/-! ## Every pattern of one theory but G-sorts is a pattern of the other -/

theorem mem_pats_of {α : Type} {f : α → Item} {l l' : List α} {φ : P}
    (h : φ ∈ (l.map f).map (·.pat)) (hl : ∀ x ∈ l, x ∈ l') : φ ∈ (l'.map f).map (·.pat) := by
  obtain ⟨it, hit, rfl⟩ := List.mem_map.mp h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hit
  exact List.mem_map_of_mem (List.mem_map_of_mem (hl x hx))

theorem pats_sub {e k : Kore.Definition} (h : Reordered e k)
    (hn : (e.symbolDecls.map (·.name)).Nodup) (hx : NextOK e) (φ : P)
    (hφ : φ ∈ (Theory.ofDefinition e).all.map (·.pat)) :
    φ = (sortsItem e.sortDecls).pat ∨ φ ∈ (Theory.ofDefinition k).all.map (·.pat) := by
  have hxk := hx.perm h
  have hS := sortDecls_perm h
  have hY := symbolDecls_perm h
  have hA := aliasNames_perm h
  simp only [Theory.all, Theory.ofDefinition, List.map_append, List.mem_append, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hφ ⊢
  rcases hφ with ((((((((h0 | h1) | h2) | h3) | h4) | (h5 | h5')) | h6) | h7) | h8)
  · right; simp only [h0, true_or]
  · right; simp only [mem_pats_of h1 fun _ => hS.mem_iff.mp, true_or, or_true]
  · right; simp only [mem_pats_of h2 fun _ => hS.mem_iff.mp, true_or, or_true]
  · left; exact h3
  · right; simp only [mem_pats_of h4 fun _ => hY.mem_iff.mp, true_or, or_true]
  · right; simp only [h5, true_or, or_true]
  · right; simp only [h5', true_or, or_true]
  · right
    have := mem_pats_of h6 fun x hx' =>
      (nextSorts_mem hxk x).mpr ((nextPairs_perm h).mem_iff.mp ((nextSorts_mem hx x).mp hx'))
    simp only [this, true_or, or_true]
  · right
    have hl : ∀ x ∈ (e.axiomDecls.flatMap fun ad => dvLitsOf ad.ax.pattern).eraseDups,
        x ∈ (k.axiomDecls.flatMap fun ad => dvLitsOf ad.ax.pattern).eraseDups := by
      intro x hx'
      rw [List.mem_eraseDups, axiomDecls_flatMap e (fun a => dvLitsOf a.pattern)] at hx'
      rw [List.mem_eraseDups, axiomDecls_flatMap k (fun a => dvLitsOf a.pattern)]
      exact ((axioms_perm h).flatMap_right _).mem_iff.mp hx'
    have := mem_pats_of h7 hl
    simp only [this, true_or, or_true]
  · right
    obtain ⟨it, hit, rfl⟩ := List.mem_map.mp h8
    obtain ⟨ad, had, rfl⟩ := List.mem_map.mp hit
    have hae : ad.ax ∈ axiomsOf e := by rw [← axiomDecls_ax]; exact List.mem_map_of_mem had
    have hak : ad.ax ∈ (k.axiomDecls).map (·.ax) := by
      rw [axiomDecls_ax]; exact (axioms_perm h).mem_iff.mp hae
    obtain ⟨ad', had', hax⟩ := List.mem_map.mp hak
    have := List.mem_map_of_mem (f := Item.pat)
      (List.mem_map_of_mem (f := trAxiom k.symbolDecls k.aliasNames) had')
    rw [← trAxiom_pat hY hn hA ad ad' hax.symm] at this
    simp only [this, or_true]

theorem sortsItem_mem (D : Kore.Definition) :
    (sortsItem D.sortDecls).pat ∈ (Theory.ofDefinition D).all.map (·.pat) := by
  simp only [Theory.all, Theory.ofDefinition, List.map_append, List.mem_append, List.map_cons,
    List.mem_cons, true_or, or_true]

theorem satisfies_sub {e k : Kore.Definition} (h : Reordered e k)
    (hn : (e.symbolDecls.map (·.name)).Nodup) (hx : NextOK e) {M : Type}
    (I : Interpretation Sym M) (hI : I ⊧ᴵP (Theory.ofDefinition k).premises) :
    I ⊧ᴵP (Theory.ofDefinition e).premises := by
  intro γ hγ
  rcases hγ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
  · rcases pats_sub h hn hx it.pat (List.mem_map_of_mem hit) with hs | hk
    · rw [hs]
      have hsk : I ⊧ᴵ (sortsItem k.sortDecls).pat := by
        obtain ⟨it', hit', heq⟩ := List.mem_map.mp (sortsItem_mem k)
        exact hI _ (Or.inl ⟨it', hit', heq⟩)
      intro ev m
      rw [sortsItem_perm I (sortDecls_perm h) ev]
      exact hsk ev m
    · obtain ⟨it', hit', heq⟩ := List.mem_map.mp hk
      exact hI _ (Or.inl ⟨it', hit', heq⟩)
  · exact hI _ (Or.inr ⟨x, rfl⟩)

theorem sameModels_of_reordered {e k : Kore.Definition} (h : Reordered e k)
    (hn : (e.symbolDecls.map (·.name)).Nodup) (hx : NextOK e) :
    ∀ (M : Type) [Inhabited M] (I : Interpretation Sym M),
      I ⊧ᴵP (Theory.ofDefinition e).premises ↔ I ⊧ᴵP (Theory.ofDefinition k).premises :=
  fun _ _ I =>
    ⟨satisfies_sub (Reordered.symm' h) ((symbolDecls_perm h).map _ |>.nodup_iff.mp hn)
        (hx.perm h) I,
     satisfies_sub h hn hx I⟩

end KoreAML.ReorderTheory
