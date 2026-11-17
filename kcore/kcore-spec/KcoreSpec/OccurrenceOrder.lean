/-
  KCore. The translation of a KORE pattern reads the order in which its variables occur, not how
  they are spelled.

  `tableOf` numbers the variables of an axiom's pattern in order of first occurrence
  (`VarTable.index`), and `tr` writes a variable as its number. So two patterns that differ only in
  the spelling of their element and set variables, bound or free, with one order of occurrence,
  translate to one KoreAML pattern.

  - `renVars f g p`: p with each element variable `n : s` spelled `f n s` and each set variable
    `g n s`, binders included; sorts, sort variables and symbols as they are.
  - `tr_renVars`: under two tables that give each variable of p and its renamed key one index, the
    two patterns have one translation.
  - `tableOf_renVars`: where the renaming is one-to-one on the variables of p (with the declared
    sort variables), the table of the renamed pattern is the table of p, renamed.
  - `tr_occurrence_order`: such a renaming does not change the translation of the axiom's pattern
    under its own table.

  A sentence whose rule holds a binder is written by `Cond.kore` with the binder spelled `V<i>`
  (`Cond.binder`), whatever the text spells it; it is tied to the text's sentence through
  `tr_occurrence_order`, on the translated patterns, which hold no names.
-/
import KcoreSpec.Kore.Translate

set_option autoImplicit false

namespace KoreAML

open ML

/-- The element variable x spelled `f n s`, its sort as it is. -/
def renEVar (f : String → Kore.KSort → String) (x : Kore.EVar) : Kore.EVar :=
  ⟨⟨⟨f x.var.ident.name x.sort⟩⟩, x.sort⟩

/-- The set variable X spelled `g n s`, its sort as it is. -/
def renSVar (g : String → Kore.KSort → String) (X : Kore.SVar) : Kore.SVar :=
  ⟨⟨⟨g X.var.ident.name X.sort⟩⟩, X.sort⟩

/-- The key of a renamed variable; a sort variable's key is as it is. -/
def renKey (f g : String → Kore.KSort → String) : VarKey → VarKey
  | .sortVar n => .sortVar n
  | .evar n s => .evar (f n s) s
  | .svar n s => .svar (g n s) s

mutual
  /-- `p` with its element variables spelled by `f` and its set variables by `g` (name and sort to
  name), binders included, nothing else changed. -/
  def renVars (f g : String → Kore.KSort → String) : Kore.Pattern → Kore.Pattern
    | .var (.evar x) => .var (.evar (renEVar f x))
    | .var (.svar X) => .var (.svar (renSVar g X))
    | .app h ss ps => .app h ss (renVarsList f g ps)
    | .string s => .string s
    | .top s => .top s
    | .bottom s => .bottom s
    | .not s p => .not s (renVars f g p)
    | .and s ps => .and s (renVarsList f g ps)
    | .or s ps => .or s (renVarsList f g ps)
    | .implies s p q => .implies s (renVars f g p) (renVars f g q)
    | .iff s p q => .iff s (renVars f g p) (renVars f g q)
    | .exist s x p => .exist s (renEVar f x) (renVars f g p)
    | .forall s x p => .forall s (renEVar f x) (renVars f g p)
    | .mu X p => .mu (renSVar g X) (renVars f g p)
    | .nu X p => .nu (renSVar g X) (renVars f g p)
    | .ceil s s' p => .ceil s s' (renVars f g p)
    | .floor s s' p => .floor s s' (renVars f g p)
    | .equals s s' p q => .equals s s' (renVars f g p) (renVars f g q)
    | .in s s' p q => .in s s' (renVars f g p) (renVars f g q)
    | .next s p => .next s (renVars f g p)
    | .rewrites s p q => .rewrites s (renVars f g p) (renVars f g q)
    | .dv s l => .dv s l
    | .leftAssoc h ss ps => .leftAssoc h ss (renVarsList f g ps)
    | .rightAssoc h ss ps => .rightAssoc h ss (renVarsList f g ps)
    termination_by structural p => p
  def renVarsList (f g : String → Kore.KSort → String) : List Kore.Pattern → List Kore.Pattern
    | [] => []
    | p :: ps => renVars f g p :: renVarsList f g ps
    termination_by structural ps => ps
end

section
variable (f g : String → Kore.KSort → String)

theorem evarKey_renEVar (x : Kore.EVar) : evarKey (renEVar f x) = renKey f g (evarKey x) := rfl
theorem svarKey_renSVar (X : Kore.SVar) : svarKey (renSVar g X) = renKey f g (svarKey X) := rfl
theorem renKey_sortVarKey (α : Kore.SortVar) : renKey f g (sortVarKey α) = sortVarKey α := rfl

mutual
  /-- The keys of a sort are sort variables, which the renaming leaves. -/
  theorem sortVarsOf_renKey : ∀ (s : Kore.KSort), (sortVarsOf s).map (renKey f g) = sortVarsOf s
    | .var _ => rfl
    | .ctor _ args => by rw [sortVarsOf]; exact sortVarsOfList_renKey args
  theorem sortVarsOfList_renKey : ∀ (ss : List Kore.KSort),
      (sortVarsOfList ss).map (renKey f g) = sortVarsOfList ss
    | [] => rfl
    | s :: ss => by
      rw [sortVarsOfList, List.map_append, sortVarsOf_renKey s, sortVarsOfList_renKey ss]
end

mutual
  /-- **The variables of the renamed pattern are those of the pattern, renamed, in one order.** -/
  theorem varsOf_renVars : ∀ (p : Kore.Pattern),
      varsOf (renVars f g p) = (varsOf p).map (renKey f g)
    | .var (.evar x) => by
      simp only [renVars, varsOf, List.map_append, List.map_cons, List.map_nil]
      rw [sortVarsOf_renKey]; rfl
    | .var (.svar X) => by
      simp only [renVars, varsOf, List.map_append, List.map_cons, List.map_nil]
      rw [sortVarsOf_renKey]; rfl
    | .app _ ss ps | .leftAssoc _ ss ps | .rightAssoc _ ss ps => by
      simp only [renVars, varsOf, List.map_append]
      rw [sortVarsOfList_renKey, varsOfList_renVars ps]
    | .string _ => rfl
    | .top s | .bottom s | .dv s _ => by
      simp only [renVars, varsOf]; rw [sortVarsOf_renKey]
    | .not s p | .next s p => by
      simp only [renVars, varsOf, List.map_append]
      rw [sortVarsOf_renKey, varsOf_renVars p]
    | .and s ps | .or s ps => by
      simp only [renVars, varsOf, List.map_append]
      rw [sortVarsOf_renKey, varsOfList_renVars ps]
    | .implies s p q | .iff s p q | .rewrites s p q => by
      simp only [renVars, varsOf, List.map_append]
      rw [sortVarsOf_renKey, varsOf_renVars p, varsOf_renVars q]
    | .exist s x p | .forall s x p => by
      simp only [renVars, varsOf, List.map_append, List.map_cons, List.map_nil]
      rw [sortVarsOf_renKey, sortVarsOf_renKey, varsOf_renVars p]; rfl
    | .mu X p | .nu X p => by
      simp only [renVars, varsOf, List.map_append, List.map_cons, List.map_nil]
      rw [sortVarsOf_renKey, varsOf_renVars p]; rfl
    | .ceil s s' p | .floor s s' p => by
      simp only [renVars, varsOf, List.map_append]
      rw [sortVarsOf_renKey, sortVarsOf_renKey, varsOf_renVars p]
    | .equals s s' p q | .in s s' p q => by
      simp only [renVars, varsOf, List.map_append]
      rw [sortVarsOf_renKey, sortVarsOf_renKey, varsOf_renVars p, varsOf_renVars q]
  theorem varsOfList_renVars : ∀ (ps : List Kore.Pattern),
      varsOfList (renVarsList f g ps) = (varsOfList ps).map (renKey f g)
    | [] => rfl
    | p :: ps => by
      rw [renVarsList, varsOfList, varsOfList, List.map_append, varsOf_renVars p,
        varsOfList_renVars ps]
end

/-! ## One translation under two tables that agree on the pattern's variables -/

/-- A key is among the keys of a pattern, of a list of patterns or of sorts, by their equations. -/
macro "occ_vmem" : tactic =>
  `(tactic| (simp only [varsOf, varsOfList, sortVarsOf, sortVarsOfList, List.mem_append, List.mem_cons,
      List.mem_singleton]; simp [*]))

/-- The two tables give each of the keys and its renamed key one index. -/
def SameIndex (t t' : VarTable) (ks : List VarKey) : Prop :=
  ∀ k ∈ ks, t'.index (renKey f g k) = t.index k

variable {f g}

theorem SameIndex.sub {t t' : VarTable} {ks ks' : List VarKey} (h : SameIndex f g t t' ks)
    (hs : ∀ k ∈ ks', k ∈ ks) : SameIndex f g t t' ks' := fun k hk => h k (hs k hk)

theorem SameIndex.ev {t t' : VarTable} {ks : List VarKey} (h : SameIndex f g t t' ks)
    {k : VarKey} (hk : k ∈ ks) : t'.ev (renKey f g k) = t.ev k := by
  simp only [VarTable.ev, h k hk]

theorem SameIndex.sv {t t' : VarTable} {ks : List VarKey} (h : SameIndex f g t t' ks)
    {k : VarKey} (hk : k ∈ ks) : t'.sv (renKey f g k) = t.sv k := by
  simp only [VarTable.sv, h k hk]

mutual
  theorem trSort_sameIndex {t t' : VarTable} : ∀ (s : Kore.KSort),
      SameIndex f g t t' (sortVarsOf s) → trSort t' s = trSort t s
    | .var α, h => by
      have := h.ev (k := sortVarKey α) (by occ_vmem)
      rw [renKey_sortVarKey] at this
      rw [trSort, trSort, this]
    | .ctor _ args, h => by
      rw [trSort, trSort]; exact trSortApp_sameIndex args _ (by rw [sortVarsOf] at h; exact h)
  theorem trSortApp_sameIndex {t t' : VarTable} : ∀ (ss : List Kore.KSort) (acc : P),
      SameIndex f g t t' (sortVarsOfList ss) → trSortApp t' acc ss = trSortApp t acc ss
    | [], _, _ => rfl
    | s :: ss, acc, h => by
      rw [trSortApp, trSortApp, trSort_sameIndex s (h.sub fun k hk => by occ_vmem),
        trSortApp_sameIndex ss _ (h.sub fun k hk => by occ_vmem)]
end

end

section
variable {f g : String → Kore.KSort → String} {c c' : Ctx}

set_option maxHeartbeats 4000000 in
mutual
  /-- **One translation under two tables**: where the tables give each variable of p and its
  renamed key one index, and the aliases are the same, the renamed pattern under the one table is
  the pattern under the other. -/
  theorem tr_renVars (hal : c'.aliases = c.aliases) : ∀ (p : Kore.Pattern), SameIndex f g c.vars c'.vars (varsOf p) →
      tr c' (renVars f g p) = tr c p
    | .var (.evar x), h => by
      simp only [renVars, tr]
      rw [evarKey_renEVar f g, h.ev (by occ_vmem)]
    | .var (.svar X), h => by
      simp only [renVars, tr]
      rw [svarKey_renSVar f g, h.sv (by occ_vmem)]
    | .app hd ss ps, h => by
      simp only [renVars, tr, hal]
      rw [trSortApp_sameIndex ss _ (h.sub fun k hk => by occ_vmem),
        trArgs_renVars hal ps _ (h.sub fun k hk => by occ_vmem)]
    | .string _, _ => by simp only [renVars, tr]
    | .top s, h => by
      simp only [renVars, tr]; rw [trSort_sameIndex s (h.sub fun k hk => by occ_vmem)]
    | .bottom s, h => by
      simp only [renVars, tr]; rw [trSort_sameIndex s (h.sub fun k hk => by occ_vmem)]
    | .dv s _, h => by
      simp only [renVars, tr]; rw [trSort_sameIndex s (h.sub fun k hk => by occ_vmem)]
    | .not s p, h => by
      simp only [renVars, tr]
      rw [trSort_sameIndex s (h.sub fun k hk => by occ_vmem),
        tr_renVars hal p (h.sub fun k hk => by occ_vmem)]
    | .next s p, h => by
      simp only [renVars, tr]
      rw [tr_renVars hal p (h.sub fun k hk => by occ_vmem)]
    | .and s ps, h => by
      simp only [renVars, tr]
      rw [trSort_sameIndex s (h.sub fun k hk => by occ_vmem),
        trAndList_renVars hal ps _ (h.sub fun k hk => by occ_vmem)]
    | .or s ps, h => by
      simp only [renVars, tr]
      rw [trSort_sameIndex s (h.sub fun k hk => by occ_vmem),
        trOrList_renVars hal ps _ (h.sub fun k hk => by occ_vmem)]
    | .implies s p q, h => by
      simp only [renVars, tr]
      rw [trSort_sameIndex s (h.sub fun k hk => by occ_vmem),
        tr_renVars hal p (h.sub fun k hk => by occ_vmem),
        tr_renVars hal q (h.sub fun k hk => by occ_vmem)]
    | .iff s p q, h => by
      simp only [renVars, tr]
      rw [trSort_sameIndex s (h.sub fun k hk => by occ_vmem),
        tr_renVars hal p (h.sub fun k hk => by occ_vmem),
        tr_renVars hal q (h.sub fun k hk => by occ_vmem)]
    | .rewrites s p q, h => by
      simp only [renVars, tr]
      rw [trSort_sameIndex s (h.sub fun k hk => by occ_vmem),
        tr_renVars hal p (h.sub fun k hk => by occ_vmem),
        tr_renVars hal q (h.sub fun k hk => by occ_vmem)]
    | .exist s x p, h => by
      simp only [renVars, tr]
      rw [evarKey_renEVar f g, h.ev (by occ_vmem),
        show (renEVar f x).sort = x.sort from rfl,
        trSort_sameIndex x.sort (h.sub fun k hk => by occ_vmem),
        tr_renVars hal p (h.sub fun k hk => by occ_vmem)]
    | .forall s x p, h => by
      simp only [renVars, tr]
      rw [evarKey_renEVar f g, h.ev (by occ_vmem),
        show (renEVar f x).sort = x.sort from rfl,
        trSort_sameIndex s (h.sub fun k hk => by occ_vmem),
        trSort_sameIndex x.sort (h.sub fun k hk => by occ_vmem),
        tr_renVars hal p (h.sub fun k hk => by occ_vmem)]
    | .mu X p, h => by
      simp only [renVars, tr]
      rw [svarKey_renSVar f g, h.sv (by occ_vmem),
        tr_renVars hal p (h.sub fun k hk => by occ_vmem)]
    | .nu X p, h => by
      simp only [renVars, tr]
      rw [svarKey_renSVar f g, h.sv (by occ_vmem),
        show (renSVar g X).sort = X.sort from rfl,
        trSort_sameIndex X.sort (h.sub fun k hk => by occ_vmem),
        tr_renVars hal p (h.sub fun k hk => by occ_vmem)]
    | .ceil s s' p, h => by
      simp only [renVars, tr]
      rw [trSort_sameIndex s (h.sub fun k hk => by occ_vmem),
        trSort_sameIndex s' (h.sub fun k hk => by occ_vmem),
        tr_renVars hal p (h.sub fun k hk => by occ_vmem)]
    | .floor s s' p, h => by
      simp only [renVars, tr]
      rw [trSort_sameIndex s (h.sub fun k hk => by occ_vmem),
        trSort_sameIndex s' (h.sub fun k hk => by occ_vmem),
        tr_renVars hal p (h.sub fun k hk => by occ_vmem)]
    | .equals s s' p q, h => by
      simp only [renVars, tr]
      rw [trSort_sameIndex s (h.sub fun k hk => by occ_vmem),
        trSort_sameIndex s' (h.sub fun k hk => by occ_vmem),
        tr_renVars hal p (h.sub fun k hk => by occ_vmem),
        tr_renVars hal q (h.sub fun k hk => by occ_vmem)]
    | .in s s' p q, h => by
      simp only [renVars, tr]
      rw [trSort_sameIndex s (h.sub fun k hk => by occ_vmem),
        trSort_sameIndex s' (h.sub fun k hk => by occ_vmem),
        tr_renVars hal p (h.sub fun k hk => by occ_vmem),
        tr_renVars hal q (h.sub fun k hk => by occ_vmem)]
    | .leftAssoc hd ss ps, h => by
      simp only [renVars, tr]
      rw [trSortApp_sameIndex ss _ (h.sub fun k hk => by occ_vmem),
        trLeftAssoc_renVars hal ps _ (h.sub fun k hk => by occ_vmem)]
    | .rightAssoc hd ss ps, h => by
      simp only [renVars, tr]
      rw [trSortApp_sameIndex ss _ (h.sub fun k hk => by occ_vmem),
        trRightAssoc_renVars hal ps _ (h.sub fun k hk => by occ_vmem)]
  theorem trArgs_renVars (hal : c'.aliases = c.aliases) : ∀ (ps : List Kore.Pattern) (acc : P),
      SameIndex f g c.vars c'.vars (varsOfList ps) →
      trArgs c' acc (renVarsList f g ps) = trArgs c acc ps
    | [], _, _ => by simp only [renVarsList, trArgs]
    | p :: ps, acc, h => by
      simp only [renVarsList, trArgs]
      rw [tr_renVars hal p (h.sub fun k hk => by occ_vmem),
        trArgs_renVars hal ps _ (h.sub fun k hk => by occ_vmem)]
  theorem trAndList_renVars (hal : c'.aliases = c.aliases) : ∀ (ps : List Kore.Pattern) (s : P),
      SameIndex f g c.vars c'.vars (varsOfList ps) →
      trAndList c' s (renVarsList f g ps) = trAndList c s ps
    | [], _, _ => by simp only [renVarsList, trAndList]
    | [p], s, h => by
      simp only [renVarsList, trAndList]
      rw [tr_renVars hal p (h.sub fun k hk => by occ_vmem)]
    | p :: q :: ps, s, h => by
      have ih := trAndList_renVars hal (q :: ps) s (h.sub fun k hk => by rw [varsOfList]; exact List.mem_append_right _ hk)
      simp only [renVarsList, trAndList] at ih ⊢
      rw [tr_renVars hal p (h.sub fun k hk => by occ_vmem), ih]
  theorem trOrList_renVars (hal : c'.aliases = c.aliases) : ∀ (ps : List Kore.Pattern) (s : P),
      SameIndex f g c.vars c'.vars (varsOfList ps) →
      trOrList c' s (renVarsList f g ps) = trOrList c s ps
    | [], _, _ => by simp only [renVarsList, trOrList]
    | [p], s, h => by
      simp only [renVarsList, trOrList]
      rw [tr_renVars hal p (h.sub fun k hk => by occ_vmem)]
    | p :: q :: ps, s, h => by
      have ih := trOrList_renVars hal (q :: ps) s (h.sub fun k hk => by rw [varsOfList]; exact List.mem_append_right _ hk)
      simp only [renVarsList, trOrList] at ih ⊢
      rw [tr_renVars hal p (h.sub fun k hk => by occ_vmem), ih]
  theorem trLeftAssoc_renVars (hal : c'.aliases = c.aliases) : ∀ (ps : List Kore.Pattern) (head : P),
      SameIndex f g c.vars c'.vars (varsOfList ps) →
      trLeftAssoc c' head (renVarsList f g ps) = trLeftAssoc c head ps
    | [], _, _ => by simp only [renVarsList, trLeftAssoc]
    | p :: ps, head, h => by
      simp only [renVarsList, trLeftAssoc]
      rw [tr_renVars hal p (h.sub fun k hk => by occ_vmem),
        trLeftAssocRest_renVars hal ps _ _ (h.sub fun k hk => by occ_vmem)]
  theorem trLeftAssocRest_renVars (hal : c'.aliases = c.aliases) : ∀ (ps : List Kore.Pattern) (head acc : P),
      SameIndex f g c.vars c'.vars (varsOfList ps) →
      trLeftAssocRest c' head acc (renVarsList f g ps) = trLeftAssocRest c head acc ps
    | [], _, _, _ => by simp only [renVarsList, trLeftAssocRest]
    | p :: ps, head, acc, h => by
      simp only [renVarsList, trLeftAssocRest]
      rw [tr_renVars hal p (h.sub fun k hk => by occ_vmem),
        trLeftAssocRest_renVars hal ps _ _ (h.sub fun k hk => by occ_vmem)]
  theorem trRightAssoc_renVars (hal : c'.aliases = c.aliases) : ∀ (ps : List Kore.Pattern) (head : P),
      SameIndex f g c.vars c'.vars (varsOfList ps) →
      trRightAssoc c' head (renVarsList f g ps) = trRightAssoc c head ps
    | [], _, _ => by simp only [renVarsList, trRightAssoc]
    | [p], head, h => by
      simp only [renVarsList, trRightAssoc]
      rw [tr_renVars hal p (h.sub fun k hk => by occ_vmem)]
    | p :: q :: ps, head, h => by
      have ih := trRightAssoc_renVars hal (q :: ps) head
        (h.sub fun k hk => by rw [varsOfList]; exact List.mem_append_right _ hk)
      simp only [renVarsList, trRightAssoc] at ih ⊢
      rw [tr_renVars hal p (h.sub fun k hk => by occ_vmem), ih]
end

end

/-! ## The table of the renamed pattern -/

/-- Erasing duplicates commutes with a map that is one-to-one on the list. -/
theorem eraseDups_map_injOn {α : Type} [BEq α] [LawfulBEq α] (ρ : α → α) :
    ∀ (n : Nat) (l : List α), l.length ≤ n → (∀ a ∈ l, ∀ b ∈ l, ρ a = ρ b → a = b) →
      (l.map ρ).eraseDups = l.eraseDups.map ρ
  | _, [], _, _ => by simp
  | 0, _ :: _, hn, _ => by simp at hn
  | n + 1, a :: as, hn, hinj => by
    rw [List.map_cons, List.eraseDups_cons, List.eraseDups_cons, List.map_cons]
    have hf : (as.map ρ).filter (fun b => !(b == ρ a)) = (as.filter (fun b => !(b == a))).map ρ := by
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro b hb
      show (!(ρ b == ρ a)) = (!(b == a))
      by_cases hba : b = a
      · simp [hba]
      · have hne : ¬ ρ b = ρ a := fun e =>
          hba (hinj b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self ..) e)
        rw [beq_false_of_ne hne, beq_false_of_ne hba]
    rw [hf, eraseDups_map_injOn ρ n (as.filter fun b => !(b == a))
      (Nat.le_trans (List.length_filter_le _ _) (by simpa using hn))
      (fun x hx y hy => hinj x (List.mem_cons_of_mem _ (List.mem_filter.mp hx).1) y
        (List.mem_cons_of_mem _ (List.mem_filter.mp hy).1))]

/-- A map that is one-to-one on a list with the key keeps the key's place in the list. -/
theorem idxOf_map_injOn {α : Type} [BEq α] [LawfulBEq α] (ρ : α → α) (k : α) :
    ∀ (l : List α), (∀ a ∈ l, ρ a = ρ k → a = k) → (l.map ρ).idxOf (ρ k) = l.idxOf k
  | [], _ => rfl
  | a :: as, h => by
    rw [List.map_cons, List.idxOf_cons, List.idxOf_cons,
      idxOf_map_injOn ρ k as (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    by_cases hak : a = k
    · simp [hak]
    · have hne : ¬ ρ a = ρ k := fun e => hak (h a (List.mem_cons_self ..) e)
      simp [hak, hne]

section
variable (f g : String → Kore.KSort → String)

/-- The renaming is one-to-one on the keys: no two of them are spelled alike after it. -/
def RenInjOn (ks : List VarKey) : Prop :=
  ∀ a ∈ ks, ∀ b ∈ ks, renKey f g a = renKey f g b → a = b

instance (ks : List VarKey) : Decidable (RenInjOn f g ks) := by
  unfold RenInjOn; infer_instance

/-- **The table of the renamed pattern is the table of the pattern, renamed**, where the renaming
is one-to-one on the declared sort variables and the pattern's variables. -/
theorem tableOf_renVars (sortVars : List Kore.SortVar) (φ : Kore.Pattern)
    (hinj : RenInjOn f g (sortVars.map sortVarKey ++ varsOf φ)) :
    tableOf sortVars (renVars f g φ) = (tableOf sortVars φ).map (renKey f g) := by
  have hsv : (sortVars.map sortVarKey).map (renKey f g) = sortVars.map sortVarKey := by
    rw [List.map_map]; rfl
  unfold tableOf
  rw [← eraseDups_map_injOn (renKey f g) _ _ (Nat.le_refl _) hinj, List.map_append, hsv,
    varsOf_renVars]

/-- **Two patterns that differ only in the spelling of their variables, bound or free, with one
order of occurrence, translate to one pattern**: for a renaming of the element and set variables of
an axiom's pattern that is one-to-one on its variables, the renamed pattern under its own table
(`tableOf`) is the pattern under its own. -/
theorem tr_occurrence_order (sortVars : List Kore.SortVar) (aliases : List String)
    (φ : Kore.Pattern) (hinj : RenInjOn f g (sortVars.map sortVarKey ++ varsOf φ)) :
    tr ⟨tableOf sortVars (renVars f g φ), aliases⟩ (renVars f g φ) =
      tr ⟨tableOf sortVars φ, aliases⟩ φ := by
  refine tr_renVars (c := ⟨tableOf sortVars φ, aliases⟩)
    (c' := ⟨tableOf sortVars (renVars f g φ), aliases⟩) rfl φ ?_
  intro k hk
  show (tableOf sortVars (renVars f g φ)).index (renKey f g k) = (tableOf sortVars φ).index k
  rw [tableOf_renVars f g sortVars φ hinj]
  unfold VarTable.index
  rw [idxOf_map_injOn (renKey f g) k]
  intro a ha hak
  have ha' : a ∈ sortVars.map sortVarKey ++ varsOf φ := by
    unfold tableOf at ha; exact List.mem_eraseDups.mp ha
  exact hinj a ha' k (List.mem_append_right _ hk) hak

end

end KoreAML
