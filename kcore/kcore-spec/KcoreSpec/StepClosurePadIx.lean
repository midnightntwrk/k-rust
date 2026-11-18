/-
  The step's closure axiom in compiled code.

  `closureDisjunct` numbers a rule's variables after `offset` padding keys, so each read of an
  index in its table walks the padding first, and `stepClosureItem` places every rule after all the
  rules before it. Here the same disjunct is computed with the index read as `offset` plus the
  index in the rule's own table:
  - `trPadIx`, `trSortPadIx`: `tr` and `trSort` with the table's index function passed as a
    function; `trPadIx_index`, `trSortPadIx_index`: at a table's `index` they are `tr` and `trSort`.
  - `padIx offset t`: the index of a key in `offset` padding keys followed by `t`
    (`padIx_eq_index`).
  - `closureDisjunctPadIx`, `stepClosureItemPadIx`: `closureDisjunct` and `stepClosureItem` read
    through `padIx`, equal to them (`closureDisjunct_eq_padIx`, `stepClosureItem_eq_padIx`, both
    `@[csimp]`), so the compiled code of every module importing this one computes the closure
    through `padIx`. The definitions and what is proved about them are unchanged.
-/
import KcoreSpec.Faithful

set_option autoImplicit false

namespace KoreAML

open ML

mutual
  /-- `trSort` with the table read through `ix`. -/
  def trSortPadIx (ix : VarKey → Nat) : Kore.KSort → P
    | .var α => .evar ⟨ix (sortVarKey α)⟩
    | .ctor C args => trSortAppPadIx ix (sym (.sort C.ident.name)) args
    termination_by structural s => s
  def trSortAppPadIx (ix : VarKey → Nat) (acc : P) : List Kore.KSort → P
    | [] => acc
    | s :: ss => trSortAppPadIx ix (acc ⬝ trSortPadIx ix s) ss
    termination_by structural ss => ss
end

mutual
  /-- `tr` with the table read through `ix`. -/
  def trPadIx (ix : VarKey → Nat) (aliases : List String) : Kore.Pattern → P
    | .var (.evar x) => .evar ⟨ix (evarKey x)⟩
    | .var (.svar X) => .svar ⟨ix (svarKey X)⟩
    | .app h ss ps =>
      if aliases.contains h.ident.name then sym (.untranslated s!"alias {h.ident.name}")
      else trArgsPadIx ix aliases (trSortAppPadIx ix (sym (.symbol h.ident.name)) ss) ps
    | .string s => sym (.str s)
    | .top s => sTop (trSortPadIx ix s)
    | .bottom s => sBot (trSortPadIx ix s)
    | .not s p => sNot (trSortPadIx ix s) (trPadIx ix aliases p)
    | .and s ps => trAndListPadIx ix aliases (trSortPadIx ix s) ps
    | .or s ps => trOrListPadIx ix aliases (trSortPadIx ix s) ps
    | .implies s p q => sImp (trSortPadIx ix s) (trPadIx ix aliases p) (trPadIx ix aliases q)
    | .iff s p q => sIff (trSortPadIx ix s) (trPadIx ix aliases p) (trPadIx ix aliases q)
    | .exist _ x p => sExists ⟨ix (evarKey x)⟩ (trSortPadIx ix x.sort) (trPadIx ix aliases p)
    | .forall s x p =>
      sForall (trSortPadIx ix s) ⟨ix (evarKey x)⟩ (trSortPadIx ix x.sort) (trPadIx ix aliases p)
    | .mu X p => .mu ⟨ix (svarKey X)⟩ (trPadIx ix aliases p)
    | .nu X p => sNu (trSortPadIx ix X.sort) ⟨ix (svarKey X)⟩ (trPadIx ix aliases p)
    | .ceil s s' p => sCeil (trSortPadIx ix s) (trSortPadIx ix s') (trPadIx ix aliases p)
    | .floor s s' p => sFloor (trSortPadIx ix s) (trSortPadIx ix s') (trPadIx ix aliases p)
    | .equals s s' p q =>
      sEquals (trSortPadIx ix s) (trSortPadIx ix s') (trPadIx ix aliases p) (trPadIx ix aliases q)
    | .in s s' p q =>
      sIn (trSortPadIx ix s) (trSortPadIx ix s') (trPadIx ix aliases p) (trPadIx ix aliases q)
    | .next _ p => sNext (trPadIx ix aliases p)
    | .rewrites s p q => sRewrites (trSortPadIx ix s) (trPadIx ix aliases p) (trPadIx ix aliases q)
    | .dv s lit => sym (.dv lit) ⬝ trSortPadIx ix s
    | .leftAssoc h ss ps =>
      trLeftAssocPadIx ix aliases (trSortAppPadIx ix (sym (.symbol h.ident.name)) ss) ps
    | .rightAssoc h ss ps =>
      trRightAssocPadIx ix aliases (trSortAppPadIx ix (sym (.symbol h.ident.name)) ss) ps
    termination_by structural p => p
  def trArgsPadIx (ix : VarKey → Nat) (aliases : List String) (acc : P) : List Kore.Pattern → P
    | [] => acc
    | p :: ps => trArgsPadIx ix aliases (acc ⬝ trPadIx ix aliases p) ps
    termination_by structural ps => ps
  def trAndListPadIx (ix : VarKey → Nat) (aliases : List String) (s : P) : List Kore.Pattern → P
    | [] => sTop s
    | p :: ps => match ps with
      | [] => trPadIx ix aliases p
      | _ :: _ => sAnd (trPadIx ix aliases p) (trAndListPadIx ix aliases s ps)
    termination_by structural ps => ps
  def trOrListPadIx (ix : VarKey → Nat) (aliases : List String) (s : P) : List Kore.Pattern → P
    | [] => sBot s
    | p :: ps => match ps with
      | [] => trPadIx ix aliases p
      | _ :: _ => sOr s (trPadIx ix aliases p) (trOrListPadIx ix aliases s ps)
    termination_by structural ps => ps
  def trLeftAssocPadIx (ix : VarKey → Nat) (aliases : List String) (head : P) :
      List Kore.Pattern → P
    | [] => head
    | p :: ps => trLeftAssocRestPadIx ix aliases head (trPadIx ix aliases p) ps
    termination_by structural ps => ps
  def trLeftAssocRestPadIx (ix : VarKey → Nat) (aliases : List String) (head acc : P) :
      List Kore.Pattern → P
    | [] => acc
    | p :: ps => trLeftAssocRestPadIx ix aliases head (head ⬝ acc ⬝ trPadIx ix aliases p) ps
    termination_by structural ps => ps
  def trRightAssocPadIx (ix : VarKey → Nat) (aliases : List String) (head : P) :
      List Kore.Pattern → P
    | [] => head
    | p :: ps => match ps with
      | [] => trPadIx ix aliases p
      | _ :: _ => head ⬝ trPadIx ix aliases p ⬝ trRightAssocPadIx ix aliases head ps
    termination_by structural ps => ps
end

mutual
  theorem trSortPadIx_index (t : VarTable) : ∀ s : Kore.KSort, trSortPadIx t.index s = trSort t s
    | .var α => by rw [trSortPadIx, trSort]; rfl
    | .ctor _ args => by rw [trSortPadIx, trSort, trSortAppPadIx_index t args]
  theorem trSortAppPadIx_index (t : VarTable) : ∀ (ss : List Kore.KSort) (acc : P),
      trSortAppPadIx t.index acc ss = trSortApp t acc ss
    | [], _ => by rw [trSortAppPadIx, trSortApp]
    | s :: ss, acc => by
      rw [trSortAppPadIx, trSortApp, trSortPadIx_index t s, trSortAppPadIx_index t ss]
end

mutual
  /-- `trPadIx` reading a table's index function is `tr` under that table. -/
  theorem trPadIx_index (c : Ctx) : ∀ p : Kore.Pattern, trPadIx c.vars.index c.aliases p = tr c p
    | .var (.evar _) | .var (.svar _) | .string _ => by simp only [trPadIx, tr, VarTable.ev, VarTable.sv]
    | .app _ ss ps => by
      simp only [trPadIx, tr, trSortAppPadIx_index, trArgsPadIx_index c ps]
    | .top _ | .bottom _ | .dv _ _ => by simp only [trPadIx, tr, trSortPadIx_index]
    | .not _ p | .next _ p => by simp only [trPadIx, tr, trSortPadIx_index, trPadIx_index c p]
    | .and _ ps => by simp only [trPadIx, tr, trSortPadIx_index, trAndListPadIx_index c ps]
    | .or _ ps => by simp only [trPadIx, tr, trSortPadIx_index, trOrListPadIx_index c ps]
    | .implies _ p q | .iff _ p q | .rewrites _ p q => by
      simp only [trPadIx, tr, trSortPadIx_index, trPadIx_index c p, trPadIx_index c q]
    | .exist _ _ p | .forall _ _ p | .mu _ p | .nu _ p => by
      simp only [trPadIx, tr, VarTable.ev, VarTable.sv, trSortPadIx_index, trPadIx_index c p]
    | .ceil _ _ p | .floor _ _ p => by
      simp only [trPadIx, tr, trSortPadIx_index, trPadIx_index c p]
    | .equals _ _ p q | .in _ _ p q => by
      simp only [trPadIx, tr, trSortPadIx_index, trPadIx_index c p, trPadIx_index c q]
    | .leftAssoc _ ss ps => by
      simp only [trPadIx, tr, trSortAppPadIx_index, trLeftAssocPadIx_index c ps]
    | .rightAssoc _ ss ps => by
      simp only [trPadIx, tr, trSortAppPadIx_index, trRightAssocPadIx_index c ps]
  theorem trArgsPadIx_index (c : Ctx) : ∀ (ps : List Kore.Pattern) (acc : P),
      trArgsPadIx c.vars.index c.aliases acc ps = trArgs c acc ps
    | [], _ => by simp only [trArgsPadIx, trArgs]
    | p :: ps, acc => by
      simp only [trArgsPadIx, trArgs, trPadIx_index c p, trArgsPadIx_index c ps]
  theorem trAndListPadIx_index (c : Ctx) : ∀ (ps : List Kore.Pattern) (s : P),
      trAndListPadIx c.vars.index c.aliases s ps = trAndList c s ps
    | [], _ => by simp only [trAndListPadIx, trAndList]
    | [p], _ => by simp only [trAndListPadIx, trAndList, trPadIx_index c p]
    | p :: q :: ps, s => by
      have ih := trAndListPadIx_index c (q :: ps) s
      simp only [trAndListPadIx, trAndList] at ih ⊢
      rw [trPadIx_index c p, ih]
  theorem trOrListPadIx_index (c : Ctx) : ∀ (ps : List Kore.Pattern) (s : P),
      trOrListPadIx c.vars.index c.aliases s ps = trOrList c s ps
    | [], _ => by simp only [trOrListPadIx, trOrList]
    | [p], _ => by simp only [trOrListPadIx, trOrList, trPadIx_index c p]
    | p :: q :: ps, s => by
      have ih := trOrListPadIx_index c (q :: ps) s
      simp only [trOrListPadIx, trOrList] at ih ⊢
      rw [trPadIx_index c p, ih]
  theorem trLeftAssocPadIx_index (c : Ctx) : ∀ (ps : List Kore.Pattern) (head : P),
      trLeftAssocPadIx c.vars.index c.aliases head ps = trLeftAssoc c head ps
    | [], _ => by simp only [trLeftAssocPadIx, trLeftAssoc]
    | p :: ps, head => by
      simp only [trLeftAssocPadIx, trLeftAssoc, trPadIx_index c p, trLeftAssocRestPadIx_index c ps]
  theorem trLeftAssocRestPadIx_index (c : Ctx) : ∀ (ps : List Kore.Pattern) (head acc : P),
      trLeftAssocRestPadIx c.vars.index c.aliases head acc ps = trLeftAssocRest c head acc ps
    | [], _, _ => by simp only [trLeftAssocRestPadIx, trLeftAssocRest]
    | p :: ps, head, acc => by
      simp only [trLeftAssocRestPadIx, trLeftAssocRest, trPadIx_index c p,
        trLeftAssocRestPadIx_index c ps]
  theorem trRightAssocPadIx_index (c : Ctx) : ∀ (ps : List Kore.Pattern) (head : P),
      trRightAssocPadIx c.vars.index c.aliases head ps = trRightAssoc c head ps
    | [], _ => by simp only [trRightAssocPadIx, trRightAssoc]
    | [p], _ => by simp only [trRightAssocPadIx, trRightAssoc, trPadIx_index c p]
    | p :: q :: ps, head => by
      have ih := trRightAssocPadIx_index c (q :: ps) head
      simp only [trRightAssocPadIx, trRightAssoc] at ih ⊢
      rw [trPadIx_index c p, ih]
end

/-- The index of a key in `offset` padding keys followed by `t`, read without the padding. -/
def padIx (offset : Nat) (t : VarTable) (k : VarKey) : Nat :=
  if offset ≠ 0 ∧ k = .sortVar "#pad" then 1 else offset + t.index k

theorem padIx_eq_index (offset : Nat) (t : VarTable) :
    padIx offset t = VarTable.index (List.replicate offset (VarKey.sortVar "#pad") ++ t) := by
  funext k
  unfold padIx VarTable.index
  induction offset with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, List.idxOf_cons]
    by_cases hk : k = .sortVar "#pad"
    · subst hk; simp
    · rw [beq_false_of_ne (Ne.symm hk)]
      simp only [hk, and_false, Bool.false_eq_true, ite_false] at ih ⊢
      omega

/-- `closureDisjunct` with the index read by `padIx`. -/
def closureDisjunctPadIx (aliases : List String) (offset : Nat) (y : EVar) (pat : Kore.Pattern) :
    List String × P :=
  let t0 := tableOf [] pat
  let ix := padIx offset t0
  let (L, R) := match pat with
    | .rewrites _ l r => (trPadIx ix aliases l, trPadIx ix aliases r)
    | _ => (⊥, ⊥)
  let free := (freeOf [] pat).eraseDups.filterMap fun
    | k@(.evar _ s) => some (k, s)
    | _ => none
  (t0.map VarKey.name,
   free.foldr (fun (k, s) φ => sExists ⟨ix k⟩ (trSortPadIx ix s) φ) (L ⋀ (y ∈∈ R)))

@[csimp] theorem closureDisjunct_eq_padIx : @closureDisjunct = @closureDisjunctPadIx := by
  funext aliases offset y pat
  have hc := trPadIx_index ⟨List.replicate offset (.sortVar "#pad") ++ tableOf [] pat, aliases⟩
  simp only at hc
  unfold closureDisjunct closureDisjunctPadIx
  dsimp only
  rw [padIx_eq_index]
  cases pat <;> simp only [hc, trSortPadIx_index, VarTable.ev] <;> rfl

end KoreAML

namespace KCore

namespace Faithful

open ML

/-- `stepClosureItem` with each disjunct computed by `closureDisjunctPadIx`. -/
def stepClosureItemPadIx (c : Semantics) : KoreAML.Item :=
  let pats := c.rules.map (prioRuleK c)
  let total := pats.foldl (fun n p => n + (KoreAML.tableOf [] p).length) 0
  let y : EVar := ⟨total + 1⟩
  let (names, disjuncts, _) := pats.foldl (fun (acc : List String × List KoreAML.P × Nat) p =>
      let (ns, φ) := KoreAML.closureDisjunctPadIx [] acc.2.2 y p
      (acc.1 ++ ns, acc.2.1 ++ [φ], acc.2.2 + ns.length)) ([], [], 0)
  { label := s!"closure ({pats.length} rules)", rule := "Closure", names := names ++ ["y"]
    pat := ∀∀ y (KoreAML.sNext (.evar y) ⊆⊆ KoreAML.disjList disjuncts) }

@[csimp] theorem stepClosureItem_eq_padIx : @stepClosureItem = @stepClosureItemPadIx := by
  funext c
  unfold stepClosureItem stepClosureItemPadIx
  rw [← KoreAML.closureDisjunct_eq_padIx]

end Faithful

end KCore
