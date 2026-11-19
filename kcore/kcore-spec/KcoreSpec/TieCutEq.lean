/-
  KCore, outside the cone: a function equation whose premise Γ's item writes through a cut of its
  `requires` (the readings `andUnderAppCut`, `Parse.condAndCutT`, and `notAsCondition`,
  `Parse.notCondTerm?`), against the premise as the text writes it. For a tie file.

  - `textPrem`: of Γ's premise of a clause read through the cut, the premise the text writes.
    `Cut.andApp path`: Γ writes `(⌈K[x] = true⌉ ∧ args) ∧ x ∈ u`, x an element variable at `path` in
    the `requires` term, and the text `⌈K[x ∧ u] = true⌉ ∧ args`. `Cut.notCond`: Γ writes
    `(⊤ ∧ args) ∧ b = false` and the text `⌈¬b = true⌉ ∧ args`, `¬` the complement in Bool.
  - `Place`: the premise is the equation's own (`own`), or stands under the binders of one
    competitor in the negation an equation of a larger priority carries (`under i n`); `textPremAt`.
  - `textItem k pl a`: the item of Γ's equation `a` with the premise so written, at `a`'s variable
    table. A tie file compares it with the sentence's translation up to the names of the variables
    (`TieAlpha.acEqB`).
  - The inclusions of the two premises, at one valuation:
    `and_gamma_sub`: Γ's is inside the text's, in every interpretation: `x ∈ u` is an application
    whose argument `x ∧ u` has an element, so u holds x's element and `K[x ∧ u]` is `K[x]`.
    `and_text_sub`: the text's is inside Γ's where definedness and `⌈_⌉` are read, the sorts denote
    sorts, x is an element of its sort and `true` has an element in Bool: `K[x ∧ u]` then holds it,
    so `x ∧ u` has an element.
    `not_iff`: the two are one where, beside these, every element of Bool is in exactly one of
    `true` and `false`. That is sufficient, and Γ's premise is inside the text's only with it: where
    b is `false` and Bool has an element beside its literals, the complement of b holds that
    element and is not `true`. The text's premise is inside Γ's without the closure where b has at
    most one element of Bool; no lemma here states that case.
  - Under a competitor's negation the inclusions swap sides (`Frame.fill_sub`).
  - `cutEq_from_text_pure` (`andApp`, `own`) and `cutEq_entailed_pure` (`andApp`, `under`): one item
    from the other in every model of definedness. `cutEq_from_text`, `cutEq_entailed`, `cutEq_iff`:
    in a model with the constructors' facts (`NodeFacts`), for `notCond` with the closure of Bool
    (`boolClosed`) as a hypothesis.
-/
import KcoreSpec.TieRuleLhs
import KcoreSpec.ExistsHoist
import KcoreSpec.RuleAndIn
import KcoreSpec.HoldsNode
import KcoreSpec.FaithfulFamilies
import KcoreSpec.CondTwoTables

set_option autoImplicit false

namespace KCore

namespace TieCutEq

open ML Faithful KoreAML

/-- The item of the pattern `p` of sort `S` under the variable table `t`, with the guards of
`free`. -/
def itemAt (t : VarTable) (free : List VarKey) (S : Kore.KSort) (p : Kore.Pattern) : P :=
  conjList (free.map (guardOf t)) ⇒ (tr ⟨t, []⟩ p ≡ inhOf (trSort t S))

/-- The reading of a condition: a conjunction under applications cut at `path` (the argument
indices from the top of the `requires` term), or `\not{SortBool{}}` of a term. -/
inductive Cut where
  | andApp (path : List Nat)
  | notCond
  deriving DecidableEq, Repr

/-- The parts of Γ's premise `\and{R}(\and{R₁}(\equals{sB, R₂}(K[x], tt), args), \in{S, R₂}(x, u))`
of a clause whose `requires` holds the variable x at `path`, where the text holds `\and{S}(x, u)`:
`(R, R₁, sB, R₂, tt, args, S, x, u, K)`, no head of K an alias. -/
def andParts (path : List Nat) : Kore.Pattern →
    Option (Kore.KSort × Kore.KSort × Kore.KSort × Kore.KSort × Kore.Pattern × Kore.Pattern ×
      Kore.KSort × Kore.EVar × Kore.Pattern × KoreCutCtx)
  | .and R [.and R₁ [.equals sB R₂ q tt, args], .in S R₃ (.var (.evar x)) u] =>
    match TieRuleLhs.cutAt path q with
    | some (K, _) =>
      if R₃ = R₂ ∧ q = K.fill (.var (.evar x)) ∧ K.noAlias ⟨[], []⟩ = true then
        some (R, R₁, sB, R₂, tt, args, S, x, u, K)
      else none
    | none => none
  | _ => none

/-- The parts of Γ's premise `\and{R}(\and{R₁}(\top{R₂}(), args), \equals{sB, R₂}(b, ff))` of a
clause without a `requires` whose predicate is an equality: `(R, R₁, R₂, args, sB, b, ff)`. -/
def notParts : Kore.Pattern →
    Option (Kore.KSort × Kore.KSort × Kore.KSort × Kore.Pattern × Kore.KSort × Kore.Pattern × Kore.Pattern)
  | .and R [.and R₁ [.top R₂, args], .equals sB R₃ b ff] =>
    if R₃ = R₂ then some (R, R₁, R₂, args, sB, b, ff) else none
  | _ => none

/-- **The premise as the text writes it**, of Γ's premise of a clause read through the cut:
`\and{R}(\equals{sB, R₂}(K[\and{S}(x, u)], tt), args)` for `andApp`, and
`\and{R}(\equals{sB, R₂}(\not{sB}(b), \dv{sB}("true")), args)` for `notCond`. -/
def textPrem : Cut → Kore.Pattern → Option Kore.Pattern
  | .andApp path, p => (andParts path p).map fun x =>
      .and x.1 [.equals x.2.2.1 x.2.2.2.1 (x.2.2.2.2.2.2.2.2.2.fill
        (.and x.2.2.2.2.2.2.1 [.var (.evar x.2.2.2.2.2.2.2.1), x.2.2.2.2.2.2.2.2.1])) x.2.2.2.2.1, x.2.2.2.2.2.1]
  | .notCond, p => (notParts p).map fun x =>
      .and x.1 [.equals x.2.2.2.2.1 x.2.2.1 (.not x.2.2.2.2.1 x.2.2.2.2.2.1) (.dv x.2.2.2.2.1 "true"), x.2.2.2.1]

/-- `\exists` of each binder, the first outermost. -/
def exAll (zs : List (Kore.KSort × Kore.EVar)) (b : Kore.Pattern) : Kore.Pattern :=
  zs.foldr (fun z acc => .exist z.1 z.2 acc) b

/-- A right-nested chain of disjunctions `\or{R₀}(d₀, \or{R₁}(d₁, … inner))`. -/
def orWrap (pre : List (Kore.KSort × Kore.Pattern)) (inner : Kore.Pattern) : Kore.Pattern :=
  pre.foldr (fun d acc => .or d.1 [d.2, acc]) inner

/-- A pattern under `n` binders `\exists`: the binders and the body. -/
def exSplit : Nat → Kore.Pattern → Option (List (Kore.KSort × Kore.EVar) × Kore.Pattern)
  | 0, p => some ([], p)
  | n + 1, .exist R z p => (exSplit n p).map fun zb => ((R, z) :: zb.1, zb.2)
  | _ + 1, _ => none

/-- A right-nested chain of disjunctions at its `i`-th operand: the operands before it, and
`\or{R}(d, rest)`. -/
def orSplit : Nat → Kore.Pattern →
    Option (List (Kore.KSort × Kore.Pattern) × Kore.KSort × Kore.Pattern × Kore.Pattern)
  | 0, .or R [d, rest] => some ([], R, d, rest)
  | i + 1, .or R [d, rest] => (orSplit i rest).map fun x => ((R, d) :: x.1, x.2)
  | _, _ => none

theorem exSplit_eq : ∀ (n : Nat) (p : Kore.Pattern) {zs : List (Kore.KSort × Kore.EVar)} {b : Kore.Pattern},
    exSplit n p = some (zs, b) → p = exAll zs b
  | 0, p, zs, b, h => by
    simp only [exSplit, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | n + 1, p, zs, b, h => by
    cases p with
    | exist R z q =>
      simp only [exSplit, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨zs', b'⟩, hq, rfl, rfl⟩ := h
      rw [exSplit_eq n q hq]; rfl
    | _ => simp [exSplit] at h

theorem orSplit_eq : ∀ (i : Nat) (D : Kore.Pattern) {pre : List (Kore.KSort × Kore.Pattern)} {Ro : Kore.KSort}
    {d rest : Kore.Pattern}, orSplit i D = some (pre, Ro, d, rest) → D = orWrap pre (.or Ro [d, rest]) := by
  intro i
  induction i with
  | zero =>
    intro D pre Ro d rest h
    unfold orSplit at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl
    · rename_i heq; cases heq
    · cases h
  | succ j ih =>
    intro D pre Ro d rest h
    unfold orSplit at h
    split at h
    · rename_i heq; cases heq
    · rename_i heq
      cases heq
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨pre', x⟩, hq, rfl, rfl⟩ := h
      rw [ih _ hq]; rfl
    · cases h

/-- The premise `\and{R}(\not{R'}(⋁ competitors), own)` around one competitor's body: the
disjuncts before the competitor, its disjunction's sort and the rest of the chain, and the
competitor's binders. -/
structure Frame where
  R : Kore.KSort
  R' : Kore.KSort
  pre : List (Kore.KSort × Kore.Pattern)
  Ro : Kore.KSort
  rest : Kore.Pattern
  own : Kore.Pattern
  zs : List (Kore.KSort × Kore.EVar)

def Frame.fill (F : Frame) (body : Kore.Pattern) : Kore.Pattern :=
  .and F.R [.not F.R' (orWrap F.pre (.or F.Ro [exAll F.zs body, F.rest])), F.own]

/-- The frame of the `i`-th competitor under its `n` binders, and the competitor's body. -/
def frameOf (i n : Nat) : Kore.Pattern → Option (Frame × Kore.Pattern)
  | .and R [.not R' D, own] => (orSplit i D).bind fun x =>
      (exSplit n x.2.2.1).map fun zb => (⟨R, R', x.1, x.2.1, x.2.2.2, own, zb.1⟩, zb.2)
  | _ => none

theorem frameOf_eq {i n : Nat} {p : Kore.Pattern} {F : Frame} {body : Kore.Pattern}
    (h : frameOf i n p = some (F, body)) : p = F.fill body := by
  unfold frameOf at h
  split at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨pre, Ro, d, rest⟩, ho, ⟨zs, b⟩, he, rfl, rfl⟩ := h
    dsimp only at he ⊢
    rw [orSplit_eq _ _ ho, exSplit_eq _ _ he]; rfl
  · cases h

/-- Where the cut premise stands in an equation's premise: the premise itself (`own`), or, in the
premise `\and{R}(\not{R}(⋁ competitors), own)` of an equation under the negation of the clauses of
a smaller priority, the `i`-th competitor's under its `n` binders (`under i n`). -/
inductive Place where
  | own
  | under (i n : Nat)
  deriving DecidableEq, Repr

/-- The binders around the cut premise at the place, and the cut premise. -/
def cutBody : Place → Kore.Pattern → Option (List (Kore.KSort × Kore.EVar) × Kore.Pattern)
  | .own, p => some ([], p)
  | .under i n, p => (frameOf i n p).map fun Fb => (Fb.1.zs, Fb.2)

/-- The premise as the text writes it, the cut premise at `pl`. -/
def textPremAt (k : Cut) : Place → Kore.Pattern → Option Kore.Pattern
  | .own, p => textPrem k p
  | .under i n, p => (frameOf i n p).bind fun Fb => (textPrem k Fb.2).map Fb.1.fill

/-- Γ's equation `\implies{R}(prem, eq)` with the premise as the text writes it. -/
def textPat (k : Cut) (pl : Place) : Kore.Pattern → Option Kore.Pattern
  | .implies R prem eq => (textPremAt k pl prem).map fun prem' => .implies R prem' eq
  | _ => none

/-- The free variables of an axiom, its sort variables first: the guards of its item. -/
def freeG (a : Kore.Axiom) : List VarKey := (a.sortVars.map sortVarKey ++ freeOf [] a.pattern).eraseDups

/-- The free variables of the pattern `p'` with `a`'s sort variables first. -/
def freeT (a : Kore.Axiom) (p' : Kore.Pattern) : List VarKey :=
  (a.sortVars.map sortVarKey ++ freeOf [] p').eraseDups

/-- **The item of the text's form of Γ's equation `a`**, at `a`'s variable table, with the guards
of the form's own free variables in the order of their occurrence in it. -/
def textItem (k : Cut) (pl : Place) (a : Kore.Axiom) : Option P :=
  match a.pattern with
  | .implies R _ _ => (textPat k pl a.pattern).map fun p' =>
      itemAt (tableOf a.sortVars a.pattern) (freeT a p') R p'
  | _ => none

/-- The two forms have the same free variables. -/
def shapeOK (k : Cut) (pl : Place) (a : Kore.Axiom) : Bool :=
  match textPat k pl a.pattern with
  | some p' => (freeT a p').all (freeG a).contains && (freeG a).all (freeT a p').contains
  | none => false

/-- The sort `R₂` of the premise is a sort variable among the free variables, and no binder of
`zs` has its index. -/
def sortVarOK (t : VarTable) (fG : List VarKey) (zs : List (Kore.KSort × Kore.EVar)) : Kore.KSort → Bool
  | .var α => fG.contains (sortVarKey α) && zs.all fun z => decide (t.ev (evarKey z.2) ≠ t.ev (sortVarKey α))
  | _ => false

/-- What the converse inclusions read of the cut premise `body` under the binders `zs`, decided:
its sort is a sort variable of the axiom that no binder rebinds; Bool and its literals are the
definition's; for `andApp`, the conjunction's sort is a numbered sort and the variable's, and the
variable is free in the axiom or bound by a binder, no binder of another name having its index;
for `notCond`, the sort variable is not the variable of `\top`. -/
def bodyOK (c : Semantics) (t : VarTable) (fG : List VarKey) (zs : List (Kore.KSort × Kore.EVar)) :
    Cut → Kore.Pattern → Bool
  | .andApp path, body => match andParts path body with
    | some (_, _, sB, R₂, tt, _, S, x, _, _) =>
      sortVarOK t fG zs R₂ && decide (sB = srtOf c Srt.bool) && decide (tt = (KCore.bool true).kore c) &&
      (List.range (nRegSorts + c.sortNames.length)).any (fun s => decide (S = srtOf c s)) &&
      decide (x.sort = S) &&
      zs.all (fun z => decide (evarKey z.2 = evarKey x) || decide (t.ev (evarKey z.2) ≠ t.ev (evarKey x))) &&
      (fG.contains (evarKey x) || zs.any (fun z => decide (evarKey z.2 = evarKey x)))
    | none => false
  | .notCond, body => match notParts body with
    | some (_, _, R₂, _, sB, _, ff) =>
      sortVarOK t fG zs R₂ && decide (sB = srtOf c Srt.bool) && decide (ff = (KCore.bool false).kore c) &&
      decide (Kore.Pattern.dv sB "true" = (KCore.bool true).kore c) &&
      !(trSort t R₂).isFreeEvar topVar
    | none => false

/-- `bodyOK` of the cut premise of the equation `a` at the place. -/
def factsOK (c : Semantics) (k : Cut) (pl : Place) (a : Kore.Axiom) : Bool :=
  match a.pattern with
  | .implies _ prem _ => match cutBody pl prem with
    | some (zs, body) => bodyOK c (tableOf a.sortVars a.pattern) (freeG a) zs k body
    | none => false
  | _ => false

theorem andParts_eq {path : List Nat} {p : Kore.Pattern} {R R₁ sB R₂ : Kore.KSort} {tt args : Kore.Pattern}
    {S : Kore.KSort} {x : Kore.EVar} {u : Kore.Pattern} {K : KoreCutCtx}
    (h : andParts path p = some (R, R₁, sB, R₂, tt, args, S, x, u, K)) :
    p = .and R [.and R₁ [.equals sB R₂ (K.fill (.var (.evar x))) tt, args], .in S R₂ (.var (.evar x)) u] ∧
      K.noAlias ⟨[], []⟩ = true := by
  unfold andParts at h
  split at h
  · split at h
    · split at h
      · next hc =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
        obtain ⟨rfl, hq, hK⟩ := hc
        exact ⟨by rw [← hq], hK⟩
      · cases h
    · cases h
  · cases h

theorem notParts_eq {p : Kore.Pattern} {R R₁ R₂ : Kore.KSort} {args : Kore.Pattern} {sB : Kore.KSort}
    {b ff : Kore.Pattern} (h : notParts p = some (R, R₁, R₂, args, sB, b, ff)) :
    p = .and R [.and R₁ [.top R₂, args], .equals sB R₂ b ff] := by
  unfold notParts at h
  split at h
  · split at h
    · next hc =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      rw [hc]
    · cases h
  · cases h

theorem noAlias_vars (t t' : VarTable) (al : List String) :
    ∀ K : KoreCutCtx, K.noAlias ⟨t, al⟩ = K.noAlias ⟨t', al⟩
  | .hole => rfl
  | .app h ss pre C post => by simp only [KoreCutCtx.noAlias, noAlias_vars t t' al C]

theorem tr_evar (t : VarTable) (x : Kore.EVar) : tr ⟨t, []⟩ (.var (.evar x)) = .evar (t.ev (evarKey x)) := by
  rw [tr]

theorem tr_equals (t : VarTable) (s s' : Kore.KSort) (p q : Kore.Pattern) :
    tr ⟨t, []⟩ (.equals s s' p q) = sEquals (trSort t s) (trSort t s') (tr ⟨t, []⟩ p) (tr ⟨t, []⟩ q) := by
  rw [tr]

theorem tr_in (t : VarTable) (s s' : Kore.KSort) (p q : Kore.Pattern) :
    tr ⟨t, []⟩ (.in s s' p q) = sIn (trSort t s) (trSort t s') (tr ⟨t, []⟩ p) (tr ⟨t, []⟩ q) := by
  rw [tr]

theorem tr_not (t : VarTable) (s : Kore.KSort) (p : Kore.Pattern) :
    tr ⟨t, []⟩ (.not s p) = sNot (trSort t s) (tr ⟨t, []⟩ p) := by
  rw [tr]

theorem tr_top (t : VarTable) (s : Kore.KSort) : tr ⟨t, []⟩ (.top s) = sTop (trSort t s) := by
  rw [tr]

theorem tr_implies (t : VarTable) (s : Kore.KSort) (p q : Kore.Pattern) :
    tr ⟨t, []⟩ (.implies s p q) = sImp (trSort t s) (tr ⟨t, []⟩ p) (tr ⟨t, []⟩ q) := by
  rw [tr]

theorem tr_exist (t : VarTable) (s : Kore.KSort) (z : Kore.EVar) (p : Kore.Pattern) :
    tr ⟨t, []⟩ (.exist s z p) = sExists (t.ev (evarKey z)) (trSort t z.sort) (tr ⟨t, []⟩ p) := by
  rw [tr]

theorem tr_or2 (t : VarTable) (s : Kore.KSort) (p q : Kore.Pattern) :
    tr ⟨t, []⟩ (.or s [p, q]) = sOr (trSort t s) (tr ⟨t, []⟩ p) (tr ⟨t, []⟩ q) := by
  rw [tr]; simp only [trOrList]

/-- `trAxiom` of an equation axiom is `itemAt` at its table and its free variables. -/
theorem trAxiom_implies (a : Kore.Axiom) {R : Kore.KSort} {prem eq : Kore.Pattern}
    (h : a.pattern = .implies R prem eq) :
    (trAxiom [] [] ⟨0, "kernel", a⟩).pat = itemAt (tableOf a.sortVars a.pattern) (freeG a) R a.pattern := by
  unfold trAxiom itemAt freeG
  simp only [h, sortOf]

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- Every element of `p` is one of `q`, under the table `t` at the valuation `e`. -/
def Sub (I : Interpretation KoreAML.Sym M) (t : VarTable) (e : Valuation M) (p q : Kore.Pattern) : Prop :=
  ∀ a, (tr ⟨t, []⟩ p).interpret I e a → (tr ⟨t, []⟩ q).interpret I e a

/-- **An equation axiom entails the one with a smaller premise.** The item of
`\implies{R}(prem, eq)` with the guards of `f` holds in `I`; at the valuation `e`, where the guards
of `f' ⊇ f` hold, every element of `prem'` is one of `prem`. Then the item of
`\implies{R}(prem', eq)` with the guards of `f'` holds at `e`. -/
theorem item_of_sub (hD : DefOK I) {t : VarTable} {f f' : List VarKey} {R : Kore.KSort}
    {prem prem' eq : Kore.Pattern} (hsub : ∀ k ∈ f, k ∈ f') (h : I ⊧ᴵ itemAt t f R (.implies R prem eq))
    (e : Valuation M) (m : M)
    (hP : (∀ k ∈ f', (guardOf t k).interpret I e m) → Sub I t e prem' prem) :
    (itemAt t f' R (.implies R prem' eq)).interpret I e m := by
  have h1 := h e m
  unfold itemAt at h1 ⊢
  rw [interpret_impl] at h1 ⊢
  intro hg
  rw [TieUnion.interp_conjListAll] at hg
  have hg' : ∀ k ∈ f', (guardOf t k).interpret I e m := fun k hk => hg _ (List.mem_map_of_mem hk)
  have h2 := h1 (TieUnion.interp_conjListAll.mpr fun φ hφ => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hφ
    exact hg' k (hsub k hk))
  rw [interp_equal hD] at h2 ⊢
  intro a
  have h3 := h2 a
  rw [tr_implies, interp_sImp] at h3 ⊢
  exact ⟨fun hf => hf.1, fun ht' => ⟨ht', fun hl => (h3.mpr ht').2 (hP hg' a hl)⟩⟩

/-- `sEquals` reads its left operand only through the set it denotes. -/
theorem sEquals_congrL {e : Valuation M} {S S' φ φ' ψ : P}
    (h : ∀ b, φ.interpret I e b ↔ φ'.interpret I e b) (m : M) :
    (sEquals S S' φ ψ).interpret I e m ↔ (sEquals S S' φ' ψ).interpret I e m := by
  unfold sEquals sFloor sIff sImp sOr sCeil
  simp only [interp_sNot, interp_sAnd, interp_app, h]

/-- `x ∈ ψ` holds somewhere only where ψ holds x's element, in every interpretation: it is an
application whose argument is `x ∧ ψ`. -/
theorem sIn_evar_elem {e : Valuation M} {S S' ψ : P} {x : EVar} {m : M}
    (h : (sIn S S' (.evar x) ψ).interpret I e m) : ψ.interpret I e (e.evalEvar x) := by
  unfold sIn sCeil at h
  obtain ⟨_, b, -, hb, -⟩ := interp_app.mp h
  obtain ⟨h1, h2⟩ := interp_sAnd.mp hb
  rw [interp_evar] at h1
  exact h1 ▸ h2

/-- **`andApp`: Γ's premise is inside the text's**, in every interpretation. -/
theorem and_gamma_sub {t : VarTable} {R R₁ sB R₂ S : Kore.KSort} {tt args u : Kore.Pattern} {x : Kore.EVar}
    {K : KoreCutCtx} (hK : K.noAlias ⟨t, []⟩ = true) (e : Valuation M) :
    Sub I t e (.and R [.and R₁ [.equals sB R₂ (K.fill (.var (.evar x))) tt, args], .in S R₂ (.var (.evar x)) u])
      (.and R [.equals sB R₂ (K.fill (.and S [.var (.evar x), u])) tt, args]) := by
  intro a ha
  rw [tr_and2, tr_and2, interp_sAnd, interp_sAnd, tr_equals, tr_in, tr_evar] at ha
  obtain ⟨⟨heq, hargs⟩, hin⟩ := ha
  have hu := sIn_evar_elem hin
  rw [tr_and2, interp_sAnd, tr_equals]
  refine ⟨(sEquals_congrL (fun b => ?_) a).mp heq, hargs⟩
  rw [tr_cutCtx _ _ K hK, tr_cutCtx _ _ K hK, tr_and2, tr_evar, CutCtx.fill_evar_and]
  exact ⟨fun h => ⟨hu, h⟩, fun h => h.2⟩

/-- **`andApp`: the text's premise is inside Γ's** where definedness and `⌈_⌉` are read, the three
sort patterns denote sorts, x has an element of its sort and `tt` an element in the sort of the
condition. -/
theorem and_text_sub [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {t : VarTable}
    {R R₁ sB R₂ S : Kore.KSort} {tt args u : Kore.Pattern} {x : Kore.EVar} {K : KoreCutCtx}
    (hK : K.noAlias ⟨t, []⟩ = true) {e : Valuation M} {σB ρ σ : M}
    (hSB : ∀ a, (trSort t sB).interpret I e a ↔ a = σB) (hR : ∀ a, (trSort t R₂).interpret I e a ↔ a = ρ)
    (hS : ∀ a, (trSort t S).interpret I e a ↔ a = σ) (hσB : IsSort I σB) (hρ : IsSort I ρ) (hσ : IsSort I σ)
    (hx : Inh I σ (e.evalEvar (t.ev (evarKey x))))
    (hT : ∃ a0, Inh I σB a0 ∧ (tr ⟨t, []⟩ tt).interpret I e a0) :
    Sub I t e (.and R [.equals sB R₂ (K.fill (.and S [.var (.evar x), u])) tt, args])
      (.and R [.and R₁ [.equals sB R₂ (K.fill (.var (.evar x))) tt, args], .in S R₂ (.var (.evar x)) u]) := by
  intro a ha
  rw [tr_and2, interp_sAnd, tr_equals] at ha
  obtain ⟨heq, hargs⟩ := ha
  have h1 := (interp_sEquals hD hc hSB hR hσB hρ a).mp heq
  obtain ⟨a0, ha0, hta0⟩ := hT
  have hf := (h1.2 a0 ha0).mpr hta0
  rw [tr_cutCtx _ _ K hK, tr_and2, tr_evar, CutCtx.fill_evar_and] at hf
  have hu := hf.1
  have hcongr : ∀ b, (tr ⟨t, []⟩ (K.fill (.and S [.var (.evar x), u]))).interpret I e b ↔
      (tr ⟨t, []⟩ (K.fill (.var (.evar x)))).interpret I e b := by
    intro b
    rw [tr_cutCtx _ _ K hK, tr_cutCtx _ _ K hK, tr_and2, tr_evar, CutCtx.fill_evar_and]
    exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩
  rw [tr_and2, tr_and2, interp_sAnd, interp_sAnd, tr_equals, tr_in, tr_evar]
  exact ⟨⟨(sEquals_congrL hcongr a).mp heq, hargs⟩,
    (mem_iff_cut hD hc hS hR hσ hρ _ hx _ a).mpr ⟨hu, h1.1⟩⟩

/-- **`notCond`: the two premises are one** where definedness and `⌈_⌉` are read, the two sort
patterns denote sorts, and every element of the condition's sort is in exactly one of `true` and
`ff`. -/
theorem not_iff [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {t : VarTable}
    {R R₁ R₂ sB : Kore.KSort} {args b ff : Kore.Pattern} {e : Valuation M} {σB ρ : M}
    (hSB : ∀ a, (trSort t sB).interpret I e a ↔ a = σB) (hR : ∀ a, (trSort t R₂).interpret I e a ↔ a = ρ)
    (hσB : IsSort I σB) (hρ : IsSort I ρ) (htop : (trSort t R₂).isFreeEvar topVar = false)
    (hB : ∀ m, Inh I σB m →
      ((tr ⟨t, []⟩ (.dv sB "true")).interpret I e m ↔ ¬ (tr ⟨t, []⟩ ff).interpret I e m)) (a : M) :
    (tr ⟨t, []⟩ (.and R [.and R₁ [.top R₂, args], .equals sB R₂ b ff])).interpret I e a ↔
      (tr ⟨t, []⟩ (.and R [.equals sB R₂ (.not sB b) (.dv sB "true"), args])).interpret I e a := by
  rw [tr_and2, tr_and2, tr_and2, interp_sAnd, interp_sAnd, interp_sAnd, tr_equals, tr_equals, tr_top, tr_not,
    interp_sTop hD htop, interp_inhOf_of hR, interp_sEquals hD hc hSB hR hσB hρ,
    interp_sEquals hD hc hSB hR hσB hρ]
  constructor
  · rintro ⟨⟨-, hargs⟩, hm, h⟩
    refine ⟨⟨hm, fun m hmB => ?_⟩, hargs⟩
    rw [interp_sNot, interp_inhOf_of hSB, hB m hmB, h m hmB]
    exact ⟨fun h' => h'.1, fun h' => ⟨h', hmB⟩⟩
  · rintro ⟨⟨hm, h⟩, hargs⟩
    refine ⟨⟨hm, hargs⟩, hm, fun m hmB => ?_⟩
    have h2 := h m hmB
    rw [interp_sNot, interp_inhOf_of hSB, hB m hmB] at h2
    constructor
    · intro hb
      apply Classical.byContradiction
      intro hff
      exact (h2.mpr hff).1 hb
    · intro hff
      apply Classical.byContradiction
      intro hb
      exact (h2.mp ⟨hb, hmB⟩) hff

/-! ### Under a competitor's negation -/

theorem or_left_sub {t : VarTable} {e : Valuation M} {R : Kore.KSort} {d d' rest : Kore.Pattern}
    (h : Sub I t e d d') : Sub I t e (.or R [d, rest]) (.or R [d', rest]) := by
  intro a ha
  rw [tr_or2, interp_sOr] at ha ⊢
  exact ⟨ha.1, ha.2.imp (h a) id⟩

theorem or_right_sub {t : VarTable} {e : Valuation M} {R : Kore.KSort} {d rest rest' : Kore.Pattern}
    (h : Sub I t e rest rest') : Sub I t e (.or R [d, rest]) (.or R [d, rest']) := by
  intro a ha
  rw [tr_or2, interp_sOr] at ha ⊢
  exact ⟨ha.1, ha.2.imp id (h a)⟩

theorem orWrap_sub {t : VarTable} {e : Valuation M} {x x' : Kore.Pattern} (h : Sub I t e x x') :
    ∀ pre : List (Kore.KSort × Kore.Pattern), Sub I t e (orWrap pre x) (orWrap pre x')
  | [] => h
  | _ :: pre => or_right_sub (orWrap_sub h pre)

/-- A negated conjunct is antitone. -/
theorem not_and_sub {t : VarTable} {e : Valuation M} {R R' : Kore.KSort} {D D' own : Kore.Pattern}
    (h : Sub I t e D' D) : Sub I t e (.and R [.not R' D, own]) (.and R [.not R' D', own]) := by
  intro a ha
  rw [tr_and2, interp_sAnd, tr_not, interp_sNot] at ha ⊢
  exact ⟨⟨fun hd => ha.1.1 (h a hd), ha.1.2⟩, ha.2⟩

/-- **An inclusion under binders.** `Inv j` holds of the valuations under the first j binders: it
holds after a binder takes an element of its sort, and where it holds under all of them every
element of `body` is one of `body'`. -/
theorem exAll_sub (hD : DefOK I) {t : VarTable} {body body' : Kore.Pattern} :
    ∀ (zs : List (Kore.KSort × Kore.EVar)) (Inv : Nat → Valuation M → Prop),
      (∀ j z, zs[j]? = some z → ∀ (e : Valuation M) (a : M), Inv j e →
        (inhOf (trSort t z.2.sort)).interpret I (updE e (t.ev (evarKey z.2)) a) a →
        Inv (j + 1) (updE e (t.ev (evarKey z.2)) a)) →
      (∀ e, Inv zs.length e → Sub I t e body body') →
      ∀ e, Inv 0 e → Sub I t e (exAll zs body) (exAll zs body')
  | [], _, _, hb, e, h0 => hb e h0
  | z :: zs, Inv, hs, hb, e, h0 => by
    intro a ha
    have hE : ∀ b, exAll (z :: zs) b = .exist z.1 z.2 (exAll zs b) := fun _ => rfl
    rw [hE, tr_exist, interp_sExists_elem hD] at ha ⊢
    obtain ⟨v, hv, hφ⟩ := ha
    exact ⟨v, hv, exAll_sub hD zs (fun j => Inv (j + 1))
      (fun j z' hz e' a' hi hin => hs (j + 1) z' (by simpa using hz) e' a' hi hin)
      (fun e' hi => hb e' (by simpa using hi)) _ (hs 0 z rfl e v h0 hv) a hφ⟩

/-- **Under a competitor's negation the inclusion swaps sides**: where every element of `body'` is
one of `body` under the binders, every element of the frame at `body` is one of the frame at
`body'`. -/
theorem Frame.fill_sub (hD : DefOK I) {t : VarTable} (F : Frame) {body body' : Kore.Pattern}
    (Inv : Nat → Valuation M → Prop)
    (hs : ∀ j z, F.zs[j]? = some z → ∀ (e : Valuation M) (a : M), Inv j e →
      (inhOf (trSort t z.2.sort)).interpret I (updE e (t.ev (evarKey z.2)) a) a →
      Inv (j + 1) (updE e (t.ev (evarKey z.2)) a))
    (hb : ∀ e, Inv F.zs.length e → Sub I t e body' body) (e : Valuation M) (h0 : Inv 0 e) :
    Sub I t e (F.fill body) (F.fill body') :=
  not_and_sub (orWrap_sub (or_left_sub (exAll_sub hD F.zs Inv hs hb e h0)) F.pre)

end

/-! ### The items -/

theorem textItem_parts {k : Cut} {pl : Place} {a : Kore.Axiom} {g : P} (h : textItem k pl a = some g) :
    ∃ R prem eq prem', a.pattern = .implies R prem eq ∧ textPremAt k pl prem = some prem' ∧
      textPat k pl a.pattern = some (.implies R prem' eq) ∧
      g = itemAt (tableOf a.sortVars a.pattern) (freeT a (.implies R prem' eq)) R (.implies R prem' eq) := by
  unfold textItem at h
  split at h
  · next R prem eq hp =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨p', hp', rfl⟩ := h
    have h2 : textPat k pl (.implies R prem eq) = some p' := hp ▸ hp'
    unfold textPat at h2
    simp only [Option.map_eq_some_iff] at h2
    obtain ⟨prem', hprem, rfl⟩ := h2
    exact ⟨R, prem, eq, prem', hp, hprem, hp', rfl⟩
  · cases h

theorem shapeOK_sub {k : Cut} {pl : Place} {a : Kore.Axiom} {p' : Kore.Pattern}
    (hp : textPat k pl a.pattern = some p') (h : shapeOK k pl a = true) :
    (∀ x ∈ freeT a p', x ∈ freeG a) ∧ (∀ x ∈ freeG a, x ∈ freeT a p') := by
  unfold shapeOK at h
  rw [hp] at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact h

theorem sortVarOK_parts {t : VarTable} {fG : List VarKey} {zs : List (Kore.KSort × Kore.EVar)} {R₂ : Kore.KSort}
    (h : sortVarOK t fG zs R₂ = true) :
    ∃ α, R₂ = .var α ∧ sortVarKey α ∈ fG ∧ ∀ z ∈ zs, t.ev (evarKey z.2) ≠ t.ev (sortVarKey α) := by
  cases R₂ with
  | var α =>
    simp only [sortVarOK, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
    exact ⟨α, rfl, h.1, h.2⟩
  | ctor _ _ => simp [sortVarOK] at h

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **Sentence to item, `andApp` at the equation's own premise**: a model of definedness of the
text's form of the equation is a model of Γ's item. -/
theorem cutEq_from_text_pure (hD : DefOK I) {path : List Nat} {a : Kore.Axiom} {g : P}
    (hg : textItem (.andApp path) .own a = some g) (hok : shapeOK (.andApp path) .own a = true)
    (h : I ⊧ᴵ g) : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat := by
  obtain ⟨R, prem, eq, prem', hp, hprem, hpat, rfl⟩ := textItem_parts hg
  obtain ⟨hTG, -⟩ := shapeOK_sub hpat hok
  simp only [textPremAt, textPrem, Option.map_eq_some_iff] at hprem
  obtain ⟨⟨R0, R₁, sB, R₂, tt, args, S, x, u, K⟩, hparts, rfl⟩ := hprem
  obtain ⟨rfl, hK⟩ := andParts_eq hparts
  intro e m
  rw [trAxiom_implies a hp]
  generalize tableOf a.sortVars a.pattern = T at h ⊢
  rw [hp]
  exact item_of_sub hD hTG h e m fun _ => and_gamma_sub ((noAlias_vars T [] [] K).trans hK) e

/-- **Item to sentence, `andApp` under a competitor's negation**: a model of definedness of Γ's
item is a model of the text's form of the equation. -/
theorem cutEq_entailed_pure (hD : DefOK I) {path : List Nat} {i n : Nat} {a : Kore.Axiom} {g : P}
    (hg : textItem (.andApp path) (.under i n) a = some g) (hok : shapeOK (.andApp path) (.under i n) a = true)
    (h : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat) : I ⊧ᴵ g := by
  obtain ⟨R, prem, eq, prem', hp, hprem, hpat, rfl⟩ := textItem_parts hg
  obtain ⟨-, hGT⟩ := shapeOK_sub hpat hok
  simp only [textPremAt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hprem
  obtain ⟨⟨F, body⟩, hF, body', hb', rfl⟩ := hprem
  have hprem := frameOf_eq hF
  subst hprem
  simp only [textPrem, Option.map_eq_some_iff] at hb'
  obtain ⟨⟨R0, R₁, sB, R₂, tt, args, S, x, u, K⟩, hparts, rfl⟩ := hb'
  obtain ⟨rfl, hK⟩ := andParts_eq hparts
  intro e m
  rw [trAxiom_implies a hp] at h
  generalize tableOf a.sortVars a.pattern = T at h ⊢
  rw [hp] at h
  exact item_of_sub hD hGT h e m fun _ =>
    F.fill_sub hD (fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial)
      (fun e' _ => and_gamma_sub ((noAlias_vars T [] [] K).trans hK) e') e trivial

open HoldsShape (NodeFacts) in
/-- **The two premises under the binders, with the constructors' facts.** For a cut premise
`bodyOK` accepts: a property of the valuations under each number of binders that holds where the
guards of the axiom's free variables hold, is kept by each binder, and under all of them makes the
two premises hold the same elements. For `notCond`, with `false` a value of Bool and the closure
of Bool. -/
theorem body_facts [Inhabited M] {c : Semantics} (N : NodeFacts c I)
    (hT : c.sortOf (KCore.bool true) = some Srt.bool) {t : VarTable} {fG : List VarKey}
    {zs : List (Kore.KSort × Kore.EVar)} {k : Cut} {body body' : Kore.Pattern}
    (hcl : k = .notCond → c.sortOf (KCore.bool false) = some Srt.bool ∧ (I ⊧ᴵ boolClosed c))
    (hok : bodyOK c t fG zs k body = true) (hb : textPrem k body = some body') :
    ∃ Inv : Nat → Valuation M → Prop,
      (∀ j z, zs[j]? = some z → ∀ (e : Valuation M) (a : M), Inv j e →
        (inhOf (trSort t z.2.sort)).interpret I (updE e (t.ev (evarKey z.2)) a) a →
        Inv (j + 1) (updE e (t.ev (evarKey z.2)) a)) ∧
      (∀ e m, (∀ kk ∈ fG, (guardOf t kk).interpret I e m) → Inv 0 e) ∧
      (∀ e, Inv zs.length e → Sub I t e body body' ∧ Sub I t e body' body) := by
  have hD := N.defOK
  obtain ⟨σB, hσB, hSB⟩ := N.sort (N.valNum hT)
  cases k with
  | andApp path =>
    simp only [textPrem, Option.map_eq_some_iff] at hb
    obtain ⟨⟨R, R₁, sB, R₂, tt, args, S, x, u, K⟩, hparts, rfl⟩ := hb
    simp only [bodyOK, hparts, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
      List.contains_iff_mem, List.any_eq_true, List.mem_range] at hok
    obtain ⟨⟨⟨⟨⟨⟨hsv, rfl⟩, rfl⟩, s, hs, rfl⟩, hxs⟩, hzs⟩, hhave⟩ := hok
    obtain ⟨α, rfl, hα, hzR⟩ := sortVarOK_parts hsv
    obtain ⟨rfl, hK⟩ := andParts_eq hparts
    have hK' : K.noAlias ⟨t, []⟩ = true := (noAlias_vars t [] [] K).trans hK
    obtain ⟨σ, hσ, hS⟩ := N.sort hs
    refine ⟨fun j e => IsSort I (e.evalEvar (t.ev (sortVarKey α))) ∧
      ((evarKey x ∈ fG ∨ ∃ z ∈ zs.take j, evarKey z.2 = evarKey x) → Inh I σ (e.evalEvar (t.ev (evarKey x)))),
      ?_, ?_, ?_⟩
    · rintro j z hz e a ⟨h1, h2⟩ hin
      have hzm : z ∈ zs := List.mem_of_getElem? hz
      refine ⟨?_, fun hh => ?_⟩
      · show IsSort I (Function.update e.evalEvar _ a _)
        rw [Function.update_noteq (hzR z hzm).symm]; exact h1
      · by_cases hk : evarKey z.2 = evarKey x
        · have hsort : z.2.sort = x.sort := by
            have h3 := hk; unfold evarKey at h3; injection h3
          show Inh I σ (Function.update e.evalEvar (t.ev (evarKey z.2)) a (t.ev (evarKey x)))
          rw [hk, Function.update_same]
          rw [hsort, hxs] at hin
          exact (interp_inhOf_of (hS t _)).mp hin
        · have hne : t.ev (evarKey z.2) ≠ t.ev (evarKey x) := (hzs z hzm).resolve_left hk
          show Inh I σ (Function.update e.evalEvar (t.ev (evarKey z.2)) a (t.ev (evarKey x)))
          rw [Function.update_noteq hne.symm]
          apply h2
          rcases hh with hh | ⟨z', hz', hk'⟩
          · exact Or.inl hh
          · rw [List.take_add_one, hz] at hz'
            rcases List.mem_append.mp hz' with hz' | hz'
            · exact Or.inr ⟨z', hz', hk'⟩
            · simp only [Option.toList_some, List.mem_singleton] at hz'
              exact absurd (hz' ▸ hk') hk
    · intro e m hg
      refine ⟨?_, fun hh => ?_⟩
      · have h3 := hg _ hα
        unfold sortVarKey guardOf sortGuard at h3
        rw [interp_member hD, interp_sortsDomain] at h3
        exact h3
      · rcases hh with hh | ⟨z', hz', -⟩
        · have h3 := (TieRuleLhs.guard_evarKey hD).mp (hg _ hh)
          rw [hxs] at h3
          exact (interp_inhOf_of (hS t e)).mp h3
        · simp at hz'
    · rintro e ⟨h1, h2⟩
      have hx := h2 (by
        rw [List.take_length]
        rcases hhave with hh | ⟨z, hz, hk⟩
        · exact Or.inl hh
        · exact Or.inr ⟨z, hz, hk⟩)
      have hR : ∀ a, (trSort t (.var α)).interpret I e a ↔ a = e.evalEvar (t.ev (sortVarKey α)) := fun a => by
        rw [trSort]; exact interp_evar
      obtain ⟨a0, ha0, hin0⟩ := N.val hT t e
      exact ⟨and_gamma_sub hK' e, and_text_sub hD N.ceilDef hK' (hSB t e) hR (hS t e) hσB h1 hσ hx
        ⟨a0, (interp_inhOf_of (hSB t e)).mp hin0, by rw [tr_ground_den]; exact (ha0 a0).mpr rfl⟩⟩
  | notCond =>
    simp only [textPrem, Option.map_eq_some_iff] at hb
    obtain ⟨⟨R, R₁, R₂, args, sB, b, ff⟩, hparts, rfl⟩ := hb
    simp only [bodyOK, hparts, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hok
    obtain ⟨⟨⟨⟨hsv, rfl⟩, rfl⟩, htt⟩, htop⟩ := hok
    obtain ⟨α, rfl, hα, hzR⟩ := sortVarOK_parts hsv
    have hpe := notParts_eq hparts
    subst hpe
    obtain ⟨hF, hclosed⟩ := hcl rfl
    refine ⟨fun _ e => IsSort I (e.evalEvar (t.ev (sortVarKey α))), ?_, ?_, ?_⟩
    · intro j z hz e a h1 _
      show IsSort I (Function.update e.evalEvar _ a _)
      rw [Function.update_noteq (hzR z (List.mem_of_getElem? hz)).symm]; exact h1
    · intro e m hg
      have h3 := hg _ hα
      unfold sortVarKey guardOf sortGuard at h3
      rw [interp_member hD, interp_sortsDomain] at h3
      exact h3
    · intro e h1
      have hR : ∀ a, (trSort t (.var α)).interpret I e a ↔ a = e.evalEvar (t.ev (sortVarKey α)) := fun a => by
        rw [trSort]; exact interp_evar
      have hB : ∀ m, Inh I σB m → ((tr ⟨t, []⟩ (.dv (srtOf c Srt.bool) "true")).interpret I e m ↔
          ¬ (tr ⟨t, []⟩ ((KCore.bool false).kore c)).interpret I e m) := by
        intro m hm
        rw [htt, tr_ground_den, tr_ground_den]
        constructor
        · intro h3 h4
          have h5 := N.apart hT hF e m h3 h4
          simp [KCore.bool] at h5
        · intro h4
          have h5 := hclosed e m
          unfold boolClosed at h5
          rw [interp_included hD] at h5
          have h6 := h5 m ((interp_inhOf_of (S := sortP (c.sortName Srt.bool)) (fun a => by
            have h7 := hSB t e a
            rwa [trSort_srtOf_twoT] at h7)).mpr hm)
          rw [interpret_disj] at h6
          exact h6.resolve_right h4
      have key := fun a => not_iff (R := R) (R₁ := R₁) (args := args) (b := b) hD N.ceilDef (hSB t e) hR hσB h1
        htop hB a
      exact ⟨fun a => (key a).mp, fun a => (key a).mpr⟩

open HoldsShape (NodeFacts) in
/-- **The two premises of the equation hold the same elements** where the guards of its free
variables hold, with the constructors' facts. -/
theorem place_facts [Inhabited M] {c : Semantics} (N : NodeFacts c I)
    (hT : c.sortOf (KCore.bool true) = some Srt.bool) {k : Cut} {pl : Place} {a : Kore.Axiom}
    {R : Kore.KSort} {prem eq prem' : Kore.Pattern} (hp : a.pattern = .implies R prem eq)
    (hprem : textPremAt k pl prem = some prem')
    (hcl : k = .notCond → c.sortOf (KCore.bool false) = some Srt.bool ∧ (I ⊧ᴵ boolClosed c))
    (hok : factsOK c k pl a = true) (e : Valuation M) (m : M)
    (hg : ∀ kk ∈ freeG a, (guardOf (tableOf a.sortVars a.pattern) kk).interpret I e m) :
    Sub I (tableOf a.sortVars a.pattern) e prem prem' ∧ Sub I (tableOf a.sortVars a.pattern) e prem' prem := by
  unfold factsOK at hok
  generalize tableOf a.sortVars a.pattern = T at hok hg ⊢
  rw [hp] at hok
  cases pl with
  | own =>
    simp only [cutBody] at hok
    obtain ⟨Inv, -, h0, hb⟩ := body_facts N hT hcl hok hprem
    exact hb e (h0 e m hg)
  | under i n =>
    simp only [textPremAt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hprem
    obtain ⟨⟨F, body⟩, hF, body', hb', rfl⟩ := hprem
    simp only [cutBody, hF, Option.map_some] at hok
    have hpe := frameOf_eq hF
    subst hpe
    obtain ⟨Inv, hs, h0, hb⟩ := body_facts N hT hcl hok hb'
    exact ⟨F.fill_sub N.defOK Inv hs (fun e' h => (hb e' h).2) e (h0 e m hg),
      F.fill_sub N.defOK Inv hs (fun e' h => (hb e' h).1) e (h0 e m hg)⟩

open HoldsShape (NodeFacts) in
/-- **Sentence to item**: with the constructors' facts, a model of the text's form of the
equation is a model of Γ's item; for `notCond`, where `false` is a value of Bool and Bool is
closed. -/
theorem cutEq_from_text [Inhabited M] {c : Semantics} (N : NodeFacts c I)
    (hT : c.sortOf (KCore.bool true) = some Srt.bool) {k : Cut} {pl : Place} {a : Kore.Axiom} {g : P}
    (hcl : k = .notCond → c.sortOf (KCore.bool false) = some Srt.bool ∧ (I ⊧ᴵ boolClosed c))
    (hg : textItem k pl a = some g) (hs : shapeOK k pl a = true) (hf : factsOK c k pl a = true)
    (h : I ⊧ᴵ g) : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat := by
  obtain ⟨R, prem, eq, prem', hp, hprem, hpat, rfl⟩ := textItem_parts hg
  obtain ⟨hTG, -⟩ := shapeOK_sub hpat hs
  intro e m
  rw [trAxiom_implies a hp]
  have key := fun hgd => (place_facts N hT hp hprem hcl hf e m hgd).1
  generalize tableOf a.sortVars a.pattern = T at h key ⊢
  rw [hp]
  exact item_of_sub N.defOK hTG h e m key

open HoldsShape (NodeFacts) in
/-- **Item to sentence**: with the constructors' facts, a model of Γ's item is a model of the
text's form of the equation; for `notCond`, where `false` is a value of Bool and Bool is closed. -/
theorem cutEq_entailed [Inhabited M] {c : Semantics} (N : NodeFacts c I)
    (hT : c.sortOf (KCore.bool true) = some Srt.bool) {k : Cut} {pl : Place} {a : Kore.Axiom} {g : P}
    (hcl : k = .notCond → c.sortOf (KCore.bool false) = some Srt.bool ∧ (I ⊧ᴵ boolClosed c))
    (hg : textItem k pl a = some g) (hs : shapeOK k pl a = true) (hf : factsOK c k pl a = true)
    (h : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat) : I ⊧ᴵ g := by
  obtain ⟨R, prem, eq, prem', hp, hprem, hpat, rfl⟩ := textItem_parts hg
  obtain ⟨-, hGT⟩ := shapeOK_sub hpat hs
  intro e m
  rw [trAxiom_implies a hp] at h
  have key := fun (hgd : ∀ kk ∈ freeT a (.implies R prem' eq),
      (guardOf (tableOf a.sortVars a.pattern) kk).interpret I e m) =>
    (place_facts N hT hp hprem hcl hf e m fun kk hk => hgd kk (hGT kk hk)).2
  generalize tableOf a.sortVars a.pattern = T at h key ⊢
  rw [hp] at h
  exact item_of_sub N.defOK hGT h e m key

open HoldsShape (NodeFacts) in
/-- **The text's form of the equation and Γ's item hold in the same models with the
constructors' facts** (for `notCond`: in which Bool is closed). -/
theorem cutEq_iff [Inhabited M] {c : Semantics} (N : NodeFacts c I)
    (hT : c.sortOf (KCore.bool true) = some Srt.bool) {k : Cut} {pl : Place} {a : Kore.Axiom} {g : P}
    (hcl : k = .notCond → c.sortOf (KCore.bool false) = some Srt.bool ∧ (I ⊧ᴵ boolClosed c))
    (hg : textItem k pl a = some g) (hs : shapeOK k pl a = true) (hf : factsOK c k pl a = true) :
    (I ⊧ᴵ g) ↔ (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat) :=
  ⟨cutEq_from_text N hT hcl hg hs hf, cutEq_entailed N hT hcl hg hs hf⟩

end

/-- `factsOK` reads the definition's sort names only. -/
theorem factsOK_withHooks (c : Semantics) (H : HookParams) (k : Cut) (pl : Place) (a : Kore.Axiom) :
    factsOK (c.withHooks H) k pl a = factsOK c k pl a := rfl

end TieCutEq

end KCore
