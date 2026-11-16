/-
  Copyright (c) 2023 Institute for Logic and Data Science (ILDS). All rights reserved.
  Released under MIT license as described in the file LICENSE.
  Authors: Horațiu Cheval

  Ported to Lean v4.34.0 for k-rust (2026-11); the changes are listed in README.md.
  The syntax follows the KORE grammar of `haskell-backend/docs/kore-syntax.md`.
-/

set_option autoImplicit false

namespace Kore

/-! ## Identifiers

Identifiers are plain strings wrapped by role.
A set variable's identifier is stored without its leading `@`;
a symbol identifier keeps a leading `\` when the text has one. -/

structure Identifier where
  name : String
  deriving Repr, BEq, DecidableEq, Hashable, Ord, Inhabited

instance : ToString Identifier where toString := Identifier.name

structure SymbolIdent where
  ident : Identifier
  deriving Repr, BEq, DecidableEq, Hashable, Ord, Inhabited

instance : ToString SymbolIdent where toString id := toString id.ident

structure EVarIdent where
  ident : Identifier
  deriving Repr, BEq, DecidableEq, Hashable, Ord, Inhabited

instance : ToString EVarIdent where toString id := toString id.ident

structure SVarIdent where
  ident : Identifier
  deriving Repr, BEq, DecidableEq, Hashable, Ord, Inhabited

instance : ToString SVarIdent where toString id := toString id.ident

structure SortIdent where
  ident : Identifier
  deriving Repr, BEq, DecidableEq, Hashable, Ord, Inhabited

instance : ToString SortIdent where toString id := toString id.ident

structure ModuleName where
  ident : Identifier
  deriving Repr, BEq, DecidableEq, Hashable, Ord, Inhabited

instance : ToString ModuleName where toString name := toString name.ident

structure SortVar where
  ident : SortIdent
  deriving Repr, BEq, DecidableEq, Hashable, Ord, Inhabited

instance : ToString SortVar where toString v := toString v.ident

/-! ## Sorts -/

/-- A sort: a sort variable (`R`), or a sort constructor applied to sorts (`SortK{}`, `SortMap{}`).
The two differ in the text by the braces: `R` is a variable, `R{}` a constructor with no arguments. -/
inductive KSort where
  | var (var : SortVar)
  | ctor (head : SortIdent) (args : List KSort)
  deriving Repr, BEq, Hashable, Inhabited

/- `DecidableEq` for the nested inductive `KSort`, by mutual structural recursion
(Lean v4.34.0 does not derive it for nested inductives). -/
mutual
  def KSort.decEq : (a b : KSort) → Decidable (a = b)
    | .var v, .var w =>
      if h : v = w then isTrue (h ▸ rfl) else isFalse (fun e => by injection e; contradiction)
    | .ctor h as, .ctor g bs =>
      if e₁ : h = g then
        match KSort.decEqList as bs with
        | isTrue e₂ => isTrue (e₁ ▸ e₂ ▸ rfl)
        | isFalse e₂ => isFalse (fun e => by injection e; contradiction)
      else isFalse (fun e => by injection e; contradiction)
    | .var _, .ctor _ _ => isFalse (fun e => by cases e)
    | .ctor _ _, .var _ => isFalse (fun e => by cases e)
    termination_by structural a => a
  def KSort.decEqList : (as bs : List KSort) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | a :: as, b :: bs =>
      match KSort.decEq a b, KSort.decEqList as bs with
      | isTrue e₁, isTrue e₂ => isTrue (e₁ ▸ e₂ ▸ rfl)
      | isFalse e₁, _ => isFalse (fun e => by injection e; contradiction)
      | _, isFalse e₂ => isFalse (fun e => by injection e; contradiction)
    | [], _ :: _ => isFalse (fun e => by cases e)
    | _ :: _, [] => isFalse (fun e => by cases e)
    termination_by structural as => as
end

instance : DecidableEq KSort := KSort.decEq

/-! ## Variables -/

structure EVar where
  var : EVarIdent
  sort : KSort
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

structure SVar where
  var : SVarIdent
  sort : KSort
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

inductive VarPattern where
  | evar : EVar → VarPattern
  | svar : SVar → VarPattern
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

/-! ## Patterns

One inductive with `List` children, so that functions over it can recurse structurally
(mutually with a function over `List Pattern`; see `KoreParser/Stats.lean`).
String literals and domain values hold the decoded code points, not the escaped text. -/

inductive Pattern where
  | var : VarPattern → Pattern
  /-- `σ{s₁,…,sₖ}(φ₁,…,φₙ)` -/
  | app (head : SymbolIdent) (sorts : List KSort) (args : List Pattern)
  /-- a string literal `"…"` (decoded) -/
  | string : String → Pattern
  | top (sort : KSort)
  | bottom (sort : KSort)
  | not (sort : KSort) (patt : Pattern)
  /-- `\and{s}(φ₁,…,φₙ)`: n-ary, as the grammar allows (`<patterns>`). -/
  | and (sort : KSort) (patts : List Pattern)
  /-- `\or{s}(φ₁,…,φₙ)`: n-ary, as the grammar allows (`<patterns>`). -/
  | or (sort : KSort) (patts : List Pattern)
  | implies (sort : KSort) (patt₁ patt₂ : Pattern)
  | iff (sort : KSort) (patt₁ patt₂ : Pattern)
  | exist (sort : KSort) (var : EVar) (patt : Pattern)
  | «forall» (sort : KSort) (var : EVar) (patt : Pattern)
  | mu (var : SVar) (patt : Pattern)
  | nu (var : SVar) (patt : Pattern)
  /-- `\ceil{operand, result}(φ)` -/
  | ceil (source : KSort) (target : KSort) (patt : Pattern)
  | floor (source : KSort) (target : KSort) (patt : Pattern)
  | equals (source : KSort) (target : KSort) (patt₁ patt₂ : Pattern)
  | «in» (source : KSort) (target : KSort) (patt₁ patt₂ : Pattern)
  | next (sort : KSort) (patt : Pattern)
  | rewrites (sort : KSort) (patt₁ patt₂ : Pattern)
  /-- `\dv{s}("…")` (decoded) -/
  | dv (sort : KSort) (value : String)
  /-- `\left-assoc{}(σ{…}(φ₁,…,φₙ))`, kept unexpanded. -/
  | leftAssoc (head : SymbolIdent) (sorts : List KSort) (args : List Pattern)
  /-- `\right-assoc{}(σ{…}(φ₁,…,φₙ))`, kept unexpanded. -/
  | rightAssoc (head : SymbolIdent) (sorts : List KSort) (args : List Pattern)
  deriving Repr, BEq, Hashable, Inhabited

/- `DecidableEq` for the nested inductive `Pattern`, by mutual structural recursion:
equal constructor indices first, then the fields. -/
mutual
  def Pattern.decEq (x y : Pattern) : Decidable (x = y) :=
    if hc : x.ctorIdx = y.ctorIdx then
      match x, y, hc with
      | .var a, .var b, _ =>
        if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by injection e; contradiction)
      | .app h₁ s₁ a₁, .app h₂ s₂ a₂, _ =>
        if e₁ : h₁ = h₂ then if e₂ : s₁ = s₂ then
          match Pattern.decEqList a₁ a₂ with
          | isTrue e₃ => isTrue (e₁ ▸ e₂ ▸ e₃ ▸ rfl)
          | isFalse e₃ => isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
      | .string a, .string b, _ =>
        if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by injection e; contradiction)
      | .top a, .top b, _ =>
        if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by injection e; contradiction)
      | .bottom a, .bottom b, _ =>
        if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by injection e; contradiction)
      | .not s₁ p₁, .not s₂ p₂, _ =>
        if e₁ : s₁ = s₂ then
          match Pattern.decEq p₁ p₂ with
          | isTrue e₂ => isTrue (e₁ ▸ e₂ ▸ rfl)
          | isFalse e₂ => isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
      | .and s₁ p₁, .and s₂ p₂, _ =>
        if e₁ : s₁ = s₂ then
          match Pattern.decEqList p₁ p₂ with
          | isTrue e₂ => isTrue (e₁ ▸ e₂ ▸ rfl)
          | isFalse e₂ => isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
      | .or s₁ p₁, .or s₂ p₂, _ =>
        if e₁ : s₁ = s₂ then
          match Pattern.decEqList p₁ p₂ with
          | isTrue e₂ => isTrue (e₁ ▸ e₂ ▸ rfl)
          | isFalse e₂ => isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
      | .implies s₁ p₁ q₁, .implies s₂ p₂ q₂, _ =>
        if e₁ : s₁ = s₂ then
          match Pattern.decEq p₁ p₂, Pattern.decEq q₁ q₂ with
          | isTrue e₂, isTrue e₃ => isTrue (e₁ ▸ e₂ ▸ e₃ ▸ rfl)
          | isFalse e₂, _ => isFalse (fun e => by injection e; contradiction)
          | _, isFalse e₃ => isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
      | .iff s₁ p₁ q₁, .iff s₂ p₂ q₂, _ =>
        if e₁ : s₁ = s₂ then
          match Pattern.decEq p₁ p₂, Pattern.decEq q₁ q₂ with
          | isTrue e₂, isTrue e₃ => isTrue (e₁ ▸ e₂ ▸ e₃ ▸ rfl)
          | isFalse e₂, _ => isFalse (fun e => by injection e; contradiction)
          | _, isFalse e₃ => isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
      | .exist s₁ v₁ p₁, .exist s₂ v₂ p₂, _ =>
        if e₁ : s₁ = s₂ then if e₂ : v₁ = v₂ then
          match Pattern.decEq p₁ p₂ with
          | isTrue e₃ => isTrue (e₁ ▸ e₂ ▸ e₃ ▸ rfl)
          | isFalse e₃ => isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
      | .forall s₁ v₁ p₁, .forall s₂ v₂ p₂, _ =>
        if e₁ : s₁ = s₂ then if e₂ : v₁ = v₂ then
          match Pattern.decEq p₁ p₂ with
          | isTrue e₃ => isTrue (e₁ ▸ e₂ ▸ e₃ ▸ rfl)
          | isFalse e₃ => isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
      | .mu v₁ p₁, .mu v₂ p₂, _ =>
        if e₁ : v₁ = v₂ then
          match Pattern.decEq p₁ p₂ with
          | isTrue e₂ => isTrue (e₁ ▸ e₂ ▸ rfl)
          | isFalse e₂ => isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
      | .nu v₁ p₁, .nu v₂ p₂, _ =>
        if e₁ : v₁ = v₂ then
          match Pattern.decEq p₁ p₂ with
          | isTrue e₂ => isTrue (e₁ ▸ e₂ ▸ rfl)
          | isFalse e₂ => isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
      | .ceil s₁ t₁ p₁, .ceil s₂ t₂ p₂, _ =>
        if e₁ : s₁ = s₂ then if e₂ : t₁ = t₂ then
          match Pattern.decEq p₁ p₂ with
          | isTrue e₃ => isTrue (e₁ ▸ e₂ ▸ e₃ ▸ rfl)
          | isFalse e₃ => isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
      | .floor s₁ t₁ p₁, .floor s₂ t₂ p₂, _ =>
        if e₁ : s₁ = s₂ then if e₂ : t₁ = t₂ then
          match Pattern.decEq p₁ p₂ with
          | isTrue e₃ => isTrue (e₁ ▸ e₂ ▸ e₃ ▸ rfl)
          | isFalse e₃ => isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
      | .equals s₁ t₁ p₁ q₁, .equals s₂ t₂ p₂ q₂, _ =>
        if e₁ : s₁ = s₂ then if e₂ : t₁ = t₂ then
          match Pattern.decEq p₁ p₂, Pattern.decEq q₁ q₂ with
          | isTrue e₃, isTrue e₄ => isTrue (e₁ ▸ e₂ ▸ e₃ ▸ e₄ ▸ rfl)
          | isFalse e₃, _ => isFalse (fun e => by injection e; contradiction)
          | _, isFalse e₄ => isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
      | .in s₁ t₁ p₁ q₁, .in s₂ t₂ p₂ q₂, _ =>
        if e₁ : s₁ = s₂ then if e₂ : t₁ = t₂ then
          match Pattern.decEq p₁ p₂, Pattern.decEq q₁ q₂ with
          | isTrue e₃, isTrue e₄ => isTrue (e₁ ▸ e₂ ▸ e₃ ▸ e₄ ▸ rfl)
          | isFalse e₃, _ => isFalse (fun e => by injection e; contradiction)
          | _, isFalse e₄ => isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
      | .next s₁ p₁, .next s₂ p₂, _ =>
        if e₁ : s₁ = s₂ then
          match Pattern.decEq p₁ p₂ with
          | isTrue e₂ => isTrue (e₁ ▸ e₂ ▸ rfl)
          | isFalse e₂ => isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
      | .rewrites s₁ p₁ q₁, .rewrites s₂ p₂ q₂, _ =>
        if e₁ : s₁ = s₂ then
          match Pattern.decEq p₁ p₂, Pattern.decEq q₁ q₂ with
          | isTrue e₂, isTrue e₃ => isTrue (e₁ ▸ e₂ ▸ e₃ ▸ rfl)
          | isFalse e₂, _ => isFalse (fun e => by injection e; contradiction)
          | _, isFalse e₃ => isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
      | .dv s₁ v₁, .dv s₂ v₂, _ =>
        if e₁ : s₁ = s₂ then if e₂ : v₁ = v₂ then isTrue (e₁ ▸ e₂ ▸ rfl)
        else isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
      | .leftAssoc h₁ s₁ a₁, .leftAssoc h₂ s₂ a₂, _ =>
        if e₁ : h₁ = h₂ then if e₂ : s₁ = s₂ then
          match Pattern.decEqList a₁ a₂ with
          | isTrue e₃ => isTrue (e₁ ▸ e₂ ▸ e₃ ▸ rfl)
          | isFalse e₃ => isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
      | .rightAssoc h₁ s₁ a₁, .rightAssoc h₂ s₂ a₂, _ =>
        if e₁ : h₁ = h₂ then if e₂ : s₁ = s₂ then
          match Pattern.decEqList a₁ a₂ with
          | isTrue e₃ => isTrue (e₁ ▸ e₂ ▸ e₃ ▸ rfl)
          | isFalse e₃ => isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
        else isFalse (fun e => by injection e; contradiction)
    else isFalse (fun e => hc (congrArg Pattern.ctorIdx e))
    termination_by structural x
  def Pattern.decEqList : (xs ys : List Pattern) → Decidable (xs = ys)
    | [], [] => isTrue rfl
    | p :: ps, q :: qs =>
      match Pattern.decEq p q, Pattern.decEqList ps qs with
      | isTrue e₁, isTrue e₂ => isTrue (e₁ ▸ e₂ ▸ rfl)
      | isFalse e₁, _ => isFalse (fun e => by injection e; contradiction)
      | _, isFalse e₂ => isFalse (fun e => by injection e; contradiction)
    | [], _ :: _ => isFalse (fun e => by cases e)
    | _ :: _, [] => isFalse (fun e => by cases e)
    termination_by structural xs => xs
end

instance : DecidableEq Pattern := Pattern.decEq

/-- An application pattern: an attribute, or the left-hand side of an alias sentence. -/
structure AppPattern where
  head : SymbolIdent
  sorts : List KSort
  args : List Pattern
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

def AppPattern.toPattern (a : AppPattern) : Pattern := .app a.head a.sorts a.args

/-! ## Sentences, modules, definitions

Attributes are application patterns, as the grammar says.
Their order is kept, so that printing reproduces the text. -/

/-- `σ{α₁,…,αₖ}`: the declared head of a symbol or alias with its sort parameters. -/
structure SymbolOrAlias where
  ident : SymbolIdent
  sortVars : List SortVar
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

structure Symbol extends SymbolOrAlias
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

structure Alias extends SymbolOrAlias
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

structure Import where
  module : ModuleName
  attributes : List AppPattern
  deriving Repr, BEq, DecidableEq, Inhabited

structure SentenceSort where
  sort : SortIdent
  sortVars : List SortVar
  attributes : List AppPattern
  deriving Repr, BEq, DecidableEq, Inhabited

structure HookedSort where
  sort : SortIdent
  sortVars : List SortVar
  attributes : List AppPattern
  deriving Repr, BEq, DecidableEq, Inhabited

structure SentenceSymbol where
  symbol : Symbol
  sorts : List KSort
  sort : KSort
  attributes : List AppPattern
  deriving Repr, BEq, DecidableEq, Inhabited

structure HookedSymbol where
  symbol : Symbol
  sorts : List KSort
  sort : KSort
  attributes : List AppPattern
  deriving Repr, BEq, DecidableEq, Inhabited

structure SentenceAlias where
  alias : Alias
  sorts : List KSort
  sort : KSort
  app : AppPattern
  body : Pattern
  attributes : List AppPattern
  deriving Repr, BEq, DecidableEq, Inhabited

structure Axiom where
  sortVars : List SortVar
  pattern : Pattern
  attributes : List AppPattern
  deriving Repr, BEq, DecidableEq, Inhabited

structure Claim where
  sortVars : List SortVar
  pattern : Pattern
  attributes : List AppPattern
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Sentence where
  | «import» : Import → Sentence
  | sort : SentenceSort → Sentence
  | hookedSort : HookedSort → Sentence
  | symbol : SentenceSymbol → Sentence
  | hookedSymbol : HookedSymbol → Sentence
  | alias : SentenceAlias → Sentence
  | «axiom» : Axiom → Sentence
  | claim : Claim → Sentence
  deriving Repr, BEq, DecidableEq, Inhabited

structure Module where
  name : ModuleName
  sentences : List Sentence
  attributes : List AppPattern
  deriving Repr, BEq, DecidableEq, Inhabited

structure Definition where
  attributes : List AppPattern
  modules : List Module
  deriving Repr, BEq, DecidableEq, Inhabited

end Kore
