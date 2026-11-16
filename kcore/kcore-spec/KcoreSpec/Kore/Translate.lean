/-
  The translation of a KORE definition into an AML theory Γ_D.

  Rule ids (T-…, D-…, G-…, S-…) refer to TRANSLATION.md, which states each rule with its
  source or marks it CHOICE.
  Every function on patterns and sorts is total and structurally recursive
  (mutually with the function on the `List` of children).
-/
import KcoreSpec.Kore.Signature

set_option autoImplicit false

namespace KoreAML

open ML

/-! ## Variables

[Thesis] §7.2 keeps a variable's sort as a superscript: `x : s` becomes the AML variable `xˢ`.
A `VarKey` is that pair; sort variables (S-param) are keys of their own kind.
A table assigns each key an index from 1; index 0 is `topVar`. -/

inductive VarKey where
  | sortVar (name : String)
  | evar (name : String) (sort : Kore.KSort)
  | svar (name : String) (sort : Kore.KSort)
  deriving DecidableEq, Repr, Inhabited

abbrev VarTable := List VarKey

def VarTable.index (t : VarTable) (k : VarKey) : Nat := t.idxOf k + 1
def VarTable.ev (t : VarTable) (k : VarKey) : EVar := ⟨t.index k⟩
def VarTable.sv (t : VarTable) (k : VarKey) : SVar := ⟨t.index k⟩

def evarKey (x : Kore.EVar) : VarKey := .evar x.var.ident.name x.sort
def svarKey (X : Kore.SVar) : VarKey := .svar X.var.ident.name X.sort
def sortVarKey (α : Kore.SortVar) : VarKey := .sortVar α.ident.ident.name

mutual
  /-- The sort variables of a sort, in order of occurrence. -/
  def sortVarsOf : Kore.KSort → List VarKey
    | .var α => [sortVarKey α]
    | .ctor _ args => sortVarsOfList args
    termination_by structural s => s
  def sortVarsOfList : List Kore.KSort → List VarKey
    | [] => []
    | s :: ss => sortVarsOf s ++ sortVarsOfList ss
    termination_by structural ss => ss
end

mutual
  /-- Every variable occurring in a pattern (free or bound), and the sort variables of every
  sort in it, in order of first occurrence (with repetitions). -/
  def varsOf : Kore.Pattern → List VarKey
    | .var (.evar x) => sortVarsOf x.sort ++ [evarKey x]
    | .var (.svar X) => sortVarsOf X.sort ++ [svarKey X]
    | .app _ ss ps | .leftAssoc _ ss ps | .rightAssoc _ ss ps => sortVarsOfList ss ++ varsOfList ps
    | .string _ => []
    | .top s | .bottom s | .dv s _ => sortVarsOf s
    | .not s p | .next s p => sortVarsOf s ++ varsOf p
    | .and s ps | .or s ps => sortVarsOf s ++ varsOfList ps
    | .implies s p q | .iff s p q | .rewrites s p q => sortVarsOf s ++ varsOf p ++ varsOf q
    | .exist s x p | .forall s x p => sortVarsOf s ++ sortVarsOf x.sort ++ [evarKey x] ++ varsOf p
    | .mu X p | .nu X p => sortVarsOf X.sort ++ [svarKey X] ++ varsOf p
    | .ceil s s' p | .floor s s' p => sortVarsOf s ++ sortVarsOf s' ++ varsOf p
    | .equals s s' p q | .in s s' p q => sortVarsOf s ++ sortVarsOf s' ++ varsOf p ++ varsOf q
    termination_by structural p => p
  def varsOfList : List Kore.Pattern → List VarKey
    | [] => []
    | p :: ps => varsOf p ++ varsOfList ps
    termination_by structural ps => ps
end

mutual
  /-- The free element and set variables of a pattern, in order of first occurrence
  (with repetitions); `bound` lists the variables bound around the pattern. -/
  def freeOf (bound : List VarKey) : Kore.Pattern → List VarKey
    | .var (.evar x) => if bound.contains (evarKey x) then [] else [evarKey x]
    | .var (.svar X) => if bound.contains (svarKey X) then [] else [svarKey X]
    | .app _ _ ps | .leftAssoc _ _ ps | .rightAssoc _ _ ps
    | .and _ ps | .or _ ps => freeOfList bound ps
    | .string _ | .top _ | .bottom _ | .dv _ _ => []
    | .not _ p | .next _ p | .ceil _ _ p | .floor _ _ p => freeOf bound p
    | .implies _ p q | .iff _ p q | .rewrites _ p q
    | .equals _ _ p q | .in _ _ p q => freeOf bound p ++ freeOf bound q
    | .exist _ x p | .forall _ x p => freeOf (evarKey x :: bound) p
    | .mu X p | .nu X p => freeOf (svarKey X :: bound) p
    termination_by structural p => p
  def freeOfList (bound : List VarKey) : List Kore.Pattern → List VarKey
    | [] => []
    | p :: ps => freeOf bound p ++ freeOfList bound ps
    termination_by structural ps => ps
end

/-- The table of an axiom: its declared sort variables first, then every variable of its pattern. -/
def tableOf (sortVars : List Kore.SortVar) (φ : Kore.Pattern) : VarTable :=
  (sortVars.map sortVarKey ++ varsOf φ).eraseDups

/-! ## Sorts (T-sort)

A sort variable `α` becomes the AML element variable `α` (S-param);
a sort `C{s₁,…,sₖ}` becomes the symbol `C` applied to the translated arguments (S-param,
[Thesis] §7.3.2: parametric sorts as functions over `Sort`). -/

mutual
  def trSort (t : VarTable) : Kore.KSort → P
    | .var α => .evar (t.ev (sortVarKey α))
    | .ctor C args => trSortApp t (sym (.sort C.ident.name)) args
    termination_by structural s => s
  def trSortApp (t : VarTable) (acc : P) : List Kore.KSort → P
    | [] => acc
    | s :: ss => trSortApp t (acc ⬝ trSort t s) ss
    termination_by structural ss => ss
end

/-! ## Patterns: AML2 ([Thesis] (7.12)–(7.18)) extended to KORE's connectives -/

/-- The context of the pattern translation: the variable table and the names of the
definition's aliases (whose applications are not expanded: T-alias). -/
structure Ctx where
  vars : VarTable
  aliases : List String

mutual
  def tr (c : Ctx) : Kore.Pattern → P
    -- T-evar (7.12), T-svar (7.13)
    | .var (.evar x) => .evar (c.vars.ev (evarKey x))
    | .var (.svar X) => .svar (c.vars.sv (svarKey X))
    -- T-app (7.14) with explicit sort arguments (S-args); T-alias
    | .app h ss ps =>
      if c.aliases.contains h.ident.name then sym (.untranslated s!"alias {h.ident.name}")
      else trArgs c (trSortApp c.vars (sym (.symbol h.ident.name)) ss) ps
    -- T-string (CHOICE)
    | .string s => sym (.str s)
    -- T-top, T-bottom (2.96), (2.97)
    | .top s => sTop (trSort c.vars s)
    | .bottom s => sBot (trSort c.vars s)
    -- T-not (7.16)
    | .not s p => sNot (trSort c.vars s) (tr c p)
    -- T-and (7.15), T-or (2.95), n-ary (CHOICE T-nary)
    | .and s ps => trAndList c (trSort c.vars s) ps
    | .or s ps => trOrList c (trSort c.vars s) ps
    -- T-implies, T-iff (2.96)
    | .implies s p q => sImp (trSort c.vars s) (tr c p) (tr c q)
    | .iff s p q => sIff (trSort c.vars s) (tr c p) (tr c q)
    -- T-exists (7.17), T-forall (2.95)
    | .exist _ x p => sExists (c.vars.ev (evarKey x)) (trSort c.vars x.sort) (tr c p)
    | .forall s x p => sForall (trSort c.vars s) (c.vars.ev (evarKey x)) (trSort c.vars x.sort) (tr c p)
    -- T-mu (7.18), T-nu (4.6)
    | .mu X p => .mu (c.vars.sv (svarKey X)) (tr c p)
    | .nu X p => sNu (trSort c.vars X.sort) (c.vars.sv (svarKey X)) (tr c p)
    -- T-ceil (2.98), T-floor (2.100), T-equals (2.101), T-in (2.102)
    | .ceil s s' p => sCeil (trSort c.vars s) (trSort c.vars s') (tr c p)
    | .floor s s' p => sFloor (trSort c.vars s) (trSort c.vars s') (tr c p)
    | .equals s s' p q => sEquals (trSort c.vars s) (trSort c.vars s') (tr c p) (tr c q)
    | .in s s' p q => sIn (trSort c.vars s) (trSort c.vars s') (tr c p) (tr c q)
    -- T-next, T-rewrites
    | .next _ p => sNext (tr c p)
    | .rewrites s p q => sRewrites (trSort c.vars s) (tr c p) (tr c q)
    -- T-dv (CHOICE)
    | .dv s lit => sym (.dv lit) ⬝ trSort c.vars s
    -- T-assoc
    | .leftAssoc h ss ps => trLeftAssoc c (trSortApp c.vars (sym (.symbol h.ident.name)) ss) ps
    | .rightAssoc h ss ps => trRightAssoc c (trSortApp c.vars (sym (.symbol h.ident.name)) ss) ps
    termination_by structural p => p
  /-- `σ s̄ φ₁ … φₙ`: the arguments of an application, left-nested. -/
  def trArgs (c : Ctx) (acc : P) : List Kore.Pattern → P
    | [] => acc
    | p :: ps => trArgs c (acc ⬝ tr c p) ps
    termination_by structural ps => ps
  /-- `\and{s}(φ₁,…,φₙ)`: `φ₁ ∧ (φ₂ ∧ …)`; one operand is itself; none is `⊤_s`. -/
  def trAndList (c : Ctx) (s : P) : List Kore.Pattern → P
    | [] => sTop s
    | p :: ps => match ps with
      | [] => tr c p
      | _ :: _ => sAnd (tr c p) (trAndList c s ps)
    termination_by structural ps => ps
  /-- `\or{s}(φ₁,…,φₙ)`: `φ₁ ∨ (φ₂ ∨ …)`; one operand is itself; none is `⊥_s`. -/
  def trOrList (c : Ctx) (s : P) : List Kore.Pattern → P
    | [] => sBot s
    | p :: ps => match ps with
      | [] => tr c p
      | _ :: _ => sOr s (tr c p) (trOrList c s ps)
    termination_by structural ps => ps
  /-- `\left-assoc{}(σ{s̄}(φ₁,…,φₙ))` is `σ{s̄}(…σ{s̄}(φ₁,φ₂)…,φₙ)` (kore-syntax.md);
  the accumulator after the first operand is the chain so far. Zero operands: `σ s̄`. -/
  def trLeftAssoc (c : Ctx) (head : P) : List Kore.Pattern → P
    | [] => head
    | p :: ps => trLeftAssocRest c head (tr c p) ps
    termination_by structural ps => ps
  def trLeftAssocRest (c : Ctx) (head acc : P) : List Kore.Pattern → P
    | [] => acc
    | p :: ps => trLeftAssocRest c head (head ⬝ acc ⬝ tr c p) ps
    termination_by structural ps => ps
  /-- `\right-assoc{}(σ{s̄}(φ₁,…,φₙ))` is `σ{s̄}(φ₁,σ{s̄}(φ₂,…))`. Zero operands: `σ s̄`. -/
  def trRightAssoc (c : Ctx) (head : P) : List Kore.Pattern → P
    | [] => head
    | p :: ps => match ps with
      | [] => tr c p
      | _ :: _ => head ⬝ tr c p ⬝ trRightAssoc c head ps
    termination_by structural ps => ps
end

/-! ## Declarations of a definition -/

structure SortDecl where
  name : String
  params : List Kore.SortVar
  hooked : Bool
  deriving Repr

structure SymbolDecl where
  name : String
  params : List Kore.SortVar
  args : List Kore.KSort
  result : Kore.KSort
  hooked : Bool
  attributes : List String
  deriving Repr

structure AxiomDecl where
  /-- 1-based position among the definition's axioms, in text order. -/
  index : Nat
  module : String
  ax : Kore.Axiom

def attrNames (as : List Kore.AppPattern) : List String := as.map (·.head.ident.name)

def _root_.Kore.Definition.sortDecls (d : Kore.Definition) : List SortDecl :=
  d.modules.flatMap fun m => m.sentences.filterMap fun
    | .sort s => some ⟨s.sort.ident.name, s.sortVars, false⟩
    | .hookedSort s => some ⟨s.sort.ident.name, s.sortVars, true⟩
    | _ => none

def _root_.Kore.Definition.symbolDecls (d : Kore.Definition) : List SymbolDecl :=
  d.modules.flatMap fun m => m.sentences.filterMap fun
    | .symbol s => some ⟨s.symbol.ident.ident.name, s.symbol.sortVars, s.sorts, s.sort, false,
        attrNames s.attributes⟩
    | .hookedSymbol s => some ⟨s.symbol.ident.ident.name, s.symbol.sortVars, s.sorts, s.sort, true,
        attrNames s.attributes⟩
    | _ => none

def _root_.Kore.Definition.aliasNames (d : Kore.Definition) : List String :=
  d.modules.flatMap fun m => m.sentences.filterMap fun
    | .alias a => some a.alias.ident.ident.name
    | _ => none

def _root_.Kore.Definition.axiomDecls (d : Kore.Definition) : List AxiomDecl :=
  let raw := d.modules.flatMap fun m => m.sentences.filterMap fun
    | .axiom a => some (m.name.ident.name, a)
    | _ => none
  (List.range raw.length).zip raw |>.map fun (i, (m, a)) => ⟨i + 1, m, a⟩

/-! ## The sort of a pattern (needed by (7.10) for `⊤_s`) -/

mutual
  def substSort (σ : List (String × Kore.KSort)) : Kore.KSort → Kore.KSort
    | .var α => (σ.lookup α.ident.ident.name).getD (.var α)
    | .ctor C args => .ctor C (substSortList σ args)
    termination_by structural s => s
  def substSortList (σ : List (String × Kore.KSort)) : List Kore.KSort → List Kore.KSort
    | [] => []
    | s :: ss => substSort σ s :: substSortList σ ss
    termination_by structural ss => ss
end

def sortOfApp (decls : List SymbolDecl) (h : Kore.SymbolIdent) (ss : List Kore.KSort) :
    Option Kore.KSort :=
  (decls.find? (·.name == h.ident.name)).map fun d =>
    substSort ((d.params.map (·.ident.ident.name)).zip ss) d.result

/-- The sort of a KORE pattern, read off its outermost construct ([kore-implicits.md] signatures). -/
def sortOf (decls : List SymbolDecl) : Kore.Pattern → Option Kore.KSort
  | .var (.evar x) => some x.sort
  | .var (.svar X) => some X.sort
  | .app h ss _ | .leftAssoc h ss _ | .rightAssoc h ss _ => sortOfApp decls h ss
  | .string _ => none
  | .top s | .bottom s | .not s _ | .and s _ | .or s _ | .implies s _ _ | .iff s _ _
  | .exist s _ _ | .forall s _ _ | .next s _ | .rewrites s _ _ | .dv s _ => some s
  | .mu X _ | .nu X _ => some X.sort
  | .ceil _ s _ | .floor _ s _ | .equals _ s _ _ | .in _ s _ _ => some s

/-! ## Γ_D -/

/-- One axiom of Γ_D, with the names of its variables (index i ↦ `names[i-1]`) for printing. -/
structure Item where
  label : String
  /-- The TRANSLATION.md rule that produced it. -/
  rule : String
  names : List String
  pat : P
  deriving Repr

/-- The display name of a variable key. -/
def VarKey.name : VarKey → String
  | .sortVar n => n
  | .evar n _ => n
  | .svar n _ => "@" ++ n

/-- The guard of a free variable ([Thesis] (7.11)): `xˢ ∈ ⊤_s`, `Xˢ ⊆ ⊤_s`;
of a sort variable (S-param): `α ∈ ⟦Sort⟧`. -/
def guardOf (t : VarTable) : VarKey → P
  | k@(.sortVar _) => sortGuard (t.ev k)
  | k@(.evar _ s) => t.ev k ∈∈ inhOf (trSort t s)
  | k@(.svar _ s) => .svar (t.sv k) ⊆⊆ inhOf (trSort t s)

/-- T-axiom: [Thesis] (7.10), `AML(φ_s) = wellsorted(φ_s) → (AML2(φ_s) = ⊤_s)`, where the
guard conjunction lists the axiom's sort variables (S-param) and then its free variables (7.11). -/
def trAxiom (decls : List SymbolDecl) (aliases : List String) (ad : AxiomDecl) : Item :=
  let a := ad.ax
  let t : VarTable := tableOf a.sortVars a.pattern
  let free := (a.sortVars.map sortVarKey ++ freeOf [] a.pattern).eraseDups
  let ws := free.map (guardOf t)
  let top := match sortOf decls a.pattern with
    | some s => inhOf (trSort t s)
    | none => sym (.untranslated "sort of the axiom")
  let attrs := attrNames a.attributes |>.filter (fun n =>
    !(n.startsWith "org'Stop'kframework" || n == "UNIQUE'Unds'ID"))
  { label := s!"axiom {ad.index} ({ad.module}){if attrs.isEmpty then "" else s!" {attrs}"}"
    rule := "T-axiom"
    names := t.map VarKey.name
    pat := conjList ws ⇒ (tr ⟨t, aliases⟩ a.pattern ≡ top) }

/-- The guards and table of a declaration's sort parameters. -/
def paramTable (params : List Kore.SortVar) : VarTable := params.map sortVarKey

/-- G-sort: `∃y:Sort. C ᾱ = y` ([FoSSaCS] §4.1 item 2; [Thesis] (7.28) for sort functions).
The binder `y` takes the index after the parameters', whatever their names (a parameter named
`y` must not be captured: review 2, finding 3). -/
def sortConstantItem (sd : SortDecl) : Item :=
  let t : VarTable := paramTable sd.params
  let C := appList (sym (.sort sd.name)) (sd.params.map fun α => .evar (t.ev (sortVarKey α)))
  let y : EVar := ⟨sd.params.length + 1⟩
  let yName := if (t.map VarKey.name).contains "y" then "y'" else "y"
  { label := s!"sort {sd.name}{if sd.hooked then " (hooked)" else ""}", rule := "G-sort"
    names := t.map VarKey.name ++ [yName]
    pat := guarded (sd.params.map fun α => sortGuard (t.ev (sortVarKey α)))
      (sExists y (sym .sortSort) (C ≡ .evar y)) }

/-- G-nonempty: [Thesis] (7.8), `⊤_s ≠ ∅`. -/
def nonemptyItem (sd : SortDecl) : Item :=
  let t : VarTable := paramTable sd.params
  let C := appList (sym (.sort sd.name)) (sd.params.map fun α => .evar (t.ev (sortVarKey α)))
  { label := s!"nonempty {sd.name}", rule := "G-nonempty", names := t.map VarKey.name
    pat := guarded (sd.params.map fun α => sortGuard (t.ev (sortVarKey α))) (notEqual (inhOf C) ⊥) }

/-- G-sorts (CHOICE): `⟦Sort⟧ = µS. C₁ ∨ … ∨ Cₙ S…S` ([AML-TR] §7, (Sorts)). -/
def sortsItem (sds : List SortDecl) : Item :=
  let S : SVar := ⟨1⟩
  let gens := sds.map fun sd => appList (sym (.sort sd.name)) (sd.params.map fun _ => .svar S)
  { label := "the sorts", rule := "G-sorts", names := ["S"]
    pat := sortsDomain ≡ .mu S (disjList gens) }

/-- G-arity: [Thesis] (7.9), `σ ⊤_{s₁} … ⊤_{sₙ} ⊆ ⊤_s`, over the sort parameters (S-param, S-args). -/
def arityItem (sd : SymbolDecl) : Item :=
  let t : VarTable := paramTable sd.params
  let head := appList (sym (.symbol sd.name)) (sd.params.map fun α => .evar (t.ev (sortVarKey α)))
  let lhs := appList head (sd.args.map fun s => inhOf (trSort t s))
  { label := s!"arity {sd.name}{if sd.hooked then " (hooked)" else ""}", rule := "G-arity"
    names := t.map VarKey.name
    pat := guarded (sd.params.map fun α => sortGuard (t.ev (sortVarKey α)))
      (lhs ⊆⊆ inhOf (trSort t sd.result)) }

/-- G-def: [Thesis] (7.7), aml-port's `definedness` (`∀x. ⌈x⌉`). -/
def definednessItem : Item :=
  { label := "definedness", rule := "G-def", names := ["x"], pat := @definedness Sym _ ⟨1⟩ }

/-- G-ceil-arity: (7.9) for the symbols `⌈_⌉^{s'}_s` of [Thesis] (2.98). -/
def ceilArityItem : Item :=
  let s : EVar := ⟨1⟩; let s' : EVar := ⟨2⟩
  { label := "arity ⌈_⌉{s,s'}", rule := "G-ceil-arity", names := ["s", "s'"]
    pat := guarded [sortGuard s, sortGuard s']
      (sCeil (.evar s) (.evar s') (inhOf (.evar s)) ⊆⊆ inhOf (.evar s')) }

/-- G-ceil-def: (2.99) `⌈x:s⌉^{s'}_s` translated by (7.10). -/
def ceilDefItem : Item :=
  let s : EVar := ⟨1⟩; let s' : EVar := ⟨2⟩; let x : EVar := ⟨3⟩
  { label := "definedness ⌈_⌉{s,s'}", rule := "G-ceil-def", names := ["s", "s'", "x"]
    pat := guarded [sortGuard s, sortGuard s', x ∈∈ inhOf (.evar s)]
      (sCeil (.evar s) (.evar s') (.evar x) ≡ inhOf (.evar s')) }

mutual
  /-- The sorts of the `\rewrites` and `\next` nodes of a pattern. -/
  def nextSortsOf : Kore.Pattern → List Kore.KSort
    | .rewrites s p q => s :: (nextSortsOf p ++ nextSortsOf q)
    | .next s p => s :: nextSortsOf p
    | .app _ _ ps | .leftAssoc _ _ ps | .rightAssoc _ _ ps | .and _ ps | .or _ ps => nextSortsOfList ps
    | .not _ p | .exist _ _ p | .forall _ _ p | .mu _ p | .nu _ p | .ceil _ _ p | .floor _ _ p =>
      nextSortsOf p
    | .implies _ p q | .iff _ p q | .equals _ _ p q | .in _ _ p q => nextSortsOf p ++ nextSortsOf q
    | .var _ | .string _ | .top _ | .bottom _ | .dv _ _ => []
    termination_by structural p => p
  def nextSortsOfList : List Kore.Pattern → List Kore.KSort
    | [] => []
    | p :: ps => nextSortsOf p ++ nextSortsOfList ps
    termination_by structural ps => ps
end

mutual
  /-- The literals of the `\dv` nodes of a pattern. -/
  def dvLitsOf : Kore.Pattern → List String
    | .dv _ lit => [lit]
    | .app _ _ ps | .leftAssoc _ _ ps | .rightAssoc _ _ ps | .and _ ps | .or _ ps => dvLitsOfList ps
    | .not _ p | .exist _ _ p | .forall _ _ p | .mu _ p | .nu _ p | .ceil _ _ p | .floor _ _ p
    | .next _ p => dvLitsOf p
    | .implies _ p q | .iff _ p q | .equals _ _ p q | .in _ _ p q | .rewrites _ p q =>
      dvLitsOf p ++ dvLitsOf q
    | .var _ | .string _ | .top _ | .bottom _ => []
    termination_by structural p => p
  def dvLitsOfList : List Kore.Pattern → List String
    | [] => []
    | p :: ps => dvLitsOf p ++ dvLitsOfList ps
    termination_by structural ps => ps
end

/-- G-next-arity: `• ⊤_S ⊆ ⊤_S` for each sort `S` of a `\rewrites` or `\next` ([AML-TR] §8). -/
def nextArityItem (sortVars : List Kore.SortVar) (s : Kore.KSort) : Item :=
  let t : VarTable := paramTable sortVars ++ sortVarsOf s |>.eraseDups
  let S := trSort t s
  { label := s!"arity • at {Kore.Printer.sort s}", rule := "G-next-arity", names := t.map VarKey.name
    pat := guarded ((sortVarsOf s).eraseDups.map fun k => sortGuard (t.ev k))
      (sNext (inhOf S) ⊆⊆ inhOf S) }

/-- G-dv-arity (CHOICE): `dv_lit s ⊆ ⊤_s` for every sort `s`. -/
def dvArityItem (lit : String) : Item :=
  let s : EVar := ⟨1⟩
  { label := s!"arity \\dv(\"{lit}\")", rule := "G-dv-arity", names := ["s"]
    pat := guarded [sortGuard s] (sym (.dv lit) ⬝ .evar s ⊆⊆ inhOf (.evar s)) }

/-- Γ_D = Γ^AML ∪ AML(Γ) ([Thesis] Prop. 7.2), kept as two lists. -/
structure Theory where
  /-- Γ^AML, the axioms of the encoding ((7.7)–(7.9) and the G-rules of TRANSLATION.md). -/
  signature : List Item
  /-- AML(Γ): one item per KORE axiom, in text order. -/
  axioms : List Item
  deriving Repr

def Theory.all (T : Theory) : List Item := T.signature ++ T.axioms

/-- D-*: the theory of a KORE definition (all modules; attributes ignored, D-attributes). -/
def Theory.ofDefinition (d : Kore.Definition) : Theory :=
  let sorts := d.sortDecls
  let syms := d.symbolDecls
  let aliases := d.aliasNames
  let axs := d.axiomDecls
  let nextSorts := (axs.flatMap fun ad => (nextSortsOf ad.ax.pattern).map (ad.ax.sortVars, ·))
    |>.foldl (fun acc x => if acc.any (fun y => decide (y.2 = x.2)) then acc else acc ++ [x]) []
  let lits := (axs.flatMap fun ad => dvLitsOf ad.ax.pattern).eraseDups
  { signature :=
      [definednessItem]
      ++ sorts.map sortConstantItem
      ++ sorts.map nonemptyItem
      ++ [sortsItem sorts]
      ++ syms.map arityItem
      ++ [ceilArityItem, ceilDefItem]
      ++ nextSorts.map (fun (vs, s) => nextArityItem vs s)
      ++ lits.map dvArityItem
    axioms := axs.map (trAxiom syms aliases) }

/-- The premises of Γ_D, as aml-port's `Premises`.
aml-port's `HasDefinedness` asks for `definedness` at every variable, so all of them are in. -/
def Theory.premises (T : Theory) : Premises Sym :=
  fun φ => (∃ it ∈ T.all, it.pat = φ) ∨ ∃ x : EVar, φ = @definedness Sym _ x

instance (T : Theory) : HasDefinedness T.premises where
  hasDefinedness {x} := Or.inr ⟨x, rfl⟩

end KoreAML
