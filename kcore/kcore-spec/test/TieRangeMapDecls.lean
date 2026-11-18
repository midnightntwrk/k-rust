/-
  RANGEMAP's declarations and the `functional` sentences of its interpreted symbols on the text of
  the fixture e6-rangemap (`f2-examples/e6rm.kompile.kore`), for every interpretation H. Nothing
  here reads `Parse.parse` or `emit`. Run from the package root:
  `lake env lean -j1 test/TieRangeMapDecls.lean`. The function equations, the constructor
  sentences, the rule and the expectations: test/TieRangeMap.lean.

  - `rm_sorts`: the declarations of the sorts `RangeMap` and `Range` have no sort parameter and
    their items are items of `sigItems c` (G-sort, direction E, `decls_entailed`).
  - `rm_syms`: of RANGEMAP's 19 symbol declarations (the constructor `RangeMap:Range` and the 18
    hooked symbols), none has a sort parameter; 16 name a symbol of Γ and their items are the arity
    items `sigItems c` holds for it (G-arity, E); `choice`, `keys_list` and `values` name none: the
    text applies none of the three and the reading has no parameter (`params_nil`), so their
    declarations have no direction, as the sentences that would apply them.
  - `lib_decls_entailed`: the library's symbol declarations named in `libDeclNames` (RANGEMAP's
    `RangeMap:Range`, DEFAULT-CONFIGURATION's `<k>`, INT's `freshInt`) each name a symbol of Γ, and
    their items are the arity items `sigItems c` holds for it (`lib_syms`), so Γ entails the item of
    each one without sort parameters, for every H.
  - `fun_entailed` (direction Ev): the `functional` sentences of the eight interpreted RANGEMAP
    symbols that are not partial (`.RangeMap` 22, `lookupOrDefault` 37, `-RangeMap` 46,
    `<=RangeMap` 49, `in_keys` 80, `keys` 124, `size` 138, `updateRangeMap` 140) hold in every model
    of Γ at every valuation sending their variables to values (`LibEv.functional_ev`). They are all
    the user module's sentences of that form over a RANGEMAP symbol but the constructor's (35, a
    constructor sentence, test/TieRangeMapCons.lean) (`fun_all`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRangeMapDecls

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6rm.kompile.kore"
definition_of defn from "f2-examples/e6rm.kompile.kore"
user_axioms U from "f2-examples/e6rm.kompile.kore" module "E6-RANGEMAP"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

/-- The reading has no parameter symbol. -/
theorem params_nil : c.params = [] := by decide +kernel

/-! ## The declarations (row 19, direction E) -/

/-- The first of Γ's symbols under the name `n`. -/
noncomputable def symFind (n : String) : Option CtorSig := (kernelSyms c).find? fun k => c.symName k.name == n

/-- Γ has a symbol under the name `n`. -/
noncomputable def hasSym (n : String) : Bool := (symFind n).isSome

/-- The item is one of `sigItems c`, pattern for pattern. -/
noncomputable def inSigItems (it : Item) : Bool := (sigItems c).any (·.pat == it.pat)

/-- RANGEMAP's sorts. -/
def rmSortNames : List String := ["SortRangeMap", "SortRange"]

/-- RANGEMAP's symbols: the constructor `RangeMap:Range` and the hooked symbols. -/
def rmSymNames : List String :=
  ["LblRangeMap'Coln'Range", "Lbl'Stop'RangeMap", "Lbl'Unds'r'Pipe'-'-GT-Unds'", "Lbl'Unds'RangeMap'Unds'",
   "LblRangeMap'Coln'lookup", "LblRangeMap'Coln'lookupOrDefault", "LblRangeMap'Coln'find'Unds'range",
   "LblRangeMap'Coln'update", "Lbl'Unds'r'LSqBUnds-LT-'-undef'RSqB'",
   "Lbl'Unds'-RangeMap'UndsUnds'RANGEMAP'Unds'RangeMap'Unds'RangeMap'Unds'RangeMap",
   "LblupdateRangeMap'LParUndsCommUndsRParUnds'RANGEMAP'Unds'RangeMap'Unds'RangeMap'Unds'RangeMap",
   "LblremoveAll'LParUndsCommUndsRParUnds'RANGEMAP'Unds'RangeMap'Unds'RangeMap'Unds'Set",
   "Lblkeys'LParUndsRParUnds'RANGEMAP'Unds'Set'Unds'RangeMap",
   "Lbl'Unds'in'Unds'keys'LParUndsRParUnds'RANGEMAP'Unds'Bool'Unds'KItem'Unds'RangeMap",
   "LblsizeRangeMap", "Lbl'Unds-LT-Eqls'RangeMap'UndsUnds'RANGEMAP'Unds'Bool'Unds'RangeMap'Unds'RangeMap",
   "LblRangeMap'Coln'choice", "Lblkeys'Unds'list'LParUndsRParUnds'RANGEMAP'Unds'List'Unds'RangeMap",
   "Lblvalues'LParUndsRParUnds'RANGEMAP'Unds'List'Unds'RangeMap"]

noncomputable def rmSorts : List SortDecl := kore.sortDecls.filter (rmSortNames.contains ·.name)
noncomputable def rmSyms : List SymbolDecl := kore.symbolDecls.filter (rmSymNames.contains ·.name)

/-- **The two sort declarations**, each once, without sort parameters, their items in Γ. -/
theorem rm_sorts : rmSorts.map (·.name) = rmSortNames ∧
    rmSorts.all (fun sd => sd.params.isEmpty && inSigItems (sortConstantItem sd)) = true := by
  decide +kernel

/-- A symbol declaration names no symbol of Γ, or its item is the arity item of the first of Γ's
symbols under its name. -/
noncomputable def symOK (sd : SymbolDecl) : Bool :=
  match symFind sd.name with
  | some k => (symArityItem c k).pat == (arityItem sd).pat
  | none => true

/-- **The 19 symbol declarations**, each once, without sort parameters: 16 name a symbol of Γ and
their arity items are Γ's for it; `choice`, `keys_list` and `values` name none. -/
theorem rm_syms : rmSyms.length = 19 ∧ (rmSyms.map (·.name)).Nodup ∧ rmSyms.all (·.params.isEmpty) = true ∧
    (rmSyms.filter (!hasSym ·.name)).map (·.name) =
      ["LblRangeMap'Coln'choice", "Lblkeys'Unds'list'LParUndsRParUnds'RANGEMAP'Unds'List'Unds'RangeMap",
       "Lblvalues'LParUndsRParUnds'RANGEMAP'Unds'List'Unds'RangeMap"] := by
  decide +kernel

theorem rm_symOK : rmSyms.all symOK = true := by decide +kernel

/-- **E for the declarations**: Γ entails the G-sort item of each RANGEMAP sort declaration and the
G-arity item of each RANGEMAP symbol declaration that names a symbol of Γ, for every H. -/
theorem decls_entailed (H : HookParams) :
    (∀ sd ∈ rmSorts, Γ (cH H) ⊧ (sortConstantItem sd).pat) ∧
    (∀ sd ∈ rmSyms, hasSym sd.name = true → Γ (cH H) ⊧ (arityItem sd).pat) := by
  have hin : ∀ it, inSigItems it = true → Γ (cH H) ⊧ it.pat := by
    intro it h M _ I hI
    obtain ⟨it', hit', he⟩ := List.any_eq_true.mp h
    rw [← of_decide_eq_true he]
    exact sat_sigItem hI (by rw [sigItems_withHooks]; exact hit')
  constructor
  · intro sd hsd
    have h := List.all_eq_true.mp rm_sorts.2 sd hsd
    simp only [Bool.and_eq_true] at h
    intro M _ I hI
    exact hin _ h.2 hI
  · intro sd hsd hs
    have h := List.all_eq_true.mp rm_symOK sd hsd
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
    simp only [symOK, hk] at h
    have hmem : symArityItem c k ∈ sigItems c := by
      unfold sigItems
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_of_find?_eq_some hk)))
    intro M _ I hI
    rw [← of_decide_eq_true h]
    exact sat_sigItem hI (by rw [sigItems_withHooks]; exact hmem)

/-- Library symbol declarations of the text, by name. -/
def libDeclNames : List String :=
  ["LblRangeMap'Coln'Range", "Lbl'-LT-'k'-GT-'", "LblfreshInt'LParUndsRParUnds'INT'Unds'Int'Unds'Int"]

/-- The text's symbol declarations named in `libDeclNames`. -/
noncomputable def libSyms : List SymbolDecl := kore.symbolDecls.filter (libDeclNames.contains ·.name)

/-- Each names a symbol of Γ, and its item is the arity item of the first of Γ's symbols under its
name. -/
theorem lib_syms : libSyms.all (fun sd => hasSym sd.name && symOK sd) = true := by decide +kernel

/-- **E for the library's symbol declarations named in `libDeclNames`**: Γ entails the G-arity
item of each such declaration without sort parameters, for every H. -/
theorem lib_decls_entailed (H : HookParams) :
    ∀ sd ∈ kore.symbolDecls, sd.params = [] → sd.name ∈ libDeclNames → Γ (cH H) ⊧ (arityItem sd).pat := by
  intro sd hsd _ hn
  have h := List.all_eq_true.mp lib_syms sd (List.mem_filter.mpr ⟨hsd, List.elem_eq_true_of_mem hn⟩)
  simp only [Bool.and_eq_true] at h
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h.1
  have h2 := h.2
  simp only [symOK, hk] at h2
  have hmem : symArityItem c k ∈ sigItems c := by
    unfold sigItems
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_of_find?_eq_some hk)))
  intro M _ I hI
  rw [← of_decide_eq_true h2]
  exact sat_sigItem hI (by rw [sigItems_withHooks]; exact hmem)

/-! ## The `functional` sentences of the interpreted symbols (row 9, direction Ev) -/

/-- The indices of the sentences. -/
def funIdx : List Nat := [22, 37, 46, 49, 80, 124, 138, 140]

/-- The sentences, in text order. -/
noncomputable def funText : List AxiomDecl := U.all.filter fun ad => funIdx.contains ad.index

/-- The name of the symbol a sentence of the form `\exists{R}(Val, \equals{s, R}(Val, f(…)))`
applies. -/
def headOf : Kore.Pattern → Option String
  | .exist _ _ (.equals _ _ _ (.app h _ _)) => some h.ident.name
  | _ => none

/-- The sentences' symbols, in text order. -/
theorem fun_heads : funText.map (headOf ·.ax.pattern) =
    [some "Lbl'Stop'RangeMap", some "LblRangeMap'Coln'lookupOrDefault",
     some "Lbl'Unds'-RangeMap'UndsUnds'RANGEMAP'Unds'RangeMap'Unds'RangeMap'Unds'RangeMap",
     some "Lbl'Unds-LT-Eqls'RangeMap'UndsUnds'RANGEMAP'Unds'Bool'Unds'RangeMap'Unds'RangeMap",
     some "Lbl'Unds'in'Unds'keys'LParUndsRParUnds'RANGEMAP'Unds'Bool'Unds'KItem'Unds'RangeMap",
     some "Lblkeys'LParUndsRParUnds'RANGEMAP'Unds'Set'Unds'RangeMap", some "LblsizeRangeMap",
     some "LblupdateRangeMap'LParUndsCommUndsRParUnds'RANGEMAP'Unds'RangeMap'Unds'RangeMap'Unds'RangeMap"] := by
  decide +kernel

/-- The signature of the interpreted symbol with the name of the sentence's symbol. -/
def sigOf (ad : AxiomDecl) : Option KCore.CtorSig :=
  (headOf ad.ax.pattern).bind fun n => hookSigs.find? fun k => regSymNames.getD k.name "" == n

/-- The sentence is the `functional` sentence of a symbol of `hookSigs` that is not partial, over
the one sort variable `R`. -/
def funOK (ad : AxiomDecl) : Bool :=
  match sigOf ad with
  | some k => decide (ad.ax.pattern = LibEv.funPatR k) && decide (ad.ax.sortVars = [Rv]) && LibEv.funReg k &&
      !partialHooks.contains k.name
  | none => false

theorem fun_checked : funText.all funOK = true := by decide +kernel

/-- The eight are the user module's sentences of the form `\exists{R}(Val, \equals{s, R}(Val, f(…)))`
over a RANGEMAP symbol, but for the constructor's `functional` sentence (35). -/
theorem fun_all : (U.all.filter fun ad => match headOf ad.ax.pattern with
    | some n => rmSymNames.contains n | none => false).map (·.index) = [22, 35, 37, 46, 49, 80, 124, 138, 140] := by
  decide +kernel

/-- None of the eight reads a declaration or an alias. -/
theorem fun_trS : funText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **Ev for the `functional` sentences of the interpreted RANGEMAP symbols**: each of the eight
holds in every model of Γ at every valuation sending its variables to values, for every H. -/
theorem fun_entailed (H : HookParams) : ∀ ad ∈ funText, EntailsAtValues (cH H) ad (trS ad).pat := by
  intro ad had
  rw [of_decide_eq_true (List.all_eq_true.mp fun_trS ad had)]
  have hok := List.all_eq_true.mp fun_checked ad had
  unfold funOK at hok
  cases hsig : sigOf ad with
  | none => rw [hsig] at hok; cases hok
  | some k =>
    rw [hsig] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hok
    obtain ⟨⟨⟨hp, hsv⟩, hreg⟩, hpar⟩ := hok
    obtain ⟨n, -, hfind⟩ := Option.bind_eq_some_iff.mp hsig
    exact LibEv.functional_ev (coreOKH H) (shapesOKH H) (List.mem_of_find?_eq_some hfind) (Or.inl hpar) hreg ad hp
      hsv

end KCore.TieRangeMapDecls

#check @KCore.TieRangeMapDecls.decls_entailed
#check @KCore.TieRangeMapDecls.fun_entailed
#print axioms KCore.TieRangeMapDecls.rm_sorts
#print axioms KCore.TieRangeMapDecls.rm_syms
#print axioms KCore.TieRangeMapDecls.rm_symOK
#print axioms KCore.TieRangeMapDecls.decls_entailed
#print axioms KCore.TieRangeMapDecls.fun_heads
#print axioms KCore.TieRangeMapDecls.fun_all
#print axioms KCore.TieRangeMapDecls.fun_entailed
#print axioms KCore.TieRangeMapDecls.lib_decls_entailed
