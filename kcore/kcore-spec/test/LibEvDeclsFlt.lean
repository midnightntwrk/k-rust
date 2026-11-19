/-
  Declarations of the text of silentflt (`f2-examples/silentflt.kompile.kore`: FLOAT, STRING, BYTES
  and SET imported), in the direction E, for every interpretation H, and the two library symbols
  it declares that name no symbol of Γ. Nothing here reads `Parse.parse` or `emit`. Run from the
  package root: `lake env lean -j1 test/LibEvDeclsFlt.lean`.

  - `sorts_in_sig`, `decls_entailed`: of the 22 sort declarations, each without sort parameters
    (all but `SortMInt{Width}`, `sort_params`) has its item among `sigItems c`, pattern for
    pattern, so Γ entails it for every H (Bytes, Endianness and Signedness among them).
  - `lib_syms`, `lib_decls_entailed`: the library's symbol declarations named in `libDeclNames`
    (BYTES-HOOKED's four constructors of Endianness and Signedness; FLOAT's `isInfinite`,
    `sqrtFloat` and `=/=Float`) each name a symbol of Γ, and their items are the arity items
    `sigItems c` holds for it, so Γ entails the item of each one without sort parameters.
  - `dividesInt_absent`, `int2BytesNoLen_absent_decl`: INT-COMMON's `dividesInt` (registry symbol
    219) and BYTES-HOOKED's `Int2BytesNoLen` (306) are declared without sort parameters and name no
    symbol of Γ. Each is one of its module's parameter symbols (a function of the library no hook
    of the registry interprets: `library`'s `params`, not in `hookSigs`); the reading has no
    parameter symbol (`c.params = []`: no rule or function of the reading applies either), so Γ
    has neither. The library's equation of `dividesInt` (sentence 274, domains.md 1454) applies
    it, the one head of the sentence Γ lacks.
  - `rootFloat_absent`: FLOAT's equation of `sqrtFloat` (sentence 380, domains.md 1671) applies
    `rootFloat`, a symbol the text declares without sort parameters and Γ lacks, the one head of the
    sentence Γ lacks.
  - `andInt_absent`: INT's `&Int`, declared without sort parameters, is the one head Γ lacks of its
    `functional` sentence 54 and of INT-KORE's associativity lemma 236 (domains.md 1428).
  - `floatParams_absent`: FLOAT's `total` symbols `Float2Int`, `atanFloat`, `cosFloat`,
    `expFloat`, `exponentFloat`, `signFloat` and `sinFloat` are declared without sort parameters
    and name no symbol of Γ; each is the one head Γ lacks of its `functional` sentence (42, 105,
    112, 116, 118, 165, 168).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvDeclsFlt

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/silentflt.kompile.kore"
definition_of defn from "f2-examples/silentflt.kompile.kore"
user_axioms U from "f2-examples/silentflt.kompile.kore" module "SILENTFLT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

/-- The first of Γ's symbols under the name `n`. -/
noncomputable def symFind (n : String) : Option CtorSig := (kernelSyms c).find? fun k => c.symName k.name == n

/-- Γ has a symbol under the name `n`. -/
noncomputable def hasSym (n : String) : Bool := (symFind n).isSome

/-- The item is one of `sigItems c`, pattern for pattern. -/
noncomputable def inSigItems (it : Item) : Bool := (sigItems c).any (·.pat == it.pat)

/-- A sort declaration has sort parameters or its item is one of Γ's. -/
noncomputable def sortOK (sd : SortDecl) : Bool := !sd.params.isEmpty || inSigItems (sortConstantItem sd)

theorem decl_lengths : kore.sortDecls.length = 22 ∧ kore.symbolDecls.length = 245 := by decide +kernel

theorem sort_params : (kore.sortDecls.filter fun sd => !sd.params.isEmpty).map (·.name) = ["SortMInt"] := by
  decide +kernel

theorem sorts_in_sig : kore.sortDecls.all sortOK = true := by decide +kernel

/-- **E for the sort declarations**: Γ entails the G-sort item of each sort declaration without
sort parameters, for every H; each is one of `sigItems c`'s items. -/
theorem decls_entailed (H : HookParams) :
    ∀ sd ∈ kore.sortDecls, sd.params = [] → Γ (cH H) ⊧ (sortConstantItem sd).pat := by
  intro sd hsd hp
  have h := List.all_eq_true.mp sorts_in_sig sd hsd
  simp only [sortOK, hp, List.isEmpty_nil, Bool.not_true, Bool.false_or] at h
  intro M _ I hI
  obtain ⟨it', hit', he⟩ := List.any_eq_true.mp h
  rw [← of_decide_eq_true he]
  exact sat_sigItem hI (by rw [sigItems_withHooks]; exact hit')

/-- A symbol declaration names no symbol of Γ, or its item is the arity item of the first of Γ's
symbols under its name. -/
noncomputable def symOK (sd : SymbolDecl) : Bool :=
  match symFind sd.name with
  | some k => (symArityItem c k).pat == (arityItem sd).pat
  | none => true

/-- Library symbol declarations of the text, by name. -/
def libDeclNames : List String :=
  ["LblbigEndianBytes", "LbllittleEndianBytes", "LblsignedBytes", "LblunsignedBytes",
   "LblisInfinite'LParUndsRParUnds'FLOAT'Unds'Bool'Unds'Float",
   "LblsqrtFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float",
   "Lbl'UndsEqlsSlshEqls'Float'UndsUnds'FLOAT'Unds'Bool'Unds'Float'Unds'Float"]

/-- The text's symbol declarations named in `libDeclNames`. -/
noncomputable def libSyms : List SymbolDecl := kore.symbolDecls.filter (libDeclNames.contains ·.name)

/-- Each name is declared once. -/
theorem lib_syms : libDeclNames.all (fun n => (kore.symbolDecls.filter (·.name == n)).length == 1) = true := by
  decide +kernel

/-- Each is declared without sort parameters, names a symbol of Γ, and its item is the arity item
of the first of Γ's symbols under its name. -/
theorem lib_symOK : libSyms.all (fun sd => sd.params.isEmpty && hasSym sd.name && symOK sd) = true := by
  decide +kernel

/-- **E for the library's symbol declarations named in `libDeclNames`**: Γ entails the G-arity
item of each such declaration without sort parameters, for every H. -/
theorem lib_decls_entailed (H : HookParams) :
    ∀ sd ∈ kore.symbolDecls, sd.params = [] → sd.name ∈ libDeclNames → Γ (cH H) ⊧ (arityItem sd).pat := by
  intro sd hsd _ hn
  have h := List.all_eq_true.mp lib_symOK sd (List.mem_filter.mpr ⟨hsd, List.elem_eq_true_of_mem hn⟩)
  simp only [Bool.and_eq_true] at h
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h.1.2
  have h2 := h.2
  simp only [symOK, hk] at h2
  have hmem : symArityItem c k ∈ sigItems c := by
    unfold sigItems
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_of_find?_eq_some hk)))
  intro M _ I hI
  rw [← of_decide_eq_true h2]
  exact sat_sigItem hI (by rw [sigItems_withHooks]; exact hmem)

/-! ## Two library symbols the text declares and Γ lacks -/

/-- The names of the heads a sentence applies, each with its sort arguments (`appHeadsOf`), that are
not Γ's (`gammaHeads`). -/
noncomputable def absentOf (ad : AxiomDecl) : List String :=
  ((appHeadsOf ad.ax.pattern).filter fun h => !gammaHasHead c h).map (·.1)

def dividesIntName : String := "Lbl'Unds'dividesInt'UndsUnds'INT-COMMON'Unds'Bool'Unds'Int'Unds'Int"

/-- A library module's parameter symbols hold the registry symbol `f`, and no hook of the registry
interprets it. -/
def libParamOf (m : String) (f : Sym) : Bool :=
  (library.find? (·.name == m)).any (·.params.any (·.name == f)) && hookSigs.all (·.name != f)

/-- **`dividesInt` is declared and Γ lacks it**: the text declares it once, without sort parameters;
it is INT-COMMON's parameter symbol 219, which no hook interprets; the reading has no parameter
symbol, so Γ has no symbol under its name; its equation (274) applies it, the one head of the
sentence Γ lacks. -/
theorem dividesInt_absent :
    (kore.symbolDecls.filter (·.name == dividesIntName)).map (·.params.isEmpty) = [true] ∧
    c.symName 219 = dividesIntName ∧ libParamOf "INT-COMMON" 219 = true ∧
    c.params = [] ∧ hasSym dividesIntName = false ∧
    absentOf U.ax274 = [dividesIntName] := by
  decide +kernel

/-- **`Int2BytesNoLen` is declared and Γ lacks it**: the text declares it once, without sort
parameters; it is BYTES-HOOKED's parameter symbol 306, which no hook interprets, so Γ (no parameter
symbol) has no symbol under its name. -/
theorem int2BytesNoLen_absent_decl :
    (kore.symbolDecls.filter (·.name == "LblInt2BytesNoLen")).map (·.params.isEmpty) = [true] ∧
    c.symName 306 = "LblInt2BytesNoLen" ∧ libParamOf "BYTES-HOOKED" 306 = true ∧
    hasSym "LblInt2BytesNoLen" = false := by
  decide +kernel

def rootFloatName : String := "LblrootFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Int"

/-- **`sqrtFloat`'s equation applies `rootFloat`, which Γ lacks**: 380 (domains.md 1671,
`sqrtFloat(F) => rootFloat(F, 2)`) applies `rootFloat`, the one head of the sentence Γ lacks;
`sqrtFloat`, its left side's head, is Γ's. -/
theorem rootFloat_absent : absentOf U.ax380 = [rootFloatName] := by
  decide +kernel

def andIntName : String := "Lbl'UndsAnd-'Int'Unds'"

/-- **`&Int`'s sentences apply it, which Γ lacks**: its `functional` sentence 54 and INT-KORE's
lemma 236 (domains.md 1428, `I1 &Int (I2 &Int C) = (I1 &Int I2) &Int C`) apply `&Int` (once and
four times), a symbol the text declares without sort parameters, and no other head Γ lacks. -/
theorem andInt_absent :
    [U.ax54, U.ax236].map absentOf = [[andIntName], [andIntName, andIntName, andIntName, andIntName]] := by
  decide +kernel

/-- The names of seven of FLOAT's `total` symbols, in the order of their `functional` sentences in
the text. -/
def floatParamNamesFlt : List String :=
  ["LblFloat2Int'LParUndsRParUnds'FLOAT'Unds'Int'Unds'Float",
   "LblatanFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float",
   "LblcosFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float",
   "LblexpFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float",
   "LblexponentFloat'LParUndsRParUnds'FLOAT'Unds'Int'Unds'Float",
   "LblsignFloat'LParUndsRParUnds'FLOAT'Unds'Bool'Unds'Float",
   "LblsinFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float"]

/-- **The `functional` sentences of seven of FLOAT's `total` symbols apply a symbol Γ lacks**: 42 (`Float2Int`), 105 (`atanFloat`), 112 (`cosFloat`), 116 (`expFloat`), 118
(`exponentFloat`), 165 (`signFloat`) and 168 (`sinFloat`) each apply their own symbol, declared
without sort parameters, and no other head Γ lacks; Γ has no symbol under any of the seven names. -/
theorem floatParams_absent :
    [U.ax42, U.ax105, U.ax112, U.ax116, U.ax118, U.ax165, U.ax168].map absentOf =
      floatParamNamesFlt.map (fun n => [n]) ∧
    floatParamNamesFlt.all (fun n => (kore.symbolDecls.filter (·.name == n)).map (·.params.isEmpty) == [true]) ∧
    floatParamNamesFlt.all (fun n => !hasSym n) := by
  decide +kernel

end KCore.LibEvDeclsFlt

#check @KCore.LibEvDeclsFlt.decls_entailed
#check @KCore.LibEvDeclsFlt.lib_decls_entailed
#check @KCore.LibEvDeclsFlt.dividesInt_absent
#check @KCore.LibEvDeclsFlt.floatParams_absent
#print axioms KCore.LibEvDeclsFlt.decls_entailed
#print axioms KCore.LibEvDeclsFlt.lib_decls_entailed
#print axioms KCore.LibEvDeclsFlt.dividesInt_absent
#print axioms KCore.LibEvDeclsFlt.int2BytesNoLen_absent_decl
#check @KCore.LibEvDeclsFlt.rootFloat_absent
#print axioms KCore.LibEvDeclsFlt.rootFloat_absent
#print axioms KCore.LibEvDeclsFlt.andInt_absent
#print axioms KCore.LibEvDeclsFlt.floatParams_absent
