/-
  Declarations of the text of the fixture e6-string-buffer (`f2-examples/e6sb.kompile.kore`:
  STRING-BUFFER imported, one rule `go => res(StringBuffer2String(.StringBuffer +String "a"))`), in
  the direction E, for every interpretation H. Nothing here reads `Parse.parse` or `emit`. Run from
  the package root: `lake env lean -j1 test/LibEvDeclsStrBuf.lean`.

  - `sorts_in_sig`, `decls_entailed`: each sort declaration without sort parameters (all but
    `SortMInt{Width}`, `sort_params`) has its item among `sigItems c`, pattern for pattern, so Γ
    entails it for every H (StringBuffer among them).
  - `params_sb`: the reading's parameter symbols are STRING-BUFFER-IN-K's three functions
    (`.StringBuffer`, `_+String_` on StringBuffer, `StringBuffer2String`): each is one of its module's
    parameter symbols (no hook of the registry interprets it) and the rule applies each.
  - `lib_syms`, `lib_symOK`, `lib_decls_entailed`: the three declarations named in `libDeclNames`
    are each declared once, without sort parameters, and name a symbol of Γ whose arity item is
    the declaration's, so Γ entails the item of each one, for every H.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvDeclsStrBuf

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6sb.kompile.kore"
definition_of defn from "f2-examples/e6sb.kompile.kore"

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
  ["Lbl'Stop'StringBuffer'Unds'STRING-BUFFER-IN-K'Unds'StringBuffer",
   "Lbl'UndsPlus'String'UndsUnds'STRING-BUFFER-IN-K'Unds'StringBuffer'Unds'StringBuffer'Unds'String",
   "LblStringBuffer2String'LParUndsRParUnds'STRING-BUFFER-IN-K'Unds'String'Unds'StringBuffer"]

/-- A library module's parameter symbols hold the registry symbol `f`, and no hook of the registry
interprets it. -/
def libParamOf (m : String) (f : Sym) : Bool :=
  (library.find? (·.name == m)).any (·.params.any (·.name == f)) && hookSigs.all (·.name != f)

/-- **The reading's parameter symbols** are the three, in the registry's numbering 294 to 296 under
the names of `libDeclNames`, each a parameter symbol of STRING-BUFFER-IN-K. -/
theorem params_sb : c.params.map (·.sig.name) = [294, 295, 296] ∧
    [294, 295, 296].map c.symName = libDeclNames ∧
    [294, 295, 296].all (libParamOf "STRING-BUFFER-IN-K") = true := by
  decide +kernel

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

end KCore.LibEvDeclsStrBuf

#check @KCore.LibEvDeclsStrBuf.decls_entailed
#check @KCore.LibEvDeclsStrBuf.lib_decls_entailed
#print axioms KCore.LibEvDeclsStrBuf.decls_entailed
#print axioms KCore.LibEvDeclsStrBuf.params_sb
#print axioms KCore.LibEvDeclsStrBuf.lib_decls_entailed
