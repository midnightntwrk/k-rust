/-
  The declarations of kore.k's text as kompile wrote it (`examples/ref-kk/RefKk/definition.kore`,
  all modules), in the direction E (row 19), on the literals `kore` and `defn`. Nothing here reads
  `Parse.parse` or `emit`. Run from the package root: `lake env lean test/TieKkDecls.lean`.

  - `sorts_in_sig`: the item of each of the 33 sort declarations without sort parameters (all but
    `SortMInt{Width}`, `decl_params`) is an item of `sigItems c`, pattern for pattern.
  - `syms_in_sig`: of the 311 symbol declarations, each without sort parameters (all but 5,
    `decl_params`) names no symbol of Γ, or its item is the arity item `sigItems c` holds for the
    first of Γ's symbols under its name, pattern for pattern (`symOK`); the former are
    57 (`noSym_count`; no direction, as the sentences that apply them), so 249 have their item in
    Γ. Decided by ranges of 50 declarations, each its own kernel decision (`syms_a`), joined by
    `tieAll_range` and `declCount_range`.
  - `decls_entailed`: so Γ entails the item of each sort declaration without sort parameters and of
    each symbol declaration without sort parameters that names a symbol of Γ, for every H.
    G-nonempty and G-sorts are not items of Γ.
  - `lib_decls_entailed`: the library's symbol declarations named in `libDeclNames` (INT's
    `freshInt`, STRING-COMMON's `Bool2String` and `String2Bool`) each name a symbol of Γ
    (`libDeclNames_has`), so Γ entails the item of each one without sort parameters, for every H.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKk

open KCore ML Faithful KoreAML

kore_term kore from "examples/ref-kk/RefKk/definition.kore"
definition_of defn from "examples/ref-kk/RefKk/definition.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

/-- Counts over a list from the counts of its ranges, as `tieAll_range`. -/
theorem declCount_range {α : Type} {l : List α} {p : α → Bool} {a n k k' : Nat}
    (h : ((l.drop a).take n).countP p = k) (ht : (l.drop (a + n)).countP p = k') :
    (l.drop a).countP p = k + k' := by
  rw [← List.take_append_drop n (l.drop a), List.countP_append, h, List.drop_drop, ht]

/-- The first of Γ's symbols under the name `n` (`symFindCD`). -/
noncomputable def symFind (n : String) : Option CtorSig := symFindCD c n

/-- Γ has a symbol under the name `n`. -/
noncomputable def hasSym (n : String) : Bool := (symFind n).isSome

/-- The item is one of `sigItems c`, pattern for pattern. -/
noncomputable def inSigItems (it : Item) : Bool := (sigItems c).any (·.pat == it.pat)

/-- A sort declaration has sort parameters or its item is one of Γ's. -/
noncomputable def sortOK (sd : SortDecl) : Bool := !sd.params.isEmpty || inSigItems (sortConstantItem sd)

/-- A symbol declaration has sort parameters, or names no symbol of Γ, or its item is the arity
item of the first of Γ's symbols under its name. -/
noncomputable def symOK (sd : SymbolDecl) : Bool :=
  !sd.params.isEmpty || match symFind sd.name with
    | some k => (symArityItem c k).pat == (arityItem sd).pat
    | none => true

/-- A symbol declaration without sort parameters that names no symbol of Γ. -/
noncomputable def noSymP (sd : SymbolDecl) : Bool := sd.params.isEmpty && !hasSym sd.name

theorem decl_lengths : kore.sortDecls.length = 33 ∧ kore.symbolDecls.length = 311 := by decide +kernel

theorem decl_params : (kore.sortDecls.filter fun sd => !sd.params.isEmpty).map (·.name) = ["SortMInt"] ∧
    (kore.symbolDecls.filter fun sd => !sd.params.isEmpty).map (·.name) =
      ["inj", "LblList'Coln'getMInt", "LblList'Coln'setMInt", "Lblite", "LblsizeMInt"] := by decide +kernel

theorem sorts_in_sig : kore.sortDecls.all sortOK = true := by decide +kernel

theorem syms_0 : (((kore.symbolDecls.drop 0).take 50).all symOK, ((kore.symbolDecls.drop 0).take 50).countP noSymP) = (true, 9) := by
  decide +kernel
theorem syms_50 : (((kore.symbolDecls.drop 50).take 50).all symOK, ((kore.symbolDecls.drop 50).take 50).countP noSymP) = (true, 4) := by
  decide +kernel
theorem syms_100 : (((kore.symbolDecls.drop 100).take 50).all symOK, ((kore.symbolDecls.drop 100).take 50).countP noSymP) = (true, 6) := by
  decide +kernel
theorem syms_150 : (((kore.symbolDecls.drop 150).take 50).all symOK, ((kore.symbolDecls.drop 150).take 50).countP noSymP) = (true, 1) := by
  decide +kernel
theorem syms_200 : (((kore.symbolDecls.drop 200).take 50).all symOK, ((kore.symbolDecls.drop 200).take 50).countP noSymP) = (true, 19) := by
  decide +kernel
theorem syms_250 : (((kore.symbolDecls.drop 250).take 50).all symOK, ((kore.symbolDecls.drop 250).take 50).countP noSymP) = (true, 15) := by
  decide +kernel
theorem syms_300 : ((kore.symbolDecls.drop 300).all symOK, (kore.symbolDecls.drop 300).countP noSymP) = (true, 3) := by
  decide +kernel

theorem syms_in_sig : kore.symbolDecls.all symOK = true :=
  tieAll_whole (p := symOK) <|
    tieAll_range (a := 0) (n := 50) (Prod.mk.inj syms_0).1 <|
    tieAll_range (a := 50) (n := 50) (Prod.mk.inj syms_50).1 <|
    tieAll_range (a := 100) (n := 50) (Prod.mk.inj syms_100).1 <|
    tieAll_range (a := 150) (n := 50) (Prod.mk.inj syms_150).1 <|
    tieAll_range (a := 200) (n := 50) (Prod.mk.inj syms_200).1 <|
    tieAll_range (a := 250) (n := 50) (Prod.mk.inj syms_250).1 <|
    (Prod.mk.inj syms_300).1

/-- **The account of the symbol declarations**: 57 have no sort parameter and name no symbol of Γ;
with the 5 with sort parameters (`decl_params`), the other 249 have their item in Γ
(`syms_in_sig`). -/
theorem noSym_count : kore.symbolDecls.countP noSymP = 57 := by
  have h : (kore.symbolDecls.drop 0).countP noSymP = _ :=
    declCount_range (a := 0) (n := 50) (Prod.mk.inj syms_0).2 <|
    declCount_range (a := 50) (n := 50) (Prod.mk.inj syms_50).2 <|
    declCount_range (a := 100) (n := 50) (Prod.mk.inj syms_100).2 <|
    declCount_range (a := 150) (n := 50) (Prod.mk.inj syms_150).2 <|
    declCount_range (a := 200) (n := 50) (Prod.mk.inj syms_200).2 <|
    declCount_range (a := 250) (n := 50) (Prod.mk.inj syms_250).2 <|
    (Prod.mk.inj syms_300).2
  rw [List.drop_zero] at h
  rw [h]

/-- **E for the declarations**: Γ entails the G-sort item of each sort declaration without sort
parameters and the G-arity item of each symbol declaration without sort parameters that names a
symbol of Γ, for every H; each is one of `sigItems c`'s items. -/
theorem decls_entailed (H : HookParams) :
    (∀ sd ∈ kore.sortDecls, sd.params = [] → Γ (cH H) ⊧ (sortConstantItem sd).pat) ∧
    (∀ sd ∈ kore.symbolDecls, sd.params = [] → hasSym sd.name = true → Γ (cH H) ⊧ (arityItem sd).pat) := by
  have hin : ∀ it, inSigItems it = true → Γ (cH H) ⊧ it.pat := by
    intro it h M _ I hI
    obtain ⟨it', hit', he⟩ := List.any_eq_true.mp h
    rw [← of_decide_eq_true he]
    exact sat_sigItem hI (by rw [sigItems_withHooks]; exact hit')
  constructor
  · intro sd hsd hp
    have h := List.all_eq_true.mp sorts_in_sig sd hsd
    simp only [sortOK, hp, List.isEmpty_nil, Bool.not_true, Bool.false_or] at h
    intro M _ I hI
    exact hin _ h hI
  · intro sd hsd hp hs
    have h := List.all_eq_true.mp syms_in_sig sd hsd
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
    simp only [symOK, hp, hk, List.isEmpty_nil, Bool.not_true, Bool.false_or] at h
    have hmem : symArityItem c k ∈ sigItems c := symArityItem_mem_of_findCD hk
    intro M _ I hI
    rw [← of_decide_eq_true h]
    exact sat_sigItem hI (by rw [sigItems_withHooks]; exact hmem)

/-- Library symbol declarations of the text, by name. -/
def libDeclNames : List String :=
  ["LblfreshInt'LParUndsRParUnds'INT'Unds'Int'Unds'Int",
   "LblBool2String'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Bool",
   "LblString2Bool'LParUndsRParUnds'STRING-COMMON'Unds'Bool'Unds'String"]

/-- Each names a symbol of Γ. -/
theorem libDeclNames_has : libDeclNames.all hasSym = true := by decide +kernel

/-- **E for the library's symbol declarations named in `libDeclNames`**: Γ entails the G-arity
item of each such declaration without sort parameters, for every H. -/
theorem lib_decls_entailed (H : HookParams) :
    ∀ sd ∈ kore.symbolDecls, sd.params = [] → sd.name ∈ libDeclNames → Γ (cH H) ⊧ (arityItem sd).pat :=
  fun sd hsd hp hn => (decls_entailed H).2 sd hsd hp (List.all_eq_true.mp libDeclNames_has _ hn)

end KCore.TieKk

#check @KCore.TieKk.decls_entailed
#print axioms KCore.TieKk.decls_entailed
#print axioms KCore.TieKk.lib_decls_entailed
