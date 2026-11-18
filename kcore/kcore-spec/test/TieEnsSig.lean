/-
  The tie (C14) on `f2-examples/ens.kompile.kore` for the declarations (row 19), on the literals
  `kore` and `defn`. Nothing here reads `Parse.parse` or `emit`.
  Run from the package root: `lake env lean test/TieEnsSig.lean`.

  - `sig_origin`: each of the 208 items of `sigItems c` is the item of a declaration of the text
    (`Theory.ofDefinition kore`'s signature), or is about a registry name the text does not declare
    at that shape (`surplusItem`).
  - `decls_entailed`: the item of each sort declaration without sort parameters, and of each symbol
    declaration without sort parameters of a symbol Γ has (`declItems`), is an item of `sigItems c`
    pattern for pattern (`decls_in_sig`), so Γ entails it for every H. G-nonempty and G-sorts are
    not items of Γ.

  One kernel decision of either list statement is too large; each is decided by ranges of the
  list, each its own decision, joined by `tieAllE_range`. The items of `sigItems c`: definedness
  (0), the sort constants of the 33 sorts (1 to 33; the registry sorts 8 to 16 and 21 to 29, at 9 to
  17 and 22 to 30, are surplus, `SortMInt` among them since the text declares it with a sort
  parameter), the arities of the 10 constructors and 16 functions (34 to 59), of the 132 interpreted
  hooked symbols (60 to 191; those the text does not declare are surplus), and `⌈_⌉`'s arity and
  definition and next's arity (192 to 194).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieEns

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/ens.kompile.kore"
definition_of defn from "f2-examples/ens.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-! ## Decisions over a list, by ranges -/

/-- `p` holds from `a` on where it holds on the `n` members from `a` and from `a + n` on. -/
theorem tieAllE_range {α : Type} {l : List α} {p : α → Bool} {a n : Nat}
    (h : ((l.drop a).take n).all p = true) (ht : (l.drop (a + n)).all p = true) :
    (l.drop a).all p = true := by
  rw [← List.take_append_drop n (l.drop a), List.all_append, h, List.drop_drop, ht]; rfl

/-- `p` holds of the whole list where it holds from `0` on. -/
theorem tieAllE_whole {α : Type} {l : List α} {p : α → Bool} (h : (l.drop 0).all p = true) :
    l.all p = true := h

/-! ## The converse: each item of `sigItems c` has its origin -/

/-- The item of Γ's signature is a declaration's item of the text, or a surplus one. -/
noncomputable def sigFrom (it : Item) : Bool :=
  (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it

theorem sigE_0 : (((sigItems c).drop 0).take 34).all sigFrom = true := by decide +kernel
theorem sigE_34 : (((sigItems c).drop 34).take 26).all sigFrom = true := by decide +kernel
theorem sigE_60 : (((sigItems c).drop 60).take 13).all sigFrom = true := by decide +kernel
theorem sigE_73 : (((sigItems c).drop 73).take 13).all sigFrom = true := by decide +kernel
theorem sigE_86 : (((sigItems c).drop 86).take 13).all sigFrom = true := by decide +kernel
theorem sigE_99 : (((sigItems c).drop 99).take 13).all sigFrom = true := by decide +kernel
theorem sigE_112 : (((sigItems c).drop 112).take 13).all sigFrom = true := by decide +kernel
theorem sigE_125 : (((sigItems c).drop 125).take 13).all sigFrom = true := by decide +kernel
theorem sigE_138 : (((sigItems c).drop 138).take 13).all sigFrom = true := by decide +kernel
theorem sigE_151 : (((sigItems c).drop 151).take 13).all sigFrom = true := by decide +kernel
theorem sigE_164 : (((sigItems c).drop 164).take 13).all sigFrom = true := by decide +kernel
theorem sigE_177 : (((sigItems c).drop 177).take 13).all sigFrom = true := by decide +kernel
theorem sigE_190 : ((sigItems c).drop 190).all sigFrom = true := by decide +kernel

theorem sig_sizes : (sigItems c).length = 208 := by decide +kernel

/-- **Every item of Γ's signature has its origin**: it is the item of a declaration of the text
(the G-sort item of a sort declaration, the G-arity item of a symbol declaration, definedness, the
arity and definition of `⌈_⌉`, the arity of next at the configuration sort), or it states the sort
constant of a registry sort or the arity of an interpreted hooked symbol that the text does not
declare at that shape. -/
theorem sig_origin : (sigItems c).all (fun it =>
    (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it) = true :=
  tieAllE_whole (p := sigFrom) <|
    tieAllE_range (a := 0) (n := 34) sigE_0 <|
    tieAllE_range (a := 34) (n := 26) sigE_34 <|
    tieAllE_range (a := 60) (n := 13) sigE_60 <|
    tieAllE_range (a := 73) (n := 13) sigE_73 <|
    tieAllE_range (a := 86) (n := 13) sigE_86 <|
    tieAllE_range (a := 99) (n := 13) sigE_99 <|
    tieAllE_range (a := 112) (n := 13) sigE_112 <|
    tieAllE_range (a := 125) (n := 13) sigE_125 <|
    tieAllE_range (a := 138) (n := 13) sigE_138 <|
    tieAllE_range (a := 151) (n := 13) sigE_151 <|
    tieAllE_range (a := 164) (n := 13) sigE_164 <|
    tieAllE_range (a := 177) (n := 13) sigE_177 <|
    sigE_190

/-! ## E for the declarations -/

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

/-- Γ has a symbol under the name `n`. -/
noncomputable def hasSym (n : String) : Bool := (kernelSyms c).any fun k => c.symName k.name == n

/-- The declarations of the text whose item `sigItems c` holds: the sort declarations without sort
parameters, and the symbol declarations without sort parameters of a symbol Γ has. -/
noncomputable def plainSorts : List SortDecl := kore.sortDecls.filter (·.params.isEmpty)
noncomputable def plainSyms : List SymbolDecl := kore.symbolDecls.filter fun sd => sd.params.isEmpty && hasSym sd.name
noncomputable def declItems : List Item := plainSorts.map sortConstantItem ++ plainSyms.map arityItem

/-- The item is one of `sigItems c`, pattern for pattern. -/
noncomputable def inSigItems (it : Item) : Bool := (sigItems c).any (·.pat == it.pat)

/-- **The account of the declarations** (all modules of the text): of the 16 sort declarations, 15
have no sort parameter (the other is `SortMInt{Width}`); of the 131 symbol declarations, 93 have no
sort parameter and name a symbol Γ has, 5 have sort parameters, and 33 name a symbol Γ does not
have (no direction, as the sentences that apply them). -/
theorem decl_counts :
    (kore.sortDecls.length, plainSorts.length, kore.symbolDecls.length, plainSyms.length,
      (kore.symbolDecls.filter fun sd => !sd.params.isEmpty).length,
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (16, 15, 131, 93, 5, 33) := by
  decide +kernel

theorem decl_params : (kore.sortDecls.filter fun sd => !sd.params.isEmpty).map (·.name) = ["SortMInt"] ∧
    (kore.symbolDecls.filter fun sd => !sd.params.isEmpty).map (·.name) =
      ["inj", "LblList'Coln'getMInt", "LblList'Coln'setMInt", "Lblite", "LblsizeMInt"] := by decide +kernel

theorem declsE_0 : ((declItems.drop 0).take 25).all inSigItems = true := by
  decide +kernel
theorem declsE_25 : ((declItems.drop 25).take 25).all inSigItems = true := by
  decide +kernel
theorem declsE_50 : ((declItems.drop 50).take 25).all inSigItems = true := by
  decide +kernel
theorem declsE_75 : (declItems.drop 75).all inSigItems = true := by
  decide +kernel

/-- Each such declaration's item is an item of `sigItems c`, pattern for pattern. -/
theorem decls_in_sig : declItems.all inSigItems = true :=
  tieAllE_whole (p := inSigItems) <|
    tieAllE_range (a := 0) (n := 25) declsE_0 <|
    tieAllE_range (a := 25) (n := 25) declsE_25 <|
    tieAllE_range (a := 50) (n := 25) declsE_50 <|
    declsE_75

/-- **E for the declarations**: Γ entails the G-sort item of each sort declaration without sort
parameters and the G-arity item of each symbol declaration without sort parameters of a symbol Γ
has, for every H; each is one of `sigItems c`'s items. -/
theorem decls_entailed (H : HookParams) : ∀ it ∈ declItems, Γ (cH H) ⊧ it.pat := by
  intro it hit M _ I hI
  have h1 : (sigItems c).any (·.pat == it.pat) = true := List.all_eq_true.mp decls_in_sig it hit
  obtain ⟨it', hit', he⟩ := List.any_eq_true.mp h1
  rw [← of_decide_eq_true he]
  exact sat_sigItem hI (by rw [sigItems_withHooks]; exact hit')

end KCore.TieEns

#check @KCore.TieEns.sig_origin
#check @KCore.TieEns.decls_entailed
#print axioms KCore.TieEns.sig_origin
#print axioms KCore.TieEns.decls_entailed
