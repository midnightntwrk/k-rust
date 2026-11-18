/-
  The tie (C14) of kimp's declarations (row 19) on its text as kompile wrote it
  (`examples/ref-kimp/RefKimp/definition.kore`), on the literals `kore` and `defn`. Nothing here
  reads `Parse.parse` or `emit`. Run from the package root: `lake env lean test/TieKimpDecls.lean`.

  - `decls_entailed` (E): the item of each sort declaration without sort parameters, and of each
    symbol declaration without sort parameters of a symbol Γ has (`declItems`, 163 items), is an
    item of `sigItems c` pattern for pattern (`decls_in_sig`), so Γ entails it for every H.
    `declPos` names each one's place in `sigItems c` (test/TieKimpHints.lean prints it); the kernel
    checks the item there. Decided by
    ranges, joined by `tieAll_range`.
  - `decl_counts`: of the text's 21 sort declarations, 20 have no sort parameter (the other is
    `SortMInt{Width}`); of its 187 symbol declarations, 143 have no sort parameter and name a
    symbol Γ has, 5 have sort parameters, and 39 name a symbol Γ does not have (no direction, as
    the sentences that apply them).

  The converse, `sig_origin`, is test/TieKimpSig.lean's.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKimp

open KCore ML Faithful KoreAML

kore_term kore from "examples/ref-kimp/RefKimp/definition.kore"
definition_of defn from "examples/ref-kimp/RefKimp/definition.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

/-- Γ has a symbol under the name `n`. -/
noncomputable def hasSym (n : String) : Bool := (kernelSyms c).any fun k => c.symName k.name == n

/-- The declarations of the text whose item `sigItems c` holds: the sort declarations without sort
parameters, and the symbol declarations without sort parameters of a symbol Γ has. -/
noncomputable def plainSorts : List SortDecl := kore.sortDecls.filter (·.params.isEmpty)
noncomputable def plainSyms : List SymbolDecl := kore.symbolDecls.filter fun sd => sd.params.isEmpty && hasSym sd.name
noncomputable def declItems : List Item := plainSorts.map sortConstantItem ++ plainSyms.map arityItem

/-- **The account of the declarations** (all modules of the text). -/
theorem decl_counts :
    (kore.sortDecls.length, plainSorts.length, kore.symbolDecls.length, plainSyms.length,
      (kore.symbolDecls.filter fun sd => !sd.params.isEmpty).length,
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (21, 20, 187, 143, 5, 39) := by
  decide +kernel

theorem decl_params : (kore.sortDecls.filter fun sd => !sd.params.isEmpty).map (·.name) = ["SortMInt"] ∧
    (kore.symbolDecls.filter fun sd => !sd.params.isEmpty).map (·.name) =
      ["inj", "LblList'Coln'getMInt", "LblList'Coln'setMInt", "Lblite", "LblsizeMInt"] := by decide +kernel

/-- The place in `sigItems c` of each item of `declItems`, in its order. -/
def declPos : List Nat :=
  [1, 2, 35, 31, 7, 10, 5, 4, 8, 32, 33, 19, 6, 34, 18, 20, 36, 37, 3, 38, 39, 40, 48, 49, 50, 51, 52, 53,
   54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 171, 150, 161, 45, 47, 41,
   42, 43, 174, 175, 178, 172, 155, 156, 153, 166, 167, 162, 76, 128, 77, 126, 78, 124, 79, 125, 80, 127, 81, 142, 134, 168, 82, 133,
   83, 123, 138, 149, 122, 137, 148, 84, 85, 136, 86, 141, 135, 87, 170, 152, 163, 154, 144, 147, 88, 116, 117, 129, 121, 176, 157, 130,
   118, 119, 120, 151, 164, 89, 139, 145, 181, 140, 90, 91, 165, 101, 108, 109, 111, 110, 104, 105, 103, 102, 95, 106, 107, 97, 96, 112,
   100, 98, 99, 113, 114, 160, 143, 179, 132, 131, 46, 44, 115, 173, 159, 146, 169, 177, 158, 180, 92, 93, 94]

theorem declPos_length : declItems.length = 163 ∧ declPos.length = 163 := by decide +kernel

/-- The item at the place `p.2` of `sigItems c` is `p.1`, pattern for pattern. -/
noncomputable def sigAt (p : Item × Nat) : Bool :=
  match (sigItems c)[p.2]? with
  | some it => decide (it.pat = p.1.pat)
  | none => false

noncomputable def declPairs : List (Item × Nat) := declItems.zip declPos

/-- A member of a list is paired with a member of a list of the same length. -/
theorem tieMem_zip {α β : Type} : ∀ {l : List α} {ps : List β}, l.length = ps.length →
    ∀ {a : α}, a ∈ l → ∃ b, (a, b) ∈ l.zip ps
  | [], _, _, _, h => absurd h List.not_mem_nil
  | _ :: _, [], hl, _, _ => by simp at hl
  | _ :: _, y :: _, hl, _, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨y, List.mem_cons_self ..⟩
    · obtain ⟨b, hb⟩ := tieMem_zip (by simpa using hl) h
      exact ⟨b, List.mem_cons_of_mem _ hb⟩

theorem decls_0 : ((declPairs.drop 0).take 40).all sigAt = true := by decide +kernel
theorem decls_40 : ((declPairs.drop 40).take 40).all sigAt = true := by decide +kernel
theorem decls_80 : ((declPairs.drop 80).take 40).all sigAt = true := by decide +kernel
theorem decls_120 : (declPairs.drop 120).all sigAt = true := by decide +kernel

theorem decls_in_sig : declPairs.all sigAt = true :=
  tieAll_whole (p := sigAt) <|
    tieAll_range (a := 0) (n := 40) decls_0 <|
    tieAll_range (a := 40) (n := 40) decls_40 <|
    tieAll_range (a := 80) (n := 40) decls_80 <|
    decls_120

/-- **E for the declarations**: Γ entails the G-sort item of each sort declaration without sort
parameters and the G-arity item of each symbol declaration without sort parameters of a symbol Γ
has, for every H; each is one of `sigItems c`'s items. -/
theorem decls_entailed (H : HookParams) : ∀ it ∈ declItems, Γ (cH H) ⊧ it.pat := by
  intro it hit M _ I hI
  obtain ⟨k, hk⟩ := tieMem_zip (declPos_length.1.trans declPos_length.2.symm) hit
  have h := List.all_eq_true.mp decls_in_sig _ hk
  unfold sigAt at h
  split at h
  · rename_i it' hit'
    rw [← of_decide_eq_true h]
    exact sat_sigItem hI (by rw [sigItems_withHooks]; exact List.mem_of_getElem? hit')
  · cases h

end KCore.TieKimp

#check @KCore.TieKimp.decls_entailed
#print axioms KCore.TieKimp.decls_entailed
#print axioms KCore.TieKimp.decl_counts
