/-
  Part Decls of the tie (C14) on `f2-examples/e6-param-ffi.kompile.kore`, test/TieE6ParamFfi.lean: the sections
  `--split` puts here, in the tie's namespace. A test file imports no test file, so this one
  repeats the literals and the definitions and facts it reads. Written by
  `test/constructs/tiegen.py e6-param-ffi --split`; run from the package root:
  `lake env lean -j1 test/TieE6ParamFfiDecls.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE6ParamFfi

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6-param-ffi.kompile.kore"
definition_of defn from "f2-examples/e6-param-ffi.kompile.kore"
user_axioms U from "f2-examples/e6-param-ffi.kompile.kore" module "E6-PARAM-FFI"
user_axioms PreludeKseq from "f2-examples/e6-param-ffi.kompile.kore" module "KSEQ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `p` holds from `a` on where it holds on the `n` members from `a` and from `a + n` on. -/
theorem tieAllE_range {α : Type} {l : List α} {p : α → Bool} {a n : Nat}
    (h : ((l.drop a).take n).all p = true) (ht : (l.drop (a + n)).all p = true) :
    (l.drop a).all p = true := by
  rw [← List.take_append_drop n (l.drop a), List.all_append, h, List.drop_drop, ht]; rfl

/-- `p` holds of the whole list where it holds from `0` on. -/
theorem tieAllE_whole {α : Type} {l : List α} {p : α → Bool} (h : (l.drop 0).all p = true) :
    l.all p = true := h

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

/-- Γ has a symbol under the name `n`. -/
noncomputable def hasSym (n : String) : Bool := (kernelSyms c).any fun k => c.symName k.name == n

noncomputable def plainSorts : List SortDecl := kore.sortDecls.filter (·.params.isEmpty)
noncomputable def plainSyms : List SymbolDecl := kore.symbolDecls.filter fun sd => sd.params.isEmpty && hasSym sd.name
noncomputable def declItems : List Item := plainSorts.map sortConstantItem ++ plainSyms.map arityItem

/-- The item is one of `sigItems c`, pattern for pattern. -/
noncomputable def inSigItems (it : Item) : Bool := (sigItems c).any (·.pat == it.pat)

/-- The declarations of the text: sorts, sorts without parameters, symbols, symbols without
parameters that Γ has, symbols with parameters, symbols without parameters that Γ lacks. -/
theorem decl_counts :
    (kore.sortDecls.length, plainSorts.length, kore.symbolDecls.length, plainSyms.length,
      (kore.symbolDecls.filter fun sd => !sd.params.isEmpty).length,
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (21, 20, 234, 172, 12, 50) := by
  decide +kernel

theorem declsE_0 : (((declItems).drop 0).take 8).all inSigItems = true := by decide +kernel
theorem declsE_8 : (((declItems).drop 8).take 8).all inSigItems = true := by decide +kernel
theorem declsE_16 : (((declItems).drop 16).take 8).all inSigItems = true := by decide +kernel
theorem declsE_24 : (((declItems).drop 24).take 8).all inSigItems = true := by decide +kernel
theorem declsE_32 : (((declItems).drop 32).take 8).all inSigItems = true := by decide +kernel
theorem declsE_40 : (((declItems).drop 40).take 8).all inSigItems = true := by decide +kernel
theorem declsE_48 : (((declItems).drop 48).take 8).all inSigItems = true := by decide +kernel
theorem declsE_56 : (((declItems).drop 56).take 8).all inSigItems = true := by decide +kernel
theorem declsE_64 : (((declItems).drop 64).take 8).all inSigItems = true := by decide +kernel
theorem declsE_72 : (((declItems).drop 72).take 8).all inSigItems = true := by decide +kernel
theorem declsE_80 : (((declItems).drop 80).take 8).all inSigItems = true := by decide +kernel
theorem declsE_88 : (((declItems).drop 88).take 8).all inSigItems = true := by decide +kernel
theorem declsE_96 : (((declItems).drop 96).take 8).all inSigItems = true := by decide +kernel
theorem declsE_104 : (((declItems).drop 104).take 8).all inSigItems = true := by decide +kernel
theorem declsE_112 : (((declItems).drop 112).take 8).all inSigItems = true := by decide +kernel
theorem declsE_120 : (((declItems).drop 120).take 8).all inSigItems = true := by decide +kernel
theorem declsE_128 : (((declItems).drop 128).take 8).all inSigItems = true := by decide +kernel
theorem declsE_136 : (((declItems).drop 136).take 8).all inSigItems = true := by decide +kernel
theorem declsE_144 : (((declItems).drop 144).take 8).all inSigItems = true := by decide +kernel
theorem declsE_152 : (((declItems).drop 152).take 8).all inSigItems = true := by decide +kernel
theorem declsE_160 : (((declItems).drop 160).take 8).all inSigItems = true := by decide +kernel
theorem declsE_168 : (((declItems).drop 168).take 8).all inSigItems = true := by decide +kernel
theorem declsE_176 : (((declItems).drop 176).take 8).all inSigItems = true := by decide +kernel
theorem declsE_184 : ((declItems).drop 184).all inSigItems = true := by decide +kernel

theorem decls_in_sig : declItems.all inSigItems = true :=
  tieAllE_whole (p := inSigItems) <|
    tieAllE_range (a := 0) (n := 8) declsE_0 <|
    tieAllE_range (a := 8) (n := 8) declsE_8 <|
    tieAllE_range (a := 16) (n := 8) declsE_16 <|
    tieAllE_range (a := 24) (n := 8) declsE_24 <|
    tieAllE_range (a := 32) (n := 8) declsE_32 <|
    tieAllE_range (a := 40) (n := 8) declsE_40 <|
    tieAllE_range (a := 48) (n := 8) declsE_48 <|
    tieAllE_range (a := 56) (n := 8) declsE_56 <|
    tieAllE_range (a := 64) (n := 8) declsE_64 <|
    tieAllE_range (a := 72) (n := 8) declsE_72 <|
    tieAllE_range (a := 80) (n := 8) declsE_80 <|
    tieAllE_range (a := 88) (n := 8) declsE_88 <|
    tieAllE_range (a := 96) (n := 8) declsE_96 <|
    tieAllE_range (a := 104) (n := 8) declsE_104 <|
    tieAllE_range (a := 112) (n := 8) declsE_112 <|
    tieAllE_range (a := 120) (n := 8) declsE_120 <|
    tieAllE_range (a := 128) (n := 8) declsE_128 <|
    tieAllE_range (a := 136) (n := 8) declsE_136 <|
    tieAllE_range (a := 144) (n := 8) declsE_144 <|
    tieAllE_range (a := 152) (n := 8) declsE_152 <|
    tieAllE_range (a := 160) (n := 8) declsE_160 <|
    tieAllE_range (a := 168) (n := 8) declsE_168 <|
    tieAllE_range (a := 176) (n := 8) declsE_176 <|
    declsE_184

/-- **E for the declarations**: Γ entails the item of each declaration without sort parameters of
a symbol Γ has, for every H. -/
theorem decls_entailed (H : HookParams) : ∀ it ∈ declItems, Γ (cH H) ⊧ it.pat := by
  intro it hit M _ I hI
  have h1 : (sigItems c).any (·.pat == it.pat) = true := List.all_eq_true.mp decls_in_sig it hit
  obtain ⟨it', hit', he⟩ := List.any_eq_true.mp h1
  rw [← of_decide_eq_true he]
  exact sat_sigItem hI (by rw [sigItems_withHooks]; exact hit')

/-- The symbol declarations of the text with a K builtin file's `Source`, without a `hook`
attribute and without sort parameters, that Γ has, by name. -/
def builtinDeclNames : List String :=
  ["Lbl'Hash'ffiCall'LParUndsCommUndsCommUndsCommUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'Bool'Unds'Int'Unds'List'Unds'List'Unds'Int'Unds'FFIType",
   "Lbl'Hash'ffi'Unds'complexdouble",
   "Lbl'Hash'ffi'Unds'complexfloat",
   "Lbl'Hash'ffi'Unds'complexlongdouble",
   "Lbl'Hash'ffi'Unds'double",
   "Lbl'Hash'ffi'Unds'float",
   "Lbl'Hash'ffi'Unds'longdouble",
   "Lbl'Hash'ffi'Unds'pointer",
   "Lbl'Hash'ffi'Unds'schar",
   "Lbl'Hash'ffi'Unds'sint",
   "Lbl'Hash'ffi'Unds'sint16",
   "Lbl'Hash'ffi'Unds'sint32",
   "Lbl'Hash'ffi'Unds'sint64",
   "Lbl'Hash'ffi'Unds'sint8",
   "Lbl'Hash'ffi'Unds'slong",
   "Lbl'Hash'ffi'Unds'sshort",
   "Lbl'Hash'ffi'Unds'struct",
   "Lbl'Hash'ffi'Unds'uchar",
   "Lbl'Hash'ffi'Unds'uint",
   "Lbl'Hash'ffi'Unds'uint16",
   "Lbl'Hash'ffi'Unds'uint32",
   "Lbl'Hash'ffi'Unds'uint64",
   "Lbl'Hash'ffi'Unds'uint8",
   "Lbl'Hash'ffi'Unds'ulong",
   "Lbl'Hash'ffi'Unds'ushort",
   "Lbl'Hash'ffi'Unds'void",
   "Lbl'-LT-'k'-GT-'",
   "LblBool2String'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Bool",
   "LblString2Bool'LParUndsRParUnds'STRING-COMMON'Unds'Bool'Unds'String",
   "LblbigEndianBytes",
   "LblfreshInt'LParUndsRParUnds'INT'Unds'Int'Unds'Int",
   "LbllittleEndianBytes",
   "LblsignedBytes",
   "LblunsignedBytes"]

/-- Each names a symbol of Γ. -/
theorem builtinDeclNames_has : builtinDeclNames.all hasSym = true := by decide +kernel

/-- **E for the symbol declarations named in `builtinDeclNames`**: Γ entails the G-arity item
of each such declaration without sort parameters, for every H. -/
theorem builtin_decls_entailed (H : HookParams) :
    ∀ sd ∈ kore.symbolDecls, sd.params = [] → sd.name ∈ builtinDeclNames → Γ (cH H) ⊧ (arityItem sd).pat :=
  fun sd hsd hp hn => decls_entailed H _ (List.mem_append_right _ (List.mem_map_of_mem
    (List.mem_filter.mpr ⟨hsd, by
      simp only [hp, List.isEmpty_nil, Bool.true_and]; exact List.all_eq_true.mp builtinDeclNames_has _ hn⟩)))

end KCore.TieE6ParamFfi

#check @KCore.TieE6ParamFfi.decls_entailed
#check @KCore.TieE6ParamFfi.builtin_decls_entailed
#print axioms KCore.TieE6ParamFfi.decls_entailed
#print axioms KCore.TieE6ParamFfi.builtin_decls_entailed
