/-
  The text of the fixture e6-int2bytes-nolen (`f2-examples/e6-int2bytes-nolen.kompile.kore`: BYTES
  and INT imported, the rules `go(I, E, S) => Int2Bytes(I, E, S)` and `neg(I) => ~Int I`), in the
  direction E. Run from the package root: `lake env lean -j1 test/LibEvInt2BytesNoLen.lean`.

  The rules apply BYTES-HOOKED's `Int2Bytes` without a length (`Int2BytesNoLen`, 306) and
  INT-COMMON's `~Int`, which no hook of the registry interprets, so the reading has both as
  parameter symbols without implementation (`params_i2b`), and Γ states their values only as the
  interpretation's (`Semantics.paramVal`). The library's equations of `Int2BytesNoLen` (domains.md
  2250-2258, axioms 185-189) are then hypotheses on H (owed-sentence rule item 3, class parameter
  lemma).
  - `sorts_in_sig`, `decls_entailed`: each sort declaration without sort parameters has its item
    among `sigItems c`, so Γ entails it for every H.
  - `lib_syms`, `lib_symOK`, `lib_decls_entailed`: `Int2BytesNoLen`'s declaration (`libDeclNames`)
    is declared once, without sort parameters, and names a symbol of Γ whose arity item is the
    declaration's, so Γ entails its item for every H.
  - `i2bZeroEq`: the condition on H that 2250 states: at 0, an Endianness and a Signedness,
    `Int2BytesNoLen` is the empty Bytes.
  - `ev189` (2250, `Int2Bytes(I, _, _) => .Bytes requires I ==Int 0`): entailed at values for every
    H meeting `i2bZeroEq` (`LibEv.FnEqn.entailedP`).
  - `Hi2b`, `hi2b_meets`: an interpretation meeting `i2bZeroEq`.
  - `zero_none`: at `HookParams.none` the left side has no value at 0 while the right side has one,
    so the equation's function form fails there. A statement about the values of the sides, not
    about models of Γ.
  The other four equations (2252-2258, axioms 185-188) match the Signedness argument against a
  constructor (`Signed`, `Unsigned`), which `LibEv`'s terms do not express.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvInt2BytesNoLen

open KCore ML Faithful KoreAML LibEv

kore_term kore from "f2-examples/e6-int2bytes-nolen.kompile.kore"
definition_of defn from "f2-examples/e6-int2bytes-nolen.kompile.kore"
user_axioms U from "f2-examples/e6-int2bytes-nolen.kompile.kore" module "E6-INT2BYTES-NOLEN"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem userAxioms_eq : kore.axiomDecls.filter (·.module == "E6-INT2BYTES-NOLEN") = U.all := by kernel_rfl

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-! ## Declarations -/

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

/-- The first of Γ's symbols under the name `n`. -/
noncomputable def symFind (n : String) : Option CtorSig := (kernelSyms c).find? fun k => c.symName k.name == n

/-- Γ has a symbol under the name `n`. -/
noncomputable def hasSym (n : String) : Bool := (symFind n).isSome

/-- The item is one of `sigItems c`, pattern for pattern. -/
noncomputable def inSigItems (it : Item) : Bool := (sigItems c).any (·.pat == it.pat)

/-- A sort declaration has sort parameters or its item is one of Γ's. -/
noncomputable def sortOK (sd : SortDecl) : Bool := !sd.params.isEmpty || inSigItems (sortConstantItem sd)

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
def libDeclNames : List String := ["LblInt2BytesNoLen"]

/-- A library module's parameter symbols hold the registry symbol `f`, and no hook of the registry
interprets it. -/
def libParamOf (m : String) (f : Sym) : Bool :=
  (library.find? (·.name == m)).any (·.params.any (·.name == f)) && hookSigs.all (·.name != f)

/-- The parameter symbol `Int2BytesNoLen`. -/
abbrev i2bSym : Sym := 306

/-- **The reading's parameter symbols** are `~Int` and `Int2BytesNoLen` (registry symbol 306, a
parameter symbol of BYTES-HOOKED), both without implementation. -/
theorem params_i2b : c.params.map (fun p => (c.symName p.sig.name, p.impl)) =
      [("Lbl'Tild'Int'Unds'", none), ("LblInt2BytesNoLen", none)] ∧
    c.symName i2bSym = "LblInt2BytesNoLen" ∧ libParamOf "BYTES-HOOKED" i2bSym = true := by
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

/-! ## The condition on H -/

/-- **domains.md 2250** at H: at 0, an Endianness and a Signedness, `Int2BytesNoLen` is the empty
Bytes. -/
def i2bZeroEq (H : HookParams) : Prop :=
  ∀ e s, c.sortOf e = some Srt.endianness → c.sortOf s = some Srt.signedness →
    H.app i2bSym [int 0, e, s] = some (bytesV [])

/-- An interpretation meeting `i2bZeroEq`. -/
def Hi2b : HookParams := ⟨fun f vs => match f, vs with
  | 306, [.dv _ (.int a), _, _] => if a = 0 then some (bytesV []) else none
  | _, _ => none⟩

theorem hi2b_meets : i2bZeroEq Hi2b := fun _ _ _ _ => rfl

/-! ## The equation -/

/-- 2250: `Int2Bytes(I, _, _) => .Bytes requires I ==Int 0`. -/
def E189 : FnEqn :=
  { vars := [("VarI", Srt.int), ("Var'Unds'Gen0", Srt.endianness), ("Var'Unds'Gen1", Srt.signedness)],
    f := i2bSym,
    pats := [(Srt.int, .var 0, none), (Srt.endianness, .var 1, none), (Srt.signedness, .var 2, none)],
    s := Srt.bytes, req := some (.app intEq [.var 0, intT 0]), rhs := .app bytesEmpty [] }

kernel_rfl pattern189 : ∀ H : HookParams, U.ax189.ax.pattern = E189.patternP (cH H)
kernel_rfl typed189 : ∀ H : HookParams, E189.typedP (cH H) = true

theorem sortVars189 : U.ax189.ax.sortVars = [KoreAML.Rv] := by decide +kernel

kernel_rfl vkey_withHooks : ∀ (H : HookParams) (vars : Vars) (i : Nat), vkey (cH H) vars i = vkey c vars i

theorem free189 : ∀ i, i < E189.av.length → vkey c E189.av i ∈ KoreAML.freeOf [] U.ax189.ax.pattern := by
  decide +kernel

/-! ## Γ's values of the heads -/

-- Γ's value of `Int2BytesNoLen` at H: H's answer where it is a Bytes value.
kernel_rfl appValI2b : ∀ (H : HookParams) (ws : List GroundTerm),
  appValP (cH H) i2bSym ws = (H.app i2bSym ws).filter fun v => (cH H).sortOf v == some Srt.bytes
kernel_rfl appValEq : ∀ (H : HookParams) (ws : List GroundTerm), appValP (cH H) intEq ws = (cH H).hv intEq ws
kernel_rfl appValEmpty : ∀ (H : HookParams) (ws : List GroundTerm),
  appValP (cH H) bytesEmpty ws = (cH H).hv bytesEmpty ws
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem sortOf_withHooks (H : HookParams) (v : GroundTerm) : (cH H).sortOf v = c.sortOf v :=
  congrFun (Semantics.sortOf_withHooks c H noRaw) v
kernel_rfl sortOf_empty : ∀ H : HookParams, (cH H).sortOf (bytesV []) = some Srt.bytes

theorem fhv_bytesEmpty {d : Semantics} : d.hv bytesEmpty [] = some (bytesV []) := hv_of_value rfl

/-! ## The sides' values -/

theorem holds189 (H : HookParams) (hH : i2bZeroEq H) : E189.HoldsP (cH H) := by
  intro σ hσ hq hm
  obtain ⟨v0, h0, hs0⟩ := hσ 0 ("VarI", Srt.int) rfl
  obtain ⟨e, h1, hs1⟩ := hσ 1 ("Var'Unds'Gen0", Srt.endianness) rfl
  obtain ⟨s, h2, hs2⟩ := hσ 2 ("Var'Unds'Gen1", Srt.signedness) rfl
  obtain ⟨a, rfl⟩ := shape_int (shapesOKH H) hs0
  have hr := hq _ rfl
  simp only [valP, valPList, h0, allSome, Option.bind_some, Option.map_some, appValEq, intT] at hr
  have ha : a = 0 := by
    have h' : (cH H).hv intEq [int a, int 0] = some (bool true) := hr
    rw [fhv_intEq] at h'
    simpa [bool] using h'
  subst ha
  obtain ⟨hm1, -, hm2, -, hm3, -, -⟩ := hm
  have h3 : σ.lookup 3 = some (int 0) := hm1.symm.trans (by show valP (cH H) σ (.var 0) = _; rw [valP, h0])
  have h4 : σ.lookup 4 = some e := hm2.symm.trans (by show valP (cH H) σ (.var 1) = _; rw [valP, h1])
  have h5 : σ.lookup 5 = some s := hm3.symm.trans (by show valP (cH H) σ (.var 2) = _; rw [valP, h2])
  show valP (cH H) σ (.app i2bSym [.var 3, .var 4, .var 5]) = valP (cH H) σ (.app bytesEmpty [])
  simp only [valP, valPList, h3, h4, h5, allSome, Option.bind_some, Option.map_some, appValI2b, appValEmpty]
  rw [sortOf_withHooks] at hs1 hs2
  rw [hH e s hs1 hs2, fhv_bytesEmpty]
  simp [Option.filter, sortOf_empty]

/-! ## Entailed at values -/

/-- **2250** `Int2Bytes(I, _, _) => .Bytes requires I ==Int 0`, entailed at values for every H
meeting `i2bZeroEq`. -/
theorem ev189 (H : HookParams) (hH : i2bZeroEq H) : EntailsAtValues (cH H) U.ax189 (trS U.ax189).pat := by
  rw [(by decide +kernel : (trS U.ax189).pat = (trAxiom [] [] U.ax189).pat)]
  exact FnEqn.entailedP (coreOKH H) E189 (typed189 H) (holds189 H hH) U.ax189 (pattern189 H)
    sortVars189 (fun i hi => by rw [vkey_withHooks]; exact free189 i hi)

/-- At `Hi2b` it is entailed at values. -/
theorem ev189_Hi2b : EntailsAtValues (cH Hi2b) U.ax189 (trS U.ax189).pat := ev189 Hi2b hi2b_meets

/-! ## At `HookParams.none` -/

/-- At `HookParams.none`, 2250's left side has no value at 0, while its right side has one. -/
theorem zero_none (σ : Subst) (e s : GroundTerm) (h3 : σ.lookup 3 = some (int 0)) (h4 : σ.lookup 4 = some e)
    (h5 : σ.lookup 5 = some s) :
    valP (cH HookParams.none) σ E189.lhs = none ∧ valP (cH HookParams.none) σ E189.rhs = some (bytesV []) := by
  constructor
  · show valP (cH HookParams.none) σ (.app i2bSym [.var 3, .var 4, .var 5]) = none
    simp only [valP, valPList, h3, h4, h5, allSome, Option.bind_some, Option.map_some, appValI2b]
    rfl
  · show valP (cH HookParams.none) σ (.app bytesEmpty []) = _
    simp only [valP, valPList, allSome, Option.bind_some, appValEmpty]
    exact fhv_bytesEmpty

end KCore.LibEvInt2BytesNoLen

#check @KCore.LibEvInt2BytesNoLen.decls_entailed
#check @KCore.LibEvInt2BytesNoLen.lib_decls_entailed
#check @KCore.LibEvInt2BytesNoLen.ev189
/-- info: 'KCore.LibEvInt2BytesNoLen.ev189' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvInt2BytesNoLen.ev189
#print axioms KCore.LibEvInt2BytesNoLen.decls_entailed
#print axioms KCore.LibEvInt2BytesNoLen.lib_decls_entailed
#print axioms KCore.LibEvInt2BytesNoLen.params_i2b
#print axioms KCore.LibEvInt2BytesNoLen.ev189_Hi2b
#print axioms KCore.LibEvInt2BytesNoLen.zero_none
