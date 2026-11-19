/-
  The text of the fixture e6-divides-int (`f2-examples/e6-divides-int.kompile.kore`: INT imported,
  one rule `go(X1, X2) => X1 dividesInt X2`), in the direction E. Run from the package root:
  `lake env lean -j1 test/LibEvDividesInt.lean`.

  The rule applies INT-COMMON's `dividesInt`, which no hook of the registry interprets, so the
  reading has it as its one parameter symbol, without implementation (`params_div`), and Γ states
  its value only as the interpretation's (`Semantics.paramVal`). Its library equation (domains.md
  1454, axiom 183) is then a hypothesis on H (owed-sentence rule item 3, class parameter lemma).
  - `sorts_in_sig`, `decls_entailed`: each sort declaration without sort parameters has its item
    among `sigItems c`, so Γ entails it for every H.
  - `lib_syms`, `lib_symOK`, `lib_decls_entailed`: `dividesInt`'s declaration (`libDeclNames`) is
    declared once, without sort parameters, and names a symbol of Γ whose arity item is the
    declaration's, so Γ entails its item for every H.
  - `divEq`: the condition on H, at Int literals: `I1 dividesInt I2` has no value at I1 = 0 and is
    otherwise whether the truncating remainder of I2 by I1 is 0, i.e. whether I1 divides I2.
  - `ev183` (1454, `I1 dividesInt I2 => (I2 %Int I1) ==Int 0`): entailed at values for every H
    meeting `divEq` (`LibEv.FnEqn.entailedP`). At I1 = 0 the right side has no value (`%Int` by 0
    is undefined), and `divEq` gives the left side none there.
  - `Hdiv`, `hdiv_meets`: an interpretation meeting `divEq`.
  - `div_none`: at `HookParams.none` the left side has no value while the right side has one at
    I1 ≠ 0, so the equation's function form fails there. A statement about the values of the sides,
    not about models of Γ.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvDividesInt

open KCore ML Faithful KoreAML LibEv

kore_term kore from "f2-examples/e6-divides-int.kompile.kore"
definition_of defn from "f2-examples/e6-divides-int.kompile.kore"
user_axioms U from "f2-examples/e6-divides-int.kompile.kore" module "E6-DIVIDES-INT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem userAxioms_eq : kore.axiomDecls.filter (·.module == "E6-DIVIDES-INT") = U.all := by kernel_rfl

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

/-- `dividesInt`'s name. -/
def dividesIntName : String := "Lbl'Unds'dividesInt'UndsUnds'INT-COMMON'Unds'Bool'Unds'Int'Unds'Int"

/-- Library symbol declarations of the text, by name. -/
def libDeclNames : List String :=
  ["Lbl'Unds'dividesInt'UndsUnds'INT-COMMON'Unds'Bool'Unds'Int'Unds'Int"]

/-- A library module's parameter symbols hold the registry symbol `f`, and no hook of the registry
interprets it. -/
def libParamOf (m : String) (f : Sym) : Bool :=
  (library.find? (·.name == m)).any (·.params.any (·.name == f)) && hookSigs.all (·.name != f)

/-- The parameter symbol `dividesInt`. -/
abbrev divSym : Sym := 219

/-- **The reading's parameter symbols** are `dividesInt` alone, registry symbol 219, a parameter
symbol of INT-COMMON, without implementation. -/
theorem params_div : c.params.map (fun p => (p.sig.name, p.impl)) = [(divSym, none)] ∧
    c.symName divSym = dividesIntName ∧ libParamOf "INT-COMMON" divSym = true := by
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

/-- **domains.md 1454** at H, at Int literals: `I1 dividesInt I2` has no value at I1 = 0, and is
otherwise whether I2's truncating remainder by I1 is 0. -/
def divEq (H : HookParams) : Prop :=
  ∀ a b : Int, H.app divSym [int a, int b] = if a = 0 then none else some (bool (decide (b.tmod a = 0)))

/-- An interpretation meeting `divEq`. -/
def Hdiv : HookParams := ⟨fun f vs => match f, vs with
  | 219, [.dv _ (.int a), .dv _ (.int b)] => if a = 0 then none else some (bool (decide (b.tmod a = 0)))
  | _, _ => none⟩

theorem hdiv_meets : divEq Hdiv := fun _ _ => rfl

/-! ## The equation -/

/-- 1454: `I1 dividesInt I2 => (I2 %Int I1) ==Int 0`. -/
def E183 : FnEqn :=
  { vars := [("VarI1", Srt.int), ("VarI2", Srt.int)], f := divSym,
    pats := [(Srt.int, .var 0, none), (Srt.int, .var 1, none)],
    s := Srt.bool, req := none, rhs := .app intEq [.app intTMod [.var 1, .var 0], intT 0] }

kernel_rfl pattern183 : ∀ H : HookParams, U.ax183.ax.pattern = E183.patternP (cH H)
kernel_rfl typed183 : ∀ H : HookParams, E183.typedP (cH H) = true

theorem sortVars183 : U.ax183.ax.sortVars = [KoreAML.Rv] := by decide +kernel

kernel_rfl vkey_withHooks : ∀ (H : HookParams) (vars : Vars) (i : Nat), vkey (cH H) vars i = vkey c vars i

theorem free183 : ∀ i, i < E183.av.length → vkey c E183.av i ∈ KoreAML.freeOf [] U.ax183.ax.pattern := by
  decide +kernel

/-! ## Γ's values of the heads -/

-- Γ's value of `dividesInt` at H: H's answer where it is a Bool.
kernel_rfl appValDiv : ∀ (H : HookParams) (ws : List GroundTerm),
  appValP (cH H) divSym ws = (H.app divSym ws).filter fun v => (cH H).sortOf v == some Srt.bool
kernel_rfl appValMod : ∀ (H : HookParams) (ws : List GroundTerm), appValP (cH H) intTMod ws = (cH H).hv intTMod ws
kernel_rfl sortOf_bool : ∀ (H : HookParams) (b : Bool), (cH H).sortOf (bool b) = some Srt.bool

theorem fhv_intTMod {d : Semantics} {x y : Int} (hy : y ≠ 0) : d.hv intTMod [int x, int y] = some (int (x.tmod y)) :=
  hv_of_value (by
    show hook intTMod [int x, int y] = some (some (int (x.tmod y)))
    have : hook intTMod [int x, int y] = some (nonzero y (x.tmod y)) := rfl
    rw [this, nonzero]; simp only [hy, ↓reduceIte])

/-- `%Int` by 0 has no value: K's text states none (division by zero), whatever the interpretation. -/
theorem fhv_intTMod_zero {d : Semantics} (x : Int) : d.hv intTMod [int x, int 0] = none := by
  unfold Semantics.hv Semantics.hookRes
  rw [show silent intTMod [int x, int 0] = false from rfl]
  rfl

/-! ## The sides' values -/

theorem holds183 (H : HookParams) (hH : divEq H) : E183.HoldsP (cH H) := by
  intro σ hσ _ hm
  obtain ⟨v0, h0, hs0⟩ := hσ 0 ("VarI1", Srt.int) rfl
  obtain ⟨v1, h1, hs1⟩ := hσ 1 ("VarI2", Srt.int) rfl
  obtain ⟨a, rfl⟩ := shape_int (shapesOKH H) hs0
  obtain ⟨b, rfl⟩ := shape_int (shapesOKH H) hs1
  obtain ⟨hm1, -, hm2, -, -⟩ := hm
  have h2 : σ.lookup 2 = some (int a) := hm1.symm.trans (by show valP (cH H) σ (.var 0) = _; rw [valP, h0])
  have h3 : σ.lookup 3 = some (int b) := hm2.symm.trans (by show valP (cH H) σ (.var 1) = _; rw [valP, h1])
  show valP (cH H) σ (.app divSym [.var 2, .var 3]) =
    valP (cH H) σ (.app intEq [.app intTMod [.var 1, .var 0], intT 0])
  simp only [valP, valPList, h0, h1, h2, h3, allSome, Option.bind_some, Option.map_some, appValDiv,
    appValMod, intT]
  rw [hH a b]
  by_cases ha : a = 0
  · subst ha
    rw [fhv_intTMod_zero]
    simp
  · rw [fhv_intTMod ha]
    simp only [ha, ↓reduceIte, Option.filter, sortOf_bool, beq_self_eq_true, Option.bind_some]
    exact (fhv_intEq (b.tmod a) 0).symm

/-! ## Entailed at values -/

/-- **1454** `I1 dividesInt I2 => (I2 %Int I1) ==Int 0`, entailed at values for every H meeting
`divEq`. -/
theorem ev183 (H : HookParams) (hH : divEq H) : EntailsAtValues (cH H) U.ax183 (trS U.ax183).pat := by
  rw [(by decide +kernel : (trS U.ax183).pat = (trAxiom [] [] U.ax183).pat)]
  exact FnEqn.entailedP (coreOKH H) E183 (typed183 H) (holds183 H hH) U.ax183 (pattern183 H)
    sortVars183 (fun i hi => by rw [vkey_withHooks]; exact free183 i hi)

/-- At `Hdiv` it is entailed at values. -/
theorem ev183_Hdiv : EntailsAtValues (cH Hdiv) U.ax183 (trS U.ax183).pat := ev183 Hdiv hdiv_meets

/-! ## At `HookParams.none` -/

/-- At `HookParams.none`, 1454's left side has no value, and at I1 ≠ 0 its right side has one. -/
theorem div_none (σ : Subst) (a b : Int) (ha : a ≠ 0) (h0 : σ.lookup 0 = some (int a))
    (h1 : σ.lookup 1 = some (int b)) (h2 : σ.lookup 2 = some (int a)) (h3 : σ.lookup 3 = some (int b)) :
    valP (cH HookParams.none) σ E183.lhs = none ∧ (valP (cH HookParams.none) σ E183.rhs).isSome := by
  constructor
  · show valP (cH HookParams.none) σ (.app divSym [.var 2, .var 3]) = none
    simp only [valP, valPList, h2, h3, allSome, Option.bind_some, Option.map_some, appValDiv]
    rfl
  · show (valP (cH HookParams.none) σ (.app intEq [.app intTMod [.var 1, .var 0], intT 0])).isSome
    simp only [valP, valPList, h0, h1, allSome, Option.bind_some, Option.map_some, appValMod, intT]
    rw [fhv_intTMod ha]
    simp only [Option.bind_some]
    exact Option.isSome_iff_exists.mpr ⟨_, fhv_intEq (b.tmod a) 0⟩

end KCore.LibEvDividesInt

#check @KCore.LibEvDividesInt.decls_entailed
#check @KCore.LibEvDividesInt.lib_decls_entailed
#check @KCore.LibEvDividesInt.ev183
/-- info: 'KCore.LibEvDividesInt.ev183' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvDividesInt.ev183
#print axioms KCore.LibEvDividesInt.decls_entailed
#print axioms KCore.LibEvDividesInt.lib_decls_entailed
#print axioms KCore.LibEvDividesInt.params_div
#print axioms KCore.LibEvDividesInt.ev183_Hdiv
#print axioms KCore.LibEvDividesInt.div_none
