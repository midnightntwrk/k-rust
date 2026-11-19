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
  constructor (`Signed`, `Unsigned`), a term `LibEv.srtP?` gives its sort (the value
  `.ctor signedBytes []`).
  - `FitsI2b`, `MinLenI2b`: n bytes hold an Int as two's complement (signed) or unsigned, and n is
    the fewest that do (domains.md 2060-2063, 2074-2079: `Bytes2Int` reads the bytes so, and the
    second variant of `Int2Bytes` is the smallest Bytes that `Bytes2Int` reads back as the Int).
  - `i2bMinEq`: the condition on H that `Int2BytesNoLen(I, E, S)` is `Int2Bytes(n, I, E)` at the
    fewest bytes n holding I under S; `notEqI2b`: `~Int I` is `-I - 1` (domains.md 1227, the
    complement in two's complement), which 2256's right side applies.
  - `minLen_unsigned_i2b`, `minLen_signed_pos_i2b`, `minLen_signed_neg_i2b`, `minLen_m1_i2b`:
    the lengths the right sides compute, `(log2Int(I) +Int 8) /Int 8` unsigned and
    `(log2Int(I) +Int 9) /Int 8`, `(log2Int(~Int I) +Int 9) /Int 8` and 1 signed, are the fewest
    bytes under each equation's condition.
  - `ev185` (2254), `ev186` (2256, also under `notEqI2b`), `ev187` (2258), `ev188` (2252): entailed
    at values for every H meeting `i2bMinEq` (`LibEv.FnEqn.entailedP`).
  - `Hi2bAll`, `hi2bAll_meets`, `ev_Hi2bAll`: `Hi2b` extended by the fewest-bytes `Int2Bytes`
    (`.Bytes` at a negative Int with `Unsigned`, which no length holds and no equation reaches) and
    by `~Int I = -I - 1` meets the three conditions, so at that one H the five equations 185-189
    are entailed at values together.
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

/-! ## The equations at a Signedness constructor (2252-2258) -/

/-- `n` bytes hold `a` under the signedness (`true` signed): as two's complement,
`-2^(8n) ≤ 2a < 2^(8n)`; unsigned, `0 ≤ a < 2^(8n)` (domains.md 2060-2063: `Bytes2Int` reads a
Bytes as a two's complement or an unsigned representation). -/
def FitsI2b (sg : Bool) (a : Int) (n : Nat) : Prop :=
  if sg then -(2 ^ (8 * n) : Int) ≤ 2 * a ∧ 2 * a < 2 ^ (8 * n) else 0 ≤ a ∧ a < 2 ^ (8 * n)

/-- `n` is the fewest bytes that hold `a` under the signedness. -/
def MinLenI2b (sg : Bool) (a : Int) (n : Nat) : Prop := FitsI2b sg a n ∧ ∀ m, m < n → ¬ FitsI2b sg a m

/-- The parameter symbol `~Int`. -/
abbrev notSymI2b : Sym := 208

/-- **domains.md 2074-2077** at H: `Int2BytesNoLen(I, E, S)` is `Int2Bytes(n, I, E)` at the fewest
bytes n holding I under S, for an Endianness E and a Signedness S (`asSigned`: `Signed` true). -/
def i2bMinEq (H : HookParams) : Prop :=
  ∀ (sg : Bool) (a : Int) (n : Nat) (e s : GroundTerm), c.sortOf e = some Srt.endianness →
    asSigned s = some sg → MinLenI2b sg a n →
    H.app i2bSym [int a, e, s] = (cH H).hv int2Bytes [int n, int a, e]

/-- **domains.md 1227** at H: `~Int I`, the bitwise complement of I in two's complement, is `-I - 1`. -/
def notEqI2b (H : HookParams) : Prop := ∀ a : Int, H.app notSymI2b [int a] = some (int (-a - 1))

/-! ### The fewest bytes -/

theorem pow2_mono_i2b {i j : Nat} (h : i ≤ j) : (2 : Int) ^ i ≤ 2 ^ j := by
  have := Nat.pow_le_pow_right (n := 2) (by decide) h
  exact_mod_cast this

theorem log2_bounds_i2b {x : Nat} (hx : x ≠ 0) :
    (2 : Int) ^ x.log2 ≤ x ∧ (x : Int) < 2 ^ (x.log2 + 1) :=
  ⟨by exact_mod_cast Nat.log2_self_le hx, by exact_mod_cast Nat.lt_log2_self⟩

/-- The fewest bytes are one number. -/
theorem minLen_unique_i2b {sg : Bool} {a : Int} {n n' : Nat} (h : MinLenI2b sg a n)
    (h' : MinLenI2b sg a n') : n = n' := by
  rcases Nat.lt_trichotomy n n' with hl | he | hg
  · exact absurd h.1 (h'.2 n hl)
  · exact he
  · exact absurd h'.1 (h.2 n' hg)

theorem minLen_zero_i2b (sg : Bool) : MinLenI2b sg 0 0 := by
  refine ⟨?_, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  cases sg <;> simp [FitsI2b]

theorem minLen_m1_i2b : MinLenI2b true (-1) 1 := by
  refine ⟨?_, fun m hm => ?_⟩
  · simp only [FitsI2b, ↓reduceIte]; decide
  · have : m = 0 := by omega
    subst this
    simp only [FitsI2b, ↓reduceIte]; decide

/-- Unsigned, at `x > 0`: `(log2 x + 8) / 8` bytes (2252's length). -/
theorem minLen_unsigned_i2b {x : Nat} (hx : x ≠ 0) : MinLenI2b false x ((x.log2 + 8) / 8) := by
  obtain ⟨h1, h2⟩ := log2_bounds_i2b hx
  refine ⟨?_, fun m hm => ?_⟩
  · simp only [FitsI2b, Bool.false_eq_true, ↓reduceIte]
    have := pow2_mono_i2b (show x.log2 + 1 ≤ 8 * ((x.log2 + 8) / 8) by omega)
    omega
  · simp only [FitsI2b, Bool.false_eq_true, ↓reduceIte]
    have := pow2_mono_i2b (show 8 * m ≤ x.log2 by omega)
    omega

/-- Signed, at `x > 0`: `(log2 x + 9) / 8` bytes (2254's length). -/
theorem minLen_signed_pos_i2b {x : Nat} (hx : x ≠ 0) : MinLenI2b true x ((x.log2 + 9) / 8) := by
  obtain ⟨h1, h2⟩ := log2_bounds_i2b hx
  refine ⟨?_, fun m hm => ?_⟩
  · simp only [FitsI2b, ↓reduceIte]
    have := pow2_mono_i2b (show x.log2 + 2 ≤ 8 * ((x.log2 + 9) / 8) by omega)
    have h3 : (2 : Int) ^ (x.log2 + 2) = 2 * 2 ^ (x.log2 + 1) := by rw [Int.pow_succ]; omega
    have h4 : (0 : Int) ≤ 2 ^ (8 * ((x.log2 + 9) / 8)) := Int.pow_nonneg (by decide)
    omega
  · simp only [FitsI2b, ↓reduceIte]
    have := pow2_mono_i2b (show 8 * m ≤ x.log2 + 1 by omega)
    have h3 : (2 : Int) ^ (x.log2 + 1) = 2 * 2 ^ x.log2 := by rw [Int.pow_succ]; omega
    omega

/-- Signed, at `-x - 1` with `x > 0` (so below -1, and `x` is its `~Int`): `(log2 x + 9) / 8`
bytes (2256's length). -/
theorem minLen_signed_neg_i2b {x : Nat} (hx : x ≠ 0) : MinLenI2b true (-(x : Int) - 1) ((x.log2 + 9) / 8) := by
  obtain ⟨h1, h2⟩ := log2_bounds_i2b hx
  refine ⟨?_, fun m hm => ?_⟩
  · simp only [FitsI2b, ↓reduceIte]
    have := pow2_mono_i2b (show x.log2 + 2 ≤ 8 * ((x.log2 + 9) / 8) by omega)
    have h3 : (2 : Int) ^ (x.log2 + 2) = 2 * 2 ^ (x.log2 + 1) := by rw [Int.pow_succ]; omega
    have h4 : (0 : Int) ≤ 2 ^ (8 * ((x.log2 + 9) / 8)) := Int.pow_nonneg (by decide)
    omega
  · simp only [FitsI2b, ↓reduceIte]
    have := pow2_mono_i2b (show 8 * m ≤ x.log2 + 1 by omega)
    have h3 : (2 : Int) ^ (x.log2 + 1) = 2 * 2 ^ x.log2 := by rw [Int.pow_succ]; omega
    omega

/-- The fewest bytes at the boundaries: signed 127, -128 and -1 take one, 128 and -129 two;
unsigned 255 one, 256 two; 0 none. -/
example : MinLenI2b true 127 1 ∧ MinLenI2b true 128 2 ∧ MinLenI2b true (-128) 1 ∧ MinLenI2b true (-129) 2 ∧
    MinLenI2b true (-1) 1 ∧ MinLenI2b false 255 1 ∧ MinLenI2b false 256 2 ∧ MinLenI2b true 0 0 :=
  ⟨minLen_signed_pos_i2b (x := 127) (by decide), minLen_signed_pos_i2b (x := 128) (by decide),
   minLen_signed_neg_i2b (x := 127) (by decide), minLen_signed_neg_i2b (x := 128) (by decide),
   minLen_m1_i2b, minLen_unsigned_i2b (x := 255) (by decide), minLen_unsigned_i2b (x := 256) (by decide),
   minLen_zero_i2b true⟩

/-! ### The equations -/

/-- The right side's length `(log2Int(J) +Int k) /Int 8`. -/
def lenT (j : Term) (k : Int) : Term := .app intTDiv [.app intAdd [.app intLog2 [j], intT k], intT 8]

/-- `Int2BytesNoLen(I, E, sg) => rhs requires req`, the Signedness argument matched against the
constructor `sg`. -/
def eqnI2b (sg : Sym) (req rhs : Term) : FnEqn :=
  { vars := [("VarI", Srt.int), ("VarE", Srt.endianness)], f := i2bSym,
    pats := [(Srt.int, .var 0, none), (Srt.endianness, .var 1, none), (Srt.signedness, .app sg [], none)],
    s := Srt.bytes, req := some req, rhs := rhs }

/-- 2254: `Int2Bytes(I, E, Signed) => Int2Bytes((log2Int(I) +Int 9) /Int 8, I, E) requires I >Int 0`. -/
def E185 : FnEqn :=
  eqnI2b signedBytes (.app intGt [.var 0, intT 0]) (.app int2Bytes [lenT (.var 0) 9, .var 0, .var 1])

/-- 2256: `Int2Bytes(I, E, Signed) => Int2Bytes((log2Int(~Int I) +Int 9) /Int 8, I, E) requires I <Int -1`. -/
def E186 : FnEqn :=
  eqnI2b signedBytes (.app intLt [.var 0, intT (-1)])
    (.app int2Bytes [lenT (.app notSymI2b [.var 0]) 9, .var 0, .var 1])

/-- 2258: `Int2Bytes(I, E, Signed) => Int2Bytes(1, -1, E) requires I ==Int -1`. -/
def E187 : FnEqn :=
  eqnI2b signedBytes (.app intEq [.var 0, intT (-1)]) (.app int2Bytes [intT 1, intT (-1), .var 1])

/-- 2252: `Int2Bytes(I, E, Unsigned) => Int2Bytes((log2Int(I) +Int 8) /Int 8, I, E) requires I >Int 0`. -/
def E188 : FnEqn :=
  eqnI2b unsignedBytes (.app intGt [.var 0, intT 0]) (.app int2Bytes [lenT (.var 0) 8, .var 0, .var 1])

kernel_rfl pattern185 : ∀ H : HookParams, U.ax185.ax.pattern = E185.patternP (cH H)
kernel_rfl pattern186 : ∀ H : HookParams, U.ax186.ax.pattern = E186.patternP (cH H)
kernel_rfl pattern187 : ∀ H : HookParams, U.ax187.ax.pattern = E187.patternP (cH H)
kernel_rfl pattern188 : ∀ H : HookParams, U.ax188.ax.pattern = E188.patternP (cH H)
kernel_rfl typed185 : ∀ H : HookParams, E185.typedP (cH H) = true
kernel_rfl typed186 : ∀ H : HookParams, E186.typedP (cH H) = true
kernel_rfl typed187 : ∀ H : HookParams, E187.typedP (cH H) = true
kernel_rfl typed188 : ∀ H : HookParams, E188.typedP (cH H) = true

theorem sortVars185 : U.ax185.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sortVars186 : U.ax186.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sortVars187 : U.ax187.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sortVars188 : U.ax188.ax.sortVars = [KoreAML.Rv] := by decide +kernel

theorem free185 : ∀ i, i < E185.av.length → vkey c E185.av i ∈ KoreAML.freeOf [] U.ax185.ax.pattern := by
  decide +kernel
theorem free186 : ∀ i, i < E186.av.length → vkey c E186.av i ∈ KoreAML.freeOf [] U.ax186.ax.pattern := by
  decide +kernel
theorem free187 : ∀ i, i < E187.av.length → vkey c E187.av i ∈ KoreAML.freeOf [] U.ax187.ax.pattern := by
  decide +kernel
theorem free188 : ∀ i, i < E188.av.length → vkey c E188.av i ∈ KoreAML.freeOf [] U.ax188.ax.pattern := by
  decide +kernel

/-! ### Γ's values of the heads -/

-- A Signedness constructor's value is itself; `~Int`'s is H's answer where it is an Int.
kernel_rfl appValSigned : ∀ H : HookParams, appValP (cH H) signedBytes [] = some (.ctor signedBytes [])
kernel_rfl appValUnsigned : ∀ H : HookParams, appValP (cH H) unsignedBytes [] = some (.ctor unsignedBytes [])
kernel_rfl appValNot : ∀ (H : HookParams) (ws : List GroundTerm),
  appValP (cH H) notSymI2b ws = (H.app notSymI2b ws).filter fun v => (cH H).sortOf v == some Srt.int
kernel_rfl appValI2B : ∀ (H : HookParams) (ws : List GroundTerm), appValP (cH H) int2Bytes ws = (cH H).hv int2Bytes ws
kernel_rfl appValGt : ∀ (H : HookParams) (ws : List GroundTerm), appValP (cH H) intGt ws = (cH H).hv intGt ws
kernel_rfl appValLt : ∀ (H : HookParams) (ws : List GroundTerm), appValP (cH H) intLt ws = (cH H).hv intLt ws
kernel_rfl appValAdd : ∀ (H : HookParams) (ws : List GroundTerm), appValP (cH H) intAdd ws = (cH H).hv intAdd ws
kernel_rfl appValTDiv : ∀ (H : HookParams) (ws : List GroundTerm), appValP (cH H) intTDiv ws = (cH H).hv intTDiv ws
kernel_rfl appValLog2 : ∀ (H : HookParams) (ws : List GroundTerm), appValP (cH H) intLog2 ws = (cH H).hv intLog2 ws

theorem fhv_intGt {d : Semantics} (x y : Int) : d.hv intGt [int x, int y] = some (bool (decide (x > y))) :=
  hv_of_value rfl
theorem fhv_intLt {d : Semantics} (x y : Int) : d.hv intLt [int x, int y] = some (bool (decide (x < y))) :=
  hv_of_value rfl
theorem fhv_intAdd {d : Semantics} (x y : Int) : d.hv intAdd [int x, int y] = some (int (x + y)) := hv_of_value rfl
theorem fhv_intLog2 {d : Semantics} {y : Int} (hy : 0 < y) : d.hv intLog2 [int y] = some (int y.toNat.log2) :=
  hv_of_value (by
    rw [show hook intLog2 [int y] = some (if 0 < y then some (int y.toNat.log2) else none) from rfl]
    simp only [hy, ↓reduceIte])
theorem fhv_tdiv8 {d : Semantics} (x : Int) : d.hv intTDiv [int x, int 8] = some (int (x.tdiv 8)) :=
  hv_of_value (by
    rw [show hook intTDiv [int x, int 8] = some (nonzero 8 (x.tdiv 8)) from rfl, nonzero]
    simp only [show (8 : Int) ≠ 0 by decide, ↓reduceIte])

/-- `Int2Bytes(n, x, E)` at an Endianness E is the Bytes value of `KBytes.ofInt` at E's byte order. -/
theorem fhv_int2Bytes {d : Semantics} (n : Nat) (x : Int) {e : GroundTerm}
    (he : e = .ctor littleEndianBytes [] ∨ e = .ctor bigEndianBytes []) :
    ∃ be r, asEndian e = some be ∧ KBytes.ofInt n x be = some r ∧ d.hv int2Bytes [int n, int x, e] = some (bytesV r) ∧
      d.sortOf (bytesV r) = some Srt.bytes := by
  have hof : ∀ b : Bool, ∃ r, KBytes.ofInt n x b = some r := fun b => by
    unfold KBytes.ofInt
    simp only [show ¬ (n : Int) < 0 by omega, ↓reduceIte]
    exact ⟨_, rfl⟩
  rcases he with rfl | rfl
  · obtain ⟨r, hr⟩ := hof false
    exact ⟨false, r, rfl, hr, hv_of_value (by
      rw [show hook int2Bytes [int n, int x, .ctor littleEndianBytes []] = some ((KBytes.ofInt n x false).map bytesV)
        from rfl, hr]; rfl), sortOf_bytesV (KBytes.ofInt_lt hr)⟩
  · obtain ⟨r, hr⟩ := hof true
    exact ⟨true, r, rfl, hr, hv_of_value (by
      rw [show hook int2Bytes [int n, int x, .ctor bigEndianBytes []] = some ((KBytes.ofInt n x true).map bytesV)
        from rfl, hr]; rfl), sortOf_bytesV (KBytes.ofInt_lt hr)⟩

kernel_rfl sortOf_int : ∀ (H : HookParams) (x : Int), (cH H).sortOf (int x) = some Srt.int

/-- The left side at `(int a, e, s)` under `i2bMinEq`: H's `Int2Bytes(n, a, e)` at the fewest bytes. -/
theorem lhs_minLen (H : HookParams) (hH : i2bMinEq H) {sg : Bool} {a : Int} {n : Nat} {e s : GroundTerm}
    (he : c.sortOf e = some Srt.endianness) (hs : asSigned s = some sg) (hn : MinLenI2b sg a n) :
    appValP (cH H) i2bSym [int a, e, s] = (cH H).hv int2Bytes [int n, int a, e] := by
  rw [appValI2b, hH sg a n e s he hs hn]
  obtain ⟨_, r, -, -, hv, hsr⟩ := fhv_int2Bytes (d := cH H) n a (shape_endian (shapesOKH H) (by rw [sortOf_withHooks]; exact he))
  rw [hv]
  simp [Option.filter, hsr]

/-! ### The sides' values -/

theorem dv9 : GroundTerm.dv Srt.int (.int 9) = int 9 := rfl
theorem dv8 : GroundTerm.dv Srt.int (.int 8) = int 8 := rfl
theorem dv0 : GroundTerm.dv Srt.int (.int 0) = int 0 := rfl
theorem dvm1 : GroundTerm.dv Srt.int (.int (-1)) = int (-1) := rfl
theorem dv1 : GroundTerm.dv Srt.int (.int 1) = int 1 := rfl

/-- The common start of the four: σ's values of the pattern variables and argument variables. -/
theorem match_i2b (H : HookParams) {sg : Sym} {req rhs : Term} (σ : Subst)
    (hσ : ∀ i p, (eqnI2b sg req rhs).av[i]? = some p → ∃ v, σ.lookup i = some v ∧ (cH H).sortOf v = some p.2)
    (hm : FnEqn.MatchesP (cH H) σ (eqnI2b sg req rhs).vars.length (eqnI2b sg req rhs).pats) :
    ∃ a e, σ.lookup 0 = some (int a) ∧ σ.lookup 1 = some e ∧ c.sortOf e = some Srt.endianness ∧
      σ.lookup 2 = some (int a) ∧ σ.lookup 3 = some e ∧ σ.lookup 4 = valP (cH H) σ (.app sg []) := by
  obtain ⟨v0, h0, hs0⟩ := hσ 0 ("VarI", Srt.int) rfl
  obtain ⟨e, h1, hs1⟩ := hσ 1 ("VarE", Srt.endianness) rfl
  obtain ⟨a, rfl⟩ := shape_int (shapesOKH H) hs0
  obtain ⟨hm1, -, hm2, -, hm3, -, -⟩ := hm
  refine ⟨a, e, h0, h1, by rw [← sortOf_withHooks H]; exact hs1, ?_, ?_, hm3.symm⟩
  · exact hm1.symm.trans (by show valP (cH H) σ (.var 0) = _; rw [valP, h0])
  · exact hm2.symm.trans (by show valP (cH H) σ (.var 1) = _; rw [valP, h1])

theorem bool_true_i2b {p : Prop} [Decidable p] (h : bool (decide p) = bool true) : p := by
  unfold bool at h; injection h with _ h; injection h with h; simpa using h

theorem holds185 (H : HookParams) (hH : i2bMinEq H) : E185.HoldsP (cH H) := by
  intro σ hσ hq hm
  obtain ⟨a, e, h0, h1, he, h2, h3, h4⟩ := match_i2b H σ hσ hm
  simp only [valP, valPList, allSome, Option.bind_some, appValSigned] at h4
  have hr := hq _ rfl
  simp only [valP, valPList, h0, allSome, Option.bind_some, Option.map_some, appValGt, intT, dv0] at hr
  have ha : a > 0 := bool_true_i2b (Option.some.inj ((fhv_intGt a 0).symm.trans hr))
  obtain ⟨x, rfl⟩ : ∃ x : Nat, a = x := ⟨a.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  show valP (cH H) σ (.app i2bSym [.var 2, .var 3, .var 4]) = valP (cH H) σ (.app int2Bytes [lenT (.var 0) 9, .var 0, .var 1])
  simp only [lenT, valP, valPList, h0, h1, h2, h3, h4, allSome, Option.bind_some, appValI2B, appValTDiv, appValAdd,
    appValLog2, intT, Option.map_some, dv9, dv8, fhv_intLog2 ha, fhv_intAdd, fhv_tdiv8]
  have hlen : ((((x : Int).toNat.log2 : Nat) : Int) + 9).tdiv 8 = (((x.log2 + 9) / 8 : Nat) : Int) := by
    rw [Int.toNat_natCast, Int.ofNat_tdiv]; push_cast; rfl
  rw [hlen]
  exact lhs_minLen H hH he rfl (minLen_signed_pos_i2b (by omega))

theorem holds188 (H : HookParams) (hH : i2bMinEq H) : E188.HoldsP (cH H) := by
  intro σ hσ hq hm
  obtain ⟨a, e, h0, h1, he, h2, h3, h4⟩ := match_i2b H σ hσ hm
  simp only [valP, valPList, allSome, Option.bind_some, appValUnsigned] at h4
  have hr := hq _ rfl
  simp only [valP, valPList, h0, allSome, Option.bind_some, Option.map_some, appValGt, intT, dv0] at hr
  have ha : a > 0 := bool_true_i2b (Option.some.inj ((fhv_intGt a 0).symm.trans hr))
  obtain ⟨x, rfl⟩ : ∃ x : Nat, a = x := ⟨a.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  show valP (cH H) σ (.app i2bSym [.var 2, .var 3, .var 4]) = valP (cH H) σ (.app int2Bytes [lenT (.var 0) 8, .var 0, .var 1])
  simp only [lenT, valP, valPList, h0, h1, h2, h3, h4, allSome, Option.bind_some, appValI2B, appValTDiv, appValAdd,
    appValLog2, intT, Option.map_some, dv8, fhv_intLog2 ha, fhv_intAdd, fhv_tdiv8]
  have hlen : ((((x : Int).toNat.log2 : Nat) : Int) + 8).tdiv 8 = (((x.log2 + 8) / 8 : Nat) : Int) := by
    rw [Int.toNat_natCast, Int.ofNat_tdiv]; push_cast; rfl
  rw [hlen]
  exact lhs_minLen H hH he rfl (minLen_unsigned_i2b (by omega))

theorem holds186 (H : HookParams) (hH : i2bMinEq H) (hN : notEqI2b H) : E186.HoldsP (cH H) := by
  intro σ hσ hq hm
  obtain ⟨a, e, h0, h1, he, h2, h3, h4⟩ := match_i2b H σ hσ hm
  simp only [valP, valPList, allSome, Option.bind_some, appValSigned] at h4
  have hr := hq _ rfl
  simp only [valP, valPList, h0, allSome, Option.bind_some, Option.map_some, appValLt, intT, dvm1] at hr
  have ha : a < -1 := bool_true_i2b (Option.some.inj ((fhv_intLt a (-1)).symm.trans hr))
  obtain ⟨x, hx⟩ : ∃ x : Nat, -a - 1 = x := ⟨(-a - 1).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hax : a = -(x : Int) - 1 := by omega
  show valP (cH H) σ (.app i2bSym [.var 2, .var 3, .var 4]) =
    valP (cH H) σ (.app int2Bytes [lenT (.app notSymI2b [.var 0]) 9, .var 0, .var 1])
  simp only [lenT, valP, valPList, h0, h1, h2, h3, h4, allSome, Option.bind_some, appValNot, intT, Option.map_some,
    dv9, dv8, hN a, hx]
  simp only [Option.filter, sortOf_int, beq_self_eq_true, ↓reduceIte, Option.bind_some, appValI2B, appValTDiv, appValAdd, appValLog2, fhv_intLog2 (show (0 : Int) < x by omega), fhv_intAdd, fhv_tdiv8]
  have hlen : ((((x : Int).toNat.log2 : Nat) : Int) + 9).tdiv 8 = (((x.log2 + 9) / 8 : Nat) : Int) := by
    rw [Int.toNat_natCast, Int.ofNat_tdiv]; push_cast; rfl
  rw [hlen]
  have := lhs_minLen (s := .ctor signedBytes []) H hH he rfl (minLen_signed_neg_i2b (x := x) (by omega))
  rw [← hax] at this
  exact this

theorem holds187 (H : HookParams) (hH : i2bMinEq H) : E187.HoldsP (cH H) := by
  intro σ hσ hq hm
  obtain ⟨a, e, h0, h1, he, h2, h3, h4⟩ := match_i2b H σ hσ hm
  simp only [valP, valPList, allSome, Option.bind_some, appValSigned] at h4
  have hr := hq _ rfl
  simp only [valP, valPList, h0, allSome, Option.bind_some, Option.map_some, appValEq, intT, dvm1] at hr
  have ha : a = -1 := bool_true_i2b (Option.some.inj ((fhv_intEq a (-1)).symm.trans hr))
  subst ha
  show valP (cH H) σ (.app i2bSym [.var 2, .var 3, .var 4]) = valP (cH H) σ (.app int2Bytes [intT 1, intT (-1), .var 1])
  simp only [valP, valPList, h1, h2, h3, h4, allSome, Option.bind_some, Option.map_some, appValI2B, intT, dv1, dvm1]
  exact lhs_minLen H hH he rfl minLen_m1_i2b

/-! ### Entailed at values -/

/-- **2254**, entailed at values for every H meeting `i2bMinEq`. -/
theorem ev185 (H : HookParams) (hH : i2bMinEq H) : EntailsAtValues (cH H) U.ax185 (trS U.ax185).pat := by
  rw [(by decide +kernel : (trS U.ax185).pat = (trAxiom [] [] U.ax185).pat)]
  exact FnEqn.entailedP (coreOKH H) E185 (typed185 H) (holds185 H hH) U.ax185 (pattern185 H)
    sortVars185 (fun i hi => by rw [vkey_withHooks]; exact free185 i hi)

/-- **2256**, entailed at values for every H meeting `i2bMinEq` and `notEqI2b`. -/
theorem ev186 (H : HookParams) (hH : i2bMinEq H) (hN : notEqI2b H) :
    EntailsAtValues (cH H) U.ax186 (trS U.ax186).pat := by
  rw [(by decide +kernel : (trS U.ax186).pat = (trAxiom [] [] U.ax186).pat)]
  exact FnEqn.entailedP (coreOKH H) E186 (typed186 H) (holds186 H hH hN) U.ax186 (pattern186 H)
    sortVars186 (fun i hi => by rw [vkey_withHooks]; exact free186 i hi)

/-- **2258**, entailed at values for every H meeting `i2bMinEq`. -/
theorem ev187 (H : HookParams) (hH : i2bMinEq H) : EntailsAtValues (cH H) U.ax187 (trS U.ax187).pat := by
  rw [(by decide +kernel : (trS U.ax187).pat = (trAxiom [] [] U.ax187).pat)]
  exact FnEqn.entailedP (coreOKH H) E187 (typed187 H) (holds187 H hH) U.ax187 (pattern187 H)
    sortVars187 (fun i hi => by rw [vkey_withHooks]; exact free187 i hi)

/-- **2252**, entailed at values for every H meeting `i2bMinEq`. -/
theorem ev188 (H : HookParams) (hH : i2bMinEq H) : EntailsAtValues (cH H) U.ax188 (trS U.ax188).pat := by
  rw [(by decide +kernel : (trS U.ax188).pat = (trAxiom [] [] U.ax188).pat)]
  exact FnEqn.entailedP (coreOKH H) E188 (typed188 H) (holds188 H hH) U.ax188 (pattern188 H)
    sortVars188 (fun i hi => by rw [vkey_withHooks]; exact free188 i hi)

/-! ## One interpretation for the five -/

/-- The fewest bytes holding `a` under the signedness, by the four equations' lengths: none for a
negative `a` unsigned, which no length holds. -/
def minLenOfI2b (sg : Bool) (a : Int) : Option Nat :=
  if a = 0 then some 0
  else if 0 < a then some ((a.toNat.log2 + (if sg then 9 else 8)) / 8)
  else if !sg then none
  else if a = -1 then some 1
  else some (((-a - 1).toNat.log2 + 9) / 8)

theorem minLenOf_of_i2b {sg : Bool} {a : Int} {n : Nat} (h : MinLenI2b sg a n) : minLenOfI2b sg a = some n := by
  unfold minLenOfI2b
  by_cases h0 : a = 0
  · subst h0; simp only [↓reduceIte]; rw [minLen_unique_i2b (minLen_zero_i2b sg) h]
  by_cases hp : 0 < a
  · obtain ⟨x, rfl⟩ : ∃ x : Nat, a = x := ⟨a.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    simp only [h0, hp, ↓reduceIte, Int.toNat_natCast]
    cases sg
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [minLen_unique_i2b (minLen_unsigned_i2b (by omega)) h]
    · simp only [↓reduceIte]; rw [minLen_unique_i2b (minLen_signed_pos_i2b (by omega)) h]
  cases sg
  · exfalso
    have := h.1
    simp only [FitsI2b, Bool.false_eq_true, ↓reduceIte] at this
    omega
  by_cases hm : a = -1
  · subst hm; simp only [↓reduceIte, Bool.not_true]; rw [minLen_unique_i2b minLen_m1_i2b h]; rfl
  obtain ⟨x, hx⟩ : ∃ x : Nat, -a - 1 = x := ⟨(-a - 1).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hax : a = -(x : Int) - 1 := by omega
  simp only [h0, hp, hm, ↓reduceIte, Bool.not_true, hx, Int.toNat_natCast]
  rw [hax] at h
  rw [minLen_unique_i2b (minLen_signed_neg_i2b (by omega)) h]
  rfl

/-- `Hi2b` with, at a nonzero Int, an Endianness and a Signedness, `Int2Bytes` at the fewest bytes
(`KBytes.ofInt`), `.Bytes` where no length holds the Int (a negative one with `Unsigned`, where no
equation applies), and `~Int I` as `-I - 1`. -/
def Hi2bAll : HookParams := ⟨fun f vs => match f, vs with
  | 306, [.dv _ (.int a), e, s] =>
    if a = 0 then some (bytesV [])
    else (asSigned s).bind fun sg => (asEndian e).bind fun be =>
      (KBytes.ofInt ((minLenOfI2b sg a).getD 0) a be).map bytesV
  | 208, [.dv _ (.int a)] => some (int (-a - 1))
  | _, _ => none⟩

theorem hi2bAll_meets : i2bZeroEq Hi2bAll ∧ i2bMinEq Hi2bAll ∧ notEqI2b Hi2bAll := by
  refine ⟨fun _ _ _ _ => rfl, ?_, fun _ => rfl⟩
  intro sg a n e s he hs hn
  obtain ⟨be, r, hbe, hr, hv, -⟩ := fhv_int2Bytes (d := cH Hi2bAll) n a (shape_endian (shapesOKH Hi2bAll)
    (by rw [sortOf_withHooks]; exact he))
  rw [hv]
  show (if a = 0 then some (bytesV []) else (asSigned s).bind fun sg => (asEndian e).bind fun be =>
    (KBytes.ofInt ((minLenOfI2b sg a).getD 0) a be).map bytesV) = _
  by_cases h0 : a = 0
  · subst h0
    have hn0 := minLen_unique_i2b (minLen_zero_i2b sg) hn
    subst hn0
    simp only [↓reduceIte]
    have : KBytes.ofInt ((0 : Nat) : Int) 0 be = some [] := by cases be <;> rfl
    rw [hr] at this
    cases this
    rfl
  · simp only [h0, ↓reduceIte, hs, Option.bind_some, minLenOf_of_i2b hn, Option.getD_some, hbe, hr, Option.map_some]

/-- **The five equations at one interpretation**: at `Hi2bAll`, 2250 to 2258 (sentences 185 to 189)
are entailed at values together. -/
theorem ev_Hi2bAll : EntailsAtValues (cH Hi2bAll) U.ax185 (trS U.ax185).pat ∧
    EntailsAtValues (cH Hi2bAll) U.ax186 (trS U.ax186).pat ∧ EntailsAtValues (cH Hi2bAll) U.ax187 (trS U.ax187).pat ∧
    EntailsAtValues (cH Hi2bAll) U.ax188 (trS U.ax188).pat ∧ EntailsAtValues (cH Hi2bAll) U.ax189 (trS U.ax189).pat :=
  ⟨ev185 _ hi2bAll_meets.2.1, ev186 _ hi2bAll_meets.2.1 hi2bAll_meets.2.2, ev187 _ hi2bAll_meets.2.1,
   ev188 _ hi2bAll_meets.2.1, ev189 _ hi2bAll_meets.1⟩

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
#check @KCore.LibEvInt2BytesNoLen.ev185
#check @KCore.LibEvInt2BytesNoLen.ev186
#check @KCore.LibEvInt2BytesNoLen.ev187
#check @KCore.LibEvInt2BytesNoLen.ev188
#check @KCore.LibEvInt2BytesNoLen.ev_Hi2bAll
/-- info: 'KCore.LibEvInt2BytesNoLen.ev_Hi2bAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvInt2BytesNoLen.ev_Hi2bAll
#print axioms KCore.LibEvInt2BytesNoLen.ev185
#print axioms KCore.LibEvInt2BytesNoLen.ev186
#print axioms KCore.LibEvInt2BytesNoLen.ev187
#print axioms KCore.LibEvInt2BytesNoLen.ev188
#print axioms KCore.LibEvInt2BytesNoLen.hi2bAll_meets
