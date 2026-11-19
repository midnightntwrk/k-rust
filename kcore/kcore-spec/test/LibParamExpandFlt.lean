/-
  The sentences of four library symbols Γ lacks hold together at values in one model of Γ whose
  steps are Step's, on silentflt (`f2-examples/silentflt.kompile.kore`: FLOAT, STRING, BYTES and
  SET imported), for every interpretation H: owed-sentence rule item 7, library parameters. Run
  from the package root: `lake env lean -j1 test/LibParamExpandFlt.lean`.

  The four symbols are library parameters no rule and no function of the reading applies, so Γ
  lacks them (`lacked_names`; `test/LibEvDeclsFlt.lean`, `dividesInt_absent`): INT-COMMON's
  `dividesInt` (registry symbol 219), INT's `~Int` (208), BYTES-HOOKED's `Int2BytesNoLen` (306)
  and FLOAT's `rootFloat` (235). The model is the value model with the four names patched
  (`TieLibParam.model_lacked`), their values at values chosen by shape:
  - `dividesInt(a, b)` is what `(b %Int a) ==Int 0` has (shape s3, sentence 274);
  - `rootFloat(x, n)` is what `sqrtFloat(x)` has where `n` is 2, nothing elsewhere (shape s5,
    sentence 380, the equation of `sqrtFloat`, a symbol of Γ);
  - `~Int(i)` is `-i - 1`, and `Int2BytesNoLen(i, e, s)` the value of the one equation of 228 to
    232 whose condition holds at `(i, s)`, `.Bytes` where none does (`i < 0` with
    `unsignedBytes`) (shape s4, with the `functional` sentences of both, 45 and 176).

  `expansion`: for every H, one interpretation satisfying `Γc ∪ Γstep` of `c.withHooks H`, whose
  steps at configurations are `Step`'s, in which each of these sentences, as the text's
  translation writes it, holds at every valuation that sends its free element variables to values.

  Not stated here: that every model of Γ has such a choice (the expansion condition (E) for every
  model). `TieLibParam.expand_lacked` keeps a model a model where the interpretation changes at the
  lacked names only, keeping its carrier and its application. A choice there needs, for
  `dividesInt`, an element of the carrier whose application to two Int elements denotes what
  `(I2 %Int I1) ==Int 0` does; Γ states the existence of no such element, and this file does not
  show one in every model. The model here gains such elements by patching the value model's
  application at elements no premise reaches.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibParamExpandFlt

open KCore ML Faithful KoreAML LibEv TieLibParam

kore_term kore from "f2-examples/silentflt.kompile.kore"
definition_of defn from "f2-examples/silentflt.kompile.kore"
user_axioms U from "f2-examples/silentflt.kompile.kore" module "SILENTFLT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- The text's translation of a sentence, with its declarations. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem sortOfH (H : HookParams) : (cH H).sortOf = c.sortOf := Semantics.sortOf_withHooks c H (by decide +kernel)

/-! ## `FnHyp` under every H -/

theorem fns_params : c.fns = [] ∧ c.params = [] := by decide +kernel

theorem term_named : c.rankObligations [] ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP [] [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (cH H) [] [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-! ## The symbols -/

def dividesSig : CtorSig := ⟨219, [Srt.int, Srt.int], Srt.bool⟩
def notSig : CtorSig := ⟨208, [Srt.int], Srt.int⟩
def noLenSig : CtorSig := ⟨306, [Srt.int, Srt.endianness, Srt.signedness], Srt.bytes⟩
def rootSig : CtorSig := ⟨235, [Srt.float, Srt.int], Srt.float⟩

/-- The four library symbols. -/
def lacked : List CtorSig := [dividesSig, notSig, noLenSig, rootSig]
/-- Signedness's two constructors, which the equations of `Int2BytesNoLen` match. -/
def ctorsL : List CtorSig := [⟨signedBytes, [], Srt.signedness⟩, ⟨unsignedBytes, [], Srt.signedness⟩]
/-- The heads the sentences apply that are no interpreted hooked symbol. -/
def ls : List CtorSig := lacked ++ ctorsL

/-- **The four are the registry's library parameters under the names the text declares, Γ lacks
each, and each resolves to no symbol**: each is a parameter of a module of the library with the
signature above, no hook interprets it, the text declares it once, and its name is neither `inj`
nor the name of a head of Γ. -/
theorem lacked_names :
    lacked.all (fun k => (library.any fun m => m.params.any (· == k)) && !isHook k.name &&
      (kore.symbolDecls.filter (·.name == c.symName k.name)).length == 1 &&
      sigNamed c lacked (c.symName k.name) == some k && lackedNameB c (c.symName k.name) &&
      GenEqs.unresolvedB c (c.symName k.name) && (iteSort? (c.symName k.name)).isNone) = true := by
  decide +kernel

theorem names_text : c.symName 219 = "Lbl'Unds'dividesInt'UndsUnds'INT-COMMON'Unds'Bool'Unds'Int'Unds'Int" ∧
    c.symName 208 = "Lbl'Tild'Int'Unds'" ∧ c.symName 306 = "LblInt2BytesNoLen" ∧
    c.symName 235 = "LblrootFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Int" := by
  decide +kernel

/-! ## The values -/

def zeroV : GroundTerm := .dv Srt.int (.int 0)
def twoV : GroundTerm := .dv Srt.int (.int 2)

/-- `~Int(i)`: `-i - 1`, bitwise not. -/
def notG (ws : List GroundTerm) : Option GroundTerm :=
  match ws with
  | [i] => (asInt i).map fun x => int (-x - 1)
  | _ => none

/-- `Int2Bytes((log2Int(j) +Int k) /Int 8, i, e)`, the right side of 228, 229 and 231. -/
noncomputable def bytesOfLen (H : HookParams) (k : Int) (j i e : GroundTerm) : Option GroundTerm :=
  ((cH H).hv intLog2 [j]).bind fun l => ((cH H).hv intAdd [l, .dv Srt.int (.int k)]).bind fun a =>
    ((cH H).hv intTDiv [a, .dv Srt.int (.int 8)]).bind fun n => (cH H).hv int2Bytes [n, i, e]

/-- `Int2BytesNoLen(i, e, s)`: the right side of the one equation of 228 to 232 whose condition
holds, `.Bytes` where none does (`i < 0` with `unsignedBytes`). -/
noncomputable def noLenG (H : HookParams) (i e s : GroundTerm) : Option GroundTerm :=
  match asInt i with
  | none => none
  | some x =>
    if x = 0 then (cH H).hv bytesEmpty []
    else if s = .ctor signedBytes [] then
      if 0 < x then bytesOfLen H 9 i i e
      else if x = -1 then (cH H).hv int2Bytes [.dv Srt.int (.int 1), .dv Srt.int (.int (-1)), e]
      else (notG [i]).bind fun j => bytesOfLen H 9 j i e
    else if 0 < x then bytesOfLen H 8 i i e
    else (cH H).hv bytesEmpty []

/-- The values chosen for the heads `ls` names, at their argument values. -/
noncomputable def G (H : HookParams) : Sym → List GroundTerm → Option GroundTerm := fun f ws =>
  if f = 219 then
    match ws with
    | [a, b] => ((cH H).hv intTMod [b, a]).bind fun r => (cH H).hv intEq [r, zeroV]
    | _ => none
  else if f = 235 then
    match ws with
    | [x, n] => if n = twoV then (cH H).hv floatSqrt [x] else none
    | _ => none
  else if f = 208 then notG ws
  else if f = 306 then
    match ws with
    | [i, e, s] => noLenG H i e s
    | _ => none
  else if f = signedBytes ∨ f = unsignedBytes then
    if ws = [] then some (.ctor f []) else none
  else none

theorem isHook_facts : isHook 219 = false ∧ isHook 235 = false ∧ isHook 208 = false ∧ isHook 306 = false ∧
    isHook signedBytes = false ∧ isHook unsignedBytes = false ∧ isHook intTMod = true ∧ isHook intEq = true ∧
    isHook floatSqrt = true ∧ isHook intGt = true ∧ isHook intLt = true ∧ isHook intLog2 = true ∧
    isHook intAdd = true ∧ isHook intTDiv = true ∧ isHook int2Bytes = true ∧ isHook bytesEmpty = true := by
  decide +kernel

/-! ## The equations -/

/-- 274 (domains.md 1454): `I1 dividesInt I2 => (I2 %Int I1) ==Int 0`. -/
def e274 : FnEqn :=
  ⟨[("VarI1", Srt.int), ("VarI2", Srt.int)], 219, [(Srt.int, .var 0, none), (Srt.int, .var 1, none)], Srt.bool,
    none, .app intEq [.app intTMod [.var 1, .var 0], .dv Srt.int (.int 0)]⟩

/-- 380 (domains.md 1671): `sqrtFloat(F) => rootFloat(F, 2)`. -/
def e380 : FnEqn :=
  ⟨[("VarF", Srt.float)], floatSqrt, [(Srt.float, .var 0, none)], Srt.float, none,
    .app 235 [.var 0, .dv Srt.int (.int 2)]⟩

theorem e274_text : U.ax274.ax.pattern = e274.patR ∧ U.ax274.ax.sortVars = [KoreAML.Rv] ∧ e274.regular = true ∧
    e274.typedLk c.sortOf ls = true ∧ (trS U.ax274).pat = (trAxiom [] [] U.ax274).pat := by
  decide +kernel

theorem e380_text : U.ax380.ax.pattern = e380.patR ∧ U.ax380.ax.sortVars = [KoreAML.Rv] ∧ e380.regular = true ∧
    e380.typedLk c.sortOf ls = true ∧ (trS U.ax380).pat = (trAxiom [] [] U.ax380).pat := by
  decide +kernel

/-- 228 (domains.md 2254): `Int2BytesNoLen(I, E, signedBytes) => Int2Bytes((log2Int(I) +Int 9) /Int 8, I, E)
requires I >Int 0`. -/
def e228 : FnEqn :=
  ⟨[("VarI", Srt.int), ("VarE", Srt.endianness)], 306,
    [(Srt.int, .var 0, none), (Srt.endianness, .var 1, none), (Srt.signedness, .app signedBytes [], none)], Srt.bytes,
    some (.app intGt [.var 0, .dv Srt.int (.int 0)]),
    .app int2Bytes [.app intTDiv [.app intAdd [.app intLog2 [.var 0], .dv Srt.int (.int 9)], .dv Srt.int (.int 8)],
      .var 0, .var 1]⟩

/-- 229 (domains.md 2256): `Int2BytesNoLen(I, E, signedBytes) => Int2Bytes((log2Int(~Int I) +Int 9) /Int 8, I, E)
requires I <Int -1`. -/
def e229 : FnEqn :=
  ⟨[("VarI", Srt.int), ("VarE", Srt.endianness)], 306,
    [(Srt.int, .var 0, none), (Srt.endianness, .var 1, none), (Srt.signedness, .app signedBytes [], none)], Srt.bytes,
    some (.app intLt [.var 0, .dv Srt.int (.int (-1))]),
    .app int2Bytes [.app intTDiv [.app intAdd [.app intLog2 [.app 208 [.var 0]], .dv Srt.int (.int 9)],
      .dv Srt.int (.int 8)], .var 0, .var 1]⟩

/-- 230 (domains.md 2258): `Int2BytesNoLen(I, E, signedBytes) => Int2Bytes(1, -1, E) requires I ==Int -1`. -/
def e230 : FnEqn :=
  ⟨[("VarI", Srt.int), ("VarE", Srt.endianness)], 306,
    [(Srt.int, .var 0, none), (Srt.endianness, .var 1, none), (Srt.signedness, .app signedBytes [], none)], Srt.bytes,
    some (.app intEq [.var 0, .dv Srt.int (.int (-1))]),
    .app int2Bytes [.dv Srt.int (.int 1), .dv Srt.int (.int (-1)), .var 1]⟩

/-- 231 (domains.md 2252): `Int2BytesNoLen(I, E, unsignedBytes) => Int2Bytes((log2Int(I) +Int 8) /Int 8, I, E)
requires I >Int 0`. -/
def e231 : FnEqn :=
  ⟨[("VarI", Srt.int), ("VarE", Srt.endianness)], 306,
    [(Srt.int, .var 0, none), (Srt.endianness, .var 1, none), (Srt.signedness, .app unsignedBytes [], none)],
    Srt.bytes, some (.app intGt [.var 0, .dv Srt.int (.int 0)]),
    .app int2Bytes [.app intTDiv [.app intAdd [.app intLog2 [.var 0], .dv Srt.int (.int 8)], .dv Srt.int (.int 8)],
      .var 0, .var 1]⟩

/-- 232 (domains.md 2250): `Int2BytesNoLen(I, _, _) => .Bytes requires I ==Int 0`. -/
def e232 : FnEqn :=
  ⟨[("VarI", Srt.int), ("Var'Unds'Gen0", Srt.endianness), ("Var'Unds'Gen1", Srt.signedness)], 306,
    [(Srt.int, .var 0, none), (Srt.endianness, .var 1, none), (Srt.signedness, .var 2, none)], Srt.bytes,
    some (.app intEq [.var 0, .dv Srt.int (.int 0)]), .app bytesEmpty []⟩

theorem e228_text : U.ax228.ax.pattern = e228.patR ∧ U.ax228.ax.sortVars = [KoreAML.Rv] ∧ e228.regular = true ∧
    e228.typedLk c.sortOf ls = true ∧ (trS U.ax228).pat = (trAxiom [] [] U.ax228).pat := by
  decide +kernel
theorem e229_text : U.ax229.ax.pattern = e229.patR ∧ U.ax229.ax.sortVars = [KoreAML.Rv] ∧ e229.regular = true ∧
    e229.typedLk c.sortOf ls = true ∧ (trS U.ax229).pat = (trAxiom [] [] U.ax229).pat := by
  decide +kernel
theorem e230_text : U.ax230.ax.pattern = e230.patR ∧ U.ax230.ax.sortVars = [KoreAML.Rv] ∧ e230.regular = true ∧
    e230.typedLk c.sortOf ls = true ∧ (trS U.ax230).pat = (trAxiom [] [] U.ax230).pat := by
  decide +kernel
theorem e231_text : U.ax231.ax.pattern = e231.patR ∧ U.ax231.ax.sortVars = [KoreAML.Rv] ∧ e231.regular = true ∧
    e231.typedLk c.sortOf ls = true ∧ (trS U.ax231).pat = (trAxiom [] [] U.ax231).pat := by
  decide +kernel
theorem e232_text : U.ax232.ax.pattern = e232.patR ∧ U.ax232.ax.sortVars = [KoreAML.Rv] ∧ e232.regular = true ∧
    e232.typedLk c.sortOf ls = true ∧ (trS U.ax232).pat = (trAxiom [] [] U.ax232).pat := by
  decide +kernel

/-- The `functional` sentences of `Int2BytesNoLen` (45) and `~Int` (176). -/
theorem fun_text : U.ax45.ax.pattern = funPatR noLenSig ∧ U.ax45.ax.sortVars = [KoreAML.Rv] ∧ funReg noLenSig = true ∧
    (trS U.ax45).pat = (trAxiom [] [] U.ax45).pat ∧
    U.ax176.ax.pattern = funPatR notSig ∧ U.ax176.ax.sortVars = [KoreAML.Rv] ∧ funReg notSig = true ∧
    (trS U.ax176).pat = (trAxiom [] [] U.ax176).pat ∧
    sigLk ls noLenSig.name = some noLenSig ∧ sigLk ls notSig.name = some notSig := by
  decide +kernel

theorem holds274 (H : HookParams) : e274.HoldsLk (cH H) (G H) := by
  intro σ hσ _ hm
  obtain ⟨v0, h0, -⟩ := hσ 0 _ rfl
  obtain ⟨v1, h1, -⟩ := hσ 1 _ rfl
  obtain ⟨v2, h2, -⟩ := hσ 2 _ rfl
  obtain ⟨v3, h3, -⟩ := hσ 3 _ rfl
  obtain ⟨hm0, -, hm1, -, -⟩ := hm
  simp only [e274, valLk, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.zero_add, h0, h1, h2, h3,
    Option.some.injEq] at hm0 hm1
  subst hm0 hm1
  simp [e274, FnEqn.lhs, FnEqn.xTerms, valLk, valListLk, allSome, h0, h1, h2, h3, isHook_facts, G, zeroV,
    Option.bind_assoc]

theorem holds380 (H : HookParams) : e380.HoldsLk (cH H) (G H) := by
  intro σ hσ _ hm
  obtain ⟨v0, h0, -⟩ := hσ 0 _ rfl
  obtain ⟨v1, h1, -⟩ := hσ 1 _ rfl
  obtain ⟨hm0, -, -⟩ := hm
  simp only [e380, valLk, List.length_cons, List.length_nil, Nat.zero_add, h0, h1,
    Option.some.injEq] at hm0
  subst hm0
  simp [e380, FnEqn.lhs, FnEqn.xTerms, valLk, valListLk, allSome, h0, h1, isHook_facts, G, twoV]

/-! ## The hooks at Int values -/

theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

theorem hvGt {d : Semantics} (x y : Int) : d.hv intGt [int x, int y] = some (bool (decide (x > y))) := hv_of_value rfl
theorem hvLt {d : Semantics} (x y : Int) : d.hv intLt [int x, int y] = some (bool (decide (x < y))) := hv_of_value rfl
theorem hvEq {d : Semantics} (x y : Int) : d.hv intEq [int x, int y] = some (bool (decide (x = y))) := hv_of_value rfl
theorem hvAdd {d : Semantics} (x y : Int) : d.hv intAdd [int x, int y] = some (int (x + y)) := hv_of_value rfl
theorem hvLog2 {d : Semantics} {y : Int} (hy : 0 < y) : d.hv intLog2 [int y] = some (int y.toNat.log2) :=
  hv_of_value (by
    rw [show hook intLog2 [int y] = some (if 0 < y then some (int y.toNat.log2) else none) from rfl]
    simp only [hy, ↓reduceIte])
theorem hvTDiv8 {d : Semantics} (x : Int) : d.hv intTDiv [int x, int 8] = some (int (x.tdiv 8)) :=
  hv_of_value (by
    rw [show hook intTDiv [int x, int 8] = some (nonzero 8 (x.tdiv 8)) from rfl, nonzero]
    simp only [show (8 : Int) ≠ 0 by decide, ↓reduceIte])
theorem hvEmpty {d : Semantics} : d.hv bytesEmpty [] = some (bytesV []) := hv_of_value rfl

theorem hvI2B {d : Semantics} {n : Int} (hn : 0 ≤ n) (x : Int) {e : GroundTerm}
    (he : e = .ctor littleEndianBytes [] ∨ e = .ctor bigEndianBytes []) : ∃ v, d.hv int2Bytes [int n, int x, e] = some v := by
  have hof : ∀ b : Bool, ∃ r, KBytes.ofInt n x b = some r := fun b => by
    unfold KBytes.ofInt
    simp only [show ¬ n < 0 by omega, ↓reduceIte]
    exact ⟨_, rfl⟩
  rcases he with rfl | rfl
  · obtain ⟨r, hr⟩ := hof false
    exact ⟨bytesV r, hv_of_value (by
      rw [show hook int2Bytes [int n, int x, .ctor littleEndianBytes []] = some ((KBytes.ofInt n x false).map bytesV)
        from rfl, hr]; rfl)⟩
  · obtain ⟨r, hr⟩ := hof true
    exact ⟨bytesV r, hv_of_value (by
      rw [show hook int2Bytes [int n, int x, .ctor bigEndianBytes []] = some ((KBytes.ofInt n x true).map bytesV)
        from rfl, hr]; rfl)⟩

theorem bool_inj {a b : Bool} (h : bool a = bool b) : a = b := by
  unfold bool at h; injection h with _ h; injection h

/-- `Int2Bytes((log2Int(j) +Int k) /Int 8, i, e)` has a value at `j > 0`, `k ≥ 0`, an Int `i` and an
Endianness `e`. -/
theorem bytesOfLen_some (H : HookParams) {k y : Int} (hk : 0 ≤ k) (hy : 0 < y) (x : Int) {e : GroundTerm}
    (he : e = .ctor littleEndianBytes [] ∨ e = .ctor bigEndianBytes []) : ∃ v, bytesOfLen H k (int y) (int x) e = some v := by
  obtain ⟨v, hv⟩ := hvI2B (d := cH H) (n := ((y.toNat.log2 : Int) + k).tdiv 8)
    (Int.tdiv_nonneg (by omega) (by decide)) x he
  refine ⟨v, ?_⟩
  unfold bytesOfLen
  rw [hvLog2 hy, Option.bind_some, show GroundTerm.dv Srt.int (.int k) = int k from rfl, hvAdd, Option.bind_some,
    show GroundTerm.dv Srt.int (.int 8) = int 8 from rfl, hvTDiv8, Option.bind_some, hv]

theorem sigs_bytes : lookupSig hookSigs intLog2 = some ⟨intLog2, [Srt.int], Srt.int⟩ ∧
    lookupSig hookSigs intAdd = some ⟨intAdd, [Srt.int, Srt.int], Srt.int⟩ ∧
    lookupSig hookSigs intTDiv = some ⟨intTDiv, [Srt.int, Srt.int], Srt.int⟩ ∧
    lookupSig hookSigs int2Bytes = some ⟨int2Bytes, [Srt.int, Srt.int, Srt.endianness], Srt.bytes⟩ ∧
    lookupSig hookSigs bytesEmpty = some ⟨bytesEmpty, [], Srt.bytes⟩ := by decide +kernel

/-! ## The equations of `Int2BytesNoLen` hold under `G` -/

/-- At a substitution of values of an equation of 228 to 231's variables: the Int variable is an Int
literal, the argument variables are the pattern variables', and the Signedness one is `sg`. -/
theorem nolen_subst (H : HookParams) {E : FnEqn} (hav : E.av = [("VarI", Srt.int), ("VarE", Srt.endianness),
      ("X0", Srt.int), ("X1", Srt.endianness), ("X2", Srt.signedness)])
    (hvl : E.vars.length = 2) {sg : Sym} (hsg : sg = signedBytes ∨ sg = unsignedBytes)
    (hpats : E.pats = [(Srt.int, .var 0, none), (Srt.endianness, .var 1, none), (Srt.signedness, .app sg [], none)])
    {σ : Subst} (hσ : ∀ i p, E.av[i]? = some p → ∃ v, σ.lookup i = some v ∧ (cH H).sortOf v = some p.2)
    (hm : FnEqn.MatchesLk (cH H) (G H) σ E.vars.length E.pats) :
    ∃ x e, σ.lookup 0 = some (int x) ∧ σ.lookup 1 = some e ∧ σ.lookup 2 = some (int x) ∧ σ.lookup 3 = some e ∧
      σ.lookup 4 = some (.ctor sg []) ∧ (e = .ctor littleEndianBytes [] ∨ e = .ctor bigEndianBytes []) := by
  rw [hav] at hσ
  obtain ⟨v0, h0, hs0⟩ := hσ 0 _ rfl
  obtain ⟨v1, h1, hs1⟩ := hσ 1 _ rfl
  obtain ⟨x, rfl⟩ := shape_int (shapesOKH H) hs0
  rw [hvl, hpats] at hm
  obtain ⟨hm0, -, hm1, -, hm2, -, -⟩ := hm
  have hG : G H sg [] = some (.ctor sg []) := by
    rcases hsg with rfl | rfl <;> simp (config := { decide := true }) [G]
  have hh : isHook sg = false := by rcases hsg with rfl | rfl <;> decide +kernel
  simp only [valLk, valListLk, allSome, h0, h1, Option.bind_some, hh, Bool.false_eq_true, ↓reduceIte, hG] at hm0 hm1 hm2
  exact ⟨x, v1, h0, h1, hm0.symm, hm1.symm, hm2.symm, shape_endian (shapesOKH H) hs1⟩

theorem asInt_int (x : Int) : asInt (int x) = some x := rfl

theorem holds228 (H : HookParams) : e228.HoldsLk (cH H) (G H) := by
  intro σ hσ hreq hm
  obtain ⟨x, e, h0, h1, h2, h3, h4, -⟩ := nolen_subst H rfl rfl (.inl rfl) rfl hσ hm
  have hq := hreq _ rfl
  simp only [valLk, valListLk, allSome, h0, Option.bind_some, Option.map_some, isHook_facts, ↓reduceIte,
    show GroundTerm.dv Srt.int (.int 0) = int 0 from rfl, hvGt, Option.some.injEq] at hq
  have hx : 0 < x := by simpa using bool_inj hq
  simp (config := { decide := true }) only [e228, FnEqn.lhs, FnEqn.xTerms, valLk, valListLk, allSome, h0, h1, h2, h3, h4,
    Option.bind_some, Option.map_some, ↓reduceIte, G, noLenG, asInt_int, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.zero_add, show x ≠ 0 by omega, hx, bytesOfLen, Option.bind_assoc]

theorem holds229 (H : HookParams) : e229.HoldsLk (cH H) (G H) := by
  intro σ hσ hreq hm
  obtain ⟨x, e, h0, h1, h2, h3, h4, -⟩ := nolen_subst H rfl rfl (.inl rfl) rfl hσ hm
  have hq := hreq _ rfl
  simp only [valLk, valListLk, allSome, h0, Option.bind_some, Option.map_some, isHook_facts, ↓reduceIte,
    show GroundTerm.dv Srt.int (.int (-1)) = int (-1) from rfl, hvLt, Option.some.injEq] at hq
  have hx : x < -1 := by simpa using bool_inj hq
  simp (config := { decide := true }) only [e229, FnEqn.lhs, FnEqn.xTerms, valLk, valListLk, allSome, h0, h1, h2, h3,
    h4, Option.bind_some, Option.map_some, ↓reduceIte, G, noLenG, notG, asInt_int, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.zero_add, show x ≠ 0 by omega, show ¬ 0 < x by omega, show x ≠ -1 by omega,
    bytesOfLen, Option.bind_assoc]

theorem holds230 (H : HookParams) : e230.HoldsLk (cH H) (G H) := by
  intro σ hσ hreq hm
  obtain ⟨x, e, h0, h1, h2, h3, h4, -⟩ := nolen_subst H rfl rfl (.inl rfl) rfl hσ hm
  have hq := hreq _ rfl
  simp only [valLk, valListLk, allSome, h0, Option.bind_some, Option.map_some, isHook_facts, ↓reduceIte,
    show GroundTerm.dv Srt.int (.int (-1)) = int (-1) from rfl, hvEq, Option.some.injEq] at hq
  have hx : x = -1 := by simpa using bool_inj hq
  subst hx
  simp (config := { decide := true }) only [e230, FnEqn.lhs, FnEqn.xTerms, valLk, valListLk, allSome, h1, h2, h3,
    h4, Option.bind_some, Option.map_some, ↓reduceIte, G, noLenG, asInt_int, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.zero_add]

theorem holds231 (H : HookParams) : e231.HoldsLk (cH H) (G H) := by
  intro σ hσ hreq hm
  obtain ⟨x, e, h0, h1, h2, h3, h4, -⟩ := nolen_subst H rfl rfl (.inr rfl) rfl hσ hm
  have hq := hreq _ rfl
  simp only [valLk, valListLk, allSome, h0, Option.bind_some, Option.map_some, isHook_facts, ↓reduceIte,
    show GroundTerm.dv Srt.int (.int 0) = int 0 from rfl, hvGt, Option.some.injEq] at hq
  have hx : 0 < x := by simpa using bool_inj hq
  simp (config := { decide := true }) only [e231, FnEqn.lhs, FnEqn.xTerms, valLk, valListLk, allSome, h0, h1, h2, h3,
    h4, Option.bind_some, Option.map_some, ↓reduceIte, G, noLenG, asInt_int, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.zero_add, show x ≠ 0 by omega, hx, bytesOfLen, Option.bind_assoc]

theorem holds232 (H : HookParams) : e232.HoldsLk (cH H) (G H) := by
  intro σ hσ hreq hm
  obtain ⟨v0, h0, hs0⟩ := hσ 0 _ rfl
  obtain ⟨v1, h1, -⟩ := hσ 1 _ rfl
  obtain ⟨v2, h2, -⟩ := hσ 2 _ rfl
  obtain ⟨v3, h3, -⟩ := hσ 3 _ rfl
  obtain ⟨v4, h4, -⟩ := hσ 4 _ rfl
  obtain ⟨v5, h5, -⟩ := hσ 5 _ rfl
  obtain ⟨x, rfl⟩ := shape_int (shapesOKH H) hs0
  obtain ⟨hm0, -, hm1, -, hm2, -, -⟩ := hm
  simp only [e232, valLk, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.zero_add, h0, h1, h2, h3, h4, h5,
    Option.some.injEq] at hm0 hm1 hm2
  subst hm0 hm1 hm2
  have hq := hreq _ rfl
  simp only [valLk, valListLk, allSome, h0, Option.bind_some, Option.map_some, isHook_facts, ↓reduceIte,
    show GroundTerm.dv Srt.int (.int 0) = int 0 from rfl, hvEq, Option.some.injEq] at hq
  have hx : x = 0 := by simpa using bool_inj hq
  subst hx
  simp (config := { decide := true }) only [e232, FnEqn.lhs, FnEqn.xTerms, valLk, valListLk, allSome, h3, h4, h5,
    Option.bind_some, Option.map_some, ↓reduceIte, G, noLenG, asInt_int, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.zero_add]

/-! ## The values' sorts -/

theorem hv_sorted {d : Semantics} (h : d.coreOK = true) {f : Sym} {k : CtorSig} (hk : lookupSig hookSigs f = some k)
    {ws : List GroundTerm} (hws : d.sortsOf ws = some k.args) {v : GroundTerm} (hv : d.hv f ws = some v) :
    d.sortOf v = some k.result := by
  refine hookRes_sorted (fun _ => rangeBelow_of_core h) hk hws ?_
  unfold Semantics.hv at hv
  cases hr : d.hookRes f ws with
  | none => rw [hr] at hv; cases hv
  | some o => rw [hr] at hv; cases o with
    | none => cases hv
    | some w => cases hv; rfl

theorem sigs_hook : lookupSig hookSigs intTMod = some ⟨intTMod, [Srt.int, Srt.int], Srt.int⟩ ∧
    lookupSig hookSigs intEq = some ⟨intEq, [Srt.int, Srt.int], Srt.bool⟩ ∧
    lookupSig hookSigs floatSqrt = some ⟨floatSqrt, [Srt.float], Srt.float⟩ := by decide +kernel

theorem sortsOf2 {d : Semantics} {a b : GroundTerm} {s t : Srt} :
    d.sortsOf [a, b] = some [s, t] ↔ d.sortOf a = some s ∧ d.sortOf b = some t := by
  rw [sortsOf_cons]
  constructor
  · rintro ⟨s', ss', h1, h2, he⟩
    obtain ⟨s'', ss'', h3, h4, rfl⟩ := sortsOf_cons.mp h2
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨s, [t], h1, sortsOf_cons.mpr ⟨t, [], h2, sortsOf_nil, rfl⟩, rfl⟩

theorem sortsOf1 {d : Semantics} {a : GroundTerm} {s : Srt} : d.sortsOf [a] = some [s] ↔ d.sortOf a = some s := by
  rw [sortsOf_cons]
  constructor
  · rintro ⟨s', ss', h1, h2, he⟩
    rw [sortsOf_nil] at h2
    cases h2
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact h1
  · intro h1
    exact ⟨s, [], h1, sortsOf_nil, rfl⟩

theorem sortsOf3 {d : Semantics} {a b x : GroundTerm} {s t u : Srt} :
    d.sortsOf [a, b, x] = some [s, t, u] ↔ d.sortOf a = some s ∧ d.sortOf b = some t ∧ d.sortOf x = some u := by
  rw [sortsOf_cons]
  constructor
  · rintro ⟨s', ss', h1, h2, he⟩
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨h1, sortsOf2.mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨s, [t, u], h1, sortsOf2.mpr h2, rfl⟩

theorem bytesOfLen_sorted (H : HookParams) {k : Int} {j i e v : GroundTerm} (hj : (cH H).sortOf j = some Srt.int)
    (hi : (cH H).sortOf i = some Srt.int) (he : (cH H).sortOf e = some Srt.endianness)
    (hv : bytesOfLen H k j i e = some v) : (cH H).sortOf v = some Srt.bytes := by
  unfold bytesOfLen at hv
  obtain ⟨l, hl, hv⟩ := Option.bind_eq_some_iff.mp hv
  have hls := hv_sorted (coreOKH H) sigs_bytes.1 (sortsOf1.mpr hj) hl
  obtain ⟨a, ha, hv⟩ := Option.bind_eq_some_iff.mp hv
  have has := hv_sorted (coreOKH H) sigs_bytes.2.1 (sortsOf2.mpr ⟨hls, sortOf_int k⟩) ha
  obtain ⟨n, hn, hv⟩ := Option.bind_eq_some_iff.mp hv
  have hns := hv_sorted (coreOKH H) sigs_bytes.2.2.1 (sortsOf2.mpr ⟨has, sortOf_int 8⟩) hn
  exact hv_sorted (coreOKH H) sigs_bytes.2.2.2.1 (sortsOf3.mpr ⟨hns, hi, he⟩) hv

theorem notG_sorted {i v : GroundTerm} (hv : notG [i] = some v) {d : Semantics} : d.sortOf v = some Srt.int := by
  simp only [notG, Option.map_eq_some_iff] at hv
  obtain ⟨x, -, rfl⟩ := hv
  exact sortOf_int _

theorem noLenG_sorted (H : HookParams) {i e s v : GroundTerm} (hi : (cH H).sortOf i = some Srt.int)
    (he : (cH H).sortOf e = some Srt.endianness) (hv : noLenG H i e s = some v) : (cH H).sortOf v = some Srt.bytes := by
  have hE : ∀ {w}, (cH H).hv bytesEmpty [] = some w → (cH H).sortOf w = some Srt.bytes := fun hw =>
    hv_sorted (coreOKH H) sigs_bytes.2.2.2.2 sortsOf_nil hw
  unfold noLenG at hv
  split at hv
  · cases hv
  · split at hv
    · exact hE hv
    · split at hv
      · split at hv
        · exact bytesOfLen_sorted H hi hi he hv
        · split at hv
          · exact hv_sorted (coreOKH H) sigs_bytes.2.2.2.1 (sortsOf3.mpr ⟨sortOf_int 1, sortOf_int (-1), he⟩) hv
          · obtain ⟨j, hj, hv⟩ := Option.bind_eq_some_iff.mp hv
            exact bytesOfLen_sorted H (notG_sorted hj) hi he hv
      · split at hv
        · exact bytesOfLen_sorted H hi hi he hv
        · exact hE hv

/-- **`G`'s values at values of a lacked symbol's argument sorts are of its result sort.** -/
theorem G_sorted (H : HookParams) : ∀ k ∈ lacked, ∀ ws, (cH H).sortsOf ws = some k.args → ∀ v,
    G H k.name ws = some v → (cH H).sortOf v = some k.result := by
  intro k hk ws hws v hv
  simp only [lacked, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · -- dividesInt
    obtain ⟨a, b, rfl⟩ : ∃ a b, ws = [a, b] := by
      match ws, hws with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    obtain ⟨ha, hb⟩ := sortsOf2.mp hws
    simp only [G, dividesSig, ite_true] at hv
    obtain ⟨r, hr, hv⟩ := Option.bind_eq_some_iff.mp hv
    have hrs := hv_sorted (coreOKH H) sigs_hook.1 (sortsOf2.mpr ⟨hb, ha⟩) hr
    exact hv_sorted (coreOKH H) sigs_hook.2.1 (sortsOf2.mpr ⟨hrs, sortOf_int 0⟩) hv
  · -- ~Int
    obtain ⟨i, rfl⟩ : ∃ i, ws = [i] := by
      match ws, hws with
      | [i], _ => exact ⟨i, rfl⟩
    rw [show G H notSig.name [i] = notG [i] from rfl] at hv
    exact notG_sorted hv
  · -- Int2BytesNoLen
    obtain ⟨i, e, s, rfl⟩ : ∃ i e s, ws = [i, e, s] := by
      match ws, hws with
      | [i, e, s], _ => exact ⟨i, e, s, rfl⟩
    obtain ⟨hi, he, -⟩ := sortsOf3.mp hws
    rw [show G H noLenSig.name [i, e, s] = noLenG H i e s from rfl] at hv
    exact noLenG_sorted H hi he hv
  · -- rootFloat
    obtain ⟨x, n, rfl⟩ : ∃ x n, ws = [x, n] := by
      match ws, hws with
      | [x, n], _ => exact ⟨x, n, rfl⟩
    obtain ⟨hx, -⟩ := sortsOf2.mp hws
    rw [show G H rootSig.name [x, n] = (if n = twoV then (cH H).hv floatSqrt [x] else none) from rfl] at hv
    split at hv
    · exact hv_sorted (coreOKH H) sigs_hook.2.2 (sortsOf1.mpr hx) hv
    · cases hv

theorem ctor_facts : ((cH default).symName signedBytes = "LblsignedBytes" ∧ iteSort? "LblsignedBytes" = none) ∧
    ((cH default).symName unsignedBytes = "LblunsignedBytes" ∧ iteSort? "LblunsignedBytes" = none) ∧
    c.sortOf (.ctor signedBytes []) = some Srt.signedness ∧ c.sortOf (.ctor unsignedBytes []) = some Srt.signedness := by
  decide +kernel

/-- **Signedness's constructors denote their values in every interpretation.** -/
theorem ctorDen (H : HookParams) {M : Type} (I : Interpretation KoreAML.Sym M) : LackedDen (cH H) ctorsL (G H) I := by
  intro k hk ws hws
  have hws0 : ws = [] := by
    match ws, hws with
    | [], _ => rfl
    | w :: ws', h =>
      simp only [ctorsL, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;>
      · obtain ⟨_, _, -, -, he⟩ := sortsOf_cons.mp h
        cases he
  subst hws0
  have hG : G H k.name [] = some (.ctor k.name []) := by
    simp only [ctorsL, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> simp (config := { decide := true }) [G]
  have hite : iteSort? ((cH H).symName k.name) = none := by
    simp only [ctorsL, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact ctor_facts.1.1 ▸ ctor_facts.1.2
    · exact ctor_facts.2.1.1 ▸ ctor_facts.2.1.2
  refine ⟨fun e m => ?_, fun v hv => ?_⟩
  · rw [hG, GenEqs.symApp_den hite []]
    exact GenEqs.ctor_den k.name .nil m
  · rw [hG] at hv
    cases hv
    rw [sortOfH]
    simp only [ctorsL, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact ctor_facts.2.2.1
    · exact ctor_facts.2.2.2

/-! ## The `functional` sentences: `G` has a value at every argument list of the sorts -/

theorem not_total (H : HookParams) : ∀ ws, (cH H).sortsOf ws = some notSig.args → ∃ v, G H notSig.name ws = some v := by
  intro ws hws
  obtain ⟨i, rfl⟩ : ∃ i, ws = [i] := by
    have hl := Faithful.sortsOf_length hws
    match ws, hl with
    | [i], _ => exact ⟨i, rfl⟩
    | [], h => simp [notSig] at h
    | _ :: _ :: _, h => simp [notSig] at h
  obtain ⟨x, rfl⟩ := shape_int (shapesOKH H) (sortsOf1.mp hws)
  exact ⟨int (-x - 1), rfl⟩

theorem noLen_total (H : HookParams) : ∀ ws, (cH H).sortsOf ws = some noLenSig.args →
    ∃ v, G H noLenSig.name ws = some v := by
  intro ws hws
  obtain ⟨i, e, s, rfl⟩ : ∃ i e s, ws = [i, e, s] := by
    have hl := Faithful.sortsOf_length hws
    match ws, hl with
    | [i, e, s], _ => exact ⟨i, e, s, rfl⟩
    | [], h => simp [noLenSig] at h
    | [_], h => simp [noLenSig] at h
    | [_, _], h => simp [noLenSig] at h
    | _ :: _ :: _ :: _ :: _, h => simp [noLenSig] at h
  obtain ⟨hi, he, -⟩ := sortsOf3.mp hws
  obtain ⟨x, rfl⟩ := shape_int (shapesOKH H) hi
  have hE := shape_endian (shapesOKH H) he
  rw [show G H noLenSig.name [int x, e, s] = noLenG H (int x) e s from rfl]
  unfold noLenG
  rw [asInt_int]
  dsimp only
  split
  · exact ⟨_, hvEmpty⟩
  · split
    · split
      · exact bytesOfLen_some H (by decide) (by assumption) x hE
      · split
        · rename_i h
          obtain ⟨v, hv⟩ := hvI2B (d := cH H) (n := 1) (by decide) (-1) hE
          exact ⟨v, hv⟩
        · rename_i h0 h1 h2
          obtain ⟨v, hv⟩ := bytesOfLen_some H (k := 9) (y := -x - 1) (by decide) (by omega) x hE
          exact ⟨v, by simp only [notG, asInt_int, Option.map_some, Option.bind_some]; exact hv⟩
    · split
      · exact bytesOfLen_some H (by decide) (by assumption) x hE
      · exact ⟨_, hvEmpty⟩

/-! ## The model -/

theorem lacked_ok (H : HookParams) : ∀ k ∈ lacked, sigNamed (cH H) lacked ((cH H).symName k.name) = some k ∧
    lackedNameB (cH H) ((cH H).symName k.name) = true ∧ GenEqs.unresolvedB (cH H) ((cH H).symName k.name) = true ∧
    iteSort? ((cH H).symName k.name) = none := by
  intro k hk
  have h := List.all_eq_true.mp lacked_names k hk
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
  exact ⟨h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- **For every H, one model of `Γc ∪ Γstep` of `c.withHooks H`, whose steps at configurations are
`Step`'s, in which the library's sentences of the four symbols Γ lacks hold at values**: 274
(`dividesInt`, shape s3), 380 (`rootFloat` in `sqrtFloat`'s equation, shape s5), the five equations
228 to 232 of `Int2BytesNoLen` and the `functional` sentences 45 (`Int2BytesNoLen`) and 176 (`~Int`)
(shape s4), each as the text's translation writes it, at every valuation that sends its free
element variables to values. -/
theorem expansion (H : HookParams) :
    ∃ I : Interpretation KoreAML.Sym Faithful.Model.Elem,
      (I ⊧ᴵP (Γc (cH H) ∪ Γstep (cH H))) ∧
      (∀ x y : Config (cH H), Step (cH H) x y ↔ ¬ (I ⊧ᴵ (den (cH H) x.val ⇒ ∼ KoreAML.sNext (den (cH H) y.val)))) ∧
      (∀ e, AtValues (cH H) I e U.ax274.ax → ∀ m, (trS U.ax274).pat.interpret I e m) ∧
      (∀ e, AtValues (cH H) I e U.ax380.ax → ∀ m, (trS U.ax380).pat.interpret I e m) ∧
      (∀ e, AtValues (cH H) I e U.ax228.ax → ∀ m, (trS U.ax228).pat.interpret I e m) ∧
      (∀ e, AtValues (cH H) I e U.ax229.ax → ∀ m, (trS U.ax229).pat.interpret I e m) ∧
      (∀ e, AtValues (cH H) I e U.ax230.ax → ∀ m, (trS U.ax230).pat.interpret I e m) ∧
      (∀ e, AtValues (cH H) I e U.ax231.ax → ∀ m, (trS U.ax231).pat.interpret I e m) ∧
      (∀ e, AtValues (cH H) I e U.ax232.ax → ∀ m, (trS U.ax232).pat.interpret I e m) ∧
      (∀ e, AtValues (cH H) I e U.ax45.ax → ∀ m, (trS U.ax45).pat.interpret I e m) ∧
      (∀ e, AtValues (cH H) I e U.ax176.ax → ∀ m, (trS U.ax176).pat.interpret I e m) := by
  obtain ⟨I, hsat, hstep, hL⟩ := model_lacked (cH H) (coreOKH H) (fnHypH H) lacked (G H) (lacked_ok H) (G_sorted H)
  have hΓ : I ⊧ᴵP Γ (cH H) := fun φ hφ => hsat φ (Or.inl (Or.inl hφ))
  have hLs : LackedDen (cH H) ls (G H) I := fun k hk =>
    (List.mem_append.mp hk).elim (hL k) (ctorDen H I k)
  have heq : ∀ (E : FnEqn) (ad : AxiomDecl), E.HoldsLk (cH H) (G H) →
      (ad.ax.pattern = E.patR ∧ ad.ax.sortVars = [KoreAML.Rv] ∧ E.regular = true ∧ E.typedLk c.sortOf ls = true ∧
        (trS ad).pat = (trAxiom [] [] ad).pat) →
      ∀ e, AtValues (cH H) I e ad.ax → ∀ m, (trS ad).pat.interpret I e m := by
    intro E ad hE ⟨hp, hsv, hr, ht, htr⟩
    rw [htr]
    exact FnEqn.entailedLk_reg (coreOKH H) hΓ hLs E hr (by rw [sortOfH]; exact ht) hE ad hp hsv
  obtain ⟨p45, sv45, r45, tr45, p176, sv176, r176, tr176, k45, k176⟩ := fun_text
  refine ⟨I, hsat, hstep, ?_, ?_, heq e228 U.ax228 (holds228 H) e228_text, heq e229 U.ax229 (holds229 H) e229_text,
    heq e230 U.ax230 (holds230 H) e230_text, heq e231 U.ax231 (holds231 H) e231_text,
    heq e232 U.ax232 (holds232 H) e232_text, ?_, ?_⟩
  · obtain ⟨hp, hsv, hr, ht, htr⟩ := e274_text
    rw [htr]
    exact FnEqn.entailedLk_reg (coreOKH H) hΓ hLs e274 hr (by rw [sortOfH]; exact ht) (holds274 H) U.ax274 hp hsv
  · obtain ⟨hp, hsv, hr, ht, htr⟩ := e380_text
    rw [htr]
    exact FnEqn.entailedLk_reg (coreOKH H) hΓ hLs e380 hr (by rw [sortOfH]; exact ht) (holds380 H) U.ax380 hp hsv
  · rw [tr45]
    exact functionalLk (coreOKH H) hΓ hLs isHook_facts.2.2.2.1 k45 (noLen_total H) r45 U.ax45 p45 sv45
  · rw [tr176]
    exact functionalLk (coreOKH H) hΓ hLs isHook_facts.2.2.1 k176 (not_total H) r176 U.ax176 p176 sv176

end KCore.LibParamExpandFlt

#check @KCore.TieLibParam.expand_lacked
#check @KCore.TieLibParam.agree_updAt

/-- info: 'KCore.LibParamExpandFlt.expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibParamExpandFlt.expansion
/-- info: 'KCore.TieLibParam.expand_lacked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieLibParam.expand_lacked
/-- info: 'KCore.TieLibParam.agree_updAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieLibParam.agree_updAt
