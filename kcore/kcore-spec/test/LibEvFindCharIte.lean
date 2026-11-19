/-
  STRING-COMMON's equation of `findChar` (domains.md 1891), axiom 237 of the text of the fixture
  e6-ite-int (`f2-examples/e6ite.kompile.kore`), entailed at values for every H meeting
  `Semantics.findCharEq`. Run from the package root: `lake env lean -j1 test/LibEvFindCharIte.lean`.

  1891: `findChar(S1, S2, I) => #if findString(S1, substrString(S2, 0, 1), I) ==Int -1 #then
  findChar(S1, substrString(S2, 1, lengthString(S2)), I) #else #if findChar(S1, substrString(S2, 1,
  lengthString(S2)), I) ==Int -1 #then findString(S1, substrString(S2, 0, 1), I) #else
  minInt(findString(S1, substrString(S2, 0, 1), I), findChar(S1, substrString(S2, 1,
  lengthString(S2)), I)) #fi #fi requires S2 =/=String ""`.

  On this text `#if` at Int is the reading's parameter symbol `ite{Int}` (`iteInt`, 386, implemented
  by `kIte`; test/IteIntParam.lean `params_ite`), so its value at a Bool literal is the second or
  third argument (`Semantics.paramVal`, `paramVal_ite`); every other head of the equation is an
  interpreted hooked symbol.
  - `E237`: the equation in the function form over terms applying the parameter symbol
    (`LibEv.FnEqn`, `LibEv.koreP`); `pattern237`: axiom 237's pattern is its pattern.
  - `holds237`: its sides have the same value (`LibEv.valP`) at every substitution meeting its
    `requires`, for every H meeting `findCharEq`. Where I is a position of S1 both sides are `hook`'s:
    the first position from I of one of S2's characters is the first of its first character or of the
    others, −1 counting as none (`lfc_firstOr_or`); elsewhere `findChar` is at a silent point, where
    `findCharEq` is the sentence.
  - `ev237`: entailed at values for every H meeting `findCharEq` (`LibEv.FnEqn.entailedP`);
    `ev237_lib`: `HookParams.lib` meets it (`findCharEq_lib`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvFindCharIte

open KCore ML Faithful KoreAML LibEv

kore_term kore from "f2-examples/e6ite.kompile.kore"
definition_of defn from "f2-examples/e6ite.kompile.kore"
user_axioms U from "f2-examples/e6ite.kompile.kore" module "E6-ITE-INT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The parameter symbol `ite{Int}`. -/
abbrev iteInt : Sym := 386

theorem iteInt_name : c.symName iteInt = Parse.iteName "Int" := by decide +kernel

kernel_rfl lookupIte : ∀ H : HookParams,
  ((cH H).lookupParam iteInt).map (fun k => (k.impl, k.sig.result)) = some (some kIte, Srt.int)

/-! ## The equation -/

/-- `findString(S1, substrString(S2, 0, 1), I)`. -/
def tFs : Term := .app stringFind [.var 0, .app stringSubstr [.var 1, intT 0, intT 1], .var 2]

/-- `findChar(S1, substrString(S2, 1, lengthString(S2)), I)`. -/
def tFc : Term := .app stringFindChar [.var 0, .app stringSubstr [.var 1, intT 1, .app stringLength [.var 1]], .var 2]

/-- 1891 in the function form. -/
def E237 : FnEqn :=
  { vars := [("VarS1", Srt.string), ("VarS2", Srt.string), ("VarI", Srt.int)], f := stringFindChar,
    pats := [(Srt.string, .var 0, none), (Srt.string, .var 1, none), (Srt.int, .var 2, none)],
    s := Srt.int, req := some (.app stringNe [.var 1, stT ""]),
    rhs := .app iteInt [.app intEq [tFs, intT (-1)], tFc,
      .app iteInt [.app intEq [tFc, intT (-1)], tFs, .app intMin [tFs, tFc]]] }

kernel_rfl pattern237 : ∀ H : HookParams, U.ax237.ax.pattern = E237.patternP (cH H)
kernel_rfl typed237 : ∀ H : HookParams, E237.typedP (cH H) = true

theorem sortVars237 : U.ax237.ax.sortVars = [KoreAML.Rv] := by decide +kernel

kernel_rfl vkey_withHooks : ∀ (H : HookParams) (vars : Vars) (i : Nat), vkey (cH H) vars i = vkey c vars i

theorem free237 : ∀ i, i < E237.av.length → vkey c E237.av i ∈ KoreAML.freeOf [] U.ax237.ax.pattern := by
  decide +kernel

/-! ## Γ's values of the heads -/

theorem appValP_hookLfc {d : Semantics} {f : Sym} (h : (lookupSig hookSigs f).isSome = true) :
    appValP d f = d.hv f := by
  funext ws
  unfold appValP
  cases hl : lookupSig hookSigs f with
  | none => rw [hl] at h; cases h
  | some _ => rfl

kernel_rfl appValIte' : ∀ (H : HookParams) (ws : List GroundTerm),
  appValP (cH H) iteInt ws = (cH H).paramVal iteInt ws

theorem appValIte (H : HookParams) : appValP (cH H) iteInt = (cH H).paramVal iteInt := funext (appValIte' H)

theorem sigFind : lookupSig hookSigs stringFind = some ⟨stringFind, [Srt.string, Srt.string, Srt.int], Srt.int⟩ := by
  decide +kernel
theorem sigFindChar :
    lookupSig hookSigs stringFindChar = some ⟨stringFindChar, [Srt.string, Srt.string, Srt.int], Srt.int⟩ := by
  decide +kernel

theorem hkF : (lookupSig hookSigs stringFind).isSome = true := by decide +kernel
theorem hkFC : (lookupSig hookSigs stringFindChar).isSome = true := by decide +kernel
theorem hkS : (lookupSig hookSigs stringSubstr).isSome = true := by decide +kernel
theorem hkL : (lookupSig hookSigs stringLength).isSome = true := by decide +kernel
theorem hkN : (lookupSig hookSigs stringNe).isSome = true := by decide +kernel
theorem hkE : (lookupSig hookSigs intEq).isSome = true := by decide +kernel
theorem hkM : (lookupSig hookSigs intMin).isSome = true := by decide +kernel

/-- `ite{Int}` at a Bool literal and two Int literals. -/
theorem pvIte (H : HookParams) (b : Bool) (x y : Int) :
    (cH H).paramVal iteInt [bool b, int x, int y] = some (int (if b then x else y)) := by
  have hl := lookupIte H
  cases hk : (cH H).lookupParam iteInt with
  | none => rw [hk] at hl; cases hl
  | some k =>
    rw [hk] at hl
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
    have hz : (cH H).sortOf (if b then int x else int y) = some k.sig.result := by
      rw [hl.2]; cases b <;> exact sortOf_int _
    have := paramVal_ite (c := cH H) hk hl.1 b hz
    cases b <;> simpa using this

/-- `kIte` at a Bool literal. -/
theorem hvKIte (H : HookParams) (b : Bool) (x y : Int) :
    (cH H).hv kIte [bool b, int x, int y] = some (int (if b then x else y)) := by
  rw [hv_of_value (show hook kIte [bool b, int x, int y] = some (some (if b then int x else int y)) from rfl)]
  cases b <;> rfl

/-- A value of `findString` or `findChar` at three arguments of their sorts is an Int literal. -/
theorem hvIntLfc (H : HookParams) {f : Sym} (hf : lookupSig hookSigs f = some ⟨f, [Srt.string, Srt.string, Srt.int], Srt.int⟩)
    {ws : List GroundTerm} (hws : (cH H).sortsOf ws = some [Srt.string, Srt.string, Srt.int]) :
    (cH H).hv f ws = none ∨ ∃ n, (cH H).hv f ws = some (int n) := by
  cases hv : (cH H).hv f ws with
  | none => exact Or.inl rfl
  | some v =>
    right
    have hr : (cH H).hookRes f ws = some (some v) := by
      unfold Semantics.hv at hv
      exact Option.join_eq_some_iff.mp hv
    have hs := hookRes_sorted (fun _ => rangeBelow_of_core (coreOKH H)) hf hws hr
    obtain ⟨n, rfl⟩ := shape_int (shapesOKH H) hs
    exact ⟨n, rfl⟩

/-! ## The first position meeting a test -/

/-- `ite`'s combination of two first positions, −1 counting as none: the other where one is −1,
else the lesser. -/
def gLfc (x y : Int) : Int := if x = -1 then y else if y = -1 then x else min x y

theorem lfc_firstOr_snoc (l : List Nat) (n : Nat) :
    KStr.firstOr (l ++ [n]) = if KStr.firstOr l = -1 then (n : Int) else KStr.firstOr l := by
  cases l with
  | nil => simp [KStr.firstOr]
  | cons p _ =>
    simp only [List.cons_append, KStr.firstOr]
    have : ((p : Int) = -1) = False := by simp only [eq_iff_iff, iff_false]; omega
    simp [this]

theorem lfc_firstOr_bound (P : Nat → Bool) : ∀ n : Nat,
    KStr.firstOr ((List.range n).filter P) = -1 ∨
      (0 ≤ KStr.firstOr ((List.range n).filter P) ∧ KStr.firstOr ((List.range n).filter P) < n)
  | 0 => by simp [KStr.firstOr]
  | n + 1 => by
    rw [st_filter_range_succ]
    have ih := lfc_firstOr_bound P n
    cases P n
    · simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]; omega
    · simp only [↓reduceIte, lfc_firstOr_snoc]; split <;> omega

set_option linter.unusedSimpArgs false in
/-- **The first position meeting `P` or `Q`** is `gLfc` of the first meeting each. -/
theorem lfc_firstOr_or (P Q : Nat → Bool) : ∀ n : Nat,
    KStr.firstOr ((List.range n).filter fun p => P p || Q p) =
      gLfc (KStr.firstOr ((List.range n).filter P)) (KStr.firstOr ((List.range n).filter Q))
  | 0 => by simp [KStr.firstOr, gLfc]
  | n + 1 => by
    simp only [st_filter_range_succ]
    have bP := lfc_firstOr_bound P n
    have bQ := lfc_firstOr_bound Q n
    have ih := lfc_firstOr_or P Q n
    unfold gLfc at ih ⊢
    cases hp : P n <;> cases hq : Q n <;>
      simp only [hp, hq, Bool.or_false, Bool.false_or, Bool.or_true, Bool.false_eq_true, ↓reduceIte,
        List.append_nil, lfc_firstOr_snoc, ih] <;>
      generalize KStr.firstOr (List.filter P (List.range n)) = x at bP ⊢ <;>
      generalize KStr.firstOr (List.filter Q (List.range n)) = y at bQ ⊢ <;>
      (repeat' split) <;> omega

/-- `findString` of one character at a position: the first position from there of that character. -/
theorem lfc_find1 (s : List Char) (ch : Char) (i : Int) (hp : KStr.isPos s i = true) :
    KStr.find s [ch] i =
      some (KStr.firstOr ((List.range s.length).filter fun (p : Nat) => decide (i ≤ (p : Int)) && KStr.charIn s [ch] p)) := by
  unfold KStr.find KStr.positions
  simp only [hp, ↓reduceIte, st_filter_range_succ]
  have hlast : KStr.occursAt [ch] s s.length = false := by simp [KStr.occursAt]
  simp only [hlast, Bool.and_false, Bool.false_eq_true, ↓reduceIte, List.append_nil, Option.some.injEq]
  congr 1
  refine List.filter_congr fun p hp' => ?_
  have hpl : p < s.length := List.mem_range.mp hp'
  simp only [KStr.occursAt, KStr.charIn, List.drop_eq_getElem_cons hpl, List.getElem?_eq_getElem hpl,
    List.isPrefixOf, Option.any_some, List.contains_cons, List.contains_nil, Bool.or_false, Bool.and_true]
  cases h : (ch == s[p]) <;> cases h' : (s[p] == ch) <;> simp_all [beq_iff_eq]

/-- `findChar` at a position: the first position from there whose character is one of `cs` (−1 for
none, so also at the empty `cs`). -/
theorem lfc_fc (s cs : List Char) (i : Int) (hp : KStr.isPos s i = true) :
    KStr.findChar s cs i =
      some (KStr.firstOr ((List.range s.length).filter fun (p : Nat) => decide (i ≤ (p : Int)) && KStr.charIn s cs p)) := by
  unfold KStr.findChar
  cases cs with
  | nil =>
    have : ((List.range s.length).filter fun (p : Nat) => decide (i ≤ (p : Int)) && KStr.charIn s [] p) = [] :=
      List.filter_eq_nil_iff.mpr fun p _ => by
        simp only [KStr.charIn, Bool.and_eq_true, decide_eq_true_eq, not_and]
        intro _; generalize s[p]? = o; cases o <;> simp
    rw [this]; rfl
  | cons ch t => simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, hp]

section
variable {d : Semantics}

theorem lfc_hv_find (x y : List Char) (i v : Int) (h : KStr.find x y i = some v) :
    d.hv stringFind [strV x, strV y, int i] = some (int v) := by
  refine hv_of_value ?_
  show some ((asStr (strV x)).bind fun a => (asStr (strV y)).bind fun b => (asInt (int i)).bind fun j =>
    (KStr.find a b j).map int) = _
  rw [st_asStr, st_asStr]
  show some ((KStr.find x y i).map int) = _
  rw [h]; rfl

theorem lfc_hv_findChar (x y : List Char) (i v : Int) (h : KStr.findChar x y i = some v) :
    d.hv stringFindChar [strV x, strV y, int i] = some (int v) := by
  refine hv_of_value ?_
  show some ((asStr (strV x)).bind fun a => (asStr (strV y)).bind fun b => (asInt (int i)).bind fun j =>
    (KStr.findChar a b j).map int) = _
  rw [st_asStr, st_asStr]
  show some ((KStr.findChar x y i).map int) = _
  rw [h]; rfl

theorem lfc_hook_findChar_none (x y : List Char) (i : Int) (h : KStr.findChar x y i = none) :
    hook stringFindChar [strV x, strV y, int i] = some none := by
  show some ((asStr (strV x)).bind fun a => (asStr (strV y)).bind fun b => (asInt (int i)).bind fun j =>
    (KStr.findChar a b j).map int) = _
  rw [st_asStr, st_asStr]
  show some ((KStr.findChar x y i).map int) = _
  rw [h]; rfl

end

/-! ## The sides' values -/

theorem holds237 (H : HookParams) (hc : (cH H).findCharEq) : E237.HoldsP (cH H) := by
  intro σ hσ hreq hm
  have hs := shapesOKH H
  obtain ⟨a, ha, sa⟩ := st_string_at' hs hσ 0 (n := "VarS1") rfl
  obtain ⟨b, hb, sb⟩ := st_string_at' hs hσ 1 (n := "VarS2") rfl
  obtain ⟨vi, hvi, si⟩ := hσ 2 ("VarI", Srt.int) rfl
  obtain ⟨i, rfl⟩ := shape_int hs si
  obtain ⟨h3, -, h4, -, h5, -, -⟩ := hm
  rw [fq_valP_var] at h3 h4 h5
  have h3' : σ.lookup 3 = some (foS a) := h3.symm.trans ha
  have h4' : σ.lookup 4 = some (foS b) := h4.symm.trans hb
  have h5' : σ.lookup 5 = some (int i) := h5.symm.trans hvi
  have hq := hreq _ rfl
  simp only [valP, valPList, allSome, hb, stT, Option.bind_some, Option.map_some,
    appValP_hookLfc hkN] at hq
  have hne : (cH H).hv stringNe [foS b, strV []] = some (bool true) := hq
  have hq2 := (st_hv_ne (c := cH H) b "").symm.trans hq
  obtain ⟨ch, t, hbe⟩ : ∃ ch t, b.toList = ch :: t := by
    cases hbl : b.toList with
    | nil => rw [hbl] at hq2; exact absurd (fq_bool_inj (Option.some.inj hq2)) (by decide)
    | cons ch t => exact ⟨ch, t, rfl⟩
  have hA : σ.lookup 0 = some (strV a.toList) := by rw [st_foS_strV]; exact ha
  have hB : σ.lookup 1 = some (strV (ch :: t)) := by rw [← hbe, st_foS_strV]; exact hb
  have hl : valP (cH H) σ E237.lhs = (cH H).hv stringFindChar [strV a.toList, strV (ch :: t), int i] := by
    show valP (cH H) σ (.app stringFindChar [.var 3, .var 4, .var 5]) = _
    simp only [valP, valPList, allSome, h3', h4', h5', Option.bind_some, Option.map_some,
      appValP_hookLfc hkFC]
    rw [← hbe, st_foS_strV, st_foS_strV]
  have hsub0 : (cH H).hv stringSubstr [strV (ch :: t), int 0, int 1] = some (strV [ch]) :=
    st_hv_substr_pre (ch :: t) 1 (by simp)
  have hsub1 : (cH H).hv stringSubstr [strV (ch :: t), int 1, int (ch :: t).length] = some (strV t) :=
    st_hv_substr_suf (ch :: t) 1 (by simp)
  have hsA : (cH H).sortsOf [strV a.toList, strV [ch], int i] = some [Srt.string, Srt.string, Srt.int] :=
    sortsOf_cons.mpr ⟨_, _, sortOf_strV _, sortsOf_cons.mpr ⟨_, _, sortOf_strV _,
      sortsOf_cons.mpr ⟨_, _, sortOf_int _, sortsOf_nil, rfl⟩, rfl⟩, rfl⟩
  have hsB : (cH H).sortsOf [strV a.toList, strV t, int i] = some [Srt.string, Srt.string, Srt.int] :=
    sortsOf_cons.mpr ⟨_, _, sortOf_strV _, sortsOf_cons.mpr ⟨_, _, sortOf_strV _,
      sortsOf_cons.mpr ⟨_, _, sortOf_int _, sortsOf_nil, rfl⟩, rfl⟩, rfl⟩
  -- the right side from the values of the two searches
  have hr : ∀ A B : Option Int,
      (cH H).hv stringFind [strV a.toList, strV [ch], int i] = A.map int →
      (cH H).hv stringFindChar [strV a.toList, strV t, int i] = B.map int →
      valP (cH H) σ E237.rhs = (A.bind fun x => B.map fun y => int (gLfc x y)) := by
    intro A B hFA hFB
    show valP (cH H) σ (.app iteInt [.app intEq [tFs, intT (-1)], tFc,
      .app iteInt [.app intEq [tFc, intT (-1)], tFs, .app intMin [tFs, tFc]]]) = _
    simp only [tFs, tFc, valP, valPList, allSome, hA, hB, hvi, intT, dv_int, Option.bind_some, Option.map_some,
      appValP_hookLfc hkF, appValP_hookLfc hkFC, appValP_hookLfc hkS, appValP_hookLfc hkL,
      appValP_hookLfc hkE, appValP_hookLfc hkM, appValIte, hsub0, st_hv_length', hsub1, hFA, hFB]
    cases A with
    | none => simp
    | some x =>
      cases B with
      | none => simp
      | some y =>
        simp only [Option.map_some, Option.bind_some, fhv_intEq, fhv_intMin, pvIte, gLfc]
        congr 2
        by_cases hx : x = -1 <;> by_cases hy : y = -1 <;> simp [hx, hy]
  rw [hl]
  cases hpos : KStr.isPos a.toList i with
  | true =>
    rw [hr (some _) (some _) (lfc_hv_find _ _ _ _ (lfc_find1 a.toList ch i hpos)) (lfc_hv_findChar _ _ _ _ (lfc_fc a.toList t i hpos)),
      lfc_hv_findChar _ _ _ _ (lfc_fc _ _ _ hpos)]
    simp only [Option.bind_some, Option.map_some]
    rw [← lfc_firstOr_or]
    congr 4
    funext p
    rw [st_charIn_cons, Bool.and_or_distrib_left]
  | false =>
    have hnone : KStr.findChar a.toList (ch :: t) i = none := by simp [KStr.findChar, hpos]
    have hs3 : (cH H).sortsOf [strV a.toList, strV (ch :: t), int i] = some [Srt.string, Srt.string, Srt.int] :=
      sortsOf_cons.mpr ⟨_, _, sortOf_strV _, sortsOf_cons.mpr ⟨_, _, sortOf_strV _,
        sortsOf_cons.mpr ⟨_, _, sortOf_int _, sortsOf_nil, rfl⟩, rfl⟩, rfl⟩
    rw [hc _ _ _ hs3 (by rw [← hbe, st_foS_strV]; exact hne) (lfc_hook_findChar_none _ _ _ hnone)]
    simp only [hsub0, Option.bind_some, st_hv_length', hsub1]
    rcases hvIntLfc H sigFind hsA with hFA | ⟨x, hFA⟩ <;>
      rcases hvIntLfc H sigFindChar hsB with hFB | ⟨y, hFB⟩
    · rw [hr none none hFA hFB, hFA]; rfl
    · rw [hr none (some y) hFA hFB, hFA]; rfl
    · rw [hr (some x) none hFA hFB, hFA, hFB]; rfl
    · rw [hr (some x) (some y) hFA hFB, hFA, hFB]
      simp only [Option.bind_some, Option.map_some, fhv_intEq, fhv_intMin, hvKIte, gLfc]
      congr 2
      by_cases hx : x = -1 <;> by_cases hy : y = -1 <;> simp [hx, hy]

/-! ## Entailed at values -/

/-- **1891** `findChar(S1, S2, I) => #if … #fi requires S2 =/=String ""`, entailed at values for every
H meeting `findCharEq`. -/
theorem ev237 (H : HookParams) (hc : (cH H).findCharEq) : EntailsAtValues (cH H) U.ax237 (trS U.ax237).pat := by
  rw [(by decide +kernel : (trS U.ax237).pat = (trAxiom [] [] U.ax237).pat)]
  exact FnEqn.entailedP (coreOKH H) E237 (typed237 H) (holds237 H hc) U.ax237 (pattern237 H) sortVars237
    (fun i hi => by rw [vkey_withHooks]; exact free237 i hi)

/-- At `HookParams.lib`, which meets `findCharEq`. -/
theorem ev237_lib : EntailsAtValues (cH HookParams.lib) U.ax237 (trS U.ax237).pat :=
  ev237 HookParams.lib (findCharEq_lib c)

end KCore.LibEvFindCharIte

/-- info: 'KCore.LibEvFindCharIte.ev237' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFindCharIte.ev237
/-- info: 'KCore.LibEvFindCharIte.ev237_lib' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFindCharIte.ev237_lib
#print axioms KCore.LibEvFindCharIte.iteInt_name
