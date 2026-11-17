/-
  KCore, checked layer: STRING's and BYTES' library sentences over Γ's symbols, entailed at values
  (`EntailsAtValues`) in every semantics meeting `coreOK` whose String values are literals
  (`shapesOK`), for every interpretation, or for every interpretation meeting a named condition of
  `Semantics.libAdmitted` where the sentence reaches a silent point.

  The line numbers are those of domains.md in K 7.1.337 (STRING-COMMON, STRING-KORE,
  BYTES-SYMBOLIC-CEIL). Each sentence is stated once, over the registry's names.
  - Function form (`FnEqn`), for every H: `fnB2S` (1787, 1788 `Bool2String`), `fnS2B` (1793, 1794
    `String2Bool`), `fnNeStr` (1867 `=/=String`), `fnLeStr`, `fnGtStr`, `fnGeStr` (1887 to 1889),
    `fnCharNone` (1892, 1894: `findChar`, `rfindChar` at the empty set of characters),
    `fnCountNone` (1896), `fnRepFirst`, `fnRepFirstNone` (1901, 1904), `fnReplace` (1911).
  - Function form under a condition on H: `fnReplaceAll` (1917, `replaceAllEq`), `fnRfindChar`
    (1893, `rfindCharEq`). Off the silent points both sides are `hook`'s; at a silent point of the
    left side the condition is the sentence.
  - `strKEq` (1925): `S1 ==K S2 => S1 ==String S2` at K sequences of one injected String
    (`KSeqEq`).
  - `CeilEqn`, the form `#Ceil(t) => {req #Equals true}` over element variables, and `ceilPad`
    (2241, 2242: `padRightBytes`, `padLeftBytes`): the padding is defined exactly where the length
    is not negative and the value is a byte.
-/
import KcoreSpec.LibEvFnOwise
import KcoreSpec.LibEvBoolK
import KcoreSpec.LibEvPred
import KcoreSpec.LibEvSetVar

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-- A String literal as a term. -/
def stT (a : String) : Term := .dv Srt.string (.tok a)

section
variable {c : Semantics}

theorem st_hv_bool2String (b : Bool) : c.hv bool2String [bool b] = some (strV (boolRepr b).toList) :=
  hv_of_value rfl
theorem st_hv_string2Bool (b : Bool) : c.hv string2Bool [foS (boolRepr b)] = some (bool b) := by
  cases b <;> exact hv_of_value rfl
theorem st_hv_lt (a b : String) : c.hv stringLt [foS a, foS b] = some (bool (KStr.lexLt a.toList b.toList)) :=
  hv_of_value rfl
theorem st_hv_le (a b : String) : c.hv stringLe [foS a, foS b] = some (bool !(KStr.lexLt b.toList a.toList)) :=
  hv_of_value rfl
theorem st_hv_gt (a b : String) : c.hv stringGt [foS a, foS b] = some (bool (KStr.lexLt b.toList a.toList)) :=
  hv_of_value rfl
theorem st_hv_ge (a b : String) : c.hv stringGe [foS a, foS b] = some (bool !(KStr.lexLt a.toList b.toList)) :=
  hv_of_value rfl
theorem st_hv_eq (a b : String) : c.hv stringEq [foS a, foS b] = some (bool (a.toList == b.toList)) :=
  hv_of_value rfl
theorem st_hv_ne (a b : String) : c.hv stringNe [foS a, foS b] = some (bool (a.toList != b.toList)) :=
  hv_of_value rfl

end

/-- A substitution of values of the variables' sorts gives a String variable a String literal. -/
theorem st_string_at {c : Semantics} (hs : c.shapesOK = true) {vars : Vars} {σ : Subst}
    (hσ : ∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2)
    (i : Nat) {n : String} (hi : vars[i]? = some (n, Srt.string)) : ∃ a : String, σ.lookup i = some (foS a) := by
  obtain ⟨v, hv, hsv⟩ := hσ i _ hi
  obtain ⟨a, rfl⟩ := shape_string hs hsv
  exact ⟨a, hv⟩

/-- The value of a pattern variable that matches its argument variable `k`. -/
theorem st_arg {c : Semantics} {σ : Subst} {j k : Nat} {v : GroundTerm} (hm : val c σ (.var j) = σ.lookup k)
    (hj : σ.lookup j = some v) : σ.lookup k = some v := by
  rw [fq_val_var] at hm; exact hm.symm.trans hj

/-! ## 1787, 1788: `Bool2String(b) => "b"`; 1793, 1794: `String2Bool("b") => b` -/

def fnB2S (b : Bool) : FnEqn :=
  ⟨[], bool2String, [(Srt.bool, fqB b, none)], Srt.string, none, stT (boolRepr b)⟩

theorem fnB2S_holds {c : Semantics} (b : Bool) : (fnB2S b).Holds c := by
  intro σ _ _ hm
  obtain ⟨h0, -, -⟩ := hm
  have h0' : σ.lookup 0 = some (bool b) := h0.symm
  fq_eval [fnB2S, h0', st_hv_bool2String, stT]
  cases b <;> rfl

theorem fnB2S_ev {c : Semantics} (h : c.coreOK = true) (b : Bool) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = (fnB2S b).patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h (fnB2S b) (by cases b <;> decide) (by cases b <;> rfl) (fnB2S_holds b) ad hp hsv

def fnS2B (b : Bool) : FnEqn :=
  ⟨[], string2Bool, [(Srt.string, stT (boolRepr b), none)], Srt.bool, none, fqB b⟩

theorem fnS2B_holds {c : Semantics} (b : Bool) : (fnS2B b).Holds c := by
  intro σ _ _ hm
  obtain ⟨h0, -, -⟩ := hm
  have h0' : σ.lookup 0 = some (foS (boolRepr b)) := h0.symm
  fq_eval [fnS2B, h0', st_hv_string2Bool]

theorem fnS2B_ev {c : Semantics} (h : c.coreOK = true) (b : Bool) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = (fnS2B b).patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h (fnS2B b) (by cases b <;> decide) (by cases b <;> rfl) (fnS2B_holds b) ad hp hsv

/-! ## 1867, 1887 to 1889: `=/=String`, `<=String`, `>String`, `>=String` by `==String`, `<String` -/

/-- `f(S1, S2) => rhs` over two String variables. -/
def fnStr2 (f : Sym) (s : Srt) (rhs : Term) : FnEqn :=
  ⟨[("VarS1", Srt.string), ("VarS2", Srt.string)], f, [(Srt.string, .var 0, none), (Srt.string, .var 1, none)], s,
    none, rhs⟩

/-- 1867: `S1 =/=String S2 => notBool (S1 ==String S2)`. -/
def fnNeStr : FnEqn := fnStr2 stringNe Srt.bool (.app boolNot [.app stringEq [.var 0, .var 1]])
/-- 1887: `S1 <=String S2 => notBool (S2 <String S1)`. -/
def fnLeStr : FnEqn := fnStr2 stringLe Srt.bool (.app boolNot [.app stringLt [.var 1, .var 0]])
/-- 1888: `S1 >String S2 => S2 <String S1`. -/
def fnGtStr : FnEqn := fnStr2 stringGt Srt.bool (.app stringLt [.var 1, .var 0])
/-- 1889: `S1 >=String S2 => notBool (S1 <String S2)`. -/
def fnGeStr : FnEqn := fnStr2 stringGe Srt.bool (.app boolNot [.app stringLt [.var 0, .var 1]])

/-- Where both sides read only the values at the two String variables, each through its `hook`
value, the equation holds where they agree at every two Strings. -/
theorem fnStr2_holds {c : Semantics} (hs : c.shapesOK = true) (f : Sym) (s : Srt) (rhs : Term)
    (hag : ∀ σ a b, σ.lookup 0 = some (foS a) → σ.lookup 1 = some (foS b) →
      c.hv f [foS a, foS b] = val c σ rhs) : (fnStr2 f s rhs).Holds c := by
  intro σ hσ _ hm
  obtain ⟨a, ha⟩ := st_string_at hs hσ 0 (n := "VarS1") rfl
  obtain ⟨b, hb⟩ := st_string_at hs hσ 1 (n := "VarS2") rfl
  obtain ⟨h2, -, h3, -⟩ := hm
  have h2' : σ.lookup 2 = some (foS a) := st_arg h2 ha
  have h3' : σ.lookup 3 = some (foS b) := st_arg h3 hb
  have hl : val c σ (fnStr2 f s rhs).lhs = c.hv f [foS a, foS b] := by fq_eval [fnStr2, h2', h3']
  rw [hl, hag σ a b ha hb]; rfl

theorem fnNeStr_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnNeStr.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnNeStr (by decide) (by rfl)
    (fnStr2_holds hs _ _ _ fun σ a b ha hb => by
      simp only [val, valList, allSome, ha, hb, Option.bind_some, Option.map_some, st_hv_ne, st_hv_eq, fhv_boolNot]
      simp only [bne]) ad hp hsv

theorem fnLeStr_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnLeStr.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnLeStr (by decide) (by rfl)
    (fnStr2_holds hs _ _ _ fun σ a b ha hb => by
      simp only [val, valList, allSome, ha, hb, Option.bind_some, Option.map_some, st_hv_le, st_hv_lt, fhv_boolNot]) ad hp hsv

theorem fnGtStr_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnGtStr.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnGtStr (by decide) (by rfl)
    (fnStr2_holds hs _ _ _ fun σ a b ha hb => by
      simp only [val, valList, allSome, ha, hb, Option.bind_some, Option.map_some, st_hv_gt, st_hv_lt]) ad hp hsv

theorem fnGeStr_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnGeStr.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnGeStr (by decide) (by rfl)
    (fnStr2_holds hs _ _ _ fun σ a b ha hb => by
      simp only [val, valList, allSome, ha, hb, Option.bind_some, Option.map_some, st_hv_ge, st_hv_lt, fhv_boolNot]) ad hp hsv

/-! ## 1892, 1894: `findChar(_, "", _) => -1`, `rfindChar(_, "", _) => -1` -/

/-- `f(_Gen0, "", _Gen1) => -1`. -/
def fnCharNone (f : Sym) : FnEqn :=
  ⟨[("Var'Unds'Gen0", Srt.string), ("Var'Unds'Gen1", Srt.int)], f,
    [(Srt.string, .var 0, none), (Srt.string, stT "", none), (Srt.int, .var 1, none)], Srt.int, none, intT (-1)⟩

theorem fnCharNone_holds {c : Semantics} (hs : c.shapesOK = true) (f : Sym)
    (hf : ∀ a i, c.hv f [foS a, foS "", int i] = some (int (-1))) : (fnCharNone f).Holds c := by
  intro σ hσ _ hm
  obtain ⟨a, ha⟩ := st_string_at hs hσ 0 (n := "Var'Unds'Gen0") rfl
  obtain ⟨i, hi⟩ := int_at hs hσ 1 (n := "Var'Unds'Gen1") rfl
  obtain ⟨h2, -, h3, -, h4, -, -⟩ := hm
  have h2' : σ.lookup 2 = some (foS a) := st_arg h2 ha
  have h3' : σ.lookup 3 = some (foS "") := h3.symm
  have h4' : σ.lookup 4 = some (int i) := st_arg h4 hi
  fq_eval [fnCharNone, h2', h3', h4', hf]

theorem fnCharNone_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (rev : Bool)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = (fnCharNone (if rev then stringRfindChar else stringFindChar)).patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv]) : EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h _ (by cases rev <;> decide) (by cases rev <;> rfl)
    (fnCharNone_holds hs _ fun a i => by cases rev <;> exact hv_of_value rfl) ad hp hsv

/-! ## The first occurrence of a needle -/

/-- The positions at which `n` occurs in `s`, from the first. -/
def stOcc (s n : List Char) : List Nat := (KStr.positions s).filter (KStr.occursAt n s)

theorem st_filter0 (s n : List Char) :
    (KStr.positions s).filter (fun (p : Nat) => decide ((0 : Int) ≤ (p : Int)) && KStr.occursAt n s p) = stOcc s n := by
  unfold stOcc
  exact List.filter_congr fun p _ => by simp

theorem st_firstAt (s n : List Char) : KStr.firstAt s n = (stOcc s n).head? := rfl

/-- An occurrence lies within the string. -/
theorem st_occ_bound {s n : List Char} {p : Nat} (h : p ∈ stOcc s n) : p + n.length ≤ s.length := by
  unfold stOcc KStr.occursAt at h
  obtain ⟨hpos, hp⟩ := List.mem_filter.mp h
  have hp' : p < s.length + 1 := List.mem_range.mp hpos
  have := (List.isPrefixOf_iff_prefix.mp hp).length_le
  simp only [List.length_drop] at this
  omega

/-- The empty needle occurs at 0. -/
theorem st_occ_nil (s : List Char) : stOcc s [] = KStr.positions s := by
  unfold stOcc; exact List.filter_eq_self.mpr fun p _ => by simp [KStr.occursAt, List.isPrefixOf]

theorem st_firstOr_neg (l : List Nat) : KStr.firstOr l < 0 ↔ l = [] := by
  cases l with
  | nil => simp [KStr.firstOr]
  | cons p _ => simp only [KStr.firstOr, reduceCtorEq, iff_false]; omega

section
variable {c : Semantics}

theorem st_foS_strV (a : String) : strV a.toList = foS a := by unfold strV foS; rw [String.ofList_toList]
theorem st_strV_foS (cs : List Char) : strV cs = foS (String.ofList cs) := rfl

theorem st_hv_find0 (a b : String) :
    c.hv stringFind [foS a, foS b, int 0] = some (int (KStr.firstOr (stOcc a.toList b.toList))) := by
  rw [fo_hv_stringFind0, st_filter0]

theorem st_hv_length (a : String) : c.hv stringLength [foS a] = some (int a.toList.length) := hv_of_value rfl

theorem st_hv_concat (a b : String) : c.hv stringConcat [foS a, foS b] = some (strV (a.toList ++ b.toList)) :=
  hv_of_value rfl

theorem st_hv_substr (a : String) (i j : Int) (h1 : ¬ (0 < i ∧ i = j ∧ j < a.toList.length))
    (h2 : 0 ≤ i ∧ i ≤ j ∧ j ≤ a.toList.length) :
    c.hv stringSubstr [foS a, int i, int j] = some (strV ((a.toList.drop i.toNat).take (j - i).toNat)) := by
  refine hv_of_value ?_
  show some ((KStr.substrString a.toList i j).map strV) = _
  unfold KStr.substrString KStr.substr
  simp only [h1, h2, and_self, ↓reduceIte, Option.map_some]

theorem st_hv_replaceFirst (a b r : String) :
    c.hv stringReplaceFirst [foS a, foS b, foS r] = some (strV (KStr.replaceFirst a.toList b.toList r.toList)) :=
  hv_of_value rfl

end

/-- `findString(S, N, 0)`, a term over the variables `i`, `j`. -/
def stFind (i j : Nat) : Term := .app stringFind [.var i, .var j, intT 0]

/-! ## 1896: `countAllOccurrences(Source, ToCount) => 0 requires findString(Source, ToCount, 0) <Int 0` -/

def fnCountNone : FnEqn :=
  ⟨[("VarSource", Srt.string), ("VarToCount", Srt.string)], stringCountAll,
    [(Srt.string, .var 0, none), (Srt.string, .var 1, none)], Srt.int, some (.app intLt [stFind 0 1, intT 0]), intT 0⟩

theorem fnCountNone_holds {c : Semantics} (hs : c.shapesOK = true) : fnCountNone.Holds c := by
  intro σ hσ hreq hm
  obtain ⟨a, ha⟩ := st_string_at hs hσ 0 (n := "VarSource") rfl
  obtain ⟨b, hb⟩ := st_string_at hs hσ 1 (n := "VarToCount") rfl
  obtain ⟨h2, -, h3, -, -⟩ := hm
  have h2' : σ.lookup 2 = some (foS a) := st_arg h2 ha
  have h3' : σ.lookup 3 = some (foS b) := st_arg h3 hb
  have hq := hreq _ rfl
  simp only [stFind, val, valList, allSome, ha, hb, intT, dv_int, Option.bind_some, Option.map_some, st_hv_find0,
    hv_intLt, Option.some.injEq] at hq
  have hnil : stOcc a.toList b.toList = [] := (st_firstOr_neg _).mp (of_decide_eq_true (fq_bool_inj hq))
  have hb0 : b.toList ≠ [] := fun h0 => by
    rw [h0, st_occ_nil] at hnil
    simp [KStr.positions] at hnil
  have hcount : c.hv stringCountAll [foS a, foS b] = some (int 0) := by
    refine hv_of_value ?_
    show some ((KStr.countAll a.toList b.toList).map fun k => int k) = _
    unfold KStr.countAll
    have he : b.toList.isEmpty = false := by cases h : b.toList with | nil => exact absurd h hb0 | cons _ _ => rfl
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    cases a.toList.length with
    | zero => rfl
    | succ k => simp only [KStr.countFrom, st_firstAt, hnil, List.head?_nil]; rfl
  fq_eval [fnCountNone, h2', h3', hcount]

theorem fnCountNone_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnCountNone.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnCountNone (by decide) (by rfl) (fnCountNone_holds hs) ad hp hsv

/-! ## 1904: `replaceFirst(Source, ToReplace, _) => Source requires findString(Source, ToReplace, 0) <Int 0` -/

def fnRepFirstNone : FnEqn :=
  ⟨[("VarSource", Srt.string), ("VarToReplace", Srt.string), ("Var'Unds'Gen0", Srt.string)], stringReplaceFirst,
    [(Srt.string, .var 0, none), (Srt.string, .var 1, none), (Srt.string, .var 2, none)], Srt.string,
    some (.app intLt [stFind 0 1, intT 0]), .var 0⟩

theorem fnRepFirstNone_holds {c : Semantics} (hs : c.shapesOK = true) : fnRepFirstNone.Holds c := by
  intro σ hσ hreq hm
  obtain ⟨a, ha⟩ := st_string_at hs hσ 0 (n := "VarSource") rfl
  obtain ⟨b, hb⟩ := st_string_at hs hσ 1 (n := "VarToReplace") rfl
  obtain ⟨r, hr⟩ := st_string_at hs hσ 2 (n := "Var'Unds'Gen0") rfl
  obtain ⟨h3, -, h4, -, h5, -, -⟩ := hm
  have h3' : σ.lookup 3 = some (foS a) := st_arg h3 ha
  have h4' : σ.lookup 4 = some (foS b) := st_arg h4 hb
  have h5' : σ.lookup 5 = some (foS r) := st_arg h5 hr
  have hq := hreq _ rfl
  simp only [stFind, val, valList, allSome, ha, hb, intT, dv_int, Option.bind_some, Option.map_some, st_hv_find0,
    hv_intLt, Option.some.injEq] at hq
  have hnil : stOcc a.toList b.toList = [] := (st_firstOr_neg _).mp (of_decide_eq_true (fq_bool_inj hq))
  fq_eval [fnRepFirstNone, h3', h4', h5', ha, st_hv_replaceFirst]
  simp only [KStr.replaceFirst, st_firstAt, hnil, List.head?_nil, st_foS_strV]

theorem fnRepFirstNone_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnRepFirstNone.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnRepFirstNone (by decide) (by rfl) (fnRepFirstNone_holds hs) ad hp hsv

/-! ## 1901: `replaceFirst(S, N, R) => substrString(S, 0, findString(S, N, 0)) +String R +String
substrString(S, findString(S, N, 0) +Int lengthString(N), lengthString(S)) requires findString(S, N, 0) >=Int 0` -/

section
variable {c : Semantics}

theorem st_asStr (cs : List Char) : asStr (strV cs) = some cs := by
  simp [asStr, strV, String.toList_ofList]

theorem st_hv_concat' (x y : List Char) : c.hv stringConcat [strV x, strV y] = some (strV (x ++ y)) := by
  refine hv_of_value ?_
  show some ((asStr (strV x)).bind fun x => (asStr (strV y)).map fun y => strV (x ++ y)) = _
  rw [st_asStr, st_asStr]; rfl

theorem st_hv_length' (x : List Char) : c.hv stringLength [strV x] = some (int x.length) := by
  refine hv_of_value ?_
  show some ((asStr (strV x)).map fun x => int x.length) = _
  rw [st_asStr]; rfl

/-- `substrString(S, 0, p)` at a position: the first `p` characters. -/
theorem st_hv_substr_pre (x : List Char) (p : Nat) (hp : p ≤ x.length) :
    c.hv stringSubstr [strV x, int 0, int p] = some (strV (x.take p)) := by
  refine hv_of_value ?_
  show some ((asStr (strV x)).bind fun y => (asInt (int 0)).bind fun i => (asInt (int p)).bind fun j =>
    (KStr.substrString y i j).map strV) = _
  rw [st_asStr]
  show some ((KStr.substrString x 0 p).map strV) = _
  have h1 : ¬ ((0 : Int) < 0 ∧ (0 : Int) = p ∧ (p : Int) < x.length) := by omega
  have h2 : (0 : Int) ≤ 0 ∧ (0 : Int) ≤ p ∧ (p : Int) ≤ x.length := by omega
  unfold KStr.substrString KStr.substr
  simp only [h1, h2, ↓reduceIte]
  congr 3

/-- `substrString(S, q, lengthString(S))` at a position: the characters from `q` on. -/
theorem st_hv_substr_suf (x : List Char) (q : Nat) (hq : q ≤ x.length) :
    c.hv stringSubstr [strV x, int q, int x.length] = some (strV (x.drop q)) := by
  refine hv_of_value ?_
  show some ((asStr (strV x)).bind fun y => (asInt (int q)).bind fun i => (asInt (int x.length)).bind fun j =>
    (KStr.substrString y i j).map strV) = _
  rw [st_asStr]
  show some ((KStr.substrString x q x.length).map strV) = _
  have h1 : ¬ ((0 : Int) < q ∧ (q : Int) = x.length ∧ (x.length : Int) < x.length) := by omega
  have h2 : (0 : Int) ≤ q ∧ (q : Int) ≤ x.length ∧ (x.length : Int) ≤ x.length := by omega
  unfold KStr.substrString KStr.substr
  simp only [h1, h2, and_self, ↓reduceIte, Option.map_some, Int.toNat_natCast]
  rw [List.take_of_length_le (by simp only [List.length_drop]; omega)]

end

/-- The value of `findString(S, N, 0)` where `N` occurs in `S`, first at `p`. -/
theorem st_val_find {c : Semantics} {σ : Subst} {i j : Nat} {a b : String} (ha : σ.lookup i = some (foS a))
    (hb : σ.lookup j = some (foS b)) :
    val c σ (stFind i j) = some (int (KStr.firstOr (stOcc a.toList b.toList))) := by
  simp only [stFind, val, valList, allSome, ha, hb, intT, dv_int, Option.bind_some, Option.map_some, st_hv_find0]

def fnRepFirst : FnEqn :=
  ⟨[("VarSource", Srt.string), ("VarToReplace", Srt.string), ("VarReplacement", Srt.string)], stringReplaceFirst,
    [(Srt.string, .var 0, none), (Srt.string, .var 1, none), (Srt.string, .var 2, none)], Srt.string,
    some (.app intGe [stFind 0 1, intT 0]),
    .app stringConcat [.app stringConcat [.app stringSubstr [.var 0, intT 0, stFind 0 1], .var 2],
      .app stringSubstr [.var 0, .app intAdd [stFind 0 1, .app stringLength [.var 1]], .app stringLength [.var 0]]]⟩

/-- The right side of 1901 (and the first part of 1911's): at an occurrence `p`, the characters
before it, `R`, and those behind it. -/
theorem st_val_around {c : Semantics} {σ : Subst} {a b : String} {p : Nat} (ha : σ.lookup 0 = some (foS a))
    (hb : σ.lookup 1 = some (foS b)) (hocc : (stOcc a.toList b.toList).head? = some p) :
    val c σ (.app stringSubstr [.var 0, intT 0, stFind 0 1]) = some (strV (a.toList.take p)) ∧
    val c σ (.app stringSubstr [.var 0, .app intAdd [stFind 0 1, .app stringLength [.var 1]],
      .app stringLength [.var 0]]) = some (strV (a.toList.drop (p + b.toList.length))) := by
  have hmem : p ∈ stOcc a.toList b.toList := List.mem_of_mem_head? hocc
  have hbd := st_occ_bound hmem
  have hF : val c σ (stFind 0 1) = some (int p) := by
    rw [st_val_find ha hb]
    cases h : stOcc a.toList b.toList with
    | nil => rw [h] at hocc; cases hocc
    | cons q _ => rw [h] at hocc; cases hocc; rfl
  have hA : σ.lookup 0 = some (strV a.toList) := by rw [st_foS_strV]; exact ha
  have hB : σ.lookup 1 = some (strV b.toList) := by rw [st_foS_strV]; exact hb
  constructor
  · simp only [val, valList, allSome, hA, hF, intT, dv_int, Option.bind_some, Option.map_some]
    exact st_hv_substr_pre _ _ (by omega)
  · simp only [val, valList, allSome, hA, hB, hF, Option.bind_some, Option.map_some, st_hv_length', hv_intAdd]
    rw [show (p : Int) + (b.toList.length : Int) = ((p + b.toList.length : Nat) : Int) by omega]
    exact st_hv_substr_suf _ _ hbd

theorem st_occ_head {a b : String} (h : 0 ≤ KStr.firstOr (stOcc a.toList b.toList)) :
    ∃ p, (stOcc a.toList b.toList).head? = some p := by
  cases hl : stOcc a.toList b.toList with
  | nil => rw [hl] at h; simp [KStr.firstOr] at h
  | cons p _ => exact ⟨p, rfl⟩

theorem fnRepFirst_holds {c : Semantics} (hs : c.shapesOK = true) : fnRepFirst.Holds c := by
  intro σ hσ hreq hm
  obtain ⟨a, ha⟩ := st_string_at hs hσ 0 (n := "VarSource") rfl
  obtain ⟨b, hb⟩ := st_string_at hs hσ 1 (n := "VarToReplace") rfl
  obtain ⟨r, hr⟩ := st_string_at hs hσ 2 (n := "VarReplacement") rfl
  obtain ⟨h3, -, h4, -, h5, -, -⟩ := hm
  have h3' : σ.lookup 3 = some (foS a) := st_arg h3 ha
  have h4' : σ.lookup 4 = some (foS b) := st_arg h4 hb
  have h5' : σ.lookup 5 = some (foS r) := st_arg h5 hr
  have hq := hreq _ rfl
  simp only [val, valList, allSome, st_val_find ha hb, intT, dv_int, Option.bind_some, Option.map_some,
    fhv_intGe, Option.some.injEq] at hq
  obtain ⟨p, hocc⟩ := st_occ_head (of_decide_eq_true (fq_bool_inj hq))
  obtain ⟨v1, v2⟩ := st_val_around (c := c) ha hb hocc
  have hR : σ.lookup 2 = some (strV r.toList) := by rw [st_foS_strV]; exact hr
  have hl : val c σ fnRepFirst.lhs = some (strV (KStr.replaceFirst a.toList b.toList r.toList)) := by
    fq_eval [fnRepFirst, h3', h4', h5', st_hv_replaceFirst]
  rw [hl]
  show _ = val c σ (.app stringConcat [.app stringConcat [_, .var 2], _])
  simp only [val, valList, allSome] at v1 v2 ⊢
  rw [v1, v2]
  simp only [hR, Option.bind_some, Option.map_some, st_hv_concat']
  simp only [KStr.replaceFirst]
  rw [st_firstAt, hocc]

theorem fnRepFirst_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnRepFirst.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnRepFirst (by decide) (by rfl) (fnRepFirst_holds hs) ad hp hsv

/-! ## 1911: `replace(S, N, R, Count) => substrString(S, 0, findString(S, N, 0)) +String R +String
replace(substrString(S, findString(S, N, 0) +Int lengthString(N), lengthString(S)), N, R, Count -Int 1)
requires Count >Int 0 andBool findString(S, N, 0) >=Int 0` -/

def fnReplace : FnEqn :=
  ⟨[("VarSource", Srt.string), ("VarToReplace", Srt.string), ("VarReplacement", Srt.string), ("VarCount", Srt.int)],
    stringReplace,
    [(Srt.string, .var 0, none), (Srt.string, .var 1, none), (Srt.string, .var 2, none), (Srt.int, .var 3, none)],
    Srt.string, some (.app boolAnd [.app intGt [.var 3, intT 0], .app intGe [stFind 0 1, intT 0]]),
    .app stringConcat [.app stringConcat [.app stringSubstr [.var 0, intT 0, stFind 0 1], .var 2],
      .app stringReplace [.app stringSubstr [.var 0, .app intAdd [stFind 0 1, .app stringLength [.var 1]],
        .app stringLength [.var 0]], .var 1, .var 2, .app intSub [.var 3, intT 1]]]⟩

theorem fnReplace_holds {c : Semantics} (hs : c.shapesOK = true) : fnReplace.Holds c := by
  intro σ hσ hreq hm
  obtain ⟨a, ha⟩ := st_string_at hs hσ 0 (n := "VarSource") rfl
  obtain ⟨b, hb⟩ := st_string_at hs hσ 1 (n := "VarToReplace") rfl
  obtain ⟨r, hr⟩ := st_string_at hs hσ 2 (n := "VarReplacement") rfl
  obtain ⟨k, hk⟩ := int_at hs hσ 3 (n := "VarCount") rfl
  obtain ⟨h4, -, h5, -, h6, -, h7, -, -⟩ := hm
  have h4' : σ.lookup 4 = some (foS a) := st_arg h4 ha
  have h5' : σ.lookup 5 = some (foS b) := st_arg h5 hb
  have h6' : σ.lookup 6 = some (foS r) := st_arg h6 hr
  have h7' : σ.lookup 7 = some (int k) := st_arg h7 hk
  have hq := hreq _ rfl
  simp only [val, valList, allSome, hk, st_val_find ha hb, intT, dv_int, Option.bind_some, Option.map_some,
    fo_hv_intGt, fhv_intGe, fhv_boolAnd, Option.some.injEq] at hq
  have hq' := fq_bool_inj hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
  obtain ⟨hk0, hf0⟩ := hq'
  obtain ⟨p, hocc⟩ := st_occ_head hf0
  obtain ⟨v1, v2⟩ := st_val_around (c := c) ha hb hocc
  have hR : σ.lookup 2 = some (strV r.toList) := by rw [st_foS_strV]; exact hr
  have hl : val c σ fnReplace.lhs = some (strV (KStr.replaceN b.toList r.toList k.toNat a.toList)) := by
    fq_eval [fnReplace, h4', h5', h6', h7', fo_hv_stringReplace a b r (k := k) (by omega)]
  rw [hl]
  show _ = val c σ (.app stringConcat [.app stringConcat [_, .var 2], .app stringReplace [_, .var 1, .var 2, _]])
  simp only [val, valList, allSome] at v1 v2 ⊢
  rw [v1, v2]
  have hB : σ.lookup 1 = some (strV b.toList) := by rw [st_foS_strV]; exact hb
  have hrep : c.hv stringReplace [strV (a.toList.drop (p + b.toList.length)), strV b.toList, strV r.toList,
      int (k - 1)] =
      some (strV (KStr.replaceN b.toList r.toList (k - 1).toNat (a.toList.drop (p + b.toList.length)))) := by
    rw [st_foS_strV, st_foS_strV, st_strV_foS, fo_hv_stringReplace _ b r (by omega), String.toList_ofList]
  simp only [val, hR, hB, hk, intT, dv_int, Option.bind_some, Option.map_some, hv_intSub, hrep, st_hv_concat']
  have hkn : k.toNat = (k - 1).toNat + 1 := by omega
  rw [hkn, KStr.replaceN, st_firstAt, hocc]

theorem fnReplace_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnReplace.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnReplace (by decide +kernel) (by rfl) (fnReplace_holds hs) ad hp hsv

/-! ## The last position of a filter of `0 … n - 1` -/

theorem st_filter_range_succ (P : Nat → Bool) (n : Nat) :
    (List.range (n + 1)).filter P = (List.range n).filter P ++ (if P n then [n] else []) := by
  rw [List.range_succ, List.filter_append]
  cases h : P n <;> simp [h]

theorem st_lastOr_snoc (l : List Nat) (n : Nat) : KStr.lastOr (l ++ [n]) = n := by
  simp [KStr.lastOr, KStr.firstOr]

theorem st_lastOr_bound (P : Nat → Bool) : ∀ n : Nat,
    -1 ≤ KStr.lastOr ((List.range n).filter P) ∧ KStr.lastOr ((List.range n).filter P) < n
  | 0 => by simp [KStr.lastOr, KStr.firstOr]
  | n + 1 => by
    rw [st_filter_range_succ]
    have ih := st_lastOr_bound P n
    cases P n
    · simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]; omega
    · simp only [↓reduceIte, st_lastOr_snoc]; omega

set_option linter.unusedSimpArgs false in
/-- **The last position meeting `P` or `Q` is the greater of the last meeting each.** -/
theorem st_lastOr_or (P Q : Nat → Bool) : ∀ n : Nat,
    KStr.lastOr ((List.range n).filter fun p => P p || Q p) =
      max (KStr.lastOr ((List.range n).filter P)) (KStr.lastOr ((List.range n).filter Q))
  | 0 => by simp [KStr.lastOr, KStr.firstOr]
  | n + 1 => by
    simp only [st_filter_range_succ]
    have bP := st_lastOr_bound P n
    have bQ := st_lastOr_bound Q n
    have ih := st_lastOr_or P Q n
    cases hp : P n <;> cases hq : Q n <;>
      simp only [hp, hq, Bool.or_false, Bool.false_or, Bool.or_true, Bool.false_eq_true, ↓reduceIte,
        List.append_nil, st_lastOr_snoc, ih] <;> omega

/-- A substitution of values of the variables' sorts gives a String variable a String literal, of
the sort String. -/
theorem st_string_at' {c : Semantics} (hs : c.shapesOK = true) {vars : Vars} {σ : Subst}
    (hσ : ∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2)
    (i : Nat) {n : String} (hi : vars[i]? = some (n, Srt.string)) :
    ∃ a : String, σ.lookup i = some (foS a) ∧ c.sortOf (foS a) = some Srt.string := by
  obtain ⟨v, hv, hsv⟩ := hσ i _ hi
  obtain ⟨a, rfl⟩ := shape_string hs hsv
  exact ⟨a, hv, hsv⟩

/-! ## 1917: `replaceAll(S, N, R) => replace(S, N, R, countAllOccurrences(S, N))`, under `replaceAllEq` -/

def fnReplaceAll : FnEqn :=
  ⟨[("VarSource", Srt.string), ("VarToReplace", Srt.string), ("VarReplacement", Srt.string)], stringReplaceAll,
    [(Srt.string, .var 0, none), (Srt.string, .var 1, none), (Srt.string, .var 2, none)], Srt.string, none,
    .app stringReplace [.var 0, .var 1, .var 2, .app stringCountAll [.var 0, .var 1]]⟩

/-- **1917 holds of the values where the interpretation meets `replaceAllEq`**: at a non-empty needle
both sides are `replace` at the count of the needle's occurrences; at the empty needle `replaceAll`
is at a silent point, where the condition is the sentence. -/
theorem fnReplaceAll_holds {c : Semantics} (hs : c.shapesOK = true) (hc : c.replaceAllEq) : fnReplaceAll.Holds c := by
  intro σ hσ _ hm
  obtain ⟨a, ha, sa⟩ := st_string_at' hs hσ 0 (n := "VarSource") rfl
  obtain ⟨b, hb, sb⟩ := st_string_at' hs hσ 1 (n := "VarToReplace") rfl
  obtain ⟨r, hr, sr⟩ := st_string_at' hs hσ 2 (n := "VarReplacement") rfl
  obtain ⟨h3, -, h4, -, h5, -, -⟩ := hm
  have h3' : σ.lookup 3 = some (foS a) := st_arg h3 ha
  have h4' : σ.lookup 4 = some (foS b) := st_arg h4 hb
  have h5' : σ.lookup 5 = some (foS r) := st_arg h5 hr
  have hl : val c σ fnReplaceAll.lhs = c.hv stringReplaceAll [foS a, foS b, foS r] := by
    fq_eval [fnReplaceAll, h3', h4', h5']
  have hrv : val c σ fnReplaceAll.rhs =
      (c.hv stringCountAll [foS a, foS b]).bind fun k => c.hv stringReplace [foS a, foS b, foS r, k] := by
    show val c σ (.app stringReplace [.var 0, .var 1, .var 2, .app stringCountAll [.var 0, .var 1]]) = _
    simp only [val, valList, allSome, ha, hb, hr, Option.bind_some, Option.map_some]
    cases c.hv stringCountAll [foS a, foS b] <;> rfl
  rw [hl, hrv]
  cases hbe : b.toList with
  | nil =>
    refine hc _ _ _ ?_ ?_
    · exact sortsOf_cons.mpr ⟨_, _, sa, sortsOf_cons.mpr ⟨_, _, sb, sortsOf_cons.mpr ⟨_, _, sr, sortsOf_nil, rfl⟩,
        rfl⟩, rfl⟩
    · show some ((asStr (foS a)).bind fun x => (asStr (foS b)).bind fun y => (asStr (foS r)).bind fun z =>
        (KStr.replaceAll x y z).map strV) = _
      simp only [asStr, foS, beq_self_eq_true, ↓reduceIte, Option.bind_some, hbe, KStr.replaceAll, KStr.countAll,
        List.isEmpty_nil, Option.map_none]
  | cons ch t =>
    have hne : b.toList.isEmpty = false := by rw [hbe]; rfl
    have hcount : c.hv stringCountAll [foS a, foS b] =
        some (int (KStr.countFrom b.toList a.toList.length a.toList)) := by
      refine hv_of_value ?_
      show some ((KStr.countAll a.toList b.toList).map fun k => int k) = _
      simp only [KStr.countAll, hne, Bool.false_eq_true, ↓reduceIte]
      rfl
    have hall : c.hv stringReplaceAll [foS a, foS b, foS r] =
        some (strV (KStr.replaceN b.toList r.toList (KStr.countFrom b.toList a.toList.length a.toList) a.toList)) := by
      refine hv_of_value ?_
      show some ((KStr.replaceAll a.toList b.toList r.toList).map strV) = _
      simp only [KStr.replaceAll, KStr.countAll, hne, Bool.false_eq_true, ↓reduceIte, Option.map_some]
    rw [hall, hcount, Option.bind_some, fo_hv_stringReplace a b r (by omega)]
    simp

theorem fnReplaceAll_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (hc : c.replaceAllEq)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = fnReplaceAll.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnReplaceAll (by decide +kernel) (by rfl) (fnReplaceAll_holds hs hc) ad hp hsv

/-! ## 1893: `rfindChar(S1, S2, I) => maxInt(rfindString(S1, substrString(S2, 0, 1), I),
rfindChar(S1, substrString(S2, 1, lengthString(S2)), I)) requires S2 =/=String ""`, under `rfindCharEq` -/

theorem st_charIn_cons (s : List Char) (ch : Char) (t : List Char) (p : Nat) :
    KStr.charIn s (ch :: t) p = (KStr.charIn s [ch] p || KStr.charIn s t p) := by
  unfold KStr.charIn
  cases s[p]? with
  | none => rfl
  | some x => simp

/-- `rfindChar` at a position: the last position up to `i` whose character is one of `cs` (−1 for
none, so also at the empty `cs`). -/
theorem st_rfc (s cs : List Char) (i : Int) (hp : KStr.isPos s i = true) :
    KStr.rfindChar s cs i =
      some (KStr.lastOr ((List.range s.length).filter fun (p : Nat) => decide ((p : Int) ≤ i) && KStr.charIn s cs p)) := by
  unfold KStr.rfindChar
  cases cs with
  | nil =>
    have : ((List.range s.length).filter fun (p : Nat) => decide ((p : Int) ≤ i) && KStr.charIn s [] p) = [] :=
      List.filter_eq_nil_iff.mpr fun p _ => by
        simp only [KStr.charIn, Bool.and_eq_true, decide_eq_true_eq, not_and]
        intro _; generalize s[p]? = o; cases o <;> simp
    rw [this]; rfl
  | cons ch t => simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, hp]

/-- `rfindString` of one character at a position: as `rfindChar` of that character. -/
theorem st_rfind1 (s : List Char) (ch : Char) (i : Int) (hp : KStr.isPos s i = true) :
    KStr.rfind s [ch] i =
      some (KStr.lastOr ((List.range s.length).filter fun (p : Nat) => decide ((p : Int) ≤ i) && KStr.charIn s [ch] p)) := by
  unfold KStr.rfind KStr.positions
  simp only [hp, ↓reduceIte, st_filter_range_succ]
  have hlast : KStr.occursAt [ch] s s.length = false := by simp [KStr.occursAt]
  simp only [hlast, Bool.and_false, Bool.false_eq_true, ↓reduceIte, List.append_nil, Option.some.injEq]
  congr 1
  refine List.filter_congr fun p hp' => ?_
  have hpl : p < s.length := List.mem_range.mp hp'
  simp only [KStr.occursAt, KStr.charIn, List.drop_eq_getElem_cons hpl, List.getElem?_eq_getElem hpl,
    List.isPrefixOf, Option.any_some, List.contains_cons, List.contains_nil, Bool.or_false, Bool.and_true]
  cases h : (ch == s[p]) <;> cases h' : (s[p] == ch) <;> simp_all [beq_iff_eq]

section
variable {c : Semantics}

theorem st_hv_rfind (x y : List Char) (i v : Int) (h : KStr.rfind x y i = some v) :
    c.hv stringRfind [strV x, strV y, int i] = some (int v) := by
  refine hv_of_value ?_
  show some ((asStr (strV x)).bind fun a => (asStr (strV y)).bind fun b => (asInt (int i)).bind fun j =>
    (KStr.rfind a b j).map int) = _
  rw [st_asStr, st_asStr]
  show some ((KStr.rfind x y i).map int) = _
  rw [h]; rfl

theorem st_hv_rfindChar (x y : List Char) (i v : Int) (h : KStr.rfindChar x y i = some v) :
    c.hv stringRfindChar [strV x, strV y, int i] = some (int v) := by
  refine hv_of_value ?_
  show some ((asStr (strV x)).bind fun a => (asStr (strV y)).bind fun b => (asInt (int i)).bind fun j =>
    (KStr.rfindChar a b j).map int) = _
  rw [st_asStr, st_asStr]
  show some ((KStr.rfindChar x y i).map int) = _
  rw [h]; rfl

theorem st_hook_rfindChar_none (x y : List Char) (i : Int) (h : KStr.rfindChar x y i = none) :
    hook stringRfindChar [strV x, strV y, int i] = some none := by
  show some ((asStr (strV x)).bind fun a => (asStr (strV y)).bind fun b => (asInt (int i)).bind fun j =>
    (KStr.rfindChar a b j).map int) = _
  rw [st_asStr, st_asStr]
  show some ((KStr.rfindChar x y i).map int) = _
  rw [h]; rfl

theorem st_hv_intMax (x y : Int) : c.hv intMax [int x, int y] = some (int (max x y)) := hv_of_value rfl

end

def fnRfindChar : FnEqn :=
  ⟨[("VarS1", Srt.string), ("VarS2", Srt.string), ("VarI", Srt.int)], stringRfindChar,
    [(Srt.string, .var 0, none), (Srt.string, .var 1, none), (Srt.int, .var 2, none)], Srt.int,
    some (.app stringNe [.var 1, stT ""]),
    .app intMax [.app stringRfind [.var 0, .app stringSubstr [.var 1, intT 0, intT 1], .var 2],
      .app stringRfindChar [.var 0, .app stringSubstr [.var 1, intT 1, .app stringLength [.var 1]], .var 2]]⟩

/-- **1893 holds of the values where the interpretation meets `rfindCharEq`**: at a position `I` of
`S1`, the last position up to `I` of one of `S2`'s characters is the greater of the last of its
first character and the last of the others; at another `I` the left side is at a silent point,
where the condition is the sentence. -/
theorem fnRfindChar_holds {c : Semantics} (hs : c.shapesOK = true) (hc : c.rfindCharEq) : fnRfindChar.Holds c := by
  intro σ hσ hreq hm
  obtain ⟨a, ha, sa⟩ := st_string_at' hs hσ 0 (n := "VarS1") rfl
  obtain ⟨b, hb, sb⟩ := st_string_at' hs hσ 1 (n := "VarS2") rfl
  obtain ⟨vi, hvi, si⟩ := hσ 2 ("VarI", Srt.int) rfl
  obtain ⟨i, rfl⟩ := shape_int hs si
  obtain ⟨h3, -, h4, -, h5, -, -⟩ := hm
  have h3' : σ.lookup 3 = some (foS a) := st_arg h3 ha
  have h4' : σ.lookup 4 = some (foS b) := st_arg h4 hb
  have h5' : σ.lookup 5 = some (int i) := st_arg h5 hvi
  have hq := hreq _ rfl
  simp only [val, valList, allSome, hb, stT, Option.bind_some, Option.map_some] at hq
  have hne : c.hv stringNe [foS b, strV []] = some (bool true) := hq
  have hq2 := (st_hv_ne (c := c) b "").symm.trans hq
  obtain ⟨ch, t, hbe⟩ : ∃ ch t, b.toList = ch :: t := by
    cases hbl : b.toList with
    | nil => rw [hbl] at hq2; exact absurd (fq_bool_inj (Option.some.inj hq2)) (by decide)
    | cons ch t => exact ⟨ch, t, rfl⟩
  have hA : σ.lookup 0 = some (strV a.toList) := by rw [st_foS_strV]; exact ha
  have hB : σ.lookup 1 = some (strV (ch :: t)) := by rw [← hbe, st_foS_strV]; exact hb
  have hl : val c σ fnRfindChar.lhs = c.hv stringRfindChar [strV a.toList, strV (ch :: t), int i] := by
    fq_eval [fnRfindChar, h3', h4', h5']
    rw [← hbe, st_foS_strV, st_foS_strV]
  have hsub0 : c.hv stringSubstr [strV (ch :: t), int 0, int 1] = some (strV [ch]) :=
    st_hv_substr_pre (ch :: t) 1 (by simp)
  have hsub1 : c.hv stringSubstr [strV (ch :: t), int 1, int (ch :: t).length] = some (strV t) :=
    st_hv_substr_suf (ch :: t) 1 (by simp)
  have hr : val c σ fnRfindChar.rhs =
      (c.hv stringRfind [strV a.toList, strV [ch], int i]).bind fun x =>
        (c.hv stringRfindChar [strV a.toList, strV t, int i]).bind fun y => c.hv intMax [x, y] := by
    show val c σ (.app intMax [.app stringRfind [.var 0, .app stringSubstr [.var 1, intT 0, intT 1], .var 2],
      .app stringRfindChar [.var 0, .app stringSubstr [.var 1, intT 1, .app stringLength [.var 1]], .var 2]]) = _
    simp only [val, valList, allSome, hA, hB, hvi, intT, dv_int, Option.bind_some, Option.map_some, hsub0,
      st_hv_length', hsub1]
    cases c.hv stringRfind [strV a.toList, strV [ch], int i] <;>
      cases c.hv stringRfindChar [strV a.toList, strV t, int i] <;> rfl
  rw [hl, hr]
  cases hpos : KStr.isPos a.toList i with
  | true =>
    rw [st_hv_rfindChar _ _ _ _ (st_rfc _ _ _ hpos), st_hv_rfind _ _ _ _ (st_rfind1 _ _ _ hpos),
      Option.bind_some, st_hv_rfindChar _ _ _ _ (st_rfc _ _ _ hpos), Option.bind_some, st_hv_intMax]
    rw [← st_lastOr_or]
    congr 4
    funext p
    rw [st_charIn_cons, Bool.and_or_distrib_left]
  | false =>
    have hnone : KStr.rfindChar a.toList (ch :: t) i = none := by
      simp [KStr.rfindChar, hpos]
    rw [hc _ _ _ (sortsOf_cons.mpr ⟨_, _, by rw [st_foS_strV]; exact sa, sortsOf_cons.mpr ⟨_, _,
        by rw [← hbe, st_foS_strV]; exact sb, sortsOf_cons.mpr ⟨_, _, si, sortsOf_nil, rfl⟩, rfl⟩, rfl⟩)
      (by rw [← hbe, st_foS_strV]; exact hne) (st_hook_rfindChar_none _ _ _ hnone)]
    simp only [hsub0, Option.bind_some, st_hv_length', hsub1]

theorem fnRfindChar_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (hc : c.rfindCharEq)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = fnRfindChar.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnRfindChar (by decide +kernel) (by rfl) (fnRfindChar_holds hs hc) ad hp hsv

/-! ## 1925: `S1 ==K S2 => S1 ==String S2` at K sequences of one injected String -/

/-- `inj{String, KItem}(S1) ==K inj{String, KItem}(S2) => S1 ==String S2`. -/
def strKEq : KSeqEq := ⟨"VarS1", "VarS2", Srt.string, stringEq⟩

/-- `==String` at two String values. -/
theorem stringEq_graphK {c : Semantics} (hs : c.shapesOK = true) (v w : GroundTerm)
    (hv : c.sortOf v = some Srt.string) (hw : c.sortOf w = some Srt.string) :
    ∃ r : Bool, c.hv stringEq [v, w] = some (bool r) ∧ (r = true ↔ v = w) := by
  obtain ⟨a, rfl⟩ := shape_string hs hv
  obtain ⟨b, rfl⟩ := shape_string hs hw
  refine ⟨a.toList == b.toList, st_hv_eq a b, ?_⟩
  rw [beq_iff_eq, String.toList_inj]
  constructor
  · rintro rfl; rfl
  · intro hab; unfold foS at hab; cases hab; rfl

/-- **domains.md 1925** is entailed at values. -/
theorem strKEq_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true)
    (hsK : Srt.string ∈ c.sortsBelowKItem) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = strKEq.patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv]) : EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  KSeqEq.entailed h strKEq (by decide) hsK (by decide) (by decide) rfl (by decide) (by decide)
    (stringEq_graphK hs) ad hp hsv

/-! ## `#Ceil(t) => {req #Equals true}` over element variables; 2241, 2242: the padding of Bytes -/

/-- A definedness lemma over element variables: `\implies{R}(\top{R}(), \equals{Q0, R}(\ceil{s,
Q0}(t), \and{Q0}(rhs, \top{Q0}())))`, `t` a term of the sort `s` and `rhs` a predicate. -/
structure CeilEqn where
  vars : Vars
  s : Srt
  t : Term
  rhs : Pred

namespace CeilEqn

/-- The pattern of the lemma's axiom, over the registry's names. -/
def patR (E : CeilEqn) : Kore.Pattern :=
  .implies KoreAML.R (.top KoreAML.R)
    (.equals Q0 KoreAML.R (.ceil (regSrtK E.s) Q0 (koreR E.vars E.t)) (.and Q0 [E.rhs.koreR E.vars, .top Q0]))

/-- The variables are of registry sorts, `t` is of the sort `s` and over the registry's names, the
predicate is typed. -/
def typed (c : Semantics) (E : CeilEqn) : Bool :=
  E.vars.all (fun p => decide (p.2 < nRegSorts)) && decide (E.s < nRegSorts) && reg E.t &&
    srt? c E.vars E.t == some E.s && E.rhs.typed c E.vars && E.rhs.reg &&
    E.vars.all (fun p => (KoreAML.freeOf [] E.patR).contains (.evar p.1 (regSrtK p.2)))

/-- `t` has a value exactly where the predicate holds, at every substitution of values of the
variables' sorts. -/
def Holds (c : Semantics) (E : CeilEqn) : Prop :=
  ∀ σ : Subst, (∀ i p, E.vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) →
    ((val c σ E.t).isSome ↔ E.rhs.Holds c σ)

end CeilEqn

/-- **A definedness lemma whose term has a value exactly where its predicate holds is entailed at
values.** -/
theorem CeilEqn.entailed {c : Semantics} (h : c.coreOK = true) (E : CeilEqn) (ht : E.typed c = true)
    (hap : E.rhs.Apart c) (hE : E.Holds c) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = E.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  intro M _ I hI e hat m
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  simp only [CeilEqn.typed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨⟨⟨hvR, hs⟩, hrt⟩, hst⟩, hrty⟩, hrreg⟩, hfree⟩ := ht
  have hvR' : ∀ p ∈ E.vars, p.2 < nRegSorts := fun p hp => hvR p hp
  have hfv : ∀ i, i < E.vars.length → vkey c E.vars i ∈ KoreAML.freeOf [] ad.ax.pattern := by
    intro i hi
    have hmem : E.vars.getD i ("", 0) ∈ E.vars := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi
    rw [hp]; unfold vkey; rw [srtOf_reg c (hvR _ hmem)]
    exact List.mem_of_elem_eq_true (hfree _ hmem)
  obtain ⟨σ, hσ, hel⟩ := subst_of_atValues h hI hat E.vars hvR' hfv
  unfold KoreAML.trAxiom
  dsimp only
  rw [interpret_impl]
  intro hgd
  obtain ⟨hR, hQ⟩ := sv_sortGuards hI ad hsv hgd
  generalize htb : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hel hR hQ ⊢
  have hag : ∀ i v, i < E.vars.length → σ.lookup i = some v →
      ∀ m, m = e.evalEvar (t.ev (vkey c E.vars i)) ↔ (den c v).interpret I e m := by
    intro i v hi hv m'
    obtain ⟨h1, h2⟩ := hel i v hi hv
    rw [(elemOf_spec hI h1 e).1 m', h2]
  have hRv : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  have hQv : ∀ b, (KoreAML.trSort t Q0).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "Q0")) :=
    fun b => by rw [trSort_Q0, KoreAML.interp_evar]
  obtain ⟨τ, hτsort, hτ⟩ := srt_den hI (Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _))
  have d1 := den_val (tbl := t) (e := e) h hI hσ hag E.t hst
  have hin : ∀ v, c.sortOf v = some E.s → KoreAML.Inh I τ (elemOf c I v) := fun v hv => by
    refine (KoreAML.interp_inhOf_of (fun a' => ?_)).mp (elemOf_spec hI hv e).2
    have := hτ t e a'
    rwa [trSort_srtOf_twoT] at this
  have hφ : ∀ b, (KoreAML.tr ⟨t, []⟩ (kore c E.vars E.t)).interpret I e b → KoreAML.Inh I τ b := by
    intro b hb
    rw [d1.1 b] at hb
    cases hv : val c σ E.t with
    | none => rw [hv] at hb; exact hb.elim
    | some v =>
      rw [hv] at hb
      have hs1 := d1.2 v hv
      change (den c v).interpret I e b at hb
      rw [(elemOf_spec hI hs1 e).1 b] at hb
      rw [hb]; exact hin v hs1
  rw [hp]
  unfold CeilEqn.patR
  simp only [KoreAML.sortOf]
  rw [KoreAML.interp_equal hD]
  intro a
  rw [KoreAML.tr, KoreAML.interp_sImp]
  constructor
  · exact fun h' => h'.1
  · intro ha
    refine ⟨ha, fun _ => ?_⟩
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hQv hRv hQ hR]
    refine ⟨(KoreAML.interp_inhOf_of hRv).mp ha, fun b hb => ?_⟩
    rw [← kore_reg c hvR' _ hrt, ← srtOf_reg c hs]
    rw [show KoreAML.tr ⟨t, []⟩ (.ceil (srtOf c E.s) Q0 (kore c E.vars E.t)) =
      KoreAML.sCeil (KoreAML.trSort t (srtOf c E.s)) (KoreAML.trSort t Q0) (KoreAML.tr ⟨t, []⟩ (kore c E.vars E.t)) by
        rw [KoreAML.tr], KoreAML.interp_sCeil hD hc (hτ t e) hQv hτsort hQ hφ, KoreAML.tr]
    simp only [KoreAML.trAndList]
    rw [KoreAML.interp_sAnd, ← Pred.kore_reg c hvR' _ hrreg, Pred.den h hI hσ hag hQ E.rhs hrty hap b, KoreAML.tr,
      KoreAML.interp_sTop hD (by rw [trSort_Q0]; simp [Pattern.isFreeEvar]; exact fun hh => ev_ne_top hh.symm),
      KoreAML.interp_inhOf_of hQv]
    have hiff := hE σ hσ
    have hdef : (∃ x, (KoreAML.tr ⟨t, []⟩ (kore c E.vars E.t)).interpret I e x) ↔ (val c σ E.t).isSome := by
      constructor
      · rintro ⟨x, hx⟩
        rw [d1.1 x] at hx
        cases hv : val c σ E.t with
        | none => rw [hv] at hx; exact hx.elim
        | some _ => rfl
      · intro hsome
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
        exact ⟨elemOf c I v, (d1.1 _).mpr (by rw [hv]; exact ((elemOf_spec hI (d1.2 v hv) e).1 _).mpr rfl)⟩
    rw [hdef, hiff]
    exact ⟨fun ⟨x, y⟩ => ⟨⟨y, x⟩, y⟩, fun ⟨⟨y, x⟩, _⟩ => ⟨x, y⟩⟩

/-- `#Ceil(f(_Gen0, LEN, VAL)) => {(0 <=Int LEN andBool 0 <=Int VAL andBool VAL <Int 256) #Equals true}`,
`f` the padding of Bytes to the right or to the left. -/
def ceilPad (f : Sym) : CeilEqn :=
  ⟨[("Var'Unds'Gen0", Srt.bytes), ("VarLEN", Srt.int), ("VarVAL", Srt.int)], Srt.bytes,
    .app f [.var 0, .var 1, .var 2],
    .eq Srt.bool (.app boolAnd [.app boolAnd [.app intLe [intT 0, .var 1], .app intLe [intT 0, .var 2]],
      .app intLt [.var 2, intT 256]]) (fqB true)⟩

theorem ceilPad_holds {c : Semantics} (hs : c.shapesOK = true) (f : Sym)
    (hf : ∀ (x : String) (l v : Int), (c.hv f [.dv Srt.bytes (.tok x), int l, int v]).isSome = decide (0 ≤ l ∧ 0 ≤ v ∧ v < 256)) :
    (ceilPad f).Holds c := by
  intro σ hσ
  obtain ⟨vb, hvb, sb⟩ := hσ 0 _ rfl
  obtain ⟨x, rfl⟩ := shape_bytes hs sb
  obtain ⟨l, hl⟩ := int_at hs hσ 1 (n := "VarLEN") rfl
  obtain ⟨v, hv⟩ := int_at hs hσ 2 (n := "VarVAL") rfl
  show (val c σ (.app f [.var 0, .var 1, .var 2])).isSome ↔ val c σ _ = val c σ (fqB true)
  simp only [val, valList, allSome, hvb, hl, hv, intT, dv_int, fqB, fq_dv_bool, Option.bind_some, Option.map_some,
    hv_intLe, hv_intLt, fhv_boolAnd]
  rw [hf, Option.some.injEq]
  constructor
  · intro hd
    obtain ⟨a1, a2, a3⟩ := of_decide_eq_true hd
    simp [a1, a2, a3]
  · intro he
    have := fq_bool_inj he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact decide_eq_true ⟨this.1.1, this.1.2, this.2⟩

/-- The padding is defined exactly where the length is not negative and the value is a byte. -/
theorem ceilPad_graph {c : Semantics} (left : Bool) (x : String) (l v : Int) :
    (c.hv (if left then bytesPadLeft else bytesPadRight) [.dv Srt.bytes (.tok x), int l, int v]).isSome =
      decide (0 ≤ l ∧ 0 ≤ v ∧ v < 256) := by
  unfold Semantics.hv
  rw [Semantics.hookRes_of_notKey (by cases left <;> decide +kernel)]
  cases left
  · show (some ((KBytes.padRight x.toList l v).map bytesV)).join.isSome = _
    unfold KBytes.padRight
    by_cases hc : 0 ≤ l ∧ 0 ≤ v ∧ v < 256 <;> simp [hc]
  · show (some ((KBytes.padLeft x.toList l v).map bytesV)).join.isSome = _
    unfold KBytes.padLeft
    by_cases hc : 0 ≤ l ∧ 0 ≤ v ∧ v < 256 <;> simp [hc]

/-- **domains.md 2241, 2242** are entailed at values. -/
theorem ceilPad_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (left : Bool)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = (ceilPad (if left then bytesPadLeft else bytesPadRight)).patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v]) : EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  haveI : OvlOK c := ovlOK_of_core h
  exact CeilEqn.entailed h (ceilPad (if left then bytesPadLeft else bytesPadRight)) (by cases left <;> rfl)
    (apart_of_distinct bool_distinct)
    (ceilPad_holds hs _ (ceilPad_graph left)) ad hp hsv

end LibEv

end KCore
