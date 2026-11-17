/-
  The supported hook rows of INT (test/constructs/rows.toml, `hook:INT.*` with status `supported`):
  the sort row `INT.Int` and the sixteen operations `INT.add`, `sub`, `mul`, `tdiv`, `tmod`, `ediv`,
  `emod`, `min`, `max`, `abs`, `le`, `lt`, `ge`, `gt`, `eq`, `ne` (`intRows`). Each has its three
  statements (DONE-0 C2, evidence row "supported hook (E6)"). The expectation is the builtin
  file's prose, cited by line: DOM is K 7.1.337's
  `k-distribution/include/kframework/builtin/domains.md`. No expected value below is taken from a
  run or from `hook`'s text: each is derived by hand from the cited sentence (the derivation is
  written at the point), and the two divisions are stated by the property the prose names, with
  the proof that the property has one solution. Run from the package root:
  `lake env lean test/HooksInt.lean`. Kernel-checked.

  1. One in-domain value per operation (`vals`, some operations two): `hook`'s value there is the
     hand-derived one (`vals_hook`), it is the result under every interpretation in every semantics
     (`vals_hookRes`), and Γ of every semantics states it under every interpretation
     (`vals_gamma`).
  2. The regions the prose excludes or leaves unstated. INT's prose leaves no region of these
     sixteen unstated: twelve are declared `total` and described at every pair of integers, and of
     the four divisions the prose says "Division by zero is `#False`" (DOM 1233-1234, 1235-1237),
     which states that there is no value. So no point of these rows has the `param_undetermined`
     shape (over all H, Γ entails neither ⊥ nor a value): at divisor 0, Γ of every semantics states
     ⊥ under every interpretation (`div_zero_gamma`, `div_zero_entails`), which is the negation of
     that shape's first half. "Excludes" is read here as "says nothing of the value"; `#False` is a
     statement of the value (none).
  3. The silent predicate: none of the sixteen is a key of `silentTable` (`int_not_silentKey`), so
     its silent region is empty (`int_not_silent`), and the prose covers every argument list: a
     value of sort Int is an integer literal and nothing else (`int_only`, under `shapesOK`), so an
     argument list of the signature is a pair of integers (one integer for `absInt`), where the
     twelve `total` operations have the described value (`*_at`, `covered_total`, `covered_abs`) and
     the four divisions the described value off divisor 0 and none at it (`tdiv_at`, `ediv_at`,
     `div_zero`, `covered_div`).

  The sort row `INT.Int` (DOM 1196-1199, 1209-1210, 1215): every integer is a value of Int
  (`int_value`), two integers are two values (`int_inj`), nothing else is one (`int_only`); a sort
  has no argument list, so no key of `silentTable` (a list of symbols) is about it. The reader's
  literal texts are at `reader_canonical` and `reader_other`.
-/
import KcoreSpec

set_option autoImplicit false

namespace KCore.HooksIntTest

open KCore ML Faithful

/-! ## Γ at an interpreted symbol's application (as test/SilentPoints.lean writes it) -/

/-- The interpreted symbol `k` applied to the values `vs`, as Γ writes it. -/
abbrev appP (c : Semantics) (k : CtorSig) (vs : List GroundTerm) : KoreAML.P :=
  KoreAML.den (symApp c k.name (GroundTerm.koreList c vs))

/-- Where `hook` gives a value, Γ states it, in every semantics. -/
theorem gamma_val (c : Semantics) {k : CtorSig} (hk : k ∈ hookSigs) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) {v : GroundTerm} (hh : hook k.name vs = some (some v)) :
    Γ c (appP c k vs ≡ den c v) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨k, vs, some v, hk, hvs, hh, (fun h => nomatch h), rfl⟩)))))

/-- Off the silent points, Γ states ⊥ where `hook` gives no value, in every semantics. -/
theorem gamma_bot (c : Semantics) {k : CtorSig} (hk : k ∈ hookSigs) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) (hh : hook k.name vs = some none) (hs : silent k.name vs = false) :
    Γ c (appP c k vs ≡ ⊥) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨k, vs, none, hk, hvs, hh, fun _ => hs, rfl⟩)))))

/-- The signature of an interpreted symbol. -/
def sig (f : Sym) : CtorSig := (lookupSig hookSigs f).getD default

/-! ## The rows -/

/-- The sixteen supported operation rows of INT: the symbol and its `hook` attribute in the prose's
productions (DOM 1253 `INT.mul`, 1256-1258 `INT.tdiv`, 1259-1261 `INT.tmod`, 1263 `INT.ediv`,
1264 `INT.emod`, 1266 `INT.add`, 1267 `INT.sub`, 1284 `INT.min`, 1285 `INT.max`, 1293 `INT.abs`,
1328 `INT.le`, 1329 `INT.lt`, 1330 `INT.ge`, 1331 `INT.gt`, 1332 `INT.eq`, 1333 `INT.ne`). The
seventeenth row is the sort (`INT.Int`, DOM 1209). `freshInt` (DOM 1456-1457) has no `hook`
attribute and no row. -/
def intRows : List (Sym × String) :=
  [(intAdd, "INT.add"), (intSub, "INT.sub"), (intMul, "INT.mul"),
   (intTDiv, "INT.tdiv"), (intTMod, "INT.tmod"), (intEDiv, "INT.ediv"), (intEMod, "INT.emod"),
   (intMin, "INT.min"), (intMax, "INT.max"),
   (intLt, "INT.lt"), (intLe, "INT.le"), (intGt, "INT.gt"), (intGe, "INT.ge"),
   (intEq, "INT.eq"), (intNe, "INT.ne"), (intAbs, "INT.abs")]

/-- The four the prose does not declare `total` (DOM 1256-1264), with "Division by zero is
`#False`" (DOM 1233-1234, 1235-1237). -/
def divs : List Sym := [intTDiv, intTMod, intEDiv, intEMod]

/-- The eleven binary operations the prose declares `total` (DOM 1253, 1266, 1267, 1284, 1285,
1328-1333). `absInt` (DOM 1293, `total`) is the twelfth. -/
def binTotals : List Sym :=
  [intAdd, intSub, intMul, intMin, intMax, intLt, intLe, intGt, intGe, intEq, intNe]

/-- The rows are the registry's entries with an `INT.` hook, each with its hook name. -/
theorem intRows_registry :
    regHookNames.filter (fun e => e.2.toList.take 4 == "INT.".toList) = intRows := by
  decide +kernel

/-- Each row's symbol has a signature among `hookSigs`, of Int arguments: two, and a result Int
(arithmetic, `minInt`, `maxInt`) or Bool (the comparisons); one and Int for `absInt`. -/
theorem intRows_sig : intRows.all (fun r => decide (sig r.1 ∈ hookSigs) && (sig r.1).name == r.1 &&
    (sig r.1).args == (if r.1 == intAbs then [Srt.int] else [Srt.int, Srt.int]) &&
    (sig r.1).result == (if [intLt, intLe, intGt, intGe, intEq, intNe].contains r.1 then Srt.bool
      else Srt.int)) = true := by
  decide +kernel

/-- `partialHooks` (the interpreted symbols the totality deciders do not count as total) holds of
these rows exactly the four the prose does not declare `total`. -/
theorem intRows_partial : intRows.all (fun r => partialHooks.contains r.1 == divs.contains r.1) = true := by
  decide +kernel

/-! ## The sort row `INT.Int` -/

/-- Every integer is a value of sort Int, in every semantics: "arbitrary-precision integer
arithmetic" (DOM 1196-1197), the sort declared at DOM 1209. -/
theorem int_value (c : Semantics) (i : Int) : c.sortOf (int i) = some Srt.int := by
  simp [int, Semantics.sortOf, dvOK]

/-- Two integers are two values. -/
theorem int_inj {i j : Int} (h : int i = int j) : i = j := by
  simp only [int, GroundTerm.dv.injEq, Lit.int.injEq, true_and] at h; exact h

/-- Nothing else is a value of sort Int (where the sorts the interpreted symbols read have their
shapes, `shapesOK`): the prose gives Int no constructor, only the tokens of DOM 1210 and 1215. -/
theorem int_only {c : Semantics} (hs : c.shapesOK = true) {v : GroundTerm}
    (h : c.sortOf v = some Srt.int) : ∃ i, v = int i :=
  shape_int hs h

/-- The reader takes an integer's canonical text (`0`, or an optional `-` then digits not starting
with `0`), a text of DOM 1215's syntax `[\+\-]?[0-9]+`, as that integer. -/
theorem reader_canonical (i : Int) : intLit? (intRepr i) = some i := intLit?_intRepr i

example : intLit? "0" = some 0 ∧ intLit? "12" = some 12 ∧ intLit? "-12" = some (-12) := by
  decide +kernel

/-- Texts of DOM 1215's syntax that are not canonical (`+1`, `05`, `-0`) are not read: `intLit?`
gives none, so `Parse.lit?` at Int gives none (`reader_other_lit`), which the reader of a `\dv`
turns into the refusal `literal` (Parse.lean, `need (lit? …) .literal`): no value is given to it.
Whether a kompiled text holds such a literal is not established here. -/
theorem reader_other : intLit? "+1" = none ∧ intLit? "05" = none ∧ intLit? "-0" = none ∧
    intLit? "" = none := by
  decide +kernel

theorem reader_other_lit : Parse.lit? Srt.int "+1" = none ∧ Parse.lit? Srt.int "05" = none ∧
    Parse.lit? Srt.int "-0" = none := by
  decide +kernel

/-! ## The two divisions, by the property the prose names -/

/-- "t-division, which rounds towards zero" (DOM 1233-1234): the quotient `q` of `x` by `y` is
`x / y` (the rational) rounded towards zero, and `r` what remains. `x / y - q` is then in `(-1, 1)`
and is zero or has the sign of `x / y`; multiplied by `y`: `|r| < |y|`, and `r` is zero or has the
sign of `x`. -/
def Trunc (x y q r : Int) : Prop :=
  q * y + r = x ∧ r.natAbs < y.natAbs ∧ (0 ≤ x → 0 ≤ r) ∧ (x ≤ 0 → r ≤ 0)

/-- "Euclidean division, in which the remainder is always non-negative" (DOM 1235-1237): the
quotient and remainder of the division theorem, `x = q * y + r` with `0 ≤ r < |y|`. -/
def Euclid (x y q r : Int) : Prop := q * y + r = x ∧ 0 ≤ r ∧ r < y.natAbs

theorem quot_zero {d y e : Int} (h : d * y = e) (he : e.natAbs < y.natAbs) : d = 0 := by
  by_cases hd : d = 0
  · exact hd
  · have h1 : (d * y).natAbs = d.natAbs * y.natAbs := Int.natAbs_mul d y
    have h2 : y.natAbs ≤ d.natAbs * y.natAbs := Nat.le_mul_of_pos_left _ (by omega)
    rw [h] at h1; omega

/-- The property of t-division has one solution. -/
theorem trunc_unique {x y q r q' r' : Int} (h : Trunc x y q r) (h' : Trunc x y q' r') :
    q = q' ∧ r = r' := by
  obtain ⟨e, b, p, n⟩ := h
  obtain ⟨e', b', p', n'⟩ := h'
  have hd : q - q' = 0 := quot_zero (y := y) (e := r' - r) (by rw [Int.sub_mul]; omega) (by omega)
  have hq : q = q' := by omega
  subst hq
  exact ⟨rfl, by omega⟩

/-- The property of Euclidean division has one solution. -/
theorem euclid_unique {x y q r q' r' : Int} (h : Euclid x y q r) (h' : Euclid x y q' r') :
    q = q' ∧ r = r' := by
  obtain ⟨e, p, b⟩ := h
  obtain ⟨e', p', b'⟩ := h'
  have hd : q - q' = 0 := quot_zero (y := y) (e := r' - r) (by rw [Int.sub_mul]; omega) (by omega)
  have hq : q = q' := by omega
  subst hq
  exact ⟨rfl, by omega⟩

theorem trunc_tdiv (x : Int) {y : Int} (hy : y ≠ 0) : Trunc x y (x.tdiv y) (x.tmod y) := by
  refine ⟨by rw [Int.mul_comm]; exact Int.mul_tdiv_add_tmod x y, ?_, Int.tmod_nonneg y, fun h => ?_⟩
  · rw [Int.natAbs_tmod]; exact Nat.mod_lt _ (by omega)
  · have h1 : 0 ≤ (-x).tmod y := Int.tmod_nonneg y (by omega)
    rw [Int.neg_tmod] at h1; omega

theorem euclid_ediv (x : Int) {y : Int} (hy : y ≠ 0) : Euclid x y (x / y) (x % y) :=
  ⟨by rw [Int.mul_comm]; exact Int.mul_ediv_add_emod x y, Int.emod_nonneg x hy, Int.emod_lt x hy⟩

/-! ## `hook` at every argument list of integers -/

theorem hook_add (vs : List GroundTerm) : hook intAdd vs = some (int2 vs fun x y => some (int (x + y))) := rfl
theorem hook_sub (vs : List GroundTerm) : hook intSub vs = some (int2 vs fun x y => some (int (x - y))) := rfl
theorem hook_mul (vs : List GroundTerm) : hook intMul vs = some (int2 vs fun x y => some (int (x * y))) := rfl
theorem hook_tdiv (vs : List GroundTerm) : hook intTDiv vs = some (int2 vs fun x y => nonzero y (x.tdiv y)) := rfl
theorem hook_tmod (vs : List GroundTerm) : hook intTMod vs = some (int2 vs fun x y => nonzero y (x.tmod y)) := rfl
theorem hook_ediv (vs : List GroundTerm) : hook intEDiv vs = some (int2 vs fun x y => nonzero y (x.ediv y)) := rfl
theorem hook_emod (vs : List GroundTerm) : hook intEMod vs = some (int2 vs fun x y => nonzero y (x.emod y)) := rfl
theorem hook_min (vs : List GroundTerm) : hook intMin vs = some (int2 vs fun x y => some (int (min x y))) := rfl
theorem hook_max (vs : List GroundTerm) : hook intMax vs = some (int2 vs fun x y => some (int (max x y))) := rfl
theorem hook_lt (vs : List GroundTerm) : hook intLt vs = some (int2 vs fun x y => some (bool (decide (x < y)))) := rfl
theorem hook_le (vs : List GroundTerm) : hook intLe vs = some (int2 vs fun x y => some (bool (decide (x ≤ y)))) := rfl
theorem hook_gt (vs : List GroundTerm) : hook intGt vs = some (int2 vs fun x y => some (bool (decide (x > y)))) := rfl
theorem hook_ge (vs : List GroundTerm) : hook intGe vs = some (int2 vs fun x y => some (bool (decide (x ≥ y)))) := rfl
theorem hook_eq' (vs : List GroundTerm) : hook intEq vs = some (int2 vs fun x y => some (bool (decide (x = y)))) := rfl
theorem hook_ne (vs : List GroundTerm) : hook intNe vs = some (int2 vs fun x y => some (bool (decide (x ≠ y)))) := rfl
theorem hook_abs (vs : List GroundTerm) :
    hook intAbs vs = some (match vs with | [a] => (asInt a).map fun x => int x.natAbs | _ => none) := rfl

theorem int2_at (x y : Int) (f : Int → Int → Option GroundTerm) : int2 [int x, int y] f = f x y := by
  simp [int2, asInt, int]

/-- The sum (DOM 1238). -/
theorem add_at (x y : Int) : hook intAdd [int x, int y] = some (some (int (x + y))) := by
  rw [hook_add, int2_at]

/-- The difference (DOM 1238). -/
theorem sub_at (x y : Int) : hook intSub [int x, int y] = some (some (int (x - y))) := by
  rw [hook_sub, int2_at]

/-- The product (DOM 1232). -/
theorem mul_at (x y : Int) : hook intMul [int x, int y] = some (some (int (x * y))) := by
  rw [hook_mul, int2_at]

/-- `/Int` and `%Int` off divisor 0: the quotient and the remainder of t-division (DOM 1233-1234),
the one pair with that property (`trunc_unique`). -/
theorem tdiv_at (x : Int) {y : Int} (hy : y ≠ 0) : ∃ q r,
    hook intTDiv [int x, int y] = some (some (int q)) ∧
    hook intTMod [int x, int y] = some (some (int r)) ∧ Trunc x y q r :=
  ⟨x.tdiv y, x.tmod y, by rw [hook_tdiv, int2_at]; simp [nonzero, hy],
    by rw [hook_tmod, int2_at]; simp [nonzero, hy], trunc_tdiv x hy⟩

/-- `divInt` and `modInt` off divisor 0: the quotient and the remainder of Euclidean division
(DOM 1235-1237), the one pair with that property (`euclid_unique`). -/
theorem ediv_at (x : Int) {y : Int} (hy : y ≠ 0) : ∃ q r,
    hook intEDiv [int x, int y] = some (some (int q)) ∧
    hook intEMod [int x, int y] = some (some (int r)) ∧ Euclid x y q r :=
  ⟨x / y, x % y, by rw [hook_ediv, int2_at]; simp [nonzero, hy]; rfl,
    by rw [hook_emod, int2_at]; simp [nonzero, hy]; rfl, euclid_ediv x hy⟩

/-- At divisor 0 the four divisions have no value: "Division by zero is `#False`" (DOM 1233-1234,
1235-1237). -/
theorem div_zero (x : Int) : ∀ f ∈ divs, hook f [int x, int 0] = some none := by
  intro f hf
  simp only [divs, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · rw [hook_tdiv, int2_at]; simp [nonzero]
  · rw [hook_tmod, int2_at]; simp [nonzero]
  · rw [hook_ediv, int2_at]; simp [nonzero]
  · rw [hook_emod, int2_at]; simp [nonzero]

theorem min_ite (x y : Int) : min x y = if x < y then x else y := by split <;> omega
theorem max_ite (x y : Int) : max x y = if x < y then y else x := by split <;> omega
theorem abs_ite (x : Int) : (x.natAbs : Int) = if x < 0 then -x else x := by split <;> omega

/-- The minimum (DOM 1281), in the form of the prose's two rules: `I1` where `I1 <Int I2`, `I2`
where `I1 >=Int I2` (DOM 1450-1451). -/
theorem min_at (x y : Int) : hook intMin [int x, int y] = some (some (int (if x < y then x else y))) := by
  rw [hook_min, int2_at, min_ite]

/-- The maximum (DOM 1281): the argument that is not below the other. -/
theorem max_at (x y : Int) : hook intMax [int x, int y] = some (some (int (if x < y then y else x))) := by
  rw [hook_max, int2_at, max_ite]

/-- The absolute value (DOM 1290). -/
theorem abs_at (x : Int) : hook intAbs [int x] = some (some (int (if x < 0 then -x else x))) := by
  rw [← abs_ite, hook_abs]; simp [asInt, int]

/-- "less than or equal to, less than, greater than or equal to, greater than, equal, or unequal"
(DOM 1324-1325). -/
theorem le_at (x y : Int) : hook intLe [int x, int y] = some (some (bool (decide (x ≤ y)))) := by
  rw [hook_le, int2_at]
theorem lt_at (x y : Int) : hook intLt [int x, int y] = some (some (bool (decide (x < y)))) := by
  rw [hook_lt, int2_at]
theorem ge_at (x y : Int) : hook intGe [int x, int y] = some (some (bool (decide (y ≤ x)))) := by
  rw [hook_ge, int2_at]
theorem gt_at (x y : Int) : hook intGt [int x, int y] = some (some (bool (decide (y < x)))) := by
  rw [hook_gt, int2_at]
theorem eq_at (x y : Int) : hook intEq [int x, int y] = some (some (bool (decide (x = y)))) := by
  rw [hook_eq', int2_at]
/-- Unequal, in the form of the prose's rule `I1 =/=Int I2 => notBool (I1 ==Int I2)` (DOM 1453). -/
theorem ne_at (x y : Int) : hook intNe [int x, int y] = some (some (bool (!decide (x = y)))) := by
  rw [hook_ne, int2_at]; simp

/-! ## The prose's rules between these operations (DOM 1442-1448), at every pair of integers -/

/-- `I1 divInt I2 => (I1 -Int (I1 modInt I2)) /Int I2 requires I2 =/=Int 0` (DOM 1442-1443): the
Euclidean quotient is the t-quotient of `x` less its Euclidean remainder. -/
theorem ediv_rule (x : Int) {y : Int} (hy : y ≠ 0) : x / y = (x - x % y).tdiv y := by
  obtain ⟨e, p, b⟩ := euclid_ediv x hy
  exact (trunc_unique (x := x - x % y) (y := y) (q := x / y) (r := 0)
    ⟨by omega, by simp; omega, fun _ => Int.le_refl 0, fun _ => Int.le_refl 0⟩ (trunc_tdiv _ hy)).1

/-- `I1 modInt I2 => ((I1 %Int absInt(I2)) +Int absInt(I2)) %Int absInt(I2) requires I2 =/=Int 0`
(DOM 1444-1448). -/
theorem emod_rule (x : Int) {y : Int} (hy : y ≠ 0) :
    x % y = ((x.tmod (y.natAbs : Int)) + (y.natAbs : Int)).tmod (y.natAbs : Int) := by
  have ha : ((y.natAbs : Nat) : Int) ≠ 0 := by omega
  obtain ⟨e1, b1, p1, n1⟩ := trunc_tdiv x ha
  obtain ⟨e2, b2, p2, n2⟩ := trunc_tdiv (x.tmod (y.natAbs : Int) + (y.natAbs : Int)) ha
  generalize x.tmod (y.natAbs : Int) = t at *
  generalize x.tdiv (y.natAbs : Int) = qt at *
  generalize (t + (y.natAbs : Int)).tmod (y.natAbs : Int) = r at *
  generalize (t + (y.natAbs : Int)).tdiv (y.natAbs : Int) = q2 at *
  rcases Int.natAbs_eq y with h | h
  · refine (euclid_unique (euclid_ediv x hy) (q' := qt + q2 - 1) (r' := r) ⟨?_, by omega, by omega⟩).2
    rw [← h] at e1 e2
    rw [Int.sub_mul, Int.add_mul]; omega
  · refine (euclid_unique (euclid_ediv x hy) (q' := -(qt + q2 - 1)) (r' := r) ⟨?_, by omega, by omega⟩).2
    have hy' : (y.natAbs : Int) = -y := by omega
    rw [hy'] at e1 e2
    rw [Int.neg_mul, Int.sub_mul, Int.add_mul]
    rw [Int.mul_neg] at e1 e2
    omega

/-! ## Statement 1: one in-domain value per operation, derived from the prose -/

/-- A point: the operation, its hook name, its integer arguments and the expected value. -/
structure Pt where
  f : Sym
  name : String
  xs : List Int
  v : GroundTerm

/-- The expected values, each derived by hand from the cited sentence.
- `+Int`, `-Int`: "the sum … or difference" (DOM 1238): 5 + (-8) = -3; 3 - 5 = -2 (5 - 3 is 2).
- `*Int`: "the product" (DOM 1232): (-4) · 6 = -24.
- `/Int`, `%Int`: "t-division, which rounds towards zero" (DOM 1233-1234): -7 / 2 = -3.5, towards
  zero -3 (flooring gives -4); the remainder is -7 - (-3) · 2 = -1 (a non-negative remainder would
  be 1). At (7, -2): 7 / -2 = -3.5, towards zero -3; 7 - (-3) · (-2) = 1.
- `divInt`, `modInt`: "Euclidean division, in which the remainder is always non-negative" (DOM
  1235-1237): -7 = 4 · (-2) + 1 with 0 ≤ 1 < 2, so 4 and 1 (rounding -7 / -2 = 3.5 towards zero gives
  3, with remainder -1). At (-7, 2): -7 = (-4) · 2 + 1, so -4 and 1.
- `minInt`, `maxInt`: "the minimum and maximum … of two integers" (DOM 1281): of 5 and 3, 3; of 3
  and 5, 5; of -2 and -9, -9 and -2.
- `absInt`: "the absolute value" (DOM 1290): of -7, 7; of 7, 7.
- the comparisons (DOM 1324-1325): 3 ≤ 3; not 3 < 3; 3 ≥ 3; not 3 > 3; 3 = 3; not 3 ≠ 3; and at
  (2, 3): 2 ≤ 3, 2 < 3, not 2 ≥ 3, not 2 > 3, not 2 = 3, 2 ≠ 3. -/
def vals : List Pt :=
  [⟨intAdd, "INT.add", [5, -8], int (-3)⟩,
   ⟨intSub, "INT.sub", [3, 5], int (-2)⟩,
   ⟨intMul, "INT.mul", [-4, 6], int (-24)⟩,
   ⟨intTDiv, "INT.tdiv", [-7, 2], int (-3)⟩, ⟨intTMod, "INT.tmod", [-7, 2], int (-1)⟩,
   ⟨intTDiv, "INT.tdiv", [7, -2], int (-3)⟩, ⟨intTMod, "INT.tmod", [7, -2], int 1⟩,
   ⟨intEDiv, "INT.ediv", [-7, -2], int 4⟩, ⟨intEMod, "INT.emod", [-7, -2], int 1⟩,
   ⟨intEDiv, "INT.ediv", [-7, 2], int (-4)⟩, ⟨intEMod, "INT.emod", [-7, 2], int 1⟩,
   ⟨intMin, "INT.min", [5, 3], int 3⟩, ⟨intMax, "INT.max", [3, 5], int 5⟩,
   ⟨intMin, "INT.min", [-2, -9], int (-9)⟩, ⟨intMax, "INT.max", [-2, -9], int (-2)⟩,
   ⟨intAbs, "INT.abs", [-7], int 7⟩, ⟨intAbs, "INT.abs", [7], int 7⟩,
   ⟨intLe, "INT.le", [3, 3], bool true⟩, ⟨intLt, "INT.lt", [3, 3], bool false⟩,
   ⟨intGe, "INT.ge", [3, 3], bool true⟩, ⟨intGt, "INT.gt", [3, 3], bool false⟩,
   ⟨intEq, "INT.eq", [3, 3], bool true⟩, ⟨intNe, "INT.ne", [3, 3], bool false⟩,
   ⟨intLe, "INT.le", [2, 3], bool true⟩, ⟨intLt, "INT.lt", [2, 3], bool true⟩,
   ⟨intGe, "INT.ge", [2, 3], bool false⟩, ⟨intGt, "INT.gt", [2, 3], bool false⟩,
   ⟨intEq, "INT.eq", [2, 3], bool false⟩, ⟨intNe, "INT.ne", [2, 3], bool true⟩]

/-- Every row has a point, and every point is of a row. -/
theorem vals_rows : (intRows.all (fun r => vals.any fun p => p.f == r.1 && p.name == r.2) &&
    vals.all (fun p => intRows.contains (p.f, p.name))) = true := by
  decide +kernel

/-- **`hook`'s value at each point is the one derived from the prose.** -/
theorem vals_hook : vals.all (fun p => hook p.f (p.xs.map int) == some (some p.v)) = true := by
  decide +kernel

theorem vals_sig : vals.all (fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    (sig p.f).args == p.xs.map (fun _ => Srt.int)) = true := by
  decide +kernel

/-- **At each point the result is that value, under every interpretation, in every semantics.** -/
theorem vals_hookRes : ∀ p ∈ vals, ∀ (c : Semantics) (H : HookParams),
    (c.withHooks H).hookRes p.f (p.xs.map int) = some (some p.v) :=
  fun p hp _ _ => Semantics.hookRes_of_value (by simpa using List.all_eq_true.mp vals_hook p hp)

theorem sortsOf_ints (c : Semantics) (xs : List Int) :
    c.sortsOf (xs.map int) = some (xs.map fun _ => Srt.int) := by
  induction xs with
  | nil => simp [Semantics.sortsOf]
  | cons x xs ih => simp [Semantics.sortsOf, int_value, ih]

/-- **At each point Γ states that value, under every interpretation, in every semantics.** -/
theorem vals_gamma : ∀ p ∈ vals, ∀ (c : Semantics) (H : HookParams),
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) (p.xs.map int) ≡ den (c.withHooks H) p.v) := by
  intro p hp c H
  have h := List.all_eq_true.mp vals_sig p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hk, hname⟩, hargs⟩ := h
  have hh : hook p.f (p.xs.map int) = some (some p.v) := by
    simpa using List.all_eq_true.mp vals_hook p hp
  exact gamma_val _ hk (by rw [hargs]; exact sortsOf_ints _ _) (by rw [hname]; exact hh)

/-! ## Statement 3: no silent region; the prose covers every argument list -/

/-- **None of the sixteen is a key of `silentTable`.** -/
theorem int_not_silentKey : ∀ r ∈ intRows, silentKey r.1 = false := by decide +kernel

/-- **The silent predicate of each is false at every argument list**: the region the prose leaves
unstated is empty. -/
theorem int_not_silent : ∀ r ∈ intRows, ∀ vs : List GroundTerm, silent r.1 vs = false :=
  fun r hr vs => silent_of_not_silentKey (int_not_silentKey r hr) vs

/-- An argument list of two Ints is two integers. -/
theorem cover2 {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (h : c.sortsOf vs = some [Srt.int, Srt.int]) : ∃ x y, vs = [int x, int y] := by
  obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := sortsOf_two h
  obtain ⟨x, rfl⟩ := shape_int hs h₁
  obtain ⟨y, rfl⟩ := shape_int hs h₂
  exact ⟨x, y, rfl⟩

/-- **The eleven binary operations declared `total` have a value at every argument list of their
signature** (DOM 1253, 1266, 1267, 1284, 1285, 1328-1333), the one `*_at` gives. -/
theorem covered_total {c : Semantics} (hs : c.shapesOK = true) : ∀ f ∈ binTotals,
    ∀ vs : List GroundTerm, c.sortsOf vs = some [Srt.int, Srt.int] → ∃ v, hook f vs = some (some v) := by
  intro f hf vs hvs
  obtain ⟨x, y, rfl⟩ := cover2 hs hvs
  simp only [binTotals, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, add_at x y⟩
  · exact ⟨_, sub_at x y⟩
  · exact ⟨_, mul_at x y⟩
  · exact ⟨_, min_at x y⟩
  · exact ⟨_, max_at x y⟩
  · exact ⟨_, lt_at x y⟩
  · exact ⟨_, le_at x y⟩
  · exact ⟨_, gt_at x y⟩
  · exact ⟨_, ge_at x y⟩
  · exact ⟨_, eq_at x y⟩
  · exact ⟨_, ne_at x y⟩

/-- **`absInt` (declared `total`, DOM 1293) has a value at every argument list of its signature.** -/
theorem covered_abs {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.int]) : ∃ v, hook intAbs vs = some (some v) := by
  obtain ⟨w, rfl, hw⟩ := sortsOf_one hvs
  obtain ⟨x, rfl⟩ := shape_int hs hw
  exact ⟨_, abs_at x⟩

/-- **The four divisions at every argument list of their signature**: a pair of integers, with a
value where the divisor is not 0 and none where it is (DOM 1233-1234, 1235-1237). -/
theorem covered_div {c : Semantics} (hs : c.shapesOK = true) : ∀ f ∈ divs,
    ∀ vs : List GroundTerm, c.sortsOf vs = some [Srt.int, Srt.int] →
    ∃ x y, vs = [int x, int y] ∧ (y ≠ 0 → ∃ v, hook f vs = some (some v)) ∧
      (y = 0 → hook f vs = some none) := by
  intro f hf vs hvs
  obtain ⟨x, y, rfl⟩ := cover2 hs hvs
  refine ⟨x, y, rfl, fun hy => ?_, fun hy => by subst hy; exact div_zero x f hf⟩
  obtain ⟨q, r, h1, h2, -⟩ := tdiv_at x hy
  obtain ⟨q', r', h3, h4, -⟩ := ediv_at x hy
  simp only [divs, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact ⟨_, h1⟩
  · exact ⟨_, h2⟩
  · exact ⟨_, h3⟩
  · exact ⟨_, h4⟩

/-! ## Statement 2: at divisor 0 the prose says `#False`, and Γ states ⊥ for every interpretation -/

theorem divs_sig : ∀ f ∈ divs, sig f ∈ hookSigs ∧ (sig f).name = f ∧ (sig f).args = [Srt.int, Srt.int] := by
  decide +kernel

/-- **Γ of every semantics states ⊥ at divisor 0, under every interpretation** (DOM 1233-1234,
1235-1237: "Division by zero is `#False`"). -/
theorem div_zero_gamma (c : Semantics) (H : HookParams) (x : Int) : ∀ f ∈ divs,
    Γ (c.withHooks H) (appP (c.withHooks H) (sig f) [int x, int 0] ≡ ⊥) := by
  intro f hf
  obtain ⟨hk, hname, hargs⟩ := divs_sig f hf
  have hr : intRows.any (·.1 == f) = true := by
    simp only [divs, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl <;> decide
  obtain ⟨r, hr, hrf⟩ := List.any_eq_true.mp hr
  have hs : silent f [int x, int 0] = false := by
    have := int_not_silent r hr [int x, int 0]
    rwa [beq_iff_eq.mp hrf] at this
  exact gamma_bot _ hk (by rw [hargs]; exact sortsOf_ints _ [x, 0]) (by rw [hname]; exact div_zero x f hf)
    (by rw [hname]; exact hs)

/-- **So no interpretation gives division by zero a value**: over all H, Γ entails ⊥ there, the
negation of the first half of the `param_undetermined` shape (which says Γ entails neither ⊥ nor a
value). INT has no point of that shape among these rows. -/
theorem div_zero_entails (c : Semantics) (x : Int) : ∀ f ∈ divs, ∀ H : HookParams,
    Γ (c.withHooks H) ⊧ (appP (c.withHooks H) (sig f) [int x, int 0] ≡ ⊥) := by
  intro f hf H M _ I hI
  exact hI _ (div_zero_gamma c H x f hf)

/-! ## Axioms -/

/-- info: 'KCore.HooksIntTest.vals_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vals_gamma

/-- info: 'KCore.HooksIntTest.vals_hookRes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vals_hookRes

/-- info: 'KCore.HooksIntTest.div_zero_entails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms div_zero_entails

/-- info: 'KCore.HooksIntTest.covered_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covered_total

/-- info: 'KCore.HooksIntTest.covered_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covered_div

/-- info: 'KCore.HooksIntTest.covered_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covered_abs

/-- info: 'KCore.HooksIntTest.int_not_silent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms int_not_silent

/-- info: 'KCore.HooksIntTest.emod_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms emod_rule

/-- info: 'KCore.HooksIntTest.ediv_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ediv_rule

/-- info: 'KCore.HooksIntTest.int_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms int_only

end KCore.HooksIntTest
