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

  The three rows `INT.shr`, `INT.shl`, `INT.log2` (`shiftRows`, the last section), none declared
  `total` (DOM 1269, 1270, 1304). The prose: "Compute the arithmetic right shift `>>Int` of two
  integers. Shifting by a negative quantity is `#False`. Compute the left shift of two integers.
  Shifting by a negative quantity is `#False`." (DOM 1239-1242); "the log base 2, rounded towards
  zero, of an integer. The log base 2 of an integer is equal to the index of the highest bit set
  in the representation of a positive integer. Log base 2 of zero or a negative number is
  `#False`." (DOM 1298-1301). Readings, each with the property that has one solution: the left
  shift by `n ≥ 0` is `x · 2^n`; the arithmetic right shift by `n ≥ 0` is the `q` with
  `q · 2^n ≤ x < (q + 1) · 2^n` (the floor of `x / 2^n`: dropping the `n` low bits of the two's
  complement representation, the sign kept); the log of `x > 0` is the `k` with
  `2^k ≤ x < 2^(k + 1)`. Statements: the value at every argument list of the described region
  (`shl_at`, `shr_at`, `log2_at`), no value on the `#False` region (`shift_neg`, `log2_nonpos`),
  which is not silent (`shift_not_silentKey`), so Γ of every semantics states ⊥ there under every
  interpretation (`shift_neg_gamma`, `log2_nonpos_gamma`) and the value elsewhere
  (`shl_gamma`, `shr_gamma`, `log2_gamma`); the points (`shiftVals`, `shiftBots`); every argument
  list of the signatures is covered (`covered_shift`, `covered_log2`); none of the three is a
  parameter symbol of a library module (`shift_not_param`).

  The three rows `INT.powmod`, `INT.bitRange`, `INT.signExtendBitRange` (`bitRows`), none declared
  `total` (DOM 1251, 1318, 1319). The prose of the bit ranges (DOM 1309-1315) states no edge; their
  equations do: `bitRangeInt(I, IDX, LEN) => (I >>Int IDX) modInt (1 <<Int LEN)` (DOM 1438) and
  `signExtendBitRangeInt(I, IDX, LEN) => (bitRangeInt(I, IDX, LEN) +Int (1 <<Int (LEN -Int 1)))
  modInt (1 <<Int LEN) -Int (1 <<Int (LEN -Int 1))` (DOM 1440), unconditional equations of the
  functions. An equation equates the application with its right side, and a symbol applied to an
  argument with no value has none, so at a negative index or length (and for the sign extension at
  length 0, the subterm `1 <<Int (0 -Int 1)`) there is no value, through the shifts' `#False`.
  Statements: each equation holds of `hook` at every three integers, both sides having the same
  value or both none (`bitRange_eq`, `signExt_eq`); the points (`bitVals`, `bitBots`, Γ's statement
  under every interpretation); every argument list of the signature is covered (`covered_bitRange`).
  `A ^%Int B C` is "equal in value to `(A ^Int B) %Int C`" (DOM 1229-1231): at `C = 0` there is no
  value (DOM 1233-1234), and Γ states ⊥ under every interpretation (`powmod_zero_gamma`). At
  `B ≥ 0`, `C ≠ 0` the value is the remainder `(A ^Int B) %Int C`, the truncating one (DOM
  1233-1234): Γ states it under every interpretation (`powmod_at`, `powmod_gamma`, `powmodVals`,
  `-2 ^%Int 3 5` = -3 among them). The prose states the value; `smt-hook((mod (^ #1 #2) #3))`
  (DOM 1251) is how a solver query encodes the production (MAN 2381-2389), which the same block
  says must "convert from Euclidian division operations" (DOM 1255), and states no value. At
  `B < 0`, `C ≠ 0` `hook` gives none and the point is silent (`powmod_silent`): DOM 1228 says
  nothing of a negative exponent. There the prose still says the two sides are equal in value, but
  Γ leaves each to the interpretation separately, so Γ does not entail `A ^%Int B C = (A ^Int B)
  %Int C` at a negative exponent; no statement here says that relation is undetermined by the text.
  None of the three is a parameter symbol of a library module (`bit_not_param`).

  The row `INT.pow` (the last section), not declared `total` (DOM 1250): "Compute the
  exponentiation `^Int` of two integers" (DOM 1228). At `b ≥ 0` the one value is `a` to the power
  `b` (`pow_at`, `pow_gamma`, `powVals`); at `b < 0` the sentence names no integer and writes no
  `#False`, so `hook` gives none and the point is silent (`pow_neg`, `2 ^Int -1` among them).
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

/-- The rows are the registry's entries with an `INT.` hook, each with its hook name, before the
three of `shiftRows`, the three of `bitRows` and `^Int` (the last three sections). -/
theorem intRows_registry :
    regHookNames.filter (fun e => e.2.toList.take 4 == "INT.".toList) =
      intRows ++ [(intShr, "INT.shr"), (intShl, "INT.shl"), (intLog2, "INT.log2"),
        (intPowMod, "INT.powmod"), (intBitRange, "INT.bitRange"), (intSignExtBitRange, "INT.signExtendBitRange"),
        (intPow, "INT.pow")] := by
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

/-! ## The shifts and `log2Int` -/

/-- The three rows: the symbol and its `hook` attribute in the prose's productions (DOM 1269
`INT.shr`, 1270 `INT.shl`, 1304 `INT.log2`), none with `total`. -/
def shiftRows : List (Sym × String) := [(intShr, "INT.shr"), (intShl, "INT.shl"), (intLog2, "INT.log2")]

/-- Their KORE names (the symbols of `_>>Int_`, `_<<Int_`, `log2Int`). -/
theorem shiftRows_names :
    (regSymNames.getD intShr "", regSymNames.getD intShl "", regSymNames.getD intLog2 "") =
      ("Lbl'Unds-GT--GT-'Int'Unds'", "Lbl'Unds-LT--LT-'Int'Unds'",
       "Lbllog2Int'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int") := by
  decide +kernel

/-- Each has a signature among `hookSigs` (Int, Int : Int for the shifts, Int : Int for the log), is
among `partialHooks`, and is no key of `silentTable`: where `hook` gives no value the prose says
`#False`. -/
theorem shiftRows_sig : shiftRows.all (fun r => decide (sig r.1 ∈ hookSigs) && (sig r.1).name == r.1 &&
    (sig r.1).args == (if r.1 == intLog2 then [Srt.int] else [Srt.int, Srt.int]) &&
    (sig r.1).result == Srt.int && partialHooks.contains r.1 && regHookOf r.2 == some r.1) = true := by
  decide +kernel

theorem shift_not_silentKey : ∀ r ∈ shiftRows, silentKey r.1 = false := by decide +kernel

theorem shift_not_silent : ∀ r ∈ shiftRows, ∀ vs : List GroundTerm, silent r.1 vs = false :=
  fun r hr vs => silent_of_not_silentKey (shift_not_silentKey r hr) vs

/-- No library module has one of the three among its parameter symbols. -/
theorem shift_not_param : (List.range library.length).all (fun i =>
    (libParams [i]).all fun p => !(shiftRows.map (·.1)).contains p.sig.name) = true := by
  decide +kernel

theorem hook_shr (vs : List GroundTerm) :
    hook intShr vs = some (int2 vs fun x n => if n < 0 then none else some (int (x.fdiv (2 ^ n.toNat)))) := rfl
theorem hook_shl (vs : List GroundTerm) :
    hook intShl vs = some (int2 vs fun x n => if n < 0 then none else some (int (x * 2 ^ n.toNat))) := rfl
theorem hook_log2 (x : Int) :
    hook intLog2 [int x] = some (if 0 < x then some (int x.toNat.log2) else none) := rfl

/-- "the left shift of two integers" (DOM 1241) by `n ≥ 0`: `x · 2^n`. -/
theorem shl_at (x : Int) {n : Int} (hn : 0 ≤ n) :
    hook intShl [int x, int n] = some (some (int (x * 2 ^ n.toNat))) := by
  rw [hook_shl, int2_at, if_neg (by omega)]

/-- "the arithmetic right shift" (DOM 1239) by `n ≥ 0`: the floor of `x / 2^n`, by its property. -/
def Floor (x : Int) (n : Nat) (q : Int) : Prop := q * 2 ^ n ≤ x ∧ x < (q + 1) * 2 ^ n

theorem floor_unique {x : Int} {n : Nat} {q q' : Int} (h : Floor x n q) (h' : Floor x n q') : q = q' := by
  have hp : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)
  obtain ⟨a, b⟩ := h
  obtain ⟨a', b'⟩ := h'
  have h1 : q < q' + 1 := Int.lt_of_mul_lt_mul_right (Int.lt_of_le_of_lt a b') (Int.le_of_lt hp)
  have h2 : q' < q + 1 := Int.lt_of_mul_lt_mul_right (Int.lt_of_le_of_lt a' b) (Int.le_of_lt hp)
  omega

theorem floor_fdiv (x : Int) (n : Nat) : Floor x n (x.fdiv (2 ^ n)) := by
  have hp : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)
  rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt hp)]
  refine ⟨Int.ediv_mul_le x (Int.ne_of_gt hp), ?_⟩
  have := Int.lt_ediv_add_one_mul_self x hp
  exact this

theorem shr_at (x : Int) {n : Int} (hn : 0 ≤ n) :
    ∃ q, hook intShr [int x, int n] = some (some (int q)) ∧ Floor x n.toNat q :=
  ⟨_, by rw [hook_shr, int2_at, if_neg (by omega)], floor_fdiv x n.toNat⟩

/-- "Shifting by a negative quantity is `#False`" (DOM 1239-1242), of both shifts. -/
theorem shift_neg (x : Int) {n : Int} (hn : n < 0) :
    hook intShr [int x, int n] = some none ∧ hook intShl [int x, int n] = some none := by
  rw [hook_shr, hook_shl, int2_at, int2_at, if_pos hn, if_pos hn]; exact ⟨rfl, rfl⟩

/-- "the index of the highest bit set in the representation of a positive integer" (DOM
1299-1300): the `k` with `2^k ≤ x < 2^(k + 1)`. -/
def HighBit (x : Int) (k : Nat) : Prop := (2 : Int) ^ k ≤ x ∧ x < 2 ^ (k + 1)

theorem highBit_unique {x : Int} {k k' : Nat} (h : HighBit x k) (h' : HighBit x k') : k = k' := by
  obtain ⟨a, b⟩ := h
  obtain ⟨a', b'⟩ := h'
  have e1 : (2 : Int) ^ k < 2 ^ (k' + 1) := Int.lt_of_le_of_lt a b'
  have e2 : (2 : Int) ^ k' < 2 ^ (k + 1) := Int.lt_of_le_of_lt a' b
  have n1 : 2 ^ k < 2 ^ (k' + 1) := by exact_mod_cast e1
  have n2 : 2 ^ k' < 2 ^ (k + 1) := by exact_mod_cast e2
  have := (Nat.pow_lt_pow_iff_right (a := 2) (by decide)).mp n1
  have := (Nat.pow_lt_pow_iff_right (a := 2) (by decide)).mp n2
  omega

theorem log2_at {x : Int} (hx : 0 < x) :
    ∃ k, hook intLog2 [int x] = some (some (int (k : Nat))) ∧ HighBit x k := by
  refine ⟨x.toNat.log2, by rw [hook_log2, if_pos hx], ?_⟩
  have hne : x.toNat ≠ 0 := by omega
  have h1 : 2 ^ x.toNat.log2 ≤ x.toNat := Nat.log2_self_le hne
  have h2 : x.toNat < 2 ^ (x.toNat.log2 + 1) := Nat.lt_log2_self
  have hx' : x = (x.toNat : Int) := by omega
  constructor
  · rw [hx']; exact_mod_cast h1
  · rw [hx']; exact_mod_cast h2

/-- "Log base 2 of zero or a negative number is `#False`" (DOM 1300-1301). -/
theorem log2_nonpos {x : Int} (hx : x ≤ 0) : hook intLog2 [int x] = some none := by
  rw [hook_log2, if_neg (by omega)]

/-- A point of one of the three: the symbol, its integer arguments, a value. -/
structure SPt where
  f : Sym
  xs : List Int
  v : GroundTerm

/-- Points, each derived from the sentence: `-5 <<Int 1` is -5 · 2 = -10; `-5 >>Int 1` is the floor
of -5 / 2 = -3 (-3 · 2 = -6 ≤ -5 < -4); `13 >>Int 2` is 3 (12 ≤ 13 < 16); `7 <<Int 0` and
`7 >>Int 0` are 7; `log2Int(5)` is 2 (4 ≤ 5 < 8), `log2Int(1)` is 0 (1 ≤ 1 < 2), `log2Int(8)` is 3. -/
def shiftVals : List SPt :=
  [⟨intShl, [-5, 1], int (-10)⟩, ⟨intShr, [-5, 1], int (-3)⟩, ⟨intShr, [13, 2], int 3⟩,
   ⟨intShl, [7, 0], int 7⟩, ⟨intShr, [7, 0], int 7⟩, ⟨intShr, [-1, 5], int (-1)⟩,
   ⟨intLog2, [5], int 2⟩, ⟨intLog2, [1], int 0⟩, ⟨intLog2, [8], int 3⟩]

theorem shiftVals_ok : shiftVals.all (fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    (sig p.f).args == p.xs.map (fun _ => Srt.int) && hook p.f (p.xs.map int) == some (some p.v)) = true := by
  decide +kernel

/-- **At each, Γ of every semantics states the value under every interpretation.** -/
theorem shiftVals_gamma : ∀ p ∈ shiftVals, ∀ (c : Semantics) (H : HookParams),
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) (p.xs.map int) ≡ den (c.withHooks H) p.v) := by
  intro p hp c H
  have h := List.all_eq_true.mp shiftVals_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hk, hname⟩, hargs⟩, hh⟩ := h
  exact gamma_val _ hk (by rw [hargs]; exact sortsOf_ints _ _) (by rw [hname]; exact hh)

/-- The `#False` points: `1 <<Int -1`, `1 >>Int -1`, `log2Int(0)`, `log2Int(-4)`. The last
component of a point is not read. -/
def shiftBots : List SPt :=
  [⟨intShl, [1, -1], int 0⟩, ⟨intShr, [1, -1], int 0⟩, ⟨intLog2, [0], int 0⟩, ⟨intLog2, [-4], int 0⟩]

/-- At each, `hook` gives no value and the point is not silent. -/
theorem shiftBots_ok : shiftBots.all (fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    (sig p.f).args == p.xs.map (fun _ => Srt.int) && hook p.f (p.xs.map int) == some none &&
    !silent p.f (p.xs.map int)) = true := by
  decide +kernel

/-- **At each, Γ of every semantics states ⊥ under every interpretation**, so over all
interpretations Γ entails ⊥ there: no interpretation gives the point a value. -/
theorem shiftBots_gamma : ∀ p ∈ shiftBots, ∀ (c : Semantics) (H : HookParams),
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) (p.xs.map int) ≡ ⊥) := by
  intro p hp c H
  have h := List.all_eq_true.mp shiftBots_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hk, hname⟩, hargs⟩, hh⟩, hs⟩ := h
  exact gamma_bot _ hk (by rw [hargs]; exact sortsOf_ints _ _) (by rw [hname]; exact hh) (by rw [hname]; exact hs)

theorem shiftBots_entails : ∀ p ∈ shiftBots, ∀ (c : Semantics) (H : HookParams),
    Γ (c.withHooks H) ⊧ (appP (c.withHooks H) (sig p.f) (p.xs.map int) ≡ ⊥) :=
  fun p hp c H _ _ I hI => hI _ (shiftBots_gamma p hp c H)

theorem shift_sigs : sig intShr = ⟨intShr, [Srt.int, Srt.int], Srt.int⟩ ∧
    sig intShl = ⟨intShl, [Srt.int, Srt.int], Srt.int⟩ ∧ sig intLog2 = ⟨intLog2, [Srt.int], Srt.int⟩ ∧
    sig intShr ∈ hookSigs ∧ sig intShl ∈ hookSigs ∧ sig intLog2 ∈ hookSigs := by
  decide +kernel

/-- **On the whole `#False` region of the shifts Γ states ⊥, in every semantics under every
interpretation.** -/
theorem shift_neg_gamma (c : Semantics) (H : HookParams) (x : Int) {n : Int} (hn : n < 0) :
    Γ (c.withHooks H) (appP (c.withHooks H) (sig intShr) [int x, int n] ≡ ⊥) ∧
    Γ (c.withHooks H) (appP (c.withHooks H) (sig intShl) [int x, int n] ≡ ⊥) := by
  obtain ⟨e1, e2, -, m1, m2, -⟩ := shift_sigs
  have hs := sortsOf_ints (c.withHooks H) [x, n]
  exact ⟨gamma_bot _ m1 (by rw [e1]; exact hs) (by rw [e1]; exact (shift_neg x hn).1)
      (by rw [e1]; exact shift_not_silent (intShr, "INT.shr") (by decide) _),
    gamma_bot _ m2 (by rw [e2]; exact hs) (by rw [e2]; exact (shift_neg x hn).2)
      (by rw [e2]; exact shift_not_silent (intShl, "INT.shl") (by decide) _)⟩

/-- **And of `log2Int`.** -/
theorem log2_nonpos_gamma (c : Semantics) (H : HookParams) {x : Int} (hx : x ≤ 0) :
    Γ (c.withHooks H) (appP (c.withHooks H) (sig intLog2) [int x] ≡ ⊥) := by
  obtain ⟨-, -, e3, -, -, m3⟩ := shift_sigs
  exact gamma_bot _ m3 (by rw [e3]; exact sortsOf_ints (c.withHooks H) [x]) (by rw [e3]; exact log2_nonpos hx)
    (by rw [e3]; exact shift_not_silent (intLog2, "INT.log2") (by decide) _)

/-- **On the described region Γ states the value.** -/
theorem shl_gamma (c : Semantics) (H : HookParams) (x : Int) {n : Int} (hn : 0 ≤ n) :
    Γ (c.withHooks H) (appP (c.withHooks H) (sig intShl) [int x, int n] ≡ den (c.withHooks H) (int (x * 2 ^ n.toNat))) := by
  obtain ⟨-, e2, -, -, m2, -⟩ := shift_sigs
  exact gamma_val _ m2 (by rw [e2]; exact sortsOf_ints (c.withHooks H) [x, n]) (by rw [e2]; exact shl_at x hn)

theorem shr_gamma (c : Semantics) (H : HookParams) (x : Int) {n : Int} (hn : 0 ≤ n) :
    ∃ q, Floor x n.toNat q ∧
      Γ (c.withHooks H) (appP (c.withHooks H) (sig intShr) [int x, int n] ≡ den (c.withHooks H) (int q)) := by
  obtain ⟨e1, -, -, m1, -, -⟩ := shift_sigs
  obtain ⟨q, hq, hf⟩ := shr_at x hn
  exact ⟨q, hf, gamma_val _ m1 (by rw [e1]; exact sortsOf_ints (c.withHooks H) [x, n]) (by rw [e1]; exact hq)⟩

theorem log2_gamma (c : Semantics) (H : HookParams) {x : Int} (hx : 0 < x) :
    ∃ k : Nat, HighBit x k ∧
      Γ (c.withHooks H) (appP (c.withHooks H) (sig intLog2) [int x] ≡ den (c.withHooks H) (int k)) := by
  obtain ⟨-, -, e3, -, -, m3⟩ := shift_sigs
  obtain ⟨k, hk, hb⟩ := log2_at hx
  exact ⟨k, hb, gamma_val _ m3 (by rw [e3]; exact sortsOf_ints (c.withHooks H) [x]) (by rw [e3]; exact hk)⟩

/-- **The shifts at every argument list of their signature**: a pair of integers, with a value
where the amount is not negative and none where it is. -/
theorem covered_shift {c : Semantics} (hs : c.shapesOK = true) : ∀ f ∈ [intShr, intShl],
    ∀ vs : List GroundTerm, c.sortsOf vs = some [Srt.int, Srt.int] →
    ∃ x n, vs = [int x, int n] ∧ (0 ≤ n → ∃ v, hook f vs = some (some v)) ∧ (n < 0 → hook f vs = some none) := by
  intro f hf vs hvs
  obtain ⟨x, n, rfl⟩ := cover2 hs hvs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨x, n, rfl, fun hn => (shr_at x hn).elim fun _ h => ⟨_, h.1⟩, fun hn => (shift_neg x hn).1⟩
  · exact ⟨x, n, rfl, fun hn => ⟨_, shl_at x hn⟩, fun hn => (shift_neg x hn).2⟩

/-- **`log2Int` at every argument list of its signature.** -/
theorem covered_log2 {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.int]) :
    ∃ x, vs = [int x] ∧ (0 < x → ∃ v, hook intLog2 vs = some (some v)) ∧ (x ≤ 0 → hook intLog2 vs = some none) := by
  obtain ⟨w, rfl, hw⟩ := sortsOf_one hvs
  obtain ⟨x, rfl⟩ := shape_int hs hw
  exact ⟨x, rfl, fun hx => (log2_at hx).elim fun _ h => ⟨_, h.1⟩, log2_nonpos⟩

/-- The four simplification rules of INT-SYMBOLIC (DOM 1380-1383: `X <<Int 0 => X`,
`0 <<Int Y => 0 requires 0 <=Int Y`, `X >>Int 0 => X`, `0 >>Int Y => 0 requires 0 <=Int Y`) hold of
`hook`. `Semantics.libAdmitted` names none of them (its conjuncts are about silent points, and
these three symbols have none). -/
theorem shift_rules (x : Int) {y : Int} (hy : 0 ≤ y) :
    hook intShl [int x, int 0] = some (some (int x)) ∧ hook intShl [int 0, int y] = some (some (int 0)) ∧
    hook intShr [int x, int 0] = some (some (int x)) ∧ hook intShr [int 0, int y] = some (some (int 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [shl_at x (Int.le_refl 0)]; simp
  · rw [shl_at 0 hy]; simp
  · rw [hook_shr, int2_at, if_neg (by omega)]; simp [Int.fdiv_one]
  · rw [hook_shr, int2_at, if_neg (by omega)]; simp [Int.zero_fdiv]

/-! ## The bit ranges and `^%Int` -/

/-- The three rows: the symbol and its `hook` attribute in the prose's productions (DOM 1251
`INT.powmod`, 1318 `INT.bitRange`, 1319 `INT.signExtendBitRange`), none with `total`. -/
def bitRows : List (Sym × String) :=
  [(intPowMod, "INT.powmod"), (intBitRange, "INT.bitRange"), (intSignExtBitRange, "INT.signExtendBitRange")]

/-- Their KORE names (the symbols of `_^%Int__`, `bitRangeInt`, `signExtendBitRangeInt`). -/
theorem bitRows_names :
    (regSymNames.getD intPowMod "", regSymNames.getD intBitRange "", regSymNames.getD intSignExtBitRange "") =
      ("Lbl'UndsXor-Perc'Int'UndsUnds'",
       "LblbitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int",
       "LblsignExtendBitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int") := by
  decide +kernel

/-- Each has the signature Int, Int, Int : Int among `hookSigs`, is among `partialHooks`, and is the
registry's symbol of its `hook` attribute. -/
theorem bitRows_sig : bitRows.all (fun r => decide (sig r.1 ∈ hookSigs) && (sig r.1).name == r.1 &&
    (sig r.1).args == [Srt.int, Srt.int, Srt.int] && (sig r.1).result == Srt.int && partialHooks.contains r.1 &&
    regHookOf r.2 == some r.1) = true := by
  decide +kernel

/-- No library module has one of the three among its parameter symbols. -/
theorem bit_not_param : (List.range library.length).all (fun i =>
    (libParams [i]).all fun p => !(bitRows.map (·.1)).contains p.sig.name) = true := by
  decide +kernel

/-- The two bit ranges have no silent point: where `hook` gives no value, the text states none. -/
theorem bitRange_not_silentKey : silentKey intBitRange = false ∧ silentKey intSignExtBitRange = false := by
  decide +kernel

theorem intArgs3_at (x y z : Int) (f : Int → Int → Int → Option GroundTerm) :
    intArgs3 [int x, int y, int z] f = f x y z := by
  simp [intArgs3, asInt, int]

theorem hook_bitRange (x i l : Int) : hook intBitRange [int x, int i, int l] =
    some (if i < 0 ∨ l < 0 then none else some (int (bitRangeVal x i l))) := by
  rw [show hook intBitRange [int x, int i, int l] = some (intArgs3 [int x, int i, int l] fun x i l =>
    if i < 0 ∨ l < 0 then none else some (int (bitRangeVal x i l))) from rfl, intArgs3_at]

theorem hook_signExt (x i l : Int) : hook intSignExtBitRange [int x, int i, int l] =
    some (if i < 0 ∨ l < 1 then none else some (int (signExtVal x i l))) := by
  rw [show hook intSignExtBitRange [int x, int i, int l] = some (intArgs3 [int x, int i, int l] fun x i l =>
    if i < 0 ∨ l < 1 then none else some (int (signExtVal x i l))) from rfl, intArgs3_at]

/-- Where `^%Int` has a value: a non-negative exponent and a modulus other than 0. -/
def powmodStated (_a b m : Int) : Prop := 0 ≤ b ∧ m ≠ 0

theorem hook_powmod (a b m : Int) : hook intPowMod [int a, int b, int m] =
    some (if b < 0 ∨ m = 0 then none else some (int ((a ^ b.toNat).tmod m))) := by
  rw [show hook intPowMod [int a, int b, int m] = some (intArgs3 [int a, int b, int m] fun a b m =>
    if b < 0 ∨ m = 0 then none else some (int ((a ^ b.toNat).tmod m))) from rfl, intArgs3_at]

/-- `hook`'s value of an interpreted symbol at values, none where it has none: what Γ states of the
application where the point is not silent. -/
def hv (f : Sym) (vs : List GroundTerm) : Option GroundTerm := (hook f vs).join

theorem hv_shr (x n : Int) :
    hv intShr [int x, int n] = if n < 0 then none else some (int (x.fdiv (2 ^ n.toNat))) := by
  simp only [hv, hook_shr, int2_at, Option.join_some]

theorem hv_shl (x n : Int) : hv intShl [int x, int n] = if n < 0 then none else some (int (x * 2 ^ n.toNat)) := by
  simp only [hv, hook_shl, int2_at, Option.join_some]

theorem hv_emod (x y : Int) : hv intEMod [int x, int y] = nonzero y (x.emod y) := by
  simp only [hv, hook_emod, int2_at, Option.join_some]

theorem hv_add (x y : Int) : hv intAdd [int x, int y] = some (int (x + y)) := by
  simp only [hv, hook_add, int2_at, Option.join_some]

theorem hv_sub (x y : Int) : hv intSub [int x, int y] = some (int (x - y)) := by
  simp only [hv, hook_sub, int2_at, Option.join_some]

theorem pow2_ne (n : Nat) : (1 : Int) * 2 ^ n ≠ 0 := by
  rw [Int.one_mul]; exact Int.ne_of_gt (Int.pow_pos (by decide))

/-- **DOM 1438 holds of `hook` at every three integers**: `bitRangeInt(I, IDX, LEN)` and
`(I >>Int IDX) modInt (1 <<Int LEN)` have the same value, or both none (a symbol applied to an
argument with no value has none). -/
theorem bitRange_eq (x i l : Int) :
    hv intBitRange [int x, int i, int l] =
      (hv intShr [int x, int i]).bind fun a => (hv intShl [int 1, int l]).bind fun b => hv intEMod [a, b] := by
  rw [hv_shr, hv_shl]
  simp only [hv, hook_bitRange, Option.join_some]
  by_cases hi : i < 0
  · simp [hi]
  · by_cases hl : l < 0
    · simp [hi, hl]
    · simp only [hi, hl, or_self, if_false, Option.bind_some, hook_emod, int2_at, Option.join_some, nonzero,
        pow2_ne, ite_false]
      simp [bitRangeVal]

/-- **DOM 1440 holds of `hook` at every three integers**: `signExtendBitRangeInt(I, IDX, LEN)` and
`(bitRangeInt(I, IDX, LEN) +Int (1 <<Int (LEN -Int 1))) modInt (1 <<Int LEN) -Int
(1 <<Int (LEN -Int 1))` have the same value, or both none; the subterm `1 <<Int (LEN -Int 1)`
(both of its occurrences have its one value) has none at `LEN = 0`. -/
theorem signExt_eq (x i l : Int) :
    hv intSignExtBitRange [int x, int i, int l] =
      (hv intSub [int l, int 1]).bind fun m => (hv intBitRange [int x, int i, int l]).bind fun r =>
      (hv intShl [int 1, m]).bind fun h => (hv intAdd [r, h]).bind fun s =>
      (hv intShl [int 1, int l]).bind fun p => (hv intEMod [s, p]).bind fun q => hv intSub [q, h] := by
  rw [hv_sub l 1]
  simp only [Option.bind_some]
  rw [hv_shl 1 (l - 1), hv_shl 1 l]
  simp only [hv, hook_signExt, hook_bitRange, Option.join_some]
  by_cases hi : i < 0
  · simp [hi]
  · by_cases hl : l < 1
    · by_cases hl0 : l < 0
      · simp [hi, hl, hl0]
      · have : l - 1 < 0 := by omega
        simp [hi, hl, hl0, this]
    · have h1 : ¬ l < 0 := by omega
      have h2 : ¬ l - 1 < 0 := by omega
      simp only [hi, hl, h1, h2, or_self, if_false, Option.bind_some, hook_add, hook_emod, hook_sub, int2_at,
        Option.join_some, nonzero, pow2_ne, ite_false]
      simp [signExtVal]

/-- Points, each derived from the equations: `bitRangeInt(13, 1, 2)`: 13 >>Int 1 is 6, 6 modInt 4
is 2; `signExtendBitRangeInt(13, 1, 2)`: (2 + 2) modInt 4 - 2 = -2; `bitRangeInt(-1, 0, 8)`:
-1 modInt 256 = 255; `signExtendBitRangeInt(255, 0, 8)`: (255 + 128) modInt 256 - 128 = -1;
`signExtendBitRangeInt(127, 0, 8)`: (127 + 128) modInt 256 - 128 = 127. -/
def bitVals : List SPt :=
  [⟨intBitRange, [13, 1, 2], int 2⟩, ⟨intSignExtBitRange, [13, 1, 2], int (-2)⟩,
   ⟨intBitRange, [-1, 0, 8], int 255⟩, ⟨intSignExtBitRange, [255, 0, 8], int (-1)⟩,
   ⟨intSignExtBitRange, [127, 0, 8], int 127⟩]

theorem bitVals_ok : bitVals.all (fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    (sig p.f).args == p.xs.map (fun _ => Srt.int) && hook p.f (p.xs.map int) == some (some p.v)) = true := by
  decide +kernel

/-- **At each, Γ of every semantics states the value under every interpretation.** -/
theorem bitVals_gamma : ∀ p ∈ bitVals, ∀ (c : Semantics) (H : HookParams),
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) (p.xs.map int) ≡ den (c.withHooks H) p.v) := by
  intro p hp c H
  have h := List.all_eq_true.mp bitVals_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hk, hname⟩, hargs⟩, hh⟩ := h
  exact gamma_val _ hk (by rw [hargs]; exact sortsOf_ints _ _) (by rw [hname]; exact hh)

/-- The points without a value: `bitRangeInt(1, -1, 1)` (`1 >>Int -1`), `bitRangeInt(1, 0, -1)`
(`1 <<Int -1`), `signExtendBitRangeInt(1, 0, 0)` (`1 <<Int (0 -Int 1)`), `2 ^%Int 3 0`
(`(2 ^Int 3) %Int 0`, DOM 1233-1234). The last component of a point is not read. -/
def bitBots : List SPt :=
  [⟨intBitRange, [1, -1, 1], int 0⟩, ⟨intBitRange, [1, 0, -1], int 0⟩, ⟨intSignExtBitRange, [1, 0, 0], int 0⟩,
   ⟨intPowMod, [2, 3, 0], int 0⟩]

/-- At each, `hook` gives no value and the point is not silent. -/
theorem bitBots_ok : bitBots.all (fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    (sig p.f).args == p.xs.map (fun _ => Srt.int) && hook p.f (p.xs.map int) == some none &&
    !silent p.f (p.xs.map int)) = true := by
  decide +kernel

/-- **At each, Γ of every semantics states ⊥ under every interpretation.** -/
theorem bitBots_gamma : ∀ p ∈ bitBots, ∀ (c : Semantics) (H : HookParams),
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) (p.xs.map int) ≡ ⊥) := by
  intro p hp c H
  have h := List.all_eq_true.mp bitBots_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hk, hname⟩, hargs⟩, hh⟩, hs⟩ := h
  exact gamma_bot _ hk (by rw [hargs]; exact sortsOf_ints _ _) (by rw [hname]; exact hh) (by rw [hname]; exact hs)

theorem bit_sigs : sig intPowMod = ⟨intPowMod, [Srt.int, Srt.int, Srt.int], Srt.int⟩ ∧
    sig intPowMod ∈ hookSigs := by
  decide +kernel

/-- **At a zero modulus Γ states ⊥ for every base and exponent, in every semantics under every
interpretation**: the point is not silent. -/
theorem powmod_zero_gamma (c : Semantics) (H : HookParams) (a b : Int) :
    Γ (c.withHooks H) (appP (c.withHooks H) (sig intPowMod) [int a, int b, int 0] ≡ ⊥) := by
  obtain ⟨e, m⟩ := bit_sigs
  have hs : silent intPowMod [int a, int b, int 0] = false := rfl
  exact gamma_bot _ m (by rw [e]; exact sortsOf_ints (c.withHooks H) [a, b, 0])
    (by rw [e]; exact (hook_powmod a b 0).trans (by simp)) (by rw [e]; exact hs)

/-- **Where the text states the value** (`powmodStated`), `hook` gives `(A ^Int B) %Int C`. -/
theorem powmod_at {a b m : Int} (h : powmodStated a b m) :
    hook intPowMod [int a, int b, int m] = some (some (int ((a ^ b.toNat).tmod m))) := by
  obtain ⟨hb, hm⟩ := h
  rw [hook_powmod, if_neg (by omega)]

/-- **There Γ of every semantics states that value under every interpretation.** -/
theorem powmod_gamma (c : Semantics) (H : HookParams) {a b m : Int} (h : powmodStated a b m) :
    Γ (c.withHooks H) (appP (c.withHooks H) (sig intPowMod) [int a, int b, int m] ≡
      den (c.withHooks H) (int ((a ^ b.toNat).tmod m))) := by
  obtain ⟨e, mm⟩ := bit_sigs
  exact gamma_val _ mm (by rw [e]; exact sortsOf_ints (c.withHooks H) [a, b, m]) (by rw [e]; exact powmod_at h)

/-- **Off a zero modulus, every point where the text does not state the value (a negative
exponent) is silent**: `hook` gives no value there, and Γ states the interpretation's. -/
theorem powmod_silent {a b m : Int} (hm : m ≠ 0) (h : ¬ powmodStated a b m) :
    hook intPowMod [int a, int b, int m] = some none ∧ silent intPowMod [int a, int b, int m] = true := by
  refine ⟨?_, ?_⟩
  · rw [hook_powmod, if_pos]
    by_cases hb : b < 0
    · exact Or.inl hb
    · exact absurd ⟨by omega, hm⟩ h
  · show (asInt (int m)).any (· != 0) = true
    simp [asInt, int, hm]

/-- Points, each derived from the sentence: `2 ^%Int 3 5` is 8 %Int 5 = 3; `-2 ^%Int 2 5` is
4 %Int 5 = 4; `-2 ^%Int 3 4` is -8 %Int 4 = 0 (4 divides -8); `7 ^%Int 2 -5` is 49 %Int -5 = 4;
`3 ^%Int 0 7` is 1 %Int 7 = 1; `-2 ^%Int 3 5` is -8 %Int 5 = -3 (rounding -8 / 5 towards zero). -/
def powmodVals : List SPt :=
  [⟨intPowMod, [2, 3, 5], int 3⟩, ⟨intPowMod, [-2, 2, 5], int 4⟩, ⟨intPowMod, [-2, 3, 4], int 0⟩,
   ⟨intPowMod, [7, 2, -5], int 4⟩, ⟨intPowMod, [3, 0, 7], int 1⟩, ⟨intPowMod, [-2, 3, 5], int (-3)⟩]

theorem powmodVals_ok : powmodVals.all (fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    (sig p.f).args == p.xs.map (fun _ => Srt.int) && hook p.f (p.xs.map int) == some (some p.v)) = true := by
  decide +kernel

/-- A silent point: `2 ^%Int -1 5` (a negative exponent). -/
example : hook intPowMod [int 2, int (-1), int 5] = some none ∧ silent intPowMod [int 2, int (-1), int 5] = true := by
  decide +kernel

/-- `HookParams.lib` (LibAdmitted.lean) gives `^%Int` no value at any point. -/
theorem lib_powmod_none (vs : List GroundTerm) : HookParams.lib.app intPowMod vs = none := rfl

/-- **The bit ranges at every argument list of their signature**: three integers, with a value
where the index and the length are not negative (and, for `signExtendBitRangeInt`, the length not
0), and none elsewhere. -/
theorem covered_bitRange {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.int, Srt.int, Srt.int]) :
    ∃ x i l, vs = [int x, int i, int l] ∧
      hook intBitRange vs = some (if i < 0 ∨ l < 0 then none else some (int (bitRangeVal x i l))) ∧
      hook intSignExtBitRange vs = some (if i < 0 ∨ l < 1 then none else some (int (signExtVal x i l))) := by
  obtain ⟨w₁, w₂, w₃, rfl, h₁, h₂, h₃⟩ := sortsOf_three hvs
  obtain ⟨x, rfl⟩ := shape_int hs h₁
  obtain ⟨i, rfl⟩ := shape_int hs h₂
  obtain ⟨l, rfl⟩ := shape_int hs h₃
  exact ⟨x, i, l, rfl, hook_bitRange x i l, hook_signExt x i l⟩

#print axioms bitRange_eq
#print axioms signExt_eq
#print axioms bitVals_gamma
#print axioms bitBots_gamma
#print axioms powmod_zero_gamma
#print axioms powmod_silent
#print axioms powmod_at
#print axioms powmod_gamma
#print axioms lib_powmod_none
#print axioms covered_bitRange
#print axioms bit_not_param

/-! ## `^Int` -/

/-- The row `INT.pow` (DOM 1250, not declared `total`): its KORE name, its signature Int, Int : Int
among `hookSigs`, among `partialHooks`, the registry's symbol of its `hook` attribute, and no
parameter symbol of a library module. -/
theorem pow_row : regSymNames.getD intPow "" = "Lbl'UndsXor-'Int'Unds'" ∧
    sig intPow = ⟨intPow, [Srt.int, Srt.int], Srt.int⟩ ∧ sig intPow ∈ hookSigs ∧
    partialHooks.contains intPow = true ∧ regHookOf "INT.pow" = some intPow ∧
    (List.range library.length).all (fun i => (libParams [i]).all fun p => p.sig.name != intPow) = true := by
  decide +kernel

theorem hook_pow (vs : List GroundTerm) :
    hook intPow vs = some (int2 vs fun a b => if b < 0 then none else some (int (a ^ b.toNat))) := rfl

/-- "Compute the exponentiation `^Int` of two integers" (DOM 1228), at `b ≥ 0`: `a` to the power `b`,
the product of `b` factors `a` (1 at `b = 0`, the empty product). -/
theorem pow_at (a : Int) {b : Int} (hb : 0 ≤ b) :
    hook intPow [int a, int b] = some (some (int (a ^ b.toNat))) := by
  rw [hook_pow, int2_at, if_neg (by omega)]

/-- At a negative exponent the sentence names no integer and writes no `#False`: `hook` gives no
value, and the point is silent (Γ states the interpretation's value). -/
theorem pow_neg (a : Int) {b : Int} (hb : b < 0) :
    hook intPow [int a, int b] = some none ∧ silent intPow [int a, int b] = true :=
  ⟨by rw [hook_pow, int2_at, if_pos hb], rfl⟩

/-- `2 ^Int -1`: silent, not without value. -/
example : hook intPow [int 2, int (-1)] = some none ∧ silent intPow [int 2, int (-1)] = true := by
  decide +kernel

/-- Points, each derived from the sentence: `2 ^Int 10` is 1024, `-2 ^Int 3` is -8, `7 ^Int 0` is 1,
`0 ^Int 2` is 0. -/
def powVals : List SPt :=
  [⟨intPow, [2, 10], int 1024⟩, ⟨intPow, [-2, 3], int (-8)⟩, ⟨intPow, [7, 0], int 1⟩, ⟨intPow, [0, 2], int 0⟩]

theorem powVals_ok : powVals.all (fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    (sig p.f).args == p.xs.map (fun _ => Srt.int) && hook p.f (p.xs.map int) == some (some p.v)) = true := by
  decide +kernel

/-- **At a non-negative exponent Γ of every semantics states the power under every
interpretation.** -/
theorem pow_gamma (c : Semantics) (H : HookParams) (a : Int) {b : Int} (hb : 0 ≤ b) :
    Γ (c.withHooks H) (appP (c.withHooks H) (sig intPow) [int a, int b] ≡ den (c.withHooks H) (int (a ^ b.toNat))) := by
  obtain ⟨-, e, m, -⟩ := pow_row
  exact gamma_val _ m (by rw [e]; exact sortsOf_ints (c.withHooks H) [a, b]) (by rw [e]; exact pow_at a hb)

/-- `HookParams.lib` (LibAdmitted.lean) gives `^Int` no value at any point, as it gave none while
`^Int` was a parameter symbol: at `b ≥ 0` the value is `hook`'s, and at `b < 0` it gives none still. -/
theorem lib_pow_none (vs : List GroundTerm) : HookParams.lib.app intPow vs = none := rfl

#print axioms pow_at
#print axioms pow_neg
#print axioms pow_gamma
#print axioms lib_pow_none

/-- info: 'KCore.HooksIntTest.shiftBots_entails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms shiftBots_entails

/-- info: 'KCore.HooksIntTest.shiftVals_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms shiftVals_gamma

#print axioms shift_neg_gamma
#print axioms log2_nonpos_gamma
#print axioms shr_gamma
#print axioms log2_gamma
#print axioms covered_shift
#print axioms covered_log2
#print axioms shift_rules
#print axioms shift_not_param

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

/-- info: 'KCore.HooksIntTest.int_not_silent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms int_not_silent

/-- info: 'KCore.HooksIntTest.emod_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms emod_rule

/-- info: 'KCore.HooksIntTest.ediv_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ediv_rule

/-- info: 'KCore.HooksIntTest.int_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms int_only

end KCore.HooksIntTest
