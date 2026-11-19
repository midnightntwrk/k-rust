/-
  K's FLOAT as a library module, and Float values, read from K 7.1.337 kompile's KORE. Run from the
  package root: `lake env lean test/FloatLib.lean`.
  - `f2-examples/flt.kompile.kore` (`flt.k`): FLOAT's 44 sentences carry the K installation's
    `domains.md` as `Source`; each is a sentence of the library's module FLOAT up to its place
    (`kBuiltinModule?`), so FLOAT is imported: nothing refused or unaccounted, FLOAT whole.
  - with one FLOAT sentence dropped (`maxFloat`'s declaration): read, and the account names the
    module's missing sentence (`builtinIncomplete`, FLOAT); with `isNaN`'s `total` and
    `functional` dropped: no sentence of the library, refused (`builtinText`).
  - `f2-examples/flt-lit.kompile.kore` (`flt-lit.k`): a Float literal `0.0`, read as binary64's +0.
  - Float literals read (`Parse.floatLit?`): the decimal value rounded to the nearest datum of the
    format, the sign after, where K's text states which that is (refused at a tie, above the
    largest finite datum, and nonzero rounding to zero); the suffixes `f` (binary32), none or `d` (binary64), `pNxM`;
    `Infinity`, `NaN` (the canonical NaN). The literal's text (`Lit.text`, `KFloat.text`) is its
    exact decimal value with its format, which reads back to the same literal.
  - FLOAT's interpreted operations on concrete values, in the kernel (`hook`): `0.1 + 0.2`, `1 / 3`,
    subnormals and ties, no value where K's text states none (above the largest finite datum, a
    zero result of unstated sign, an infinite or NaN operand, an inexact `Int2Float` or `sqrtFloat`), signed zeros
    and NaN compared, binary32, two formats, rounding to integral, `Int2Float`, `%Float`,
    `sqrtFloat`, the format's properties.
  - in the kernel, for `f2-examples/fltadd.kompile.kore` (`fltadd.k`: `Number ::= Int | Float`, a
    Float literal `0.5`): `Float < Number` is read, `coreOK`, `inj{Float,Number}(0.5)` is a value
    of `Number`, and `add(0.1, 0.2)` steps to `done` of the computed sum.
  As evidence only (not the definition): the encodings agree with Lean's `Float` on binary64.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- The text with the user module's sentences edited by `f`. -/
def editUser (f : Kore.Sentence → Option Kore.Sentence) (k : Kore.Definition) : Kore.Definition :=
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.filterMap f }]).getD [] }

/-- Without the hooked symbol `n`'s declaration. -/
def dropHooked (n : String) : Kore.Sentence → Option Kore.Sentence
  | .hookedSymbol x => if x.symbol.ident.ident.name == n then none else some (.hookedSymbol x)
  | s => some s

/-- The hooked symbol `n` without its `total` and `functional` attributes. -/
def untotal (n : String) : Kore.Sentence → Option Kore.Sentence
  | .hookedSymbol x => if x.symbol.ident.ident.name == n then
      some (.hookedSymbol { x with attributes := x.attributes.filter fun a =>
        a.head.ident.name != "total" && a.head.ident.name != "functional" })
    else some (.hookedSymbol x)
  | s => some s

/-- The reader's verdict on the text at `path` (edited by `edit`). -/
def verdict (path : String) (edit : Kore.Definition → Kore.Definition := id) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let k := edit k
    return match Parse.parse k with
      | .ok d => s!"read; unaccounted {(Parse.unconsumed k d).map (·.detail)}; missing {(Parse.missingBuiltin k d).map (·.head)}"
      | .error r => s!"{r.reason.name}{if r.detail.isEmpty then "" else " " ++ r.detail}"

/--
info: read; unaccounted []; missing []
read; unaccounted []; missing [FLOAT]
builtinText
read; unaccounted []; missing []
read; unaccounted []; missing []
-/
#guard_msgs in
#eval show IO Unit from do
  let f := "f2-examples/flt.kompile.kore"
  IO.println (← verdict f)
  IO.println (← verdict f (editUser (dropHooked "LblmaxFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float")))
  IO.println (← verdict f (editUser (untotal "LblisNaN'LParUndsRParUnds'FLOAT'Unds'Bool'Unds'Float")))
  IO.println (← verdict "f2-examples/flt-lit.kompile.kore")
  IO.println (← verdict "f2-examples/fltadd.kompile.kore")

/-! ## Literals, decided in the kernel -/

/-- binary64 `0.1`: the nearest double, `0x3FB999999999999A`. -/
example : Parse.floatLit? "0.1" = some (.float 53 11 0x3FB999999999999A) := by decide +kernel
/-- `666.0`, `6.66e2` and `666` are one value. -/
example : Parse.floatLit? "666.0" = some (.float 53 11 0x4084D00000000000) ∧
    Parse.floatLit? "6.66e2" = Parse.floatLit? "666.0" ∧ Parse.floatLit? "666d" = Parse.floatLit? "666.0" := by
  decide +kernel
/-- `-0.0` is negative zero, distinct from `0.0`. -/
example : Parse.floatLit? "-0.0" = some (.float 53 11 0x8000000000000000) ∧
    Parse.floatLit? "0.0" = some (.float 53 11 0) := by decide +kernel
/-- binary32 `1.5e3f` = 1500 = `0x44BB8000`; `0.1f` = `0x3DCCCCCD`. -/
example : Parse.floatLit? "1.5e3f" = some (.float 24 8 0x44BB8000) ∧
    Parse.floatLit? "0.1f" = some (.float 24 8 0x3DCCCCCD) := by decide +kernel
/-- The explicit format `p24x8` is binary32. -/
example : Parse.floatLit? "0.1p24x8" = Parse.floatLit? "0.1f" := by decide +kernel
/-- `Infinity`, `-Infinity`, `NaN` (the canonical quiet NaN); a decimal above the largest finite
datum, or nonzero and rounding to zero, is refused (K's text does not say whether an infinity or
which zero is its nearest value). -/
example : Parse.floatLit? "Infinity" = some (.float 53 11 0x7FF0000000000000) ∧
    Parse.floatLit? "-Infinityf" = some (.float 24 8 0xFF800000) ∧
    Parse.floatLit? "NaN" = some (.float 53 11 0x7FF8000000000000) ∧
    Parse.floatLit? "1e400" = none ∧
    Parse.floatLit? "4.9e-324" = some (.float 53 11 1) ∧
    Parse.floatLit? "1e-400" = none := by decide +kernel
/-- Not a Float literal: no digit, a format without a model. -/
example : Parse.floatLit? "." = none ∧ Parse.floatLit? "1.0p1x8" = none ∧ Parse.floatLit? "abc" = none := by
  decide +kernel

/-! One case per production of FLOAT-SYNTAX (domains.md:1495-1497) and the strings outside every
production (the kk entry t90-float-literal-forms, krs/semantics/kore/texts): construct table E6
row token:SortFloat. -/

/-- The decimal production's second alternative, `.d+`, unsigned, with an exponent and a suffix. -/
example : Parse.floatLit? ".5" = some (.float 53 11 0x3FE0000000000000) ∧
    Parse.floatLit? ".5e2" = some (.float 53 11 0x4049000000000000) ∧
    Parse.floatLit? ".5f" = some (.float 24 8 0x3F000000) := by
  decide +kernel
/-- The decimal production's first alternative: a sign before digits, a point with or without a
fraction, an exponent, the suffix letters in either case (`1.0P24X8` is binary32's 1, as `1.0f` and
`1.0p24x8` are). -/
example : Parse.floatLit? "+1.5" = some (.float 53 11 0x3FF8000000000000) ∧
    Parse.floatLit? "-1.5" = some (.float 53 11 0xBFF8000000000000) ∧
    Parse.floatLit? "1e3" = some (.float 53 11 0x408F400000000000) ∧
    Parse.floatLit? "1." = Parse.floatLit? "1.0" ∧ Parse.floatLit? "1.0D" = Parse.floatLit? "1.0" ∧
    Parse.floatLit? "1.0P24X8" = some (.float 24 8 0x3F800000) ∧
    Parse.floatLit? "1.0p24x8" = Parse.floatLit? "1.0P24X8" ∧ Parse.floatLit? "1.0F" = Parse.floatLit? "1.0P24X8" ∧
    Parse.floatLit? "1.0P53x11" = Parse.floatLit? "1.0" := by
  decide +kernel
/-- The production `[+-]?Infinity` with a suffix. -/
example : Parse.floatLit? "+Infinity" = some (.float 53 11 0x7FF0000000000000) ∧
    Parse.floatLit? "-InfinityD" = some (.float 53 11 0xFFF0000000000000) ∧
    Parse.floatLit? "-Infinityp24x8" = some (.float 24 8 0xFF800000) ∧
    Parse.floatLit? "InfinityP24X8" = some (.float 24 8 0x7F800000) := by
  decide +kernel
/-- The production `NaN` with a suffix, unsigned: the format's canonical NaN. -/
example : Parse.floatLit? "NaNf" = some (.float 24 8 0x7FC00000) ∧
    Parse.floatLit? "NaNP24X8" = Parse.floatLit? "NaNf" ∧ Parse.floatLit? "NaNd" = Parse.floatLit? "NaN" := by
  decide +kernel
/-- Outside every production: a sign before a mantissa without an integer part, a signed NaN, a
`p` without its `x` and an `x` without its `p`. -/
example : Parse.floatLit? "+.5" = none ∧ Parse.floatLit? "-.5" = none ∧ Parse.floatLit? "-.5e2" = none ∧
    Parse.floatLit? "+NaN" = none ∧ Parse.floatLit? "-NaN" = none ∧
    Parse.floatLit? "1.0p24" = none ∧ Parse.floatLit? "1.0x8" = none := by
  decide +kernel

/-! ### Reading a decimal text by its parts

`Parse.floatLit?` on the text of the least subnormal binary64 datum (763 characters) is read through
the lemmas below rather than by one kernel decision: the suffix `p53x11` after a body without `p`
or `P` names binary64, and digits then `e-` then digits are the decimal `m·10^(-k)`; what is left
to decide is the rounding of that decimal. -/

namespace KCore.FloatLibRead

/-- After a body with no `p` or `P`, the suffix `p53x11` names binary64 and leaves the body. -/
theorem floatSuffix_p53x11 {body : List Char} (h : ∀ c ∈ body, c ≠ 'p' ∧ c ≠ 'P') :
    Parse.floatSuffix (body ++ ['p', '5', '3', 'x', '1', '1']) = some (body, 53, 11) := by
  have hall : ∀ c ∈ body, (!(c == 'p' || c == 'P')) = true := by
    intro c hc; obtain ⟨h1, h2⟩ := h c hc; simp [h1, h2]
  have hany : (body ++ ['p', '5', '3', 'x', '1', '1']).any (fun c => c == 'p' || c == 'P') = true := by
    simp
  unfold Parse.floatSuffix
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  simp only [hany, ↓reduceIte]
  rw [List.takeWhile_append_of_pos hall, List.dropWhile_append_of_pos hall]
  have ht : List.takeWhile (fun a => !(a == 'p' || a == 'P')) ['p', '5', '3', 'x', '1', '1'] = [] := by decide
  rw [ht, List.append_nil]
  rfl

/-- The digits of `m`, `e-`, the digits of `k`: the decimal `m·10^(-k)`. -/
theorem decimal?_digits_exp (M k : Nat) :
    Parse.decimal? (Nat.toDigits 10 M ++ 'e' :: '-' :: Nat.toDigits 10 k) = some (M, -(k : Int)) := by
  obtain ⟨h1, h2⟩ := KFloat.takeWhile_digits M 'e' ('-' :: Nat.toDigits 10 k) (by decide)
  obtain ⟨d, ds, hd, -, -⟩ := toDigits_head M
  obtain ⟨d', ds', hd', -, -⟩ := toDigits_head k
  unfold Parse.decimal?
  simp only [h1, h2]
  simp only [hd, List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i heq; simp at heq
  · rw [← hd, List.append_nil, digitsVal_toDigits]
    simp only [Option.bind_some, Parse.expPart?, Parse.expDigits?, hd', List.isEmpty_cons]
    simp [← hd', digitsVal_toDigits]

/-- A text that is the digits of `m`, `e-`, the digits of `k`, then `p53x11` reads as binary64's
rounding of `m·10^(-k)` (unsigned: the body starts with a digit). -/
theorem floatLit?_dec53 {t : String} {M k : Nat}
    (h : t.toList = (Nat.toDigits 10 M ++ 'e' :: '-' :: Nat.toDigits 10 k) ++ ['p', '5', '3', 'x', '1', '1']) :
    Parse.floatLit? t = (do
      let s ← KFloat.spec? 53 11
      let s' ← KFloat.spec? 54 11
      let u ← KFloat.ofDecimal? s s' M (-(k : Int))
      pure (.float 53 11 (KFloat.packBits s u))) := by
  have hb : ∀ c ∈ Nat.toDigits 10 M ++ 'e' :: '-' :: Nat.toDigits 10 k, c ≠ 'p' ∧ c ≠ 'P' := by
    intro c hc
    simp only [List.mem_append, List.mem_cons] at hc
    rcases hc with hc | rfl | rfl | hc
    · have := KFloat.digit_of_mem hc; constructor <;> (rintro rfl; cases this)
    · decide
    · decide
    · have := KFloat.digit_of_mem hc; constructor <;> (rintro rfl; cases this)
  unfold Parse.floatLit?
  rw [h, floatSuffix_p53x11 hb]
  obtain ⟨d, r, hdr, hd⟩ := KFloat.digits_head M ('e' :: '-' :: Nat.toDigits 10 k)
  have hm1 : d ≠ '-' := by rintro rfl; cases hd
  have hm2 : d ≠ '+' := by rintro rfl; cases hd
  have hn : (d :: r == "NaN".toList) = false := by
    simp only [beq_eq_false_iff_ne]; rintro ⟨⟩; cases hd
  have hi : (d :: r == "Infinity".toList) = false := by
    simp only [beq_eq_false_iff_ne]; rintro ⟨⟩; cases hd
  have hdec := decimal?_digits_exp M k
  rw [hdr] at hdec ⊢
  obtain ⟨s0, hs0⟩ : ∃ s, KFloat.spec? 53 11 = some s := ⟨_, rfl⟩
  obtain ⟨s1, hs1⟩ : ∃ s, KFloat.spec? 54 11 = some s := ⟨_, rfl⟩
  -- the sign split of `floatLit?` (its compiled matcher is `expDigits?`'s, which has the same patterns)
  have hq : Parse.expDigits?.match_1 (fun _ => Bool × List Char) (d :: r) (fun r => (true, r))
      (fun r => (false, r)) (fun r => (false, r)) = (false, d :: r) := by
    split
    · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 hm1
    · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 hm2
    · rfl
  simp only [Option.bind_eq_bind, Option.bind_some, hs0, show 53 + 1 = 54 from rfl, hs1, hn, hi, hq, hdec,
    Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, Bool.false_and]

/-- The text of the least subnormal binary64 datum (encoding 1): `5^1074` written out, `e-1074`,
`p53x11` (`KFloat.text`: significand 1, exponent field 0 read as 1, shift 1075). -/
theorem text_least_subnormal :
    (Lit.text (.float 53 11 1)).toList =
      (Nat.toDigits 10 (1 * 5 ^ 1074) ++ 'e' :: '-' :: Nat.toDigits 10 1074) ++ ['p', '5', '3', 'x', '1', '1'] := by
  show (KFloat.text 53 11 1).toList = _
  rw [KFloat.text_eq]
  have hf : KFloat.fields 53 11 1 = (0, 0, 1) := by decide
  have hb : (KFloat.body 53 11 1).toList = (KFloat.magText 53 11 0 1).toList := by
    unfold KFloat.body
    rw [hf]
    simp
  rw [hb, KFloat.magText_toList]
  have hs : KFloat.sig 53 0 1 = 1 := by decide
  have hsh : KFloat.shift 53 11 = 1075 := by decide
  have he : KFloat.expo 0 = 1 := by decide
  have h53 : Nat.toDigits 10 53 = ['5', '3'] := by decide
  have h11 : Nat.toDigits 10 11 = ['1', '1'] := by decide
  simp only [hs, hsh, he, h53, h11, Nat.reduceSub, Nat.reduceLeDiff, Nat.one_ne_zero, ↓reduceIte,
    List.append_assoc, List.cons_append, List.nil_append]

end KCore.FloatLibRead

/-- The text of a literal is its exact decimal value with its format (`m·5^k` then `e-k`, or an
integer of the format's top binade with `.0`), and reads back to it. -/
example : Lit.text (.float 53 11 0x3FB999999999999A) =
      "10000000000000000555111512312578270211815834045410156250e-56p53x11" ∧
    Parse.floatLit? "10000000000000000555111512312578270211815834045410156250e-56p53x11" =
      some (.float 53 11 0x3FB999999999999A) ∧
    Lit.text (.float 24 8 0x44BB8000) = "15000000000000000e-13p24x8" ∧
    Lit.text (.float 53 11 0x4340000000000000) = "9007199254740992.0p53x11" ∧
    Lit.text (.float 53 11 0x8000000000000000) = "-0.0p53x11" ∧
    Lit.text (.float 24 8 0xFF800000) = "-Infinityp24x8" ∧
    Lit.text (.float 53 11 0x7FF8000000000000) = "NaNp53x11" ∧
    Parse.floatLit? (Lit.text (.float 53 11 1)) = some (.float 53 11 1) ∧
    Parse.floatLit? (Lit.text (.float 53 11 0x4084D00000000000)) = some (.float 53 11 0x4084D00000000000) := by
  rw [KCore.FloatLibRead.floatLit?_dec53 KCore.FloatLibRead.text_least_subnormal]
  decide_cheap

/-- A NaN other than the canonical one is no value; a pattern beyond the format's bits neither. -/
example : dvOK {} Srt.float (.float 53 11 0x7FF8000000000001) = false ∧
    dvOK {} Srt.float (.float 53 11 0x7FF8000000000000) = true ∧
    dvOK {} Srt.float (.float 24 8 (2 ^ 32)) = false := by decide +kernel

/-! ## Evidence: agreement with Lean's `Float` on binary64 -/

example : (Parse.floatLit? "0.1") = some (.float 53 11 (0.1 : Float).toBits.toNat) ∧
    (Parse.floatLit? "666.0") = some (.float 53 11 (666.0 : Float).toBits.toNat) ∧
    (Parse.floatLit? "4.9e-324") = some (.float 53 11 (4.9e-324 : Float).toBits.toNat) := by decide +kernel


/-! ## Operations, decided in the kernel (IEEE 754: the exact result rounded to nearest, ties even) -/

def f64 (b : Nat) : GroundTerm := .dv Srt.float (.float 53 11 b)
def f32 (b : Nat) : GroundTerm := .dv Srt.float (.float 24 8 b)

/-- `0.1 + 0.2` is the double next above `0.3`'s, `0x3FD3333333333334`; `1 / 3`. -/
example : hook floatAdd [f64 0x3FB999999999999A, f64 0x3FC999999999999A] = some (some (f64 0x3FD3333333333334)) ∧
    hook floatDiv [f64 0x3FF0000000000000, f64 0x4008000000000000] = some (some (f64 0x3FD5555555555555)) := by
  decide +kernel
/-- Above the largest finite datum, no value: `1e308 * 10`. -/
example : hook floatMul [f64 0x7FE1CCF385EBC8A0, f64 0x4024000000000000] = some none := by
  decide +kernel
/-- Subnormals: the smallest normal over 4; three times the smallest subnormal over 2 is a tie,
rounded to the even 2; the smallest subnormal over 2 rounds to zero, of a sign the text does not
give: no value. -/
example : hook floatDiv [f64 0x0010000000000000, f64 0x4010000000000000] = some (some (f64 0x0004000000000000)) ∧
    hook floatDiv [f64 1, f64 0x4000000000000000] = some none ∧
    hook floatDiv [f64 3, f64 0x4000000000000000] = some (some (f64 2)) := by decide +kernel
/-- No value at a zero divisor or an infinite operand: `0 / 0`, `∞ − ∞`. -/
example : hook floatDiv [f64 0, f64 0] = some none ∧
    hook floatSub [f64 0x7FF0000000000000, f64 0x7FF0000000000000] = some none := by
  decide +kernel
/-- Signed zeros compare equal, though they are two values; NaN is unordered, even with itself. -/
example : hook floatEq [f64 0x8000000000000000, f64 0] = some (some (bool true)) ∧
    hook floatLt [f64 0x8000000000000000, f64 0] = some (some (bool false)) ∧
    hook floatEq [f64 0x7FF8000000000000, f64 0x7FF8000000000000] = some (some (bool false)) ∧
    hook floatNe [f64 0x7FF8000000000000, f64 0x7FF8000000000000] = some (some (bool true)) ∧
    hook floatLe [f64 0x7FF8000000000000, f64 0] = some (some (bool false)) := by decide +kernel
/-- binary32: `0.1f + 0.2f` is `0x3E99999A`; `roundFloat` of binary64's `1.5` to binary32 is `1.5f`,
which binary32 holds; of binary64's `1 / 3`, which it does not hold, no value (the text names no
direction to round in). -/
example : hook floatAdd [f32 0x3DCCCCCD, f32 0x3E4CCCCD] = some (some (f32 0x3E99999A)) ∧
    hook floatRound [f64 0x3FF8000000000000, int 24, int 8] = some (some (f32 0x3FC00000)) ∧
    hook floatRound [f64 0x3FD5555555555555, int 24, int 8] = some none := by decide +kernel
/-- Two formats: compared by their exact values (`1.0 == 1.0f`, `0.1 < 0.1f`); added, undefined. -/
example : hook floatEq [f64 0x3FF0000000000000, f32 0x3F800000] = some (some (bool true)) ∧
    hook floatLt [f64 0x3FB999999999999A, f32 0x3DCCCCCD] = some (some (bool true)) ∧
    hook floatAdd [f64 0x3FF0000000000000, f32 0x3F800000] = some none := by decide +kernel
/-- Rounding to integral: `floor(-2.5) = -3`, `trunc(2.7) = 2`; `ceil(-0.5)` and `floor(0.5)`, a zero
of a sign the text does not give: no value. -/
example : hook floatFloor [f64 0xC004000000000000] = some (some (f64 0xC008000000000000)) ∧
    hook floatCeil [f64 0xBFE0000000000000] = some none ∧
    hook floatTrunc [f64 0x400599999999999A] = some (some (f64 0x4000000000000000)) ∧
    hook floatFloor [f64 0x3FE0000000000000] = some none := by decide +kernel
/-- `Int2Float(2^53 + 1, 53, 11)`, which binary64 does not hold: no value; `5 %Float 3 = -1`; at
precision 1 and 8 exponent bits, `Int2Float(1, 1, 8)` is `1.0p1x8` (the exponent field 127, no
significand field); at precision 24 and one exponent bit, `Int2Float(1, 24, 1)` is `1.0p24x1` (bias
0, every finite datum subnormal: the significand field 2^22, 2^22·2^-22). -/
example : hook int2Float [int 9007199254740993, int 53, int 11] = some none ∧
    hook floatRem [f64 0x4014000000000000, f64 0x4008000000000000] = some (some (f64 0xBFF0000000000000)) ∧
    hook int2Float [int 1, int 1, int 8] = some (some (.dv Srt.float (.float 1 8 127))) ∧
    hook int2Float [int 1, int 24, int 1] = some (some (.dv Srt.float (.float 24 1 (2 ^ 22)))) := by
  decide +kernel
/-- `sqrtFloat` where the format holds the root: `sqrtFloat(4.0) = 2.0`, `sqrtFloat(2.25) = 1.5`,
binary32's `sqrtFloat(9.0f) = 3.0f`, the least subnormal `2^-1074` to the normal `2^-537`. No value
at a root the format does not hold (`sqrtFloat(2.0)`, the subnormal `2^-1073`), at NaN, at `-1.0`
and `-Infinity`, at `+Infinity`, and at `+0.0` and `-0.0` (a zero of a sign the text does not
give). -/
example : hook floatSqrt [f64 0x4010000000000000] = some (some (f64 0x4000000000000000)) ∧
    hook floatSqrt [f64 0x4002000000000000] = some (some (f64 0x3FF8000000000000)) ∧
    hook floatSqrt [f32 0x41100000] = some (some (f32 0x40400000)) ∧
    hook floatSqrt [f64 1] = some (some (f64 0x1E60000000000000)) ∧
    hook floatSqrt [f64 0] = some none ∧
    hook floatSqrt [f64 0x4000000000000000] = some none ∧
    hook floatSqrt [f64 2] = some none ∧
    hook floatSqrt [f64 0x7FF8000000000000] = some none ∧
    hook floatSqrt [f64 0xBFF0000000000000] = some none ∧
    hook floatSqrt [f64 0xFFF0000000000000] = some none ∧
    hook floatSqrt [f64 0x7FF0000000000000] = some none ∧
    hook floatSqrt [f64 0x8000000000000000] = some none := by decide_cheap
/-- Tests and the format: `isNaN`, `isInfinite`, precision, exponent width, the largest finite and
the smallest positive value. -/
example : hook floatIsNaN [f64 0x7FF8000000000000] = some (some (bool true)) ∧
    hook floatIsInfinite [f64 0xFFF0000000000000] = some (some (bool true)) ∧
    hook floatPrecision [f32 0] = some (some (int 24)) ∧ hook floatExponentBits [f64 0] = some (some (int 11)) ∧
    hook floatMaxValue [int 53, int 11] = some (some (f64 0x7FEFFFFFFFFFFFFF)) ∧
    hook floatMinValue [int 53, int 11] = some (some (f64 1)) := by decide +kernel

/-! ## Evidence: agreement with Lean's `Float` on binary64 -/

example : hook floatAdd [f64 (0.1 : Float).toBits.toNat, f64 (0.2 : Float).toBits.toNat] =
      some (some (f64 ((0.1 : Float) + 0.2).toBits.toNat)) ∧
    hook floatDiv [f64 (1.0 : Float).toBits.toNat, f64 (3.0 : Float).toBits.toNat] =
      some (some (f64 ((1.0 : Float) / 3.0).toBits.toNat)) ∧
    hook floatSqrt [f64 (2.25 : Float).toBits.toNat] = some (some (f64 (Float.sqrt 2.25).toBits.toNat)) := by
  decide +kernel

/-! ## `fltadd`: Float below a sort of the definition, a literal as a value -/

namespace FltAdd

definition_of defn from "f2-examples/fltadd.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- `Number`, the definition's first own sort after its cells. -/
noncomputable def number : Srt := (c.userSorts.find? fun s => c.sortName s == "Number").getD 0

theorem subsort : (c.subsorts.contains (Srt.float, number)) = true := by decide +kernel

/-- `inj{Float,Number}(0.5)` is a value of `Number`. -/
theorem half_value :
    c.sortOf (.inj Srt.float number (.dv Srt.float (.float 53 11 0x3FE0000000000000))) = some number := by
  decide +kernel


/-- The definition's symbols the step names, by number. -/
def kCell : Sym := 384
def addL : Sym := 386
def doneL : Sym := 387
def cmdS : Srt := 33

theorem names_ok : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName addL = "Lbladd" ∧ c.symName doneL = "Lbldone" ∧
    c.sortName cmdS = "Cmd" ∧ number = 32 := by decide +kernel

theorem ok : c.ok = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem matchReady : c.matchReady = true := by decide +kernel
theorem coherent : CoherentAll c :=
  Det.coherentAll_of_nil ok srReady matchReady (by decide +kernel) (by decide +kernel)

def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj cmdS Srt.kitem st, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

def num (b : Nat) : GroundTerm := .inj Srt.float 32 (f64 b)

def Add : Config c := ⟨cfg (.ctor addL [num 0x3FB999999999999A, num 0x3FC999999999999A]), by decide +kernel⟩
def Done : Config c := ⟨cfg (.ctor doneL [num 0x3FD3333333333334]), by decide +kernel⟩

/-- `add(0.1, 0.2)` steps to `done(0x3FD3333333333334)`, the sum computed by `+Float`. -/
theorem step_add : Step c Add Done :=
  (Exec.step_iff_of_ok c ok srReady matchReady coherent _ _).mpr ⟨100, by decide +kernel⟩

tables_of T from "f2-examples/fltadd.kompile.kore"

theorem T_eq : T = tables c := by decide +kernel

set_option maxHeartbeats 1000000 in
open Faithful Faithful.Model in
/-- `coreOK`, conjunct by conjunct, the sort checks from the tables. -/
theorem coreOK : c.coreOK = true :=
  Semantics.coreOK_of_T T_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide_cheap)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FltAdd

#print axioms FltAdd.subsort
#print axioms FltAdd.half_value
#print axioms FltAdd.coreOK
#print axioms FltAdd.step_add
