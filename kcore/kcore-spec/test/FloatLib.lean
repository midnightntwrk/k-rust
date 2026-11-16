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
  - Float literals read (`Parse.floatLit?`): the decimal value rounded to the format, nearest ties
    to even, the sign after; the suffixes `f` (binary32), none or `d` (binary64), `pNxM`;
    `Infinity`, `NaN` (the canonical NaN). The literal's text (`Lit.text`, `KFloat.text`) is its
    exact decimal value with its format, which reads back to the same literal.
  - FLOAT's interpreted operations on concrete values, in the kernel (`hook`): `0.1 + 0.2`, `1 / 3`,
    overflow, subnormals and ties, the canonical NaN, signed zeros and NaN compared, binary32, two
    formats, rounding to integral, `Int2Float`, `%Float`, `sqrtFloat`, the format's properties.
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
/-- `Infinity`, `-Infinity`, `NaN` (the canonical quiet NaN), and overflow and underflow of a
decimal. -/
example : Parse.floatLit? "Infinity" = some (.float 53 11 0x7FF0000000000000) ∧
    Parse.floatLit? "-Infinityf" = some (.float 24 8 0xFF800000) ∧
    Parse.floatLit? "NaN" = some (.float 53 11 0x7FF8000000000000) ∧
    Parse.floatLit? "1e400" = some (.float 53 11 0x7FF0000000000000) ∧
    Parse.floatLit? "4.9e-324" = some (.float 53 11 1) ∧
    Parse.floatLit? "1e-400" = some (.float 53 11 0) := by decide +kernel
/-- Not a Float literal: no digit, a format without a model. -/
example : Parse.floatLit? "." = none ∧ Parse.floatLit? "1.0p1x8" = none ∧ Parse.floatLit? "abc" = none := by
  decide +kernel

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
  decide +kernel

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
/-- Overflow to `+∞`: `1e308 * 10`. -/
example : hook floatMul [f64 0x7FE1CCF385EBC8A0, f64 0x4024000000000000] = some (some (f64 0x7FF0000000000000)) := by
  decide +kernel
/-- Subnormals: the smallest normal over 4; the smallest subnormal over 2 is a tie, rounded to the
even `+0`; three times it over 2 is a tie, rounded to the even 2. -/
example : hook floatDiv [f64 0x0010000000000000, f64 0x4010000000000000] = some (some (f64 0x0004000000000000)) ∧
    hook floatDiv [f64 1, f64 0x4000000000000000] = some (some (f64 0)) ∧
    hook floatDiv [f64 3, f64 0x4000000000000000] = some (some (f64 2)) := by decide +kernel
/-- NaN is the canonical NaN: `0 / 0`, `∞ − ∞`. -/
example : hook floatDiv [f64 0, f64 0] = some (some (f64 0x7FF8000000000000)) ∧
    hook floatSub [f64 0x7FF0000000000000, f64 0x7FF0000000000000] = some (some (f64 0x7FF8000000000000)) := by
  decide +kernel
/-- Signed zeros compare equal, though they are two values; NaN is unordered, even with itself. -/
example : hook floatEq [f64 0x8000000000000000, f64 0] = some (some (bool true)) ∧
    hook floatLt [f64 0x8000000000000000, f64 0] = some (some (bool false)) ∧
    hook floatEq [f64 0x7FF8000000000000, f64 0x7FF8000000000000] = some (some (bool false)) ∧
    hook floatNe [f64 0x7FF8000000000000, f64 0x7FF8000000000000] = some (some (bool true)) ∧
    hook floatLe [f64 0x7FF8000000000000, f64 0] = some (some (bool false)) := by decide +kernel
/-- binary32: `0.1f + 0.2f` is `0x3E99999A`; `1 / 3` rounded to binary32 is `0x3EAAAAAB`. -/
example : hook floatAdd [f32 0x3DCCCCCD, f32 0x3E4CCCCD] = some (some (f32 0x3E99999A)) ∧
    hook floatRound [f64 0x3FD5555555555555, int 24, int 8] = some (some (f32 0x3EAAAAAB)) := by decide +kernel
/-- Two formats: compared by their exact values (`1.0 == 1.0f`, `0.1 < 0.1f`); added, undefined. -/
example : hook floatEq [f64 0x3FF0000000000000, f32 0x3F800000] = some (some (bool true)) ∧
    hook floatLt [f64 0x3FB999999999999A, f32 0x3DCCCCCD] = some (some (bool true)) ∧
    hook floatAdd [f64 0x3FF0000000000000, f32 0x3F800000] = some none := by decide +kernel
/-- Rounding to integral: `floor(-2.5) = -3`, `ceil(-0.5) = -0`, `trunc(2.7) = 2`, `floor(0.5) = +0`. -/
example : hook floatFloor [f64 0xC004000000000000] = some (some (f64 0xC008000000000000)) ∧
    hook floatCeil [f64 0xBFE0000000000000] = some (some (f64 0x8000000000000000)) ∧
    hook floatTrunc [f64 0x400599999999999A] = some (some (f64 0x4000000000000000)) ∧
    hook floatFloor [f64 0x3FE0000000000000] = some (some (f64 0)) := by decide +kernel
/-- `Int2Float(2^53 + 1, 53, 11)` is a tie, rounded to the even `2^53`; `5 %Float 3 = -1`;
`sqrtFloat(2)`, `sqrtFloat(4.0) = 2.0`, `sqrtFloat(+0.0) = +0.0`, `sqrtFloat(-1.0)` NaN, no value
at `sqrtFloat(-0.0)` (squareRoot gives −0, rootn(−0, 2) +0); a format without a model gives no value. -/
example : hook int2Float [int 9007199254740993, int 53, int 11] = some (some (f64 0x4340000000000000)) ∧
    hook floatRem [f64 0x4014000000000000, f64 0x4008000000000000] = some (some (f64 0xBFF0000000000000)) ∧
    hook floatSqrt [f64 0x4000000000000000] = some (some (f64 0x3FF6A09E667F3BCD)) ∧
    hook floatSqrt [f64 0x4010000000000000] = some (some (f64 0x4000000000000000)) ∧
    hook floatSqrt [f64 0] = some (some (f64 0)) ∧
    hook floatSqrt [f64 0xBFF0000000000000] = some (some (f64 0x7FF8000000000000)) ∧
    hook floatSqrt [f64 0x8000000000000000] = some none ∧
    hook int2Float [int 1, int 1, int 8] = some none := by decide +kernel
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
    hook floatMul [f64 (1.0e308 : Float).toBits.toNat, f64 (10.0 : Float).toBits.toNat] =
      some (some (f64 ((1.0e308 : Float) * 10.0).toBits.toNat)) ∧
    hook floatSqrt [f64 (2.0 : Float).toBits.toNat] = some (some (f64 (Float.sqrt 2.0).toBits.toNat)) := by
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
def kCell : Sym := 380
def addL : Sym := 382
def doneL : Sym := 383
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
    (Semantics.faithCoreOK_of_parts (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FltAdd

#print axioms FltAdd.subsort
#print axioms FltAdd.half_value
#print axioms FltAdd.coreOK
#print axioms FltAdd.step_add
