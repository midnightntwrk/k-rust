/-! A stand-in for an external library (a hash, an encoding): a pure Lean function with a lemma,
written without any knowledge of k2lean. -/

namespace HexLib

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

/-- Lower-case hexadecimal of a byte string, two characters per byte. -/
def toHex (bs : List UInt8) : String :=
  String.ofList (bs.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

theorem toHex_nil : toHex [] = "" := rfl

end HexLib
