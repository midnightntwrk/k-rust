import Params.Functions
import HexLib

/-! The user's assumption: `Params`'s hooks, implemented by an external library. -/

namespace Consumer

/-- `Bytes2Hex` is HexLib's encoder; `oracle` (a function K gives no equations) is a constant. -/
@[instance_reducible] def hooks : Params.Hooks where
  «BYTES.bytes2hex» b := some (HexLib.toHex b)
  «fn.oracle(_)_PARAMS_Int_Int» _ := some 7

end Consumer
