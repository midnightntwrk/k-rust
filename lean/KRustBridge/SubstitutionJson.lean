import Lean.Data.Json
import KRust.SubstitutionSaturation

/-!
Conformance codec for the changed saturation schedule. Rust maps each ordered Variable
key to its ordinal, and each real Term in the case to its equality-class ID. The model
reads only key/value identity and map operations. The test callback supplies `answers`
in call order; its value is deliberately arbitrary, as in the universally quantified proof.
The codec and the Rust encoder do not run a copy of the saturation algorithm.
-/
namespace KRust.Bridge
open Lean (Json)
open KRust.SubstitutionSaturation

def bindingPairsToJson (pairs : List (Nat × Nat)) : Json :=
  Json.arr (pairs.map fun (key, value) => Json.arr #[Lean.toJson key, Lean.toJson value]).toArray

def saturationRequest (restoring : Bool) (input : Json) : Except String Json := do
  let initial ← (← (← input.getObjVal? "bindings").getArr?).toList.mapM fun item => do
    let #[key, value] ← item.getArr? | throw "binding: expected [key, value]"
    return (← key.getNat?, ← value.getNat?)
  let answers ← (← (← input.getObjVal? "answers").getArr?).toList.mapM (·.getNat?)
  let keys := initial.map Prod.fst
  let result := replay restoring initial answers
  return Json.mkObj [
    ("bindings", bindingPairsToJson (entries keys result.bindings)),
    ("cursor", Lean.toJson result.cursor),
    ("calls", Json.arr (result.calls.map fun call => Json.mkObj [
      ("key", Lean.toJson call.key), ("value", Lean.toJson call.value),
      ("others", bindingPairsToJson (entries keys call.others))]).toArray)]

end KRust.Bridge
