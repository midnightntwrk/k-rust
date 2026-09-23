import Lean.Data.Json
import KRust.SubsortEncoding

/-!
The JSON form of the order-constraint model `KRust.SubsortEncoding` at `G = Nat`, shared with the
Rust encoder `crates/k-rust/src/inner/parser/z3_inference/tests/lean_bridge.rs`.
A ground value is its index in the list of cached ground sort values the Rust test builds, so two
ground values are equal exactly when their indexes are; an expression that is not a cached ground
value is numbered by the test.

  side     = {"val": g} | {"other": n}                    (`Tm Nat`)
  request  = {"relation": [[l, r], …], "lesser": side, "greater": side}
  equality = [lhs, rhs]                                   (`Eqn Nat`, `lhs.eq(rhs)` in Rust)
  answer   = [[equality, …], …]                           (`Dnf Nat`: disjunction of conjunctions)

Decoding and encoding are harness code; no statement mentions them.
-/

namespace KRust.Bridge
open Lean (Json)
open KRust.SubsortEncoding

def sideFromJson (j : Json) : Except String (Tm Nat) :=
  match j.getObjValAs? Nat "val", j.getObjValAs? Nat "other" with
  | .ok g, .error _ => .ok (.val g)
  | .error _, .ok n => .ok (.other n)
  | _, _ =>
    .error s!"side: expected an object with one of the keys val and other, got {j.compress}"

def sideToJson : Tm Nat → Json
  | .val g   => Json.mkObj [("val", Lean.toJson g)]
  | .other n => Json.mkObj [("other", Lean.toJson n)]

def relationFromJson (j : Json) : Except String (List (Nat × Nat)) := do
  (← j.getArr?).toList.mapM fun pair => do
    match (← pair.getArr?).toList with
    | [l, r] => return (← l.getNat?, ← r.getNat?)
    | _      => throw s!"relation: expected a pair, got {pair.compress}"

def dnfToJson (d : Dnf Nat) : Json :=
  Json.arr (d.map fun c =>
    Json.arr (c.map fun e => Json.arr #[sideToJson e.lhs, sideToJson e.rhs]).toArray).toArray

/-- Decode a request into the relation and the two sides. -/
def orderRequestFromJson (j : Json) : Except String (List (Nat × Nat) × Tm Nat × Tm Nat) := do
  return (← relationFromJson (← j.getObjVal? "relation"),
          ← sideFromJson (← j.getObjVal? "lesser"),
          ← sideFromJson (← j.getObjVal? "greater"))

end KRust.Bridge
