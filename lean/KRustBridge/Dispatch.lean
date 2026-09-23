import KRustBridge.Json
import KRust.TermAttributes

/-!
The models the bridge runs, by name. Each entry decodes the input with `KRustBridge.Json`, applies
a definition imported from the `KRust` library, and encodes the result. The definitions are the
ones the proofs are about; this library defines no model function of its own.

  "firstMacro": term ↦ `KRust.TermAttributes.firstMacro term`, a name or null; compared with
                `Term::macro_or_alias_symbol` (term.rs:808-816).
  "findK":      term ↦ `KRust.TermAttributes.findK term []`, a list of terms; compared with the
                cells `find_k_cells` (rule.rs:789-840) pushes into an empty vector, as `rule_index`
                (rule.rs:766-777) calls it.
-/

namespace KRust.Bridge
open Lean (Json)

/-- The models by name: input JSON to output JSON. -/
def models : List (String × (Json → Except String Json)) :=
  [("firstMacro", fun input => do
      let t ← termFromJson input
      return match KRust.TermAttributes.firstMacro t with
        | some name => Json.str name
        | none => Json.null),
   ("findK", fun input => do
      let t ← termFromJson input
      return Json.arr ((KRust.TermAttributes.findK t []).map termToJson).toArray)]

/-- Answer one request `{"id": n, "model": m, "input": x}` with `{"id": n, "output": y}`, or with
`{"id": n, "error": message}` when the request or its input does not decode. -/
def answer (line : String) : Json :=
  let request := Json.parse line
  let id := (request.toOption.bind fun j => (j.getObjVal? "id").toOption).getD Json.null
  let output : Except String Json := do
    let j ← request
    let name ← (← j.getObjVal? "model").getStr?
    let some (_, run) := models.find? (·.1 == name) | throw s!"unknown model {name}"
    run (← j.getObjVal? "input")
  match output with
  | .ok y    => Json.mkObj [("id", id), ("output", y)]
  | .error e => Json.mkObj [("id", id), ("error", e)]

end KRust.Bridge
