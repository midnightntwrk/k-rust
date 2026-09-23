import KRustBridge.Json
import KRustBridge.SubsortJson
import KRust.TermAttributes
import KRust.SubsortEncoding

/-!
The models the bridge runs, by name. Each entry decodes the input with `KRustBridge.Json` (terms)
or `KRustBridge.SubsortJson` (order constraints), applies a definition imported from the `KRust`
library, and encodes the result. The definitions are the
ones the proofs are about; this library defines no model function of its own.

  "firstMacro": term ↦ `KRust.TermAttributes.firstMacro term`, a name or null; compared with
                the walk `Term::first_macro_or_alias_symbol` (term.rs), which
                `Term::macro_or_alias_symbol` runs when the stored flag is set.
  "findK":      term ↦ `KRust.TermAttributes.findK term []`, a list of terms; compared with the
                cells `find_k_cells` (rule.rs:789-840) pushes into an empty vector, as `rule_index`
                (rule.rs:766-777) calls it.
  "ceilFree":   [term, …] ↦ [`KRust.TermAttributes.ceilFree term`, …], one Boolean per term;
                the Rust sends every subterm of a generated term, and compares each answer with
                the stored attribute `TermAttributes::ceil_free`, which `Term::new` sets from
                term.rs `ceil_free`.
  "hasMacro":   [term, …] ↦ [`KRust.TermAttributes.hasMacro term`, …]; compared with the stored
                attribute `TermAttributes::has_macro_or_alias` (term.rs `has_macro_or_alias`) of
                every subterm.
  "kCells":     [term, …] ↦ [`KRust.TermAttributes.kCells term`, …]; compared with the stored
                attribute `TermAttributes::k_cells` (term.rs `k_cells`) of every subterm.
  "fetchK":     term ↦ `KRust.TermAttributes.fetchK term`, a term or null; compared with
                `rule::fetch_k_cell`, which `rule_index` runs when the stored count is 1.
  "lessThanEq": {relation, lesser, greater} ↦ `KRust.SubsortEncoding.new relation lesser greater`
                at `G = Nat` (`KRustBridge.SubsortJson`), a disjunction of conjunctions of
                equalities; compared with the formula `Encoding::less_than_eq` (z3_inference.rs)
                builds, read back from its Z3 AST.
  "fullDisjunction": {relation, lesser, greater} ↦ `KRust.SubsortEncoding.old relation lesser
                greater`; compared with `OrderRelation::full_disjunction` (z3_inference.rs), the
                formula `new_equiv` proves `new` equivalent to.
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
      return Json.arr ((KRust.TermAttributes.findK t []).map termToJson).toArray),
   ("ceilFree", fun input => do
      let ts ← (← input.getArr?).toList.mapM termFromJson
      return Json.arr (ts.map fun t => Json.bool (KRust.TermAttributes.ceilFree t)).toArray),
   ("hasMacro", fun input => do
      let ts ← (← input.getArr?).toList.mapM termFromJson
      return Json.arr (ts.map fun t => Json.bool (KRust.TermAttributes.hasMacro t)).toArray),
   ("kCells", fun input => do
      let ts ← (← input.getArr?).toList.mapM termFromJson
      return Json.arr (ts.map fun t => Lean.toJson (KRust.TermAttributes.kCells t)).toArray),
   ("fetchK", fun input => do
      let t ← termFromJson input
      return match KRust.TermAttributes.fetchK t with
        | some cell => termToJson cell
        | none => Json.null),
   ("lessThanEq", fun input => do
      let (relation, lesser, greater) ← orderRequestFromJson input
      return dnfToJson (KRust.SubsortEncoding.new relation lesser greater)),
   ("fullDisjunction", fun input => do
      let (relation, lesser, greater) ← orderRequestFromJson input
      return dnfToJson (KRust.SubsortEncoding.old relation lesser greater))]

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
