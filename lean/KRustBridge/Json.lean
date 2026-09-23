import Lean.Data.Json
import KRust.TermAttributes

/-!
The JSON form of the term model `KRust.TermAttributes.Term`, shared with the Rust encoder
`crates/k-rust-backend/src/tests/lean_bridge/term_json.rs`. One object per node, keyed by the
`TermKind` variant (term.rs:227-259):

  {"and": [l, r]}
  {"app": {"symbol": sym, "sorts": [s, …], "args": [t, …]}}
  {"dv": {"sort": s, "value": hex}}
  {"var": {"kind": "element" | "set", "sort": s, "name": n}}
  {"inj": {"source": s, "target": s, "term": t}}
  {"map": {"definition": d, "entries": [[k, v], …], "rest": t | null}}
  {"list": {"definition": d, "heads": [t, …], "rest": null | {"middle": t, "tails": [t, …]}}}
  {"set": {"definition": d, "elements": [t, …], "rest": t | null}}

  sym = {"name": n, "type": "constructor" | "partial" | "total", "anywhere": b,
         "declaredFunction": b, "injective": b, "macroOrAlias": b, "other": s}

Every string is one field of the model; the Rust encoder chooses an injective rendering of each
Rust value (sorts, the domain-value bytes as hex, a collection definition, the symbol fields the
model keeps in `other`), and this codec copies the string unchanged in both directions.
For every `j` the Rust encoder produces, `termFromJson j = .ok t` and `termToJson t = j`, so an
answer that contains terms is compared with the Rust's encoding of its answer as JSON values.

Decoding and encoding are `partial` harness code; no statement mentions them.
-/

namespace KRust.Bridge
open Lean (Json)
open KRust.TermAttributes

private def field (j : Json) (k : String) : Except String Json := j.getObjVal? k

private def str (j : Json) (k : String) : Except String String := do (← field j k).getStr?

private def bool (j : Json) (k : String) : Except String Bool := do (← field j k).getBool?

private def arr (j : Json) (k : String) : Except String (List Json) := do
  return (← (← field j k).getArr?).toList

private def optional (j : Json) (k : String) : Except String (Option Json) :=
  match j.getObjVal? k with
  | .ok .null => .ok none
  | .ok v     => .ok (some v)
  | .error e  => .error e

def symFromJson (j : Json) : Except String Sym := do
  let symbolType ← match ← str j "type" with
    | "constructor" => pure SymbolType.constructor
    | "partial"     => pure (SymbolType.function .Partial)
    | "total"       => pure (SymbolType.function .Total)
    | other         => throw s!"symbol: unknown type {other}"
  return { name := ← str j "name", symbolType, anywhere := ← bool j "anywhere",
           declaredFunction := ← bool j "declaredFunction", injective := ← bool j "injective",
           macroOrAlias := ← bool j "macroOrAlias", other := ← str j "other" }

def symToJson (s : Sym) : Json :=
  Json.mkObj
    [("name", s.name),
     ("type", match s.symbolType with
       | .constructor => "constructor"
       | .function .Partial => "partial"
       | .function .Total => "total"),
     ("anywhere", s.anywhere), ("declaredFunction", s.declaredFunction),
     ("injective", s.injective), ("macroOrAlias", s.macroOrAlias), ("other", s.other)]

private def strings (js : List Json) : Except String (List String) := js.mapM (·.getStr?)

partial def termFromJson (j : Json) : Except String Term := do
  if let .ok a := j.getObjVal? "and" then
    let #[l, r] ← a.getArr? | throw "and: expected two operands"
    return .and (← termFromJson l) (← termFromJson r)
  if let .ok a := j.getObjVal? "app" then
    return .app (← symFromJson (← field a "symbol")) (← strings (← arr a "sorts"))
      (← (← arr a "args").mapM termFromJson)
  if let .ok d := j.getObjVal? "dv" then
    return .dv (← str d "sort") (← str d "value")
  if let .ok v := j.getObjVal? "var" then
    let kind ← match ← str v "kind" with
      | "element" => pure VarKind.element
      | "set"     => pure VarKind.set
      | other     => throw s!"var: unknown kind {other}"
    return .var kind (← str v "sort") (← str v "name")
  if let .ok i := j.getObjVal? "inj" then
    return .inj (← str i "source") (← str i "target") (← termFromJson (← field i "term"))
  if let .ok m := j.getObjVal? "map" then
    let entries ← (← arr m "entries").mapM fun e => do
      let #[k, v] ← e.getArr? | throw "map: expected a [key, value] pair"
      return (← termFromJson k, ← termFromJson v)
    return .map (← str m "definition") entries (← (← optional m "rest").mapM termFromJson)
  if let .ok l := j.getObjVal? "list" then
    let rest ← (← optional l "rest").mapM fun r => do
      return (← termFromJson (← field r "middle"), ← (← arr r "tails").mapM termFromJson)
    return .list (← str l "definition") (← (← arr l "heads").mapM termFromJson) rest
  if let .ok s := j.getObjVal? "set" then
    return .set (← str s "definition") (← (← arr s "elements").mapM termFromJson)
      (← (← optional s "rest").mapM termFromJson)
  throw s!"unknown term {j.compress}"

partial def termToJson : Term → Json
  | .and l r => Json.mkObj [("and", Json.arr #[termToJson l, termToJson r])]
  | .app s ss args => Json.mkObj [("app", Json.mkObj
      [("symbol", symToJson s), ("sorts", Json.arr (ss.map Json.str).toArray),
       ("args", Json.arr (args.map termToJson).toArray)])]
  | .dv sort value => Json.mkObj [("dv", Json.mkObj [("sort", sort), ("value", value)])]
  | .var k sort name => Json.mkObj [("var", Json.mkObj
      [("kind", match k with | .element => "element" | .set => "set"), ("sort", sort),
       ("name", name)])]
  | .inj s t u => Json.mkObj [("inj", Json.mkObj
      [("source", s), ("target", t), ("term", termToJson u)])]
  | .map d es rest => Json.mkObj [("map", Json.mkObj
      [("definition", d),
       ("entries", Json.arr (es.map fun (k, v) => Json.arr #[termToJson k, termToJson v]).toArray),
       ("rest", match rest with | some r => termToJson r | none => Json.null)])]
  | .list d hs rest => Json.mkObj [("list", Json.mkObj
      [("definition", d),
       ("heads", Json.arr (hs.map termToJson).toArray),
       ("rest", match rest with
         | some (m, ts) =>
             Json.mkObj [("middle", termToJson m), ("tails", Json.arr (ts.map termToJson).toArray)]
         | none => Json.null)])]
  | .set d es rest => Json.mkObj [("set", Json.mkObj
      [("definition", d),
       ("elements", Json.arr (es.map termToJson).toArray),
       ("rest", match rest with | some r => termToJson r | none => Json.null)])]

end KRust.Bridge
