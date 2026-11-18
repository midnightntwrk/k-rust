/-
  A function's application as a map key in a rule's left side, read from K 7.1.337 kompile's KORE.
  Run from the package root: `lake env lean test/KeyFunction.lean`.
  - `f2-examples/keyfn.kompile.kore` (`keyfn.k`): `idx(Int, Int) [function, total]` and the rule
    `<k> get(I) => V … </k> <base> B </base> <mem> idx(B, I) |-> V … </mem>`, `B` and `I` bound by
    the rest of the left side. Read with the key a fresh variable `Key0` (of `idx`'s result sort,
    under the key's injection into KItem) and the membership `Key0 ∈ idx(B, I)` as the rule's `pre`,
    no `requires`: `idx` no longer in the left side, nothing refused, `coreOK` and `execReady`
    (decided by the compiled checks, not in the kernel); the account names the rule (`keysAsMember`).
  - `B` renamed in the `<base>` cell of the left side, so that the key's argument is bound only
    inside the key: not read so, refused (`functionInPattern`; `coreOK` fails too, the function
    application staying in the pattern).
  - `f2-examples/keyfn-both.kompile.kore` (`keyfn-both.k`): the same key, and `idx(B, I)` again in
    the right side, `get(I) => at(idx(B, I), V)`. The left side is cut as above; the right side is
    read as written: it applies `idx`, and `Key0` is not in it.
  - `f2-examples/keyfn-partial.kompile.kore` (`keyfn-partial.k`): key functions not declared total,
    `pidx(B, I)` (a value at I = 0 and I = 1 only) and `kf(I)` (result sort `Key`, a value at I = 1
    only). Read so: `get` with `pre` `Key0 ∈ pidx(B, I)`; `put`, whose written `requires` is
    `W >Int 0`, with that `requires` and the `pre` `Key0 ∈ pidx(B, I)`; `look` with `Key0 ∈ kf(I)`
    at `Key`. Nothing refused, `coreOK`, `execReady`, no lazy obligation (compiled). The compiled
    step function (`CExec.successorsN`, the executable reading of `Step` where `CExec.execReady`
    holds, which evaluates a rule's `pre`) at the parsed semantics, whose interpretation is
    `HookParams.none` (`AtNone.steps`):
    `get(I)` with `pidx(B, I)` a key of `<mem>` gives its value; where `pidx(B, I)` has a value
    that is no key, the `[owise]` rule gives `miss()`: the rule does not block it; `put` steps where
    `W >Int 0` and the key is there, not otherwise; `look(1)` finds `k(1)`'s value. These hold
    under every interpretation: an equation decides `pidx(B, 0)`, `pidx(B, 1)` and `kf(1)`.
    `pidx(B, 2)` and `kf(2)` are points where no equation of a function not declared total
    applies: their values are the interpretation's, and the text fixes none. Under
    `HookParams.none` they have no value, so `get(2)` goes to `miss()`, `put(2, 4)` and `look(2)`
    have no successor: results at that interpretation, not what the text states. Under an
    interpretation giving `kf(2)` the key `k(1)`, `look(2)` steps to that key's entry
    (test/Guards.lean, `DevKey.look2_Hk`).
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- A term, variables by name. -/
partial def keyFnTermStr (c : Semantics) (ns : List String) : Term → String
  | .var i => ns.getD i s!"?{i}"
  | .app f as => s!"{c.symName f}(" ++ ", ".intercalate (as.map (keyFnTermStr c ns)) ++ ")"
  | .inj a b t => s!"inj[{c.sortName a},{c.sortName b}](" ++ keyFnTermStr c ns t ++ ")"
  | .as t i => "(" ++ keyFnTermStr c ns t ++ s!" as {ns.getD i s!"?{i}"})"
  | .dv _ l => reprStr l

/-- A condition, terms as `keyFnTermStr` prints them. -/
partial def keyFnCondStr (c : Semantics) (ns : List String) : Cond → String
  | .top => "top"
  | .and p q => "and(" ++ keyFnCondStr c ns p ++ ", " ++ keyFnCondStr c ns q ++ ")"
  | .mem s t u => s!"in[{c.sortName s}](" ++ keyFnTermStr c ns t ++ ", " ++ keyFnTermStr c ns u ++ ")"
  | _ => "other"

/-- The reader's verdict on the text at `path` (its text edited by `edit`): per rule, the key
functions its left side and its right side apply, the symbols of its `requires`, its `pre`, whether
a cut variable (`Key…`) is in its right side, and its variables' names; the functions in left sides
the account refuses; the rules read with a key as a membership conjunct of `pre`; `coreOK`;
`execReady`; the number of lazy obligations; or the refusal. -/
def verdict (path : String) (edit : String → String := id) : IO String := do
  match Kore.parseDefinition (edit (← IO.FS.readFile path)) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    return match Parse.parse k with
      | .ok d =>
        let user := fun (fs : List Sym) => (fs.filter (· ≥ nRegSyms)).map d.sem.symName |>.filter
          fun n => ["Lblidx", "Lblpidx", "Lblkf"].contains n
        let rules := (withPres d.sem.rules d.pres.rules).map fun (r, rp) =>
          let keyInRhs := (varOccs r.rhs).any fun i => (rp.names.getD i "").startsWith "Key"
          s!"lhs {user (Term.heads r.lhs)} rhs {user (Term.heads r.rhs)} req {r.req.map fun t => (Term.heads t).map d.sem.symName} pre {keyFnCondStr d.sem rp.names r.pre} keyInRhs {keyInRhs} vars {rp.names}"
        s!"read; rules {rules}; functionInPattern {(Parse.functionInPattern k d).map (·.detail)}; keys {(Parse.keysAsMember k).map (·.2)}; coreOK {d.sem.coreOK}; execReady {CExec.execReady d.sem}; lazy {d.sem.lazyObligations.length}"
      | .error r => s!"{r.reason.name} {r.detail}"

/--
info: read; rules [lhs [] rhs [] req none pre in[Int](Key0, Lblidx(B, I)) keyInRhs false vars [I, 'Unds'DotVar1, B, 'Unds'Gen3, V, 'Unds'DotVar2, 'Unds'Gen4, 'Unds'DotVar0, Key0]]; functionInPattern []; keys [[Lblidx]]; coreOK true; execReady true; lazy 0
read; rules [lhs [Lblidx] rhs [] req none pre top keyInRhs false vars [I, 'Unds'DotVar1, B2, 'Unds'Gen3, B, V, 'Unds'DotVar2, 'Unds'Gen4, 'Unds'DotVar0]]; functionInPattern [Lblidx]; keys []; coreOK false; execReady false; lazy 0
read; rules [lhs [] rhs [Lblidx] req none pre in[Int](Key0, Lblidx(B, I)) keyInRhs false vars [I, 'Unds'DotVar1, B, 'Unds'Gen3, V, 'Unds'DotVar2, 'Unds'Gen4, 'Unds'DotVar0, Key0]]; functionInPattern []; keys [[Lblidx]]; coreOK true; execReady true; lazy 0
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/keyfn.kompile.kore")
  IO.println (← verdict "f2-examples/keyfn.kompile.kore" fun s =>
    s.replace "Lbl'-LT-'base'-GT-'{}(VarB:SortInt{})" "Lbl'-LT-'base'-GT-'{}(VarB2:SortInt{})")
  IO.println (← verdict "f2-examples/keyfn-both.kompile.kore")

/--
info: read; rules [lhs [] rhs [] req none pre in[Int](Key0, Lblpidx(B, I)) keyInRhs false vars [I, 'Unds'DotVar1, B, 'Unds'Gen5, V, 'Unds'DotVar2, 'Unds'Gen6, 'Unds'Gen0, 'Unds'Gen1, Key0], lhs [] rhs [] req none pre top keyInRhs false vars ['Unds'Gen0, 'Unds'DotVar1, 'Unds'Gen1, 'Unds'Gen2, 'Unds'Gen3, 'Unds'Gen4], lhs [] rhs [] req none pre in[Key](Key0, Lblkf(I)) keyInRhs false vars [I, 'Unds'DotVar1, 'Unds'Gen0, 'Unds'Gen1, V, 'Unds'DotVar2, 'Unds'Gen6, 'Unds'Gen2, Key0], lhs [] rhs [] req (some [Lbl'Unds-GT-'Int'Unds']) pre in[Int](Key0, Lblpidx(B, I)) keyInRhs false vars [I, W, 'Unds'DotVar1, B, 'Unds'Gen6, 'Unds'Gen0, 'Unds'DotVar2, 'Unds'Gen7, 'Unds'Gen1, 'Unds'Gen2, Key0]]; functionInPattern []; keys [[Lblpidx], [Lblkf], [Lblpidx]]; coreOK true; execReady true; lazy 0
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/keyfn-partial.kompile.kore")

-- At the interpretation that gives nothing (`HookParams.none`): no statement for every interpretation.
namespace AtNone

/-- The successors of `keyfn-partial`'s configurations, by the compiled step function at the parsed
semantics (`CExec.successorsN`, `HookParams.none`): for each program, its `<k>` cell's first item after a step, or none
for no successor. -/
def steps : IO String := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile "f2-examples/keyfn-partial.kompile.kore")
    | return "KORE read error"
  let .ok d := Parse.parse k | return "refused"
  let c := d.sem
  let sym := fun (n : String) => ((List.range (nRegSyms + c.symNames.length)).find? (c.symName · == n)).getD 0
  let srt := fun (n : String) => nRegSorts + c.sortNames.idxOf n
  let int := fun (i : Int) => GroundTerm.dv Srt.int (.int i)
  let item := fun (s : Srt) (t : GroundTerm) => GroundTerm.inj s Srt.kitem t
  let mapOf := fun (es : List (GroundTerm × GroundTerm)) =>
    GroundTerm.map Srt.map (es.mergeSort fun a b => GroundTerm.cmp a.1 b.1 != .gt)
  let ints := fun (es : List (Int × Int)) => mapOf (es.map fun (a, b) => (item Srt.int (int a), item Srt.int (int b)))
  let cfg := fun (pgm : GroundTerm) (base : Int) (mem tab : GroundTerm) =>
    GroundTerm.ctor topLabel [.ctor (sym "Lbl'-LT-'k'-GT-'") [.ctor kseq [pgm, .ctor dotk []]],
      .ctor (sym "Lbl'-LT-'base'-GT-'") [int base], .ctor (sym "Lbl'-LT-'mem'-GT-'") [mem],
      .ctor (sym "Lbl'-LT-'tab'-GT-'") [tab], .ctor counterLabel [int 0]]
  let app := fun (f : String) (as : List Int) => GroundTerm.ctor (sym f) (as.map int)
  let kf1 := item (srt "Key") (.ctor (sym "Lblk") [int 1])
  let empty := mapOf []
  let progs : List (String × GroundTerm) := [
    ("get(0), 5 |-> 7", cfg (app "Lblget" [0]) 5 (ints [(5, 7)]) empty),
    ("get(1), 6 |-> 8", cfg (app "Lblget" [1]) 5 (ints [(5, 7), (6, 8)]) empty),
    ("get(1), 5 |-> 7", cfg (app "Lblget" [1]) 5 (ints [(5, 7)]) empty),
    ("get(2), 7 |-> 9", cfg (app "Lblget" [2]) 5 (ints [(5, 7), (7, 9)]) empty),
    ("put(0, 4)", cfg (app "Lblput" [0, 4]) 5 (ints [(5, 7)]) empty),
    ("put(0, -4)", cfg (app "Lblput" [0, -4]) 5 (ints [(5, 7)]) empty),
    ("put(2, 4)", cfg (app "Lblput" [2, 4]) 5 (ints [(5, 7), (7, 9)]) empty),
    ("look(1)", cfg (app "Lbllook" [1]) 0 empty (mapOf [(kf1, item Srt.int (int 3))])),
    ("look(2)", cfg (app "Lbllook" [2]) 0 empty (mapOf [(kf1, item Srt.int (int 3))]))]
  let first : GroundTerm → String
    | .ctor _ (.ctor _ [.ctor _ [.inj _ _ (.dv _ (.int i)), _]] :: _) => s!"{i}"
    | .ctor _ (.ctor _ [.ctor _ [.ctor f _, _]] :: _) => c.symName f
    | .ctor _ (.ctor _ [.ctor f []] :: _) => c.symName f
    | _ => "?"
  return ", ".intercalate (progs.map fun (n, x) => s!"{n}: {(CExec.successorsN c 1000 x).map first}")

/--
info: get(0), 5 |-> 7: [7], get(1), 6 |-> 8: [8], get(1), 5 |-> 7: [Lblmiss], get(2), 7 |-> 9: [Lblmiss], put(0, 4): [4], put(0, -4): [], put(2, 4): [], look(1): [3], look(2): []
-/
#guard_msgs in
#eval show IO Unit from do IO.println (← steps)

end AtNone
