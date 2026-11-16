/-
  A function's application as a map key in a rule's left side, read from K 7.1.337 kompile's KORE.
  Run from the package root: `lake env lean test/KeyFunction.lean`.
  - `f2-examples/keyfn.kompile.kore` (`keyfn.k`): `idx(Int, Int) [function, total]` and the rule
    `<k> get(I) => V … </k> <base> B </base> <mem> idx(B, I) |-> V … </mem>`, `B` and `I` bound by
    the rest of the left side. Read with the key a fresh variable `Key0` (of `idx`'s result sort,
    under the key's injection into KItem) and `Key0 ==Int idx(B, I)` as the rule's `requires`:
    `idx` no longer in the left side, nothing refused, `coreOK` (decided by the compiled `coreOK`,
    not in the kernel); the account names the rule (`keysAsRequires`).
  - `B` renamed in the `<base>` cell of the left side, so that the key's argument is bound only
    inside the key: not read so, refused (`functionInPattern`; `coreOK` fails too, the function
    application staying in the pattern).
  - `f2-examples/keyfn-partial.kompile.kore` (`keyfn-partial.k`): key functions not declared total,
    `pidx(B, I)` (a value at I = 0 and I = 1 only) and `kf(I)` (result sort `Key`, a value at I = 1
    only). Read so: `get` with `Key0 ==Int pidx(B, I)`; `put`, whose written `requires` is
    `W >Int 0`, with the strict conjunction `⟨W >Int 0, Key0 ==Int pidx(B, I)⟩ ==K ⟨true, true⟩`;
    `look` with `==K` of one-item sequences of `Key0` and `kf(I)`. Nothing refused, `coreOK`, no lazy
    obligation (compiled). The compiled step function (`Exec.successorsN`, the executable reading
    of `Step`): `get(I)` with `pidx(B, I)` a key of `<mem>` gives its value; where `pidx(B, I)` has a
    value that is no key, and where it has none (I = 2), the `[owise]` rule gives `miss()`: the rule
    does not block it; `put` steps where `W >Int 0` and the key is there, not otherwise; `look(1)`
    finds `k(1)`'s value, `look(2)` (`kf(2)` has none) has no successor.
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The reader's verdict on the text at `path` (its text edited by `edit`): per rule, the symbols
of its left side and of its `requires` and its variables' names; the functions in left sides the
account refuses; the rules read with a key as a `requires` conjunct; `coreOK`; the number of lazy
obligations; or the refusal. -/
def verdict (path : String) (edit : String → String := id) : IO String := do
  match Kore.parseDefinition (edit (← IO.FS.readFile path)) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    return match Parse.parse k with
      | .ok d =>
        let user := fun (fs : List Sym) => (fs.filter (· ≥ nRegSyms)).map d.sem.symName |>.filter
          fun n => ["Lblidx", "Lblpidx", "Lblkf"].contains n
        let rules := (withPres d.sem.rules d.pres.rules).map fun (r, rp) =>
          (user (Term.heads r.lhs), (r.req.map fun t => (Term.heads t).map d.sem.symName), rp.names)
        s!"read; rules {rules}; functionInPattern {(Parse.functionInPattern k d).map (·.detail)}; keys {(Parse.keysAsRequires k).map (·.2)}; coreOK {d.sem.coreOK}; lazy {d.sem.lazyObligations.length}"
      | .error r => s!"{r.reason.name} {r.detail}"

/--
info: read; rules [([], ((some [Lbl'UndsEqlsEqls'Int'Unds', Lblidx]), [I, 'Unds'DotVar1, B, 'Unds'Gen3, V, 'Unds'DotVar2, 'Unds'Gen4, 'Unds'DotVar0, Key0]))]; functionInPattern []; keys [[Lblidx]]; coreOK true; lazy 0
read; rules [([Lblidx], (none, [I, 'Unds'DotVar1, B2, 'Unds'Gen3, B, V, 'Unds'DotVar2, 'Unds'Gen4, 'Unds'DotVar0]))]; functionInPattern [Lblidx]; keys []; coreOK false; lazy 0
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/keyfn.kompile.kore")
  IO.println (← verdict "f2-examples/keyfn.kompile.kore" fun s =>
    s.replace "Lbl'-LT-'base'-GT-'{}(VarB:SortInt{})" "Lbl'-LT-'base'-GT-'{}(VarB2:SortInt{})")

/--
info: read; rules [([], ((some [Lbl'UndsEqlsEqls'Int'Unds', Lblpidx]), [I, 'Unds'DotVar1, B, 'Unds'Gen5, V, 'Unds'DotVar2, 'Unds'Gen6, 'Unds'Gen0, 'Unds'Gen1, Key0])), ([], (none, ['Unds'Gen0, 'Unds'DotVar1, 'Unds'Gen1, 'Unds'Gen2, 'Unds'Gen3, 'Unds'Gen4])), ([], ((some [Lbl'UndsEqlsEqls'K'Unds', kseq, dotk, kseq, Lblkf, dotk]), [I, 'Unds'DotVar1, 'Unds'Gen0, 'Unds'Gen1, V, 'Unds'DotVar2, 'Unds'Gen6, 'Unds'Gen2, Key0])), ([], ((some [Lbl'UndsEqlsEqls'K'Unds', kseq, Lbl'Unds-GT-'Int'Unds', kseq, Lbl'UndsEqlsEqls'Int'Unds', Lblpidx, dotk, kseq, kseq, dotk]), [I, W, 'Unds'DotVar1, B, 'Unds'Gen6, 'Unds'Gen0, 'Unds'DotVar2, 'Unds'Gen7, 'Unds'Gen1, 'Unds'Gen2, Key0]))]; functionInPattern []; keys [[Lblpidx], [Lblkf], [Lblpidx]]; coreOK true; lazy 0
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/keyfn-partial.kompile.kore")

/-- The successors of `keyfn-partial`'s configurations, by the compiled step function: for each
program, its `<k>` cell's first item after a step, or none for no successor. -/
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
  return ", ".intercalate (progs.map fun (n, x) => s!"{n}: {(Exec.successorsN c 1000 x).map first}")

/--
info: get(0), 5 |-> 7: [7], get(1), 6 |-> 8: [8], get(1), 5 |-> 7: [Lblmiss], get(2), 7 |-> 9: [Lblmiss], put(0, 4): [4], put(0, -4): [], put(2, 4): [], look(1): [3], look(2): []
-/
#guard_msgs in
#eval show IO Unit from do IO.println (← steps)
