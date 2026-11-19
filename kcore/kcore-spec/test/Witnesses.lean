/-
  The witness modules (`KcoreSpec/Model*Witness.lean`): semantics built to show that a condition of
  `coreOK` or of the hypotheses cannot be dropped (each module's header says which). For each
  module: its theorems, each depending on no axiom but `propext`, `Classical.choice` and
  `Quot.sound`, and the names of the negative ones among them (`no_model`, `not_*`).
  Fails when a module has no theorem or a theorem depends on another axiom. Run from the package
  root: `lake env lean test/Witnesses.lean`.

  The table `test/witnesses.toml`: one row per leaf conjunct of `coreOK` and per hypothesis
  `FnDet` and `FnSolves` on the functions, each with its witness module or `none` and the
  reason. The leaves are computed from the definitions' terms: `coreOK` and the definitions in
  `unfolded` are unfolded, `&&` is split, the body of a `List.all` over a lambda, of a
  single-alternative `match` and of a `let` is entered, and every other term is a leaf, keyed
  `<definition>.<n>` (its n-th leaf, left to right) with its printed text. Fails when a leaf has no
  row or its row's text differs (the expected rows are printed), when a row names no leaf, or
  when a row's witness is neither `none…` nor a collected witness module, or a file its `evidence`
  names is missing. A row's `note` is free text.
-/
import KcoreSpec

open Lean Elab Command Meta

run_cmd do
  let env ← getEnv
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mods := env.header.moduleNames.filter fun m =>
    (`KcoreSpec).isPrefixOf m && m.toString.startsWith "KcoreSpec.Model" && m.toString.endsWith "Witness"
  if mods.isEmpty then throwError "no witness module found"
  let mut byMod : Std.HashMap Name (Array Name) := {}
  for (c, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let m := env.header.moduleNames[idx.toNat]!
    if mods.contains m && ci matches .thmInfo _ && !c.isInternal then
      byMod := byMod.insert m ((byMod.getD m #[]).push c)
  let mut lines : Array MessageData := #[]
  let mut bad : Array MessageData := #[]
  for m in mods.qsort (·.toString < ·.toString) do
    let thms := byMod.getD m #[]
    if thms.isEmpty then bad := bad.push m!"{m}: no theorem"
    for c in thms do
      let other := (← collectAxioms c).filter (!std.contains ·)
      unless other.isEmpty do bad := bad.push m!"{c}: {other.toList}"
    let neg := thms.filter fun c => match c with
      | .str _ s => s == "no_model" || s.startsWith "not_"
      | _ => false
    let negs := (neg.qsort (·.toString < ·.toString)).toList.map fun c => c.componentsRev.head!.toString
    lines := lines.push m!"{m}: {thms.size} theorems, negative: {negs}"
  unless bad.isEmpty do
    throwError m!"witnesses:{indentD (MessageData.joinSep bad.toList Format.line)}"
  logInfo m!"{MessageData.joinSep lines.toList Format.line}\nwitnesses: {mods.size} modules, every theorem within propext, Classical.choice, Quot.sound"

namespace WitnessTable

/-- The definitions whose conjuncts are leaves: `coreOK`, its six conjuncts, and `itesApart`, whose
two halves are listed apart. -/
def unfolded : List Name :=
  [``KCore.Semantics.coreOK, ``KCore.Semantics.sortedOK, ``KCore.Semantics.faithCoreOK,
   ``KCore.Semantics.hooksApart, ``KCore.Semantics.predsApart, ``KCore.Semantics.idsOK,
   ``KCore.Semantics.overloadsOK, ``KCore.Faithful.Model.itesApart]

/-- The hypotheses on the functions the table lists (`consistent_of`'s `OpenLaws` is not listed). -/
def hyps : List Name := [``KCore.FnDet, ``KCore.FnSolves, ``KCore.ClausePreDecided, ``KCore.ClausePostDecided]

def lastName : Name → String
  | .str _ s => s
  | n => n.toString

/-- `s` with every run of white space one space, none at the ends. -/
def oneLine (s : String) : String := Id.run do
  let mut out : List Char := []
  let mut sp := false
  for ch in s.toList do
    if ch.isWhitespace then sp := true
    else
      if sp && !out.isEmpty then out := ' ' :: out
      sp := false
      out := ch :: out
  return String.ofList out.reverse

/-- The leaves of `e`, each with the definition it is a conjunct of and its printed text. -/
partial def walk (owner : Name) (e : Expr) (acc : Array (Name × String)) : MetaM (Array (Name × String)) := do
  let e := e.consumeMData.headBeta
  if let .letE _ _ v b _ := e then return ← walk owner (b.instantiate1 v) acc
  let args := e.getAppArgs
  if let .const n us := e.getAppFn then
    if n == ``Bool.and && args.size == 2 then
      return ← walk owner args[1]! (← walk owner args[0]! acc)
    if n == ``List.all && args.size == 3 && args[2]!.consumeMData.isLambda then
      return ← lambdaTelescope args[2]!.consumeMData fun _ b => walk owner b acc
    if unfolded.contains n then
      let ci ← getConstInfo n
      return ← walk n ((← instantiateValueLevelParams ci us).beta args) acc
  if let some m ← matchMatcherApp? e then
    if m.alts.size == 1 then
      return ← lambdaTelescope m.alts[0]! fun _ b => walk owner b acc
  return acc.push (owner, oneLine (toString (← ppExpr e)))

structure Row where
  key : String := ""
  text : String := ""
  witness : String := ""
  evidence : String := ""
  note : String := ""

def trimL (l : List Char) : List Char := (l.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace |>.reverse

def unescape : List Char → List Char
  | '\\' :: ch :: rest => ch :: unescape rest
  | ch :: rest => ch :: unescape rest
  | [] => []

def escape (s : String) : String :=
  String.ofList (s.toList.flatMap fun ch => if ch == '\\' || ch == '"' then ['\\', ch] else [ch])

/-- The rows of the table: `[[conjunct]]` starts a row, `field = "value"` sets a field. -/
def parse (src : String) : Except String (Array Row) := do
  let mut rows : Array Row := #[]
  for line in src.splitOn "\n" do
    let l := trimL line.toList
    if l.isEmpty || l.head? == some '#' then continue
    if l == "[[conjunct]]".toList then rows := rows.push {}; continue
    match (String.ofList l).splitOn " = " with
    | f :: rest =>
      let v := (" = ".intercalate rest).toList
      unless v.length ≥ 2 && v.head? == some '"' && v.getLast? == some '"' do
        throw s!"not a quoted value: {String.ofList l}"
      let v := String.ofList (unescape (v.drop 1).dropLast)
      let some r := rows.back? | throw s!"a field before the first row: {String.ofList l}"
      let r ← match f with
        | "key" => pure { r with key := v }
        | "text" => pure { r with text := v }
        | "witness" => pure { r with witness := v }
        | "evidence" => pure { r with evidence := v }
        | "note" => pure { r with note := v }
        | _ => throw s!"unknown field {f}"
      rows := rows.pop.push r
    | [] => throw s!"not a field: {String.ofList l}"
  return rows

end WitnessTable

open WitnessTable in
run_cmd do
  let env ← getEnv
  let mods := (env.header.moduleNames.filter fun m =>
    (`KcoreSpec).isPrefixOf m && m.toString.startsWith "KcoreSpec.Model" && m.toString.endsWith "Witness").map toString
  let leaves ← liftTermElabM do
    withLocalDeclD `c (mkConst ``KCore.Semantics) fun c =>
      walk ``KCore.Semantics.coreOK (mkApp (mkConst ``KCore.Semantics.coreOK) c) #[]
  let mut count : Std.HashMap Name Nat := {}
  let mut want : Array (String × String) := #[]
  for (o, t) in leaves do
    let n := count.getD o 0 + 1
    count := count.insert o n
    want := want.push (s!"{lastName o}.{n}", t)
  for h in hyps do
    unless env.contains h do throwError "witness table: no hypothesis {h}"
    want := want.push (lastName h, h.toString)
  let src ← IO.FS.readFile "test/witnesses.toml"
  let rows ← match parse src with
    | .ok r => pure r
    | .error e => throwError "witness table: {e}"
  let mut bad : Array String := #[]
  let mut missing : Array String := #[]
  for (k, t) in want do
    match rows.find? (·.key == k) with
    | some r => if r.text != t then missing := missing.push s!"[[conjunct]]\nkey = \"{k}\"\ntext = \"{escape t}\"\nwitness = \"{escape r.witness}\"\n(table text: {r.text})"
    | none => missing := missing.push s!"[[conjunct]]\nkey = \"{k}\"\ntext = \"{escape t}\"\nwitness = \"none\""
  let mut seen : Array String := #[]
  let mut withWit := 0
  for r in rows do
    if seen.contains r.key then bad := bad.push s!"{r.key}: listed twice"
    seen := seen.push r.key
    unless want.any (·.1 == r.key) do bad := bad.push s!"{r.key}: names no leaf conjunct"
    if r.witness.startsWith "none" then pure ()
    else if mods.contains r.witness then withWit := withWit + 1
    else bad := bad.push s!"{r.key}: witness {r.witness} is no collected witness module"
    unless r.evidence.isEmpty do
      for p in r.evidence.splitOn ", " do
        unless ← System.FilePath.pathExists p do bad := bad.push s!"{r.key}: evidence {p} is missing"
  unless missing.isEmpty && bad.isEmpty do
    throwError m!"witness table:{indentD (MessageData.joinSep (bad.toList.map toMessageData) Format.line)}\nrows missing or changed:\n{"\n\n".intercalate missing.toList}"
  logInfo m!"witness table: {rows.size} rows ({leaves.size} leaf conjuncts of coreOK, {hyps.length} hypotheses), {withWit} with a witness module, {rows.size - withWit} none"
