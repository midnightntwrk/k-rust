import Lean
/-! `k2l-eval`: the cost metric, the frozen check and the result of a generated library (CT-4a, CT-3, CT-4b).

    k2l-eval FILE MODULE [OUT.jsonl [SPEC.MODULE]]     (from the library's root: `lake env k2l-eval …`)
    k2l-eval --replay MODULE
    k2l-eval --freeze-record NS OUTDIR [SPEC.MODULE …]   (below, "The frozen part")
    k2l-eval --freeze-check NS OUTDIR
    k2l-eval --result NS OUT.json [MODULE …]            (below, "The result of a library")

The first form elaborates `FILE` as module `MODULE` against the built imports, command by command, and
writes one JSON line per command: its line, kind, declared names, heartbeats (`hb` raw, `kHb` in the
unit of `maxHeartbeats`), time, resident memory, status and errors; then a summary line. Heartbeats are
read with `IO.getNumHeartbeats` around each command, with `Elab.async=false`, so that proof elaboration
and the kernel check run on this thread and the delta is the command's whole cost: unlike wall time it
does not depend on the host's load (two runs differ by a few raw heartbeats), so a loop keeps or reverts a
proof by it. Numbers compare within one module path, toolchain and prelude only (a module's name and
namespace change the counts).

Each declared theorem `X` with a frozen statement `X.statement` is checked against it as `#k2l_proves`
does: `proved` (its type the statement's closure or the statement written out, Lean's three axioms
only), `moved` (another type), `axioms` (another axiom), `not-a-theorem`. With `SPEC.MODULE`, every
statement of that module without a theorem here is listed `open`.

`--replay MODULE` re-checks the module's declarations in the kernel against its imports (as
lean4checker does): a declaration added without the kernel's check (`debug.skipKernelTC`), which no
axiom report shows, is rejected. Exit status 0 when there is no error. -/

open Lean Elab Frontend Meta

def vm (key : String) : IO Nat := do
  let s ← IO.FS.readFile "/proc/self/status"
  for l in s.splitOn "\n" do
    if l.startsWith key then
      let n := ((l.drop key.length).toString.trimAscii.toString.takeWhile Char.isDigit).toString
      return n.toNat!
  return 0

/-- The status of theorem `n` against its frozen statement `n.statement`, if there is one:
`proved` (type structurally the statement's closure or its one-step unfolding, only Lean's three
axioms), `moved` (another type), `axioms` (a disallowed axiom, e.g. `sorryAx`), or `none` when the
environment has no `n.statement` (an internal lemma, checked layer). -/
def obligationStatus (env : Environment) (n : Name) : IO (Option (String × Array Name)) := do
  let some (.defnInfo si) := env.find? (n ++ `statement) | return none
  let some ci := env.find? n | return some ("open", #[])
  let .thmInfo ti := ci | return some ("not-a-theorem", #[])
  let ctx : Core.Context := { fileName := "<check>", fileMap := default }
  let ((closed, unfolded), _) ← (Meta.MetaM.run' (Meta.forallTelescope si.type fun xs _ => do
      let c ← Meta.mkForallFVars xs (mkAppN (mkConst si.name (si.levelParams.map mkLevelParam)) xs)
      let u ← Meta.mkForallFVars xs (si.value.beta xs)
      return (c, u))).toIO ctx { env }
  unless ti.type == closed || ti.type == unfolded do return some ("moved", #[])
  let (axs, _) ← (Lean.collectAxioms n : CoreM _).toIO ctx { env }
  let bad := axs.filter (fun a => ![``propext, ``Quot.sound, ``Classical.choice].contains a)
  return some (if bad.isEmpty then "proved" else "axioms", axs)

/-- The declared names of a command, from its syntax (`declId`s), prefixed by the namespace. -/
partial def declNames (ns : Name) (stx : Syntax) : Array Name := Id.run do
  let mut out := #[]
  if stx.isOfKind ``Lean.Parser.Command.declId then
    return #[ns ++ stx[0].getId]
  for a in stx.getArgs do
    -- do not descend into proofs/bodies: declIds only occur in headers
    if a.isOfKind ``Lean.Parser.Term.byTactic then continue
    out := out ++ declNames ns a
  return out

/-- `--replay MODULE`: the module's declarations re-checked by the kernel into the environment of its
own imports. -/
unsafe def replay (m : String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mod := m.toName
  let env ← importModules #[{ module := mod }] {} (trustLevel := 1024) (loadExts := false)
  let some idx := env.getModuleIdx? mod | throw (IO.userError s!"k2l-eval: no module {m}")
  let md := env.header.moduleData[idx.toNat]!
  let mut cs : Std.HashMap Name ConstantInfo := {}
  for c in md.constants do cs := cs.insert c.name c
  let base ← importModules (md.imports) {} (trustLevel := 1024) (loadExts := false)
  let h0 ← IO.getNumHeartbeats
  let t0 ← IO.monoMsNow
  let ok ← try discard <| base.toKernelEnv.replay cs; pure true
    catch e => IO.eprintln s!"REJECTED: {e}"; pure false
  let t1 ← IO.monoMsNow
  let h1 ← IO.getNumHeartbeats
  IO.println (Json.mkObj [("module", toJson m), ("constants", toJson cs.size),
    ("replayHb", toJson (h1 - h0)), ("replayMs", toJson (t1 - t0)), ("ok", toJson ok)]).compress
  return if ok then 0 else 1


/-! ## The frozen part (CT-3)

    k2l-eval --freeze-record NS OUTDIR [SPEC.MODULE …]
    k2l-eval --freeze-check NS OUTDIR

run from the root of the generated library `NS` (`lake env k2l-eval …`), right after generation for
`--freeze-record`. The frozen names are the theorems the library's axiom guards name
(`#k2l_assert_axioms`, and the refutation of `#k2l_refuted`) in its Lean files, apart from hand
modules (`*Hand.lean`) and `.lake/`: what the generator states, the same rule for every area. With
them, every obligation `X` that has a frozen statement `X.statement`, proved or open. The
specification is the closure of their statements through definitions: every constant of the
library's own modules that a frozen statement mentions, and every constant that a definition's value
mentions in turn, stopping at theorems (a theorem's statement counts, its proof does not). So a
proof, a decreasing proof included (Lean abstracts it into a theorem `f._proof_k`), is free, and a
definition, a termination measure included, is frozen. With `SPEC.MODULE`, every constant of that
module (the user's own Lean specification, `contract.md` §2) is a root of the closure too. The
prelude and Lean are pinned by the lake manifest and the toolchain, whose files are hashed.

`--freeze-record` writes `OUTDIR/k2lean.freeze` (the fingerprints: a 128-bit structural hash of
each statement, and of each closure constant's type and value, binder names aside) and
`OUTDIR/k2lean.frozen.md`, the frozen statements as Lean prints them, for people to read.
`--freeze-check` recomputes both from the names `k2lean.freeze` lists and reports each change:
`moved` (a frozen theorem's statement), `open` (no theorem), `axioms` (a disallowed axiom),
`spec-moved` / `spec-missing` (a closure constant), `file` (a hashed file), `readable` (the printed
statements differ from `k2lean.frozen.md`), `lint` (`debug.skipKernelTC`, `implemented_by` or
`@[extern` in a source). Exit status 1 when the frozen part moved (every kind but `open`). It guards
against accidents, not against a determined agent (`contract.md` §3.6); `--replay` is the kernel's
own check. -/

/-- A 128-bit structural hash of an expression: binder names and metadata aside, binder info kept. -/
partial def fpExpr (e : Expr) : StateM (Std.HashMap Expr (UInt64 × UInt64)) (UInt64 × UInt64) := do
  if let some h := (← get)[e]? then return h
  let mix (a b : UInt64 × UInt64) : UInt64 × UInt64 :=
    (mixHash a.1 b.1, mixHash (a.2 * 0x9E3779B97F4A7C15) (b.2 ^^^ 0xC2B2AE3D27D4EB4F))
  let tag (k : UInt64) : UInt64 × UInt64 := (k, k * 0xFF51AFD7ED558CCD)
  let nm (n : Name) : UInt64 × UInt64 := (n.hash, hash n.toString)
  let lv (l : Level) : UInt64 × UInt64 := (hash l, hash (toString l))
  let r ← match e with
    | .bvar i => pure (mix (tag 1) (tag i.toUInt64))
    | .fvar f => pure (mix (tag 2) (nm f.name))
    | .mvar m => pure (mix (tag 3) (nm m.name))
    | .sort l => pure (mix (tag 4) (lv l))
    | .const n ls => pure (ls.foldl (fun a l => mix a (lv l)) (mix (tag 5) (nm n)))
    | .app f a => return mix (mix (tag 6) (← fpExpr f)) (← fpExpr a)
    | .lam _ t b bi => return mix (mix (mix (tag 7) (tag (hash bi))) (← fpExpr t)) (← fpExpr b)
    | .forallE _ t b bi => return mix (mix (mix (tag 8) (tag (hash bi))) (← fpExpr t)) (← fpExpr b)
    | .letE _ t v b _ => return mix (mix (mix (tag 9) (← fpExpr t)) (← fpExpr v)) (← fpExpr b)
    | .lit (.natVal n) => pure (mix (tag 10) (tag (hash n)))
    | .lit (.strVal s) => pure (mix (tag 11) (tag (hash s)))
    | .mdata _ x => fpExpr x
    | .proj s i x => return mix (mix (mix (tag 12) (nm s)) (tag i.toUInt64)) (← fpExpr x)
  modify (·.insert e r)
  return r

def hex128 (h : UInt64 × UInt64) : String :=
  let f (x : UInt64) := let s := String.ofList (Nat.toDigits 16 x.toNat); "".pushn '0' (16 - s.length) ++ s
  f h.1 ++ f h.2

/-- A 128-bit hash of a file's bytes (`-` when it does not exist). -/
def fileHash (p : System.FilePath) : IO String := do
  unless ← p.pathExists do return "-"
  let b ← IO.FS.readBinFile p
  let mut h : UInt64 × UInt64 := (0xCBF29CE484222325, 0x84222325CBF29CE4)
  for x in b do
    h := (mixHash h.1 x.toUInt64, mixHash (h.2 * 0x100000001B3) (x.toUInt64 + 0x9E37))
  return hex128 h

/-- The Lean files of the library under `dir`, apart from `.lake/` and the like, and the lakefile;
`hand`: hand modules (`*Hand.lean`) included. -/
partial def leanFiles (dir : System.FilePath) (hand : Bool) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then
      unless e.fileName.startsWith "." do out := out ++ (← leanFiles e.path hand)
    else if e.fileName.endsWith ".lean" && e.fileName != "lakefile.lean"
        && (hand || !e.fileName.endsWith "Hand.lean") then
      out := out.push e.path
  return out.qsort (·.toString < ·.toString)

/-- The space-separated names of a command's arguments, `«…»`-aware. -/
def argNames (s : String) : List String := Id.run do
  let mut out := #[]
  let mut cur := ""
  let mut quoted := false
  for ch in s.toList do
    if ch == '«' then quoted := true; cur := cur.push ch
    else if ch == '»' then quoted := false; cur := cur.push ch
    else if ch.isWhitespace && !quoted then
      unless cur.isEmpty do out := out.push cur; cur := ""
    else cur := cur.push ch
  unless cur.isEmpty do out := out.push cur
  return out.toList

/-- The names a file's guard commands name, each with the namespace it is written in and, for a
refutation (`#k2l_refuted`), the statement constant it refutes (`X.statement`, or `S`). -/
def guardLines (text : String) : Array (String × String × Option String) := Id.run do
  let mut out := #[]
  let mut nss : Array String := #[]
  for line in text.splitOn "\n" do
    if line.startsWith "namespace " then nss := nss.push (line.drop 10).toString.trimAscii.toString
    else if line.startsWith "end " then
      if nss.back? == some (line.drop 4).toString.trimAscii.toString then nss := nss.pop
    else if line.startsWith "#k2l_assert_axioms " then
      for n in argNames (line.drop 19).toString do out := out.push (n, ".".intercalate nss.toList, none)
    else if line.startsWith "#k2l_refuted " then
      match argNames (line.drop 13).toString with
      | [x] => out := out.push (x ++ ".refuted", ".".intercalate nss.toList, some (x ++ ".statement"))
      | [s, r] => out := out.push (r, ".".intercalate nss.toList, some s)
      | _ => pure ()
  return out

/-- The names a file's guard commands name, each with the namespace it is written in. -/
def guardNames (text : String) : Array (String × String) :=
  (guardLines text).map fun (n, sp, _) => (n, sp)

/-- A name as printed (`Name.toString`) or written in a source: components separated by `.`
outside `«…»`, a quoted component taken whole. -/
def nameOf (s : String) : Name := Id.run do
  let mut n : Name := .anonymous
  let mut cur := ""
  let mut quoted := false
  for ch in s.toList do
    if ch == '«' then quoted := true
    else if ch == '»' then quoted := false
    else if ch == '.' && !quoted then n := .str n cur; cur := ""
    else cur := cur.push ch
  return .str n cur

/-- The module of a file of the library rooted at `root`. -/
def moduleOf (root p : System.FilePath) : Name :=
  let rel := (p.toString.drop (root.toString.length + 1)).toString
  nameOf ((rel.dropEnd 5).toString.replace "/" ".")

structure Frozen where
  ns : Name
  specs : Array Name := #[]
  files : Array (String × String) := #[]
  /-- per guard module, the frozen names (resolved) with their statement fingerprints -/
  stmts : Array (Name × Array (Name × String)) := #[]
  /-- the obligations with a frozen statement `X.statement` -/
  obls : Array Name := #[]
  /-- the refutations the guards check: (statement constant, refutation) -/
  refutes : Array (Name × Name) := #[]
  consts : Array (Name × String × String) := #[]
  /-- the modules that define the frozen names and statements: what a check imports (not the
  guard modules, which do not build once a frozen theorem is gone) -/
  imports : Array Name := #[]

def hashedFiles : List String := ["lean-toolchain", "lakefile.lean", "lake-manifest.json"]

/-- Whether a module belongs to the library `ns` (its root component is `ns`'s, or that with `Test`
or `Bench`), or is one of the user's specification modules. -/
def ownModule (ns : Name) (specs : Array Name) (m : Name) : Bool :=
  let r := ns.getRoot
  let mr := m.getRoot
  mr == r || mr == r.appendAfter "Test" || mr == r.appendAfter "Bench" || specs.contains m

/-- The closure of `roots` through definitions within the library's modules, with each constant's
type and value fingerprints (`-` for a theorem's value). -/
def closure (env : Environment) (own : Name → Bool) (roots : Array Name)
    (cache : Std.HashMap Expr (UInt64 × UInt64)) :
    Array (Name × String × String) × Std.HashMap Expr (UInt64 × UInt64) := Id.run do
  let mut cache := cache
  let mut seen : Std.HashSet Name := {}
  let mut work := roots
  let mut out := #[]
  while h : work.size > 0 do
    let k := work.back
    work := work.pop
    if seen.contains k then continue
    let some i := env.getModuleIdxFor? k | continue
    unless own env.header.moduleNames[i.toNat]! do continue
    seen := seen.insert k
    let some c := env.find? k | continue
    let (ht, c1) := (fpExpr c.type).run cache
    cache := c1
    let mut deps := c.type.getUsedConstants
    let mut vs := "-"
    match c with
    | .thmInfo _ => pure ()
    | .inductInfo ii => deps := deps ++ ii.ctors.toArray
    | _ =>
      if let some v := c.value? then
        let (hv, c2) := (fpExpr v).run cache
        cache := c2
        vs := hex128 hv
        deps := deps ++ v.getUsedConstants
    out := out.push (k, hex128 ht, vs)
    work := work ++ deps
  return (out.qsort (fun a b => a.1.toString < b.1.toString), cache)

/-- The frozen statements as Lean prints them, for people to read. -/
def readable (env : Environment) (fz : Frozen) : IO String := do
  let opens := [OpenDecl.simple fz.ns [], OpenDecl.simple `KPrelude []]
  let ctx : Core.Context := { fileName := "<frozen>", fileMap := default, maxHeartbeats := 0, openDecls := opens }
  let pp (e : Expr) : IO String := do
    let r ← ((ppExpr e : MetaM Format).run' {} |>.run' ctx { env }).toBaseIO
    return match r with
      | .ok f => (f.pretty 96).replace "\n" "\n    "
      | .error _ => "(not printable)"
  let mut o := s!"# The frozen statements of {fz.ns}\n\nWritten by `k2l-eval --freeze-record` (CT-3); do not edit: `k2l-eval --freeze-check` prints them\nagain and compares. A proof may change; these statements, and the definitions they mention, may not\n(`contract.md` §2). Printed with `open {fz.ns} KPrelude`.\n"
  for (m, ns) in fz.stmts do
    o := o ++ s!"\n## {m}\n\n```lean\n"
    for (n, _) in ns do
      if let some c := env.find? n then o := o ++ s!"theorem {n} :\n    {← pp c.type}\n"
    o := o ++ "```\n"
  unless fz.obls.isEmpty do
    o := o ++ "\n## Obligations with a frozen statement\n\n```lean\n"
    for n in fz.obls do
      if let some (.defnInfo d) := env.find? (n ++ `statement) then
        o := o ++ s!"def {n}.statement : {← pp d.type} :=\n    {← pp d.value}\n"
    o := o ++ "```\n"
  return o

/-- `k2lean.frozen.md` without the printed statements of the theorems `gone`: each from its line
`theorem X :` to the next statement or the end of its block. -/
def dropBlocks (text : String) (gone : Std.HashSet String) : String := Id.run do
  if gone.isEmpty then return text
  let mut out := #[]
  let mut skip := false
  for l in text.splitOn "\n" do
    if l.startsWith "theorem " || l.startsWith "def " || l.startsWith "```" then
      skip := l.startsWith "theorem " && gone.contains ((l.drop 8).toString.dropEnd 2).toString
    unless skip do out := out.push l
  return "\n".intercalate out.toList

/-- The obligations with a frozen statement (`X.statement`, a definition) in the modules `own` accepts. -/
def obligations (env : Environment) (own : Name → Bool) : Array Name := Id.run do
  let mut obls := #[]
  for (k, c) in env.constants.toList do
    if k.isStr && k.getString! == "statement" && c matches .defnInfo _ then
      if let some i := env.getModuleIdxFor? k then
        if own env.header.moduleNames[i.toNat]! then obls := obls.push k.getPrefix
  return obls

/-- The frozen part of the library `ns` in `env`: from the guard files under `root` (record), or
from the names of a previous record (check). -/
def computeFrozen (env : Environment) (ns : Name) (specs : Array Name)
    (stmtNames : Array (Name × Array Name)) : IO Frozen := do
  let own := ownModule ns specs
  let mut cache : Std.HashMap Expr (UInt64 × UInt64) := {}
  let mut stmts := #[]
  let mut roots : Array Name := #[]
  for (m, ns') in stmtNames do
    let mut row := #[]
    for n in ns' do
      match env.find? n with
      | some c =>
        let (h, c1) := (fpExpr c.type).run cache
        cache := c1
        row := row.push (n, hex128 h)
        roots := roots ++ c.type.getUsedConstants
      | none => row := row.push (n, "-")
    stmts := stmts.push (m, row)
  let obls := obligations env own
  roots := roots ++ obls.map (· ++ `statement)
  for sp in specs do
    if let some i := env.getModuleIdx? sp then
      roots := roots ++ (env.header.moduleData[i.toNat]!.constants.map (·.name))
  let (consts, _) := closure env own roots cache
  let mut files := #[]
  for f in hashedFiles do files := files.push (f, ← fileHash f)
  let mut imports : Std.HashSet Name := {}
  for (_, r) in stmts do
    for (n, _) in r do
      if let some i := env.getModuleIdxFor? n then imports := imports.insert env.header.moduleNames[i.toNat]!
  for n in obls do
    for k in [n ++ `statement, n] do
      if let some i := env.getModuleIdxFor? k then imports := imports.insert env.header.moduleNames[i.toNat]!
  for sp in specs do imports := imports.insert sp
  return { ns, specs, files, stmts, obls := obls.qsort (·.toString < ·.toString), consts,
           imports := imports.toArray.qsort (·.toString < ·.toString) }

def writeFrozen (out : System.FilePath) (fz : Frozen) : IO Unit := do
  let mut o := "# Written by k2l-eval --freeze-record (CT-3); do not edit. The fingerprints of the frozen part:\n# `stmt` a frozen theorem's statement, `const` a constant of the specification (type, value).\n"
  o := o ++ s!"ns\t{fz.ns}\n"
  for s in fz.specs do o := o ++ s!"spec\t{s}\n"
  for m in fz.imports do o := o ++ s!"import\t{m}\n"
  for (f, h) in fz.files do o := o ++ s!"file\t{f}\t{h}\n"
  for (m, ns) in fz.stmts do
    o := o ++ s!"module\t{m}\n"
    for (n, h) in ns do o := o ++ s!"stmt\t{n}\t{h}\n"
  for n in fz.obls do o := o ++ s!"obl\t{n}\n"
  for (st, r) in fz.refutes do o := o ++ s!"refute\t{st}\t{r}\n"
  for (n, t, v) in fz.consts do o := o ++ s!"const\t{n}\t{t}\t{v}\n"
  IO.FS.writeFile (out / "k2lean.freeze") o

def readFrozen (out : System.FilePath) : IO Frozen := do
  let mut fz : Frozen := { ns := .anonymous }
  for l in (← IO.FS.readFile (out / "k2lean.freeze")).splitOn "\n" do
    match l.splitOn "\t" with
    | ["ns", n] => fz := { fz with ns := nameOf n }
    | ["spec", s] => fz := { fz with specs := fz.specs.push (nameOf s) }
    | ["file", f, h] => fz := { fz with files := fz.files.push (f, h) }
    | ["module", m] => fz := { fz with stmts := fz.stmts.push (nameOf m, #[]) }
    | ["stmt", n, h] =>
      let some (m, row) := fz.stmts.back? | throw (IO.userError "k2lean.freeze: stmt before module")
      fz := { fz with stmts := fz.stmts.pop.push (m, row.push (nameOf n, h)) }
    | ["const", n, t, v] => fz := { fz with consts := fz.consts.push (nameOf n, t, v) }
    | ["import", m] => fz := { fz with imports := fz.imports.push (nameOf m) }
    | ["obl", n] => fz := { fz with obls := fz.obls.push (nameOf n) }
    | ["refute", st, r] => fz := { fz with refutes := fz.refutes.push (nameOf st, nameOf r) }
    | _ => pure ()
  return fz

/-- The lines of the library's sources (hand modules included) that a lint rejects. -/
def lint (root : System.FilePath) : IO (Array String) := do
  let mut out := #[]
  for f in ← leanFiles root true do
    let lines := (← IO.FS.readFile f).splitOn "\n"
    for i in [0:lines.length] do
      let l := lines[i]!
      for bad in ["skipKernelTC", "implemented_by", "@[extern"] do
        if (l.splitOn bad).length > 1 then out := out.push s!"{f}:{i + 1}: {bad}"
  return out

/-- Resolve a guard's name: `ns.n` when the guard is written in namespace `ns` and that exists. -/
def resolve (env : Environment) (n space : String) : Name :=
  let nm := nameOf n
  let full := (if space == "" then .anonymous else nameOf space) ++ nm
  if space != "" && env.contains full then full else nm

unsafe def freezeImport (ns : Name) (mods : Array Name) : IO Environment := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let imps := if mods.isEmpty then #[ns] else mods
  importModules (imps.map ({ module := · })) {} (trustLevel := 1024) (loadExts := true)

/-- The guard files of the library under `root`: each module with its guard lines. -/
def guardFiles (root : System.FilePath) : IO (Array (Name × Array (String × String × Option String))) := do
  let mut out := #[]
  for f in ← leanFiles root false do
    let g := guardLines (← IO.FS.readFile f)
    unless g.isEmpty do out := out.push (moduleOf root f, g)
  return out

/-- The refutations of the guards' `#k2l_refuted` lines: (statement constant, refutation), resolved. -/
def refutations (env : Environment) (guards : Array (Name × Array (String × String × Option String))) :
    Array (Name × Name) := Id.run do
  let mut out := #[]
  for (_, g) in guards do
    for (n, sp, st?) in g do
      if let some st := st? then out := out.push (resolve env st sp, resolve env n sp)
  return out

unsafe def freezeRecord (ns : Name) (out : System.FilePath) (specs : Array Name) : IO UInt32 := do
  let root : System.FilePath := "."
  let guards ← guardFiles root
  let env ← freezeImport ns (guards.map (·.1) ++ specs)
  let stmtNames := guards.map fun (m, g) => (m, g.map fun (n, sp, _) => resolve env n sp)
  let mut missing := #[]
  for (_, ns') in stmtNames do
    for n in ns' do unless env.contains n do missing := missing.push n
  unless missing.isEmpty do
    IO.eprintln s!"k2l-eval: guarded names not in the library: {missing}"
    return 1
  let fz := { (← computeFrozen env ns specs stmtNames) with refutes := refutations env guards }
  IO.FS.createDirAll out
  writeFrozen out fz
  IO.FS.writeFile (out / "k2lean.frozen.md") (← readable env fz)
  let bad ← lint root
  for b in bad do IO.eprintln s!"lint: {b}"
  IO.println (Json.mkObj [("ns", toJson ns.toString), ("statements", toJson (fz.stmts.foldl (· + ·.2.size) 0)),
    ("obligations", toJson fz.obls.size), ("constants", toJson fz.consts.size), ("lint", toJson bad.size)]).compress
  return if bad.isEmpty then 0 else 1

/-! ## The result of a library (CT-4b)

    k2l-eval --result NS OUT.json [MODULE …]

run from the root of the generated library `NS` (`lake env k2l-eval …`) once it is built: the status
of every frozen name, read from the built environment rather than from the generated text, so a
proof moved to another module, restated through its statement, or added in a new file counts as
it is. It imports `MODULE …` (by default every guard file of the library, as `--freeze-record`
does; a gate passes the guard it built, so that no `.olean` of a module it did not build is read).
The entries are the names of the library's guard files (apart from refutations), and every
obligation `X` with a statement `X.statement` in the library's own modules; a name of a guard module
the import did not reach, absent from it, is `unbuilt` (a library built only as far as its
`Equations`: its proved equations are there, its `step_sound` is not). A refutation
(`#k2l_refuted X`, of `X.refuted`, or `#k2l_refuted S R`) is not an entry: it gives its statement's
status. `--freeze-check` writes `OUTDIR/k2lean-result.json` too, of the recorded names.

Each entry has its `name`, `kind`, `status`, `module` (where its theorem, else its statement, is:
the module a loop evaluates with the first form) and `axioms`. The kind is read from the frozen name,
the generator's naming: `equation` (`NS.Eqn.*`, `NS.Simp.*`, `NS.Lemma.*`), `divergence`
(`*.diverges`), `total` (`*.total`), `other` (any other guarded theorem or obligation). The status
is `proved` (a theorem, of the statement's closure or its unfolding when there is a statement, on
Lean's three axioms), `refuted` (the refutation's type the negation of the statement's closure, as
`#k2l_refuted` checks, on the three axioms), `open` (neither), `axioms` (another axiom), `moved` (a
freeze check found it moved), `unbuilt`, or `not-a-theorem`. Heartbeats are not in it: they need the module
elaborated again (the first form), at about the cost of building it. -/

def allowedAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- The status of the refutation `rn` of the statement constant `sn`, as `#k2l_refuted` checks it:
`refuted` (its type the negation of the statement's closure, Lean's three axioms only), `axioms`,
`moved` (another type), or `none` when there is no such theorem. -/
def refutationStatus (env : Environment) (sn rn : Name) : IO (Option String) := do
  let some s := env.find? sn | return none
  let some (.thmInfo r) := env.find? rn | return none
  let ctx : Core.Context := { fileName := "<check>", fileMap := default }
  let (expected, _) ← (Meta.MetaM.run' (Meta.forallTelescope s.type fun xs _ =>
      Meta.mkForallFVars xs (mkAppN (mkConst s.name (s.levelParams.map mkLevelParam)) xs))).toIO ctx { env }
  unless r.type == mkNot expected do return some "moved"
  let (axs, _) ← (Lean.collectAxioms rn : CoreM _).toIO ctx { env }
  return some (if axs.all allowedAxioms.contains then "refuted" else "axioms")

/-- An entry's kind, read from its frozen name (the generator's naming). -/
def kindOf (ns n : Name) : String :=
  let first := ((n.replacePrefix ns .anonymous).components.head?.map toString).getD ""
  if ns.isPrefixOf n && ["Eqn", "Simp", "Lemma"].contains first then "equation"
  else if n.isStr && n.getString! == "diverges" then "divergence"
  else if n.isStr && n.getString! == "total" then "total"
  else "other"

structure Entry where
  name : Name
  kind : String
  status : String
  module : String
  axioms : Array Name := #[]

def moduleName (env : Environment) (n : Name) : Option String :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!.toString

/-- The entries of the library `ns`: the obligations `obls` (each with `X.statement`), the
statement constants that `refs` refute outright (claims, `#k2l_refuted S R`), and the other frozen
theorems `thms`. A refutation of `refs` (statement constant, refutation) gives its statement's status
instead of an entry of its own; `moved` are the names a freeze check found moved, `unreached` those of
guard modules the import did not reach: one of them that is not in the environment is `unbuilt`
rather than `open` (nothing is known of it). -/
def resultEntries (env : Environment) (ns : Name) (thms obls : Array Name) (refs : Array (Name × Name))
    (moved unreached : Std.HashSet Name) : IO (Array Entry) := do
  let ctx : Core.Context := { fileName := "<check>", fileMap := default }
  let refOf : Std.HashMap Name Name := refs.foldl (fun m (sn, r) => m.insert sn r) {}
  let refNames : Std.HashSet Name := refs.foldl (fun m (_, r) => m.insert r) {}
  let claims := refs.filterMap fun (sn, _) =>
    if sn.isStr && sn.getString! == "statement" then none else some sn
  let mut out := #[]
  let mut seen : Std.HashSet Name := {}
  for x in obls ++ claims do
    if seen.contains x then continue
    seen := seen.insert x
    let sn := if claims.contains x then x else x ++ `statement
    let (st0, axs) ← if sn == x then pure ("open", #[]) else pure ((← obligationStatus env x).getD ("open", #[]))
    let mut st := st0
    if st == "open" then
      if let some r := refOf[sn]? then
        if let some rs ← refutationStatus env sn r then st := rs
        else if unreached.contains r then st := "unbuilt"
    if moved.contains x then st := "moved"
    out := out.push { name := x, kind := kindOf ns x, status := st, axioms := axs,
                      module := (moduleName env x).getD ((moduleName env sn).getD "-") }
  for n in thms do
    if seen.contains n || refNames.contains n then continue
    seen := seen.insert n
    let (st, axs) ← match env.find? n with
      | none => pure (if unreached.contains n then "unbuilt" else "open", #[])
      | some (.thmInfo _) =>
        let (axs, _) ← (Lean.collectAxioms n : CoreM _).toIO ctx { env }
        pure (if axs.all allowedAxioms.contains then "proved" else "axioms", axs)
      | some _ => pure ("not-a-theorem", #[])
    out := out.push { name := n, kind := kindOf ns n, status := if moved.contains n then "moved" else st,
                      axioms := axs, module := (moduleName env n).getD "-" }
  return out.qsort (·.name.toString < ·.name.toString)

/-- The result: the entries, and their number per kind and status. -/
def resultJson (ns : Name) (es : Array Entry) : Json := Id.run do
  let mut totals : Std.HashMap String (Std.HashMap String Nat) := {}
  for e in es do
    let k := totals.getD e.kind {}
    totals := totals.insert e.kind (k.insert e.status (k.getD e.status 0 + 1))
  let tj := Json.mkObj (totals.toList.map fun (k, m) => (k, Json.mkObj (m.toList.map fun (s, n) => (s, toJson n))))
  return Json.mkObj [("ns", toJson ns.toString), ("totals", tj),
    ("entries", Json.arr (es.map fun e => Json.mkObj [("name", toJson e.name.toString),
      ("kind", toJson e.kind), ("status", toJson e.status), ("module", toJson e.module),
      ("axioms", toJson (e.axioms.map toString))]))]

unsafe def result (ns : Name) (out : System.FilePath) (mods : Array Name) : IO UInt32 := do
  let guards ← guardFiles "."
  let env ← freezeImport ns (if mods.isEmpty then guards.map (·.1) else mods)
  let thms := guards.foldl (init := #[]) fun a (_, g) =>
    a ++ (g.filter (·.2.2.isNone)).map fun (n, sp, _) => resolve env n sp
  let unreached : Std.HashSet Name := guards.foldl (init := {}) fun a (m, g) =>
    if (env.getModuleIdx? m).isSome then a else g.foldl (fun a (n, sp, _) => a.insert (resolve env n sp)) a
  let es ← resultEntries env ns thms (obligations env (ownModule ns #[])) (refutations env guards) {} unreached
  let j := resultJson ns es
  IO.FS.writeFile out (j.pretty ++ "\n")
  IO.println (Json.mkObj [("ns", toJson ns.toString), ("entries", toJson es.size),
    ("totals", j.getObjValD "totals")]).compress
  return 0

unsafe def freezeCheck (ns : Name) (out : System.FilePath) : IO UInt32 := do
  let was ← readFrozen out
  let env ← freezeImport ns was.imports
  let now ← computeFrozen env ns was.specs (was.stmts.map fun (m, r) => (m, r.map (·.1)))
  let mut rep : Array (String × String) := #[]
  let mut movedNames : Std.HashSet Name := {}
  for ((f, h), (_, h')) in was.files.zip now.files do
    if h != h' then rep := rep.push ("file", f)
  for ((_, r), (_, r')) in was.stmts.zip now.stmts do
    for ((n, h), (_, h')) in r.zip r' do
      match env.find? n with
      | none => rep := rep.push ("open", n.toString)
      | some (.thmInfo _) =>
        -- a frozen obligation may be restated through its statement (`theorem X : X.statement`)
        let viaStatement ← if h != h' then
            pure ((← obligationStatus env n).map (·.1) == some "proved") else pure true
        if h != h' && !viaStatement then rep := rep.push ("moved", n.toString); movedNames := movedNames.insert n
        else
          let ctx : Core.Context := { fileName := "<check>", fileMap := default }
          let (axs, _) ← (Lean.collectAxioms n : CoreM _).toIO ctx { env }
          if axs.any (fun a => ![``propext, ``Quot.sound, ``Classical.choice].contains a) then
            rep := rep.push ("axioms", n.toString)
      | some _ => rep := rep.push ("moved", s!"{n} (not a theorem)"); movedNames := movedNames.insert n
  -- the obligations with a frozen statement: proved as stated, open, moved, or on another axiom
  for n in was.obls do
    match ← obligationStatus env n with
    | some ("proved", _) => pure ()
    | some ("open", _) => rep := rep.push ("open", n.toString)
    | some ("axioms", _) => rep := rep.push ("axioms", n.toString)
    | some (st, _) => rep := rep.push ("moved", s!"{n} ({st})"); movedNames := movedNames.insert n
    | none => rep := rep.push ("spec-missing", s!"{n}.statement")
  let nowC : Std.HashMap Name (String × String) :=
    now.consts.foldl (fun m (n, t, v) => m.insert n (t, v)) {}
  for (n, t, v) in was.consts do
    match nowC[n]? with
    | none => rep := rep.push ("spec-missing", n.toString)
    | some tv => if tv != (t, v) then rep := rep.push ("spec-moved", n.toString)
  -- the readable statements, apart from those of frozen theorems that are gone (reported open)
  let gone : Std.HashSet String := rep.foldl (fun s (k, n) => if k == "open" then s.insert n else s) {}
  let text ← readable env { now with stmts := was.stmts }
  if dropBlocks (← IO.FS.readFile (out / "k2lean.frozen.md")) gone != text then
    rep := rep.push ("readable", "k2lean.frozen.md")
  for b in ← lint "." do rep := rep.push ("lint", b)
  for (k, n) in rep do IO.println (Json.mkObj [("kind", toJson k), ("name", toJson n)]).compress
  -- the result (CT-4b) of the recorded names: what a loop's run is judged by
  let thms := was.stmts.foldl (fun a (_, r) => a ++ r.map (·.1)) #[]
  let es ← resultEntries env ns thms was.obls was.refutes movedNames {}
  IO.FS.writeFile (out / "k2lean-result.json") ((resultJson ns es).pretty ++ "\n")
  let moved := rep.filter (·.1 != "open")
  IO.println (Json.mkObj [("ns", toJson ns.toString), ("open", toJson (rep.size - moved.size)),
    ("moved", toJson moved.size)]).compress
  return if moved.isEmpty then 0 else 1

unsafe def main (args : List String) : IO UInt32 := do
  if let ["--replay", m] := args then return ← replay m
  if let "--freeze-record" :: n :: o :: specs := args then
    return ← freezeRecord (nameOf n) o (specs.toArray.map nameOf)
  if let ["--freeze-check", n, o] := args then return ← freezeCheck (nameOf n) o
  if let "--result" :: n :: o :: mods := args then return ← result (nameOf n) o (mods.toArray.map nameOf)
  let (file, modName, out?, spec?) ← match args with
    | [f, m] => pure (f, m.toName, none, none)
    | [f, m, o] => pure (f, m.toName, some o, none)
    | [f, m, o, sp] => pure (f, m.toName, some o, some sp.toName)
    | _ => throw (IO.userError "usage: k2l-eval FILE MODULE [OUT.jsonl [SPEC.MODULE]] | k2l-eval --replay MODULE | k2l-eval --freeze-record NS OUTDIR [SPEC.MODULE …] | k2l-eval --freeze-check NS OUTDIR | k2l-eval --result NS OUT.json [MODULE …]")
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let opts := Options.empty.setBool `Elab.async false
  let hStart ← IO.getNumHeartbeats
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx (trustLevel := 1024)
    (mainModule := modName)
  let hHeader ← IO.getNumHeartbeats
  let cmdState := Command.mkState env messages opts
  let ctx : Frontend.Context := { inputCtx }
  let st0 : Frontend.State := { commandState := cmdState, parserState, cmdPos := parserState.pos }
  let rows ← IO.mkRef (#[] : Array Json)
  let nerrRef ← IO.mkRef 0
  let step : FrontendM Bool := do
    let pos := (← get).parserState.pos
    let scope := (← get).commandState.scopes.head!
    let h0 ← IO.getNumHeartbeats
    let t0 ← IO.monoNanosNow
    let done ← processCommand
    let t1 ← IO.monoNanosNow
    let h1 ← IO.getNumHeartbeats
    let stx := (← get).commands.back!
    let names := declNames scope.currNamespace stx
    let line := inputCtx.fileMap.toPosition pos |>.line
    -- messages are reset per command (`elabCommandTopLevel`): read this command's here
    let mut errs : Array String := #[]
    for m in (← get).commandState.messages.toList do
      if m.severity == .error then
        let t ← m.toString
        errs := errs.push ((t.take 300).toString)
        IO.eprintln t
    nerrRef.modify (· + errs.size)
    unless stx.getKind == ``Lean.Parser.Command.eoi do
      rows.modify (·.push <| Json.mkObj [
        ("line", toJson line), ("kind", toString stx.getKind),
        ("decls", toJson (names.map toString)),
        ("hb", toJson (h1 - h0)), ("kHb", toJson ((h1 - h0) / 1000)),
        ("ms", toJson ((t1 - t0) / 1000000)), ("rssKiB", toJson (← vm "VmRSS:")),
        ("status", if errs.isEmpty then "ok" else "error"), ("errors", toJson errs)])
    return done
  let rec loop : Nat → FrontendM Unit
    | 0 => pure ()
    | n+1 => do if !(← step) then loop n
  let (_, st) ← (loop 1000000 ctx).run st0
  let hEnd ← IO.getNumHeartbeats
  let nerr ← nerrRef.get
  -- CT-3: each declared theorem against its frozen statement, in the final environment
  let env := st.commandState.env
  let rows' ← (← rows.get).mapM fun r => do
    let decls : Array String := (r.getObjValAs? (Array String) "decls").toOption.getD #[]
    let mut obl : Array Json := #[]
    for d in decls do
      if let some (st, axs) ← obligationStatus env d.toName then
        obl := obl.push (Json.mkObj [("name", toJson d), ("status", toJson st), ("axioms", toJson (axs.map toString))])
    return if obl.isEmpty then r else r.setObjVal! "obligations" (toJson obl)
  rows.set rows'
  -- CT-3: with a statements module, every statement of it without a theorem here is open
  let mut openNames : Array String := #[]
  if let some sp := spec? then
    if let some idx := env.getModuleIdx? sp then
      for c in env.header.moduleData[idx.toNat]!.constants do
        if c.name.isStr && c.name.getString! == "statement" then
          if (env.find? c.name.getPrefix).isNone then openNames := openNames.push c.name.getPrefix.toString
  let summary := Json.mkObj [("module", toString modName), ("headerHb", toJson (hHeader - hStart)),
    ("commandsHb", toJson (hEnd - hHeader)), ("totalHb", toJson (hEnd - hStart)),
    ("errors", toJson nerr), ("peakRssKiB", toJson (← vm "VmHWM:")), ("open", toJson openNames)]
  let lines := (← rows.get).map (·.compress) |>.push summary.compress
  match out? with
  | some o => IO.FS.writeFile o (String.intercalate "\n" lines.toList ++ "\n")
  | none => pure ()
  IO.println summary.compress
  return if nerr == 0 then 0 else 1
