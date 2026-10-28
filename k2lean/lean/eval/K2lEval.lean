import Lean
/-! `k2l-eval`: the cost metric and the frozen check of one module of a generated library (CT-4a).

    k2l-eval FILE MODULE [OUT.jsonl [SPEC.MODULE]]     (from the library's root: `lake env k2l-eval …`)
    k2l-eval --replay MODULE

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

open Lean Elab Frontend

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

unsafe def main (args : List String) : IO UInt32 := do
  if let ["--replay", m] := args then return ← replay m
  let (file, modName, out?, spec?) ← match args with
    | [f, m] => pure (f, m.toName, none, none)
    | [f, m, o] => pure (f, m.toName, some o, none)
    | [f, m, o, sp] => pure (f, m.toName, some o, some sp.toName)
    | _ => throw (IO.userError "usage: k2l-eval FILE MODULE [OUT.jsonl [SPEC.MODULE]] | k2l-eval --replay MODULE")
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
