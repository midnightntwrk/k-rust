/-
  A function declared `hooked-symbol` names a hook no registry hook interprets
  (`Definition.hookFnsUnregOK`, a conjunct of `Definition.paramsOK` and so of `wf`). Run from the
  package root: `lake env lean -j1 test/HookFnWf.lean`.
  - `INT.add` is a registry hook, `INT.rand` is not (decided).
  - `f2-examples/owisene.kompile.kore` read: a well-formed definition with functions, none of them
    hooked. Its first function's presentation given the hook `INT.add` (a definition the reader
    never builds: it reads a hooked symbol as a function only where `regHookOf` has nothing for
    its hook, `Parse.hookFnSym`): not well formed, `paramsOK` and `hookFnsUnregOK` false, the
    report naming the check. The same function given `INT.rand`: well formed.
-/
import KcoreSpec

set_option autoImplicit false

open KCore

theorem hookFnWf_add_registry : (regHookOf "INT.add").isSome = true := by decide +kernel
theorem hookFnWf_rand_unregistered : (regHookOf "INT.rand").isNone = true := by decide +kernel

/-- `d` with its first function's presentation carrying the hook `h`. -/
def hookFnWfWith (d : Definition) (h : String) : Definition :=
  { d with pres := { d.pres with fns := d.pres.fns.modify 0 fun fp => { fp with hook := some h } } }

def hookFnWfLine (what : String) (d : Definition) : String :=
  s!"{what}: wf {wf d}; paramsOK {d.paramsOK}; hookFnsUnregOK {d.hookFnsUnregOK}; failing {(d.report.filter (!·.2)).map (·.1)}"

/--
info: functions 1
read: wf true; paramsOK true; hookFnsUnregOK true; failing []
INT.add: wf false; paramsOK false; hookFnsUnregOK false; failing [hooked functions: no registry hook interprets their hook, parameter symbols (paramsOK): the imported modules' and the user's, each as its hook names]
INT.rand: wf true; paramsOK true; hookFnsUnregOK true; failing []
-/
#guard_msgs in
#eval show IO Unit from do
  match Kore.parseDefinition (← IO.FS.readFile "f2-examples/owisene.kompile.kore") with
  | .error e => IO.println s!"KORE read error {e}"
  | .ok k => match Parse.parse k with
    | .error r => IO.println s!"refused {r.reason.name} {r.detail}"
    | .ok d =>
      IO.println s!"functions {d.pres.fns.length}"
      IO.println (hookFnWfLine "read" d)
      IO.println (hookFnWfLine "INT.add" (hookFnWfWith d "INT.add"))
      IO.println (hookFnWfLine "INT.rand" (hookFnWfWith d "INT.rand"))
