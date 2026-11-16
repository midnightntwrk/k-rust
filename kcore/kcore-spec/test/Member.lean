/-
  Why each KORE text is or is not tied (compiled diagnostics), and the parameter symbols `parse`
  finds in it with their meaning (`impl`: the registry hook, or a parameter). Also checks the
  frozen table `regHookNames` against the builtin library's text: every hooked symbol named like a
  registry hook carries that hook's `hook{}` attribute. Run by test/member.sh:
      lean --run test/Ph/Member.lean KORE...
-/
import KcoreSpec.Tie
import KcoreSpec.Account
open KCore

def count {α} [BEq α] (a : α) (l : List α) : Nat := (l.filter (· == a)).length

def why (k : Kore.Definition) : String :=
  match Parse.parse k with
  | .error r => s!"parse refuses it: {r.toText}"
  | .ok d =>
    let ps := d.sem.params.map fun p => s!"{d.sem.symName p.sig.name}:{repr p.impl}"
    let pre := s!"imports {d.pres.imports.length}, params {ps.length} [{", ".intercalate ps}]; "
    if !d.namesOK then pre ++ "wf fails: namesOK"
    else if !d.sem.ok then pre ++ "wf fails: ok"
    else if !d.cert.ok d.sem then pre ++ "wf fails: cert"
    else if !d.pres.ok d.sem then pre ++ "wf fails: pres"
    else if !d.paramsOK then pre ++ "wf fails: paramsOK"
    else if decide (KoreAML.Reordered d.emit k) then pre ++ "tied"
    else match d.emit.modules.getLast?, k.modules.getLast? with
      | some e, some m =>
        let missing := m.sentences.filter fun s => count s e.sentences < count s m.sentences
        let extra := e.sentences.filter fun s => count s m.sentences < count s e.sentences
        pre ++ s!"emit differs: {missing.length} missing, {extra.length} extra\n" ++
          String.join ((missing.take 6).map fun s => "    - " ++ (Kore.Printer.sentence s).take 400 ++ "\n") ++
          String.join ((extra.take 6).map fun s => "    + " ++ (Kore.Printer.sentence s).take 400 ++ "\n")
      | _, _ => pre ++ "emit differs"

/-- Every hooked symbol of the library's text named like a registry hook has that hook's
attribute, and each interpreted hook's attribute is declared there. -/
def hookNamesOK : List String := Id.run do
  let mut bad := []
  let all := (List.range library.length).flatMap (moduleText false)
  for s in all do
    match s with
    | .hookedSymbol h =>
      let n := h.symbol.ident.ident.name
      for (g, hk) in regHookNames do
        if regSymNames.getD g "" == n && KoreAML.Parse.attrStr? h.attributes "hook" != some hk then
          bad := bad ++ [n]
    | _ => pure ()
  for (g, hk) in regHookNames do
    let found := all.any fun
      | .hookedSymbol h => h.symbol.ident.ident.name == regSymNames.getD g "" && KoreAML.Parse.attrStr? h.attributes "hook" == some hk
      | _ => false
    if !found then bad := bad ++ [s!"not in the library: {hk}"]
  return bad

def main (argv : List String) : IO UInt32 := do
  let bad := hookNamesOK
  IO.println s!"regHookNames against the library: {if bad.isEmpty then "ok" else ", ".intercalate bad}"
  let mut rc : UInt32 := if bad.isEmpty then 0 else 1
  for path in argv do
    let text ← IO.FS.readFile path
    match Kore.parseDefinition text with
    | .ok k =>
      let w := why k
      IO.println s!"{path}: {w}"
      unless w.endsWith "tied" do rc := 1
    | .error e => IO.println s!"{path}: KORE read error {e}"; rc := 1
  return rc
