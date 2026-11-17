/-
  A rewrite axiom whose right side applies an alias of K's prelude (FIX-core.allpath-alias-read).
  Run from the package root: `lake env lean test/AliasRhs.lean`.

  kompile writes a rule of a module carrying all-path as `\rewrites(\and(l, \top), weakAlwaysFinally{S}(
  \and(r, \top)))`; the text's prelude defines the alias by `weakAlwaysFinally{A}(@X:A) := @X:A`, and
  likewise weakExistsFinally (one-path) and allPathGlobally. An alias application denotes the body
  with the argument for the parameter, so where the body is the parameter the axiom denotes the one
  with the argument in the alias's place (`Parse.unaliasRule`, `ReadingNote.identityAlias`).
  - every alias of `preludeAliases` is one the prelude's own sentences define as the identity
    (`Parse.identityAliases`, decided by `aliasIsIdentity` on the sentences);
  - `aliasIsIdentity` is false for the prelude's sentence edited: another body, a second argument,
    another result sort, the body a variable other than the argument;
  - `hw-allpath-alias` (kompile's text for e2-all-path, one parenthesis added) is read, and its
    Semantics is that of the same text with `weakAlwaysFinally{S}(` and its parenthesis removed;
    the alias's rule is classified `read identityAlias`; likewise with the head renamed to
    weakExistsFinally and to allPathGlobally;
  - the text edited so that the alias is applied to two arguments, or with no sort argument, is
    refused `aliasApplication`, the detail naming the alias.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

def hw : String := "test/constructs/fixtures/hw-allpath-alias/hw-allpath-alias.kore"

/-- The prelude's alias sentence named `n`. -/
def preludeAlias (n : String) : Option Kore.SentenceAlias :=
  ((preludeModules.flatMap (·.sentences)).filterMap fun
    | .alias a => some a
    | _ => none).find? (·.alias.ident.ident.name == n)

/-- The rewrite axioms of the user module with their right side edited by `ed`. -/
def editRhs (ed : Kore.Pattern → Kore.Pattern) (k : Kore.Definition) : Kore.Definition :=
  let sent := fun (s : Kore.Sentence) => match s with
    | .axiom a => match a.pattern with
      | .rewrites srt l r => .axiom { a with pattern := .rewrites srt l (ed r) }
      | _ => s
    | s => s
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.map sent }]).getD [] }

/-- The reader's verdict on the text at `path` (edited by `edit`): "read" or the refusal. -/
def verdict (path : String) (edit : Kore.Definition → Kore.Definition := id) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    return match Parse.parse (edit k) with
    | .ok _ => "read"
    | .error r => if r.detail.isEmpty then r.reason.name else s!"{r.reason.name}: {r.detail}"

/-- info: ["weakExistsFinally", "weakAlwaysFinally", "allPathGlobally"] -/
#guard_msgs in
#eval Parse.identityAliases

/--
info: prelude: [true, true, true]
another body: false
two arguments: false
another result sort: false
another variable: false
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println s!"prelude: {Parse.preludeAliases.map fun n => ((preludeAlias n).map Parse.aliasIsIdentity).getD false}"
  let some a := preludeAlias "weakAlwaysFinally" | IO.println "no sentence"
  let x := a.app.args.headD default
  IO.println s!"another body: {Parse.aliasIsIdentity { a with body := .bottom a.sort }}"
  IO.println s!"two arguments: {Parse.aliasIsIdentity { a with sorts := a.sorts ++ a.sorts, app := { a.app with args := [x, x] } }}"
  IO.println s!"another result sort: {Parse.aliasIsIdentity { a with sort := .ctor ⟨⟨"SortK"⟩⟩ [] }}"
  IO.println s!"another variable: {Parse.aliasIsIdentity { a with body := .var (.svar ⟨⟨⟨"@Y"⟩⟩, a.sort⟩) }}"

/-- info: hw-allpath-alias: read; twin: read; Semantics equal: true; class: [(read identityAlias, 1)] -/
#guard_msgs in
#eval show IO Unit from do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile hw) | IO.println "KORE read error"
  let unalias := editRhs fun r => match r with
    | .app _ _ [φ] => φ
    | r => r
  let k' := unalias k
  match Parse.parse k, Parse.parse k' with
  | .ok d, .ok d' =>
    let cls := (Parse.classCounts k).filter fun (n, _) => n == "read identityAlias"
    IO.println s!"hw-allpath-alias: read; twin: read; Semantics equal: {reprStr d.sem == reprStr d'.sem}; class: {cls}"
  | _, _ => IO.println "refused"

/--
info: weakExistsFinally: read; Semantics equal: true; class: [(read identityAlias, 1)]
allPathGlobally: read; Semantics equal: true; class: [(read identityAlias, 1)]
-/
#guard_msgs in
#eval show IO Unit from do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile hw) | IO.println "KORE read error"
  let .ok d' := Parse.parse (editRhs (fun r => match r with
    | .app _ _ [φ] => φ
    | r => r) k) | IO.println "twin refused"
  for n in ["weakExistsFinally", "allPathGlobally"] do
    let k₁ := editRhs (fun r => match r with
      | .app h ss [φ] => if h.ident.name == "weakAlwaysFinally" then .app ⟨⟨n⟩⟩ ss [φ] else r
      | r => r) k
    match Parse.parse k₁ with
    | .ok d =>
      let cls := (Parse.classCounts k₁).filter fun (c, _) => c == "read identityAlias"
      IO.println s!"{n}: read; Semantics equal: {reprStr d.sem == reprStr d'.sem}; class: {cls}"
    | .error r => IO.println s!"{n}: {r.reason.name}"

/--
info: two arguments: aliasApplication: weakAlwaysFinally: an alias of K's prelude heading the right side of the rewrite axiom (the form kompile writes for a rule of a module carrying all-path or one-path), not at one sort and one argument or not defined by the text as the identity on its argument (aliasIsIdentity); not read as its argument
no sort argument: aliasApplication: weakAlwaysFinally: an alias of K's prelude heading the right side of the rewrite axiom (the form kompile writes for a rule of a module carrying all-path or one-path), not at one sort and one argument or not defined by the text as the identity on its argument (aliasIsIdentity); not read as its argument
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println s!"two arguments: {← verdict hw (editRhs fun r => match r with
    | .app h ss [φ] => .app h ss [φ, φ]
    | r => r)}"
  IO.println s!"no sort argument: {← verdict hw (editRhs fun r => match r with
    | .app h _ [φ] => .app h [] [φ]
    | r => r)}"
