/-
  `#review_cone`: the declarations a reader must review to know what a list of root declarations
  means (checked layer; a meta program, not part of the specification).

      #review_cone "title" [root₁, root₂, …]
      #review_cone "title" [root₁, root₂, …] to "path/to/output.txt"
      #review_cone "title" [root₁, …] opaque [d₁, …] to "path/to/output.txt"

  `opaque [d₁, …]`: the listed definitions are read by their type only (their value is not
  entered), for a definition whose every use in the roots is a property that a root asserts of
  it (as `refStep` in soundness and completeness, declared `opaque` at the freeze).

  The cone is the least set of declarations that contains the roots and is closed under:
  - the constants occurring in the type of a reached declaration;
  - the constants occurring in the value of a reached definition (`def`, `abbrev`, `instance`),
    except inside proofs: a subterm whose type is a proposition is not entered (by proof
    irrelevance its content does not affect what the definition means), and a reached theorem is
    listed but neither its type nor its proof is entered, unless it is a root;
  - for an inductive type or structure: the types of the inductive types declared with it and
    of their constructors.
  A declaration of Lean's own library (modules `Init.*`, `Std.*`, `Lean.*`) is trusted: it is
  counted, grouped by its first name component, and not entered.

  Generated declarations are folded into the declaration they belong to and are not listed:
  constructors and projections into their type; recursors, `casesOn`, `noConfusion`, `below`,
  `brecOn`, `sizeOf` and similar into their inductive type (and not entered: the kernel or the
  elaborator derives them from the type); matchers, `_proof_N`, `_unsafe_rec`, `eq_N`, `eq_def`
  and other names with an internal component into the nearest enclosing declaration that is not
  generated (matchers are entered, since they carry the case split of their parent; Lean shares
  one matcher between declarations with the same case shape, so a matcher is folded into the
  declaration whose type or value uses it).

  Output, per listed declaration: name, kind, module, the source line range that
  `Lean.findDeclarationRanges?` records for it (the whole command, doc comment included; for a
  theorem, which is listed only as a root, up to the first line containing `:=`, so its proof is
  not counted), and the listed declaration whose type or value first met it (`via`). Per
  module: the number of declarations and the number of distinct source lines they cover. The
  lines between declarations (module doc comments, `namespace`, `variable`, `open`, blank lines
  between commands) are not counted.
-/
import Lean

namespace KoreAML.ReviewCone

open Lean Meta Elab Command

/-- The modules whose declarations are trusted rather than reviewed. -/
def trustedRoots : List Name := [`Init, `Std, `Lean]

def moduleOf? (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!

def isTrusted (env : Environment) (n : Name) : Bool :=
  match moduleOf? env n with
  | some m => trustedRoots.contains m.getRoot
  | none => false

/-- Last name components of declarations that are generated from their parent. -/
def generatedSuffixes : List String :=
  ["rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "sizeOf_spec", "injEq", "inj",
   "ctorIdx", "toCtorIdx", "eq_def", "splitter", "eq_unfold", "ofNat_ctorIdx", "ctorElim",
   "ctorElimType", "induct", "mutual_induct", "default"]

/-- Prefixes of the last name component of generated declarations (`below_1`, `brecOn_2`, …). -/
def generatedLastPrefixes : List String := ["below", "ibelow", "brecOn", "binductionOn", "rec_"]

/-- Prefixes of any name component of generated declarations. -/
def generatedPrefixes : List String :=
  ["match_", "proof_", "eq_", "_", "fun_cases", "mutual_"]

/-- The name has a component that only generated declarations have. -/
def isGeneratedName (n : Name) : Bool :=
  (n.components.any fun c => match c with
    | .str _ s => generatedPrefixes.any (s.startsWith ·)
    | .num _ _ => true
    | .anonymous => false) ||
  (match n with
    | .str _ s => generatedSuffixes.contains s || generatedLastPrefixes.any (s.startsWith ·)
    | _ => false)

/-- The declaration a generated one belongs to (itself if it is not generated). -/
partial def parentOf (env : Environment) (n : Name) : Name :=
  match env.find? n with
  | some (.ctorInfo c) => c.induct
  | some (.recInfo _) => n.getPrefix
  | _ =>
    if let some info := env.getProjectionFnInfo? n then
      match env.find? info.ctorName with
      | some (.ctorInfo c) => c.induct
      | _ => n
    else if isGeneratedName n && !n.getPrefix.isAnonymous then
      let p := n.getPrefix
      if (env.find? p).isSome && !isGeneratedName p then p else parentOf env p
    else n

/-- Generated from an inductive type and not entered. -/
def isTypeGenerated (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.recInfo _) => true
  | some (.ctorInfo _) => false
  | _ => match n with
    | .str p s => (generatedSuffixes.contains s || generatedLastPrefixes.any (s.startsWith ·)) &&
        (match env.find? (parentOf env p) with
        | some (.inductInfo _) => true
        | _ => false)
    | _ => false

structure Entry where
  name : Name
  via : Name
  kind : String
  module : Name
  lines : Option (Nat × Nat)

structure State where
  /-- listed declarations (parents), in the order reached -/
  listed : Array Name := #[]
  listedSet : NameSet := {}
  /-- declarations whose contents were entered or are queued -/
  entered : NameSet := {}
  queue : Array Name := #[]
  trusted : NameSet := {}
  theorems : NameSet := {}
  folded : NameSet := {}
  /-- the listed declaration whose type or value first met each listed one -/
  via : NameMap Name := {}
  current : Name := .anonymous
  /-- definitions whose value is not entered (`opaque [...]`): only their type is reviewed -/
  cut : NameSet := {}
  seenExpr : Std.HashSet Expr := {}

abbrev M := StateRefT State MetaM

def kindOf (env : Environment) (n : Name) : MetaM String := do
  match env.find? n with
  | some (.thmInfo _) => return "theorem"
  | some (.axiomInfo _) => return "axiom"
  | some (.opaqueInfo _) => return "opaque"
  | some (.quotInfo _) => return "quot"
  | some (.inductInfo _) => return if isStructure env n then "structure" else "inductive"
  | some (.defnInfo _) =>
    if isInstanceCore env n then return "instance"
    else if (← getReducibilityStatus n) == .reducible then return "abbrev"
    else return "def"
  | some (.ctorInfo _) => return "constructor"
  | some (.recInfo _) => return "recursor"
  | none => return "?"

def enqueue (n : Name) : M Unit := do
  unless (← get).entered.contains n do
    modify fun s => { s with entered := s.entered.insert n, queue := s.queue.push n }

/-- Record a constant met in a type or a value. -/
def reach (roots : NameSet) (n : Name) : M Unit := do
  let env ← getEnv
  if isTrusted env n then
    modify fun s => { s with trusted := s.trusted.insert n }
    return
  -- Lean shares a matcher between declarations with the same case shape, so a matcher is
  -- folded into the declaration that uses it, not into the one its name comes from.
  let cur := (← get).current
  let p := if Meta.isMatcherCore env n && !cur.isAnonymous then cur else parentOf env n
  if p != n then modify fun s => { s with folded := s.folded.insert n }
  unless (← get).listedSet.contains p do
    if (env.find? p) matches some (.thmInfo _) && !roots.contains p then
      modify fun s => { s with theorems := s.theorems.insert p }
      return
    modify fun s => { s with listed := s.listed.push p, listedSet := s.listedSet.insert p,
                              via := s.via.insert p s.current }
  enqueue p
  -- a generated declaration other than the type's own recursors etc. is entered too
  if p != n && !isTypeGenerated env n && !((env.find? n) matches some (.ctorInfo _)) &&
      !((env.find? n) matches some (.thmInfo _)) then
    enqueue n

/-- A data constructor application is not a proof; this avoids type inference on large data. -/
def isDataCtor (env : Environment) (f : Expr) : Bool :=
  match f with
  | .const n _ => match env.find? n with
    | some (.ctorInfo c) => match env.find? c.induct with
      | some (.inductInfo i) => !i.type.getForallBody.isProp && !(i.type.getForallBody matches .sort .zero)
      | _ => false
    | _ => false
  | _ => false

def isProofSafe (e : Expr) : MetaM Bool := do
  try isProof e catch _ => return false

partial def visit (roots : NameSet) (e : Expr) : M Unit := do
  if (← get).seenExpr.contains e then return
  modify fun s => { s with seenExpr := s.seenExpr.insert e }
  match e with
  | .const n _ => reach roots n
  | .mdata _ b => visit roots b
  | .proj s _ b =>
    if ← isProofSafe e then return
    reach roots s; visit roots b
  | .app .. =>
    let f := e.getAppFn
    unless isDataCtor (← getEnv) f do
      if ← isProofSafe e then return
    visit roots f
    for a in e.getAppArgs do visit roots a
  | .lam .. =>
    if ← isProofSafe e then return
    lambdaTelescope e fun xs b => do
      for x in xs do visit roots (← inferType x)
      visit roots b
  | .forallE .. =>
    forallTelescope e fun xs b => do
      for x in xs do visit roots (← inferType x)
      visit roots b
  | .letE n t v b _ =>
    visit roots t; visit roots v
    withLetDecl n t v fun x => visit roots (b.instantiate1 x)
  | _ => pure ()

/-- Enter one declaration: its type, and what the rules say of its value and constructors. -/
def enter (roots : NameSet) (n : Name) : M Unit := do
  let env ← getEnv
  let some ci := env.find? n | return
  if isTypeGenerated env n then return
  modify fun s => { s with current := parentOf env n }
  visit roots ci.type
  match ci with
  | .defnInfo d => unless (← get).cut.contains n do visit roots d.value
  | .inductInfo i =>
    for t in i.all do reach roots t
    for c in i.ctors do
      if let some cc := env.find? c then visit roots cc.type
  | _ => pure ()

def run (roots : Array Name) (cut : Array Name := #[]) : M Unit := do
  let rootSet := roots.foldl (·.insert ·) ({} : NameSet)
  modify fun s => { s with cut := cut.foldl (·.insert ·) {} }
  for r in roots do
    modify fun s => { s with listed := s.listed.push r, listedSet := s.listedSet.insert r }
    enqueue r
  let mut i := 0
  while i < (← get).queue.size do
    let n := (← get).queue[i]!
    enter rootSet n
    i := i + 1

/-- The source file of a module of this package (`KcoreSpec/X.lean`, relative to the package
root, where `lake env lean` runs). -/
def sourceOf? (m : Name) : IO (Option String) := do
  let path := System.mkFilePath (m.components.map toString) |>.addExtension "lean"
  if ← path.pathExists then return some (← IO.FS.readFile path) else return none

/-- For a theorem, only its statement is reviewed: the lines from the start of its range to the
first line that contains `:=` (the start of the proof). -/
def statementEnd (src : String) (a b : Nat) : Nat :=
  let ls := (src.splitOn "\n").toArray
  let hasDef : Nat → Bool := fun i => match ls[i - 1]? with
    | some l => decide ((l.splitOn ":=").length > 1)
    | none => false
  (((List.range (b - a + 1)).map (a + ·)).find? hasDef).getD b

def entryOf (s : State) (n : Name) : MetaM Entry := do
  let env ← getEnv
  let mut lines := (← findDeclarationRanges? n).map fun r => (r.range.pos.line, r.range.endPos.line)
  if let (some (.thmInfo _), some (a, b), some m) := (env.find? n, lines, moduleOf? env n) then
    if let some src ← sourceOf? m then lines := some (a, statementEnd src a b)
  return { name := n, via := (s.via.find? n).getD .anonymous, kind := ← kindOf env n, module := (moduleOf? env n).getD `«(this file)»,
           lines }

def pad (s : String) (k : Nat) : String := s ++ String.ofList (List.replicate (k - s.length) ' ')

/-- The distinct lines covered by a list of ranges. -/
def coveredLines (rs : List (Nat × Nat)) : Nat :=
  let sorted := rs.toArray.qsort (fun a b => a.1 < b.1) |>.toList
  let (total, _) := sorted.foldl (fun (acc : Nat × Nat) (a, b) =>
    let (t, last) := acc
    let a' := max a (last + 1)
    if b < a' then (t, last) else (t + (b - a' + 1), b)) (0, 0)
  total

def report (title : String) (roots cut : Array Name) (s : State) : MetaM String := do
  let env ← getEnv
  let entries ← s.listed.mapM (entryOf s)
  -- modules in import order
  let modIdx := fun (m : Name) => (env.header.moduleNames.idxOf? m).getD env.header.moduleNames.size
  let mods := (entries.map (·.module)).toList.eraseDups.toArray.qsort (fun a b => modIdx a < modIdx b)
  let mut out := s!"# review cone: {title}\n"
  out := out ++ s!"# roots: {", ".intercalate (roots.toList.map toString)}\n"
  unless cut.isEmpty do
    out := out ++ s!"# read as opaque (type only, value not entered): {", ".intercalate (cut.toList.map toString)}\n"
  out := out ++ "# computed by #review_cone (KcoreSpec/ReviewCone.lean); rule: types of reached declarations, values of reached non-theorem definitions, proofs not entered, Init/Std/Lean trusted\n\n"
  let mut summary : Array (Name × Nat × Nat × Option Nat) := #[]
  for m in mods do
    let es := (entries.filter (·.module == m)).qsort fun a b =>
      (a.lines.map (·.1)).getD 0 < (b.lines.map (·.1)).getD 0
    let lines := coveredLines (es.toList.filterMap (·.lines))
    let fileLines := (← sourceOf? m).map fun src => (src.splitOn "\n").length - 1
    summary := summary.push (m, es.size, lines, fileLines)
    out := out ++ s!"## {m}  ({es.size} declarations, {lines} lines)\n"
    for e in es do
      let r := match e.lines with
        | some (a, b) => s!"{a}-{b}"
        | none => "?"
      let via := if e.via.isAnonymous then "root" else s!"via {e.via}"
      out := out ++ s!"  {pad r 10} {pad e.kind 10} {pad e.name.toString 44} {via}\n"
    out := out ++ "\n"
  out := out ++ "## lines per module (cone lines, declarations, lines of the whole file in this package)\n"
  let mut total := 0
  let mut totalDecls := 0
  let mut totalFile := 0
  for (m, k, l, f) in summary do
    let fs := match f with | some n => toString n | none => "-"
    out := out ++ s!"  {pad (toString l) 6} {pad (toString k) 5} {pad fs 6} {m}\n"
    total := total + l
    totalDecls := totalDecls + k
    totalFile := totalFile + f.getD 0
  out := out ++ s!"  {pad (toString total) 6} {pad (toString totalDecls) 5} {pad (toString totalFile) 6} total\n\n"
  -- the roots as the elaborator produced them, to compare with their source text
  out := out ++ "## roots, as elaborated (type of a theorem, value of a definition)\n"
  for r in roots do
    let some ci := env.find? r | continue
    let e := match ci with
      | .defnInfo d => d.value
      | _ => ci.type
    let txt := toString (← ppExpr e)
    let n := (txt.splitOn "\n").length
    if n > 40 then out := out ++ s!"  {r} := ({n} lines, not printed)\n"
    else out := out ++ s!"  {r} :=\n    {txt.replace "\n" "\n    "}\n"
  out := out ++ "\n"
  -- theorems met in values outside proofs
  let thms := s.theorems.toList.toArray.qsort (·.toString < ·.toString)
  out := out ++ s!"## theorems met, not entered ({thms.size})\n"
  for t in thms do out := out ++ s!"  {t}\n"
  out := out ++ s!"\n## generated declarations folded into their parent: {s.folded.size}\n\n"
  -- trusted library, grouped by first component
  let groups := s.trusted.toList.foldl (fun (acc : Std.HashMap Name (List Name)) n =>
    acc.insert n.getRoot (n :: acc.getD n.getRoot [])) {}
  let gs := groups.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  out := out ++ s!"## trusted library (Init, Std, Lean): {s.trusted.size} declarations, by first name component\n"
  for (g, ns) in gs do
    let names := (ns.toArray.qsort (·.toString < ·.toString)).toList.map toString
    out := out ++ s!"  {pad (toString ns.length) 4} {pad g.toString 24} {" ".intercalate names}\n"
  return out

syntax (name := reviewConeCmd)
  "#review_cone " str " [" ident,* "]" (" opaque " "[" ident,* "]")? (" to " str)? : command

@[command_elab reviewConeCmd] def elabReviewCone : CommandElab := fun stx => do
  match stx with
  | `(#review_cone $title [$roots,*] $[opaque [$cuts,*]]? $[to $path]?) =>
    let resolve := fun (r : Ident) => liftCoreM <| realizeGlobalConstNoOverloadWithInfo r
    let names ← roots.getElems.mapM resolve
    let cut ← match cuts with
      | some cs => cs.getElems.mapM resolve
      | none => pure #[]
    let text ← liftTermElabM do
      let ((), s) ← (run names cut).run {}
      report title.getString names cut s
    match path with
    | some p => IO.FS.writeFile p.getString text; logInfo m!"wrote {p.getString}"
    | none => logInfo text
  | _ => throwUnsupportedSyntax

end KoreAML.ReviewCone
