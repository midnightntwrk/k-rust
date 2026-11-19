/-
  `kcore gen definition.kore OUTDIR NAME [--tie]` (ARCHITECTURE.md §3.8): writes a Lake package for
  the definition. Nothing in it is edited by hand; the user's package imports it and holds their
  statements and the proofs of named obligations.

  The generator runs KCore's `parse` (the one the tie checks) by compiled code, and uses what it
  computes only as data the kernel checks: the tables (`T = tables c`), the determinism index
  (`idxOK`), each kind's obligations (the indices its decider does not confirm: the kind's decision
  fails without them, and each is a premise of the kind's theorem), the block boundaries. A wrong
  choice makes a module fail to build; it cannot make a theorem false.

  Before writing anything it accounts for the KORE's sentences (Account.lean): it prints each
  class's count, and stops with every refusal when `parse` refuses the text, or with the
  sentences classified read that the definition does not account for (`unconsumed`) when there
  are any.

  The package (NAME the namespace and the directory):
  - `NAME/definition.kore`: the input;
  - `NAME/Core.lean`: the definition as a term (`definition_of`: parsed, added by `addDecl`, not
    printed and not compiled), `c` its semantics;
  - `NAME/Names.lean`: readable names of its own symbols and sorts (checked against the KORE names),
    its rules' numbers, its cells' paths and getters;
  - `NAME/Syntax.lean`: readable terms (`KCore.Tm`): a function per constructor (its own, the
    library's, the configuration's cells), named after its production (`ctorNames`), with its value
    by `rfl`; each subsort as a coercion that is the injection (scoped: `open NAME.Syntax`);
    `top_sorts`, the inversion of a configuration's sort at the top cell. With `--core` the symbols
    and sorts are numbers (no `Names`), and `--no-syntax` leaves the module out;
  - `NAME/Facts/*.lean`: the tables (`T_eq`), `ok` (a head decision and blocks of rules), `srReady`,
    `matchReady`, `clausesFixed`, `uses`, the determinism index and blocks of its rows, and the
    lazy obligations (`Lazy`: the arguments a short-circuiting evaluation may skip that
    `definedArg` does not show defined, stated with or without the tie);
    `NAME/Facts.lean` joins them; `NAME/Facts/Terminates.lean`: every function terminates
    (`terminates`) and every `[total]` one is total (`totals`), under the named obligations if
    any, with or without the tie;
  - `NAME/Surface.lean`: `step_iff` instantiated, each rule and function clause as data, `step_cases`,
    `rules_cases` (a rule is one of them, one case per rule), and `fireFacts`, the instance of
    `KCore.FireFacts` the tactic `fire` reads (`ok`, `srReady`, `matchReady`, the smallest priority
    of a rule, `prio_floor`);
  - `NAME/Kinds/*.lean`: determinism, the counter cell's frame and invariant, and noninterference
    for the cells `--high` and `--keyed` name. Each is a `Kind` (KcoreSpec/Kind.lean) emitted one
    way: its obligations listed (the indices its decider does not confirm), its decision by the
    kernel (in blocks for determinism, `Facts/DetRows*`), and its theorem by `Kind.of_decided` or
    `Kind.of_blocks` with each listed obligation a premise. Determinism's indices are pairs of
    rules, the diagonal included (a rule whose match is not shown to fix its right-hand side is an
    obligation (i, i)); `deterministic_except` lists them in its conclusion instead. With
    determinism's obligations, noninterference is stated relative to an invariant, and each of them
    where it holds is a premise. `NAME/Certs/*.lean`: krust's runs as certificates (none where a
    parameter is an open generator, as the root module's header says). Every kind and
    certificate is stated for every interpretation H of the parameters (`c.withHooks H`), from
    conditions decided once on the data, which do not read the interpretation;
  - with `--tie`, `NAME/Tie/*.lean`: the tie by blocks, each module one decision of bounded size.
    `Kore`: the KORE as a term, its user module in segments. `ParseData`, `ScanAll`, `Scan*`, `Env`,
    `Prods*`, `Rules*`, `Asm*`, `Assemble`, `Parse`: `parse kore = .ok defn` from its stages (the
    prelude, the scan a block of segments at a time with no sentence refused, the names, the
    productions and the rules a block at a time, the assembly in its parts). `Emit*`, `Emit`:
    `Reordered defn.emit kore`, the user module's blocks against the KORE's segments a slice at a
    time. `SortNames`, `SymNames`, `Faith`, `Wf`: `wf defn`, the names' distinctness by codes,
    `ok` from the facts, `faithOK` one kernel decision per conjunct, and the named obligations'
    lists (`Obligations`). `Tie`: `Tied kore`, from the three. `NAME.Sound` (built with the tie):
    soundness, `sound : Sound defn`, and completeness for every step function `ref`,
    `complete ref : Complete defn ref`, from `wf defn` and the named obligations (unconditional
    where none is named), and `sound_withHooks`, `complete_withHooks` for every interpretation of
    the parameters; `coreOK_defn : defn.sem.coreOK = true`, from `wf defn`, and from it, for
    functions that meet the hypothesis `FnHyp`, `sound_hyp hf : SoundC defn.sem` and
    `complete_hyp ref hf : CompleteC defn.sem ref`, which read no named obligation. Without
    `--tie` the package has no tie and `gen` does not compare `emit` with the KORE; with `--wf`
    in place of `--tie`, `NAME/Wf/*.lean` (`SortNames`, `SymNames`, `Faith`, `Wf`: `wf defn` and the
    named obligations, as the tie's) and `NAME.Sound`, in `modules.txt`: soundness and
    completeness are facts of `defn`, whatever text it was read from, and without the tie the
    reader is trusted to have read the text (`kcore account`). After `NAME.Sound` (with the tie
    or `--wf`), what the deciders leave of `FnHyp`, as with `--core` below (`NAME.FnHyp.*`,
    `NAME.FnHyp`): where no fact is named, `fnHyp_defn : FnHyp defn.sem` outright (for every
    interpretation total on the declared-total parameters, where there are parameters), which
    `sound_hyp` and `complete_hyp` take;
  - with `--core` in place of `--tie` and `--wf`, for a definition that meets `coreOK` whether or
    not it meets `okAll` and `wf`: only the core, its tables, `NAME/CoreOK/*.lean` (one
    kernel decision per conjunct of `coreOK`, the clauses' and rules' sort checks read from the
    tables in blocks; the three conjuncts that read names decided on the names' codes, a table of
    them checked by blocks of rows: `Codes`, `SymCodes*`, `SortCodes*`, `NameCodes`),
    `NAME.CoreOK` (`coreOK_defn`, joined), `NAME.Sound` (`sound_hyp`,
    `complete_hyp` from it), and what the deciders leave of `FnHyp`: a rank of the functions
    (`NAME.FnHyp.Order`), the parameters the text declares total (`NAME.FnHyp.Params`), the four
    named lists each decided in its own module (`NAME.FnHyp.Term`, `Total`, `Agree` from the
    tables, `Match`), and `NAME.FnHyp` (`namedFacts`, the named facts with their source locations;
    `Obl`, `KCore.FnObligations` at the rank; `fnHyp_defn`, `sound_defn`, `complete_defn` from it:
    for a definition with parameter symbols no registry hook implements, for every interpretation
    total on the parameters the text declares total, `HooksTotal`; without such parameters also
    `fnHyp_withHooks_defn`, `sound_withHooks_defn`, `complete_withHooks_defn` under `OblH H`, for
    every interpretation H). Under the same facts, for every H, `NAME.FnHyp` states `consistent`,
    `sound_at`, `complete_at` and, where the core is `CExec.execReady` and the package has its facts,
    `run_exact`, each concluding `Consistent … ∧ …`; where facts are named they are hypotheses and
    the names end in `_of`. Such a package states no `wf`, `sound`, `complete`, facts, surface,
    kinds or certificates, and has no `NAME.Names` (whose `names_ok` exceeds the default
    heartbeats at KEVM's size and which `coreOK` does not read);
  - `NAME.lean`, `lakefile.toml`, `modules.txt` (the build order for `gen/build.sh`), and with
    `--tie` `tie.txt` (the tie's modules, built with `gen/build.sh --tie`).

  A core outside `ok` (a left-hand side with a collection pattern the executable matcher's theorems
  do not cover), or with a clause whose patterns `clauseFixed` does not show to fix its variables
  (the coherence the executable evaluation's completeness reads is shown from `clausesFixed`), gets the core, its names, its
  tie, and of the facts the tables, `okAll`, `srReady` and subject reduction from them
  (`rhs_sorted`, `step_of_apply`); no surface, kinds or certificates.
-/
import KcoreSpec

open KCore

namespace KcoreGen

/-! ## Names -/

/-- K's encoding of a symbol in a KORE identifier: between quotes, 4-character codes. -/
def kCodes : List (String × String) :=
  [("Spce", " "), ("Bang", "!"), ("Quot", "\""), ("Hash", "#"), ("Dolr", "$"), ("Perc", "%"),
   ("And-", "&"), ("Apos", "'"), ("LPar", "("), ("RPar", ")"), ("Star", "*"), ("Plus", "+"),
   ("Comm", ","), ("Hyph", "-"), ("Stop", "."), ("Slsh", "/"), ("Coln", ":"), ("SCln", ";"),
   ("-LT-", "<"), ("Eqls", "="), ("-GT-", ">"), ("Ques", "?"), ("-AT-", "@"), ("LSqB", "["),
   ("RSqB", "]"), ("Bash", "\\"), ("Xor-", "^"), ("Unds", "_"), ("BQuo", "`"), ("LBra", "{"),
   ("Pipe", "|"), ("RBra", "}"), ("Tild", "~")]

partial def decodeCodes (cs : List Char) : String :=
  match cs with
  | a :: b :: c :: d :: rest =>
    let k := String.ofList [a, b, c, d]
    match kCodes.lookup k with
    | some v => v ++ decodeCodes rest
    | none => String.ofList cs
  | _ => String.ofList cs

/-- A KORE identifier read back: `Lbl'Unds'+'Unds'` is `_+_`. -/
def decodeK (s : String) : String :=
  let s := if s.startsWith "Lbl" then s.drop 3 |>.toString else s
  let parts := s.splitOn "'"
  String.join (parts.zipIdx.map fun (p, i) => if i % 2 == 1 then decodeCodes p.toList else p)

/-- A name usable as a Lean identifier: `«…»` around it, guillemets and newlines dropped. -/
def quoteId (s : String) : String :=
  let s := String.ofList (s.toList.filter fun ch => ch != '«' && ch != '»' && ch != '\n')
  if s.isEmpty then "«_»" else "«" ++ s ++ "»"

/-- Distinct readable names: a repeated one gets the number appended. -/
def uniqueNames (ns : List (Nat × String)) : List (Nat × String) :=
  ns.map fun (i, n) =>
    if (ns.filter (·.2 == n)).length > 1 then (i, s!"{n}_{i}") else (i, n)

structure Ctx where
  ns : String
  d : Definition
  T : Tables
  symIds : List (Nat × String)
  srtIds : List (Nat × String)

def Ctx.c (g : Ctx) : Semantics := g.d.sem

/-- The registry's named symbols and sorts (FixedSignature.lean). -/
def regSymConsts : List (Nat × String) := [(0, "KCore.kseq"), (1, "KCore.dotk"), (2, "KCore.kconfigValue"), (3, "KCore.boolNot"), (4, "KCore.boolAnd"), (5, "KCore.boolAndThen"), (6, "KCore.boolOr"), (7, "KCore.boolOrElse"), (8, "KCore.boolXor"), (9, "KCore.boolImplies"), (10, "KCore.boolEq"), (11, "KCore.boolNe"), (12, "KCore.intAdd"), (13, "KCore.intSub"), (14, "KCore.intMul"), (15, "KCore.intTDiv"), (16, "KCore.intTMod"), (17, "KCore.intEDiv"), (18, "KCore.intEMod"), (19, "KCore.intLt"), (20, "KCore.intLe"), (21, "KCore.intGt"), (22, "KCore.intGe"), (23, "KCore.intEq"), (24, "KCore.intNe"), (25, "KCore.intMin"), (26, "KCore.intMax"), (27, "KCore.intAbs"), (28, "KCore.freshInt"), (29, "KCore.kEq"), (30, "KCore.kNe"), (31, "KCore.mapUnit"), (32, "KCore.mapElem"), (33, "KCore.mapConcat"), (34, "KCore.mapUpdate"), (35, "KCore.mapRemove"), (36, "KCore.mapLookup"), (37, "KCore.mapLookupOrDefault"), (38, "KCore.mapInKeys"), (39, "KCore.mapSize"), (40, "KCore.mapRemoveAll"), (41, "KCore.mapKeys"), (42, "KCore.setUnit"), (43, "KCore.setElem"), (44, "KCore.setConcat"), (45, "KCore.setUnion"), (46, "KCore.setIntersect"), (47, "KCore.setDifference"), (48, "KCore.setIn"), (49, "KCore.setInclusion"), (50, "KCore.setSize"), (51, "KCore.isK"), (52, "KCore.isKItem"), (71, "KCore.topLabel"), (72, "KCore.topFragLabel"), (73, "KCore.counterLabel"), (74, "KCore.noCounter"), (151, "KCore.unboxKConfigValue")]
def regSrtConsts : List (Nat × String) := [(0, "KCore.Srt.k"), (1, "KCore.Srt.kitem"), (2, "KCore.Srt.bool"), (3, "KCore.Srt.int"), (4, "KCore.Srt.kconfigVar"), (5, "KCore.Srt.list"), (6, "KCore.Srt.map"), (7, "KCore.Srt.set"), (8, "KCore.Srt.mint"), (9, "KCore.Srt.ident"), (10, "KCore.Srt.string"), (11, "KCore.Srt.float"), (12, "KCore.Srt.ioError"), (13, "KCore.Srt.ioFile"), (14, "KCore.Srt.ioInt"), (15, "KCore.Srt.ioString"), (16, "KCore.Srt.stream"), (17, "KCore.Srt.top"), (18, "KCore.Srt.topFrag"), (19, "KCore.Srt.counter"), (20, "KCore.Srt.counterOpt")]

def Ctx.sym (g : Ctx) (f : Sym) : String :=
  match g.symIds.lookup f, regSymConsts.lookup f with
  | some n, _ => s!"{g.ns}.Sym.{quoteId n}"
  | none, some k => k
  | none, none => s!"({f} : KCore.Sym)"

def Ctx.srt (g : Ctx) (s : Srt) : String :=
  match g.srtIds.lookup s, regSrtConsts.lookup s with
  | some n, _ => s!"{g.ns}.Srt.{quoteId n}"
  | none, some k => k
  | none, none => s!"({s} : KCore.Srt)"

def litStr : Lit → String
  | .int i => s!"(.int ({i}))"
  | .bool b => s!"(.bool {b})"
  | .tok s => s!"(.tok {s.quote})"
  | .float p e b => s!"(.float {p} {e} {b})"

partial def Ctx.term (g : Ctx) : Term → String
  | .var i => s!"(.var {i})"
  | .app f ts => s!"(.app {g.sym f} [{", ".intercalate (ts.map g.term)}])"
  | .inj a b t => s!"(.inj {g.srt a} {g.srt b} {g.term t})"
  | .as t i => s!"(.as {g.term t} {i})"
  | .dv s l => s!"(.dv {g.srt s} {litStr l})"

def Ctx.srts (g : Ctx) (ss : List Srt) : String := "[" ++ ", ".intercalate (ss.map g.srt) ++ "]"

def Ctx.optTerm (g : Ctx) : Option Term → String
  | some t => s!"(some {g.term t})"
  | none => "none"

def Ctx.rule (g : Ctx) (r : Rule) : String :=
  s!"\{ vars := {g.srts r.vars},\n    lhs := {g.term r.lhs},\n    req := {g.optTerm r.req},\n    rhs := {g.term r.rhs},\n    ens := {g.optTerm r.ens},\n    prio := {r.prio} }"

def Ctx.clause (g : Ctx) (cl : Clause) : String :=
  s!"\{ vars := {g.srts cl.vars},\n    pats := [{", ".intercalate (cl.pats.map g.term)}],\n    req := {g.optTerm cl.req},\n    rhs := {g.term cl.rhs},\n    ens := {g.optTerm cl.ens},\n    prio := {cl.prio} }"

/-! ## The determinism index: paths chosen per definition -/

/-- The index paths of a pattern below the root, up to depth `k` (an injection's argument is 0). -/
def Ctx.site (g : Ctx) : LazySite → String
  | .ruleReq i => s!"(.ruleReq {i})"
  | .ruleRhs i => s!"(.ruleRhs {i})"
  | .ruleEns i => s!"(.ruleEns {i})"
  | .clauseReq f j => s!"(.clauseReq {g.sym f} {j})"
  | .clauseRhs f j => s!"(.clauseRhs {g.sym f} {j})"
  | .clauseEns f j => s!"(.clauseEns {g.sym f} {j})"

def Ctx.lazyOcc (g : Ctx) (o : LazyOcc) : String :=
  s!"\{ site := {g.site o.site}, vars := {g.srts o.vars}, path := {reprStr o.path}, sym := {g.sym o.sym},\n    guard := {g.term o.guard}, skipWhen := {o.skipWhen}, pos := {o.pos},\n    skipped := {g.term o.skipped} }"

/-- An occurrence as the listing names it: the rule (its index, its label) or the function and
clause (the function's KORE name decoded, the clause's index and label), the place in it, and the
argument skipped. -/
def lazyDesc (d : Definition) (o : LazyOcc) : String :=
  let c := d.sem
  let lbl := fun (l : Option String) => match l with | some l => s!" (`{l}`)" | none => ""
  let fnPres := fun (f : Sym) => ((withPres c.fns d.pres.fns).find? (·.1.label == f)).map (·.2)
  let clLbl := fun (f : Sym) (j : Nat) => lbl ((fnPres f).bind fun fp => (fp.clauses[j]?).bind (·.label))
  let place := match o.site with
    | .ruleReq i => s!"rule {i}{lbl ((d.pres.rules[i]?).bind (·.label))}, `requires`"
    | .ruleRhs i => s!"rule {i}{lbl ((d.pres.rules[i]?).bind (·.label))}, right-hand side"
    | .ruleEns i => s!"rule {i}{lbl ((d.pres.rules[i]?).bind (·.label))}, `ensures`"
    | .clauseReq f j => s!"function `{decodeK (c.symName f)}` clause {j}{clLbl f j}, `requires`"
    | .clauseRhs f j => s!"function `{decodeK (c.symName f)}` clause {j}{clLbl f j}, right-hand side"
    | .clauseEns f j => s!"function `{decodeK (c.symName f)}` clause {j}{clLbl f j}, `ensures`"
  s!"{place}, at {reprStr o.path}: argument {o.pos} of `{decodeK (c.symName o.sym)}`, skipped when argument 0 is {o.skipWhen}"

partial def termPaths (k : Nat) : Term → List (List Nat)
  | .app _ ts => if k == 0 then [] else
      (ts.zipIdx.flatMap fun (t, i) => [i] :: (termPaths (k - 1) t).map (i :: ·))
  | .inj _ _ t => if k == 0 then [] else [0] :: (termPaths (k - 1) t).map (0 :: ·)
  | .as t _ => termPaths k t
  | _ => []

/-- The subterm at an index path (as `pkeys` descends). -/
partial def termAt : Term → List Nat → Option Term
  | t, [] => some t
  | .as t _, P => termAt t P
  | .app _ ts, i :: P => (ts[i]?).bind (termAt · P)
  | .inj _ _ t, 0 :: P => termAt t P
  | _, _ => none

/-- Pairs of rules of one priority whose keys are compatible at the paths: those that reach
`apart` in the determinism decision. -/
def compatPairs (c : Semantics) (T : Tables) (paths : List (List Nat)) : List (Nat × Nat) :=
  let ks := (c.rules.map (Det.ruleKeys c T paths)).toArray
  let ps := (c.rules.map (·.prio)).toArray
  (List.range ps.size).flatMap fun i => ((List.range ps.size).filter (i < ·)).filterMap fun j =>
    if ps[i]! == ps[j]! && Det.compat ks[i]! ks[j]! then some (i, j) else none

/-- The default paths, then greedily, up to 4 more below the k cell's first item that most reduce
the compatible pairs. -/
def choosePaths (c : Semantics) (T : Tables) : List (List Nat) := Id.run do
  let base := Det.autoPaths c
  let some P := c.rules.head? >>= fun r => Det.kseqPath r.lhs | return base
  let cands := (c.rules.flatMap fun r => match termAt r.lhs (P ++ [0]) with
      | some t => (termPaths 5 t).map ((P ++ [0]) ++ ·)
      | none => []).eraseDups.filter (!base.contains ·)
  let mut paths := base
  let mut best := (compatPairs c T paths).length
  for _ in [0:4] do
    let mut pick : Option (List Nat × Nat) := none
    for q in cands do
      if !paths.contains q then
        let n := (compatPairs c T (paths ++ [q])).length
        if n < best && (pick.map fun p => decide (n < p.2)).getD true then pick := some (q, n)
    match pick with
    | some (q, n) => paths := paths ++ [q]; best := n
    | none => break
  return paths

/-! ## Blocks -/

/-- Consecutive blocks `(lo, len)` of `0..n`, a block closing when its weight would pass `budget`. -/
def blocks (n : Nat) (w : Nat → Nat) (budget : Nat) : List (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  let mut lo := 0
  let mut acc := 0
  for i in [0:n] do
    if acc + w i > budget && i > lo then
      out := out.push (lo, i - lo); lo := i; acc := 0
    acc := acc + w i
  if n > lo then out := out.push (lo, n - lo)
  return out.toList

partial def termSize : Term → Nat
  | .app _ ts => 1 + (ts.map termSize).foldl (· + ·) 0
  | .inj _ _ t => 1 + termSize t
  | .as t _ => 1 + termSize t
  | _ => 1

/-! ## Run certificates from krust -/

/-- A ground KORE pattern (a configuration krust prints) as a value, under the definition's
numbers: constructors and their arguments, injections, domain values. -/
partial def groundOf (c : Semantics) : Kore.Pattern → Option GroundTerm
  | .and _ [p, .top _] => groundOf c p
  | .app h [A, B] [p] => if h.ident.name == "inj" then do
      pure (.inj (← srtId c A) (← srtId c B) (← groundOf c p)) else none
  | .app h [] ps => do
      let f ← symId c h.ident.name
      pure (.ctor f (← ps.mapM (groundOf c)))
  | .dv s l => do let s ← srtId c s; pure (.dv s (← Parse.lit? s l))
  | _ => none
where
  symId (c : Semantics) (n : String) : Option Sym :=
    match regSymNames.idxOf? n with
    | some i => some i
    | none => (c.symNames.idxOf? n).map (nRegSyms + ·)
  srtId (c : Semantics) (s : Kore.KSort) : Option Srt := do
    let n ← KoreAML.Parse.sortName? s
    match regSortNames.idxOf? n with
    | some i => some i
    | none => (c.sortNames.idxOf? n).map (nRegSorts + ·)

/-- A value as Lean source, with the package's readable names. -/
partial def Ctx.ground (g : Ctx) : GroundTerm → String
  | .ctor f ts => s!"(.ctor {g.sym f} [{", ".intercalate (ts.map g.ground)}])"
  | .inj a b t => s!"(.inj {g.srt a} {g.srt b} {g.ground t})"
  | .dv s l => s!"(.dv {g.srt s} {litStr l})"
  | .map s es => s!"(.map {g.srt s} [{", ".intercalate (es.map fun (k, v) => s!"({g.ground k}, {g.ground v})")}])"
  | .set s es => s!"(.set {g.srt s} [{", ".intercalate (es.map g.ground)}])"
  | .list s es => s!"(.list {g.srt s} [{", ".intercalate (es.map g.ground)}])"

/-- The evaluation fuel of the certificate checks the package states (`checkRun`, `stuckCheck`). -/
def certFuel : Nat := 100

/-- The rule number of a certificate's `k`-th step (from 1), from `x` to `y` by the rule id `uid`,
`uids` the rules' ids by number. One sentence can be read as several rules that share its id
(`orSplit`, `requiresOrSplit`); the step is then by the first of them that rewrites `x` to `y`
(`Cert.checkStep` with the package's fuel), and it is an error when none of them does. Where
several of them do, each is a reading of the one sentence the id names and each gives the step as
a step of `Step`, so any of them justifies it: the first is taken. The id of one rule is that
rule's number, and the package's check decides the step. -/
def certRuleOfStep (c : Semantics) (uids : List String) (path : String) (k : Nat) (uid : String)
    (x y : GroundTerm) : Except String Nat :=
  match (List.range uids.length).filter (uids[·]? == some uid) with
  | [] => throw s!"{path}: step {k}: rule id {uid} is no rule's"
  | [i] => pure i
  | is => match is.find? (fun i => match c.rules[i]? with
      | some r => Cert.checkStep c certFuel r x y
      | none => false) with
    | some i => pure i
    | none => throw s!"{path}: step {k}: rule id {uid} is the id of rules {is}, and none of them rewrites the step's configuration to the next"

/-- A krust run (`rpcrun.py`'s JSON: the start, each step's rule id and configuration, how it
ended) as values and rule numbers (`certRuleOfStep`). -/
def readCert (c : Semantics) (p : Presentation) (path : String) :
    IO (Except String (GroundTerm × List (Nat × GroundTerm) × Bool)) := do
  let txt ← IO.FS.readFile path
  let .ok j := Lean.Json.parse txt | return .error s!"{path}: not JSON"
  let pat (s : String) : Except String GroundTerm := do
    let q ← (Kore.parsePattern s).mapError (s!"{path}: KORE: " ++ ·)
    match groundOf c q with
    | some t => pure t
    | none => throw s!"{path}: a configuration outside the ground values KCore reads"
  let uids := (withPres c.rules p.rules).map (·.2.info.uid)
  match (do
    let start ← pat (← (← j.getObjVal? "start").getStr?)
    let (_, steps) ← (← (← j.getObjVal? "steps").getArr?).toList.zipIdx.foldlM
      (fun (x, acc) (st, k) => do
        let uid ← (← st.getObjVal? "uid").getStr?
        let y ← pat (← (← st.getObjVal? "config").getStr?)
        let i ← certRuleOfStep c uids path (k + 1) uid x y
        pure (y, acc.push (i, y)))
      (start, (#[] : Array (Nat × GroundTerm)))
    let steps := steps.toList
    let stuck := ((j.getObjVal? "end").toOption.bind (·.getStr?.toOption)) == some "stuck"
    pure (start, steps, stuck) : Except String _) with
  | .ok r => return .ok r
  | .error e => return .error e

/-! ## Writing the package -/

def hdr (what : String) : String :=
  s!"/- Generated by `kcore gen` (kcore-spec/KcoreGen.lean); not edited by hand. {what} -/\nset_option autoImplicit false\nset_option maxRecDepth 1000000\n"

/-- The tie's permutation hint: each module's sentences of `d.emit` in the KORE's order. -/
def perms (e k : Kore.Definition) : Option (List (List Nat)) :=
  (e.modules.zip k.modules).mapM fun (me, mk) => Id.run do
    let mut used : Array Bool := Array.replicate mk.sentences.length false
    let mut π : List Nat := []
    for s in me.sentences do
      match (List.range mk.sentences.length).find? fun i => !used[i]! && decide (mk.sentences[i]! = s) with
      | some i => used := used.set! i true; π := π ++ [i]
      | none => return none
    return some π

structure Out where
  dir : System.FilePath
  mods : Array String := #[]
  /-- modules not written (a core outside `ok`: no surface, kinds or certificates, and of the facts
  only the tables, `okAll`, `srReady` and subject reduction) -/
  skip : String → Bool := fun _ => false

def Out.write (o : Out) (mod : String) (text : String) : IO Out := do
  if o.skip mod then return o
  let path := o.dir / (mod.replace "." "/" ++ ".lean")
  if let some p := path.parent then IO.FS.createDirAll p
  IO.FS.writeFile path text
  return { o with mods := o.mods.push mod }

def boolStr (b : Bool) : String := if b then "true" else "false"

/-- A proof of `∀ i ∈ [a, b, …], P i` from the proofs `ps` of `P a`, `P b`, … (Lean source). -/
def forallList (ps : List String) : String :=
  ps.foldr (fun p acc => s!"List.forall_mem_cons.mpr ⟨{p}, {acc}⟩") "fun _ h => nomatch h"

/-- The relative path from directory `a` to directory `b` (both absolute, normalized). -/
def relPath (a b : System.FilePath) : String :=
  let xs := a.components.filter (· != ""); let ys := b.components.filter (· != "")
  let n := ((xs.zip ys).takeWhile fun (x, y) => x == y).length
  String.join ((xs.drop n).map fun _ => "../") ++ "/".intercalate (ys.drop n)

/-- The counter cell's position: the last argument of the top cell. -/
def ctrPathOf (p : Presentation) : KCore.Path :=
  [KCore.Pos.arg topLabel (p.config.length + 1) p.config.length]

/-- Each leaf cell's position (through its ancestors) and a getter, as Lean source. -/
partial def cellGo (g : Ctx) (pre : String) : Cell → List String
  | .leaf nm _ ids => [s!"def {quoteId (nm ++ "Path")} : Path := {pre}.arg {g.sym ids.label} 1 0]",
      s!"def {quoteId ("get_" ++ nm)} (x : GroundTerm) : Option GroundTerm := x.atPath {quoteId (nm ++ "Path")}"]
  | .node _ cs ids => cs.zipIdx.flatMap fun (ch, i) => cellGo g (pre ++ s!".arg {g.sym ids.label} {cs.length} {i}, ") ch
  | .coll _ => []

def cellPathsOf (g : Ctx) : List String :=
  let p := g.d.pres
  let n := p.config.length + 1
  let roots := p.config.zipIdx.flatMap fun (x, i) => cellGo g s!"[.arg topLabel {n} {i}, " x
  roots ++ [s!"def counterPath : Path := [.arg topLabel {n} {n - 1}]",
    "def get_generatedCounter (x : GroundTerm) : Option GroundTerm := x.atPath counterPath"]

/-- The modules of `wf defn` and of the theorems it gives: the names' distinctness (`{pre}.SortNames`,
`{pre}.SymNames`), `faithOK` (`{pre}.Faith`), `wf defn` and the named obligations (`{pre}.Wf`), and
`sound` and `complete`, `coreOK_defn`, `sound_hyp` and `complete_hyp` (`Sound`). `pre` is `Tie` in a
tied package and `Wf` in one without the tie:
`wf defn` is a fact of the definition `defn` alone, with or without the tie. -/
def genWf (o : Out) (ns pre : String) (d : Definition) (exec plain : Bool) : IO Out := do
  let mut o := o
  let c := d.sem
  let nSorts := d.emit.sortDecls.length
  let nSyms := d.emit.symbolDecls.length + d.emit.aliasNames.length
  o ← o.write s!"{ns}.{pre}.SortNames" (s!"import KcoreSpec.Tie\nimport {ns}.Core\n" ++ hdr s!"The emitted KORE's {nSorts} sort names are distinct (their codes, sorted, ascend)." ++ s!"
namespace {ns}

theorem sorts_distinct : KoreAML.Distinct.codesDistinct {KoreAML.Distinct.passesFor nSorts} (defn.emit.sortDecls.map (·.name)) = true := by decide +kernel

end {ns}
")
  o ← o.write s!"{ns}.{pre}.SymNames" (s!"import KcoreSpec.Tie\nimport {ns}.Core\n" ++ hdr s!"The emitted KORE's {nSyms} symbol and alias names are distinct (their codes, sorted, ascend)." ++ s!"
namespace {ns}

theorem syms_distinct : KoreAML.Distinct.codesDistinct {KoreAML.Distinct.passesFor nSyms} (defn.emit.symbolDecls.map (·.name) ++ defn.emit.aliasNames) = true := by decide +kernel

end {ns}
")
  -- where the definition is not `plain`, `Obligations.of_nil` does not apply: `OpenDecided` and
  -- `OpenLaws` are owed, and the statements take the obligations
  let noObl := plain && c.orderObligations.isEmpty && (d.cert.obligations c).isEmpty && c.totalObligations.isEmpty &&
    c.agreeObligations.isEmpty && c.matchObligations.isEmpty && c.lazyObligations.isEmpty
  let oblNil := if noObl then "

/-- No obligation is named: `KCore.Obligations` holds of the definition. -/
theorem obligations_nil : Obligations defn :=
  Obligations.of_nil (by rw [obligations.1, obligations.2.1]; rfl) obligations.2.2 agree_obligations
    match_obligations lazy_obligations" else ""
  let faithParts := ["namesNumbered", "genWf", "collSortsOK", "collsOK", "patHeadsOK", "namesApartFast",
    "LitsApart", "sortsNumbered", "collsNotCtors", "itesApart", "kindsApart", "ctorsOnce", "fnsApart"]
  -- the conjuncts that read the names at every symbol, decided on the names' codes (each name
  -- encoded once) rather than on the names' strings
  let faithProof := fun (n : String) => match n with
    | "namesNumbered" => "namesNumbered_of_codesCD (by decide +kernel)"
    | "itesApart" => "itesApart_of_codesCD (by decide +kernel)"
    | _ => "by decide +kernel"
  o ← o.write s!"{ns}.{pre}.Faith" (s!"import KcoreSpec.Tie\nimport KcoreSpec.CoreDecide\nimport {ns}.Core\n" ++ hdr "`defn.sem.faithOK`, conjunct by conjunct by the kernel: `namesNumbered` and `itesApart` on the names' codes (`namesNumberedC`, `itesApartC`), the names' apartness by sorted codes (`namesApartFast`)." ++ s!"
namespace {ns}
open KCore KCore.Faithful KCore.Faithful.Model
" ++ String.join (faithParts.map fun n => s!"
theorem faith_{n} : {n} defn.sem = true := {faithProof n}
") ++ s!"
theorem faith_ok : defn.sem.faithOK = true :=
  Semantics.faithOK_of_parts {" ".intercalate (faithParts.map (s!"faith_{·}"))}

end {ns}
")
  o ← o.write s!"{ns}.{pre}.Wf" (s!"import KcoreSpec.Tie\nimport {ns}.Facts.Ok\nimport {ns}.Facts.Lazy\nimport {ns}.{pre}.Faith\n" ++ (if exec then s!"import {ns}.Facts.Fixed\n" else "") ++ s!"import {ns}.{pre}.SortNames\nimport {ns}.{pre}.SymNames\n" ++ hdr "`wf defn`, conjunct by conjunct: the names' distinctness by codes, `ok` from the facts, the rest by the kernel." ++ s!"
namespace {ns}
open KCore

theorem names_rest : (defn.sem.hooksApart && defn.sem.predsApart && defn.sem.idsOK) = true := by decide +kernel
theorem cert_ok : defn.cert.ok defn.sem = true := by decide +kernel
theorem pres_ok : defn.pres.ok defn.sem = true := by decide +kernel
theorem params_ok : defn.paramsOK = true := by decide +kernel
theorem overloads_ok : defn.sem.overloadsOK = true := by decide +kernel

/-- The named obligations `wf` does not decide (`KCore.Obligations`): the functions calling a later
one, the self-calling functions with no decreasing argument, and the `[total]` functions `totalOK`
does not confirm. -/
theorem obligations : defn.sem.orderObligations = {c.orderObligations} ∧ defn.cert.obligations defn.sem = {d.cert.obligations c} ∧
    defn.sem.totalObligations = {c.totalObligations} := by decide +kernel

/-- The functions whose equations `fnExclusiveOK` does not show to agree: that each two of one
priority are coherent, in both orders (`ClausesAgree`, `Coherent`), is a named obligation
(`KCore.Obligations`). -/
theorem agree_obligations : defn.sem.agreeObligations = {c.agreeObligations} := {if exec then "agreeObligations_of_T T_eq (by decide +kernel)" else "by decide +kernel"}

/-- The clauses whose patterns `clauseFixed` does not show to fix their variables, as (function,
index of the clause): that each is match independent (`MatchIndependent`: coherent with itself, and
with a result at each match where it decides if it has existential variables) is a named obligation
(`KCore.Obligations`). The lazy obligations are `lazy_obligations` (`{ns}.Facts.Lazy`). -/
theorem match_obligations : defn.sem.matchObligations = {c.matchObligations} := {if exec then "matchObligations_nil_of_fixed clausesFixed (by decide +kernel)" else "by decide +kernel"}{oblNil}

theorem wf_defn : wf defn = true := {if exec then "wf_of_parts" else "wf_of_parts_all"} sorts_distinct syms_distinct names_rest {if exec then "ok" else "okAll"} cert_ok pres_ok params_ok faith_ok overloads_ok

end {ns}
")
  -- with an open generator the `…_withHooks` forms do not apply (they ask that no parameter be
  -- raw): the base statements at the definition under H, `RightHeld` there from `rightValued`
  let raw := c.params.any (·.raw)
  let rhW := "(Semantics.rightHeld_withHooks_of_valued (by decide +kernel) H)"
  let wfW := "((Definition.wf_withHooks defn H).trans wf_defn)"
  let soundW := if raw then s!"KCore.sound \{ defn with sem := defn.sem.withHooks H } {wfW} hob {rhW}"
    else "KCore.sound_withHooks defn wf_defn H hob"
  let completeW := if raw then s!"KCore.complete \{ defn with sem := defn.sem.withHooks H } ref {wfW} hob {rhW}"
    else "KCore.complete_withHooks defn ref wf_defn H hob"
  let soundStmt := if noObl then s!"
/-- **Soundness** (`KCore.Sound`): the theory of the definition's semantics with the step's closure
has a model, and at every step x has, in every model, a successor among the instances of the
application, y being one of them. No obligation is named. -/
theorem sound : Sound defn := KCore.sound defn wf_defn obligations_nil

/-- Soundness for every interpretation of the parameters. -/
theorem sound_withHooks (H : HookParams) : Sound \{ defn with sem := defn.sem.withHooks H } :=
  KCore.sound_withHooks defn wf_defn H (Obligations.withHooks_of_nil
    (by rw [obligations.1, obligations.2.1]; rfl) obligations.2.2 agree_obligations match_obligations
    lazy_obligations H)

/-- **Completeness** (`KCore.Complete`): for an outcome function `ref` that lists the outcomes at
each configuration (`KCore.OutIs`), with the step's closure every successor of a configuration is in
an outcome `ref` lists. No obligation is
named. -/
theorem complete (ref : OutFn) : Complete defn ref := KCore.complete defn ref wf_defn obligations_nil

/-- Completeness for every interpretation of the parameters. -/
theorem complete_withHooks (ref : OutFn) (H : HookParams) :
    Complete \{ defn with sem := defn.sem.withHooks H } ref :=
  KCore.complete_withHooks defn ref wf_defn H (Obligations.withHooks_of_nil
    (by rw [obligations.1, obligations.2.1]; rfl) obligations.2.2 agree_obligations match_obligations
    lazy_obligations H)" else s!"
/-- **Soundness** (`KCore.Sound`): the theory of the definition's semantics with the step's closure
has a model, and at every step x has, in every model, a successor among the instances of the
application, y being one of them, under the named obligations
(`KCore.Obligations`, `{ns}.{pre}.Wf`). -/
theorem sound (hob : Obligations defn) : Sound defn := KCore.sound defn wf_defn hob

/-- Soundness for every interpretation of the parameters, under the named obligations stated for it. -/
theorem sound_withHooks (H : HookParams) (hob : Obligations \{ defn with sem := defn.sem.withHooks H }) :
    Sound \{ defn with sem := defn.sem.withHooks H } :=
  {soundW}

/-- **Completeness** (`KCore.Complete`): for an outcome function `ref` that lists the outcomes at
each configuration (`KCore.OutIs`), with the step's closure every successor of a configuration is in
an outcome `ref` lists, under the named
obligations (`KCore.Obligations`, `{ns}.{pre}.Wf`). -/
theorem complete (ref : OutFn) (hob : Obligations defn) : Complete defn ref :=
  KCore.complete defn ref wf_defn hob

/-- Completeness for every interpretation of the parameters, under the named obligations stated for
it. -/
theorem complete_withHooks (ref : OutFn) (H : HookParams)
    (hob : Obligations \{ defn with sem := defn.sem.withHooks H }) :
    Complete \{ defn with sem := defn.sem.withHooks H } ref :=
  {completeW}"
  let hypStmt := s!"

/-- The decidable conditions soundness and completeness assume of the definition's semantics
(`KCore.Semantics.coreOK`), from `wf defn` (`KCore.Definition.coreOK_of_wf`). -/
theorem coreOK_defn : defn.sem.coreOK = true := KCore.Definition.coreOK_of_wf wf_defn

/-- **Soundness of the semantics** (`KCore.SoundC`) for functions that meet the hypothesis
`KCore.FnHyp` (each has a result at every argument list of its sorts, each `[total]` one a value,
equations of one priority coherent, matches of a clause agreeing): from `coreOK_defn`, with no
named obligation read. -/
theorem sound_hyp (hf : FnHyp defn.sem) : SoundC defn.sem := KCore.sound_hyp defn.sem coreOK_defn hf

/-- **Completeness of the semantics** (`KCore.CompleteC`), for an outcome function `ref` that lists
the outcomes at each configuration (`KCore.OutIs`), for functions that meet `KCore.FnHyp`: from `coreOK_defn`, with no named
obligation read. -/
theorem complete_hyp (ref : OutFn) (hf : FnHyp defn.sem) : CompleteC defn.sem ref :=
  KCore.complete_hyp defn.sem ref coreOK_defn hf"
  o ← o.write s!"{ns}.Sound" (s!"import KcoreSpec.Sound\nimport {ns}.{pre}.Wf\n" ++ hdr "Soundness and completeness of the definition (`KCore.Sound`, `KCore.Complete`), from `wf defn` and the named obligations; `coreOK` of its semantics from `wf defn`, and soundness and completeness of the semantics (`KCore.SoundC`, `KCore.CompleteC`) from `coreOK` and the hypothesis on its functions (`KCore.FnHyp`)." ++ s!"
namespace {ns}
open KCore
{soundStmt}{hypStmt}

end {ns}
")
  return o

/-- The package's `lakefile.toml`, requiring kcore-spec (the current directory). -/
def writeLakefile (out : System.FilePath) (ns : String) : IO Unit := do
  IO.FS.writeFile (out / "lakefile.toml") s!"# Generated by `kcore gen`; not edited by hand. Built by kcore-spec/gen/build.sh.
name = \"{ns}\"

[[require]]
name = \"kcoreSpec\"
path = \"{relPath (← IO.FS.realPath out) (← IO.currentDir)}\"

[[lean_lib]]
name = \"{ns}\"
moreLeanArgs = [\"-j1\"]
"

/-- The conjuncts of `faithCoreOK` as `genCore` decides them. The three that read names
(`nameParts`) are decided on the names' codes (NameCodes.lean). -/
def faithCoreParts : List String := ["namesNumbered", "genWf", "collSortsOK", "collsOK", "patHeadsOK",
  "namesApartK", "LitsApart", "sortsNumbered", "itesApart", "kindsApart", "ctorsOnce", "fnsApart"]

/-- The conjuncts of `faithCoreOK` that read names, each with the lemma that gives it from its
decision on codes and that decision's arguments. -/
def nameParts : List (String × String × String) :=
  [("namesNumbered", "Model.namesNumbered_of_codes sym_codes inst_idx", "Model.namesNumberedC defn.sem instIdxs"),
   ("namesApartK", "Model.namesApartK_of_codes sym_codes sort_codes", "Model.namesApartC defn.sem symCodes sortCodes"),
   ("itesApart", "Model.itesApart_of_codes sym_codes sort_codes inst_idx", "Model.itesApartC defn.sem instIdxs sortCodes")]

/-- A list of numbers as Lean source, a few to a line. -/
def natListSrc (l : List Nat) : String :=
  if l.isEmpty then "[]" else
  let rows := (List.range ((l.length + 3) / 4)).map fun i => ", ".intercalate ((l.drop (4 * i)).take 4 |>.map toString)
  s!"[\n  {",\n  ".intercalate rows}]"

open Faithful Faithful.Model in
/-- `coreOK`'s conjuncts on the data, each with its answer, the sort checks read from the tables. -/
def coreParts (c : Semantics) (T : Tables) : List (String × Bool) :=
  [("subsortsOK", c.subsortsOKT T), ("clauses sorted", c.fnRowsSortedT T 0 c.fns.length),
   ("rules sorted", c.ruleRowsSortedT T 0 c.rules.length),
   ("namesNumbered", namesNumbered c), ("genWf", Faithful.genWf c), ("collSortsOK", collSortsOK c),
   ("collsOK", collsOK c), ("patHeadsOK", patHeadsOK c), ("namesApartK", namesApartFast c),
   ("LitsApart", LitsApart c), ("sortsNumbered", sortsNumbered c), ("itesApart", itesApart c),
   ("kindsApart", kindsApart c), ("ctorsOnce", ctorsOnce c), ("fnsApart", fnsApart c),
   ("hooksApart", c.hooksApart), ("predsApart", c.predsApart), ("idsOK", c.idsOK),
   ("overloadsOK", c.overloadsOK), ("rulesPlain", c.rulesPlain), ("clausesPlain", c.clausesPlain),
   ("paramsPlain", c.paramsPlain)]

/-- A rank of the functions for `KCore.Semantics.rankObligations`: the strongly connected sets of
the call graph, callees first, each at consecutive positions (Tarjan's depth-first search; without
cycles, the depth-first postorder). Data the kernel checks: a function whose callees it does not
rank below it is named, unless the interval of its position is a cycle whose calls decrease in a
shared weight. -/
partial def callOrderOf (c : Semantics) : List Sym := Id.run do
  let labels := c.fns.map (·.label)
  let calls : Std.HashMap Nat (List Sym) := c.fns.foldl (fun m f =>
    m.insert f.label (f.callees.eraseDups.filter fun g => labels.contains g && g != f.label)) {}
  -- state: depth-first index, lowest index reached, the search stack, its members, the output
  let rec go (v : Sym) (st : Std.HashMap Nat Nat × Std.HashMap Nat Nat × List Sym × Std.HashSet Nat × Array Sym) :
      Std.HashMap Nat Nat × Std.HashMap Nat Nat × List Sym × Std.HashSet Nat × Array Sym :=
    let (idx, low, stk, on, out) := st
    let i := idx.size
    let st := (idx.insert v i, low.insert v i, v :: stk, on.insert v, out)
    let st := (calls.getD v []).foldl (fun st w =>
      let (idx, low, stk, on, out) := st
      match idx.get? w with
      | none =>
        let (idx, low, stk, on, out) := go w (idx, low, stk, on, out)
        (idx, low.insert v (min (low.getD v i) (low.getD w i)), stk, on, out)
      | some iw =>
        if on.contains w then (idx, low.insert v (min (low.getD v i) iw), stk, on, out)
        else (idx, low, stk, on, out)) st
    let (idx, low, stk, on, out) := st
    if low.getD v i == i then
      -- v is the root of its set: the stack down to v
      let rec pop (stk : List Sym) (on : Std.HashSet Nat) (out : Array Sym) :
          List Sym × Std.HashSet Nat × Array Sym :=
        match stk with
        | [] => ([], on, out)
        | w :: rest => if w == v then (rest, on.erase w, out.push w) else pop rest (on.erase w) (out.push w)
      let (stk, on, out) := pop stk on out
      (idx, low, stk, on, out)
    else (idx, low, stk, on, out)
  let mut st : Std.HashMap Nat Nat × Std.HashMap Nat Nat × List Sym × Std.HashSet Nat × Array Sym :=
    ({}, {}, [], {}, #[])
  for f in labels do
    if !st.1.contains f then
      st := go f st
  return st.2.2.2.2.toList

/-- The statements at a step and at a configuration a package gives, for every interpretation H
(binders `bind`, starting with `(H : HookParams)`, and `hf` a term of `FnHyp (defn.sem.withHooks H)`
under them): `Consistent` from the named facts (`KCore.consistent_of`), and `sound_at`,
`complete_at` and, where `run` (the core is `execReady`), `CExec.run_exact`, each concluding
`Consistent … ∧ …`: an entailment from a theory with no model holds vacuously, so none is stated
bare. Where facts are `named`, they are hypotheses in `bind` and each name ends in `_of`.
The definition is `plain` (`KCore.Semantics.plain`, decided by the kernel in `plain_defn`):
`sound_at` and `complete_at` are over `Step` and `Γ` (`KCore.sound_at_plain`,
`KCore.complete_at_plain`). A definition that is not `plain` has `headlineAtOpen`. -/
def headlineAt (bind hf given : String) (named run plain : Bool) : String :=
  -- with facts named, they are hypotheses (in `bind`) and the names end in `_of`
  let sfx := if named then "_of" else ""
  let S := "(defn.sem.withHooks H)"
  let hc := "(coreOK_withHooks_defn H)"
  let cons := s!"consistent_of_fnHyp _ {hc} ({hf})"
  let runPart := if !run then "" else s!"

/-- The core is ready for the checked executor (`KCore.CExec.execReady`). -/
theorem exec_ready : CExec.execReady defn.sem = true :=
  CExec.execReady_of_rest coreOK_defn srReady (by decide +kernel)

/-- **A run at a fuel where nothing ran out is exact** (`KCore.CExec.run_exact`) under H, with the
theory's model, {given}: with the step's closure every successor of x is one `successorsN` lists,
and each one it lists is a successor of x in every model of `Γ`. -/
theorem run_exact{sfx}{bind} \{n : Nat} \{x : Config {S}}
    (hfu : CExec.outOfFuel {S} n x.val = false) :
    Consistent {S} ∧
      ((Γ {S} ∪ Γstep {S}) ⊧
        (den {S} x.val ⇒ KoreAML.allNext (KoreAML.disjList ((CExec.successorsN {S} n x.val).map (den {S}))))) ∧
      ∀ y ∈ CExec.successorsN {S} n x.val, (Γ {S} ⊧ (den {S} x.val ⇒ KoreAML.sNext (den {S} y))) :=
  ⟨{cons}, CExec.run_exact {hc} ((CExec.execReady_withHooks _ H).trans exec_ready)
    (fnModel_of_fnHyp {hc} ({hf})).1 hfu⟩"
  let plainPart := if !plain then "" else s!"
/-- The definition uses only the plain shapes (`KCore.Semantics.plain`), decided. -/
theorem plain_defn : defn.sem.plain = true := by decide +kernel

/-- `plain` under every interpretation H (`plain` does not read it). -/
theorem plain_withHooks_defn (H : HookParams) : {S}.plain = true :=
  (Semantics.plain_withHooks defn.sem H).trans plain_defn
"
  let atPart := s!"/-- **Soundness at a step** (`KCore.sound_at_plain`) under H, with the theory's model, {given}:
every step of `Step` is a theorem of `Γ`. The entailment reads `coreOK` and `plain` alone;
`Consistent` beside it reads the facts. -/
theorem sound_at{sfx}{bind} (x y : Config {S}) (hs : Step {S} x y) :
    Consistent {S} ∧ (Γ {S} ⊧ (den {S} x.val ⇒ KoreAML.sNext (den {S} y.val))) :=
  ⟨{cons}, KCore.sound_at_plain _ {hc} (plain_withHooks_defn H) x y hs⟩

/-- **Completeness at a configuration** (`KCore.complete_at_plain`) under H, with the theory's model,
{given}: where the evaluations the step at x reads have results (`StepDecided`), with the step's
closure every successor of x is one of `ys`, any list holding `Step`'s successors of x. The
entailment reads `coreOK`, `plain` and `StepDecided` alone; `Consistent` beside it reads the facts. -/
theorem complete_at{sfx}{bind} (x : Config {S}) (hd : StepDecided {S} x.val)
    (ys : List GroundTerm) (hys : ∀ y : Config {S}, Step {S} x y → y.val ∈ ys) :
    Consistent {S} ∧
      ((Γ {S} ∪ Γstep {S}) ⊧ (den {S} x.val ⇒ KoreAML.allNext (KoreAML.disjList (ys.map (den {S}))))) :=
  ⟨{cons}, KCore.complete_at_plain _ {hc} (plain_withHooks_defn H) x hd ys hys⟩"
  s!"
/-- `coreOK` under every interpretation H (`coreOK` does not read it). -/
theorem coreOK_withHooks_defn (H : HookParams) : {S}.coreOK = true :=
  (Semantics.coreOK_withHooks defn.sem H).trans coreOK_defn
{plainPart}
/-- **The theory without the `[total]` axioms has a model** (`KCore.Consistent`, by
`KCore.consistent_of`) under every interpretation H, {given} (the facts still owed are
`namedFacts`). `Γ` holds no axiom `∃y. f(x̄) = y` of a function, so no `[total]` declaration is
read here (the theory with them: `KCore.Faithful.has_model_total`). -/
theorem consistent{sfx}{bind} : Consistent {S} :=
  {cons}

{atPart}{runPart}"

/-- The statements at a step and at a configuration of a definition that is not `plain`, for every
interpretation H (binders `bind`, starting with `(H : HookParams)`, and `hob` a term of the named
facts `FnFacts (defn.sem.withHooks H) …` under them): `Consistent` from the named facts
(`KCore.consistent_of_fnFacts`, no owed condition read), `KCore.sound_at` and
`KCore.complete_at` themselves, over a rule's instances (`famEx`) and `Γc`, and, where `run` (the
core is `execReady`), `CExec.run_exact`, each concluding `Consistent … ∧ …`. Each statement takes
the hypotheses of the pinned theorem it instantiates and no more: where rules are owed (`owesR`),
`sound_at` takes the pinned `hw` (the owed rules of smaller priority number whose left side matches
x decided); where clauses are owed (`owesC`), `sound_at` and `complete_at` take the pinned `hc`;
otherwise those sides are proved in the package (`rulesDecided_defn`, `clausesDecided_defn`). A name
ends in `_of` exactly where its statement has a binder for a fact (`named`: the facts `hob`, or,
where functions are held-named, `held`, the facts `hheld` owed of them, which then stand in place
of `rightHeld_withHooks_defn`). Where `hf` is given (a term of `FnHyp (defn.sem.withHooks H)` under
`bind`), `Consistent` and the functions' model are read from it (`KCore.consistent_of_fnHyp`,
`KCore.fnModel_of_fnHyp`) in place of the named facts. -/
def headlineAtOpen (bind hob given : String) (named run owesR owesC : Bool) (held : Bool := false)
    (hf : String := "") : String :=
  let sfxC := if named then "_of" else ""
  let sfxS := if named || owesR || owesC then "_of" else ""
  let sfxP := if named || owesC then "_of" else ""
  let S := "(defn.sem.withHooks H)"
  let hc := "(coreOK_withHooks_defn H)"
  -- with functions held-named (`held`), the facts owed of them are the binder `hheld` (in `bind`)
  let cons := if !hf.isEmpty then s!"consistent_of_fnHyp _ {hc} {hf}"
    else if held then s!"consistent_of_fnFacts_withHooksN coreOK_defn H hheld {hob}"
    else s!"consistent_of_fnFacts {hc} (rightHeld_withHooks_defn H) {hob}"
  let consName := if !hf.isEmpty then "consistent_of_fnHyp"
    else if held then "consistent_of_fnFacts_withHooksN" else "consistent_of_fnFacts"
  let fnModel := if !hf.isEmpty then s!"fnModel_of_fnHyp {hc} {hf}"
    else if held then s!"fnModel_of_fnFacts_withHooksN coreOK_defn H hheld {hob}"
    else s!"fnModel_of_fnFacts {hc} (rightHeld_withHooks_defn H) {hob}"
  let owedD := if hf.isEmpty then " (the facts still
owed are `namedFacts`)" else ""
  let hwB := if owesR then s!"
    (hw : ∀ r' ∈ {S}.rules, r'.prio < r.prio → r'.needsWitness {S} = true →
      (∃ σ', PatVal {S} σ' r'.lhs x.val) → r'.CondDecided {S})" else ""
  let hcB := if owesC then s!"
    (hc : ∀ fn ∈ {S}.fns, ∀ cl ∈ fn.clauses, cl.needsWitness {S} = true → cl.CondDecided {S})" else ""
  let HW := if owesR then "hw" else "(fun r' hr' _ hn _ => rulesDecided_defn H r' hr' hn)"
  let HC := if owesC then "hc" else "(clausesDecided_defn H)"
  let swDoc := if owesR then " A rule of smaller priority number whose conditions are owed and whose
left side matches x is decided (`hw`); a step no such rule competes in needs none." else ""
  let scDoc := if owesC then " The owed clauses' conditions are decided (`hc`)." else ""
  let runPart := if !run then "" else s!"

/-- The core is ready for the checked executor (`KCore.CExec.execReady`). -/
theorem exec_ready : CExec.execReady defn.sem = true :=
  CExec.execReady_of_rest coreOK_defn srReady (by decide +kernel)

/-- **A run at a fuel where nothing ran out is exact** (`KCore.CExec.run_exact`) under H, with the
theory's model, {given}: with the step's closure every successor of x is one `successorsN` lists,
and each one it lists is a successor of x in every model of `Γ`. -/
theorem run_exact{sfxC}{bind} \{n : Nat} \{x : Config {S}}
    (hfu : CExec.outOfFuel {S} n x.val = false) :
    Consistent {S} ∧
      ((Γ {S} ∪ Γstep {S}) ⊧
        (den {S} x.val ⇒ KoreAML.allNext (KoreAML.disjList ((CExec.successorsN {S} n x.val).map (den {S}))))) ∧
      ∀ y ∈ CExec.successorsN {S} n x.val, (Γ {S} ⊧ (den {S} x.val ⇒ KoreAML.sNext (den {S} y))) :=
  ⟨{cons}, CExec.run_exact {hc} ((CExec.execReady_withHooks _ H).trans exec_ready)
    ({fnModel}).1 hfu⟩"
  s!"
/-- `coreOK` under every interpretation H (`coreOK` does not read it). -/
theorem coreOK_withHooks_defn (H : HookParams) : {S}.coreOK = true :=
  (Semantics.coreOK_withHooks defn.sem H).trans coreOK_defn

/-- **The theory without the `[total]` axioms has a model** (`KCore.Consistent`, by
`KCore.{consName}`) under every interpretation H, {given}{owedD}; no owed condition is read. `Γ` holds no axiom `∃y. f(x̄) = y` of a
function, so no `[total]` declaration is read here (the theory with them:
`KCore.Faithful.has_model_total`). -/
theorem consistent{sfxC}{bind} : Consistent {S} :=
  {cons}

/-- **Soundness at a step by a rule** (`KCore.sound_at`) under H, with the theory's model, {given}:
at a step of `Step` by the rule r under σ, x has in every model of `Γc` a successor among the
instances of r's right side (`KCore.Faithful.famEx`), and y is one of them.{swDoc}{scDoc} -/
theorem sound_at{sfxS}{bind} (x y : Config {S}) (r : Rule) (σ : Subst) (hs : KCore.StepBy {S} r σ x y){hwB}{hcB} :
    Consistent {S} ∧ (KCore.Faithful.Γc {S} ⊧ (den {S} x.val ⇒ KoreAML.sNext (KCore.Faithful.famEx {S} r σ))) ∧
      (KCore.Faithful.Γc {S} ⊧ (den {S} y.val ⇒ KCore.Faithful.famEx {S} r σ)) :=
  ⟨{cons}, KCore.sound_at _ {hc} x y r σ hs {HW} {HC}⟩

/-- **Completeness at a configuration** (`KCore.complete_at`) under H, with the theory's model,
{given}: where the evaluations the step at x reads have results (`StepDecided`), with the step's
closure every successor of x is one of the outcomes `os`, any list holding each successor by a rule
with no open variable and an instance family of each rule with one that is not blocked at x. It
reads no rule's owed condition: an open rule's instances are among the outcomes (`hfam`).{scDoc} -/
theorem complete_at{sfxP}{bind} (x : Config {S}) (hd : StepDecided {S} x.val) (os : List KCore.Outcome)
    (hval : ∀ (y : Config {S}) (r : Rule) (σ : Subst), r.opens = [] → KCore.StepBy {S} r σ x y →
      KCore.Outcome.val y.val ∈ os)
    (hfam : ∀ r ∈ {S}.rules, r.opens ≠ [] → ∀ σ, KCore.Unblocked {S} r σ x.val →
      ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ KCore.Outcome.fam r σ' ∈ os){hcB} :
    Consistent {S} ∧
      ((KCore.Faithful.Γc {S} ∪ Γstep {S}) ⊧
        (den {S} x.val ⇒ KoreAML.allNext (KoreAML.disjList (os.map (KCore.Outcome.pat {S}))))) :=
  ⟨{cons}, KCore.complete_at _ {hc} x hd os hval hfam {HC}⟩{runPart}"

/-- The facts of `FnHyp` the deciders leave open (`--core`): the rank (`NS.FnHyp.Order`), the four
lists each decided in its own module, and `fnHyp_defn`, `sound_defn`, `complete_defn` under
`KCore.FnObligations` (`NS.FnHyp`), each for every interpretation of the parameters; with them the
statements at a step and at a configuration (`headlineAt`). `facts`: the package has `NS.Facts`
(`srReady`), which `run_exact_defn` reads. `plain`: the definition is `plain` (decided natively by
the caller); otherwise `OpenDecided` and `OpenLaws`, the two conjuncts of `FnObligations` that only
`plain` gives (`FnObligations.of_nil`), are not given by `plain`. Then the named facts are
`KCore.FnFacts` (`FnObligations` less `OpenDecided`; `OpenLaws` is decided where no parameter is
open), and `NS.FnHyp.Owed` decides the positions of the rules and clauses whose conditions are
owed (`owed_rules`, `owed_clauses`): with none owed, `OpenDecided` is proved in the package
(`openDecided_defn`); otherwise it is `Owed`, a hypothesis of `fnHyp_defn`, `sound_defn` and
`complete_defn` only, and the statements at a step take what the pinned ones take
(`headlineAtOpen`). Where a function is held-named (`KCore.Semantics.heldObligations` is not
empty: an equation holds a variable outside its patterns and conditions, of a sort without an
exhibited value, so `rightValued` is false), `NS.FnHyp.Held` states the list (`held_named`) and
`fnHyp_defn`, `sound_defn`, `complete_defn` and the statements at a step take the facts owed of
those functions (`Held`: `KCore.HeldOwed` of each) through the forms `…N` of FnObligations.lean;
with none held-named the emitted text is as before. Where a parameter is an open generator
(`raw`), every statement takes, after H, `OpenLaws` and `OpenTotal` of `defn.sem.withHooks H`
(`hop`, `_hot`), never discharged by fixing H; `Obl H` is the named facts given the laws;
`HooksTotal` reads the sorts under H; `fnHyp_defn`, `sound_defn` and `complete_defn` are the base
lemmas at `defn.sem.withHooks H` (the `…_withHooks` forms ask that no parameter be raw); and the
module ends with `lawHooks`: the laws, the values and the library's sentences there
(`openLaws_lawHooks_defn`, `openTotal_lawHooks_defn`, `libAdmitted_lawHooks_defn`,
`lawHooks_lib_defn`) and each statement's instance (`…_lawHooks`). Where a clause's predicate is not
`\top` (`KCore.Semantics.clausesPreTop` false, decided by `clausesPreTop_false`), the named facts do
not give `FnHyp` (every lemma from them to `FnHyp` or `Consistent` reads `clausesPreTop`): the four
lists are still decided, but `Obl`, `fnHyp_defn` and the `lawHooks` section are not written, and
soundness, completeness, consistency and the statements at a step take `FnHyp` itself (`hf`).
`force` (`--as-not-plain`): every binder is written, as if facts and conditions were owed. -/
def genFnHyp (o : Out) (ns : String) (d : Definition) (facts plain : Bool) (force : Bool := false) : IO Out := do
  let mut o := o
  let c := d.sem
  let ord := callOrderOf c
  -- a definition with parameters no registry hook implements is stated for the interpretations
  -- total on the parameters its text declares total; without any, for its one meaning
  let hasParams := c.params.any (·.impl.isNone)
  let tp := if hasParams then d.totalParams else []
  let tpSrc := if hasParams then "defn.totalParams" else "[]"
  let termL := c.rankObligations ord ++ c.decObligationsL
  let totL := c.totalObligationsRP ord tp
  let agrL := c.agreeObligationsI
  let matL := c.matchObligationsL
  let nm := fun (f : Sym) => decodeK (c.symName f)
  let lst := fun (l : List Sym) => if l.isEmpty then "[]" else
    "[" ++ ",
    ".intercalate (l.map fun f => s!"{f} /- {nm f} -/") ++ "]"
  let lstP := fun (l : List (Sym × Nat)) => if l.isEmpty then "([] : List (Nat × Nat))" else
    "[" ++ ",
    ".intercalate (l.map fun (f, i) => s!"({f}, {i}) /- {nm f}, clause {i} -/") ++ "]"
  -- each function's source location, `file:line` (the file's last path component)
  let base := fun (s : String) => ((s.splitOn "/").getLast?.getD s).replace ")" ""
  let locOf := fun (f : Sym) => match (withPres c.fns d.pres.fns).find? (·.1.label == f) with
    | some (_, fp) => if fp.loc.l1 == 0 then "generated, no source location" else
        s!"{base ((fp.src.getD d.pres.source).replace "Source(" "")}:{fp.loc.l1}"
    | none => "generated, no source location"
  o ← o.write s!"{ns}.FnHyp.Order" (s!"import {ns}.Core
import KcoreSpec.FnObligations
" ++ hdr "A rank of the functions (callees first), computed by `kcore gen` from the call graph and checked where it is read (`KCore.Semantics.rankObligations`)." ++ s!"
namespace {ns}

def callOrder : List Nat := {natListSrc ord}

end {ns}
")
  let thm := fun (o : Out) (mod imp what stmt : String) =>
    o.write s!"{ns}.FnHyp.{mod}" (s!"import {imp}
import KcoreSpec.FnObligations
" ++ hdr what ++ s!"
namespace {ns}
open KCore KCore.Det

{stmt}

end {ns}
")
  o ← thm o "Params" s!"{ns}.Core" "The parameter symbols the text declares total (`KCore.Definition.totalParams`): the statements are about the interpretations total on those that no registry hook implements (`KCore.ParamsTotal`)."
    s!"theorem totalParams_eq : defn.totalParams =
    {lst d.totalParams} := by decide +kernel"
  o ← thm o "Term" s!"{ns}.FnHyp.Order" "The functions whose termination neither the rank nor their self calls' decrease in weight shows (`KCore.FnObligations`, first conjunct)."
    s!"theorem term_named : defn.sem.rankObligations callOrder ++ defn.sem.decObligationsL =
    {lst termL} := by decide +kernel"
  o ← thm o "Total" s!"{ns}.FnHyp.Order\nimport {ns}.FnHyp.Params" "The `[total]` functions `totalOKP` does not confirm, calls of the parameters the text declares total admitted where the definition has parameters (`KCore.FnObligations`, second conjunct)."
    s!"theorem total_named : defn.sem.totalObligationsRP callOrder {tpSrc} =
    {lst totL} := by decide +kernel"
  o ← thm o "Agree" s!"{ns}.Facts.Tables" "The functions whose equations of one priority `fnExclusiveI` does not show to agree (`KCore.FnObligations`, third conjunct), read from the tables."
    s!"theorem agree_named : defn.sem.agreeObligationsI =
    {lst agrL} :=
  agreeObligationsI_of_T T_eq (by decide +kernel)"
  o ← thm o "Match" s!"{ns}.Core" "The clauses `clauseFixedL` does not show to fix their variables (`KCore.FnObligations`, fourth conjunct)."
    s!"theorem match_named : defn.sem.matchObligationsL =
    {lstP matL} := by decide +kernel"
  -- the held-named functions (`Semantics.heldObligations`): where there is one, `rightValued` is
  -- false, the package states the list and its statements take the facts owed of them (`Held`)
  let heldL := c.heldObligations
  let held := !heldL.isEmpty
  if held then
    o ← thm o "Held" s!"{ns}.Core" "The functions with an equation holding a variable outside its patterns and conditions, of a sort without an exhibited value (`KCore.Semantics.heldObligations`): of each, `KCore.HeldOwed` is owed."
      s!"theorem held_named : defn.sem.heldObligations =
    {lst heldL} := by decide +kernel"
  -- not plain: the rules and clauses whose conditions are owed, and whether a parameter is open
  let owedR := c.owedRules
  let owedC := c.owedClauses
  let raw := c.params.any (·.raw)
  let owesR := !plain && (force || !owedR.isEmpty)
  let owesC := !plain && (force || !owedC.isEmpty)
  let owes := owesR || owesC
  let none := if plain then termL.isEmpty && totL.isEmpty && agrL.isEmpty && matL.isEmpty
    else !force && termL.isEmpty && totL.isEmpty && agrL.isEmpty && matL.isEmpty
  -- each owed rule's label and its open condition variables of an unconfined sort; each owed
  -- clause's function
  let ruleVs := fun (i : Nat) =>
    let names := ((d.pres.rules[i]?).map (·.names)).getD []
    let sorts := (c.rules[i]?.map (·.vars)).getD []
    let js := ((Parse.owedCondDecided c).find? (·.1 == i)).map (·.2) |>.getD []
    ", ".intercalate (js.map fun j => s!"Var{names.getD j ""}:{c.sortName (sorts.getD j 0)}")
  let ruleLbl := fun (i : Nat) => match (d.pres.rules[i]?).bind (·.label) with
    | some l => s!" `{l}`" | _ => ""
  let fnName := fun (i : Nat) => match c.fns[i]? with | some f => nm f.label | _ => "?"
  -- the named facts with each function's source location
  let entries : List String :=
    (c.rankObligations ord).map (fun f =>
      if c.fnOvlCallers.contains f then s!"termination (it applies a function-overloaded symbol) {nm f} {locOf f}"
      else s!"termination (a call not ranked below it) {nm f} {locOf f}") ++
    c.decObligationsL.map (fun f => s!"termination (a self call not decreasing) {nm f} {locOf f}") ++
    totL.map (fun f => s!"totality {nm f} {locOf f}") ++
    agrL.map (fun f => s!"agreement {nm f} {locOf f}") ++
    matL.map (fun (f, i) => s!"match independence {nm f} clause {i} {locOf f}") ++
    heldL.map (fun f => s!"held variables or results (an equation's variable outside its patterns and conditions, of a sort without an exhibited value) {nm f} {locOf f}") ++
    (if plain then [] else
      owedR.map (fun i => s!"condition decided (closed over {ruleVs i}, unconfined): rule {i}{ruleLbl i}") ++
      owedC.map (fun (i, j) => s!"condition decided (a witness at which the `requires` has no other result, or a refutation): clause {j} of {fnName i}") ++
      (if raw then ["the open generators' laws (`KCore.OpenLaws`)",
        "the open generators' values at every argument list of their sorts (`KCore.OpenTotal`)"] else []))
  -- a clause's predicate is not `\top` (`clausesPreTop` false): every lemma that gives `FnHyp`,
  -- `Consistent` or the functions' model from the named facts reads `clausesPreTop`, so the
  -- statements take `FnHyp` itself (`hf`), and `Consistent` and the step statements read it
  let preTop := c.clausesPreTop
  let entries := if preTop then entries else entries ++
    ["`FnHyp` itself (a clause's predicate is not `\\top`, `clausesPreTop_false`: the facts above do not give it)"]
  let strs := if entries.isEmpty then "[]" else
    "[\n  " ++ ",\n  ".intercalate (entries.map fun e => (repr e).pretty) ++ "]"
  let factsDef := s!"/-- The named facts, one per line: the class, the function (its KORE name decoded) and its source
location (the declaring file and line). Data for the reader; the statements are `term_named`,
`total_named`, `agree_named`, `match_named`. -/
def namedFacts : List String := {strs}
"
  -- with no fact named, `FnHyp` and soundness and completeness hold outright (`obl_nil`)
  -- with an open generator (`raw`) every statement is for the interpretations H that satisfy the
  -- generators' laws and give each a value at every argument list of its sorts: two binders after
  -- H, never discharged by fixing H; the named facts `Obl H` are then stated given the laws
  let rawB := if raw then " (hop : OpenLaws (defn.sem.withHooks H)) (_hot : OpenTotal (defn.sem.withHooks H))" else ""
  let hobB := if none then "" else " (hob : Obl H)"
  let hobA := if raw then (if none then "(obl_nil H hop)" else "(hob hop)") else if none then "(obl_nil H)" else "hob"
  let hobB0 := if none then "" else " (hob : Obl)"
  let hobA0 := if none then "obl_nil" else "hob"
  -- the laws the text writes for its functions (`defn.laws`): every statement is about the
  -- interpretations under which they hold at values (`KCore.FnLaws`), a hypothesis beside the
  -- others, which no proof reads (`_hl`); with no law there is none
  let laws := !d.laws.isEmpty
  let lawsH := if laws then " (_hl : FnLaws (defn.sem.withHooks H) defn.laws)" else ""
  let laws0 := if laws then " (_hl : FnLaws defn.sem defn.laws)" else ""
  let lawsA := if laws then " _hl" else ""
  let lawsD := if laws then ", under the laws the text writes for its functions at values (`KCore.FnLaws`, `defn.laws`)" else ""
  let rawD := if raw then ", for an interpretation that satisfies the open generators' laws (`hop`) and gives each a value at every argument list of its sorts (`_hot`)" else ""
  let given := (if none then "no fact being named (`obl_nil`)" else "given the named facts") ++ lawsD ++ rawD
  -- not plain: the named facts are `FnFacts`; `OpenDecided` is proved (nothing owed) or `Owed`
  let oblK := if plain then "FnObligations" else "FnFacts"
  let rawArg := if plain then "" else "\n    (show defn.sem.params.all (fun k => !k.raw) = true by decide +kernel)"
  let oblDoc := if plain then "" else " `OpenDecided` is not among them: with it (`KCore.FnFacts.obligations`) they
are `KCore.FnObligations`."
  let givenD := if plain || !owes then given
    else if none then "given the owed conditions (`Owed`)" ++ lawsD ++ rawD
    else "given the named facts and the owed conditions (`Owed`)" ++ lawsD ++ rawD
  -- the held-named functions: the statements take the facts owed of them in place of `RightHeld`
  let nN := if held then "N" else ""
  let rh0 := if held then "hheld" else "(Semantics.rightHeld_of_valued (by decide +kernel))"
  let rhH := if held then "H hheld" else "(Semantics.rightHeld_of_valued (by decide +kernel)) H"
  let heldDoc := s!"/-- **The facts owed of the held-named functions** (`held_named`, {heldL.length} functions with an
equation holding a variable outside its patterns and conditions, of a sort without an exhibited
value), of each one of two (`KCore.HeldOwed`): each such variable's sort has a value, or the
function has a result at every argument list of its sorts, a value where it is `[total]`. The text
may hold this or not; where it does not, the statements that take it say nothing of the text. -/"
  let givenD := if held then givenD ++ ", and the facts owed of the held-named functions (`Held`)" else givenD
  let hobBD := hobB ++ (if owes then " (how : Owed H)" else "") ++ (if held then " (hheld : Held H)" else "") ++ lawsH
  let hobAD := if plain then hobA else s!"({hobA}.obligations {if owes then "how" else "(openDecided_defn H)"})"
  let hobBD0 := hobB0 ++ (if owes then " (how : Owed)" else "") ++ (if held then " (hheld : Held)" else "") ++ laws0
  let hobAD0 := if plain then hobA0 else s!"({hobA0}.obligations {if owes then "how" else "openDecided_defn"})"
  let S := "(defn.sem.withHooks H)"
  let sidesPart := (if held then "" else s!"
/-- `RightHeld` of the definition under every interpretation H (`KCore.Semantics.rightValued`, decided on
the data). -/
theorem rightHeld_withHooks_defn (H : HookParams) : (defn.sem.withHooks H).RightHeld :=
  Semantics.rightHeld_withHooks_of_valued (by decide +kernel) H
") ++ (if owesR then "" else s!"
/-- No rule's condition is owed (`owed_rules`): the rule side of `KCore.OpenDecided` under every
interpretation H. -/
theorem rulesDecided_defn (H : HookParams) :
    ∀ r ∈ {S}.rules, r.needsWitness {S} = true → r.CondDecided {S} :=
  openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi)
") ++ (if owesC then "" else s!"
/-- No clause's condition is owed (`owed_clauses`): the clause side of `KCore.OpenDecided` under
every interpretation H. -/
theorem clausesDecided_defn (H : HookParams) :
    ∀ fn ∈ {S}.fns, ∀ cl ∈ fn.clauses, cl.needsWitness {S} = true → cl.CondDecided {S} :=
  openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)
")
  let owedDoc := s!"/-- **The owed conditions**: the conditions of the {owedR.length} rules and {owedC.length} clauses of `owed_rules`,
`owed_clauses` are decided by the text (`KCore.Rule.CondDecided`, `KCore.Clause.CondDecided`:
witnessed at values, or refuted by the theory). The text may hold this or not; where it does not,
the statements that take it say nothing of the text. -/"
  -- a clause's predicate is not `\top`: `FnHyp` itself is the hypothesis (`hf`), and soundness and
  -- completeness are `KCore.sound_hyp` and `KCore.complete_hyp` under H
  let cw := "((Semantics.coreOK_withHooks defn.sem H).trans coreOK_defn)"
  let hypPre := s!"/-- **A clause's predicate is not `\\top`** (`KCore.Semantics.clausesPreTop`, decided). The
named facts give `FnHyp` only where every clause's predicate is `\\top`
(`KCore.fnHyp_of_fnObligations` and `KCore.consistent_of_fnFacts` read `clausesPreTop`), so here
`FnHyp` itself is the hypothesis of every statement (`hf`), as of `sound_hyp` and `complete_hyp`;
the named facts (`namedFacts`) are not read. -/
theorem clausesPreTop_false : defn.sem.clausesPreTop = false := by decide +kernel
"
  let hypH := s!"
/-- **Soundness of the semantics** (`KCore.SoundC`, by `KCore.sound_hyp`) under every interpretation
H, given `FnHyp` of the semantics under H (`hf`). -/
theorem {if hasParams then "sound_defn" else "sound_withHooks_defn"} (H : HookParams) (hf : FnHyp {S}) : SoundC {S} :=
  KCore.sound_hyp _ {cw} hf

/-- **Completeness of the semantics** (`KCore.CompleteC`, by `KCore.complete_hyp`) under every
interpretation H, given `FnHyp` of the semantics under H (`hf`). -/
theorem {if hasParams then "complete_defn" else "complete_withHooks_defn"} (ref : OutFn) (H : HookParams) (hf : FnHyp {S}) : CompleteC {S} ref :=
  KCore.complete_hyp _ ref {cw} hf"
  let hyp0 := s!"
/-- **Soundness of the semantics** (`KCore.SoundC`, by `KCore.sound_hyp`), given `FnHyp` (`hf`). -/
theorem sound_defn (hf : FnHyp defn.sem) : SoundC defn.sem := KCore.sound_hyp defn.sem coreOK_defn hf

/-- **Completeness of the semantics** (`KCore.CompleteC`, by `KCore.complete_hyp`), given `FnHyp` (`hf`). -/
theorem complete_defn (ref : OutFn) (hf : FnHyp defn.sem) : CompleteC defn.sem ref :=
  KCore.complete_hyp defn.sem ref coreOK_defn hf
"
  let body := if hasParams then
    let nilPart := if !none then "" else if raw then s!"

/-- No fact is named: under every interpretation that satisfies the open generators' laws,
`{oblK}` holds (`KCore.FnFacts.of_nil_laws`). -/
theorem obl_nil (H : HookParams) : Obl H := fun hop =>
  FnFacts.of_nil_laws
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named) hop
" else s!"

/-- No fact is named: `{oblK}` holds for every interpretation. -/
theorem obl_nil (H : HookParams) : Obl H :=
  {oblK}.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named){rawArg}
"
    let owedPart := if plain then "" else sidesPart ++ (if owes then s!"
{owedDoc}
abbrev Owed (H : HookParams) : Prop := OpenDecided {S}
" else "
/-- No condition is owed: `KCore.OpenDecided` under every interpretation H. -/
theorem openDecided_defn (H : HookParams) : OpenDecided (defn.sem.withHooks H) :=
  ⟨rulesDecided_defn H, clausesDecided_defn H⟩
")
    let heldPart := if held then s!"
{heldDoc}
abbrev Held (H : HookParams) : Prop := ∀ f ∈ defn.sem.heldObligations, HeldOwed (defn.sem.withHooks H) f
" else ""
    -- with an open generator the sorts are the interpretation's (an open generator's application
    -- is a value only where H leaves it raw), so the statements are the base lemmas at
    -- `defn.sem.withHooks H`, with `ParamsTotal` read there
    let htSem := if raw then "(defn.sem.withHooks H)" else "defn.sem"
    let htDoc := if raw then " The sorts are those under H: with an open generator a value's sort
depends on the interpretation." else ""
    let oblTy := if raw then s!"OpenLaws (defn.sem.withHooks H) → {oblK} (defn.sem.withHooks H) callOrder defn.totalParams"
      else s!"{oblK} (defn.sem.withHooks H) callOrder defn.totalParams"
    let oblRawDoc := if raw then " They are stated for an H that satisfies the open generators' laws
(`KCore.OpenLaws`, the last conjunct of `KCore.FnFacts`), which each statement takes as `hop`." else ""
    let cwH := "((Semantics.coreOK_withHooks defn.sem H).trans coreOK_defn)"
    let rhR := if held then "hheld" else "(rightHeld_withHooks_defn H)"
    let fnHypPf := if raw then s!"fnHyp_of_fnObligations{nN} {cwH} {rhR} hH {hobAD}"
      else s!"fnHyp_withHooks{nN} coreOK_defn {rhH} hH {hobAD}"
    let soundPf := if raw then s!"sound_fn{nN} (defn.sem.withHooks H) callOrder defn.totalParams {cwH} {rhR} hH {hobAD}"
      else s!"sound_fn_withHooks{nN} defn.sem callOrder defn.totalParams coreOK_defn {rhH} hH {hobAD}"
    let completePf := if raw then s!"complete_fn{nN} (defn.sem.withHooks H) callOrder defn.totalParams ref {cwH} {rhR} hH {hobAD}"
      else s!"complete_fn_withHooks{nN} defn.sem callOrder defn.totalParams ref coreOK_defn {rhH} hH {hobAD}"
    if !preTop then hypPre ++ owedPart ++ hypH else
    s!"/-- **The interpretations the statements are about**: H gives each parameter symbol the text
declares total, and no registry hook implements, a value of its result sort at every argument list
of its sorts (`KCore.ParamsTotal`; the parameters are `totalParams_eq`'s). A parameter the text does
not declare total may be undefined anywhere.{htDoc} -/
abbrev HooksTotal (H : HookParams) : Prop := ParamsTotal {htSem} defn.totalParams H

/-- **The facts the deciders leave of `FnHyp`** under the interpretation H ({termL.length} functions'
termination, {totL.length} `[total]` functions' totality, {agrL.length} functions' agreement,
{matL.length} clauses' match independence; the lists are `term_named`, `total_named`,
`agree_named`, `match_named`, the same for every H).{oblDoc}{oblRawDoc} -/
abbrev Obl (H : HookParams) : Prop := {oblTy}
{nilPart}{owedPart}{heldPart}
/-- `FnHyp` of the definition's semantics under H, {givenD}. -/
theorem fnHyp_defn (H : HookParams){rawB} (hH : HooksTotal H){hobBD} : FnHyp (defn.sem.withHooks H) :=
  {fnHypPf}

/-- **Soundness of the semantics** (`KCore.SoundC`) under every interpretation total where the text
declares the parameters total, {givenD}. -/
theorem sound_defn (H : HookParams){rawB} (hH : HooksTotal H){hobBD} : SoundC (defn.sem.withHooks H) :=
  {soundPf}

/-- **Completeness of the semantics** (`KCore.CompleteC`) under every interpretation total where
the text declares the parameters total, {givenD}. -/
theorem complete_defn (ref : OutFn) (H : HookParams){rawB} (hH : HooksTotal H){hobBD} :
    CompleteC (defn.sem.withHooks H) ref :=
  {completePf}"
  else
    let nilPart := if none then s!"
/-- No fact is named: `{oblK}` holds. -/
theorem obl_nil : Obl := {oblK}.of_nil term_named total_named agree_named match_named{if plain then "" else " (by decide +kernel)"}
" else ""
    let nilPartH := if none then s!"
/-- No fact is named: `{oblK}` holds for every interpretation. -/
theorem obl_nil_withHooks (H : HookParams) : OblH H :=
  {oblK}.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named){rawArg}
" else ""
    let hobBH := if none then "" else " (hob : OblH H)"
    let hobAH := if none then "(obl_nil_withHooks H)" else "hob"
    let hobBDH := hobBH ++ (if owes then " (how : OwedH H)" else "") ++ (if held then " (hheld : HeldH H)" else "") ++ lawsH
    let heldPart := if held then s!"
{heldDoc}
abbrev Held : Prop := ∀ f ∈ defn.sem.heldObligations, HeldOwed defn.sem f

/-- The facts owed of the held-named functions under an interpretation H (the functions are
`Held`'s). -/
abbrev HeldH (H : HookParams) : Prop := ∀ f ∈ defn.sem.heldObligations, HeldOwed (defn.sem.withHooks H) f
" else ""
    let hobADH := if plain then hobAH else s!"({hobAH}.obligations {if owes then "how" else "(openDecided_withHooks_defn H)"})"
    let owedPart := if plain then "" else sidesPart ++ (if owes then s!"
{owedDoc}
abbrev Owed : Prop := OpenDecided defn.sem

/-- The owed conditions under an interpretation H (the rules and clauses are `Owed`'s). -/
abbrev OwedH (H : HookParams) : Prop := OpenDecided {S}
" else s!"
/-- No condition is owed: `KCore.OpenDecided`. -/
theorem openDecided_defn : OpenDecided defn.sem :=
  ⟨openRules_of_owed (by rw [owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by rw [owed_clauses]; intro p hp; cases hp)⟩

/-- No condition is owed: `KCore.OpenDecided` under every interpretation H. -/
theorem openDecided_withHooks_defn (H : HookParams) : OpenDecided {S} :=
  ⟨rulesDecided_defn H, clausesDecided_defn H⟩
")
    if !preTop then hypPre ++ owedPart ++ hyp0 ++ hypH else
    s!"/-- **The facts the deciders leave of `FnHyp`** ({termL.length} functions' termination, {totL.length}
`[total]` functions' totality, {agrL.length} functions' agreement, {matL.length} clauses' match
independence; the lists are `term_named`, `total_named`, `agree_named`, `match_named`). The
definition has no parameter symbol an interpretation gives a meaning to.{oblDoc} -/
abbrev Obl : Prop := {oblK} defn.sem callOrder []
{nilPart}{owedPart}{heldPart}
/-- **`FnHyp` of the definition's semantics** (`KCore.fnHyp_of_fnObligations{nN}`), {givenD}: what
`sound_hyp` and `complete_hyp` take. -/
theorem fnHyp_defn{hobBD0} : FnHyp defn.sem := fnHyp_of_fnObligations{nN} coreOK_defn {rh0} ParamsTotal.nil {hobAD0}

/-- **Soundness of the semantics** (`KCore.SoundC`), {givenD}. -/
theorem sound_defn{hobBD0} : SoundC defn.sem := sound_fn{nN} defn.sem callOrder [] coreOK_defn {rh0} ParamsTotal.nil {hobAD0}

/-- **Completeness of the semantics** (`KCore.CompleteC`), {givenD}. -/
theorem complete_defn (ref : OutFn){hobBD0} : CompleteC defn.sem ref :=
  complete_fn{nN} defn.sem callOrder [] ref coreOK_defn {rh0} ParamsTotal.nil {hobAD0}

/-- The facts the deciders leave of `FnHyp` under an interpretation H (the lists are `Obl`'s, the
same for every H). -/
abbrev OblH (H : HookParams) : Prop := {oblK} (defn.sem.withHooks H) callOrder []
{nilPartH}
/-- `FnHyp` of the definition's semantics under every interpretation H, {givenD}. -/
theorem fnHyp_withHooks_defn (H : HookParams){hobBDH} : FnHyp (defn.sem.withHooks H) :=
  fnHyp_withHooks{nN} coreOK_defn {rhH} ParamsTotal.nil {hobADH}

/-- **Soundness of the semantics** (`KCore.SoundC`) under every interpretation H, {givenD}. -/
theorem sound_withHooks_defn (H : HookParams){hobBDH} : SoundC (defn.sem.withHooks H) :=
  sound_fn_withHooks{nN} defn.sem callOrder [] coreOK_defn {rhH} ParamsTotal.nil {hobADH}

/-- **Completeness of the semantics** (`KCore.CompleteC`) under every interpretation H, {givenD}. -/
theorem complete_withHooks_defn (ref : OutFn) (H : HookParams){hobBDH} : CompleteC (defn.sem.withHooks H) ref :=
  complete_fn_withHooks{nN} defn.sem callOrder [] ref coreOK_defn {rhH} ParamsTotal.nil {hobADH}"
  -- the statements at a step and at a configuration, for every interpretation H, under the binders
  -- and the `FnHyp` term of the branch above
  let hobArg := if none then "" else " hob"
  let heldBH := if !held then "" else if hasParams then " (hheld : Held H)" else " (hheld : HeldH H)"
  let heldA := if held then " hheld" else ""
  let givenH := if held then given ++ ", and the facts owed of the held-named functions (`Held`)" else given
  let (bindH, fnHypH) := if hasParams then (s!" (H : HookParams) (hH : HooksTotal H){hobB}{heldBH}{lawsH}", s!"fnHyp_defn H hH{hobArg}{heldA}{lawsA}")
    else (s!" (H : HookParams){if none then "" else " (hob : OblH H)"}{heldBH}{lawsH}", s!"fnHyp_withHooks_defn H{hobArg}{heldA}{lawsA}")
  let runExact := facts && CExec.execReady c
  let bindF := s!" (H : HookParams) (hf : FnHyp {S})"
  let givenF := "given `FnHyp` of the semantics under H (`hf`)"
  let atSrc := if !preTop then
      (if plain then headlineAt bindF "hf" givenF true runExact plain
       else headlineAtOpen bindF "" givenF true runExact owesR owesC (hf := "hf"))
    else if plain then headlineAt bindH fnHypH givenH (!none || held) runExact plain else
    let bindN := if hasParams then s!" (H : HookParams){rawB}{hobB}{heldBH}{lawsH}"
      else s!" (H : HookParams){if none then "" else " (hob : OblH H)"}{heldBH}{lawsH}"
    let hobT := if raw then hobA else if !none then "hob" else if hasParams then "(obl_nil H)" else "(obl_nil_withHooks H)"
    headlineAtOpen bindN hobT givenH (!none || held) runExact owesR owesC held
  -- with an open generator: `lawHooks defn.sem H` satisfies the laws and gives the generators
  -- values, for every H, and is admitted by the library's sentences where H is and gives
  -- `_RangeMap_` no value; beside each
  -- statement, its instance there with both obligations discharged (with `FnHyp` the hypothesis,
  -- no statement takes the laws or the values, and there is none)
  let lawPart := if !raw || !preTop then "" else
    let named := !none || held
    let sfxC := if named then "_of" else ""
    let sfxS := if named || owesR || owesC then "_of" else ""
    let sfxP := if named || owesC then "_of" else ""
    let inst := fun (nm pre : String) => s!"
/-- `{nm}` at `lawHooks defn.sem H`, the two obligations discharged. -/
def {nm}_lawHooks{pre} (H : HookParams) :=
  @{nm}{if pre.isEmpty then "" else " ref"} (lawHooks defn.sem H) (openLaws_lawHooks_defn H) (openTotal_lawHooks_defn H)
"
    s!"
/-! ## The interpretation `lawHooks`

`lawHooks defn.sem H` is H everywhere but at the open generators, where it applies their laws: at a
generator with no law or one law it is the free interpretation of its laws; at one with both `assoc`
and `idem` it keeps each flattened argument at its first occurrence (`Band.nf`), so that
`f(x, f(y, x))` is `f(x, y)` there, which the two laws do not state. It shows that the
interpretations the statements are about exist; it is not the meaning of a generator, and no
statement above is stated only there. A fact that holds at `lawHooks` and that the text does not
state holds at `lawHooks`, not for every H. -/

/-- The open generators' laws hold under `lawHooks defn.sem H`, for every H
(`KCore.openLaws_lawHooks`). -/
theorem openLaws_lawHooks_defn (H : HookParams) : OpenLaws (defn.sem.withHooks (lawHooks defn.sem H)) :=
  openLaws_lawHooks defn.sem coreOK_defn H

/-- Each open generator has a value at every argument list of its sorts under `lawHooks defn.sem H`,
for every H (`KCore.openTotal_lawHooks`). -/
theorem openTotal_lawHooks_defn (H : HookParams) : OpenTotal (defn.sem.withHooks (lawHooks defn.sem H)) :=
  openTotal_lawHooks defn.sem coreOK_defn H

/-- `lawHooks defn.sem H` is admitted by the library's sentences wherever H is and gives `_RangeMap_`
no value (`KCore.libAdmitted_lawHooks`). -/
theorem libAdmitted_lawHooks_defn (H : HookParams) (ha : (defn.sem.withHooks H).libAdmitted)
    (hrm : ∀ vs, H.app rmConcat vs = none) :
    (defn.sem.withHooks (lawHooks defn.sem H)).libAdmitted :=
  libAdmitted_lawHooks defn.sem coreOK_defn H ha hrm

/-- `lawHooks defn.sem HookParams.lib` satisfies the laws, the generators' `functional` sentences and
the library's sentences together. -/
theorem lawHooks_lib_defn :
    OpenLaws (defn.sem.withHooks (lawHooks defn.sem HookParams.lib)) ∧
    OpenTotal (defn.sem.withHooks (lawHooks defn.sem HookParams.lib)) ∧
    (defn.sem.withHooks (lawHooks defn.sem HookParams.lib)).libAdmitted :=
  ⟨openLaws_lawHooks_defn HookParams.lib, openTotal_lawHooks_defn HookParams.lib,
    libAdmitted_lawHooks_defn HookParams.lib (libAdmitted_lib_of_coreOK coreOK_defn) lib_app_rmConcat_none⟩
" ++ inst "fnHyp_defn" "" ++ inst "sound_defn" "" ++ inst "complete_defn" " (ref : OutFn)" ++
      inst s!"consistent{sfxC}" "" ++ inst s!"sound_at{sfxS}" "" ++ inst s!"complete_at{sfxP}" "" ++
      (if runExact then inst s!"run_exact{sfxC}" "" else "")
  -- not plain: the owed rules' and clauses' positions, decided
  if !plain then
    let lstR := if owedR.isEmpty then "([] : List Nat)" else
      "[" ++ ",\n    ".intercalate (owedR.map fun i =>
        s!"{i} /- rule {i}{ruleLbl i}: closed over {ruleVs i} -/") ++ "]"
    let lstC := if owedC.isEmpty then "([] : List (Nat × Nat))" else
      "[" ++ ",\n    ".intercalate (owedC.map fun (i, j) =>
        s!"({i}, {j}) /- {fnName i}, clause {j} -/") ++ "]"
    o ← thm o "Owed" s!"{ns}.Core" "The rules and the clauses whose conditions are closed over an open variable of an unconfined sort, by position (`KCore.Semantics.owedRules`, `KCore.Semantics.owedClauses`): their `CondDecided` is the part of `KCore.OpenDecided` the text owes."
      s!"theorem owed_rules : defn.sem.owedRules =
    {lstR} := by decide +kernel

theorem owed_clauses : defn.sem.owedClauses =
    {lstC} := by decide +kernel"
  o ← o.write s!"{ns}.FnHyp" (s!"import {ns}.Sound
import {ns}.FnHyp.Term
import {ns}.FnHyp.Total
import {ns}.FnHyp.Agree
import {ns}.FnHyp.Match
" ++ (if held then s!"import {ns}.FnHyp.Held\n" else "") ++ (if plain then "" else s!"import {ns}.FnHyp.Owed\n") ++ (if runExact then s!"import {ns}.Facts\n" else "") ++ "import KcoreSpec.StepCompleteAt
" ++ (if raw && preTop then "import KcoreSpec.LawHooksLib\n" else "") ++ hdr (if preTop then "What the deciders leave of `FnHyp` (`KCore.FnObligations` at the rank `callOrder`; its four lists are `term_named`, `total_named`, `agree_named`, `match_named`), soundness and completeness of the definition's semantics from those facts, and, under the same facts, consistency with the statements at a step and at a configuration." else "What the deciders leave of `FnHyp` (its four lists are `term_named`, `total_named`, `agree_named`, `match_named`), which does not give `FnHyp` where a clause's predicate is not `\\top` (`clausesPreTop_false`); soundness and completeness of the definition's semantics, consistency, and the statements at a step and at a configuration, given `FnHyp` itself.") ++ s!"
namespace {ns}
open KCore
open KCore.Faithful (Γ Γstep)

{factsDef}
{body}
{atSrc}
{lawPart}
end {ns}
")
  return o

/-- The package that decides `coreOK` itself (`--core`), for a definition that meets `coreOK`
whether or not it meets `wf`: after the core and its tables, one module per conjunct of
`coreOK` (`NS.CoreOK.*`; the clauses' and the rules' sort checks read from the tables, a block of
functions or of rules a module), `coreOK_defn` joined from them (`NS.CoreOK`), and `sound_hyp` and
`complete_hyp` from it (`NS.Sound`). It states nothing that reads `wf`: no `sound`, `complete`,
facts, surface or kinds. -/
def genCore (o : Out) (ns : String) (c : Semantics) (budgetNodes : Nat) (budgetNameBytes : Nat := 8000) :
    IO Out := do
  let mut o := o
  let thm (o : Out) (mod what stmt : String) : IO Out :=
    o.write s!"{ns}.CoreOK.{mod}" (s!"import {ns}.Facts.Tables\nimport KcoreSpec.CoreChecked\n" ++ hdr what ++ s!"
namespace {ns}
open KCore KCore.Faithful KCore.Faithful.Model

{stmt}

end {ns}
")
  o ← thm o "Subsorts" "`coreOK`: the declared subsorts (`subsortsOK`), read from the tables."
    "theorem core_subsortsOK : c.subsortsOKT T = true := by decide +kernel"
  let clSize := fun (f : Fn) => (f.clauses.map fun cl =>
    (cl.pats.map termSize).foldl (· + ·) 0 + termSize cl.rhs + (cl.req.map termSize).getD 0).foldl (· + ·) 1
  let fnSizes := (c.fns.map clSize).toArray
  let fnBlocks := blocks fnSizes.size (fun i => fnSizes[i]!) budgetNodes
  let mut clMods : Array String := #[]
  for (lo, len) in fnBlocks do
    o ← thm o s!"Clauses{lo}" s!"`coreOK`: the clauses of functions {lo} to {lo + len - 1} are well sorted (`clauseSorted`), read from the tables."
      s!"theorem core_clauses{lo} : c.fnRowsSortedT T {lo} {len} = true := by decide +kernel"
    clMods := clMods.push s!"{ns}.CoreOK.Clauses{lo}"
  let ruleSizes := (c.rules.map fun r => termSize r.lhs + termSize r.rhs + (r.req.map termSize).getD 0 +
    (r.ens.map termSize).getD 0).toArray
  let ruleBlocks := blocks ruleSizes.size (fun i => ruleSizes[i]!) budgetNodes
  let mut ruleMods : Array String := #[]
  for (lo, len) in ruleBlocks do
    o ← thm o s!"Rules{lo}" s!"`coreOK`: rules {lo} to {lo + len - 1} are well sorted (`ruleSorted`), read from the tables."
      s!"theorem core_rules{lo} : c.ruleRowsSortedT T {lo} {len} = true := by decide +kernel"
    ruleMods := ruleMods.push s!"{ns}.CoreOK.Rules{lo}"
  -- the names' codes: a table of the numbered symbols' and sorts' names encoded (`strCode`),
  -- checked by blocks of rows, joined into one fact each; then the three conjuncts that read names
  -- decided on the codes
  let symNs := Faithful.allSymNames c
  let srtNs := Faithful.allSortNames c
  let symCs := symNs.map KoreAML.Distinct.strCode
  let srtCs := srtNs.map KoreAML.Distinct.strCode
  let instIs := Faithful.instIdx symCs
  o ← o.write s!"{ns}.CoreOK.Codes" (s!"import {ns}.Core\nimport KcoreSpec.NameCodes\n" ++ hdr s!"The codes (`strCode`) of the names of the {symCs.length} numbered symbols and {srtCs.length} numbered sorts, and the symbols whose codes may be of a name read as an instance (`instIdx`); data, checked in `{ns}.CoreOK.NameCodes`." ++ s!"
namespace {ns}

def symCodes : List Nat := {natListSrc symCs}

def sortCodes : List Nat := {natListSrc srtCs}

def instIdxs : List Nat := {reprStr instIs}

end {ns}
")
  let codeMods := fun (o : Out) (pfx what : String) (names : List String) => do
    let bs := blocks names.length (fun i => (names.getD i "").utf8ByteSize + 8) budgetNameBytes
    let mut o := o
    let mut mods : Array String := #[]
    for (lo, len) in bs do
      o ← o.write s!"{ns}.CoreOK.{pfx}Codes{lo}" (s!"import {ns}.CoreOK.Codes\n" ++ hdr s!"The codes of the names of the numbered {what} {lo} to {lo + len - 1}." ++ s!"
namespace {ns}
open KCore KCore.Faithful

theorem {pfx.toLower}_codes{lo} : codeRows (all{pfx}Names defn.sem) {pfx.toLower}Codes {lo} {len} = true := by decide +kernel

end {ns}
")
      mods := mods.push s!"{ns}.CoreOK.{pfx}Codes{lo}"
    return (o, bs, mods)
  let (o1, symBs, symMods) ← codeMods o "Sym" "symbols" symNs
  let (o2, srtBs, srtMods) ← codeMods o1 "Sort" "sorts" srtNs
  o := o2
  let joinCodes := fun (pfx : String) (bs : List (Nat × Nat)) (n : Nat) => Id.run do
    let p := pfx.toLower
    let mut acc := s!"{p}_codes0"
    let mut lines : Array String := #[]
    for (lo, len) in bs.drop 1 do
      let nm := s!"{p}_codes_upto{lo + len}"
      lines := lines.push s!"private theorem {nm} : codeRows (all{pfx}Names defn.sem) {p}Codes 0 {lo + len} = true :=\n  codeRows_join {acc} {p}_codes{lo} rfl rfl"
      acc := nm
    lines := lines.push s!"private theorem {p}Names_length : (all{pfx}Names defn.sem).length = {n} := by decide +kernel"
    lines := lines.push s!"private theorem {p}Codes_length : {p}Codes.length = {n} := by decide +kernel"
    lines := lines.push s!"theorem {p}_codes : (all{pfx}Names defn.sem).map KoreAML.Distinct.strCode = {p}Codes :=\n  codeRows_all {p}Names_length {p}Codes_length {acc}"
    return "\n".intercalate lines.toList
  o ← o.write s!"{ns}.CoreOK.NameCodes" (String.join ((symMods ++ srtMods).toList.map (s!"import {·}\n")) ++ hdr "The codes of the numbered names, one fact for the symbols and one for the sorts, joined from their blocks; the symbols whose codes may be of a name read as an instance (`instIdx`)." ++ s!"
namespace {ns}
open KCore KCore.Faithful

{joinCodes "Sym" symBs symCs.length}

{joinCodes "Sort" srtBs srtCs.length}

theorem inst_idx : instIdx symCodes = instIdxs := by decide +kernel

end {ns}
")
  for p in faithCoreParts do
    match nameParts.find? (·.1 == p) with
    | some (_, lemma, decision) =>
      o ← o.write s!"{ns}.CoreOK.{p}" (s!"import {ns}.CoreOK.NameCodes\n" ++ hdr s!"`coreOK`: `{p}`, decided on the names' codes (`{decision.splitOn " " |>.head!}`)." ++ s!"
namespace {ns}
open KCore KCore.Faithful KCore.Faithful.Model

theorem core_{p} : {p} defn.sem = true := {lemma} (by decide +kernel)

end {ns}
")
    | none =>
      o ← thm o p s!"`coreOK`: `{p}`, by the kernel." s!"theorem core_{p} : {p} defn.sem = true := by decide +kernel"
  for p in ["hooksApart", "predsApart", "idsOK"] do
    o ← thm o p s!"`coreOK`: `{p}`, by the kernel." s!"theorem core_{p} : defn.sem.{p} = true := by decide +kernel"
  -- joined: the blocks by their boundaries, then `coreOK_defn`
  let join := fun (bs : List (Nat × Nat)) (pfx joinL : String) (stmt : Nat → String) => Id.run do
    let mut acc := s!"{pfx}0"
    let mut lines : Array String := #[]
    for (lo, len) in bs.drop 1 do
      let nm := s!"{pfx}_upto{lo + len}"
      lines := lines.push s!"private theorem {nm} : {stmt (lo + len)} := {joinL} {acc} {pfx}{lo} rfl rfl"
      acc := nm
    return ("\n".intercalate lines.toList, acc)
  let clJ := join fnBlocks "core_clauses" "Semantics.fnRowsSortedT_join" fun n => s!"c.fnRowsSortedT T 0 {n} = true"
  let ruleJ := join ruleBlocks "core_rules" "Semantics.ruleRowsSortedT_join" fun n => s!"c.ruleRowsSortedT T 0 {n} = true"
  let clAll := if fnBlocks.isEmpty then "theorem core_clauses : c.fnRowsSortedT T 0 c.fns.length = true := by decide +kernel"
    else s!"{clJ.1}\ntheorem fns_length : c.fns.length = {fnSizes.size} := by decide +kernel\ntheorem core_clauses : c.fnRowsSortedT T 0 c.fns.length = true := Semantics.fnRowsSortedT_all fns_length {clJ.2}"
  let ruleAll := if ruleBlocks.isEmpty then "theorem core_rules : c.ruleRowsSortedT T 0 c.rules.length = true := by decide +kernel"
    else s!"{ruleJ.1}\ntheorem rules_length : c.rules.length = {ruleSizes.size} := by decide +kernel\ntheorem core_rules : c.ruleRowsSortedT T 0 c.rules.length = true := Semantics.ruleRowsSortedT_all rules_length {ruleJ.2}"
  let parts := [s!"{ns}.CoreOK.Subsorts"] ++ clMods.toList ++ ruleMods.toList ++
    (faithCoreParts ++ ["hooksApart", "predsApart", "idsOK"]).map (s!"{ns}.CoreOK.{·}")
  o ← o.write s!"{ns}.CoreOK" (String.join (parts.map (s!"import {·}\n")) ++
    hdr "`coreOK` of the definition's semantics, joined from its conjuncts, each decided by the kernel on its own (`NS.CoreOK.*`); not `wf`, which this package does not state." ++ s!"
namespace {ns}
open KCore

{clAll}
{ruleAll}

/-- The decidable conditions soundness and completeness assume of the definition's semantics
(`KCore.Semantics.coreOK`), decided conjunct by conjunct, the sort checks from the tables
(`KCore.Semantics.coreOK_of_T`). -/
theorem coreOK_defn : defn.sem.coreOK = true :=
  Semantics.coreOK_of_T T_eq core_subsortsOK core_clauses core_rules
    (Semantics.faithCoreOK_of_partsK {" ".intercalate (faithCoreParts.map (s!"core_{·}"))})
    core_hooksApart core_predsApart core_idsOK (by decide +kernel)

end {ns}
")
  o ← o.write s!"{ns}.Sound" (s!"import KcoreSpec.Sound\nimport {ns}.CoreOK\n" ++ hdr "Soundness and completeness of the definition's semantics (`KCore.SoundC`, `KCore.CompleteC`) from `coreOK` (`coreOK_defn`, decided without `wf`) and the hypothesis on its functions (`KCore.FnHyp`)." ++ s!"
namespace {ns}
open KCore

/-- **Soundness of the semantics** (`KCore.SoundC`) for functions that meet the hypothesis
`KCore.FnHyp` (each has a result at every argument list of its sorts, each `[total]` one a value,
equations of one priority coherent, matches of a clause agreeing): from `coreOK_defn`. -/
theorem sound_hyp (hf : FnHyp defn.sem) : SoundC defn.sem := KCore.sound_hyp defn.sem coreOK_defn hf

/-- **Completeness of the semantics** (`KCore.CompleteC`), for an outcome function `ref` that lists
the outcomes at each configuration (`KCore.OutIs`), for functions that meet `KCore.FnHyp`: from `coreOK_defn`. -/
theorem complete_hyp (ref : OutFn) (hf : FnHyp defn.sem) : CompleteC defn.sem ref :=
  KCore.complete_hyp defn.sem ref coreOK_defn hf

end {ns}
")
  return o

/-- The tie's modules (`--tie`), written after the package's: `Tied kore` from `parse kore = .ok defn`,
`wf defn` and `Reordered defn.emit kore`, each by blocks (`πs`: the permutation hint, `perms`). -/
def genTie (o : Out) (koreFile ns kore : String) (k : Kore.Definition) (d : Definition)
    (πs : List (List Nat)) (exec : Bool) (budgetSents budgetScan budgetProds budgetRules budgetEvents
    budgetClauses : Nat) (plain : Bool) : IO (Option Out) := do
  let mut o := o
  let c := d.sem
  -- Tie, by blocks: the KORE stored in segments (`kore_term … cut`), `Reordered` one slice of the
  -- user module's blocks at a time, `wf` conjunct by conjunct, then `Tied` from its parts
  let blocksE := userBlocks c d.pres
  let mK := k.modules.getLastD default
  let π := πs.getLastD []
  -- each emitted sentence's position in the KORE, block by block
  -- a sentence of the library's text is a constant the kernel compares at once; a generated one
  -- costs about its size
  let libSents := kernelText d.pres.simpArg ++ d.pres.imports.flatMap (moduleText d.pres.simpArg)
  let wOf (s : Kore.Sentence) : Nat := if libSents.contains s then 1 else 1 + (toString (repr s)).length / 40
  let blockW := blocksE.map fun bl => bl.foldl (fun a s => a + wOf s) 0
  let ranges := blocks blocksE.length (fun i => blockW.getD i 0) budgetSents
  -- the segments: maximal runs of emitted sentences, consecutive in the KORE, inside one range
  let mut segStarts : Array (Nat × Nat) := #[]   -- (KORE start, length), in emitted order
  let mut rangeSegs : Array (List Nat) := #[]     -- per range, its segments' numbers in emitted order (by start for now)
  let mut j := 0
  for (lo, n) in ranges do
    let cnt := ((blocksE.drop lo).take n).foldl (fun a bl => a + bl.length) 0
    let mut mine : Array Nat := #[]
    let mut i := 0
    while i < cnt do
      let st := π.getD (j + i) 0
      let mut len := 1
      while i + len < cnt && π.getD (j + i + len) 0 == st + len do len := len + 1
      mine := mine.push segStarts.size
      segStarts := segStarts.push (st, len)
      i := i + len
    rangeSegs := rangeSegs.push mine.toList
    j := j + cnt
  -- number the segments in the KORE's order
  let order := (List.range segStarts.size).toArray.qsort (fun x y => (segStarts[x]!).1 < (segStarts[y]!).1)
  let rank : Array Nat := order.zipIdx.foldl (fun acc (x, r) => acc.set! x r) (Array.replicate order.size 0)
  let cuts := (order.toList.map fun x => (segStarts[x]!).1).drop 1
  let σs := rangeSegs.toList.map (·.map fun x => rank[x]!)
  o ← o.write s!"{ns}.Tie.Kore" (s!"import KcoreSpec.Kore.KoreTerm\n" ++ hdr s!"`{kore}` as a Lean term, its user module in {segStarts.size} segments (the cuts are an untrusted hint: `kore` denotes the file's definition whatever they are)." ++ s!"
namespace {ns}

kore_term kore from {kore.quote} cut {reprStr cuts}

end {ns}
")
  -- parse by stages: the scan of the user module a block of segments at a time, then `finish`
  let segsK := cutAt mK.sentences cuts
  let segW := segsK.map fun sg => sg.foldl (fun a s => a + 1 + (toString (repr s)).length / 200) 0
  let scanBlocks := blocks segsK.length (fun i => segW.getD i 0) budgetScan
  let Sc := Parse.scan mK.sentences
  let .ok E := Parse.envOf mK Sc | IO.eprintln s!"{koreFile}: the names fail"; return none
  let prodW := (Parse.prodSyms Sc E).map fun x => 1 + (Sc.eqs.filter (·.fn == x.symbol.ident.ident.name)).length * 4
  let prodBlocks := blocks (Parse.prodSyms Sc E).length (fun i => prodW.getD i 1) budgetProds
  let ruleW := Sc.rewrites.map fun r => 1 + (toString (repr r)).length / 200
  let ruleBlocks' := blocks Sc.rewrites.length (fun i => ruleW.getD i 1) budgetRules
  let evBlocks := blocks Sc.events.length (fun _ => 1) budgetEvents
  -- a function with more than `budgetClauses` clauses has its clauses checked in blocks
  let clsSplit : List (Nat × String × List (Nat × Nat)) := ((Parse.prodSyms Sc E).zipIdx.filterMap fun (x, i) =>
    let label := x.symbol.ident.ident.name
    let n := (Parse.fnPairs Sc.eqs label).length
    if n > budgetClauses then some (i, label, blocks n (fun _ => 1) budgetClauses) else none)
  let clsData := clsSplit.flatMap fun (i, _, bs) => [i, bs.length] ++ bs.map (·.2)
  let lens := fun (bs : List (Nat × Nat)) => reprStr (bs.map (·.2))
  o ← o.write s!"{ns}.Tie.ParseData" (s!"import KcoreSpec.ParseCmd\n" ++ hdr s!"`parse`'s stages on the file, as data: the scan of the user module in {scanBlocks.length} blocks of segments, the names, the productions in {prodBlocks.length} blocks, the rules in {ruleBlocks'.length} (a hint: `Tie.Scan*`, `Tie.Env`, `Tie.Prods*`, `Tie.Rules*` and `Tie.Assemble` check each)." ++ s!"
namespace {ns}

parse_stages stage from {kore.quote} cut {reprStr cuts} scan_blocks {lens scanBlocks} prod_blocks {lens prodBlocks} rule_blocks {lens ruleBlocks'} event_blocks {lens evBlocks} clause_blocks {reprStr clsData}

end {ns}
")
  let (scanAll, scanJoin) := Id.run do
    let mut S := "stage.scan0"
    let mut acc := "scanIs0"
    let mut tot := (scanBlocks.getD 0 (0, 0)).2
    for ((_, n), r) in (scanBlocks.drop 1).zipIdx do
      S := s!"({S}.append stage.scan{r + 1})"
      acc := s!"(KCore.Parse.ScanIs.join {acc} scanIs{r + 1} (k := {tot + n}) rfl)"
      tot := tot + n
    return (S, acc)
  let joinMap := fun (pre fact : String) (bs : List (Nat × Nat)) => Id.run do
    let mut r := s!"stage.{pre}0"
    let mut acc := s!"{fact}0"
    let mut tot := (bs.getD 0 (0, 0)).2
    for ((_, n), i) in (bs.drop 1).zipIdx do
      r := s!"({r} ++ stage.{pre}{i + 1})"
      acc := s!"(KCore.Parse.MapIs.join {acc} {fact}{i + 1} (k := {tot + n}) rfl)"
      tot := tot + n
    return (r, acc)
  let (prodsAll, prodsJoin) := if prodBlocks.isEmpty then ("[]", "") else joinMap "prods" "prodsIs" prodBlocks
  let (rulesAll, rulesJoin) := if ruleBlocks'.isEmpty then ("[]", "") else joinMap "rules" "rulesIs" ruleBlocks'
  o ← o.write s!"{ns}.Tie.ScanAll" (s!"import KcoreSpec.Parse\nimport {ns}.Tie.ParseData\n" ++ hdr "The user module's scan: its blocks' scans, appended." ++ s!"
namespace {ns}

noncomputable def scanAll : KCore.Parse.Scan := {scanAll}

end {ns}
")
  let mut scanMods : Array String := #[]
  for ((lo, n), r) in scanBlocks.zipIdx do
    let m := s!"{ns}.Tie.Scan{r}"
    scanMods := scanMods.push m
    o ← o.write m (s!"import KcoreSpec.Parse\nimport KcoreSpec.Kore.KernelRfl\nimport {ns}.Tie.Kore\nimport {ns}.Tie.ParseData\n" ++ hdr s!"The scan of segments {lo} to {lo + n - 1} of the user module." ++ s!"
namespace {ns}

theorem scanIs{r} : KCore.Parse.ScanIs kore.segs {lo} {n} stage.scan{r} := by
  unfold KCore.Parse.ScanIs; kernel_rfl

end {ns}
")
  let stageImports := s!"import KcoreSpec.Parse\nimport KcoreSpec.Kore.KernelRfl\nimport {ns}.Tie.Kore\nimport {ns}.Tie.ScanAll\n"
  o ← o.write s!"{ns}.Tie.Env" (stageImports ++ hdr "The names `parse` gives, from the scan." ++ s!"
namespace {ns}

theorem env_eq : KCore.Parse.envOf (kore.modules.getLastD default) scanAll = .ok stage.env := by kernel_rfl

end {ns}
")
  let mut stageMods : Array String := #[s!"{ns}.Tie.Env"]
  -- the clauses of the functions checked in blocks, then joined (`Parse.fnClauses`)
  for (si, label, bs) in clsSplit do
    let mut clsMods : Array String := #[]
    for ((lo, n), cj) in bs.zipIdx do
      let m := s!"{ns}.Tie.Cls{si}_{cj}"
      clsMods := clsMods.push m
      stageMods := stageMods.push m
      o ← o.write m (stageImports ++ hdr s!"The clauses {lo} to {lo + n - 1} of the function `{label}`." ++ s!"
namespace {ns}

theorem clsIs{si}_{cj} : KCore.Parse.MapIs (KCore.Parse.clauseOf stage.env.N stage.env.src) (KCore.Parse.fnPairs scanAll.eqs {label.quote}) {lo} {n} stage.cls{si}_{cj} := by
  unfold KCore.Parse.MapIs; kernel_rfl

end {ns}
")
    let (r, acc) := Id.run do
      let mut r := s!"stage.cls{si}_0"
      let mut acc := s!"clsIs{si}_0"
      let mut tot := (bs.getD 0 (0, 0)).2
      for ((_, n), cj) in (bs.drop 1).zipIdx do
        r := s!"({r} ++ stage.cls{si}_{cj + 1})"
        acc := s!"(KCore.Parse.MapIs.join {acc} clsIs{si}_{cj + 1} (k := {tot + n}) rfl)"
        tot := tot + n
      return (r, acc)
    let m := s!"{ns}.Tie.Cls{si}"
    stageMods := stageMods.push m
    o ← o.write m (stageImports ++ String.join (clsMods.toList.map (s!"import " ++ · ++ "\n")) ++ hdr s!"The clauses of the function `{label}`, from their blocks." ++ s!"
namespace {ns}

theorem pairs{si}_length : (KCore.Parse.fnPairs scanAll.eqs {label.quote}).length = {(Parse.fnPairs Sc.eqs label).length} := by decide +kernel

theorem cls{si} : KCore.Parse.fnClauses stage.env.N stage.env.src scanAll.eqs {label.quote} = .ok {r} :=
  KCore.Parse.MapIs.all pairs{si}_length {acc}

end {ns}
")
  for ((lo, n), i) in prodBlocks.zipIdx do
    let m := s!"{ns}.Tie.Prods{i}"
    stageMods := stageMods.push m
    let here := clsSplit.filter fun (si, _, _) => lo ≤ si && si < lo + n
    if here.isEmpty then
      o ← o.write m (stageImports ++ hdr s!"The productions of user symbols {lo} to {lo + n - 1}." ++ s!"
namespace {ns}

theorem prodsIs{i} : KCore.Parse.MapIs (KCore.Parse.symProd stage.env scanAll.eqs) (KCore.Parse.prodSyms scanAll stage.env) {lo} {n} stage.prods{i} := by
  unfold KCore.Parse.MapIs; kernel_rfl

end {ns}
")
    else
      let ov := ", ".intercalate (here.map fun (si, label, bs) =>
        let r := (List.range bs.length).foldl (fun acc cj => if cj == 0 then s!"stage.cls{si}_0" else s!"({acc} ++ stage.cls{si}_{cj})") ""
        s!"({label.quote}, {r})")
      let pf := here.foldr (fun (si, _, _) acc => s!"(List.forall_mem_cons.2 ⟨cls{si}, {acc}⟩)") "(fun _ h => nomatch h)"
      o ← o.write m (stageImports ++ String.join (here.map fun (si, _, _) => s!"import {ns}.Tie.Cls{si}\n") ++ hdr s!"The productions of user symbols {lo} to {lo + n - 1}, the clauses of {", ".intercalate (here.map fun (_, l, _) => s!"`{l}`")} from their blocks." ++ s!"
namespace {ns}

theorem prodsIs{i} : KCore.Parse.MapIs (KCore.Parse.symProd stage.env scanAll.eqs) (KCore.Parse.prodSyms scanAll stage.env) {lo} {n} stage.prods{i} := by
  rw [← KCore.Parse.symProdT_eq (ov := [{ov}]) {pf}]
  unfold KCore.Parse.MapIs; kernel_rfl

end {ns}
")
  for ((lo, n), i) in ruleBlocks'.zipIdx do
    let m := s!"{ns}.Tie.Rules{i}"
    stageMods := stageMods.push m
    o ← o.write m (stageImports ++ hdr s!"The rules of rewrite axioms {lo} to {lo + n - 1}." ++ s!"
namespace {ns}

theorem rulesIs{i} : KCore.Parse.MapIs (KCore.Parse.ruleOf stage.env.N stage.env.src) scanAll.rewrites {lo} {n} stage.rules{i} := by
  unfold KCore.Parse.MapIs; kernel_rfl

end {ns}
")
  -- the assembly in its parts (`Parse.assemble_of_parts`), each checked in a module of its own
  -- the declaration events a block at a time, then their merge into the productions
  for ((lo, n), i) in evBlocks.zipIdx do
    let m := s!"{ns}.Tie.AsmEvents{i}"
    stageMods := stageMods.push m
    o ← o.write m (stageImports ++ hdr s!"The declaration events {lo} to {lo + n - 1} of the user module, numbered." ++ s!"
namespace {ns}

theorem eventsIs{i} : KCore.Parse.FilterIs (KCore.Parse.eventOf stage.env {prodsAll}) scanAll.events {lo} {n} stage.events{i} := by
  unfold KCore.Parse.FilterIs; kernel_rfl

end {ns}
")
  let (evAll, evJoin) := Id.run do
    let mut r := "stage.events0"
    let mut acc := "eventsIs0"
    let mut tot := (evBlocks.getD 0 (0, 0)).2
    for ((_, n), i) in (evBlocks.drop 1).zipIdx do
      r := s!"({r} ++ stage.events{i + 1})"
      acc := s!"(KCore.Parse.FilterIs.join {acc} eventsIs{i + 1} (k := {tot + n}) rfl)"
      tot := tot + n
    return (r, acc)
  let evFact := if evBlocks.isEmpty then s!"(by kernel_rfl : scanAll.events.filterMap (KCore.Parse.eventOf stage.env {prodsAll}) = [])"
    else s!"(KCore.Parse.FilterIs.all events_length {evJoin})"
  let evAll := if evBlocks.isEmpty then "[]" else evAll
  let evImports := String.join ((List.range evBlocks.length).map fun i => s!"import {ns}.Tie.AsmEvents{i}\n")
  let asm := [("AsmProds", "The productions with the subsorts merged in: the events from their blocks, then the merge.",
      s!"theorem events_length : scanAll.events.length = {Sc.events.length} := by decide +kernel

theorem merge_eq : KCore.Parse.mergeProds {prodsAll} {evAll} = stage.prodsM := by kernel_rfl

theorem prodsM_eq : KCore.Parse.prodsOf scanAll stage.env {prodsAll} = stage.prodsM :=
  (KCore.Parse.prodsOf_of_events {evFact}).trans merge_eq"),
    ("AsmCore", "The core the assembly gives is `defn.sem`.",
      s!"theorem core_eq : KCore.Parse.coreOf scanAll stage.env stage.prodsM {rulesAll} = .ok defn.sem := by kernel_rfl"),
    ("AsmCells", "The presentation's per-sort and per-cell parts.",
      "theorem cells_eq : KCore.Parse.cellPartsOf scanAll stage.env defn.sem = .ok stage.cells := by kernel_rfl"),
    ("AsmPres", "The presentation the assembly gives is `defn.pres`.",
      s!"theorem pres_eq : KCore.Parse.presOf (kore.modules.getLastD default) scanAll stage.env stage.prodsM {rulesAll} defn.sem stage.cells = .ok defn.pres := by kernel_rfl"),
    ("AsmCert", "The certificates the assembly gives are `defn.cert`.",
      "theorem cert_eq : KCore.Parse.certOf defn.sem = defn.cert := by kernel_rfl")]
  for (n, doc, thm) in asm do
    let m := s!"{ns}.Tie.{n}"
    stageMods := stageMods.push m
    o ← o.write m (stageImports ++ s!"import {ns}.Core\n" ++ (if n == "AsmProds" then evImports else "") ++ hdr doc ++ s!"
namespace {ns}

{thm}

end {ns}
")
  o ← o.write s!"{ns}.Tie.Assemble" (s!"import KcoreSpec.Parse\n" ++ String.join (asm.map fun (n, _, _) => s!"import {ns}.Tie.{n}\n") ++ hdr "The definition `parse` assembles from its stages is `defn`." ++ s!"
namespace {ns}

theorem assemble_defn : KCore.Parse.assemble (kore.modules.getLastD default) scanAll stage.env {prodsAll} {rulesAll} = .ok defn :=
  KCore.Parse.assemble_of_parts prodsM_eq core_eq cells_eq pres_eq cert_eq

end {ns}
")
  stageMods := stageMods.push s!"{ns}.Tie.Assemble"
  let mapAll := fun (lenFact join l f : String) => if join.isEmpty then s!"(by kernel_rfl : {l}.mapM ({f}) = .ok [])" else s!"(KCore.Parse.MapIs.all {lenFact} {join})"
  o ← o.write s!"{ns}.Tie.Parse" (s!"import KcoreSpec.Parse\nimport KcoreSpec.Kore.KernelRfl\nimport {ns}.Core\n" ++ String.join ((scanMods ++ stageMods).toList.map (s!"import " ++ · ++ "\n")) ++ hdr "`defn` is the kernel's `parse` of the KORE term: the scan, the names, the productions and the rules, each checked in blocks, then the assembly." ++ s!"
namespace {ns}

theorem last_module : kore.modules.getLast? = some (kore.modules.getLastD default) := by kernel_rfl
theorem segs_length : kore.segs.length = {segsK.length} := by decide +kernel
theorem userSyms_length : (KCore.Parse.prodSyms scanAll stage.env).length = {(Parse.prodSyms Sc E).length} := by decide +kernel
theorem rewrites_length : scanAll.rewrites.length = {Sc.rewrites.length} := by decide +kernel

theorem scan_eq : KCore.Parse.scan (kore.modules.getLastD default).sentences = scanAll :=
  KCore.Parse.ScanIs.all segs_length
    {scanJoin}

theorem finish_defn : KCore.Parse.finish (kore.modules.getLastD default) scanAll = .ok defn :=
  KCore.Parse.finish_of_stages env_eq
    {mapAll "userSyms_length" prodsJoin "(KCore.Parse.prodSyms scanAll stage.env)" "KCore.Parse.symProd stage.env scanAll.eqs"}
    {mapAll "rewrites_length" rulesJoin "scanAll.rewrites" "KCore.Parse.ruleOf stage.env.N stage.env.src"}
    assemble_defn

theorem prelude_eq : kore.modules.dropLast = KCore.preludeModules := by kernel_rfl

theorem refused_nil : scanAll.refused = [] := by kernel_rfl

theorem parse_defn : KCore.Parse.parse kore = .ok defn :=
  KCore.Parse.parse_of_scan last_module prelude_eq scan_eq refused_nil finish_defn

end {ns}
")
  let mut sliceMods : Array String := #[]
  for ((lo, n), r) in ranges.zipIdx do
    let m := s!"{ns}.Tie.Emit{r}"
    sliceMods := sliceMods.push m
    o ← o.write m (s!"import KcoreSpec.Tie\nimport KcoreSpec.Kore.KernelRfl\nimport {ns}.Core\nimport {ns}.Tie.Kore\n" ++ hdr s!"The user module's blocks {lo} to {lo + n - 1} are the KORE's segments {reprStr (σs.getD r [])}." ++ s!"
namespace {ns}
open KCore

theorem slice{r} : KoreAML.Blocks.SliceIs (userBlocks defn.sem defn.pres) kore.segs {lo} {n} {reprStr (σs.getD r [])} := by
  unfold KoreAML.Blocks.SliceIs; kernel_rfl

end {ns}
")
  -- the slices joined left to right, each join naming the blocks it covers
  let joined := Id.run do
    let mut acc := "slice0"
    let mut tot := (ranges.getD 0 (0, 0)).2
    for ((_, n), r) in (ranges.drop 1).zipIdx do
      acc := s!"(KoreAML.Blocks.SliceIs.join {acc} slice{r + 1} (k := {tot + n}) rfl)"
      tot := tot + n
    return acc
  o ← o.write s!"{ns}.Tie.Emit" (s!"import KcoreSpec.Tie\nimport KcoreSpec.Kore.KernelRfl\n" ++ String.join (sliceMods.toList.map (s!"import " ++ · ++ "\n")) ++ hdr "`defn`'s `emit` is the KORE term up to sentence order: the slices joined, the segments' order a permutation, and the modules around the user module the same." ++ s!"
namespace {ns}
open KCore

theorem blocks_length : (userBlocks defn.sem defn.pres).length = {blocksE.length} := by decide +kernel

theorem segs_perm : {reprStr (σs.flatten)}.isPerm (List.range kore.segs.length) = true := by decide +kernel

theorem attrs_eq : defn.emit.attributes = kore.attributes := by kernel_rfl

theorem modules_eq : kore.modules = preludeModules ++ [kore.modules.getLastD default] := by kernel_rfl

theorem name_eq : (userModule defn.sem defn.pres).name = (kore.modules.getLastD default).name := by kernel_rfl

theorem mattrs_eq : (userModule defn.sem defn.pres).attributes = (kore.modules.getLastD default).attributes := by kernel_rfl

theorem emit_defn : KoreAML.Reordered defn.emit kore :=
  reordered_of_blocks attrs_eq modules_eq name_eq mattrs_eq rfl blocks_length
    {joined}
    segs_perm

end {ns}
")
  o ← genWf o ns "Tie" d exec plain
  o ← o.write s!"{ns}.Tie" (s!"import KcoreSpec.Tie\nimport {ns}.Tie.Wf\nimport {ns}.Tie.Parse\nimport {ns}.Tie.Emit\n" ++ hdr s!"The KORE is tied: `defn` is its parse, well formed, and its `emit` is the KORE up to sentence order." ++ s!"
namespace {ns}

theorem tied : KCore.Tied kore := KCore.Tied.of_parts parse_defn wf_defn emit_defn

#eval show Lean.CoreM Unit from do
  let axs ← Lean.collectAxioms ``tied
  unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError \"axioms: \{axs}\"

end {ns}
")
  return some o

/-! ## Readable terms: one function per constructor -/

/-- The production's label in K's name of its symbol: `_+__EXPR-SYNTAX_Expr_Expr_Expr` is the label
`_+_`, the module `EXPR-SYNTAX`, the result sort and the argument sorts; `none` when the name does
not end in a module and the symbol's own sorts. -/
def prodLabel (c : Semantics) (full : String) (args : List Srt) (res : Srt) : Option String :=
  let suffix := ("_" ++ c.sortName res ++ String.join (args.map fun s => "_" ++ c.sortName s)).toList
  let fl := full.toList
  if !suffix.isSuffixOf fl then none else
  let pre := (fl.take (fl.length - suffix.length)).reverse
  let (modRev, rest) := pre.span (· != '_')
  let modOk := !modRev.isEmpty && modRev.all fun ch => ch.isUpper || ch.isDigit || ch == '-'
  match rest with
  | '_' :: labelRev => if modOk && !labelRev.isEmpty then some (String.ofList labelRev.reverse) else none
  | _ => none

/-- The readable name of each of the definition's constructors (its own, the library's, the
configuration's): the production's label (`prodLabel`), a freezer's `#freezer` with its
production's label and position; where two constructors would get one name, or the label cannot be
read, the decoded KORE name; a name still repeated gets the symbol's number. Deterministic: it
depends on the symbol names and signatures alone. -/
def ctorNames (c : Semantics) : List (CtorSig × String) := Id.run do
  let ks := c.lib.ctors ++ c.ctors
  let fullOf := fun (k : CtorSig) => decodeK (c.symName k.name)
  let fulls := ks.map fun k => (k, fullOf k)
  let short := fun (k : CtorSig) (full : String) =>
    if full.startsWith "#freezer" then
      let body := (full.toList.drop 8)
      match body.reverse with
      | '_' :: r =>
        let (digRev, innerRev) := r.span Char.isDigit
        let inner := String.ofList innerRev.reverse
        match fulls.find? (·.2 == inner), digRev.isEmpty with
        | some (k', _), false => (prodLabel c inner k'.args k'.result).map fun l => "#freezer" ++ l ++ String.ofList digRev.reverse
        | _, _ => none
      | _ => none
    else prodLabel c full k.args k.result
  let cand : List (CtorSig × String × String) := fulls.map fun (k, full) => (k, full, (short k full).getD full)
  let named : List (CtorSig × String) := cand.map fun (k, full, s) =>
    if (cand.filter fun (e : CtorSig × String × String) => e.2.2 == s).length > 1 then (k, full) else (k, s)
  return named.map fun (k, n) =>
    if (named.filter fun (e : CtorSig × String) => e.2 == n).length > 1 then (k, s!"{n}_{k.name}") else (k, n)

/-- The module `NS.Syntax`: a function on `Tm` per constructor, its value by `rfl`, the subsorts as
coercions (the injections), and the inversion of a configuration's sort at the top cell. -/
def genSyntax (o : Out) (ns : String) (g : Ctx) (c : Semantics) (imp : String) : IO Out := do
  let names := ctorNames c
  let tm := fun (s : Srt) => s!"(KCore.Tm {g.srt s})"
  let defs := names.map fun (k, n) =>
    let xs := (List.range k.args.length).map (s!"x{·}")
    let binders := String.join ((xs.zip k.args).map fun (x, s) => s!" ({x} : {tm s})")
    let vals := "[" ++ ", ".intercalate (xs.map (· ++ ".val")) ++ "]"
    let app := String.join (xs.map (" " ++ ·))
    s!"/-- `{decodeK (c.symName k.name)}` -/
def {quoteId n}{binders} : {tm k.result} := ⟨.ctor {g.sym k.name} {vals}⟩
theorem {quoteId n}.val_def{binders} : ({quoteId n}{app}).val = .ctor {g.sym k.name} {vals} := _root_.rfl"
  let subs := c.subsorts.filter fun (a, b) => a != b && b != Srt.k
  let coes := subs.map fun (a, b) =>
    s!"scoped instance coe_{a}_{b} : _root_.Coe {tm a} {tm b} := ⟨KCore.Tm.inj⟩"
  let top := match lookupSig c.ctorSigs topLabel with
    | some k => if k.args.isEmpty then "" else
      let xs := (List.range k.args.length).map (s!"x{·}")
      let concl := " ∧ ".intercalate ((xs.zip k.args).map fun (p : String × Srt) => s!"c.sortOf {p.1} = some {g.srt p.2}")
      let projs := (List.range k.args.length).map fun i =>
        "p" ++ String.join (List.replicate i ".2") ++ ".1"
      s!"
/-- **A configuration's cells have their sorts**: the arguments of the top cell of a term of the
configuration sort have the top cell's argument sorts. -/
theorem top_sorts \{{" ".intercalate xs} : KCore.GroundTerm}
    (h : c.sortOf (.ctor KCore.topLabel [{", ".intercalate xs}]) = some KCore.topCellSort) :
    {concl} := by
  have p := KCore.sortsAre_of_ctor (c := c) (ts := [{", ".intercalate xs}])
    (k := ⟨KCore.topLabel, {g.srts k.args}, {g.srt k.result}⟩) h (by kernel_defeq)
  exact {if projs.length == 1 then "p.1" else "⟨" ++ ", ".intercalate projs ++ "⟩"}
"
    | none => ""
  o.write s!"{ns}.Syntax" (s!"import {imp}\nimport KcoreSpec.Fire\n" ++ hdr s!"Readable terms: a function on `KCore.Tm` per constructor ({names.length}), named after its production (`KcoreGen.ctorNames`), its value by `rfl`; the {subs.length} subsorts as coercions (`open {ns}.Syntax` makes them apply); the inversion of a configuration's sort at the top cell." ++ s!"
namespace {ns}.Syntax
open KCore

/-! ## Subsorts: the injections, as coercions -/

{"\n".intercalate coes}

/-! ## Constructors -/

{"\n\n".intercalate defs}

end {ns}.Syntax

namespace {ns}
{top}
end {ns}
")

def gen (koreFile : String) (out : System.FilePath) (ns : String) (budgetPairs : Nat := 64)
    (budgetNodes : Nat := 3000) (budgetSents : Nat := 1000) (budgetScan : Nat := 1000) (budgetProds : Nat := 30) (budgetRules : Nat := 300) (budgetEvents : Nat := 40) (budgetClauses : Nat := 20) (certs : List (String × String) := []) (high : List String := []) (keyed : List String := []) (tie : Bool := false) (wfMods : Bool := false) (core : Bool := false) (withSyntax : Bool := true) (asNotPlain : Bool := false) : IO UInt32 := do
  let text ← IO.FS.readFile koreFile
  let .ok k := Kore.parseDefinition text | IO.eprintln s!"{koreFile}: KORE read error"; return 1
  -- the account of the reading: each class's count, then the refusals or the sentences read and
  -- not accounted for
  IO.println s!"{koreFile}: {Parse.preludeLength k} sentences of the prelude; the user module's by class:"
  for (n, i) in Parse.classCounts k do IO.println s!"  {i} {n}"
  let reportUnconsumed (d : Definition) : IO Bool := do
    let un := Parse.unconsumed k d
    unless un.isEmpty do
      IO.eprintln s!"{koreFile}: {un.length} sentences classified read that the definition does not account for:"
      let kinds := un.map (·.detail)
      for n in kinds.eraseDups do IO.eprintln s!"  {kinds.count n} {n}"
      for r in un do IO.eprintln s!"  {r.toText}"
    return un.isEmpty
  let d ← match Parse.parse k with
    | .ok d => pure d
    | .error _ =>
      let rs := Parse.refusals k
      IO.eprintln s!"{koreFile}: KCore's parse refuses it: {rs.length} refusals"
      let reasons := rs.map (·.reason.name)
      for n in reasons.eraseDups do IO.eprintln s!"  {reasons.count n} {n}"
      for r in rs do IO.eprintln s!"  {r.toText}"
      -- the definition of the sentences read, when their stages pass, accounted for all the same
      match k.modules.getLast? with
      | some m => if let .ok d := Parse.finish m (Parse.scan m.sentences) then
          let _ ← reportUnconsumed d
      | none => pure ()
      return 1
  unless ← reportUnconsumed d do return 1
  -- the inert constructor axioms are the induced ones, the library modules a K installation's
  -- text holds sentences of are whole in it, no left side applies a function symbol, and the law
  -- axioms are the collections' (`Parse.accountRefusals`)
  let checked := Parse.accountRefusals k d
  unless checked.isEmpty do
    IO.eprintln s!"{koreFile}: {checked.length} refusals of the account:"
    for r in checked do IO.eprintln s!"  {r.toText}"
    return 1
  let c := d.sem
  -- `plain` decided natively: the packages of a plain definition state `plain_defn` (by the kernel)
  -- and the statements over `Step` and `Γ` that read it; the others take what `plain` would give as
  -- obligations and state the general forms (`headlineAt`)
  let plain := !asNotPlain && c.plain
  if core && (tie || wfMods) then
    IO.eprintln "--core states `coreOK` without `wf`: it goes with neither --tie nor --wf"; return 2
  if tie && !wf d then
    IO.eprintln s!"{koreFile}: not well formed: {(d.report.filter (!·.2)).map (·.1)}"; return 1
  let T := tables c
  -- `--core`: `coreOK` decided by its conjuncts, whether or not `okAll` and `wf` hold
  if core then
    let failing := (coreParts c T).filter (!·.2)
    unless failing.isEmpty do
      IO.eprintln s!"{koreFile}: `coreOK` fails: {failing.map (·.1)}"; return 1
  if !core && !c.okAll then
    IO.eprintln s!"{koreFile}: the core is not well formed (`okAll`): {(d.report.drop 1 |>.filter (!·.2)).map (·.1)}"; return 1
  let πs ← if tie then match perms d.emit k with
      | some πs => pure πs
      | none => IO.eprintln s!"{koreFile}: emit is not the KORE up to order"; return 1
    else pure []
  -- names
  let ownSyms := (List.range c.symNames.length).map fun i => (nRegSyms + i, decodeK (c.symNames.getD i ""))
  let ownSrts := (List.range c.sortNames.length).map fun i => (nRegSorts + i, c.sortNames.getD i "")
  let g : Ctx := { ns, d, T, symIds := uniqueNames ownSyms, srtIds := uniqueNames ownSrts }
  let kore := s!"{ns}/definition.kore"
  -- the package's own directory is generated as a whole: earlier output is removed (the user's
  -- modules live beside it, not in it)
  if ← (out / ns).pathExists then IO.FS.removeDirAll (out / ns)
  IO.FS.createDirAll (out / ns)
  IO.FS.writeFile (out / ns / "definition.kore") text
  -- a core outside `ok` (a rule matches a collection the executable matcher's theorems do not
  -- cover), or with a clause `clauseFixed` does not confirm (the executable evaluation's
  -- completeness reads coherence, shown from `clausesFixed`): its package is the core, its names and its tie, `wf` from
  -- `okAll` by the kernel, and subject reduction from `okAll` and `srReady`
  let exec := !core && c.ok && c.clausesFixed
  if core then pure ()
  else if !c.ok then IO.eprintln s!"{koreFile}: outside `ok` (the executable matcher's theorems): the package is the core, its tie and subject reduction"
  else if !exec then IO.eprintln s!"{koreFile}: {c.matchObligations.length} clauses `clauseFixed` does not confirm (the coherence the executable evaluation's completeness reads): the package is the core, its tie and subject reduction"
  let isPart := fun (m : String) (p : String) => m == s!"{ns}.{p}" || m.startsWith s!"{ns}.{p}."
  let factsAll := [s!"{ns}.Facts", s!"{ns}.Facts.Ok", s!"{ns}.Facts.Tables", s!"{ns}.Facts.SrReady", s!"{ns}.Facts.Lazy",
    s!"{ns}.Facts.Terminates"]
  let mut o : Out := { dir := out, skip := fun m =>
    if core then ![s!"{ns}.Core", s!"{ns}.Facts.Tables"].contains m
    else !exec &&
      ((isPart m "Facts" && !factsAll.contains m) || isPart m "Surface" || isPart m "Kinds" || isPart m "Certs") }
  let hasParams := c.params.any (·.impl.isNone)
  -- Core
  o ← o.write s!"{ns}.Core" (s!"import KcoreSpec\n" ++ hdr s!"The definition `{koreFile}` as a term." ++ s!"
namespace {ns}
open KCore

-- KCore's parse of `{kore}`, added as a term (`Tie` proves it is the kernel's parse)
definition_of defn from {kore.quote}

/-- The definition's semantics. -/
noncomputable abbrev c : Semantics := defn.sem

end {ns}
")
  -- Names
  let symLines := g.symIds.map fun (i, n) => s!"@[match_pattern, reducible] def {quoteId n} : KCore.Sym := {i}"
  let srtLines := g.srtIds.map fun (i, n) => s!"@[match_pattern, reducible] def {quoteId n} : KCore.Srt := {i}"
  let namesEq := s!"theorem names_ok :\n    ((List.range {c.symNames.length}).map fun i => c.symName ({nRegSyms} + i)) = {reprStr c.symNames} ∧\n    ((List.range {c.sortNames.length}).map fun i => c.sortName ({nRegSorts} + i)) = {reprStr c.sortNames} := by\n  decide +kernel"
  let cellPaths := cellPathsOf g
  o ← o.write s!"{ns}.Names" (s!"import {ns}.Core\nimport KcoreSpec.Invariant\n" ++ hdr "Readable names of the definition's own symbols and sorts (`names_ok` checks them against the KORE's), its rules' numbers, and its cells' positions." ++ s!"
namespace {ns}
open KCore

namespace Sym
{"\n".intercalate symLines}
end Sym

namespace Srt
{"\n".intercalate srtLines}
end Srt

{namesEq}

/-! ## Cells: each cell's position in a configuration, and its content there -/

{"\n".intercalate cellPaths}

end {ns}
")
  -- readable terms
  o ← genSyntax o ns g c s!"{ns}.Names"
  -- Facts: the lazy obligations, with and without the tie
  let lazyOccs := c.lazyOccs
  let lazyObl := c.lazyObligations
  let lazyList := String.join (lazyObl.map fun o => s!"\n- {lazyDesc d o}")
  let lazyRhs := if lazyObl.isEmpty then "[]" else s!"[\n  {",\n  ".intercalate (lazyObl.map g.lazyOcc)}]"
  o ← o.write s!"{ns}.Facts.Lazy" (s!"import {ns}.Names\n" ++ hdr s!"The arguments a short-circuiting evaluation may skip: {lazyOccs.length} occurrences, {lazyObl.length} not shown defined by `definedArg` (the lazy obligations)." ++ s!"
namespace {ns}
open KCore

/-- The occurrences of an argument a short-circuiting evaluation may skip whose value `definedArg`
does not show: each is a named obligation (`LazyOcc.Holds`, `KCore.Obligations`), that the argument
has a value wherever the occurrence is reached with argument 0 at the value that skips it.
{lazyObl.length} of the definition's {lazyOccs.length} occurrences{if lazyObl.isEmpty then "." else ":"}{lazyList} -/
theorem lazy_obligations : defn.sem.lazyObligations = {lazyRhs} := by kernel_rfl

end {ns}
")
  IO.println s!"\{\"lazyOccs\": {lazyOccs.length}, \"lazyObl\": [{", ".intercalate (lazyObl.map fun o => (lazyDesc d o).quote)}]}"
  -- Facts: tables
  o ← o.write s!"{ns}.Facts.Tables" (s!"import {ns}.Core\n" ++ hdr "The definition's tables (A5), computed and checked once." ++ s!"
namespace {ns}
open KCore

tables_of T from {kore.quote}

theorem T_eq : T = tables c := by decide +kernel

end {ns}
")
  if core then
    o ← genCore { o with skip := fun _ => false } ns c budgetNodes
    o ← genFnHyp o ns d false plain asNotPlain
    -- a clause's predicate is not `\top`: the package's statements take `FnHyp` itself
    unless c.clausesPreTop do
      IO.println "{\"fnHyp\": \"hypothesis\", \"why\": \"clausesPreTop false: a clause's predicate is not \\\\top, and the named facts give FnHyp only where every clause's predicate is \\\\top\"}"
    -- readable terms, with the symbols' and sorts' numbers (the package has no `Names`)
    if withSyntax then o ← genSyntax o ns { g with symIds := [], srtIds := [] } c s!"{ns}.Core"
    o ← o.write ns (s!"import {ns}.FnHyp\n" ++ hdr s!"The package of `{koreFile}`, deciding `coreOK` without `wf`, with what the deciders leave of `FnHyp`.")
    writeLakefile out ns
    IO.FS.writeFile (out / "modules.txt") ("\n".intercalate o.mods.toList ++ "\n")
    IO.println s!"\{\"ns\": \"{ns}\", \"core\": true, \"rules\": {c.rules.length}, \"fns\": {c.fns.length}, \"modules\": {o.mods.size}}"
    return 0
  -- Facts: ok, in a head and blocks of rules
  o ← o.write s!"{ns}.Facts.OkHead" (s!"import {ns}.Facts.Tables\n" ++ hdr "`ok`: declarations, subsorts, functions." ++ s!"
namespace {ns}
open KCore

theorem okHead : c.okHeadT T = true := by decide +kernel

end {ns}
")
  let sizes := (c.rules.map fun r => termSize r.lhs + termSize r.rhs).toArray
  let ruleBlocks := blocks sizes.size (fun i => sizes[i]!) budgetNodes
  let mut okMods : Array String := #[]
  for (lo, len) in ruleBlocks do
    let m := s!"{ns}.Facts.OkRules{lo}"
    okMods := okMods.push m
    o ← o.write m (s!"import {ns}.Facts.Tables\n" ++ hdr s!"`ok`: rules {lo} to {lo + len - 1}." ++ s!"
namespace {ns}
open KCore

theorem okRules{lo} : c.ruleRowsT T {lo} {len} = true := by decide +kernel

end {ns}
")
  o ← o.write s!"{ns}.Facts.SrReady" (s!"import {ns}.Facts.Tables\n" ++ hdr "`srReady`, from the tables." ++ s!"
namespace {ns}
open KCore

theorem srReadyT : c.srReadyT T = true := by decide +kernel

end {ns}
")
  o ← o.write s!"{ns}.Facts.MatchReady" (s!"import {ns}.Facts.Tables\n" ++ hdr "`matchReady`, from the tables." ++ s!"
namespace {ns}
open KCore

theorem matchReadyT : c.matchReadyT T = true := by decide +kernel

end {ns}
")
  o ← o.write s!"{ns}.Facts.Fixed" (s!"import {ns}.Core
" ++ hdr "`clausesFixed`: every clause's patterns fix its variables (`clauseFixed`); so no clause is a match obligation." ++ s!"
namespace {ns}
open KCore

theorem clausesFixed : c.clausesFixed = true := by decide +kernel

end {ns}
")
  o ← o.write s!"{ns}.Facts.Uses" (s!"import {ns}.Core\nimport KcoreSpec.Features\n" ++ hdr "The features the definition uses." ++ s!"
namespace {ns}
open KCore

theorem uses_eq : c.uses defn.pres = {(reprStr (c.uses d.pres)).replace "\n" " "} := by decide +kernel

end {ns}
")
  -- determinism: paths, index, obligations (the pairs the decider does not confirm), row blocks
  let paths := choosePaths c T
  let ix := Det.DetIndex.build c T paths
  let n := c.rules.length
  let (badUniq, _) := Det.detReport c T ix
  let ovl := ((Det.detIdx ix n).filter fun p => !Det.detCond c T p).eraseDups
  let cp := compatPairs c T paths
  let ruleLbl := fun (i : Nat) => match (d.pres.rules[i]?).bind (·.label) with
    | some l => s!" (`{l}`)" | none => ""
  let mut detMods : Array String := #[]
  let mut rowBlocks : List (Nat × Nat) := []
  if n > 0 then
    let oblDoc := if ovl.isEmpty then " (none). " else ":\n" ++ String.join (ovl.map fun (i, j) =>
      if i == j then s!"- ({i}, {i}): rule {i}{ruleLbl i}, whose match is not shown to fix its right-hand side\n"
      else s!"- ({i}, {j}): rules {i}{ruleLbl i} and {j}{ruleLbl j}, not shown apart\n")
    o ← o.write s!"{ns}.Facts.DetIndex" (s!"import {ns}.Facts.Tables\n" ++ hdr s!"The determinism index (keys at {paths.length} paths; {cp.length} pairs of rules reach the decision of `apart`) and the pairs of rules listed as obligations." ++ s!"
namespace {ns}
open KCore

det_index_of ix from {kore.quote} at {reprStr paths}

/-- The pairs of rules the decider (`Det.detCond`) does not confirm: determinism's obligations{oblDoc}-/
def ovl : List (Nat × Nat) := {reprStr ovl}

theorem idx_ok : Det.idxOK c T ix = true := by decide +kernel

end {ns}
")
    rowBlocks := blocks n (fun i => 1 + (cp.filter (·.1 == i)).length) budgetPairs
    for (lo, len) in rowBlocks do
      let m := s!"{ns}.Facts.DetRows{lo}"
      detMods := detMods.push m
      o ← o.write m (s!"import {ns}.Facts.DetIndex\n" ++ hdr s!"Determinism's decision: the pairs of rows {lo} to {lo + len - 1}." ++ s!"
namespace {ns}
open KCore

theorem detRows{lo} : Kind.decides (Det.detCond c T) ovl (Kind.rows (Det.detPairs ix c.rules.length) {lo} {len}) = true := by
  decide +kernel

end {ns}
")
  -- Facts: joined
  let okJoin := Id.run do
    let mut acc := s!"okRules0"
    let mut lines : Array String := #[]
    for (lo, len) in ruleBlocks.drop 1 do
      let nm := s!"okRules_upto{lo + len}"
      lines := lines.push s!"private theorem {nm} : c.ruleRowsT T 0 {lo + len} = true := ruleRowsT_join {acc} okRules{lo} rfl rfl"
      acc := nm
    return ("\n".intercalate lines.toList, acc)
  let factImports := [s!"{ns}.Facts.OkHead", s!"{ns}.Facts.SrReady", s!"{ns}.Facts.MatchReady", s!"{ns}.Facts.Fixed", s!"{ns}.Facts.Lazy"] ++ okMods.toList ++ detMods.toList
  let okRows := if sizes.size == 0 then "theorem okRules : c.ruleRowsT T 0 c.rules.length = true := by decide +kernel"
    else s!"{okJoin.1}\ntheorem rules_length : c.rules.length = {sizes.size} := by decide +kernel\ntheorem okRules : c.ruleRowsT T 0 c.rules.length = true := ruleRowsT_all rules_length {okJoin.2}"
  let lens := reprStr (rowBlocks.map (·.2))
  let coherentPart := if c.agreeObligations.isEmpty then s!"
/-- `fnExclusiveOK` confirms every function's equations: no agreement is named. -/
theorem agree_nil : c.agreeObligations = [] := agreeObligations_of_T T_eq (by decide +kernel)

/-- **The clauses of one priority are coherent** (`CoherentAll`): every clause is fixed and every
function's equations are confirmed. The executable evaluation's completeness reads it. -/
theorem coherent : CoherentAll c := Det.coherentAll_of_nil ok srReady matchReady clausesFixed agree_nil

/-- `coherent` for every interpretation of the parameters. -/
theorem coherent_withHooks (H : HookParams) : CoherentAll (c.withHooks H) :=
  Det.coherentAll_of_nil ((Semantics.ok_withHooks c H).trans ok) ((Semantics.srReady_withHooks c H).trans srReady)
    ((Semantics.matchReady_withHooks c H).trans matchReady) ((Semantics.clausesFixed_withHooks c H).trans clausesFixed)
    ((Semantics.agreeObligations_withHooks c H).trans agree_nil)
" else s!"
/-- **The clauses of one priority are coherent** (`CoherentAll`), given the named agreements: every
clause is fixed. -/
theorem coherent_withHooks (H : HookParams)
    (hag : ∀ f ∈ c.agreeObligations, ∀ fn, (c.withHooks H).lookupFn f = some fn → ClausesAgree (c.withHooks H) fn) :
    CoherentAll (c.withHooks H) :=
  Det.coherentAll_of_fixed ((Semantics.ok_withHooks c H).trans ok) ((Semantics.srReady_withHooks c H).trans srReady)
    ((Semantics.matchReady_withHooks c H).trans matchReady) ((Semantics.clausesFixed_withHooks c H).trans clausesFixed)
    (by rw [Semantics.agreeObligations_withHooks]; exact hag)
"
  let detPart := if n > 0 then s!"
/-- Determinism's decision by blocks of rows: at every pair of a block, the decider confirms it or
`ovl` lists it. -/
theorem det_blocks : ∀ b ∈ Kind.blocks (Det.detPairs ix c.rules.length) 0 {lens},
    Kind.decides (Det.detCond c T) ovl b = true :=
  {forallList (rowBlocks.map fun (lo, _) => s!"detRows{lo}")}

/-- The blocks are determinism's indices. -/
theorem det_split : Det.detIdx ix c.rules.length = (Kind.blocks (Det.detPairs ix c.rules.length) 0 {lens}).flatten :=
  Kind.rows_blocks_of (rules_length.trans rfl)
" else ""
  if !exec then
    o ← o.write s!"{ns}.Facts.Ok" (s!"import {ns}.Core\nimport KcoreSpec.Tie\n" ++
      hdr "`okAll`, by the kernel: the core is outside `ok`, which the executable matcher's theorems read." ++ s!"
namespace {ns}
open KCore

theorem okAll : c.okAll = true := by decide +kernel

end {ns}
")
  if exec then o ← o.write s!"{ns}.Facts.Ok" (String.join ((s!"{ns}.Facts.OkHead" :: okMods.toList).map (s!"import {·}\n")) ++
    hdr "`ok`, joined from its head and its blocks of rules (the tie's `wf` reads it too)." ++ s!"
namespace {ns}
open KCore

{okRows}

theorem ok : c.ok = true := ok_of_T T_eq (okT_of_rows okHead okRules)

end {ns}
")
  -- subject reduction outside `ok`: from `okAll` and `srReady`, for every interpretation of the
  -- parameters when there are any
  let srAll := if hasParams then s!"
/-- **Subject reduction**, for every interpretation of the parameters: a rule's right-hand side,
evaluated under a substitution of the rule's variable sorts, is a configuration when defined. -/
theorem rhs_sorted (H : HookParams) \{r : Rule} (hr : r ∈ c.rules) \{σ : Subst}
    (hσ : (c.withHooks H).WellSorted r.vars σ) \{v : GroundTerm}
    (he : EvalTerm (c.withHooks H) σ r.rhs (some v)) : (c.withHooks H).sortOf v = some topCellSort :=
  rhs_sorted_all_withHooks okAll srReady (Semantics.ovlCase_of (by decide +kernel)) H hr hσ he

/-- So every application of a rule to a configuration is a step: a match under a well-sorted σ, a
true `requires`, the predicate `pre` holding, a defined right-hand side, a true `ensures`, the
predicate `post` holding, and no rule of a smaller priority applying. -/
theorem step_of_apply (H : HookParams) \{r : Rule} (hr : r ∈ c.rules) \{x : Config (c.withHooks H)}
    \{σ : Subst} (hσ : (c.withHooks H).WellSorted r.vars σ) (hm : PatVal (c.withHooks H) σ r.lhs x.val)
    (hreq : ∀ t, r.req = some t → EvalTerm (c.withHooks H) σ t (some (bool true)))
    (hpre : Holds (c.withHooks H) r.vars.length σ r.pre true)
    \{v : GroundTerm} (he : EvalTerm (c.withHooks H) σ r.rhs (some v))
    (hens : ∀ t, r.ens = some t → EvalTerm (c.withHooks H) σ t (some (bool true)))
    (hpost : Holds (c.withHooks H) r.vars.length σ r.post true)
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies (c.withHooks H) r' x.val) :
    Step (c.withHooks H) x ⟨v, {ns}.rhs_sorted H hr hσ he⟩ :=
  step_of_apply_all_withHooks okAll srReady (Semantics.ovlCase_of (by decide +kernel)) H hr hσ hm hreq hpre he hens hpost hprio" else s!"
/-- **Subject reduction**: a rule's right-hand side, evaluated under a substitution of the rule's
variable sorts, is a configuration when defined. -/
theorem rhs_sorted \{r : Rule} (hr : r ∈ c.rules) \{σ : Subst} (hσ : c.WellSorted r.vars σ)
    \{v : GroundTerm} (he : EvalTerm c σ r.rhs (some v)) : c.sortOf v = some topCellSort :=
  rhs_sorted_all okAll srReady (Semantics.ovlCase_of (by decide +kernel)) hr hσ he

/-- So every application of a rule to a configuration is a step: a match under a well-sorted σ, a
true `requires`, the predicate `pre` holding, a defined right-hand side, a true `ensures`, the
predicate `post` holding, and no rule of a smaller priority applying. -/
theorem step_of_apply \{r : Rule} (hr : r ∈ c.rules) \{x : Config c} \{σ : Subst}
    (hσ : c.WellSorted r.vars σ) (hm : PatVal c σ r.lhs x.val)
    (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c r.vars.length σ r.pre true)
    \{v : GroundTerm} (he : EvalTerm c σ r.rhs (some v))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hpost : Holds c r.vars.length σ r.post true)
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val) :
    Step c x ⟨v, {ns}.rhs_sorted hr hσ he⟩ :=
  step_of_apply_all okAll srReady (Semantics.ovlCase_of (by decide +kernel)) hr hσ hm hreq hpre he hens hpost hprio"
  if !exec then o ← o.write s!"{ns}.Facts" (s!"import {ns}.Facts.Ok\nimport {ns}.Facts.SrReady\nimport {ns}.Facts.Lazy\nimport KcoreSpec.Params\n" ++
    hdr "The definition's facts, joined: `okAll` and `srReady` (the core is outside `ok`, which the executable matcher's theorems read), and subject reduction from them." ++ s!"
namespace {ns}
open KCore

theorem srReady : c.srReady = true := srReady_of_T T_eq srReadyT
{srAll}

end {ns}
")
  if exec then o ← o.write s!"{ns}.Facts" (String.join ((s!"{ns}.Facts.Ok" :: factImports).map (s!"import {·}\n")) ++ "import KcoreSpec.DetSound\nimport KcoreSpec.FnExclusive\nimport KcoreSpec.Params\n" ++
    hdr "The definition's facts, joined: `ok`, `srReady`, `matchReady`, `clausesFixed` (the readable conditions the generic theorems take), the coherence of the clauses of one priority, and determinism's condition." ++ s!"
namespace {ns}
open KCore

theorem srReady : c.srReady = true := srReady_of_T T_eq srReadyT
theorem matchReady : c.matchReady = true := matchReady_of_T T_eq matchReadyT
{coherentPart}
{detPart}
end {ns}
")
  -- Facts: termination, with and without the tie
  let termNamed := c.orderObligations ++ d.cert.obligations c
  let okAllT := if exec then "(Semantics.okAll_of_ok ok)" else "okAll"
  -- with an open generator the `…_withHooks` forms do not apply (they ask that no parameter be
  -- raw): the base lemmas at `c.withHooks H`, the data's facts carried by their equations, and
  -- `RightHeld` there from `rightValued`
  let rawF := c.params.any (·.raw)
  let okW := s!"((Semantics.okAll_withHooks c H).trans {okAllT})"
  let srW := "((Semantics.srReady_withHooks c H).trans srReady)"
  let ovW := "(Semantics.ovlCase_withHooks (Semantics.ovlCase_of (by decide +kernel)) H)"
  let rhW := "(Semantics.rightHeld_withHooks_of_valued (by decide +kernel) H)"
  let termNilPf := if rawF then s!"terminates_of_nil {okW} {srW} {ovW} defn.cert
    (by rw [orderObligations_withHooks, certObligations_withHooks]; exact named_terminates) {rhW}"
    else s!"terminates_of_nil_withHooks {okAllT} srReady (Semantics.ovlCase_of (by decide +kernel)) defn.cert named_terminates H"
  let termOrdPf := if rawF then s!"terminates_of_order {okW} {srW} {ovW} defn.cert
    (by rw [orderObligations_withHooks, certObligations_withHooks, named_terminates]; exact hnamed) {rhW}"
    else s!"terminates_of_order_withHooks {okAllT} srReady (Semantics.ovlCase_of (by decide +kernel)) defn.cert H (by rw [named_terminates]; exact hnamed)"
  let termHooks := if termNamed.isEmpty then s!"

/-- Every function terminates, for every interpretation of the parameters. -/
theorem terminates_withHooks (H : HookParams) : ∀ f, Terminates (c.withHooks H) f :=
  {termNilPf}" else s!"

/-- Every function terminates, for every interpretation of the parameters, given the named ones'
termination under it. -/
theorem terminates_withHooks (H : HookParams)
    (hnamed : ∀ g ∈ ({termNamed} : List Sym), Terminates (c.withHooks H) g) : ∀ f, Terminates (c.withHooks H) f :=
  {termOrdPf}"
  let termMain := if termNamed.isEmpty then s!"
/-- **Every function terminates** (`KCore.Terminates`: a result at every argument list of its
argument sorts), the sort predicates among them: no function is named. -/
theorem terminates : ∀ f, Terminates c f :=
  terminates_of_nil {okAllT} srReady (Semantics.ovlCase_of (by decide +kernel)) defn.cert named_terminates" else s!"
/-- **Every function terminates** (`KCore.Terminates`: a result at every argument list of its
argument sorts), the sort predicates among them, given the named functions' termination. -/
theorem terminates (hnamed : ∀ g ∈ ({termNamed} : List Sym), Terminates c g) : ∀ f, Terminates c f :=
  terminates_of_order {okAllT} srReady (Semantics.ovlCase_of (by decide +kernel)) defn.cert (by rw [named_terminates]; exact hnamed)"
  let totNamed := c.totalObligations
  let termHyp := if termNamed.isEmpty then "" else s!" (hnamed : ∀ g ∈ ({termNamed} : List Sym), Terminates c g)"
  let termArg := if termNamed.isEmpty then "terminates" else "(terminates hnamed)"
  let termHypH := if termNamed.isEmpty then "" else s!"
    (hnamed : ∀ g ∈ ({termNamed} : List Sym), Terminates (c.withHooks H) g)"
  let termArgH := if termNamed.isEmpty then "(terminates_withHooks H)" else "(terminates_withHooks H hnamed)"
  let totMain := if totNamed.isEmpty then s!"
/-- **Every function declared `[total]` is total** (`KCore.Total`: a value at every argument list
of its argument sorts), the sort predicates among them: none is named. -/
theorem totals{termHyp} : ∀ f fn, c.lookupFn f = some fn → fn.total = true → Total c f :=
  totals_of_nil {okAllT} srReady (Semantics.ovlCase_of (by decide +kernel)) {termArg} named_totals" else s!"
/-- **Every function declared `[total]` is total** (`KCore.Total`: a value at every argument list
of its argument sorts), the sort predicates among them, given the named ones' totality. -/
theorem totals{termHyp} (htot : ∀ g ∈ ({totNamed} : List Sym), Total c g) :
    ∀ f fn, c.lookupFn f = some fn → fn.total = true → Total c f :=
  totals_of_order {okAllT} srReady (Semantics.ovlCase_of (by decide +kernel)) {termArg} (by rw [named_totals]; exact htot)"
  let totNilPf := if rawF then s!"totals_of_nil {okW} {srW} {ovW} {termArgH}
    ((Semantics.totalObligations_withHooks c H).trans named_totals) {rhW}"
    else s!"totals_of_nil_withHooks {okAllT} srReady (Semantics.ovlCase_of (by decide +kernel)) H {termArgH} named_totals"
  let totOrdPf := if rawF then s!"totals_of_order {okW} {srW} {ovW} {termArgH}
    (by rw [Semantics.totalObligations_withHooks, named_totals]; exact htot) {rhW}"
    else s!"totals_of_order_withHooks {okAllT} srReady (Semantics.ovlCase_of (by decide +kernel)) H {termArgH} (by rw [named_totals]; exact htot)"
  let totHooks := if totNamed.isEmpty then s!"

/-- Every function declared `[total]` is total, for every interpretation of the parameters. -/
theorem totals_withHooks (H : HookParams){termHypH} :
    ∀ f fn, (c.withHooks H).lookupFn f = some fn → fn.total = true → Total (c.withHooks H) f :=
  {totNilPf}" else s!"

/-- Every function declared `[total]` is total, for every interpretation of the parameters, given
the named ones' totality under it. -/
theorem totals_withHooks (H : HookParams){termHypH}
    (htot : ∀ g ∈ ({totNamed} : List Sym), Total (c.withHooks H) g) :
    ∀ f fn, (c.withHooks H).lookupFn f = some fn → fn.total = true → Total (c.withHooks H) f :=
  {totOrdPf}"
  o ← o.write s!"{ns}.Facts.Terminates" (s!"import {ns}.Facts\nimport KcoreSpec.Terminates\nimport KcoreSpec.Totals\n" ++ hdr s!"Termination and totality of the functions: {termNamed.length} named for termination (calling a later function, or a self call the certificate does not show to decrease), {totNamed.length} `[total]` functions named for totality (not confirmed by `totalOK`)." ++ s!"
namespace {ns}
open KCore

/-- The functions whose termination is named (`orderObligations`, the certificate's
`obligations`: the first conjunct of `KCore.Obligations`). -/
theorem named_terminates : defn.sem.orderObligations ++ defn.cert.obligations defn.sem = {termNamed} := by
  decide +kernel
{termMain}{termHooks}

/-- The functions declared `[total]` whose totality is named (`totalObligations`: the second
conjunct of `KCore.Obligations`). -/
theorem named_totals : defn.sem.totalObligations = {totNamed} := by decide +kernel
{totMain}{totHooks}

end {ns}
")
  -- Certificates: krust's runs, each checked by the kernel against `Step`. With an open generator
  -- (a `raw` parameter) none: `checkRun_sound` and `stuckCheck_sound` take `∀ k ∈ c.params,
  -- k.raw = false`, false there (a raw application's sort is read from the interpretation, which
  -- the checks do not evaluate)
  let rawCerts := c.params.any (·.raw)
  if rawCerts && !certs.isEmpty then
    IO.eprintln s!"{koreFile}: a parameter is an open generator: no run certificate and no stuckness theorem ({certs.length} runs not written)"
  for (nm, path) in (if rawCerts then [] else certs) do
    match ← readCert c d.pres path with
    | .error e => IO.eprintln e; return 1
    | .ok (start, steps, stuck) =>
      let final := (steps.getLast?.map (·.2)).getD start
      let stepsSrc := ",\n  ".intercalate (steps.map fun (i, t) => s!"({i}, {g.ground t})")
      let stuckPart := if stuck then s!"
theorem {nm}_stuck : stuckCheck c {certFuel} {nm}_final = true := by decide +kernel

/-- The run's last configuration has no successor, for every interpretation of the parameters. -/
theorem {nm}_ends{if c.agreeObligations.isEmpty then "" else " (hco : ∀ H : HookParams, CoherentAll (c.withHooks H))"} (H : HookParams) (hf : (c.withHooks H).sortOf {nm}_final = some topCellSort) :
    ∀ y, ¬ Step (c.withHooks H) ⟨_, hf⟩ y :=
  stuckCheck_sound ok srReady matchReady H {if c.agreeObligations.isEmpty then "(coherent_withHooks H)" else "(hco H)"} (x := ⟨_, hf⟩) {nm}_stuck
" else ""
      o ← o.write s!"{ns}.Certs.{nm}" (s!"import {ns}.Names\nimport {ns}.Facts\nimport KcoreSpec.Cert\n" ++ hdr s!"krust's run `{path}` ({steps.length} steps{if stuck then ", then stuck" else ""}) as a certificate: each step names its rule (krust's rule id, read as the rule's number) and the configuration reached, and the kernel checks it against `Step`, for every interpretation of the parameters (the check evaluates no parameter whose value is the interpretation's)." ++ s!"
namespace {ns}.Certs
open KCore KCore.Cert {ns}

def {nm}_start : GroundTerm := {g.ground start}
def {nm}_final : GroundTerm := {g.ground final}
def {nm}_steps : List (Nat × GroundTerm) := [
  {stepsSrc}]

theorem {nm}_run : checkRun c {certFuel} {nm}_start {nm}_steps {nm}_final = true := by decide +kernel

/-- krust's run is a run of `Step`, for every interpretation of the parameters. -/
theorem {nm}_reaches (H : HookParams) : ∃ (hs : (c.withHooks H).sortOf {nm}_start = some topCellSort)
    (hf : (c.withHooks H).sortOf {nm}_final = some topCellSort),
    Reach (Step (c.withHooks H)) ⟨_, hs⟩ ⟨_, hf⟩ :=
  checkRun_sound ok srReady matchReady {nm}_run H
{stuckPart}
end {ns}.Certs
")
  let nPkg := o.mods.size
  if tie then
    match ← genTie o koreFile ns kore k d πs exec budgetSents budgetScan budgetProds budgetRules budgetEvents budgetClauses plain with
    | some o' => o := o'
    | none => return 1
  -- what the deciders leave of `FnHyp`, after `NS.Sound` (`coreOK_defn`)
  if tie then o ← genFnHyp o ns d true plain asNotPlain
  let tieMods := o.mods.extract nPkg o.mods.size
  o := { o with mods := o.mods.extract 0 nPkg }
  -- without the tie, `wf defn` and soundness and completeness from it, when asked (`--wf`), and
  -- what the deciders leave of `FnHyp`
  if !tie && wfMods then
    if wf d then
      o ← genWf o ns "Wf" d exec plain
      o ← genFnHyp o ns d true plain asNotPlain
    else IO.eprintln s!"{koreFile}: not well formed: {(d.report.filter (!·.2)).map (·.1)}; no Wf or Sound modules"
  -- Surface
  let ruleLemmas := (c.rules.zipIdx.map fun (r, i) =>
    s!"kernel_rfl rule{i} : c.rules[{i}]? = some\n  {g.rule r}")
  let fnLemmas := c.fns.flatMap fun f =>
    let nm := (g.symIds.lookup f.label).getD (toString f.label)
    let base := s!"kernel_rfl {quoteId ("fn_" ++ nm ++ "_sig")} : (c.lookupFn {g.sym f.label}).map (fun fn => (fn.args, fn.result, fn.clauses.length)) = some ({g.srts f.args}, {g.srt f.result}, {f.clauses.length})"
    base :: (f.clauses.zipIdx.map fun (cl, j) =>
      s!"kernel_rfl {quoteId ("fn_" ++ nm ++ s!"_{j}")} : (c.lookupFn {g.sym f.label}).bind (·.clauses[{j}]?) = some\n  {g.clause cl}")
  let nRules := c.rules.length
  let rulesCases := s!"/-- Every rule is one of the rules above: a case split gives one case per rule, whose data is its
lemma's. -/
theorem rules_cases \{r : Rule} (h : r ∈ c.rules) :
    {if nRules == 0 then "False" else " ∨\n    ".intercalate ((List.range nRules).map (s!"c.rules[{·}]? = some r"))} :=
  atOneOf_of_mem (n := {nRules}) (by decide +kernel) h"
  let agreeEmpty := c.agreeObligations.isEmpty
  let coBinderH := if agreeEmpty then "" else " (hco : ∀ H : HookParams, CoherentAll (c.withHooks H))"
  let coH := if agreeEmpty then "(coherent_withHooks H)" else "(hco H)"
  let stepIff := if hasParams then s!"
/-- The executable step lists exactly `Step`'s successors, for every interpretation of the parameters. -/
theorem step_iff{coBinderH} (H : HookParams) (x y : Config (c.withHooks H)) :
    Step (c.withHooks H) x y ↔ ∃ n, (Exec.successorsN (c.withHooks H) n x.val).any (Exec.same · y.val) = true :=
  Exec.step_iff_all ok srReady matchReady H {coH} x y" else s!"
/-- The executable step lists exactly `Step`'s successors. -/
theorem step_iff{if agreeEmpty then "" else " (hco : CoherentAll c)"} (x y : Config c) :
    Step c x y ↔ ∃ n, (Exec.successorsN c n x.val).any (Exec.same · y.val) = true :=
  Exec.step_iff_of_ok c ok srReady matchReady {if agreeEmpty then "coherent" else "hco"} x y"
  let minPrio := ((c.rules.map (·.prio)).min?).getD 0
  let fireHooks := if hasParams then s!"
/-- `fireFacts` for every interpretation of the parameters. -/
instance fireFacts_withHooks (H : HookParams) : FireFacts (c.withHooks H) :=
  ⟨(Semantics.ok_withHooks c H).trans ok, (Semantics.srReady_withHooks c H).trans srReady,
    (Semantics.matchReady_withHooks c H).trans matchReady, {minPrio}, prio_floor⟩
" else ""
  o ← o.write s!"{ns}.Surface" (s!"import {ns}.Facts\nimport {ns}.Names\nimport KcoreSpec.Params\nimport KcoreSpec.SymbolicLemmas\nimport KcoreSpec.Fire\n" ++ hdr "`step_iff` for this definition, its rules and function clauses as data, and the case split of a step by rule." ++ s!"
namespace {ns}
open KCore
{stepIff}

/-- A step is by one of the rules, which applies to the configuration. -/
theorem step_cases \{x y : Config c} (h : Step c x y) :
    ∃ i, ∃ hi : i < c.rules.length, Det.Applies c c.rules[i] x.val := by
  cases h with
  | rule r mem σ hσ hm hq _ _ =>
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem mem
    exact ⟨i, hi, σ, hσ, hm, hq⟩

/-! ## The rules -/

{"\n\n".intercalate ruleLemmas}

{rulesCases}

/-! ## The functions: signature, then each clause -/

{"\n\n".intercalate fnLemmas}

/-! ## What a step by `fire` reads of the definition -/

/-- No rule has a priority below {minPrio}: a rule of priority {minPrio} waits on no other. -/
theorem prio_floor : c.rules.all (fun r => Nat.ble {minPrio} r.prio) = true := by decide +kernel

/-- The facts `fire` (KcoreSpec/FireTac.lean) reads of the definition (`KCore.FireFacts`). -/
instance fireFacts : FireFacts c := ⟨ok, srReady, matchReady, {minPrio}, prio_floor⟩
{fireHooks}
end {ns}
")
  -- Kinds: determinism, indexed by pairs of rules (`Det.kindAll`), decided by blocks of rows
  let hmo := if agreeEmpty then "coherent_withHooks" else "hco"
  let mut kindMods : Array String := #[]
  if n > 0 then
    let detOn := s!"
/-- **Determinism where `Inv` holds, for every interpretation of the parameters**, given the
obligations `ovl` where `Inv` holds: at each listed pair of rules, two steps from a configuration
where `Inv` holds, by its two rules, reach one configuration. -/
theorem deterministic_on{coBinderH} (H : HookParams) (Inv : Config (c.withHooks H) → Prop)
    (ho : ∀ p ∈ ovl, Det.JoinsOn (c.withHooks H) Inv p.1 p.2) :
    ∀ x y y' : Config (c.withHooks H), Inv x → Step (c.withHooks H) x y → Step (c.withHooks H) x y' → y = y' :=
  Kind.of_blocks (Det.kindAll matchReady T_eq idx_ok H Inv)
    (Det.deciderAll ok srReady {hmo} H Inv)
    ovl _ det_split det_blocks ho
"
    let stmt := if ovl.isEmpty && !hasParams then s!"
/-- **The definition is deterministic, for every interpretation of the parameters.** -/
theorem deterministic{coBinderH} (H : HookParams) \{x y y' : Config (c.withHooks H)} (h : Step (c.withHooks H) x y)
    (h' : Step (c.withHooks H) x y') : y = y' :=
  deterministic_on{if agreeEmpty then "" else " hco"} H (fun _ => True) (fun _ h => nomatch h) x y y' trivial h h'" else s!"
/-- **Determinism up to the listed pairs, for every interpretation of the parameters.** The pairs
`ovl` are the obligations, here in the conclusion: where no listed pair's two rules both apply, a
configuration has one successor. -/
theorem deterministic_except{coBinderH} (H : HookParams) \{x y y' : Config (c.withHooks H)}
    (h : Step (c.withHooks H) x y) (h' : Step (c.withHooks H) x y') :
    y = y' ∨ ∃ i j, ((i, j) ∈ ovl ∨ (j, i) ∈ ovl) ∧ ∃ (hi : i < c.rules.length) (hj : j < c.rules.length),
      Det.Applies (c.withHooks H) c.rules[i] x.val ∧ Det.Applies (c.withHooks H) c.rules[j] x.val :=
  Det.deterministic_except_of_on (deterministic_on{if agreeEmpty then "" else " hco"} H) h h'"
    o ← o.write s!"{ns}.Kinds.Det" (s!"import {ns}.Facts\nimport KcoreSpec.Params\n" ++ hdr s!"Determinism{if ovl.isEmpty then "" else s!", with {ovl.length} pairs of rules as obligations"}." ++ s!"
namespace {ns}
open KCore
{detOn}{stmt}

end {ns}
")
    kindMods := kindMods.push s!"{ns}.Kinds.Det"
  -- Kinds: the counter cell's frame
  let ctr := ctrPathOf d.pres
  let ctrObl := (c.rules.zipIdx.filter fun (r, _) => !frameOK c ctr r).map (·.2)
  o ← o.write s!"{ns}.Kinds.Counter" (s!"import {ns}.Facts\nimport {ns}.Names\nimport KcoreSpec.Invariant\n" ++ hdr s!"The counter cell's frame: every step keeps it, and its value is an invariant of every run, but by the rules listed (obligations: {ctrObl.length}); for every interpretation of the parameters." ++ s!"
namespace {ns}
open KCore

/-- The rules whose step may change the counter cell (a fresh value): obligations. -/
def counterObl : List Nat := {reprStr ctrObl}

theorem counterFrame : Kind.decides (Kind.listCond c.rules (frameOK c counterPath)) counterObl
    (List.range c.rules.length) = true := by decide +kernel

/-- **Every step keeps the counter cell**, for every interpretation of the parameters, given the
listed rules do. -/
theorem counter_kept (H : HookParams)
    (ho : ∀ i ∈ counterObl, ∀ r, c.rules[i]? = some r → RuleSteps (c.withHooks H) r (Frame counterPath)) :
    ∀ x y : Config (c.withHooks H), Step (c.withHooks H) x y → Frame counterPath x.val y.val :=
  Kind.of_decided (stepsKindAll c H (Frame counterPath))
    (stepsDecider (cond := (frameOK · counterPath)) (fun H r => frameOK_withHooks c H counterPath r)
      (fun H r h => frame_sound (c := c.withHooks H) counterPath r h) H) counterObl counterFrame ho

/-- The counter cell holds `ctr`. -/
def counterHolds (ctr v : GroundTerm) : Prop := v.atPath counterPath = some ctr

/-- **The counter cell's value is an invariant**, for every interpretation of the parameters: it
holds where it holds initially, and every step keeps it, given the listed rules do. -/
theorem counter_invariant (H : HookParams) (ctr : GroundTerm)
    (ho : ∀ i ∈ counterObl, ∀ r, c.rules[i]? = some r →
      RuleSteps (c.withHooks H) r (fun x y => counterHolds ctr x → counterHolds ctr y)) :
    Invariant (c.withHooks H) (fun x => counterHolds ctr x.val) (fun x => counterHolds ctr x.val) :=
  ⟨fun _ h => h, fun x y hx hs => Kind.of_decided
    (stepsKindAll c H (fun x y => counterHolds ctr x → counterHolds ctr y))
    (stepsDecider (cond := (frameOK · counterPath)) (fun H r => frameOK_withHooks c H counterPath r)
      (fun H r h => frame_inv_sound (c := c.withHooks H) counterPath (· = some ctr) r h) H)
    counterObl counterFrame ho x y hs hx⟩

/-- **Every configuration a run reaches has the counter cell's starting value**, for every
interpretation of the parameters, given the listed rules keep it. -/
theorem counter_reach (H : HookParams) (ctr : GroundTerm)
    (ho : ∀ i ∈ counterObl, ∀ r, c.rules[i]? = some r →
      RuleSteps (c.withHooks H) r (fun x y => counterHolds ctr x → counterHolds ctr y))
    \{x y : Config (c.withHooks H)} (hx : counterHolds ctr x.val) (hr : Cert.Reach (Step (c.withHooks H)) x y) :
    counterHolds ctr y.val :=
  (counter_invariant H ctr ho).reach hx hr

end {ns}
")
  kindMods := kindMods.push s!"{ns}.Kinds.Counter"
  -- Kinds: noninterference for the cells `--high` names and the map cells `--keyed` names
  -- (KcoreSpec/NICells.lean)
  if !high.isEmpty || !keyed.isEmpty then
    let H := NI.highOf d.pres high ++ NI.keyedOf d.pres keyed
    if high.any (fun x => (NI.highOf d.pres [x]).isEmpty) || keyed.any (fun x => (NI.keyedOf d.pres [x]).isEmpty) then
      IO.eprintln s!"{koreFile}: --high or --keyed names no cell of the configuration"; return 1
    if !(n > 0 && !hasParams) then
      IO.eprintln s!"{koreFile}: --high and --keyed need the determinism theorem (no parameters)"; return 1
    let niObl := (c.rules.zipIdx.filter fun (r, _) => !NI.cellsCond c H r).map (·.2)
    let why := fun (r : Rule) =>
      let ks := (NI.hiVars H r.lhs).map (·.1)
      let fails := [("the left-hand side reads a secret position", !NI.lhsOK c H r.lhs),
        ("a secret variable occurs twice", !NI.nodupB ks),
        ("a secret variable occurs in the public part", (NI.loVars H r.lhs).any ks.contains),
        ("the requires reads a secret variable", match r.req with | some t => (varOccs t).any ks.contains | none => false),
        ("the right-hand side moves or computes on a secret", !NI.rhsOK c (NI.hiVars H r.lhs) H r.rhs),
        ("the ensures reads a secret variable", !NI.ensOK H r),
        ("a rule of smaller priority reads a secret position", !c.rules.all fun r' => !decide (r'.prio < r.prio) || NI.appOK c H r')]
      "; ".intercalate ((fails.filter (·.2)).map (·.1))
    let lbl := fun (i : Nat) => (match (d.pres.rules[i]?).bind (·.label) with
      | some l => s!" (`{l}`)" | none => "") ++ (match c.rules[i]? with | some r => s!": {why r}" | none => "")
    IO.println s!"\{\"niObl\": [{", ".intercalate (niObl.map fun i => s!"\{\"rule\": {i}, \"why\": {(lbl i).quote}}")}]}"
    -- With determinism's obligations, the statement is relative to an invariant `Inv` of the
    -- configurations where `Init` holds (`NI.cellsKindOnAll`): each listed pair's obligation where
    -- `Inv` holds (`deterministic_on`), and each listed rule's unwinding where `Inv` holds, are the
    -- premises.
    let onInv := !ovl.isEmpty
    let unw := if onInv then "NI.RuleUnwindsOn (c.withHooks H) Inv" else "NI.RuleUnwinds (c.withHooks H)"
    let prem := String.join (niObl.map fun i =>
      s!"\n    (h{i} : ∀ r, c.rules[{i}]? = some r → {unw} (NI.LowEq (c.withHooks H) lo high) r)")
    let ho := forallList (niObl.map (s!"h{·}"))
    let ovPrem := String.join (ovl.map fun (i, j) =>
      s!"\n    (ov{i}_{j} : Det.JoinsOn (c.withHooks H) Inv {i} {j})")
    let hov := forallList (ovl.map fun (i, j) => s!"ov{i}_{j}")
    let niStmt := if onInv then s!"
/-- **Noninterference** for the secret cells relative to an invariant, for every interpretation of
the parameters and every set of observed keys `lo`: from two configurations where `Init` holds,
equal outside the secret cells, two runs that both stop end equal outside them; given an invariant
`Inv` of the configurations where `Init` holds, determinism's listed obligations where `Inv` holds
(`ovl`; `NI.joinsOn_of_refuted` gives one from the pair's refutation){if niObl.isEmpty then "" else ", and the listed rules' unwinding where `Inv` holds"}. -/
theorem noninterference (H : HookParams) (lo : GroundTerm → Prop)
    \{Init Inv : Config (c.withHooks H) → Prop} (hinv : Invariant (c.withHooks H) Init Inv){ovPrem}{prem} :
    NI.TINIOn (c.withHooks H) Init (NI.LowEq (c.withHooks H) lo high) (NI.Stuck (c.withHooks H))
      (NI.LowEq (c.withHooks H) lo high) :=
  Kind.of_decided (NI.cellsKindOnAll c lo high H hinv
      (deterministic_on H Inv ({hov})))
    (NI.cellsDeciderOnAll c lo high H) niObl ni_cond
    ({ho})" else s!"
/-- **Noninterference** for the secret cells{if niObl.isEmpty then "" else ", given the listed rules"}, for every interpretation of the parameters and every set of observed keys `lo`. -/
theorem noninterference (H : HookParams) (lo : GroundTerm → Prop){prem} :
    NI.TINI (c.withHooks H) (NI.LowEq (c.withHooks H) lo high) (NI.Stuck (c.withHooks H))
      (NI.LowEq (c.withHooks H) lo high) :=
  Kind.of_decided (NI.cellsKindAll c lo high H (fun _ _ _ h h' => deterministic H h h'))
    (NI.cellsDeciderAll c lo high H) niObl ni_cond ({ho})"
    let niHdr := if onInv then s!": from configurations where an initial condition holds, equal outside them, runs that both stop end equal outside them, given an invariant of those configurations, determinism's {ovl.length} listed obligations where it holds{if niObl.isEmpty then "" else s!" and the {niObl.length} listed rules' unwinding where it holds"} (obligations)" else s!": from configurations equal outside them, runs that both stop end equal outside them{if niObl.isEmpty then "" else s!", given the {niObl.length} listed rules unwind (obligations)"}"
    o ← o.write s!"{ns}.Kinds.NI" (s!"import {ns}.Kinds.Det\nimport KcoreSpec.NICells\n" ++ hdr s!"Noninterference for the secret cells {", ".intercalate ((high ++ keyed).map fun x => s!"`{x}`")}{if keyed.isEmpty then "" else s!" (of the maps {", ".intercalate (keyed.map fun x => s!"`{x}`")}, the observer sees the keys and the entries at the keys `lo` names)"}{niHdr}; for every interpretation of the parameters." ++ s!"
namespace {ns}
open KCore

/-- The policy: the positions of the cells kept secret, then the keyed positions of the maps whose
entries are secret except at the observed keys. -/
noncomputable def high : NI.HPaths := NI.highOf defn.pres {reprStr high} ++ NI.keyedOf defn.pres {reprStr keyed}

theorem high_eq : high = {reprStr H} := by decide +kernel

/-- The rules the decided condition does not cover{if niObl.isEmpty then " (none). " else ":\n" ++ String.join (niObl.map fun i => s!"- {i}{lbl i}\n")}-/
def niObl : List Nat := {reprStr niObl}

theorem ni_cond : Kind.decides (Kind.listCond c.rules (NI.cellsCond c high)) niObl (List.range c.rules.length) = true := by
  decide +kernel
{niStmt}

end {ns}
")
    kindMods := kindMods.push s!"{ns}.Kinds.NI"
  -- root module, lakefile, build order
  o ← o.write ns (String.join ((if exec then [s!"{ns}.Surface"] ++ kindMods.toList else [s!"{ns}.Names", s!"{ns}.Facts"]).map (s!"import {·}\n")) ++
    s!"import {ns}.Syntax\n" ++
    s!"import {ns}.Facts.Terminates\n" ++
    hdr s!"The package of `{koreFile}`.{if c.params.any (·.raw) then " It states no run certificate and no stuckness theorem: a parameter is an open generator, whose application's sort is read from the interpretation, and the certificates' soundness (`KCore.Cert.checkRun_sound`, `KCore.Cert.stuckCheck_sound`) holds where no parameter is." else ""}")
  writeLakefile out ns
  IO.FS.writeFile (out / "modules.txt") ("\n".intercalate o.mods.toList ++ "\n")
  if tie then IO.FS.writeFile (out / "tie.txt") ("\n".intercalate tieMods.toList ++ "\n")
  IO.println s!"\{\"ns\": \"{ns}\", \"rules\": {n}, \"fns\": {c.fns.length}, \"ruleBlocks\": {ruleBlocks.length}, \"paths\": {paths.length}, \"compatPairs\": {cp.length}, \"detBlocks\": {rowBlocks.length}, \"overlaps\": {ovl.length}, \"uniqFails\": {badUniq.length}, \"counterObl\": {ctrObl.length}, \"params\": {boolStr hasParams}, \"modules\": {o.mods.size}}"
  return 0

/-! ## The account of a text, without generating -/

/-- Where a sentence comes from: a file of K's builtin library (`…/include/kframework/builtin/` or
`krust-builtin://`), such a file's sentence read as the definition's own (`own builtin`,
`Parse.isOwnBuiltin`), another file, or no file (generated). -/
def origin (s : Kore.Sentence) : String :=
  match KoreAML.Parse.source? (Parse.sentenceAttrs s) with
  | none => "generated"
  | some src =>
    if Parse.isOwnBuiltin s then "own builtin"
    else if (KoreAML.Parse.dropPrefix? "krust-builtin://" src).isSome ||
       (src.splitOn "/include/kframework/builtin/").length > 1 then "builtin" else "user"

/-- The segments of `cs` (in order, together `cs`): the text outside every `Source(PATH)`'s PATH
(`true`) and each PATH, up to its `)` (`false`). `acc` is the current segment, reversed; `inPath`
whether it is a PATH. -/
def srcSegs : List Char → Bool → List Char → List (List Char × Bool)
  | [], inPath, acc => [(acc.reverse, !inPath)]
  | c :: cs, false, acc =>
    let acc' := c :: acc
    if acc'.take 7 == "Source(".toList.reverse then (acc'.reverse, true) :: srcSegs cs true []
    else srcSegs cs false acc'
  | c :: cs, true, acc =>
    if c == ')' then (acc.reverse, false) :: srcSegs cs false [c]
    else srcSegs cs true (c :: acc)

/-- The segments taken while `n` characters of the counted ones (`true`) remain, a PATH whole, and
whether a counted character was left out. -/
def clipSegs : Nat → List (List Char × Bool) → List Char × Bool
  | _, [] => ([], false)
  | n, (cs, false) :: rest =>
    let r := clipSegs n rest
    (cs ++ r.1, r.2)
  | n, (cs, true) :: rest =>
    if cs.length ≤ n then
      let r := clipSegs (n - cs.length) rest
      (cs ++ r.1, r.2)
    else (cs.take n, true)

/-- The account's class of a lemma applying a parameter symbol without `impl` (`isParamLemma`), and
of a `simplification` sentence of K's builtin library applying one (`isLibParamLemma`): the tie
class `parameter lemma` (`tieClasses`), in place of the reader's class `inert simplification`, or
`read` for the library's sentence. -/
def paramLemmaClass : String := "parameter lemma"

/-- The account's class of a user's equation of a symbol whose value the registry gives
(`Parse.regLemmaEqn`) that applies no parameter symbol without `impl`: the tie class `user lemma at
values` (`tieClasses`), in place of the reader's class `read`. The reader does not put the sentence
in Γ; it rests on an interpreted symbol's graph, which Γ states at values. -/
def userLemmaValuesClass : String := "user lemma at values"

/-- What the account says after a class line beyond the class: for a sentence of the user's text
classed `inert simplification`, that the class claims `Γ ⊧ tr s` and the reader does not decide it:
the sentence is owed, entailed by Γ, and the tie on the text (C14) proves it or fails; for a
parameter lemma, that it is owed as a hypothesis on `H` at values (some `H` meets `FnObligations`
and at it each sentence of the class is `EntailsAtValues (c.withHooks H) s (tr s)`); for a user's
equation of a symbol whose value the registry gives, that it is owed at values. -/
def classLineOwed (c o : String) : String :=
  if c == "inert simplification" && o == "user" then
    ": owed, entailed by Γ (the tie on the text proves it or fails), not decided by the reader"
  else if c == userLemmaValuesClass then
    ": owed at values, not in Γ (EntailsAtValues: Γ (c.withHooks H) entails it at the valuations sending its variables to values, or Γ with it has no model; the tie on the text proves it or fails), not decided by the reader"
  else if c == paramLemmaClass then
    ": owed as a hypothesis on H at values (some H meets FnObligations and at it each sentence of the class is EntailsAtValues (c.withHooks H) s (tr s); the tie shows an H at which the text's hypotheses hold), not decided by the reader"
  else ""

/-- `s` cut after its first `n` characters, a `Source(PATH)`'s PATH counted as none and never cut
(FIX-core.account-trunc-path): where a line is cut does not depend on the directory a text was
kompiled in or on K's installation path, so the line is the same for two texts that differ only in
their Source paths once each path is replaced by its path-free name (kfix.py's `norm`: FIXTURE/,
BUILTIN/). Without a `Source(` in `s`, the first `n` characters, as before. -/
def clip (n : Nat) (s : String) : String :=
  let r := clipSegs n (srcSegs s.toList false [])
  if r.2 then String.ofList r.1 ++ " …" else s

/-- `kcore account KORE`: the reader's account of a text, with no package written: the prelude's
agreement, the user module's sentences by class and origin with one example of each refused
class, every refusal of the stages, the sentences read that the definition does not account for,
the rules and the functions' clauses whose `CondDecided` is owed (`Parse.owedCondDecided`,
`Parse.owedClauseCondDecided`) and, printed once after them, that the text's soundness,
completeness and exactness are stated only under these facts as hypotheses (`Owed` of the
`_defn` statements, `hw` and `hc` of `sound_at_of`, `complete_at_of`) and that `consistent` reads
none of them, and, when the text is read, `wf`'s and `coreOK`'s failing conjuncts and the number of the account's
own refusals (`Parse.accountRefusals`). -/
def account (koreFile : String) : IO UInt32 := do
  let text ← IO.FS.readFile koreFile
  let .ok k := Kore.parseDefinition text | IO.eprintln s!"{koreFile}: KORE read error"; return 1
  let some m := k.modules.getLast? | IO.eprintln s!"{koreFile}: no module"; return 1
  let off := Parse.preludeLength k
  IO.println s!"{koreFile}: {k.modules.length} modules; prelude {if k.modules.dropLast = preludeModules then "agrees" else "differs: " ++ (Parse.preludeRefusal k).toText}"
  IO.println s!"user module {m.name.ident.name}: {m.sentences.length} sentences"
  let N := Parse.namesOf k
  -- a lemma applying a parameter symbol without `impl` of the reading is a parameter lemma, and so
  -- is a `simplification` sentence of K's builtin library applying one
  let dRead := match Parse.finish m (Parse.scan m.sentences) with
    | .ok d => some d
    | .error _ => none
  -- a user's equation of a symbol whose value the registry gives is out of Γ, owed: a parameter
  -- lemma where it applies a parameter symbol without `impl`, a user lemma at values otherwise
  let S := Parse.scan m.sentences
  let clsName := fun (s : Kore.Sentence) =>
    let cl := Parse.classify N s
    match s with
    | .axiom a =>
      if (Parse.rawEqn? a).any (Parse.regLemmaEqn S ·) then
        if dRead.any (fun (d : Definition) => appliesNoImplParam d.sem a.pattern) then paramLemmaClass else userLemmaValuesClass
      else if dRead.any (fun (d : Definition) => isParamLemma d.sem cl s || isLibParamLemma d.sem cl s) then paramLemmaClass else cl.name
    | _ => if dRead.any (fun (d : Definition) => isParamLemma d.sem cl s || isLibParamLemma d.sem cl s) then paramLemmaClass else cl.name
  let cls := m.sentences.map fun s => (clsName s, origin s, s)
  let keys := (cls.map fun (c, o, _) => (c, o)).eraseDups
  for (c, o) in keys do
    let these := cls.filter fun (c', o', _) => c' == c && o' == o
    IO.println s!"  {these.length} {c} [{o}]{classLineOwed c o}"
    if (c.splitOn "refused").length > 1 then
      for (_, _, s) in these.take 1 do IO.println s!"      e.g. {clip 400 (Kore.Printer.sentence s)}"
  -- printed only when some sentence is read so
  let cr := Parse.connReadings k
  unless cr.isEmpty do
    IO.println s!"connective readings per sentence: {cr.length}"
    for (i, ns) in cr do IO.println s!"      sentence {i}: {", ".intercalate (ns.map (·.name))}"
  -- printed only when the user module declares `#configuration`
  if let some us := Parse.configurationUses k then
    IO.println s!"sentences applying `#configuration` (read at a fixed value, not the documented one): {us.length}"
    for i in us do
      match m.sentences[i - off]? with
      | some s => IO.println s!"      sentence {i}: {clip 300 (Kore.Printer.sentence s)}"
      | none => pure ()
  let rs := Parse.refusals k
  let P := Parse.cellCollPairs m.sentences
  let classRefused := fun (i : Nat) => match m.sentences[i - off]? with
    | some s => match Parse.classifyShapeIn P s with | .refused _ => true | _ => false
    | none => false
  let stage := rs.filter fun r => match r.index with
    | some i => !classRefused i
    | none => true
  IO.println s!"stage refusals (of sentences classified read): {stage.length}"
  let reasons := stage.map (·.reason.name)
  for n in reasons.eraseDups do
    IO.println s!"  {reasons.count n} {n}"
    for r in (stage.filter (·.reason.name == n)).take 400 do
      IO.println s!"      {r.toText}"
      match r.index.bind fun i => m.sentences[i - off]? with
      | some s =>
        let as := Parse.sentenceAttrs s
        let place := s!"{(KoreAML.Parse.attrStr? as "label").getD "(no label)"} at {((KoreAML.Parse.source? as).getD "").splitOn "/" |>.getLast!}:{((KoreAML.Parse.loc? as).map (·.l1)).getD 0}"
        IO.println s!"        [{origin s}] {place}: {clip 400 (Kore.Printer.sentence s)}"
      | none => pure ()
  match Parse.finish m (Parse.scan m.sentences) with
  | .error f => IO.println s!"finish: {(f.toRefusal off m).toText}"
  | .ok d =>
    let un := Parse.unconsumed k d
    IO.println s!"read and not accounted for: {un.length}"
    let kinds := un.map (·.detail)
    for n in kinds.eraseDups do
      IO.println s!"  {kinds.count n} {n}"
      for r in (un.filter (·.detail == n)).take 2 do IO.println s!"      {r.toText}"
    let ui := Parse.uninduced k d
    IO.println s!"inert constructor axioms not induced by the constructors: {ui.length}"
    let uk := ui.map fun r => s!"{r.detail} of {r.head}"
    for x in uk.eraseDups do IO.println s!"    {uk.count x} {x}"
    for r in ui.take 5 do
      IO.println s!"      {r.toText}"
      match r.index.bind fun i => m.sentences[i - off]? with
      | some s => IO.println s!"        {clip 400 (Kore.Printer.sentence s)}"
      | none => pure ()
    -- printed only when the definition has overloading symbols
    unless d.sem.ovls.isEmpty do
      IO.println s!"overloading symbols read: {d.sem.ovls.length}, overloads (symbol-overload axioms) {(d.sem.ovls.map (·.over.length)).sum}"
      let oc := Parse.overloadConfusions k d
      IO.println s!"distinctness axioms an overload contradicts, stated by the text and not read (overloadConfusion): {oc.length}"
      for (i, h) in oc.take 10 do IO.println s!"      sentence {i} ({h})"
      -- printed only when some overloading symbol overloads a function
      let ofn := Parse.overloadFunctions d
      unless ofn.isEmpty do
        IO.println s!"overloading symbols that overload a function, their functional, injectivity and distinctness axioms read at the arguments no overload covers (overloadFunction): {ofn.length}"
        for (f, gs) in ofn.take 10 do IO.println s!"      {f} over {", ".intercalate gs}"
        IO.println "      at arguments an overload covers these axioms hold in a model only if the covering function is total there, injective there and apart from the other generators of the sort; if it is not, the text has no model (not decided here)"
    -- printed only when some equation is read by cases
    let byCases := (Parse.connReadings k).filter fun (_, ns) => ns.contains .orAsCases || ns.contains .existsAsCases
    unless byCases.isEmpty do
      IO.println s!"equations read by cases, a clause for each alternative of the right side and one where none has an element (orAsCases, existsAsCases): {byCases.length}"
      for (i, ns) in byCases.take 10 do
        IO.println s!"      sentence {i}: {", ".intercalate ((ns.filter fun n => n == .orAsCases || n == .existsAsCases).map (·.name))}"
      IO.println "      where two alternatives of one equation have different elements at one point the text has no model: the sentence gives the function both, its functional sentence one (not decided here)"
      if byCases.any (·.2.contains .existsAsCases) then
        IO.println s!"      existsAsCases reads the elements of Bool as its two literals, which the definition's theory states (boolClosed, an axiom of Γcl): readsConfined {d.sem.readsConfined}, litSort Bool {d.sem.litSort Srt.bool}"
    let cu := Parse.cellCollUnmatched k d
    IO.println s!"cell collection injections not of a collection of the definition: {cu.length}"
    for r in cu.take 5 do IO.println s!"      {r.toText}"
    let lu := Parse.lawUnmatched k d
    IO.println s!"law axioms of no collection's concatenation: {lu.length}"
    for r in lu.take 10 do IO.println s!"      {r.toText}"
    -- printed only when the text writes a law for an open generator that is read
    let ol := Parse.openLawSentences k d
    unless ol.isEmpty do
      IO.println s!"law axioms of open generators, read as axioms of Γ (ParamSig.assoc, ParamSig.idem; OpenLaws owed): {ol.length}"
      for (i, h, ls) in ol do IO.println s!"      sentence {i} ({h}): openLaw ({", ".intercalate ls}): OpenLaws owed"
    -- printed only when the text has an open generator
    let of := Parse.openFunctionalSentences k d
    unless of.isEmpty do
      IO.println s!"functional axioms of open generators, stated at values under OpenTotal (no item of Γ; OpenTotal owed): {of.length}"
      for (i, f) in of do IO.println s!"      sentence {i} ({f}): stated at values, under OpenTotal"
    -- printed only when the text writes a law for a function
    let fl := Parse.fnLawSentences k d
    unless fl.isEmpty do
      IO.println s!"law axioms of functions, read as laws stated at values (Definition.laws; FnLaws owed, one entry per law): {fl.length}"
      -- each sentence is one law of `Definition.laws`, in the same order (`fnLawAxioms`)
      for ((i, h, ls), l) in fl.zip d.laws do
        IO.println s!"      sentence {i} ({h}): fnLaw ({", ".intercalate ls}): {Parse.fnLawEntry d.sem l}"
      unless fl.length == d.laws.length do
        IO.println s!"      the laws read are {d.laws.length}, not one per sentence: the entries above pair them by position"
    -- printed only when a constructor or an open generator carries a unit attribute
    let ui := Parse.unitIgnored k d
    unless ui.isEmpty do
      IO.println s!"unit attributes of constructors and open generators, ignored (the text holds no unit sentence of the symbol; nothing read): {ui.length}"
      for (i, f, u) in ui do IO.println s!"      sentence {i} ({f}): unit ({u}) ignored: no unit sentence of {f}"
    IO.println s!"rules with an `ensures`: {Parse.rulesWithEnsures d}"
    IO.println s!"rules read with the premise ⌈rhs ∧ ens⌉ (ruleRightDefined): {Parse.rulesRightDefined d}"
    let fp := Parse.functionInPattern k d
    IO.println s!"rules and clauses applying a function symbol in their left side: {fp.length}"
    for r in fp.take 10 do IO.println s!"      {r.toText}"
    -- printed only when some rule or clause has the shape
    let rp := Parse.rangeMapInPattern k d
    unless rp.isEmpty do
      IO.println s!"rules and clauses binding a variable under a range-map symbol in their left side: {rp.length}"
      for r in rp.take 10 do IO.println s!"      {r.toText}"
    -- printed only when some rule or clause has the shape
    let gp := Parse.openGeneratorInPattern k d
    unless gp.isEmpty do
      IO.println s!"rules and clauses applying an open generator in their left side: {gp.length}"
      for r in gp.take 10 do IO.println s!"      {r.toText}"
    -- printed only when some rule is read so
    let kr := Parse.keysAsMember k
    unless kr.isEmpty do
      IO.println s!"rules read with a map key applying a function as a membership conjunct of pre (keyFunctionAsMember): {kr.length}"
      for (i, fs) in kr.take 10 do IO.println s!"      sentence {i}: {fs}"
    -- printed only when some rule is read so
    let rc := Parse.rulesCondConjCnj d
    unless rc.isEmpty do
      IO.println s!"rules read with conjuncts B = true of pre or post, the conjuncts of a requires or of the right side's conditions after the first (andAtBool): {rc.length}"
      for (i, np, nq) in rc.take 10 do IO.println s!"      rule {i}: {np} in pre, {nq} in post"
    -- printed only when some rule's `CondDecided` is owed
    let ow := Parse.owedCondDecided d.sem
    unless ow.isEmpty do
      IO.println s!"rules whose CondDecided is owed (closed conditions over a variable of an unconfined sort; open until witnessed or refuted): {ow.length}"
      for (i, js) in ow do
        let rp := d.pres.rules[i]?
        let lbl := match rp.bind (·.label) with | some l => s!" (`{l}`)" | none => ""
        let names := (rp.map (·.names)).getD []
        let sorts := (d.sem.rules[i]?.map (·.vars)).getD []
        let vs := js.map fun j => s!"Var{names.getD j ""}:{d.sem.sortName (sorts.getD j 0)}"
        IO.println s!"      rule {i}{lbl}: CondDecided open, over {", ".intercalate vs}"
    -- printed only when some clause's `CondDecided` is owed
    let owC := Parse.owedClauseCondDecided d.sem
    unless owC.isEmpty do
      IO.println s!"clauses whose CondDecided is owed (closed conditions over a variable of an unconfined sort; open until witnessed, some values satisfying the conditions and the requires having no result but true at them, or refuted): {owC.length}"
      for (i, j, ks) in owC do
        let f := d.sem.fns[i]?
        let fp := d.pres.fns[i]?
        let cp := fp.bind (·.clauses[j]?)
        let fname := match f with | some f => decodeK (d.sem.symName f.label) | none => "?"
        let lbl := match cp.bind (·.label) with | some l => s!" (`{l}`)" | none => ""
        let src := ((cp.bind (·.src)).getD ((fp.bind (·.src)).getD d.pres.source)).splitOn "/" |>.getLast!
        let line := (cp.map (·.info.loc.l1)).getD 0
        let names := (cp.map (·.names)).getD []
        let sorts := ((f.bind (·.clauses[j]?)).map (·.vars)).getD []
        let vs := ks.map fun k => s!"Var{names.getD k ""}:{d.sem.sortName (sorts.getD k 0)}"
        IO.println s!"      function {fname}, clause {j}{lbl} at {src}:{line}: CondDecided open, over {", ".intercalate vs}"
    unless ow.isEmpty && owC.isEmpty do
      IO.println "soundness, completeness and exactness of this text are stated only under these facts as hypotheses (`Owed`; `hw`, `hc` of `sound_at_of`, `complete_at_of`); `consistent` reads none"
    -- each printed only when some equation is read so
    let ep := Parse.equationsUnderPriority d
    unless ep == 0 do
      IO.println s!"function equations read with the premise that no clause of a smaller priority applies (equationPriority): {ep}"
    let ow := Parse.owiseEquations k d
    unless ow == 0 do
      IO.println s!"[owise] equations read as clauses of priority 200 (owiseAsPriority): {ow}"
    let on := Parse.owiseNarrowed k d
    unless on.isEmpty do
      IO.println s!"[owise] equations read with a premise narrower than the text's (owiseDisjunctNarrower): {on.length}"
      for (i, f, j) in on.take 10 do
        IO.println s!"      sentence {i} ({f}): its disjunct for sentence {j}, read with its set variable's memberships dropped, holds one element variable at both arguments"
      IO.println "      if the two right sides differ at two distinct arguments, the text has no model (kompile 7.1.337 writes the exclusion of a set-variable equation at equal arguments)"
    -- printed only when KItem's no-junk axiom leaves out a sort of `d` below KItem
    let tk := Parse.tokKItemOmitted k d
    unless tk.isEmpty do
      IO.println s!"KItem no-junk axioms read with a generator inj\{X, KItem} they do not list, X a sort of d below KItem (tokKItem): {tk.length}"
      for (i, xs) in tk.take 10 do
        IO.println s!"      sentence {i}: {", ".intercalate (xs.map fun (x, st) => s!"{x} ({if st then "the text states the subsort" else "the reading adds the subsort, which the text does not state"})")}"
      IO.println "      the text's sentence entails Γ's no-junk item of KItem; where such a sort has an element, the text's sentence with Γ has no model"
    let lu := Parse.libraryUnstated k d
    IO.println s!"sentences the library's data induces that the text does not hold: {lu.length}"
    for r in lu.take 40 do IO.println s!"      {clip 300 r.detail}"
    let mb := Parse.missingBuiltin k d
    IO.println s!"library sentences of the modules held that the text does not hold: {mb.length}"
    for r in mb.take 10 do IO.println s!"      {r.head}: {clip 300 r.detail}"
    let ka := Parse.kernelAbsent k d
    IO.println s!"sentences every definition holds (kernelText) that the text does not: {ka.length}"
    for s in ka do IO.println s!"      {clip 300 (Kore.Printer.sentence (Parse.bare s))}"
    if rs.isEmpty then
      IO.println s!"sorts without a value (not a condition of wf; the text's G-nonempty for them is not in Γ): {d.sem.valueless.length}: {", ".intercalate (d.sem.valueless.map d.sem.sortName)}"
      -- the `[total]` functions no decider confirms, as `genFnHyp` computes the package's
      -- `total_named`: `totalObligationsRP` at `callOrderOf`, with the parameters the text declares
      -- total where the definition has parameters no registry hook implements
      let tp := if d.sem.params.any (·.impl.isNone) then d.totalParams else []
      let owedTot := d.sem.totalObligationsRP (callOrderOf d.sem) tp
      IO.println s!"functions declared [total] whose totality no decider confirms (the package's total_named, Semantics.totalObligationsRP at kcore gen's call order; not a condition of wf: the text's functional axiom for each is in no part of Γ and is owed as Total): {owedTot.length}: {", ".intercalate (owedTot.map fun f => decodeK (d.sem.symName f))}"
      -- the held-named functions, as `genFnHyp` computes the package's `held_named`, each with
      -- the variables `clauseValued` does not accept
      let owedHeld := d.sem.heldObligations
      IO.println s!"functions with an equation holding a variable its arguments and conditions do not bind, of a sort without an exhibited value (the package's held_named, Semantics.heldObligations; not a condition of wf or coreOK: owed for each is that every such variable's sort has a value, or that the function has a result at every argument list, a value where it is [total]): {owedHeld.length}: {", ".intercalate (owedHeld.map fun f => decodeK (d.sem.symName f))}"
      for (f, fp) in withPres d.sem.fns d.pres.fns do
        for ((cl, cp), j) in (withPres f.clauses fp.clauses).zipIdx do
          for i in List.range cl.vars.length do
            unless cl.leftVars.contains i || (cl.vars[i]?.map d.sem.valued).getD false do
              let s := cl.vars.getD i 0
              let note := if d.sem.valueSorts.contains s then "" else "; the sort has no value"
              IO.println s!"      function {decodeK (d.sem.symName f.label)}, clause {j}: Var{cp.names.getD i ""}:{d.sem.sortName s}{note}"
      -- the functions whose equations' agreement no decider confirms, as `genFnHyp` computes the
      -- package's `agree_named`: `agreeObligationsI`
      -- the open generators, whose laws and values every statement takes as hypotheses at each
      -- interpretation H (the package's `hop`, `_hot`)
      let og := d.sem.params.filter (·.raw)
      unless og.isEmpty do
        let lawsOf := fun (k : ParamSig) =>
          let ls := (if k.assoc then ["assoc"] else []) ++ (if k.idem then ["idem"] else [])
          if ls.isEmpty then "" else s!" ({", ".intercalate ls})"
        IO.println s!"open generators, whose laws and values at every argument list are owed at each interpretation H (OpenLaws and OpenTotal of defn.sem.withHooks H, hypotheses of every statement; not a condition of wf or coreOK): {og.length}: {", ".intercalate (og.map fun k => decodeK (d.sem.symName k.sig.name) ++ lawsOf k)}"
      let owedAgr := d.sem.agreeObligationsI
      IO.println s!"functions whose equations' agreement no decider confirms (the package's agree_named, Semantics.agreeObligationsI; not a condition of wf or coreOK: where two competing equations both decide, their agreement is owed as ClausesAgree): {owedAgr.length}: {", ".intercalate (owedAgr.map fun f => decodeK (d.sem.symName f))}"
      -- printed only when some clause's predicate is not `\top`: the clauses, by function and
      -- position; the `--core` package's statements then take `FnHyp` itself
      let notTop := d.sem.fns.flatMap fun f => (f.clauses.zipIdx.filter (!·.1.pre.isTop)).map fun (_, j) =>
        s!"{decodeK (d.sem.symName f.label)} clause {j}"
      unless notTop.isEmpty do
        IO.println s!"clauses whose predicate is not \\top (Semantics.clausesPreTop false; not a condition of coreOK: the named facts give FnHyp only where every clause's predicate is \\top, so the --core package's statements take FnHyp itself as a hypothesis): {notTop.length}: {", ".intercalate notTop}"
      -- printed only when some clause holds an existential variable
      for l in Parse.owedExsText d decodeK do IO.println l
      -- printed only when some equation is read so: the clauses with `Clause.aside`, each with the
      -- index of its sentence (found by the clause's `UNIQUE'Unds'ID`) and its function
      let asides := (withPres d.sem.fns d.pres.fns).flatMap fun (f, fp) =>
        ((withPres f.clauses fp.clauses).filter (·.1.aside)).map fun (_, cp) =>
          -- a symbol-overload axiom, which has no id, by its first symbol
          let i? := m.sentences.findIdx? fun (s : Kore.Sentence) => match s with
            | .axiom a => if cp.info.uid.isEmpty then
                ((Parse.overloadSyms? a.attributes).map fun (g : String × String) => g.1) == some (d.sem.symName f.label)
              else KoreAML.Parse.attrStr? a.attributes "UNIQUE'Unds'ID" == some cp.info.uid
            | _ => false
          ((i?.map (off + ·)), decodeK (d.sem.symName f.label))
      unless asides.isEmpty do
        IO.println s!"equations read as aside clauses (non-executable, or a symbol-overload axiom of a function: no [owise] premise negates them, Clause.aside; such an equation competes with every equation of a larger priority of its function): {asides.length}"
        for (i?, fn) in asides do
          IO.println s!"      sentence {(i?.map toString).getD "?"} ({fn})"
      IO.println s!"parse: ok; wf {wf d}; failing: {(d.report.filter (!·.2)).map (·.1)}"
      let core := (coreParts d.sem (tables d.sem)).filter (!·.2)
      IO.println s!"coreOK: {core.isEmpty}; failing: {core.map (·.1)}"
      IO.println s!"refused by the account: {(Parse.accountRefusals k d).length}"
  return 0

/-- A term, its symbols and sorts by name (`vs` the variables' sorts), cut at depth `d`. -/
partial def showTerm (c : Semantics) (vs : List Srt) (d : Nat) (t : Term) : String :=
  if d == 0 then "…" else
  let sn := fun (s : Srt) => c.sortName s
  match t with
  | .var i => s!"V{i}:{(vs[i]?.map sn).getD "?"}"
  | .dv s (.int n) => s!"{n}:{sn s}"
  | .dv s (.bool b) => s!"{b}:{sn s}"
  | .dv s (.tok x) => s!"\"{x}\":{sn s}"
  | .dv s (.float p e b) => s!"{KFloat.text p e b}:{sn s}"
  | .app f ts => s!"{decodeK (c.symName f)}({", ".intercalate (ts.map (showTerm c vs (d - 1)))})"
  | .inj a b t => s!"inj\{{sn a},{sn b}}({showTerm c vs (d - 1) t})"
  | .as t i => s!"{showTerm c vs (d - 1) t} #as V{i}"

/-- The innermost subterm of `t` that has no sort in `x` though each of its arguments has one, with
why: its head is not in the context, or its arguments' sorts are not the head's. -/
partial def badSub (c : Semantics) (x : TermCtx) (vs : List Srt) (t : Term) : Option String :=
  if (sortOfTerm x vs t).isSome then none else
  let kids := match t with
    | .app _ ts => ts
    | .inj _ _ u => [u]
    | .as u _ => [u]
    | _ => []
  match kids.findSome? (badSub c x vs) with
  | some w => some w
  | none =>
    let sn := fun (s : Srt) => c.sortName s
    let argSorts := fun (ts : List Term) => ts.map fun u => ((sortOfTerm x vs u).map sn).getD "?"
    let why := match t with
      | .app f ts => match lookupSig x.heads f with
        | none => s!"{decodeK (c.symName f)} is not a symbol this context applies"
        | some k => s!"{decodeK (c.symName f)} : {k.args.map sn} → {sn k.result}, applied to {argSorts ts}"
      | .inj a b u => if x.subs.contains (a, b) then s!"its argument has sort {argSorts [u]}, not {sn a}"
          else s!"{sn a} is not below {sn b}"
      | .as _ i => s!"an as-pattern of variable V{i} here"
      | .var i => s!"variable V{i} has no sort"
      | .dv s _ => s!"not a literal of {sn s}"
    some s!"{showTerm c vs 6 t}  [{why}]"

open Faithful Faithful.Model in
/-- `kcore wf-parts KORE`: `wf`'s conjuncts on what the reader reads off the text (`Parse.finish`
on the sentences classified read, whether or not some are refused), each with the number of
constructors, functions, clauses or rules it fails at where it is a check of each, and the named
obligations' lists' lengths. Each line is printed as it is decided, so a decision that does not
finish shows where. -/
def wfParts (koreFile : String) : IO UInt32 := do
  let text ← IO.FS.readFile koreFile
  let .ok k := Kore.parseDefinition text | IO.eprintln s!"{koreFile}: KORE read error"; return 1
  let some m := k.modules.getLast? | return 1
  let d ← match Parse.finish m (Parse.scan m.sentences) with
    | .ok d => pure d
    | .error f => IO.eprintln s!"finish: {(f.toRefusal (Parse.preludeLength k) m).toText}"; return 1
  let c := d.sem
  let out := fun (s : String) => do IO.println s; (← IO.getStdout).flush
  out s!"{koreFile}: {c.ctors.length} constructors, {c.fns.length} functions ({(c.fns.map (·.clauses.length)).sum} clauses), {c.rules.length} rules, {c.userSorts.length} sorts"
  let n := fun (b : Bool) => if b then "holds" else "FAILS"
  out s!"namesOK: {n d.namesOK}"
  let badC := c.ctors.filter fun k => !(k.args.all c.argSortOK && c.ctorResultOK k.result)
  let badF := c.fns.filter fun f => !(f.args.all c.argSortOK && c.resultSortOK f.result)
  let pgmOK := c.userSorts.contains c.pgmSort || [Srt.k, Srt.kitem, Srt.int, Srt.bool].contains c.pgmSort
  out s!"okAll.declsOK: {n c.declsOK} (constructors failing {badC.length}, functions failing {badF.length}, $PGM sort {n pgmOK})"
  for k in badC.take 10 do
    out s!"  constructor {decodeK (c.symName k.name)} : {k.args.map c.sortName} → {c.sortName k.result}"
  for f in badF.take 10 do
    out s!"  function {decodeK (c.symName f.label)} : {f.args.map c.sortName} → {c.sortName f.result}"
  out s!"okAll.subsortsOK: {n c.subsortsOK}"
  unless c.subsortsOK do
    for (a, b) in c.userSubsorts do
      let why := if a == b then "reflexive"
        else if !(c.userSorts.contains a || c.libValueSorts.contains a) then s!"{c.sortName a} is neither the definition's sort nor a library value sort"
        else if !(c.userSorts.contains b || c.libConsSorts.contains b) then s!"{c.sortName b} is neither the definition's sort nor a library sort of constructor terms"
        else ""
      unless why.isEmpty do out s!"  subsort {c.sortName a} < {c.sortName b}: {why}"
    for (a, b) in c.declaredClosure do
      if a == b then out s!"  the declared subsorts' closure has a cycle through {c.sortName a}"
  out s!"note (not a condition of wf): sorts without a value: {c.valueless.length}: {", ".intercalate (c.valueless.map c.sortName)}"
  let names := fun (l : List String) => ", ".intercalate (l.take 6) ++ (if l.length > 6 then ", …" else "")
  let heads := c.fns.map Fn.sig
  let used := c.appliedSyms
  let badFn := c.fns.filter fun f => !c.fnOKAll heads f
  let badCl := c.fns.flatMap fun f => f.clauses.filter fun cl => !c.clauseOKAll f heads cl
  let unclaused := c.fns.filter fun f => f.clauses.isEmpty && used.contains f.label
  out s!"okAll.fnsOKAll: {n badFn.isEmpty} (functions failing {badFn.length}: clauses failing {badCl.length})"
  out s!"note (not a condition of wf): applied functions without an equation, each its rest everywhere: {unclaused.length}"
  for (f, fp) in withPres c.fns d.pres.fns do
    if f.clauses.isEmpty && used.contains f.label then
      out s!"  function {decodeK (c.symName f.label)} ({(fp.src.getD d.pres.source).splitOn "/" |>.getLast!}:{fp.loc.l1}): applied, no equation{if f.total then ", declared total" else ""}"
    for (cl, cp) in withPres f.clauses fp.clauses do
      unless c.clauseOKAll f heads cl do
        let fns := c.rhsCtx heads
        let at_ := s!"{decodeK (c.symName f.label)}, {cp.label.getD "(no label)"} at {(cp.src.getD (fp.src.getD d.pres.source)).splitOn "/" |>.getLast!}:{cp.info.loc.l1}"
        let parts := [("arguments not of the function's sorts", sortsOfTerms c.patCtxAll cl.vars cl.pats == some f.args,
            cl.pats.findSome? (badSub c c.patCtxAll cl.vars)),
          ("a map pattern with two frames", noMapInList cl.pats, none),
          ("a variable that occurs nowhere in the clause", binds cl.vars.length (cl.leftVars ++ varOccs cl.rhs ++
            (cl.ens.map varOccs).getD []), none),
          ("requires not of sort Bool", reqOK fns cl.vars cl.req, cl.req.bind (badSub c fns cl.vars)),
          ("right side not of the result sort", sortOfTerm fns cl.vars cl.rhs == some f.result, badSub c fns cl.vars cl.rhs),
          ("ensures not of sort Bool", reqOK fns cl.vars cl.ens, cl.ens.bind (badSub c fns cl.vars))]
        for (what, ok, sub) in parts do
          unless ok do out s!"  clause of {at_}: {what}{match sub with | some w => s!": {w}" | none => ""}"
  let badR := c.rules.filter fun r => !c.ruleOKAll r
  out s!"okAll rules: {n badR.isEmpty} (rules failing {badR.length})"
  for (r, rp) in withPres c.rules d.pres.rules do
    unless c.ruleOKAll r do
      let fns := c.rhsCtx (c.fns.map Fn.sig)
      let at_ := s!"{rp.label.getD "(no label)"} at {(rp.src.getD d.pres.source).splitOn "/" |>.getLast!}:{rp.info.loc.l1}"
      let parts := [("left side not of the configuration sort", sortOfTerm c.patCtxAll r.vars r.lhs == some topCellSort, badSub c c.patCtxAll r.vars r.lhs),
        ("a map pattern with two frames", noMapIn r.lhs, none),
        ("a variable that occurs nowhere in the rule", binds r.vars.length (varOccs r.lhs ++ r.condVars ++
          varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post), none),
        ("requires not of sort Bool", reqOK fns r.vars r.req, r.req.bind (badSub c fns r.vars)),
        ("ensures not of sort Bool", reqOK fns r.vars r.ens, r.ens.bind (badSub c fns r.vars)),
        ("right side not of the configuration sort", sortOfTerm fns r.vars r.rhs == some topCellSort, badSub c fns r.vars r.rhs)]
      for (what, ok, sub) in parts do
        unless ok do out s!"  rule {at_}: {what}{match sub with | some w => s!": {w}" | none => ""}"
  out s!"cert.ok: {n (d.cert.ok c)}"
  out s!"pres.ok: {n (d.pres.ok c)}"
  out s!"paramsOK: {n d.paramsOK}"
  out s!"paramsOK.hookFnsUnregOK: {n d.hookFnsUnregOK}"
  for (nm, f) in [("namesNumbered", Faithful.namesNumbered), ("genWf", Faithful.genWf), ("collSortsOK", collSortsOK),
      ("collsOK", collsOK), ("patHeadsOK", patHeadsOK), ("namesApartK", namesApartK), ("LitsApart", LitsApart),
      ("sortsNumbered", sortsNumbered), ("collsNotCtors", collsNotCtors), ("itesApart", itesApart),
      ("kindsApart", kindsApart), ("ctorsOnce", ctorsOnce), ("fnsApart", fnsApart)] do
    out s!"faithOK.{nm}: {n (f c)}"
  unless Faithful.genWf c do
    let cs := Faithful.consSorts c
    let k1 := c.ctorSigs.filter fun k => !cs.contains k.result
    let k2 := c.subsorts.filter fun p => !(cs.contains p.2 && p.1 != p.2)
    let k3 := cs.filter fun s => !(Faithful.apartSort c s && s != Srt.int && s != Srt.bool && s != Srt.kconfigVar &&
      !c.lib.tokenSorts.contains s && !c.lib.byteSorts.contains s && (c.collOf s).isNone)
    out s!"  genWf: constructors of a sort outside the constructor sorts {k1.length} ({names (k1.map (c.symName ·.name))}); subsorts into one or reflexive {k2.length} ({names (k2.map fun (a, b) => c.sortName a ++ " < " ++ c.sortName b)}); constructor sorts not apart or holding domain values {k3.length} ({names (k3.map c.sortName)})"
  out s!"obligations: order {c.orderObligations.length}, cert {(d.cert.obligations c).length}, total {c.totalObligations.length}"
  out s!"obligations: agree {c.agreeObligations.length}"
  out s!"obligations: match {c.matchObligations.length}"
  out s!"obligations: lazy {c.lazyObligations.length}"
  return 0

/-! ## The round trip of a text, natively -/

/-- The sentences of `k` and of `e` matched as multisets, each sentence used once: the indices of
`k`'s sentences that no sentence of `e` equals, and the sentences of `e` that no sentence of `k`
equals. Sentences are bucketed by their printed text and compared by equality within a bucket. -/
def sentenceDiff (k e : List Kore.Sentence) : List Nat × List Kore.Sentence := Id.run do
  let ka := k.toArray
  let mut byText : Std.HashMap String (List Nat) := {}
  for i in [0:ka.size] do
    let t := Kore.Printer.sentence ka[i]!
    byText := byText.insert t (byText.getD t [] ++ [i])
  let mut extra : Array Kore.Sentence := #[]
  for s in e do
    let t := Kore.Printer.sentence s
    let is := byText.getD t []
    match is.find? fun i => decide (ka[i]! = s) with
    | some i => byText := byText.insert t (is.erase i)
    | none => extra := extra.push s
  return ((byText.toList.flatMap (·.2)).mergeSort (fun a b => decide (a ≤ b)), extra.toList)

/-- Counts of names, in first-seen order: `3 read ensuresAsRequires, 1 unread setIdempotence`. -/
def countsOf (l : List String) : String :=
  ", ".intercalate (l.eraseDups.map fun n => s!"{l.count n} {n}")

/-- `kcore roundtrip KORE`: `parse`, then `emit` of the definition read, compared with the text up to
the order of each module's sentences, as the tie's `Reordered defn.emit kore` states it, natively.
The first word of the line printed is the verdict:
- `exact`: `emit` gives the text up to sentence order (exit 0);
- `modulo`: it does except for the text's sentences classified read in another form (`readAs`)
  or deliberately not read (`unread`), each counted by class, and the emitted counterparts of the
  `readAs` ones (paired with them by their attributes); nothing else differs (exit 0);
- `differs`: some other sentence, module or attribute differs; the differences are listed (exit 1);
- `cannot`: the text is not KORE or `parse` refuses it, with the first refusal (exit 3). -/
def roundTrip (koreFile : String) : IO UInt32 := do
  let text ← IO.FS.readFile koreFile
  let .ok k := Kore.parseDefinition text | IO.println s!"cannot {koreFile}: KORE read error"; return 3
  let d ← match Parse.parse k with
    | .ok d => pure d
    | .error r =>
      IO.println s!"cannot {koreFile}: KCore's parse refuses it ({(Parse.refusals k).length} refusals; first: {r.toText})"
      return 3
  let e := d.emit
  let mut probs : Array String := #[]
  unless decide (e.attributes = k.attributes) do probs := probs.push "the definition's attributes differ"
  unless e.modules.length == k.modules.length do
    probs := probs.push s!"{e.modules.length} modules emitted, {k.modules.length} in the text"
  let user := k.modules.length - 1
  let names := Parse.namesOf k
  let mut allowed : Array (String × Kore.Sentence) := #[]
  let mut other : Array (String × String × Kore.Sentence) := #[]
  let mut extra : Array Kore.Sentence := #[]
  let mut nSent := 0
  for ((me, mk), i) in (e.modules.zip k.modules).zipIdx do
    nSent := nSent + mk.sentences.length
    unless decide (me.name = mk.name) do
      probs := probs.push s!"module {i} is {me.name.ident.name} emitted, {mk.name.ident.name} in the text"
    unless decide (me.attributes = mk.attributes) do probs := probs.push s!"module {mk.name.ident.name}: attributes differ"
    let (missing, ex) := sentenceDiff mk.sentences me.sentences
    for j in missing do
      let s := mk.sentences[j]!
      let cl := Parse.classify names s
      if i == user then
        match cl with
        | .readAs _ | .unread _ => allowed := allowed.push (cl.name, s)
        | _ => other := other.push (cl.name, s!"{mk.name.ident.name} sentence {j}", s)
      else other := other.push ("prelude", s!"{mk.name.ident.name} sentence {j}", s)
    extra := extra ++ ex.toArray
  -- the emitted counterparts of the sentences read in another form, paired by their attributes
  let readAs := allowed.filter (·.1.startsWith "read ")
  let mut paired : Array Bool := Array.replicate readAs.size false
  let mut unpaired : Array Kore.Sentence := #[]
  for s in extra do
    match (List.range readAs.size).find? fun j =>
        !paired[j]! && decide (Parse.sentenceAttrs readAs[j]!.2 = Parse.sentenceAttrs s) with
    | some j => paired := paired.set! j true
    | none => unpaired := unpaired.push s
  let nPaired := (paired.toList.filter id).length
  if probs.isEmpty && other.isEmpty && unpaired.isEmpty then
    if allowed.isEmpty then
      IO.println s!"exact {koreFile}: emit gives the text up to sentence order ({k.modules.length} modules, {nSent} sentences)"
    else
      IO.println s!"modulo {koreFile}: emit gives the text up to sentence order except {allowed.size} of its {nSent} sentences: {countsOf (allowed.toList.map (·.1))}; {nPaired} of the {readAs.size} read in another form emitted as read (paired by attributes)"
    return 0
  IO.println s!"differs {koreFile}: {probs.size} module or attribute differences, {other.size} sentences of the text not emitted ({countsOf (other.toList.map (·.1))}), {unpaired.size} emitted sentences not in the text; besides, {allowed.size} sentences read in another form or not read ({countsOf (allowed.toList.map (·.1))})"
  for p in probs do IO.println s!"  {p}"
  for (cl, w, s) in other.toList.take 5 do IO.println s!"  not emitted: {w} ({cl}): {clip 300 (Kore.Printer.sentence s)}"
  for s in unpaired.toList.take 5 do IO.println s!"  emitted, not in the text: {clip 300 (Kore.Printer.sentence s)}"
  return 1

/-! ## The gap between a text and its print-back: `kcore gap`

`emit` writes a definition's text from the definition read (`roundtrip` compares the two up to the
order of each module's sentences). For a kompiled text the two differ: the emitter writes the
library's and the generated sentences in its own form. `kcore gap KORE` classifies every sentence
of the difference by cause. The text's sentences that `emit` does not write back are paired, one
to one, with the emitted sentences the text lacks, in stages, each pairing what the earlier stages
left by a key that forgets one more thing:
1. `places`: the sentence without its `Source` and `Location` attributes (`Parse.bare`);
2. `variable names`: also up to a one-to-one renaming of its element variables (`Parse.alphaKey`);
3. `order`: also with its attributes, and the arguments of each `\and` and `\or` of an axiom, in a
   fixed order (`Parse.canon`);
4. `attributes`: without any attribute, the pattern in that normal form; the cause names the
   attributes the two do not share;
5. `same name`: a declaration of the same sort or symbol, an axiom with the same `UNIQUE'Unds'ID`;
   the two state different things.
A sentence of stage 1 to 4 states, as an axiom or a declaration, what its partner states: the
attributes are not read as statements except those the account and the attribute agreement read.
What no stage pairs is classified by kind (`gapKind`). A kind has a direction where the tie
relates its sentences to `d`'s theory (TIE-1 D1: declarations, rewrite rules, the equations of
`d`'s functions, the constructor and subsort axioms): a text sentence of such a kind that stage 1 to
4 does not pair is one `d` does not hold as written, and every such sentence is printed. -/

/-- A sentence with its attributes replaced. -/
def gapSetAttrs (s : Kore.Sentence) (as : List Kore.AppPattern) : Kore.Sentence :=
  match s with
  | .sort x => .sort { x with attributes := as }
  | .hookedSort x => .hookedSort { x with attributes := as }
  | .symbol x => .symbol { x with attributes := as }
  | .hookedSymbol x => .hookedSymbol { x with attributes := as }
  | .alias x => .alias { x with attributes := as }
  | .axiom x => .axiom { x with attributes := as }
  | .claim x => .claim { x with attributes := as }
  | t => t

/-- The attributes of a sentence without its places, printed and sorted. -/
def gapAttrs (s : Kore.Sentence) : List String :=
  ((Parse.sentenceAttrs s).filter (!Parse.isPlaceAttr ·)).map (fun a => Kore.Printer.pattern (.app a.head a.sorts a.args))
    |>.mergeSort fun a b => decide (a ≤ b)

/-- A sentence's text with its attributes `as` and, for an axiom or a claim, its pattern in the
normal form `Parse.canon`. -/
def gapForm (s : Kore.Sentence) (as : List String) : String :=
  let body := match gapSetAttrs s [] with
    | .axiom a => s!"axiom {a.sortVars.map toString} {Parse.canon a.pattern}"
    | .claim a => s!"claim {a.sortVars.map toString} {Parse.canon a.pattern}"
    | t => Kore.Printer.sentence t
  s!"{body} [{", ".intercalate as}]"

/-- The name a sentence declares or carries: a sort's, a symbol's, an axiom's `UNIQUE'Unds'ID`. -/
def gapName (s : Kore.Sentence) : Option String :=
  match s with
  | .sort x => some s!"sort {x.sort.ident.name}"
  | .hookedSort x => some s!"sort {x.sort.ident.name}"
  | .symbol x => some s!"symbol {x.symbol.ident.ident.name}"
  | .hookedSymbol x => some s!"symbol {x.symbol.ident.ident.name}"
  | .axiom a => (KoreAML.Parse.attrStr? a.attributes "UNIQUE'Unds'ID").map (s!"axiom " ++ ·)
  | _ => none

/-- What a sentence is, for the gap, and whether the tie has a direction for it (TIE-1 D1: `true`
for declarations, rewrite rules, the equations of a function of `d`, a constructor's `functional`
axiom, the subsort, injectivity, distinctness and no-junk axioms). The kinds without one: an
import, a claim, a projection's selector-domain axiom and selector-inverse lemma (named by their
`UNIQUE'Unds'ID`), a lemma (`simplification`), an equation of a symbol `d` has no function for (a
library symbol's, a cell initializer's, a projection `d` does not read), the `functional` axiom of
a function (read into `FnHyp`, not into Γ) or of a hooked symbol, a collection law, set
idempotence, and a sentence of any other form. The class is the one at the text's cell-collection
pairs `P` (`Parse.cellCollPairs`). -/
def gapKind (P : List (String × String)) (d : Definition) (s : Kore.Sentence) : String × Bool :=
  let c := d.sem
  let fnLabels := c.fns.map fun f => c.symName f.label
  let ctorNames := c.ctorSigs.map fun k => c.symName k.name
  match s with
  | .import _ => ("import", false)
  | .claim _ => ("claim", false)
  | .alias _ => ("alias declaration", false)
  | .sort _ | .hookedSort _ => ("sort declaration", true)
  | .symbol _ | .hookedSymbol _ => ("symbol declaration", true)
  | .axiom a =>
    let uid := (KoreAML.Parse.attrStr? a.attributes "UNIQUE'Unds'ID").getD ""
    if uid.endsWith ".selector-domain" then ("selector-domain axiom of a projection", false)
    else if uid.endsWith ".selector-inverse" then ("selector-inverse lemma of a projection", false)
    else
    match Parse.classifyShapeIn P s with
    | .inert .simplification => ("simplification", false)
    | .inert .injectivity => ("injectivity axiom", true)
    | .inert .distinctCtors => ("distinctness axiom", true)
    | .inert .noJunk => ("no-junk axiom", true)
    | .inert .collectionLaw => ("collection law", false)
    | .inert .parametricFunctional => ("functional axiom of a sort-parametric symbol", false)
    | .unread .setIdempotence => ("set idempotence", false)
    | _ =>
      if (Parse.scanRewrite s).isSome then ("rewrite rule", true)
      else match ((Parse.rawEqn? a).orElse fun _ => Parse.overloadEqn? a).orElse fun _ => Parse.projDomainEqn? a with
      | some e =>
        if fnLabels.contains e.fn then ("equation of a function of d", true)
        else if regSymNames.contains e.fn then ("equation of a library symbol", false)
        else ("equation of a symbol d has no function for", false)
      | none => match Parse.scanEvent s with
        | some (.inl f) =>
          if ctorNames.contains f then ("functional axiom of a constructor", true)
          else if fnLabels.contains f then ("functional axiom of a function", false)
          else ("functional axiom of another symbol", false)
        | some (.inr _) => ("subsort axiom", true)
        | none => if (Parse.scanOr s).isSome then ("no-junk axiom", true)
          else (s!"axiom of another form ({(Parse.classifyShapeIn P s).name})", false)

/-- The attributes the two sentences do not share, `-a` the text's, `+a` the emitted's (their head
names, sorted). -/
def gapAttrDiff (t e : Kore.Sentence) : String :=
  let hd := fun (s : Kore.Sentence) => ((Parse.sentenceAttrs s).filter (!Parse.isPlaceAttr ·))
  let pr := fun (a : Kore.AppPattern) => Kore.Printer.pattern (.app a.head a.sorts a.args)
  let ta := hd t; let ea := hd e
  let tOnly := ta.filter fun a => !ea.any (pr · == pr a)
  let eOnly := ea.filter fun a => !ta.any (pr · == pr a)
  " ".intercalate (((tOnly.map (s!"-" ++ ·.head.ident.name)) ++ (eOnly.map (s!"+" ++ ·.head.ident.name))).eraseDups
    |>.mergeSort fun a b => decide (a ≤ b))

/-- `kcore gap KORE`: the text's sentences that `emit` does not write back and the emitted
sentences the text lacks (module by module, as `roundtrip` finds them), each classified by cause
(the section's stages), with counts: the pairs by stage (stage 4 by the attributes not shared), then
what no stage pairs by kind and origin. Then every text sentence of a kind with a direction that no
stage but `same name` pairs: what `d` does not hold as written, each with the reading notes the
account gives it (`Parse.connReadings`, `keysAsMember`, `owiseNarrowed`, `tokKItemOmitted`, a `readAs`, `unread` or `inert` class; an
inert constructor axiom that `d`'s constructors induce, `Parse.uninduced` not naming it): a sentence
read in another form under a note is a named reading (C14's weaker or more, with its note); one
without a note is a candidate reader defect, each to be decided. Exit 0 when there is none of the second kind, 1 when there is one, 3 when
the text is not read. With `all`, every sentence of the gap with its cause
(and its partner). -/
def gapCmd (koreFile : String) (all : Bool) : IO UInt32 := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile koreFile) | IO.println s!"cannot {koreFile}: KORE read error"; return 3
  let d ← match Parse.parse k with
    | .ok d => pure d
    | .error r => IO.println s!"cannot {koreFile}: KCore's parse refuses it ({r.toText})"; return 3
  let e := d.emit
  let P := (k.modules.getLast?.map fun m => Parse.cellCollPairs m.sentences).getD []
  -- the text's sentences not emitted (module name, index in the module, sentence), the emitted not in the text
  let mut ts : Array (String × Nat × Kore.Sentence) := #[]
  let mut es : Array (String × Kore.Sentence) := #[]
  for (me, mk) in e.modules.zip k.modules do
    let (missing, ex) := sentenceDiff mk.sentences me.sentences
    for j in missing do ts := ts.push (mk.name.ident.name, j, mk.sentences[j]!)
    for s in ex do es := es.push (me.name.ident.name, s)
  let stages : List (String × (Kore.Sentence → Option String)) :=
    [("places", fun s => some (Kore.Printer.sentence (Parse.bare s))),
     ("variable names", fun s => some (Parse.alphaKey s)),
     ("order", fun s => some (gapForm s (gapAttrs s))),
     ("attributes", fun s => some (gapForm s [])),
     ("same name", gapName)]
  -- per text sentence its partner (index into es) and stage
  let mut tPair : Array (Option (Nat × String)) := Array.replicate ts.size none
  let mut eUsed : Array Bool := Array.replicate es.size false
  for (st, key) in stages do
    let mut byKey : Std.HashMap String (List Nat) := {}
    for j in [0:es.size] do
      if !eUsed[j]! then
        if let some kk := key es[j]!.2 then byKey := byKey.insert kk (byKey.getD kk [] ++ [j])
    for i in [0:ts.size] do
      if tPair[i]!.isNone then
        if let some kk := key ts[i]!.2.2 then
          match byKey.getD kk [] with
          | j :: rest =>
            byKey := byKey.insert kk rest
            tPair := tPair.set! i (some (j, st)); eUsed := eUsed.set! j true
          | [] => pure ()
  let tally := fun (l : List String) => l.eraseDups.map fun n => (n, l.count n)
  let pairs := (List.range ts.size).filterMap fun i => tPair[i]!.map fun (j, st) => (i, j, st)
  let pairCauses := pairs.map fun (i, j, st) =>
    if st == "attributes" then s!"attributes ({gapAttrDiff ts[i]!.2.2 es[j]!.2})" else st
  let tAlone := (List.range ts.size).filter fun i => tPair[i]!.isNone
  let eAlone := (List.range es.size).filter fun j => !eUsed[j]!
  let kindOf := fun (s : Kore.Sentence) => let (kd, dir) := gapKind P d s; s!"{kd}{if dir then " (direction)" else ""} [{origin s}]"
  IO.println s!"gap {koreFile}: {ts.size} sentences of the text not emitted, {es.size} emitted sentences not in the text"
  IO.println s!"paired, one text sentence with one emitted: {pairs.length}"
  for (n, m) in tally pairCauses do IO.println s!"  {m} {n}"
  IO.println s!"text sentences not paired: {tAlone.length}"
  for (n, m) in tally (tAlone.map fun i => kindOf ts[i]!.2.2) do IO.println s!"  {m} {n}"
  IO.println s!"emitted sentences not paired: {eAlone.length}"
  for (n, m) in tally (eAlone.map fun j => kindOf es[j]!.2) do IO.println s!"  {m} {n}"
  if all then
    for (i, j, st) in pairs do
      IO.println s!"  pair ({st}): {ts[i]!.1} sentence {ts[i]!.2.1}: {clip 200 (Kore.Printer.sentence ts[i]!.2.2)}"
      IO.println s!"      emitted: {clip 200 (Kore.Printer.sentence es[j]!.2)}"
    for i in tAlone do
      IO.println s!"  text alone ({kindOf ts[i]!.2.2}): {ts[i]!.1} sentence {ts[i]!.2.1}: {clip 200 (Kore.Printer.sentence ts[i]!.2.2)}"
    for j in eAlone do
      IO.println s!"  emitted alone ({kindOf es[j]!.2}): {clip 200 (Kore.Printer.sentence es[j]!.2)}"
  -- the text sentences of a kind with a direction that `d` does not hold as written, each with the
  -- reading notes the account gives it (a sentence read in another form, named)
  let held := fun (i : Nat) => match tPair[i]! with
    | some (_, st) => st != "same name"
    | none => false
  let userName := (k.modules.getLast?.map (·.name.ident.name)).getD ""
  let off := Parse.preludeLength k
  let conn := Parse.connReadings k
  let N := Parse.namesOf k
  let keys := Parse.keysAsMember k
  -- the `[owise]` equations read with a premise narrower than the text's
  let narrowed := (Parse.owiseNarrowed k d).map (·.1)
  -- KItem's no-junk axioms read with a generator they do not list
  let tokOmitted := (Parse.tokKItemOmitted k d).map (·.1)
  -- the inert constructor axioms the account finds not induced by `d`'s constructors (`uninduced`):
  -- the others `d` holds as values, written or not
  let uninduced := (Parse.uninduced k d).filterMap (·.index)
  let notesOf := fun (i : Nat) =>
    let (mn, j, s) := ts[i]!
    if mn != userName then [] else
      let n := off + j
      ((match Parse.classify N s with
        | .readAs r => [r.name]
        | .unread r => [s!"unread {r.name}"]
        | .inert r => if Parse.ctorInert? P s |>.isSome then (if uninduced.contains n then [] else [s!"{r.name} induced"]) else [s!"inert {r.name}"]
        | _ => []) ++
      ((conn.lookup n).getD []).map (·.name) ++
      (if (keys.lookup n).isSome then [Parse.ReadingNote.keyFunctionAsMember.name] else []) ++
      (if narrowed.contains n then ["owiseDisjunctNarrower"] else []) ++
      (if tokOmitted.contains n then ["tokKItem"] else [])).eraseDups
  let notHeld := (List.range ts.size).filter fun i => (gapKind P d ts[i]!.2.2).2 && !held i
  let noted := notHeld.filter fun i => !(notesOf i).isEmpty
  let unnoted := notHeld.filter fun i => (notesOf i).isEmpty
  IO.println s!"text sentences of a kind with a direction that d does not hold as written: {notHeld.length}; read in another form with a reading note: {noted.length}{if noted.isEmpty then "" else s!" ({countsOf (noted.flatMap notesOf)})"}; without one (a candidate reader defect): {unnoted.length}"
  for i in noted ++ unnoted do
    let (mn, j, s) := ts[i]!
    let partner := match tPair[i]! with
      | some (jj, _) =>
        let a := (Kore.Printer.sentence s).toList
        let b := (Kore.Printer.sentence es[jj]!.2).toList
        let pos := ((a.zip b).findIdx? fun (p : Char × Char) => p.1 != p.2).getD (min a.length b.length)
        let around := fun (l : List Char) => String.ofList ((l.drop (pos - 60)).take 160)
        s!"; emitted under the same name, the first difference at character {pos}: text …{around a}…, emitted …{around b}…"
      | none => ""
    let ns := notesOf i
    IO.println s!"  {mn} sentence {j} ({(gapKind P d s).1}, {origin s}; {if ns.isEmpty then "no reading note" else s!"read {", ".intercalate ns}"}): {clip 200 (Kore.Printer.sentence s)}{partner}"
  return if unnoted.isEmpty then 0 else 1

/-! ## Agreement with recorded results

A case (one JSON line; test/agree-cases.py builds them) is a KORE text, an input configuration
(KORE), a mode with an optional depth, the expected result (KORE) and where it came from.
`kcore agree CASES.jsonl...` reads each case's text with `parse`, chooses the executable step
(`Executable`: `CExec` where `CExec.execReady` holds, else `Exec` where `ok`, `srReady` and
`matchReady` hold), reads the input and the expected configurations as values with its evaluation
(`valueOf`), runs its step in the case's mode, and compares the two sets of configurations. -/

/-- An executable step and its evaluation, at the fuel `Exec.fuel`. Each lists, for some fuel,
exactly `Step`'s successors on the cores it is chosen for (`CExec.step_iff` under `execReady`,
`Exec.step_iff_of_ok` under `ok`, `srReady`, `matchReady`, both also given `CoherentAll`, which is not
checked here). At the fixed fuel, every successor listed is a `Step` successor; for `CExec` the list
is exactly the `Step` successors where `outOfFuel` is false (`CExec.step_iff_at`, given
`CoherentAll`), which the runs check at every configuration they expand (`runMode`); for `Exec` only
soundness is proved. `ruleMatches` lists, per rule, the step's own matches of its left-hand side at
a configuration, each with its `requires` value at that fuel (`some true`, `some false` for false
or undefined, `none` out of fuel); `evalRhs` evaluates a right-hand side under a match at that
fuel. -/
structure Executable where
  name : String
  successors : GroundTerm → List GroundTerm
  evalT : Term → Option (Option GroundTerm)
  ruleMatches : GroundTerm → List (Rule × List (Subst × Option Bool))
  evalRhs : Subst → Term → Option (Option GroundTerm)

def Executable.cexec (c : Semantics) : Executable :=
  ⟨"CExec", CExec.successors c, CExec.evalT c Exec.fuel [],
   fun x => c.rules.map fun r => (r, CExec.ruleMatches c Exec.fuel r x), CExec.evalT c Exec.fuel⟩

def Executable.exec (c : Semantics) : Executable :=
  ⟨"Exec", Exec.successors c, Exec.evalT c Exec.fuel [],
   fun x => c.rules.map fun r => (r, Exec.ruleMatches c Exec.fuel r x), Exec.evalT c Exec.fuel⟩

/-- Whether some match the step lists at x has its `requires` out of fuel, or its `requires`
`true` and its right-hand side out of fuel: for `CExec`, `CExec.outOfFuel c Exec.fuel x`. -/
def Executable.outOfFuel (ex : Executable) (x : GroundTerm) : Bool :=
  (ex.ruleMatches x).any fun (r, l) => l.any fun (σ, b) => b == Option.none ||
    (b == some true && (ex.evalRhs σ r.rhs).isNone)

/-- What a configuration without a listed successor is, for `CExec` on a core `execReady` accepts:
- `none`: no rule applies, `∀ r ∈ c.rules, NotApplies c r x`, read off the step's matches (every
  match of every rule has the `requires` value `some false`): `CExec.noRule_of_ruleMatches`, at any
  fuel, without coherence;
- `undef`: some rule applies (a match with `requires` `some true`: `CExec.applies_of_ruleMatches`,
  and `CExec.not_notApplies_of_ruleMatches` given `CoherentAll`) and x has no `Step` successor
  (nothing out of fuel and no successor listed: `CExec.noStep_at`, given `CoherentAll`);
- `fuel`: neither, a `requires` or a right-hand side having run out of fuel (`outOfFuel`). -/
inductive NoSucc | none | undef | fuel
  deriving BEq

def Executable.noSucc (ex : Executable) (x : GroundTerm) : NoSucc :=
  let ms := ex.ruleMatches x
  if ms.all fun (_, l) => l.all fun (_, b) => b == some false then .none
  else if ex.outOfFuel x then .fuel
  else .undef

/-! ### The run without the interpretation

The evaluation reads the interpretation of the parameters (`Semantics.hooks`) at three places and
nowhere else: a parameter applied to defined arguments (`Semantics.paramVal`: one of `impl = none`,
or a registry hook's silent point), an interpreted symbol at a silent point where `hook` gives no
value (`Semantics.hookRes`, `fallback`), and a function every clause of which fails
(`Semantics.fnRest`). `Executable.atNone` is the executable step with the evaluation that has no
result there (`none`, as out of fuel: `Cert.hookResC`, `Cert.paramValC`, as `Cert.evalTC` does), and
otherwise the same: the same matcher (`Exec`'s or `CExec`'s), overloading symbols as `CExec`
evaluates them, the same order of clauses and the same fuel. A run made with it either reaches the
judgement the run with the executable reaches (nothing it evaluated read the interpretation) or
stops where a value is the interpretation's (an evaluation without a result is out of fuel to
`runMode` and to `valueOf?`). `kcore agree` judges each case both ways; where the two judgements
differ, the verdict is the one at the interpretation the data carries, `HookParams.none`, and is
named so (`agree-at-none`, `differ-at-none`). Where some parameter is raw, the sorts (`sortOf`) read
the interpretation too, and every verdict is so named. That `atNoneEvalT`'s results are `evalT`'s is
not proved here (it is `Cert.evalTC_sound`'s statement for `Exec`'s evaluation); a judgement of the
two runs that differs where nothing read the interpretation would flag a case wrongly, never pass
one. -/

mutual
  /-- `Exec.evalT` (`ovl` false, `cms` `Exec.clauseMatches c`) or `CExec.evalT` (`ovl` true, `cms`
  `CExec.clauseMatches c`), except that a value of the interpretation has no result. -/
  def atNoneEvalT (c : Semantics) (ovl : Bool) (cms : Clause → List GroundTerm → List Subst) :
      Nat → Subst → Term → Option (Option GroundTerm)
    | 0, _, _ => none
    | _ + 1, σ, .var i => some (σ.lookup i)
    | _ + 1, _, .dv s l => some (some (.dv s l))
    | n + 1, σ, .inj a b t => (atNoneEvalT c ovl cms n σ t).map (·.map (injNormal a b))
    | _ + 1, _, .as _ _ => none
    | n + 1, σ, .app f ts => do
      let rs ← atNoneEvalTs c ovl cms n σ ts
      if c.isCtor f then pure ((allSome rs).map (.ctor f))
      else if isHook f then match allSome rs with
        | none => pure none
        | some vs => Cert.hookResC f vs
      else if c.isParam f then match allSome rs with
        | none => pure none
        | some vs => Cert.paramValC c f vs
      else if ovl && c.isOvl f then pure ((allSome rs).map (c.norm f))
      else match allSome rs with
        | none => pure none
        | some vs => atNoneEvalF c ovl cms n f vs
  def atNoneEvalTs (c : Semantics) (ovl : Bool) (cms : Clause → List GroundTerm → List Subst) :
      Nat → Subst → List Term → Option (List (Option GroundTerm))
    | 0, _, _ => none
    | _ + 1, _, [] => some []
    | n + 1, σ, t :: ts => do pure ((← atNoneEvalT c ovl cms n σ t) :: (← atNoneEvalTs c ovl cms n σ ts))
  def atNoneEvalF (c : Semantics) (ovl : Bool) (cms : Clause → List GroundTerm → List Subst) :
      Nat → Sym → List GroundTerm → Option (Option GroundTerm)
    | 0, _, _ => none
    | n + 1, f, vs => do
      let fn ← c.lookupFn f
      atNoneFirstClause c ovl cms n vs (Exec.byPrio fn.clauses)
  /-- `firstClause`, except that where every clause fails (the function's rest, the
  interpretation's) there is no result. -/
  def atNoneFirstClause (c : Semantics) (ovl : Bool) (cms : Clause → List GroundTerm → List Subst) :
      Nat → List GroundTerm → List Clause → Option (Option GroundTerm)
    | 0, _, _ => none
    | _ + 1, _, [] => none
    | n + 1, vs, cl :: rest =>
      let vals := ((cl :: rest).takeWhile (·.prio == cl.prio)).flatMap fun cl' =>
        (cms cl' vs).map fun σ =>
          (cl', σ, match cl'.req with
            | none => some true
            | some t => (atNoneEvalT c ovl cms n σ t).map Exec.isTrue)
      match vals.findSome? fun (cl', σ, b) => if b == some true then
          (match (match cl'.ens with
            | none => some true
            | some t => (atNoneEvalT c ovl cms n σ t).map Exec.isTrue) with
          | some true => atNoneEvalT c ovl cms n σ cl'.rhs
          | some false => some none
          | none => none)
        else none with
      | some r => some r
      | none =>
        if vals.all (·.2.2 == some false) then
          atNoneFirstClause c ovl cms n vs ((cl :: rest).dropWhile (·.prio == cl.prio))
        else none
end

/-- The executable step `ex` with the evaluation that has no result where a value is the
interpretation's: `rms` lists a rule's matches at a configuration (the step's matcher), `ovl` and
`cms` as in `atNoneEvalT`; the successors as `Exec.successorsN` lists them (each once, as
`CExec.successors`, with `dedup`). -/
def Executable.atNone (ex : Executable) (c : Semantics) (ovl dedup : Bool)
    (cms : Clause → List GroundTerm → List Subst) (rms : Rule → GroundTerm → List Subst) : Executable :=
  let ev := atNoneEvalT c ovl cms Exec.fuel
  let isT := fun (o : Option (Option GroundTerm)) => o.map Exec.isTrue
  let rm := fun (x : GroundTerm) => c.rules.map fun r => (r, (rms r x).map fun σ =>
    (σ, match r.req with | none => some true | some t => isT (ev σ t)))
  let ens := fun (r : Rule) (σ : Subst) => match r.ens with | none => some true | some t => isT (ev σ t)
  let succ := fun (x : GroundTerm) =>
    let applying := (rm x).filter fun (_, l) => l.any fun (_, b) => b != some false
    let ys := match (applying.map (·.1.prio)).min? with
      | none => []
      | some p => (applying.filter (·.1.prio == p)).flatMap fun (r, l) =>
        l.filterMap fun (σ, b) =>
          if b == some true then match ev σ r.rhs with
            | some (some y) => if c.sortOf y == some topCellSort && ens r σ == some true then some y else none
            | _ => none
          else none
    if dedup then ys.foldl (fun acc y => if acc.any (Exec.same · y) then acc else acc ++ [y]) [] else ys
  { name := ex.name, successors := succ, evalT := ev [], ruleMatches := rm, evalRhs := ev }

/-- `CExec` without the interpretation. -/
def Executable.cexecAtNone (c : Semantics) : Executable :=
  (Executable.cexec c).atNone c true true (CExec.clauseMatches c) fun r x => CExec.cmatch c r.vars [r.lhs] [x]

/-- `Exec` without the interpretation. -/
def Executable.execAtNone (c : Semantics) : Executable :=
  (Executable.exec c).atNone c false false (Exec.clauseMatches c) fun r x =>
    (Exec.matchP c (Exec.patFuel [r.lhs]) [] r.lhs x).filter (Exec.wellSorted c r.vars)

/-- What `kcore agree` says of the executables, once per run. -/
def agreeNote : String :=
  "CExec runs where CExec.execReady holds (CExec.step_iff), Exec where only ok, srReady and matchReady hold (Exec.step_iff_of_ok); both theorems take CoherentAll, not checked here. At the fixed fuel Exec.fuel: every successor listed is a Step successor (CExec.successorsN_sound); for CExec the listed successors are exactly the Step successors at every configuration a run expands, since a run stops (not-runnable) at one where CExec.outOfFuel holds (CExec.step_iff_at, given CoherentAll); for Exec only soundness is proved, and a successor could be missed. search-final: the finals are the reached configurations at which no rule applies (N: every match the step lists of every rule has its requires false or undefined; CExec.noRule_of_ruleMatches gives NotApplies for every rule, at any fuel, from execReady alone; conversely CExec.noRule_iff, CExec.noRule_iff_at given CoherentAll), compared with the expected; those at which a rule applies (a listed match with requires true: CExec.applies_of_ruleMatches, CExec.not_notApplies_of_ruleMatches) with no Step successor (CExec.noStep_at, given CoherentAll) (U) are printed apart (undefined), not compared. Not checked here: CoherentAll; the input's evaluation and the expected's are sound at the fixed fuel (evalT_sound). A verdict whose run read the interpretation of the parameters (a parameter's value, a silent point, a function's rest; or a raw parameter's sort: the same run with the evaluation that has no result there, Executable.atNone, judges otherwise) is agree-at-none or differ-at-none, a verdict at HookParams.none only, counted apart from agree and differ"


/-- The names `Parse.term` reads a definition's patterns with, from its semantics: its own sorts
and symbols as numbered, and the registry's names that are also its own symbols (the library
projections it defines) taken as its own. -/
def namesOf (c : Semantics) : Parse.Names :=
  { sorts := c.sortNames, syms := c.symNames, own := c.symNames.filter (regSymNames.contains ·) }

/-- A ground pattern as a value: read as a term with no variable (`Parse.term`, as the reader reads
a rule's right-hand side), then evaluated (the executable's `evalT`), which applies the functions it
names and builds collections in their normal form. -/
def valueOf? (c : Semantics) (ex : Executable) (p : Kore.Pattern) : Except String (Option GroundTerm) := do
  let (t, vs) ← (Parse.term (namesOf c) [] p).mapError fun f =>
    s!"{f.reason.name}{if f.detail.isEmpty then "" else s!" ({f.detail})"}"
  unless vs.isEmpty do throw s!"a pattern with variables ({", ".intercalate (vs.map (·.name))})"
  match ex.evalT t with
  | some v => pure v
  | none => throw "its evaluation runs out of fuel"

def valueOf (c : Semantics) (ex : Executable) (p : Kore.Pattern) : Except String GroundTerm := do
  match ← valueOf? c ex p with
  | some v => pure v
  | none => throw "its evaluation is undefined"

/-- Whether a condition of an expected result holds, its terms read as values (`valueOf?`): a
ground term denotes its value, or nothing where its evaluation is undefined. `\ceil(q)` holds where
`q` has a value; `\equals(a, b)` where `a` and `b` denote the same: the same value, or both nothing;
`\not`, `\and`, `\top`, `\bottom` as written. Any other connective is not read. -/
partial def condHolds (c : Semantics) (ex : Executable) : Kore.Pattern → Except String Bool
  | .ceil _ _ q => return (← valueOf? c ex q).isSome
  | .equals _ _ a b => do
    match ← valueOf? c ex a, ← valueOf? c ex b with
    | some u, some v => return Exec.same u v
    | none, none => return true
    | _, _ => return false
  | .not _ q => return !(← condHolds c ex q)
  | .and _ qs => qs.allM (condHolds c ex)
  | .top _ => return true
  | .bottom _ => return false
  | q => throw s!"a condition KCore does not read: {clip 120 (Kore.Printer.pattern q)}"

/-- The configurations a disjunct of an expected result denotes: `p` (`resultOf`) as a value, or,
for `\and(p, φ)` with φ a condition (a backend's result under ` if …`), that value where φ holds
(`condHolds`) and none where it does not. -/
def expectedOf (c : Semantics) (ex : Executable) (p : Kore.Pattern) : Except String (List GroundTerm) := do
  match p with
  | .and _ [p', φ] =>
    if ← condHolds c ex φ then pure [← valueOf c ex p'] else pure []
  | _ => pure [← valueOf c ex p]

/-- The disjuncts of a result: `\or` flattened, `\bottom` none. -/
partial def disjunctsOf : Kore.Pattern → List Kore.Pattern
  | .or _ ps => ps.flatMap disjunctsOf
  | .bottom _ => []
  | p => [p]

/-- A configuration of a result: a search's `\equals(VarResult, p)`, `p ∧ \top`, or `p`. -/
partial def resultOf : Kore.Pattern → Kore.Pattern
  | .equals _ _ (.var _) p => resultOf p
  | .and _ [p, .top _] => resultOf p
  | .and _ [.top _, p] => resultOf p
  | p => p

def dedupG (l : List GroundTerm) : List GroundTerm :=
  l.foldl (fun acc v => if acc.any (Exec.same · v) then acc else acc ++ [v]) []

def sameSet (a b : List GroundTerm) : Bool :=
  a.all (fun v => b.any (Exec.same v ·)) && b.all (fun v => a.any (Exec.same v ·))

/-- The configurations a mode gives from `x`, at most `cap` configurations expanded, and (second)
the undefined-result configurations a search reached:
- `step`: the successors of `x`;
- `execute`: every path followed until it has no successor or reaches `depth` steps; the
  configurations where the paths end (with or without a rule applying);
- `search-final`: the configurations reachable in at most `depth` steps at which no rule applies
  (`NoSucc.none`); second, those reached at which a rule applies but no successor is listed
  (`NoSucc.undef`); a reached configuration without a listed successor where the evaluation ran out
  of fuel is an error;
- `search-all`: every configuration reachable in at most `depth` steps, `x` included.
A configuration expanded where a `requires` or right-hand side runs out of fuel (`outOfFuel`) is an
error: elsewhere the successors listed are exactly the `Step` successors (`CExec.step_iff_at`). -/
def runMode (ex : Executable) (mode : String) (depth : Option Nat) (x : GroundTerm) (cap : Nat := 20000) :
    Except String (List GroundTerm × List GroundTerm) := do
  let succ := fun s => do
    if ex.outOfFuel s then
      throw "a reached configuration where a requires or right-hand side ran out of fuel: its listed successors may be incomplete"
    pure (ex.successors s)
  if mode == "step" then return (dedupG (← succ x), [])
  unless ["execute", "search-final", "search-all"].contains mode do throw s!"unknown mode {mode}"
  let mut frontier := [x]
  let mut seen := [x]
  let mut out : List GroundTerm := if mode == "search-all" then [x] else []
  let mut undef : List GroundTerm := []
  let mut d := 0
  let mut work := 0
  while !frontier.isEmpty do
    let mut ends : List GroundTerm := []
    let mut next : List GroundTerm := []
    if depth == some d then
      if mode == "execute" then out := out ++ frontier
      else if mode == "search-final" then ends := frontier.filter fun s => (ex.successors s).isEmpty
    else
      for s in frontier do
        work := work + 1
        if work > cap then throw s!"more than {cap} configurations to expand"
        let ss ← succ s
        if ss.isEmpty then
          if mode == "execute" then out := out ++ [s]
          else if mode == "search-final" then ends := ends ++ [s]
        else
          for y in ss do
            if mode == "execute" then next := next ++ [y]
            else if !seen.any (Exec.same · y) then
              seen := seen ++ [y]; next := next ++ [y]
    for s in ends do
      match ex.noSucc s with
      | .none => out := out ++ [s]
      | .undef => undef := undef ++ [s]
      | .fuel => throw "a reached configuration without a listed successor: a requires or right-hand side ran out of fuel"
    if depth == some d then break
    frontier := dedupG next
    if mode == "search-all" then out := out ++ frontier
    d := d + 1
  return (dedupG out, dedupG undef)

/-- A case of a case file, its text's path resolved against the file's directory. -/
structure Case where
  id : String
  definition : String
  input : Option String
  mode : String
  depth : Option Nat
  expected : Option String
  noReference : Option String := none

def readCase (dir : System.FilePath) (j : Lean.Json) : Except String Case := do
  let str (k : String) : Option String := (j.getObjValAs? String k).toOption
  let some id := str "id" | throw "a case without an id"
  let some df := str "definition" | throw s!"{id}: no definition"
  return { id, definition := (dir / df).toString, input := str "input", mode := (str "mode").getD "execute",
           depth := (j.getObjValAs? Nat "depth").toOption, expected := str "expected",
           noReference := str "no_reference" }

def jsonStrs (l : List String) : Lean.Json := Lean.Json.arr (l.map Lean.Json.str).toArray

/-- A case's text read for running: the semantics and the executable step chosen, or why it is not
runnable. `CExec` lists exactly `Step`'s successors (for some fuel) where `CExec.execReady` holds
(`CExec.step_iff`), `Exec` where `ok`, `srReady` and `matchReady` hold (`Exec.step_iff_of_ok`);
`CExec` is chosen where both apply. Elsewhere no theorem says so, and the case is not run as
evidence of KCore's meaning; where `okAll`, `srReady` and `matchReady` hold, the semantics comes
back with the reason, and the case is run anyway with `CExec`, its result said in the reason. A text
the account refuses (the checks `kcore gen` makes after reading) is run anyway too, where
`execReady` holds: the semantics read is not the text's there. -/
def runnable (path : String) : IO (Except String (Semantics × Executable × Option String)) := do
  unless ← System.FilePath.pathExists path do
    return .error s!"no text at {path} (test/corpus.py extracts the corpus)"
  let .ok k := Kore.parseDefinition (← IO.FS.readFile path) | return .error "the text is not KORE"
  match Parse.parse k with
  | .error r => return .error s!"the text is refused by the reader ({r.toText})"
  | .ok d =>
    let c := d.sem
    -- the account's refusals, which `kcore gen` makes too: the text read is not what it states
    -- there (e.g. `functionInPattern`: a left side applying a function symbol), so the case is run
    -- anyway, not judged
    let refused := Parse.accountRefusals k d
    unless refused.isEmpty do
      let why := s!"the account refuses the reading ({"; ".intercalate (refused.map (clip 120 ·.toText))})"
      if CExec.execReady c then return .ok (c, .cexec c, some why)
      return .error why
    if CExec.execReady c then return .ok (c, .cexec c, none)
    let failing := [("ok", c.ok), ("srReady", c.srReady), ("matchReady", c.matchReady)].filter (!·.2)
    if failing.isEmpty then return .ok (c, .exec c, none)
    let why := s!"outside what the executable steps cover: CExec.execReady fails, {", ".intercalate (failing.map (·.1))} fails"
    if c.okAll && c.srReady && c.matchReady then
      return .ok (c, .cexec c, some s!"{why} (`okAll` holds)")
    return .error why

/-- One case's verdict, reason, (when they differ) both results as KORE, and the undefined-result
configurations its search reached, as KORE. -/
def judge (c : Semantics) (ex : Executable) (cs : Case) :
    String × String × List String × List String × List String :=
  let pat (t : String) : Except String Kore.Pattern := (Kore.parsePattern t).mapError (s!"KORE: " ++ ·)
  match cs.expected with
  | none => ("no-reference", cs.noReference.getD "no expected result", [], [], [])
  | some et =>
    match (do
      let some it := cs.input | throw "no input"
      let x ← (do valueOf? c ex (← pat it)).mapError (s!"the input: " ++ ·)
      -- the theorems the runs rest on are about configurations (`Config c`)
      if let some v := x then
        unless c.sortOf v == some topCellSort do throw "the input: its value is not of the top cell's sort"
      let ys ← (do (disjunctsOf (← pat et)).flatMapM fun p => expectedOf c ex (resultOf p)).mapError
        (s!"the expected result: " ++ ·)
      -- an input without a value is no configuration: nothing is reachable from it
      let (zs, us) ← match x with
        | some x => runMode ex cs.mode cs.depth x
        | none => pure ([], [])
      pure (dedupG ys, zs, us, x.isNone) :
        Except String (List GroundTerm × List GroundTerm × List GroundTerm × Bool)) with
    | .error e => ("not-runnable", e, [], [], [])
    | .ok (ys, zs, us, noInput) =>
      let pr := fun (v : GroundTerm) => Kore.Printer.pattern (GroundTerm.kore c v)
      let pre := if noInput then "the input has no value (its evaluation is undefined), so no configuration; " else ""
      let post := if us.isEmpty then "" else s!"; {us.length} undefined-result configurations reached (a rule applies, no successor), not compared"
      if sameSet ys zs then ("agree", s!"{pre}{zs.length} configurations{post}", [], [], us.map pr)
      else ("differ", s!"{pre}{zs.length} configurations by KCore, {ys.length} expected; {(zs.filter fun z => !ys.any (Exec.same z ·)).length} of KCore's not expected, {(ys.filter fun y => !zs.any (Exec.same y ·)).length} expected not KCore's{post}",
        zs.map pr, ys.map pr, us.map pr)

/-- Whether a case's judgement `j` (by `ex`) read the interpretation of the parameters: `none` where
the run without it (`Executable.atNone`) gives the same judgement, else what that run gives. Every
judgement on a semantics with a raw parameter reads it (its sorts are the interpretation's). -/
def atNoneReading (c : Semantics) (ex : Executable) (cs : Case)
    (j : String × String × List String × List String × List String) : Option String :=
  if c.params.any (·.raw) then some "a parameter is raw: its applications' sorts are the interpretation's"
  else
    let exN := if ex.name == "CExec" then Executable.cexecAtNone c else Executable.execAtNone c
    let j' := judge c exN cs
    if j' == j then none
    else some s!"without it the run gives {j'.1}{if j'.2.1.isEmpty then "" else s!": {j'.2.1}"}"

/-- `kcore agree CASES.jsonl...`: first a line `{"note"}` (`agreeNote`: what is proved of the
executables), then one JSON line per case, `{"id", "verdict", "executable", "reason", "kcore",
"expected", "undefined"}`, `executable` the step whose result the verdict compares (`CExec` or `Exec`; empty when the verdict
is not `agree` or `differ`), the verdict
one of `agree`, `differ` (with both results, as KORE), `not-runnable` (with the reason: the text
missing, refused by the reader, or outside what the executable steps cover, with the result of
running it anyway with `CExec` where `okAll` holds; an input or expected pattern KCore
does not read as a value; the mode's bound exceeded) and `no-reference` (no expected result, the
case's `no_reference` text the reason); then a summary line. An input read as a term whose
evaluation is undefined is no configuration, and its result is empty in every mode; an expected
disjunct `\and(p, φ)`, φ a condition (`\ceil`, `\equals`, `\not`, `\and`), is `p`'s value where φ
holds and nothing where it does not (`condHolds`).
In `search-final`, `kcore` is the reached configurations at which no rule applies and `undefined`
those at which a rule applies but no successor is listed (`runMode`), which are not compared.
Each `agree` or `differ` says in `interpretation` whether the run read the interpretation of the
parameters (`read`, `not read`; `atNoneReading`): where it did, the verdict is `agree-at-none` or
`differ-at-none`, a judgement at `HookParams.none` only, outside the counts of `agree` and `differ`
(the summary counts it apart), and the reason says what the run without the interpretation gives.
Exit 1 when a case differs and the run read no interpretation. -/
def agree (files : List String) : IO UInt32 := do
  let mut defs : Std.HashMap String (Except String (Semantics × Executable × Option String)) := {}
  let mut counts : Std.HashMap String Nat := {}
  IO.println (Lean.Json.compress (Lean.Json.mkObj [("note", agreeNote)]))
  for f in files do
    let dir := (System.FilePath.mk f).parent.getD "."
    let lines := (← IO.FS.readFile f).splitOn "\n" |>.filter (!·.trimAscii.isEmpty)
    for line in lines do
      let .ok j := Lean.Json.parse line | IO.eprintln s!"{f}: not JSON: {clip 80 line}"; return 2
      let cs ← match readCase dir j with
        | .ok cs => pure cs
        | .error e => IO.eprintln s!"{f}: {e}"; return 2
      if !defs.contains cs.definition then defs := defs.insert cs.definition (← runnable cs.definition)
      let (verdict, exName, reason, mine, theirs, undef, interp) := match defs.getD cs.definition (.error "") with
        | .error e => ("not-runnable", "", e, [], [], [], "")
        | .ok (c, ex, none) =>
          let j := judge c ex cs
          let (v, r, m, t, u) := j
          if v == "agree" || v == "differ" then
            match atNoneReading c ex cs j with
            | none => (v, ex.name, r, m, t, u, "not read")
            | some w => (v ++ "-at-none", ex.name, s!"{r}; the run read the interpretation of the parameters, so the verdict is at HookParams.none ({w})", m, t, u, "read")
          else (v, "", r, m, t, u, "")
        | .ok (c, ex, some why) =>
          let j := judge c ex cs
          let (v, r, m, t, u) := j
          let v := if (v == "agree" || v == "differ") && (atNoneReading c ex cs j).isSome then v ++ "-at-none" else v
          ("not-runnable", "", s!"{why}; run anyway with {ex.name}: {v}{if r.isEmpty then "" else s!" ({r})"}", m, t, u, "")
      counts := counts.insert verdict (counts.getD verdict 0 + 1)
      IO.println (Lean.Json.compress (Lean.Json.mkObj [("id", cs.id), ("verdict", verdict),
        ("executable", exName), ("interpretation", interp), ("reason", reason), ("kcore", jsonStrs mine), ("expected", jsonStrs theirs), ("undefined", jsonStrs undef)]))
      (← IO.getStdout).flush
  IO.println (Lean.Json.compress (Lean.Json.mkObj [("summary", Lean.Json.mkObj
    (["agree", "differ", "agree-at-none", "differ-at-none", "not-runnable", "no-reference"].map fun v => (v, Lean.Json.num (counts.getD v 0))))]))
  return if counts.getD "differ" 0 > 0 then 1 else 0

/-- Whether `CoherentAll c` is decided on the data: where `coreOK` holds and the deciders name no
agreement (`agreeObligationsI`) and no match independence (`matchObligationsL`), `CoherentAll c`
follows from `clausesAgree_of_IO`, `matchIndependentAll_of_L` and `coherentAll_of_parts`, as in
`fnHyp_of_fnObligations`; otherwise the facts left open are named. -/
def coherentVerdict (c : Semantics) : String × List String :=
  if !c.coreOK then ("not-decided", ["coreOK fails"])
  else
    let nm := fun (f : Sym) => decodeK (c.symName f)
    let opn := c.agreeObligationsI.map (fun f => s!"agreement of {nm f}") ++
      c.matchObligationsL.map (fun (f, i) => s!"match independence of {nm f}, clause {i}")
    if opn.isEmpty then ("decided", []) else ("open", opn)

/-- A reached configuration of an oracle run: its successors, and for none what it is (`NoSucc`). -/
structure Reached where
  config : GroundTerm
  successors : List GroundTerm
  kind : String

/-- The configurations reachable from `x` by `CExec`'s step at the fuel `Exec.fuel`, each with its
successors, at most `cap` expanded; an error where a reached configuration has `outOfFuel` (its
listed successors are then not shown to be `Step`'s). Elsewhere, given `CoherentAll`, the listed
successors are exactly the `Step` successors (`CExec.step_iff_at`); a configuration without one is
`N` where every listed match of every rule has `requires` `some false` (no rule applies:
`CExec.noRule_of_ruleMatches`, from `execReady` alone; `CExec.noRule_iff_at` for the converse) and
`U` otherwise (a rule applies, `CExec.applies_of_ruleMatches`, and no `Step` successor,
`CExec.noStep_at`). -/
def oracleRun (c : Semantics) (x : GroundTerm) (cap : Nat := 20000) : Except String (List Reached) := do
  let ex := Executable.cexec c
  let mut frontier := [x]
  let mut seen := [x]
  let mut out : Array Reached := #[]
  while !frontier.isEmpty do
    let mut next : List GroundTerm := []
    for s in frontier do
      if out.size ≥ cap then throw s!"more than {cap} configurations to expand"
      if ex.outOfFuel s then
        throw "a reached configuration where a requires or right-hand side ran out of fuel (outOfFuel)"
      let ss := dedupG (ex.successors s)
      let kind := if !ss.isEmpty then "step" else match ex.noSucc s with
        | .none => "N" | .undef => "U" | .fuel => "fuel"
      out := out.push ⟨s, ss, kind⟩
      for y in ss do
        if !seen.any (Exec.same · y) then
          seen := seen ++ [y]; next := next ++ [y]
    frontier := next
  return out.toList

/-- One oracle verdict, as a JSON object: KCore's own successors of every configuration reachable
from the input, the sets N (no rule applies) and U (a rule applies, no successor), whether
`CExec.execReady` holds and whether `CoherentAll` is decided (`coherentVerdict`); `oracle` is true
when the reader and the account accept the text, `execReady` holds, the input is a configuration
and no reached configuration has `outOfFuel`, and `exact` says what the lists then rest on. With an
expected result (a case's `expected`), `vs_expected` compares N with it as `kcore agree` does. -/
def oracleOne (path : String) (input : Option String) (expected : Option String) :
    IO (List (String × Lean.Json)) := do
  let fail := fun (why : String) => pure [("oracle", Lean.Json.bool false), ("reason", Lean.Json.str why)]
  unless ← System.FilePath.pathExists path do return ← fail s!"no text at {path}"
  let .ok k := Kore.parseDefinition (← IO.FS.readFile path) | return ← fail "the text is not KORE"
  match Parse.parse k with
  | .error r => fail s!"the text is refused by the reader ({r.toText})"
  | .ok d =>
    let c := d.sem
    let refused := Parse.accountRefusals k d
    let ready := CExec.execReady c
    let (co, opn) := coherentVerdict c
    let head : List (String × Lean.Json) := [("execReady", Lean.Json.bool ready), ("coherent", Lean.Json.str co),
      ("coherent_open", jsonStrs opn), ("fuel", Lean.Json.num Exec.fuel)]
    let why : List String := (if refused.isEmpty then [] else
        [s!"the account refuses the reading ({"; ".intercalate (refused.map (clip 120 ·.toText))})"]) ++
      (if ready then [] else ["CExec.execReady fails"])
    unless ready do return [("oracle", Lean.Json.bool false), ("reason", Lean.Json.str ("; ".intercalate why))] ++ head
    let ex := Executable.cexec c
    let pat (t : String) : Except String Kore.Pattern := (Kore.parsePattern t).mapError (s!"KORE: " ++ ·)
    let pr := fun (v : GroundTerm) => Lean.Json.str (Kore.Printer.pattern (GroundTerm.kore c v))
    let run : Except String (Option (List Reached)) := do
      let some it := input | throw "no input"
      let x ← (do valueOf? c ex (← pat it)).mapError (s!"the input: " ++ ·)
      match x with
      | none => pure none
      | some x =>
        unless c.sortOf x == some topCellSort do throw "the input: its value is not of the top cell's sort"
        some <$> oracleRun c x
    match run with
    | .error e => return [("oracle", Lean.Json.bool false), ("reason", Lean.Json.str ("; ".intercalate (why ++ [e])))] ++ head
    | .ok rs =>
      let rs := rs.getD []
      let ns := (rs.filter (·.kind == "N")).map (·.config)
      let us := (rs.filter (·.kind == "U")).map (·.config)
      let vs : String := match expected with
        | none => "none"
        | some et =>
          match (do (disjunctsOf (← pat et)).flatMapM fun p => expectedOf c ex (resultOf p) :
              Except String (List GroundTerm)) with
          | .error e => s!"not-runnable: the expected result: {e}"
          | .ok ys => if sameSet (dedupG ys) ns then "agree" else "differ"
      let exact := if co == "decided" then "proved (CExec.step_iff_at, noRule_iff_at; CoherentAll decided)"
        else "given CoherentAll (CExec.step_iff_at, noRule_iff_at)"
      return [("oracle", Lean.Json.bool why.isEmpty), ("reason", Lean.Json.str ("; ".intercalate why))] ++ head ++
        [("exact", Lean.Json.str exact), ("input_value", Lean.Json.bool (input.isSome && !rs.isEmpty)),
         ("reached", Lean.Json.num rs.length),
         ("configurations", Lean.Json.arr (rs.map fun r => Lean.Json.mkObj [("config", pr r.config),
            ("kind", Lean.Json.str r.kind), ("successors", Lean.Json.arr (r.successors.map pr).toArray)]).toArray),
         ("N", Lean.Json.arr (ns.map pr).toArray), ("U", Lean.Json.arr (us.map pr).toArray),
         ("vs_expected", Lean.Json.str vs)]

/-- `kcore oracle DEFINITION.kore CONFIG.kore` or `kcore oracle CASES.jsonl...`: KCore's own verdict
(`oracleOne`), one JSON line per definition and initial configuration (per case, with its `id`); it
does not compare with a backend, except `vs_expected` where a case carries an expected result. -/
def oracle (args : List String) : IO UInt32 := do
  match args with
  | [df, cf] =>
    if df.endsWith ".kore" && cf.endsWith ".kore" then
      let fields ← oracleOne df (some (← IO.FS.readFile cf)) none
      IO.println (Lean.Json.compress (Lean.Json.mkObj ([("definition", Lean.Json.str df)] ++ fields)))
      return 0
  | _ => pure ()
  for f in args do
    let dir := (System.FilePath.mk f).parent.getD "."
    let lines := (← IO.FS.readFile f).splitOn "\n" |>.filter (!·.trimAscii.isEmpty)
    for line in lines do
      let .ok j := Lean.Json.parse line | IO.eprintln s!"{f}: not JSON: {clip 80 line}"; return 2
      let cs ← match readCase dir j with
        | .ok cs => pure cs
        | .error e => IO.eprintln s!"{f}: {e}"; return 2
      let fields ← oracleOne cs.definition cs.input cs.expected
      IO.println (Lean.Json.compress (Lean.Json.mkObj ([("id", Lean.Json.str cs.id)] ++ fields)))
      (← IO.getStdout).flush
  return 0

/-- The heads of a right-hand side that `totalTermG tot tp fs` does not accept, each with why. -/
partial def nonTotalHeads (c : Semantics) (tot tp : List Sym) (fs : List (Term × Bool)) : Term → List String
  | .var _ => []
  | .dv _ _ => []
  | .inj _ _ t => nonTotalHeads c tot tp fs t
  | .as _ _ => ["an alias in a right-hand side"]
  | .app f ts =>
    let nm := decodeK (c.symName f)
    let here :=
      if c.headTotalG tot tp fs f ts then []
      else if isHook f then [s!"partial hook {nm}"]
      else match c.lookupParam f with
        | some k => if k.impl.isSome then [s!"parameter {nm} implemented by a registry hook"]
            else [s!"parameter {nm} not declared total"]
        | none => match c.fns.find? (·.label == f) with
            | some _ => [s!"function {nm} not declared total"]
            | none => [s!"{nm}: no function, constructor, hook or parameter"]
    here ++ ts.flatMap (nonTotalHeads c tot tp fs)

/-- `kcore fn-facts KORE`: the facts the `--core` package's deciders leave of `FnHyp`, each with
what its decider did not find: for a call not ranked below, the callees; for a self call not
decreasing, the calls; for totality, the parts of `totalOKP` that fail (the clauses where the
cover fails, the heads of right-hand sides `totalTermG` does not accept); for agreement, the pairs of
clauses `fnExclusiveI` (`fnExclusiveIO` where there are overloading symbols) does not accept. -/
def fnFacts (koreFile : String) : IO UInt32 := do
  let text ← IO.FS.readFile koreFile
  let .ok k := Kore.parseDefinition text | IO.eprintln s!"{koreFile}: KORE read error"; return 1
  let some m := k.modules.getLast? | return 1
  let d ← match Parse.finish m (Parse.scan m.sentences) with
    | .ok d => pure d
    | .error f => IO.eprintln s!"finish: {(f.toRefusal (Parse.preludeLength k) m).toText}"; return 1
  let c := d.sem
  let out := fun (s : String) => do IO.println s; (← IO.getStdout).flush
  let ord := callOrderOf c
  let tp := if c.params.any (·.impl.isNone) then d.totalParams else []
  let nm := fun (f : Sym) => decodeK (c.symName f)
  let labels := c.fns.map (·.label)
  let base := fun (s : String) => ((s.splitOn "/").getLast?.getD s).replace ")" ""
  let locOf := fun (f : Sym) => match (withPres c.fns d.pres.fns).find? (·.1.label == f) with
    | some (_, fp) => if fp.loc.l1 == 0 then "generated" else
        s!"{base ((fp.src.getD d.pres.source).replace "Source(" "")}:{fp.loc.l1}"
    | none => "generated"
  let clLoc := fun (f : Sym) (i : Nat) => match (withPres c.fns d.pres.fns).find? (·.1.label == f) with
    | some (_, fp) => match fp.clauses[i]? with
      | some cp => s!"{base ((cp.src.getD (fp.src.getD d.pres.source)).replace "Source(" "")}:{cp.info.loc.l1}"
      | none => "?"
    | none => "?"
  let showCl := fun (cl : Clause) =>
    let req := match cl.req with | some q => s!" requires {showTerm c cl.vars 8 q}" | none => ""
    let ens := match cl.ens with | some q => s!" ensures {showTerm c cl.vars 8 q}" | none => ""
    s!"[{cl.prio}] ({", ".intercalate (cl.pats.map (showTerm c cl.vars 8))}){req} => {showTerm c cl.vars 5 cl.rhs}{ens}"
  let fnOf := fun (f : Sym) => c.fns.find? (·.label == f)
  let rk := c.rankObligations ord
  let dec := c.decObligationsL
  let tot := c.totalObligationsRP ord tp
  let agr := c.agreeObligationsI
  out s!"{koreFile}: termination {rk.length} + {dec.length}, totality {tot.length}, agreement {agr.length}, match {c.matchObligationsL.length}"
  unless c.clausesPreTop do
    out "a clause's predicate is not \\top (clausesPreTop false): these facts do not give FnHyp, which the --core package's statements take as a hypothesis"
  for f in rk do
    let some fn := fnOf f | continue
    let bad := fn.callees.eraseDups.filter fun g => g != f && labels.contains g && !decide (ord.idxOf g < ord.idxOf f)
    out s!"RANK {nm f} {locOf f}: calls {", ".intercalate (bad.map nm)}"
    for (cl, i) in fn.clauses.zipIdx do
      let calls := bad.flatMap fun g => (callsOf g cl.rhs ++ (cl.req.map (callsOf g)).getD []).map (g, ·)
      unless calls.isEmpty do
        out s!"  clause {i} {clLoc f i}: {showCl cl}"
        for (g, a) in calls do
          out s!"    call {nm g}({", ".intercalate (a.map (showTerm c cl.vars 6))})"
  for f in dec do
    let some fn := fnOf f | continue
    out s!"DEC {nm f} {locOf f}"
    for (cl, i) in fn.clauses.zipIdx do
      let calls := callsOf f cl.rhs ++ (cl.req.map (callsOf f)).getD []
      unless calls.isEmpty do
        out s!"  clause {i} {clLoc f i}: {showCl cl}"
        for a in calls do
          out s!"    call ({", ".intercalate (a.map (showTerm c cl.vars 6))})"
  let heads := c.fns.map Fn.sig
  for f in tot do
    let some fn := fnOf f | continue
    let totL := c.totalLabels
    let cOK := c.covers (Semantics.coverFuel fn) fn.args (c.coverRowsG heads totL tp fn)
    let rhsBad := fn.clauses.flatMap fun cl => nonTotalHeads c totL tp (Det.reqLits cl.req) cl.rhs
    let parts := (if c.shapesOK then [] else ["shapes"]) ++
      (if cOK then [] else ["cover"]) ++ (if rhsBad.isEmpty then [] else ["right sides: " ++ ", ".intercalate rhsBad.eraseDups])
    out s!"TOTAL {nm f} {locOf f}: {"; ".intercalate parts}"
    unless cOK do
      for (cl, i) in fn.clauses.zipIdx do
        out s!"  clause {i} {clLoc f i}: {showCl cl}"
  for f in agr do
    let some fn := fnOf f | continue
    out s!"AGREE {nm f} {locOf f}"
    let idx := fn.clauses.zipIdx
    for ((cl, i), (cl', j)) in pairs idx do
      let ok := if c.ovls.isEmpty then
          c.pairAgreeL heads cl cl' || (cl.prio == cl'.prio && (c.instAgree heads cl cl' || c.instAgree heads cl' cl))
        else c.pairAgreeO heads cl cl'
      unless ok do
        out s!"  pair {i} {clLoc f i} / {j} {clLoc f j}"
        out s!"    {showCl cl}"
        out s!"    {showCl cl'}"
  return 0

/-- What a symbol with no `CExec.role` that is no constructor is, in a pattern. -/
def noRoleKind (c : Semantics) (f : Sym) : String :=
  if (c.lookupFn f).isSome then "a function"
  else if c.isParam f then "a parameter implemented by no collection symbol"
  else if isHook f then "a hook that is no collection pattern symbol"
  else "a symbol of no known kind"

/-- Why `CExec.readyP c vars n p` is false, as a category and a detail; `none` when it is true.
The first failing subpattern in `readyP`'s order. -/
def readyWhy (c : Semantics) (vars : List Srt) : Nat → Term → Option (String × String)
  | 0, _ => some ("out of depth", "")
  | _ + 1, .var _ => none
  | _ + 1, .dv _ _ => none
  | n + 1, .inj _ _ p => readyWhy c vars n p
  | n + 1, .as p _ => readyWhy c vars n p
  | n + 1, .app f ps =>
    if c.isCtor f then ps.findSome? (readyWhy c vars n)
    else match CExec.role c f with
      | some (K, _) => match CExec.flatten c K (Exec.termSize (.app f ps)) (.app f ps) with
        | some parts =>
          let kind := match K with | .map => "map" | .set => "set" | .list => "list" | .rangeMap => "range map"
          let fs := CExec.Part.frames parts
          if CExec.Part.hasOther parts then
            let q := (parts.findSome? fun | .other q => some q | _ => none).getD (.var 0)
            let what := match q with
              | .app g _ => match CExec.role c g with
                | some (K', _) => s!"a {match K' with | .map => "map" | .set => "set" | .list => "list" | .rangeMap => "range map"} pattern"
                | none => if c.isCtor g then "a constructor term" else noRoleKind c g
              | .dv _ _ => "a literal"
              | .inj _ _ _ => "an injection"
              | .as _ _ => "an alias"
              | .var _ => "a variable"
            let qn := match q with | .app g _ => decodeK (c.symName g) | _ => ""
            some (s!"{kind} pattern with {what} at a concatenation's argument", s!"{decodeK (c.symName f)} / {qn}")
          else if fs.length > 1 then
            some (s!"{kind} pattern with {fs.length} frames", decodeK (c.symName f))
          else if !fs.all (fun j => (vars[j]?).isSome) then
            some (s!"{kind} pattern with an undeclared frame", decodeK (c.symName f))
          else (CExec.Part.elems parts).findSome? (·.findSome? (readyWhy c vars n))
        | none => some ("a collection symbol applied to the wrong number of arguments", decodeK (c.symName f))
      | none =>
        if c.isOvl f then ps.findSome? (readyWhy c vars n)
        else some (s!"{noRoleKind c f} in a pattern", decodeK (c.symName f))

/-- `kcore exec-ready definition.kore`: `coreOK`, the conditions the executable matcher of Exec.lean
reads (`ok`, `srReady`, `matchReady`), `CExec.execReady`, `ok`'s conjuncts and `readsConfined`, as `name 0|1`
pairs on one line; then,
for each clause and rule whose left-hand side `execReady` does not accept, and each rule with a
predicate other than a conjunction of `\in` and `\equals` atoms (`CExec.predAtoms`), a
tab-separated line `why`, the reason, its detail, the place. A line `mismatch` where `readyWhy` and `readyP` disagree. -/
def execReadyCmd (koreFile : String) : IO UInt32 := do
  let out := fun (s : String) => do IO.println s; (← IO.getStdout).flush
  let .ok k := Kore.parseDefinition (← IO.FS.readFile koreFile) | IO.eprintln s!"{koreFile}: KORE read error"; return 1
  let d ← match Parse.parse k with
    | .ok d => pure d
    | .error r => IO.eprintln s!"{koreFile}: refused: {r.toText}"; return 1
  let c := d.sem
  let b := fun (x : Bool) => if x then "1" else "0"
  let core := ((coreParts c (tables c)).filter (!·.2)).isEmpty
  out s!"coreOK {b core} ok {b c.ok} srReady {b c.srReady} matchReady {b c.matchReady} sortedOK {b c.sortedOK} execReady {b (CExec.execReady c)} ok.declsOK {b c.declsOK} ok.subsortsOK {b c.subsortsOK} ok.fnsOK {b c.fnsOK} ok.rulesOK {b (c.rules.all c.ruleOK)} matchReadyO {b c.matchReadyO} readsConfined {b c.readsConfined}"
  let check := fun (vars : List Srt) (ps : List Term) (at_ : String) => do
    for p in ps do
      let r := readyWhy c vars (Exec.termSize p) p
      if r.isNone != CExec.readyP c vars (Exec.termSize p) p then out s!"mismatch\t{at_}"
    match ps.findSome? fun p => readyWhy c vars (Exec.termSize p) p with
    | some (cat, det) => out s!"why\t{cat}\t{det}\t{at_}"
    | none => unless binds vars.length (varOccsList ps) do out s!"why\ta variable not bound by the left-hand side\t\t{at_}"
  for (f, fp) in withPres c.fns d.pres.fns do
    for (cl, cp) in withPres f.clauses fp.clauses do
      check cl.vars cl.pats s!"{decodeK (c.symName f.label)}, {cp.label.getD "(no label)"} at {(cp.src.getD (fp.src.getD d.pres.source)).splitOn "/" |>.getLast!}:{cp.info.loc.l1}"
  for f in c.sortPreds do
    for cl in f.clauses do check cl.vars cl.pats s!"sort predicate {decodeK (c.symName f.label)}"
  for (r, rp) in withPres c.rules d.pres.rules do
    let at_ := s!"rule {rp.label.getD "(no label)"} at {(rp.src.getD d.pres.source).splitOn "/" |>.getLast!}:{rp.info.loc.l1}"
    check r.vars [r.lhs] at_
    unless CExec.predAtoms r.pre && CExec.predAtoms r.post do
      out s!"why\ta predicate of the rule (pre or post) other than a conjunction of \\in and \\equals atoms\t\t{at_}"
  return 0

/-- `kcore exec definition.kore config.kore [--steps N] [--fuel F]`: the executable step of
CollExec.lean (collection patterns included) from the configuration the KORE pattern in
`config.kore` denotes. With N = 1 (the default), the successors, each once; with N > 1, the run of
at most N steps, each to the first successor, and the configuration it ends at. -/
def execCmd (koreFile cfgFile : String) (steps fuel : Nat) : IO UInt32 := do
  let out := fun (s : String) => do IO.println s; (← IO.getStdout).flush
  let .ok k := Kore.parseDefinition (← IO.FS.readFile koreFile) | IO.eprintln s!"{koreFile}: KORE read error"; return 1
  let d ← match Parse.parse k with
    | .ok d => pure d
    | .error r => IO.eprintln s!"{koreFile}: refused: {r.toText}"; return 1
  let c := d.sem
  out s!"readiness (CExec.execReady): {if CExec.execReady c then "holds" else "FAILS"}"
  let x ← match CExec.configOfText c (← IO.FS.readFile cfgFile) with
    | .ok x => pure x
    | .error e => IO.eprintln s!"{cfgFile}: {e}"; return 1
  if steps ≤ 1 then
    let ys := (CExec.successorsN c fuel x).foldl
      (fun acc y => if acc.any (Exec.same · y) then acc else acc ++ [y]) []
    out s!"successors: {ys.length}"
    for y in ys do out (CExec.showValue c y)
    if CExec.outOfFuel c fuel x then out "out of fuel: a rule's requires or right-hand side was not evaluated"
  else
    let (path, branched) := CExec.runFrom c fuel steps x
    let last := path.getLast?.getD x
    let stuck := (CExec.successorsN c fuel last).isEmpty
    out s!"steps: {path.length}{if stuck then " (no successor)" else " (bound reached)"}{if branched then ", a step had several successors (the first taken)" else ""}"
    out (CExec.showValue c last)
    if stuck && CExec.outOfFuel c fuel last then out "out of fuel: a rule's requires or right-hand side was not evaluated"
  return 0

/-- `kcore rule-ids KORE`: the rules of KCore's parse by number, one line each, `NUMBER UID`: the
numbers a package generated from the text gives its rules (`c.rules[NUMBER]`) and the `UNIQUE_ID`
of the sentence each is read from, which `readCert` resolves a certificate's rule id with. -/
def ruleIdsCmd (koreFile : String) : IO UInt32 := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile koreFile) | IO.eprintln s!"{koreFile}: KORE read error"; return 1
  let d ← match Parse.parse k with
    | .ok d => pure d
    | .error r => IO.eprintln s!"{koreFile}: refused: {r.toText}"; return 1
  for ((_, rp), i) in (withPres d.sem.rules d.pres.rules).zipIdx do
    IO.println s!"{i} {rp.info.uid}"
  return 0

/-- `kcore generated-eqs KORE`: the equations the account accounts for by its arm for generated
equations alone (`Parse.generatedEqs`), one line each, `eq<TAB>INDEX<TAB>FUNCTION<TAB>KIND<TAB>SHAPE`, KIND what `d` makes of the function. -/
def generatedEqsCmd (koreFile : String) : IO UInt32 := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile koreFile) | IO.eprintln s!"{koreFile}: KORE read error"; return 1
  let d ← match Parse.parse k with
    | .ok d => pure d
    | .error r => IO.eprintln s!"{koreFile}: refused: {r.toText}"; return 1
  let c := d.sem
  let named := fun (ns : List Sym) => ns.map c.symName
  let preds := named (c.sortPreds.map (·.label))
  let fns := named (c.fns.map (·.label))
  let params := named (c.params.map (·.sig.name))
  for (i, f, sh) in Parse.generatedEqs k d do
    -- what `d` makes of the head: a sort predicate (`sortPreds`), a function, a parameter, a
    -- symbol of the registry or of `d` otherwise, or no symbol of `d`
    let tag := if preds.contains f then "sortPred" else if fns.contains f then "fn"
      else if params.contains f then "param" else if regSymNames.contains f then "registry"
      else if c.symNames.contains f then "sym" else "absent"
    IO.println s!"eq\t{i}\t{f}\t{tag}\t{sh}"
  return 0

/-- A term with its symbols and sorts by name (`Semantics.symName`, `Semantics.sortName`), so that
two texts that number them differently print one semantics alike. -/
partial def semFieldsTerm (c : Semantics) : Term → String
  | .var i => s!"V{i}"
  | .app f as => s!"{c.symName f}(" ++ ", ".intercalate (as.map (semFieldsTerm c)) ++ ")"
  | .inj a b t => s!"inj[{c.sortName a},{c.sortName b}](" ++ semFieldsTerm c t ++ ")"
  | .as t i => "(" ++ semFieldsTerm c t ++ s!" as V{i})"
  | .dv s l => s!"dv[{c.sortName s}]({reprStr l})"

/-- A condition, as `semFieldsTerm` prints terms. -/
partial def semFieldsCond (c : Semantics) : Cond → String
  | .top => "top"
  | .bot => "bot"
  | .not p => "not(" ++ semFieldsCond c p ++ ")"
  | .and p q => "and(" ++ semFieldsCond c p ++ ", " ++ semFieldsCond c q ++ ")"
  | .or p q => "or(" ++ semFieldsCond c p ++ ", " ++ semFieldsCond c q ++ ")"
  | .implies p q => "implies(" ++ semFieldsCond c p ++ ", " ++ semFieldsCond c q ++ ")"
  | .ceil s t => s!"ceil[{c.sortName s}](" ++ semFieldsTerm c t ++ ")"
  | .equals s t u => s!"equals[{c.sortName s}](" ++ semFieldsTerm c t ++ ", " ++ semFieldsTerm c u ++ ")"
  | .mem s t u => s!"in[{c.sortName s}](" ++ semFieldsTerm c t ++ ", " ++ semFieldsTerm c u ++ ")"
  | .exMatch ys s p t b => s!"exMatch[{ys.map c.sortName}; {c.sortName s}](" ++ semFieldsTerm c p ++
      ", " ++ semFieldsTerm c t ++ ", " ++ semFieldsCond c b ++ ")"
  | .ex s b => s!"ex[{c.sortName s}](" ++ semFieldsCond c b ++ ")"
  | .all s b => s!"all[{c.sortName s}](" ++ semFieldsCond c b ++ ")"

/-- `kcore sem-fields KORE`: every field of the semantics' functions (`Fn`, with each `Clause`) and
rules (`Rule`), one line per function, clause and rule; one line per sort of `Semantics.userSorts`,
per constructor of `Semantics.ctors` (its argument and result sorts) and per parameter symbol of
`Semantics.params` (every `ParamSig` field: its signature, the registry hook that interprets it or
`none`, and `raw`, `assoc`, `idem`); symbols and sorts by name, the lines sorted (the order of these
lists carries no meaning). Two texts whose lines are equal have equal `Fn`, `Clause`, `Rule`,
`userSorts`, `ctors` and `params` up to that naming. Not printed: `lib`, `userSubsorts`, `pgmSort`,
`colls`, `ovls`, and the hook names of the text (`ParamPres`, the presentation, not `Semantics`). -/
def semFieldsCmd (koreFile : String) : IO UInt32 := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile koreFile) | IO.eprintln s!"{koreFile}: KORE read error"; return 1
  let d ← match Parse.parse k with
    | .ok d => pure d
    | .error r => IO.eprintln s!"{koreFile}: refused: {r.toText}"; return 1
  let c := d.sem
  let t := semFieldsTerm c
  let ot := fun (o : Option Term) => match o with | some x => t x | none => "none"
  let srts := fun (ss : List Srt) => ss.map c.sortName
  let mut out : Array String := #[]
  for f in c.fns do
    let n := c.symName f.label
    out := out.push s!"fn\t{n}\targs={srts f.args}\tresult={c.sortName f.result}\ttotal={f.total}\tclauses={f.clauses.length}"
    for cl in f.clauses do
      out := out.push (s!"clause\t{n}\tprio={cl.prio}\taside={cl.aside}\tvars={srts cl.vars}\tpats=" ++
        ", ".intercalate (cl.pats.map t) ++ s!"\treq={ot cl.req}\trhs={t cl.rhs}\tens={ot cl.ens}" ++
        s!"\texs={cl.exs}\tpre={semFieldsCond c cl.pre}\tpost={semFieldsCond c cl.post}")
  for r in c.rules do
    out := out.push (s!"rule\tprio={r.prio}\tvars={srts r.vars}\tlhs={t r.lhs}\treq={ot r.req}" ++
      s!"\trhs={t r.rhs}\tens={ot r.ens}\texs={r.exs}\tpre={semFieldsCond c r.pre}\tpost={semFieldsCond c r.post}")
  for s in c.userSorts do
    out := out.push s!"sort\t{c.sortName s}"
  for k in c.ctors do
    out := out.push s!"ctor\t{c.symName k.name}\targs={srts k.args}\tresult={c.sortName k.result}"
  for p in c.params do
    let impl := match p.impl with | some g => c.symName g | none => "none"
    out := out.push (s!"param\t{c.symName p.sig.name}\targs={srts p.sig.args}\tresult={c.sortName p.sig.result}" ++
      s!"\timpl={impl}\traw={p.raw}\tassoc={p.assoc}\tidem={p.idem}")
  for l in out.qsort (· < ·) do IO.println l
  return 0

/-! ## `kcore scope-count`: forms the KPROV scope decisions say kompile never writes -/

/-- The counts `kcore scope-count` prints for a text, of its modules other than the prelude's
(findings/KPROV-scope.md sections 1, 3, 5; KPROV.scope-corpus-count). -/
structure ScopeCount where
  iff : Nat := 0
  mu : Nat := 0
  nu : Nat := 0
  next : Nat := 0
  leftAssoc : Nat := 0
  rightAssoc : Nat := 0
  /-- `Pattern.string` in a sentence's pattern (never in an attribute list, never `\dv`'s) -/
  string : Nat := 0
  /-- `Sentence.alias` -/
  alias : Nat := 0
  /-- axioms without `simplification` of the form `\equals(f(…), _)` (under an `\implies` or not)
  with a set variable under the application of f -/
  svarEqn : Nat := 0
  /-- axioms without `simplification` or `symbol-overload` of the form `\equals(c(…), r)` (under an
  `\implies` or not), c a symbol the text declares `constructor`, r (the first conjunct where it is
  an `\and`) no application of such a symbol: an equation headed by a constructor -/
  ctorEqn : Nat := 0
  /-- axioms `∃B. (φ₁ ∧ … ∧ φₙ)`, n ≥ 2, one conjunct equating an application to B
  (`Parse.existentialAxiom?`) -/
  existEqn : Nat := 0
  /-- axioms carrying `smt-lemma` whose pattern holds a `\rewrites` -/
  smtRewrites : Nat := 0

partial def scopePat (c : ScopeCount) (p : Kore.Pattern) : ScopeCount :=
  let sub := fun (c : ScopeCount) (ps : List Kore.Pattern) => ps.foldl scopePat c
  match p with
  | .string _ => { c with string := c.string + 1 }
  | .app _ _ ps | .and _ ps | .or _ ps => sub c ps
  | .not _ q | .exist _ _ q | .forall _ _ q | .ceil _ _ q | .floor _ _ q => scopePat c q
  | .implies _ a b | .equals _ _ a b | .in _ _ a b | .rewrites _ a b => sub c [a, b]
  | .iff _ a b => sub { c with iff := c.iff + 1 } [a, b]
  | .mu _ q => scopePat { c with mu := c.mu + 1 } q
  | .nu _ q => scopePat { c with nu := c.nu + 1 } q
  | .next _ q => scopePat { c with next := c.next + 1 } q
  | .leftAssoc _ _ ps => sub { c with leftAssoc := c.leftAssoc + 1 } ps
  | .rightAssoc _ _ ps => sub { c with rightAssoc := c.rightAssoc + 1 } ps
  | _ => c

partial def hasSetVar : Kore.Pattern → Bool
  | .var (.svar _) => true
  | .app _ _ ps | .and _ ps | .or _ ps | .leftAssoc _ _ ps | .rightAssoc _ _ ps => ps.any hasSetVar
  | .not _ q | .exist _ _ q | .forall _ _ q | .ceil _ _ q | .floor _ _ q | .mu _ q | .nu _ q
  | .next _ q => hasSetVar q
  | .implies _ a b | .iff _ a b | .equals _ _ a b | .in _ _ a b | .rewrites _ a b => hasSetVar a || hasSetVar b
  | _ => false

def svarEqn (a : Kore.Axiom) : Bool :=
  !(a.attributes.any (·.head.ident.name == "simplification")) &&
  match a.pattern with
  | .implies _ _ (.equals _ _ (.app _ _ args) _) | .equals _ _ (.app _ _ args) _ => args.any hasSetVar
  | _ => false

partial def hasRewrites : Kore.Pattern → Bool
  | .rewrites _ _ _ => true
  | .app _ _ ps | .and _ ps | .or _ ps | .leftAssoc _ _ ps | .rightAssoc _ _ ps => ps.any hasRewrites
  | .not _ q | .exist _ _ q | .forall _ _ q | .ceil _ _ q | .floor _ _ q | .mu _ q | .nu _ q
  | .next _ q => hasRewrites q
  | .implies _ a b | .iff _ a b | .equals _ _ a b | .in _ _ a b => hasRewrites a || hasRewrites b
  | _ => false

def scopeHasAttr (a : Kore.Axiom) (n : String) : Bool := a.attributes.any (·.head.ident.name == n)

def ctorEqn (ctors : List String) (a : Kore.Axiom) : Bool :=
  let isCtor := fun (p : Kore.Pattern) => match p with
    | .app h _ _ => ctors.contains h.ident.name
    | _ => false
  let first := fun (r : Kore.Pattern) => match r with
    | .and _ (q :: _) => q
    | q => q
  !scopeHasAttr a "simplification" && !scopeHasAttr a "symbol-overload" &&
  match a.pattern with
  | .implies _ _ (.equals _ _ l r) | .equals _ _ l r => isCtor l && !isCtor (first r)
  | _ => false

def scopeSentence (ctors : List String) (c : ScopeCount) : Kore.Sentence → ScopeCount
  | .alias a => scopePat { c with alias := c.alias + 1 } a.body
  | .axiom a =>
    let c := if svarEqn a then { c with svarEqn := c.svarEqn + 1 } else c
    let c := if ctorEqn ctors a then { c with ctorEqn := c.ctorEqn + 1 } else c
    let c := if (Parse.existentialAxiom? a).isSome then { c with existEqn := c.existEqn + 1 } else c
    let c := if scopeHasAttr a "smt-lemma" && hasRewrites a.pattern then
      { c with smtRewrites := c.smtRewrites + 1 } else c
    scopePat c a.pattern
  | .claim a => scopePat c a.pattern
  | _ => c

/-- `kcore scope-count KORE`: one line of the counts `ScopeCount` holds, over the modules of the
text other than those named as the prelude's (`preludeModules`), and the number of modules counted. -/
def scopeCountCmd (koreFile : String) : IO UInt32 := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile koreFile) | IO.eprintln s!"{koreFile}: KORE read error"; return 1
  let pre := preludeModules.map (·.name)
  let ms := k.modules.filter fun m => !pre.contains m.name
  let ctors := (k.modules.flatMap (·.sentences)).filterMap fun s => match s with
    | .symbol x => if x.attributes.any (·.head.ident.name == "constructor") then some x.symbol.ident.ident.name else none
    | _ => none
  let c := (ms.flatMap (·.sentences)).foldl (scopeSentence ctors) {}
  IO.println s!"modules={ms.length}\tiff={c.iff}\tmu={c.mu}\tnu={c.nu}\tnext={c.next}\tleftAssoc={c.leftAssoc}\trightAssoc={c.rightAssoc}\tstring={c.string}\talias={c.alias}\tsvarEqn={c.svarEqn}\tctorEqn={c.ctorEqn}\texistEqn={c.existEqn}\tsmtRewrites={c.smtRewrites}"
  return 0

/-! ## `kcore sentence-heads`: each sentence's kind, attribute heads, Source and Location -/

/-- The text of a string, one line: tabs and line ends as spaces. -/
def sentenceHeadsOneLine (s : String) : String :=
  s.map fun ch => if ch == '\t' || ch == '\n' || ch == '\r' then ' ' else ch

/-- The sentence's kind (its keyword) and its attributes. -/
def sentenceHeadsOf : Kore.Sentence → String × List Kore.AppPattern
  | .import i => ("import", i.attributes)
  | .sort s => ("sort", s.attributes)
  | .hookedSort s => ("hooked-sort", s.attributes)
  | .symbol s => ("symbol", s.attributes)
  | .hookedSymbol s => ("hooked-symbol", s.attributes)
  | .alias a => ("alias", a.attributes)
  | .axiom a => ("axiom", a.attributes)
  | .claim c => ("claim", c.attributes)

/-- The string argument of the attribute whose head is `head`, or "-". -/
def sentenceHeadsArg (attrs : List Kore.AppPattern) (head : String) : String :=
  match attrs.find? (·.head.ident.name == head) with
  | some { args := [.string v], .. } => sentenceHeadsOneLine v
  | _ => "-"

/-- One line of an attribute list: its heads (comma-separated, in order), the Source and the
Location strings. -/
def sentenceHeadsLine (attrs : List Kore.AppPattern) : String :=
  ",".intercalate (attrs.map (·.head.ident.name)) ++ "\t" ++
    sentenceHeadsArg attrs "org'Stop'kframework'Stop'attributes'Stop'Source" ++ "\t" ++
    sentenceHeadsArg attrs "org'Stop'kframework'Stop'attributes'Stop'Location"

/-- `kcore sentence-heads KORE`: the parsed text's attribute lists, one line each, tab-separated:
`definition HEADS SOURCE LOCATION` for the definition's, then per module (index I from 0)
`module I NAME HEADS SOURCE LOCATION` and per sentence (index J from 0 in its module)
`sentence I J KIND HEADS SOURCE LOCATION`, KIND the sentence's keyword, HEADS the head identifiers
of its attributes (comma-separated, as written), SOURCE and LOCATION the string arguments of its
Source and Location attributes or "-". Then `sentences N`, their number. -/
def sentenceHeadsCmd (koreFile : String) : IO UInt32 := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile koreFile) | IO.eprintln s!"{koreFile}: KORE read error"; return 1
  IO.println s!"definition\t{sentenceHeadsLine k.attributes}"
  let mut n := 0
  for (m, i) in k.modules.zipIdx do
    IO.println s!"module\t{i}\t{sentenceHeadsOneLine m.name.ident.name}\t{sentenceHeadsLine m.attributes}"
    for (s, j) in m.sentences.zipIdx do
      let (kind, attrs) := sentenceHeadsOf s
      IO.println s!"sentence\t{i}\t{j}\t{kind}\t{sentenceHeadsLine attrs}"
      n := n + 1
  IO.println s!"sentences {n}"
  return 0


/-! ## kore.k's `succs` against the executable step (`kk-native`) -/

/-- kore.k's semantics read from its kompiled text at `path` and the symbols `succs` and
`strictHook`, or why not (the text refused, a symbol missing, a number of the embeddings naming
another symbol in it). -/
def kkNativeLoad (path : String) : IO (Except String (Semantics × Sym × Sym × Sym)) := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile path) | return .error s!"{path}: not KORE"
  match Parse.parse k with
  | .error r => return .error s!"{path}: refused by the reader ({r.toText})"
  | .ok kd =>
    let K := kd.sem
    let wrong := KK.Native.embNamesWrong K
    unless wrong.isEmpty do return .error s!"the embeddings' symbols {wrong} have other names in {path}"
    match KK.Native.symOf K KK.Native.succsName, KK.Native.symOf K KK.Native.strictHookName,
        KK.Native.symOf K KK.Native.hookOpName with
    | some sc, some sh, some ho => return .ok (K, sc, sh, ho)
    | _, _, _ => return .error s!"{path}: no succs, strictHook or hookOp"

/-- Argument lists for each interpreted symbol of `hookCodes` and for `=/=Bool`: values of the
sorts its operation reads, where its result differs between neighbouring operations, and lists
of another arity or sort, where it has none. -/
def kkNativeHookArgs (f : Sym) : List (List GroundTerm) :=
  let i := fun (n : Int) => GroundTerm.dv Srt.int (.int n)
  let b := fun (x : Bool) => GroundTerm.dv Srt.bool (.bool x)
  let s := fun (x : String) => GroundTerm.dv Srt.string (.tok x)
  let ints := [-7, -1, 0, 2, 7].map i
  let bools := [b false, b true]
  let m0 := GroundTerm.map Srt.map []
  let m := ((hook mapUpdate [m0, i 2, i 20]).join.bind fun m => (hook mapUpdate [m, i 1, i 10]).join).getD m0
  let s0 := GroundTerm.set Srt.set []
  let st := ((hook setElem [i 3]).join.bind fun a => (hook setUnion [a, .set Srt.set [i 1]]).join).getD s0
  let l := GroundTerm.list Srt.list [i 5, i 6, i 5]
  let pairs := fun (xs : List GroundTerm) => xs.flatMap fun x => xs.map fun y => [x, y]
  let bad := [[], [b true, i 1, i 2, i 3], [s "x"]]
  let vals := [i 1, i 2, b true, s "a", .ctor 0 [], m, st, l]
  let typed : List (List GroundTerm) :=
    if [intAdd, intSub, intMul, intTDiv, intTMod, intLt, intLe, intGt, intGe, intEq, intNe].contains f then
      pairs ints ++ [[b true, i 1]]
    else if [boolAnd, boolOr, boolEq, boolNe].contains f then pairs bools ++ [[i 1, b true]]
    else if f == boolNot then bools.map ([·]) ++ [[i 0]]
    else if f == kIte then bools.map (fun c => [c, i 1, i 2]) ++ [[i 1, i 1, i 2]]
    else if f == mapLookup then [[m, i 1], [m, i 2], [m, i 3], [m0, i 1], [i 1, m]]
    else if f == mapLookupOrDefault then [[m, i 1, i 0], [m, i 3, i 0], [m0, i 3, b true]]
    else if f == mapUpdate then [[m, i 1, i 11], [m, i 3, i 30], [m0, i 1, i 1]]
    else if f == mapRemove then [[m, i 1], [m, i 3], [m0, i 1]]
    else if f == mapInKeys then [[i 1, m], [i 3, m], [i 1, m0], [m, i 1]]
    else if f == mapSize then [[m], [m0], [st]]
    else if f == setIn then [[i 1, st], [i 2, st], [i 1, s0], [st, i 1]]
    else if f == setSize then [[st], [s0], [m]]
    else if f == setUnion then [[st, s0], [st, st], [s0, .set Srt.set [i 2]], [m, st]]
    else if f == listSize then [[l], [.list Srt.list []], [st]]
    else if f == kEq || f == kNe then pairs vals
    else if f == stringEq || f == stringLt then pairs [s "", s "a", s "ab", s "b"] ++ [[i 1, s "a"]]
    else []
  typed ++ bad

/-- `kcore kk-native-hooks KK.kore`: kore.k's `hookOp` has a clause for exactly the codes of
`KK.hookCodes`; `KK.derivedHook` writes codes of that table only; and at the argument lists of
`kkNativeHookArgs`, `strictHook` at each symbol's code (`=/=Bool` through its nested form) gives
`encR` of KCore's `hook`. One line per symbol; exit 1 on any difference. -/
def kkNativeHooks (kkPath : String) : IO UInt32 := do
  match ← kkNativeLoad kkPath with
  | .error e => IO.eprintln s!"kk-native-hooks: {e}"; return 2
  | .ok (K, _, strict, hookOp) =>
    let K0 := K.withHooks HookParams.none
    let mut bad := 0
    let table := KK.hookCodes.map (·.2)
    let inText := KK.Native.hookOpCodes K hookOp
    let same := table.all inText.contains && inText.all table.contains && table.eraseDups.length == table.length
    IO.println s!"codes: hookCodes {table.length}, kore.k's hookOp clauses with a code {inText.length} ({inText.eraseDups.length} codes): {if same then "the same codes" else s!"DIFFER (table only {table.filter (!inText.contains ·)}, text only {inText.filter (!table.contains ·)})"}"
    unless same do bad := bad + 1
    let derived := (hookTable.map (·.1)).filterMap fun f =>
      (KK.derivedHook f [.vr 0, .vr 1]).map fun t => (f, KK.Native.hkCodes t)
    for (f, cs) in derived do
      let ok := cs.all table.contains
      IO.println s!"derivedHook {decodeK (K.symName f)}: codes {cs} {if ok then "in hookCodes" else "NOT in hookCodes"}"
      unless ok do bad := bad + 1
    for f in (KK.hookCodes.map (·.1)) ++ [boolNe] do
      let rs := (kkNativeHookArgs f).map fun vs => (vs, KK.Native.hookCase K0 strict f vs)
      let fails := rs.filter (!·.2.1)
      let defined := (rs.filter fun (vs, _) => (hook f vs).join.isSome).length
      IO.println s!"{decodeK (K.symName f)} ({(KK.opOf f).map toString |>.getD "derived"}): {rs.length - fails.length}/{rs.length} agree, KCore defined at {defined}"
      for (vs, (_, why)) in fails do
        IO.println s!"  DIFFER at {vs.length} argument(s) {reprStr vs |> clip 160}: {why}"
      unless fails.isEmpty do bad := bad + 1
    IO.println s!"{if bad == 0 then "PASS" else "FAIL"} kk-native-hooks"
    return if bad == 0 then 0 else 1

/-- `kcore kk-native KK.kore CASES.jsonl [ID...]`: for each case (`id`, `definition` relative to the
cases file, `input`), the encodable conditions and `execReady` of its text, then at every
configuration reachable from the input at `d₀` (at most 2000), the executable step's successors
and what a configuration without one is (`KK.Native.objAt`) against kore.k's `succs` at
`[embD E, emb (enc x)]` at `K₀` (`KK.Native.kkAt`), with `KK.Native.verdict`. A case may name a
configuration (`reaches`, KORE) that must be a successor at a configuration that agrees. One `case`
line per case, then one indented line per configuration that does not agree. -/
def kkNative (kkPath cases : String) (only : List String) : IO UInt32 := do
  match ← kkNativeLoad kkPath with
  | .error e => IO.eprintln s!"kk-native: {e}"; return 2
  | .ok (K, succs, _, _) =>
    let K0 := K.withHooks HookParams.none
    IO.println s!"kk: {kkPath}: succs {succs}, the embeddings' {KK.Native.embNames.length} symbols named as in Emb.lean, execReady K₀ {CExec.execReady K0}"
    let dir := (System.FilePath.mk cases).parent.getD "."
    let mut differ := 0
    for line in (← IO.FS.readFile cases).splitOn "\n" do
      let .ok j := Lean.Json.parse line | continue
      let .ok id := j.getObjValAs? String "id" | continue
      unless only.isEmpty || only.contains id do continue
      let .ok df := j.getObjValAs? String "definition" | continue
      let .ok input := j.getObjValAs? String "input" | continue
      let path := (dir / df).toString
      let t0 ← IO.monoMsNow
      unless ← System.FilePath.pathExists path do
        IO.println s!"case {id} no-text {path}"; continue
      let .ok k := Kore.parseDefinition (← IO.FS.readFile path) | IO.println s!"case {id} not-KORE"; continue
      match Parse.parse k with
      | .error r => IO.println s!"case {id} refused ({clip 120 r.toText})"
      | .ok dd =>
        let d := dd.sem
        let ready := CExec.execReady d
        match KK.encDef d with
        | none => IO.println s!"case {id} outside-encDef execReady={ready} ({"; ".intercalate (KK.Native.outsideWhy d)})"
        | some E =>
          let d0 := d.withHooks HookParams.none
          let pr := fun (v : GroundTerm) => clip 400 (Kore.Printer.pattern (GroundTerm.kore d v))
          match (do KK.Native.valueOf d0 (← (Kore.parsePattern input).mapError (s!"KORE: " ++ ·))) with
          | .error e => IO.println s!"case {id} no-input ({e})"
          | .ok none => IO.println s!"case {id} no-configuration execReady={ready} (the input's evaluation at d₀ is undefined)"
          | .ok (some x) =>
            let mut frontier := [x]
            let mut seen := [x]
            let mut rows : Array (GroundTerm × String × String) := #[]
            let mut agreed : List GroundTerm := []
            while !frontier.isEmpty && rows.size < 2000 do
              let mut next : List GroundTerm := []
              for c in frontier do
                let o := KK.Native.objAt d0 c
                let (v, why) := KK.Native.verdict o (KK.Native.kkAt K0 succs E c)
                rows := rows.push (c, v, why)
                let ys := match o with | .step ys => ys | _ => []
                if v == "agree" then agreed := agreed ++ ys
                for y in ys do
                  if !seen.any (Exec.same · y) then
                    seen := seen ++ [y]; next := next ++ [y]
              frontier := next
            let cnt := fun (v : String) => (rows.filter (·.2.1 == v)).size
            let kinds := fun (w : String) => (rows.filter fun r => r.2.1 == "agree" && r.2.2.startsWith w &&
              !(w == "next(" && r.2.2.startsWith "next(0), a rule")).size
            let dt := (← IO.monoMsNow) - t0
            -- `reaches`: a configuration that must be the successor of a configuration that agrees
            let reaches : String := match j.getObjValAs? String "reaches" with
              | .error _ => ""
              | .ok r => match (do KK.Native.valueOf d0 (← (Kore.parsePattern r).mapError (s!"KORE: " ++ ·))) with
                | .ok (some y) => if agreed.any (Exec.same · y) then " reaches=yes" else " reaches=no"
                | _ => " reaches=unreadable"
            IO.println s!"case {id} execReady={ready} configurations={rows.size}{if frontier.isEmpty then "" else "+ (capped)"} agree={cnt "agree"} (next {kinds "next("} stuck {kinds "stuck"} next-empty {kinds "next(0), a rule"}) differ={cnt "differ"} no-verdict={cnt "no-verdict"}{reaches} ms={dt}"
            for ((c, v, why), n) in rows.toList.zipIdx do
              if v != "agree" then IO.println s!"  {v} at configuration {n}: {why}: {pr c}"
            differ := differ + cnt "differ"
    return if differ == 0 then 0 else 1

/-! ## `kcore encodable` -/

/-- The eleven conjuncts of `KK.encodable`, in its order, by name. -/
def encodableParts (c : Semantics) : List (String × Bool) :=
  [("ovlsOK", KK.ovlsOK c), ("paramsOK", KK.paramsOK c), ("appsOK", KK.appsOK c),
   ("headsOK", KK.headsOK c), ("litsOK", KK.litsOK c), ("subsortsOK", KK.subsortsOK c),
   ("colPatsOK", KK.colPatsOK c), ("asOK", KK.asOK c), ("ensOK", KK.ensOK c),
   ("shapesOK", KK.shapesOK c), ("collFormOK", KK.collFormOK c)]

/-- The library modules a KORE text holds a sentence of (the reader's `moduleAt` of each builtin
sentence's source and line, and the scan's own builtin modules), by name, in the library's order. -/
def encodableModules (k : Kore.Definition) : List String :=
  match k.modules.getLast? with
  | none => []
  | some m =>
    let S := Parse.scan m.sentences
    let mods := S.builtin.filterMap (fun (s, l) => moduleAt s l) ++ S.kbuiltin
    ((List.range library.length).filter mods.contains).filterMap fun i => library[i]?.map (·.name)

/-- A sentence's declared name, `hook` attribute and whether it declares sort parameters, where it
has a `hook` attribute. -/
def encodableHookOf : Kore.Sentence → Option (String × String × Bool)
  | .hookedSymbol s => (KoreAML.Parse.attrStr? s.attributes "hook").map
      (s.symbol.ident.ident.name, ·, !s.symbol.sortVars.isEmpty)
  | .symbol s => (KoreAML.Parse.attrStr? s.attributes "hook").map
      (s.symbol.ident.ident.name, ·, !s.symbol.sortVars.isEmpty)
  | .hookedSort s => (KoreAML.Parse.attrStr? s.attributes "hook").map (s.sort.ident.name, ·, !s.sortVars.isEmpty)
  | .sort s => (KoreAML.Parse.attrStr? s.attributes "hook").map (s.sort.ident.name, ·, !s.sortVars.isEmpty)
  | _ => none

/-- Whether a library declaration with the hook `h` declares sort parameters: the reader reads an
application of such a symbol at an instance as a parameter symbol whose `impl` is the hook's
(KCORE-SPEC.md Q11), so `KK.paramsOK` judges it, not `KK.readApp`. -/
def encodableHookParametric (h : String) : Bool :=
  (List.range library.length).any fun i =>
    (moduleText false i).any fun s => match encodableHookOf s with
      | some (_, h', p) => h' == h && p
      | none => false

/-- A composition `KK.derivedHook` writes, from its value at the empty argument list: each code
with the hook `KK.hookCodes` gives it, and `ARGS` where the arguments' forms go (`derivedHook`
places the argument list unchanged as its innermost list). -/
partial def derivedFormShow : KK.T → String
  | .hk o [] => s!"hk {o} {codeHook o} ARGS"
  | .hk o as => s!"hk {o} {codeHook o} [{", ".intercalate (as.map derivedFormShow)}]"
  | _ => "?"
where codeHook (o : Int) : String :=
  ((KK.hookCodes.find? (·.2 == o)).bind fun (g, _) => (regHookNames.find? (·.1 == g)).map (·.2)).getD "?"

/-- Where `KK.readApp` gives an application of the registered hook `f` a `kore.k` form, whatever its
arguments' forms: as a collection construction (`KK.libCollOf`), an operation code
(`KK.hookCodes`) or a composition of codes (`KK.derivedHook`, written out by `derivedFormShow`);
`none` where it gives none. -/
def encodableHookForm (f : Sym) : Option String :=
  if isHook f then
    match KK.libCollOf f, KK.opOf f, KK.derivedHook f [] with
    | some _, _, _ => some "KK.libCollOf"
    | none, some o, _ => some s!"KK.hookCodes {o}"
    | none, none, some t => some s!"KK.derivedHook {derivedFormShow t}"
    | none, none, none => none
  else none

/-- A registry sort's form in `kore.k`: a library collection sort has one where its unit symbol
has a form (`KK.libCollOf`); another sort where `KK.litsOK` admits it (not `Float`) and its
literals, read by `Parse.lit?` (whose literal kind is fixed by the sort), have one (`KK.encLit`).
The Bool that fails otherwise: `appsOK` (no construction of the collection has a form) or
`litsOK`. -/
def encodableSortForm (s : Srt) : Except String String :=
  match builtinColls.find? (·.sort == s) with
  | some k => if (KK.libCollOf k.unit).isSome then .ok "KK.libCollOf" else .error "appsOK"
  | none =>
    let sample := if s == Srt.int then "0" else if s == Srt.bool then "true" else "a"
    if s != Srt.float && ((Parse.lit? s sample).bind (KK.encLit s)).isSome then .ok "KK.encLit"
    else .error "litsOK"

/-- `kcore encodable definition.kore`: one JSON line, `KK.encodable` of the text's semantics
(`encodable`), each of its eleven conjuncts by name, and the library modules the text holds a
sentence of (`modules`). `kcore encodable --library`: the tables a row of a hook, a hooked sort or
a library module is judged by, one tab-separated line each: `hook NAME covered FORM` or
`hook NAME refused BOOL` for each registered hook (`regHookNames`): one whose library declaration
declares sort parameters (`encodableHookParametric`) and that is no collection symbol is refused
`paramsOK`, which admits a parameter only with a collection `impl`; the others by
`encodableHookForm` (`appsOK` where it gives none);
`sort NAME covered FORM` or `sort NAME refused BOOL` for each registry sort
(`encodableSortForm`); `module NAME SOURCE` for each library module (its file, as its sentences'
`Source` reads), followed by `mhook MODULE HOOK DECL`
for each declaration of its text with a `hook` attribute, in text order. -/
def encodableCmd (koreFile : String) : IO UInt32 := do
  let out := fun (s : String) => do IO.println s; (← IO.getStdout).flush
  if koreFile == "--library" then
    for (f, h) in regHookNames do
      if encodableHookParametric h && (KK.libCollOf f).isNone then out s!"hook\t{h}\trefused\tparamsOK"
      else match encodableHookForm f with
        | some form => out s!"hook\t{h}\tcovered\t{form}"
        | none => out s!"hook\t{h}\trefused\tappsOK"
    for (n, s) in regSortNames.zipIdx do
      match encodableSortForm s with
      | .ok form => out s!"sort\t{n}\tcovered\t{form}"
      | .error b => out s!"sort\t{n}\trefused\t{b}"
    for (m, i) in library.zipIdx do
      out s!"module\t{m.name}\t{m.src}"
      for s in moduleText false i do
        if let some (d, h, _) := encodableHookOf s then out s!"mhook\t{m.name}\t{h}\t{d}"
    return 0
  let .ok k := Kore.parseDefinition (← IO.FS.readFile koreFile) | IO.eprintln s!"{koreFile}: KORE read error"; return 1
  let d ← match Parse.parse k with
    | .ok d => pure d
    | .error r => IO.eprintln s!"{koreFile}: refused: {r.toText}"; return 1
  let c := d.sem
  let parts := encodableParts c
  let all := parts.all (·.2)
  if all != KK.encodable c then IO.eprintln "encodable: the conjuncts differ from KK.encodable"; return 1
  let fields := parts.map (fun (n, b) => (n, Lean.Json.bool b)) ++
    [("encodable", Lean.Json.bool (KK.encodable c)), ("modules", jsonStrs (encodableModules k))]
  out (Lean.Json.compress (Lean.Json.mkObj fields))
  return 0

end KcoreGen

def main (argv : List String) : IO UInt32 := do
  match argv with
  | ["generated-eqs", kore] => KcoreGen.generatedEqsCmd kore
  | ["sem-fields", kore] => KcoreGen.semFieldsCmd kore
  | ["scope-count", kore] => KcoreGen.scopeCountCmd kore
  | ["sentence-heads", kore] => KcoreGen.sentenceHeadsCmd kore
  | ["account", kore] => KcoreGen.account kore
  | ["wf-parts", kore] => KcoreGen.wfParts kore
  | ["roundtrip", kore] => KcoreGen.roundTrip kore
  | ["gap", kore] => KcoreGen.gapCmd kore false
  | ["gap", kore, "--all"] => KcoreGen.gapCmd kore true
  | "agree" :: files@(_ :: _) => KcoreGen.agree files
  | "oracle" :: args@(_ :: _) => KcoreGen.oracle args
  | ["kk-native-hooks", kk] => KcoreGen.kkNativeHooks kk
  | "kk-native" :: kk :: cases :: only => KcoreGen.kkNative kk cases only
  | ["fn-facts", kore] => KcoreGen.fnFacts kore
  | ["exec-ready", kore] => KcoreGen.execReadyCmd kore
  | ["rule-ids", kore] => KcoreGen.ruleIdsCmd kore
  | ["encodable", kore] => KcoreGen.encodableCmd kore
  | "exec" :: kore :: cfg :: rest =>
    let num := fun (flag : String) (dflt : Nat) =>
      ((rest.zip (rest.drop 1)).find? (·.1 == flag)).bind (·.2.toNat?) |>.getD dflt
    KcoreGen.execCmd kore cfg (num "--steps" 1) (num "--fuel" Exec.fuel)
  | "gen" :: kore :: out :: ns :: rest =>
    -- `--cert NAME=RUN.json`: krust's run as a certificate module `NS.Certs.NAME`
    let certs := (rest.zip (rest.drop 1)).filterMap fun (f, v) =>
      if f == "--cert" then match v.splitOn "=" with | [n, p] => some (n, p) | _ => none else none
    -- `--high CELL`: noninterference for the cell CELL kept secret (`NS.Kinds.NI`)
    let high := (rest.zip (rest.drop 1)).filterMap fun (f, v) => if f == "--high" then some v else none
    -- `--keyed CELL`: the map cell CELL secret except at the keys the observer is given
    let keyed := (rest.zip (rest.drop 1)).filterMap fun (f, v) => if f == "--keyed" then some v else none
    -- `--tie`: the tie's modules too (`NS.Tie.*`, `tie.txt`)
    -- `--wf`: without the tie, `NS.Wf.*` (`wf defn`) and `NS.Sound`
    -- `--core`: without the tie and `wf`, `NS.CoreOK.*` (`coreOK` by its conjuncts) and `NS.Sound`
    -- (`sound_hyp`, `complete_hyp`)
    -- `--no-syntax` (with `--core`): no `NS.Syntax`
    -- `--as-not-plain`: the text stated for a definition that is not `plain`, whether or not it is
    -- (the branch test/not-plain.sh builds)
    KcoreGen.gen kore out ns (certs := certs) (high := high) (keyed := keyed) (tie := rest.contains "--tie")
      (wfMods := rest.contains "--wf") (core := rest.contains "--core") (withSyntax := !rest.contains "--no-syntax")
      (asNotPlain := rest.contains "--as-not-plain")
  | _ => IO.eprintln "usage: kcore gen definition.kore OUTDIR NAME [--tie | --wf | --core [--no-syntax]] [--as-not-plain] [--cert NAME=RUN.json]... [--high CELL]... [--keyed CELL]...\n       kcore account definition.kore\n       kcore wf-parts definition.kore\n       kcore roundtrip definition.kore\n       kcore gap definition.kore [--all]\n       kcore agree CASES.jsonl...\n       kcore oracle definition.kore config.kore | kcore oracle CASES.jsonl...\n       kcore kk-native KK.kore CASES.jsonl [ID...]\n       kcore kk-native-hooks KK.kore\n       kcore exec definition.kore config.kore [--steps N] [--fuel F]\n       kcore exec-ready definition.kore\n       kcore rule-ids definition.kore\n       kcore sem-fields definition.kore\n       kcore scope-count definition.kore\n       kcore sentence-heads definition.kore\n       kcore encodable definition.kore | kcore encodable --library"; return 2
