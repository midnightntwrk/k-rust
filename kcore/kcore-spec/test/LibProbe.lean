/-
  The library's sentences about interpreted hooked symbols, evaluated at values against Γ's
  graphs (`hook`, `silent`). Native evaluation only (`#eval`), no kernel proof.
  Run from the package root: `lake env lean test/LibProbe.lean`.

  For a kompile text, each axiom of the user module is put in one of four classes (TIE-0's rows):
  - 9: `functional` of a hooked symbol (the sort-parametric `ite{S}`'s among them);
  - 15: a collection law (`assoc`, `unit`; inert `collectionLaw`);
  - 17: a library equation (builtin source, read, not `simplification`, not `functional`);
  - 18: a library `simplification` (builtin source), and an inert `simplification`.
  A sentence of these classes that applies a symbol Γ does not have (`kernelSyms`) is counted and
  not probed. Each other one is evaluated at every point of a grid of values of its variables'
  sorts, an element variable at each value, a set variable at ∅ and at each value's singleton.
  A sentence with a free set variable is then evaluated at the points where some set variable holds
  two values of the grid and each other set variable ∅, one value or two (`probeTwo`); what fails
  there and at no point of the first grid is reported apart (`Two`).

  The evaluation is Γ's: an application at sets of values denotes the values of the symbol at each
  choice of one value per argument, and `\equals` holds where both sides denote the same set;
  a value of a constructor applied to values is that term; of an
  interpreted symbol, `hook`'s value; where `hook` gives none and the point is not silent, no
  value (ΓDomains states ⊥); at a silent point (`silent`) ΓFallback states the interpretation's
  value `fallback`, which is no value under `HookParams.none` (its `app` gives none). So the probe
  reads a silent point three ways: as `HookParams.none` (no value), and as the two interpretations
  giving, at every silent point, the first (`pick 0`) or the second (`pick 1`) grid value of the
  symbol's result sort; each is an interpretation (`HookParams.app` is any function, `fallback`
  keeps a value of the result sort). A parameter symbol is read by `paramVal` and a function by
  `Exec.evalF`, both under `HookParams.none`; a point reaching one is marked.

  A sentence holds at a point where its pattern denotes every element (`\top`): `\implies` with
  a premise that does not hold holds; `\equals` holds where both sides denote the same (no value
  and no value, one value and the same value); `\exists Val. Val = t` (the `functional` sentence)
  holds where `t` has one value. A point where the sentence fails and no silent point, parameter
  or function rest was reached is a counterexample for every interpretation: Γ with the sentence
  has no model. A sentence's sort variables (`R`, `Q0`) are not instantiated: its predicates denote
  every element or none in any sort.

  Grids: Int -3 … 3 and 2^64 + 1 (a sentence applying `<<Int` or `>>Int` without 2^64 + 1, a shift
  amount of which names a number of that many bits); Bool both; KItem the injections of 0, 1, 2, true and of a user
  constructor of one Int argument applied to 0; K `.K` and four sequences; Map, Set, List six
  values each over the KItems 0, 1, 2 (empty, one entry, two, overlapping and disjoint); RangeMap
  six values over the same KItems (empty, `[0, 2)`, `[2, 3)` of the same value, which concatenation
  merges with it, two touching ranges of different values, `[1, 3)`, which overlaps three of them,
  and `[3, 5)`);
  String "", "a", "ab", "é∀"; Float binary32's 1.0, largest finite, ∞, NaN, `p1x2`'s 1.0, ∞,
  NaN and one value of `p2x1` (one exponent bit); Bytes three values; Endianness `LE`, `BE` and
  Signedness `Signed`, `Unsigned`.

  `check` runs the probe on `ens.kompile.kore` and on kompile's text of kimp (`ref-kimp.kore`) and
  compares the per-class counts with `expected`, and what the points with a two-element set find
  with `expectedTwo`; set idempotence (row 16) is probed as the control.
  `checkFlt` runs it on `silentflt.kompile.kore` (FLOAT, STRING, BYTES, SET) with two more readings,
  interpretations meeting `Semantics.silentTotal` that give no value at the other silent points,
  and compares with `expectedFlt`. Both add two readings: `HookParams.lib` (its value, through
  `Semantics.fallback`), and `hash`, which gives a silent point one of the first two grid values of
  the result sort by a hash of the symbol and the arguments (so that two silent points of a sort
  have different values). Both check that the conditions on the interpretation are closed
  (`Reads`, `readsOK`): a sentence that reads the interpretation at a probed point is a `functional`
  sentence of a symbol of `totalSilentKeys` or at a line of `libSentences`, reads it only where its
  left side is at a silent point, and every sentence at a line of `libSentences` that the text holds
  and the probe evaluates reads it; and that under `HookParams.lib` only the control fails. One
  sentence is excepted from both (`unmet`): `countAllOccurrences`' second equation at the empty
  needle, which no interpretation that gives the count a value there meets. Two lines of
  `libSentences` are outside what the probe evaluates: `findChar`'s equation (1891), which it does
  not probe (it applies `ite{Int}`, a symbol Γ does not have), and `sqrtFloat`'s (1671), which applies
  `rootFloat`, no symbol of Γ in these texts. A collection law carries no line of its own: the probe
  names it by its symbol, and puts the law generated from a symbol's `assoc` attribute at the line
  of the symbol's declaration (`declPlace`, `Res.lawPlace`), so that RANGEMAP's associativity is at
  line 508, `rangeMapAssocEq`'s line of `libSentences`.

  A sentence of these classes that applies a symbol Γ does not have is printed with that reason
  (`applies symbols Γ does not have`), as silentflt's `Int2Bytes` equations at three arguments
  (228 to 232, `Int2BytesNoLen`): that is the tie's account of the sentence, no direction, which
  test/LibEvStrFlt.lean states in the kernel (`int2BytesNoLen_absent`). `kcore account` counts the
  same sentences under `read [builtin]`: that is the reader's classification (how a sentence is
  consumed: as the library's text), not a direction, and it agrees with the tie's: the library's
  text is read, and Γ has no symbol `Int2BytesNoLen`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.LibProbe

open KCore KCore.Parse KCore.Faithful KoreAML

/-- What a pattern denotes at a point: nothing, one value, two or more distinct values (`many`), or
every element (`\top`, a predicate that holds). -/
inductive D where
  | bot
  | val (v : GroundTerm)
  | many (vs : List GroundTerm)
  | top
  deriving Inhabited

def hasV (vs : List GroundTerm) (v : GroundTerm) : Bool := vs.any (GroundTerm.cmp · v == .eq)

/-- The values a term denotes; none for `\top`. -/
def D.elems : D → Option (List GroundTerm)
  | .bot => some []
  | .val v => some [v]
  | .many vs => some vs
  | .top => none

/-- The set of the values `vs`. -/
def D.ofElems (vs : List GroundTerm) : D :=
  match vs.foldl (fun acc v => if hasV acc v then acc else acc ++ [v]) [] with
  | [] => .bot
  | [v] => .val v
  | ws => .many ws

def D.isMany : D → Bool
  | .many _ => true
  | _ => false

def D.same : D → D → Bool
  | .top, .top => true
  | a, b => match a.elems, b.elems with
    | some xs, some ys => xs.all (hasV ys) && ys.all (hasV xs)
    | _, _ => false

def D.meet : D → D → D
  | .top, d | d, .top => d
  | a, b => match a.elems, b.elems with
    | some xs, some ys => D.ofElems (xs.filter (hasV ys))
    | _, _ => .bot

/-- How a silent point is read: `HookParams.none`, or the interpretation giving the i-th grid value
of the result sort. -/
inductive Mode where
  | none
  | pick (i : Nat)
  /-- the i-th grid value at the silent points of the symbols `ks`, no value at the others -/
  | only (ks : List Sym) (i : Nat)
  /-- `HookParams.lib`'s value (`Semantics.fallback` under it) -/
  | lib
  /-- one of the first two grid values of the result sort, chosen by a hash of the symbol and the
  arguments: an interpretation that gives two silent points of a sort different values -/
  | hash
  deriving Inhabited, BEq

def Mode.name : Mode → String
  | .none => "H=none"
  | .pick i => s!"H=pick{i}"
  | .only _ i => s!"H=only{i}"
  | .lib => "H=lib"
  | .hash => "H=hash"

/-- What a point's evaluation reached that depends on the interpretation. -/
structure Fl where
  silent : List String := []
  param : List String := []
  deriving Inhabited

abbrev M := StateT Fl (Except String)

instance : Inhabited (M D) := ⟨throw "unreachable"⟩

/-! ## Values -/

def iK (i : Int) : GroundTerm := .inj Srt.int Srt.kitem (int i)
def bK (b : Bool) : GroundTerm := .inj Srt.bool Srt.kitem (bool b)
def kOf (ks : List GroundTerm) : GroundTerm := ks.foldr (fun a b => .ctor kseq [a, b]) (.ctor dotk [])

def ints : List Int := [-3, -2, -1, 0, 1, 2, 3, 18446744073709551617]

/-- A user constructor of one Int argument whose sort is below KItem, applied to 0, as a KItem. -/
def userItem (c : Semantics) : List GroundTerm :=
  match c.ctors.find? (fun k => k.args == [Srt.int] && c.sortOf (.inj k.result Srt.kitem (.ctor k.name [int 0])) == some Srt.kitem) with
  | some k => [.inj k.result Srt.kitem (.ctor k.name [int 0])]
  | none => []

def mapV (es : List (Int × Int)) : GroundTerm :=
  .map Srt.map (es.foldl (fun m (k, v) => insertE (iK k) (iK v) m) [])
def setV (es : List Int) : GroundTerm := .set Srt.set (es.foldr (fun k s => insertS (iK k) s) [])
def listV (es : List Int) : GroundTerm := .list Srt.list (es.map iK)
/-- The range map of the intervals `[a, b) |-> v` (`es` the triples (a, b, v), in the order of their
lower bounds, maximal). -/
def rangeMapV (es : List (Int × Int × Int)) : GroundTerm := rmV (es.map fun (a, b, v) => (rangeT a b, iK v))

/-- Float values (precision, exponent width, encoding): binary32's 1.0, the largest finite value,
+∞ and NaN; `p1x2`'s (a format with a field of 1, `KFloat.thinOK`) 1.0, ∞ and NaN; and the `p2x1`
encoding 1 (sign 0, the one exponent bit 0, the fraction bit 1), of a format with one exponent bit,
at which no Float has a datum (`asDatum`), so that the comparisons are silent there. -/
def floats : List (Nat × Nat × Nat) :=
  [(24, 8, 0x3F800000), (24, 8, 0x7F7FFFFF), (24, 8, 0x7F800000), (24, 8, 0x7FC00000),
   (1, 2, 1), (1, 2, 3), (1, 2, 8), (2, 1, 1)]

/-- The grid of values of a sort (each checked to be of it); none for a sort without one. -/
def gridOf (c : Semantics) (s : Srt) (small : Bool := false) : Option (List GroundTerm) :=
  let raw : Option (List GroundTerm) :=
    if s == Srt.int then some ((if small then ints.filter (·.natAbs ≤ 3) else ints).map int)
    else if s == Srt.bool then some [bool true, bool false]
    else if s == Srt.kitem then some ([iK 0, iK 1, iK 2, bK true] ++ userItem c)
    else if s == Srt.k then some [kOf [], kOf [iK 0], kOf [iK 1], kOf [iK 0, iK 1], kOf [bK true]]
    else if s == Srt.map then some [mapV [], mapV [(0, 1)], mapV [(1, 2)], mapV [(0, 1), (1, 2)], mapV [(0, 2)], mapV [(2, 0)]]
    else if s == Srt.set then some [setV [], setV [0], setV [1], setV [0, 1], setV [1, 2], setV [2]]
    else if s == Srt.list then some [listV [], listV [0], listV [1], listV [0, 1], listV [1, 0], listV [0, 0]]
    else if s == Srt.rangeMap then
      some [rangeMapV [], rangeMapV [(0, 2, 0)], rangeMapV [(2, 3, 0)], rangeMapV [(0, 1, 0), (1, 2, 1)],
        rangeMapV [(1, 3, 1)], rangeMapV [(3, 5, 2)]]
    else if s == Srt.string then some (["", "a", "ab", "é∀"].map fun t => .dv Srt.string (.tok t))
    else if s == Srt.float then some (floats.map fun (p, e, b) => .dv Srt.float (.float p e b))
    else if s == Srt.bytes then some (["", "\x01", "\x00\xff"].map fun t => .dv Srt.bytes (.tok t))
    else if s == Srt.endianness then some [.ctor littleEndianBytes [], .ctor bigEndianBytes []]
    else if s == Srt.signedness then some [.ctor signedBytes [], .ctor unsignedBytes []]
    else none
  raw.map (·.filter fun v => c.sortOf v == some s)

/-! ## Printing -/

partial def showV (c : Semantics) : GroundTerm → String
  | .dv _ (.int i) => toString i
  | .dv _ (.bool b) => toString b
  | .dv _ (.tok t) => s!"\"{t}\""
  | .dv _ (.float p e b) => s!"float({p},{e},{b})"
  | .inj _ _ t => showV c t
  | .ctor f [] => if f == dotk then ".K" else c.symName f
  | .ctor f [a, b] => if f == kseq then s!"{showV c a} ~> {showV c b}" else s!"{c.symName f}({showV c a}, {showV c b})"
  | .ctor f ts => s!"{c.symName f}({", ".intercalate (ts.map (showV c))})"
  | .map _ [] => ".Map"
  | .map _ es => "{" ++ ", ".intercalate (es.map fun (k, v) => s!"{showV c k} |-> {showV c v}") ++ "}"
  | .set _ [] => ".Set"
  | .set _ es => "{" ++ ", ".intercalate (es.map (showV c)) ++ "}"
  | .list _ [] => ".List"
  | .list _ es => "[" ++ ", ".intercalate (es.map (showV c)) ++ "]"

def showD (c : Semantics) : D → String
  | .bot => "⊥"
  | .top => "⊤"
  | .val v => showV c v
  | .many vs => "{" ++ ", ".intercalate (vs.map (showV c)) ++ "}"

/-! ## Γ's symbols and sorts by their KORE names -/

def stripSort (n : String) : String := if n.startsWith "Sort" then n.drop 4 |>.toString else n

def ksortName : Kore.KSort → String
  | .ctor h [] => h.ident.name
  | .ctor h _ => h.ident.name ++ "{…}"
  | .var v => v.ident.ident.name

/-- The key of an application: the symbol's name, and for an instance of a sort-parametric symbol
its name at the sorts, `Sort` dropped (`f{X₁,…}`, as the reader names it). -/
def appKey (h : Kore.SymbolIdent) (sorts : List Kore.KSort) : String :=
  if sorts.isEmpty then h.ident.name
  else h.ident.name ++ "{" ++ ",".intercalate (sorts.map (stripSort ∘ ksortName)) ++ "}"

structure Ctx where
  c : Semantics
  syms : List (String × CtorSig)
  sorts : List (String × Srt)
  mode : Mode
  /-- the Int grid without 2^64 + 1 (a length or count of that size is not evaluated) -/
  small : Bool := false

def Ctx.of (c : Semantics) (m : Mode) (small : Bool := false) : Ctx :=
  { c, mode := m, small
    syms := (kernelSyms c).map fun k => (c.symName k.name, k)
    sorts := (kernelSorts c).map fun s => ("Sort" ++ c.sortName s, s) }

def Ctx.sort (x : Ctx) (s : Kore.KSort) : Except String Srt :=
  match x.sorts.lookup (ksortName s) with
  | some s => pure s
  | none => throw s!"sort {ksortName s} not among Γ's"

mutual
  /-- The applications of a pattern, by key (an injection as `inj`: Γ's injections are its
  subsorts, checked where one is evaluated). -/
  partial def appsOf : Kore.Pattern → List String
    | .app h ss ps => (if h.ident.name == "inj" then "inj" else appKey h ss) :: appsOfL ps
    | .not _ p | .exist _ _ p | .forall _ _ p | .mu _ p | .nu _ p | .ceil _ _ p | .floor _ _ p | .next _ p => appsOf p
    | .and _ ps | .or _ ps => appsOfL ps
    | .implies _ p q | .iff _ p q | .equals _ _ p q | .in _ _ p q | .rewrites _ p q => appsOf p ++ appsOf q
    | .leftAssoc h ss ps | .rightAssoc h ss ps => appKey h ss :: appsOfL ps
    | _ => []
  partial def appsOfL : List Kore.Pattern → List String
    | [] => []
    | p :: ps => appsOf p ++ appsOfL ps
end

/-- The free variables of a pattern: name (a set variable's with `@`) and sort. -/
partial def freeVars (bound : List String) : Kore.Pattern → List (String × Kore.KSort)
  | .var (.evar v) => if bound.contains v.var.ident.name then [] else [(v.var.ident.name, v.sort)]
  | .var (.svar v) => if bound.contains ("@" ++ v.var.ident.name) then [] else [("@" ++ v.var.ident.name, v.sort)]
  | .app _ _ ps | .and _ ps | .or _ ps | .leftAssoc _ _ ps | .rightAssoc _ _ ps => ps.flatMap (freeVars bound)
  | .not _ p | .ceil _ _ p | .floor _ _ p | .next _ p => freeVars bound p
  | .exist _ v p | .forall _ v p => freeVars (v.var.ident.name :: bound) p
  | .mu v p | .nu v p => freeVars (("@" ++ v.var.ident.name) :: bound) p
  | .implies _ p q | .iff _ p q | .equals _ _ p q | .in _ _ p q | .rewrites _ p q => freeVars bound p ++ freeVars bound q
  | _ => []

/-! ## The evaluator -/

def dvVal (x : Ctx) (s : Kore.KSort) (t : String) : M D := do
  let s ← liftM (m := Except String) (x.sort s)
  if s == Srt.int then
    match t.toInt? with
    | some i => pure (.val (int i))
    | none => throw s!"Int literal {t}"
  else if s == Srt.bool then
    if t == "true" then pure (.val (bool true)) else if t == "false" then pure (.val (bool false)) else throw s!"Bool literal {t}"
  else if s == Srt.string then pure (.val (.dv Srt.string (.tok t)))
  else throw s!"literal of sort {x.c.sortName s}"

/-- The meaning of Γ's symbol `k` at the values `vs`. -/
def applyAt (x : Ctx) (key : String) (k : CtorSig) (vs : List GroundTerm) : M D := do
  let c := x.c
  if c.sortsOf vs != some k.args then throw s!"{key} applied to arguments not of its sorts"
  if (lookupSig c.ctorSigs k.name).isSome then return .val (.ctor k.name vs)
  match hook k.name vs with
  | some (some v) => return .val v
  | some none =>
    if silent k.name vs then
      modify fun f => { f with silent := f.silent ++ [key] }
      let pickAt (i : Nat) : M D := match gridOf c k.result x.small with
        | some (g :: gs) => return .val ((g :: gs)[i % (gs.length + 1)]!)
        | _ => throw s!"no grid for the result sort of {key}"
      match x.mode with
      | .none => return .bot
      | .pick i => pickAt i
      | .only ks i => if ks.contains k.name then pickAt i else return .bot
      | .lib => return match (c.withHooks HookParams.lib).fallback k.name vs with
        | some v => .val v
        | none => .bot
      | .hash => pickAt ((hash (key ++ "(" ++ ", ".intercalate (vs.map (showV c)) ++ ")")).toNat % 2)
    else return .bot
  | none =>
    if (c.lookupParam k.name).isSome then
      modify fun f => { f with param := f.param ++ [key] }
      return match c.paramVal k.name vs with
        | some v => .val v
        | none => .bot
    match Exec.evalF c 10000 k.name vs with
    | some (some v) => return .val v
    | some none =>
      modify fun f => { f with param := f.param ++ [key ++ " (rest)"] }
      return .bot
    | none => throw s!"{key}: no meaning found (not a constructor, hook, parameter, or function with a result)"

partial def eval (x : Ctx) (env : List (String × D)) : Kore.Pattern → M D
  | .var (.evar v) => match env.lookup v.var.ident.name with
    | some d => pure d
    | none => throw s!"unbound {v.var.ident.name}"
  | .var (.svar v) => match env.lookup ("@" ++ v.var.ident.name) with
    | some d => pure d
    | none => throw s!"unbound @{v.var.ident.name}"
  | .dv s t => dvVal x s t
  | .top _ => pure .top
  | .bottom _ => pure .bot
  | .and _ ps => do
    let ds ← ps.mapM (eval x env)
    pure (ds.foldl D.meet .top)
  | .not _ p => do
    match ← eval x env p with
    | .top => pure .bot
    | .bot => pure .top
    | _ => throw "\\not of a term"
  | .implies _ p q => do
    match ← eval x env p with
    | .bot => pure .top
    | .top => eval x env q
    | _ => throw "\\implies with a term premise"
  | .equals _ _ p q => do
    let a ← eval x env p
    let b ← eval x env q
    pure (if a.same b then .top else .bot)
  | .in _ _ p q => do
    let a ← eval x env p
    let b ← eval x env q
    pure (match a.meet b with | .bot => .bot | _ => .top)
  | .ceil _ _ p => do
    match ← eval x env p with
    | .bot => pure .bot
    | _ => pure .top
  | .exist _ v (.equals _ _ (.var (.evar v')) t) => do
    if v != v' then throw "\\exists of another shape"
    match ← eval x env t with
    | .val _ => pure .top
    | .bot | .many _ => pure .bot
    | .top => throw "\\exists over \\top"
  | .app h sorts args => do
    let ds ← args.mapM (eval x env)
    if h.ident.name == "inj" then
      match sorts, ds with
      | [_, B], [d] => do
        let B ← liftM (m := Except String) (x.sort B)
        let A ← liftM (m := Except String) (x.sort (sorts.headD default))
        match d.elems with
        | none => throw "inj of \\top"
        | some vs =>
          let ws ← vs.mapM fun v => do
            let w := match v with
              | .inj a0 _ t => GroundTerm.inj a0 B t
              | _ => GroundTerm.inj A B v
            if x.c.sortOf w == some B then pure w else throw "ill-sorted injection"
          pure (D.ofElems ws)
      | _, _ => throw "inj of another shape"
    else
      let key := appKey h sorts
      match x.syms.lookup key with
      | none => throw s!"{key} not among Γ's symbols"
      | some k =>
        if ds.any (fun d => match d with | .bot => true | _ => false) then pure .bot
        else
          let vss ← ds.mapM fun d => match d.elems with
            | some vs => pure vs
            | none => throw s!"{key} applied to \\top"
          match vss.foldr (fun vs acc => vs.flatMap fun v => acc.map (v :: ·)) [[]] with
          | [vs] => applyAt x key k vs
          | tuples =>
            let rs ← tuples.mapM (applyAt x key k)
            match rs.mapM D.elems with
            | some ess => pure (D.ofElems ess.flatten)
            | none => throw s!"{key} with the value \\top"
  | p => throw s!"construct not evaluated ({(reprStr p).take 60})"

/-! ## Sentences -/

/-- The two sides the sentence compares, for printing. -/
partial def sides : Kore.Pattern → Option (Kore.Pattern × Kore.Pattern)
  | .implies _ _ q => sides q
  | .equals _ _ l r => some (l, r)
  | .exist _ _ (.equals _ _ _ t) => some (t, t)
  | _ => none

def points : List (String × List D) → List (List (String × D))
  | [] => [[]]
  | (n, ds) :: rest => let ps := points rest; ds.flatMap fun d => ps.map ((n, d) :: ·)

def attr? (as : List Kore.AppPattern) (n : String) : Option String :=
  match as.find? (·.head.ident.name == n) with
  | some a => match a.args with
    | [.string s] => some s
    | _ => some ""
  | none => none

def hasAttr (as : List Kore.AppPattern) (n : String) : Bool := (attr? as n).isSome

def srcOf (as : List Kore.AppPattern) : String := (attr? as "org'Stop'kframework'Stop'attributes'Stop'Source").getD ""
def locOf (as : List Kore.AppPattern) : String := (attr? as "org'Stop'kframework'Stop'attributes'Stop'Location").getD ""

def isBuiltin (as : List Kore.AppPattern) : Bool := ((srcOf as).splitOn "/include/kframework/builtin/").length > 1

/-- The builtin file and line of a library sentence (`domains.md:1415`). -/
def placeOf (as : List Kore.AppPattern) : String :=
  let file := ((srcOf as).splitOn "/").getLast?.getD "" |>.replace ")" ""
  let line := (((locOf as).drop 9).toString.splitOn ",").headD ""
  if file.isEmpty then "-" else s!"{file}:{line}"

/-- The place (`placeOf`) of the declaration of the symbol named `n` in `k`; `-` where `k` declares
none. -/
def declPlace (k : Kore.Definition) (n : String) : String :=
  let at? (sym : Kore.Symbol) (as : List Kore.AppPattern) : Option String :=
    if sym.ident.ident.name == n then some (placeOf as) else none
  ((k.modules.flatMap (·.sentences)).findSome? fun
    | .symbol s => at? s.symbol s.attributes
    | .hookedSymbol s => at? s.symbol s.attributes
    | _ => none).getD "-"

def isFunctionalShape : Kore.Pattern → Option (Kore.SymbolIdent × List Kore.KSort)
  | .exist _ v (.equals _ _ (.var (.evar v')) (.app h ss _)) => if v == v' then some (h, ss) else none
  | _ => none

def isReadC : SentenceClass → Bool
  | .read | .readAs _ => true
  | _ => false

/-- The class (TIE-0 row) of a user-module axiom, if one of 9, 15, 17, 18; 16 (set idempotence,
refuted, out of scope) is probed as the control that the probe finds a counterexample. A hooked
symbol's `functional` sentence is row 9 whatever its reading (the sort-parametric `ite{S}`'s is
inert `parametricFunctional`, and applies `ite{S}`, a symbol Γ does not have). -/
def rowOf (k : Kore.Definition) (a : Kore.Axiom) : Option Nat :=
  let cls := classify (.axiom a)
  match cls with
  | .inert .collectionLaw => some 15
  | .inert .simplification => some 18
  | .unread .setIdempotence => some 16
  | _ =>
    match isFunctionalShape a.pattern with
    | some (h, _) =>
      let hooked := (k.symbolDecls.find? (·.name == h.ident.name)).any (·.hooked)
      if hasAttr a.attributes "functional" && hooked then some 9 else none
    | none =>
      if isBuiltin a.attributes && hasAttr a.attributes "simplification" then some 18
      else if isBuiltin a.attributes && isReadC cls then some 17
      else none

structure Res where
  index : Nat
  line : Nat
  row : Nat
  place : String
  syms : List String
  absent : List String
  /-- a collection law generated from its symbol's `assoc` attribute: the place of the symbol's
  declaration, which the law sentence, carrying no location, is named by; `-` for any other -/
  lawPlace : String := "-"
  points : Nat := 0
  holds : Nat := 0
  /-- points where the sentence's premise (`\implies`' first argument) holds under `HookParams.none`:
  the points at which the sentence says something -/
  active : Nat := 0
  /-- points where a silent point, a parameter or a function's rest was reached -/
  hdep : Nat := 0
  /-- failures under `HookParams.none` at points reaching nothing that depends on H -/
  cex : List String := []
  /-- failures under some interpretation at points reaching a silent point or parameter -/
  hfail : List String := []
  /-- points reading the interpretation where the left side (the application the sentence states
  the value of) is not at a silent point: the interpretation is read inside the right side only -/
  hOff : Nat := 0
  /-- the readings under which it fails at some point -/
  failModes : List String := []
  /-- why not probed -/
  skip : Option String := none
  /-- the sentence has a free set variable -/
  setVar : Bool := false
  /-- points where some set variable holds two values -/
  points2 : Nat := 0
  /-- failures there under `HookParams.none` at points reaching nothing that depends on H: how many,
  and the first eight -/
  ncex2 : Nat := 0
  cex2 : List String := []
  /-- failures there under some interpretation at points reaching a silent point or parameter -/
  nhfail2 : Nat := 0
  hfail2 : List String := []
  /-- why a point there was not evaluated -/
  skip2 : Option String := none

def showPoint (c : Semantics) (pt : List (String × D)) : String :=
  ", ".intercalate (pt.map fun (n, d) => s!"{n} = {showD c d}")

/-- Evaluate one sentence at every point of its grid, in the three readings of silent points. -/
def probe (c : Semantics) (r : Res) (a : Kore.Axiom) (modes : List Mode := [.none, .pick 0, .pick 1])
    (small : Bool := false) : Res := Id.run do
  let fv := (freeVars [] a.pattern).eraseDups
  let x0 := Ctx.of c .none small
  let mut grids : List (String × List D) := []
  for (n, s) in fv do
    match x0.sort s with
    | .error e => return { r with skip := some e }
    | .ok srt =>
      match gridOf c srt small with
      | none => return { r with skip := some s!"no grid for sort {c.sortName srt} (variable {n})" }
      | some g =>
        let ds := g.map D.val
        grids := grids ++ [(n, if n.startsWith "@" then D.bot :: ds else ds)]
  let pts := points grids
  let leftKey : Option String := match sides a.pattern with
    | some (.app h ss _, _) => some (appKey h ss)
    | _ => none
  let mut r := { r with points := pts.length }
  for pt in pts do
    let mut dep := false
    let mut off := false
    let mut okAll := true
    for m in modes do
      let x := Ctx.of c m small
      match (eval x pt a.pattern).run {} with
      | .error e => return { r with skip := some s!"at {showPoint c pt}: {e}" }
      | .ok (d, fl) =>
        let isDep := !fl.silent.isEmpty || !fl.param.isEmpty
        if isDep then
          dep := true
          if !(leftKey.any fl.silent.contains) then off := true
        let holds := match d with | .top => true | _ => false
        if !holds then
          okAll := false
          if !r.failModes.contains m.name then r := { r with failModes := r.failModes ++ [m.name] }
          let sd := match sides a.pattern with
            | some (l, rr) =>
              let l' := match (eval x pt l).run {} with | .ok (d, _) => showD c d | .error e => e
              let r' := match (eval x pt rr).run {} with | .ok (d, _) => showD c d | .error e => e
              s!"left {l'}, right {r'}"
            | none => ""
          let msg := s!"{m.name} at {showPoint c pt}: {sd}" ++
            (if isDep then s!" (reached {fl.silent ++ fl.param})" else "")
          if isDep then r := { r with hfail := r.hfail ++ [msg] }
          else if m == .none then r := { r with cex := r.cex ++ [msg] }
    let premise := match a.pattern with
      | .implies _ p _ => p
      | _ => .top (.var ⟨⟨⟨"R"⟩⟩⟩)
    match (eval (Ctx.of c .none small) pt premise).run {} with
    | .ok (.top, _) => r := { r with active := r.active + 1 }
    | _ => pure ()
    if dep then r := { r with hdep := r.hdep + 1 }
    if off then r := { r with hOff := r.hOff + 1 }
    if okAll then r := { r with holds := r.holds + 1 }
  return r

def pairsOf {α : Type} : List α → List (α × α)
  | [] => []
  | a :: as => as.map (a, ·) ++ pairsOf as

/-- Evaluate a sentence with a free set variable at the points where some set variable holds two
values of its sort's grid; each other set variable is at ∅, one value or two, each element variable
at one value. -/
def probeTwo (c : Semantics) (r : Res) (a : Kore.Axiom) (modes : List Mode := [.none, .pick 0, .pick 1])
    (small : Bool := false) : Res := Id.run do
  let fv := (freeVars [] a.pattern).eraseDups
  if r.skip.isSome || !fv.any (·.1.startsWith "@") then return r
  let x0 := Ctx.of c .none small
  let mut grids : List (String × List D) := []
  for (n, s) in fv do
    match x0.sort s with
    | .error e => return { r with setVar := true, skip2 := some e }
    | .ok srt =>
      match gridOf c srt small with
      | none => return { r with setVar := true, skip2 := some s!"no grid for sort {c.sortName srt} (variable {n})" }
      | some g =>
        let ds := g.map D.val
        grids := grids ++ [(n, if n.startsWith "@" then D.bot :: ds ++ (pairsOf g).map (fun (v, w) => D.many [v, w]) else ds)]
  let pts := (points grids).filter (·.any (·.2.isMany))
  let mut r := { r with setVar := true, points2 := pts.length }
  for pt in pts do
    for m in modes do
      let x := Ctx.of c m small
      match (eval x pt a.pattern).run {} with
      | .error e => return { r with skip2 := some s!"at {showPoint c pt}: {e}" }
      | .ok (d, fl) =>
        let isDep := !fl.silent.isEmpty || !fl.param.isEmpty
        let holds := match d with | .top => true | _ => false
        if !holds && (isDep || m == .none) then
          let first := if isDep then r.nhfail2 < 8 else r.ncex2 < 8
          let msg := if !first then "" else
            let sd := match sides a.pattern with
              | some (l, rr) =>
                let l' := match (eval x pt l).run {} with | .ok (d, _) => showD c d | .error e => e
                let r' := match (eval x pt rr).run {} with | .ok (d, _) => showD c d | .error e => e
                s!"left {l'}, right {r'}"
              | none => ""
            s!"{m.name} at {showPoint c pt}: {sd}" ++ (if isDep then s!" (reached {fl.silent ++ fl.param})" else "")
          if isDep then r := { r with nhfail2 := r.nhfail2 + 1, hfail2 := if first then r.hfail2 ++ [msg] else r.hfail2 }
          else r := { r with ncex2 := r.ncex2 + 1, cex2 := if first then r.cex2 ++ [msg] else r.cex2 }
  return r

def verdictTwo (r : Res) : String :=
  if !r.setVar then "" else
  match r.skip2 with
  | some e => s!"; two-element sets not evaluated: {e}"
  | none =>
    if r.ncex2 > 0 then s!"; at two-element sets ({r.points2} points) COUNTEREXAMPLE ({r.ncex2} points; first: {r.cex2.headD ""})"
    else if r.nhfail2 > 0 then s!"; at two-element sets ({r.points2} points) FAILS UNDER SOME H at a silent point ({r.nhfail2} point-readings; first: {r.hfail2.headD ""})"
    else s!"; holds at two-element sets ({r.points2} points)"

def verdict (r : Res) : String :=
  match r.skip with
  | some e => s!"not probed: {e}"
  | none =>
    if !r.cex.isEmpty then s!"COUNTEREXAMPLE ({r.cex.length} points; first: {r.cex.headD ""})"
    else if !r.hfail.isEmpty then s!"FAILS UNDER SOME H at a silent point ({r.hfail.length} point-readings; first: {r.hfail.headD ""})"
    else if r.hdep > 0 then s!"holds ({r.hdep} points reach a silent point or parameter; holds in every reading)"
    else "holds"

/-- The line of each axiom of the text, by its 1-based index. -/
def axiomLines (text : String) : List Nat :=
  ((text.splitOn "\n").zipIdx.filter fun (l, _) => l.trimAsciiStart.startsWith "axiom").map (·.2 + 1)

/-- Per class: sentences, over Γ's symbols, holding at every point in the three readings, with a
counterexample, failing only in some reading at a silent point, not probed though over Γ. -/
abbrev Summary := List (Nat × Nat × Nat × Nat × Nat × Nat × Nat)

/-- What a run finds of the sentences that read the interpretation, each named by its row and its
place (a `functional` sentence, which has none, by its symbol):
- `unnamed`: those reading it at some point that are neither a `functional` sentence of a symbol of
  `totalSilentKeys` nor at a line of `libSentences`;
- `unread`: those at a line of `libSentences`, probed, that read it at no point;
- `off`: those reading it at a point where the left side is not at a silent point;
- `libFails`: those failing at some point under `HookParams.lib`. -/
structure Reads where
  unnamed : List String
  unread : List String
  off : List String
  libFails : List String
  deriving BEq, Repr

/-- What the points with a two-element set find, of the sentences with a free set variable that
are over Γ's symbols and hold at every point of the first grid in every reading (each named as in
`Reads`): how many there are and how many hold at every such point too; `refuted`, those with a
counterexample there (a failure at a point reading nothing of the interpretation, so Γ with the
sentence has no model); `hOnly`, those failing there only at points reading the interpretation;
`unevaluated`, those with a point the evaluator has no meaning for. -/
structure Two where
  sentences : Nat
  hold : Nat
  refuted : List String
  hOnly : List String
  unevaluated : List String
  deriving BEq, Repr

/-- The library's definedness lemmas of `/Int`, `%Int`, `modInt`, `>>Int` and `<<Int` (domains.md
1392 to 1396) and the generated one of a map with one entry and a rest, `#Ceil(@K0 |-> @K1 @Rest)`,
as `Two` names them, in text order. -/
def ceilLemmas : List String :=
  ["18 domains.md:1393", "18 domains.md:1392", "18 domains.md:1396", "18 domains.md:1395", "18 domains.md:1394",
   "18 Lbl'Unds'Map'Unds' Lbl'UndsPipe'-'-GT-Unds' Lbl'Unds'in'Unds'keys'LParUndsRParUnds'MAP'Unds'Bool'Unds'KItem'Unds'Map"]

/-- What both texts give at two-element sets, apart from row 18's count (which is of the first
grid): of the fourteen sentences with a set variable over Γ's symbols, the eight Bool ones
(domains.md 1176 to 1179, 1181 to 1184) hold there, and the six of `ceilLemmas` have a
counterexample: with `@I2 = {0, d}` the left side holds and `@I2 =/=Int 0` denotes both `false` and
`true`; with `@I2` a negative and a non-negative shift, `@I2 >=Int 0` denotes both; with `@Rest`
two maps, one holding the key and one not, the left side holds and `@K0 in_keys(@Rest)` denotes
both. -/
def expectedTwo : Two := { sentences := 14, hold := 8, refuted := ceilLemmas, hOnly := [], unevaluated := [] }
def expectedFltTwo : Two := expectedTwo
/-- `allbuiltins.kompile.kore` holds six more sentences with a set variable over Γ's symbols. Two
hold at two-element sets (domains.md 449, 450: `@Key in_keys(.Map)` against `#Ceil(@Key)`), and four
have a counterexample there: 411 (`#Ceil(@M [@K])`, at `@K` a key of the map and one that is not),
830 (`#Ceil(@S SetItem(@E))`, at `@E` a member and one that is not), and 451, 452
(`@Key in_keys(Key' |-> Val @M)`). -/
def expectedAllTwo : Two :=
  { sentences := 20, hold := 10,
    refuted := ["18 domains.md:1393", "18 domains.md:1392", "18 domains.md:1396", "18 domains.md:1395",
      "18 domains.md:1394", "18 domains.md:411", "18 domains.md:830", "18 domains.md:452",
      "18 domains.md:451",
      "18 Lbl'Unds'Map'Unds' Lbl'UndsPipe'-'-GT-Unds' Lbl'Unds'in'Unds'keys'LParUndsRParUnds'MAP'Unds'Bool'Unds'KItem'Unds'Map"],
    hOnly := [], unevaluated := [] }

/-- The text without the user module's sentences the reader refuses as builtin sentences outside
the library's text (`builtinText`: a module of a K installation KCore's library does not hold), with
their heads; the text itself when there are none. -/
def outOfLibrary (k : Kore.Definition) : Kore.Definition × List String :=
  let off := Parse.preludeLength k
  let rs := (Parse.refusals k).filter (·.reason.name == "builtinText")
  let ix := rs.filterMap (·.index)
  match k.modules.getLast? with
  | none => (k, [])
  | some m =>
    let m' := { m with sentences := (m.sentences.zipIdx.filter fun (_, i) => !ix.contains (off + i)).map (·.1) }
    ({ k with modules := k.modules.dropLast ++ [m'] }, rs.map (·.head))

def run (path : String) (verbose : Bool := true) (modes : List Mode := [.none, .pick 0, .pick 1])
    (small : Bool := false) (dropOut : Bool := false) : IO (Summary × Reads × Two) := do
  let text ← IO.FS.readFile path
  let k ← match Kore.parseDefinition text with
    | .ok k => pure k
    | .error e => throw (IO.userError s!"read: {e}")
  let (k, dropped) := if dropOut then outOfLibrary k else (k, [])
  unless dropped.isEmpty do
    IO.println s!"{path}: {dropped.length} sentences of builtin modules outside the library's text left out: {dropped}"
  let d ← match Parse.parse k with
    | .ok d => pure d
    | .error e => throw (IO.userError s!"parse: {e.toText}")
  let c := d.sem
  let user := (k.modules.getLast?.map (·.name.ident.name)).getD ""
  let lines := if dropped.isEmpty then axiomLines text else []
  let ads := k.axiomDecls
  IO.println s!"{path}: user module {user}, {ads.length} axioms (lines found {lines.length})"
  let gNames := ((kernelSyms c).map fun k => c.symName k.name) ++ ["inj"]
  let mut res : List Res := []
  for ad in ads do
    if ad.module != user then continue
    match rowOf k ad.ax with
    | none => pure ()
    | some row =>
      let syms := (appsOf ad.ax.pattern).eraseDups
      let absent := syms.filter (!gNames.contains ·)
      let lawPlace := if row == 15 && hasAttr ad.ax.attributes "assoc" then (syms.head?.map (declPlace k)).getD "-" else "-"
      let place := placeOf ad.ax.attributes
      let r : Res := { index := ad.index, line := lines.getD (ad.index - 1) 0, row, place, syms, absent, lawPlace }
      -- a shift by 2^64 + 1 is a number of that many bits: its sentences are probed on the small grid
      let small := small || syms.any ["Lbl'Unds-LT--LT-'Int'Unds'", "Lbl'Unds-GT--GT-'Int'Unds'"].contains
      let r := if absent.isEmpty then probe c r ad.ax modes small else { r with skip := some s!"applies symbols Γ does not have: {absent}" }
      let r := if r.skip.isNone && r.cex.isEmpty && r.hfail.isEmpty then probeTwo c r ad.ax modes small else r
      res := res ++ [r]
  IO.println s!"Γ's instances of ite: {gNames.filter (·.startsWith "Lblite")}"
  let mut sum : Summary := []
  for row in [9, 15, 17, 18, 16] do
    let rs := res.filter (·.row == row)
    let over := rs.filter (·.absent.isEmpty)
    let cexs := over.filter (!·.cex.isEmpty)
    let hf := over.filter (fun r => r.cex.isEmpty && !r.hfail.isEmpty)
    let sk := over.filter (·.skip.isSome)
    let hold := over.filter (fun r => r.skip.isNone && r.cex.isEmpty && r.hfail.isEmpty)
    IO.println s!"row {row}{if row == 16 then " (control, not in scope)" else ""}: {rs.length} sentences, {over.length} over Γ's symbols ({rs.length - over.length} not), probed {over.length - sk.length}: {hold.length} hold, {cexs.length} with a counterexample, {hf.length} failing only under some H at silent points, {sk.length} not probed"
    sum := sum ++ [(row, rs.length, over.length, hold.length, cexs.length, hf.length, sk.length)]
  if verbose then
    for r in res do
      IO.println s!"#{r.index} L{r.line} row {r.row} {r.place} [{" ".intercalate r.syms}] points {r.points} (premise holds at {r.active}, reads H at {r.hdep}): {verdict r}{verdictTwo r}{if r.failModes.isEmpty then "" else s!" [fails under {r.failModes}]"}"
      for m in r.cex.drop 1 |>.take 7 do IO.println s!"    also {m}"
      for m in r.hfail.drop 1 |>.take 7 do IO.println s!"    also {m}"
      for m in r.cex2.drop 1 do IO.println s!"    also {m}"
  let name (r : Res) : String := s!"{r.row} {if r.place == "-" then " ".intercalate r.syms else r.place}"
  let keyNames := totalSilentKeys.map c.symName
  let places := libSentences.map fun (l, _) => s!"domains.md:{l}"
  -- a sentence at a line of `libSentences`: by its own place, or a law by its symbol's declaration's
  let atLine (r : Res) : Bool := r.row != 9 && (places.contains r.place || places.contains r.lawPlace)
  let named (r : Res) : Bool :=
    (r.row == 9 && r.syms.length == 1 && r.syms.all keyNames.contains) || atLine r
  let probed := res.filter (·.skip.isNone)
  let reads : Reads :=
    { unnamed := (probed.filter fun r => r.hdep > 0 && !named r).map name
      unread := (probed.filter fun r => atLine r && r.hdep == 0).map name
      off := (probed.filter (·.hOff > 0)).map name
      libFails := (probed.filter (·.failModes.contains Mode.lib.name)).map name }
  let readers := probed.filter (·.hdep > 0)
  IO.println s!"sentences reading the interpretation: {readers.map fun r => s!"{name r} ({r.hdep} points)"}"
  IO.println s!"guard: {reprStr reads}"
  let sv := res.filter (·.setVar)
  let two : Two :=
    { sentences := sv.length
      hold := (sv.filter fun r => r.skip2.isNone && r.ncex2 == 0 && r.nhfail2 == 0).length
      refuted := (sv.filter fun r => r.skip2.isNone && r.ncex2 > 0).map name
      hOnly := (sv.filter fun r => r.skip2.isNone && r.ncex2 == 0 && r.nhfail2 > 0).map name
      unevaluated := (sv.filter (·.skip2.isSome)).map name }
  IO.println s!"set variables at two-element sets: {reprStr two}"
  return (sum, reads, two)

/-- The counts both texts give: every sentence over Γ's symbols of rows 9, 15, 17, 18 holds in the
three readings (`<=Set`'s `functional` sentence too: it has a value at every pair of sets); row 16
(set idempotence) is the control. -/
def expected : Summary :=
  [(9, 54, 46, 46, 0, 0, 0), (15, 9, 9, 9, 0, 0, 0), (17, 28, 23, 23, 0, 0, 0), (18, 64, 63, 63, 0, 0, 0),
   (16, 1, 1, 0, 1, 0, 0)]

/-- The sentences reading the interpretation that are no condition of `Semantics.libAdmitted`,
because no interpretation meets them: the second equation of `countAllOccurrences` (domains.md
1898), whose instance at the empty needle is `c = 1 +Int c` of the count c. It fails under
`HookParams.lib` as under every interpretation that gives the count a value there. -/
def unmet : List String := ["17 domains.md:1898"]

/-- What a check requires of a run: every sentence reading the interpretation has a named
condition, `unmet` aside, and reads it only where its left side is silent, every named sentence
the text holds reads it at some point of the grid, and under `HookParams.lib` only the control
(set idempotence) and `unmet` fail. -/
def readsOK (r : Reads) : Bool :=
  r.unnamed.all unmet.contains && r.unread.isEmpty && r.off.isEmpty &&
    r.libFails.all fun n => n.startsWith "16 " || unmet.contains n

/-- The readings `check` and `checkFlt` add: `HookParams.lib`, and the non-constant `hash`. -/
def libModes : List Mode := [.lib, .hash]

def check (path : String) : IO Unit := do
  let (s, r, t) ← run path (modes := [.none, .pick 0, .pick 1] ++ libModes)
  if s != expected then throw (IO.userError s!"{path}: counts {s}, expected {expected}")
  if t != expectedTwo then throw (IO.userError s!"{path}: at two-element sets {reprStr t}, expected {reprStr expectedTwo}")
  if !readsOK r then throw (IO.userError s!"{path}: sentences reading the interpretation: {reprStr r}")
  IO.println s!"{path}: counts as expected, conditions closed, HookParams.lib fails only the control"

/-- The interpretations `checkFlt` reads silent points by: the three readings, and two that give the
symbols of `totalSilentKeys` the first or second grid value of the result sort at their silent
points and no value elsewhere (each meets `Semantics.silentTotal`). -/
def fltModes : List Mode := [.none, .pick 0, .pick 1, .only totalSilentKeys 0, .only totalSilentKeys 1] ++ libModes

/-- The counts of `silentflt.kompile.kore` (FLOAT, STRING, BYTES, SET imported) over the five
readings, the Int grid without 2^64 + 1. Row 9's ten failures are the `functional` sentences of
`substrString`, `Int2Bytes` (at a negative length), `--Float`, `absFloat`, `floorFloat`,
`ceilFloat`, `truncFloat`, `countAllOccurrences` and `replaceAll` (at the empty needle), and
`isNaN`'s at the `p2x1` value, which has no datum (`asDatum`; `isNaN` has its values at the `p1x2`
data), under `HookParams.none` only. Row 17's five: `countAllOccurrences`' second equation (1898)
at the empty needle, under every reading that gives the count a value there (`unmet`);
`replaceAll`'s (1917) at the empty needle under the readings that give `replaceAll` and `replace`
at the count different values; `isInfinite`'s equation (domains.md 1673) at the three `p1x2` values
and the `p2x1` one, under the two `only` readings (`isInfinite` has a value, `maxValueFloat` none, so
the right side has none) and under `pick0`, `pick1` and `hash`; `rfindChar`'s (1893) under `pick0`
and `pick1` (in the points printed), which give the silent points of two symbols values that do
not agree with the equation; and `=/=Float`'s (1648) where an operand is the `p2x1` value, at which
`==Float` and `=/=Float` are silent, under `pick0`, `pick1` and `hash`, which give the two values
that do not agree with the equation (`neFloatEq`). -/
def expectedFlt : Summary :=
  [(9, 93, 73, 63, 0, 10, 0), (15, 9, 9, 9, 0, 0, 0), (17, 55, 43, 37, 0, 5, 1), (18, 67, 66, 66, 0, 0, 0),
   (16, 1, 1, 0, 1, 0, 0)]

def checkFlt : IO Unit := do
  let path := "f2-examples/silentflt.kompile.kore"
  let (s, r, t) ← run path (modes := fltModes) (small := true)
  if s != expectedFlt then throw (IO.userError s!"{path}: counts {s}, expected {expectedFlt}")
  if t != expectedFltTwo then throw (IO.userError s!"{path}: at two-element sets {reprStr t}, expected {reprStr expectedFltTwo}")
  if !readsOK r then throw (IO.userError s!"{path}: sentences reading the interpretation: {reprStr r}")
  IO.println s!"{path}: counts as expected, conditions closed, HookParams.lib fails only the control"

/-- The counts of `allbuiltins.kompile.kore` (kompile's text of a definition importing every module
of the K 7.1.337 installation's builtin files) over `fltModes`, the Int grid without 2^64 + 1, after
leaving out the 193 sentences of builtin modules outside the library's text (`outOfLibrary`:
ARRAY, RAT, FFI, MINT, …). The sentences reading the interpretation are those of silentflt and
RANGEMAP's associativity, at the line of `_RangeMap_`'s declaration (508, `rangeMapAssocEq`), the
one sentence of row 15 failing only under some interpretation; RANGEMAP's other sentences over
Γ's symbols with a variable of sort RangeMap (the `functional` sentences of `lookupOrDefault`,
`-RangeMap`, `<=RangeMap`, `in_keys`, `keys`, `size` and `updateRangeMap`, and the two unit laws)
hold in every reading. -/
def expectedAll : Summary :=
  [(9, 110, 81, 71, 0, 10, 0), (15, 12, 12, 11, 0, 1, 0), (17, 63, 43, 37, 0, 5, 1), (18, 114, 113, 113, 0, 0, 0),
   (16, 1, 1, 0, 1, 0, 0)]

def checkAll : IO Unit := do
  let path := "f2-examples/allbuiltins.kompile.kore"
  let (s, r, t) ← run path (modes := fltModes) (small := true) (dropOut := true)
  if s != expectedAll then throw (IO.userError s!"{path}: counts {s}, expected {expectedAll}")
  if t != expectedAllTwo then throw (IO.userError s!"{path}: at two-element sets {reprStr t}, expected {reprStr expectedAllTwo}")
  if !readsOK r then throw (IO.userError s!"{path}: sentences reading the interpretation: {reprStr r}")
  IO.println s!"{path}: counts as expected, conditions closed, HookParams.lib fails only the control"

end KCore.LibProbe

#eval KCore.LibProbe.check "f2-examples/ens.kompile.kore"
#eval KCore.LibProbe.check "f2-examples/ref-kimp.kore"
#eval KCore.LibProbe.checkFlt
-- about 30 minutes: run with LIBPROBE_ALL=1
#eval show IO Unit from do if (← IO.getEnv "LIBPROBE_ALL").isSome then KCore.LibProbe.checkAll else pure ()
