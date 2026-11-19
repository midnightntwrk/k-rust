/-
  The sentences of a kompiled text about names of the definition's own, evaluated at values against
  Γ's graphs: the sentences of a K installation's builtin files that the reader reads as the
  definition's own (`Parse.isOwnBuiltin`: about names no library text gives a meaning, as RAT's,
  ARRAY's, FFI's, MINT's, KVAR's), and the `functional` sentences generated from the declarations of
  those names (`isOwnAbout`). Native evaluation only (`#eval`), no kernel proof. test/LibProbe.lean
  probes the library's sentences and leaves these out (`outOfLibrary`).
  Run from the package root: `lake env lean test/OwnProbe.lean` (about 8 minutes); with
  `OWNPROBE_LOG=FILE` each sentence's line is also added to FILE as it is done (`#eval` shows its
  output only at its end), and `OWNPROBE_FROM=N` probes the sentences of index N and above only (the
  check then fails on its counts).

  The evaluator is test/LibProbe.lean's (a test file imports the library only, so it is repeated
  here), with these differences:
  - Each reading is an interpretation `HookParams` (`Mode.hp`): `HookParams.none`, the two giving
    every symbol the first or second grid value of its result sort (`pick0`, `pick1`), `HookParams.lib`,
    and one choosing between those two by a hash of the symbol and the arguments (`hash`). It gives
    the silent points of the library's symbols their values (`Semantics.fallback`), as in LibProbe,
    and also a parameter's and a function's: a parameter whose value is its hook's at a point the
    hook's text decides (`Cert.paramValC`), and a function application whose value no interpretation
    takes part in (`Cert.evalFC`), read nothing of it; any other is evaluated under the reading
    (`Semantics.paramVal`, `Exec.evalF` of `c.withHooks`) and the point is marked as reading it.
  - The definition's own sorts have grids (`ownGrids`: Rat, with a pair `<0, 2>Rat` that is no
    fraction in lowest terms, KVar, Array, FFIType).
  - A set variable takes ∅, each value's singleton and each set of two values of its grid.
  - `#Ceil(p)` reads nothing of the interpretation where p has a value under every interpretation
    (`sureVals`), whatever p's other values read.
  - A variable an equation's premise binds by a conjunct `\in(X, p)` takes the values of p at each
    point of the other variables (`inBinds`): elsewhere the premise denotes nothing and the
    sentence holds.
  - A point that reads nothing of the interpretation under `HookParams.none` is evaluated once.
  - Past `bigGrid` points every variable takes a smaller grid (`reduceGrid`).

  Each sentence is put in its class of the tie (`tieClassOf`, `KCore.tieClasses`), and the check
  prints what the reading owes for it (`owes`): from the class's direction, an item of Γ, an owed
  sentence (Γ is to entail it), a hypothesis (the statements take it), or no direction; and from the
  probe, whether it holds at every point under every reading, holds only under some interpretations
  (a condition on H, with the readings that meet it), or fails at a point reading nothing of the
  interpretation (no model). The check compares the sentences whose verdict is not their class's
  plain one with `expectedNoted` and the counts with `expectedTally`, rat.md:109 at two points with
  `expectedPinned`, and requires every counterexample to be one the text states (`refutedByText`:
  rat.md:173 at J = D < 0, rat.md:109 where `@R2` is 0 and a value no `<0, J>Rat`, rat.md:221 and 224 at
  `<0, 2>Rat` and 0).

  On `allbuiltins.kompile.kore` (kompile's text of a definition importing every module of the K
  7.1.337 installation's builtin files), 140 sentences. None that holds at every point reads the
  interpretation where its left side does not (MINT's `sminMInt`, `smaxMInt`, `uminMInt`, `umaxMInt`, `soverflowMInt` and
  `uoverflowMInt` equations, domains.md 2948 to 2951, 2964, 2968, and rat.md 171, 172 read nothing of
  it: where `<<Int` has a negative shift amount Γ states no value, at every interpretation;
  substitution.md:54, `freshKVar`'s equation, reads `String2KVar`, a parameter, on both sides). The
  sentences of `expectedNoted` are the rest.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.OwnProbe

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
also a field of 1, at which every Float has a datum (`asDatum`, `KFloat.tnUnpack`). -/
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

/-- The values of a sort the definition declares in a builtin file of its own (`Rat`, `KVar`, `Array`,
`FFIType`), each checked to be of it: `Rat`'s Int values -1 … 2, the fractions `<1, 2>Rat`,
`<-3, 2>Rat`, `<2, 3>Rat` (numerator and denominator coprime, denominator at least 2) and `<0, 2>Rat`,
a pair whose first component is 0 (`<_,_>Rat` takes any two integers; that a pair is a fraction in
lowest terms is a comment of rat.md, not a sentence, so the text's sentences range over it too); two
`KVar` tokens; three arrays `arr(L, N, D)`; two nullary `FFIType` constructors. -/
def ownGrids (c : Semantics) (syms : List (String × CtorSig)) : List (Srt × List GroundTerm) :=
  let srt (n : String) : Option Srt := (kernelSorts c).find? (c.sortName · == n)
  let sym (n : String) : Option Sym := (syms.lookup n).map (·.name)
  let of (s : Srt) (vs : List GroundTerm) : Srt × List GroundTerm := (s, vs.filter fun v => c.sortOf v == some s)
  let rat := match srt "Rat", sym ratCtorName with
    | some r, some q => [of r ([-1, 0, 1, 2].map (fun i => .inj Srt.int r (int i)) ++
        [(1, 2), (-3, 2), (2, 3), (0, 2)].map fun (a, b) => .ctor q [int a, int b])]
    | _, _ => []
  let kvar := match srt "KVar" with
    | some s => [of s (["x", "_0"].map fun t => .dv s (.tok t))]
    | none => []
  let arr := match srt "Array", sym "Lblarr'LParUndsCommUndsCommUndsRParUnds'ARRAY-IN-K'Unds'Array'Unds'List'Unds'Int'Unds'KItem" with
    | some s, some a => [of s [.ctor a [listV [], int 2, iK 0], .ctor a [listV [1], int 2, iK 0], .ctor a [listV [0, 1], int 3, iK 2]]]
    | _, _ => []
  let ffi := match srt "FFIType", sym "Lbl'Hash'ffi'Unds'sint", sym "Lbl'Hash'ffi'Unds'void" with
    | some s, some a, some b => [of s [.ctor a [], .ctor b []]]
    | _, _, _ => []
  rat ++ kvar ++ arr ++ ffi
where ratCtorName := "Lbl'-LT-UndsCommUnds-GT-'Rat'Unds'RAT-COMMON'Unds'Rat'Unds'Int'Unds'Int"

/-- The interpretation a reading names: at every argument list of a symbol of `ks` (every symbol
for `pick`), the i-th grid value of its result sort (`pick`, `only`), one of the first two chosen
by a hash of the symbol and the arguments (`hash`); `HookParams.lib`; none (`HookParams.none`). -/
def Mode.hp (m : Mode) (res : Std.HashMap Nat Srt) (grid : Srt → Option (List GroundTerm)) : HookParams :=
  let pickAt (i : Nat) (f : Sym) : Option GroundTerm := match res.get? f >>= grid with
    | some (g :: gs) => some ((g :: gs)[i % (gs.length + 1)]!)
    | _ => Option.none
  match m with
  | .none => HookParams.none
  | .pick i => ⟨fun f _ => pickAt i f⟩
  | .only ks i => ⟨fun f _ => if ks.contains f then pickAt i f else Option.none⟩
  | .lib => HookParams.lib
  | .hash => ⟨fun f vs => pickAt ((Hashable.hash (toString f ++ "(" ++ ", ".intercalate (vs.map reprStr) ++ ")")).toNat % 2) f⟩

structure Ctx where
  c : Semantics
  syms : List (String × CtorSig)
  sorts : List (String × Srt)
  mode : Mode
  /-- the Int grid without 2^64 + 1 (a length or count of that size is not evaluated) -/
  small : Bool := false
  /-- the grids of the definition's own sorts (`ownGrids`) -/
  extra : List (Srt × List GroundTerm) := []
  /-- the interpretation of the reading (`Mode.hp`) -/
  hp : HookParams := HookParams.none

def Ctx.grid (x : Ctx) (s : Srt) : Option (List GroundTerm) :=
  match x.extra.lookup s with
  | some g => some g
  | none => gridOf x.c s x.small

/-- The contexts of the readings `ms`, built once. -/
def Ctx.all (c : Semantics) (ms : List Mode) (small : Bool) : List Ctx :=
  let syms := (kernelSyms c).map fun k => (c.symName k.name, k)
  let sorts := (kernelSorts c).map fun s => ("Sort" ++ c.sortName s, s)
  let extra := ownGrids c syms
  let res : Std.HashMap Nat Srt := Std.HashMap.ofList ((kernelSyms c).map fun k => (k.name, k.result))
  let x0 : Ctx := { c, syms, sorts, mode := .none, small, extra }
  ms.map fun m => { x0 with mode := m, hp := m.hp res x0.grid }

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

def ofOpt : Option GroundTerm → D
  | some v => .val v
  | none => .bot

/-- Evaluation's fuel for a function's application. -/
def fnFuel : Nat := 10000

/-- The meaning of Γ's symbol `k` at the values `vs` under the reading's interpretation `x.hp`. A
point is marked where the value depends on it: a silent point of an interpreted symbol, a parameter
whose value is not its hook's at a point the hook's text decides (`Cert.paramValC`), a function
whose value there is not one no interpretation takes part in (`Cert.evalFC`: its evaluation reaches
a silent point, a parameter without hook or a function's rest). -/
def applyAt (x : Ctx) (key : String) (k : CtorSig) (vs : List GroundTerm) : M D := do
  let c := x.c
  if c.sortsOf vs != some k.args then throw s!"{key} applied to arguments not of its sorts"
  if (lookupSig c.ctorSigs k.name).isSome then return .val (.ctor k.name vs)
  match hook k.name vs with
  | some (some v) => return .val v
  | some none =>
    if silent k.name vs then
      modify fun f => { f with silent := f.silent ++ [key] }
      return ofOpt ((c.withHooks x.hp).fallback k.name vs)
    else return .bot
  | none =>
    if (c.lookupParam k.name).isSome then
      match Cert.paramValC c k.name vs with
      | some r => return ofOpt r
      | none =>
        modify fun f => { f with param := f.param ++ [key] }
        return ofOpt ((c.withHooks x.hp).paramVal k.name vs)
    match Cert.evalFC c fnFuel k.name vs with
    | some r => return ofOpt r
    | none =>
      match Exec.evalF (c.withHooks x.hp) fnFuel k.name vs with
      | some r =>
        modify fun f => { f with param := f.param ++ [key ++ " (reads H)"] }
        return ofOpt r
      | none => throw s!"{key}: no meaning found (not a constructor, hook, parameter, or function with a result)"

def pairsOf {α : Type} : List α → List (α × α)
  | [] => []
  | a :: as => as.map (a, ·) ++ pairsOf as

/-- Values a term pattern denotes under every interpretation: those of a variable, a literal, an
injection of such a value, and an application at such values whose meaning reads nothing of the
interpretation (`applyAt` marks nothing). Under every reading each is among the values `eval` gives
the pattern, whatever the interpretation gives elsewhere in it. -/
partial def sureVals (x : Ctx) (env : List (String × D)) : Kore.Pattern → List GroundTerm
  | .var (.evar v) => ((env.lookup v.var.ident.name).bind D.elems).getD []
  | .var (.svar v) => ((env.lookup ("@" ++ v.var.ident.name)).bind D.elems).getD []
  | .dv s t => match (dvVal x s t).run {} with
    | .ok (d, _) => d.elems.getD []
    | .error _ => []
  | .app h sorts args =>
    let ass := args.map (sureVals x env)
    if h.ident.name == "inj" then
      match sorts, ass, x.sort (sorts.headD default), (sorts.getLast?.map x.sort) with
      | [_, _], [vs], .ok A, some (.ok B) => vs.filterMap fun v =>
        let w := match v with
          | .inj a0 _ t => GroundTerm.inj a0 B t
          | _ => GroundTerm.inj A B v
        if x.c.sortOf w == some B then some w else none
      | _, _, _, _ => []
    else
      let key := appKey h sorts
      match x.syms.lookup key with
      | none => []
      | some k => (ass.foldr (fun vs acc => vs.flatMap fun v => acc.map (v :: ·)) [[]]).flatMap fun vs =>
        match (applyAt x key k vs).run {} with
        | .ok (d, fl) => if fl.silent.isEmpty && fl.param.isEmpty then d.elems.getD [] else []
        | .error _ => []
  | _ => []

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
    let fl0 ← get
    match ← eval x env p with
    | .bot => pure .bot
    | _ =>
      -- where `p` has a value under every interpretation (`sureVals`), `#Ceil(p)` holds whatever the
      -- interpretation gives elsewhere in `p`: what `p`'s evaluation read of it is not read
      if !(sureVals x env p).isEmpty then set fl0
      pure .top
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
  | .or _ _ => throw "\\or not evaluated"
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

def isFunctionalShape : Kore.Pattern → Option (Kore.SymbolIdent × List Kore.KSort)
  | .exist _ v (.equals _ _ (.var (.evar v')) (.app h ss _)) => if v == v' then some (h, ss) else none
  | _ => none

/-! ## The sentences read as the definition's own -/

/-- The names an own declaration declares (`Parse.isOwnBuiltin`, `Parse.ownBuiltinDeclName?`). -/
def ownDeclNames (k : Kore.Definition) : List String :=
  ((k.modules.getLast?.map (·.sentences)).getD []).filterMap fun s =>
    if Parse.isOwnBuiltin s then Parse.ownBuiltinDeclName? s else none

/-- A sentence of the user module about the definition's own names: read as the definition's own
(`Parse.isOwnBuiltin`: an equation, a lemma), or the `functional` sentence, without a place,
generated from the declaration of a symbol an own declaration declares. -/
def isOwnAbout (names : List String) (a : Kore.Axiom) : Bool :=
  Parse.isOwnBuiltin (.axiom a) ||
    (srcOf a.attributes == "" && (isFunctionalShape a.pattern).any fun (h, _) => names.contains h.ident.name)

/-- The class of a tie (`KCore.tieClasses`) each sentence is of, from what Γ has of the symbol it
states something of: a sentence applying a symbol Γ does not have is of `no direction`; a
`functional` sentence of a constructor, function, parameter without hook, interpreted hooked symbol
or parameter with a hook (`constructor functional`, `function functional`, `parameter functional`,
`hooked functional`); a lemma the reader leaves out of Γ (`inert simplification`) of `parameter
lemma` where it applies a parameter without hook and of `user lemma` otherwise; an equation of a
function of Γ of `function equation`, or of `priority equation` where it carries a `priority` and is
not `owise`. A `user lemma` the probe then refutes at a point where a set variable holds two values
is of `set-variable lemma` (`reclass`). -/
def tieClassOf (c : Semantics) (syms : List (String × CtorSig)) (absent : List String) (a : Kore.Axiom) : String :=
  if !absent.isEmpty then "no direction" else
  let noImpl (n : String) : Bool := match syms.lookup n with
    | some k => (c.lookupParam k.name).any (·.impl.isNone)
    | none => false
  match isFunctionalShape a.pattern with
  | some (h, ss) =>
    match syms.lookup (appKey h ss) with
    | none => "no direction"
    | some k =>
      if (lookupSig c.ctorSigs k.name).isSome then "constructor functional"
      else if (c.lookupFn k.name).isSome then "function functional"
      else if noImpl (appKey h ss) then "parameter functional"
      else "hooked functional"
  | none =>
    if classifyShape (.axiom a) == .inert .simplification then
      if (appsOf a.pattern).any noImpl then "parameter lemma" else "user lemma"
    else if hasAttr a.attributes "priority" && !hasAttr a.attributes "owise" then "priority equation"
    else "function equation"

/-- The class of a sentence once probed: a lemma the reader leaves out of Γ (`user lemma`) that fails
at a point reading nothing of the interpretation where a set variable holds two values is of
`set-variable lemma`, whose direction is `refuted`: Γ with it has no model, at a valuation sending
each free set variable to a set of values. -/
def reclass (cls : String) (ncexTwo : Nat) : String :=
  if cls == "user lemma" && ncexTwo > 0 then "set-variable lemma" else cls

/-- The direction of a class (`KCore.tieClasses`). -/
def dirOf (cls : String) : Option TieDir := (tieClasses.find? (·.1 == cls)).map (·.2)

/-! ## The probe -/

partial def conjuncts : Kore.Pattern → List Kore.Pattern
  | .and _ ps => ps.flatMap conjuncts
  | p => [p]

/-- The variables the premise of an equation binds by a conjunct `\in(X, p)`: each once, by a
pattern applying none of them. At a point where X is no value of p the conjunct, so the premise,
denotes nothing and the sentence holds, so the points where it says something are those where X is
a value of p: the probe takes X there, and every other variable over its grid. -/
def inBinds (a : Kore.Axiom) : List (String × Kore.Pattern) :=
  match a.pattern with
  | .implies _ p _ =>
    let cands := (conjuncts p).filterMap fun q => match q with
      | .in _ _ (.var (.evar v)) t => some (v.var.ident.name, t)
      | _ => none
    let xs := cands.map (·.1)
    cands.filter fun (x, t) => (xs.filter (· == x)).length == 1 && (freeVars [] t).all (fun (n, _) => !xs.contains n)
  | _ => []

/-- `<I, J>Rat` with J below 2 or I and J not coprime: a constructor term of `Rat` that is no
fraction in lowest terms. -/
def nonCanon : GroundTerm → Bool
  | .ctor _ [.dv _ (.int a), .dv _ (.int b)] => b < 2 || Int.gcd a b != 1
  | _ => false

structure Res where
  index : Nat
  place : String
  /-- the sentence's place, or the symbol of a `functional` sentence -/
  name : String
  cls : String
  syms : List String
  absent : List String
  points : Nat := 0
  holds : Nat := 0
  /-- points where the premise holds under `HookParams.none` -/
  active : Nat := 0
  /-- points where the interpretation was read (a silent point, a parameter, a function's value
  that depends on it) -/
  hdep : Nat := 0
  /-- of those, points where the left side (the application the sentence states the value of) is
  not at a silent point -/
  hOff : Nat := 0
  /-- failures at points reading nothing of the interpretation: how many, how many of them at a
  point holding a `<I, J>Rat` no fraction in lowest terms (`nonCanon`), and the first eight (a
  failure under `HookParams.none`, which is then one under every reading) -/
  ncex : Nat := 0
  ncexNC : Nat := 0
  /-- of those, how many at a point where a set variable holds two values -/
  ncexTwo : Nat := 0
  cex : List String := []
  /-- every point of those failures -/
  cexPts : List (List (String × D)) := []
  /-- failures under some interpretation at points reading it -/
  nhfail : Nat := 0
  hfail : List String := []
  failModes : List String := []
  /-- the variables bound by the premise (`inBinds`) -/
  bound : List String := []
  skip : Option String := none
  setVar : Bool := false
  /-- at each point of `pinned` for the sentence: the readings it fails under there, and whether
  its evaluation under `HookParams.none` reads the interpretation (`failsAt`) -/
  pinnedAt : List (List String × Bool) := []

def showPoint (c : Semantics) (pt : List (String × D)) : String :=
  ", ".intercalate (pt.map fun (n, d) => s!"{n} = {showD c d}")

/-- The number of points beyond which a variable's grid is reduced (`reduceGrid`). -/
def bigGrid : Nat := 1000

/-- A smaller grid of a library sort, for a variable that would take the points past `bigGrid`: Int
-2 … 2, and of another library sort with more than three values the first, third and fourth (of
KItem 0, 2 and `true`; of List, Map and Set the empty one, one with one entry and one with two);
a sort of the definition's own keeps its grid. -/
def reduceGrid (x : Ctx) (s : Srt) (g : List GroundTerm) : List GroundTerm :=
  if s == Srt.int then g.filter fun v => match v with
    | .dv _ (.int i) => i.natAbs ≤ 2
    | _ => true
  else if (x.extra.lookup s).isSome || g.length ≤ 3 then g
  else [g[0]!, g[2]!, g[3]!]

/-- Evaluate one sentence at its points under the readings `xs` (the first `HookParams.none`'s): a
point whose evaluation under the first reads nothing of the interpretation evaluates the same under
every reading, the interpretation being read nowhere else. -/
def probe (x0 : Ctx) (xs : List Ctx) (r : Res) (a : Kore.Axiom) : Res := Id.run do
  let c := x0.c
  let fv := (freeVars [] a.pattern).eraseDups
  let binds := inBinds a
  let mut full : List (String × Srt × List GroundTerm) := []
  for (n, s) in fv do
    if binds.any (·.1 == n) then continue
    match x0.sort s with
    | .error e => return { r with skip := some e }
    | .ok srt =>
      match x0.grid srt with
      | none => return { r with skip := some s!"no grid for sort {c.sortName srt} (variable {n})" }
      | some g => full := full ++ [(n, srt, g)]
  -- past `bigGrid` points, every variable takes the smaller grid of its sort
  let big := (full.map (fun (n, _, g) => if n.startsWith "@" then g.length + 1 else g.length)).foldl (· * ·) 1 > bigGrid
  -- a set variable at ∅, at each value's singleton and at each set of two values
  let grids : List (String × List D) := full.map fun (n, srt, g) =>
    let g := if big then reduceGrid x0 srt g else g
    let ds := g.map D.val
    (n, if n.startsWith "@" then D.bot :: ds ++ (pairsOf g).map (fun (v, w) => D.many [v, w]) else ds)
  -- each point of the grid, with the bound variables at each value of their patterns
  let mut pts : List (List (String × D)) := []
  for pt in points grids do
    let mut ext : List (List (String × D)) := [pt]
    for (n, t) in binds do
      match (eval x0 pt t).run {} with
      | .error e => return { r with skip := some s!"at {showPoint c pt}: {e}" }
      | .ok (d, fl) =>
        if !fl.silent.isEmpty || !fl.param.isEmpty then
          return { r with skip := some s!"the pattern bound to {n} reads the interpretation at {showPoint c pt}" }
        match d.elems with
        | none => return { r with skip := some s!"the pattern bound to {n} denotes every element" }
        | some vs => ext := ext.flatMap fun e => vs.map fun v => e ++ [(n, D.val v)]
    pts := pts ++ ext
  let leftKey : Option String := match sides a.pattern with
    | some (.app h ss _, _) => some (appKey h ss)
    | _ => none
  let premise := match a.pattern with
    | .implies _ p _ => p
    | _ => .top (.var ⟨⟨⟨"R"⟩⟩⟩)
  let mut r := { r with points := pts.length, bound := binds.map (·.1), setVar := fv.any (·.1.startsWith "@") }
  for pt in pts do
    let mut dep := false
    let mut off := false
    let mut okAll := true
    for x in xs do
      if x.mode != Mode.none && !dep then break
      match (eval x pt a.pattern).run {} with
      | .error e => return { r with skip := some s!"at {showPoint c pt}: {e}" }
      | .ok (d, fl) =>
        let isDep := !fl.silent.isEmpty || !fl.param.isEmpty
        if isDep then
          dep := true
          let onLeft := leftKey.any fun k => fl.silent.contains k || fl.param.contains k || fl.param.contains (k ++ " (reads H)")
          if !onLeft then off := true
        let holds := match d with | .top => true | _ => false
        if !holds then
          okAll := false
          if !r.failModes.contains x.mode.name then r := { r with failModes := r.failModes ++ [x.mode.name] }
          let first := if isDep then r.nhfail < 8 else r.ncex < 8
          let msg := if !first then "" else
            let sd := match sides a.pattern with
              | some (l, rr) =>
                let l' := match (eval x pt l).run {} with | .ok (d, _) => showD c d | .error e => e
                let r' := match (eval x pt rr).run {} with | .ok (d, _) => showD c d | .error e => e
                s!"left {l'}, right {r'}"
              | none => ""
            s!"{x.mode.name} at {showPoint c pt}: {sd}" ++ (if isDep then s!" (reached {fl.silent ++ fl.param})" else "")
          if isDep then r := { r with nhfail := r.nhfail + 1, hfail := if first then r.hfail ++ [msg] else r.hfail }
          else
            let nc := pt.any fun (_, d) => match d with | .val v => nonCanon v | _ => false
            r := { r with ncex := r.ncex + 1, ncexNC := r.ncexNC + (if nc then 1 else 0),
                          ncexTwo := r.ncexTwo + (if pt.any (·.2.isMany) then 1 else 0),
                          cex := if first then r.cex ++ [msg] else r.cex, cexPts := r.cexPts ++ [pt] }
    match (eval x0 pt premise).run {} with
    | .ok (.top, _) => r := { r with active := r.active + 1 }
    | _ => pure ()
    if dep then r := { r with hdep := r.hdep + 1 }
    if off then r := { r with hOff := r.hOff + 1 }
    if okAll then r := { r with holds := r.holds + 1 }
  return r

/-- What the reading owes for the sentence: first what its class's direction (`dirOf`) makes it
- `no direction`: it applies a symbol Γ does not have, and states nothing of Γ's symbols;
- `Γ's item`: an item of Γ is its translation (`equal`, `weaker`);
- `owed`: Γ is to entail it (`entailed`, `atValues`);
- `hypothesis`: Γ does not hold it, the statements take it (`hypothesis`);
then what the probe finds:
- nothing more: it holds at every point under every reading;
- `, reads H`: it holds at every point, and at some point reads the interpretation where its left
  side (the application whose value it states) is not at a point the interpretation gives;
- `; holds only under some H, met by M`: it fails under some reading, only at points reading the
  interpretation, and holds at every point under the readings M (`met by none probed` where every
  reading fails it): a condition on the interpretation;
- `no model`: it fails at a point reading nothing of the interpretation, so Γ with it has no model
  whatever the interpretation (for a hypothesis: no interpretation meets it); `no model, at
  non-canonical fractions only` where every such point holds a `<I, J>Rat` that is no fraction in
  lowest terms; `refuted` for a class of direction `refuted`, whose claim that is;
- `; not probed: R`: the probe has no value of a variable's sort or no meaning for a construct. -/
def owes (allModes : List String) (r : Res) : String :=
  if r.cls == "no direction" then "no direction" else
  let base := match dirOf r.cls with
    | some .equal | some .weaker => "Γ's item"
    | some .hypothesis => "hypothesis"
    | _ => "owed"
  match r.skip with
  | some e =>
    -- the reason, without the point at which it was met
    let e := if e.startsWith "at " then ": ".intercalate ((e.splitOn ": ").drop 1) else e
    s!"{base}; not probed: {e}"
  | none =>
    if r.ncex > 0 then
      if dirOf r.cls == some .refuted then "refuted"
      else if r.ncexNC == r.ncex then "no model, at non-canonical fractions only" else "no model"
    else if r.nhfail > 0 then
      let met := allModes.filter (!r.failModes.contains ·)
      s!"{base}; holds only under some H, met by {if met.isEmpty then "none probed" else toString met}"
    else if r.hOff > 0 then base ++ ", reads H" else base

/-- The verdict's kind, for the counts: `owes` without the reason a sentence is not probed and
without the readings meeting a condition, except `none probed`. -/
def kindOf (o : String) : String :=
  match o.splitOn "; not probed" with
  | b :: _ :: _ => b ++ "; not probed"
  | _ =>
    if (o.splitOn "met by none probed").length > 1 then o
    else match o.splitOn " met by " with
      | b :: _ :: _ => b ++ " met by some"
      | _ => o

def verdict (r : Res) : String :=
  match r.skip with
  | some e => s!"not probed: {e}"
  | none =>
    let pts := s!"{r.points} points (premise holds at {r.active}, reads H at {r.hdep}{if r.hOff > 0 then s!", {r.hOff} of them off the left side" else ""})"
    if r.ncex > 0 then s!"{pts}: COUNTEREXAMPLE ({r.ncex} points{if r.ncexNC > 0 then s!", {r.ncexNC} at a non-canonical fraction" else ""}; first: {r.cex.headD ""})"
    else if r.nhfail > 0 then s!"{pts}: FAILS UNDER SOME H ({r.nhfail} point-readings; first: {r.hfail.headD ""}) [fails under {r.failModes}]"
    else s!"{pts}: holds"

/-- The readings: `HookParams.none` first, the two constant ones, `HookParams.lib` and the hash. -/
def modes : List Mode := [.none, .pick 0, .pick 1, .lib, .hash]

/-- The readings under which a sentence fails at a point, each evaluated, and whether its evaluation
under `HookParams.none` reads the interpretation there (where it does not, it evaluates the same
under every reading). -/
def failsAt (xs : List Ctx) (a : Kore.Axiom) (pt : List (String × D)) : Except String (List String × Bool) := do
  let mut ms : List String := []
  let mut dep := false
  for x in xs do
    let (d, fl) ← (eval x pt a.pattern).run {}
    if x.mode == Mode.none then dep := !fl.silent.isEmpty || !fl.param.isEmpty
    match d with
    | .top => pure ()
    | _ => ms := ms ++ [x.mode.name]
  return (ms, dep)

/-- Points of a sentence checked one by one (`failsAt`, `expectedPinned`): rat.md:109's two of
`kk:t240-rat-ceil-div`, `@R1 = {1}`, `@R2 = {<0, 2>Rat}` and `@R1 = {0}`, `@R2 = {0, 1}`. -/
def pinned (x : Ctx) : List (String × List (List (String × D))) :=
  match (kernelSorts x.c).find? (x.c.sortName · == "Rat"), x.syms.lookup ownGrids.ratCtorName with
  | some r, some q =>
    let ri (i : Int) : GroundTerm := .inj Srt.int r (int i);
    [("rat.md:109",
      [[("@VarR1", .val (ri 1)), ("@VarR2", .val (.ctor q.name [int 0, int 2]))],
       [("@VarR1", .val (ri 0)), ("@VarR2", .many [ri 0, ri 1])]])]
  | _, _ => []

/-- The text without the user module's sentences the reader refuses as builtin sentences outside
the library's text (`builtinText`) or as a subsort axiom whose lower sort is K (`sortAboveK`), none
of which is about a name of the definition's own; the sentences read as the definition's own are
kept. -/
def withoutRefused (k : Kore.Definition) : Kore.Definition × List String :=
  let off := Parse.preludeLength k
  let rs := (Parse.refusals k).filter (fun r => r.reason.name == "builtinText" || r.reason.name == "sortAboveK")
  let ix := rs.filterMap (·.index)
  match k.modules.getLast? with
  | none => (k, [])
  | some m =>
    let m' := { m with sentences := (m.sentences.zipIdx.filter fun (_, i) => !ix.contains (off + i)).map (·.1) }
    ({ k with modules := k.modules.dropLast ++ [m'] }, rs.map (·.head))

/-- Probe the sentences about the definition's own names (`isOwnAbout`) of the text at `path`
whose index `sel` admits; print a line for each as it is done; return each one's name, class and
`owes`. -/
def run (path : String) (sel : Nat → Bool := fun _ => true) : IO (List (Res × String)) := do
  -- `#eval` shows what it prints when it ends; OWNPROBE_LOG names a file each line is added to as it
  -- is printed
  let logTo ← IO.getEnv "OWNPROBE_LOG"
  let from_ := ((← IO.getEnv "OWNPROBE_FROM").bind (·.toNat?)).getD 0
  let say (l : String) : IO Unit := do
    IO.println l
    if let some f := logTo then
      let h ← IO.FS.Handle.mk f .append
      h.putStrLn l
      h.flush
  let text ← IO.FS.readFile path
  let k ← match Kore.parseDefinition text with
    | .ok k => pure k
    | .error e => throw (IO.userError s!"read: {e}")
  let (k, refused) := withoutRefused k
  say s!"{path}: refused and left out: {refused}"
  let d ← match Parse.parse k with
    | .ok d => pure d
    | .error e => throw (IO.userError s!"parse: {e.toText}")
  let c := d.sem
  let user := (k.modules.getLast?.map (·.name.ident.name)).getD ""
  let names := ownDeclNames k
  let xs := Ctx.all c modes true
  let x0 ← match xs with
    | x :: _ => pure x
    | [] => throw (IO.userError "no reading")
  say s!"{path}: user module {user}, {names.length} names declared as the definition's own; grids of its sorts: {x0.extra.map fun (s, g) => (c.sortName s, g.length)}"
  let gNames := (x0.syms.map (·.1)) ++ ["inj"]
  let mut res : List (Res × String) := []
  let mut setVars : List String := []
  for ad in k.axiomDecls do
    if ad.module != user || !isOwnAbout names ad.ax || !sel ad.index || ad.index < from_ then continue
    let syms := (appsOf ad.ax.pattern).eraseDups
    let absent := syms.filter (!gNames.contains ·)
    let cls := tieClassOf c x0.syms absent ad.ax
    let place := placeOf ad.ax.attributes
    let name := if place != "-" then place else
      ((isFunctionalShape ad.ax.pattern).map fun (h, ss) => appKey h ss).getD "-"
    let r : Res := { index := ad.index, place, name, cls, syms, absent }
    let t0 ← IO.monoMsNow
    let r := if absent.isEmpty then probe x0 xs r ad.ax else { r with skip := some s!"applies symbols Γ does not have: {absent}" }
    let r := { r with cls := reclass r.cls r.ncexTwo }
    let pinnedAt ← match (pinned x0).lookup name with
      | none => pure []
      | some pts => pts.mapM fun pt => match failsAt xs ad.ax pt with
        | .ok v => pure v
        | .error e => throw (IO.userError s!"{name} at {showPoint c pt}: {e}")
    let r := { r with pinnedAt }
    let t1 ← IO.monoMsNow
    if r.setVar then setVars := setVars ++ [name]
    let o := owes (modes.map (·.name)) r
    say s!"#{r.index} {name} [{r.cls}] {o} | {verdict r}{if r.bound.isEmpty then "" else s!" (bound {r.bound})"} ({(t1 - t0) / 1000} s)"
    for m in r.cex.drop 1 do say s!"    also {m}"
    for m in r.hfail.drop 1 do say s!"    also {m}"
    res := res ++ [(r, o)]
  say s!"sentences with a free set variable: {setVars}"
  return res

/-- How many sentences of each class have each verdict kind (`kindOf`), in the order first met. -/
def tally (rs : List (Res × String)) : List (String × String × Nat) :=
  let keys := (rs.map fun (r, o) => (r.cls, kindOf o)).eraseDups
  keys.map fun (c, k) => (c, k, (rs.filter fun (r, o) => r.cls == c && kindOf o == k).length)

/-- The Int value of a variable at a point. -/
def intAt (pt : List (String × D)) (n : String) : Option Int :=
  match pt.lookup n with
  | some (.val (.dv _ (.int i))) => some i
  | _ => none

/-- The sentences with a counterexample that the text refutes, each with the points where it does:
rat.md:173 (`makeRat(I, J, D) => makeRat(0 -Int I, 0 -Int J, D) requires J <Int 0`) at J = D < 0,
where rat.md:171 (`=> I /Int D requires J ==Int D`) also applies and the text states two values of
`makeRat(I, J, D)`, the integer I /Int D and the pair `<0 -Int (I /Int D), -1>Rat` (at I = J = D = -3,
1 and `<-1, -1>Rat`, which Γ holds apart): the reading reads the three equations of `makeRat/3` as
written, all of one priority, and a text holding them has no model (Kore-in-K entry
`kk:t239-rat-makerat-overlap`); rat.md:109 (`#Ceil(@R1 /Rat @R2) => {(@R2 =/=Rat 0) #Equals true}
#And #Ceil(@R1) #And #Ceil(@R2)`) where `@R1` holds a value and `@R2` is `{0, y}` with y no pair
`<0, J>Rat`: the quotient by y is a value whatever the interpretation gives a quotient by 0 (a
quotient by `<0, J>Rat` is one by 0, rat.md:152, 153), so the left side holds, and `@R2 =/=Rat 0`
denotes both `false` and `true`, so the right side does not (Kore-in-K entry `kk:t240-rat-ceil-div`); minRat's second equation (rat.md:221, `minRat(R, S) => S requires
S <=Rat R`) and maxRat's (rat.md:224, `maxRat(R, S) => S requires S >=Rat R`) where one argument is
`<0, J>Rat` and the other the integer 0: each is `<=Rat` (and `>=Rat`) the other, so both equations
of the function apply, the first (rat.md:220, 223) gives R and the second S, two elements Γ holds
apart. That is the disagreement test/RatNoModel.lean shows at `<1, 1>Rat` and 1 (`no_model`,
`no_model_min`: Γ of a text holding RAT has no model), here at a pair whose first component is 0
(Kore-in-K entry `kk:t242-rat-minmax-overlap`: both equations of maxRat, and both of minRat, apply at
`(<0, J>Rat, 0)` for every nonzero J, so in a model `<0, 1>Rat` and `<0, 2>Rat` would be one element,
which the constructor at different arguments is not). A counterexample at another point, or of
another sentence, is a finding. -/
def refutedByText : List (String × (List (String × D) → Bool)) :=
  [("rat.md:173", fun pt => match intAt pt "VarJ", intAt pt "VarD" with
    | some j, some d => j == d && j < 0
    | _, _ => false),
   ("rat.md:109", fun pt => match pt.lookup "@VarR1", pt.lookup "@VarR2" with
    | some d1, some (.many vs) =>
      let zero (v : GroundTerm) : Bool := match v with | .inj _ _ (.dv _ (.int 0)) => true | _ => false
      let zeroPair (v : GroundTerm) : Bool := match v with | .ctor _ [.dv _ (.int 0), _] => true | _ => false
      (match d1 with | .val _ | .many _ => true | _ => false) &&
        vs.length == 2 && vs.any zero && !vs.any zeroPair
    | _, _ => false),
   ("rat.md:221", zeroPairAndZero), ("rat.md:224", zeroPairAndZero)]
where
  /-- `{VarR, VarS}` is `{<0, J>Rat, 0}`. -/
  zeroPairAndZero (pt : List (String × D)) : Bool :=
    let zp (d : Option D) : Bool := match d with
      | some (.val (.ctor _ [.dv _ (.int 0), _])) => true
      | _ => false
    let z (d : Option D) : Bool := match d with
      | some (.val (.inj _ _ (.dv _ (.int 0)))) => true
      | _ => false
    (zp (pt.lookup "VarR") && z (pt.lookup "VarS")) || (z (pt.lookup "VarR") && zp (pt.lookup "VarS"))

/-- The sentences whose verdict is not their class's plain one (`plain`), by name with their verdict:
- the `functional` sentences of REQUIRES-ENSURES' constructors `#ruleEnsures`, `#ruleNoConditions`,
  `#ruleRequires`, `#ruleRequiresEnsures` (constructor functional: owed, Γ's constructor axioms
  entail it), not probed: no grid for `#RuleBody`;
- `String2KVar`'s `functional` sentence (parameter functional: KVAR's `String2KVar`, whose hook
  `STRING.string2token` no registry hook implements, is a parameter without hook; the sentence is the
  hypothesis on H the statements take, `ParamsTotal`): it holds under the readings that give
  `String2KVar` a `KVar` value at every string (`pick0`, `pick1`, `hash`) and fails under those that
  give it none (`HookParams.none`, `HookParams.lib`), which are no witness against it;
- `^Rat`'s `functional` sentence (function functional, `FnHyp`; `^Rat` is declared `total`): at
  `<0, 2>Rat ^Rat N` with N negative, rat.md:192 gives `(1 /Rat <0, 2>Rat) ^Rat (0 -Int N)` (the pair
  is `=/=Rat 0`), and rat.md:153 makes `1 /Rat <0, 2>Rat` the rest of `/Rat` at `(2, 0)`: the readings
  giving that rest a value (`pick0`, `pick1`, `hash`) meet it, and those giving none do not;
- `freshKVar`'s `functional` sentence (function functional, `FnHyp`): its one equation
  (substitution.md:54) gives it `String2KVar`'s value, so the same readings meet it;
- rat.md:109 (`#Ceil(@R1 /Rat @R2) = {(@R2 =/=Rat 0) #Equals true} #And #Ceil(@R1) #And
  #Ceil(@R2)`, a lemma): refuted, at the points where `@R1` holds a value and `@R2` is 0 and a value
  no `<0, J>Rat` (`refutedByText`, `kk:t240-rat-ceil-div`), so of set-variable lemma (`reclass`). It also
  fails under every reading at points of one value each, there reading the interpretation: at
  `@R2 = {0}` `@R1 /Rat 0` is the function's rest, and under a reading giving it a value (`pick0`,
  `pick1`, `hash`) the left side holds and the right side does not; at `@R2 = {<0, 2>Rat}` rat.md:153
  makes `@R1 /Rat <0, 2>Rat` the rest at `(2 *Int @R1) /Rat 0`, and under a reading giving it none
  (`HookParams.none`, `HookParams.lib`) the left side does not hold and the right side does
  (`expectedPinned`);
- domains.md:171 (`arr(_, _, D)[_] => D [owise]`, function equation), not probed: its premise negates
  the other equation's (`\or`), which the probe does not evaluate;
- rat.md:173: no model, at the 21 points with J = D < 0 (`refutedByText`; first I = J = D = -3: left
  1, by rat.md:171, right `<-1, -1>Rat`);
- rat.md:224 and rat.md:221: no model, at the two points where one argument is `<0, 2>Rat` and the
  other 0 (`refutedByText`, `kk:t242-rat-minmax-overlap`; at `R = <0, 2>Rat`, `S = 0`: left
  `<0, 2>Rat`, by rat.md:223 or 220, right 0). -/
def expectedNoted : List (String × String) :=
  [("Lbl'Hash'ruleEnsures", "owed; not probed: no grid for sort 'Hash'RuleBody (variable K0)"),
   ("Lbl'Hash'ruleNoConditions", "owed; not probed: no grid for sort 'Hash'RuleBody (variable K0)"),
   ("Lbl'Hash'ruleRequires", "owed; not probed: no grid for sort 'Hash'RuleBody (variable K0)"),
   ("Lbl'Hash'ruleRequiresEnsures", "owed; not probed: no grid for sort 'Hash'RuleBody (variable K0)"),
   ("LblString2KVar'LParUndsRParUnds'KVAR-COMMON'Unds'KVar'Unds'String",
     "hypothesis; holds only under some H, met by [H=pick0, H=pick1, H=hash]"),
   ("Lbl'UndsXor-'Rat'Unds'", "hypothesis; holds only under some H, met by [H=pick0, H=pick1, H=hash]"),
   ("LblfreshKVar'LParUndsRParUnds'KVAR-COMMON'Unds'KVar'Unds'Int",
     "hypothesis; holds only under some H, met by [H=pick0, H=pick1, H=hash]"),
   ("rat.md:109", "refuted"),
   ("domains.md:171", "Γ's item; not probed: \\or not evaluated"),
   ("rat.md:173", "no model"),
   ("rat.md:224", "no model, at non-canonical fractions only"),
   ("rat.md:221", "no model, at non-canonical fractions only")]

/-- The count per class and verdict kind (`tally`) of the 140 sentences: 77 `functional` sentences
(31 of constructors, 27 of them probed; 31 of MINT's sort-parametric symbols, which Γ does not have;
14 of functions, 12 holding everywhere; `String2KVar`'s), 62 equations (58 holding at every point
under every reading, domains.md:171 not probed, rat.md:173 refuted, rat.md:221 and 224 refuted at
`<0, 2>Rat` and 0) and one lemma, refuted. -/
def expectedTally : List (String × String × Nat) :=
  [("constructor functional", "owed", 27),
   ("constructor functional", "owed; not probed", 4),
   ("no direction", "no direction", 31),
   ("parameter functional", "hypothesis; holds only under some H, met by some", 1),
   ("function functional", "hypothesis", 12),
   ("function functional", "hypothesis; holds only under some H, met by some", 2),
   ("set-variable lemma", "refuted", 1),
   ("function equation", "Γ's item", 58),
   ("function equation", "Γ's item; not probed", 1),
   ("function equation", "no model", 1),
   ("function equation", "no model, at non-canonical fractions only", 2)]

/-- What `failsAt` gives at the points of `pinned`: rat.md:109 at `@R1 = {1}`, `@R2 = {<0, 2>Rat}`
fails under `HookParams.none` and `HookParams.lib`, reading the interpretation (the rest of `/Rat` at
`(2, 0)`, which rat.md:153 makes `1 /Rat <0, 2>Rat`); at `@R1 = {0}`, `@R2 = {0, 1}` it fails under
every reading, reading nothing of the interpretation (`0 /Rat 1` is `0`). -/
def expectedPinned : List (String × List (List String × Bool)) :=
  [("rat.md:109", [(["H=none", "H=lib"], true), (modes.map (·.name), false)])]

def plain (o : String) : Bool := ["Γ's item", "owed", "hypothesis", "no direction"].contains o

def check (path : String) : IO Unit := do
  let rs ← run path
  let noted := (rs.filter fun (_, o) => !plain o).map fun (r, o) => (r.name, o)
  let t := tally rs
  IO.println s!"noted: {reprStr noted}"
  IO.println s!"tally: {reprStr t}"
  -- every counterexample is one the text states, at a point where it does
  for (r, _) in rs do
    if r.ncex > 0 then
      match refutedByText.lookup r.name with
      | none => throw (IO.userError s!"{path}: {r.name} has a counterexample not recorded as the text's: {r.cex.headD ""}")
      | some p =>
        let out := r.cexPts.filter (!p ·)
        unless out.isEmpty do
          throw (IO.userError s!"{path}: {r.name} refuted outside the points the text refutes it at: {out.take 3 |>.map fun pt => pt.map fun (n, _) => (n, intAt pt n)}")
        IO.println s!"{r.name}: {r.ncex} counterexamples, each where the text refutes it"
  let pins := (rs.filter fun (r, _) => !r.pinnedAt.isEmpty).map fun (r, _) => (r.name, r.pinnedAt)
  IO.println s!"at the pinned points: {reprStr pins}"
  if pins != expectedPinned then throw (IO.userError s!"{path}: at the pinned points {reprStr pins}, expected {reprStr expectedPinned}")
  if noted != expectedNoted then throw (IO.userError s!"{path}: verdicts {reprStr noted}, expected {reprStr expectedNoted}")
  if t != expectedTally then throw (IO.userError s!"{path}: tally {reprStr t}, expected {reprStr expectedTally}")
  IO.println s!"{path}: verdicts as expected; every counterexample is the text's own"

end KCore.OwnProbe

#eval KCore.OwnProbe.check "f2-examples/allbuiltins.kompile.kore"
