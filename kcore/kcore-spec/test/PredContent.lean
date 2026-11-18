/-
  The equations of a sort's predicate that a text holds, against the clauses the reading gives
  that predicate (`Semantics.sortPreds`): `Parse.predEqnOK`, `Parse.predProjOK?`,
  `Parse.predEqnFaults`, the reader's refusal (`Parse.coreOf`) and the account's
  (`Parse.consumedWith`). Run from the package root: `lake env lean -j1 test/PredContent.lean`.

  ## Hand-written equations, in the kernel (`Hand`)

  A semantics with one own sort Foo and a constructor `pair(Foo, Foo) : Foo`; its `sortPreds` hold
  `isFoo(kseq(inj{Foo,KItem}(V), dotk)) = true` and `isFoo(K) = false` at priority 200. Equations
  of `isFoo`:
  - `std`, `isFoo(kseq(inj{Foo,KItem}(V), dotk)) = true`;
  - `pair`, `isFoo(kseq(inj{Foo,KItem}(pair(K0, K1)), dotk)) = true requires isFoo(K0) andBool
    isFoo(K1)`;
  - `ow ds`, `isFoo(K) = false [owise]` with the exclusion's disjuncts `ds`: `dStd` excludes `std`,
    `dPair` excludes `pair`.
  `decide +kernel`:
  - the text `[ow [dStd], std]`: both are sentences the reading states, no fault;
  - `pair` is none, first or second among the equations without `[owise]`;
  - `ow []` (it says `false` where `std` says `true`), `ow [dPair, dStd]` and `ow [dStd, dPair]`
    (silent where the reading says `false`), `ow [dPair]`, and `ow [dStd, dStd]` are none;
  - `ow [dStd]` in a text that holds `pair` too is one (the fault is `pair`'s alone);
  - `ow [dStd]` in a text without `std` is none: no equation of the text reads to the clause its
    disjunct excludes;
  - the faults of `[ow [dPair, dStd], pair, std]` and of `[ow [dPair, dStd], std, pair]` are the
    `[owise]` equation's and `pair`'s, `generatedEquation`; with a user source, `unaccounted`.

  ## The fixtures' kompiled texts (K 7.1.337 kompile's KORE, from the cache `kfix.py` keeps)

  - `c3-strict-hybrid` and `e2-frontend-effect` (`pair` declared `hybrid`: the text holds
    `isKResult(pair(K0, K1)) = true requires isKResult(K0) andBool isKResult(K1)` and the `[owise]`
    equation excludes it): refused `generatedEquation`, two refusals, the `[owise]` equation and
    the pair equation.
  - `c3-strict-hybrid` with the standard equation moved before the pair equation: the same two.
  - `c3-strict-base` (the same text without `hybrid`): read, every sentence accounted for.
  - The account alone, the definition read from `c3-strict-base` and the sentences of
    `c3-strict-hybrid` in both orders: the `[owise]` equation and the pair equation are not
    accounted for, the standard equation is; none of the three is accounted for without the arm
    for the equations no function holds (`consumedWith false`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Parse

namespace PredContent

namespace Hand

open KoreAML (ev evar ap srt asK uidAttr attr srcAttr R)

def Foo : Srt := nRegSorts
def isFoo : Sym := nRegSyms
def pairS : Sym := nRegSyms + 1

def N : Names := { sorts := ["Foo"], syms := ["LblisFoo", "Lblpair"] }

/-- One own sort Foo, with `pair(Foo, Foo) : Foo`; no function, no rule. -/
def c : Semantics :=
  { lib := libOf [], sortNames := N.sorts, symNames := N.syms, userSorts := [Foo]
    ctors := [⟨pairS, [Foo, Foo], Foo⟩], fns := [], userSubsorts := [], pgmSort := Srt.k, rules := [] }

def tt : Kore.Pattern := .dv (srt "Bool") "true"
def ff : Kore.Pattern := .dv (srt "Bool") "false"
def item (p : Kore.Pattern) : Kore.Pattern := asK "Foo" p
def isFooP (p : Kore.Pattern) : Kore.Pattern := ap "LblisFoo" [item p]
def bothP (a b : Kore.Pattern) : Kore.Pattern := ap "Lbl'Unds'andBool'Unds'" [isFooP a, isFooP b]

def std : RawEqn := ⟨"LblisFoo", [item (ev "VarV" (srt "Foo"))], none, none, tt, [uidAttr "std"], none, false⟩

def pair : RawEqn :=
  ⟨"LblisFoo", [item (ap "Lblpair" [ev "VarK0" (srt "Foo"), ev "VarK1" (srt "Foo")])],
   some (bothP (ev "VarK0" (srt "Foo")) (ev "VarK1" (srt "Foo"))), none, tt, [uidAttr "pair"], none, false⟩

/-- A disjunct `\exists x̄. req ∧ X0 ∈ p ∧ \top`. -/
def disjunct (xs : List Kore.EVar) (req p : Kore.Pattern) : Kore.Pattern :=
  KoreAML.existsAll R xs (.and R [req, .and R [.in (srt "K") R (ev "X0" (srt "K")) p, .top R]])

def dStd : Kore.Pattern :=
  disjunct [evar "Var'Unds'Gen2" (srt "Foo")] (.top R) (item (ev "Var'Unds'Gen2" (srt "Foo")))

def dPair : Kore.Pattern :=
  let g0 := ev "Var'Unds'Gen0" (srt "Foo")
  let g1 := ev "Var'Unds'Gen1" (srt "Foo")
  disjunct [evar "Var'Unds'Gen0" (srt "Foo"), evar "Var'Unds'Gen1" (srt "Foo")]
    (.equals (srt "Bool") R (bothP g0 g1) tt) (item (ap "Lblpair" [g0, g1]))

def ow (ds : List Kore.Pattern) : RawEqn :=
  ⟨"LblisFoo", [ev "VarK" (srt "K")], none, some ds, ff, [uidAttr "ow", attr "owise"], none, false⟩

def ok (eqs : List RawEqn) (e : RawEqn) : Option Bool := predProjOK? N "" eqs c e

/-- The reading's predicate of Foo: the two clauses. -/
theorem isFoo_clauses : ((c.sortPreds.find? (·.label == isFoo)).map fun fn => fn.clauses.map (·.prio)) =
    some [50, 200] := by decide +kernel

/-- The two standard equations are the predicate's clauses. -/
theorem standard : ok [ow [dStd], std] std = some true ∧ ok [ow [dStd], std] (ow [dStd]) = some true ∧
    (predEqnFaults N "" [ow [dStd], std] c).length = 0 := by decide +kernel

/-- The pair equation is no clause of the predicate, first or second in the text. -/
theorem pair_none : ok [ow [dPair, dStd], pair, std] pair = some false ∧
    ok [ow [dPair, dStd], std, pair] pair = some false ∧ ok [ow [dStd], pair, std] pair = some false := by
  decide +kernel

/-- The standard equation is a clause beside the pair equation, in either order. -/
theorem std_beside : ok [ow [dPair, dStd], pair, std] std = some true ∧
    ok [ow [dPair, dStd], std, pair] std = some true := by decide +kernel

/-- An `[owise]` equation whose exclusion is not one disjunct for the clause before it. -/
theorem owise_none :
    ok [ow [], std] (ow []) = some false ∧
    ok [ow [dPair, dStd], pair, std] (ow [dPair, dStd]) = some false ∧
    ok [ow [dPair, dStd], std, pair] (ow [dPair, dStd]) = some false ∧
    ok [ow [dStd, dPair], pair, std] (ow [dStd, dPair]) = some false ∧
    ok [ow [dPair], pair, std] (ow [dPair]) = some false ∧
    ok [ow [dStd, dStd], std] (ow [dStd, dStd]) = some false ∧
    ok [ow [dStd]] (ow [dStd]) = some false := by decide +kernel

/-- The `[owise]` equation with the standard exclusion is the clause, whatever else the text holds. -/
theorem owise_beside : ok [ow [dStd], pair, std] (ow [dStd]) = some true := by decide +kernel

/-- The attributes of the equation a fault is at. -/
def at? (f : Fault) : List Kore.AppPattern := match f.site with
  | .attrs as => as
  | _ => []

/-- The faults of the text with the pair equation, in both orders: the `[owise]` equation's and the
pair equation's. -/
theorem faults :
    (predEqnFaults N "" [ow [dPair, dStd], pair, std] c).map (fun f => (f.reason, at? f)) =
      [(.generatedEquation, (ow []).attrs), (.generatedEquation, pair.attrs)] ∧
    (predEqnFaults N "" [ow [dPair, dStd], std, pair] c).map (fun f => (f.reason, at? f)) =
      [(.generatedEquation, (ow []).attrs), (.generatedEquation, pair.attrs)] := by
  decide +kernel

/-- Written in a user's file, the pair equation is refused `unaccounted`. -/
theorem fault_user :
    let src := srcAttr "/made-up/user.k"
    (predEqnFaults N "/made-up/user.k" [ow [dStd], { pair with attrs := pair.attrs ++ [src] }, std] c).map (·.reason) =
      [.unaccounted] := by decide +kernel

/-- An equation of another symbol is not these functions'. -/
theorem other : ok [std] { std with fn := "Lblpair" } = none := by decide +kernel

/-! ### An instance of `std` at a constructor pattern (`predInstOK`, `predInstAcc`) -/

/-- `pairT`, `isFoo(kseq(inj{Foo,KItem}(pair(K0, K1)), dotk)) = true`: `std` with the constructor
pattern `pair(K0, K1)` in V's place; `pairF` the same with `false`. -/
def pairT : RawEqn := { pair with req := none, attrs := [uidAttr "pairT"] }
def pairF : RawEqn := { pairT with rhs := ff, attrs := [uidAttr "pairF"] }

def dPairT : Kore.Pattern :=
  let g0 := ev "Var'Unds'Gen0" (srt "Foo")
  let g1 := ev "Var'Unds'Gen1" (srt "Foo")
  disjunct [evar "Var'Unds'Gen0" (srt "Foo"), evar "Var'Unds'Gen1" (srt "Foo")] (.top R) (item (ap "Lblpair" [g0, g1]))

/-- `pairT` is an instance of `std` (and `std` of itself, V in V's place); `pairF`, which gives the
other value, and `pair`, which has a `requires`, are not. -/
theorem inst : predInstOK N "" c pairT = true ∧ predInstOK N "" c pairF = false ∧
    predInstOK N "" c pair = false ∧ predInstOK N "" c std = true := by decide +kernel

/-- The text with `pairT` and its `[owise]` equation excluding it and `std`, in either order of the
disjuncts: no fault; `predProjOK?` still says neither is a clause of the predicate. -/
theorem inst_text :
    (predEqnFaults N "" [ow [dPairT, dStd], pairT, std] c).length = 0 ∧
    (predEqnFaults N "" [ow [dStd, dPairT], std, pairT] c).length = 0 ∧
    ok [ow [dPairT, dStd], pairT, std] pairT = some false ∧
    ok [ow [dPairT, dStd], pairT, std] (ow [dPairT, dStd]) = some false := by decide +kernel

/-- The text with `pairF` (a sentence contradicting the predicate's clause): both refused, as is an
`[owise]` equation that excludes `pairT` in a text without it. -/
theorem inst_false :
    (predEqnFaults N "" [ow [dPairT, dStd], pairF, std] c).map (fun f => (f.reason, at? f)) =
      [(.generatedEquation, (ow []).attrs), (.generatedEquation, pairF.attrs)] ∧
    (predEqnFaults N "" [ow [dPairT, dStd], std] c).map (·.reason) = [.generatedEquation] := by
  decide +kernel

/-- **`Γ` entails `pairT`'s equation**, for the semantics `c` (`GenEqs.predInst_entailed`). -/
theorem inst_entailed : ∃ fn ∈ c.sortPreds, c.symName fn.label = "LblisFoo" ∧ ∃ cl cp,
    clause? N "" pairT none = .ok (cl, cp) ∧
    ∀ it ∈ Faithful.kernelItems [Faithful.prioEquation c fn cl], Faithful.Γ c ⊧ it.pat :=
  GenEqs.predInst_entailed (by decide +kernel) inst.1

end Hand

def cacheDir : IO String := do
  let get := fun (n : String) => do
    match ← IO.getEnv n with
    | some d => pure (if d.isEmpty then none else some d)
    | none => pure none
  if let some d ← get "KCORE_KFIX_CACHE" then return d
  if let some d ← get "XDG_CACHE_HOME" then return s!"{d}/kcore-kfix"
  let home := (← get "HOME").getD "."
  return s!"{home}/.cache/kcore-kfix"

/-- The kompiled text of fixture `n`, its `BUILTIN/` and `FIXTURE/` paths restored to made-up
directories (as `kfix.py accounts` restores them before reading). -/
def load (n : String) : IO Kore.Definition := do
  let t ← IO.FS.readFile s!"test/constructs/fixtures/{n}/kompile.txt"
  let some l := (t.splitOn "\n").find? (·.startsWith "definition.kore sha256: ")
    | throw (IO.userError s!"{n}: kompile.txt names no sha256")
  let sha := (l.splitOn ": ").getD 1 ""
  let raw ← IO.FS.readFile s!"{← cacheDir}/{sha}.kore"
  let raw := ((raw.replace "BUILTIN/" "/made-up-k/include/kframework/builtin/").replace "FIXTURE/" "/made-up-fx/").replace
    "FIXTURE" "/made-up-fx"
  match Kore.parseDefinition raw with
  | .ok k => pure k
  | .error e => throw (IO.userError s!"{n}: KORE read error {e}")

/-- The equation of `LblisKResult` a sentence is, by its kind: `owise`, `pair` (it has a
`requires`) or `standard`. -/
def kind? (s : Kore.Sentence) : Option String :=
  match s with
  | .axiom a => (rawEqn? a).bind fun e =>
    if e.fn != "LblisKResult" then none
    else some (if e.competitors.isSome then "owise" else if e.req.isSome then "pair" else "standard")
  | _ => none

/-- The text with the standard equation of `isKResult` moved before the pair equation. -/
def standardFirst (k : Kore.Definition) : Kore.Definition :=
  let move := fun (ss : List Kore.Sentence) =>
    let stds := ss.filter (kind? · == some "standard")
    ss.flatMap fun s => match kind? s with
      | some "pair" => stds ++ [s]
      | some "standard" => []
      | _ => [s]
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := move m.sentences }]).getD [] }

/-- The order of the equations of `isKResult` in the text, the reader's verdict, and each refusal
(its reason and which equation). -/
def verdict (n : String) (edit : Kore.Definition → Kore.Definition := id) : IO Unit := do
  let k := edit (← load n)
  let some m := k.modules.getLast? | throw (IO.userError "no module")
  let off := preludeLength k
  IO.println s!"{n}: equations of isKResult in text order: {m.sentences.filterMap kind?}"
  match Parse.parse k with
  | .ok d => IO.println s!"  read; read and not accounted for: {(unconsumed k d).length}"
  | .error r => IO.println s!"  refused {r.reason.name} at the {((r.index.bind fun i => m.sentences[i - off]?).bind kind?).getD "?"} equation"
  for r in refusals k do
    IO.println s!"  refusal: {r.reason.name}, the {((r.index.bind fun i => m.sentences[i - off]?).bind kind?).getD "?"} equation: {r.detail}"

/--
info: c3-strict-hybrid: equations of isKResult in text order: [owise, pair, standard]
  refused generatedEquation at the owise equation
  refusal: generatedEquation, the owise equation: LblisKResult: LblisKResult(_) = "false" [owise]
  refusal: generatedEquation, the pair equation: LblisKResult: LblisKResult(kseq(inj(Lblpair(_, _)), dotk)) = "true" requires Lbl'Unds'andBool'Unds'(LblisKResult(kseq(inj(…), dotk)), LblisKResult(kseq(inj(…), dotk)))
c3-strict-hybrid: equations of isKResult in text order: [owise, standard, pair]
  refused generatedEquation at the owise equation
  refusal: generatedEquation, the owise equation: LblisKResult: LblisKResult(_) = "false" [owise]
  refusal: generatedEquation, the pair equation: LblisKResult: LblisKResult(kseq(inj(Lblpair(_, _)), dotk)) = "true" requires Lbl'Unds'andBool'Unds'(LblisKResult(kseq(inj(…), dotk)), LblisKResult(kseq(inj(…), dotk)))
e2-frontend-effect: equations of isKResult in text order: [owise, pair, standard]
  refused generatedEquation at the owise equation
  refusal: generatedEquation, the owise equation: LblisKResult: LblisKResult(_) = "false" [owise]
  refusal: generatedEquation, the pair equation: LblisKResult: LblisKResult(kseq(inj(Lblpair(_, _)), dotk)) = "true" requires Lbl'Unds'andBool'Unds'(LblisKResult(kseq(inj(…), dotk)), LblisKResult(kseq(inj(…), dotk)))
c3-strict-base: equations of isKResult in text order: [owise, standard]
  read; read and not accounted for: 0
-/
#guard_msgs in
#eval show IO Unit from do
  verdict "c3-strict-hybrid"
  verdict "c3-strict-hybrid" standardFirst
  verdict "e2-frontend-effect"
  verdict "c3-strict-base"

/-- The account of the equations of `isKResult` of the text `n` (edited by `edit`) by the
definition read from `c3-strict-base`: `consumed`, and `consumedWith false`. -/
def account (n : String) (edit : Kore.Definition → Kore.Definition := id) : IO Unit := do
  let d ← match Parse.parse (← load "c3-strict-base") with
    | .ok d => pure d
    | .error r => throw (IO.userError s!"c3-strict-base: refused: {r.toText}")
  let k := edit (← load n)
  let some m := k.modules.getLast? | throw (IO.userError "no module")
  let S := scan m.sentences
  let E ← match envOf m S with
    | .ok E => pure E
    | .error f => throw (IO.userError s!"envOf: {f.reason.name} {f.detail}")
  for s in m.sentences do
    if let some kd := kind? s then
      IO.println s!"{n}, {kd}: accounted {consumed S E d s}, without the arm {consumedWith false S E d s}"

/--
info: c3-strict-hybrid, owise: accounted false, without the arm false
c3-strict-hybrid, pair: accounted false, without the arm false
c3-strict-hybrid, standard: accounted true, without the arm false
c3-strict-hybrid, owise: accounted false, without the arm false
c3-strict-hybrid, standard: accounted true, without the arm false
c3-strict-hybrid, pair: accounted false, without the arm false
c3-strict-base, owise: accounted true, without the arm false
c3-strict-base, standard: accounted true, without the arm false
-/
#guard_msgs in
#eval show IO Unit from do
  account "c3-strict-hybrid"
  account "c3-strict-hybrid" standardFirst
  account "c3-strict-base"

end PredContent
