/-
  A function-overloaded symbol in a rule's left side, read through the cut (`Parse.ovlCut`), on
  K 7.1.337 kompile's KORE of three fixtures (test/constructs/fixtures/NAME; the kompiled texts in
  f2-examples with their paths restored). Run from the package root:
  `lake env lean test/OvlCutRule.lean`.

  - `e5-ovl-fun-lhs`: `capGas : Gas → Gas` overloads the function `capN : N → N`; the rule
    `<k> run(cap(G:Gas)) => done(G) </k>` is read with the left side `run(Ovl0)` and
    `pre := Ovl0 ∈ capGas(G)`. The left side applies no function-overloaded symbol: `ovlPatsOK`
    holds and the account names no `functionInPattern`. G is held by the right side under the
    constructor `done`, so the rule is read (no `openRefusal`). The symbols the reader cuts
    (`Names.ovlCutSyms`) are the built definition's `fnOvlSyms`.
  - `e5-ovl-fun-lhs-int`: `rule <k> run(dbl(_:Exp)) => done(0) </k>` beside an `[owise]` rule, with
    `dblExp : Exp → Exp` over `dblInt : Int → Int`: refused `openRequires`, the detail naming the
    variable (`_Gen0:Exp`) and the symbol `dblExp`.
  - `e5-ovl-fun-lhs-owise`: `e5-ovl-fun-lhs` beside `rule <k> run(G:Gas) => done(inf) </k> [owise]`:
    read. G is of the unconfined sort Gas, in a rule below another's priority, and the cut
    `Ovl0 ∈ capGas(G)` holds it (`memHeld`): `capGas`'s function overload `capN` takes an argument
    of the confined sort N, so an application of `capGas` that is a value's element has a value's
    element as its argument, and whether some G satisfies the cut at a matched value is decided
    over values. Without the cut counted the rule fails (`rulePlainHO1 false`); with it it holds
    (`rulePlainHO2 true`) and `openRefusal` gives none.
  - `e5-ovl-fun-lhs`'s rule with its right side replaced by its left side (`ovlCutOpenArm`): no
    part of the rule but the cut holds G, and the rule is read by the cut alone.
  - The emitted rule (`rulePattern`) carries the cut's membership beside the `requires`:
    `\and(lhs, \and(req, V ∈ g(P̄)))`, for any rule whose `pre` is one membership (kernel-checked),
    and on the rules read from `e5-ovl-fun-lhs` and `e5-ovl-fun-keep-run` (printed).
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- A term, variables by name. -/
partial def ovlCutTermStr (c : Semantics) (ns : List String) : Term → String
  | .var i => ns.getD i s!"?{i}"
  | .app f as => s!"{c.symName f}(" ++ ", ".intercalate (as.map (ovlCutTermStr c ns)) ++ ")"
  | .inj a b t => s!"inj[{c.sortName a},{c.sortName b}](" ++ ovlCutTermStr c ns t ++ ")"
  | .as t i => "(" ++ ovlCutTermStr c ns t ++ s!" as {ns.getD i s!"?{i}"})"
  | .dv s l => s!"dv[{c.sortName s}]({reprStr l})"

/-- A condition, terms as `ovlCutTermStr` prints them. -/
partial def ovlCutCondStr (c : Semantics) (ns : List String) : Cond → String
  | .top => "top"
  | .bot => "bot"
  | .and p q => "and(" ++ ovlCutCondStr c ns p ++ ", " ++ ovlCutCondStr c ns q ++ ")"
  | .or p q => "or(" ++ ovlCutCondStr c ns p ++ ", " ++ ovlCutCondStr c ns q ++ ")"
  | .mem s t u => s!"in[{c.sortName s}](" ++ ovlCutTermStr c ns t ++ ", " ++ ovlCutTermStr c ns u ++ ")"
  | _ => "other"

/-- The reader's verdict on the text at `path`: the refusal, or each rule's variables, left side and
`pre`, with `fnOvlSyms`, the symbols the reader cuts, `ovlPatsOK`, the account's
`functionInPattern` refusals and `coreOK`. -/
def ovlCutVerdict (path : String) : IO String := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile path) | return "KORE read error"
  let cuts := match k.modules.getLast? with
    | some m => match Parse.envOf m (Parse.scan m.sentences) with
      | .ok (E : Parse.Env) => E.N.ovlCutSyms.map fun (p : Sym × String) => p.1
      | .error _ => []
    | none => []
  return match Parse.parse k with
    | .error r => s!"{r.reason.name} ({r.detail})"
    | .ok d =>
      let c := d.sem
      let rules := (c.rules.zip d.pres.rules).map fun (r, p) =>
        s!"[{p.names}] {ovlCutTermStr c p.names r.lhs} pre {ovlCutCondStr c p.names r.pre}"
      s!"read; {rules}; fnOvlSyms {c.fnOvlSyms.map c.symName}; cut {cuts.map c.symName}; \
        ovlPatsOK {c.ovlPatsOK}; functionInPattern {(Parse.functionInPattern k d).map (·.detail)}; \
        coreOK {c.coreOK}"

/--
info: read; [[[G, 'Unds'DotVar0, Ovl0]] Lbl'-LT-'generatedTop'-GT-'(Lbl'-LT-'k'-GT-'(kseq(inj[Pgm,KItem](Lblrun(Ovl0)), dotk())), 'Unds'DotVar0) pre in[Gas](Ovl0, LblcapGas(G))]; fnOvlSyms [LblcapGas]; cut [LblcapGas]; ovlPatsOK true; functionInPattern []; coreOK true
openRequires (Var'Unds'Gen0:Exp: in a condition with a variable the left side binds (V ∈ LbldblExp(…)), under LbldblExp, of a sort the text leaves unconfined)
read; [[['Unds'Gen0, 'Unds'DotVar0]] Lbl'-LT-'generatedTop'-GT-'(Lbl'-LT-'k'-GT-'(kseq(inj[Pgm,KItem](Lblrun('Unds'Gen0)), dotk())), 'Unds'DotVar0) pre top, [[G, 'Unds'DotVar0, Ovl0]] Lbl'-LT-'generatedTop'-GT-'(Lbl'-LT-'k'-GT-'(kseq(inj[Pgm,KItem](Lblrun(Ovl0)), dotk())), 'Unds'DotVar0) pre in[Gas](Ovl0, LblcapGas(G))]; fnOvlSyms [LblcapGas]; cut [LblcapGas]; ovlPatsOK true; functionInPattern []; coreOK true
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← ovlCutVerdict "f2-examples/e5-ovl-fun-lhs.kompile.kore")
  IO.println (← ovlCutVerdict "f2-examples/e5-ovl-fun-lhs-int.kompile.kore")
  IO.println (← ovlCutVerdict "f2-examples/e5-ovl-fun-lhs-owise.kompile.kore")

/-- Each rule of the text at `path` as the reader reads it: its priority, the variables its left
side leaves open, whether the cut of its `pre` holds each (`memHeld`), `rulePlainHO1` (no variable
counted as held by a cut), `rulePlainHO2` (what `rulesPlain` asks) and `openRefusal`. -/
def ovlCutOpen (path : String) : IO String := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile path) | return "KORE read error"
  return match Parse.parse k with
    | .error r => s!"{r.reason.name} ({r.detail})"
    | .ok d =>
      let c := d.sem
      "\n".intercalate ((c.rules.zip d.pres.rules).map fun (r, p) =>
        s!"prio {r.prio}; opens {r.opens.map fun i => p.names.getD i ""}; memHeld {r.opens.map (memHeld c (varOccs r.lhs) r.pre)}; \
          rulePlainHO1 {c.rulePlainHO1 r}; rulePlainHO2 {c.rulePlainHO2 r}; \
          openRefusal {(Parse.openRefusal c r p.names).map (·.1.name)}")

/--
info: prio 200; opens []; memHeld []; rulePlainHO1 true; rulePlainHO2 true; openRefusal none
prio 50; opens [G]; memHeld [true]; rulePlainHO1 false; rulePlainHO2 true; openRefusal none
prio 50; opens [G]; memHeld [true]; rulePlainHO1 true; rulePlainHO2 true; openRefusal none
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← ovlCutOpen "f2-examples/e5-ovl-fun-lhs-owise.kompile.kore")
  IO.println (← ovlCutOpen "f2-examples/e5-ovl-fun-lhs.kompile.kore")

/-- The rules of the text at `path` with each right side replaced by the rule's left side, which
holds no variable the left side leaves open: as `ovlCutOpen` prints them, over the semantics with
those rules. -/
def ovlCutOpenArm (path : String) : IO String := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile path) | return "KORE read error"
  return match Parse.parse k with
    | .error r => s!"{r.reason.name} ({r.detail})"
    | .ok d =>
      let rs := d.sem.rules.map fun r => { r with rhs := r.lhs }
      let c := { d.sem with rules := rs }
      "\n".intercalate ((rs.zip d.pres.rules).map fun (r, p) =>
        s!"prio {r.prio}; opens {r.opens.map fun i => p.names.getD i ""}; held by the right side {r.opens.map (heldOccs c r.rhs).contains}; \
          memHeld {r.opens.map (memHeld c (varOccs r.lhs) r.pre)}; \
          rulePlainHO1 {c.rulePlainHO1 r}; rulePlainHO2 {c.rulePlainHO2 r}; \
          openRefusal {(Parse.openRefusal c r p.names).map (·.1.name)}")

/--
info: prio 50; opens [G]; held by the right side [false]; memHeld [true]; rulePlainHO1 false; rulePlainHO2 true; openRefusal none
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← ovlCutOpenArm "f2-examples/e5-ovl-fun-lhs.kompile.kore")

/-- A rule without existential variables whose `pre` is one membership `t ∈ u` and whose `post` is
`\top` is emitted with the membership beside its `requires`. -/
example (c : Semantics) (vs : List KoreAML.Var) (r : Rule) (s : Srt) (t u : Term) (hex : r.exs = [])
    (hpre : r.pre = .mem s t u) (hpost : r.post = .top) :
    rulePattern c vs r =
      .rewrites (srtOf c topCellSort)
        (.and (srtOf c topCellSort) [Term.kore c vs r.lhs,
          .and (srtOf c topCellSort) [reqPat (srtOf c topCellSort) (r.req.map (Term.kore c vs)),
            .in (srtOf c s) (srtOf c topCellSort) (Term.kore c vs t) (Term.kore c vs u)]])
        (.and (srtOf c topCellSort) [Term.kore c vs r.rhs, reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c vs))]) := by
  rw [rulePattern_noExs c vs r hex, rulePredPat_top hpost, hpre]; rfl

/-- Each rule of the text at `path`, emitted (`rulePattern`, under the presentation's names). -/
def ovlCutEmitted (path : String) : IO String := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile path) | return "KORE read error"
  return match Parse.parse k with
    | .error r => s!"{r.reason.name} ({r.detail})"
    | .ok d => "\n".intercalate ((d.sem.rules.zip d.pres.rules).map fun (r, p) =>
        Kore.Printer.pattern (rulePattern d.sem (KoreAML.varList (r.vars.map d.sem.sortName) p.names) r))

/--
info: \rewrites{SortGeneratedTopCell{}}(\and{SortGeneratedTopCell{}}(Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortPgm{}, SortKItem{}}(Lblrun{}(VarOvl0:SortGas{})), dotk{}())), Var'Unds'DotVar0:SortGeneratedCounterCell{}), \and{SortGeneratedTopCell{}}(\top{SortGeneratedTopCell{}}(), \in{SortGas{}, SortGeneratedTopCell{}}(VarOvl0:SortGas{}, LblcapGas{}(VarG:SortGas{})))), \and{SortGeneratedTopCell{}}(Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortPgm{}, SortKItem{}}(Lbldone{}(VarG:SortGas{})), dotk{}())), Var'Unds'DotVar0:SortGeneratedCounterCell{}), \top{SortGeneratedTopCell{}}()))
\rewrites{SortGeneratedTopCell{}}(\and{SortGeneratedTopCell{}}(Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortPgm{}, SortKItem{}}(Lblrun{}(VarOvl0:SortGas{})), dotk{}())), Var'Unds'DotVar0:SortGeneratedCounterCell{}), \and{SortGeneratedTopCell{}}(\top{SortGeneratedTopCell{}}(), \in{SortGas{}, SortGeneratedTopCell{}}(VarOvl0:SortGas{}, LblcapGas{}(VarG:SortGas{})))), \and{SortGeneratedTopCell{}}(Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortPgm{}, SortKItem{}}(Lbldone{}(VarG:SortGas{})), dotk{}())), Var'Unds'DotVar0:SortGeneratedCounterCell{}), \top{SortGeneratedTopCell{}}()))
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← ovlCutEmitted "f2-examples/e5-ovl-fun-lhs.kompile.kore")
  IO.println (← ovlCutEmitted "f2-examples/e5-ovl-fun-keep-run.kompile.kore")
