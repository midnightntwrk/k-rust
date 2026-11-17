/-
  A rule cut at a function-overloaded symbol whose function overload takes an argument of an
  unconfined sort (CN-4b §3.2): its cut variable is not decided by values. Run from the package
  root: `lake env lean -j1 test/OvlHeldRefused.lean`. Kernel-checked (`decide +kernel`) but the
  reader's details (`#eval`).

  The semantics is the reader's for `f2-examples/ovlsub.kompile.kore` (`ovlsub.k`) with a function
  `fI : Int -> Gas` added to `capGas`'s overloads (`cInt`), in the place of §3.2's `dbl` and its
  overload `dbl : Int -> Int` (no text the reader reads has a function overload). Gas and Int are
  unconfined. The rules, at the cut's shape (V the variable 0, E the variable 2, both Gas):
  - `rA`: `run(V) => done(inf)`, `pre := V ∈ capGas(E)` (§3.2's `=> done(0)`);
  - `rB`: `run(V) => done(E)`, the same `pre`;
  - `rO`: `run(G) => done(inf)` of priority 200, the `[owise]` rule.

  - `capGas` is not `ovlHeld` (its function overload takes Int), so `memHeld` does not hold E, at
    HO-1's `holds` and at HO-2's (`ovlHeld` being the disjunct HO-2 adds).
  - The conjuncts of `rulePlainPP`, and of its HO-2 form `rulePlainHeld` (conf widened by
    `memHeld`, CN-4b §3.3), each by itself: `rB` beside `rO` passes the arms (E by arm A) and fails
    the competition conjunct; `rB` alone passes both; `rA` fails the arms, alone and beside `rO`.
  - The reader's `openRefusal`: `openRequires`, naming E, its sort and `capGas`, for `rA` and for
    `rB` beside `rO`; `none` for `rB` alone.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace OvlHeldRefused

definition_of defn from "f2-examples/ovlsub.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def capN : Sym := 387
def symDone : Sym := 388
def symInf : Sym := 389
def symRun : Sym := 390
def capGas : Sym := 394
def gasS : Srt := 32
def cntS : Srt := 19
def fI : Sym := 5000

/-- `<generatedTop>(<k>(kseq(inj{Pgm,KItem}(x), dotk)), cnt)`, as the reader writes ovlsub's rules. -/
def cfg (x cnt : Term) : Term :=
  .app 71 [.app 385 [.app 0 [.inj 34 1 x, .app 1 []]], cnt]

/-- ovlsub's semantics with `fI : Int -> Gas` among `capGas`'s overloads. -/
noncomputable def cInt : Semantics :=
  { c with ovls := [⟨⟨capGas, [gasS], gasS⟩, [capN, fI]⟩],
           fns := c.fns ++ [{ label := fI, args := [Srt.int], result := gasS, clauses := [] }] }

/-- The cut `V ∈ capGas(E)`. -/
def cutE : Cond := .mem gasS (.var 0) (.app capGas [.var 2])
def rA : Rule :=
  { vars := [gasS, cntS, gasS], lhs := cfg (.app symRun [.var 0]) (.var 1), req := none,
    rhs := cfg (.app symDone [.app symInf []]) (.var 1), ens := none, pre := cutE, prio := 50 }
def rB : Rule := { rA with rhs := cfg (.app symDone [.var 2]) (.var 1) }
def rO : Rule :=
  { vars := [gasS, cntS], lhs := cfg (.app symRun [.var 0]) (.var 1), req := none,
    rhs := cfg (.app symDone [.app symInf []]) (.var 1), ens := none, prio := 200 }

/-- The arms of `rulePlainPP` for one rule, with `conf` given. -/
def arms (c : Semantics) (r : Rule) (conf : Nat → Bool) : Bool :=
  let rest := varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post
  let condApart := r.reqClosed && r.condVars.all fun j => !rest.contains j
  r.opens.all (fun i => (ctorOccs c r.rhs).contains i || conf i || (r.condVars.contains i && condApart))
/-- The competition conjunct of `rulePlainPP` for one rule, with `conf` given. -/
def compete (c : Semantics) (r : Rule) (conf : Nat → Bool) : Bool :=
  !r.reqOpen || !c.rules.any (fun r' => r.prio < r'.prio) || r.openCondVars.all conf || r.reqClosed
/-- `rulePlainPP`'s `conf`, and HO-2's: confined, or held by a cut (`memHeld`). -/
def confPP (c : Semantics) (r : Rule) (i : Nat) : Bool := (r.vars[i]?.map c.confined).getD false
def confHeld (c : Semantics) (r : Rule) (i : Nat) : Bool := confPP c r i || memHeld c (varOccs r.lhs) r.pre i
/-- `rulePlainPP` with HO-2's `conf`. -/
def rulePlainHeld (c : Semantics) (r : Rule) : Bool := arms c r (confHeld c r) && compete c r (confHeld c r)

/-- `rulePlainPP` is its two conjuncts. -/
theorem rulePlainPP_eq (c : Semantics) (r : Rule) :
    c.rulePlainPP r = (arms c r (confPP c r) && compete c r (confPP c r)) := rfl

theorem names_ok : c.symName capGas = "LblcapGas" ∧ c.symName symRun = "Lblrun" ∧ c.symName symDone = "Lbldone" ∧
    c.symName symInf = "Lblinf" ∧ c.sortName gasS = "Gas" ∧ c.isOvl capGas = true := by
  decide +kernel

/-- `capGas`'s function overload takes Int, which is not confined; Gas is not confined; so
`capGas` is not `ovlHeld`, and neither `holds` nor `memHeld` holds E. -/
theorem not_held : (cInt.fnOverloads capGas).map (·.label) = [fI] ∧
    cInt.confined Srt.int = false ∧ cInt.confined gasS = false ∧ cInt.ovlHeld capGas = false ∧
    cInt.holds capGas = false ∧ memHeld cInt [0, 1] cutE 2 = false ∧
    varOccs rA.lhs = [0, 1] ∧ rA.opens = [2] ∧ rA.openCondVars = [2] ∧ rA.reqClosed = false := by
  decide +kernel

/-- `rB` beside the `[owise]` rule: E passes arm A, and the competition conjunct fails. -/
theorem rB_owise : let c' := { cInt with rules := [rB, rO] }
    arms c' rB (confPP c' rB) = true ∧ compete c' rB (confPP c' rB) = false ∧
    arms c' rB (confHeld c' rB) = true ∧ compete c' rB (confHeld c' rB) = false ∧
    c'.rulePlainPP rB = false ∧ rulePlainHeld c' rB = false := by
  decide +kernel

/-- `rB` alone passes both conjuncts. -/
theorem rB_alone : let c' := { cInt with rules := [rB] }
    arms c' rB (confPP c' rB) = true ∧ compete c' rB (confPP c' rB) = true ∧
    c'.rulePlainPP rB = true ∧ rulePlainHeld c' rB = true := by
  decide +kernel

/-- `rA` fails the arms alone, and beside the `[owise]` rule. -/
theorem rA_alone : let c' := { cInt with rules := [rA] }
    arms c' rA (confPP c' rA) = false ∧ arms c' rA (confHeld c' rA) = false ∧ c'.rulePlainPP rA = false := by
  decide +kernel

theorem rA_owise : let c' := { cInt with rules := [rA, rO] }
    arms c' rA (confHeld c' rA) = false ∧ rulePlainHeld c' rA = false := by
  decide +kernel

/-- The reader's details, at the same rules over the semantics read at run time. -/
def details : IO Unit := do
  match Kore.parseDefinition (← IO.FS.readFile "f2-examples/ovlsub.kompile.kore") with
  | .error e => IO.println s!"KORE read error {e}"
  | .ok k =>
    match Parse.parse k with
    | .error r => IO.println s!"refused {repr r.reason} {r.detail}"
    | .ok d =>
      let c0 := d.sem
      let fnI : Fn := { label := fI, args := [Srt.int], result := gasS, clauses := [] }
      let ci := { c0 with ovls := [⟨⟨capGas, [gasS], gasS⟩, [capN, fI]⟩], fns := c0.fns ++ [fnI] }
      let row := fun (n : String) (rs : List Rule) =>
        let shown := match Parse.openRefusal { ci with rules := rs } (rs.headD rO) ["V", "C", "E"] with
          | none => "none"
          | some (why, detail) => s!"{repr why} {detail}"
        IO.println s!"{n}: {shown}"
      row "rA" [rA]
      row "rA+owise" [rA, rO]
      row "rB" [rB]
      row "rB+owise" [rB, rO]

/--
info: rA: KCore.Parse.RefusalReason.openRequires VarE:Gas: in a condition with a variable the left side binds (V ∈ LblcapGas(…)), under LblcapGas, of a sort the text leaves unconfined
rA+owise: KCore.Parse.RefusalReason.openRequires VarE:Gas: in a condition with a variable the left side binds (V ∈ LblcapGas(…)), under LblcapGas, of a sort the text leaves unconfined
rB: none
rB+owise: KCore.Parse.RefusalReason.openRequires VarE:Gas: in a condition with a variable the left side binds (V ∈ LblcapGas(…)), under LblcapGas, of a sort the text leaves unconfined, in a rule of a priority below another's
-/
#guard_msgs in
#eval details

end OvlHeldRefused
