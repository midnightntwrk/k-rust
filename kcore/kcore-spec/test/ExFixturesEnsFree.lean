/-
  The fixture e3-vars-ens-free (CN-4 §4.8, R2 fixture table, row 4), read from K 7.1.337 kompile's
  KORE: an existential variable in the `ensures` only. Run from the package root:
  `lake env lean -j1 test/ExFixturesEnsFree.lean`. Beside `test/ExFixtures.lean`.

  `c() => c() ensures ?Z ==Int 0`, kompiled (`test/constructs/fixtures/e3-vars-ens-free/kore.txt:81-89`,
  copied to `f2-examples/exensfree.kompile.kore`) as
  `\rewrites(\and(<generatedTop>(\and(<k>(c() ~> .), _Gen0), _DotVar0), \top),
    \exists(?Z:Int, \and(<generatedTop>(_Gen0, _DotVar0), \equals(?Z ==Int 0, true))))`.

  The reader refuses the text: `openRight`, Z bound by `\exists`, held under no constructor, Int
  unconfined (`verdict`). That is a limit of the reader, not what the sentence states. The sentence's
  right side does not hold Z: it is the left side's instance, and the binder is satisfied at the value
  `Z := 0`. So `<k> c() </k>` steps to itself and to nothing else (`step_iff`).

  `step_iff` is stated over the reader's own reading of the text before it checks the rules
  (`Parse.coreBase`; `baseOf`, `core_base_of`): the semantics `c` here is that reading, not one
  written by hand. `c.coreOK` is false (`facts`: `rulePlainEx` fails of the rule), so no statement
  over the models of `Γc c` is made of this text; `Step` does not read `coreOK`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore
open ML Faithful

namespace ExFixtures

/-- The reader's semantics of a text before its rules are checked (`Parse.coreBase`, the stage
after which `Parse.coreOf` refuses a rule), and the names of each rule's variables. -/
def baseOf (path : String) : IO (Except String (Semantics × List (List String))) := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return .error s!"KORE read error {e}"
  | .ok k =>
    let some m := k.modules.getLast? | return .error "no module"
    let S := Parse.scan m.sentences
    let r : Parse.Rd (Semantics × List (List String)) := do
      let E ← Parse.envOf m S
      let sp ← (Parse.prodSyms S E).mapM (Parse.symProd E S.eqs)
      let rules ← S.rewrites.mapM (Parse.ruleOf E.N E.src)
      let c ← Parse.coreBase S E (Parse.prodsOf S E sp) rules
      pure (c, rules.map (·.2.names))
    match r with
    | .ok x => return .ok x
    | .error f => return .error s!"{repr f.reason} {f.detail}"

open Lean Elab Command in
/-- `core_base_of NAME from "file.kore"`: `def NAME : Semantics`, `baseOf`'s semantics of the file
(a text without parameter symbols), checked by the kernel where it is used. -/
elab "core_base_of " id:ident " from " path:str : command => do
  match ← baseOf path.getString with
  | .error e => throwError "core_base_of: {path.getString}: {e}"
  | .ok (c, _) =>
    unless c.params.isEmpty do throwError "core_base_of: {path.getString}: the text has parameter symbols"
    let name := (← getCurrNamespace) ++ id.getId
    liftCoreM <| addDecl <| .defnDecl {
      name, levelParams := [], type := mkConst ``Semantics, value := semanticsExpr c,
      hints := .regular 0, safety := .safe }

namespace EnsFree

/-- The reader on the text: its refusal; and on its reading before the rules are checked, each
rule's `exs` with their names, `ruleSorted`, `rulePlainEx` and `openRefusal`'s reason. -/
def verdict : IO Unit := do
  let path := "f2-examples/exensfree.kompile.kore"
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => IO.println s!"KORE read error {e}"
  | .ok k => match Parse.parse k with
    | .error r => IO.println s!"parse: refused {r.reason.name} {r.detail}"
    | .ok _ => IO.println "parse: read"
  match ← baseOf path with
  | .error e => IO.println s!"base: {e}"
  | .ok (c, ns) =>
    for ((r, n), i) in (c.rules.zip ns).zipIdx do
      IO.println s!"base rule {i}: exs {r.exs} {r.exs.map fun j => n.getD j ""}; ruleSorted {c.ruleSorted r}; rulePlainEx {c.rulePlainEx r}; openRefusal {(Parse.openRefusal c r n).map (·.1.name)}"

/--
info: parse: refused openRight Var'Ques'Z:Int: bound by \exists on the right side, held there or in the ensures under no constructor, of a sort the text leaves unconfined: the successor is a value through an element that is no value's
base rule 0: exs [2] ['Ques'Z]; ruleSorted true; rulePlainEx false; openRefusal (some openRight)
-/
#guard_msgs in
#eval verdict

core_base_of c from "f2-examples/exensfree.kompile.kore"

def sKCell : Srt := 30
def sExp : Srt := 32
def kCell : Sym := 383
def symC : Sym := 385

theorem names_ok : c.sortName sKCell = "KCell" ∧ c.sortName sExp = "Exp" ∧
    c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName symC = "Lblc" := by
  decide +kernel

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

theorem r0_mem : r0 ∈ c.rules := List.getElem_mem _

/-- The text has the one rule. -/
theorem rules_one {r : Rule} (h : r ∈ c.rules) : r = r0 := by
  have hl : c.rules.length = 1 := by decide +kernel
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hl
  have h0 : r0 = a := by unfold r0; simp only [ha, List.getElem_cons_zero]
  rw [ha, List.mem_singleton] at h
  rw [h, h0]

/-- `Z ==Int 0`, Z the rule's variable 2. -/
def ensT : Term := .app intEq [.var 2, .dv Srt.int (.int 0)]

/-- The rule as the reader reads the sentence: `_Gen0` (variable 0) the k cell, bound by `#as` on
the left side; `_DotVar0` (variable 1) the counter cell; Z (variable 2) existential, in the
`ensures` only. -/
theorem r0_vars : r0.vars = [sKCell, Srt.counter, Srt.int] := by decide +kernel
theorem r0_lhs : r0.lhs = .app topLabel [.as (.app kCell [.app kseq [.inj sExp Srt.kitem (.app symC []),
    .app dotk []]]) 0, .var 1] := rfl
theorem r0_rhs : r0.rhs = .app topLabel [.var 0, .var 1] := rfl
theorem r0_shape : r0.req = none ∧ r0.ens = some ensT ∧ r0.pre = .top ∧ r0.post = .top ∧ r0.exs = [2] ∧
    r0.prio = 50 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- What refuses the rule: Z is held by no constructor of the right side (it is not held there at
all), so `rulePlainEx` fails and with it `coreOK`. The rule is sorted. -/
theorem facts : c.ruleSorted r0 = true ∧ c.rulePlainEx r0 = false ∧ (varOccs r0.rhs).contains 2 = false ∧
    c.coreOK = false := by
  decide +kernel

theorem syms_ok : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor symC = true ∧ c.isCtor dotk = true ∧ c.isCtor intEq = false := by
  decide +kernel

/-- `<k> c() ~> . </k>` and the counter cell at 0. -/
def kc : GroundTerm := .ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor symC []), .ctor dotk []]]
def cnt : GroundTerm := .ctor counterLabel [int 0]

/-- The configuration `<k> c() </k>`. -/
def X : Config c := ⟨.ctor topLabel [kc, cnt], by decide +kernel⟩

def σ0 : Subst := [(0, kc), (1, cnt), (2, int 0)]

theorem int2_at (x y : Int) (f : Int → Int → Option GroundTerm) : int2 [int x, int y] f = f x y := by
  simp [int2, asInt, int]

/-- **`<k> c() </k>` steps to itself by the rule**, at `Z := 0`. -/
theorem stepBy : StepBy c r0 σ0 X X where
  mem := r0_mem
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 2, hs => cases hs; exact ⟨_, rfl, sortOf_int 0⟩
  hmatch := by
    rw [r0_lhs]
    exact .ctor syms_ok.1 (.cons (.as (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons (.inj (.ctor syms_ok.2.2.2.1 .nil)) (.cons (.ctor syms_ok.2.2.2.2.1 .nil) .nil))) .nil)) rfl)
      (.cons (.var rfl) .nil))
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := by rw [r0_shape.2.2.1]; exact .top
  heval := by
    rw [r0_rhs]
    exact .ctor syms_ok.1 (.cons .var (.cons .var .nil))
  hens := fun t ht => by
    rw [r0_shape.2.1] at ht
    cases ht
    exact .hook syms_ok.2.2.2.2.2 rfl (.cons .var (.cons .dv .nil))
      (fun vs hvs => by
        cases hvs
        exact Semantics.hookRes_of_value (by
          show hook intEq [int 0, int 0] = _
          rw [Det.hook_intEq, int2_at]; rfl))
      (fun h => by cases h)
  hpost := by rw [r0_shape.2.2.2.1]; exact .top
  hprio := fun r' hr' hlt => by
    cases rules_one hr'
    exact absurd hlt (Nat.lt_irrefl _)

/-- **What the sentence states of `<k> c() </k>`: it steps to itself, and to nothing else.** The
right side is the left side's instance (`_Gen0` and `_DotVar0`, bound by the left side), whatever
the value of Z. -/
theorem step_iff (y : Config c) : Step c X y ↔ y = X := by
  constructor
  · intro h
    obtain ⟨r, σ, hb⟩ := step_iff_by.mp h
    cases rules_one hb.mem
    have hm := hb.hmatch
    rw [r0_lhs] at hm
    obtain ⟨-, vs, hvs, hps⟩ := PatVal.app_inv (by decide) hm syms_ok.1
    have hvs' : GroundTerm.ctor topLabel [kc, cnt] = .ctor topLabel vs := hvs
    cases hvs'
    obtain ⟨v1, vs1, hv1, hp1, hps1⟩ := hps.cons_inv
    cases hv1
    obtain ⟨v2, vs2, hv2, hp2, -⟩ := hps1.cons_inv
    cases hv2
    have h0 := hp1.as_inv.2
    have h1 := hp2.var_inv
    have he := hb.heval
    rw [r0_rhs] at he
    obtain ⟨rs, hts, hr⟩ := he.ctor_inv syms_ok.1
    obtain ⟨r1, rs1, rfl, he1, hts1⟩ := hts.cons_inv
    obtain ⟨r2, rs2, rfl, he2, hts2⟩ := hts1.cons_inv
    cases hts2.nil_inv
    rw [he1.var_inv, he2.var_inv, h0, h1] at hr
    exact Subtype.ext (Option.some.inj hr)
  · rintro rfl
    exact step_iff_by.mpr ⟨r0, σ0, stepBy⟩

/-- info: 'ExFixtures.EnsFree.step_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_iff

end EnsFree

end ExFixtures
