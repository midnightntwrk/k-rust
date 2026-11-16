/-
  `rulesPlain`'s arm for an open variable held by closed conditions: those conditions share no
  variable with the right side, the `ensures` or `post` (findings/R1-DECISION.md §2.3). Run from
  the package root: `lake env lean test/RulesPlainArmC.lean`.

  - The arm's three readings: `rulesPlainOld` (the variable under test not in the rest of the
    rule), the library's `rulesPlain` (no condition variable in the rest), `rulesPlainNarrow` (no
    condition variable under constructors of the right side). On rules over the semantics of
    `f2-examples/symrule.kompile.kore`: `bad1` (`a() => b(X) requires X ==Int 2 *Int H`) and `bad2`
    (`a() => a() requires B ==Bool (2 *Int H ==Int 1) ensures B`) leave a step open (at values no
    step, at a non-value Int element h with `2 *Int h = 1` one) and are refused by the library's
    text; `bad2` is admitted by the narrower one. `ok1` to `ok4` (the shapes of e2-unbound and
    e2-rule among them) are admitted by every reading.
  - `rulesPlainLand_eq`: where no rule leaves a variable open, the library's text accepts exactly
    what the text with the conjunct `r.opens.isEmpty` and the arm as first written (`rulesPlainA3`)
    accepts.
-/
import KcoreSpec.Statements

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- The arm as first written: the variable under test is in no right side, `ensures` or `post`. -/
def rulesPlainOld (c : Semantics) : Bool := c.rules.all fun r =>
  r.exs.isEmpty && r.pre.isTop && r.post.isTop &&
  (let conf := fun i => (r.vars[i]?.map c.confined).getD false
   r.opens.all (fun i => (ctorOccs c r.rhs).contains i || conf i ||
     (r.condVars.contains i && r.reqClosed &&
       !(varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post).contains i)) &&
   (!r.reqOpen || !c.rules.any (fun r' => r.prio < r'.prio) || r.openCondVars.all conf || r.reqClosed))

/-- A narrower candidate: only the condition variables the right side holds under constructors
are kept apart. -/
def rulesPlainNarrow (c : Semantics) : Bool := c.rules.all fun r =>
  r.exs.isEmpty && r.pre.isTop && r.post.isTop &&
  (let conf := fun i => (r.vars[i]?.map c.confined).getD false
   let rest := varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post
   r.opens.all (fun i => (ctorOccs c r.rhs).contains i || conf i ||
     (r.condVars.contains i && r.reqClosed && !rest.contains i &&
       r.condVars.all fun j => !(ctorOccs c r.rhs).contains j)) &&
   (!r.reqOpen || !c.rules.any (fun r' => r.prio < r'.prio) || r.openCondVars.all conf || r.reqClosed))

/-- The text with the conjunct `r.opens.isEmpty` and the arm as first written. -/
def rulesPlainA3 (c : Semantics) : Bool := c.rules.all fun r =>
  r.exs.isEmpty && r.pre.isTop && r.post.isTop && r.opens.isEmpty &&
  (let conf := fun i => (r.vars[i]?.map c.confined).getD false
   r.opens.all (fun i => (ctorOccs c r.rhs).contains i || conf i ||
     (r.condVars.contains i && r.reqClosed &&
       !(varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post).contains i)) &&
   (!r.reqOpen || !c.rules.any (fun r' => r.prio < r'.prio) || r.openCondVars.all conf || r.reqClosed))

/-- Where no rule leaves a variable open, the library's text and `rulesPlainA3` accept the same
semantics. -/
theorem rulesPlainLand_eq (c : Semantics) (h0 : ∀ r ∈ c.rules, r.opens = []) :
    c.rulesPlain = rulesPlainA3 c := by
  apply Bool.eq_iff_iff.mpr
  unfold rulesPlainA3 Semantics.rulesPlain
  simp only [List.all_eq_true]
  refine forall_congr' fun r => imp_congr_right fun hr => ?_
  simp [Rule.reqOpen, Rule.openCondVars, h0 r hr]

/-- info: 'rulesPlainLand_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rulesPlainLand_eq

def i (n : Int) : Term := .dv Srt.int (.int n)
/-- `<generatedTop>(<k>(kseq(inj{Exp,KItem}(b), V0)), cnt)`: the symbols and sorts of the text
(named in the output's first line). -/
def cfg (cnt : Term) : Term :=
  .app 71 [.app 379 [.app 0 [.inj 32 1 (.app 382 []), .var 0]], cnt]

def run : IO Unit := do
  match Kore.parseDefinition (← IO.FS.readFile "f2-examples/symrule.kompile.kore") with
  | .error e => IO.println s!"KORE read error {e}"
  | .ok k =>
    match Parse.parse k with
    | .error r => IO.println s!"refused {repr r.reason} {r.detail}"
    | .ok d =>
      let c := d.sem
      let vs0 := (c.rules.map (·.vars)).getD 0 []
      let sK := vs0.getD 1 0
      let sC := vs0.getD 2 0
      IO.println s!"names {c.symName 71} {c.symName 379} {c.symName 0} {c.symName 382} {c.symName 73} {c.sortName 32} {c.sortName 1}"
      let mk := fun (vars : List Srt) (rhs : Term) (req ens : Option Term) (prio : Nat) =>
        ({ vars := vars, lhs := cfg (.var 1), req := req, rhs := rhs, ens := ens, prio := prio } : Rule)
      -- a() => b(X) requires X ==Int 2 *Int H
      let bad1 := mk [sK, sC, Srt.int, Srt.int] (cfg (.app 73 [.var 2]))
        (some (.app intEq [.var 2, .app intMul [i 2, .var 3]])) none 50
      -- a() => a() requires B ==Bool (2 *Int H ==Int 1) ensures B
      let bad2 := mk [sK, sC, Srt.bool, Srt.int] (cfg (.var 1))
        (some (.app boolEq [.var 2, .app intEq [.app intMul [i 2, .var 3], i 1]])) (some (.var 2)) 50
      -- a() => b(X)
      let ok1 := mk [sK, sC, Srt.int] (cfg (.app 73 [.var 2])) none none 50
      -- a() => a() requires H ==Int 0
      let ok2 := mk [sK, sC, Srt.int] (cfg (.var 1)) (some (.app intEq [.var 2, i 0])) none 50
      -- a() => b(X) requires X ==Int 0
      let ok3 := mk [sK, sC, Srt.int] (cfg (.app 73 [.var 2])) (some (.app intEq [.var 2, i 0])) none 50
      -- a() => b(X) requires H ==Int 0
      let ok4 := mk [sK, sC, Srt.int, Srt.int] (cfg (.app 73 [.var 2])) (some (.app intEq [.var 3, i 0])) none 50
      let plain := mk [sK, sC] (cfg (.var 1)) none none 200
      let show1 := fun (n : String) (rs : List Rule) =>
        let c' := { c with rules := rs }
        IO.println s!"{n}: sorted {rs.all c'.ruleSorted} old {rulesPlainOld c'} new {c'.rulesPlain} narrow {rulesPlainNarrow c'} needsWitness {rs.map (·.needsWitness c')} opens {rs.map (·.opens)} condVars {rs.map (·.condVars)}"
      IO.println s!"sorts K {c.sortName sK} C {c.sortName sC} confBool {c.confined Srt.bool} confInt {c.confined Srt.int}"
      show1 "bad1" [bad1]
      show1 "bad2" [bad2]
      show1 "ok1" [ok1]
      show1 "ok2" [ok2]
      show1 "ok3" [ok3]
      show1 "ok4" [ok4]
      show1 "ok2+larger" [ok2, plain]
      show1 "bad1+larger" [bad1, plain]

/--
info: names Lbl'-LT-'generatedTop'-GT-' Lbl'-LT-'k'-GT-' kseq Lblb Lbl'-LT-'generatedCounter'-GT-' Exp KItem
sorts K K C GeneratedCounterCell confBool true confInt false
bad1: sorted true old true new false narrow false needsWitness [true] opens [[2, 3]] condVars [[2, 3]]
bad2: sorted true old true new false narrow true needsWitness [true] opens [[2, 3]] condVars [[2, 3]]
ok1: sorted true old true new true narrow true needsWitness [false] opens [[2]] condVars [[]]
ok2: sorted true old true new true narrow true needsWitness [true] opens [[2]] condVars [[2]]
ok3: sorted true old true new true narrow true needsWitness [true] opens [[2]] condVars [[2]]
ok4: sorted true old true new true narrow true needsWitness [true] opens [[2, 3]] condVars [[3]]
ok2+larger: sorted true old true new true narrow true needsWitness [true, false] opens [[2], []] condVars [[2], []]
bad1+larger: sorted true old true new false narrow false needsWitness [true, false] opens [[2, 3], []] condVars [[2, 3], []]
-/
#guard_msgs in
#eval run
