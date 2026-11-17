/-
  A function equation over a set variable beside an `[owise]` equation, read from K 7.1.337
  kompile's own KORE. Run from the package root: `lake env lean test/SetVarOwise.lean`.
  - `f2-examples/svowise.kompile.kore` (`svowise.k`, the text of fixture e3-setvar-owise):
    `f(@S, @S) => one()` beside `f(_, _) => two() [owise]`. The first is read with its two
    memberships dropped (`setVarInDropped`); the `[owise]` exclusion's disjunct for it holds one
    element variable at both arguments, so the `[owise]` equation is read with a premise narrower
    than the text's (`owiseDisjunctNarrower`, listed by `owiseNarrowed`). In the kernel: `f` is
    `one` at every pair of values of `Exp` (its four constructors), equal or not, and never `two`.
  - the same text with that disjunct written with two distinct bound variables: read, and no
    `[owise]` equation is listed under the note;
  - the same text with the disjunct's second argument a constructor, the bound variable at the
    first only: refused (`exclusionShape`);
  - `f2-examples/mlsetv.kompile.kore` (e3-setvar-read, `w(@S) => @S`): refused `setVariable`;
  - `f2-examples/svnonlinear.kompile.kore` (e3-setvar-nonlinear, `f(@S, @S) => r()` alone): in
    the kernel, `f` is `r` at every pair of values of `Exp` (its three constructors).

  Evidence, not a reason: K 7.1.337's `krun` (Haskell backend 0.1.155) on the fixture's text gives
  `<k> two ( ) ~> .K </k>` for `f(a(), b())`, a difference from the reading here (`one`, which the
  first sentence states at every pair; the text states both off the diagonal, `owiseDisjunctNarrower`),
  and for `f(a(), a())` prints the unevaluated initializer `initGeneratedTopCell ( $PGM |-> f ( a
  ( ) , a ( ) ) )`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- The `[owise]` equation of `Lblf`, its exclusion's one disjunct edited by `ed`. -/
def editDisjuncts (ed : Kore.Pattern → Kore.Pattern) (k : Kore.Definition) : Kore.Definition :=
  let edit : Kore.Pattern → Kore.Pattern
    | .implies s (.and s' [.not s'' (.or s₁ [d, b]), rest]) c@(.equals _ _ (.app f [] _) _) =>
      if f.ident.name == "Lblf" then .implies s (.and s' [.not s'' (.or s₁ [ed d, b]), rest]) c
      else .implies s (.and s' [.not s'' (.or s₁ [d, b]), rest]) c
    | p => p
  let sent := fun (s : Kore.Sentence) => match s with
    | .axiom a => .axiom { a with pattern := edit a.pattern }
    | s => s
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.map sent }]).getD [] }

/-- `∃G. ⌈r⌉ ∧ X₀ ∈ G ∧ X₁ ∈ p ∧ …` with `p` made `q G` (`G` the binder). -/
def secondArg (q : Kore.EVar → Kore.Pattern) (two : Bool) : Kore.Pattern → Kore.Pattern
  | .exist s g (.and s' [r, .and s₀ [m₀, .and s₁ [.in a b x₁ _, rest]]]) =>
    let g' : Kore.EVar := ⟨⟨⟨g.var.ident.name ++ "x"⟩⟩, g.sort⟩
    let body := fun (h : Kore.EVar) => Kore.Pattern.and s' [r, .and s₀ [m₀, .and s₁ [.in a b x₁ (q h), rest]]]
    if two then .exist s g (.exist s g' (body g')) else .exist s g (body g)
  | p => p

/-- The reader's verdict on the text at `path` (edited by `edit`): "read" with the `[owise]`
equations listed under `owiseDisjunctNarrower`, or its refusal. -/
def verdict (path : String) (edit : Kore.Definition → Kore.Definition := id) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let k := edit k
    return match Parse.parse k with
    | .ok d => s!"read; narrowed {(Parse.owiseNarrowed k d).map fun (i, f, j) => (i, f, j)}; \
        unaccounted {(Parse.unconsumed k d).length}; coreOK {d.sem.coreOK}"
    | .error r => r.reason.name

/--
info: read; narrowed [(216, (Lblf, 215))]; unaccounted 0; coreOK true
read; narrowed []; unaccounted 0; coreOK true
exclusionShape
setVariable
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/svowise.kompile.kore")
  IO.println (← verdict "f2-examples/svowise.kompile.kore"
    (editDisjuncts (secondArg (fun h => .var (.evar h)) true)))
  IO.println (← verdict "f2-examples/svowise.kompile.kore"
    (editDisjuncts (secondArg (fun _ => .app ⟨⟨"Lbla"⟩⟩ [] []) false)))
  IO.println (← verdict "f2-examples/mlsetv.kompile.kore")

namespace SvOwise

definition_of defn from "f2-examples/svowise.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- `f`, the definition's function, and the four constructors of `Exp`. -/
def f : Sym := 389
def ca : GroundTerm := .ctor 385 []
def cb : GroundTerm := .ctor 386 []
def one : GroundTerm := .ctor 387 []
def two : GroundTerm := .ctor 388 []

theorem names : c.symName f = "Lblf" ∧ c.symName 385 = "Lbla" ∧ c.symName 386 = "Lblb" ∧
    c.symName 387 = "Lblone" ∧ c.symName 388 = "Lbltwo" := by decide +kernel

private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn f = some (c.fns[0]'(by decide +kernel)) := rfl

theorem core_ok : c.coreOK = true := by decide_cheap

/-- `f`'s clauses: the equation read with its memberships dropped, then the `[owise]` one. -/
theorem f_prios : (c.fns[0]'(by decide +kernel)).clauses.map (·.prio) = [50, 200] := by
  decide +kernel

theorem coherent : CoherentAll c :=
  Det.coherentAll_of_nil hok hsr hmr (by decide +kernel) (by decide +kernel)

/-- The values of `Exp`. -/
def vals : List GroundTerm := [ca, cb, one, two]

/-- `f` is `one` at every pair of values of `Exp`, the two equal or not. -/
theorem f_one : ∀ x ∈ vals, ∀ y ∈ vals, Eval c f [x, y] (some one) := by
  intro x hx y hy
  simp only [vals, List.mem_cons, List.mem_nil_iff, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
  exact Exec.evalF_sound (sortCtx_of hok hsr (Exec.ovlCase_of hmr)) (Exec.clauseCtx_of hok)
    (Exec.matchCtx_of hmr) 10 (by decide +kernel) hfn (by decide +kernel)

/-- `f(a, b) = one` (the arguments differ) and `f(a, a) = one`. -/
theorem f_a_b : Eval c f [ca, cb] (some one) := f_one _ (by decide) _ (by decide)
theorem f_a_a : Eval c f [ca, ca] (some one) := f_one _ (by decide) _ (by decide)

/-- `f` is never `two` at a pair of values of `Exp`. -/
theorem f_not_two : ∀ x ∈ vals, ∀ y ∈ vals, ¬ Eval c f [x, y] (some two) := fun x hx y hy h =>
  nomatch Eval.functional coherent h (f_one x hx y hy)

end SvOwise

#print axioms SvOwise.f_one
#print axioms SvOwise.f_not_two
#print axioms SvOwise.core_ok

namespace SvNonlinear

/-! `f2-examples/svnonlinear.kompile.kore` (`svnonlinear.k`, the text of fixture
e3-setvar-nonlinear): `f(@S, @S) => r()` alone, read with its memberships dropped. -/

definition_of defn from "f2-examples/svnonlinear.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- `f`, the definition's function, and the three constructors of `Exp`. -/
def f : Sym := 388
def ca : GroundTerm := .ctor 385 []
def cb : GroundTerm := .ctor 386 []
def r : GroundTerm := .ctor 387 []

theorem names : c.symName f = "Lblf" ∧ c.symName 385 = "Lbla" ∧ c.symName 386 = "Lblb" ∧
    c.symName 387 = "Lblr" := by decide +kernel

private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn f = some (c.fns[0]'(by decide +kernel)) := rfl

theorem core_ok : c.coreOK = true := by decide_cheap

/-- The values of `Exp`. -/
def vals : List GroundTerm := [ca, cb, r]

/-- `f` is `r` at every pair of values of `Exp`, the two equal or not. -/
theorem f_r : ∀ x ∈ vals, ∀ y ∈ vals, Eval c f [x, y] (some r) := by
  intro x hx y hy
  simp only [vals, List.mem_cons, List.mem_nil_iff, or_false] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
  exact Exec.evalF_sound (sortCtx_of hok hsr (Exec.ovlCase_of hmr)) (Exec.clauseCtx_of hok)
    (Exec.matchCtx_of hmr) 10 (by decide +kernel) hfn (by decide +kernel)

/-- `f(a, b) = r` (the arguments differ) and `f(a, a) = r`. -/
theorem f_a_b : Eval c f [ca, cb] (some r) := f_r _ (by decide) _ (by decide)
theorem f_a_a : Eval c f [ca, ca] (some r) := f_r _ (by decide) _ (by decide)

end SvNonlinear

#print axioms SvNonlinear.f_r
#print axioms SvNonlinear.core_ok
