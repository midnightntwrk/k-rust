/-
  A function equation with an `ensures`, read from K 7.1.337 kompile's own KORE. Run from the
  package root: `lake env lean test/Ensures.lean`.
  - `f2-examples/ens.kompile.kore` (`ens.k`): `half(N) => N /Int 2 ensures N >=Int 0` is `half`'s
    only equation. The text says `half(N) = N /Int 2 ∧ (N >=Int 0 = true)`: the value N /Int 2 where
    N >=Int 0, no value where not (`r ∧ ⊥` is empty). It is read as written, with no note: the clause
    `half(N) = N /Int 2` with the `ensures` `N >=Int 0` (`Clause.ens`). For every interpretation H
    of the points the text leaves open: `half(4)` is 2, and `half(-4)` has no value (the clause
    decides there and its `ensures` is false, `Eval.ensFails`; the rest is not read).
  - `f2-examples/ens-owise.kompile.kore` (`ens-owise.k`): the same equation beside
    `half(_) => 0 [owise]`. The text's `[owise]` premise negates `∃ N. X0 ∈ N`, the first
    equation's argument and `requires` (true), not its `ensures`: the `[owise]` equation holds at no
    integer. So `half(-4)` has no value here too, for every H, and `half(4)` is 2.
  - `Ens.half_item_is_text`: `Γ`'s item for `half`'s equation is the translation of the text's
    sentence, right side `\and{SortInt{}}(N /Int 2, \equals{SortBool{},SortInt{}}(N >=Int 0, true))`.
  - `f2-examples/ensparam.kompile.kore` (`ensparam.k`): a library parameter symbol, `randInt`,
    applied only in an equation's `ensures`, is one of the semantics' parameters (`EnsParam`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- The reader's verdict on the text at `path`: "read", or its refusal; and the classes of the user
module's sentences that are read in another form than written. -/
def verdict (path : String) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let notes := (Parse.classCounts k).filter fun (n, _) => n.startsWith "read "
    return match Parse.parse k with
      | .ok _ => s!"read {notes}"
      | .error r => s!"{r.reason.name} {notes}"

/--
info: read []
read []
read []
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/ens.kompile.kore")
  IO.println (← verdict "f2-examples/ens-owise.kompile.kore")
  IO.println (← verdict "f2-examples/ensparam.kompile.kore")



/-- `evalFC` reads no interpretation where no parameter is raw. -/
theorem evalFC_withHooks (c : Semantics) (H : HookParams) (hr : ∀ k ∈ c.params, k.raw = false) (n : Nat) (f : Sym)
    (vs : List GroundTerm) : Cert.evalFC (c.withHooks H) n f vs = Cert.evalFC c n f vs :=
  Cert.evalFC_withHooks c H hr n f vs
kernel_rfl clausesFixed_withHooks : ∀ (c : Semantics) (H : HookParams),
  (c.withHooks H).clausesFixed = c.clausesFixed

/-- A function's result that `evalFC` computes on the data is its result under every interpretation:
`evalFC` reads no interpretation. -/
theorem eval_everyH {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (hr : ∀ k ∈ c.params, k.raw = false)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {vs : List GroundTerm} (hvs : c.sortsOf vs = some fn.args)
    {n : Nat} {r : Option GroundTerm} (h : Cert.evalFC c n f vs = some r) (H : HookParams) :
    Eval (c.withHooks H) f vs r := by
  have hok' := (Semantics.ok_withHooks c H).trans hok
  have hsr' := (Semantics.srReady_withHooks c H).trans hsr
  have hmr' := (Semantics.matchReady_withHooks c H).trans hmr
  have hF : Exec.evalF (c.withHooks H) n f vs = some r :=
    Cert.evalFC_sound n (by rw [evalFC_withHooks _ _ hr]; exact h)
  exact Exec.evalF_sound (sortCtx_of hok' hsr' (Exec.ovlCase_of hmr')) (Exec.clauseCtx_of hok') (Exec.matchCtx_of hmr') n
    hF (by rw [Semantics.lookupFn_withHooks]; exact hfn) (by rw [Semantics.sortsOf_withHooks c H hr]; exact hvs)

/-- Coherence under every interpretation, from the deciders on the data. -/
theorem coherent_everyH {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (hcf : c.clausesFixed = true) (hag : c.agreeObligations = []) (H : HookParams) : CoherentAll (c.withHooks H) :=
  Det.coherentAll_of_nil ((Semantics.ok_withHooks c H).trans hok) ((Semantics.srReady_withHooks c H).trans hsr)
    ((Semantics.matchReady_withHooks c H).trans hmr) ((clausesFixed_withHooks c H).trans hcf)
    ((Semantics.agreeObligations_withHooks c H).trans hag)

namespace Ens

definition_of defn from "f2-examples/ens.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- `half`, the definition's function. -/
def half : Sym := 387

theorem half_named : c.symName half = "Lblhalf" := by decide +kernel

private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn half = some (c.fns[0]'(by decide +kernel)) := rfl

/-- `half`'s one clause: the pattern `N`, no `requires`, the right side `N /Int 2`, the `ensures`
`N >=Int 0`. -/
theorem half_clause : (c.fns[0]'(by decide +kernel)).clauses =
    [⟨[Srt.int], [.var 0], none, .app intTDiv [.var 0, .dv Srt.int (.int 2)],
      some (.app intGe [.var 0, .dv Srt.int (.int 0)]), 50, false, [], .top, .top⟩] := rfl

theorem coherent (H : HookParams) : CoherentAll (c.withHooks H) :=
  coherent_everyH hok hsr hmr (by decide +kernel) (by decide +kernel) H

/-- Where the `ensures` holds, `half` has the right side's value, under every interpretation:
`half(4) = 2`. -/
theorem half_4 (H : HookParams) : Eval (c.withHooks H) half [int 4] (some (int 2)) :=
  eval_everyH hok hsr hmr noRaw hfn (by decide +kernel) (n := 10) (by decide +kernel) H

/-- Where it fails, `half` has no value, under every interpretation: `half(-4)` is undefined. -/
theorem half_neg4_none (H : HookParams) : Eval (c.withHooks H) half [int (-4)] none :=
  eval_everyH hok hsr hmr noRaw hfn (by decide +kernel) (n := 10) (by decide +kernel) H

theorem half_neg4 (H : HookParams) : ¬ ∃ r, Eval (c.withHooks H) half [int (-4)] (some r) := fun ⟨_, h⟩ =>
  nomatch Eval.functional (coherent H) h (half_neg4_none H)

open KoreAML (srt ev ap R Rv) in
/-- `half`'s equation as `ens.kompile.kore` writes it (the axiom after the comment
`// rule half(N)=>…ensures…`), attributes left out: `\implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortInt{},
R}(X0:SortInt{}, VarN:SortInt{}), \top{R}())), \equals{SortInt{},R}(Lblhalf{}(X0:SortInt{}),
\and{SortInt{}}(Lbl'UndsSlsh'Int'Unds'{}(VarN:SortInt{}, \dv{SortInt{}}("2")),
\equals{SortBool{},SortInt{}}(Lbl'Unds-GT-Eqls'Int'Unds'{}(VarN:SortInt{}, \dv{SortInt{}}("0")),
\dv{SortBool{}}("true")))))`. `text_half_is_texts` checks it against the parsed file. -/
def textHalf : Kore.Axiom :=
  { sortVars := [Rv]
    pattern := .implies R
      (.and R [.top R, .and R [.in (srt "Int") R (ev "X0" (srt "Int")) (ev "VarN" (srt "Int")), .top R]])
      (.equals (srt "Int") R (ap "Lblhalf" [ev "X0" (srt "Int")])
        (.and (srt "Int") [ap "Lbl'UndsSlsh'Int'Unds'" [ev "VarN" (srt "Int"), .dv (srt "Int") "2"],
          .equals (srt "Bool") (srt "Int")
            (ap "Lbl'Unds-GT-Eqls'Int'Unds'" [ev "VarN" (srt "Int"), .dv (srt "Int") "0"])
            (.dv (srt "Bool") "true")]))
    attributes := [] }

/-- `Γ`'s item for `half`'s equation (the first of `fnItems`, `half` being the first function and
having one clause) is the translation of the text's sentence, not only a sentence it entails: the
right side is `\and{SortInt{}}(N /Int 2, \equals{SortBool{},SortInt{}}(N >=Int 0, true))`, as written. -/
theorem half_item_is_text : (Faithful.fnItems c)[0]?.map (·.pat) =
    some (KoreAML.trAxiom [] [] ⟨0, "kernel", textHalf⟩).pat := by decide +kernel

end Ens

-- `Ens.textHalf` is the text's axiom: a sentence of `ens.kompile.kore` has its sort variables and
-- pattern, and its translation with the text's declarations is the same item pattern.
/--
info: true
-/
#guard_msgs in
#eval show IO Unit from do
  match Kore.parseDefinition (← IO.FS.readFile "f2-examples/ens.kompile.kore") with
  | .error e => IO.println s!"KORE read error {e}"
  | .ok k =>
    IO.println (k.axiomDecls.any fun ad =>
      decide (ad.ax.sortVars = Ens.textHalf.sortVars) && decide (ad.ax.pattern = Ens.textHalf.pattern) &&
      decide ((KoreAML.trAxiom k.symbolDecls k.aliasNames ad).pat = (KoreAML.trAxiom [] [] ⟨0, "kernel", Ens.textHalf⟩).pat))

-- `f2-examples/ensparam.kompile.kore` (`ensparam.k`): `f(X) => X ensures randInt(X) >=Int 0`, where
-- `randInt` (INT's `INT.rand`, no hook of the registry) is applied only in the `ensures`: the text's
-- equation is `\equals{SortInt{},R}(Lblf{}(X0), \and{SortInt{}}(VarX, \equals{SortBool{},SortInt{}}(
-- Lbl'Unds-GT-Eqls'Int'Unds'{}(LblrandInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int{}(VarX),
-- \dv{SortInt{}}("0")), \dv{SortBool{}}("true"))))`. `randInt` is one of the semantics' parameter
-- symbols, so the clause is well sorted and `coreOK` holds.
namespace EnsParam

definition_of defn from "f2-examples/ensparam.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem randInt_param :
    c.params.map (fun k => c.symName k.sig.name) = ["LblrandInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int"] := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

end EnsParam

namespace EnsOwise

definition_of defn from "f2-examples/ens-owise.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

def half : Sym := 387

theorem half_named : c.symName half = "Lblhalf" := by decide +kernel

private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn half = some (c.fns[0]'(by decide +kernel)) := rfl

/-- `half`'s clauses: the equation with its `ensures` (priority 50), and the `[owise]` one
(priority 200). -/
theorem half_clauses : ((c.fns[0]'(by decide +kernel)).clauses.map fun cl => (cl.ens.isSome, cl.prio)) =
    [(true, 50), (false, 200)] := by decide +kernel

theorem coherent (H : HookParams) : CoherentAll (c.withHooks H) :=
  coherent_everyH hok hsr hmr (by decide +kernel) (by decide +kernel) H

theorem half_4 (H : HookParams) : Eval (c.withHooks H) half [int 4] (some (int 2)) :=
  eval_everyH hok hsr hmr noRaw hfn (by decide +kernel) (n := 10) (by decide +kernel) H

/-- The equation with the `ensures` decides at `-4` and blocks the `[owise]` one; its `ensures` is
false, so `half(-4)` has no value, under every interpretation. -/
theorem half_neg4_none (H : HookParams) : Eval (c.withHooks H) half [int (-4)] none :=
  eval_everyH hok hsr hmr noRaw hfn (by decide +kernel) (n := 10) (by decide +kernel) H

theorem half_neg4 (H : HookParams) : ¬ ∃ r, Eval (c.withHooks H) half [int (-4)] (some r) := fun ⟨_, h⟩ =>
  nomatch Eval.functional (coherent H) h (half_neg4_none H)

end EnsOwise

#print axioms Ens.half_4
#print axioms Ens.half_neg4
#print axioms Ens.half_item_is_text
#print axioms EnsParam.coreOK
#print axioms EnsOwise.half_4
#print axioms EnsOwise.half_neg4
