/-
  Generated functions a rule applies, read as functions with the text's equations, not as parameter
  symbols. Run from the package root: `lake env lean test/GenFns.lean`.
  - `f2-examples/kappend.kompile.kore` (`kappend.k`): `<k> run(K1, K2) => K1 ~> K2 </k>`, which
    kompile writes with `append(K1, K2)`, K's `append`, whose equations the text states in the
    prelude's module KSEQ: `append(dotk, T) = T`, `append(kseq(K, KS), T) = kseq(K, append(KS, T))`.
    `append` is a function with those two clauses (`Parse.appendEqns`), no parameter symbol; for
    every interpretation H and every value t of sort K, `append(.K, t)` is t. Its clauses cover
    K × K (`covers` splits K over `dotk` and `kseq`), and the totality decider accepts it.
  - `f2-examples/kappend-init.kompile.kore`: the same text with the rule's right side holding
    `initGeneratedCounterCell()` for the counter cell's variable (an edit of the text, so that a rule
    applies an initializer of the top cell tree, which no K source can write). The initializer is a
    function with the text's equation `initGeneratedCounterCell() = <generatedCounter>(0)`; for every
    H its value is `<generatedCounter>(0)`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- The functions and the parameter symbols of the text at `path` by name, and the functions whose
production and equations `emit` leaves to the prelude or the cells. -/
def summary (path : String) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k => return match Parse.parse k with
    | .ok d =>
      let c := d.sem
      s!"fns {c.fns.map fun f => (c.symName f.label, f.clauses.length)}, params {c.params.map (c.symName ·.sig.name)}, generated {d.pres.generatedFns.map c.symName}, wf {wf d}"
    | .error r => s!"refused {r.toText}"

/--
info: fns [(append, 2)], params [], generated [append], wf true
fns [(append, 2), (LblinitGeneratedCounterCell, 1)], params [], generated [append, LblinitGeneratedCounterCell], wf true
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← summary "f2-examples/kappend.kompile.kore")
  IO.println (← summary "f2-examples/kappend-init.kompile.kore")

kernel_rfl isCtor_withHooks : ∀ (c : Semantics) (H : HookParams), (c.withHooks H).isCtor = c.isCtor

namespace KAppend

definition_of defn from "f2-examples/kappend.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

def appendS : Sym := 387

theorem append_named : c.symName appendS = "append" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

theorem fn_label : fn.label = appendS := by decide +kernel

/-- The prelude's equations, its clauses: `append(dotk, T) = T` and `append(kseq(K, KS), T) =
kseq(K, append(KS, T))`, priority 50. -/
def cl1 : Clause := ⟨[Srt.k], [.app dotk [], .var 0], none, .var 0, none, 50, false, [], .top, .top⟩
def cl2 : Clause := ⟨[Srt.kitem, Srt.k, Srt.k], [.app kseq [.var 0, .var 1], .var 2], none,
  .app kseq [.var 0, .app appendS [.var 1, .var 2]], none, 50, false, [], .top, .top⟩

theorem fn_clauses : fn.clauses = [cl1, cl2] := rfl

private theorem hfn : c.lookupFn appendS = some fn := rfl

theorem dotk_ctor : c.isCtor dotk = true := by decide +kernel

/-- **For every H, `append(.K, t) = t`**, t any value of sort K: the prelude's first equation. -/
theorem append_dotk (H : HookParams) (t : GroundTerm) (ht : c.sortOf t = some Srt.k) :
    Eval (c.withHooks H) appendS [.ctor dotk [], t] (some t) := by
  have hfnH : (c.withHooks H).lookupFn appendS = some fn := by
    rw [Semantics.lookupFn_withHooks]; exact hfn
  have hd := dotk_ctor
  rw [← isCtor_withHooks c H] at hd
  refine Eval.clause (cl := cl1) (σ := [(0, t)]) hfnH (by rw [fn_clauses]; simp) ?_ ?_
    (fun t ht => nomatch ht) .top ?_ rfl .var (fun t ht => nomatch ht) .top
  · intro i s hs
    cases i with
    | zero => cases hs; exact ⟨t, rfl, by rw [Semantics.sortOf_withHooks _ _ noRaw]; exact ht⟩
    | succ i => simp [cl1] at hs
  · exact .cons (.ctor hd .nil) (.cons (.var rfl) .nil)
  · intro cl' hcl' _ hlt
    rw [fn_clauses] at hcl'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl'
    rcases hcl' with rfl | rfl <;> exact absurd hlt (by decide)

theorem not_param : (c.params.any (·.sig.name == appendS)) = false := by decide +kernel

/-- The clauses' patterns cover K × K: K is enumerable, and `covers` splits the first argument over
K's generators, `dotk` and `kseq`. -/
theorem k_enumerable : c.enumerable Srt.k = true := by decide +kernel

theorem append_covers : c.covers (Semantics.coverFuel fn) fn.args (Semantics.coverRows fn) = true := by
  decide +kernel

/-- **`append` is total by the decider** (`totalOKG`, sound by `totals_of_rankP`). -/
theorem append_totalOKG : c.totalOKG [] fn = true := by decide +kernel

end KAppend

namespace KAppendInit

definition_of defn from "f2-examples/kappend-init.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

def initCtr : Sym := 388

theorem init_named : c.symName initCtr = "LblinitGeneratedCounterCell" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[1]'(by decide +kernel)

theorem fn_label : fn.label = initCtr := by decide +kernel

/-- The text's equation `initGeneratedCounterCell() = <generatedCounter>(0)`, its one clause. -/
def cl : Clause := ⟨[], [], none, .app counterLabel [.dv Srt.int (.int 0)], none, 50, false, [], .top, .top⟩

theorem fn_clauses : fn.clauses = [cl] := rfl

private theorem hfn : c.lookupFn initCtr = some fn := rfl

theorem counter_ctor : c.isCtor counterLabel = true := by decide +kernel

/-- **For every H, `initGeneratedCounterCell() = <generatedCounter>(0)`**: the text's equation. -/
theorem init_value (H : HookParams) :
    Eval (c.withHooks H) initCtr [] (some (.ctor counterLabel [.dv Srt.int (.int 0)])) := by
  have hfnH : (c.withHooks H).lookupFn initCtr = some fn := by
    rw [Semantics.lookupFn_withHooks]; exact hfn
  have hk := counter_ctor
  rw [← isCtor_withHooks c H] at hk
  refine Eval.clause (cl := cl) (σ := []) hfnH (by rw [fn_clauses]; simp)
    (fun i s hs => by simp [cl] at hs) .nil (fun t ht => nomatch ht) .top ?_ rfl ?_ (fun t ht => nomatch ht) .top
  · intro cl' hcl' _ hlt
    rw [fn_clauses] at hcl'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl'
    subst hcl'; exact absurd hlt (by decide)
  · exact .ctor hk (.cons .dv .nil)

end KAppendInit

#print axioms KAppend.append_dotk
#print axioms KAppend.not_param
#print axioms KAppend.append_covers
#print axioms KAppend.append_totalOKG
#print axioms KAppendInit.init_value
