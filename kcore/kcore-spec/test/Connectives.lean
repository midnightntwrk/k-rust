/-
  Matching-logic connectives in rules and equations outside `[simplification]`, read from K 7.1.337
  kompile's KORE (the construct fixtures of designs/CN-2 section 5 Brief 2, unit e0). Run from the
  package root: `lake env lean test/Connectives.lean`.

  Each text is read with the note of its connective (`Parse.ReadingNote`), nothing refused or
  unaccounted, and the kernel shows the steps (the values) the laws of the note give:
  - `f2-examples/mlor` (fixture e7-guardors): `c(a() #Or b()) => a()`, one rule per disjunct
    (`orSplit`): `c(a)` and `c(b)` step to `a`, `c(c(a))` has no successor.
  - `f2-examples/mlex` (e3-ml-rule-lhs-exists): `c(#Exists Y. d(Y, b())) => a()`, Y a variable of
    the rule (`existsAsVariable`): `c(d(a, b))` steps to `a`, `c(a)` has no successor.
  - `f2-examples/mlbot` (e3-ml-rule-rhs-bottom): `go(_) => #Bottom` beside `go(_) => done` of
    priority 60, the first read with the `ensures` false (`bottomAsEnsures`): it applies at `go(1)`,
    gives no successor and blocks the second, so `go(1)` has no successor.
  - `f2-examples/mlandt` (e3-ml-rule-rhs-and-term): `go(X) => f(X) #And g(X)`, f the identity and
    g negation, read through the cut as `go(X) => ?Z` with `post := Z ∈ f(X) ∧ Z ∈ g(X)`
    (`andTermsCut`; the steps in test/PredFixtures.lean, `RhsAnd.MlAndT`).
  - `f2-examples/mlceil` (e3-ml-req-ceil): `go(X) => done requires #Ceil(1 /Int X)` beside
    `go(_) => other` of priority 60, the first `requires` read as `false` (`predicateAtBool`: a
    predicate at Bool is `\top` or `\bottom`, neither `true`): the first never applies, and `go(1)`
    steps to `other`.
  - `f2-examples/mleqand` (e3-ml-eq-rhs-and-pred): `f(X) => X #And {(X >Int 0) #Equals true}`, the
    clause `f(X) = X ensures X >Int 0` (`andAsEnsures`): `f(1) = 1`, `f(0)` has no value.
  - `f2-examples/mlandc` (e3-ml-rule-rhs-and-ctor): `c(X) => X #And a()`, read through the cut as
    `c(X) => X` with `post := X ∈ a()` (`andTermsCut`; the steps in test/PredFixtures.lean,
    `RhsAnd.MlAndC`).
  - `f2-examples/mleqbot` (e3-ml-eq-rhs-bottom): `f(X) => #Bottom requires X <Int 0` beside
    `f(X) => X [owise]`, the first the clause with the `ensures` false (`bottomAsEnsures`): `f(-1)`
    has no value (the `[owise]` clause does not apply), `f(2) = 2`.
  - `f2-examples/mleqorb` (e3-ml-eq-rhs-or-bottom): `f(X) => X #Or #Bottom` read as `f(X) = X`
    (`orBottom`): `f(3) = 3`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- The reader's verdict on the text at `path`: its user sentences read in another form than
written or inert by `vacuousLeft`, and the refusal or what the account finds. -/
def verdict (path : String) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let notes := (Parse.classCounts k).filter fun (n, _) =>
      ["read orSplit", "read topAsVariable", "read existsAsVariable", "read andAsEnsures",
       "read andTermsWeaker", "read andTermsCut", "read bottomAsEnsures", "read orBottom", "read predicateAtBool", "read andAtBool",
       "inert vacuousLeft"].contains n
    return s!"{notes}; " ++ match Parse.parse k with
      | .ok d => s!"read; unaccounted {(Parse.unconsumed k d).length}; uninduced {(Parse.uninduced k d).length}; coreOK {d.sem.coreOK}"
      | .error r => s!"{r.reason.name}{if r.detail.isEmpty then "" else " " ++ r.detail}"

/--
info: [(read orSplit, 1)]; read; unaccounted 0; uninduced 0; coreOK true
[(read existsAsVariable, 1)]; read; unaccounted 0; uninduced 0; coreOK true
[(read bottomAsEnsures, 1)]; read; unaccounted 0; uninduced 0; coreOK true
[(read andTermsCut, 1)]; read; unaccounted 0; uninduced 0; coreOK true
[(read predicateAtBool, 1)]; read; unaccounted 0; uninduced 0; coreOK true
[(read andAsEnsures, 1)]; read; unaccounted 0; uninduced 0; coreOK true
[(read andTermsCut, 1)]; read; unaccounted 0; uninduced 0; coreOK true
[(read bottomAsEnsures, 1)]; read; unaccounted 0; uninduced 0; coreOK true
[(read orBottom, 1)]; read; unaccounted 0; uninduced 0; coreOK true
-/
#guard_msgs in
#eval show IO Unit from do
  for f in ["mlor", "mlex", "mlbot", "mlandt", "mlceil", "mleqand", "mlandc", "mleqbot", "mleqorb"] do
    IO.println (← verdict s!"f2-examples/{f}.kompile.kore")

section
open KCore.Exec KCore.Cert

/-- No listed successor where a rule r₀ applies and every rule of priority at most r₀'s gives none
(test/EnsuresRule.lean's lemma). -/
theorem successorsN_nil_of_blocked {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true) (hco : CoherentAll c) {n : Nat} {x : GroundTerm} {r₀ : Rule}
    (hr₀ : r₀ ∈ c.rules)
    (happ : ((matchP c (patFuel [r₀.lhs]) [] r₀.lhs x).filter (wellSorted c r₀.vars)).any
      (fun σ => reqValC c n r₀ σ == some true) = true)
    (hst : c.rules.all (fun r => !decide (r.prio ≤ r₀.prio) || ruleStuck c n r x) = true)
    (m : Nat) : successorsN c m x = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro y hy
  obtain ⟨r, hr, hlow, σ, hσb, he, hs, hens⟩ := successorsN_mem_ens hy
  have hsc := sortCtx_of hok hsr (Exec.ovlCase_of hmr)
  have hcc := clauseCtx_of hok
  have hmc := matchCtx_of hmr
  have hagree : ∀ {r : Rule} {σ : Subst} {t : Term} {v w : Option GroundTerm} {s : Srt},
      c.WellSorted r.vars σ → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some s →
      evalT c n σ t = some v → evalT c m σ t = some w → v = w := fun hσw ht hv hw =>
    EvalTerm.functional hco (evalT_sound hsc hcc hmc n hv headsOK_fns hσw ht)
      (evalT_sound hsc hcc hmc m hw headsOK_fns hσw ht)
  by_cases hp : r₀.prio < r.prio
  · obtain ⟨σ₀, hσ₀, hb₀⟩ := List.any_eq_true.mp happ
    have hq := reqValC_sound (beq_iff_eq.mp hb₀)
    have hl := hlow r₀ hr₀ hp (σ₀, reqVal c m r₀ σ₀) (ruleMatches_mem.mpr ⟨hσ₀, rfl⟩)
    simp only at hl
    have hσw : c.WellSorted r₀.vars σ₀ := wellSorted_iff.mp (List.mem_filter.mp hσ₀).2
    obtain ⟨-, -, -, hrqOK, -⟩ := ruleOK_of hok hr₀
    unfold reqVal at hq hl
    cases hrq : r₀.req with
    | none => rw [hrq] at hl; cases hl
    | some t =>
      rw [hrq] at hq hl hrqOK
      simp only at hq hl
      cases hn : evalT c n σ₀ t with
      | none => rw [hn] at hq; cases hq
      | some v =>
        cases hm : evalT c m σ₀ t with
        | none => rw [hm] at hl; cases hl
        | some w =>
          rw [hn] at hq; rw [hm] at hl
          cases hagree hσw (reqOK_some hrqOK) hn hm
          simp only [Option.map_some, Option.some.injEq] at hq hl
          rw [hq] at hl; cases hl
  · have hrs : ruleStuck c n r x = true := by
      have := List.all_eq_true.mp hst r hr
      simpa [Nat.le_of_not_lt hp] using this
    obtain ⟨hσm, hb⟩ := ruleMatches_mem.mp hσb
    have h2 := ruleStuck_at (List.all_eq_true.mp hrs σ hσm)
    have hσw : c.WellSorted r.vars σ := wellSorted_iff.mp (List.mem_filter.mp hσm).2
    obtain ⟨-, -, -, hrqOK, hrtOK⟩ := ruleOK_of hok hr
    have hreq : reqVal c n r σ = some true ∨ reqVal c n r σ = none := by
      unfold reqVal at hb ⊢
      cases hrq : r.req with
      | none => left; rfl
      | some t =>
        rw [hrq] at hb
        cases hm : evalT c m σ t with
        | none => simp [hm] at hb
        | some w =>
          cases hn : evalT c n σ t with
          | none => right; simp only [hn, Option.map_none]
          | some v =>
            left
            rw [hrq] at hrqOK
            cases hagree hσw (reqOK_some hrqOK) hn hm
            simp only [hm, Option.map_some, Option.some.injEq] at hb
            simp [hn, hb]
    rcases h2 with h2 | ⟨h2, h3⟩
    · rcases hreq with hreq | hreq <;> rw [hreq] at h2 <;> cases h2
    · rcases h3 with h3 | ⟨y', h3, hs'⟩
      · cases hagree hσw hrtOK h3 he
      · cases hagree hσw hrtOK h3 he
        rcases hs' with hs' | hs'
        · exact hs' hs
        · exact ensVal_not_false_true hok hsr hmr hco hr hσw hs' hens

end

/-- The configuration with `it` in the k cell and the counter at 0. -/
def cfgOf (kCell : Sym) (it : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [it, .ctor dotk []]], .ctor counterLabel [.dv Srt.int (.int 0)]]

namespace MlOr

definition_of defn from "f2-examples/mlor.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
def a : Sym := 385
def b : Sym := 386
def cc : Sym := 387
def exp : Srt := 32
theorem names_ok : c.symName a = "Lbla" ∧ c.symName b = "Lblb" ∧ c.symName cc = "Lblc" ∧
    c.sortName exp = "Exp" := by decide +kernel
/-- One rule per disjunct, of one priority. -/
theorem two_rules : c.rules.map (·.prio) = [50, 50] := by decide +kernel
theorem ok : c.ok = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem matchReady : c.matchReady = true := by decide +kernel
theorem coherent : CoherentAll c :=
  Det.coherentAll_of_nil ok srReady matchReady (by decide +kernel) (by decide +kernel)
def cfg (e : GroundTerm) : GroundTerm := cfgOf 383 (.inj exp Srt.kitem e)
def CA : Config c := ⟨cfg (.ctor cc [.ctor a []]), by decide +kernel⟩
def CB : Config c := ⟨cfg (.ctor cc [.ctor b []]), by decide +kernel⟩
def CCA : Config c := ⟨cfg (.ctor cc [.ctor cc [.ctor a []]]), by decide +kernel⟩
def A : Config c := ⟨cfg (.ctor a []), by decide +kernel⟩
theorem step_ca : Step c CA A :=
  (Exec.step_iff_of_ok c ok srReady matchReady coherent _ _).mpr ⟨100, by decide +kernel⟩
theorem step_cb : Step c CB A :=
  (Exec.step_iff_of_ok c ok srReady matchReady coherent _ _).mpr ⟨100, by decide +kernel⟩
theorem stuck_cca : ∀ y, ¬ Step c CCA y := by
  intro y h
  obtain ⟨n, hn⟩ := (Exec.step_iff_of_ok c ok srReady matchReady coherent _ y).mp h
  rw [Cert.successorsN_nil_of_stuckCheck ok srReady matchReady coherent (n := 100) (by decide +kernel) n] at hn
  cases hn

end MlOr

namespace MlEx

definition_of defn from "f2-examples/mlex.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
def a : Sym := 385
def b : Sym := 386
def cc : Sym := 387
def d : Sym := 388
def exp : Srt := 32
theorem names_ok : c.symName a = "Lbla" ∧ c.symName b = "Lblb" ∧ c.symName cc = "Lblc" ∧
    c.symName d = "Lbld" ∧ c.sortName exp = "Exp" := by decide +kernel
theorem ok : c.ok = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem matchReady : c.matchReady = true := by decide +kernel
theorem coherent : CoherentAll c :=
  Det.coherentAll_of_nil ok srReady matchReady (by decide +kernel) (by decide +kernel)
def cfg (e : GroundTerm) : GroundTerm := cfgOf 383 (.inj exp Srt.kitem e)
def CD : Config c := ⟨cfg (.ctor cc [.ctor d [.ctor a [], .ctor b []]]), by decide +kernel⟩
def CA : Config c := ⟨cfg (.ctor cc [.ctor a []]), by decide +kernel⟩
def A : Config c := ⟨cfg (.ctor a []), by decide +kernel⟩
theorem step_cd : Step c CD A :=
  (Exec.step_iff_of_ok c ok srReady matchReady coherent _ _).mpr ⟨100, by decide +kernel⟩
theorem stuck_ca : ∀ y, ¬ Step c CA y := by
  intro y h
  obtain ⟨n, hn⟩ := (Exec.step_iff_of_ok c ok srReady matchReady coherent _ y).mp h
  rw [Cert.successorsN_nil_of_stuckCheck ok srReady matchReady coherent (n := 100) (by decide +kernel) n] at hn
  cases hn

end MlEx

namespace MlBot

definition_of defn from "f2-examples/mlbot.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
def go : Sym := 386
def exp : Srt := 32
theorem names_ok : c.symName go = "Lblgo" ∧ c.sortName exp = "Exp" := by decide +kernel
/-- The rule of `#Bottom` (priority 50) has the `ensures` false; the other has priority 60. -/
theorem rules_shape : c.rules.map (·.prio) = [50, 60] ∧
    c.rules.map (fun r => r.ens.map (Term.beq (.dv Srt.bool (.bool false)))) = [some true, none] := by
  decide +kernel
theorem ok : c.ok = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem matchReady : c.matchReady = true := by decide +kernel
theorem coherent : CoherentAll c :=
  Det.coherentAll_of_nil ok srReady matchReady (by decide +kernel) (by decide +kernel)
def cfg (e : GroundTerm) : GroundTerm := cfgOf 383 (.inj exp Srt.kitem e)
def Go1 : Config c := ⟨cfg (.ctor go [.dv Srt.int (.int 1)]), by decide +kernel⟩
/-- The first rule applies and gives no successor; it blocks the second. -/
theorem stuck_go1 : ∀ y, ¬ Step c Go1 y := by
  intro y h
  obtain ⟨n, hn⟩ := (Exec.step_iff_of_ok c ok srReady matchReady coherent _ y).mp h
  rw [successorsN_nil_of_blocked ok srReady matchReady coherent (n := 100) (r₀ := c.rules[0]'(by decide +kernel))
    (List.getElem_mem _) (by decide +kernel) (by decide +kernel) n] at hn
  cases hn

end MlBot

/-! `MlAndT` (mlandt): the rule is read through the cut (`andTermsCut`), `go(X) => ?Z` with
`post := Z ∈ f(X) ∧ Z ∈ g(X)`; its steps are test/PredFixtures.lean's (`RhsAnd.MlAndT`: `go(0)`
steps to `0` and to nothing else, `go(1)` has no successor), whose rule is this text's as parsed. -/

namespace MlCeil

definition_of defn from "f2-examples/mlceil.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
def go : Sym := 386
def other : Sym := 387
def exp : Srt := 32
theorem names_ok : c.symName go = "Lblgo" ∧ c.symName other = "Lblother" ∧ c.sortName exp = "Exp" := by
  decide +kernel
/-- The `requires` `#Ceil(1 /Int X)` is the literal `false`. -/
theorem req_false : c.rules.map (fun r => r.req.map (Term.beq (.dv Srt.bool (.bool false)))) = [some true, none] := by
  decide +kernel
theorem ok : c.ok = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem matchReady : c.matchReady = true := by decide +kernel
theorem coherent : CoherentAll c :=
  Det.coherentAll_of_nil ok srReady matchReady (by decide +kernel) (by decide +kernel)
def cfg (e : GroundTerm) : GroundTerm := cfgOf 383 (.inj exp Srt.kitem e)
def Go1 : Config c := ⟨cfg (.ctor go [.dv Srt.int (.int 1)]), by decide +kernel⟩
def Other : Config c := ⟨cfg (.ctor other []), by decide +kernel⟩
/-- The first rule never applies; the rule of priority 60 steps. -/
theorem step_go1 : Step c Go1 Other :=
  (Exec.step_iff_of_ok c ok srReady matchReady coherent _ _).mpr ⟨100, by decide +kernel⟩

end MlCeil

namespace MlEqAnd

definition_of defn from "f2-examples/mleqand.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
def f : Sym := 384
theorem names_ok : c.symName f = "Lblf" := by decide +kernel
noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)
theorem fn_label : fn.label = f := by decide +kernel
/-- The clause `f(X) = X ensures X >Int 0`. -/
theorem clause_shape : fn.clauses.map (fun cl => (cl.ens.map (Term.beq (.app intGt [.var 0, .dv Srt.int (.int 0)])),
    Term.beq cl.rhs (.var 0))) = [(some true, true)] := by decide +kernel
private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn f = some fn := rfl

theorem eval_of_evalFC {vs : List GroundTerm} (hvs : c.sortsOf vs = some fn.args) {n : Nat}
    {r : Option GroundTerm} (h : Cert.evalFC c n f vs = some r) : Eval c f vs r :=
  Exec.evalF_sound (sortCtx_of hok hsr (Exec.ovlCase_of hmr)) (Exec.clauseCtx_of hok)
    (Exec.matchCtx_of hmr) n (Cert.evalFC_sound n h) hfn hvs

theorem f_1 : Eval c f [.dv Srt.int (.int 1)] (some (.dv Srt.int (.int 1))) :=
  eval_of_evalFC (by decide +kernel) (n := 10) (by decide +kernel)
theorem f_0 : Eval c f [.dv Srt.int (.int 0)] none :=
  eval_of_evalFC (by decide +kernel) (n := 10) (by decide +kernel)

end MlEqAnd

/-! `MlAndC` (mlandc): the rule is read through the cut (`andTermsCut`), `c(X) => X` with
`post := X ∈ a()`; its steps are test/PredFixtures.lean's (`RhsAnd.MlAndC`: `c(a)` steps to `a`,
`c(b)` has no successor), whose rule is this text's as parsed. -/

namespace MlEqBot

definition_of defn from "f2-examples/mleqbot.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
def f : Sym := 384
theorem names_ok : c.symName f = "Lblf" := by decide +kernel
noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)
theorem fn_label : fn.label = f := by decide +kernel
private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn f = some fn := rfl

theorem eval_of_evalFC {vs : List GroundTerm} (hvs : c.sortsOf vs = some fn.args) {n : Nat}
    {r : Option GroundTerm} (h : Cert.evalFC c n f vs = some r) : Eval c f vs r :=
  Exec.evalF_sound (sortCtx_of hok hsr (Exec.ovlCase_of hmr)) (Exec.clauseCtx_of hok)
    (Exec.matchCtx_of hmr) n (Cert.evalFC_sound n h) hfn hvs

/-- `f(X) => #Bottom requires X <Int 0` applies at `-1` and gives no value; the `[owise]` clause
does not apply there (no fall-through). -/
theorem f_neg1 : Eval c f [.dv Srt.int (.int (-1))] none :=
  eval_of_evalFC (by decide +kernel) (n := 10) (by decide +kernel)
theorem f_2 : Eval c f [.dv Srt.int (.int 2)] (some (.dv Srt.int (.int 2))) :=
  eval_of_evalFC (by decide +kernel) (n := 10) (by decide +kernel)

end MlEqBot

namespace MlEqOrB

definition_of defn from "f2-examples/mleqorb.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
def f : Sym := 384
theorem names_ok : c.symName f = "Lblf" := by decide +kernel
noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)
theorem fn_label : fn.label = f := by decide +kernel
private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn f = some fn := rfl

/-- `f(X) => X #Or #Bottom` is `f(X) = X` (`orBottom`). -/
theorem f_3 : Eval c f [.dv Srt.int (.int 3)] (some (.dv Srt.int (.int 3))) :=
  Exec.evalF_sound (sortCtx_of hok hsr (Exec.ovlCase_of hmr)) (Exec.clauseCtx_of hok)
    (Exec.matchCtx_of hmr) 10 (Cert.evalFC_sound 10 (by decide +kernel)) hfn (by decide +kernel)

end MlEqOrB

/-! ## Conjunctions with a variable, empty right sides, several notes, and the refused shapes

- `f2-examples/mlandv` (e3-ml-rule-rhs-and-var): `c(X) => a() #And X`, read through the cut as
  `c(X) => X` with `post := X ∈ a()` (`andTermsCut`; a right side binds nothing, so `a() ∧ X` is no
  `#as`): the steps in test/PredFixtures.lean (`RhsAnd.MlAndV`).
- `f2-examples/mlreqv` (e3-ml-req-and-var): `go(B) => done requires true #And B`, read conjunct by
  conjunct, the `requires` `true` and the conjunct `B = true` of `pre` (`andAtBool`): `go(true)`
  steps to `done`, `go(false)` has none (the executable step, which evaluates `pre`).
- `f2-examples/mlbotf` (e3-ml-rule-rhs-bottom-fn): `go(X) => pair(f(X), #Bottom)`, f partial: the
  right side read in the empty one's place is the left side (`bottomAsEnsures`), which applies no
  function.
- `f2-examples/mleqbotc` (e3-ml-eq-rhs-bottom-ctor): `f(X) => #Bottom requires X <Int 0` beside
  `f(X) => a() [owise]` at the sort Exp: the clause's right side is the constructor value `a()`, not
  the call `f(X)`; `f(-1)` has no value, `f(1) = a`.
- `f2-examples/mleqbotn` (e3-ml-eq-rhs-bottom-noval): the same at a sort whose one constructor takes a
  String: no value the reader names, the right side is the call `f(X)` at the clause's arguments;
  read, `coreOK` (natively).
- `f2-examples/mlorand` (e3-ml-rule-lhs-or-rhs-and): `c(X) #Or d(X) => X #And a()`, read through
  `orSplit` and `andTermsCut`, both listed (`Parse.connReadings`): the steps in
  test/PredFixtures.lean (`RhsAnd.MlOrAnd`).
- `f2-examples/mlempty` (e3-ml-lhs-empty-sort): `c(#Exists Y:Empty. a()) => b()` and
  `e(_:Empty) #Or d() => b()`, Empty without a value: each axiom holds for every element of Empty,
  so it states nothing where Empty has none, and a rule without the variable would step at `c(a)`
  and `d`; read through `existsAsVariable` and `orSplit`, then refused `unheldVariable`, the
  reader exhibiting no value of Empty (`Parse.exhibit?`).
- `f2-examples/mlmixed` (e3-ml-lhs-mixed-sort): `e(_:Val) #Or f(_:Empty) => b()`: the rule of the
  first disjunct does not hold the variable of Empty; refused whole, `unheldVariable`.
- `f2-examples/mlrequnheld` (e3-ml-req-or-unheld): `go(X) => done requires X >Int 0 #Or Y >Int 2`:
  the rule of the first disjunct does not hold Y, of Int (a value: read without it); the rule of the
  second holds Y in its `requires` alone, a closed condition no variable of which the rest of the
  rule holds: read, its `CondDecided` owed.
- `f2-examples/mleqor` (e3-ml-eq-rhs-or): `h(X) => f(X) #Or g(X)`, refused `manyValuedRightSide`.
- `f2-examples/mlsetv` (e3-setvar-read): `w(@S) => @S`, refused `setVariable`.
- `f2-examples/mlallexp` (e3-ml-rule-lhs-forall-exp): `c(#Forall Y:Exp. Y) => a()`, refused
  `openExtent` at Exp.
-/

/-- The reader's verdict on the text at `path`: every connective note of each sentence read through
one (`Parse.connReadings`), the sentences `classify` refuses by class, and the first refusal or what
the account finds. -/
def verdictAll (path : String) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let notes := (Parse.connReadings k).map fun (_, ns) => ns.map Parse.ReadingNote.name
    let refused := (Parse.classCounts k).filter fun (n, _) => n.startsWith "refused"
    return s!"{notes}; {refused}; " ++ match Parse.parse k with
      | .ok d => s!"read; unaccounted {(Parse.unconsumed k d).length}; uninduced {(Parse.uninduced k d).length}; coreOK {d.sem.coreOK}"
      | .error r => s!"{r.reason.name}{if r.detail.isEmpty then "" else " " ++ r.detail}"

/--
info: mlandv: [[andTermsCut]]; []; read; unaccounted 0; uninduced 0; coreOK true
mlreqv: [[andAtBool]]; []; read; unaccounted 0; uninduced 0; coreOK true
mlbotf: [[bottomAsEnsures]]; []; read; unaccounted 0; uninduced 0; coreOK true
mleqbotc: [[bottomAsEnsures]]; []; read; unaccounted 0; uninduced 0; coreOK true
mleqbotn: [[bottomAsEnsures]]; []; read; unaccounted 0; uninduced 0; coreOK true
mlorand: [[orSplit, andTermsCut]]; []; read; unaccounted 0; uninduced 0; coreOK true
mlempty: [[orSplit], [existsAsVariable]]; []; unheldVariable Var'Unds'Gen0:Empty: a variable of the axiom that a rule read from it does not hold, of a sort of which the reader exhibits no value: the axiom holds for every element of the sort, so where the sort has none it states nothing while the rule would step, and Γ entails neither an element of the sort nor its emptiness (the text's sorted theory gives every sort an element, which Γ does not state)
mlmixed: [[orSplit]]; []; unheldVariable Var'Unds'Gen1:Empty: a variable of the axiom that a rule read from it does not hold, of a sort of which the reader exhibits no value: the axiom holds for every element of the sort, so where the sort has none it states nothing while the rule would step, and Γ entails neither an element of the sort nor its emptiness (the text's sorted theory gives every sort an element, which Γ does not state)
mlrequnheld: [[requiresOrSplit]]; []; read; unaccounted 0; uninduced 0; coreOK true
mlvalue: [[orSplit], [orSplit], [existsAsVariable]]; []; read; unaccounted 0; uninduced 0; coreOK true
mlreqor: [[requiresOrSplit]]; []; read; unaccounted 0; uninduced 0; coreOK true
mleqor: []; []; manyValuedRightSide \or: the sentence gives the function every element of each side; the text holds no functional sentence of the function, so where the sides differ that is more than one element, which no clause states
mlsetv: []; []; setVariable VarS: in the right side, the requires, the ensures or an exclusion: the sentence states the function's value at every set holding the arguments; with the set as the value it has no model at a sort with two elements, otherwise its truth reads every subset of the sort
mlallexp: []; []; openExtent Exp
-/
#guard_msgs in
#eval show IO Unit from do
  for f in ["mlandv", "mlreqv", "mlbotf", "mleqbotc", "mleqbotn", "mlorand", "mlempty", "mlmixed",
      "mlrequnheld", "mlvalue", "mlreqor", "mleqor", "mlsetv", "mlallexp"] do
    IO.println s!"{f}: {← verdictAll s!"f2-examples/{f}.kompile.kore"}"

/-! `MlAndV` (mlandv): read through the cut (`andTermsCut`), `c(X) => X` with `post := X ∈ a()`;
its steps are test/PredFixtures.lean's (`RhsAnd.MlAndV`). -/

namespace MlReqV

definition_of defn from "f2-examples/mlreqv.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
def done : Sym := 385
def go : Sym := 386
def exp : Srt := 32
theorem names_ok : c.symName done = "Lbldone" ∧ c.symName go = "Lblgo" ∧ c.sortName exp = "Exp" := by
  decide +kernel
/-- The rule is read with the `requires` `true` and the conjunct `B = true` of `pre`. -/
theorem rule_shape : c.rules.map (fun r => (r.req.map (Term.beq (.dv Srt.bool (.bool true))),
    Cond.isTop r.pre, Cond.isTop r.post)) = [(some true, false, true)] := by decide +kernel
theorem ready : CExec.execReady c = true := by decide +kernel
theorem noFns : c.fns = [] := by decide +kernel
theorem fnDet : FnDet c :=
  Faithful.fnDet_of_agree (fun _ h => by rw [noFns] at h; cases h) (fun _ h => by rw [noFns] at h; cases h)
def cfg (e : GroundTerm) : GroundTerm := cfgOf 383 (.inj exp Srt.kitem e)
def GoT : Config c := ⟨cfg (.ctor go [.dv Srt.bool (.bool true)]), by decide +kernel⟩
def GoF : Config c := ⟨cfg (.ctor go [.dv Srt.bool (.bool false)]), by decide +kernel⟩
def Done : Config c := ⟨cfg (.ctor done []), by decide +kernel⟩
/-- `requires true #And B`: at `true` the step. -/
theorem step_got : Step c GoT Done := by
  obtain ⟨_, h⟩ := CExec.successorsN_step_ready ready (x := GoT) (n := 100) (y := Done.val) (by decide +kernel)
  exact h
/-- At `false` none. -/
theorem stuck_gof : ∀ y, ¬ Step c GoF y :=
  CExec.noStep_at ready fnDet (n := 100) (by decide +kernel) (by decide +kernel)

end MlReqV

namespace MlBotF

definition_of defn from "f2-examples/mlbotf.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
/-- The one rule's right side is its left side (no `#as` in it) and its `ensures` false: the read
right side applies no function, `f` among them. -/
theorem rule_shape : c.rules.map (fun r => (Term.beq r.rhs r.lhs,
    r.ens.map (Term.beq (.dv Srt.bool (.bool false))))) = [(true, some true)] := by decide +kernel
theorem ok : c.ok = true := by decide +kernel

end MlBotF

namespace MlEqBotC

definition_of defn from "f2-examples/mleqbotc.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
def a : Sym := 385
def f : Sym := 387
theorem names_ok : c.symName a = "Lbla" ∧ c.symName f = "Lblf" := by decide +kernel
noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)
theorem fn_label : fn.label = f := by decide +kernel
/-- Both clauses' right sides are `a()`: the empty one's placeholder is the constructor value, not
the call `f(X)`; its `ensures` is false. -/
theorem clause_shape : fn.clauses.map (fun cl => (Term.beq cl.rhs (.app a []),
    cl.ens.map (Term.beq (.dv Srt.bool (.bool false))))) = [(true, some true), (true, none)] := by
  decide +kernel
private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn f = some fn := rfl

theorem eval_of_evalFC {vs : List GroundTerm} (hvs : c.sortsOf vs = some fn.args) {n : Nat}
    {r : Option GroundTerm} (h : Cert.evalFC c n f vs = some r) : Eval c f vs r :=
  Exec.evalF_sound (sortCtx_of hok hsr (Exec.ovlCase_of hmr)) (Exec.clauseCtx_of hok)
    (Exec.matchCtx_of hmr) n (Cert.evalFC_sound n h) hfn hvs

theorem f_neg1 : Eval c f [.dv Srt.int (.int (-1))] none :=
  eval_of_evalFC (by decide +kernel) (n := 10) (by decide +kernel)
theorem f_1 : Eval c f [.dv Srt.int (.int 1)] (some (.ctor a [])) :=
  eval_of_evalFC (by decide +kernel) (n := 10) (by decide +kernel)

end MlEqBotC

namespace MlEqBotN

definition_of defn from "f2-examples/mleqbotn.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
def f : Sym := 386
theorem names_ok : c.symName f = "Lblf" := by decide +kernel
noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)
theorem fn_label : fn.label = f := by decide +kernel
/-- No value of Exp the reader names: the empty right side's placeholder is the call `f(X)` at the
clause's argument. -/
theorem clause_shape : fn.clauses.map (fun cl => Term.beq cl.rhs (.app f [.var 0])) = [true, false] := by
  decide +kernel

end MlEqBotN

/-! `MlOrAnd` (mlorand): two rules (`orSplit`), each read through the cut (`andTermsCut`); their
steps are test/PredFixtures.lean's (`RhsAnd.MlOrAnd`: `c(a)` and `d(a)` step to `a`, `c(b)` has no
successor). -/

/-! ## Rules read without a variable of the axiom, at a sort with a value

- `f2-examples/mlvalue` (e3-ml-lhs-value-sort): `c(#Exists Y:Val. a()) => b()`,
  `e(_:Val) #Or d() => b()` and `p(_:Int) #Or q(_:Int) => b()`, Val with the value `v()`: each rule
  read without the variable its disjunct does not hold (`existsAsVariable`, `orSplit`), since `Γ`
  entails an element of Val and of Int (`Faithful.inhabited_of_exhibit`): `c(a)`, `d`, `p(1)` and
  `q(1)` step to `b`.
- `f2-examples/mlreqor` (e3-ml-req-or-undef): `go(X) => done requires X >=Int 0 #Or 10 /Int X >Int 0`,
  two rules (`requiresOrSplit`): at `go(0)` the first disjunct is `true` and the second has no
  value, and the rule with the first steps; `go(-1)` has no successor (both disjuncts `false`).
-/

namespace MlValue

definition_of defn from "f2-examples/mlvalue.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
def kc : Sym := 384
def a : Sym := 386
def b : Sym := 387
def cc : Sym := 388
def d : Sym := 389
def p : Sym := 391
def q : Sym := 392
def v : Sym := 393
def exp : Srt := 33
def val : Srt := 32
theorem names_ok : c.symName kc = "Lbl'-LT-'k'-GT-'" ∧ c.symName a = "Lbla" ∧ c.symName b = "Lblb" ∧
    c.symName cc = "Lblc" ∧ c.symName d = "Lbld" ∧ c.symName p = "Lblp" ∧ c.symName q = "Lblq" ∧
    c.symName v = "Lblv" ∧ c.sortName exp = "Exp" ∧ c.sortName val = "Val" := by decide +kernel
/-- The value the reader exhibits of Val. -/
theorem exhibit_val : Parse.exhibit? c val = some (.ctor v []) := by decide +kernel
/-- Five rules of one priority: two for each disjunction, one for the `\exists`. -/
theorem five_rules : c.rules.map (·.prio) = [50, 50, 50, 50, 50] := by decide +kernel
theorem ok : c.ok = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem matchReady : c.matchReady = true := by decide +kernel
theorem coherent : CoherentAll c :=
  Det.coherentAll_of_nil ok srReady matchReady (by decide +kernel) (by decide +kernel)
def cfg (e : GroundTerm) : GroundTerm := cfgOf kc (.inj exp Srt.kitem e)
def CA : Config c := ⟨cfg (.ctor cc [.ctor a []]), by decide +kernel⟩
def D : Config c := ⟨cfg (.ctor d []), by decide +kernel⟩
def P1 : Config c := ⟨cfg (.ctor p [.dv Srt.int (.int 1)]), by decide +kernel⟩
def Q1 : Config c := ⟨cfg (.ctor q [.dv Srt.int (.int 1)]), by decide +kernel⟩
def B : Config c := ⟨cfg (.ctor b []), by decide +kernel⟩
theorem step_ca : Step c CA B :=
  (Exec.step_iff_of_ok c ok srReady matchReady coherent _ _).mpr ⟨100, by decide +kernel⟩
theorem step_d : Step c D B :=
  (Exec.step_iff_of_ok c ok srReady matchReady coherent _ _).mpr ⟨100, by decide +kernel⟩
theorem step_p1 : Step c P1 B :=
  (Exec.step_iff_of_ok c ok srReady matchReady coherent _ _).mpr ⟨100, by decide +kernel⟩
theorem step_q1 : Step c Q1 B :=
  (Exec.step_iff_of_ok c ok srReady matchReady coherent _ _).mpr ⟨100, by decide +kernel⟩

end MlValue

namespace MlReqOr

definition_of defn from "f2-examples/mlreqor.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
def kc : Sym := 383
def go : Sym := 386
def done : Sym := 385
def exp : Srt := 32
theorem names_ok : c.symName kc = "Lbl'-LT-'k'-GT-'" ∧ c.symName go = "Lblgo" ∧
    c.symName done = "Lbldone" ∧ c.sortName exp = "Exp" := by decide +kernel
/-- Two rules of one priority, each with a `requires`. -/
theorem two_rules : c.rules.map (fun r => (r.prio, r.req.isSome)) = [(50, true), (50, true)] := by
  decide +kernel
theorem ok : c.ok = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem matchReady : c.matchReady = true := by decide +kernel
theorem coherent : CoherentAll c :=
  Det.coherentAll_of_nil ok srReady matchReady (by decide +kernel) (by decide +kernel)
def goCfg (i : Int) : GroundTerm := cfgOf kc (.inj exp Srt.kitem (.ctor go [.dv Srt.int (.int i)]))
def Go0 : Config c := ⟨goCfg 0, by decide +kernel⟩
def GoM1 : Config c := ⟨goCfg (-1), by decide +kernel⟩
def Done : Config c := ⟨cfgOf kc (.inj exp Srt.kitem (.ctor done [])), by decide +kernel⟩
/-- `0 >=Int 0` is `true` and `10 /Int 0` has no value: the rule with the first disjunct steps. -/
theorem step_go0 : Step c Go0 Done :=
  (Exec.step_iff_of_ok c ok srReady matchReady coherent _ _).mpr ⟨100, by decide +kernel⟩
theorem stuck_gom1 : ∀ y, ¬ Step c GoM1 y := by
  intro y h
  obtain ⟨n, hn⟩ := (Exec.step_iff_of_ok c ok srReady matchReady coherent _ y).mp h
  rw [Cert.successorsN_nil_of_stuckCheck ok srReady matchReady coherent (n := 100) (by decide +kernel) n] at hn
  cases hn

end MlReqOr
