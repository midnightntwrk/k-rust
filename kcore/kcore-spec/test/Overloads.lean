/-
  Overloading symbols read from K 7.1.337 kompile's KORE. Run from the package root:
  `lake env lean test/Overloads.lean`.
  - `f2-examples/ovlsub.kompile.kore` (`ovlsub.k`, as the corpus's gas3): `capGas : Gas → Gas`,
    declared `anywhere`, overloads the constructor `capN : N → N`, `N < Gas`; the text states
    `capGas(inj{N,Gas}(K)) = inj{N,Gas}(capN(K))`. Read: `capGas` an overloading symbol over `capN`
    (`Semantics.ovls`), numbered last, the overload axiom accounted for, its constructor axioms
    (injectivity, Gas's no-junk axiom with `capGas` among the generators) induced; `coreOK`.
  - `f2-examples/ovllist.kompile.kore` (`ovllist.k`, wasm's list sorts): the conses and nils of
    Instrs, Defns and Stmts, six overloading symbols over EmptyStmts' constructors and over each
    other, ten overload axioms; read, numbered so that each comes after those it overloads,
    nothing unaccounted or not induced, no function in a left side, `coreOK`.
  - `f2-examples/ovlconf.kompile.kore` (`ovlconf.k`, as the corpus's overload-constructors): an
    overload keeping the result sort and one keeping the argument sort; read; the text's
    distinctness of `asMedium` and `asSmall`, which the overload contradicts, is not read
    (`overloadConfusion`).
  - `f2-examples/ovlfun.kompile.kore` (`ovlfun.k`): `capGas` overloads the function `capN`: read,
    with the function among `capGas`'s overloads (`Parse.overloadFunctions`,
    `ReadingNote.overloadFunction`), and `coreOK`, whose `overloadsOK` admits an overload by a
    function.
    Edited texts of ovlsub: an argument of the
    overload axiom that is no injected variable, a right side without its injection, and the
    overload axiom dropped (then `capGas` is a function without clauses, applied in a left side).
  - In the kernel, on ovlsub: the overloading symbol's data, `coreOK`; `capGas(inj{N,Gas}(z))`
    denotes `inj{N,Gas}(capN(z))` (`norm`), a raw `capGas(inf)` is a value of Gas and a raw
    `capGas(inj{N,Gas}(z))` none; the rule `run(cap(G)) => done(G)` steps from
    `run(inj{N,Gas}(capN(z)))` to `done(inj{N,Gas}(z))` (its left side's `capGas(G)` denotes the
    configuration's argument through the overload, `PatVal.ovl`) and from `run(capGas(inf))` to
    `done(inf)`; the rule `wrap(G) => done(cap(G))` steps from `wrap(inj{N,Gas}(z))` to
    `done(inj{N,Gas}(capN(z)))` (`EvalTerm.ovl`). The steps are built from `Step.rule`, the left
    side and right side read symbol by symbol with `norm` for an overloading symbol (`instO`).
  - The executable step (`CExec`, CollExec.lean), which reads overloading symbols (a pattern
    `f(p̄)` matched at `ovlArgs`, `norm` in evaluation): `execReady` holds of ovlsub, ovllist and
    ovlconf; in the kernel, the three steps above are listed by `CExec.successorsN` and so are
    `Step`s by `successorsN_step_ready` (`exec_run`, `exec_raw`, `exec_wrap`); natively, from the
    configurations `test/collexec/ovlsub-*.kore` (with `capGas` applied in the input, read through
    `norm`), the same three successors and no other, and on ovllist (`len(_S:Stmt SS:Stmts, N)`
    over a list of two `nop`s built with the Stmts cons, which `norm` makes an Instrs list) the run
    `len(nop nop, count(nop nop))` to `done(4)` (`count` evaluated through its clauses `count(_S SS)`
    and `count(.Stmts)`, both overloading patterns).
  - The `FnHyp` deciders on ovllist in the kernel: `count`'s two clauses agree (their heads'
    overload closures meet nowhere) and are match independent; its totality is named (`named`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- The reader's verdict on the text at `path` (its text edited by `edit`): the overloading symbols
with the symbols each overloads, the sentences unaccounted, the inert constructor axioms not
induced, the distinctness axioms an overload contradicts, the functions in left sides, `coreOK`; or
the refusal. -/
def verdict (path : String) (edit : String → String := id) (names : Bool := true) : IO String := do
  match Kore.parseDefinition (edit (← IO.FS.readFile path)) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    return match Parse.parse k with
      | .ok d =>
        let c := d.sem
        let ovls := if names then s!"{c.ovls.map fun o => (c.symName o.sig.name, o.over.map c.symName)}"
          else s!"{c.ovls.length} over {(c.ovls.map (·.over.length)).sum}"
        s!"read; ovls {ovls}; unaccounted {(Parse.unconsumed k d).length}; not induced {(Parse.uninduced k d).length}; confusions {(Parse.overloadConfusions k d).map (·.2)}; functionInPattern {((Parse.functionInPattern k d).map (·.detail)).eraseDups}; coreOK {c.coreOK}"
      | .error r => s!"{r.reason.name} ({r.detail})"

/-- Each overloading symbol of `ovllist` comes after those it overloads; their numbers are the last
of the definition's own, and the definition's own symbols are numbered as `idsOK` asks. -/
def order (path : String) : IO String := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile path) | return "KORE read error"
  let .ok d := Parse.parse k | return "refused"
  let c := d.sem
  -- a list symbol as `nil X` or `cons X`, X its result sort
  let short := fun (f : Sym) =>
    let kind := if (c.symName f).startsWith "Lbl'Stop'List" then "nil" else "cons"
    match lookupSig (c.ctorSigs ++ c.ovlSigs) f with
    | some k => s!"{f} {kind} {c.sortName k.result}"
    | none => s!"{f}"
  return s!"{c.ovls.map fun o => (short o.sig.name, o.over.map short)}; last {c.symNames.length + nRegSyms - 1}; idsOK {c.idsOK}"

/-- info: read; ovls [(LblcapGas, [LblcapN])]; unaccounted 0; not induced 0; confusions []; functionInPattern []; coreOK true -/
#guard_msgs in
#eval show IO Unit from do IO.println (← verdict "f2-examples/ovlsub.kompile.kore")

/-- info: read; ovls 6 over 10; unaccounted 0; not induced 0; confusions []; functionInPattern []; coreOK true -/
#guard_msgs in
#eval show IO Unit from do IO.println (← verdict "f2-examples/ovllist.kompile.kore" (names := false))

/-- info: [(400 nil Defns, [393 nil EmptyStmts]), (401 nil Instrs, [393 nil EmptyStmts]), (402 cons Defns, [394 cons EmptyStmts]), (403 cons Instrs, [394 cons EmptyStmts]), (404 nil Stmts, [400 nil Defns, 393 nil EmptyStmts, 401 nil Instrs]), (405 cons Stmts, [403 cons Instrs, 394 cons EmptyStmts, 402 cons Defns])]; last 405; idsOK true -/
#guard_msgs in
#eval show IO Unit from do IO.println (← order "f2-examples/ovllist.kompile.kore")

/-- info: read; ovls [(LblasMedium, [LblasSmall]), (LblfromMedium, [LblfromSmall]), (Lblwide, [Lblnarrow]), (Lblwidest, [Lblwide, Lblnarrow])]; unaccounted 0; not induced 0; confusions [LblasMedium]; functionInPattern []; coreOK true -/
#guard_msgs in
#eval show IO Unit from do IO.println (← verdict "f2-examples/ovlconf.kompile.kore")

/-- info: read; ovls [(LblcapGas, [LblcapN])]; unaccounted 0; not induced 0; confusions []; functionInPattern []; coreOK true -/
#guard_msgs in
#eval show IO Unit from do IO.println (← verdict "f2-examples/ovlfun.kompile.kore")

/-- The overloading symbols that overload a function, each with those functions
(`ReadingNote.overloadFunction`), and whether `overloadsOK` holds. -/
def fnOverloads (path : String) : IO String := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile path) | return "KORE read error"
  let .ok d := Parse.parse k | return "refused"
  return s!"overloadFunction {Parse.overloadFunctions d}; overloadsOK {d.sem.overloadsOK}"

/-- info: overloadFunction [(LblcapGas, [LblcapN])]; overloadsOK true -/
#guard_msgs in
#eval show IO Unit from do IO.println (← fnOverloads "f2-examples/ovlfun.kompile.kore")

/-- info: overloadFunction []; overloadsOK true -/
#guard_msgs in
#eval show IO Unit from do IO.println (← fnOverloads "f2-examples/ovlsub.kompile.kore")

/-- The overload axiom of ovlsub, its left side's argument and its right side. -/
def ovlLhsArg : String := "LblcapGas{}(inj{SortN{}, SortGas{}} (K0:SortN{}))"
def ovlRhs : String := "inj{SortN{}, SortGas{}} (LblcapN{}(K0:SortN{})))"

/-- info: overloadForm (an argument other than a variable of the overloaded symbol's argument sort (injected where the argument sorts differ)) -/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/ovlsub.kompile.kore" fun s =>
    s.replace ovlLhsArg "LblcapGas{}(inj{SortN{}, SortGas{}} (LblcapN{}(K0:SortN{})))")

/-- info: overloadForm (a right side other than an application of LblcapN (injected where the result sorts differ)) -/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/ovlsub.kompile.kore" fun s => s.replace ovlRhs "LblcapN{}(K0:SortN{}))")

/-- info: read; ovls []; unaccounted 0; not induced 3; confusions []; functionInPattern [LblcapGas]; coreOK false -/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/ovlsub.kompile.kore" fun s =>
    "\n".intercalate ((s.splitOn "\n").filter fun l => !(l.splitOn "symbol-overload").length > 1))

/-! ## A left side and a right side read symbol by symbol, overloading symbols by `norm` -/

namespace OvlStep

mutual
  /-- A term read symbol by symbol: a constructor builds its term, an overloading symbol its normal
  form (`norm`); `none` at a hook, a collection's symbol, a function or an alias. -/
  def instO (c : Semantics) (σ : Subst) : Term → Option GroundTerm
    | .var i => σ.lookup i
    | .dv s lit => some (.dv s lit)
    | .app f ps => (instOs c σ ps).bind fun vs =>
        if c.isCtor f then some (.ctor f vs) else if c.isOvl f then some (c.norm f vs) else none
    | .inj a b p => (instO c σ p).map (injNormal a b)
    | .as _ _ => none
  def instOs (c : Semantics) (σ : Subst) : List Term → Option (List GroundTerm)
    | [] => some []
    | p :: ps => (instO c σ p).bind fun v => (instOs c σ ps).map (v :: ·)
end

mutual
  /-- What `instO` reads off a pattern is a value the pattern denotes. -/
  theorem patVal_of_instO (c : Semantics) (σ : Subst) :
      ∀ (p : Term) {v : GroundTerm}, instO c σ p = some v → PatVal c σ p v
    | .var _, _, h => .var h
    | .dv _ _, _, h => by cases h; exact .dv
    | .app f ps, v, h => by
      simp only [instO] at h
      obtain ⟨vs, hvs, h⟩ := Option.bind_eq_some_iff.mp h
      have hs := patVals_of_instO c σ ps hvs
      by_cases hc : c.isCtor f = true
      · rw [if_pos hc] at h; cases h; exact .ctor hc hs
      · rw [if_neg hc] at h
        by_cases ho : c.isOvl f = true
        · rw [if_pos ho] at h; cases h; exact .ovl (by simpa using hc) ho hs rfl
        · rw [if_neg ho] at h; cases h
    | .inj _ _ p, _, h => by
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .inj (patVal_of_instO c σ p hw)
    | .as _ _, _, h => by simp [instO] at h
  theorem patVals_of_instO (c : Semantics) (σ : Subst) :
      ∀ (ps : List Term) {vs : List GroundTerm}, instOs c σ ps = some vs → PatVals c σ ps vs
    | [], _, h => by cases h; exact .nil
    | p :: ps, _, h => by
      simp only [instOs] at h
      obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vs', hvs', rfl⟩ := Option.map_eq_some_iff.mp h
      exact .cons (patVal_of_instO c σ p hv) (patVals_of_instO c σ ps hvs')
end

theorem allSome_map_some : ∀ (vs : List GroundTerm), allSome (vs.map some) = some vs
  | [] => rfl
  | v :: vs => by simp [allSome, allSome_map_some vs]

mutual
  /-- What `instO` reads off a term is its evaluation's result, where no function overload covers
  anything. -/
  theorem evalTerm_of_instO (c : Semantics) (σ : Subst) (hN : ∀ f vs, c.fnCover f vs = none) :
      ∀ (t : Term) {v : GroundTerm}, instO c σ t = some v → EvalTerm c σ t (some v)
    | .var _, _, h => by rw [← h]; exact .var
    | .dv _ _, _, h => by cases h; exact .dv
    | .app f ts, v, h => by
      simp only [instO] at h
      obtain ⟨vs, hvs, h⟩ := Option.bind_eq_some_iff.mp h
      have hs := evalTerms_of_instO c σ hN ts hvs
      by_cases hc : c.isCtor f = true
      · rw [if_pos hc] at h; cases h
        have := EvalTerm.ctor hc hs
        rwa [allSome_map_some] at this
      · rw [if_neg hc] at h
        by_cases ho : c.isOvl f = true
        · rw [if_pos ho] at h; cases h
          have := EvalTerm.ovl (by simpa using hc) ho hs (fun vs _ => hN f vs)
          rwa [allSome_map_some] at this
        · rw [if_neg ho] at h; cases h
    | .inj _ _ t, _, h => by
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .inj (evalTerm_of_instO c σ hN t hw)
    | .as _ _, _, h => by simp [instO] at h
  theorem evalTerms_of_instO (c : Semantics) (σ : Subst) (hN : ∀ f vs, c.fnCover f vs = none) :
      ∀ (ts : List Term) {vs : List GroundTerm}, instOs c σ ts = some vs → EvalTerms c σ ts (vs.map some)
    | [], _, h => by cases h; exact .nil
    | t :: ts, _, h => by
      simp only [instOs] at h
      obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vs', hvs', rfl⟩ := Option.map_eq_some_iff.mp h
      exact .cons (evalTerm_of_instO c σ hN t hv) (evalTerms_of_instO c σ hN ts hvs')
end

/-- **A step by the rule `r`** under `sub vs`: its left side read by `instO` is x, it has no
`requires`, its right side read by `instO` is y, and no rule of a smaller priority applies. -/
theorem step_of_instO {c : Semantics} {r : Rule} (hr : r ∈ c.rules) {vs : List GroundTerm} {x y : Config c}
    (hσ : SortsAre c r.vars vs) (hl : instO c (sub vs) r.lhs = some x.val) (hreq : r.req = none)
    (he : instO c (sub vs) r.rhs = some y.val)
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val)
    (hens : r.ens.isNone = true := by decide +kernel)
    (hpre : r.pre.isTop = true := by decide +kernel) (hpost : r.post.isTop = true := by decide +kernel)
    (hno : c.fnOvlSyms = [] := by decide +kernel) :
    Step c x y :=
  .rule r hr (sub vs) (wellSorted_sub hσ) (patVal_of_instO c _ r.lhs hl)
    (fun t ht => by rw [hreq] at ht; cases ht) (Cond.eq_top_of_isTop hpre ▸ .top) (evalTerm_of_instO c _ (OvlLaws.fnCover_none_of_noFnOvl hno) r.rhs he)
    (fun t ht => by rw [ht] at hens; cases hens) (Cond.eq_top_of_isTop hpost ▸ .top) hprio

end OvlStep

/-! ## ovlsub in the kernel -/

namespace OvlSub

open OvlStep

definition_of defn from "f2-examples/ovlsub.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The symbols and sorts the facts name, by number (`names_ok`). -/
def kCell : Sym := 385
def capN : Sym := 387
def done : Sym := 388
def inf : Sym := 389
def run : Sym := 390
def wrap : Sym := 392
def z : Sym := 393
def capGas : Sym := 394
def gasS : Srt := 32
def nS : Srt := 33
def pgmS : Srt := 34

theorem names_ok : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName capN = "LblcapN" ∧ c.symName done = "Lbldone" ∧
    c.symName inf = "Lblinf" ∧ c.symName run = "Lblrun" ∧ c.symName wrap = "Lblwrap" ∧ c.symName z = "Lblz" ∧
    c.symName capGas = "LblcapGas" ∧ c.sortName gasS = "Gas" ∧ c.sortName nS = "N" ∧ c.sortName pgmS = "Pgm" := by
  decide +kernel

/-- `capGas` is the one overloading symbol: at Gas, over `capN`; the last symbol of the
definition's own. -/
theorem ovls_eq : c.ovls = [⟨⟨capGas, [gasS], gasS⟩, [capN]⟩] ∧ c.symNames.length + nRegSyms - 1 = capGas ∧
    c.isOvl capGas = true ∧ c.isCtor capGas = false := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- `z`, injected into Gas; `inf`. -/
def zG : GroundTerm := .inj nS gasS (.ctor z [])
def infG : GroundTerm := .ctor inf []

/-- `capGas(inj{N,Gas}(z))` denotes `inj{N,Gas}(capN(z))`; a raw `capGas(inf)` is a value of Gas
(no overload covers `inf`), a raw `capGas(inj{N,Gas}(z))` is none (the overload covers it). -/
theorem norm_capGas : c.norm capGas [zG] = .inj nS gasS (.ctor capN [.ctor z []]) ∧
    c.norm capGas [infG] = .ctor capGas [infG] ∧
    c.sortOf (.ctor capGas [infG]) = some gasS ∧ c.sortOf (.ctor capGas [zG]) = none := by
  decide +kernel

/-- The configuration with `st` of sort `Pgm` in the k cell and the counter at 0. -/
def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj pgmS Srt.kitem st, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]
def ctr : GroundTerm := .ctor counterLabel [.dv Srt.int (.int 0)]

def X1 : Config c := ⟨cfg (.ctor run [.inj nS gasS (.ctor capN [.ctor z []])]), by decide +kernel⟩
def Y1 : Config c := ⟨cfg (.ctor done [zG]), by decide +kernel⟩
def X2 : Config c := ⟨cfg (.ctor run [.ctor capGas [infG]]), by decide +kernel⟩
def Y2 : Config c := ⟨cfg (.ctor done [infG]), by decide +kernel⟩
def X3 : Config c := ⟨cfg (.ctor wrap [zG]), by decide +kernel⟩
def Y3 : Config c := ⟨cfg (.ctor done [.inj nS gasS (.ctor capN [.ctor z []])]), by decide +kernel⟩

/-- Both rules have priority 50: neither waits on the other. -/
theorem prio_flat : c.rules.all (fun r => r.prio == 50) = true := by decide +kernel

theorem noPrio {x : GroundTerm} {r : Rule} (hr : r ∈ c.rules) :
    ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x := by
  intro r' hr' hlt
  have h1 := List.all_eq_true.mp prio_flat r hr
  have h2 := List.all_eq_true.mp prio_flat r' hr'
  simp only [beq_iff_eq] at h1 h2
  omega

theorem two : c.rules.length = 2 := by decide +kernel

/-- The rules: `run(cap(G)) => done(G)` and `wrap(G) => done(cap(G))`. -/
noncomputable abbrev runR : Rule := c.rules[0]'(by rw [two]; decide)
noncomputable abbrev wrapR : Rule := c.rules[1]'(by rw [two]; decide)

theorem rules_shape : runR.vars = [gasS, Srt.counter] ∧ wrapR.vars = [gasS, Srt.counter] ∧
    runR.req = none ∧ wrapR.req = none := by
  decide +kernel

theorem sorts (g : GroundTerm) (hg : c.sortOf g = some gasS) : SortsAre c [gasS, Srt.counter] [g, ctr] :=
  ⟨hg, by decide +kernel, trivial⟩

/-- **A step through the overload**: `run(capGas(G))` denotes `run(inj{N,Gas}(capN(z)))` at
`G = inj{N,Gas}(z)`. -/
theorem step_run : Step c X1 Y1 :=
  step_of_instO (List.getElem_mem _) (vs := [zG, ctr])
    (by rw [rules_shape.1]; exact sorts zG (by decide +kernel)) (by decide +kernel) rules_shape.2.2.1
    (by decide +kernel) (noPrio (List.getElem_mem _))

/-- At a raw value: `run(capGas(G))` denotes `run(capGas(inf))` at `G = inf`. -/
theorem step_raw : Step c X2 Y2 :=
  step_of_instO (List.getElem_mem _) (vs := [infG, ctr])
    (by rw [rules_shape.1]; exact sorts infG (by decide +kernel)) (by decide +kernel) rules_shape.2.2.1
    (by decide +kernel) (noPrio (List.getElem_mem _))

/-- In a right side: `done(cap(G))` at `G = inj{N,Gas}(z)` is `done(inj{N,Gas}(capN(z)))`. -/
theorem step_wrap : Step c X3 Y3 :=
  step_of_instO (r := wrapR) (List.getElem_mem _) (vs := [zG, ctr])
    (by rw [rules_shape.2.1]; exact sorts zG (by decide +kernel)) (by decide +kernel) rules_shape.2.2.2
    (by decide +kernel) (noPrio (List.getElem_mem _))

end OvlSub

#print axioms OvlSub.coreOK
#print axioms OvlSub.step_run
#print axioms OvlSub.step_raw
#print axioms OvlSub.step_wrap

/-! ## The executable step on overloading symbols -/

namespace OvlSub

theorem ready : CExec.execReady c = true := by decide +kernel

theorem readsConfined_ready : c.readsConfined = false := CExec.readsConfined_of_execReady coreOK ready

/-- `execReady` gives the rule `wrap` predicates the executable step evaluates and a left side
binding both of its variables. -/
theorem wrap_plain_ready : CExec.predAtoms wrapR.pre = true ∧ CExec.predAtoms wrapR.post = true ∧
    binds wrapR.vars.length (varOccs wrapR.lhs) = true :=
  CExec.rule_atoms_of_execReady ready (List.getElem_mem _)

theorem exec_run : Step c X1 Y1 :=
  (CExec.successorsN_step_ready ready (n := 20) (x := X1) (y := Y1.val) (by decide +kernel)).2

theorem exec_raw : Step c X2 Y2 :=
  (CExec.successorsN_step_ready ready (n := 20) (x := X2) (y := Y2.val) (by decide +kernel)).2

theorem exec_wrap : Step c X3 Y3 :=
  (CExec.successorsN_step_ready ready (n := 20) (x := X3) (y := Y3.val) (by decide +kernel)).2

end OvlSub

#print axioms OvlSub.exec_run
#print axioms OvlSub.exec_wrap

/-! ## The `FnHyp` deciders on clause patterns that apply overloading symbols -/

namespace OvlList

definition_of defn from "f2-examples/ovllist.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- `count(.Stmts) = 0` and `count(_S SS) = 1 +Int count(SS)`, both patterns headed by overloading
symbols that overload others: the two clauses agree because the heads' overload closures meet
nowhere (`clausesHeadApart`, in `fnExclusiveIO`), and each clause is match independent because a
normal form determines its arguments (`uniqL`'s overloading branch, `norm_inj_ovlF`); only `count`'s
totality (its cover) and termination are named. -/
theorem named : c.agreeObligationsI = [] ∧ c.matchObligationsL = [] ∧ (c.totalObligationsRP [] []).length = 1 := by
  decide +kernel

end OvlList

#print axioms OvlList.named

/-- The successors `CExec` lists from each configuration of `test/collexec/` named, after its
readiness; with `steps`, the run of that many steps (each to the first successor). -/
def execShow (path : String) (names : List String) (steps : Nat := 1) : IO Unit := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile path) | throw (IO.userError "KORE read error")
  let .ok d := Parse.parse k | throw (IO.userError "refused")
  let c := d.sem
  IO.println s!"{path}: readiness {CExec.execReady c}"
  for n in names do
    let x ← match CExec.configOfText c (← IO.FS.readFile s!"test/collexec/{n}.kore") with
      | .ok x => pure x
      | .error e => throw (IO.userError s!"{n}: {e}")
    if steps ≤ 1 then
      let ys := CExec.successors c x
      IO.println s!"{n}: {ys.length}"
      for y in ys do IO.println ("  " ++ CExec.showValue c y)
    else
      let (path, _) := CExec.runFrom c Exec.fuel steps x
      IO.println s!"{n}: {path.length} steps"
      IO.println ("  " ++ CExec.showValue c (path.getLast?.getD x))

/--
info: f2-examples/ovlsub.kompile.kore: readiness true
ovlsub-run: 1
  Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortPgm{}, SortKItem{}}(Lbldone{}(inj{SortN{}, SortGas{}}(Lblz{}()))), dotk{}())), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))
ovlsub-raw: 1
  Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortPgm{}, SortKItem{}}(Lbldone{}(Lblinf{}())), dotk{}())), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))
ovlsub-wrap: 1
  Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortPgm{}, SortKItem{}}(Lbldone{}(inj{SortN{}, SortGas{}}(LblcapN{}(Lblz{}())))), dotk{}())), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))
-/
#guard_msgs in
#eval execShow "f2-examples/ovlsub.kompile.kore" ["ovlsub-run", "ovlsub-raw", "ovlsub-wrap"]

/--
info: f2-examples/ovllist.kompile.kore: readiness true
ovllist-len: 3 steps
  Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortPgm{}, SortKItem{}}(Lbldone{}(\dv{SortInt{}}("4"))), dotk{}())), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))
-/
#guard_msgs in
#eval execShow "f2-examples/ovllist.kompile.kore" ["ovllist-len"] (steps := 5)

/-- info: ovlconf: readiness true -/
#guard_msgs in
#eval do IO.println s!"ovlconf: readiness {CExec.execReady (← match Kore.parseDefinition (← IO.FS.readFile "f2-examples/ovlconf.kompile.kore") with
  | .ok k => match Parse.parse k with | .ok d => pure d.sem | .error _ => throw (IO.userError "refused")
  | .error _ => throw (IO.userError "KORE read error"))}"

