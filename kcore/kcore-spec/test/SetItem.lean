/-
  Set patterns without concatenation, read from K 7.1.337 kompile's own KORE
  (`f2-examples/setitem.k`, `setitem.kompile.kore`). Run from the package root:
  `lake env lean test/SetItem.lean`.
  - `SetItem(P)` alone in a left side (`<s> SetItem(X:Int) => .Set </s>`, and `SetItem(1)` as in the
    corpus's symbolic-collection-frames) and a cell set's element alone (`<tasks> <task> <id> I
    </id> </task> => .Bag </tasks>`, kompile's `TaskCellSetItem(<task>(<id>(I)))`) are collection
    patterns (`isCollPat`): the text is read with nothing unaccounted and `coreOK` holds.
  - The rule `take` steps from `go` with `<s>` holding `{5}` to `got(5)` with `<s>` empty: its left
    side denotes the configuration under `X ↦ 5` (`PatVal.coll` at `SetItem`, read by `Term.instP`).
  - The rule `finish` steps from `finish` with `<tasks>` holding the one task of id 7 to `got(7)`
    with `<tasks>` empty (`PatVal.coll` at the cell set's element, a parameter implemented by the
    set's element).
  The left sides apply collection pattern symbols, which `ok` (the executable matcher's context)
  does not admit, so the steps are built from `Step.rule`: the match by `PatVal.of_instP`, the right
  side by the executable evaluation's soundness (`Exec.evalT_sound`), whose contexts `coreOK`'s
  sorting conditions and the functions' conditions give. Every fact is a kernel decision.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- The functions' clauses as `fnOK` checks them, from `fnsOK`, their predicates being `\top` and
their having no existential variable (`Exec.clauseCtx_of` reads these from `ok`). -/
theorem clauseCtx_of_fns {c : Semantics} (hfns : c.fnsOK = true)
    (hpre : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre = .top)
    (hpl : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.exs = [] ∧ cl.post = .top) : Exec.ClauseCtx c := by
  intro fn hfn'
  rcases List.mem_append.mp hfn' with hfn | hfn
  rotate_left
  · exact ⟨[], fun k hk => (nomatch hk), fun cl hcl =>
      let ⟨h1, h2, h3, h4, h5, h6⟩ := sortPreds_ctx hfn cl hcl
      ⟨h1, h2, h3, h4, h5, h6, hpre fn hfn' cl hcl, hpl fn hfn' cl hcl⟩⟩
  have hok := (List.all_eq_true.mp hfns) fn hfn
  simp only [Semantics.fnOK, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨hcls, _⟩ := hok
  refine ⟨c.fns.map Fn.sig, fun k hk => ?_, fun cl hcl => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
    exact ⟨g, List.mem_append_left _ hg, rfl⟩
  · have := hcls cl hcl
    simp only [Semantics.clauseOK, Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨this.1.1.1.1.1, this.1.1.1.1.2, this.1.1.1.2, this.1.1.2, this.1.2, this.2, hpre fn hfn' cl hcl,
      hpl fn hfn' cl hcl⟩

/-- **A step by the rule `r`** under the substitution `sub vs`: its left side read symbol by symbol
is the configuration x, it has no `requires`, its right side evaluates to y, and no rule of a
smaller priority applies. -/
theorem step_of {c : Semantics} (hsc : SortCtx c) (hcc : Exec.ClauseCtx c) (hmc : Exec.MatchCtx c)
    {r : Rule} (hr : r ∈ c.rules) {vs : List GroundTerm} {x y : Config c} (hσ : SortsAre c r.vars vs)
    (hu : Term.instP c (sub vs) r.lhs = some x.val)
    (ha : (Term.aliasPairsP c (sub vs) r.lhs).map Prod.fst = (Term.aliasPairsP c (sub vs) r.lhs).map Prod.snd)
    (hreq : r.req.isNone = true) (n : Nat) (he : Exec.evalT c n (sub vs) r.rhs = some (some y.val))
    (hrhs : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.rhs = some topCellSort)
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val)
    (hens : r.ens.isNone = true := by decide +kernel)
    (hpre : r.pre.isTop = true := by decide +kernel) (hpost : r.post.isTop = true := by decide +kernel) :
    Step c x y :=
  .rule r hr (sub vs) (wellSorted_sub hσ) (PatVal.of_instP _ r.lhs hu ha)
    (fun t ht => by rw [ht] at hreq; cases hreq) (Cond.eq_top_of_isTop hpre ▸ .top)
    (Exec.evalT_sound hsc hcc hmc n he Exec.headsOK_fns (wellSorted_sub hσ) hrhs)
    (fun t ht => by rw [ht] at hens; cases hens) (Cond.eq_top_of_isTop hpost ▸ .top) hprio

/-- The reader's verdict: the sentences unaccounted and the inert constructor axioms not induced. -/
def verdict (path : String) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    return match Parse.parse k with
      | .ok d => s!"read; unaccounted {(Parse.unconsumed k d).map (·.detail)}; not induced {(Parse.uninduced k d).length}"
      | .error r => r.reason.name

/-- info: read; unaccounted []; not induced 0 -/
#guard_msgs in
#eval show IO Unit from do IO.println (← verdict "f2-examples/setitem.kompile.kore")

namespace SetItemT

definition_of defn from "f2-examples/setitem.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The symbols and sorts the facts name, by number. -/
def kCell : Sym := 393
def sCell : Sym := 395
def tasksCell : Sym := 397
def finishL : Sym := 401
def goL : Sym := 402
def gotL : Sym := 403
def idCell : Sym := 404
def taskCell : Sym := 405
def taskItem : Sym := 412
def pgmS : Srt := 41
def taskSetS : Srt := 42

theorem names_ok : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName sCell = "Lbl'-LT-'s'-GT-'" ∧
    c.symName tasksCell = "Lbl'-LT-'tasks'-GT-'" ∧ c.symName finishL = "Lblfinish" ∧ c.symName goL = "Lblgo" ∧
    c.symName gotL = "Lblgot" ∧ c.symName idCell = "Lbl'-LT-'id'-GT-'" ∧ c.symName taskCell = "Lbl'-LT-'task'-GT-'" ∧
    c.symName taskItem = "LblTaskCellSetItem" ∧ c.sortName pgmS = "Pgm" ∧ c.sortName taskSetS = "TaskCellSet" := by
  decide +kernel

/-- `SetItem`, the cell set's element and `_Set_` are collection pattern symbols. -/
theorem collPats : c.isCollPat setElem = true ∧ c.isCollPat taskItem = true ∧ c.isCollPat setConcat = true := by
  decide +kernel

tables_of T from "f2-examples/setitem.kompile.kore"

theorem T_eq : T = tables c := by decide +kernel

-- `faithCoreOK` by `decide_cheap`: each conjunct apart, the names on their codes
set_option maxHeartbeats 1000000 in
open Faithful Faithful.Model in
/-- `coreOK`, conjunct by conjunct, the sort checks from the tables. -/
theorem coreOK : c.coreOK = true :=
  Semantics.coreOK_of_T T_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide_cheap)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem sortedOK : c.sortedOK = true := by decide_cheap
theorem clausesPreTopC : c.clausesPreTop = true := by decide +kernel
theorem srReady : c.srReady = true := srReady_of_T T_eq (by decide +kernel)
theorem matchReady : c.matchReady = true := matchReady_of_T T_eq (by decide +kernel)
theorem fnsOK : c.fnsOK = true := by decide +kernel

theorem hsc : SortCtx c := sortCtx_of_all sortedOK srReady (Semantics.ovlCase_of (by decide +kernel))
theorem hcc : Exec.ClauseCtx c := clauseCtx_of_fns fnsOK (Semantics.allFns_preTop clausesPreTopC)
  (Semantics.sortedOK_plainCl_of_noExs sortedOK (Semantics.fnsNoExs_of_all (by decide +kernel)))
theorem hmc : Exec.MatchCtx c := Exec.matchCtx_of matchReady

/-- Every rule has priority 50: none waits on another. -/
theorem prio_flat : c.rules.all (fun r => r.prio == 50) = true := by decide +kernel

theorem noPrio {x : GroundTerm} {r : Rule} (hr : r ∈ c.rules) : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x := by
  intro r' hr' hlt
  have h1 := List.all_eq_true.mp prio_flat r hr
  have h2 := List.all_eq_true.mp prio_flat r' hr'
  simp only [beq_iff_eq] at h1 h2
  omega

/-- A value of `Int` injected into `KItem`. -/
def iv (n : Int) : GroundTerm := .inj Srt.int Srt.kitem (.dv Srt.int (.int n))
/-- The counter cell at 0. -/
def ctr : GroundTerm := .ctor counterLabel [.dv Srt.int (.int 0)]
/-- The `<s>` cell holding the set `es`, and the `<tasks>` cell holding the tasks `ts`. -/
def sC (es : List GroundTerm) : GroundTerm := .ctor sCell [.set Srt.set es]
def tasksC (ts : List GroundTerm) : GroundTerm := .ctor tasksCell [.set taskSetS ts]
/-- The task of id `n`. -/
def task (n : Int) : GroundTerm := .ctor taskCell [.ctor idCell [.dv Srt.int (.int n)]]

/-- The configuration with `p` of sort `Pgm` in the k cell. -/
def cfg (p s ts : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj pgmS Srt.kitem p, .ctor dotk []]], s, ts, ctr]

/-! ### `SetItem(X:Int)` alone -/

theorem two_lt : 2 < c.rules.length := by decide +kernel

noncomputable def take : Rule := c.rules[2]'two_lt

theorem take_mem : take ∈ c.rules := List.getElem_mem two_lt
theorem take_vars : take.vars = [Srt.int, 34, Srt.counter] := by decide +kernel
/-- `take`'s left side holds `SetItem(inj{Int,KItem}(X))` in the `<s>` cell. -/
theorem take_lhs_s : Term.beq take.lhs (.app topLabel [.app kCell [.app kseq [.inj pgmS Srt.kitem (.app goL []), .app dotk []]],
    .app sCell [.app setElem [.inj Srt.int Srt.kitem (.var 0)]], .var 1, .var 2]) = true := by decide +kernel

def x1 : GroundTerm := cfg (.ctor goL []) (sC [iv 5]) (tasksC [])
def y1 : GroundTerm := cfg (.ctor gotL [.dv Srt.int (.int 5)]) (sC []) (tasksC [])
def vs1 : List GroundTerm := [.dv Srt.int (.int 5), tasksC [], ctr]

def X1 : Config c := ⟨x1, sortOf_of_T T_eq (by decide +kernel)⟩
def Y1 : Config c := ⟨y1, sortOf_of_T T_eq (by decide +kernel)⟩

/-- **`take` steps**: under `X ↦ 5`, `SetItem(X)` denotes `{5}`. -/
theorem step_take : Step c X1 Y1 :=
  step_of hsc hcc hmc take_mem (vs := vs1) (by
      rw [take_vars]
      exact ⟨sortOf_of_T T_eq (by decide +kernel), sortOf_of_T T_eq (by decide +kernel),
        sortOf_of_T T_eq (by decide +kernel), trivial⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 100 (by decide +kernel) (by decide +kernel)
    (noPrio take_mem)

/-! ### A cell set's element alone -/

theorem one_lt : 1 < c.rules.length := by decide +kernel

noncomputable def finish : Rule := c.rules[1]'one_lt

theorem finish_mem : finish ∈ c.rules := List.getElem_mem one_lt
theorem finish_vars : finish.vars = [32, Srt.int, Srt.counter] := by decide +kernel
/-- `finish`'s left side holds `TaskCellSetItem(<task>(<id>(I)))` in the `<tasks>` cell. -/
theorem finish_lhs : Term.beq finish.lhs (.app topLabel [.app kCell [.app kseq [.inj pgmS Srt.kitem (.app finishL []), .app dotk []]],
    .var 0, .app tasksCell [.app taskItem [.app taskCell [.app idCell [.var 1]]]], .var 2]) = true := by decide +kernel

def x2 : GroundTerm := cfg (.ctor finishL []) (sC []) (tasksC [task 7])
def y2 : GroundTerm := cfg (.ctor gotL [.dv Srt.int (.int 7)]) (sC []) (tasksC [])
def vs2 : List GroundTerm := [sC [], .dv Srt.int (.int 7), ctr]

def X2 : Config c := ⟨x2, sortOf_of_T T_eq (by decide +kernel)⟩
def Y2 : Config c := ⟨y2, sortOf_of_T T_eq (by decide +kernel)⟩

/-- **`finish` steps**: under `I ↦ 7`, the cell set's element denotes the set of the one task. -/
theorem step_finish : Step c X2 Y2 :=
  step_of hsc hcc hmc finish_mem (vs := vs2) (by
      rw [finish_vars]
      exact ⟨sortOf_of_T T_eq (by decide +kernel), sortOf_of_T T_eq (by decide +kernel),
        sortOf_of_T T_eq (by decide +kernel), trivial⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 100 (by decide +kernel) (by decide +kernel)
    (noPrio finish_mem)

end SetItemT

#print axioms SetItemT.coreOK
#print axioms SetItemT.step_take
#print axioms SetItemT.step_finish
