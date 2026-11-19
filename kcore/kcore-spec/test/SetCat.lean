/-
  Concatenating set patterns, read from K 7.1.337 kompile's own KORE (`f2-examples/setcat.k`,
  `setcat.kompile.kore`). Run from the package root: `lake env lean test/SetCat.lean`.
  `_Set_` is the union of two sets with no member in common, undefined where they share one
  (Hooks.lean), so `SetItem(P) S` denotes `{v} ∪ s` with v not in s: one match per member.
  - The text is read with nothing unaccounted (its two `[idem]` axioms, `_Set_`'s and
    `_TaskCellSet_`'s, are `unread setIdempotence`); `_Set_` and the cell set's concatenation are
    collection pattern symbols; `coreOK` holds.
  - `drop` (`<s> SetItem(_X) REST => REST </s>`) steps from `<s>` holding `{1, 2}` to `{2}` and to
    `{1}`, and to nothing else: a match binds `REST` to the set without the member `_X` matched
    (`drop_only`), never to the whole set.
  - `add` (`<s> S => S SetItem(1) </s>`) has no successor where 1 is in S: its right side
    concatenates overlapping sets and has no value (`add_stuck`).
  - `bump` (`<task> <id> I => I +Int 10 </id> </task>`, kompile's
    `TaskCellSetItem(<task>(<id>(I))) _DotVar1` on both sides) updates one task in place: from the
    tasks of ids 1 and 2 to those of ids 2 and 11.
  The left sides apply collection pattern symbols, which `ok` (the executable matcher's context)
  does not admit, so the steps are built from `Step.rule` (match by `PatVal.of_instP`, right side by
  `Exec.evalT_sound`), and the non-steps by inverting `Step.rule`: a rule whose left side is apart
  from one that matches (`overlap`, `Det.overlap_sound_term`) does not match; `drop`'s and `add`'s
  matches are read off the pattern, and the right side's result is the executable evaluation's
  (`Exec.evalT_congr`, `EvalTerm.functional`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- The functions' clauses as `fnOK` checks them, from `fnsOK`; their precondition `.top` from
`clausesPreTop`, their having no existential variable and their right sides'
predicate `.top` from `clausesPlain`, as their patterns bind every variable (`clauseOK`). -/
theorem clauseCtx_of_fns {c : Semantics} (hfns : c.fnsOK = true) (hp : c.clausesPlain = true)
    (hpreTop : c.clausesPreTop = true) :
    Exec.ClauseCtx c := by
  intro fn hfn'
  rcases List.mem_append.mp hfn' with hfn | hfn
  rotate_left
  · exact ⟨[], fun k hk => (nomatch hk), fun cl hcl =>
      ⟨(sortPreds_ctx hfn cl hcl).1, (sortPreds_ctx hfn cl hcl).2.1, (sortPreds_ctx hfn cl hcl).2.2.1,
        (sortPreds_ctx hfn cl hcl).2.2.2.1, (sortPreds_ctx hfn cl hcl).2.2.2.2.1,
        (sortPreds_ctx hfn cl hcl).2.2.2.2.2, Semantics.sortPreds_pre hfn cl hcl,
        Semantics.sortPreds_exs hfn cl hcl, Semantics.sortPreds_post hfn cl hcl⟩⟩
  have hok := (List.all_eq_true.mp hfns) fn hfn
  simp only [Semantics.fnOK, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨hcls, _⟩ := hok
  refine ⟨c.fns.map Fn.sig, fun k hk => ?_, fun cl hcl => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
    exact ⟨g, List.mem_append_left _ hg, rfl⟩
  · have := hcls cl hcl
    simp only [Semantics.clauseOK, Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨this.1.1.1.1.1, this.1.1.1.1.2, this.1.1.1.2, this.1.1.2, this.1.2, this.2,
      Semantics.allFns_preTop hpreTop fn hfn' cl hcl, Semantics.clausesPlain_plainCl_of_binds hp hfn hcl this.1.1.1.2⟩

/-- **A step by the rule `r`** under the substitution `sub vs` (as test/SetItem.lean). -/
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

/-- A constructor's pattern denotes only constructor terms of that constructor. -/
theorem ctor_inv {c : Semantics} (hmc : Exec.MatchCtx c) {σ : Subst} {f : Sym} {ps : List Term} {v : GroundTerm}
    (hc : c.isCtor f = true) (h : PatVal c σ (.app f ps) v) : ∃ vs, v = .ctor f vs ∧ PatVals c σ ps vs := by
  generalize ht : Term.app f ps = t at h
  cases h with
  | ctor _ hs => cases ht; exact ⟨_, rfl, hs⟩
  | hook hp _ _ => cases ht; rw [hmc.patHooks _ (List.contains_iff_mem.mp hp)] at hc; cases hc
  | coll hc' _ _ _ => cases ht; rw [hc] at hc'; cases hc'
  | ovl hc' _ _ _ => cases ht; rw [hc] at hc'; cases hc'
  | _ => cases ht

theorem pats4 {c : Semantics} {σ : Subst} {p₁ p₂ p₃ p₄ : Term} {vs : List GroundTerm}
    (h : PatVals c σ [p₁, p₂, p₃, p₄] vs) : ∃ v₁ v₂ v₃ v₄, vs = [v₁, v₂, v₃, v₄] ∧
      PatVal c σ p₁ v₁ ∧ PatVal c σ p₂ v₂ ∧ PatVal c σ p₃ v₃ ∧ PatVal c σ p₄ v₄ := by
  obtain ⟨v₁, _, rfl, h1, h⟩ := Det.PatVals.cons_inv' h
  obtain ⟨v₂, _, rfl, h2, h⟩ := Det.PatVals.cons_inv' h
  obtain ⟨v₃, _, rfl, h3, h⟩ := Det.PatVals.cons_inv' h
  obtain ⟨v₄, _, rfl, h4, h⟩ := Det.PatVals.cons_inv' h
  cases h
  exact ⟨_, _, _, _, rfl, h1, h2, h3, h4⟩

theorem pats1 {c : Semantics} {σ : Subst} {p : Term} {vs : List GroundTerm}
    (h : PatVals c σ [p] vs) : ∃ v, vs = [v] ∧ PatVal c σ p v := by
  obtain ⟨v, _, rfl, h1, h⟩ := Det.PatVals.cons_inv' h
  cases h
  exact ⟨_, rfl, h1⟩

theorem pats2 {c : Semantics} {σ : Subst} {p q : Term} {vs : List GroundTerm}
    (h : PatVals c σ [p, q] vs) : ∃ v w, vs = [v, w] ∧ PatVal c σ p v ∧ PatVal c σ q w := by
  obtain ⟨v, _, rfl, h1, h⟩ := Det.PatVals.cons_inv' h
  obtain ⟨w, _, rfl, h2, h⟩ := Det.PatVals.cons_inv' h
  cases h
  exact ⟨_, _, rfl, h1, h2⟩

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
#eval show IO Unit from do IO.println (← verdict "f2-examples/setcat.kompile.kore")

/-- The classes of the text's `[idem]` axioms. -/
def idemClasses (path : String) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let ss := k.modules.flatMap (·.sentences)
    let cls := ss.filterMap fun s => match s with
      | .axiom a => if KoreAML.Parse.hasAttr a.attributes "idem" then some (reprStr (Parse.classifyShape s)) else none
      | _ => none
    return toString cls

/-- info: [KCore.Parse.SentenceClass.unread (KCore.Parse.UnreadReason.setIdempotence), KCore.Parse.SentenceClass.unread (KCore.Parse.UnreadReason.setIdempotence)] -/
#guard_msgs in
#eval show IO Unit from do IO.println (← idemClasses "f2-examples/setcat.kompile.kore")

namespace SetCatT

definition_of defn from "f2-examples/setcat.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The symbols and sorts the facts name, by number. -/
def kCell : Sym := 393
def sCell : Sym := 395
def tasksCell : Sym := 397
def addL : Sym := 399
def bumpL : Sym := 400
def doneL : Sym := 401
def goL : Sym := 402
def idCell : Sym := 403
def taskCell : Sym := 404
def taskItem : Sym := 411
def taskConcat : Sym := 412
def pgmS : Srt := 41
def taskSetS : Srt := 42

theorem names_ok : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName sCell = "Lbl'-LT-'s'-GT-'" ∧
    c.symName tasksCell = "Lbl'-LT-'tasks'-GT-'" ∧ c.symName addL = "Lbladd" ∧ c.symName bumpL = "Lblbump" ∧
    c.symName doneL = "Lbldone" ∧ c.symName goL = "Lblgo" ∧ c.symName idCell = "Lbl'-LT-'id'-GT-'" ∧
    c.symName taskCell = "Lbl'-LT-'task'-GT-'" ∧ c.symName taskItem = "LblTaskCellSetItem" ∧
    c.symName taskConcat = "Lbl'Unds'TaskCellSet'Unds'" ∧ c.sortName pgmS = "Pgm" ∧
    c.sortName taskSetS = "TaskCellSet" := by
  decide +kernel

/-- `SetItem`, `_Set_`, the cell set's element and its concatenation are collection pattern symbols. -/
theorem collPats : c.isCollPat setElem = true ∧ c.isCollPat setConcat = true ∧ c.isCollPat taskItem = true ∧
    c.isCollPat taskConcat = true := by
  decide +kernel

tables_of T from "f2-examples/setcat.kompile.kore"

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
theorem srReady : c.srReady = true := srReady_of_T T_eq (by decide +kernel)
theorem matchReady : c.matchReady = true := matchReady_of_T T_eq (by decide +kernel)
theorem fnsOK : c.fnsOK = true := by decide +kernel

theorem hsc : SortCtx c := sortCtx_of_all sortedOK srReady (Semantics.ovlCase_of (by decide +kernel))
theorem hcc : Exec.ClauseCtx c := clauseCtx_of_fns fnsOK (by decide +kernel) (by decide +kernel)
theorem hmc : Exec.MatchCtx c := Exec.matchCtx_of matchReady

/-- No agreement or match obligation is named, so the clauses of one priority are coherent. -/
theorem coherent : CoherentAll c :=
  coherentAll_of_parts (matchIndependentAll_of_sortedOK sortedOK (Semantics.fnsNoExs_of_all (by decide +kernel)) matchReady (.of_nil (by decide +kernel)))
    fun f fn hfn => by
      obtain ⟨hmem, -⟩ := lookupFn_spec hfn
      rcases List.mem_append.mp hmem with hu | hp
      · exact clausesAgree_of_sortedOK sortedOK (Semantics.fnsNoExs_of_all (by decide +kernel)) srReady matchReady
          (fun f hf => by rw [show c.agreeObligations = [] by decide +kernel] at hf; nomatch hf) fn hu
      · exact sortPreds_agree hp

/-- Every rule has priority 50: none waits on another. -/
theorem prio_flat : c.rules.all (fun r => r.prio == 50) = true := by decide +kernel

theorem noPrio {x : GroundTerm} {r : Rule} (hr : r ∈ c.rules) : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x := by
  intro r' hr' hlt
  have h1 := List.all_eq_true.mp prio_flat r hr
  have h2 := List.all_eq_true.mp prio_flat r' hr'
  simp only [beq_iff_eq] at h1 h2
  omega

/-! ### The rules -/

theorem len3 : c.rules.length = 3 := by decide +kernel

noncomputable def add : Rule := c.rules[0]'(by rw [len3]; decide)
noncomputable def bump : Rule := c.rules[1]'(by rw [len3]; decide)
noncomputable def drop : Rule := c.rules[2]'(by rw [len3]; decide)

theorem add_mem : add ∈ c.rules := List.getElem_mem _
theorem bump_mem : bump ∈ c.rules := List.getElem_mem _
theorem drop_mem : drop ∈ c.rules := List.getElem_mem _

theorem mem_rules {r : Rule} (hr : r ∈ c.rules) : r = add ∨ r = bump ∨ r = drop := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  match i, hi with
  | 0, _ => exact .inl rfl
  | 1, _ => exact .inr (.inl rfl)
  | 2, _ => exact .inr (.inr rfl)
  | n + 3, hi => rw [len3] at hi; omega

theorem add_vars : add.vars = [Srt.set, 34, Srt.counter] := by decide +kernel
theorem bump_vars : bump.vars = [32, Srt.int, taskSetS, Srt.counter] := by decide +kernel
theorem drop_vars : drop.vars = [Srt.kitem, Srt.set, 34, Srt.counter] := by decide +kernel

/-- `drop`'s left side: `SetItem(_X) REST` in the `<s>` cell. -/
theorem drop_lhs : drop.lhs = .app topLabel [.app kCell [.app kseq [.inj pgmS Srt.kitem (.app goL []), .app dotk []]],
    .app sCell [.app setConcat [.app setElem [.var 0], .var 1]], .var 2, .var 3] :=
  Det.Term.beq_sound (by decide +kernel)

/-- `add`'s left side: a plain variable `S` in the `<s>` cell; its right side `S SetItem(1)`. -/
theorem add_lhs : add.lhs = .app topLabel [.app kCell [.app kseq [.inj pgmS Srt.kitem (.app addL []), .app dotk []]],
    .app sCell [.var 0], .var 1, .var 2] :=
  Det.Term.beq_sound (by decide +kernel)

/-- `bump`'s left side: a cell set's element concatenated with the other tasks. -/
theorem bump_lhs : bump.lhs = .app topLabel [.app kCell [.app kseq [.inj pgmS Srt.kitem (.app bumpL []), .app dotk []]],
    .var 0, .app tasksCell [.app taskConcat [.app taskItem [.app taskCell [.app idCell [.var 1]]], .var 2]], .var 3] :=
  Det.Term.beq_sound (by decide +kernel)

/-! ### Values -/

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

/-! ### `SetItem(_X) REST`: one match per member -/

def x1 : GroundTerm := cfg (.ctor goL []) (sC [iv 1, iv 2]) (tasksC [])
def ya : GroundTerm := cfg (.ctor doneL []) (sC [iv 2]) (tasksC [])
def yb : GroundTerm := cfg (.ctor doneL []) (sC [iv 1]) (tasksC [])
def vsa : List GroundTerm := [iv 1, .set Srt.set [iv 2], tasksC [], ctr]
def vsb : List GroundTerm := [iv 2, .set Srt.set [iv 1], tasksC [], ctr]

def X1 : Config c := ⟨x1, sortOf_of_T T_eq (by decide +kernel)⟩
def Ya : Config c := ⟨ya, sortOf_of_T T_eq (by decide +kernel)⟩
def Yb : Config c := ⟨yb, sortOf_of_T T_eq (by decide +kernel)⟩

theorem sorts_a : SortsAre c drop.vars vsa := by
  rw [drop_vars]
  exact ⟨sortOf_of_T T_eq (by decide +kernel), sortOf_of_T T_eq (by decide +kernel),
    sortOf_of_T T_eq (by decide +kernel), sortOf_of_T T_eq (by decide +kernel), trivial⟩

theorem sorts_b : SortsAre c drop.vars vsb := by
  rw [drop_vars]
  exact ⟨sortOf_of_T T_eq (by decide +kernel), sortOf_of_T T_eq (by decide +kernel),
    sortOf_of_T T_eq (by decide +kernel), sortOf_of_T T_eq (by decide +kernel), trivial⟩

/-- **`drop` steps to `{2}`**: `_X ↦ 1`, `REST ↦ {2}`. -/
theorem step_a : Step c X1 Ya :=
  step_of hsc hcc hmc drop_mem sorts_a (by decide +kernel) (by decide +kernel) (by decide +kernel) 100
    (by decide +kernel) (by decide +kernel) (noPrio drop_mem)

/-- **`drop` steps to `{1}`**: `_X ↦ 2`, `REST ↦ {1}`. -/
theorem step_b : Step c X1 Yb :=
  step_of hsc hcc hmc drop_mem sorts_b (by decide +kernel) (by decide +kernel) (by decide +kernel) 100
    (by decide +kernel) (by decide +kernel) (noPrio drop_mem)

theorem drop_matches_a : PatVal c (sub vsa) drop.lhs x1 := PatVal.of_instP _ _ (by decide +kernel) (by decide +kernel)

/-- `{u} ⊎ rs = {1, 2}` with `rs` canonical: `u` is one member and `rs` the other. -/
theorem pair_split {u : GroundTerm} {rs : List GroundTerm} (hrs : KCore.Set.Canon rs)
    (h : concatS [u] rs = some [iv 1, iv 2]) : (u = iv 1 ∧ rs = [iv 2]) ∨ (u = iv 2 ∧ rs = [iv 1]) := by
  have hm := Faithful.Model.concatS_mem h
  have hd := (Faithful.Model.concatS_iff.mp h).1 u (List.mem_singleton_self _)
  have hu : u = iv 1 ∨ u = iv 2 := by simpa using (hm u).mpr (.inl (List.mem_singleton_self _))
  have h12 : iv 1 ≠ iv 2 := by decide
  have hrest : ∀ w, w ≠ u → (w ∈ rs ↔ w = iv 1 ∨ w = iv 2) := fun w hw => by
    have := hm w
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    constructor
    · intro hr; exact this.mpr (.inr hr)
    · intro hw'; rcases this.mp hw' with h' | h'
      · exact absurd h' hw
      · exact h'
  have hcan : ∀ w : GroundTerm, KCore.Set.Canon [w] := fun _ => rfl
  rcases hu with rfl | rfl
  · refine .inl ⟨rfl, KCore.Set.ext hrs (hcan _) fun w => ?_⟩
    by_cases hw : w = iv 1
    · subst hw; simp [hd, h12]
    · rw [hrest w hw]; simp [hw]
  · refine .inr ⟨rfl, KCore.Set.ext hrs (hcan _) fun w => ?_⟩
    by_cases hw : w = iv 2
    · subst hw; simp [hd, h12.symm]
    · rw [hrest w hw]; simp [hw]

/-- **A match of `drop` at `{1, 2}`** binds `REST` to `{2}` or to `{1}`, and the cells around it to
their values. -/
theorem drop_match {σ : Subst} (hσ : c.WellSorted drop.vars σ) (h : PatVal c σ drop.lhs x1) :
    (σ.lookup 1 = some (.set Srt.set [iv 2]) ∨ σ.lookup 1 = some (.set Srt.set [iv 1])) ∧
      σ.lookup 2 = some (tasksC []) ∧ σ.lookup 3 = some ctr := by
  rw [drop_lhs] at h
  obtain ⟨vs, hv, hs⟩ := ctor_inv hmc (by decide +kernel) h
  obtain ⟨v₁, v₂, v₃, v₄, rfl, -, h2, h3, h4⟩ := pats4 hs
  simp only [x1, cfg, sC, GroundTerm.ctor.injEq, List.cons.injEq, true_and, and_true] at hv
  obtain ⟨-, rfl, rfl, rfl⟩ := hv
  refine ⟨?_, PatVal.var_inv h3, PatVal.var_inv h4⟩
  obtain ⟨ws, hw, hws⟩ := ctor_inv hmc (by decide +kernel) h2
  obtain ⟨w, rfl, hcat⟩ := pats1 hws
  simp only [GroundTerm.ctor.injEq, List.cons.injEq, true_and, and_true] at hw
  subst hw
  obtain ⟨us, hus, hcv⟩ := Det.PatVal.coll_inv (by decide +kernel) (by decide +kernel) hcat
  obtain ⟨e, r, rfl, he, hr⟩ := pats2 hus
  obtain ⟨as, has, hev⟩ := Det.PatVal.coll_inv (by decide +kernel) (by decide +kernel) he
  obtain ⟨a, rfl, -⟩ := pats1 has
  rw [Faithful.collVal_hook rfl] at hev
  cases hev
  have hl := PatVal.var_inv hr
  obtain ⟨v, hv1, hvs⟩ := hσ 1 Srt.set (by rw [drop_vars]; rfl)
  rw [hl] at hv1
  cases hv1
  rw [Faithful.collVal_hook rfl, Faithful.Model.hook_setConcat_eq] at hcv
  cases r with
  | set s rs =>
    obtain ⟨-, -, -, hso, -, hs⟩ := sortOf_setS.mp hvs
    subst hs
    have hcs : concatS [a] rs = some [iv 1, iv 2] := by
      cases hc : concatS [a] rs with
      | none => simp [hc] at hcv
      | some u => simp [hc] at hcv; rw [hcv]
    rcases pair_split hso hcs with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact .inl hl
    · exact .inr hl
  | _ => simp at hcv

/-- `drop`'s right side has, under a match, the value it has under `sub vs` where the match agrees
with `sub vs` on its variables. -/
theorem drop_rhs {σ : Subst} (hσ : c.WellSorted drop.vars σ) {vs : List GroundTerm} {y : GroundTerm} {Y : Config c}
    (hl : ∀ i ∈ varOccs drop.rhs, σ.lookup i = (sub vs).lookup i)
    (he : Exec.evalT c 100 (sub vs) drop.rhs = some (some y))
    (heval : EvalTerm c σ drop.rhs (some Y.val)) : Y.val = y :=
  Option.some.inj (EvalTerm.functional coherent heval
    (Exec.evalT_sound hsc hcc hmc 100 ((Exec.evalT_congr 100 hl).trans he) Exec.headsOK_fns hσ
      (s := topCellSort) (by decide +kernel)))

theorem drop_rhs_vars : varOccs drop.rhs = [1, 2, 3] := by decide +kernel

/-- **`drop`'s successors of `{1, 2}` are exactly `{2}` and `{1}`**: `add` and `bump` do not
match (their left sides are apart from `drop`'s, which matches), and a match of `drop` binds `REST`
to the set without the member matched. -/
theorem drop_only : ∀ Y, Step c X1 Y → Y = Ya ∨ Y = Yb := by
  intro Y h
  cases h with
  | rule r hr σ hσ hmatch _ _ heval _ =>
    rcases mem_rules hr with rfl | rfl | rfl
    · exact (Det.overlap_sound_term hmc hσ (wellSorted_sub sorts_a) add.lhs (s := topCellSort) (s' := topCellSort) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) hmatch drop_matches_a).elim
    · exact (Det.overlap_sound_term hmc hσ (wellSorted_sub sorts_a) bump.lhs (s := topCellSort) (s' := topCellSort) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) hmatch drop_matches_a).elim
    · obtain ⟨h1, h2, h3⟩ := drop_match hσ hmatch
      have hl : ∀ vs : List GroundTerm, σ.lookup 1 = (sub vs).lookup 1 → (sub vs).lookup 2 = some (tasksC []) →
          (sub vs).lookup 3 = some ctr → ∀ i ∈ varOccs drop.rhs, σ.lookup i = (sub vs).lookup i := by
        intro vs e1 e2 e3 i hi
        rw [drop_rhs_vars] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · exact e1
        · rw [h2, e2]
        · rw [h3, e3]
      rcases h1 with h1 | h1
      · exact .inl (Subtype.ext (drop_rhs hσ (hl vsa (by rw [h1]; rfl) rfl rfl) (by decide +kernel) heval))
      · exact .inr (Subtype.ext (drop_rhs hσ (hl vsb (by rw [h1]; rfl) rfl rfl) (by decide +kernel) heval))

/-! ### `S SetItem(1)` with 1 in S: no value, no step -/

def x3 : GroundTerm := cfg (.ctor addL []) (sC [iv 1, iv 2]) (tasksC [])
def vs3 : List GroundTerm := [.set Srt.set [iv 1, iv 2], tasksC [], ctr]
def X3 : Config c := ⟨x3, sortOf_of_T T_eq (by decide +kernel)⟩

theorem sorts_3 : SortsAre c add.vars vs3 := by
  rw [add_vars]
  exact ⟨sortOf_of_T T_eq (by decide +kernel), sortOf_of_T T_eq (by decide +kernel),
    sortOf_of_T T_eq (by decide +kernel), trivial⟩

theorem add_matches : PatVal c (sub vs3) add.lhs x3 := PatVal.of_instP _ _ (by decide +kernel) (by decide +kernel)

/-- `add`'s right side `S SetItem(1)` at `S = {1, 2}` has no value: the parts share the member 1. -/
theorem add_rhs_undef : Exec.evalT c 100 (sub vs3) add.rhs = some none := by decide +kernel

theorem add_rhs_vars : varOccs add.rhs = [0, 1, 2] := by decide +kernel

/-- **`add` has no successor where 1 is in S.** -/
theorem add_stuck : ∀ Y, ¬ Step c X3 Y := by
  intro Y h
  cases h with
  | rule r hr σ hσ hmatch _ _ heval _ =>
    rcases mem_rules hr with rfl | rfl | rfl
    · rw [add_lhs] at hmatch
      obtain ⟨vs, hv, hs⟩ := ctor_inv hmc (by decide +kernel) hmatch
      obtain ⟨v₁, v₂, v₃, v₄, rfl, -, h2, h3, h4⟩ := pats4 hs
      simp only [X3, x3, cfg, sC, GroundTerm.ctor.injEq, List.cons.injEq, true_and, and_true] at hv
      obtain ⟨-, rfl, rfl, rfl⟩ := hv
      obtain ⟨ws, hw, hws⟩ := ctor_inv hmc (by decide +kernel) h2
      obtain ⟨w, rfl, h0⟩ := pats1 hws
      simp only [GroundTerm.ctor.injEq, List.cons.injEq, true_and, and_true] at hw
      subst hw
      have hl : ∀ i ∈ varOccs add.rhs, σ.lookup i = (sub vs3).lookup i := by
        intro i hi
        rw [add_rhs_vars] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · rw [PatVal.var_inv h0]; rfl
        · rw [PatVal.var_inv h3]; rfl
        · rw [PatVal.var_inv h4]; rfl
      have hu := Exec.evalT_sound hsc hcc hmc 100 ((Exec.evalT_congr 100 hl).trans add_rhs_undef)
        Exec.headsOK_fns hσ (s := topCellSort) (by decide +kernel)
      cases EvalTerm.functional coherent heval hu
    · exact (Det.overlap_sound_term hmc hσ (wellSorted_sub sorts_3) bump.lhs (s := topCellSort) (s' := topCellSort) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) hmatch add_matches).elim
    · exact (Det.overlap_sound_term hmc hσ (wellSorted_sub sorts_3) drop.lhs (s := topCellSort) (s' := topCellSort) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) hmatch add_matches).elim

/-! ### A cell set's element updated in place -/

def x4 : GroundTerm := cfg (.ctor bumpL []) (sC []) (tasksC [task 1, task 2])
def y4 : GroundTerm := cfg (.ctor doneL []) (sC []) (tasksC [task 2, task 11])
def vs4 : List GroundTerm := [sC [], .dv Srt.int (.int 1), .set taskSetS [task 2], ctr]

def X4 : Config c := ⟨x4, sortOf_of_T T_eq (by decide +kernel)⟩
def Y4 : Config c := ⟨y4, sortOf_of_T T_eq (by decide +kernel)⟩

/-- **`bump` steps**: under `I ↦ 1` and the other tasks `{task 2}`, the task of id 1 becomes the
task of id 11 beside the task of id 2. -/
theorem step_bump : Step c X4 Y4 :=
  step_of hsc hcc hmc bump_mem (vs := vs4) (by
      rw [bump_vars]
      exact ⟨sortOf_of_T T_eq (by decide +kernel), sortOf_of_T T_eq (by decide +kernel),
        sortOf_of_T T_eq (by decide +kernel), sortOf_of_T T_eq (by decide +kernel), trivial⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 100 (by decide +kernel) (by decide +kernel)
    (noPrio bump_mem)

end SetCatT

#print axioms SetCatT.coreOK
#print axioms SetCatT.step_a
#print axioms SetCatT.step_b
#print axioms SetCatT.drop_only
#print axioms SetCatT.add_stuck
#print axioms SetCatT.step_bump
