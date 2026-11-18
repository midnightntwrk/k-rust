/-
  The account's arm for the cell tree's initializers (`Parse.initEqnOK`, `Parse.initFunctionalOK`)
  against the model of `KcoreSpec/GenEqsInit.lean`, on kompiled texts (`KcoreSpec/GenEqsInitArm.lean`).
  Run from the package root: `lake env lean -j1 test/GenEqsInitArm.lean`.

  Nothing here writes a right side or a `G` by hand. The equations are the reader's (`Parse.rawEqn?`)
  of the user module's axioms (`user_axioms`, the text's literal); the tree is the presentation's
  (`Cell.all`, bottom up); the arm takes each initializer's equation (`armAccB`, which is
  `initEqnOK` at the tree's cell); `G` is read from the equations (`GenEqs.armG`), the sort
  projections and the getter by `GenEqs.armBase`; the names are checked by `armNameB` (no symbol of
  the semantics, or a sort projection the arm for sort projections accepts, `predProjAcc`). The model
  is `GenEqs.model_of_arm`; each equation at values is `GenEqs.init_arm_at`: the text's equation
  `L(ws) = rhs[ws/xs]`, its right side read (`armAt`, kernel) as the value or as nothing.

  - `SortLabel` (`f2-examples/sortlabel.kompile.kore`, e2-sort-label, the default configuration
    `<k> $PGM:K </k>`): `initKCell(Init) = <k>(kseq(project:KItem(kseq(Map:lookup(Init, $PGM),
    dotk)), dotk))`, `project:KItem` registry-numbered; at the map `$PGM ↦ foo()` (`w1`) and at the
    empty map (`w0`, no value).
  - `Vars` (`f2-examples/e3-vars.kompile.kore`, `<k> $PGM:Exp </k> <n> $N:Int </n>`): `initNCell`'s
    right side applies the registry-numbered `project:Int`, `initKCell`'s the unnumbered
    `project:Exp`.
  - `Fresh` (`f2-examples/freshcfg.kompile.kore`, e7-freshconfig): `initIdCell(Init,
    #Configuration) = <id>(0)`, an initializer of two arguments whose right side is total. The
    text holds no `functional` axiom of it; `initFunctionalOK` takes one (at the `functional`
    symbols `[initIdCell]`), and its instance `∃y:IdCell. y = initIdCell(ws)` holds at all values
    `ws` of a sort.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Parse KCore.GenEqs

namespace GenEqsInitArm

theorem srt {o : Option Srt} (h : o.isSome = true) : o = some (o.get h) := (Option.some_get h).symm

def N : Names := { sorts := [], syms := [] }

def key : GroundTerm := .inj Srt.kconfigVar Srt.kitem (.dv Srt.kconfigVar (.tok "$PGM"))
def w0 : GroundTerm := .map Srt.map []
def zero : GroundTerm := .dv Srt.int (.int 0)
def dotK : GroundTerm := .ctor dotk []

def initK : String := "LblinitKCell"
def initN : String := "LblinitNCell"
def initTop : String := "LblinitGeneratedTopCell"
def initCtr : String := "LblinitGeneratedCounterCell"
def initId : String := "LblinitIdCell"
def getter : String := "LblgetGeneratedCounterCell"
def projKItem : String := "Lblproject'Coln'KItem"
def projExp : String := "Lblproject'Coln'Exp"
def projInt : String := "Lblproject'Coln'Int"

def ctrV : GroundTerm := .ctor counterLabel [zero]
def one : GroundTerm := .dv Srt.int (.int 1)

/-- The symbol named `f` applied to `ps`, as the translation writes an application. -/
def app (f : String) (ps : List KoreAML.P) : KoreAML.P := KoreAML.appList (symP f) ps

theorem sorted1 {c : Semantics} {w : GroundTerm} (h : (c.sortOf w).isSome = true) : ∀ x ∈ [w], ∃ s, c.sortOf x = some s :=
  fun x hx => by rw [List.mem_singleton.mp hx]; exact ⟨_, (Option.some_get h).symm⟩

theorem sorted2 {c : Semantics} {w v : GroundTerm} (h : (c.sortOf w).isSome = true) (h' : (c.sortOf v).isSome = true) :
    ∀ x ∈ [w, v], ∃ s, c.sortOf x = some s := fun x hx => by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ⟨_, (Option.some_get h).symm⟩
  · rw [List.mem_singleton.mp hx]; exact ⟨_, (Option.some_get h').symm⟩

theorem sortOf_some {c : Semantics} {w : GroundTerm} (h : (c.sortOf w).isSome = true) : ∃ s, c.sortOf w = some s :=
  ⟨_, (Option.some_get h).symm⟩

/-- **The text's equation of `L` at the values `ws` holds in `I`, and `G` there is `r`**: the
equation `e` the text has for `L`, its patterns the distinct variables `xs`, and
`L(ws) = rhs[ws/xs]` (both sides translated with the variables replaced by the values' KORE
terms). -/
def TextEqn (c : Semantics) (eqs : List RawEqn) (G : String → List GroundTerm → Option GroundTerm)
    (I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem) (L : String) (ws : List GroundTerm) (r : Option GroundTerm) :
    Prop :=
  ∃ e xs, eqs.find? (·.fn == L) = some e ∧ distinctEVars? e.pats = some xs ∧ G L ws = r ∧
    (I ⊧ᴵ (KoreAML.den (armSubst c (armZip xs ws) (armLhs e)) ≡ KoreAML.den (armSubst c (armZip xs ws) e.rhs)))

namespace SortLabel

definition_of defn from "f2-examples/sortlabel.kompile.kore"
user_axioms U from "f2-examples/sortlabel.kompile.kore" module "E2-SORT-LABEL"

noncomputable abbrev c : Semantics := defn.sem

theorem coreOK : c.coreOK = true := by decide_cheap

theorem fns_nil : c.fns = [] := by decide +kernel
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem noWitness : ∀ r ∈ c.rules, r.needsWitness c = false := by decide +kernel

theorem fnHyp : FnHyp c :=
  have hn : ∀ fn, fn ∈ c.fns → False := fun fn hfn => by rw [fns_nil] at hfn; cases hfn
  ⟨fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim,
    fun fn hfn => (hn fn hfn).elim,
    openDecided_of_plain noWitness (fun fn hfn => (hn fn hfn).elim),
    openLaws_of_plain noRaw⟩

/-- The text's equations: the user module's axioms the reader reads as equations. -/
noncomputable def eqs : List RawEqn := U.all.filterMap (rawEqn? ·.ax)
/-- The presentation's cell tree. -/
noncomputable def cells : List Cell := Cell.all defn.pres.topCell
/-- The tree's initializers, bottom up. -/
noncomputable def order : List String := (cells.map (·.initLabel c)).reverse
noncomputable def names : List String := order ++ [getter, projKItem]

theorem order_eq : order = [initCtr, initK, initTop] := by decide +kernel

/-- No premise of the theory names the registry's `project:KItem` (decided). -/
theorem proj_free : freeB c [projectSym Srt.kitem] = true := by
  rw [freeB, DetachedB.listsB, DetachedB.valuesB, DetachedB.graphsB]; decide_cheap 40

theorem proj_eqn : (eqs.find? fun e => e.fn == projKItem && predProjOK? N "" eqs c e == some true).isSome = true := by
  decide +kernel
theorem proj_idx : regSymNames.idxOf? projKItem = some (projectSym Srt.kitem) := by decide +kernel

theorem proj_ok : armNameB N "" eqs c projKItem = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp proj_eqn
  have hp := List.find?_some he
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨hfn, hok⟩ := hp
  rw [← hfn]
  exact armNameB_of_proj (List.mem_of_find?_eq_some he) (by rw [hfn]; decide) hok (by rw [hfn]; exact proj_idx) proj_free

/-- **The names are free of the theory**: the initializers and the getter are no symbol of the
semantics, and `project:KItem`, registry-numbered, has an equation `predProjAcc` accepts. -/
theorem names_ok : names.all (armNameB N "" eqs c) = true := by
  rw [names, order_eq]
  simp only [List.cons_append, List.nil_append, List.all_cons, List.all_nil, proj_ok, Bool.and_true]
  decide +kernel

theorem rank : armRankB order eqs = true := by decide +kernel
theorem hord : order.all names.contains = true := by decide +kernel

/-- **The arm takes each initializer's equation.** -/
theorem accepted : armAccB N "" eqs c cells initK = true ∧ armAccB N "" eqs c cells initTop = true ∧
    armAccB N "" eqs c cells initCtr = true := by decide +kernel

theorem arities : armAr eqs initK = 1 ∧ armAr eqs initTop = 1 ∧ armAr eqs initCtr = 0 ∧ armAr eqs getter = 1 := by
  decide +kernel

noncomputable abbrev G : String → List GroundTerm → Option GroundTerm := armGOf c eqs names order (armBase c eqs)

noncomputable def symN (n : String) : Sym := nRegSyms + c.symNames.idxOf n
noncomputable def fooS : Srt := nRegSorts + c.sortNames.idxOf "Foo"
noncomputable def pgm : GroundTerm := .inj fooS Srt.kitem (.ctor (symN "Lblfoo") [])
/-- The map `$PGM ↦ foo()`. -/
noncomputable def w1 : GroundTerm := .map Srt.map [(key, pgm)]
noncomputable def kV : GroundTerm := .ctor (symN "Lbl'-LT-'k'-GT-'") [.ctor kseq [pgm, dotK]]
/-- The initial configuration at `w1`. -/
noncomputable def topV : GroundTerm := .ctor topLabel [kV, ctrV]

theorem sorts : (c.sortOf w1).isSome ∧ (c.sortOf w0).isSome ∧ (c.sortOf topV).isSome ∧ (c.sortOf ctrV).isSome := by
  decide +kernel

/-- **The right sides, read**: `initKCell` at `w1` is `<k>(kseq(inj{Foo,KItem}(foo()), dotk))`
(`project:KItem` of the item `Map:lookup` gives), `initGeneratedTopCell` the initial
configuration; at the empty map `Map:lookup` has no value, nor has either right side. -/
theorem reads : armAt c eqs names order (armBase c eqs) initK [w1] = some (some kV) ∧
    armAt c eqs names order (armBase c eqs) initTop [w1] = some (some topV) ∧
    armAt c eqs names order (armBase c eqs) initCtr [] = some (some ctrV) ∧
    armAt c eqs names order (armBase c eqs) initK [w0] = some none ∧
    armAt c eqs names order (armBase c eqs) initTop [w0] = some none ∧
    G getter [topV] = some ctrV := by
  decide +kernel

theorem in_order : order.contains initK = true ∧ order.contains initTop = true ∧ order.contains initCtr = true ∧
    names.contains getter = true ∧ names.contains initTop = true := by decide +kernel

/-- **One model of the theory, whose steps are the semantics', holds the text's initializer
equations at values**, `G` read from them: `initKCell` and `initGeneratedTopCell` at `w1` with
their values and at the empty map with none, the counter's constant; the initial configuration and
the getter at it. -/
theorem eqns :
    ∃ I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem, (I ⊧ᴵP (Faithful.Γc c ∪ Faithful.Γstep c)) ∧
      TextEqn c eqs G I initK [w1] (some kV) ∧ TextEqn c eqs G I initTop [w1] (some topV) ∧
      TextEqn c eqs G I initCtr [] (some ctrV) ∧
      TextEqn c eqs G I initK [w0] none ∧ TextEqn c eqs G I initTop [w0] none ∧
      (I ⊧ᴵ (app initTop [den c w1] ≡ den c topV)) ∧ (I ⊧ᴵ (app getter [den c topV] ≡ den c ctrV)) ∧
      (I ⊧ᴵ (app initTop [den c w0] ≡ ⊥)) ∧
      ∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  obtain ⟨I, hM, hstep⟩ := model_of_arm c coreOK fnHyp N "" eqs names order (armBase c eqs) names_ok
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := reads
  obtain ⟨a1, a2, a3⟩ := accepted
  obtain ⟨o1, o2, o3, o4, o5⟩ := in_order
  obtain ⟨ar1, ar2, ar3, ar4⟩ := arities
  obtain ⟨h1, h0, htop, hctr⟩ := sorts
  have e2 := init_arm_at hM rank hord a2 o2 (ws := [w1]) ar2.symm (sorted1 h1) r2
  have e5 := init_arm_at hM rank hord a2 o2 (ws := [w0]) ar2.symm (sorted1 h0) r5
  have ⟨_, _, _, _, hg2, _⟩ := e2
  have ⟨_, _, _, _, hg5, _⟩ := e5
  obtain ⟨st, hst⟩ := sortOf_some htop
  obtain ⟨sc, hsc⟩ := sortOf_some hctr
  exact ⟨I, hM.sat, init_arm_at hM rank hord a1 o1 (ws := [w1]) ar1.symm (sorted1 h1) r1, e2,
    init_arm_at hM rank hord a3 o3 (ws := []) ar3.symm (fun _ h => by cases h) r3,
    init_arm_at hM rank hord a1 o1 (ws := [w0]) ar1.symm (sorted1 h0) r4, e5,
    arm_name_eqn hM o5 (ws := [w1]) ar2.symm (sorted1 h1) hg2 hst,
    arm_name_eqn hM o4 (ws := [topV]) ar4.symm (sorted1 htop) r6 hsc,
    arm_name_none hM o5 (ws := [w0]) ar2.symm (sorted1 h0) hg5, hstep⟩

end SortLabel

namespace Vars

definition_of defn from "f2-examples/e3-vars.kompile.kore"
user_axioms U from "f2-examples/e3-vars.kompile.kore" module "E3-VARS"

noncomputable abbrev c : Semantics := defn.sem

theorem coreOK : c.coreOK = true := by decide_cheap

theorem fns_nil : c.fns = [] := by decide +kernel
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem noWitness : ∀ r ∈ c.rules, r.needsWitness c = false := by decide +kernel

theorem fnHyp : FnHyp c :=
  have hn : ∀ fn, fn ∈ c.fns → False := fun fn hfn => by rw [fns_nil] at hfn; cases hfn
  ⟨fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim,
    fun fn hfn => (hn fn hfn).elim,
    openDecided_of_plain noWitness (fun fn hfn => (hn fn hfn).elim),
    openLaws_of_plain noRaw⟩

noncomputable def eqs : List RawEqn := U.all.filterMap (rawEqn? ·.ax)
noncomputable def cells : List Cell := Cell.all defn.pres.topCell
noncomputable def order : List String := (cells.map (·.initLabel c)).reverse
noncomputable def names : List String := order ++ [getter, projExp, projInt]

theorem order_eq : order = [initCtr, initN, initK, initTop] := by decide +kernel

/-- No premise of the theory names the registry's `project:Int` (decided). -/
theorem proj_free : freeB c [projectSym Srt.int] = true := by
  rw [freeB, DetachedB.listsB, DetachedB.valuesB, DetachedB.graphsB]; decide_cheap 40

theorem proj_eqn : (eqs.find? fun e => e.fn == projInt && predProjOK? N "" eqs c e == some true).isSome = true := by
  decide +kernel
theorem proj_idx : regSymNames.idxOf? projInt = some (projectSym Srt.int) := by decide +kernel

theorem proj_ok : armNameB N "" eqs c projInt = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp proj_eqn
  have hp := List.find?_some he
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨hfn, hok⟩ := hp
  rw [← hfn]
  exact armNameB_of_proj (List.mem_of_find?_eq_some he) (by rw [hfn]; decide) hok (by rw [hfn]; exact proj_idx) proj_free

/-- **The names are free of the theory**: `project:Int`, registry-numbered, through `predProjAcc`;
`project:Exp` and the initializers are no symbol of the semantics. -/
theorem names_ok : names.all (armNameB N "" eqs c) = true := by
  rw [names, order_eq]
  simp only [List.cons_append, List.nil_append, List.all_cons, List.all_nil, proj_ok, Bool.and_true]
  decide +kernel

theorem rank : armRankB order eqs = true := by decide +kernel
theorem hord : order.all names.contains = true := by decide +kernel

theorem accepted : armAccB N "" eqs c cells initN = true ∧ armAccB N "" eqs c cells initK = true ∧
    armAccB N "" eqs c cells initTop = true := by decide +kernel

theorem arities : armAr eqs initN = 1 ∧ armAr eqs initK = 1 ∧ armAr eqs initTop = 1 := by decide +kernel

noncomputable abbrev G : String → List GroundTerm → Option GroundTerm := armGOf c eqs names order (armBase c eqs)

noncomputable def symN (n : String) : Sym := nRegSyms + c.symNames.idxOf n
noncomputable def expS : Srt := nRegSorts + c.sortNames.idxOf "Exp"
def keyN : GroundTerm := .inj Srt.kconfigVar Srt.kitem (.dv Srt.kconfigVar (.tok "$N"))
noncomputable def pgm : GroundTerm := .inj expS Srt.kitem (.ctor (symN "Lblb") [])
def five : GroundTerm := .dv Srt.int (.int 5)
/-- The map `$N ↦ 5, $PGM ↦ b()`. -/
noncomputable def w1 : GroundTerm := .map Srt.map [(keyN, .inj Srt.int Srt.kitem five), (key, pgm)]
noncomputable def kV : GroundTerm := .ctor (symN "Lbl'-LT-'k'-GT-'") [.ctor kseq [pgm, dotK]]
noncomputable def nV : GroundTerm := .ctor (symN "Lbl'-LT-'n'-GT-'") [five]
noncomputable def topV : GroundTerm := .ctor topLabel [kV, nV, ctrV]

theorem sorts : (c.sortOf w1).isSome ∧ (c.sortOf w0).isSome ∧ (c.sortOf topV).isSome := by decide +kernel

/-- **The right sides, read**: `initNCell` at `w1` is `<n>(5)` (`project:Int` of the item
`Map:lookup` gives at `$N`), `initKCell` `<k>(kseq(inj{Exp,KItem}(b()), dotk))`,
`initGeneratedTopCell` the initial configuration; at the empty map `initNCell` has no value. -/
theorem reads : armAt c eqs names order (armBase c eqs) initN [w1] = some (some nV) ∧
    armAt c eqs names order (armBase c eqs) initK [w1] = some (some kV) ∧
    armAt c eqs names order (armBase c eqs) initTop [w1] = some (some topV) ∧
    armAt c eqs names order (armBase c eqs) initN [w0] = some none := by
  decide +kernel

theorem in_order : order.contains initN = true ∧ order.contains initK = true ∧ order.contains initTop = true ∧
    names.contains initTop = true := by decide +kernel

/-- **One model of the theory, whose steps are the semantics', holds the text's initializer
equations at values**, `G` read from them, among them `initNCell`'s, whose right side applies the
registry-numbered `project:Int`: at `w1` with their values, and `initNCell` at the empty map with
none; the initial configuration. -/
theorem eqns :
    ∃ I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem, (I ⊧ᴵP (Faithful.Γc c ∪ Faithful.Γstep c)) ∧
      TextEqn c eqs G I initN [w1] (some nV) ∧ TextEqn c eqs G I initK [w1] (some kV) ∧
      TextEqn c eqs G I initTop [w1] (some topV) ∧ TextEqn c eqs G I initN [w0] none ∧
      (I ⊧ᴵ (app initTop [den c w1] ≡ den c topV)) ∧
      ∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  obtain ⟨I, hM, hstep⟩ := model_of_arm c coreOK fnHyp N "" eqs names order (armBase c eqs) names_ok
  obtain ⟨r1, r2, r3, r4⟩ := reads
  obtain ⟨a1, a2, a3⟩ := accepted
  obtain ⟨o1, o2, o3, o4⟩ := in_order
  obtain ⟨ar1, ar2, ar3⟩ := arities
  obtain ⟨h1, h0, htop⟩ := sorts
  have e3 := init_arm_at hM rank hord a3 o3 (ws := [w1]) ar3.symm (sorted1 h1) r3
  have ⟨_, _, _, _, hg3, _⟩ := e3
  obtain ⟨st, hst⟩ := sortOf_some htop
  exact ⟨I, hM.sat, init_arm_at hM rank hord a1 o1 (ws := [w1]) ar1.symm (sorted1 h1) r1,
    init_arm_at hM rank hord a2 o2 (ws := [w1]) ar2.symm (sorted1 h1) r2, e3,
    init_arm_at hM rank hord a1 o1 (ws := [w0]) ar1.symm (sorted1 h0) r4,
    arm_name_eqn hM o4 (ws := [w1]) ar3.symm (sorted1 h1) hg3 hst, hstep⟩

end Vars

namespace Fresh

definition_of defn from "f2-examples/freshcfg.kompile.kore"
user_axioms U from "f2-examples/freshcfg.kompile.kore" module "E7-FRESHCONFIG"

noncomputable abbrev c : Semantics := defn.sem

theorem coreOK : c.coreOK = true := by decide_cheap

theorem fns_nil : c.fns = [] := by decide +kernel
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem noWitness : ∀ r ∈ c.rules, r.needsWitness c = false := by decide +kernel

theorem fnHyp : FnHyp c :=
  have hn : ∀ fn, fn ∈ c.fns → False := fun fn hfn => by rw [fns_nil] at hfn; cases hfn
  ⟨fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim,
    fun fn hfn => (hn fn hfn).elim,
    openDecided_of_plain noWitness (fun fn hfn => (hn fn hfn).elim),
    openLaws_of_plain noRaw⟩

noncomputable def eqs : List RawEqn := U.all.filterMap (rawEqn? ·.ax)
noncomputable def cells : List Cell := Cell.all defn.pres.topCell
noncomputable def order : List String := (cells.map (·.initLabel c)).reverse
noncomputable def names : List String := order ++ [getter, projExp]

theorem order_eq : order = [initCtr, initId, initK, initTop] := by decide +kernel
theorem names_ok : names.all (armNameB N "" eqs c) = true := by
  rw [names, order_eq]
  decide +kernel
theorem rank : armRankB order eqs = true := by decide +kernel
theorem hord : order.all names.contains = true := by decide +kernel

theorem accepted : armAccB N "" eqs c cells initId = true ∧ armAccB N "" eqs c cells initTop = true := by
  decide +kernel

/-- `initIdCell` and `initGeneratedTopCell` take two arguments, `(Init, #Configuration)`. -/
theorem arities : armAr eqs initId = 2 ∧ armAr eqs initTop = 2 := by decide +kernel

noncomputable abbrev G : String → List GroundTerm → Option GroundTerm := armGOf c eqs names order (armBase c eqs)

noncomputable def symN (n : String) : Sym := nRegSyms + c.symNames.idxOf n
noncomputable def expS : Srt := nRegSorts + c.sortNames.idxOf "Exp"
noncomputable def idS : Srt := nRegSorts + c.sortNames.idxOf "IdCell"
noncomputable def pgm : GroundTerm := .inj expS Srt.kitem (.ctor (symN "Lbla") [])
noncomputable def w1 : GroundTerm := .map Srt.map [(key, pgm)]
noncomputable def kV : GroundTerm := .ctor (symN "Lbl'-LT-'k'-GT-'") [.ctor kseq [pgm, dotK]]
noncomputable def idV : GroundTerm := .ctor (symN "Lbl'-LT-'id'-GT-'") [zero]
/-- The counter's initial value is 1: the configuration holds a fresh variable. -/
def ctr1 : GroundTerm := .ctor counterLabel [one]
/-- The initial configuration at `w1`. -/
noncomputable def topV : GroundTerm := .ctor topLabel [kV, idV, ctr1]

theorem sorts : (c.sortOf w1).isSome ∧ (c.sortOf topV).isSome := by decide +kernel
theorem idSort : c.sortOf idV = some idS ∧ c.sortName idS = "IdCell" := by decide +kernel

/-- **The right sides, read**, at `(w1, t)` for the initial configuration `t`. -/
theorem reads : armAt c eqs names order (armBase c eqs) initId [w1, topV] = some (some idV) ∧
    armAt c eqs names order (armBase c eqs) initTop [w1, topV] = some (some topV) := by
  decide +kernel

theorem in_order : order.contains initId = true ∧ order.contains initTop = true := by decide +kernel

/-- `initFunctionalOK` takes a `functional` axiom of `initIdCell` (were the text to hold one: its
`functional` symbols then include it). -/
theorem idFunctional : (cells.find? (·.initLabel c == initId)).any
    (fun x => initFunctionalOK N "" eqs [initId] c x && x.initLabel c == initId) = true := by decide +kernel

/-- `initIdCell`'s right side holds no variable and is read as `<id>(0)`. -/
theorem idRhs : (match eqs.find? (·.fn == initId) with
    | some e => (armVars e.rhs).isEmpty && decide (armVal c names.contains (armAr eqs) G [] e.rhs = some (some idV))
    | none => false) = true := by decide +kernel

/-- **One model of the theory, whose steps are the semantics', holds the text's initializer
equations at two arguments**, `G` read from them: `initIdCell(w1, t) = <id>(0)` and
`initGeneratedTopCell(w1, t)` the initial configuration `t`; and the instance of a `functional`
axiom of `initIdCell`, `∃y:IdCell. y = initIdCell(ws)`, at all values `ws` of a sort: an
initializer of positive arity whose right side has a value at all of them. -/
theorem eqns :
    ∃ I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem, (I ⊧ᴵP (Faithful.Γc c ∪ Faithful.Γstep c)) ∧
      TextEqn c eqs G I initId [w1, topV] (some idV) ∧ TextEqn c eqs G I initTop [w1, topV] (some topV) ∧
      (∃ e xs, eqs.find? (·.fn == initId) = some e ∧ distinctEVars? e.pats = some xs ∧
        ∀ ws : List GroundTerm, ws.length = 2 → (∀ w ∈ ws, ∃ s, c.sortOf w = some s) → ∀ y : ML.EVar,
          I ⊧ᴵ KoreAML.sExists y (KoreAML.Cons.sortP "IdCell")
            (.evar y ≡ KoreAML.den (armSubst c (armZip xs ws) (armLhs e)))) ∧
      ∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  obtain ⟨I, hM, hstep⟩ := model_of_arm c coreOK fnHyp N "" eqs names order (armBase c eqs) names_ok
  obtain ⟨r1, r2⟩ := reads
  obtain ⟨a1, a2⟩ := accepted
  obtain ⟨o1, o2⟩ := in_order
  obtain ⟨ar1, ar2⟩ := arities
  have sw := sorted2 sorts.1 sorts.2
  have hfx := idFunctional
  cases hx : cells.find? (·.initLabel c == initId) with
  | none => rw [hx] at hfx; cases hfx
  | some x =>
  rw [hx] at hfx
  simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hfx
  obtain ⟨hok, hxL⟩ := hfx
  obtain ⟨e, xs, he, hxs, hall⟩ := init_arm_functional (base := armBase c eqs) hM rank hord hok (hxL ▸ o1)
  rw [hxL] at he
  have hrhs := idRhs
  rw [he] at hrhs
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hrhs
  obtain ⟨hv, hval⟩ := hrhs
  refine ⟨I, hM.sat, init_arm_at hM rank hord a1 o1 (ws := [w1, topV]) ar1.symm sw r1,
    init_arm_at hM rank hord a2 o2 (ws := [w1, topV]) ar2.symm sw r2,
    ⟨e, xs, he, hxs, fun ws hl hws y => ?_⟩, hstep⟩
  have hl' : ws.length = xs.length := by
    rw [hl, ← ar1]; unfold armAr; rw [he]
    show e.pats.length = xs.length
    rw [(armDistinct_spec hxs).1, List.length_map]
  have hr : armVal c names.contains (armAr eqs) G (armZip xs ws) e.rhs = some (some idV) := by
    rw [armVal_congr c _ _ e.rhs (G' := G) (σ' := []) (fun _ _ => rfl) (fun z hz => by rw [hv] at hz; cases hz)]
    exact hval
  have := hall ws hl' hws idV idS hr idSort.1 y
  rwa [idSort.2] at this

end Fresh

/-- info: 'GenEqsInitArm.SortLabel.eqns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortLabel.eqns
/-- info: 'GenEqsInitArm.Vars.eqns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Vars.eqns
/-- info: 'GenEqsInitArm.Fresh.eqns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fresh.eqns
/-- info: 'KCore.GenEqs.init_arm_eqn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms init_arm_eqn
/-- info: 'KCore.GenEqs.init_arm_functional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms init_arm_functional
/-- info: 'KCore.GenEqs.model_with_inits_arm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms model_with_inits_arm

end GenEqsInitArm
