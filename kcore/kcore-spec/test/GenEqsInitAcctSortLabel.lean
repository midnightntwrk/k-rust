/-
  The cell tree's initializers through the account's arm (`KcoreSpec/GenEqsInitArm.lean`), on
  `f2-examples/sortlabel.kompile.kore`, with the account's own scan and names.
  Run from the package root: `lake env lean -j1 test/GenEqsInitAcctSortLabel.lean`.

  The text is the construct fixture e2-sort-label, the default configuration `<k> $PGM:K </k>`,
  by K 7.1.337's kompile. Its initializers: the constant `initGeneratedCounterCell()`;
  `initKCell(Init) = <k>(kseq(project:KItem(kseq(Map:lookup(Init, $PGM), dotk)), dotk))`, whose
  `project:KItem` the registry numbers; `initGeneratedTopCell(Init)`, whose right side applies
  `initKCell` and `initGeneratedCounterCell`.

  What the account reads, here as it reads it (`consumedWith`, `Account.lean`): the user module `m`
  is the text's last; its scan is `S = scan m.sentences`; its names are `E` with
  `envOf m S = .ok E`; an initializer's equation is taken by `initEqnOK E.N E.src S.eqs c x e`, its
  `functional` axiom by `initFunctionalOK E.N E.src S.eqs (functionalSyms S.events) c x`. The scan
  and the names are computed by compiled code (`parse_stages`) and checked by the kernel: the scan
  block by block (`scan_eq`, `ScanIs`), the names from it (`env_eq`).

  Nothing here writes a right side or a `G` by hand. The tree is the presentation's (`Cell.all`,
  bottom up); the arm takes each initializer's equation (`armAccB`, `initEqnOK` at the tree's cell);
  `G` is read from `S.eqs` (`GenEqs.armG`), `project:KItem` and the getter by `GenEqs.armBase`; the
  names are checked by `armNameB` at `E.N`, `E.src` and `S.eqs`: the initializers and the getter
  are no symbol of the semantics, and `project:KItem` has an equation in `S.eqs` that `predProjAcc`
  accepts. The model is `GenEqs.model_of_arm`; each equation at values is `GenEqs.init_arm_at`, the
  text's equation `L(ws) = rhs[ws/xs]` with its right side read (`armAt`, kernel) as a value or as
  nothing; the counter's `functional` axiom, which the text holds and `initFunctionalOK` takes at the
  text's `functional` symbols, is `GenEqs.init_arm_functional`.

  `eqns`: one model of the theory whose steps are the semantics' holds
  - the counter's equation and its `functional` axiom;
  - at the map `$PGM ↦ foo()` (`w1`), the equations of `initKCell` and `initGeneratedTopCell`,
    whose value is the initial configuration `<generatedTop>(<k>(foo()), <generatedCounter>(0))`,
    and the getter there;
  - at the empty map (`w0`), where `Map:lookup(Init, $PGM)` has no value, both equations with both
    sides denoting nothing, and `initGeneratedTopCell(.Map) = ⊥`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Parse KCore.GenEqs

namespace GenEqsInitAcctSortLabel

def key : GroundTerm := .inj Srt.kconfigVar Srt.kitem (.dv Srt.kconfigVar (.tok "$PGM"))
def w0 : GroundTerm := .map Srt.map []
def zero : GroundTerm := .dv Srt.int (.int 0)
def dotK : GroundTerm := .ctor dotk []
def ctrV : GroundTerm := .ctor counterLabel [zero]

def initK : String := "LblinitKCell"
def initTop : String := "LblinitGeneratedTopCell"
def initCtr : String := "LblinitGeneratedCounterCell"
def getter : String := "LblgetGeneratedCounterCell"
def projKItem : String := "Lblproject'Coln'KItem"

/-- The symbol named `f` applied to `ps`, as the translation writes an application. -/
def app (f : String) (ps : List KoreAML.P) : KoreAML.P := KoreAML.appList (symP f) ps

theorem sortOf_some {c : Semantics} {w : GroundTerm} (h : (c.sortOf w).isSome = true) : ∃ s, c.sortOf w = some s :=
  ⟨_, (Option.some_get h).symm⟩

theorem sorted1 {c : Semantics} {w : GroundTerm} (h : (c.sortOf w).isSome = true) : ∀ x ∈ [w], ∃ s, c.sortOf x = some s :=
  fun x hx => by rw [List.mem_singleton.mp hx]; exact sortOf_some h

theorem sorted0 {c : Semantics} : ∀ x ∈ ([] : List GroundTerm), ∃ s, c.sortOf x = some s := fun _ h => by cases h

/-- **The text's equation of `L` at the values `ws` holds in `I`, and `G` there is `r`**: the
equation `e` the text has for `L`, its patterns the distinct variables `xs`, and
`L(ws) = rhs[ws/xs]` (both sides translated with the variables replaced by the values' KORE
terms). -/
def TextEqn (c : Semantics) (eqs : List RawEqn) (G : String → List GroundTerm → Option GroundTerm)
    (I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem) (L : String) (ws : List GroundTerm) (r : Option GroundTerm) :
    Prop :=
  ∃ e xs, eqs.find? (·.fn == L) = some e ∧ distinctEVars? e.pats = some xs ∧ G L ws = r ∧
    (I ⊧ᴵ (KoreAML.den (armSubst c (armZip xs ws) (armLhs e)) ≡ KoreAML.den (armSubst c (armZip xs ws) e.rhs)))

/-- **The `functional` axiom of a constant initializer `L` that the arm takes holds**: where
`initFunctionalOK` takes it for the tree's cell of `L` and the right side is read as the value `v`
of sort `s`, `∃y:s. y = L()`. -/
theorem functional_const {c : Semantics} {Nm : Names} {msrc : String} {eqs : List RawEqn} {names order : List String}
    {base : String → List GroundTerm → Option GroundTerm} {I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem}
    (hM : InitModel c (fun n => names.contains n = true) (armAr eqs) (armGOf c eqs names order base) I)
    (hR : armRankB order eqs = true) (hord : order.all names.contains = true) {funcs : List String}
    {cells : List Cell} {L : String}
    (hok : (cells.find? (·.initLabel c == L)).any (fun x => initFunctionalOK Nm msrc eqs funcs c x && x.initLabel c == L) = true)
    (hL : order.contains L = true) (har : armAr eqs L = 0) {v : GroundTerm} {s : Srt}
    (hr : armAt c eqs names order base L [] = some (some v)) (hs : c.sortOf v = some s) (y : ML.EVar) :
    I ⊧ᴵ KoreAML.sExists y (KoreAML.Cons.sortP (c.sortName s)) (.evar y ≡ app L []) := by
  cases hx : cells.find? (·.initLabel c == L) with
  | none => rw [hx] at hok; cases hok
  | some x =>
    rw [hx] at hok
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨hok, hxL⟩ := hok
    obtain ⟨e, xs, he, hxs, hall⟩ := init_arm_functional (base := base) hM hR hord hok (hxL ▸ hL)
    rw [hxL] at he
    have hxl : xs = [] := by
      unfold armAr at har; rw [he] at har
      have : e.pats.length = 0 := har
      rw [(armDistinct_spec hxs).1, List.length_map] at this
      exact List.eq_nil_of_length_eq_zero this
    subst hxl
    have hr' : armVal c names.contains (armAr eqs) (armGOf c eqs names order base) (armZip [] []) e.rhs = some (some v) := by
      unfold armAt at hr; rw [he] at hr; dsimp only at hr; rw [hxs] at hr; exact hr
    have h := hall [] rfl sorted0 v s hr' hs y
    rw [armLhs_den c hxs rfl] at h
    have hfn : e.fn = L := by have := List.find?_some he; exact beq_iff_eq.mp this
    rw [hfn] at h
    exact h

/-! ## The text, its scan and its names, as the account reads them -/

kore_term kore from "f2-examples/sortlabel.kompile.kore" cut [59, 118, 177]
parse_stages stage from "f2-examples/sortlabel.kompile.kore" cut [59, 118, 177] scan_blocks [1, 1, 1, 1]
  prod_blocks [] rule_blocks [] event_blocks [] clause_blocks []
definition_of defn from "f2-examples/sortlabel.kompile.kore"

/-- The user module: the text's last. -/
noncomputable abbrev m : Kore.Module := kore.modules.getLastD default
/-- The account's scan of the user module. -/
noncomputable abbrev S : Scan := scan m.sentences
/-- The names `envOf` gives (computed; `env_eq` checks them). -/
noncomputable abbrev E : Env := stage.env

theorem last_eq : kore.modules.getLast? = some m := by kernel_rfl

theorem scan0 : ScanIs kore.segs 0 1 stage.scan0 := by unfold ScanIs; kernel_rfl
theorem scan1 : ScanIs kore.segs 1 1 stage.scan1 := by unfold ScanIs; kernel_rfl
theorem scan2 : ScanIs kore.segs 2 1 stage.scan2 := by unfold ScanIs; kernel_rfl
theorem scan3 : ScanIs kore.segs 3 1 stage.scan3 := by unfold ScanIs; kernel_rfl

/-- The blocks' scans, appended. -/
noncomputable def scanAll : Scan := ((stage.scan0.append stage.scan1).append stage.scan2).append stage.scan3

/-- **The account's scan of the user module**, block by block. -/
theorem scan_eq : S = scanAll :=
  ScanIs.all (n := 4) rfl (((scan0.join scan1 rfl).join scan2 rfl).join scan3 rfl)

/-- **The names the account reads the user module with.** -/
theorem env_eq : envOf m S = .ok E := by
  show envOf m S = .ok stage.env
  rw [scan_eq]; kernel_rfl

/-- The text's equations, as the account's scan gives them. -/
noncomputable def eqs : List RawEqn := scanAll.eqs
/-- The symbols of the text's `functional` axioms, as the account's scan gives them. -/
noncomputable def funcs : List String := functionalSyms scanAll.events

theorem eqs_eq : S.eqs = eqs := by rw [scan_eq]; rfl
theorem funcs_eq : functionalSyms S.events = funcs := by rw [scan_eq]; rfl

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

/-! ## The arm on the tree -/

/-- The presentation's cell tree. -/
noncomputable def cells : List Cell := Cell.all defn.pres.topCell
/-- The tree's initializers, bottom up. -/
noncomputable def order : List String := (cells.map (·.initLabel c)).reverse
noncomputable def names : List String := order ++ [getter, projKItem]

theorem order_eq : order = [initCtr, initK, initTop] := by decide +kernel

/-- No premise of the theory names the registry's `project:KItem` (decided). -/
theorem proj_free : freeB c [projectSym Srt.kitem] = true := by
  rw [freeB, DetachedB.listsB, DetachedB.valuesB, DetachedB.graphsB]; decide_cheap 40

theorem proj_eqn : (eqs.find? fun e => e.fn == projKItem && predProjOK? E.N E.src eqs c e == some true).isSome = true := by
  decide +kernel
theorem proj_idx : regSymNames.idxOf? projKItem = some (projectSym Srt.kitem) := by decide +kernel

theorem proj_ok : armNameB E.N E.src eqs c projKItem = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp proj_eqn
  have hp := List.find?_some he
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨hfn, hok⟩ := hp
  rw [← hfn]
  exact armNameB_of_proj (List.mem_of_find?_eq_some he) (by rw [hfn]; decide) hok (by rw [hfn]; exact proj_idx) proj_free

/-- **The names are free of the theory**: the initializers and the getter are no symbol of the
semantics, and `project:KItem`, registry-numbered, has an equation `predProjAcc` accepts. -/
theorem names_ok : names.all (armNameB E.N E.src eqs c) = true := by
  rw [names, order_eq]
  simp only [List.cons_append, List.nil_append, List.all_cons, List.all_nil, proj_ok, Bool.and_true]
  decide +kernel

theorem rank : armRankB order eqs = true := by decide +kernel
theorem hord : order.all names.contains = true := by decide +kernel

/-- **The arm takes each initializer's equation**, `initEqnOK E.N E.src S.eqs` at the tree's cell. -/
theorem accepted : armAccB E.N E.src eqs c cells initK = true ∧ armAccB E.N E.src eqs c cells initTop = true ∧
    armAccB E.N E.src eqs c cells initCtr = true := by decide +kernel

/-- **The arm takes the counter's `functional` axiom**, `initFunctionalOK E.N E.src S.eqs
(functionalSyms S.events)`; the text holds it (`initGeneratedCounterCell` is among its `functional`
symbols). -/
theorem functionals : funcs.contains initCtr = true ∧
    (cells.find? (·.initLabel c == initCtr)).any
      (fun x => initFunctionalOK E.N E.src eqs funcs c x && x.initLabel c == initCtr) = true := by
  decide +kernel

theorem arities : armAr eqs initK = 1 ∧ armAr eqs initTop = 1 ∧ armAr eqs initCtr = 0 ∧ armAr eqs getter = 1 := by
  decide +kernel

theorem in_order : order.contains initK = true ∧ order.contains initTop = true ∧ order.contains initCtr = true ∧
    names.contains getter = true ∧ names.contains initTop = true := by decide +kernel

noncomputable abbrev G : String → List GroundTerm → Option GroundTerm := armGOf c eqs names order (armBase c eqs)

noncomputable def symN (n : String) : Sym := nRegSyms + c.symNames.idxOf n
noncomputable def fooS : Srt := nRegSorts + c.sortNames.idxOf "Foo"
/-- The counter cell's sort, a registry sort. -/
def ctrS : Srt := Srt.counter
noncomputable def pgm : GroundTerm := .inj fooS Srt.kitem (.ctor (symN "Lblfoo") [])
/-- The map `$PGM ↦ foo()`. -/
noncomputable def w1 : GroundTerm := .map Srt.map [(key, pgm)]
noncomputable def kV : GroundTerm := .ctor (symN "Lbl'-LT-'k'-GT-'") [.ctor kseq [pgm, dotK]]
/-- The initial configuration at `w1`. -/
noncomputable def topV : GroundTerm := .ctor topLabel [kV, ctrV]

theorem sorts : (c.sortOf w1).isSome ∧ (c.sortOf w0).isSome ∧ (c.sortOf topV).isSome ∧
    c.sortOf ctrV = some ctrS ∧ c.sortName ctrS = "GeneratedCounterCell" := by
  decide +kernel

/-- **The right sides, read**: `initKCell` at `w1` is `<k>(kseq(inj{Foo,KItem}(foo()), dotk))`
(`project:KItem` of the item `Map:lookup` gives), `initGeneratedTopCell` the initial
configuration, the counter `<generatedCounter>(0)`, the getter at the initial configuration the
counter; at the empty map `Map:lookup` has no value, nor has either right side. -/
theorem reads : armAt c eqs names order (armBase c eqs) initK [w1] = some (some kV) ∧
    armAt c eqs names order (armBase c eqs) initTop [w1] = some (some topV) ∧
    armAt c eqs names order (armBase c eqs) initCtr [] = some (some ctrV) ∧
    armAt c eqs names order (armBase c eqs) initK [w0] = some none ∧
    armAt c eqs names order (armBase c eqs) initTop [w0] = some none ∧
    G getter [topV] = some ctrV := by
  decide +kernel

/-- **One model of the theory, whose steps are the semantics', holds the text's initializer
equations at values**, read as the account reads the text (its scan `S`, its names `E`) and `G`
read from them: the counter's equation and its `functional` axiom; `initKCell` and
`initGeneratedTopCell` at `w1` with their values and at the empty map with none; the initial
configuration, the getter at it, and `initGeneratedTopCell(.Map) = ⊥`. -/
theorem eqns :
    kore.modules.getLast? = some m ∧ envOf m S = .ok E ∧ S.eqs = eqs ∧ functionalSyms S.events = funcs ∧
    ∃ I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem, (I ⊧ᴵP (Faithful.Γc c ∪ Faithful.Γstep c)) ∧
      TextEqn c eqs G I initCtr [] (some ctrV) ∧
      (I ⊧ᴵ KoreAML.sExists ⟨1⟩ (KoreAML.Cons.sortP "GeneratedCounterCell") (.evar ⟨1⟩ ≡ app initCtr [])) ∧
      TextEqn c eqs G I initK [w1] (some kV) ∧ TextEqn c eqs G I initTop [w1] (some topV) ∧
      TextEqn c eqs G I initK [w0] none ∧ TextEqn c eqs G I initTop [w0] none ∧
      (I ⊧ᴵ (app initTop [den c w1] ≡ den c topV)) ∧ (I ⊧ᴵ (app getter [den c topV] ≡ den c ctrV)) ∧
      (I ⊧ᴵ (app initTop [den c w0] ≡ ⊥)) ∧
      ∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  obtain ⟨I, hM, hstep⟩ := model_of_arm c coreOK fnHyp E.N E.src eqs names order (armBase c eqs) names_ok
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := reads
  obtain ⟨a1, a2, a3⟩ := accepted
  obtain ⟨o1, o2, o3, o4, o5⟩ := in_order
  obtain ⟨ar1, ar2, ar3, ar4⟩ := arities
  obtain ⟨-, f1⟩ := functionals
  obtain ⟨h1, h0, htop, hctr, nCtr⟩ := sorts
  have e2 := init_arm_at hM rank hord a2 o2 (ws := [w1]) ar2.symm (sorted1 h1) r2
  have e5 := init_arm_at hM rank hord a2 o2 (ws := [w0]) ar2.symm (sorted1 h0) r5
  have ⟨_, _, _, _, hg2, _⟩ := e2
  have ⟨_, _, _, _, hg5, _⟩ := e5
  obtain ⟨st, hst⟩ := sortOf_some htop
  have fCtr := functional_const hM rank hord f1 o3 ar3 r3 hctr ⟨1⟩
  rw [nCtr] at fCtr
  exact ⟨last_eq, env_eq, eqs_eq, funcs_eq, I, hM.sat,
    init_arm_at hM rank hord a3 o3 (ws := []) ar3.symm sorted0 r3, fCtr,
    init_arm_at hM rank hord a1 o1 (ws := [w1]) ar1.symm (sorted1 h1) r1, e2,
    init_arm_at hM rank hord a1 o1 (ws := [w0]) ar1.symm (sorted1 h0) r4, e5,
    arm_name_eqn hM o5 (ws := [w1]) ar2.symm (sorted1 h1) hg2 hst,
    arm_name_eqn hM o4 (ws := [topV]) ar4.symm (sorted1 htop) r6 hctr,
    arm_name_none hM o5 (ws := [w0]) ar2.symm (sorted1 h0) hg5, hstep⟩

/-- info: 'GenEqsInitAcctSortLabel.eqns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eqns

end GenEqsInitAcctSortLabel
