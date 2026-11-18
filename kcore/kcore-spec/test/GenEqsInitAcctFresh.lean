/-
  The cell tree's initializers through the account's arm (`KcoreSpec/GenEqsInitArm.lean`), on
  `f2-examples/freshcfg.kompile.kore`, with the account's own scan and names.
  Run from the package root: `lake env lean -j1 test/GenEqsInitAcctFresh.lean`.

  The text is the construct fixture e7-freshconfig, `configuration <k> $PGM:Exp </k>
  <id> !N:Int </id>`, by K 7.1.337's kompile. The fresh variable gives `initIdCell` and
  `initGeneratedTopCell` the arguments `(Init, #Configuration)`, and the counter the initial value
  1: `initGeneratedCounterCell() = <generatedCounter>(1)`, `initIdCell(Init, #Configuration) =
  <id>(0)`, an initializer of two arguments whose right side is total.

  What the account reads, here as it reads it (`consumedWith`, `Account.lean`): the user module `m`
  is the text's last; its scan is `S = scan m.sentences`; its names are `E` with
  `envOf m S = .ok E`; an initializer's equation is taken by `initEqnOK E.N E.src S.eqs c x e`, its
  `functional` axiom by `initFunctionalOK E.N E.src S.eqs (functionalSyms S.events) c x`. The scan
  and the names are computed by compiled code (`parse_stages`) and checked by the kernel: the scan
  block by block (`scan_eq`, `ScanIs`), the names from it (`env_eq`).

  Nothing here writes a right side or a `G` by hand. The tree is the presentation's (`Cell.all`,
  bottom up); the arm takes each initializer's equation (`armAccB`); `G` is read from `S.eqs`
  (`GenEqs.armG`), `project:Exp` and the getter by `GenEqs.armBase`; the names are checked by
  `armNameB` at `E.N`, `E.src` and `S.eqs`. The model is `GenEqs.model_of_arm`.

  The `functional` axioms. The counter's, which the text holds (`initGeneratedCounterCell` is
  among its `functional` symbols), is taken by `initFunctionalOK` and holds. The text holds no
  `functional` axiom of `initIdCell` (`noIdFunctional`: it is not among the text's `functional`
  symbols, and its symbol declaration is `function` only); no kompiled text here declares an
  initializer of positive arity `functional` or `total`. The axiom `∃y:IdCell. y =
  initIdCell(ws)` is therefore supplied here, not read: `initFunctionalOK` at the text's own
  `functional` symbols takes it for `initIdCell`'s cell (its right side applies only a constructor,
  so no initializer below is consulted), and its instance holds at all values `ws` of a sort.

  `eqns`: one model of the theory whose steps are the semantics' holds the counter's equation and
  its `functional` axiom; `initIdCell(w1, t) = <id>(0)` and `initGeneratedTopCell(w1, t) = t` at
  the map `$PGM ↦ a()` (`w1`) and the initial configuration `t`; and the instance of a `functional`
  axiom of `initIdCell` at all values of a sort.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Parse KCore.GenEqs

namespace GenEqsInitAcctFresh

def key : GroundTerm := .inj Srt.kconfigVar Srt.kitem (.dv Srt.kconfigVar (.tok "$PGM"))
def zero : GroundTerm := .dv Srt.int (.int 0)
def one : GroundTerm := .dv Srt.int (.int 1)
def dotK : GroundTerm := .ctor dotk []
/-- The counter's initial value is 1: the configuration holds a fresh variable. -/
def ctr1 : GroundTerm := .ctor counterLabel [one]

def initK : String := "LblinitKCell"
def initTop : String := "LblinitGeneratedTopCell"
def initCtr : String := "LblinitGeneratedCounterCell"
def initId : String := "LblinitIdCell"
def getter : String := "LblgetGeneratedCounterCell"
def projExp : String := "Lblproject'Coln'Exp"

/-- The symbol named `f` applied to `ps`, as the translation writes an application. -/
def app (f : String) (ps : List KoreAML.P) : KoreAML.P := KoreAML.appList (symP f) ps

theorem sorted0 {c : Semantics} : ∀ x ∈ ([] : List GroundTerm), ∃ s, c.sortOf x = some s := fun _ h => by cases h

theorem sorted2 {c : Semantics} {w v : GroundTerm} (h : (c.sortOf w).isSome = true) (h' : (c.sortOf v).isSome = true) :
    ∀ x ∈ [w, v], ∃ s, c.sortOf x = some s := fun x hx => by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ⟨_, (Option.some_get h).symm⟩
  · rw [List.mem_singleton.mp hx]; exact ⟨_, (Option.some_get h').symm⟩

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

kore_term kore from "f2-examples/freshcfg.kompile.kore" cut [59, 118, 177, 236, 295, 354]
parse_stages stage from "f2-examples/freshcfg.kompile.kore" cut [59, 118, 177, 236, 295, 354]
  scan_blocks [1, 1, 1, 1, 1, 1, 1] prod_blocks [] rule_blocks [] event_blocks [] clause_blocks []
definition_of defn from "f2-examples/freshcfg.kompile.kore"

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
theorem scan4 : ScanIs kore.segs 4 1 stage.scan4 := by unfold ScanIs; kernel_rfl
theorem scan5 : ScanIs kore.segs 5 1 stage.scan5 := by unfold ScanIs; kernel_rfl
theorem scan6 : ScanIs kore.segs 6 1 stage.scan6 := by unfold ScanIs; kernel_rfl

/-- The blocks' scans, appended. -/
noncomputable def scanAll : Scan :=
  ((((((stage.scan0.append stage.scan1).append stage.scan2).append stage.scan3).append stage.scan4).append stage.scan5).append stage.scan6)

/-- **The account's scan of the user module**, block by block. -/
theorem scan_eq : S = scanAll :=
  ScanIs.all (n := 7) rfl
    ((((((scan0.join scan1 rfl).join scan2 rfl).join scan3 rfl).join scan4 rfl).join scan5 rfl).join scan6 rfl)

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
noncomputable def names : List String := order ++ [getter, projExp]

theorem order_eq : order = [initCtr, initId, initK, initTop] := by decide +kernel

/-- **The names are free of the theory**: none is a symbol of the semantics. -/
theorem names_ok : names.all (armNameB E.N E.src eqs c) = true := by
  rw [names, order_eq]; decide +kernel

theorem rank : armRankB order eqs = true := by decide +kernel
theorem hord : order.all names.contains = true := by decide +kernel

/-- **The arm takes each initializer's equation**, `initEqnOK E.N E.src S.eqs` at the tree's cell. -/
theorem accepted : armAccB E.N E.src eqs c cells initId = true ∧ armAccB E.N E.src eqs c cells initTop = true ∧
    armAccB E.N E.src eqs c cells initCtr = true := by
  decide +kernel

/-- `initIdCell` and `initGeneratedTopCell` take two arguments, `(Init, #Configuration)`. -/
theorem arities : armAr eqs initId = 2 ∧ armAr eqs initTop = 2 ∧ armAr eqs initCtr = 0 := by decide +kernel

theorem in_order : order.contains initId = true ∧ order.contains initTop = true ∧ order.contains initCtr = true := by
  decide +kernel

/-- **The arm takes the counter's `functional` axiom**, `initFunctionalOK E.N E.src S.eqs
(functionalSyms S.events)`; the text holds it. -/
theorem ctrFunctional : funcs.contains initCtr = true ∧
    (cells.find? (·.initLabel c == initCtr)).any
      (fun x => initFunctionalOK E.N E.src eqs funcs c x && x.initLabel c == initCtr) = true := by
  decide +kernel

/-- **The text holds no `functional` axiom of `initIdCell`**: it is not among the text's
`functional` symbols. -/
theorem noIdFunctional : funcs.contains initId = false := by decide +kernel

/-- `initFunctionalOK`, at the text's own `functional` symbols, takes a `functional` axiom of
`initIdCell` for its cell (were the text to hold one). -/
theorem idFunctional : (cells.find? (·.initLabel c == initId)).any
    (fun x => initFunctionalOK E.N E.src eqs funcs c x && x.initLabel c == initId) = true := by decide +kernel

noncomputable abbrev G : String → List GroundTerm → Option GroundTerm := armGOf c eqs names order (armBase c eqs)

noncomputable def symN (n : String) : Sym := nRegSyms + c.symNames.idxOf n
noncomputable def expS : Srt := nRegSorts + c.sortNames.idxOf "Exp"
noncomputable def idS : Srt := nRegSorts + c.sortNames.idxOf "IdCell"
/-- The counter cell's sort, a registry sort. -/
def ctrS : Srt := Srt.counter
noncomputable def pgm : GroundTerm := .inj expS Srt.kitem (.ctor (symN "Lbla") [])
/-- The map `$PGM ↦ a()`. -/
noncomputable def w1 : GroundTerm := .map Srt.map [(key, pgm)]
noncomputable def kV : GroundTerm := .ctor (symN "Lbl'-LT-'k'-GT-'") [.ctor kseq [pgm, dotK]]
noncomputable def idV : GroundTerm := .ctor (symN "Lbl'-LT-'id'-GT-'") [zero]
/-- The initial configuration at `w1`. -/
noncomputable def topV : GroundTerm := .ctor topLabel [kV, idV, ctr1]

theorem sorts : (c.sortOf w1).isSome ∧ (c.sortOf topV).isSome ∧ c.sortOf ctr1 = some ctrS ∧
    c.sortName ctrS = "GeneratedCounterCell" := by decide +kernel
theorem idSort : c.sortOf idV = some idS ∧ c.sortName idS = "IdCell" := by decide +kernel

/-- **The right sides, read**, at `(w1, t)` for the initial configuration `t`, and the counter's. -/
theorem reads : armAt c eqs names order (armBase c eqs) initId [w1, topV] = some (some idV) ∧
    armAt c eqs names order (armBase c eqs) initTop [w1, topV] = some (some topV) ∧
    armAt c eqs names order (armBase c eqs) initCtr [] = some (some ctr1) := by
  decide +kernel

/-- `initIdCell`'s right side holds no variable and is read as `<id>(0)`. -/
theorem idRhs : (match eqs.find? (·.fn == initId) with
    | some e => (armVars e.rhs).isEmpty && decide (armVal c names.contains (armAr eqs) G [] e.rhs = some (some idV))
    | none => false) = true := by decide +kernel

/-- **One model of the theory, whose steps are the semantics', holds the text's initializer
equations**, read as the account reads the text (its scan `S`, its names `E`) and `G` read from
them: the counter's equation and its `functional` axiom; `initIdCell(w1, t) = <id>(0)` and
`initGeneratedTopCell(w1, t)` the initial configuration `t`; and, the text holding no `functional`
axiom of `initIdCell`, the instance of one, `∃y:IdCell. y = initIdCell(ws)`, at all values `ws` of
a sort: an initializer of positive arity whose right side has a value at all of them. -/
theorem eqns :
    kore.modules.getLast? = some m ∧ envOf m S = .ok E ∧ S.eqs = eqs ∧ functionalSyms S.events = funcs ∧
    funcs.contains initId = false ∧
    ∃ I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem, (I ⊧ᴵP (Faithful.Γc c ∪ Faithful.Γstep c)) ∧
      TextEqn c eqs G I initCtr [] (some ctr1) ∧
      (I ⊧ᴵ KoreAML.sExists ⟨1⟩ (KoreAML.Cons.sortP "GeneratedCounterCell") (.evar ⟨1⟩ ≡ app initCtr [])) ∧
      TextEqn c eqs G I initId [w1, topV] (some idV) ∧ TextEqn c eqs G I initTop [w1, topV] (some topV) ∧
      (∃ e xs, eqs.find? (·.fn == initId) = some e ∧ distinctEVars? e.pats = some xs ∧
        ∀ ws : List GroundTerm, ws.length = 2 → (∀ w ∈ ws, ∃ s, c.sortOf w = some s) → ∀ y : ML.EVar,
          I ⊧ᴵ KoreAML.sExists y (KoreAML.Cons.sortP "IdCell")
            (.evar y ≡ KoreAML.den (armSubst c (armZip xs ws) (armLhs e)))) ∧
      ∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  obtain ⟨I, hM, hstep⟩ := model_of_arm c coreOK fnHyp E.N E.src eqs names order (armBase c eqs) names_ok
  obtain ⟨r1, r2, r3⟩ := reads
  obtain ⟨a1, a2, a3⟩ := accepted
  obtain ⟨o1, o2, o3⟩ := in_order
  obtain ⟨ar1, ar2, ar3⟩ := arities
  obtain ⟨hw1, htop, hctr, nCtr⟩ := sorts
  have sw := sorted2 hw1 htop
  have fCtr := functional_const hM rank hord ctrFunctional.2 o3 ar3 r3 hctr ⟨1⟩
  rw [nCtr] at fCtr
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
  refine ⟨last_eq, env_eq, eqs_eq, funcs_eq, noIdFunctional, I, hM.sat,
    init_arm_at hM rank hord a3 o3 (ws := []) ar3.symm sorted0 r3, fCtr,
    init_arm_at hM rank hord a1 o1 (ws := [w1, topV]) ar1.symm sw r1,
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

/-- info: 'GenEqsInitAcctFresh.eqns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eqns

end GenEqsInitAcctFresh
