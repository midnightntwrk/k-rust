/-
  The no-direction sentences of e7-freshconfig.kompile.kore that define a generated symbol (the cell initializers, the
  counter's getter, the sorts' projections) and the initializers' `functional` axioms, in one model
  of the theory, for every interpretation H of the parameters. Run from the package root:
  `lake env lean -j1 test/GenEqsNodirE7Freshconfig.lean`.

  The text is the construct fixture e7-freshconfig, `configuration <k> $PGM:Exp </k> <id> !N:Int </id>`, by K 7.1.337's kompile. Its user module is
  read as the account reads it (`consumedWith`, `Account.lean`): its scan `S = scan m.sentences`
  block by block (`scan_eq`) and its names `E` (`env_eq`), both computed by compiled code
  (`parse_stages`) and checked by the kernel.

  The sentences are named by index (`AxiomDecl.index`, the text's axiom numbers): `eqIdx` the
  equations (as `Parse.scanEqn` reads each), `funIdx` the constants' `functional` axioms
  (`GenEqs.nodFunctional?`). Their union `listed` is a sublist of the no-direction class of the
  text's tie (`test/TieE7Freshconfig.lean`; `listed_sub`), and each applies a symbol Γ lacks, the class's
  defining property there (`listed_absent`, `account_absent`'s predicate). Left out of the class:
  the `functional` axioms of hooked symbols (39, 43, 45, 76, 78, 101, 113, 114), the library equations of `andInt` (157), `dividesInt` (189) and `ite` (246, 247).

  Nothing here writes a right side, a value or a `G` by hand. The model is the arm's
  (`GenEqs.model_of_arm`): `G` read from `S.eqs` along the cell tree (`GenEqs.armG`), the getter and
  the projections by `GenEqs.armBase`; the names are the tree's initializers and the listed
  equations' other symbols, each no symbol of the semantics or a sort's projection with an equation
  `predProjOK?` accepts (`nodNameB`), the registry's projections among them checked free of the
  theory by one check for all (`freeB` at `ksReg`), which `GenEqs.nod_names_reg` turns into each
  name's `armNameB`. The sorts of each right side are read from the text (`GenEqs.nodTy`, `nodR`)
  and checked (`nodOrderB`), and each listed equation is one of the shapes `GenEqs.nod_eqB` takes
  (`nodSentEqB`): so each holds at every list of values of its variables' sorts (`GenEqs.NodEqn`),
  the instance `L(ws) = rhs[ws]` giving the symbol's value at `ws`. The checks read no
  interpretation (`GenEqs.nodSentEqB_withHooks`, …), so they are decided once on the data and the
  model is had for every H (`GenEqs.nod_instance_reg_withHooks`), with `FnHyp` under every H as the
  tie has it (`fnHypH`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Parse KCore.GenEqs

namespace GenEqsNodirE7Freshconfig

kore_term kore from "f2-examples/e7-freshconfig.kompile.kore" cut [59, 118, 177, 236, 295, 354]
parse_stages stage from "f2-examples/e7-freshconfig.kompile.kore" cut [59, 118, 177, 236, 295, 354] scan_blocks [1, 1, 1, 1, 1, 1, 1]
  prod_blocks [] rule_blocks [] event_blocks [] clause_blocks []
definition_of defn from "f2-examples/e7-freshconfig.kompile.kore"
user_axioms U from "f2-examples/e7-freshconfig.kompile.kore" module "E7-FRESHCONFIG"

/-! ## The text, its scan and its names, as the account reads them -/

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
noncomputable def scanAll : Scan := (((((stage.scan0.append stage.scan1).append stage.scan2).append stage.scan3).append stage.scan4).append stage.scan5).append stage.scan6

/-- **The account's scan of the user module**, block by block. -/
theorem scan_eq : S = scanAll := ScanIs.all (n := 7) rfl ((((((scan0.join scan1 rfl).join scan2 rfl).join scan3 rfl).join scan4 rfl).join scan5 rfl).join scan6 rfl)

/-- **The names the account reads the user module with.** -/
theorem env_eq : envOf m S = .ok E := by
  show envOf m S = .ok stage.env
  rw [scan_eq]; kernel_rfl

/-- The text's equations, as the account's scan gives them. -/
noncomputable def eqs : List RawEqn := scanAll.eqs

theorem eqs_eq : S.eqs = eqs := by rw [scan_eq]; rfl

/-- The axioms of the user module, in text order. -/
theorem userAxioms_eq : kore.axiomDecls.filter (·.module == "E7-FRESHCONFIG") = U.all := by kernel_rfl

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap

/-! ## `FnHyp` under every H, as the tie has it -/

def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H
  ParamsTotal.nil (obl_nil H)

/-! ## The listed sentences -/

/-- The equations: the getter's, the initializers', the projections'. -/
def eqIdx : List Nat := [210, 211, 212, 213, 214, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266]
/-- The constant initializers' `functional` axioms. -/
def funIdx : List Nat := [83]
def listed : List Nat := [83, 210, 211, 212, 213, 214, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266]

/-- The no-direction class of the tie (`test/TieE7Freshconfig.lean`, `classes`). -/
def nodirClass : List Nat := [39, 43, 45, 76, 78, 83, 101, 113, 114, 157, 189, 210, 211, 212, 213, 214, 246, 247, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266]

theorem listed_eq : listed.isPerm (eqIdx ++ funIdx) = true := by decide

/-- **The listed sentences are a sublist of the tie's no-direction class.** -/
theorem listed_sub : listed.Sublist nodirClass := by decide

/-- **Each listed sentence applies a symbol Γ lacks**, the no-direction class's defining property
(`account_absent` of the tie). -/
theorem listed_absent : listed.all (fun i => match U.all.find? (·.index == i) with
    | some ad => !(appHeadsOf ad.ax.pattern).all (gammaHasHead c)
    | none => false) = true := by
  decide +kernel

/-! ## The arm on the tree -/

/-- The presentation's cell tree. -/
noncomputable def cells : List Cell := Cell.all defn.pres.topCell
/-- The tree's initializers, bottom up. -/
noncomputable def order : List String := (cells.map (·.initLabel c)).reverse
/-- The symbols of the listed equations outside the tree: the getter and the projections. -/
noncomputable def others : List String :=
  ((eqIdx.filterMap fun i => (U.all.find? (·.index == i)).bind fun ad => scanEqn (.axiom ad.ax)).map (·.fn)).filter
    (!order.contains ·)
noncomputable def names : List String := order ++ others

/-- The registry numbers of the sorts' projections among the names (`ks_ok`). -/
def ksReg : List Sym := [152, 153, 154, 155, 157, 158, 159, 169, 170, 171]
/-- `ksReg` holds the registry number of each sort's projection among the names. -/
theorem ks_ok : (nodRegKs names).all ksReg.contains = true := by decide +kernel
/-- **The registry's projections among the names are free of the theory**, decided once for all. -/
theorem free_ok : freeB c ksReg = true := by decide +kernel
/-- **Each name is no symbol of the semantics, or a sort's projection with an equation
`predProjOK?` accepts.** -/
theorem names_ok : names.all (nodNameB E.N E.src eqs c) = true := by decide +kernel

theorem rank : armRankB order eqs = true := by decide +kernel
theorem hord : order.all names.contains = true := by decide +kernel
/-- **The right sides are of the names' sorts** (`nodR`, read from the text). -/
theorem sorts_ok : nodOrderB c names eqs order = true := by decide +kernel
theorem fixed_ok : nodFixedB c = true := by decide +kernel

/-- **Each listed equation is one the lemmas hold of.** -/
theorem eqs_ok : eqIdx.all (nodSentEqB E.N E.src eqs c cells names order U.all) = true := by decide +kernel
/-- **Each listed `functional` axiom is a constant initializer's, of its right side's sort.** -/
theorem funs_ok : funIdx.all (nodSentFunB c eqs names order U.all) = true := by decide +kernel

/-- **For every H, one model of `Γc ∪ Γstep` of `c.withHooks H`, whose steps at configurations
are `Step`'s, in which each listed equation holds at every list of values of its variables' sorts
and each listed `functional` axiom holds**, read as the account reads the text. -/
theorem nodir_instance (H : HookParams) :
    kore.modules.getLast? = some m ∧ envOf m S = .ok E ∧ S.eqs = eqs ∧ listed.Sublist nodirClass ∧
    ∃ I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem,
      (I ⊧ᴵP (Faithful.Γc (cH H) ∪ Faithful.Γstep (cH H))) ∧
      (∀ x y : Config (cH H), Step (cH H) x y ↔ ¬ (I ⊧ᴵ (den (cH H) x.val ⇒ ∼ KoreAML.sNext (den (cH H) y.val)))) ∧
      (∀ i ∈ eqIdx, ∃ ad ∈ U.all, ad.index = i ∧ ∃ e, scanEqn (.axiom ad.ax) = some e ∧ NodEqn (cH H) I e) ∧
      (∀ i ∈ funIdx, ∃ ad ∈ U.all, ad.index = i ∧ ∃ L S, nodFunctional? ad.ax = some (L, S) ∧ NodFun (cH H) I L S) :=
  ⟨last_eq, env_eq, eqs_eq, listed_sub,
    nod_instance_reg_withHooks c coreOK fnHypH E.N E.src eqs cells names order U.all eqIdx funIdx ksReg ks_ok free_ok
      names_ok rank hord sorts_ok fixed_ok eqs_ok funs_ok H⟩

/-- info: 'GenEqsNodirE7Freshconfig.nodir_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodir_instance

end GenEqsNodirE7Freshconfig
