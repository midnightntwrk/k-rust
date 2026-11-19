/-
  The no-direction sentences of e2-cells-stream.kompile.kore that define a generated symbol (the
  cell initializers, among them the stream cells' `initInCell` (sentence 2893) and `initOutCell`
  (2895), the counter's getter, the sorts' projections), the counter initializer's `functional`
  axiom, and the `functional` axioms of K-IO's `#stdin` and `#stdout`, in one model of the theory,
  for every interpretation H of the parameters. Run from the package root:
  `lake env lean -j1 test/GenEqsNodirE2CellsStream.lean`.

  The text is the construct fixture e2-cells-stream, `configuration <t> <k> $PGM:Exp </k>
  <in stream="stdin"> .List </in> <out stream="stdout"> .List </out> </t>`, by K 7.1.337's kompile.
  Its user module is read as the account reads it (`consumedWith`, `Account.lean`): its scan
  `S = scan m.sentences` block by block (`scan_eq`) and its names `E` (`env_eq`), both computed by
  compiled code (`parse_stages`) and checked by the kernel.

  The sentences are named by index (`AxiomDecl.index`, the text's axiom numbers): `eqIdx` the
  equations (as `Parse.scanEqn` reads each), `funIdx` the constants' `functional` axioms
  (`GenEqs.nodFunctional?`). Their union `listed` is a sublist of the no-direction class of the
  text's tie (`test/TieE2CellsStream.lean`; `listed_sub`), and each applies a symbol Γ lacks, the
  class's defining property there (`listed_absent`, `account_absent`'s predicate). Not listed: the
  projection `project:Int`'s equation (2976), which applies no symbol Γ lacks, and the equations of
  `#stdin` and `#stdout` (2813, 2814), which are no initializer's, projection's or getter's, the
  shapes `nodSentEqB` takes.

  Nothing here writes a right side, a value or a `G` by hand. The model is the arm's: `G` read from
  `S.eqs` along `order` (`GenEqs.armG`), the getter and the projections by `GenEqs.armBase`. The
  stream cells' initializers apply `#stdin` and `#stdout`, constants of K-IO that no symbol of the
  semantics is: `order` is these two, then the tree's initializers bottom up, so the arm gives each
  its equation's value. The names are `order` and the listed equations' other symbols, each borne
  by no symbol of the semantics (`GenEqs.nodLackedB`), so that no premise of the theory names it
  (`GenEqs.nodLacked_free`). The sorts of each right side are read from the text (`GenEqs.nodTy`,
  `nodR`) and checked (`nodOrderB`), and each listed equation is one of the shapes
  `GenEqs.nod_eqB` takes (`nodSentEqB`): so each holds at every list of values of its variables'
  sorts (`GenEqs.NodEqn`). The checks read no interpretation, so they are decided once on the data
  and the model is had for every H (`GenEqs.nod_instance_lacked_withHooks`), with `FnHyp` under
  every H (`fnHypH`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Parse KCore.GenEqs

namespace GenEqsNodirE2CellsStream

kore_term kore from "f2-examples/e2-cells-stream.kompile.kore" cut [20, 40, 60, 80, 100, 120, 140, 160, 180, 200, 220, 240, 260, 280, 300, 320, 340, 360, 380, 400, 500, 600, 700, 800, 900, 1000, 1100, 1200, 1300, 1400, 1500, 1600, 1700, 1800, 1900, 2000, 2100, 2200, 2300, 2400, 2500, 2600, 2700, 2800, 2900, 3000, 3020, 3040, 3060, 3080, 3100, 3120, 3140, 3160, 3180, 3200, 3220, 3240, 3260, 3280, 3300, 3320]
parse_stages stage from "f2-examples/e2-cells-stream.kompile.kore" cut [20, 40, 60, 80, 100, 120, 140, 160, 180, 200, 220, 240, 260, 280, 300, 320, 340, 360, 380, 400, 500, 600, 700, 800, 900, 1000, 1100, 1200, 1300, 1400, 1500, 1600, 1700, 1800, 1900, 2000, 2100, 2200, 2300, 2400, 2500, 2600, 2700, 2800, 2900, 3000, 3020, 3040, 3060, 3080, 3100, 3120, 3140, 3160, 3180, 3200, 3220, 3240, 3260, 3280, 3300, 3320] scan_blocks [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  prod_blocks [] rule_blocks [] event_blocks [] clause_blocks []
definition_of defn from "f2-examples/e2-cells-stream.kompile.kore"
user_axioms U from "f2-examples/e2-cells-stream.kompile.kore" module "E2-CELLS-STREAM"

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
theorem scan7 : ScanIs kore.segs 7 1 stage.scan7 := by unfold ScanIs; kernel_rfl
theorem scan8 : ScanIs kore.segs 8 1 stage.scan8 := by unfold ScanIs; kernel_rfl
theorem scan9 : ScanIs kore.segs 9 1 stage.scan9 := by unfold ScanIs; kernel_rfl
theorem scan10 : ScanIs kore.segs 10 1 stage.scan10 := by unfold ScanIs; kernel_rfl
theorem scan11 : ScanIs kore.segs 11 1 stage.scan11 := by unfold ScanIs; kernel_rfl
theorem scan12 : ScanIs kore.segs 12 1 stage.scan12 := by unfold ScanIs; kernel_rfl
theorem scan13 : ScanIs kore.segs 13 1 stage.scan13 := by unfold ScanIs; kernel_rfl
theorem scan14 : ScanIs kore.segs 14 1 stage.scan14 := by unfold ScanIs; kernel_rfl
theorem scan15 : ScanIs kore.segs 15 1 stage.scan15 := by unfold ScanIs; kernel_rfl
theorem scan16 : ScanIs kore.segs 16 1 stage.scan16 := by unfold ScanIs; kernel_rfl
theorem scan17 : ScanIs kore.segs 17 1 stage.scan17 := by unfold ScanIs; kernel_rfl
theorem scan18 : ScanIs kore.segs 18 1 stage.scan18 := by unfold ScanIs; kernel_rfl
theorem scan19 : ScanIs kore.segs 19 1 stage.scan19 := by unfold ScanIs; kernel_rfl
theorem scan20 : ScanIs kore.segs 20 1 stage.scan20 := by unfold ScanIs; kernel_rfl
theorem scan21 : ScanIs kore.segs 21 1 stage.scan21 := by unfold ScanIs; kernel_rfl
theorem scan22 : ScanIs kore.segs 22 1 stage.scan22 := by unfold ScanIs; kernel_rfl
theorem scan23 : ScanIs kore.segs 23 1 stage.scan23 := by unfold ScanIs; kernel_rfl
theorem scan24 : ScanIs kore.segs 24 1 stage.scan24 := by unfold ScanIs; kernel_rfl
theorem scan25 : ScanIs kore.segs 25 1 stage.scan25 := by unfold ScanIs; kernel_rfl
theorem scan26 : ScanIs kore.segs 26 1 stage.scan26 := by unfold ScanIs; kernel_rfl
theorem scan27 : ScanIs kore.segs 27 1 stage.scan27 := by unfold ScanIs; kernel_rfl
theorem scan28 : ScanIs kore.segs 28 1 stage.scan28 := by unfold ScanIs; kernel_rfl
theorem scan29 : ScanIs kore.segs 29 1 stage.scan29 := by unfold ScanIs; kernel_rfl
theorem scan30 : ScanIs kore.segs 30 1 stage.scan30 := by unfold ScanIs; kernel_rfl
theorem scan31 : ScanIs kore.segs 31 1 stage.scan31 := by unfold ScanIs; kernel_rfl
theorem scan32 : ScanIs kore.segs 32 1 stage.scan32 := by unfold ScanIs; kernel_rfl
theorem scan33 : ScanIs kore.segs 33 1 stage.scan33 := by unfold ScanIs; kernel_rfl
theorem scan34 : ScanIs kore.segs 34 1 stage.scan34 := by unfold ScanIs; kernel_rfl
theorem scan35 : ScanIs kore.segs 35 1 stage.scan35 := by unfold ScanIs; kernel_rfl
theorem scan36 : ScanIs kore.segs 36 1 stage.scan36 := by unfold ScanIs; kernel_rfl
theorem scan37 : ScanIs kore.segs 37 1 stage.scan37 := by unfold ScanIs; kernel_rfl
theorem scan38 : ScanIs kore.segs 38 1 stage.scan38 := by unfold ScanIs; kernel_rfl
theorem scan39 : ScanIs kore.segs 39 1 stage.scan39 := by unfold ScanIs; kernel_rfl
theorem scan40 : ScanIs kore.segs 40 1 stage.scan40 := by unfold ScanIs; kernel_rfl
theorem scan41 : ScanIs kore.segs 41 1 stage.scan41 := by unfold ScanIs; kernel_rfl
theorem scan42 : ScanIs kore.segs 42 1 stage.scan42 := by unfold ScanIs; kernel_rfl
theorem scan43 : ScanIs kore.segs 43 1 stage.scan43 := by unfold ScanIs; kernel_rfl
theorem scan44 : ScanIs kore.segs 44 1 stage.scan44 := by unfold ScanIs; kernel_rfl
theorem scan45 : ScanIs kore.segs 45 1 stage.scan45 := by unfold ScanIs; kernel_rfl
theorem scan46 : ScanIs kore.segs 46 1 stage.scan46 := by unfold ScanIs; kernel_rfl
theorem scan47 : ScanIs kore.segs 47 1 stage.scan47 := by unfold ScanIs; kernel_rfl
theorem scan48 : ScanIs kore.segs 48 1 stage.scan48 := by unfold ScanIs; kernel_rfl
theorem scan49 : ScanIs kore.segs 49 1 stage.scan49 := by unfold ScanIs; kernel_rfl
theorem scan50 : ScanIs kore.segs 50 1 stage.scan50 := by unfold ScanIs; kernel_rfl
theorem scan51 : ScanIs kore.segs 51 1 stage.scan51 := by unfold ScanIs; kernel_rfl
theorem scan52 : ScanIs kore.segs 52 1 stage.scan52 := by unfold ScanIs; kernel_rfl
theorem scan53 : ScanIs kore.segs 53 1 stage.scan53 := by unfold ScanIs; kernel_rfl
theorem scan54 : ScanIs kore.segs 54 1 stage.scan54 := by unfold ScanIs; kernel_rfl
theorem scan55 : ScanIs kore.segs 55 1 stage.scan55 := by unfold ScanIs; kernel_rfl
theorem scan56 : ScanIs kore.segs 56 1 stage.scan56 := by unfold ScanIs; kernel_rfl
theorem scan57 : ScanIs kore.segs 57 1 stage.scan57 := by unfold ScanIs; kernel_rfl
theorem scan58 : ScanIs kore.segs 58 1 stage.scan58 := by unfold ScanIs; kernel_rfl
theorem scan59 : ScanIs kore.segs 59 1 stage.scan59 := by unfold ScanIs; kernel_rfl
theorem scan60 : ScanIs kore.segs 60 1 stage.scan60 := by unfold ScanIs; kernel_rfl
theorem scan61 : ScanIs kore.segs 61 1 stage.scan61 := by unfold ScanIs; kernel_rfl
theorem scan62 : ScanIs kore.segs 62 1 stage.scan62 := by unfold ScanIs; kernel_rfl

/-- The blocks' scans, appended. -/
noncomputable def scanAll : Scan := ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((stage.scan0).append stage.scan1).append stage.scan2).append stage.scan3).append stage.scan4).append stage.scan5).append stage.scan6).append stage.scan7).append stage.scan8).append stage.scan9).append stage.scan10).append stage.scan11).append stage.scan12).append stage.scan13).append stage.scan14).append stage.scan15).append stage.scan16).append stage.scan17).append stage.scan18).append stage.scan19).append stage.scan20).append stage.scan21).append stage.scan22).append stage.scan23).append stage.scan24).append stage.scan25).append stage.scan26).append stage.scan27).append stage.scan28).append stage.scan29).append stage.scan30).append stage.scan31).append stage.scan32).append stage.scan33).append stage.scan34).append stage.scan35).append stage.scan36).append stage.scan37).append stage.scan38).append stage.scan39).append stage.scan40).append stage.scan41).append stage.scan42).append stage.scan43).append stage.scan44).append stage.scan45).append stage.scan46).append stage.scan47).append stage.scan48).append stage.scan49).append stage.scan50).append stage.scan51).append stage.scan52).append stage.scan53).append stage.scan54).append stage.scan55).append stage.scan56).append stage.scan57).append stage.scan58).append stage.scan59).append stage.scan60).append stage.scan61).append stage.scan62

/-- **The account's scan of the user module**, block by block. -/
theorem scan_eq : S = scanAll := ScanIs.all (n := 63) rfl ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((scan0.join scan1 rfl).join scan2 rfl).join scan3 rfl).join scan4 rfl).join scan5 rfl).join scan6 rfl).join scan7 rfl).join scan8 rfl).join scan9 rfl).join scan10 rfl).join scan11 rfl).join scan12 rfl).join scan13 rfl).join scan14 rfl).join scan15 rfl).join scan16 rfl).join scan17 rfl).join scan18 rfl).join scan19 rfl).join scan20 rfl).join scan21 rfl).join scan22 rfl).join scan23 rfl).join scan24 rfl).join scan25 rfl).join scan26 rfl).join scan27 rfl).join scan28 rfl).join scan29 rfl).join scan30 rfl).join scan31 rfl).join scan32 rfl).join scan33 rfl).join scan34 rfl).join scan35 rfl).join scan36 rfl).join scan37 rfl).join scan38 rfl).join scan39 rfl).join scan40 rfl).join scan41 rfl).join scan42 rfl).join scan43 rfl).join scan44 rfl).join scan45 rfl).join scan46 rfl).join scan47 rfl).join scan48 rfl).join scan49 rfl).join scan50 rfl).join scan51 rfl).join scan52 rfl).join scan53 rfl).join scan54 rfl).join scan55 rfl).join scan56 rfl).join scan57 rfl).join scan58 rfl).join scan59 rfl).join scan60 rfl).join scan61 rfl).join scan62 rfl)

/-- **The names the account reads the user module with.** -/
theorem env_eq : envOf m S = .ok E := by
  show envOf m S = .ok stage.env
  rw [scan_eq]; kernel_rfl

/-- The text's equations, as the account's scan gives them. -/
noncomputable def eqs : List RawEqn := scanAll.eqs

theorem eqs_eq : S.eqs = eqs := by rw [scan_eq]; rfl

/-- The axioms of the user module, in text order. -/
theorem userAxioms_eq : kore.axiomDecls.filter (·.module == "E2-CELLS-STREAM") = U.all := by kernel_rfl

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap

/-! ## `FnHyp` under every H -/

def callOrder : List Nat := [401, 402]

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
def eqIdx : List Nat := [2890, 2891, 2892, 2893, 2894, 2895, 2896, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975, 2977, 2978, 2979, 2980, 2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988, 2989, 2990]
/-- The `functional` axioms of `#stdin`, `#stdout` and the counter's initializer. -/
def funIdx : List Nat := [2615, 2616, 2705]
def listed : List Nat := [2615, 2616, 2705, 2890, 2891, 2892, 2893, 2894, 2895, 2896, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975, 2977, 2978, 2979, 2980, 2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988, 2989, 2990]

theorem listed_eq : listed.isPerm (eqIdx ++ funIdx) = true := by decide

/-- The no-direction class of the tie (`test/TieE2CellsStream.lean`, `classes`). -/
def nodirClass : List Nat := [2603, 2604, 2613, 2614, 2615, 2616, 2621, 2622, 2653, 2658, 2660, 2697, 2699, 2705, 2736, 2755, 2756, 2811, 2812, 2813, 2814, 2828, 2865, 2887, 2890, 2891, 2892, 2893, 2894, 2895, 2896, 2954, 2955, 2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975, 2977, 2978, 2979, 2980, 2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988, 2989, 2990]

/-- **The listed sentences are a sublist of the tie's no-direction class.** -/
theorem listed_sub : listed.Sublist nodirClass := by decide

/-- No symbol of the semantics has a name `instDecode?` reads as an instance, so Γ's heads
are its symbols' names at no sort argument and `inj` at its subsorts (`gammaHasHead_eq_plain`). -/
theorem iteFree : (Faithful.kernelSyms c).all (fun k => (instDecode? (c.symName k.name)).isNone) = true := by
  decide +kernel

/-- **Each listed sentence applies a symbol Γ lacks**, the no-direction class's defining property
(`account_absent`'s predicate). -/
theorem listed_absent : listed.all (fun i => match U.all.find? (·.index == i) with
    | some ad => !(appHeadsOf ad.ax.pattern).all (gammaHasHead c)
    | none => false) = true := by
  rw [gammaHasHead_eq_plain iteFree]; decide +kernel

/-! ## The arm on the tree -/

/-- The presentation's cell tree. -/
noncomputable def cells : List Cell := Cell.all defn.pres.topCell
/-- K-IO's constants the stream cells' initializers apply. -/
def ioConsts : List String := ["Lbl'Hash'stdin'Unds'K-IO'Unds'Int", "Lbl'Hash'stdout'Unds'K-IO'Unds'Int"]
/-- K-IO's constants, then the tree's initializers, bottom up. -/
noncomputable def order : List String := ioConsts ++ (cells.map (·.initLabel c)).reverse
/-- The symbols of the listed equations outside `order`: the getter and the projections. -/
noncomputable def others : List String :=
  ((eqIdx.filterMap fun i => (U.all.find? (·.index == i)).bind fun ad => scanEqn (.axiom ad.ax)).map (·.fn)).filter
    (!order.contains ·)
noncomputable def names : List String := order ++ others

/-- **Each name is borne by no symbol of the semantics**, so no premise of the theory names it. -/
theorem names_ok : names.all (nodLackedB c) = true := by decide +kernel

theorem rank : armRankB order eqs = true := by decide +kernel
theorem hord : order.all names.contains = true := by decide +kernel
/-- **The right sides are of the names' sorts** (`nodR`, read from the text). -/
theorem sorts_ok : nodOrderB c names eqs order = true := by decide +kernel
theorem fixed_ok : nodFixedB c = true := by decide +kernel

/-- **Each listed equation is one the lemmas hold of.** -/
theorem eqs_ok : eqIdx.all (nodSentEqB E.N E.src eqs c cells names order U.all) = true := by decide +kernel
/-- **Each listed `functional` axiom is a constant's in `order`, of its right side's sort.** -/
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
    nod_instance_lacked_withHooks c coreOK fnHypH E.N E.src eqs cells names order U.all eqIdx funIdx names_ok rank hord
      sorts_ok fixed_ok eqs_ok funs_ok H⟩

/-- info: 'GenEqsNodirE2CellsStream.nodir_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodir_instance

end GenEqsNodirE2CellsStream
