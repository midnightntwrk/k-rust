/-
  Part Cons of the tie (C14) on `f2-examples/e2-cells.kompile.kore`, test/TieE2Cells.lean: the sections
  `--split` puts here, in the tie's namespace. A test file imports no test file, so this one
  repeats the literals and the definitions and facts it reads. Written by
  `test/constructs/tiegen.py e2-cells --split`; run from the package root:
  `lake env lean -j1 test/TieE2CellsCons.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE2Cells

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e2-cells.kompile.kore"
definition_of defn from "f2-examples/e2-cells.kompile.kore"
user_axioms U from "f2-examples/e2-cells.kompile.kore" module "E2-CELLS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-! ## The constructor sentences: functional, subsort, injectivity, distinctness -/

/-- The constructor sentences `tchConsB` decides, in text order. -/
noncomputable def consText : List AxiomDecl :=
  [U.ax4, U.ax5, U.ax6, U.ax7, U.ax8, U.ax9, U.ax10, U.ax11, U.ax12, U.ax13, U.ax14, U.ax15,
   U.ax16, U.ax17, U.ax18, U.ax19, U.ax20, U.ax21, U.ax22, U.ax23, U.ax25, U.ax26, U.ax27, U.ax28,
   U.ax29, U.ax31, U.ax32, U.ax33, U.ax34, U.ax35, U.ax36, U.ax37, U.ax38, U.ax39, U.ax40, U.ax41,
   U.ax42, U.ax43, U.ax44, U.ax45, U.ax46, U.ax47, U.ax48, U.ax49, U.ax50, U.ax51, U.ax52, U.ax53,
   U.ax54, U.ax56, U.ax57, U.ax58, U.ax59, U.ax60, U.ax61, U.ax62, U.ax63, U.ax66, U.ax67, U.ax69,
   U.ax70, U.ax71, U.ax72, U.ax73, U.ax74, U.ax75, U.ax76, U.ax77, U.ax78, U.ax79, U.ax80, U.ax81,
   U.ax82, U.ax83, U.ax84, U.ax85, U.ax86, U.ax87, U.ax88, U.ax89, U.ax90, U.ax91, U.ax92, U.ax93,
   U.ax94, U.ax95, U.ax96, U.ax97, U.ax98, U.ax99, U.ax100, U.ax101, U.ax102, U.ax103, U.ax104,
   U.ax105, U.ax106, U.ax107, U.ax108, U.ax109, U.ax110, U.ax111, U.ax112, U.ax113, U.ax114,
   U.ax174, U.ax242, U.ax243, U.ax244, U.ax245, U.ax246, U.ax247, U.ax248, U.ax249, U.ax250,
   U.ax251, U.ax252, U.ax253]

theorem consE_0 : (((consText).drop 0).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_40 : (((consText).drop 40).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_80 : ((consText).drop 80).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem cons_checked_hd : consText.all (fun ad => tchConsB c ad.ax) = true :=
  tieAll_whole (l := consText) (p := (fun ad => tchConsB c ad.ax)) <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 0) (n := 40) consE_0 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 40) (n := 40) consE_40 <|
    consE_80

theorem cons_checked : consText.all (fun ad => tieConsB c ad.ax) = true := tchConsB_all cons_checked_hd

theorem consT_0 : (((consText).drop 0).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_40 : (((consText).drop 40).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_80 : ((consText).drop 80).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem cons_trS : consText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true :=
  tieAll_whole (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 0) (n := 40) consT_0 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 40) (n := 40) consT_40 <|
    consT_80

/-- **E for the constructor sentences**: Γ entails each, for every H. -/
theorem cons_entailed (H : HookParams) : ∀ ad ∈ consText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  rw [of_decide_eq_true (List.all_eq_true.mp cons_trS ad had)]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact tieCons_entailed (c := cH H) (a := ad.ax)
    ((tieConsB_withHooks c H ad.ax).trans (List.all_eq_true.mp cons_checked ad had)) ad.index ad.module hI

end KCore.TieE2Cells

#check @KCore.TieE2Cells.cons_entailed
#print axioms KCore.TieE2Cells.cons_entailed
