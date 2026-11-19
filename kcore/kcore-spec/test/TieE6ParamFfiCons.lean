/-
  Part Cons of the tie (C14) on `f2-examples/e6-param-ffi.kompile.kore`, test/TieE6ParamFfi.lean: the sections
  `--split` puts here, in the tie's namespace. A test file imports no test file, so this one
  repeats the literals and the definitions and facts it reads. Written by
  `test/constructs/tiegen.py e6-param-ffi --split`; run from the package root:
  `lake env lean -j1 test/TieE6ParamFfiCons.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE6ParamFfi

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6-param-ffi.kompile.kore"
definition_of defn from "f2-examples/e6-param-ffi.kompile.kore"
user_axioms U from "f2-examples/e6-param-ffi.kompile.kore" module "E6-PARAM-FFI"
user_axioms PreludeKseq from "f2-examples/e6-param-ffi.kompile.kore" module "KSEQ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-! ## The constructor sentences: functional, subsort, injectivity, distinctness -/

/-- The constructor sentences `tieConsB` decides, in text order. -/
noncomputable def consText : List AxiomDecl :=
  [U.ax4, U.ax5, U.ax6, U.ax7, U.ax8, U.ax9, U.ax10, U.ax11, U.ax12, U.ax13, U.ax14, U.ax15,
   U.ax16, U.ax17, U.ax18, U.ax19, U.ax20, U.ax21, U.ax22, U.ax23, U.ax24, U.ax25, U.ax26, U.ax27,
   U.ax28, U.ax29, U.ax30, U.ax31, U.ax32, U.ax33, U.ax34, U.ax35, U.ax36, U.ax37, U.ax38, U.ax39,
   U.ax40, U.ax41, U.ax42, U.ax43, U.ax44, U.ax45, U.ax46, U.ax47, U.ax48, U.ax49, U.ax50, U.ax51,
   U.ax52, U.ax53, U.ax54, U.ax55, U.ax56, U.ax57, U.ax58, U.ax59, U.ax60, U.ax61, U.ax62, U.ax63,
   U.ax64, U.ax65, U.ax66, U.ax67, U.ax68, U.ax69, U.ax70, U.ax71, U.ax72, U.ax73, U.ax74, U.ax75,
   U.ax76, U.ax77, U.ax78, U.ax79, U.ax80, U.ax81, U.ax82, U.ax83, U.ax84, U.ax85, U.ax86, U.ax87,
   U.ax88, U.ax89, U.ax90, U.ax91, U.ax92, U.ax93, U.ax94, U.ax95, U.ax96, U.ax97, U.ax98, U.ax99,
   U.ax100, U.ax101, U.ax102, U.ax103, U.ax104, U.ax105, U.ax106, U.ax107, U.ax108, U.ax109,
   U.ax110, U.ax111, U.ax112, U.ax113, U.ax114, U.ax115, U.ax116, U.ax117, U.ax118, U.ax119,
   U.ax120, U.ax121, U.ax122, U.ax123, U.ax124, U.ax125, U.ax126, U.ax127, U.ax128, U.ax129,
   U.ax130, U.ax131, U.ax132, U.ax133, U.ax134, U.ax135, U.ax136, U.ax137, U.ax138, U.ax139,
   U.ax140, U.ax141, U.ax142, U.ax143, U.ax144, U.ax145, U.ax146, U.ax147, U.ax148, U.ax149,
   U.ax150, U.ax151, U.ax152, U.ax153, U.ax154, U.ax155, U.ax156, U.ax157, U.ax158, U.ax159,
   U.ax160, U.ax161, U.ax162, U.ax163, U.ax164, U.ax165, U.ax166, U.ax167, U.ax168, U.ax169,
   U.ax170, U.ax171, U.ax172, U.ax173, U.ax174, U.ax175, U.ax176, U.ax177, U.ax178, U.ax179,
   U.ax180, U.ax181, U.ax182, U.ax183, U.ax184, U.ax185, U.ax186, U.ax187, U.ax188, U.ax189,
   U.ax190, U.ax191, U.ax192, U.ax193, U.ax194, U.ax195, U.ax196, U.ax197, U.ax198, U.ax199,
   U.ax200, U.ax201, U.ax202, U.ax203, U.ax204, U.ax205, U.ax206, U.ax207, U.ax208, U.ax209,
   U.ax210, U.ax211, U.ax212, U.ax213, U.ax214, U.ax215, U.ax216, U.ax217, U.ax218, U.ax219,
   U.ax220, U.ax221, U.ax222, U.ax223, U.ax224, U.ax225, U.ax226, U.ax227, U.ax228, U.ax229,
   U.ax230, U.ax231, U.ax232, U.ax233, U.ax234, U.ax235, U.ax236, U.ax237, U.ax238, U.ax239,
   U.ax240, U.ax241, U.ax242, U.ax243, U.ax244, U.ax245, U.ax246, U.ax247, U.ax248, U.ax249,
   U.ax250, U.ax251, U.ax252, U.ax253, U.ax254, U.ax255, U.ax256, U.ax257, U.ax258, U.ax259,
   U.ax260, U.ax261, U.ax262, U.ax263, U.ax264, U.ax265, U.ax266, U.ax267, U.ax268, U.ax269,
   U.ax270, U.ax271, U.ax272, U.ax273, U.ax274, U.ax275, U.ax276, U.ax277, U.ax278, U.ax279,
   U.ax280, U.ax281, U.ax282, U.ax283, U.ax284, U.ax285, U.ax286, U.ax287, U.ax288, U.ax289,
   U.ax290, U.ax291, U.ax292, U.ax293, U.ax294, U.ax295, U.ax296, U.ax297, U.ax298, U.ax299,
   U.ax300, U.ax301, U.ax302, U.ax303, U.ax304, U.ax305, U.ax306, U.ax307, U.ax308, U.ax309,
   U.ax310, U.ax311, U.ax312, U.ax313, U.ax314, U.ax315, U.ax316, U.ax317, U.ax318, U.ax319,
   U.ax320, U.ax321, U.ax322, U.ax323, U.ax324, U.ax325, U.ax326, U.ax327, U.ax328, U.ax329,
   U.ax330, U.ax331, U.ax332, U.ax333, U.ax334, U.ax335, U.ax336, U.ax337, U.ax338, U.ax339,
   U.ax340, U.ax341, U.ax342, U.ax343, U.ax344, U.ax345, U.ax346, U.ax347, U.ax348, U.ax349,
   U.ax354, U.ax355, U.ax356, U.ax357, U.ax358, U.ax359, U.ax360, U.ax361, U.ax427, U.ax428,
   U.ax431, U.ax432, U.ax460, U.ax463, U.ax464, U.ax471, U.ax472, U.ax477]

theorem consE_0 : (((consText).drop 0).take 40).all (fun ad => tieConsB c ad.ax) = true := by decide +kernel
theorem consE_40 : (((consText).drop 40).take 40).all (fun ad => tieConsB c ad.ax) = true := by decide +kernel
theorem consE_80 : (((consText).drop 80).take 40).all (fun ad => tieConsB c ad.ax) = true := by decide +kernel
theorem consE_120 : (((consText).drop 120).take 40).all (fun ad => tieConsB c ad.ax) = true := by decide +kernel
theorem consE_160 : (((consText).drop 160).take 40).all (fun ad => tieConsB c ad.ax) = true := by decide +kernel
theorem consE_200 : (((consText).drop 200).take 40).all (fun ad => tieConsB c ad.ax) = true := by decide +kernel
theorem consE_240 : (((consText).drop 240).take 40).all (fun ad => tieConsB c ad.ax) = true := by decide +kernel
theorem consE_280 : (((consText).drop 280).take 40).all (fun ad => tieConsB c ad.ax) = true := by decide +kernel
theorem consE_320 : (((consText).drop 320).take 40).all (fun ad => tieConsB c ad.ax) = true := by decide +kernel
theorem consE_360 : ((consText).drop 360).all (fun ad => tieConsB c ad.ax) = true := by decide +kernel
theorem cons_checked : consText.all (fun ad => tieConsB c ad.ax) = true :=
  tieAll_whole (l := consText) (p := (fun ad => tieConsB c ad.ax)) <|
    tieAll_range (l := consText) (p := (fun ad => tieConsB c ad.ax)) (a := 0) (n := 40) consE_0 <|
    tieAll_range (l := consText) (p := (fun ad => tieConsB c ad.ax)) (a := 40) (n := 40) consE_40 <|
    tieAll_range (l := consText) (p := (fun ad => tieConsB c ad.ax)) (a := 80) (n := 40) consE_80 <|
    tieAll_range (l := consText) (p := (fun ad => tieConsB c ad.ax)) (a := 120) (n := 40) consE_120 <|
    tieAll_range (l := consText) (p := (fun ad => tieConsB c ad.ax)) (a := 160) (n := 40) consE_160 <|
    tieAll_range (l := consText) (p := (fun ad => tieConsB c ad.ax)) (a := 200) (n := 40) consE_200 <|
    tieAll_range (l := consText) (p := (fun ad => tieConsB c ad.ax)) (a := 240) (n := 40) consE_240 <|
    tieAll_range (l := consText) (p := (fun ad => tieConsB c ad.ax)) (a := 280) (n := 40) consE_280 <|
    tieAll_range (l := consText) (p := (fun ad => tieConsB c ad.ax)) (a := 320) (n := 40) consE_320 <|
    consE_360

theorem consT_0 : (((consText).drop 0).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_40 : (((consText).drop 40).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_80 : (((consText).drop 80).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_120 : (((consText).drop 120).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_160 : (((consText).drop 160).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_200 : (((consText).drop 200).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_240 : (((consText).drop 240).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_280 : (((consText).drop 280).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_320 : (((consText).drop 320).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_360 : ((consText).drop 360).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem cons_trS : consText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true :=
  tieAll_whole (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 0) (n := 40) consT_0 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 40) (n := 40) consT_40 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 80) (n := 40) consT_80 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 120) (n := 40) consT_120 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 160) (n := 40) consT_160 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 200) (n := 40) consT_200 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 240) (n := 40) consT_240 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 280) (n := 40) consT_280 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 320) (n := 40) consT_320 <|
    consT_360

/-- **E for the constructor sentences**: Γ entails each, for every H. -/
theorem cons_entailed (H : HookParams) : ∀ ad ∈ consText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  rw [of_decide_eq_true (List.all_eq_true.mp cons_trS ad had)]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact tieCons_entailed (c := cH H) (a := ad.ax)
    ((tieConsB_withHooks c H ad.ax).trans (List.all_eq_true.mp cons_checked ad had)) ad.index ad.module hI

end KCore.TieE6ParamFfi

#check @KCore.TieE6ParamFfi.cons_entailed
#print axioms KCore.TieE6ParamFfi.cons_entailed
