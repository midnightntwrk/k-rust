/-
  On `f2-examples/e1-starinit.kompile.kore` (the text `test/TieE1Starinit.lean` ties), for every
  interpretation H: no model of `Γc (cH H)` satisfies both the translation of sentence 31 (the
  subsort sentence of TCell into TCellSet, `∃Val:TCellSet. Val = inj{TCell,TCellSet}(From)`) and
  the translation of the axiom of the prelude's module INJ (sentence 3,
  `inj{S2,S3}(inj{S1,S2}(T)) = inj{S1,S3}(T)` over the sort variables S1, S2, S3, R):
  `cellcoll_subsort_refuted`.

  The argument, in a model `I` of Γ:
  - a value of TCell (`<t>(<v>(0), <p>(go()))`) denotes an element `e` of TCell (`elemOf_spec`);
  - by 31 there is `s` in TCellSet with `s ∈ inj{TCell,TCellSet}(e)` (`text31`);
  - Cons-Fun of the injections of TCell and TCellSet into KItem gives `y = inj{TCell,KItem}(e)` and
    `y' = inj{TCellSet,KItem}(s)`, both of KItem (`gen_fun`);
  - the INJ axiom at S1 = TCell, S2 = TCellSet, S3 = KItem and `T = e`, read at `y'`, puts `y'` in
    `inj{TCell,KItem}(e)`, so `y' = y` (`textTri`);
  - so `s` and `e` have the same injection into KItem, which Γ's Cons-Dist of the two injections
    refutes, the order `subsorts` comparing TCell and TCellSet in neither direction and no sort
    lying below both (`Faithful.inj_apart_no_model`).
  Run from the package root: `lake env lean -j1 test/TieE1StarinitCellColl.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE1Starinit

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e1-starinit.kompile.kore"
definition_of defn from "f2-examples/e1-starinit.kompile.kore"
user_axioms U from "f2-examples/e1-starinit.kompile.kore" module "STARINIT"
user_axioms J from "f2-examples/e1-starinit.kompile.kore" module "INJ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The translation of sentence 31, the subsort sentence of TCell into TCellSet. -/
noncomputable def tr31 : KoreAML.P := (trS U.ax31).pat
/-- The translation of the axiom of the prelude's module INJ (sentence 3), over its sort
variables. -/
noncomputable def trTri : KoreAML.P := (trS J.ax3).pat

/-- The two sentences are the text's axioms 3 and 31 (`AxiomDecl.index`, counted from 1). -/
theorem ax3_text : kore.axiomDecls[2]? = some J.ax3 := by kernel_rfl
theorem ax31_text : kore.axiomDecls[30]? = some U.ax31 := by kernel_rfl

/-- The module INJ has the one axiom, sentence 3, and sentence 31 is of the user module. -/
theorem inj_module : J.all.map (·.index) = [3] ∧ J.ax3.module = "INJ" ∧ U.ax31.module = "STARINIT" := by
  decide +kernel

/-! ## The order and the generators -/

/-- The sorts TCell and TCellSet. -/
noncomputable abbrev tC : Srt := nRegSorts + c.sortNames.idxOf "TCell"
noncomputable abbrev tS : Srt := nRegSorts + c.sortNames.idxOf "TCellSet"

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem sort_names : c.sortName tC = "TCell" ∧ c.sortName tS = "TCellSet" ∧ c.sortName Srt.kitem = "KItem" := by
  decide +kernel

theorem sorts_numbered : tC < nRegSorts + c.sortNames.length ∧ tS < nRegSorts + c.sortNames.length ∧
    Srt.kitem < nRegSorts + c.sortNames.length := by decide +kernel

/-- TCell and TCellSet are distinct, `subsorts` compares them in neither direction, and no sort is
below both. -/
theorem order_cc : tC ≠ tS ∧ (c.le tC tS || c.le tS tC) = false ∧ c.lowerBounds tC tS = [] ∧
    c.lowerBounds tS tC = [] := by decide +kernel

/-- Whether a generator is the injection of the sort `a`. -/
def injOfB (a : Srt) : Gen → Bool
  | .inj s => s == a
  | _ => false

theorem cir_mem_inj {l : List Gen} {a : Srt} (h : l.any (injOfB a) = true) : Gen.inj a ∈ l := by
  obtain ⟨g, hg, hm⟩ := List.any_eq_true.mp h
  cases g with
  | ctor k => simp [injOfB] at hm
  | inj s => rw [← beq_iff_eq.mp hm]; exact hg

/-- KItem is a constructor sort, the injections of TCell and TCellSet are generators of it (no
open generator), and neither is function-overloaded. -/
theorem gens_ccB : (consSorts c).contains Srt.kitem = true ∧
    ((c.gens Srt.kitem).filter (!c.isOpenGen ·)).any (injOfB tC) = true ∧
    ((c.gens Srt.kitem).filter (!c.isOpenGen ·)).any (injOfB tS) = true ∧
    c.fnOvl (Gen.inj tC) = false ∧ c.fnOvl (Gen.inj tS) = false := by decide +kernel

theorem gens_cc : Srt.kitem ∈ consSorts c ∧ Gen.inj tC ∈ (c.gens Srt.kitem).filter (!c.isOpenGen ·) ∧
    Gen.inj tS ∈ (c.gens Srt.kitem).filter (!c.isOpenGen ·) ∧
    c.fnOvl (Gen.inj tC) = false ∧ c.fnOvl (Gen.inj tS) = false :=
  ⟨List.contains_iff_mem.mp gens_ccB.1, cir_mem_inj gens_ccB.2.1, cir_mem_inj gens_ccB.2.2.1,
    gens_ccB.2.2.2.1, gens_ccB.2.2.2.2⟩

/-- A value of TCell: `<t>(<v>(0), <p>(go()))`. -/
noncomputable def cell0 : GroundTerm :=
  .ctor (nRegSyms + c.symNames.idxOf "Lbl'-LT-'t'-GT-'")
    [.ctor (nRegSyms + c.symNames.idxOf "Lbl'-LT-'v'-GT-'") [.dv Srt.int (.int 0)],
     .ctor (nRegSyms + c.symNames.idxOf "Lbl'-LT-'p'-GT-'") [.ctor (nRegSyms + c.symNames.idxOf "Lblgo") []]]

theorem cell0_sort : c.sortOf cell0 = some tC := by decide +kernel

/-! ## The two translations -/

/-- The variables of sentence 31 and of the INJ axiom. -/
def kR : VarKey := .sortVar "R"
def kVal : VarKey := .evar "Val" (KoreAML.srt "TCellSet")
def kFrom : VarKey := .evar "From" (KoreAML.srt "TCell")
def kS1 : VarKey := .sortVar "S1"
def kS2 : VarKey := .sortVar "S2"
def kS3 : VarKey := .sortVar "S3"
def kT : VarKey := .evar "T" (.var ⟨⟨⟨"S1"⟩⟩⟩)

noncomputable def tbl31 : VarTable := KoreAML.tableOf U.ax31.ax.sortVars U.ax31.ax.pattern
noncomputable def tbl3 : VarTable := KoreAML.tableOf J.ax3.ax.sortVars J.ax3.ax.pattern

/-- `inj{A,B}` applied to `X`, as the translation writes an application with two sort arguments. -/
def injP3 (A B X : KoreAML.P) : KoreAML.P := KoreAML.appList (KoreAML.sym (.symbol "inj")) [A, B, X]

theorem trS31 : (trS U.ax31).pat = (trAxiom [] [] U.ax31).pat := by decide +kernel
theorem trS3 : (trS J.ax3).pat = (trAxiom [] [] J.ax3).pat := by decide +kernel

theorem vars31 : (U.ax31.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax31.ax.pattern).eraseDups =
    [kR, kFrom] := by decide +kernel
theorem sort31 : KoreAML.sortOf [] U.ax31.ax.pattern = some KoreAML.R := by decide +kernel
theorem mem31 : kR ∈ tbl31 ∧ kFrom ∈ tbl31 ∧ kVal ∈ tbl31 ∧ tbl31.ev kVal ≠ tbl31.ev kR ∧
    tbl31.ev kVal ≠ tbl31.ev kFrom := by decide +kernel

/-- Sentence 31 as the translation writes it: `∃Val:TCellSet. Val =^R_TCellSet inj{TCell,TCellSet}(From)`. -/
theorem pat31 : KoreAML.tr ⟨tbl31, []⟩ U.ax31.ax.pattern =
    KoreAML.sExists (tbl31.ev kVal) (KoreAML.sym (.sort ("Sort" ++ "TCellSet")))
      (KoreAML.sEquals (KoreAML.sym (.sort ("Sort" ++ "TCellSet"))) (.evar (tbl31.ev kR)) (.evar (tbl31.ev kVal))
        (injP3 (KoreAML.sym (.sort ("Sort" ++ "TCell"))) (KoreAML.sym (.sort ("Sort" ++ "TCellSet")))
          (.evar (tbl31.ev kFrom)))) := by decide +kernel

theorem vars3 : (J.ax3.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] J.ax3.ax.pattern).eraseDups =
    [kS1, kS2, kS3, kR, kT] := by decide +kernel
theorem sort3 : KoreAML.sortOf [] J.ax3.ax.pattern = some KoreAML.R := by decide +kernel
theorem mem3 : kS1 ∈ tbl3 ∧ kS2 ∈ tbl3 ∧ kS3 ∈ tbl3 ∧ kR ∈ tbl3 ∧ kT ∈ tbl3 := by decide +kernel

/-- The INJ axiom as the translation writes it: `inj{S2,S3}(inj{S1,S2}(T)) =^R_S3 inj{S1,S3}(T)`,
with the sort variables S1, S2, S3, R. -/
theorem pat3 : KoreAML.tr ⟨tbl3, []⟩ J.ax3.ax.pattern =
    KoreAML.sEquals (.evar (tbl3.ev kS3)) (.evar (tbl3.ev kR))
      (injP3 (.evar (tbl3.ev kS2)) (.evar (tbl3.ev kS3))
        (injP3 (.evar (tbl3.ev kS1)) (.evar (tbl3.ev kS2)) (.evar (tbl3.ev kT))))
      (injP3 (.evar (tbl3.ev kS1)) (.evar (tbl3.ev kS3)) (.evar (tbl3.ev kT))) := by decide +kernel

section Refute
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- `inj{A,B}(X)`, where `A` and `B` denote the sorts named `nA` and `nB`: the elements the
generator `inj{nA}` of `nB` builds from an element of `X`. -/
theorem cir_injP3 {e : Valuation M} {A B X : KoreAML.P} {nA nB : String} {σA σB : M}
    (hA : ∀ a, A.interpret I e a ↔ a = σA) (hB : ∀ a, B.interpret I e a ↔ a = σB)
    (hA' : ∀ a, I.evalSymb (.sort ("Sort" ++ nA)) a ↔ a = σA)
    (hB' : ∀ a, I.evalSymb (.sort ("Sort" ++ nB)) a ↔ a = σB) (m : M) :
    (injP3 A B X).interpret I e m ↔ ∃ x, X.interpret I e x ∧ GS I nB (.inj nA) [x] m := by
  simp only [injP3, GS, genHead, KoreAML.Cons.sortP, KoreAML.appList, KoreAML.interp_app,
    KoreAML.interp_sym, AppE, hA, hB, hA', hB']
  constructor
  · rintro ⟨a, x, ⟨a1, b1, ⟨a2, b2, h2, rfl, h21⟩, rfl, h1⟩, hx, hm⟩
    exact ⟨x, hx, a, ⟨a1, _, ⟨a2, _, h2, rfl, h21⟩, rfl, h1⟩, m, hm, rfl⟩
  · rintro ⟨x, hx, a, ⟨a1, b1, ⟨a2, b2, h2, rfl, h21⟩, rfl, h1⟩, a', hm, rfl⟩
    exact ⟨a, x, ⟨a1, _, ⟨a2, _, h2, rfl, h21⟩, rfl, h1⟩, hx, hm⟩

variable (H : HookParams) (hI : I ⊧ᴵP Γ (cH H))
include hI

/-- **Sentence 31 at an element.** For every element `e` of TCell there is an element `s` of
TCellSet that `inj{TCell,TCellSet}(e)` contains. -/
theorem text31 (h31 : I ⊧ᴵ tr31) {σa σb : M}
    (ha : ∀ a, I.evalSymb (.sort ("Sort" ++ "TCell")) a ↔ a = σa) (ha' : KoreAML.IsSort I σa)
    (hb : ∀ a, I.evalSymb (.sort ("Sort" ++ "TCellSet")) a ↔ a = σb) (hb' : KoreAML.IsSort I σb)
    {e : M} (he : KoreAML.Inh I σa e) :
    ∃ s, KoreAML.Inh I σb s ∧ GS I "TCellSet" (.inj "TCell") [e] s := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold tr31 at h31
  rw [trS31] at h31
  obtain ⟨hmR, hmF, hmV, hVR, hVF⟩ := mem31
  let val : VarKey → M := fun
    | .sortVar _ => σa
    | _ => e
  let e' : Valuation M := valOf tbl31 val
  have hRv : ∀ b, (KoreAML.trSort tbl31 KoreAML.R).interpret I e' b ↔ b = σa := fun b => by
    rw [trSort_R, KoreAML.interp_evar]; exact iff_of_eq (congrArg _ (valOf_ev hmR))
  have hFv : e'.evalEvar (tbl31.ev kFrom) = e := valOf_ev hmF
  have hg : ∀ k ∈ (U.ax31.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax31.ax.pattern).eraseDups,
      ∀ m, (KoreAML.guardOf tbl31 k).interpret I e' m := by
    intro k hk m
    rw [vars31] at hk
    rcases List.mem_cons.mp hk with rfl | hk
    · rw [kR, KoreAML.interp_guard_sortVar hD]
      show KoreAML.IsSort I (e'.evalEvar (tbl31.ev kR))
      rw [valOf_ev hmR]; exact ha'
    · rw [List.mem_singleton.mp hk, kFrom, KoreAML.interp_guard_evar hD, trSort_srt]
      show (KoreAML.inhOf _).interpret I e' (e'.evalEvar (tbl31.ev kFrom))
      rw [hFv, KoreAML.interp_inhOf_of (fun a => KoreAML.interp_sym.trans (ha a))]; exact he
  have hP := (KoreAML.trAxiom_at hD h31 e' hg e).mpr (by
    rw [sort31]
    show (KoreAML.inhOf (KoreAML.trSort tbl31 KoreAML.R)).interpret I e' e
    rw [KoreAML.interp_inhOf_of hRv]; exact he)
  have hP : (KoreAML.tr ⟨tbl31, []⟩ U.ax31.ax.pattern).interpret I e' e := hP
  rw [pat31, KoreAML.interp_sExists_elem hD] at hP
  obtain ⟨s, hs, hEq⟩ := hP
  have hbS : ∀ (e0 : Valuation M) a, (KoreAML.sym (.sort ("Sort" ++ "TCellSet"))).interpret I e0 a ↔ a = σb :=
    fun _ a => KoreAML.interp_sym.trans (hb a)
  have haS : ∀ (e0 : Valuation M) a, (KoreAML.sym (.sort ("Sort" ++ "TCell"))).interpret I e0 a ↔ a = σa :=
    fun _ a => KoreAML.interp_sym.trans (ha a)
  have hsI : KoreAML.Inh I σb s := (KoreAML.interp_inhOf_of (hbS _)).mp hs
  have hR' : ∀ a, (Pattern.evar (tbl31.ev kR) : KoreAML.P).interpret I (KoreAML.updE e' (tbl31.ev kVal) s) a ↔ a = σa := by
    intro a
    rw [KoreAML.interp_evar]
    show a = Function.update e'.evalEvar (tbl31.ev kVal) s (tbl31.ev kR) ↔ _
    rw [Function.update_noteq hVR.symm, valOf_ev hmR]; exact Iff.rfl
  rw [KoreAML.interp_sEquals hD hc (hbS _) hR' hb' ha'] at hEq
  have hinj := (hEq.2 s hsI).mp (by
    rw [KoreAML.interp_evar]
    show s = Function.update e'.evalEvar (tbl31.ev kVal) s (tbl31.ev kVal)
    exact (Function.update_same (tbl31.ev kVal) s e'.evalEvar).symm)
  rw [cir_injP3 (haS _) (hbS _) ha hb] at hinj
  obtain ⟨x, hx, hgs⟩ := hinj
  rw [KoreAML.interp_evar] at hx
  have hx' : x = e := by
    rw [hx]
    show Function.update e'.evalEvar (tbl31.ev kVal) s (tbl31.ev kFrom) = e
    rw [Function.update_noteq hVF.symm, hFv]
  exact ⟨s, hsI, hx' ▸ hgs⟩

/-- **The INJ axiom at (TCell, TCellSet, KItem), at an element.** For an element `e` of TCell and
an element `z` of KItem: `z` is in `inj{TCellSet,KItem}(inj{TCell,TCellSet}(e))` exactly when it is
in `inj{TCell,KItem}(e)`. The sentence is read at the valuation S1 ↦ TCell, S2 ↦ TCellSet,
S3 ↦ KItem, R ↦ TCell, T ↦ e. -/
theorem textTri (hT : I ⊧ᴵ trTri) {σa σb σN : M}
    (ha : ∀ a, I.evalSymb (.sort ("Sort" ++ "TCell")) a ↔ a = σa) (ha' : KoreAML.IsSort I σa)
    (hb : ∀ a, I.evalSymb (.sort ("Sort" ++ "TCellSet")) a ↔ a = σb) (hb' : KoreAML.IsSort I σb)
    (hN : ∀ a, I.evalSymb (.sort ("Sort" ++ "KItem")) a ↔ a = σN) (hN' : KoreAML.IsSort I σN)
    {e : M} (he : KoreAML.Inh I σa e) (z : M) (hz : KoreAML.Inh I σN z) :
    (∃ x, GS I "TCellSet" (.inj "TCell") [e] x ∧ GS I "KItem" (.inj "TCellSet") [x] z) ↔
      GS I "KItem" (.inj "TCell") [e] z := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trTri at hT
  rw [trS3] at hT
  obtain ⟨m1, m2, m3, mR, mT⟩ := mem3
  let val : VarKey → M := fun k =>
    if k = kS2 then σb else if k = kS3 then σN else if k = kT then e else σa
  let e' : Valuation M := valOf tbl3 val
  have v1 : e'.evalEvar (tbl3.ev kS1) = σa := by rw [valOf_ev m1]; simp [val, kS1, kS2, kS3, kT]
  have v2 : e'.evalEvar (tbl3.ev kS2) = σb := by rw [valOf_ev m2]; simp [val]
  have v3 : e'.evalEvar (tbl3.ev kS3) = σN := by rw [valOf_ev m3]; simp [val, kS2, kS3]
  have vR : e'.evalEvar (tbl3.ev kR) = σa := by rw [valOf_ev mR]; simp [val, kR, kS2, kS3, kT]
  have vT : e'.evalEvar (tbl3.ev kT) = e := by rw [valOf_ev mT]; simp [val, kS2, kS3, kT]
  have h1 : ∀ a, (Pattern.evar (tbl3.ev kS1) : KoreAML.P).interpret I e' a ↔ a = σa := fun a => by
    rw [KoreAML.interp_evar, v1]
  have h2 : ∀ a, (Pattern.evar (tbl3.ev kS2) : KoreAML.P).interpret I e' a ↔ a = σb := fun a => by
    rw [KoreAML.interp_evar, v2]
  have h3 : ∀ a, (Pattern.evar (tbl3.ev kS3) : KoreAML.P).interpret I e' a ↔ a = σN := fun a => by
    rw [KoreAML.interp_evar, v3]
  have hR : ∀ a, (Pattern.evar (tbl3.ev kR) : KoreAML.P).interpret I e' a ↔ a = σa := fun a => by
    rw [KoreAML.interp_evar, vR]
  have hg : ∀ k ∈ (J.ax3.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] J.ax3.ax.pattern).eraseDups,
      ∀ m, (KoreAML.guardOf tbl3 k).interpret I e' m := by
    intro k hk m
    rw [vars3] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · rw [kS1, KoreAML.interp_guard_sortVar hD]
      show KoreAML.IsSort I (e'.evalEvar (tbl3.ev kS1)); rw [v1]; exact ha'
    · rw [kS2, KoreAML.interp_guard_sortVar hD]
      show KoreAML.IsSort I (e'.evalEvar (tbl3.ev kS2)); rw [v2]; exact hb'
    · rw [kS3, KoreAML.interp_guard_sortVar hD]
      show KoreAML.IsSort I (e'.evalEvar (tbl3.ev kS3)); rw [v3]; exact hN'
    · rw [kR, KoreAML.interp_guard_sortVar hD]
      show KoreAML.IsSort I (e'.evalEvar (tbl3.ev kR)); rw [vR]; exact ha'
    · rw [kT, KoreAML.interp_guard_evar hD]
      show (KoreAML.inhOf (.evar (tbl3.ev kS1))).interpret I e' (e'.evalEvar (tbl3.ev kT))
      rw [vT, KoreAML.interp_inhOf_of h1]; exact he
  have hP := (KoreAML.trAxiom_at hD hT e' hg e).mpr (by
    rw [sort3]
    show (KoreAML.inhOf (.evar (tbl3.ev kR))).interpret I e' e
    rw [KoreAML.interp_inhOf_of hR]; exact he)
  have hP : (KoreAML.tr ⟨tbl3, []⟩ J.ax3.ax.pattern).interpret I e' e := hP
  rw [pat3, KoreAML.interp_sEquals hD hc h3 hR hN' ha'] at hP
  have h := hP.2 z hz
  rw [cir_injP3 h2 h3 hb hN, cir_injP3 h1 h3 ha hN] at h
  simp only [cir_injP3 h1 h2 ha hb, KoreAML.interp_evar, vT, exists_eq_left] at h
  exact h

end Refute

/-- **Sentence 31 and the INJ axiom have no model with Γ, for every H** (form (r)). `tr31` is the
translation of sentence 31 (the subsort sentence of TCell into TCellSet) and `trTri` the
translation of the prelude's axiom of module INJ, both as `Theory.ofDefinition kore` writes them;
`trTri` is the sentence over its sort variables S1, S2, S3, R, and the proof reads it at S1 = TCell,
S2 = TCellSet, S3 = KItem. A value of TCell gives an element `e` (ΓDomains); 31 gives `e` an
element `s` of TCellSet with `s ∈ inj{TCell,TCellSet}(e)`; the INJ axiom with Γ's Cons-Fun of the
two injections into KItem makes `inj{TCellSet,KItem}(s)` and `inj{TCell,KItem}(e)` one element,
which Γ's Cons-Dist of the two injections refutes (`Faithful.inj_apart_no_model`). -/
theorem cellcoll_subsort_refuted (H : HookParams) :
    ¬ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      (I ⊧ᴵP Γc (cH H)) ∧ (I ⊧ᴵ tr31) ∧ (I ⊧ᴵ trTri) := by
  rintro ⟨M, _, I, hIc, h31, hT⟩
  have hI : I ⊧ᴵP Γ (cH H) := fun φ hφ => hIc φ (Or.inl hφ)
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hnC : (cH H).sortName tC = "TCell" := sort_names.1
  have hnS : (cH H).sortName tS = "TCellSet" := sort_names.2.1
  have hnK : (cH H).sortName Srt.kitem = "KItem" := sort_names.2.2
  obtain ⟨σa, ha, ha'⟩ := sortSing (c := cH H) hI sorts_numbered.1
  obtain ⟨σb, hb, hb'⟩ := sortSing (c := cH H) hI sorts_numbered.2.1
  obtain ⟨σN, hN, hN'⟩ := sortSing (c := cH H) hI sorts_numbered.2.2
  rw [hnC] at ha; rw [hnS] at hb; rw [hnK] at hN
  have inS_a : ∀ x, InS I "TCell" x ↔ KoreAML.Inh I σa x := fun x =>
    KoreAML.interp_inhOf_of (fun a => KoreAML.interp_sym.trans (ha a))
  have inS_b : ∀ x, InS I "TCellSet" x ↔ KoreAML.Inh I σb x := fun x =>
    KoreAML.interp_inhOf_of (fun a => KoreAML.interp_sym.trans (hb a))
  have inS_N : ∀ x, InS I "KItem" x ↔ KoreAML.Inh I σN x := fun x =>
    KoreAML.interp_inhOf_of (fun a => KoreAML.interp_sym.trans (hN a))
  have single : ∀ (n : String) (x : M), InS I n x →
      ∀ (i : Nat) (x0 : M) (s0 : String), [x][i]? = some x0 → [n][i]? = some s0 → InS I s0 x0 := by
    intro n x hx i x0 s0 h1 h2
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
      subst h1; subst h2; exact hx
    | succ n => simp at h1
  obtain ⟨-, hes⟩ := elemOf_spec hI (v := cell0) (s := tC)
    (by rw [Semantics.sortOf_withHooks _ _ noRaw]; exact cell0_sort) KoreAML.val0
  rw [hnC] at hes
  obtain ⟨hgN, hga, hgb, hfa, hfb⟩ := gens_cc
  obtain ⟨hne, hab, hlb, hlb'⟩ := order_cc
  refine inj_apart_no_model (c := cH H) hI (N := Srt.kitem) (a := tC) (b := tS) hgN hga hgb hne hab hlb hlb'
    ⟨_, by rw [hnC]; exact hes⟩ ?_
  intro x hx
  rw [hnC] at hx
  obtain ⟨s, hsI, hs⟩ := text31 H hI h31 ha ha' hb hb' ((inS_a x).mp hx)
  have hsS : InS I "TCellSet" s := (inS_b s).mpr hsI
  refine ⟨s, by rw [hnS]; exact hsS, ?_⟩
  rw [hnK, hnS, hnC]
  obtain ⟨y', hy'K, hy'⟩ := gen_fun (c := cH H) hI hgN hgb hfb (xs := [s]) rfl
    (fun i x0 s0 h1 h2 => single _ s (by rw [hnS]; exact hsS) i x0 s0 h1 h2)
  obtain ⟨y, -, hy⟩ := gen_fun (c := cH H) hI hgN hga hfa (xs := [x]) rfl
    (fun i x0 s0 h1 h2 => single _ x (by rw [hnC]; exact hx) i x0 s0 h1 h2)
  have hy'2 : ∀ m, GS I "KItem" (.inj "TCellSet") [s] m ↔ m = y' := by
    intro m; have := hy' m
    rw [show Gen.toK (cH H) (Gen.inj tS) = .inj ((cH H).sortName tS) from rfl, hnS, hnK] at this
    exact this
  have hy2 : ∀ m, GS I "KItem" (.inj "TCell") [x] m ↔ m = y := by
    intro m; have := hy m
    rw [show Gen.toK (cH H) (Gen.inj tC) = .inj ((cH H).sortName tC) from rfl, hnC, hnK] at this
    exact this
  rw [hnK] at hy'K
  have hyy : y' = y := (hy2 y').mp ((textTri H hI hT ha ha' hb hb' hN hN' ((inS_a x).mp hx) y'
    ((inS_N y').mp hy'K)).mp ⟨s, hs, (hy'2 y').mpr rfl⟩)
  intro m
  rw [hy'2 m, hy2 m, hyy]


end KCore.TieE1Starinit

#check @KCore.Faithful.inj_apart_of_incomparable
#check @KCore.TieE1Starinit.cellcoll_subsort_refuted
#print axioms KCore.TieE1Starinit.ax3_text
#print axioms KCore.TieE1Starinit.ax31_text
#print axioms KCore.Faithful.inj_apart_of_incomparable
#print axioms KCore.Faithful.inj_apart_no_model
#print axioms KCore.TieE1Starinit.text31
#print axioms KCore.TieE1Starinit.textTri
#print axioms KCore.TieE1Starinit.cellcoll_subsort_refuted
