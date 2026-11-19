/-
  STRING-BUFFER-IN-K's three equations (domains.md 1963-1965) on the text of the fixture
  e6-string-buffer (`f2-examples/e6sb.kompile.kore`), in the direction E, under the interpretations
  H that give the three parameter symbols the String operations. Run from the package root:
  `lake env lean -j1 test/LibEvStrBufEqs.lean`.

  The reading has `.StringBuffer` (294), `_+String_` on StringBuffer (295) and `StringBuffer2String`
  (296) as parameter symbols without implementation (`LibEvDeclsStrBuf.params_sb`), so Γ states
  their values only as the interpretation's (`Semantics.paramVal`): each equation is a hypothesis on
  H (owed-sentence rule item 3, class parameter lemma).
  - `sbUnitEq`, `sbConcatEq`, `sbToStrEq`: the three conditions on H, stated at String literals
    (`strV`): `.StringBuffer` is `""` injected into StringBuffer, `SB +String S` is the injected
    concatenation of the String SB and S, `StringBuffer2String` of an injected String is that String.
  - `ev179` (1964, `.StringBuffer => ""`), `ev185` (1965, `StringBuffer2String(S) => S`), `ev195`
    (1963, `SB +String S => SB +String S`): each is entailed at values for every H meeting its
    condition (`LibEv.FnEqn.entailedP`, its terms applying the parameter symbol and the injection
    `inj{String, StringBuffer}`; the values of the String variables are String literals, `shapesOK`).
  - `Hsb`, `hsb_meets`: an interpretation meeting the three conditions.
  - `unit_none`, `toStr_none`: at `HookParams.none` the left sides of 1964 and 1965 have no value
    while their right sides have one (`LibEv.valP`), so the equations' function form fails there.
    These are statements about the values of the sides, not about models of Γ.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvStrBufEqs

open KCore ML Faithful KoreAML LibEv

kore_term kore from "f2-examples/e6sb.kompile.kore"
definition_of defn from "f2-examples/e6sb.kompile.kore"
user_axioms U from "f2-examples/e6sb.kompile.kore" module "E6-STRING-BUFFER"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem userAxioms_eq : kore.axiomDecls.filter (·.module == "E6-STRING-BUFFER") = U.all := by kernel_rfl

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The sort StringBuffer. -/
abbrev sbSrt : Srt := 27

/-- A String injected into StringBuffer. -/
def sbInj (v : GroundTerm) : GroundTerm := .inj Srt.string sbSrt v

theorem names_sb : c.sortName sbSrt = "StringBuffer" ∧
    [294, 295, 296].map c.symName =
      ["Lbl'Stop'StringBuffer'Unds'STRING-BUFFER-IN-K'Unds'StringBuffer",
       "Lbl'UndsPlus'String'UndsUnds'STRING-BUFFER-IN-K'Unds'StringBuffer'Unds'StringBuffer'Unds'String",
       "LblStringBuffer2String'LParUndsRParUnds'STRING-BUFFER-IN-K'Unds'String'Unds'StringBuffer"] := by
  decide +kernel

/-! ## The conditions on H -/

/-- **domains.md 1964** at H: `.StringBuffer` is `""` injected into StringBuffer. -/
def sbUnitEq (H : HookParams) : Prop := H.app 294 [] = some (sbInj (strV []))

/-- **domains.md 1963** at H: `SB +String S` at the String literals x and y (x injected) is
x ++ y injected. -/
def sbConcatEq (H : HookParams) : Prop :=
  ∀ x y : List Char, H.app 295 [sbInj (strV x), strV y] = some (sbInj (strV (x ++ y)))

/-- **domains.md 1965** at H: `StringBuffer2String` of the String literal x injected is x. -/
def sbToStrEq (H : HookParams) : Prop := ∀ x : List Char, H.app 296 [sbInj (strV x)] = some (strV x)

/-- The interpretation reading the three as the String operations. -/
def Hsb : HookParams := ⟨fun f vs => match f, vs with
  | 294, [] => some (sbInj (strV []))
  | 295, [.inj _ _ v, w] => (asStr v).bind fun x => (asStr w).map fun y => sbInj (strV (x ++ y))
  | 296, [.inj _ _ v] => some v
  | _, _ => none⟩

theorem asStr_strV (cs : List Char) : asStr (strV cs) = some cs := by
  simp [asStr, strV, String.toList_ofList]

theorem hsb_meets : sbUnitEq Hsb ∧ sbConcatEq Hsb ∧ sbToStrEq Hsb := by
  refine ⟨rfl, fun x y => ?_, fun x => rfl⟩
  show ((asStr (strV x)).bind fun x => (asStr (strV y)).map fun y => sbInj (strV (x ++ y))) = _
  rw [asStr_strV, asStr_strV]; rfl

/-! ## The equations -/

/-- 1964: `.StringBuffer => ""`. -/
def E179 : FnEqn :=
  { vars := [], f := 294, pats := [], s := sbSrt, req := none,
    rhs := .inj Srt.string sbSrt (.dv Srt.string (.tok "")) }

/-- 1965: `StringBuffer2String(inj(S)) => S`. -/
def E185 : FnEqn :=
  { vars := [("VarS", Srt.string)], f := 296, pats := [(sbSrt, .inj Srt.string sbSrt (.var 0), none)],
    s := Srt.string, req := none, rhs := .var 0 }

/-- 1963: `inj(SB) +String S => inj(SB +String S)`. -/
def E195 : FnEqn :=
  { vars := [("VarSB", Srt.string), ("VarS", Srt.string)], f := 295,
    pats := [(sbSrt, .inj Srt.string sbSrt (.var 0), none), (Srt.string, .var 1, none)],
    s := sbSrt, req := none, rhs := .inj Srt.string sbSrt (.app stringConcat [.var 0, .var 1]) }

kernel_rfl pattern179 : ∀ H : HookParams, U.ax179.ax.pattern = E179.patternP (cH H)
kernel_rfl pattern185 : ∀ H : HookParams, U.ax185.ax.pattern = E185.patternP (cH H)
kernel_rfl pattern195 : ∀ H : HookParams, U.ax195.ax.pattern = E195.patternP (cH H)
kernel_rfl typed179 : ∀ H : HookParams, E179.typedP (cH H) = true
kernel_rfl typed185 : ∀ H : HookParams, E185.typedP (cH H) = true
kernel_rfl typed195 : ∀ H : HookParams, E195.typedP (cH H) = true

theorem sortVars_R : [U.ax179, U.ax185, U.ax195].all (·.ax.sortVars == [KoreAML.Rv]) = true := by
  decide +kernel

-- Γ's value of each of the three at H: H's answer where it has the declared result sort.
kernel_rfl appVal294 : ∀ (H : HookParams) (ws : List GroundTerm),
  appValP (cH H) 294 ws = (H.app 294 ws).filter fun v => (cH H).sortOf v == some sbSrt
kernel_rfl appVal295 : ∀ (H : HookParams) (ws : List GroundTerm),
  appValP (cH H) 295 ws = (H.app 295 ws).filter fun v => (cH H).sortOf v == some sbSrt
kernel_rfl appVal296 : ∀ (H : HookParams) (ws : List GroundTerm),
  appValP (cH H) 296 ws = (H.app 296 ws).filter fun v => (cH H).sortOf v == some Srt.string
kernel_rfl appValConcat : ∀ (H : HookParams) (ws : List GroundTerm),
  appValP (cH H) stringConcat ws = (cH H).hv stringConcat ws
kernel_rfl sortOf_sbInj : ∀ (H : HookParams) (cs : List Char), (cH H).sortOf (sbInj (strV cs)) = some sbSrt

kernel_rfl vkey_withHooks : ∀ (H : HookParams) (vars : Vars) (i : Nat), vkey (cH H) vars i = vkey c vars i

theorem free179 : ∀ i, i < E179.av.length → vkey c E179.av i ∈ KoreAML.freeOf [] U.ax179.ax.pattern := by
  decide +kernel
theorem free185 : ∀ i, i < E185.av.length → vkey c E185.av i ∈ KoreAML.freeOf [] U.ax185.ax.pattern := by
  decide +kernel
theorem free195 : ∀ i, i < E195.av.length → vkey c E195.av i ∈ KoreAML.freeOf [] U.ax195.ax.pattern := by
  decide +kernel

theorem strV_toList (t : String) : strV t.toList = .dv Srt.string (.tok t) := by
  simp [strV, String.ofList_toList]

/-! ## The sides' values -/

theorem holds179 (H : HookParams) (hH : sbUnitEq H) : E179.HoldsP (cH H) := by
  intro σ _ _ _
  unfold sbUnitEq at hH
  show valP (cH H) σ (.app 294 []) = valP (cH H) σ (.inj Srt.string sbSrt (.dv Srt.string (.tok "")))
  simp only [valP, valPList, allSome, Option.bind_some, Option.map_some, appVal294]
  rw [hH]
  simp only [Option.filter, sortOf_sbInj, beq_self_eq_true, ↓reduceIte]
  rfl

theorem holds185 (H : HookParams) (hH : sbToStrEq H) : E185.HoldsP (cH H) := by
  intro σ hσ _ hm
  obtain ⟨v0, h0, hs0⟩ := hσ 0 ("VarS", Srt.string) rfl
  obtain ⟨t0, rfl⟩ := shape_string (shapesOKH H) hs0
  obtain ⟨hm1, -, -⟩ := hm
  have h1 : σ.lookup 1 = some (.inj Srt.string sbSrt (.dv Srt.string (.tok t0))) :=
    hm1.symm.trans (by show valP (cH H) σ (.inj Srt.string sbSrt (.var 0)) = _; rw [valP, valP, h0]; rfl)
  show valP (cH H) σ (.app 296 [.var 1]) = valP (cH H) σ (.var 0)
  have h2 := hH t0.toList
  rw [strV_toList] at h2
  simp only [valP, valPList, h1, h0, allSome, Option.bind_some, Option.map_some, appVal296]
  rw [show sbInj (.dv Srt.string (.tok t0)) = .inj Srt.string sbSrt (.dv Srt.string (.tok t0)) from rfl] at h2
  rw [h2]
  simp [Option.filter, hs0]

theorem holds195 (H : HookParams) (hH : sbConcatEq H) : E195.HoldsP (cH H) := by
  intro σ hσ _ hm
  obtain ⟨v0, h0, hs0⟩ := hσ 0 ("VarSB", Srt.string) rfl
  obtain ⟨v1, h1, hs1⟩ := hσ 1 ("VarS", Srt.string) rfl
  obtain ⟨t0, rfl⟩ := shape_string (shapesOKH H) hs0
  obtain ⟨t1, rfl⟩ := shape_string (shapesOKH H) hs1
  obtain ⟨hm1, -, hm2, -, -⟩ := hm
  have h2' : σ.lookup 2 = some (.inj Srt.string sbSrt (.dv Srt.string (.tok t0))) :=
    hm1.symm.trans (by show valP (cH H) σ (.inj Srt.string sbSrt (.var 0)) = _; rw [valP, valP, h0]; rfl)
  have h3' : σ.lookup 3 = some (.dv Srt.string (.tok t1)) :=
    hm2.symm.trans (by show valP (cH H) σ (.var 1) = _; rw [valP, h1])
  show valP (cH H) σ (.app 295 [.var 2, .var 3]) =
    valP (cH H) σ (.inj Srt.string sbSrt (.app stringConcat [.var 0, .var 1]))
  have h2 := hH t0.toList t1.toList
  rw [strV_toList, strV_toList] at h2
  have hc := st_hv_concat' (c := cH H) t0.toList t1.toList
  rw [strV_toList, strV_toList] at hc
  simp only [valP, valPList, h2', h3', h0, h1, allSome, Option.bind_some, Option.map_some,
    appVal295, appValConcat]
  rw [show sbInj (.dv Srt.string (.tok t0)) = .inj Srt.string sbSrt (.dv Srt.string (.tok t0)) from rfl] at h2
  rw [h2, hc]
  simp only [Option.filter, sortOf_sbInj, beq_self_eq_true, ↓reduceIte, Option.map_some]
  rfl

/-! ## Entailed at values -/

/-- **1964** `.StringBuffer => ""`, entailed at values for every H meeting `sbUnitEq`. -/
theorem ev179 (H : HookParams) (hH : sbUnitEq H) : EntailsAtValues (cH H) U.ax179 (trS U.ax179).pat := by
  rw [(by decide +kernel : (trS U.ax179).pat = (trAxiom [] [] U.ax179).pat)]
  exact FnEqn.entailedP (coreOKH H) E179 (typed179 H) (holds179 H hH) U.ax179 (pattern179 H)
    (by decide +kernel) (fun i hi => by rw [vkey_withHooks]; exact free179 i hi)

/-- **1965** `StringBuffer2String(S) => S`, entailed at values for every H meeting `sbToStrEq`. -/
theorem ev185 (H : HookParams) (hH : sbToStrEq H) : EntailsAtValues (cH H) U.ax185 (trS U.ax185).pat := by
  rw [(by decide +kernel : (trS U.ax185).pat = (trAxiom [] [] U.ax185).pat)]
  exact FnEqn.entailedP (coreOKH H) E185 (typed185 H) (holds185 H hH) U.ax185 (pattern185 H)
    (by decide +kernel) (fun i hi => by rw [vkey_withHooks]; exact free185 i hi)

/-- **1963** `SB +String S => SB +String S`, entailed at values for every H meeting `sbConcatEq`. -/
theorem ev195 (H : HookParams) (hH : sbConcatEq H) : EntailsAtValues (cH H) U.ax195 (trS U.ax195).pat := by
  rw [(by decide +kernel : (trS U.ax195).pat = (trAxiom [] [] U.ax195).pat)]
  exact FnEqn.entailedP (coreOKH H) E195 (typed195 H) (holds195 H hH) U.ax195 (pattern195 H)
    (by decide +kernel) (fun i hi => by rw [vkey_withHooks]; exact free195 i hi)

/-- At `Hsb` all three are entailed at values. -/
theorem ev_Hsb : EntailsAtValues (cH Hsb) U.ax179 (trS U.ax179).pat ∧
    EntailsAtValues (cH Hsb) U.ax185 (trS U.ax185).pat ∧ EntailsAtValues (cH Hsb) U.ax195 (trS U.ax195).pat :=
  ⟨ev179 Hsb hsb_meets.1, ev185 Hsb hsb_meets.2.2, ev195 Hsb hsb_meets.2.1⟩

/-! ## At `HookParams.none` -/

/-- At `HookParams.none`, 1964's left side has no value and its right side has one. -/
theorem unit_none (σ : Subst) :
    valP (cH HookParams.none) σ E179.lhs = none ∧ (valP (cH HookParams.none) σ E179.rhs).isSome := by
  refine ⟨?_, rfl⟩
  show valP (cH HookParams.none) σ (.app 294 []) = none
  simp only [valP, valPList, allSome, Option.bind_some, appVal294]
  rfl

/-- At `HookParams.none`, 1965's left side has no value at a substitution matching its pattern,
while its right side has the value of `S`. -/
theorem toStr_none (σ : Subst) (v : GroundTerm) (h0 : σ.lookup 0 = some v)
    (h1 : σ.lookup 1 = some (sbInj v)) :
    valP (cH HookParams.none) σ E185.lhs = none ∧ valP (cH HookParams.none) σ E185.rhs = some v := by
  refine ⟨?_, by show valP _ σ (.var 0) = _; rw [valP, h0]⟩
  show valP (cH HookParams.none) σ (.app 296 [.var 1]) = none
  simp only [valP, valPList, h1, allSome, Option.bind_some, Option.map_some, appVal296]
  rfl

end KCore.LibEvStrBufEqs

/-- info: 'KCore.LibEvStrBufEqs.ev179' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrBufEqs.ev179
/-- info: 'KCore.LibEvStrBufEqs.ev185' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrBufEqs.ev185
/-- info: 'KCore.LibEvStrBufEqs.ev195' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvStrBufEqs.ev195
#print axioms KCore.LibEvStrBufEqs.ev_Hsb
#print axioms KCore.LibEvStrBufEqs.unit_none
#print axioms KCore.LibEvStrBufEqs.toStr_none
