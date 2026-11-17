/-
  The hoisting laws of KcoreSpec/ExistsHoist.lean, each at one interpretation: the value model
  `stdI c` of the reader's semantics for `f2-examples/ovlsub.kompile.kore`. Run from the package
  root: `lake env lean -j1 test/ExistsHoist.lean`.

  On patterns: the valuation `e0` gives y the sort element of Bool and every other element
  variable the value `true`; S is y, φ is `⊤_S`, the contexts put the hole under an application
  beside S. `app_exists`, `and_exists`, `or_exists` (Bool has the element `true`) and
  `var_and_mem` have every hypothesis discharged; `or_exists_only_if` is at the sort `⊥`, which
  has no element.

  On KORE patterns, each translated in one context:
  - `tr_app_exists` at `inj{Bool,KItem}(\exists{Bool}(B:Bool, B))` and
    `\exists{KItem}(B:Bool, inj{Bool,KItem}(B))`; `tr_and_exists` at
    `\and{Bool}(\exists{Bool}(B:Bool, B), \dv{Bool}("true"))`;
  - `tr_or_exists`, `tr_var_and_mem` and `tr_mem_and` at variables `V:R` and `W:R` of a sort
    variable R that the valuation `eR` reads as Bool, with `eR V = eR W = true`.
-/
import KcoreSpec

set_option autoImplicit false

open KCore Faithful Model KoreAML ML

namespace ExistsHoistTest

definition_of defn from "f2-examples/ovlsub.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def x : EVar := ⟨100⟩
def y : EVar := ⟨101⟩
def bTrue : Elem := .val (.dv Srt.bool (.bool true))
def σB : Elem := .srt Srt.bool
noncomputable def e0 : Valuation Elem := ⟨fun v => if v = y then σB else bTrue, fun _ _ => False⟩
def S : KoreAML.P := .evar y
def φ : KoreAML.P := inhOf S

theorem bool_facts : Srt.bool < nRegSorts + c.sortNames.length ∧
    c.sortOf (.dv Srt.bool (.bool true)) = some Srt.bool := by
  decide +kernel

theorem hS : ∀ a, S.interpret (stdI c) e0 a ↔ a = σB := fun a => by
  show a = e0.evalEvar y ↔ _
  simp [e0]

theorem hσ : IsSort (stdI c) σB := (isSort_iff _).mpr ⟨Srt.bool, List.mem_range.mpr bool_facts.1, rfl⟩

theorem hbT : Inh (stdI c) σB bTrue := (inh_srt Srt.bool bTrue).mpr bool_facts.2

theorem hx : Inh (stdI c) σB (e0.evalEvar x) := by
  have : e0.evalEvar x = bTrue := by simp [e0, x, y]
  rw [this]
  exact hbT

theorem noRead_S : NoReadCut (stdI c) x S := fun e a m => by
  show m = Function.update e.evalEvar x a y ↔ m = e.evalEvar y
  rw [Function.update_noteq (by simp [x, y])]

theorem noRead_φ : NoReadCut (stdI c) x φ := fun e a m => by
  unfold φ
  rw [interp_inhOf, interp_inhOf]
  exact exists_congr fun σ => and_congr_left' (noRead_S e a σ)

/-- Bool has an element, read with x at it. -/
theorem hs : ∃ a, (inhOf S).interpret (stdI c) (updE e0 x a) a :=
  ⟨bTrue, (noRead_φ e0 bTrue bTrue).mpr ((interp_inhOf_of hS).mpr hbT)⟩

/-- The sort `⊥` has no element. -/
theorem hs_bot : ¬ ∃ a, (inhOf (⊥ : KoreAML.P)).interpret (stdI c) (updE e0 x a) a := by
  rintro ⟨a, h⟩
  obtain ⟨σ, hσ', -⟩ := interp_inhOf.mp h
  exact interpret_bottom.mp hσ'

def C₁ : CutCtx := .fn .hole S
def C₂ : CutCtx := .arg S .hole
theorem fresh₁ : C₁.Fresh (stdI c) x := ⟨trivial, noRead_S⟩
theorem fresh₂ : C₂.Fresh (stdI c) x := ⟨noRead_S, trivial⟩

example (m : Elem) := app_exists defOK_std x S φ C₁ fresh₁ e0 m
example (m : Elem) := app_exists defOK_std x S φ C₂ fresh₂ e0 m
example (m : Elem) := and_exists defOK_std x S φ S noRead_S e0 m
example (m : Elem) := or_exists defOK_std x S S φ S noRead_S noRead_S e0 hs m
example (m : Elem) := or_exists_only_if defOK_std x S ⊥ φ S e0 hs_bot m
example (m : Elem) := var_and_mem defOK_std sat_ceilDef hS hS hσ hσ x hx hx φ m

/-- Where the bound sort is empty the two sides of `or_exists` differ at `true`, with the
alternative φ (the elements of Bool): the left side holds it and the right side is empty. -/
example : (sOr S (sExists x ⊥ φ) φ).interpret (stdI c) e0 bTrue ∧
    ¬ (sExists x ⊥ (sOr S φ φ)).interpret (stdI c) e0 bTrue := by
  obtain ⟨h1, h2⟩ := or_exists_only_if defOK_std x S ⊥ φ φ e0 hs_bot bTrue
  have hb : (inhOf S).interpret (stdI c) e0 bTrue := (interp_inhOf_of hS).mpr hbT
  exact ⟨h2.mpr ⟨hb, hb⟩, h1⟩

/-! ### At the translation of KORE patterns -/

abbrev sB : Kore.KSort := .ctor ⟨⟨"SortBool"⟩⟩ []
abbrev sKI : Kore.KSort := .ctor ⟨⟨"SortKItem"⟩⟩ []
def vB : Kore.EVar := ⟨⟨⟨"VarB"⟩⟩, sB⟩
def injK : KoreCutCtx := .app ⟨⟨"inj"⟩⟩ [sB, sKI] [] .hole []
def tt : Kore.Pattern := .dv sB "true"
def kctx : Ctx :=
  { vars := tableOf [] (injK.fill (.exist sB vB (.var (.evar vB)))),
    aliases := ["weakExistsFinally", "weakAlwaysFinally", "allPathGlobally"] }

theorem injK_noAlias : injK.noAlias kctx = true := by decide +kernel

theorem injK_sides : injK.SidesNoRead (stdI c) kctx (kctx.vars.ev (evarKey vB)) :=
  ⟨NoReadCut.of_closed (trArgs_closed (trSortApp_closed (Closed.sym _) (by simp))
      (fun p hp' => by simp at hp')) _,
   by simp, trivial⟩

/-- `inj{Bool,KItem}(\exists{Bool}(B:Bool, B))` is `\exists{KItem}(B:Bool, inj{Bool,KItem}(B))`. -/
example (m : Elem) :
    (tr kctx (.app ⟨⟨"inj"⟩⟩ [sB, sKI] [.exist sB vB (.var (.evar vB))])).interpret (stdI c) e0 m ↔
      (tr kctx (.exist sKI vB (.app ⟨⟨"inj"⟩⟩ [sB, sKI] [.var (.evar vB)]))).interpret (stdI c) e0 m :=
  tr_app_exists defOK_std kctx sB sKI vB (.var (.evar vB)) injK injK_noAlias injK_sides e0 m

/-- `\and{Bool}(\exists{Bool}(B:Bool, B), true)` is `\exists{Bool}(B:Bool, \and{Bool}(B, true))`. -/
example (m : Elem) :
    (tr kctx (.and sB [.exist sB vB (.var (.evar vB)), tt])).interpret (stdI c) e0 m ↔
      (tr kctx (.exist sB vB (.and sB [.var (.evar vB), tt]))).interpret (stdI c) e0 m :=
  tr_and_exists defOK_std kctx sB vB (.var (.evar vB)) tt
    (NoReadCut.of_closed (KGround.dv.closed kctx) _) e0 m

/-! Variables `V:R` and `W:R` of a sort variable R: `eR` reads R as Bool's sort element and every
other variable as `true`. -/

def sR : Kore.KSort := .var ⟨⟨⟨"R"⟩⟩⟩
def vV : Kore.EVar := ⟨⟨⟨"VarV"⟩⟩, sR⟩
def vW : Kore.EVar := ⟨⟨⟨"VarW"⟩⟩, sR⟩
def ttR : Kore.Pattern := .var (.evar vW)
def rctx : Ctx := { vars := tableOf [⟨⟨⟨"R"⟩⟩⟩] (.and sR [.var (.evar vV), ttR]), aliases := [] }

abbrev xR : EVar := rctx.vars.ev (sortVarKey ⟨⟨⟨"R"⟩⟩⟩)
abbrev xV : EVar := rctx.vars.ev (evarKey vV)
abbrev xW : EVar := rctx.vars.ev (evarKey vW)

theorem rctx_ne : xV ≠ xR ∧ xW ≠ xR ∧ xV ≠ xW := by decide +kernel

noncomputable def eR : Valuation Elem := ⟨fun v => if v = xR then σB else bTrue, fun _ _ => False⟩

theorem hR : ∀ a, (trSort rctx.vars sR).interpret (stdI c) eR a ↔ a = σB := fun a => by
  show a = eR.evalEvar xR ↔ _
  simp [eR]

theorem hV : Inh (stdI c) σB (eR.evalEvar xV) := by
  have : eR.evalEvar xV = bTrue := by simp [eR, rctx_ne.1]
  rw [this]
  exact hbT

theorem noRead_R : NoReadCut (stdI c) xV (trSort rctx.vars sR) := fun e a m => by
  show m = Function.update e.evalEvar xV a xR ↔ m = e.evalEvar xR
  rw [Function.update_noteq (Ne.symm rctx_ne.1)]

theorem hsR : ∃ a, (inhOf (trSort rctx.vars vV.sort)).interpret (stdI c) (updE eR xV a) a := by
  refine ⟨bTrue, ?_⟩
  have h : (inhOf (trSort rctx.vars sR)).interpret (stdI c) eR bTrue := (interp_inhOf_of hR).mpr hbT
  rw [interp_inhOf] at h
  obtain ⟨σ, h1, h2⟩ := h
  exact interp_inhOf.mpr ⟨σ, (noRead_R eR bTrue σ).mpr h1, h2⟩

theorem noRead_ttR : NoReadCut (stdI c) xV (tr rctx ttR) := fun e a m => by
  show m = Function.update e.evalEvar xV a xW ↔ m = e.evalEvar xW
  rw [Function.update_noteq (Ne.symm rctx_ne.2.2)]

/-- `\or{R}(\exists{R}(V:R, V), W)` is `\exists{R}(V:R, \or{R}(V, W))`, R read as
Bool, which has the element `true`. -/
example (m : Elem) :
    (tr rctx (.or sR [.exist sR vV (.var (.evar vV)), ttR])).interpret (stdI c) eR m ↔
      (tr rctx (.exist sR vV (.or sR [.var (.evar vV), ttR]))).interpret (stdI c) eR m :=
  tr_or_exists defOK_std rctx sR vV (.var (.evar vV)) ttR noRead_ttR noRead_R eR hsR m

/-- `\and{R}(V, W)` is `\and{R}(V, \in{R,R}(V, W))`. -/
example (m : Elem) :
    (tr rctx (.and sR [.var (.evar vV), ttR])).interpret (stdI c) eR m ↔
      (tr rctx (.and sR [.var (.evar vV), .in sR sR (.var (.evar vV)) ttR])).interpret (stdI c) eR m :=
  tr_var_and_mem defOK_std sat_ceilDef rctx sR sR vV ttR hR hR hσ hσ hV hV m

/-- `\in{R,R}(V, \and{R}(W, V))` is `\and{R}(\in{R,R}(V, W), \in{R,R}(V, V))`. -/
example (m : Elem) :
    (tr rctx (.in sR sR (.var (.evar vV)) (.and sR [ttR, .var (.evar vV)]))).interpret (stdI c) eR m ↔
      (tr rctx (.and sR [.in sR sR (.var (.evar vV)) ttR,
        .in sR sR (.var (.evar vV)) (.var (.evar vV))])).interpret (stdI c) eR m :=
  tr_mem_and defOK_std sat_ceilDef rctx sR sR vV ttR (.var (.evar vV)) hR hR hσ hσ hV m

/-- info: 'KoreAML.app_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms app_exists
#print axioms and_exists
#print axioms or_exists
#print axioms or_exists_only_if
#print axioms var_and_mem
#print axioms tr_app_exists
#print axioms tr_and_exists
#print axioms tr_or_exists
#print axioms tr_var_and_mem
#print axioms tr_mem_and

end ExistsHoistTest
