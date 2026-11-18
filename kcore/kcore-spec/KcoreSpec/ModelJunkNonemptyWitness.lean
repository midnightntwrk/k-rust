/-
  KCore. The junk witness (ModelJunkWitness.lean) with every sort said to be inhabited has no model:
  the negative half of that module's claim that `ΓSig` must not say every sort is inhabited.

  `ΓNonempty c` is G-nonempty, `⊤_s ≠ ⊥`, for every numbered sort `s` (`nonemptyItem`), the item
  `sigItems` leaves out. In a model of `Γ c ∪ ΓNonempty c`, IOError holds an element `j`; the
  injection builds from it one element `x₀` of KItem (Cons-Fun, `gen_fun`). Read at `x₀`, the
  equation `f(inj{IOError,KItem}(F)) = false requires f(inj{IOError,KItem}(F))` with `F := j` says
  `f(x₀) = true → f(x₀) = false`, and the catch-all `f(X) = true [owise]`, whose premise negates the
  first clause (`∃F. f(inj(F)) = true ∧ X ∈ inj(F)`, which at `x₀` is `f(x₀) = true`, since an `F`
  with `x₀ ∈ inj(F)` builds `x₀` and only it), says `f(x₀) ≠ true → f(x₀) = true`. Either way `true`
  and `false` are one element of Bool, which `Γ` refutes (`values_apart`). So `no_model`: the theory
  of a core that `HypModel` accepts (`JunkWitness.hypModel`, ModelHas.lean) becomes inconsistent
  once every sort is said to be inhabited.
-/
import KcoreSpec.ModelHas

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace Faithful

namespace JunkWitness

open ML
open KoreAML (Inh IsSort)

/-- **G-nonempty for every numbered sort**: `⊤_s ≠ ⊥`, the item `sigItems` leaves out. -/
def ΓNonempty (c : Semantics) : Premises KoreAML.Sym := fun φ =>
  ∃ s ∈ kernelSorts c, φ = (KoreAML.nonemptyItem (sortDeclOf c s)).pat

/-! ## The two equations of `f`, as KORE patterns -/

local notation "sB" => KoreAML.srt "Bool"
local notation "sK" => KoreAML.srt "KItem"
local notation "sE" => KoreAML.srt "IOError"
local notation "vE" => KoreAML.evar "VarV0" sE
local notation "vK" => KoreAML.evar "VarV0" sK
local notation "vX" => KoreAML.evar "X0" sK
def injV : Kore.Pattern := .app ⟨⟨"inj"⟩⟩ [sE, sK] [.var (.evar vE)]
def fX : Kore.Pattern := .app ⟨⟨"Lblf"⟩⟩ [] [.var (.evar vX)]
/-- `cl1`'s premise: `f(inj(F)) = true ∧ X0 ∈ inj(F)`. -/
def prem1 : Kore.Pattern :=
  .and KoreAML.R [.equals sB KoreAML.R (.app ⟨⟨"Lblf"⟩⟩ [] [injV]) (.dv sB "true"),
    .and KoreAML.R [.in sK KoreAML.R (.var (.evar vX)) injV, .top KoreAML.R]]
def concl (b : String) : Kore.Pattern := .equals sB KoreAML.R fX (.and sB [.dv sB b, .top sB])
/-- `cl1`'s equation. -/
def P1 : Kore.Pattern := .implies KoreAML.R prem1 (concl "false")
/-- The catch-all's premise: `cl1` does not apply, and `X0 ∈ X`. -/
def prem2 : Kore.Pattern :=
  .and KoreAML.R [.not KoreAML.R (.or KoreAML.R [.exist KoreAML.R vE prem1, .bottom KoreAML.R]),
    .and KoreAML.R [.top KoreAML.R, .and KoreAML.R [.in sK KoreAML.R (.var (.evar vX)) (.var (.evar vK)), .top KoreAML.R]]]
/-- The catch-all's equation. -/
def P2 : Kore.Pattern := .implies KoreAML.R prem2 (concl "true")

def ax1 : Kore.Axiom := { sortVars := [KoreAML.Rv], pattern := P1, attributes := [] }
def ax2 : Kore.Axiom := { sortVars := [KoreAML.Rv], pattern := P2, attributes := [] }

theorem ax1_eq : clauseAxiom c fn cl1 = ax1 := rfl
theorem ax2_eq : competingEquation c fn [cl1] cl2 = .axiom ax2 := rfl

theorem item1_mem : KoreAML.trAxiom [] [] ⟨0, "kernel", ax1⟩ ∈ fnItems c := by
  rw [← ax1_eq]
  exact clause_item_mem (List.mem_append_left _ (List.mem_singleton_self _)) (by simp [fn]) rfl rfl rfl

theorem item2_mem : KoreAML.trAxiom [] [] ⟨0, "kernel", ax2⟩ ∈ fnItems c := by
  unfold fnItems
  refine List.mem_flatMap.mpr ⟨fn, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
  unfold kernelItems
  refine List.mem_filterMap.mpr ⟨competingEquation c fn [cl1] cl2, ?_, by rw [ax2_eq]⟩
  show competingEquation c fn [cl1] cl2 ∈ [prioEquation c fn cl1, prioEquation c fn cl2]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

local notation "kR" => KoreAML.VarKey.sortVar "R"
local notation "kE" => KoreAML.VarKey.evar "VarV0" sE
local notation "kK" => KoreAML.VarKey.evar "VarV0" sK
local notation "kX" => KoreAML.VarKey.evar "X0" sK

def tbl1 : KoreAML.VarTable := KoreAML.tableOf [KoreAML.Rv] P1
def tbl2 : KoreAML.VarTable := KoreAML.tableOf [KoreAML.Rv] P2

theorem tbl1_eq : tbl1 = [kR, kE, kX] := by decide +kernel
theorem tbl2_eq : tbl2 = [kR, kE, kX, kK] := by decide +kernel
theorem kR_tbl1 : kR ∈ tbl1 := by decide +kernel
theorem kE_tbl1 : kE ∈ tbl1 := by decide +kernel
theorem kX_tbl1 : kX ∈ tbl1 := by decide +kernel
theorem kR_tbl2 : kR ∈ tbl2 := by decide +kernel
theorem kE_tbl2 : kE ∈ tbl2 := by decide +kernel
theorem kX_tbl2 : kX ∈ tbl2 := by decide +kernel
theorem kK_tbl2 : kK ∈ tbl2 := by decide +kernel
theorem kE_ne_kR : kE ≠ kR := by decide
theorem kX_ne_kR : kX ≠ kR := by decide
theorem kK_ne_kR : kK ≠ kR := by decide
theorem kX_ne_kE : kX ≠ kE := by decide
theorem kK_ne_kE : kK ≠ kE := by decide
theorem kR_ne_kE : kR ≠ kE := by decide

theorem guards1_eq : ([KoreAML.Rv].map KoreAML.sortVarKey ++ KoreAML.freeOf [] P1).eraseDups = [kR, kE, kX] := by
  decide +kernel
theorem guards2_eq : ([KoreAML.Rv].map KoreAML.sortVarKey ++ KoreAML.freeOf [] P2).eraseDups = [kR, kX, kK] := by
  decide +kernel


section
variable (ctx : KoreAML.Ctx)
theorem tr_equals (s s' : Kore.KSort) (p q : Kore.Pattern) : KoreAML.tr ctx (.equals s s' p q) =
    KoreAML.sEquals (KoreAML.trSort ctx.vars s) (KoreAML.trSort ctx.vars s') (KoreAML.tr ctx p) (KoreAML.tr ctx q) := by
  rw [KoreAML.tr]
theorem tr_in (s s' : Kore.KSort) (p q : Kore.Pattern) : KoreAML.tr ctx (.in s s' p q) =
    KoreAML.sIn (KoreAML.trSort ctx.vars s) (KoreAML.trSort ctx.vars s') (KoreAML.tr ctx p) (KoreAML.tr ctx q) := by
  rw [KoreAML.tr]
theorem tr_top (s : Kore.KSort) : KoreAML.tr ctx (.top s) = KoreAML.sTop (KoreAML.trSort ctx.vars s) := by
  rw [KoreAML.tr]
theorem tr_bottom (s : Kore.KSort) : KoreAML.tr ctx (.bottom s) = KoreAML.sBot (KoreAML.trSort ctx.vars s) := by
  rw [KoreAML.tr]
theorem tr_implies (s : Kore.KSort) (p q : Kore.Pattern) : KoreAML.tr ctx (.implies s p q) =
    KoreAML.sImp (KoreAML.trSort ctx.vars s) (KoreAML.tr ctx p) (KoreAML.tr ctx q) := by
  rw [KoreAML.tr]
theorem tr_not (s : Kore.KSort) (p : Kore.Pattern) : KoreAML.tr ctx (.not s p) =
    KoreAML.sNot (KoreAML.trSort ctx.vars s) (KoreAML.tr ctx p) := by
  rw [KoreAML.tr]
theorem tr_exist (s : Kore.KSort) (x : Kore.EVar) (p : Kore.Pattern) : KoreAML.tr ctx (.exist s x p) =
    KoreAML.sExists (ctx.vars.ev (KoreAML.evarKey x)) (KoreAML.trSort ctx.vars x.sort) (KoreAML.tr ctx p) := by
  rw [KoreAML.tr]
theorem tr_or2 (s : Kore.KSort) (p q : Kore.Pattern) : KoreAML.tr ctx (.or s [p, q]) =
    KoreAML.sOr (KoreAML.trSort ctx.vars s) (KoreAML.tr ctx p) (KoreAML.tr ctx q) := by
  rw [KoreAML.tr]; simp only [KoreAML.trOrList]
end

/-! ## The argument -/

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The valuation of an equation's table: `R` the sort `σ`, `F : IOError` the element `j`, every other
key the element `x`. -/
def val (σ j x : M) (k : KoreAML.VarKey) : M := if k = kR then σ else if k = kE then j else x

omit [Inhabited M] in
theorem val_R (σ j x : M) : val σ j x kR = σ := by simp [val]
omit [Inhabited M] in
theorem val_E (σ j x : M) : val σ j x kE = j := by
  unfold val; split
  · exact absurd ‹_› kE_ne_kR
  · split
    · rfl
    · exact absurd rfl ‹_›
omit [Inhabited M] in
theorem val_X (σ j x : M) : val σ j x kX = x := by
  unfold val; split
  · exact absurd ‹_› kX_ne_kR
  · split
    · exact absurd ‹_› kX_ne_kE
    · rfl
omit [Inhabited M] in
theorem val_K (σ j x : M) : val σ j x kK = x := by
  unfold val; split
  · exact absurd ‹_› kK_ne_kR
  · split
    · exact absurd ‹_› kK_ne_kE
    · rfl

omit [Inhabited M] in
theorem tr_sort {tbl : KoreAML.VarTable} {e : Valuation M} {n : String} {σ : M}
    (h : ∀ a, I.evalSymb (.sort ("Sort" ++ n)) a ↔ a = σ) (a : M) :
    (KoreAML.trSort tbl (KoreAML.srt n)).interpret I e a ↔ a = σ := by
  rw [trSort_srt]; exact h a

omit [Inhabited M] in
theorem tr_evar {tbl : KoreAML.VarTable} {e : Valuation M} {x : Kore.EVar} (a : M) :
    (KoreAML.tr ⟨tbl, []⟩ (.var (.evar x))).interpret I e a ↔ a = e.evalEvar (tbl.ev (KoreAML.evarKey x)) := by
  rw [KoreAML.tr, KoreAML.interp_evar]

set_option maxHeartbeats 1000000 in
/-- **`Γ c` with every sort said to be inhabited has no model**, though `c` meets `HypModel`
(`JunkWitness.hypModel`). -/
theorem no_model :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP (Γ c ∪ ΓNonempty c)) := by
  intro M _ I hI'
  have hI : I ⊧ᴵP Γ c := fun φ h => hI' φ (Or.inl h)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  have htr := (sortCtx_of_all (Semantics.sortedOK_of_okAll okAll (Semantics.ovlPatsOK_of_ovlCase (OvlOK.ovlCase inferInstance))) srReady (OvlOK.ovlCase inferInstance)).trans
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (s := Srt.bool) (by decide +kernel)
  obtain ⟨σK, hσK1, hσK2⟩ := sortSing hI (s := Srt.kitem) (by decide +kernel)
  obtain ⟨σE, hσE1, hσE2⟩ := sortSing hI (s := Srt.ioError) (by decide +kernel)
  have hnB : c.sortName Srt.bool = "Bool" := by decide +kernel
  have hnK : c.sortName Srt.kitem = "KItem" := by decide +kernel
  have hnE : c.sortName Srt.ioError = "IOError" := by decide +kernel
  rw [hnB] at hσB1; rw [hnK] at hσK1; rw [hnE] at hσE1
  have hInS : ∀ {n : String} {σ : M}, (∀ a, I.evalSymb (.sort ("Sort" ++ n)) a ↔ a = σ) →
      ∀ a, InS I n a ↔ Inh I σ a := fun h a => by
    unfold InS; exact KoreAML.interp_inhOf_of (fun b => h b)
  -- an element of IOError, from G-nonempty
  obtain ⟨j, hj⟩ : ∃ j, Inh I σE j := by
    have hne := hI' _ (Or.inr ⟨Srt.ioError, by decide +kernel, rfl⟩) KoreAML.val0 default
    simp only [KoreAML.nonemptyItem, sortDeclOf, KoreAML.guarded, List.map_nil, KoreAML.appList] at hne
    rw [KoreAML.interp_notEqual hD] at hne
    refine Classical.byContradiction fun hn => hne fun a => ?_
    rw [KoreAML.interp_inhOf_of (fun b => (show _ ↔ b = σE from hnE ▸ hσE1 b)), interpret_bottom]
    exact ⟨fun h => hn ⟨a, h⟩, False.elim⟩
  -- the element the injection builds from an element of IOError
  have hgm : Gen.inj Srt.ioError ∈ c.gens Srt.kitem := List.mem_of_getElem? (i := 1) (show (c.gens Srt.kitem)[1]? = some (Gen.inj Srt.ioError) from rfl)
  have hN : Srt.kitem ∈ consSorts c := by decide +kernel
  have hinj : ∀ j', Inh I σE j' → ∃ x, Inh I σK x ∧ ∀ m, GS I "KItem" (.inj "IOError") [j'] m ↔ m = x := by
    intro j' hj'
    obtain ⟨x, hx, hgs⟩ := gen_fun hI hN (List.mem_filter.mpr ⟨hgm, rfl⟩) rfl (xs := [j']) rfl (fun i x s h1 h2 => by
      cases i with
      | zero =>
        simp only [show (Gen.inj Srt.ioError).argSorts = [Srt.ioError] from rfl, List.map_cons, List.map_nil,
          List.getElem?_cons_zero, Option.some.injEq, hnE] at h1 h2
        subst h1; subst h2
        exact (hInS hσE1 _).mpr hj'
      | succ i => simp at h1)
    rw [hnK] at hx hgs
    exact ⟨x, (hInS hσK1 _).mp hx, fun m => by simpa [Gen.toK, hnE] using hgs m⟩
  obtain ⟨x0, hx0, hgs0⟩ := hinj j hj
  -- `true` and `false`
  have hsT : c.sortOf (bool true) = some Srt.bool := by decide +kernel
  have hsF : c.sortOf (bool false) = some Srt.bool := by decide +kernel
  let tT := elemOf c I (bool true)
  let tF := elemOf c I (bool false)
  have hdv : ∀ (b : Bool) (tbl : KoreAML.VarTable) (e : Valuation M) (a : M),
      (KoreAML.tr ⟨tbl, []⟩ (.dv sB (toString b))).interpret I e a ↔ a = elemOf c I (bool b) := by
    intro b tbl e a
    have := (elemOf_spec hI (show c.sortOf (bool b) = some Srt.bool by cases b <;> decide +kernel) e).1 a
    rw [← this]
    unfold den KoreAML.den bool
    rw [GroundTerm.kore, hnB, KoreAML.tr_dv, KoreAML.tr_dv]
    cases b <;> rfl
  have hTin : Inh I σB tT := by
    have := (elemOf_spec hI hsT KoreAML.val0).2
    rw [hnB] at this
    exact (hInS hσB1 _).mp this
  have hTF : tT ≠ tF := fun he => by
    have := values_apart hI (by decide +kernel) htr (by decide +kernel) hsT hsF he
    simp [bool] at this
  -- `f(x₀)`
  let F0 : M → Prop := fun a => ∃ h, I.evalSymb (.symbol "Lblf") h ∧ I.evalApp h x0 a
  have hfX : ∀ (tbl : KoreAML.VarTable) (e : Valuation M), e.evalEvar (tbl.ev kX) = x0 →
      ∀ a, (KoreAML.tr ⟨tbl, []⟩ fX).interpret I e a ↔ F0 a := fun tbl e he a => by
    unfold fX
    rw [KoreAML.tr_app0, trArgs_appList]
    simp only [List.map_cons, List.map_nil, KoreAML.appList]
    rw [KoreAML.interp_app]
    constructor
    · rintro ⟨h, b, hh, hb, hm⟩
      rw [tr_evar] at hb
      exact ⟨h, hh, by rw [hb] at hm; exact he ▸ hm⟩
    · rintro ⟨h, hh, hm⟩
      exact ⟨h, x0, hh, by rw [tr_evar]; exact he.symm, hm⟩
  -- `inj(F)` at an element of IOError, and `f(inj(F))`
  have hinjV : ∀ (tbl : KoreAML.VarTable) (e : Valuation M) (b : M),
      (KoreAML.tr ⟨tbl, []⟩ injV).interpret I e b ↔ GS I "KItem" (.inj "IOError") [e.evalEvar (tbl.ev kE)] b := by
    intro tbl e b
    unfold injV
    rw [show (Kore.Pattern.app ⟨⟨"inj"⟩⟩ [sE, sK] [.var (.evar vE)]) = KoreAML.injP "IOError" "KItem" (.var (.evar vE))
      from rfl, KoreAML.tr_injP, interp_injApp]
    constructor
    · rintro ⟨x, hx, hm⟩; rw [tr_evar] at hx; rw [hx] at hm; exact hm
    · intro hm; exact ⟨_, by rw [tr_evar]; rfl, hm⟩
  have hfinj : ∀ (tbl : KoreAML.VarTable) (e : Valuation M), Inh I σE (e.evalEvar (tbl.ev kE)) →
      (∀ b, GS I "KItem" (.inj "IOError") [e.evalEvar (tbl.ev kE)] b → b = x0) →
      GS I "KItem" (.inj "IOError") [e.evalEvar (tbl.ev kE)] x0 →
      ∀ a, (KoreAML.tr ⟨tbl, []⟩ (.app ⟨⟨"Lblf"⟩⟩ [] [injV])).interpret I e a ↔ F0 a := by
    intro tbl e _ hone hx a
    rw [KoreAML.tr_app0, trArgs_appList]
    simp only [List.map_cons, List.map_nil, KoreAML.appList]
    rw [KoreAML.interp_app]
    constructor
    · rintro ⟨h, b, hh, hb, hm⟩
      rw [hinjV] at hb
      exact ⟨h, hh, hone b hb ▸ hm⟩
    · rintro ⟨h, hh, hm⟩
      exact ⟨h, x0, hh, (hinjV _ _ _).mpr hx, hm⟩
  -- the statement both equations speak of: `f(x₀) = true` on Bool
  let P : Prop := ∀ a, Inh I σB a → (F0 a ↔ a = tT)
  have hconcl : ∀ (tbl : KoreAML.VarTable) (e : Valuation M) (b : Bool), e.evalEvar (tbl.ev kX) = x0 →
      e.evalEvar (tbl.ev kR) = σK → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (concl (toString b))).interpret I e m →
      ∀ a, Inh I σB a → (F0 a ↔ a = elemOf c I (bool b)) := by
    intro tbl e b hx hR m hm a ha
    have hRr : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σK := fun a => by
      rw [trSort_R, KoreAML.interp_evar]; exact Iff.of_eq (congrArg (a = ·) hR)
    unfold concl at hm
    rw [tr_equals, KoreAML.interp_sEquals hD hc (tr_sort hσB1) hRr hσB2 hσK2] at hm
    rw [← hfX tbl e hx a, hm.2 a ha, tr_and2, KoreAML.interp_sAnd,
      hdv b tbl e a, tr_top, KoreAML.interp_sTop hD (by rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of (tr_sort hσB1)]
    exact ⟨fun h => h.1, fun h => ⟨h, ha⟩⟩
  -- the premise of `cl1` at an element `j'` of IOError whose injection is `x₀`
  have hprem1 : ∀ (tbl : KoreAML.VarTable) (e : Valuation M), e.evalEvar (tbl.ev kX) = x0 →
      e.evalEvar (tbl.ev kR) = σK → Inh I σE (e.evalEvar (tbl.ev kE)) →
      ((KoreAML.tr ⟨tbl, []⟩ prem1).interpret I e x0 →
        GS I "KItem" (.inj "IOError") [e.evalEvar (tbl.ev kE)] x0 ∧ P) ∧
      (GS I "KItem" (.inj "IOError") [e.evalEvar (tbl.ev kE)] x0 → P → (KoreAML.tr ⟨tbl, []⟩ prem1).interpret I e x0) := by
    intro tbl e hx hR hE
    have hRr : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σK := fun a => by
      rw [trSort_R, KoreAML.interp_evar]; exact Iff.of_eq (congrArg (a = ·) hR)
    obtain ⟨y, -, hy⟩ := hinj _ hE
    have hone : GS I "KItem" (.inj "IOError") [e.evalEvar (tbl.ev kE)] x0 →
        ∀ b, GS I "KItem" (.inj "IOError") [e.evalEvar (tbl.ev kE)] b → b = x0 := fun h0 b hb => by
      rw [(hy b).mp hb, (hy x0).mp h0]
    have hXr : ∀ a, (KoreAML.tr ⟨tbl, []⟩ (.var (.evar vX))).interpret I e a ↔ a = x0 := fun a => by
      rw [tr_evar]; exact Iff.of_eq (congrArg (a = ·) hx)
    unfold prem1
    rw [tr_and2, KoreAML.interp_sAnd, tr_equals, KoreAML.interp_sEquals hD hc (tr_sort hσB1) hRr hσB2 hσK2,
      tr_and2, KoreAML.interp_sAnd, tr_in,
      KoreAML.interp_sIn hD hc (tr_sort hσK1) hRr hσK2 hσK2 (fun a ha => by rw [(hXr a).mp ha]; exact hx0),
      tr_top, KoreAML.interp_sTop hD isFree_R, KoreAML.interp_inhOf_of hRr]
    constructor
    · rintro ⟨⟨-, hreq⟩, ⟨⟨a, ha, hia⟩, -⟩, -⟩
      rw [(hXr a).mp ha, hinjV] at hia
      refine ⟨hia, fun a' ha' => ?_⟩
      rw [← hfinj tbl e hE (hone hia) hia a', hreq a' ha']
      exact hdv true tbl e a'
    · intro hia hP
      refine ⟨⟨hx0, fun a ha => ?_⟩, ⟨⟨x0, (hXr x0).mpr rfl, (hinjV _ _ _).mpr hia⟩, hx0⟩, hx0⟩
      rw [hfinj tbl e hE (hone hia) hia a, hP a ha]
      exact (hdv true tbl e a).symm
  -- `cl1`'s equation at `R := KItem`, `F := j`, `X0 := x0`
  have heq1 : P → ∀ a, Inh I σB a → (F0 a ↔ a = tF) := by
    intro hP
    let e : Valuation M := valOf tbl1 (val σK j x0)
    have heR : e.evalEvar (tbl1.ev kR) = σK := by rw [valOf_ev kR_tbl1, val_R]
    have heE : e.evalEvar (tbl1.ev kE) = j := by rw [valOf_ev kE_tbl1, val_E]
    have heX : e.evalEvar (tbl1.ev kX) = x0 := by rw [valOf_ev kX_tbl1, val_X]
    have hax := sat_fns hI (Or.inl ⟨_, item1_mem, rfl⟩)
    have hg : ∀ k ∈ ((ax1.sortVars.map KoreAML.sortVarKey) ++ KoreAML.freeOf [] ax1.pattern).eraseDups, ∀ m,
        (KoreAML.guardOf (KoreAML.tableOf ax1.sortVars ax1.pattern) k).interpret I e m := by
      intro k hk m
      change k ∈ ([KoreAML.Rv].map KoreAML.sortVarKey ++ KoreAML.freeOf [] P1).eraseDups at hk
      change (KoreAML.guardOf tbl1 k).interpret I e m
      rw [guards1_eq] at hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · rw [KoreAML.interp_guard_sortVar hD]
        exact heR ▸ hσK2
      · rw [KoreAML.interp_guard_evar hD,
          KoreAML.interp_inhOf_of (tr_sort hσE1)]
        exact heE ▸ hj
      · rw [KoreAML.interp_guard_evar hD,
          KoreAML.interp_inhOf_of (tr_sort hσK1)]
        exact heX ▸ hx0
    have hP1 := (KoreAML.trAxiom_at hD hax e hg x0).mpr (by
      show (KoreAML.inhOf (KoreAML.trSort tbl1 KoreAML.R)).interpret I e x0
      rw [KoreAML.interp_inhOf_of (fun a => by rw [trSort_R, KoreAML.interp_evar, heR])]
      exact hx0)
    change (KoreAML.tr ⟨tbl1, []⟩ P1).interpret I e x0 at hP1
    unfold P1 at hP1
    rw [tr_implies, KoreAML.interp_sImp] at hP1
    have hc1 := hP1.2 ((hprem1 tbl1 e heX heR (heE ▸ hj)).2 (by rw [heE]; exact (hgs0 x0).mpr rfl) hP)
    exact hconcl tbl1 e false heX heR x0 hc1
  -- the catch-all's equation at `R := KItem`, `X0 := X := x0`
  have heq2 : ¬ P → P := by
    intro hnP
    let e : Valuation M := valOf tbl2 (val σK j x0)
    have heR : e.evalEvar (tbl2.ev kR) = σK := by rw [valOf_ev kR_tbl2, val_R]
    have heX : e.evalEvar (tbl2.ev kX) = x0 := by rw [valOf_ev kX_tbl2, val_X]
    have heK : e.evalEvar (tbl2.ev kK) = x0 := by rw [valOf_ev kK_tbl2, val_K]
    have hax := sat_fns hI (Or.inl ⟨_, item2_mem, rfl⟩)
    have hg : ∀ k ∈ ((ax2.sortVars.map KoreAML.sortVarKey) ++ KoreAML.freeOf [] ax2.pattern).eraseDups, ∀ m,
        (KoreAML.guardOf (KoreAML.tableOf ax2.sortVars ax2.pattern) k).interpret I e m := by
      intro k hk m
      change k ∈ ([KoreAML.Rv].map KoreAML.sortVarKey ++ KoreAML.freeOf [] P2).eraseDups at hk
      change (KoreAML.guardOf tbl2 k).interpret I e m
      rw [guards2_eq] at hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · rw [KoreAML.interp_guard_sortVar hD]
        exact heR ▸ hσK2
      · rw [KoreAML.interp_guard_evar hD,
          KoreAML.interp_inhOf_of (tr_sort hσK1)]
        exact heX ▸ hx0
      · rw [KoreAML.interp_guard_evar hD,
          KoreAML.interp_inhOf_of (tr_sort hσK1)]
        exact heK ▸ hx0
    have hRr : ∀ (e' : Valuation M), e'.evalEvar (tbl2.ev kR) = σK →
        ∀ a, (KoreAML.trSort tbl2 KoreAML.R).interpret I e' a ↔ a = σK := fun e' h a => by
      rw [trSort_R, KoreAML.interp_evar]; exact Iff.of_eq (congrArg (a = ·) h)
    have hP2 := (KoreAML.trAxiom_at hD hax e hg x0).mpr (by
      show (KoreAML.inhOf (KoreAML.trSort tbl2 KoreAML.R)).interpret I e x0
      rw [KoreAML.interp_inhOf_of (hRr e heR)]
      exact hx0)
    change (KoreAML.tr ⟨tbl2, []⟩ P2).interpret I e x0 at hP2
    unfold P2 at hP2
    rw [tr_implies, KoreAML.interp_sImp] at hP2
    refine fun a ha => (hconcl tbl2 e true heX heR x0 (hP2.2 ?_) a ha)
    -- the premise: `cl1` does not apply at `x₀`
    have hXr : ∀ a, (KoreAML.tr ⟨tbl2, []⟩ (.var (.evar vX))).interpret I e a ↔ a = x0 := fun a => by
      rw [tr_evar]; exact Iff.of_eq (congrArg (a = ·) heX)
    unfold prem2
    rw [tr_and2, KoreAML.interp_sAnd, tr_not, KoreAML.interp_sNot, KoreAML.interp_inhOf_of (hRr e heR)]
    refine ⟨⟨fun hor => ?_, hx0⟩, ?_⟩
    · rw [tr_or2] at hor
      rw [KoreAML.interp_sOr] at hor
      rcases hor.2 with hex | hbot
      · rw [tr_exist, KoreAML.interp_sExists] at hex
        obtain ⟨j', hj'1, hj'2⟩ := hex
        let e' : Valuation M := ⟨Function.update e.evalEvar (tbl2.ev kE) j', e.evalSvar⟩
        have hoff : ∀ k, k ∈ tbl2 → k ≠ kE → e'.evalEvar (tbl2.ev k) = e.evalEvar (tbl2.ev k) :=
          fun k hk hne => Function.update_noteq (fun he => hne (ev_inj hk kE_tbl2 he)) _ _
        have he'E : e'.evalEvar (tbl2.ev kE) = j' := by
          show Function.update e.evalEvar (tbl2.ev kE) j' (tbl2.ev kE) = j'
          exact Function.update_same _ _ _
        have he'R : e'.evalEvar (tbl2.ev kR) = σK := by rw [hoff _ kR_tbl2 kR_ne_kE]; exact heR
        have he'X : e'.evalEvar (tbl2.ev kX) = x0 := by rw [hoff _ kX_tbl2 kX_ne_kE]; exact heX
        have hj'E : Inh I σE j' := by
          rw [KoreAML.interp_member hD] at hj'1
          change (KoreAML.inhOf (KoreAML.trSort tbl2 sE)).interpret I e' (e'.evalEvar (tbl2.ev kE)) at hj'1
          rw [he'E, KoreAML.interp_inhOf_of (tr_sort hσE1)] at hj'1
          exact hj'1
        obtain ⟨-, hP⟩ := (hprem1 tbl2 e' he'X he'R (he'E ▸ hj'E)).1 hj'2
        exact hnP hP
      · rw [tr_bottom] at hbot
        unfold KoreAML.sBot at hbot
        rw [KoreAML.interp_sNot, KoreAML.interp_sTop hD isFree_R] at hbot
        exact hbot.1 hbot.2
    · rw [tr_and2, KoreAML.interp_sAnd, tr_top, KoreAML.interp_sTop hD isFree_R, KoreAML.interp_inhOf_of (hRr e heR),
        tr_and2, KoreAML.interp_sAnd, tr_in,
        KoreAML.interp_sIn hD hc (tr_sort hσK1) (hRr e heR) hσK2 hσK2 (fun a ha => by rw [(hXr a).mp ha]; exact hx0),
        tr_top, KoreAML.interp_sTop hD isFree_R, KoreAML.interp_inhOf_of (hRr e heR)]
      refine ⟨hx0, ⟨⟨x0, (hXr x0).mpr rfl, ?_⟩, hx0⟩, hx0⟩
      rw [tr_evar]
      exact heK.symm
  -- either way `true` and `false` are one element
  by_cases hP : P
  · exact hTF (((heq1 hP tT hTin).mp ((hP tT hTin).mpr rfl)))
  · exact hP (heq2 hP)

end

end JunkWitness

end Faithful

end KCore
