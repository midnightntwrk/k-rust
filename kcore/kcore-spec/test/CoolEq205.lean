/-
  Sentence 205 of `f2-examples/e2-cool-eq.kompile.kore` (fixture e2-cool-eq), the user lemma
  `rule f(f(X)) => f(X) [simplification, cool]`, which kompile writes
  `f(f(X)) = f(X) requires true andBool isKResult(HOLE:K)`: entailed by Γ for every interpretation H,
  at every valuation (`TieE2CoolEq.UserLemmaEntailed`, here `userlemma_entailed`). Run from the
  package root: `lake env lean -j1 test/CoolEq205.lean`.

  HOLE occurs in the requires only, so the sentence is about every element of K at once; it holds
  because its conclusion holds at every valuation, whatever HOLE is.
  - `kr_hG`: in every model of Γ, `isKResult` of the element of `hG = kseq(inj{Int,KItem}(0), dotk)`
    is the element of `true`, from the equation 233
    (`isKResult(kseq(inj{KResult,KItem}(V), dotk)) = true`) at `V :=` the element of
    `inj{Int,KResult}(0)`: the injections compose along `Int < KResult < KItem` (`coh_at`), so the
    element of `hG` is of that pattern; `isKResult` gives elements of Bool only (its arity).
  - `f_id`: in every model of Γ, `f(x) = x` at every element `x` of Int, value or not: the equation
    204 of `f` (`f(X) => X requires true andBool isKResult(HOLE)`) holds at every valuation, so at
    `HOLE :=` the element of `hG`, where its requires is `true andBool true`, which the graph of
    `andBool` (`ΓDomains`) makes `true`.
  - `s205_entailed`: both sides of 205 then denote the element of X.
  204 and 233 are Γ's items (each of Γ's equations is the translation of its sentence, `shape`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.CoolEq205

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e2-cool-eq.kompile.kore"
definition_of defn from "f2-examples/e2-cool-eq.kompile.kore"
user_axioms U from "f2-examples/e2-cool-eq.kompile.kore" module "E2-COOL-EQ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-! ## The patterns -/

def vInt (n : String) : Kore.Pattern := KoreAML.ev n (KoreAML.srt "Int")
def vHole : Kore.Pattern := KoreAML.ev "VarHOLE" (KoreAML.srt "K")
def dvB : Kore.Pattern := .dv (KoreAML.srt "Bool") "true"
def andP : Kore.Pattern :=
  .app ⟨⟨"Lbl'Unds'andBool'Unds'"⟩⟩ [] [dvB, .app ⟨⟨"LblisKResult"⟩⟩ [] [vHole]]
def fP (p : Kore.Pattern) : Kore.Pattern := .app ⟨⟨"Lblf"⟩⟩ [] [p]
/-- `kseq(q, dotk)`. -/
def kseqOf (q : Kore.Pattern) : Kore.Pattern := .app ⟨⟨"kseq"⟩⟩ [] [q, .app ⟨⟨"dotk"⟩⟩ [] []]
/-- `kseq(inj{KResult,KItem}(p), dotk)`. -/
def kpatOf (p : Kore.Pattern) : Kore.Pattern := kseqOf (KoreAML.injP "KResult" "KItem" p)
/-- `0`, of Int. -/
def dv0 : Kore.Pattern := .dv (KoreAML.srt "Int") "0"

theorem trS_text : ∀ ad ∈ [U.ax204, U.ax205, U.ax233], (trS ad).pat = (trAxiom [] [] ad).pat := by decide +kernel

/-- 204: `f(X) => X requires true andBool isKResult(HOLE)`. -/
theorem s204_pattern : U.ax204.ax.pattern = .implies KoreAML.R
    (.and KoreAML.R [.equals (KoreAML.srt "Bool") KoreAML.R andP dvB,
      .and KoreAML.R [Kore.Pattern.in (KoreAML.srt "Int") KoreAML.R (vInt "X0") (vInt "VarX"), .top KoreAML.R]])
    (.equals (KoreAML.srt "Int") KoreAML.R (fP (vInt "X0")) (.and (KoreAML.srt "Int") [vInt "VarX", .top (KoreAML.srt "Int")])) := by
  decide +kernel
/-- 205: `f(f(X)) => f(X) requires true andBool isKResult(HOLE)`. -/
theorem s205_pattern : U.ax205.ax.pattern = .implies KoreAML.R
    (.equals (KoreAML.srt "Bool") KoreAML.R andP dvB)
    (.equals (KoreAML.srt "Int") KoreAML.R (fP (fP (vInt "VarX"))) (.and (KoreAML.srt "Int") [fP (vInt "VarX"), .top (KoreAML.srt "Int")])) := by
  decide +kernel
/-- 233: `isKResult(kseq(inj{KResult,KItem}(V), dotk)) => true`. -/
theorem s233_pattern : U.ax233.ax.pattern = .implies KoreAML.R
    (.and KoreAML.R [.top KoreAML.R, .and KoreAML.R [Kore.Pattern.in (KoreAML.srt "K") KoreAML.R
      (KoreAML.ev "X0" (KoreAML.srt "K")) (kpatOf (KoreAML.ev "VarKResult" (KoreAML.srt "KResult"))), .top KoreAML.R]])
    (.equals (KoreAML.srt "Bool") KoreAML.R (.app ⟨⟨"LblisKResult"⟩⟩ [] [KoreAML.ev "X0" (KoreAML.srt "K")])
      (.and (KoreAML.srt "Bool") [dvB, .top (KoreAML.srt "Bool")])) := by
  decide +kernel

def k204 : VarTable := [.sortVar "R", .evar "VarHOLE" (KoreAML.srt "K"), .evar "X0" (KoreAML.srt "Int"),
  .evar "VarX" (KoreAML.srt "Int")]
def k205 : VarTable := [.sortVar "R", .evar "VarHOLE" (KoreAML.srt "K"), .evar "VarX" (KoreAML.srt "Int")]
def k233 : VarTable := [.sortVar "R", .evar "X0" (KoreAML.srt "K"), .evar "VarKResult" (KoreAML.srt "KResult")]

theorem s204_keys : (U.ax204.ax.sortVars.map sortVarKey ++ freeOf [] U.ax204.ax.pattern).eraseDups = k204 ∧
    tableOf U.ax204.ax.sortVars U.ax204.ax.pattern = k204 := by decide +kernel
theorem s205_keys : (U.ax205.ax.sortVars.map sortVarKey ++ freeOf [] U.ax205.ax.pattern).eraseDups =
      [.sortVar "R", .evar "VarHOLE" (KoreAML.srt "K"), .evar "VarX" (KoreAML.srt "Int")] ∧
    tableOf U.ax205.ax.sortVars U.ax205.ax.pattern = k205 := by decide +kernel
theorem s233_keys : (U.ax233.ax.sortVars.map sortVarKey ++ freeOf [] U.ax233.ax.pattern).eraseDups = k233 ∧
    tableOf U.ax233.ax.sortVars U.ax233.ax.pattern = k233 := by decide +kernel

/-! ## The symbols, sorts and values -/

def fS : Sym := 385
def krS : Sym := 382
def andS : Sym := 4
def krSort : Srt := 32

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem names (H : HookParams) : (cH H).symName fS = "Lblf" ∧ (cH H).symName krS = "LblisKResult" ∧
    (cH H).symName andS = "Lbl'Unds'andBool'Unds'" ∧ (cH H).sortName Srt.int = "Int" ∧ (cH H).sortName Srt.k = "K" ∧
    (cH H).sortName krSort = "KResult" ∧ (cH H).sortName Srt.bool = "Bool" ∧
    instDecode? "Lbl'Unds'andBool'Unds'" = none ∧ instDecode? "Lblf" = none ∧ instDecode? "LblisKResult" = none :=
  (by decide +kernel : c.symName fS = "Lblf" ∧ c.symName krS = "LblisKResult" ∧
    c.symName andS = "Lbl'Unds'andBool'Unds'" ∧ c.sortName Srt.int = "Int" ∧ c.sortName Srt.k = "K" ∧
    c.sortName krSort = "KResult" ∧ c.sortName Srt.bool = "Bool" ∧
    instDecode? "Lbl'Unds'andBool'Unds'" = none ∧ instDecode? "Lblf" = none ∧ instDecode? "LblisKResult" = none)

theorem numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length ∧
    Srt.k < nRegSorts + (cH H).sortNames.length ∧ Srt.bool < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length ∧
    Srt.k < nRegSorts + c.sortNames.length ∧ Srt.bool < nRegSorts + c.sortNames.length)

theorem kernels (H : HookParams) : (⟨fS, [Srt.int], Srt.int⟩ : CtorSig) ∈ kernelSyms (cH H) ∧
    (⟨krS, [Srt.k], Srt.bool⟩ : CtorSig) ∈ kernelSyms (cH H) := by
  show _ ∈ kernelSyms c ∧ _ ∈ kernelSyms c; decide +kernel

theorem heads (H : HookParams) : symHead (cH H) fS = KoreAML.sym (.symbol "Lblf") ∧
    symHead (cH H) krS = KoreAML.sym (.symbol "LblisKResult") := by
  unfold symHead
  rw [(names H).1, (names H).2.1, (names H).2.2.2.2.2.2.2.2.1, (names H).2.2.2.2.2.2.2.2.2]
  exact ⟨rfl, rfl⟩

theorem kitem_name (H : HookParams) : (cH H).sortName Srt.kitem = "KItem" :=
  (by decide +kernel : c.sortName Srt.kitem = "KItem")

/-- `Int < KResult < KItem`. -/
theorem subs (H : HookParams) : (Srt.int, krSort) ∈ (cH H).subsorts ∧ (krSort, Srt.kitem) ∈ (cH H).subsorts := by
  show _ ∈ c.subsorts ∧ _ ∈ c.subsorts; decide +kernel

/-- `true`. -/
def tG : GroundTerm := .dv Srt.bool (.bool true)
/-- `0`. -/
def zG : GroundTerm := .dv Srt.int (.int 0)
/-- `inj{Int,KResult}(0)`. -/
def vG : GroundTerm := .inj Srt.int krSort zG
/-- `kseq(inj{Int,KItem}(0), dotk)`: a K whose one item is an Int, so a KResult. -/
def hG : GroundTerm := .ctor kseq [.inj Srt.int Srt.kitem zG, .ctor dotk []]

theorem sorts (H : HookParams) : (cH H).sortOf tG = some Srt.bool ∧ (cH H).sortOf vG = some krSort ∧
    (cH H).sortOf hG = some Srt.k ∧ (cH H).sortOf zG = some Srt.int := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]
  decide +kernel

theorem den_tG (H : HookParams) : den (cH H) tG = KoreAML.sym (.dv "true") ⬝ KoreAML.sym (.sort "SortBool") := by
  show den c tG = _; decide +kernel

theorem kores (H : HookParams) : hG.kore (cH H) = kseqOf (KoreAML.injP "Int" "KItem" dv0) ∧
    vG.kore (cH H) = KoreAML.injP "Int" "KResult" dv0 ∧ zG.kore (cH H) = dv0 := by
  show hG.kore c = _ ∧ vG.kore c = _ ∧ zG.kore c = _; decide +kernel

theorem andBool_dom (H : HookParams) : ΓDomains (cH H)
    (KoreAML.den (symApp (cH H) andS (GroundTerm.koreList (cH H) [tG, tG])) ≡ den (cH H) tG) :=
  Or.inl ⟨⟨andS, [Srt.bool, Srt.bool], Srt.bool⟩, [tG, tG], some tG, by decide +kernel,
    sortsOf_cons.mpr ⟨_, _, (sorts H).1, sortsOf_cons.mpr ⟨_, _, (sorts H).1, sortsOf_nil, rfl⟩, rfl⟩, by decide +kernel, fun h => absurd h (by simp), rfl⟩

/-! ## Translation facts -/

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- What the symbol named `n` applied to the element `x` denotes. -/
def appE (I : Interpretation KoreAML.Sym M) (n : String) (x m : M) : Prop :=
  ∃ a, I.evalSymb (.symbol n) a ∧ I.evalApp a x m

theorem tr_app1 {e : Valuation M} (t : VarTable) (n : String) (x : Kore.EVar) (m : M) :
    (KoreAML.tr ⟨t, []⟩ (.app ⟨⟨n⟩⟩ [] [.var (.evar x)])).interpret I e m ↔
      appE I n (e.evalEvar (t.ev (KoreAML.evarKey x))) m := by
  rw [KoreAML.tr_app0, KoreAML.trArgs_cons, KoreAML.trArgs_nil, KoreAML.interp_app, KoreAML.tr]
  simp only [KoreAML.interp_sym, KoreAML.interp_evar, appE]
  constructor
  · rintro ⟨a, b, ha, rfl, h⟩; exact ⟨a, ha, h⟩
  · rintro ⟨a, ha, h⟩; exact ⟨a, _, ha, rfl, h⟩

theorem tr_var {e : Valuation M} (t : VarTable) (n : String) (s : Kore.KSort) (m : M) :
    (KoreAML.tr ⟨t, []⟩ (KoreAML.ev n s)).interpret I e m ↔ m = e.evalEvar (t.ev (.evar n s)) := by
  unfold KoreAML.ev; rw [KoreAML.tr, KoreAML.interp_evar]; rfl

theorem tr_dvB {e e' : Valuation M} (t : VarTable) (H : HookParams) (m : M) :
    (KoreAML.tr ⟨t, []⟩ dvB).interpret I e m ↔ (den (cH H) tG).interpret I e' m := by
  unfold dvB; rw [KoreAML.tr_dv, den_tG]; exact Iff.rfl

/-- `kseq(q, dotk)` depends only on the set `q` denotes. -/
theorem kseq_congr {e e' : Valuation M} {t t' : VarTable} {q q' : Kore.Pattern}
    (h : ∀ m, (KoreAML.tr ⟨t, []⟩ q).interpret I e m ↔ (KoreAML.tr ⟨t', []⟩ q').interpret I e' m) (m : M) :
    (KoreAML.tr ⟨t, []⟩ (kseqOf q)).interpret I e m ↔ (KoreAML.tr ⟨t', []⟩ (kseqOf q')).interpret I e' m := by
  unfold kseqOf
  simp only [KoreAML.tr_app0, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
  exact KoreAML.interp_app_congr (e := e) (e' := e') (KoreAML.interp_app_congr (e := e) (e' := e')
    (fun _ => Iff.rfl) h) (fun _ => Iff.rfl) m

/-- `inj{A,B}(p)` depends only on the set `p` denotes. -/
theorem inj_congr {e e' : Valuation M} {t t' : VarTable} {A B : String} {p p' : Kore.Pattern}
    (h : ∀ m, (KoreAML.tr ⟨t, []⟩ p).interpret I e m ↔ (KoreAML.tr ⟨t', []⟩ p').interpret I e' m) (m : M) :
    (KoreAML.tr ⟨t, []⟩ (KoreAML.injP A B p)).interpret I e m ↔
      (KoreAML.tr ⟨t', []⟩ (KoreAML.injP A B p')).interpret I e' m := by
  rw [KoreAML.tr_injP, KoreAML.tr_injP]
  simp only [KoreAML.appList]
  exact KoreAML.interp_app_congr (e := e) (e' := e') (fun _ => Iff.rfl) h m

end

/-! ## In a model of Γ -/

section
variable (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **Arity**: a symbol of `[sa] → sr` applied to an element of `sa` gives elements of `sr` only. -/
theorem arity (hI : I ⊧ᴵP Γ (cH H)) {f : Sym} {sa sr : Srt} {n na nr : String}
    (hk : (⟨f, [sa], sr⟩ : CtorSig) ∈ kernelSyms (cH H)) (hhead : symHead (cH H) f = KoreAML.sym (.symbol n))
    (hna : (cH H).sortName sa = na) (hnr : (cH H).sortName sr = nr)
    {σa σr : M} (hσa : ∀ a, I.evalSymb (.sort ("Sort" ++ na)) a ↔ a = σa)
    (hσr : ∀ a, I.evalSymb (.sort ("Sort" ++ nr)) a ↔ a = σr)
    {x a : M} (hx : Inh I σa x) (h : appE I n x a) : Inh I σr a := by
  have hSa : ∀ b, (KoreAML.sym (.sort ("Sort" ++ na)) : KoreAML.P).interpret I KoreAML.val0 b ↔ b = σa := hσa
  have hSr : ∀ b, (KoreAML.sym (.sort ("Sort" ++ nr)) : KoreAML.P).interpret I KoreAML.val0 b ↔ b = σr := hσr
  have := symArity_at hI hk KoreAML.val0 a (by
    simp only [List.map, hna, hhead, KoreAML.appList, trSort_srt]
    obtain ⟨fa, hfa, happ⟩ := h
    exact KoreAML.interp_app.mpr ⟨fa, x, hfa, (KoreAML.interp_inhOf_of hSa).mpr hx, happ⟩)
  simp only [hnr] at this
  exact (KoreAML.interp_inhOf_of hSr).mp this

/-- The sorts Int, K, KResult and Bool of a model. -/
structure Frame (I : Interpretation KoreAML.Sym M) where
  σI : M
  σK : M
  σR : M
  σB : M
  hI1 : ∀ a, I.evalSymb (.sort ("Sort" ++ "Int")) a ↔ a = σI
  hI2 : IsSort I σI
  hK1 : ∀ a, I.evalSymb (.sort ("Sort" ++ "K")) a ↔ a = σK
  hK2 : IsSort I σK
  hR1 : ∀ a, I.evalSymb (.sort ("Sort" ++ "KResult")) a ↔ a = σR
  hR2 : IsSort I σR
  hB1 : ∀ a, I.evalSymb (.sort ("Sort" ++ "Bool")) a ↔ a = σB
  hB2 : IsSort I σB

theorem frame (hI : I ⊧ᴵP Γ (cH H)) : Nonempty (Frame I) := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σI, h1, h2⟩ := sortSing hI (numbered H).1
  obtain ⟨σK, k1, k2⟩ := sortSing hI (numbered H).2.1
  obtain ⟨σB, b1, b2⟩ := sortSing hI (numbered H).2.2
  obtain ⟨σR, r1, r2⟩ := sortSing hI (s := krSort) (by show krSort < nRegSorts + c.sortNames.length; decide +kernel)
  rw [(names H).2.2.2.1] at h1
  rw [(names H).2.2.2.2.1] at k1
  rw [(names H).2.2.2.2.2.2.1] at b1
  rw [(names H).2.2.2.2.2.1] at r1
  exact ⟨⟨σI, σK, σR, σB, h1, h2, k1, k2, r1, r2, b1, b2⟩⟩

end

/-! ## The equations 204 and 233 hold in every model of Γ -/

/-- The text sentences of Γ's equations, in `fnItems`'s order (`TiePair.fnTextOf`). -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all
noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- Each of Γ's equations is the translation of its text sentence (`TiePair.sameB`; kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel
theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

theorem fnText_index : fnText.map (·.index) =
    [204, 223, 231, 230, 229, 228, 237, 236, 239, 238, 235, 234, 212, 211, 222, 221, 218, 217, 220, 219,
     225, 224, 227, 226, 214, 213, 216, 215, 233, 232] := by
  decide +kernel

theorem text_mem : (trS U.ax204).pat ∈ textPats ∧ (trS U.ax233).pat ∈ textPats := by decide +kernel

/-- **A model of Γ satisfies the equation of `f` (204) and the first equation of `isKResult` (233).** -/
theorem eqns_sat (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H)) :
    (I ⊧ᴵ (trAxiom [] [] U.ax204).pat) ∧ (I ⊧ᴵ (trAxiom [] [] U.ax233).pat) := by
  rw [← trS_text U.ax204 (by simp), ← trS_text U.ax233 (by simp)]
  exact ⟨TiePair.entailed (shapeH H) _ text_mem.1 hI, TiePair.entailed (shapeH H) _ text_mem.2 hI⟩

section
variable (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- A value's element, in the sort its name gives. -/
theorem elem (hI : I ⊧ᴵP Γ (cH H)) {v : GroundTerm} {s : Srt} {n : String} {σ : M}
    (hv : (cH H).sortOf v = some s) (hn : (cH H).sortName s = n) (hσ : ∀ a, I.evalSymb (.sort ("Sort" ++ n)) a ↔ a = σ)
    (e : Valuation M) : (∀ m, (den (cH H) v).interpret I e m ↔ m = elemOf (cH H) I v) ∧ Inh I σ (elemOf (cH H) I v) := by
  obtain ⟨h1, h2⟩ := elemOf_spec hI hv e
  rw [hn] at h2
  have hS : ∀ a, (KoreAML.sym (.sort ("Sort" ++ n)) : KoreAML.P).interpret I e a ↔ a = σ := hσ
  exact ⟨h1, (KoreAML.interp_inhOf_of hS).mp h2⟩

/-- **`isKResult` of the element of `hG` is the element of `true`, in every model of Γ**: the
equation 233 at `X0 :=` that element and `V :=` the element of `inj{Int,KResult}(0)`, where `X0` is
in `kseq(inj{KResult,KItem}(V), dotk)` by the coherence of the injections along
`Int < KResult < KItem`; with the arity of `isKResult` off Bool. -/
theorem kr_hG (hI : I ⊧ᴵP Γ (cH H)) (F : Frame I) (m : M) :
    appE I "LblisKResult" (elemOf (cH H) I hG) m ↔ m = elemOf (cH H) I tG := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  have hax := (eqns_sat H hI).2
  let val : VarKey → M := fun k =>
    if k = .evar "X0" (KoreAML.srt "K") then elemOf (cH H) I hG
    else if k = .evar "VarKResult" (KoreAML.srt "KResult") then elemOf (cH H) I vG else F.σK
  let e1 : Valuation M := valOf k233 val
  have hX0 : e1.evalEvar (k233.ev (.evar "X0" (KoreAML.srt "K"))) = elemOf (cH H) I hG :=
    (valOf_ev (by decide)).trans (ite_eq_left rfl)
  have hV : e1.evalEvar (k233.ev (.evar "VarKResult" (KoreAML.srt "KResult"))) = elemOf (cH H) I vG :=
    (valOf_ev (by decide)).trans ((ite_eq_right (by decide)).trans (ite_eq_left rfl))
  have hRe : e1.evalEvar (k233.ev (.sortVar "R")) = F.σK :=
    (valOf_ev (by decide)).trans ((ite_eq_right (by decide)).trans (ite_eq_right (by decide)))
  obtain ⟨hh1, hh2⟩ := elem H hI (sorts H).2.2.1 (names H).2.2.2.2.1 F.hK1 e1
  obtain ⟨hv1, hv2⟩ := elem H hI (sorts H).2.1 (names H).2.2.2.2.2.1 F.hR1 e1
  obtain ⟨ht1, ht2⟩ := elem H hI (sorts H).1 (names H).2.2.2.2.2.2.1 F.hB1 e1
  have hSK : ∀ b, (KoreAML.trSort k233 (KoreAML.srt "K")).interpret I e1 b ↔ b = F.σK := fun b => by
    rw [trSort_srt]; exact F.hK1 b
  have hSKR : ∀ b, (KoreAML.trSort k233 (KoreAML.srt "KResult")).interpret I e1 b ↔ b = F.σR := fun b => by
    rw [trSort_srt]; exact F.hR1 b
  have hSB : ∀ b, (KoreAML.trSort k233 (KoreAML.srt "Bool")).interpret I e1 b ↔ b = F.σB := fun b => by
    rw [trSort_srt]; exact F.hB1 b
  have hRv : ∀ b, (KoreAML.trSort k233 KoreAML.R).interpret I e1 b ↔ b = F.σK := fun b => by
    rw [trSort_R, KoreAML.interp_evar, hRe]
  have hg : ∀ k ∈ (U.ax233.ax.sortVars.map sortVarKey ++ freeOf [] U.ax233.ax.pattern).eraseDups, ∀ m,
      (guardOf (tableOf U.ax233.ax.sortVars U.ax233.ax.pattern) k).interpret I e1 m := by
    rw [s233_keys.1, s233_keys.2]
    intro k hk m
    simp only [k233, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · rw [KoreAML.interp_guard_sortVar hD, hRe]; exact F.hK2
    · rw [KoreAML.interp_guard_evar hD, hX0, KoreAML.interp_inhOf_of hSK]; exact hh2
    · rw [KoreAML.interp_guard_evar hD, hV, KoreAML.interp_inhOf_of hSKR]; exact hv2
  have hP := (KoreAML.trAxiom_at hD hax e1 hg (elemOf (cH H) I hG)).mpr (by
    rw [s233_keys.2, s233_pattern]
    show (KoreAML.inhOf (KoreAML.trSort k233 KoreAML.R)).interpret I e1 _
    rw [KoreAML.interp_inhOf_of hRv]; exact hh2)
  rw [s233_keys.2, s233_pattern, KoreAML.tr, KoreAML.interp_sImp] at hP
  have hX0v : ∀ b, (KoreAML.tr ⟨k233, []⟩ (KoreAML.ev "X0" (KoreAML.srt "K"))).interpret I e1 b ↔
      b = elemOf (cH H) I hG := fun b => by rw [tr_var, hX0]
  obtain ⟨hz1, -⟩ := elem H hI (sorts H).2.2.2 (names H).2.2.2.1 F.hI1 e1
  have hzs := (elemOf_spec hI (sorts H).2.2.2 e1).2
  have hdv0 : ∀ m, (KoreAML.tr ⟨[], []⟩ dv0).interpret I e1 m ↔ m = elemOf (cH H) I zG := by
    rw [← (kores H).2.2]; exact hz1
  have hcoh := coh_at hI (a' := Srt.int) (a := krSort) (b := Srt.kitem) (subs H).1 (subs H).2 hdv0 hzs
  rw [(names H).2.2.2.1, (names H).2.2.2.2.2.1, kitem_name] at hcoh
  have hkp : ∀ b, (KoreAML.tr ⟨k233, []⟩ (kpatOf (KoreAML.ev "VarKResult" (KoreAML.srt "KResult")))).interpret I e1 b ↔
      b = elemOf (cH H) I hG := fun b => by
    unfold kpatOf
    refine (kseq_congr (t' := []) (e' := e1) (q' := KoreAML.injP "Int" "KItem" dv0) (fun m => ?_) b).trans ?_
    · refine (inj_congr (t' := []) (e' := e1) (p' := KoreAML.injP "Int" "KResult" dv0) (fun m' => ?_) m).trans ?_
      · rw [tr_var, hV, ← (kores H).2.1]; exact (hv1 m').symm
      · simp only [KoreAML.tr_injP]; exact hcoh m
    · rw [← (kores H).1]; exact hh1 b
  have hT : ∀ m, (KoreAML.tr ⟨k233, []⟩ (.top KoreAML.R)).interpret I e1 m ↔ Inh I F.σK m := fun m => by
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by rw [trSort_R]; simp [Pattern.isFreeEvar]; exact fun h => ev_ne_top h.symm),
      KoreAML.interp_inhOf_of hRv]
  have hTB : ∀ m, (KoreAML.tr ⟨k233, []⟩ (.top (KoreAML.srt "Bool"))).interpret I e1 m ↔ Inh I F.σB m := fun m => by
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of hSB]
  have hprem : (KoreAML.tr ⟨k233, []⟩ (.and KoreAML.R [.top KoreAML.R, .and KoreAML.R [Kore.Pattern.in (KoreAML.srt "K")
      KoreAML.R (KoreAML.ev "X0" (KoreAML.srt "K")) (kpatOf (KoreAML.ev "VarKResult" (KoreAML.srt "KResult"))),
      .top KoreAML.R]])).interpret I e1 (elemOf (cH H) I hG) := by
    simp only [KoreAML.tr, KoreAML.trAndList]
    rw [KoreAML.interp_sAnd, KoreAML.interp_sAnd]
    refine ⟨(hT _).mpr hh2, ?_, (hT _).mpr hh2⟩
    rw [KoreAML.interp_sIn hD hc hSK hRv F.hK2 F.hK2 (fun b hb => by rw [(hX0v b).mp hb]; exact hh2)]
    exact ⟨⟨_, (hX0v _).mpr rfl, (hkp _).mpr rfl⟩, hh2⟩
  have hC := hP.2 hprem
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hSB hRv F.hB2 F.hK2] at hC
  have hL : ∀ b, (KoreAML.tr ⟨k233, []⟩ (.app ⟨⟨"LblisKResult"⟩⟩ [] [KoreAML.ev "X0" (KoreAML.srt "K")])).interpret I e1 b ↔
      appE I "LblisKResult" (elemOf (cH H) I hG) b := fun b => by
    unfold KoreAML.ev; rw [tr_app1]; exact Iff.of_eq (congrArg (fun y => appE I "LblisKResult" y b) hX0)
  have hRt : ∀ b, (KoreAML.tr ⟨k233, []⟩ (.and (KoreAML.srt "Bool") [dvB, .top (KoreAML.srt "Bool")])).interpret I e1 b ↔
      b = elemOf (cH H) I tG ∧ Inh I F.σB b := fun b => by
    rw [KoreAML.tr]; simp only [KoreAML.trAndList]; rw [KoreAML.interp_sAnd, tr_dvB (e' := e1) k233 H, ht1, hTB]
  have hBool : ∀ b, Inh I F.σB b → (appE I "LblisKResult" (elemOf (cH H) I hG) b ↔ b = elemOf (cH H) I tG) :=
    fun b hb => (hL b).symm.trans ((hC.2 b hb).trans ((hRt b).trans ⟨And.left, fun h => ⟨h, hb⟩⟩))
  constructor
  · intro h
    exact (hBool m (arity H hI (kernels H).2 (heads H).2 (names H).2.2.2.2.1 (names H).2.2.2.2.2.2.1 F.hK1 F.hB1
      hh2 h)).mp h
  · intro h; subst h; exact (hBool _ ht2).mpr rfl

/-- **`f` is the identity on Int, in every model of Γ, at every element of Int** (not only at
values): the equation 204 at `HOLE :=` the element of `hG`, where `true andBool isKResult(HOLE)`
denotes the element of `true` (`kr_hG`, and the graph of `andBool` at `true, true`). -/
theorem f_id (hI : I ⊧ᴵP Γ (cH H)) (F : Frame I) {x : M} (hx : Inh I F.σI x) (a : M) :
    appE I "Lblf" x a ↔ a = x := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  have hax := (eqns_sat H hI).1
  let val : VarKey → M := fun k =>
    if k = .evar "VarHOLE" (KoreAML.srt "K") then elemOf (cH H) I hG
    else if k = .sortVar "R" then F.σI else x
  let e2 : Valuation M := valOf k204 val
  have hHe : e2.evalEvar (k204.ev (.evar "VarHOLE" (KoreAML.srt "K"))) = elemOf (cH H) I hG :=
    (valOf_ev (by decide)).trans (ite_eq_left rfl)
  have hRe : e2.evalEvar (k204.ev (.sortVar "R")) = F.σI :=
    (valOf_ev (by decide)).trans ((ite_eq_right (by decide)).trans (ite_eq_left rfl))
  have hX0e : e2.evalEvar (k204.ev (.evar "X0" (KoreAML.srt "Int"))) = x :=
    (valOf_ev (by decide)).trans ((ite_eq_right (by decide)).trans (ite_eq_right (by decide)))
  have hVXe : e2.evalEvar (k204.ev (.evar "VarX" (KoreAML.srt "Int"))) = x :=
    (valOf_ev (by decide)).trans ((ite_eq_right (by decide)).trans (ite_eq_right (by decide)))
  obtain ⟨hh1, hh2⟩ := elem H hI (sorts H).2.2.1 (names H).2.2.2.2.1 F.hK1 e2
  obtain ⟨ht1, -⟩ := elem H hI (sorts H).1 (names H).2.2.2.2.2.2.1 F.hB1 e2
  have hSI : ∀ b, (KoreAML.trSort k204 (KoreAML.srt "Int")).interpret I e2 b ↔ b = F.σI := fun b => by
    rw [trSort_srt]; exact F.hI1 b
  have hSK : ∀ b, (KoreAML.trSort k204 (KoreAML.srt "K")).interpret I e2 b ↔ b = F.σK := fun b => by
    rw [trSort_srt]; exact F.hK1 b
  have hSB : ∀ b, (KoreAML.trSort k204 (KoreAML.srt "Bool")).interpret I e2 b ↔ b = F.σB := fun b => by
    rw [trSort_srt]; exact F.hB1 b
  have hRv : ∀ b, (KoreAML.trSort k204 KoreAML.R).interpret I e2 b ↔ b = F.σI := fun b => by
    rw [trSort_R, KoreAML.interp_evar, hRe]
  have hg : ∀ k ∈ (U.ax204.ax.sortVars.map sortVarKey ++ freeOf [] U.ax204.ax.pattern).eraseDups, ∀ m,
      (guardOf (tableOf U.ax204.ax.sortVars U.ax204.ax.pattern) k).interpret I e2 m := by
    rw [s204_keys.1, s204_keys.2]
    intro k hk m
    simp only [k204, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · rw [KoreAML.interp_guard_sortVar hD, hRe]; exact F.hI2
    · rw [KoreAML.interp_guard_evar hD, hHe, KoreAML.interp_inhOf_of hSK]; exact hh2
    · rw [KoreAML.interp_guard_evar hD, hX0e, KoreAML.interp_inhOf_of hSI]; exact hx
    · rw [KoreAML.interp_guard_evar hD, hVXe, KoreAML.interp_inhOf_of hSI]; exact hx
  have hP := (KoreAML.trAxiom_at hD hax e2 hg x).mpr (by
    rw [s204_keys.2, s204_pattern]
    show (KoreAML.inhOf (KoreAML.trSort k204 KoreAML.R)).interpret I e2 x
    rw [KoreAML.interp_inhOf_of hRv]; exact hx)
  rw [s204_keys.2, s204_pattern, KoreAML.tr, KoreAML.interp_sImp] at hP
  -- `true andBool isKResult(HOLE)` denotes the element of `true`
  have hKR := kr_hG H hI F
  have hgraph := sat_dom hI (andBool_dom H)
  have hden : KoreAML.den (symApp (cH H) andS (GroundTerm.koreList (cH H) [tG, tG])) =
      (KoreAML.sym (.symbol "Lbl'Unds'andBool'Unds'") ⬝ den (cH H) tG) ⬝ den (cH H) tG := by
    unfold symApp; rw [(names H).2.2.1, (names H).2.2.2.2.2.2.2.1]; rfl
  have hAndG : ∀ b, ((KoreAML.sym (.symbol "Lbl'Unds'andBool'Unds'") ⬝ den (cH H) tG) ⬝ den (cH H) tG).interpret I e2 b ↔
      (den (cH H) tG).interpret I e2 b := by
    rw [← hden]; exact (KoreAML.interp_equal hD).mp (hgraph e2 default)
  have hAndP : ∀ b, (KoreAML.tr ⟨k204, []⟩ andP).interpret I e2 b ↔ b = elemOf (cH H) I tG := fun b => by
    unfold andP vHole KoreAML.ev
    rw [KoreAML.tr_app0, KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
    refine (KoreAML.interp_app_congr (KoreAML.interp_app_congr (fun _ => Iff.rfl) (fun m => tr_dvB k204 H m))
      (fun m => ?_) b).trans ((hAndG b).trans (ht1 b))
    rw [tr_app1]
    exact (Iff.of_eq (congrArg (fun y => appE I "LblisKResult" y m) hHe)).trans ((hKR m).trans (ht1 m).symm)
  have hX0v : ∀ b, (KoreAML.tr ⟨k204, []⟩ (vInt "X0")).interpret I e2 b ↔ b = x := fun b => by
    unfold vInt; rw [tr_var, hX0e]
  have hVXv : ∀ b, (KoreAML.tr ⟨k204, []⟩ (vInt "VarX")).interpret I e2 b ↔ b = x := fun b => by
    unfold vInt; rw [tr_var, hVXe]
  have hT : ∀ m, (KoreAML.tr ⟨k204, []⟩ (.top KoreAML.R)).interpret I e2 m ↔ Inh I F.σI m := fun m => by
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by rw [trSort_R]; simp [Pattern.isFreeEvar]; exact fun h => ev_ne_top h.symm),
      KoreAML.interp_inhOf_of hRv]
  have hTI : ∀ m, (KoreAML.tr ⟨k204, []⟩ (.top (KoreAML.srt "Int"))).interpret I e2 m ↔ Inh I F.σI m := fun m => by
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of hSI]
  have hprem : (KoreAML.tr ⟨k204, []⟩ (.and KoreAML.R [.equals (KoreAML.srt "Bool") KoreAML.R andP dvB,
      .and KoreAML.R [Kore.Pattern.in (KoreAML.srt "Int") KoreAML.R (vInt "X0") (vInt "VarX"), .top KoreAML.R]])).interpret
      I e2 x := by
    simp only [KoreAML.tr, KoreAML.trAndList]
    rw [KoreAML.interp_sAnd, KoreAML.interp_sAnd]
    refine ⟨?_, ?_, (hT x).mpr hx⟩
    · rw [KoreAML.interp_sEquals hD hc hSB hRv F.hB2 F.hI2 x]
      exact ⟨hx, fun b _ => (hAndP b).trans ((ht1 b).symm.trans (tr_dvB k204 H b).symm)⟩
    · rw [KoreAML.interp_sIn hD hc hSI hRv F.hI2 F.hI2 (fun b hb => by rw [(hX0v b).mp hb]; exact hx) x]
      exact ⟨⟨x, (hX0v x).mpr rfl, (hVXv x).mpr rfl⟩, hx⟩
  have hC := hP.2 hprem
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hSI hRv F.hI2 F.hI2] at hC
  have hL : ∀ b, (KoreAML.tr ⟨k204, []⟩ (fP (vInt "X0"))).interpret I e2 b ↔ appE I "Lblf" x b := fun b => by
    unfold fP vInt KoreAML.ev; rw [tr_app1]; exact Iff.of_eq (congrArg (fun y => appE I "Lblf" y b) hX0e)
  have hRt : ∀ b, (KoreAML.tr ⟨k204, []⟩ (.and (KoreAML.srt "Int") [vInt "VarX", .top (KoreAML.srt "Int")])).interpret
      I e2 b ↔ b = x ∧ Inh I F.σI b := fun b => by
    rw [KoreAML.tr]; simp only [KoreAML.trAndList]; rw [KoreAML.interp_sAnd, hVXv, hTI]
  have hInt : ∀ b, Inh I F.σI b → (appE I "Lblf" x b ↔ b = x) := fun b hb =>
    (hL b).symm.trans ((hC.2 b hb).trans ((hRt b).trans ⟨And.left, fun h => ⟨h, hb⟩⟩))
  exact ⟨fun h => (hInt a (arity H hI (kernels H).1 (heads H).1 (names H).2.2.2.1 (names H).2.2.2.1 F.hI1 F.hI1
    hx h)).mp h, fun h => by subst h; exact (hInt _ hx).mpr rfl⟩

end

/-! ## Sentence 205 -/

/-- **Sentence 205** (`f(f(X)) => f(X) requires true andBool isKResult(HOLE)`, `simplification`,
`cool`) **is entailed by Γ, for every H**: in every model of Γ, at every valuation, `f` is the
identity on Int (`f_id`), so both sides denote the element of `X`, whatever HOLE is. -/
theorem s205_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax205).pat := by
  intro M _ I hI e m
  rw [trS_text U.ax205 (by simp)]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨F⟩ := frame H hI
  unfold trAxiom
  dsimp only
  rw [s205_keys.1, s205_keys.2, s205_pattern]
  rw [interpret_impl]
  intro hg
  simp only [List.map, conjList, interpret_conj] at hg
  have hR := (interp_guard_sortVar hD).mp hg.1
  have hX := (interp_guard_evar hD).mp hg.2.2
  have hSI : ∀ b, (trSort k205 (KoreAML.srt "Int")).interpret I e b ↔ b = F.σI := fun b => by
    rw [trSort_srt]; exact F.hI1 b
  rw [interp_inhOf_of hSI] at hX
  have hRv : ∀ b, (trSort k205 KoreAML.R).interpret I e b ↔ b = e.evalEvar (k205.ev (.sortVar "R")) := fun b => by
    rw [trSort_R, KoreAML.interp_evar]
  have hTI : ∀ m, (KoreAML.tr ⟨k205, []⟩ (.top (KoreAML.srt "Int"))).interpret I e m ↔ Inh I F.σI m := fun m => by
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of hSI]
  have hinner : ∀ y, (KoreAML.sym (.symbol "Lblf") ⬝ KoreAML.tr ⟨k205, []⟩ (vInt "VarX")).interpret I e y ↔
      (KoreAML.tr ⟨k205, []⟩ (vInt "VarX")).interpret I e y := fun y => by
    have h1 := tr_app1 (I := I) (e := e) k205 "Lblf" (KoreAML.evar "VarX" (KoreAML.srt "Int")) y
    rw [KoreAML.tr_app0, KoreAML.trArgs_cons, KoreAML.trArgs_nil] at h1
    exact h1.trans ((f_id H hI F hX y).trans (tr_var k205 "VarX" (KoreAML.srt "Int") y).symm)
  have hfX : ∀ y, (KoreAML.tr ⟨k205, []⟩ (fP (vInt "VarX"))).interpret I e y ↔
      y = e.evalEvar (k205.ev (.evar "VarX" (KoreAML.srt "Int"))) := fun y => by
    unfold fP
    simp only [KoreAML.tr_app0, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
    exact (hinner y).trans (tr_var k205 "VarX" (KoreAML.srt "Int") y)
  have hff : ∀ b, (KoreAML.tr ⟨k205, []⟩ (fP (fP (vInt "VarX")))).interpret I e b ↔
      (KoreAML.tr ⟨k205, []⟩ (fP (vInt "VarX"))).interpret I e b := fun b => by
    unfold fP
    simp only [KoreAML.tr_app0, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
    exact KoreAML.interp_app_congr (fun _ => Iff.rfl) hinner b
  have hRt : ∀ b, (KoreAML.tr ⟨k205, []⟩ (.and (KoreAML.srt "Int") [fP (vInt "VarX"), .top (KoreAML.srt "Int")])).interpret
      I e b ↔ b = e.evalEvar (k205.ev (.evar "VarX" (KoreAML.srt "Int"))) ∧ Inh I F.σI b := fun b => by
    rw [KoreAML.tr]; simp only [KoreAML.trAndList]; rw [KoreAML.interp_sAnd, hfX, hTI]
  rw [interp_equal hD]
  intro a
  simp only [sortOf]
  rw [KoreAML.tr, interp_sImp]
  constructor
  · exact fun h => h.1
  · intro ha
    refine ⟨ha, fun _ => ?_⟩
    rw [KoreAML.tr, interp_sEquals hD hc hSI hRv F.hI2 hR]
    refine ⟨(interp_inhOf_of hRv).mp ha, fun b hb => ?_⟩
    rw [hff, hRt, hfX]
    exact ⟨fun h => ⟨h, hb⟩, And.left⟩

/-- **The user lemma of e2-cool-eq (205) is entailed, for every H**: `TieE2CoolEq.UserLemmaEntailed`
over its one sentence. -/
theorem userlemma_entailed : ∀ (H : HookParams), ∀ ad ∈ [U.ax205], Γ (cH H) ⊧ (trS ad).pat := by
  intro H ad had
  rw [List.mem_singleton.mp had]
  exact s205_entailed H

end KCore.CoolEq205

/-- info: 'KCore.CoolEq205.s205_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.CoolEq205.s205_entailed
