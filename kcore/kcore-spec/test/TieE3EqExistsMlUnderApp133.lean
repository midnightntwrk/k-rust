/-
  The companion of sentence 133 of fixture `e3-eq-exists-ml-under-app` (test/constructs/fixtures),
  on the fixture's kompiled text `f2-examples/e3-eq-exists-ml-under-app.kompile.kore`:
  `rule f(X) => g(#Exists B:Bool. (B #And {B #Equals X}))`, f and g `total`, `rule g(B) => notBool B`.
  Run from the package root: `lake env lean -j1 test/TieE3EqExistsMlUnderApp133.lean`.

  The reader moves the binder to the top of the right side and reads the equation by cases
  (`existsAsCases`): Γ holds three equations of f (`spItems`, the first three of `TiePair.gammaPats c`):
  `g(true)` under `⌈g(true)⌉ ∧ true = X`, `g(false)` under `⌈g(false)⌉ ∧ false = X`, and a last one
  under `¬∃B:Bool. (⌈g(B)⌉ ∧ B = X)` (`read`, `gamma_shape_fun`).

  - `text_shape`, `hoist_ok`, `hoisted_shape` (kernel): the translated sentence is `eqnPat` with the
    right side `tr (g(∃B. φ)) ∧ ⊤`; the decision `TieExHoistB.hoistB` holds between it and
    `∃B. g(φ)`, so the sentence holds where the one with the binder at the top does (`eqnPat_hoistB`).
  - `exReadB_fun` (kernel): the decision `TieEXReadB.exReadB` of the readings of the hoisted body
    `g(B ∧ (B = X))`, at the semantics with any hook parameters; `facts`: the six readings.
  - `sp_from_text_nodeFacts`, for every H: in an interpretation with `NodeFacts (cH H)` and
    `TermsInSort (cH H)`, sentence 133 and f's functional sentence 62 give Γ's three items
    (`TieEX.ex_clause_of_text`, `ex_last_of_text`). The two hypotheses are facts of the
    interpretation and not sentences of the text: `NodeFacts` holds that each literal of Bool is one
    element of Bool and that distinct values are apart (items of `ΓDomains`), and `TermsInSort` that
    `g(B)` lies in Bool. The proof reads them; whether the three items follow from the two
    sentences with the text's signature (`ΓSig`) alone is not shown by this statement.
  - `sp_from_text_sig`, for every H: Γ's three items hold in every model of `PreText H`, which is
    sentences 133 and 62, the four sentences of the Bool literals (151, 72, 167, 83), K's
    G-nonempty item (an item of the text's signature, `kNonempty_text`) and `ΓSig (cH H)`. The
    signature gives definedness, the item of `⌈_⌉`, that each numbered sort is one sort and that
    the terms read lie in their sorts (none holds an injection, `ni_facts`); the four sentences
    give that each Bool literal is one element of Bool (`lit_of_text`). That two values are apart
    is not read.
  - `sp_entailed`, for every H: `Γc (cH H)` entails sentence 133, from Γ's three items and
    `boolClosed` (`TieEX.ex_text_of_split`). `boolClosed` is the item of `Γcl`, a sentence of `Γc`
    and not of `Γ` (`readsConfined_c`); f's functional sentence is not read.
  - `f(true) = false`: `f_true_of_item` from Γ's item of the clause at `true`, g's sentence 134
    and the graph of `notBool` at `true` (an item of `ΓDomains`), in an interpretation with the two
    facts above; `f_true_from_text_nodeFacts` from the sentences 133, 62 and 134 under the same
    hypotheses; `f_true_c` in every model of `Γc (cH H)`, for every H (g's item is sentence 134 as
    written, `g_at`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3EqExistsMlUnderApp133

open ML KoreAML KoreAML.TieFR KCore.TieEX KCore.TieEXReadB KCore.TieExHoistB

kore_term kore from "f2-examples/e3-eq-exists-ml-under-app.kompile.kore"
definition_of defn from "f2-examples/e3-eq-exists-ml-under-app.kompile.kore"
user_axioms U from "f2-examples/e3-eq-exists-ml-under-app.kompile.kore" module "E3-EQ-EXISTS-ML-UNDER-APP"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The definition reads a confined sort, and Bool holds its literals only: its theory is `Γc`,
which holds `boolClosed`. -/
theorem readsConfined_c : c.readsConfined = true ∧ c.litSort Srt.bool = true := by
  constructor <;> decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

def Fs : Sym := 384
def Gs : Sym := 385
theorem names : c.symName Fs = "Lblf" ∧ c.symName Gs = "Lblg" := by constructor <;> decide +kernel

def litT (b : Bool) : Term := .dv Srt.bool (.bool b)
def xLit (b : Bool) : Term × List Cond := (.app Gs [litT b], [.equals Srt.bool (litT b) (.var 0)])
def jB : Term × List Cond := (.app Gs [.var 1], [.equals Srt.bool (.var 1) (.var 0)])

def fFn : Fn := ⟨Fs, [Srt.bool], Srt.bool,
  Parse.exClauses Srt.bool [Srt.bool] [.var 0] none 50 false [xLit true, xLit false] [jB], true⟩
def gFn : Fn := ⟨Gs, [Srt.bool], Srt.bool,
  [⟨[Srt.bool], [.var 0], none, .app boolNot [.var 0], none, 50, false, [], .top, .top⟩], true⟩

theorem read : c.fns = [fFn, gFn] := by kernel_rfl

def bS : Kore.KSort := srt "Bool"
def Xp : Kore.Pattern := ev "VarX" bS
def Bp : Kore.Pattern := ev "VarB" bS
def bodyP : Kore.Pattern := .and bS [Bp, .equals bS bS Bp Xp]
def rhsK : Kore.Pattern := ap "Lblg" [.exist bS (evar "VarB" bS) bodyP]
def bodyG : Kore.Pattern := ap "Lblg" [bodyP]
def rhsH : Kore.Pattern := .exist bS (evar "VarB" bS) bodyG
def premK : Kore.Pattern := .and R [.top R, .and R [.in bS R (ev "X0" bS) Xp, .top R]]
def FK : Kore.Pattern := ap "Lblf" [ev "X0" bS]

theorem ax133_eq : U.ax133.ax.sortVars = [Rv] ∧
    U.ax133.ax.pattern = .implies R premK (.equals bS R FK (.and bS [rhsK, .top bS])) := by
  constructor <;> decide +kernel

theorem ax62_eq : U.ax62.ax.sortVars = [Rv] ∧
    U.ax62.ax.pattern = .exist R (evar "Val" bS) (.equals bS R (.var (.evar (evar "Val" bS))) (ap "Lblf" [ev "K0" bS])) := by
  constructor <;> decide +kernel

theorem ax134_eq : U.ax134.ax.sortVars = [Rv] ∧
    U.ax134.ax.pattern = .implies R (.and R [.top R, .and R [.in bS R (ev "X0" bS) Bp, .top R]])
      (.equals bS R (ap "Lblg" [ev "X0" bS]) (.and bS [ap "LblnotBool'Unds'" [Bp], .top bS])) := by
  constructor <;> decide +kernel

noncomputable def tbl : VarTable := tableOf U.ax133.ax.sortVars U.ax133.ax.pattern
noncomputable abbrev ctx : Ctx := ⟨tbl, kore.aliasNames⟩
def tblG : VarTable := [.sortVar "R", .evar "X0" bS, .evar "VarV0" bS, .evar "VarV1" bS]
noncomputable def ws : List P := guardsOf U.ax133.ax
def rG : EVar := tblG.ev (sortVarKey Rv)
noncomputable def prem : P := tr ctx premK
noncomputable def BoolP : P := trSort tbl bS
noncomputable def Ff : P := tr ctx FK
def vsF : List KoreAML.Var := [⟨"X", "Bool"⟩]
def Bv : KoreAML.Var := ⟨"B", "Bool"⟩
noncomputable def xB : EVar := tbl.ev (evarKey Bv.kore)
noncomputable def ensT : P := tr ctx (.top bS)

theorem tbl_eq : tbl = [.sortVar "R", .evar "X0" bS, .evar "VarX" bS, .evar "VarB" bS] := by decide +kernel

theorem text_shape : (trS U.ax133).pat = eqnPat ws rG prem BoolP Ff (sAnd (tr ctx rhsK) ensT) := by
  decide +kernel

theorem hoist_ok : hoistB ctx rhsK rhsH = true := by decide +kernel

theorem hoisted_shape : tr ctx rhsH = sExists xB TieFRRead.boolP (tr ctx bodyG) := by decide +kernel

noncomputable def NT : Parse.Names :=
  { sorts := c.sortNames
    syms := c.symNames
    keyFns := [(Fs, "Bool"), (Gs, "Bool")]
    fnlSyms := [("Lblf", false)]
    boolLits := true }

theorem exReadB_c : exReadB NT c tblG tbl [Srt.bool] vsF Bv Srt.bool bodyG (.top bS)
    (xLit true) (xLit false) jB = true := by decide +kernel

theorem exReadB_fun : (fun Hk : HookParams => exReadB NT (c.withHooks Hk) tblG tbl [Srt.bool] vsF Bv Srt.bool bodyG
    (.top bS) (xLit true) (xLit false) jB) = fun _ => true := by kernel_rfl

theorem lit_facts : Parse.varSorts NT vsF = .ok [Srt.bool] ∧ TieFRVars.guardsHold ws tbl vsF = true ∧
    sortGuard (tblG.ev (sortVarKey Rv)) ∈ ws ∧ BoolP = TieFRRead.boolP ∧
    TieFRRead.aliasFreeFR kore.aliasNames bodyG = true ∧ TieFRRead.aliasFreeFR kore.aliasNames (.top bS) = true :=
  ⟨by kernel_rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

noncomputable def spItems : List P := (TiePair.gammaPats c).take 3

noncomputable def gShape (d : Semantics) : List P :=
  [eqnPat ws rG (clauseQC d tblG (Faithful.canonVars d [Srt.bool]) Srt.bool prem (xLit true)) BoolP Ff
     (sAnd (altPC d tblG (Faithful.canonVars d [Srt.bool]) (xLit true)) (sTop BoolP)),
   eqnPat ws rG (clauseQC d tblG (Faithful.canonVars d [Srt.bool]) Srt.bool prem (xLit false)) BoolP Ff
     (sAnd (altPC d tblG (Faithful.canonVars d [Srt.bool]) (xLit false)) (sTop BoolP)),
   eqnPat ws rG (lastBQC d tblG (Faithful.canonVars d [Srt.bool]) Srt.bool prem [jB]) BoolP Ff
     (sAnd (altPC d tblG (Faithful.canonVars d [Srt.bool]) (xLit true))
       (tr ⟨tblG, []⟩ (reqPat (srtOf d Srt.bool)
         (some (Term.kore d (Faithful.canonVars d [Srt.bool]) (Parse.boolT false))))))]

theorem gamma_shape_fun : (fun Hk : HookParams => gShape (c.withHooks Hk)) = fun _ => spItems := by kernel_rfl

/-! ## f's functional sentence -/

noncomputable def tblF : VarTable := tableOf U.ax62.ax.sortVars U.ax62.ax.pattern
noncomputable def rF : EVar := tblF.ev (sortVarKey Rv)
noncomputable def vF : EVar := tblF.ev (evarKey (evar "Val" bS))
noncomputable def k0 : EVar := tblF.ev (evarKey (evar "K0" bS))
noncomputable def x0 : EVar := tbl.ev (evarKey (evar "X0" bS))
def fHead : P := sym (.symbol "Lblf")
noncomputable def tsF : List (EVar × EVar × P) := [(x0, k0, BoolP)]

theorem fnl_shape : (trS U.ax62).pat =
    fnlPat (sortGuard rF :: tsF.map fun t => (t.2.1 ∈∈ inhOf t.2.2)) rF vF BoolP
      (appList fHead (tsF.map fun t => .evar t.2.1)) := by decide +kernel

theorem idx_facts :
    Ff = appList fHead (tsF.map fun t => .evar t.1) ∧ (tsF.map (·.2.1)).Nodup ∧ rF ∉ tsF.map (·.2.1) ∧
      vF ∉ tsF.map (·.2.1) ∧ vF ≠ rF ∧ (x0 ∈∈ inhOf BoolP) ∈ ws := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## In a model -/

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

theorem facts (H : HookParams) (F : HoldsShape.NodeFacts (cH H) I) (hTS : Faithful.TermsInSort (cH H) I) :
    ∃ β, SortAt I BoolP β ∧
      (∀ (e : Valuation M) a, (trSort tblG (srtOf (cH H) Srt.bool)).interpret I e a ↔ a = β) ∧
      ExFacts I (cH H) tblG (Faithful.canonVars (cH H) [Srt.bool]) ws β (xsOfB (xLit true) (xLit false)) [jB]
        (tr ctx bodyG) ensT xB (CGof I (cH H) tblG (Faithful.canonVars (cH H) [Srt.bool]))
        (CGof I (cH H) tblG (vsBof (cH H) [Srt.bool])) := by
  obtain ⟨β, hβ, hβd⟩ := TieFRRead.boolDen_of F
  obtain ⟨hvars, hg, hr, hBP, hal, hal'⟩ := lit_facts
  have hσ : ∀ (e : Valuation M) a, (trSort tblG (srtOf (cH H) Srt.bool)).interpret I e a ↔ a = β := fun e a => by
    have h := hβd e a
    rw [srtOf, Faithful.sortName_bool, Faithful.trSort_srt]
    exact h
  have hd : ∀ (e : Valuation M) a, BoolP.interpret I e a ↔ a = β := fun e a => by rw [hBP]; exact hβd e a
  exact ⟨β, ⟨hd, hβ, by rw [hBP]; rfl⟩, hσ,
    exFacts_of_exB F hTS rfl rfl (al := kore.aliasNames) hvars hg hr hσ hβ hal hal' (congrFun exReadB_fun H)⟩

theorem sp_from_text_nodeFacts (H : HookParams) (F : HoldsShape.NodeFacts (cH H) I) (hTS : Faithful.TermsInSort (cH H) I)
    (hT : I ⊧ᴵ (trS U.ax133).pat) (hF : I ⊧ᴵ (trS U.ax62).pat) : ∀ φ ∈ spItems, I ⊧ᴵ φ := by
  obtain ⟨β, hS, hσ, X⟩ := facts H F hTS
  obtain ⟨-, -, hr, hBP, -, -⟩ := lit_facts
  have hG : GuardsPred I ws := guardsOf_pred F.defOK U.ax133.ax
  rw [text_shape] at hT
  have hT' := (eqnPat_hoistB F.defOK hoist_ok).mp hT
  rw [hoisted_shape] at hT'
  rw [fnl_shape] at hF
  obtain ⟨hFf, hnd, hrk, hvk, hvr, hx0⟩ := idx_facts
  have hone : ∀ e m, At I ws rG e m → ∃ y, Inh I β y ∧ ∀ a, Inh I β a → (Ff.interpret I e a ↔ a = y) := by
    intro e m hat
    rw [hFf]
    exact one_of_fnl F.defOK F.ceilDef hS.den hS.isSort hr hF (Closed.sym _) hnd hrk hvk hvr rfl
      (fun t ht => by
        simp only [tsF, List.mem_singleton] at ht
        subst ht
        exact ⟨hx0, by rw [hBP]; exact Closed.sym _⟩) hat
  have hcl := fun (x : Term × List Cond)
      (hx : x ∈ xsOfB (xLit true) (xLit false) true ++ xsOfB (xLit true) (xLit false) false) =>
    ex_clause_of_text F (tbl := tblG) (vs := Faithful.canonVars (cH H) [Srt.bool]) (s := Srt.bool)
      hS hG hr hσ X.hin X.hcond X.hbody hT' hone hx
  have hl := ex_last_of_text F (tbl := tblG) (vs := Faithful.canonVars (cH H) [Srt.bool]) (s := Srt.bool)
      hS hG hr hσ X.hxr X.hinB X.hcondB X.hbodyB hT' hone
      (sAnd (altPC (cH H) tblG (Faithful.canonVars (cH H) [Srt.bool]) (xLit true))
        (tr ⟨tblG, []⟩ (reqPat (srtOf (cH H) Srt.bool)
          (some (Term.kore (cH H) (Faithful.canonVars (cH H) [Srt.bool]) (Parse.boolT false))))))
  have hg : gShape (cH H) = spItems := congrFun gamma_shape_fun H
  intro φ hφ
  rw [← hg] at hφ
  simp only [gShape, List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl | rfl
  · exact hcl _ (List.mem_cons_self ..)
  · exact hcl _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · exact hl

/-! ### From the text and its signature

  | sentence | index |
  |---|---|
  | `rule isK(K) => true` | 151 |
  | functional sentence of `isK` | 72 |
  | `rule notBool true => false` | 167 |
  | functional sentence of `notBool_` | 83 |
-/

/-- The terms the readings take hold no injection (kernel): the operands `tightB` reads of the
hoisted body as terms, and the last alternative's term. -/
theorem ni_facts : TieFRSig.tightNIB NT (vsF ++ [Bv]) bodyG = true ∧ TieFRSig.injFree jB.1 = true := by
  decide +kernel

/-- The readings in a model with `LitFacts` and `TermsInSortNI`. -/
theorem factsL (H : HookParams) (F : TieEXSig.LitFacts (cH H) I) (hTS : TieFRSig.TermsInSortNI (cH H) I) :
    ∃ β, SortAt I BoolP β ∧
      (∀ (e : Valuation M) a, (trSort tblG (srtOf (cH H) Srt.bool)).interpret I e a ↔ a = β) ∧
      ExFacts I (cH H) tblG (Faithful.canonVars (cH H) [Srt.bool]) ws β (xsOfB (xLit true) (xLit false)) [jB]
        (tr ctx bodyG) ensT xB (CGof I (cH H) tblG (Faithful.canonVars (cH H) [Srt.bool]))
        (CGof I (cH H) tblG (vsBof (cH H) [Srt.bool])) := by
  obtain ⟨β, hβ, hβd⟩ := TieFRSig.boolDen_of_sig F.sig
  obtain ⟨hvars, hg, hr, hBP, hal, hal'⟩ := lit_facts
  have hσ : ∀ (e : Valuation M) a, (trSort tblG (srtOf (cH H) Srt.bool)).interpret I e a ↔ a = β := fun e a => by
    have h := hβd e a
    rw [srtOf, Faithful.sortName_bool, Faithful.trSort_srt]
    exact h
  have hd : ∀ (e : Valuation M) a, BoolP.interpret I e a ↔ a = β := fun e a => by rw [hBP]; exact hβd e a
  exact ⟨β, ⟨hd, hβ, by rw [hBP]; rfl⟩, hσ,
    TieEXSig.exFacts_of_exB_lit F hTS rfl rfl (al := kore.aliasNames) ni_facts.1 ni_facts.2 hvars hg hr hσ hβ
      hal hal' (congrFun exReadB_fun H)⟩

/-- Γ's three items in a model of sentences 133 and 62 with `LitFacts` and `TermsInSortNI`. -/
theorem sp_of_litFacts (H : HookParams) (F : TieEXSig.LitFacts (cH H) I) (hTS : TieFRSig.TermsInSortNI (cH H) I)
    (hT : I ⊧ᴵ (trS U.ax133).pat) (hF : I ⊧ᴵ (trS U.ax62).pat) : ∀ φ ∈ spItems, I ⊧ᴵ φ := by
  obtain ⟨β, hS, hσ, X⟩ := factsL H F hTS
  obtain ⟨-, -, hr, hBP, -, -⟩ := lit_facts
  have hG : GuardsPred I ws := guardsOf_pred F.sig.defOK U.ax133.ax
  rw [text_shape] at hT
  have hT' := (eqnPat_hoistB F.sig.defOK hoist_ok).mp hT
  rw [hoisted_shape] at hT'
  rw [fnl_shape] at hF
  obtain ⟨hFf, hnd, hrk, hvk, hvr, hx0⟩ := idx_facts
  have hone : ∀ e m, At I ws rG e m → ∃ y, Inh I β y ∧ ∀ a, Inh I β a → (Ff.interpret I e a ↔ a = y) := by
    intro e m hat
    rw [hFf]
    exact one_of_fnl F.sig.defOK F.sig.ceilDef hS.den hS.isSort hr hF (Closed.sym _) hnd hrk hvk hvr rfl
      (fun t ht => by
        simp only [tsF, List.mem_singleton] at ht
        subst ht
        exact ⟨hx0, by rw [hBP]; exact Closed.sym _⟩) hat
  have hcl := fun (x : Term × List Cond)
      (hx : x ∈ xsOfB (xLit true) (xLit false) true ++ xsOfB (xLit true) (xLit false) false) =>
    TieEXSig.ex_clause_of_text_lit F (tbl := tblG) (vs := Faithful.canonVars (cH H) [Srt.bool]) (s := Srt.bool)
      (CG := CGof I (cH H) tblG (Faithful.canonVars (cH H) [Srt.bool])) hS hG hr hσ X.hin X.hcond X.hbody hT' hone hx
  have hl := TieEXSig.ex_last_of_text_lit F (tbl := tblG) (vs := Faithful.canonVars (cH H) [Srt.bool]) (s := Srt.bool)
      (CGB := CGof I (cH H) tblG (vsBof (cH H) [Srt.bool]))
      hS hG hr hσ X.hxr X.hinB X.hcondB X.hbodyB hT' hone
      (sAnd (altPC (cH H) tblG (Faithful.canonVars (cH H) [Srt.bool]) (xLit true))
        (tr ⟨tblG, []⟩ (reqPat (srtOf (cH H) Srt.bool)
          (some (Term.kore (cH H) (Faithful.canonVars (cH H) [Srt.bool]) (Parse.boolT false))))))
  have hg : gShape (cH H) = spItems := congrFun gamma_shape_fun H
  intro φ hφ
  rw [← hg] at hφ
  simp only [gShape, List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl | rfl
  · exact hcl _ (List.mem_cons_self ..)
  · exact hcl _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · exact hl

/-- The four sentences of the Bool literals are sentences of the user module, at these indices. -/
theorem lit_idx : [U.ax151, U.ax72, U.ax167, U.ax83].map (·.index) = [151, 72, 167, 83] ∧
    [151, 72, 167, 83].all (fun i => (U.all.map (·.index)).contains i) = true := by
  constructor <;> decide +kernel

/-- **Each of the four is the library's pattern of its sentence** (kernel). -/
theorem lit_sents :
    (trS U.ax151).pat = TieReqBool.sentPat TieReqBool.isKTrueAx ∧
    (trS U.ax72).pat = TieReqBool.sentPat (TieReqBool.fnl1Ax "LblisK" "K") ∧
    (trS U.ax167).pat = TieReqBool.sentPat TieReqBool.notTrueFalseAx ∧
    (trS U.ax83).pat = TieReqBool.sentPat (TieReqBool.fnl1Ax "LblnotBool'Unds'" "Bool") := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- K's G-nonempty item. -/
def kNonempty : P := (nonemptyItem ⟨"SortK", [], false⟩).pat

/-- It is an item of the text's signature (`ΓSig` does not hold it). -/
theorem kNonempty_text : ((Theory.ofDefinition kore).signature.map (·.pat)).contains kNonempty = true := by
  decide +kernel

/-- The premises from the text: sentences 133 and 62, the four sentences of the Bool literals, K's
G-nonempty item, and the signature. -/
noncomputable abbrev PreText (H : HookParams) : Premises KoreAML.Sym :=
  TiePair.Texts [(trS U.ax133).pat, (trS U.ax62).pat, (trS U.ax151).pat, (trS U.ax72).pat, (trS U.ax167).pat,
    (trS U.ax83).pat] ∪ (fun φ => φ = kNonempty) ∪ Faithful.ΓSig (cH H)

theorem k_name (H : HookParams) : (cH H).sortName Srt.k = "K" :=
  (by decide +kernel : c.sortName Srt.k = "K")
theorem k_numbered (H : HookParams) : Srt.k < nRegSorts + (cH H).sortNames.length :=
  Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)

theorem den_lit (H : HookParams) (b : Bool) :
    den (cH H) (KCore.bool b) = TieReqBool.litP (if b then "true" else "false") := by
  show den c (KCore.bool b) = _; cases b <;> decide +kernel

/-- **Each of `true` and `false` denotes one element, an element of Bool**, in a model of
`PreText H`, for every H: at an element of K, `isK` of it is one element of Bool that agrees with
`true` (72, 151), and `notBool` of that one is one element of Bool that agrees with `false`
(83, 167); a literal holds nothing outside Bool by its arity item in `ΓSig`. -/
theorem lit_of_text (H : HookParams) (hI : I ⊧ᴵP PreText H) (b : Bool) (e : Valuation M) :
    ∃ y, (∀ m, (den (cH H) (KCore.bool b)).interpret I e m ↔ m = y) ∧ (inhOf TieFRRead.boolP).interpret I e y := by
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  have hSig : I ⊧ᴵP Faithful.ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨s1, s2, s3, s4⟩ := lit_sents
  have hT : ∀ φ ∈ [(trS U.ax133).pat, (trS U.ax62).pat, (trS U.ax151).pat, (trS U.ax72).pat, (trS U.ax167).pat,
      (trS U.ax83).pat], I ⊧ᴵ φ := fun φ hφ => hI φ (Or.inl (Or.inl (Or.inl hφ)))
  obtain ⟨aF, aT, hF, hTr, hiF, hiT⟩ := TieReqBool.boolLits_of_bool_text_sig hD hSig (k_numbered H) (k_name H)
    (hI _ (Or.inl (Or.inr rfl)))
    (s1 ▸ hT _ (.tail _ (.tail _ (.head _)))) (s2 ▸ hT _ (.tail _ (.tail _ (.tail _ (.head _)))))
    (s3 ▸ hT _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    (s4 ▸ hT _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) e
  rw [den_lit]
  cases b
  · exact ⟨aF, hF, hiF⟩
  · exact ⟨aT, hTr, hiT⟩

/-- **Γ's three items for f are consequences of the text's sentences and its signature**, for
every H: in a model of `PreText H`. Each premise is a sentence of the text, an item of its
signature (`kNonempty_text`), or an item of `ΓSig (cH H)`; the terms read hold no injection
(`ni_facts`). No `boolClosed`, and nothing of two values being apart. -/
theorem sp_from_text_sig (H : HookParams) (hI : I ⊧ᴵP PreText H) : ∀ φ ∈ spItems, I ⊧ᴵ φ := by
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  have hSig : I ⊧ᴵP Faithful.ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  obtain ⟨F, hTS⟩ := TieFRSig.sig_of_core (coreOKH H) hD hSig
  exact sp_of_litFacts H ⟨F, lit_of_text H hI⟩ hTS (hI _ (Or.inl (Or.inl (Or.inl (.head _)))))
    (hI _ (Or.inl (Or.inl (Or.inl (.tail _ (.head _))))))

omit [Inhabited M] in
theorem spItems_sat (H : HookParams) (hI : I ⊧ᴵP Faithful.Γ (cH H)) : ∀ φ ∈ spItems, I ⊧ᴵ φ := by
  intro φ hφ
  have hm : φ ∈ TiePair.gammaPats c := List.mem_of_mem_take hφ
  unfold TiePair.gammaPats at hm
  obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hm
  exact hI _ (TiePair.mem_Γ_fns (Or.inl ⟨it, by rw [TiePair.fnItems_withHooks]; exact hit, rfl⟩))

end

theorem sp_entailed (H : HookParams) : Faithful.Γc (cH H) ⊧ (trS U.ax133).pat := by
  intro M _ I hIc
  have hI : I ⊧ᴵP Faithful.Γ (cH H) := fun φ hφ => hIc φ (Or.inl hφ)
  have F := HoldsShape.nodeFacts_of_core (coreOKH H) hIc
  have hTS : Faithful.TermsInSort (cH H) I := Faithful.termsInSort_of_core (coreOKH H) hI
  have hcl : I ⊧ᴵ Faithful.boolClosed (cH H) :=
    hIc _ (Or.inr ⟨(Semantics.readsConfined_withHooks c H).trans readsConfined_c.1, readsConfined_c.2, rfl⟩)
  obtain ⟨β, hS, hσ, X⟩ := facts H F hTS
  obtain ⟨-, -, hr, -, -, -⟩ := lit_facts
  have hG : GuardsPred I ws := guardsOf_pred F.defOK U.ax133.ax
  have hg : gShape (cH H) = spItems := congrFun gamma_shape_fun H
  have hs : ∀ φ ∈ gShape (cH H), I ⊧ᴵ φ := by rw [hg]; exact spItems_sat H hI
  have hk : ∀ x ∈ xsOfB (xLit true) (xLit false) true ++ xsOfB (xLit true) (xLit false) false,
      I ⊧ᴵ eqnPat ws rG (clauseQC (cH H) tblG (Faithful.canonVars (cH H) [Srt.bool]) Srt.bool prem x) BoolP Ff
        (sAnd (altPC (cH H) tblG (Faithful.canonVars (cH H) [Srt.bool]) x) (sTop BoolP)) := by
    intro x hx
    simp only [xsOfB, Bool.cond_true, Bool.cond_false, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hs _ (List.mem_cons_self ..)
    · exact hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hn := hs _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have h := ex_text_of_split F hcl (tbl := tblG) (vs := Faithful.canonVars (cH H) [Srt.bool]) (s := Srt.bool)
    (SR := srtOf (cH H) Srt.bool) hS hG hr hσ hσ X.hin X.hcond X.hbody X.hxr X.hinB X.hcondB X.hbodyB hk hn
  rw [text_shape]
  refine (eqnPat_hoistB F.defOK hoist_ok).mpr ?_
  rw [hoisted_shape]
  exact h

/-! ## `f(true) = false` -/

noncomputable def xV : EVar := tbl.ev (evarKey (evar "VarX" bS))
noncomputable abbrev vsH (H : HookParams) : List KoreAML.Var := Faithful.canonVars (cH H) [Srt.bool]

theorem val_facts :
    tbl.ev (.sortVar "R") = rG ∧ tbl.ev (.evar "X0" bS) = x0 ∧ tbl.ev (.evar "VarX" bS) = xV ∧
      x0 ≠ rG ∧ xV ≠ rG ∧
      ws = [guardOf tbl (.sortVar "R"), guardOf tbl (.evar "X0" bS), guardOf tbl (.evar "VarX" bS)] ∧
      prem = sAnd (sTop (.evar rG)) (sAnd (sIn BoolP (.evar rG) (.evar x0) (.evar xV)) (sTop (.evar rG))) ∧
      Ff = sym (.symbol "Lblf") ⬝ .evar x0 ∧
      (trS U.ax134).pat = eqnPat ws rG prem BoolP (sym (.symbol "Lblg") ⬝ .evar x0)
        (sAnd (sym (.symbol "LblnotBool'Unds'") ⬝ .evar xV) (sTop BoolP)) ∧
      (Pattern.evar rG : P).isFreeEvar topVar = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem appF_fun : (fun Hk : HookParams => TiePair.app (c.withHooks Hk) Fs [bool true]) =
    fun Hk => sym (.symbol "Lblf") ⬝ den (c.withHooks Hk) (bool true) := by kernel_rfl
theorem appNot_fun : (fun Hk : HookParams => TiePair.app (c.withHooks Hk) boolNot [bool true]) =
    fun Hk => sym (.symbol "LblnotBool'Unds'") ⬝ den (c.withHooks Hk) (bool true) := by kernel_rfl
theorem altG_fun : (fun Hk : HookParams => altPC (c.withHooks Hk) tblG (Faithful.canonVars (c.withHooks Hk) [Srt.bool])
    (xLit true)) = fun Hk => sym (.symbol "Lblg") ⬝ den (c.withHooks Hk) (bool true) := by kernel_rfl
theorem condT_fun : (fun Hk : HookParams => tr ⟨tblG, []⟩ (Cond.kore (c.withHooks Hk)
    (Faithful.canonVars (c.withHooks Hk) [Srt.bool]) R (.equals Srt.bool (litT true) (.var 0)))) =
    fun Hk => sEquals BoolP (.evar rG) (den (c.withHooks Hk) (bool true)) (.evar xV) := by kernel_rfl
theorem termF_fun : (fun Hk : HookParams => tr ⟨tblG, []⟩ (Term.kore (c.withHooks Hk)
    (Faithful.canonVars (c.withHooks Hk) []) (.app Fs [litT true]))) =
    fun Hk => sym (.symbol "Lblf") ⬝ den (c.withHooks Hk) (bool true) := by kernel_rfl
theorem sortF_fun : (fun Hk : HookParams => sortOfTerm ((c.withHooks Hk).rhsCtx ((c.withHooks Hk).fns.map Fn.sig)) []
    (.app Fs [litT true])) = fun _ => some Srt.bool := by kernel_rfl

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **`f(true) = false` from Γ's item of the clause at `true`, g's sentence 134 and the graph of
`notBool` at `true`**: at X := the element of `true` the clause's premise holds (`g(true)` is
`notBool(true)`, the element of `false`, and `true = X`), so `f(true)` is `g(true)` on Bool, and
f's results lie in Bool (`TermsInSort`). -/
theorem f_true_of_item (H : HookParams) (F : HoldsShape.NodeFacts (cH H) I) (hTS : Faithful.TermsInSort (cH H) I)
    (h0 : I ⊧ᴵ eqnPat ws rG (clauseQC (cH H) tblG (vsH H) Srt.bool prem (xLit true)) BoolP Ff
      (sAnd (altPC (cH H) tblG (vsH H) (xLit true)) (sTop BoolP)))
    (hg : I ⊧ᴵ (trS U.ax134).pat)
    (hnot : I ⊧ᴵ (TiePair.app (cH H) boolNot [bool true] ≡ den (cH H) (bool false))) :
    I ⊧ᴵ (TiePair.app (cH H) Fs [bool true] ≡ den (cH H) (bool false)) := by
  obtain ⟨β, hS, hσ, X⟩ := facts H F hTS
  obtain ⟨-, -, hr, hBP, -, -⟩ := lit_facts
  obtain ⟨hkR, hkX0, hkXV, hx0r, hxVr, hws, hprem, hFf, hg134, htop⟩ := val_facts
  have hD := F.defOK
  have appF : TiePair.app (cH H) Fs [bool true] = sym (.symbol "Lblf") ⬝ den (cH H) (bool true) := congrFun appF_fun H
  have appNot : TiePair.app (cH H) boolNot [bool true] = sym (.symbol "LblnotBool'Unds'") ⬝ den (cH H) (bool true) :=
    congrFun appNot_fun H
  have altG : altPC (cH H) tblG (vsH H) (xLit true) = sym (.symbol "Lblg") ⬝ den (cH H) (bool true) :=
    congrFun altG_fun H
  have condT : tr ⟨tblG, []⟩ (Cond.kore (cH H) (vsH H) R (.equals Srt.bool (litT true) (.var 0))) =
      sEquals BoolP (.evar rG) (den (cH H) (bool true)) (.evar xV) := congrFun condT_fun H
  have termF : tr ⟨tblG, []⟩ (Term.kore (cH H) (Faithful.canonVars (cH H) []) (.app Fs [litT true])) =
      sym (.symbol "Lblf") ⬝ den (cH H) (bool true) := congrFun termF_fun H
  have sortF : sortOfTerm ((cH H).rhsCtx ((cH H).fns.map Fn.sig)) [] (.app Fs [litT true]) = some Srt.bool :=
    congrFun sortF_fun H
  intro e m
  rw [interp_equal hD]
  obtain ⟨t, ht, htB⟩ := bool_lit F true e
  obtain ⟨fl, hfl, hflB⟩ := bool_lit F false e
  have hinB : ∀ (e : Valuation M) a, (inhOf BoolP).interpret I e a ↔ Inh I β a := fun e a => interp_inhOf_of (hS.den e)
  have htβ : Inh I β t := by rw [← hBP] at htB; exact (hinB e t).mp htB
  have hflβ : Inh I β fl := by rw [← hBP] at hflB; exact (hinB e fl).mp hflB
  have hclo : ∀ b, Closed (den (cH H) (bool b)) := fun b => by
    rw [TieFRRead.den_bool]; exact (Closed.sym _).app (Closed.sym _)
  have htA : ∀ (e2 : Valuation M) a, (den (cH H) (bool true)).interpret I e2 a ↔ a = t := fun e2 a => by
    rw [(hclo true).interp e2 e a]; exact ht a
  have hfA : ∀ (e2 : Valuation M) a, (den (cH H) (bool false)).interpret I e2 a ↔ a = fl := fun e2 a => by
    rw [(hclo false).interp e2 e a]; exact hfl a
  -- an application of a symbol at a pattern whose one element is t
  have happ : ∀ (s : KoreAML.Sym) (ψ : P) (e2 : Valuation M), (∀ a, ψ.interpret I e2 a ↔ a = t) → ∀ m,
      ((sym s ⬝ ψ : P).interpret I e2 m ↔ ∃ a, I.evalSymb s a ∧ I.evalApp a t m) := by
    intro s ψ e2 hψ m
    rw [interp_app]
    constructor
    · rintro ⟨a, b, ha, hb, hab⟩
      rw [(hψ b).mp hb] at hab
      exact ⟨a, ha, hab⟩
    · rintro ⟨a, ha, hab⟩
      exact ⟨a, t, ha, (hψ t).mpr rfl, hab⟩
  -- the valuation: R is Bool, every element variable the element of `true`
  let e' : Valuation M := ⟨fun x => if x = rG then β else t, e.evalSvar⟩
  have er : e'.evalEvar rG = β := by
    show (if rG = rG then β else t) = β
    simp
  have ex0 : e'.evalEvar x0 = t := by
    show (if x0 = rG then β else t) = t
    simp [hx0r]
  have exV : e'.evalEvar xV = t := by
    show (if xV = rG then β else t) = t
    simp [hxVr]
  have hat : At I ws rG e' t := by
    refine ⟨fun w hw => ?_, by rw [er]; exact htβ⟩
    rw [hws] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · rw [interp_guard_sortVar hD, hkR, er]; exact hS.isSort
    · rw [interp_guard_evar hD, hkX0, ex0]; exact (hinB e' t).mpr htβ
    · rw [interp_guard_evar hD, hkXV, exV]; exact (hinB e' t).mpr htβ
  have hSr : ∀ a, (Pattern.evar rG : P).interpret I e' a ↔ a = β := fun a => by rw [interp_evar, er]
  have hTop : (sTop (.evar rG) : P).interpret I e' t :=
    (interp_sTop hD htop t).mpr ((interp_inhOf_of hSr).mpr htβ)
  have hIn : (sIn BoolP (.evar rG) (.evar x0) (.evar xV)).interpret I e' t :=
    (interp_sIn hD F.ceilDef (hS.den e') hSr hS.isSort hS.isSort
      (fun a ha => by rw [interp_evar.mp ha, ex0]; exact htβ) t).mpr
      ⟨⟨t, by rw [interp_evar, ex0], by rw [interp_evar, exV]⟩, htβ⟩
  have hpr : prem.interpret I e' t := by
    rw [hprem]; exact interp_sAnd.mpr ⟨hTop, interp_sAnd.mpr ⟨hIn, hTop⟩⟩
  -- `notBool(true)` is the element of `false`
  have hN : ∀ a, (∃ h, I.evalSymb (.symbol "LblnotBool'Unds'") h ∧ I.evalApp h t a) ↔ a = fl := by
    intro a
    have h := (interp_equal hD).mp (hnot e m) a
    rw [appNot, happ (.symbol "LblnotBool'Unds'") (den (cH H) (bool true)) e (htA e) a] at h
    exact h.trans (hfA e a)
  -- `g(true)` is `notBool(true)` on Bool
  rw [hg134] at hg
  have hG1 := eqnPat_at hD F.ceilDef hS.den hS.isSort hr hg hat hpr
  have hGβ : ∀ a, Inh I β a → ((∃ h, I.evalSymb (.symbol "Lblg") h ∧ I.evalApp h t a) ↔ a = fl) := by
    intro a ha
    have h1 := hG1 a ha
    rw [happ (.symbol "Lblg") (.evar x0) e' (fun a => by rw [interp_evar, ex0]) a, andTop_on hD hS ha,
      happ (.symbol "LblnotBool'Unds'") (.evar xV) e' (fun a => by rw [interp_evar, exV]) a] at h1
    exact h1.trans (hN a)
  have hx : xLit true ∈ xsOfB (xLit true) (xLit false) true ++ xsOfB (xLit true) (xLit false) false :=
    List.mem_cons_self ..
  have hAlt : ∀ a, (altPC (cH H) tblG (vsH H) (xLit true)).interpret I e' a ↔
      ∃ h, I.evalSymb (.symbol "Lblg") h ∧ I.evalApp h t a := fun a => by
    rw [altG]; exact happ _ _ e' (htA e') a
  -- the clause's premise at X := the element of `true`
  have hCG : altGC (CGof I (cH H) tblG (vsH H)) (xLit true) e' := by
    intro p hp
    have hp' : p = .equals Srt.bool (litT true) (.var 0) := by simpa [xLit] using hp
    subst hp'
    intro m' hm'
    have hm'' : Inh I β m' := by rw [← er]; exact hm'
    rw [condT, interp_sEquals hD F.ceilDef (hS.den e') hSr hS.isSort hS.isSort]
    exact ⟨hm'', fun a _ => by rw [htA e' a, interp_evar, exV]⟩
  have hq : (clauseQC (cH H) tblG (vsH H) Srt.bool prem (xLit true)).interpret I e' t :=
    (clauseQC_iff F hr hσ hS.isSort hat (X.hin e' t hat _ hx) (X.hcond e' t hat _ hx)).mpr
      ⟨hpr, ⟨fl, (hAlt fl).mpr ((hGβ fl hflβ).mpr rfl)⟩, hCG⟩
  have hF1 := eqnPat_at hD F.ceilDef hS.den hS.isSort hr h0 hat hq
  have hFβ : ∀ a, Inh I β a → ((∃ h, I.evalSymb (.symbol "Lblf") h ∧ I.evalApp h t a) ↔ a = fl) := by
    intro a ha
    have h1 := hF1 a ha
    rw [hFf, happ (.symbol "Lblf") (.evar x0) e' (fun a => by rw [interp_evar, ex0]) a, andTop_on hD hS ha,
      hAlt a] at h1
    exact h1.trans (hGβ a ha)
  intro a
  rw [appF, happ (.symbol "Lblf") (den (cH H) (bool true)) e (htA e) a, hfA e a]
  constructor
  · intro h
    have hin := hTS (vars := []) (tbl := tblG) (e := e) (t := .app Fs [litT true]) (s := Srt.bool) sortF
      Faithful.bool_numbered (fun i hi => by simp [varOccs, varOccsList, litT] at hi) a
      (by rw [termF]; exact (happ (.symbol "Lblf") (den (cH H) (bool true)) e (htA e) a).mpr h)
    have haβ : Inh I β a := (interp_inhOf_of (hσ e)).mp ((HoldsShape.inhOf_srtOf_inS (tbl := tblG) (e := e)).mpr hin)
    exact (hFβ a haβ).mp h
  · intro h
    rw [h]
    exact (hFβ fl hflβ).mpr rfl

/-- **`f(true) = false` from the sentences 133, 62 and 134**, in an interpretation with
`NodeFacts` and `TermsInSort` where `notBool(true)` is `false`. -/
theorem f_true_from_text_nodeFacts (H : HookParams) (F : HoldsShape.NodeFacts (cH H) I) (hTS : Faithful.TermsInSort (cH H) I)
    (hT : I ⊧ᴵ (trS U.ax133).pat) (hF : I ⊧ᴵ (trS U.ax62).pat) (hg : I ⊧ᴵ (trS U.ax134).pat)
    (hnot : I ⊧ᴵ (TiePair.app (cH H) boolNot [bool true] ≡ den (cH H) (bool false))) :
    I ⊧ᴵ (TiePair.app (cH H) Fs [bool true] ≡ den (cH H) (bool false)) := by
  have hg' : gShape (cH H) = spItems := congrFun gamma_shape_fun H
  have h0 := sp_from_text_nodeFacts H F hTS hT hF
  rw [← hg'] at h0
  exact f_true_of_item H F hTS (h0 _ (List.mem_cons_self ..)) hg hnot

end

/-- Γ's item of g's equation is sentence 134 as written. -/
theorem g_at : (TiePair.gammaPats c)[3]? = some (trS U.ax134).pat := by decide +kernel

theorem g_entailed (H : HookParams) {M : Type} {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Faithful.Γ (cH H)) :
    I ⊧ᴵ (trS U.ax134).pat := by
  have hm : (trS U.ax134).pat ∈ TiePair.gammaPats c := List.mem_of_getElem? g_at
  unfold TiePair.gammaPats at hm
  obtain ⟨it, hit, he⟩ := List.mem_map.mp hm
  rw [← he]
  exact hI _ (TiePair.mem_Γ_fns (Or.inl ⟨it, by rw [TiePair.fnItems_withHooks]; exact hit, rfl⟩))

theorem notSig_mem : (⟨boolNot, [Srt.bool], Srt.bool⟩ : CtorSig) ∈ hookSigs := by decide +kernel
theorem sortsTrue_fun : (fun Hk : HookParams => (c.withHooks Hk).sortsOf [bool true]) = fun _ => some [Srt.bool] := by
  kernel_rfl
theorem sortsTrue (H : HookParams) : (cH H).sortsOf [bool true] = some [Srt.bool] := congrFun sortsTrue_fun H
theorem hookNotH (H : HookParams) : (cH H).hookRes boolNot [bool true] = some (some (bool false)) :=
  Semantics.hookRes_of_value (by decide +kernel)

set_option maxHeartbeats 1000000 in
/-- **`f(true) = false` in every model of `Γc`, for every H.** -/
theorem f_true_c (H : HookParams) : Faithful.Γc (cH H) ⊧ (TiePair.app (cH H) Fs [bool true] ≡ den (cH H) (bool false)) := by
  intro M _ I hIc
  have hI : I ⊧ᴵP Faithful.Γ (cH H) := fun φ hφ => hIc φ (Or.inl hφ)
  have F := HoldsShape.nodeFacts_of_core (coreOKH H) hIc
  have hTS : Faithful.TermsInSort (cH H) I := Faithful.termsInSort_of_core (coreOKH H) hI
  have hg' : gShape (cH H) = spItems := congrFun gamma_shape_fun H
  have hs : ∀ φ ∈ gShape (cH H), I ⊧ᴵ φ := by rw [hg']; exact spItems_sat H hI
  have hnot := Faithful.sat_hookRes (k := ⟨boolNot, [Srt.bool], Srt.bool⟩) (vs := [bool true])
    (r := some (bool false)) hI notSig_mem (sortsTrue H) (hookNotH H)
  have h0 : I ⊧ᴵ eqnPat ws rG (clauseQC (cH H) tblG (vsH H) Srt.bool prem (xLit true)) BoolP Ff
      (sAnd (altPC (cH H) tblG (vsH H) (xLit true)) (sTop BoolP)) := hs _ (List.mem_cons_self ..)
  exact f_true_of_item H F hTS h0 (g_entailed H hI) hnot

end KCore.TieE3EqExistsMlUnderApp133

#check @KCore.TieE3EqExistsMlUnderApp133.read
#check @KCore.TieE3EqExistsMlUnderApp133.text_shape
#check @KCore.TieE3EqExistsMlUnderApp133.hoist_ok
#check @KCore.TieE3EqExistsMlUnderApp133.exReadB_fun
#check @KCore.TieE3EqExistsMlUnderApp133.gamma_shape_fun
#check @KCore.TieE3EqExistsMlUnderApp133.facts
#check @KCore.TieE3EqExistsMlUnderApp133.sp_from_text_nodeFacts
#check @KCore.TieE3EqExistsMlUnderApp133.sp_entailed
#check @KCore.TieE3EqExistsMlUnderApp133.f_true_of_item
#check @KCore.TieE3EqExistsMlUnderApp133.f_true_from_text_nodeFacts
#check @KCore.TieE3EqExistsMlUnderApp133.f_true_c
/-- info: 'KCore.TieE3EqExistsMlUnderApp133.sp_from_text_nodeFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieE3EqExistsMlUnderApp133.sp_from_text_nodeFacts
/-- info: 'KCore.TieE3EqExistsMlUnderApp133.sp_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieE3EqExistsMlUnderApp133.sp_entailed
/-- info: 'KCore.TieE3EqExistsMlUnderApp133.f_true_from_text_nodeFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieE3EqExistsMlUnderApp133.f_true_from_text_nodeFacts
/-- info: 'KCore.TieE3EqExistsMlUnderApp133.f_true_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieE3EqExistsMlUnderApp133.f_true_c
#check @KCore.TieE3EqExistsMlUnderApp133.lit_idx
#check @KCore.TieE3EqExistsMlUnderApp133.lit_sents
#check @KCore.TieE3EqExistsMlUnderApp133.kNonempty_text
#check @KCore.TieE3EqExistsMlUnderApp133.lit_of_text
#check @KCore.TieE3EqExistsMlUnderApp133.sp_from_text_sig
/-- info: 'KCore.TieE3EqExistsMlUnderApp133.sp_from_text_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieE3EqExistsMlUnderApp133.sp_from_text_sig
