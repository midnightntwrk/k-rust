/-
  The tie of an equation with `\or` on its right side that has a competitor: a literal text where
  h has the equation `rule h(0) => 0` and the `[owise]` equation `rule h(X) => f(X) #Or g(X)`, with
  h `total`. The `[owise]` sentence's premise is `¬ ⋁ competitors ∧ ⌈⊤⌉ ∧ X0 ∈ VarX`, the
  competitor h(0)'s argument conjunction `X0 ∈ 0`; the clauses `Parse.frRead` reads of it are
  `frClauses … 200 …`, each of which h(0)'s clause (of priority 50) competes with
  (`lowerClauses`). Run from the package root: `lake env lean -j1 test/TieFRCompete.lean`.

  - `axT`, `ax216`: the `[owise]` sentence and h's functional sentence, written with the builders of
    Kore/Build.lean in the shape `competingPremise` describes for an `[owise]` equation (the
    text is a literal, not a kompiled fixture).
  - `gamma_shapeC`: `Γ`'s items for the clauses of the split, from `TieFRGamma.gamma_shapeFG`, the
    frame (`frame_facts`) being the competitors' negation `nT` before the premise `prem`, over the
    table `tblG` and the text's guards; each item's premise is `nT ∧ clauseQ …` or
    `nT ∧ lastQ …`. `gamma_splitC`: `Γ`'s items for h are h(0)'s and those
    (`TieFRGamma.fnEquationsK_splitFG`).
  - `readingsC`: the readings of the general lemmas (`readings_of_frT`) for `prem`, under the
    competitors' negation by `readings_compete`, so that they read the text's premise `nT ∧ prem`
    and `Γ`'s premises.
  - `text_of_gammaC`: `Γ`'s items for h give the sentence; `gamma_of_textC`: the sentence with h's
    functional sentence gives each of the items of the split. In a model with `NodeFacts c I` and
    `TermsInSort c I`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.TieFRCompeteTest

open ML KoreAML KoreAML.TieFR KCore.TieFRRead KCore.TieFRGamma
open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

/-! ## The semantics: h with h(0)'s clause and the clauses of the split -/

def F : Sym := nRegSyms + 4
def G : Sym := nRegSyms + 5
def H : Sym := nRegSyms + 6
def fX : Term := .app F [.var 0]
def gX : Term := .app G [.var 0]

def fFn : Fn := ⟨F, [Srt.int], Srt.int, [⟨[Srt.int], [.var 0], none, .var 0, none, 50, false, [], .top, .top⟩], true⟩
def gFn : Fn := ⟨G, [Srt.int], Srt.int,
  [⟨[Srt.int], [.var 0], none, .app intSub [.dv Srt.int (.int 0), .var 0], none, 50, false, [], .top, .top⟩], true⟩

/-- `h(0) => 0`, of priority 50. -/
def h0 : Clause := ⟨[], [.dv Srt.int (.int 0)], none, .dv Srt.int (.int 0), none, 50, false, [], .top, .top⟩

/-- The alternatives `frRead` gives `frClauses`: `f(X)` and `g(X)` with no condition. -/
def xsC : List (Term × List Term) := [(fX, []), (gX, [])]

/-- The clauses of the split of the `[owise]` equation, of priority 200. -/
def cls : List Clause := Parse.frClauses Srt.int [Srt.int] [.var 0] none 200 false (frAltsOf xsC)

/-- h, declared `total`, with h(0)'s clause and the clauses of the split. -/
def hFn : Fn := ⟨H, [Srt.int], Srt.int, h0 :: cls, true⟩

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf", "Lblg", "Lblh"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [fFn, gFn, hFn]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

/-- h(0)'s clause competes with each clause of the split. -/
theorem lower_facts : lowerAtFG hFn 200 = [h0] ∧ ∀ cl ∈ cls, Faithful.lowerClauses hFn cl = [h0] := by
  have hp : ∀ cl ∈ cls, cl.prio = 200 := by decide
  refine ⟨rfl, fun cl hcl => ?_⟩
  rw [lowerClauses_eqFG, hp cl hcl]
  rfl

/-! ## The text's two sentences -/

def iS : Kore.KSort := srt "Int"
def fK : Kore.Pattern := ap "Lblf" [ev "VarX" iS]
def gK : Kore.Pattern := ap "Lblg" [ev "VarX" iS]
def pT : Kore.Pattern := .or iS [fK, gK]
def enT : Kore.Pattern := .top iS

/-- The competitors' negation: h(0)'s argument conjunction `⌈⊤⌉ ∧ X0 ∈ 0`, negated. -/
def notK : Kore.Pattern :=
  .not R (.or R [.and R [.top R, .and R [.in iS R (ev "X0" iS) (.dv iS "0"), .top R]], .bottom R])
/-- The equation's own premise: `⌈⊤⌉ ∧ X0 ∈ VarX`. -/
def premK : Kore.Pattern := .and R [.top R, .and R [.in iS R (ev "X0" iS) (ev "VarX" iS), .top R]]

/-- The `[owise]` sentence: `¬ ⋁ competitors ∧ X0 ∈ VarX → h(X0) = (f(VarX) ∨ g(VarX)) ∧ ⊤`. -/
def axT : Kore.Axiom :=
  { sortVars := [Rv]
    pattern := .implies R (.and R [notK, premK]) (.equals iS R (ap "Lblh" [ev "X0" iS]) (.and iS [pT, enT]))
    attributes := [attr "owise"] }

/-- h's functional sentence: `∃Val. Val = h(K0)`. -/
def ax216 : Kore.Axiom :=
  { sortVars := [Rv]
    pattern := .exist R (evar "Val" iS) (.equals iS R (.var (.evar (evar "Val" iS))) (ap "Lblh" [ev "K0" iS]))
    attributes := [attr "functional"] }

theorem ax216_eq : ax216 = Faithful.Model.functionalAxiom c hFn := by decide +kernel

def textItem : Item := trAxiom [] [] ⟨2, "E3-ML-EQ-RHS-OR-OWISE", axT⟩
def fnlItem : Item := Faithful.Model.functionalItem c hFn

/-- The names of the text: f, g, h are the symbols `nRegSyms + 4` to `nRegSyms + 6`, of result
sort Int; h has its `functional` sentence. -/
def NT : Parse.Names :=
  { sorts := ["KCell", "KCellOpt"]
    syms := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf", "Lblg", "Lblh"]
    keyFns := [(nRegSyms + 4, "Int"), (nRegSyms + 5, "Int"), (nRegSyms + 6, "Int")]
    fnlSyms := [("Lblh", false)] }

/-- The `[owise]` equation as the reader takes it, with its competitor. -/
def eqT : Parse.RawEqn :=
  ⟨"Lblh", [ev "VarX" iS], none, some [.and R [.top R, .and R [.in iS R (ev "X0" iS) (.dv iS "0"), .top R]]],
    pT, [attr "owise"], none, false⟩

/-- **The reader reads the equation** as the clauses of the split, of priority 200 (kernel). -/
theorem frRead_eqT : Parse.frRead NT eqT = .ok (some (cls, [⟨"X", "Int"⟩])) := by
  kernel_rfl

/-! ## The shapes -/

def tbl : VarTable := tableOf axT.sortVars axT.pattern
def ctx : Ctx := ⟨tbl, []⟩
def ws : List P := guardsOf axT
def r : EVar := tbl.ev (sortVarKey Rv)
def nT : P := tr ctx notK
def prem : P := tr ctx premK
def IntP : P := trSort tbl iS
def Fh : P := tr ctx (ap "Lblh" [ev "X0" iS])
def rhsT : P := sAnd (tr ctx pT) (tr ctx enT)
def x0 : EVar := tbl.ev (evarKey (evar "X0" iS))
def xv : EVar := tbl.ev (evarKey (evar "VarX" iS))

theorem text_shape : textItem.pat = eqnPat ws r (sAnd nT prem) IntP Fh rhsT := by
  rw [show sAnd nT prem = tr ctx (.and R [notK, premK]) from (Faithful.tr_and2 _ _ _).symm]
  exact trAxiom_eqnPat [] [] _ _ axT rfl rfl

/-- The clauses' variables and the table of `Γ`'s items for the split. -/
def vsC : List KoreAML.Var := Faithful.canonVars c [Srt.int]
def tblG : VarTable := [.sortVar "R", .evar "X0" (srt "Int"), .evar "VarV0" (srt "Int")]

/-- The last clause's right side `f(X) ∧ (false = true)`. -/
def BNG : P := sAnd (altP c tblG vsC (fX, []))
  (tr ⟨tblG, []⟩ (reqPat (srtOf c Srt.int) (some (Term.kore c vsC (Parse.boolT false)))))

/-- The frame of the split's items is the text's: its table `tblG`, the text's guards, `R`, the
competitors' negation, the premise and the left side (kernel). -/
theorem frame_facts : tblFG c hFn [h0] [Srt.int] [.var 0] none = tblG ∧ wsFG c hFn [h0] [Srt.int] [.var 0] none = ws ∧
    tblG.ev (sortVarKey Rv) = r ∧ tr ⟨tblG, []⟩ (compNotFG c hFn [h0]) = nT ∧
    tr ⟨tblG, []⟩ (premFG c hFn [Srt.int] [.var 0] none) = prem ∧ trSort tblG (srtOf c hFn.result) = IntP ∧
    tr ⟨tblG, []⟩ (headFG c hFn) = Fh := by
  decide +kernel

/-- **`Γ`'s items for the split**, each premise under the competitors' negation `nT`. -/
theorem gamma_shapeC : (Faithful.kernelItems (cls.map (Faithful.prioEquation c hFn))).map (·.pat) =
    [eqnPat ws r (sAnd nT (clauseQ c tblG vsC Srt.int prem (fX, []))) IntP Fh
       (sAnd (altP c tblG vsC (fX, [])) (sTop IntP)),
     eqnPat ws r (sAnd nT (clauseQ c tblG vsC Srt.int prem (gX, []))) IntP Fh
       (sAnd (altP c tblG vsC (gX, [])) (sTop IntP)),
     eqnPat ws r (sAnd nT (lastQ c tblG vsC Srt.int prem xsC)) IntP Fh BNG] := by
  obtain ⟨ht, hw, hr, hn, hp, hS, hF⟩ := frame_facts
  have h := gamma_shapeFG c hFn (s := Srt.int) (vars := [Srt.int]) (pats := [.var 0]) (req := none)
    (prio := 200) (aside := false) (xs := xsC) (by decide) rfl (by decide)
  simp only [lower_facts.1, ht, hw, hr, hn, hp, hS, hF, withCompFG_ne (L := [h0]) (by simp)] at h
  exact h

/-- **`Γ`'s items for h**: h(0)'s, then those of the split. -/
theorem gamma_splitC : (Faithful.kernelItems (Faithful.fnEquationsK c hFn)).map (·.pat) =
    (Faithful.kernelItems [Faithful.prioEquation c hFn h0]).map (·.pat) ++
      (Faithful.kernelItems (cls.map (Faithful.prioEquation c hFn))).map (·.pat) := by
  rw [fnEquationsK_splitFG c hFn (before := [h0]) (cls := cls) (after := []) rfl]
  rfl

/-- The functional sentence: `∃v. v = h(K0)`, K0 the variable `k0`. -/
def tblF : VarTable := tableOf ax216.sortVars ax216.pattern
def rF : EVar := tblF.ev (sortVarKey Rv)
def vF : EVar := tblF.ev (evarKey (evar "Val" iS))
def k0 : EVar := tblF.ev (evarKey (evar "K0" iS))
def hHead : P := sym (.symbol "Lblh")
def tsF : List (EVar × EVar × P) := [(x0, k0, IntP)]

theorem fnl_shape : fnlItem.pat =
    fnlPat (sortGuard rF :: tsF.map fun t => (t.2.1 ∈∈ inhOf t.2.2)) rF vF IntP
      (appList hHead (tsF.map fun t => .evar t.2.1)) := by
  show (trAxiom [] [] ⟨0, "kernel", Faithful.Model.functionalAxiom c hFn⟩).pat = _
  rw [← ax216_eq, trAxiom_fnlPat [] [] 0 "kernel" ax216 (F := ap "Lblh" [ev "K0" iS]) (v := evar "Val" iS) rfl rfl]
  decide +kernel

/-- The facts of the indices `one_of_fnl` reads, and of the guards. -/
theorem idx_facts :
    Fh = appList hHead (tsF.map fun t => .evar t.1) ∧ (tsF.map (·.2.1)).Nodup ∧ rF ∉ tsF.map (·.2.1) ∧
      vF ∉ tsF.map (·.2.1) ∧ vF ≠ rF ∧ sortGuard r ∈ ws ∧ (x0 ∈∈ inhOf IntP) ∈ ws ∧
      (xv ∈∈ inhOf IntP) ∈ ws ∧ IntP = sym (.sort "SortInt") := by
  decide +kernel

/-- The facts of the literals the general lemmas read: the tables agree on R and on the
variable, the text's alternatives translate as `Γ`'s, the sorts and variables of the terms. -/
theorem lit_facts :
    tblG.ev (sortVarKey Rv) = r ∧ trSort tblG (srtOf c Srt.int) = IntP ∧
    tr ⟨tbl, []⟩ fK = altP c tblG vsC (fX, []) ∧ tr ⟨tbl, []⟩ gK = altP c tblG vsC (gX, []) ∧
    tblG.ev (Faithful.canonKey c [Srt.int] 0) = xv ∧ c.sortName Srt.int = "Int" ∧
    sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) [Srt.int] fX = some Srt.int ∧
    sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) [Srt.int] gX = some Srt.int ∧ varOccs fX = [0] ∧ varOccs gX = [0] := by
  decide +kernel

/-- The alternatives translate as the kept ones, with no condition (`altsTrOK`, kernel). -/
theorem tr_facts : altsTrOK c tblG vsC tbl (frConds eqT.rhs) [] (keptAlts (frSide eqT.rhs)) xsC = true := by
  decide +kernel

/-! ## In a model -/

section GeneralModel
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The readings of the general lemmas, under the competitors' negation (`readings_compete`), in a
model with `NodeFacts c I` and `TermsInSort c I`. -/
theorem readingsC (F : HoldsShape.NodeFacts c I) (hTS : Faithful.TermsInSort c I) :
    ∃ σI, SortAt I IntP σI ∧ (∀ (e : Valuation M) a, (trSort tblG (srtOf c Srt.int)).interpret I e a ↔ a = σI) ∧
      Readings I ws r σI (sAnd nT prem) rhsT xsC (altP c tblG vsC) (altG I c tblG vsC)
        (fun x => sAnd nT (clauseQ c tblG vsC Srt.int prem x)) (sAnd nT (lastQ c tblG vsC Srt.int prem xsC)) := by
  obtain ⟨hr0, hS0, hA1, hA2, hk0, hn0, hty1, hty2, hv1, hv2⟩ := lit_facts
  obtain ⟨-, -, -, -, -, hr, -, hxv, hIntP⟩ := idx_facts
  obtain ⟨σI, hσS, hσ⟩ := F.sort (s := Srt.int) (by decide)
  have hσ' : ∀ (e : Valuation M) a, (trSort tblG (srtOf c Srt.int)).interpret I e a ↔ a = σI := fun e a => hσ tblG e a
  have hSA : SortAt I IntP σI := ⟨fun e a => by rw [← hS0]; exact hσ' e a, hσS, by rw [hIntP]; rfl⟩
  have hD := F.defOK
  -- the alternatives lie in Int
  have hin : ∀ e m, At I ws r e m → ∀ x ∈ xsC, ∀ a, (altP c tblG vsC x).interpret I e a → Inh I σI a := by
    refine inSort_of_terms hTS (vars := [Srt.int]) (by decide) hσ' ?_ ?_
    · intro x hx
      simp only [xsC, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hty1
      · exact hty2
    · intro e m hat x hx i hi
      have hi0 : i = 0 := by
        simp only [xsC, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · rw [hv1] at hi; simpa using hi
        · rw [hv2] at hi; simpa using hi
      subst hi0
      have := hat.1 _ hxv
      rw [interp_member hD] at this
      rw [List.getD_cons_zero, hn0, hk0, ← Faithful.inS_iff e]
      rw [hIntP] at this
      exact this
  -- the right side's operands, the two alternatives, lie in Int
  have hT : ∀ e m, At I ws r e m → TightSem I tbl e pT := by
    intro e m hat
    refine ⟨fun q hq a ha => ?_, ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    have hIn : Inh I σI a := by
      rcases hq with rfl | rfl
      · rw [hA1] at ha; exact hin e m hat _ (List.mem_cons_self ..) a ha
      · rw [hA2] at ha; exact hin e m hat _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) a ha
    show (inhOf IntP).interpret I e a
    rw [interp_inhOf_of (hSA.den e)]
    exact hIn
  have hr' : sortGuard (tblG.ev (sortVarKey Rv)) ∈ ws := by rw [hr0]; exact hr
  have R := readings_of_frT F (al := []) (prem := prem) frRead_eqT (by decide) (by decide) hr' hσ' hσS
    (by rw [hr0]; exact hin) (by rw [hr0]; exact hT) (en := enT) rfl (fun e a => hSA.den e a) tr_facts
  rw [hr0] at R
  exact ⟨σI, hSA, hσ', readings_compete (n := nT) R⟩

/-- **`Γ`'s items for h give the `[owise]` sentence**, from `NodeFacts c I` and `TermsInSort c I`,
the last clause's right side empty because `false` and `true` are two elements of Bool. -/
theorem text_of_gammaC (F : HoldsShape.NodeFacts c I) (hTS : Faithful.TermsInSort c I)
    (h : ∀ it ∈ Faithful.kernelItems (Faithful.fnEquationsK c hFn), I ⊧ᴵ it.pat) : I ⊧ᴵ textItem.pat := by
  have hs : ∀ φ ∈ (Faithful.kernelItems (cls.map (Faithful.prioEquation c hFn))).map (·.pat), I ⊧ᴵ φ := by
    intro φ hφ
    have hφ' : φ ∈ (Faithful.kernelItems (Faithful.fnEquationsK c hFn)).map (·.pat) := by
      rw [gamma_splitC]; exact List.mem_append_right _ hφ
    obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hφ'
    exact h it hit
  rw [gamma_shapeC] at hs
  rw [text_shape]
  obtain ⟨σI, hSA, hσ', R⟩ := readingsC F hTS
  obtain ⟨-, -, -, -, -, hr, -, -, -⟩ := idx_facts
  refine text_of_split (BN := BNG) F.defOK F.ceilDef hSA hr (guardsOf_pred F.defOK axT) R
    (fun x hx => ?_) (hs _ (by simp)) (noneEmpty_of_apart F hσ' hSA.isSort)
  simp only [xsC, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact hs _ (by simp)
  · exact hs _ (by simp)

/-- **The `[owise]` sentence with h's functional sentence gives each of `Γ`'s items for the
split**, from `NodeFacts c I` and `TermsInSort c I`. -/
theorem gamma_of_textC (F : HoldsShape.NodeFacts c I) (hTS : Faithful.TermsInSort c I)
    (hT : I ⊧ᴵ textItem.pat) (hF : I ⊧ᴵ fnlItem.pat) :
    ∀ it ∈ Faithful.kernelItems (cls.map (Faithful.prioEquation c hFn)), I ⊧ᴵ it.pat := by
  intro it hit
  have hmem : it.pat ∈ (Faithful.kernelItems (cls.map (Faithful.prioEquation c hFn))).map (·.pat) :=
    List.mem_map.mpr ⟨it, hit, rfl⟩
  rw [gamma_shapeC] at hmem
  rw [text_shape] at hT
  rw [fnl_shape] at hF
  obtain ⟨σI, hSA, -, R⟩ := readingsC F hTS
  obtain ⟨hFh, hnd, hrk, hvk, hvr, hr, hx0, -, hIntP⟩ := idx_facts
  have hG := guardsOf_pred F.defOK axT
  have hone : ∀ e m, At I ws r e m → ∃ y, Inh I σI y ∧ ∀ a, Inh I σI a → (Fh.interpret I e a ↔ a = y) := by
    intro e m hat
    rw [hFh]
    exact one_of_fnl F.defOK F.ceilDef hSA.den hSA.isSort hr hF (Closed.sym _) hnd hrk hvk hvr rfl
      (fun t ht => by
        simp only [tsF, List.mem_singleton] at ht
        subst ht
        exact ⟨hx0, by rw [hIntP]; exact Closed.sym _⟩) hat
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h <;> rw [h]
  · exact clause_of_text F.defOK F.ceilDef hSA hr hG R hT hone (List.mem_cons_self ..)
  · exact clause_of_text F.defOK F.ceilDef hSA hr hG R hT hone (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · exact none_of_text F.defOK F.ceilDef hSA hr hG R hT hone BNG

end GeneralModel

end KCore.TieFRCompeteTest

#check @KCore.TieFRCompeteTest.gamma_of_textC
#check @KCore.TieFRCompeteTest.text_of_gammaC
#check @KCore.TieFRGamma.gamma_shapeFG
#check @KCore.TieFRGamma.fnEquationsK_splitFG
#check @KCore.TieFRGamma.readings_withCompFG
/-- info: 'KCore.TieFRCompeteTest.gamma_of_textC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieFRCompeteTest.gamma_of_textC
/-- info: 'KCore.TieFRCompeteTest.text_of_gammaC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieFRCompeteTest.text_of_gammaC
/-- info: 'KCore.TieFRGamma.gamma_shapeFG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieFRGamma.gamma_shapeFG
