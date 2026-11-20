/-
  The equation with `\exists` over one Bool variable on its right side, on the kompiled text of
  fixture `e3-eq-exists-bool-ml` (`f2-examples/e3-eq-exists-bool-ml.kompile.kore`, the text
  `test/constructs/fixtures/e3-eq-exists-bool-ml/kompile.txt` records): sentence 132,
  `rule f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})` with f `total`, and f's functional
  sentence 62, against the three equations Γ states for f, on the literals `kore` and `defn`, for
  every interpretation H of the hooks. Indices are `AxiomDecl.index`. Run from the package root:
  `lake env lean -j1 test/TieExBoolMlText.lean`.

  The reading. `defn.sem` has one function, f, whose three clauses are `Parse.exClauses` of the
  alternatives at the literals and of the body with B a variable (`fns_eq`, kernel): at the literal
  b the term b where `b = notBool(X)`, and a last clause where no element of Bool gives the right
  side an element. Γ's items for f are items 0, 1, 2 of `fnItems` (`fnItems_split`,
  `items_length`).

  The shapes (kernel).
  - `text_shape`: the translated sentence 132 is `eqnPat` of `(∃B:Bool. body) ∧ ⊤`.
  - `fnl_shape`: the translated sentence 62 is `fnlPat` of f applied to its variable.
  - `gamma_shape`: Γ's three items are `eqnPat` over the same guards, with the premises `clauseQC`
    and `lastBQC`, for every H.
  - `exReadB_H`: the decision `TieEXReadB.exReadB` on the body, for every H. It is checked as a
    function of the hook parameters equal to the constant `true`; no part of it reads them.

  From the text to Γ's items (`sp_from_text`, `sp0_from_text`, `sp1_from_text`, `sp2_from_text`).
  Premises: sentence 132, sentence 62, and two facts of the model, `NodeFacts (cH H) I` (definedness,
  every numbered sort a sort, each value one element of its sort, distinct values apart) and
  `TermsInSort (cH H) I` (a sorted term's elements lie in its sort). No `boolClosed`. The two facts
  of the model are not sentences of the text, and no sentence states them: that a value is one
  element and that distinct values are apart are Γ's own account of the values (`ΓDomains`), and
  `TermsInSort` is shown here only of a model of Γ. So this is not "Γ's items are consequences of
  the text": the statement is "in a model with these two facts, the two sentences give the three
  items", and it names them.

  From Γ's items to the sentence. `sp_of_items`: in a model with the same two facts, Γ's three
  items and `boolClosed (cH H)` give sentence 132, with no functional sentence. `boolClosed` (every
  element of Bool is the element of `true` or of `false`) is a named premise: no sentence of the
  text states it (the text's no-junk sentence of Bool is `\or(\top, \bottom)`). It is the sentence
  of `Γcl` here, since the last clause's predicate has a binder (`gammaC_closed`). So
  `sp_entailed_closed`: a model of `Γ (cH H)` that satisfies `boolClosed (cH H)` satisfies sentence
  132; and `sp_entailed`: `Γc (cH H)` entails it. The statement is over `Γc`, not `Γ`.

  The expectation `f(true) = false` (`f_true`): entailed by `Γc (cH H)`, for every H, through Γ's
  items for f (`eval_true`: the second clause applies, `false = notBool(true)`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieExBoolMlText

open ML KoreAML KoreAML.TieFR KCore.TieEX KCore.TieEXReadB

kore_term kore from "f2-examples/e3-eq-exists-bool-ml.kompile.kore"
definition_of defn from "f2-examples/e3-eq-exists-bool-ml.kompile.kore"
user_axioms U from "f2-examples/e3-eq-exists-bool-ml.kompile.kore" module "E3-EQ-EXISTS-BOOL-ML"

noncomputable section

abbrev c : Semantics := defn.sem
abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-- The two sentences' indices in the text. -/
theorem sentence_indices : U.ax132.index = 132 ∧ U.ax62.index = 62 := ⟨rfl, rfl⟩

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-! ## The reading: f with the clauses of its split -/

def Fs : Sym := nRegSyms + 4
def litT (b : Bool) : Term := .dv Srt.bool (.bool b)
def notX : Term := .app boolNot [.var 0]
/-- The alternative of the instance at the literal b: the term b, with `b = notBool(X)`. -/
def xLit (b : Bool) : Term × List Cond := (litT b, [.equals Srt.bool (litT b) notX])
/-- The alternative of the body with B the variable at index 1: B, with `B = notBool(X)`. -/
def jB : Term × List Cond := (.var 1, [.equals Srt.bool (.var 1) notX])

/-- f, declared `total`, with the clauses of the split. -/
def fFn : Fn := ⟨Fs, [Srt.bool], Srt.bool,
  Parse.exClauses Srt.bool [Srt.bool] [.var 0] none 50 false [xLit true, xLit false] [jB], true⟩

/-- **The definition's functions are f alone, with these clauses** (kernel). -/
theorem fns_eq : c.fns = [fFn] := by kernel_rfl

theorem allFns_eq (H : HookParams) : (cH H).allFns = fFn :: (cH H).sortPreds := by
  show c.fns ++ (cH H).sortPreds = _
  rw [fns_eq]; rfl

theorem fFn_mem (H : HookParams) : fFn ∈ (cH H).allFns := by
  rw [allFns_eq H]; exact List.mem_cons_self ..

/-- Γ's items for f come first in `fnItems`. -/
theorem fnItems_split (H : HookParams) : ∃ rest, Faithful.fnItems (cH H) =
    Faithful.kernelItems (Faithful.fnEquationsK (cH H) fFn) ++ rest := by
  refine ⟨(cH H).sortPreds.flatMap fun f => Faithful.kernelItems (Faithful.fnEquationsK (cH H) f), ?_⟩
  unfold Faithful.fnItems
  rw [allFns_eq H, List.flatMap_cons]

/-! ## The text's two sentences -/

def bS : Kore.KSort := srt "Bool"
def Xp : Kore.Pattern := ev "VarX" bS
def Bp : Kore.Pattern := ev "VarB" bS
def vsF : List KoreAML.Var := [⟨"X", "Bool"⟩]
def Bv : KoreAML.Var := ⟨"B", "Bool"⟩

/-- The names the body is read with: the definition's sorts and symbols, f a function of the
definition with a `functional` sentence, Bool's literals its values. -/
def NT : Parse.Names :=
  { sorts := ["KCell", "KCellOpt"]
    syms := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf"]
    keyFns := [(nRegSyms + 4, "Bool")]
    fnlSyms := [("Lblf", false)]
    boolLits := true }

theorem names_c : NT.syms = c.symNames ∧ NT.sorts = c.sortNames := by decide +kernel

/-- The binder's body `B ∧ (B = notBool(X))`. -/
def bodyK : Kore.Pattern := .and bS [Bp, .equals bS bS Bp (ap "LblnotBool'Unds'" [Xp])]

/-- The table of sentence 132, its guards, and the table of Γ's items for f: R, the argument, the
clause's variable and the binder. -/
def tbl : VarTable := tableOf U.ax132.ax.sortVars U.ax132.ax.pattern
def ws : List P := guardsOf U.ax132.ax
def tblG : VarTable := [.sortVar "R", .evar "X0" bS, .evar "VarV0" bS, .evar "VarV1" bS]
abbrev rG : EVar := tblG.ev (sortVarKey Rv)
def prem : P := tr ⟨tbl, []⟩ (.and R [.top R, .and R [.in bS R (ev "X0" bS) Xp, .top R]])
def Ff : P := tr ⟨tbl, []⟩ (ap "Lblf" [ev "X0" bS])
def xB : EVar := tbl.ev (evarKey Bv.kore)
def bodyT : P := tr ⟨tbl, []⟩ bodyK
def ensT : P := tr ⟨tbl, []⟩ (.top bS)
def x0 : EVar := tbl.ev (evarKey (evar "X0" bS))

/-- **Sentence 132, translated as the text writes it, is the equation
`X0 ∈ X → f(X0) = (∃B:Bool. B ∧ (B = notBool(X))) ∧ ⊤`** (kernel). -/
theorem text_shape : (trS U.ax132).pat =
    eqnPat ws rG prem TieFRRead.boolP Ff (sAnd (sExists xB TieFRRead.boolP bodyT) ensT) := by decide +kernel

/-- The functional sentence 62: `∃v. v = f(K0)`. -/
def tblF : VarTable := tableOf U.ax62.ax.sortVars U.ax62.ax.pattern
def rF : EVar := tblF.ev (sortVarKey Rv)
def vF : EVar := tblF.ev (evarKey (evar "Val" bS))
def k0 : EVar := tblF.ev (evarKey (evar "K0" bS))
def fHead : P := sym (.symbol "Lblf")
def tsF : List (EVar × EVar × P) := [(x0, k0, TieFRRead.boolP)]

/-- **Sentence 62, translated as the text writes it, is f's functional sentence** (kernel). -/
theorem fnl_shape : (trS U.ax62).pat =
    fnlPat (sortGuard rF :: tsF.map fun t => (t.2.1 ∈∈ inhOf t.2.2)) rF vF TieFRRead.boolP
      (appList fHead (tsF.map fun t => .evar t.2.1)) := by decide +kernel

/-- The facts of the indices the lemmas read. -/
theorem idx_facts :
    Ff = appList fHead (tsF.map fun t => .evar t.1) ∧ (tsF.map (·.2.1)).Nodup ∧ rF ∉ tsF.map (·.2.1) ∧
      vF ∉ tsF.map (·.2.1) ∧ vF ≠ rF ∧ sortGuard rG ∈ ws ∧ (x0 ∈∈ inhOf TieFRRead.boolP) ∈ ws := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The variables read are of Bool, and the guards hold each in its sort. -/
theorem lit_facts : Parse.varSorts NT vsF = .ok [Srt.bool] ∧ TieFRVars.guardsHold ws tbl vsF = true :=
  ⟨by kernel_rfl, by decide +kernel⟩

/-! ## Γ's items for f -/

/-- The clauses' variables. -/
abbrev vsOf (C : Semantics) : List KoreAML.Var := Faithful.canonVars C [Srt.bool]

/-- The last clause's right side `true ∧ (false = true)`. -/
def BNG (C : Semantics) : P := sAnd (altPC C tblG (vsOf C) (xLit true))
  (tr ⟨tblG, []⟩ (reqPat (srtOf C Srt.bool) (some (Term.kore C (vsOf C) (Parse.boolT false)))))

/-- The three equations: of the alternative at `true`, of the alternative at `false`, and the
last, over the sentence's guards and application of f. -/
def gpats (C : Semantics) : List P :=
  [eqnPat ws rG (clauseQC C tblG (vsOf C) Srt.bool prem (xLit true)) TieFRRead.boolP Ff
     (sAnd (altPC C tblG (vsOf C) (xLit true)) (sTop TieFRRead.boolP)),
   eqnPat ws rG (clauseQC C tblG (vsOf C) Srt.bool prem (xLit false)) TieFRRead.boolP Ff
     (sAnd (altPC C tblG (vsOf C) (xLit false)) (sTop TieFRRead.boolP)),
   eqnPat ws rG (lastBQC C tblG (vsOf C) Srt.bool prem [jB]) TieFRRead.boolP Ff (BNG C)]

/-- The decisions on the semantics with any hook parameters: Γ's items for f are `gpats`, and
Bool's sort translates to Bool's pattern. -/
def shapeB (C : Semantics) : Bool :=
  decide ((Faithful.kernelItems (Faithful.fnEquationsK C fFn)).map (·.pat) = gpats C) &&
    decide (trSort tblG (srtOf C Srt.bool) = TieFRRead.boolP)

/-- (kernel) As a function of the hook parameters, the constant `true`. -/
theorem shapeB_fun : (fun Hk : HookParams => shapeB (c.withHooks Hk)) = fun _ => true := by kernel_rfl

/-- **Γ's items for f are the three equations**, for every H. -/
theorem gamma_shape (H : HookParams) :
    (Faithful.kernelItems (Faithful.fnEquationsK (cH H) fFn)).map (·.pat) = gpats (cH H) := by
  have h : shapeB (cH H) = true := congrFun shapeB_fun H
  simp only [shapeB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem boolSort_H (H : HookParams) : trSort tblG (srtOf (cH H) Srt.bool) = TieFRRead.boolP := by
  have h : shapeB (cH H) = true := congrFun shapeB_fun H
  simp only [shapeB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem items_length (H : HookParams) :
    (Faithful.kernelItems (Faithful.fnEquationsK (cH H) fFn)).length = 3 := by
  have := congrArg List.length (gamma_shape H)
  rw [List.length_map] at this
  exact this

/-- **The decision of the readings** (`TieEXReadB.exReadB`), at the semantics with any hook
parameters (kernel): the function of the hook parameters is the constant `true`. -/
theorem exReadB_fun : (fun Hk : HookParams => exReadB NT (c.withHooks Hk) tblG tbl [Srt.bool] vsF Bv Srt.bool bodyK
    (.top bS) (xLit true) (xLit false) jB) = fun _ => true := by kernel_rfl

theorem exReadB_H (H : HookParams) : exReadB NT (cH H) tblG tbl [Srt.bool] vsF Bv Srt.bool bodyK
    (.top bS) (xLit true) (xLit false) jB = true := congrFun exReadB_fun H

/-- (kernel) The definition reads a confined sort, and Bool's literals are its values, with any
hook parameters. -/
theorem closed_fun : (fun Hk : HookParams => (c.withHooks Hk).readsConfined && (c.withHooks Hk).litSort Srt.bool) =
    fun _ => true := by kernel_rfl

/-- **`boolClosed` is the sentence of `Γcl`**, for every H: the last clause's predicate has a
binder, so the definition reads a confined sort. -/
theorem gammaC_closed (H : HookParams) : Faithful.Γcl (cH H) (Faithful.boolClosed (cH H)) := by
  have h : ((cH H).readsConfined && (cH H).litSort Srt.bool) = true := congrFun closed_fun H
  rw [Bool.and_eq_true] at h
  exact ⟨h.1, h.2, rfl⟩

/-! ## In a model -/

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The readings** `TieEX`'s lemmas take, in a model with `NodeFacts` and `TermsInSort`, from the
decision. -/
theorem facts (H : HookParams) (N : HoldsShape.NodeFacts (cH H) I) (hTS : Faithful.TermsInSort (cH H) I) :
    ∃ β, IsSort I β ∧ (∀ (e : Valuation M) a, TieFRRead.boolP.interpret I e a ↔ a = β) ∧
      (∀ (e : Valuation M) a, (trSort tblG (srtOf (cH H) Srt.bool)).interpret I e a ↔ a = β) ∧
      ExFacts I (cH H) tblG (vsOf (cH H)) ws β (xsOfB (xLit true) (xLit false)) [jB] bodyT ensT xB
        (CGof I (cH H) tblG (vsOf (cH H))) (CGof I (cH H) tblG (vsBof (cH H) [Srt.bool])) := by
  obtain ⟨β, hβ, hβd⟩ := TieFRRead.boolDen_of N
  have hσ : ∀ (e : Valuation M) a, (trSort tblG (srtOf (cH H) Srt.bool)).interpret I e a ↔ a = β := fun e a => by
    rw [boolSort_H H]; exact hβd e a
  exact ⟨β, hβ, hβd, hσ, exFacts_of_exB N hTS names_c.1 names_c.2 (al := []) lit_facts.1 lit_facts.2
    idx_facts.2.2.2.2.2.1 hσ hβ rfl rfl (exReadB_H H)⟩

/-- **Sentence 132 and f's functional sentence 62 give each of Γ's three items for f**, for every
H, in a model with `NodeFacts (cH H) I` and `TermsInSort (cH H) I`. No `boolClosed`. -/
theorem sp_from_text (H : HookParams) (N : HoldsShape.NodeFacts (cH H) I) (hTS : Faithful.TermsInSort (cH H) I)
    (hT : I ⊧ᴵ (trS U.ax132).pat) (hF : I ⊧ᴵ (trS U.ax62).pat) :
    ∀ it ∈ Faithful.kernelItems (Faithful.fnEquationsK (cH H) fFn), I ⊧ᴵ it.pat := by
  intro it hit
  have hmem : it.pat ∈ gpats (cH H) := by
    rw [← gamma_shape H]; exact List.mem_map.mpr ⟨it, hit, rfl⟩
  rw [text_shape] at hT
  rw [fnl_shape] at hF
  obtain ⟨β, hβ, hd, hσ, X⟩ := facts H N hTS
  have hSA : SortAt I TieFRRead.boolP β := ⟨hd, hβ, rfl⟩
  obtain ⟨hFf, hnd, hrk, hvk, hvr, hr, hx0⟩ := idx_facts
  have hG := guardsOf_pred (I := I) N.defOK U.ax132.ax
  have hone : ∀ e m, At I ws rG e m → ∃ y, Inh I β y ∧ ∀ a, Inh I β a → (Ff.interpret I e a ↔ a = y) := by
    intro e m hat
    rw [hFf]
    exact one_of_fnl N.defOK N.ceilDef hSA.den hSA.isSort hr hF (Closed.sym _) hnd hrk hvk hvr rfl
      (fun t ht => by
        simp only [tsF, List.mem_singleton] at ht
        subst ht
        exact ⟨hx0, Closed.sym _⟩) hat
  have hcl1 := fun (x : Term × List Cond)
      (hx : x ∈ xsOfB (xLit true) (xLit false) true ++ xsOfB (xLit true) (xLit false) false) =>
    ex_clause_of_text N (tbl := tblG) (vs := vsOf (cH H)) (s := Srt.bool) (CG := CGof I (cH H) tblG (vsOf (cH H)))
      hSA hG hr hσ X.hin X.hcond X.hbody hT hone hx
  simp only [gpats, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h <;> rw [h]
  · exact hcl1 (xLit true) (List.mem_cons_self ..)
  · exact hcl1 (xLit false) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · exact ex_last_of_text N (tbl := tblG) (vs := vsOf (cH H)) (s := Srt.bool)
      (CGB := CGof I (cH H) tblG (vsBof (cH H) [Srt.bool]))
      hSA hG hr hσ X.hxr X.hinB X.hcondB X.hbodyB hT hone (BNG (cH H))

/-- An item at a position below 3 of `fnItems` is one of Γ's items for f. -/
theorem item_at (H : HookParams) {j : Nat} (hj : j < 3) {it : Item}
    (h : (Faithful.fnItems (cH H))[j]? = some it) :
    it ∈ Faithful.kernelItems (Faithful.fnEquationsK (cH H) fFn) := by
  obtain ⟨rest, hsplit⟩ := fnItems_split H
  rw [hsplit, List.getElem?_append_left (by rw [items_length H]; exact hj)] at h
  exact List.mem_of_getElem? h

/-- **Item 0 of `fnItems (cH H)`**, the equation of the alternative at `true`, from sentences 132
and 62 in a model with `NodeFacts` and `TermsInSort`. -/
theorem sp0_from_text (H : HookParams) (N : HoldsShape.NodeFacts (cH H) I) (hTS : Faithful.TermsInSort (cH H) I)
    (hT : I ⊧ᴵ (trS U.ax132).pat) (hF : I ⊧ᴵ (trS U.ax62).pat) :
    ∀ it, (Faithful.fnItems (cH H))[0]? = some it → I ⊧ᴵ it.pat :=
  fun it h => sp_from_text H N hTS hT hF it (item_at H (by decide) h)

/-- **Item 1**, the equation of the alternative at `false`. -/
theorem sp1_from_text (H : HookParams) (N : HoldsShape.NodeFacts (cH H) I) (hTS : Faithful.TermsInSort (cH H) I)
    (hT : I ⊧ᴵ (trS U.ax132).pat) (hF : I ⊧ᴵ (trS U.ax62).pat) :
    ∀ it, (Faithful.fnItems (cH H))[1]? = some it → I ⊧ᴵ it.pat :=
  fun it h => sp_from_text H N hTS hT hF it (item_at H (by decide) h)

/-- **Item 2**, the last equation, where no element of Bool gives the right side an element. -/
theorem sp2_from_text (H : HookParams) (N : HoldsShape.NodeFacts (cH H) I) (hTS : Faithful.TermsInSort (cH H) I)
    (hT : I ⊧ᴵ (trS U.ax132).pat) (hF : I ⊧ᴵ (trS U.ax62).pat) :
    ∀ it, (Faithful.fnItems (cH H))[2]? = some it → I ⊧ᴵ it.pat :=
  fun it h => sp_from_text H N hTS hT hF it (item_at H (by decide) h)

/-- **Γ's three items for f and `boolClosed` give sentence 132**, for every H, in a model with
`NodeFacts (cH H) I` and `TermsInSort (cH H) I`, without f's functional sentence. `boolClosed` is
a premise: no sentence of the text states it. -/
theorem sp_of_items (H : HookParams) (N : HoldsShape.NodeFacts (cH H) I) (hTS : Faithful.TermsInSort (cH H) I)
    (hcl : I ⊧ᴵ Faithful.boolClosed (cH H))
    (hs : ∀ it ∈ Faithful.kernelItems (Faithful.fnEquationsK (cH H) fFn), I ⊧ᴵ it.pat) :
    I ⊧ᴵ (trS U.ax132).pat := by
  have hs' : ∀ φ ∈ gpats (cH H), I ⊧ᴵ φ := by
    intro φ hφ
    rw [← gamma_shape H] at hφ
    obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hφ
    exact hs it hit
  rw [text_shape]
  obtain ⟨β, hβ, hd, hσ, X⟩ := facts H N hTS
  have hSA : SortAt I TieFRRead.boolP β := ⟨hd, hβ, rfl⟩
  have hr := idx_facts.2.2.2.2.2.1
  have hk : ∀ x ∈ xsOfB (xLit true) (xLit false) true ++ xsOfB (xLit true) (xLit false) false,
      I ⊧ᴵ eqnPat ws rG (clauseQC (cH H) tblG (vsOf (cH H)) Srt.bool prem x) TieFRRead.boolP Ff
        (sAnd (altPC (cH H) tblG (vsOf (cH H)) x) (sTop TieFRRead.boolP)) := by
    intro x hx
    have hx' : x = xLit true ∨ x = xLit false := by
      rcases List.mem_append.mp hx with h | h
      · exact Or.inl (List.mem_singleton.mp h)
      · exact Or.inr (List.mem_singleton.mp h)
    rcases hx' with rfl | rfl
    · exact hs' _ (List.mem_cons_self ..)
    · exact hs' _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hn : I ⊧ᴵ eqnPat ws rG (lastBQC (cH H) tblG (vsOf (cH H)) Srt.bool prem [jB]) TieFRRead.boolP Ff
      (BNG (cH H)) :=
    hs' _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  exact ex_text_of_split N hcl (tbl := tblG) (vs := vsOf (cH H)) (s := Srt.bool)
    (CG := CGof I (cH H) tblG (vsOf (cH H))) (CGB := CGof I (cH H) tblG (vsBof (cH H) [Srt.bool]))
    (body := bodyT) (ensT := ensT) (xB := xB) (SR := srtOf (cH H) Srt.bool)
    hSA (guardsOf_pred (I := I) N.defOK U.ax132.ax) hr hσ hσ X.hin X.hcond X.hbody X.hxr X.hinB X.hcondB
    X.hbodyB hk hn

/-- **A model of `Γ (cH H)` that satisfies `boolClosed (cH H)` satisfies sentence 132**, for every
H. `boolClosed` is the named premise beside Γ. -/
theorem sp_entailed_closed (H : HookParams) (hI : I ⊧ᴵP Faithful.Γ (cH H))
    (hcl : I ⊧ᴵ Faithful.boolClosed (cH H)) : I ⊧ᴵ (trS U.ax132).pat := by
  have hIc : I ⊧ᴵP Faithful.Γc (cH H) := by
    intro φ hφ
    rcases hφ with h | ⟨-, -, rfl⟩
    · exact hI φ h
    · exact hcl
  have N := HoldsShape.nodeFacts_of_core (coreOKH H) hIc
  have hTS : Faithful.TermsInSort (cH H) I := Faithful.termsInSort_of_core (coreOKH H) hI
  refine sp_of_items H N hTS hcl fun it hit => ?_
  have hfn : it ∈ Faithful.fnItems (cH H) := List.mem_flatMap.mpr ⟨fFn, fFn_mem H, hit⟩
  exact Faithful.sat_fns hI (Or.inl ⟨it, hfn, rfl⟩)

end

/-- **`Γc (cH H)` entails sentence 132**, for every H: `Γ (cH H)` with `boolClosed (cH H)`, the
sentence of `Γcl` on this text (`gammaC_closed`). -/
theorem sp_entailed (H : HookParams) : Faithful.Γc (cH H) ⊧ (trS U.ax132).pat := by
  intro M _ I hIc
  exact sp_entailed_closed H (fun φ hφ => hIc φ (Or.inl hφ)) (hIc _ (Or.inr (gammaC_closed H)))

/-! ## The expectation `f(true) = false` -/

/-- f's second clause: at the literal `false`, where `false = notBool(X)`. -/
def cl1 : Clause :=
  { vars := [Srt.bool], pats := [.var 0], req := none, rhs := litT false, ens := none, prio := 50, aside := false,
    pre := .and (.ceil Srt.bool (litT false)) (.equals Srt.bool (litT false) notX) }

theorem cl1_at : fFn.clauses[1]? = some cl1 := by kernel_rfl
theorem prios : fFn.clauses.map (·.prio) = [50, 50, 50] := by decide +kernel

theorem prio_50 {cl' : Clause} (h : cl' ∈ fFn.clauses) : cl'.prio = 50 := by
  have : cl'.prio ∈ fFn.clauses.map (·.prio) := List.mem_map.mpr ⟨cl', h, rfl⟩
  rw [prios] at this
  simpa using this

theorem lookupF (H : HookParams) : (cH H).lookupFn Fs = some fFn := by
  rw [Semantics.lookupFn_eq, allFns_eq H]; rfl

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- (kernel) With any hook parameters: `notBool` is a hook and no constructor, and no clause needs
a witness. -/
theorem flags_fun : (fun Hk : HookParams => !(c.withHooks Hk).isCtor boolNot && isHook boolNot &&
    ((c.withHooks Hk).fns.all fun fn => fn.clauses.all fun cl => !cl.needsWitness (c.withHooks Hk))) =
    fun _ => true := by kernel_rfl

theorem flags (H : HookParams) : (cH H).isCtor boolNot = false ∧ isHook boolNot = true ∧
    ((cH H).fns.all fun fn => fn.clauses.all fun cl => !cl.needsWitness (cH H)) = true := by
  have h : (!(cH H).isCtor boolNot && isHook boolNot &&
      ((cH H).fns.all fun fn => fn.clauses.all fun cl => !cl.needsWitness (cH H))) = true := congrFun flags_fun H
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem noWit (H : HookParams) :
    ∀ fn ∈ (cH H).fns, ∀ cl ∈ fn.clauses, cl.needsWitness (cH H) = true → cl.CondDecided (cH H) := by
  intro fn hfn cl hcl hw
  have := List.all_eq_true.mp (List.all_eq_true.mp (flags H).2.2 fn hfn) cl hcl
  rw [hw] at this
  cases this

theorem not_true : hook boolNot [bool true] = some (some (bool false)) := by kernel_rfl

/-- **`f(true)` evaluates to `false`**, for every H, by the second clause: `⌈false⌉` and
`false = notBool(true)` hold, and no clause has a smaller priority. -/
theorem eval_true (H : HookParams) : Eval (cH H) Fs [bool true] (some (bool false)) := by
  have hnot : EvalTerm (cH H) [(0, bool true)] notX (some (bool false)) :=
    EvalTerm.hook (rs := [some (bool true)]) (flags H).1 (flags H).2.1 (.cons .var .nil)
      (fun vs hvs => by
        obtain rfl : [bool true] = vs := Option.some.inj hvs
        exact Semantics.hookRes_of_value not_true)
      (fun h => nomatch (h : some [bool true] = none))
  refine Eval.clause (cl := cl1) (σ := [(0, bool true)]) (lookupF H) (List.mem_of_getElem? cl1_at) ?_
    (.cons (.var rfl) .nil) (fun t ht => nomatch (ht : (none : Option Term) = some t)) ?_
    (fun cl' hcl' _ hlt => absurd hlt (by rw [prio_50 hcl']; exact Nat.lt_irrefl 50)) rfl .dv
    (fun t ht => nomatch (ht : (none : Option Term) = some t)) .top
  · intro i s hs
    match i, hs with
    | 0, hs =>
      obtain rfl : Srt.bool = s := Option.some.inj hs
      exact ⟨bool true, rfl, rmS_sortOf_bool _ true⟩
    | i + 1, hs => exact nomatch (hs : (none : Option Srt) = some s)
  · exact Holds.and (b := true) (b' := true) (Holds.ceil (r := some (bool false)) .dv)
      (Holds.equals (r := some (bool false)) (r' := some (bool false)) .dv hnot)

/-- **`f(true) = false`**, for every H: `Γc (cH H)` entails that f applied to `true` denotes what
`false` denotes. Through Γ's items for f and `boolClosed`, the sentence of `Γcl`. -/
theorem f_true (H : HookParams) :
    Faithful.Γc (cH H) ⊧ (TiePair.app (cH H) Fs [bool true] ≡ den (cH H) (bool false)) := by
  intro M _ I hIc e m
  obtain ⟨hok, hsr, -, -, hph, -, -, -, hno⟩ := hypSound_of_core (coreOKH H)
  haveI : OvlOK (cH H) := hno
  have N := HoldsShape.nodeFacts_of_core (coreOKH H) hIc
  rw [KoreAML.interp_equal N.defOK]
  intro a
  unfold TiePair.app
  rw [Faithful.eval_den4_coreCl hIc
    (Semantics.sortedOKCl_of_sortedOK_noExs hok
      ((Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel))))
    hsr (Semantics.coreOK_parts (coreOKH H)).2.1 hph (noWit H) (HoldsShape.preReadAll_of_core (coreOKH H) hIc)
    (eval_true H) (lookupF H) (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; rfl) e a]
  rfl

end

end KCore.TieExBoolMlText

#check @KCore.TieExBoolMlText.fns_eq
#check @KCore.TieExBoolMlText.text_shape
#check @KCore.TieExBoolMlText.fnl_shape
#check @KCore.TieExBoolMlText.gamma_shape
#check @KCore.TieExBoolMlText.exReadB_H
#check @KCore.TieExBoolMlText.gammaC_closed
#check @KCore.TieExBoolMlText.sp_from_text
#check @KCore.TieExBoolMlText.sp0_from_text
#check @KCore.TieExBoolMlText.sp1_from_text
#check @KCore.TieExBoolMlText.sp2_from_text
#check @KCore.TieExBoolMlText.sp_of_items
#check @KCore.TieExBoolMlText.sp_entailed_closed
#check @KCore.TieExBoolMlText.sp_entailed
#check @KCore.TieExBoolMlText.eval_true
#check @KCore.TieExBoolMlText.f_true
/-- info: 'KCore.TieExBoolMlText.sp_from_text' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieExBoolMlText.sp_from_text
/-- info: 'KCore.TieExBoolMlText.sp2_from_text' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieExBoolMlText.sp2_from_text
/-- info: 'KCore.TieExBoolMlText.sp_entailed_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieExBoolMlText.sp_entailed_closed
/-- info: 'KCore.TieExBoolMlText.sp_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieExBoolMlText.sp_entailed
/-- info: 'KCore.TieExBoolMlText.f_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieExBoolMlText.f_true
