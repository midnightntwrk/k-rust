/-
  The equation of a construct fixture that Γ reads by cases (`orAsCases`), tied to the text's
  sentence, on the literals `kore`, `defn` and `U` of the kompiled text. Nothing here reads
  `Parse.parse` or `emit`. Run from the package root: `lake env lean -j1 test/TieFrOrNestText.lean`.

  `f2-examples/e3-ml-eq-rhs-or-nest.kompile.kore` (fixture e3-ml-eq-rhs-or-nest):
  `rule h(X) => (k(f(X) #Or g(X)) #Or #Bottom) #And {X *Int X >=Int 0 #Equals true}`, h `total`.
  The text writes one sentence, 208, whose right side holds every element of `k(f(X))` and of
  `k(g(X))` where `X *Int X >=Int 0` is `true`. Γ writes three items for h, at the positions 2, 3
  and 4 of `fnItems` (`spItem`, `sp_items`): `h(X) = k(f(X))` where `k(f(X))` has an element and
  the condition holds, the same for `k(g(X))`, and a last one, with the right side
  `k(f(X)) ∧ (false = true)`, where neither applies.

  - `raw208`, `frRead_eqT`: the sentence is h's equation and `Parse.frRead` reads it as h's clauses
    in `defn` (`hFn_at`), over names that are the definition's (`sorts_eq`, `syms_eq`).
  - `text_shape`, `fnl_shape`, `gamma_shapeG`: sentence 208, h's `functional` sentence 80 and Γ's
    three items as the patterns the lemmas of KcoreSpec/TieFR.lean read.
  - **W1**, `sp_from_text` and `sp2_from_text`, `sp3_from_text`, `sp4_from_text`, for every H. The
    premise set, written out: sentence 208; sentence 80; and two facts of the model,
    `HoldsShape.NodeFacts (cH H) I` and `Faithful.TermsInSort (cH H) I`. No item follows from
    sentence 208 alone: the sentence gives `h(X)` every element of each alternative, and an item
    says `h(X)` is one alternative, which needs `h(X)` to be one element (sentence 80). The last
    item holds because its premise is never met: the sentence would leave `h(X)` empty there and
    sentence 80 gives it an element.
    `NodeFacts` is the structure the lemmas take whole; it holds, beside definedness, `⌈_⌉` and
    that the numbered sorts denote sorts, that each value is one element of its sort and that
    distinct values are distinct elements, which no sentence of the text states. The library
    obtains it from a model of Γc only (`HoldsShape.nodeFacts_of_core`). So these statements are
    not consequences of the two sentences with the text's signature, and they are not stated as
    such.
  - **E**, `sp_entailed`: Γ entails sentence 208, for every H. The three items give it where the
    last item's right side is empty, which holds because `false` and `true` are two elements of
    Bool (`TieFRRead.noneEmpty_of_apart`). No `functional` sentence is read. The text reads no
    confined sort (`readsConfined_c`), so Γc is Γ.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieFrOrNestText

open KCore ML Faithful KoreAML KoreAML.TieFR KCore.TieFRRead KCore.TieFRTightB

kore_term kore from "f2-examples/e3-ml-eq-rhs-or-nest.kompile.kore"
definition_of defn from "f2-examples/e3-ml-eq-rhs-or-nest.kompile.kore"
user_axioms U from "f2-examples/e3-ml-eq-rhs-or-nest.kompile.kore" module "E3-ML-EQ-RHS-OR-NEST"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The text reads no confined sort: Γc is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-! ## h and its clauses in `defn` -/

def fS : Sym := nRegSyms + 4
def gS : Sym := nRegSyms + 5
def hS : Sym := nRegSyms + 6
def kS : Sym := nRegSyms + 7
def kfX : Term := .app kS [.app fS [.var 0]]
def kgX : Term := .app kS [.app gS [.var 0]]
/-- `X *Int X >=Int 0`. -/
def bX : Term := .app intGe [.app intMul [.var 0, .var 0], .dv Srt.int (.int 0)]

/-- The alternatives: `k(f(X))` and `k(g(X))`, each with the lifted condition. -/
def xsC : List (Term × List Term) := [(kfX, [bX]), (kgX, [bX])]

/-- h, declared `total`, with the clauses of the split of its equation. -/
def hFn : Fn := ⟨hS, [Srt.int], Srt.int, Parse.frClauses Srt.int [Srt.int] [.var 0] none 50 false (frAltsOf xsC), true⟩

/-! **h is the third function of `defn`**, with these clauses. -/
kernel_rfl hFn_at : c.fns[2]? = some hFn
theorem hFn_mem (H : HookParams) : hFn ∈ (cH H).fns := List.mem_of_getElem? hFn_at

theorem names_c : c.sortNames = ["KCell", "KCellOpt"] ∧ c.symName fS = "Lblf" ∧ c.symName gS = "Lblg" ∧
    c.symName hS = "Lblh" ∧ c.symName kS = "Lblk" := by decide +kernel

/-! ## The text's two sentences -/

def iS : Kore.KSort := srt "Int"
def bS : Kore.KSort := srt "Bool"
def xK : Kore.Pattern := ev "VarX" iS
def fK : Kore.Pattern := ap "Lblf" [xK]
def gK : Kore.Pattern := ap "Lblg" [xK]
/-- `k(f(X) ∨ g(X))`. -/
def kOr : Kore.Pattern := ap "Lblk" [.or iS [fK, gK]]
/-- `X *Int X >=Int 0`. -/
def bK : Kore.Pattern := ap "Lbl'Unds-GT-Eqls'Int'Unds'" [ap "Lbl'UndsStar'Int'Unds'" [xK, xK], .dv iS "0"]
/-- `{X *Int X >=Int 0 #Equals true}`. -/
def eqK : Kore.Pattern := .equals bS iS bK (.dv bS "true")
/-- The right side: `(k(f(X) ∨ g(X)) ∨ ⊥) ∧ {X *Int X >=Int 0 #Equals true}`. -/
def pT : Kore.Pattern := .and iS [.or iS [kOr, .bottom iS], eqK]
def enT : Kore.Pattern := .top iS
/-- The premise: `X0 ∈ VarX`. -/
def premK : Kore.Pattern := .and R [.top R, .and R [.in iS R (ev "X0" iS) xK, .top R]]

/-- **Sentence 208** is `X0 ∈ VarX → h(X0) = pT ∧ ⊤`. -/
theorem pat208 : U.ax208.ax.sortVars = [Rv] ∧
    U.ax208.ax.pattern = .implies R premK (.equals iS R (ap "Lblh" [ev "X0" iS]) (.and iS [pT, enT])) := by
  decide +kernel

/-- **Sentence 80** is h's `functional` sentence, `∃Val. Val = h(K0)`. -/
theorem pat80 : U.ax80.ax.sortVars = [Rv] ∧
    U.ax80.ax.pattern = .exist R (evar "Val" iS) (.equals iS R (.var (.evar (evar "Val" iS))) (ap "Lblh" [ev "K0" iS])) ∧
    U.ax80.ax = Model.functionalAxiom c hFn := by
  decide +kernel

/-- The names the equation is read with: the definition's sorts and symbols (`sorts_eq`, `syms_eq`),
f, g, h, k its functions of result sort Int, and h with a `functional` sentence (sentence 80). -/
def NT : Parse.Names :=
  { sorts := ["KCell", "KCellOpt"]
    syms := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf", "Lblg", "Lblh", "Lblk"]
    keyFns := [(nRegSyms + 4, "Int"), (nRegSyms + 5, "Int"), (nRegSyms + 6, "Int"), (nRegSyms + 7, "Int")]
    fnlSyms := [("Lblh", false)] }

theorem sorts_eq : NT.sorts = c.sortNames := by decide +kernel
theorem syms_eq : NT.syms = c.symNames := by decide +kernel

/-- The equation of sentence 208 as `Parse.rawEqn?` reads it. -/
noncomputable def eqT : Parse.RawEqn := ⟨"Lblh", [xK], none, none, pT, U.ax208.ax.attributes, none, false⟩
kernel_rfl raw208 : Parse.rawEqn? U.ax208.ax = some eqT

def vsF : List KoreAML.Var := [⟨"X", "Int"⟩]

/-! **The reader reads the equation** as h's clauses (kernel). -/
kernel_rfl frRead_eqT : Parse.frRead NT eqT = .ok (some (hFn.clauses, vsF))

/-! ## The shapes -/

noncomputable def al : List String := kore.aliasNames
noncomputable def tbl : VarTable := tableOf U.ax208.ax.sortVars U.ax208.ax.pattern
noncomputable def ctx : Ctx := ⟨tbl, al⟩
noncomputable def ws : List P := guardsOf U.ax208.ax
noncomputable def r : EVar := tbl.ev (sortVarKey Rv)
noncomputable def prem : P := tr ctx premK
noncomputable def IntP : P := trSort tbl iS
noncomputable def Fh : P := tr ctx (ap "Lblh" [ev "X0" iS])
noncomputable def rhsT : P := sAnd (tr ctx pT) (tr ctx enT)
noncomputable def x0 : EVar := tbl.ev (evarKey (evar "X0" iS))
noncomputable def xv : EVar := tbl.ev (evarKey (evar "VarX" iS))

theorem text_shape : (trS U.ax208).pat = eqnPat ws r prem IntP Fh rhsT :=
  trAxiom_eqnPat kore.symbolDecls kore.aliasNames U.ax208.index U.ax208.module U.ax208.ax pat208.1 pat208.2

/-- The right side and the `ensures` part apply no alias of the text. -/
theorem alias_free : aliasFreeFR al eqT.rhs = true ∧ aliasFreeFR al enT = true := by decide +kernel

/-- The table of Γ's items for h. -/
def tblG : VarTable := [.sortVar "R", .evar "X0" (srt "Int"), .evar "VarV0" (srt "Int")]

/-- The clauses' variables. -/
noncomputable abbrev vsC (H : HookParams) : List KoreAML.Var := Faithful.canonVars (cH H) [Srt.int]

/-- The last clause's right side `k(f(X)) ∧ (false = true)`. -/
noncomputable def BNG (H : HookParams) : P := sAnd (altP (cH H) tblG (vsC H) (kfX, [bX]))
  (tr ⟨tblG, []⟩ (reqPat (srtOf (cH H) Srt.int) (some (Term.kore (cH H) (vsC H) (Parse.boolT false)))))

/-! The semantics is well sorted (`sortedOK`, a part of `coreOK`), for every H (kernel). -/
kernel_rfl sortedH : ∀ H : HookParams, (cH H).sortedOK = true

/-- The clause check holds of h's clauses. -/
theorem sorted_h (H : HookParams) : ∀ cl ∈ hFn.clauses, (cH H).clauseSorted hFn ((cH H).fns.map Fn.sig) cl = true :=
  TieFRVars.clauseSorted_of_sortedOK (sortedH H) (hFn_mem H)

/-! The frame of Γ's items for h (no competitor: h's clauses are all of priority 50) is the text's:
its table `tblG`, the text's guards, premise and left side, for every H (kernel). -/
kernel_rfl gf_lower : TieFRGamma.lowerAtFG hFn 50 = []
kernel_rfl gf_tbl : ∀ H : HookParams, TieFRGamma.tblFG (cH H) hFn [] [Srt.int] [.var 0] none = tblG
kernel_rfl gf_ws : ∀ H : HookParams, TieFRGamma.wsFG (cH H) hFn [] [Srt.int] [.var 0] none = ws
kernel_rfl gf_r : tblG.ev (sortVarKey Rv) = r
kernel_rfl gf_prem : ∀ H : HookParams, tr ⟨tblG, []⟩ (TieFRGamma.premFG (cH H) hFn [Srt.int] [.var 0] none) = prem
kernel_rfl gf_S : ∀ H : HookParams, trSort tblG (srtOf (cH H) Srt.int) = IntP
kernel_rfl gf_F : ∀ H : HookParams, tr ⟨tblG, []⟩ (TieFRGamma.headFG (cH H) hFn) = Fh

/-- **Γ's three items for h**, with the premises `clauseQ`, `lastQ` of the general lemmas
(`TieFRGamma.gamma_shapeFG`), for every H. -/
theorem gamma_shapeG (H : HookParams) : (Faithful.kernelItems (Faithful.fnEquationsK (cH H) hFn)).map (·.pat) =
    [eqnPat ws r (clauseQ (cH H) tblG (vsC H) Srt.int prem (kfX, [bX])) IntP Fh
       (sAnd (altP (cH H) tblG (vsC H) (kfX, [bX])) (sTop IntP)),
     eqnPat ws r (clauseQ (cH H) tblG (vsC H) Srt.int prem (kgX, [bX])) IntP Fh
       (sAnd (altP (cH H) tblG (vsC H) (kgX, [bX])) (sTop IntP)),
     eqnPat ws r (lastQ (cH H) tblG (vsC H) Srt.int prem xsC) IntP Fh (BNG H)] := by
  obtain ⟨hxs, hlen, hocc⟩ := TieFRVars.gammaPrem_of_frRead (c := cH H) frRead_eqT
    (rfl : hFn.clauses = Parse.frClauses Srt.int [Srt.int] [.var 0] none 50 false (frAltsOf xsC)) (sorted_h H)
  have h := TieFRGamma.gamma_shapeFG (cH H) hFn (s := Srt.int) (vars := [Srt.int]) (pats := [.var 0]) (req := none)
    (prio := 50) (aside := false) (xs := xsC) hxs hlen hocc
  have hS : trSort tblG (srtOf (cH H) hFn.result) = IntP := gf_S H
  simp only [gf_lower, gf_tbl H, gf_ws H, gf_r, gf_prem H, hS, gf_F H, TieFRGamma.withCompFG_nil] at h
  exact h

/-- Γ's axiom at position j of `fnItems`, and its item. -/
noncomputable def spAx (j : Nat) : Kore.Axiom := ((TiePair.fnAxioms c)[j]?).getD ⟨[], .top KoreAML.R, []⟩
noncomputable def spItem (j : Nat) : P := (trAxiom [] [] ⟨0, "kernel", spAx j⟩).pat

theorem spAx_at : (TiePair.fnAxioms c)[2]? = some (spAx 2) ∧ (TiePair.fnAxioms c)[3]? = some (spAx 3) ∧
    (TiePair.fnAxioms c)[4]? = some (spAx 4) := by decide +kernel

/-! **Γ's items for h are the items 2, 3 and 4 of `fnItems`**, for every H (kernel). -/
kernel_rfl sp_items : ∀ H : HookParams,
  (Faithful.kernelItems (Faithful.fnEquationsK (cH H) hFn)).map (·.pat) = [spItem 2, spItem 3, spItem 4]

/-- The functional sentence: `∃v. v = h(K0)`, K0 the variable `k0`. -/
noncomputable def tblF : VarTable := tableOf U.ax80.ax.sortVars U.ax80.ax.pattern
noncomputable def rF : EVar := tblF.ev (sortVarKey Rv)
noncomputable def vF : EVar := tblF.ev (evarKey (evar "Val" iS))
noncomputable def k0 : EVar := tblF.ev (evarKey (evar "K0" iS))
def hHead : P := sym (.symbol "Lblh")
noncomputable def tsF : List (EVar × EVar × P) := [(x0, k0, IntP)]

theorem fnl_shape : (trS U.ax80).pat =
    fnlPat (sortGuard rF :: tsF.map fun t => (t.2.1 ∈∈ inhOf t.2.2)) rF vF IntP
      (appList hHead (tsF.map fun t => .evar t.2.1)) := by
  rw [show (trS U.ax80).pat = _ from trAxiom_fnlPat kore.symbolDecls kore.aliasNames U.ax80.index U.ax80.module
    U.ax80.ax (F := ap "Lblh" [ev "K0" iS]) (v := evar "Val" iS) pat80.1 pat80.2.1]
  decide +kernel

/-- The facts of the indices `one_of_fnl` reads, and of the guards. -/
theorem idx_facts :
    Fh = appList hHead (tsF.map fun t => .evar t.1) ∧ (tsF.map (·.2.1)).Nodup ∧ rF ∉ tsF.map (·.2.1) ∧
      vF ∉ tsF.map (·.2.1) ∧ vF ≠ rF ∧ sortGuard r ∈ ws ∧ (x0 ∈∈ inhOf IntP) ∈ ws ∧
      (xv ∈∈ inhOf IntP) ∈ ws ∧ IntP = sym (.sort "SortInt") := by
  decide +kernel

/-- What the round trip of `Parse.term` takes of the text (kernel): the sorts of the variables
read, the alternatives and the lifted conjunct read as the terms of their patterns (`frRT`), and
the guards holding each variable read in its sort (`guardsHold`). -/
theorem rt_facts : Parse.varSorts NT vsF = .ok [Srt.int] ∧ TieFRRT.frRT NT eqT = true ∧
    TieFRVars.guardsHold ws tbl vsF = true :=
  ⟨by kernel_rfl, by decide +kernel, by decide +kernel⟩

/-! The tables are aligned on the variables read, for every H (kernel). -/
kernel_rfl alignH : ∀ H : HookParams, TermRT.alignOK (cH H) tblG tbl [Srt.int] vsF = true

/-! **The decision `tightB` on the right side**, for every H (kernel): each operand of its
connectives states its sort or is read as a term of it. -/
kernel_rfl tightH : ∀ H : HookParams, tightB NT (cH H) tblG tbl [Srt.int] vsF pT = true

theorem int_num (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)

/-- The alternatives translate as the kept ones, each with the lifted conjunct's Bool term as its
condition (`altsTrOK`): from the reader, by the round trip of `Parse.term`. -/
theorem tr_ofReader (H : HookParams) :
    altsTrOK (cH H) tblG (vsC H) tbl (frConds eqT.rhs) [] (keptAlts (frSide eqT.rhs)) xsC = true :=
  TieFRRT.altsTrOK_of_clauses (c := cH H) syms_eq sorts_eq frRead_eqT rt_facts.1 (alignH H) rt_facts.2.1
    (rfl : hFn.clauses = Parse.frClauses Srt.int [Srt.int] [.var 0] none 50 false (frAltsOf xsC))

/-! ## In a model -/

/-- A model of Γ satisfies each of Γ's equations. -/
theorem fnItem_sat {H : HookParams} {M : Type} {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) {j : Nat} {a : Kore.Axiom} (ha : (TiePair.fnAxioms c)[j]? = some a) :
    I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat := by
  have hg := TiePair.gammaPats_at ha
  obtain ⟨it, hit, he⟩ : ∃ it ∈ fnItems c, it.pat = (trAxiom [] [] ⟨0, "kernel", a⟩).pat := by
    unfold TiePair.gammaPats at hg
    rw [List.getElem?_map] at hg
    cases h : (fnItems c)[j]? with
    | none => rw [h] at hg; cases hg
    | some it => rw [h] at hg; exact ⟨it, List.mem_of_getElem? h, Option.some.inj hg⟩
  rw [← he]
  exact hI _ (TiePair.mem_Γ_fns (Or.inl ⟨it, by rw [TiePair.fnItems_withHooks]; exact hit, rfl⟩))

section Model
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The readings of the general lemmas, in a model with `NodeFacts (cH H) I` and
`TermsInSort (cH H) I`: `TightSem` of the right side from the decision `tightH`. -/
theorem readingsG (H : HookParams) (F : HoldsShape.NodeFacts (cH H) I) (hTS : Faithful.TermsInSort (cH H) I) :
    ∃ σI, SortAt I IntP σI ∧
      (∀ (e : Valuation M) a, (trSort tblG (srtOf (cH H) Srt.int)).interpret I e a ↔ a = σI) ∧
      Readings I ws r σI prem rhsT xsC (altP (cH H) tblG (vsC H)) (altG I (cH H) tblG (vsC H))
        (clauseQ (cH H) tblG (vsC H) Srt.int prem) (lastQ (cH H) tblG (vsC H) Srt.int prem xsC) := by
  obtain ⟨-, -, -, -, -, hr, -, -, hIntP⟩ := idx_facts
  obtain ⟨σI, hσS, hσ⟩ := F.sort (s := Srt.int) (int_num H)
  have hσ' : ∀ (e : Valuation M) a, (trSort tblG (srtOf (cH H) Srt.int)).interpret I e a ↔ a = σI :=
    fun e a => hσ tblG e a
  have hSA : SortAt I IntP σI := ⟨fun e a => by rw [← gf_S H]; exact hσ' e a, hσS, by rw [hIntP]; rfl⟩
  have hin : ∀ e m, At I ws r e m → ∀ x ∈ xsC, ∀ a, (altP (cH H) tblG (vsC H) x).interpret I e a → Inh I σI a :=
    TieFRVars.inSort_of_read (c := cH H) (f := hFn) F.defOK hTS sorts_eq rt_facts.1 (alignH H) rt_facts.2.2
      (sorted_h H) (int_num H) hσ'
  have hT : ∀ e m, At I ws r e m → TightSem I tbl e pT :=
    tightSem_of_guardsB F hTS syms_eq sorts_eq rt_facts.1 (alignH H) rt_facts.2.2 (tightH H)
  have hr' : sortGuard (tblG.ev (sortVarKey Rv)) ∈ ws := by rw [gf_r]; exact hr
  have R := readings_of_frT F (al := al) (prem := prem) frRead_eqT alias_free.1 alias_free.2 hr' hσ' hσS
    (by rw [gf_r]; exact hin) (by rw [gf_r]; exact hT) (en := enT) rfl (fun e a => hSA.den e a) (tr_ofReader H)
  rw [gf_r] at R
  exact ⟨σI, hSA, hσ', R⟩

/-- **W1, the three items together**: sentence 208 with h's functional sentence 80 gives each of
Γ's three items for h, for every H, in a model with `NodeFacts` and `TermsInSort`. -/
theorem sp_from_text (H : HookParams) (F : HoldsShape.NodeFacts (cH H) I) (hTS : Faithful.TermsInSort (cH H) I)
    (hT : I ⊧ᴵ (trS U.ax208).pat) (hF : I ⊧ᴵ (trS U.ax80).pat) :
    ∀ φ ∈ [spItem 2, spItem 3, spItem 4], I ⊧ᴵ φ := by
  intro φ hmem
  rw [← sp_items H, gamma_shapeG H] at hmem
  rw [text_shape] at hT
  rw [fnl_shape] at hF
  obtain ⟨σI, hSA, -, R⟩ := readingsG H F hTS
  obtain ⟨hFh, hnd, hrk, hvk, hvr, hr, hx0, -, hIntP⟩ := idx_facts
  have hG := guardsOf_pred F.defOK U.ax208.ax
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
  · exact none_of_text F.defOK F.ceilDef hSA hr hG R hT hone (BNG H)

/-- **W1 for item 2**, `h(X) = k(f(X))` where `k(f(X))` has an element and the condition holds.
Premises: sentence 208, sentence 80, `NodeFacts (cH H) I`, `TermsInSort (cH H) I`. -/
theorem sp2_from_text (H : HookParams) (F : HoldsShape.NodeFacts (cH H) I) (hTS : Faithful.TermsInSort (cH H) I)
    (hT : I ⊧ᴵ (trS U.ax208).pat) (hF : I ⊧ᴵ (trS U.ax80).pat) : I ⊧ᴵ spItem 2 :=
  sp_from_text H F hTS hT hF _ (by simp)

/-- **W1 for item 3**, `h(X) = k(g(X))` where `k(g(X))` has an element and the condition holds.
Premises: sentence 208, sentence 80, `NodeFacts (cH H) I`, `TermsInSort (cH H) I`. -/
theorem sp3_from_text (H : HookParams) (F : HoldsShape.NodeFacts (cH H) I) (hTS : Faithful.TermsInSort (cH H) I)
    (hT : I ⊧ᴵ (trS U.ax208).pat) (hF : I ⊧ᴵ (trS U.ax80).pat) : I ⊧ᴵ spItem 3 :=
  sp_from_text H F hTS hT hF _ (by simp)

/-- **W1 for item 4**, the last clause, where neither alternative applies. Premises: sentence 208,
sentence 80, `NodeFacts (cH H) I`, `TermsInSort (cH H) I`. -/
theorem sp4_from_text (H : HookParams) (F : HoldsShape.NodeFacts (cH H) I) (hTS : Faithful.TermsInSort (cH H) I)
    (hT : I ⊧ᴵ (trS U.ax208).pat) (hF : I ⊧ᴵ (trS U.ax80).pat) : I ⊧ᴵ spItem 4 :=
  sp_from_text H F hTS hT hF _ (by simp)

/-- **Γ's three items for h give sentence 208**, in a model with `NodeFacts` and `TermsInSort`:
the last clause's right side is empty because `false` and `true` are two elements of Bool. -/
theorem sp_of_items (H : HookParams) (F : HoldsShape.NodeFacts (cH H) I) (hTS : Faithful.TermsInSort (cH H) I)
    (hs : ∀ φ ∈ [spItem 2, spItem 3, spItem 4], I ⊧ᴵ φ) : I ⊧ᴵ (trS U.ax208).pat := by
  rw [← sp_items H, gamma_shapeG H] at hs
  rw [text_shape]
  obtain ⟨σI, hSA, hσ', R⟩ := readingsG H F hTS
  obtain ⟨-, -, -, -, -, hr, -, -, -⟩ := idx_facts
  refine text_of_split (BN := BNG H) F.defOK F.ceilDef hSA hr (guardsOf_pred F.defOK U.ax208.ax) R
    (fun x hx => ?_) (hs _ (by simp)) (noneEmpty_of_apart F hσ' hSA.isSort)
  simp only [xsC, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact hs _ (by simp)
  · exact hs _ (by simp)

/-- A model of Γ has the constructors' facts (Γc is Γ here). -/
theorem nodeFacts_of_gamma (H : HookParams) (hI : I ⊧ᴵP Γ (cH H)) : HoldsShape.NodeFacts (cH H) I :=
  HoldsShape.nodeFacts_of_core (coreOKH H)
    (by rw [Γc_plain ((Semantics.readsConfined_withHooks c H).trans readsConfined_c)]; exact hI)

/-- **The tie of sentence 208 in a model of Γ**: it holds, as Γ's three items for h do, for
every H. -/
theorem sp_tie (H : HookParams) (hI : I ⊧ᴵP Γ (cH H)) :
    (I ⊧ᴵ (trS U.ax208).pat) ∧ ∀ φ ∈ [spItem 2, spItem 3, spItem 4], I ⊧ᴵ φ := by
  have hs : ∀ φ ∈ [spItem 2, spItem 3, spItem 4], I ⊧ᴵ φ := by
    intro φ hφ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl
    · exact fnItem_sat hI spAx_at.1
    · exact fnItem_sat hI spAx_at.2.1
    · exact fnItem_sat hI spAx_at.2.2
  exact ⟨sp_of_items H (nodeFacts_of_gamma H hI) (termsInSort_of_core (coreOKH H) hI) hs, hs⟩

end Model

/-- **E for sentence 208**: Γ entails it, for every H. -/
theorem sp_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax208).pat := by
  intro M _ I hI
  exact (sp_tie H hI).1

end KCore.TieFrOrNestText

#check @KCore.TieFrOrNestText.hFn_at
#check @KCore.TieFrOrNestText.raw208
#check @KCore.TieFrOrNestText.frRead_eqT
#check @KCore.TieFrOrNestText.gamma_shapeG
#check @KCore.TieFrOrNestText.sp_items
#check @KCore.TieFrOrNestText.sp_from_text
#check @KCore.TieFrOrNestText.sp2_from_text
#check @KCore.TieFrOrNestText.sp3_from_text
#check @KCore.TieFrOrNestText.sp4_from_text
#check @KCore.TieFrOrNestText.sp_of_items
#check @KCore.TieFrOrNestText.sp_tie
#check @KCore.TieFrOrNestText.sp_entailed
/-- info: 'KCore.TieFrOrNestText.sp_from_text' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieFrOrNestText.sp_from_text
/-- info: 'KCore.TieFrOrNestText.sp_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieFrOrNestText.sp_entailed
