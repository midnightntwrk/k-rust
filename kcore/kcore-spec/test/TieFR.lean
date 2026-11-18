/-
  The tie of an equation with `\or` on its right side (KcoreSpec/TieFR.lean) on fixture
  `e3-ml-eq-rhs-or-total` (test/constructs/fixtures): its sentence 344, `rule h(X) => f(X) #Or g(X)`
  with h `total`, and h's functional sentence 216, against the three equations `Γ` states for the
  clauses `Parse.frClauses` gives that equation. Run from the package root:
  `lake env lean -j1 test/TieFR.lean`.

  - `ax344`, `ax216`: the two sentences as kore.txt writes them (`//@ 344`, `//@ 216`), written out
    with the builders of Kore/Build.lean; `ax216_eq`: 216 is `Model.functionalAxiom c hFn`.
  - `hFn`: h with the clauses `Parse.frClauses` gives for the alternatives `f(X)`, `g(X)` with no
    predicate (`frClauses_eq`: `pre := ⌈f(X)⌉`, `⌈g(X)⌉`, and `¬⌈f(X)⌉ ∧ ¬⌈g(X)⌉` with
    `ens := false`). `Γ`'s items for h are `kernelItems (fnEquationsK c hFn)`.
  - The shapes (kernel): the translated sentence is `eqnPat ws r prem Int Fh rhsT`
    (`text_shape`), `Γ`'s three items are `eqnPat` with the premises `prem ∧ ⌈aₖ⌉` and
    `prem ∧ ¬⌈f(X)⌉ ∧ ¬⌈g(X)⌉` over the same guards, variable of R and application `Fh`
    (`gamma_shape`), and the functional sentence is `fnlPat` of h applied to its variable K0
    (`fnl_shape`), which `one_of_fnl` reads at X0.
  - What is read of the model (`Bg`): definedness, the definedness symbols (`ceilDefItem`), that
    `SortInt` denotes a sort, and that f and g map an element of Int into Int. Nothing about h.
  - `gamma_of_text`: the sentence with h's functional sentence gives each of `Γ`'s three items.
  - `text_of_gamma`: `Γ`'s three items give the sentence, without the functional sentence. No
    predicate of an alternative (no `ensures`), so the last clause's right side `f(X) ∧
    ⌈false = true⌉` is empty where `¬⌈f(X)⌉` holds, whatever Bool's elements are
    (`noneEmpty_of_sub`).
  - `readingsG`, `text_of_gammaG`, `gamma_of_textG`: the same two directions with the readings the
    general lemmas of KcoreSpec/TieFRRead.lean derive (`readings_of_fr`, `rhs_of_reader`,
    `inSort_of_terms`) and the last clause's right side empty from `noneEmpty_of_apart`, in a
    model with `NodeFacts c I` and `TermsInSort c I`. The literal facts they read are kernel
    decisions (`gamma_shapeG`, `lit_facts`, `norm_facts`): `Γ`'s premises are `clauseQ` and
    `lastQ` over `Γ`'s table `tblG`, the text's alternatives translate as `Γ`'s, and the reader
    reads `f(X) ∨ g(X)` as the alternatives `f(X)`, `g(X)` with no condition.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.TieFRTest

open ML KoreAML KoreAML.TieFR
open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

/-! ## The semantics: h with the clauses of its split -/

def F : Sym := nRegSyms + 4
def G : Sym := nRegSyms + 5
def H : Sym := nRegSyms + 6
def fX : Term := .app F [.var 0]
def gX : Term := .app G [.var 0]

def fFn : Fn := ⟨F, [Srt.int], Srt.int, [⟨[Srt.int], [.var 0], none, .var 0, none, 50, false, [], .top, .top⟩], true⟩
def gFn : Fn := ⟨G, [Srt.int], Srt.int,
  [⟨[Srt.int], [.var 0], none, .app intSub [.dv Srt.int (.int 0), .var 0], none, 50, false, [], .top, .top⟩], true⟩

/-- h, declared `total`, with the clauses of the split of `h(X) => f(X) #Or g(X)`. -/
def hFn : Fn := ⟨H, [Srt.int], Srt.int, Parse.frClauses Srt.int [Srt.int] [.var 0] none 50 false [(fX, []), (gX, [])], true⟩

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

/-- The three clauses: `⌈f(X)⌉ → h(X) = f(X)`, `⌈g(X)⌉ → h(X) = g(X)`, and where neither is
defined `h(X) = f(X) ∧ ⌈false = true⌉`. -/
theorem frClauses_eq : hFn.clauses =
    [⟨[Srt.int], [.var 0], none, fX, none, 50, false, [], .ceil Srt.int fX, .top⟩,
     ⟨[Srt.int], [.var 0], none, gX, none, 50, false, [], .ceil Srt.int gX, .top⟩,
     ⟨[Srt.int], [.var 0], none, fX, some (.dv Srt.bool (.bool false)), 50, false, [],
       .and (.not (.ceil Srt.int fX)) (.not (.ceil Srt.int gX)), .top⟩] := rfl

/-! ## The text's two sentences -/

def iS : Kore.KSort := srt "Int"

/-- Sentence 344: `X0 ∈ VarX → h(X0) = (f(VarX) ∨ g(VarX)) ∧ ⊤`. -/
def ax344 : Kore.Axiom :=
  { sortVars := [Rv]
    pattern := .implies R
      (.and R [.top R, .and R [.in iS R (ev "X0" iS) (ev "VarX" iS), .top R]])
      (.equals iS R (ap "Lblh" [ev "X0" iS])
        (.and iS [.or iS [ap "Lblf" [ev "VarX" iS], ap "Lblg" [ev "VarX" iS]], .top iS]))
    attributes := [] }

/-- Sentence 216: `∃Val. Val = h(K0)`. -/
def ax216 : Kore.Axiom :=
  { sortVars := [Rv]
    pattern := .exist R (evar "Val" iS) (.equals iS R (.var (.evar (evar "Val" iS))) (ap "Lblh" [ev "K0" iS]))
    attributes := [attr "functional"] }

theorem ax216_eq : ax216 = Faithful.Model.functionalAxiom c hFn := by decide +kernel

def textItem : Item := trAxiom [] [] ⟨344, "E3-ML-EQ-RHS-OR-TOTAL", ax344⟩
def fnlItem : Item := Faithful.Model.functionalItem c hFn

/-! ## The shapes -/

def tbl : VarTable := tableOf ax344.sortVars ax344.pattern
def ctx : Ctx := ⟨tbl, []⟩
def ws : List P := guardsOf ax344
def r : EVar := tbl.ev (sortVarKey Rv)
def prem : P := tr ctx (.and R [.top R, .and R [.in iS R (ev "X0" iS) (ev "VarX" iS), .top R]])
def IntP : P := trSort tbl iS
def Fh : P := tr ctx (ap "Lblh" [ev "X0" iS])
def A1 : P := tr ctx (ap "Lblf" [ev "VarX" iS])
def A2 : P := tr ctx (ap "Lblg" [ev "VarX" iS])
def rhsT : P := sAnd (tr ctx (.or iS [ap "Lblf" [ev "VarX" iS], ap "Lblg" [ev "VarX" iS]])) (tr ctx (.top iS))
def x0 : EVar := tbl.ev (evarKey (evar "X0" iS))
def xv : EVar := tbl.ev (evarKey (evar "VarX" iS))

/-- The premise of the clause of an alternative x: `prem ∧ ⌈x⌉`. -/
def Q (x : P) : P := sAnd prem (sCeil IntP (.evar r) x)
/-- The premise of the last clause: `prem ∧ ¬⌈f(X)⌉ ∧ ¬⌈g(X)⌉`. -/
def QN : P := sAnd prem (sAnd (sNot (.evar r) (sCeil IntP (.evar r) A1)) (sNot (.evar r) (sCeil IntP (.evar r) A2)))
/-- The last clause's right side: `f(X) ∧ ⌈false = true⌉`. -/
def BN : P := sAnd A1 (sEquals (trSort tbl (srt "Bool")) IntP (tr ctx (.dv (srt "Bool") "false")) (tr ctx (.dv (srt "Bool") "true")))

theorem text_shape : textItem.pat = eqnPat ws r prem IntP Fh rhsT :=
  trAxiom_eqnPat [] [] _ _ ax344 rfl rfl

/-- `Γ`'s items for h: the three clauses' equations, over the sentence's guards, variable of R and
application of h. -/
theorem gamma_shape : (Faithful.kernelItems (Faithful.fnEquationsK c hFn)).map (·.pat) =
    [eqnPat ws r (Q A1) IntP Fh (sAnd A1 (sTop IntP)), eqnPat ws r (Q A2) IntP Fh (sAnd A2 (sTop IntP)),
     eqnPat ws r QN IntP Fh BN] := by decide +kernel

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
      (xv ∈∈ inhOf IntP) ∈ ws ∧ IntP = sym (.sort "SortInt") ∧ rhsT = sAnd (sOr IntP A1 A2) (sTop IntP) := by
  decide +kernel

/-! ## In a model -/

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- What is read of the model: definedness, the definedness symbols, `SortInt` a sort, and f and g
mapping an element of Int into Int. -/
structure Bg (I : Interpretation KoreAML.Sym M) (σI : M) : Prop where
  defOK : DefOK I
  ceilDef : I ⊧ᴵ ceilDefItem.pat
  intSort : ∀ a, I.evalSymb (.sort "SortInt") a ↔ a = σI
  isSort : IsSort I σI
  fg : ∀ (e : Valuation M), Inh I σI (e.evalEvar xv) → ∀ x ∈ [A1, A2], ∀ a, x.interpret I e a → Inh I σI a

omit [Inhabited M] in
theorem Bg.sortAt {σI : M} (B : Bg I σI) : SortAt I IntP σI :=
  ⟨fun e a => by rw [idx_facts.2.2.2.2.2.2.2.2.1]; exact B.intSort a, B.isSort,
   by rw [idx_facts.2.2.2.2.2.2.2.2.1]; rfl⟩

omit [Inhabited M] in
theorem Bg.inhInt {σI : M} (B : Bg I σI) {e : Valuation M} {m : M} {x : EVar} (hx : (x ∈∈ inhOf IntP) ∈ ws)
    (hat : At I ws r e m) : Inh I σI (e.evalEvar x) := by
  have := hat.1 _ hx
  rwa [interp_member B.defOK, interp_inhOf_of (B.sortAt.den e)] at this

theorem Bg.ceil {σI : M} (B : Bg I σI) {e : Valuation M} {m : M} (hat : At I ws r e m) {x : P} (hx : x ∈ [A1, A2]) :
    (sCeil IntP (.evar r) x).interpret I e m ↔ ∃ b, x.interpret I e b := by
  rw [interp_sCeil B.defOK B.ceilDef (B.sortAt.den e) (fun _ => interp_evar) B.isSort
    (isSort_of_at B.defOK idx_facts.2.2.2.2.2.1 hat)
    (B.fg e (B.inhInt idx_facts.2.2.2.2.2.2.2.1 hat) x hx) m]
  exact ⟨fun h => h.1, fun h => ⟨h, hat.2⟩⟩

/-- The readings of the sentence's and the clauses' patterns, the alternatives f(X) and g(X)
with no predicate. -/
theorem readings {σI : M} (B : Bg I σI) :
    Readings I ws r σI prem rhsT [A1, A2] id (fun _ _ => True) Q QN where
  inSort e m hat x hx := B.fg e (B.inhInt idx_facts.2.2.2.2.2.2.2.1 hat) x hx
  clause e m hat x hx := by
    show (sAnd prem (sCeil IntP (.evar r) x)).interpret I e m ↔ _
    rw [interp_sAnd, B.ceil hat hx]
    simp
  none e m hat := by
    unfold QN
    have hR : ∀ a, (Pattern.evar r : P).interpret I e a ↔ a = e.evalEvar r := fun _ => interp_evar
    simp only [interp_sAnd, interp_sNot, interp_inhOf_of hR, B.ceil hat (List.mem_cons_self ..),
      B.ceil hat (List.mem_cons_of_mem _ (List.mem_cons_self ..)), List.mem_cons, List.not_mem_nil,
      forall_eq_or_imp, id, and_true, or_false, forall_eq]
    exact ⟨fun h => ⟨h.1, h.2.1.1, h.2.2.1⟩, fun h => ⟨h.1, ⟨h.2.1, hat.2⟩, h.2.2, hat.2⟩⟩
  rhs e m hat a ha := by
    rw [idx_facts.2.2.2.2.2.2.2.2.2, interp_sAnd, interp_sOr, interp_sTop B.defOK B.sortAt.closed,
      interp_inhOf_of (B.sortAt.den e)]
    simp only [List.mem_cons, List.not_mem_nil, exists_eq_or_imp, id, and_true, or_false, exists_eq_left]
    exact ⟨fun h => h.1.2, fun h => ⟨⟨ha, h⟩, ha⟩⟩

/-- **The sentence with h's functional sentence gives each of `Γ`'s three items for h.** -/
theorem gamma_of_text {σI : M} (B : Bg I σI) (hT : I ⊧ᴵ textItem.pat) (hF : I ⊧ᴵ fnlItem.pat) :
    ∀ it ∈ Faithful.kernelItems (Faithful.fnEquationsK c hFn), I ⊧ᴵ it.pat := by
  intro it hit
  have hmem : it.pat ∈ (Faithful.kernelItems (Faithful.fnEquationsK c hFn)).map (·.pat) :=
    List.mem_map.mpr ⟨it, hit, rfl⟩
  rw [gamma_shape] at hmem
  rw [text_shape] at hT
  rw [fnl_shape] at hF
  obtain ⟨hFh, hnd, hrk, hvk, hvr, hr, hx0, -, -, -⟩ := idx_facts
  have hG := guardsOf_pred B.defOK ax344
  have hone : ∀ e m, At I ws r e m → ∃ y, Inh I σI y ∧ ∀ a, Inh I σI a → (Fh.interpret I e a ↔ a = y) := by
    intro e m hat
    rw [hFh]
    exact one_of_fnl B.defOK B.ceilDef B.sortAt.den B.isSort hr hF (Closed.sym _) hnd hrk hvk hvr rfl
      (fun t ht => by
        simp only [tsF, List.mem_singleton] at ht
        subst ht
        exact ⟨hx0, by rw [idx_facts.2.2.2.2.2.2.2.2.1]; exact Closed.sym _⟩) hat
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h <;> rw [h]
  · exact clause_of_text B.defOK B.ceilDef B.sortAt hr hG (readings B) hT hone (List.mem_cons_self ..)
  · exact clause_of_text B.defOK B.ceilDef B.sortAt hr hG (readings B) hT hone
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · exact none_of_text B.defOK B.ceilDef B.sortAt hr hG (readings B) hT hone BN

/-- **`Γ`'s three items for h give the sentence**, without h's functional sentence. -/
theorem text_of_gamma {σI : M} (B : Bg I σI)
    (h : ∀ it ∈ Faithful.kernelItems (Faithful.fnEquationsK c hFn), I ⊧ᴵ it.pat) : I ⊧ᴵ textItem.pat := by
  have hs : ∀ φ ∈ (Faithful.kernelItems (Faithful.fnEquationsK c hFn)).map (·.pat), I ⊧ᴵ φ := by
    intro φ hφ
    obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hφ
    exact h it hit
  rw [gamma_shape] at hs
  rw [text_shape]
  obtain ⟨-, -, -, -, -, hr, -, -, -, -⟩ := idx_facts
  refine text_of_split (BN := BN) B.defOK B.ceilDef B.sortAt hr (guardsOf_pred B.defOK ax344) (readings B)
    (fun x hx => ?_) (hs _ (by simp)) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hs _ (by simp [Q])
    · exact hs _ (by simp [Q])
  · refine noneEmpty_of_sub (x₁ := A1) (List.mem_cons_self ..) (fun _ _ _ => trivial) ?_
    intro e m _ a ha
    unfold BN at ha
    exact (interp_sAnd.mp ha).1

end

/-! ## The readings from the reader's output (KcoreSpec/TieFRRead.lean)

The same tie with the readings derived by the general lemmas: `Readings` from `readings_of_fr`
(the clauses' premises read from `NodeFacts`, the alternatives in Int from `TermsInSort`, the
right side from `rhs_of_reader`), and the last clause's right side empty from `NodeFacts.apart`
(`noneEmpty_of_apart`). What is read of the model is `NodeFacts c I` and `TermsInSort c I`. -/

section General
open KCore.TieFRRead

/-- The clauses' variables, the table of `Γ`'s items for h, and the alternatives `frRead` gives
`frClauses`: `f(X)` and `g(X)` with no condition. -/
def vsC : List KoreAML.Var := Faithful.canonVars c [Srt.int]
def tblG : VarTable := [.sortVar "R", .evar "X0" (srt "Int"), .evar "VarV0" (srt "Int")]
def xsC : List (Term × List Term) := [(fX, []), (gX, [])]

/-- The text's right side `f(X) ∨ g(X)` and its `ensures` part `\top`. -/
def fK : Kore.Pattern := ap "Lblf" [ev "VarX" iS]
def gK : Kore.Pattern := ap "Lblg" [ev "VarX" iS]
def pT : Kore.Pattern := .or iS [fK, gK]
def enT : Kore.Pattern := .top iS

theorem hFn_clauses : hFn.clauses = Parse.frClauses Srt.int [Srt.int] [.var 0] none 50 false (frAltsOf xsC) := rfl

/-- The last clause's right side `f(X) ∧ (false = true)`. -/
def BNG : P := sAnd (altP c tblG vsC (fX, []))
  (tr ⟨tblG, []⟩ (reqPat (srtOf c Srt.int) (some (Term.kore c vsC (Parse.boolT false)))))

/-- `Γ`'s items for h, with the premises `clauseQ`, `lastQ` of the general lemmas. -/
theorem gamma_shapeG : (Faithful.kernelItems (Faithful.fnEquationsK c hFn)).map (·.pat) =
    [eqnPat ws r (clauseQ c tblG vsC Srt.int prem (fX, [])) IntP Fh (sAnd (altP c tblG vsC (fX, [])) (sTop IntP)),
     eqnPat ws r (clauseQ c tblG vsC Srt.int prem (gX, [])) IntP Fh (sAnd (altP c tblG vsC (gX, [])) (sTop IntP)),
     eqnPat ws r (lastQ c tblG vsC Srt.int prem xsC) IntP Fh BNG] := by decide +kernel

/-- The facts of the literals the general lemmas read: the tables agree on R and on the
variable, the text's alternatives translate as `Γ`'s, and the reader's normalisation of `pT`. -/
theorem lit_facts :
    tblG.ev (sortVarKey Rv) = r ∧ trSort tblG (srtOf c Srt.int) = IntP ∧
    tr ⟨tbl, []⟩ fK = altP c tblG vsC (fX, []) ∧ tr ⟨tbl, []⟩ gK = altP c tblG vsC (gX, []) ∧
    rhsT = sAnd (tr ctx pT) (tr ctx enT) ∧ Parse.orAlts pT = [fK, gK] ∧
    tblG.ev (Faithful.canonKey c [Srt.int] 0) = xv ∧ c.sortName Srt.int = "Int" ∧
    sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) [Srt.int] fX = some Srt.int ∧
    sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) [Srt.int] gX = some Srt.int ∧ varOccs fX = [0] ∧ varOccs gX = [0] := by
  decide +kernel

/-- The reader's normalisation of `pT`: nothing to drop or lift, the alternatives `f(X)` and
`g(X)`, none empty, no condition. -/
theorem norm_facts : Parse.hoist (Parse.dropEmptyAlts pT) = (pT, [], false) ∧
    keptAlts pT = [(fK, []), (gK, [])] ∧ (Parse.hoist fK).2.1 = [] ∧ (Parse.hoist gK).2.1 = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

end General

section GeneralModel
open KCore.TieFRRead
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The readings of the general lemmas, in a model with `NodeFacts c I` and `TermsInSort c I`. -/
theorem readingsG (F : HoldsShape.NodeFacts c I) (hTS : Faithful.TermsInSort c I) :
    ∃ σI, SortAt I IntP σI ∧ (∀ (e : Valuation M) a, (trSort tblG (srtOf c Srt.int)).interpret I e a ↔ a = σI) ∧
      Readings I ws r σI prem rhsT xsC (altP c tblG vsC) (altG I c tblG vsC)
        (clauseQ c tblG vsC Srt.int prem) (lastQ c tblG vsC Srt.int prem xsC) := by
  obtain ⟨hr0, hS0, hA1, hA2, hrhs0, hor0, hk0, hn0, hty1, hty2, hv1, hv2⟩ := lit_facts
  obtain ⟨hh0, hkept0, hal1, hal2⟩ := norm_facts
  obtain ⟨-, -, -, -, -, hr, -, hxv, hIntP, -⟩ := idx_facts
  obtain ⟨σI, hσS, hσ⟩ := F.sort (s := Srt.int) (by decide)
  have hσ' : ∀ (e : Valuation M) a, (trSort tblG (srtOf c Srt.int)).interpret I e a ↔ a = σI := fun e a => hσ tblG e a
  have hSA : SortAt I IntP σI := ⟨fun e a => by rw [← hS0]; exact hσ' e a, hσS, by rw [hIntP]; rfl⟩
  have hD := F.defOK
  have hB : BoolDen I := boolDen_of F
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
  -- the right side, from the reader
  have hrhs : ∀ e m, At I ws r e m → ∀ a, Inh I σI a →
      (rhsT.interpret I e a ↔ ∃ x ∈ xsC, (altP c tblG vsC x).interpret I e a ∧ altG I c tblG vsC x e) := by
    rw [hrhs0]
    refine rhs_of_reader hD F.ceilDef hB (Ens := fun _ => True) (cs := []) (r0 := pT) ?_ hh0 (by simp [AllTrue]) ?_ ?_ ?_
    · intro e m hat
      refine ⟨fun q hq => ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        refine ⟨by rcases hq with rfl | rfl <;> rfl, fun a ha => ?_⟩
        have hIn : Inh I σI a := by
          rcases hq with rfl | rfl
          · rw [hA1] at ha; exact hin e m hat _ (List.mem_cons_self ..) a ha
          · rw [hA2] at ha; exact hin e m hat _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) a ha
        show (inhOf IntP).interpret I e a
        rw [interp_inhOf_of (hSA.den e)]
        exact hIn
      · exact ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial⟩
    · intro a ha
      rw [hor0] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · rw [hal1]; simp [AllTrue]
      · rw [hal2]; simp [AllTrue]
    · intro e m _ a ha
      rw [enT, tr_top_iff hD (hSA.den e)]
      exact iff_of_true ha trivial
    · rw [hkept0]
      refine .cons ⟨fun e m _ a => by rw [hA1], fun e m _ => ?_⟩
        (.cons ⟨fun e m _ a => by rw [hA2], fun e m _ => ?_⟩ .nil)
      · simp [altG, holdsSC_nil]
      · simp [altG, holdsSC_nil]
  have hr' : sortGuard (tblG.ev (sortVarKey Rv)) ∈ ws := by rw [hr0]; exact hr
  have R := readings_of_fr F (prem := prem) hr' hσ' hσS (by rw [hr0]; exact hin) (by rw [hr0]; exact hrhs)
  rw [hr0] at R
  exact ⟨σI, hSA, hσ', R⟩

/-- **`Γ`'s three items for h give the sentence**, from `NodeFacts c I` and `TermsInSort c I`,
the last clause's right side empty because `false` and `true` are two elements of Bool. -/
theorem text_of_gammaG (F : HoldsShape.NodeFacts c I) (hTS : Faithful.TermsInSort c I)
    (h : ∀ it ∈ Faithful.kernelItems (Faithful.fnEquationsK c hFn), I ⊧ᴵ it.pat) : I ⊧ᴵ textItem.pat := by
  have hs : ∀ φ ∈ (Faithful.kernelItems (Faithful.fnEquationsK c hFn)).map (·.pat), I ⊧ᴵ φ := by
    intro φ hφ
    obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hφ
    exact h it hit
  rw [gamma_shapeG] at hs
  rw [text_shape]
  obtain ⟨σI, hSA, hσ', R⟩ := readingsG F hTS
  obtain ⟨-, -, -, -, -, hr, -, -, -, -⟩ := idx_facts
  refine text_of_split (BN := BNG) F.defOK F.ceilDef hSA hr (guardsOf_pred F.defOK ax344) R
    (fun x hx => ?_) (hs _ (by simp)) (noneEmpty_of_apart F hσ' hSA.isSort)
  simp only [xsC, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact hs _ (by simp)
  · exact hs _ (by simp)

/-- **The sentence with h's functional sentence gives each of `Γ`'s three items for h**, from
`NodeFacts c I` and `TermsInSort c I`. -/
theorem gamma_of_textG (F : HoldsShape.NodeFacts c I) (hTS : Faithful.TermsInSort c I)
    (hT : I ⊧ᴵ textItem.pat) (hF : I ⊧ᴵ fnlItem.pat) :
    ∀ it ∈ Faithful.kernelItems (Faithful.fnEquationsK c hFn), I ⊧ᴵ it.pat := by
  intro it hit
  have hmem : it.pat ∈ (Faithful.kernelItems (Faithful.fnEquationsK c hFn)).map (·.pat) :=
    List.mem_map.mpr ⟨it, hit, rfl⟩
  rw [gamma_shapeG] at hmem
  rw [text_shape] at hT
  rw [fnl_shape] at hF
  obtain ⟨σI, hSA, -, R⟩ := readingsG F hTS
  obtain ⟨hFh, hnd, hrk, hvk, hvr, hr, hx0, -, hIntP, -⟩ := idx_facts
  have hG := guardsOf_pred F.defOK ax344
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

end KCore.TieFRTest

#check @KCore.TieFRTest.gamma_of_text
#check @KCore.TieFRTest.text_of_gamma
/-- info: 'KCore.TieFRTest.gamma_of_text' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieFRTest.gamma_of_text
/-- info: 'KCore.TieFRTest.text_of_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieFRTest.text_of_gamma
/-- info: 'KoreAML.TieFR.clause_of_text' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KoreAML.TieFR.clause_of_text
/-- info: 'KoreAML.TieFR.none_of_text' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KoreAML.TieFR.none_of_text
/-- info: 'KoreAML.TieFR.text_of_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KoreAML.TieFR.text_of_split
/-- info: 'KoreAML.TieFR.one_of_fnl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KoreAML.TieFR.one_of_fnl
#check @KCore.TieFRTest.gamma_of_textG
#check @KCore.TieFRTest.text_of_gammaG
/-- info: 'KCore.TieFRTest.gamma_of_textG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieFRTest.gamma_of_textG
/-- info: 'KCore.TieFRTest.text_of_gammaG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieFRTest.text_of_gammaG
/-- info: 'KCore.TieFRRead.rhs_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieFRRead.rhs_sem
/-- info: 'KCore.TieFRRead.readings_of_fr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieFRRead.readings_of_fr
/-- info: 'KCore.TieFRRead.noneEmpty_of_apart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieFRRead.noneEmpty_of_apart
