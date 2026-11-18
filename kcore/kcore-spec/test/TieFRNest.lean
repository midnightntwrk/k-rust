/-
  The tie of an equation with `\or` on its right side, on fixture `e3-ml-eq-rhs-or-nest`
  (test/constructs/fixtures): its sentence 346 (`//@ 346`), `rule h(X) => (k(f(X) #Or g(X)) #Or
  #Bottom) #And {X *Int X >=Int 0 #Equals true}` with h `total`, against the equations `Γ` states for
  the clauses `Parse.frRead` reads of it, with the readings of the general lemmas of
  KcoreSpec/TieFRRead.lean (`readings_of_frT`). Run from the package root:
  `lake env lean -j1 test/TieFRNest.lean`.

  The right side exercises each step of the reader's normalisation (`norm_facts`):
  `dropEmptyAlts` leaves out the alternative `\bottom` (the `\or` it is in becomes its other
  alternative), `hoist` lifts the conjunct `{X *Int X >=Int 0 #Equals true}` out of the
  conjunction, and `orAlts` distributes the `\or` under the application of k: the alternatives are
  `k(f(X))` and `k(g(X))`, each with the lifted condition.

  - `ax346`, `ax217`: the equation and h's functional sentence as kore.txt writes them, written with
    the builders of Kore/Build.lean; `ax217_eq`: the functional sentence is
    `Model.functionalAxiom c hFn`.
  - `frRead_eqT`: the reader reads the equation as h's clauses (kernel).
  - What the general lemmas take of the text, decided on its literal (kernel): `gamma_shapeG`
    (`Γ`'s premises are `clauseQ` and `lastQ` over `Γ`'s table, over the text's guards),
    `lit_facts` (the tables agree on R and the variable, the sorts and variables of the terms),
    `read_facts` (the terms `Parse.term` reads of the operands and of the alternatives under k),
    `rt_facts` (the sorts of the variables read, the tables aligned on them, and `frRT`: the
    alternatives and the lifted conjunct are read as the terms of their patterns) and `ops_facts`
    (the operands of the right side's connectives).
  - `tr_ofReader`: the alternatives translate as the kept ones, their condition as the lifted
    conjunct's Bool term (`altsTrOK`), by the round trip of `Parse.term`
    (KcoreSpec/TieFRTermRT.lean) from `frRead_eqT` and `rt_facts`.
  - What is read of the model: `NodeFacts c I` and `TermsInSort c I`. `TightSem` of the right side
    from `tightSem_of_ops`: its operands are `\bottom`, the lifted conjunct, the terms `f(X)` and
    `g(X)`, and `k(f(X) ∨ g(X))`, whose alternatives are terms.
  - `text_of_gammaG`: `Γ`'s items for h give the sentence; `gamma_of_textG`: the sentence with h's
    functional sentence gives each of them.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.TieFRNestTest

open ML KoreAML KoreAML.TieFR KCore.TieFRRead
open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

/-! ## The semantics: h with the clauses `frRead` reads -/

def F : Sym := nRegSyms + 4
def G : Sym := nRegSyms + 5
def K : Sym := nRegSyms + 6
def H : Sym := nRegSyms + 7
def fX : Term := .app F [.var 0]
def gX : Term := .app G [.var 0]
def kfX : Term := .app K [fX]
def kgX : Term := .app K [gX]
/-- `X *Int X >=Int 0`. -/
def bX : Term := .app intGe [.app intMul [.var 0, .var 0], .dv Srt.int (.int 0)]

def fFn : Fn := ⟨F, [Srt.int], Srt.int, [⟨[Srt.int], [.var 0], none, .var 0, none, 50, false, [], .top, .top⟩], true⟩
def gFn : Fn := ⟨G, [Srt.int], Srt.int,
  [⟨[Srt.int], [.var 0], none, .app intAdd [.var 0, .dv Srt.int (.int 0)], none, 50, false, [], .top, .top⟩], true⟩
def kFn : Fn := ⟨K, [Srt.int], Srt.int,
  [⟨[Srt.int], [.var 0], none, .app intAdd [.var 0, .dv Srt.int (.int 1)], none, 50, false, [], .top, .top⟩], true⟩

/-- The alternatives `frRead` gives `frClauses`: `k(f(X))` and `k(g(X))`, each with the lifted
condition. -/
def xsC : List (Term × List Term) := [(kfX, [bX]), (kgX, [bX])]

/-- h, declared `total`, with the clauses of the split of its equation. -/
def hFn : Fn := ⟨H, [Srt.int], Srt.int, Parse.frClauses Srt.int [Srt.int] [.var 0] none 50 false (frAltsOf xsC), true⟩

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf", "Lblg", "Lblk", "Lblh"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [fFn, gFn, kFn, hFn]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

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

/-- Sentence 346: `X0 ∈ VarX → h(X0) = pT ∧ ⊤`. -/
def ax346 : Kore.Axiom :=
  { sortVars := [Rv]
    pattern := .implies R
      (.and R [.top R, .and R [.in iS R (ev "X0" iS) xK, .top R]])
      (.equals iS R (ap "Lblh" [ev "X0" iS]) (.and iS [pT, enT]))
    attributes := [] }

/-- Sentence 217: `∃Val. Val = h(K0)`. -/
def ax217 : Kore.Axiom :=
  { sortVars := [Rv]
    pattern := .exist R (evar "Val" iS) (.equals iS R (.var (.evar (evar "Val" iS))) (ap "Lblh" [ev "K0" iS]))
    attributes := [attr "functional"] }

theorem ax217_eq : ax217 = Faithful.Model.functionalAxiom c hFn := by decide +kernel

def textItem : Item := trAxiom [] [] ⟨346, "E3-ML-EQ-RHS-OR-NEST", ax346⟩
def fnlItem : Item := Faithful.Model.functionalItem c hFn

/-- The names of the text: f, g, k, h are the symbols `nRegSyms + 4` to `nRegSyms + 7`, of result
sort Int; h has its `functional` sentence. -/
def NT : Parse.Names :=
  { sorts := ["KCell", "KCellOpt"]
    syms := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf", "Lblg", "Lblk", "Lblh"]
    keyFns := [(nRegSyms + 4, "Int"), (nRegSyms + 5, "Int"), (nRegSyms + 6, "Int"), (nRegSyms + 7, "Int")]
    fnlSyms := [("Lblh", false)] }

/-- The equation as the reader takes it. -/
def eqT : Parse.RawEqn := ⟨"Lblh", [xK], none, none, pT, [], none, false⟩

/-- **The reader reads the equation** as h's clauses (kernel). -/
theorem frRead_eqT : Parse.frRead NT eqT = .ok (some (hFn.clauses, [⟨"X", "Int"⟩])) := by
  kernel_rfl

/-- **The normalisation drops, lifts and distributes**: `dropEmptyAlts` changes the right side,
leaving `k(f(X) ∨ g(X))` of the `\or` with `\bottom`; `hoist` lifts one condition, the conjunct; the
side holds `\or` only under the application of k, and `orAlts` gives `k(f(X))` and `k(g(X))`, none
empty and with no condition of its own. -/
theorem norm_facts : Parse.dropEmptyAlts pT ≠ pT ∧ Parse.dropEmptyAlts pT = .and iS [kOr, eqK] ∧
    frSide eqT.rhs = kOr ∧ frConds eqT.rhs = [.isTrue bK] ∧
    Parse.orAlts kOr = [ap "Lblk" [fK], ap "Lblk" [gK]] ∧
    keptAlts (frSide eqT.rhs) = [(ap "Lblk" [fK], []), (ap "Lblk" [gK], [])] :=
  ⟨by decide +kernel, rfl, rfl, rfl, rfl, rfl⟩

/-- The reader's sort check accepts an operand `\and{Int}(\bottom, \top{Bool})` of an `\or{Int}`: it
does not look at a `\top`'s sort (`Parse.rhsOpSort`). The operand holds nothing, but `TightSem`
asks its own operand `\top{Bool}` to lie in Int, so `TightSem` is no consequence of `frRead`. -/
example : Parse.rhsSorted (.or iS [.and iS [.bottom iS, .top bS], fK, gK]) = true := by decide

/-! ## The shapes -/

def tbl : VarTable := tableOf ax346.sortVars ax346.pattern
def ctx : Ctx := ⟨tbl, []⟩
def ws : List P := guardsOf ax346
def r : EVar := tbl.ev (sortVarKey Rv)
def prem : P := tr ctx (.and R [.top R, .and R [.in iS R (ev "X0" iS) xK, .top R]])
def IntP : P := trSort tbl iS
def Fh : P := tr ctx (ap "Lblh" [ev "X0" iS])
def rhsT : P := sAnd (tr ctx pT) (tr ctx enT)
def x0 : EVar := tbl.ev (evarKey (evar "X0" iS))
def xv : EVar := tbl.ev (evarKey (evar "VarX" iS))

theorem text_shape : textItem.pat = eqnPat ws r prem IntP Fh rhsT :=
  trAxiom_eqnPat [] [] _ _ ax346 rfl rfl

/-- The clauses' variables and the table of `Γ`'s items for h. -/
def vsC : List KoreAML.Var := Faithful.canonVars c [Srt.int]
def tblG : VarTable := [.sortVar "R", .evar "X0" (srt "Int"), .evar "VarV0" (srt "Int")]

/-- The last clause's right side `k(f(X)) ∧ (false = true)`. -/
def BNG : P := sAnd (altP c tblG vsC (kfX, [bX]))
  (tr ⟨tblG, []⟩ (reqPat (srtOf c Srt.int) (some (Term.kore c vsC (Parse.boolT false)))))

/-- `Γ`'s items for h, with the premises `clauseQ`, `lastQ` of the general lemmas. -/
theorem gamma_shapeG : (Faithful.kernelItems (Faithful.fnEquationsK c hFn)).map (·.pat) =
    [eqnPat ws r (clauseQ c tblG vsC Srt.int prem (kfX, [bX])) IntP Fh (sAnd (altP c tblG vsC (kfX, [bX])) (sTop IntP)),
     eqnPat ws r (clauseQ c tblG vsC Srt.int prem (kgX, [bX])) IntP Fh (sAnd (altP c tblG vsC (kgX, [bX])) (sTop IntP)),
     eqnPat ws r (lastQ c tblG vsC Srt.int prem xsC) IntP Fh BNG] := by decide +kernel

/-- The functional sentence: `∃v. v = h(K0)`, K0 the variable `k0`. -/
def tblF : VarTable := tableOf ax217.sortVars ax217.pattern
def rF : EVar := tblF.ev (sortVarKey Rv)
def vF : EVar := tblF.ev (evarKey (evar "Val" iS))
def k0 : EVar := tblF.ev (evarKey (evar "K0" iS))
def hHead : P := sym (.symbol "Lblh")
def tsF : List (EVar × EVar × P) := [(x0, k0, IntP)]

theorem fnl_shape : fnlItem.pat =
    fnlPat (sortGuard rF :: tsF.map fun t => (t.2.1 ∈∈ inhOf t.2.2)) rF vF IntP
      (appList hHead (tsF.map fun t => .evar t.2.1)) := by
  show (trAxiom [] [] ⟨0, "kernel", Faithful.Model.functionalAxiom c hFn⟩).pat = _
  rw [← ax217_eq, trAxiom_fnlPat [] [] 0 "kernel" ax217 (F := ap "Lblh" [ev "K0" iS]) (v := evar "Val" iS) rfl rfl]
  decide +kernel

/-- The facts of the indices `one_of_fnl` reads, and of the guards. -/
theorem idx_facts :
    Fh = appList hHead (tsF.map fun t => .evar t.1) ∧ (tsF.map (·.2.1)).Nodup ∧ rF ∉ tsF.map (·.2.1) ∧
      vF ∉ tsF.map (·.2.1) ∧ vF ≠ rF ∧ sortGuard r ∈ ws ∧ (x0 ∈∈ inhOf IntP) ∈ ws ∧
      (xv ∈∈ inhOf IntP) ∈ ws ∧ IntP = sym (.sort "SortInt") := by
  decide +kernel

/-- The facts of the literals the general lemmas read: the tables agree on R and on the
variable; the sorts; the sorts and variables of the terms of the alternatives and of the
operands. -/
theorem lit_facts :
    tblG.ev (sortVarKey Rv) = r ∧ trSort tblG (srtOf c Srt.int) = IntP ∧ trSort tbl iS = IntP ∧
    tblG.ev (Faithful.canonKey c [Srt.int] 0) = xv ∧ c.sortName Srt.int = "Int" ∧
    sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) [Srt.int] fX = some Srt.int ∧
    sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) [Srt.int] gX = some Srt.int ∧
    sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) [Srt.int] kfX = some Srt.int ∧
    sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) [Srt.int] kgX = some Srt.int ∧
    varOccs fX = [0] ∧ varOccs gX = [0] ∧ varOccs kfX = [0] ∧ varOccs kgX = [0] := by
  decide +kernel

/-- What the round trip of `Parse.term` takes of the text (kernel): the sorts of the variables
read, the tables aligned on them (`alignOK`), and the alternatives and the lifted conjunct read as
the terms of their patterns (`frRT`). -/
theorem rt_facts : Parse.varSorts NT [⟨"X", "Int"⟩] = .ok [Srt.int] ∧
    TermRT.alignOK c tblG tbl [Srt.int] [⟨"X", "Int"⟩] = true ∧ TieFRRT.frRT NT eqT = true :=
  ⟨by kernel_rfl, by decide +kernel, by decide +kernel⟩

/-- The alternatives translate as the kept ones, each with the lifted conjunct's Bool term as its
condition (`altsTrOK`): from the reader, by the round trip of `Parse.term`
(`altsTrOK_of_clauses`). -/
theorem tr_ofReader : altsTrOK c tblG vsC tbl (frConds eqT.rhs) [] (keptAlts (frSide eqT.rhs)) xsC = true :=
  TieFRRT.altsTrOK_of_clauses (c := c) rfl rfl frRead_eqT rt_facts.1 rt_facts.2.1 rt_facts.2.2
    (rfl : hFn.clauses = Parse.frClauses Srt.int [Srt.int] [.var 0] none 50 false (frAltsOf xsC))

/-- The terms `Parse.term` reads of the operands `f(X)`, `g(X)` and of the alternatives of
`k(f(X) ∨ g(X))` (kernel), each `rtPat`: their translations are then the round trip's
(`inSortK_of_read`). -/
theorem read_facts :
    Parse.term NT [] fK = .ok (fX, [⟨"X", "Int"⟩]) ∧ Parse.term NT [] gK = .ok (gX, [⟨"X", "Int"⟩]) ∧
    Parse.term NT [] (ap "Lblk" [fK]) = .ok (kfX, [⟨"X", "Int"⟩]) ∧
    Parse.term NT [] (ap "Lblk" [gK]) = .ok (kgX, [⟨"X", "Int"⟩]) ∧
    TermRT.rtPat NT fK = true ∧ TermRT.rtPat NT gK = true ∧ TermRT.rtPat NT (ap "Lblk" [fK]) = true ∧
    TermRT.rtPat NT (ap "Lblk" [gK]) = true :=
  ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel⟩

/-- The operands of the right side's connectives, with their sorts. -/
theorem ops_facts : connOps pT =
    [(iS, .or iS [kOr, .bottom iS]), (iS, eqK), (iS, kOr), (iS, .bottom iS), (iS, fK), (iS, gK)] ∧
    andSorts pT = [iS] ∧ Parse.rhsSorted pT = true ∧ Parse.rhsSorted kOr = true ∧
    Parse.orAlts kOr = [ap "Lblk" [fK], ap "Lblk" [gK]] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## In a model -/

section GeneralModel
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The variable X is in Int wherever the guards hold. -/
theorem varInt (F : HoldsShape.NodeFacts c I) {e : Valuation M} {m : M} (hat : At I ws r e m) :
    ∀ i ∈ [0], Faithful.InS I (c.sortName ([Srt.int].getD i 0)) (e.evalEvar (tblG.ev (Faithful.canonKey c [Srt.int] i))) := by
  obtain ⟨-, -, -, hk0, hn0, -⟩ := lit_facts
  obtain ⟨-, -, -, -, -, -, -, hxv, hIntP⟩ := idx_facts
  intro i hi
  rw [List.mem_singleton] at hi
  subst hi
  have := hat.1 _ hxv
  rw [interp_member F.defOK] at this
  rw [List.getD_cons_zero, hn0, hk0, ← Faithful.inS_iff e]
  rw [hIntP] at this
  exact this

/-- The readings of the general lemmas, in a model with `NodeFacts c I` and `TermsInSort c I`. -/
theorem readingsG (F : HoldsShape.NodeFacts c I) (hTS : Faithful.TermsInSort c I) :
    ∃ σI, SortAt I IntP σI ∧ (∀ (e : Valuation M) a, (trSort tblG (srtOf c Srt.int)).interpret I e a ↔ a = σI) ∧
      Readings I ws r σI prem rhsT xsC (altP c tblG vsC) (altG I c tblG vsC)
        (clauseQ c tblG vsC Srt.int prem) (lastQ c tblG vsC Srt.int prem xsC) := by
  obtain ⟨hr0, hS0, hST, hk0, hn0, htyf, htyg, htykf, htykg, hvf, hvg, hvkf, hvkg⟩ := lit_facts
  obtain ⟨hrf, hrg, hrkf, hrkg, hpf, hpg, hpkf, hpkg⟩ := read_facts
  obtain ⟨hops, hands, hsorted, hsortedK, horK⟩ := ops_facts
  obtain ⟨-, -, -, -, -, hr, -, -, hIntP⟩ := idx_facts
  obtain ⟨σI, hσS, hσ⟩ := F.sort (s := Srt.int) (by decide)
  have hσ' : ∀ (e : Valuation M) a, (trSort tblG (srtOf c Srt.int)).interpret I e a ↔ a = σI := fun e a => hσ tblG e a
  have hSA : SortAt I IntP σI := ⟨fun e a => by rw [← hS0]; exact hσ' e a, hσS, by rw [hIntP]; rfl⟩
  have hD := F.defOK
  have hB : BoolDen I := boolDen_of F
  have hDen : ∀ e, SortDen I tbl e iS := fun e => ⟨σI, hσS, by rw [hST]; exact hSA.den e⟩
  have hTrS : trSort tbl iS = trSort tblG (srtOf c Srt.int) := by rw [hST, hS0]
  -- the alternatives lie in Int
  have hin : ∀ e m, At I ws r e m → ∀ x ∈ xsC, ∀ a, (altP c tblG vsC x).interpret I e a → Inh I σI a := by
    refine inSort_of_terms hTS (vars := [Srt.int]) (by decide) hσ' ?_ ?_
    · intro x hx
      simp only [xsC, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact htykf
      · exact htykg
    · intro e m hat x hx i hi
      simp only [xsC, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rw [hvkf] at hi; exact varInt F hat i hi
      · rw [hvkg] at hi; exact varInt F hat i hi
  -- the right side's operands lie in their sorts
  have hT : ∀ e m, At I ws r e m → TightSem I tbl e pT := by
    intro e m hat
    have hterm : ∀ (t : Term) (q : Kore.Pattern), sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) [Srt.int] t = some Srt.int →
        Parse.term NT [] q = .ok (t, [⟨"X", "Int"⟩]) → TermRT.rtPat NT q = true → varOccs t = [0] →
        InSortK I tbl e iS q :=
      fun t q hty hrd hrt hv => TieFRRT.inSortK_of_read (c := c) rfl rfl hTS rt_facts.2.1 hrd hrt
        (List.prefix_refl _) (by decide) hty hTrS (by rw [hv]; exact varInt F hat)
    have hf : InSortK I tbl e iS fK := hterm fX fK htyf hrf hpf hvf
    have hg : InSortK I tbl e iS gK := hterm gX gK htyg hrg hpg hvg
    have hkOr : InSortK I tbl e iS kOr := by
      have hTk : Tight I tbl e kOr := tight_of_rhsSorted kOr hsortedK
        (tightSem_of_ops hD kOr hsortedK (fun x hx _ => by
            rw [show connOps kOr = [(iS, fK), (iS, gK)] from rfl] at hx
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl
            · exact hf
            · exact hg)
          (fun s hs => by cases hs))
      refine inSortK_of_alts hD hTk fun q hq => ?_
      rw [horK] at hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact hterm kfX _ htykf hrkf hpkf hvkf
      · exact hterm kgX _ htykg hrkg hpkg hvkg
    refine tightSem_of_ops hD pT hsorted (fun x hx hleaf => ?_) (fun s hs => ?_)
    · rw [hops] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · cases hleaf
      · exact inSortK_isTrue hD F.ceilDef hB rfl rfl (hDen e)
      · exact hkOr
      · exact inSortK_bottom hD _ _
      · exact hf
      · exact hg
    · rw [hands, List.mem_singleton] at hs
      subst hs
      exact hDen e
  have hr' : sortGuard (tblG.ev (sortVarKey Rv)) ∈ ws := by rw [hr0]; exact hr
  have R := readings_of_frT F (al := []) (prem := prem) frRead_eqT (by decide) (by decide) hr' hσ' hσS
    (by rw [hr0]; exact hin) (by rw [hr0]; exact hT) (en := enT) rfl (fun e a => hSA.den e a) tr_ofReader
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
  obtain ⟨-, -, -, -, -, hr, -, -, -⟩ := idx_facts
  refine text_of_split (BN := BNG) F.defOK F.ceilDef hSA hr (guardsOf_pred F.defOK ax346) R
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
  obtain ⟨hFh, hnd, hrk, hvk, hvr, hr, hx0, -, hIntP⟩ := idx_facts
  have hG := guardsOf_pred F.defOK ax346
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

end KCore.TieFRNestTest

#check @KCore.TieFRNestTest.gamma_of_textG
#check @KCore.TieFRNestTest.text_of_gammaG
/-- info: 'KCore.TieFRNestTest.gamma_of_textG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieFRNestTest.gamma_of_textG
/-- info: 'KCore.TieFRNestTest.text_of_gammaG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieFRNestTest.text_of_gammaG
